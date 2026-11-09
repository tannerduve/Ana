// Pinned Pi baseline. No credentials are loaded here: the host broker authenticates.
import fs from 'node:fs';
import {spawn} from 'node:child_process';
import {Agent} from '@earendil-works/pi-agent-core';
import {getModel, streamSimple} from '@earendil-works/pi-ai/compat';
import {createAgentSession, DefaultResourceLoader, SessionManager, SettingsManager} from '@earendil-works/pi-coding-agent';
import {piContextOptions} from './context-settings.mjs';

const config = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
// Satisfies Pi's auth-presence check. The broker replaces this nonsecret marker.
process.env.ANTHROPIC_API_KEY = 'evaluation-broker';
const workspace = config.workspace || '/workspace';
const sessionDir = config.sessionDir || '/sessions';
const toolBinary = config.toolBinary || '/app/eval_tools';
const base = getModel('anthropic', config.model);
if (!base) throw new Error('pinned Pi catalog does not contain the configured model');
const contextOptions = piContextOptions(config, base,
  Object.hasOwn(config, 'piContextWindow') || Object.hasOwn(config, 'piCompaction')
    ? SettingsManager.inMemory().getCompactionSettings(base) : undefined);
const model = {...base, baseUrl: config.testEndpoint.replace(/\/v1\/messages$/, ''),
  maxTokens: config.maxOutputTokens, ...contextOptions.modelOverrides};
let toolsRun = 0;
const events = event => process.stdout.write(JSON.stringify(event) + '\n');
let controlledSchemas;
const artifacts = new Map();
const stream = (m, context, options) => streamSimple(m, context, {...options,
  apiKey: 'evaluation-broker', maxTokens: config.maxOutputTokens, maxRetries: 0,
  timeoutMs: config.operationTimeoutMs, cacheRetention: 'none', reasoning: undefined,
  onPayload: payload => {
    if (config.track === 'controlled') {
      // Match Lean's provider settings and schemas; Pi still owns its agent loop.
      delete payload.thinking; delete payload.output_config;
      payload.system = config.instructions;
      payload.tools = controlledSchemas;
      payload.messages = payload.messages.filter(m => m.role !== 'system');
      const bytes = Buffer.byteLength(JSON.stringify({model:payload.model,system:config.instructions,
        messages:payload.messages,maxTokens:payload.max_tokens,purpose:'task'})) + 16384;
      if (bytes > config.maxContextBytes) throw new Error('context allowance exhausted');
    }
    return payload;
  }});
const beforeToolCall = () => {
  if (toolsRun >= config.maxToolCalls) return {block:true, reason:'tool dispatch ceiling exhausted', terminate:true};
  toolsRun++;
};

function callNative(request, signal) {
  return new Promise((resolve, reject) => {
    const child = spawn(toolBinary, [], {stdio:['pipe','pipe','pipe']});
    let output = '', error = '';
    const abort = () => fs.writeFileSync(`${sessionDir}/cancel`, 'cancel\n');
    signal?.addEventListener('abort', abort, {once:true});
    child.stdout.on('data', chunk => { output += chunk; if (output.length > 2_000_000) child.kill('SIGTERM'); });
    child.stderr.on('data', chunk => { if (error.length < 4096) error += chunk; });
    child.on('error', reject);
    child.on('close', () => {
      signal?.removeEventListener('abort', abort);
      try { resolve(JSON.parse(output)); } catch { reject(new Error('Lean tool bridge failed')); }
    });
    child.stdin.end(JSON.stringify(request)+'\n');
  });
}

let session, agent;
if (config.track === 'controlled') {
  const schemas = JSON.parse(fs.readFileSync(config.schemasPath || '/schemas.json', 'utf8'));
  controlledSchemas = schemas;
  const tools = schemas.map(schema => ({name:schema.name, label:schema.name,
    description:schema.description, parameters:schema.input_schema,
    execute:async (id, input, signal) => {
      const result = await callNative({call:{id,name:schema.name,input}, workspace,
        artifactDir:`${sessionDir}/artifacts`, cancelPath:`${sessionDir}/cancel`,
        timeoutMs:config.operationTimeoutMs, outputBytes:config.maxToolOutputBytes,
        artifacts:[...artifacts.values()]}, signal);
      for (const artifact of result.artifacts || []) artifacts.set(artifact.id, artifact);
      if (result.uncertain) agent.abort();
      return {content:[{type:'text',text:result.text}], details:{}, isError:result.isError};
    }}));
  fs.mkdirSync(`${sessionDir}/artifacts`, {recursive:true});
  agent = new Agent({initialState:{systemPrompt:config.instructions, model, thinkingLevel:'off', tools},
    streamFn:stream, toolExecution:'sequential', beforeToolCall});
} else {
  const settingsManager = SettingsManager.inMemory({retry:{enabled:false,maxRetries:0,
    provider:{maxRetries:0,timeoutMs:config.operationTimeoutMs}}, cacheWarming:'off',
    ...contextOptions.settingsOverrides});
  const loader = new DefaultResourceLoader({cwd:workspace,agentDir:`${sessionDir}/pi`, settingsManager,
    noExtensions:true,noSkills:true,noPromptTemplates:true,noThemes:true,noContextFiles:true});
  await loader.reload();
  ({session} = await createAgentSession({cwd:workspace,agentDir:`${sessionDir}/pi`,model,
    thinkingLevel:'off',settingsManager,resourceLoader:loader,sessionManager:SessionManager.create(workspace,`${sessionDir}/pi`)}));
  agent = session.agent;
  agent.streamFunction = stream;
  agent.beforeToolCall = beforeToolCall;
}
agent.subscribe(events);
const timer = setTimeout(() => agent.abort(), config.maxElapsedMs);
try {
  if (session) await session.prompt(config.task);
  else await agent.prompt(config.task);
  const last = agent.state.messages.filter(m => m.role === 'assistant').at(-1);
  const succeeded = last?.stopReason === 'stop' && !agent.state.errorMessage;
  events({type:'evaluation_end',toolDispatches:toolsRun,stopReason:last?.stopReason,
    error:agent.state.errorMessage,normalFinish:succeeded,
    ...(contextOptions.record ? {piContextConfiguration:contextOptions.record} : {})});
  process.exitCode = succeeded ? 0 : 1;
} finally {
  clearTimeout(timer);
  session?.dispose();
}

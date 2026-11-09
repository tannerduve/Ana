// Offline prerequisite: exercise the installed SDK/session, never prompt a model.
import fs from 'node:fs';
import crypto from 'node:crypto';
import net from 'node:net';
import {piContextOptions} from './context-settings.mjs';

let attemptedNetwork = 0;
const rejectNetwork = () => {
  attemptedNetwork++;
  throw new Error('network access is forbidden during Pi startup preflight');
};
globalThis.fetch = rejectNetwork;
net.Socket.prototype.connect = rejectNetwork;

const {Agent} = await import('@earendil-works/pi-agent-core');
const {getModel, streamSimple} = await import('@earendil-works/pi-ai/compat');
const {createAgentSession, DefaultResourceLoader, SessionManager, SettingsManager} =
  await import('@earendil-works/pi-coding-agent');
const [modelId, workspace, sessionDir, contextConfigPath] = process.argv.slice(2);
if (!modelId || !workspace || !sessionDir || typeof Agent !== 'function' || typeof streamSimple !== 'function') {
  throw new Error('invalid Pi startup preflight arguments or SDK exports');
}
const base = getModel('anthropic', modelId);
if (!base) throw new Error('pinned Pi catalog does not contain the configured model');
const contextOptions = piContextOptions(contextConfigPath
  ? JSON.parse(fs.readFileSync(contextConfigPath, 'utf8')) : {}, base,
  contextConfigPath ? SettingsManager.inMemory().getCompactionSettings(base) : undefined);
const model = contextOptions.record ? {...base, ...contextOptions.modelOverrides} : base;
const settingsManager = SettingsManager.inMemory({retry:{enabled:false,maxRetries:0}, cacheWarming:'off',
  ...contextOptions.settingsOverrides});
const loader = new DefaultResourceLoader({cwd:workspace,agentDir:sessionDir,settingsManager,
  noExtensions:true,noSkills:true,noPromptTemplates:true,noThemes:true,noContextFiles:true});
await loader.reload();
const {session} = await createAgentSession({cwd:workspace,agentDir:sessionDir,model,thinkingLevel:'off',
  settingsManager,resourceLoader:loader,sessionManager:SessionManager.inMemory(workspace)});
session.dispose();
if (attemptedNetwork !== 0) throw new Error('Pi startup attempted network access');
const pkg = JSON.parse(fs.readFileSync(new URL('./node_modules/@earendil-works/pi-coding-agent/package.json', import.meta.url)));
process.stdout.write(JSON.stringify({status:'ok',nodeVersion:process.version,
  nodeSha256:crypto.createHash('sha256').update(fs.readFileSync(process.execPath)).digest('hex'),
  model:modelId,piVersion:pkg.version,providerRequests:0})+'\n');

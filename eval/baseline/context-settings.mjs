// Optional evaluation overrides. Omission preserves the pinned SDK defaults.
export function piContextOptions(config, catalogModel, defaultCompaction) {
  if (Object.keys(config).some(key => key.startsWith('pi') && !['piContextWindow', 'piCompaction'].includes(key))) {
    throw new Error('unknown Pi context setting');
  }
  const supplied = ['piContextWindow', 'piCompaction'].filter(key => Object.hasOwn(config, key));
  if (!supplied.length) return {modelOverrides: {}, settingsOverrides: {}, record: null};
  if (config.track !== 'product') throw new Error('Pi context settings require the product track');
  const integer = (value, name, minimum = 0) => {
    if (!Number.isSafeInteger(value) || value < minimum) {
      throw new Error(`${name} must be a safe integer >= ${minimum}`);
    }
    return value;
  };
  const catalogWindow = integer(catalogModel.contextWindow, 'catalog contextWindow', 1);
  const window = Object.hasOwn(config, 'piContextWindow')
    ? integer(config.piContextWindow, 'piContextWindow', 1) : catalogWindow;
  if (window > catalogWindow) throw new Error('piContextWindow exceeds the pinned model catalog');
  if (window <= integer(config.maxOutputTokens, 'maxOutputTokens', 1)) {
    throw new Error('piContextWindow must exceed maxOutputTokens');
  }
  const requested = Object.fromEntries(supplied.map(key => [key, config[key]]));
  let compaction = {};
  if (Object.hasOwn(config, 'piCompaction')) {
    compaction = config.piCompaction;
    if (!compaction || typeof compaction !== 'object' || Array.isArray(compaction) ||
        Object.keys(compaction).some(key => !['enabled', 'reserveTokens', 'keepRecentTokens'].includes(key))) {
      throw new Error('piCompaction must contain only enabled, reserveTokens and keepRecentTokens');
    }
    if (Object.hasOwn(compaction, 'enabled') && typeof compaction.enabled !== 'boolean') {
      throw new Error('piCompaction.enabled must be Boolean');
    }
    for (const field of ['reserveTokens', 'keepRecentTokens']) {
      if (Object.hasOwn(compaction, field) && integer(compaction[field], `piCompaction.${field}`) >= window) {
        throw new Error(`piCompaction.${field} must be smaller than the context window`);
      }
    }
  }
  const effective = {...defaultCompaction, ...compaction};
  if (effective.enabled && (effective.reserveTokens >= window ||
      effective.keepRecentTokens >= window - effective.reserveTokens)) {
    throw new Error('Pi compaction reserve and recent tokens must leave room in the context window');
  }
  return {
    modelOverrides: Object.hasOwn(config, 'piContextWindow') ? {contextWindow: window} : {},
    settingsOverrides: Object.hasOwn(config, 'piCompaction') ? {compaction: {...compaction}} : {},
    record: {requested, effective: {catalogContextWindow: catalogWindow,
      contextWindow: window, compaction: effective}},
  };
}

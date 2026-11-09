def apply(settings,operations):
    for op in operations: settings[op['path'][-1]]=op.get('value')
    return settings

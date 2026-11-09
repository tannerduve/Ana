exports.report=events=>events.map(e=>({account:e.account,balance:e.delta,events:1}));

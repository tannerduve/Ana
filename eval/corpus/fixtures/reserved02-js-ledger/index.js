const {normalize}=require('./normalize');const {report}=require('./report');
exports.summarize=events=>report(normalize(events));

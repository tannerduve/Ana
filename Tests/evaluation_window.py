"""Actual isolated positive/negative controls for the post hoc numeric probe."""
import json
from pathlib import Path
import socket
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "eval/runner"))
from posthoc_window import EXPECTED, run_source


class WindowPosthoc(unittest.TestCase):
    def test_identity_passes_and_rolling_difference_preserves_infinity(self):
        positive = run_source(b"exports.windowSums=(values,width)=>values.slice();")
        self.assertTrue(positive["passed"], positive)
        bad = run_source(b"exports.windowSums=(v,w)=>[v[0],v[0]+(v[1]-v[0])];")
        self.assertEqual(bad["status"], "observed")
        self.assertFalse(bad["passed"])
        self.assertEqual(bad["actual"]["value"],
                         [EXPECTED[0], {"kind": "non-finite", "value": "Infinity"}])

    def test_worker_cannot_read_host_write_source_or_connect_host_network(self):
        with tempfile.TemporaryDirectory() as temporary, socket.socket() as listener:
            host_file = Path(temporary) / "private-sentinel"
            host_file.write_text("host-only-data")
            listener.bind(("127.0.0.1", 0))
            listener.listen()
            port = listener.getsockname()[1]
            source = """
const fs=require('node:fs'),child=require('node:child_process');
exports.windowSums=(values,width)=>{
 for(const path of PATHS){
   if(fs.existsSync(path)) throw new Error('host path exposed');
 }
 let readonly=false;
 try{fs.writeFileSync(__filename,'modified');}catch(e){readonly=e.code==='EROFS';}
 if(!readonly) throw new Error('source writable');
 const code="import socket,sys\\ns=socket.socket();s.settimeout(1)\\ntry: s.connect(('127.0.0.1',PORT))\\nexcept OSError: sys.exit(0)\\nsys.exit(1)";
 const result=child.spawnSync('/usr/bin/python3',['-I','-S','-c',code]);
 if(result.status!==0) throw new Error('host network exposed or probe failed');
 return values.slice();
};
""".replace("PATHS", json.dumps([str(host_file), str(ROOT), "/checker", "/home"]))
            source = source.replace("PORT", str(port))
            report = run_source(source.encode())
            self.assertTrue(report["passed"], report)
            self.assertEqual(host_file.read_text(), "host-only-data")

    def test_input_mutation_is_not_accepted(self):
        report = run_source(b"exports.windowSums=(values)=>{const out=values.slice();values[0]=0;return out;};")
        self.assertFalse(report["passed"])
        self.assertFalse(report["actual"]["input_preserved"])


if __name__ == "__main__":
    unittest.main()

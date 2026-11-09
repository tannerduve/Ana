import unittest
from report import report
class Public(unittest.TestCase):
    def test_header(self): self.assertEqual(report("category,amount\n"), [])

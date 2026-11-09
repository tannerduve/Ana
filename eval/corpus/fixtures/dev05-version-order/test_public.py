import unittest
from versions import compare
class Public(unittest.TestCase):
    def test_equal(self): self.assertEqual(compare("1", "1"), 0)

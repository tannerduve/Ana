import unittest
from inventory import summarize
class Public(unittest.TestCase):
    def test_empty(self): self.assertEqual(summarize([]), [])

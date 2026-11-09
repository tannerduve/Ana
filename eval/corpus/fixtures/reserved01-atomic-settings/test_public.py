import unittest
from transactions import apply
class Public(unittest.TestCase):
    def test_empty(self): self.assertEqual(apply({}, []), {})

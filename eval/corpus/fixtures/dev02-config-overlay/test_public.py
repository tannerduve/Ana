import unittest
from overlay import overlay
class Public(unittest.TestCase):
    def test_empty(self): self.assertEqual(overlay({}, {}), {})

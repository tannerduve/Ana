import unittest
from planner import plan
class Public(unittest.TestCase):
    def test_empty(self): self.assertEqual(plan({}), [])

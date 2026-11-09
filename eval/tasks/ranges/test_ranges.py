"""Visible regression tests. The evaluator also uses independent cases."""
import unittest

from ranges import parse_ranges


class ParseRangesTests(unittest.TestCase):
    def test_empty_input(self):
        self.assertEqual(parse_ranges("  "), [])

    def test_inclusive_range(self):
        self.assertEqual(parse_ranges("2-4"), [2, 3, 4])

    def test_sorted_unique(self):
        self.assertEqual(parse_ranges("3,1-3,2"), [1, 2, 3])

    def test_nonpositive_invalid(self):
        with self.assertRaises(ValueError):
            parse_ranges("0")


if __name__ == "__main__":
    unittest.main()

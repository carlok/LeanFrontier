from __future__ import annotations

import pathlib
import sys
import unittest
from datetime import date

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import collect_rejections as collector  # noqa: E402


class WeeklyCollection(unittest.TestCase):
    """The week logic, without GitHub: listings and reports are stubbed."""

    def setUp(self) -> None:
        self.original = collector.run_ids, collector.codes_of
        self.listed: list[date] = []
        weeks = {
            date(2026, 9, 14): [1, 2, 3],
            date(2026, 9, 21): [4, 5],
            date(2026, 9, 28): [6],
        }
        verdicts = {1: {"ACCEPTED"}, 2: {"SORRY", "BUILD_FAILED"}, 3: None, 4: {"ACCEPTED"}, 5: {"ACCEPTED"}, 6: {"SORRY"}}

        def run_ids(repository: str, week: date) -> list[int]:
            self.listed.append(week)
            return weeks.get(week, [])

        collector.run_ids = run_ids
        collector.codes_of = lambda repository, run_id: verdicts[run_id]

    def tearDown(self) -> None:
        collector.run_ids, collector.codes_of = self.original

    def test_each_closed_week_is_listed_once_and_counted(self) -> None:
        rows = collector.new_rows("o/r", collector.HEADER, today=date(2026, 9, 29), since=date(2026, 9, 14))
        self.assertEqual(rows, [
            "2026-09-14,ACCEPTED,1\n", "2026-09-14,BUILD_FAILED,1\n", "2026-09-14,SORRY,1\n",
            "2026-09-21,ACCEPTED,2\n",
        ])
        # The current week is not closed, so it is not even listed.
        self.assertEqual(self.listed, [date(2026, 9, 14), date(2026, 9, 21)])

    def test_recorded_weeks_are_not_listed_again(self) -> None:
        existing = collector.HEADER + "2026-09-14,ACCEPTED,1\n"
        rows = collector.new_rows("o/r", existing, today=date(2026, 9, 29), since=date(2026, 9, 14))
        self.assertEqual(rows, ["2026-09-21,ACCEPTED,2\n"])
        self.assertEqual(self.listed, [date(2026, 9, 21)])


if __name__ == "__main__":
    unittest.main()

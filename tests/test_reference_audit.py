"""Static integrity checks for the retained scholarly reference audit."""

from __future__ import annotations

import csv
import re
import unittest
from pathlib import Path


class ReferenceAuditTests(unittest.TestCase):
    def test_reference_inventory_is_complete_unique_and_canonically_located(self) -> None:
        path = Path(__file__).resolve().parents[1] / "reference_audit.csv"
        with path.open(newline="", encoding="utf-8") as handle:
            rows = list(csv.DictReader(handle))

        self.assertEqual(63, len(rows))
        keys = [row["key"] for row in rows]
        titles = [row["title"].casefold() for row in rows]
        locators = [row["canonical_locator"] for row in rows]
        self.assertEqual(len(keys), len(set(keys)))
        self.assertEqual(len(titles), len(set(titles)))
        self.assertEqual(len(locators), len(set(locators)))
        self.assertEqual(60, sum(row["locator_kind"] == "DOI" for row in rows))
        self.assertEqual(3, sum(row["locator_kind"] == "official_archive_URL" for row in rows))

        doi_pattern = re.compile(r"^https://doi\.org/10\.[0-9]{4,9}/\S+$", re.IGNORECASE)
        allowed_status = {
            "canonical_locator_and_bibliographic_consistency_checked",
            "publisher_or_official_archive_record_rechecked",
        }
        allowed_depth = {
            "metadata_and_claim_relevance_inspected",
            "substantive_or_targeted_text_inspection_recorded",
        }
        for row in rows:
            self.assertRegex(row["year"], r"^(19|20)\d{2}$")
            self.assertTrue(row["title"].strip())
            self.assertTrue(row["manuscript_role"].strip())
            self.assertIn(row["audit_status"], allowed_status)
            self.assertIn(row["content_review_depth"], allowed_depth)
            self.assertIn(row["access_date"], {"2026-09-16", "2026-09-20"})
            if row["locator_kind"] == "DOI":
                self.assertRegex(row["canonical_locator"], doi_pattern)
            else:
                self.assertTrue(row["canonical_locator"].startswith("https://"))


if __name__ == "__main__":
    unittest.main()

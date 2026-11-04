import unittest, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import bid_keeper as K

INST = {"actual_status": "running", "dph_base": 1.91, "machine_id": 151320}
def off(m, b, rel=0.99, g=4): return {"machine_id": m, "min_bid": b, "reliability2": rel, "num_gpus": g}

class T(unittest.TestCase):
    def test_raise_to_cheapest_comparable_plus_delta(self):
        t, why = K.decide(INST, [off(151320, 1.067), off(152044, 2.08), off(153538, 2.667), off(41635, 2.0, rel=0.68)], 2.70, 0.02)
        self.assertEqual(t, 2.10)                      # own machine and the 0.68-reliability box are not alternatives
    def test_lower_target_and_caps(self):
        self.assertEqual(K.decide(dict(INST, dph_base=2.687), [off(152044, 2.08)], 2.70, 0.02)[0], 2.10)   # the caller applies it after 3 polls
        self.assertIsNone(K.decide(dict(INST, dph_base=2.13), [off(152044, 2.08)], 2.70, 0.02)[0])         # within $0.05: keep
        self.assertEqual(K.decide(INST, [off(152044, 3.5)], 2.70, 0.02)[0], 2.70)
    def test_no_action_when_not_running_unreadable_or_no_alternative(self):
        self.assertIsNone(K.decide(dict(INST, actual_status="exited"), [off(152044, 2.08)], 2.7, 0.02)[0])
        self.assertIsNone(K.decide(None, [off(152044, 2.08)], 2.7, 0.02)[0])
        self.assertIsNone(K.decide(INST, None, 2.7, 0.02)[0])
        self.assertIsNone(K.decide(INST, [off(151320, 1.0), off(5, 1.5, g=2)], 2.7, 0.02)[0])

if __name__ == "__main__":
    unittest.main()


class Floor(unittest.TestCase):
    """2026-10-31 10:05 outbid at ~$2.26 while the keeper sat at the cheapest alternative + $0.02 = $2.10: --floor."""
    inst = {"actual_status": "running", "machine_id": 1}

    def test_floor_raises(self):
        t, _ = K.decide(dict(self.inst, dph_base=2.10), [off(2, 1.60)], cap=3.50, delta=0.02, floor=2.50)
        self.assertAlmostEqual(t, 2.50)

    def test_floor_blocks_lowering(self):
        t, _ = K.decide(dict(self.inst, dph_base=2.50), [off(2, 1.60)], cap=3.50, delta=0.02, floor=2.50)
        self.assertIsNone(t)

    def test_floor_capped(self):
        t, _ = K.decide(dict(self.inst, dph_base=2.10), [off(2, 1.60)], cap=2.40, delta=0.02, floor=2.50)
        self.assertAlmostEqual(t, 2.40)

    def test_no_floor_unchanged(self):
        t, _ = K.decide(dict(self.inst, dph_base=2.10), [off(2, 2.08)], cap=3.50, delta=0.02)
        self.assertIsNone(t)

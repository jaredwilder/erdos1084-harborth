"""Append the S1 / H3 / splice / model / defect nodes to the e1084 upper DAG.

Hand-append, exactly as the H3S2 node was appended by the preceding session: the
generator (MINE/e1084-upper/gen_dag.py) does not know about the H-rungs.  Every node
added here carries a kernel receipt path that exists on disk; nothing is asserted.
"""
import hashlib
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
UPPER = os.path.dirname(HERE)
DAG = os.path.join(UPPER, "erdos1084.upper.dag.json")
REL = "oracle/evidence/msl-machine/campaigns/erdos1084-harborth-2026-09-02/upper/"

BACKEND = ("box 51.158.234.15, /root/formalizer/proofs, lake env lean, "
           "Mathlib 919544d430, toolchain v4.31.0-rc1")
TRIPLE = ["propext", "Classical.choice", "Quot.sound"]
BINDING_DETAIL = ("a typed Lean obligation of the upper-bound ladder, stated over the "
                  "target's own verbatim definitions")


def sha(name):
    with open(os.path.join(UPPER, name), "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def node(nid, statement, depends, lean_file, signature, receipt, remaining,
         kind="LEMMA", status="PROVED_KERNEL", extra=None):
    d = {
        "id": nid,
        "statement": statement,
        "kind": kind,
        "depends_on": depends,
        "binding": "PARAPHRASE",
        "binding_detail": BINDING_DETAIL,
        "status": status,
        "obligation": "interior angles of a convex h-gon sum to (h-2)*pi.",
        "proof_status": "KERNEL_CHECKED",
        "remaining_obligation": remaining,
        "lean_file": REL + lean_file,
        "lean_signature": signature,
        "lean_file_sha256": sha(lean_file),
        "carries_sorry": False,
        "court": ["formalizer", "kernel"],
        "problem": "erdos1084",
        "supports": [],
        "receipt": "receipts-box-2026-09-05-s1/" + receipt,
        "receipt_kind": "AXIOM_PRINT",
        "axioms": list(TRIPLE),
        "backend": BACKEND,
        "supersedes": None,
        "is_not_a_close_of": None,
        "library_gap_closed": None,
        "needs_decomposition": False,
        "is_leaf": True,
        "manufacture_target": False,
    }
    if extra:
        d.update(extra)
    return d


NEW = [
    node(
        "erdos1084:UPPER:H3S1",
        "H3 OBLIGATION S1, PROVED, AFTER THREE STATEMENT REPAIRS. For a listing of "
        "EXTREME points of a convex set A, described in polar coordinates about a point "
        "v0 in A with STRICTLY DESCENDING arguments and every consecutive central gap "
        "strictly below pi, all three cross-product signs that s2_sides_to_polar consumes "
        "hold at every index: 0 < cross (p (i+1)) (p i) (p (i+2)), and the two positive "
        "products. METHOD: two of the three signs are FREE from the polar data alone "
        "(cross (p(i+1)) (p i) v0 = -r_i r_{i+1} sin(gap) and its mirror). Only the "
        "orientation cross (p(i+1)) (p i) (p(i+2)) needs convexity, and only when the two "
        "consecutive gaps sum to LESS than pi -- above pi it is free too. In that one "
        "case CRAMER writes the middle direction as lam*u + mu*w with lam, mu > 0, a "
        "non-positive turn forces lam + mu <= 1, and the middle point is then an interior "
        "convex combination of three points of A, contradicting extremality.",
        [],
        "H3_S1_Convexity.lean",
        "theorem s1_consecutive_signs (A) (hA : Convex R A) (v0) (hv0 : v0 in A) (p a r) "
        "(hext : forall i, p i in A.extremePoints R) (hr) (hp0) (hp1) "
        "(hpos : forall i, 0 < a i - a (i+1)) (hlt : forall i, a i - a (i+1) < pi) (i) : "
        "0 < cross (p (i+1)) (p i) (p (i+2)) and the two positive products",
        "S1_core.axioms.txt",
        "The gap ceiling hlt (every consecutive central gap STRICTLY below pi) is taken as "
        "a hypothesis. It is forced by v0 being INTERIOR to the hull -- a gap of exactly "
        "pi puts v0 on a chord with every other listed point in one closed half-plane, so "
        "that chord's line supports the hull and v0 lies on the frontier -- but that "
        "derivation is NOT kernel-proved here and is DECLARED UNPROVED.",
        extra={"supersedes": REL + "H3_Decomposition_SCAFFOLD.lean"},
    ),
    node(
        "erdos1084:UPPER:H3",
        "H3, PROVED. A listing of EXTREME points of a convex set A, sorted by strictly "
        "descending polar argument about a point v0 in A with every consecutive central "
        "gap strictly below pi, satisfies InsideAngleAt v0 p i at EVERY index. S1 composed "
        "with the sealed S2.",
        ["erdos1084:UPPER:H3S1", "erdos1084:UPPER:H3S2"],
        "H3_Assembled.lean",
        "theorem h3_hull_inside (A) (hA) (v0) (hv0) (p a r) (hext) (hr) (hp0) (hp1) "
        "(hpos) (hlt) : forall i, InsideAngleAt v0 p i",
        "H3_Assembled.axioms.txt",
        "Inherits H3S1's declared residue (the strict gap ceiling as hypothesis).",
        extra={"needs_decomposition": False, "is_leaf": False},
    ),
    node(
        "erdos1084:UPPER:H3X",
        "THE SPLICE, PROVED. The interior angles of a listing of EXTREME points of a "
        "convex set, described only by polar data about an interior point (strictly "
        "descending arguments, gaps strictly below pi, gap total 2pi, h-periodic), sum to "
        "(h-2)*pi. NOTHING about the angles is assumed: not the angle split at the vertex "
        "(hadd), not the cone containment (InsideAngleAt), not the central angle sum "
        "(hcentral). H3 feeds the sealed descending handoff o06_angle_sum_of_polar_fan_desc.",
        ["erdos1084:UPPER:H3", "erdos1084:UPPER:O06D"],
        "H3_Assembled.lean",
        "theorem e1084_hull_angle_sum (A) (hA) (h) (hh : 3 <= h) (v0) (hv0) (p a r) "
        "(hext) (hper) (hr) (hp0) (hp1) (hpos) (hlt) (hgap) : "
        "sum over range h of angle (p i) (p (i+1)) (p (i+2)) = (h-2)*pi",
        "H3_Assembled.axioms.txt",
        "This is NOT the FanInterface of H05_Assembly. FanInterface indexes hullPts S = "
        "the FRONTIER points of S; this theorem indexes EXTREME points. Mathlib has no "
        "extremePoints/frontier bridge (its own TODO, Extreme.lean:40) and the two sets "
        "genuinely differ when S has three collinear boundary points. Closing H05's fan "
        "branch needs (a) vertexPts subset hullPts and (b) a treatment of the non-extreme "
        "frontier points, which contribute interior angle exactly pi. BOTH ARE OPEN.",
        extra={"is_leaf": False},
    ),
    node(
        "erdos1084:UPPER:H3M",
        "THE MODEL, PROVED. Every hypothesis of the splice holds SIMULTANEOUSLY on the "
        "CLOCKWISE unit square listed about its centre, taken as extreme points of the "
        "closed unit BALL (a point of norm 1 is extreme by strict convexity -- this "
        "sidesteps Mathlib's missing extremePoints/frontier bridge entirely), and the "
        "theorem returns the square's interior-angle sum 2pi. The same value was sealed "
        "independently by the other route (o06_polar_fan_desc_model), so this is also a "
        "cross-check of the new path. NON-VACUITY IS THEREFORE NOT A CLAIM BUT A RECEIPT.",
        ["erdos1084:UPPER:H3X"],
        "H3_Assembled.lean",
        "theorem e1084_hull_angle_sum_square : sum over range 4 of "
        "angle (ww i) (ww (i+1)) (ww (i+2)) = (4-2)*pi",
        "H3_Assembled.axioms.txt",
        "None. The model is closed.",
        kind="MODEL",
    ),
    node(
        "erdos1084:UPPER:H3D",
        "THE TWO STATEMENT DEFECTS OF THE FROZEN S1, KERNEL-CHECKED. (A) ORIENTATION: "
        "under ASCENDING central arguments with strict gaps below pi -- which is what "
        "H3_Decomposition_SCAFFOLD froze -- cross (p (i+1)) (p i) v0 < 0 at every index, "
        "so the frozen conclusion FORCES cross (p (i+1)) (p i) (p (i+2)) < 0, the exact "
        "negation of s2_sides_to_polar's orientation hypothesis. The ascending S1 is not "
        "merely unproved: proved in full it could never be consumed. (B) FRONTIER IS NOT "
        "ENOUGH: if the middle listed point lies on the segment between its neighbours -- "
        "which a frontier point of S in the relative interior of a hull edge does -- then "
        "cross vanishes and BOTH frozen conclusion clauses (0 < _ * _) are FALSE.",
        [],
        "H3_S1_Defects.lean",
        "theorem ascending_defeats_hor (...) (hfrozen) : cross (p (i+1)) (p i) (p (i+2)) < 0 "
        "AND theorem collinear_kills_all_clauses (v0 X Y Z s) (hY : Y = (1-s)X + sZ) : "
        "cross Y X Z = 0 and not (0 < cross Y X v0 * cross Y X Z) and the mirror",
        "S1_Defects.axioms.txt",
        "Defect B is proved as a LOCAL fact about a collinear triple. The stronger claim "
        "-- that a finite S exists whose frozen hull hypotheses (S-membership, frontier "
        "membership, surjectivity, periodicity, polar sortedness) ALL hold with a "
        "collinear listed triple -- is NOT kernel-exhibited here and is DECLARED UNPROVED; "
        "it is supported only by the Python probes h3probe3/h3probe4 beside the scaffold.",
        kind="REFUTATION",
        extra={"is_not_a_close_of": "erdos1084:UPPER:H3S1"},
    ),
]


def main():
    with open(DAG, encoding="utf-8") as fh:
        dag = json.load(fh)
    have = {n["id"] for n in dag["nodes"]}
    added = [n for n in NEW if n["id"] not in have]
    dag["nodes"].extend(added)
    s = dag["summary"]
    s["nodes"] = len(dag["nodes"])
    s["proved_kernel"] = sum(1 for n in dag["nodes"] if n.get("status") == "PROVED_KERNEL")
    s["open"] = sum(1 for n in dag["nodes"] if n.get("status") == "OPEN")
    s["refuted"] = sum(1 for n in dag["nodes"] if n.get("status") == "REFUTED")
    s["hand_appended_h_rungs"] = sorted(
        n["id"] for n in dag["nodes"] if n["id"].startswith("erdos1084:UPPER:H3"))
    with open(DAG, "w", encoding="utf-8") as fh:
        json.dump(dag, fh, indent=1, ensure_ascii=False)
    print("added:", [n["id"] for n in added])
    print("nodes", s["nodes"], "proved_kernel", s["proved_kernel"],
          "open", s["open"], "refuted", s["refuted"])


if __name__ == "__main__":
    main()

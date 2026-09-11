"""Append the gap-1 / gap-2 / assembly nodes to the e1084 upper DAG.

Hand-append, exactly as dag_append_s1.py did one rung earlier: the generator does not
know about the H-rungs.  Every node added here carries a kernel receipt path that exists
on disk; nothing is asserted.

This script ALSO patches two existing nodes' `remaining_obligation` strings -- H3S1's
declared UNPROVED gap ceiling and H3X's "BOTH ARE OPEN" -- by PREPENDING a dated CLOSED
line naming the node that closes it.  The original text is preserved verbatim after it,
so the record shows what was claimed and what closed it.
"""
import hashlib
import json
import os
import shutil

HERE = os.path.dirname(os.path.abspath(__file__))
UPPER = os.path.dirname(HERE)
DAG = os.path.join(UPPER, "erdos1084.upper.dag.json")
REL = "oracle/evidence/msl-machine/campaigns/erdos1084-harborth-2026-09-02/upper/"
RCPT = "receipts-box-2026-09-05-gap1/"

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
        "receipt": RCPT + receipt,
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
        "erdos1084:UPPER:G1A",
        "GAP 1a, PROVED: AN EXTREME POINT IS ON THE FRONTIER, and the hull of a finite S "
        "is the hull of its FRONTIER points. Mathlib records the extremePoints/frontier "
        "bridge as its own TODO (Extreme.lean:40, Exposed.lean:41). The cheap direction "
        "needs NO supporting hyperplane: an interior point of A has a ball around it, so "
        "it is the midpoint of two DISTINCT points of A, which extremality forbids; being "
        "in A it is in the closure, hence in frontier = closure minus interior. Krein-"
        "Milman then upgrades this to convexHull S subset convexHull (hullPts S), because "
        "the hull of a finite set is compact and the hull of the (finite) extreme set is "
        "closed. THIS IS THE COVERING THE GAP CEILING NEEDS.",
        [],
        "H3G_Frontier.lean",
        "theorem extremePoint_mem_frontier (A) (x) (hx : x in A.extremePoints R) : "
        "x in frontier A  AND  theorem vertexPts_subset_hullPts (S) : "
        "vertexPts S subset hullPts S  AND  theorem convexHull_subset_hullPts (S) : "
        "convexHull R S subset convexHull R (hullPts S)",
        "H3G_Frontier.axioms.txt",
        "None for the stated direction. The CONVERSE (a frontier point is extreme) is "
        "FALSE in general and is not claimed: that is precisely why gap 1b exists.",
        extra={"library_gap_closed": "Mathlib TODO: no extremePoints/frontier bridge "
                                     "(Analysis/Convex/Extreme.lean:40) -- one direction."},
    ),
    node(
        "erdos1084:UPPER:G1B",
        "GAP 1b, PROVED: THE DEGENERATE BRANCH. S1 and S2 re-proved with the STRICT turn "
        "relaxed to 0 <= cross (p(i+1)) (p i) (p(i+2)), and with EXTREMALITY REPLACED by "
        "the two facts hullPts actually gives: the centre v0 is INTERIOR to A and every "
        "listed point is NOT. METHOD: the two side signs stay strictly free from the polar "
        "data. For the turn, a STRICTLY right turn makes Cramer's lam + mu STRICTLY below "
        "1, so p(i+1) lies on an OPEN SEGMENT from the interior point v0 to a point of A, "
        "hence in interior A (Convex.openSegment_interior_self_subset_interior) -- "
        "forbidden. A straight turn is now ADMITTED, and S2 handles it: at cross = 0 the "
        "two consecutive arguments differ by exactly pi, so gamma - alpha = pi and "
        "InsideAngleAt still holds. The flat vertex carries interior angle exactly pi.",
        ["erdos1084:UPPER:H3S2"],
        "H3G_Frontier.lean",
        "theorem s2_sides_to_polar_ge (v X Y Z) (hut : 0 < cross Y X v) "
        "(htw : 0 < cross Y v Z) (hor : 0 <= cross Y X Z) (p i) (...) : InsideAngleAt v p i "
        "AND theorem s1_frontier_signs (A) (hA) (v0) (hv0 : v0 in interior A) (p a r) "
        "(hmem : forall i, p i in A) (hfr : forall i, p i not in interior A) (hr) (hp0) "
        "(hp1) (hpos) (hlt) (i) : 0 < cross (p(i+1)) (p i) v0 and 0 < cross (p(i+1)) v0 "
        "(p(i+2)) and 0 <= cross (p(i+1)) (p i) (p(i+2)) "
        "AND theorem h3_frontier_inside (...) : forall i, InsideAngleAt v0 p i",
        "H3G_Frontier.axioms.txt",
        "The gap ceiling hlt is still a hypothesis HERE; it is closed one node over by "
        "erdos1084:UPPER:G2, which is what fanInterface_of_polarFan consumes.",
        extra={"is_leaf": False,
               "supersedes": REL + "H3_Assembled.lean (s1_consecutive_signs, extreme-only)"},
    ),
    node(
        "erdos1084:UPPER:G1X",
        "THE FRONTIER SPLICE, PROVED. The interior angles of a listing of FRONTIER points "
        "of a convex set -- described only by polar data about an INTERIOR point (strictly "
        "descending arguments, gaps strictly below pi, gap total 2pi, h-periodic) -- sum to "
        "(h-2)*pi. Non-extreme (flat) listed points are admitted. e1084_hullPts_angle_sum "
        "states it over hullPts S, VERBATIM the index H05_Assembly's FanInterface uses. "
        "THIS IS THE STATEMENT H3X COULD NOT MAKE.",
        ["erdos1084:UPPER:G1A", "erdos1084:UPPER:G1B", "erdos1084:UPPER:O06D"],
        "H3G_Frontier.lean",
        "theorem e1084_frontier_angle_sum (A) (hA) (h) (hh : 3 <= h) (v0) "
        "(hv0 : v0 in interior A) (p a r) (hmem) (hfr) (hper) (hr) (hp0) (hp1) (hpos) "
        "(hlt) (hgap) : sum over range h of angle (p i) (p (i+1)) (p (i+2)) = (h-2)*pi "
        "AND theorem e1084_hullPts_angle_sum (S : Finset) (...) (hmem : forall i, "
        "p i in hullPts S) (...) : same conclusion",
        "H3G_Frontier.axioms.txt",
        "None at this rung beyond its own hypotheses. The listing itself (theta-injectivity "
        "of hull points seen from an interior point) is STILL NOT CONSTRUCTED -- see "
        "erdos1084:UPPER:H05F's residue.",
        extra={"is_leaf": False},
    ),
    node(
        "erdos1084:UPPER:G1M",
        "THE DEGENERATE MODEL, PROVED. A listing containing a NON-EXTREME frontier point "
        "is run end to end through the frontier splice: A = the strip |y| <= 1, centre the "
        "origin, listing = the four corners of the square PLUS the midpoint (0,1) of its "
        "top edge, at polar angles pi/2, pi/4, -pi/4, -3pi/4, -5pi/4 (gaps pi/4, pi/2, "
        "pi/2, pi/2, pi/4 summing to 2pi). h = 5 and the theorem returns 3pi. TWO SEPARATE "
        "RECEIPTS MAKE THE DEGENERACY REAL, NOT DECORATIVE: flat_cross_zero proves "
        "cross (qq 5) (qq 4) (qq 6) = 0 -- the STRICT cross product concluded by the sealed "
        "extreme-point route s1_consecutive_signs is FALSE here, so this configuration is "
        "provably outside it -- and flat_angle_pi proves the flat vertex carries interior "
        "angle exactly pi. NON-VACUITY OF THE DEGENERATE BRANCH IS A RECEIPT, NOT A CLAIM.",
        ["erdos1084:UPPER:G1X"],
        "H3G_FlatModel.lean",
        "theorem e1084_flat_model : sum over range 5 of angle (qq i) (qq (i+1)) (qq (i+2)) "
        "= (5-2)*pi  AND  theorem flat_cross_zero : cross (qq 5) (qq 4) (qq 6) = 0 "
        "AND theorem flat_angle_pi : angle (qq 4) (qq 5) (qq 6) = pi",
        "H3G_FlatModel.axioms.txt",
        "None. The model is closed. It also retires the existential half of defect (C) "
        "recorded at erdos1084:UPPER:H3D for the FRONTIER statement: a listing with a "
        "collinear triple satisfying every hypothesis simultaneously is now EXHIBITED in "
        "the kernel, not merely probed in Python. (H3D's own claim was about the FROZEN "
        "scaffold's hull hypotheses over a Finset S, which is a different statement and "
        "stays as recorded.)",
        kind="MODEL",
    ),
    node(
        "erdos1084:UPPER:G2",
        "GAP 2, PROVED: THE STRICT GAP CEILING IS A THEOREM, NOT A HYPOTHESIS. If one "
        "consecutive central gap reached pi, then -- the gaps being positive and summing "
        "to 2pi over one period -- every listed point would have polar angle in "
        "[a(k+1) - pi, a(k+1)], so the functional x |-> <x - v0, n> with n at angle "
        "a(k+1) + pi/2 takes the value r_j * sin(angle_j - a(k+1)) <= 0 at every listed "
        "point. The half-plane is convex, so it contains the hull of the listing, hence "
        "(by the covering) A itself; v0 sits ON its bounding line, so no ball around v0 "
        "fits in A, contradicting v0 INTERIOR. gap_lt_pi_hullPts then DISCHARGES the "
        "covering hypothesis from erdos1084:UPPER:G1A plus the surjectivity onto hullPts "
        "that FanInterface already demands -- the consumer supplies nothing new.",
        ["erdos1084:UPPER:G1A"],
        "G2_GapCeiling.lean",
        "theorem gap_lt_pi (A) (h) (v0) (hv0 : v0 in interior A) (p a r) (hr) (hp0) (hp1) "
        "(hpos) (hper) (hpera : forall i, a (i+h) = a i - 2*pi) "
        "(hcov : A subset convexHull R (p '' Icc 1 h)) (k) (hk : k < h) : "
        "a k - a (k+1) < pi   AND   theorem gap_lt_pi_hullPts (S : Finset) (...) "
        "(hsurj : forall w in hullPts S, exists i < h, p (i+1) = w) (k) (hk) : same",
        "G2_GapCeiling.axioms.txt",
        "None. Note what it does NOT need: no supporting-hyperplane API, no separation "
        "theorem, no Mathlib frontier characterisation. It needs the argument function to "
        "be 2pi-periodic over the period (hpera), which any closed listing carries.",
        extra={"supersedes": None,
               "is_not_a_close_of": None},
    ),
    node(
        "erdos1084:UPPER:H05",
        "H05 PRE-ASSEMBLY, PROVED (node added 2026-09-05; the theorem was sealed earlier "
        "the same day but had never been entered in the DAG). The package conclusion "
        "follows from the aggregate bound sum over hullPts of udeg <= 4h-6, and BOTH "
        "branches deliver it: the degenerate branch via udeg <= 2, the fan branch via one "
        "sum_bij reindex plus the per-vertex packing bound. Reproduced VERBATIM (namespace "
        "dropped) inside H05G_Assembly.lean and re-verified there.",
        [],
        "H05_Assembly.lean",
        "theorem hull_angle_package_pre (S) (h) (hh : h = (hullPts S).card) (h3 : 3 <= h) "
        "(hbranch : (forall v in S, udeg S v <= 2) or FanInterface S h) : "
        "exists alpha, (forall v in hullPts S, udeg S v <= 1 + 3*alpha v/pi) and "
        "(sum over hullPts of alpha = (h-2)*pi)",
        "H05G_Assembly.axioms.txt",
        "FanInterface was an ASSUMED interface when this was sealed. It is produced from "
        "polar data at erdos1084:UPPER:H05F.",
        extra={"is_leaf": False},
    ),
    node(
        "erdos1084:UPPER:H05F",
        "H05'S FAN BRANCH, PRODUCED FROM POLAR DATA. FanInterface S h -- whose interior-"
        "angle-sum clause H05_Assembly could only ASSUME -- now FOLLOWS from a closed polar "
        "listing of hullPts about an interior centre plus the per-vertex packing bound. "
        "Discharged inside: the angle sum (G1X), the angle split at each vertex (G1B), the "
        "central total 2pi (telescoping, gap_sum_of_period), the strict gap ceiling at "
        "EVERY index (G2 plus gap_periodic), and the covering (G1A). "
        "hull_angle_package_of_polar then delivers H05's package conclusion with the fan "
        "branch replaced by PolarFan.",
        ["erdos1084:UPPER:G1X", "erdos1084:UPPER:G2", "erdos1084:UPPER:H05"],
        "H05G_Assembly.lean",
        "theorem fanInterface_of_polarFan (S) (h) (hh : 3 <= h) (hpf : PolarFan S h) : "
        "FanInterface S h   AND   theorem hull_angle_package_of_polar (S) (h) "
        "(hh : h = (hullPts S).card) (h3 : 3 <= h) "
        "(hbranch : (forall v in S, udeg S v <= 2) or PolarFan S h) : "
        "exists alpha, (forall v in hullPts S, udeg S v <= 1 + 3*alpha v/pi) and "
        "(sum over hullPts of alpha = (h-2)*pi)",
        "H05G_Assembly.axioms.txt",
        "TWO INPUTS OF PolarFan REMAIN OPEN AND ARE NOT CLAIMED HERE. (1) THE CONSTRUCTION "
        "OF THE LISTING: that the frontier points of S admit an h-periodic, strictly "
        "descending, injective-and-surjective polar listing about some interior v0 "
        "(theta-injectivity, Risk 3 of the API map) -- PolarFan takes it as given. (2) THE "
        "PER-VERTEX PACKING BOUND udeg <= 1 + 3*alpha/pi at the listed aperture: H04's "
        "h4_cone_packing is SEALED but its instantiation at the listed angle is not. Also "
        "unchanged: hcentral at m <= 3 (Contract C section 3) for the OTHER route.",
        extra={"is_leaf": False},
    ),
]

PATCH = {
    "erdos1084:UPPER:H3S1": (
        "CLOSED 2026-09-05 by erdos1084:UPPER:G2 (gap_lt_pi / gap_lt_pi_hullPts, "
        "kernel-checked): the strict gap ceiling is now a THEOREM for any closed listing "
        "whose hull covers A about an interior centre. ORIGINAL RESIDUE, preserved: "),
    "erdos1084:UPPER:H3X": (
        "CLOSED 2026-09-05 by erdos1084:UPPER:G1A (vertexPts subset hullPts) and "
        "erdos1084:UPPER:G1B/G1X (the degenerate branch and the frontier splice), modelled "
        "at erdos1084:UPPER:G1M and consumed at erdos1084:UPPER:H05F. ORIGINAL RESIDUE, "
        "preserved: "),
}


def main():
    shutil.copy(DAG, os.path.join(HERE, "erdos1084.upper.dag.json.bak"))
    with open(DAG, encoding="utf-8") as fh:
        dag = json.load(fh)
    have = {n["id"] for n in dag["nodes"]}
    added = [n for n in NEW if n["id"] not in have]
    dag["nodes"].extend(added)
    patched = []
    for n in dag["nodes"]:
        pre = PATCH.get(n["id"])
        if pre and not n.get("remaining_obligation", "").startswith("CLOSED 2026-09-05"):
            n["remaining_obligation"] = pre + n.get("remaining_obligation", "")
            patched.append(n["id"])
    s = dag["summary"]
    s["nodes"] = len(dag["nodes"])
    s["proved_kernel"] = sum(1 for n in dag["nodes"] if n.get("status") == "PROVED_KERNEL")
    s["open"] = sum(1 for n in dag["nodes"] if n.get("status") == "OPEN")
    s["refuted"] = sum(1 for n in dag["nodes"] if n.get("status") == "REFUTED")
    s["hand_appended_h_rungs"] = sorted(
        n["id"] for n in dag["nodes"]
        if n["id"].startswith("erdos1084:UPPER:H3")
        or n["id"].startswith("erdos1084:UPPER:G")
        or n["id"] == "erdos1084:UPPER:H05F")
    with open(DAG, "w", encoding="utf-8") as fh:
        json.dump(dag, fh, indent=1, ensure_ascii=False)
    print("added:", [n["id"] for n in added])
    print("patched:", patched)
    print("nodes", s["nodes"], "proved_kernel", s["proved_kernel"],
          "open", s["open"], "refuted", s["refuted"])


if __name__ == "__main__":
    main()

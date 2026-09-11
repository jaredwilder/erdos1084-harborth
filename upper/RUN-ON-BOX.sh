#!/usr/bin/env bash
# erdos:1084 upper-bound ladder -- box runner.
#
# Every file in this directory is SELF-CONTAINED: `import Mathlib`, its own copy of the
# target's verbatim definitions, exactly one theorem.  There is no shared module and no
# build order dependency at the LEAN level.  COMPILE_ORDER below is the order in which a
# HUMAN should read the results: leaves first, so that a failure lands on the smallest
# statement that can carry it.
#
# A file whose header says LADDER_ATTEMPT is expected to compile with exit 0 and NO
# `sorry` in `#print axioms`.  A file named *_SCAFFOLD.lean is expected to compile with
# exit 0 and `sorryAx` PRESENT -- that is the point of a scaffold, and a scaffold that
# compiles has had its STATEMENT type-checked even though its proof has not been given.
#
# ⛔ A scaffold that fails to compile is a STATEMENT defect, and is the more urgent bug.

set -u

BOX=${BOX:-root@51.15.107.148}
REMOTE=${REMOTE:-/root/peer/e1084-upper}
MATHLIB=${MATHLIB:-/root/mathlib4}

COMPILE_ORDER=(
  O02b_ArccosCosLeAbs.lean
  O02e_CyclicGapSum.lean
  O02a_PolarCoordinates.lean
  O02d_UnitChordIdentity.lean
  O01_SixtyDegreeGap.lean
  O02c_AngleLeArgGap.lean
  O02f_GapBoundCardLeSix.lean
  O03_InteriorDegreeLeSix.lean
  O08_Handshake.lean
  O10_Assemble.lean
  O11_TriangularOptimalD2.lean
  O04_SupportingLine_SCAFFOLD.lean
  O06_ConvexPolygonAngleSum_SCAFFOLD.lean
  O02_CyclicAngularOrder_SCAFFOLD.lean
  O05_DegreeSumBound_SCAFFOLD.lean
  O07_HullSizeLowerBound_SCAFFOLD.lean
  O09_UnitDistNumEqEdges_SCAFFOLD.lean
  L01_IdxCard_SCAFFOLD.lean
  L02_IdxUnitNum_SCAFFOLD.lean
)

ssh "$BOX" "mkdir -p $REMOTE $REMOTE/receipts"
scp "$(dirname "$0")"/*.lean "$BOX:$REMOTE/"

for f in "${COMPILE_ORDER[@]}"; do
  echo "=== $f"
  ssh "$BOX" "cd $MATHLIB && export PATH=/root/.elan/bin:\$PATH && \
    /usr/bin/time -f '%e s' lake env lean $REMOTE/$f > $REMOTE/receipts/$f.log 2>&1; \
    echo \"exit \$?\"; tail -40 $REMOTE/receipts/$f.log"
done

echo
echo "Pull the receipts back into upper/receipts/ and, for every file that came back"
echo "exit 0 with clean axioms, flip its DAG node in erdos1084.upper.dag.json from"
echo "OPEN to PROVED_KERNEL with receipt_kind VERIFY_JSON.  msl_obligation_dag's"
echo "_gate_kernel_receipt re-reads the receipt on every later emission, so a receipt"
echo "that stops being true stops producing a node."

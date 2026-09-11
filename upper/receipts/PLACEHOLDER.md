# erdos:1084 upper-bound ladder — receipts

**THIS DIRECTORY IS EMPTY OF RECEIPTS ON PURPOSE.** There is no Lean toolchain on the
authoring machine, so nothing here has been compiled. Every `.lean` file one level up
passed **offline structural checks only**.

⛔ **An absent receipt is not a pending receipt.** Until a file in this directory carries
a `*.verify.json` with `status: VERIFIED` and `exitCode: 0`, the matching DAG node stays
`OPEN`, and `msl_obligation_dag._gate_kernel_receipt` will refuse any attempt to mark it
`PROVED_KERNEL`.

## What each compiled file must deposit here

For a file `X.lean` in `../`:

| artifact | content |
|---|---|
| `X.verify.json` | `{"status":"VERIFIED","exitCode":0,"seconds":…,"sha256":…,"declarations":[{"declaration":…,"axioms":[…]}],"errors":[]}` — same shape as `../../kernel/Erdos1084Lower.verify.json` |
| `X.axioms.txt` | the raw `#print axioms` output |
| `X.sha256` | `<sha256>  X.lean` — must match `lean_file_sha256` in `../erdos1084.upper.dag.json` |
| `X.lean.log` | the full `lake env lean` stdout/stderr |

## The honesty law for this ladder

- `LADDER_ATTEMPT` file → **expected** exit 0, and `#print axioms` showing only
  `propext, Classical.choice, Quot.sound`. **`sorryAx` in a LADDER_ATTEMPT file is a
  defect, not a partial result.**
- `*_SCAFFOLD.lean` → **expected** exit 0 **with `sorryAx` present**. The scaffold's
  value is that its *statement* type-checks. A scaffold that fails to compile is a
  **statement** defect and is the more urgent bug of the two.
- No `native_decide` anywhere. The lower-bound half was sealed with kernel `decide`; the
  upper-bound half uses no evaluation at all.

Generated 2026-09-02 by the upper-bound ladder pass. Run `../RUN-ON-BOX.sh` to fill it.

# Tutorial-path defect log

Per the falsification protocol in `NEXTSTEPS.md` ("'Easy' gets a
falsification protocol"): every time an executor of `TUTORIAL.md` has to
leave the documented path — read library source, guess a name, hit an
undocumented requirement — the excursion is recorded here as a defect
against the library or the documentation, not as user error.

## Run 1 — 2026-07-28, maintainer-adjacent executor (Claude, this repo's
working agent), building `SatCounter.lean` before the tutorial existed

Caveat on this run's evidential weight: it was executed *to write* the
tutorial, by an agent with full source access, so it bounds the defect list
from below. The protocol still requires a genuinely fresh human executor; a
maintainer-adjacent run finding N defects means a stranger would find at
least N.

1. **No generic emit entry point.** [ADDRESSED 2026-07-29:
   `Loom.Hw.Design.emit` (`Loom/Hw/EmitIO.lean`) — one call, compiles and
   prints via the verified functions; tutorial §5 and this repo's
   SatCounter now use it.] `lake exe emit` accepts only
   `acc8|lnp64u` (`Tools/Emit.lean:143`); a new design cannot be emitted by
   the shipped CLI at all. Excursion: read `Tools/Emit.lean` to learn the
   printing API, then wrote a per-design `main`. The tutorial now documents
   the per-design `main` as the path, but the library should grow
   `Loom.Hw.Design.emit : Design → System.FilePath → IO Unit` (or an
   `emit <module>` CLI) so the user writes zero IO code.
2. **`lake env lean --run` requires a root-level `main`; nothing says so.**
   First attempt defined `main` inside the design's namespace and failed
   with the opaque `(interpreter) unknown declaration 'main'`. Excursion:
   compared against `GeneratedRelease/*/CertGen.lean`. Documented in the
   tutorial; the error message is the defect.
3. **Proof friction: user definitions must be fed to `simp` by hand.** The
   invariant proof stalls on a raw
   `List.foldl (fun acc r => Act.run s r.body acc) s design.rules` goal
   until `design` (and the rule and `Expr` shorthands) are added to the
   simp set. A first-time user has no way to know a `List.foldl` goal means
   "unfold your own definitions". Excursions: two failed `simp` variants
   before the working incantation. Fix candidates: `@[simp]` unfolding
   lemmas for `Design.cycle` over literal rule lists, or a small
   `cycle_simp` simp-set/tactic shipped by the library and named in the
   tutorial.
4. **Init-hypothesis shape is unobvious.** `design.toTSys.init s` unfolds
   to `s = design.reset` only after `TSys.ofFun` is understood; the working
   proof needs the `have : s = design.reset := hinit; subst this` two-step.
   Minor, but a `Design.toTSys_init_iff` simp lemma would remove it.
5. **Lint churn during iteration.** `linter.unusedSimpArgs` and
   `linter.unnecessarySimpa` fire on intermediate proof states, adding
   noise while the proof is still converging. Not a correctness issue;
   worth a note in the tutorial if it confuses a first-timer.

Total: 5 defects, 0 blockers — the path completes without touching any
file outside the user's own, and the final artifact checks with the
three-axiom closure.

## Run 2 — pending

The protocol's real test: a person who has never seen this repository,
given only `TUTORIAL.md` and a clean checkout. Record wall-time and every
intervention here.

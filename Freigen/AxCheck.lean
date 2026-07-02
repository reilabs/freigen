import Freigen.Examples.Circuit
import Freigen.Examples.Storage
import Freigen.Examples.Recursion

/-!
# Axiom guard

Pins the axiom footprint of the key soundness theorems — the reflector-generated `*_sound` proofs
(one per arm: value, function, helper-calling, recursion) and the core `≈`/`mrec` lemmas — to
exactly the three standard axioms.  A stray `sorry` (`sorryAx`), `native_decide`
(`Lean.ofReduceBool`), or new axiom anywhere in a soundness path fails this module, and the
lakefile's `Freigen.+` glob makes CI build it.
-/

namespace Freigen

/-- info: 'Freigen.circC_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms circC_sound

/-- info: 'Freigen.vgetSymC_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vgetSymC_sound

/-- info: 'Freigen.viaHelperC_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms viaHelperC_sound

/-- info: 'Freigen.storeC_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms storeC_sound

/-- info: 'Freigen.countdownC_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms countdownC_sound

/-- info: 'Freigen.smC_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms smC_sound

/-- info: 'Freigen.sumAccC_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sumAccC_sound

/-- info: 'Freigen.countAssertsC_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms countAssertsC_sound

/-- info: 'Freigen.ITree.Eutt.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ITree.Eutt.trans

/-- info: 'Freigen.recSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms recSound

/-- info: 'Freigen.ITree.interp_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ITree.interp_bind

end Freigen


import ConnesRigidity.PropertyTExactCertificateOrbitRadixPackedOrbitSoundness

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators

set_option maxRecDepth 1000000

noncomputable def orbitRadixPackedGramOrbitBoundCheck : Nat → Nat → Bool
  | 0, _ => true
  | remaining + 1, index =>
      decide
          (|congruenceInverseScale ^ 2 *
            orbitRadixPackedGramOrbitValue index| ≤
              orbitRadixScaledGramBound) &&
        orbitRadixPackedGramOrbitBoundCheck remaining (index + 1)

set_option maxHeartbeats 0 in

theorem orbitRadixPackedGramOrbitBoundCheck_valid :
    orbitRadixPackedGramOrbitBoundCheck 2256 0 = true := by
  decide +kernel

theorem orbitRadixPackedGramOrbitBoundCheck_get
    (remaining start index : Nat)
    (hindex : index < remaining)
    (hcheck : orbitRadixPackedGramOrbitBoundCheck remaining start = true) :
    |congruenceInverseScale ^ 2 *
      orbitRadixPackedGramOrbitValue (start + index)| ≤
        orbitRadixScaledGramBound := by
  induction remaining generalizing start index with
  | zero => omega
  | succ remaining ih =>
      simp only [orbitRadixPackedGramOrbitBoundCheck,
        Bool.and_eq_true, decide_eq_true_eq] at hcheck
      cases index with
      | zero => simpa only [Nat.add_zero] using hcheck.1
      | succ index =>
          have hindex' : index < remaining := by omega
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (start + 1) index hindex' hcheck.2

theorem orbitRadixGramOrbitCoefficient_abs_le
    (index : Nat) (hindex : index < gramOrbitData.size) :
    |congruenceInverseScale ^ 2 * gramOrbitCoefficient index| ≤
      orbitRadixScaledGramBound := by
  have hcount : index < 2256 := by
    simpa [gramOrbitData_size] using hindex
  have hbound := orbitRadixPackedGramOrbitBoundCheck_get
    2256 0 index hcount orbitRadixPackedGramOrbitBoundCheck_valid
  simpa only [Nat.zero_add,
    orbitRadixPackedGramOrbitValue_eq_gramOrbitCoefficient index hcount]
    using hbound

end ConnesRigidity.AffineSymplecticOrbitCertificate

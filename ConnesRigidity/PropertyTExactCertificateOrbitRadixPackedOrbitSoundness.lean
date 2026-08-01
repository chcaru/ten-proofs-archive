


import ConnesRigidity.PropertyTExactCertificateOrbitRadixData
import ConnesRigidity.PropertyTExactCertificateOrbitRadixCheckers
import ConnesRigidity.PropertyTExactCertificateOrbitIncidenceValidation












namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators

set_option maxRecDepth 1000000


def orbitRadixPackedSignedValue (packed : Int) (index : Nat) : Int :=
  (((packed.toNat >>> (64 * index)) % 18446744073709551616 : Nat) : Int) -
    9223372036854775808


noncomputable def orbitRadixPackedGramOrbitValues : Int :=
  (radixPackedGramOrbitValueData.getD 0 []).getD 0 0


noncomputable def orbitRadixPackedGramOrbitValue (index : Nat) : Int :=
  orbitRadixPackedSignedValue orbitRadixPackedGramOrbitValues index



noncomputable def orbitRadixPackedGramOrbitCrossCheck : Nat → Nat → Bool
  | 0, _ => true
  | remaining + 1, index =>
      decide
          (orbitRadixPackedGramOrbitValue index =
            orbitPackedIntEntry packedGramCoefficients 55 index) &&
        orbitRadixPackedGramOrbitCrossCheck remaining (index + 1)

set_option maxHeartbeats 0 in

theorem orbitRadixPackedGramOrbitCrossCheck_valid :
    orbitRadixPackedGramOrbitCrossCheck 2256 0 = true := by
  decide +kernel



theorem orbitRadixPackedGramOrbitCrossCheck_get
    (remaining start index : Nat)
    (hindex : index < remaining)
    (hcheck : orbitRadixPackedGramOrbitCrossCheck remaining start = true) :
    orbitRadixPackedGramOrbitValue (start + index) =
        orbitPackedIntEntry packedGramCoefficients 55 (start + index) := by
  induction remaining generalizing start index with
  | zero => omega
  | succ remaining ih =>
      simp only [orbitRadixPackedGramOrbitCrossCheck,
        Bool.and_eq_true, decide_eq_true_eq] at hcheck
      cases index with
      | zero =>
          simpa only [Nat.add_zero] using hcheck.1
      | succ index =>
          have hindex' : index < remaining := by omega
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (start + 1) index hindex' hcheck.2



theorem orbitRadixPackedGramOrbitValue_eq_gramOrbitCoefficient
    (index : Nat) (hindex : index < 2256) :
    orbitRadixPackedGramOrbitValue index = gramOrbitCoefficient index := by
  have hactual : index < gramOrbitData.size := by
    simpa [gramOrbitData_size] using hindex
  have hpacked :=
    orbitRadixPackedGramOrbitCrossCheck_get
      2256 0 index hindex orbitRadixPackedGramOrbitCrossCheck_valid
  have hpacked' :
      orbitRadixPackedGramOrbitValue index =
        orbitPackedIntEntry packedGramCoefficients 55 index := by
    simpa only [Nat.zero_add] using hpacked
  have hincidence :=
    (orbitPackedGramColumns_eq_dataEntry index hactual).2.2
  simpa [gramOrbitCoefficient] using hpacked'.trans hincidence.symm

end ConnesRigidity.AffineSymplecticOrbitCertificate

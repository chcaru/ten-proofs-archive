


import ConnesRigidity.PropertyTExactCertificateOrbitPairWitnessValidation
import ConnesRigidity.PropertyTExactCertificateOrbitRadixPackedOrbitSoundness













namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0



def orbitRadixNormalizedGramEntriesCheck
    (packed : Int) : Nat → List Int → List Int → Bool
  | _, [], [] => true
  | column, value :: values, orbit :: orbits =>
      decide (0 ≤ orbit ∧ orbit < (2256 : Int)) &&
        decide (value = orbitRadixPackedGramOrbitValue orbit.toNat) &&
        decide (value = orbitRadixPackedSignedValue packed column) &&
        orbitRadixNormalizedGramEntriesCheck packed
          (column + 1) values orbits
  | _, _, _ => false




def orbitRadixNormalizedGramRowCheck (index : Nat) : Bool :=
  match radixNormalizedGramRowData[index]?,
      radixPackedNormalizedGramRowData[index]?,
      pairOrbitIndexData[index]? with
  | some (row :: entries), some [packedRow, packed], some orbits =>
      decide (row = (index : Int)) &&
        decide (packedRow = (index : Int)) &&
        decide (entries.length = 425) &&
        decide (orbits.size = 425) &&
        orbitRadixNormalizedGramEntriesCheck packed 0
          entries orbits.toList
  | _, _, _ => false



def orbitRadixDenseGramEntriesCheck
    (packed : Int) (permutation : Nat) : Nat → List Int → Bool
  | _, [] => true
  | column, value :: values =>
      decide
          (value = orbitRadixPackedSignedValue packed
            (pairWitnessPackedIndex permutation (column + 1))) &&
        orbitRadixDenseGramEntriesCheck packed permutation
          (column + 1) values




def orbitRadixDenseGramRowCheck (index : Nat) : Bool :=
  match radixDenseReducedGramRowData[index]?,
      basisTransporterData[index + 1]? with
  | some (stored :: entries), some transporter =>
      let orbit := (transporter.getD 0 0).toNat
      let symmetry := (transporter.getD 1 0).toNat
      let inverse := inverseSymmetry symmetry
      match radixPackedNormalizedGramRowData[orbit]? with
      | some [packedOrbit, packed] =>
          decide (stored = (index : Int)) &&
            decide (entries.length = 424) &&
            decide (orbit < 26) &&
            decide (symmetry < 64) &&
            decide (inverse < 64) &&
            decide (packedOrbit = (orbit : Int)) &&
            orbitRadixDenseGramEntriesCheck packed
              (pairWitnessPackedPermutationRows.getD inverse 0)
              0 entries
      | _ => false
  | _, _ => false


theorem orbitRadixNormalizedGramEntriesCheck_get
    (packed : Int) (entries orbits : List Int)
    (start index : Nat) (hindex : index < entries.length)
    (hcheck : orbitRadixNormalizedGramEntriesCheck packed
      start entries orbits = true) :
    ∃ horbit : index < orbits.length,
      0 ≤ orbits[index] ∧ orbits[index] < (2256 : Int) ∧
      entries[index] =
        orbitRadixPackedGramOrbitValue orbits[index].toNat ∧
      entries[index] =
        orbitRadixPackedSignedValue packed (start + index) := by
  induction entries generalizing orbits start index with
  | nil => simp at hindex
  | cons entry entries ih =>
      cases orbits with
      | nil => simp [orbitRadixNormalizedGramEntriesCheck] at hcheck
      | cons orbit orbits =>
          simp only [orbitRadixNormalizedGramEntriesCheck,
            Bool.and_eq_true, decide_eq_true_eq] at hcheck
          cases index with
          | zero =>
              exact ⟨by simp, hcheck.1.1.1.1,
                hcheck.1.1.1.2, hcheck.1.1.2,
                by simpa using hcheck.1.2⟩
          | succ index =>
              have hindex' : index < entries.length := by simpa using hindex
              obtain ⟨horbit, hnonnegative, hbound, hvalue, hpacked⟩ :=
                ih orbits (start + 1) index hindex' hcheck.2
              refine ⟨by simpa using horbit, ?_, ?_, ?_, ?_⟩
              · simpa using hnonnegative
              · simpa using hbound
              · simpa using hvalue
              · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpacked


theorem orbitRadixDenseGramEntriesCheck_get
    (packed : Int) (permutation : Nat) (entries : List Int)
    (start index : Nat) (hindex : index < entries.length)
    (hcheck : orbitRadixDenseGramEntriesCheck packed permutation
      start entries = true) :
    entries[index] = orbitRadixPackedSignedValue packed
      (pairWitnessPackedIndex permutation (start + index + 1)) := by
  induction entries generalizing start index with
  | nil => simp at hindex
  | cons entry entries ih =>
      simp only [orbitRadixDenseGramEntriesCheck,
        Bool.and_eq_true, decide_eq_true_eq] at hcheck
      cases index with
      | zero => simpa using hcheck.1
      | succ index =>
          have hindex' : index < entries.length := by simpa using hindex
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (start + 1) index hindex' hcheck.2

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

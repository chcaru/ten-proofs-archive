
import ConnesRigidity.PropertyTExactCertificateOrbitPairWitnessValidation

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

theorem orbitPairWitnessPackedEntriesCheck_get
    (basisOrbit : Nat) (orbits witnesses : List Int)
    (start index : Nat) (hindex : index < orbits.length)
    (hcheck : orbitPairWitnessPackedEntriesCheck
      basisOrbit start orbits witnesses = true) :
    ∃ witness, witnesses[index]? = some witness ∧
      orbitPairWitnessPackedEntryCheck basisOrbit (start + index)
        orbits[index] witness = true := by
  induction orbits generalizing witnesses start index with
  | nil => simp at hindex
  | cons orbit orbits ih =>
      cases witnesses with
      | nil => simp [orbitPairWitnessPackedEntriesCheck] at hcheck
      | cons witness witnesses =>
          simp only [orbitPairWitnessPackedEntriesCheck,
            Bool.and_eq_true] at hcheck
          cases index with
          | zero => exact ⟨witness, by simp, by simpa using hcheck.1⟩
          | succ index =>
              have hindex' : index < orbits.length := by simpa using hindex
              obtain ⟨value, hvalue, hentry⟩ :=
                ih witnesses (start + 1) index hindex' hcheck.2
              exact ⟨value, by simpa using hvalue,
                by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                  using hentry⟩

theorem orbitPairWitnessPackedRowsCheck_get
    (orbits witnesses : List (Array Int)) (start index : Nat)
    (hindex : index < orbits.length)
    (hcheck : orbitPairWitnessPackedRowsCheck
      start orbits witnesses = true) :
    ∃ witness, witnesses[index]? = some witness ∧
      orbits[index].size = 425 ∧ witness.size = 425 ∧
      orbitPairWitnessPackedEntriesCheck (start + index) 0
        orbits[index].toList witness.toList = true := by
  induction orbits generalizing witnesses start index with
  | nil => simp at hindex
  | cons orbit orbits ih =>
      cases witnesses with
      | nil => simp [orbitPairWitnessPackedRowsCheck] at hcheck
      | cons witness witnesses =>
          simp only [orbitPairWitnessPackedRowsCheck,
            Bool.and_eq_true, decide_eq_true_eq] at hcheck
          cases index with
          | zero =>
              exact ⟨witness, by simp, hcheck.1.1.1,
                hcheck.1.1.2, by simpa using hcheck.1.2⟩
          | succ index =>
              have hindex' : index < orbits.length := by simpa using hindex
              obtain ⟨value, hvalue, hrow, hwitness, hentries⟩ :=
                ih witnesses (start + 1) index hindex' hcheck.2
              exact ⟨value, by simpa using hvalue,
                by simpa using hrow, hwitness,
                by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                  using hentries⟩

theorem orbitPairWitnessEntryCheck_valid
    (basisOrbit second : Nat)
    (hbasisOrbit : basisOrbit < basisOrbitRepresentativeData.size)
    (hsecond : second < basisData.size) :
    orbitPairWitnessEntryCheck basisOrbit second = true := by
  have hindexRows : basisOrbit < pairOrbitIndexData.size := by
    rw [pairWitnessDataSizes_valid.2.2.2.2.2.1]
    simpa [pairWitnessDataSizes_valid.2.2.2.2.1] using hbasisOrbit
  obtain ⟨witnessRow, hwitnessRow, horbitSize, hwitnessSize, hentries⟩ :=
    orbitPairWitnessPackedRowsCheck_get
      pairOrbitIndexData.toList pairOrbitWitnessData.toList
      0 basisOrbit (by simpa using hindexRows)
      orbitPairWitnessPackedRowsCheck_valid
  have hwitnessRowsIndex : basisOrbit < pairOrbitWitnessData.size := by
    rw [pairWitnessDataSizes_valid.2.2.2.2.2.2]
    simpa [pairWitnessDataSizes_valid.2.2.2.2.1] using hbasisOrbit
  have hwitnessRow' : pairOrbitWitnessData[basisOrbit]? = some witnessRow := by
    simpa using hwitnessRow
  have hwitnessRowValue : witnessRow = pairOrbitWitnessData[basisOrbit] := by
    simpa [hwitnessRowsIndex] using hwitnessRow'.symm
  have horbitSize' : (pairOrbitIndexData[basisOrbit]).size = 425 := by
    simpa using horbitSize
  have hsecond425 : second < 425 := by
    simpa [pairWitnessDataSizes_valid.1] using hsecond
  have horbitColumn : second < (pairOrbitIndexData[basisOrbit]).size := by
    simpa [horbitSize'] using hsecond425
  have hwitnessColumn : second < witnessRow.size := by
    simpa [hwitnessSize] using hsecond425
  have hentries' : orbitPairWitnessPackedEntriesCheck basisOrbit 0
      (pairOrbitIndexData[basisOrbit]).toList witnessRow.toList = true := by
    simpa using hentries
  obtain ⟨witness, hwitness, hentry⟩ :=
    orbitPairWitnessPackedEntriesCheck_get basisOrbit
      (pairOrbitIndexData[basisOrbit]).toList witnessRow.toList
      0 second (by simpa using horbitColumn) hentries'
  have hwitness' : witnessRow[second]? = some witness := by
    simpa using hwitness
  have hwitnessValue : witness = witnessRow[second] := by
    simpa [hwitnessColumn] using hwitness'.symm
  have hwitnessActualColumn :
      second < (pairOrbitWitnessData[basisOrbit]).size := by
    rw [← hwitnessRowValue]
    exact hwitnessColumn
  have horbit : dataEntry pairOrbitIndexData basisOrbit second =
      (pairOrbitIndexData[basisOrbit])[second] := by
    simp [dataEntry, Array.getD_eq_getD_getElem?, hindexRows, horbitColumn]
  have hpacked : dataEntry pairOrbitWitnessData basisOrbit second = witness := by
    calc
      dataEntry pairOrbitWitnessData basisOrbit second =
          (pairOrbitWitnessData[basisOrbit])[second] := by
            simp [dataEntry, Array.getD_eq_getD_getElem?,
              hwitnessRowsIndex, hwitnessActualColumn]
      _ = witnessRow[second] := by simp [hwitnessRowValue]
      _ = witness := hwitnessValue.symm
  have hentry' : orbitPairWitnessPackedEntryCheck basisOrbit second
      (pairOrbitIndexData[basisOrbit])[second] witness = true := by
    simpa using hentry
  exact orbitPairWitnessPackedEntryCheck_sound basisOrbit second
    (pairOrbitIndexData[basisOrbit])[second] witness horbit hpacked hentry'

theorem orbitPairWitnessRowCheck_valid
    (basisOrbit : Nat)
    (hbasisOrbit : basisOrbit < basisOrbitRepresentativeData.size) :
    orbitPairWitnessRowCheck basisOrbit = true := by
  have hindexRows : basisOrbit < pairOrbitIndexData.size := by
    rw [pairWitnessDataSizes_valid.2.2.2.2.2.1]
    simpa [pairWitnessDataSizes_valid.2.2.2.2.1] using hbasisOrbit
  obtain ⟨witnessRow, hwitnessRow, _, hwitnessSize, _⟩ :=
    orbitPairWitnessPackedRowsCheck_get
      pairOrbitIndexData.toList pairOrbitWitnessData.toList
      0 basisOrbit (by simpa using hindexRows)
      orbitPairWitnessPackedRowsCheck_valid
  have hrow : pairOrbitWitnessData[basisOrbit]? = some witnessRow := by
    simpa using hwitnessRow
  simp only [orbitPairWitnessRowCheck, hrow, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · simpa [pairWitnessDataSizes_valid.1] using hwitnessSize
  · intro second hsecond
    exact orbitPairWitnessEntryCheck_valid basisOrbit second
      hbasisOrbit hsecond

theorem orbitPairWitnessCheck_valid : orbitPairWitnessCheck = true := by
  simp only [orbitPairWitnessCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rw [pairWitnessDataSizes_valid.2.2.2.2.2.2,
      pairWitnessDataSizes_valid.2.2.2.2.1]
  · intro basisOrbit hbasisOrbit
    apply orbitPairWitnessRowCheck_valid
    rw [pairWitnessDataSizes_valid.2.2.2.2.1]
    simpa [pairWitnessDataSizes_valid.2.2.2.2.2.2] using hbasisOrbit

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

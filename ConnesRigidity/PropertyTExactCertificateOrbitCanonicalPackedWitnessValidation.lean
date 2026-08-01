


import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedData
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedCoordinate
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalCodeSorted
import ConnesRigidity.PropertyTExactCertificateOrbitBasisTransport
import ConnesRigidity.PropertyTExactCertificateOrbitStabilizerData
import ConnesRigidity.PropertyTExactCertificateOrbitTargetRadix
import ConnesRigidity.PropertyTExactCertificateOrbitIncidenceValidation












namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000



def canonicalPackedWitnessCanonicalRow (witness : List Int)
    (representative inverse : Array Int) : Array Int :=
  let source := if witness.getD 3 0 = 0 then representative else inverse
  signedRowAction (symmetryData.getD (witness.getD 2 0).toNat #[])
    source



def canonicalPackedWitnessRecordCheck (orbit : Nat)
    (packed witness : List Int)
    (representative inverse : Array Int) : Bool :=
  let canonical :=
    canonicalPackedWitnessCanonicalRow witness representative inverse
  decide (packed.length = 4) &&
    decide (witness.length = 4) &&
    decide (packed.getD 0 0 = (orbit : Int)) &&
    decide (witness.getD 0 0 = (orbit : Int)) &&
    decide (0 ≤ witness.getD 2 0 ∧ witness.getD 2 0 < (64 : Int)) &&
    decide (witness.getD 3 0 = 0 ∨ witness.getD 3 0 = 1) &&
    decide (representative.size = 20) &&
    decide (inverse.size = 20) &&
    targetCoordinateBounds canonical.toList &&
    targetCoordinateBounds representative.toList &&
    targetCoordinateBounds inverse.toList &&
    decide (0 ≤ packed.getD 1 0) &&
    decide (0 ≤ packed.getD 2 0) &&
    decide (0 ≤ packed.getD 3 0) &&
    decide (packed.getD 1 0 = witness.getD 1 0) &&
    decide ((packed.getD 1 0).toNat = canonicalPackedRow canonical) &&
    decide ((packed.getD 2 0).toNat =
      canonicalPackedRow representative) &&
    decide ((packed.getD 3 0).toNat = canonicalPackedRow inverse)



def canonicalPackedWitnessRowsCheck :
    Nat → List (List Int) → List (List Int) →
      List (Array Int) → List (Array Int) → Bool
  | _, [], [], [], [] => true
  | orbit, packed :: records, witness :: witnesses,
      representative :: representatives, inverse :: inverses =>
      canonicalPackedWitnessRecordCheck orbit packed witness
        representative inverse &&
        canonicalPackedWitnessRowsCheck (orbit + 1)
          records witnesses representatives inverses
  | _, _, _, _, _ => false



theorem canonicalPackedWitnessData_length :
    canonicalPackedWitnessData.length = 995 := by
  unfold canonicalPackedWitnessData
  decide +kernel

set_option maxHeartbeats 0 in


theorem canonicalPackedWitnessRowsCheck_valid :
    canonicalPackedWitnessRowsCheck 0
      canonicalPackedWitnessData coefficientCanonicalWitnessData
      coefficientRepresentativeData.toList
      coefficientInverseRepresentativeData.toList = true := by
  unfold canonicalPackedWitnessRowsCheck canonicalPackedWitnessRecordCheck
    canonicalPackedWitnessCanonicalRow targetCoordinateBounds
    canonicalPackedRow canonicalPackedRowList
    canonicalPackedCoordinateDigit signedRowAction
    signedActionMatrixCoordinate signedActionVectorCoordinate
    matrixCoordinate vectorCoordinate symmetryPermutationCoordinate
    symmetrySignCoordinate canonicalPackedWitnessData
    coefficientCanonicalWitnessData coefficientRepresentativeData
    coefficientInverseRepresentativeData symmetryData
  decide +kernel


theorem canonicalPackedWitnessRowsCheck_get
    (records witnesses : List (List Int))
    (representatives inverses : List (Array Int))
    (start index : Nat)
    (hindex : index < records.length)
    (hwitness : records.length = witnesses.length)
    (hrepresentative : records.length = representatives.length)
    (hinverse : records.length = inverses.length)
    (hcheck : canonicalPackedWitnessRowsCheck start
      records witnesses representatives inverses = true) :
    canonicalPackedWitnessRecordCheck (start + index)
      (records.getD index []) (witnesses.getD index [])
      (representatives.getD index #[]) (inverses.getD index #[]) = true := by
  induction records generalizing witnesses representatives inverses
      start index with
  | nil => simp at hindex
  | cons record records ih =>
      cases witnesses with
      | nil => simp at hwitness
      | cons witness witnesses =>
          cases representatives with
          | nil => simp at hrepresentative
          | cons representative representatives =>
              cases inverses with
              | nil => simp at hinverse
              | cons inverse inverses =>
                  simp only [canonicalPackedWitnessRowsCheck,
                    Bool.and_eq_true] at hcheck
                  cases index with
                  | zero => simpa using hcheck.1
                  | succ index =>
                      have hindex' : index < records.length := by
                        simpa using hindex
                      have hwitness' :
                          records.length = witnesses.length := by
                        simpa using hwitness
                      have hrepresentative' :
                          records.length = representatives.length := by
                        simpa using hrepresentative
                      have hinverse' :
                          records.length = inverses.length := by
                        simpa using hinverse
                      simpa [Nat.add_assoc, Nat.add_comm,
                        Nat.add_left_comm] using
                        ih witnesses representatives inverses
                          (start + 1) index hindex' hwitness'
                          hrepresentative' hinverse' hcheck.2


theorem canonicalPackedInverseRepresentativeData_size :
    coefficientInverseRepresentativeData.size = 995 := by
  unfold coefficientInverseRepresentativeData
  decide +kernel


noncomputable def canonicalPackedWitnessRecord (orbit : Fin 995) :
    List Int := canonicalPackedWitnessData.getD orbit.val []



theorem canonicalPackedWitnessRecord_valid (orbit : Fin 995) :
    canonicalPackedWitnessRecordCheck orbit.val
      (canonicalPackedWitnessRecord orbit)
      (coefficientCanonicalWitnessData.getD orbit.val [])
      (coefficientRepresentativeData.getD orbit.val #[])
      (coefficientInverseRepresentativeData.getD orbit.val #[]) = true := by
  have hindex : orbit.val < canonicalPackedWitnessData.length := by
    rw [canonicalPackedWitnessData_length]
    exact orbit.isLt
  have hwitness : canonicalPackedWitnessData.length =
      coefficientCanonicalWitnessData.length := by
    rw [canonicalPackedWitnessData_length,
      coefficientCanonicalCodeData_lengths.1]
  have hrepresentative : canonicalPackedWitnessData.length =
      coefficientRepresentativeData.toList.length := by
    simp [canonicalPackedWitnessData_length,
      coefficientRepresentativeData_size]
  have hinverse : canonicalPackedWitnessData.length =
      coefficientInverseRepresentativeData.toList.length := by
    simp [canonicalPackedWitnessData_length,
      canonicalPackedInverseRepresentativeData_size]
  have hrecord := canonicalPackedWitnessRowsCheck_get
    canonicalPackedWitnessData coefficientCanonicalWitnessData
    coefficientRepresentativeData.toList
    coefficientInverseRepresentativeData.toList 0 orbit.val
    hindex hwitness hrepresentative hinverse
    canonicalPackedWitnessRowsCheck_valid
  have hrepresentativeIndex : orbit.val <
      coefficientRepresentativeData.size := by
    simp [coefficientRepresentativeData_size]
  have hinverseIndex : orbit.val <
      coefficientInverseRepresentativeData.size := by
    simp [canonicalPackedInverseRepresentativeData_size]
  simpa [canonicalPackedWitnessRecord,
    List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?,
    hrepresentativeIndex, hinverseIndex] using hrecord



theorem canonicalPackedWitnessRecord_sound (orbit : Fin 995) :
    let packed := canonicalPackedWitnessRecord orbit
    let witness := coefficientCanonicalWitnessData.getD orbit.val []
    let representative := coefficientRepresentativeData.getD orbit.val #[]
    let inverse := coefficientInverseRepresentativeData.getD orbit.val #[]
    let canonical :=
      canonicalPackedWitnessCanonicalRow witness representative inverse
    packed.length = 4 ∧ witness.length = 4 ∧
      packed.getD 0 0 = (orbit.val : Int) ∧
      witness.getD 0 0 = (orbit.val : Int) ∧
      (0 ≤ witness.getD 2 0 ∧ witness.getD 2 0 < (64 : Int)) ∧
      (witness.getD 3 0 = 0 ∨ witness.getD 3 0 = 1) ∧
      representative.size = 20 ∧ inverse.size = 20 ∧
      targetCoordinateBounds canonical.toList = true ∧
      targetCoordinateBounds representative.toList = true ∧
      targetCoordinateBounds inverse.toList = true ∧
      0 ≤ packed.getD 1 0 ∧ 0 ≤ packed.getD 2 0 ∧
      0 ≤ packed.getD 3 0 ∧
      packed.getD 1 0 = witness.getD 1 0 ∧
      (packed.getD 1 0).toNat = canonicalPackedRow canonical ∧
      (packed.getD 2 0).toNat = canonicalPackedRow representative ∧
      (packed.getD 3 0).toNat = canonicalPackedRow inverse := by
  have hcheck := canonicalPackedWitnessRecord_valid orbit
  simpa only [canonicalPackedWitnessRecordCheck,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hcheck



theorem canonicalPackedCoordinateBounds_sound
    (row : Array Int)
    (hcheck : targetCoordinateBounds row.toList = true)
    (coordinate : Nat) (hcoordinate : coordinate < row.size) :
    -8 ≤ row[coordinate]'hcoordinate ∧
      row[coordinate]'hcoordinate < 8 := by
  have hentry := List.all_eq_true.mp hcheck row[coordinate]
    (by simp)
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using hentry

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

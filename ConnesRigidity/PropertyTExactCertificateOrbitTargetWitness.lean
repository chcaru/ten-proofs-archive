
import ConnesRigidity.PropertyTExactCertificateOrbitBasisTransport
import ConnesRigidity.PropertyTExactCertificateOrbitGeneratorEnumeration
import ConnesRigidity.PropertyTExactCertificateOrbitTargetData
import ConnesRigidity.PropertyTExactCertificateOrbitTargetGeneratorSemantics
import ConnesRigidity.PropertyTExactCertificateOrbitTargetMergeSoundness
import ConnesRigidity.PropertyTExactCertificateOrbitTargetRadix

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def orbitTargetProductRecordCoordinates (record : List Int) : List Int :=
  (record.drop 2).take 20

def orbitTargetProductRecordCheck (position : Nat) (record : List Int) : Bool :=
  let left := record.getD 0 0
  let right := record.getD 1 0
  let coordinates := orbitTargetProductRecordCoordinates record
  decide (record.length = 23) &&
    decide (0 ≤ left ∧ left < (24 : Int)) &&
    decide (0 ≤ right ∧ right < (24 : Int)) &&
    targetCoordinateBounds coordinates &&
    isSymplecticRow coordinates.toArray &&
    rawProductCheck
      (generatorData.getD left.toNat #[])
      (generatorData.getD right.toNat #[])
      coordinates.toArray &&
    decide (record.getD 22 0 = targetCoordinateCode coordinates) &&
    decide
      ((targetGeneratorProductRowIndexData.getD
          (24 * left.toNat + right.toNat) []).getD 0 (-1) =
        (position : Int))

def orbitTargetProductRecordsCheck : Nat → List (List Int) → Bool
  | _, [] => true
  | position, record :: records =>
      orbitTargetProductRecordCheck position record &&
        orbitTargetProductRecordsCheck (position + 1) records

def orbitTargetProductInverseCheck : Nat → List (List Int) → Bool
  | _, [] => true
  | pair, inverse :: inverses =>
      let position := inverse.getD 0 (-1)
      let record := targetGeneratorProductRowData.getD position.toNat []
      decide (inverse.length = 1) &&
        decide (0 ≤ position ∧ position < (576 : Int)) &&
        decide
          (24 * (record.getD 0 0).toNat +
            (record.getD 1 0).toNat = pair) &&
        orbitTargetProductInverseCheck (pair + 1) inverses

def orbitTargetRepresentativeInverseCheck : Nat → List (List Int) → Bool
  | _, [] => true
  | orbit, inverse :: inverses =>
      let position := inverse.getD 0 (-1)
      let record := targetRepresentativeCodeSortedData.getD position.toNat []
      decide (inverse.length = 1) &&
        decide (0 ≤ position ∧ position < (995 : Int)) &&
        decide (record.getD 0 0 = (orbit : Int)) &&
        orbitTargetRepresentativeInverseCheck (orbit + 1) inverses

def orbitTargetConsumeProductGroup (code : Int) :
    Nat → List (List Int) → Option (List (List Int)) :=
  targetConsumeCode (fun product => product.getD 22 0) code

def orbitTargetProductGroupsCheck :
    Int → Nat → List (List Int) → List (List Int) → Bool :=
  targetGroupCheck (fun product => product.getD 22 0)

def orbitTargetSeekProductGroup
    (code : Int) : List (List Int) → (Int × List (List Int)) :=
  targetSeekGroup code

def orbitTargetRepresentativeRecordCheck
    (previous : Int) (position : Nat) (record : List Int)
    (groups : List (List Int)) : Bool :=
  let orbit := record.getD 0 0
  let code := record.getD 1 0
  let representative := coefficientRepresentativeData.getD orbit.toNat #[]
  let witness := coefficientTargetWitnessData.getD orbit.toNat #[]
  let group := orbitTargetSeekProductGroup code groups
  decide (record.length = 2) &&
    decide (0 ≤ orbit ∧ orbit < (995 : Int)) &&
    decide (previous < code) &&
    decide
      ((targetRepresentativeCodeIndexData.getD orbit.toNat []).getD
        0 (-1) = (position : Int)) &&
    decide (representative.size = 20) &&
    targetCoordinateBounds representative.toList &&
    isSymplecticRow representative &&
    decide (targetCoordinateCode representative.toList = code) &&
    decide (witness.size = 3) &&
    decide
      (witness.getD 0 0 =
        if (basisData.getD 0 #[]) == representative then
          1
        else
          0) &&
    decide
      (witness.getD 1 0 =
        generatorData.toList.foldl
          (fun count generator =>
            if generator == representative then count + 1 else count)
          0) &&
    decide (witness.getD 2 0 = group.1)

def orbitTargetRepresentativeRowsCheck :
    Int → Nat → List (List Int) → List (List Int) → Bool
  | _, _, [], _ => true
  | previous, position, record :: records, groups =>
      orbitTargetRepresentativeRecordCheck previous position record groups &&
        orbitTargetRepresentativeRowsCheck (record.getD 1 0)
          (position + 1) records
          (orbitTargetSeekProductGroup (record.getD 1 0) groups).2

def orbitTargetStreamingCheck : Bool :=
  decide (targetGeneratorProductRowData.length = 576) &&
    decide (targetGeneratorProductRowIndexData.length = 576) &&
    decide (targetRepresentativeCodeSortedData.length = 995) &&
    decide (targetRepresentativeCodeIndexData.length = 995) &&
    decide (coefficientRepresentativeData.size = 995) &&
    decide (coefficientTargetWitnessData.size = 995) &&
    generatorRowsSymplecticCheck &&
    orbitTargetProductRecordsCheck 0 targetGeneratorProductRowData &&
    orbitTargetProductInverseCheck 0 targetGeneratorProductRowIndexData &&
    orbitTargetRepresentativeInverseCheck 0 targetRepresentativeCodeIndexData &&
    orbitTargetProductGroupsCheck (-1) 0 targetGeneratorProductGroupData
      targetGeneratorProductRowData &&
    orbitTargetRepresentativeRowsCheck (-1) 0
      targetRepresentativeCodeSortedData targetGeneratorProductGroupData

theorem orbitTargetProductRecordsCheck_get
    (records : List (List Int)) (start index : Nat)
    (hindex : index < records.length)
    (hcheck : orbitTargetProductRecordsCheck start records = true) :
    orbitTargetProductRecordCheck (start + index)
      (records.getD index []) = true := by
  induction records generalizing start index with
  | nil => simp at hindex
  | cons record records inductionHypothesis =>
      simp only [orbitTargetProductRecordsCheck, Bool.and_eq_true] at hcheck
      cases index with
      | zero => simpa using hcheck.1
      | succ index =>
          have htail : index < records.length := by simpa using hindex
          have hresult := inductionHypothesis (start + 1) index htail hcheck.2
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hresult

theorem orbitTargetProductInverseCheck_get
    (inverses : List (List Int)) (start index : Nat)
    (hindex : index < inverses.length)
    (hcheck : orbitTargetProductInverseCheck start inverses = true) :
    let position := (inverses.getD index []).getD 0 (-1)
    0 ≤ position ∧ position < (576 : Int) ∧
      24 * ((targetGeneratorProductRowData.getD position.toNat []).getD 0 0).toNat +
        ((targetGeneratorProductRowData.getD position.toNat []).getD 1 0).toNat =
          start + index := by
  induction inverses generalizing start index with
  | nil => simp at hindex
  | cons inverse inverses inductionHypothesis =>
      simp only [orbitTargetProductInverseCheck, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨⟨_, hposition⟩, hpair⟩, htail⟩
      cases index with
      | zero =>
          simpa using ⟨hposition.1, hposition.2, hpair⟩
      | succ index =>
          have hlt : index < inverses.length := by simpa using hindex
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            inductionHypothesis (start + 1) index hlt htail

theorem orbitTargetRepresentativeInverseCheck_get
    (inverses : List (List Int)) (start index : Nat)
    (hindex : index < inverses.length)
    (hcheck : orbitTargetRepresentativeInverseCheck start inverses = true) :
    let position := (inverses.getD index []).getD 0 (-1)
    0 ≤ position ∧ position < (995 : Int) ∧
      (targetRepresentativeCodeSortedData.getD position.toNat []).getD 0 0 =
        (start + index : Nat) := by
  induction inverses generalizing start index with
  | nil => simp at hindex
  | cons inverse inverses inductionHypothesis =>
      simp only [orbitTargetRepresentativeInverseCheck, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨⟨_, hposition⟩, horbit⟩, htail⟩
      cases index with
      | zero =>
          simpa using ⟨hposition.1, hposition.2, horbit⟩
      | succ index =>
          have hlt : index < inverses.length := by simpa using hindex
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            inductionHypothesis (start + 1) index hlt htail

theorem orbitTargetProductRecordCheck_sound
    (position : Nat) (record : List Int)
    (hcheck : orbitTargetProductRecordCheck position record = true) :
    record.length = 23 ∧
      (0 ≤ record.getD 0 0 ∧ record.getD 0 0 < (24 : Int)) ∧
      (0 ≤ record.getD 1 0 ∧ record.getD 1 0 < (24 : Int)) ∧
      targetCoordinateBounds (orbitTargetProductRecordCoordinates record) = true ∧
      isSymplecticRow
        (orbitTargetProductRecordCoordinates record).toArray = true ∧
      rawProductCheck
        (generatorData.getD (record.getD 0 0).toNat #[])
        (generatorData.getD (record.getD 1 0).toNat #[])
        (orbitTargetProductRecordCoordinates record).toArray = true ∧
      record.getD 22 0 =
        targetCoordinateCode (orbitTargetProductRecordCoordinates record) ∧
      (targetGeneratorProductRowIndexData.getD
        (24 * (record.getD 0 0).toNat + (record.getD 1 0).toNat)
          []).getD 0 (-1) = (position : Int) := by
  simpa only [orbitTargetProductRecordCheck, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc] using hcheck

theorem orbitTargetRepresentativeRecordCheck_sound
    (previous : Int) (position : Nat) (record : List Int)
    (groups : List (List Int))
    (hcheck : orbitTargetRepresentativeRecordCheck
      previous position record groups = true) :
    let orbit := record.getD 0 0
    let code := record.getD 1 0
    let representative := coefficientRepresentativeData.getD orbit.toNat #[]
    let witness := coefficientTargetWitnessData.getD orbit.toNat #[]
    record.length = 2 ∧
      (0 ≤ orbit ∧ orbit < (995 : Int)) ∧
      previous < code ∧
      (targetRepresentativeCodeIndexData.getD orbit.toNat []).getD
        0 (-1) = (position : Int) ∧
      representative.size = 20 ∧
      targetCoordinateBounds representative.toList = true ∧
      isSymplecticRow representative = true ∧
      targetCoordinateCode representative.toList = code ∧
      witness.size = 3 ∧
      witness.getD 0 0 =
        (if (basisData.getD 0 #[]) == representative then 1 else 0) ∧
      witness.getD 1 0 =
        generatorData.toList.foldl
          (fun count generator =>
            if generator == representative then count + 1 else count)
          0 ∧
      witness.getD 2 0 =
        (orbitTargetSeekProductGroup code groups).1 := by
  simpa only [orbitTargetRepresentativeRecordCheck, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc] using hcheck

theorem orbitTargetStreamingCheck_sound
    (hcheck : orbitTargetStreamingCheck = true) :
    targetGeneratorProductRowData.length = 576 ∧
      targetGeneratorProductRowIndexData.length = 576 ∧
      targetRepresentativeCodeSortedData.length = 995 ∧
      targetRepresentativeCodeIndexData.length = 995 ∧
      coefficientRepresentativeData.size = 995 ∧
      coefficientTargetWitnessData.size = 995 ∧
      generatorRowsSymplecticCheck = true ∧
      orbitTargetProductRecordsCheck 0 targetGeneratorProductRowData = true ∧
      orbitTargetProductInverseCheck 0 targetGeneratorProductRowIndexData = true ∧
      orbitTargetRepresentativeInverseCheck 0
        targetRepresentativeCodeIndexData = true ∧
      orbitTargetProductGroupsCheck (-1) 0 targetGeneratorProductGroupData
        targetGeneratorProductRowData = true ∧
      orbitTargetRepresentativeRowsCheck (-1) 0
        targetRepresentativeCodeSortedData targetGeneratorProductGroupData =
          true := by
  simpa only [orbitTargetStreamingCheck, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc] using hcheck

def orbitTargetRawRowEq (left right : Array Int) : Bool :=
  left == right

def orbitTargetProductCoordinate
    (left right : Array Int) (coordinate : Nat) : Int :=
  if coordinate < 16 then
    let i := coordinate / 4
    let j := coordinate % 4
    left.getD (4 * i) 0 * right.getD j 0 +
      left.getD (4 * i + 1) 0 * right.getD (4 + j) 0 +
      left.getD (4 * i + 2) 0 * right.getD (8 + j) 0 +
      left.getD (4 * i + 3) 0 * right.getD (12 + j) 0
  else
    let i := coordinate - 16
    left.getD (16 + i) 0 +
      left.getD (4 * i) 0 * right.getD 16 0 +
      left.getD (4 * i + 1) 0 * right.getD 17 0 +
      left.getD (4 * i + 2) 0 * right.getD 18 0 +
      left.getD (4 * i + 3) 0 * right.getD 19 0

def orbitTargetRawProductCheck
    (left right representative : Array Int) : Bool :=
  (List.range 20).all fun coordinate =>
    decide
      (orbitTargetProductCoordinate left right coordinate =
        representative.getD coordinate 0)

def orbitTargetGeneratorCount (representative : Array Int) : Int :=
  generatorData.toList.foldl
    (fun count generator =>
      if orbitTargetRawRowEq generator representative then count + 1
      else count)
    0

def orbitTargetProductCount (representative : Array Int) : Int :=
  generatorData.toList.foldl
    (fun count right =>
      generatorData.toList.foldl
        (fun count left =>
          if orbitTargetRawProductCheck right left representative then
            count + 1
          else
            count)
        count)
    0

def orbitTargetWitnessRowCheck
    (representative witness target : Array Int) : Bool :=
  decide (representative.size = 20) &&
    decide (witness.size = 3) &&
    decide (target.size = 1) &&
    isSymplecticRow representative &&
    decide
      (witness.getD 0 0 =
        if orbitTargetRawRowEq (basisData.getD 0 #[]) representative then
          1
        else
          0) &&
    decide (witness.getD 1 0 = orbitTargetGeneratorCount representative) &&
    decide (witness.getD 2 0 = orbitTargetProductCount representative) &&
    decide
      (target.getD 0 0 =
        64000000000000 *
            (576 * witness.getD 0 0 - 48 * witness.getD 1 0 +
              witness.getD 2 0) -
          640000000000 *
            (24 * witness.getD 0 0 - witness.getD 1 0))

def orbitTargetWitnessCheck : Bool :=
  decide (coefficientRepresentativeData.size =
      coefficientTargetWitnessData.size) &&
    decide (coefficientRepresentativeData.size =
      coefficientTargetData.size) &&
    generatorRowsSymplecticCheck &&
    (generatorData.toList.all fun generator =>
      decide (generator.size = 20)) &&
    (((coefficientRepresentativeData.toList.zip
          coefficientTargetWitnessData.toList).zip
        coefficientTargetData.toList).all fun row =>
      orbitTargetWitnessRowCheck row.1.1 row.1.2 row.2)

theorem orbitTargetWitnessRowCheck_sound
    (representative witness target : Array Int)
    (hcheck : orbitTargetWitnessRowCheck representative witness target = true) :
    representative.size = 20 ∧ witness.size = 3 ∧ target.size = 1 ∧
      isSymplecticRow representative = true ∧
      witness.getD 0 0 =
        (if orbitTargetRawRowEq (basisData.getD 0 #[]) representative then
          1
        else
          0) ∧
      witness.getD 1 0 = orbitTargetGeneratorCount representative ∧
      witness.getD 2 0 = orbitTargetProductCount representative ∧
      target.getD 0 0 =
        64000000000000 *
            (576 * witness.getD 0 0 - 48 * witness.getD 1 0 +
              witness.getD 2 0) -
          640000000000 *
            (24 * witness.getD 0 0 - witness.getD 1 0) := by
  simpa only [orbitTargetWitnessRowCheck, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc] using hcheck

theorem orbitTargetWitnessCheck_row
    (hcheck : orbitTargetWitnessCheck = true)
    (index : Nat) (hindex : index < coefficientRepresentativeData.size) :
    orbitTargetWitnessRowCheck
      (coefficientRepresentativeData.getD index #[])
      (coefficientTargetWitnessData.getD index #[])
      (coefficientTargetData.getD index #[]) = true := by
  simp only [orbitTargetWitnessCheck, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  rcases hcheck with
    ⟨⟨⟨⟨hwitness, htarget⟩, hgenerators⟩, hwidth⟩, hrows⟩
  have hwitnessIndex : index < coefficientTargetWitnessData.size := by
    omega
  have htargetIndex : index < coefficientTargetData.size := by
    omega
  have hzip : index <
      ((coefficientRepresentativeData.toList.zip
          coefficientTargetWitnessData.toList).zip
        coefficientTargetData.toList).length := by
    simp only [List.length_zip, Array.length_toList]
    omega
  have hrow := List.all_eq_true.mp hrows _ (List.getElem_mem hzip)
  simp only [List.getElem_zip, Array.getElem_toList] at hrow
  simpa [Array.getD_eq_getD_getElem?, hindex, hwitnessIndex,
    htargetIndex] using hrow

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

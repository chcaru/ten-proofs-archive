
import ConnesRigidity.PropertyTExactCertificateOrbitData

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

def orbitEntry (row : Array Int) (column : Nat) : Int :=
  row.getD column 0

def orbitRowWidthCheck (rows : Array (Array Int)) (width : Nat) : Bool :=
  rows.toList.all fun row => decide (row.size = width)

def orbitIndexCheck (index : Int) (bound : Nat) : Bool :=
  decide (0 ≤ index ∧ index < (bound : Int))

def orbitCoefficientTermValue (row : Array Int) : Int :=
  orbitEntry row 1 * orbitEntry row 2

def orbitCoefficientRangeTotal (start count : Nat) : Int :=
  coefficientTermData.foldl
    (fun total row => total + orbitCoefficientTermValue row)
    0 start (start + count)

def orbitCoefficientRangeTermsCheck
    (start count : Nat) (key : Int) : Bool :=
  coefficientTermData.foldl
    (fun valid row =>
      valid && decide (row.size = coefficientTermRowWidth) &&
        decide (orbitEntry row 0 = key))
    true start (start + count)

def orbitCoefficientTotal (key : Int) : Int :=
  coefficientTermData.toList.foldl
    (fun total row =>
      if orbitEntry row 0 = key then
        total + orbitCoefficientTermValue row
      else
        total)
    0

def orbitCoefficientRowCheck (index : Nat) : Bool :=
  match coefficientEquationData[index]? with
  | none => false
  | some row =>
      let key := orbitEntry row 0
      let start := orbitEntry row 1
      let count := orbitEntry row 2
      decide (row.size = coefficientEquationRowWidth) &&
        decide (0 ≤ start) &&
        decide (0 ≤ count) &&
        decide (start.toNat + count.toNat ≤ coefficientTermData.size) &&
        orbitCoefficientRangeTermsCheck start.toNat count.toNat key &&
        decide (orbitCoefficientRangeTotal start.toNat count.toNat =
          orbitEntry row 3)

def orbitCoefficientCheck : Bool :=
  (List.range coefficientEquationData.size).all orbitCoefficientRowCheck

def orbitCoefficientSlicePartitionRowCheck (index : Nat) : Bool :=
  match coefficientEquationData[index]? with
  | none => false
  | some row =>
      let start := (orbitEntry row 1).toNat
      let count := (orbitEntry row 2).toNat
      let previous := coefficientEquationData.getD (index - 1) #[]
      (if index = 0 then
        decide (start = 0)
      else
        decide (orbitEntry previous 0 < orbitEntry row 0) &&
          decide
            ((orbitEntry previous 1).toNat +
              (orbitEntry previous 2).toNat = start)) &&
        (if index + 1 = coefficientEquationData.size then
          decide (start + count = coefficientTermData.size)
        else true)

def orbitGramIncidenceRowCheck (index : Nat) : Bool :=
  match gramOrbitData[index]? with
  | none => false
  | some row =>
      let coefficientOrbit := orbitEntry row 2
      let incidence := orbitEntry row 3
      let coefficientOrbitSize :=
        dataEntry coefficientOrbitSizeData coefficientOrbit.toNat 0
      decide (row.size = gramOrbitRowWidth) &&
        orbitIndexCheck coefficientOrbit coefficientOrbitSizeData.size &&
        decide (0 < incidence) &&
        decide (0 < coefficientOrbitSize) &&
        decide (orbitEntry row 7 = incidence * coefficientOrbitSize)

def orbitGramStabilizerCount (left right : Nat) : Nat :=
  (List.range symmetryData.size).foldl
    (fun total symmetry =>
      let imageLeft := symmetryBasisImage symmetry left
      let imageRight := symmetryBasisImage symmetry right
      total +
        (if imageLeft = left ∧ imageRight = right then 1 else 0) +
        (if imageLeft = right ∧ imageRight = left then 1 else 0))
    0

def orbitGramStabilizerRowCheck (index : Nat) : Bool :=
  match gramOrbitData[index]? with
  | none => false
  | some row =>
      let left := orbitEntry row 0
      let right := orbitEntry row 1
      let size := orbitEntry row 7
      orbitIndexCheck left basisData.size &&
        orbitIndexCheck right basisData.size &&
        decide (0 < size) &&
        decide
          (size * (orbitGramStabilizerCount left.toNat right.toNat : Int) =
            (2 * symmetryData.size : Nat))

def orbitCoefficientTermGramOrbitRowCheck (index : Nat) : Bool :=
  match coefficientTermData[index]?,
        coefficientTermGramOrbitIndexData[index]? with
  | some term, some witness =>
      let orbit := orbitEntry witness 0
      let gram := gramOrbitData.getD orbit.toNat #[]
      let equation :=
        dataEntry coefficientOrbitEquationIndexData
          (orbitEntry term 0).toNat 0
      let equationRow := coefficientEquationData.getD equation.toNat #[]
      decide (term.size = coefficientTermRowWidth) &&
        decide (witness.size = 1) &&
        orbitIndexCheck orbit gramOrbitData.size &&
        orbitIndexCheck equation coefficientEquationData.size &&
        decide (orbitEntry term 0 = orbitEntry gram 2) &&
        decide (orbitEntry term 1 = orbitEntry gram 3) &&
        decide (orbitEntry term 2 = orbitEntry gram 4) &&
        decide (orbitEntry term 2 ≠ 0) &&
        decide (orbitEntry equationRow 0 = orbitEntry term 0) &&
        decide ((orbitEntry equationRow 1).toNat ≤ index) &&
        decide
          (index < (orbitEntry equationRow 1).toNat +
            (orbitEntry equationRow 2).toNat) &&
        decide
          (dataEntry gramOrbitTermIndexData orbit.toNat 0 =
            (index : Int))
  | _, _ => false

def orbitGramTermIndexRowCheck (index : Nat) : Bool :=
  match gramOrbitData[index]?, gramOrbitTermIndexData[index]? with
  | some gram, some witness =>
      let term := orbitEntry witness 0
      decide (witness.size = 1) &&
        (if orbitEntry gram 4 = 0 then
          decide (term = -1)
        else
          orbitIndexCheck term coefficientTermData.size &&
            decide
              (dataEntry coefficientTermGramOrbitIndexData term.toNat 0 =
                (index : Int)))
  | _, _ => false

def orbitCoefficientOrbitEquationRowCheck (index : Nat) : Bool :=
  match coefficientOrbitEquationIndexData[index]?,
        coefficientTargetData[index]? with
  | some inverse, some target =>
      let equation := orbitEntry inverse 0
      decide (inverse.size = 1) &&
        decide (target.size = 1) &&
        (if equation = -1 then
          decide (orbitEntry target 0 = 0)
        else
          orbitIndexCheck equation coefficientEquationData.size &&
            decide
              (coefficientEquationOrbit equation.toNat = (index : Int)) &&
            decide
              (coefficientEquationTarget equation.toNat =
                orbitEntry target 0))
  | _, _ => false

def orbitGramValue (orbit : Int) : Int :=
  orbitEntry (gramOrbitData.getD orbit.toNat #[]) 4

def orbitRowSumTermValue (row : Array Int) : Int :=
  orbitEntry row 2 * orbitEntry row 3

def orbitRowSumRangeTotal (start count : Nat) : Int :=
  rowSumTermData.foldl
    (fun total row => total + orbitRowSumTermValue row)
    0 start (start + count)

def orbitRowSumRangeTermsCheck
    (start count : Nat) (basisOrbit : Int) : Bool :=
  rowSumTermData.foldl
    (fun valid row =>
      valid && decide (row.size = 4) &&
        decide (orbitEntry row 0 = basisOrbit))
    true start (start + count)

def orbitRowSumTotal (basisOrbit : Int) : Int :=
  match rowSumEquationData[basisOrbit.toNat]? with
  | none => 0
  | some row =>
      orbitRowSumRangeTotal
        (orbitEntry row 1).toNat (orbitEntry row 2).toNat

def orbitRowSumRowCheck (index : Nat) : Bool :=
  match rowSumEquationData[index]? with
  | none => false
  | some row =>
      let start := orbitEntry row 1
      let count := orbitEntry row 2
      decide (index < basisOrbitRepresentativeData.size) &&
        decide (row.size = 3) &&
        decide (orbitEntry row 0 = (index : Int)) &&
        decide (0 ≤ start) &&
        decide (0 ≤ count) &&
        decide (start.toNat + count.toNat ≤ rowSumTermData.size) &&
        orbitRowSumRangeTermsCheck start.toNat count.toNat (index : Int) &&
        decide (orbitRowSumRangeTotal start.toNat count.toNat = 0)

def orbitRowSumTermGramRowCheck (index : Nat) : Bool :=
  match rowSumTermData[index]? with
  | none => false
  | some row =>
      decide (row.size = 4) &&
        orbitIndexCheck (orbitEntry row 0)
          basisOrbitRepresentativeData.size &&
        orbitIndexCheck (orbitEntry row 1) gramOrbitData.size &&
        decide (orbitEntry row 3 = orbitGramValue (orbitEntry row 1))

def orbitRowSumCheck : Bool :=
  decide (rowSumEquationData.size = basisOrbitRepresentativeData.size) &&
    (List.range basisOrbitRepresentativeData.size).all orbitRowSumRowCheck

def orbitRowSumTermGramCheck : Bool :=
  (List.range rowSumTermData.size).all orbitRowSumTermGramRowCheck

def orbitPairCoverageRowCheck (index : Nat) : Bool :=
  match pairOrbitIndexData[index]? with
  | none => false
  | some row =>
      decide (row.size = basisData.size) &&
        row.toList.all fun orbit => orbitIndexCheck orbit gramOrbitData.size

def orbitPairCoverageCheck : Bool :=
  decide (pairOrbitIndexData.size = basisOrbitRepresentativeData.size) &&
    (List.range pairOrbitIndexData.size).all orbitPairCoverageRowCheck

def orbitCoefficientTermGramOrbitCheck : Bool :=
  decide
      (coefficientTermGramOrbitIndexData.size = coefficientTermData.size) &&
    (List.range coefficientTermData.size).all
      orbitCoefficientTermGramOrbitRowCheck

def orbitGramTermIndexCheck : Bool :=
  decide (gramOrbitTermIndexData.size = gramOrbitData.size) &&
    (List.range gramOrbitData.size).all orbitGramTermIndexRowCheck

def orbitCoefficientOrbitEquationCheck : Bool :=
  decide
      (coefficientOrbitEquationIndexData.size =
        coefficientRepresentativeData.size) &&
    decide
      (coefficientTargetData.size = coefficientRepresentativeData.size) &&
    (List.range coefficientRepresentativeData.size).all
      orbitCoefficientOrbitEquationRowCheck

def orbitGramIncidenceCheck : Bool :=
  (List.range gramOrbitData.size).all orbitGramIncidenceRowCheck

def orbitGramStabilizerCheck : Bool :=
  (List.range gramOrbitData.size).all orbitGramStabilizerRowCheck

def orbitGramOrbitSizeTotalCheck : Bool :=
  decide
    (gramOrbitData.toList.foldl
      (fun total row => total + orbitEntry row 7) 0 =
        (basisData.size * basisData.size : Nat))

def orbitCoefficientSlicePartitionCheck : Bool :=
  (List.range coefficientEquationData.size).all
    orbitCoefficientSlicePartitionRowCheck

def orbitBasisPermutationRowCheck (index : Nat) : Bool :=
  match basisPermutationData[index]? with
  | none => false
  | some row =>
      decide (row.size = basisData.size) &&
        row.toList.all fun target => orbitIndexCheck target basisData.size

def orbitBasisPermutationCheck : Bool :=
  decide (basisPermutationData.size = symmetryData.size) &&
    (List.range basisPermutationData.size).all
      orbitBasisPermutationRowCheck

def orbitBasisRepresentative (index : Nat) : Nat :=
  (orbitEntry (basisOrbitRepresentativeData.getD index #[]) 0).toNat

def orbitBasisTransportRowCheck (index : Nat) : Bool :=
  match basisTransporterData[index]? with
  | none => false
  | some row =>
      let orbit := orbitEntry row 0
      let symmetry := orbitEntry row 1
      decide (row.size = 2) &&
        orbitIndexCheck orbit basisOrbitRepresentativeData.size &&
        orbitIndexCheck symmetry symmetryData.size &&
        decide
          (symmetryBasisImage symmetry.toNat
            (orbitBasisRepresentative orbit.toNat) = index)

def orbitBasisTransportCheck : Bool :=
  decide (basisTransporterData.size = basisData.size) &&
    (List.range basisTransporterData.size).all orbitBasisTransportRowCheck

def orbitSymmetryInverseEntryCheck (symmetry index : Nat) : Bool :=
  let inverse := inverseSymmetry symmetry
  decide (symmetry < symmetryData.size) &&
    decide (inverse < symmetryData.size) &&
    decide (index < basisData.size) &&
    decide (symmetryBasisImage inverse
      (symmetryBasisImage symmetry index) = index) &&
    decide (symmetryBasisImage symmetry
      (symmetryBasisImage inverse index) = index)

def orbitSymmetryInverseRowCheck (symmetry : Nat) : Bool :=
  match symmetryInverseData[symmetry]? with
  | none => false
  | some row =>
      decide (row.size = 1) &&
        orbitIndexCheck (orbitEntry row 0) symmetryData.size &&
        (List.range basisData.size).all
          (orbitSymmetryInverseEntryCheck symmetry)

def orbitSymmetryInverseCheck : Bool :=
  decide (symmetryInverseData.size = symmetryData.size) &&
    (List.range symmetryInverseData.size).all orbitSymmetryInverseRowCheck

def orbitPairWitnessEntryCheck (basisOrbit second : Nat) : Bool :=
  let orbit := dataEntry pairOrbitIndexData basisOrbit second
  let packed := dataEntry pairOrbitWitnessData basisOrbit second
  let symmetry := packed.toNat / 2
  let transpose := packed.toNat % 2 = 1
  let representative := gramOrbitData.getD orbit.toNat #[]
  let firstRepresentative :=
    if transpose then orbitEntry representative 1
    else orbitEntry representative 0
  let secondRepresentative :=
    if transpose then orbitEntry representative 0
    else orbitEntry representative 1
  decide (basisOrbit < basisOrbitRepresentativeData.size) &&
    decide (second < basisData.size) &&
    orbitIndexCheck orbit gramOrbitData.size &&
    orbitIndexCheck packed (2 * symmetryData.size) &&
    orbitIndexCheck firstRepresentative basisData.size &&
    orbitIndexCheck secondRepresentative basisData.size &&
    decide (symmetryBasisImage symmetry firstRepresentative.toNat =
      orbitBasisRepresentative basisOrbit) &&
    decide (symmetryBasisImage symmetry secondRepresentative.toNat = second)

def orbitPairWitnessRowCheck (index : Nat) : Bool :=
  match pairOrbitWitnessData[index]? with
  | none => false
  | some row =>
      decide (row.size = basisData.size) &&
        (List.range basisData.size).all (orbitPairWitnessEntryCheck index)

def orbitPairWitnessCheck : Bool :=
  decide (pairOrbitWitnessData.size = basisOrbitRepresentativeData.size) &&
    (List.range pairOrbitWitnessData.size).all orbitPairWitnessRowCheck

def orbitGramRepresentativeRowCheck (index : Nat) : Bool :=
  match gramOrbitData[index]? with
  | none => false
  | some row =>
      let left := orbitEntry row 0
      let right := orbitEntry row 1
      decide (row.size = gramOrbitRowWidth) &&
        orbitIndexCheck left basisData.size &&
        orbitIndexCheck right basisData.size &&
        orbitIndexCheck (orbitEntry row 2)
          coefficientRepresentativeData.size &&
        decide (0 ≤ orbitEntry row 3) &&
        orbitIndexCheck (orbitEntry row 5) symmetryData.size &&
        decide (orbitEntry row 6 = 0 ∨ orbitEntry row 6 = 1) &&
        decide (0 < orbitEntry row 7) &&
        decide (pairOrbit left.toNat right.toNat = index)

def orbitGramRepresentativeCheck : Bool :=
  (List.range gramOrbitData.size).all orbitGramRepresentativeRowCheck

theorem orbitIndexCheck_sound
    (index : Int) (bound : Nat)
    (hcheck : orbitIndexCheck index bound = true) :
    0 ≤ index ∧ index < (bound : Int) := by
  simpa only [orbitIndexCheck, decide_eq_true_eq] using hcheck

theorem orbitGramIncidenceRowCheck_sound
    (index : Nat) (row : Array Int)
    (hrow : gramOrbitData[index]? = some row)
    (hcheck : orbitGramIncidenceRowCheck index = true) :
    row.size = gramOrbitRowWidth ∧
      (0 ≤ orbitEntry row 2 ∧
        orbitEntry row 2 < (coefficientOrbitSizeData.size : Int)) ∧
      0 < orbitEntry row 3 ∧
      0 < dataEntry coefficientOrbitSizeData (orbitEntry row 2).toNat 0 ∧
      orbitEntry row 7 = orbitEntry row 3 *
        dataEntry coefficientOrbitSizeData (orbitEntry row 2).toNat 0 := by
  simp only [orbitGramIncidenceRowCheck, hrow, orbitIndexCheck,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with
    ⟨⟨⟨⟨hwidth, hindex⟩, hincidence⟩, hsize⟩, hcardinality⟩
  exact ⟨hwidth, hindex, hincidence, hsize, hcardinality⟩

theorem orbitGramStabilizerRowCheck_sound
    (index : Nat) (row : Array Int)
    (hrow : gramOrbitData[index]? = some row)
    (hcheck : orbitGramStabilizerRowCheck index = true) :
    (0 ≤ orbitEntry row 0 ∧ orbitEntry row 0 < (basisData.size : Int)) ∧
      (0 ≤ orbitEntry row 1 ∧ orbitEntry row 1 < (basisData.size : Int)) ∧
      0 < orbitEntry row 7 ∧
      orbitEntry row 7 *
        (orbitGramStabilizerCount
          (orbitEntry row 0).toNat (orbitEntry row 1).toNat : Int) =
          (2 * symmetryData.size : Nat) := by
  simp only [orbitGramStabilizerRowCheck, hrow, orbitIndexCheck,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨hleft, hright⟩, hsize⟩, hcardinality⟩
  exact ⟨hleft, hright, hsize, hcardinality⟩

theorem orbitGramOrbitSizeTotalCheck_sound
    (hcheck : orbitGramOrbitSizeTotalCheck = true) :
    gramOrbitData.toList.foldl
      (fun total row => total + orbitEntry row 7) 0 =
        (basisData.size * basisData.size : Nat) := by
  simpa only [orbitGramOrbitSizeTotalCheck, decide_eq_true_eq] using hcheck

theorem orbitCoefficientRowCheck_sound
    (index : Nat) (row : Array Int)
    (hrow : coefficientEquationData[index]? = some row)
    (hcheck : orbitCoefficientRowCheck index = true) :
    row.size = coefficientEquationRowWidth ∧
      0 ≤ orbitEntry row 1 ∧
      0 ≤ orbitEntry row 2 ∧
      (orbitEntry row 1).toNat + (orbitEntry row 2).toNat ≤
        coefficientTermData.size ∧
      orbitCoefficientRangeTermsCheck
        (orbitEntry row 1).toNat (orbitEntry row 2).toNat
          (orbitEntry row 0) = true ∧
      orbitCoefficientRangeTotal
        (orbitEntry row 1).toNat (orbitEntry row 2).toNat =
          orbitEntry row 3 := by
  simp only [orbitCoefficientRowCheck, hrow, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  rcases hcheck with
    ⟨⟨⟨⟨⟨hwidth, hstart⟩, hcount⟩, hbound⟩, hterms⟩, htotal⟩
  exact ⟨hwidth, hstart, hcount, hbound, hterms, htotal⟩

theorem orbitRowSumRowCheck_sound
    (index : Nat) (hcheck : orbitRowSumRowCheck index = true) :
    index < basisOrbitRepresentativeData.size ∧
      orbitRowSumTotal index = 0 := by
  unfold orbitRowSumRowCheck at hcheck
  split at hcheck
  next => contradiction
  next row hrow =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck with
      ⟨⟨⟨⟨⟨⟨⟨hindex, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hzero⟩
    refine ⟨hindex, ?_⟩
    simp only [orbitRowSumTotal, Int.toNat_natCast, hrow]
    exact hzero

theorem orbitPairCoverageRowCheck_sound
    (index : Nat) (row : Array Int)
    (hrow : pairOrbitIndexData[index]? = some row)
    (hcheck : orbitPairCoverageRowCheck index = true) :
    row.size = basisData.size ∧
      row.toList.all
        (fun orbit => orbitIndexCheck orbit gramOrbitData.size) = true := by
  simpa only [orbitPairCoverageRowCheck, hrow, Bool.and_eq_true,
    decide_eq_true_eq] using hcheck

theorem orbitBasisTransportRowCheck_sound
    (index : Nat) (row : Array Int)
    (hrow : basisTransporterData[index]? = some row)
    (hcheck : orbitBasisTransportRowCheck index = true) :
    row.size = 2 ∧
      (0 ≤ orbitEntry row 0 ∧
        orbitEntry row 0 < (basisOrbitRepresentativeData.size : Int)) ∧
      (0 ≤ orbitEntry row 1 ∧
        orbitEntry row 1 < (symmetryData.size : Int)) ∧
      symmetryBasisImage (orbitEntry row 1).toNat
        (orbitBasisRepresentative (orbitEntry row 0).toNat) = index := by
  simp only [orbitBasisTransportRowCheck, hrow, orbitIndexCheck,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨hwidth, horbit⟩, hsymmetry⟩, htransport⟩
  exact ⟨hwidth, horbit, hsymmetry, htransport⟩

theorem orbitPairWitnessEntryCheck_sound
    (basisOrbit second : Nat)
    (hcheck : orbitPairWitnessEntryCheck basisOrbit second = true) :
    basisOrbit < basisOrbitRepresentativeData.size ∧
      second < basisData.size ∧
      (0 ≤ dataEntry pairOrbitIndexData basisOrbit second ∧
        dataEntry pairOrbitIndexData basisOrbit second <
          (gramOrbitData.size : Int)) ∧
      (0 ≤ dataEntry pairOrbitWitnessData basisOrbit second ∧
        dataEntry pairOrbitWitnessData basisOrbit second <
          (2 * symmetryData.size : Nat)) := by
  simp only [orbitPairWitnessEntryCheck, Bool.and_eq_true,
    orbitIndexCheck, decide_eq_true_eq] at hcheck
  rcases hcheck with
    ⟨⟨⟨⟨⟨⟨⟨horbit, hsecond⟩, hgram⟩, hwitness⟩, _⟩, _⟩, _⟩, _⟩
  exact ⟨horbit, hsecond, hgram, hwitness⟩

end

end ConnesRigidity.AffineSymplecticOrbitCertificate




import ConnesRigidity.PropertyTExactCertificateOrbitBasis
import ConnesRigidity.PropertyTExactCertificateOrbitCheckers














namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section


theorem orbitListRangeAll_iff (check : Nat → Bool) (bound : Nat) :
    (List.range bound).all check = true ↔
      ∀ index, index < bound → check index = true := by
  simp only [List.all_eq_true, List.mem_range]


theorem orbitArrayToListAll_iff {α : Type*}
    (rows : Array α) (check : α → Bool) :
    rows.toList.all check = true ↔
      ∀ index (hindex : index < rows.size), check rows[index] = true := by
  simp


theorem orbitArrayToListAll_get {α : Type*}
    (rows : Array α) (check : α → Bool)
    (hcheck : rows.toList.all check = true)
    (index : Nat) (hindex : index < rows.size) :
    check rows[index] = true :=
  (orbitArrayToListAll_iff rows check).mp hcheck index hindex


theorem orbitCoefficientCheck_sound
    (hcheck : orbitCoefficientCheck = true) :
    ∀ index, index < coefficientEquationData.size →
      orbitCoefficientRowCheck index = true :=
  (orbitListRangeAll_iff orbitCoefficientRowCheck
    coefficientEquationData.size).mp hcheck


theorem orbitRowSumCheck_sound (hcheck : orbitRowSumCheck = true) :
    ∀ index, index < basisOrbitRepresentativeData.size →
      orbitRowSumTotal index = 0 := by
  simp only [orbitRowSumCheck, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  intro index hindex
  have hrow := (orbitListRangeAll_iff orbitRowSumRowCheck
    basisOrbitRepresentativeData.size).mp hcheck.2 index hindex
  exact (orbitRowSumRowCheck_sound index hrow).2


theorem orbitPairCoverageCheck_sound
    (hcheck : orbitPairCoverageCheck = true) :
    pairOrbitIndexData.size = basisOrbitRepresentativeData.size ∧
      ∀ index, index < pairOrbitIndexData.size →
        orbitPairCoverageRowCheck index = true := by
  simp only [orbitPairCoverageCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at hcheck
  exact hcheck


theorem orbitBasisPermutationCheck_sound
    (hcheck : orbitBasisPermutationCheck = true) :
    basisPermutationData.size = symmetryData.size ∧
      ∀ index, index < basisPermutationData.size →
        orbitBasisPermutationRowCheck index = true := by
  simpa only [orbitBasisPermutationCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] using hcheck


theorem orbitBasisTransportCheck_sound
    (hcheck : orbitBasisTransportCheck = true) :
    basisTransporterData.size = basisData.size ∧
      ∀ index, index < basisTransporterData.size →
        orbitBasisTransportRowCheck index = true := by
  simpa only [orbitBasisTransportCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] using hcheck


theorem orbitSymmetryInverseCheck_sound
    (hcheck : orbitSymmetryInverseCheck = true) :
    symmetryInverseData.size = symmetryData.size ∧
      ∀ index, index < symmetryInverseData.size →
        orbitSymmetryInverseRowCheck index = true := by
  simpa only [orbitSymmetryInverseCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] using hcheck


theorem orbitPairWitnessCheck_sound
    (hcheck : orbitPairWitnessCheck = true) :
    pairOrbitWitnessData.size = basisOrbitRepresentativeData.size ∧
      ∀ index, index < pairOrbitWitnessData.size →
        orbitPairWitnessRowCheck index = true := by
  simpa only [orbitPairWitnessCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] using hcheck


theorem orbitCoefficientTermGramOrbitCheck_sound
    (hcheck : orbitCoefficientTermGramOrbitCheck = true) :
    coefficientTermGramOrbitIndexData.size = coefficientTermData.size ∧
      ∀ index, index < coefficientTermData.size →
        orbitCoefficientTermGramOrbitRowCheck index = true := by
  simpa only [orbitCoefficientTermGramOrbitCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] using hcheck


theorem orbitGramTermIndexCheck_sound
    (hcheck : orbitGramTermIndexCheck = true) :
    gramOrbitTermIndexData.size = gramOrbitData.size ∧
      ∀ index, index < gramOrbitData.size →
        orbitGramTermIndexRowCheck index = true := by
  simpa only [orbitGramTermIndexCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] using hcheck


theorem orbitCoefficientOrbitEquationCheck_sound
    (hcheck : orbitCoefficientOrbitEquationCheck = true) :
    coefficientOrbitEquationIndexData.size =
        coefficientRepresentativeData.size ∧
      coefficientTargetData.size = coefficientRepresentativeData.size ∧
      ∀ index, index < coefficientRepresentativeData.size →
        orbitCoefficientOrbitEquationRowCheck index = true := by
  simpa only [orbitCoefficientOrbitEquationCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range, and_assoc] using hcheck


theorem orbitGramIncidenceCheck_sound
    (hcheck : orbitGramIncidenceCheck = true) :
    ∀ index, index < gramOrbitData.size →
      orbitGramIncidenceRowCheck index = true :=
  (orbitListRangeAll_iff orbitGramIncidenceRowCheck
    gramOrbitData.size).mp hcheck


theorem orbitCoefficientSlicePartitionCheck_sound
    (hcheck : orbitCoefficientSlicePartitionCheck = true) :
    ∀ index, index < coefficientEquationData.size →
      orbitCoefficientSlicePartitionRowCheck index = true :=
  (orbitListRangeAll_iff orbitCoefficientSlicePartitionRowCheck
    coefficientEquationData.size).mp hcheck


theorem orbitGramRepresentativeCheck_sound
    (hcheck : orbitGramRepresentativeCheck = true) :
    ∀ index, index < gramOrbitData.size →
      orbitGramRepresentativeRowCheck index = true :=
  (orbitListRangeAll_iff orbitGramRepresentativeRowCheck
    gramOrbitData.size).mp hcheck


theorem orbitPairCoverageRowCheck_sound_entry
    (index : Nat) (row : Array Int)
    (hrow : pairOrbitIndexData[index]? = some row)
    (hcheck : orbitPairCoverageRowCheck index = true)
    (column : Nat) (hcolumn : column < row.size) :
    0 ≤ row[column] ∧ row[column] < (gramOrbitData.size : Int) := by
  have hall := (orbitPairCoverageRowCheck_sound index row hrow hcheck).2
  have hentry := List.all_eq_true.mp hall _
    (Array.getElem_mem_toList hcolumn)
  exact orbitIndexCheck_sound _ _ hentry







theorem orbitPairWitnessEntryCheck_sound_full
    (basisOrbit second : Nat)
    (hcheck : orbitPairWitnessEntryCheck basisOrbit second = true) :
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
    basisOrbit < basisOrbitRepresentativeData.size ∧
      second < basisData.size ∧
      (0 ≤ orbit ∧ orbit < (gramOrbitData.size : Int)) ∧
      (0 ≤ packed ∧ packed < (2 * symmetryData.size : Nat)) ∧
      (0 ≤ firstRepresentative ∧
        firstRepresentative < (basisData.size : Int)) ∧
      (0 ≤ secondRepresentative ∧
        secondRepresentative < (basisData.size : Int)) ∧
      symmetryBasisImage symmetry firstRepresentative.toNat =
        orbitBasisRepresentative basisOrbit ∧
      symmetryBasisImage symmetry secondRepresentative.toNat = second := by
  simpa only [orbitPairWitnessEntryCheck, orbitIndexCheck,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hcheck


theorem orbitPairWitnessRowCheck_sound
    (basisOrbit : Nat) (row : Array Int)
    (hrow : pairOrbitWitnessData[basisOrbit]? = some row)
    (hcheck : orbitPairWitnessRowCheck basisOrbit = true) :
    row.size = basisData.size ∧
      ∀ second, second < basisData.size →
        orbitPairWitnessEntryCheck basisOrbit second = true := by
  simpa only [orbitPairWitnessRowCheck, hrow, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] using hcheck


theorem orbitPairWitnessRowCheck_entry_sound_full
    (basisOrbit second : Nat) (row : Array Int)
    (hrow : pairOrbitWitnessData[basisOrbit]? = some row)
    (hcheck : orbitPairWitnessRowCheck basisOrbit = true)
    (hsecond : second < basisData.size) :
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
    basisOrbit < basisOrbitRepresentativeData.size ∧
      second < basisData.size ∧
      (0 ≤ orbit ∧ orbit < (gramOrbitData.size : Int)) ∧
      (0 ≤ packed ∧ packed < (2 * symmetryData.size : Nat)) ∧
      (0 ≤ firstRepresentative ∧
        firstRepresentative < (basisData.size : Int)) ∧
      (0 ≤ secondRepresentative ∧
        secondRepresentative < (basisData.size : Int)) ∧
      symmetryBasisImage symmetry firstRepresentative.toNat =
        orbitBasisRepresentative basisOrbit ∧
      symmetryBasisImage symmetry secondRepresentative.toNat = second := by
  exact orbitPairWitnessEntryCheck_sound_full basisOrbit second
    ((orbitPairWitnessRowCheck_sound basisOrbit row hrow hcheck).2
      second hsecond)

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

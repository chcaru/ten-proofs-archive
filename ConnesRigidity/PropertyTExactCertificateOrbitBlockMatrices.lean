


import ConnesRigidity.PropertyTExactCertificateOrbitData
import ConnesRigidity.PropertyTExactCertificateOrbitBlockLocalData
import ConnesRigidity.PropertyTExactCertificateOrbitMatrixAlgebra














namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators


noncomputable def blockDimension (block : Nat) : Nat :=
  (dataEntry blockMetadataData block 0).toNat



noncomputable def blockRowStart (block : Nat) : Nat :=
  (dataEntry blockMetadataData block 4).toNat



noncomputable def denseBlockEntry
    (rows : List (List Int)) (block row column : Nat) : Int :=
  ((rows.getD (blockRowStart block + row) []).getD (column + 2) 0)


noncomputable def blockGramEntryInt (block row column : Nat) : Int :=
  (blockGramLocalData block).getD row [] |>.getD column 0


noncomputable def blockFactorEntryInt (block row column : Nat) : Int :=
  (blockFactorLocalData block).getD row [] |>.getD column 0


noncomputable def blockResidualEntryInt (block row column : Nat) : Int :=
  (blockResidualLocalData block).getD row [] |>.getD column 0


noncomputable def blockSlackEntryInt (block row : Nat) : Int :=
  dataEntry blockSlackData (blockRowStart block + row) 2


noncomputable def orbitReducedGram : Matrix (Fin 424) (Fin 424) ℚ :=
  fun row column => (gramEntry (row.val + 1) (column.val + 1) : ℚ)


noncomputable def congruenceEntryInt (row column : Nat) : Int :=
  congruenceData.toList.foldl
    (fun total entry =>
      if entry.getD 0 0 = (row : Int) ∧
          entry.getD 1 0 = (column : Int) then
        total + entry.getD 2 0
      else
        total)
    0


noncomputable def orbitCongruence : Matrix (Fin 424) (Fin 424) ℚ :=
  fun row column => (congruenceEntryInt row.val column.val : ℚ)


noncomputable def congruenceInverseEntry
    (row column : Nat) : ℚ :=
  congruenceInverseData.toList.foldl
    (fun total entry =>
      if entry.getD 0 0 = (row : Int) ∧
          entry.getD 1 0 = (column : Int) then
        total + (entry.getD 2 0 : ℚ) / (entry.getD 3 1 : ℚ)
      else
        total)
    0


noncomputable def orbitCongruenceInverse :
    Matrix (Fin 424) (Fin 424) ℚ :=
  fun row column => congruenceInverseEntry row.val column.val


noncomputable def blockGram (block : Nat) :
    Matrix (Fin (blockDimension block)) (Fin (blockDimension block)) ℚ :=
  fun row column => (blockGramEntryInt block row.val column.val : ℚ)


noncomputable def blockFactor (block : Nat) :
    Matrix (Fin (blockDimension block)) (Fin (blockDimension block)) ℚ :=
  fun row column => (blockFactorEntryInt block row.val column.val : ℚ)


noncomputable def blockResidual (block : Nat) :
    Matrix (Fin (blockDimension block)) (Fin (blockDimension block)) ℚ :=
  fun row column => (blockResidualEntryInt block row.val column.val : ℚ)

@[simp] theorem orbitReducedGram_apply (row column : Fin 424) :
    orbitReducedGram row column =
      (gramEntry (row.val + 1) (column.val + 1) : ℚ) := rfl

@[simp] theorem orbitCongruence_apply (row column : Fin 424) :
    orbitCongruence row column =
      (congruenceEntryInt row.val column.val : ℚ) := rfl

@[simp] theorem orbitCongruenceInverse_apply (row column : Fin 424) :
    orbitCongruenceInverse row column =
      congruenceInverseEntry row.val column.val := rfl

@[simp] theorem blockGram_apply (block : Nat)
    (row column : Fin (blockDimension block)) :
    blockGram block row column =
      (blockGramEntryInt block row.val column.val : ℚ) := rfl

@[simp] theorem blockFactor_apply (block : Nat)
    (row column : Fin (blockDimension block)) :
    blockFactor block row column =
      (blockFactorEntryInt block row.val column.val : ℚ) := rfl

@[simp] theorem blockResidual_apply (block : Nat)
    (row column : Fin (blockDimension block)) :
    blockResidual block row column =
      (blockResidualEntryInt block row.val column.val : ℚ) := rfl


noncomputable def blockFactorDotInt (block row column : Nat) : Int :=
  ∑ k : Fin (blockDimension block),
    blockFactorEntryInt block k.val row *
      blockFactorEntryInt block k.val column


noncomputable def blockFactorIdentityEntryCheck
    (block row column : Nat) : Bool :=
  decide (factorScale ^ 2 * blockGramEntryInt block row column =
    blockFactorDotInt block row column +
      blockResidualEntryInt block row column)


noncomputable def blockResidualSymmetricEntryCheck
    (block row column : Nat) : Bool :=
  decide (blockResidualEntryInt block row column =
    blockResidualEntryInt block column row)


noncomputable def blockResidualOffDiagonalMassInt
    (block row : Nat) : Int :=
  ∑ column : Fin (blockDimension block),
    if column.val = row then 0 else
      |blockResidualEntryInt block row column.val|


noncomputable def blockResidualDominanceRowCheck
    (block row : Nat) : Bool :=
  decide (blockResidualOffDiagonalMassInt block row ≤
    blockResidualEntryInt block row row)


noncomputable def blockSlackRowCheck (block row : Nat) : Bool :=
  decide (blockSlackEntryInt block row =
    blockResidualEntryInt block row row -
      blockResidualOffDiagonalMassInt block row ∧
    0 < blockSlackEntryInt block row)




def localBlockFactorDot
    (factor : List (List Int)) (row column : Nat) : Int :=
  factor.foldl
    (fun total coefficients =>
      total + coefficients.getD row 0 * coefficients.getD column 0)
    0



noncomputable def blockFactorIdentityBlockCheck (block : Nat) : Bool :=
  let dimension := blockDimension block
  let gram := blockGramLocalData block
  let factor := blockFactorLocalData block
  let residual := blockResidualLocalData block
  decide (gram.length = dimension ∧ factor.length = dimension ∧
    residual.length = dimension) &&
    (List.range dimension).all fun row =>
      (List.range dimension).all fun column =>
        decide (factorScale ^ 2 *
          (gram.getD row []).getD column 0 =
            localBlockFactorDot factor row column +
              (residual.getD row []).getD column 0)


noncomputable def blockResidualSymmetryBlockCheck (block : Nat) : Bool :=
  let dimension := blockDimension block
  let residual := blockResidualLocalData block
  (List.range dimension).all fun row =>
    (List.range dimension).all fun column =>
      decide ((residual.getD row []).getD column 0 =
        (residual.getD column []).getD row 0)


noncomputable def blockResidualDominanceBlockCheck (block : Nat) : Bool :=
  (List.range (blockDimension block)).all fun row =>
    blockResidualDominanceRowCheck block row

private theorem list_row_dot_eq_fin_sum
    (rows : List (List Int)) (row column : Nat) :
    localBlockFactorDot rows row column =
      ∑ index : Fin rows.length,
        (rows.getD index.val []).getD row 0 *
          (rows.getD index.val []).getD column 0 := by
  unfold localBlockFactorDot
  rw [← List.foldl_map, ← List.sum_eq_foldl]
  induction rows with
  | nil => simp
  | cons head tail ih =>
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simpa only [List.map_cons, List.sum_cons, List.length_cons,
        List.getD_cons_zero, List.getD_cons_succ,
        Fin.val_zero, Fin.val_succ] using congrArg
          (fun value => head.getD row 0 * head.getD column 0 + value) ih

private theorem localBlockFactorDot_eq (block row column : Nat)
    (hshape : (blockFactorLocalData block).length = blockDimension block) :
    localBlockFactorDot (blockFactorLocalData block) row column =
      blockFactorDotInt block row column := by
  have hsum := list_row_dot_eq_fin_sum
    (blockFactorLocalData block) row column
  rw [hshape] at hsum
  simpa only [blockFactorDotInt, blockFactorEntryInt] using hsum

theorem blockFactorIdentityEntryCheck_sound
    (block row column : Nat)
    (hcheck : blockFactorIdentityEntryCheck block row column = true) :
    factorScale ^ 2 * blockGramEntryInt block row column =
      blockFactorDotInt block row column +
        blockResidualEntryInt block row column := by
  simpa only [blockFactorIdentityEntryCheck, decide_eq_true_eq] using hcheck

theorem blockResidualSymmetricEntryCheck_sound
    (block row column : Nat)
    (hcheck : blockResidualSymmetricEntryCheck block row column = true) :
    blockResidualEntryInt block row column =
      blockResidualEntryInt block column row := by
  simpa only [blockResidualSymmetricEntryCheck, decide_eq_true_eq] using hcheck

theorem blockResidualDominanceRowCheck_sound
    (block row : Nat)
    (hcheck : blockResidualDominanceRowCheck block row = true) :
    blockResidualOffDiagonalMassInt block row ≤
      blockResidualEntryInt block row row := by
  simpa only [blockResidualDominanceRowCheck, decide_eq_true_eq] using hcheck

theorem blockSlackRowCheck_sound
    (block row : Nat) (hcheck : blockSlackRowCheck block row = true) :
    blockSlackEntryInt block row =
        blockResidualEntryInt block row row -
          blockResidualOffDiagonalMassInt block row ∧
      0 < blockSlackEntryInt block row := by
  simpa only [blockSlackRowCheck, decide_eq_true_eq] using hcheck


theorem blockFactorIdentityBlockCheck_sound (block : Nat)
    (hcheck : blockFactorIdentityBlockCheck block = true) :
    ∀ row column : Fin (blockDimension block),
      blockFactorIdentityEntryCheck block row.val column.val = true := by
  unfold blockFactorIdentityBlockCheck at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨_, hfactor, _⟩, hrows⟩ := hcheck
  intro row column
  have hrow := (List.all_eq_true.mp hrows)
    row.val (List.mem_range.mpr row.isLt)
  have hcolumn := (List.all_eq_true.mp hrow)
    column.val (List.mem_range.mpr column.isLt)
  simp only [decide_eq_true_eq] at hcolumn
  unfold blockFactorIdentityEntryCheck
  apply decide_eq_true_eq.mpr
  simpa only [blockGramEntryInt, blockResidualEntryInt,
    localBlockFactorDot_eq block row.val column.val hfactor] using hcolumn


theorem blockResidualSymmetryBlockCheck_sound (block : Nat)
    (hcheck : blockResidualSymmetryBlockCheck block = true) :
    ∀ row column : Fin (blockDimension block),
      blockResidualSymmetricEntryCheck block row.val column.val = true := by
  unfold blockResidualSymmetryBlockCheck at hcheck
  intro row column
  have hrow := (List.all_eq_true.mp hcheck)
    row.val (List.mem_range.mpr row.isLt)
  have hcolumn := (List.all_eq_true.mp hrow)
    column.val (List.mem_range.mpr column.isLt)
  change decide (((blockResidualLocalData block).getD row.val []).getD
    column.val 0 = ((blockResidualLocalData block).getD column.val []).getD
      row.val 0) = true
  exact hcolumn


theorem blockResidualDominanceBlockCheck_sound (block : Nat)
    (hcheck : blockResidualDominanceBlockCheck block = true) :
    ∀ row : Fin (blockDimension block),
      blockResidualDominanceRowCheck block row.val = true := by
  unfold blockResidualDominanceBlockCheck at hcheck
  intro row
  exact (List.all_eq_true.mp hcheck)
    row.val (List.mem_range.mpr row.isLt)



theorem blockFactorDotInt_cast (block : Nat)
    (row column : Fin (blockDimension block)) :
    (blockFactorDotInt block row.val column.val : ℚ) =
      ((blockFactor block).transpose * blockFactor block) row column := by
  simp only [blockFactorDotInt, Matrix.mul_apply, Matrix.transpose_apply,
    blockFactor_apply, Int.cast_sum, Int.cast_mul]


theorem blockFactorIdentity_of_checks (block : Nat)
    (hcheck : ∀ row column : Fin (blockDimension block),
      blockFactorIdentityEntryCheck block row.val column.val = true) :
    ((factorScale : ℚ) ^ 2) • blockGram block =
      (blockFactor block).transpose * blockFactor block +
        blockResidual block := by
  ext row column
  have hentry := blockFactorIdentityEntryCheck_sound
    block row.val column.val (hcheck row column)
  have hcast :
      ((factorScale ^ 2 * blockGramEntryInt block row.val column.val : Int) : ℚ) =
        ((blockFactorDotInt block row.val column.val +
          blockResidualEntryInt block row.val column.val : Int) : ℚ) :=
    congrArg (fun value : Int => (value : ℚ)) hentry
  simpa only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    blockGram_apply, blockResidual_apply, Int.cast_mul, Int.cast_pow,
    Int.cast_add, blockFactorDotInt_cast] using hcast


theorem blockResidualSymmetric_of_checks (block : Nat)
    (hcheck : ∀ row column : Fin (blockDimension block),
      blockResidualSymmetricEntryCheck block row.val column.val = true) :
    (blockResidual block).IsSymm := by
  ext row column
  simpa only [Matrix.transpose_apply, blockResidual_apply] using
    congrArg (fun value : Int => (value : ℚ))
      (blockResidualSymmetricEntryCheck_sound
        block column.val row.val (hcheck column row))


theorem blockResidualOffDiagonalMassInt_cast (block : Nat)
    (row : Fin (blockDimension block)) :
    (blockResidualOffDiagonalMassInt block row.val : ℚ) =
      SDDCertificate.offDiagonalMass (blockResidual block) row := by
  simp only [blockResidualOffDiagonalMassInt,
    SDDCertificate.offDiagonalMass, blockResidual_apply, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro column _
  by_cases hcolumn : column = row
  · subst column
    simp
  · have hval : column.val ≠ row.val := by
      exact fun heq => hcolumn (Fin.ext heq)
    simp [hcolumn, hval]


theorem blockResidualDominant_of_checks (block : Nat)
    (hcheck : ∀ row : Fin (blockDimension block),
      blockResidualDominanceRowCheck block row.val = true) :
    SDDCertificate.IsDiagonallyDominant (blockResidual block) := by
  intro row
  rw [← blockResidualOffDiagonalMassInt_cast]
  change (blockResidualOffDiagonalMassInt block row.val : ℚ) ≤
    (blockResidualEntryInt block row.val row.val : ℚ)
  exact_mod_cast blockResidualDominanceRowCheck_sound
    block row.val (hcheck row)



theorem blockGram_isPositiveSumOfSquares
    {G : Type*} [Group G]
    (block : Nat)
    (atom : Fin (blockDimension block) → RationalGroupRing G)
    (hidentity : ∀ row column : Fin (blockDimension block),
      blockFactorIdentityEntryCheck block row.val column.val = true)
    (hsymmetric : ∀ row column : Fin (blockDimension block),
      blockResidualSymmetricEntryCheck block row.val column.val = true)
    (hdominant : ∀ row : Fin (blockDimension block),
      blockResidualDominanceRowCheck block row.val = true) :
    RationalGroupRing.IsPositiveSumOfSquares
      (OrbitPositivity.matrixAtomExpansion atom (blockGram block)) := by
  apply OrbitPositivity.scaled_gram_add_sdd_expansion_isPositiveSumOfSquares
    atom (blockGram block) (blockFactor block) (blockResidual block)
      (factorScale : ℚ)
  · norm_num [factorScale]
  · exact blockFactorIdentity_of_checks block hidentity
  · exact blockResidualSymmetric_of_checks block hsymmetric
  · exact blockResidualDominant_of_checks block hdominant



noncomputable def blockOfColumn (column : Nat) : Nat :=
  (dataEntry blockColumnData column 1).toNat


noncomputable def blockOffsetOfColumn (column : Nat) : Nat :=
  (dataEntry blockColumnData column 2).toNat



noncomputable def orbitBlockDiagonalGram : Matrix (Fin 424) (Fin 424) ℚ :=
  fun row column =>
    if blockOfColumn row.val = blockOfColumn column.val then
      (blockGramEntryInt (blockOfColumn row.val)
        (blockOffsetOfColumn row.val)
        (blockOffsetOfColumn column.val) : ℚ)
    else 0

@[simp] theorem orbitBlockDiagonalGram_apply (row column : Fin 424) :
    orbitBlockDiagonalGram row column =
      if blockOfColumn row.val = blockOfColumn column.val then
        (blockGramEntryInt (blockOfColumn row.val)
          (blockOffsetOfColumn row.val)
          (blockOffsetOfColumn column.val) : ℚ)
      else 0 := rfl



theorem orbitReducedGram_eq_inverse_block_congruence
    (hinverse : orbitCongruence * orbitCongruenceInverse = 1)
    (hcongruence :
      orbitCongruence.transpose * orbitReducedGram * orbitCongruence =
        orbitBlockDiagonalGram) :
    orbitReducedGram =
      orbitCongruenceInverse.transpose * orbitBlockDiagonalGram *
        orbitCongruenceInverse := by
  rw [← hcongruence]
  exact OrbitPositivity.matrix_eq_inverse_congruence
    orbitReducedGram orbitCongruence orbitCongruenceInverse hinverse

end ConnesRigidity.AffineSymplecticOrbitCertificate

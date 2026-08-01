
import ConnesRigidity.PropertyTExactCertificateChecks
import ConnesRigidity.PropertyTExactCertificateGram
import ConnesRigidity.PropertyTExactCertificateProduct

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000
set_option maxErrors 3

local instance gammaZeroDecidableEqProof :
    DecidableEq IntegralSymplecticCocycleInput.GammaZero :=
  fun x y =>
    decidable_of_iff (x.fst = y.fst ∧ x.snd = y.snd)
      ⟨fun h ↦ by cases x; cases y; simp_all,
       fun h ↦ ⟨congrArg CocycleExtension.fst h,
         congrArg CocycleExtension.snd h⟩⟩

noncomputable local instance constructedGammaZeroDecidableEqProof :
    DecidableEq constructedGammaZeroGroup :=
  Classical.decEq _

private abbrev denominator : ℚ := 2000000000000

noncomputable def tableAtom (k : Fin 73033) : GroupRing :=
  MonoidAlgebra.single (tableElement k) 1

theorem interpretedCertificate_eq_target :
    interpretIntegerTerms tableAtom certificateTerms =
      interpretIntegerTerms tableAtom targetTerms := by
  exact coefficientIdentity_sound tableAtom

theorem sparseSquare_eq_terms
    (weight : ℤ) (entries : List (Fin 425 × ℤ)) :
    ((weight : ℚ) / denominator) •
        (RationalGroupRing.adjoint (sparseVector entries) *
          sparseVector entries) =
      (1 / denominator) •
        interpretIntegerTerms tableAtom
          (integerOuterTerms weight entries) := by
  unfold sparseVector integerOuterTerms
  rw [show tableAtom =
      (fun k : Fin 73033 ↦
        MonoidAlgebra.single (tableElement k) 1) by
    funext k
    rfl]
  exact weightedSparseSquare_eq_interpretIntegerTerms
      certificateBasis tableElement
      tableIndex tableElement_index_product_valid denominator weight entries

private theorem list_sum_flatMap
    {A B : Type*} [AddCommMonoid B]
    (entries : List A) (f : A → List B) :
    (entries.flatMap f).sum =
      (entries.map fun entry ↦ (f entry).sum).sum := by
  induction entries with
  | nil => simp
  | cons entry entries ih => simp [ih]

theorem interpretIntegerTerms_append
    (left right : List (IntegerTableTerm 73033)) :
    interpretIntegerTerms tableAtom (left ++ right) =
      interpretIntegerTerms tableAtom left +
        interpretIntegerTerms tableAtom right := by
  simp [interpretIntegerTerms]

theorem interpretIntegerTerms_flatMap
    {A : Type*} (entries : List A)
    (f : A → List (IntegerTableTerm 73033)) :
    interpretIntegerTerms tableAtom (entries.flatMap f) =
      (entries.map fun entry ↦
        interpretIntegerTerms tableAtom (f entry)).sum := by
  rw [interpretIntegerTerms, List.map_flatMap, list_sum_flatMap]
  rfl

theorem interpretIntegerTerms_flatten
    (terms : List (List (IntegerTableTerm 73033))) :
    interpretIntegerTerms tableAtom terms.flatten =
      (terms.map fun term ↦
        interpretIntegerTerms tableAtom term).sum := by
  induction terms with
  | nil => simp [interpretIntegerTerms]
  | cons term terms ih =>
      rw [List.flatten_cons, interpretIntegerTerms_append,
        List.map_cons, List.sum_cons, ih]

private theorem map_finRange_eq_map_range
    {α : Type*} {n : Nat} (f : Fin n → α) (g : Nat → α)
    (h : ∀ i : Fin n, f i = g i) :
    (List.finRange n).map f = (List.range n).map g := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp only [List.length_map, List.length_finRange] at hi₁
    simpa using h ⟨i, hi₁⟩

private theorem zipWith_eq_map_range
    {α β γ : Type*} (f : α → β → γ)
    (left : List α) (right : List β)
    (leftDefault : α) (rightDefault : β) (n : Nat)
    (hleft : left.length = n) (hright : right.length = n) :
    List.zipWith f left right =
      (List.range n).map fun i =>
        f (left.getD i leftDefault) (right.getD i rightDefault) := by
  apply List.ext_getElem
  · simp [hleft, hright]
  · intro i _ hi
    have hli : i < left.length := by simpa [hleft] using hi
    have hri : i < right.length := by simpa [hright] using hi
    simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ hli,
      List.getD_eq_getElem _ _ hri]

private theorem factorTermRow_eq_map (i : Fin 425) :
    factorTermRow i =
      (List.finRange 425).map fun j =>
        { key := tableIndex i j
          numerator := 8 * fullGramCoefficient i j } := by
  unfold factorTermRow
  rw [← coefficientFullGramData_getD i]
  rw [zipWith_eq_map_range _ _ _ 0 0 425
    (by simp [productIndexDataRow_size i])
    (fullGramDataRow_length i)]
  unfold tableIndex productIndex fullGramCoefficient
  symm
  apply map_finRange_eq_map_range
  intro j
  congr 1
  simp only [Array.getD_eq_getD_getElem?,
    List.getD_eq_getElem?_getD, Array.getElem?_toList]

theorem interpret_factorTerms :
    interpretIntegerTerms tableAtom factorTerms =
      ∑ i : Fin 425, ∑ j : Fin 425,
        (8 * (fullGramCoefficient i j : ℚ)) •
          tableAtom (tableIndex i j) := by
  rw [factorTerms, interpretIntegerTerms_flatMap]
  rw [← List.sum_toFinset _ (List.nodup_finRange 425)]
  simp only [List.toFinset_finRange]
  apply Finset.sum_congr rfl
  intro i hi
  rw [factorTermRow_eq_map, interpretIntegerTerms]
  simp only [List.map_map]
  rw [← List.sum_toFinset _ (List.nodup_finRange 425)]
  simp only [List.toFinset_finRange]
  apply Finset.sum_congr rfl
  intro j hj
  change
    (↑(8 * fullGramCoefficient i j) : ℚ) •
        tableAtom (tableIndex i j) =
      (8 * (fullGramCoefficient i j : ℚ)) •
        tableAtom (tableIndex i j)
  norm_num

theorem factor_coefficient_identity (i j : Fin 425) :
    (factorData.map fun row ↦
        ((8 : ℚ) / denominator) *
          (fullFactorCoefficient row i : ℚ) *
          (fullFactorCoefficient row j : ℚ)).sum =
      ((8 : ℚ) / denominator) *
        (fullGramCoefficient i j : ℚ) := by
  have intCast_product_sum
      (l : List (List ℤ)) (f g : List ℤ → ℤ) :
      ((l.map fun row ↦ f row * g row).sum : ℚ) =
        (l.map fun row ↦ (f row : ℚ) * (g row : ℚ)).sum := by
    induction l with
    | nil => simp
    | cons row rows ih => simp [ih]
  have hgram :
      (fullGramCoefficient i j : ℚ) =
        (factorData.map fun row ↦
          (fullFactorCoefficient row i : ℚ) *
            (fullFactorCoefficient row j : ℚ)).sum := by
    rw [fullGram_valid]
    exact intCast_product_sum factorData
      (fun row ↦ fullFactorCoefficient row i)
      (fun row ↦ fullFactorCoefficient row j)
  calc
    (factorData.map fun row ↦
        ((8 : ℚ) / denominator) *
          (fullFactorCoefficient row i : ℚ) *
          (fullFactorCoefficient row j : ℚ)).sum =
        (factorData.map fun row ↦
          ((8 : ℚ) / denominator) *
            ((fullFactorCoefficient row i : ℚ) *
              (fullFactorCoefficient row j : ℚ))).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro row hrow
          ring
    _ = ((8 : ℚ) / denominator) *
          (factorData.map fun row ↦
            (fullFactorCoefficient row i : ℚ) *
              (fullFactorCoefficient row j : ℚ)).sum :=
      List.sum_map_mul_left _ _ _
    _ = _ := by rw [← hgram]

set_option maxHeartbeats 0 in

theorem factorSquares_sum_eq_terms :
    (factorSquares.map fun x ↦ x.1 •
      (RationalGroupRing.adjoint x.2 * x.2)).sum =
      (1 / denominator) •
        interpretIntegerTerms tableAtom factorTerms := by
  let coefficient : List ℤ → Fin 425 → ℚ :=
    fun row i ↦ (fullFactorCoefficient row i : ℚ)
  have factorSquares_expansion :
      (factorSquares.map fun x ↦ x.1 •
        (RationalGroupRing.adjoint x.2 * x.2)).sum =
        (factorData.map fun row ↦
          ((8 : ℚ) / denominator) •
            (RationalGroupRing.adjoint
                (RationalGroupRing.basisVector certificateBasis
                  (coefficient row)) *
              RationalGroupRing.basisVector certificateBasis
                (coefficient row))).sum := by
    rw [factorSquares, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro row hrow
    rfl
  rw [factorSquares_expansion]
  calc
    (factorData.map fun row ↦
      ((8 : ℚ) / denominator) •
        (RationalGroupRing.adjoint
            (RationalGroupRing.basisVector certificateBasis
              (coefficient row)) *
          RationalGroupRing.basisVector certificateBasis
            (coefficient row))).sum =
        ∑ i : Fin 425, ∑ j : Fin 425,
          ((factorData.map fun row ↦
            ((8 : ℚ) / denominator) *
              coefficient row i * coefficient row j).sum) •
            MonoidAlgebra.single
              ((certificateBasis i)⁻¹ * certificateBasis j) 1 :=
      by
        simpa only [List.map_map, Function.comp_def] using
          (RationalGroupRing.weightedSquaresList_eq_gram
            certificateBasis ((8 : ℚ) / denominator)
              (factorData.map coefficient))
    _ = ∑ i : Fin 425, ∑ j : Fin 425,
          (((8 : ℚ) / denominator) *
            (fullGramCoefficient i j : ℚ)) •
            MonoidAlgebra.single
              ((certificateBasis i)⁻¹ * certificateBasis j) 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      exact factor_coefficient_identity i j
    _ = (1 / denominator) •
          interpretIntegerTerms tableAtom factorTerms := by
      rw [interpret_factorTerms, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [tableAtom, tableElement_index_product_valid, smul_smul]
      congr 1
      ring

theorem negativeEdgeSquare_eq_terms (edge : Edge) :
    edgeWeight edge •
        (RationalGroupRing.adjoint (negativeEdgeVector edge) *
          negativeEdgeVector edge) =
      (1 / denominator) •
        interpretIntegerTerms tableAtom
          (integerOuterTerms (4 * edge.weightNumerator)
            (negativeEdgeEntries edge)) := by
  simpa [edgeWeight, negativeEdgeVector] using
    sparseSquare_eq_terms
      (4 * (edge.weightNumerator : ℤ))
      (negativeEdgeEntries edge)

theorem negativeEdgeSquares_sum_eq_terms :
    (negativeEdgeSquares.map fun x ↦ x.1 •
      (RationalGroupRing.adjoint x.2 * x.2)).sum =
      (1 / denominator) •
        interpretIntegerTerms tableAtom negativeEdgeTerms := by
  rw [negativeEdgeSquares, negativeEdgeTerms, negativeEdgeTermRow,
    interpretIntegerTerms_flatMap, List.smul_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro edge hedge
  exact negativeEdgeSquare_eq_terms edge

theorem positiveEdgeSquare_eq_terms (edge : Edge) :
    edgeWeight edge •
        (RationalGroupRing.adjoint (positiveEdgeVector edge) *
          positiveEdgeVector edge) =
      (1 / denominator) •
        interpretIntegerTerms tableAtom
          (integerOuterTerms (4 * edge.weightNumerator)
            (positiveEdgeEntries edge)) := by
  simpa [edgeWeight, positiveEdgeVector] using
    sparseSquare_eq_terms
      (4 * (edge.weightNumerator : ℤ))
      (positiveEdgeEntries edge)

private theorem positiveEdgeSquares_sum_eq_terms_aux
    (edges : List Edge) :
    ((edges.filterMap fun edge ↦
        if edge.left = 0 ∨ edge.right = 0 then none
        else some (edgeWeight edge, positiveEdgeVector edge)).map
          fun x ↦ x.1 •
            (RationalGroupRing.adjoint x.2 * x.2)).sum =
      (1 / denominator) •
        interpretIntegerTerms tableAtom
          (edges.flatMap positiveEdgeTermRow) := by
  induction edges with
  | nil => simp [interpretIntegerTerms]
  | cons edge edges ih =>
      by_cases hskip : edge.left = 0 ∨ edge.right = 0
      · simp [positiveEdgeTermRow, hskip, ih]
      · simp only [List.filterMap_cons, hskip, ↓reduceIte,
          List.map_cons, List.sum_cons, List.flatMap_cons,
          positiveEdgeTermRow]
        rw [interpretIntegerTerms_append, smul_add,
          positiveEdgeSquare_eq_terms, ih]

theorem positiveEdgeSquares_sum_eq_terms :
    (positiveEdgeSquares.map fun x ↦ x.1 •
      (RationalGroupRing.adjoint x.2 * x.2)).sum =
      (1 / denominator) •
        interpretIntegerTerms tableAtom positiveEdgeTerms := by
  exact positiveEdgeSquares_sum_eq_terms_aux positiveEdges

theorem diagonalSquare_eq_terms (i : ℕ) (weight : ℤ) :
    ((4 * weight.toNat : ℚ) / denominator) •
        (RationalGroupRing.adjoint
            (sparseVector (diagonalEntries i)) *
          sparseVector (diagonalEntries i)) =
      (1 / denominator) •
        interpretIntegerTerms tableAtom
          (integerOuterTerms (4 * (weight.toNat : ℤ))
            (diagonalEntries i)) := by
  have hcast :
      (4 * weight.toNat : ℚ) =
        (↑(4 * (weight.toNat : ℤ)) : ℚ) := by
    norm_cast
  rw [hcast]
  exact
    sparseSquare_eq_terms (4 * (weight.toNat : ℤ))
      (diagonalEntries i)

set_option maxHeartbeats 0 in

theorem diagonalSquares_sum_eq_terms :
    (diagonalSquares.map fun x ↦ x.1 •
      (RationalGroupRing.adjoint x.2 * x.2)).sum =
      (1 / denominator) •
        interpretIntegerTerms tableAtom diagonalTerms := by
  rw [diagonalSquares, diagonalTerms,
    List.mapIdx_eq_zipIdx_map, List.mapIdx_eq_zipIdx_map]
  rw [interpretIntegerTerms_flatten, List.smul_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro indexedWeight hindexedWeight
  exact diagonalSquare_eq_terms indexedWeight.2 indexedWeight.1

theorem squares_sum_eq_certificateTerms :
    (squares.map fun x ↦ x.1 •
      (RationalGroupRing.adjoint x.2 * x.2)).sum =
      (1 / denominator) •
        interpretIntegerTerms tableAtom certificateTerms := by
  rw [squares, certificateTerms]
  simp only [List.map_append, List.sum_append]
  rw [factorSquares_sum_eq_terms, negativeEdgeSquares_sum_eq_terms,
    positiveEdgeSquares_sum_eq_terms, diagonalSquares_sum_eq_terms]
  simp only [interpretIntegerTerms_append, smul_add]

noncomputable def certificateCustomaryLaplacian : GroupRing :=
  sparseVector customaryLaplacianEntries

theorem tableAtom_identityRow (i : Fin 425) :
    tableAtom (tableIndex (basisIndex 0) i) =
      MonoidAlgebra.single (certificateBasis i) 1 := by
  rw [tableAtom, tableElement_index_product_valid]
  have hzero : certificateBasis (basisIndex 0) = 1 := by
    simpa [certificateBasis, basisIndex] using basisElement_zero
  rw [hzero]
  simp

theorem interpret_targetLinearTerms :
    interpretIntegerTerms tableAtom
        (customaryLaplacianEntries.map fun entry ↦
          { key := tableIndex (basisIndex 0) entry.1
            numerator := -80000000000 * entry.2 }) =
      (-80000000000 : ℚ) • certificateCustomaryLaplacian := by
  rw [interpretIntegerTerms, certificateCustomaryLaplacian,
    sparseVector, RationalGroupRing.sparseBasisVector, List.smul_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro entry hentry
  change
    (↑(-80000000000 * entry.2) : ℚ) •
        tableAtom (tableIndex (basisIndex 0) entry.1) =
      (-80000000000 : ℚ) •
        ((entry.2 : ℚ) •
          MonoidAlgebra.single (certificateBasis entry.1) 1)
  rw [tableAtom_identityRow, smul_smul]
  congr 1
  norm_num

theorem scaled_interpret_targetTerms :
    (1 / denominator) •
        interpretIntegerTerms tableAtom targetTerms =
      (4 : ℚ) •
          (RationalGroupRing.adjoint certificateCustomaryLaplacian *
            certificateCustomaryLaplacian) -
        (1 / 25 : ℚ) • certificateCustomaryLaplacian := by
  rw [targetTerms, interpretIntegerTerms_append, smul_add,
    interpret_targetLinearTerms]
  have houter :=
    sparseSquare_eq_terms (8000000000000 : ℤ)
      customaryLaplacianEntries
  change
    (1 / denominator) •
          interpretIntegerTerms tableAtom
            (integerOuterTerms 8000000000000
              customaryLaplacianEntries) +
        (1 / denominator) •
          ((-80000000000 : ℚ) •
            certificateCustomaryLaplacian) =
      _
  rw [← houter]
  change
    ((8000000000000 : ℚ) / denominator) •
          (RationalGroupRing.adjoint certificateCustomaryLaplacian *
            certificateCustomaryLaplacian) +
        (1 / denominator) •
          ((-80000000000 : ℚ) •
            certificateCustomaryLaplacian) =
      _
  simp only [smul_smul]
  norm_num [sub_eq_add_neg]

theorem generatorAtoms_sum :
    ((List.range 24).map fun i ↦
      MonoidAlgebra.single (basisElement (i + 1)) (1 : ℚ)).sum =
      ∑ g ∈ generators, MonoidAlgebra.single g (1 : ℚ) := by
  have h := congrArg
    (fun l : List IntegralSymplecticCocycleInput.GammaZero ↦
      (l.map fun g ↦ MonoidAlgebra.single g (1 : ℚ)).sum)
    basisElement_generatorList
  have h' :
      ((List.range 24).map fun i ↦
        MonoidAlgebra.single (basisElement (i + 1)) (1 : ℚ)).sum =
        ((generatorData.map gammaZeroOfData).map fun g ↦
          MonoidAlgebra.single g (1 : ℚ)).sum := by
    simpa only [List.map_map, Function.comp_def] using h
  rw [h']
  change
    ((generatorData.map gammaZeroOfData).map fun g ↦
      MonoidAlgebra.single g (1 : ℚ)).sum =
      ∑ g ∈ (generatorData.map gammaZeroOfData).toFinset,
        MonoidAlgebra.single g (1 : ℚ)
  exact (List.sum_toFinset _ generatorList_nodup).symm

private theorem list_sum_neg
    {A : Type*} [AddCommGroup A] (l : List A) :
    (l.map fun x ↦ -x).sum = -l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, add_comm]

theorem certificateCustomaryLaplacian_eq :
    certificateCustomaryLaplacian =
      RationalGroupRing.customaryLaplacian generators := by
  rw [certificateCustomaryLaplacian, sparseVector,
    customaryLaplacianEntries]
  simp only [List.map_cons, List.map_map]
  unfold certificateBasis
  change
    (24 : ℚ) • MonoidAlgebra.single (basisElement 0) 1 +
        ((List.range 24).map fun i ↦
          (-1 : ℚ) •
            MonoidAlgebra.single (basisElement (i + 1)) 1).sum =
      RationalGroupRing.customaryLaplacian generators
  rw [basisElement_zero]
  simp_rw [neg_one_smul]
  have hneg :
      ((List.range 24).map fun i ↦
        -MonoidAlgebra.single (basisElement (i + 1)) (1 : ℚ)).sum =
        -((List.range 24).map fun i ↦
          MonoidAlgebra.single (basisElement (i + 1)) (1 : ℚ)).sum := by
    simpa only [List.map_map, Function.comp_def] using
      list_sum_neg
        ((List.range 24).map fun i ↦
          MonoidAlgebra.single (basisElement (i + 1)) (1 : ℚ))
  rw [hneg, generatorAtoms_sum]
  rw [RationalGroupRing.customaryLaplacian]
  simp only [RationalGroupRing.difference,
    Finset.sum_sub_distrib]
  simp [generators_card, sub_eq_add_neg]

private def constructedGenerators :
    Finset constructedGammaZeroGroup :=
  generators

theorem elementaryGenerators_subset_generators :
    (gammaZeroElementaryGenerators :
      Set constructedGammaZeroGroup) ⊆
        (constructedGenerators :
          Set constructedGammaZeroGroup) := by
  intro x hx
  change x ∈ gammaZeroElementaryGenerators at hx
  simp only [gammaZeroElementaryGenerators] at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
      exact positiveSymplecticGenerators_mem g
        (List.mem_toFinset.mp hg)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact basisTranslations_mem i
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    let y' : IntegralSymplecticCocycleInput.GammaZero := y
    have hy' : y' ∈ generators := by
      rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hy
        exact positiveSymplecticGenerators_mem g
          (List.mem_toFinset.mp hg)
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
        exact basisTranslations_mem i
    have himage : y'⁻¹ ∈ generators.image Inv.inv :=
      Finset.mem_image.mpr ⟨y', hy', rfl⟩
    rw [generators_inverse_closed] at himage
    change y'⁻¹ ∈ generators
    exact himage

theorem generators_generate :
    IsGeneratingSet constructedGammaZeroGroup generators := by
  change IsGeneratingSet constructedGammaZeroGroup constructedGenerators
  have helementary := gammaZeroElementaryGenerators_generate
  unfold IsGeneratingSet at helementary ⊢
  apply top_unique
  calc
    ⊤ = Subgroup.closure
        (gammaZeroElementaryGenerators :
          Set constructedGammaZeroGroup) :=
      helementary.symm
    _ ≤ Subgroup.closure
        (constructedGenerators :
          Set constructedGammaZeroGroup) :=
      Subgroup.closure_mono elementaryGenerators_subset_generators

theorem factorSquares_weights_nonnegative :
    ∀ x ∈ factorSquares, 0 ≤ x.1 := by
  intro x hx
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hx
  norm_num [denominator]

theorem negativeEdgeSquares_weights_nonnegative :
    ∀ x ∈ negativeEdgeSquares, 0 ≤ x.1 := by
  intro x hx
  obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hx
  change 0 ≤ edgeWeight edge
  simp only [edgeWeight]
  positivity

theorem positiveEdgeSquares_weights_nonnegative :
    ∀ x ∈ positiveEdgeSquares, 0 ≤ x.1 := by
  intro x hx
  obtain ⟨edge, hedge, heq⟩ := List.mem_filterMap.mp hx
  by_cases hskip : edge.left = 0 ∨ edge.right = 0
  · simp [hskip] at heq
  · simp only [hskip, ↓reduceIte, Option.some.injEq] at heq
    subst x
    change 0 ≤ edgeWeight edge
    simp only [edgeWeight]
    positivity

set_option maxHeartbeats 0 in

theorem diagonalSquares_weights_nonnegative :
    ∀ x ∈ diagonalSquares, 0 ≤ x.1 := by
  intro x hx
  obtain ⟨i, hi, heq⟩ := List.mem_mapIdx.mp hx
  rw [← heq]
  simp only
  positivity

theorem squares_weights_nonnegative :
    ∀ x ∈ squares, 0 ≤ x.1 := by
  intro x hx
  simp only [squares, List.mem_append] at hx
  rcases hx with ((hx | hx) | hx) | hx
  · exact factorSquares_weights_nonnegative x hx
  · exact negativeEdgeSquares_weights_nonnegative x hx
  · exact positiveEdgeSquares_weights_nonnegative x hx
  · exact diagonalSquares_weights_nonnegative x hx

theorem exactSpectralGapCertificate :
    RationalGroupRing.HasSpectralGapCertificate
      generators (1 / 50) := by
  refine ⟨by norm_num, ?_⟩
  refine ⟨squares, squares_weights_nonnegative, ?_⟩
  have hself :
      RationalGroupRing.adjoint
          (RationalGroupRing.customaryLaplacian generators) =
        RationalGroupRing.customaryLaplacian generators :=
    RationalGroupRing.adjoint_customaryLaplacian
      generators generators_inverse_closed
  have hlaplacian :=
    RationalGroupRing.laplacian_eq_two_smul_customaryLaplacian
      generators generators_inverse_closed
  calc
    RationalGroupRing.laplacian generators *
          RationalGroupRing.laplacian generators -
        (1 / 50 : ℚ) • RationalGroupRing.laplacian generators =
        (4 : ℚ) •
            (RationalGroupRing.adjoint
                (RationalGroupRing.customaryLaplacian generators) *
              RationalGroupRing.customaryLaplacian generators) -
          (1 / 25 : ℚ) •
            RationalGroupRing.customaryLaplacian generators := by
      rw [hlaplacian, hself]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      norm_num
    _ = (1 / denominator) •
          interpretIntegerTerms tableAtom targetTerms := by
      rw [← certificateCustomaryLaplacian_eq]
      exact scaled_interpret_targetTerms.symm
    _ = (1 / denominator) •
          interpretIntegerTerms tableAtom certificateTerms := by
      rw [interpretedCertificate_eq_target]
    _ = (squares.map fun x ↦ x.1 •
          (RationalGroupRing.adjoint x.2 * x.2)).sum :=
      squares_sum_eq_certificateTerms.symm

theorem constructedGammaZero_hasKazhdanPropertyT :
    HasKazhdanPropertyT constructedGammaZeroGroup :=
  hasKazhdanPropertyT_of_spectralGapCertificate
    constructedGammaZeroGroup generators (1 / 50)
      generators_generate exactSpectralGapCertificate

end AffineSymplecticCertificate

end ConnesRigidity


import ConnesRigidity.PropertyTSumOfSquares

namespace ConnesRigidity

universe u v w

variable {G : Type u} [Group G]
variable {ι : Type v}

noncomputable def RationalGroupRing.customaryLaplacian
    (K : Finset G) : RationalGroupRing G :=
  ∑ g ∈ K, RationalGroupRing.difference g

theorem RationalGroupRing.laplacian_eq_two_smul_customaryLaplacian
    [DecidableEq G] (K : Finset G) (hinv : K.image Inv.inv = K) :
    RationalGroupRing.laplacian K =
      (2 : ℚ) • RationalGroupRing.customaryLaplacian K := by
  classical
  have hinverseSum :
      (∑ g ∈ K, MonoidAlgebra.single g⁻¹ (1 : ℚ)) =
        ∑ g ∈ K, MonoidAlgebra.single g (1 : ℚ) := by
    calc
      (∑ g ∈ K, MonoidAlgebra.single g⁻¹ (1 : ℚ)) =
          ∑ g ∈ K.image Inv.inv,
            MonoidAlgebra.single g (1 : ℚ) := by
              rw [Finset.sum_image]
              intro x _ y _ hxy
              simpa using congrArg Inv.inv hxy
      _ = ∑ g ∈ K, MonoidAlgebra.single g (1 : ℚ) := by
        rw [hinv]
  simp only [RationalGroupRing.laplacian,
    RationalGroupRing.customaryLaplacian,
    RationalGroupRing.difference, RationalGroupRing.adjoint_sub,
    RationalGroupRing.adjoint_single, inv_one]
  have hterm (g : G) :
      (MonoidAlgebra.single (1 : G) (1 : ℚ) -
          MonoidAlgebra.single g⁻¹ (1 : ℚ)) *
          (MonoidAlgebra.single (1 : G) (1 : ℚ) -
            MonoidAlgebra.single g (1 : ℚ)) =
        (2 : ℚ) • MonoidAlgebra.single (1 : G) (1 : ℚ) -
          MonoidAlgebra.single g (1 : ℚ) -
          MonoidAlgebra.single g⁻¹ (1 : ℚ) := by
    rw [sub_mul, mul_sub, mul_sub,
      MonoidAlgebra.single_mul_single,
      MonoidAlgebra.single_mul_single,
      MonoidAlgebra.single_mul_single,
      MonoidAlgebra.single_mul_single]
    simp only [mul_one, one_mul, inv_mul_cancel,
      MonoidAlgebra.smul_single, smul_eq_mul]
    have htwo :
        MonoidAlgebra.single (1 : G) (2 : ℚ) =
          MonoidAlgebra.single (1 : G) (1 : ℚ) +
            MonoidAlgebra.single (1 : G) (1 : ℚ) := by
      rw [← MonoidAlgebra.single_add]
      norm_num
    rw [htwo]
    abel
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    hinverseSum]
  rw [Finset.smul_sum]
  simp_rw [smul_sub, two_smul]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib]
  abel

noncomputable def RationalGroupRing.basisVector
    [Fintype ι] (basis : ι → G) (coefficient : ι → ℚ) :
    RationalGroupRing G :=
  ∑ i, coefficient i • MonoidAlgebra.single (basis i) 1

theorem RationalGroupRing.adjoint_finset_sum
    (s : Finset ι) (f : ι → RationalGroupRing G) :
    RationalGroupRing.adjoint (∑ i ∈ s, f i) =
      ∑ i ∈ s, RationalGroupRing.adjoint (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [hi, ih]

theorem RationalGroupRing.adjoint_sum
    [Fintype ι]
    (f : ι → RationalGroupRing G) :
    RationalGroupRing.adjoint (∑ i, f i) =
      ∑ i, RationalGroupRing.adjoint (f i) := by
  classical
  simpa only [Finset.sum_filter] using
    RationalGroupRing.adjoint_finset_sum
      (G := G) (Finset.univ : Finset ι) f

theorem RationalGroupRing.adjoint_customaryLaplacian
    [DecidableEq G] (K : Finset G) (hinv : K.image Inv.inv = K) :
    RationalGroupRing.adjoint
        (RationalGroupRing.customaryLaplacian K) =
      RationalGroupRing.customaryLaplacian K := by
  classical
  rw [RationalGroupRing.customaryLaplacian,
    RationalGroupRing.adjoint_finset_sum]
  simp only [RationalGroupRing.difference,
    RationalGroupRing.adjoint_sub,
    RationalGroupRing.adjoint_single, inv_one]
  calc
    (∑ x ∈ K,
        (MonoidAlgebra.single (1 : G) (1 : ℚ) -
          MonoidAlgebra.single x⁻¹ (1 : ℚ))) =
        ∑ x ∈ K.image Inv.inv,
          (MonoidAlgebra.single (1 : G) (1 : ℚ) -
            MonoidAlgebra.single x (1 : ℚ)) := by
      rw [Finset.sum_image]
      intro x _ y _ hxy
      simpa using congrArg Inv.inv hxy
    _ = ∑ x ∈ K,
          (MonoidAlgebra.single (1 : G) (1 : ℚ) -
            MonoidAlgebra.single x (1 : ℚ)) := by
      rw [hinv]

theorem RationalGroupRing.adjoint_basisVector
    [Fintype ι]
    (basis : ι → G) (coefficient : ι → ℚ) :
    RationalGroupRing.adjoint
        (RationalGroupRing.basisVector basis coefficient) =
      ∑ i, coefficient i •
        MonoidAlgebra.single (basis i)⁻¹ 1 := by
  classical
  rw [RationalGroupRing.basisVector,
    RationalGroupRing.adjoint_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem RationalGroupRing.adjoint_basisVector_mul_basisVector
    [Fintype ι]
    (basis : ι → G) (coefficient : ι → ℚ) :
    RationalGroupRing.adjoint
          (RationalGroupRing.basisVector basis coefficient) *
        RationalGroupRing.basisVector basis coefficient =
      ∑ i, ∑ j, (coefficient i * coefficient j) •
        MonoidAlgebra.single ((basis i)⁻¹ * basis j) 1 := by
  classical
  rw [RationalGroupRing.adjoint_basisVector,
    RationalGroupRing.basisVector, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_mul_assoc, mul_smul_comm,
    MonoidAlgebra.single_mul_single]
  simp [mul_smul]

noncomputable def RationalGroupRing.sparseBasisVector
    (basis : ι → G) (entries : List (ι × ℚ)) :
    RationalGroupRing G :=
  (entries.map fun entry ↦
    entry.2 • MonoidAlgebra.single (basis entry.1) 1).sum

private theorem list_sum_mul
    {A : Type*} [NonUnitalNonAssocSemiring A]
    (entries : List A) (right : A) :
    entries.sum * right = (entries.map fun left ↦ left * right).sum := by
  induction entries with
  | nil => simp
  | cons left entries ih => simp [ih, add_mul]

private theorem mul_list_sum
    {A : Type*} [NonUnitalNonAssocSemiring A]
    (left : A) (entries : List A) :
    left * entries.sum = (entries.map fun right ↦ left * right).sum := by
  induction entries with
  | nil => simp
  | cons right entries ih => simp [ih, mul_add]

private theorem list_sum_flatMap
    {A B : Type*} [AddCommMonoid B]
    (entries : List A) (f : A → List B) :
    (entries.flatMap f).sum =
      (entries.map fun entry ↦ (f entry).sum).sum := by
  induction entries with
  | nil => simp
  | cons entry entries ih => simp [ih]

private theorem RationalGroupRing.adjoint_list_sum
    (entries : List (RationalGroupRing G)) :
    RationalGroupRing.adjoint entries.sum =
      (entries.map RationalGroupRing.adjoint).sum := by
  induction entries with
  | nil => simp
  | cons entry entries ih => simp [ih]

private theorem RationalGroupRing.adjoint_sparseBasisVector
    (basis : ι → G) (entries : List (ι × ℚ)) :
    RationalGroupRing.adjoint
        (RationalGroupRing.sparseBasisVector basis entries) =
      (entries.map fun entry ↦
        entry.2 • MonoidAlgebra.single (basis entry.1)⁻¹ 1).sum := by
  rw [RationalGroupRing.sparseBasisVector,
    RationalGroupRing.adjoint_list_sum]
  apply congrArg List.sum
  rw [List.map_map]
  apply List.map_congr_left
  intro entry hentry
  change RationalGroupRing.adjoint
      (entry.2 • MonoidAlgebra.single (basis entry.1) 1) =
    entry.2 • MonoidAlgebra.single (basis entry.1)⁻¹ 1
  simp

theorem RationalGroupRing.adjoint_sparseBasisVector_mul_sparseBasisVector
    (basis : ι → G) (entries : List (ι × ℚ)) :
    RationalGroupRing.adjoint
          (RationalGroupRing.sparseBasisVector basis entries) *
        RationalGroupRing.sparseBasisVector basis entries =
      (entries.flatMap fun left ↦
        entries.map fun right ↦
          (left.2 * right.2) •
            MonoidAlgebra.single
              ((basis left.1)⁻¹ * basis right.1) 1).sum := by
  classical
  rw [RationalGroupRing.adjoint_sparseBasisVector,
    list_sum_mul, list_sum_flatMap]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro left hleft
  change
    (left.2 • MonoidAlgebra.single (basis left.1)⁻¹ 1) *
        RationalGroupRing.sparseBasisVector basis entries =
      _
  rw [RationalGroupRing.sparseBasisVector, mul_list_sum]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro right hright
  change
    (left.2 • MonoidAlgebra.single (basis left.1)⁻¹ 1) *
        (right.2 • MonoidAlgebra.single (basis right.1) 1) =
      _
  rw [smul_mul_assoc, mul_smul_comm,
    MonoidAlgebra.single_mul_single]
  simp [mul_smul]

theorem RationalGroupRing.weightedSquaresList_eq_gram
    [Fintype ι]
    (basis : ι → G) (weight : ℚ)
    (coefficients : List (ι → ℚ)) :
    (coefficients.map fun coefficient ↦
      weight •
        (RationalGroupRing.adjoint
            (RationalGroupRing.basisVector basis coefficient) *
          RationalGroupRing.basisVector basis coefficient)).sum =
      ∑ i, ∑ j,
        ((coefficients.map fun coefficient ↦
          weight * coefficient i * coefficient j).sum) •
            MonoidAlgebra.single ((basis i)⁻¹ * basis j) 1 := by
  classical
  induction coefficients with
  | nil => simp
  | cons coefficient coefficients ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [RationalGroupRing.adjoint_basisVector_mul_basisVector, ih]
      simp_rw [Finset.smul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [add_smul]
      rw [smul_smul]
      congr 1
      ring_nf

variable {ρ : Type w}

def RationalGroupRing.gramEntry
    [Fintype ρ]
    (weight : ρ → ℚ) (coefficient : ρ → ι → ℚ)
    (i j : ι) : ℚ :=
  ∑ r, weight r * coefficient r i * coefficient r j

theorem RationalGroupRing.weightedSquares_eq_gram
    [Fintype ι] [Fintype ρ]
    (basis : ι → G) (weight : ρ → ℚ)
    (coefficient : ρ → ι → ℚ) :
    ∑ r, weight r •
        (RationalGroupRing.adjoint
            (RationalGroupRing.basisVector basis (coefficient r)) *
          RationalGroupRing.basisVector basis (coefficient r)) =
      ∑ i, ∑ j,
        RationalGroupRing.gramEntry weight coefficient i j •
          MonoidAlgebra.single ((basis i)⁻¹ * basis j) 1 := by
  classical
  simp_rw [RationalGroupRing.adjoint_basisVector_mul_basisVector,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [RationalGroupRing.gramEntry]
  simp_rw [smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem RationalGroupRing.gramExpansion_eq_of_product_table
    [Fintype ι]
    (basis : ι → G) (elements : ℕ → G) (productIndex : ι → ι → ℕ)
    (hproduct : ∀ i j, elements (productIndex i j) =
      (basis i)⁻¹ * basis j)
    (gram : ι → ι → ℚ) :
    (∑ i, ∑ j, gram i j •
        MonoidAlgebra.single ((basis i)⁻¹ * basis j) 1 :
      RationalGroupRing G) =
      ∑ i, ∑ j, gram i j •
        MonoidAlgebra.single (elements (productIndex i j)) 1 := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hproduct]

def RationalGroupRing.aggregateGramCoefficient
    [Fintype ι] {N : ℕ} (productIndex : ι → ι → Fin N)
    (gram : ι → ι → ℚ) (k : Fin N) : ℚ :=
  ∑ i, ∑ j, if productIndex i j = k then gram i j else 0

theorem RationalGroupRing.gramExpansion_eq_aggregate
    [Fintype ι] {N : ℕ} (elements : Fin N → G)
    (productIndex : ι → ι → Fin N) (gram : ι → ι → ℚ) :
    (∑ i, ∑ j, gram i j •
        MonoidAlgebra.single (elements (productIndex i j)) 1 :
      RationalGroupRing G) =
      ∑ k, RationalGroupRing.aggregateGramCoefficient
          productIndex gram k • MonoidAlgebra.single (elements k) 1 := by
  classical
  simp_rw [RationalGroupRing.aggregateGramCoefficient,
    Finset.sum_smul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (productIndex i j)]
  · simp
  · intro k _ hk
    simp [hk.symm]
  · simp

theorem RationalGroupRing.gramExpansions_eq_of_aggregate_eq
    [Fintype ι] {N : ℕ} (elements : Fin N → G)
    (productIndex : ι → ι → Fin N)
    (left right : ι → ι → ℚ)
    (hcoeff : ∀ k, RationalGroupRing.aggregateGramCoefficient
        productIndex left k =
      RationalGroupRing.aggregateGramCoefficient productIndex right k) :
    (∑ i, ∑ j, left i j •
        MonoidAlgebra.single (elements (productIndex i j)) 1 :
      RationalGroupRing G) =
      ∑ i, ∑ j, right i j •
        MonoidAlgebra.single (elements (productIndex i j)) 1 := by
  rw [RationalGroupRing.gramExpansion_eq_aggregate,
    RationalGroupRing.gramExpansion_eq_aggregate]
  apply Finset.sum_congr rfl
  intro k _
  rw [hcoeff k]

structure IntegerTableTerm (N : ℕ) where
  key : Fin N
  numerator : ℤ
deriving DecidableEq

def integerOuterTerms
    {N : ℕ} (productIndex : ι → ι → Fin N)
    (weight : ℤ) (entries : List (ι × ℤ)) :
    List (IntegerTableTerm N) :=
  entries.flatMap fun left ↦
    entries.map fun right ↦
      { key := productIndex left.1 right.1
        numerator := weight * left.2 * right.2 }

noncomputable def interpretIntegerTerms
    {N : ℕ} {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (atom : Fin N → M) (terms : List (IntegerTableTerm N)) : M :=
  (terms.map fun term ↦ (term.numerator : ℚ) • atom term.key).sum

theorem interpretIntegerOuterTerms
    {N : ℕ} {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (atom : Fin N → M) (productIndex : ι → ι → Fin N)
    (weight : ℤ) (entries : List (ι × ℤ)) :
    interpretIntegerTerms atom
        (integerOuterTerms productIndex weight entries) =
      (entries.map fun left ↦
        (entries.map fun right ↦
          ((weight : ℚ) * left.2 * right.2) •
            atom (productIndex left.1 right.1)).sum).sum := by
  rw [interpretIntegerTerms, integerOuterTerms,
    List.map_flatMap, list_sum_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro left hleft
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro right hright
  change
    ((↑(weight * left.2 * right.2) : ℚ) •
        atom (productIndex left.1 right.1)) =
      ((weight : ℚ) * left.2 * right.2) •
        atom (productIndex left.1 right.1)
  simp only [Int.cast_mul]

theorem weightedSparseSquare_eq_interpretIntegerTerms
    {N : ℕ} (basis : ι → G) (elements : Fin N → G)
    (productIndex : ι → ι → Fin N)
    (hproduct : ∀ i j, elements (productIndex i j) =
      (basis i)⁻¹ * basis j)
    (denominator : ℚ) (weight : ℤ) (entries : List (ι × ℤ)) :
    ((weight : ℚ) / denominator) •
        (RationalGroupRing.adjoint
            (RationalGroupRing.sparseBasisVector basis
              (entries.map fun entry ↦ (entry.1, (entry.2 : ℚ)))) *
          RationalGroupRing.sparseBasisVector basis
            (entries.map fun entry ↦ (entry.1, (entry.2 : ℚ)))) =
      (1 / denominator) •
        interpretIntegerTerms
          (fun k ↦ MonoidAlgebra.single (elements k) 1)
          (integerOuterTerms productIndex weight entries) := by
  classical
  rw [RationalGroupRing.adjoint_sparseBasisVector_mul_sparseBasisVector,
    interpretIntegerOuterTerms]
  simp only [List.flatMap_map, List.map_map]
  rw [list_sum_flatMap]
  simp_rw [List.smul_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro left hleft
  change
    ((weight : ℚ) / denominator) •
        (entries.map fun right ↦
          (((left.2 : ℚ) * right.2) •
            MonoidAlgebra.single
              ((basis left.1)⁻¹ * basis right.1) 1)).sum =
      (1 / denominator) •
        (entries.map fun right ↦
          (((weight : ℚ) * left.2 * right.2) •
            MonoidAlgebra.single
              (elements (productIndex left.1 right.1)) 1)).sum
  rw [List.smul_sum, List.smul_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro right hright
  change
    ((weight : ℚ) / denominator) •
        (((left.2 : ℚ) * right.2) •
          MonoidAlgebra.single
            ((basis left.1)⁻¹ * basis right.1) 1) =
      (1 / denominator) •
        (((weight : ℚ) * left.2 * right.2) •
          MonoidAlgebra.single
            (elements (productIndex left.1 right.1)) 1)
  rw [hproduct]
  simp only [smul_smul]
  congr 1
  ring

def collapseIntegerTerms {N : ℕ} :
    List (IntegerTableTerm N) → List (IntegerTableTerm N)
  | [] => []
  | term :: terms =>
      match collapseIntegerTerms terms with
      | [] => if term.numerator = 0 then [] else [term]
      | next :: rest =>
          if term.key = next.key then
            let numerator := term.numerator + next.numerator
            if numerator = 0 then rest
            else { key := term.key, numerator := numerator } :: rest
          else if term.numerator = 0 then next :: rest
          else term :: next :: rest

theorem interpretIntegerTerms_collapse
    {N : ℕ} {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (atom : Fin N → M) (terms : List (IntegerTableTerm N)) :
    interpretIntegerTerms atom (collapseIntegerTerms terms) =
      interpretIntegerTerms atom terms := by
  induction terms with
  | nil => simp [collapseIntegerTerms, interpretIntegerTerms]
  | cons term terms ih =>
      simp only [collapseIntegerTerms]
      split
      next hcollapsed =>
        change _ =
          (term.numerator : ℚ) • atom term.key +
            interpretIntegerTerms atom terms
        rw [← ih, hcollapsed]
        split <;> rename_i hzero <;>
          simp [interpretIntegerTerms, hzero]
      next next rest hcollapsed =>
        change _ =
          (term.numerator : ℚ) • atom term.key +
            interpretIntegerTerms atom terms
        rw [← ih, hcollapsed]
        split <;> rename_i hkey
        · rw [hkey]
          split <;> rename_i hsum
          · have hsumQ :
                (term.numerator : ℚ) + next.numerator = 0 := by
              exact_mod_cast hsum
            simp only [interpretIntegerTerms, List.map_cons, List.sum_cons]
            rw [← add_assoc, ← add_smul, hsumQ, zero_smul, zero_add]
          · simp only [interpretIntegerTerms, List.map_cons, List.sum_cons]
            simp only [Int.cast_add, add_smul]
            abel
        · split <;> rename_i hzero
          · have hzeroQ : (term.numerator : ℚ) = 0 := by
              exact_mod_cast hzero
            simp only [interpretIntegerTerms, List.map_cons, List.sum_cons]
            rw [hzeroQ, zero_smul, zero_add]
          · simp only [interpretIntegerTerms, List.map_cons, List.sum_cons]

def normalizeIntegerTerms {N : ℕ}
    (terms : List (IntegerTableTerm N)) : List (IntegerTableTerm N) :=
  collapseIntegerTerms
    (terms.mergeSort fun left right ↦
      decide (left.key.val ≤ right.key.val))

theorem interpretIntegerTerms_normalize
    {N : ℕ} {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (atom : Fin N → M) (terms : List (IntegerTableTerm N)) :
    interpretIntegerTerms atom (normalizeIntegerTerms terms) =
      interpretIntegerTerms atom terms := by
  rw [normalizeIntegerTerms, interpretIntegerTerms_collapse]
  exact
    (List.Perm.sum_eq
      ((List.mergeSort_perm terms fun left right ↦
        decide (left.key.val ≤ right.key.val)).map
          (fun term ↦ (term.numerator : ℚ) • atom term.key)))

theorem interpretIntegerTerms_eq_of_normalize_eq
    {N : ℕ} {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (atom : Fin N → M) {left right : List (IntegerTableTerm N)}
    (h : normalizeIntegerTerms left = normalizeIntegerTerms right) :
    interpretIntegerTerms atom left = interpretIntegerTerms atom right := by
  rw [← interpretIntegerTerms_normalize atom left,
    ← interpretIntegerTerms_normalize atom right, h]

end ConnesRigidity




import ConnesRigidity.GroupRingCertificateAlgebra









namespace ConnesRigidity

namespace SDDCertificate

open scoped BigOperators

universe u v

variable {ι : Type u} [Fintype ι] [LinearOrder ι]


abbrev Pair (ι : Type u) [Fintype ι] [LinearOrder ι] :=
  {pair : ι × ι // pair.1 < pair.2}


def incidentMass (matrix : Matrix ι ι ℚ) (i : ι) : ℚ :=
  ∑ pair : Pair ι,
    if i = pair.1.1 ∨ i = pair.1.2
    then |matrix pair.1.1 pair.1.2|
    else 0



def offDiagonalMass (matrix : Matrix ι ι ℚ) (i : ι) : ℚ :=
  ∑ j, if j = i then 0 else |matrix i j|

private def pairForOther (i : ι) (j : {j : ι // j ≠ i}) :
    {pair : Pair ι // i = pair.1.1 ∨ i = pair.1.2} :=
  if h : i < j.1 then
    ⟨⟨(i, j.1), h⟩, Or.inl rfl⟩
  else
    ⟨⟨(j.1, i), lt_of_le_of_ne (le_of_not_gt h) j.2⟩, Or.inr rfl⟩

private def otherEndpoint (i : ι)
    (pair : {pair : Pair ι // i = pair.1.1 ∨ i = pair.1.2}) :
    {j : ι // j ≠ i} :=
  if h : i = pair.1.1.1 then
    ⟨pair.1.1.2, by
      intro hj
      exact pair.1.2.ne (h.symm.trans hj.symm)⟩
  else
    ⟨pair.1.1.1, by
      intro hj
      exact h hj.symm⟩

private def incidentPairEquiv (i : ι) :
    {j : ι // j ≠ i} ≃
      {pair : Pair ι // i = pair.1.1 ∨ i = pair.1.2} where
  toFun := pairForOther i
  invFun := otherEndpoint i
  left_inv j := by
    apply Subtype.ext
    by_cases h : i < j.1
    · simp [pairForOther, otherEndpoint, h]
    · have hne : i ≠ j.1 := Ne.symm j.2
      simp [pairForOther, otherEndpoint, h, hne]
  right_inv pair := by
    rcases pair with ⟨⟨⟨a, b⟩, hab⟩, hi⟩
    apply Subtype.ext
    apply Subtype.ext
    rcases hi with hia | hib
    · subst i
      simp [pairForOther, otherEndpoint, hab]
    · subst i
      simp [pairForOther, otherEndpoint, hab.ne',
        not_lt_of_ge hab.le]

private theorem sum_ite_eq_sum_subtype
    {α β : Type*} [Fintype α] [AddCommMonoid β]
    (p : α → Prop) [DecidablePred p] (f : α → β) :
    (∑ x, if p x then f x else 0) =
      ∑ x : {x : α // p x}, f x.1 := by
  rw [← Finset.sum_subtype
    (Finset.univ.filter p) (by simp)]
  exact (Finset.sum_filter p f).symm




theorem incidentMass_eq_offDiagonalMass
    (matrix : Matrix ι ι ℚ) (hsymm : matrix.IsSymm) (i : ι) :
    incidentMass matrix i = offDiagonalMass matrix i := by
  classical
  unfold incidentMass offDiagonalMass
  calc
    (∑ pair : Pair ι,
        if i = pair.1.1 ∨ i = pair.1.2
        then |matrix pair.1.1 pair.1.2|
        else 0) =
        ∑ pair :
            {pair : Pair ι // i = pair.1.1 ∨ i = pair.1.2},
          |matrix pair.1.1.1 pair.1.1.2| := by
      exact sum_ite_eq_sum_subtype
        (fun pair : Pair ι =>
          i = pair.1.1 ∨ i = pair.1.2)
        (fun pair : Pair ι => |matrix pair.1.1 pair.1.2|)
    _ = ∑ j : {j : ι // j ≠ i}, |matrix i j.1| := by
      symm
      apply Fintype.sum_equiv (incidentPairEquiv i)
      intro j
      by_cases h : i < j.1
      · simp [incidentPairEquiv, pairForOther, h]
      · simp only [incidentPairEquiv, pairForOther, h, ↓reduceDIte,
          Equiv.coe_fn_mk]
        rw [hsymm.apply i j.1]
    _ = ∑ j, if j = i then 0 else |matrix i j| := by
      rw [← sum_ite_eq_sum_subtype
        (fun j : ι => j ≠ i)
        (fun j : ι => |matrix i j|)]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = i <;> simp [h]



def slack (matrix : Matrix ι ι ℚ) (i : ι) : ℚ :=
  matrix i i - incidentMass matrix i


def diagonalCoefficient (i : ι) : ι → ℚ :=
  fun k ↦ if k = i then 1 else 0



def pairCoefficient (matrix : Matrix ι ι ℚ) (i j : ι) : ι → ℚ :=
  fun k ↦
    if k = i then 1
    else if k = j then if 0 ≤ matrix i j then 1 else -1
    else 0



abbrev Row (ι : Type u) [Fintype ι] [LinearOrder ι] :=
  Sum ι (Pair ι)


def rowWeight (matrix : Matrix ι ι ℚ) : Row ι → ℚ
  | Sum.inl i => slack matrix i
  | Sum.inr pair => |matrix pair.1.1 pair.1.2|


def rowCoefficient (matrix : Matrix ι ι ℚ) : Row ι → ι → ℚ
  | Sum.inl i => diagonalCoefficient i
  | Sum.inr pair => pairCoefficient matrix pair.1.1 pair.1.2

private theorem abs_mul_sign (r : ℚ) :
    |r| * (if 0 ≤ r then 1 else -1) = r := by
  by_cases h : 0 ≤ r
  · simp [h, abs_of_nonneg h]
  · have hr : r ≤ 0 := le_of_not_ge h
    simp [h, abs_of_nonpos hr]

private theorem pairContribution_diagonal
    (matrix : Matrix ι ι ℚ) (pair : Pair ι) (k : ι) :
    |matrix pair.1.1 pair.1.2| *
        pairCoefficient matrix pair.1.1 pair.1.2 k *
          pairCoefficient matrix pair.1.1 pair.1.2 k =
      if k = pair.1.1 ∨ k = pair.1.2
      then |matrix pair.1.1 pair.1.2|
      else 0 := by
  rcases pair with ⟨⟨i, j⟩, hij⟩
  by_cases hki : k = i
  · subst k
    simp [pairCoefficient, hij.ne]
  · by_cases hkj : k = j
    · subst k
      simp only [pairCoefficient, hki, ↓reduceIte]
      split <;> norm_num
    · simp [pairCoefficient, hki, hkj]

private theorem pairContribution_offDiagonal
    (matrix : Matrix ι ι ℚ) (hsymm : matrix.IsSymm)
    (pair : Pair ι) (i j : ι) (hij : i ≠ j) :
    |matrix pair.1.1 pair.1.2| *
        pairCoefficient matrix pair.1.1 pair.1.2 i *
          pairCoefficient matrix pair.1.1 pair.1.2 j =
      if i = pair.1.1 ∧ j = pair.1.2 then matrix i j
      else if i = pair.1.2 ∧ j = pair.1.1 then matrix i j
      else 0 := by
  rcases pair with ⟨⟨a, b⟩, hab⟩
  by_cases hia : i = a
  · subst i
    by_cases hjb : j = b
    · subst j
      simp only [pairCoefficient, hab.ne', ↓reduceIte, true_and]
      simpa only [mul_one] using abs_mul_sign (matrix a b)
    · have hja : j ≠ a := by
        intro h
        apply hij
        exact h.symm
      simp [pairCoefficient, hab.ne, hjb, hja]
  · by_cases hib : i = b
    · subst i
      by_cases hja : j = a
      · subst j
        have hba : b ≠ a := hab.ne'
        have hsymm' : matrix b a = matrix a b := hsymm.apply a b
        simp only [pairCoefficient, hba, ↓reduceIte, mul_one, and_self]
        rw [hsymm']
        exact abs_mul_sign (matrix a b)
      · have hjb : j ≠ b := by
          intro h
          apply hij
          exact h.symm
        simp [pairCoefficient, hia, hja, hjb]
    · simp [pairCoefficient, hia, hib]

private theorem gramEntry_expand (matrix : Matrix ι ι ℚ)
    (hsymm : matrix.IsSymm) (i j : ι) :
    RationalGroupRing.gramEntry (rowWeight matrix) (rowCoefficient matrix) i j =
      matrix i j := by
  classical
  simp only [RationalGroupRing.gramEntry, rowWeight, rowCoefficient,
    Fintype.sum_sum_type, diagonalCoefficient, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  by_cases hij : i = j
  · subst j
    simp_rw [pairContribution_diagonal]
    simp [slack, incidentMass]
  · simp_rw [pairContribution_offDiagonal matrix hsymm _ i j hij]
    simp only [hij, ↓reduceIte, zero_add]
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · let pair : Pair ι := ⟨(i, j), hijlt⟩
      rw [Finset.sum_eq_single pair]
      · simp [pair]
      · intro other _ hne
        have hforward : ¬(i = other.1.1 ∧ j = other.1.2) := by
          intro h
          apply hne
          apply Subtype.ext
          exact Prod.ext h.1.symm h.2.symm
        have hreverse : ¬(i = other.1.2 ∧ j = other.1.1) := by
          intro h
          have hji : j < i := by
            rw [h.2, h.1]
            exact other.2
          exact (not_lt_of_ge hijlt.le) hji
        simp [hforward, hreverse]
      · simp
    · let pair : Pair ι := ⟨(j, i), hjilt⟩
      rw [Finset.sum_eq_single pair]
      · simp [pair, hij]
      · intro other _ hne
        have hforward : ¬(i = other.1.1 ∧ j = other.1.2) := by
          intro h
          have hij' : i < j := by
            rw [h.1, h.2]
            exact other.2
          exact (not_lt_of_ge hjilt.le) hij'
        have hreverse : ¬(i = other.1.2 ∧ j = other.1.1) := by
          intro h
          apply hne
          apply Subtype.ext
          exact Prod.ext h.2.symm h.1.symm
        simp [hforward, hreverse]
      · simp



def IsDiagonallyDominant (matrix : Matrix ι ι ℚ) : Prop :=
  ∀ i, offDiagonalMass matrix i ≤ matrix i i

theorem slack_nonnegative {matrix : Matrix ι ι ℚ}
    (hsymm : matrix.IsSymm) (hdominant : IsDiagonallyDominant matrix)
    (i : ι) : 0 ≤ slack matrix i := by
  rw [slack, incidentMass_eq_offDiagonalMass matrix hsymm i]
  exact sub_nonneg.mpr (hdominant i)

theorem rowWeight_nonnegative {matrix : Matrix ι ι ℚ}
    (hsymm : matrix.IsSymm) (hdominant : IsDiagonallyDominant matrix)
    (row : Row ι) : 0 ≤ rowWeight matrix row := by
  cases row with
  | inl i => exact slack_nonnegative hsymm hdominant i
  | inr pair => exact abs_nonneg _

private theorem sum_map_toList
    {α M : Type*} [AddCommMonoid M] (s : Finset α) (f : α → M) :
    (s.toList.map f).sum = ∑ x ∈ s, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih => simp [hx]




noncomputable def atomVector
    {G : Type v} [Group G] (atom : ι → RationalGroupRing G)
    (coefficient : ι → ℚ) : RationalGroupRing G :=
  ∑ i, coefficient i • atom i

omit [LinearOrder ι] in
private theorem adjoint_atomVector
    {G : Type v} [Group G] (atom : ι → RationalGroupRing G)
    (coefficient : ι → ℚ) :
    RationalGroupRing.adjoint (atomVector atom coefficient) =
      ∑ i, coefficient i • RationalGroupRing.adjoint (atom i) := by
  classical
  rw [atomVector, RationalGroupRing.adjoint_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp

omit [LinearOrder ι] in
private theorem adjoint_atomVector_mul_atomVector
    {G : Type v} [Group G] (atom : ι → RationalGroupRing G)
    (coefficient : ι → ℚ) :
    RationalGroupRing.adjoint (atomVector atom coefficient) *
        atomVector atom coefficient =
      ∑ i, ∑ j, (coefficient i * coefficient j) •
        (RationalGroupRing.adjoint (atom i) * atom j) := by
  classical
  rw [adjoint_atomVector, atomVector, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_mul_assoc, mul_smul_comm]
  simp [mul_smul]

omit [LinearOrder ι] in
private theorem weightedAtomSquares_eq_gram
    {G : Type v} [Group G] {ρ : Type*} [Fintype ρ]
    (atom : ι → RationalGroupRing G) (weight : ρ → ℚ)
    (coefficient : ρ → ι → ℚ) :
    ∑ row, weight row •
        (RationalGroupRing.adjoint
            (atomVector atom (coefficient row)) *
          atomVector atom (coefficient row)) =
      ∑ i, ∑ j,
        RationalGroupRing.gramEntry weight coefficient i j •
          (RationalGroupRing.adjoint (atom i) * atom j) := by
  classical
  simp_rw [adjoint_atomVector_mul_atomVector, Finset.smul_sum]
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
  intro row _
  ring




theorem weightedAtomSquares_eq_matrixExpansion
    {G : Type v} [Group G] (atom : ι → RationalGroupRing G)
    (matrix : Matrix ι ι ℚ) (hsymm : matrix.IsSymm) :
    (∑ row : Row ι,
        rowWeight matrix row •
          (RationalGroupRing.adjoint
              (atomVector atom (rowCoefficient matrix row)) *
            atomVector atom (rowCoefficient matrix row))) =
      ∑ i, ∑ j, matrix i j •
        (RationalGroupRing.adjoint (atom i) * atom j) := by
  rw [weightedAtomSquares_eq_gram]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [gramEntry_expand matrix hsymm i j]





theorem weightedSquares_eq_matrixExpansion
    {G : Type v} [Group G] (basis : ι → G)
    (matrix : Matrix ι ι ℚ) (hsymm : matrix.IsSymm) :
    (∑ row : Row ι,
        rowWeight matrix row •
          (RationalGroupRing.adjoint
              (RationalGroupRing.basisVector basis
                (rowCoefficient matrix row)) *
            RationalGroupRing.basisVector basis
              (rowCoefficient matrix row))) =
      ∑ i, ∑ j, matrix i j •
        MonoidAlgebra.single ((basis i)⁻¹ * basis j) 1 := by
  rw [RationalGroupRing.weightedSquares_eq_gram]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [gramEntry_expand matrix hsymm i j]



noncomputable def atomSquareList
    {G : Type v} [Group G] (atom : ι → RationalGroupRing G)
    (matrix : Matrix ι ι ℚ) :
    List (ℚ × RationalGroupRing G) :=
  Finset.univ.toList.map fun row : Row ι ↦
    (rowWeight matrix row,
      atomVector atom (rowCoefficient matrix row))



theorem matrixAtomExpansion_isPositiveSumOfSquares
    {G : Type v} [Group G] (atom : ι → RationalGroupRing G)
    (matrix : Matrix ι ι ℚ) (hsymm : matrix.IsSymm)
    (hdominant : IsDiagonallyDominant matrix) :
    RationalGroupRing.IsPositiveSumOfSquares
      (∑ i, ∑ j, matrix i j •
        (RationalGroupRing.adjoint (atom i) * atom j)) := by
  classical
  refine ⟨atomSquareList atom matrix, ?_, ?_⟩
  · intro square hsquare
    simp only [atomSquareList, List.mem_map, Finset.mem_toList,
      Finset.mem_univ, true_and] at hsquare
    obtain ⟨row, rfl⟩ := hsquare
    exact rowWeight_nonnegative hsymm hdominant row
  · rw [atomSquareList, List.map_map, sum_map_toList]
    exact (weightedAtomSquares_eq_matrixExpansion atom matrix hsymm).symm




noncomputable def squareList
    {G : Type v} [Group G] (basis : ι → G)
    (matrix : Matrix ι ι ℚ) :
    List (ℚ × RationalGroupRing G) :=
  Finset.univ.toList.map fun row : Row ι ↦
    (rowWeight matrix row,
      RationalGroupRing.basisVector basis (rowCoefficient matrix row))



theorem matrixExpansion_isPositiveSumOfSquares
    {G : Type v} [Group G] (basis : ι → G)
    (matrix : Matrix ι ι ℚ) (hsymm : matrix.IsSymm)
    (hdominant : IsDiagonallyDominant matrix) :
    RationalGroupRing.IsPositiveSumOfSquares
      (∑ i, ∑ j, matrix i j •
        MonoidAlgebra.single ((basis i)⁻¹ * basis j) 1) := by
  classical
  refine ⟨squareList basis matrix, ?_, ?_⟩
  · intro square hsquare
    simp only [squareList, List.mem_map, Finset.mem_toList,
      Finset.mem_univ, true_and] at hsquare
    obtain ⟨row, rfl⟩ := hsquare
    exact rowWeight_nonnegative hsymm hdominant row
  · rw [squareList, List.map_map, sum_map_toList]
    exact (weightedSquares_eq_matrixExpansion basis matrix hsymm).symm

end SDDCertificate

end ConnesRigidity

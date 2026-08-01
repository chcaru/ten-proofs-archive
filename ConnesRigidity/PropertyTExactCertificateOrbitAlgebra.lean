


import ConnesRigidity.GroupRingCertificateAlgebra












namespace ConnesRigidity

namespace AffineSymplecticOrbitCertificate

universe u v w

variable {G : Type u} [Group G]


noncomputable def groupAtom {ι : Type v} (basis : ι → G) (i : ι) :
    RationalGroupRing G :=
  MonoidAlgebra.single (basis i) 1


noncomputable def fullGramExpansion {ι : Type v} [Fintype ι]
    (basis : ι → G) (gram : ι → ι → ℚ) : RationalGroupRing G :=
  ∑ i, ∑ j, gram i j •
    MonoidAlgebra.single ((basis i)⁻¹ * basis j) 1



theorem fullGramExpansion_coeff {ι : Type v} [Fintype ι] [DecidableEq G]
    (basis : ι → G) (gram : ι → ι → ℚ) (g : G) :
    (fullGramExpansion basis gram).coeff g =
      ∑ i, ∑ j, if (basis i)⁻¹ * basis j = g then gram i j else 0 := by
  classical
  simp [fullGramExpansion, Finsupp.single_apply]



theorem mem_fullGramExpansion_support {ι : Type v} [Fintype ι]
    (basis : ι → G) (gram : ι → ι → ℚ) {g : G}
    (hg : g ∈ (fullGramExpansion basis gram).coeff.support) :
    ∃ i j, (basis i)⁻¹ * basis j = g := by
  classical
  have hnonzero := Finsupp.mem_support_iff.mp hg
  by_contra hmissing
  push Not at hmissing
  apply hnonzero
  simp [fullGramExpansion_coeff, hmissing]



theorem groupRing_eq_of_coeff_eq_on_support [DecidableEq G]
    (left right : RationalGroupRing G)
    (hcoeff : ∀ g ∈ left.coeff.support ∪ right.coeff.support,
      left.coeff g = right.coeff g) :
    left = right := by
  classical
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  by_cases hleft : g ∈ left.coeff.support
  · exact hcoeff g (Finset.mem_union_left _ hleft)
  by_cases hright : g ∈ right.coeff.support
  · exact hcoeff g (Finset.mem_union_right _ hright)
  have hleft_zero : left.coeff g = 0 :=
    Classical.byContradiction fun h => hleft (Finsupp.mem_support_iff.mpr h)
  have hright_zero : right.coeff g = 0 :=
    Classical.byContradiction fun h => hright (Finsupp.mem_support_iff.mpr h)
  exact hleft_zero.trans hright_zero.symm



noncomputable def reducedGroupAtom {n : ℕ}
    (basis : Fin (n + 1) → G) (i : Fin n) : RationalGroupRing G :=
  groupAtom basis i.succ - groupAtom basis 0







theorem sum_pair_eq_sum_key {ι : Type v} {κ : Type w}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    {A : Type*} [AddCommMonoid A]
    (key : ι → ι → κ) (term : ι → ι → A) :
    (∑ i, ∑ j, term i j) =
      ∑ k, ∑ i, ∑ j, if key i j = k then term i j else 0 := by
  classical
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp


theorem fullGramExpansion_eq_sum_key {ι : Type v} {κ : Type w}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (basis : ι → G) (gram : ι → ι → ℚ) (key : ι → ι → κ) :
    fullGramExpansion basis gram =
      ∑ k, ∑ i, ∑ j,
        if key i j = k then
          gram i j • MonoidAlgebra.single ((basis i)⁻¹ * basis j) 1
        else 0 := by
  exact sum_pair_eq_sum_key key fun i j ↦
    gram i j • MonoidAlgebra.single ((basis i)⁻¹ * basis j) 1



theorem centeredGramExpansion_eq {ι : Type v} [Fintype ι]
    (atom : ι → RationalGroupRing G) (gram : ι → ι → ℚ)
    (center : RationalGroupRing G)
    (hrow : ∀ i, ∑ j, gram i j = 0)
    (hcol : ∀ j, ∑ i, gram i j = 0) :
    (∑ i, ∑ j, gram i j •
      (RationalGroupRing.adjoint (atom i - center) * (atom j - center))) =
      ∑ i, ∑ j, gram i j •
        (RationalGroupRing.adjoint (atom i) * atom j) := by
  classical
  simp_rw [RationalGroupRing.adjoint_sub, sub_mul, mul_sub,
    smul_sub]
  have hright (i : ι) :
      (∑ j, gram i j •
        (RationalGroupRing.adjoint (atom i) * center)) = 0 := by
    rw [← Finset.sum_smul, hrow i, zero_smul]
  have hconstant (i : ι) :
      (∑ j, gram i j •
        (RationalGroupRing.adjoint center * center)) = 0 := by
    rw [← Finset.sum_smul, hrow i, zero_smul]
  have hleft :
      (∑ i, ∑ j, gram i j •
        (RationalGroupRing.adjoint center * atom j)) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [← Finset.sum_smul, hcol j, zero_smul]
  simp_rw [Finset.sum_sub_distrib]
  simp only [hright, hconstant, Finset.sum_const_zero, sub_zero, hleft]



theorem fullGramExpansion_eq_reduced_of_zero_sums {n : ℕ}
    (basis : Fin (n + 1) → G) (gram : Fin (n + 1) → Fin (n + 1) → ℚ)
    (hrow : ∀ i, ∑ j, gram i j = 0)
    (hcol : ∀ j, ∑ i, gram i j = 0) :
    fullGramExpansion basis gram =
      ∑ i : Fin n, ∑ j : Fin n,
        gram i.succ j.succ •
          (RationalGroupRing.adjoint (reducedGroupAtom basis i) *
            reducedGroupAtom basis j) := by
  classical
  have hatom (i j : Fin (n + 1)) :
      RationalGroupRing.adjoint (groupAtom basis i) * groupAtom basis j =
        MonoidAlgebra.single ((basis i)⁻¹ * basis j) 1 := by
    simp [groupAtom, RationalGroupRing.adjoint_single,
      MonoidAlgebra.single_mul_single]
  rw [fullGramExpansion]
  simp_rw [← hatom]
  rw [← centeredGramExpansion_eq (groupAtom basis) gram
    (groupAtom basis 0) hrow hcol]
  rw [Fin.sum_univ_succ]
  simp only [sub_self, RationalGroupRing.adjoint_zero, zero_mul,
    smul_zero, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succ]
  simp [reducedGroupAtom]

end AffineSymplecticOrbitCertificate

end ConnesRigidity

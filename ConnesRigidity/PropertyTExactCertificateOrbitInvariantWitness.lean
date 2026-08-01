
import ConnesRigidity.PropertyTExactCertificateOrbitFiniteGroup
import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientIncidence
import ConnesRigidity.PropertyTExactCertificateOrbitIncidenceValidation
import ConnesRigidity.PropertyTExactCertificateOrbitStabilizerGramSoundness
import ConnesRigidity.PropertyTExactCertificateOrbitBasisPermutation
import ConnesRigidity.PropertyTExactCertificateOrbitGramRepresentativeValidation
import ConnesRigidity.PropertyTExactCertificateOrbitPairWitnessSoundness
import ConnesRigidity.PropertyTExactCertificateOrbitPairKeyBound
import Mathlib.Data.ZMod.Basic

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators

noncomputable section

set_option maxRecDepth 1000000

theorem orbitInvariant_basisData_size : basisData.size = 425 := by
  decide +kernel

theorem gramOrbitRepresentativeLeft_lt (orbit : Fin 2256) :
    (gramOrbitRepresentativeLeft orbit.val).toNat < 425 := by
  have hindex : orbit.val < gramOrbitData.size := by
    simp [gramOrbitData_size]
  have hfields := orbitGramRepresentativeFields_valid orbit.val hindex
  have hentry : gramOrbitRepresentativeLeft orbit.val =
      orbitEntry gramOrbitData[orbit.val] 0 := by
    simp [gramOrbitRepresentativeLeft, dataEntry, orbitEntry,
      Array.getD_eq_getD_getElem?, hindex]
  rw [hentry]
  have hbound := (Int.toNat_lt hfields.2.1.1).2 hfields.2.1.2
  simpa [orbitInvariant_basisData_size] using hbound

theorem gramOrbitRepresentativeRight_lt (orbit : Fin 2256) :
    (gramOrbitRepresentativeRight orbit.val).toNat < 425 := by
  have hindex : orbit.val < gramOrbitData.size := by
    simp [gramOrbitData_size]
  have hfields := orbitGramRepresentativeFields_valid orbit.val hindex
  have hentry : gramOrbitRepresentativeRight orbit.val =
      orbitEntry gramOrbitData[orbit.val] 1 := by
    simp [gramOrbitRepresentativeRight, dataEntry, orbitEntry,
      Array.getD_eq_getD_getElem?, hindex]
  rw [hentry]
  have hbound := (Int.toNat_lt hfields.2.2.1.1).2 hfields.2.2.1.2
  simpa [orbitInvariant_basisData_size] using hbound

noncomputable def orbitGramRepresentative (orbit : Fin 2256) :
    Fin 425 × Fin 425 :=
  (⟨(gramOrbitRepresentativeLeft orbit.val).toNat,
      gramOrbitRepresentativeLeft_lt orbit⟩,
    ⟨(gramOrbitRepresentativeRight orbit.val).toNat,
      gramOrbitRepresentativeRight_lt orbit⟩)

@[simp] theorem orbitGramRepresentative_fst_val (orbit : Fin 2256) :
    (orbitGramRepresentative orbit).1.val =
      (gramOrbitRepresentativeLeft orbit.val).toNat := rfl

@[simp] theorem orbitGramRepresentative_snd_val (orbit : Fin 2256) :
    (orbitGramRepresentative orbit).2.val =
      (gramOrbitRepresentativeRight orbit.val).toNat := rfl

noncomputable def orbitPairKey (left right : Fin 425) : Fin 2256 :=
  ⟨pairOrbit left.val right.val, orbitPair_lt left right⟩

@[simp] theorem orbitPairKey_val (left right : Fin 425) :
    (orbitPairKey left right).val = pairOrbit left.val right.val := rfl

abbrev OrbitSignedSymmetry := OrbitSymmetry × Multiplicative (ZMod 2)

@[simp] theorem card_orbitSignedSymmetry :
    Fintype.card OrbitSignedSymmetry = 128 := by
  rw [Fintype.card_prod, OrbitSymmetry.card]
  change 64 * Fintype.card (ZMod 2) = 128
  simp

theorem zmodTwo_eq_zero_or_one (value : ZMod 2) :
    value = 0 ∨ value = 1 := by
  have hvalue := ZMod.val_lt value
  interval_cases h : value.val
  · exact Or.inl ((ZMod.val_eq_zero value).mp h)
  · exact Or.inr ((ZMod.val_eq_one (by decide) value).mp h)

def signedPairAction {α : Type*} [MulAction OrbitSymmetry α]
    (symmetry : OrbitSignedSymmetry) (pair : α × α) : α × α :=
  if symmetry.2.toAdd = 0 then
    (symmetry.1 • pair.1, symmetry.1 • pair.2)
  else
    (symmetry.1 • pair.2, symmetry.1 • pair.1)

instance signedPairMulAction {α : Type*} [MulAction OrbitSymmetry α] :
    MulAction OrbitSignedSymmetry (α × α) where
  smul := signedPairAction
  one_smul pair := by
    change signedPairAction 1 pair = pair
    simp [signedPairAction]
  mul_smul left right pair := by
    change signedPairAction (left * right) pair =
      signedPairAction left (signedPairAction right pair)
    obtain hleft | hleft := zmodTwo_eq_zero_or_one left.2.toAdd
    all_goals obtain hright | hright := zmodTwo_eq_zero_or_one right.2.toAdd
    all_goals simp [signedPairAction, toAdd_mul,
      hleft, hright, mul_smul,
      show (1 + 1 : ZMod 2) = 0 by decide]

@[simp] theorem signedPairAction_apply {α : Type*}
    [MulAction OrbitSymmetry α]
    (symmetry : OrbitSignedSymmetry) (pair : α × α) :
    symmetry • pair =
      if symmetry.2.toAdd = 0 then
        (symmetry.1 • pair.1, symmetry.1 • pair.2)
      else
        (symmetry.1 • pair.2, symmetry.1 • pair.1) := rfl

def signedGroupAction (symmetry : OrbitSignedSymmetry)
    (element : constructedGammaZeroGroup) : constructedGammaZeroGroup :=
  if symmetry.2.toAdd = 0 then
    symmetry.1 • element
  else
    (symmetry.1 • element)⁻¹

instance signedGammaZeroMulAction :
    MulAction OrbitSignedSymmetry constructedGammaZeroGroup where
  smul := signedGroupAction
  one_smul element := by
    change signedGroupAction 1 element = element
    simp [signedGroupAction]
  mul_smul left right element := by
    change signedGroupAction (left * right) element =
      signedGroupAction left (signedGroupAction right element)
    obtain hleft | hleft := zmodTwo_eq_zero_or_one left.2.toAdd
    all_goals obtain hright | hright := zmodTwo_eq_zero_or_one right.2.toAdd
    all_goals simp [signedGroupAction, toAdd_mul,
      hleft, hright, mul_smul,
      OrbitSymmetry.smul_def,
      show (1 + 1 : ZMod 2) = 0 by decide]

@[simp] theorem signedGroupAction_apply
    (symmetry : OrbitSignedSymmetry)
    (element : constructedGammaZeroGroup) :
    symmetry • element =
      if symmetry.2.toAdd = 0 then
        orbitSymmetry symmetry.1.index element
      else
        (orbitSymmetry symmetry.1.index element)⁻¹ := rfl

noncomputable instance signedGroupOrbitFintype
    (element : constructedGammaZeroGroup) :
    Fintype (MulAction.orbit OrbitSignedSymmetry element) :=
  (Finite.finite_mulAction_orbit element).fintype

theorem signedPairProduct_equivariant
    {α : Type*} [MulAction OrbitSymmetry α]
    (basis : α → constructedGammaZeroGroup)
    (hbasis : ∀ symmetry : OrbitSymmetry, ∀ index : α,
      orbitSymmetry symmetry.index (basis index) = basis (symmetry • index))
    (symmetry : OrbitSignedSymmetry) (pair : α × α) :
    (basis (symmetry • pair).1)⁻¹ * basis (symmetry • pair).2 =
      symmetry • ((basis pair.1)⁻¹ * basis pair.2) := by
  obtain hparity | hparity :=
    zmodTwo_eq_zero_or_one symmetry.2.toAdd
  · simp only [signedPairAction_apply, signedGroupAction_apply, hparity,
      if_true]
    rw [← hbasis, ← hbasis, map_mul, map_inv]
  · simp only [signedPairAction_apply, signedGroupAction_apply, hparity,
      one_ne_zero, if_false]
    rw [← hbasis, ← hbasis, map_mul, map_inv, mul_inv_rev, inv_inv]

noncomputable def signedOrbitFinset
    {α : Type*} [Fintype α] [DecidableEq α]
    [MulAction OrbitSignedSymmetry α] (base : α) : Finset α := by
  classical
  exact Finset.univ.filter fun value =>
    value ∈ MulAction.orbit OrbitSignedSymmetry base

@[simp] theorem mem_signedOrbitFinset
    {α : Type*} [Fintype α] [DecidableEq α]
    [MulAction OrbitSignedSymmetry α] (base value : α) :
    value ∈ signedOrbitFinset base ↔
      value ∈ MulAction.orbit OrbitSignedSymmetry base := by
  classical
  simp [signedOrbitFinset]

theorem signedOrbitFinset_card
    {α : Type*} [Fintype α] [DecidableEq α]
    [MulAction OrbitSignedSymmetry α] (base : α)
    [Fintype (MulAction.orbit OrbitSignedSymmetry base)] :
    (signedOrbitFinset base).card =
      Fintype.card (MulAction.orbit OrbitSignedSymmetry base) := by
  classical
  symm
  exact Fintype.card_subtype _

theorem orbitSymmetry_sum_eq_range_foldl (value : Nat → Nat) :
    (∑ symmetry : OrbitSymmetry, value symmetry.index.val) =
      (List.range 64).foldl
        (fun total index => total + value index) 0 := by
  calc
    (∑ symmetry : OrbitSymmetry, value symmetry.index.val) =
        ∑ index : Fin 64, value index.val :=
      Fintype.sum_equiv OrbitSymmetry.equivFin _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range, ← List.toFinset_range 64,
        List.sum_toFinset value List.nodup_range,
        List.sum_eq_foldl, List.foldl_map]

theorem orbitGramStabilizerCount_eq_sum (left right : Nat) :
    orbitGramStabilizerCount left right =
      ∑ symmetry : OrbitSymmetry,
        ((if symmetryBasisImage symmetry.index.val left = left ∧
              symmetryBasisImage symmetry.index.val right = right
            then 1 else 0) +
          (if symmetryBasisImage symmetry.index.val left = right ∧
              symmetryBasisImage symmetry.index.val right = left
            then 1 else 0)) := by
  unfold orbitGramStabilizerCount
  have hsize : symmetryData.size = 64 := by
    simpa [symmetryCardinality] using
      (orbitSymmetryCompositionCheck_sound
        orbitSymmetryCompositionCheck_valid).1
  rw [hsize]
  have hsum := orbitSymmetry_sum_eq_range_foldl
    (fun symmetry =>
      ((if symmetryBasisImage symmetry left = left ∧
            symmetryBasisImage symmetry right = right then 1 else 0) +
        (if symmetryBasisImage symmetry left = right ∧
            symmetryBasisImage symmetry right = left then 1 else 0)))
  rw [hsum]
  apply congrArg
    (fun step : Nat → Nat → Nat => (List.range 64).foldl step 0)
  funext total symmetry
  simp only [Nat.add_assoc]

theorem signedPair_card_stabilizer_eq_two_sum
    {G X : Type*} [Group G] [Fintype G] [DecidableEq X]
    [MulAction (G × Multiplicative (ZMod 2)) X] (point : X) :
    Fintype.card (MulAction.stabilizer
      (G × Multiplicative (ZMod 2)) point) =
      ∑ symmetry : G,
        ((if (symmetry, Multiplicative.ofAdd (0 : ZMod 2)) • point = point
          then 1 else 0) +
          (if (symmetry, Multiplicative.ofAdd (1 : ZMod 2)) • point = point
          then 1 else 0)) := by
  classical
  change Fintype.card
    {symmetry : G × Multiplicative (ZMod 2) //
      symmetry • point = point} = _
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro symmetry _
  let equivalence : Multiplicative (ZMod 2) ≃ Fin 2 :=
    Multiplicative.toAdd.trans (ZMod.finEquiv 2).toEquiv.symm
  calc
    (∑ parity : Multiplicative (ZMod 2),
        if (symmetry, parity) • point = point then 1 else 0) =
        ∑ parity : Fin 2,
          if (symmetry, equivalence.symm parity) • point = point
            then 1 else 0 :=
      Fintype.sum_equiv equivalence _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fin.sum_univ_two]
      rfl

theorem signedPair_stabilizer_card
    [MulAction OrbitSymmetry (Fin 425)]
    (himage : ∀ (symmetry : OrbitSymmetry) (index : Fin 425),
      (symmetry • index).val =
        symmetryBasisImage symmetry.index.val index.val)
    (left right : Fin 425) :
    Fintype.card
        (MulAction.stabilizer OrbitSignedSymmetry (left, right)) =
      orbitGramStabilizerCount left.val right.val := by
  rw [signedPair_card_stabilizer_eq_two_sum,
    orbitGramStabilizerCount_eq_sum]
  apply Finset.sum_congr rfl
  intro symmetry _
  simp [signedPairAction_apply, Prod.mk.injEq,
    Fin.ext_iff, himage, and_comm]

theorem signedOrbit_card_eq_checked_size
    {α : Type*} [MulAction OrbitSignedSymmetry α]
    (point : α) [Fintype (MulAction.orbit OrbitSignedSymmetry point)]
    [Fintype (MulAction.stabilizer OrbitSignedSymmetry point)]
    (size : Int) (count : Nat)
    (hpositive : 0 < size)
    (hcount : Fintype.card
      (MulAction.stabilizer OrbitSignedSymmetry point) = count)
    (hchecked : size * (count : Int) = (128 : Int)) :
    Fintype.card (MulAction.orbit OrbitSignedSymmetry point) =
      size.toNat := by
  have hsize : (size.toNat : Int) = size :=
    Int.toNat_of_nonneg hpositive.le
  have hcheckedNat : size.toNat * count = 128 := by
    exact_mod_cast hsize.symm ▸ hchecked
  have hactual :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      OrbitSignedSymmetry point
  rw [card_orbitSignedSymmetry, hcount] at hactual
  have hcountPositive : 0 < count := by
    by_contra hnot
    have hzero : count = 0 := by omega
    simp [hzero] at hcheckedNat
  apply Nat.eq_of_mul_eq_mul_right hcountPositive
  exact hactual.trans hcheckedNat.symm

noncomputable instance signedPairOrbitFintype
    [MulAction OrbitSymmetry (Fin 425)] (pair : Fin 425 × Fin 425) :
    Fintype (MulAction.orbit OrbitSignedSymmetry pair) :=
  Fintype.ofFinite _

theorem orbitGramRepresentative_orbit_card_of_action
    [MulAction OrbitSymmetry (Fin 425)]
    (himage : ∀ (symmetry : OrbitSymmetry) (index : Fin 425),
      (symmetry • index).val =
        symmetryBasisImage symmetry.index.val index.val)
    (orbit : Fin 2256) :
    Fintype.card (MulAction.orbit OrbitSignedSymmetry
      (orbitGramRepresentative orbit)) =
        (gramOrbitSize orbit.val).toNat := by
  classical
  have hindex : orbit.val < gramOrbitData.size := by
    simp [gramOrbitData_size]
  have hrow : gramOrbitData[orbit.val]? =
      some gramOrbitData[orbit.val] := by
    simp [hindex]
  have hcheck : orbitGramStabilizerRowCheck orbit.val = true :=
    (List.all_eq_true.mp orbitGramStabilizerCheck_valid)
      orbit.val (List.mem_range.mpr hindex)
  obtain ⟨_, _, hpositive, hidentity⟩ :=
    orbitGramStabilizerRowCheck_sound orbit.val
      gramOrbitData[orbit.val] hrow hcheck
  have hsize : gramOrbitSize orbit.val =
      orbitEntry gramOrbitData[orbit.val] 7 := by
    simp [gramOrbitSize, dataEntry, orbitEntry,
      Array.getD_eq_getD_getElem?, hindex]
  have hleft : gramOrbitRepresentativeLeft orbit.val =
      orbitEntry gramOrbitData[orbit.val] 0 := by
    simp [gramOrbitRepresentativeLeft, dataEntry, orbitEntry,
      Array.getD_eq_getD_getElem?, hindex]
  have hright : gramOrbitRepresentativeRight orbit.val =
      orbitEntry gramOrbitData[orbit.val] 1 := by
    simp [gramOrbitRepresentativeRight, dataEntry, orbitEntry,
      Array.getD_eq_getD_getElem?, hindex]
  have hsymmetrySize : symmetryData.size = 64 := by
    simpa [symmetryCardinality] using
      (orbitSymmetryCompositionCheck_sound
        orbitSymmetryCompositionCheck_valid).1
  apply signedOrbit_card_eq_checked_size
    (orbitGramRepresentative orbit)
    (gramOrbitSize orbit.val)
    (orbitGramStabilizerCount
      (orbitGramRepresentative orbit).1.val
      (orbitGramRepresentative orbit).2.val)
    (by simpa [hsize] using hpositive)
    (signedPair_stabilizer_card himage
      (orbitGramRepresentative orbit).1
      (orbitGramRepresentative orbit).2)
  simpa [hsize, hleft, hright, orbitGramRepresentative,
    hsymmetrySize] using hidentity

theorem orbitGramRepresentative_orbit_card (orbit : Fin 2256) :
    Fintype.card (MulAction.orbit OrbitSignedSymmetry
      (orbitGramRepresentative orbit)) =
        (gramOrbitSize orbit.val).toNat :=
  orbitGramRepresentative_orbit_card_of_action
    (fun symmetry index => orbitBasis_smul_val symmetry index) orbit

theorem orbitList_foldl_eq_fin_sum
    {α : Type*} (rows : List α) (value : α → Int) :
    rows.foldl (fun total row => total + value row) 0 =
      ∑ index : Fin rows.length, value rows[index] := by
  rw [← List.foldl_map, ← List.sum_eq_foldl]
  induction rows with
  | nil => simp
  | cons head tail ih =>
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      exact congrArg (fun total => value head + total) ih

theorem orbitNat_sum_eq_of_int_fold
    {α : Type*} (rows : List α) (value : α → Int)
    (hpositive : ∀ row ∈ rows, 0 ≤ value row)
    (target : Nat)
    (hfold : rows.foldl (fun total row => total + value row) 0 =
      (target : Int)) :
    (∑ index : Fin rows.length, (value rows[index]).toNat) = target := by
  have hsum :
      (∑ index : Fin rows.length, value rows[index]) = (target : Int) :=
    (orbitList_foldl_eq_fin_sum rows value).symm ▸ hfold
  have hterm (index : Fin rows.length) :
      (((value rows[index]).toNat : Nat) : Int) = value rows[index] :=
    Int.toNat_of_nonneg (hpositive _ (List.getElem_mem index.isLt))
  have hcast :
      (((∑ index : Fin rows.length, (value rows[index]).toNat) : Nat) : Int) =
        (target : Int) := by
    rw [Nat.cast_sum]
    simpa only [hterm] using hsum
  exact_mod_cast hcast

theorem orbitLabel_eq_of_mem_of_card
    {H α κ : Type*} [Group H] [Fintype α] [Fintype κ]
    [MulAction H α]
    (representative : κ → α)
    [∀ index : κ, Fintype (MulAction.orbit H (representative index))]
    (label : α → κ)
    (hcover : ∀ value : α,
      value ∈ MulAction.orbit H (representative (label value)))
    (hcard : (∑ index : κ,
      Fintype.card (MulAction.orbit H (representative index))) =
        Fintype.card α)
    {value : α} {index : κ}
    (hvalue : value ∈ MulAction.orbit H (representative index)) :
    label value = index := by
  classical
  let projection :
      (Σ index : κ, MulAction.orbit H (representative index)) → α :=
    fun point => point.2.1
  have hsurjective : Function.Surjective projection := by
    intro value
    exact ⟨⟨label value, ⟨value, hcover value⟩⟩, rfl⟩
  have hbijective : Function.Bijective projection :=
    (Fintype.bijective_iff_surjective_and_card projection).2
      ⟨hsurjective, by simpa [Fintype.card_sigma] using hcard⟩
  have heq :
      (⟨label value, ⟨value, hcover value⟩⟩ :
        Σ index : κ, MulAction.orbit H (representative index)) =
        ⟨index, ⟨value, hvalue⟩⟩ := hbijective.1 rfl
  exact congrArg Sigma.fst heq

theorem orbitLabel_smul_eq_of_card
    {H α κ : Type*} [Group H] [Fintype α] [Fintype κ]
    [MulAction H α]
    (representative : κ → α)
    [∀ index : κ, Fintype (MulAction.orbit H (representative index))]
    (label : α → κ)
    (hcover : ∀ value : α,
      value ∈ MulAction.orbit H (representative (label value)))
    (hcard : (∑ index : κ,
      Fintype.card (MulAction.orbit H (representative index))) =
        Fintype.card α)
    (symmetry : H) (value : α) :
    label (symmetry • value) = label value := by
  apply orbitLabel_eq_of_mem_of_card representative label hcover hcard
  obtain ⟨other, hother⟩ :=
    MulAction.mem_orbit_iff.mp (hcover value)
  exact MulAction.mem_orbit_iff.mpr
    ⟨symmetry * other, by simp [mul_smul, hother]⟩

theorem orbitLabel_eq_iff_mem_of_card
    {H α κ : Type*} [Group H] [Fintype α] [Fintype κ]
    [MulAction H α]
    (representative : κ → α)
    [∀ index : κ, Fintype (MulAction.orbit H (representative index))]
    (label : α → κ)
    (hcover : ∀ value : α,
      value ∈ MulAction.orbit H (representative (label value)))
    (hcard : (∑ index : κ,
      Fintype.card (MulAction.orbit H (representative index))) =
        Fintype.card α)
    (value : α) (index : κ) :
    label value = index ↔
      value ∈ MulAction.orbit H (representative index) := by
  constructor
  · intro heq
    rw [← heq]
    exact hcover value
  · exact orbitLabel_eq_of_mem_of_card representative label hcover hcard

theorem orbitPairLabel_symmetry_eq_of_card
    {α κ : Type*} [Fintype α] [Fintype κ]
    [MulAction OrbitSymmetry α]
    (representative : κ → α × α)
    [∀ index : κ,
      Fintype (MulAction.orbit OrbitSignedSymmetry
        (representative index))]
    (label : α × α → κ)
    (hcover : ∀ pair : α × α,
      pair ∈ MulAction.orbit OrbitSignedSymmetry
        (representative (label pair)))
    (hcard : (∑ index : κ,
      Fintype.card (MulAction.orbit OrbitSignedSymmetry
        (representative index))) = Fintype.card (α × α))
    (symmetry : OrbitSymmetry) (left right : α) :
    label (symmetry • left, symmetry • right) = label (left, right) := by
  have hinvariant := orbitLabel_smul_eq_of_card representative label
    hcover hcard
    (symmetry, Multiplicative.ofAdd (0 : ZMod 2)) (left, right)
  simpa [signedPairAction_apply] using hinvariant

theorem orbitPairLabel_swap_eq_of_card
    {α κ : Type*} [Fintype α] [Fintype κ]
    [MulAction OrbitSymmetry α]
    (representative : κ → α × α)
    [∀ index : κ,
      Fintype (MulAction.orbit OrbitSignedSymmetry
        (representative index))]
    (label : α × α → κ)
    (hcover : ∀ pair : α × α,
      pair ∈ MulAction.orbit OrbitSignedSymmetry
        (representative (label pair)))
    (hcard : (∑ index : κ,
      Fintype.card (MulAction.orbit OrbitSignedSymmetry
        (representative index))) = Fintype.card (α × α))
    (left right : α) :
    label (right, left) = label (left, right) := by
  have hinvariant := orbitLabel_smul_eq_of_card representative label
    hcover hcard
    (1, Multiplicative.ofAdd (1 : ZMod 2)) (left, right)
  simpa [signedPairAction_apply] using hinvariant

theorem orbitPairCoefficient_swap_of_card
    {α κ β : Type*} [Fintype α] [Fintype κ]
    [MulAction OrbitSymmetry α]
    (representative : κ → α × α)
    [∀ index : κ,
      Fintype (MulAction.orbit OrbitSignedSymmetry
        (representative index))]
    (label : α × α → κ) (coefficient : κ → β)
    (hcover : ∀ pair : α × α,
      pair ∈ MulAction.orbit OrbitSignedSymmetry
        (representative (label pair)))
    (hcard : (∑ index : κ,
      Fintype.card (MulAction.orbit OrbitSignedSymmetry
        (representative index))) = Fintype.card (α × α))
    (left right : α) :
    coefficient (label (right, left)) =
      coefficient (label (left, right)) := by
  rw [orbitPairLabel_swap_eq_of_card representative label
    hcover hcard left right]

theorem orbitPairCoefficient_symmetry_of_card
    {α κ β : Type*} [Fintype α] [Fintype κ]
    [MulAction OrbitSymmetry α]
    (representative : κ → α × α)
    [∀ index : κ,
      Fintype (MulAction.orbit OrbitSignedSymmetry
        (representative index))]
    (label : α × α → κ) (coefficient : κ → β)
    (hcover : ∀ pair : α × α,
      pair ∈ MulAction.orbit OrbitSignedSymmetry
        (representative (label pair)))
    (hcard : (∑ index : κ,
      Fintype.card (MulAction.orbit OrbitSignedSymmetry
        (representative index))) = Fintype.card (α × α))
    (symmetry : OrbitSymmetry) (left right : α) :
    coefficient (label (symmetry • left, symmetry • right)) =
      coefficient (label (left, right)) := by
  rw [orbitPairLabel_symmetry_eq_of_card representative label
    hcover hcard symmetry left right]

end

end ConnesRigidity.AffineSymplecticOrbitCertificate




import ConnesRigidity.PropertyTExactCertificateOrbitAlgebra
import ConnesRigidity.PropertyTExactCertificateOrbitAverage

















namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators

universe u v w

variable {G : Type u} [Group G]



noncomputable def gramPairFiberCount
    {ι : Type v} {κ : Type w} [Fintype ι] [DecidableEq ι]
    (basis : ι → G) (orbit : ι → ι → κ)
    (key : κ) (g : G) : Nat := by
  classical
  exact ((Finset.univ.product Finset.univ).filter fun pair : ι × ι =>
    orbit pair.1 pair.2 = key ∧
      (basis pair.1)⁻¹ * basis pair.2 = g).card



theorem sum_pair_indicator_eq_card
    {ι : Type v} [Fintype ι]
    (predicate : ι → ι → Prop) [DecidableRel predicate]
    (value : ℚ) :
    (∑ i, ∑ j, if predicate i j then value else 0) =
      ((((Finset.univ.product Finset.univ).filter fun pair : ι × ι =>
        predicate pair.1 pair.2).card : Nat) : ℚ) * value := by
  classical
  calc
    (∑ i, ∑ j, if predicate i j then value else 0) =
        ∑ pair ∈ Finset.univ.product Finset.univ,
          if predicate pair.1 pair.2 then value else 0 := by
      simpa using (Finset.sum_product
        (Finset.univ : Finset ι) (Finset.univ : Finset ι)
        (fun pair : ι × ι =>
          if predicate pair.1 pair.2 then value else 0)).symm
    _ = ∑ pair ∈ (Finset.univ.product Finset.univ).filter
          (fun pair : ι × ι => predicate pair.1 pair.2), value := by
      simpa using (Finset.sum_filter
        (fun pair : ι × ι => predicate pair.1 pair.2)
        (fun _pair : ι × ι => value)).symm
    _ = _ := by simp






theorem fullGramExpansion_coeff_eq_sum_pairFiberCount
    {ι : Type v} {κ : Type w}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (basis : ι → G) (orbit : ι → ι → κ)
    (entry : κ → ℚ) (g : G) :
    (fullGramExpansion basis (fun i j => entry (orbit i j))).coeff g =
      ∑ key, (gramPairFiberCount basis orbit key g : ℚ) * entry key := by
  classical
  rw [fullGramExpansion_coeff]
  rw [sum_pair_eq_sum_key orbit
    (fun i j => if (basis i)⁻¹ * basis j = g then entry (orbit i j) else 0)]
  apply Finset.sum_congr rfl
  intro key _hkey
  calc
    (∑ i, ∑ j,
        if orbit i j = key then
          (if (basis i)⁻¹ * basis j = g then entry (orbit i j) else 0)
        else 0) =
      ∑ i, ∑ j,
        if orbit i j = key ∧ (basis i)⁻¹ * basis j = g
        then entry key else 0 := by
          apply Finset.sum_congr rfl
          intro i _hi
          apply Finset.sum_congr rfl
          intro j _hj
          split_ifs with hkey' hproduct hboth <;>
            simp_all
    _ = (gramPairFiberCount basis orbit key g : ℚ) * entry key := by
      unfold gramPairFiberCount
      have hsum :=
        sum_pair_indicator_eq_card
          (fun i j => orbit i j = key ∧ (basis i)⁻¹ * basis j = g)
          (entry key)
      rw [hsum]
      congr 2
      congr 1
      ext pair
      simp





theorem fintype_card_eq_mul_card_fiber_of_equiv
    {α : Type v} {β : Type w} [Fintype α] [Fintype β] [DecidableEq β]
    (map : α → β) (base : β)
    (hfibers : ∀ point : β,
      Nonempty ({value : α // map value = point} ≃
        {value : α // map value = base})) :
    Fintype.card α =
      Fintype.card β *
        Fintype.card {value : α // map value = base} := by
  classical
  calc
    Fintype.card α =
        Fintype.card (Σ point : β, {value : α // map value = point}) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv map)).symm
    _ = ∑ point : β, Fintype.card {value : α // map value = point} := by
      rw [Fintype.card_sigma]
    _ = ∑ _point : β, Fintype.card {value : α // map value = base} := by
      apply Finset.sum_congr rfl
      intro point _hpoint
      exact Fintype.card_congr (Classical.choice (hfibers point))
    _ = Fintype.card β *
          Fintype.card {value : α // map value = base} := by
      simp




theorem card_fiber_eq_incidence_of_equiv
    {α : Type v} {β : Type w} [Fintype α] [Fintype β] [DecidableEq β]
    (map : α → β) (base : β) (incidence : Nat)
    (hcoefficient : 0 < Fintype.card β)
    (hcardinality : Fintype.card α = incidence * Fintype.card β)
    (hfibers : ∀ point : β,
      Nonempty ({value : α // map value = point} ≃
        {value : α // map value = base})) :
    Fintype.card {value : α // map value = base} = incidence := by
  have hcount :=
    fintype_card_eq_mul_card_fiber_of_equiv map base hfibers
  apply Nat.eq_of_mul_eq_mul_left hcoefficient
  calc
    Fintype.card β *
        Fintype.card {value : α // map value = base} =
      Fintype.card α := hcount.symm
    _ = Fintype.card β * incidence := by
      simpa only [Nat.mul_comm] using hcardinality






theorem finset_partition_eq_of_card_saturation
    {α : Type v} {κ : Type w}
    [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (key : α → κ) (orbit : κ → Finset α)
    (hsubset : ∀ value : α, value ∈ orbit (key value))
    (hcardinality : (∑ index : κ, (orbit index).card) = Fintype.card α) :
    ∀ index : κ,
      (Finset.univ.filter fun value : α => key value = index) = orbit index := by
  classical
  have hbucket_subset (index : κ) :
      (Finset.univ.filter fun value : α => key value = index) ⊆ orbit index := by
    intro value hvalue
    have hkey := (Finset.mem_filter.mp hvalue).2
    simpa only [hkey] using hsubset value
  have hbucket_sum :
      (∑ index : κ,
        (Finset.univ.filter fun value : α => key value = index).card) =
        Fintype.card α := by
    symm
    exact Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ) (t := Finset.univ) (f := key)
      (by simp)
  have hcard (index : κ) :
      (Finset.univ.filter fun value : α => key value = index).card =
        (orbit index).card := by
    have hall := (Finset.sum_eq_sum_iff_of_le
      (s := Finset.univ)
      (f := fun index : κ =>
        (Finset.univ.filter fun value : α => key value = index).card)
      (g := fun index : κ => (orbit index).card)
      (fun index _hindex => Finset.card_le_card (hbucket_subset index))).mp
        (hbucket_sum.trans hcardinality.symm)
    exact hall index (Finset.mem_univ index)
  intro index
  exact Finset.eq_of_subset_of_card_le
    (hbucket_subset index) (hcard index).ge


noncomputable def equivariantOrbitMap
    {H : Type*} {α : Type v} {β : Type w}
    [Group H] [MulAction H α] [MulAction H β]
    (map : α → β)
    (hequivariant : ∀ (symmetry : H) (value : α),
      map (symmetry • value) = symmetry • map value)
    (base : α) :
    MulAction.orbit H base → MulAction.orbit H (map base) :=
  fun value => ⟨map value, by
    obtain ⟨symmetry, hsymmetry⟩ := value.property
    change symmetry • base = (value : α) at hsymmetry
    refine ⟨symmetry, ?_⟩
    change symmetry • map base = map value
    rw [← hequivariant, hsymmetry]⟩

@[simp] theorem equivariantOrbitMap_apply
    {H : Type*} {α : Type v} {β : Type w}
    [Group H] [MulAction H α] [MulAction H β]
    (map : α → β)
    (hequivariant : ∀ (symmetry : H) (value : α),
      map (symmetry • value) = symmetry • map value)
    (base : α) (value : MulAction.orbit H base) :
    ((equivariantOrbitMap map hequivariant base value :
      MulAction.orbit H (map base)) : β) = map value := rfl



theorem orbit_exists_smul_eq
    {H : Type*} {α : Type v} [Group H] [MulAction H α]
    {base : α} (source target : MulAction.orbit H base) :
    ∃ symmetry : H, symmetry • (source : α) = (target : α) := by
  obtain ⟨first, hfirst⟩ := source.property
  obtain ⟨second, hsecond⟩ := target.property
  change first • base = (source : α) at hfirst
  change second • base = (target : α) at hsecond
  refine ⟨second * first⁻¹, ?_⟩
  rw [← hfirst, mul_smul, inv_smul_smul, hsecond]



noncomputable def equivariantOrbitFiberEquiv
    {H : Type*} {α : Type v} {β : Type w}
    [Group H] [MulAction H α] [MulAction H β]
    (map : α → β)
    (hequivariant : ∀ (symmetry : H) (value : α),
      map (symmetry • value) = symmetry • map value)
    (base : α) (source target : MulAction.orbit H (map base)) :
    {value : MulAction.orbit H base //
      equivariantOrbitMap map hequivariant base value = source} ≃
      {value : MulAction.orbit H base //
        equivariantOrbitMap map hequivariant base value = target} := by
  classical
  let symmetry := Classical.choose (orbit_exists_smul_eq source target)
  have hsymmetry := Classical.choose_spec (orbit_exists_smul_eq source target)
  refine
    { toFun := fun value => ⟨symmetry • value.val, ?_⟩
      invFun := fun value => ⟨symmetry⁻¹ • value.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply Subtype.ext
    change map (symmetry • (value.val : α)) = (target : β)
    rw [hequivariant]
    have hvalue := congrArg Subtype.val value.property
    change map (value.val : α) = (source : β) at hvalue
    rw [hvalue, hsymmetry]
  · apply Subtype.ext
    change map (symmetry⁻¹ • (value.val : α)) = (source : β)
    rw [hequivariant]
    have hvalue := congrArg Subtype.val value.property
    change map (value.val : α) = (target : β) at hvalue
    rw [hvalue, ← hsymmetry, inv_smul_smul]
  · intro value
    apply Subtype.ext
    change (symmetry⁻¹ • (symmetry • value.val)) = value.val
    exact inv_smul_smul symmetry value.val
  · intro value
    apply Subtype.ext
    change (symmetry • (symmetry⁻¹ • value.val)) = value.val
    exact smul_inv_smul symmetry value.val



theorem equivariantOrbitFiber_card_eq_incidence
    {H : Type*} {α : Type v} {β : Type w}
    [Group H] [MulAction H α] [MulAction H β] [DecidableEq β]
    (map : α → β)
    (hequivariant : ∀ (symmetry : H) (value : α),
      map (symmetry • value) = symmetry • map value)
    (base : α)
    [Fintype (MulAction.orbit H base)]
    [Fintype (MulAction.orbit H (map base))]
    (coefficient : MulAction.orbit H (map base)) (incidence : Nat)
    (hcardinality :
      Fintype.card (MulAction.orbit H base) =
        incidence * Fintype.card (MulAction.orbit H (map base))) :
    Fintype.card {value : MulAction.orbit H base //
      equivariantOrbitMap map hequivariant base value = coefficient} =
      incidence := by
  classical
  apply card_fiber_eq_incidence_of_equiv
    (equivariantOrbitMap map hequivariant base) coefficient incidence
  · exact Fintype.card_pos_iff.mpr
      ⟨⟨map base, MulAction.mem_orbit_self (map base)⟩⟩
  · exact hcardinality
  · intro point
    exact ⟨equivariantOrbitFiberEquiv map hequivariant base point coefficient⟩



noncomputable def gramPairOrbitFiberEquiv
    {H : Type*} {ι : Type v} {κ : Type w}
    [Group H] [MulAction H (ι × ι)] [MulAction H G]
    (basis : ι → G) (key : ι → ι → κ)
    (hequivariant : ∀ (symmetry : H) (pair : ι × ι),
      (basis (symmetry • pair).1)⁻¹ * basis (symmetry • pair).2 =
        symmetry • ((basis pair.1)⁻¹ * basis pair.2))
    (representative : ι × ι) (index : κ)
    (hkey : ∀ pair : ι × ι,
      key pair.1 pair.2 = index ↔
        pair ∈ MulAction.orbit H representative)
    (coefficient : G)
    (hcoefficient : coefficient ∈ MulAction.orbit H
      ((basis representative.1)⁻¹ * basis representative.2)) :
    {pair : ι × ι //
      key pair.1 pair.2 = index ∧
        (basis pair.1)⁻¹ * basis pair.2 = coefficient} ≃
      {pair : MulAction.orbit H representative //
        equivariantOrbitMap
          (fun pair : ι × ι =>
            (basis pair.1)⁻¹ * basis pair.2)
          hequivariant representative pair =
          (⟨coefficient, hcoefficient⟩ :
            MulAction.orbit H
              ((basis representative.1)⁻¹ * basis representative.2))} where
  toFun pair :=
    ⟨⟨pair.val, (hkey pair.val).mp pair.property.1⟩,
      Subtype.ext pair.property.2⟩
  invFun pair :=
    ⟨pair.val.val,
      (hkey pair.val.val).mpr pair.val.property,
      congrArg Subtype.val pair.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)





theorem gramPairFiberCount_eq_incidence_of_orbit
    {H : Type*} {ι : Type v} {κ : Type w}
    [Group H] [Fintype H] [Fintype ι] [DecidableEq ι]
    [MulAction H (ι × ι)] [MulAction H G] [DecidableEq G]
    (basis : ι → G) (key : ι → ι → κ)
    (hequivariant : ∀ (symmetry : H) (pair : ι × ι),
      (basis (symmetry • pair).1)⁻¹ * basis (symmetry • pair).2 =
        symmetry • ((basis pair.1)⁻¹ * basis pair.2))
    (representative : ι × ι) (index : κ)
    [Fintype (MulAction.orbit H representative)]
    [Fintype (MulAction.orbit H
      ((basis representative.1)⁻¹ * basis representative.2))]
    (hkey : ∀ pair : ι × ι,
      key pair.1 pair.2 = index ↔
        pair ∈ MulAction.orbit H representative)
    (coefficient : G)
    (hcoefficient : coefficient ∈ MulAction.orbit H
      ((basis representative.1)⁻¹ * basis representative.2))
    (incidence : Nat)
    (hcardinality :
      Fintype.card (MulAction.orbit H representative) =
        incidence * Fintype.card (MulAction.orbit H
          ((basis representative.1)⁻¹ * basis representative.2))) :
    gramPairFiberCount basis key index coefficient = incidence := by
  classical
  let product : ι × ι → G :=
    fun pair => (basis pair.1)⁻¹ * basis pair.2
  let coefficientPoint : MulAction.orbit H (product representative) :=
    ⟨coefficient, hcoefficient⟩
  have hfiber := equivariantOrbitFiber_card_eq_incidence
    (H := H) product hequivariant representative coefficientPoint
    incidence hcardinality
  have hequiv := Fintype.card_congr
    (gramPairOrbitFiberEquiv basis key hequivariant representative index
      hkey coefficient hcoefficient)
  have hsubtype :
      Fintype.card
        {pair : ι × ι // key pair.1 pair.2 = index ∧
          (basis pair.1)⁻¹ * basis pair.2 = coefficient} =
        gramPairFiberCount basis key index coefficient := by
    rw [Fintype.card_subtype]
    unfold gramPairFiberCount
    congr 1
    ext pair
    simp
  exact hsubtype.symm.trans (hequiv.trans hfiber)




theorem fullGramExpansion_coeff_eq_sum_orbit_incidence
    {ι : Type v} {κ : Type w}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (basis : ι → G) (orbit : ι → ι → κ)
    (entry : κ → ℚ) (incidence : κ → Nat)
    (contributes : κ → Prop) [DecidablePred contributes]
    (g : G)
    (hfiber : ∀ key,
      gramPairFiberCount basis orbit key g =
        if contributes key then incidence key else 0) :
    (fullGramExpansion basis (fun i j => entry (orbit i j))).coeff g =
      ∑ key, if contributes key
        then (incidence key : ℚ) * entry key else 0 := by
  rw [fullGramExpansion_coeff_eq_sum_pairFiberCount]
  apply Finset.sum_congr rfl
  intro key _hkey
  rw [hfiber key]
  split_ifs <;> simp

end ConnesRigidity.AffineSymplecticOrbitCertificate

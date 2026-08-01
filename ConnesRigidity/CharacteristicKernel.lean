


import ConnesRigidity.CocycleExtension










namespace ConnesRigidity

universe u v

namespace CocycleExtension

variable {G : Type u} {A : Type v}
variable [Group G] [AddCommGroup A] [DistribMulAction G A]

private abbrev zeroCocycle : NormalizedAddCocycle G A :=
  NormalizedAddCocycle.zero


def zeroInr : G →* CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) where
  toFun g := ⟨0, g⟩
  map_one' := rfl
  map_mul' g h := by
    apply CocycleExtension.ext
    · simp
    · simp

@[simp]
theorem zeroInr_apply (g : G) :
    zeroInr (A := A) g = ⟨0, g⟩ := rfl


def PreservesKernel
    (c : NormalizedAddCocycle G A)
    (f : CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) ≃*
      CocycleExtension c) : Prop :=
  ∀ x, x.snd = 1 ↔ (f x).snd = 1


def quotientHom
    (c : NormalizedAddCocycle G A)
    (f : CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) ≃*
      CocycleExtension c) : G →* G :=
  (rightHom c).comp (f.toMonoidHom.comp (zeroInr (A := A)))

@[simp]
theorem quotientHom_apply
    (c : NormalizedAddCocycle G A)
    (f : CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) ≃*
      CocycleExtension c)
    (g : G) :
    quotientHom c f g = (f ⟨0, g⟩).snd := rfl

theorem quotientHom_injective_of_preservesKernel
    (c : NormalizedAddCocycle G A)
    (f : CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) ≃*
      CocycleExtension c)
    (hf : PreservesKernel c f) :
    Function.Injective (quotientHom c f) := by
  intro g h hgh
  apply eq_of_mul_inv_eq_one
  have hker : quotientHom c f (g * h⁻¹) = 1 := by
    rw [map_mul, map_inv, hgh, mul_inv_cancel]
  have hsource : (⟨0, g * h⁻¹⟩ :
      CocycleExtension (zeroCocycle : NormalizedAddCocycle G A)).snd = 1 :=
    (hf ⟨0, g * h⁻¹⟩).mpr hker
  exact hsource

theorem quotientHom_surjective_of_preservesKernel
    (c : NormalizedAddCocycle G A)
    (f : CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) ≃*
      CocycleExtension c)
    (hf : PreservesKernel c f) :
    Function.Surjective (quotientHom c f) := by
  intro q
  let x : CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) :=
    f.symm ⟨0, q⟩
  refine ⟨x.snd, ?_⟩
  have hx :
      x = (⟨x.fst, (1 : G)⟩ :
        CocycleExtension (zeroCocycle : NormalizedAddCocycle G A)) *
        (⟨(0 : A), x.snd⟩ :
        CocycleExtension (zeroCocycle : NormalizedAddCocycle G A)) := by
    apply CocycleExtension.ext
    · simp
    · simp
  have hk : (f ⟨x.fst, (1 : G)⟩).snd = 1 :=
    (hf ⟨x.fst, (1 : G)⟩).mp rfl
  have hfx : f x = ⟨0, q⟩ :=
    f.apply_symm_apply ⟨0, q⟩
  calc
    quotientHom c f x.snd = (f ⟨(0 : A), x.snd⟩).snd := rfl
    _ = (f ⟨x.fst, (1 : G)⟩ * f ⟨(0 : A), x.snd⟩).snd := by simp [hk]
    _ = (f ((⟨x.fst, (1 : G)⟩ :
        CocycleExtension (zeroCocycle : NormalizedAddCocycle G A)) *
          (⟨(0 : A), x.snd⟩ :
            CocycleExtension (zeroCocycle : NormalizedAddCocycle G A)))).snd := by
      rw [f.map_mul]
    _ = (f x).snd := by rw [← hx]
    _ = q := congr_arg CocycleExtension.snd hfx


noncomputable def quotientEquivOfPreservesKernel
    (c : NormalizedAddCocycle G A)
    (f : CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) ≃*
      CocycleExtension c)
    (hf : PreservesKernel c f) : G ≃* G :=
  MulEquiv.ofBijective (quotientHom c f)
    ⟨quotientHom_injective_of_preservesKernel c f hf,
      quotientHom_surjective_of_preservesKernel c f hf⟩



noncomputable def splittingOfEquivPreservingKernel
    (c : NormalizedAddCocycle G A)
    (f : CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) ≃*
      CocycleExtension c)
    (hf : PreservesKernel c f) :
    Splitting c := by
  let β := quotientEquivOfPreservesKernel c f hf
  let s : G →* CocycleExtension c :=
    f.toMonoidHom.comp ((zeroInr (A := A)).comp β.symm.toMonoidHom)
  refine ⟨s, ?_⟩
  ext g
  exact β.apply_symm_apply g



theorem not_isomorphic_of_kernel_characteristic
    (c : NormalizedAddCocycle G A)
    (hc : ¬c.IsCoboundary)
    (hcharacteristic :
      ∀ f : CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) ≃*
        CocycleExtension c, PreservesKernel c f) :
    ¬Nonempty
      (CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) ≃*
        CocycleExtension c) := by
  rintro ⟨f⟩
  exact hc (isCoboundaryOfSplitting c
    (splittingOfEquivPreservingKernel c f (hcharacteristic f)))

end CocycleExtension

end ConnesRigidity

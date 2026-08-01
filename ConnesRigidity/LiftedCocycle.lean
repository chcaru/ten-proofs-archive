
import ConnesRigidity.CocycleExtension

namespace ConnesRigidity

universe u v w

structure ModTwoLiftingData (G : Type u) (V : Type v) (W : Type w)
    [Group G] [AddCommGroup V] [AddCommGroup W]
    [DistribMulAction G V] [DistribMulAction G W] where
  reduce : V →+ W
  reduce_smul : ∀ (g : G) (v : V), reduce (g • v) = g • reduce v
  lift : W → V
  reduce_lift : ∀ w : W, reduce (lift w) = w
  lift_zero : lift 0 = 0
  exponent_two : ∀ w : W, (2 : ℕ) • w = 0
  exists_half_of_reduce_eq_zero :
    ∀ v : V, reduce v = 0 → ∃ u : V, (2 : ℕ) • u = v
  two_nsmul_injective : Function.Injective (fun v : V ↦ (2 : ℕ) • v)

namespace ModTwoLiftingData

variable {G : Type u} {V : Type v} {W : Type w}
variable [Group G] [AddCommGroup V] [AddCommGroup W]
variable [DistribMulAction G V] [DistribMulAction G W]

variable (D : ModTwoLiftingData G V W)
variable (d : G → W)

def liftedOneCochain (g : G) : V :=
  D.lift (d g)

@[simp]
theorem reduce_liftedOneCochain (g : G) :
    D.reduce (D.liftedOneCochain d g) = d g :=
  D.reduce_lift _

theorem liftedOneCochain_one (hd : groupCohomology.IsCocycle₁ d) :
    D.liftedOneCochain d 1 = 0 := by
  rw [liftedOneCochain, groupCohomology.map_one_of_isCocycle₁ hd, D.lift_zero]

def liftDefect (g h : G) : V :=
  D.liftedOneCochain d g + g • D.liftedOneCochain d h -
    D.liftedOneCochain d (g * h)

theorem reduce_liftDefect (hd : groupCohomology.IsCocycle₁ d) (g h : G) :
    D.reduce (D.liftDefect d g h) = 0 := by
  simp only [liftDefect, map_sub, map_add, D.reduce_smul, reduce_liftedOneCochain]
  rw [hd g h]
  abel

noncomputable def halfLiftDefect (hd : groupCohomology.IsCocycle₁ d) (g h : G) : V :=
  Classical.choose
    (D.exists_half_of_reduce_eq_zero (D.liftDefect d g h) (D.reduce_liftDefect d hd g h))

theorem two_nsmul_halfLiftDefect (hd : groupCohomology.IsCocycle₁ d) (g h : G) :
    (2 : ℕ) • D.halfLiftDefect d hd g h = D.liftDefect d g h :=
  Classical.choose_spec
    (D.exists_half_of_reduce_eq_zero (D.liftDefect d g h) (D.reduce_liftDefect d hd g h))

theorem halfLiftDefect_one_left (hd : groupCohomology.IsCocycle₁ d) (g : G) :
    D.halfLiftDefect d hd 1 g = 0 := by
  apply D.two_nsmul_injective
  change (2 : ℕ) • D.halfLiftDefect d hd 1 g = (2 : ℕ) • (0 : V)
  rw [D.two_nsmul_halfLiftDefect]
  simp [liftDefect, D.liftedOneCochain_one d hd]

theorem halfLiftDefect_one_right (hd : groupCohomology.IsCocycle₁ d) (g : G) :
    D.halfLiftDefect d hd g 1 = 0 := by
  apply D.two_nsmul_injective
  change (2 : ℕ) • D.halfLiftDefect d hd g 1 = (2 : ℕ) • (0 : V)
  rw [D.two_nsmul_halfLiftDefect]
  simp [liftDefect, D.liftedOneCochain_one d hd]

theorem halfLiftDefect_cocycle (hd : groupCohomology.IsCocycle₁ d) :
    ∀ g h k,
      D.halfLiftDefect d hd (g * h) k + D.halfLiftDefect d hd g h =
        g • D.halfLiftDefect d hd h k + D.halfLiftDefect d hd g (h * k) := by
  intro g h k
  apply D.two_nsmul_injective
  change
    (2 : ℕ) •
        (D.halfLiftDefect d hd (g * h) k + D.halfLiftDefect d hd g h) =
      (2 : ℕ) •
        (g • D.halfLiftDefect d hd h k + D.halfLiftDefect d hd g (h * k))
  simp only [nsmul_add]
  rw [D.two_nsmul_halfLiftDefect, D.two_nsmul_halfLiftDefect,
    D.two_nsmul_halfLiftDefect]
  rw [show (2 : ℕ) • (g • D.halfLiftDefect d hd h k) =
      g • ((2 : ℕ) • D.halfLiftDefect d hd h k) by
        exact ((DistribSMul.toAddMonoidHom V g).map_nsmul _ _).symm]
  rw [D.two_nsmul_halfLiftDefect]
  simp only [liftDefect, smul_add, smul_sub, mul_smul, mul_assoc]
  abel

noncomputable def liftedTwoCocycle (hd : groupCohomology.IsCocycle₁ d) :
    NormalizedAddCocycle G V where
  toFun := D.halfLiftDefect d hd
  cocycle := D.halfLiftDefect_cocycle d hd
  one_left := D.halfLiftDefect_one_left d hd
  one_right := D.halfLiftDefect_one_right d hd

@[simp]
theorem liftedTwoCocycle_apply (hd : groupCohomology.IsCocycle₁ d) (g h : G) :
    D.liftedTwoCocycle d hd g h = D.halfLiftDefect d hd g h := rfl

theorem two_nsmul_liftedTwoCocycle (hd : groupCohomology.IsCocycle₁ d) (g h : G) :
    (2 : ℕ) • D.liftedTwoCocycle d hd g h = D.liftDefect d g h :=
  D.two_nsmul_halfLiftDefect d hd g h

theorem liftedTwoCocycle_not_isCoboundary
    (hd : groupCohomology.IsCocycle₁ d)
    (hd_not : ¬groupCohomology.IsCoboundary₁ d)
    (hV : ∀ F : G → V, groupCohomology.IsCocycle₁ F →
      groupCohomology.IsCoboundary₁ F) :
    ¬(D.liftedTwoCocycle d hd).IsCoboundary := by
  intro hc
  rcases hc with ⟨r, hr1, hr⟩
  let F : G → V := fun g ↦ D.liftedOneCochain d g - (2 : ℕ) • r g
  have hF : groupCohomology.IsCocycle₁ F := by
    intro g h
    change
      D.liftedOneCochain d (g * h) - (2 : ℕ) • r (g * h) =
        g • (D.liftedOneCochain d h - (2 : ℕ) • r h) +
          (D.liftedOneCochain d g - (2 : ℕ) • r g)
    have htwo := D.two_nsmul_liftedTwoCocycle d hd g h
    have hr' := hr g h
    simp only [liftDefect] at htwo
    rw [← hr'] at htwo
    simp only [nsmul_add, nsmul_sub] at htwo
    rw [show (2 : ℕ) • (g • r h) = g • ((2 : ℕ) • r h) by
      exact ((DistribSMul.toAddMonoidHom V g).map_nsmul _ _).symm] at htwo
    have hsum :
        (g • ((2 : ℕ) • r h) - (2 : ℕ) • r (g * h) + (2 : ℕ) • r g) +
            D.liftedOneCochain d (g * h) =
          D.liftedOneCochain d g + g • D.liftedOneCochain d h :=
      (eq_sub_iff_add_eq.mp htwo)
    rw [smul_sub]
    calc
      D.liftedOneCochain d (g * h) - (2 : ℕ) • r (g * h) =
          (g • ((2 : ℕ) • r h) - (2 : ℕ) • r (g * h) + (2 : ℕ) • r g +
              D.liftedOneCochain d (g * h)) -
            (g • ((2 : ℕ) • r h) + (2 : ℕ) • r g) := by abel
      _ = (D.liftedOneCochain d g + g • D.liftedOneCochain d h) -
            (g • ((2 : ℕ) • r h) + (2 : ℕ) • r g) := by rw [hsum]
      _ = (g • D.liftedOneCochain d h - g • ((2 : ℕ) • r h)) +
            (D.liftedOneCochain d g - (2 : ℕ) • r g) := by abel
  have hFred (g : G) : D.reduce (F g) = d g := by
    simp only [F, map_sub, reduce_liftedOneCochain, map_nsmul, D.exponent_two, sub_zero]
  rcases hV F hF with ⟨x, hx⟩
  apply hd_not
  refine ⟨D.reduce x, ?_⟩
  intro g
  rw [← hFred g, ← hx g, map_sub, D.reduce_smul]

end ModTwoLiftingData

end ConnesRigidity

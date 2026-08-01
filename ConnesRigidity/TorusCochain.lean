


import ConnesRigidity.ArithmeticCocycle
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Function.Floor









namespace ConnesRigidity

open Matrix
open scoped BigOperators
noncomputable section

abbrev SymplecticTorus := UnitAddTorus SymplecticIndex
abbrev RealSymplecticSpace := SymplecticIndex → ℝ

def integralMatrixReal (g : IntegralSymplecticGroup) :
    Matrix SymplecticIndex SymplecticIndex ℝ :=
  g.1.map (Int.castRingHom ℝ)

def realSymplecticAction (g : IntegralSymplecticGroup)
    (x : RealSymplecticSpace) : RealSymplecticSpace :=
  (integralMatrixReal g).mulVec x

def moduleMulVec {ι : Type*} [Fintype ι] {M : Type*} [AddCommGroup M]
    (A : Matrix ι ι ℤ) (v : ι → M) : ι → M :=
  fun i => ∑ j, A i j • v j

theorem moduleMulVec_add {ι : Type*} [Fintype ι] {M : Type*} [AddCommGroup M]
    (A : Matrix ι ι ℤ) (x y : ι → M) :
    moduleMulVec A (x + y) = moduleMulVec A x + moduleMulVec A y := by
  funext i
  simp [moduleMulVec, Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem moduleMulVec_mul {ι : Type*} [Fintype ι] {M : Type*} [AddCommGroup M]
    (A B : Matrix ι ι ℤ) (v : ι → M) :
    moduleMulVec (A * B) v = moduleMulVec A (moduleMulVec B v) := by
  funext i
  simp only [moduleMulVec, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum,
    mul_smul]
  rw [Finset.sum_comm]

theorem moduleMulVec_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Type*} [AddCommGroup M] (v : ι → M) :
    moduleMulVec (1 : Matrix ι ι ℤ) v = v := by
  funext i
  simp [moduleMulVec, Matrix.one_apply]

def torusLinearMap (g : IntegralSymplecticGroup) :
    SymplecticTorus →+ SymplecticTorus where
  toFun t := moduleMulVec g.1 t
  map_zero' := by
    funext i
    simp [moduleMulVec]
  map_add' := moduleMulVec_add g.1

theorem torusLinearMap_mul (g h : IntegralSymplecticGroup) (t : SymplecticTorus) :
    torusLinearMap (g * h) t = torusLinearMap g (torusLinearMap h t) := by
  exact moduleMulVec_mul g.1 h.1 t

theorem torusLinearMap_one (t : SymplecticTorus) :
    torusLinearMap 1 t = t := by
  exact moduleMulVec_one t

def torusActionHom : IntegralSymplecticGroup →* AddMonoid.End SymplecticTorus where
  toFun := torusLinearMap
  map_one' := by
    apply AddMonoidHom.ext
    intro t
    exact torusLinearMap_one t
  map_mul' g h := by
    apply AddMonoidHom.ext
    intro t
    exact torusLinearMap_mul g h t

instance : DistribMulAction IntegralSymplecticGroup SymplecticTorus :=
  DistribMulAction.compHom SymplecticTorus torusActionHom

@[simp]
theorem torus_smul_apply (g : IntegralSymplecticGroup)
    (t : SymplecticTorus) (i : SymplecticIndex) :
    (g • t) i = moduleMulVec g.1 t i :=
  rfl

def realToTorus (x : RealSymplecticSpace) : SymplecticTorus :=
  fun i => (x i : UnitAddCircle)

theorem realToTorus_add (x y : RealSymplecticSpace) :
    realToTorus (x + y) = realToTorus x + realToTorus y := by
  funext i
  exact AddCircle.coe_add 1 _ _

theorem realToTorus_neg (x : RealSymplecticSpace) :
    realToTorus (-x) = -realToTorus x := by
  funext i
  exact AddCircle.coe_neg 1

theorem realToTorus_sub (x y : RealSymplecticSpace) :
    realToTorus (x - y) = realToTorus x - realToTorus y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, realToTorus_add, realToTorus_neg]

theorem realToTorus_action (g : IntegralSymplecticGroup)
    (x : RealSymplecticSpace) :
    realToTorus (realSymplecticAction g x) = g • realToTorus x := by
  funext i
  let q : ℝ →+ UnitAddCircle :=
    QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
  change q (∑ j, (g.1 i j : ℝ) * x j) =
    ∑ j, g.1 i j • (x j : UnitAddCircle)
  rw [map_sum q]
  apply Finset.sum_congr rfl
  intro j _
  simp [q]

def torusSection (t : SymplecticTorus) : RealSymplecticSpace :=
  fun i => (AddCircle.equivIoc 1 0 (t i)).1

theorem realToTorus_torusSection (t : SymplecticTorus) :
    realToTorus (torusSection t) = t := by
  funext i
  exact AddCircle.coe_equivIoc

def realTranslationDefect (g : IntegralSymplecticGroup)
    (t : SymplecticTorus) : RealSymplecticSpace :=
  realSymplecticAction g (torusSection (g⁻¹ • t)) - torusSection t

theorem realToTorus_realTranslationDefect (g : IntegralSymplecticGroup)
    (t : SymplecticTorus) :
    realToTorus (realTranslationDefect g t) = 0 := by
  rw [realTranslationDefect, realToTorus_sub, realToTorus_action,
    realToTorus_torusSection, realToTorus_torusSection]
  simp

def translationDefect (g : IntegralSymplecticGroup)
    (t : SymplecticTorus) : IntegralLattice :=
  fun i => ⌊realTranslationDefect g t i⌋

theorem translationDefect_cast (g : IntegralSymplecticGroup)
    (t : SymplecticTorus) (i : SymplecticIndex) :
    (translationDefect g t i : ℝ) = realTranslationDefect g t i := by
  have hzero := congr_fun (realToTorus_realTranslationDefect g t) i
  change ((realTranslationDefect g t i : ℝ) : UnitAddCircle) = 0 at hzero
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  have hn' : (n : ℝ) = realTranslationDefect g t i := by
    simpa [zsmul_eq_mul] using hn
  rw [translationDefect, ← hn']
  norm_cast
  exact Int.floor_intCast n

def integralToReal (v : IntegralLattice) : RealSymplecticSpace :=
  fun i => (v i : ℝ)

theorem integralToReal_injective : Function.Injective integralToReal := by
  intro v w h
  funext i
  exact Int.cast_injective (congr_fun h i)

theorem integralToReal_add (v w : IntegralLattice) :
    integralToReal (v + w) = integralToReal v + integralToReal w := by
  funext i
  simp [integralToReal]

theorem integralToReal_action (g : IntegralSymplecticGroup)
    (v : IntegralLattice) :
    integralToReal (g • v) = realSymplecticAction g (integralToReal v) := by
  funext i
  change (↑(∑ j, g.1 i j * v j) : ℝ) =
    ∑ j, (g.1 i j : ℝ) * (v j : ℝ)
  exact_mod_cast rfl

theorem realSymplecticAction_add (g : IntegralSymplecticGroup)
    (x y : RealSymplecticSpace) :
    realSymplecticAction g (x + y) =
      realSymplecticAction g x + realSymplecticAction g y := by
  exact Matrix.mulVec_add _ _ _

theorem realSymplecticAction_sub (g : IntegralSymplecticGroup)
    (x y : RealSymplecticSpace) :
    realSymplecticAction g (x - y) =
      realSymplecticAction g x - realSymplecticAction g y := by
  exact Matrix.mulVec_sub _ _ _

theorem realSymplecticAction_mul (g h : IntegralSymplecticGroup)
    (x : RealSymplecticSpace) :
    realSymplecticAction (g * h) x =
      realSymplecticAction g (realSymplecticAction h x) := by
  change
    (((g.1 * h.1).map (Int.castRingHom ℝ)).mulVec x) =
      (g.1.map (Int.castRingHom ℝ)).mulVec
        ((h.1.map (Int.castRingHom ℝ)).mulVec x)
  rw [Matrix.map_mul]
  exact (Matrix.mulVec_mulVec x _ _).symm

theorem realSymplecticAction_one (x : RealSymplecticSpace) :
    realSymplecticAction 1 x = x := by
  change
    ((1 : Matrix SymplecticIndex SymplecticIndex ℤ).map
      (Int.castRingHom ℝ)).mulVec x = x
  rw [Matrix.map_one (Int.castRingHom ℝ) (map_zero _) (map_one _)]
  exact Matrix.one_mulVec x

theorem translationDefect_real_eq (g : IntegralSymplecticGroup)
    (t : SymplecticTorus) :
    integralToReal (translationDefect g t) =
      realTranslationDefect g t := by
  funext i
  exact translationDefect_cast g t i

theorem section_relation (g : IntegralSymplecticGroup)
    (t : SymplecticTorus) :
    realSymplecticAction g (torusSection (g⁻¹ • t)) =
      torusSection t + integralToReal (translationDefect g t) := by
  rw [translationDefect_real_eq, realTranslationDefect]
  abel

theorem translationDefect_cocycle (g h : IntegralSymplecticGroup)
    (t : SymplecticTorus) :
    translationDefect (g * h) t =
      translationDefect g t + g • translationDefect h (g⁻¹ • t) := by
  apply integralToReal_injective
  rw [integralToReal_add, integralToReal_action]
  rw [translationDefect_real_eq, translationDefect_real_eq,
    translationDefect_real_eq]
  simp only [realTranslationDefect]
  have hinv :
      (g * h)⁻¹ • t = h⁻¹ • (g⁻¹ • t) := by
    rw [_root_.mul_inv_rev, mul_smul]
  rw [hinv, realSymplecticAction_sub, realSymplecticAction_mul]
  abel

def modTwoTranslationDefect (g : IntegralSymplecticGroup)
    (t : SymplecticTorus) : ModTwoSpace :=
  reduceVector (translationDefect g t)

theorem modTwoTranslationDefect_cocycle (g h : IntegralSymplecticGroup)
    (t : SymplecticTorus) :
    modTwoTranslationDefect (g * h) t =
      modTwoTranslationDefect g t +
        g • modTwoTranslationDefect h (g⁻¹ • t) := by
  simp only [modTwoTranslationDefect]
  rw [translationDefect_cocycle,
    map_add, reduceVector_smul]

def realSymplecticForm (x y : RealSymplecticSpace) : ℝ :=
  ∑ i : Fin 2, (x (Sum.inl i) * y (Sum.inr i) -
    x (Sum.inr i) * y (Sum.inl i))

theorem realSymplecticForm_eq_dotProduct
    (x y : RealSymplecticSpace) :
    realSymplecticForm x y =
      -dotProduct x ((Matrix.J (Fin 2) ℝ).mulVec y) := by
  simp [realSymplecticForm, Matrix.J, Matrix.mulVec, dotProduct]
  ring

def realSymplecticGroupMap :
    IntegralSymplecticGroup →* Matrix.symplecticGroup (Fin 2) ℝ where
  toFun g :=
    ⟨integralMatrixReal g,
      SymplecticGroup.map_mem g.2 (Int.castRingHom ℝ)⟩
  map_one' := by
    apply Subtype.ext
    exact Matrix.map_one (Int.castRingHom ℝ) (map_zero _) (map_one _)
  map_mul' g h := by
    apply Subtype.ext
    exact Matrix.map_mul

theorem realSymplecticForm_action
    (g : IntegralSymplecticGroup) (x y : RealSymplecticSpace) :
    realSymplecticForm (realSymplecticAction g x)
      (realSymplecticAction g y) = realSymplecticForm x y := by
  rw [realSymplecticForm_eq_dotProduct, realSymplecticForm_eq_dotProduct]
  let gr := realSymplecticGroupMap g
  change -dotProduct (gr.1.mulVec x)
      ((Matrix.J (Fin 2) ℝ).mulVec (gr.1.mulVec y)) =
    -dotProduct x ((Matrix.J (Fin 2) ℝ).mulVec y)
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [SymplecticGroup.mem_iff'.mp gr.2]
  rw [← Matrix.dotProduct_mulVec]

theorem realSymplecticAction_inv (g : IntegralSymplecticGroup)
    (x : RealSymplecticSpace) :
    realSymplecticAction g⁻¹ (realSymplecticAction g x) = x := by
  rw [← realSymplecticAction_mul, inv_mul_cancel]
  exact realSymplecticAction_one x

theorem realSymplecticForm_action_left
    (g : IntegralSymplecticGroup) (x y : RealSymplecticSpace) :
    realSymplecticForm (realSymplecticAction g x) y =
      realSymplecticForm x (realSymplecticAction g⁻¹ y) := by
  rw [← realSymplecticForm_action g x (realSymplecticAction g⁻¹ y)]
  rw [← realSymplecticAction_mul, mul_inv_cancel]
  rw [realSymplecticAction_one]

theorem realSymplecticForm_add_left
    (x y z : RealSymplecticSpace) :
    realSymplecticForm (x + y) z =
      realSymplecticForm x z + realSymplecticForm y z := by
  simp [realSymplecticForm, add_mul, Finset.sum_add_distrib]
  ring

theorem realSymplecticForm_add_right
    (x y z : RealSymplecticSpace) :
    realSymplecticForm x (y + z) =
      realSymplecticForm x y + realSymplecticForm x z := by
  simp [realSymplecticForm, mul_add, Finset.sum_add_distrib]
  ring

theorem realSymplecticForm_sub_left
    (x y z : RealSymplecticSpace) :
    realSymplecticForm (x - y) z =
      realSymplecticForm x z - realSymplecticForm y z := by
  simp [realSymplecticForm, sub_mul, Finset.sum_sub_distrib]
  ring

theorem realSymplecticForm_sub_right
    (x y z : RealSymplecticSpace) :
    realSymplecticForm x (y - z) =
      realSymplecticForm x y - realSymplecticForm x z := by
  simp [realSymplecticForm, mul_sub, Finset.sum_sub_distrib]
  ring

theorem realSymplecticForm_integral
    (v w : IntegralLattice) :
    realSymplecticForm (integralToReal v) (integralToReal w) =
      (∑ i : Fin 2, (v (Sum.inl i) * w (Sum.inr i) -
        v (Sum.inr i) * w (Sum.inl i)) : ℤ) := by
  simp [realSymplecticForm, integralToReal]

def integralSymplecticForm (v w : IntegralLattice) : ℤ :=
  ∑ i : Fin 2, (v (Sum.inl i) * w (Sum.inr i) -
    v (Sum.inr i) * w (Sum.inl i))

theorem realSymplecticForm_integral' (v w : IntegralLattice) :
    realSymplecticForm (integralToReal v) (integralToReal w) =
      integralSymplecticForm v w := by
  exact realSymplecticForm_integral v w

theorem integralSymplecticForm_modTwo (v w : IntegralLattice) :
    (integralSymplecticForm v w : ZMod 2) =
      modTwoSymplecticForm (reduceVector v) (reduceVector w) := by
  simp [integralSymplecticForm, modTwoSymplecticForm]
  simp only [CharTwo.sub_eq_add]
  abel

def liftedQuadraticCocycle (g : IntegralSymplecticGroup) : IntegralLattice :=
  liftVector (integralQuadraticCocycle g)

theorem two_nsmul_integralTwoCocycle (g h : IntegralSymplecticGroup) :
    (2 : ℕ) • integralSymplecticCocycleInput.twoCocycle g h =
      liftedQuadraticCocycle g + g • liftedQuadraticCocycle h -
        liftedQuadraticCocycle (g * h) := by
  exact symplecticModTwoLiftingData.two_nsmul_liftedTwoCocycle
    integralQuadraticCocycle integralQuadraticCocycle_isCocycle g h

theorem integralToReal_sub (v w : IntegralLattice) :
    integralToReal (v - w) = integralToReal v - integralToReal w := by
  funext i
  simp [integralToReal]

theorem integralToReal_two_nsmul (v : IntegralLattice) :
  integralToReal ((2 : ℕ) • v) = (2 : ℝ) • integralToReal v := by
  funext i
  simp [integralToReal]

def characterExponent (v : IntegralLattice) (t : SymplecticTorus) : ℝ :=
  realSymplecticForm (integralToReal v) (torusSection t)

def wExponent (g : IntegralSymplecticGroup) (t : SymplecticTorus) : ℝ :=
  realSymplecticForm (integralToReal (liftedQuadraticCocycle g))
    (torusSection t) / 2

theorem wExponent_coboundary (g h : IntegralSymplecticGroup)
    (t : SymplecticTorus) :
    wExponent g t + wExponent h (g⁻¹ • t) - wExponent (g * h) t =
      characterExponent (integralSymplecticCocycleInput.twoCocycle g h) t +
        (integralSymplecticForm
          (g • liftedQuadraticCocycle h) (translationDefect g t) : ℝ) / 2 := by
  let ag := liftedQuadraticCocycle g
  let ah := liftedQuadraticCocycle h
  let agh := liftedQuadraticCocycle (g * h)
  let c := integralSymplecticCocycleInput.twoCocycle g h
  let ng := translationDefect g t
  have hinv :
      realSymplecticForm (integralToReal ah) (torusSection (g⁻¹ • t)) =
        realSymplecticForm (integralToReal (g • ah))
          (realSymplecticAction g (torusSection (g⁻¹ • t))) := by
    rw [integralToReal_action, realSymplecticForm_action]
  have hsection :
      realSymplecticAction g (torusSection (g⁻¹ • t)) =
        torusSection t + integralToReal ng :=
    section_relation g t
  have hcInt : (2 : ℕ) • c = ag + g • ah - agh :=
    two_nsmul_integralTwoCocycle g h
  have hcReal :
      (2 : ℝ) • integralToReal c =
        integralToReal ag + integralToReal (g • ah) - integralToReal agh := by
    have hc := congrArg integralToReal hcInt
    rw [integralToReal_two_nsmul, integralToReal_sub,
      integralToReal_add] at hc
    exact hc
  have hcForm :
      (2 : ℝ) * realSymplecticForm (integralToReal c) (torusSection t) =
        realSymplecticForm
          (integralToReal ag + integralToReal (g • ah) - integralToReal agh)
          (torusSection t) := by
    rw [← hcReal]
    simp [realSymplecticForm]
    ring
  simp only [wExponent, characterExponent]
  change
    realSymplecticForm (integralToReal ag) (torusSection t) / 2 +
        realSymplecticForm (integralToReal ah) (torusSection (g⁻¹ • t)) / 2 -
        realSymplecticForm (integralToReal agh) (torusSection t) / 2 =
      realSymplecticForm (integralToReal c) (torusSection t) +
        (integralSymplecticForm (g • ah) ng : ℝ) / 2
  rw [hinv, hsection, realSymplecticForm_add_right,
    ← realSymplecticForm_integral']
  rw [realSymplecticForm_sub_left, realSymplecticForm_add_left] at hcForm
  linarith

def bitInt (b : ZMod 2) : ℤ :=
  b.val

@[simp]
theorem bitInt_cast (b : ZMod 2) : (bitInt b : ZMod 2) = b := by
  exact_mod_cast ZMod.natCast_zmod_val b

def ellInteger (g : IntegralSymplecticGroup) (t : SymplecticTorus) : ℤ :=
  bitInt (standardQuadraticForm (modTwoTranslationDefect g t))

def kInteger (g : IntegralSymplecticGroup) (t : SymplecticTorus) : ℤ :=
  bitInt (modTwoSymplecticForm (modTwoTranslationDefect g t)
    (integralQuadraticCocycle g))

def correctionExponent (g : IntegralSymplecticGroup)
    (t : SymplecticTorus) : ℝ :=
  ((ellInteger g t + kInteger g t : ℤ) : ℝ) / 2 +
    realSymplecticForm (torusSection t)
      (integralToReal (translationDefect g t)) / 2

theorem correctionParityIdentity (g h : IntegralSymplecticGroup)
    (A C : ModTwoSpace) :
    standardQuadraticForm A + standardQuadraticForm C -
          standardQuadraticForm (A + g • C) +
        (modTwoSymplecticForm A (integralQuadraticCocycle g) +
          modTwoSymplecticForm C (integralQuadraticCocycle h) -
          modTwoSymplecticForm (A + g • C)
            (integralQuadraticCocycle (g * h))) +
        modTwoSymplecticForm A (g • C) =
      modTwoSymplecticForm A (g • integralQuadraticCocycle h) := by
  have hp :=
    integralQuadraticCocycle_defining_identity g (g • C)
  have hd := integralQuadraticCocycle_isCocycle g h
  simp only [inv_smul_smul] at hp
  rw [hd, standardQuadraticForm_add]
  rw [modTwoSymplecticForm_add_left A (g • C)
    (g • integralQuadraticCocycle h + integralQuadraticCocycle g)]
  rw [modTwoSymplecticForm_add_right A
    (g • integralQuadraticCocycle h) (integralQuadraticCocycle g)]
  rw [modTwoSymplecticForm_add_right (g • C)
    (g • integralQuadraticCocycle h) (integralQuadraticCocycle g)]
  have hinv :
      modTwoSymplecticForm (g • C) (g • integralQuadraticCocycle h) =
        modTwoSymplecticForm C (integralQuadraticCocycle h) := by
    rw [← reducedSymplecticHom_smul g C,
      ← reducedSymplecticHom_smul g (integralQuadraticCocycle h)]
    exact modTwoSymplecticForm_smul (reducedSymplecticHom g) _ _
  rw [hinv]
  have hsym (x y : ModTwoSpace) :
      modTwoSymplecticForm x y = modTwoSymplecticForm y x := by
    simp [modTwoSymplecticForm, mul_comm]
    abel
  rw [hsym (g • C) (integralQuadraticCocycle g)]
  simp only [CharTwo.sub_eq_add]
  have hpzero :
      standardQuadraticForm C + standardQuadraticForm (g • C) +
        modTwoSymplecticForm (integralQuadraticCocycle g) (g • C) = 0 := by
    rw [hp]
    exact CharTwo.add_self_eq_zero _
  abel_nf at hpzero ⊢
  have htwo (x : ZMod 2) : (2 : ℤ) • x = 0 := by
    rw [zsmul_eq_mul]
    have h2 : ((2 : ℤ) : ZMod 2) = 0 := by decide
    rw [h2, zero_mul]
  simp_rw [htwo]
  simp only [zero_add]
  linear_combination hpzero

def correctionInteger (g h : IntegralSymplecticGroup)
    (t : SymplecticTorus) : ℤ :=
  ellInteger g t + ellInteger h (g⁻¹ • t) - ellInteger (g * h) t +
    (kInteger g t + kInteger h (g⁻¹ • t) - kInteger (g * h) t) +
    integralSymplecticForm (translationDefect g t)
      (g • translationDefect h (g⁻¹ • t))

theorem correctionInteger_modTwo (g h : IntegralSymplecticGroup)
    (t : SymplecticTorus) :
    (correctionInteger g h t : ZMod 2) =
      modTwoSymplecticForm (modTwoTranslationDefect g t)
        (g • integralQuadraticCocycle h) := by
  let A := modTwoTranslationDefect g t
  let C := modTwoTranslationDefect h (g⁻¹ • t)
  have hm :
      modTwoTranslationDefect (g * h) t = A + g • C :=
    modTwoTranslationDefect_cocycle g h t
  have homega :
      (integralSymplecticForm (translationDefect g t)
        (g • translationDefect h (g⁻¹ • t)) : ZMod 2) =
        modTwoSymplecticForm A (g • C) := by
    rw [integralSymplecticForm_modTwo, reduceVector_smul]
    rfl
  simp only [correctionInteger, ellInteger, kInteger]
  rw [hm]
  push_cast
  rw [homega]
  simp only [bitInt_cast]
  dsimp [A, C]
  exact correctionParityIdentity g h A C

def yExponent (g : IntegralSymplecticGroup)
    (t : SymplecticTorus) : ℝ :=
  realSymplecticForm (torusSection t)
    (integralToReal (translationDefect g t)) / 2

theorem yExponent_coboundary (g h : IntegralSymplecticGroup)
    (t : SymplecticTorus) :
    yExponent g t + yExponent h (g⁻¹ • t) - yExponent (g * h) t =
      (integralSymplecticForm (translationDefect g t)
        (g • translationDefect h (g⁻¹ • t)) : ℝ) / 2 := by
  let ng := translationDefect g t
  let nh := translationDefect h (g⁻¹ • t)
  let s := torusSection t
  let s' := torusSection (g⁻¹ • t)
  have hngh :
      integralToReal (translationDefect (g * h) t) =
        integralToReal ng + integralToReal (g • nh) := by
    rw [translationDefect_cocycle, integralToReal_add]
  have hinv :
      realSymplecticForm s' (integralToReal nh) =
        realSymplecticForm (realSymplecticAction g s')
          (integralToReal (g • nh)) := by
    rw [integralToReal_action, realSymplecticForm_action]
  have hsection :
      realSymplecticAction g s' = s + integralToReal ng :=
    section_relation g t
  simp only [yExponent]
  change
    realSymplecticForm s (integralToReal ng) / 2 +
        realSymplecticForm s' (integralToReal nh) / 2 -
        realSymplecticForm s
          (integralToReal (translationDefect (g * h) t)) / 2 =
      (integralSymplecticForm ng (g • nh) : ℝ) / 2
  rw [hinv, hsection, hngh, realSymplecticForm_add_left,
    realSymplecticForm_add_right, ← realSymplecticForm_integral']
  ring

theorem correctionExponent_coboundary (g h : IntegralSymplecticGroup)
    (t : SymplecticTorus) :
    correctionExponent g t + correctionExponent h (g⁻¹ • t) -
        correctionExponent (g * h) t =
      (correctionInteger g h t : ℝ) / 2 := by
  have hy := yExponent_coboundary g h t
  simp only [correctionExponent, yExponent] at hy ⊢
  simp only [correctionInteger]
  push_cast
  linarith

theorem totalError_modTwo (g h : IntegralSymplecticGroup)
    (t : SymplecticTorus) :
    ((correctionInteger g h t +
        integralSymplecticForm (g • liftedQuadraticCocycle h)
          (translationDefect g t) : ℤ) : ZMod 2) = 0 := by
  rw [Int.cast_add, correctionInteger_modTwo,
    integralSymplecticForm_modTwo, reduceVector_smul,
    show reduceVector (liftedQuadraticCocycle h) =
      integralQuadraticCocycle h by
        exact reduceVector_liftVector _]
  let A := modTwoTranslationDefect g t
  let E := g • integralQuadraticCocycle h
  change modTwoSymplecticForm A E + modTwoSymplecticForm E A = 0
  have hsym : modTwoSymplecticForm E A = modTwoSymplecticForm A E := by
    simp [modTwoSymplecticForm, mul_comm]
    abel
  rw [hsym]
  exact CharTwo.add_self_eq_zero _

def totalCochainExponent (g : IntegralSymplecticGroup)
    (t : SymplecticTorus) : ℝ :=
  wExponent g t + correctionExponent g t

def torusCochainPhase (g : IntegralSymplecticGroup)
    (t : SymplecticTorus) : UnitAddCircle :=
  (totalCochainExponent g t : UnitAddCircle)

def latticeCharacterPhase (v : IntegralLattice)
    (t : SymplecticTorus) : UnitAddCircle :=
  (characterExponent v t : UnitAddCircle)

theorem torusCochainPhase_coboundary (g h : IntegralSymplecticGroup)
    (t : SymplecticTorus) :
    torusCochainPhase g t + torusCochainPhase h (g⁻¹ • t) -
        torusCochainPhase (g * h) t =
      latticeCharacterPhase (integralSymplecticCocycleInput.twoCocycle g h) t := by
  let r : ℤ :=
    integralSymplecticForm (g • liftedQuadraticCocycle h)
      (translationDefect g t)
  let q : ℤ := correctionInteger g h t
  have hw := wExponent_coboundary g h t
  have hc := correctionExponent_coboundary g h t
  have hreal :
      totalCochainExponent g t + totalCochainExponent h (g⁻¹ • t) -
          totalCochainExponent (g * h) t -
          characterExponent
            (integralSymplecticCocycleInput.twoCocycle g h) t =
        ((q + r : ℤ) : ℝ) / 2 := by
    simp only [totalCochainExponent]
    change _ = (((correctionInteger g h t + r : ℤ) : ℝ) / 2)
    push_cast
    linarith
  have hmod : ((q + r : ℤ) : ZMod 2) = 0 := by
    exact totalError_modTwo g h t
  have hdiv : (2 : ℤ) ∣ q + r :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (q + r) 2).mp hmod
  obtain ⟨k, hk⟩ := hdiv
  have hrealInt :
      totalCochainExponent g t + totalCochainExponent h (g⁻¹ • t) -
          totalCochainExponent (g * h) t -
          characterExponent
            (integralSymplecticCocycleInput.twoCocycle g h) t =
        (k : ℝ) := by
    rw [hreal, hk]
    push_cast
    ring
  apply sub_eq_zero.mp
  change
    ((totalCochainExponent g t + totalCochainExponent h (g⁻¹ • t) -
      totalCochainExponent (g * h) t -
      characterExponent
        (integralSymplecticCocycleInput.twoCocycle g h) t : ℝ) :
      UnitAddCircle) = 0
  rw [hrealInt]
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨k, by simp [zsmul_eq_mul]⟩

def torusCochain (g : IntegralSymplecticGroup)
    (t : SymplecticTorus) : Circle :=
  AddCircle.toCircle (torusCochainPhase g t)

def latticeCharacter (v : IntegralLattice)
    (t : SymplecticTorus) : Circle :=
  AddCircle.toCircle (latticeCharacterPhase v t)


theorem latticeCharacter_add (v w : IntegralLattice)
    (t : SymplecticTorus) :
    latticeCharacter (v + w) t =
      latticeCharacter v t * latticeCharacter w t := by
  have hr :
      characterExponent (v + w) t =
        characterExponent v t + characterExponent w t := by
    rw [characterExponent, characterExponent, characterExponent,
      integralToReal_add, realSymplecticForm_add_left]
  rw [latticeCharacter, latticeCharacter, latticeCharacter,
    latticeCharacterPhase, latticeCharacterPhase, latticeCharacterPhase,
    hr, AddCircle.coe_add, AddCircle.toCircle_add]

theorem torusCochain_coboundary (g h : IntegralSymplecticGroup)
    (t : SymplecticTorus) :
    torusCochain g t * torusCochain h (g⁻¹ • t) *
        (torusCochain (g * h) t)⁻¹ =
      latticeCharacter (integralSymplecticCocycleInput.twoCocycle g h) t := by
  have hphase := congrArg AddCircle.toCircle
    (torusCochainPhase_coboundary g h t)
  simpa only [torusCochain, latticeCharacter, sub_eq_add_neg,
    AddCircle.toCircle_add, AddCircle.toCircle_neg] using hphase

theorem torusCochain_one (t : SymplecticTorus) :
    torusCochain 1 t = 1 := by
  have hphase := torusCochainPhase_coboundary 1 1 t
  have hc0 :
      integralSymplecticCocycleInput.twoCocycle 1 1 = 0 :=
    integralSymplecticCocycleInput.twoCocycle.one_left 1
  have hzero : latticeCharacterPhase (0 : IntegralLattice) t = 0 := by
    have hzreal : characterExponent (0 : IntegralLattice) t = 0 := by
      simp [characterExponent, realSymplecticForm, integralToReal]
    rw [latticeCharacterPhase, hzreal]
    rfl
  simp only [one_mul, inv_one, one_smul] at hphase
  rw [hc0, hzero] at hphase
  have hphase0 : torusCochainPhase 1 t = 0 := by
    simpa using hphase
  rw [torusCochain, hphase0, AddCircle.toCircle_zero]




theorem measurable_torusSection : Measurable torusSection := by
  let e := UnitAddTorus.measurableEquivPiIoc
    (fun _ : SymplecticIndex => (0 : ℝ))
  have h : Measurable (fun t : SymplecticTorus => (e t).1) :=
    measurable_subtype_coe.comp e.measurable
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply i).comp h


theorem continuous_torus_smul (g : IntegralSymplecticGroup) :
    Continuous (fun t : SymplecticTorus => g • t) := by
  apply continuous_pi
  intro i
  simp only [torus_smul_apply, moduleMulVec]
  fun_prop

theorem measurable_torus_smul (g : IntegralSymplecticGroup) :
    Measurable (fun t : SymplecticTorus => g • t) :=
  (continuous_torus_smul g).measurable


theorem continuous_realSymplecticAction (g : IntegralSymplecticGroup) :
    Continuous (realSymplecticAction g) := by
  apply continuous_pi
  intro i
  simp only [realSymplecticAction, integralMatrixReal, Matrix.mulVec, dotProduct]
  fun_prop

theorem measurable_realTranslationDefect (g : IntegralSymplecticGroup) :
    Measurable (realTranslationDefect g) := by
  have harg : Measurable (fun t : SymplecticTorus =>
      torusSection (g⁻¹ • t)) :=
    measurable_torusSection.comp (measurable_torus_smul g⁻¹)
  have hleft : Measurable (fun t : SymplecticTorus =>
      realSymplecticAction g (torusSection (g⁻¹ • t))) :=
    (continuous_realSymplecticAction g).measurable.comp harg
  exact hleft.sub measurable_torusSection

theorem measurable_translationDefect (g : IntegralSymplecticGroup) :
    Measurable (translationDefect g) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_realTranslationDefect g).eval.floor

theorem measurable_modTwoTranslationDefect (g : IntegralSymplecticGroup) :
    Measurable (modTwoTranslationDefect g) :=
  (measurable_of_countable reduceVector).comp (measurable_translationDefect g)

theorem measurable_realSymplecticForm_comp
    {α : Type*} [MeasurableSpace α]
    {f h : α → RealSymplecticSpace}
    (hf : Measurable f) (hh : Measurable h) :
    Measurable (fun x => realSymplecticForm (f x) (h x)) := by
  simp only [realSymplecticForm]
  fun_prop

theorem measurable_characterExponent (v : IntegralLattice) :
    Measurable (characterExponent v) :=
  measurable_realSymplecticForm_comp measurable_const measurable_torusSection

theorem measurable_wExponent (g : IntegralSymplecticGroup) :
    Measurable (wExponent g) :=
  (measurable_realSymplecticForm_comp measurable_const measurable_torusSection).div_const _

theorem measurable_ellInteger (g : IntegralSymplecticGroup) :
    Measurable (ellInteger g) := by
  exact (measurable_of_finite
    (fun m : ModTwoSpace => bitInt (standardQuadraticForm m))).comp
      (measurable_modTwoTranslationDefect g)

theorem measurable_kInteger (g : IntegralSymplecticGroup) :
    Measurable (kInteger g) := by
  exact (measurable_of_finite
    (fun m : ModTwoSpace => bitInt
      (modTwoSymplecticForm m (integralQuadraticCocycle g)))).comp
      (measurable_modTwoTranslationDefect g)

theorem measurable_integralToReal_translationDefect
    (g : IntegralSymplecticGroup) :
    Measurable (fun t => integralToReal (translationDefect g t)) :=
  (measurable_of_countable integralToReal).comp
    (measurable_translationDefect g)

theorem measurable_yExponent (g : IntegralSymplecticGroup) :
    Measurable (yExponent g) :=
  (measurable_realSymplecticForm_comp measurable_torusSection
    (measurable_integralToReal_translationDefect g)).div_const _

theorem measurable_correctionExponent (g : IntegralSymplecticGroup) :
    Measurable (correctionExponent g) := by
  have hiInt : Measurable (fun t => ellInteger g t + kInteger g t) :=
    (measurable_ellInteger g).add (measurable_kInteger g)
  have hi : Measurable (fun t =>
      ((ellInteger g t + kInteger g t : ℤ) : ℝ)) :=
    (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp hiInt
  exact hi.div_const _ |>.add (measurable_yExponent g)

theorem measurable_totalCochainExponent (g : IntegralSymplecticGroup) :
    Measurable (totalCochainExponent g) :=
  (measurable_wExponent g).add (measurable_correctionExponent g)

theorem measurable_torusCochainPhase (g : IntegralSymplecticGroup) :
    Measurable (torusCochainPhase g) :=
  (AddCircle.continuous_mk' (1 : ℝ)).measurable.comp
    (measurable_totalCochainExponent g)


theorem measurable_torusCochain_complex (g : IntegralSymplecticGroup) :
    Measurable (fun t => (torusCochain g t : ℂ)) := by
  have hc : Continuous (fun x : UnitAddCircle =>
      (AddCircle.toCircle x : ℂ)) :=
    continuous_subtype_val.comp AddCircle.continuous_toCircle
  exact hc.measurable.comp (measurable_torusCochainPhase g)





def symplecticFourierIndex : IntegralLattice ≃+ IntegralLattice where
  toFun v
    | Sum.inl i => -v (Sum.inr i)
    | Sum.inr i => v (Sum.inl i)
  invFun v
    | Sum.inl i => v (Sum.inr i)
    | Sum.inr i => -v (Sum.inl i)
  left_inv := by
    intro v
    funext i
    rcases i with i | i <;> simp
  right_inv := by
    intro v
    funext i
    rcases i with i | i <;> simp
  map_add' := by
    intro v w
    funext i
    rcases i with i | i
    · dsimp
      abel
    · rfl

theorem latticeCharacterPhase_eq_sum
    (v : IntegralLattice) (t : SymplecticTorus) :
    latticeCharacterPhase v t =
      ∑ i : SymplecticIndex, symplecticFourierIndex v i • t i := by
  simp only [latticeCharacterPhase, characterExponent, realSymplecticForm,
    symplecticFourierIndex, AddEquiv.coe_mk,
    Equiv.coe_fn_mk]
  let q : ℝ →+ UnitAddCircle :=
    QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
  change q (∑ i : Fin 2,
      (integralToReal v (Sum.inl i) * torusSection t (Sum.inr i) -
        integralToReal v (Sum.inr i) * torusSection t (Sum.inl i))) = _
  rw [map_sum]
  rw [← Finset.univ_disjSum_univ]
  simp only [Finset.sum_disjSum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have ht (j : SymplecticIndex) :
      q (torusSection t j) = t j := by
    exact congrFun (realToTorus_torusSection t) j
  rw [map_sub]
  have hx :
      q (integralToReal v (Sum.inl i) * torusSection t (Sum.inr i)) =
        v (Sum.inl i) • t (Sum.inr i) := by
    rw [← ht]
    rw [← map_zsmul]
    simp [integralToReal, zsmul_eq_mul]
  have hy :
      q (integralToReal v (Sum.inr i) * torusSection t (Sum.inl i)) =
        v (Sum.inr i) • t (Sum.inl i) := by
    rw [← ht]
    rw [← map_zsmul]
    simp [integralToReal, zsmul_eq_mul]
  rw [hx, hy, neg_zsmul]
  abel



theorem latticeCharacter_coe_eq_mFourier
    (v : IntegralLattice) (t : SymplecticTorus) :
    (latticeCharacter v t : ℂ) =
      UnitAddTorus.mFourier (symplecticFourierIndex v) t := by
  rw [latticeCharacter, latticeCharacterPhase_eq_sum]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    fourier_apply]
  have hc :
      AddCircle.toCircle
          (∑ i : SymplecticIndex, symplecticFourierIndex v i • t i) =
        ∏ i : SymplecticIndex,
          AddCircle.toCircle (symplecticFourierIndex v i • t i) := by
    classical
    induction (Finset.univ : Finset SymplecticIndex) using Finset.induction_on with
    | empty => simp [AddCircle.toCircle_zero]
    | @insert a s ha ih =>
        simp [ha, ih, AddCircle.toCircle_add]
  simpa using congrArg ((↑) : Circle → ℂ) hc

theorem characterExponent_action
    (g : IntegralSymplecticGroup) (v : IntegralLattice)
    (t : SymplecticTorus) :
    characterExponent (g • v) t =
      characterExponent v (g⁻¹ • t) -
        (integralSymplecticForm (g • v) (translationDefect g t) : ℝ) := by
  have hs := section_relation g t
  have hs' :
      torusSection t =
        realSymplecticAction g (torusSection (g⁻¹ • t)) -
          integralToReal (translationDefect g t) := by
    rw [hs]
    abel
  rw [characterExponent, characterExponent, hs',
    realSymplecticForm_sub_right, integralToReal_action,
    realSymplecticForm_action]
  rw [← integralToReal_action, realSymplecticForm_integral']


theorem latticeCharacter_action
    (g : IntegralSymplecticGroup) (v : IntegralLattice)
    (t : SymplecticTorus) :
    latticeCharacter (g • v) t =
      latticeCharacter v (g⁻¹ • t) := by
  have hr := characterExponent_action g v t
  have hp :
      latticeCharacterPhase (g • v) t =
        latticeCharacterPhase v (g⁻¹ • t) := by
    simp only [latticeCharacterPhase]
    rw [hr]
    let q : ℝ →+ UnitAddCircle :=
      QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
    change q (characterExponent v (g⁻¹ • t) -
        (integralSymplecticForm (g • v) (translationDefect g t) : ℝ)) =
      q (characterExponent v (g⁻¹ • t))
    rw [map_sub]
    have hz :
        q (integralSymplecticForm (g • v) (translationDefect g t) : ℝ) = 0 := by
      apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
      exact ⟨integralSymplecticForm (g • v) (translationDefect g t), by
        simp [zsmul_eq_mul]⟩
    rw [hz, sub_zero]
  exact congrArg AddCircle.toCircle hp

theorem measurable_latticeCharacter_complex (v : IntegralLattice) :
    Measurable (fun t : SymplecticTorus => (latticeCharacter v t : ℂ)) := by
  have hm :=
    (UnitAddTorus.mFourier (symplecticFourierIndex v)).continuous.measurable
  convert hm using 1
  funext t
  exact latticeCharacter_coe_eq_mFourier v t

end

end ConnesRigidity

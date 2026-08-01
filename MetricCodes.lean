import SpherePacking

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace MetricCodes

instance numeralTwoAtLeast : Nat.AtLeastTwo 2 := ⟨by decide⟩

abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)

abbrev BinaryWord (n : ℕ) := Fin n → Bool

def hammingDist {n : ℕ} (x y : BinaryWord n) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ y i).card

@[simp] theorem hammingDist_self {n : ℕ} (x : BinaryWord n) :
    hammingDist x x = 0 := by
  simp [hammingDist]

def binaryWeight {n : ℕ} (x : BinaryWord n) : ℕ :=
  (Finset.univ.filter fun i => x i = true).card

def IsBinaryCode {n : ℕ} (d : ℕ) (C : Finset (BinaryWord n)) : Prop :=
  ∀ ⦃x⦄, x ∈ C → ∀ ⦃y⦄, y ∈ C → x ≠ y → d ≤ hammingDist x y

abbrev JohnsonSphere (n w : ℕ) :=
  {x : BinaryWord n // binaryWeight x = w}

def hammingCorrelation {n : ℕ} (x y : BinaryWord n) : ℝ :=
  1 - 2 * (hammingDist x y : ℝ) / (n : ℝ)

@[simp] theorem hammingCorrelation_self {n : ℕ} (x : BinaryWord n) :
    hammingCorrelation x x = 1 := by
  simp [hammingCorrelation]

theorem hammingCorrelation_le_of_dist_le
    {n d : ℕ} (hn : 0 < n) {x y : BinaryWord n}
    (hd : d ≤ hammingDist x y) :
    hammingCorrelation x y ≤ 1 - 2 * (d : ℝ) / (n : ℝ) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hd' : (d : ℝ) ≤ (hammingDist x y : ℝ) := by
    exact_mod_cast hd
  unfold hammingCorrelation
  have hdiv :
      2 * (d : ℝ) / (n : ℝ) ≤
        2 * (hammingDist x y : ℝ) / (n : ℝ) := by
    exact (div_le_div_iff_of_pos_right hn').2 (by linarith)
  linarith

def sphericalEntropy (u : ℝ) : ℝ :=
  (1 + u) * Real.logb 2 (1 + u) - u * Real.logb 2 u

@[simp] theorem sphericalEntropy_zero : sphericalEntropy 0 = 0 := by
  simp [sphericalEntropy]

theorem sphericalEntropy_eq_log_add {u : ℝ} (hu : 0 < u) :
    sphericalEntropy u =
      Real.logb 2 (1 + u) +
        u * Real.logb 2 ((1 + u) / u) := by
  have hu' : u ≠ 0 := hu.ne'
  have hone : 1 + u ≠ 0 := by linarith
  rw [Real.logb_div hone hu']
  unfold sphericalEntropy
  ring

def binaryEntropy (u : ℝ) : ℝ :=
  -(u * Real.logb 2 u) -
    (1 - u) * Real.logb 2 (1 - u)

@[simp] theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy]

theorem binaryEntropy_nonneg {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1) :
    0 ≤ binaryEntropy u := by
  have h₁ : Real.logb 2 u ≤ 0 :=
    Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) hu hu'
  have h₂ : Real.logb 2 (1 - u) ≤ 0 :=
    Real.logb_nonpos (by norm_num : (1 : ℝ) < 2)
      (by linarith) (by linarith)
  unfold binaryEntropy
  have hleft : u * Real.logb 2 u ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hu h₁
  have hright : (1 - u) * Real.logb 2 (1 - u) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) h₂
  linarith

def Gamma (a b : ℝ) : ℝ :=
  ((a - b) * (1 + a + b)) /
    ((1 + 2 * a) * Real.sqrt (a * (1 + a)))

theorem Gamma_eq_sub (a b : ℝ) :
    Gamma a b =
      (a * (1 + a) - b * (1 + b)) /
        ((1 + 2 * a) * Real.sqrt (a * (1 + a))) := by
  unfold Gamma
  congr 1
  ring

def classicalThreshold (s : ℝ) : ℝ :=
  (1 / Real.sqrt (1 - s ^ 2) - 1) / 2

@[simp] theorem classicalThreshold_zero : classicalThreshold 0 = 0 := by
  simp [classicalThreshold]

theorem classicalThreshold_pos {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    0 < classicalThreshold s := by
  have hrad : 0 < 1 - s ^ 2 := by nlinarith
  have hsqrt : 0 < Real.sqrt (1 - s ^ 2) := Real.sqrt_pos.2 hrad
  have hsqrt' : Real.sqrt (1 - s ^ 2) < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
    nlinarith
  have hrecip : 1 < 1 / Real.sqrt (1 - s ^ 2) := by
    apply (lt_div_iff₀ hsqrt).2
    simpa using hsqrt'
  unfold classicalThreshold
  linarith

def booleanHarmonicDimension (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => n.choose (k + 1) - n.choose k

theorem booleanHarmonicDimension_succ (n k : ℕ) :
    booleanHarmonicDimension n (k + 1) =
      n.choose (k + 1) - n.choose k := rfl

theorem sum_booleanHarmonicDimension (n L : ℕ) (hL : 2 * L ≤ n) :
    (∑ k ∈ Finset.range (L + 1), booleanHarmonicDimension n k) =
      n.choose L := by
  induction L generalizing n with
  | zero =>
      simp [booleanHarmonicDimension]
  | succ L ih =>
      have hprev : 2 * L ≤ n := by omega
      have hhalf : L < n / 2 := by omega
      have hmono : n.choose L ≤ n.choose (L + 1) :=
        Nat.choose_le_succ_of_lt_half_left hhalf
      rw [Finset.sum_range_succ, ih n hprev]
      change n.choose L + (n.choose (L + 1) - n.choose L) =
        n.choose (L + 1)
      omega

def hammingFibreDimension (n k : ℕ) : ℕ :=
  booleanHarmonicDimension n k

def johnsonFibreDimension (n w p q : ℕ) : ℕ :=
  booleanHarmonicDimension w p *
    booleanHarmonicDimension (n - w) q

def hammingJacobiEntry (n k i : ℕ) : ℝ :=
  (((i : ℝ) - (k : ℝ) + 1) *
    ((n : ℝ) - (i : ℝ) - (k : ℝ))) /
    ((n : ℝ) * Real.sqrt (((i : ℝ) + 1) * ((n : ℝ) - (i : ℝ))))

theorem hammingJacobiEntry_pos {n k i : ℕ}
    (hn : 0 < n) (hki : k ≤ i) (hi : i + k < n) :
    0 < hammingJacobiEntry n k i := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hki' : (k : ℝ) ≤ i := by exact_mod_cast hki
  have hi' : (i : ℝ) + (k : ℝ) < n := by exact_mod_cast hi
  have hzero : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  unfold hammingJacobiEntry
  apply div_pos
  · apply mul_pos <;> linarith
  · apply mul_pos hn'
    apply Real.sqrt_pos.2
    apply mul_pos <;> linarith

def hammingJacobiMatrix (n k L : ℕ) :
    Matrix (Fin (L - k + 1)) (Fin (L - k + 1)) ℝ :=
  fun p q =>
    if p.val + 1 = q.val then
      hammingJacobiEntry n k (k + p.val)
    else if q.val + 1 = p.val then
      hammingJacobiEntry n k (k + q.val)
    else
      0

theorem hammingJacobiMatrix_symmetric (n k L : ℕ) :
    (hammingJacobiMatrix n k L).transpose =
      hammingJacobiMatrix n k L := by
  ext p q
  simp only [Matrix.transpose_apply]
  by_cases hpq : p.val + 1 = q.val
  · have hqp : q.val + 1 ≠ p.val := by omega
    simp [hammingJacobiMatrix, hpq, hqp]
  · by_cases hqp : q.val + 1 = p.val
    · simp [hammingJacobiMatrix, hpq, hqp]
    · simp [hammingJacobiMatrix, hpq, hqp]

def hammingGamma (a b : ℝ) : ℝ :=
  (2 * (a - b) * (1 - a - b)) /
    Real.sqrt (a * (1 - a))

def johnsonJ1 (w p : ℕ) : ℝ :=
  (w : ℝ) / 2 - (p : ℝ)

def johnsonJ2 (n w q : ℕ) : ℝ :=
  ((n - w : ℕ) : ℝ) / 2 - (q : ℝ)

def johnsonJ (n j : ℕ) : ℝ :=
  (n : ℝ) / 2 - (j : ℝ)

def johnsonM (n w : ℕ) : ℝ :=
  (n : ℝ) / 2 - (w : ℝ)

def johnsonSigma (n w p q : ℕ) : ℝ :=
  johnsonJ1 w p + johnsonJ2 n w q

def johnsonDelta (n w p q : ℕ) : ℝ :=
  johnsonJ2 n w q - johnsonJ1 w p

def johnsonLastDegree (n w p q : ℕ) : ℕ :=
  min w (min (w - p + q) (n - w + p - q))

def johnsonMu (n w p q j : ℕ) : ℝ :=
  (johnsonM n w / 2) *
    (johnsonJ2 n w q * (johnsonJ2 n w q + 1) -
      johnsonJ1 w p * (johnsonJ1 w p + 1)) /
    (johnsonJ n j * (johnsonJ n j + 1))

def johnsonNu (n w p q j : ℕ) : ℝ :=
  Real.sqrt
      ((johnsonJ n j ^ 2 - johnsonM n w ^ 2) *
        (johnsonJ n j ^ 2 - johnsonDelta n w p q ^ 2) *
        ((johnsonSigma n w p q + 1) ^ 2 - johnsonJ n j ^ 2)) /
    (2 * johnsonJ n j *
      Real.sqrt ((2 * johnsonJ n j - 1) *
        (2 * johnsonJ n j + 1)))

def johnsonDiagonal (n w p q j : ℕ) : ℝ :=
  ((n : ℝ) * johnsonMu n w p q j - johnsonM n w ^ 2) /
    ((w : ℝ) * ((n - w : ℕ) : ℝ))

def johnsonEdge (n w p q j : ℕ) : ℝ :=
  ((n : ℝ) * johnsonNu n w p q j) /
    ((w : ℝ) * ((n - w : ℕ) : ℝ))

def johnsonZonalDiagonal (n w j : ℕ) : ℝ :=
  johnsonDiagonal n w 0 0 j

def johnsonZonalEdge (n w j : ℕ) : ℝ :=
  johnsonEdge n w 0 0 j

def johnsonHattedDiagonal (n w p q j : ℕ) : ℝ :=
  if j = 0 then 0
  else johnsonDiagonal n w p q j ^ 2 / johnsonZonalDiagonal n w j

def johnsonHattedEdge (n w p q j : ℕ) : ℝ :=
  johnsonEdge n w p q j ^ 2 / johnsonZonalEdge n w j

theorem johnsonHattedDiagonal_nonneg {n w p q j : ℕ}
    (hzero : 0 < johnsonZonalDiagonal n w j) :
    0 ≤ johnsonHattedDiagonal n w p q j := by
  unfold johnsonHattedDiagonal
  split <;> positivity

def johnsonJacobiMatrix (n w p q L : ℕ) :
    Matrix (Fin (L - (p + q) + 1))
      (Fin (L - (p + q) + 1)) ℝ :=
  fun i j =>
    if i = j then
      johnsonHattedDiagonal n w p q (p + q + i.val)
    else if i.val + 1 = j.val then
      johnsonHattedEdge n w p q (p + q + i.val)
    else if j.val + 1 = i.val then
      johnsonHattedEdge n w p q (p + q + j.val)
    else
      0

@[simp] theorem johnsonJacobiMatrix_diag (n w p q L : ℕ)
    (i : Fin (L - (p + q) + 1)) :
    johnsonJacobiMatrix n w p q L i i =
      johnsonHattedDiagonal n w p q (p + q + i.val) := by
  simp [johnsonJacobiMatrix]

theorem johnsonJacobiMatrix_symmetric (n w p q L : ℕ) :
    (johnsonJacobiMatrix n w p q L).transpose =
      johnsonJacobiMatrix n w p q L := by
  ext i j
  simp only [Matrix.transpose_apply]
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm hij
    by_cases hup : i.val + 1 = j.val
    · have hdown : j.val + 1 ≠ i.val := by omega
      simp [johnsonJacobiMatrix, hij, hji, hup, hdown]
    · by_cases hdown : j.val + 1 = i.val
      · simp [johnsonJacobiMatrix, hij, hji, hup, hdown]
      · simp [johnsonJacobiMatrix, hij, hji, hup, hdown]

end MetricCodes

end

section

noncomputable section

open scoped BigOperators

namespace MetricCodes.Boolean

abbrev Function (n : ℕ) := Finset (Fin n) → ℝ

abbrev Level (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

@[simp] theorem card_level (n k : ℕ) :
    Fintype.card (Level n k) = n.choose k := by
  simp [Level, Fintype.card_finset_len]

def raiseAt {n : ℕ} (a : Fin n) (f : Function n) (S : Finset (Fin n)) : ℝ :=
  if a ∈ S then f (S.erase a) else 0

def lowerAt {n : ℕ} (a : Fin n) (f : Function n) (S : Finset (Fin n)) : ℝ :=
  if a ∈ S then 0 else f (insert a S)

def raise {n : ℕ} (f : Function n) (S : Finset (Fin n)) : ℝ :=
  ∑ a : Fin n, raiseAt a f S

def lower {n : ℕ} (f : Function n) (S : Finset (Fin n)) : ℝ :=
  ∑ a : Fin n, lowerAt a f S

def IsLevel {n : ℕ} (k : ℕ) (f : Function n) : Prop :=
  ∀ S : Finset (Fin n), S.card ≠ k → f S = 0

def IsHarmonic {n : ℕ} (k : ℕ) (f : Function n) : Prop :=
  IsLevel k f ∧ ∀ S : Finset (Fin n), lower f S = 0

variable {n : ℕ}

theorem lowerAt_raiseAt_of_ne (f : Function n) (a b : Fin n)
    (hab : a ≠ b) (S : Finset (Fin n)) :
    lowerAt a (raiseAt b f) S = raiseAt b (lowerAt a f) S := by
  classical
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · simp [lowerAt, raiseAt, ha, hb, Finset.mem_erase, hab]
  · simp [lowerAt, raiseAt, ha, hb]
  · simp [lowerAt, raiseAt, ha, hb, Finset.mem_erase, hab,
      Finset.erase_insert_of_ne hab]
  · simp [lowerAt, raiseAt, ha, hb, Finset.mem_insert, hab.symm]

theorem lowerAt_raiseAt_self (f : Function n) (a : Fin n)
    (S : Finset (Fin n)) :
    lowerAt a (raiseAt a f) S = if a ∈ S then 0 else f S := by
  classical
  by_cases ha : a ∈ S
  · simp [lowerAt, ha]
  · simp [lowerAt, raiseAt, ha, Finset.erase_insert ha]

theorem raiseAt_lowerAt_self (f : Function n) (a : Fin n)
    (S : Finset (Fin n)) :
    raiseAt a (lowerAt a f) S = if a ∈ S then f S else 0 := by
  classical
  by_cases ha : a ∈ S
  · simp [lowerAt, raiseAt, ha, Finset.insert_erase ha]
  · simp [raiseAt, ha]

theorem lowerAt_raise (f : Function n) (a : Fin n)
    (S : Finset (Fin n)) :
    lowerAt a (raise f) S =
      ∑ b : Fin n, lowerAt a (raiseAt b f) S := by
  classical
  by_cases ha : a ∈ S <;> simp [lowerAt, raise, ha]

theorem raiseAt_lower (f : Function n) (a : Fin n)
    (S : Finset (Fin n)) :
    raiseAt a (lower f) S =
      ∑ b : Fin n, raiseAt a (lowerAt b f) S := by
  classical
  by_cases ha : a ∈ S <;> simp [raiseAt, lower, ha]

theorem sum_mem_indicator (S : Finset (Fin n)) (x : ℝ) :
    (∑ a : Fin n, if a ∈ S then x else 0) = (S.card : ℝ) * x := by
  classical
  calc
    (∑ a : Fin n, if a ∈ S then x else 0) = ∑ a ∈ S, x := by
      simp
    _ = (S.card : ℝ) * x := by simp

theorem lower_raise_sub_raise_lower (f : Function n)
    (S : Finset (Fin n)) :
    lower (raise f) S - raise (lower f) S =
      ((n : ℝ) - 2 * (S.card : ℝ)) * f S := by
  classical
  change
    (∑ a : Fin n, lowerAt a (raise f) S) -
      (∑ a : Fin n, raiseAt a (lower f) S) = _
  simp_rw [lowerAt_raise, raiseAt_lower]
  have hswap :
      (∑ a : Fin n, ∑ b : Fin n, raiseAt a (lowerAt b f) S) =
        ∑ b : Fin n, ∑ a : Fin n, raiseAt a (lowerAt b f) S := by
    exact Finset.sum_comm
  rw [hswap, ← Finset.sum_sub_distrib]
  have hcross (a : Fin n) :
      (∑ b : Fin n, lowerAt a (raiseAt b f) S) -
        (∑ b : Fin n, raiseAt b (lowerAt a f) S) =
          lowerAt a (raiseAt a f) S - raiseAt a (lowerAt a f) S := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_single a
    · intro b _ hba
      rw [lowerAt_raiseAt_of_ne f a b hba.symm S]
      exact sub_self _
    · simp
  simp_rw [hcross, lowerAt_raiseAt_self, raiseAt_lowerAt_self]
  have hterm (a : Fin n) :
      (if a ∈ S then (0 : ℝ) else f S) -
          (if a ∈ S then f S else 0) =
        f S - 2 * (if a ∈ S then f S else 0) := by
    by_cases ha : a ∈ S <;> simp [ha] ; ring
  simp_rw [hterm, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, sum_mem_indicator]
  simp
  ring

theorem lower_raise_sub_raise_lower_of_level {k : ℕ}
    (f : Function n) (hf : IsLevel k f) (S : Finset (Fin n)) :
    lower (raise f) S - raise (lower f) S =
      ((n : ℝ) - 2 * (k : ℝ)) * f S := by
  by_cases hS : S.card = k
  · simpa [hS] using lower_raise_sub_raise_lower f S
  · rw [lower_raise_sub_raise_lower, hf S hS]
    simp

theorem lower_raise_of_harmonic {k : ℕ} (f : Function n)
    (hf : IsHarmonic k f) (S : Finset (Fin n)) :
    lower (raise f) S = ((n : ℝ) - 2 * (k : ℝ)) * f S := by
  have hcomm := lower_raise_sub_raise_lower_of_level f hf.1 S
  have hzero : raise (lower f) S = 0 := by
    simp [raise, raiseAt, hf.2]
  simpa [hzero] using hcomm

theorem raise_add (f g : Function n) :
    raise (f + g) = raise f + raise g := by
  classical
  funext S
  change
    (∑ a : Fin n, if a ∈ S then f (S.erase a) + g (S.erase a) else 0) =
      (∑ a : Fin n, if a ∈ S then f (S.erase a) else 0) +
        (∑ a : Fin n, if a ∈ S then g (S.erase a) else 0)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ S <;> simp [ha]

theorem raise_smul (c : ℝ) (f : Function n) :
    raise (c • f) = c • raise f := by
  classical
  funext S
  simp only [raise, raiseAt, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ S <;> simp [ha]

theorem lower_add (f g : Function n) :
    lower (f + g) = lower f + lower g := by
  classical
  funext S
  change
    (∑ a : Fin n, if a ∈ S then 0 else f (insert a S) + g (insert a S)) =
      (∑ a : Fin n, if a ∈ S then 0 else f (insert a S)) +
        (∑ a : Fin n, if a ∈ S then 0 else g (insert a S))
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ S <;> simp [ha]

theorem lower_smul (c : ℝ) (f : Function n) :
    lower (c • f) = c • lower f := by
  classical
  funext S
  simp only [lower, lowerAt, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ S <;> simp [ha]

def raiseLinear (n : ℕ) : Function n →ₗ[ℝ] Function n where
  toFun := raise
  map_add' := raise_add
  map_smul' := raise_smul

def lowerLinear (n : ℕ) : Function n →ₗ[ℝ] Function n where
  toFun := lower
  map_add' := lower_add
  map_smul' := lower_smul

@[simp] theorem raiseLinear_apply (f : Function n) :
    raiseLinear n f = raise f := rfl

theorem IsLevel.raise {k : ℕ} {f : Function n} (hf : IsLevel k f) :
    IsLevel (k + 1) (raise f) := by
  classical
  intro S hS
  unfold MetricCodes.Boolean.raise
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : a ∈ S
  · have herase : (S.erase a).card ≠ k := by
      intro he
      apply hS
      calc
        S.card = (S.erase a).card + 1 :=
          (Finset.card_erase_add_one ha).symm
        _ = k + 1 := by rw [he]
    simp [raiseAt, ha, hf (S.erase a) herase]
  · simp [raiseAt, ha]

theorem IsLevel.lower {k : ℕ} {f : Function n}
    (hf : IsLevel (k + 1) f) :
    IsLevel k (lower f) := by
  classical
  intro S hS
  unfold MetricCodes.Boolean.lower
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : a ∈ S
  · simp [lowerAt, ha]
  · have hinsert : (insert a S).card ≠ k + 1 := by
      intro hi
      have hcard : S.card + 1 = k + 1 := by
        simpa only [Finset.card_insert_of_notMem ha] using hi
      exact hS (Nat.add_right_cancel hcard)
    simp [lowerAt, ha, hf (insert a S) hinsert]

def raised {n : ℕ} (f : Function n) : ℕ → Function n
  | 0 => f
  | r + 1 => raise (raised f r)

@[simp] theorem raised_succ (f : Function n) (r : ℕ) :
    raised f (r + 1) = raise (raised f r) := rfl

theorem IsLevel.raised {k : ℕ} {f : Function n}
    (hf : IsLevel k f) (r : ℕ) :
    IsLevel (k + r) (raised f r) := by
  induction r with
  | zero =>
      change IsLevel k f
      exact hf
  | succ r ih =>
      simpa [Nat.add_assoc] using ih.raise

def harmonicCoefficient (n k r : ℕ) : ℝ :=
  (r : ℝ) * ((n : ℝ) - 2 * (k : ℝ) - (r : ℝ) + 1)

@[simp] theorem harmonicCoefficient_zero (n k : ℕ) :
    harmonicCoefficient n k 0 = 0 := by
  simp [harmonicCoefficient]

theorem harmonicCoefficient_succ (n k r : ℕ) :
    harmonicCoefficient n k (r + 1) =
      harmonicCoefficient n k r +
        ((n : ℝ) - 2 * ((k + r : ℕ) : ℝ)) := by
  simp [harmonicCoefficient, Nat.cast_add, Nat.cast_one]
  ring

theorem lower_raised_succ_of_harmonic {k : ℕ}
    (f : Function n) (hf : IsHarmonic k f) (r : ℕ) :
    lower (raised f (r + 1)) =
      harmonicCoefficient n k (r + 1) • raised f r := by
  induction r with
  | zero =>
      funext S
      simpa [raised, harmonicCoefficient, Pi.smul_apply, smul_eq_mul] using
        lower_raise_of_harmonic f hf S
  | succ r ih =>
      have hlevel : IsLevel (k + (r + 1)) (raised f (r + 1)) :=
        hf.1.raised (r + 1)
      funext S
      have hcomm :=
        lower_raise_sub_raise_lower_of_level
          (raised f (r + 1)) hlevel S
      rw [ih, raise_smul] at hcomm
      have hsum := sub_eq_iff_eq_add.mp hcomm
      calc
        lower (raised f ((r + 1) + 1)) S =
            ((n : ℝ) - 2 * ((k + (r + 1) : ℕ) : ℝ)) *
                raised f (r + 1) S +
              harmonicCoefficient n k (r + 1) * raised f (r + 1) S := by
          simpa only [raised_succ, Pi.smul_apply, smul_eq_mul] using hsum
        _ = harmonicCoefficient n k ((r + 1) + 1) *
              raised f (r + 1) S := by
          rw [harmonicCoefficient_succ n k (r + 1)]
          ring
        _ = (harmonicCoefficient n k ((r + 1) + 1) •
              raised f (r + 1)) S := by
          simp [Pi.smul_apply, smul_eq_mul]

def toggle (a : Fin n) (S : Finset (Fin n)) : Finset (Fin n) :=
  if a ∈ S then S.erase a else insert a S

@[simp] theorem toggle_toggle (a : Fin n) (S : Finset (Fin n)) :
    toggle a (toggle a S) = S := by
  classical
  by_cases ha : a ∈ S
  · simp [toggle, ha, Finset.insert_erase ha]
  · simp [toggle, ha, Finset.erase_insert ha]

def toggleEquiv (a : Fin n) : Finset (Fin n) ≃ Finset (Fin n) where
  toFun := toggle a
  invFun := toggle a
  left_inv := toggle_toggle a
  right_inv := toggle_toggle a

def dot (f g : Function n) : ℝ :=
  ∑ S : Finset (Fin n), f S * g S

theorem dot_raiseAt_eq_lowerAt (a : Fin n) (f g : Function n) :
    dot (raiseAt a f) g = dot f (lowerAt a g) := by
  classical
  unfold dot
  calc
    (∑ S : Finset (Fin n), raiseAt a f S * g S) =
        ∑ S : Finset (Fin n),
          raiseAt a f (toggle a S) * g (toggle a S) := by
      symm
      exact (toggleEquiv a).sum_comp
        (fun S : Finset (Fin n) => raiseAt a f S * g S)
    _ = ∑ S : Finset (Fin n), f S * lowerAt a g S := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases ha : a ∈ S
      · simp [toggle, raiseAt, lowerAt, ha]
      · simp [toggle, raiseAt, lowerAt, ha, Finset.erase_insert ha]

theorem dot_raise_eq_lower (f g : Function n) :
    dot (raise f) g = dot f (lower g) := by
  classical
  calc
    dot (raise f) g = ∑ a : Fin n, dot (raiseAt a f) g := by
      simp only [dot, raise, Finset.sum_mul]
      exact Finset.sum_comm
    _ = ∑ a : Fin n, dot f (lowerAt a g) := by
      apply Finset.sum_congr rfl
      intro a _
      exact dot_raiseAt_eq_lowerAt a f g
    _ = dot f (lower g) := by
      simp only [dot, lower, Finset.mul_sum]
      exact Finset.sum_comm

theorem dot_comm (f g : Function n) : dot f g = dot g f := by
  classical
  unfold dot
  apply Finset.sum_congr rfl
  intro S _
  exact mul_comm _ _

theorem dot_smul_right (f g : Function n) (c : ℝ) :
    dot f (c • g) = c * dot f g := by
  classical
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

def normSq (f : Function n) : ℝ := dot f f

theorem normSq_nonneg (f : Function n) : 0 ≤ normSq f := by
  unfold normSq dot
  apply Finset.sum_nonneg
  intro S _
  exact mul_self_nonneg (f S)

@[simp] theorem normSq_eq_zero_iff (f : Function n) :
    normSq f = 0 ↔ f = 0 := by
  classical
  change (∑ S : Finset (Fin n), f S * f S) = 0 ↔ f = 0
  constructor
  · intro h
    have hz :=
      (Finset.sum_mul_self_eq_zero_iff
        (Finset.univ : Finset (Finset (Fin n))) f).mp h
    funext S
    exact hz S (Finset.mem_univ S)
  · intro h
    subst f
    simp

end MetricCodes.Boolean

end

section

noncomputable section

open scoped BigOperators Matrix InnerProductSpace

namespace MetricCodes

structure ProjectionFamily (X : Type*) (D d : ℕ) where

  projection : X → Matrix (Fin D) (Fin D) ℝ

  symmetric : ∀ x, (projection x)ᵀ = projection x

  idempotent : ∀ x, projection x * projection x = projection x

  trace_eq : ∀ x, Matrix.trace (projection x) = (d : ℝ)

namespace ProjectionFamily

variable {X : Type*} {D d : ℕ}

def overlap (P : ProjectionFamily X D d) (x y : X) : ℝ :=
  Matrix.trace (P.projection x * P.projection y)

@[simp] theorem overlap_self (P : ProjectionFamily X D d) (x : X) :
    P.overlap x x = (d : ℝ) := by
  unfold overlap
  rw [P.idempotent x, P.trace_eq x]

theorem overlap_eq_trace_sq (P : ProjectionFamily X D d) (x y : X) :
    P.overlap x y =
      Matrix.trace
        ((P.projection x * P.projection y)ᴴ *
          (P.projection x * P.projection y)) := by
  unfold overlap
  rw [Matrix.conjTranspose_mul,
    Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.conjTranspose_eq_transpose_of_trivial,
    P.symmetric x, P.symmetric y]
  symm
  calc
    Matrix.trace
        ((P.projection y * P.projection x) *
          (P.projection x * P.projection y)) =
        Matrix.trace
          ((P.projection y * (P.projection x * P.projection x)) *
            P.projection y) := by
          congr 1
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace
          ((P.projection y * P.projection x) * P.projection y) := by
          rw [P.idempotent x]
    _ = Matrix.trace
          (P.projection y * (P.projection x * P.projection y)) := by
          rw [Matrix.mul_assoc]
    _ = Matrix.trace
          ((P.projection x * P.projection y) * P.projection y) := by
          exact Matrix.trace_mul_comm _ _
    _ = Matrix.trace
          (P.projection x * (P.projection y * P.projection y)) := by
          rw [Matrix.mul_assoc]
    _ = Matrix.trace (P.projection x * P.projection y) := by
          rw [P.idempotent y]

theorem overlap_nonneg (P : ProjectionFamily X D d) (x y : X) :
    0 ≤ P.overlap x y := by
  rw [P.overlap_eq_trace_sq]
  exact
    (Matrix.posSemidef_conjTranspose_mul_self
      (P.projection x * P.projection y)).trace_nonneg

theorem sq_trace_le_dimension_mul_trace_sq
    (A : Matrix (Fin D) (Fin D) ℝ) :
    (Matrix.trace A) ^ 2 ≤
      (D : ℝ) * Matrix.trace (Aᵀ * A) := by
  classical
  have hdiag :
      (Matrix.trace A) ^ 2 ≤
        (D : ℝ) * ∑ i : Fin D, (A i i) ^ 2 := by
    simpa [Matrix.trace] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin D)))
        (f := fun i : Fin D => A i i))
  have hterm (i : Fin D) :
      (A i i) ^ 2 ≤ ∑ j : Fin D, (A i j) ^ 2 :=
    Finset.single_le_sum
      (fun j _ => sq_nonneg (A i j)) (Finset.mem_univ i)
  have hsum :
      (∑ i : Fin D, (A i i) ^ 2) ≤
        ∑ i : Fin D, ∑ j : Fin D, (A i j) ^ 2 :=
    Finset.sum_le_sum (fun i _ => hterm i)
  have htrace :
      Matrix.trace (Aᵀ * A) =
        ∑ i : Fin D, ∑ j : Fin D, (A i j) ^ 2 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.transpose_apply, pow_two]
    rw [Finset.sum_comm]
  calc
    (Matrix.trace A) ^ 2 ≤
        (D : ℝ) * ∑ i : Fin D, (A i i) ^ 2 := hdiag
    _ ≤ (D : ℝ) *
        (∑ i : Fin D, ∑ j : Fin D, (A i j) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg D)
    _ = (D : ℝ) * Matrix.trace (Aᵀ * A) := by rw [htrace]

theorem sum_symmetric (P : ProjectionFamily X D d)
    (C : Finset X) :
    (∑ x ∈ C, P.projection x)ᵀ =
      ∑ x ∈ C, P.projection x := by
  classical
  ext i j
  simp only [Matrix.transpose_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro x _
  have h := congrFun (congrFun (P.symmetric x) i) j
  simpa [Matrix.transpose_apply] using h

theorem sum_overlap_eq_trace_mul_sum (P : ProjectionFamily X D d)
    (C : Finset X) :
    (∑ x ∈ C, ∑ y ∈ C, P.overlap x y) =
      Matrix.trace
        ((∑ x ∈ C, P.projection x) *
          (∑ y ∈ C, P.projection y)) := by
  classical
  simp only [overlap, Matrix.trace_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem card_mul_rank_sq_le_dimension_mul_sum_overlap
    (P : ProjectionFamily X D d) (C : Finset X) :
    ((C.card : ℝ) * (d : ℝ)) ^ 2 ≤
      (D : ℝ) * (∑ x ∈ C, ∑ y ∈ C, P.overlap x y) := by
  classical
  let A : Matrix (Fin D) (Fin D) ℝ :=
    ∑ x ∈ C, P.projection x
  have htrace : Matrix.trace A = (C.card : ℝ) * (d : ℝ) := by
    dsimp [A]
    simp [Matrix.trace_sum, P.trace_eq]
  have hsym : Aᵀ = A := P.sum_symmetric C
  have hcs := sq_trace_le_dimension_mul_trace_sq A
  rw [htrace, hsym, ← P.sum_overlap_eq_trace_mul_sum C] at hcs
  exact hcs

end ProjectionFamily

section Gram

variable {X E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem gram_double_sum_nonneg (C : Finset X) (q : X → E) :
    0 ≤ ∑ x ∈ C, ∑ y ∈ C, ⟪q x, q y⟫_ℝ := by
  classical
  calc
    0 ≤ ⟪∑ x ∈ C, q x, ∑ x ∈ C, q x⟫_ℝ :=
      real_inner_self_nonneg
    _ = ∑ x ∈ C, ∑ y ∈ C, ⟪q x, q y⟫_ℝ := by
      simp only [sum_inner, inner_sum]
      rw [Finset.sum_comm]

end Gram

section Certificate

variable {X E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D d : ℕ}

theorem projection_certificate_mul
    (P : ProjectionFamily X D d)
    (C : Finset X)
    (t : X → X → ℝ)
    (q : X → E)
    {s lam : ℝ}
    (hd : 0 < d)
    (hs : s < 1)
    (hgap : s < lam)
    (hdiag : ∀ x ∈ C, t x x = 1)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → t x y ≤ s)
    (hgram : ∀ x ∈ C, ∀ y ∈ C,
      ⟪q x, q y⟫_ℝ = (t x y - lam) * P.overlap x y) :
    (C.card : ℝ) * (lam - s) * (d : ℝ) ≤
      (1 - s) * (D : ℝ) := by
  classical
  let f : X → X → ℝ :=
    fun x y => (t x y - s) * P.overlap x y
  have hfeature (x : X) (hx : x ∈ C)
      (y : X) (hy : y ∈ C) :
      f x y =
        (lam - s) * P.overlap x y + ⟪q x, q y⟫_ℝ := by
    dsimp [f]
    rw [hgram x hx y hy]
    ring
  have hgram_nonneg :
      0 ≤ ∑ x ∈ C, ∑ y ∈ C, ⟪q x, q y⟫_ℝ :=
    gram_double_sum_nonneg C q
  have hfeature_sum :
      (∑ x ∈ C, ∑ y ∈ C, f x y) =
        (lam - s) * (∑ x ∈ C, ∑ y ∈ C, P.overlap x y) +
          (∑ x ∈ C, ∑ y ∈ C, ⟪q x, q y⟫_ℝ) := by
    calc
      (∑ x ∈ C, ∑ y ∈ C, f x y) =
          ∑ x ∈ C, ∑ y ∈ C,
            ((lam - s) * P.overlap x y + ⟪q x, q y⟫_ℝ) := by
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro y hy
              exact hfeature x hx y hy
      _ = (lam - s) * (∑ x ∈ C, ∑ y ∈ C, P.overlap x y) +
          (∑ x ∈ C, ∑ y ∈ C, ⟪q x, q y⟫_ℝ) := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hlower :
      (lam - s) * (∑ x ∈ C, ∑ y ∈ C, P.overlap x y) ≤
        ∑ x ∈ C, ∑ y ∈ C, f x y := by
    rw [hfeature_sum]
    exact le_add_of_nonneg_right hgram_nonneg
  have hrow (x : X) (hx : x ∈ C) :
      (∑ y ∈ C, f x y) ≤ (1 - s) * (d : ℝ) := by
    calc
      (∑ y ∈ C, f x y) ≤
          ∑ y ∈ C, if y = x then f x x else 0 := by
            apply Finset.sum_le_sum
            intro y hy
            by_cases hyx : y = x
            · subst y
              simp
            · have hnonpos : f x y ≤ 0 := by
                exact mul_nonpos_of_nonpos_of_nonneg
                  (sub_nonpos.mpr
                    (hsep x hx y hy (Ne.symm hyx)))
                  (P.overlap_nonneg x y)
              simpa [hyx] using hnonpos
      _ = f x x := by simp [hx]
      _ = (1 - s) * (d : ℝ) := by
        dsimp [f]
        rw [hdiag x hx, P.overlap_self x]
  have hupper :
      (∑ x ∈ C, ∑ y ∈ C, f x y) ≤
        (C.card : ℝ) * (1 - s) * (d : ℝ) := by
    calc
      (∑ x ∈ C, ∑ y ∈ C, f x y) ≤
          ∑ x ∈ C, (1 - s) * (d : ℝ) :=
            Finset.sum_le_sum (fun x hx => hrow x hx)
      _ = (C.card : ℝ) * (1 - s) * (d : ℝ) := by
        simp
        ring
  have hoverlap :
      ((C.card : ℝ) * (d : ℝ)) ^ 2 ≤
        (D : ℝ) * (∑ x ∈ C, ∑ y ∈ C, P.overlap x y) :=
    P.card_mul_rank_sq_le_dimension_mul_sum_overlap C
  have hD : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hgap_pos : 0 < lam - s := sub_pos.mpr hgap
  have hmain :
      (lam - s) * ((C.card : ℝ) * (d : ℝ)) ^ 2 ≤
        (D : ℝ) * ((C.card : ℝ) * (1 - s) * (d : ℝ)) := by
    calc
      (lam - s) * ((C.card : ℝ) * (d : ℝ)) ^ 2 ≤
          (lam - s) *
            ((D : ℝ) * (∑ x ∈ C, ∑ y ∈ C, P.overlap x y)) :=
              mul_le_mul_of_nonneg_left hoverlap hgap_pos.le
      _ = (D : ℝ) *
          ((lam - s) *
            (∑ x ∈ C, ∑ y ∈ C, P.overlap x y)) := by ring
      _ ≤ (D : ℝ) * (∑ x ∈ C, ∑ y ∈ C, f x y) :=
        mul_le_mul_of_nonneg_left hlower hD
      _ ≤ (D : ℝ) *
          ((C.card : ℝ) * (1 - s) * (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hupper hD
  by_cases hC : C.Nonempty
  · have hcard : 0 < (C.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hC
    have hrank : 0 < (d : ℝ) := by exact_mod_cast hd
    have hcancel :
        ((C.card : ℝ) * (d : ℝ)) *
            ((C.card : ℝ) * (lam - s) * (d : ℝ)) ≤
          ((C.card : ℝ) * (d : ℝ)) *
            ((1 - s) * (D : ℝ)) := by
      calc
        ((C.card : ℝ) * (d : ℝ)) *
            ((C.card : ℝ) * (lam - s) * (d : ℝ)) =
            (lam - s) * ((C.card : ℝ) * (d : ℝ)) ^ 2 := by ring
        _ ≤ (D : ℝ) *
            ((C.card : ℝ) * (1 - s) * (d : ℝ)) := hmain
        _ = ((C.card : ℝ) * (d : ℝ)) *
            ((1 - s) * (D : ℝ)) := by ring
    exact le_of_mul_le_mul_left hcancel (mul_pos hcard hrank)
  · have hempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    subst C
    simpa using
      (mul_nonneg (sub_nonneg.mpr hs.le) (Nat.cast_nonneg D))

theorem projection_certificate
    (P : ProjectionFamily X D d)
    (C : Finset X)
    (t : X → X → ℝ)
    (q : X → E)
    {s lam : ℝ}
    (hd : 0 < d)
    (hs : s < 1)
    (hgap : s < lam)
    (hdiag : ∀ x ∈ C, t x x = 1)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → t x y ≤ s)
    (hgram : ∀ x ∈ C, ∀ y ∈ C,
      ⟪q x, q y⟫_ℝ = (t x y - lam) * P.overlap x y) :
    (C.card : ℝ) ≤
      ((1 - s) / (lam - s)) * ((D : ℝ) / (d : ℝ)) := by
  have hrank : 0 < (d : ℝ) := by exact_mod_cast hd
  have hgap_pos : 0 < lam - s := sub_pos.mpr hgap
  have hmul :=
    projection_certificate_mul P C t q hd hs hgap hdiag hsep hgram
  have hdiv :
      (C.card : ℝ) * (d : ℝ) ≤
        ((1 - s) * (D : ℝ)) / (lam - s) := by
    apply (le_div_iff₀ hgap_pos).2
    calc
      ((C.card : ℝ) * (d : ℝ)) * (lam - s) =
          (C.card : ℝ) * (lam - s) * (d : ℝ) := by ring
      _ ≤ (1 - s) * (D : ℝ) := hmul
  calc
    (C.card : ℝ) ≤
        (((1 - s) / (lam - s)) * (D : ℝ)) / (d : ℝ) := by
          apply (le_div_iff₀ hrank).2
          calc
            (C.card : ℝ) * (d : ℝ) ≤
                ((1 - s) * (D : ℝ)) / (lam - s) := hdiv
            _ = ((1 - s) / (lam - s)) * (D : ℝ) := by ring
    _ = ((1 - s) / (lam - s)) * ((D : ℝ) / (d : ℝ)) := by ring

end Certificate

end MetricCodes

end

section

noncomputable section

open scoped BigOperators Matrix

namespace MetricCodes.Boolean

variable {n : ℕ}

def sign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem sign_mul_self (b : Bool) : sign b * sign b = 1 := by
  cases b <;> simp [sign]

def character (x : BinaryWord n) (S : Finset (Fin n)) : ℝ :=
  ∏ a ∈ S, sign (x a)

@[simp] theorem character_mul_self
    (x : BinaryWord n) (S : Finset (Fin n)) :
    character x S * character x S = 1 := by
  classical
  unfold character
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro a _
  exact sign_mul_self (x a)

def twist (x : BinaryWord n) (f : Function n) (S : Finset (Fin n)) : ℝ :=
  character x S * f S

theorem twist_smul (x : BinaryWord n) (c : ℝ) (f : Function n) :
    twist x (c • f) = c • twist x f := by
  funext S
  simp [twist, mul_left_comm]

theorem dot_twist (x : BinaryWord n) (f g : Function n) :
    dot (twist x f) (twist x g) = dot f g := by
  classical
  unfold dot
  apply Finset.sum_congr rfl
  intro S _
  unfold twist
  calc
    (character x S * f S) * (character x S * g S) =
        (character x S * character x S) * (f S * g S) := by ring
    _ = f S * g S := by rw [character_mul_self, one_mul]

theorem IsLevel.twist {k : ℕ} {f : Function n}
    (hf : IsLevel k f) (x : BinaryWord n) :
    IsLevel k (twist x f) := by
  intro S hS
  change character x S * f S = 0
  rw [hf S hS, mul_zero]

abbrev CoordinateFunction (n : ℕ) := Fin n → Function n

def coordinateDot (f g : CoordinateFunction n) : ℝ :=
  ∑ a : Fin n, dot (f a) (g a)

def deleteChannel (i : ℕ) (f : Function n) : CoordinateFunction n :=
  fun a => (Real.sqrt (i : ℝ))⁻¹ • lowerAt a f

def addChannel (i : ℕ) (f : Function n) : CoordinateFunction n :=
  fun a => (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ • raiseAt a f

theorem sum_not_mem_indicator (S : Finset (Fin n)) (z : ℝ) :
    (∑ a : Fin n, if a ∈ S then 0 else z) =
      ((n : ℝ) - (S.card : ℝ)) * z := by
  classical
  have hterm (a : Fin n) :
      (if a ∈ S then (0 : ℝ) else z) =
        z - (if a ∈ S then z else 0) := by
    by_cases ha : a ∈ S <;> simp [ha]
  simp_rw [hterm, Finset.sum_sub_distrib]
  rw [sum_mem_indicator]
  simp
  ring

theorem sum_dot_lowerAt (f g : Function n) :
    (∑ a : Fin n, dot (lowerAt a f) (lowerAt a g)) =
      ∑ S : Finset (Fin n), (S.card : ℝ) * f S * g S := by
  classical
  calc
    (∑ a : Fin n, dot (lowerAt a f) (lowerAt a g)) =
        ∑ a : Fin n, dot (raiseAt a (lowerAt a f)) g := by
      apply Finset.sum_congr rfl
      intro a _
      exact (dot_raiseAt_eq_lowerAt a (lowerAt a f) g).symm
    _ = ∑ a : Fin n, ∑ S : Finset (Fin n),
          (if a ∈ S then f S else 0) * g S := by
      apply Finset.sum_congr rfl
      intro a _
      unfold dot
      apply Finset.sum_congr rfl
      intro S _
      rw [raiseAt_lowerAt_self]
    _ = ∑ S : Finset (Fin n), ∑ a : Fin n,
          (if a ∈ S then f S else 0) * g S := by
      exact Finset.sum_comm
    _ = ∑ S : Finset (Fin n), (S.card : ℝ) * f S * g S := by
      apply Finset.sum_congr rfl
      intro S _
      rw [← Finset.sum_mul, sum_mem_indicator]

theorem sum_dot_raiseAt (f g : Function n) :
    (∑ a : Fin n, dot (raiseAt a f) (raiseAt a g)) =
      ∑ S : Finset (Fin n),
        ((n : ℝ) - (S.card : ℝ)) * f S * g S := by
  classical
  calc
    (∑ a : Fin n, dot (raiseAt a f) (raiseAt a g)) =
        ∑ a : Fin n, dot f (lowerAt a (raiseAt a g)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact dot_raiseAt_eq_lowerAt a f (raiseAt a g)
    _ = ∑ a : Fin n, ∑ S : Finset (Fin n),
          f S * (if a ∈ S then 0 else g S) := by
      apply Finset.sum_congr rfl
      intro a _
      unfold dot
      apply Finset.sum_congr rfl
      intro S _
      rw [lowerAt_raiseAt_self]
    _ = ∑ S : Finset (Fin n), ∑ a : Fin n,
          f S * (if a ∈ S then 0 else g S) := by
      exact Finset.sum_comm
    _ = ∑ S : Finset (Fin n),
          ((n : ℝ) - (S.card : ℝ)) * f S * g S := by
      apply Finset.sum_congr rfl
      intro S _
      rw [← Finset.mul_sum, sum_not_mem_indicator]
      ring

theorem sum_dot_lowerAt_of_level {i : ℕ} (f g : Function n)
    (hf : IsLevel i f) :
    (∑ a : Fin n, dot (lowerAt a f) (lowerAt a g)) =
      (i : ℝ) * dot f g := by
  classical
  rw [sum_dot_lowerAt]
  calc
    (∑ S : Finset (Fin n), (S.card : ℝ) * f S * g S) =
        ∑ S : Finset (Fin n), (i : ℝ) * f S * g S := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : S.card = i
      · simp [hS]
      · simp [hf S hS]
    _ = (i : ℝ) * dot f g := by
      simp only [dot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring

theorem sum_dot_raiseAt_of_level {i : ℕ} (f g : Function n)
    (hf : IsLevel i f) :
    (∑ a : Fin n, dot (raiseAt a f) (raiseAt a g)) =
      ((n : ℝ) - (i : ℝ)) * dot f g := by
  classical
  rw [sum_dot_raiseAt]
  calc
    (∑ S : Finset (Fin n),
          ((n : ℝ) - (S.card : ℝ)) * f S * g S) =
        ∑ S : Finset (Fin n),
          ((n : ℝ) - (i : ℝ)) * f S * g S := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : S.card = i
      · simp [hS]
      · simp [hf S hS]
    _ = ((n : ℝ) - (i : ℝ)) * dot f g := by
      simp only [dot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring

theorem dot_smul_left (f g : Function n) (c : ℝ) :
    dot (c • f) g = c * dot f g := by
  rw [dot_comm, dot_smul_right, dot_comm]

theorem dot_add_right (f g h : Function n) :
    dot f (g + h) = dot f g + dot f h := by
  classical
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem normSq_raise_of_level {i : ℕ}
    (f : Function n) (hf : IsLevel i f) :
    normSq (raise f) = normSq (lower f) +
      ((n : ℝ) - 2 * (i : ℝ)) * normSq f := by
  have hcomm :
      lower (raise f) =
        raise (lower f) + ((n : ℝ) - 2 * (i : ℝ)) • f := by
    funext S
    have h :=
      sub_eq_iff_eq_add.mp
        (lower_raise_sub_raise_lower_of_level f hf S)
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_comm] using h
  calc
    normSq (raise f) = dot (raise f) (raise f) := rfl
    _ = dot f (lower (raise f)) := dot_raise_eq_lower f (raise f)
    _ = dot f
          (raise (lower f) + ((n : ℝ) - 2 * (i : ℝ)) • f) := by
      rw [hcomm]
    _ = dot f (raise (lower f)) +
          dot f (((n : ℝ) - 2 * (i : ℝ)) • f) :=
      dot_add_right f (raise (lower f))
        (((n : ℝ) - 2 * (i : ℝ)) • f)
    _ = normSq (lower f) +
          ((n : ℝ) - 2 * (i : ℝ)) * normSq f := by
      rw [dot_smul_right, dot_comm f (raise (lower f)),
        dot_raise_eq_lower]
      rfl

theorem raise_eq_zero_iff_of_level {i : ℕ}
    (hi : 2 * i < n) (f : Function n) (hf : IsLevel i f) :
    raise f = 0 ↔ f = 0 := by
  constructor
  · intro hraise
    have hzero : normSq (raise f) = 0 := by
      rw [hraise]
      simp [normSq, dot]
    have hidentity := normSq_raise_of_level f hf
    rw [hzero] at hidentity
    have hi' : (2 : ℝ) * (i : ℝ) < (n : ℝ) := by
      exact_mod_cast hi
    have hpos : 0 < (n : ℝ) - 2 * (i : ℝ) := by linarith
    have hnonneg := normSq_nonneg (lower f)
    have hfn := normSq_nonneg f
    have hnorm : normSq f = 0 := by nlinarith
    exact (normSq_eq_zero_iff f).mp hnorm
  · intro hfzero
    subst f
    change raiseLinear n (0 : Function n) = 0
    exact map_zero (raiseLinear n)

abbrev LayerFunction (n k : ℕ) := Level n k → ℝ

def layerExtend {n k : ℕ} (f : LayerFunction n k) : Function n :=
  fun S => if h : S.card = k then f ⟨S, h⟩ else 0

def layerRestrict (k : ℕ) (f : Function n) : LayerFunction n k :=
  fun S => f S.val

theorem isLevel_layerExtend {k : ℕ} (f : LayerFunction n k) :
    IsLevel k (layerExtend f) := by
  intro S hS
  simp [layerExtend, hS]

@[simp] theorem layerRestrict_layerExtend {k : ℕ}
    (f : LayerFunction n k) :
    layerRestrict k (layerExtend f) = f := by
  funext S
  simp [layerRestrict, layerExtend, S.property]

theorem layerExtend_layerRestrict_of_level {k : ℕ}
    (f : Function n) (hf : IsLevel k f) :
    layerExtend (layerRestrict k f) = f := by
  funext S
  by_cases hS : S.card = k
  · simp [layerExtend, layerRestrict, hS]
  · simp [layerExtend, hS, hf S hS]

theorem layerExtend_injective {k : ℕ} :
    Function.Injective (layerExtend (n := n) (k := k)) := by
  intro f g h
  have := congrArg (layerRestrict k) h
  simpa using this

def layerExtendLinear (n k : ℕ) :
    LayerFunction n k →ₗ[ℝ] Function n where
  toFun := layerExtend
  map_add' := by
    intro f g
    funext S
    by_cases hS : S.card = k <;>
      simp [layerExtend, hS, Pi.add_apply]
  map_smul' := by
    intro c f
    funext S
    by_cases hS : S.card = k <;>
      simp [layerExtend, hS, Pi.smul_apply, smul_eq_mul]

def layerRestrictLinear (n k : ℕ) :
    Function n →ₗ[ℝ] LayerFunction n k where
  toFun := layerRestrict k
  map_add' := by
    intro f g
    rfl
  map_smul' := by
    intro c f
    rfl

def layerUp (n k : ℕ) :
    LayerFunction n k →ₗ[ℝ] LayerFunction n (k + 1) :=
  (layerRestrictLinear n (k + 1)).comp
    ((raiseLinear n).comp (layerExtendLinear n k))

def layerDown (n k : ℕ) :
    LayerFunction n (k + 1) →ₗ[ℝ] LayerFunction n k :=
  (layerRestrictLinear n k).comp
    ((lowerLinear n).comp (layerExtendLinear n (k + 1)))

@[simp] theorem layerUp_apply {k : ℕ} (f : LayerFunction n k) :
    layerUp n k f = layerRestrict (k + 1) (raise (layerExtend f)) := rfl

@[simp] theorem layerDown_apply {k : ℕ}
    (f : LayerFunction n (k + 1)) :
    layerDown n k f = layerRestrict k (lower (layerExtend f)) := rfl

theorem layerUp_injective {k : ℕ} (hk : 2 * k < n) :
    Function.Injective (layerUp n k) := by
  intro f g hfg
  have hflevel : IsLevel (k + 1) (raise (layerExtend f)) :=
    (isLevel_layerExtend f).raise
  have hglevel : IsLevel (k + 1) (raise (layerExtend g)) :=
    (isLevel_layerExtend g).raise
  have hrestrict :
      layerRestrict (k + 1) (raise (layerExtend f)) =
        layerRestrict (k + 1) (raise (layerExtend g)) := by
    simpa only [layerUp_apply] using hfg
  have hfull : raise (layerExtend f) = raise (layerExtend g) := by
    calc
      raise (layerExtend f) =
          layerExtend (layerRestrict (k + 1) (raise (layerExtend f))) :=
        (layerExtend_layerRestrict_of_level _ hflevel).symm
      _ = layerExtend
          (layerRestrict (k + 1) (raise (layerExtend g))) := by
        rw [hrestrict]
      _ = raise (layerExtend g) :=
        layerExtend_layerRestrict_of_level _ hglevel
  have hdifflevel : IsLevel k (layerExtend f - layerExtend g) := by
    intro S hS
    simp [Pi.sub_apply, layerExtend, hS]
  have hraisezero : raise (layerExtend f - layerExtend g) = 0 := by
    change raiseLinear n (layerExtend f - layerExtend g) = 0
    rw [map_sub, raiseLinear_apply, raiseLinear_apply, hfull, sub_self]
  have hdiffzero : layerExtend f - layerExtend g = 0 :=
    (raise_eq_zero_iff_of_level hk _ hdifflevel).mp hraisezero
  apply layerExtend_injective
  exact sub_eq_zero.mp hdiffzero

def layerDot {n k : ℕ} (f g : LayerFunction n k) : ℝ :=
  ∑ S : Level n k, f S * g S

theorem dot_layerExtend {k : ℕ} (f g : LayerFunction n k) :
    dot (layerExtend f) (layerExtend g) = layerDot f g := by
  classical
  unfold dot layerDot
  refine Finset.sum_congr_set
    {S : Finset (Fin n) | S.card = k}
    (fun S => layerExtend f S * layerExtend g S)
    (fun S : Level n k => f S * g S) ?_ ?_
  · intro S hS
    change S.card = k at hS
    simp [layerExtend, hS]
  · intro S hS
    change S.card ≠ k at hS
    simp [layerExtend, hS]

theorem layerUp_layerDown_adjoint {k : ℕ}
    (f : LayerFunction n k) (g : LayerFunction n (k + 1)) :
    layerDot (layerUp n k f) g = layerDot f (layerDown n k g) := by
  rw [← dot_layerExtend, ← dot_layerExtend]
  have hup :
      layerExtend (layerUp n k f) = raise (layerExtend f) := by
    rw [layerUp_apply]
    exact layerExtend_layerRestrict_of_level _
      (isLevel_layerExtend f).raise
  have hdown :
      layerExtend (layerDown n k g) = lower (layerExtend g) := by
    rw [layerDown_apply]
    exact layerExtend_layerRestrict_of_level _
      (isLevel_layerExtend g).lower
  rw [hup, hdown, dot_raise_eq_lower]

theorem layerUp_toMatrix_transpose (n k : ℕ) :
    LinearMap.toMatrix' (layerUp n k) =
      (LinearMap.toMatrix' (layerDown n k))ᵀ := by
  classical
  ext T S
  change
    layerUp n k (Pi.single S 1) T =
      layerDown n k (Pi.single T 1) S
  have hadjoint := layerUp_layerDown_adjoint
    (n := n) (k := k) (Pi.single S 1) (Pi.single T 1)
  simpa [layerDot, Pi.single_apply] using hadjoint

theorem layerUp_matrix_rank {k : ℕ} (hk : 2 * k < n) :
    (LinearMap.toMatrix' (layerUp n k)).rank = n.choose k := by
  classical
  have hker : LinearMap.ker (layerUp n k) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (layerUp_injective hk)
  have hrange := (layerUp n k).finrank_range_add_finrank_ker
  rw [hker, finrank_bot, add_zero,
    Module.finrank_fintype_fun_eq_card, card_level] at hrange
  have hlin :
      (LinearMap.toMatrix' (layerUp n k)).mulVecLin =
        layerUp n k := by
    simpa only [Matrix.toLin'_apply'] using
      Matrix.toLin'_toMatrix' (layerUp n k)
  change
    Module.finrank ℝ
      (LinearMap.range
        (LinearMap.toMatrix' (layerUp n k)).mulVecLin) =
      n.choose k
  rw [hlin]
  exact hrange

theorem layerDown_matrix_rank {k : ℕ} (hk : 2 * k < n) :
    (LinearMap.toMatrix' (layerDown n k)).rank = n.choose k := by
  classical
  calc
    (LinearMap.toMatrix' (layerDown n k)).rank =
        ((LinearMap.toMatrix' (layerDown n k))ᵀ).rank :=
      (Matrix.rank_transpose _).symm
    _ = (LinearMap.toMatrix' (layerUp n k)).rank := by
      rw [← layerUp_toMatrix_transpose n k]
    _ = n.choose k := layerUp_matrix_rank hk

theorem layerDown_surjective {k : ℕ} (hk : 2 * k < n) :
    Function.Surjective (layerDown n k) := by
  classical
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, card_level]
  have hlin :
      (LinearMap.toMatrix' (layerDown n k)).mulVecLin =
        layerDown n k := by
    simpa only [Matrix.toLin'_apply'] using
      Matrix.toLin'_toMatrix' (layerDown n k)
  calc
    Module.finrank ℝ (LinearMap.range (layerDown n k)) =
        (LinearMap.toMatrix' (layerDown n k)).rank := by
      change
        Module.finrank ℝ (LinearMap.range (layerDown n k)) =
          Module.finrank ℝ
            (LinearMap.range
              (LinearMap.toMatrix' (layerDown n k)).mulVecLin)
      rw [hlin]
    _ = n.choose k := layerDown_matrix_rank hk

theorem finrank_ker_layerDown {k : ℕ} (hk : 2 * k < n) :
    Module.finrank ℝ (LinearMap.ker (layerDown n k)) =
      n.choose (k + 1) - n.choose k := by
  have hrange : LinearMap.range (layerDown n k) = ⊤ :=
    LinearMap.range_eq_top.mpr (layerDown_surjective hk)
  have hcod : Module.finrank ℝ (LayerFunction n k) = n.choose k := by
    change Module.finrank ℝ (Level n k → ℝ) = n.choose k
    rw [Module.finrank_fintype_fun_eq_card, card_level]
  have hdomain :
      Module.finrank ℝ (LayerFunction n (k + 1)) =
        n.choose (k + 1) := by
    change
      Module.finrank ℝ (Level n (k + 1) → ℝ) = n.choose (k + 1)
    rw [Module.finrank_fintype_fun_eq_card, card_level]
  have hrank := (layerDown n k).finrank_range_add_finrank_ker
  rw [hrange, finrank_top, hcod, hdomain] at hrank
  exact Nat.eq_sub_of_add_eq' hrank

def harmonicLayer (n : ℕ) :
    (k : ℕ) → Submodule ℝ (LayerFunction n k)
  | 0 => ⊤
  | k + 1 => LinearMap.ker (layerDown n k)

theorem harmonicLayer_finrank (n k : ℕ) (hk : 2 * k ≤ n) :
    Module.finrank ℝ (harmonicLayer n k) =
      MetricCodes.hammingFibreDimension n k := by
  cases k with
  | zero =>
      change Module.finrank ℝ (⊤ : Submodule ℝ (LayerFunction n 0)) =
        MetricCodes.hammingFibreDimension n 0
      rw [finrank_top,
        Module.finrank_fintype_fun_eq_card, card_level]
      simp [MetricCodes.hammingFibreDimension, MetricCodes.booleanHarmonicDimension]
  | succ k =>
      have hbelow : 2 * k < n := by omega
      change
        Module.finrank ℝ (LinearMap.ker (layerDown n k)) =
          n.choose (k + 1) - n.choose k
      exact finrank_ker_layerDown (n := n) (k := k) hbelow

theorem deleteChannel_isometry {i : ℕ} (hi : 0 < i)
    (f g : Function n) (hf : IsLevel i f) :
    coordinateDot (deleteChannel i f) (deleteChannel i g) = dot f g := by
  classical
  have hi' : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have hs : Real.sqrt (i : ℝ) ≠ 0 := (Real.sqrt_pos.2 hi').ne'
  have hsqr : Real.sqrt (i : ℝ) * Real.sqrt (i : ℝ) = (i : ℝ) :=
    Real.mul_self_sqrt hi'.le
  have hscalar :
      (Real.sqrt (i : ℝ))⁻¹ * (Real.sqrt (i : ℝ))⁻¹ * (i : ℝ) = 1 := by
    calc
      (Real.sqrt (i : ℝ))⁻¹ * (Real.sqrt (i : ℝ))⁻¹ * (i : ℝ) =
          (Real.sqrt (i : ℝ))⁻¹ * (Real.sqrt (i : ℝ))⁻¹ *
            (Real.sqrt (i : ℝ) * Real.sqrt (i : ℝ)) := by rw [hsqr]
      _ = 1 := by field_simp [hs]
  calc
    coordinateDot (deleteChannel i f) (deleteChannel i g) =
        ((Real.sqrt (i : ℝ))⁻¹ * (Real.sqrt (i : ℝ))⁻¹) *
          (∑ a : Fin n, dot (lowerAt a f) (lowerAt a g)) := by
      simp only [coordinateDot, deleteChannel, dot_smul_left,
        dot_smul_right, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ((Real.sqrt (i : ℝ))⁻¹ * (Real.sqrt (i : ℝ))⁻¹) *
          ((i : ℝ) * dot f g) := by rw [sum_dot_lowerAt_of_level f g hf]
    _ = ((Real.sqrt (i : ℝ))⁻¹ * (Real.sqrt (i : ℝ))⁻¹ *
          (i : ℝ)) * dot f g := by ring
    _ = dot f g := by rw [hscalar, one_mul]

theorem addChannel_isometry {i : ℕ} (hi : i < n)
    (f g : Function n) (hf : IsLevel i f) :
    coordinateDot (addChannel i f) (addChannel i g) = dot f g := by
  classical
  have hi' : (i : ℝ) < (n : ℝ) := by exact_mod_cast hi
  have hpos : 0 < (n : ℝ) - (i : ℝ) := sub_pos.mpr hi'
  have hs : Real.sqrt ((n : ℝ) - (i : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  have hsqr :
      Real.sqrt ((n : ℝ) - (i : ℝ)) *
          Real.sqrt ((n : ℝ) - (i : ℝ)) = (n : ℝ) - (i : ℝ) :=
    Real.mul_self_sqrt hpos.le
  have hscalar :
      (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
            ((n : ℝ) - (i : ℝ)) = 1 := by
    calc
      (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
            ((n : ℝ) - (i : ℝ)) =
        (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
            (Real.sqrt ((n : ℝ) - (i : ℝ)) *
              Real.sqrt ((n : ℝ) - (i : ℝ))) := by rw [hsqr]
      _ = 1 := by field_simp [hs]
  calc
    coordinateDot (addChannel i f) (addChannel i g) =
        ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹) *
            (∑ a : Fin n, dot (raiseAt a f) (raiseAt a g)) := by
      simp only [coordinateDot, addChannel, dot_smul_left,
        dot_smul_right, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹) *
            (((n : ℝ) - (i : ℝ)) * dot f g) := by
      rw [sum_dot_raiseAt_of_level f g hf]
    _ = ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
            ((n : ℝ) - (i : ℝ))) * dot f g := by ring
    _ = dot f g := by rw [hscalar, one_mul]

theorem dot_lowerAt_raiseAt (a : Fin n) (f g : Function n) :
    dot (lowerAt a f) (raiseAt a g) = 0 := by
  classical
  unfold dot
  apply Finset.sum_eq_zero
  intro S _
  by_cases ha : a ∈ S <;> simp [lowerAt, raiseAt, ha]

theorem deleteChannel_orthogonal_addChannel (i j : ℕ)
    (f g : Function n) :
    coordinateDot (deleteChannel i f) (addChannel j g) = 0 := by
  classical
  unfold coordinateDot deleteChannel addChannel
  apply Finset.sum_eq_zero
  intro a _
  rw [dot_smul_left, dot_smul_right, dot_lowerAt_raiseAt]
  simp

def harmonicNormFactor (n k r : ℕ) : ℝ :=
  ∏ j ∈ Finset.range r, harmonicCoefficient n k (j + 1)

@[simp] theorem harmonicNormFactor_zero (n k : ℕ) :
    harmonicNormFactor n k 0 = 1 := by
  simp [harmonicNormFactor]

theorem harmonicCoefficient_pos {n k r : ℕ}
    (hr : 0 < r) (hbound : 2 * k + r ≤ n) :
    0 < harmonicCoefficient n k r := by
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hbound' :
      (2 : ℝ) * (k : ℝ) + (r : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hbound
  unfold harmonicCoefficient
  apply mul_pos hr'
  linarith

theorem harmonicNormFactor_pos {n k r : ℕ}
    (hbound : 2 * k + r ≤ n) :
    0 < harmonicNormFactor n k r := by
  unfold harmonicNormFactor
  apply Finset.prod_pos
  intro j hj
  have hj' : j < r := Finset.mem_range.mp hj
  apply harmonicCoefficient_pos (Nat.succ_pos j)
  exact (Nat.add_le_add_left (Nat.succ_le_of_lt hj') (2 * k)).trans hbound

theorem dot_raised_succ_of_harmonic {k : ℕ}
    (f g : Function n) (hg : IsHarmonic k g) (r : ℕ) :
    dot (raised f (r + 1)) (raised g (r + 1)) =
      harmonicCoefficient n k (r + 1) *
        dot (raised f r) (raised g r) := by
  calc
    dot (raised f (r + 1)) (raised g (r + 1)) =
        dot (raise (raised f r)) (raise (raised g r)) := rfl
    _ = dot (raised f r) (lower (raise (raised g r))) :=
      dot_raise_eq_lower (raised f r) (raise (raised g r))
    _ = dot (raised f r) (lower (raised g (r + 1))) := rfl
    _ = dot (raised f r)
          (harmonicCoefficient n k (r + 1) • raised g r) := by
      rw [lower_raised_succ_of_harmonic g hg r]
    _ = harmonicCoefficient n k (r + 1) *
          dot (raised f r) (raised g r) := by
      rw [dot_smul_right]

theorem dot_raised_of_harmonic {k : ℕ}
    (f g : Function n) (hg : IsHarmonic k g) (r : ℕ) :
    dot (raised f r) (raised g r) =
      harmonicNormFactor n k r * dot f g := by
  induction r with
  | zero => simp [raised, harmonicNormFactor]
  | succ r ih =>
      rw [dot_raised_succ_of_harmonic f g hg r, ih]
      simp only [harmonicNormFactor, Finset.prod_range_succ]
      ring

def harmonicEmbedding (k r : ℕ) (f : Function n) : Function n :=
  (Real.sqrt (harmonicNormFactor n k r))⁻¹ • raised f r

def wordHarmonicEmbedding (x : BinaryWord n) (k r : ℕ)
    (f : Function n) : Function n :=
  twist x (harmonicEmbedding k r f)

theorem harmonicEmbedding_isometry {k : ℕ}
    (f g : Function n) (hg : IsHarmonic k g) (r : ℕ)
    (hbound : 2 * k + r ≤ n) :
    dot (harmonicEmbedding k r f) (harmonicEmbedding k r g) =
      dot f g := by
  have hpos : 0 < harmonicNormFactor n k r :=
    harmonicNormFactor_pos hbound
  have hs : Real.sqrt (harmonicNormFactor n k r) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  have hsqr :
      Real.sqrt (harmonicNormFactor n k r) *
          Real.sqrt (harmonicNormFactor n k r) =
        harmonicNormFactor n k r :=
    Real.mul_self_sqrt hpos.le
  have hscalar :
      (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
          (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
            harmonicNormFactor n k r = 1 := by
    calc
      (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
          (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
            harmonicNormFactor n k r =
        (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
          (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
            (Real.sqrt (harmonicNormFactor n k r) *
              Real.sqrt (harmonicNormFactor n k r)) := by rw [hsqr]
      _ = 1 := by field_simp [hs]
  calc
    dot (harmonicEmbedding k r f) (harmonicEmbedding k r g) =
        ((Real.sqrt (harmonicNormFactor n k r))⁻¹ *
          (Real.sqrt (harmonicNormFactor n k r))⁻¹) *
            dot (raised f r) (raised g r) := by
      simp only [harmonicEmbedding, dot_smul_left, dot_smul_right]
      ring
    _ = ((Real.sqrt (harmonicNormFactor n k r))⁻¹ *
          (Real.sqrt (harmonicNormFactor n k r))⁻¹) *
            (harmonicNormFactor n k r * dot f g) := by
      rw [dot_raised_of_harmonic f g hg r]
    _ = ((Real.sqrt (harmonicNormFactor n k r))⁻¹ *
          (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
            harmonicNormFactor n k r) * dot f g := by ring
    _ = dot f g := by rw [hscalar, one_mul]

theorem wordHarmonicEmbedding_isometry {k : ℕ}
    (x : BinaryWord n) (f g : Function n)
    (hg : IsHarmonic k g) (r : ℕ) (hbound : 2 * k + r ≤ n) :
    dot (wordHarmonicEmbedding x k r f)
        (wordHarmonicEmbedding x k r g) = dot f g := by
  unfold wordHarmonicEmbedding
  rw [dot_twist]
  exact harmonicEmbedding_isometry f g hg r hbound

theorem IsLevel.harmonicEmbedding {k : ℕ} {f : Function n}
    (hf : IsLevel k f) (r : ℕ) :
    IsLevel (k + r) (harmonicEmbedding k r f) := by
  intro S hS
  change
    (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
      MetricCodes.Boolean.raised f r S = 0
  rw [(MetricCodes.Boolean.IsLevel.raised hf r) S hS, mul_zero]

theorem IsLevel.wordHarmonicEmbedding {k : ℕ} {f : Function n}
    (hf : IsLevel k f) (x : BinaryWord n) (r : ℕ) :
    IsLevel (k + r) (wordHarmonicEmbedding x k r f) := by
  exact (hf.harmonicEmbedding r).twist x

theorem mem_harmonicLayer_iff {k : ℕ} (f : LayerFunction n k) :
    f ∈ harmonicLayer n k ↔ IsHarmonic k (layerExtend f) := by
  classical
  cases k with
  | zero =>
      constructor
      · intro _
        refine ⟨isLevel_layerExtend f, ?_⟩
        intro S
        unfold lower
        apply Finset.sum_eq_zero
        intro a _
        by_cases ha : a ∈ S
        · simp [lowerAt, ha]
        · have hcard : (insert a S).card ≠ 0 :=
            Finset.card_ne_zero_of_mem (Finset.mem_insert_self a S)
          simp [lowerAt, ha, layerExtend]
      · intro _
        exact Submodule.mem_top
  | succ k =>
      constructor
      · intro hf
        change f ∈ LinearMap.ker (layerDown n k) at hf
        have hdown : layerDown n k f = 0 := LinearMap.mem_ker.mp hf
        refine ⟨isLevel_layerExtend f, ?_⟩
        have hrestrict :
            layerRestrict k (lower (layerExtend f)) = 0 := by
          simpa only [layerDown_apply] using hdown
        have hlower : lower (layerExtend f) = 0 := by
          calc
            lower (layerExtend f) =
                layerExtend (layerRestrict k (lower (layerExtend f))) :=
              (layerExtend_layerRestrict_of_level _
                (isLevel_layerExtend f).lower).symm
            _ = layerExtend (0 : LayerFunction n k) := by rw [hrestrict]
            _ = 0 := by
              change layerExtendLinear n k (0 : LayerFunction n k) = 0
              exact map_zero (layerExtendLinear n k)
        exact fun S => congrFun hlower S
      · intro hf
        change f ∈ LinearMap.ker (layerDown n k)
        apply LinearMap.mem_ker.mpr
        rw [layerDown_apply]
        have hlower : lower (layerExtend f) = 0 := funext hf.2
        rw [hlower]
        change layerRestrictLinear n k (0 : Function n) = 0
        exact map_zero (layerRestrictLinear n k)

abbrev EuclideanLayer (n k : ℕ) := EuclideanSpace ℝ (Level n k)

def harmonicEuclideanLayer (n k : ℕ) :
    Submodule ℝ (EuclideanLayer n k) :=
  (harmonicLayer n k).map
    (WithLp.linearEquiv 2 ℝ (LayerFunction n k)).symm.toLinearMap

theorem harmonicEuclideanLayer_finrank
    (n k : ℕ) (hk : 2 * k ≤ n) :
    Module.finrank ℝ (harmonicEuclideanLayer n k) =
      MetricCodes.hammingFibreDimension n k := by
  calc
    Module.finrank ℝ (harmonicEuclideanLayer n k) =
        Module.finrank ℝ (harmonicLayer n k) := by
      change
        Module.finrank ℝ
            ((harmonicLayer n k).map
              (WithLp.linearEquiv 2 ℝ (LayerFunction n k)).symm.toLinearMap) =
          Module.finrank ℝ (harmonicLayer n k)
      exact
        (WithLp.linearEquiv 2 ℝ (LayerFunction n k)).symm.finrank_map_eq
          (harmonicLayer n k)
    _ = MetricCodes.hammingFibreDimension n k := harmonicLayer_finrank n k hk

def harmonicOrthonormalBasis
    (n k : ℕ) (hk : 2 * k ≤ n) :
    OrthonormalBasis (Fin (MetricCodes.hammingFibreDimension n k)) ℝ
      (harmonicEuclideanLayer n k) :=
  (stdOrthonormalBasis ℝ (harmonicEuclideanLayer n k)).reindex
    (finCongr (harmonicEuclideanLayer_finrank n k hk))

def harmonicBasisFunction
    (n k : ℕ) (hk : 2 * k ≤ n)
    (p : Fin (MetricCodes.hammingFibreDimension n k)) : Function n :=
  layerExtend
    (WithLp.ofLp ((harmonicOrthonormalBasis n k hk p).val))

theorem harmonicBasisFunction_isHarmonic
    (n k : ℕ) (hk : 2 * k ≤ n)
    (p : Fin (MetricCodes.hammingFibreDimension n k)) :
    IsHarmonic k (harmonicBasisFunction n k hk p) := by
  let b := harmonicOrthonormalBasis n k hk p
  have hmem : b.val ∈ harmonicEuclideanLayer n k := b.property
  change
    b.val ∈
      (harmonicLayer n k).map
        (WithLp.linearEquiv 2 ℝ (LayerFunction n k)).symm.toLinearMap
    at hmem
  obtain ⟨g, hg, heq⟩ := (Submodule.mem_map).mp hmem
  have hcoef : WithLp.ofLp b.val = g := by
    have h := congrArg
      (fun z : EuclideanLayer n k => WithLp.ofLp z) heq.symm
    simpa using h
  change IsHarmonic k (layerExtend (WithLp.ofLp b.val))
  apply (mem_harmonicLayer_iff (WithLp.ofLp b.val)).mp
  rw [hcoef]
  exact hg

def hammingWindowDimension (n k L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (L - k + 1), n.choose (k + j)

abbrev HammingWindowIndex (n k L : ℕ) :=
  Σ j : Fin (L - k + 1), Level n (k + j.val)

theorem hammingWindowIndex_card (n k L : ℕ) :
    Fintype.card (HammingWindowIndex n k L) =
      hammingWindowDimension n k L := by
  classical
  rw [Fintype.card_sigma]
  simp only [card_level]
  unfold hammingWindowDimension
  refine Finset.sum_bij (fun j _ => j.val) ?_ ?_ ?_ ?_
  · intro j _
    exact Finset.mem_range.mpr j.isLt
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro j hj
    refine ⟨⟨j, Finset.mem_range.mp hj⟩, Finset.mem_univ _, rfl⟩
  · intro j _
    rfl

def hammingWindowIndexEquiv (n k L : ℕ) :
    HammingWindowIndex n k L ≃ Fin (hammingWindowDimension n k L) :=
  Fintype.equivOfCardEq (by
    simpa using hammingWindowIndex_card n k L)

def hammingRecurrenceWeight
    (n k L : ℕ) (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (j : Fin (L - k + 1)) : ℝ :=
  Real.sqrt (n.choose (k + j.val) : ℝ) * v j

def hammingRecurrenceNormalization
    (n k L : ℕ) (v : EuclideanSpace ℝ (Fin (L - k + 1))) : ℝ :=
  ∑ j : Fin (L - k + 1), hammingRecurrenceWeight n k L v j

def hammingFibreAmplitude
    (n k L : ℕ) (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (j : Fin (L - k + 1)) : ℝ :=
  Real.sqrt
    (hammingRecurrenceWeight n k L v j /
      hammingRecurrenceNormalization n k L v)

theorem hammingRecurrenceWeight_nonneg
    (n k L : ℕ) (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j)
    (j : Fin (L - k + 1)) :
    0 ≤ hammingRecurrenceWeight n k L v j := by
  exact mul_nonneg (Real.sqrt_nonneg _) (hv j)

theorem hammingRecurrenceNormalization_pos
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j) :
    0 < hammingRecurrenceNormalization n k L v := by
  classical
  have hvzero : v ≠ 0 := by
    intro hzero
    simp [hzero] at hunit
  obtain ⟨j, hj⟩ : ∃ j : Fin (L - k + 1), 0 < v j := by
    by_contra hnone
    simp only [not_exists, not_lt] at hnone
    apply hvzero
    apply PiLp.ext
    intro i
    change v i = 0
    exact le_antisymm (hnone i) (hv i)
  have hlevel : k + j.val ≤ n := by
    have hjbound := j.isLt
    omega
  have hdimension : 0 < (n.choose (k + j.val) : ℝ) := by
    exact_mod_cast Nat.choose_pos hlevel
  unfold hammingRecurrenceNormalization
  apply Finset.sum_pos'
  · intro i _
    exact hammingRecurrenceWeight_nonneg n k L v hv i
  · refine ⟨j, Finset.mem_univ j, ?_⟩
    exact mul_pos (Real.sqrt_pos.2 hdimension) hj

theorem hammingFibreAmplitude_sq
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j)
    (j : Fin (L - k + 1)) :
    hammingFibreAmplitude n k L v j ^ 2 =
      hammingRecurrenceWeight n k L v j /
        hammingRecurrenceNormalization n k L v := by
  unfold hammingFibreAmplitude
  apply Real.sq_sqrt
  exact div_nonneg
    (hammingRecurrenceWeight_nonneg n k L v hv j)
    (hammingRecurrenceNormalization_pos hkL hLn v hunit hv).le

theorem hammingFibreAmplitude_sq_sum
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j) :
    (∑ j : Fin (L - k + 1), hammingFibreAmplitude n k L v j ^ 2) =
      1 := by
  simp_rw [hammingFibreAmplitude_sq hkL hLn v hunit hv]
  rw [← Finset.sum_div]
  change
    hammingRecurrenceNormalization n k L v /
      hammingRecurrenceNormalization n k L v = 1
  exact div_self
    (hammingRecurrenceNormalization_pos hkL hLn v hunit hv).ne'

theorem harmonicBasisFunction_dot
    (n k : ℕ) (hk : 2 * k ≤ n)
    (p q : Fin (MetricCodes.hammingFibreDimension n k)) :
    dot (harmonicBasisFunction n k hk p)
        (harmonicBasisFunction n k hk q) =
      if p = q then 1 else 0 := by
  classical
  unfold harmonicBasisFunction
  rw [dot_layerExtend]
  have h := (harmonicOrthonormalBasis n k hk).inner_eq_ite p q
  simpa [layerDot, PiLp.inner_apply, Real.inner_apply, mul_comm] using h

theorem dot_eq_layerDot_of_level {i : ℕ}
    (f g : Function n) (hf : IsLevel i f) (hg : IsLevel i g) :
    dot f g = layerDot (layerRestrict i f) (layerRestrict i g) := by
  rw [← dot_layerExtend,
    layerExtend_layerRestrict_of_level f hf,
    layerExtend_layerRestrict_of_level g hg]

def hammingWindowFibreMatrix
    (n k L : ℕ) (hk : 2 * k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (x : BinaryWord n) :
    Matrix (HammingWindowIndex n k L)
      (Fin (MetricCodes.hammingFibreDimension n k)) ℝ :=
  fun T p =>
    hammingFibreAmplitude n k L v T.1 *
      wordHarmonicEmbedding x k T.1.val
        (harmonicBasisFunction n k hk p) T.2.val

theorem hammingWindowFibreMatrix_transpose_mul
    {n k L : ℕ} (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j)
    (x : BinaryWord n) :
    (hammingWindowFibreMatrix n k L hk v x)ᵀ *
        hammingWindowFibreMatrix n k L hk v x = 1 := by
  classical
  ext p q
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  change
    (∑ T : HammingWindowIndex n k L,
      hammingWindowFibreMatrix n k L hk v x T p *
        hammingWindowFibreMatrix n k L hk v x T q) =
      if p = q then 1 else 0
  calc
    (∑ T : HammingWindowIndex n k L,
      hammingWindowFibreMatrix n k L hk v x T p *
        hammingWindowFibreMatrix n k L hk v x T q) =
      ∑ j : Fin (L - k + 1),
        hammingFibreAmplitude n k L v j ^ 2 *
          dot
            (wordHarmonicEmbedding x k j.val
              (harmonicBasisFunction n k hk p))
            (wordHarmonicEmbedding x k j.val
              (harmonicBasisFunction n k hk q)) := by
        simp only [hammingWindowFibreMatrix]
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro j _
        change
          (∑ S : Level n (k + j.val),
            (hammingFibreAmplitude n k L v j *
              wordHarmonicEmbedding x k j.val
                (harmonicBasisFunction n k hk p) S.val) *
            (hammingFibreAmplitude n k L v j *
              wordHarmonicEmbedding x k j.val
                (harmonicBasisFunction n k hk q) S.val)) =
            hammingFibreAmplitude n k L v j ^ 2 *
              dot
                (wordHarmonicEmbedding x k j.val
                  (harmonicBasisFunction n k hk p))
                (wordHarmonicEmbedding x k j.val
                  (harmonicBasisFunction n k hk q))
        calc
          (∑ S : Level n (k + j.val),
            (hammingFibreAmplitude n k L v j *
              wordHarmonicEmbedding x k j.val
                (harmonicBasisFunction n k hk p) S.val) *
            (hammingFibreAmplitude n k L v j *
              wordHarmonicEmbedding x k j.val
                (harmonicBasisFunction n k hk q) S.val)) =
              hammingFibreAmplitude n k L v j ^ 2 *
                (∑ S : Level n (k + j.val),
                  wordHarmonicEmbedding x k j.val
                    (harmonicBasisFunction n k hk p) S.val *
                  wordHarmonicEmbedding x k j.val
                    (harmonicBasisFunction n k hk q) S.val) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro S _
                ring
          _ = hammingFibreAmplitude n k L v j ^ 2 *
              dot
                (wordHarmonicEmbedding x k j.val
                  (harmonicBasisFunction n k hk p))
                (wordHarmonicEmbedding x k j.val
                  (harmonicBasisFunction n k hk q)) := by
                congr 1
                exact
                  (dot_eq_layerDot_of_level
                    (wordHarmonicEmbedding x k j.val
                      (harmonicBasisFunction n k hk p))
                    (wordHarmonicEmbedding x k j.val
                      (harmonicBasisFunction n k hk q))
                    (MetricCodes.Boolean.IsLevel.wordHarmonicEmbedding
                      (harmonicBasisFunction_isHarmonic n k hk p).1
                      x j.val)
                    (MetricCodes.Boolean.IsLevel.wordHarmonicEmbedding
                      (harmonicBasisFunction_isHarmonic n k hk q).1
                      x j.val)).symm
    _ = ∑ j : Fin (L - k + 1),
          hammingFibreAmplitude n k L v j ^ 2 *
            (if p = q then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        have hjbound : 2 * k + j.val ≤ n := by
          have hj := j.isLt
          omega
        rw [wordHarmonicEmbedding_isometry x
          (harmonicBasisFunction n k hk p)
          (harmonicBasisFunction n k hk q)
          (harmonicBasisFunction_isHarmonic n k hk q)
          j.val hjbound, harmonicBasisFunction_dot]
    _ = (if p = q then 1 else 0) := by
        by_cases hpq : p = q
        · simp [hpq, hammingFibreAmplitude_sq_sum hkL hLn v hunit hv]
        · simp [hpq]

def hammingFibreMatrix
    (n k L : ℕ) (hk : 2 * k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (x : BinaryWord n) :
    Matrix (Fin (hammingWindowDimension n k L))
      (Fin (MetricCodes.hammingFibreDimension n k)) ℝ :=
  fun i p =>
    hammingWindowFibreMatrix n k L hk v x
      ((hammingWindowIndexEquiv n k L).symm i) p

theorem hammingFibreMatrix_transpose_mul
    {n k L : ℕ} (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j)
    (x : BinaryWord n) :
    (hammingFibreMatrix n k L hk v x)ᵀ *
        hammingFibreMatrix n k L hk v x = 1 := by
  classical
  ext p q
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  change
    (∑ i : Fin (hammingWindowDimension n k L),
      hammingWindowFibreMatrix n k L hk v x
        ((hammingWindowIndexEquiv n k L).symm i) p *
      hammingWindowFibreMatrix n k L hk v x
        ((hammingWindowIndexEquiv n k L).symm i) q) =
      if p = q then 1 else 0
  calc
    (∑ i : Fin (hammingWindowDimension n k L),
      hammingWindowFibreMatrix n k L hk v x
        ((hammingWindowIndexEquiv n k L).symm i) p *
      hammingWindowFibreMatrix n k L hk v x
        ((hammingWindowIndexEquiv n k L).symm i) q) =
      ∑ T : HammingWindowIndex n k L,
        hammingWindowFibreMatrix n k L hk v x T p *
          hammingWindowFibreMatrix n k L hk v x T q :=
        (hammingWindowIndexEquiv n k L).symm.sum_comp
          (fun T =>
            hammingWindowFibreMatrix n k L hk v x T p *
              hammingWindowFibreMatrix n k L hk v x T q)
    _ = (if p = q then 1 else 0) := by
        have h := congrArg
          (fun M : Matrix
              (Fin (MetricCodes.hammingFibreDimension n k))
              (Fin (MetricCodes.hammingFibreDimension n k)) ℝ => M p q)
          (hammingWindowFibreMatrix_transpose_mul
            hk hkL hLn v hunit hv x)
        simpa [Matrix.mul_apply, Matrix.transpose_apply,
          Matrix.one_apply] using h

def hammingProjectionFamily
    {n k L : ℕ} (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j) :
    MetricCodes.ProjectionFamily (BinaryWord n)
      (hammingWindowDimension n k L)
      (MetricCodes.hammingFibreDimension n k) where
  projection x :=
    hammingFibreMatrix n k L hk v x *
      (hammingFibreMatrix n k L hk v x)ᵀ
  symmetric x := by
    simp [Matrix.transpose_mul]
  idempotent x := by
    let A := hammingFibreMatrix n k L hk v x
    change (A * Aᵀ) * (A * Aᵀ) = A * Aᵀ
    calc
      (A * Aᵀ) * (A * Aᵀ) = A * ((Aᵀ * A) * Aᵀ) := by
        simp [Matrix.mul_assoc]
      _ = A * Aᵀ := by
        rw [hammingFibreMatrix_transpose_mul hk hkL hLn
          v hunit hv x, Matrix.one_mul]
  trace_eq x := by
    rw [Matrix.trace_mul_comm,
      hammingFibreMatrix_transpose_mul hk hkL hLn v hunit hv x]
    simp

theorem sign_mul_eq_difference_indicator (b c : Bool) :
    sign b * sign c =
      1 - 2 * (if b ≠ c then (1 : ℝ) else 0) := by
  cases b <;> cases c <;> norm_num [sign]

theorem sum_sign_mul_eq_hammingDist
    (x y : BinaryWord n) :
    (∑ a : Fin n, sign (x a) * sign (y a)) =
      (n : ℝ) - 2 * (MetricCodes.hammingDist x y : ℝ) := by
  classical
  calc
    (∑ a : Fin n, sign (x a) * sign (y a)) =
        ∑ a : Fin n,
          (1 - 2 * (if x a ≠ y a then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact sign_mul_eq_difference_indicator (x a) (y a)
    _ = (n : ℝ) - 2 * (MetricCodes.hammingDist x y : ℝ) := by
      have hcount :
          (∑ a : Fin n,
            if x a ≠ y a then (1 : ℝ) else 0) =
              (MetricCodes.hammingDist x y : ℝ) := by
        simpa only [MetricCodes.hammingDist] using
          (Finset.sum_boole (R := ℝ)
            (fun a : Fin n => x a ≠ y a)
            (Finset.univ : Finset (Fin n)))
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hcount]
      simp

def hammingAxis (x : BinaryWord n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2
    (fun a : Fin n => (Real.sqrt (n : ℝ))⁻¹ * sign (x a))

theorem hammingAxis_inner {n : ℕ} (hn : 0 < n)
    (x y : BinaryWord n) :
    @inner ℝ (EuclideanSpace ℝ (Fin n)) _
      (hammingAxis x) (hammingAxis y) =
        MetricCodes.hammingCorrelation x y := by
  classical
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hs :
      Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt hn'.le
  have hsne : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr hn').ne'
  calc
    @inner ℝ (EuclideanSpace ℝ (Fin n)) _
        (hammingAxis x) (hammingAxis y) =
      ∑ a : Fin n,
        ((Real.sqrt (n : ℝ))⁻¹ * sign (x a)) *
          ((Real.sqrt (n : ℝ))⁻¹ * sign (y a)) := by
        rw [PiLp.inner_apply]
        apply Finset.sum_congr rfl
        intro a _
        simp [hammingAxis, mul_comm]
    _ = ((Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt (n : ℝ))⁻¹) *
        (∑ a : Fin n, sign (x a) * sign (y a)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ = ((Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt (n : ℝ))⁻¹) *
        ((n : ℝ) - 2 * (MetricCodes.hammingDist x y : ℝ)) := by
        rw [sum_sign_mul_eq_hammingDist]
    _ = MetricCodes.hammingCorrelation x y := by
        unfold MetricCodes.hammingCorrelation
        field_simp [hsne, hn'.ne'] ; nlinarith [hs]

theorem character_insert
    (x : BinaryWord n) (a : Fin n) (S : Finset (Fin n))
    (ha : a ∉ S) :
    character x (insert a S) = sign (x a) * character x S := by
  classical
  simp [character, ha]

theorem character_erase
    (x : BinaryWord n) (a : Fin n) (S : Finset (Fin n))
    (ha : a ∈ S) :
    character x S = sign (x a) * character x (S.erase a) := by
  have h := character_insert x a (S.erase a)
    (by simp)
  simpa [Finset.insert_erase ha] using h

theorem lowerAt_twist
    (x : BinaryWord n) (a : Fin n) (f : Function n) :
    lowerAt a (twist x f) =
      sign (x a) • twist x (lowerAt a f) := by
  classical
  funext S
  by_cases ha : a ∈ S
  · simp [lowerAt, ha, twist]
  · simp [lowerAt, ha, twist, character_insert x a S ha,
      mul_assoc]

theorem raiseAt_twist
    (x : BinaryWord n) (a : Fin n) (f : Function n) :
    raiseAt a (twist x f) =
      sign (x a) • twist x (raiseAt a f) := by
  classical
  funext S
  by_cases ha : a ∈ S
  · simp only [raiseAt, ha, ite_true, twist,
      Pi.smul_apply, smul_eq_mul]
    rw [character_erase x a S ha]
    calc
      character x (S.erase a) * f (S.erase a) =
          (sign (x a) * sign (x a)) *
            (character x (S.erase a) * f (S.erase a)) := by
        rw [sign_mul_self, one_mul]
      _ = sign (x a) *
          ((sign (x a) * character x (S.erase a)) *
            f (S.erase a)) := by
        ring
  · simp [raiseAt, ha, twist]

def matrixHilbertSchmidtFeature
    {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (A : Matrix ι ρ ℝ) : EuclideanSpace ℝ (ι × ρ) :=
  WithLp.toLp 2 (fun p : ι × ρ => A p.1 p.2)

theorem matrixHilbertSchmidtFeature_inner
    {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (A B : Matrix ι ρ ℝ) :
    @inner ℝ (EuclideanSpace ℝ (ι × ρ)) _
      (matrixHilbertSchmidtFeature A)
      (matrixHilbertSchmidtFeature B) =
        Matrix.trace (Aᵀ * B) := by
  classical
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp only [matrixHilbertSchmidtFeature, Real.inner_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]

@[simp] theorem matrixHilbertSchmidtFeature_sub
    {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (A B : Matrix ι ρ ℝ) :
    matrixHilbertSchmidtFeature (A - B) =
      matrixHilbertSchmidtFeature A -
        matrixHilbertSchmidtFeature B := by
  apply PiLp.ext
  intro p
  rfl

@[simp] theorem matrixHilbertSchmidtFeature_smul
    {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (c : ℝ) (A : Matrix ι ρ ℝ) :
    matrixHilbertSchmidtFeature (c • A) =
      c • matrixHilbertSchmidtFeature A := by
  apply PiLp.ext
  intro p
  rfl

def matrixAxisLift {κ ι ρ : Type*}
    (z : κ → ℝ) (A : Matrix ι ρ ℝ) :
    Matrix (κ × ι) ρ ℝ :=
  fun p j => z p.1 * A p.2 j

theorem matrixAxisLift_transpose_mul
    {κ ι ρ : Type*} [Fintype κ] [Fintype ι] [Fintype ρ]
    (z w : κ → ℝ) (A B : Matrix ι ρ ℝ) :
    (matrixAxisLift z A)ᵀ * matrixAxisLift w B =
      (∑ a : κ, z a * w a) • (Aᵀ * B) := by
  classical
  ext i j
  change
    (∑ p : κ × ι,
      (z p.1 * A p.2 i) * (w p.1 * B p.2 j)) =
      (∑ a : κ, z a * w a) *
        (∑ r : ι, A r i * B r j)
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

def matrixAxisResidual
    {X κ : Type*} [Fintype κ] {D d : ℕ}
    (P : MetricCodes.ProjectionFamily X D d)
    (axis : X → κ → ℝ)
    (B : Matrix (κ × Fin D) (Fin D) ℝ)
    (c : ℝ) (x : X) :
    Matrix (κ × Fin D) (Fin D) ℝ :=
  matrixAxisLift (axis x) (P.projection x) -
    c • (B * P.projection x)

def matrixAxisGramFeature
    {X κ : Type*} [Fintype κ] {D d : ℕ}
    (P : MetricCodes.ProjectionFamily X D d)
    (axis : X → κ → ℝ)
    (B : Matrix (κ × Fin D) (Fin D) ℝ)
    (c : ℝ) (x : X) :
    EuclideanSpace ℝ ((κ × Fin D) × Fin D) :=
  matrixHilbertSchmidtFeature (matrixAxisResidual P axis B c x)

theorem matrixAxisResidual_gram
    {X κ : Type*} [Fintype κ] {D d : ℕ}
    (P : MetricCodes.ProjectionFamily X D d)
    (axis : X → κ → ℝ)
    (B : Matrix (κ × Fin D) (Fin D) ℝ)
    (c lam : ℝ)
    (hB : Bᵀ * B = 1)
    (haxis : ∀ x : X,
      Bᵀ * matrixAxisLift (axis x) (P.projection x) =
        c • P.projection x)
    (hsq : c ^ 2 = lam)
    (x y : X) :
    @inner ℝ (EuclideanSpace ℝ ((κ × Fin D) × Fin D)) _
      (matrixAxisGramFeature P axis B c x)
      (matrixAxisGramFeature P axis B c y) =
        ((∑ a : κ, axis x a * axis y a) - lam) *
          P.overlap x y := by
  classical
  let Lx : Matrix (κ × Fin D) (Fin D) ℝ :=
    matrixAxisLift (axis x) (P.projection x)
  let Ly : Matrix (κ × Fin D) (Fin D) ℝ :=
    matrixAxisLift (axis y) (P.projection y)
  let Gx : Matrix (κ × Fin D) (Fin D) ℝ :=
    B * P.projection x
  let Gy : Matrix (κ × Fin D) (Fin D) ℝ :=
    B * P.projection y
  have haxisx : Bᵀ * Lx = c • P.projection x := by
    simpa only [Lx] using haxis x
  have haxisy : Bᵀ * Ly = c • P.projection y := by
    simpa only [Ly] using haxis y
  have hleft : Lxᵀ * B = c • P.projection x := by
    calc
      Lxᵀ * B = (Bᵀ * Lx)ᵀ := by
        simp [Matrix.transpose_mul]
      _ = (c • P.projection x)ᵀ := by rw [haxisx]
      _ = c • P.projection x := by
        rw [Matrix.transpose_smul, P.symmetric x]
  have hLL :
      @inner ℝ (EuclideanSpace ℝ ((κ × Fin D) × Fin D)) _
        (matrixHilbertSchmidtFeature Lx)
        (matrixHilbertSchmidtFeature Ly) =
          (∑ a : κ, axis x a * axis y a) * P.overlap x y := by
    dsimp [Lx, Ly]
    rw [matrixHilbertSchmidtFeature_inner,
      matrixAxisLift_transpose_mul, P.symmetric x,
      Matrix.trace_smul]
    simp [MetricCodes.ProjectionFamily.overlap]
  have hLG :
      @inner ℝ (EuclideanSpace ℝ ((κ × Fin D) × Fin D)) _
        (matrixHilbertSchmidtFeature Lx)
        (matrixHilbertSchmidtFeature Gy) =
          c * P.overlap x y := by
    rw [matrixHilbertSchmidtFeature_inner]
    dsimp [Gy]
    rw [← Matrix.mul_assoc, hleft]
    simp [MetricCodes.ProjectionFamily.overlap]
  have hGL :
      @inner ℝ (EuclideanSpace ℝ ((κ × Fin D) × Fin D)) _
        (matrixHilbertSchmidtFeature Gx)
        (matrixHilbertSchmidtFeature Ly) =
          c * P.overlap x y := by
    rw [matrixHilbertSchmidtFeature_inner]
    dsimp [Gx]
    rw [Matrix.transpose_mul, P.symmetric x,
      Matrix.mul_assoc, haxisy]
    simp [MetricCodes.ProjectionFamily.overlap]
  have hGG :
      @inner ℝ (EuclideanSpace ℝ ((κ × Fin D) × Fin D)) _
        (matrixHilbertSchmidtFeature Gx)
        (matrixHilbertSchmidtFeature Gy) =
          P.overlap x y := by
    rw [matrixHilbertSchmidtFeature_inner]
    dsimp [Gx, Gy]
    rw [Matrix.transpose_mul, P.symmetric x]
    change
      Matrix.trace
        ((P.projection x * Bᵀ) * (B * P.projection y)) =
          P.overlap x y
    calc
      Matrix.trace
          ((P.projection x * Bᵀ) * (B * P.projection y)) =
        Matrix.trace
          (P.projection x * ((Bᵀ * B) * P.projection y)) := by
            congr 1
            simp [Matrix.mul_assoc]
      _ = P.overlap x y := by
        rw [hB, Matrix.one_mul]
        rfl
  change
    @inner ℝ (EuclideanSpace ℝ ((κ × Fin D) × Fin D)) _
      (matrixHilbertSchmidtFeature (Lx - c • Gx))
      (matrixHilbertSchmidtFeature (Ly - c • Gy)) =
        ((∑ a : κ, axis x a * axis y a) - lam) *
          P.overlap x y
  simp only [matrixHilbertSchmidtFeature_sub,
    matrixHilbertSchmidtFeature_smul,
    inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right,
    hLL, hLG, hGL, hGG]
  rw [← hsq]
  ring

@[simp] theorem harmonicNormFactor_succ (n k r : ℕ) :
    harmonicNormFactor n k (r + 1) =
      harmonicNormFactor n k r * harmonicCoefficient n k (r + 1) := by
  simp [harmonicNormFactor, Finset.prod_range_succ]

theorem raise_harmonicEmbedding {k : ℕ}
    (f : Function n) (r : ℕ)
    (hbound : 2 * k + (r + 1) ≤ n) :
    raise (harmonicEmbedding k r f) =
      Real.sqrt (harmonicCoefficient n k (r + 1)) •
        harmonicEmbedding k (r + 1) f := by
  have hfactor : 0 < harmonicNormFactor n k r :=
    harmonicNormFactor_pos (by omega)
  have hcoefficient : 0 < harmonicCoefficient n k (r + 1) :=
    harmonicCoefficient_pos (by omega) hbound
  have hfactorne : Real.sqrt (harmonicNormFactor n k r) ≠ 0 :=
    (Real.sqrt_pos.mpr hfactor).ne'
  have hcoefficientne :
      Real.sqrt (harmonicCoefficient n k (r + 1)) ≠ 0 :=
    (Real.sqrt_pos.mpr hcoefficient).ne'
  unfold harmonicEmbedding
  rw [raise_smul, ← raised_succ, smul_smul,
    harmonicNormFactor_succ, Real.sqrt_mul hfactor.le]
  congr 1
  field_simp [hfactorne, hcoefficientne]

theorem lower_harmonicEmbedding {k : ℕ}
    (f : Function n) (hf : IsHarmonic k f) (r : ℕ)
    (hbound : 2 * k + (r + 1) ≤ n) :
    lower (harmonicEmbedding k (r + 1) f) =
      Real.sqrt (harmonicCoefficient n k (r + 1)) •
        harmonicEmbedding k r f := by
  have hfactor : 0 < harmonicNormFactor n k r :=
    harmonicNormFactor_pos (by omega)
  have hcoefficient : 0 < harmonicCoefficient n k (r + 1) :=
    harmonicCoefficient_pos (by omega) hbound
  have hfactorne : Real.sqrt (harmonicNormFactor n k r) ≠ 0 :=
    (Real.sqrt_pos.mpr hfactor).ne'
  have hcoefficientne :
      Real.sqrt (harmonicCoefficient n k (r + 1)) ≠ 0 :=
    (Real.sqrt_pos.mpr hcoefficient).ne'
  unfold harmonicEmbedding
  rw [lower_smul, lower_raised_succ_of_harmonic f hf r,
    smul_smul, smul_smul, harmonicNormFactor_succ,
    Real.sqrt_mul hfactor.le]
  congr 1
  field_simp [hfactorne, hcoefficientne] ;
    nlinarith [Real.sq_sqrt hcoefficient.le]

def hammingSourceChannelCoefficient
    (n k L : ℕ)
    (m i : Fin (L - k + 1)) : ℝ :=
  MetricCodes.hammingJacobiMatrix n k L m i *
    Real.sqrt (n.choose (k + m.val) : ℝ) /
      Real.sqrt (n.choose (k + i.val) : ℝ)

theorem hammingSourceChannelCoefficient_mul_sqrt_choose
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (m i : Fin (L - k + 1)) :
    hammingSourceChannelCoefficient n k L m i *
        Real.sqrt (n.choose (k + i.val) : ℝ) =
      MetricCodes.hammingJacobiMatrix n k L m i *
        Real.sqrt (n.choose (k + m.val) : ℝ) := by
  have hi := i.isLt
  have hlevel : k + i.val ≤ n := by omega
  have hchoose : 0 < (n.choose (k + i.val) : ℝ) := by
    exact_mod_cast Nat.choose_pos hlevel
  have hsqrt : Real.sqrt (n.choose (k + i.val) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr hchoose).ne'
  unfold hammingSourceChannelCoefficient
  field_simp [hsqrt]

theorem hammingSourceChannelCoefficient_nonneg
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (m i : Fin (L - k + 1)) :
    0 ≤ hammingSourceChannelCoefficient n k L m i := by
  have hm := m.isLt
  have hi := i.isLt
  have hentry : 0 ≤ MetricCodes.hammingJacobiMatrix n k L m i := by
    unfold MetricCodes.hammingJacobiMatrix
    split_ifs with hforward hbackward
    · exact (MetricCodes.hammingJacobiEntry_pos hn
        (by omega) (by omega)).le
    · exact (MetricCodes.hammingJacobiEntry_pos hn
        (by omega) (by omega)).le
    · exact le_rfl
  unfold hammingSourceChannelCoefficient
  exact div_nonneg
    (mul_nonneg hentry (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

theorem hammingRecurrenceWeight_eigenrecurrence
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1))) (lam : ℝ)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (m : Fin (L - k + 1)) :
    (∑ i : Fin (L - k + 1),
      hammingSourceChannelCoefficient n k L m i *
        hammingRecurrenceWeight n k L v i) =
      lam * hammingRecurrenceWeight n k L v m := by
  classical
  have hcoordinate := congrArg
    (fun z : EuclideanSpace ℝ (Fin (L - k + 1)) => z m)
      heigen
  change
    (∑ i : Fin (L - k + 1),
      MetricCodes.hammingJacobiMatrix n k L m i * v i) =
      lam * v m at hcoordinate
  calc
    (∑ i : Fin (L - k + 1),
      hammingSourceChannelCoefficient n k L m i *
        hammingRecurrenceWeight n k L v i) =
      ∑ i : Fin (L - k + 1),
        (MetricCodes.hammingJacobiMatrix n k L m i * v i) *
          Real.sqrt (n.choose (k + m.val) : ℝ) := by
            apply Finset.sum_congr rfl
            intro i _
            unfold hammingRecurrenceWeight
            have h := hammingSourceChannelCoefficient_mul_sqrt_choose
              hkL hLn m i
            calc
              hammingSourceChannelCoefficient n k L m i *
                  (Real.sqrt (n.choose (k + i.val) : ℝ) * v i) =
                (hammingSourceChannelCoefficient n k L m i *
                  Real.sqrt (n.choose (k + i.val) : ℝ)) * v i := by
                    ring
              _ = (MetricCodes.hammingJacobiMatrix n k L m i *
                    Real.sqrt (n.choose (k + m.val) : ℝ)) * v i := by
                      rw [h]
              _ = (MetricCodes.hammingJacobiMatrix n k L m i * v i) *
                    Real.sqrt (n.choose (k + m.val) : ℝ) := by
                      ring
    _ = (∑ i : Fin (L - k + 1),
          MetricCodes.hammingJacobiMatrix n k L m i * v i) *
        Real.sqrt (n.choose (k + m.val) : ℝ) := by
          rw [Finset.sum_mul]
    _ = lam * hammingRecurrenceWeight n k L v m := by
          rw [hcoordinate]
          unfold hammingRecurrenceWeight
          ring

theorem hammingRecurrenceWeight_pos_of_pos
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (i : Fin (L - k + 1)) :
    0 < hammingRecurrenceWeight n k L v i := by
  have hi := i.isLt
  unfold hammingRecurrenceWeight
  apply mul_pos
  · apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (show k + i.val ≤ n by omega)
  · exact hv i

theorem hammingFibreAmplitude_pos_of_pos
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (i : Fin (L - k + 1)) :
    0 < hammingFibreAmplitude n k L v i := by
  unfold hammingFibreAmplitude
  apply Real.sqrt_pos.mpr
  exact div_pos
    (hammingRecurrenceWeight_pos_of_pos hkL hLn v hv i)
    (hammingRecurrenceNormalization_pos hkL hLn v hunit
      (fun j => (hv j).le))

def hammingAdjacentBlockCoefficient
    (n k L : ℕ)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (lam : ℝ)
    (target source : Fin (L - k + 1)) : ℝ :=
  Real.sqrt
    (hammingSourceChannelCoefficient n k L source target *
      hammingRecurrenceWeight n k L v target /
        (lam * hammingRecurrenceWeight n k L v source))

theorem hammingAdjacentBlockCoefficient_sq
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (target source : Fin (L - k + 1)) :
    hammingAdjacentBlockCoefficient n k L v lam target source ^ 2 =
      hammingSourceChannelCoefficient n k L source target *
        hammingRecurrenceWeight n k L v target /
          (lam * hammingRecurrenceWeight n k L v source) := by
  unfold hammingAdjacentBlockCoefficient
  apply Real.sq_sqrt
  exact div_nonneg
    (mul_nonneg
      (hammingSourceChannelCoefficient_nonneg hn hkL hLn
        source target)
      (hammingRecurrenceWeight_pos_of_pos hkL hLn v hv target).le)
    (mul_pos hlam
      (hammingRecurrenceWeight_pos_of_pos hkL hLn v hv source)).le

theorem hammingAdjacentBlockCoefficient_sq_sum
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (source : Fin (L - k + 1)) :
    (∑ target : Fin (L - k + 1),
      hammingAdjacentBlockCoefficient n k L v lam target source ^ 2) =
      1 := by
  classical
  simp_rw [hammingAdjacentBlockCoefficient_sq
    hn hkL hLn v hv lam hlam]
  rw [← Finset.sum_div,
    hammingRecurrenceWeight_eigenrecurrence
      hkL hLn v lam heigen source]
  exact div_self
    (mul_pos hlam
      (hammingRecurrenceWeight_pos_of_pos hkL hLn v hv source)).ne'

theorem hammingAdjacentBlockCoefficient_amplitude_identity
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (target source : Fin (L - k + 1)) :
    hammingAdjacentBlockCoefficient n k L v lam target source *
        hammingFibreAmplitude n k L v target *
        Real.sqrt
          (hammingSourceChannelCoefficient n k L source target) =
      hammingAdjacentBlockCoefficient n k L v lam target source ^ 2 *
        Real.sqrt lam * hammingFibreAmplitude n k L v source := by
  have hcoefficient :=
    hammingSourceChannelCoefficient_nonneg hn hkL hLn source target
  have hsource :=
    hammingRecurrenceWeight_pos_of_pos hkL hLn v hv source
  have hnormal := hammingRecurrenceNormalization_pos
    hkL hLn v hunit (fun i => (hv i).le)
  have hleft :
      0 ≤ hammingAdjacentBlockCoefficient n k L v lam target source *
        hammingFibreAmplitude n k L v target *
        Real.sqrt
          (hammingSourceChannelCoefficient n k L source target) := by
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _)
        (hammingFibreAmplitude_pos_of_pos
          hkL hLn v hunit hv target).le)
      (Real.sqrt_nonneg _)
  have hright :
      0 ≤ hammingAdjacentBlockCoefficient n k L v lam target source ^ 2 *
        Real.sqrt lam * hammingFibreAmplitude n k L v source := by
    exact mul_nonneg
      (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
      (hammingFibreAmplitude_pos_of_pos
        hkL hLn v hunit hv source).le
  have hsquare :
      (hammingAdjacentBlockCoefficient n k L v lam target source *
        hammingFibreAmplitude n k L v target *
        Real.sqrt
          (hammingSourceChannelCoefficient n k L source target)) ^ 2 =
      (hammingAdjacentBlockCoefficient n k L v lam target source ^ 2 *
        Real.sqrt lam * hammingFibreAmplitude n k L v source) ^ 2 := by
    simp only [mul_pow]
    rw [hammingAdjacentBlockCoefficient_sq
      hn hkL hLn v hv lam hlam target source,
      hammingFibreAmplitude_sq
        hkL hLn v hunit (fun i => (hv i).le) target,
      Real.sq_sqrt hcoefficient,
      Real.sq_sqrt hlam.le,
      hammingFibreAmplitude_sq
        hkL hLn v hunit (fun i => (hv i).le) source]
    field_simp [hlam.ne', hsource.ne', hnormal.ne']
  nlinarith

theorem hammingAdjacentBlockCoefficient_amplitude_sum
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (source : Fin (L - k + 1)) :
    (∑ target : Fin (L - k + 1),
      hammingAdjacentBlockCoefficient n k L v lam target source *
        hammingFibreAmplitude n k L v target *
        Real.sqrt
          (hammingSourceChannelCoefficient n k L source target)) =
      Real.sqrt lam * hammingFibreAmplitude n k L v source := by
  simp_rw [hammingAdjacentBlockCoefficient_amplitude_identity
    hn hkL hLn v hunit hv lam hlam]
  rw [← Finset.sum_mul, ← Finset.sum_mul,
    hammingAdjacentBlockCoefficient_sq_sum
      hn hkL hLn v hv lam hlam heigen source]
  simp

theorem IsLevel.smul {i : ℕ} {f : Function n}
    (hf : IsLevel i f) (c : ℝ) : IsLevel i (c • f) := by
  intro S hS
  change c * f S = 0
  rw [hf S hS, mul_zero]

theorem IsLevel.lowerAt {i : ℕ} {f : Function n}
    (hf : IsLevel (i + 1) f) (a : Fin n) :
    IsLevel i (MetricCodes.Boolean.lowerAt a f) := by
  classical
  intro S hS
  by_cases ha : a ∈ S
  · change (if a ∈ S then 0 else f (insert a S)) = 0
    rw [if_pos ha]
  · have hinsert : (insert a S).card ≠ i + 1 := by
      intro hcard
      apply hS
      have hinsertcard := Finset.card_insert_of_notMem ha
      omega
    change (if a ∈ S then 0 else f (insert a S)) = 0
    rw [if_neg ha, hf (insert a S) hinsert]

theorem IsLevel.raiseAt {i : ℕ} {f : Function n}
    (hf : IsLevel i f) (a : Fin n) :
    IsLevel (i + 1) (MetricCodes.Boolean.raiseAt a f) := by
  classical
  intro S hS
  by_cases ha : a ∈ S
  · have herase : (S.erase a).card ≠ i := by
      intro hcard
      apply hS
      have herasecard := Finset.card_erase_add_one ha
      omega
    change (if a ∈ S then f (S.erase a) else 0) = 0
    rw [if_pos ha, hf (S.erase a) herase]
  · change (if a ∈ S then f (S.erase a) else 0) = 0
    rw [if_neg ha]

def hammingWindowBasis (n k L : ℕ)
    (T : HammingWindowIndex n k L) : Function n :=
  fun S => if S = T.2.val then 1 else 0

theorem isLevel_hammingWindowBasis (n k L : ℕ)
    (T : HammingWindowIndex n k L) :
    IsLevel (k + T.1.val) (hammingWindowBasis n k L T) := by
  classical
  intro S hS
  unfold hammingWindowBasis
  split_ifs with heq
  · subst S
    exact False.elim (hS T.2.property)
  · rfl

theorem dot_hammingWindowBasis (n k L : ℕ)
    (S T : HammingWindowIndex n k L) :
    dot (hammingWindowBasis n k L S)
        (hammingWindowBasis n k L T) =
      if S.2.val = T.2.val then 1 else 0 := by
  classical
  by_cases h : S.2.val = T.2.val
  · unfold dot hammingWindowBasis
    rw [if_pos h, Finset.sum_eq_single S.2.val]
    · rw [if_pos rfl, if_pos h]
      norm_num
    · intro U _ hU
      rw [if_neg hU, zero_mul]
    · simp
  · have h' : T.2.val ≠ S.2.val := Ne.symm h
    simp [dot, hammingWindowBasis, h, h']

def hammingAdjacentChannel (n k L : ℕ)
    (target source : Fin (L - k + 1))
    (f : Function n) : CoordinateFunction n :=
  if target.val + 1 = source.val then
    deleteChannel (k + source.val) f
  else if source.val + 1 = target.val then
    addChannel (k + source.val) f
  else
    0

theorem coordinateDot_comm (f g : CoordinateFunction n) :
    coordinateDot f g = coordinateDot g f := by
  classical
  unfold coordinateDot
  apply Finset.sum_congr rfl
  intro a _
  exact dot_comm (f a) (g a)

theorem hammingAdjacentChannel_isometry
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (target source : Fin (L - k + 1))
    (hadjacent : target.val + 1 = source.val ∨
      source.val + 1 = target.val)
    (f g : Function n) (hf : IsLevel (k + source.val) f) :
    coordinateDot
      (hammingAdjacentChannel n k L target source f)
      (hammingAdjacentChannel n k L target source g) =
      dot f g := by
  have hs := source.isLt
  have ht := target.isLt
  rcases hadjacent with hdelete | hadd
  · simp only [hammingAdjacentChannel, hdelete, ↓reduceIte]
    exact deleteChannel_isometry (by omega) f g hf
  · have hnot : target.val + 1 ≠ source.val := by omega
    simp only [hammingAdjacentChannel, hnot, hadd, ↓reduceIte]
    exact addChannel_isometry (by omega) f g hf

theorem hammingAdjacentChannel_orthogonal
    (n k L : ℕ)
    (target source other : Fin (L - k + 1))
    (hne : source ≠ other)
    (f g : Function n) :
    coordinateDot
      (hammingAdjacentChannel n k L target source f)
      (hammingAdjacentChannel n k L target other g) = 0 := by
  classical
  have hvalne : source.val ≠ other.val := by
    intro h
    exact hne (Fin.ext h)
  have hvalne' : other.val ≠ source.val := Ne.symm hvalne
  by_cases hsourceDelete : target.val + 1 = source.val
  · by_cases hotherDelete : target.val + 1 = other.val
    · exfalso
      apply hne
      apply Fin.ext
      omega
    · by_cases hotherAdd : other.val + 1 = target.val
      · simpa [hammingAdjacentChannel, hsourceDelete,
          hotherDelete, hotherAdd, hvalne, hvalne'] using
          (deleteChannel_orthogonal_addChannel
            (k + source.val) (k + other.val) f g)
      · simp [hammingAdjacentChannel, hsourceDelete,
          hotherAdd, hvalne,           coordinateDot, dot]
  · by_cases hsourceAdd : source.val + 1 = target.val
    · by_cases hotherDelete : target.val + 1 = other.val
      · calc
          coordinateDot
              (hammingAdjacentChannel n k L target source f)
              (hammingAdjacentChannel n k L target other g) =
            coordinateDot
              (hammingAdjacentChannel n k L target other g)
              (hammingAdjacentChannel n k L target source f) :=
                coordinateDot_comm _ _
          _ = 0 := by
            simpa [hammingAdjacentChannel, hsourceDelete,
              hsourceAdd, hotherDelete, hvalne, hvalne'] using
              (deleteChannel_orthogonal_addChannel
                (k + other.val) (k + source.val) g f)
      · by_cases hotherAdd : other.val + 1 = target.val
        · exfalso
          apply hne
          apply Fin.ext
          omega
        · simp [hammingAdjacentChannel, hsourceDelete,
            hsourceAdd, hotherDelete, hotherAdd,
            coordinateDot, dot]
    · simp [hammingAdjacentChannel, hsourceDelete,
        hsourceAdd, coordinateDot, dot]

theorem hammingAdjacentChannel_isLevel
    (n k L : ℕ)
    (target source : Fin (L - k + 1))
    (f : Function n)
    (hf : IsLevel (k + source.val) f)
    (a : Fin n) :
    IsLevel (k + target.val)
      (hammingAdjacentChannel n k L target source f a) := by
  classical
  by_cases hdelete : target.val + 1 = source.val
  · have hsource :
        IsLevel ((k + target.val) + 1) f := by
      convert hf using 1 ; omega
    simpa [hammingAdjacentChannel, hdelete, deleteChannel] using
      (hsource.lowerAt a).smul
        (Real.sqrt (k + source.val : ℝ))⁻¹
  · by_cases hadd : source.val + 1 = target.val
    · have hsource := (hf.raiseAt a).smul
        (Real.sqrt ((n : ℝ) - (k + source.val : ℝ)))⁻¹
      have htarget : k + source.val + 1 = k + target.val := by
        omega
      simpa [hammingAdjacentChannel, hdelete, hadd,
        addChannel, htarget] using hsource
    · intro S hS
      simp [hammingAdjacentChannel, hdelete, hadd]

theorem hammingAdjacentChannel_restricted_coordinateDot
    (n k L : ℕ)
    (target source other : Fin (L - k + 1))
    (f g : Function n)
    (hf : IsLevel (k + source.val) f)
    (hg : IsLevel (k + other.val) g) :
    (∑ a : Fin n,
      ∑ S : Level n (k + target.val),
        hammingAdjacentChannel n k L target source f a S.val *
          hammingAdjacentChannel n k L target other g a S.val) =
      coordinateDot
        (hammingAdjacentChannel n k L target source f)
        (hammingAdjacentChannel n k L target other g) := by
  classical
  unfold coordinateDot
  apply Finset.sum_congr rfl
  intro a _
  simpa [layerDot, layerRestrict] using
    (dot_eq_layerDot_of_level
      (hammingAdjacentChannel n k L target source f a)
      (hammingAdjacentChannel n k L target other g a)
      (hammingAdjacentChannel_isLevel n k L target source f hf a)
      (hammingAdjacentChannel_isLevel n k L target other g hg a)).symm

theorem hammingSourceChannelCoefficient_eq_zero_of_not_adjacent
    (n k L : ℕ)
    (source target : Fin (L - k + 1))
    (hnot : ¬ (target.val + 1 = source.val ∨
      source.val + 1 = target.val)) :
    hammingSourceChannelCoefficient n k L source target = 0 := by
  have hforward : source.val + 1 ≠ target.val := by
    intro h
    exact hnot (Or.inr h)
  have hbackward : target.val + 1 ≠ source.val := by
    intro h
    exact hnot (Or.inl h)
  simp [hammingSourceChannelCoefficient,
    MetricCodes.hammingJacobiMatrix, hforward, hbackward]

def hammingWindowChannelMatrix
    (n k L : ℕ)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (lam : ℝ) :
    Matrix (Fin n × HammingWindowIndex n k L)
      (HammingWindowIndex n k L) ℝ :=
  fun p Q =>
    hammingAdjacentBlockCoefficient n k L v lam p.2.1 Q.1 *
      hammingAdjacentChannel n k L p.2.1 Q.1
        (hammingWindowBasis n k L Q) p.1 p.2.2.val

theorem hammingWindowChannelMatrix_pairing
    (n k L : ℕ)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (lam : ℝ)
    (Q R : HammingWindowIndex n k L) :
    (∑ p : Fin n × HammingWindowIndex n k L,
      hammingWindowChannelMatrix n k L v lam p Q *
        hammingWindowChannelMatrix n k L v lam p R) =
      ∑ target : Fin (L - k + 1),
        (hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
          hammingAdjacentBlockCoefficient n k L v lam target R.1) *
        coordinateDot
          (hammingAdjacentChannel n k L target Q.1
            (hammingWindowBasis n k L Q))
          (hammingAdjacentChannel n k L target R.1
            (hammingWindowBasis n k L R)) := by
  classical
  unfold hammingWindowChannelMatrix
  rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro target _
  calc
    (∑ S : Level n (k + target.val),
      ∑ a : Fin n,
        (hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
          hammingAdjacentChannel n k L target Q.1
            (hammingWindowBasis n k L Q) a S.val) *
        (hammingAdjacentBlockCoefficient n k L v lam target R.1 *
          hammingAdjacentChannel n k L target R.1
            (hammingWindowBasis n k L R) a S.val)) =
      (hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
        hammingAdjacentBlockCoefficient n k L v lam target R.1) *
        (∑ a : Fin n,
          ∑ S : Level n (k + target.val),
            hammingAdjacentChannel n k L target Q.1
                (hammingWindowBasis n k L Q) a S.val *
              hammingAdjacentChannel n k L target R.1
                (hammingWindowBasis n k L R) a S.val) := by
          rw [Finset.sum_comm, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S _
          ring
    _ = (hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
        hammingAdjacentBlockCoefficient n k L v lam target R.1) *
        coordinateDot
          (hammingAdjacentChannel n k L target Q.1
            (hammingWindowBasis n k L Q))
          (hammingAdjacentChannel n k L target R.1
            (hammingWindowBasis n k L R)) := by
          rw [hammingAdjacentChannel_restricted_coordinateDot
            n k L target Q.1 R.1
            (hammingWindowBasis n k L Q)
            (hammingWindowBasis n k L R)
            (isLevel_hammingWindowBasis n k L Q)
            (isLevel_hammingWindowBasis n k L R)]

theorem hammingWindowChannelMatrix_transpose_mul
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v) :
    (hammingWindowChannelMatrix n k L v lam)ᵀ *
      hammingWindowChannelMatrix n k L v lam = 1 := by
  classical
  ext Q R
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  rw [hammingWindowChannelMatrix_pairing]
  rcases Q with ⟨source, S⟩
  rcases R with ⟨other, T⟩
  by_cases heq : source = other
  · subst other
    calc
      (∑ target : Fin (L - k + 1),
        (hammingAdjacentBlockCoefficient n k L v lam target source *
          hammingAdjacentBlockCoefficient n k L v lam target source) *
        coordinateDot
          (hammingAdjacentChannel n k L target source
            (hammingWindowBasis n k L ⟨source, S⟩))
          (hammingAdjacentChannel n k L target source
            (hammingWindowBasis n k L ⟨source, T⟩))) =
        ∑ target : Fin (L - k + 1),
          hammingAdjacentBlockCoefficient n k L v lam target source ^ 2 *
            dot (hammingWindowBasis n k L ⟨source, S⟩)
              (hammingWindowBasis n k L ⟨source, T⟩) := by
          apply Finset.sum_congr rfl
          intro target _
          by_cases hadjacent : target.val + 1 = source.val ∨
              source.val + 1 = target.val
          · rw [hammingAdjacentChannel_isometry
              hkL hLn target source hadjacent
              (hammingWindowBasis n k L ⟨source, S⟩)
              (hammingWindowBasis n k L ⟨source, T⟩)
              (isLevel_hammingWindowBasis n k L ⟨source, S⟩)]
            ring
          · have hzero :=
              hammingSourceChannelCoefficient_eq_zero_of_not_adjacent
                n k L source target hadjacent
            have hblock :
                hammingAdjacentBlockCoefficient
                  n k L v lam target source = 0 := by
              simp [hammingAdjacentBlockCoefficient, hzero]
            simp [hblock]
      _ = (∑ target : Fin (L - k + 1),
            hammingAdjacentBlockCoefficient n k L v lam target source ^ 2) *
          dot (hammingWindowBasis n k L ⟨source, S⟩)
            (hammingWindowBasis n k L ⟨source, T⟩) := by
          rw [Finset.sum_mul]
      _ = if (⟨source, S⟩ : HammingWindowIndex n k L) =
            (⟨source, T⟩ : HammingWindowIndex n k L)
          then 1 else 0 := by
          rw [hammingAdjacentBlockCoefficient_sq_sum
            hn hkL hLn v hv lam hlam heigen source, one_mul,
            dot_hammingWindowBasis]
          by_cases hST : S = T
          · subst T
            simp
          · have hval : S.val ≠ T.val := by
              intro h
              exact hST (Subtype.ext h)
            have hsigma :
                (⟨source, S⟩ : HammingWindowIndex n k L) ≠
                  (⟨source, T⟩ : HammingWindowIndex n k L) := by
              intro h
              have hsecond : S.val = T.val :=
                congrArg (fun Z : HammingWindowIndex n k L => Z.2.val) h
              exact hval hsecond
            simp [hval, hsigma]
  · have hsigma :
        (⟨source, S⟩ : HammingWindowIndex n k L) ≠
          (⟨other, T⟩ : HammingWindowIndex n k L) := by
      intro h
      exact heq
        (congrArg (fun Z : HammingWindowIndex n k L => Z.1) h)
    rw [if_neg hsigma]
    apply Finset.sum_eq_zero
    intro target _
    rw [hammingAdjacentChannel_orthogonal
      n k L target source other heq
      (hammingWindowBasis n k L ⟨source, S⟩)
      (hammingWindowBasis n k L ⟨other, T⟩)]
    ring

def hammingChannelMatrix
    (n k L : ℕ)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (lam : ℝ) :
    Matrix (Fin n × Fin (hammingWindowDimension n k L))
      (Fin (hammingWindowDimension n k L)) ℝ :=
  fun p q =>
    hammingWindowChannelMatrix n k L v lam
      (p.1, (hammingWindowIndexEquiv n k L).symm p.2)
      ((hammingWindowIndexEquiv n k L).symm q)

theorem hammingChannelMatrix_transpose_mul
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v) :
    (hammingChannelMatrix n k L v lam)ᵀ *
      hammingChannelMatrix n k L v lam = 1 := by
  classical
  let e := hammingWindowIndexEquiv n k L
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  change
    (∑ p : Fin n × Fin (hammingWindowDimension n k L),
      hammingWindowChannelMatrix n k L v lam
          (p.1, e.symm p.2) (e.symm i) *
        hammingWindowChannelMatrix n k L v lam
          (p.1, e.symm p.2) (e.symm j)) =
      if i = j then 1 else 0
  have hwindow := congrArg
    (fun M : Matrix (HammingWindowIndex n k L)
        (HammingWindowIndex n k L) ℝ =>
      M (e.symm i) (e.symm j))
    (hammingWindowChannelMatrix_transpose_mul
      hn hkL hLn v hv lam hlam heigen)
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.one_apply] at hwindow
  rw [Fintype.sum_prod_type] at hwindow ⊢
  calc
    (∑ a : Fin n,
      ∑ t : Fin (hammingWindowDimension n k L),
        hammingWindowChannelMatrix n k L v lam
            (a, e.symm t) (e.symm i) *
          hammingWindowChannelMatrix n k L v lam
            (a, e.symm t) (e.symm j)) =
      ∑ a : Fin n,
        ∑ T : HammingWindowIndex n k L,
          hammingWindowChannelMatrix n k L v lam
              (a, T) (e.symm i) *
            hammingWindowChannelMatrix n k L v lam
              (a, T) (e.symm j) := by
          apply Finset.sum_congr rfl
          intro a _
          exact e.symm.sum_comp
            (fun T : HammingWindowIndex n k L =>
              hammingWindowChannelMatrix n k L v lam
                  (a, T) (e.symm i) *
                hammingWindowChannelMatrix n k L v lam
                  (a, T) (e.symm j))
    _ = (if e.symm i = e.symm j then 1 else 0) := hwindow
    _ = (if i = j then 1 else 0) := by
      simp

theorem hammingPositiveRadicalSymmetrization
    {d e a b N r : ℝ}
    (hd : 0 < d) (he : 0 < e)
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hcross : d * b = e * a) :
    (r / (N * a)) * Real.sqrt d =
      (r / (N * Real.sqrt (a * b))) * Real.sqrt e := by
  have hradical :
      Real.sqrt d * Real.sqrt b =
        Real.sqrt e * Real.sqrt a := by
    calc
      Real.sqrt d * Real.sqrt b = Real.sqrt (d * b) :=
        (Real.sqrt_mul hd.le b).symm
      _ = Real.sqrt (e * a) := by rw [hcross]
      _ = Real.sqrt e * Real.sqrt a :=
        Real.sqrt_mul he.le a
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hsb : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  calc
    (r / (N * a)) * Real.sqrt d =
        (r * Real.sqrt d) / (N * a) := by ring
    _ = (r * Real.sqrt e) /
          (N * (Real.sqrt a * Real.sqrt b)) := by
      apply (div_eq_div_iff
        (mul_ne_zero hN.ne' ha.ne')
        (mul_ne_zero hN.ne' (mul_ne_zero hsa hsb))).mpr
      calc
        (r * Real.sqrt d) *
            (N * (Real.sqrt a * Real.sqrt b)) =
          r * N * Real.sqrt a *
            (Real.sqrt d * Real.sqrt b) := by ring
        _ = r * N * Real.sqrt a *
            (Real.sqrt e * Real.sqrt a) := by rw [hradical]
        _ = (r * Real.sqrt e) *
            (N * (Real.sqrt a * Real.sqrt a)) := by ring
        _ = (r * Real.sqrt e) * (N * a) := by
          rw [Real.mul_self_sqrt ha.le]
    _ = (r / (N * Real.sqrt (a * b))) * Real.sqrt e := by
      rw [Real.sqrt_mul ha.le]
      ring

def hammingDeletionChannelSquare (n k i : ℕ) : ℝ :=
  (((i : ℝ) - (k : ℝ) + 1) *
    ((n : ℝ) - (i : ℝ) - (k : ℝ))) /
      ((n : ℝ) * ((i : ℝ) + 1))

def hammingInsertionChannelSquare (n k i : ℕ) : ℝ :=
  (((i : ℝ) - (k : ℝ) + 1) *
    ((n : ℝ) - (i : ℝ) - (k : ℝ))) /
      ((n : ℝ) * ((n : ℝ) - (i : ℝ)))

theorem hammingDeletionChannelSquare_mul_sqrt_choose
    {n k i : ℕ} (hn : 0 < n)
    (_ : k ≤ i) (hboundary : i + k < n) :
    hammingDeletionChannelSquare n k i *
        Real.sqrt (n.choose i : ℝ) =
      MetricCodes.hammingJacobiEntry n k i *
        Real.sqrt (n.choose (i + 1) : ℝ) := by
  have hi : i < n := by omega
  have hd : 0 < (n.choose i : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt hi)
  have he : 0 < (n.choose (i + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show i + 1 ≤ n by omega)
  have ha : 0 < (i : ℝ) + 1 := by positivity
  have hb : 0 < (n : ℝ) - (i : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hi)
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcross :
      (n.choose i : ℝ) * ((n : ℝ) - (i : ℝ)) =
        (n.choose (i + 1) : ℝ) * ((i : ℝ) + 1) := by
    have h := congrArg (fun z : ℕ => (z : ℝ))
      (Nat.choose_succ_right_eq n i)
    simpa [Nat.cast_sub (Nat.le_of_lt hi)] using h.symm
  unfold hammingDeletionChannelSquare MetricCodes.hammingJacobiEntry
  exact hammingPositiveRadicalSymmetrization
    (r := (((i : ℝ) - (k : ℝ) + 1) *
      ((n : ℝ) - (i : ℝ) - (k : ℝ))))
    hd he ha hb hN hcross

theorem hammingInsertionChannelSquare_mul_sqrt_choose
    {n k i : ℕ} (hn : 0 < n)
    (_ : k ≤ i) (hboundary : i + k < n) :
    hammingInsertionChannelSquare n k i *
        Real.sqrt (n.choose (i + 1) : ℝ) =
      MetricCodes.hammingJacobiEntry n k i *
        Real.sqrt (n.choose i : ℝ) := by
  have hi : i < n := by omega
  have hd : 0 < (n.choose i : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt hi)
  have he : 0 < (n.choose (i + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show i + 1 ≤ n by omega)
  have ha : 0 < (i : ℝ) + 1 := by positivity
  have hb : 0 < (n : ℝ) - (i : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hi)
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcross :
      (n.choose i : ℝ) * ((n : ℝ) - (i : ℝ)) =
        (n.choose (i + 1) : ℝ) * ((i : ℝ) + 1) := by
    have h := congrArg (fun z : ℕ => (z : ℝ))
      (Nat.choose_succ_right_eq n i)
    simpa [Nat.cast_sub (Nat.le_of_lt hi)] using h.symm
  have hradical := hammingPositiveRadicalSymmetrization
    (r := (((i : ℝ) - (k : ℝ) + 1) *
      ((n : ℝ) - (i : ℝ) - (k : ℝ))))
    he hd hb ha hN hcross.symm
  unfold hammingInsertionChannelSquare MetricCodes.hammingJacobiEntry
  convert hradical using 1 ; ring_nf

theorem hammingSourceChannelCoefficient_eq_deletion
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (source target : Fin (L - k + 1))
    (hadjacent : target.val + 1 = source.val) :
    hammingSourceChannelCoefficient n k L source target =
      hammingDeletionChannelSquare n k (k + target.val) := by
  have hs := source.isLt
  have ht := target.isLt
  have hboundary : k + target.val + k < n := by omega
  have hdimension : 0 < (n.choose (k + target.val) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show k + target.val ≤ n by omega)
  have hroot : Real.sqrt (n.choose (k + target.val) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr hdimension).ne'
  apply mul_right_cancel₀ hroot
  rw [hammingSourceChannelCoefficient_mul_sqrt_choose
    hkL hLn source target]
  have hnot : source.val + 1 ≠ target.val := by omega
  have hdegree : k + source.val = (k + target.val) + 1 := by omega
  simpa [MetricCodes.hammingJacobiMatrix, hnot, hadjacent, hdegree] using
    (hammingDeletionChannelSquare_mul_sqrt_choose
      hn (show k ≤ k + target.val by omega) hboundary).symm

theorem hammingSourceChannelCoefficient_eq_insertion
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (source target : Fin (L - k + 1))
    (hadjacent : source.val + 1 = target.val) :
    hammingSourceChannelCoefficient n k L source target =
      hammingInsertionChannelSquare n k (k + source.val) := by
  have hs := source.isLt
  have ht := target.isLt
  have hboundary : k + source.val + k < n := by omega
  have hdimension : 0 < (n.choose (k + target.val) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show k + target.val ≤ n by omega)
  have hroot : Real.sqrt (n.choose (k + target.val) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr hdimension).ne'
  apply mul_right_cancel₀ hroot
  rw [hammingSourceChannelCoefficient_mul_sqrt_choose
    hkL hLn source target]
  have hdegree : k + target.val = (k + source.val) + 1 := by omega
  simpa [MetricCodes.hammingJacobiMatrix, hadjacent, hdegree] using
    (hammingInsertionChannelSquare_mul_sqrt_choose
      hn (show k ≤ k + source.val by omega) hboundary).symm

theorem dot_lowerAt_eq_raiseAt (a : Fin n) (f g : Function n) :
    dot (lowerAt a f) g = dot f (raiseAt a g) := by
  calc
    dot (lowerAt a f) g = dot g (lowerAt a f) :=
      dot_comm _ _
    _ = dot (raiseAt a g) f :=
      (dot_raiseAt_eq_lowerAt a g f).symm
    _ = dot f (raiseAt a g) := dot_comm _ _

theorem sum_dot_twist_raiseAt
    (x : BinaryWord n) (f g : Function n) :
    (∑ a : Fin n, dot f (twist x (raiseAt a g))) =
      dot f (twist x (raise g)) := by
  classical
  unfold dot twist raise
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem sum_dot_twist_lowerAt
    (x : BinaryWord n) (f g : Function n) :
    (∑ a : Fin n, dot f (twist x (lowerAt a g))) =
      dot f (twist x (lower g)) := by
  classical
  unfold dot twist lower
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

def hammingAxisTensor (x : BinaryWord n) (f : Function n) :
    CoordinateFunction n :=
  fun a => hammingAxis x a • f

theorem coordinateDot_deleteChannel_hammingAxisTensor
    (i : ℕ) (x : BinaryWord n) (f g : Function n) :
    coordinateDot (deleteChannel i f)
      (hammingAxisTensor x (twist x g)) =
      ((Real.sqrt (i : ℝ))⁻¹ *
        (Real.sqrt (n : ℝ))⁻¹) *
        dot f (twist x (raise g)) := by
  classical
  unfold coordinateDot deleteChannel hammingAxisTensor
  simp only [dot_smul_left, dot_smul_right,
    hammingAxis, PiLp.toLp_apply]
  change
    (∑ a : Fin n,
      ((Real.sqrt (n : ℝ))⁻¹ * sign (x a)) *
        ((Real.sqrt (i : ℝ))⁻¹ *
          dot (lowerAt a f) (twist x g))) = _
  simp_rw [dot_lowerAt_eq_raiseAt,
    raiseAt_twist, dot_smul_right]
  calc
    (∑ a : Fin n,
      ((Real.sqrt (n : ℝ))⁻¹ * sign (x a)) *
        ((Real.sqrt (i : ℝ))⁻¹ *
          (sign (x a) * dot f (twist x (raiseAt a g))))) =
      ((Real.sqrt (i : ℝ))⁻¹ *
        (Real.sqrt (n : ℝ))⁻¹) *
        (∑ a : Fin n, dot f (twist x (raiseAt a g))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          calc
            ((Real.sqrt (n : ℝ))⁻¹ * sign (x a)) *
                ((Real.sqrt (i : ℝ))⁻¹ *
                  (sign (x a) * dot f (twist x (raiseAt a g)))) =
              ((Real.sqrt (i : ℝ))⁻¹ *
                (Real.sqrt (n : ℝ))⁻¹) *
                  ((sign (x a) * sign (x a)) *
                    dot f (twist x (raiseAt a g))) := by
                      ring
            _ = ((Real.sqrt (i : ℝ))⁻¹ *
                (Real.sqrt (n : ℝ))⁻¹) *
                  dot f (twist x (raiseAt a g)) := by
                    rw [sign_mul_self, one_mul]
    _ = ((Real.sqrt (i : ℝ))⁻¹ *
        (Real.sqrt (n : ℝ))⁻¹) *
        dot f (twist x (raise g)) := by
          rw [sum_dot_twist_raiseAt]

theorem coordinateDot_addChannel_hammingAxisTensor
    (i : ℕ) (x : BinaryWord n) (f g : Function n) :
    coordinateDot (addChannel i f)
      (hammingAxisTensor x (twist x g)) =
      ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
        (Real.sqrt (n : ℝ))⁻¹) *
        dot f (twist x (lower g)) := by
  classical
  unfold coordinateDot addChannel hammingAxisTensor
  simp only [dot_smul_left, dot_smul_right,
    hammingAxis, PiLp.toLp_apply]
  change
    (∑ a : Fin n,
      ((Real.sqrt (n : ℝ))⁻¹ * sign (x a)) *
        ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          dot (raiseAt a f) (twist x g))) = _
  simp_rw [dot_raiseAt_eq_lowerAt,
    lowerAt_twist, dot_smul_right]
  calc
    (∑ a : Fin n,
      ((Real.sqrt (n : ℝ))⁻¹ * sign (x a)) *
        ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (sign (x a) * dot f (twist x (lowerAt a g))))) =
      ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
        (Real.sqrt (n : ℝ))⁻¹) *
        (∑ a : Fin n, dot f (twist x (lowerAt a g))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          calc
            ((Real.sqrt (n : ℝ))⁻¹ * sign (x a)) *
                ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
                  (sign (x a) * dot f (twist x (lowerAt a g)))) =
              ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
                (Real.sqrt (n : ℝ))⁻¹) *
                  ((sign (x a) * sign (x a)) *
                    dot f (twist x (lowerAt a g))) := by
                      ring
            _ = ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
                (Real.sqrt (n : ℝ))⁻¹) *
                  dot f (twist x (lowerAt a g)) := by
                    rw [sign_mul_self, one_mul]
    _ = ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
        (Real.sqrt (n : ℝ))⁻¹) *
        dot f (twist x (lower g)) := by
          rw [sum_dot_twist_lowerAt]

theorem hammingSqrtDivProduct
    {r a b : ℝ} (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (r / (a * b)) =
      (Real.sqrt a)⁻¹ * (Real.sqrt b)⁻¹ * Real.sqrt r := by
  rw [Real.sqrt_div hr, Real.sqrt_mul ha.le]
  field_simp [(Real.sqrt_pos.mpr ha).ne',
    (Real.sqrt_pos.mpr hb).ne']

theorem hammingSourceChannelCoefficient_sqrt_deletion
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (source target : Fin (L - k + 1))
    (hadjacent : target.val + 1 = source.val) :
    Real.sqrt (hammingSourceChannelCoefficient n k L source target) =
      (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt (k + source.val : ℝ))⁻¹ *
          Real.sqrt (harmonicCoefficient n k source.val) := by
  have hs := source.isLt
  have hcoefficient : 0 < harmonicCoefficient n k source.val :=
    harmonicCoefficient_pos (by omega) (by omega)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsreal : 0 < (k + source.val : ℝ) := by
    exact_mod_cast (show 0 < k + source.val by omega)
  have hnum :
      (((k + target.val : ℕ) : ℝ) - (k : ℝ) + 1) *
          ((n : ℝ) - ((k + target.val : ℕ) : ℝ) - (k : ℝ)) =
        harmonicCoefficient n k source.val := by
    have hval : source.val = target.val + 1 := by omega
    rw [hval]
    simp only [harmonicCoefficient, Nat.cast_add, Nat.cast_one]
    ring
  have hden :
      ((k + target.val : ℕ) : ℝ) + 1 =
        ((k + source.val : ℕ) : ℝ) := by
    exact_mod_cast (show k + target.val + 1 = k + source.val by omega)
  rw [hammingSourceChannelCoefficient_eq_deletion
    hn hkL hLn source target hadjacent]
  unfold hammingDeletionChannelSquare
  rw [hnum, hden]
  simpa only [Nat.cast_add] using
    hammingSqrtDivProduct hcoefficient.le hnreal hsreal

theorem hammingSourceChannelCoefficient_sqrt_insertion
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (source target : Fin (L - k + 1))
    (hadjacent : source.val + 1 = target.val) :
    Real.sqrt (hammingSourceChannelCoefficient n k L source target) =
      (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt ((n : ℝ) - (k + source.val : ℝ)))⁻¹ *
          Real.sqrt (harmonicCoefficient n k target.val) := by
  have hs := source.isLt
  have ht := target.isLt
  have hcoefficient : 0 < harmonicCoefficient n k target.val :=
    harmonicCoefficient_pos (by omega) (by omega)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsreal : 0 < (n : ℝ) - (k + source.val : ℝ) := by
    have hdegree : k + source.val < n := by omega
    exact sub_pos.mpr (by exact_mod_cast hdegree)
  have hnum :
      (((k + source.val : ℕ) : ℝ) - (k : ℝ) + 1) *
          ((n : ℝ) - ((k + source.val : ℕ) : ℝ) - (k : ℝ)) =
        harmonicCoefficient n k target.val := by
    have hval : target.val = source.val + 1 := by omega
    rw [hval]
    simp only [harmonicCoefficient, Nat.cast_add, Nat.cast_one]
    ring
  rw [hammingSourceChannelCoefficient_eq_insertion
    hn hkL hLn source target hadjacent]
  unfold hammingInsertionChannelSquare
  rw [hnum]
  simpa only [Nat.cast_add] using
    hammingSqrtDivProduct hcoefficient.le hnreal hsreal

theorem hammingAdjacentChannel_axis_inner
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (x : BinaryWord n)
    (target source : Fin (L - k + 1))
    (f h : Function n) (hh : IsHarmonic k h) :
    coordinateDot
      (hammingAdjacentChannel n k L target source f)
      (hammingAxisTensor x (wordHarmonicEmbedding x k target.val h)) =
      Real.sqrt (hammingSourceChannelCoefficient n k L source target) *
        dot f (wordHarmonicEmbedding x k source.val h) := by
  classical
  have hs := source.isLt
  have ht := target.isLt
  by_cases hdelete : target.val + 1 = source.val
  · simp only [hammingAdjacentChannel, hdelete, ↓reduceIte]
    unfold wordHarmonicEmbedding
    rw [coordinateDot_deleteChannel_hammingAxisTensor]
    rw [raise_harmonicEmbedding h target.val (by omega),
      twist_smul, dot_smul_right,
      hammingSourceChannelCoefficient_sqrt_deletion
        hn hkL hLn source target hdelete]
    have hval : target.val + 1 = source.val := hdelete
    rw [hval]
    simp only [Nat.cast_add]
    ring
  · by_cases hadd : source.val + 1 = target.val
    · simp only [hammingAdjacentChannel, hdelete,
        hadd, ↓reduceIte]
      unfold wordHarmonicEmbedding
      rw [coordinateDot_addChannel_hammingAxisTensor]
      have hval : target.val = source.val + 1 := by omega
      rw [hval,
        lower_harmonicEmbedding h hh source.val (by omega),
        twist_smul, dot_smul_right,
        hammingSourceChannelCoefficient_sqrt_insertion
          hn hkL hLn source target hadd]
      rw [hval]
      simp only [Nat.cast_add]
      ring
    · have hzero :=
        hammingSourceChannelCoefficient_eq_zero_of_not_adjacent
          n k L source target (by tauto)
      simp [hammingAdjacentChannel, hdelete, hadd,
        hammingAxisTensor, coordinateDot, dot, hzero]

theorem dot_hammingWindowBasis_apply
    (n k L : ℕ) (Q : HammingWindowIndex n k L)
    (f : Function n) :
    dot (hammingWindowBasis n k L Q) f = f Q.2.val := by
  classical
  unfold dot hammingWindowBasis
  rw [Finset.sum_eq_single Q.2.val]
  · rw [if_pos rfl, one_mul]
  · intro S _ hS
    rw [if_neg hS, zero_mul]
  · simp

theorem hammingAdjacentChannel_restricted_axisDot
    (n k L : ℕ) (x : BinaryWord n)
    (target source : Fin (L - k + 1))
    (f g : Function n)
    (hf : IsLevel (k + source.val) f)
    (hg : IsLevel (k + target.val) g) :
    (∑ a : Fin n,
      ∑ S : Level n (k + target.val),
        hammingAdjacentChannel n k L target source f a S.val *
          (hammingAxis x a * g S.val)) =
      coordinateDot
        (hammingAdjacentChannel n k L target source f)
        (hammingAxisTensor x g) := by
  classical
  unfold coordinateDot
  apply Finset.sum_congr rfl
  intro a _
  simpa [layerDot, layerRestrict, hammingAxisTensor,
    Pi.smul_apply, smul_eq_mul] using
    (dot_eq_layerDot_of_level
      (hammingAdjacentChannel n k L target source f a)
      (hammingAxisTensor x g a)
      (hammingAdjacentChannel_isLevel n k L target source f hf a)
      (hg.smul (hammingAxis x a))).symm

theorem hammingWindowChannelMatrix_transpose_axis_fibre
    {n k L : ℕ} (hn : 0 < n) (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (x : BinaryWord n) :
    (hammingWindowChannelMatrix n k L v lam)ᵀ *
      matrixAxisLift (fun a : Fin n => hammingAxis x a)
        (hammingWindowFibreMatrix n k L hk v x) =
      Real.sqrt lam • hammingWindowFibreMatrix n k L hk v x := by
  classical
  ext Q p
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul]
  change
    (∑ z : Fin n × HammingWindowIndex n k L,
      (hammingAdjacentBlockCoefficient n k L v lam z.2.1 Q.1 *
        hammingAdjacentChannel n k L z.2.1 Q.1
          (hammingWindowBasis n k L Q) z.1 z.2.2.val) *
      (hammingAxis x z.1 *
        (hammingFibreAmplitude n k L v z.2.1 *
          wordHarmonicEmbedding x k z.2.1.val
            (harmonicBasisFunction n k hk p) z.2.2.val))) =
      Real.sqrt lam *
        (hammingFibreAmplitude n k L v Q.1 *
          wordHarmonicEmbedding x k Q.1.val
            (harmonicBasisFunction n k hk p) Q.2.val)
  rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_sigma]
  let h : Function n := harmonicBasisFunction n k hk p
  have hh : IsHarmonic k h :=
    harmonicBasisFunction_isHarmonic n k hk p
  calc
    (∑ target : Fin (L - k + 1),
      ∑ S : Level n (k + target.val),
      ∑ a : Fin n,
        (hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
          hammingAdjacentChannel n k L target Q.1
            (hammingWindowBasis n k L Q) a S.val) *
        (hammingAxis x a *
          (hammingFibreAmplitude n k L v target *
            wordHarmonicEmbedding x k target.val h S.val))) =
      ∑ target : Fin (L - k + 1),
        (hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
          hammingFibreAmplitude n k L v target) *
        coordinateDot
          (hammingAdjacentChannel n k L target Q.1
            (hammingWindowBasis n k L Q))
          (hammingAxisTensor x
            (wordHarmonicEmbedding x k target.val h)) := by
          apply Finset.sum_congr rfl
          intro target _
          rw [Finset.sum_comm, ←
            hammingAdjacentChannel_restricted_axisDot
              n k L x target Q.1
              (hammingWindowBasis n k L Q)
              (wordHarmonicEmbedding x k target.val h)
              (isLevel_hammingWindowBasis n k L Q)
              (IsLevel.wordHarmonicEmbedding hh.1 x target.val),
            Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S _
          ring
    _ = (∑ target : Fin (L - k + 1),
          hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
            hammingFibreAmplitude n k L v target *
              Real.sqrt
                (hammingSourceChannelCoefficient n k L Q.1 target)) *
          dot (hammingWindowBasis n k L Q)
            (wordHarmonicEmbedding x k Q.1.val h) := by
          simp_rw [hammingAdjacentChannel_axis_inner
            hn hkL hLn x _ Q.1
            (hammingWindowBasis n k L Q) h hh]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro target _
          ring
    _ = Real.sqrt lam *
          (hammingFibreAmplitude n k L v Q.1 *
            wordHarmonicEmbedding x k Q.1.val h Q.2.val) := by
          rw [hammingAdjacentBlockCoefficient_amplitude_sum
            hn hkL hLn v hunit hv lam hlam heigen Q.1,
            dot_hammingWindowBasis_apply]
          ring

theorem hammingChannelMatrix_transpose_axis_fibre
    {n k L : ℕ} (hn : 0 < n) (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (x : BinaryWord n) :
    (hammingChannelMatrix n k L v lam)ᵀ *
      matrixAxisLift (fun a : Fin n => hammingAxis x a)
        (hammingFibreMatrix n k L hk v x) =
      Real.sqrt lam • hammingFibreMatrix n k L hk v x := by
  classical
  let e := hammingWindowIndexEquiv n k L
  ext i p
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul]
  change
    (∑ z : Fin n × Fin (hammingWindowDimension n k L),
      hammingWindowChannelMatrix n k L v lam
          (z.1, e.symm z.2) (e.symm i) *
        (hammingAxis x z.1 *
          hammingWindowFibreMatrix n k L hk v x
            (e.symm z.2) p)) =
      Real.sqrt lam *
        hammingWindowFibreMatrix n k L hk v x (e.symm i) p
  have hwindow := congrArg
    (fun M : Matrix (HammingWindowIndex n k L)
        (Fin (MetricCodes.hammingFibreDimension n k)) ℝ =>
      M (e.symm i) p)
    (hammingWindowChannelMatrix_transpose_axis_fibre
      hn hk hkL hLn v hunit hv lam hlam heigen x)
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul] at hwindow
  rw [Fintype.sum_prod_type] at hwindow ⊢
  calc
    (∑ a : Fin n,
      ∑ t : Fin (hammingWindowDimension n k L),
        hammingWindowChannelMatrix n k L v lam
            (a, e.symm t) (e.symm i) *
          (hammingAxis x a *
            hammingWindowFibreMatrix n k L hk v x
              (e.symm t) p)) =
      ∑ a : Fin n,
        ∑ T : HammingWindowIndex n k L,
          hammingWindowChannelMatrix n k L v lam
              (a, T) (e.symm i) *
            (hammingAxis x a *
              hammingWindowFibreMatrix n k L hk v x T p) := by
          apply Finset.sum_congr rfl
          intro a _
          exact e.symm.sum_comp
            (fun T : HammingWindowIndex n k L =>
              hammingWindowChannelMatrix n k L v lam
                  (a, T) (e.symm i) *
                (hammingAxis x a *
                  hammingWindowFibreMatrix n k L hk v x T p))
    _ = Real.sqrt lam *
      hammingWindowFibreMatrix n k L hk v x (e.symm i) p :=
        hwindow

theorem matrixAxisLift_mul
    {κ ι ρ σ : Type*} [Fintype ρ]
    (z : κ → ℝ) (A : Matrix ι ρ ℝ) (C : Matrix ρ σ ℝ) :
    matrixAxisLift z (A * C) = matrixAxisLift z A * C := by
  classical
  ext p j
  simp only [matrixAxisLift, Matrix.mul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem hammingChannelMatrix_transpose_axis_projection
    {n k L : ℕ} (hn : 0 < n) (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (x : BinaryWord n) :
    (hammingChannelMatrix n k L v lam)ᵀ *
      matrixAxisLift (fun a : Fin n => hammingAxis x a)
        ((hammingProjectionFamily hk hkL hLn
          v hunit (fun i => (hv i).le)).projection x) =
      Real.sqrt lam •
        ((hammingProjectionFamily hk hkL hLn
          v hunit (fun i => (hv i).le)).projection x) := by
  let A := hammingFibreMatrix n k L hk v x
  change
    (hammingChannelMatrix n k L v lam)ᵀ *
      matrixAxisLift (fun a : Fin n => hammingAxis x a)
        (A * Aᵀ) =
      Real.sqrt lam • (A * Aᵀ)
  rw [matrixAxisLift_mul, ← Matrix.mul_assoc,
    hammingChannelMatrix_transpose_axis_fibre
      hn hk hkL hLn v hunit hv lam hlam heigen x,
    Matrix.smul_mul]

def hammingProjectionGramFeature
    {n k L : ℕ} (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (x : BinaryWord n) :
    EuclideanSpace ℝ
      ((Fin n × Fin (hammingWindowDimension n k L)) ×
        Fin (hammingWindowDimension n k L)) :=
  matrixAxisGramFeature
    (hammingProjectionFamily hk hkL hLn
      v hunit (fun i => (hv i).le))
    (fun (y : BinaryWord n) (a : Fin n) => hammingAxis y a)
    (hammingChannelMatrix n k L v lam)
    (Real.sqrt lam) x

theorem hammingProjectionGramFeature_inner
    {n k L : ℕ} (hn : 0 < n) (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (x y : BinaryWord n) :
    @inner ℝ
      (EuclideanSpace ℝ
        ((Fin n × Fin (hammingWindowDimension n k L)) ×
          Fin (hammingWindowDimension n k L))) _
      (hammingProjectionGramFeature hk hkL hLn
        v hunit hv lam x)
      (hammingProjectionGramFeature hk hkL hLn
        v hunit hv lam y) =
      (MetricCodes.hammingCorrelation x y - lam) *
        (hammingProjectionFamily hk hkL hLn
          v hunit (fun i => (hv i).le)).overlap x y := by
  have hgram := matrixAxisResidual_gram
    (hammingProjectionFamily hk hkL hLn
      v hunit (fun i => (hv i).le))
    (fun (z : BinaryWord n) (a : Fin n) => hammingAxis z a)
    (hammingChannelMatrix n k L v lam)
    (Real.sqrt lam) lam
    (hammingChannelMatrix_transpose_mul
      hn hkL hLn v hv lam hlam heigen)
    (fun z => hammingChannelMatrix_transpose_axis_projection
      hn hk hkL hLn v hunit hv lam hlam heigen z)
    (Real.sq_sqrt hlam.le) x y
  change
    @inner ℝ
      (EuclideanSpace ℝ
        ((Fin n × Fin (hammingWindowDimension n k L)) ×
          Fin (hammingWindowDimension n k L))) _
      (hammingProjectionGramFeature hk hkL hLn
        v hunit hv lam x)
      (hammingProjectionGramFeature hk hkL hLn
        v hunit hv lam y) =
      (MetricCodes.hammingCorrelation x y - lam) *
        (hammingProjectionFamily hk hkL hLn
          v hunit (fun i => (hv i).le)).overlap x y
  have haxis' :
      (∑ a : Fin n, hammingAxis x a * hammingAxis y a) =
        MetricCodes.hammingCorrelation x y := by
    simpa only [PiLp.inner_apply, Real.inner_apply, mul_comm] using
      hammingAxis_inner hn x y
  change
    @inner ℝ
      (EuclideanSpace ℝ
        ((Fin n × Fin (hammingWindowDimension n k L)) ×
          Fin (hammingWindowDimension n k L))) _
      (matrixAxisGramFeature
        (hammingProjectionFamily hk hkL hLn
          v hunit (fun i => (hv i).le))
        (fun (z : BinaryWord n) (a : Fin n) => hammingAxis z a)
        (hammingChannelMatrix n k L v lam)
        (Real.sqrt lam) x)
      (matrixAxisGramFeature
        (hammingProjectionFamily hk hkL hLn
          v hunit (fun i => (hv i).le))
        (fun (z : BinaryWord n) (a : Fin n) => hammingAxis z a)
        (hammingChannelMatrix n k L v lam)
        (Real.sqrt lam) y) = _
  rw [← haxis']
  exact hgram

end MetricCodes.Boolean

end

section

open scoped BigOperators

namespace MetricCodes

open Finset

def wordSupport {n : ℕ} (x : BinaryWord n) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i = true

@[simp] theorem mem_wordSupport {n : ℕ} (x : BinaryWord n) (i : Fin n) :
    i ∈ wordSupport x ↔ x i = true := by
  simp [wordSupport]

def wordOfSupport {n : ℕ} (s : Finset (Fin n)) : BinaryWord n :=
  fun i => decide (i ∈ s)

@[simp] theorem wordOfSupport_apply {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    wordOfSupport s i = true ↔ i ∈ s := by
  simp [wordOfSupport]

@[simp] theorem wordSupport_wordOfSupport {n : ℕ} (s : Finset (Fin n)) :
    wordSupport (wordOfSupport s) = s := by
  ext i
  simp

@[simp] theorem wordOfSupport_wordSupport {n : ℕ} (x : BinaryWord n) :
    wordOfSupport (wordSupport x) = x := by
  funext i
  cases h : x i <;> simp [wordOfSupport, wordSupport, h]

def binaryWordEquivFinset (n : ℕ) : BinaryWord n ≃ Finset (Fin n) where
  toFun := wordSupport
  invFun := wordOfSupport
  left_inv := wordOfSupport_wordSupport
  right_inv := wordSupport_wordOfSupport

theorem wordOfSupport_injective {n : ℕ} :
    Function.Injective (wordOfSupport (n := n)) :=
  (binaryWordEquivFinset n).symm.injective

theorem binaryWeight_eq_card_wordSupport {n : ℕ} (x : BinaryWord n) :
    binaryWeight x = (wordSupport x).card := by
  rfl

theorem hammingDist_comm {n : ℕ} (x y : BinaryWord n) :
    hammingDist x y = hammingDist y x := by
  unfold hammingDist
  congr 1
  ext i
  simp [ne_comm]

theorem hammingDist_eq_card_support_sdiff {n : ℕ}
    (x y : BinaryWord n) :
    hammingDist x y =
      (wordSupport x \ wordSupport y).card +
      (wordSupport y \ wordSupport x).card := by
  have hsets :
      (Finset.univ.filter fun i => x i ≠ y i) =
        (wordSupport x \ wordSupport y) ∪
        (wordSupport y \ wordSupport x) := by
    ext i
    cases hx : x i <;> cases hy : y i <;>
      simp [wordSupport, hx, hy]
  have hdisj :
      Disjoint (wordSupport x \ wordSupport y)
        (wordSupport y \ wordSupport x) := by
    apply Finset.disjoint_left.mpr
    intro i hxy hyx
    exact (Finset.mem_sdiff.mp hxy).2 (Finset.mem_sdiff.mp hyx).1
  unfold hammingDist
  rw [hsets, Finset.card_union_of_disjoint hdisj]

theorem hammingDist_eq_two_mul_of_binaryWeight_eq {n : ℕ}
    (x y : BinaryWord n) (hweight : binaryWeight x = binaryWeight y) :
    hammingDist x y = 2 * (wordSupport x \ wordSupport y).card := by
  have hcard : (wordSupport x).card = (wordSupport y).card := by
    simpa [binaryWeight_eq_card_wordSupport] using hweight
  have hdiff :
      (wordSupport x \ wordSupport y).card =
        (wordSupport y \ wordSupport x).card :=
    Finset.card_sdiff_comm hcard
  rw [hammingDist_eq_card_support_sdiff, ← hdiff, two_mul]

def johnsonDist {n w : ℕ} (x y : JohnsonSphere n w) : ℕ :=
  (wordSupport (x : BinaryWord n) \ wordSupport (y : BinaryWord n)).card

theorem hammingDist_eq_two_mul_johnsonDist {n w : ℕ}
    (x y : JohnsonSphere n w) :
    hammingDist (x : BinaryWord n) (y : BinaryWord n) =
      2 * johnsonDist x y := by
  apply hammingDist_eq_two_mul_of_binaryWeight_eq
  exact x.property.trans y.property.symm

theorem johnsonDist_eq_weight_sub_inter {n w : ℕ}
    (x y : JohnsonSphere n w) :
    johnsonDist x y =
      w - (wordSupport (x : BinaryWord n) ∩
        wordSupport (y : BinaryWord n)).card := by
  unfold johnsonDist
  rw [Finset.card_sdiff, Finset.inter_comm]
  rw [← binaryWeight_eq_card_wordSupport, x.property]

def binaryTranslate {n : ℕ} (x y : BinaryWord n) : BinaryWord n :=
  fun i => Bool.xor (x i) (y i)

@[simp] theorem binaryTranslate_involutive {n : ℕ} (x y : BinaryWord n) :
    binaryTranslate x (binaryTranslate x y) = y := by
  funext i
  change Bool.xor (x i) (Bool.xor (x i) (y i)) = y i
  rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]

theorem binaryTranslate_injective {n : ℕ} (x : BinaryWord n) :
    Function.Injective (binaryTranslate x) := by
  intro y z h
  have := congrArg (binaryTranslate x) h
  simpa using this

theorem hammingDist_binaryTranslate {n : ℕ} (z x y : BinaryWord n) :
    hammingDist (binaryTranslate z x) (binaryTranslate z y) =
      hammingDist x y := by
  unfold hammingDist
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    binaryTranslate, ne_eq]
  exact not_congr Bool.xor_right_inj

theorem binaryWeight_binaryTranslate {n : ℕ} (x y : BinaryWord n) :
    binaryWeight (binaryTranslate x y) = hammingDist x y := by
  unfold binaryWeight hammingDist
  congr 1
  ext i
  simp [binaryTranslate]

def weightShell (n w : ℕ) : Finset (BinaryWord n) :=
  Finset.univ.filter fun x => binaryWeight x = w

@[simp] theorem mem_weightShell {n w : ℕ} (x : BinaryWord n) :
    x ∈ weightShell n w ↔ binaryWeight x = w := by
  simp [weightShell]

theorem weightShell_eq_image (n w : ℕ) :
    weightShell n w =
      ((Finset.univ : Finset (Fin n)).powersetCard w).image wordOfSupport := by
  ext x
  constructor
  · intro hx
    have hw : binaryWeight x = w := (mem_weightShell x).mp hx
    refine Finset.mem_image.mpr
      ⟨wordSupport x, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩,
        wordOfSupport_wordSupport x⟩
    simpa [binaryWeight_eq_card_wordSupport] using hw
  · intro hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    apply (mem_weightShell _).mpr
    rw [binaryWeight_eq_card_wordSupport, wordSupport_wordOfSupport]
    exact (Finset.mem_powersetCard.mp hs).2

theorem card_weightShell (n w : ℕ) :
    (weightShell n w).card = n.choose w := by
  rw [weightShell_eq_image, Finset.card_image_of_injective _ wordOfSupport_injective,
    Finset.card_powersetCard]
  simp

def hammingSphere {n : ℕ} (x : BinaryWord n) (r : ℕ) :
    Finset (BinaryWord n) :=
  Finset.univ.filter fun y => hammingDist x y = r

@[simp] theorem mem_hammingSphere {n r : ℕ} (x y : BinaryWord n) :
    y ∈ hammingSphere x r ↔ hammingDist x y = r := by
  simp [hammingSphere]

theorem hammingSphere_eq_image {n : ℕ} (x : BinaryWord n) (r : ℕ) :
    hammingSphere x r = (weightShell n r).image (binaryTranslate x) := by
  ext y
  constructor
  · intro hy
    have hd : hammingDist x y = r := (mem_hammingSphere x y).mp hy
    refine Finset.mem_image.mpr
      ⟨binaryTranslate x y, (mem_weightShell _).mpr ?_,
        binaryTranslate_involutive x y⟩
    simpa [binaryWeight_binaryTranslate] using hd
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    apply (mem_hammingSphere _ _).mpr
    rw [← binaryWeight_binaryTranslate, binaryTranslate_involutive]
    exact (mem_weightShell _).mp hz

theorem card_hammingSphere {n : ℕ} (x : BinaryWord n) (r : ℕ) :
    (hammingSphere x r).card = n.choose r := by
  rw [hammingSphere_eq_image,
    Finset.card_image_of_injective _ (binaryTranslate_injective x),
    card_weightShell]

def localizedCode {n : ℕ} (C : Finset (BinaryWord n))
    (z : BinaryWord n) (w : ℕ) : Finset (BinaryWord n) :=
  C.filter fun x => binaryWeight (binaryTranslate z x) = w

@[simp] theorem mem_localizedCode {n w : ℕ} (C : Finset (BinaryWord n))
    (z x : BinaryWord n) :
    x ∈ localizedCode C z w ↔
      x ∈ C ∧ binaryWeight (binaryTranslate z x) = w := by
  simp [localizedCode]

def translateLocalizedCode {n : ℕ} (C : Finset (BinaryWord n))
    (z : BinaryWord n) (w : ℕ) : Finset (BinaryWord n) :=
  (localizedCode C z w).image (binaryTranslate z)

theorem translateLocalizedCode_subset_weightShell {n w : ℕ}
    (C : Finset (BinaryWord n)) (z : BinaryWord n) :
    translateLocalizedCode C z w ⊆ weightShell n w := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact (mem_weightShell _).mpr ((mem_localizedCode C z x).mp hx).2

theorem card_translateLocalizedCode {n w : ℕ}
    (C : Finset (BinaryWord n)) (z : BinaryWord n) :
    (translateLocalizedCode C z w).card = (localizedCode C z w).card := by
  exact Finset.card_image_of_injective _ (binaryTranslate_injective z)

theorem translateLocalizedCode_isBinaryCode {n d w : ℕ}
    (C : Finset (BinaryWord n)) (z : BinaryWord n)
    (hC : IsBinaryCode d C) :
    IsBinaryCode d (translateLocalizedCode C z w) := by
  intro x hx y hy hxy
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  rw [hammingDist_binaryTranslate]
  apply hC ((mem_localizedCode C z u).mp hu).1
    ((mem_localizedCode C z v).mp hv).1
  intro huv
  exact hxy (congrArg (binaryTranslate z) huv)

theorem localization_double_count {n : ℕ}
    (C : Finset (BinaryWord n)) (w : ℕ) :
    (∑ z : BinaryWord n, (localizedCode C z w).card) =
      C.card * n.choose w := by
  calc
    (∑ z : BinaryWord n, (localizedCode C z w).card) =
        ∑ z : BinaryWord n, ∑ x ∈ C,
          if binaryWeight (binaryTranslate z x) = w then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      change
        (C.filter fun x => binaryWeight (binaryTranslate z x) = w).card =
          ∑ x ∈ C,
            if binaryWeight (binaryTranslate z x) = w then 1 else 0
      exact Finset.card_filter
        (fun x => binaryWeight (binaryTranslate z x) = w) C
    _ = ∑ x ∈ C, ∑ z : BinaryWord n,
          if binaryWeight (binaryTranslate z x) = w then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x ∈ C, (hammingSphere x w).card := by
      apply Finset.sum_congr rfl
      intro x hx
      calc
        (∑ z : BinaryWord n,
            if binaryWeight (binaryTranslate z x) = w then 1 else 0) =
            (Finset.univ.filter fun z : BinaryWord n =>
              binaryWeight (binaryTranslate z x) = w).card :=
          (Finset.card_filter
            (fun z : BinaryWord n =>
              binaryWeight (binaryTranslate z x) = w)
            Finset.univ).symm
        _ = (hammingSphere x w).card := by
          congr 1
          ext z
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            mem_hammingSphere, binaryWeight_binaryTranslate]
          rw [hammingDist_comm]
    _ = C.card * n.choose w := by
      simp [card_hammingSphere]

theorem bassalygo_elias_bound {n d w B : ℕ}
    (C : Finset (BinaryWord n)) (hC : IsBinaryCode d C)
    (hB : ∀ D : Finset (BinaryWord n),
      D ⊆ weightShell n w → IsBinaryCode d D → D.card ≤ B) :
    C.card * n.choose w ≤ 2 ^ n * B := by
  calc
    C.card * n.choose w =
        ∑ z : BinaryWord n, (localizedCode C z w).card :=
      (localization_double_count C w).symm
    _ ≤ ∑ _z : BinaryWord n, B := by
      apply Finset.sum_le_sum
      intro z hz
      rw [← card_translateLocalizedCode C z]
      exact hB (translateLocalizedCode C z w)
        (translateLocalizedCode_subset_weightShell C z)
        (translateLocalizedCode_isBinaryCode C z hC)
    _ = 2 ^ n * B := by
      simp

def precedingBinomial (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => n.choose k

theorem choose_monotone_to_half (n : ℕ) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ n / 2) :
    n.choose i ≤ n.choose j := by
  have hi : 2 * i ≤ n := by omega
  have hj' : 2 * j ≤ n := by omega
  rw [← sum_booleanHarmonicDimension n i hi,
    ← sum_booleanHarmonicDimension n j hj']
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

def johnsonAmbientDimension (n a L : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc a L, booleanHarmonicDimension n j

theorem johnsonAmbientDimension_eq (n a L : ℕ)
    (haL : a ≤ L) (hL : L ≤ n / 2) :
    johnsonAmbientDimension n a L =
      n.choose L - precedingBinomial n a := by
  unfold johnsonAmbientDimension
  induction L generalizing a with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      simp [booleanHarmonicDimension, precedingBinomial]
  | succ L ih =>
      by_cases htop : a = L + 1
      · subst a
        simp [booleanHarmonicDimension, precedingBinomial]
      · have ha' : a ≤ L := by omega
        have hhalf : L < n / 2 := by omega
        have hchoose : n.choose L ≤ n.choose (L + 1) :=
          Nat.choose_le_succ_of_lt_half_left hhalf
        have hbase : precedingBinomial n a ≤ n.choose L := by
          cases a with
          | zero => simp [precedingBinomial]
          | succ a =>
              apply choose_monotone_to_half n
              · omega
              · exact hhalf.le
        have hinter :
            Finset.Icc a (L + 1) =
              insert (L + 1) (Finset.Icc a L) := by
          ext j
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [hinter, Finset.sum_insert (by simp),
          ih a ha' hhalf.le, booleanHarmonicDimension_succ]
        exact Nat.sub_add_sub_cancel hchoose hbase

theorem johnsonAmbientDimension_eq_of_fibre (n p q L : ℕ)
    (hpq : p + q ≤ L) (hL : L ≤ n / 2) :
    johnsonAmbientDimension n (p + q) L =
      n.choose L - precedingBinomial n (p + q) :=
  johnsonAmbientDimension_eq n (p + q) L hpq hL

end MetricCodes

end

section

set_option autoImplicit false

noncomputable section

section

open Filter MeasureTheory Metric
open scoped ENNReal InnerProductSpace Topology

attribute [-instance]
  CohnElkies.numeralTwoAtLeast
  CohnElkies.euclideanFiniteDimensional
  CohnElkies.euclideanBorelSpace

namespace SpherePacking

abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

attribute [-instance] MetricCodes.numeralTwoAtLeast in

structure UnitPacking (n : ℕ) where

  centers : Set (Euclidean n)

  separation : centers.Pairwise (fun x y => (2 : ℝ) ≤ dist x y)

def covered {n : ℕ} (P : UnitPacking n) : Set (Euclidean n) :=
  ⋃ x ∈ P.centers, ball x (1 : ℝ)

def unitFiniteDensity {n : ℕ} (P : UnitPacking n) (R : ℝ) : ℝ≥0∞ :=
  volume (covered P ∩ ball (0 : Euclidean n) R) /
    volume (ball (0 : Euclidean n) R)

def upperDensity {n : ℕ} (P : UnitPacking n) : ℝ≥0∞ :=
  Filter.limsup (unitFiniteDensity P) Filter.atTop

def packingConstant (n : ℕ) : ℝ≥0∞ :=
  ⨆ P : UnitPacking n, upperDensity P

end SpherePacking

end

end

end

section

set_option autoImplicit false

noncomputable section

section

open Filter Real
open scoped Nat Topology

namespace SpherePacking

def factorialLogError (n : ℕ) : ℝ :=
  Real.log (n.factorial : ℝ) / (n : ℝ) - Real.log (n : ℝ) + 1

theorem tendsto_log_natCast_div_natCast :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have h :=
    (Real.tendsto_pow_log_div_mul_add_atTop
      (1 : ℝ) 0 1 (by norm_num)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  refine h.congr ?_
  intro n
  simp

theorem tendsto_log_two_mul_natCast_div_natCast :
    Tendsto (fun n : ℕ =>
      Real.log (2 * (n : ℝ)) / (n : ℝ)) atTop (nhds 0) := by
  have hc := tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
  have hs := hc.add tendsto_log_natCast_div_natCast
  have heq :
      (fun n : ℕ =>
        Real.log 2 / (n : ℝ) + Real.log (n : ℝ) / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => Real.log (2 * (n : ℝ)) / (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    rw [Real.log_mul (by norm_num) hn', add_div]
  simpa using hs.congr' heq

theorem tendsto_log_stirlingSeq_div_natCast :
    Tendsto
      (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ))
      atTop (nhds 0) := by
  have hlog :
      Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n))
        atTop (nhds (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log (by positivity)).tendsto.comp
      Stirling.tendsto_stirlingSeq_sqrt_pi
  have hinv := tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
  simpa [div_eq_mul_inv] using hlog.mul hinv

theorem factorialLogError_eq (n : ℕ) (hn : n ≠ 0) :
    factorialLogError n =
      Real.log (Stirling.stirlingSeq n) / (n : ℝ) +
        (1 / 2 : ℝ) * Real.log (2 * (n : ℝ)) / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have he : Real.exp (1 : ℝ) ≠ 0 := (Real.exp_pos 1).ne'
  have hst := Stirling.log_stirlingSeq_formula n
  rw [Real.log_div hn' he, Real.log_exp] at hst
  have hlog : Real.log ((n : ℝ) * 2) = Real.log (2 * (n : ℝ)) := by
    rw [mul_comm]
  unfold factorialLogError
  field_simp [hn']
  nlinarith [hst, hlog]

theorem tendsto_factorialLogError :
    Tendsto factorialLogError atTop (nhds 0) := by
  have hhalf :=
    tendsto_log_two_mul_natCast_div_natCast.const_mul (1 / 2 : ℝ)
  have hsum := tendsto_log_stirlingSeq_div_natCast.add hhalf
  have heq :
      (fun n : ℕ =>
        Real.log (Stirling.stirlingSeq n) / (n : ℝ) +
          (1 / 2 : ℝ) * (Real.log (2 * (n : ℝ)) / (n : ℝ))) =ᶠ[atTop]
        factorialLogError := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    rw [factorialLogError_eq n hn]
    ring
  simpa using hsum.congr' heq

theorem scaled_log_factorial_identity (m n : ℕ)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    Real.log (m.factorial : ℝ) / (n : ℝ) -
        ((m : ℝ) / (n : ℝ)) * Real.log (n : ℝ) =
      ((m : ℝ) / (n : ℝ)) *
        (factorialLogError m + Real.log ((m : ℝ) / (n : ℝ)) - 1) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [Real.log_div hm' hn']
  unfold factorialLogError
  field_simp [hm', hn']
  ring_nf

theorem tendsto_scaled_log_factorial_sub
    (k : ℕ → ℕ) (u : ℝ)
    (hk : Tendsto k atTop atTop)
    (hratio : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ))
      atTop (nhds u))
    (hu : u ≠ 0) :
    Tendsto
      (fun n : ℕ =>
        Real.log ((k n).factorial : ℝ) / (n : ℝ) -
          ((k n : ℝ) / (n : ℝ)) * Real.log (n : ℝ))
      atTop (nhds (u * Real.log u - u)) := by
  have herror :
      Tendsto (fun n : ℕ => factorialLogError (k n))
        atTop (nhds 0) :=
    tendsto_factorialLogError.comp hk
  have hlog :
      Tendsto (fun n : ℕ => Real.log ((k n : ℝ) / (n : ℝ)))
        atTop (nhds (Real.log u)) :=
    (Real.continuousAt_log hu).tendsto.comp hratio
  have hproduct :=
    hratio.mul ((herror.add hlog).sub (tendsto_const_nhds (x := (1 : ℝ))))
  have heq :
      (fun n : ℕ =>
        ((k n : ℝ) / (n : ℝ)) *
          (factorialLogError (k n) +
            Real.log ((k n : ℝ) / (n : ℝ)) - 1)) =ᶠ[atTop]
      (fun n : ℕ =>
        Real.log ((k n).factorial : ℝ) / (n : ℝ) -
          ((k n : ℝ) / (n : ℝ)) * Real.log (n : ℝ)) := by
    filter_upwards [hk.eventually (eventually_ne_atTop (0 : ℕ)),
      eventually_ne_atTop (0 : ℕ)] with n hkn hn
    exact (scaled_log_factorial_identity (k n) n hkn hn).symm
  simpa only [zero_add, mul_sub, mul_one] using hproduct.congr' heq

theorem log_add_choose_div_eq (a b n : ℕ) :
    Real.log (((a + b).choose a : ℝ)) / (n : ℝ) =
      Real.log ((a + b).factorial : ℝ) / (n : ℝ) -
        Real.log (a.factorial : ℝ) / (n : ℝ) -
        Real.log (b.factorial : ℝ) / (n : ℝ) := by
  rw [Nat.cast_add_choose ℝ]
  rw [Real.log_div (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  ring

theorem tendsto_log_add_choose_div
    (k l : ℕ → ℕ) (u v : ℝ)
    (hk : Tendsto k atTop atTop)
    (hl : Tendsto l atTop atTop)
    (hku : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ))
      atTop (nhds u))
    (hlv : Tendsto (fun n : ℕ => (l n : ℝ) / (n : ℝ))
      atTop (nhds v))
    (hu : 0 < u) (hv : 0 < v) :
    Tendsto
      (fun n : ℕ =>
        Real.log (((k n + l n).choose (k n) : ℝ)) / (n : ℝ))
      atTop
      (nhds ((u + v) * Real.log (u + v) -
        u * Real.log u - v * Real.log v)) := by
  have hsum : Tendsto (fun n : ℕ => k n + l n) atTop atTop := by
    apply tendsto_atTop_mono (f := k)
    · intro n
      omega
    · exact hk
  have hsumratio :
      Tendsto (fun n : ℕ => ((k n + l n : ℕ) : ℝ) / (n : ℝ))
        atTop (nhds (u + v)) := by
    simpa only [Nat.cast_add, add_div] using hku.add hlv
  have htotal :=
    tendsto_scaled_log_factorial_sub (fun n => k n + l n)
      (u + v) hsum hsumratio (ne_of_gt (add_pos hu hv))
  have hfirst := tendsto_scaled_log_factorial_sub k u hk hku hu.ne'
  have hsecond := tendsto_scaled_log_factorial_sub l v hl hlv hv.ne'
  have hcomb := (htotal.sub hfirst).sub hsecond
  have heq :
      (fun n : ℕ =>
        (Real.log ((k n + l n).factorial : ℝ) / (n : ℝ) -
          (((k n + l n : ℕ) : ℝ) / (n : ℝ)) * Real.log (n : ℝ)) -
          (Real.log ((k n).factorial : ℝ) / (n : ℝ) -
            ((k n : ℝ) / (n : ℝ)) * Real.log (n : ℝ)) -
          (Real.log ((l n).factorial : ℝ) / (n : ℝ) -
            ((l n : ℝ) / (n : ℝ)) * Real.log (n : ℝ))) =ᶠ[atTop]
  (fun n : ℕ =>
        Real.log (((k n + l n).choose (k n) : ℝ)) / (n : ℝ)) := by
    apply Eventually.of_forall
    intro n
    change _ = Real.log (((k n + l n).choose (k n) : ℝ)) / (n : ℝ)
    rw [log_add_choose_div_eq]
    push_cast
    ring
  have hlimit :
      ((u + v) * Real.log (u + v) - (u + v)) -
          (u * Real.log u - u) - (v * Real.log v - v) =
        (u + v) * Real.log (u + v) -
          u * Real.log u - v * Real.log v := by
    ring
  rw [← hlimit]
  exact hcomb.congr' heq

end SpherePacking

end

end

end

section

set_option autoImplicit false

noncomputable section

open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology

namespace MetricCodes.Hamming

noncomputable def validCodes (n d : ℕ) : Finset (Finset (BinaryWord n)) := by
  classical
  exact Finset.univ.filter (MetricCodes.IsBinaryCode d)

theorem mem_validCodes {n d : ℕ} (C : Finset (BinaryWord n)) :
    C ∈ validCodes n d ↔ MetricCodes.IsBinaryCode d C := by
  classical
  simp [validCodes]

theorem validCodes_nonempty (n d : ℕ) : (validCodes n d).Nonempty := by
  refine ⟨∅, (mem_validCodes (n := n) (d := d) ∅).2 ?_⟩
  simp [MetricCodes.IsBinaryCode]

noncomputable def codeNumber (n d : ℕ) : ℕ :=
  (validCodes n d).sup fun C => C.card

theorem card_le_codeNumber {n d : ℕ} (C : Finset (BinaryWord n))
    (hC : MetricCodes.IsBinaryCode d C) :
    C.card ≤ codeNumber n d := by
  unfold codeNumber
  exact Finset.le_sup ((mem_validCodes C).2 hC)

theorem exists_codeNumber (n d : ℕ) :
    ∃ C : Finset (BinaryWord n),
      MetricCodes.IsBinaryCode d C ∧ C.card = codeNumber n d := by
  obtain ⟨C, hC, hmax⟩ :=
    Finset.exists_mem_eq_sup (validCodes n d)
      (validCodes_nonempty n d) (fun C => C.card)
  exact ⟨C, (mem_validCodes C).1 hC, hmax.symm⟩

theorem codeNumber_real_le_of_forall {n d : ℕ} {B : ℝ}
    (h : ∀ C : Finset (BinaryWord n),
      MetricCodes.IsBinaryCode d C → (C.card : ℝ) ≤ B) :
    (codeNumber n d : ℝ) ≤ B := by
  obtain ⟨C, hC, hmax⟩ := exists_codeNumber n d
  simpa [hmax] using h C hC

theorem codeNumber_pos (n d : ℕ) : 0 < codeNumber n d := by
  classical
  let x : BinaryWord n := fun _ => false
  have hcode : MetricCodes.IsBinaryCode d ({x} : Finset (BinaryWord n)) := by
    intro u hu v hv huv
    have hu' : u = x := Finset.mem_singleton.mp hu
    have hv' : v = x := Finset.mem_singleton.mp hv
    exact False.elim (huv (hu'.trans hv'.symm))
  have hcard : 1 ≤ codeNumber n d := by
    simpa using card_le_codeNumber ({x} : Finset (BinaryWord n)) hcode
  omega

def ambientDimension (n k L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (L - k + 1), n.choose (k + j)

theorem hammingFibreDimension_pos {n k : ℕ} (hk : 2 * k ≤ n) :
    0 < MetricCodes.hammingFibreDimension n k := by
  cases k with
  | zero => simp [MetricCodes.hammingFibreDimension, MetricCodes.booleanHarmonicDimension]
  | succ j =>
      change 0 < n.choose (j + 1) - n.choose j
      apply Nat.sub_pos_of_lt
      have hchoose : 0 < n.choose j := Nat.choose_pos (by omega)
      have hfactor : j + 1 < n - j := by omega
      have hmul :
          n.choose j * (j + 1) < n.choose j * (n - j) :=
        Nat.mul_lt_mul_of_pos_left hfactor hchoose
      have hmul' :
          n.choose j * (j + 1) < n.choose (j + 1) * (j + 1) := by
        calc
          n.choose j * (j + 1) < n.choose j * (n - j) := hmul
          _ = n.choose (j + 1) * (j + 1) :=
            (Nat.choose_succ_right_eq n j).symm
      exact (Nat.mul_lt_mul_right (by omega : 0 < j + 1)).mp hmul'

def threshold (n d : ℕ) : ℝ :=
  1 - 2 * (d : ℝ) / (n : ℝ)

theorem threshold_lt_one {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    threshold n d < 1 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  unfold threshold
  have hpos : 0 < 2 * (d : ℝ) / (n : ℝ) := by positivity
  linarith

abbrev Index (k L : ℕ) := Fin (L - k + 1)

abbrev Space (k L : ℕ) := EuclideanSpace ℝ (Index k L)

def matrix (n k L : ℕ) : Matrix (Index k L) (Index k L) ℝ :=
  MetricCodes.hammingJacobiMatrix n k L

theorem matrix_hermitian (n k L : ℕ) : (matrix n k L).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have h := congrArg
    (fun A : Matrix (Index k L) (Index k L) ℝ => A i j)
    (MetricCodes.hammingJacobiMatrix_symmetric n k L)
  simpa [matrix] using h

def operator (n k L : ℕ) : Space k L →ₗ[ℝ] Space k L :=
  Matrix.toEuclideanLin (matrix n k L)

theorem operator_isSymmetric (n k L : ℕ) :
    (operator n k L).IsSymmetric := by
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (matrix_hermitian n k L)

def continuousOperator (n k L : ℕ) : Space k L →L[ℝ] Space k L :=
  LinearMap.toContinuousLinearMap (operator n k L)

def rayleigh (n k L : ℕ) (x : Space k L) : ℝ :=
  (continuousOperator n k L).rayleighQuotient x

theorem rayleigh_bddAbove (n k L : ℕ) :
    BddAbove
      (Set.range
        (fun x : {x : Space k L // x ≠ 0} => rayleigh n k L x)) := by
  refine ⟨‖continuousOperator n k L‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (le_abs_self _).trans
    ((continuousOperator n k L).rayleighQuotient_le_norm x)

def topEigenvalue (n k L : ℕ) : ℝ :=
  ⨆ x : {x : Space k L // x ≠ 0}, rayleigh n k L x

theorem rayleigh_le_top (n k L : ℕ) (x : Space k L) (hx : x ≠ 0) :
    rayleigh n k L x ≤ topEigenvalue n k L := by
  exact le_ciSup (rayleigh_bddAbove n k L) ⟨x, hx⟩

theorem topEigenvalue_hasEigenvalue (n k L : ℕ) :
    Module.End.HasEigenvalue (operator n k L) (topEigenvalue n k L) := by
  have h := (operator_isSymmetric n k L).hasEigenvalue_iSup_of_finiteDimensional
  simpa [topEigenvalue, rayleigh, continuousOperator,
    ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply] using h

theorem exists_topEigenvector (n k L : ℕ) :
    ∃ x : Space k L, x ≠ 0 ∧
      operator n k L x = topEigenvalue n k L • x := by
  obtain ⟨x, hx⟩ :=
    (topEigenvalue_hasEigenvalue n k L).exists_hasEigenvector
  exact ⟨x, hx.2, hx.apply_eq_smul⟩

theorem rayleigh_eq_inner (n k L : ℕ) (x : Space k L) :
    rayleigh n k L x =
      @inner ℝ (Space k L) _ (operator n k L x) x / ‖x‖ ^ 2 := by
  rfl

def coordinateAbs (k L : ℕ) (x : Space k L) : Space k L :=
  WithLp.toLp 2 (fun p : Index k L => |x p|)

theorem coordinateAbs_nonneg (k L : ℕ)
    (x : Space k L) (p : Index k L) :
    0 ≤ coordinateAbs k L x p :=
  abs_nonneg _

theorem coordinateAbs_norm (k L : ℕ) (x : Space k L) :
    ‖coordinateAbs k L x‖ = ‖x‖ := by
  have hsquare : ‖coordinateAbs k L x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro p hp
    simp [coordinateAbs]
  nlinarith [norm_nonneg (coordinateAbs k L x), norm_nonneg x]

theorem coordinateAbs_ne_zero (k L : ℕ)
    {x : Space k L} (hx : x ≠ 0) :
    coordinateAbs k L x ≠ 0 := by
  intro habs
  have hnorm := coordinateAbs_norm k L x
  rw [habs, norm_zero] at hnorm
  exact hx (norm_eq_zero.mp hnorm.symm)

theorem matrix_entry_nonneg {n k L : ℕ}
    (hn : 0 < n) (hkL : k ≤ L) (hLn : L + k ≤ n)
    (p q : Index k L) :
    0 ≤ matrix n k L p q := by
  unfold matrix MetricCodes.hammingJacobiMatrix
  split_ifs with hpq hqp
  · apply (MetricCodes.hammingJacobiEntry_pos hn (by omega) ?_).le
    have hq := q.isLt
    omega
  · apply (MetricCodes.hammingJacobiEntry_pos hn (by omega) ?_).le
    have hp := p.isLt
    omega
  · exact le_rfl

theorem inner_le_inner_coordinateAbs {n k L : ℕ}
    (hn : 0 < n) (hkL : k ≤ L) (hLn : L + k ≤ n)
    (x : Space k L) :
    @inner ℝ (Space k L) _ (operator n k L x) x ≤
      @inner ℝ (Space k L) _
        (operator n k L (coordinateAbs k L x))
        (coordinateAbs k L x) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [Real.inner_apply]
  change
    (∑ p : Index k L,
      (∑ q : Index k L, matrix n k L p q * x q) * x p) ≤
    (∑ p : Index k L,
      (∑ q : Index k L, matrix n k L p q * |x q|) * |x p|)
  simp_rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro q hq
  have hentry := matrix_entry_nonneg hn hkL hLn p q
  have hproduct : x q * x p ≤ |x q| * |x p| := by
    calc
      x q * x p ≤ |x q * x p| := le_abs_self _
      _ = |x q| * |x p| := abs_mul _ _
  calc
    matrix n k L p q * x q * x p =
        matrix n k L p q * (x q * x p) := by ring
    _ ≤ matrix n k L p q * (|x q| * |x p|) :=
      mul_le_mul_of_nonneg_left hproduct hentry
    _ = matrix n k L p q * |x q| * |x p| := by ring

theorem rayleigh_le_coordinateAbs {n k L : ℕ}
    (hn : 0 < n) (hkL : k ≤ L) (hLn : L + k ≤ n)
    (x : Space k L) :
    rayleigh n k L x ≤ rayleigh n k L (coordinateAbs k L x) := by
  rw [rayleigh_eq_inner, rayleigh_eq_inner, coordinateAbs_norm]
  gcongr
  exact inner_le_inner_coordinateAbs hn hkL hLn x

theorem rayleigh_eq_of_eigenvector
    (n k L : ℕ) (x : Space k L) (hx : x ≠ 0)
    (eigenvalue : ℝ)
    (heig : operator n k L x = eigenvalue • x) :
    rayleigh n k L x = eigenvalue := by
  rw [rayleigh_eq_inner, heig,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hnorm : ‖x‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  field_simp [hnorm]

theorem coordinateAbs_top_rayleigh {n k L : ℕ}
    (hn : 0 < n) (hkL : k ≤ L) (hLn : L + k ≤ n)
    (x : Space k L) (hx : x ≠ 0)
    (heig : operator n k L x = topEigenvalue n k L • x) :
    rayleigh n k L (coordinateAbs k L x) = topEigenvalue n k L := by
  have hbelow := rayleigh_le_coordinateAbs hn hkL hLn x
  have habove := rayleigh_le_top n k L
    (coordinateAbs k L x) (coordinateAbs_ne_zero k L hx)
  rw [rayleigh_eq_of_eigenvector n k L x hx
    (topEigenvalue n k L) heig] at hbelow
  exact le_antisymm habove hbelow

theorem exists_nonnegative_topEigenvector {n k L : ℕ}
    (hn : 0 < n) (hkL : k ≤ L) (hLn : L + k ≤ n) :
    ∃ x : Space k L,
      x ≠ 0 ∧ operator n k L x = topEigenvalue n k L • x ∧
      ∀ p : Index k L, 0 ≤ x p := by
  obtain ⟨x, hx, heig⟩ := exists_topEigenvector n k L
  let y : Space k L := coordinateAbs k L x
  have hy : y ≠ 0 := coordinateAbs_ne_zero k L hx
  have hyray : rayleigh n k L y = topEigenvalue n k L :=
    coordinateAbs_top_rayleigh hn hkL hLn x hx heig
  have hself : IsSelfAdjoint (continuousOperator n k L) :=
    (operator_isSymmetric n k L).isSelfAdjoint
  have hmax :
      IsMaxOn (continuousOperator n k L).reApplyInnerSelf
        (sphere (0 : Space k L) ‖y‖) y := by
    intro z hz
    have hnorm : ‖z‖ = ‖y‖ := by simpa using hz
    have hznonzero : z ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hnorm
      exact hy (norm_eq_zero.mp hnorm.symm)
    have hray := rayleigh_le_top n k L z hznonzero
    rw [← hyray] at hray
    change
      (continuousOperator n k L).reApplyInnerSelf z / ‖z‖ ^ 2 ≤
        (continuousOperator n k L).reApplyInnerSelf y / ‖y‖ ^ 2 at hray
    rw [hnorm] at hray
    have hnormpos : 0 < ‖y‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hy)
    exact (div_le_div_iff_of_pos_right hnormpos).mp hray
  have heigy := hself.hasEigenvector_of_isMaxOn hy hmax
  refine ⟨y, hy, ?_, fun p => coordinateAbs_nonneg k L x p⟩
  have happly := heigy.apply_eq_smul
  simpa [topEigenvalue, rayleigh, continuousOperator] using happly

theorem exists_nonnegative_unit_topEigenvector {n k L : ℕ}
    (hn : 0 < n) (hkL : k ≤ L) (hLn : L + k ≤ n) :
    ∃ x : Space k L,
      ‖x‖ = 1 ∧ operator n k L x = topEigenvalue n k L • x ∧
      ∀ p : Index k L, 0 ≤ x p := by
  obtain ⟨x, hx, heig, hnonneg⟩ :=
    exists_nonnegative_topEigenvector hn hkL hLn
  have hnormpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  refine ⟨‖x‖⁻¹ • x, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hnormpos)]
    exact inv_mul_cancel₀ (ne_of_gt hnormpos)
  · rw [map_smul, heig]
    exact smul_comm _ _ _
  · intro p
    change 0 ≤ ‖x‖⁻¹ * x p
    exact mul_nonneg (inv_nonneg.mpr hnormpos.le) (hnonneg p)

theorem matrix_adjacent_pos {n k L : ℕ}
    (hn : 0 < n) (hkL : k ≤ L) (hLn : L + k ≤ n)
    (p q : Index k L)
    (hadjacent : p.val + 1 = q.val ∨ q.val + 1 = p.val) :
    0 < matrix n k L p q := by
  have hp := p.isLt
  have hq := q.isLt
  rcases hadjacent with hforward | hbackward
  · have hnot : q.val + 1 ≠ p.val := by omega
    simpa [matrix, MetricCodes.hammingJacobiMatrix, hforward, hnot] using
      MetricCodes.hammingJacobiEntry_pos hn
        (show k ≤ k + p.val by omega)
        (show k + p.val + k < n by omega)
  · have hnot : p.val + 1 ≠ q.val := by omega
    simpa [matrix, MetricCodes.hammingJacobiMatrix, hnot, hbackward] using
      MetricCodes.hammingJacobiEntry_pos hn
        (show k ≤ k + q.val by omega)
        (show k + q.val + k < n by omega)

theorem nonnegative_eigenvector_zero_propagates {n k L : ℕ}
    (hn : 0 < n) (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : Space k L) (eigenvalue : ℝ)
    (heigen : operator n k L v = eigenvalue • v)
    (hnonnegative : ∀ i : Index k L, 0 ≤ v i)
    (p q : Index k L)
    (hp : v p = 0)
    (hadjacent : p.val + 1 = q.val ∨ q.val + 1 = p.val) :
    v q = 0 := by
  classical
  have hcoordinate := congrArg (fun z : Space k L => z p) heigen
  change
    (∑ i : Index k L, matrix n k L p i * v i) =
      eigenvalue * v p at hcoordinate
  rw [hp, mul_zero] at hcoordinate
  have hterms :
      ∀ i ∈ (Finset.univ : Finset (Index k L)),
        0 ≤ matrix n k L p i * v i := by
    intro i _
    exact mul_nonneg
      (matrix_entry_nonneg hn hkL hLn p i)
      (hnonnegative i)
  have hterm : matrix n k L p q * v q = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hcoordinate
      q (Finset.mem_univ q)
  exact (mul_eq_zero.mp hterm).resolve_left
    (matrix_adjacent_pos hn hkL hLn p q hadjacent).ne'

theorem nonnegative_eigenvector_coordinate_pos {n k L : ℕ}
    (hn : 0 < n) (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : Space k L) (eigenvalue : ℝ)
    (heigen : operator n k L v = eigenvalue • v)
    (hnonnegative : ∀ i : Index k L, 0 ≤ v i)
    (hnonzero : v ≠ 0)
    (i : Index k L) :
    0 < v i := by
  rcases (hnonnegative i).eq_or_lt with hzero | hpositive
  · exfalso
    apply hnonzero
    apply PiLp.ext
    intro q
    change v q = 0
    have hchain :
        ∀ distance : ℕ,
          ∀ q : Index k L,
            Nat.dist i.val q.val = distance → v q = 0 := by
      intro distance
      induction distance using Nat.strong_induction_on with
      | h distance ih =>
          intro q hdistance
          by_cases hequal : i.val = q.val
          · have hiq : i = q := Fin.ext hequal
            simpa [hiq] using hzero.symm
          · by_cases hforward : i.val < q.val
            · let previous : Index k L :=
                ⟨q.val - 1, by have hq := q.isLt; omega⟩
              have hprevious_distance :
                  Nat.dist i.val previous.val < distance := by
                rw [Nat.dist_eq_sub_of_le
                  (show i.val ≤ previous.val by
                    dsimp [previous]
                    omega)]
                rw [Nat.dist_eq_sub_of_le
                  (Nat.le_of_lt hforward)] at hdistance
                dsimp [previous]
                omega
              have hprevious_zero : v previous = 0 :=
                ih (Nat.dist i.val previous.val)
                  hprevious_distance previous rfl
              exact nonnegative_eigenvector_zero_propagates
                hn hkL hLn v eigenvalue heigen hnonnegative previous q
                hprevious_zero (Or.inl (by
                  dsimp [previous]
                  omega))
            · have hbackward : q.val < i.val := by omega
              let next : Index k L :=
                ⟨q.val + 1, by have hi := i.isLt; omega⟩
              have hnext_distance :
                  Nat.dist i.val next.val < distance := by
                rw [Nat.dist_eq_sub_of_le_right
                  (show next.val ≤ i.val by
                    dsimp [next]
                    omega)]
                rw [Nat.dist_eq_sub_of_le_right
                  (Nat.le_of_lt hbackward)] at hdistance
                dsimp [next]
                omega
              have hnext_zero : v next = 0 :=
                ih (Nat.dist i.val next.val)
                  hnext_distance next rfl
              exact nonnegative_eigenvector_zero_propagates
                hn hkL hLn v eigenvalue heigen hnonnegative next q
                hnext_zero (Or.inr (by
                  dsimp [next]))
    exact hchain (Nat.dist i.val q.val) q rfl
  · exact hpositive

theorem nonnegative_eigenvalue_pos_of_lt {n k L : ℕ}
    (hn : 0 < n) (hkL : k < L) (hLn : L + k ≤ n)
    (v : Space k L) (eigenvalue : ℝ)
    (heigen : operator n k L v = eigenvalue • v)
    (hnonnegative : ∀ i : Index k L, 0 ≤ v i)
    (hnonzero : v ≠ 0) :
    0 < eigenvalue := by
  classical
  let p : Index k L := ⟨0, by omega⟩
  let q : Index k L := ⟨1, by omega⟩
  have hp : 0 < v p :=
    nonnegative_eigenvector_coordinate_pos
      hn hkL.le hLn v eigenvalue heigen hnonnegative hnonzero p
  have hq : 0 < v q :=
    nonnegative_eigenvector_coordinate_pos
      hn hkL.le hLn v eigenvalue heigen hnonnegative hnonzero q
  have hentry : 0 < matrix n k L p q := by
    apply matrix_adjacent_pos hn hkL.le hLn p q
    exact Or.inl (by rfl)
  have hterms :
      ∀ i ∈ (Finset.univ : Finset (Index k L)),
        0 ≤ matrix n k L p i * v i := by
    intro i _
    exact mul_nonneg
      (matrix_entry_nonneg hn hkL.le hLn p i)
      (hnonnegative i)
  have hsum :
      0 < ∑ i : Index k L, matrix n k L p i * v i := by
    apply Finset.sum_pos' hterms
    exact ⟨q, Finset.mem_univ q, mul_pos hentry hq⟩
  have hcoordinate := congrArg (fun z : Space k L => z p) heigen
  change
    (∑ i : Index k L, matrix n k L p i * v i) =
      eigenvalue * v p at hcoordinate
  rw [hcoordinate] at hsum
  exact (mul_pos_iff_of_pos_right hp).mp hsum

theorem exists_positive_unit_topEigenvector {n k L : ℕ}
    (hn : 0 < n) (hkL : k ≤ L) (hLn : L + k ≤ n) :
    ∃ v : Space k L,
      ‖v‖ = 1 ∧
        operator n k L v = topEigenvalue n k L • v ∧
        ∀ i : Index k L, 0 < v i := by
  obtain ⟨v, hunit, heigen, hnonnegative⟩ :=
    exists_nonnegative_unit_topEigenvector hn hkL hLn
  have hnonzero : v ≠ 0 := by
    intro hzero
    simp [hzero] at hunit
  refine ⟨v, hunit, heigen, ?_⟩
  exact fun i => nonnegative_eigenvector_coordinate_pos
    hn hkL hLn v (topEigenvalue n k L)
      heigen hnonnegative hnonzero i

theorem topEigenvalue_pos {n k L : ℕ}
    (hn : 0 < n) (hkL : k < L) (hLn : L + k ≤ n) :
    0 < topEigenvalue n k L := by
  obtain ⟨v, hunit, heigen, hnonnegative⟩ :=
    exists_nonnegative_unit_topEigenvector hn hkL.le hLn
  have hnonzero : v ≠ 0 := by
    intro hzero
    simp [hzero] at hunit
  exact nonnegative_eigenvalue_pos_of_lt hn hkL hLn
    v (topEigenvalue n k L) heigen hnonnegative hnonzero

theorem finite_bound_of_projection_gram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n k L d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (C : Finset (BinaryWord n)) (hC : MetricCodes.IsBinaryCode d C)
    (P : MetricCodes.ProjectionFamily (BinaryWord n)
      (ambientDimension n k L) (MetricCodes.hammingFibreDimension n k))
    (q : BinaryWord n → E)
    (hrank : 0 < MetricCodes.hammingFibreDimension n k)
    (hgap : threshold n d < topEigenvalue n k L)
    (hgram : ∀ x ∈ C, ∀ y ∈ C,
      ⟪q x, q y⟫_ℝ =
        (MetricCodes.hammingCorrelation x y - topEigenvalue n k L) *
          P.overlap x y) :
    (C.card : ℝ) ≤
      ((1 - threshold n d) /
        (topEigenvalue n k L - threshold n d)) *
        ((ambientDimension n k L : ℝ) /
          (MetricCodes.hammingFibreDimension n k : ℝ)) := by
  refine MetricCodes.projection_certificate P C MetricCodes.hammingCorrelation q
    hrank (threshold_lt_one hn hd) hgap
    (fun x _ => MetricCodes.hammingCorrelation_self x) ?_ hgram
  intro x hx y hy hxy
  exact MetricCodes.hammingCorrelation_le_of_dist_le hn (hC hx hy hxy)

theorem finite_codeNumber_bound_of_projection_gram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n k L d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (P : MetricCodes.ProjectionFamily (BinaryWord n)
      (ambientDimension n k L) (MetricCodes.hammingFibreDimension n k))
    (q : BinaryWord n → E)
    (hrank : 0 < MetricCodes.hammingFibreDimension n k)
    (hgap : threshold n d < topEigenvalue n k L)
    (hgram : ∀ x y : BinaryWord n,
      ⟪q x, q y⟫_ℝ =
        (MetricCodes.hammingCorrelation x y - topEigenvalue n k L) *
          P.overlap x y) :
    (codeNumber n d : ℝ) ≤
      ((1 - threshold n d) /
        (topEigenvalue n k L - threshold n d)) *
        ((ambientDimension n k L : ℝ) /
          (MetricCodes.hammingFibreDimension n k : ℝ)) := by
  apply codeNumber_real_le_of_forall
  intro C hC
  apply finite_bound_of_projection_gram hn hd C hC P q hrank hgap
  intro x hx y hy
  exact hgram x y

theorem binaryEntropy_eq_binEntropy_div_log (u : ℝ) :
    MetricCodes.binaryEntropy u = Real.binEntropy u / Real.log 2 := by
  simp only [MetricCodes.binaryEntropy, Real.logb, Real.binEntropy, Real.log_inv]
  ring

theorem binaryEntropy_le_one (u : ℝ) :
    MetricCodes.binaryEntropy u ≤ 1 := by
  rw [binaryEntropy_eq_binEntropy_div_log]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ hlog).2
  simpa using (Real.binEntropy_le_log_two (p := u))

theorem binaryEntropy_continuous : Continuous MetricCodes.binaryEntropy := by
  have hfun : MetricCodes.binaryEntropy =
      (fun u : ℝ => Real.binEntropy u / Real.log 2) :=
    funext binaryEntropy_eq_binEntropy_div_log
  rw [hfun]
  exact Real.binEntropy_continuous.div_const (Real.log 2)

def Feasible (δ a b : ℝ) : Prop :=
  0 ≤ b ∧ b < a ∧ a ≤ (1 : ℝ) / 2 ∧
    1 - 2 * δ < MetricCodes.hammingGamma a b

def rateSet (δ : ℝ) : Set ℝ :=
  {r | ∃ a b : ℝ, Feasible δ a b ∧
    r = MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b}

def variationalRate (δ : ℝ) : ℝ := sInf (rateSet δ)

theorem rateSet_bddBelow (δ : ℝ) : BddBelow (rateSet δ) := by
  refine ⟨-1, ?_⟩
  rintro r ⟨a, b, hfeasible, rfl⟩
  obtain ⟨hb, hba, ha, hgamma⟩ := hfeasible
  have ha0 : 0 ≤ a := (lt_of_le_of_lt hb hba).le
  have ha1 : a ≤ 1 := by linarith
  have hapos := MetricCodes.binaryEntropy_nonneg ha0 ha1
  have hble := binaryEntropy_le_one b
  linarith

theorem variationalRate_le_of_feasible {δ a b : ℝ}
    (h : Feasible δ a b) :
    variationalRate δ ≤ MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b := by
  exact csInf_le (rateSet_bddBelow δ) ⟨a, b, h, rfl⟩

def classicalParameter (δ : ℝ) : ℝ :=
  (1 : ℝ) / 2 - Real.sqrt (δ * (1 - δ))

def classicalRate (δ : ℝ) : ℝ :=
  MetricCodes.binaryEntropy (classicalParameter δ)

theorem classicalParameter_lt_half {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    classicalParameter δ < (1 : ℝ) / 2 := by
  have hrad : 0 < δ * (1 - δ) := mul_pos hδ (by linarith)
  unfold classicalParameter
  have hsqrt := Real.sqrt_pos.2 hrad
  linarith

theorem classicalParameter_pos {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    0 < classicalParameter δ := by
  have hsquare : 0 < (δ - (1 : ℝ) / 2) ^ 2 :=
    sq_pos_of_ne_zero (by linarith)
  have hrad : 0 < δ * (1 - δ) := mul_pos hδ (by linarith)
  have hrad_lt : δ * (1 - δ) < ((1 : ℝ) / 2) ^ 2 := by
    nlinarith
  have hroot : Real.sqrt (δ * (1 - δ)) < (1 : ℝ) / 2 := by
    exact (Real.sqrt_lt' (by norm_num)).2 hrad_lt
  unfold classicalParameter
  linarith

theorem classicalParameter_mul_one_sub {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    classicalParameter δ * (1 - classicalParameter δ) =
      ((1 : ℝ) / 2 - δ) ^ 2 := by
  have hrad : 0 ≤ δ * (1 - δ) :=
    (mul_pos hδ (by linarith)).le
  have hsqrt := Real.sq_sqrt hrad
  unfold classicalParameter
  nlinarith

theorem hammingGamma_zero {a : ℝ} (ha : 0 < a) (ha' : a < 1) :
    MetricCodes.hammingGamma a 0 = 2 * Real.sqrt (a * (1 - a)) := by
  have hrad : 0 < a * (1 - a) := mul_pos ha (sub_pos.mpr ha')
  have hsqrt : Real.sqrt (a * (1 - a)) ≠ 0 :=
    (Real.sqrt_pos.2 hrad).ne'
  have hsquare := Real.sq_sqrt hrad.le
  unfold MetricCodes.hammingGamma
  simp only [sub_zero]
  field_simp [hsqrt]
  nlinarith

theorem hammingGamma_classicalParameter {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    MetricCodes.hammingGamma (classicalParameter δ) 0 = 1 - 2 * δ := by
  have ha := classicalParameter_pos hδ hδ'
  have ha' : classicalParameter δ < 1 :=
    (classicalParameter_lt_half hδ hδ').trans (by norm_num)
  rw [hammingGamma_zero ha ha',
    classicalParameter_mul_one_sub hδ hδ',
    Real.sqrt_sq (by linarith : 0 ≤ (1 : ℝ) / 2 - δ)]
  ring

def improvementSlope (a : ℝ) : ℝ :=
  2 / (1 - 2 * a) + 1

def improvementPath (a b : ℝ) : ℝ :=
  a + improvementSlope a * b

theorem improvementSlope_gt_one {a : ℝ} (ha : a < (1 : ℝ) / 2) :
    1 < improvementSlope a := by
  have hden : 0 < 1 - 2 * a := by linarith
  have hfrac : 0 < 2 / (1 - 2 * a) := by positivity
  unfold improvementSlope
  linarith

theorem tendsto_improvementPath_zero (a : ℝ) :
    Tendsto (improvementPath a) (𝓝[>] (0 : ℝ)) (nhds a) := by
  have hcontinuous : Continuous (improvementPath a) := by
    unfold improvementPath
    fun_prop
  simpa [improvementPath] using
    (hcontinuous.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      nhdsWithin_le_nhds

def spectralMarginPolynomial (a c b : ℝ) : ℝ :=
  let r := a * (1 - a)
  let p := c * (1 - 2 * a) - 1
  let q := c ^ 2 - 1
  r * (c * (1 - 2 * a) - 2) +
    b * (p ^ 2 + r * (2 - c ^ 2)) -
      2 * b ^ 2 * p * q + b ^ 3 * q ^ 2

theorem spectralMarginPolynomial_factor (a c b : ℝ) :
    ((a + c * b - b) * (1 - (a + c * b) - b)) ^ 2 -
      (a * (1 - a)) * ((a + c * b) * (1 - (a + c * b))) =
        b * spectralMarginPolynomial a c b := by
  unfold spectralMarginPolynomial
  ring

theorem spectralMarginPolynomial_continuous (a c : ℝ) :
    Continuous (spectralMarginPolynomial a c) := by
  unfold spectralMarginPolynomial
  fun_prop

theorem spectralMarginPolynomial_improvement_zero {a : ℝ}
    (ha : a < (1 : ℝ) / 2) :
    spectralMarginPolynomial a (improvementSlope a) 0 =
      a * (1 - a) * (1 - 2 * a) := by
  have hden : 1 - 2 * a ≠ 0 := by linarith
  have hden' : 1 - a * 2 ≠ 0 := by
    simpa [mul_comm] using hden
  unfold spectralMarginPolynomial improvementSlope
  field_simp [hden, hden']
  ; ring

theorem eventually_hammingGamma_improvement {a : ℝ}
    (ha : 0 < a) (ha' : a < (1 : ℝ) / 2) :
    ∀ᶠ b : ℝ in 𝓝[>] 0,
      MetricCodes.hammingGamma a 0 <
        MetricCodes.hammingGamma (improvementPath a b) b := by
  have hzero : 0 < spectralMarginPolynomial a (improvementSlope a) 0 := by
    rw [spectralMarginPolynomial_improvement_zero ha']
    have ha1 : 0 < 1 - a := by linarith
    have hhalf : 0 < 1 - 2 * a := by linarith
    exact mul_pos (mul_pos ha ha1) hhalf
  have hpoly :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        0 < spectralMarginPolynomial a (improvementSlope a) b := by
    have hcontinuous :
        ContinuousAt
          (spectralMarginPolynomial a (improvementSlope a)) 0 :=
      (spectralMarginPolynomial_continuous a (improvementSlope a)).continuousAt
    have hlim := hcontinuous.tendsto
    exact nhdsWithin_le_nhds (hlim.eventually (lt_mem_nhds hzero))
  have hhalf :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        improvementPath a b < (1 : ℝ) / 2 :=
    (tendsto_improvementPath_zero a).eventually (gt_mem_nhds ha')
  have hc : 1 < improvementSlope a := improvementSlope_gt_one ha'
  filter_upwards [hpoly, hhalf, self_mem_nhdsWithin]
    with b hbpoly hbhalf (hb : 0 < b)
  have hbpath : b < improvementPath a b := by
    unfold improvementPath
    nlinarith [mul_pos (sub_pos.mpr hc) hb]
  have hpath : 0 < improvementPath a b := lt_trans hb hbpath
  have hpath1 : improvementPath a b < 1 :=
    hbhalf.trans (by norm_num)
  have htail : 0 < 1 - improvementPath a b - b := by
    linarith
  have hbase : 0 < a * (1 - a) := mul_pos ha (by linarith)
  have hrad : 0 < improvementPath a b * (1 - improvementPath a b) :=
    mul_pos hpath (sub_pos.mpr hpath1)
  have hfactor :
      ((improvementPath a b - b) *
        (1 - improvementPath a b - b)) ^ 2 -
        (a * (1 - a)) *
          (improvementPath a b * (1 - improvementPath a b)) =
        b * spectralMarginPolynomial a (improvementSlope a) b := by
    simpa [improvementPath] using
      spectralMarginPolynomial_factor a (improvementSlope a) b
  have hmargin :
      0 < ((improvementPath a b - b) *
        (1 - improvementPath a b - b)) ^ 2 -
        (a * (1 - a)) *
          (improvementPath a b * (1 - improvementPath a b)) := by
    rw [hfactor]
    exact mul_pos hb hbpoly
  have htarget :
      0 < (improvementPath a b - b) *
        (1 - improvementPath a b - b) :=
    mul_pos (sub_pos.mpr hbpath) htail
  have hsquare :
      (Real.sqrt (a * (1 - a)) *
        Real.sqrt (improvementPath a b *
          (1 - improvementPath a b))) ^ 2 =
        (a * (1 - a)) *
          (improvementPath a b * (1 - improvementPath a b)) := by
    rw [mul_pow, Real.sq_sqrt hbase.le, Real.sq_sqrt hrad.le]
  have hroot :
      Real.sqrt (a * (1 - a)) *
          Real.sqrt (improvementPath a b *
            (1 - improvementPath a b)) <
        (improvementPath a b - b) *
          (1 - improvementPath a b - b) := by
    have hnonneg :
        0 ≤ Real.sqrt (a * (1 - a)) *
          Real.sqrt (improvementPath a b *
            (1 - improvementPath a b)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  have hquot :
      Real.sqrt (a * (1 - a)) <
        ((improvementPath a b - b) *
          (1 - improvementPath a b - b)) /
            Real.sqrt
              (improvementPath a b * (1 - improvementPath a b)) :=
    (lt_div_iff₀ (Real.sqrt_pos.2 hrad)).2 hroot
  rw [hammingGamma_zero ha (by linarith)]
  unfold MetricCodes.hammingGamma
  calc
    2 * Real.sqrt (a * (1 - a)) <
        2 * (((improvementPath a b - b) *
          (1 - improvementPath a b - b)) /
            Real.sqrt
              (improvementPath a b * (1 - improvementPath a b))) :=
      mul_lt_mul_of_pos_left hquot (by norm_num)
    _ = 2 * (improvementPath a b - b) *
        (1 - improvementPath a b - b) /
          Real.sqrt
            (improvementPath a b * (1 - improvementPath a b)) := by ring

theorem differentiableAt_binaryEntropy {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) :
    DifferentiableAt ℝ MetricCodes.binaryEntropy a := by
  have hfun : MetricCodes.binaryEntropy =
      (fun u : ℝ => Real.binEntropy u / Real.log 2) :=
    funext binaryEntropy_eq_binEntropy_div_log
  rw [hfun]
  exact
    (Real.differentiableAt_binEntropy ha.ne' (ne_of_lt ha')).div_const
      (Real.log 2)

theorem neg_mul_logb_le_binaryEntropy {b : ℝ}
    (hb : 0 ≤ b) (hb' : b ≤ 1) :
    b * (-Real.logb 2 b) ≤ MetricCodes.binaryEntropy b := by
  have hlog : Real.logb 2 (1 - b) ≤ 0 :=
    Real.logb_nonpos (by norm_num) (by linarith) (by linarith)
  have hterm : (1 - b) * Real.logb 2 (1 - b) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) hlog
  unfold MetricCodes.binaryEntropy
  nlinarith

theorem eventually_binaryEntropy_improvement {a : ℝ}
    (ha : 0 < a) (ha' : a < (1 : ℝ) / 2) :
    ∀ᶠ b : ℝ in 𝓝[>] 0,
      MetricCodes.binaryEntropy (improvementPath a b) -
        MetricCodes.binaryEntropy b < MetricCodes.binaryEntropy a := by
  let f : ℝ → ℝ := fun b =>
    MetricCodes.binaryEntropy (improvementPath a b)
  have hinner : DifferentiableAt ℝ (improvementPath a) 0 := by
    unfold improvementPath
    fun_prop
  have houter :
      DifferentiableAt ℝ MetricCodes.binaryEntropy (improvementPath a 0) := by
    simpa [improvementPath] using
      differentiableAt_binaryEntropy ha (ha'.trans (by norm_num))
  have hf : DifferentiableAt ℝ f 0 :=
    houter.comp 0 hinner
  let M : ℝ := deriv f 0 + 1
  have hM : deriv f 0 < M := by
    dsimp [M]
    linarith
  have hslope := hf.hasDerivAt.tendsto_slope_zero_right
  have hupper :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        b⁻¹ * (MetricCodes.binaryEntropy (improvementPath a b) -
          MetricCodes.binaryEntropy a) < M := by
    have h := hslope.eventually (gt_mem_nhds hM)
    filter_upwards [h] with b hb
    simpa [f, improvementPath, smul_eq_mul] using hb
  have hloglim :
      Tendsto (fun b : ℝ => -Real.logb 2 b) (𝓝[>] 0) atTop := by
    simpa [Function.comp_def] using
      tendsto_neg_atBot_atTop.comp
        (Real.tendsto_logb_nhdsGT_zero (by norm_num : (1 : ℝ) < 2))
  have hlog :
      ∀ᶠ b : ℝ in 𝓝[>] 0, M < -Real.logb 2 b :=
    hloglim.eventually (eventually_gt_atTop M)
  have hsmall : ∀ᶠ b : ℝ in 𝓝[>] 0, b < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hupper, hlog, hsmall, self_mem_nhdsWithin]
    with b hbound hlogb hb1 (hb : 0 < b)
  have houter_bound :
      MetricCodes.binaryEntropy (improvementPath a b) -
        MetricCodes.binaryEntropy a < b * M := by
    calc
      MetricCodes.binaryEntropy (improvementPath a b) -
          MetricCodes.binaryEntropy a =
        b * (b⁻¹ * (MetricCodes.binaryEntropy (improvementPath a b) -
          MetricCodes.binaryEntropy a)) := by
            field_simp [hb.ne']
      _ < b * M := mul_lt_mul_of_pos_left hbound hb
  have hsingular :
      b * M < b * (-Real.logb 2 b) :=
    mul_lt_mul_of_pos_left hlogb hb
  have hentropy := neg_mul_logb_le_binaryEntropy hb.le hb1.le
  linarith

theorem exists_strict_improving_feasible {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    ∃ a b : ℝ, Feasible δ a b ∧
      MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b < classicalRate δ := by
  let a₀ : ℝ := classicalParameter δ
  have ha₀ : 0 < a₀ := classicalParameter_pos hδ hδ'
  have ha₀half : a₀ < (1 : ℝ) / 2 :=
    classicalParameter_lt_half hδ hδ'
  have hgamma := eventually_hammingGamma_improvement ha₀ ha₀half
  have hentropy := eventually_binaryEntropy_improvement ha₀ ha₀half
  have hhalf :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        improvementPath a₀ b < (1 : ℝ) / 2 :=
    (tendsto_improvementPath_zero a₀).eventually
      (gt_mem_nhds ha₀half)
  have hc : 1 < improvementSlope a₀ :=
    improvementSlope_gt_one ha₀half
  have hall :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        Feasible δ (improvementPath a₀ b) b ∧
          MetricCodes.binaryEntropy (improvementPath a₀ b) -
            MetricCodes.binaryEntropy b < classicalRate δ := by
    filter_upwards [hgamma, hentropy, hhalf, self_mem_nhdsWithin]
      with b hgamma' hentropy' hhalf' (hb : 0 < b)
    have hbpath : b < improvementPath a₀ b := by
      unfold improvementPath
      nlinarith [mul_pos (sub_pos.mpr hc) hb]
    constructor
    · refine ⟨hb.le, hbpath, hhalf'.le, ?_⟩
      have hboundary : MetricCodes.hammingGamma a₀ 0 = 1 - 2 * δ := by
        dsimp [a₀]
        exact hammingGamma_classicalParameter hδ hδ'
      rwa [hboundary] at hgamma'
    · simpa [classicalRate, a₀] using hentropy'
  obtain ⟨b, hb⟩ := hall.exists
  exact ⟨improvementPath a₀ b, b, hb⟩

theorem variationalRate_lt_classicalRate {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    variationalRate δ < classicalRate δ := by
  obtain ⟨a, b, hfeasible, himprove⟩ :=
    exists_strict_improving_feasible hδ hδ'
  exact (variationalRate_le_of_feasible hfeasible).trans_lt himprove

def longitudinalDegree (a : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (a * (n : ℝ))

def transverseDegree (b : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (b * (n : ℝ))

theorem tendsto_longitudinal_ratio {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (longitudinalDegree a n : ℝ) / (n : ℝ))
      atTop (nhds a) := by
  simpa [longitudinalDegree, Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop ha).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

theorem tendsto_transverse_ratio {b : ℝ} (hb : 0 ≤ b) :
    Tendsto (fun n : ℕ => (transverseDegree b n : ℝ) / (n : ℝ))
      atTop (nhds b) := by
  simpa [transverseDegree, Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop hb).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

theorem tendsto_terminal_degree_ratio {a : ℝ}
    (ha : 0 < a) (r : ℕ) :
    Tendsto
      (fun n : ℕ => ((longitudinalDegree a n - r : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds a) := by
  have hoffset := tendsto_const_div_atTop_nhds_zero_nat (r : ℝ)
  have hmain := (tendsto_longitudinal_ratio ha.le).sub hoffset
  rw [sub_zero] at hmain
  have hgrowth : Tendsto (longitudinalDegree a) atTop atTop := by
    change Tendsto (fun n : ℕ => Nat.floor (a * (n : ℝ))) atTop atTop
    exact tendsto_nat_floor_mul_atTop a ha
  refine hmain.congr' ?_
  filter_upwards [hgrowth.eventually (eventually_ge_atTop r)] with n hn
  rw [Nat.cast_sub hn]
  ring

def normalizedCoefficient (x y z : ℝ) : ℝ :=
  ((x - y + z) * (1 - x - y)) /
    Real.sqrt ((x + z) * (1 - x))

theorem hammingJacobiEntry_eq_normalized
    (n k i : ℕ) (hn : 0 < n) :
    MetricCodes.hammingJacobiEntry n k i =
      normalizedCoefficient
        ((i : ℝ) / (n : ℝ))
        ((k : ℝ) / (n : ℝ))
        ((1 : ℝ) / (n : ℝ)) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := hnreal.ne'
  have hrad :
      (((i : ℝ) + 1) * ((n : ℝ) - (i : ℝ))) =
        (n : ℝ) ^ 2 *
          (((i : ℝ) / (n : ℝ) + (1 : ℝ) / (n : ℝ)) *
            (1 - (i : ℝ) / (n : ℝ))) := by
    field_simp [hnne]

  unfold MetricCodes.hammingJacobiEntry normalizedCoefficient
  rw [hrad, Real.sqrt_mul (sq_nonneg (n : ℝ)),
    Real.sqrt_sq hnreal.le]
  field_simp [hnne]

theorem normalizedCoefficient_zero (a b : ℝ) :
    normalizedCoefficient a b 0 = MetricCodes.hammingGamma a b / 2 := by
  unfold normalizedCoefficient MetricCodes.hammingGamma
  simp only [add_zero]
  ring

theorem tendsto_terminal_coefficient {a b : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hb : 0 ≤ b) (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.hammingJacobiEntry n (transverseDegree b n)
          (longitudinalDegree a n - r))
      atTop (nhds (MetricCodes.hammingGamma a b / 2)) := by
  have hx := tendsto_terminal_degree_ratio ha r
  have hy := tendsto_transverse_ratio hb
  have hz := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hnum := ((hx.sub hy).add hz).mul ((hone.sub hx).sub hy)
  have hrad := (hx.add hz).mul (hone.sub hx)
  have hroot := hrad.sqrt
  have hrootne : Real.sqrt (a * (1 - a)) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos ha (sub_pos.mpr ha'))).ne'
  have pointwise_div {f g : ℕ → ℝ} {l : ℝ}
      (h : Tendsto (f / g) atTop (nhds l)) :
      Tendsto (fun n => f n / g n) atTop (nhds l) :=
    h.congr' (Filter.Eventually.of_forall (fun _ => rfl))
  have hnorm :
      Tendsto
        (fun n : ℕ => normalizedCoefficient
          (((longitudinalDegree a n - r : ℕ) : ℝ) / (n : ℝ))
          ((transverseDegree b n : ℝ) / (n : ℝ))
          ((1 : ℝ) / (n : ℝ)))
        atTop (nhds (normalizedCoefficient a b 0)) := by
    simpa [normalizedCoefficient] using
      pointwise_div (hnum.div hroot (by simpa using hrootne))
  rw [normalizedCoefficient_zero] at hnorm
  refine hnorm.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (hammingJacobiEntry_eq_normalized n
    (transverseDegree b n) (longitudinalDegree a n - r) hn).symm

theorem tridiagonal_quadratic_sum
    (d : ℕ) (c v : ℕ → ℝ) :
    (∑ p ∈ Finset.range (d + 1),
      ∑ q ∈ Finset.range (d + 1),
        (if p + 1 = q then c p
          else if q + 1 = p then c q else 0) * v q * v p) =
      2 * ∑ p ∈ Finset.range d, c p * v p * v (p + 1) := by
  have hpoint (p q : ℕ) :
      (if p + 1 = q then c p
        else if q + 1 = p then c q else 0) * v q * v p =
        (if p + 1 = q then c p * v q * v p else 0) +
        (if q + 1 = p then c q * v q * v p else 0) := by
    by_cases h₁ : p + 1 = q
    · have h₂ : ¬ q + 1 = p := by omega
      simp [h₁, h₂]
    · by_cases h₂ : q + 1 = p
      · simp [h₁, h₂]
      · simp [h₁, h₂]
  have hupper :
      (∑ p ∈ Finset.range (d + 1),
        ∑ q ∈ Finset.range (d + 1),
          if p + 1 = q then c p * v q * v p else 0) =
        ∑ p ∈ Finset.range d, c p * v p * v (p + 1) := by
    simp only [Finset.sum_ite_eq, Finset.mem_range]
    rw [Finset.sum_range_succ]
    simp only [lt_self_iff_false, ite_false, add_zero]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' : p < d := Finset.mem_range.mp hp
    simp [hp', mul_comm, mul_left_comm, mul_assoc]
  have hlower :
      (∑ p ∈ Finset.range (d + 1),
        ∑ q ∈ Finset.range (d + 1),
          if q + 1 = p then c q * v q * v p else 0) =
        ∑ p ∈ Finset.range d, c p * v p * v (p + 1) := by
    rw [Finset.sum_comm]
    calc
      (∑ q ∈ Finset.range (d + 1),
        ∑ p ∈ Finset.range (d + 1),
          if q + 1 = p then c q * v q * v p else 0) =
        ∑ q ∈ Finset.range (d + 1),
          ∑ p ∈ Finset.range (d + 1),
            if q + 1 = p then c q * v p * v q else 0 := by
              apply Finset.sum_congr rfl
              intro q hq
              apply Finset.sum_congr rfl
              intro p hp
              split_ifs <;> ring
      _ = _ := hupper
  calc
    (∑ p ∈ Finset.range (d + 1),
      ∑ q ∈ Finset.range (d + 1),
        (if p + 1 = q then c p
          else if q + 1 = p then c q else 0) * v q * v p) =
        ∑ p ∈ Finset.range (d + 1),
          ∑ q ∈ Finset.range (d + 1),
            ((if p + 1 = q then c p * v q * v p else 0) +
             (if q + 1 = p then c q * v q * v p else 0)) := by
              apply Finset.sum_congr rfl
              intro p hp
              apply Finset.sum_congr rfl
              intro q hq
              exact hpoint p q
    _ =
        (∑ p ∈ Finset.range (d + 1),
          ∑ q ∈ Finset.range (d + 1),
            if p + 1 = q then c p * v q * v p else 0) +
        (∑ p ∈ Finset.range (d + 1),
          ∑ q ∈ Finset.range (d + 1),
            if q + 1 = p then c q * v q * v p else 0) := by
              simp_rw [Finset.sum_add_distrib]
    _ = 2 * ∑ p ∈ Finset.range d, c p * v p * v (p + 1) := by
      rw [hupper, hlower]
      ring

def terminalIndicator (d m p : ℕ) : ℝ :=
  if d - m ≤ p then 1 else 0

theorem terminal_indicator_sum (d m : ℕ) (hm : m ≤ d) :
    (∑ p ∈ Finset.range (d + 1), terminalIndicator d m p) =
      (m : ℝ) + 1 := by
  have hsplit : d + 1 = (d - m) + (m + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hfirst :
      (∑ p ∈ Finset.range (d - m), terminalIndicator d m p) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hp' : p < d - m := Finset.mem_range.mp hp
    simp [terminalIndicator, Nat.not_le.mpr hp']
  rw [hfirst, zero_add]
  calc
    (∑ p ∈ Finset.range (m + 1),
      terminalIndicator d m (d - m + p)) =
        ∑ _p ∈ Finset.range (m + 1), (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro p hp
          simp [terminalIndicator]
    _ = (m : ℝ) + 1 := by simp

theorem terminal_indicator_edge_sum
    (d m : ℕ) (hm : m ≤ d) (c : ℕ → ℝ) :
    (∑ p ∈ Finset.range d,
      c p * terminalIndicator d m p *
        terminalIndicator d m (p + 1)) =
      ∑ r ∈ Finset.range m, c (d - m + r) := by
  have hsplit : d = (d - m) + m := by omega
  rw [hsplit, Finset.sum_range_add]
  simp only [← hsplit]
  have hfirst :
      (∑ p ∈ Finset.range (d - m),
        c p * terminalIndicator d m p *
          terminalIndicator d m (p + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hp' : p < d - m := Finset.mem_range.mp hp
    simp [terminalIndicator, Nat.not_le.mpr hp']
  rw [hfirst, zero_add]
  apply Finset.sum_congr rfl
  intro p hp
  have h₁ : d - m ≤ d - m + p := by omega
  have h₂ : d - m ≤ d - m + p + 1 := by omega
  simp only [terminalIndicator, if_pos h₁, if_pos h₂, mul_one]

def terminalVector (k L m : ℕ) : Space k L :=
  WithLp.toLp 2
    (fun p : Fin (L - k + 1) => terminalIndicator (L - k) m p.val)

theorem terminalVector_last (k L m : ℕ) :
    terminalVector k L m (Fin.last (L - k)) = 1 := by
  change (if L - k - m ≤ L - k then (1 : ℝ) else 0) = 1
  simp

theorem terminalVector_ne_zero (k L m : ℕ) :
    terminalVector k L m ≠ 0 := by
  intro h
  have hx := congrArg
    (fun x : Space k L => x (Fin.last (L - k))) h
  simp [terminalVector_last] at hx

theorem terminalVector_norm_sq
    (k L m : ℕ) (hm : m ≤ L - k) :
    ‖terminalVector k L m‖ ^ 2 = (m : ℝ) + 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change
    (∑ p : Fin (L - k + 1),
      terminalIndicator (L - k) m p.val ^ 2) = (m : ℝ) + 1
  have hsq (p : ℕ) :
      terminalIndicator (L - k) m p ^ 2 =
        terminalIndicator (L - k) m p := by
    simp [terminalIndicator]
  simp_rw [hsq]
  rw [Fin.sum_univ_eq_sum_range]
  exact terminal_indicator_sum (L - k) m hm

theorem terminalVector_inner
    (n k L m : ℕ) (hkl : k ≤ L) (hm : m ≤ L - k) :
    @inner ℝ (Space k L) _
        (operator n k L (terminalVector k L m))
        (terminalVector k L m) =
      2 * ∑ r ∈ Finset.range m,
        MetricCodes.hammingJacobiEntry n k (L - m + r) := by
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  change
    (∑ p : Fin (L - k + 1),
      (∑ q : Fin (L - k + 1),
        (if p.val + 1 = q.val then
          MetricCodes.hammingJacobiEntry n k (k + p.val)
        else if q.val + 1 = p.val then
          MetricCodes.hammingJacobiEntry n k (k + q.val)
        else 0) * terminalIndicator (L - k) m q.val) *
        terminalIndicator (L - k) m p.val) =
      2 * ∑ r ∈ Finset.range m,
        MetricCodes.hammingJacobiEntry n k (L - m + r)
  simp_rw [Finset.sum_mul]
  let f : ℕ → ℝ := fun p =>
    ∑ q : Fin (L - k + 1),
      (if p + 1 = q.val then
        MetricCodes.hammingJacobiEntry n k (k + p)
      else if q.val + 1 = p then
        MetricCodes.hammingJacobiEntry n k (k + q.val)
      else 0) * terminalIndicator (L - k) m q.val *
        terminalIndicator (L - k) m p
  change
    (∑ p : Fin (L - k + 1), f p.val) =
      2 * ∑ r ∈ Finset.range m,
        MetricCodes.hammingJacobiEntry n k (L - m + r)
  rw [Fin.sum_univ_eq_sum_range f]
  dsimp only [f]
  have hfin (p : ℕ) :
      (∑ q : Fin (L - k + 1),
        (if p + 1 = q.val then
          MetricCodes.hammingJacobiEntry n k (k + p)
        else if q.val + 1 = p then
          MetricCodes.hammingJacobiEntry n k (k + q.val)
        else 0) * terminalIndicator (L - k) m q.val *
          terminalIndicator (L - k) m p) =
        ∑ q ∈ Finset.range (L - k + 1),
          (if p + 1 = q then
            MetricCodes.hammingJacobiEntry n k (k + p)
          else if q + 1 = p then
            MetricCodes.hammingJacobiEntry n k (k + q)
          else 0) * terminalIndicator (L - k) m q *
            terminalIndicator (L - k) m p := by
    let g : ℕ → ℝ := fun q =>
      (if p + 1 = q then
        MetricCodes.hammingJacobiEntry n k (k + p)
      else if q + 1 = p then
        MetricCodes.hammingJacobiEntry n k (k + q)
      else 0) * terminalIndicator (L - k) m q *
        terminalIndicator (L - k) m p
    change (∑ q : Fin (L - k + 1), g q.val) =
      ∑ q ∈ Finset.range (L - k + 1), g q
    exact Fin.sum_univ_eq_sum_range g (L - k + 1)
  simp_rw [hfin]
  rw [tridiagonal_quadratic_sum]
  rw [terminal_indicator_edge_sum (L - k) m hm]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  omega

theorem terminalVector_rayleigh
    (n k L m : ℕ) (hkl : k ≤ L) (hm : m ≤ L - k) :
    rayleigh n k L (terminalVector k L m) =
      (2 * ∑ r ∈ Finset.range m,
        MetricCodes.hammingJacobiEntry n k (L - m + r)) /
          ((m : ℝ) + 1) := by
  rw [rayleigh_eq_inner,
    terminalVector_inner n k L m hkl hm,
    terminalVector_norm_sq k L m hm]

theorem terminal_edge_sum_le_top
    (n k L m : ℕ) (hkl : k ≤ L) (hm : m ≤ L - k) :
    (2 * ∑ r ∈ Finset.range m,
      MetricCodes.hammingJacobiEntry n k (L - m + r)) /
        ((m : ℝ) + 1) ≤ topEigenvalue n k L := by
  rw [← terminalVector_rayleigh n k L m hkl hm]
  exact rayleigh_le_top n k L
    (terminalVector k L m) (terminalVector_ne_zero k L m)

theorem eventually_transverse_add_le_longitudinal
    {a b : ℝ} (hb : 0 ≤ b) (hba : b < a) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      transverseDegree b n + m ≤ longitudinalDegree a n := by
  let ε : ℝ := (a - b) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hεlt : ε < a - b := by
    dsimp [ε]
    linarith
  have ha : 0 ≤ a := (lt_of_le_of_lt hb hba).le
  have hratio :=
    ((tendsto_longitudinal_ratio ha).sub
      (tendsto_transverse_ratio hb)).eventually
        (lt_mem_nhds hεlt)
  have hgrowth :
      Tendsto (fun n : ℕ => ε * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hε
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hgrowth.eventually (eventually_ge_atTop (m : ℝ))
  filter_upwards [hratio, hlarge, eventually_gt_atTop (0 : ℕ)]
    with n hnratio hnlarge hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmul := mul_lt_mul_of_pos_right hnratio hnreal
  have hidentity :
      (((longitudinalDegree a n : ℝ) / (n : ℝ) -
        (transverseDegree b n : ℝ) / (n : ℝ)) * (n : ℝ)) =
        (longitudinalDegree a n : ℝ) -
          (transverseDegree b n : ℝ) := by
    field_simp [hnreal.ne']
  rw [hidentity] at hmul
  have hreal :
      (transverseDegree b n : ℝ) + (m : ℝ) ≤
        (longitudinalDegree a n : ℝ) := by
    linarith
  exact_mod_cast hreal

def terminalEdgeRayleigh (a b : ℝ) (m n : ℕ) : ℝ :=
  (2 * ∑ r ∈ Finset.range m,
    MetricCodes.hammingJacobiEntry n (transverseDegree b n)
      (longitudinalDegree a n - (m - r))) /
        ((m : ℝ) + 1)

theorem tendsto_terminalEdgeRayleigh {a b : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hb : 0 ≤ b) (m : ℕ) :
    Tendsto (terminalEdgeRayleigh a b m) atTop
      (nhds
        (((m : ℝ) / ((m : ℝ) + 1)) * MetricCodes.hammingGamma a b)) := by
  have hsum :
      Tendsto
        (fun n : ℕ => ∑ r ∈ Finset.range m,
          MetricCodes.hammingJacobiEntry n (transverseDegree b n)
            (longitudinalDegree a n - (m - r)))
        atTop
        (nhds (∑ _r ∈ Finset.range m,
          MetricCodes.hammingGamma a b / 2)) := by
    apply tendsto_finsetSum
    intro r hr
    exact tendsto_terminal_coefficient ha ha' hb (m - r)
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hquot := (htwo.mul hsum).div_const ((m : ℝ) + 1)
  change Tendsto
    (fun n : ℕ => terminalEdgeRayleigh a b m n) atTop
      (nhds (((m : ℝ) / ((m : ℝ) + 1)) * MetricCodes.hammingGamma a b))
  simpa [terminalEdgeRayleigh, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using hquot

theorem terminalEdgeRayleigh_le_top
    (a b : ℝ) (m n : ℕ)
    (hfit : transverseDegree b n + m ≤ longitudinalDegree a n) :
    terminalEdgeRayleigh a b m n ≤
      topEigenvalue n (transverseDegree b n) (longitudinalDegree a n) := by
  have hkl : transverseDegree b n ≤ longitudinalDegree a n := by omega
  have hm : m ≤ longitudinalDegree a n - transverseDegree b n := by omega
  have hsum :
      (∑ r ∈ Finset.range m,
        MetricCodes.hammingJacobiEntry n (transverseDegree b n)
          (longitudinalDegree a n - (m - r))) =
        ∑ r ∈ Finset.range m,
          MetricCodes.hammingJacobiEntry n (transverseDegree b n)
            (longitudinalDegree a n - m + r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < m := Finset.mem_range.mp hr
    congr 1
    omega
  unfold terminalEdgeRayleigh
  rw [hsum]
  exact terminal_edge_sum_le_top n
    (transverseDegree b n) (longitudinalDegree a n) m hkl hm

theorem eventually_topEigenvalue_gt {a b s : ℝ}
    (hb : 0 ≤ b) (hba : b < a) (ha : a ≤ (1 : ℝ) / 2)
    (hs : s < MetricCodes.hammingGamma a b) :
    ∀ᶠ n : ℕ in atTop,
      s < topEigenvalue n
        (transverseDegree b n) (longitudinalDegree a n) := by
  have ha0 : 0 < a := lt_of_le_of_lt hb hba
  have ha1 : a < 1 := lt_of_le_of_lt ha (by norm_num)
  have hsecond : 0 < 1 - a - b := by linarith
  have hgamma : 0 < MetricCodes.hammingGamma a b := by
    unfold MetricCodes.hammingGamma
    apply div_pos
    · exact mul_pos (mul_pos (by norm_num) (sub_pos.mpr hba)) hsecond
    · exact Real.sqrt_pos.2 (mul_pos ha0 (sub_pos.mpr ha1))
  let ε : ℝ := (MetricCodes.hammingGamma a b - s) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (MetricCodes.hammingGamma a b / ε)
  have hprod : MetricCodes.hammingGamma a b < (m : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hm
  have hden : 0 < (m : ℝ) + 1 := by positivity
  have hrem : MetricCodes.hammingGamma a b / ((m : ℝ) + 1) < ε := by
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hidentity :
      ((m : ℝ) / ((m : ℝ) + 1)) * MetricCodes.hammingGamma a b =
        MetricCodes.hammingGamma a b -
          MetricCodes.hammingGamma a b / ((m : ℝ) + 1) := by
    field_simp [hden.ne']
    ; ring
  have hbelow :
      s < ((m : ℝ) / ((m : ℝ) + 1)) * MetricCodes.hammingGamma a b := by
    rw [hidentity]
    dsimp [ε] at hrem
    linarith
  have hquot := (tendsto_terminalEdgeRayleigh ha0 ha1 hb m).eventually
    (lt_mem_nhds hbelow)
  filter_upwards [hquot,
    eventually_transverse_add_le_longitudinal hb hba m] with n hn hfit
  exact hn.trans_le (terminalEdgeRayleigh_le_top a b m n hfit)

theorem longitudinalDegree_le_dimension {a : ℝ}
    (ha : a ≤ 1) (n : ℕ) :
    longitudinalDegree a n ≤ n := by
  unfold longitudinalDegree
  apply Nat.floor_le_of_le
  simpa using mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg n)

theorem complement_longitudinalDegree_floor_le {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1) (n : ℕ) :
    longitudinalDegree (1 - a) n ≤ n - longitudinalDegree a n := by
  have hk := longitudinalDegree_le_dimension ha' n
  have hfloor : (longitudinalDegree a n : ℝ) ≤ a * (n : ℝ) := by
    unfold longitudinalDegree
    exact Nat.floor_le (mul_nonneg ha (Nat.cast_nonneg n))
  change Nat.floor ((1 - a) * (n : ℝ)) ≤
    n - longitudinalDegree a n
  apply Nat.floor_le_of_le
  change (1 - a) * (n : ℝ) ≤
    ((n - longitudinalDegree a n : ℕ) : ℝ)
  rw [Nat.cast_sub hk]
  nlinarith

theorem tendsto_complement_longitudinalDegree {a : ℝ}
    (ha : 0 ≤ a) (ha' : a < 1) :
    Tendsto (fun n : ℕ => n - longitudinalDegree a n) atTop atTop := by
  have hcomp : Tendsto (longitudinalDegree (1 - a)) atTop atTop := by
    change Tendsto
      (fun n : ℕ => Nat.floor ((1 - a) * (n : ℝ))) atTop atTop
    exact tendsto_nat_floor_mul_atTop (1 - a) (sub_pos.mpr ha')
  exact tendsto_atTop_mono
    (fun n => complement_longitudinalDegree_floor_le ha ha'.le n)
    hcomp

theorem tendsto_complement_longitudinal_ratio {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1) :
    Tendsto
      (fun n : ℕ => ((n - longitudinalDegree a n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (1 - a)) := by
  have hone : Tendsto
      (fun n : ℕ => (n : ℝ) / (n : ℝ)) atTop (nhds 1) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    refine hconst.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    simp [hn]
  have hmain := hone.sub (tendsto_longitudinal_ratio ha)
  refine hmain.congr' (Filter.Eventually.of_forall fun n => ?_)
  change
    (n : ℝ) / (n : ℝ) -
      (longitudinalDegree a n : ℝ) / (n : ℝ) =
        ((n - longitudinalDegree a n : ℕ) : ℝ) / (n : ℝ)
  rw [Nat.cast_sub (longitudinalDegree_le_dimension ha' n)]
  ring

theorem tendsto_log_choose_longitudinal {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) :
    Tendsto
      (fun n : ℕ =>
        Real.log (n.choose (longitudinalDegree a n) : ℝ) / (n : ℝ))
      atTop (nhds (Real.binEntropy a)) := by
  have hgrowth : Tendsto (longitudinalDegree a) atTop atTop := by
    change Tendsto (fun n : ℕ => Nat.floor (a * (n : ℝ))) atTop atTop
    exact tendsto_nat_floor_mul_atTop a ha
  have hcomplement := tendsto_complement_longitudinalDegree ha.le ha'
  have hratio := tendsto_longitudinal_ratio ha.le
  have hcomplementratio :=
    tendsto_complement_longitudinal_ratio ha.le ha'.le
  have hchoose := SpherePacking.tendsto_log_add_choose_div
    (longitudinalDegree a)
    (fun n : ℕ => n - longitudinalDegree a n)
    a (1 - a)
    hgrowth hcomplement hratio hcomplementratio ha (sub_pos.mpr ha')
  have hlimit :
      (a + (1 - a)) * Real.log (a + (1 - a)) -
        a * Real.log a - (1 - a) * Real.log (1 - a) =
        Real.binEntropy a := by
    simp [Real.binEntropy, Real.log_inv]
    ring
  rw [hlimit] at hchoose
  refine hchoose.congr' (Filter.Eventually.of_forall fun n => ?_)
  have hk := longitudinalDegree_le_dimension ha'.le n
  have hsum :
      longitudinalDegree a n + (n - longitudinalDegree a n) = n := by
    omega
  rw [hsum]

theorem tendsto_logb_choose_longitudinal {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2 (n.choose (longitudinalDegree a n) : ℝ) /
          (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy a)) := by
  have h := (tendsto_log_choose_longitudinal ha ha').div_const (Real.log 2)
  rw [← binaryEntropy_eq_binEntropy_div_log a] at h
  refine h.congr' (Filter.Eventually.of_forall fun n => ?_)
  unfold Real.logb
  ring

theorem longitudinalDegree_le_half {a : ℝ}
    (ha : a ≤ (1 : ℝ) / 2) (n : ℕ) :
    longitudinalDegree a n ≤ n / 2 := by
  unfold longitudinalDegree
  calc
    Nat.floor (a * (n : ℝ)) ≤ Nat.floor ((n : ℝ) / 2) := by
      apply Nat.floor_mono
      have h := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg n)
      linarith
    _ = n / 2 := by
      simpa using (Nat.floor_div_eq_div (K := ℝ) n 2)

theorem choose_le_ambientDimension (n k L : ℕ) (hkL : k ≤ L) :
    n.choose L ≤ ambientDimension n k L := by
  unfold ambientDimension
  have hindex : L - k ∈ Finset.range (L - k + 1) := by
    simp
  have hterm := Finset.single_le_sum
    (s := Finset.range (L - k + 1))
    (f := fun j => n.choose (k + j))
    (fun j _ => Nat.zero_le _) hindex
  have hdegree : k + (L - k) = L := by omega
  simpa [hdegree] using hterm

theorem ambientDimension_le_mul_choose
    (n k L : ℕ) (hkL : k ≤ L) (hL : L ≤ n / 2) :
    ambientDimension n k L ≤ (n + 1) * n.choose L := by
  calc
    ambientDimension n k L =
        ∑ j ∈ Finset.range (L - k + 1), n.choose (k + j) := rfl
    _ ≤ ∑ _j ∈ Finset.range (L - k + 1), n.choose L := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j < L - k + 1 := Finset.mem_range.mp hj
      apply MetricCodes.choose_monotone_to_half n (by omega) hL
    _ = (L - k + 1) * n.choose L := by simp
    _ ≤ (n + 1) * n.choose L := by
      apply Nat.mul_le_mul_right
      omega

theorem choose_le_mul_hammingFibreDimension
    {n k : ℕ} (hk : 2 * k ≤ n) :
    n.choose k ≤ (n + 1) * MetricCodes.hammingFibreDimension n k := by
  cases k with
  | zero => simp [MetricCodes.hammingFibreDimension, MetricCodes.booleanHarmonicDimension]
  | succ j =>
      change n.choose (j + 1) ≤
        (n + 1) * (n.choose (j + 1) - n.choose j)
      have hpositive :=
        hammingFibreDimension_pos (n := n) (k := j + 1) hk
      change 0 < n.choose (j + 1) - n.choose j at hpositive
      have hmono : n.choose j ≤ n.choose (j + 1) :=
        (Nat.sub_pos_iff_lt.mp hpositive).le
      have hrec :
          (n.choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) =
            (n.choose j : ℝ) * ((n - j : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_succ_right_eq n j
      have hidentity :
          ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) *
              ((n - j : ℕ) : ℝ) =
            (n.choose (j + 1) : ℝ) *
              (((n - j : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ)) := by
        rw [Nat.cast_sub hmono]
        calc
          ((n.choose (j + 1) : ℝ) - (n.choose j : ℝ)) *
              ((n - j : ℕ) : ℝ) =
            (n.choose (j + 1) : ℝ) * ((n - j : ℕ) : ℝ) -
              (n.choose j : ℝ) * ((n - j : ℕ) : ℝ) := by ring
          _ = (n.choose (j + 1) : ℝ) * ((n - j : ℕ) : ℝ) -
              (n.choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
                rw [← hrec]
          _ = (n.choose (j + 1) : ℝ) *
              (((n - j : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ)) := by ring
      have hfactorNat : j + 2 ≤ n - j := by omega
      have hfactorReal :
          (1 : ℝ) ≤
            ((n - j : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ) := by
        have hcast : ((j + 2 : ℕ) : ℝ) ≤ ((n - j : ℕ) : ℝ) := by
          exact_mod_cast hfactorNat
        have hcastj : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by
          norm_num
        rw [hcastj]
        push_cast at hcast
        linarith
      have hlower :
          (n.choose (j + 1) : ℝ) ≤
            ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) *
              ((n - j : ℕ) : ℝ) := by
        rw [hidentity]
        nlinarith [Nat.cast_nonneg (α := ℝ) (n.choose (j + 1))]
      have hrange :
          ((n - j : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show n - j ≤ n + 1 by omega)
      have hupper :
          ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) *
              ((n - j : ℕ) : ℝ) ≤
            ((n + 1 : ℕ) : ℝ) *
              ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) := by
        calc
          ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) *
              ((n - j : ℕ) : ℝ) ≤
            ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) *
              ((n + 1 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hrange (Nat.cast_nonneg _)
          _ = ((n + 1 : ℕ) : ℝ) *
              ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) := by ring
      exact_mod_cast hlower.trans hupper

theorem hammingFibreDimension_le_choose (n k : ℕ) :
    MetricCodes.hammingFibreDimension n k ≤ n.choose k := by
  cases k with
  | zero => simp [MetricCodes.hammingFibreDimension, MetricCodes.booleanHarmonicDimension]
  | succ j =>
      change n.choose (j + 1) - n.choose j ≤ n.choose (j + 1)
      exact Nat.sub_le _ _

theorem tendsto_logb_succ_div :
    Tendsto
      (fun n : ℕ => Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  have hupper := SpherePacking.tendsto_log_two_mul_natCast_div_natCast
  have hnonneg :
      ∀ᶠ n : ℕ in atTop,
        (0 : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ n + 1 by omega)
    · exact Nat.cast_nonneg n
  have hle :
      ∀ᶠ n : ℕ in atTop,
        Real.log ((n + 1 : ℕ) : ℝ) / (n : ℝ) ≤
          Real.log (2 * (n : ℝ)) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    apply (div_le_div_iff_of_pos_right hnreal).2
    apply Real.log_le_log
    · positivity
    · have hnat : n + 1 ≤ 2 * n := by omega
      exact_mod_cast hnat
  have hnatural :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hzero hupper hnonneg hle
  have hbase := hnatural.div_const (Real.log 2)
  have hbase' :
      Tendsto
        (fun n : ℕ =>
          (Real.log ((n + 1 : ℕ) : ℝ) / (n : ℝ)) / Real.log 2)
        atTop (nhds 0) := by
    simpa using hbase
  refine hbase'.congr' (Filter.Eventually.of_forall fun n => ?_)
  unfold Real.logb
  ring

theorem tendsto_logb_ambientDimension {a b : ℝ}
    (hb : 0 ≤ b) (hba : b < a) (ha : a ≤ (1 : ℝ) / 2) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (ambientDimension n
            (transverseDegree b n) (longitudinalDegree a n) : ℝ) /
          (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy a)) := by
  have ha0 : 0 < a := lt_of_le_of_lt hb hba
  have ha1 : a < 1 := lt_of_le_of_lt ha (by norm_num)
  have hchoose := tendsto_logb_choose_longitudinal ha0 ha1
  have hpoly := tendsto_logb_succ_div
  have hupperlim :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ) +
            Real.logb 2
              (n.choose (longitudinalDegree a n) : ℝ) / (n : ℝ))
        atTop (nhds (MetricCodes.binaryEntropy a)) := by
    simpa using hpoly.add hchoose
  have hfit := eventually_transverse_add_le_longitudinal hb hba 0
  have hlower :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
            (n.choose (longitudinalDegree a n) : ℝ) / (n : ℝ) ≤
          Real.logb 2
            (ambientDimension n (transverseDegree b n)
              (longitudinalDegree a n) : ℝ) / (n : ℝ) := by
    filter_upwards [hfit, eventually_gt_atTop (0 : ℕ)] with n hkn hn
    have hkL : transverseDegree b n ≤ longitudinalDegree a n := by omega
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    apply (div_le_div_iff_of_pos_right hnreal).2
    apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    · exact_mod_cast Nat.choose_pos
        (longitudinalDegree_le_dimension ha1.le n)
    · exact_mod_cast choose_le_ambientDimension n
        (transverseDegree b n) (longitudinalDegree a n) hkL
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
            (ambientDimension n (transverseDegree b n)
              (longitudinalDegree a n) : ℝ) / (n : ℝ) ≤
          Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ) +
            Real.logb 2
              (n.choose (longitudinalDegree a n) : ℝ) / (n : ℝ) := by
    filter_upwards [hfit, eventually_gt_atTop (0 : ℕ)] with n hkn hn
    have hkL : transverseDegree b n ≤ longitudinalDegree a n := by omega
    have hhalf := longitudinalDegree_le_half ha n
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hchoosepos :
        0 < (n.choose (longitudinalDegree a n) : ℝ) := by
      exact_mod_cast Nat.choose_pos
        (longitudinalDegree_le_dimension ha1.le n)
    have hambientpos :
        0 < (ambientDimension n (transverseDegree b n)
          (longitudinalDegree a n) : ℝ) := by
      have hle := choose_le_ambientDimension n
        (transverseDegree b n) (longitudinalDegree a n) hkL
      exact lt_of_lt_of_le hchoosepos (by exact_mod_cast hle)
    calc
      Real.logb 2
          (ambientDimension n (transverseDegree b n)
            (longitudinalDegree a n) : ℝ) / (n : ℝ) ≤
        Real.logb 2
          (((n + 1) * n.choose (longitudinalDegree a n) : ℕ) : ℝ) /
            (n : ℝ) := by
          apply (div_le_div_iff_of_pos_right hnreal).2
          apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
            hambientpos
          exact_mod_cast ambientDimension_le_mul_choose n
            (transverseDegree b n) (longitudinalDegree a n) hkL hhalf
      _ = Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ) +
            Real.logb 2
              (n.choose (longitudinalDegree a n) : ℝ) / (n : ℝ) := by
          push_cast
          rw [Real.logb_mul (by positivity) hchoosepos.ne']
          ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hchoose hupperlim hlower hupper

theorem tendsto_logb_hammingFibreDimension {b : ℝ}
    (hb : 0 < b) (hb' : b ≤ (1 : ℝ) / 2) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (MetricCodes.hammingFibreDimension n (transverseDegree b n) : ℝ) /
          (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy b)) := by
  have hb1 : b < 1 := lt_of_le_of_lt hb' (by norm_num)
  have hchoose :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2
            (n.choose (transverseDegree b n) : ℝ) / (n : ℝ))
        atTop (nhds (MetricCodes.binaryEntropy b)) := by
    simpa [transverseDegree, longitudinalDegree] using
      tendsto_logb_choose_longitudinal hb hb1
  have hpoly := tendsto_logb_succ_div
  have hlowerlim :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2
              (n.choose (transverseDegree b n) : ℝ) / (n : ℝ) -
            Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ))
        atTop (nhds (MetricCodes.binaryEntropy b)) := by
    simpa using hchoose.sub hpoly
  have hlower :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
              (n.choose (transverseDegree b n) : ℝ) / (n : ℝ) -
            Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ) ≤
          Real.logb 2
            (MetricCodes.hammingFibreDimension n
              (transverseDegree b n) : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hkhalf : 2 * transverseDegree b n ≤ n := by
      have h : transverseDegree b n ≤ n / 2 := by
        simpa [transverseDegree, longitudinalDegree] using
          longitudinalDegree_le_half hb' n
      omega
    have hfibre :
        0 < (MetricCodes.hammingFibreDimension n
          (transverseDegree b n) : ℝ) := by
      exact_mod_cast hammingFibreDimension_pos hkhalf
    have hchoosepos : 0 < (n.choose (transverseDegree b n) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : transverseDegree b n ≤ n)
    have hlog :
        Real.logb 2 (n.choose (transverseDegree b n) : ℝ) ≤
          Real.logb 2 ((n + 1 : ℕ) : ℝ) +
            Real.logb 2
              (MetricCodes.hammingFibreDimension n
                (transverseDegree b n) : ℝ) := by
      rw [← Real.logb_mul (by positivity) hfibre.ne']
      apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        hchoosepos
      exact_mod_cast choose_le_mul_hammingFibreDimension hkhalf
    calc
      Real.logb 2 (n.choose (transverseDegree b n) : ℝ) / (n : ℝ) -
          Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ) =
        (Real.logb 2 (n.choose (transverseDegree b n) : ℝ) -
          Real.logb 2 ((n + 1 : ℕ) : ℝ)) / (n : ℝ) := by ring
      _ ≤ Real.logb 2
          (MetricCodes.hammingFibreDimension n
            (transverseDegree b n) : ℝ) / (n : ℝ) := by
        apply (div_le_div_iff_of_pos_right hnreal).2
        linarith
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
            (MetricCodes.hammingFibreDimension n
              (transverseDegree b n) : ℝ) / (n : ℝ) ≤
          Real.logb 2
            (n.choose (transverseDegree b n) : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hkhalf : 2 * transverseDegree b n ≤ n := by
      have h : transverseDegree b n ≤ n / 2 := by
        simpa [transverseDegree, longitudinalDegree] using
          longitudinalDegree_le_half hb' n
      omega
    have hfibre :
        0 < (MetricCodes.hammingFibreDimension n
          (transverseDegree b n) : ℝ) := by
      exact_mod_cast hammingFibreDimension_pos hkhalf
    apply (div_le_div_iff_of_pos_right hnreal).2
    apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      hfibre
    exact_mod_cast hammingFibreDimension_le_choose n
      (transverseDegree b n)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowerlim hchoose hlower hupper

def binaryRate (δ : ℝ) : ℝ :=
  Filter.limsup
    (fun n : ℕ =>
      Real.logb 2
        (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) / (n : ℝ))
    Filter.atTop

theorem tendsto_ceil_distance_ratio {δ : ℝ} (hδ : 0 ≤ δ) :
    Tendsto
      (fun n : ℕ => (Nat.ceil (δ * (n : ℝ)) : ℝ) / (n : ℝ))
      atTop (nhds δ) := by
  simpa [Function.comp_def] using
    (tendsto_nat_ceil_mul_div_atTop hδ).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

theorem tendsto_threshold_ceil {δ : ℝ} (hδ : 0 ≤ δ) :
    Tendsto
      (fun n : ℕ => threshold n (Nat.ceil (δ * (n : ℝ))))
      atTop (nhds (1 - 2 * δ)) := by
  have hratio := tendsto_ceil_distance_ratio hδ
  have hlimit :=
    (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := (2 : ℝ))).mul hratio)
  refine hlimit.congr' (Filter.Eventually.of_forall fun n => ?_)
  unfold threshold
  ring

theorem ceil_distance_pos {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (hn : 0 < n) :
    0 < Nat.ceil (δ * (n : ℝ)) := by
  apply Nat.ceil_pos.mpr
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact mul_pos hδ hnreal

def windowFibreQuotient (a b : ℝ) (n : ℕ) : ℝ :=
  (ambientDimension n (transverseDegree b n)
      (longitudinalDegree a n) : ℝ) /
    (MetricCodes.hammingFibreDimension n (transverseDegree b n) : ℝ)

theorem windowFibreQuotient_pos_of_fit {a b : ℝ} {n : ℕ}
    (ha : a ≤ (1 : ℝ) / 2)
    (hfit : transverseDegree b n ≤ longitudinalDegree a n) :
    0 < windowFibreQuotient a b n := by
  have hhalf := longitudinalDegree_le_half ha n
  have hkhalf : 2 * transverseDegree b n ≤ n := by omega
  have hfibre :
      0 < (MetricCodes.hammingFibreDimension n (transverseDegree b n) : ℝ) := by
    exact_mod_cast hammingFibreDimension_pos hkhalf
  have haone : a ≤ 1 := by linarith
  have hchoose : 0 < (n.choose (longitudinalDegree a n) : ℝ) := by
    exact_mod_cast
      Nat.choose_pos (longitudinalDegree_le_dimension haone n)
  have hambient :
      0 < (ambientDimension n (transverseDegree b n)
        (longitudinalDegree a n) : ℝ) := by
    have hle := choose_le_ambientDimension n
      (transverseDegree b n) (longitudinalDegree a n) hfit
    exact lt_of_lt_of_le hchoose (by exact_mod_cast hle)
  exact div_pos hambient hfibre

theorem eventually_windowFibreQuotient_pos {a b : ℝ}
    (hb : 0 ≤ b) (hba : b < a) (ha : a ≤ (1 : ℝ) / 2) :
    ∀ᶠ n : ℕ in atTop, 0 < windowFibreQuotient a b n := by
  filter_upwards [eventually_transverse_add_le_longitudinal hb hba 0]
    with n hfit
  apply windowFibreQuotient_pos_of_fit ha
  omega

theorem tendsto_logb_windowFibreQuotient {a b : ℝ}
    (hb : 0 < b) (hba : b < a) (ha : a ≤ (1 : ℝ) / 2) :
    Tendsto
      (fun n : ℕ => Real.logb 2 (windowFibreQuotient a b n) / (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b)) := by
  have hbhalf : b ≤ (1 : ℝ) / 2 := hba.le.trans ha
  have hnum := tendsto_logb_ambientDimension hb.le hba ha
  have hden := tendsto_logb_hammingFibreDimension hb hbhalf
  have hdiff := hnum.sub hden
  refine hdiff.congr' ?_
  filter_upwards [eventually_transverse_add_le_longitudinal hb.le hba 0]
    with n hfit
  have hkn : transverseDegree b n ≤ longitudinalDegree a n := by omega
  have hhalf := longitudinalDegree_le_half ha n
  have hkhalf : 2 * transverseDegree b n ≤ n := by omega
  have hfibre :
      0 < (MetricCodes.hammingFibreDimension n (transverseDegree b n) : ℝ) := by
    exact_mod_cast hammingFibreDimension_pos hkhalf
  have haone : a ≤ 1 := by linarith
  have hchoose : 0 < (n.choose (longitudinalDegree a n) : ℝ) := by
    exact_mod_cast
      Nat.choose_pos (longitudinalDegree_le_dimension haone n)
  have hambient :
      0 < (ambientDimension n (transverseDegree b n)
        (longitudinalDegree a n) : ℝ) := by
    have hle := choose_le_ambientDimension n
      (transverseDegree b n) (longitudinalDegree a n) hkn
    exact lt_of_lt_of_le hchoose (by exact_mod_cast hle)
  unfold windowFibreQuotient
  rw [Real.logb_div hambient.ne' hfibre.ne']
  ring

theorem tendsto_logb_const_mul_windowFibreQuotient
    {a b C : ℝ} (hb : 0 < b) (hba : b < a)
    (ha : a ≤ (1 : ℝ) / 2) (hC : 0 < C) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2 (C * windowFibreQuotient a b n) / (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b)) := by
  have hconst :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.logb 2 C)
  have hquot := tendsto_logb_windowFibreQuotient hb hba ha
  have hsum :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2 C / (n : ℝ) +
            Real.logb 2 (windowFibreQuotient a b n) / (n : ℝ))
        atTop (nhds (MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b)) := by
    simpa using hconst.add hquot
  refine hsum.congr' ?_
  filter_upwards [eventually_windowFibreQuotient_pos hb.le hba ha]
    with n hpos
  rw [Real.logb_mul hC.ne' hpos.ne']
  ring

theorem codeLogRate_nonneg (δ : ℝ) (n : ℕ) :
    0 ≤ Real.logb 2
      (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) / (n : ℝ) := by
  apply div_nonneg
  · apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
    exact_mod_cast codeNumber_pos n (Nat.ceil (δ * (n : ℝ)))
  · exact Nat.cast_nonneg n

theorem binaryRate_le_of_eventually {δ r : ℝ} {u : ℕ → ℝ}
    (hu : Tendsto u atTop (nhds r))
    (hbound : ∀ᶠ n : ℕ in atTop,
      Real.logb 2
        (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) / (n : ℝ) ≤ u n) :
    binaryRate δ ≤ r := by
  let w : ℕ → ℝ := fun n =>
    Real.logb 2
      (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) / (n : ℝ)
  have hlower : atTop.IsBoundedUnder (· ≥ ·) w :=
    Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall (codeLogRate_nonneg δ))
  have hcob : atTop.IsCoboundedUnder (· ≤ ·) w :=
    hlower.isCoboundedUnder_le
  have hcomparison : Filter.limsup w atTop ≤ Filter.limsup u atTop :=
    Filter.limsup_le_limsup hbound hcob hu.isBoundedUnder_le
  change Filter.limsup w atTop ≤ r
  exact hcomparison.trans_eq hu.limsup_eq

theorem ceil_distance_le_dimension {δ : ℝ} (hδ : δ ≤ 1) (n : ℕ) :
    Nat.ceil (δ * (n : ℝ)) ≤ n := by
  apply Nat.ceil_le.mpr
  calc
    δ * (n : ℝ) ≤ 1 * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg n)
    _ = (n : ℝ) := one_mul _

theorem threshold_ceil_numerator_le_two {δ : ℝ}
    (hδ : δ ≤ 1) {n : ℕ} (hn : 0 < n) :
    1 - threshold n (Nat.ceil (δ * (n : ℝ))) ≤ 2 := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdreal : (Nat.ceil (δ * (n : ℝ)) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast ceil_distance_le_dimension hδ n
  have hquot :
      2 * (Nat.ceil (δ * (n : ℝ)) : ℝ) / (n : ℝ) ≤ 2 := by
    apply (div_le_iff₀ hnreal).2
    exact mul_le_mul_of_nonneg_left hdreal (by norm_num)
  unfold threshold
  linarith

def spectralGap (δ a b : ℝ) : ℝ :=
  (MetricCodes.hammingGamma a b - (1 - 2 * δ)) / 4

theorem spectralGap_pos {δ a b : ℝ} (h : Feasible δ a b) :
    0 < spectralGap δ a b := by
  unfold spectralGap
  linarith [h.2.2.2]

theorem eventually_topEigenvalue_uniform_gap_ceil {δ a b : ℝ}
    (hδ : 0 ≤ δ) (h : Feasible δ a b) :
    ∀ᶠ n : ℕ in atTop,
      spectralGap δ a b <
        topEigenvalue n (transverseDegree b n)
          (longitudinalDegree a n) -
            threshold n (Nat.ceil (δ * (n : ℝ))) := by
  obtain ⟨hb, hba, ha, hgamma⟩ := h
  have hgap : 0 < spectralGap δ a b :=
    spectralGap_pos ⟨hb, hba, ha, hgamma⟩
  have hstrict :
      1 - 2 * δ + 2 * spectralGap δ a b <
        MetricCodes.hammingGamma a b := by
    unfold spectralGap
    linarith
  have heigen :=
    eventually_topEigenvalue_gt hb hba ha hstrict
  have hthreshold :
      ∀ᶠ n : ℕ in atTop,
        threshold n (Nat.ceil (δ * (n : ℝ))) <
          1 - 2 * δ + spectralGap δ a b :=
    (tendsto_threshold_ceil hδ).eventually
      (gt_mem_nhds (by linarith))
  filter_upwards [heigen, hthreshold] with n he hn
  linarith

def spectralPrefactor (δ a b : ℝ) : ℝ :=
  2 / spectralGap δ a b

theorem spectralPrefactor_pos {δ a b : ℝ} (h : Feasible δ a b) :
    0 < spectralPrefactor δ a b := by
  unfold spectralPrefactor
  exact div_pos (by norm_num) (spectralGap_pos h)

theorem eventually_hamming_prefactor_le {δ a b : ℝ}
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (h : Feasible δ a b) :
    ∀ᶠ n : ℕ in atTop,
      ((1 - threshold n (Nat.ceil (δ * (n : ℝ)))) /
        (topEigenvalue n (transverseDegree b n)
          (longitudinalDegree a n) -
            threshold n (Nat.ceil (δ * (n : ℝ))))) ≤
        spectralPrefactor δ a b := by
  have hgap : 0 < spectralGap δ a b := spectralGap_pos h
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_topEigenvalue_uniform_gap_ceil hδ h]
      with n hn heigen
  unfold spectralPrefactor
  apply div_le_div₀ (by norm_num : (0 : ℝ) ≤ 2)
  · exact threshold_ceil_numerator_le_two hδ' hn
  · exact hgap
  · exact heigen.le

theorem rateSet_nonempty_of_interior {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    (rateSet δ).Nonempty := by
  obtain ⟨a, b, hfeasible, _⟩ :=
    exists_strict_improving_feasible hδ hδ'
  exact ⟨MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b,
    a, b, hfeasible, rfl⟩

theorem exists_positive_feasible_of_zero {δ a : ℝ}
    (h : Feasible δ a 0) :
    ∃ b : ℝ, 0 < b ∧ Feasible δ a b := by
  obtain ⟨_, ha, hahalf, hgamma⟩ := h
  have hcontinuous :
      Continuous (fun b : ℝ => MetricCodes.hammingGamma a b) := by
    unfold MetricCodes.hammingGamma
    fun_prop
  have hnear :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        1 - 2 * δ < MetricCodes.hammingGamma a b := by
    exact nhdsWithin_le_nhds
      ((hcontinuous.continuousAt (x := (0 : ℝ))).tendsto.eventually
        (lt_mem_nhds hgamma))
  have hsmall : ∀ᶠ b : ℝ in 𝓝[>] 0, b < a :=
    nhdsWithin_le_nhds (gt_mem_nhds ha)
  have htotal :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        0 < b ∧ Feasible δ a b := by
    filter_upwards [hnear, hsmall, self_mem_nhdsWithin]
      with b hgamma' hba (hb : 0 < b)
    exact ⟨hb, hb.le, hba, hahalf, hgamma'⟩
  exact htotal.exists

theorem binaryRate_le_of_eventually_windowFibreQuotient
    {δ a b C : ℝ}
    (hb : 0 < b) (hba : b < a)
    (ha : a ≤ (1 : ℝ) / 2) (hC : 0 < C)
    (hbound : ∀ᶠ n : ℕ in atTop,
      (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) ≤
        C * windowFibreQuotient a b n) :
    binaryRate δ ≤ MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b := by
  refine binaryRate_le_of_eventually
    (tendsto_logb_const_mul_windowFibreQuotient hb hba ha hC) ?_
  filter_upwards [hbound, eventually_gt_atTop (0 : ℕ)]
    with n hncode hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcode :
      0 < (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) := by
    exact_mod_cast codeNumber_pos n (Nat.ceil (δ * (n : ℝ)))
  apply (div_le_div_iff_of_pos_right hnreal).2
  exact Real.logb_le_logb_of_le
    (by norm_num : (1 : ℝ) < 2) hcode hncode

theorem binaryRate_le_of_positive_feasible_bound {δ a b : ℝ}
    (h : Feasible δ a b) (hb : 0 < b)
    (hbound : ∀ᶠ n : ℕ in atTop,
      (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) ≤
        spectralPrefactor δ a b * windowFibreQuotient a b n) :
    binaryRate δ ≤ MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b := by
  exact binaryRate_le_of_eventually_windowFibreQuotient
    hb h.2.1 h.2.2.1 (spectralPrefactor_pos h) hbound

theorem binaryRate_le_variationalRate_of_positive_feasible_bounds
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2)
    (hbound : ∀ ⦃a b : ℝ⦄,
      Feasible δ a b → 0 < b →
        ∀ᶠ n : ℕ in atTop,
          (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) ≤
            spectralPrefactor δ a b * windowFibreQuotient a b n) :
    binaryRate δ ≤ variationalRate δ := by
  have hcandidate :
      ∀ ⦃a b : ℝ⦄, Feasible δ a b →
        binaryRate δ ≤ MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b := by
    intro a b hfeasible
    rcases hfeasible.1.eq_or_lt with hzero | hpositive
    · have hbzero : b = 0 := hzero.symm
      subst b
      obtain ⟨c, hc, hfeasible'⟩ :=
        exists_positive_feasible_of_zero hfeasible
      have hrate := binaryRate_le_of_positive_feasible_bound
        hfeasible' hc (hbound hfeasible' hc)
      have hcunit : c ≤ 1 := by
        have hca := hfeasible'.2.1
        have hahalf := hfeasible'.2.2.1
        linarith
      have hentropy : 0 ≤ MetricCodes.binaryEntropy c :=
        MetricCodes.binaryEntropy_nonneg hc.le hcunit
      calc
        binaryRate δ ≤
            MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy c := hrate
        _ ≤ MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy 0 := by
          simpa using sub_le_self (MetricCodes.binaryEntropy a) hentropy
    · exact binaryRate_le_of_positive_feasible_bound
        hfeasible hpositive (hbound hfeasible hpositive)
  unfold variationalRate
  apply le_csInf (rateSet_nonempty_of_interior hδ hδ')
  rintro _ ⟨a, b, hfeasible, rfl⟩
  exact hcandidate hfeasible

theorem finite_bound {n k L d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (hkL : k < L) (hLn : L + k ≤ n)
    (hgap : threshold n d < topEigenvalue n k L) :
    (codeNumber n d : ℝ) ≤
      ((1 - threshold n d) /
        (topEigenvalue n k L - threshold n d)) *
        ((ambientDimension n k L : ℝ) /
          (MetricCodes.hammingFibreDimension n k : ℝ)) := by
  have hk : 2 * k ≤ n := by omega
  obtain ⟨v, hunit, heigen, hpositive⟩ :=
    exists_positive_unit_topEigenvector hn hkL.le hLn
  have heigenraw :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        topEigenvalue n k L • v := by
    simpa [operator, matrix] using heigen
  have hlambda : 0 < topEigenvalue n k L :=
    topEigenvalue_pos hn hkL hLn
  let P : MetricCodes.ProjectionFamily (BinaryWord n)
      (ambientDimension n k L) (MetricCodes.hammingFibreDimension n k) :=
    MetricCodes.Boolean.hammingProjectionFamily hk hkL.le hLn
      v hunit (fun i => (hpositive i).le)
  let q := MetricCodes.Boolean.hammingProjectionGramFeature
    hk hkL.le hLn v hunit hpositive (topEigenvalue n k L)
  apply finite_codeNumber_bound_of_projection_gram
    hn hd P q (hammingFibreDimension_pos hk) hgap
  intro x y
  simpa [P, q, ambientDimension, MetricCodes.Boolean.hammingWindowDimension] using
    (MetricCodes.Boolean.hammingProjectionGramFeature_inner
      hn hk hkL.le hLn v hunit hpositive (topEigenvalue n k L)
      hlambda heigenraw x y)

theorem eventually_codeNumber_le_spectralPrefactor_mul_windowFibreQuotient
    {δ a b : ℝ} (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2)
    (h : Feasible δ a b) :
    ∀ᶠ n : ℕ in atTop,
      (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) ≤
        spectralPrefactor δ a b * windowFibreQuotient a b n := by
  have hδone : δ ≤ 1 := by linarith
  filter_upwards [
    eventually_gt_atTop (0 : ℕ),
    eventually_transverse_add_le_longitudinal h.1 h.2.1 1,
    eventually_topEigenvalue_uniform_gap_ceil hδ.le h,
    eventually_hamming_prefactor_le hδ.le hδone h]
    with n hn hfit hmargin hprefactor
  have hkL : transverseDegree b n < longitudinalDegree a n := by
    omega
  have hhalf := longitudinalDegree_le_half h.2.2.1 n
  have hLn :
      longitudinalDegree a n + transverseDegree b n ≤ n := by
    omega
  have hd : 0 < Nat.ceil (δ * (n : ℝ)) :=
    ceil_distance_pos hδ hn
  have hgap :
      threshold n (Nat.ceil (δ * (n : ℝ))) <
        topEigenvalue n (transverseDegree b n)
          (longitudinalDegree a n) := by
    have hpositive := spectralGap_pos h
    linarith
  have hfinite := finite_bound hn hd hkL hLn hgap
  have hquotient : 0 ≤ windowFibreQuotient a b n :=
    (windowFibreQuotient_pos_of_fit h.2.2.1 hkL.le).le
  calc
    (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) ≤
        ((1 - threshold n (Nat.ceil (δ * (n : ℝ)))) /
          (topEigenvalue n (transverseDegree b n)
            (longitudinalDegree a n) -
              threshold n (Nat.ceil (δ * (n : ℝ))))) *
            windowFibreQuotient a b n := by
      simpa [windowFibreQuotient] using hfinite
    _ ≤ spectralPrefactor δ a b * windowFibreQuotient a b n :=
      mul_le_mul_of_nonneg_right hprefactor hquotient

theorem binaryRate_le_variationalRate {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    binaryRate δ ≤ variationalRate δ := by
  apply binaryRate_le_variationalRate_of_positive_feasible_bounds hδ hδ'
  intro a b hfeasible _
  exact eventually_codeNumber_le_spectralPrefactor_mul_windowFibreQuotient
    hδ hδ' hfeasible

theorem binaryRate_lt_classicalRate {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    binaryRate δ < classicalRate δ := by
  exact (binaryRate_le_variationalRate hδ hδ').trans_lt
    (variationalRate_lt_classicalRate hδ hδ')

theorem exists_binaryRate_improvement {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    ∃ ε : ℝ, 0 < ε ∧ binaryRate δ ≤ classicalRate δ - ε := by
  refine ⟨classicalRate δ - variationalRate δ, ?_, ?_⟩
  · exact sub_pos.mpr (variationalRate_lt_classicalRate hδ hδ')
  · have hrate := binaryRate_le_variationalRate hδ hδ'
    linarith

end MetricCodes.Hamming

end

end

section

noncomputable section

open scoped BigOperators InnerProductSpace Matrix

namespace MetricCodes.Johnson

def binaryCodeFamily (n d : ℕ) : Finset (Finset (BinaryWord n)) := by
  classical
  exact (Finset.univ : Finset (BinaryWord n)).powerset.filter
    (fun C => IsBinaryCode d C)

@[simp] theorem mem_binaryCodeFamily {n d : ℕ}
    (C : Finset (BinaryWord n)) :
    C ∈ binaryCodeFamily n d ↔ IsBinaryCode d C := by
  classical
  simp [binaryCodeFamily]

theorem binaryCodeFamily_nonempty (n d : ℕ) :
    (binaryCodeFamily n d).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  simp [binaryCodeFamily, IsBinaryCode]

def binaryCodeNumber (n d : ℕ) : ℕ :=
  (binaryCodeFamily n d).sup (fun C => C.card)

theorem card_le_binaryCodeNumber {n d : ℕ}
    (C : Finset (BinaryWord n)) (hC : IsBinaryCode d C) :
    C.card ≤ binaryCodeNumber n d := by
  exact Finset.le_sup ((mem_binaryCodeFamily C).mpr hC)

theorem exists_binaryCodeNumber (n d : ℕ) :
    ∃ C : Finset (BinaryWord n),
      IsBinaryCode d C ∧ C.card = binaryCodeNumber n d := by
  obtain ⟨C, hC, hmax⟩ :=
    Finset.exists_mem_eq_sup (binaryCodeFamily n d)
      (binaryCodeFamily_nonempty n d) (fun C => C.card)
  exact ⟨C, (mem_binaryCodeFamily C).mp hC, hmax.symm⟩

def shellCodeFamily (n w d : ℕ) : Finset (Finset (BinaryWord n)) := by
  classical
  exact (weightShell n w).powerset.filter (fun C => IsBinaryCode d C)

@[simp] theorem mem_shellCodeFamily {n w d : ℕ}
    (C : Finset (BinaryWord n)) :
    C ∈ shellCodeFamily n w d ↔
      C ⊆ weightShell n w ∧ IsBinaryCode d C := by
  classical
  simp [shellCodeFamily]

theorem shellCodeFamily_nonempty (n w d : ℕ) :
    (shellCodeFamily n w d).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  simp [shellCodeFamily, IsBinaryCode]

def shellCodeNumber (n w d : ℕ) : ℕ :=
  (shellCodeFamily n w d).sup (fun C => C.card)

theorem card_le_shellCodeNumber {n w d : ℕ}
    (C : Finset (BinaryWord n))
    (hweight : C ⊆ weightShell n w) (hC : IsBinaryCode d C) :
    C.card ≤ shellCodeNumber n w d := by
  exact Finset.le_sup ((mem_shellCodeFamily C).mpr ⟨hweight, hC⟩)

theorem exists_shellCodeNumber (n w d : ℕ) :
    ∃ C : Finset (BinaryWord n),
      C ⊆ weightShell n w ∧ IsBinaryCode d C ∧
        C.card = shellCodeNumber n w d := by
  obtain ⟨C, hC, hmax⟩ :=
    Finset.exists_mem_eq_sup (shellCodeFamily n w d)
      (shellCodeFamily_nonempty n w d) (fun C => C.card)
  obtain ⟨hweight, hdistance⟩ := (mem_shellCodeFamily C).mp hC
  exact ⟨C, hweight, hdistance, hmax.symm⟩

theorem bassalygo_elias (n w d : ℕ) :
    binaryCodeNumber n d * n.choose w ≤
      2 ^ n * shellCodeNumber n w d := by
  obtain ⟨C, hC, hcard⟩ := exists_binaryCodeNumber n d
  rw [← hcard]
  exact MetricCodes.bassalygo_elias_bound C hC
    (fun D hweight hD => card_le_shellCodeNumber D hweight hD)

theorem bassalygo_elias_real {n w d : ℕ} (hw : w ≤ n) :
    (binaryCodeNumber n d : ℝ) ≤
      ((2 : ℝ) ^ n / (n.choose w : ℝ)) *
        (shellCodeNumber n w d : ℝ) := by
  have hc : 0 < (n.choose w : ℝ) := by
    exact_mod_cast Nat.choose_pos hw
  calc
    (binaryCodeNumber n d : ℝ) ≤
        ((2 : ℝ) ^ n * (shellCodeNumber n w d : ℝ)) /
          (n.choose w : ℝ) := by
      apply (le_div_iff₀ hc).mpr
      exact_mod_cast bassalygo_elias n w d
    _ = ((2 : ℝ) ^ n / (n.choose w : ℝ)) *
        (shellCodeNumber n w d : ℝ) := by
      ring

theorem binaryCodeNumber_eq_hamming (n d : ℕ) :
    binaryCodeNumber n d = MetricCodes.Hamming.codeNumber n d := by
  apply Nat.le_antisymm
  · obtain ⟨C, hC, hcard⟩ := exists_binaryCodeNumber n d
    rw [← hcard]
    exact MetricCodes.Hamming.card_le_codeNumber C hC
  · obtain ⟨C, hC, hcard⟩ := MetricCodes.Hamming.exists_codeNumber n d
    rw [← hcard]
    exact card_le_binaryCodeNumber C hC

def words {n w : ℕ} (C : Finset (JohnsonSphere n w)) :
    Finset (BinaryWord n) :=
  C.image Subtype.val

def IsCode {n w : ℕ} (d : ℕ)
    (C : Finset (JohnsonSphere n w)) : Prop :=
  IsBinaryCode d (words C)

def asSubtype {n w : ℕ} (C : Finset (BinaryWord n))
    (hweight : C ⊆ weightShell n w) :
    Finset (JohnsonSphere n w) := by
  classical
  exact C.attach.image (fun x =>
    (⟨x.val, (MetricCodes.mem_weightShell x.val).mp
      (hweight x.property)⟩ : JohnsonSphere n w))

theorem card_asSubtype {n w : ℕ}
    (C : Finset (BinaryWord n))
    (hweight : C ⊆ weightShell n w) :
    (asSubtype C hweight).card = C.card := by
  classical
  unfold asSubtype
  rw [Finset.card_image_of_injective, Finset.card_attach]
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun q : JohnsonSphere n w => q.val) hxy

theorem words_asSubtype {n w : ℕ}
    (C : Finset (BinaryWord n))
    (hweight : C ⊆ weightShell n w) :
    words (asSubtype C hweight) = C := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z, _hz, hz⟩ := Finset.mem_image.mp hy
    have hval := congrArg Subtype.val hz
    simpa using hval ▸ z.property
  · intro hx
    let z : {z : BinaryWord n // z ∈ C} := ⟨x, hx⟩
    let y : JohnsonSphere n w :=
      ⟨x, (MetricCodes.mem_weightShell x).mp (hweight hx)⟩
    apply Finset.mem_image.mpr
    refine ⟨y, ?_, rfl⟩
    unfold asSubtype
    apply Finset.mem_image.mpr
    refine ⟨z, by simp, ?_⟩
    exact Subtype.ext rfl

theorem isCode_asSubtype {n w d : ℕ}
    (C : Finset (BinaryWord n))
    (hweight : C ⊆ weightShell n w)
    (hC : IsBinaryCode d C) :
    IsCode d (asSubtype C hweight) := by
  unfold IsCode
  rw [words_asSubtype]
  exact hC

def correlation {n w : ℕ} (x y : JohnsonSphere n w) : ℝ :=
  1 - (n : ℝ) * (MetricCodes.johnsonDist x y : ℝ) /
    ((w : ℝ) * ((n - w : ℕ) : ℝ))

@[simp] theorem correlation_self {n w : ℕ}
    (x : JohnsonSphere n w) :
    correlation x x = 1 := by
  simp [correlation, MetricCodes.johnsonDist]

def threshold (n w d : ℕ) : ℝ :=
  1 - (n : ℝ) * (d : ℝ) /
    (2 * (w : ℝ) * ((n - w : ℕ) : ℝ))

theorem correlation_eq_hamming {n w : ℕ}
    (hw : 0 < w) (hwn : w < n) (x y : JohnsonSphere n w) :
    correlation x y =
      1 - (n : ℝ) *
        (MetricCodes.hammingDist (x : BinaryWord n) (y : BinaryWord n) : ℝ) /
          (2 * (w : ℝ) * ((n - w : ℕ) : ℝ)) := by
  have hw' : (w : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hw
  have hcomp : 0 < n - w := Nat.sub_pos_of_lt hwn
  have hcomp' : ((n - w : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hcomp
  rw [MetricCodes.hammingDist_eq_two_mul_johnsonDist]
  push_cast
  unfold correlation
  field_simp [hw', hcomp']

theorem threshold_lt_one {n w d : ℕ}
    (hw : 0 < w) (hwn : w < n) (hd : 0 < d) :
    threshold n w d < 1 := by
  have hn : 0 < n := by omega
  have hcomp : 0 < n - w := Nat.sub_pos_of_lt hwn
  have hnum : 0 < (n : ℝ) * (d : ℝ) := by positivity
  have hden : 0 < 2 * (w : ℝ) * ((n - w : ℕ) : ℝ) := by
    positivity
  unfold threshold
  have hfrac := div_pos hnum hden
  linarith

theorem correlation_le_threshold {n w d : ℕ}
    (hw : 0 < w) (hwn : w < n)
    {x y : JohnsonSphere n w}
    (hd : d ≤ MetricCodes.hammingDist (x : BinaryWord n) (y : BinaryWord n)) :
    correlation x y ≤ threshold n w d := by
  rw [correlation_eq_hamming hw hwn x y]
  have hcomp : 0 < n - w := Nat.sub_pos_of_lt hwn
  have hden : 0 < 2 * (w : ℝ) * ((n - w : ℕ) : ℝ) := by
    positivity
  have hd' : (d : ℝ) ≤
      (MetricCodes.hammingDist (x : BinaryWord n) (y : BinaryWord n) : ℝ) := by
    exact_mod_cast hd
  have hnum :
      (n : ℝ) * (d : ℝ) ≤
        (n : ℝ) *
          (MetricCodes.hammingDist (x : BinaryWord n) (y : BinaryWord n) : ℝ) :=
    mul_le_mul_of_nonneg_left hd' (Nat.cast_nonneg n)
  have hfrac :=
    (div_le_div_iff_of_pos_right hden).mpr hnum
  unfold threshold
  linarith

theorem correlation_le_threshold_of_code {n w d : ℕ}
    (hw : 0 < w) (hwn : w < n)
    {C : Finset (JohnsonSphere n w)} (hC : IsCode d C)
    {x y : JohnsonSphere n w}
    (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    correlation x y ≤ threshold n w d := by
  apply correlation_le_threshold hw hwn
  apply hC (Finset.mem_image_of_mem Subtype.val hx)
    (Finset.mem_image_of_mem Subtype.val hy)
  intro hval
  exact hxy (Subtype.ext hval)

def coordinateIndicator {n : ℕ} (x : BinaryWord n)
    (i : Fin n) : ℝ :=
  if i ∈ MetricCodes.wordSupport x then 1 else 0

theorem sum_coordinateIndicator {n : ℕ} (x : BinaryWord n) :
    (∑ i : Fin n, coordinateIndicator x i) =
      (MetricCodes.binaryWeight x : ℝ) := by
  simpa [coordinateIndicator, MetricCodes.binaryWeight_eq_card_wordSupport] using
    (MetricCodes.Boolean.sum_mem_indicator (MetricCodes.wordSupport x) (1 : ℝ))

theorem sum_coordinateIndicator_mul {n : ℕ}
    (x y : BinaryWord n) :
    (∑ i : Fin n, coordinateIndicator x i * coordinateIndicator y i) =
      ((MetricCodes.wordSupport x ∩ MetricCodes.wordSupport y).card : ℝ) := by
  calc
    (∑ i : Fin n, coordinateIndicator x i * coordinateIndicator y i) =
        ∑ i : Fin n,
          if i ∈ MetricCodes.wordSupport x ∩ MetricCodes.wordSupport y
            then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hx : i ∈ MetricCodes.wordSupport x <;>
        by_cases hy : i ∈ MetricCodes.wordSupport y <;>
        simp [coordinateIndicator, hx, hy]
    _ = ((MetricCodes.wordSupport x ∩ MetricCodes.wordSupport y).card : ℝ) := by
      simpa using
        (MetricCodes.Boolean.sum_mem_indicator
          (MetricCodes.wordSupport x ∩ MetricCodes.wordSupport y) (1 : ℝ))

theorem centered_coordinate_inner_sum {n w : ℕ}
    (hn : 0 < n) (x y : JohnsonSphere n w) :
    (∑ i : Fin n,
      (coordinateIndicator (x : BinaryWord n) i -
        (w : ℝ) / (n : ℝ)) *
      (coordinateIndicator (y : BinaryWord n) i -
        (w : ℝ) / (n : ℝ))) =
      ((MetricCodes.wordSupport (x : BinaryWord n) ∩
        MetricCodes.wordSupport (y : BinaryWord n)).card : ℝ) -
        (w : ℝ) ^ 2 / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  calc
    (∑ i : Fin n,
      (coordinateIndicator (x : BinaryWord n) i -
        (w : ℝ) / (n : ℝ)) *
      (coordinateIndicator (y : BinaryWord n) i -
        (w : ℝ) / (n : ℝ))) =
        ∑ i : Fin n,
          (coordinateIndicator (x : BinaryWord n) i *
            coordinateIndicator (y : BinaryWord n) i -
            ((w : ℝ) / (n : ℝ)) *
              coordinateIndicator (x : BinaryWord n) i -
            ((w : ℝ) / (n : ℝ)) *
              coordinateIndicator (y : BinaryWord n) i +
            ((w : ℝ) / (n : ℝ)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ((MetricCodes.wordSupport (x : BinaryWord n) ∩
          MetricCodes.wordSupport (y : BinaryWord n)).card : ℝ) -
        ((w : ℝ) / (n : ℝ)) * (w : ℝ) -
        ((w : ℝ) / (n : ℝ)) * (w : ℝ) +
        (n : ℝ) * ((w : ℝ) / (n : ℝ)) ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [sum_coordinateIndicator_mul,
        sum_coordinateIndicator, sum_coordinateIndicator,
        x.property, y.property]
    _ = ((MetricCodes.wordSupport (x : BinaryWord n) ∩
          MetricCodes.wordSupport (y : BinaryWord n)).card : ℝ) -
        (w : ℝ) ^ 2 / (n : ℝ) := by
      field_simp [hn']
      ; ring

def geometricAxis {n w : ℕ} (x : JohnsonSphere n w) : MetricCodes.Ambient n :=
  WithLp.toLp 2 (fun i : Fin n =>
    Real.sqrt ((n : ℝ) /
      ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (coordinateIndicator (x : BinaryWord n) i -
          (w : ℝ) / (n : ℝ)))

theorem geometricAxis_inner {n w : ℕ}
    (hw : 0 < w) (hwn : w < n)
    (x y : JohnsonSphere n w) :
    ⟪geometricAxis x, geometricAxis y⟫_ℝ = correlation x y := by
  have hn : 0 < n := by omega
  have hcomp : 0 < n - w := Nat.sub_pos_of_lt hwn
  have hn' : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  have hw' : (w : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hw
  have hcomp' : ((n - w : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hcomp
  have hscale :
      0 ≤ (n : ℝ) / ((w : ℝ) * ((n - w : ℕ) : ℝ)) := by
    positivity
  have hxcard : (MetricCodes.wordSupport (x : BinaryWord n)).card = w := by
    simpa [MetricCodes.binaryWeight_eq_card_wordSupport] using x.property
  have hinter :
      (MetricCodes.wordSupport (x : BinaryWord n) ∩
        MetricCodes.wordSupport (y : BinaryWord n)).card ≤ w := by
    calc
      (MetricCodes.wordSupport (x : BinaryWord n) ∩
        MetricCodes.wordSupport (y : BinaryWord n)).card ≤
          (MetricCodes.wordSupport (x : BinaryWord n)).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = w := hxcard
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  change
    (∑ i : Fin n,
      (Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (coordinateIndicator (x : BinaryWord n) i -
          (w : ℝ) / (n : ℝ))) *
      (Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (coordinateIndicator (y : BinaryWord n) i -
          (w : ℝ) / (n : ℝ)))) = correlation x y
  calc
    (∑ i : Fin n,
      (Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (coordinateIndicator (x : BinaryWord n) i -
          (w : ℝ) / (n : ℝ))) *
      (Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (coordinateIndicator (y : BinaryWord n) i -
          (w : ℝ) / (n : ℝ)))) =
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) ^ 2 *
        (∑ i : Fin n,
          (coordinateIndicator (x : BinaryWord n) i -
            (w : ℝ) / (n : ℝ)) *
          (coordinateIndicator (y : BinaryWord n) i -
            (w : ℝ) / (n : ℝ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (((MetricCodes.wordSupport (x : BinaryWord n) ∩
            MetricCodes.wordSupport (y : BinaryWord n)).card : ℝ) -
          (w : ℝ) ^ 2 / (n : ℝ)) := by
      rw [Real.sq_sqrt hscale, centered_coordinate_inner_sum hn x y]
    _ = correlation x y := by
      unfold correlation
      rw [MetricCodes.johnsonDist_eq_weight_sub_inter,
        Nat.cast_sub hinter]
      field_simp [hn', hw', hcomp']
      rw [Nat.cast_sub (Nat.le_of_lt hwn)]
      ring

abbrev SupportCoordinates {n w : ℕ} (x : JohnsonSphere n w) :=
  {i : Fin n // i ∈ MetricCodes.wordSupport (x : BinaryWord n)}

abbrev ComplementCoordinates {n w : ℕ} (x : JohnsonSphere n w) :=
  {i : Fin n // i ∈
    (Finset.univ : Finset (Fin n)) \
      MetricCodes.wordSupport (x : BinaryWord n)}

def supportCoordinateEquiv {n w : ℕ} (x : JohnsonSphere n w) :
    SupportCoordinates x ≃ Fin w :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_coe, Fintype.card_fin]
    simpa only [MetricCodes.binaryWeight_eq_card_wordSupport] using x.property)

def complementCoordinateEquiv {n w : ℕ} (x : JohnsonSphere n w) :
    ComplementCoordinates x ≃ Fin (n - w) :=
  Fintype.equivOfCardEq (by
    have hx : (MetricCodes.wordSupport (x : BinaryWord n)).card = w := by
      simpa only [MetricCodes.binaryWeight_eq_card_wordSupport] using x.property
    rw [Fintype.card_coe, Fintype.card_fin,
      Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [hx])

abbrev HarmonicFibreIndex (n w p q : ℕ) :=
  Fin (MetricCodes.hammingFibreDimension w p) ×
    Fin (MetricCodes.hammingFibreDimension (n - w) q)

def harmonicFibreIndexEquiv (n w p q : ℕ) :
    HarmonicFibreIndex n w p q ≃
      Fin (MetricCodes.johnsonFibreDimension n w p q) :=
  Fintype.equivOfCardEq (by
    change
      Fintype.card
          (Fin (MetricCodes.booleanHarmonicDimension w p) ×
            Fin (MetricCodes.booleanHarmonicDimension (n - w) q)) =
        Fintype.card
          (Fin (MetricCodes.booleanHarmonicDimension w p *
            MetricCodes.booleanHarmonicDimension (n - w) q))
    rw [Fintype.card_prod]
    simp only [Fintype.card_fin])

abbrev ShellWindowIndex (n p q L : ℕ) :=
  Σ i : Fin (L - (p + q) + 1),
    Fin (MetricCodes.booleanHarmonicDimension n (p + q + i.val))

theorem shellWindowIndex_card (n p q L : ℕ)
    (hfirst : p + q ≤ L) :
    Fintype.card (ShellWindowIndex n p q L) =
      MetricCodes.johnsonAmbientDimension n (p + q) L := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  unfold MetricCodes.johnsonAmbientDimension
  refine Finset.sum_bij (fun i _ => p + q + i.val) ?_ ?_ ?_ ?_
  · intro i _
    apply Finset.mem_Icc.mpr
    constructor
    · omega
    · have hi := i.isLt
      omega
  · intro i _ j _ heq
    apply Fin.ext
    omega
  · intro j hj
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hj
    refine ⟨⟨j - (p + q), by omega⟩,
      Finset.mem_univ _, ?_⟩
    change p + q + (j - (p + q)) = j
    exact Nat.add_sub_of_le hlo
  · intro i _
    rfl

def shellWindowIndexEquiv (n p q L : ℕ)
    (hfirst : p + q ≤ L) :
    ShellWindowIndex n p q L ≃
      Fin (MetricCodes.johnsonAmbientDimension n (p + q) L) :=
  Fintype.equivOfCardEq (by
    simpa only [Fintype.card_fin] using
      shellWindowIndex_card n p q L hfirst)

abbrev Index (p q L : ℕ) := Fin (L - (p + q) + 1)

abbrev Space (p q L : ℕ) := EuclideanSpace ℝ (Index p q L)

def matrix (n w p q L : ℕ) :
    Matrix (Index p q L) (Index p q L) ℝ :=
  MetricCodes.johnsonJacobiMatrix n w p q L

theorem matrix_hermitian (n w p q L : ℕ) :
    (matrix n w p q L).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have h := congrArg
    (fun A : Matrix (Index p q L) (Index p q L) ℝ => A i j)
    (MetricCodes.johnsonJacobiMatrix_symmetric n w p q L)
  simpa [matrix] using h

def operator (n w p q L : ℕ) : Space p q L →ₗ[ℝ] Space p q L :=
  Matrix.toEuclideanLin (matrix n w p q L)

theorem operator_isSymmetric (n w p q L : ℕ) :
    (operator n w p q L).IsSymmetric := by
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (matrix_hermitian n w p q L)

def continuousOperator (n w p q L : ℕ) :
    Space p q L →L[ℝ] Space p q L :=
  LinearMap.toContinuousLinearMap (operator n w p q L)

def rayleigh (n w p q L : ℕ) (x : Space p q L) : ℝ :=
  (continuousOperator n w p q L).rayleighQuotient x

theorem rayleigh_bddAbove (n w p q L : ℕ) :
    BddAbove (Set.range
      (fun x : {x : Space p q L // x ≠ 0} =>
        rayleigh n w p q L x)) := by
  refine ⟨‖continuousOperator n w p q L‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (le_abs_self _).trans
    ((continuousOperator n w p q L).rayleighQuotient_le_norm x)

def topEigenvalue (n w p q L : ℕ) : ℝ :=
  ⨆ x : {x : Space p q L // x ≠ 0}, rayleigh n w p q L x

theorem rayleigh_le_top (n w p q L : ℕ)
    (x : Space p q L) (hx : x ≠ 0) :
    rayleigh n w p q L x ≤ topEigenvalue n w p q L := by
  exact le_ciSup (rayleigh_bddAbove n w p q L) ⟨x, hx⟩

theorem topEigenvalue_hasEigenvalue (n w p q L : ℕ) :
    Module.End.HasEigenvalue (operator n w p q L)
      (topEigenvalue n w p q L) := by
  have h :=
    (operator_isSymmetric n w p q L).hasEigenvalue_iSup_of_finiteDimensional
  simpa [topEigenvalue, rayleigh, continuousOperator,
    ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply] using h

theorem exists_topEigenvector (n w p q L : ℕ) :
    ∃ x : Space p q L, x ≠ 0 ∧
      operator n w p q L x = topEigenvalue n w p q L • x := by
  obtain ⟨x, hx⟩ :=
    (topEigenvalue_hasEigenvalue n w p q L).exists_hasEigenvector
  exact ⟨x, hx.2, hx.apply_eq_smul⟩

theorem rayleigh_eq_inner (n w p q L : ℕ) (x : Space p q L) :
    rayleigh n w p q L x =
      @inner ℝ (Space p q L) _ (operator n w p q L x) x / ‖x‖ ^ 2 := by
  rfl

structure AdmissibleDegrees (n w p q L : ℕ) : Prop where
  weight_pos : 0 < w
  weight_lt : w < n
  weight_half : 2 * w ≤ n
  support_half : 2 * p ≤ w
  complement_half : 2 * q ≤ n - w
  first_le : p + q ≤ L
  last_le : L ≤ MetricCodes.johnsonLastDegree n w p q

theorem AdmissibleDegrees.terminal_le_weight
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L) :
    L ≤ w := by
  exact h.last_le.trans (by
    unfold MetricCodes.johnsonLastDegree
    exact min_le_left _ _)

theorem AdmissibleDegrees.terminal_le_half
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L) :
    L ≤ n / 2 := by
  have hL := h.terminal_le_weight
  have hw := h.weight_half
  omega

theorem booleanHarmonicDimension_pos {n k : ℕ}
    (hk : 2 * k ≤ n) :
    0 < MetricCodes.booleanHarmonicDimension n k := by
  cases k with
  | zero => simp [MetricCodes.booleanHarmonicDimension]
  | succ j =>
      change 0 < n.choose (j + 1) - n.choose j
      apply Nat.sub_pos_of_lt
      have hchoose : 0 < n.choose j := Nat.choose_pos (by omega)
      have hfactor : j + 1 < n - j := by omega
      have hmul :
          n.choose j * (j + 1) < n.choose j * (n - j) :=
        Nat.mul_lt_mul_of_pos_left hfactor hchoose
      have hmul' :
          n.choose j * (j + 1) < n.choose (j + 1) * (j + 1) := by
        calc
          n.choose j * (j + 1) < n.choose j * (n - j) := hmul
          _ = n.choose (j + 1) * (j + 1) :=
            (Nat.choose_succ_right_eq n j).symm
      exact (Nat.mul_lt_mul_right (by omega : 0 < j + 1)).mp hmul'

theorem AdmissibleDegrees.fibreDimension_pos
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L) :
    0 < MetricCodes.johnsonFibreDimension n w p q := by
  unfold MetricCodes.johnsonFibreDimension
  exact Nat.mul_pos
    (booleanHarmonicDimension_pos h.support_half)
    (booleanHarmonicDimension_pos h.complement_half)

theorem ambientDimension_eq {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L) :
    MetricCodes.johnsonAmbientDimension n (p + q) L =
      n.choose L - MetricCodes.precedingBinomial n (p + q) := by
  exact MetricCodes.johnsonAmbientDimension_eq_of_fibre n p q L
    h.first_le h.terminal_le_half

theorem zonalDiagonal_eq {n w j : ℕ}
    (hw : 0 < w) (hhalf : 2 * w < n) (hj : j ≤ w) :
    MetricCodes.johnsonZonalDiagonal n w j =
      MetricCodes.johnsonM n w ^ 2 * (j : ℝ) *
        ((n : ℝ) - (j : ℝ) + 1) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ) *
          MetricCodes.johnsonJ n j * (MetricCodes.johnsonJ n j + 1)) := by
  have hwn : w < n := by omega
  have hhalf' : (2 : ℝ) * (w : ℝ) < (n : ℝ) := by
    exact_mod_cast hhalf
  have hj' : (j : ℝ) ≤ (w : ℝ) := by
    exact_mod_cast hj
  have hsmall : (2 : ℝ) * (j : ℝ) < (n : ℝ) := by
    nlinarith
  have hw' : (w : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hw
  have hN' : (n : ℝ) - (w : ℝ) ≠ 0 := by
    have hwn' : (w : ℝ) < (n : ℝ) := by exact_mod_cast hwn
    linarith
  have hJ : 0 < MetricCodes.johnsonJ n j := by
    unfold MetricCodes.johnsonJ
    nlinarith
  have hJone : MetricCodes.johnsonJ n j + 1 ≠ 0 := by
    linarith
  have hD :
      (n : ℝ) * 2 - (n : ℝ) * (j : ℝ) * 4 +
          (n : ℝ) ^ 2 - (j : ℝ) * 4 + (j : ℝ) ^ 2 * 4 ≠ 0 := by
    have hfactor :
        (n : ℝ) * 2 - (n : ℝ) * (j : ℝ) * 4 +
            (n : ℝ) ^ 2 - (j : ℝ) * 4 + (j : ℝ) ^ 2 * 4 =
          ((n : ℝ) - 2 * (j : ℝ)) *
            ((n : ℝ) - 2 * (j : ℝ) + 2) := by
      ring
    rw [hfactor]
    exact (mul_pos (by linarith) (by linarith)).ne'
  unfold MetricCodes.johnsonZonalDiagonal MetricCodes.johnsonDiagonal
    MetricCodes.johnsonMu MetricCodes.johnsonM
    MetricCodes.johnsonJ1 MetricCodes.johnsonJ2
  rw [Nat.cast_sub (Nat.le_of_lt hwn)]
  field_simp [hw', hN', hJ.ne', hJone]
  unfold MetricCodes.johnsonJ
  ring

theorem zonalDiagonal_pos {n w j : ℕ}
    (hw : 0 < w) (hhalf : 2 * w < n)
    (hj : 0 < j) (hjw : j ≤ w) :
    0 < MetricCodes.johnsonZonalDiagonal n w j := by
  rw [zonalDiagonal_eq hw hhalf hjw]
  have hwn : w < n := by omega
  have hhalf' : (2 : ℝ) * (w : ℝ) < (n : ℝ) := by
    exact_mod_cast hhalf
  have hjw' : (j : ℝ) ≤ (w : ℝ) := by
    exact_mod_cast hjw
  have hM : 0 < MetricCodes.johnsonM n w := by
    unfold MetricCodes.johnsonM
    nlinarith
  have hJ : 0 < MetricCodes.johnsonJ n j := by
    unfold MetricCodes.johnsonJ
    nlinarith
  have hN : 0 < n - w := Nat.sub_pos_of_lt hwn
  have hlast : 0 < (n : ℝ) - (j : ℝ) + 1 := by
    nlinarith
  positivity

theorem associatedEdge_pos {n w p q j : ℕ}
    (hw : 0 < w) (hhalf : 2 * w < n)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (hfirst : p + q ≤ j)
    (hlast : j < MetricCodes.johnsonLastDegree n w p q) :
    0 < MetricCodes.johnsonEdge n w p q j := by
  have hwn : w < n := by omega
  have hN : 0 < n - w := Nat.sub_pos_of_lt hwn
  have hjw : j < w := by
    exact lt_of_lt_of_le hlast (by
      unfold MetricCodes.johnsonLastDegree
      exact min_le_left _ _)
  have hjleft : j < w - p + q := by
    apply lt_of_lt_of_le hlast
    unfold MetricCodes.johnsonLastDegree
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hjright : j < n - w + p - q := by
    apply lt_of_lt_of_le hlast
    unfold MetricCodes.johnsonLastDegree
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hhalf' : (2 : ℝ) * (w : ℝ) < (n : ℝ) := by
    exact_mod_cast hhalf
  have hjw' : (j : ℝ) < (w : ℝ) := by
    exact_mod_cast hjw
  have hfirst' : (p : ℝ) + (q : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast hfirst
  have hjleft' :
      (j : ℝ) < (w : ℝ) - (p : ℝ) + (q : ℝ) := by
    have hcast : (j : ℝ) < ((w - p + q : ℕ) : ℝ) := by
      exact_mod_cast hjleft
    simpa only [Nat.cast_add, Nat.cast_sub (by omega : p ≤ w)]
      using hcast
  have hjright' :
      (j : ℝ) < (n : ℝ) - (w : ℝ) + (p : ℝ) - (q : ℝ) := by
    have hcast : (j : ℝ) < ((n - w + p - q : ℕ) : ℝ) := by
      exact_mod_cast hjright
    simpa only [Nat.cast_sub (by omega : q ≤ n - w + p),
      Nat.cast_add, Nat.cast_sub (by omega : w ≤ n)] using hcast
  have hJ : 0 < MetricCodes.johnsonJ n j := by
    unfold MetricCodes.johnsonJ
    nlinarith
  have hM : 0 < MetricCodes.johnsonM n w := by
    unfold MetricCodes.johnsonM
    nlinarith
  have hJminusM : 0 < MetricCodes.johnsonJ n j - MetricCodes.johnsonM n w := by
    unfold MetricCodes.johnsonJ MetricCodes.johnsonM
    linarith
  have hJplusM : 0 < MetricCodes.johnsonJ n j + MetricCodes.johnsonM n w := by
    linarith
  have hJminusDelta :
      0 < MetricCodes.johnsonJ n j - MetricCodes.johnsonDelta n w p q := by
    unfold MetricCodes.johnsonJ MetricCodes.johnsonDelta
      MetricCodes.johnsonJ2 MetricCodes.johnsonJ1
    rw [Nat.cast_sub (by omega : w ≤ n)]
    linarith
  have hJplusDelta :
      0 < MetricCodes.johnsonJ n j + MetricCodes.johnsonDelta n w p q := by
    unfold MetricCodes.johnsonJ MetricCodes.johnsonDelta
      MetricCodes.johnsonJ2 MetricCodes.johnsonJ1
    rw [Nat.cast_sub (by omega : w ≤ n)]
    linarith
  have hSigmaMinus :
      0 < MetricCodes.johnsonSigma n w p q + 1 -
        MetricCodes.johnsonJ n j := by
    unfold MetricCodes.johnsonSigma MetricCodes.johnsonJ1 MetricCodes.johnsonJ2
      MetricCodes.johnsonJ
    rw [Nat.cast_sub (by omega : w ≤ n)]
    linarith
  have hSigmaPlus :
      0 < MetricCodes.johnsonSigma n w p q + 1 +
        MetricCodes.johnsonJ n j := by
    linarith
  have hJM :
      0 < MetricCodes.johnsonJ n j ^ 2 - MetricCodes.johnsonM n w ^ 2 := by
    nlinarith [mul_pos hJminusM hJplusM]
  have hJDelta :
      0 < MetricCodes.johnsonJ n j ^ 2 -
        MetricCodes.johnsonDelta n w p q ^ 2 := by
    nlinarith [mul_pos hJminusDelta hJplusDelta]
  have hSigma :
      0 < (MetricCodes.johnsonSigma n w p q + 1) ^ 2 -
        MetricCodes.johnsonJ n j ^ 2 := by
    nlinarith [mul_pos hSigmaMinus hSigmaPlus]
  have hjstep : (j : ℝ) + 1 ≤ (w : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hjw
  have hhalfstep :
      (2 : ℝ) * (w : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast (show 2 * w + 1 ≤ n by omega)
  have hdenleft : 0 < 2 * MetricCodes.johnsonJ n j - 1 := by
    unfold MetricCodes.johnsonJ
    nlinarith
  have hdenright : 0 < 2 * MetricCodes.johnsonJ n j + 1 := by
    linarith
  have hnu : 0 < MetricCodes.johnsonNu n w p q j := by
    unfold MetricCodes.johnsonNu
    apply div_pos
    · exact Real.sqrt_pos.mpr
        (mul_pos (mul_pos hJM hJDelta) hSigma)
    · exact mul_pos (mul_pos (by norm_num) hJ)
        (Real.sqrt_pos.mpr (mul_pos hdenleft hdenright))
  unfold MetricCodes.johnsonEdge
  exact div_pos
    (mul_pos (by exact_mod_cast (show 0 < n by omega)) hnu)
    (mul_pos (by exact_mod_cast hw)
      (by exact_mod_cast hN))

theorem zonalEdge_pos {n w j : ℕ}
    (hw : 0 < w) (hhalf : 2 * w < n) (hj : j < w) :
    0 < MetricCodes.johnsonZonalEdge n w j := by
  have hlast : MetricCodes.johnsonLastDegree n w 0 0 = w := by
    simp [MetricCodes.johnsonLastDegree,
      min_eq_left (by omega : w ≤ n - w)]
  unfold MetricCodes.johnsonZonalEdge
  apply associatedEdge_pos hw hhalf (by omega) (by omega)
    (Nat.zero_le j)
  simpa [hlast] using hj

theorem hattedDiagonal_nonneg {n w p q j : ℕ}
    (hw : 0 < w) (hhalf : 2 * w < n) (hj : j ≤ w) :
    0 ≤ MetricCodes.johnsonHattedDiagonal n w p q j := by
  by_cases hz : j = 0
  · subst j
    simp [MetricCodes.johnsonHattedDiagonal]
  · exact MetricCodes.johnsonHattedDiagonal_nonneg
      (zonalDiagonal_pos hw hhalf (Nat.pos_of_ne_zero hz) hj)

theorem hattedEdge_pos {n w p q j : ℕ}
    (hw : 0 < w) (hhalf : 2 * w < n)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (hfirst : p + q ≤ j)
    (hlast : j < MetricCodes.johnsonLastDegree n w p q) :
    0 < MetricCodes.johnsonHattedEdge n w p q j := by
  have hedge := associatedEdge_pos hw hhalf hp hq hfirst hlast
  have hjw : j < w :=
    lt_of_lt_of_le hlast (by
      unfold MetricCodes.johnsonLastDegree
      exact min_le_left _ _)
  unfold MetricCodes.johnsonHattedEdge
  exact div_pos (sq_pos_of_pos hedge)
    (zonalEdge_pos hw hhalf hjw)

theorem matrix_entry_nonneg {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (i j : Index p q L) :
    0 ≤ matrix n w p q L i j := by
  have hfirst := h.first_le
  have hiL : p + q + i.val ≤ L := by
    have hi := i.isLt
    omega
  have hjL : p + q + j.val ≤ L := by
    have hj := j.isLt
    omega
  unfold matrix MetricCodes.johnsonJacobiMatrix
  split_ifs with hdiag hforward hbackward
  · exact hattedDiagonal_nonneg h.weight_pos hstrict
      (hiL.trans h.terminal_le_weight)
  · apply (hattedEdge_pos h.weight_pos hstrict
      h.support_half h.complement_half (by omega) ?_).le
    apply lt_of_lt_of_le (by omega : p + q + i.val < L)
    exact h.last_le
  · apply (hattedEdge_pos h.weight_pos hstrict
      h.support_half h.complement_half (by omega) ?_).le
    apply lt_of_lt_of_le (by omega : p + q + j.val < L)
    exact h.last_le
  · exact le_rfl

def coordinateAbs (p q L : ℕ)
    (x : Space p q L) : Space p q L :=
  WithLp.toLp 2 (fun i : Index p q L => |x i|)

theorem coordinateAbs_norm (p q L : ℕ)
    (x : Space p q L) :
    ‖coordinateAbs p q L x‖ = ‖x‖ := by
  have hsquare : ‖coordinateAbs p q L x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    simp [coordinateAbs]
  nlinarith [norm_nonneg (coordinateAbs p q L x), norm_nonneg x]

theorem coordinateAbs_ne_zero (p q L : ℕ)
    {x : Space p q L} (hx : x ≠ 0) :
    coordinateAbs p q L x ≠ 0 := by
  intro habs
  have hnorm := coordinateAbs_norm p q L x
  rw [habs, norm_zero] at hnorm
  exact hx (norm_eq_zero.mp hnorm.symm)

theorem inner_le_inner_coordinateAbs {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (x : Space p q L) :
    @inner ℝ (Space p q L) _ (operator n w p q L x) x ≤
      @inner ℝ (Space p q L) _
        (operator n w p q L (coordinateAbs p q L x))
        (coordinateAbs p q L x) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [Real.inner_apply]
  change
    (∑ i : Index p q L,
      (∑ j : Index p q L, matrix n w p q L i j * x j) * x i) ≤
    (∑ i : Index p q L,
      (∑ j : Index p q L,
        matrix n w p q L i j * |x j|) * |x i|)
  simp_rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hentry := matrix_entry_nonneg h hstrict i j
  have hproduct : x j * x i ≤ |x j| * |x i| := by
    calc
      x j * x i ≤ |x j * x i| := le_abs_self _
      _ = |x j| * |x i| := abs_mul _ _
  calc
    matrix n w p q L i j * x j * x i =
        matrix n w p q L i j * (x j * x i) := by ring
    _ ≤ matrix n w p q L i j * (|x j| * |x i|) :=
      mul_le_mul_of_nonneg_left hproduct hentry
    _ = matrix n w p q L i j * |x j| * |x i| := by ring

theorem rayleigh_le_coordinateAbs {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (x : Space p q L) :
    rayleigh n w p q L x ≤
      rayleigh n w p q L (coordinateAbs p q L x) := by
  rw [rayleigh_eq_inner, rayleigh_eq_inner, coordinateAbs_norm]
  gcongr
  exact inner_le_inner_coordinateAbs h hstrict x

theorem rayleigh_eq_of_eigenvector
    (n w p q L : ℕ) (x : Space p q L) (hx : x ≠ 0)
    (eigenvalue : ℝ)
    (heigen : operator n w p q L x = eigenvalue • x) :
    rayleigh n w p q L x = eigenvalue := by
  rw [rayleigh_eq_inner, heigen,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hnorm : ‖x‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  field_simp [hnorm]

theorem coordinateAbs_top_rayleigh {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (x : Space p q L) (hx : x ≠ 0)
    (heigen :
      operator n w p q L x = topEigenvalue n w p q L • x) :
    rayleigh n w p q L (coordinateAbs p q L x) =
      topEigenvalue n w p q L := by
  have hbelow := rayleigh_le_coordinateAbs h hstrict x
  have habove := rayleigh_le_top n w p q L
    (coordinateAbs p q L x) (coordinateAbs_ne_zero p q L hx)
  rw [rayleigh_eq_of_eigenvector n w p q L x hx
    (topEigenvalue n w p q L) heigen] at hbelow
  exact le_antisymm habove hbelow

theorem exists_nonnegative_topEigenvector {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n) :
    ∃ x : Space p q L,
      x ≠ 0 ∧
        operator n w p q L x = topEigenvalue n w p q L • x ∧
        ∀ i : Index p q L, 0 ≤ x i := by
  obtain ⟨x, hx, heigen⟩ := exists_topEigenvector n w p q L
  let y : Space p q L := coordinateAbs p q L x
  have hy : y ≠ 0 := coordinateAbs_ne_zero p q L hx
  have hyray : rayleigh n w p q L y = topEigenvalue n w p q L :=
    coordinateAbs_top_rayleigh h hstrict x hx heigen
  have hself : IsSelfAdjoint (continuousOperator n w p q L) :=
    (operator_isSymmetric n w p q L).isSelfAdjoint
  have hmax :
      IsMaxOn (continuousOperator n w p q L).reApplyInnerSelf
        (Metric.sphere (0 : Space p q L) ‖y‖) y := by
    intro z hz
    have hnorm : ‖z‖ = ‖y‖ := by simpa using hz
    have hznonzero : z ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hnorm
      exact hy (norm_eq_zero.mp hnorm.symm)
    have hray := rayleigh_le_top n w p q L z hznonzero
    rw [← hyray] at hray
    change
      (continuousOperator n w p q L).reApplyInnerSelf z / ‖z‖ ^ 2 ≤
        (continuousOperator n w p q L).reApplyInnerSelf y / ‖y‖ ^ 2
      at hray
    rw [hnorm] at hray
    have hnormpos : 0 < ‖y‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hy)
    exact (div_le_div_iff_of_pos_right hnormpos).mp hray
  have heigeny := hself.hasEigenvector_of_isMaxOn hy hmax
  refine ⟨y, hy, ?_, fun i => abs_nonneg (x i)⟩
  have happly := heigeny.apply_eq_smul
  simpa [topEigenvalue, rayleigh, continuousOperator] using happly

theorem exists_nonnegative_unit_topEigenvector
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n) :
    ∃ x : Space p q L,
      ‖x‖ = 1 ∧
        operator n w p q L x = topEigenvalue n w p q L • x ∧
        ∀ i : Index p q L, 0 ≤ x i := by
  obtain ⟨x, hx, heigen, hnonneg⟩ :=
    exists_nonnegative_topEigenvector h hstrict
  have hnormpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  refine ⟨‖x‖⁻¹ • x, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hnormpos)]
    exact inv_mul_cancel₀ (ne_of_gt hnormpos)
  · rw [map_smul, heigen]
    exact smul_comm _ _ _
  · intro i
    change 0 ≤ ‖x‖⁻¹ * x i
    exact mul_nonneg (inv_nonneg.mpr hnormpos.le) (hnonneg i)

theorem matrix_adjacent_pos {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (i j : Index p q L)
    (hadjacent : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    0 < matrix n w p q L i j := by
  have hi := i.isLt
  have hj := j.isLt
  rcases hadjacent with hforward | hbackward
  · have hnot : j.val + 1 ≠ i.val := by omega
    have hne : i ≠ j := by
      intro heq
      subst j
      omega
    have hlast : p + q + i.val <
        MetricCodes.johnsonLastDegree n w p q := by
      have hlt : p + q + i.val < L := by omega
      exact hlt.trans_le h.last_le
    simpa [matrix, MetricCodes.johnsonJacobiMatrix,
      hne, hforward, hnot] using
      hattedEdge_pos h.weight_pos hstrict h.support_half
        h.complement_half (show p + q ≤ p + q + i.val by omega)
        hlast
  · have hnot : i.val + 1 ≠ j.val := by omega
    have hne : i ≠ j := by
      intro heq
      subst j
      omega
    have hlast : p + q + j.val <
        MetricCodes.johnsonLastDegree n w p q := by
      have hlt : p + q + j.val < L := by omega
      exact hlt.trans_le h.last_le
    simpa [matrix, MetricCodes.johnsonJacobiMatrix,
      hne, hnot, hbackward] using
      hattedEdge_pos h.weight_pos hstrict h.support_half
        h.complement_half (show p + q ≤ p + q + j.val by omega)
        hlast

theorem nonnegative_eigenvector_zero_propagates
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L) (eigenvalue : ℝ)
    (heigen : operator n w p q L v = eigenvalue • v)
    (hnonnegative : ∀ i : Index p q L, 0 ≤ v i)
    (i j : Index p q L)
    (hzero : v i = 0)
    (hadjacent : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    v j = 0 := by
  classical
  have hcoordinate :=
    congrArg (fun z : Space p q L => z i) heigen
  change
    (∑ r : Index p q L, matrix n w p q L i r * v r) =
      eigenvalue * v i at hcoordinate
  rw [hzero, mul_zero] at hcoordinate
  have hterms :
      ∀ r ∈ (Finset.univ : Finset (Index p q L)),
        0 ≤ matrix n w p q L i r * v r := by
    intro r _
    exact mul_nonneg
      (matrix_entry_nonneg h hstrict i r)
      (hnonnegative r)
  have hterm : matrix n w p q L i j * v j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hcoordinate
      j (Finset.mem_univ j)
  exact (mul_eq_zero.mp hterm).resolve_left
    (matrix_adjacent_pos h hstrict i j hadjacent).ne'

theorem nonnegative_eigenvector_coordinate_pos
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L) (eigenvalue : ℝ)
    (heigen : operator n w p q L v = eigenvalue • v)
    (hnonnegative : ∀ i : Index p q L, 0 ≤ v i)
    (hnonzero : v ≠ 0)
    (i : Index p q L) :
    0 < v i := by
  rcases (hnonnegative i).eq_or_lt with hzero | hpositive
  · exfalso
    apply hnonzero
    apply PiLp.ext
    intro j
    change v j = 0
    have hchain :
        ∀ distance : ℕ,
          ∀ j : Index p q L,
            Nat.dist i.val j.val = distance → v j = 0 := by
      intro distance
      induction distance using Nat.strong_induction_on with
      | h distance ih =>
          intro j hdistance
          by_cases hequal : i.val = j.val
          · have hij : i = j := Fin.ext hequal
            simpa [hij] using hzero.symm
          · by_cases hforward : i.val < j.val
            · let previous : Index p q L :=
                ⟨j.val - 1, by have hj := j.isLt; omega⟩
              have hprevious_distance :
                  Nat.dist i.val previous.val < distance := by
                rw [Nat.dist_eq_sub_of_le
                  (show i.val ≤ previous.val by
                    dsimp [previous]
                    omega)]
                rw [Nat.dist_eq_sub_of_le
                  (Nat.le_of_lt hforward)] at hdistance
                dsimp [previous]
                omega
              have hprevious_zero : v previous = 0 :=
                ih (Nat.dist i.val previous.val)
                  hprevious_distance previous rfl
              exact nonnegative_eigenvector_zero_propagates
                h hstrict v eigenvalue heigen hnonnegative previous j
                hprevious_zero (Or.inl (by
                  dsimp [previous]
                  omega))
            · have hbackward : j.val < i.val := by omega
              let next : Index p q L :=
                ⟨j.val + 1, by have hi := i.isLt; omega⟩
              have hnext_distance :
                  Nat.dist i.val next.val < distance := by
                rw [Nat.dist_eq_sub_of_le_right
                  (show next.val ≤ i.val by
                    dsimp [next]
                    omega)]
                rw [Nat.dist_eq_sub_of_le_right
                  (Nat.le_of_lt hbackward)] at hdistance
                dsimp [next]
                omega
              have hnext_zero : v next = 0 :=
                ih (Nat.dist i.val next.val)
                  hnext_distance next rfl
              exact nonnegative_eigenvector_zero_propagates
                h hstrict v eigenvalue heigen hnonnegative next j
                hnext_zero (Or.inr (by
                  dsimp [next]))
    exact hchain (Nat.dist i.val j.val) j rfl
  · exact hpositive

theorem exists_positive_unit_topEigenvector
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n) :
    ∃ v : Space p q L,
      ‖v‖ = 1 ∧
        operator n w p q L v = topEigenvalue n w p q L • v ∧
        ∀ i : Index p q L, 0 < v i := by
  obtain ⟨v, hunit, heigen, hnonnegative⟩ :=
    exists_nonnegative_unit_topEigenvector h hstrict
  have hnonzero : v ≠ 0 := by
    intro hzero
    simp [hzero] at hunit
  exact ⟨v, hunit, heigen, fun i =>
    nonnegative_eigenvector_coordinate_pos h hstrict
      v (topEigenvalue n w p q L)
      heigen hnonnegative hnonzero i⟩

theorem topEigenvalue_pos {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (hwindow : p + q < L) :
    0 < topEigenvalue n w p q L := by
  classical
  obtain ⟨v, hunit, heigen, hv⟩ :=
    exists_positive_unit_topEigenvector h hstrict
  let i : Index p q L := ⟨0, by omega⟩
  let j : Index p q L := ⟨1, by omega⟩
  have hentry : 0 < matrix n w p q L i j :=
    matrix_adjacent_pos h hstrict i j (Or.inl (by rfl))
  have hterms :
      ∀ r ∈ (Finset.univ : Finset (Index p q L)),
        0 ≤ matrix n w p q L i r * v r := by
    intro r _
    exact mul_nonneg
      (matrix_entry_nonneg h hstrict i r) (hv r).le
  have hsum :
      0 < ∑ r : Index p q L,
        matrix n w p q L i r * v r := by
    apply Finset.sum_pos' hterms
    exact ⟨j, Finset.mem_univ j, mul_pos hentry (hv j)⟩
  have hcoordinate :=
    congrArg (fun z : Space p q L => z i) heigen
  change
    (∑ r : Index p q L, matrix n w p q L i r * v r) =
      topEigenvalue n w p q L * v i at hcoordinate
  rw [hcoordinate] at hsum
  exact (mul_pos_iff_of_pos_right (hv i)).mp hsum

theorem johnsonWindowHarmonicDimension_pos
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (i : Index p q L) :
    0 < MetricCodes.booleanHarmonicDimension n (p + q + i.val) := by
  apply booleanHarmonicDimension_pos
  have hi := i.isLt
  have hfirst := h.first_le
  have hterminal := h.terminal_le_weight
  have hhalf := h.weight_half
  omega

def johnsonRecurrenceWeight
    (n _ p q L : ℕ) (v : Space p q L) (i : Index p q L) : ℝ :=
  Real.sqrt (MetricCodes.booleanHarmonicDimension n (p + q + i.val) : ℝ) *
    v i

def johnsonSourceChannelCoefficient
    (n w p q L : ℕ) (m i : Index p q L) : ℝ :=
  matrix n w p q L m i *
    Real.sqrt (MetricCodes.booleanHarmonicDimension n (p + q + m.val) : ℝ) /
      Real.sqrt (MetricCodes.booleanHarmonicDimension n (p + q + i.val) : ℝ)

theorem johnsonSourceChannelCoefficient_mul_sqrt_dimension
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (m i : Index p q L) :
    johnsonSourceChannelCoefficient n w p q L m i *
        Real.sqrt
          (MetricCodes.booleanHarmonicDimension n (p + q + i.val) : ℝ) =
      matrix n w p q L m i *
        Real.sqrt
          (MetricCodes.booleanHarmonicDimension n (p + q + m.val) : ℝ) := by
  have hdimension :
      0 < (MetricCodes.booleanHarmonicDimension n (p + q + i.val) : ℝ) := by
    exact_mod_cast johnsonWindowHarmonicDimension_pos h i
  have hsqrt :
      Real.sqrt
        (MetricCodes.booleanHarmonicDimension n (p + q + i.val) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr hdimension).ne'
  unfold johnsonSourceChannelCoefficient
  field_simp [hsqrt]

theorem johnsonSourceChannelCoefficient_nonneg
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n) (m i : Index p q L) :
    0 ≤ johnsonSourceChannelCoefficient n w p q L m i := by
  unfold johnsonSourceChannelCoefficient
  exact div_nonneg
    (mul_nonneg (matrix_entry_nonneg h hstrict m i)
      (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

theorem johnsonRecurrenceWeight_pos_of_pos
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (v : Space p q L) (hv : ∀ i : Index p q L, 0 < v i)
    (i : Index p q L) :
    0 < johnsonRecurrenceWeight n w p q L v i := by
  unfold johnsonRecurrenceWeight
  apply mul_pos
  · apply Real.sqrt_pos.mpr
    exact_mod_cast johnsonWindowHarmonicDimension_pos h i
  · exact hv i

theorem johnsonRecurrenceWeight_eigenrecurrence
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (v : Space p q L) (lam : ℝ)
    (heigen : operator n w p q L v = lam • v)
    (m : Index p q L) :
    (∑ i : Index p q L,
      johnsonSourceChannelCoefficient n w p q L m i *
        johnsonRecurrenceWeight n w p q L v i) =
      lam * johnsonRecurrenceWeight n w p q L v m := by
  classical
  have hcoordinate :=
    congrArg (fun z : Space p q L => z m) heigen
  change
    (∑ i : Index p q L, matrix n w p q L m i * v i) =
      lam * v m at hcoordinate
  calc
    (∑ i : Index p q L,
      johnsonSourceChannelCoefficient n w p q L m i *
        johnsonRecurrenceWeight n w p q L v i) =
      ∑ i : Index p q L,
        (matrix n w p q L m i * v i) *
          Real.sqrt
            (MetricCodes.booleanHarmonicDimension n (p + q + m.val) : ℝ) := by
            apply Finset.sum_congr rfl
            intro i _
            unfold johnsonRecurrenceWeight
            have hentry :=
              johnsonSourceChannelCoefficient_mul_sqrt_dimension h m i
            calc
              johnsonSourceChannelCoefficient n w p q L m i *
                  (Real.sqrt
                    (MetricCodes.booleanHarmonicDimension
                      n (p + q + i.val) : ℝ) * v i) =
                (johnsonSourceChannelCoefficient n w p q L m i *
                  Real.sqrt
                    (MetricCodes.booleanHarmonicDimension
                      n (p + q + i.val) : ℝ)) * v i := by
                    ring
              _ = (matrix n w p q L m i *
                    Real.sqrt
                      (MetricCodes.booleanHarmonicDimension
                        n (p + q + m.val) : ℝ)) * v i := by
                      rw [hentry]
              _ = (matrix n w p q L m i * v i) *
                    Real.sqrt
                      (MetricCodes.booleanHarmonicDimension
                        n (p + q + m.val) : ℝ) := by
                      ring
    _ = (∑ i : Index p q L,
          matrix n w p q L m i * v i) *
        Real.sqrt
          (MetricCodes.booleanHarmonicDimension n (p + q + m.val) : ℝ) := by
          rw [Finset.sum_mul]
    _ = lam * johnsonRecurrenceWeight n w p q L v m := by
          rw [hcoordinate]
          unfold johnsonRecurrenceWeight
          ring

def johnsonAdjacentBlockCoefficient
    (n w p q L : ℕ) (v : Space p q L) (lam : ℝ)
    (target source : Index p q L) : ℝ :=
  Real.sqrt
    (johnsonSourceChannelCoefficient n w p q L source target *
      johnsonRecurrenceWeight n w p q L v target /
        (lam * johnsonRecurrenceWeight n w p q L v source))

theorem johnsonAdjacentBlockCoefficient_sq
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L) (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (target source : Index p q L) :
    johnsonAdjacentBlockCoefficient n w p q L v lam target source ^ 2 =
      johnsonSourceChannelCoefficient n w p q L source target *
        johnsonRecurrenceWeight n w p q L v target /
          (lam * johnsonRecurrenceWeight n w p q L v source) := by
  unfold johnsonAdjacentBlockCoefficient
  apply Real.sq_sqrt
  exact div_nonneg
    (mul_nonneg
      (johnsonSourceChannelCoefficient_nonneg h hstrict source target)
      (johnsonRecurrenceWeight_pos_of_pos h v hv target).le)
    (mul_pos hlam
      (johnsonRecurrenceWeight_pos_of_pos h v hv source)).le

theorem johnsonAdjacentBlockCoefficient_sq_sum
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L) (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen : operator n w p q L v = lam • v)
    (source : Index p q L) :
    (∑ target : Index p q L,
      johnsonAdjacentBlockCoefficient n w p q L v lam
        target source ^ 2) = 1 := by
  classical
  simp_rw [johnsonAdjacentBlockCoefficient_sq
    h hstrict v hv lam hlam]
  rw [← Finset.sum_div,
    johnsonRecurrenceWeight_eigenrecurrence
      h v lam heigen source]
  exact div_self
    (mul_pos hlam
      (johnsonRecurrenceWeight_pos_of_pos h v hv source)).ne'

def johnsonRecurrenceNormalization
    (n w p q L : ℕ) (v : Space p q L) : ℝ :=
  ∑ i : Index p q L, johnsonRecurrenceWeight n w p q L v i

def johnsonFibreAmplitude
    (n w p q L : ℕ) (v : Space p q L) (i : Index p q L) : ℝ :=
  Real.sqrt
    (johnsonRecurrenceWeight n w p q L v i /
      johnsonRecurrenceNormalization n w p q L v)

theorem johnsonRecurrenceNormalization_pos
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (v : Space p q L) (hv : ∀ i : Index p q L, 0 < v i) :
    0 < johnsonRecurrenceNormalization n w p q L v := by
  classical
  let i : Index p q L := ⟨0, by
    have hfirst := h.first_le
    omega⟩
  unfold johnsonRecurrenceNormalization
  apply Finset.sum_pos'
  · intro j _
    exact (johnsonRecurrenceWeight_pos_of_pos h v hv j).le
  · exact ⟨i, Finset.mem_univ i,
      johnsonRecurrenceWeight_pos_of_pos h v hv i⟩

theorem johnsonFibreAmplitude_sq
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (v : Space p q L) (hv : ∀ i : Index p q L, 0 < v i)
    (i : Index p q L) :
    johnsonFibreAmplitude n w p q L v i ^ 2 =
      johnsonRecurrenceWeight n w p q L v i /
        johnsonRecurrenceNormalization n w p q L v := by
  unfold johnsonFibreAmplitude
  apply Real.sq_sqrt
  exact div_nonneg
    (johnsonRecurrenceWeight_pos_of_pos h v hv i).le
    (johnsonRecurrenceNormalization_pos h v hv).le

theorem johnsonFibreAmplitude_sq_sum
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (v : Space p q L) (hv : ∀ i : Index p q L, 0 < v i) :
    (∑ i : Index p q L,
      johnsonFibreAmplitude n w p q L v i ^ 2) = 1 := by
  simp_rw [johnsonFibreAmplitude_sq h v hv]
  rw [← Finset.sum_div]
  change
    johnsonRecurrenceNormalization n w p q L v /
      johnsonRecurrenceNormalization n w p q L v = 1
  exact div_self (johnsonRecurrenceNormalization_pos h v hv).ne'

theorem johnsonFibreAmplitude_pos_of_pos
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (v : Space p q L) (hv : ∀ i : Index p q L, 0 < v i)
    (i : Index p q L) :
    0 < johnsonFibreAmplitude n w p q L v i := by
  unfold johnsonFibreAmplitude
  apply Real.sqrt_pos.mpr
  exact div_pos
    (johnsonRecurrenceWeight_pos_of_pos h v hv i)
    (johnsonRecurrenceNormalization_pos h v hv)

theorem johnsonAdjacentBlockCoefficient_amplitude_identity
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L) (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (target source : Index p q L) :
    johnsonAdjacentBlockCoefficient n w p q L v lam target source *
        johnsonFibreAmplitude n w p q L v target *
        Real.sqrt
          (johnsonSourceChannelCoefficient n w p q L source target) =
      johnsonAdjacentBlockCoefficient n w p q L v lam target source ^ 2 *
        Real.sqrt lam * johnsonFibreAmplitude n w p q L v source := by
  have hcoefficient :=
    johnsonSourceChannelCoefficient_nonneg h hstrict source target
  have hsource :=
    johnsonRecurrenceWeight_pos_of_pos h v hv source
  have hnormal := johnsonRecurrenceNormalization_pos h v hv
  have hleft :
      0 ≤ johnsonAdjacentBlockCoefficient n w p q L v lam target source *
        johnsonFibreAmplitude n w p q L v target *
        Real.sqrt
          (johnsonSourceChannelCoefficient n w p q L source target) := by
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _)
        (johnsonFibreAmplitude_pos_of_pos h v hv target).le)
      (Real.sqrt_nonneg _)
  have hright :
      0 ≤
        johnsonAdjacentBlockCoefficient n w p q L v lam target source ^ 2 *
          Real.sqrt lam * johnsonFibreAmplitude n w p q L v source := by
    exact mul_nonneg
      (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
      (johnsonFibreAmplitude_pos_of_pos h v hv source).le
  have hsquare :
      (johnsonAdjacentBlockCoefficient n w p q L v lam target source *
        johnsonFibreAmplitude n w p q L v target *
        Real.sqrt
          (johnsonSourceChannelCoefficient
            n w p q L source target)) ^ 2 =
      (johnsonAdjacentBlockCoefficient n w p q L v lam target source ^ 2 *
        Real.sqrt lam * johnsonFibreAmplitude n w p q L v source) ^ 2 := by
    simp only [mul_pow]
    rw [johnsonAdjacentBlockCoefficient_sq
      h hstrict v hv lam hlam target source,
      johnsonFibreAmplitude_sq h v hv target,
      Real.sq_sqrt hcoefficient,
      Real.sq_sqrt hlam.le,
      johnsonFibreAmplitude_sq h v hv source]
    field_simp [hlam.ne', hsource.ne', hnormal.ne']
  nlinarith

theorem johnsonAdjacentBlockCoefficient_amplitude_sum
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L) (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen : operator n w p q L v = lam • v)
    (source : Index p q L) :
    (∑ target : Index p q L,
      johnsonAdjacentBlockCoefficient n w p q L v lam target source *
        johnsonFibreAmplitude n w p q L v target *
        Real.sqrt
          (johnsonSourceChannelCoefficient
            n w p q L source target)) =
      Real.sqrt lam * johnsonFibreAmplitude n w p q L v source := by
  simp_rw [johnsonAdjacentBlockCoefficient_amplitude_identity
    h hstrict v hv lam hlam]
  rw [← Finset.sum_mul, ← Finset.sum_mul,
    johnsonAdjacentBlockCoefficient_sq_sum
      h hstrict v hv lam hlam heigen source]
  simp

structure ProjectionGram (n w p q L : ℕ) where

  projections :
    MetricCodes.ProjectionFamily (JohnsonSphere n w)
      (MetricCodes.johnsonAmbientDimension n (p + q) L)
      (MetricCodes.johnsonFibreDimension n w p q)

  feature : JohnsonSphere n w →
    EuclideanSpace ℝ
      (Fin (n * MetricCodes.johnsonAmbientDimension n (p + q) L *
        MetricCodes.johnsonAmbientDimension n (p + q) L))

  gram : ∀ x y : JohnsonSphere n w,
    ⟪feature x, feature y⟫_ℝ =
      (correlation x y - topEigenvalue n w p q L) *
        projections.overlap x y

theorem finite_bound_of_projection_gram
    {n w p q L d : ℕ}
    (hdegree : AdmissibleDegrees n w p q L)
    (hd : 0 < d)
    (data : ProjectionGram n w p q L)
    (C : Finset (JohnsonSphere n w)) (hC : IsCode d C)
    (hgap : threshold n w d < topEigenvalue n w p q L) :
    (C.card : ℝ) ≤
      ((1 - threshold n w d) /
        (topEigenvalue n w p q L - threshold n w d)) *
          ((MetricCodes.johnsonAmbientDimension n (p + q) L : ℝ) /
            (MetricCodes.johnsonFibreDimension n w p q : ℝ)) := by
  apply MetricCodes.projection_certificate data.projections C
    correlation data.feature hdegree.fibreDimension_pos
    (threshold_lt_one hdegree.weight_pos hdegree.weight_lt hd) hgap
  · intro x _
    exact correlation_self x
  · intro x hx y hy hxy
    exact correlation_le_threshold_of_code hdegree.weight_pos
      hdegree.weight_lt hC hx hy hxy
  · intro x _ y _
    exact data.gram x y

theorem finite_shellCodeNumber_bound_of_projection_gram
    {n w p q L d : ℕ}
    (hdegree : AdmissibleDegrees n w p q L)
    (hd : 0 < d)
    (data : ProjectionGram n w p q L)
    (hgap : threshold n w d < topEigenvalue n w p q L) :
    (shellCodeNumber n w d : ℝ) ≤
      ((1 - threshold n w d) /
        (topEigenvalue n w p q L - threshold n w d)) *
          ((MetricCodes.johnsonAmbientDimension n (p + q) L : ℝ) /
            (MetricCodes.johnsonFibreDimension n w p q : ℝ)) := by
  obtain ⟨C, hweight, hC, hcard⟩ := exists_shellCodeNumber n w d
  have hbound := finite_bound_of_projection_gram hdegree hd data
    (asSubtype C hweight) (isCode_asSubtype C hweight hC) hgap
  rw [card_asSubtype, hcard] at hbound
  exact hbound

theorem finite_binaryCodeNumber_bound_of_projection_gram
    {n w p q L d : ℕ}
    (hdegree : AdmissibleDegrees n w p q L)
    (hd : 0 < d)
    (data : ProjectionGram n w p q L)
    (hgap : threshold n w d < topEigenvalue n w p q L) :
    (binaryCodeNumber n d : ℝ) ≤
      ((2 : ℝ) ^ n / (n.choose w : ℝ)) *
        (((1 - threshold n w d) /
          (topEigenvalue n w p q L - threshold n w d)) *
            ((MetricCodes.johnsonAmbientDimension n (p + q) L : ℝ) /
              (MetricCodes.johnsonFibreDimension n w p q : ℝ))) := by
  have hfactor : 0 ≤ (2 : ℝ) ^ n / (n.choose w : ℝ) := by
    exact div_nonneg (by positivity) (Nat.cast_nonneg _)
  calc
    (binaryCodeNumber n d : ℝ) ≤
        ((2 : ℝ) ^ n / (n.choose w : ℝ)) *
          (shellCodeNumber n w d : ℝ) :=
      bassalygo_elias_real hdegree.weight_lt.le
    _ ≤ ((2 : ℝ) ^ n / (n.choose w : ℝ)) *
        (((1 - threshold n w d) /
          (topEigenvalue n w p q L - threshold n w d)) *
            ((MetricCodes.johnsonAmbientDimension n (p + q) L : ℝ) /
              (MetricCodes.johnsonFibreDimension n w p q : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (finite_shellCodeNumber_bound_of_projection_gram
          hdegree hd data hgap)
        hfactor

def centeredDegree (u : ℝ) : ℝ := 1 - 2 * u

def centeredWeight (α : ℝ) : ℝ := 1 - 2 * α

def centeredSigma (β γ : ℝ) : ℝ := 1 - 2 * β - 2 * γ

def centeredEta (α β γ : ℝ) : ℝ :=
  1 - 2 * α + 2 * β - 2 * γ

def spectralLimit (α β γ u : ℝ) : ℝ :=
  let z := centeredDegree u
  let m := centeredWeight α
  let σ := centeredSigma β γ
  let η := centeredEta α β γ
  (σ * η - m * z ^ 2) ^ 2 /
      (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
    ((z ^ 2 - η ^ 2) * (σ ^ 2 - z ^ 2)) /
      (z ^ 2 * (1 - m ^ 2) * Real.sqrt (1 - z ^ 2))

theorem sqrt_one_sub_centeredDegree_sq {u : ℝ}
    (hu : 0 < u) (hhalf : u < (1 : ℝ) / 2) :
    Real.sqrt (1 - centeredDegree u ^ 2) =
      2 * Real.sqrt (u * (1 - u)) := by
  have hvariance : 0 < u * (1 - u) :=
    mul_pos hu (by linarith)
  have hrad : 0 ≤ 1 - centeredDegree u ^ 2 := by
    unfold centeredDegree
    nlinarith
  have hsquare := Real.sq_sqrt hvariance.le
  apply (Real.sqrt_eq_iff_eq_sq hrad (by positivity)).mpr
  unfold centeredDegree
  nlinarith

theorem zero_fibre_spectral_algebra
    (z m s : ℝ)
    (hz : z ≠ 0) (hm : 1 - m ^ 2 ≠ 0)
    (hs : s ≠ 0) (hplus : 1 + 2 * s ≠ 0)
    (hsquare : 4 * s ^ 2 = 1 - z ^ 2) :
    1 -
        ((m - m * z ^ 2) ^ 2 /
          (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
          ((z ^ 2 - m ^ 2) * (1 - z ^ 2)) /
            (z ^ 2 * (1 - m ^ 2) * (2 * s))) =
      (z ^ 2 - m ^ 2) /
        ((1 - m ^ 2) * (1 + 2 * s)) := by
  have hzsq : z ^ 2 = 1 - 4 * s ^ 2 := by
    nlinarith [hsquare]
  have hzsqne : 1 - 4 * s ^ 2 ≠ 0 := by
    rw [← hzsq]
    exact pow_ne_zero 2 hz
  have hplus' : 2 * s + 1 ≠ 0 := by
    simpa [add_comm] using hplus
  have hplus'' : 1 + s * 2 ≠ 0 := by
    simpa [mul_comm] using hplus
  have hfour : 4 * s ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hs)
  rw [hzsq]
  field_simp [hm, hs, hplus, hplus', hplus'', hfour, hzsqne]
  ; ring

theorem spectralLimit_zero_fibre_boundary {α u : ℝ}
    (hu : 0 < u) (hua : u < α)
    (ha : α < (1 : ℝ) / 2) :
    1 - spectralLimit α 0 0 u =
      (α * (1 - α) - u * (1 - u)) /
        (α * (1 - α) *
          (1 + 2 * Real.sqrt (u * (1 - u)))) := by
  let z : ℝ := centeredDegree u
  let m : ℝ := centeredWeight α
  let s : ℝ := Real.sqrt (u * (1 - u))
  have ha0 : 0 < α := lt_trans hu hua
  have haone : 0 < 1 - α := by linarith
  have huone : 0 < 1 - u := by linarith
  have hvariance : 0 < u * (1 - u) := mul_pos hu huone
  have hz : z ≠ 0 := by
    dsimp [z, centeredDegree]
    nlinarith
  have hm : 1 - m ^ 2 ≠ 0 := by
    have hprod : 0 < α * (1 - α) := mul_pos ha0 haone
    dsimp [m, centeredWeight]
    nlinarith
  have hs : s ≠ 0 := by
    dsimp [s]
    exact (Real.sqrt_pos.mpr hvariance).ne'
  have hplus : 1 + 2 * s ≠ 0 := by
    have hsnonneg : 0 ≤ s := by
      dsimp [s]
      exact Real.sqrt_nonneg _
    nlinarith
  have hsquare : 4 * s ^ 2 = 1 - z ^ 2 := by
    have hsqrt := Real.sq_sqrt hvariance.le
    dsimp [s, z, centeredDegree]
    nlinarith
  have hradical : Real.sqrt (1 - z ^ 2) = 2 * s := by
    simpa [z, s] using
      sqrt_one_sub_centeredDegree_sq hu (lt_trans hua ha)
  have hsig : centeredSigma 0 0 = 1 := by
    norm_num [centeredSigma]
  have heta : centeredEta α 0 0 = centeredWeight α := by
    simp [centeredEta, centeredWeight]
  have hlimit :
      spectralLimit α 0 0 u =
        (m - m * z ^ 2) ^ 2 /
            (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
          ((z ^ 2 - m ^ 2) * (1 - z ^ 2)) /
            (z ^ 2 * (1 - m ^ 2) * (2 * s)) := by
    change
      ((centeredSigma 0 0 * centeredEta α 0 0 -
          centeredWeight α * centeredDegree u ^ 2) ^ 2 /
        (centeredDegree u ^ 2 *
          (1 - centeredWeight α ^ 2) *
          (1 - centeredDegree u ^ 2)) +
        ((centeredDegree u ^ 2 - centeredEta α 0 0 ^ 2) *
          (centeredSigma 0 0 ^ 2 - centeredDegree u ^ 2)) /
          (centeredDegree u ^ 2 *
            (1 - centeredWeight α ^ 2) *
            Real.sqrt (1 - centeredDegree u ^ 2))) = _
    rw [hsig, heta]
    simp only [one_mul, one_pow]
    change
      (m - m * z ^ 2) ^ 2 /
          (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
        ((z ^ 2 - m ^ 2) * (1 - z ^ 2)) /
          (z ^ 2 * (1 - m ^ 2) * Real.sqrt (1 - z ^ 2)) = _
    rw [hradical]
  have hA : α * (1 - α) ≠ 0 :=
    (mul_pos ha0 haone).ne'
  have hfourA : α * 4 - α ^ 2 * 4 ≠ 0 := by
    have hp : 0 < α * (1 - α) := mul_pos ha0 haone
    nlinarith
  have hmraw : 1 - (1 - 2 * α) ^ 2 ≠ 0 := by
    simpa [m, centeredWeight] using hm
  have hplusraw :
      1 + 2 * Real.sqrt (u * (1 - u)) ≠ 0 := by
    simpa [s] using hplus
  calc
    1 - spectralLimit α 0 0 u =
        (z ^ 2 - m ^ 2) /
          ((1 - m ^ 2) * (1 + 2 * s)) := by
      rw [hlimit]
      exact zero_fibre_spectral_algebra z m s hz hm hs hplus hsquare
    _ = (α * (1 - α) - u * (1 - u)) /
        (α * (1 - α) *
          (1 + 2 * Real.sqrt (u * (1 - u)))) := by
      dsimp [z, m, s, centeredDegree, centeredWeight]
      field_simp [hmraw, hA, hfourA, hplusraw]
      ; ring

def asymptoticThreshold (δ α : ℝ) : ℝ :=
  1 - δ / (2 * α * (1 - α))

def rankPenalty (α β γ : ℝ) : ℝ :=
  α * MetricCodes.binaryEntropy (β / α) +
    (1 - α) * MetricCodes.binaryEntropy (γ / (1 - α))

def shellRate (α β γ u : ℝ) : ℝ :=
  1 - MetricCodes.binaryEntropy α + MetricCodes.binaryEntropy u -
    rankPenalty α β γ

theorem binaryEntropy_eq_binEntropy_div_log (u : ℝ) :
    MetricCodes.binaryEntropy u = Real.binEntropy u / Real.log 2 := by
  simp only [MetricCodes.binaryEntropy, Real.logb, Real.binEntropy,
    Real.log_inv]
  ring

theorem binaryEntropy_le_one (u : ℝ) :
    MetricCodes.binaryEntropy u ≤ 1 := by
  rw [binaryEntropy_eq_binEntropy_div_log]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ hlog).mpr
  simpa using (Real.binEntropy_le_log_two (p := u))

structure AsymptoticParameters (δ α β γ u : ℝ) : Prop where
  distance_pos : 0 < δ
  distance_lt_half : δ < (1 : ℝ) / 2
  weight_gt_distance : δ / 2 < α
  weight_lt_half : α < (1 : ℝ) / 2
  support_nonneg : 0 ≤ β
  support_lt_half : β < α / 2
  complement_nonneg : 0 ≤ γ
  complement_lt_half : γ < (1 - α) / 2
  first_lt_degree : β + γ < u
  degree_lt_weight : u < α
  degree_lt_left : u < α - β + γ
  degree_lt_right : u < 1 - α + β - γ

namespace AsymptoticParameters

variable {δ α β γ u : ℝ}

theorem weight_pos (h : AsymptoticParameters δ α β γ u) :
    0 < α := by
  nlinarith [h.distance_pos, h.weight_gt_distance]

theorem weight_complement_pos
    (h : AsymptoticParameters δ α β γ u) :
    0 < 1 - α := by
  nlinarith [h.weight_lt_half]

theorem degree_pos (h : AsymptoticParameters δ α β γ u) :
    0 < u := by
  nlinarith [h.support_nonneg, h.complement_nonneg,
    h.first_lt_degree]

theorem centeredDegree_pos
    (h : AsymptoticParameters δ α β γ u) :
    0 < centeredDegree u := by
  unfold centeredDegree
  nlinarith [h.degree_lt_weight, h.weight_lt_half]

theorem centeredWeight_pos
    (h : AsymptoticParameters δ α β γ u) :
    0 < centeredWeight α := by
  unfold centeredWeight
  nlinarith [h.weight_lt_half]

theorem centeredSigma_gt_degree
    (h : AsymptoticParameters δ α β γ u) :
    centeredDegree u < centeredSigma β γ := by
  unfold centeredDegree centeredSigma
  nlinarith [h.first_lt_degree]

theorem centeredSigma_pos
    (h : AsymptoticParameters δ α β γ u) :
    0 < centeredSigma β γ := by
  exact lt_trans h.centeredDegree_pos h.centeredSigma_gt_degree

theorem centeredEta_lt_degree
    (h : AsymptoticParameters δ α β γ u) :
    centeredEta α β γ < centeredDegree u := by
  unfold centeredEta centeredDegree
  nlinarith [h.degree_lt_left]

theorem neg_degree_lt_centeredEta
    (h : AsymptoticParameters δ α β γ u) :
    -centeredDegree u < centeredEta α β γ := by
  unfold centeredEta centeredDegree
  nlinarith [h.degree_lt_right]

theorem one_sub_centeredWeight_sq_pos
    (h : AsymptoticParameters δ α β γ u) :
    0 < 1 - centeredWeight α ^ 2 := by
  have hprod : 0 < α * (1 - α) :=
    mul_pos h.weight_pos h.weight_complement_pos
  unfold centeredWeight
  nlinarith

theorem one_sub_centeredDegree_sq_pos
    (h : AsymptoticParameters δ α β γ u) :
    0 < 1 - centeredDegree u ^ 2 := by
  have huone : 0 < 1 - u := by
    nlinarith [h.degree_lt_weight, h.weight_lt_half]
  have hprod : 0 < u * (1 - u) := mul_pos h.degree_pos huone
  unfold centeredDegree
  nlinarith

theorem degree_sq_sub_eta_sq_pos
    (h : AsymptoticParameters δ α β γ u) :
    0 < centeredDegree u ^ 2 - centeredEta α β γ ^ 2 := by
  have hleft : 0 < centeredDegree u - centeredEta α β γ :=
    sub_pos.mpr h.centeredEta_lt_degree
  have hright : 0 < centeredDegree u + centeredEta α β γ := by
    linarith [h.neg_degree_lt_centeredEta]
  nlinarith [mul_pos hleft hright]

theorem sigma_sq_sub_degree_sq_pos
    (h : AsymptoticParameters δ α β γ u) :
    0 < centeredSigma β γ ^ 2 - centeredDegree u ^ 2 := by
  have hleft : 0 < centeredSigma β γ - centeredDegree u :=
    sub_pos.mpr h.centeredSigma_gt_degree
  have hright : 0 < centeredSigma β γ + centeredDegree u :=
    add_pos h.centeredSigma_pos h.centeredDegree_pos
  nlinarith [mul_pos hleft hright]

theorem rankPenalty_le_one
    (h : AsymptoticParameters δ α β γ u) :
    rankPenalty α β γ ≤ 1 := by
  have hsupport := mul_le_mul_of_nonneg_left
    (binaryEntropy_le_one (β / α)) h.weight_pos.le
  have hcomplement := mul_le_mul_of_nonneg_left
    (binaryEntropy_le_one (γ / (1 - α)))
    h.weight_complement_pos.le
  unfold rankPenalty
  nlinarith

theorem shellRate_lower
    (h : AsymptoticParameters δ α β γ u) :
    -1 ≤ shellRate α β γ u := by
  have hαentropy := binaryEntropy_le_one α
  have huone : u ≤ 1 := by
    nlinarith [h.degree_lt_weight, h.weight_lt_half]
  have huentropy := MetricCodes.binaryEntropy_nonneg h.degree_pos.le huone
  unfold shellRate
  nlinarith [h.rankPenalty_le_one]

end AsymptoticParameters

@[simp] theorem shellRate_zero_fibre (α u : ℝ) :
    shellRate α 0 0 u =
      1 - MetricCodes.binaryEntropy α + MetricCodes.binaryEntropy u := by
  simp [shellRate, rankPenalty]

def IsSpectrallyFeasible (δ α β γ u : ℝ) : Prop :=
  asymptoticThreshold δ α < spectralLimit α β γ u

def Feasible (δ α β γ u : ℝ) : Prop :=
  AsymptoticParameters δ α β γ u ∧
    IsSpectrallyFeasible δ α β γ u

def rateSet (δ : ℝ) : Set ℝ :=
  {r | ∃ α β γ u : ℝ,
    Feasible δ α β γ u ∧ r = shellRate α β γ u}

theorem rateSet_bddBelow (δ : ℝ) :
    BddBelow (rateSet δ) := by
  refine ⟨-1, ?_⟩
  rintro r ⟨α, β, γ, u, ⟨hparameter, _hspectral⟩, rfl⟩
  exact hparameter.shellRate_lower

def variationalRate (δ : ℝ) : ℝ :=
  sInf (rateSet δ)

theorem variationalRate_le_of_feasible {δ α β γ u : ℝ}
    (h : Feasible δ α β γ u) :
    variationalRate δ ≤ shellRate α β γ u := by
  exact csInf_le (rateSet_bddBelow δ) ⟨α, β, γ, u, h, rfl⟩

def mrrwG (v : ℝ) : ℝ :=
  MetricCodes.binaryEntropy ((1 - Real.sqrt (1 - v)) / 2)

@[simp] theorem mrrwG_one : mrrwG 1 = 1 := by
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  simp [mrrwG, binaryEntropy_eq_binEntropy_div_log, hlog]

theorem mrrwG_continuous : Continuous mrrwG := by
  unfold mrrwG
  exact MetricCodes.Hamming.binaryEntropy_continuous.comp
    ((continuous_const.sub
      ((continuous_const.sub continuous_id).sqrt)).div_const 2)

theorem mrrwG_nonneg {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ mrrwG v := by
  have hroot : Real.sqrt (1 - v) ≤ 1 :=
    Real.sqrt_le_one.mpr (by linarith)
  have hroot' : 0 ≤ Real.sqrt (1 - v) :=
    Real.sqrt_nonneg _
  unfold mrrwG
  apply MetricCodes.binaryEntropy_nonneg
  · linarith
  · linarith

def mrrwObjective (δ r : ℝ) : ℝ :=
  1 + mrrwG (r ^ 2) -
    mrrwG (r ^ 2 + 2 * δ * r + 2 * δ)

theorem mrrwObjective_continuous (δ : ℝ) :
    Continuous (mrrwObjective δ) := by
  have hsquare : Continuous (fun r : ℝ => r ^ 2) :=
    continuous_id.pow 2
  have hargument :
      Continuous (fun r : ℝ => r ^ 2 + 2 * δ * r + 2 * δ) :=
    (hsquare.add (continuous_const.mul continuous_id)).add
      continuous_const
  unfold mrrwObjective
  exact (continuous_const.add (mrrwG_continuous.comp hsquare)).sub
    (mrrwG_continuous.comp hargument)

theorem mrrwObjective_endpoint {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    mrrwObjective δ (1 - 2 * δ) =
      MetricCodes.Hamming.classicalRate δ := by
  have hlast :
      (1 - 2 * δ) ^ 2 + 2 * δ * (1 - 2 * δ) + 2 * δ =
        (1 : ℝ) := by
    ring
  have hroot :
      Real.sqrt (1 - (1 - 2 * δ) ^ 2) =
        2 * Real.sqrt (δ * (1 - δ)) := by
    simpa [centeredDegree] using
      sqrt_one_sub_centeredDegree_sq hδ hhalf
  calc
    mrrwObjective δ (1 - 2 * δ) =
        mrrwG ((1 - 2 * δ) ^ 2) := by
      unfold mrrwObjective
      rw [hlast, mrrwG_one]
      ring
    _ = MetricCodes.Hamming.classicalRate δ := by
      unfold mrrwG MetricCodes.Hamming.classicalRate
        MetricCodes.Hamming.classicalParameter
      rw [hroot]
      congr 1 ; ring

theorem mrrwG_variance {u : ℝ}
    (hu : u ≤ (1 : ℝ) / 2) :
    mrrwG (4 * u * (1 - u)) = MetricCodes.binaryEntropy u := by
  have hrad :
      1 - 4 * u * (1 - u) = (1 - 2 * u) ^ 2 := by
    ring
  have hroot :
      Real.sqrt (1 - 4 * u * (1 - u)) = 1 - 2 * u := by
    rw [hrad, Real.sqrt_sq (by linarith)]
  unfold mrrwG
  rw [hroot]
  congr 1
  ring

theorem zero_fibre_boundary_variance {δ α u : ℝ}
    (hu : 0 < u) (hua : u < α)
    (ha : α < (1 : ℝ) / 2)
    (hboundary :
      spectralLimit α 0 0 u = asymptoticThreshold δ α) :
    4 * α * (1 - α) =
      (2 * Real.sqrt (u * (1 - u))) ^ 2 +
        2 * δ * (2 * Real.sqrt (u * (1 - u))) + 2 * δ := by
  have hα : 0 < α := lt_trans hu hua
  have hαone : 0 < 1 - α := by linarith
  have huone : 0 < 1 - u := by linarith
  have hA : α * (1 - α) ≠ 0 :=
    (mul_pos hα hαone).ne'
  have hs : 0 ≤ Real.sqrt (u * (1 - u)) :=
    Real.sqrt_nonneg _
  have hplus : 1 + 2 * Real.sqrt (u * (1 - u)) ≠ 0 := by
    nlinarith
  have hrel :
      δ / (2 * α * (1 - α)) =
        (α * (1 - α) - u * (1 - u)) /
          (α * (1 - α) *
            (1 + 2 * Real.sqrt (u * (1 - u)))) := by
    calc
      δ / (2 * α * (1 - α)) =
          1 - spectralLimit α 0 0 u := by
        rw [hboundary]
        unfold asymptoticThreshold
        ring
      _ = _ := spectralLimit_zero_fibre_boundary hu hua ha
  have hsquare := Real.sq_sqrt (mul_pos hu huone).le
  field_simp [hA, hα.ne', hαone.ne', hplus] at hrel
  nlinarith [hsquare]

theorem mrrwObjective_zero_fibre_boundary {δ α u : ℝ}
    (hu : 0 < u) (hua : u < α)
    (ha : α < (1 : ℝ) / 2)
    (hboundary :
      spectralLimit α 0 0 u = asymptoticThreshold δ α) :
    mrrwObjective δ (2 * Real.sqrt (u * (1 - u))) =
      shellRate α 0 0 u := by
  have huone : 0 < 1 - u := by linarith
  have hsquare := Real.sq_sqrt (mul_pos hu huone).le
  have hvariance :
      (2 * Real.sqrt (u * (1 - u))) ^ 2 =
        4 * u * (1 - u) := by
    nlinarith [hsquare]
  have hboundary' :=
    zero_fibre_boundary_variance hu hua ha hboundary
  have hargument :
      4 * u * (1 - u) +
        2 * δ * (2 * Real.sqrt (u * (1 - u))) + 2 * δ =
        4 * α * (1 - α) := by
    nlinarith [hboundary', hvariance]
  unfold mrrwObjective
  rw [hvariance, hargument,
    mrrwG_variance (by linarith : u ≤ (1 : ℝ) / 2),
    mrrwG_variance ha.le, shellRate_zero_fibre]
  ring

def mrrwRateSet (δ : ℝ) : Set ℝ :=
  {t | ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 - 2 * δ ∧
    t = mrrwObjective δ r}

theorem mrrwRateSet_bddBelow (δ : ℝ) :
    BddBelow (mrrwRateSet δ) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨r, _hr, _hupper, rfl⟩
  have hfirst := mrrwG_nonneg (sq_nonneg r)
  have hsecond :
      mrrwG (r ^ 2 + 2 * δ * r + 2 * δ) ≤ 1 := by
    unfold mrrwG
    exact binaryEntropy_le_one _
  unfold mrrwObjective
  linarith

def mrrwRate (δ : ℝ) : ℝ :=
  sInf (mrrwRateSet δ)

theorem mrrwRate_le_objective {δ r : ℝ}
    (hr : 0 ≤ r) (hupper : r ≤ 1 - 2 * δ) :
    mrrwRate δ ≤ mrrwObjective δ r := by
  exact csInf_le (mrrwRateSet_bddBelow δ)
    ⟨r, hr, hupper, rfl⟩

theorem exists_mrrw_minimizer {δ : ℝ}
    (hhalf : δ ≤ (1 : ℝ) / 2) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 - 2 * δ ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 - 2 * δ →
        mrrwObjective δ r ≤ mrrwObjective δ s := by
  have hnonempty : (Set.Icc 0 (1 - 2 * δ)).Nonempty := by
    refine ⟨0, ?_⟩
    constructor
    · exact le_rfl
    · linarith
  obtain ⟨r, hr, hmin⟩ :=
    isCompact_Icc.exists_isMinOn hnonempty
      (mrrwObjective_continuous δ).continuousOn
  refine ⟨r, hr.1, hr.2, ?_⟩
  intro s hs hupper
  exact hmin ⟨hs, hupper⟩

theorem mrrwRate_eq_objective_of_minimizer {δ r : ℝ}
    (hr : 0 ≤ r) (hupper : r ≤ 1 - 2 * δ)
    (hmin : ∀ s : ℝ, 0 ≤ s → s ≤ 1 - 2 * δ →
      mrrwObjective δ r ≤ mrrwObjective δ s) :
    mrrwRate δ = mrrwObjective δ r := by
  apply le_antisymm
  · exact mrrwRate_le_objective hr hupper
  · unfold mrrwRate
    apply le_csInf
    · exact ⟨mrrwObjective δ r, r, hr, hupper, rfl⟩
    · rintro _ ⟨s, hs, hsupper, rfl⟩
      exact hmin s hs hsupper

theorem mrrwRate_le_classicalRate {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    mrrwRate δ ≤ MetricCodes.Hamming.classicalRate δ := by
  calc
    mrrwRate δ ≤ mrrwObjective δ (1 - 2 * δ) :=
      mrrwRate_le_objective (by linarith) (le_refl _)
    _ = MetricCodes.Hamming.classicalRate δ :=
      mrrwObjective_endpoint hδ hhalf

theorem mrrw_endpoint_dichotomy {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    mrrwRate δ < MetricCodes.Hamming.classicalRate δ ∨
      mrrwRate δ = MetricCodes.Hamming.classicalRate δ := by
  exact lt_or_eq_of_le (mrrwRate_le_classicalRate hδ hhalf)

def combinedVariationalRate (δ : ℝ) : ℝ :=
  min (MetricCodes.Hamming.variationalRate δ) (variationalRate δ)

theorem combinedVariationalRate_le_hamming (δ : ℝ) :
    combinedVariationalRate δ ≤ MetricCodes.Hamming.variationalRate δ := by
  exact min_le_left _ _

theorem combinedVariationalRate_le_shell (δ : ℝ) :
    combinedVariationalRate δ ≤ variationalRate δ := by
  exact min_le_right _ _

theorem combinedVariationalRate_lt_mrrw_of_endpoint
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2)
    (hendpoint : mrrwRate δ = MetricCodes.Hamming.classicalRate δ) :
    combinedVariationalRate δ < mrrwRate δ := by
  calc
    combinedVariationalRate δ ≤
        MetricCodes.Hamming.variationalRate δ :=
      combinedVariationalRate_le_hamming δ
    _ < MetricCodes.Hamming.classicalRate δ :=
      MetricCodes.Hamming.variationalRate_lt_classicalRate hδ hhalf
    _ = mrrwRate δ := hendpoint.symm

end MetricCodes.Johnson

end

end

section

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped Topology

namespace MetricCodes.Johnson.Asymptotics

def shellWeight (a : ℝ) (n : ℕ) : ℕ :=
  MetricCodes.Hamming.longitudinalDegree a n

def supportDegree (b : ℝ) (n : ℕ) : ℕ :=
  MetricCodes.Hamming.longitudinalDegree b n

def complementDegree (g : ℝ) (n : ℕ) : ℕ :=
  MetricCodes.Hamming.longitudinalDegree g n

def terminalDegree (u : ℝ) (n : ℕ) : ℕ :=
  MetricCodes.Hamming.longitudinalDegree u n

theorem tendsto_shellWeight_ratio {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (shellWeight a n : ℝ) / (n : ℝ))
      atTop (nhds a) := by
  simpa [shellWeight] using
    MetricCodes.Hamming.tendsto_longitudinal_ratio ha

theorem tendsto_supportDegree_ratio {b : ℝ} (hb : 0 ≤ b) :
    Tendsto (fun n : ℕ => (supportDegree b n : ℝ) / (n : ℝ))
      atTop (nhds b) := by
  simpa [supportDegree] using
    MetricCodes.Hamming.tendsto_longitudinal_ratio hb

theorem tendsto_complementDegree_ratio {g : ℝ} (hg : 0 ≤ g) :
    Tendsto (fun n : ℕ => (complementDegree g n : ℝ) / (n : ℝ))
      atTop (nhds g) := by
  simpa [complementDegree] using
    MetricCodes.Hamming.tendsto_longitudinal_ratio hg

theorem tendsto_terminalDegree_ratio {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun n : ℕ => (terminalDegree u n : ℝ) / (n : ℝ))
      atTop (nhds u) := by
  simpa [terminalDegree] using
    MetricCodes.Hamming.tendsto_longitudinal_ratio hu

theorem tendsto_dimension_ratio :
    Tendsto (fun n : ℕ => (n : ℝ) / (n : ℝ))
      atTop (nhds (1 : ℝ)) := by
  refine (tendsto_const_nhds (x := (1 : ℝ))).congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  simp [hn]

theorem tendsto_add_degree_ratio
    {f g : ℕ → ℕ} {a b : ℝ}
    (hf : Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ))
      atTop (nhds a))
    (hg : Tendsto (fun n : ℕ => (g n : ℝ) / (n : ℝ))
      atTop (nhds b)) :
    Tendsto
      (fun n : ℕ => ((f n + g n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (a + b)) := by
  refine (hf.add hg).congr' (Eventually.of_forall fun n => ?_)
  push_cast
  ring

theorem eventually_degree_lt_of_ratio
    {f g : ℕ → ℕ} {a b : ℝ}
    (hf : Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ))
      atTop (nhds a))
    (hg : Tendsto (fun n : ℕ => (g n : ℝ) / (n : ℝ))
      atTop (nhds b))
    (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, f n < g n := by
  have hnegative : a - b < 0 := sub_neg.mpr hab
  have hratio :=
    (hf.sub hg).eventually (gt_mem_nhds hnegative)
  filter_upwards [hratio, eventually_gt_atTop (0 : ℕ)]
    with n hdiff hn
  have hnreal : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hquot : (f n : ℝ) / (n : ℝ) <
      (g n : ℝ) / (n : ℝ) := by
    linarith
  have hreal : (f n : ℝ) < (g n : ℝ) :=
    (div_lt_div_iff_of_pos_right hnreal).mp hquot
  exact_mod_cast hreal

theorem tendsto_atTop_of_ratio_pos
    {f : ℕ → ℕ} {a : ℝ}
    (ha : 0 < a)
    (hf : Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ))
      atTop (nhds a)) :
    Tendsto f atTop atTop := by
  refine tendsto_atTop.2 fun m => ?_
  have hratio := hf.eventually (Ioi_mem_nhds (half_lt_self ha))
  have hgrowth :
      Tendsto (fun n : ℕ => (a / 2) * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (half_pos ha)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hgrowth.eventually (eventually_ge_atTop (m : ℝ))
  filter_upwards [hratio, hlarge, eventually_gt_atTop (0 : ℕ)]
    with n hratio' hlarge' hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hfreal : (a / 2) * (n : ℝ) < (f n : ℝ) :=
    (lt_div_iff₀ hnreal).mp hratio'
  exact_mod_cast hlarge'.trans hfreal.le

theorem tendsto_sub_degree_ratio
    {f g : ℕ → ℕ} {a b : ℝ}
    (hf : Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ))
      atTop (nhds a))
    (hg : Tendsto (fun n : ℕ => (g n : ℝ) / (n : ℝ))
      atTop (nhds b))
    (hgf : ∀ᶠ n : ℕ in atTop, g n ≤ f n) :
    Tendsto
      (fun n : ℕ => ((f n - g n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (a - b)) := by
  refine (hf.sub hg).congr' ?_
  filter_upwards [hgf] with n hn
  rw [Nat.cast_sub hn]
  ring

theorem scaled_binomialEntropy_identity
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    (a * Real.log a - b * Real.log b -
      (a - b) * Real.log (a - b)) / Real.log 2 =
      a * MetricCodes.binaryEntropy (b / a) := by
  have hab : 0 < a - b := sub_pos.mpr hba
  have hratio : 0 < b / a := div_pos hb ha
  have hcomp : 0 < 1 - b / a := by
    apply sub_pos.mpr
    exact (div_lt_one ha).mpr hba
  have hblog :
      Real.log b = Real.log a + Real.log (b / a) := by
    calc
      Real.log b = Real.log (a * (b / a)) := by
        congr 1
        field_simp
      _ = Real.log a + Real.log (b / a) :=
        Real.log_mul ha.ne' hratio.ne'
  have hcomplog :
      Real.log (a - b) =
        Real.log a + Real.log (1 - b / a) := by
    calc
      Real.log (a - b) = Real.log (a * (1 - b / a)) := by
        congr 1
        field_simp

      _ = Real.log a + Real.log (1 - b / a) :=
        Real.log_mul ha.ne' hcomp.ne'
  rw [MetricCodes.Johnson.binaryEntropy_eq_binEntropy_div_log,
    Real.binEntropy, Real.log_inv, Real.log_inv,
    hblog, hcomplog]
  field_simp [ha.ne']
  ; ring

theorem tendsto_logb_choose_of_ratio
    {N K : ℕ → ℕ} {a b : ℝ}
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ))
      atTop (nhds a))
    (hK : Tendsto (fun n : ℕ => (K n : ℝ) / (n : ℝ))
      atTop (nhds b))
    (hb : 0 < b) (hba : b < a)
    (hKN : ∀ᶠ n : ℕ in atTop, K n ≤ N n) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2 ((N n).choose (K n) : ℝ) / (n : ℝ))
      atTop (nhds (a * MetricCodes.binaryEntropy (b / a))) := by
  have ha : 0 < a := lt_trans hb hba
  have hcomplement := tendsto_sub_degree_ratio hN hK hKN
  have hKgrowth := tendsto_atTop_of_ratio_pos hb hK
  have hcomplementgrowth :=
    tendsto_atTop_of_ratio_pos (sub_pos.mpr hba) hcomplement
  have hstirling := SpherePacking.tendsto_log_add_choose_div
    K (fun n : ℕ => N n - K n) b (a - b)
    hKgrowth hcomplementgrowth hK hcomplement
    hb (sub_pos.mpr hba)
  have hsum : b + (a - b) = a := by ring
  simp only [hsum] at hstirling
  have hbase := hstirling.div_const (Real.log 2)
  rw [scaled_binomialEntropy_identity ha hb hba] at hbase
  refine hbase.congr' ?_
  filter_upwards [hKN] with n hn
  have hinteger : K n + (N n - K n) = N n := by omega
  rw [hinteger]
  unfold Real.logb
  ring

theorem tendsto_logb_succ_of_le_dimension
    {N : ℕ → ℕ}
    (hN : ∀ᶠ n : ℕ in atTop, N n ≤ n) :
    Tendsto
      (fun n : ℕ => Real.logb 2 ((N n + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  have hupper := MetricCodes.Hamming.tendsto_logb_succ_div
  have hnonnegative :
      ∀ᶠ n : ℕ in atTop,
        (0 : ℝ) ≤
          Real.logb 2 ((N n + 1 : ℕ) : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    apply div_nonneg
    · apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
      exact_mod_cast (show 1 ≤ N n + 1 by omega)
    · exact Nat.cast_nonneg n
  have hbounded :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2 ((N n + 1 : ℕ) : ℝ) / (n : ℝ) ≤
          Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
    filter_upwards [hN, eventually_gt_atTop (0 : ℕ)]
      with n hNn hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    apply (div_le_div_iff_of_pos_right hnreal).mpr
    apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    · exact_mod_cast (show 0 < N n + 1 by omega)
    · exact_mod_cast (show N n + 1 ≤ n + 1 by omega)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hzero hupper hnonnegative hbounded

theorem tendsto_logb_booleanHarmonicDimension_of_ratio
    {N K : ℕ → ℕ} {a b : ℝ}
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ))
      atTop (nhds a))
    (hK : Tendsto (fun n : ℕ => (K n : ℝ) / (n : ℝ))
      atTop (nhds b))
    (hb : 0 < b) (hba : b < a)
    (hhalf : ∀ᶠ n : ℕ in atTop, 2 * K n ≤ N n)
    (hNle : ∀ᶠ n : ℕ in atTop, N n ≤ n) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) /
            (n : ℝ))
      atTop (nhds (a * MetricCodes.binaryEntropy (b / a))) := by
  have hKN : ∀ᶠ n : ℕ in atTop, K n ≤ N n :=
    hhalf.mono (fun _ hn => by omega)
  have hchoose :=
    tendsto_logb_choose_of_ratio hN hK hb hba hKN
  have hpoly := tendsto_logb_succ_of_le_dimension hNle
  have hlowerlimit :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2 ((N n).choose (K n) : ℝ) / (n : ℝ) -
            Real.logb 2 ((N n + 1 : ℕ) : ℝ) / (n : ℝ))
        atTop (nhds (a * MetricCodes.binaryEntropy (b / a))) := by
    simpa using hchoose.sub hpoly
  have hlower :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2 ((N n).choose (K n) : ℝ) / (n : ℝ) -
            Real.logb 2 ((N n + 1 : ℕ) : ℝ) / (n : ℝ) ≤
          Real.logb 2
            (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) /
              (n : ℝ) := by
    filter_upwards [hhalf, eventually_gt_atTop (0 : ℕ)]
      with n hhalf' hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hfibre :
        0 < (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) := by
      exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos hhalf'
    have hchoosepos : 0 < ((N n).choose (K n) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : K n ≤ N n)
    have hlog :
        Real.logb 2 ((N n).choose (K n) : ℝ) ≤
          Real.logb 2 ((N n + 1 : ℕ) : ℝ) +
            Real.logb 2
              (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) := by
      rw [← Real.logb_mul (by positivity) hfibre.ne']
      apply Real.logb_le_logb_of_le
        (by norm_num : (1 : ℝ) < 2) hchoosepos
      have hcomparison :=
        MetricCodes.Hamming.choose_le_mul_hammingFibreDimension hhalf'
      change
        ((N n).choose (K n) : ℝ) ≤
          ((N n + 1 : ℕ) : ℝ) *
            (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ)
      exact_mod_cast hcomparison
    calc
      Real.logb 2 ((N n).choose (K n) : ℝ) / (n : ℝ) -
          Real.logb 2 ((N n + 1 : ℕ) : ℝ) / (n : ℝ) =
        (Real.logb 2 ((N n).choose (K n) : ℝ) -
          Real.logb 2 ((N n + 1 : ℕ) : ℝ)) / (n : ℝ) := by ring
      _ ≤ Real.logb 2
            (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) /
              (n : ℝ) := by
        apply (div_le_div_iff_of_pos_right hnreal).mpr
        linarith
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
            (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) /
              (n : ℝ) ≤
          Real.logb 2 ((N n).choose (K n) : ℝ) / (n : ℝ) := by
    filter_upwards [hhalf, eventually_gt_atTop (0 : ℕ)]
      with n hhalf' hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hfibre :
        0 < (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) := by
      exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos hhalf'
    apply (div_le_div_iff_of_pos_right hnreal).mpr
    apply Real.logb_le_logb_of_le
      (by norm_num : (1 : ℝ) < 2) hfibre
    have hcomparison :=
      MetricCodes.Hamming.hammingFibreDimension_le_choose (N n) (K n)
    exact_mod_cast hcomparison
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowerlimit hchoose hlower hupper

theorem eventually_admissibleDegrees
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    ∀ᶠ n : ℕ in atTop,
      MetricCodes.Johnson.AdmissibleDegrees n
        (shellWeight a n)
        (supportDegree b n)
        (complementDegree g n)
        (terminalDegree u n) := by
  have ha := h.weight_pos
  have hu := h.degree_pos
  have hw := tendsto_shellWeight_ratio ha.le
  have hp := tendsto_supportDegree_ratio h.support_nonneg
  have hq := tendsto_complementDegree_ratio h.complement_nonneg
  have hL := tendsto_terminalDegree_ratio hu.le
  have hn := tendsto_dimension_ratio
  have hww := tendsto_add_degree_ratio hw hw
  have hpp := tendsto_add_degree_ratio hp hp
  have hqq := tendsto_add_degree_ratio hq hq
  have hpq := tendsto_add_degree_ratio hp hq
  have hLp := tendsto_add_degree_ratio hL hp
  have hwq := tendsto_add_degree_ratio hw hq
  have hLw := tendsto_add_degree_ratio hL hw
  have hLwq := tendsto_add_degree_ratio hLw hq
  have hnp := tendsto_add_degree_ratio hn hp
  have hweight_positive :
      ∀ᶠ n : ℕ in atTop, 0 < shellWeight a n := by
    have hgrowth : Tendsto (shellWeight a) atTop atTop := by
      change Tendsto
        (fun n : ℕ => Nat.floor (a * (n : ℝ))) atTop atTop
      exact tendsto_nat_floor_mul_atTop a ha
    exact hgrowth.eventually (eventually_gt_atTop (0 : ℕ))
  have hweight_lt := eventually_degree_lt_of_ratio hw hn
    (by linarith [h.weight_lt_half])
  have hweight_half := eventually_degree_lt_of_ratio hww hn
    (by linarith [h.weight_lt_half])
  have hsupport_half := eventually_degree_lt_of_ratio hpp hw
    (by linarith [h.support_lt_half])
  have hcomplement_half := eventually_degree_lt_of_ratio
    (tendsto_add_degree_ratio hqq hw) hn
    (by linarith [h.complement_lt_half])
  have hfirst := eventually_degree_lt_of_ratio hpq hL
    h.first_lt_degree
  have hterminal_weight := eventually_degree_lt_of_ratio hL hw
    h.degree_lt_weight
  have hterminal_left := eventually_degree_lt_of_ratio hLp hwq
    (by linarith [h.degree_lt_left])
  have hterminal_right := eventually_degree_lt_of_ratio hLwq hnp
    (by linarith [h.degree_lt_right])
  filter_upwards [hweight_positive, hweight_lt, hweight_half,
    hsupport_half, hcomplement_half, hfirst,
    hterminal_weight, hterminal_left, hterminal_right]
    with n hpos hlt hhalf hsupport hcomplement
      hfirst' hweight' hleft hright
  refine {
    weight_pos := hpos
    weight_lt := hlt
    weight_half := by omega
    support_half := by omega
    complement_half := by omega
    first_le := by omega
    last_le := ?_
  }
  unfold MetricCodes.johnsonLastDegree
  apply le_min
  · omega
  · apply le_min <;> omega

theorem tendsto_complementShellWeight_ratio
    {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        ((n - shellWeight a n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (1 - a)) := by
  simpa [shellWeight] using
    MetricCodes.Hamming.tendsto_complement_longitudinal_ratio ha ha'

theorem tendsto_logb_supportHarmonicDimension
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (MetricCodes.booleanHarmonicDimension
            (shellWeight a n) (supportDegree b n) : ℝ) /
            (n : ℝ))
      atTop (nhds (a * MetricCodes.binaryEntropy (b / a))) := by
  by_cases hbzero : b = 0
  · subst b
    simp [supportDegree, MetricCodes.Hamming.longitudinalDegree,
      MetricCodes.booleanHarmonicDimension]
  · have hb : 0 < b := lt_of_le_of_ne h.support_nonneg
      (Ne.symm hbzero)
    have hba : b < a := by
      nlinarith [h.support_lt_half, h.weight_pos]
    have hhalf :
        ∀ᶠ n : ℕ in atTop,
          2 * supportDegree b n ≤ shellWeight a n :=
      (eventually_admissibleDegrees h).mono
        (fun _ hn => hn.support_half)
    have hN : ∀ᶠ n : ℕ in atTop, shellWeight a n ≤ n := by
      apply Eventually.of_forall
      intro n
      exact MetricCodes.Hamming.longitudinalDegree_le_dimension
        (by linarith [h.weight_lt_half]) n
    exact tendsto_logb_booleanHarmonicDimension_of_ratio
      (tendsto_shellWeight_ratio h.weight_pos.le)
      (tendsto_supportDegree_ratio h.support_nonneg)
      hb hba hhalf hN

theorem tendsto_logb_complementHarmonicDimension
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (MetricCodes.booleanHarmonicDimension
            (n - shellWeight a n) (complementDegree g n) : ℝ) /
            (n : ℝ))
      atTop (nhds
        ((1 - a) * MetricCodes.binaryEntropy (g / (1 - a)))) := by
  by_cases hgzero : g = 0
  · subst g
    simp [complementDegree, MetricCodes.Hamming.longitudinalDegree,
      MetricCodes.booleanHarmonicDimension]
  · have hg : 0 < g := lt_of_le_of_ne h.complement_nonneg
      (Ne.symm hgzero)
    have hga : g < 1 - a := by
      nlinarith [h.complement_lt_half, h.weight_complement_pos]
    have hhalf :
        ∀ᶠ n : ℕ in atTop,
          2 * complementDegree g n ≤ n - shellWeight a n :=
      (eventually_admissibleDegrees h).mono
        (fun _ hn => hn.complement_half)
    have hN :
        ∀ᶠ n : ℕ in atTop, n - shellWeight a n ≤ n :=
      Eventually.of_forall (fun n => Nat.sub_le n _)
    exact tendsto_logb_booleanHarmonicDimension_of_ratio
      (tendsto_complementShellWeight_ratio
        h.weight_pos.le (by linarith [h.weight_lt_half]))
      (tendsto_complementDegree_ratio h.complement_nonneg)
      hg hga hhalf hN

theorem tendsto_logb_johnsonFibreDimension
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (MetricCodes.johnsonFibreDimension n
            (shellWeight a n)
            (supportDegree b n)
            (complementDegree g n) : ℝ) /
              (n : ℝ))
      atTop (nhds (MetricCodes.Johnson.rankPenalty a b g)) := by
  have hsupport := tendsto_logb_supportHarmonicDimension h
  have hcomplement := tendsto_logb_complementHarmonicDimension h
  have hsum := hsupport.add hcomplement
  change
    Tendsto _ atTop
      (nhds
        (a * MetricCodes.binaryEntropy (b / a) +
          (1 - a) * MetricCodes.binaryEntropy (g / (1 - a))))
  refine hsum.congr' ?_
  filter_upwards [eventually_admissibleDegrees h]
    with n hn
  have hsupportpos :
      0 < (MetricCodes.booleanHarmonicDimension
        (shellWeight a n) (supportDegree b n) : ℝ) := by
    exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos
      hn.support_half
  have hcomplementpos :
      0 < (MetricCodes.booleanHarmonicDimension
        (n - shellWeight a n) (complementDegree g n) : ℝ) := by
    exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos
      hn.complement_half
  unfold MetricCodes.johnsonFibreDimension
  push_cast
  rw [Real.logb_mul hsupportpos.ne' hcomplementpos.ne']
  ring

theorem terminalHarmonic_le_johnsonAmbientDimension
    {n w p q L : ℕ}
    (h : MetricCodes.Johnson.AdmissibleDegrees n w p q L) :
    MetricCodes.booleanHarmonicDimension n L ≤
      MetricCodes.johnsonAmbientDimension n (p + q) L := by
  unfold MetricCodes.johnsonAmbientDimension
  have hmem : L ∈ Finset.Icc (p + q) L := by
    simp [h.first_le]
  exact Finset.single_le_sum
    (s := Finset.Icc (p + q) L)
    (f := fun j => MetricCodes.booleanHarmonicDimension n j)
    (fun _ _ => Nat.zero_le _) hmem

theorem johnsonAmbientDimension_le_terminalChoose
    {n w p q L : ℕ}
    (h : MetricCodes.Johnson.AdmissibleDegrees n w p q L) :
    MetricCodes.johnsonAmbientDimension n (p + q) L ≤ n.choose L := by
  rw [MetricCodes.Johnson.ambientDimension_eq h]
  exact Nat.sub_le _ _

theorem tendsto_logb_johnsonAmbientDimension
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (MetricCodes.johnsonAmbientDimension n
            (supportDegree b n + complementDegree g n)
            (terminalDegree u n) : ℝ) /
              (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy u)) := by
  have hu := h.degree_pos
  have huhalf : u ≤ (1 : ℝ) / 2 := by
    linarith [h.degree_lt_weight, h.weight_lt_half]
  have huone : u < 1 := by linarith
  have hterminal :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2
            (MetricCodes.booleanHarmonicDimension n
              (terminalDegree u n) : ℝ) /
                (n : ℝ))
        atTop (nhds (MetricCodes.binaryEntropy u)) := by
    simpa [terminalDegree, MetricCodes.Hamming.transverseDegree,
      MetricCodes.Hamming.longitudinalDegree,
      MetricCodes.hammingFibreDimension] using
      MetricCodes.Hamming.tendsto_logb_hammingFibreDimension hu huhalf
  have hchoose :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2
            (n.choose (terminalDegree u n) : ℝ) /
              (n : ℝ))
        atTop (nhds (MetricCodes.binaryEntropy u)) := by
    simpa [terminalDegree] using
      MetricCodes.Hamming.tendsto_logb_choose_longitudinal hu huone
  have hlower :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
            (MetricCodes.booleanHarmonicDimension n
              (terminalDegree u n) : ℝ) /
                (n : ℝ) ≤
          Real.logb 2
            (MetricCodes.johnsonAmbientDimension n
              (supportDegree b n + complementDegree g n)
              (terminalDegree u n) : ℝ) /
                (n : ℝ) := by
    filter_upwards [eventually_admissibleDegrees h,
      eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have htermhalf : 2 * terminalDegree u n ≤ n := by
      have hhalf := hn.terminal_le_half
      omega
    have htermpos :
        0 < (MetricCodes.booleanHarmonicDimension n
          (terminalDegree u n) : ℝ) := by
      exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos
        htermhalf
    apply (div_le_div_iff_of_pos_right hnreal).mpr
    apply Real.logb_le_logb_of_le
      (by norm_num : (1 : ℝ) < 2) htermpos
    exact_mod_cast terminalHarmonic_le_johnsonAmbientDimension hn
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
            (MetricCodes.johnsonAmbientDimension n
              (supportDegree b n + complementDegree g n)
              (terminalDegree u n) : ℝ) /
                (n : ℝ) ≤
          Real.logb 2
            (n.choose (terminalDegree u n) : ℝ) /
              (n : ℝ) := by
    filter_upwards [eventually_admissibleDegrees h,
      eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have htermhalf : 2 * terminalDegree u n ≤ n := by
      have hhalf := hn.terminal_le_half
      omega
    have htermpos :
        0 < (MetricCodes.booleanHarmonicDimension n
          (terminalDegree u n) : ℝ) := by
      exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos
        htermhalf
    have hambientpos :
        0 < (MetricCodes.johnsonAmbientDimension n
          (supportDegree b n + complementDegree g n)
          (terminalDegree u n) : ℝ) := by
      have hle := terminalHarmonic_le_johnsonAmbientDimension hn
      exact lt_of_lt_of_le htermpos (by exact_mod_cast hle)
    apply (div_le_div_iff_of_pos_right hnreal).mpr
    apply Real.logb_le_logb_of_le
      (by norm_num : (1 : ℝ) < 2) hambientpos
    exact_mod_cast johnsonAmbientDimension_le_terminalChoose hn
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hterminal hchoose hlower hupper

def windowFibreQuotient (a b g u : ℝ) (n : ℕ) : ℝ :=
  (MetricCodes.johnsonAmbientDimension n
    (supportDegree b n + complementDegree g n)
    (terminalDegree u n) : ℝ) /
      (MetricCodes.johnsonFibreDimension n
        (shellWeight a n)
        (supportDegree b n)
        (complementDegree g n) : ℝ)

theorem eventually_windowFibreQuotient_pos
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    ∀ᶠ n : ℕ in atTop, 0 < windowFibreQuotient a b g u n := by
  filter_upwards [eventually_admissibleDegrees h] with n hn
  have htermhalf : 2 * terminalDegree u n ≤ n := by
    have hhalf := hn.terminal_le_half
    omega
  have htermpos :
      0 < (MetricCodes.booleanHarmonicDimension n
        (terminalDegree u n) : ℝ) := by
    exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos
      htermhalf
  have hambientpos :
      0 < (MetricCodes.johnsonAmbientDimension n
        (supportDegree b n + complementDegree g n)
        (terminalDegree u n) : ℝ) := by
    exact lt_of_lt_of_le htermpos
      (by exact_mod_cast terminalHarmonic_le_johnsonAmbientDimension hn)
  have hfibrepos :
      0 < (MetricCodes.johnsonFibreDimension n
        (shellWeight a n)
        (supportDegree b n)
        (complementDegree g n) : ℝ) := by
    exact_mod_cast hn.fibreDimension_pos
  exact div_pos hambientpos hfibrepos

theorem tendsto_logb_windowFibreQuotient
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2 (windowFibreQuotient a b g u n) / (n : ℝ))
      atTop
      (nhds (MetricCodes.binaryEntropy u -
        MetricCodes.Johnson.rankPenalty a b g)) := by
  have hnum := tendsto_logb_johnsonAmbientDimension h
  have hden := tendsto_logb_johnsonFibreDimension h
  have hdiff := hnum.sub hden
  refine hdiff.congr' ?_
  filter_upwards [eventually_admissibleDegrees h] with n hn
  have htermhalf : 2 * terminalDegree u n ≤ n := by
    have hhalf := hn.terminal_le_half
    omega
  have htermpos :
      0 < (MetricCodes.booleanHarmonicDimension n
        (terminalDegree u n) : ℝ) := by
    exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos
      htermhalf
  have hambientpos :
      0 < (MetricCodes.johnsonAmbientDimension n
        (supportDegree b n + complementDegree g n)
        (terminalDegree u n) : ℝ) := by
    exact lt_of_lt_of_le htermpos
      (by exact_mod_cast terminalHarmonic_le_johnsonAmbientDimension hn)
  have hfibrepos :
      0 < (MetricCodes.johnsonFibreDimension n
        (shellWeight a n)
        (supportDegree b n)
        (complementDegree g n) : ℝ) := by
    exact_mod_cast hn.fibreDimension_pos
  unfold windowFibreQuotient
  rw [Real.logb_div hambientpos.ne' hfibrepos.ne']
  ring

def bassalygoFactor (a : ℝ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n / (n.choose (shellWeight a n) : ℝ)

theorem tendsto_logb_shellChoose
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2 (n.choose (shellWeight a n) : ℝ) / (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy a)) := by
  simpa [shellWeight] using
    MetricCodes.Hamming.tendsto_logb_choose_longitudinal
      h.weight_pos (by linarith [h.weight_lt_half])

theorem tendsto_logb_bassalygoFactor
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2 (bassalygoFactor a n) / (n : ℝ))
      atTop (nhds (1 - MetricCodes.binaryEntropy a)) := by
  have hpower :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2 ((2 : ℝ) ^ n) / (n : ℝ))
        atTop (nhds (1 : ℝ)) := by
    refine tendsto_dimension_ratio.congr'
      (Eventually.of_forall fun n => ?_)
    change
      (n : ℝ) / (n : ℝ) =
        Real.logb 2 ((2 : ℝ) ^ n) / (n : ℝ)
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    simp
  have hchoose := tendsto_logb_shellChoose h
  have hdiff := hpower.sub hchoose
  refine hdiff.congr' (Eventually.of_forall fun n => ?_)
  have hw : shellWeight a n ≤ n :=
    MetricCodes.Hamming.longitudinalDegree_le_dimension
      (by linarith [h.weight_lt_half]) n
  have hchoosepos : 0 < (n.choose (shellWeight a n) : ℝ) := by
    exact_mod_cast Nat.choose_pos hw
  unfold bassalygoFactor
  change
    Real.logb 2 ((2 : ℝ) ^ n) / (n : ℝ) -
        Real.logb 2 (n.choose (shellWeight a n) : ℝ) / (n : ℝ) =
      Real.logb 2
        (((2 : ℝ) ^ n) / (n.choose (shellWeight a n) : ℝ)) /
          (n : ℝ)
  rw [Real.logb_div (by positivity) hchoosepos.ne']
  ring

def bassalygoWindowFibreQuotient
    (a b g u : ℝ) (n : ℕ) : ℝ :=
  bassalygoFactor a n * windowFibreQuotient a b g u n

theorem eventually_bassalygoWindowFibreQuotient_pos
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    ∀ᶠ n : ℕ in atTop,
      0 < bassalygoWindowFibreQuotient a b g u n := by
  filter_upwards [eventually_windowFibreQuotient_pos h]
    with n hquot
  have hw : shellWeight a n ≤ n :=
    MetricCodes.Hamming.longitudinalDegree_le_dimension
      (by linarith [h.weight_lt_half]) n
  have hchoosepos : 0 < (n.choose (shellWeight a n) : ℝ) := by
    exact_mod_cast Nat.choose_pos hw
  unfold bassalygoWindowFibreQuotient bassalygoFactor
  exact mul_pos (div_pos (by positivity) hchoosepos) hquot

theorem tendsto_logb_bassalygoWindowFibreQuotient
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (bassalygoWindowFibreQuotient a b g u n) / (n : ℝ))
      atTop (nhds (MetricCodes.Johnson.shellRate a b g u)) := by
  have hfactor := tendsto_logb_bassalygoFactor h
  have hquotient := tendsto_logb_windowFibreQuotient h
  have hsum := hfactor.add hquotient
  have hlimit :
      (1 - MetricCodes.binaryEntropy a) +
          (MetricCodes.binaryEntropy u -
            MetricCodes.Johnson.rankPenalty a b g) =
        MetricCodes.Johnson.shellRate a b g u := by
    unfold MetricCodes.Johnson.shellRate
    ring
  rw [hlimit] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_windowFibreQuotient_pos h]
    with n hquotpos
  have hw : shellWeight a n ≤ n :=
    MetricCodes.Hamming.longitudinalDegree_le_dimension
      (by linarith [h.weight_lt_half]) n
  have hchoosepos : 0 < (n.choose (shellWeight a n) : ℝ) := by
    exact_mod_cast Nat.choose_pos hw
  have hfactorpos : 0 < bassalygoFactor a n := by
    unfold bassalygoFactor
    exact div_pos (by positivity) hchoosepos
  unfold bassalygoWindowFibreQuotient
  rw [Real.logb_mul hfactorpos.ne' hquotpos.ne']
  ring

theorem tendsto_logb_const_mul_bassalygoWindowFibreQuotient
    {d a b g u C : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (hC : 0 < C) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (C * bassalygoWindowFibreQuotient a b g u n) /
            (n : ℝ))
      atTop (nhds (MetricCodes.Johnson.shellRate a b g u)) := by
  have hconstant :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.logb 2 C)
  have hquotient := tendsto_logb_bassalygoWindowFibreQuotient h
  have hsum := hconstant.add hquotient
  have hsum' :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2 C / (n : ℝ) +
            Real.logb 2
              (bassalygoWindowFibreQuotient a b g u n) /
                (n : ℝ))
        atTop (nhds (MetricCodes.Johnson.shellRate a b g u)) := by
    simpa using hsum
  refine hsum'.congr' ?_
  filter_upwards [eventually_bassalygoWindowFibreQuotient_pos h]
    with n hn
  rw [Real.logb_mul hC.ne' hn.ne']
  ring

theorem centered_diagonal_limit_algebra
    {a m sigma eta z : ℝ}
    (hz : z ≠ 0)
    (hm : 1 - m ^ 2 ≠ 0)
    (hcenter : 1 - m ^ 2 = 4 * a * (1 - a)) :
    (m * sigma * eta / (4 * z ^ 2) - (m / 2) ^ 2) /
        (a * (1 - a)) =
      m * (sigma * eta - m * z ^ 2) /
        (z ^ 2 * (1 - m ^ 2)) := by
  have hprod : a * (1 - a) ≠ 0 := by
    intro hzero
    apply hm
    rw [hcenter]
    calc
      4 * a * (1 - a) = 4 * (a * (1 - a)) := by ring
      _ = 0 := by rw [hzero]; ring
  have ha : a ≠ 0 := by
    intro hzero
    apply hprod
    simp [hzero]
  have ha' : 1 - a ≠ 0 := by
    intro hzero
    apply hprod
    rw [hzero]
    ring
  rw [hcenter]
  field_simp [hz, ha, ha']
  ; ring

theorem tendsto_threshold_ceil
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.Johnson.threshold n (shellWeight a n)
          (Nat.ceil (d * (n : ℝ))))
      atTop (nhds (MetricCodes.Johnson.asymptoticThreshold d a)) := by
  have hw := tendsto_shellWeight_ratio h.weight_pos.le
  have hc := tendsto_complementShellWeight_ratio
    h.weight_pos.le (by linarith [h.weight_lt_half])
  have hd := MetricCodes.Hamming.tendsto_ceil_distance_ratio
    h.distance_pos.le
  have hden :=
    ((tendsto_const_nhds (x := (2 : ℝ))).mul hw).mul hc
  have hdenpos : 0 < 2 * a * (1 - a) := by
    have ha := h.weight_pos
    have hc' := h.weight_complement_pos
    positivity
  have hdivision := hd.div hden hdenpos.ne'
  have hnormalized :=
    (tendsto_const_nhds (x := (1 : ℝ))).sub hdivision
  have hnormalized' :
      Tendsto
        (fun n : ℕ =>
          1 -
            (((Nat.ceil (d * (n : ℝ)) : ℕ) : ℝ) /
              (n : ℝ)) /
              (2 * ((shellWeight a n : ℝ) / (n : ℝ)) *
                (((n - shellWeight a n : ℕ) : ℝ) / (n : ℝ))))
        atTop (nhds (MetricCodes.Johnson.asymptoticThreshold d a)) := by
    simpa [MetricCodes.Johnson.asymptoticThreshold] using hnormalized
  refine hnormalized'.congr' ?_
  filter_upwards [eventually_admissibleDegrees h,
    eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hwreal : (0 : ℝ) < (shellWeight a n : ℝ) := by
    exact_mod_cast hn.weight_pos
  have hcreal :
      (0 : ℝ) < ((n - shellWeight a n : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - shellWeight a n by
      exact Nat.sub_pos_of_lt hn.weight_lt)
  unfold MetricCodes.Johnson.threshold
  field_simp [hnreal.ne', hwreal.ne', hcreal.ne']

theorem binaryRate_le_shellRate_of_eventually
    {d a b g u C : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (hC : 0 < C)
    (hbound : ∀ᶠ n : ℕ in atTop,
      (MetricCodes.Hamming.codeNumber n
        (Nat.ceil (d * (n : ℝ))) : ℝ) ≤
          C * bassalygoWindowFibreQuotient a b g u n) :
    MetricCodes.Hamming.binaryRate d ≤
      MetricCodes.Johnson.shellRate a b g u := by
  apply MetricCodes.Hamming.binaryRate_le_of_eventually
    (tendsto_logb_const_mul_bassalygoWindowFibreQuotient h hC)
  filter_upwards [hbound, eventually_gt_atTop (0 : ℕ)]
    with n hcode hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcodepositive :
      0 < (MetricCodes.Hamming.codeNumber n
        (Nat.ceil (d * (n : ℝ))) : ℝ) := by
    exact_mod_cast MetricCodes.Hamming.codeNumber_pos n
      (Nat.ceil (d * (n : ℝ)))
  apply (div_le_div_iff_of_pos_right hnreal).mpr
  exact Real.logb_le_logb_of_le
    (by norm_num : (1 : ℝ) < 2) hcodepositive hcode

end MetricCodes.Johnson.Asymptotics

end

end

section

noncomputable section

open scoped BigOperators InnerProductSpace Matrix

namespace MetricCodes.Johnson

def complementNegEquiv {n w : ℕ} (x : JohnsonSphere n w) :
    ComplementCoordinates x ≃
      {i : Fin n // i ∉ MetricCodes.wordSupport (x : BinaryWord n)} :=
  Equiv.subtypeEquivRight (fun i => by simp)

def coordinateSumEquiv {n w : ℕ} (x : JohnsonSphere n w) :
    SupportCoordinates x ⊕ ComplementCoordinates x ≃ Fin n :=
  (Equiv.sumCongr (Equiv.refl (SupportCoordinates x))
    (complementNegEquiv x)).trans
      (Equiv.sumCompl
        (fun i : Fin n => i ∈ MetricCodes.wordSupport (x : BinaryWord n)))

@[simp] theorem coordinateSumEquiv_symm_support {n w : ℕ}
    (x : JohnsonSphere n w) (i : SupportCoordinates x) :
    (coordinateSumEquiv x).symm (i : Fin n) = Sum.inl i := by
  have hi : coordinateSumEquiv x (Sum.inl i) = (i : Fin n) := rfl
  simpa only [hi] using
    (coordinateSumEquiv x).symm_apply_apply (Sum.inl i)

@[simp] theorem coordinateSumEquiv_symm_complement {n w : ℕ}
    (x : JohnsonSphere n w) (i : ComplementCoordinates x) :
    (coordinateSumEquiv x).symm (i : Fin n) = Sum.inr i := by
  have hi : coordinateSumEquiv x (Sum.inr i) = (i : Fin n) := rfl
  simpa only [hi] using
    (coordinateSumEquiv x).symm_apply_apply (Sum.inr i)

def coordinateSplitEquiv {n w : ℕ} (x : JohnsonSphere n w) :
    Finset (Fin n) ≃
      Finset (SupportCoordinates x) ×
        Finset (ComplementCoordinates x) :=
  (coordinateSumEquiv x).symm.finsetCongr.trans
    Finset.sumEquiv.toEquiv

theorem coordinateSplitEquiv_card {n w : ℕ}
    (x : JohnsonSphere n w) (S : Finset (Fin n)) :
    ((coordinateSplitEquiv x S).1).card +
      ((coordinateSplitEquiv x S).2).card = S.card := by
  change
    (((coordinateSumEquiv x).symm.finsetCongr S).toLeft).card +
      (((coordinateSumEquiv x).symm.finsetCongr S).toRight).card =
        S.card
  rw [Finset.card_toLeft_add_card_toRight]
  simp

theorem coordinateSplitEquiv_insert_support {n w : ℕ}
    (x : JohnsonSphere n w) (i : SupportCoordinates x)
    (S : Finset (Fin n)) :
    coordinateSplitEquiv x (insert (i : Fin n) S) =
      (insert i (coordinateSplitEquiv x S).1,
        (coordinateSplitEquiv x S).2) := by
  apply Prod.ext
  · change
      (((coordinateSumEquiv x).symm.finsetCongr
        (insert (i : Fin n) S)).toLeft) =
          insert i
            (((coordinateSumEquiv x).symm.finsetCongr S).toLeft)
    simp [Equiv.finsetCongr_apply]
  · change
      (((coordinateSumEquiv x).symm.finsetCongr
        (insert (i : Fin n) S)).toRight) =
          (((coordinateSumEquiv x).symm.finsetCongr S).toRight)
    simp [Equiv.finsetCongr_apply]

theorem coordinateSplitEquiv_insert_complement {n w : ℕ}
    (x : JohnsonSphere n w) (i : ComplementCoordinates x)
    (S : Finset (Fin n)) :
    coordinateSplitEquiv x (insert (i : Fin n) S) =
      ((coordinateSplitEquiv x S).1,
        insert i (coordinateSplitEquiv x S).2) := by
  apply Prod.ext
  · change
      (((coordinateSumEquiv x).symm.finsetCongr
        (insert (i : Fin n) S)).toLeft) =
          (((coordinateSumEquiv x).symm.finsetCongr S).toLeft)
    simp [Equiv.finsetCongr_apply]
  · change
      (((coordinateSumEquiv x).symm.finsetCongr
        (insert (i : Fin n) S)).toRight) =
          insert i
            (((coordinateSumEquiv x).symm.finsetCongr S).toRight)
    simp [Equiv.finsetCongr_apply]

def supportRaisedFunction {n w p : ℕ}
    (x : JohnsonSphere n w) (hp : 2 * p ≤ w)
    (a : Fin (MetricCodes.hammingFibreDimension w p)) (r : ℕ) :
    Finset (SupportCoordinates x) → ℝ :=
  fun S =>
    MetricCodes.Boolean.harmonicEmbedding p r
      (MetricCodes.Boolean.harmonicBasisFunction w p hp a)
      ((supportCoordinateEquiv x).finsetCongr S)

def complementRaisedFunction {n w q : ℕ}
    (x : JohnsonSphere n w) (hq : 2 * q ≤ n - w)
    (a : Fin (MetricCodes.hammingFibreDimension (n - w) q)) (r : ℕ) :
    Finset (ComplementCoordinates x) → ℝ :=
  fun S =>
    MetricCodes.Boolean.harmonicEmbedding q r
      (MetricCodes.Boolean.harmonicBasisFunction (n - w) q hq a)
      ((complementCoordinateEquiv x).finsetCongr S)

theorem supportRaisedFunction_eq_zero_of_card_ne {n w p : ℕ}
    (x : JohnsonSphere n w) (hp : 2 * p ≤ w)
    (a : Fin (MetricCodes.hammingFibreDimension w p)) (r : ℕ)
    (S : Finset (SupportCoordinates x))
    (hS : S.card ≠ p + r) :
    supportRaisedFunction x hp a r S = 0 := by
  unfold supportRaisedFunction
  apply
    ((MetricCodes.Boolean.harmonicBasisFunction_isHarmonic w p hp a).1
      |>.harmonicEmbedding r)
  simpa using hS

theorem complementRaisedFunction_eq_zero_of_card_ne {n w q : ℕ}
    (x : JohnsonSphere n w) (hq : 2 * q ≤ n - w)
    (a : Fin (MetricCodes.hammingFibreDimension (n - w) q)) (r : ℕ)
    (S : Finset (ComplementCoordinates x))
    (hS : S.card ≠ q + r) :
    complementRaisedFunction x hq a r S = 0 := by
  unfold complementRaisedFunction
  apply
    ((MetricCodes.Boolean.harmonicBasisFunction_isHarmonic
      (n - w) q hq a).1 |>.harmonicEmbedding r)
  simpa using hS

theorem supportRaisedFunction_pairing {n w p : ℕ}
    (x : JohnsonSphere n w) (hp : 2 * p ≤ w)
    (a b : Fin (MetricCodes.hammingFibreDimension w p)) (r s : ℕ) :
    (∑ S : Finset (SupportCoordinates x),
      supportRaisedFunction x hp a r S *
        supportRaisedFunction x hp b s S) =
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.harmonicEmbedding p r
          (MetricCodes.Boolean.harmonicBasisFunction w p hp a))
        (MetricCodes.Boolean.harmonicEmbedding p s
          (MetricCodes.Boolean.harmonicBasisFunction w p hp b)) := by
  classical
  unfold supportRaisedFunction MetricCodes.Boolean.dot
  exact (supportCoordinateEquiv x).finsetCongr.sum_comp
    (fun S : Finset (Fin w) =>
      MetricCodes.Boolean.harmonicEmbedding p r
        (MetricCodes.Boolean.harmonicBasisFunction w p hp a) S *
      MetricCodes.Boolean.harmonicEmbedding p s
        (MetricCodes.Boolean.harmonicBasisFunction w p hp b) S)

theorem complementRaisedFunction_pairing {n w q : ℕ}
    (x : JohnsonSphere n w) (hq : 2 * q ≤ n - w)
    (a b : Fin (MetricCodes.hammingFibreDimension (n - w) q))
    (r s : ℕ) :
    (∑ S : Finset (ComplementCoordinates x),
      complementRaisedFunction x hq a r S *
        complementRaisedFunction x hq b s S) =
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.harmonicEmbedding q r
          (MetricCodes.Boolean.harmonicBasisFunction (n - w) q hq a))
        (MetricCodes.Boolean.harmonicEmbedding q s
          (MetricCodes.Boolean.harmonicBasisFunction (n - w) q hq b)) := by
  classical
  unfold complementRaisedFunction MetricCodes.Boolean.dot
  exact (complementCoordinateEquiv x).finsetCongr.sum_comp
    (fun S : Finset (Fin (n - w)) =>
      MetricCodes.Boolean.harmonicEmbedding q r
        (MetricCodes.Boolean.harmonicBasisFunction (n - w) q hq a) S *
      MetricCodes.Boolean.harmonicEmbedding q s
        (MetricCodes.Boolean.harmonicBasisFunction (n - w) q hq b) S)

theorem supportRaisedFunction_orthonormal {n w p r : ℕ}
    (x : JohnsonSphere n w) (hp : 2 * p ≤ w)
    (hr : 2 * p + r ≤ w)
    (a b : Fin (MetricCodes.hammingFibreDimension w p)) :
    (∑ S : Finset (SupportCoordinates x),
      supportRaisedFunction x hp a r S *
        supportRaisedFunction x hp b r S) =
      if a = b then 1 else 0 := by
  rw [supportRaisedFunction_pairing,
    MetricCodes.Boolean.harmonicEmbedding_isometry
      (MetricCodes.Boolean.harmonicBasisFunction w p hp a)
      (MetricCodes.Boolean.harmonicBasisFunction w p hp b)
      (MetricCodes.Boolean.harmonicBasisFunction_isHarmonic w p hp b)
      r hr,
    MetricCodes.Boolean.harmonicBasisFunction_dot]

theorem complementRaisedFunction_orthonormal {n w q r : ℕ}
    (x : JohnsonSphere n w) (hq : 2 * q ≤ n - w)
    (hr : 2 * q + r ≤ n - w)
    (a b : Fin (MetricCodes.hammingFibreDimension (n - w) q)) :
    (∑ S : Finset (ComplementCoordinates x),
      complementRaisedFunction x hq a r S *
        complementRaisedFunction x hq b r S) =
      if a = b then 1 else 0 := by
  rw [complementRaisedFunction_pairing,
    MetricCodes.Boolean.harmonicEmbedding_isometry
      (MetricCodes.Boolean.harmonicBasisFunction (n - w) q hq a)
      (MetricCodes.Boolean.harmonicBasisFunction (n - w) q hq b)
      (MetricCodes.Boolean.harmonicBasisFunction_isHarmonic
        (n - w) q hq b)
      r hr,
    MetricCodes.Boolean.harmonicBasisFunction_dot]

theorem supportRaisedFunction_cross_orthogonal {n w p : ℕ}
    (x : JohnsonSphere n w) (hp : 2 * p ≤ w)
    (a b : Fin (MetricCodes.hammingFibreDimension w p))
    (r s : ℕ) (hrs : r ≠ s) :
    (∑ S : Finset (SupportCoordinates x),
      supportRaisedFunction x hp a r S *
        supportRaisedFunction x hp b s S) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro S _
  by_cases hS : S.card = p + r
  · have hother : S.card ≠ p + s := by omega
    rw [supportRaisedFunction_eq_zero_of_card_ne x hp b s S hother,
      mul_zero]
  · rw [supportRaisedFunction_eq_zero_of_card_ne x hp a r S hS,
      zero_mul]

def splitTensor {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) (r s : ℕ) :
    MetricCodes.Boolean.Function n :=
  fun S =>
    supportRaisedFunction x hp a.1 r
      (coordinateSplitEquiv x S).1 *
    complementRaisedFunction x hq a.2 s
      (coordinateSplitEquiv x S).2

theorem splitTensor_isLevel {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) (r s : ℕ) :
    MetricCodes.Boolean.IsLevel ((p + r) + (q + s))
      (splitTensor x hp hq a r s) := by
  intro S hS
  have hcard := coordinateSplitEquiv_card x S
  by_cases hsupport :
      ((coordinateSplitEquiv x S).1).card = p + r
  · have hcomplement :
        ((coordinateSplitEquiv x S).2).card ≠ q + s := by
      omega
    unfold splitTensor
    rw [complementRaisedFunction_eq_zero_of_card_ne
      x hq a.2 s (coordinateSplitEquiv x S).2 hcomplement,
      mul_zero]
  · unfold splitTensor
    rw [supportRaisedFunction_eq_zero_of_card_ne
      x hp a.1 r (coordinateSplitEquiv x S).1 hsupport,
      zero_mul]

theorem splitTensor_pairing {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a b : HarmonicFibreIndex n w p q)
    (r s r' s' : ℕ) :
    MetricCodes.Boolean.dot
      (splitTensor x hp hq a r s)
      (splitTensor x hp hq b r' s') =
      (∑ A : Finset (SupportCoordinates x),
        supportRaisedFunction x hp a.1 r A *
          supportRaisedFunction x hp b.1 r' A) *
      (∑ B : Finset (ComplementCoordinates x),
        complementRaisedFunction x hq a.2 s B *
          complementRaisedFunction x hq b.2 s' B) := by
  classical
  calc
    MetricCodes.Boolean.dot
        (splitTensor x hp hq a r s)
        (splitTensor x hp hq b r' s') =
      ∑ T : Finset (SupportCoordinates x) ×
          Finset (ComplementCoordinates x),
        (supportRaisedFunction x hp a.1 r T.1 *
          complementRaisedFunction x hq a.2 s T.2) *
        (supportRaisedFunction x hp b.1 r' T.1 *
          complementRaisedFunction x hq b.2 s' T.2) := by
      unfold MetricCodes.Boolean.dot splitTensor
      exact (coordinateSplitEquiv x).sum_comp
        (fun T : Finset (SupportCoordinates x) ×
          Finset (ComplementCoordinates x) =>
          (supportRaisedFunction x hp a.1 r T.1 *
            complementRaisedFunction x hq a.2 s T.2) *
          (supportRaisedFunction x hp b.1 r' T.1 *
            complementRaisedFunction x hq b.2 s' T.2))
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      ring

theorem splitTensor_orthonormal {n w p q r s : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (hr : 2 * p + r ≤ w) (hs : 2 * q + s ≤ n - w)
    (a b : HarmonicFibreIndex n w p q) :
    MetricCodes.Boolean.dot
      (splitTensor x hp hq a r s)
      (splitTensor x hp hq b r s) =
      if a = b then 1 else 0 := by
  rw [splitTensor_pairing,
    supportRaisedFunction_orthonormal x hp hr,
    complementRaisedFunction_orthonormal x hq hs]
  by_cases hfirst : a.1 = b.1 <;>
    by_cases hsecond : a.2 = b.2 <;>
    simp [hfirst, hsecond, Prod.ext_iff]

theorem splitTensor_cross_orthogonal {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a b : HarmonicFibreIndex n w p q)
    (r s r' s' : ℕ) (hrr' : r ≠ r') :
    MetricCodes.Boolean.dot
      (splitTensor x hp hq a r s)
      (splitTensor x hp hq b r' s') = 0 := by
  rw [splitTensor_pairing,
    supportRaisedFunction_cross_orthogonal
      x hp a.1 b.1 r r' hrr', zero_mul]

def clebschCoefficient (w N p q t : ℕ) : ℕ → ℝ
  | 0 => 1
  | r + 1 =>
      -clebschCoefficient w N p q t r *
        Real.sqrt (MetricCodes.Boolean.harmonicCoefficient N q (t - r)) /
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r + 1))

theorem clebschCoefficient_succ_mul {w N p q t r : ℕ}
    (hbound : 2 * p + (r + 1) ≤ w) :
    clebschCoefficient w N p q t (r + 1) *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) =
      -clebschCoefficient w N p q t r *
        Real.sqrt (MetricCodes.Boolean.harmonicCoefficient N q (t - r)) := by
  have hpositive :
      0 < MetricCodes.Boolean.harmonicCoefficient w p (r + 1) :=
    MetricCodes.Boolean.harmonicCoefficient_pos (Nat.succ_pos r) hbound
  have hnonzero :
      Real.sqrt
        (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) ≠ 0 :=
    (Real.sqrt_pos.mpr hpositive).ne'
  simp only [clebschCoefficient]
  field_simp [hnonzero]

def clebschNormSq (w N p q t : ℕ) : ℝ :=
  ∑ r : Fin (t + 1),
    clebschCoefficient w N p q t r.val ^ 2

theorem clebschNormSq_pos (w N p q t : ℕ) :
    0 < clebschNormSq w N p q t := by
  classical
  unfold clebschNormSq
  apply Finset.sum_pos'
  · intro r _
    exact sq_nonneg _
  · let r : Fin (t + 1) := ⟨0, by omega⟩
    refine ⟨r, Finset.mem_univ r, ?_⟩
    change 0 < clebschCoefficient w N p q t 0 ^ 2
    norm_num [clebschCoefficient]

def coupledTensor {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) (t : ℕ) :
    MetricCodes.Boolean.Function n :=
  fun S =>
    ∑ r : Fin (t + 1),
      clebschCoefficient w (n - w) p q t r.val *
        splitTensor x hp hq a r.val (t - r.val) S

theorem coupledTensor_isLevel {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) (t : ℕ) :
    MetricCodes.Boolean.IsLevel (p + q + t)
      (coupledTensor x hp hq a t) := by
  classical
  intro S hS
  unfold coupledTensor
  apply Finset.sum_eq_zero
  intro r _
  have hr : r.val ≤ t := by
    have hlt := r.isLt
    omega
  have hdegree :
      (p + r.val) + (q + (t - r.val)) = p + q + t := by
    omega
  have hzero :=
    splitTensor_isLevel x hp hq a r.val (t - r.val) S
      (by simpa [hdegree] using hS)
  rw [hzero, mul_zero]

def coupledHarmonic {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) (t : ℕ) :
    MetricCodes.Boolean.Function n :=
  (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ •
    coupledTensor x hp hq a t

theorem coupledHarmonic_isLevel {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) (t : ℕ) :
    MetricCodes.Boolean.IsLevel (p + q + t)
      (coupledHarmonic x hp hq a t) := by
  unfold coupledHarmonic
  exact (coupledTensor_isLevel x hp hq a t).smul _

theorem dot_fintype_weighted_sum
    {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℝ) (d : κ → ℝ)
    (f : ι → MetricCodes.Boolean.Function n)
    (g : κ → MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.dot
      (fun S => ∑ i : ι, c i * f i S)
      (fun S => ∑ j : κ, d j * g j S) =
      ∑ i : ι, ∑ j : κ,
        c i * d j * MetricCodes.Boolean.dot (f i) (g j) := by
  classical
  unfold MetricCodes.Boolean.dot
  calc
    (∑ S : Finset (Fin n),
      (∑ i : ι, c i * f i S) *
        (∑ j : κ, d j * g j S)) =
      ∑ S : Finset (Fin n), ∑ i : ι, ∑ j : κ,
        (c i * f i S) * (d j * g j S) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = ∑ i : ι, ∑ j : κ, ∑ S : Finset (Fin n),
          (c i * f i S) * (d j * g j S) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ j : κ,
        c i * d j *
          (∑ S : Finset (Fin n), f i S * g j S) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring

theorem coupledTensor_dot {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + t ≤ w)
    (htcomplement : 2 * q + t ≤ n - w)
    (a b : HarmonicFibreIndex n w p q) :
    MetricCodes.Boolean.dot
      (coupledTensor x hp hq a t)
      (coupledTensor x hp hq b t) =
      clebschNormSq w (n - w) p q t *
        (if a = b then 1 else 0) := by
  classical
  let c : Fin (t + 1) → ℝ :=
    fun r => clebschCoefficient w (n - w) p q t r.val
  let f : Fin (t + 1) → MetricCodes.Boolean.Function n :=
    fun r => splitTensor x hp hq a r.val (t - r.val)
  let g : Fin (t + 1) → MetricCodes.Boolean.Function n :=
    fun r => splitTensor x hp hq b r.val (t - r.val)
  have hpair :
      MetricCodes.Boolean.dot
        (coupledTensor x hp hq a t)
        (coupledTensor x hp hq b t) =
      ∑ r : Fin (t + 1), ∑ s : Fin (t + 1),
        c r * c s * MetricCodes.Boolean.dot (f r) (g s) := by
    change
      MetricCodes.Boolean.dot
        (fun S => ∑ r : Fin (t + 1), c r * f r S)
        (fun S => ∑ s : Fin (t + 1), c s * g s S) = _
    exact dot_fintype_weighted_sum c c f g
  rw [hpair]
  calc
    (∑ r : Fin (t + 1), ∑ s : Fin (t + 1),
      c r * c s * MetricCodes.Boolean.dot (f r) (g s)) =
      ∑ r : Fin (t + 1),
        c r ^ 2 * (if a = b then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro r _
      calc
        (∑ s : Fin (t + 1),
          c r * c s * MetricCodes.Boolean.dot (f r) (g s)) =
          ∑ s : Fin (t + 1),
            if s = r then
              c r ^ 2 * (if a = b then 1 else 0)
            else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          by_cases hsr : s = r
          · subst s
            have hr : r.val ≤ t := by
              have hlt := r.isLt
              omega
            have hsupport : 2 * p + r.val ≤ w := by
              omega
            have hcomplement :
                2 * q + (t - r.val) ≤ n - w := by
              omega
            change
              c r * c r *
                  MetricCodes.Boolean.dot
                    (splitTensor x hp hq a r.val (t - r.val))
                    (splitTensor x hp hq b r.val (t - r.val)) =
                if r = r then
                  c r ^ 2 * (if a = b then 1 else 0)
                else 0
            rw [splitTensor_orthonormal x hp hq
              hsupport hcomplement a b]
            simp [pow_two]
          · have hrs : r.val ≠ s.val := by
              intro heq
              exact hsr (Fin.ext heq.symm)
            change
              c r * c s *
                  MetricCodes.Boolean.dot
                    (splitTensor x hp hq a r.val (t - r.val))
                    (splitTensor x hp hq b s.val (t - s.val)) =
                if s = r then
                  c r ^ 2 * (if a = b then 1 else 0)
                else 0
            rw [splitTensor_cross_orthogonal x hp hq
              a b r.val (t - r.val) s.val (t - s.val) hrs]
            simp [hsr]
        _ = c r ^ 2 * (if a = b then 1 else 0) := by
          simp
    _ = clebschNormSq w (n - w) p q t *
        (if a = b then 1 else 0) := by
      simp only [clebschNormSq, c, Finset.sum_mul]

theorem coupledHarmonic_dot {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + t ≤ w)
    (htcomplement : 2 * q + t ≤ n - w)
    (a b : HarmonicFibreIndex n w p q) :
    MetricCodes.Boolean.dot
      (coupledHarmonic x hp hq a t)
      (coupledHarmonic x hp hq b t) =
      if a = b then 1 else 0 := by
  have hpositive := clebschNormSq_pos w (n - w) p q t
  have hsquare := Real.sq_sqrt hpositive.le
  have hnonzero :
      Real.sqrt (clebschNormSq w (n - w) p q t) ≠ 0 :=
    (Real.sqrt_pos.mpr hpositive).ne'
  unfold coupledHarmonic
  rw [MetricCodes.Boolean.dot_smul_left,
    MetricCodes.Boolean.dot_smul_right,
    coupledTensor_dot x hp hq htsupport htcomplement a b]
  by_cases hab : a = b
  · simp only [hab, ↓reduceIte]
    field_simp [hnonzero]
    exact hsquare.symm
  · simp [hab]

@[simp] theorem coordinateSplitEquiv_mem_support {n w : ℕ}
    (x : JohnsonSphere n w) (i : SupportCoordinates x)
    (S : Finset (Fin n)) :
    i ∈ (coordinateSplitEquiv x S).1 ↔ (i : Fin n) ∈ S := by
  change
    i ∈ (((coordinateSumEquiv x).symm.finsetCongr S).toLeft) ↔
      (i : Fin n) ∈ S
  rw [Finset.mem_toLeft]
  change
    Sum.inl i ∈ S.map (coordinateSumEquiv x).symm.toEmbedding ↔
      (i : Fin n) ∈ S
  rw [Finset.mem_map_equiv]
  change (i : Fin n) ∈ S ↔ (i : Fin n) ∈ S
  rfl

@[simp] theorem coordinateSplitEquiv_mem_complement {n w : ℕ}
    (x : JohnsonSphere n w) (i : ComplementCoordinates x)
    (S : Finset (Fin n)) :
    i ∈ (coordinateSplitEquiv x S).2 ↔ (i : Fin n) ∈ S := by
  change
    i ∈ (((coordinateSumEquiv x).symm.finsetCongr S).toRight) ↔
      (i : Fin n) ∈ S
  rw [Finset.mem_toRight]
  change
    Sum.inr i ∈ S.map (coordinateSumEquiv x).symm.toEmbedding ↔
      (i : Fin n) ∈ S
  rw [Finset.mem_map_equiv]
  change (i : Fin n) ∈ S ↔ (i : Fin n) ∈ S
  rfl

def coordinateLower {α : Type*} [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ) (S : Finset α) : ℝ :=
  ∑ i : α, if i ∈ S then 0 else f (insert i S)

theorem coordinateLower_reindex
    {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (e : α ≃ Fin m) (f : MetricCodes.Boolean.Function m)
    (S : Finset α) :
    coordinateLower
        (fun T : Finset α => f (e.finsetCongr T)) S =
      MetricCodes.Boolean.lower f (e.finsetCongr S) := by
  classical
  unfold coordinateLower MetricCodes.Boolean.lower MetricCodes.Boolean.lowerAt
  calc
    (∑ i : α,
      if i ∈ S then 0 else f (e.finsetCongr (insert i S))) =
      ∑ i : α,
        if e i ∈ e.finsetCongr S then 0
        else f (insert (e i) (e.finsetCongr S)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [Equiv.finsetCongr_apply]
    _ = ∑ i : Fin m,
        if i ∈ e.finsetCongr S then 0
        else f (insert i (e.finsetCongr S)) := by
      exact e.sum_comp (fun i : Fin m =>
        if i ∈ e.finsetCongr S then 0
        else f (insert i (e.finsetCongr S)))

theorem supportRaisedFunction_lower {n w p r : ℕ}
    (x : JohnsonSphere n w) (hp : 2 * p ≤ w)
    (hbound : 2 * p + (r + 1) ≤ w)
    (a : Fin (MetricCodes.hammingFibreDimension w p))
    (S : Finset (SupportCoordinates x)) :
    coordinateLower (supportRaisedFunction x hp a (r + 1)) S =
      Real.sqrt (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) *
        supportRaisedFunction x hp a r S := by
  unfold supportRaisedFunction
  rw [coordinateLower_reindex]
  rw [MetricCodes.Boolean.lower_harmonicEmbedding
    (MetricCodes.Boolean.harmonicBasisFunction w p hp a)
    (MetricCodes.Boolean.harmonicBasisFunction_isHarmonic w p hp a)
    r hbound]
  rfl

theorem complementRaisedFunction_lower {n w q r : ℕ}
    (x : JohnsonSphere n w) (hq : 2 * q ≤ n - w)
    (hbound : 2 * q + (r + 1) ≤ n - w)
    (a : Fin (MetricCodes.hammingFibreDimension (n - w) q))
    (S : Finset (ComplementCoordinates x)) :
    coordinateLower (complementRaisedFunction x hq a (r + 1)) S =
      Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient (n - w) q (r + 1)) *
        complementRaisedFunction x hq a r S := by
  unfold complementRaisedFunction
  rw [coordinateLower_reindex]
  rw [MetricCodes.Boolean.lower_harmonicEmbedding
    (MetricCodes.Boolean.harmonicBasisFunction (n - w) q hq a)
    (MetricCodes.Boolean.harmonicBasisFunction_isHarmonic
      (n - w) q hq a)
    r hbound]
  rfl

theorem supportRaisedFunction_lower_zero {n w p : ℕ}
    (x : JohnsonSphere n w) (hp : 2 * p ≤ w)
    (a : Fin (MetricCodes.hammingFibreDimension w p))
    (S : Finset (SupportCoordinates x)) :
    coordinateLower (supportRaisedFunction x hp a 0) S = 0 := by
  unfold supportRaisedFunction
  rw [coordinateLower_reindex]
  simpa [MetricCodes.Boolean.harmonicEmbedding, MetricCodes.Boolean.raised] using
    (MetricCodes.Boolean.harmonicBasisFunction_isHarmonic w p hp a).2
      ((supportCoordinateEquiv x).finsetCongr S)

theorem complementRaisedFunction_lower_zero {n w q : ℕ}
    (x : JohnsonSphere n w) (hq : 2 * q ≤ n - w)
    (a : Fin (MetricCodes.hammingFibreDimension (n - w) q))
    (S : Finset (ComplementCoordinates x)) :
    coordinateLower (complementRaisedFunction x hq a 0) S = 0 := by
  unfold complementRaisedFunction
  rw [coordinateLower_reindex]
  simpa [MetricCodes.Boolean.harmonicEmbedding, MetricCodes.Boolean.raised] using
    (MetricCodes.Boolean.harmonicBasisFunction_isHarmonic
      (n - w) q hq a).2
      ((complementCoordinateEquiv x).finsetCongr S)

theorem lower_splitTensor {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) (r s : ℕ)
    (S : Finset (Fin n)) :
    MetricCodes.Boolean.lower (splitTensor x hp hq a r s) S =
      coordinateLower (supportRaisedFunction x hp a.1 r)
          (coordinateSplitEquiv x S).1 *
        complementRaisedFunction x hq a.2 s
          (coordinateSplitEquiv x S).2 +
      supportRaisedFunction x hp a.1 r
          (coordinateSplitEquiv x S).1 *
        coordinateLower (complementRaisedFunction x hq a.2 s)
          (coordinateSplitEquiv x S).2 := by
  classical
  calc
    MetricCodes.Boolean.lower (splitTensor x hp hq a r s) S =
      ∑ i : SupportCoordinates x ⊕ ComplementCoordinates x,
        if coordinateSumEquiv x i ∈ S then 0
        else splitTensor x hp hq a r s
          (insert (coordinateSumEquiv x i) S) := by
      unfold MetricCodes.Boolean.lower MetricCodes.Boolean.lowerAt
      symm
      exact (coordinateSumEquiv x).sum_comp
        (fun i : Fin n =>
          if i ∈ S then 0
          else splitTensor x hp hq a r s (insert i S))
    _ =
      (∑ i : SupportCoordinates x,
        if (i : Fin n) ∈ S then 0
        else splitTensor x hp hq a r s (insert (i : Fin n) S)) +
      (∑ i : ComplementCoordinates x,
        if (i : Fin n) ∈ S then 0
        else splitTensor x hp hq a r s (insert (i : Fin n) S)) := by
      rw [Fintype.sum_sum_type]
      simp [coordinateSumEquiv, complementNegEquiv]
    _ = _ := by
      congr 1
      · calc
          (∑ i : SupportCoordinates x,
            if (i : Fin n) ∈ S then 0
            else splitTensor x hp hq a r s
              (insert (i : Fin n) S)) =
            ∑ i : SupportCoordinates x,
              (if i ∈ (coordinateSplitEquiv x S).1 then 0
                else supportRaisedFunction x hp a.1 r
                  (insert i (coordinateSplitEquiv x S).1)) *
              complementRaisedFunction x hq a.2 s
                (coordinateSplitEquiv x S).2 := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : (i : Fin n) ∈ S
            · have hi' : i ∈ (coordinateSplitEquiv x S).1 :=
                (coordinateSplitEquiv_mem_support x i S).mpr hi
              simp [hi, hi']
            · have hi' : i ∉ (coordinateSplitEquiv x S).1 := by
                intro hmem
                exact hi
                  ((coordinateSplitEquiv_mem_support x i S).mp hmem)
              simp [hi, hi', splitTensor,
                coordinateSplitEquiv_insert_support]
          _ = _ := by
            unfold coordinateLower
            rw [Finset.sum_mul]
      · calc
          (∑ i : ComplementCoordinates x,
            if (i : Fin n) ∈ S then 0
            else splitTensor x hp hq a r s
              (insert (i : Fin n) S)) =
            ∑ i : ComplementCoordinates x,
              supportRaisedFunction x hp a.1 r
                (coordinateSplitEquiv x S).1 *
              (if i ∈ (coordinateSplitEquiv x S).2 then 0
                else complementRaisedFunction x hq a.2 s
                  (insert i (coordinateSplitEquiv x S).2)) := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : (i : Fin n) ∈ S
            · have hi' : i ∈ (coordinateSplitEquiv x S).2 :=
                (coordinateSplitEquiv_mem_complement x i S).mpr hi
              simp [hi, hi']
            · have hi' : i ∉ (coordinateSplitEquiv x S).2 := by
                intro hmem
                exact hi
                  ((coordinateSplitEquiv_mem_complement x i S).mp hmem)
              simp [hi, hi', splitTensor,
                coordinateSplitEquiv_insert_complement]
          _ = _ := by
            unfold coordinateLower
            rw [Finset.mul_sum]

theorem lower_fintype_weighted_sum
    {n : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (f : ι → MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.lower
      (fun S => ∑ i : ι, c i * f i S) =
      fun S => ∑ i : ι, c i * MetricCodes.Boolean.lower (f i) S := by
  classical
  funext S
  unfold MetricCodes.Boolean.lower MetricCodes.Boolean.lowerAt
  calc
    (∑ j : Fin n,
      if j ∈ S then 0
      else ∑ i : ι, c i * f i (insert j S)) =
      ∑ j : Fin n, ∑ i : ι,
        c i * (if j ∈ S then 0 else f i (insert j S)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ S <;> simp [hj]
    _ = ∑ i : ι, ∑ j : Fin n,
        c i * (if j ∈ S then 0 else f i (insert j S)) := by
      rw [Finset.sum_comm]
    _ = ∑ i : ι,
        c i * (∑ j : Fin n,
          if j ∈ S then 0 else f i (insert j S)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]

theorem coupledTensor_lower_eq_zero {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + t ≤ w)
    (htcomplement : 2 * q + t ≤ n - w)
    (a : HarmonicFibreIndex n w p q) :
    MetricCodes.Boolean.lower (coupledTensor x hp hq a t) = 0 := by
  classical
  funext S
  let A : Finset (SupportCoordinates x) :=
    (coordinateSplitEquiv x S).1
  let B : Finset (ComplementCoordinates x) :=
    (coordinateSplitEquiv x S).2
  have hsupport :
      (∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q t r.val *
          (coordinateLower
              (supportRaisedFunction x hp a.1 r.val) A *
            complementRaisedFunction x hq a.2
              (t - r.val) B)) =
        ∑ r : Fin t,
          clebschCoefficient w (n - w) p q t (r.val + 1) *
            Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient w p
                (r.val + 1)) *
            splitTensor x hp hq a r.val
              (t - (r.val + 1)) S := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.sub_zero,
      supportRaisedFunction_lower_zero, zero_mul, mul_zero,
      zero_add, Fin.val_succ]
    apply Finset.sum_congr rfl
    intro r _
    have hr : r.val < t := r.isLt
    have hbound : 2 * p + (r.val + 1) ≤ w := by
      omega
    rw [supportRaisedFunction_lower x hp hbound a.1 A]
    change
      clebschCoefficient w (n - w) p q t (r.val + 1) *
        (Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
            supportRaisedFunction x hp a.1 r.val A *
          complementRaisedFunction x hq a.2
            (t - (r.val + 1)) B) =
      clebschCoefficient w (n - w) p q t (r.val + 1) *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
        splitTensor x hp hq a r.val
          (t - (r.val + 1)) S
    change
      clebschCoefficient w (n - w) p q t (r.val + 1) *
        (Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
            supportRaisedFunction x hp a.1 r.val A *
          complementRaisedFunction x hq a.2
            (t - (r.val + 1)) B) =
      clebschCoefficient w (n - w) p q t (r.val + 1) *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
        (supportRaisedFunction x hp a.1 r.val A *
          complementRaisedFunction x hq a.2
            (t - (r.val + 1)) B)
    ring
  have hcomplement :
      (∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q t r.val *
          (supportRaisedFunction x hp a.1 r.val A *
            coordinateLower
              (complementRaisedFunction x hq a.2
                (t - r.val)) B)) =
        ∑ r : Fin t,
          clebschCoefficient w (n - w) p q t r.val *
            Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient (n - w) q
                (t - r.val)) *
            splitTensor x hp hq a r.val
              (t - (r.val + 1)) S := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.sub_self,
      complementRaisedFunction_lower_zero, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro r _
    have hr : r.val < t := r.isLt
    have hresidual :
        t - r.val = (t - (r.val + 1)) + 1 := by
      omega
    have hbound :
        2 * q + ((t - (r.val + 1)) + 1) ≤ n - w := by
      omega
    rw [hresidual,
      complementRaisedFunction_lower x hq hbound a.2 B]
    change
      clebschCoefficient w (n - w) p q t r.val *
        (supportRaisedFunction x hp a.1 r.val A *
          (Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient (n - w) q
                ((t - (r.val + 1)) + 1)) *
            complementRaisedFunction x hq a.2
              (t - (r.val + 1)) B)) =
      clebschCoefficient w (n - w) p q t r.val *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient (n - w) q
            ((t - (r.val + 1)) + 1)) *
        (supportRaisedFunction x hp a.1 r.val A *
          complementRaisedFunction x hq a.2
            (t - (r.val + 1)) B)
    ring
  calc
    MetricCodes.Boolean.lower (coupledTensor x hp hq a t) S =
      ∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q t r.val *
          MetricCodes.Boolean.lower
            (splitTensor x hp hq a r.val (t - r.val)) S := by
      change
        MetricCodes.Boolean.lower
          (fun T : Finset (Fin n) =>
            ∑ r : Fin (t + 1),
              clebschCoefficient w (n - w) p q t r.val *
                splitTensor x hp hq a r.val (t - r.val) T) S =
          ∑ r : Fin (t + 1),
            clebschCoefficient w (n - w) p q t r.val *
              MetricCodes.Boolean.lower
                (splitTensor x hp hq a r.val (t - r.val)) S
      exact congrFun
        (lower_fintype_weighted_sum
          (fun r : Fin (t + 1) =>
            clebschCoefficient w (n - w) p q t r.val)
          (fun r : Fin (t + 1) =>
            splitTensor x hp hq a r.val (t - r.val))) S
    _ =
      (∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q t r.val *
          (coordinateLower
              (supportRaisedFunction x hp a.1 r.val) A *
            complementRaisedFunction x hq a.2
              (t - r.val) B)) +
      (∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q t r.val *
          (supportRaisedFunction x hp a.1 r.val A *
            coordinateLower
              (complementRaisedFunction x hq a.2
                (t - r.val)) B)) := by
      simp_rw [lower_splitTensor]
      change
        (∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val *
            (coordinateLower
                (supportRaisedFunction x hp a.1 r.val) A *
              complementRaisedFunction x hq a.2
                (t - r.val) B +
              supportRaisedFunction x hp a.1 r.val A *
                coordinateLower
                  (complementRaisedFunction x hq a.2
                    (t - r.val)) B)) = _
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    _ =
      (∑ r : Fin t,
        clebschCoefficient w (n - w) p q t (r.val + 1) *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
          splitTensor x hp hq a r.val
            (t - (r.val + 1)) S) +
      (∑ r : Fin t,
        clebschCoefficient w (n - w) p q t r.val *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient (n - w) q
              (t - r.val)) *
          splitTensor x hp hq a r.val
            (t - (r.val + 1)) S) := by
      rw [hsupport, hcomplement]
    _ =
      ∑ r : Fin t,
        (clebschCoefficient w (n - w) p q t (r.val + 1) *
            Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) +
          clebschCoefficient w (n - w) p q t r.val *
            Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient (n - w) q
                (t - r.val))) *
          splitTensor x hp hq a r.val
            (t - (r.val + 1)) S := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro r _
      have hbound : 2 * p + (r.val + 1) ≤ w := by
        have hr := r.isLt
        omega
      rw [clebschCoefficient_succ_mul hbound]
      ring

theorem coupledHarmonic_isHarmonic {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + t ≤ w)
    (htcomplement : 2 * q + t ≤ n - w)
    (a : HarmonicFibreIndex n w p q) :
    MetricCodes.Boolean.IsHarmonic (p + q + t)
      (coupledHarmonic x hp hq a t) := by
  refine ⟨coupledHarmonic_isLevel x hp hq a t, ?_⟩
  intro S
  unfold coupledHarmonic
  rw [MetricCodes.Boolean.lower_smul,
    coupledTensor_lower_eq_zero x hp hq
      htsupport htcomplement a]
  simp

theorem AdmissibleDegrees.supportResidual_bound
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (i : Index p q L) :
    2 * p + i.val ≤ w := by
  have hi : p + q + i.val ≤ L := by
    have hfirst := h.first_le
    have hival := i.isLt
    omega
  have hleft :
      MetricCodes.johnsonLastDegree n w p q ≤ w - p + q := by
    unfold MetricCodes.johnsonLastDegree
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hbound := (hi.trans h.last_le).trans hleft
  have hp := h.support_half
  omega

theorem AdmissibleDegrees.complementResidual_bound
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (i : Index p q L) :
    2 * q + i.val ≤ n - w := by
  have hi : p + q + i.val ≤ L := by
    have hfirst := h.first_le
    have hival := i.isLt
    omega
  have hright :
      MetricCodes.johnsonLastDegree n w p q ≤ n - w + p - q := by
    unfold MetricCodes.johnsonLastDegree
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hbound := (hi.trans h.last_le).trans hright
  have hq := h.complement_half
  omega

theorem AdmissibleDegrees.window_degree_le_weight
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (i : Index p q L) :
    p + q + i.val ≤ w := by
  have hival := i.isLt
  have hfirst := h.first_le
  have hterminal := h.terminal_le_weight
  omega

def globalHarmonicVector {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) :
    MetricCodes.Boolean.harmonicEuclideanLayer n j :=
  ⟨WithLp.toLp 2 (MetricCodes.Boolean.layerRestrict j f), by
    change
      WithLp.toLp 2 (MetricCodes.Boolean.layerRestrict j f) ∈
        (MetricCodes.Boolean.harmonicLayer n j).map
          (WithLp.linearEquiv 2 ℝ
            (MetricCodes.Boolean.LayerFunction n j)).symm.toLinearMap
    apply Submodule.mem_map.mpr
    refine ⟨MetricCodes.Boolean.layerRestrict j f, ?_, rfl⟩
    apply (MetricCodes.Boolean.mem_harmonicLayer_iff _).mpr
    rw [MetricCodes.Boolean.layerExtend_layerRestrict_of_level f hf.1]
    exact hf⟩

theorem globalHarmonicVector_inner {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hg : MetricCodes.Boolean.IsHarmonic j g) :
    @inner ℝ (MetricCodes.Boolean.harmonicEuclideanLayer n j) _
      (globalHarmonicVector f hf)
      (globalHarmonicVector g hg) =
        MetricCodes.Boolean.dot f g := by
  change
    @inner ℝ (MetricCodes.Boolean.EuclideanLayer n j) _
      (WithLp.toLp 2 (MetricCodes.Boolean.layerRestrict j f))
      (WithLp.toLp 2 (MetricCodes.Boolean.layerRestrict j g)) =
        MetricCodes.Boolean.dot f g
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  symm
  simpa [MetricCodes.Boolean.layerDot, MetricCodes.Boolean.layerRestrict]
    using MetricCodes.Boolean.dot_eq_layerDot_of_level f g hf.1 hg.1

theorem AdmissibleDegrees.window_degree_half
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (i : Index p q L) :
    2 * (p + q + i.val) ≤ n := by
  have hdegree := h.window_degree_le_weight i
  have hhalf := h.weight_half
  omega

def coupledDegreeVector {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (x : JohnsonSphere n w) (i : Index p q L)
    (a : HarmonicFibreIndex n w p q) :
    MetricCodes.Boolean.harmonicEuclideanLayer n (p + q + i.val) :=
  globalHarmonicVector
    (coupledHarmonic x h.support_half h.complement_half a i.val)
    (coupledHarmonic_isHarmonic x h.support_half h.complement_half
      (h.supportResidual_bound i)
      (h.complementResidual_bound i) a)

def coupledDegreeCoordinates {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (x : JohnsonSphere n w) (i : Index p q L)
    (a : HarmonicFibreIndex n w p q)
    (b : Fin (MetricCodes.booleanHarmonicDimension
      n (p + q + i.val))) : ℝ :=
  (MetricCodes.Boolean.harmonicOrthonormalBasis
    n (p + q + i.val) (h.window_degree_half i)).repr
      (coupledDegreeVector h x i a) b

theorem coupledDegreeCoordinates_pairing {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (x : JohnsonSphere n w) (i : Index p q L)
    (a b : HarmonicFibreIndex n w p q) :
    (∑ u : Fin (MetricCodes.booleanHarmonicDimension
      n (p + q + i.val)),
      coupledDegreeCoordinates h x i a u *
        coupledDegreeCoordinates h x i b u) =
      if a = b then 1 else 0 := by
  let e := MetricCodes.Boolean.harmonicOrthonormalBasis
    n (p + q + i.val) (h.window_degree_half i)
  let A := coupledDegreeVector h x i a
  let B := coupledDegreeVector h x i b
  calc
    (∑ u : Fin (MetricCodes.booleanHarmonicDimension
      n (p + q + i.val)),
      coupledDegreeCoordinates h x i a u *
        coupledDegreeCoordinates h x i b u) =
      @inner ℝ
        (EuclideanSpace ℝ
          (Fin (MetricCodes.hammingFibreDimension
            n (p + q + i.val)))) _
        (e.repr A) (e.repr B) := by
      change
        (∑ u : Fin (MetricCodes.hammingFibreDimension
          n (p + q + i.val)),
          e.repr A u * e.repr B u) =
        @inner ℝ
          (EuclideanSpace ℝ
            (Fin (MetricCodes.hammingFibreDimension
              n (p + q + i.val)))) _
          (e.repr A) (e.repr B)
      rw [PiLp.inner_apply]
      simp [mul_comm]
    _ = @inner ℝ
        (MetricCodes.Boolean.harmonicEuclideanLayer n
          (p + q + i.val)) _ A B :=
      e.repr.inner_map_map A B
    _ = MetricCodes.Boolean.dot
        (coupledHarmonic x h.support_half h.complement_half
          a i.val)
        (coupledHarmonic x h.support_half h.complement_half
          b i.val) := by
      exact globalHarmonicVector_inner
        (coupledHarmonic x h.support_half h.complement_half
          a i.val)
        (coupledHarmonic x h.support_half h.complement_half
          b i.val)
        (coupledHarmonic_isHarmonic x h.support_half
          h.complement_half (h.supportResidual_bound i)
          (h.complementResidual_bound i) a)
        (coupledHarmonic_isHarmonic x h.support_half
          h.complement_half (h.supportResidual_bound i)
          (h.complementResidual_bound i) b)
    _ = (if a = b then 1 else 0) :=
      coupledHarmonic_dot x h.support_half h.complement_half
        (h.supportResidual_bound i)
        (h.complementResidual_bound i) a b

def johnsonWindowFibreMatrix {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (v : Space p q L) (x : JohnsonSphere n w) :
    Matrix (ShellWindowIndex n p q L)
      (HarmonicFibreIndex n w p q) ℝ :=
  fun T a =>
    johnsonFibreAmplitude n w p q L v T.1 *
      coupledDegreeCoordinates h x T.1 a T.2

theorem johnsonWindowFibreMatrix_transpose_mul
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (v : Space p q L)
    (hv : ∀ i : Index p q L, 0 < v i)
    (x : JohnsonSphere n w) :
    (johnsonWindowFibreMatrix h v x)ᵀ *
      johnsonWindowFibreMatrix h v x = 1 := by
  classical
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.one_apply]
  change
    (∑ T : ShellWindowIndex n p q L,
      johnsonWindowFibreMatrix h v x T a *
        johnsonWindowFibreMatrix h v x T b) =
      if a = b then 1 else 0
  calc
    (∑ T : ShellWindowIndex n p q L,
      johnsonWindowFibreMatrix h v x T a *
        johnsonWindowFibreMatrix h v x T b) =
      ∑ i : Index p q L,
        johnsonFibreAmplitude n w p q L v i ^ 2 *
          (∑ u : Fin (MetricCodes.booleanHarmonicDimension
            n (p + q + i.val)),
            coupledDegreeCoordinates h x i a u *
              coupledDegreeCoordinates h x i b u) := by
      simp only [johnsonWindowFibreMatrix]
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = ∑ i : Index p q L,
        johnsonFibreAmplitude n w p q L v i ^ 2 *
          (if a = b then 1 else 0) := by
      simp_rw [coupledDegreeCoordinates_pairing h x]
    _ = (if a = b then 1 else 0) := by
      by_cases hab : a = b
      · simp [hab, johnsonFibreAmplitude_sq_sum h v hv]
      · simp [hab]

def johnsonFibreMatrix {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (v : Space p q L) (x : JohnsonSphere n w) :
    Matrix (Fin (MetricCodes.johnsonAmbientDimension n (p + q) L))
      (Fin (MetricCodes.johnsonFibreDimension n w p q)) ℝ :=
  fun i a =>
    johnsonWindowFibreMatrix h v x
      ((shellWindowIndexEquiv n p q L h.first_le).symm i)
      ((harmonicFibreIndexEquiv n w p q).symm a)

theorem johnsonFibreMatrix_transpose_mul {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (v : Space p q L)
    (hv : ∀ i : Index p q L, 0 < v i)
    (x : JohnsonSphere n w) :
    (johnsonFibreMatrix h v x)ᵀ *
      johnsonFibreMatrix h v x = 1 := by
  classical
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.one_apply]
  change
    (∑ i : Fin (MetricCodes.johnsonAmbientDimension n (p + q) L),
      johnsonWindowFibreMatrix h v x
        ((shellWindowIndexEquiv n p q L h.first_le).symm i)
        ((harmonicFibreIndexEquiv n w p q).symm a) *
      johnsonWindowFibreMatrix h v x
        ((shellWindowIndexEquiv n p q L h.first_le).symm i)
        ((harmonicFibreIndexEquiv n w p q).symm b)) =
      if a = b then 1 else 0
  calc
    (∑ i : Fin (MetricCodes.johnsonAmbientDimension n (p + q) L),
      johnsonWindowFibreMatrix h v x
        ((shellWindowIndexEquiv n p q L h.first_le).symm i)
        ((harmonicFibreIndexEquiv n w p q).symm a) *
      johnsonWindowFibreMatrix h v x
        ((shellWindowIndexEquiv n p q L h.first_le).symm i)
        ((harmonicFibreIndexEquiv n w p q).symm b)) =
      ∑ T : ShellWindowIndex n p q L,
        johnsonWindowFibreMatrix h v x T
          ((harmonicFibreIndexEquiv n w p q).symm a) *
        johnsonWindowFibreMatrix h v x T
          ((harmonicFibreIndexEquiv n w p q).symm b) :=
      (shellWindowIndexEquiv n p q L h.first_le).symm.sum_comp
        (fun T : ShellWindowIndex n p q L =>
          johnsonWindowFibreMatrix h v x T
            ((harmonicFibreIndexEquiv n w p q).symm a) *
          johnsonWindowFibreMatrix h v x T
            ((harmonicFibreIndexEquiv n w p q).symm b))
    _ = (if a = b then 1 else 0) := by
      have hmatrix := congrArg
        (fun M : Matrix (HarmonicFibreIndex n w p q)
          (HarmonicFibreIndex n w p q) ℝ =>
          M ((harmonicFibreIndexEquiv n w p q).symm a)
            ((harmonicFibreIndexEquiv n w p q).symm b))
        (johnsonWindowFibreMatrix_transpose_mul h v hv x)
      simpa [Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.one_apply] using hmatrix

def johnsonProjectionFamily {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (v : Space p q L)
    (hv : ∀ i : Index p q L, 0 < v i) :
    MetricCodes.ProjectionFamily (JohnsonSphere n w)
      (MetricCodes.johnsonAmbientDimension n (p + q) L)
      (MetricCodes.johnsonFibreDimension n w p q) where
  projection x :=
    johnsonFibreMatrix h v x *
      (johnsonFibreMatrix h v x)ᵀ
  symmetric x := by
    simp [Matrix.transpose_mul]
  idempotent x := by
    let A := johnsonFibreMatrix h v x
    change (A * Aᵀ) * (A * Aᵀ) = A * Aᵀ
    calc
      (A * Aᵀ) * (A * Aᵀ) = A * ((Aᵀ * A) * Aᵀ) := by
        simp [Matrix.mul_assoc]
      _ = A * Aᵀ := by
        rw [johnsonFibreMatrix_transpose_mul h v hv x,
          Matrix.one_mul]
  trace_eq x := by
    rw [Matrix.trace_mul_comm,
      johnsonFibreMatrix_transpose_mul h v hv x]
    simp

def johnsonHarmonicGap (n j : ℕ) : ℝ :=
  (n : ℝ) - 2 * (j : ℝ)

theorem johnsonHarmonicGap_pos {n j : ℕ}
    (hj : 2 * j < n) :
    0 < johnsonHarmonicGap n j := by
  have hj' : (2 : ℝ) * (j : ℝ) < (n : ℝ) := by
    exact_mod_cast hj
  unfold johnsonHarmonicGap
  linarith

def johnsonMiddleScale (n j : ℕ) : ℝ :=
  (j : ℝ) * johnsonHarmonicGap n j *
      ((n : ℝ) - (j : ℝ) + 1) /
    ((n : ℝ) * (johnsonHarmonicGap n j + 2))

def johnsonUpperScale (n j : ℕ) : ℝ :=
  (johnsonHarmonicGap n j - 1) *
      ((n : ℝ) - (j : ℝ) + 1) /
    (johnsonHarmonicGap n j + 1)

theorem johnsonMiddleScale_pos {n j : ℕ}
    (hj : 0 < j) (hhalf : 2 * j < n) :
    0 < johnsonMiddleScale n j := by
  have hj' : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hn : 0 < n := by omega
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hgap := johnsonHarmonicGap_pos hhalf
  have hlast : 0 < (n : ℝ) - (j : ℝ) + 1 := by
    have hcast : (j : ℝ) < (n : ℝ) := by
      exact_mod_cast (show j < n by omega)
    linarith
  unfold johnsonMiddleScale
  positivity

theorem johnsonUpperScale_pos {n j : ℕ}
    (hhalf : 2 * (j + 1) ≤ n) :
    0 < johnsonUpperScale n j := by
  have hcast :
      (2 : ℝ) * ((j : ℝ) + 1) ≤ (n : ℝ) := by
    exact_mod_cast hhalf
  have hgap : 1 < johnsonHarmonicGap n j := by
    unfold johnsonHarmonicGap
    linarith
  have hlast : 0 < (n : ℝ) - (j : ℝ) + 1 := by
    linarith
  unfold johnsonUpperScale
  positivity

theorem johnsonLowerAt_commutes {n : ℕ}
    (f : MetricCodes.Boolean.Function n) (a : Fin n) :
    MetricCodes.Boolean.lower (MetricCodes.Boolean.lowerAt a f) =
      MetricCodes.Boolean.lowerAt a (MetricCodes.Boolean.lower f) := by
  classical
  funext S
  by_cases ha : a ∈ S
  · simp [MetricCodes.Boolean.lower, MetricCodes.Boolean.lowerAt, ha]
  · simp only [MetricCodes.Boolean.lower, MetricCodes.Boolean.lowerAt,
      ha, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : b ∈ S
    · simp [hb]
    · by_cases hba : b = a
      · subst b
        simp [ha]
      · simp [ha, hb, hba, Ne.symm hba, Finset.insert_comm]

theorem johnsonLowerAt_harmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (j + 1) f)
    (a : Fin n) :
    MetricCodes.Boolean.IsHarmonic j (MetricCodes.Boolean.lowerAt a f) := by
  refine ⟨hf.1.lowerAt a, ?_⟩
  have hzero : MetricCodes.Boolean.lower f = 0 := funext hf.2
  intro S
  rw [johnsonLowerAt_commutes f a, hzero]
  simp [MetricCodes.Boolean.lowerAt]

theorem johnsonLowerRaiseAt_commutator {n : ℕ}
    (f : MetricCodes.Boolean.Function n) (a : Fin n)
    (S : Finset (Fin n)) :
    MetricCodes.Boolean.lower (MetricCodes.Boolean.raiseAt a f) S -
        MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lower f) S =
      f S - 2 *
        MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f) S := by
  classical
  calc
    MetricCodes.Boolean.lower (MetricCodes.Boolean.raiseAt a f) S -
        MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lower f) S =
      ∑ b : Fin n,
        (MetricCodes.Boolean.lowerAt b (MetricCodes.Boolean.raiseAt a f) S -
          MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt b f) S) := by
      change
        (∑ b : Fin n,
          MetricCodes.Boolean.lowerAt b (MetricCodes.Boolean.raiseAt a f) S) -
          MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lower f) S = _
      rw [MetricCodes.Boolean.raiseAt_lower, ← Finset.sum_sub_distrib]
    _ = MetricCodes.Boolean.lowerAt a (MetricCodes.Boolean.raiseAt a f) S -
          MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f) S := by
      apply Finset.sum_eq_single a
      · intro b _ hba
        rw [MetricCodes.Boolean.lowerAt_raiseAt_of_ne f b a hba S]
        exact sub_self _
      · simp
    _ = f S - 2 *
          MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f) S := by
      rw [MetricCodes.Boolean.lowerAt_raiseAt_self,
        MetricCodes.Boolean.raiseAt_lowerAt_self]
      by_cases ha : a ∈ S <;> simp [ha] ; ring

theorem johnsonLowerAt_lowerAt_self {n : ℕ}
    (f : MetricCodes.Boolean.Function n) (a : Fin n) :
    MetricCodes.Boolean.lowerAt a (MetricCodes.Boolean.lowerAt a f) = 0 := by
  classical
  funext S
  by_cases ha : a ∈ S <;>
    simp [MetricCodes.Boolean.lowerAt, ha]

theorem johnsonLowerRaiseAtLowerAt_of_harmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (a : Fin n) :
    MetricCodes.Boolean.lower
      (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f)) =
        MetricCodes.Boolean.lowerAt a f := by
  classical
  have hzero : MetricCodes.Boolean.lower f = 0 := funext hf.2
  have hlow :
      MetricCodes.Boolean.lower (MetricCodes.Boolean.lowerAt a f) = 0 := by
    rw [johnsonLowerAt_commutes f a, hzero]
    funext S
    simp [MetricCodes.Boolean.lowerAt]
  have hdouble := johnsonLowerAt_lowerAt_self f a
  funext S
  have hcomm := johnsonLowerRaiseAt_commutator
    (MetricCodes.Boolean.lowerAt a f) a S
  rw [hlow, hdouble] at hcomm
  simpa [MetricCodes.Boolean.raiseAt] using hcomm

theorem johnsonBooleanLower_sub {n : ℕ}
    (f g : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.lower (f - g) =
      MetricCodes.Boolean.lower f - MetricCodes.Boolean.lower g := by
  change
    MetricCodes.Boolean.lowerLinear n (f - g) =
      MetricCodes.Boolean.lowerLinear n f -
        MetricCodes.Boolean.lowerLinear n g
  exact map_sub (MetricCodes.Boolean.lowerLinear n) f g

def johnsonMiddleRaw {n : ℕ} (j : ℕ)
    (a : Fin n) (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.Function n :=
  MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f) -
      (johnsonHarmonicGap n j + 2)⁻¹ •
        MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f) -
      ((j : ℝ) / (n : ℝ)) • f

theorem johnsonMiddleRaw_isLevel {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hj : 0 < j) (a : Fin n) :
    MetricCodes.Boolean.IsLevel j (johnsonMiddleRaw j a f) := by
  cases j with
  | zero => omega
  | succ k =>
      have hdown :
          MetricCodes.Boolean.IsLevel k (MetricCodes.Boolean.lowerAt a f) :=
        hf.1.lowerAt a
      have hmembership :
          MetricCodes.Boolean.IsLevel (k + 1)
            (MetricCodes.Boolean.raiseAt a
              (MetricCodes.Boolean.lowerAt a f)) :=
        hdown.raiseAt a
      have hraise :
          MetricCodes.Boolean.IsLevel (k + 1)
            (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f)) :=
        hdown.raise
      intro S hS
      simp only [johnsonMiddleRaw, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [hmembership S hS, hraise S hS, hf.1 S hS]
      ring

theorem johnsonMiddleRaw_isHarmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hj : 0 < j) (hhalf : 2 * j < n) (a : Fin n) :
    MetricCodes.Boolean.IsHarmonic j (johnsonMiddleRaw j a f) := by
  refine ⟨johnsonMiddleRaw_isLevel f hf hj a, ?_⟩
  cases j with
  | zero => omega
  | succ k =>
      have hlow := johnsonLowerAt_harmonic f hf a
      have hzero : MetricCodes.Boolean.lower f = 0 := funext hf.2
      have hmembership :=
        johnsonLowerRaiseAtLowerAt_of_harmonic f hf a
      have hraise :
          MetricCodes.Boolean.lower
              (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f)) =
            (johnsonHarmonicGap n (k + 1) + 2) •
              MetricCodes.Boolean.lowerAt a f := by
        funext S
        rw [MetricCodes.Boolean.lower_raise_of_harmonic
          (MetricCodes.Boolean.lowerAt a f) hlow]
        change
          ((n : ℝ) - 2 * (k : ℝ)) *
              MetricCodes.Boolean.lowerAt a f S =
            (johnsonHarmonicGap n (k + 1) + 2) *
              MetricCodes.Boolean.lowerAt a f S
        unfold johnsonHarmonicGap
        push_cast
        ring
      have hden : johnsonHarmonicGap n (k + 1) + 2 ≠ 0 := by
        have hgap := johnsonHarmonicGap_pos hhalf
        linarith
      intro S
      unfold johnsonMiddleRaw
      rw [johnsonBooleanLower_sub,
        johnsonBooleanLower_sub,
        MetricCodes.Boolean.lower_smul,
        MetricCodes.Boolean.lower_smul,
        hmembership, hraise, hzero]
      simp only [Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, Pi.zero_apply, mul_zero, sub_zero]
      field_simp [hden] ; simp

def johnsonUpperRaw {n : ℕ} (j : ℕ)
    (a : Fin n) (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.Function n :=
  MetricCodes.Boolean.raiseAt a f -
      (johnsonHarmonicGap n j)⁻¹ • MetricCodes.Boolean.raise f +
      (2 / johnsonHarmonicGap n j) •
        MetricCodes.Boolean.raise
          (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f)) -
      (johnsonHarmonicGap n j *
        (johnsonHarmonicGap n j + 1))⁻¹ •
        MetricCodes.Boolean.raise
          (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f))

theorem johnsonLowerAt_eq_zero_of_level_zero {n : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsLevel 0 f)
    (a : Fin n) :
    MetricCodes.Boolean.lowerAt a f = 0 := by
  classical
  funext S
  by_cases ha : a ∈ S
  · simp [MetricCodes.Boolean.lowerAt, ha]
  · have hcard : (insert a S).card ≠ 0 :=
      Finset.card_ne_zero_of_mem (Finset.mem_insert_self a S)
    simp [MetricCodes.Boolean.lowerAt, ha, hf (insert a S) hcard]

theorem johnsonMembership_isLevel {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsLevel j f)
    (a : Fin n) :
    MetricCodes.Boolean.IsLevel j
      (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f)) := by
  intro S hS
  rw [MetricCodes.Boolean.raiseAt_lowerAt_self]
  simp [hf S hS]

theorem johnsonUpperRaw_isLevel {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (a : Fin n) :
    MetricCodes.Boolean.IsLevel (j + 1) (johnsonUpperRaw j a f) := by
  cases j with
  | zero =>
      have hzero := johnsonLowerAt_eq_zero_of_level_zero f hf.1 a
      have hcoordinate := hf.1.raiseAt a
      have hglobal := hf.1.raise
      intro S hS
      simp only [johnsonUpperRaw, Pi.sub_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [hcoordinate S hS, hglobal S hS, hzero]
      simp [MetricCodes.Boolean.raise, MetricCodes.Boolean.raiseAt]
  | succ k =>
      have hdown :
          MetricCodes.Boolean.IsLevel k (MetricCodes.Boolean.lowerAt a f) :=
        hf.1.lowerAt a
      have hcoordinate := hf.1.raiseAt a
      have hglobal := hf.1.raise
      have hmembership :=
        (johnsonMembership_isLevel f hf.1 a).raise
      have hdouble := hdown.raise.raise
      intro S hS
      simp only [johnsonUpperRaw, Pi.sub_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [hcoordinate S hS, hglobal S hS,
        hmembership S hS, hdouble S hS]
      ring

theorem johnsonLowerRaise_of_level {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsLevel j f) :
    MetricCodes.Boolean.lower (MetricCodes.Boolean.raise f) =
      MetricCodes.Boolean.raise (MetricCodes.Boolean.lower f) +
        johnsonHarmonicGap n j • f := by
  funext S
  have h :=
    MetricCodes.Boolean.lower_raise_sub_raise_lower_of_level f hf S
  have h' := sub_eq_iff_eq_add.mp h
  simpa [johnsonHarmonicGap, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, add_comm] using h'

theorem johnsonLowerRaiseAt_of_harmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (a : Fin n) :
    MetricCodes.Boolean.lower (MetricCodes.Boolean.raiseAt a f) =
      f - (2 : ℝ) •
        MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f) := by
  classical
  have hzero : MetricCodes.Boolean.lower f = 0 := funext hf.2
  funext S
  have h := johnsonLowerRaiseAt_commutator f a S
  rw [hzero] at h
  simpa [MetricCodes.Boolean.raiseAt, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul] using h

theorem johnsonLowerRaise_of_harmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) :
    MetricCodes.Boolean.lower (MetricCodes.Boolean.raise f) =
      johnsonHarmonicGap n j • f := by
  funext S
  simpa [johnsonHarmonicGap, Pi.smul_apply, smul_eq_mul]
    using MetricCodes.Boolean.lower_raise_of_harmonic f hf S

theorem johnsonLowerDoubleRaiseLowerAt_of_harmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (a : Fin n) :
    MetricCodes.Boolean.lower
      (MetricCodes.Boolean.raise
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f))) =
      (2 * (johnsonHarmonicGap n j + 1)) •
        MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f) := by
  cases j with
  | zero =>
      have hzero := johnsonLowerAt_eq_zero_of_level_zero f hf.1 a
      have hraise :
          MetricCodes.Boolean.raise (0 : MetricCodes.Boolean.Function n) = 0 := by
        change MetricCodes.Boolean.raiseLinear n
          (0 : MetricCodes.Boolean.Function n) = 0
        exact map_zero (MetricCodes.Boolean.raiseLinear n)
      have hlower :
          MetricCodes.Boolean.lower (0 : MetricCodes.Boolean.Function n) = 0 := by
        change MetricCodes.Boolean.lowerLinear n
          (0 : MetricCodes.Boolean.Function n) = 0
        exact map_zero (MetricCodes.Boolean.lowerLinear n)
      rw [hzero]
      simp only [hraise, hlower, smul_zero]
  | succ k =>
      have hdown := johnsonLowerAt_harmonic f hf a
      have h := MetricCodes.Boolean.lower_raised_succ_of_harmonic
        (MetricCodes.Boolean.lowerAt a f) hdown 1
      change
        MetricCodes.Boolean.lower
          (MetricCodes.Boolean.raise
            (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f))) =
          MetricCodes.Boolean.harmonicCoefficient n k 2 •
            MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f) at h
      have hcoefficient :
          MetricCodes.Boolean.harmonicCoefficient n k 2 =
            2 * (johnsonHarmonicGap n (k + 1) + 1) := by
        simp [MetricCodes.Boolean.harmonicCoefficient,
          johnsonHarmonicGap, Nat.cast_add, Nat.cast_one]
        ring
      rw [hcoefficient] at h
      exact h

theorem johnsonLowerRaiseMembership_of_harmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (a : Fin n) :
    MetricCodes.Boolean.lower
      (MetricCodes.Boolean.raise
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))) =
      MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f) +
        johnsonHarmonicGap n j •
          MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f) := by
  rw [johnsonLowerRaise_of_level
    (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))
    (johnsonMembership_isLevel f hf.1 a),
    johnsonLowerRaiseAtLowerAt_of_harmonic f hf a]

theorem johnsonUpperRaw_isHarmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hhalf : 2 * (j + 1) ≤ n) (a : Fin n) :
    MetricCodes.Boolean.IsHarmonic (j + 1)
      (johnsonUpperRaw j a f) := by
  refine ⟨johnsonUpperRaw_isLevel f hf a, ?_⟩
  have hgap : 0 < johnsonHarmonicGap n j := by
    apply johnsonHarmonicGap_pos
    omega
  have hgapone : johnsonHarmonicGap n j + 1 ≠ 0 := by
    linarith
  have hgapne : johnsonHarmonicGap n j ≠ 0 := hgap.ne'
  have hcoordinate := johnsonLowerRaiseAt_of_harmonic f hf a
  have hglobal := johnsonLowerRaise_of_harmonic f hf
  have hmembership :=
    johnsonLowerRaiseMembership_of_harmonic f hf a
  have hdouble :=
    johnsonLowerDoubleRaiseLowerAt_of_harmonic f hf a
  intro S
  unfold johnsonUpperRaw
  rw [johnsonBooleanLower_sub,
    MetricCodes.Boolean.lower_add,
    johnsonBooleanLower_sub,
    MetricCodes.Boolean.lower_smul,
    MetricCodes.Boolean.lower_smul,
    MetricCodes.Boolean.lower_smul,
    hcoordinate, hglobal, hmembership, hdouble]
  simp only [Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  field_simp [hgapne, hgapone]
  ring

theorem johnsonBooleanDot_sub_left {n : ℕ}
    (f g h : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.dot (f - g) h =
      MetricCodes.Boolean.dot f h - MetricCodes.Boolean.dot g h := by
  classical
  simp only [MetricCodes.Boolean.dot, Pi.sub_apply, sub_mul,
    Finset.sum_sub_distrib]

theorem johnsonBooleanDot_sub_right {n : ℕ}
    (f g h : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.dot f (g - h) =
      MetricCodes.Boolean.dot f g - MetricCodes.Boolean.dot f h := by
  classical
  simp only [MetricCodes.Boolean.dot, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib]

theorem johnsonBooleanDot_add_left {n : ℕ}
    (f g h : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.dot (f + g) h =
      MetricCodes.Boolean.dot f h + MetricCodes.Boolean.dot g h := by
  classical
  simp only [MetricCodes.Boolean.dot, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]

theorem johnsonDotRaise_harmonic_right {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hg : MetricCodes.Boolean.IsHarmonic j g) :
    MetricCodes.Boolean.dot (MetricCodes.Boolean.raise f) g = 0 := by
  rw [MetricCodes.Boolean.dot_raise_eq_lower]
  have hzero : MetricCodes.Boolean.lower g = 0 := funext hg.2
  rw [hzero]
  simp [MetricCodes.Boolean.dot]

theorem johnsonLowerAtRaiseAtLowerAt {n : ℕ}
    (f : MetricCodes.Boolean.Function n) (a : Fin n) :
    MetricCodes.Boolean.lowerAt a
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f)) =
      MetricCodes.Boolean.lowerAt a f := by
  classical
  funext S
  rw [MetricCodes.Boolean.lowerAt_raiseAt_self]
  by_cases ha : a ∈ S
  · simp [ha, MetricCodes.Boolean.lowerAt]
  · simp [ha]

theorem johnsonSumDotMembershipMembership {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsLevel j f) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g))) =
      (j : ℝ) * MetricCodes.Boolean.dot f g := by
  classical
  calc
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g))) =
      ∑ a : Fin n,
        MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f)
          (MetricCodes.Boolean.lowerAt a (MetricCodes.Boolean.raiseAt a
            (MetricCodes.Boolean.lowerAt a g))) := by
          apply Finset.sum_congr rfl
          intro a _
          exact MetricCodes.Boolean.dot_raiseAt_eq_lowerAt a
            (MetricCodes.Boolean.lowerAt a f)
            (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g))
    _ = ∑ a : Fin n,
          MetricCodes.Boolean.dot
            (MetricCodes.Boolean.lowerAt a f)
            (MetricCodes.Boolean.lowerAt a g) := by
          simp_rw [johnsonLowerAtRaiseAtLowerAt]
    _ = (j : ℝ) * MetricCodes.Boolean.dot f g :=
      MetricCodes.Boolean.sum_dot_lowerAt_of_level f g hf

theorem johnsonSumDotMembershipLeft {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsLevel j f) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f)) g) =
      (j : ℝ) * MetricCodes.Boolean.dot f g := by
  classical
  calc
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f)) g) =
      ∑ a : Fin n,
        MetricCodes.Boolean.dot
          (MetricCodes.Boolean.lowerAt a f)
          (MetricCodes.Boolean.lowerAt a g) := by
          apply Finset.sum_congr rfl
          intro a _
          exact MetricCodes.Boolean.dot_raiseAt_eq_lowerAt a
            (MetricCodes.Boolean.lowerAt a f) g
    _ = (j : ℝ) * MetricCodes.Boolean.dot f g :=
      MetricCodes.Boolean.sum_dot_lowerAt_of_level f g hf

theorem johnsonSumDotMembershipRight {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hg : MetricCodes.Boolean.IsLevel j g) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot f
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g))) =
      (j : ℝ) * MetricCodes.Boolean.dot f g := by
  classical
  calc
    (∑ a : Fin n,
      MetricCodes.Boolean.dot f
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g))) =
      ∑ a : Fin n,
        MetricCodes.Boolean.dot
          (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)) f := by
          apply Finset.sum_congr rfl
          intro a _
          exact MetricCodes.Boolean.dot_comm _ _
    _ = (j : ℝ) * MetricCodes.Boolean.dot g f :=
      johnsonSumDotMembershipLeft g f hg
    _ = (j : ℝ) * MetricCodes.Boolean.dot f g := by
      rw [MetricCodes.Boolean.dot_comm g f]

theorem johnsonLowerRaiseLowerAt_of_harmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hj : 0 < j) (a : Fin n) :
    MetricCodes.Boolean.lower
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f)) =
      (johnsonHarmonicGap n j + 2) •
        MetricCodes.Boolean.lowerAt a f := by
  cases j with
  | zero => omega
  | succ k =>
      have hdown := johnsonLowerAt_harmonic f hf a
      funext S
      rw [MetricCodes.Boolean.lower_raise_of_harmonic
        (MetricCodes.Boolean.lowerAt a f) hdown]
      change
        ((n : ℝ) - 2 * (k : ℝ)) *
            MetricCodes.Boolean.lowerAt a f S =
          (johnsonHarmonicGap n (k + 1) + 2) *
            MetricCodes.Boolean.lowerAt a f S
      unfold johnsonHarmonicGap
      push_cast
      ring

theorem johnsonSumDotMembershipRaisedDeletion {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g))) =
      (j : ℝ) * MetricCodes.Boolean.dot f g := by
  classical
  calc
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g))) =
      ∑ a : Fin n,
        MetricCodes.Boolean.dot
          (MetricCodes.Boolean.lowerAt a f)
          (MetricCodes.Boolean.lowerAt a g) := by
          apply Finset.sum_congr rfl
          intro a _
          calc
            MetricCodes.Boolean.dot
                (MetricCodes.Boolean.raiseAt a
                  (MetricCodes.Boolean.lowerAt a f))
                (MetricCodes.Boolean.raise
                  (MetricCodes.Boolean.lowerAt a g)) =
              MetricCodes.Boolean.dot
                (MetricCodes.Boolean.raise
                  (MetricCodes.Boolean.lowerAt a g))
                (MetricCodes.Boolean.raiseAt a
                  (MetricCodes.Boolean.lowerAt a f)) :=
                MetricCodes.Boolean.dot_comm _ _
            _ = MetricCodes.Boolean.dot
                (MetricCodes.Boolean.lowerAt a g)
                (MetricCodes.Boolean.lower
                  (MetricCodes.Boolean.raiseAt a
                    (MetricCodes.Boolean.lowerAt a f))) :=
                MetricCodes.Boolean.dot_raise_eq_lower _ _
            _ = MetricCodes.Boolean.dot
                (MetricCodes.Boolean.lowerAt a g)
                (MetricCodes.Boolean.lowerAt a f) := by
                  rw [johnsonLowerRaiseAtLowerAt_of_harmonic f hf a]
            _ = MetricCodes.Boolean.dot
                (MetricCodes.Boolean.lowerAt a f)
                (MetricCodes.Boolean.lowerAt a g) :=
                MetricCodes.Boolean.dot_comm _ _
    _ = (j : ℝ) * MetricCodes.Boolean.dot f g :=
      MetricCodes.Boolean.sum_dot_lowerAt_of_level f g hf.1

theorem johnsonSumDotRaisedDeletionMembership {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsLevel j f)
    (hg : MetricCodes.Boolean.IsHarmonic j g) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g))) =
      (j : ℝ) * MetricCodes.Boolean.dot f g := by
  classical
  calc
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g))) =
      ∑ a : Fin n,
        MetricCodes.Boolean.dot
          (MetricCodes.Boolean.lowerAt a f)
          (MetricCodes.Boolean.lowerAt a g) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [MetricCodes.Boolean.dot_raise_eq_lower,
            johnsonLowerRaiseAtLowerAt_of_harmonic g hg a]
    _ = (j : ℝ) * MetricCodes.Boolean.dot f g :=
      MetricCodes.Boolean.sum_dot_lowerAt_of_level f g hf

theorem johnsonSumDotRaisedDeletionRaisedDeletion {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsLevel j f)
    (hg : MetricCodes.Boolean.IsHarmonic j g)
    (hj : 0 < j) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g))) =
      (johnsonHarmonicGap n j + 2) *
        ((j : ℝ) * MetricCodes.Boolean.dot f g) := by
  classical
  calc
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g))) =
      ∑ a : Fin n,
        MetricCodes.Boolean.dot
          (MetricCodes.Boolean.lowerAt a f)
          (MetricCodes.Boolean.lower
            (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g))) := by
          apply Finset.sum_congr rfl
          intro a _
          exact MetricCodes.Boolean.dot_raise_eq_lower
            (MetricCodes.Boolean.lowerAt a f)
            (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g))
    _ = ∑ a : Fin n,
          (johnsonHarmonicGap n j + 2) *
            MetricCodes.Boolean.dot
              (MetricCodes.Boolean.lowerAt a f)
              (MetricCodes.Boolean.lowerAt a g) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [johnsonLowerRaiseLowerAt_of_harmonic g hg hj a,
            MetricCodes.Boolean.dot_smul_right]
    _ = (johnsonHarmonicGap n j + 2) *
          (∑ a : Fin n,
            MetricCodes.Boolean.dot
              (MetricCodes.Boolean.lowerAt a f)
              (MetricCodes.Boolean.lowerAt a g)) := by
          rw [Finset.mul_sum]
    _ = (johnsonHarmonicGap n j + 2) *
          ((j : ℝ) * MetricCodes.Boolean.dot f g) := by
          rw [MetricCodes.Boolean.sum_dot_lowerAt_of_level f g hf]

theorem johnsonSumDotRaisedDeletionHarmonicRight {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hg : MetricCodes.Boolean.IsHarmonic j g) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f)) g) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a _
  exact johnsonDotRaise_harmonic_right
    (MetricCodes.Boolean.lowerAt a f) g hg

theorem johnsonSumDotHarmonicRaisedDeletion {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot f
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g))) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a _
  rw [MetricCodes.Boolean.dot_comm]
  exact johnsonDotRaise_harmonic_right
    (MetricCodes.Boolean.lowerAt a g) f hf

theorem johnsonMiddleRaw_coordinateDot {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hg : MetricCodes.Boolean.IsHarmonic j g)
    (hj : 0 < j) (hhalf : 2 * j < n) :
    MetricCodes.Boolean.coordinateDot
        (fun a : Fin n => johnsonMiddleRaw j a f)
        (fun a : Fin n => johnsonMiddleRaw j a g) =
      johnsonMiddleScale n j * MetricCodes.Boolean.dot f g := by
  classical
  let c : ℝ := (johnsonHarmonicGap n j + 2)⁻¹
  let b : ℝ := (j : ℝ) / (n : ℝ)
  let mf : Fin n → MetricCodes.Boolean.Function n :=
    fun a => MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f)
  let mg : Fin n → MetricCodes.Boolean.Function n :=
    fun a => MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)
  let uf : Fin n → MetricCodes.Boolean.Function n :=
    fun a => MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f)
  let ug : Fin n → MetricCodes.Boolean.Function n :=
    fun a => MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g)
  have hpoint (a : Fin n) :
      MetricCodes.Boolean.dot
          (johnsonMiddleRaw j a f)
          (johnsonMiddleRaw j a g) =
        MetricCodes.Boolean.dot (mf a) (mg a) -
          c * MetricCodes.Boolean.dot (mf a) (ug a) -
          b * MetricCodes.Boolean.dot (mf a) g -
          c * MetricCodes.Boolean.dot (uf a) (mg a) +
          c ^ 2 * MetricCodes.Boolean.dot (uf a) (ug a) +
          c * b * MetricCodes.Boolean.dot (uf a) g -
          b * MetricCodes.Boolean.dot f (mg a) +
          b * c * MetricCodes.Boolean.dot f (ug a) +
          b ^ 2 * MetricCodes.Boolean.dot f g := by
    dsimp [mf, mg, uf, ug, c, b]
    simp only [johnsonMiddleRaw,
      johnsonBooleanDot_sub_left,
      johnsonBooleanDot_sub_right,
      MetricCodes.Boolean.dot_smul_left,
      MetricCodes.Boolean.dot_smul_right]
    ring
  have hn : 0 < n := by omega
  have hnreal : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hgap := johnsonHarmonicGap_pos hhalf
  have hgapplus : johnsonHarmonicGap n j + 2 ≠ 0 := by
    linarith
  have hconstant :
      (∑ _a : Fin n, MetricCodes.Boolean.dot f g) =
        (n : ℝ) * MetricCodes.Boolean.dot f g := by
    simp
  calc
    MetricCodes.Boolean.coordinateDot
        (fun a : Fin n => johnsonMiddleRaw j a f)
        (fun a : Fin n => johnsonMiddleRaw j a g) =
      (∑ a : Fin n, MetricCodes.Boolean.dot (mf a) (mg a)) -
        c * (∑ a : Fin n, MetricCodes.Boolean.dot (mf a) (ug a)) -
        b * (∑ a : Fin n, MetricCodes.Boolean.dot (mf a) g) -
        c * (∑ a : Fin n, MetricCodes.Boolean.dot (uf a) (mg a)) +
        c ^ 2 *
          (∑ a : Fin n, MetricCodes.Boolean.dot (uf a) (ug a)) +
        c * b * (∑ a : Fin n, MetricCodes.Boolean.dot (uf a) g) -
        b * (∑ a : Fin n, MetricCodes.Boolean.dot f (mg a)) +
        b * c * (∑ a : Fin n, MetricCodes.Boolean.dot f (ug a)) +
        b ^ 2 * (∑ _a : Fin n, MetricCodes.Boolean.dot f g) := by
          unfold MetricCodes.Boolean.coordinateDot
          simp_rw [hpoint]
          simp only [Finset.sum_add_distrib,
            Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = johnsonMiddleScale n j * MetricCodes.Boolean.dot f g := by
          dsimp only [mf, mg, uf, ug]
          rw [johnsonSumDotMembershipMembership f g hf.1,
            johnsonSumDotMembershipRaisedDeletion f g hf,
            johnsonSumDotMembershipLeft f g hf.1,
            johnsonSumDotRaisedDeletionMembership f g hf.1 hg,
            johnsonSumDotRaisedDeletionRaisedDeletion
              f g hf.1 hg hj,
            johnsonSumDotRaisedDeletionHarmonicRight f g hg,
            johnsonSumDotMembershipRight f g hg.1,
            johnsonSumDotHarmonicRaisedDeletion f g hf,
            hconstant]
          dsimp [c, b]
          unfold johnsonMiddleScale
          field_simp [hnreal, hgapplus]
          unfold johnsonHarmonicGap
          ring

def johnsonMiddleChannel {n : ℕ} (j : ℕ)
    (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.CoordinateFunction n :=
  fun a =>
    (Real.sqrt (johnsonMiddleScale n j))⁻¹ •
      johnsonMiddleRaw j a f

theorem johnsonMiddleChannel_isometry {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hg : MetricCodes.Boolean.IsHarmonic j g)
    (hj : 0 < j) (hhalf : 2 * j < n) :
    MetricCodes.Boolean.coordinateDot
        (johnsonMiddleChannel j f)
        (johnsonMiddleChannel j g) =
      MetricCodes.Boolean.dot f g := by
  classical
  have hpos := johnsonMiddleScale_pos hj hhalf
  have hs : Real.sqrt (johnsonMiddleScale n j) ≠ 0 :=
    (Real.sqrt_pos.mpr hpos).ne'
  have hsquare :
      Real.sqrt (johnsonMiddleScale n j) *
          Real.sqrt (johnsonMiddleScale n j) =
        johnsonMiddleScale n j :=
    Real.mul_self_sqrt hpos.le
  have hscalar :
      (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          johnsonMiddleScale n j = 1 := by
    calc
      (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          johnsonMiddleScale n j =
        (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          (Real.sqrt (johnsonMiddleScale n j) *
            Real.sqrt (johnsonMiddleScale n j)) := by
              rw [hsquare]
      _ = 1 := by
        field_simp [hs]
  calc
    MetricCodes.Boolean.coordinateDot
        (johnsonMiddleChannel j f)
        (johnsonMiddleChannel j g) =
      ((Real.sqrt (johnsonMiddleScale n j))⁻¹ *
        (Real.sqrt (johnsonMiddleScale n j))⁻¹) *
        MetricCodes.Boolean.coordinateDot
          (fun a : Fin n => johnsonMiddleRaw j a f)
          (fun a : Fin n => johnsonMiddleRaw j a g) := by
          simp only [MetricCodes.Boolean.coordinateDot,
            johnsonMiddleChannel,
            MetricCodes.Boolean.dot_smul_left,
            MetricCodes.Boolean.dot_smul_right,
            Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = ((Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          (Real.sqrt (johnsonMiddleScale n j))⁻¹) *
        (johnsonMiddleScale n j * MetricCodes.Boolean.dot f g) := by
          rw [johnsonMiddleRaw_coordinateDot f g hf hg hj hhalf]
    _ = ((Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          johnsonMiddleScale n j) *
        MetricCodes.Boolean.dot f g := by
          ring
    _ = MetricCodes.Boolean.dot f g := by
          rw [hscalar, one_mul]

theorem johnsonSumDotRaiseAtRaise {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hg : MetricCodes.Boolean.IsHarmonic j g) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot (MetricCodes.Boolean.raiseAt a f)
        (MetricCodes.Boolean.raise g)) =
      johnsonHarmonicGap n j * MetricCodes.Boolean.dot f g := by
  classical
  calc
    (∑ a : Fin n,
      MetricCodes.Boolean.dot (MetricCodes.Boolean.raiseAt a f)
        (MetricCodes.Boolean.raise g)) =
      ∑ a : Fin n,
        MetricCodes.Boolean.dot f
          (MetricCodes.Boolean.lowerAt a (MetricCodes.Boolean.raise g)) := by
          apply Finset.sum_congr rfl
          intro a _
          exact MetricCodes.Boolean.dot_raiseAt_eq_lowerAt a f
            (MetricCodes.Boolean.raise g)
    _ = MetricCodes.Boolean.dot f
          (MetricCodes.Boolean.lower (MetricCodes.Boolean.raise g)) := by
          simp only [MetricCodes.Boolean.dot, MetricCodes.Boolean.lower,
            Finset.mul_sum]
          exact Finset.sum_comm
    _ = johnsonHarmonicGap n j * MetricCodes.Boolean.dot f g := by
          rw [johnsonLowerRaise_of_harmonic g hg,
            MetricCodes.Boolean.dot_smul_right]

theorem johnsonSumDotRaiseAtRaisedMembership {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hg : MetricCodes.Boolean.IsLevel j g) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot (MetricCodes.Boolean.raiseAt a f)
        (MetricCodes.Boolean.raise
          (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)))) =
      -(j : ℝ) * MetricCodes.Boolean.dot f g := by
  classical
  calc
    (∑ a : Fin n,
      MetricCodes.Boolean.dot (MetricCodes.Boolean.raiseAt a f)
        (MetricCodes.Boolean.raise
          (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)))) =
      ∑ a : Fin n,
        (MetricCodes.Boolean.dot f
          (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)) -
          2 * MetricCodes.Boolean.dot
            (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))
            (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g))) := by
          apply Finset.sum_congr rfl
          intro a _
          calc
            MetricCodes.Boolean.dot (MetricCodes.Boolean.raiseAt a f)
                (MetricCodes.Boolean.raise
                  (MetricCodes.Boolean.raiseAt a
                    (MetricCodes.Boolean.lowerAt a g))) =
              MetricCodes.Boolean.dot
                (MetricCodes.Boolean.raise
                  (MetricCodes.Boolean.raiseAt a
                    (MetricCodes.Boolean.lowerAt a g)))
                (MetricCodes.Boolean.raiseAt a f) :=
                MetricCodes.Boolean.dot_comm _ _
            _ = MetricCodes.Boolean.dot
                (MetricCodes.Boolean.raiseAt a
                  (MetricCodes.Boolean.lowerAt a g))
                (MetricCodes.Boolean.lower
                  (MetricCodes.Boolean.raiseAt a f)) :=
                MetricCodes.Boolean.dot_raise_eq_lower _ _
            _ = MetricCodes.Boolean.dot
                (MetricCodes.Boolean.raiseAt a
                  (MetricCodes.Boolean.lowerAt a g))
                (f - (2 : ℝ) •
                  MetricCodes.Boolean.raiseAt a
                    (MetricCodes.Boolean.lowerAt a f)) := by
                  rw [johnsonLowerRaiseAt_of_harmonic f hf a]
            _ = MetricCodes.Boolean.dot f
                  (MetricCodes.Boolean.raiseAt a
                    (MetricCodes.Boolean.lowerAt a g)) -
                2 * MetricCodes.Boolean.dot
                  (MetricCodes.Boolean.raiseAt a
                    (MetricCodes.Boolean.lowerAt a f))
                  (MetricCodes.Boolean.raiseAt a
                    (MetricCodes.Boolean.lowerAt a g)) := by
                  rw [johnsonBooleanDot_sub_right,
                    MetricCodes.Boolean.dot_smul_right,
                    MetricCodes.Boolean.dot_comm
                      (MetricCodes.Boolean.raiseAt a
                        (MetricCodes.Boolean.lowerAt a g)) f,
                    MetricCodes.Boolean.dot_comm
                      (MetricCodes.Boolean.raiseAt a
                        (MetricCodes.Boolean.lowerAt a g))
                      (MetricCodes.Boolean.raiseAt a
                        (MetricCodes.Boolean.lowerAt a f))]
    _ = (∑ a : Fin n,
          MetricCodes.Boolean.dot f
            (MetricCodes.Boolean.raiseAt a
              (MetricCodes.Boolean.lowerAt a g))) -
        2 * (∑ a : Fin n,
          MetricCodes.Boolean.dot
            (MetricCodes.Boolean.raiseAt a
              (MetricCodes.Boolean.lowerAt a f))
            (MetricCodes.Boolean.raiseAt a
              (MetricCodes.Boolean.lowerAt a g))) := by
          simp only [Finset.sum_sub_distrib,
            ← Finset.mul_sum]
    _ = -(j : ℝ) * MetricCodes.Boolean.dot f g := by
          rw [johnsonSumDotMembershipRight f g hg,
            johnsonSumDotMembershipMembership f g hf.1]
          ring

theorem johnsonSumDotRaiseAtDoubleRaisedDeletion {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot (MetricCodes.Boolean.raiseAt a f)
        (MetricCodes.Boolean.raise
          (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g)))) =
      -(2 * (j : ℝ)) * MetricCodes.Boolean.dot f g := by
  classical
  calc
    (∑ a : Fin n,
      MetricCodes.Boolean.dot (MetricCodes.Boolean.raiseAt a f)
        (MetricCodes.Boolean.raise
          (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g)))) =
      ∑ a : Fin n,
        (MetricCodes.Boolean.dot f
          (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g)) -
          2 * MetricCodes.Boolean.dot
            (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))
            (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g))) := by
          apply Finset.sum_congr rfl
          intro a _
          calc
            MetricCodes.Boolean.dot (MetricCodes.Boolean.raiseAt a f)
                (MetricCodes.Boolean.raise
                  (MetricCodes.Boolean.raise
                    (MetricCodes.Boolean.lowerAt a g))) =
              MetricCodes.Boolean.dot
                (MetricCodes.Boolean.raise
                  (MetricCodes.Boolean.raise
                    (MetricCodes.Boolean.lowerAt a g)))
                (MetricCodes.Boolean.raiseAt a f) :=
                MetricCodes.Boolean.dot_comm _ _
            _ = MetricCodes.Boolean.dot
                (MetricCodes.Boolean.raise
                  (MetricCodes.Boolean.lowerAt a g))
                (MetricCodes.Boolean.lower
                  (MetricCodes.Boolean.raiseAt a f)) :=
                MetricCodes.Boolean.dot_raise_eq_lower _ _
            _ = MetricCodes.Boolean.dot
                (MetricCodes.Boolean.raise
                  (MetricCodes.Boolean.lowerAt a g))
                (f - (2 : ℝ) •
                  MetricCodes.Boolean.raiseAt a
                    (MetricCodes.Boolean.lowerAt a f)) := by
                  rw [johnsonLowerRaiseAt_of_harmonic f hf a]
            _ = MetricCodes.Boolean.dot f
                  (MetricCodes.Boolean.raise
                    (MetricCodes.Boolean.lowerAt a g)) -
                2 * MetricCodes.Boolean.dot
                  (MetricCodes.Boolean.raiseAt a
                    (MetricCodes.Boolean.lowerAt a f))
                  (MetricCodes.Boolean.raise
                    (MetricCodes.Boolean.lowerAt a g)) := by
                  rw [johnsonBooleanDot_sub_right,
                    MetricCodes.Boolean.dot_smul_right,
                    MetricCodes.Boolean.dot_comm
                      (MetricCodes.Boolean.raise
                        (MetricCodes.Boolean.lowerAt a g)) f,
                    MetricCodes.Boolean.dot_comm
                      (MetricCodes.Boolean.raise
                        (MetricCodes.Boolean.lowerAt a g))
                      (MetricCodes.Boolean.raiseAt a
                        (MetricCodes.Boolean.lowerAt a f))]
    _ = (∑ a : Fin n,
          MetricCodes.Boolean.dot f
            (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g))) -
        2 * (∑ a : Fin n,
          MetricCodes.Boolean.dot
            (MetricCodes.Boolean.raiseAt a
              (MetricCodes.Boolean.lowerAt a f))
            (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g))) := by
          simp only [Finset.sum_sub_distrib,
            ← Finset.mul_sum]
    _ = -(2 * (j : ℝ)) * MetricCodes.Boolean.dot f g := by
          rw [johnsonSumDotHarmonicRaisedDeletion f g hf,
            johnsonSumDotMembershipRaisedDeletion f g hf]
          ring

theorem johnsonUpperRaw_dot_eq_coordinateCreation {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hg : MetricCodes.Boolean.IsHarmonic j g)
    (hhalf : 2 * (j + 1) ≤ n) (a : Fin n) :
    MetricCodes.Boolean.dot
        (johnsonUpperRaw j a f)
        (johnsonUpperRaw j a g) =
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raiseAt a f)
        (johnsonUpperRaw j a g) := by
  have hup := johnsonUpperRaw_isHarmonic g hg hhalf a
  have hglobal := johnsonDotRaise_harmonic_right f
    (johnsonUpperRaw j a g) hup
  have hmembership := johnsonDotRaise_harmonic_right
    (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))
    (johnsonUpperRaw j a g) hup
  have hdouble := johnsonDotRaise_harmonic_right
    (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f))
    (johnsonUpperRaw j a g) hup
  change
    MetricCodes.Boolean.dot
      (MetricCodes.Boolean.raiseAt a f -
        (johnsonHarmonicGap n j)⁻¹ •
          MetricCodes.Boolean.raise f +
        (2 / johnsonHarmonicGap n j) •
          MetricCodes.Boolean.raise
            (MetricCodes.Boolean.raiseAt a
              (MetricCodes.Boolean.lowerAt a f)) -
        (johnsonHarmonicGap n j *
          (johnsonHarmonicGap n j + 1))⁻¹ •
          MetricCodes.Boolean.raise
            (MetricCodes.Boolean.raise
              (MetricCodes.Boolean.lowerAt a f)))
      (johnsonUpperRaw j a g) = _
  simp only [johnsonBooleanDot_sub_left,
    johnsonBooleanDot_add_left,
    MetricCodes.Boolean.dot_smul_left]
  rw [hglobal, hmembership, hdouble]
  ring

theorem johnsonUpperRaw_coordinateDot {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hg : MetricCodes.Boolean.IsHarmonic j g)
    (hhalf : 2 * (j + 1) ≤ n) :
    MetricCodes.Boolean.coordinateDot
        (fun a : Fin n => johnsonUpperRaw j a f)
        (fun a : Fin n => johnsonUpperRaw j a g) =
      johnsonUpperScale n j * MetricCodes.Boolean.dot f g := by
  classical
  have hbelow : 2 * j < n := by omega
  have hgap := johnsonHarmonicGap_pos hbelow
  have hgapne : johnsonHarmonicGap n j ≠ 0 := hgap.ne'
  have hgapone : johnsonHarmonicGap n j + 1 ≠ 0 := by
    linarith
  calc
    MetricCodes.Boolean.coordinateDot
        (fun a : Fin n => johnsonUpperRaw j a f)
        (fun a : Fin n => johnsonUpperRaw j a g) =
      ∑ a : Fin n,
        MetricCodes.Boolean.dot
          (MetricCodes.Boolean.raiseAt a f)
          (johnsonUpperRaw j a g) := by
          unfold MetricCodes.Boolean.coordinateDot
          apply Finset.sum_congr rfl
          intro a _
          exact johnsonUpperRaw_dot_eq_coordinateCreation
            f g hg hhalf a
    _ = (∑ a : Fin n,
          MetricCodes.Boolean.dot
            (MetricCodes.Boolean.raiseAt a f)
            (MetricCodes.Boolean.raiseAt a g)) -
        (johnsonHarmonicGap n j)⁻¹ *
          (∑ a : Fin n,
            MetricCodes.Boolean.dot
              (MetricCodes.Boolean.raiseAt a f)
              (MetricCodes.Boolean.raise g)) +
        (2 / johnsonHarmonicGap n j) *
          (∑ a : Fin n,
            MetricCodes.Boolean.dot
              (MetricCodes.Boolean.raiseAt a f)
              (MetricCodes.Boolean.raise
                (MetricCodes.Boolean.raiseAt a
                  (MetricCodes.Boolean.lowerAt a g)))) -
        (johnsonHarmonicGap n j *
            (johnsonHarmonicGap n j + 1))⁻¹ *
          (∑ a : Fin n,
            MetricCodes.Boolean.dot
              (MetricCodes.Boolean.raiseAt a f)
              (MetricCodes.Boolean.raise
                (MetricCodes.Boolean.raise
                  (MetricCodes.Boolean.lowerAt a g)))) := by
          simp only [johnsonUpperRaw,
            johnsonBooleanDot_sub_right,
            MetricCodes.Boolean.dot_add_right,
            MetricCodes.Boolean.dot_smul_right,
            Finset.sum_add_distrib,
            Finset.sum_sub_distrib,
            ← Finset.mul_sum]
    _ = johnsonUpperScale n j * MetricCodes.Boolean.dot f g := by
          rw [MetricCodes.Boolean.sum_dot_raiseAt_of_level f g hf.1,
            johnsonSumDotRaiseAtRaise f g hg,
            johnsonSumDotRaiseAtRaisedMembership f g hf hg.1,
            johnsonSumDotRaiseAtDoubleRaisedDeletion f g hf]
          unfold johnsonUpperScale
          field_simp [hgapne, hgapone]
          unfold johnsonHarmonicGap
          ring

def johnsonUpperChannel {n : ℕ} (j : ℕ)
    (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.CoordinateFunction n :=
  fun a =>
    (Real.sqrt (johnsonUpperScale n j))⁻¹ •
      johnsonUpperRaw j a f

theorem johnsonUpperChannel_isometry {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hg : MetricCodes.Boolean.IsHarmonic j g)
    (hhalf : 2 * (j + 1) ≤ n) :
    MetricCodes.Boolean.coordinateDot
        (johnsonUpperChannel j f)
        (johnsonUpperChannel j g) =
      MetricCodes.Boolean.dot f g := by
  classical
  have hpos := johnsonUpperScale_pos hhalf
  have hs : Real.sqrt (johnsonUpperScale n j) ≠ 0 :=
    (Real.sqrt_pos.mpr hpos).ne'
  have hsquare :
      Real.sqrt (johnsonUpperScale n j) *
          Real.sqrt (johnsonUpperScale n j) =
        johnsonUpperScale n j :=
    Real.mul_self_sqrt hpos.le
  have hscalar :
      (Real.sqrt (johnsonUpperScale n j))⁻¹ *
          (Real.sqrt (johnsonUpperScale n j))⁻¹ *
          johnsonUpperScale n j = 1 := by
    calc
      (Real.sqrt (johnsonUpperScale n j))⁻¹ *
          (Real.sqrt (johnsonUpperScale n j))⁻¹ *
          johnsonUpperScale n j =
        (Real.sqrt (johnsonUpperScale n j))⁻¹ *
          (Real.sqrt (johnsonUpperScale n j))⁻¹ *
          (Real.sqrt (johnsonUpperScale n j) *
            Real.sqrt (johnsonUpperScale n j)) := by
              rw [hsquare]
      _ = 1 := by
        field_simp [hs]
  calc
    MetricCodes.Boolean.coordinateDot
        (johnsonUpperChannel j f)
        (johnsonUpperChannel j g) =
      ((Real.sqrt (johnsonUpperScale n j))⁻¹ *
        (Real.sqrt (johnsonUpperScale n j))⁻¹) *
        MetricCodes.Boolean.coordinateDot
          (fun a : Fin n => johnsonUpperRaw j a f)
          (fun a : Fin n => johnsonUpperRaw j a g) := by
          simp only [MetricCodes.Boolean.coordinateDot,
            johnsonUpperChannel,
            MetricCodes.Boolean.dot_smul_left,
            MetricCodes.Boolean.dot_smul_right,
            Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = ((Real.sqrt (johnsonUpperScale n j))⁻¹ *
          (Real.sqrt (johnsonUpperScale n j))⁻¹) *
        (johnsonUpperScale n j * MetricCodes.Boolean.dot f g) := by
          rw [johnsonUpperRaw_coordinateDot f g hf hg hhalf]
    _ = ((Real.sqrt (johnsonUpperScale n j))⁻¹ *
          (Real.sqrt (johnsonUpperScale n j))⁻¹ *
          johnsonUpperScale n j) *
        MetricCodes.Boolean.dot f g := by
          ring
    _ = MetricCodes.Boolean.dot f g := by
          rw [hscalar, one_mul]

def johnsonLowerChannel {n : ℕ} (j : ℕ)
    (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.CoordinateFunction n :=
  MetricCodes.Boolean.deleteChannel j f

theorem johnsonLowerChannel_isometry {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hj : 0 < j) :
    MetricCodes.Boolean.coordinateDot
        (johnsonLowerChannel j f)
        (johnsonLowerChannel j g) =
      MetricCodes.Boolean.dot f g := by
  exact MetricCodes.Boolean.deleteChannel_isometry hj f g hf.1

theorem johnsonDotHarmonicRaise {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) :
    MetricCodes.Boolean.dot f (MetricCodes.Boolean.raise g) = 0 := by
  rw [MetricCodes.Boolean.dot_comm]
  exact johnsonDotRaise_harmonic_right g f hf

theorem johnsonSumDotRaiseAtRight {n : ℕ}
    (f g : MetricCodes.Boolean.Function n) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot f (MetricCodes.Boolean.raiseAt a g)) =
      MetricCodes.Boolean.dot f (MetricCodes.Boolean.raise g) := by
  classical
  simp only [MetricCodes.Boolean.dot, MetricCodes.Boolean.raise,
    Finset.mul_sum]
  exact Finset.sum_comm

theorem johnsonSumDotLowerAtRight {n : ℕ}
    (f g : MetricCodes.Boolean.Function n) :
    (∑ a : Fin n,
      MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f) g) =
      MetricCodes.Boolean.dot f (MetricCodes.Boolean.raise g) := by
  classical
  calc
    (∑ a : Fin n,
      MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f) g) =
      ∑ a : Fin n,
        MetricCodes.Boolean.dot f (MetricCodes.Boolean.raiseAt a g) := by
          apply Finset.sum_congr rfl
          intro a _
          exact MetricCodes.Boolean.dot_lowerAt_eq_raiseAt a f g
    _ = MetricCodes.Boolean.dot f (MetricCodes.Boolean.raise g) :=
      johnsonSumDotRaiseAtRight f g

theorem johnsonDotMembershipRaiseAt {n : ℕ}
    (f g : MetricCodes.Boolean.Function n) (a : Fin n) :
    MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raiseAt a g) =
      MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f) g := by
  classical
  calc
    MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raiseAt a g) =
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.lowerAt a f)
        (MetricCodes.Boolean.lowerAt a (MetricCodes.Boolean.raiseAt a g)) :=
      MetricCodes.Boolean.dot_raiseAt_eq_lowerAt a
        (MetricCodes.Boolean.lowerAt a f)
        (MetricCodes.Boolean.raiseAt a g)
    _ = MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f) g := by
      unfold MetricCodes.Boolean.dot
      apply Finset.sum_congr rfl
      intro S _
      rw [MetricCodes.Boolean.lowerAt_raiseAt_self]
      by_cases ha : a ∈ S
      · simp [ha, MetricCodes.Boolean.lowerAt]
      · simp [ha]

theorem johnsonDotRaisedDeletionRaiseAt {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hg : MetricCodes.Boolean.IsHarmonic j g) (a : Fin n) :
    MetricCodes.Boolean.dot
        (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f))
        (MetricCodes.Boolean.raiseAt a g) =
      MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f) g := by
  rw [MetricCodes.Boolean.dot_raise_eq_lower,
    johnsonLowerRaiseAt_of_harmonic g hg a,
    johnsonBooleanDot_sub_right,
    MetricCodes.Boolean.dot_smul_right,
    MetricCodes.Boolean.dot_lowerAt_raiseAt]
  ring

theorem johnsonLowerMiddleRaw_orthogonal {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (j + 1) f) :
    MetricCodes.Boolean.coordinateDot
        (fun a : Fin n => MetricCodes.Boolean.lowerAt a f)
        (fun a : Fin n => johnsonMiddleRaw j a g) = 0 := by
  classical
  have hpoint (a : Fin n) :
      MetricCodes.Boolean.dot
          (MetricCodes.Boolean.lowerAt a f)
          (johnsonMiddleRaw j a g) =
        -((j : ℝ) / (n : ℝ)) *
          MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f) g := by
    have hdown := johnsonLowerAt_harmonic f hf a
    have hraise := johnsonDotHarmonicRaise
      (MetricCodes.Boolean.lowerAt a f)
      (MetricCodes.Boolean.lowerAt a g) hdown
    simp only [johnsonMiddleRaw,
      johnsonBooleanDot_sub_right,
      MetricCodes.Boolean.dot_smul_right]
    rw [MetricCodes.Boolean.dot_lowerAt_raiseAt, hraise]
    ring
  calc
    MetricCodes.Boolean.coordinateDot
        (fun a : Fin n => MetricCodes.Boolean.lowerAt a f)
        (fun a : Fin n => johnsonMiddleRaw j a g) =
      -((j : ℝ) / (n : ℝ)) *
        (∑ a : Fin n,
          MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f) g) := by
          unfold MetricCodes.Boolean.coordinateDot
          simp_rw [hpoint]
          rw [Finset.mul_sum]
    _ = 0 := by
          rw [johnsonSumDotLowerAtRight f g,
            johnsonDotHarmonicRaise f g hf]
          ring

theorem johnsonLowerUpperRaw_orthogonal {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (j + 2) f) :
    MetricCodes.Boolean.coordinateDot
        (fun a : Fin n => MetricCodes.Boolean.lowerAt a f)
        (fun a : Fin n => johnsonUpperRaw j a g) = 0 := by
  classical
  unfold MetricCodes.Boolean.coordinateDot
  apply Finset.sum_eq_zero
  intro a _
  have hf' : MetricCodes.Boolean.IsHarmonic ((j + 1) + 1) f := by
    simpa [Nat.add_assoc] using hf
  have hdown := johnsonLowerAt_harmonic f hf' a
  have hglobal := johnsonDotHarmonicRaise
    (MetricCodes.Boolean.lowerAt a f) g hdown
  have hmembership := johnsonDotHarmonicRaise
    (MetricCodes.Boolean.lowerAt a f)
    (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)) hdown
  have hdouble := johnsonDotHarmonicRaise
    (MetricCodes.Boolean.lowerAt a f)
    (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g)) hdown
  simp only [johnsonUpperRaw,
    johnsonBooleanDot_sub_right,
    MetricCodes.Boolean.dot_add_right,
    MetricCodes.Boolean.dot_smul_right]
  rw [MetricCodes.Boolean.dot_lowerAt_raiseAt,
    hglobal, hmembership, hdouble]
  ring

theorem johnsonMiddleUpperRaw_orthogonal {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (j + 1) f)
    (hg : MetricCodes.Boolean.IsHarmonic j g)
    (hhalf : 2 * (j + 1) < n) :
    MetricCodes.Boolean.coordinateDot
        (fun a : Fin n => johnsonMiddleRaw (j + 1) a f)
        (fun a : Fin n => johnsonUpperRaw j a g) = 0 := by
  classical
  have hpoint (a : Fin n) :
      MetricCodes.Boolean.dot
          (johnsonMiddleRaw (j + 1) a f)
          (johnsonUpperRaw j a g) =
        (1 - (johnsonHarmonicGap n (j + 1) + 2)⁻¹) *
          MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f) g -
        (((j + 1 : ℕ) : ℝ) / (n : ℝ)) *
          MetricCodes.Boolean.dot f (MetricCodes.Boolean.raiseAt a g) := by
    have hmid := johnsonMiddleRaw_isHarmonic
      f hf (by omega) hhalf a
    have hglobal := johnsonDotHarmonicRaise
      (johnsonMiddleRaw (j + 1) a f) g hmid
    have hmembership := johnsonDotHarmonicRaise
      (johnsonMiddleRaw (j + 1) a f)
      (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)) hmid
    have hdouble := johnsonDotHarmonicRaise
      (johnsonMiddleRaw (j + 1) a f)
      (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a g)) hmid
    calc
      MetricCodes.Boolean.dot
          (johnsonMiddleRaw (j + 1) a f)
          (johnsonUpperRaw j a g) =
        MetricCodes.Boolean.dot
          (johnsonMiddleRaw (j + 1) a f)
          (MetricCodes.Boolean.raiseAt a g) := by
            change
              MetricCodes.Boolean.dot
                (johnsonMiddleRaw (j + 1) a f)
                (MetricCodes.Boolean.raiseAt a g -
                  (johnsonHarmonicGap n j)⁻¹ •
                    MetricCodes.Boolean.raise g +
                  (2 / johnsonHarmonicGap n j) •
                    MetricCodes.Boolean.raise
                      (MetricCodes.Boolean.raiseAt a
                        (MetricCodes.Boolean.lowerAt a g)) -
                  (johnsonHarmonicGap n j *
                    (johnsonHarmonicGap n j + 1))⁻¹ •
                    MetricCodes.Boolean.raise
                      (MetricCodes.Boolean.raise
                        (MetricCodes.Boolean.lowerAt a g))) = _
            simp only [johnsonBooleanDot_sub_right,
              MetricCodes.Boolean.dot_add_right,
              MetricCodes.Boolean.dot_smul_right]
            rw [hglobal, hmembership, hdouble]
            ring
      _ = (1 - (johnsonHarmonicGap n (j + 1) + 2)⁻¹) *
            MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f) g -
          (((j + 1 : ℕ) : ℝ) / (n : ℝ)) *
            MetricCodes.Boolean.dot f (MetricCodes.Boolean.raiseAt a g) := by
            unfold johnsonMiddleRaw
            simp only [johnsonBooleanDot_sub_left,
              MetricCodes.Boolean.dot_smul_left]
            rw [johnsonDotMembershipRaiseAt f g a,
              johnsonDotRaisedDeletionRaiseAt f g hg a]
            ring
  calc
    MetricCodes.Boolean.coordinateDot
        (fun a : Fin n => johnsonMiddleRaw (j + 1) a f)
        (fun a : Fin n => johnsonUpperRaw j a g) =
      (1 - (johnsonHarmonicGap n (j + 1) + 2)⁻¹) *
          (∑ a : Fin n,
            MetricCodes.Boolean.dot (MetricCodes.Boolean.lowerAt a f) g) -
        (((j + 1 : ℕ) : ℝ) / (n : ℝ)) *
          (∑ a : Fin n,
            MetricCodes.Boolean.dot f (MetricCodes.Boolean.raiseAt a g)) := by
          unfold MetricCodes.Boolean.coordinateDot
          simp_rw [hpoint]
          simp only [Finset.sum_sub_distrib,
            ← Finset.mul_sum]
    _ = 0 := by
          rw [johnsonSumDotLowerAtRight f g,
            johnsonSumDotRaiseAtRight f g,
            johnsonDotHarmonicRaise f g hf]
          ring

theorem johnsonCoordinateDot_smul {n : ℕ}
    (c d : ℝ)
    (f g : MetricCodes.Boolean.CoordinateFunction n) :
    MetricCodes.Boolean.coordinateDot
        (fun a => c • f a)
        (fun a => d • g a) =
      (c * d) * MetricCodes.Boolean.coordinateDot f g := by
  classical
  simp only [MetricCodes.Boolean.coordinateDot,
    MetricCodes.Boolean.dot_smul_left,
    MetricCodes.Boolean.dot_smul_right,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem johnsonLowerChannel_orthogonal_middleChannel {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (j + 1) f) :
    MetricCodes.Boolean.coordinateDot
        (johnsonLowerChannel (j + 1) f)
        (johnsonMiddleChannel j g) = 0 := by
  unfold johnsonLowerChannel MetricCodes.Boolean.deleteChannel
    johnsonMiddleChannel
  rw [johnsonCoordinateDot_smul,
    johnsonLowerMiddleRaw_orthogonal f g hf]
  simp

theorem johnsonLowerChannel_orthogonal_upperChannel {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (j + 2) f) :
    MetricCodes.Boolean.coordinateDot
        (johnsonLowerChannel (j + 2) f)
        (johnsonUpperChannel j g) = 0 := by
  unfold johnsonLowerChannel MetricCodes.Boolean.deleteChannel
    johnsonUpperChannel
  rw [johnsonCoordinateDot_smul,
    johnsonLowerUpperRaw_orthogonal f g hf]
  simp

theorem johnsonMiddleChannel_orthogonal_upperChannel {n j : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (j + 1) f)
    (hg : MetricCodes.Boolean.IsHarmonic j g)
    (hhalf : 2 * (j + 1) < n) :
    MetricCodes.Boolean.coordinateDot
        (johnsonMiddleChannel (j + 1) f)
        (johnsonUpperChannel j g) = 0 := by
  unfold johnsonMiddleChannel johnsonUpperChannel
  rw [johnsonCoordinateDot_smul,
    johnsonMiddleUpperRaw_orthogonal f g hf hg hhalf]
  simp

theorem johnsonHarmonic_smul {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) (c : ℝ) :
    MetricCodes.Boolean.IsHarmonic j (c • f) := by
  refine ⟨hf.1.smul c, ?_⟩
  intro S
  rw [MetricCodes.Boolean.lower_smul]
  simp [hf.2 S]

theorem johnsonLowerChannel_isHarmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (j + 1) f)
    (a : Fin n) :
    MetricCodes.Boolean.IsHarmonic j
      (johnsonLowerChannel (j + 1) f a) := by
  change
    MetricCodes.Boolean.IsHarmonic j
      ((Real.sqrt (((j + 1 : ℕ) : ℝ)))⁻¹ •
        MetricCodes.Boolean.lowerAt a f)
  exact johnsonHarmonic_smul
    (MetricCodes.Boolean.lowerAt a f)
    (johnsonLowerAt_harmonic f hf a)
    (Real.sqrt (((j + 1 : ℕ) : ℝ)))⁻¹

theorem johnsonMiddleChannel_isHarmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hhalf : 2 * j < n) (a : Fin n) :
    MetricCodes.Boolean.IsHarmonic j
      (johnsonMiddleChannel j f a) := by
  cases j with
  | zero =>
      have hscale : johnsonMiddleScale n 0 = 0 := by
        simp [johnsonMiddleScale]
      change
        MetricCodes.Boolean.IsHarmonic 0
          ((Real.sqrt (johnsonMiddleScale n 0))⁻¹ •
            johnsonMiddleRaw 0 a f)
      rw [hscale]
      simp only [Real.sqrt_zero, inv_zero, zero_smul]
      simpa using johnsonHarmonic_smul f hf (0 : ℝ)
  | succ j =>
      change
        MetricCodes.Boolean.IsHarmonic (j + 1)
          ((Real.sqrt (johnsonMiddleScale n (j + 1)))⁻¹ •
            johnsonMiddleRaw (j + 1) a f)
      exact johnsonHarmonic_smul
        (johnsonMiddleRaw (j + 1) a f)
        (johnsonMiddleRaw_isHarmonic f hf (by omega) hhalf a)
        (Real.sqrt (johnsonMiddleScale n (j + 1)))⁻¹

theorem johnsonUpperChannel_isHarmonic {n j : ℕ}
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hhalf : 2 * (j + 1) ≤ n) (a : Fin n) :
    MetricCodes.Boolean.IsHarmonic (j + 1)
      (johnsonUpperChannel j f a) := by
  change
    MetricCodes.Boolean.IsHarmonic (j + 1)
      ((Real.sqrt (johnsonUpperScale n j))⁻¹ •
        johnsonUpperRaw j a f)
  exact johnsonHarmonic_smul
    (johnsonUpperRaw j a f)
    (johnsonUpperRaw_isHarmonic f hf hhalf a)
    (Real.sqrt (johnsonUpperScale n j))⁻¹

def johnsonDiagonalChannelSign
    (n w p q j : ℕ) : ℝ :=
  if 0 ≤ MetricCodes.johnsonDiagonal n w p q j then 1 else -1

theorem johnsonDiagonalChannelSign_sq
    (n w p q j : ℕ) :
    johnsonDiagonalChannelSign n w p q j ^ 2 = 1 := by
  unfold johnsonDiagonalChannelSign
  split <;> norm_num

def johnsonAdjacentChannel
    (n w p q L : ℕ)
    (target source : Index p q L)
    (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.CoordinateFunction n :=
  if target.val + 1 = source.val then
    (-1 : ℝ) • johnsonLowerChannel (p + q + source.val) f
  else if target = source then
    johnsonDiagonalChannelSign n w p q (p + q + source.val) •
      johnsonMiddleChannel (p + q + source.val) f
  else if source.val + 1 = target.val then
    (-1 : ℝ) • johnsonUpperChannel (p + q + source.val) f
  else
    0

def johnsonChannelActive
    (p q L : ℕ) (target source : Index p q L) : Prop :=
  target.val + 1 = source.val ∨
    (target = source ∧ 0 < p + q + source.val) ∨
    source.val + 1 = target.val

theorem johnsonSourceChannelCoefficient_eq_zero_of_not_active
    {n w p q L : ℕ}
    (source target : Index p q L)
    (hinactive : ¬ johnsonChannelActive p q L target source) :
    johnsonSourceChannelCoefficient n w p q L source target = 0 := by
  classical
  have hdown : target.val + 1 ≠ source.val := by
    intro h
    exact hinactive (Or.inl h)
  have hup : source.val + 1 ≠ target.val := by
    intro h
    exact hinactive (Or.inr (Or.inr h))
  by_cases heq : source = target
  · subst target
    have hzero : p + q + source.val = 0 := by
      by_contra hnonzero
      apply hinactive
      exact Or.inr
        (Or.inl ⟨rfl, Nat.pos_of_ne_zero hnonzero⟩)
    simp [johnsonSourceChannelCoefficient, matrix,
      MetricCodes.johnsonJacobiMatrix, hzero,
      MetricCodes.johnsonHattedDiagonal]
  · simp [johnsonSourceChannelCoefficient, matrix,
      MetricCodes.johnsonJacobiMatrix, heq, hup, hdown]

theorem johnsonZero_isHarmonic (n j : ℕ) :
    MetricCodes.Boolean.IsHarmonic j
      (0 : MetricCodes.Boolean.Function n) := by
  refine ⟨?_, ?_⟩
  · intro S _
    rfl
  · have hzero :
        MetricCodes.Boolean.lower (0 : MetricCodes.Boolean.Function n) = 0 := by
      change MetricCodes.Boolean.lowerLinear n
        (0 : MetricCodes.Boolean.Function n) = 0
      exact map_zero (MetricCodes.Boolean.lowerLinear n)
    intro S
    exact congrFun hzero S

theorem johnsonMiddleChannel_zero_degree {n : ℕ}
    (f : MetricCodes.Boolean.Function n) :
    johnsonMiddleChannel 0 f = 0 := by
  funext a
  simp [johnsonMiddleChannel, johnsonMiddleScale]

theorem johnsonAdjacentChannel_eq_zero_of_not_active
    {n w p q L : ℕ}
    (target source : Index p q L)
    (f : MetricCodes.Boolean.Function n)
    (hinactive : ¬ johnsonChannelActive p q L target source) :
    johnsonAdjacentChannel n w p q L target source f = 0 := by
  classical
  have hdown : target.val + 1 ≠ source.val := by
    intro h
    exact hinactive (Or.inl h)
  have hup : source.val + 1 ≠ target.val := by
    intro h
    exact hinactive (Or.inr (Or.inr h))
  by_cases heq : target = source
  · subst target
    have hzero : p + q + source.val = 0 := by
      by_contra hnonzero
      exact hinactive
        (Or.inr
          (Or.inl ⟨rfl, Nat.pos_of_ne_zero hnonzero⟩))
    simp [johnsonAdjacentChannel, hzero,
      johnsonMiddleChannel_zero_degree]
  · simp [johnsonAdjacentChannel, hdown, heq, hup]

theorem johnsonCoordinateDot_pi_smul {n : ℕ}
    (c d : ℝ)
    (f g : MetricCodes.Boolean.CoordinateFunction n) :
    MetricCodes.Boolean.coordinateDot (c • f) (d • g) =
      (c * d) * MetricCodes.Boolean.coordinateDot f g := by
  change
    MetricCodes.Boolean.coordinateDot
      (fun a => c • f a)
      (fun a => d • g a) = _
  exact johnsonCoordinateDot_smul c d f g

theorem johnsonAdjacentChannel_isHarmonic
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (target source : Index p q L)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic
      (p + q + source.val) f)
    (a : Fin n) :
    MetricCodes.Boolean.IsHarmonic
      (p + q + target.val)
      (johnsonAdjacentChannel n w p q L target source f a) := by
  classical
  by_cases hdown : target.val + 1 = source.val
  · have hdegree :
        p + q + source.val = (p + q + target.val) + 1 := by
      omega
    have hf' :
        MetricCodes.Boolean.IsHarmonic
          ((p + q + target.val) + 1) f := by
      simpa [hdegree] using hf
    simp only [johnsonAdjacentChannel, hdown, ↓reduceIte,
      Pi.smul_apply]
    rw [hdegree]
    exact johnsonHarmonic_smul
      (johnsonLowerChannel ((p + q + target.val) + 1) f a)
      (johnsonLowerChannel_isHarmonic f hf' a)
      (-1 : ℝ)
  · by_cases hdiag : target = source
    · subst source
      have hdegree := h.window_degree_le_weight target
      have hhalf : 2 * (p + q + target.val) < n := by
        omega
      simp only [johnsonAdjacentChannel, hdown, ↓reduceIte,
        Pi.smul_apply]
      exact johnsonHarmonic_smul
        (johnsonMiddleChannel (p + q + target.val) f a)
        (johnsonMiddleChannel_isHarmonic f hf hhalf a)
        (johnsonDiagonalChannelSign
          n w p q (p + q + target.val))
    · by_cases hup : source.val + 1 = target.val
      · have hdegree :
            (p + q + source.val) + 1 =
              p + q + target.val := by
          omega
        have hhalf := h.window_degree_half target
        have hhalf' :
            2 * ((p + q + source.val) + 1) ≤ n := by
          omega
        simp only [johnsonAdjacentChannel, hdown, hdiag, hup,
          ↓reduceIte, Pi.smul_apply]
        rw [← hdegree]
        exact johnsonHarmonic_smul
          (johnsonUpperChannel (p + q + source.val) f a)
          (johnsonUpperChannel_isHarmonic f hf hhalf' a)
          (-1 : ℝ)
      · simp only [johnsonAdjacentChannel, hdown, hdiag, hup,
          ↓reduceIte, Pi.zero_apply]
        exact johnsonZero_isHarmonic n (p + q + target.val)

theorem johnsonAdjacentChannel_isometry
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (target source : Index p q L)
    (hactive : johnsonChannelActive p q L target source)
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic
      (p + q + source.val) f)
    (hg : MetricCodes.Boolean.IsHarmonic
      (p + q + source.val) g) :
    MetricCodes.Boolean.coordinateDot
        (johnsonAdjacentChannel n w p q L target source f)
        (johnsonAdjacentChannel n w p q L target source g) =
      MetricCodes.Boolean.dot f g := by
  classical
  by_cases hdown : target.val + 1 = source.val
  · simp only [johnsonAdjacentChannel, hdown, ↓reduceIte]
    rw [johnsonCoordinateDot_pi_smul,
      johnsonLowerChannel_isometry f g hf (by omega)]
    norm_num
  · by_cases hdiag : target = source
    · subst target
      have hj : 0 < p + q + source.val := by
        rcases hactive with hfirst | hmiddle | hlast
        · omega
        · exact hmiddle.2
        · omega
      have hdegree := h.window_degree_le_weight source
      have hhalf : 2 * (p + q + source.val) < n := by
        omega
      simp only [johnsonAdjacentChannel, hdown, ↓reduceIte]
      rw [johnsonCoordinateDot_pi_smul,
        johnsonMiddleChannel_isometry f g hf hg hj hhalf,
        ← pow_two,
        johnsonDiagonalChannelSign_sq,
        one_mul]
    · have hup : source.val + 1 = target.val := by
        rcases hactive with hfirst | hmiddle | hlast
        · exact False.elim (hdown hfirst)
        · exact False.elim (hdiag hmiddle.1)
        · exact hlast
      have htarget := h.window_degree_half target
      have hhalf :
          2 * ((p + q + source.val) + 1) ≤ n := by
        omega
      simp only [johnsonAdjacentChannel, hdown, hdiag, hup,
        ↓reduceIte]
      rw [johnsonCoordinateDot_pi_smul,
        johnsonUpperChannel_isometry f g hf hg hhalf]
      norm_num

theorem johnsonAdjacentChannel_orthogonal
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (target source other : Index p q L)
    (hne : source ≠ other)
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic
      (p + q + source.val) f)
    (hg : MetricCodes.Boolean.IsHarmonic
      (p + q + other.val) g) :
    MetricCodes.Boolean.coordinateDot
        (johnsonAdjacentChannel n w p q L target source f)
        (johnsonAdjacentChannel n w p q L target other g) = 0 := by
  classical
  by_cases hs : johnsonChannelActive p q L target source
  swap
  · rw [johnsonAdjacentChannel_eq_zero_of_not_active
      target source f hs]
    simp [MetricCodes.Boolean.coordinateDot, MetricCodes.Boolean.dot]
  by_cases ho : johnsonChannelActive p q L target other
  swap
  · rw [johnsonAdjacentChannel_eq_zero_of_not_active
      target other g ho]
    simp [MetricCodes.Boolean.coordinateDot, MetricCodes.Boolean.dot]
  rcases hs with hsdown | hsdiag | hsup
  · rcases ho with hodown | hodiag | houp
    · exfalso
      apply hne
      apply Fin.ext
      omega
    · rcases hodiag with ⟨hother, _⟩
      subst other
      have hnotdown : target.val + 1 ≠ target.val := by omega
      have hsource_val_ne : source.val ≠ target.val := by omega
      have hdegree :
          p + q + source.val = (p + q + target.val) + 1 := by
        omega
      have hf' :
          MetricCodes.Boolean.IsHarmonic
            ((p + q + target.val) + 1) f := by
        simpa [hdegree] using hf
      simp only [johnsonAdjacentChannel, hsdown,         hsource_val_ne,
        ↓reduceIte]
      rw [hdegree, johnsonCoordinateDot_pi_smul,
        johnsonLowerChannel_orthogonal_middleChannel f g hf']
      ring
    · have hsource_degree :
          p + q + source.val = (p + q + other.val) + 2 := by
        omega
      have hother_notdown : target.val + 1 ≠ other.val := by
        omega
      have hother_notdiag : target ≠ other := by
        intro heq
        subst other
        omega
      have hsource_other_val_ne : source.val ≠ other.val := by
        omega
      have hf' :
          MetricCodes.Boolean.IsHarmonic
            ((p + q + other.val) + 2) f := by
        simpa [hsource_degree] using hf
      simp only [johnsonAdjacentChannel, hsdown,
        hother_notdiag, houp,
        hsource_other_val_ne, ↓reduceIte]
      rw [hsource_degree, johnsonCoordinateDot_pi_smul,
        johnsonLowerChannel_orthogonal_upperChannel f g hf']
      ring
  · rcases hsdiag with ⟨hsource, _⟩
    subst source
    rcases ho with hodown | hodiag | houp
    · have hnotdown : target.val + 1 ≠ target.val := by omega
      have hother_val_ne : other.val ≠ target.val := by omega
      have hother_degree :
          p + q + other.val = (p + q + target.val) + 1 := by
        omega
      have hg' :
          MetricCodes.Boolean.IsHarmonic
            ((p + q + target.val) + 1) g := by
        simpa [hother_degree] using hg
      simp only [johnsonAdjacentChannel,         hodown, hother_val_ne, ↓reduceIte]
      rw [hother_degree, johnsonCoordinateDot_pi_smul,
        MetricCodes.Boolean.coordinateDot_comm,
        johnsonLowerChannel_orthogonal_middleChannel g f hg']
      ring
    · exfalso
      apply hne
      exact hodiag.1
    · have hnotdown : target.val + 1 ≠ target.val := by omega
      have hother_notdown : target.val + 1 ≠ other.val := by
        omega
      have hother_notdiag : target ≠ other := by
        intro heq
        subst other
        omega
      have htarget_degree :
          p + q + target.val = (p + q + other.val) + 1 := by
        omega
      have hf' :
          MetricCodes.Boolean.IsHarmonic
            ((p + q + other.val) + 1) f := by
        simpa [htarget_degree] using hf
      have hhalf :
          2 * ((p + q + other.val) + 1) < n := by
        have hbound := h.window_degree_le_weight target
        omega
      simp only [johnsonAdjacentChannel, hnotdown,
        hother_notdown, hother_notdiag, houp, ↓reduceIte]
      rw [htarget_degree, johnsonCoordinateDot_pi_smul,
        johnsonMiddleChannel_orthogonal_upperChannel
          f g hf' hg hhalf]
      ring
  · rcases ho with hodown | hodiag | houp
    · have hsource_notdown : target.val + 1 ≠ source.val := by
        omega
      have hsource_notdiag : target ≠ source := by
        intro heq
        subst source
        omega
      have hother_source_val_ne : other.val ≠ source.val := by
        omega
      have hother_degree :
          p + q + other.val = (p + q + source.val) + 2 := by
        omega
      have hg' :
          MetricCodes.Boolean.IsHarmonic
            ((p + q + source.val) + 2) g := by
        simpa [hother_degree] using hg
      simp only [johnsonAdjacentChannel,         hsource_notdiag, hsup, hodown,
        hother_source_val_ne, ↓reduceIte]
      rw [hother_degree, johnsonCoordinateDot_pi_smul,
        MetricCodes.Boolean.coordinateDot_comm,
        johnsonLowerChannel_orthogonal_upperChannel g f hg']
      ring
    · rcases hodiag with ⟨hother, _⟩
      subst other
      have hsource_notdown : target.val + 1 ≠ source.val := by
        omega
      have hsource_notdiag : target ≠ source := by
        intro heq
        subst source
        omega
      have hnotdown : target.val + 1 ≠ target.val := by omega
      have htarget_degree :
          p + q + target.val = (p + q + source.val) + 1 := by
        omega
      have hg' :
          MetricCodes.Boolean.IsHarmonic
            ((p + q + source.val) + 1) g := by
        simpa [htarget_degree] using hg
      have hhalf :
          2 * ((p + q + source.val) + 1) < n := by
        have hbound := h.window_degree_le_weight target
        omega
      simp only [johnsonAdjacentChannel, hsource_notdown,
        hsource_notdiag, hsup, hnotdown, ↓reduceIte]
      rw [htarget_degree, johnsonCoordinateDot_pi_smul,
        MetricCodes.Boolean.coordinateDot_comm,
        johnsonMiddleChannel_orthogonal_upperChannel
          g f hg' hf hhalf]
      ring
    · exfalso
      apply hne
      apply Fin.ext
      omega

def johnsonAxisTensor {n w : ℕ}
    (x : JohnsonSphere n w) (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.CoordinateFunction n :=
  fun a => (geometricAxis x a) • f

def johnsonAxisRaise {n w : ℕ}
    (x : JohnsonSphere n w) (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.Function n :=
  fun S => ∑ a : Fin n,
    geometricAxis x a * MetricCodes.Boolean.raiseAt a f S

def johnsonAxisLower {n w : ℕ}
    (x : JohnsonSphere n w) (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.Function n :=
  fun S => ∑ a : Fin n,
    geometricAxis x a * MetricCodes.Boolean.lowerAt a f S

def johnsonAxisMembership {n w : ℕ}
    (x : JohnsonSphere n w) (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.Function n :=
  fun S => ∑ a : Fin n,
    geometricAxis x a *
      MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f) S

theorem sum_geometricAxis {n w : ℕ}
    (hn : 0 < n) (x : JohnsonSphere n w) :
    (∑ a : Fin n, geometricAxis x a) = 0 := by
  classical
  have hn' : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hweight : MetricCodes.binaryWeight (x : BinaryWord n) = w :=
    x.property
  change
    (∑ a : Fin n,
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
          (coordinateIndicator (x : BinaryWord n) a -
            (w : ℝ) / (n : ℝ))) = 0
  rw [← Finset.mul_sum, Finset.sum_sub_distrib,
    sum_coordinateIndicator, hweight]
  simp only [Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hn']
  ring

theorem johnsonDot_axisRaise {n w : ℕ}
    (x : JohnsonSphere n w)
    (f g : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.dot f (johnsonAxisRaise x g) =
      ∑ a : Fin n,
        geometricAxis x a *
          MetricCodes.Boolean.dot f (MetricCodes.Boolean.raiseAt a g) := by
  classical
  unfold MetricCodes.Boolean.dot johnsonAxisRaise
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem johnsonDot_axisLower {n w : ℕ}
    (x : JohnsonSphere n w)
    (f g : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.dot f (johnsonAxisLower x g) =
      ∑ a : Fin n,
        geometricAxis x a *
          MetricCodes.Boolean.dot f (MetricCodes.Boolean.lowerAt a g) := by
  classical
  unfold MetricCodes.Boolean.dot johnsonAxisLower
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem johnsonDot_axisMembership {n w : ℕ}
    (x : JohnsonSphere n w)
    (f g : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.dot f (johnsonAxisMembership x g) =
      ∑ a : Fin n,
        geometricAxis x a *
          MetricCodes.Boolean.dot f
            (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)) := by
  classical
  unfold MetricCodes.Boolean.dot johnsonAxisMembership
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem johnsonLowerChannel_axis_inner {n w j : ℕ}
    (x : JohnsonSphere n w)
    (f g : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.coordinateDot (johnsonLowerChannel j f)
      (johnsonAxisTensor x g) =
        (Real.sqrt (j : ℝ))⁻¹ *
          MetricCodes.Boolean.dot f (johnsonAxisRaise x g) := by
  classical
  unfold MetricCodes.Boolean.coordinateDot johnsonLowerChannel
    MetricCodes.Boolean.deleteChannel johnsonAxisTensor
  simp only [MetricCodes.Boolean.dot_smul_left,
    MetricCodes.Boolean.dot_smul_right]
  simp_rw [MetricCodes.Boolean.dot_lowerAt_eq_raiseAt]
  rw [johnsonDot_axisRaise, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem johnsonUpperRaw_dot_harmonic_right {n j k : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hg : MetricCodes.Boolean.IsHarmonic k g) (a : Fin n) :
    MetricCodes.Boolean.dot (johnsonUpperRaw j a f) g =
      MetricCodes.Boolean.dot (MetricCodes.Boolean.raiseAt a f) g := by
  simp only [johnsonUpperRaw,
    johnsonBooleanDot_sub_left,
    johnsonBooleanDot_add_left,
    MetricCodes.Boolean.dot_smul_left]
  rw [johnsonDotRaise_harmonic_right f g hg,
    johnsonDotRaise_harmonic_right
      (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a f)) g hg,
    johnsonDotRaise_harmonic_right
      (MetricCodes.Boolean.raise (MetricCodes.Boolean.lowerAt a f)) g hg]
  ring

theorem johnsonUpperChannel_axis_inner {n w j k : ℕ}
    (x : JohnsonSphere n w)
    (f g : MetricCodes.Boolean.Function n)
    (hg : MetricCodes.Boolean.IsHarmonic k g) :
    MetricCodes.Boolean.coordinateDot (johnsonUpperChannel j f)
      (johnsonAxisTensor x g) =
        (Real.sqrt (johnsonUpperScale n j))⁻¹ *
          MetricCodes.Boolean.dot f (johnsonAxisLower x g) := by
  classical
  unfold MetricCodes.Boolean.coordinateDot johnsonUpperChannel
    johnsonAxisTensor
  simp only [MetricCodes.Boolean.dot_smul_left,
    MetricCodes.Boolean.dot_smul_right]
  simp_rw [johnsonUpperRaw_dot_harmonic_right f g hg,
    MetricCodes.Boolean.dot_raiseAt_eq_lowerAt]
  rw [johnsonDot_axisLower, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem johnsonMiddleRaw_dot_harmonic_right {n j k : ℕ}
    (f g : MetricCodes.Boolean.Function n)
    (hg : MetricCodes.Boolean.IsHarmonic k g) (a : Fin n) :
    MetricCodes.Boolean.dot (johnsonMiddleRaw j a f) g =
      MetricCodes.Boolean.dot f
          (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)) -
        ((j : ℝ) / (n : ℝ)) * MetricCodes.Boolean.dot f g := by
  simp only [johnsonMiddleRaw,
    johnsonBooleanDot_sub_left,
    MetricCodes.Boolean.dot_smul_left]
  rw [johnsonDotRaise_harmonic_right
    (MetricCodes.Boolean.lowerAt a f) g hg,
    MetricCodes.Boolean.dot_raiseAt_eq_lowerAt,
    MetricCodes.Boolean.dot_lowerAt_eq_raiseAt]
  ring

theorem johnsonMiddleChannel_axis_inner {n w j k : ℕ}
    (hn : 0 < n) (x : JohnsonSphere n w)
    (f g : MetricCodes.Boolean.Function n)
    (hg : MetricCodes.Boolean.IsHarmonic k g) :
    MetricCodes.Boolean.coordinateDot (johnsonMiddleChannel j f)
      (johnsonAxisTensor x g) =
        (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          MetricCodes.Boolean.dot f (johnsonAxisMembership x g) := by
  classical
  unfold MetricCodes.Boolean.coordinateDot johnsonMiddleChannel
    johnsonAxisTensor
  simp only [MetricCodes.Boolean.dot_smul_left,
    MetricCodes.Boolean.dot_smul_right]
  simp_rw [johnsonMiddleRaw_dot_harmonic_right f g hg]
  rw [johnsonDot_axisMembership]
  have hcenter := sum_geometricAxis hn x
  calc
    (∑ a : Fin n,
      geometricAxis x a *
        ((Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          (MetricCodes.Boolean.dot f
              (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)) -
            ((j : ℝ) / (n : ℝ)) * MetricCodes.Boolean.dot f g))) =
      (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
        (∑ a : Fin n,
          (geometricAxis x a *
            MetricCodes.Boolean.dot f
              (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g)) -
            ((j : ℝ) / (n : ℝ)) * MetricCodes.Boolean.dot f g *
              geometricAxis x a)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
        ((∑ a : Fin n,
          geometricAxis x a *
            MetricCodes.Boolean.dot f
              (MetricCodes.Boolean.raiseAt a (MetricCodes.Boolean.lowerAt a g))) -
          ((j : ℝ) / (n : ℝ)) * MetricCodes.Boolean.dot f g *
            (∑ a : Fin n, geometricAxis x a)) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by rw [hcenter]; ring

theorem sum_coordinateIndicator_on_subset {n w : ℕ}
    (x : JohnsonSphere n w) (S : Finset (Fin n)) :
    (∑ a : Fin n,
      if a ∈ S then coordinateIndicator (x : BinaryWord n) a else 0) =
      (((coordinateSplitEquiv x S).1).card : ℝ) := by
  classical
  calc
    (∑ a : Fin n,
      if a ∈ S then coordinateIndicator (x : BinaryWord n) a else 0) =
      ∑ a : SupportCoordinates x ⊕ ComplementCoordinates x,
        if coordinateSumEquiv x a ∈ S then
          coordinateIndicator (x : BinaryWord n)
            (coordinateSumEquiv x a)
        else 0 := by
          exact ((coordinateSumEquiv x).sum_comp
            (fun a : Fin n =>
              if a ∈ S then
                coordinateIndicator (x : BinaryWord n) a
              else 0)).symm
    _ = ∑ a : SupportCoordinates x,
          if a ∈ (coordinateSplitEquiv x S).1 then (1 : ℝ)
          else 0 := by
          rw [Fintype.sum_sum_type]
          have hsupport (a : SupportCoordinates x) :
              coordinateIndicator (x : BinaryWord n)
                (a : Fin n) = 1 := by
            simp [coordinateIndicator, a.property]
          have hcomplement (a : ComplementCoordinates x) :
              coordinateIndicator (x : BinaryWord n)
                (a : Fin n) = 0 := by
            have ha :
                (a : Fin n) ∉
                  MetricCodes.wordSupport (x : BinaryWord n) := by
              exact (Finset.mem_sdiff.mp a.property).2
            simp [coordinateIndicator, ha]
          have hinl (i : SupportCoordinates x) :
              coordinateSumEquiv x (Sum.inl i) = (i : Fin n) := rfl
          have hinr (i : ComplementCoordinates x) :
              coordinateSumEquiv x (Sum.inr i) = (i : Fin n) := rfl
          simp_rw [hinl, hinr, hsupport, hcomplement]
          simp only [ite_self, Finset.sum_const_zero, add_zero]
          apply Finset.sum_congr rfl
          intro a _
          by_cases ha : (a : Fin n) ∈ S
          · have ha' : a ∈ (coordinateSplitEquiv x S).1 :=
              (coordinateSplitEquiv_mem_support x a S).mpr ha
            simp [ha, ha']
          · have ha' : a ∉ (coordinateSplitEquiv x S).1 := by
              intro hmem
              exact ha
                ((coordinateSplitEquiv_mem_support x a S).mp hmem)
            simp [ha, ha']
    _ = (((coordinateSplitEquiv x S).1).card : ℝ) := by
          rw [Finset.sum_ite_mem, Finset.univ_inter]
          simp

theorem sum_geometricAxis_on_subset {n w : ℕ}
    (x : JohnsonSphere n w) (S : Finset (Fin n)) :
    (∑ a : Fin n,
      if a ∈ S then geometricAxis x a else 0) =
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
          ((((coordinateSplitEquiv x S).1).card : ℝ) -
            (w : ℝ) / (n : ℝ) * (S.card : ℝ)) := by
  classical
  change
    (∑ a : Fin n,
      if a ∈ S then
        Real.sqrt ((n : ℝ) /
          ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
            (coordinateIndicator (x : BinaryWord n) a -
              (w : ℝ) / (n : ℝ))
      else 0) = _
  calc
    (∑ a : Fin n,
      if a ∈ S then
        Real.sqrt ((n : ℝ) /
          ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
            (coordinateIndicator (x : BinaryWord n) a -
              (w : ℝ) / (n : ℝ))
      else 0) =
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        ((∑ a : Fin n,
          if a ∈ S then coordinateIndicator (x : BinaryWord n) a
          else 0) -
          (∑ a : Fin n,
            if a ∈ S then (w : ℝ) / (n : ℝ) else 0)) := by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a ∈ S <;> simp [ha] ; ring
    _ = _ := by
      rw [sum_coordinateIndicator_on_subset x S,
        MetricCodes.Boolean.sum_mem_indicator]
      ring

theorem johnsonAxisMembership_apply {n w : ℕ}
    (x : JohnsonSphere n w)
    (f : MetricCodes.Boolean.Function n)
    (S : Finset (Fin n)) :
    johnsonAxisMembership x f S =
      (∑ a : Fin n,
        if a ∈ S then geometricAxis x a else 0) * f S := by
  classical
  unfold johnsonAxisMembership
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [MetricCodes.Boolean.raiseAt_lowerAt_self]
  by_cases ha : a ∈ S <;> simp [ha]

theorem johnsonAxisMembership_splitTensor {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) (r s : ℕ) :
    johnsonAxisMembership x (splitTensor x hp hq a r s) =
      (Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (((p + r : ℕ) : ℝ) -
          (w : ℝ) / (n : ℝ) *
            (((p + r) + (q + s) : ℕ) : ℝ))) •
        splitTensor x hp hq a r s := by
  classical
  funext S
  rw [johnsonAxisMembership_apply,
    sum_geometricAxis_on_subset]
  by_cases hsupport :
      ((coordinateSplitEquiv x S).1).card = p + r
  swap
  · have hzero : splitTensor x hp hq a r s S = 0 := by
      unfold splitTensor
      rw [supportRaisedFunction_eq_zero_of_card_ne
        x hp a.1 r (coordinateSplitEquiv x S).1 hsupport,
        zero_mul]
    simp [hzero]
  by_cases hcomplement :
      ((coordinateSplitEquiv x S).2).card = q + s
  swap
  · have hzero : splitTensor x hp hq a r s S = 0 := by
      unfold splitTensor
      rw [complementRaisedFunction_eq_zero_of_card_ne
        x hq a.2 s (coordinateSplitEquiv x S).2 hcomplement,
        mul_zero]
    simp [hzero]
  have hcard : S.card = (p + r) + (q + s) := by
    have hsplit := coordinateSplitEquiv_card x S
    omega
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hsupport, hcard]

theorem johnsonAxisMembership_smul {n w : ℕ}
    (x : JohnsonSphere n w) (c : ℝ)
    (f : MetricCodes.Boolean.Function n) :
    johnsonAxisMembership x (c • f) =
      c • johnsonAxisMembership x f := by
  classical
  funext S
  simp only [johnsonAxisMembership, Pi.smul_apply, smul_eq_mul,
    MetricCodes.Boolean.raiseAt, MetricCodes.Boolean.lowerAt]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ S <;> simp [ha] ; ring

theorem johnsonDot_fintype_weighted_sum_right
    {n : ℕ} {ι : Type*} [Fintype ι]
    (f : MetricCodes.Boolean.Function n)
    (c : ι → ℝ)
    (g : ι → MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.dot f
        (fun S => ∑ i : ι, c i * g i S) =
      ∑ i : ι, c i * MetricCodes.Boolean.dot f (g i) := by
  classical
  unfold MetricCodes.Boolean.dot
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem johnsonAxisMembership_coupledTensor {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) (t : ℕ) :
    johnsonAxisMembership x (coupledTensor x hp hq a t) =
      fun S =>
        ∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val *
            (Real.sqrt ((n : ℝ) /
              ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
                (((p + r.val : ℕ) : ℝ) -
                  (w : ℝ) / (n : ℝ) *
                    ((p + q + t : ℕ) : ℝ))) *
            splitTensor x hp hq a r.val (t - r.val) S := by
  classical
  funext S
  rw [johnsonAxisMembership_apply]
  change
    (∑ b : Fin n,
      if b ∈ S then geometricAxis x b else 0) *
        (∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val *
            splitTensor x hp hq a r.val (t - r.val) S) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hr : r.val ≤ t := by
    have hlt := r.isLt
    omega
  have hdegree :
      (p + r.val) + (q + (t - r.val)) = p + q + t := by
    omega
  have hsplit := congrFun
    (johnsonAxisMembership_splitTensor
      x hp hq a r.val (t - r.val)) S
  rw [johnsonAxisMembership_apply] at hsplit
  simp only [Pi.smul_apply, smul_eq_mul, hdegree] at hsplit
  calc
    (∑ b : Fin n,
        if b ∈ S then geometricAxis x b else 0) *
        (clebschCoefficient w (n - w) p q t r.val *
          splitTensor x hp hq a r.val (t - r.val) S) =
      clebschCoefficient w (n - w) p q t r.val *
        ((∑ b : Fin n,
          if b ∈ S then geometricAxis x b else 0) *
          splitTensor x hp hq a r.val (t - r.val) S) := by
      ring
    _ = _ := by rw [hsplit]; ring

theorem johnsonAxisMembership_coupledHarmonic_dot
    {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (t : ℕ) (f : MetricCodes.Boolean.Function n) :
    MetricCodes.Boolean.dot f
        (johnsonAxisMembership x
          (coupledHarmonic x hp hq a t)) =
      (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
        Real.sqrt ((n : ℝ) /
          ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val *
            (((p + r.val : ℕ) : ℝ) -
              (w : ℝ) / (n : ℝ) *
                ((p + q + t : ℕ) : ℝ)) *
            MetricCodes.Boolean.dot f
              (splitTensor x hp hq a r.val (t - r.val))) := by
  unfold coupledHarmonic
  rw [johnsonAxisMembership_smul,
    MetricCodes.Boolean.dot_smul_right,
    johnsonAxisMembership_coupledTensor]
  rw [johnsonDot_fintype_weighted_sum_right]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem coordinateSplitEquiv_erase_support {n w : ℕ}
    (x : JohnsonSphere n w) (i : SupportCoordinates x)
    (S : Finset (Fin n)) :
    coordinateSplitEquiv x (S.erase (i : Fin n)) =
      (((coordinateSplitEquiv x S).1).erase i,
        (coordinateSplitEquiv x S).2) := by
  apply Prod.ext
  · change
      (((coordinateSumEquiv x).symm.finsetCongr
        (S.erase (i : Fin n))).toLeft) =
        (((coordinateSumEquiv x).symm.finsetCongr S).toLeft).erase i
    ext j
    simp [Equiv.finsetCongr_apply, Finset.map_erase,
      Finset.mem_toLeft]
  · change
      (((coordinateSumEquiv x).symm.finsetCongr
        (S.erase (i : Fin n))).toRight) =
        (((coordinateSumEquiv x).symm.finsetCongr S).toRight)
    ext j
    simp [Equiv.finsetCongr_apply, Finset.map_erase,
      Finset.mem_toRight]

theorem coordinateSplitEquiv_erase_complement {n w : ℕ}
    (x : JohnsonSphere n w) (i : ComplementCoordinates x)
    (S : Finset (Fin n)) :
    coordinateSplitEquiv x (S.erase (i : Fin n)) =
      ((coordinateSplitEquiv x S).1,
        ((coordinateSplitEquiv x S).2).erase i) := by
  apply Prod.ext
  · change
      (((coordinateSumEquiv x).symm.finsetCongr
        (S.erase (i : Fin n))).toLeft) =
        (((coordinateSumEquiv x).symm.finsetCongr S).toLeft)
    ext j
    simp [Equiv.finsetCongr_apply, Finset.map_erase,
      Finset.mem_toLeft]
  · change
      (((coordinateSumEquiv x).symm.finsetCongr
        (S.erase (i : Fin n))).toRight) =
        (((coordinateSumEquiv x).symm.finsetCongr S).toRight).erase i
    ext j
    simp [Equiv.finsetCongr_apply, Finset.map_erase,
      Finset.mem_toRight]

def coordinateRaise {α : Type*} [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ) (S : Finset α) : ℝ :=
  ∑ i : α, if i ∈ S then f (S.erase i) else 0

theorem coordinateRaise_reindex
    {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (e : α ≃ Fin m) (f : MetricCodes.Boolean.Function m)
    (S : Finset α) :
    coordinateRaise
        (fun T : Finset α => f (e.finsetCongr T)) S =
      MetricCodes.Boolean.raise f (e.finsetCongr S) := by
  classical
  unfold coordinateRaise MetricCodes.Boolean.raise MetricCodes.Boolean.raiseAt
  calc
    (∑ i : α,
      if i ∈ S then f (e.finsetCongr (S.erase i)) else 0) =
      ∑ i : α,
        if e i ∈ e.finsetCongr S then
          f ((e.finsetCongr S).erase (e i))
        else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp [Equiv.finsetCongr_apply, Finset.map_erase]
    _ = ∑ i : Fin m,
        if i ∈ e.finsetCongr S then
          f ((e.finsetCongr S).erase i)
        else 0 := by
      exact e.sum_comp (fun i : Fin m =>
        if i ∈ e.finsetCongr S then
          f ((e.finsetCongr S).erase i)
        else 0)

theorem supportRaisedFunction_raise {n w p r : ℕ}
    (x : JohnsonSphere n w) (hp : 2 * p ≤ w)
    (hbound : 2 * p + (r + 1) ≤ w)
    (a : Fin (MetricCodes.hammingFibreDimension w p))
    (S : Finset (SupportCoordinates x)) :
    coordinateRaise (supportRaisedFunction x hp a r) S =
      Real.sqrt (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) *
        supportRaisedFunction x hp a (r + 1) S := by
  unfold supportRaisedFunction
  rw [coordinateRaise_reindex,
    MetricCodes.Boolean.raise_harmonicEmbedding
      (MetricCodes.Boolean.harmonicBasisFunction w p hp a) r hbound]
  rfl

theorem complementRaisedFunction_raise {n w q r : ℕ}
    (x : JohnsonSphere n w) (hq : 2 * q ≤ n - w)
    (hbound : 2 * q + (r + 1) ≤ n - w)
    (a : Fin (MetricCodes.hammingFibreDimension (n - w) q))
    (S : Finset (ComplementCoordinates x)) :
    coordinateRaise (complementRaisedFunction x hq a r) S =
      Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient (n - w) q (r + 1)) *
        complementRaisedFunction x hq a (r + 1) S := by
  unfold complementRaisedFunction
  rw [coordinateRaise_reindex,
    MetricCodes.Boolean.raise_harmonicEmbedding
      (MetricCodes.Boolean.harmonicBasisFunction (n - w) q hq a)
        r hbound]
  rfl

theorem raise_splitTensor {n w p q : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) (r s : ℕ)
    (S : Finset (Fin n)) :
    MetricCodes.Boolean.raise (splitTensor x hp hq a r s) S =
      coordinateRaise (supportRaisedFunction x hp a.1 r)
          (coordinateSplitEquiv x S).1 *
        complementRaisedFunction x hq a.2 s
          (coordinateSplitEquiv x S).2 +
      supportRaisedFunction x hp a.1 r
          (coordinateSplitEquiv x S).1 *
        coordinateRaise (complementRaisedFunction x hq a.2 s)
          (coordinateSplitEquiv x S).2 := by
  classical
  calc
    MetricCodes.Boolean.raise (splitTensor x hp hq a r s) S =
      ∑ i : SupportCoordinates x ⊕ ComplementCoordinates x,
        if coordinateSumEquiv x i ∈ S then
          splitTensor x hp hq a r s
            (S.erase (coordinateSumEquiv x i))
        else 0 := by
      unfold MetricCodes.Boolean.raise MetricCodes.Boolean.raiseAt
      symm
      exact (coordinateSumEquiv x).sum_comp
        (fun i : Fin n =>
          if i ∈ S then
            splitTensor x hp hq a r s (S.erase i)
          else 0)
    _ =
      (∑ i : SupportCoordinates x,
        if (i : Fin n) ∈ S then
          splitTensor x hp hq a r s (S.erase (i : Fin n))
        else 0) +
      (∑ i : ComplementCoordinates x,
        if (i : Fin n) ∈ S then
          splitTensor x hp hq a r s (S.erase (i : Fin n))
        else 0) := by
      rw [Fintype.sum_sum_type]
      simp [coordinateSumEquiv, complementNegEquiv]
    _ = _ := by
      congr 1
      · calc
          (∑ i : SupportCoordinates x,
            if (i : Fin n) ∈ S then
              splitTensor x hp hq a r s (S.erase (i : Fin n))
            else 0) =
            ∑ i : SupportCoordinates x,
              (if i ∈ (coordinateSplitEquiv x S).1 then
                supportRaisedFunction x hp a.1 r
                  (((coordinateSplitEquiv x S).1).erase i)
              else 0) *
                complementRaisedFunction x hq a.2 s
                  (coordinateSplitEquiv x S).2 := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : (i : Fin n) ∈ S
            · have hi' : i ∈ (coordinateSplitEquiv x S).1 :=
                (coordinateSplitEquiv_mem_support x i S).mpr hi
              simp [hi, hi', splitTensor,
                coordinateSplitEquiv_erase_support]
            · have hi' : i ∉ (coordinateSplitEquiv x S).1 := by
                intro hmem
                exact hi
                  ((coordinateSplitEquiv_mem_support x i S).mp hmem)
              simp [hi, hi']
          _ = _ := by
            unfold coordinateRaise
            rw [Finset.sum_mul]
      · calc
          (∑ i : ComplementCoordinates x,
            if (i : Fin n) ∈ S then
              splitTensor x hp hq a r s (S.erase (i : Fin n))
            else 0) =
            ∑ i : ComplementCoordinates x,
              supportRaisedFunction x hp a.1 r
                (coordinateSplitEquiv x S).1 *
              (if i ∈ (coordinateSplitEquiv x S).2 then
                complementRaisedFunction x hq a.2 s
                  (((coordinateSplitEquiv x S).2).erase i)
              else 0) := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : (i : Fin n) ∈ S
            · have hi' : i ∈ (coordinateSplitEquiv x S).2 :=
                (coordinateSplitEquiv_mem_complement x i S).mpr hi
              simp [hi, hi', splitTensor,
                coordinateSplitEquiv_erase_complement]
            · have hi' : i ∉ (coordinateSplitEquiv x S).2 := by
                intro hmem
                exact hi
                  ((coordinateSplitEquiv_mem_complement x i S).mp hmem)
              simp [hi, hi']
          _ = _ := by
            unfold coordinateRaise
            rw [Finset.mul_sum]

theorem raise_splitTensor_eq {n w p q r s : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (hsupport : 2 * p + (r + 1) ≤ w)
    (hcomplement : 2 * q + (s + 1) ≤ n - w)
    (a : HarmonicFibreIndex n w p q) :
    MetricCodes.Boolean.raise (splitTensor x hp hq a r s) =
      Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) •
        splitTensor x hp hq a (r + 1) s +
      Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient (n - w) q (s + 1)) •
        splitTensor x hp hq a r (s + 1) := by
  funext S
  rw [raise_splitTensor,
    supportRaisedFunction_raise x hp hsupport,
    complementRaisedFunction_raise x hq hcomplement]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    splitTensor]
  ring

theorem johnsonHarmonic_dot_splitTensor_succ_mul
    {n w p q t r : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + t ≤ w)
    (htcomplement : 2 * q + t ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + t) f)
    (hr : r < t) :
    Real.sqrt
        (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) *
      MetricCodes.Boolean.dot f
        (splitTensor x hp hq a (r + 1) (t - (r + 1))) =
      -Real.sqrt
        (MetricCodes.Boolean.harmonicCoefficient (n - w) q (t - r)) *
          MetricCodes.Boolean.dot f
            (splitTensor x hp hq a r (t - r)) := by
  have hsupport : 2 * p + (r + 1) ≤ w := by omega
  have hresidual : (t - (r + 1)) + 1 = t - r := by omega
  have hcomplement :
      2 * q + ((t - (r + 1)) + 1) ≤ n - w := by
    omega
  have hzero := johnsonDotHarmonicRaise f
    (splitTensor x hp hq a r (t - (r + 1))) hf
  rw [raise_splitTensor_eq x hp hq hsupport hcomplement a,
    MetricCodes.Boolean.dot_add_right,
    MetricCodes.Boolean.dot_smul_right,
    MetricCodes.Boolean.dot_smul_right,
    hresidual] at hzero
  linarith

theorem johnsonHarmonic_dot_splitTensor_eq_clebschCoefficient
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + t ≤ w)
    (htcomplement : 2 * q + t ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + t) f)
    (r : ℕ) (hr : r ≤ t) :
    MetricCodes.Boolean.dot f
        (splitTensor x hp hq a r (t - r)) =
      clebschCoefficient w (n - w) p q t r *
        MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t) := by
  induction r with
  | zero =>
      simp [clebschCoefficient]
  | succ r ihr =>
      have hr' : r < t := by omega
      have hbound : 2 * p + (r + 1) ≤ w := by omega
      have hsqrt :
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) ≠ 0 := by
        exact (Real.sqrt_pos.mpr
          (MetricCodes.Boolean.harmonicCoefficient_pos
            (Nat.succ_pos r) hbound)).ne'
      have hrec := johnsonHarmonic_dot_splitTensor_succ_mul
        x hp hq htsupport htcomplement a f hf hr'
      rw [ihr (by omega)] at hrec
      have hclebsch := clebschCoefficient_succ_mul
        (w := w) (N := n - w) (p := p) (q := q)
        (t := t) (r := r) hbound
      apply (mul_left_cancel₀ hsqrt)
      calc
        Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) *
            MetricCodes.Boolean.dot f
              (splitTensor x hp hq a (r + 1) (t - (r + 1))) =
          -Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient (n - w) q (t - r)) *
              (clebschCoefficient w (n - w) p q t r *
                MetricCodes.Boolean.dot f
                  (splitTensor x hp hq a 0 t)) := hrec
        _ = (Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) *
              clebschCoefficient w (n - w) p q t (r + 1)) *
                MetricCodes.Boolean.dot f
                  (splitTensor x hp hq a 0 t) := by
              rw [mul_comm
                (Real.sqrt
                  (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)))
                (clebschCoefficient w (n - w) p q t (r + 1)),
                hclebsch]
              ring
        _ = Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) *
              (clebschCoefficient w (n - w) p q t (r + 1) *
                MetricCodes.Boolean.dot f
                  (splitTensor x hp hq a 0 t)) := by
              ring

theorem johnsonHarmonic_dot_coupledHarmonic
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + t ≤ w)
    (htcomplement : 2 * q + t ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + t) f) :
    MetricCodes.Boolean.dot f (coupledHarmonic x hp hq a t) =
      Real.sqrt (clebschNormSq w (n - w) p q t) *
        MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t) := by
  have hnorm := clebschNormSq_pos w (n - w) p q t
  have hsqrt : Real.sqrt (clebschNormSq w (n - w) p q t) ≠ 0 :=
    (Real.sqrt_pos.mpr hnorm).ne'
  unfold coupledHarmonic
  rw [MetricCodes.Boolean.dot_smul_right]
  change
    (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
      MetricCodes.Boolean.dot f
        (fun S => ∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val *
            splitTensor x hp hq a r.val (t - r.val) S) = _
  rw [johnsonDot_fintype_weighted_sum_right]
  simp_rw [johnsonHarmonic_dot_splitTensor_eq_clebschCoefficient
    x hp hq htsupport htcomplement a f hf _
      (Nat.le_of_lt_succ (Fin.isLt _))]
  have hsq := Real.sq_sqrt hnorm.le
  have hscalar :
      (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
        clebschNormSq w (n - w) p q t =
      Real.sqrt (clebschNormSq w (n - w) p q t) := by
    field_simp [hsqrt]
    nlinarith [hsq]
  calc
    (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
        (∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val *
            (clebschCoefficient w (n - w) p q t r.val *
              MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t))) =
      (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
        (clebschNormSq w (n - w) p q t *
          MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t)) := by
      congr 1
      unfold clebschNormSq
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by rw [← mul_assoc, hscalar]

theorem sum_coordinateIndicator_mul_function {n w : ℕ}
    (x : JohnsonSphere n w) (F : Fin n → ℝ) :
    (∑ i : Fin n,
      coordinateIndicator (x : BinaryWord n) i * F i) =
      ∑ i : SupportCoordinates x, F (i : Fin n) := by
  classical
  calc
    (∑ i : Fin n,
      coordinateIndicator (x : BinaryWord n) i * F i) =
      ∑ i ∈ MetricCodes.wordSupport (x : BinaryWord n), F i := by
        calc
          (∑ i : Fin n,
            coordinateIndicator (x : BinaryWord n) i * F i) =
            ∑ i : Fin n,
              if i ∈ MetricCodes.wordSupport (x : BinaryWord n) then
                F i
              else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : i ∈ MetricCodes.wordSupport (x : BinaryWord n)
            <;> simp [coordinateIndicator, hi]
          _ = _ := by
            rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ i : SupportCoordinates x, F (i : Fin n) := by
      exact Finset.sum_subtype
        (MetricCodes.wordSupport (x : BinaryWord n))
        (fun i => Iff.rfl) F

def johnsonSupportRaise {n w : ℕ}
    (x : JohnsonSphere n w)
    (f : MetricCodes.Boolean.Function n) : MetricCodes.Boolean.Function n :=
  fun S => ∑ i : SupportCoordinates x,
    MetricCodes.Boolean.raiseAt (i : Fin n) f S

def johnsonSupportLower {n w : ℕ}
    (x : JohnsonSphere n w)
    (f : MetricCodes.Boolean.Function n) : MetricCodes.Boolean.Function n :=
  fun S => ∑ i : SupportCoordinates x,
    MetricCodes.Boolean.lowerAt (i : Fin n) f S

theorem johnsonAxisRaise_eq_support {n w : ℕ}
    (x : JohnsonSphere n w)
    (f : MetricCodes.Boolean.Function n) :
    johnsonAxisRaise x f =
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) •
          (johnsonSupportRaise x f -
            ((w : ℝ) / (n : ℝ)) • MetricCodes.Boolean.raise f) := by
  classical
  funext S
  change
    (∑ i : Fin n,
      (Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (coordinateIndicator (x : BinaryWord n) i -
          (w : ℝ) / (n : ℝ))) *
        MetricCodes.Boolean.raiseAt i f S) = _
  have hsupport := sum_coordinateIndicator_mul_function x
    (fun i : Fin n => MetricCodes.Boolean.raiseAt i f S)
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    johnsonSupportRaise, MetricCodes.Boolean.raise]
  calc
    (∑ i : Fin n,
      (Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (coordinateIndicator (x : BinaryWord n) i -
          (w : ℝ) / (n : ℝ))) *
        MetricCodes.Boolean.raiseAt i f S) =
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        ((∑ i : Fin n,
          coordinateIndicator (x : BinaryWord n) i *
            MetricCodes.Boolean.raiseAt i f S) -
          (w : ℝ) / (n : ℝ) *
            (∑ i : Fin n, MetricCodes.Boolean.raiseAt i f S)) := by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hsupport]

theorem johnsonAxisLower_eq_support {n w : ℕ}
    (x : JohnsonSphere n w)
    (f : MetricCodes.Boolean.Function n) :
    johnsonAxisLower x f =
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) •
          (johnsonSupportLower x f -
            ((w : ℝ) / (n : ℝ)) • MetricCodes.Boolean.lower f) := by
  classical
  funext S
  change
    (∑ i : Fin n,
      (Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (coordinateIndicator (x : BinaryWord n) i -
          (w : ℝ) / (n : ℝ))) *
        MetricCodes.Boolean.lowerAt i f S) = _
  have hsupport := sum_coordinateIndicator_mul_function x
    (fun i : Fin n => MetricCodes.Boolean.lowerAt i f S)
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    johnsonSupportLower, MetricCodes.Boolean.lower]
  calc
    (∑ i : Fin n,
      (Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (coordinateIndicator (x : BinaryWord n) i -
          (w : ℝ) / (n : ℝ))) *
        MetricCodes.Boolean.lowerAt i f S) =
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        ((∑ i : Fin n,
          coordinateIndicator (x : BinaryWord n) i *
            MetricCodes.Boolean.lowerAt i f S) -
          (w : ℝ) / (n : ℝ) *
            (∑ i : Fin n, MetricCodes.Boolean.lowerAt i f S)) := by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hsupport]

theorem johnsonAxisRaise_dot_harmonic_left {n w j : ℕ}
    (x : JohnsonSphere n w)
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) :
    MetricCodes.Boolean.dot f (johnsonAxisRaise x g) =
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
          MetricCodes.Boolean.dot f (johnsonSupportRaise x g) := by
  rw [johnsonAxisRaise_eq_support,
    MetricCodes.Boolean.dot_smul_right,
    johnsonBooleanDot_sub_right,
    MetricCodes.Boolean.dot_smul_right,
    johnsonDotHarmonicRaise f g hf]
  ring

theorem johnsonAxisLower_eq_support_of_harmonic {n w j : ℕ}
    (x : JohnsonSphere n w)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) :
    johnsonAxisLower x f =
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) •
          johnsonSupportLower x f := by
  rw [johnsonAxisLower_eq_support]
  have hzero : MetricCodes.Boolean.lower f = 0 := funext hf.2
  rw [hzero]
  simp

theorem johnsonSupportRaise_smul {n w : ℕ}
    (x : JohnsonSphere n w) (c : ℝ)
    (f : MetricCodes.Boolean.Function n) :
    johnsonSupportRaise x (c • f) = c • johnsonSupportRaise x f := by
  classical
  funext S
  unfold johnsonSupportRaise MetricCodes.Boolean.raiseAt
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (i : Fin n) ∈ S <;> simp [hi]

theorem johnsonSupportLower_smul {n w : ℕ}
    (x : JohnsonSphere n w) (c : ℝ)
    (f : MetricCodes.Boolean.Function n) :
    johnsonSupportLower x (c • f) = c • johnsonSupportLower x f := by
  classical
  funext S
  unfold johnsonSupportLower MetricCodes.Boolean.lowerAt
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (i : Fin n) ∈ S <;> simp [hi]

theorem johnsonSupportRaise_fintype_weighted_sum
    {n w : ℕ} {ι : Type*} [Fintype ι]
    (x : JohnsonSphere n w)
    (c : ι → ℝ) (f : ι → MetricCodes.Boolean.Function n) :
    johnsonSupportRaise x
        (fun S => ∑ i : ι, c i * f i S) =
      fun S => ∑ i : ι, c i * johnsonSupportRaise x (f i) S := by
  classical
  funext S
  unfold johnsonSupportRaise MetricCodes.Boolean.raiseAt
  calc
    (∑ a : SupportCoordinates x,
      if (a : Fin n) ∈ S then
        ∑ i : ι, c i * f i (S.erase (a : Fin n))
      else 0) =
      ∑ a : SupportCoordinates x, ∑ i : ι,
        c i *
          (if (a : Fin n) ∈ S then f i (S.erase (a : Fin n))
           else 0) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : (a : Fin n) ∈ S <;> simp [ha]
    _ = ∑ i : ι, ∑ a : SupportCoordinates x,
        c i *
          (if (a : Fin n) ∈ S then f i (S.erase (a : Fin n))
           else 0) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]

theorem johnsonSupportLower_fintype_weighted_sum
    {n w : ℕ} {ι : Type*} [Fintype ι]
    (x : JohnsonSphere n w)
    (c : ι → ℝ) (f : ι → MetricCodes.Boolean.Function n) :
    johnsonSupportLower x
        (fun S => ∑ i : ι, c i * f i S) =
      fun S => ∑ i : ι, c i * johnsonSupportLower x (f i) S := by
  classical
  funext S
  unfold johnsonSupportLower MetricCodes.Boolean.lowerAt
  calc
    (∑ a : SupportCoordinates x,
      if (a : Fin n) ∈ S then 0
      else ∑ i : ι, c i * f i (insert (a : Fin n) S)) =
      ∑ a : SupportCoordinates x, ∑ i : ι,
        c i *
          (if (a : Fin n) ∈ S then 0
           else f i (insert (a : Fin n) S)) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : (a : Fin n) ∈ S <;> simp [ha]
    _ = ∑ i : ι, ∑ a : SupportCoordinates x,
        c i *
          (if (a : Fin n) ∈ S then 0
           else f i (insert (a : Fin n) S)) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]

theorem johnsonSupportRaise_splitTensor {n w p q r s : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (hsupport : 2 * p + (r + 1) ≤ w)
    (a : HarmonicFibreIndex n w p q) :
    johnsonSupportRaise x (splitTensor x hp hq a r s) =
      Real.sqrt
        (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) •
          splitTensor x hp hq a (r + 1) s := by
  classical
  funext S
  change
    (∑ i : SupportCoordinates x,
      if (i : Fin n) ∈ S then
        splitTensor x hp hq a r s (S.erase (i : Fin n))
      else 0) = _
  have hcomponent :
      (∑ i : SupportCoordinates x,
        if (i : Fin n) ∈ S then
          splitTensor x hp hq a r s (S.erase (i : Fin n))
        else 0) =
      coordinateRaise (supportRaisedFunction x hp a.1 r)
          (coordinateSplitEquiv x S).1 *
        complementRaisedFunction x hq a.2 s
          (coordinateSplitEquiv x S).2 := by
    unfold coordinateRaise
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (i : Fin n) ∈ S
    · have hi' : i ∈ (coordinateSplitEquiv x S).1 :=
        (coordinateSplitEquiv_mem_support x i S).mpr hi
      simp [hi, hi', splitTensor,
        coordinateSplitEquiv_erase_support]
    · have hi' : i ∉ (coordinateSplitEquiv x S).1 := by
        intro hmem
        exact hi
          ((coordinateSplitEquiv_mem_support x i S).mp hmem)
      simp [hi, hi']
  rw [hcomponent, supportRaisedFunction_raise x hp hsupport]
  simp [splitTensor, mul_assoc]

theorem johnsonSupportLower_splitTensor_succ {n w p q r s : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (hsupport : 2 * p + (r + 1) ≤ w)
    (a : HarmonicFibreIndex n w p q) :
    johnsonSupportLower x (splitTensor x hp hq a (r + 1) s) =
      Real.sqrt
        (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) •
          splitTensor x hp hq a r s := by
  classical
  funext S
  change
    (∑ i : SupportCoordinates x,
      if (i : Fin n) ∈ S then 0
      else splitTensor x hp hq a (r + 1) s
        (insert (i : Fin n) S)) = _
  have hcomponent :
      (∑ i : SupportCoordinates x,
        if (i : Fin n) ∈ S then 0
        else splitTensor x hp hq a (r + 1) s
          (insert (i : Fin n) S)) =
      coordinateLower (supportRaisedFunction x hp a.1 (r + 1))
          (coordinateSplitEquiv x S).1 *
        complementRaisedFunction x hq a.2 s
          (coordinateSplitEquiv x S).2 := by
    unfold coordinateLower
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (i : Fin n) ∈ S
    · have hi' : i ∈ (coordinateSplitEquiv x S).1 :=
        (coordinateSplitEquiv_mem_support x i S).mpr hi
      simp [hi, hi']
    · have hi' : i ∉ (coordinateSplitEquiv x S).1 := by
        intro hmem
        exact hi
          ((coordinateSplitEquiv_mem_support x i S).mp hmem)
      simp [hi, hi', splitTensor,
        coordinateSplitEquiv_insert_support]
  rw [hcomponent, supportRaisedFunction_lower x hp hsupport]
  simp [splitTensor, mul_assoc]

theorem johnsonSupportLower_splitTensor_zero {n w p q s : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q) :
    johnsonSupportLower x (splitTensor x hp hq a 0 s) = 0 := by
  classical
  funext S
  change
    (∑ i : SupportCoordinates x,
      if (i : Fin n) ∈ S then 0
      else splitTensor x hp hq a 0 s
        (insert (i : Fin n) S)) = 0
  have hcomponent :
      (∑ i : SupportCoordinates x,
        if (i : Fin n) ∈ S then 0
        else splitTensor x hp hq a 0 s
          (insert (i : Fin n) S)) =
      coordinateLower (supportRaisedFunction x hp a.1 0)
          (coordinateSplitEquiv x S).1 *
        complementRaisedFunction x hq a.2 s
          (coordinateSplitEquiv x S).2 := by
    unfold coordinateLower
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (i : Fin n) ∈ S
    · have hi' : i ∈ (coordinateSplitEquiv x S).1 :=
        (coordinateSplitEquiv_mem_support x i S).mpr hi
      simp [hi, hi']
    · have hi' : i ∉ (coordinateSplitEquiv x S).1 := by
        intro hmem
        exact hi
          ((coordinateSplitEquiv_mem_support x i S).mp hmem)
      simp [hi, hi', splitTensor,
        coordinateSplitEquiv_insert_support]
  rw [hcomponent, supportRaisedFunction_lower_zero]
  ring

theorem johnsonSupportRaise_coupledTensor {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (hsupport : 2 * p + (t + 1) ≤ w)
    (a : HarmonicFibreIndex n w p q) :
    johnsonSupportRaise x (coupledTensor x hp hq a t) =
      fun S => ∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q t r.val *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
          splitTensor x hp hq a (r.val + 1) (t - r.val) S := by
  change
    johnsonSupportRaise x
        (fun S => ∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val *
            splitTensor x hp hq a r.val (t - r.val) S) = _
  rw [johnsonSupportRaise_fintype_weighted_sum]
  funext S
  apply Finset.sum_congr rfl
  intro r _
  have hr : r.val ≤ t := by
    have hlt := r.isLt
    omega
  have hbound : 2 * p + (r.val + 1) ≤ w := by omega
  rw [johnsonSupportRaise_splitTensor x hp hq hbound a]
  simp [mul_assoc]

theorem johnsonSupportLower_coupledTensor_succ
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (hsupport : 2 * p + (t + 1) ≤ w)
    (a : HarmonicFibreIndex n w p q) :
    johnsonSupportLower x (coupledTensor x hp hq a (t + 1)) =
      fun S => ∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q (t + 1) (r.val + 1) *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
          splitTensor x hp hq a r.val (t - r.val) S := by
  change
    johnsonSupportLower x
        (fun S => ∑ r : Fin ((t + 1) + 1),
          clebschCoefficient w (n - w) p q (t + 1) r.val *
            splitTensor x hp hq a r.val ((t + 1) - r.val) S) = _
  rw [johnsonSupportLower_fintype_weighted_sum]
  funext S
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.sub_zero,
    johnsonSupportLower_splitTensor_zero, Pi.zero_apply,
    mul_zero, zero_add, Fin.val_succ]
  apply Finset.sum_congr rfl
  intro r _
  have hr : r.val ≤ t := by
    have hlt := r.isLt
    omega
  have hbound : 2 * p + (r.val + 1) ≤ w := by omega
  have hresidual : (t + 1) - (r.val + 1) = t - r.val := by
    omega
  rw [hresidual,
    johnsonSupportLower_splitTensor_succ x hp hq hbound a]
  simp [mul_assoc]

theorem johnsonAxisRaise_coupledHarmonic_dot
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + (t + 1) ≤ w)
    (htcomplement : 2 * q + (t + 1) ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + (t + 1)) f) :
    MetricCodes.Boolean.dot f
        (johnsonAxisRaise x (coupledHarmonic x hp hq a t)) =
      Real.sqrt ((n : ℝ) /
          ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
        (Real.sqrt (clebschNormSq w (n - w) p q (t + 1)))⁻¹ *
        (∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val *
            Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
            clebschCoefficient w (n - w) p q (t + 1)
              (r.val + 1)) *
        MetricCodes.Boolean.dot f
          (coupledHarmonic x hp hq a (t + 1)) := by
  classical
  have hnorm := clebschNormSq_pos w (n - w) p q (t + 1)
  have hsqrt :
      Real.sqrt (clebschNormSq w (n - w) p q (t + 1)) ≠ 0 :=
    (Real.sqrt_pos.mpr hnorm).ne'
  have hbase := johnsonHarmonic_dot_coupledHarmonic
    x hp hq htsupport htcomplement a f hf
  rw [johnsonAxisRaise_dot_harmonic_left x f _ hf]
  change
    Real.sqrt ((n : ℝ) /
      ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
      MetricCodes.Boolean.dot f
        (johnsonSupportRaise x
          ((Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ •
            coupledTensor x hp hq a t)) = _
  rw [johnsonSupportRaise_smul,
    MetricCodes.Boolean.dot_smul_right,
    johnsonSupportRaise_coupledTensor x hp hq htsupport a,
    johnsonDot_fintype_weighted_sum_right]
  have hpair (r : Fin (t + 1)) :
      MetricCodes.Boolean.dot f
          (splitTensor x hp hq a (r.val + 1) (t - r.val)) =
        clebschCoefficient w (n - w) p q (t + 1) (r.val + 1) *
          MetricCodes.Boolean.dot f
            (splitTensor x hp hq a 0 (t + 1)) := by
    have hr : r.val ≤ t := by
      have hlt := r.isLt
      omega
    have hresidual :
        (t + 1) - (r.val + 1) = t - r.val := by omega
    simpa [hresidual] using
      (johnsonHarmonic_dot_splitTensor_eq_clebschCoefficient
        x hp hq htsupport htcomplement a f hf
          (r.val + 1) (by omega))
  simp_rw [hpair]
  rw [hbase]
  have hsum :
      (∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q t r.val *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
          (clebschCoefficient w (n - w) p q (t + 1)
            (r.val + 1) *
              MetricCodes.Boolean.dot f
                (splitTensor x hp hq a 0 (t + 1)))) =
      (∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q t r.val *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
          clebschCoefficient w (n - w) p q (t + 1)
            (r.val + 1)) *
        MetricCodes.Boolean.dot f
          (splitTensor x hp hq a 0 (t + 1)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hsum]
  have hcancel :
      (Real.sqrt (clebschNormSq w (n - w) p q (t + 1)))⁻¹ *
        Real.sqrt (clebschNormSq w (n - w) p q (t + 1)) = 1 :=
    inv_mul_cancel₀ hsqrt
  calc
    Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
      ((Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
        ((∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val *
            Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
            clebschCoefficient w (n - w) p q (t + 1)
              (r.val + 1)) *
          MetricCodes.Boolean.dot f
            (splitTensor x hp hq a 0 (t + 1)))) =
      Real.sqrt ((n : ℝ) /
          ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
        (Real.sqrt (clebschNormSq w (n - w) p q (t + 1)))⁻¹ *
        (∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val *
            Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
            clebschCoefficient w (n - w) p q (t + 1)
              (r.val + 1)) *
        (Real.sqrt (clebschNormSq w (n - w) p q (t + 1)) *
          MetricCodes.Boolean.dot f
            (splitTensor x hp hq a 0 (t + 1))) := by
      calc
        _ = Real.sqrt ((n : ℝ) /
            ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
          (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
          (∑ r : Fin (t + 1),
            clebschCoefficient w (n - w) p q t r.val *
              Real.sqrt
                (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
              clebschCoefficient w (n - w) p q (t + 1)
                (r.val + 1)) *
          (((Real.sqrt (clebschNormSq w (n - w) p q (t + 1)))⁻¹ *
              Real.sqrt (clebschNormSq w (n - w) p q (t + 1))) *
            MetricCodes.Boolean.dot f
              (splitTensor x hp hq a 0 (t + 1))) := by
          rw [hcancel]
          ring
        _ = _ := by ring

theorem johnsonAxisLower_coupledHarmonic_dot
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + (t + 1) ≤ w)
    (htcomplement : 2 * q + (t + 1) ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + t) f) :
    MetricCodes.Boolean.dot f
        (johnsonAxisLower x
          (coupledHarmonic x hp hq a (t + 1))) =
      Real.sqrt ((n : ℝ) /
          ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (Real.sqrt (clebschNormSq w (n - w) p q (t + 1)))⁻¹ *
        (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
        (∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q (t + 1)
              (r.val + 1) *
            Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
            clebschCoefficient w (n - w) p q t r.val) *
        MetricCodes.Boolean.dot f (coupledHarmonic x hp hq a t) := by
  classical
  have hsupport : 2 * p + t ≤ w := by omega
  have hcomplement : 2 * q + t ≤ n - w := by omega
  have htarget := coupledHarmonic_isHarmonic
    x hp hq htsupport htcomplement a
  have hnorm := clebschNormSq_pos w (n - w) p q t
  have hsqrt : Real.sqrt (clebschNormSq w (n - w) p q t) ≠ 0 :=
    (Real.sqrt_pos.mpr hnorm).ne'
  have hbase := johnsonHarmonic_dot_coupledHarmonic
    x hp hq hsupport hcomplement a f hf
  rw [johnsonAxisLower_eq_support_of_harmonic x _ htarget,
    MetricCodes.Boolean.dot_smul_right]
  change
    Real.sqrt ((n : ℝ) /
      ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
      MetricCodes.Boolean.dot f
        (johnsonSupportLower x
          ((Real.sqrt
            (clebschNormSq w (n - w) p q (t + 1)))⁻¹ •
              coupledTensor x hp hq a (t + 1))) = _
  rw [johnsonSupportLower_smul,
    MetricCodes.Boolean.dot_smul_right,
    johnsonSupportLower_coupledTensor_succ x hp hq htsupport a,
    johnsonDot_fintype_weighted_sum_right]
  have hpair (r : Fin (t + 1)) :
      MetricCodes.Boolean.dot f
          (splitTensor x hp hq a r.val (t - r.val)) =
        clebschCoefficient w (n - w) p q t r.val *
          MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t) :=
    johnsonHarmonic_dot_splitTensor_eq_clebschCoefficient
      x hp hq hsupport hcomplement a f hf r.val
        (by have hr := r.isLt; omega)
  simp_rw [hpair]
  rw [hbase]
  have hsum :
      (∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q (t + 1)
            (r.val + 1) *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
          (clebschCoefficient w (n - w) p q t r.val *
            MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t))) =
      (∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q (t + 1)
            (r.val + 1) *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
          clebschCoefficient w (n - w) p q t r.val) *
        MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hsum]
  have hcancel :
      (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
        Real.sqrt (clebschNormSq w (n - w) p q t) = 1 :=
    inv_mul_cancel₀ hsqrt
  calc
    Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
      ((Real.sqrt
        (clebschNormSq w (n - w) p q (t + 1)))⁻¹ *
        ((∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q (t + 1)
              (r.val + 1) *
            Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
            clebschCoefficient w (n - w) p q t r.val) *
          MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t))) =
      Real.sqrt ((n : ℝ) /
          ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (Real.sqrt
          (clebschNormSq w (n - w) p q (t + 1)))⁻¹ *
        (Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
        (∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q (t + 1)
              (r.val + 1) *
            Real.sqrt
              (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
            clebschCoefficient w (n - w) p q t r.val) *
        (Real.sqrt (clebschNormSq w (n - w) p q t) *
          MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t)) := by
      calc
        _ = Real.sqrt ((n : ℝ) /
            ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
          (Real.sqrt
            (clebschNormSq w (n - w) p q (t + 1)))⁻¹ *
          (∑ r : Fin (t + 1),
            clebschCoefficient w (n - w) p q (t + 1)
                (r.val + 1) *
              Real.sqrt
                (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
              clebschCoefficient w (n - w) p q t r.val) *
          (((Real.sqrt (clebschNormSq w (n - w) p q t))⁻¹ *
              Real.sqrt (clebschNormSq w (n - w) p q t)) *
            MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t)) := by
          rw [hcancel]
          ring
        _ = _ := by ring

end MetricCodes.Johnson

end

end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators InnerProductSpace Matrix

namespace MetricCodes.Johnson

theorem clebschCoefficient_sq_succ_mul
    {w N p q t r : ℕ}
    (hsupport : 2 * p + (r + 1) ≤ w)
    (hcomplement : 2 * q + t ≤ N) :
    clebschCoefficient w N p q t (r + 1) ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient w p (r + 1) =
      clebschCoefficient w N p q t r ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient N q (t - r) := by
  have hfirst :
      0 < MetricCodes.Boolean.harmonicCoefficient w p (r + 1) :=
    MetricCodes.Boolean.harmonicCoefficient_pos
      (Nat.succ_pos r) hsupport
  have hsecond :
      0 ≤ MetricCodes.Boolean.harmonicCoefficient N q (t - r) := by
    by_cases hzero : t - r = 0
    · simp [hzero]
    · exact
        (MetricCodes.Boolean.harmonicCoefficient_pos
          (Nat.pos_of_ne_zero hzero) (by omega)).le
  calc
    clebschCoefficient w N p q t (r + 1) ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient w p (r + 1) =
      (clebschCoefficient w N p q t (r + 1) *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient w p (r + 1))) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hfirst.le]
    _ = (-clebschCoefficient w N p q t r *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient N q (t - r))) ^ 2 := by
        rw [clebschCoefficient_succ_mul hsupport]
    _ = clebschCoefficient w N p q t r ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient N q (t - r) := by
        rw [mul_pow, Real.sq_sqrt hsecond]
        ring

def clebschFirstMoment (w N p q t : ℕ) : ℝ :=
  ∑ r : Fin (t + 1),
    (r.val : ℝ) * clebschCoefficient w N p q t r.val ^ 2

def clebschSecondMoment (w N p q t : ℕ) : ℝ :=
  ∑ r : Fin (t + 1),
    (r.val : ℝ) ^ 2 * clebschCoefficient w N p q t r.val ^ 2

theorem clebschCoefficient_sq_harmonic_balance
    {w N p q t : ℕ}
    (hsupport : 2 * p + t ≤ w)
    (hcomplement : 2 * q + t ≤ N) :
    (∑ r : Fin (t + 1),
      clebschCoefficient w N p q t r.val ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient w p r.val) =
      ∑ r : Fin (t + 1),
        clebschCoefficient w N p q t r.val ^ 2 *
          MetricCodes.Boolean.harmonicCoefficient N q (t - r.val) := by
  classical
  calc
    (∑ r : Fin (t + 1),
      clebschCoefficient w N p q t r.val ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient w p r.val) =
      ∑ r : Fin t,
        clebschCoefficient w N p q t (r.val + 1) ^ 2 *
          MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1) := by
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, Fin.val_succ,
          MetricCodes.Boolean.harmonicCoefficient_zero,
          mul_zero, zero_add]
    _ = ∑ r : Fin t,
        clebschCoefficient w N p q t r.val ^ 2 *
          MetricCodes.Boolean.harmonicCoefficient N q (t - r.val) := by
        apply Finset.sum_congr rfl
        intro r _
        apply clebschCoefficient_sq_succ_mul
        · have hr := r.isLt
          omega
        · exact hcomplement
    _ = ∑ r : Fin (t + 1),
        clebschCoefficient w N p q t r.val ^ 2 *
          MetricCodes.Boolean.harmonicCoefficient N q (t - r.val) := by
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last,
          Nat.sub_self, MetricCodes.Boolean.harmonicCoefficient_zero,
          mul_zero, add_zero]

theorem clebsch_support_moment_expansion
    (w N p q t : ℕ) :
    (∑ r : Fin (t + 1),
      clebschCoefficient w N p q t r.val ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient w p r.val) =
      ((w : ℝ) - 2 * (p : ℝ) + 1) *
          clebschFirstMoment w N p q t -
        clebschSecondMoment w N p q t := by
  classical
  unfold clebschFirstMoment clebschSecondMoment
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  unfold MetricCodes.Boolean.harmonicCoefficient
  ring

theorem clebsch_complement_moment_expansion
    (w N p q t : ℕ) :
    (∑ r : Fin (t + 1),
      clebschCoefficient w N p q t r.val ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient N q (t - r.val)) =
      (t : ℝ) * ((N : ℝ) - 2 * (q : ℝ) - (t : ℝ) + 1) *
          clebschNormSq w N p q t +
        (2 * (t : ℝ) - ((N : ℝ) - 2 * (q : ℝ)) - 1) *
          clebschFirstMoment w N p q t -
        clebschSecondMoment w N p q t := by
  classical
  unfold clebschNormSq clebschFirstMoment clebschSecondMoment
  rw [Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  have hr : r.val ≤ t := by
    have hlt := r.isLt
    omega
  simp only [MetricCodes.Boolean.harmonicCoefficient, Nat.cast_sub hr]
  ring

theorem clebschFirstMoment_mul
    {w N p q t : ℕ}
    (hsupport : 2 * p + t ≤ w)
    (hcomplement : 2 * q + t ≤ N) :
    (((w : ℝ) - 2 * (p : ℝ)) +
      ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 2) *
        clebschFirstMoment w N p q t =
      (t : ℝ) * ((N : ℝ) - 2 * (q : ℝ) - (t : ℝ) + 1) *
        clebschNormSq w N p q t := by
  classical
  have hbalance :=
    clebschCoefficient_sq_harmonic_balance hsupport hcomplement
  have hsupport' := clebsch_support_moment_expansion w N p q t
  have hcomplement' := clebsch_complement_moment_expansion w N p q t
  calc
    (((w : ℝ) - 2 * (p : ℝ)) +
      ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 2) *
        clebschFirstMoment w N p q t =
      (((w : ℝ) - 2 * (p : ℝ) + 1) *
          clebschFirstMoment w N p q t -
        clebschSecondMoment w N p q t) -
        ((2 * (t : ℝ) - ((N : ℝ) - 2 * (q : ℝ)) - 1) *
          clebschFirstMoment w N p q t -
        clebschSecondMoment w N p q t) := by
          ring
    _ = (∑ r : Fin (t + 1),
          clebschCoefficient w N p q t r.val ^ 2 *
            MetricCodes.Boolean.harmonicCoefficient w p r.val) -
        ((2 * (t : ℝ) - ((N : ℝ) - 2 * (q : ℝ)) - 1) *
          clebschFirstMoment w N p q t -
        clebschSecondMoment w N p q t) := by
          rw [hsupport']
    _ = (∑ r : Fin (t + 1),
          clebschCoefficient w N p q t r.val ^ 2 *
            MetricCodes.Boolean.harmonicCoefficient N q (t - r.val)) -
        ((2 * (t : ℝ) - ((N : ℝ) - 2 * (q : ℝ)) - 1) *
          clebschFirstMoment w N p q t -
        clebschSecondMoment w N p q t) := by
          rw [hbalance]
    _ = (t : ℝ) *
        ((N : ℝ) - 2 * (q : ℝ) - (t : ℝ) + 1) *
          clebschNormSq w N p q t := by
          rw [hcomplement']
          ring

theorem clebschFirstMoment_eq
    {w N p q t : ℕ}
    (hsupport : 2 * p + t ≤ w)
    (hcomplement : 2 * q + t ≤ N) :
    clebschFirstMoment w N p q t =
      ((t : ℝ) * ((N : ℝ) - 2 * (q : ℝ) - (t : ℝ) + 1) *
        clebschNormSq w N p q t) /
        (((w : ℝ) - 2 * (p : ℝ)) +
          ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 2) := by
  have hfirst :
      2 * (p : ℝ) + (t : ℝ) ≤ (w : ℝ) := by
    exact_mod_cast hsupport
  have hsecond :
      2 * (q : ℝ) + (t : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hcomplement
  have hdenominator :
      0 < (((w : ℝ) - 2 * (p : ℝ)) +
        ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 2) := by
    linarith only [hfirst, hsecond]
  apply (eq_div_iff hdenominator.ne').2
  calc
    clebschFirstMoment w N p q t *
        (((w : ℝ) - 2 * (p : ℝ)) +
          ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 2) =
      (((w : ℝ) - 2 * (p : ℝ)) +
        ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 2) *
        clebschFirstMoment w N p q t := by
          ring
    _ = (t : ℝ) *
        ((N : ℝ) - 2 * (q : ℝ) - (t : ℝ) + 1) *
          clebschNormSq w N p q t :=
      clebschFirstMoment_mul hsupport hcomplement

theorem clebschCoefficient_sq_weighted_harmonic_balance
    {w N p q t : ℕ}
    (hsupport : 2 * p + t ≤ w)
    (hcomplement : 2 * q + t ≤ N) :
    (∑ r : Fin (t + 1),
      ((r.val : ℝ) - 1) *
        (clebschCoefficient w N p q t r.val ^ 2 *
          MetricCodes.Boolean.harmonicCoefficient w p r.val)) =
      ∑ r : Fin (t + 1),
        (r.val : ℝ) *
          (clebschCoefficient w N p q t r.val ^ 2 *
            MetricCodes.Boolean.harmonicCoefficient N q (t - r.val)) := by
  classical
  calc
    (∑ r : Fin (t + 1),
      ((r.val : ℝ) - 1) *
        (clebschCoefficient w N p q t r.val ^ 2 *
          MetricCodes.Boolean.harmonicCoefficient w p r.val)) =
      ∑ r : Fin t,
        (r.val : ℝ) *
          (clebschCoefficient w N p q t (r.val + 1) ^ 2 *
            MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) := by
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, Fin.val_succ,
          Nat.cast_zero, Nat.cast_add, Nat.cast_one,
          MetricCodes.Boolean.harmonicCoefficient_zero,
          mul_zero, add_sub_cancel_right, zero_add]
    _ = ∑ r : Fin t,
        (r.val : ℝ) *
          (clebschCoefficient w N p q t r.val ^ 2 *
            MetricCodes.Boolean.harmonicCoefficient N q (t - r.val)) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [clebschCoefficient_sq_succ_mul
          (by have hr := r.isLt; omega) hcomplement]
    _ = ∑ r : Fin (t + 1),
        (r.val : ℝ) *
          (clebschCoefficient w N p q t r.val ^ 2 *
            MetricCodes.Boolean.harmonicCoefficient N q (t - r.val)) := by
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last,
          Nat.sub_self, MetricCodes.Boolean.harmonicCoefficient_zero,
          mul_zero, add_zero]

theorem clebschSecondMoment_mul
    {w N p q t : ℕ}
    (hsupport : 2 * p + t ≤ w)
    (hcomplement : 2 * q + t ≤ N) :
    (((w : ℝ) - 2 * (p : ℝ)) +
      ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 3) *
        clebschSecondMoment w N p q t =
      (((w : ℝ) - 2 * (p : ℝ)) +
        ((N : ℝ) - 2 * (q : ℝ)) * (t : ℝ) -
        (t : ℝ) ^ 2 + (t : ℝ) + 1) *
        clebschFirstMoment w N p q t := by
  classical
  have hbalance :=
    clebschCoefficient_sq_weighted_harmonic_balance
      hsupport hcomplement
  apply sub_eq_zero.mp
  calc
    (((w : ℝ) - 2 * (p : ℝ)) +
      ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 3) *
        clebschSecondMoment w N p q t -
      (((w : ℝ) - 2 * (p : ℝ)) +
        ((N : ℝ) - 2 * (q : ℝ)) * (t : ℝ) -
        (t : ℝ) ^ 2 + (t : ℝ) + 1) *
        clebschFirstMoment w N p q t =
      ∑ r : Fin (t + 1),
        (((r.val : ℝ) - 1) *
          (clebschCoefficient w N p q t r.val ^ 2 *
            MetricCodes.Boolean.harmonicCoefficient w p r.val) -
          (r.val : ℝ) *
            (clebschCoefficient w N p q t r.val ^ 2 *
              MetricCodes.Boolean.harmonicCoefficient N q (t - r.val))) := by
        unfold clebschFirstMoment clebschSecondMoment
        rw [Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro r _
        have hr : r.val ≤ t := by
          have hlt := r.isLt
          omega
        simp only [MetricCodes.Boolean.harmonicCoefficient,
          Nat.cast_sub hr]
        ring
    _ = (∑ r : Fin (t + 1),
          ((r.val : ℝ) - 1) *
            (clebschCoefficient w N p q t r.val ^ 2 *
              MetricCodes.Boolean.harmonicCoefficient w p r.val)) -
        ∑ r : Fin (t + 1),
          (r.val : ℝ) *
            (clebschCoefficient w N p q t r.val ^ 2 *
              MetricCodes.Boolean.harmonicCoefficient N q (t - r.val)) := by
          rw [Finset.sum_sub_distrib]
    _ = 0 := by
      rw [hbalance]
      ring

theorem clebschCoefficient_cross_degree_mul
    {w N p q t r : ℕ}
    (hsupport : 2 * p + t ≤ w)
    (hr : r ≤ t) :
    clebschCoefficient w N p q (t + 1) r *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient N q (t + 1 - r)) =
      clebschCoefficient w N p q t r *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient N q (t + 1)) := by
  have hall : ∀ s : ℕ, s ≤ t →
      clebschCoefficient w N p q (t + 1) s *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient N q (t + 1 - s)) =
        clebschCoefficient w N p q t s *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient N q (t + 1)) := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
        intro hs
        cases s with
        | zero =>
            simp [clebschCoefficient]
        | succ r =>
            have hbound : 2 * p + (r + 1) ≤ w := by
              omega
            have hpositive :
                0 < MetricCodes.Boolean.harmonicCoefficient
                  w p (r + 1) :=
              MetricCodes.Boolean.harmonicCoefficient_pos
                (Nat.succ_pos r) hbound
            have hnonzero :
                Real.sqrt
                  (MetricCodes.Boolean.harmonicCoefficient
                    w p (r + 1)) ≠ 0 :=
              (Real.sqrt_pos.mpr hpositive).ne'
            have hprevious := ih r (by omega) (by omega)
            have hnew := clebschCoefficient_succ_mul
              (w := w) (N := N) (p := p) (q := q)
              (t := t + 1) (r := r) hbound
            have hold := clebschCoefficient_succ_mul
              (w := w) (N := N) (p := p) (q := q)
              (t := t) (r := r) hbound
            have hsub : t + 1 - (r + 1) = t - r := by
              omega
            apply (mul_right_inj' hnonzero).mp
            rw [hsub]
            calc
              Real.sqrt
                  (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) *
                (clebschCoefficient w N p q (t + 1) (r + 1) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t - r))) =
                (clebschCoefficient w N p q (t + 1) (r + 1) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t - r))) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) := by
                    ring
              _ = (clebschCoefficient w N p q (t + 1) (r + 1) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient w p (r + 1))) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t - r)) := by
                    ring
              _ = (-clebschCoefficient w N p q (t + 1) r *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t + 1 - r))) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t - r)) := by
                    rw [hnew]
              _ = -(clebschCoefficient w N p q (t + 1) r *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t + 1 - r))) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t - r)) := by
                    ring
              _ = -(clebschCoefficient w N p q t r *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t + 1))) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t - r)) := by
                    rw [hprevious]
              _ = (clebschCoefficient w N p q t (r + 1) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient w p (r + 1))) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t + 1)) := by
                    rw [hold]
                    ring
              _ = (clebschCoefficient w N p q t (r + 1) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient N q (t + 1))) *
                  Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) := by
                    ring
              _ = Real.sqrt
                    (MetricCodes.Boolean.harmonicCoefficient w p (r + 1)) *
                  (clebschCoefficient w N p q t (r + 1) *
                    Real.sqrt
                      (MetricCodes.Boolean.harmonicCoefficient N q (t + 1))) := by
                    ring
  exact hall r hr

theorem clebschCoefficient_sq_cross_degree_mul
    {w N p q t r : ℕ}
    (hsupport : 2 * p + t ≤ w)
    (hcomplement : 2 * q + (t + 1) ≤ N)
    (hr : r ≤ t) :
    clebschCoefficient w N p q (t + 1) r ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient N q (t + 1 - r) =
      clebschCoefficient w N p q t r ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient N q (t + 1) := by
  have hleft :
      0 ≤ MetricCodes.Boolean.harmonicCoefficient N q (t + 1 - r) := by
    by_cases hzero : t + 1 - r = 0
    · simp [hzero]
    · exact
        (MetricCodes.Boolean.harmonicCoefficient_pos
          (Nat.pos_of_ne_zero hzero) (by omega)).le
  have hright :
      0 < MetricCodes.Boolean.harmonicCoefficient N q (t + 1) :=
    MetricCodes.Boolean.harmonicCoefficient_pos
      (Nat.succ_pos t) hcomplement
  calc
    clebschCoefficient w N p q (t + 1) r ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient N q (t + 1 - r) =
      (clebschCoefficient w N p q (t + 1) r *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient N q (t + 1 - r))) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hleft]
    _ = (clebschCoefficient w N p q t r *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient N q (t + 1))) ^ 2 := by
        rw [clebschCoefficient_cross_degree_mul hsupport hr]
    _ = clebschCoefficient w N p q t r ^ 2 *
        MetricCodes.Boolean.harmonicCoefficient N q (t + 1) := by
        rw [mul_pow, Real.sq_sqrt hright.le]

theorem clebschNormSq_cross_degree_harmonic_balance
    {w N p q t : ℕ}
    (hsupport : 2 * p + (t + 1) ≤ w)
    (hcomplement : 2 * q + (t + 1) ≤ N) :
    MetricCodes.Boolean.harmonicCoefficient N q (t + 1) *
        clebschNormSq w N p q t =
      ∑ r : Fin ((t + 1) + 1),
        clebschCoefficient w N p q (t + 1) r.val ^ 2 *
          MetricCodes.Boolean.harmonicCoefficient N q
            (t + 1 - r.val) := by
  classical
  calc
    MetricCodes.Boolean.harmonicCoefficient N q (t + 1) *
        clebschNormSq w N p q t =
      ∑ r : Fin (t + 1),
        clebschCoefficient w N p q t r.val ^ 2 *
          MetricCodes.Boolean.harmonicCoefficient N q (t + 1) := by
        unfold clebschNormSq
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
    _ = ∑ r : Fin (t + 1),
        clebschCoefficient w N p q (t + 1) r.val ^ 2 *
          MetricCodes.Boolean.harmonicCoefficient N q
            (t + 1 - r.val) := by
        apply Finset.sum_congr rfl
        intro r _
        symm
        apply clebschCoefficient_sq_cross_degree_mul
        · omega
        · exact hcomplement
        · have hr := r.isLt
          omega
    _ = ∑ r : Fin ((t + 1) + 1),
        clebschCoefficient w N p q (t + 1) r.val ^ 2 *
          MetricCodes.Boolean.harmonicCoefficient N q
            (t + 1 - r.val) := by
        symm
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last,
          Nat.sub_self, MetricCodes.Boolean.harmonicCoefficient_zero,
          mul_zero, add_zero]

set_option maxHeartbeats 800000 in

theorem clebschNormSq_succ_mul
    {w N p q t : ℕ}
    (hsupport : 2 * p + (t + 1) ≤ w)
    (hcomplement : 2 * q + (t + 1) ≤ N) :
    clebschNormSq w N p q t *
        ((((w : ℝ) - 2 * (p : ℝ)) +
          ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 1) *
          (((w : ℝ) - 2 * (p : ℝ)) +
            ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ))) =
      clebschNormSq w N p q (t + 1) *
        ((((w : ℝ) - 2 * (p : ℝ)) +
          ((N : ℝ) - 2 * (q : ℝ)) - (t : ℝ) + 1) *
          ((w : ℝ) - 2 * (p : ℝ) - (t : ℝ))) := by
  let A : ℝ := (w : ℝ) - 2 * (p : ℝ)
  let B : ℝ := (N : ℝ) - 2 * (q : ℝ)
  let T : ℝ := ((t + 1 : ℕ) : ℝ)
  let M₀ : ℝ := clebschNormSq w N p q (t + 1)
  let M₁ : ℝ := clebschFirstMoment w N p q (t + 1)
  let M₂ : ℝ := clebschSecondMoment w N p q (t + 1)
  let Mprev : ℝ := clebschNormSq w N p q t
  have hfirst := clebschFirstMoment_mul hsupport hcomplement
  change (A + B - 2 * T + 2) * M₁ =
    T * (B - T + 1) * M₀ at hfirst
  have hsecond := clebschSecondMoment_mul hsupport hcomplement
  change (A + B - 2 * T + 3) * M₂ =
    (A + B * T - T ^ 2 + T + 1) * M₁ at hsecond
  have hcross :=
    clebschNormSq_cross_degree_harmonic_balance hsupport hcomplement
  rw [clebsch_complement_moment_expansion] at hcross
  change
    T * (B - T + 1) * Mprev =
      T * (B - T + 1) * M₀ +
        (2 * T - B - 1) * M₁ - M₂ at hcross
  have hpositive :
      0 < T * (B - T + 1) := by
    change 0 < MetricCodes.Boolean.harmonicCoefficient N q (t + 1)
    exact MetricCodes.Boolean.harmonicCoefficient_pos
      (Nat.succ_pos t) hcomplement
  have hcancel :
      T * (B - T + 1) *
        (Mprev * ((A + B - 2 * T + 3) *
          (A + B - 2 * T + 2)) -
          M₀ * ((A + B - T + 2) *
            (A - T + 1))) = 0 := by
    linear_combination
      ((A + B - 2 * T + 2) *
        (A + B - 2 * T + 3)) * hcross -
      (A + B - 2 * T + 2) * hsecond +
      ((2 * T - B - 1) *
        (A + B - 2 * T + 3) -
        (A + B * T - T ^ 2 + T + 1)) * hfirst
  have hidentity :
      Mprev * ((A + B - 2 * T + 3) *
        (A + B - 2 * T + 2)) =
      M₀ * ((A + B - T + 2) * (A - T + 1)) := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp hcancel).resolve_left hpositive.ne'
  dsimp [A, B, T, M₀, Mprev] at hidentity
  push_cast at hidentity
  nlinarith only [hidentity]

theorem clebschNormSq_div_succ
    {w N p q t : ℕ}
    (hsupport : 2 * p + (t + 1) ≤ w)
    (hcomplement : 2 * q + (t + 1) ≤ N) :
    clebschNormSq w N p q t /
        clebschNormSq w N p q (t + 1) =
      ((((w : ℝ) - 2 * (p : ℝ)) +
          ((N : ℝ) - 2 * (q : ℝ)) - (t : ℝ) + 1) *
          ((w : ℝ) - 2 * (p : ℝ) - (t : ℝ))) /
        ((((w : ℝ) - 2 * (p : ℝ)) +
          ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 1) *
          (((w : ℝ) - 2 * (p : ℝ)) +
            ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ))) := by
  have hleft :
      (t : ℝ) + 1 ≤ (w : ℝ) - 2 * (p : ℝ) := by
    have hs : ((2 * p + (t + 1) : ℕ) : ℝ) ≤ (w : ℝ) := by
      exact_mod_cast hsupport
    push_cast at hs
    linarith
  have hright :
      (t : ℝ) + 1 ≤ (N : ℝ) - 2 * (q : ℝ) := by
    have hs : ((2 * q + (t + 1) : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hcomplement
    push_cast at hs
    linarith
  have hfactor :
      0 < (((w : ℝ) - 2 * (p : ℝ)) +
        ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 1) *
          (((w : ℝ) - 2 * (p : ℝ)) +
            ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ)) := by
    apply mul_pos <;> linarith
  have hnorm := (clebschNormSq_pos w N p q (t + 1)).ne'
  have hidentity := clebschNormSq_succ_mul hsupport hcomplement
  apply (div_eq_div_iff hnorm hfactor.ne').2
  nlinarith only [hidentity]

private theorem centeredExpectation_diagonal_algebra
    {N W P Q T : ℝ}
    (hN : N ≠ 0) (hW : W ≠ 0) (hNW : N - W ≠ 0)
    (hgap : N - 2 * W ≠ 0)
    (hden : N - 2 * P - 2 * Q - 2 * T + 2 ≠ 0)
    (hJ : N / 2 - (P + Q + T) ≠ 0)
    (hJone : N / 2 - (P + Q + T) + 1 ≠ 0) :
    P + T * (N - W - 2 * Q - T + 1) /
        (N - 2 * P - 2 * Q - 2 * T + 2) -
        W / N * (P + Q + T) =
      ((N *
          (((N / 2 - W) / 2) *
            (((N - W) / 2 - Q) * (((N - W) / 2 - Q) + 1) -
              (W / 2 - P) * ((W / 2 - P) + 1)) /
            ((N / 2 - (P + Q + T)) *
              ((N / 2 - (P + Q + T)) + 1))) -
            (N / 2 - W) ^ 2) /
        (W * (N - W))) *
          ((W * (N - W) * (N - 2 * (P + Q + T))) /
            (N * (N - 2 * W))) := by
  let j : ℝ := P + Q + T
  let J : ℝ := N / 2 - j
  let M : ℝ := N / 2 - W
  let U : ℝ := (N - W) / 2 - Q
  let V : ℝ := W / 2 - P
  let Z : ℝ := U * (U + 1) - V * (V + 1)
  let d : ℝ := N - 2 * P - 2 * Q - 2 * T + 2
  have hd : d ≠ 0 := hden
  have hJ' : J ≠ 0 := by
    simpa [J, j] using hJ
  have hJone' : J + 1 ≠ 0 := by
    simpa [J, j] using hJone
  have hM : M ≠ 0 := by
    intro hzero
    apply hgap
    dsimp [M] at hzero
    linarith
  have hgap' : N - 2 * W = 2 * M := by
    dsimp [M]
    ring
  have hj' : N - 2 * (P + Q + T) = 2 * J := by
    dsimp [J, j]
    ring
  have hdenJ :
      2 * (J + 1) =
        N - 2 * P - 2 * Q - 2 * T + 2 := by
    dsimp [J, j]
    ring
  change
    P + T * (N - W - 2 * Q - T + 1) /
        (N - 2 * P - 2 * Q - 2 * T + 2) - W / N * j =
      ((N * ((M / 2) * Z / (J * (J + 1))) - M ^ 2) /
        (W * (N - W))) *
          ((W * (N - W) * (N - 2 * (P + Q + T))) /
            (N * (N - 2 * W)))
  calc
    P + T * (N - W - 2 * Q - T + 1) /
        (N - 2 * P - 2 * Q - 2 * T + 2) - W / N * j =
      Z / (2 * (J + 1)) - M * J / N := by
        rw [hdenJ]
        change P + T * (N - W - 2 * Q - T + 1) / d -
          W / N * j = Z / d - M * J / N
        field_simp [hN, hd]
        dsimp [d, Z, U, V, J, M, j]
        ring
    _ = ((N * ((M / 2) * Z / (J * (J + 1))) - M ^ 2) /
        (W * (N - W))) *
          ((W * (N - W) * (N - 2 * (P + Q + T))) /
            (N * (N - 2 * W))) := by
      rw [hgap', hj']
      field_simp [hN, hW, hNW, hM, hJ', hJone']

theorem clebschCenteredExpectation_eq_johnsonDiagonal
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (source : Index p q L) :
    (p : ℝ) +
        clebschFirstMoment w (n - w) p q source.val /
          clebschNormSq w (n - w) p q source.val -
        (w : ℝ) / (n : ℝ) *
          ((p + q + source.val : ℕ) : ℝ) =
      MetricCodes.johnsonDiagonal n w p q (p + q + source.val) *
        (((w : ℝ) * ((n - w : ℕ) : ℝ) *
          ((n : ℝ) - 2 *
            ((p + q + source.val : ℕ) : ℝ))) /
          ((n : ℝ) * ((n : ℝ) - 2 * (w : ℝ)))) := by
  have hsupport := h.supportResidual_bound source
  have hcomplement := h.complementResidual_bound source
  have hn : 0 < n := by omega
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hwreal : 0 < (w : ℝ) := by exact_mod_cast h.weight_pos
  have hNreal : 0 < ((n - w : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt h.weight_lt)
  have hjbound := h.window_degree_le_weight source
  have hjreal :
      2 * ((p + q + source.val : ℕ) : ℝ) < (n : ℝ) := by
    have hj : 2 * (p + q + source.val) < n := by omega
    exact_mod_cast hj
  have hwgap : 0 < (n : ℝ) - 2 * (w : ℝ) := by
    have hs : ((2 * w : ℕ) : ℝ) < (n : ℝ) := by
      exact_mod_cast hstrict
    push_cast at hs
    linarith
  have hjgap :
      0 < (n : ℝ) -
        2 * ((p + q + source.val : ℕ) : ℝ) := by
    linarith
  have hJ :
      0 < MetricCodes.johnsonJ n (p + q + source.val) := by
    unfold MetricCodes.johnsonJ
    linarith
  have hJone :
      0 < MetricCodes.johnsonJ n (p + q + source.val) + 1 := by
    linarith
  have hnorm :=
    (clebschNormSq_pos w (n - w) p q source.val).ne'
  have hleftreal :
      2 * (p : ℝ) + (source.val : ℝ) ≤ (w : ℝ) := by
    exact_mod_cast hsupport
  have hrightreal :
      2 * (q : ℝ) + (source.val : ℝ) ≤
        ((n - w : ℕ) : ℝ) := by
    exact_mod_cast hcomplement
  have hden :
      0 < (((w : ℝ) - 2 * (p : ℝ)) +
        (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
        2 * (source.val : ℝ) + 2) := by
    linarith
  have hden' :
      0 < 2 + (n : ℝ) - 2 * (p : ℝ) -
        2 * (source.val : ℝ) - 2 * (q : ℝ) := by
    have hsub : ((n - w : ℕ) : ℝ) = (n : ℝ) - (w : ℝ) := by
      rw [Nat.cast_sub h.weight_lt.le]
    rw [hsub] at hden
    linarith
  have hcompreal : 0 < (n : ℝ) - (w : ℝ) := by
    have hs : (w : ℝ) < (n : ℝ) := by
      exact_mod_cast h.weight_lt
    linarith
  have hexpect :
      clebschFirstMoment w (n - w) p q source.val /
          clebschNormSq w (n - w) p q source.val =
        ((source.val : ℝ) *
          (((n - w : ℕ) : ℝ) - 2 * (q : ℝ) -
            (source.val : ℝ) + 1)) /
          (((w : ℝ) - 2 * (p : ℝ)) +
            (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
            2 * (source.val : ℝ) + 2) := by
    rw [clebschFirstMoment_eq hsupport hcomplement]
    field_simp [hnorm, hden.ne']

  rw [hexpect]
  have hden'' :
      (n : ℝ) - 2 * (p : ℝ) - 2 * (q : ℝ) -
        2 * (source.val : ℝ) + 2 ≠ 0 := by
    nlinarith [hden']
  have hJ' :
      (n : ℝ) / 2 -
        ((p : ℝ) + (q : ℝ) + (source.val : ℝ)) ≠ 0 := by
    have hj : 0 < (n : ℝ) / 2 -
        ((p : ℝ) + (q : ℝ) + (source.val : ℝ)) := by
      exact_mod_cast hJ
    exact hj.ne'
  have hJone' :
      (n : ℝ) / 2 -
          ((p : ℝ) + (q : ℝ) + (source.val : ℝ)) + 1 ≠ 0 := by
    have hj : 0 < (n : ℝ) / 2 -
        ((p : ℝ) + (q : ℝ) + (source.val : ℝ)) + 1 := by
      exact_mod_cast hJone
    exact hj.ne'
  have halgebra := centeredExpectation_diagonal_algebra
    (N := (n : ℝ)) (W := (w : ℝ))
    (P := (p : ℝ)) (Q := (q : ℝ))
    (T := (source.val : ℝ))
    hnreal.ne' hwreal.ne' hcompreal.ne'
    hwgap.ne' hden'' hJ' hJone'
  simp only [Nat.cast_add, Nat.cast_sub h.weight_lt.le] at halgebra ⊢
  unfold MetricCodes.johnsonDiagonal MetricCodes.johnsonMu
    MetricCodes.johnsonM MetricCodes.johnsonJ MetricCodes.johnsonJ1
    MetricCodes.johnsonJ2
  rw [Nat.cast_sub h.weight_lt.le]
  push_cast
  rw [show
    (w : ℝ) - 2 * (p : ℝ) +
        ((n : ℝ) - (w : ℝ) - 2 * (q : ℝ)) -
        2 * (source.val : ℝ) + 2 =
      (n : ℝ) - 2 * (p : ℝ) - 2 * (q : ℝ) -
        2 * (source.val : ℝ) + 2 by ring]
  exact halgebra

theorem clebschClosedCenteredExpectation_eq_johnsonDiagonal
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (source : Index p q L) :
    (((p : ℝ) - (w : ℝ) / (n : ℝ) *
        ((p + q + source.val : ℕ) : ℝ)) +
      ((source.val : ℝ) *
        (((n - w : ℕ) : ℝ) - 2 * (q : ℝ) -
          (source.val : ℝ) + 1)) /
        (((w : ℝ) - 2 * (p : ℝ)) +
          (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
          2 * (source.val : ℝ) + 2)) =
      MetricCodes.johnsonDiagonal n w p q (p + q + source.val) *
        (((w : ℝ) * ((n - w : ℕ) : ℝ) *
          ((n : ℝ) - 2 *
            ((p + q + source.val : ℕ) : ℝ))) /
          ((n : ℝ) * ((n : ℝ) - 2 * (w : ℝ)))) := by
  have hsupport := h.supportResidual_bound source
  have hcomplement := h.complementResidual_bound source
  have hleftreal :
      2 * (p : ℝ) + (source.val : ℝ) ≤ (w : ℝ) := by
    exact_mod_cast hsupport
  have hrightreal :
      2 * (q : ℝ) + (source.val : ℝ) ≤
        ((n - w : ℕ) : ℝ) := by
    exact_mod_cast hcomplement
  have hden :
      0 < (((w : ℝ) - 2 * (p : ℝ)) +
        (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
        2 * (source.val : ℝ) + 2) := by
    linarith
  have hnorm :=
    (clebschNormSq_pos w (n - w) p q source.val).ne'
  calc
    (((p : ℝ) - (w : ℝ) / (n : ℝ) *
        ((p + q + source.val : ℕ) : ℝ)) +
      ((source.val : ℝ) *
        (((n - w : ℕ) : ℝ) - 2 * (q : ℝ) -
          (source.val : ℝ) + 1)) /
        (((w : ℝ) - 2 * (p : ℝ)) +
          (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
          2 * (source.val : ℝ) + 2)) =
      (p : ℝ) +
        clebschFirstMoment w (n - w) p q source.val /
          clebschNormSq w (n - w) p q source.val -
        (w : ℝ) / (n : ℝ) *
          ((p + q + source.val : ℕ) : ℝ) := by
        rw [clebschFirstMoment_eq hsupport hcomplement]
        field_simp [hnorm, hden.ne']
        ; ring
    _ = _ := clebschCenteredExpectation_eq_johnsonDiagonal
      h hstrict source

private theorem middleNormalization_algebra
    {N W C j J M R : ℝ}
    (hN : N ≠ 0) (hW : W ≠ 0) (hC : C ≠ 0)
    (hj : j ≠ 0) (hJ : J ≠ 0) (hJone : J + 1 ≠ 0)
    (hM : M ≠ 0) (hR : R ≠ 0) :
    (j * J * R / (N * (J + 1)))⁻¹ *
        (N / (W * C)) *
        (W * C * J / (N * M)) ^ 2 =
      (M ^ 2 * j * R /
        (W * C * J * (J + 1)))⁻¹ := by
  field_simp [hN, hW, hC, hj, hJ, hJone, hM, hR]

theorem johnsonMiddleNormalization_sq_eq_inv_zonal
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (source : Index p q L)
    (hsource : 0 < p + q + source.val) :
    ((Real.sqrt
          (johnsonMiddleScale n (p + q + source.val)))⁻¹ *
        Real.sqrt
          ((n : ℝ) /
            ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (((w : ℝ) * ((n - w : ℕ) : ℝ) *
          ((n : ℝ) -
            2 * ((p + q + source.val : ℕ) : ℝ))) /
          ((n : ℝ) * ((n : ℝ) - 2 * (w : ℝ))))) ^ 2 =
      (MetricCodes.johnsonZonalDiagonal
        n w (p + q + source.val))⁻¹ := by
  let j : ℕ := p + q + source.val
  have hjw : j ≤ w := h.window_degree_le_weight source
  have hjhalf : 2 * j < n := by omega
  have hn : 0 < n := by omega
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hwreal : 0 < (w : ℝ) := by exact_mod_cast h.weight_pos
  have hcomp : 0 < ((n - w : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt h.weight_lt)
  have hjreal : 0 < (j : ℝ) := by exact_mod_cast hsource
  have hJ : 0 < MetricCodes.johnsonJ n j := by
    unfold MetricCodes.johnsonJ
    have hj' : (2 : ℝ) * (j : ℝ) < (n : ℝ) := by
      exact_mod_cast hjhalf
    linarith
  have hJone : 0 < MetricCodes.johnsonJ n j + 1 := by linarith
  have hM : 0 < MetricCodes.johnsonM n w := by
    unfold MetricCodes.johnsonM
    have hw' : (2 : ℝ) * (w : ℝ) < (n : ℝ) := by
      exact_mod_cast hstrict
    linarith
  have hlast : 0 < (n : ℝ) - (j : ℝ) + 1 := by
    have hjn : (j : ℝ) < (n : ℝ) := by
      exact_mod_cast (show j < n by omega)
    linarith
  have hmiddle := johnsonMiddleScale_pos hsource hjhalf
  have haxis : 0 ≤ (n : ℝ) /
      ((w : ℝ) * ((n - w : ℕ) : ℝ)) := by positivity
  have hF :
      ((w : ℝ) * ((n - w : ℕ) : ℝ) *
        ((n : ℝ) - 2 * (j : ℝ))) /
          ((n : ℝ) * ((n : ℝ) - 2 * (w : ℝ))) =
        ((w : ℝ) * ((n - w : ℕ) : ℝ) *
          MetricCodes.johnsonJ n j) /
          ((n : ℝ) * MetricCodes.johnsonM n w) := by
    unfold MetricCodes.johnsonJ MetricCodes.johnsonM
    have hwgap : (n : ℝ) - 2 * (w : ℝ) ≠ 0 := by
      have hs : ((2 * w : ℕ) : ℝ) < (n : ℝ) := by
        exact_mod_cast hstrict
      push_cast at hs
      linarith
    field_simp [hnreal.ne', hwgap]

  have hK :
      johnsonMiddleScale n j =
        (j : ℝ) * MetricCodes.johnsonJ n j *
          ((n : ℝ) - (j : ℝ) + 1) /
          ((n : ℝ) * (MetricCodes.johnsonJ n j + 1)) := by
    unfold johnsonMiddleScale johnsonHarmonicGap
      MetricCodes.johnsonJ
    field_simp [hnreal.ne', hJone.ne']

  change
    ((Real.sqrt (johnsonMiddleScale n j))⁻¹ *
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
      (((w : ℝ) * ((n - w : ℕ) : ℝ) *
        ((n : ℝ) - 2 * (j : ℝ))) /
        ((n : ℝ) * ((n : ℝ) - 2 * (w : ℝ))))) ^ 2 =
      (MetricCodes.johnsonZonalDiagonal n w j)⁻¹
  rw [mul_pow, mul_pow, inv_pow,
    Real.sq_sqrt hmiddle.le, Real.sq_sqrt haxis,
    hF, hK, zonalDiagonal_eq h.weight_pos hstrict hjw]
  exact middleNormalization_algebra hnreal.ne' hwreal.ne'
    hcomp.ne' hjreal.ne' hJ.ne' hJone.ne' hM.ne'
    hlast.ne'

theorem johnsonMiddleSignedScalar_eq_sqrt_hattedDiagonal
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (source : Index p q L)
    (hsource : 0 < p + q + source.val) :
    johnsonDiagonalChannelSign n w p q (p + q + source.val) *
        ((Real.sqrt
            (johnsonMiddleScale n (p + q + source.val)))⁻¹ *
          Real.sqrt
            ((n : ℝ) /
              ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
          (((p : ℝ) - (w : ℝ) / (n : ℝ) *
              ((p + q + source.val : ℕ) : ℝ)) +
            ((source.val : ℝ) *
              (((n - w : ℕ) : ℝ) - 2 * (q : ℝ) -
                (source.val : ℝ) + 1)) /
              (((w : ℝ) - 2 * (p : ℝ)) +
                (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
                2 * (source.val : ℝ) + 2))) =
      Real.sqrt
        (MetricCodes.johnsonHattedDiagonal
          n w p q (p + q + source.val)) := by
  let j : ℕ := p + q + source.val
  let z : ℝ := MetricCodes.johnsonZonalDiagonal n w j
  let D : ℝ := MetricCodes.johnsonDiagonal n w p q j
  let F : ℝ :=
    ((w : ℝ) * ((n - w : ℕ) : ℝ) *
      ((n : ℝ) - 2 * (j : ℝ))) /
      ((n : ℝ) * ((n : ℝ) - 2 * (w : ℝ)))
  let S : ℝ :=
    (Real.sqrt (johnsonMiddleScale n j))⁻¹ *
      Real.sqrt
        ((n : ℝ) /
          ((w : ℝ) * ((n - w : ℕ) : ℝ))) * F
  have hjw : j ≤ w := h.window_degree_le_weight source
  have hjhalf : 2 * j < n := by omega
  have hn : 0 < n := by omega
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hwreal : 0 < (w : ℝ) := by exact_mod_cast h.weight_pos
  have hcomp : 0 < ((n - w : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt h.weight_lt)
  have hgapj : 0 < (n : ℝ) - 2 * (j : ℝ) := by
    have hs : ((2 * j : ℕ) : ℝ) < (n : ℝ) := by
      exact_mod_cast hjhalf
    push_cast at hs
    linarith
  have hgapw : 0 < (n : ℝ) - 2 * (w : ℝ) := by
    have hs : ((2 * w : ℕ) : ℝ) < (n : ℝ) := by
      exact_mod_cast hstrict
    push_cast at hs
    linarith
  have hF : 0 < F := by
    dsimp [F]
    positivity
  have hmiddle := johnsonMiddleScale_pos hsource hjhalf
  have haxis : 0 < (n : ℝ) /
      ((w : ℝ) * ((n - w : ℕ) : ℝ)) := by
    positivity
  have hS : 0 < S := by
    dsimp [S]
    positivity
  have hz : 0 < z := by
    dsimp [z, j]
    exact zonalDiagonal_pos h.weight_pos hstrict
      hsource hjw
  have hnorm : S ^ 2 = z⁻¹ := by
    dsimp [S, F, z, j]
    exact johnsonMiddleNormalization_sq_eq_inv_zonal
      h hstrict source hsource
  have hsign :
      0 ≤ johnsonDiagonalChannelSign n w p q j * D := by
    unfold johnsonDiagonalChannelSign
    split_ifs with hD
    · simpa [D] using hD
    · have hnegative : D < 0 := by
        dsimp [D]
        exact lt_of_not_ge hD
      dsimp [D] at hnegative ⊢
      linarith
  have hleft :
      0 ≤ (johnsonDiagonalChannelSign n w p q j * D) * S :=
    mul_nonneg hsign hS.le
  have hrad : 0 ≤ D ^ 2 / z :=
    div_nonneg (sq_nonneg D) hz.le
  have hsquare :
      ((johnsonDiagonalChannelSign n w p q j * D) * S) ^ 2 =
        D ^ 2 / z := by
    rw [mul_pow, mul_pow,
      johnsonDiagonalChannelSign_sq, one_mul, hnorm]
    ring
  have hsqrt :
      (Real.sqrt (D ^ 2 / z)) ^ 2 = D ^ 2 / z :=
    Real.sq_sqrt hrad
  have heq :
      (johnsonDiagonalChannelSign n w p q j * D) * S =
        Real.sqrt (D ^ 2 / z) := by
    nlinarith [hsquare, hsqrt,
      Real.sqrt_nonneg (D ^ 2 / z)]
  rw [clebschClosedCenteredExpectation_eq_johnsonDiagonal
    h hstrict source]
  have hhatted :
      MetricCodes.johnsonHattedDiagonal n w p q j = D ^ 2 / z := by
    have hjne : j ≠ 0 := by
      dsimp [j]
      exact hsource.ne'
    simp [MetricCodes.johnsonHattedDiagonal, hjne, D, z]
  change
    johnsonDiagonalChannelSign n w p q j *
      ((Real.sqrt (johnsonMiddleScale n j))⁻¹ *
        Real.sqrt ((n : ℝ) /
          ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (D * F)) =
      Real.sqrt (MetricCodes.johnsonHattedDiagonal n w p q j)
  rw [hhatted]
  calc
    johnsonDiagonalChannelSign n w p q j *
        ((Real.sqrt (johnsonMiddleScale n j))⁻¹ *
          Real.sqrt ((n : ℝ) /
            ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
          (D * F)) =
      (johnsonDiagonalChannelSign n w p q j * D) * S := by
        dsimp [S]
        ring
    _ = Real.sqrt (D ^ 2 / z) := heq

end MetricCodes.Johnson

end

end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace MetricCodes.Johnson

theorem booleanHarmonicDimension_mul_degreeComplement
    (n j : ℕ) (hhalf : 2 * j ≤ n) :
    (MetricCodes.booleanHarmonicDimension n j : ℝ) *
        ((n : ℝ) - (j : ℝ) + 1) =
      (n.choose j : ℝ) *
        ((n : ℝ) - 2 * (j : ℝ) + 1) := by
  cases j with
  | zero =>
      simp [MetricCodes.booleanHarmonicDimension]
  | succ k =>
      have hmono : n.choose k ≤ n.choose (k + 1) :=
        Nat.choose_le_succ_of_lt_half_left (by omega)
      have hk : k ≤ n := by omega
      have hchoose :
          (n.choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) =
            (n.choose k : ℝ) * ((n - k : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_succ_right_eq n k
      rw [Nat.cast_sub hk] at hchoose
      rw [MetricCodes.booleanHarmonicDimension_succ, Nat.cast_sub hmono]
      push_cast at hchoose ⊢
      nlinarith [hchoose]

theorem booleanHarmonicDimension_succ_div
    {n j : ℕ} (hhalf : 2 * (j + 1) ≤ n) :
    (MetricCodes.booleanHarmonicDimension n (j + 1) : ℝ) /
        (MetricCodes.booleanHarmonicDimension n j : ℝ) =
      (((n : ℝ) - 2 * (j : ℝ) - 1) *
        ((n : ℝ) - (j : ℝ) + 1)) /
        (((j : ℝ) + 1) *
          ((n : ℝ) - 2 * (j : ℝ) + 1)) := by
  have hjhalf : 2 * j ≤ n := by omega
  have hjn : j ≤ n := by omega
  have hd : 0 < (MetricCodes.booleanHarmonicDimension n j : ℝ) := by
    exact_mod_cast booleanHarmonicDimension_pos hjhalf
  have hnext :=
    booleanHarmonicDimension_mul_degreeComplement n (j + 1) hhalf
  have hcurrent :=
    booleanHarmonicDimension_mul_degreeComplement n j hjhalf
  have hchoose :
      (n.choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) =
        (n.choose j : ℝ) * ((n - j : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n j
  rw [Nat.cast_sub hjn] at hchoose
  push_cast at hnext hchoose
  have hjpos : 0 < (j : ℝ) + 1 := by positivity
  have hgap : 0 < (n : ℝ) - 2 * (j : ℝ) + 1 := by
    have hh : (2 : ℝ) * (j : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hjhalf
    linarith
  have hnminus : 0 < (n : ℝ) - (j : ℝ) := by
    have hh : (j : ℝ) + 1 ≤ (n : ℝ) := by
      have hnat : j + 1 ≤ n := by omega
      exact_mod_cast hnat
    linarith
  have hnext' :
      (MetricCodes.booleanHarmonicDimension n (j + 1) : ℝ) *
          ((n : ℝ) - (j : ℝ)) =
        (n.choose (j + 1) : ℝ) *
          ((n : ℝ) - 2 * (j : ℝ) - 1) := by
    convert hnext using 1 <;> ring
  apply (div_eq_div_iff hd.ne' (mul_pos hjpos hgap).ne').mpr
  apply (mul_right_inj' hnminus.ne').mp
  calc
    ((n : ℝ) - (j : ℝ)) *
        ((MetricCodes.booleanHarmonicDimension n (j + 1) : ℝ) *
          (((j : ℝ) + 1) * ((n : ℝ) - 2 * (j : ℝ) + 1))) =
      ((MetricCodes.booleanHarmonicDimension n (j + 1) : ℝ) *
        ((n : ℝ) - (j : ℝ))) *
        (((j : ℝ) + 1) * ((n : ℝ) - 2 * (j : ℝ) + 1)) := by
        ring
    _ = ((n.choose (j + 1) : ℝ) *
          ((n : ℝ) - 2 * (j : ℝ) - 1)) *
        (((j : ℝ) + 1) * ((n : ℝ) - 2 * (j : ℝ) + 1)) := by
        rw [hnext']
    _ = ((n.choose (j + 1) : ℝ) * ((j : ℝ) + 1)) *
        (((n : ℝ) - 2 * (j : ℝ) - 1) *
          ((n : ℝ) - 2 * (j : ℝ) + 1)) := by
        ring
    _ = ((n.choose j : ℝ) * ((n : ℝ) - (j : ℝ))) *
        (((n : ℝ) - 2 * (j : ℝ) - 1) *
          ((n : ℝ) - 2 * (j : ℝ) + 1)) := by
        rw [hchoose]
    _ = ((n.choose j : ℝ) * ((n : ℝ) - 2 * (j : ℝ) + 1)) *
        (((n : ℝ) - 2 * (j : ℝ) - 1) *
          ((n : ℝ) - (j : ℝ))) := by
        ring
    _ = ((MetricCodes.booleanHarmonicDimension n j : ℝ) *
          ((n : ℝ) - (j : ℝ) + 1)) *
        (((n : ℝ) - 2 * (j : ℝ) - 1) *
          ((n : ℝ) - (j : ℝ))) := by
        rw [hcurrent]
    _ = ((n : ℝ) - (j : ℝ)) *
          ((((n : ℝ) - 2 * (j : ℝ) - 1) *
            ((n : ℝ) - (j : ℝ) + 1)) *
              (MetricCodes.booleanHarmonicDimension n j : ℝ)) := by
        ring

theorem booleanHarmonicDimension_succ_div_eq_upperScale
    {n j : ℕ} (hhalf : 2 * (j + 1) ≤ n) :
    (MetricCodes.booleanHarmonicDimension n (j + 1) : ℝ) /
        (MetricCodes.booleanHarmonicDimension n j : ℝ) =
      johnsonUpperScale n j / ((j : ℝ) + 1) := by
  rw [booleanHarmonicDimension_succ_div hhalf]
  unfold johnsonUpperScale johnsonHarmonicGap
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  have hgap : (n : ℝ) - 2 * (j : ℝ) + 1 ≠ 0 := by
    have hcast : (2 : ℝ) * ((j : ℝ) + 1) ≤ (n : ℝ) := by
      exact_mod_cast hhalf
    linarith
  field_simp [hj, hgap]

theorem clebschCenteredAxis_sum
    (w N p q t : ℕ) (c : ℝ) :
    (∑ r : Fin (t + 1),
      clebschCoefficient w N p q t r.val ^ 2 *
        (((p + r.val : ℕ) : ℝ) -
          c * ((p + q + t : ℕ) : ℝ))) =
      ((p : ℝ) - c * ((p + q + t : ℕ) : ℝ)) *
        clebschNormSq w N p q t +
      clebschFirstMoment w N p q t := by
  unfold clebschNormSq clebschFirstMoment
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  push_cast
  ring

theorem clebschCenteredAxis_sum_eq
    {w N p q t : ℕ}
    (hsupport : 2 * p + t ≤ w)
    (hcomplement : 2 * q + t ≤ N)
    (c : ℝ) :
    (∑ r : Fin (t + 1),
      clebschCoefficient w N p q t r.val ^ 2 *
        (((p + r.val : ℕ) : ℝ) -
          c * ((p + q + t : ℕ) : ℝ))) =
      clebschNormSq w N p q t *
        (((p : ℝ) - c * ((p + q + t : ℕ) : ℝ)) +
          ((t : ℝ) *
            ((N : ℝ) - 2 * (q : ℝ) - (t : ℝ) + 1)) /
            (((w : ℝ) - 2 * (p : ℝ)) +
              ((N : ℝ) - 2 * (q : ℝ)) - 2 * (t : ℝ) + 2)) := by
  rw [clebschCenteredAxis_sum,
    clebschFirstMoment_eq hsupport hcomplement]
  ring

theorem clebschSignedAdjacentCross_sum
    {w N p q t : ℕ}
    (hsupport : 2 * p + (t + 1) ≤ w)
    (_hcomplement : 2 * q + (t + 1) ≤ N) :
    (∑ r : Fin (t + 1),
      clebschCoefficient w N p q t r.val *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
        clebschCoefficient w N p q (t + 1) (r.val + 1)) =
      -Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient N q (t + 1)) *
        clebschNormSq w N p q t := by
  unfold clebschNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hr : r.val ≤ t := by
    have hlt := r.isLt
    omega
  have hrbound : 2 * p + (r.val + 1) ≤ w := by omega
  have hrow := clebschCoefficient_succ_mul
    (w := w) (N := N) (p := p) (q := q)
    (t := t + 1) (r := r.val) hrbound
  have hcross := clebschCoefficient_cross_degree_mul
    (w := w) (N := N) (p := p) (q := q)
    (t := t) (r := r.val) (by omega) hr
  calc
    clebschCoefficient w N p q t r.val *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
        clebschCoefficient w N p q (t + 1) (r.val + 1) =
      clebschCoefficient w N p q t r.val *
        (clebschCoefficient w N p q (t + 1) (r.val + 1) *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1))) := by
        ring
    _ = clebschCoefficient w N p q t r.val *
        (-clebschCoefficient w N p q (t + 1) r.val *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient N q
              (t + 1 - r.val))) := by
        rw [hrow]
    _ = -clebschCoefficient w N p q t r.val *
        (clebschCoefficient w N p q (t + 1) r.val *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient N q
              (t + 1 - r.val))) := by
        ring
    _ = -clebschCoefficient w N p q t r.val *
        (clebschCoefficient w N p q t r.val *
          Real.sqrt
            (MetricCodes.Boolean.harmonicCoefficient N q (t + 1))) := by
        rw [hcross]
    _ = -Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient N q (t + 1)) *
        clebschCoefficient w N p q t r.val ^ 2 := by
        ring

theorem johnsonAxisRaise_coupledHarmonic_dot_closed
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + (t + 1) ≤ w)
    (htcomplement : 2 * q + (t + 1) ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + (t + 1)) f) :
    MetricCodes.Boolean.dot f
        (johnsonAxisRaise x (coupledHarmonic x hp hq a t)) =
      -Real.sqrt ((n : ℝ) / ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient (n - w) q (t + 1)) *
        (Real.sqrt (clebschNormSq w (n - w) p q t) /
          Real.sqrt (clebschNormSq w (n - w) p q (t + 1))) *
        MetricCodes.Boolean.dot f (coupledHarmonic x hp hq a (t + 1)) := by
  rw [johnsonAxisRaise_coupledHarmonic_dot
    x hp hq htsupport htcomplement a f hf,
    clebschSignedAdjacentCross_sum htsupport htcomplement]
  have hnorm := clebschNormSq_pos w (n - w) p q t
  have hnext := clebschNormSq_pos w (n - w) p q (t + 1)
  have hroot := (Real.sqrt_pos.mpr hnorm).ne'
  have hroot' := (Real.sqrt_pos.mpr hnext).ne'
  field_simp [hroot, hroot']
  rw [Real.sq_sqrt hnorm.le]
  ring

theorem johnsonLowerChannel_coupled_axis_inner_closed
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + (t + 1) ≤ w)
    (htcomplement : 2 * q + (t + 1) ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + (t + 1)) f) :
    MetricCodes.Boolean.coordinateDot
        (johnsonLowerChannel (p + q + (t + 1)) f)
        (johnsonAxisTensor x (coupledHarmonic x hp hq a t)) =
      -(Real.sqrt (((p + q + (t + 1) : ℕ) : ℝ)))⁻¹ *
        Real.sqrt ((n : ℝ) / ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient (n - w) q (t + 1)) *
        (Real.sqrt (clebschNormSq w (n - w) p q t) /
          Real.sqrt (clebschNormSq w (n - w) p q (t + 1))) *
        MetricCodes.Boolean.dot f (coupledHarmonic x hp hq a (t + 1)) := by
  rw [johnsonLowerChannel_axis_inner x f
    (coupledHarmonic x hp hq a t),
    johnsonAxisRaise_coupledHarmonic_dot_closed
      x hp hq htsupport htcomplement a f hf]
  ring

theorem clebschSignedAdjacentCross_sum_comm
    {w N p q t : ℕ}
    (hsupport : 2 * p + (t + 1) ≤ w)
    (hcomplement : 2 * q + (t + 1) ≤ N) :
    (∑ r : Fin (t + 1),
      clebschCoefficient w N p q (t + 1) (r.val + 1) *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient w p (r.val + 1)) *
        clebschCoefficient w N p q t r.val) =
      -Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient N q (t + 1)) *
        clebschNormSq w N p q t := by
  rw [← clebschSignedAdjacentCross_sum hsupport hcomplement]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem johnsonAxisLower_coupledHarmonic_dot_closed
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + (t + 1) ≤ w)
    (htcomplement : 2 * q + (t + 1) ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + t) f) :
    MetricCodes.Boolean.dot f
        (johnsonAxisLower x (coupledHarmonic x hp hq a (t + 1))) =
      -Real.sqrt ((n : ℝ) / ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient (n - w) q (t + 1)) *
        (Real.sqrt (clebschNormSq w (n - w) p q t) /
          Real.sqrt (clebschNormSq w (n - w) p q (t + 1))) *
        MetricCodes.Boolean.dot f (coupledHarmonic x hp hq a t) := by
  rw [johnsonAxisLower_coupledHarmonic_dot
    x hp hq htsupport htcomplement a f hf,
    clebschSignedAdjacentCross_sum_comm htsupport htcomplement]
  have hnorm := clebschNormSq_pos w (n - w) p q t
  have hnext := clebschNormSq_pos w (n - w) p q (t + 1)
  have hroot := (Real.sqrt_pos.mpr hnorm).ne'
  have hroot' := (Real.sqrt_pos.mpr hnext).ne'
  field_simp [hroot, hroot']
  rw [Real.sq_sqrt hnorm.le]
  ring

theorem johnsonUpperChannel_coupled_axis_inner_closed
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + (t + 1) ≤ w)
    (htcomplement : 2 * q + (t + 1) ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + t) f) :
    MetricCodes.Boolean.coordinateDot
        (johnsonUpperChannel (p + q + t) f)
        (johnsonAxisTensor x (coupledHarmonic x hp hq a (t + 1))) =
      -(Real.sqrt (johnsonUpperScale n (p + q + t)))⁻¹ *
        Real.sqrt ((n : ℝ) / ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        Real.sqrt
          (MetricCodes.Boolean.harmonicCoefficient (n - w) q (t + 1)) *
        (Real.sqrt (clebschNormSq w (n - w) p q t) /
          Real.sqrt (clebschNormSq w (n - w) p q (t + 1))) *
        MetricCodes.Boolean.dot f (coupledHarmonic x hp hq a t) := by
  rw [johnsonUpperChannel_axis_inner x f
    (coupledHarmonic x hp hq a (t + 1))
    (coupledHarmonic_isHarmonic x hp hq
      htsupport htcomplement a),
    johnsonAxisLower_coupledHarmonic_dot_closed
      x hp hq htsupport htcomplement a f hf]
  ring

theorem coupledHarmonic_dot_of_split_proportional
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hpair : ∀ r : Fin (t + 1),
      MetricCodes.Boolean.dot f
          (splitTensor x hp hq a r.val (t - r.val)) =
        clebschCoefficient w (n - w) p q t r.val *
          MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t)) :
    MetricCodes.Boolean.dot f (coupledHarmonic x hp hq a t) =
      Real.sqrt (clebschNormSq w (n - w) p q t) *
        MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t) := by
  have hpos := clebschNormSq_pos w (n - w) p q t
  have hroot := (Real.sqrt_pos.mpr hpos).ne'
  have hsquare := Real.sq_sqrt hpos.le
  unfold coupledHarmonic coupledTensor
  rw [MetricCodes.Boolean.dot_smul_right,
    johnsonDot_fintype_weighted_sum_right]
  simp_rw [hpair]
  have hsum :
      (∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q t r.val *
          (clebschCoefficient w (n - w) p q t r.val *
            MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t))) =
        clebschNormSq w (n - w) p q t *
          MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t) := by
    unfold clebschNormSq
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hsum]
  field_simp [hroot]
  rw [hsquare]

theorem johnsonAxisMembership_coupledHarmonic_dot_of_split_proportional
    {n w p q t : ℕ}
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + t ≤ w)
    (htcomplement : 2 * q + t ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hpair : ∀ r : Fin (t + 1),
      MetricCodes.Boolean.dot f
          (splitTensor x hp hq a r.val (t - r.val)) =
        clebschCoefficient w (n - w) p q t r.val *
          MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t)) :
    MetricCodes.Boolean.dot f
        (johnsonAxisMembership x (coupledHarmonic x hp hq a t)) =
      Real.sqrt ((n : ℝ) / ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (((p : ℝ) - (w : ℝ) / (n : ℝ) *
            ((p + q + t : ℕ) : ℝ)) +
          ((t : ℝ) *
            (((n - w : ℕ) : ℝ) - 2 * (q : ℝ) - (t : ℝ) + 1)) /
            (((w : ℝ) - 2 * (p : ℝ)) +
              (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
              2 * (t : ℝ) + 2)) *
        MetricCodes.Boolean.dot f (coupledHarmonic x hp hq a t) := by
  rw [johnsonAxisMembership_coupledHarmonic_dot x hp hq a t f,
    coupledHarmonic_dot_of_split_proportional x hp hq a f hpair]
  simp_rw [hpair]
  have hsum :
      (∑ r : Fin (t + 1),
        clebschCoefficient w (n - w) p q t r.val *
          (((p + r.val : ℕ) : ℝ) -
            (w : ℝ) / (n : ℝ) * ((p + q + t : ℕ) : ℝ)) *
          (clebschCoefficient w (n - w) p q t r.val *
            MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t))) =
        (∑ r : Fin (t + 1),
          clebschCoefficient w (n - w) p q t r.val ^ 2 *
            (((p + r.val : ℕ) : ℝ) -
              (w : ℝ) / (n : ℝ) * ((p + q + t : ℕ) : ℝ))) *
          MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hsum, clebschCenteredAxis_sum_eq htsupport htcomplement]
  have hpos := clebschNormSq_pos w (n - w) p q t
  have hroot := (Real.sqrt_pos.mpr hpos).ne'
  have hsquare := Real.sq_sqrt hpos.le
  field_simp [hroot]
  rw [hsquare]
  ring

theorem johnsonMiddleChannel_coupled_axis_inner_of_split_proportional
    {n w p q t : ℕ}
    (hn : 0 < n)
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + t ≤ w)
    (htcomplement : 2 * q + t ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hpair : ∀ r : Fin (t + 1),
      MetricCodes.Boolean.dot f
          (splitTensor x hp hq a r.val (t - r.val)) =
        clebschCoefficient w (n - w) p q t r.val *
          MetricCodes.Boolean.dot f (splitTensor x hp hq a 0 t)) :
    MetricCodes.Boolean.coordinateDot
        (johnsonMiddleChannel (p + q + t) f)
        (johnsonAxisTensor x (coupledHarmonic x hp hq a t)) =
      (Real.sqrt (johnsonMiddleScale n (p + q + t)))⁻¹ *
        Real.sqrt ((n : ℝ) / ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (((p : ℝ) - (w : ℝ) / (n : ℝ) *
            ((p + q + t : ℕ) : ℝ)) +
          ((t : ℝ) *
            (((n - w : ℕ) : ℝ) - 2 * (q : ℝ) - (t : ℝ) + 1)) /
            (((w : ℝ) - 2 * (p : ℝ)) +
              (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
              2 * (t : ℝ) + 2)) *
        MetricCodes.Boolean.dot f (coupledHarmonic x hp hq a t) := by
  rw [johnsonMiddleChannel_axis_inner hn x f
    (coupledHarmonic x hp hq a t)
    (coupledHarmonic_isHarmonic x hp hq
      htsupport htcomplement a)]
  rw [johnsonAxisMembership_coupledHarmonic_dot_of_split_proportional
    x hp hq htsupport htcomplement a f hpair]
  ring

theorem johnsonMiddleChannel_coupled_axis_inner_closed
    {n w p q t : ℕ}
    (hn : 0 < n)
    (x : JohnsonSphere n w)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (htsupport : 2 * p + t ≤ w)
    (htcomplement : 2 * q + t ≤ n - w)
    (a : HarmonicFibreIndex n w p q)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + t) f) :
    MetricCodes.Boolean.coordinateDot
        (johnsonMiddleChannel (p + q + t) f)
        (johnsonAxisTensor x (coupledHarmonic x hp hq a t)) =
      (Real.sqrt (johnsonMiddleScale n (p + q + t)))⁻¹ *
        Real.sqrt ((n : ℝ) / ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (((p : ℝ) - (w : ℝ) / (n : ℝ) *
            ((p + q + t : ℕ) : ℝ)) +
          ((t : ℝ) *
            (((n - w : ℕ) : ℝ) - 2 * (q : ℝ) - (t : ℝ) + 1)) /
            (((w : ℝ) - 2 * (p : ℝ)) +
              (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
              2 * (t : ℝ) + 2)) *
        MetricCodes.Boolean.dot f (coupledHarmonic x hp hq a t) := by
  apply johnsonMiddleChannel_coupled_axis_inner_of_split_proportional
    hn x hp hq htsupport htcomplement a f
  intro r
  exact johnsonHarmonic_dot_splitTensor_eq_clebschCoefficient
    x hp hq htsupport htcomplement a f hf r.val
      (by have hr := r.isLt; omega)

theorem johnsonSourceChannelCoefficient_diagonal
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (source : Index p q L) :
    johnsonSourceChannelCoefficient n w p q L source source =
      MetricCodes.johnsonHattedDiagonal n w p q (p + q + source.val) := by
  have hdimension :
      0 < (MetricCodes.booleanHarmonicDimension
        n (p + q + source.val) : ℝ) := by
    exact_mod_cast johnsonWindowHarmonicDimension_pos h source
  have hroot := (Real.sqrt_pos.mpr hdimension).ne'
  unfold johnsonSourceChannelCoefficient matrix
  rw [MetricCodes.johnsonJacobiMatrix_diag]
  field_simp [hroot]

theorem johnsonSourceChannelCoefficient_reverse_mul_upperScale
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (target source : Index p q L)
    (hadj : target.val + 1 = source.val) :
    johnsonSourceChannelCoefficient n w p q L target source *
        johnsonUpperScale n (p + q + target.val) =
      johnsonSourceChannelCoefficient n w p q L source target *
        (((p + q + target.val : ℕ) : ℝ) + 1) := by
  let j : ℕ := p + q + target.val
  have hsource : p + q + source.val = j + 1 := by
    dsimp [j]
    omega
  have hhalf : 2 * (j + 1) ≤ n := by
    have hweight := h.window_degree_le_weight source
    omega
  have htargetdim :
      0 < (MetricCodes.booleanHarmonicDimension n j : ℝ) := by
    dsimp [j]
    exact_mod_cast johnsonWindowHarmonicDimension_pos h target
  have hsourcedim :
      0 < (MetricCodes.booleanHarmonicDimension n (j + 1) : ℝ) := by
    rw [← hsource]
    exact_mod_cast johnsonWindowHarmonicDimension_pos h source
  have htargetroot := (Real.sqrt_pos.mpr htargetdim).ne'
  have hsourceroot := (Real.sqrt_pos.mpr hsourcedim).ne'
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  have hratio := booleanHarmonicDimension_succ_div_eq_upperScale hhalf
  have hmul :
      (MetricCodes.booleanHarmonicDimension n (j + 1) : ℝ) *
          ((j : ℝ) + 1) =
        johnsonUpperScale n j *
          (MetricCodes.booleanHarmonicDimension n j : ℝ) :=
    (div_eq_div_iff htargetdim.ne' hj).mp hratio
  have hsym : matrix n w p q L target source =
      matrix n w p q L source target := by
    have heq := congrArg
      (fun A : Matrix (Index p q L) (Index p q L) ℝ =>
        A source target)
      (MetricCodes.johnsonJacobiMatrix_symmetric n w p q L)
    simpa [matrix] using heq
  change
    johnsonSourceChannelCoefficient n w p q L target source *
        johnsonUpperScale n j =
      johnsonSourceChannelCoefficient n w p q L source target *
        ((j : ℝ) + 1)
  unfold johnsonSourceChannelCoefficient
  change
    (matrix n w p q L target source *
      Real.sqrt (MetricCodes.booleanHarmonicDimension n j : ℝ) /
      Real.sqrt
        (MetricCodes.booleanHarmonicDimension n
          (p + q + source.val) : ℝ)) *
        johnsonUpperScale n j =
      (matrix n w p q L source target *
        Real.sqrt
          (MetricCodes.booleanHarmonicDimension n
            (p + q + source.val) : ℝ) /
        Real.sqrt (MetricCodes.booleanHarmonicDimension n j : ℝ)) *
          ((j : ℝ) + 1)
  rw [hsource]
  rw [hsym]
  field_simp [htargetroot, hsourceroot]
  rw [Real.sq_sqrt htargetdim.le,
    Real.sq_sqrt hsourcedim.le]
  linear_combination
    -(matrix n w p q L source target) * hmul

theorem johnsonSourceChannelCoefficient_reverse_eq_upperScale
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (target source : Index p q L)
    (hadj : target.val + 1 = source.val) :
    johnsonSourceChannelCoefficient n w p q L target source =
      johnsonSourceChannelCoefficient n w p q L source target *
        (((p + q + target.val : ℕ) : ℝ) + 1) /
          johnsonUpperScale n (p + q + target.val) := by
  have hhalf : 2 * (p + q + target.val + 1) ≤ n := by
    have hweight := h.window_degree_le_weight source
    omega
  have hscale := (johnsonUpperScale_pos hhalf).ne'
  exact (eq_div_iff hscale).mpr
    (johnsonSourceChannelCoefficient_reverse_mul_upperScale
      h hstrict target source hadj)

theorem johnsonSourceChannelCoefficient_reverse_sqrt_eq_upperScale
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (target source : Index p q L)
    (hadj : target.val + 1 = source.val) :
    Real.sqrt
        (johnsonSourceChannelCoefficient n w p q L target source) =
      Real.sqrt
          (johnsonSourceChannelCoefficient n w p q L source target) *
        Real.sqrt (((p + q + target.val : ℕ) : ℝ) + 1) /
          Real.sqrt (johnsonUpperScale n (p + q + target.val)) := by
  rw [johnsonSourceChannelCoefficient_reverse_eq_upperScale
    h hstrict target source hadj]
  have hsource := johnsonSourceChannelCoefficient_nonneg
    h hstrict source target
  have hdegree : 0 ≤ (((p + q + target.val : ℕ) : ℝ) + 1) := by
    positivity
  rw [Real.sqrt_div (mul_nonneg hsource hdegree),
    Real.sqrt_mul hsource]

theorem johnsonMiddleChannel_signed_axis_inner
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (x : JohnsonSphere n w)
    (source : Index p q L)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + source.val) f)
    (a : HarmonicFibreIndex n w p q)
    (hsource : 0 < p + q + source.val) :
    MetricCodes.Boolean.coordinateDot
        (johnsonDiagonalChannelSign n w p q
            (p + q + source.val) •
          johnsonMiddleChannel (p + q + source.val) f)
        (johnsonAxisTensor x
          (coupledHarmonic x h.support_half h.complement_half
            a source.val)) =
      Real.sqrt
          (johnsonSourceChannelCoefficient n w p q L source source) *
        MetricCodes.Boolean.dot f
          (coupledHarmonic x h.support_half h.complement_half
            a source.val) := by
  have hn : 0 < n := by omega
  have hclosed := johnsonMiddleChannel_coupled_axis_inner_closed
    hn x h.support_half h.complement_half
    (h.supportResidual_bound source)
    (h.complementResidual_bound source) a f hf
  have hscalar := johnsonMiddleSignedScalar_eq_sqrt_hattedDiagonal
    h hstrict source hsource
  calc
    MetricCodes.Boolean.coordinateDot
        (johnsonDiagonalChannelSign n w p q
            (p + q + source.val) •
          johnsonMiddleChannel (p + q + source.val) f)
        (johnsonAxisTensor x
          (coupledHarmonic x h.support_half h.complement_half
            a source.val)) =
      johnsonDiagonalChannelSign n w p q (p + q + source.val) *
        MetricCodes.Boolean.coordinateDot
          (johnsonMiddleChannel (p + q + source.val) f)
          (johnsonAxisTensor x
            (coupledHarmonic x h.support_half h.complement_half
              a source.val)) := by
        simpa using johnsonCoordinateDot_pi_smul
          (johnsonDiagonalChannelSign n w p q
            (p + q + source.val)) 1
          (johnsonMiddleChannel (p + q + source.val) f)
          (johnsonAxisTensor x
            (coupledHarmonic x h.support_half h.complement_half
              a source.val))
    _ = (johnsonDiagonalChannelSign n w p q (p + q + source.val) *
          ((Real.sqrt
              (johnsonMiddleScale n (p + q + source.val)))⁻¹ *
            Real.sqrt
              ((n : ℝ) /
                ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
            (((p : ℝ) - (w : ℝ) / (n : ℝ) *
                ((p + q + source.val : ℕ) : ℝ)) +
              ((source.val : ℝ) *
                (((n - w : ℕ) : ℝ) - 2 * (q : ℝ) -
                  (source.val : ℝ) + 1)) /
                (((w : ℝ) - 2 * (p : ℝ)) +
                  (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
                  2 * (source.val : ℝ) + 2)))) *
          MetricCodes.Boolean.dot f
            (coupledHarmonic x h.support_half h.complement_half
              a source.val) := by
        rw [hclosed]
        ring
    _ = Real.sqrt
          (MetricCodes.johnsonHattedDiagonal
            n w p q (p + q + source.val)) *
          MetricCodes.Boolean.dot f
            (coupledHarmonic x h.support_half h.complement_half
              a source.val) := by
        rw [hscalar]
    _ = Real.sqrt
          (johnsonSourceChannelCoefficient n w p q L source source) *
          MetricCodes.Boolean.dot f
            (coupledHarmonic x h.support_half h.complement_half
              a source.val) := by
        rw [johnsonSourceChannelCoefficient_diagonal h source]

theorem johnsonAdjacentChannel_axis_inner_of_not_active
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (x : JohnsonSphere n w)
    (target source : Index p q L)
    (f : MetricCodes.Boolean.Function n)
    (a : HarmonicFibreIndex n w p q)
    (hinactive : ¬ johnsonChannelActive p q L target source) :
    MetricCodes.Boolean.coordinateDot
        (johnsonAdjacentChannel n w p q L target source f)
        (johnsonAxisTensor x
          (coupledHarmonic x h.support_half h.complement_half
            a target.val)) =
      Real.sqrt
          (johnsonSourceChannelCoefficient n w p q L source target) *
        MetricCodes.Boolean.dot f
          (coupledHarmonic x h.support_half h.complement_half
            a source.val) := by
  rw [johnsonAdjacentChannel_eq_zero_of_not_active
    target source f hinactive,
    johnsonSourceChannelCoefficient_eq_zero_of_not_active
      source target hinactive]
  simp [MetricCodes.Boolean.coordinateDot, MetricCodes.Boolean.dot]

theorem johnsonAdjacentChannel_axis_inner_diagonal
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (x : JohnsonSphere n w)
    (source : Index p q L)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + source.val) f)
    (a : HarmonicFibreIndex n w p q) :
    MetricCodes.Boolean.coordinateDot
        (johnsonAdjacentChannel n w p q L source source f)
        (johnsonAxisTensor x
          (coupledHarmonic x h.support_half h.complement_half
            a source.val)) =
      Real.sqrt
          (johnsonSourceChannelCoefficient n w p q L source source) *
        MetricCodes.Boolean.dot f
          (coupledHarmonic x h.support_half h.complement_half
            a source.val) := by
  by_cases hsource : 0 < p + q + source.val
  · have hdown : source.val + 1 ≠ source.val := by omega
    simp only [johnsonAdjacentChannel, hdown, ↓reduceIte]
    exact johnsonMiddleChannel_signed_axis_inner
      h hstrict x source f hf a hsource
  · apply johnsonAdjacentChannel_axis_inner_of_not_active
      h x source source f a
    intro hactive
    rcases hactive with hdown | hmiddle | hup
    · omega
    · exact hsource hmiddle.2
    · omega

end MetricCodes.Johnson

end

end

section

set_option autoImplicit false

noncomputable section

namespace MetricCodes.Johnson

theorem johnsonOffDiagonal_fourthPower_grouped_algebra
    {N W C G j A B E F : ℝ}
    (hN : N ≠ 0) (hW : W ≠ 0) (hC : C ≠ 0)
    (hWj : W - j ≠ 0) (hCj : C - j ≠ 0)
    (hG : G ≠ 0) (hGminus : G - 1 ≠ 0)
    (hGplus : G + 1 ≠ 0) (hjone : j + 1 ≠ 0)
    (hlast : N - j + 1 ≠ 0) :
    (N * A * B * E * F) ^ 2 /
        (W * C * G * (G + 1)) ^ 2 / (j + 1) ^ 2 =
      (((N ^ 2 *
          ((W - j) * (C - j) * A * B * E * F)) /
          ((W * C) ^ 2 * G ^ 2 * ((G - 1) * (G + 1)))) ^ 2 /
        ((N ^ 2 *
            ((W - j) ^ 2 * (C - j) ^ 2 *
              (j + 1) * (N - j + 1))) /
          ((W * C) ^ 2 * G ^ 2 * ((G - 1) * (G + 1))))) *
        (((G - 1) * (N - j + 1)) /
          ((j + 1) * (G + 1))) := by
  field_simp [hN, hW, hC, hWj, hCj, hG,
    hGminus, hGplus, hjone, hlast]

theorem johnsonAdjacentRawSquare_compact_algebra
    {N W C P Q T : ℝ}
    (hNC : N = W + C)
    (hW : W ≠ 0) (hC : C ≠ 0)
    (hgap : N - 2 * (P + Q + T) ≠ 0)
    (hgapplus : N - 2 * (P + Q + T) + 1 ≠ 0) :
    (N / (W * C)) *
        ((T + 1) * (C - 2 * Q - T)) *
        ((((W - 2 * P) + (C - 2 * Q) - T + 1) *
            (W - 2 * P - T)) /
          (((W - 2 * P) + (C - 2 * Q) - 2 * T + 1) *
            ((W - 2 * P) + (C - 2 * Q) - 2 * T))) =
      (N * (W - (P + Q + T) - P + Q) *
        (C - (P + Q + T) + P - Q) *
        ((P + Q + T) - P - Q + 1) *
        (N - P - Q - (P + Q + T) + 1)) /
        (W * C * (N - 2 * (P + Q + T)) *
          (N - 2 * (P + Q + T) + 1)) := by
  let j : ℝ := P + Q + T
  let G : ℝ := N - 2 * j
  have hG : G ≠ 0 := hgap
  have hGone : G + 1 ≠ 0 := hgapplus
  have hden :
      ((W - 2 * P) + (C - 2 * Q) - 2 * T) = G := by
    dsimp [G, j]
    rw [hNC]
    ring
  have hdenone :
      ((W - 2 * P) + (C - 2 * Q) - 2 * T + 1) = G + 1 := by
    rw [hden]
  rw [hdenone, hden]
  change
    (N / (W * C)) *
        ((T + 1) * (C - 2 * Q - T)) *
        ((((W - 2 * P) + (C - 2 * Q) - T + 1) *
            (W - 2 * P - T)) / ((G + 1) * G)) =
      (N * (W - j - P + Q) * (C - j + P - Q) *
        (j - P - Q + 1) * (N - P - Q - j + 1)) /
        (W * C * G * (G + 1))
  field_simp [hW, hC, hG, hGone]
  dsimp [j]
  rw [hNC]
  ring

end MetricCodes.Johnson

end

end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace MetricCodes.Johnson

theorem johnsonNu_radicand_factor
    {n w p q j : ℕ} (hwn : w ≤ n) :
    ((MetricCodes.johnsonJ n j ^ 2 - MetricCodes.johnsonM n w ^ 2) *
      (MetricCodes.johnsonJ n j ^ 2 -
        MetricCodes.johnsonDelta n w p q ^ 2) *
      ((MetricCodes.johnsonSigma n w p q + 1) ^ 2 -
        MetricCodes.johnsonJ n j ^ 2)) =
      ((w : ℝ) - (j : ℝ)) *
        (((n - w : ℕ) : ℝ) - (j : ℝ)) *
        ((w : ℝ) - (j : ℝ) - (p : ℝ) + (q : ℝ)) *
        (((n - w : ℕ) : ℝ) - (j : ℝ) +
          (p : ℝ) - (q : ℝ)) *
        ((j : ℝ) - (p : ℝ) - (q : ℝ) + 1) *
        ((n : ℝ) - (p : ℝ) - (q : ℝ) - (j : ℝ) + 1) := by
  unfold MetricCodes.johnsonJ MetricCodes.johnsonM
    MetricCodes.johnsonDelta MetricCodes.johnsonSigma
    MetricCodes.johnsonJ1 MetricCodes.johnsonJ2
  rw [Nat.cast_sub hwn]
  ring

theorem johnsonNu_denominator_factor (n j : ℕ) :
    (2 * MetricCodes.johnsonJ n j - 1) *
      (2 * MetricCodes.johnsonJ n j + 1) =
      ((n : ℝ) - 2 * (j : ℝ) - 1) *
        ((n : ℝ) - 2 * (j : ℝ) + 1) := by
  unfold MetricCodes.johnsonJ
  ring

theorem johnsonNu_radicand_pos
    {n w p q L j : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (hfirst : p + q ≤ j)
    (hlast : j < MetricCodes.johnsonLastDegree n w p q) :
    0 <
      ((MetricCodes.johnsonJ n j ^ 2 - MetricCodes.johnsonM n w ^ 2) *
        (MetricCodes.johnsonJ n j ^ 2 -
          MetricCodes.johnsonDelta n w p q ^ 2) *
        ((MetricCodes.johnsonSigma n w p q + 1) ^ 2 -
          MetricCodes.johnsonJ n j ^ 2)) := by
  have hjw : j < w :=
    lt_of_lt_of_le hlast (by
      unfold MetricCodes.johnsonLastDegree
      exact min_le_left _ _)
  have hjleft : j < w - p + q :=
    lt_of_lt_of_le hlast (by
      unfold MetricCodes.johnsonLastDegree
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hjright : j < n - w + p - q :=
    lt_of_lt_of_le hlast (by
      unfold MetricCodes.johnsonLastDegree
      exact (min_le_right _ _).trans (min_le_right _ _))
  have hcompnat : j < n - w := by omega
  have hleftreal : (j : ℝ) <
      (w : ℝ) - (p : ℝ) + (q : ℝ) := by
    have hcast : (j : ℝ) < ((w - p + q : ℕ) : ℝ) := by
      exact_mod_cast hjleft
    simpa only [Nat.cast_add, Nat.cast_sub (by omega : p ≤ w)]
      using hcast
  have hrightreal : (j : ℝ) <
      ((n - w : ℕ) : ℝ) + (p : ℝ) - (q : ℝ) := by
    have hcast : (j : ℝ) < ((n - w + p - q : ℕ) : ℝ) := by
      exact_mod_cast hjright
    simpa only [Nat.cast_sub (by omega : q ≤ n - w + p),
      Nat.cast_add] using hcast
  have hfirstreal : (p : ℝ) + (q : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast hfirst
  have hjreal : (j : ℝ) < (w : ℝ) := by
    exact_mod_cast hjw
  have hcompreal : (j : ℝ) < ((n - w : ℕ) : ℝ) := by
    exact_mod_cast hcompnat
  have hlastreal :
      (p : ℝ) + (q : ℝ) + (j : ℝ) < (n : ℝ) + 1 := by
    have hnat : p + q + j < n + 1 := by omega
    exact_mod_cast hnat
  have hfactor1 : 0 < (w : ℝ) - (j : ℝ) := by linarith
  have hfactor2 : 0 < ((n - w : ℕ) : ℝ) - (j : ℝ) := by linarith
  have hfactor3 :
      0 < (w : ℝ) - (j : ℝ) - (p : ℝ) + (q : ℝ) := by
    linarith
  have hfactor4 :
      0 < ((n - w : ℕ) : ℝ) - (j : ℝ) +
        (p : ℝ) - (q : ℝ) := by
    linarith
  have hfactor5 :
      0 < (j : ℝ) - (p : ℝ) - (q : ℝ) + 1 := by
    linarith
  have hfactor6 :
      0 < (n : ℝ) - (p : ℝ) - (q : ℝ) - (j : ℝ) + 1 := by
    linarith
  rw [johnsonNu_radicand_factor (Nat.le_of_lt h.weight_lt)]
  exact mul_pos
    (mul_pos (mul_pos (mul_pos (mul_pos hfactor1 hfactor2)
      hfactor3) hfactor4) hfactor5) hfactor6

theorem johnsonNu_denominator_pos
    {n w p q L j : ℕ}
    (_ : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (hlast : j < MetricCodes.johnsonLastDegree n w p q) :
    0 <
      (2 * MetricCodes.johnsonJ n j - 1) *
        (2 * MetricCodes.johnsonJ n j + 1) := by
  have hjw : j < w :=
    lt_of_lt_of_le hlast (by
      unfold MetricCodes.johnsonLastDegree
      exact min_le_left _ _)
  have hjbound : 2 * j + 1 < n := by omega
  have hjreal : (2 : ℝ) * (j : ℝ) + 1 < (n : ℝ) := by
    exact_mod_cast hjbound
  rw [johnsonNu_denominator_factor]
  apply mul_pos <;> linarith

set_option maxHeartbeats 800000 in

theorem johnsonEdge_sq_factored
    {n w p q L j : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (hfirst : p + q ≤ j)
    (hlast : j < MetricCodes.johnsonLastDegree n w p q) :
    MetricCodes.johnsonEdge n w p q j ^ 2 =
      ((n : ℝ) ^ 2 *
        (((w : ℝ) - (j : ℝ)) *
          (((n - w : ℕ) : ℝ) - (j : ℝ)) *
          ((w : ℝ) - (j : ℝ) - (p : ℝ) + (q : ℝ)) *
          (((n - w : ℕ) : ℝ) - (j : ℝ) +
            (p : ℝ) - (q : ℝ)) *
          ((j : ℝ) - (p : ℝ) - (q : ℝ) + 1) *
          ((n : ℝ) - (p : ℝ) - (q : ℝ) - (j : ℝ) + 1))) /
        (((w : ℝ) * ((n - w : ℕ) : ℝ)) ^ 2 *
          ((n : ℝ) - 2 * (j : ℝ)) ^ 2 *
          (((n : ℝ) - 2 * (j : ℝ) - 1) *
            ((n : ℝ) - 2 * (j : ℝ) + 1))) := by
  have hrad := johnsonNu_radicand_pos h hstrict hfirst hlast
  have hden := johnsonNu_denominator_pos h hstrict hlast
  have hJ : 0 < MetricCodes.johnsonJ n j := by
    have hjw : j < w :=
      lt_of_lt_of_le hlast (by
        unfold MetricCodes.johnsonLastDegree
        exact min_le_left _ _)
    have hreal : (2 : ℝ) * (j : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 2 * j < n by omega)
    unfold MetricCodes.johnsonJ
    linarith
  have hw : (w : ℝ) ≠ 0 := by
    exact_mod_cast h.weight_pos.ne'
  have hN : ((n - w : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt h.weight_lt).ne'
  have hroot := (Real.sqrt_pos.mpr hden).ne'
  unfold MetricCodes.johnsonEdge MetricCodes.johnsonNu
  simp only [div_pow, mul_pow]
  rw [Real.sq_sqrt hrad.le, Real.sq_sqrt hden.le,
    johnsonNu_radicand_factor (Nat.le_of_lt h.weight_lt),
    johnsonNu_denominator_factor]
  unfold MetricCodes.johnsonJ
  field_simp [hw, hN, hJ.ne', hroot]

theorem johnsonZonalEdge_sq_factored
    {n w p q L j : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (hjw : j < w) :
    MetricCodes.johnsonZonalEdge n w j ^ 2 =
      ((n : ℝ) ^ 2 *
        (((w : ℝ) - (j : ℝ)) ^ 2 *
          (((n - w : ℕ) : ℝ) - (j : ℝ)) ^ 2 *
          ((j : ℝ) + 1) *
          ((n : ℝ) - (j : ℝ) + 1))) /
        (((w : ℝ) * ((n - w : ℕ) : ℝ)) ^ 2 *
          ((n : ℝ) - 2 * (j : ℝ)) ^ 2 *
          (((n : ℝ) - 2 * (j : ℝ) - 1) *
            ((n : ℝ) - 2 * (j : ℝ) + 1))) := by
  have hhalf : w ≤ n - w := by omega
  have hlast : MetricCodes.johnsonLastDegree n w 0 0 = w := by
    simp [MetricCodes.johnsonLastDegree, min_eq_left hhalf]
  let hz : AdmissibleDegrees n w 0 0 w :=
    { weight_pos := h.weight_pos
      weight_lt := h.weight_lt
      weight_half := h.weight_half
      support_half := by omega
      complement_half := by omega
      first_le := by omega
      last_le := by rw [hlast] }
  have hlast' : j < MetricCodes.johnsonLastDegree n w 0 0 := by
    simpa [hlast] using hjw
  unfold MetricCodes.johnsonZonalEdge
  rw [johnsonEdge_sq_factored hz hstrict (Nat.zero_le j) hlast']
  simp only [Nat.cast_zero, sub_zero, add_zero]
  ring

theorem johnsonSourceChannelCoefficient_sq
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (source target : Index p q L) :
    johnsonSourceChannelCoefficient n w p q L source target ^ 2 =
      matrix n w p q L source target ^ 2 *
        ((MetricCodes.booleanHarmonicDimension
          n (p + q + source.val) : ℝ) /
          (MetricCodes.booleanHarmonicDimension
            n (p + q + target.val) : ℝ)) := by
  have hsource :
      0 ≤ (MetricCodes.booleanHarmonicDimension
        n (p + q + source.val) : ℝ) := by
    exact_mod_cast (johnsonWindowHarmonicDimension_pos h source).le
  have htarget :
      0 ≤ (MetricCodes.booleanHarmonicDimension
        n (p + q + target.val) : ℝ) := by
    exact_mod_cast (johnsonWindowHarmonicDimension_pos h target).le
  unfold johnsonSourceChannelCoefficient
  simp only [div_pow, mul_pow]
  rw [Real.sq_sqrt hsource, Real.sq_sqrt htarget]
  ring

def johnsonAdjacentRawScalar
    (n w p q t : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) /
      ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
    Real.sqrt
      (MetricCodes.Boolean.harmonicCoefficient (n - w) q (t + 1)) *
    (Real.sqrt (clebschNormSq w (n - w) p q t) /
      Real.sqrt (clebschNormSq w (n - w) p q (t + 1)))

def johnsonLowerOffDiagonalScalar
    (n w p q t : ℕ) : ℝ :=
  (Real.sqrt (((p + q + (t + 1) : ℕ) : ℝ)))⁻¹ *
    johnsonAdjacentRawScalar n w p q t

def johnsonUpperOffDiagonalScalar
    (n w p q t : ℕ) : ℝ :=
  (Real.sqrt (johnsonUpperScale n (p + q + t)))⁻¹ *
    johnsonAdjacentRawScalar n w p q t

theorem johnsonAdjacentRawScalar_sq
    {n w p q t : ℕ}
    (hw : 0 < w) (hwn : w < n)
    (_ : 2 * p + (t + 1) ≤ w)
    (hcomplement : 2 * q + (t + 1) ≤ n - w) :
    johnsonAdjacentRawScalar n w p q t ^ 2 =
      ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        MetricCodes.Boolean.harmonicCoefficient (n - w) q (t + 1) *
        (clebschNormSq w (n - w) p q t /
          clebschNormSq w (n - w) p q (t + 1)) := by
  have hn : 0 < n := by omega
  have haxis :
      0 ≤ (n : ℝ) / ((w : ℝ) * ((n - w : ℕ) : ℝ)) := by
    have hw' : 0 < (w : ℝ) := by exact_mod_cast hw
    have hN : 0 < ((n - w : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt hwn
    positivity
  have hcoefficient :
      0 ≤ MetricCodes.Boolean.harmonicCoefficient (n - w) q (t + 1) :=
    (MetricCodes.Boolean.harmonicCoefficient_pos
      (Nat.succ_pos t) hcomplement).le
  have hnorm := (clebschNormSq_pos w (n - w) p q t).le
  have hnext := (clebschNormSq_pos w (n - w) p q (t + 1)).le
  unfold johnsonAdjacentRawScalar
  simp only [mul_pow, div_pow]
  rw [Real.sq_sqrt haxis, Real.sq_sqrt hcoefficient,
    Real.sq_sqrt hnorm, Real.sq_sqrt hnext]

theorem johnsonAdjacentRawScalar_sq_factored
    {n w p q t : ℕ}
    (hw : 0 < w) (hwn : w < n)
    (hsupport : 2 * p + (t + 1) ≤ w)
    (hcomplement : 2 * q + (t + 1) ≤ n - w) :
    johnsonAdjacentRawScalar n w p q t ^ 2 =
      ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (((t : ℝ) + 1) *
          (((n - w : ℕ) : ℝ) - 2 * (q : ℝ) - (t : ℝ))) *
        (((((w : ℝ) - 2 * (p : ℝ)) +
            (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) - (t : ℝ) + 1) *
            ((w : ℝ) - 2 * (p : ℝ) - (t : ℝ))) /
          (((((w : ℝ) - 2 * (p : ℝ)) +
              (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
              2 * (t : ℝ) + 1) *
            (((w : ℝ) - 2 * (p : ℝ)) +
              (((n - w : ℕ) : ℝ) - 2 * (q : ℝ)) -
              2 * (t : ℝ))))) := by
  rw [johnsonAdjacentRawScalar_sq hw hwn hsupport hcomplement,
    clebschNormSq_div_succ hsupport hcomplement]
  unfold MetricCodes.Boolean.harmonicCoefficient
  push_cast
  ring

theorem johnsonAdjacentRawScalar_pos
    {n w p q t : ℕ}
    (hw : 0 < w) (hwn : w < n)
    (_ : 2 * p + (t + 1) ≤ w)
    (hcomplement : 2 * q + (t + 1) ≤ n - w) :
    0 < johnsonAdjacentRawScalar n w p q t := by
  have hn : 0 < n := by omega
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hwreal : 0 < (w : ℝ) := by exact_mod_cast hw
  have hcomp : 0 < ((n - w : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hwn
  have hcoefficient :
      0 < MetricCodes.Boolean.harmonicCoefficient (n - w) q (t + 1) :=
    MetricCodes.Boolean.harmonicCoefficient_pos
      (Nat.succ_pos t) hcomplement
  have hnorm := clebschNormSq_pos w (n - w) p q t
  have hnext := clebschNormSq_pos w (n - w) p q (t + 1)
  unfold johnsonAdjacentRawScalar
  positivity

theorem johnsonLowerOffDiagonalScalar_sq
    {n w p q t : ℕ}
    (_ : 0 < p + q + (t + 1)) :
    johnsonLowerOffDiagonalScalar n w p q t ^ 2 =
      johnsonAdjacentRawScalar n w p q t ^ 2 /
        (((p + q + (t + 1) : ℕ) : ℝ)) := by
  have hdegree' : 0 ≤ (((p + q + (t + 1) : ℕ) : ℝ)) := by
    positivity
  unfold johnsonLowerOffDiagonalScalar
  rw [mul_pow, inv_pow, Real.sq_sqrt hdegree']
  ring

theorem johnsonSourceChannelCoefficient_lower_sq
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (target source : Index p q L)
    (hadj : target.val + 1 = source.val) :
    johnsonSourceChannelCoefficient n w p q L source target ^ 2 =
      MetricCodes.johnsonHattedEdge n w p q (p + q + target.val) ^ 2 *
        ((MetricCodes.booleanHarmonicDimension
          n (p + q + source.val) : ℝ) /
          (MetricCodes.booleanHarmonicDimension
            n (p + q + target.val) : ℝ)) := by
  have hne : source ≠ target := by
    intro heq
    subst source
    omega
  have hnotup : source.val + 1 ≠ target.val := by omega
  rw [johnsonSourceChannelCoefficient_sq h source target]
  simp [matrix, MetricCodes.johnsonJacobiMatrix, hne,
    hnotup, hadj]

end MetricCodes.Johnson

end

end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators InnerProductSpace

namespace MetricCodes.Johnson

theorem johnsonAdjacentRawScalar_sq_degree_factored
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (target source : Index p q L)
    (hadj : target.val + 1 = source.val) :
    johnsonAdjacentRawScalar n w p q target.val ^ 2 =
      ((n : ℝ) *
        ((w : ℝ) - ((p + q + target.val : ℕ) : ℝ) -
          (p : ℝ) + (q : ℝ)) *
        (((n - w : ℕ) : ℝ) -
          ((p + q + target.val : ℕ) : ℝ) +
          (p : ℝ) - (q : ℝ)) *
        (((p + q + target.val : ℕ) : ℝ) -
          (p : ℝ) - (q : ℝ) + 1) *
        ((n : ℝ) - (p : ℝ) - (q : ℝ) -
          ((p + q + target.val : ℕ) : ℝ) + 1)) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ) *
          ((n : ℝ) - 2 * ((p + q + target.val : ℕ) : ℝ)) *
          ((n : ℝ) - 2 * ((p + q + target.val : ℕ) : ℝ) + 1)) := by
  have hsupport := h.supportResidual_bound source
  have hcomplement := h.complementResidual_bound source
  have hsupport' : 2 * p + (target.val + 1) ≤ w := by omega
  have hcomplement' :
      2 * q + (target.val + 1) ≤ n - w := by omega
  have hj := h.window_degree_le_weight target
  have hgap :
      (n : ℝ) -
        2 * ((p : ℝ) + (q : ℝ) + (target.val : ℝ)) ≠ 0 := by
    have hnat : 2 * (p + q + target.val) < n := by omega
    have hreal :
        (2 : ℝ) * ((p + q + target.val : ℕ) : ℝ) < (n : ℝ) := by
      exact_mod_cast hnat
    push_cast at hreal
    linarith
  have hgapplus :
      (n : ℝ) -
        2 * ((p : ℝ) + (q : ℝ) + (target.val : ℝ)) + 1 ≠ 0 := by
    have hnat : 2 * (p + q + target.val) < n := by omega
    have hreal :
        (2 : ℝ) * ((p + q + target.val : ℕ) : ℝ) < (n : ℝ) := by
      exact_mod_cast hnat
    push_cast at hreal
    linarith
  have hNC : (n : ℝ) = (w : ℝ) + ((n - w : ℕ) : ℝ) := by
    rw [Nat.cast_sub (Nat.le_of_lt h.weight_lt)]
    ring
  have hw : (w : ℝ) ≠ 0 := by
    exact_mod_cast h.weight_pos.ne'
  have hC : ((n - w : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt h.weight_lt).ne'
  rw [johnsonAdjacentRawScalar_sq_factored
    h.weight_pos h.weight_lt hsupport' hcomplement']
  have halgebra := johnsonAdjacentRawSquare_compact_algebra
    (N := (n : ℝ)) (W := (w : ℝ))
    (C := ((n - w : ℕ) : ℝ))
    (P := (p : ℝ)) (Q := (q : ℝ))
    (T := (target.val : ℝ))
    hNC hw hC hgap hgapplus
  convert halgebra using 1 ; push_cast ; ring

set_option maxRecDepth 2048 in

theorem johnsonLowerOffDiagonalScalar_fourthPower
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (target source : Index p q L)
    (hadj : target.val + 1 = source.val) :
    johnsonLowerOffDiagonalScalar n w p q target.val ^ 4 =
      johnsonSourceChannelCoefficient n w p q L source target ^ 2 := by
  let j : ℕ := p + q + target.val
  have hjw : j < w := by
    have hsource := h.window_degree_le_weight source
    dsimp [j]
    omega
  have hlast : j < MetricCodes.johnsonLastDegree n w p q := by
    have hsource := h.window_degree_le_weight source
    have hwindow : p + q + source.val ≤ L := by
      have hi := source.isLt
      have hfirst := h.first_le
      omega
    have hlast' := h.last_le
    dsimp [j]
    omega
  have hfirst : p + q ≤ j := by
    dsimp [j]
    omega
  have hdegree : p + q + source.val = j + 1 := by
    dsimp [j]
    omega
  have hhalf : 2 * (j + 1) ≤ n := by
    have hsource := h.window_degree_half source
    omega
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show 0 < n by omega).ne'
  have hw : (w : ℝ) ≠ 0 := by
    exact_mod_cast h.weight_pos.ne'
  have hC : ((n - w : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt h.weight_lt).ne'
  have hjreal : (j : ℝ) < (w : ℝ) := by
    exact_mod_cast hjw
  have hCreal : (j : ℝ) < ((n - w : ℕ) : ℝ) := by
    exact_mod_cast (show j < n - w by omega)
  have hgapreal :
      (2 : ℝ) * (j : ℝ) + 1 < (n : ℝ) := by
    exact_mod_cast (show 2 * j + 1 < n by omega)
  have hWj : (w : ℝ) - (j : ℝ) ≠ 0 := by linarith
  have hCj : ((n - w : ℕ) : ℝ) - (j : ℝ) ≠ 0 := by linarith
  have hgap : (n : ℝ) - 2 * (j : ℝ) ≠ 0 := by linarith
  have hgapminus : (n : ℝ) - 2 * (j : ℝ) - 1 ≠ 0 := by
    linarith
  have hgapplus : (n : ℝ) - 2 * (j : ℝ) + 1 ≠ 0 := by
    linarith
  have hjone : (j : ℝ) + 1 ≠ 0 := by positivity
  have hlastreal : (n : ℝ) - (j : ℝ) + 1 ≠ 0 := by
    have hjn : (j : ℝ) < (n : ℝ) := by
      exact_mod_cast (show j < n by omega)
    linarith
  have halgebra := johnsonOffDiagonal_fourthPower_grouped_algebra
    (N := (n : ℝ)) (W := (w : ℝ))
    (C := ((n - w : ℕ) : ℝ))
    (G := (n : ℝ) - 2 * (j : ℝ))
    (j := (j : ℝ))
    (A := (w : ℝ) - (j : ℝ) - (p : ℝ) + (q : ℝ))
    (B := ((n - w : ℕ) : ℝ) - (j : ℝ) +
      (p : ℝ) - (q : ℝ))
    (E := (j : ℝ) - (p : ℝ) - (q : ℝ) + 1)
    (F := (n : ℝ) - (p : ℝ) - (q : ℝ) - (j : ℝ) + 1)
    hn hw hC hWj hCj hgap hgapminus hgapplus hjone hlastreal
  rw [show johnsonLowerOffDiagonalScalar
      n w p q target.val ^ 4 =
        (johnsonLowerOffDiagonalScalar
          n w p q target.val ^ 2) ^ 2 by ring,
    johnsonLowerOffDiagonalScalar_sq (by omega),
    johnsonAdjacentRawScalar_sq_degree_factored
      h hstrict target source hadj,
    johnsonSourceChannelCoefficient_lower_sq h target source hadj]
  rw [hdegree]
  change
    (_ / (((p + q + (target.val + 1) : ℕ) : ℝ))) ^ 2 =
      MetricCodes.johnsonHattedEdge n w p q j ^ 2 *
        ((MetricCodes.booleanHarmonicDimension n (j + 1) : ℝ) /
          (MetricCodes.booleanHarmonicDimension n j : ℝ))
  rw [booleanHarmonicDimension_succ_div hhalf]
  unfold MetricCodes.johnsonHattedEdge
  simp only [div_pow]
  rw [johnsonEdge_sq_factored h hstrict hfirst hlast,
    johnsonZonalEdge_sq_factored h hstrict hjw]
  dsimp [j] at halgebra ⊢
  push_cast at halgebra ⊢
  simpa only [add_assoc, mul_assoc] using halgebra

theorem johnsonLowerOffDiagonalScalar_eq_sqrt_source
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (target source : Index p q L)
    (hadj : target.val + 1 = source.val) :
    johnsonLowerOffDiagonalScalar n w p q target.val =
      Real.sqrt
        (johnsonSourceChannelCoefficient
          n w p q L source target) := by
  have hsupport := h.supportResidual_bound source
  have hcomplement := h.complementResidual_bound source
  have hsupport' : 2 * p + (target.val + 1) ≤ w := by omega
  have hcomplement' :
      2 * q + (target.val + 1) ≤ n - w := by omega
  have hraw := johnsonAdjacentRawScalar_pos
    h.weight_pos h.weight_lt hsupport' hcomplement'
  have hdegree : 0 < ((p + q + (target.val + 1) : ℕ) : ℝ) := by
    positivity
  have hleft :
      0 < johnsonLowerOffDiagonalScalar n w p q target.val := by
    unfold johnsonLowerOffDiagonalScalar
    positivity
  have hright := johnsonSourceChannelCoefficient_nonneg
    h hstrict source target
  have hfourth := johnsonLowerOffDiagonalScalar_fourthPower
    h hstrict target source hadj
  have hsquare :
      johnsonLowerOffDiagonalScalar n w p q target.val ^ 2 =
        johnsonSourceChannelCoefficient
          n w p q L source target := by
    nlinarith [sq_nonneg
      (johnsonLowerOffDiagonalScalar n w p q target.val ^ 2 -
        johnsonSourceChannelCoefficient n w p q L source target)]
  have hroot := Real.sq_sqrt hright
  nlinarith [Real.sqrt_nonneg
    (johnsonSourceChannelCoefficient n w p q L source target)]

theorem johnsonUpperOffDiagonalScalar_eq_sqrt_source
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (target source : Index p q L)
    (hadj : target.val + 1 = source.val) :
    johnsonUpperOffDiagonalScalar n w p q target.val =
      Real.sqrt
        (johnsonSourceChannelCoefficient
          n w p q L target source) := by
  have hhalf :
      2 * ((p + q + target.val) + 1) ≤ n := by
    have hsource := h.window_degree_half source
    omega
  have hscale := johnsonUpperScale_pos hhalf
  have hdegree :
      0 < (((p + q + target.val : ℕ) : ℝ) + 1) := by
    positivity
  have hrootdegree :
      Real.sqrt (((p + q + target.val : ℕ) : ℝ) + 1) ≠ 0 :=
    (Real.sqrt_pos.mpr hdegree).ne'
  have hrootscale :
      Real.sqrt (johnsonUpperScale n (p + q + target.val)) ≠ 0 :=
    (Real.sqrt_pos.mpr hscale).ne'
  rw [johnsonSourceChannelCoefficient_reverse_sqrt_eq_upperScale
    h hstrict target source hadj,
    ← johnsonLowerOffDiagonalScalar_eq_sqrt_source
      h hstrict target source hadj]
  unfold johnsonUpperOffDiagonalScalar
    johnsonLowerOffDiagonalScalar
  have hcast :
      (((p + q + (target.val + 1) : ℕ) : ℝ)) =
        (((p + q + target.val : ℕ) : ℝ) + 1) := by
    push_cast
    ring
  rw [hcast]
  field_simp [hrootdegree, hrootscale]

theorem johnsonCoordinateDot_smul_left
    {n : ℕ} (c : ℝ)
    (f g : MetricCodes.Boolean.CoordinateFunction n) :
    MetricCodes.Boolean.coordinateDot (c • f) g =
      c * MetricCodes.Boolean.coordinateDot f g := by
  simpa using johnsonCoordinateDot_pi_smul c (1 : ℝ) f g

theorem johnsonAdjacentChannel_axis_inner
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (x : JohnsonSphere n w)
    (target source : Index p q L)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + source.val) f)
    (a : HarmonicFibreIndex n w p q) :
    MetricCodes.Boolean.coordinateDot
        (johnsonAdjacentChannel n w p q L target source f)
        (johnsonAxisTensor x
          (coupledHarmonic x h.support_half h.complement_half
            a target.val)) =
      Real.sqrt
          (johnsonSourceChannelCoefficient
            n w p q L source target) *
        MetricCodes.Boolean.dot f
          (coupledHarmonic x h.support_half h.complement_half
            a source.val) := by
  classical
  by_cases hdown : target.val + 1 = source.val
  · have hsupport := h.supportResidual_bound source
    have hcomplement := h.complementResidual_bound source
    have hsupport' : 2 * p + (target.val + 1) ≤ w := by omega
    have hcomplement' :
        2 * q + (target.val + 1) ≤ n - w := by omega
    have hsourceval : source.val = target.val + 1 := by omega
    have hf' :
        MetricCodes.Boolean.IsHarmonic
          (p + q + (target.val + 1)) f := by
      simpa [hsourceval] using hf
    have hclosed := johnsonLowerChannel_coupled_axis_inner_closed
      x h.support_half h.complement_half
      hsupport' hcomplement' a f hf'
    have hscalar := johnsonLowerOffDiagonalScalar_eq_sqrt_source
      h hstrict target source hdown
    simp only [johnsonAdjacentChannel, hdown, ↓reduceIte]
    rw [hsourceval, johnsonCoordinateDot_smul_left, hclosed]
    rw [← hscalar]
    unfold johnsonLowerOffDiagonalScalar johnsonAdjacentRawScalar
    ring
  · by_cases hdiag : target = source
    · subst target
      exact johnsonAdjacentChannel_axis_inner_diagonal
        h hstrict x source f hf a
    · by_cases hup : source.val + 1 = target.val
      · have hsupport := h.supportResidual_bound target
        have hcomplement := h.complementResidual_bound target
        have hsupport' : 2 * p + (source.val + 1) ≤ w := by
          omega
        have hcomplement' :
            2 * q + (source.val + 1) ≤ n - w := by
          omega
        have hclosed := johnsonUpperChannel_coupled_axis_inner_closed
          x h.support_half h.complement_half
          hsupport' hcomplement' a f hf
        have hscalar := johnsonUpperOffDiagonalScalar_eq_sqrt_source
          h hstrict source target hup
        simp only [johnsonAdjacentChannel, hdown, hdiag, hup,
          ↓reduceIte]
        rw [johnsonCoordinateDot_smul_left]
        have htargetval : target.val = source.val + 1 := by omega
        rw [htargetval, hclosed]
        rw [← hscalar]
        unfold johnsonUpperOffDiagonalScalar johnsonAdjacentRawScalar
        ring
      · apply johnsonAdjacentChannel_axis_inner_of_not_active
          h x target source f a
        intro hactive
        rcases hactive with hfirst | hmiddle | hlast
        · exact hdown hfirst
        · exact hdiag hmiddle.1
        · exact hup hlast

end MetricCodes.Johnson

end

end

section

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped Topology

namespace MetricCodes.MRRW

theorem hasDerivAt_mul_continuous_zero
    (g : ℝ → ℝ) (hg : ContinuousAt g 0) (hgzero : g 0 = 0) :
    HasDerivAt (fun r : ℝ => r * g r) 0 0 := by
  apply (hasDerivAt_iff_tendsto_slope_zero).2
  have htend : Tendsto g (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa [hgzero] using
      hg.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  have hquotient :
      Tendsto (fun r : ℝ => r⁻¹ * (r * g r))
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    refine (tendsto_congr' ?_).2 htend
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hrzero : r ≠ 0 := by simpa using hr
    field_simp [hrzero]
  simpa [smul_eq_mul] using hquotient

def inverseDegree (r : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - r ^ 2)) / 2

def inverseVarianceFactor (r : ℝ) : ℝ :=
  (2 * (1 + Real.sqrt (1 - r ^ 2)))⁻¹

theorem inverseVarianceFactor_continuous :
    Continuous inverseVarianceFactor := by
  unfold inverseVarianceFactor
  apply Continuous.inv₀
  · fun_prop
  · intro r
    have hroot : 0 ≤ Real.sqrt (1 - r ^ 2) :=
      Real.sqrt_nonneg _
    positivity

theorem inverseDegree_eq_sq_mul_factor
    {r : ℝ} (hr : r ^ 2 ≤ 1) :
    inverseDegree r = r * (r * inverseVarianceFactor r) := by
  have hradical : 0 ≤ 1 - r ^ 2 := by linarith
  have hsquare := Real.sq_sqrt hradical
  have hroot : 0 ≤ Real.sqrt (1 - r ^ 2) :=
    Real.sqrt_nonneg _
  have hdenominator :
      1 + Real.sqrt (1 - r ^ 2) ≠ 0 := by
    positivity
  unfold inverseDegree inverseVarianceFactor
  field_simp [hdenominator]
  nlinarith

def inverseEntropyFactor (r : ℝ) : ℝ :=
  inverseVarianceFactor r * Real.negMulLog r +
    Real.negMulLog (r * inverseVarianceFactor r)

theorem inverseEntropyFactor_continuous :
    Continuous inverseEntropyFactor := by
  unfold inverseEntropyFactor
  exact
    (inverseVarianceFactor_continuous.mul
      Real.continuous_negMulLog).add
      (Real.continuous_negMulLog.comp
        (continuous_id.mul inverseVarianceFactor_continuous))

@[simp] theorem inverseEntropyFactor_zero :
    inverseEntropyFactor 0 = 0 := by
  simp [inverseEntropyFactor, inverseVarianceFactor]

theorem negMulLog_inverseDegree_eventually :
    (fun r : ℝ => Real.negMulLog (inverseDegree r)) =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ => r * inverseEntropyFactor r) := by
  have hsmall : ∀ᶠ r : ℝ in 𝓝 0, r ^ 2 < 1 :=
    (continuousAt_id.pow 2).tendsto
      (gt_mem_nhds (by norm_num : (0 : ℝ) ^ 2 < 1))
  filter_upwards [hsmall] with r hr
  rw [inverseDegree_eq_sq_mul_factor hr.le,
    Real.negMulLog_mul]
  unfold inverseEntropyFactor
  ring

theorem hasDerivAt_negMulLog_inverseDegree_zero :
    HasDerivAt (fun r : ℝ => Real.negMulLog (inverseDegree r)) 0 0 := by
  exact
    (hasDerivAt_mul_continuous_zero inverseEntropyFactor
      inverseEntropyFactor_continuous.continuousAt
      inverseEntropyFactor_zero).congr_of_eventuallyEq
      negMulLog_inverseDegree_eventually

theorem hasDerivAt_inverseDegree_zero :
    HasDerivAt inverseDegree 0 0 := by
  have hradical :
      HasDerivAt (fun r : ℝ => 1 - r ^ 2) 0 0 := by
    simpa using
      ((hasDerivAt_id (0 : ℝ)).pow 2).const_sub (1 : ℝ)
  have hroot :
      HasDerivAt (fun r : ℝ => Real.sqrt (1 - r ^ 2)) 0 0 := by
    simpa using
      hradical.sqrt (by norm_num : (1 : ℝ) - 0 ^ 2 ≠ 0)
  unfold inverseDegree
  simpa [Function.comp_def] using
    ((hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub
      hroot).div_const (2 : ℝ)

theorem hasDerivAt_mrrwG_sq_zero :
    HasDerivAt
      (fun r : ℝ => MetricCodes.Johnson.mrrwG (r ^ 2)) 0 0 := by
  have hcomplement :
      HasDerivAt
        (fun r : ℝ => Real.negMulLog (1 - inverseDegree r)) 0 0 := by
    have hinner :
        HasDerivAt (fun r : ℝ => 1 - inverseDegree r) 0 0 := by
      change
        HasDerivAt
          ((fun _ : ℝ => (1 : ℝ)) - inverseDegree) 0 0
      simpa using
        (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub
          hasDerivAt_inverseDegree_zero
    have houter :
        HasDerivAt Real.negMulLog (-1) (1 - inverseDegree 0) := by
      simpa [inverseDegree] using
        Real.hasDerivAt_negMulLog (by norm_num : (1 : ℝ) ≠ 0)
    simpa [Function.comp_def] using houter.comp 0 hinner
  have hentropy :
      HasDerivAt
        (fun r : ℝ =>
          (Real.negMulLog (inverseDegree r) +
            Real.negMulLog (1 - inverseDegree r)) / Real.log 2)
        0 0 := by
    simpa [Function.comp_def] using
      (hasDerivAt_negMulLog_inverseDegree_zero.add
        hcomplement).div_const (Real.log 2)
  have hfunctions :
      (fun r : ℝ => MetricCodes.Johnson.mrrwG (r ^ 2)) =
        (fun r : ℝ =>
          (Real.negMulLog (inverseDegree r) +
            Real.negMulLog (1 - inverseDegree r)) / Real.log 2) := by
    funext r
    unfold MetricCodes.Johnson.mrrwG inverseDegree
    rw [MetricCodes.Johnson.binaryEntropy_eq_binEntropy_div_log,
      Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rw [hfunctions]
  exact hentropy

def lowerEndpointRoot (δ : ℝ) : ℝ :=
  Real.sqrt (1 - 2 * δ)

def lowerEndpointWeight (δ : ℝ) : ℝ :=
  (1 - lowerEndpointRoot δ) / 2

def lowerEndpointDerivative (δ : ℝ) : ℝ :=
  δ *
    (Real.log (1 - lowerEndpointWeight δ) -
      Real.log (lowerEndpointWeight δ)) /
      (2 * lowerEndpointRoot δ * Real.log 2)

theorem lowerEndpointRoot_pos {δ : ℝ}
    (hhalf : δ < (1 : ℝ) / 2) :
    0 < lowerEndpointRoot δ := by
  unfold lowerEndpointRoot
  apply Real.sqrt_pos.mpr
  linarith

theorem lowerEndpointRoot_lt_one {δ : ℝ}
    (hδ : 0 < δ) :
    lowerEndpointRoot δ < 1 := by
  unfold lowerEndpointRoot
  apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
  linarith

theorem lowerEndpointWeight_pos {δ : ℝ}
    (hδ : 0 < δ) :
    0 < lowerEndpointWeight δ := by
  unfold lowerEndpointWeight
  linarith [lowerEndpointRoot_lt_one hδ]

theorem lowerEndpointWeight_lt_half {δ : ℝ}
    (hhalf : δ < (1 : ℝ) / 2) :
    lowerEndpointWeight δ < (1 : ℝ) / 2 := by
  unfold lowerEndpointWeight
  linarith [lowerEndpointRoot_pos hhalf]

theorem lowerEndpointDerivative_pos {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    0 < lowerEndpointDerivative δ := by
  have hweight := lowerEndpointWeight_pos hδ
  have hhalfweight := lowerEndpointWeight_lt_half hhalf
  have hlog :
      Real.log (lowerEndpointWeight δ) <
        Real.log (1 - lowerEndpointWeight δ) :=
    Real.log_lt_log hweight (by linarith)
  have hroot := lowerEndpointRoot_pos hhalf
  have hlogtwo : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  unfold lowerEndpointDerivative
  exact div_pos
    (mul_pos hδ (sub_pos.mpr hlog))
    (by positivity)

theorem hasDerivAt_mrrwG_boundary_quadratic_zero
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    HasDerivAt
      (fun r : ℝ =>
        MetricCodes.Johnson.mrrwG (r ^ 2 + 2 * δ * r + 2 * δ))
      (lowerEndpointDerivative δ) 0 := by
  have hquadratic :
      HasDerivAt
        (fun r : ℝ => r ^ 2 + 2 * δ * r + 2 * δ)
        (2 * δ) 0 := by
    simpa [id_eq] using
      (((hasDerivAt_id (0 : ℝ)).pow 2).add
        ((hasDerivAt_id (0 : ℝ)).const_mul (2 * δ))).add_const
          (2 * δ)
  have hradical :
      HasDerivAt
        (fun r : ℝ =>
          1 - (r ^ 2 + 2 * δ * r + 2 * δ))
        (-2 * δ) 0 := by
    simpa using hquadratic.const_sub (1 : ℝ)
  have hradicalzero :
      1 - ((0 : ℝ) ^ 2 + 2 * δ * 0 + 2 * δ) ≠ 0 := by
    have hpositive : 0 < 1 - 2 * δ := by linarith
    simpa using hpositive.ne'
  have hroot :
      HasDerivAt
        (fun r : ℝ =>
          Real.sqrt (1 - (r ^ 2 + 2 * δ * r + 2 * δ)))
        ((-2 * δ) / (2 * lowerEndpointRoot δ)) 0 := by
    simpa [lowerEndpointRoot] using
      hradical.sqrt hradicalzero
  have hnumerator :
      HasDerivAt
        ((fun _ : ℝ => (1 : ℝ)) -
          (fun r : ℝ =>
            Real.sqrt (1 - (r ^ 2 + 2 * δ * r + 2 * δ))))
        (0 - ((-2 * δ) / (2 * lowerEndpointRoot δ))) 0 :=
    (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub hroot
  have hprobability :
      HasDerivAt
        (fun r : ℝ =>
          (1 - Real.sqrt
            (1 - (r ^ 2 + 2 * δ * r + 2 * δ))) / 2)
        (δ / (2 * lowerEndpointRoot δ)) 0 := by
    change
      HasDerivAt
        (fun r : ℝ =>
          (((fun _ : ℝ => (1 : ℝ)) -
            (fun s : ℝ =>
              Real.sqrt (1 - (s ^ 2 + 2 * δ * s + 2 * δ)))) r) /
            (2 : ℝ))
        (δ / (2 * lowerEndpointRoot δ)) 0
    exact
      (hnumerator.div_const (2 : ℝ)).congr_deriv (by ring)
  have hweight := lowerEndpointWeight_pos hδ
  have hweightone :
      lowerEndpointWeight δ ≠ 1 := by
    have h := lowerEndpointWeight_lt_half hhalf
    linarith
  have hentropyfun :
      MetricCodes.binaryEntropy =
        (fun a : ℝ => Real.binEntropy a / Real.log 2) :=
    funext MetricCodes.Johnson.binaryEntropy_eq_binEntropy_div_log
  have hbinary :
      HasDerivAt MetricCodes.binaryEntropy
        ((Real.log (1 - lowerEndpointWeight δ) -
          Real.log (lowerEndpointWeight δ)) / Real.log 2)
        (lowerEndpointWeight δ) := by
    rw [hentropyfun]
    exact
      (Real.hasDerivAt_binEntropy hweight.ne'
        hweightone).div_const (Real.log 2)
  have hbinaryzero :
      HasDerivAt MetricCodes.binaryEntropy
        ((Real.log (1 - lowerEndpointWeight δ) -
          Real.log (lowerEndpointWeight δ)) / Real.log 2)
        ((1 - Real.sqrt
          (1 - ((0 : ℝ) ^ 2 + 2 * δ * 0 + 2 * δ))) / 2) := by
    simpa [lowerEndpointWeight, lowerEndpointRoot] using hbinary
  change
    HasDerivAt
      (fun r : ℝ =>
        MetricCodes.binaryEntropy
          ((1 - Real.sqrt
            (1 - (r ^ 2 + 2 * δ * r + 2 * δ))) / 2))
      (lowerEndpointDerivative δ) 0
  have hcoeff :
      ((Real.log (1 - lowerEndpointWeight δ) -
        Real.log (lowerEndpointWeight δ)) / Real.log 2) *
          (δ / (2 * lowerEndpointRoot δ)) =
        lowerEndpointDerivative δ := by
    unfold lowerEndpointDerivative
    field_simp [(lowerEndpointRoot_pos hhalf).ne',
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  exact (hbinaryzero.comp 0 hprobability).congr_deriv hcoeff

theorem hasDerivAt_mrrwObjective_zero
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    HasDerivAt (MetricCodes.Johnson.mrrwObjective δ)
      (-lowerEndpointDerivative δ) 0 := by
  unfold MetricCodes.Johnson.mrrwObjective
  change
    HasDerivAt
      (((fun _ : ℝ => (1 : ℝ)) +
        (fun r : ℝ => MetricCodes.Johnson.mrrwG (r ^ 2))) -
        (fun r : ℝ =>
          MetricCodes.Johnson.mrrwG (r ^ 2 + 2 * δ * r + 2 * δ)))
      (-lowerEndpointDerivative δ) 0
  simpa using
    ((hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).add
      hasDerivAt_mrrwG_sq_zero).sub
        (hasDerivAt_mrrwG_boundary_quadratic_zero hδ hhalf)

theorem exists_mrrwObjective_lt_zero
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    ∃ r : ℝ, 0 < r ∧ r < 1 - 2 * δ ∧
      MetricCodes.Johnson.mrrwObjective δ r <
        MetricCodes.Johnson.mrrwObjective δ 0 := by
  have hderivative := lowerEndpointDerivative_pos hδ hhalf
  have hslope :=
    (hasDerivAt_mrrwObjective_zero hδ hhalf).tendsto_slope_zero_right
  have hnegative :
      ∀ᶠ r : ℝ in 𝓝[>] 0,
        r⁻¹ *
          (MetricCodes.Johnson.mrrwObjective δ r -
            MetricCodes.Johnson.mrrwObjective δ 0) < 0 := by
    have h :=
      hslope.eventually
        (gt_mem_nhds (by linarith :
          -lowerEndpointDerivative δ < 0))
    filter_upwards [h] with r hr
    simpa [smul_eq_mul] using hr
  have hupper :
      ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 - 2 * δ :=
    nhdsWithin_le_nhds
      (gt_mem_nhds (by linarith : (0 : ℝ) < 1 - 2 * δ))
  have hwitness :
      ∀ᶠ r : ℝ in 𝓝[>] 0,
        0 < r ∧ r < 1 - 2 * δ ∧
          MetricCodes.Johnson.mrrwObjective δ r <
            MetricCodes.Johnson.mrrwObjective δ 0 := by
    filter_upwards [hnegative, hupper, self_mem_nhdsWithin]
      with r hquotient hrupper (hr : 0 < r)
    refine ⟨hr, hrupper, ?_⟩
    apply sub_neg.mp
    calc
      MetricCodes.Johnson.mrrwObjective δ r -
          MetricCodes.Johnson.mrrwObjective δ 0 =
        r *
          (r⁻¹ *
            (MetricCodes.Johnson.mrrwObjective δ r -
              MetricCodes.Johnson.mrrwObjective δ 0)) := by
          field_simp [hr.ne']
      _ < 0 := mul_neg_of_pos_of_neg hr hquotient
  exact hwitness.exists

theorem mrrw_minimizer_pos
    {δ r : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2)
    (hr : 0 ≤ r) (hupper : r ≤ 1 - 2 * δ)
    (hmin : ∀ s : ℝ, 0 ≤ s → s ≤ 1 - 2 * δ →
      MetricCodes.Johnson.mrrwObjective δ r ≤
        MetricCodes.Johnson.mrrwObjective δ s) :
    0 < r := by
  rcases hr.eq_or_lt with hzero | hpositive
  · have hrzero : r = 0 := hzero.symm
    subst r
    obtain ⟨s, hs, hsupper, hstrict⟩ :=
      exists_mrrwObjective_lt_zero hδ hhalf
    exact False.elim
      ((not_lt_of_ge (hmin s hs.le hsupper.le)) hstrict)
  · exact hpositive

theorem exists_positive_mrrw_minimizer
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 - 2 * δ ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ 1 - 2 * δ →
        MetricCodes.Johnson.mrrwObjective δ r ≤
          MetricCodes.Johnson.mrrwObjective δ s) ∧
      MetricCodes.Johnson.mrrwRate δ =
        MetricCodes.Johnson.mrrwObjective δ r := by
  obtain ⟨r, hr, hupper, hmin⟩ :=
    MetricCodes.Johnson.exists_mrrw_minimizer hhalf.le
  refine ⟨r, mrrw_minimizer_pos hδ hhalf hr hupper hmin,
    hupper, hmin, ?_⟩
  exact MetricCodes.Johnson.mrrwRate_eq_objective_of_minimizer
    hr hupper hmin

def inverseWeight (δ r : ℝ) : ℝ :=
  (1 - Real.sqrt
    (1 - (r ^ 2 + 2 * δ * r + 2 * δ))) / 2

set_option maxHeartbeats 1200000 in

theorem inverse_zero_fibre_boundary
    {δ r : ℝ}
    (hδ : 0 < δ) (_ : δ < (1 : ℝ) / 2)
    (hr : 0 < r) (hupper : r < 1 - 2 * δ) :
    ∃ a u : ℝ,
      0 < u ∧ u < a ∧ a < (1 : ℝ) / 2 ∧
      δ / 2 < a ∧
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a ∧
      MetricCodes.Johnson.mrrwObjective δ r =
        MetricCodes.Johnson.shellRate a 0 0 u := by
  have hrplus : 0 < 1 + r := by linarith
  have hrminus : 0 < 1 - r := by linarith
  have hmargin : 0 < 1 - 2 * δ - r := by linarith
  have hrvariance : 0 < 1 - r ^ 2 := by
    nlinarith only [mul_pos hrminus hrplus]
  have hquadratic :
      0 < 1 - (r ^ 2 + 2 * δ * r + 2 * δ) := by
    nlinarith only [mul_pos hrplus hmargin]
  have hradorder :
      1 - (r ^ 2 + 2 * δ * r + 2 * δ) <
        1 - r ^ 2 := by
    nlinarith only [mul_pos hδ hrplus]
  have hrootorder :
      Real.sqrt (1 - (r ^ 2 + 2 * δ * r + 2 * δ)) <
        Real.sqrt (1 - r ^ 2) :=
    Real.sqrt_lt_sqrt hquadratic.le hradorder
  have hrootlt : Real.sqrt (1 - r ^ 2) < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
    nlinarith only [mul_pos hr hr]
  have hsmallroot :
      0 < Real.sqrt
        (1 - (r ^ 2 + 2 * δ * r + 2 * δ)) :=
    Real.sqrt_pos.mpr hquadratic
  have hdegreesquare :
      Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 :=
    Real.sq_sqrt hrvariance.le
  have hweightsquare :
      Real.sqrt (1 - (r ^ 2 + 2 * δ * r + 2 * δ)) ^ 2 =
        1 - (r ^ 2 + 2 * δ * r + 2 * δ) :=
    Real.sq_sqrt hquadratic.le
  let u : ℝ := inverseDegree r
  let a : ℝ := inverseWeight δ r
  have hu : 0 < u := by
    dsimp [u, inverseDegree]
    linarith
  have hua : u < a := by
    dsimp [u, a, inverseDegree, inverseWeight]
    linarith
  have ha : a < (1 : ℝ) / 2 := by
    dsimp [a, inverseWeight]
    linarith
  have ha0 : 0 < a := lt_trans hu hua
  have haone : 0 < 1 - a := by linarith
  have huone : 0 < 1 - u := by linarith
  have hvarianceu : 4 * u * (1 - u) = r ^ 2 := by
    dsimp [u, inverseDegree]
    nlinarith only [hdegreesquare]
  have hvariancea :
      4 * a * (1 - a) =
        r ^ 2 + 2 * δ * r + 2 * δ := by
    dsimp [a, inverseWeight]
    nlinarith only [hweightsquare]
  have hdistancevariance : 2 * δ < 4 * a * (1 - a) := by
    rw [hvariancea]
    nlinarith only [mul_pos hδ hr, sq_nonneg r]
  have hvarianceweight : 4 * a * (1 - a) < 4 * a := by
    nlinarith only [mul_pos ha0 ha0]
  have hweightdistance : δ / 2 < a := by
    nlinarith only [hdistancevariance, hvarianceweight]
  have husquare := Real.sq_sqrt (mul_pos hu huone).le
  have hrootsquare :
      (2 * Real.sqrt (u * (1 - u))) ^ 2 = r ^ 2 := by
    nlinarith only [husquare, hvarianceu]
  have huradical :
      2 * Real.sqrt (u * (1 - u)) = r := by
    calc
      2 * Real.sqrt (u * (1 - u)) =
          Real.sqrt ((2 * Real.sqrt (u * (1 - u))) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
      _ = Real.sqrt (r ^ 2) := by rw [hrootsquare]
      _ = r := Real.sqrt_sq hr.le
  have hplus : 1 + r ≠ 0 := hrplus.ne'
  have hfraction :
      (a * (1 - a) - u * (1 - u)) /
        (a * (1 - a) * (1 + r)) =
        δ / (2 * a * (1 - a)) := by
    field_simp [ha0.ne', haone.ne', hplus] ;
      nlinarith only [hvariancea, hvarianceu]
  have hspectral :
      1 - MetricCodes.Johnson.spectralLimit a 0 0 u =
        (a * (1 - a) - u * (1 - u)) /
          (a * (1 - a) * (1 + r)) := by
    simpa only [huradical] using
      MetricCodes.Johnson.spectralLimit_zero_fibre_boundary hu hua ha
  have hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a := by
    unfold MetricCodes.Johnson.asymptoticThreshold
    linarith only [hspectral, hfraction]
  have hobjective :
      MetricCodes.Johnson.mrrwObjective δ r =
        MetricCodes.Johnson.shellRate a 0 0 u := by
    simpa only [huradical] using
      MetricCodes.Johnson.mrrwObjective_zero_fibre_boundary
        hu hua ha hboundary
  exact ⟨a, u, hu, hua, ha, hweightdistance,
    hboundary, hobjective⟩

theorem exists_zero_fibre_boundary_of_interior_minimizer
    {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2)
    (hstrict :
      MetricCodes.Johnson.mrrwRate δ <
        MetricCodes.Hamming.classicalRate δ) :
    ∃ a u : ℝ,
      0 < u ∧ u < a ∧ a < (1 : ℝ) / 2 ∧
      δ / 2 < a ∧
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a ∧
      MetricCodes.Johnson.mrrwRate δ =
        MetricCodes.Johnson.shellRate a 0 0 u := by
  obtain ⟨r, hr, hupper, _hmin, hrate⟩ :=
    exists_positive_mrrw_minimizer hδ hhalf
  have hrstrict : r < 1 - 2 * δ := by
    rcases lt_or_eq_of_le hupper with hlt | heq
    · exact hlt
    · exfalso
      have hendpoint :
          MetricCodes.Johnson.mrrwRate δ =
            MetricCodes.Hamming.classicalRate δ := by
        calc
          MetricCodes.Johnson.mrrwRate δ =
              MetricCodes.Johnson.mrrwObjective δ r := hrate
          _ = MetricCodes.Johnson.mrrwObjective δ (1 - 2 * δ) := by
            rw [heq]
          _ = MetricCodes.Hamming.classicalRate δ :=
            MetricCodes.Johnson.mrrwObjective_endpoint hδ hhalf
      exact (ne_of_lt hstrict) hendpoint
  obtain ⟨a, u, hu, hua, ha, hweightdistance,
      hboundary, hobjective⟩ :=
    inverse_zero_fibre_boundary hδ hhalf hr hrstrict
  exact ⟨a, u, hu, hua, ha, hweightdistance,
    hboundary, hrate.trans hobjective⟩

end MetricCodes.MRRW

end

end

section

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped Topology

namespace MetricCodes.MRRW

def interiorSlope (a u : ℝ) : ℝ :=
  (Real.sqrt (u * (1 - u)) * (1 - 2 * a))⁻¹

def interiorWeight (a u e : ℝ) : ℝ :=
  a - interiorSlope a u * e

def interiorSupport (a u e : ℝ) : ℝ :=
  interiorWeight a u e * e

def interiorComplement (a u e : ℝ) : ℝ :=
  (1 - interiorWeight a u e) * e

@[simp] theorem interiorWeight_zero (a u : ℝ) :
    interiorWeight a u 0 = a := by
  simp [interiorWeight]

@[simp] theorem interiorSupport_zero (a u : ℝ) :
    interiorSupport a u 0 = 0 := by
  simp [interiorSupport]

@[simp] theorem interiorComplement_zero (a u : ℝ) :
    interiorComplement a u 0 = 0 := by
  simp [interiorComplement]

theorem interiorSupport_add_complement (a u e : ℝ) :
    interiorSupport a u e + interiorComplement a u e = e := by
  unfold interiorSupport interiorComplement
  ring

theorem rankPenalty_interior {a u e : ℝ}
    (hweight : 0 < interiorWeight a u e)
    (hweight' : interiorWeight a u e < 1) :
    MetricCodes.Johnson.rankPenalty
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) =
      MetricCodes.binaryEntropy e := by
  have hsupport :
      interiorSupport a u e / interiorWeight a u e = e := by
    unfold interiorSupport
    exact mul_div_cancel_left₀ e hweight.ne'
  have hcomplement :
      interiorComplement a u e / (1 - interiorWeight a u e) = e := by
    unfold interiorComplement
    exact mul_div_cancel_left₀ e (sub_pos.mpr hweight').ne'
  unfold MetricCodes.Johnson.rankPenalty
  rw [hsupport, hcomplement]
  ring

theorem tendsto_interiorWeight_zero (a u : ℝ) :
    Tendsto (interiorWeight a u) (𝓝[>] 0) (𝓝 a) := by
  have hcontinuous : Continuous (interiorWeight a u) := by
    unfold interiorWeight
    fun_prop
  simpa using hcontinuous.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)

theorem eventually_binaryEntropy_inward_improvement
    {a : ℝ} (ha : 0 < a) (ha' : a < 1) (C : ℝ) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e) <
        MetricCodes.binaryEntropy e := by
  let f : ℝ → ℝ := fun e =>
    MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e)
  have hinner :
      DifferentiableAt ℝ (fun e : ℝ => a - C * e) 0 := by
    fun_prop
  have houter : DifferentiableAt ℝ MetricCodes.binaryEntropy a :=
    MetricCodes.Hamming.differentiableAt_binaryEntropy ha ha'
  have houter0 :
      DifferentiableAt ℝ MetricCodes.binaryEntropy (a - C * (0 : ℝ)) := by
    simpa using houter
  have hf : DifferentiableAt ℝ f 0 := by
    dsimp [f]
    exact (houter0.comp 0 hinner).const_sub (MetricCodes.binaryEntropy a)
  let M : ℝ := deriv f 0 + 1
  have hM : deriv f 0 < M := by
    dsimp [M]
    linarith
  have hslope := hf.hasDerivAt.tendsto_slope_zero_right
  have hupper :
      ∀ᶠ e : ℝ in 𝓝[>] 0,
        e⁻¹ *
          (MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e)) < M := by
    have h := hslope.eventually (gt_mem_nhds hM)
    filter_upwards [h] with e he
    simpa [f, smul_eq_mul] using he
  have hloglim :
      Tendsto (fun e : ℝ => -Real.logb 2 e) (𝓝[>] 0) atTop := by
    simpa [Function.comp_def] using
      tendsto_neg_atBot_atTop.comp
        (Real.tendsto_logb_nhdsGT_zero (by norm_num : (1 : ℝ) < 2))
  have hlog : ∀ᶠ e : ℝ in 𝓝[>] 0, M < -Real.logb 2 e :=
    hloglim.eventually (eventually_gt_atTop M)
  have hsmall : ∀ᶠ e : ℝ in 𝓝[>] 0, e < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hupper, hlog, hsmall, self_mem_nhdsWithin]
    with e hbound hlog' heone (he : 0 < e)
  have houter_bound :
      MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e) <
        e * M := by
    calc
      MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e) =
          e * (e⁻¹ *
            (MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e))) := by
            field_simp [he.ne']
      _ < e * M := mul_lt_mul_of_pos_left hbound he
  have hsingular : e * M < e * (-Real.logb 2 e) :=
    mul_lt_mul_of_pos_left hlog' he
  have hentropy :=
    MetricCodes.Hamming.neg_mul_logb_le_binaryEntropy he.le heone.le
  linarith

theorem eventually_shellRate_interior_improvement
    {a u : ℝ} (ha : 0 < a) (ha' : a < (1 : ℝ) / 2) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      MetricCodes.Johnson.shellRate
          (interiorWeight a u e)
          (interiorSupport a u e)
          (interiorComplement a u e) u <
        MetricCodes.Johnson.shellRate a 0 0 u := by
  have hentropy := eventually_binaryEntropy_inward_improvement
    ha (ha'.trans (by norm_num)) (interiorSlope a u)
  have hweight := tendsto_interiorWeight_zero a u
  have hpositive :
      ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < interiorWeight a u e :=
    hweight.eventually (lt_mem_nhds ha)
  have hless :
      ∀ᶠ e : ℝ in 𝓝[>] 0, interiorWeight a u e < 1 :=
    hweight.eventually
      (gt_mem_nhds (ha'.trans (by norm_num : (1 : ℝ) / 2 < 1)))
  filter_upwards [hentropy, hpositive, hless]
    with e he hpos hlt
  rw [MetricCodes.Johnson.shellRate, rankPenalty_interior hpos hlt,
    MetricCodes.Johnson.shellRate_zero_fibre]
  change
    1 - MetricCodes.binaryEntropy (a - interiorSlope a u * e) +
        MetricCodes.binaryEntropy u - MetricCodes.binaryEntropy e <
      1 - MetricCodes.binaryEntropy a + MetricCodes.binaryEntropy u
  linarith

def interiorSpectralMargin (δ a u e : ℝ) : ℝ :=
  MetricCodes.Johnson.spectralLimit
      (interiorWeight a u e)
      (interiorSupport a u e)
      (interiorComplement a u e) u -
    MetricCodes.Johnson.asymptoticThreshold δ (interiorWeight a u e)

theorem interiorSpectralMargin_zero {δ a u : ℝ}
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    interiorSpectralMargin δ a u 0 = 0 := by
  simp [interiorSpectralMargin, hboundary]

theorem interior_boundary_delta_relation {δ a u : ℝ}
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    δ * (1 + 2 * Real.sqrt (u * (1 - u))) =
      2 * (a * (1 - a) - u * (1 - u)) := by
  have huone : 0 < 1 - u := by linarith
  have hsquare := Real.sq_sqrt (mul_pos hu huone).le
  have hvariance := MetricCodes.Johnson.zero_fibre_boundary_variance
    hu hua ha hboundary
  nlinarith

theorem interior_boundary_weight_gt_distance {δ a u : ℝ}
    (hδ : 0 < δ)
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    δ / 2 < a := by
  have ha0 : 0 < a := lt_trans hu hua
  have huone : 0 < 1 - u := by linarith
  have hs : 0 < Real.sqrt (u * (1 - u)) :=
    Real.sqrt_pos.mpr (mul_pos hu huone)
  have hvariance := MetricCodes.Johnson.zero_fibre_boundary_variance
    hu hua ha hboundary
  have hcross : 0 < δ * (2 * Real.sqrt (u * (1 - u))) := by
    positivity
  nlinarith [sq_nonneg (2 * Real.sqrt (u * (1 - u))),
    sq_pos_of_pos ha0]

theorem spectralLimit_interior_eq (a u e : ℝ) :
    MetricCodes.Johnson.spectralLimit
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u =
      let z := MetricCodes.Johnson.centeredDegree u
      let m := MetricCodes.Johnson.centeredWeight (interiorWeight a u e)
      let t := 1 - 2 * e
      (m * (t ^ 2 - z ^ 2)) ^ 2 /
          (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
        ((z ^ 2 - (m * t) ^ 2) * (t ^ 2 - z ^ 2)) /
          (z ^ 2 * (1 - m ^ 2) * Real.sqrt (1 - z ^ 2)) := by
  dsimp [MetricCodes.Johnson.spectralLimit,
    MetricCodes.Johnson.centeredDegree, MetricCodes.Johnson.centeredWeight,
    MetricCodes.Johnson.centeredSigma, MetricCodes.Johnson.centeredEta,
    interiorSupport, interiorComplement]
  ring

theorem eventually_interior_parameters
    {δ a u : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2)
    (hδa : δ / 2 < a)
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      MetricCodes.Johnson.AsymptoticParameters δ
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u := by
  have hweight := tendsto_interiorWeight_zero a u
  have hweight_distance :
      ∀ᶠ e : ℝ in 𝓝[>] 0, δ / 2 < interiorWeight a u e :=
    hweight.eventually (lt_mem_nhds hδa)
  have hweight_half :
      ∀ᶠ e : ℝ in 𝓝[>] 0, interiorWeight a u e < (1 : ℝ) / 2 :=
    hweight.eventually (gt_mem_nhds ha)
  have hweight_degree :
      ∀ᶠ e : ℝ in 𝓝[>] 0, u < interiorWeight a u e :=
    hweight.eventually (lt_mem_nhds hua)
  have hehalf : ∀ᶠ e : ℝ in 𝓝[>] 0, e < (1 : ℝ) / 2 :=
    nhdsWithin_le_nhds
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hedegree : ∀ᶠ e : ℝ in 𝓝[>] 0, e < u :=
    nhdsWithin_le_nhds (gt_mem_nhds hu)
  have hleftcontinuous : Continuous
      (fun e : ℝ =>
        interiorWeight a u e - interiorSupport a u e +
          interiorComplement a u e) := by
    unfold interiorSupport interiorComplement interiorWeight
    fun_prop
  have hleftlimit :
      Tendsto
        (fun e : ℝ =>
          interiorWeight a u e - interiorSupport a u e +
            interiorComplement a u e)
        (𝓝[>] 0) (𝓝 a) := by
    simpa using hleftcontinuous.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hleft : ∀ᶠ e : ℝ in 𝓝[>] 0,
      u < interiorWeight a u e - interiorSupport a u e +
        interiorComplement a u e :=
    hleftlimit.eventually (lt_mem_nhds hua)
  have hrightcontinuous : Continuous
      (fun e : ℝ =>
        1 - interiorWeight a u e + interiorSupport a u e -
          interiorComplement a u e) := by
    unfold interiorSupport interiorComplement interiorWeight
    fun_prop
  have hrightlimit :
      Tendsto
        (fun e : ℝ =>
          1 - interiorWeight a u e + interiorSupport a u e -
            interiorComplement a u e)
        (𝓝[>] 0) (𝓝 (1 - a)) := by
    simpa using hrightcontinuous.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have huright : u < 1 - a := by linarith
  have hright : ∀ᶠ e : ℝ in 𝓝[>] 0,
      u < 1 - interiorWeight a u e + interiorSupport a u e -
        interiorComplement a u e :=
    hrightlimit.eventually (lt_mem_nhds huright)
  filter_upwards [hweight_distance, hweight_half, hweight_degree,
    hehalf, hedegree, hleft, hright, self_mem_nhdsWithin]
    with e hwd hwh hwu heh heu hel her (he : 0 < e)
  have hwpos : 0 < interiorWeight a u e := by
    nlinarith
  have hwcomplement : 0 < 1 - interiorWeight a u e := by
    linarith
  refine {
    distance_pos := hδ
    distance_lt_half := hδ'
    weight_gt_distance := hwd
    weight_lt_half := hwh
    support_nonneg := ?_
    support_lt_half := ?_
    complement_nonneg := ?_
    complement_lt_half := ?_
    first_lt_degree := ?_
    degree_lt_weight := hwu
    degree_lt_left := hel
    degree_lt_right := her
  }
  · unfold interiorSupport
    exact mul_nonneg hwpos.le he.le
  · unfold interiorSupport
    nlinarith [mul_lt_mul_of_pos_left heh hwpos]
  · unfold interiorComplement
    exact mul_nonneg hwcomplement.le he.le
  · unfold interiorComplement
    nlinarith [mul_lt_mul_of_pos_left heh hwcomplement]
  · rw [interiorSupport_add_complement]
    exact heu

theorem hasDerivAt_interiorSpectralMargin
    {δ a u : ℝ}
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    HasDerivAt (interiorSpectralMargin δ a u)
      ((1 - 2 * (a * (1 - a))) *
          (1 - 2 * Real.sqrt (u * (1 - u))) /
        (a * (1 - a) * Real.sqrt (u * (1 - u)) *
          (1 + 2 * Real.sqrt (u * (1 - u))))) 0 := by
  have ha0 : 0 < a := lt_trans hu hua
  have ha1 : 0 < 1 - a := by linarith
  have hu1 : 0 < 1 - u := by linarith
  have hz0 : 0 < 1 - 2 * u := by linarith
  have hm0 : 0 < 1 - 2 * a := by linarith
  have hrad : 0 < 1 - (1 - 2 * u) ^ 2 := by
    nlinarith [mul_pos hu hu1]
  have hmrad : 0 < 1 - (1 - 2 * a) ^ 2 := by
    nlinarith [mul_pos ha0 ha1]
  have hs : 0 < Real.sqrt (u * (1 - u)) :=
    Real.sqrt_pos.mpr (mul_pos hu hu1)
  have hsquare := Real.sq_sqrt (mul_pos hu hu1).le
  have hroot :
      Real.sqrt (1 - (1 - 2 * u) ^ 2) =
        2 * Real.sqrt (u * (1 - u)) := by
    simpa [MetricCodes.Johnson.centeredDegree] using
      MetricCodes.Johnson.sqrt_one_sub_centeredDegree_sq hu (lt_trans hua ha)
  have hdelta :=
    interior_boundary_delta_relation hu hua ha hboundary
  let c : ℝ := interiorSlope a u
  let A : ℝ → ℝ := fun e => a - c * e
  let m : ℝ → ℝ := fun e => 1 - 2 * A e
  let t : ℝ → ℝ := fun e => 1 - 2 * e
  let z : ℝ := 1 - 2 * u
  let q : ℝ := Real.sqrt (1 - z ^ 2)
  let p : ℝ → ℝ := fun e => t e ^ 2 - z ^ 2
  let Q : ℝ → ℝ := fun e => 1 - m e ^ 2
  have hA : HasDerivAt A (-c) 0 := by
    change
      HasDerivAt
        ((fun _ : ℝ => a) - (fun e : ℝ => c * e)) (-c) 0
    simpa using
      (hasDerivAt_const (x := (0 : ℝ)) a).sub
        ((hasDerivAt_id (0 : ℝ)).const_mul c)
  have hm : HasDerivAt m (2 * c) 0 := by
    change
      HasDerivAt
        ((fun _ : ℝ => 1) -
          (fun e : ℝ => 2 * (a - c * e)))
        (2 * c) 0
    simpa using
      (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub
        (hA.const_mul 2)
  have ht : HasDerivAt t (-2) 0 := by
    change
      HasDerivAt
        ((fun _ : ℝ => 1) - (fun e : ℝ => 2 * e))
        (-2) 0
    simpa using
      (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub
        ((hasDerivAt_id (0 : ℝ)).const_mul 2)
  have hp : HasDerivAt p (-4) 0 := by
    change
      HasDerivAt
        (((fun e : ℝ => 1 - 2 * e) ^ 2) -
          (fun _ : ℝ => z ^ 2))
        (-4) 0
    exact
      ((ht.pow 2).sub
        (hasDerivAt_const (x := (0 : ℝ)) (z ^ 2))).congr_deriv
        (by norm_num)
  have hQ : HasDerivAt Q (-4 * (1 - 2 * a) * c) 0 := by
    change
      HasDerivAt
        ((fun _ : ℝ => 1) -
          ((fun e : ℝ => 1 - 2 * (a - c * e)) ^ 2))
        (-4 * (1 - 2 * a) * c) 0
    exact
      ((hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub
        (hm.pow 2)).congr_deriv (by dsimp [m, A]; ring)
  have hden1 : z ^ 2 * Q 0 * (1 - z ^ 2) ≠ 0 := by
    simpa [z, Q, m, A] using
      mul_ne_zero
        (mul_ne_zero (pow_ne_zero 2 hz0.ne') hmrad.ne')
        hrad.ne'
  have hden2 : z ^ 2 * Q 0 * q ≠ 0 := by
    have hroot_ne : Real.sqrt (1 - (1 - 2 * u) ^ 2) ≠ 0 :=
      (Real.sqrt_pos.mpr hrad).ne'
    simpa [z, Q, m, A, q] using
      mul_ne_zero
        (mul_ne_zero (pow_ne_zero 2 hz0.ne') hmrad.ne')
        hroot_ne
  have hden3 : 2 * A 0 * (1 - A 0) ≠ 0 := by
    simpa [A] using
      mul_ne_zero
        (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) ha0.ne')
        ha1.ne'
  have hterm1 :=
    ((hm.mul hp).pow 2).div
      (((hasDerivAt_const (x := (0 : ℝ)) (z ^ 2)).mul hQ).mul
        (hasDerivAt_const (x := (0 : ℝ)) (1 - z ^ 2))) hden1
  have hterm2 :=
    (((hasDerivAt_const (x := (0 : ℝ)) (z ^ 2)).sub
        ((hm.mul ht).pow 2)).mul hp).div
      (((hasDerivAt_const (x := (0 : ℝ)) (z ^ 2)).mul hQ).mul
        (hasDerivAt_const (x := (0 : ℝ)) q)) hden2
  have hthreshold :=
    (hasDerivAt_const (x := (0 : ℝ)) δ).div
      ((hA.const_mul 2).mul
        ((hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub hA))
      hden3
  have hraw :=
    ((hterm1.add hterm2).sub
      (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ))).add hthreshold
  have hfun :
      (fun e : ℝ => interiorSpectralMargin δ a u e) =
        (fun e : ℝ =>
          (m e * p e) ^ 2 /
              (z ^ 2 * Q e * (1 - z ^ 2)) +
            ((z ^ 2 - (m e * t e) ^ 2) * p e) /
              (z ^ 2 * Q e * q) - 1 +
            δ / (2 * A e * (1 - A e))) := by
    funext e
    unfold interiorSpectralMargin
    rw [spectralLimit_interior_eq]
    dsimp [MetricCodes.Johnson.asymptoticThreshold,
      MetricCodes.Johnson.centeredDegree, MetricCodes.Johnson.centeredWeight,
      A, m, t, z, q, p, Q, c, interiorWeight]
    ring
  change HasDerivAt (fun e : ℝ => interiorSpectralMargin δ a u e) _ 0
  rw [hfun]
  refine hraw.congr_deriv ?_
  simp [p, Q, m, t, A, z, q, c, interiorSlope]
  rw [hroot]
  have hdelta_div :
      δ =
        2 * (a * (1 - a) - u * (1 - u)) /
          (1 + 2 * Real.sqrt (u * (1 - u))) := by
    apply (eq_div_iff (by positivity)).2
    exact hdelta
  rw [hdelta_div]
  field_simp [ha0.ne', ha1.ne', hu.ne', hu1.ne',
    hz0.ne', hm0.ne', hs.ne', hrad.ne', hmrad.ne']
  ring_nf at hsquare ⊢
  linear_combination
    ((-128 * a ^ 3 * (a - 1) ^ 3 * (2 * a - 1) ^ 3 *
        Real.sqrt (u - u ^ 2)) +
      (64 * a ^ 2 * u * (a - 1) ^ 2 * (2 * a - 1) * (u - 1))) *
      hsquare

theorem interiorSpectralMargin_derivative_pos
    {a u : ℝ}
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2) :
    0 <
      (1 - 2 * (a * (1 - a))) *
          (1 - 2 * Real.sqrt (u * (1 - u))) /
        (a * (1 - a) * Real.sqrt (u * (1 - u)) *
          (1 + 2 * Real.sqrt (u * (1 - u)))) := by
  have ha0 : 0 < a := lt_trans hu hua
  have ha1 : 0 < 1 - a := by linarith
  have hu1 : 0 < 1 - u := by linarith
  have hs : 0 < Real.sqrt (u * (1 - u)) :=
    Real.sqrt_pos.mpr (mul_pos hu hu1)
  have hvariance : u * (1 - u) < (1 : ℝ) / 4 := by
    nlinarith [sq_pos_of_pos (by linarith : 0 < 1 - 2 * u)]
  have hshalf : Real.sqrt (u * (1 - u)) < (1 : ℝ) / 2 := by
    exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1 / 2)).mpr
      (by nlinarith)
  have hweight : 0 < 1 - 2 * (a * (1 - a)) := by
    nlinarith [sq_nonneg (a - (1 : ℝ) / 2)]
  exact div_pos
    (mul_pos hweight (by linarith))
    (by positivity)

theorem eventually_interiorSpectralMargin_pos
    {δ a u : ℝ}
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      0 < interiorSpectralMargin δ a u e := by
  have hderiv :=
    hasDerivAt_interiorSpectralMargin hu hua ha hboundary
  have hpositive := interiorSpectralMargin_derivative_pos hu hua ha
  have hslope := hderiv.tendsto_slope_zero_right
  have heventual := hslope.eventually (lt_mem_nhds hpositive)
  filter_upwards [heventual, self_mem_nhdsWithin]
    with e he (hepos : 0 < e)
  have hzero := interiorSpectralMargin_zero hboundary
  have hslopepos : 0 < e⁻¹ * interiorSpectralMargin δ a u e := by
    simpa [hzero, smul_eq_mul] using he
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hepos)).mp hslopepos

theorem eventually_interior_feasible
    {δ a u : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2)
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      MetricCodes.Johnson.Feasible δ
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u := by
  have hweight := interior_boundary_weight_gt_distance
    hδ hu hua ha hboundary
  have hparameters := eventually_interior_parameters
    hδ hδ' hweight hu hua ha
  have hspectral := eventually_interiorSpectralMargin_pos
    hu hua ha hboundary
  filter_upwards [hparameters, hspectral] with e he hs
  refine ⟨he, ?_⟩
  change
    MetricCodes.Johnson.asymptoticThreshold δ (interiorWeight a u e) <
      MetricCodes.Johnson.spectralLimit
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u
  exact sub_pos.mp hs

theorem interior_shell_improvement
    {δ a u : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2)
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    ∃ A b g : ℝ,
      0 < b ∧ 0 < g ∧
      MetricCodes.Johnson.Feasible δ A b g u ∧
      MetricCodes.Johnson.shellRate A b g u <
        MetricCodes.Johnson.shellRate a 0 0 u := by
  have hfeasible := eventually_interior_feasible
    hδ hδ' hu hua ha hboundary
  have himprovement := eventually_shellRate_interior_improvement
    (u := u) (lt_trans hu hua) ha
  have hweight := tendsto_interiorWeight_zero a u
  have hpositive :
      ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < interiorWeight a u e :=
    hweight.eventually (lt_mem_nhds (lt_trans hu hua))
  have hcomplement :
      ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < 1 - interiorWeight a u e := by
    filter_upwards
      [hweight.eventually
        (gt_mem_nhds (show a < (1 : ℝ) by linarith))]
      with e he
    linarith
  have hall : ∀ᶠ e : ℝ in 𝓝[>] 0,
      0 < interiorSupport a u e ∧
      0 < interiorComplement a u e ∧
      MetricCodes.Johnson.Feasible δ
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u ∧
      MetricCodes.Johnson.shellRate
          (interiorWeight a u e)
          (interiorSupport a u e)
          (interiorComplement a u e) u <
        MetricCodes.Johnson.shellRate a 0 0 u := by
    filter_upwards [hfeasible, himprovement, hpositive, hcomplement,
      self_mem_nhdsWithin] with e hf hi hw hc (he : 0 < e)
    refine ⟨?_, ?_, hf, hi⟩
    · unfold interiorSupport
      exact mul_pos hw he
    · unfold interiorComplement
      exact mul_pos hc he
  obtain ⟨e, he⟩ := hall.exists
  exact ⟨interiorWeight a u e,
    interiorSupport a u e, interiorComplement a u e, he⟩

theorem variationalRate_lt_mrrw_of_interior
    {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2)
    (hstrict :
      MetricCodes.Johnson.mrrwRate δ < MetricCodes.Hamming.classicalRate δ) :
    MetricCodes.Johnson.variationalRate δ <
      MetricCodes.Johnson.mrrwRate δ := by
  obtain ⟨a, u, hu, hua, ha, _hweight, hboundary, hrate⟩ :=
    exists_zero_fibre_boundary_of_interior_minimizer
      hδ hhalf hstrict
  obtain ⟨A, b, g, _hb, _hg, hfeasible, himprovement⟩ :=
    interior_shell_improvement hδ hhalf hu hua ha hboundary
  calc
    MetricCodes.Johnson.variationalRate δ ≤
        MetricCodes.Johnson.shellRate A b g u :=
      MetricCodes.Johnson.variationalRate_le_of_feasible hfeasible
    _ < MetricCodes.Johnson.shellRate a 0 0 u := himprovement
    _ = MetricCodes.Johnson.mrrwRate δ := hrate.symm

theorem strict_mrrw2
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    MetricCodes.Johnson.combinedVariationalRate δ <
      MetricCodes.Johnson.mrrwRate δ := by
  rcases MetricCodes.Johnson.mrrw_endpoint_dichotomy hδ hhalf with
    hstrict | hendpoint
  · exact
      (MetricCodes.Johnson.combinedVariationalRate_le_shell δ).trans_lt
        (variationalRate_lt_mrrw_of_interior hδ hhalf hstrict)
  · exact MetricCodes.Johnson.combinedVariationalRate_lt_mrrw_of_endpoint
      hδ hhalf hendpoint

end MetricCodes.MRRW

end

end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators InnerProductSpace Matrix

namespace MetricCodes.Johnson

def johnsonWindowBasis {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (Q : ShellWindowIndex n p q L) :
    MetricCodes.Boolean.Function n :=
  MetricCodes.Boolean.harmonicBasisFunction n
    (p + q + Q.1.val) (h.window_degree_half Q.1) Q.2

theorem johnsonWindowBasis_isHarmonic {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (Q : ShellWindowIndex n p q L) :
    MetricCodes.Boolean.IsHarmonic (p + q + Q.1.val)
      (johnsonWindowBasis h Q) := by
  exact MetricCodes.Boolean.harmonicBasisFunction_isHarmonic n
    (p + q + Q.1.val) (h.window_degree_half Q.1) Q.2

def johnsonHarmonicCoordinates {n j : ℕ}
    (hj : 2 * j ≤ n)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) :
    Fin (MetricCodes.booleanHarmonicDimension n j) → ℝ :=
  fun a =>
    (MetricCodes.Boolean.harmonicOrthonormalBasis n j hj).repr
      (globalHarmonicVector f hf) a

theorem johnsonHarmonicCoordinates_pairing {n j : ℕ}
    (hj : 2 * j ≤ n)
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hg : MetricCodes.Boolean.IsHarmonic j g) :
    (∑ a : Fin (MetricCodes.booleanHarmonicDimension n j),
      johnsonHarmonicCoordinates hj f hf a *
        johnsonHarmonicCoordinates hj g hg a) =
      MetricCodes.Boolean.dot f g := by
  let e := MetricCodes.Boolean.harmonicOrthonormalBasis n j hj
  let A := globalHarmonicVector f hf
  let B := globalHarmonicVector g hg
  calc
    (∑ a : Fin (MetricCodes.booleanHarmonicDimension n j),
      johnsonHarmonicCoordinates hj f hf a *
        johnsonHarmonicCoordinates hj g hg a) =
      @inner ℝ
        (EuclideanSpace ℝ
          (Fin (MetricCodes.booleanHarmonicDimension n j))) _
          (e.repr A) (e.repr B) := by
            change
              (∑ a : Fin (MetricCodes.hammingFibreDimension n j),
                e.repr A a * e.repr B a) =
                @inner ℝ
                  (EuclideanSpace ℝ
                    (Fin (MetricCodes.hammingFibreDimension n j))) _
                    (e.repr A) (e.repr B)
            rw [PiLp.inner_apply]
            simp [mul_comm]
    _ = @inner ℝ
        (MetricCodes.Boolean.harmonicEuclideanLayer n j) _ A B :=
      e.repr.inner_map_map A B
    _ = MetricCodes.Boolean.dot f g :=
      globalHarmonicVector_inner f g hf hg

theorem johnsonWindowBasis_dot {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (source : Index p q L)
    (a b : Fin (MetricCodes.booleanHarmonicDimension
      n (p + q + source.val))) :
    MetricCodes.Boolean.dot
        (johnsonWindowBasis h ⟨source, a⟩)
        (johnsonWindowBasis h ⟨source, b⟩) =
      if a = b then 1 else 0 := by
  exact MetricCodes.Boolean.harmonicBasisFunction_dot n
    (p + q + source.val) (h.window_degree_half source) a b

theorem globalHarmonicVector_harmonicBasisFunction {n j : ℕ}
    (hj : 2 * j ≤ n)
    (a : Fin (MetricCodes.booleanHarmonicDimension n j)) :
    globalHarmonicVector
        (MetricCodes.Boolean.harmonicBasisFunction n j hj a)
        (MetricCodes.Boolean.harmonicBasisFunction_isHarmonic n j hj a) =
      MetricCodes.Boolean.harmonicOrthonormalBasis n j hj a := by
  apply Subtype.ext
  change
    WithLp.toLp 2
        (MetricCodes.Boolean.layerRestrict j
          (MetricCodes.Boolean.layerExtend
            (WithLp.ofLp
              ((MetricCodes.Boolean.harmonicOrthonormalBasis
                n j hj a).val)))) =
      (MetricCodes.Boolean.harmonicOrthonormalBasis n j hj a).val
  rw [MetricCodes.Boolean.layerRestrict_layerExtend]

theorem johnsonHarmonicCoordinates_eq_basis_dot {n j : ℕ}
    (hj : 2 * j ≤ n)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (a : Fin (MetricCodes.booleanHarmonicDimension n j)) :
    johnsonHarmonicCoordinates hj f hf a =
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.harmonicBasisFunction n j hj a) f := by
  unfold johnsonHarmonicCoordinates
  rw [OrthonormalBasis.repr_apply_apply]
  rw [← globalHarmonicVector_harmonicBasisFunction hj a]
  exact globalHarmonicVector_inner
    (MetricCodes.Boolean.harmonicBasisFunction n j hj a) f
    (MetricCodes.Boolean.harmonicBasisFunction_isHarmonic n j hj a) hf

theorem johnsonWindowBasis_dot_coupled
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (x : JohnsonSphere n w)
    (source : Index p q L)
    (a : HarmonicFibreIndex n w p q)
    (b : Fin (MetricCodes.booleanHarmonicDimension
      n (p + q + source.val))) :
    MetricCodes.Boolean.dot (johnsonWindowBasis h ⟨source, b⟩)
        (coupledHarmonic x h.support_half h.complement_half
          a source.val) =
      coupledDegreeCoordinates h x source a b := by
  symm
  exact johnsonHarmonicCoordinates_eq_basis_dot
    (h.window_degree_half source)
    (coupledHarmonic x h.support_half h.complement_half
      a source.val)
    (coupledHarmonic_isHarmonic x h.support_half h.complement_half
      (h.supportResidual_bound source)
      (h.complementResidual_bound source) a) b

def johnsonWindowChannelMatrix {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L) (lam : ℝ) :
    Matrix (Fin n × ShellWindowIndex n p q L)
      (ShellWindowIndex n p q L) ℝ :=
  fun T Q =>
    johnsonAdjacentBlockCoefficient n w p q L v lam T.2.1 Q.1 *
      johnsonHarmonicCoordinates (h.window_degree_half T.2.1)
        (johnsonAdjacentChannel n w p q L T.2.1 Q.1
          (johnsonWindowBasis h Q) T.1)
        (johnsonAdjacentChannel_isHarmonic h hstrict T.2.1 Q.1
          (johnsonWindowBasis h Q)
          (johnsonWindowBasis_isHarmonic h Q) T.1) T.2.2

theorem johnsonWindowChannelMatrix_pairing
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L) (lam : ℝ)
    (Q R : ShellWindowIndex n p q L) :
    (∑ T : Fin n × ShellWindowIndex n p q L,
      johnsonWindowChannelMatrix h hstrict v lam T Q *
        johnsonWindowChannelMatrix h hstrict v lam T R) =
      ∑ target : Index p q L,
        (johnsonAdjacentBlockCoefficient n w p q L v lam target Q.1 *
          johnsonAdjacentBlockCoefficient n w p q L v lam target R.1) *
        MetricCodes.Boolean.coordinateDot
          (johnsonAdjacentChannel n w p q L target Q.1
            (johnsonWindowBasis h Q))
          (johnsonAdjacentChannel n w p q L target R.1
            (johnsonWindowBasis h R)) := by
  classical
  unfold johnsonWindowChannelMatrix
  rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro target _
  calc
    (∑ b : Fin (MetricCodes.booleanHarmonicDimension
        n (p + q + target.val)),
      ∑ a : Fin n,
        (johnsonAdjacentBlockCoefficient n w p q L v lam target Q.1 *
          johnsonHarmonicCoordinates (h.window_degree_half target)
            (johnsonAdjacentChannel n w p q L target Q.1
              (johnsonWindowBasis h Q) a)
            (johnsonAdjacentChannel_isHarmonic h hstrict target Q.1
              (johnsonWindowBasis h Q)
              (johnsonWindowBasis_isHarmonic h Q) a) b) *
        (johnsonAdjacentBlockCoefficient n w p q L v lam target R.1 *
          johnsonHarmonicCoordinates (h.window_degree_half target)
            (johnsonAdjacentChannel n w p q L target R.1
              (johnsonWindowBasis h R) a)
            (johnsonAdjacentChannel_isHarmonic h hstrict target R.1
              (johnsonWindowBasis h R)
              (johnsonWindowBasis_isHarmonic h R) a) b)) =
      (johnsonAdjacentBlockCoefficient n w p q L v lam target Q.1 *
        johnsonAdjacentBlockCoefficient n w p q L v lam target R.1) *
      (∑ a : Fin n,
        ∑ b : Fin (MetricCodes.booleanHarmonicDimension
          n (p + q + target.val)),
          johnsonHarmonicCoordinates (h.window_degree_half target)
            (johnsonAdjacentChannel n w p q L target Q.1
              (johnsonWindowBasis h Q) a)
            (johnsonAdjacentChannel_isHarmonic h hstrict target Q.1
              (johnsonWindowBasis h Q)
              (johnsonWindowBasis_isHarmonic h Q) a) b *
          johnsonHarmonicCoordinates (h.window_degree_half target)
            (johnsonAdjacentChannel n w p q L target R.1
              (johnsonWindowBasis h R) a)
            (johnsonAdjacentChannel_isHarmonic h hstrict target R.1
              (johnsonWindowBasis h R)
              (johnsonWindowBasis_isHarmonic h R) a) b) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
    _ = _ := by
      unfold MetricCodes.Boolean.coordinateDot
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      exact johnsonHarmonicCoordinates_pairing
        (h.window_degree_half target)
        (johnsonAdjacentChannel n w p q L target Q.1
          (johnsonWindowBasis h Q) a)
        (johnsonAdjacentChannel n w p q L target R.1
          (johnsonWindowBasis h R) a)
        (johnsonAdjacentChannel_isHarmonic h hstrict target Q.1
          (johnsonWindowBasis h Q)
          (johnsonWindowBasis_isHarmonic h Q) a)
        (johnsonAdjacentChannel_isHarmonic h hstrict target R.1
          (johnsonWindowBasis h R)
          (johnsonWindowBasis_isHarmonic h R) a)

theorem johnsonWindowChannelMatrix_transpose_mul
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L)
    (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen : operator n w p q L v = lam • v) :
    (johnsonWindowChannelMatrix h hstrict v lam)ᵀ *
      johnsonWindowChannelMatrix h hstrict v lam = 1 := by
  classical
  ext Q R
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  rw [johnsonWindowChannelMatrix_pairing h hstrict v lam Q R]
  rcases Q with ⟨source, a⟩
  rcases R with ⟨other, b⟩
  by_cases heq : source = other
  · subst other
    calc
      (∑ target : Index p q L,
        (johnsonAdjacentBlockCoefficient n w p q L v lam target source *
          johnsonAdjacentBlockCoefficient n w p q L v lam target source) *
        MetricCodes.Boolean.coordinateDot
          (johnsonAdjacentChannel n w p q L target source
            (johnsonWindowBasis h ⟨source, a⟩))
          (johnsonAdjacentChannel n w p q L target source
            (johnsonWindowBasis h ⟨source, b⟩))) =
        ∑ target : Index p q L,
          johnsonAdjacentBlockCoefficient n w p q L v lam
            target source ^ 2 *
            MetricCodes.Boolean.dot
              (johnsonWindowBasis h ⟨source, a⟩)
              (johnsonWindowBasis h ⟨source, b⟩) := by
          apply Finset.sum_congr rfl
          intro target _
          by_cases hactive : johnsonChannelActive p q L target source
          · rw [johnsonAdjacentChannel_isometry h hstrict
              target source hactive
              (johnsonWindowBasis h ⟨source, a⟩)
              (johnsonWindowBasis h ⟨source, b⟩)
              (johnsonWindowBasis_isHarmonic h ⟨source, a⟩)
              (johnsonWindowBasis_isHarmonic h ⟨source, b⟩)]
            ring
          · have hzero :=
              johnsonSourceChannelCoefficient_eq_zero_of_not_active
                (n := n) (w := w)
                source target hactive
            have hblock :
                johnsonAdjacentBlockCoefficient
                  n w p q L v lam target source = 0 := by
              simp [johnsonAdjacentBlockCoefficient, hzero]
            simp [hblock]
      _ = (∑ target : Index p q L,
            johnsonAdjacentBlockCoefficient n w p q L v lam
              target source ^ 2) *
          MetricCodes.Boolean.dot
            (johnsonWindowBasis h ⟨source, a⟩)
            (johnsonWindowBasis h ⟨source, b⟩) := by
          rw [Finset.sum_mul]
      _ = if (⟨source, a⟩ : ShellWindowIndex n p q L) =
            (⟨source, b⟩ : ShellWindowIndex n p q L)
          then 1 else 0 := by
          rw [johnsonAdjacentBlockCoefficient_sq_sum
            h hstrict v hv lam hlam heigen source,
            one_mul, johnsonWindowBasis_dot]
          by_cases hab : a = b
          · subst b
            simp
          · have hsigma :
                (⟨source, a⟩ : ShellWindowIndex n p q L) ≠
                  (⟨source, b⟩ : ShellWindowIndex n p q L) := by
              intro heq
              cases heq
              exact hab rfl
            simp [hab, hsigma]
  · have hsigma :
        (⟨source, a⟩ : ShellWindowIndex n p q L) ≠
          (⟨other, b⟩ : ShellWindowIndex n p q L) := by
      intro hpair
      exact heq
        (congrArg (fun Z : ShellWindowIndex n p q L => Z.1) hpair)
    rw [if_neg hsigma]
    apply Finset.sum_eq_zero
    intro target _
    rw [johnsonAdjacentChannel_orthogonal h hstrict
      target source other heq
      (johnsonWindowBasis h ⟨source, a⟩)
      (johnsonWindowBasis h ⟨other, b⟩)
      (johnsonWindowBasis_isHarmonic h ⟨source, a⟩)
      (johnsonWindowBasis_isHarmonic h ⟨other, b⟩)]
    ring

def johnsonChannelMatrix {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L) (lam : ℝ) :
    Matrix
      (Fin n × Fin (MetricCodes.johnsonAmbientDimension n (p + q) L))
      (Fin (MetricCodes.johnsonAmbientDimension n (p + q) L)) ℝ :=
  fun T Q =>
    johnsonWindowChannelMatrix h hstrict v lam
      (T.1, (shellWindowIndexEquiv n p q L h.first_le).symm T.2)
      ((shellWindowIndexEquiv n p q L h.first_le).symm Q)

theorem johnsonChannelMatrix_transpose_mul
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L)
    (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen : operator n w p q L v = lam • v) :
    (johnsonChannelMatrix h hstrict v lam)ᵀ *
      johnsonChannelMatrix h hstrict v lam = 1 := by
  classical
  let e := shellWindowIndexEquiv n p q L h.first_le
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  change
    (∑ T : Fin n × Fin (MetricCodes.johnsonAmbientDimension n (p + q) L),
      johnsonWindowChannelMatrix h hstrict v lam
          (T.1, e.symm T.2) (e.symm i) *
        johnsonWindowChannelMatrix h hstrict v lam
          (T.1, e.symm T.2) (e.symm j)) =
      if i = j then 1 else 0
  have hwindow := congrArg
    (fun M : Matrix (ShellWindowIndex n p q L)
        (ShellWindowIndex n p q L) ℝ =>
      M (e.symm i) (e.symm j))
    (johnsonWindowChannelMatrix_transpose_mul
      h hstrict v hv lam hlam heigen)
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.one_apply] at hwindow
  rw [Fintype.sum_prod_type] at hwindow ⊢
  calc
    (∑ a : Fin n,
      ∑ T : Fin (MetricCodes.johnsonAmbientDimension n (p + q) L),
        johnsonWindowChannelMatrix h hstrict v lam
            (a, e.symm T) (e.symm i) *
          johnsonWindowChannelMatrix h hstrict v lam
            (a, e.symm T) (e.symm j)) =
      ∑ a : Fin n,
        ∑ T : ShellWindowIndex n p q L,
          johnsonWindowChannelMatrix h hstrict v lam
              (a, T) (e.symm i) *
            johnsonWindowChannelMatrix h hstrict v lam
              (a, T) (e.symm j) := by
          apply Finset.sum_congr rfl
          intro a _
          exact e.symm.sum_comp
            (fun T : ShellWindowIndex n p q L =>
              johnsonWindowChannelMatrix h hstrict v lam
                  (a, T) (e.symm i) *
                johnsonWindowChannelMatrix h hstrict v lam
                  (a, T) (e.symm j))
    _ = if i = j then 1 else 0 := by
      rw [hwindow]
      simp

theorem johnsonAdjacentChannel_coordinate_axisDot
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (x : JohnsonSphere n w)
    (target source : Index p q L)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + source.val) f)
    (a : HarmonicFibreIndex n w p q) :
    (∑ k : Fin n,
      ∑ b : Fin (MetricCodes.booleanHarmonicDimension
        n (p + q + target.val)),
        geometricAxis x k *
          johnsonHarmonicCoordinates (h.window_degree_half target)
            (johnsonAdjacentChannel n w p q L target source f k)
            (johnsonAdjacentChannel_isHarmonic h hstrict
              target source f hf k) b *
          coupledDegreeCoordinates h x target a b) =
      MetricCodes.Boolean.coordinateDot
        (johnsonAdjacentChannel n w p q L target source f)
        (johnsonAxisTensor x
          (coupledHarmonic x h.support_half h.complement_half
            a target.val)) := by
  classical
  unfold MetricCodes.Boolean.coordinateDot johnsonAxisTensor
  apply Finset.sum_congr rfl
  intro k _
  calc
    (∑ b : Fin (MetricCodes.booleanHarmonicDimension
        n (p + q + target.val)),
      geometricAxis x k *
        johnsonHarmonicCoordinates (h.window_degree_half target)
          (johnsonAdjacentChannel n w p q L target source f k)
          (johnsonAdjacentChannel_isHarmonic h hstrict
            target source f hf k) b *
        coupledDegreeCoordinates h x target a b) =
      geometricAxis x k *
        (∑ b : Fin (MetricCodes.booleanHarmonicDimension
          n (p + q + target.val)),
          johnsonHarmonicCoordinates (h.window_degree_half target)
            (johnsonAdjacentChannel n w p q L target source f k)
            (johnsonAdjacentChannel_isHarmonic h hstrict
              target source f hf k) b *
          johnsonHarmonicCoordinates (h.window_degree_half target)
            (coupledHarmonic x h.support_half h.complement_half
              a target.val)
            (coupledHarmonic_isHarmonic x h.support_half
              h.complement_half (h.supportResidual_bound target)
              (h.complementResidual_bound target) a) b) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        simp only [coupledDegreeCoordinates,
          johnsonHarmonicCoordinates, coupledDegreeVector]
        ring
    _ = geometricAxis x k *
        MetricCodes.Boolean.dot
          (johnsonAdjacentChannel n w p q L target source f k)
          (coupledHarmonic x h.support_half h.complement_half
            a target.val) := by
      rw [johnsonHarmonicCoordinates_pairing
        (h.window_degree_half target)
        (johnsonAdjacentChannel n w p q L target source f k)
        (coupledHarmonic x h.support_half h.complement_half
          a target.val)
        (johnsonAdjacentChannel_isHarmonic h hstrict
          target source f hf k)
        (coupledHarmonic_isHarmonic x h.support_half
          h.complement_half (h.supportResidual_bound target)
          (h.complementResidual_bound target) a)]
    _ = MetricCodes.Boolean.dot
        (johnsonAdjacentChannel n w p q L target source f k)
        ((geometricAxis x k) •
          coupledHarmonic x h.support_half h.complement_half
            a target.val) := by
      rw [MetricCodes.Boolean.dot_smul_right]

theorem johnsonWindowChannelMatrix_transpose_axis_fibre
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L)
    (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen : operator n w p q L v = lam • v)
    (haxis : ∀ (x : JohnsonSphere n w)
      (target source : Index p q L)
      (f : MetricCodes.Boolean.Function n)
      (_ : MetricCodes.Boolean.IsHarmonic (p + q + source.val) f)
      (a : HarmonicFibreIndex n w p q),
        MetricCodes.Boolean.coordinateDot
          (johnsonAdjacentChannel n w p q L target source f)
          (johnsonAxisTensor x
            (coupledHarmonic x h.support_half h.complement_half
              a target.val)) =
          Real.sqrt
              (johnsonSourceChannelCoefficient
                n w p q L source target) *
            MetricCodes.Boolean.dot f
              (coupledHarmonic x h.support_half h.complement_half
                a source.val))
    (x : JohnsonSphere n w) :
    (johnsonWindowChannelMatrix h hstrict v lam)ᵀ *
      MetricCodes.Boolean.matrixAxisLift
        (fun k : Fin n => geometricAxis x k)
        (johnsonWindowFibreMatrix h v x) =
      Real.sqrt lam • johnsonWindowFibreMatrix h v x := by
  classical
  ext Q a
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul]
  change
    (∑ T : Fin n × ShellWindowIndex n p q L,
      (johnsonAdjacentBlockCoefficient n w p q L v lam T.2.1 Q.1 *
        johnsonHarmonicCoordinates (h.window_degree_half T.2.1)
          (johnsonAdjacentChannel n w p q L T.2.1 Q.1
            (johnsonWindowBasis h Q) T.1)
          (johnsonAdjacentChannel_isHarmonic h hstrict T.2.1 Q.1
            (johnsonWindowBasis h Q)
            (johnsonWindowBasis_isHarmonic h Q) T.1) T.2.2) *
      (geometricAxis x T.1 *
        (johnsonFibreAmplitude n w p q L v T.2.1 *
          coupledDegreeCoordinates h x T.2.1 a T.2.2))) =
      Real.sqrt lam *
        (johnsonFibreAmplitude n w p q L v Q.1 *
          coupledDegreeCoordinates h x Q.1 a Q.2)
  rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_sigma]
  calc
    (∑ target : Index p q L,
      ∑ b : Fin (MetricCodes.booleanHarmonicDimension
        n (p + q + target.val)),
      ∑ k : Fin n,
        (johnsonAdjacentBlockCoefficient n w p q L v lam target Q.1 *
          johnsonHarmonicCoordinates (h.window_degree_half target)
            (johnsonAdjacentChannel n w p q L target Q.1
              (johnsonWindowBasis h Q) k)
            (johnsonAdjacentChannel_isHarmonic h hstrict target Q.1
              (johnsonWindowBasis h Q)
              (johnsonWindowBasis_isHarmonic h Q) k) b) *
          (geometricAxis x k *
            (johnsonFibreAmplitude n w p q L v target *
              coupledDegreeCoordinates h x target a b))) =
      ∑ target : Index p q L,
        (johnsonAdjacentBlockCoefficient n w p q L v lam target Q.1 *
          johnsonFibreAmplitude n w p q L v target) *
          (∑ k : Fin n,
            ∑ b : Fin (MetricCodes.booleanHarmonicDimension
              n (p + q + target.val)),
              geometricAxis x k *
                johnsonHarmonicCoordinates
                  (h.window_degree_half target)
                  (johnsonAdjacentChannel n w p q L target Q.1
                    (johnsonWindowBasis h Q) k)
                  (johnsonAdjacentChannel_isHarmonic
                    h hstrict target Q.1 (johnsonWindowBasis h Q)
                    (johnsonWindowBasis_isHarmonic h Q) k) b *
                coupledDegreeCoordinates h x target a b) := by
          apply Finset.sum_congr rfl
          intro target _
          rw [Finset.sum_comm, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
    _ = ∑ target : Index p q L,
        (johnsonAdjacentBlockCoefficient n w p q L v lam target Q.1 *
          johnsonFibreAmplitude n w p q L v target) *
          MetricCodes.Boolean.coordinateDot
            (johnsonAdjacentChannel n w p q L target Q.1
              (johnsonWindowBasis h Q))
            (johnsonAxisTensor x
              (coupledHarmonic x h.support_half h.complement_half
                a target.val)) := by
      apply Finset.sum_congr rfl
      intro target _
      rw [johnsonAdjacentChannel_coordinate_axisDot
        h hstrict x target Q.1
        (johnsonWindowBasis h Q)
        (johnsonWindowBasis_isHarmonic h Q) a]
    _ = (∑ target : Index p q L,
          johnsonAdjacentBlockCoefficient n w p q L v lam target Q.1 *
            johnsonFibreAmplitude n w p q L v target *
            Real.sqrt
              (johnsonSourceChannelCoefficient
                n w p q L Q.1 target)) *
          MetricCodes.Boolean.dot (johnsonWindowBasis h Q)
            (coupledHarmonic x h.support_half h.complement_half
              a Q.1.val) := by
      simp_rw [haxis x _ Q.1
        (johnsonWindowBasis h Q)
        (johnsonWindowBasis_isHarmonic h Q) a]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro target _
      ring
    _ = Real.sqrt lam *
        (johnsonFibreAmplitude n w p q L v Q.1 *
          coupledDegreeCoordinates h x Q.1 a Q.2) := by
      rw [johnsonAdjacentBlockCoefficient_amplitude_sum
        h hstrict v hv lam hlam heigen Q.1,
        johnsonWindowBasis_dot_coupled h x Q.1 a Q.2]
      ring

theorem johnsonChannelMatrix_transpose_axis_fibre
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L)
    (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen : operator n w p q L v = lam • v)
    (haxis : ∀ (x : JohnsonSphere n w)
      (target source : Index p q L)
      (f : MetricCodes.Boolean.Function n)
      (_ : MetricCodes.Boolean.IsHarmonic (p + q + source.val) f)
      (a : HarmonicFibreIndex n w p q),
        MetricCodes.Boolean.coordinateDot
          (johnsonAdjacentChannel n w p q L target source f)
          (johnsonAxisTensor x
            (coupledHarmonic x h.support_half h.complement_half
              a target.val)) =
          Real.sqrt
              (johnsonSourceChannelCoefficient
                n w p q L source target) *
            MetricCodes.Boolean.dot f
              (coupledHarmonic x h.support_half h.complement_half
                a source.val))
    (x : JohnsonSphere n w) :
    (johnsonChannelMatrix h hstrict v lam)ᵀ *
      MetricCodes.Boolean.matrixAxisLift
        (fun k : Fin n => geometricAxis x k)
        (johnsonFibreMatrix h v x) =
      Real.sqrt lam • johnsonFibreMatrix h v x := by
  classical
  let e := shellWindowIndexEquiv n p q L h.first_le
  let d := harmonicFibreIndexEquiv n w p q
  ext i a
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul]
  change
    (∑ T : Fin n × Fin (MetricCodes.johnsonAmbientDimension
      n (p + q) L),
      johnsonWindowChannelMatrix h hstrict v lam
          (T.1, e.symm T.2) (e.symm i) *
        (geometricAxis x T.1 *
          johnsonWindowFibreMatrix h v x
            (e.symm T.2) (d.symm a))) =
      Real.sqrt lam *
        johnsonWindowFibreMatrix h v x (e.symm i) (d.symm a)
  have hwindow := congrArg
    (fun M : Matrix (ShellWindowIndex n p q L)
        (HarmonicFibreIndex n w p q) ℝ =>
      M (e.symm i) (d.symm a))
    (johnsonWindowChannelMatrix_transpose_axis_fibre
      h hstrict v hv lam hlam heigen haxis x)
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul] at hwindow
  rw [Fintype.sum_prod_type] at hwindow ⊢
  calc
    (∑ k : Fin n,
      ∑ T : Fin (MetricCodes.johnsonAmbientDimension n (p + q) L),
        johnsonWindowChannelMatrix h hstrict v lam
            (k, e.symm T) (e.symm i) *
          (geometricAxis x k *
            johnsonWindowFibreMatrix h v x
              (e.symm T) (d.symm a))) =
      ∑ k : Fin n,
        ∑ T : ShellWindowIndex n p q L,
          johnsonWindowChannelMatrix h hstrict v lam
              (k, T) (e.symm i) *
            (geometricAxis x k *
              johnsonWindowFibreMatrix h v x T (d.symm a)) := by
        apply Finset.sum_congr rfl
        intro k _
        exact e.symm.sum_comp
          (fun T : ShellWindowIndex n p q L =>
            johnsonWindowChannelMatrix h hstrict v lam
                (k, T) (e.symm i) *
              (geometricAxis x k *
                johnsonWindowFibreMatrix h v x T (d.symm a)))
    _ = Real.sqrt lam *
        johnsonWindowFibreMatrix h v x (e.symm i) (d.symm a) :=
      hwindow

theorem johnsonChannelMatrix_transpose_axis_projection
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L)
    (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen : operator n w p q L v = lam • v)
    (haxis : ∀ (x : JohnsonSphere n w)
      (target source : Index p q L)
      (f : MetricCodes.Boolean.Function n)
      (_ : MetricCodes.Boolean.IsHarmonic (p + q + source.val) f)
      (a : HarmonicFibreIndex n w p q),
        MetricCodes.Boolean.coordinateDot
          (johnsonAdjacentChannel n w p q L target source f)
          (johnsonAxisTensor x
            (coupledHarmonic x h.support_half h.complement_half
              a target.val)) =
          Real.sqrt
              (johnsonSourceChannelCoefficient
                n w p q L source target) *
            MetricCodes.Boolean.dot f
              (coupledHarmonic x h.support_half h.complement_half
                a source.val))
    (x : JohnsonSphere n w) :
    (johnsonChannelMatrix h hstrict v lam)ᵀ *
      MetricCodes.Boolean.matrixAxisLift
        (fun k : Fin n => geometricAxis x k)
        ((johnsonProjectionFamily h v hv).projection x) =
      Real.sqrt lam •
        ((johnsonProjectionFamily h v hv).projection x) := by
  let A := johnsonFibreMatrix h v x
  change
    (johnsonChannelMatrix h hstrict v lam)ᵀ *
      MetricCodes.Boolean.matrixAxisLift
        (fun k : Fin n => geometricAxis x k)
        (A * Aᵀ) =
      Real.sqrt lam • (A * Aᵀ)
  rw [MetricCodes.Boolean.matrixAxisLift_mul, ← Matrix.mul_assoc,
    johnsonChannelMatrix_transpose_axis_fibre
      h hstrict v hv lam hlam heigen haxis x,
    Matrix.smul_mul]

def johnsonGramIndexEquiv (n D : ℕ) :
    ((Fin n × Fin D) × Fin D) ≃ Fin (n * D * D) :=
  Fintype.equivOfCardEq (by simp)

def johnsonProjectionGramFeature
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L)
    (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (x : JohnsonSphere n w) :
    EuclideanSpace ℝ
      (Fin (n * MetricCodes.johnsonAmbientDimension n (p + q) L *
        MetricCodes.johnsonAmbientDimension n (p + q) L)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (johnsonGramIndexEquiv n
      (MetricCodes.johnsonAmbientDimension n (p + q) L)))
    (MetricCodes.Boolean.matrixAxisGramFeature
      (johnsonProjectionFamily h v hv)
      (fun (y : JohnsonSphere n w) (k : Fin n) =>
        geometricAxis y k)
      (johnsonChannelMatrix h hstrict v lam)
      (Real.sqrt lam) x)

theorem johnsonProjectionGramFeature_inner
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L)
    (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen : operator n w p q L v = lam • v)
    (haxis : ∀ (x : JohnsonSphere n w)
      (target source : Index p q L)
      (f : MetricCodes.Boolean.Function n)
      (_ : MetricCodes.Boolean.IsHarmonic (p + q + source.val) f)
      (a : HarmonicFibreIndex n w p q),
        MetricCodes.Boolean.coordinateDot
          (johnsonAdjacentChannel n w p q L target source f)
          (johnsonAxisTensor x
            (coupledHarmonic x h.support_half h.complement_half
              a target.val)) =
          Real.sqrt
              (johnsonSourceChannelCoefficient
                n w p q L source target) *
            MetricCodes.Boolean.dot f
              (coupledHarmonic x h.support_half h.complement_half
                a source.val))
    (x y : JohnsonSphere n w) :
    @inner ℝ
      (EuclideanSpace ℝ
        (Fin (n * MetricCodes.johnsonAmbientDimension n (p + q) L *
          MetricCodes.johnsonAmbientDimension n (p + q) L))) _
      (johnsonProjectionGramFeature h hstrict v hv lam x)
      (johnsonProjectionGramFeature h hstrict v hv lam y) =
      (correlation x y - lam) *
        (johnsonProjectionFamily h v hv).overlap x y := by
  let P := johnsonProjectionFamily h v hv
  let axis : JohnsonSphere n w → Fin n → ℝ :=
    fun z k => geometricAxis z k
  let B := johnsonChannelMatrix h hstrict v lam
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (johnsonGramIndexEquiv n
      (MetricCodes.johnsonAmbientDimension n (p + q) L))
  have hgram := MetricCodes.Boolean.matrixAxisResidual_gram P axis B
    (Real.sqrt lam) lam
    (johnsonChannelMatrix_transpose_mul
      h hstrict v hv lam hlam heigen)
    (fun z => johnsonChannelMatrix_transpose_axis_projection
      h hstrict v hv lam hlam heigen haxis z)
    (Real.sq_sqrt hlam.le) x y
  have haxisinner :
      (∑ k : Fin n,
        geometricAxis x k * geometricAxis y k) =
        correlation x y := by
    have hinner := geometricAxis_inner h.weight_pos h.weight_lt x y
    simpa [PiLp.inner_apply, Real.inner_apply, mul_comm] using hinner
  change
    @inner ℝ
      (EuclideanSpace ℝ
        (Fin (n * MetricCodes.johnsonAmbientDimension n (p + q) L *
          MetricCodes.johnsonAmbientDimension n (p + q) L))) _
      (e (MetricCodes.Boolean.matrixAxisGramFeature P axis B
        (Real.sqrt lam) x))
      (e (MetricCodes.Boolean.matrixAxisGramFeature P axis B
        (Real.sqrt lam) y)) =
      (correlation x y - lam) * P.overlap x y
  rw [e.inner_map_map]
  simpa only [axis, haxisinner] using hgram

def johnsonProjectionGram_of_axis
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (hwindow : p + q < L)
    (haxis : ∀ (x : JohnsonSphere n w)
      (target source : Index p q L)
      (f : MetricCodes.Boolean.Function n)
      (_ : MetricCodes.Boolean.IsHarmonic (p + q + source.val) f)
      (a : HarmonicFibreIndex n w p q),
        MetricCodes.Boolean.coordinateDot
          (johnsonAdjacentChannel n w p q L target source f)
          (johnsonAxisTensor x
            (coupledHarmonic x h.support_half h.complement_half
              a target.val)) =
          Real.sqrt
              (johnsonSourceChannelCoefficient
                n w p q L source target) *
            MetricCodes.Boolean.dot f
              (coupledHarmonic x h.support_half h.complement_half
                a source.val)) :
    ProjectionGram n w p q L := by
  classical
  let hperron := exists_positive_unit_topEigenvector h hstrict
  let v : Space p q L := Classical.choose hperron
  have hdata := Classical.choose_spec hperron
  have heigen :
      operator n w p q L v =
        topEigenvalue n w p q L • v := hdata.2.1
  have hv : ∀ i : Index p q L, 0 < v i := hdata.2.2
  have hpositive := topEigenvalue_pos h hstrict hwindow
  exact {
    projections := johnsonProjectionFamily h v hv
    feature := johnsonProjectionGramFeature
      h hstrict v hv (topEigenvalue n w p q L)
    gram := fun x y => johnsonProjectionGramFeature_inner
      h hstrict v hv (topEigenvalue n w p q L)
      hpositive heigen haxis x y
  }

def johnsonProjectionGram
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (hwindow : p + q < L) :
    ProjectionGram n w p q L :=
  johnsonProjectionGram_of_axis h hstrict hwindow
    (fun x target source f hf a =>
      johnsonAdjacentChannel_axis_inner h hstrict x target source f hf a)

end MetricCodes.Johnson

end

end

section

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped BigOperators Topology

namespace MetricCodes.Johnson.SpectralAsymptotics

open MetricCodes.Johnson.Asymptotics

def terminalIndex (u : ℝ) (r n : ℕ) : ℕ :=
  terminalDegree u n - r

theorem tendsto_terminalIndex_ratio
    {u : ℝ} (hu : 0 < u) (r : ℕ) :
    Tendsto
      (fun n : ℕ => (terminalIndex u r n : ℝ) / (n : ℝ))
      atTop (nhds u) := by
  simpa [terminalIndex, terminalDegree] using
    MetricCodes.Hamming.tendsto_terminal_degree_ratio hu r

theorem tendsto_add_degree_add_fixed_ratio
    {f g : ℕ → ℕ} {a b : ℝ}
    (hf : Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ))
      atTop (nhds a))
    (hg : Tendsto (fun n : ℕ => (g n : ℝ) / (n : ℝ))
      atTop (nhds b))
    (r : ℕ) :
    Tendsto
      (fun n : ℕ => ((f n + g n + r : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (a + b)) := by
  have hsum := tendsto_add_degree_ratio hf hg
  have hoffset :=
    tendsto_const_div_atTop_nhds_zero_nat (r : ℝ)
  have htotal := hsum.add hoffset
  rw [add_zero] at htotal
  refine htotal.congr' (Eventually.of_forall fun n => ?_)
  push_cast
  ring

theorem eventually_terminal_block_fit
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (r : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      supportDegree b n + complementDegree g n + r <
        terminalDegree u n := by
  have hfirst := tendsto_add_degree_add_fixed_ratio
    (tendsto_supportDegree_ratio h.support_nonneg)
    (tendsto_complementDegree_ratio h.complement_nonneg) r
  exact eventually_degree_lt_of_ratio hfirst
    (tendsto_terminalDegree_ratio h.degree_pos.le)
    h.first_lt_degree

theorem tendsto_complementWeight_ratio
    {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        ((n - shellWeight a n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (1 - a)) := by
  simpa [shellWeight] using
    MetricCodes.Hamming.tendsto_complement_longitudinal_ratio ha ha'

theorem tendsto_johnsonJ1_ratio
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonJ1 (shellWeight a n) (supportDegree b n) /
          (n : ℝ))
      atTop (nhds (a / 2 - b)) := by
  have hspin :=
    (tendsto_shellWeight_ratio ha).div_const 2
  have hmain := hspin.sub (tendsto_supportDegree_ratio hb)
  refine hmain.congr' (Eventually.of_forall fun n => ?_)
  unfold MetricCodes.johnsonJ1
  ring

theorem tendsto_johnsonJ2_ratio
    {a g : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1) (hg : 0 ≤ g) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonJ2 n (shellWeight a n) (complementDegree g n) /
          (n : ℝ))
      atTop (nhds ((1 - a) / 2 - g)) := by
  have hspin :=
    (tendsto_complementWeight_ratio ha ha').div_const 2
  have hmain := hspin.sub (tendsto_complementDegree_ratio hg)
  refine hmain.congr' (Eventually.of_forall fun n => ?_)
  unfold MetricCodes.johnsonJ2
  ring

theorem tendsto_johnsonJ_ratio
    {u : ℝ} (hu : 0 < u) (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonJ n (terminalIndex u r n) / (n : ℝ))
      atTop (nhds (MetricCodes.Johnson.centeredDegree u / 2)) := by
  have hspin := tendsto_dimension_ratio.div_const 2
  have hmain := hspin.sub (tendsto_terminalIndex_ratio hu r)
  have hcenter : (1 : ℝ) / 2 - u =
      MetricCodes.Johnson.centeredDegree u / 2 := by
    unfold MetricCodes.Johnson.centeredDegree
    ring
  rw [hcenter] at hmain
  refine hmain.congr' (Eventually.of_forall fun n => ?_)
  unfold MetricCodes.johnsonJ
  ring

theorem tendsto_johnsonM_ratio
    {a : ℝ} (ha : 0 ≤ a) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonM n (shellWeight a n) / (n : ℝ))
      atTop (nhds (MetricCodes.Johnson.centeredWeight a / 2)) := by
  have hspin := tendsto_dimension_ratio.div_const 2
  have hmain := hspin.sub (tendsto_shellWeight_ratio ha)
  have hcenter : (1 : ℝ) / 2 - a =
      MetricCodes.Johnson.centeredWeight a / 2 := by
    unfold MetricCodes.Johnson.centeredWeight
    ring
  rw [hcenter] at hmain
  refine hmain.congr' (Eventually.of_forall fun n => ?_)
  unfold MetricCodes.johnsonM
  ring

theorem tendsto_johnsonSigma_ratio
    {a b g : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1)
    (hb : 0 ≤ b) (hg : 0 ≤ g) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonSigma n (shellWeight a n)
          (supportDegree b n) (complementDegree g n) /
            (n : ℝ))
      atTop (nhds (MetricCodes.Johnson.centeredSigma b g / 2)) := by
  have hmain :=
    (tendsto_johnsonJ1_ratio ha hb).add
      (tendsto_johnsonJ2_ratio ha ha' hg)
  have hcenter :
      (a / 2 - b) + ((1 - a) / 2 - g) =
        MetricCodes.Johnson.centeredSigma b g / 2 := by
    unfold MetricCodes.Johnson.centeredSigma
    ring
  rw [hcenter] at hmain
  refine hmain.congr' (Eventually.of_forall fun n => ?_)
  unfold MetricCodes.johnsonSigma
  ring

theorem tendsto_johnsonDelta_ratio
    {a b g : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1)
    (hb : 0 ≤ b) (hg : 0 ≤ g) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonDelta n (shellWeight a n)
          (supportDegree b n) (complementDegree g n) /
            (n : ℝ))
      atTop (nhds (MetricCodes.Johnson.centeredEta a b g / 2)) := by
  have hmain :=
    (tendsto_johnsonJ2_ratio ha ha' hg).sub
      (tendsto_johnsonJ1_ratio ha hb)
  have hcenter :
      ((1 - a) / 2 - g) - (a / 2 - b) =
        MetricCodes.Johnson.centeredEta a b g / 2 := by
    unfold MetricCodes.Johnson.centeredEta
    ring
  rw [hcenter] at hmain
  refine hmain.congr' (Eventually.of_forall fun n => ?_)
  unfold MetricCodes.johnsonDelta
  ring

def normalizedMu (j₁ j₂ j m e : ℝ) : ℝ :=
  (m / 2) *
    (j₂ * (j₂ + e) - j₁ * (j₁ + e)) /
      (j * (j + e))

theorem johnsonMu_div_eq_normalized
    (n w p q j : ℕ) (hn : 0 < n)
    (hj : MetricCodes.johnsonJ n j ≠ 0)
    (hj' : MetricCodes.johnsonJ n j + 1 ≠ 0) :
    MetricCodes.johnsonMu n w p q j / (n : ℝ) =
      normalizedMu
        (MetricCodes.johnsonJ1 w p / (n : ℝ))
        (MetricCodes.johnsonJ2 n w q / (n : ℝ))
        (MetricCodes.johnsonJ n j / (n : ℝ))
        (MetricCodes.johnsonM n w / (n : ℝ))
        ((1 : ℝ) / (n : ℝ)) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  unfold MetricCodes.johnsonMu normalizedMu
  field_simp [hnreal.ne', hj, hj']

def muLimit (a b g u : ℝ) : ℝ :=
  MetricCodes.Johnson.centeredWeight a *
      MetricCodes.Johnson.centeredSigma b g *
      MetricCodes.Johnson.centeredEta a b g /
    (4 * MetricCodes.Johnson.centeredDegree u ^ 2)

theorem normalizedMu_zero
    (a b g u : ℝ)
    (hz : MetricCodes.Johnson.centeredDegree u ≠ 0) :
    normalizedMu
        (a / 2 - b)
        ((1 - a) / 2 - g)
        (MetricCodes.Johnson.centeredDegree u / 2)
        (MetricCodes.Johnson.centeredWeight a / 2)
        0 =
      muLimit a b g u := by
  unfold normalizedMu muLimit
    MetricCodes.Johnson.centeredDegree MetricCodes.Johnson.centeredWeight
    MetricCodes.Johnson.centeredSigma MetricCodes.Johnson.centeredEta at *
  field_simp [hz]
  ; ring

private theorem tendsto_pointwise_div
    {f g : ℕ → ℝ} {a b : ℝ}
    (hf : Tendsto f atTop (nhds a))
    (hg : Tendsto g atTop (nhds b))
    (hb : b ≠ 0) :
    Tendsto (fun n : ℕ => f n / g n)
      atTop (nhds (a / b)) :=
  (hf.div hg hb).congr'
    (Eventually.of_forall fun _ => rfl)

theorem tendsto_johnsonMu_div
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonMu n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u r n) / (n : ℝ))
      atTop (nhds (muLimit a b g u)) := by
  have haone : a ≤ 1 := by linarith [h.weight_lt_half]
  have hj₁ := tendsto_johnsonJ1_ratio
    h.weight_pos.le h.support_nonneg
  have hj₂ := tendsto_johnsonJ2_ratio
    h.weight_pos.le haone h.complement_nonneg
  have hj := tendsto_johnsonJ_ratio h.degree_pos r
  have hm := tendsto_johnsonM_ratio h.weight_pos.le
  have he := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hnum :=
    (hm.div_const 2).mul
      ((hj₂.mul (hj₂.add he)).sub
        (hj₁.mul (hj₁.add he)))
  have hden := hj.mul (hj.add he)
  have hdenne :
      (MetricCodes.Johnson.centeredDegree u / 2) *
          (MetricCodes.Johnson.centeredDegree u / 2 + 0) ≠ 0 := by
    have hz := h.centeredDegree_pos
    positivity
  have hnormalized :
      Tendsto
        (fun n : ℕ =>
          normalizedMu
            (MetricCodes.johnsonJ1 (shellWeight a n)
              (supportDegree b n) / (n : ℝ))
            (MetricCodes.johnsonJ2 n (shellWeight a n)
              (complementDegree g n) / (n : ℝ))
            (MetricCodes.johnsonJ n (terminalIndex u r n) / (n : ℝ))
            (MetricCodes.johnsonM n (shellWeight a n) / (n : ℝ))
            ((1 : ℝ) / (n : ℝ)))
        atTop
        (nhds
          (normalizedMu
            (a / 2 - b)
            ((1 - a) / 2 - g)
            (MetricCodes.Johnson.centeredDegree u / 2)
            (MetricCodes.Johnson.centeredWeight a / 2)
            0)) := by
    simpa [normalizedMu] using
      tendsto_pointwise_div hnum hden hdenne
  rw [normalizedMu_zero a b g u h.centeredDegree_pos.ne']
    at hnormalized
  have hjpositive :
      ∀ᶠ n : ℕ in atTop,
        0 < MetricCodes.johnsonJ n (terminalIndex u r n) := by
    have hlimit : 0 < MetricCodes.Johnson.centeredDegree u / 2 := by
      exact div_pos h.centeredDegree_pos (by norm_num)
    have hevent := hj.eventually (Ioi_mem_nhds hlimit)
    filter_upwards [hevent, eventually_gt_atTop (0 : ℕ)]
      with n hjn hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hproduct :
        0 <
          (MetricCodes.johnsonJ n (terminalIndex u r n) / (n : ℝ)) *
            (n : ℝ) := mul_pos hjn hnreal
    have hidentity :
        (MetricCodes.johnsonJ n (terminalIndex u r n) / (n : ℝ)) *
            (n : ℝ) =
          MetricCodes.johnsonJ n (terminalIndex u r n) := by
      field_simp [hnreal.ne']
    rwa [hidentity] at hproduct
  refine hnormalized.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ), hjpositive]
    with n hn hjn
  exact
    (johnsonMu_div_eq_normalized n
      (shellWeight a n) (supportDegree b n)
      (complementDegree g n) (terminalIndex u r n) hn
      hjn.ne' (by positivity)).symm

def normalizedDiagonal
    (j₁ j₂ j m e x y : ℝ) : ℝ :=
  (normalizedMu j₁ j₂ j m e - m ^ 2) / (x * y)

theorem johnsonDiagonal_eq_normalized
    (n w p q j : ℕ)
    (hn : 0 < n) (hw : 0 < w) (hwn : w < n)
    (hj : 0 < MetricCodes.johnsonJ n j) :
    MetricCodes.johnsonDiagonal n w p q j =
      normalizedDiagonal
        (MetricCodes.johnsonJ1 w p / (n : ℝ))
        (MetricCodes.johnsonJ2 n w q / (n : ℝ))
        (MetricCodes.johnsonJ n j / (n : ℝ))
        (MetricCodes.johnsonM n w / (n : ℝ))
        ((1 : ℝ) / (n : ℝ))
        ((w : ℝ) / (n : ℝ))
        (((n - w : ℕ) : ℝ) / (n : ℝ)) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hwreal : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hc : (0 : ℝ) < ((n - w : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - w by omega)
  unfold normalizedDiagonal
  rw [← johnsonMu_div_eq_normalized n w p q j hn
    hj.ne' (by positivity)]
  unfold MetricCodes.johnsonDiagonal
  field_simp [hnreal.ne', hwreal.ne', hc.ne']

def diagonalLimit (a b g u : ℝ) : ℝ :=
  MetricCodes.Johnson.centeredWeight a *
      (MetricCodes.Johnson.centeredSigma b g *
        MetricCodes.Johnson.centeredEta a b g -
        MetricCodes.Johnson.centeredWeight a *
          MetricCodes.Johnson.centeredDegree u ^ 2) /
    (MetricCodes.Johnson.centeredDegree u ^ 2 *
      (1 - MetricCodes.Johnson.centeredWeight a ^ 2))

theorem tendsto_johnsonDiagonal
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonDiagonal n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u r n))
      atTop (nhds (diagonalLimit a b g u)) := by
  have haone : a ≤ 1 := by linarith [h.weight_lt_half]
  have hmu := tendsto_johnsonMu_div h r
  have hm := tendsto_johnsonM_ratio h.weight_pos.le
  have hw := tendsto_shellWeight_ratio h.weight_pos.le
  have hc := tendsto_complementWeight_ratio
    h.weight_pos.le haone
  have hdenne : a * (1 - a) ≠ 0 :=
    (mul_pos h.weight_pos h.weight_complement_pos).ne'
  have hquot := tendsto_pointwise_div
    (hmu.sub (hm.pow 2)) (hw.mul hc) hdenne
  have hlimit :
      (muLimit a b g u -
          (MetricCodes.Johnson.centeredWeight a / 2) ^ 2) /
        (a * (1 - a)) =
      diagonalLimit a b g u := by
    have hcenter :
        1 - MetricCodes.Johnson.centeredWeight a ^ 2 =
          4 * a * (1 - a) := by
      unfold MetricCodes.Johnson.centeredWeight
      ring
    unfold muLimit diagonalLimit
    exact MetricCodes.Johnson.Asymptotics.centered_diagonal_limit_algebra
      h.centeredDegree_pos.ne'
      h.one_sub_centeredWeight_sq_pos.ne' hcenter
  rw [hlimit] at hquot
  have hjpositive :
      ∀ᶠ n : ℕ in atTop,
        0 < MetricCodes.johnsonJ n (terminalIndex u r n) := by
    have hj := tendsto_johnsonJ_ratio h.degree_pos r
    have hlimit' : 0 < MetricCodes.Johnson.centeredDegree u / 2 := by
      exact div_pos h.centeredDegree_pos (by norm_num)
    filter_upwards [hj.eventually (Ioi_mem_nhds hlimit'),
      eventually_gt_atTop (0 : ℕ)] with n hjn hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hp := mul_pos hjn hnreal
    have heq :
        (MetricCodes.johnsonJ n (terminalIndex u r n) / (n : ℝ)) *
            (n : ℝ) =
          MetricCodes.johnsonJ n (terminalIndex u r n) := by
      field_simp [hnreal.ne']
    rwa [heq] at hp
  refine hquot.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_admissibleDegrees h, hjpositive]
    with n hn hadmissible hjn
  have hnormalized := johnsonDiagonal_eq_normalized n
    (shellWeight a n) (supportDegree b n)
    (complementDegree g n) (terminalIndex u r n)
    hn hadmissible.weight_pos hadmissible.weight_lt hjn
  have hmuidentity := johnsonMu_div_eq_normalized n
    (shellWeight a n) (supportDegree b n)
    (complementDegree g n) (terminalIndex u r n)
    hn hjn.ne' (by positivity)
  unfold normalizedDiagonal at hnormalized
  rw [← hmuidentity] at hnormalized
  exact hnormalized.symm

def normalizedNu (j m eta sigma e : ℝ) : ℝ :=
  Real.sqrt
      ((j ^ 2 - m ^ 2) *
        (j ^ 2 - eta ^ 2) *
        ((sigma + e) ^ 2 - j ^ 2)) /
    (2 * j * Real.sqrt ((2 * j - e) * (2 * j + e)))

theorem normalizedNu_scale
    (N J M eta sigma : ℝ)
    (hN : 0 < N) (hstep : 0 < 2 * J - 1) :
    (Real.sqrt
        ((J ^ 2 - M ^ 2) *
          (J ^ 2 - eta ^ 2) *
          ((sigma + 1) ^ 2 - J ^ 2)) /
      (2 * J * Real.sqrt ((2 * J - 1) * (2 * J + 1)))) / N =
      normalizedNu
        (J / N) (M / N) (eta / N) (sigma / N) (1 / N) := by
  have hrad :
      (J ^ 2 - M ^ 2) *
          (J ^ 2 - eta ^ 2) *
          ((sigma + 1) ^ 2 - J ^ 2) =
        (N ^ 3) ^ 2 *
          (((J / N) ^ 2 - (M / N) ^ 2) *
            ((J / N) ^ 2 - (eta / N) ^ 2) *
            (((sigma / N + 1 / N) ^ 2 - (J / N) ^ 2))) := by
    field_simp [hN.ne']

  have hdenrad :
      (2 * J - 1) * (2 * J + 1) =
        N ^ 2 *
          ((2 * (J / N) - 1 / N) *
            (2 * (J / N) + 1 / N)) := by
    field_simp [hN.ne']

  have hJ : 0 < J := by linarith
  have hleft : 0 < 2 * (J / N) - 1 / N := by
    have heq :
        2 * (J / N) - 1 / N = (2 * J - 1) / N := by
      field_simp [hN.ne']

    rw [heq]
    exact div_pos hstep hN
  have hright : 0 < 2 * (J / N) + 1 / N := by
    have heq :
        2 * (J / N) + 1 / N = (2 * J + 1) / N := by
      field_simp [hN.ne']

    rw [heq]
    exact div_pos (by linarith) hN
  have hroot :
      Real.sqrt
        ((2 * (J / N) - 1 / N) *
          (2 * (J / N) + 1 / N)) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos hleft hright)).ne'
  unfold normalizedNu
  rw [hrad, hdenrad,
    Real.sqrt_mul (sq_nonneg (N ^ 3)),
    Real.sqrt_sq (by positivity : 0 ≤ N ^ 3),
    Real.sqrt_mul (sq_nonneg N), Real.sqrt_sq hN.le]
  field_simp [hN.ne', hJ.ne', hroot]

theorem johnsonNu_div_eq_normalized
    (n w p q j : ℕ) (hn : 0 < n)
    (hstep : 0 < 2 * MetricCodes.johnsonJ n j - 1) :
    MetricCodes.johnsonNu n w p q j / (n : ℝ) =
      normalizedNu
        (MetricCodes.johnsonJ n j / (n : ℝ))
        (MetricCodes.johnsonM n w / (n : ℝ))
        (MetricCodes.johnsonDelta n w p q / (n : ℝ))
        (MetricCodes.johnsonSigma n w p q / (n : ℝ))
        ((1 : ℝ) / (n : ℝ)) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  simpa [MetricCodes.johnsonNu] using
    normalizedNu_scale (n : ℝ)
      (MetricCodes.johnsonJ n j) (MetricCodes.johnsonM n w)
      (MetricCodes.johnsonDelta n w p q)
      (MetricCodes.johnsonSigma n w p q) hnreal hstep

def nuLimit (a b g u : ℝ) : ℝ :=
  Real.sqrt
      ((MetricCodes.Johnson.centeredDegree u ^ 2 -
          MetricCodes.Johnson.centeredWeight a ^ 2) *
        (MetricCodes.Johnson.centeredDegree u ^ 2 -
          MetricCodes.Johnson.centeredEta a b g ^ 2) *
        (MetricCodes.Johnson.centeredSigma b g ^ 2 -
          MetricCodes.Johnson.centeredDegree u ^ 2)) /
    (8 * MetricCodes.Johnson.centeredDegree u ^ 2)

theorem normalizedNu_zero
    (a b g u : ℝ)
    (hz : 0 < MetricCodes.Johnson.centeredDegree u) :
    normalizedNu
        (MetricCodes.Johnson.centeredDegree u / 2)
        (MetricCodes.Johnson.centeredWeight a / 2)
        (MetricCodes.Johnson.centeredEta a b g / 2)
        (MetricCodes.Johnson.centeredSigma b g / 2)
        0 =
      nuLimit a b g u := by
  have hrad :
      ((MetricCodes.Johnson.centeredDegree u / 2) ^ 2 -
          (MetricCodes.Johnson.centeredWeight a / 2) ^ 2) *
        ((MetricCodes.Johnson.centeredDegree u / 2) ^ 2 -
          (MetricCodes.Johnson.centeredEta a b g / 2) ^ 2) *
        ((MetricCodes.Johnson.centeredSigma b g / 2) ^ 2 -
          (MetricCodes.Johnson.centeredDegree u / 2) ^ 2) =
      ((1 / 8 : ℝ) ^ 2) *
        ((MetricCodes.Johnson.centeredDegree u ^ 2 -
            MetricCodes.Johnson.centeredWeight a ^ 2) *
          (MetricCodes.Johnson.centeredDegree u ^ 2 -
            MetricCodes.Johnson.centeredEta a b g ^ 2) *
          (MetricCodes.Johnson.centeredSigma b g ^ 2 -
            MetricCodes.Johnson.centeredDegree u ^ 2)) := by
    ring
  have hdenrad :
      (2 * (MetricCodes.Johnson.centeredDegree u / 2)) *
          (2 * (MetricCodes.Johnson.centeredDegree u / 2)) =
        MetricCodes.Johnson.centeredDegree u ^ 2 := by
    ring
  unfold normalizedNu
  simp only [add_zero, sub_zero]
  rw [hrad, hdenrad,
    Real.sqrt_mul (sq_nonneg (1 / 8 : ℝ)),
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 8),
    Real.sqrt_sq hz.le]
  unfold nuLimit
  field_simp [hz.ne']

theorem tendsto_johnsonNu_div
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonNu n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u r n) / (n : ℝ))
      atTop (nhds (nuLimit a b g u)) := by
  have haone : a ≤ 1 := by linarith [h.weight_lt_half]
  have hj := tendsto_johnsonJ_ratio h.degree_pos r
  have hm := tendsto_johnsonM_ratio h.weight_pos.le
  have heta := tendsto_johnsonDelta_ratio
    h.weight_pos.le haone h.support_nonneg h.complement_nonneg
  have hsigma := tendsto_johnsonSigma_ratio
    h.weight_pos.le haone h.support_nonneg h.complement_nonneg
  have he := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ))
      atTop (nhds 2) := tendsto_const_nhds
  have hrad :=
    (((hj.pow 2).sub (hm.pow 2)).mul
      ((hj.pow 2).sub (heta.pow 2))).mul
        (((hsigma.add he).pow 2).sub (hj.pow 2))
  have hdenrad :=
    (((htwo.mul hj).sub he).mul
      ((htwo.mul hj).add he)).sqrt
  have hden := (htwo.mul hj).mul hdenrad
  have hz := h.centeredDegree_pos
  have hdenne :
      2 * (MetricCodes.Johnson.centeredDegree u / 2) *
        Real.sqrt
          ((2 * (MetricCodes.Johnson.centeredDegree u / 2) - 0) *
            (2 * (MetricCodes.Johnson.centeredDegree u / 2) + 0)) ≠ 0 := by
    have hhalf : 0 < MetricCodes.Johnson.centeredDegree u / 2 :=
      div_pos hz (by norm_num)
    have hrad :
        0 <
          (2 * (MetricCodes.Johnson.centeredDegree u / 2) - 0) *
            (2 * (MetricCodes.Johnson.centeredDegree u / 2) + 0) := by
      apply mul_pos <;> linarith
    exact
      (mul_pos (mul_pos (by norm_num) hhalf)
        (Real.sqrt_pos.mpr hrad)).ne'
  have hnormalized :
      Tendsto
        (fun n : ℕ =>
          normalizedNu
            (MetricCodes.johnsonJ n (terminalIndex u r n) / (n : ℝ))
            (MetricCodes.johnsonM n (shellWeight a n) / (n : ℝ))
            (MetricCodes.johnsonDelta n (shellWeight a n)
              (supportDegree b n) (complementDegree g n) /
                (n : ℝ))
            (MetricCodes.johnsonSigma n (shellWeight a n)
              (supportDegree b n) (complementDegree g n) /
                (n : ℝ))
            ((1 : ℝ) / (n : ℝ)))
        atTop
        (nhds
          (normalizedNu
            (MetricCodes.Johnson.centeredDegree u / 2)
            (MetricCodes.Johnson.centeredWeight a / 2)
            (MetricCodes.Johnson.centeredEta a b g / 2)
            (MetricCodes.Johnson.centeredSigma b g / 2)
            0)) := by
    simpa [normalizedNu] using
      tendsto_pointwise_div hrad.sqrt hden hdenne
  rw [normalizedNu_zero a b g u h.centeredDegree_pos]
    at hnormalized
  have hstep :
      ∀ᶠ n : ℕ in atTop,
        0 < 2 * MetricCodes.johnsonJ n (terminalIndex u r n) - 1 := by
    have hscaled := (htwo.mul hj).sub he
    have hlimit :
        0 < 2 * (MetricCodes.Johnson.centeredDegree u / 2) - 0 := by
      linarith [h.centeredDegree_pos]
    filter_upwards [hscaled.eventually (Ioi_mem_nhds hlimit),
      eventually_gt_atTop (0 : ℕ)] with n hscaled' hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hproduct := mul_pos hscaled' hnreal
    have hidentity :
        (2 *
            (MetricCodes.johnsonJ n (terminalIndex u r n) / (n : ℝ)) -
          (1 : ℝ) / (n : ℝ)) * (n : ℝ) =
        2 * MetricCodes.johnsonJ n (terminalIndex u r n) - 1 := by
      field_simp [hnreal.ne']

    rwa [hidentity] at hproduct
  refine hnormalized.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ), hstep]
    with n hn hstep'
  exact
    (johnsonNu_div_eq_normalized n
      (shellWeight a n) (supportDegree b n)
      (complementDegree g n) (terminalIndex u r n)
      hn hstep').symm

def edgeLimit (a b g u : ℝ) : ℝ :=
  Real.sqrt
      ((MetricCodes.Johnson.centeredDegree u ^ 2 -
          MetricCodes.Johnson.centeredWeight a ^ 2) *
        (MetricCodes.Johnson.centeredDegree u ^ 2 -
          MetricCodes.Johnson.centeredEta a b g ^ 2) *
        (MetricCodes.Johnson.centeredSigma b g ^ 2 -
          MetricCodes.Johnson.centeredDegree u ^ 2)) /
    (2 * MetricCodes.Johnson.centeredDegree u ^ 2 *
      (1 - MetricCodes.Johnson.centeredWeight a ^ 2))

private theorem centered_edge_limit_algebra
    {a m z R : ℝ}
    (hz : z ≠ 0) (ha : a ≠ 0) (hc : 1 - a ≠ 0)
    (hcenter : 1 - m ^ 2 = 4 * a * (1 - a)) :
    (Real.sqrt R / (8 * z ^ 2)) /
        (a * (1 - a)) =
      Real.sqrt R / (2 * z ^ 2 * (1 - m ^ 2)) := by
  rw [hcenter]
  field_simp [hz, ha, hc]
  ; ring

theorem tendsto_johnsonEdge
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonEdge n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u r n))
      atTop (nhds (edgeLimit a b g u)) := by
  have haone : a ≤ 1 := by linarith [h.weight_lt_half]
  have hnu := tendsto_johnsonNu_div h r
  have hw := tendsto_shellWeight_ratio h.weight_pos.le
  have hc := tendsto_complementWeight_ratio
    h.weight_pos.le haone
  have hdenne : a * (1 - a) ≠ 0 :=
    (mul_pos h.weight_pos h.weight_complement_pos).ne'
  have hquot := tendsto_pointwise_div hnu (hw.mul hc) hdenne
  have hcenter :
      1 - MetricCodes.Johnson.centeredWeight a ^ 2 =
        4 * a * (1 - a) := by
    unfold MetricCodes.Johnson.centeredWeight
    ring
  have hlimit :
      nuLimit a b g u / (a * (1 - a)) =
        edgeLimit a b g u := by
    unfold nuLimit edgeLimit
    exact centered_edge_limit_algebra
      h.centeredDegree_pos.ne' h.weight_pos.ne'
      h.weight_complement_pos.ne' hcenter
  rw [hlimit] at hquot
  refine hquot.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_admissibleDegrees h] with n hn hadmissible
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hwreal : (0 : ℝ) < (shellWeight a n : ℝ) := by
    exact_mod_cast hadmissible.weight_pos
  have hcreal :
      (0 : ℝ) < ((n - shellWeight a n : ℕ) : ℝ) := by
    exact_mod_cast
      (Nat.sub_pos_of_lt hadmissible.weight_lt)
  unfold MetricCodes.johnsonEdge
  field_simp [hnreal.ne', hwreal.ne', hcreal.ne']

theorem zeroFibreParameters
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    MetricCodes.Johnson.AsymptoticParameters d a 0 0 u := by
  refine ⟨h.distance_pos, h.distance_lt_half,
    h.weight_gt_distance, h.weight_lt_half,
    le_rfl, ?_, le_rfl, ?_, ?_, h.degree_lt_weight, ?_, ?_⟩
  · linarith [h.weight_pos]
  · linarith [h.weight_complement_pos]
  · simpa using h.degree_pos
  · simpa using h.degree_lt_weight
  · nlinarith [h.degree_lt_weight, h.weight_lt_half]

def hattedDiagonalLimit (a b g u : ℝ) : ℝ :=
  (MetricCodes.Johnson.centeredSigma b g *
      MetricCodes.Johnson.centeredEta a b g -
      MetricCodes.Johnson.centeredWeight a *
        MetricCodes.Johnson.centeredDegree u ^ 2) ^ 2 /
    (MetricCodes.Johnson.centeredDegree u ^ 2 *
      (1 - MetricCodes.Johnson.centeredWeight a ^ 2) *
      (1 - MetricCodes.Johnson.centeredDegree u ^ 2))

def hattedEdgeLimit (a b g u : ℝ) : ℝ :=
  ((MetricCodes.Johnson.centeredDegree u ^ 2 -
      MetricCodes.Johnson.centeredEta a b g ^ 2) *
    (MetricCodes.Johnson.centeredSigma b g ^ 2 -
      MetricCodes.Johnson.centeredDegree u ^ 2)) /
    (2 * MetricCodes.Johnson.centeredDegree u ^ 2 *
      (1 - MetricCodes.Johnson.centeredWeight a ^ 2) *
      Real.sqrt (1 - MetricCodes.Johnson.centeredDegree u ^ 2))

theorem spectralLimit_eq_hatted
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    MetricCodes.Johnson.spectralLimit a b g u =
      hattedDiagonalLimit a b g u + 2 * hattedEdgeLimit a b g u := by
  unfold MetricCodes.Johnson.spectralLimit hattedDiagonalLimit hattedEdgeLimit
  dsimp
  have hz := h.centeredDegree_pos.ne'
  have hm := h.one_sub_centeredWeight_sq_pos.ne'
  have hu := h.one_sub_centeredDegree_sq_pos.ne'
  have hs := (Real.sqrt_pos.mpr h.one_sub_centeredDegree_sq_pos).ne'
  field_simp [hz, hm, hu, hs]

theorem hattedEdgeLimit_pos
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    0 < hattedEdgeLimit a b g u := by
  unfold hattedEdgeLimit
  have hz := h.centeredDegree_pos
  have hm := h.one_sub_centeredWeight_sq_pos
  have hu := h.one_sub_centeredDegree_sq_pos
  have he := h.degree_sq_sub_eta_sq_pos
  have hs := h.sigma_sq_sub_degree_sq_pos
  positivity

theorem diagonalLimit_zero_eq
    {d a b g u : ℝ}
    (_h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    diagonalLimit a 0 0 u =
      MetricCodes.Johnson.centeredWeight a ^ 2 *
        (1 - MetricCodes.Johnson.centeredDegree u ^ 2) /
        (MetricCodes.Johnson.centeredDegree u ^ 2 *
          (1 - MetricCodes.Johnson.centeredWeight a ^ 2)) := by
  unfold diagonalLimit MetricCodes.Johnson.centeredSigma
    MetricCodes.Johnson.centeredEta
  have heta : 1 - 2 * a + 2 * (0 : ℝ) - 2 * 0 =
      MetricCodes.Johnson.centeredWeight a := by
    unfold MetricCodes.Johnson.centeredWeight
    ring
  rw [heta]
  norm_num
  ring

theorem diagonalLimit_zero_pos
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    0 < diagonalLimit a 0 0 u := by
  have hz := h.centeredDegree_pos
  have hm := h.centeredWeight_pos
  have hden := h.one_sub_centeredWeight_sq_pos
  have hu := h.one_sub_centeredDegree_sq_pos
  rw [diagonalLimit_zero_eq h]
  exact div_pos (mul_pos (sq_pos_of_pos hm) hu)
    (mul_pos (sq_pos_of_pos hz) hden)

theorem diagonalLimit_sq_div_zero
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    diagonalLimit a b g u ^ 2 / diagonalLimit a 0 0 u =
      hattedDiagonalLimit a b g u := by
  have hz := h.centeredDegree_pos.ne'
  have hm := h.centeredWeight_pos.ne'
  have hd := h.one_sub_centeredWeight_sq_pos.ne'
  have hu := h.one_sub_centeredDegree_sq_pos.ne'
  rw [diagonalLimit_zero_eq h]
  unfold diagonalLimit hattedDiagonalLimit
  field_simp [hz, hm, hd, hu]

theorem edgeLimit_zero_eq
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    edgeLimit a 0 0 u =
      (MetricCodes.Johnson.centeredDegree u ^ 2 -
        MetricCodes.Johnson.centeredWeight a ^ 2) *
        Real.sqrt (1 - MetricCodes.Johnson.centeredDegree u ^ 2) /
        (2 * MetricCodes.Johnson.centeredDegree u ^ 2 *
          (1 - MetricCodes.Johnson.centeredWeight a ^ 2)) := by
  have hzero := zeroFibreParameters h
  have hfactor := hzero.degree_sq_sub_eta_sq_pos
  have hfactor' : 0 < MetricCodes.Johnson.centeredDegree u ^ 2 -
      MetricCodes.Johnson.centeredWeight a ^ 2 := by
    simpa [MetricCodes.Johnson.centeredEta,
      MetricCodes.Johnson.centeredWeight] using hfactor
  unfold edgeLimit
  have heta : MetricCodes.Johnson.centeredEta a 0 0 =
      MetricCodes.Johnson.centeredWeight a := by
    simp [MetricCodes.Johnson.centeredEta, MetricCodes.Johnson.centeredWeight]
  have hsigma : MetricCodes.Johnson.centeredSigma 0 0 = 1 := by
    norm_num [MetricCodes.Johnson.centeredSigma]
  rw [heta, hsigma]
  have hrad :
      Real.sqrt
          ((MetricCodes.Johnson.centeredDegree u ^ 2 -
              MetricCodes.Johnson.centeredWeight a ^ 2) *
            (MetricCodes.Johnson.centeredDegree u ^ 2 -
              MetricCodes.Johnson.centeredWeight a ^ 2) *
            ((1 : ℝ) ^ 2 - MetricCodes.Johnson.centeredDegree u ^ 2)) =
        (MetricCodes.Johnson.centeredDegree u ^ 2 -
          MetricCodes.Johnson.centeredWeight a ^ 2) *
          Real.sqrt (1 - MetricCodes.Johnson.centeredDegree u ^ 2) := by
    rw [one_pow]
    rw [← pow_two]
    rw [Real.sqrt_mul (sq_nonneg _)]
    rw [Real.sqrt_sq hfactor'.le]
  rw [hrad]

theorem edgeLimit_zero_pos
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    0 < edgeLimit a 0 0 u := by
  rw [edgeLimit_zero_eq h]
  have hzero := zeroFibreParameters h
  have hfactor := hzero.degree_sq_sub_eta_sq_pos
  have hfactor' : 0 < MetricCodes.Johnson.centeredDegree u ^ 2 -
      MetricCodes.Johnson.centeredWeight a ^ 2 := by
    simpa [MetricCodes.Johnson.centeredEta,
      MetricCodes.Johnson.centeredWeight] using hfactor
  have hz := h.centeredDegree_pos
  have hm := h.one_sub_centeredWeight_sq_pos
  have hu := h.one_sub_centeredDegree_sq_pos
  positivity

theorem edgeLimit_sq_div_zero
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    edgeLimit a b g u ^ 2 / edgeLimit a 0 0 u =
      hattedEdgeLimit a b g u := by
  rw [edgeLimit_zero_eq h]
  have hzero := zeroFibreParameters h
  have hfactor := hzero.degree_sq_sub_eta_sq_pos
  have hfactor' : 0 < MetricCodes.Johnson.centeredDegree u ^ 2 -
      MetricCodes.Johnson.centeredWeight a ^ 2 := by
    simpa [MetricCodes.Johnson.centeredEta,
      MetricCodes.Johnson.centeredWeight] using hfactor
  have hrad : 0 ≤
      (MetricCodes.Johnson.centeredDegree u ^ 2 -
          MetricCodes.Johnson.centeredWeight a ^ 2) *
        (MetricCodes.Johnson.centeredDegree u ^ 2 -
          MetricCodes.Johnson.centeredEta a b g ^ 2) *
        (MetricCodes.Johnson.centeredSigma b g ^ 2 -
          MetricCodes.Johnson.centeredDegree u ^ 2) := by
    exact (mul_pos (mul_pos hfactor'
      h.degree_sq_sub_eta_sq_pos)
      h.sigma_sq_sub_degree_sq_pos).le
  have hsquare := Real.sq_sqrt hrad
  have hz := h.centeredDegree_pos.ne'
  have hm := h.one_sub_centeredWeight_sq_pos.ne'
  have hu := h.one_sub_centeredDegree_sq_pos
  have hs := (Real.sqrt_pos.mpr hu).ne'
  have hf := hfactor'.ne'
  unfold edgeLimit hattedEdgeLimit
  field_simp [hz, hm, hs, hf]
  nlinarith [hsquare]

theorem tendsto_johnsonHattedDiagonal
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonHattedDiagonal n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u r n))
      atTop (nhds (hattedDiagonalLimit a b g u)) := by
  have hzero := zeroFibreParameters h
  have hnum := (tendsto_johnsonDiagonal h r).pow 2
  have hden := tendsto_johnsonDiagonal hzero r
  have hden' :
      Tendsto
        (fun n : ℕ =>
          MetricCodes.johnsonZonalDiagonal n (shellWeight a n)
            (terminalIndex u r n))
        atTop (nhds (diagonalLimit a 0 0 u)) := by
    simpa [MetricCodes.johnsonZonalDiagonal,
      supportDegree, complementDegree,
      MetricCodes.Hamming.longitudinalDegree] using hden
  have hquot := hnum.div hden' (diagonalLimit_zero_pos h).ne'
  rw [diagonalLimit_sq_div_zero h] at hquot
  refine hquot.congr' ?_
  filter_upwards [eventually_terminal_block_fit h r] with n hn
  have hpositive : 0 < terminalIndex u r n := by
    unfold terminalIndex
    omega
  simp [MetricCodes.johnsonHattedDiagonal, hpositive.ne']

theorem tendsto_johnsonHattedEdge
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonHattedEdge n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u r n))
      atTop (nhds (hattedEdgeLimit a b g u)) := by
  have hzero := zeroFibreParameters h
  have hnum := (tendsto_johnsonEdge h r).pow 2
  have hden := tendsto_johnsonEdge hzero r
  have hden' :
      Tendsto
        (fun n : ℕ =>
          MetricCodes.johnsonZonalEdge n (shellWeight a n)
            (terminalIndex u r n))
        atTop (nhds (edgeLimit a 0 0 u)) := by
    simpa [MetricCodes.johnsonZonalEdge,
      supportDegree, complementDegree,
      MetricCodes.Hamming.longitudinalDegree] using hden
  have hquot := hnum.div hden' (edgeLimit_zero_pos h).ne'
  rw [edgeLimit_sq_div_zero h] at hquot
  exact hquot.congr' (Eventually.of_forall fun n => by
    rfl)

end MetricCodes.Johnson.SpectralAsymptotics

end

end

section

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped BigOperators Topology

namespace MetricCodes.Johnson.SpectralAsymptotics

open MetricCodes.Johnson.Asymptotics

theorem tridiagonal_quadratic_sum
    (d : ℕ) (b c v : ℕ → ℝ) :
    (∑ i ∈ Finset.range (d + 1),
      ∑ j ∈ Finset.range (d + 1),
        (if i = j then b i
          else if i + 1 = j then c i
          else if j + 1 = i then c j else 0) * v j * v i) =
      (∑ i ∈ Finset.range (d + 1), b i * v i ^ 2) +
        2 * ∑ i ∈ Finset.range d, c i * v i * v (i + 1) := by
  have hpoint (i j : ℕ) :
      (if i = j then b i
        else if i + 1 = j then c i
        else if j + 1 = i then c j else 0) * v j * v i =
      (if i = j then b i * v i ^ 2 else 0) +
        (if i + 1 = j then c i
          else if j + 1 = i then c j else 0) * v j * v i := by
    by_cases hij : i = j
    · subst j
      simp
      ring
    · simp [hij]
  calc
    (∑ i ∈ Finset.range (d + 1),
      ∑ j ∈ Finset.range (d + 1),
        (if i = j then b i
          else if i + 1 = j then c i
          else if j + 1 = i then c j else 0) * v j * v i) =
      ∑ i ∈ Finset.range (d + 1),
        ∑ j ∈ Finset.range (d + 1),
          ((if i = j then b i * v i ^ 2 else 0) +
            (if i + 1 = j then c i
              else if j + 1 = i then c j else 0) * v j * v i) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact hpoint i j
    _ =
      (∑ i ∈ Finset.range (d + 1),
        ∑ j ∈ Finset.range (d + 1),
          if i = j then b i * v i ^ 2 else 0) +
      (∑ i ∈ Finset.range (d + 1),
        ∑ j ∈ Finset.range (d + 1),
          (if i + 1 = j then c i
            else if j + 1 = i then c j else 0) * v j * v i) := by
        simp_rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [MetricCodes.Hamming.tridiagonal_quadratic_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]

theorem terminal_indicator_diagonal_sum
    (d m : ℕ) (hm : m ≤ d) (b : ℕ → ℝ) :
    (∑ i ∈ Finset.range (d + 1),
      b i * MetricCodes.Hamming.terminalIndicator d m i ^ 2) =
      ∑ r ∈ Finset.range (m + 1), b (d - m + r) := by
  have hsplit : d + 1 = (d - m) + (m + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hfirst :
      (∑ i ∈ Finset.range (d - m),
        b i * MetricCodes.Hamming.terminalIndicator d m i ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i < d - m := Finset.mem_range.mp hi
    simp [MetricCodes.Hamming.terminalIndicator, Nat.not_le.mpr hi']
  rw [hfirst, zero_add]
  apply Finset.sum_congr rfl
  intro r hr
  have hmem : d - m ≤ d - m + r := by omega
  simp [MetricCodes.Hamming.terminalIndicator, hmem]

def terminalVector (p q L m : ℕ) : MetricCodes.Johnson.Space p q L :=
  MetricCodes.Hamming.terminalVector (p + q) L m

theorem terminalVector_ne_zero (p q L m : ℕ) :
    terminalVector p q L m ≠ 0 := by
  exact MetricCodes.Hamming.terminalVector_ne_zero (p + q) L m

theorem terminalVector_norm_sq
    (p q L m : ℕ) (hm : m ≤ L - (p + q)) :
    ‖terminalVector p q L m‖ ^ 2 = (m : ℝ) + 1 := by
  exact MetricCodes.Hamming.terminalVector_norm_sq (p + q) L m hm

theorem terminalVector_inner
    (n w p q L m : ℕ)
    (hfirst : p + q ≤ L) (hm : m ≤ L - (p + q)) :
    @inner ℝ (MetricCodes.Johnson.Space p q L) _
      (MetricCodes.Johnson.operator n w p q L (terminalVector p q L m))
      (terminalVector p q L m) =
      (∑ r ∈ Finset.range (m + 1),
        MetricCodes.johnsonHattedDiagonal n w p q (L - m + r)) +
      2 * ∑ r ∈ Finset.range m,
        MetricCodes.johnsonHattedEdge n w p q (L - m + r) := by
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  change
    (∑ i : Fin (L - (p + q) + 1),
      (∑ j : Fin (L - (p + q) + 1),
        (if i = j then
          MetricCodes.johnsonHattedDiagonal n w p q (p + q + i.val)
        else if i.val + 1 = j.val then
          MetricCodes.johnsonHattedEdge n w p q (p + q + i.val)
        else if j.val + 1 = i.val then
          MetricCodes.johnsonHattedEdge n w p q (p + q + j.val)
        else 0) *
          MetricCodes.Hamming.terminalIndicator (L - (p + q)) m j.val) *
        MetricCodes.Hamming.terminalIndicator (L - (p + q)) m i.val) = _
  simp_rw [Finset.sum_mul]
  let f : ℕ → ℝ := fun i =>
    ∑ j : Fin (L - (p + q) + 1),
      (if i = j.val then
        MetricCodes.johnsonHattedDiagonal n w p q (p + q + i)
      else if i + 1 = j.val then
        MetricCodes.johnsonHattedEdge n w p q (p + q + i)
      else if j.val + 1 = i then
        MetricCodes.johnsonHattedEdge n w p q (p + q + j.val)
      else 0) *
        MetricCodes.Hamming.terminalIndicator (L - (p + q)) m j.val *
        MetricCodes.Hamming.terminalIndicator (L - (p + q)) m i
  have hreplace :
      (∑ i : Fin (L - (p + q) + 1),
        ∑ j : Fin (L - (p + q) + 1),
          (if i = j then
            MetricCodes.johnsonHattedDiagonal n w p q (p + q + i.val)
          else if i.val + 1 = j.val then
            MetricCodes.johnsonHattedEdge n w p q (p + q + i.val)
          else if j.val + 1 = i.val then
            MetricCodes.johnsonHattedEdge n w p q (p + q + j.val)
          else 0) *
            MetricCodes.Hamming.terminalIndicator (L - (p + q)) m j.val *
            MetricCodes.Hamming.terminalIndicator (L - (p + q)) m i.val) =
        ∑ i : Fin (L - (p + q) + 1), f i.val := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [f]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i = j
    · subst j
      simp
    · have hval : i.val ≠ j.val := fun heq => hij (Fin.ext heq)
      simp [hij, hval]
  rw [hreplace, Fin.sum_univ_eq_sum_range f]
  dsimp only [f]
  have hfin (i : ℕ) :
      (∑ j : Fin (L - (p + q) + 1),
        (if i = j.val then
          MetricCodes.johnsonHattedDiagonal n w p q (p + q + i)
        else if i + 1 = j.val then
          MetricCodes.johnsonHattedEdge n w p q (p + q + i)
        else if j.val + 1 = i then
          MetricCodes.johnsonHattedEdge n w p q (p + q + j.val)
        else 0) *
          MetricCodes.Hamming.terminalIndicator (L - (p + q)) m j.val *
          MetricCodes.Hamming.terminalIndicator (L - (p + q)) m i) =
        ∑ j ∈ Finset.range (L - (p + q) + 1),
          (if i = j then
            MetricCodes.johnsonHattedDiagonal n w p q (p + q + i)
          else if i + 1 = j then
            MetricCodes.johnsonHattedEdge n w p q (p + q + i)
          else if j + 1 = i then
            MetricCodes.johnsonHattedEdge n w p q (p + q + j)
          else 0) *
            MetricCodes.Hamming.terminalIndicator (L - (p + q)) m j *
            MetricCodes.Hamming.terminalIndicator (L - (p + q)) m i := by
    let g : ℕ → ℝ := fun j =>
      (if i = j then
        MetricCodes.johnsonHattedDiagonal n w p q (p + q + i)
      else if i + 1 = j then
        MetricCodes.johnsonHattedEdge n w p q (p + q + i)
      else if j + 1 = i then
        MetricCodes.johnsonHattedEdge n w p q (p + q + j)
      else 0) *
        MetricCodes.Hamming.terminalIndicator (L - (p + q)) m j *
        MetricCodes.Hamming.terminalIndicator (L - (p + q)) m i
    change (∑ j : Fin (L - (p + q) + 1), g j.val) =
      ∑ j ∈ Finset.range (L - (p + q) + 1), g j
    exact Fin.sum_univ_eq_sum_range g (L - (p + q) + 1)
  simp_rw [hfin]
  rw [tridiagonal_quadratic_sum]
  rw [terminal_indicator_diagonal_sum (L - (p + q)) m hm]
  rw [MetricCodes.Hamming.terminal_indicator_edge_sum (L - (p + q)) m hm]
  congr 1
  · apply Finset.sum_congr rfl
    intro r hr
    congr 1
    omega
  · congr 1
    apply Finset.sum_congr rfl
    intro r hr
    congr 1
    omega

theorem terminalVector_rayleigh
    (n w p q L m : ℕ)
    (hfirst : p + q ≤ L) (hm : m ≤ L - (p + q)) :
    MetricCodes.Johnson.rayleigh n w p q L (terminalVector p q L m) =
      ((∑ r ∈ Finset.range (m + 1),
          MetricCodes.johnsonHattedDiagonal n w p q (L - m + r)) +
        2 * ∑ r ∈ Finset.range m,
          MetricCodes.johnsonHattedEdge n w p q (L - m + r)) /
        ((m : ℝ) + 1) := by
  rw [MetricCodes.Johnson.rayleigh_eq_inner,
    terminalVector_inner n w p q L m hfirst hm,
    terminalVector_norm_sq p q L m hm]

theorem terminal_rayleigh_le_top
    (n w p q L m : ℕ)
    (hfirst : p + q ≤ L) (hm : m ≤ L - (p + q)) :
    ((∑ r ∈ Finset.range (m + 1),
        MetricCodes.johnsonHattedDiagonal n w p q (L - m + r)) +
      2 * ∑ r ∈ Finset.range m,
        MetricCodes.johnsonHattedEdge n w p q (L - m + r)) /
      ((m : ℝ) + 1) ≤ MetricCodes.Johnson.topEigenvalue n w p q L := by
  rw [← terminalVector_rayleigh n w p q L m hfirst hm]
  exact MetricCodes.Johnson.rayleigh_le_top n w p q L
    (terminalVector p q L m) (terminalVector_ne_zero p q L m)

def terminalRayleigh (a b g u : ℝ) (m n : ℕ) : ℝ :=
  ((∑ r ∈ Finset.range (m + 1),
      MetricCodes.johnsonHattedDiagonal n (shellWeight a n)
        (supportDegree b n) (complementDegree g n)
        (terminalIndex u (m - r) n)) +
    2 * ∑ r ∈ Finset.range m,
      MetricCodes.johnsonHattedEdge n (shellWeight a n)
        (supportDegree b n) (complementDegree g n)
        (terminalIndex u (m - r) n)) /
    ((m : ℝ) + 1)

theorem tendsto_terminalRayleigh
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (m : ℕ) :
    Tendsto (terminalRayleigh a b g u m) atTop
      (nhds
        ((((m : ℝ) + 1) * hattedDiagonalLimit a b g u +
          2 * (m : ℝ) * hattedEdgeLimit a b g u) /
            ((m : ℝ) + 1))) := by
  have hdiagonal :
      Tendsto
        (fun n : ℕ =>
          ∑ r ∈ Finset.range (m + 1),
            MetricCodes.johnsonHattedDiagonal n (shellWeight a n)
              (supportDegree b n) (complementDegree g n)
              (terminalIndex u (m - r) n))
        atTop
        (nhds (∑ _r ∈ Finset.range (m + 1),
          hattedDiagonalLimit a b g u)) := by
    apply tendsto_finsetSum
    intro r hr
    exact tendsto_johnsonHattedDiagonal h (m - r)
  have hedge :
      Tendsto
        (fun n : ℕ =>
          ∑ r ∈ Finset.range m,
            MetricCodes.johnsonHattedEdge n (shellWeight a n)
              (supportDegree b n) (complementDegree g n)
              (terminalIndex u (m - r) n))
        atTop
        (nhds (∑ _r ∈ Finset.range m,
          hattedEdgeLimit a b g u)) := by
    apply tendsto_finsetSum
    intro r hr
    exact tendsto_johnsonHattedEdge h (m - r)
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hquot := (hdiagonal.add (htwo.mul hedge)).div_const
    ((m : ℝ) + 1)
  change Tendsto (fun n : ℕ => terminalRayleigh a b g u m n) atTop _
  simpa [terminalRayleigh, Nat.cast_add, Nat.cast_one,
    mul_comm, mul_left_comm, mul_assoc] using hquot

theorem terminalRayleigh_le_top
    (a b g u : ℝ) (m n : ℕ)
    (hfit : supportDegree b n + complementDegree g n + m ≤
      terminalDegree u n) :
    terminalRayleigh a b g u m n ≤
      MetricCodes.Johnson.topEigenvalue n (shellWeight a n)
        (supportDegree b n) (complementDegree g n)
        (terminalDegree u n) := by
  have hfirst :
      supportDegree b n + complementDegree g n ≤
        terminalDegree u n := by omega
  have hm :
      m ≤ terminalDegree u n -
        (supportDegree b n + complementDegree g n) := by omega
  have hdiag :
      (∑ r ∈ Finset.range (m + 1),
        MetricCodes.johnsonHattedDiagonal n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u (m - r) n)) =
      ∑ r ∈ Finset.range (m + 1),
        MetricCodes.johnsonHattedDiagonal n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalDegree u n - m + r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < m + 1 := Finset.mem_range.mp hr
    congr 1
    unfold terminalIndex
    omega
  have hedge :
      (∑ r ∈ Finset.range m,
        MetricCodes.johnsonHattedEdge n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u (m - r) n)) =
      ∑ r ∈ Finset.range m,
        MetricCodes.johnsonHattedEdge n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalDegree u n - m + r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < m := Finset.mem_range.mp hr
    congr 1
    unfold terminalIndex
    omega
  unfold terminalRayleigh
  rw [hdiag, hedge]
  exact terminal_rayleigh_le_top n (shellWeight a n)
    (supportDegree b n) (complementDegree g n)
    (terminalDegree u n) m hfirst hm

theorem eventually_topEigenvalue_gt
    {d a b g u s : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (hs : s < MetricCodes.Johnson.spectralLimit a b g u) :
    ∀ᶠ n : ℕ in atTop,
      s < MetricCodes.Johnson.topEigenvalue n (shellWeight a n)
        (supportDegree b n) (complementDegree g n)
        (terminalDegree u n) := by
  let E : ℝ := hattedEdgeLimit a b g u
  let S : ℝ := MetricCodes.Johnson.spectralLimit a b g u
  let ε : ℝ := (S - s) / 2
  have hE : 0 < E := hattedEdgeLimit_pos h
  have hε : 0 < ε := by
    dsimp [ε, S]
    linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * E / ε)
  have hprod : 2 * E < (m : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hm
  have hden : 0 < (m : ℝ) + 1 := by positivity
  have hrem : 2 * E / ((m : ℝ) + 1) < ε := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hidentity :
      (((m : ℝ) + 1) * hattedDiagonalLimit a b g u +
        2 * (m : ℝ) * hattedEdgeLimit a b g u) /
          ((m : ℝ) + 1) =
        S - 2 * E / ((m : ℝ) + 1) := by
    dsimp [S, E]
    rw [spectralLimit_eq_hatted h]
    field_simp [hden.ne']
    ; ring
  have hbelow :
      s <
        (((m : ℝ) + 1) * hattedDiagonalLimit a b g u +
          2 * (m : ℝ) * hattedEdgeLimit a b g u) /
            ((m : ℝ) + 1) := by
    rw [hidentity]
    dsimp [ε] at hrem
    linarith
  have hquot := (tendsto_terminalRayleigh h m).eventually
    (lt_mem_nhds hbelow)
  filter_upwards [hquot, eventually_terminal_block_fit h m]
    with n hn hfit
  exact hn.trans_le
    (terminalRayleigh_le_top a b g u m n (by omega))

def spectralGap (d a b g u : ℝ) : ℝ :=
  (MetricCodes.Johnson.spectralLimit a b g u -
    MetricCodes.Johnson.asymptoticThreshold d a) / 4

theorem spectralGap_pos
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.Feasible d a b g u) :
    0 < spectralGap d a b g u := by
  have hgap :
      MetricCodes.Johnson.asymptoticThreshold d a <
        MetricCodes.Johnson.spectralLimit a b g u := h.2
  unfold spectralGap
  linarith

theorem eventually_spectralGap_lt
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.Feasible d a b g u) :
    ∀ᶠ n : ℕ in atTop,
      spectralGap d a b g u <
        MetricCodes.Johnson.topEigenvalue n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalDegree u n) -
        MetricCodes.Johnson.threshold n (shellWeight a n)
          (Nat.ceil (d * (n : ℝ))) := by
  have hpositive := spectralGap_pos h
  let A := MetricCodes.Johnson.asymptoticThreshold d a
  let S := MetricCodes.Johnson.spectralLimit a b g u
  have hupper : S - spectralGap d a b g u < S := by
    linarith
  have hlower : A < A + spectralGap d a b g u := by
    linarith
  have heigen := eventually_topEigenvalue_gt h.1 hupper
  have hthreshold :=
    (MetricCodes.Johnson.Asymptotics.tendsto_threshold_ceil h.1).eventually
      (gt_mem_nhds hlower)
  filter_upwards [heigen, hthreshold] with n hn ht
  dsimp [A, S] at hn ht
  unfold spectralGap at hpositive hn ht ⊢
  linarith

theorem asymptoticThreshold_lt_one
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    MetricCodes.Johnson.asymptoticThreshold d a < 1 := by
  unfold MetricCodes.Johnson.asymptoticThreshold
  have hden : 0 < 2 * a * (1 - a) := by
    exact mul_pos (mul_pos (by norm_num) h.weight_pos)
      h.weight_complement_pos
  have hquot := div_pos h.distance_pos hden
  linarith

theorem eventually_one_sub_threshold_lt
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    ∀ᶠ n : ℕ in atTop,
      1 - MetricCodes.Johnson.threshold n (shellWeight a n)
        (Nat.ceil (d * (n : ℝ))) <
        2 - MetricCodes.Johnson.asymptoticThreshold d a := by
  have hlimit :
      MetricCodes.Johnson.asymptoticThreshold d a - 1 <
        MetricCodes.Johnson.asymptoticThreshold d a := by linarith
  have hthreshold :=
    (MetricCodes.Johnson.Asymptotics.tendsto_threshold_ceil h).eventually
      (Ioi_mem_nhds hlimit)
  filter_upwards [hthreshold] with n hn
  linarith

end MetricCodes.Johnson.SpectralAsymptotics

end

end

section

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped Topology

namespace MetricCodes.Johnson.Rate

open MetricCodes.Johnson.Asymptotics
open MetricCodes.Johnson.SpectralAsymptotics

def certificateConstant (d a b g u : ℝ) : ℝ :=
  (2 - MetricCodes.Johnson.asymptoticThreshold d a) /
    spectralGap d a b g u

theorem certificateConstant_pos
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.Feasible d a b g u) :
    0 < certificateConstant d a b g u := by
  unfold certificateConstant
  apply div_pos
  · linarith [asymptoticThreshold_lt_one h.1]
  · exact spectralGap_pos h

theorem exists_zero_fibre_feasible
    {d : ℝ} (hd : 0 < d) (hdhalf : d < (1 : ℝ) / 2) :
    ∃ a u : ℝ, MetricCodes.Johnson.Feasible d a 0 0 u := by
  let a : ℝ := d / 2 + 1 / 4
  let u : ℝ := d / 4 + 1 / 4
  have ha : a < (1 : ℝ) / 2 := by
    dsimp [a]
    linarith
  have hu : 0 < u := by
    dsimp [u]
    linarith
  have hua : u < a := by
    dsimp [a, u]
    linarith
  have ha0 : 0 < a := lt_trans hu hua
  have hac : 0 < 1 - a := by linarith
  have hparams : MetricCodes.Johnson.AsymptoticParameters d a 0 0 u := by
    refine ⟨hd, hdhalf, ?_, ha, by norm_num, ?_, by norm_num,
      ?_, ?_, hua, ?_, ?_⟩
    · dsimp [a]
      linarith
    · linarith
    · linarith
    · simpa using hu
    · simpa using hua
    · norm_num
      linarith
  let A := a * (1 - a)
  let U := u * (1 - u)
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos ha0 hac
  have hs : 0 ≤ Real.sqrt U := Real.sqrt_nonneg _
  have hsden : 0 < 1 + 2 * Real.sqrt U := by positivity
  have hdiff : 2 * (A - U) < d := by
    dsimp [A, U, a, u]
    nlinarith [sq_nonneg d]
  have hinner : (A - U) / (1 + 2 * Real.sqrt U) < d / 2 := by
    apply (div_lt_iff₀ hsden).mpr
    nlinarith [mul_nonneg hd.le hs]
  have hquot :
      (A - U) / (A * (1 + 2 * Real.sqrt U)) < d / (2 * A) := by
    calc
      (A - U) / (A * (1 + 2 * Real.sqrt U)) =
          ((A - U) / (1 + 2 * Real.sqrt U)) / A := by
            field_simp [hA.ne', hsden.ne']

      _ < (d / 2) / A :=
        (div_lt_div_iff_of_pos_right hA).mpr hinner
      _ = d / (2 * A) := by ring_nf
  have hboundary :=
    MetricCodes.Johnson.spectralLimit_zero_fibre_boundary hu hua ha
  refine ⟨a, u, hparams, ?_⟩
  change MetricCodes.Johnson.asymptoticThreshold d a <
    MetricCodes.Johnson.spectralLimit a 0 0 u
  unfold MetricCodes.Johnson.asymptoticThreshold
  dsimp [A, U] at hquot
  have hquot' :
      (a * (1 - a) - u * (1 - u)) /
          (a * (1 - a) * (1 + 2 * Real.sqrt (u * (1 - u)))) <
        d / (2 * a * (1 - a)) := by
    convert hquot using 1 ; ring
  linarith

theorem rateSet_nonempty_of_interior
    {d : ℝ} (hd : 0 < d) (hdhalf : d < (1 : ℝ) / 2) :
    (MetricCodes.Johnson.rateSet d).Nonempty := by
  obtain ⟨a, u, hfeasible⟩ := exists_zero_fibre_feasible hd hdhalf
  exact ⟨MetricCodes.Johnson.shellRate a 0 0 u,
    a, 0, 0, u, hfeasible, rfl⟩

theorem eventually_strict_weight_half
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    ∀ᶠ n : ℕ in atTop, 2 * shellWeight a n < n := by
  have hw := tendsto_shellWeight_ratio h.weight_pos.le
  have hww := tendsto_add_degree_ratio hw hw
  have hstrict := eventually_degree_lt_of_ratio hww
    tendsto_dimension_ratio (by linarith [h.weight_lt_half])
  filter_upwards [hstrict] with n hn
  omega

theorem binaryRate_le_shellRate_of_projectionGrams
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.Feasible d a b g u)
    (hdata : ∀ᶠ n : ℕ in atTop,
      Nonempty
        (MetricCodes.Johnson.ProjectionGram n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalDegree u n))) :
    MetricCodes.Hamming.binaryRate d ≤ MetricCodes.Johnson.shellRate a b g u := by
  apply MetricCodes.Johnson.Asymptotics.binaryRate_le_shellRate_of_eventually
    h.1 (certificateConstant_pos h)
  filter_upwards [hdata, eventually_admissibleDegrees h.1,
    eventually_spectralGap_lt h,
    eventually_one_sub_threshold_lt h.1,
    eventually_gt_atTop (0 : ℕ)]
    with n hnonempty hadmissible hgap hnumerator hn
  obtain ⟨data⟩ := hnonempty
  let t := MetricCodes.Johnson.threshold n (shellWeight a n)
    (Nat.ceil (d * (n : ℝ)))
  let lam := MetricCodes.Johnson.topEigenvalue n (shellWeight a n)
    (supportDegree b n) (complementDegree g n)
    (terminalDegree u n)
  let G := spectralGap d a b g u
  let B := 2 - MetricCodes.Johnson.asymptoticThreshold d a
  have hd := MetricCodes.Hamming.ceil_distance_pos h.1.distance_pos hn
  have hG : 0 < G := spectralGap_pos h
  have hB : 0 < B := by
    dsimp [B]
    linarith [asymptoticThreshold_lt_one h.1]
  have hden : 0 < lam - t := by
    dsimp [lam, t, G] at hgap ⊢
    linarith [spectralGap_pos h]
  have ht : 0 < 1 - t := by
    dsimp [t]
    exact sub_pos.mpr
      (MetricCodes.Johnson.threshold_lt_one hadmissible.weight_pos
        hadmissible.weight_lt hd)
  have hratio : (1 - t) / (lam - t) ≤ B / G := by
    apply (div_le_div_iff₀ hden hG).mpr
    calc
      (1 - t) * G ≤ B * G := by
        apply mul_le_mul_of_nonneg_right _ hG.le
        exact le_of_lt hnumerator
      _ ≤ B * (lam - t) := by
        apply mul_le_mul_of_nonneg_left _ hB.le
        exact le_of_lt hgap
  have hfactor : 0 ≤ bassalygoFactor a n := by
    unfold bassalygoFactor
    exact div_nonneg (by positivity) (Nat.cast_nonneg _)
  have hwindow : 0 ≤ windowFibreQuotient a b g u n := by
    unfold windowFibreQuotient
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hfinite :=
    MetricCodes.Johnson.finite_binaryCodeNumber_bound_of_projection_gram
      hadmissible hd data (sub_pos.mp hden)
  rw [MetricCodes.Johnson.binaryCodeNumber_eq_hamming] at hfinite
  change
    (MetricCodes.Hamming.codeNumber n
      (Nat.ceil (d * (n : ℝ))) : ℝ) ≤
      bassalygoFactor a n *
        (((1 - t) / (lam - t)) * windowFibreQuotient a b g u n)
    at hfinite
  calc
    (MetricCodes.Hamming.codeNumber n
      (Nat.ceil (d * (n : ℝ))) : ℝ) ≤
        bassalygoFactor a n *
          (((1 - t) / (lam - t)) * windowFibreQuotient a b g u n) :=
      hfinite
    _ ≤ bassalygoFactor a n *
          ((B / G) * windowFibreQuotient a b g u n) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hratio hwindow) hfactor
    _ = certificateConstant d a b g u *
          bassalygoWindowFibreQuotient a b g u n := by
      unfold certificateConstant bassalygoWindowFibreQuotient
      dsimp [B, G]
      ring

theorem binaryRate_le_variationalRate_of_projectionGrams
    {d : ℝ} (hd : 0 < d) (hdhalf : d < (1 : ℝ) / 2)
    (hdata : ∀ a b g u : ℝ,
      MetricCodes.Johnson.Feasible d a b g u →
        ∀ᶠ n : ℕ in atTop,
          Nonempty
            (MetricCodes.Johnson.ProjectionGram n (shellWeight a n)
              (supportDegree b n) (complementDegree g n)
              (terminalDegree u n))) :
    MetricCodes.Hamming.binaryRate d ≤ MetricCodes.Johnson.variationalRate d := by
  apply le_csInf (rateSet_nonempty_of_interior hd hdhalf)
  rintro r ⟨a, b, g, u, hfeasible, rfl⟩
  exact binaryRate_le_shellRate_of_projectionGrams
    hfeasible (hdata a b g u hfeasible)

theorem binaryRate_le_combinedVariationalRate_of_projectionGrams
    {d : ℝ} (hd : 0 < d) (hdhalf : d < (1 : ℝ) / 2)
    (hdata : ∀ a b g u : ℝ,
      MetricCodes.Johnson.Feasible d a b g u →
        ∀ᶠ n : ℕ in atTop,
          Nonempty
            (MetricCodes.Johnson.ProjectionGram n (shellWeight a n)
              (supportDegree b n) (complementDegree g n)
              (terminalDegree u n))) :
    MetricCodes.Hamming.binaryRate d ≤
      MetricCodes.Johnson.combinedVariationalRate d := by
  unfold MetricCodes.Johnson.combinedVariationalRate
  exact le_min
    (MetricCodes.Hamming.binaryRate_le_variationalRate hd hdhalf)
    (binaryRate_le_variationalRate_of_projectionGrams hd hdhalf hdata)

end MetricCodes.Johnson.Rate

end

end

section

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped Topology

namespace MetricCodes.Johnson

open MetricCodes.Johnson.Asymptotics

theorem eventually_projectionGram
    {d a b g u : ℝ}
    (h : Feasible d a b g u) :
    ∀ᶠ n : ℕ in atTop,
      Nonempty
        (ProjectionGram n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalDegree u n)) := by
  filter_upwards [eventually_admissibleDegrees h.1,
    MetricCodes.Johnson.Rate.eventually_strict_weight_half h.1,
    MetricCodes.Johnson.SpectralAsymptotics.eventually_terminal_block_fit h.1 0]
    with n hadmissible hstrict hfit
  refine ⟨johnsonProjectionGram hadmissible hstrict ?_⟩
  omega

theorem binaryRate_le_combinedVariationalRate
    {d : ℝ} (hd : 0 < d) (hdhalf : d < (1 : ℝ) / 2) :
    MetricCodes.Hamming.binaryRate d ≤ combinedVariationalRate d := by
  apply
    MetricCodes.Johnson.Rate.binaryRate_le_combinedVariationalRate_of_projectionGrams
      hd hdhalf
  intro a b g u hfeasible
  exact eventually_projectionGram hfeasible

theorem binaryRate_lt_mrrw
    {d : ℝ} (hd : 0 < d) (hdhalf : d < (1 : ℝ) / 2) :
    MetricCodes.Hamming.binaryRate d < mrrwRate d := by
  exact (binaryRate_le_combinedVariationalRate hd hdhalf).trans_lt
    (MetricCodes.MRRW.strict_mrrw2 hd hdhalf)

theorem exists_binaryRate_mrrw_improvement
    {d : ℝ} (hd : 0 < d) (hdhalf : d < (1 : ℝ) / 2) :
    ∃ e : ℝ, 0 < e ∧ MetricCodes.Hamming.binaryRate d ≤ mrrwRate d - e := by
  refine ⟨mrrwRate d - combinedVariationalRate d, ?_, ?_⟩
  · exact sub_pos.mpr (MetricCodes.MRRW.strict_mrrw2 hd hdhalf)
  · linarith [binaryRate_le_combinedVariationalRate hd hdhalf]

end MetricCodes.Johnson

end

end

section

noncomputable section

open scoped BigOperators

namespace MetricCodes.Numerics

def kissingA : ℝ := 0.08570143806746

def kissingB : ℝ := 0.00370282933568

def packingS : ℝ := 0.54006161647549

def packingA : ℝ := 0.1056494058266

def packingB : ℝ := 0.00499524660254

theorem kissing_witness_domain : 0 < kissingB ∧ kissingB < kissingA := by
  constructor <;> norm_num [kissingA, kissingB]

theorem packing_witness_domain :
    0 < packingS ∧ packingS < 1 ∧ 0 < packingB ∧ packingB < packingA := by
  norm_num [packingS, packingA, packingB]

def logSeriesLower (x : ℝ) (m : ℕ) : ℝ :=
  2 * ∑ i ∈ Finset.range m, x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)

def logSeriesUpper (x : ℝ) (m : ℕ) : ℝ :=
  logSeriesLower x m + 2 * (x ^ (2 * m + 1) / (1 - x ^ 2))

theorem log_ratio_lower {x : ℝ} (hx : 0 ≤ x) (hx' : x < 1) (m : ℕ) :
    logSeriesLower x m ≤ Real.log ((1 + x) / (1 - x)) := by
  have h := Real.sum_range_le_log_div hx hx' m
  unfold logSeriesLower
  nlinarith

theorem log_ratio_upper {x : ℝ} (hx : 0 ≤ x) (hx' : x < 1) (m : ℕ) :
    Real.log ((1 + x) / (1 - x)) ≤ logSeriesUpper x m := by
  have h := Real.log_div_le_sum_range_add hx hx' m
  unfold logSeriesUpper logSeriesLower
  nlinarith

theorem log_interval_of_series {r x lo hi : ℝ} (m : ℕ)
    (hx : 0 ≤ x) (hx' : x < 1)
    (hr : (1 + x) / (1 - x) = r)
    (hlo : lo < logSeriesLower x m)
    (hhi : logSeriesUpper x m < hi) :
    lo < Real.log r ∧ Real.log r < hi := by
  constructor
  · calc
      lo < logSeriesLower x m := hlo
      _ ≤ Real.log ((1 + x) / (1 - x)) := log_ratio_lower hx hx' m
      _ = Real.log r := by rw [hr]
  · calc
      Real.log r = Real.log ((1 + x) / (1 - x)) := by rw [hr]
      _ ≤ logSeriesUpper x m := log_ratio_upper hx hx' m
      _ < hi := hhi

theorem log_two_interval :
    (693147180559945309 : ℝ) / 10 ^ 18 < Real.log 2 ∧
      Real.log 2 < (693147180559945310 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series (x := (1 : ℝ) / 3) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]

theorem log_kissing_one_add_a_interval :
    (82226264808038924 : ℝ) / 10 ^ 18 < Real.log (1 + kissingA) ∧
      Real.log (1 + kissingA) < (82226264808038925 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (4285071903373 : ℝ) / 104285071903373) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [kissingA]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]

theorem log_kissing_scaled_a_interval :
    (315703048970999865 : ℝ) / 10 ^ 18 < Real.log (16 * kissingA) ∧
      Real.log (16 * kissingA) < (315703048970999866 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (1160071903373 : ℝ) / 7410071903373) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [kissingA]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]

theorem log_kissing_one_add_b_interval :
    (3695990739373266 : ℝ) / 10 ^ 18 < Real.log (1 + kissingB) ∧
      Real.log (1 + kissingB) < (3695990739373267 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (5785670837 : ℝ) / 3130785670837) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [kissingB]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]

theorem log_kissing_inverse_scaled_b_interval :
    (53480621756332520 : ℝ) / 10 ^ 18 <
        Real.log (1 / (256 * kissingB)) ∧
      Real.log (1 / (256 * kissingB)) <
        (53480621756332521 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (158922394 : ℝ) / 5944593231) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [kissingB]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]

theorem log_packing_one_add_a_interval :
    (100432859923757990 : ℝ) / 10 ^ 18 < Real.log (1 + packingA) ∧
      Real.log (1 + packingA) < (100432859923757991 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (528247029133 : ℝ) / 10528247029133) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [packingA]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]

theorem log_packing_inverse_scaled_a_interval :
    (168187617235226574 : ℝ) / 10 ^ 18 <
        Real.log (1 / (8 * packingA)) ∧
      Real.log (1 / (8 * packingA)) <
        (168187617235226575 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (96752970867 : ℝ) / 1153247029133) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [packingA]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]

theorem log_packing_one_add_b_interval :
    (4982811751137358 : ℝ) / 10 ^ 18 < Real.log (1 + packingB) ∧
      Real.log (1 + packingB) < (4982811751137359 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (249762330127 : ℝ) / 100249762330127) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [packingB]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]

theorem log_packing_scaled_b_interval :
    (245908946257167831 : ℝ) / 10 ^ 18 < Real.log (256 * packingB) ∧
      Real.log (256 * packingB) < (245908946257167832 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (54449830127 : ℝ) / 445074830127) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [packingB]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]

theorem log_packing_geometric_interval :
    (83515566770761640 : ℝ) / 10 ^ 18 <
        Real.log (1 / (2 * (1 - packingS))) ∧
      Real.log (1 / (2 * (1 - packingS))) <
        (83515566770761641 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (4006161647549 : ℝ) / 95993838352451) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [packingS]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]

theorem kissing_sqrt_upper :
    Real.sqrt (kissingA * (1 + kissingA)) <
      (30503471040898065 : ℝ) / 10 ^ 17 := by
  apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) <
    (30503471040898065 : ℝ) / 10 ^ 17)).2
  norm_num [kissingA]

theorem packing_sqrt_upper :
    Real.sqrt (packingA * (1 + packingA)) <
      (34177653924474340 : ℝ) / 10 ^ 17 := by
  apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) <
    (34177653924474340 : ℝ) / 10 ^ 17)).2
  norm_num [packingA]

theorem kissing_spectral_certificate :
    (1 : ℝ) / 2 < 2 * MetricCodes.Gamma kissingA kissingB := by
  have hrad : 0 < kissingA * (1 + kissingA) := by
    norm_num [kissingA]
  have hsqrt : 0 < Real.sqrt (kissingA * (1 + kissingA)) :=
    Real.sqrt_pos.2 hrad
  have hden : 0 <
      (1 + 2 * kissingA) * Real.sqrt (kissingA * (1 + kissingA)) :=
    mul_pos (by norm_num [kissingA]) hsqrt
  unfold MetricCodes.Gamma
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hden).2
  have hupper := kissing_sqrt_upper
  norm_num [kissingA, kissingB] at hupper ⊢
  nlinarith

theorem packing_spectral_certificate :
    packingS < 2 * MetricCodes.Gamma packingA packingB := by
  have hrad : 0 < packingA * (1 + packingA) := by
    norm_num [packingA]
  have hsqrt : 0 < Real.sqrt (packingA * (1 + packingA)) :=
    Real.sqrt_pos.2 hrad
  have hden : 0 <
      (1 + 2 * packingA) * Real.sqrt (packingA * (1 + packingA)) :=
    mul_pos (by norm_num [packingA]) hsqrt
  unfold MetricCodes.Gamma
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hden).2
  have hupper := packing_sqrt_upper
  norm_num [packingS, packingA, packingB] at hupper ⊢
  nlinarith

theorem log_kissing_a :
    Real.log kissingA = Real.log (16 * kissingA) - 4 * Real.log 2 := by
  have hmul : Real.log (16 * kissingA) =
      Real.log (16 : ℝ) + Real.log kissingA :=
    Real.log_mul (by norm_num) (by norm_num [kissingA])
  have hpow : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 4 using 1 <;> norm_num
  rw [hpow] at hmul
  linarith

theorem log_kissing_b :
    Real.log kissingB =
      -8 * Real.log 2 - Real.log (1 / (256 * kissingB)) := by
  have hmul : Real.log (256 * kissingB) =
      Real.log (256 : ℝ) + Real.log kissingB :=
    Real.log_mul (by norm_num) (by norm_num [kissingB])
  have hpow : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 8 using 1 <;> norm_num
  have hinv : Real.log (1 / (256 * kissingB)) =
      -Real.log (256 * kissingB) := by
    rw [one_div, Real.log_inv]
  rw [hpow] at hmul
  linarith

theorem log_packing_a :
    Real.log packingA =
      -3 * Real.log 2 - Real.log (1 / (8 * packingA)) := by
  have hmul : Real.log (8 * packingA) =
      Real.log (8 : ℝ) + Real.log packingA :=
    Real.log_mul (by norm_num) (by norm_num [packingA])
  have hpow : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 3 using 1 <;> norm_num
  have hinv : Real.log (1 / (8 * packingA)) =
      -Real.log (8 * packingA) := by
    rw [one_div, Real.log_inv]
  rw [hpow] at hmul
  linarith

theorem log_packing_b :
    Real.log packingB = Real.log (256 * packingB) - 8 * Real.log 2 := by
  have hmul : Real.log (256 * packingB) =
      Real.log (256 : ℝ) + Real.log packingB :=
    Real.log_mul (by norm_num) (by norm_num [packingB])
  have hpow : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 8 using 1 <;> norm_num
  rw [hpow] at hmul
  linarith

theorem log_packing_geometric :
    Real.log (2 / (1 - packingS)) =
      2 * Real.log 2 + Real.log (1 / (2 * (1 - packingS))) := by
  have hpow : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
  calc
    Real.log (2 / (1 - packingS)) =
        Real.log (4 * (1 / (2 * (1 - packingS)))) := by
          congr 1
          norm_num [packingS]
    _ = Real.log (4 : ℝ) +
          Real.log (1 / (2 * (1 - packingS))) := by
            apply Real.log_mul
            · norm_num
            · norm_num [packingS]
    _ = 2 * Real.log 2 +
          Real.log (1 / (2 * (1 - packingS))) := by rw [hpow]

theorem kissing_entropy_certificate :
    MetricCodes.sphericalEntropy kissingA - MetricCodes.sphericalEntropy kissingB <
      (0.397305601680 : ℝ) := by
  have htwo := log_two_interval.1
  have h1a := log_kissing_one_add_a_interval.2
  have hsa := log_kissing_scaled_a_interval.1
  have h1b := log_kissing_one_add_b_interval.1
  have hib := log_kissing_inverse_scaled_b_interval.1
  have hmain :
      (1 + kissingA) * Real.log (1 + kissingA) -
          kissingA * (Real.log (16 * kissingA) - 4 * Real.log 2) -
          ((1 + kissingB) * Real.log (1 + kissingB) -
            kissingB *
              (-8 * Real.log 2 - Real.log (1 / (256 * kissingB)))) <
        (0.397305601680 : ℝ) * Real.log 2 := by
    norm_num [kissingA, kissingB] at htwo h1a hsa h1b hib ⊢
    linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    MetricCodes.sphericalEntropy kissingA - MetricCodes.sphericalEntropy kissingB =
        ((1 + kissingA) * Real.log (1 + kissingA) -
          kissingA * Real.log kissingA -
          ((1 + kissingB) * Real.log (1 + kissingB) -
            kissingB * Real.log kissingB)) / Real.log 2 := by
          unfold MetricCodes.sphericalEntropy Real.logb
          ring
    _ < (0.397305601680 : ℝ) := by
      apply (div_lt_iff₀ hlog).2
      rw [log_kissing_a, log_kissing_b]
      exact hmain

theorem packing_entropy_certificate :
    (0.602872829455 : ℝ) <
      (1 / 2 : ℝ) * Real.logb 2 (2 / (1 - packingS)) -
        MetricCodes.sphericalEntropy packingA + MetricCodes.sphericalEntropy packingB := by
  have htwo := log_two_interval.1
  have hgeo := log_packing_geometric_interval.1
  have h1a := log_packing_one_add_a_interval.2
  have hia := log_packing_inverse_scaled_a_interval.2
  have h1b := log_packing_one_add_b_interval.1
  have hsb := log_packing_scaled_b_interval.2
  have hmain :
      (0.602872829455 : ℝ) * Real.log 2 <
        (1 / 2 : ℝ) *
            (2 * Real.log 2 + Real.log (1 / (2 * (1 - packingS)))) -
          ((1 + packingA) * Real.log (1 + packingA) -
            packingA *
              (-3 * Real.log 2 - Real.log (1 / (8 * packingA)))) +
          ((1 + packingB) * Real.log (1 + packingB) -
            packingB * (Real.log (256 * packingB) - 8 * Real.log 2)) := by
    norm_num [packingS, packingA, packingB]
      at htwo hgeo h1a hia h1b hsb ⊢
    linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (0.602872829455 : ℝ) <
        ((1 / 2 : ℝ) * Real.log (2 / (1 - packingS)) -
          ((1 + packingA) * Real.log (1 + packingA) -
            packingA * Real.log packingA) +
          ((1 + packingB) * Real.log (1 + packingB) -
            packingB * Real.log packingB)) / Real.log 2 := by
            apply (lt_div_iff₀ hlog).2
            rw [log_packing_geometric, log_packing_a, log_packing_b]
            exact hmain
    _ = (1 / 2 : ℝ) * Real.logb 2 (2 / (1 - packingS)) -
        MetricCodes.sphericalEntropy packingA +
          MetricCodes.sphericalEntropy packingB := by
            unfold MetricCodes.sphericalEntropy Real.logb
            ring

end MetricCodes.Numerics

end

end

section

noncomputable section

namespace MetricCodes.Spherical

theorem sphericalEntropy_continuous : Continuous MetricCodes.sphericalEntropy := by
  have hplus :
      Continuous (fun u : ℝ => (1 + u) * Real.log (1 + u)) := by
    simpa [Function.comp_def, Pi.add_apply] using
      (Real.continuous_mul_log.comp
        (continuous_const.add continuous_id :
          Continuous (fun u : ℝ => 1 + u)))
  have hnatural : Continuous
      (fun u : ℝ =>
        ((1 + u) * Real.log (1 + u) - u * Real.log u) /
          Real.log 2) :=
    (hplus.sub Real.continuous_mul_log).div_const (Real.log 2)
  convert hnatural using 1
  funext u
  unfold MetricCodes.sphericalEntropy Real.logb
  ring

theorem hasDerivAt_sphericalEntropy {u : ℝ} (hu : 0 < u) :
    HasDerivAt MetricCodes.sphericalEntropy
      (Real.logb 2 ((1 + u) / u)) u := by
  have hplus :=
    (Real.hasDerivAt_mul_log (by linarith : 1 + u ≠ 0)).comp u
      ((hasDerivAt_const u (1 : ℝ)).add (hasDerivAt_id u))
  have hself := Real.hasDerivAt_mul_log hu.ne'
  have hderiv := (hplus.sub hself).div_const (Real.log 2)
  have hfun : MetricCodes.sphericalEntropy =
      (fun x : ℝ =>
        ((1 + x) * Real.log (1 + x) - x * Real.log x) /
          Real.log 2) := by
    funext x
    unfold MetricCodes.sphericalEntropy Real.logb
    ring
  have hvalue :
      Real.logb 2 ((1 + u) / u) =
        (((Real.log (1 + u) + 1) * (0 + 1) -
          (Real.log u + 1)) / Real.log 2) := by
    unfold Real.logb
    rw [Real.log_div (by linarith : 1 + u ≠ 0) hu.ne']
    ring
  rw [hfun, hvalue]
  simpa only [Function.comp_apply, Pi.sub_apply] using hderiv

theorem sphericalEntropy_strictMono :
    StrictMonoOn MetricCodes.sphericalEntropy (Set.Ici (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    sphericalEntropy_continuous.continuousOn
  intro u hu
  have hu' : 0 < u := by
    simpa only [interior_Ici, Set.mem_Ioi] using hu
  rw [(hasDerivAt_sphericalEntropy hu').deriv]
  apply Real.logb_pos (by norm_num : (1 : ℝ) < 2)
  apply (lt_div_iff₀ hu').2
  linarith

theorem sphericalEntropy_sub_nonneg {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) :
    0 ≤ MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b := by
  have ha : 0 ≤ a := hb.trans hba
  exact sub_nonneg.mpr
    (sphericalEntropy_strictMono.monotoneOn hb ha hba)

def Feasible (s a b : ℝ) : Prop :=
  0 < b ∧ b < a ∧ s < 2 * MetricCodes.Gamma a b

def rateSet (s : ℝ) : Set ℝ :=
  {r | ∃ a b : ℝ, Feasible s a b ∧
    r = MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b}

def variationalRate (s : ℝ) : ℝ := sInf (rateSet s)

theorem rateSet_bddBelow (s : ℝ) : BddBelow (rateSet s) := by
  refine ⟨0, ?_⟩
  rintro r ⟨a, b, ⟨hb, hba, _⟩, rfl⟩
  exact sphericalEntropy_sub_nonneg hb.le hba.le

theorem variationalRate_le_of_feasible {s a b : ℝ}
    (h : Feasible s a b) :
    variationalRate s ≤
      MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b := by
  exact csInf_le (rateSet_bddBelow s) ⟨a, b, h, rfl⟩

theorem kissing_witness_feasible :
    Feasible ((1 : ℝ) / 2)
      MetricCodes.Numerics.kissingA MetricCodes.Numerics.kissingB := by
  exact ⟨MetricCodes.Numerics.kissing_witness_domain.1,
    MetricCodes.Numerics.kissing_witness_domain.2,
    MetricCodes.Numerics.kissing_spectral_certificate⟩

theorem kissing_variationalRate_lt :
    variationalRate ((1 : ℝ) / 2) < (0.397305601680 : ℝ) := by
  exact lt_of_le_of_lt
    (variationalRate_le_of_feasible kissing_witness_feasible)
    MetricCodes.Numerics.kissing_entropy_certificate

def packingObjective (s a b : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 (2 / (1 - s)) -
    MetricCodes.sphericalEntropy a + MetricCodes.sphericalEntropy b

def packingExponentSet : Set EReal :=
  {r | ∃ s a b : ℝ, 0 < s ∧ s < 1 ∧ Feasible s a b ∧
    r = (packingObjective s a b : EReal)}

def packingExponent : EReal := sSup packingExponentSet

theorem packingObjective_le_packingExponent {s a b : ℝ}
    (hs : 0 < s) (hs' : s < 1) (hf : Feasible s a b) :
    (packingObjective s a b : EReal) ≤ packingExponent := by
  exact le_sSup ⟨s, a, b, hs, hs', hf, rfl⟩

theorem packing_witness_feasible :
    Feasible MetricCodes.Numerics.packingS
      MetricCodes.Numerics.packingA MetricCodes.Numerics.packingB := by
  exact ⟨MetricCodes.Numerics.packing_witness_domain.2.2.1,
    MetricCodes.Numerics.packing_witness_domain.2.2.2,
    MetricCodes.Numerics.packing_spectral_certificate⟩

theorem packingExponent_gt :
    ((0.602872829455 : ℝ) : EReal) < packingExponent := by
  calc
    ((0.602872829455 : ℝ) : EReal) <
        (packingObjective MetricCodes.Numerics.packingS
          MetricCodes.Numerics.packingA MetricCodes.Numerics.packingB : EReal) := by
            apply EReal.coe_lt_coe
            exact MetricCodes.Numerics.packing_entropy_certificate
    _ ≤ packingExponent :=
      packingObjective_le_packingExponent
        MetricCodes.Numerics.packing_witness_domain.1
        MetricCodes.Numerics.packing_witness_domain.2.1
        packing_witness_feasible

end MetricCodes.Spherical

end

end

section

noncomputable section

open Filter Topology
open scoped Topology

namespace MetricCodes.Spherical

theorem Gamma_zero {a : ℝ} (ha : 0 < a) :
    MetricCodes.Gamma a 0 =
      Real.sqrt (a * (1 + a)) / (1 + 2 * a) := by
  have hrad : 0 < a * (1 + a) := by positivity
  have hroot : Real.sqrt (a * (1 + a)) ≠ 0 :=
    (Real.sqrt_pos.2 hrad).ne'
  have hlin : 1 + 2 * a ≠ 0 := by positivity
  have hsquare := Real.sq_sqrt hrad.le
  rw [MetricCodes.Gamma_eq_sub]
  simp only [zero_mul, add_zero, sub_zero]
  field_simp [hroot, hlin]
  nlinarith

theorem classicalThreshold_spectral
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    2 * MetricCodes.Gamma (MetricCodes.classicalThreshold s) 0 = s := by
  have ha : 0 < MetricCodes.classicalThreshold s :=
    MetricCodes.classicalThreshold_pos hs hs'
  have hrad : 0 < 1 - s ^ 2 := by nlinarith
  have hroot : 0 < Real.sqrt (1 - s ^ 2) :=
    Real.sqrt_pos.2 hrad
  have hrootsq := Real.sq_sqrt hrad.le
  have hidentity :
      4 * MetricCodes.classicalThreshold s *
          (1 + MetricCodes.classicalThreshold s) =
        s ^ 2 * (1 + 2 * MetricCodes.classicalThreshold s) ^ 2 := by
    unfold MetricCodes.classicalThreshold
    field_simp [hroot.ne']
    nlinarith
  have hinner :
      0 < MetricCodes.classicalThreshold s *
        (1 + MetricCodes.classicalThreshold s) := by positivity
  have hinnersq := Real.sq_sqrt hinner.le
  have hlin : 0 < 1 + 2 * MetricCodes.classicalThreshold s := by positivity
  have htarget :
      2 * Real.sqrt
        (MetricCodes.classicalThreshold s *
          (1 + MetricCodes.classicalThreshold s)) =
        s * (1 + 2 * MetricCodes.classicalThreshold s) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    calc
      (2 * Real.sqrt
        (MetricCodes.classicalThreshold s *
          (1 + MetricCodes.classicalThreshold s))) ^ 2 =
          4 * MetricCodes.classicalThreshold s *
            (1 + MetricCodes.classicalThreshold s) := by
            rw [mul_pow, hinnersq]
            ring
      _ = s ^ 2 * (1 + 2 * MetricCodes.classicalThreshold s) ^ 2 :=
        hidentity
      _ = (s * (1 + 2 * MetricCodes.classicalThreshold s)) ^ 2 := by
        ring
  rw [Gamma_zero ha, ← mul_div_assoc]
  exact (div_eq_iff hlin.ne').2 htarget

def sphericalImprovementSlope (a : ℝ) : ℝ := 4 * a + 3

def sphericalImprovementPath (a b : ℝ) : ℝ :=
  a + sphericalImprovementSlope a * b

theorem sphericalImprovementSlope_gt_one {a : ℝ} (ha : 0 < a) :
    1 < sphericalImprovementSlope a := by
  unfold sphericalImprovementSlope
  linarith

def sphericalSpectralMarginPolynomial (a c b : ℝ) : ℝ :=
  let T := a * (1 + a)
  let l := 1 + 2 * a
  let p := c * l - 1
  let q := c ^ 2 - 1
  l ^ 2 *
      (T * (2 * p - c * l) +
        b * (p ^ 2 + 2 * T * q - T * c ^ 2) +
        2 * b ^ 2 * p * q + b ^ 3 * q ^ 2) -
    T * (4 * c * l + 4 * c ^ 2 * b) *
      (T + c * l * b + c ^ 2 * b ^ 2)

theorem sphericalSpectralMarginPolynomial_factor (a c b : ℝ) :
    (((a + c * b) * (1 + (a + c * b)) - b * (1 + b)) *
        (1 + 2 * a)) ^ 2 -
      a * (1 + a) * (1 + 2 * (a + c * b)) ^ 2 *
        ((a + c * b) * (1 + (a + c * b))) =
      b * sphericalSpectralMarginPolynomial a c b := by
  unfold sphericalSpectralMarginPolynomial
  ring

theorem sphericalSpectralMarginPolynomial_continuous (a c : ℝ) :
    Continuous (sphericalSpectralMarginPolynomial a c) := by
  unfold sphericalSpectralMarginPolynomial
  fun_prop

theorem sphericalSpectralMarginPolynomial_improvement_zero
    (a : ℝ) :
    sphericalSpectralMarginPolynomial a
      (sphericalImprovementSlope a) 0 =
      a * (1 + a) * (1 + 2 * a) := by
  unfold sphericalSpectralMarginPolynomial sphericalImprovementSlope
  ring

theorem eventually_Gamma_improvement {a : ℝ} (ha : 0 < a) :
    ∀ᶠ b : ℝ in 𝓝[>] 0,
      MetricCodes.Gamma a 0 <
        MetricCodes.Gamma (sphericalImprovementPath a b) b := by
  have hzero :
      0 < sphericalSpectralMarginPolynomial a
        (sphericalImprovementSlope a) 0 := by
    rw [sphericalSpectralMarginPolynomial_improvement_zero]
    positivity
  have hpoly :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        0 < sphericalSpectralMarginPolynomial a
          (sphericalImprovementSlope a) b := by
    have hcontinuous :
        ContinuousAt
          (sphericalSpectralMarginPolynomial a
            (sphericalImprovementSlope a)) 0 :=
      (sphericalSpectralMarginPolynomial_continuous
        a (sphericalImprovementSlope a)).continuousAt
    exact nhdsWithin_le_nhds
      (hcontinuous.tendsto.eventually (lt_mem_nhds hzero))
  have hc : 1 < sphericalImprovementSlope a :=
    sphericalImprovementSlope_gt_one ha
  filter_upwards [hpoly, self_mem_nhdsWithin]
    with b hbpoly (hb : 0 < b)
  have hbpath : b < sphericalImprovementPath a b := by
    unfold sphericalImprovementPath
    nlinarith [mul_pos (sub_pos.mpr hc) hb]
  have hpath : 0 < sphericalImprovementPath a b :=
    hb.trans hbpath
  have hbase : 0 < a * (1 + a) := by positivity
  have hrad :
      0 < sphericalImprovementPath a b *
        (1 + sphericalImprovementPath a b) := by positivity
  have hnum :
      0 < sphericalImprovementPath a b *
          (1 + sphericalImprovementPath a b) - b * (1 + b) := by
    have hfactor :
        0 < (sphericalImprovementPath a b - b) *
          (1 + sphericalImprovementPath a b + b) := by positivity
    nlinarith
  have hmargin :
      0 <
        ((sphericalImprovementPath a b *
          (1 + sphericalImprovementPath a b) - b * (1 + b)) *
          (1 + 2 * a)) ^ 2 -
        a * (1 + a) *
          (1 + 2 * sphericalImprovementPath a b) ^ 2 *
            (sphericalImprovementPath a b *
              (1 + sphericalImprovementPath a b)) := by
    have hfactor := sphericalSpectralMarginPolynomial_factor
      a (sphericalImprovementSlope a) b
    change
      0 < (((a + sphericalImprovementSlope a * b) *
          (1 + (a + sphericalImprovementSlope a * b)) -
            b * (1 + b)) * (1 + 2 * a)) ^ 2 -
        a * (1 + a) *
          (1 + 2 * (a + sphericalImprovementSlope a * b)) ^ 2 *
            ((a + sphericalImprovementSlope a * b) *
              (1 + (a + sphericalImprovementSlope a * b)))
    rw [hfactor]
    exact mul_pos hb hbpoly
  have hleftnonneg :
      0 ≤ Real.sqrt (a * (1 + a)) *
        ((1 + 2 * sphericalImprovementPath a b) *
          Real.sqrt
            (sphericalImprovementPath a b *
              (1 + sphericalImprovementPath a b))) := by
    positivity
  have hrightpos :
      0 < (sphericalImprovementPath a b *
          (1 + sphericalImprovementPath a b) - b * (1 + b)) *
        (1 + 2 * a) := by positivity
  have hsquare :
      (Real.sqrt (a * (1 + a)) *
        ((1 + 2 * sphericalImprovementPath a b) *
          Real.sqrt
            (sphericalImprovementPath a b *
              (1 + sphericalImprovementPath a b)))) ^ 2 =
        a * (1 + a) *
          (1 + 2 * sphericalImprovementPath a b) ^ 2 *
            (sphericalImprovementPath a b *
              (1 + sphericalImprovementPath a b)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hbase.le,
      Real.sq_sqrt hrad.le]
    ring
  have hcross :
      Real.sqrt (a * (1 + a)) *
        ((1 + 2 * sphericalImprovementPath a b) *
          Real.sqrt
            (sphericalImprovementPath a b *
              (1 + sphericalImprovementPath a b))) <
        (sphericalImprovementPath a b *
          (1 + sphericalImprovementPath a b) - b * (1 + b)) *
            (1 + 2 * a) := by
    nlinarith
  rw [Gamma_zero ha, MetricCodes.Gamma_eq_sub]
  have hlin : 0 < 1 + 2 * a := by positivity
  have hden :
      0 < (1 + 2 * sphericalImprovementPath a b) *
        Real.sqrt
          (sphericalImprovementPath a b *
            (1 + sphericalImprovementPath a b)) := by positivity
  exact (div_lt_div_iff₀ hlin hden).2 hcross

theorem neg_mul_logb_le_sphericalEntropy {b : ℝ} (hb : 0 ≤ b) :
    b * (-Real.logb 2 b) ≤ MetricCodes.sphericalEntropy b := by
  have hlog : 0 ≤ Real.logb 2 (1 + b) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hterm : 0 ≤ (1 + b) * Real.logb 2 (1 + b) := by
    exact mul_nonneg (by linarith) hlog
  unfold MetricCodes.sphericalEntropy
  nlinarith

theorem eventually_sphericalEntropy_improvement {a : ℝ} (ha : 0 < a) :
    ∀ᶠ b : ℝ in 𝓝[>] 0,
      MetricCodes.sphericalEntropy (sphericalImprovementPath a b) -
        MetricCodes.sphericalEntropy b < MetricCodes.sphericalEntropy a := by
  let f : ℝ → ℝ := fun b =>
    MetricCodes.sphericalEntropy (sphericalImprovementPath a b)
  have hinner : DifferentiableAt ℝ (sphericalImprovementPath a) 0 := by
    unfold sphericalImprovementPath
    fun_prop
  have houter :
      DifferentiableAt ℝ MetricCodes.sphericalEntropy
        (sphericalImprovementPath a 0) := by
    simpa [sphericalImprovementPath] using
      (hasDerivAt_sphericalEntropy ha).differentiableAt
  have hf : DifferentiableAt ℝ f 0 :=
    houter.comp 0 hinner
  let M : ℝ := deriv f 0 + 1
  have hM : deriv f 0 < M := by
    dsimp [M]
    linarith
  have hslope := hf.hasDerivAt.tendsto_slope_zero_right
  have hupper :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        b⁻¹ * (MetricCodes.sphericalEntropy
          (sphericalImprovementPath a b) -
            MetricCodes.sphericalEntropy a) < M := by
    have h := hslope.eventually (gt_mem_nhds hM)
    filter_upwards [h] with b hb
    simpa [f, sphericalImprovementPath, smul_eq_mul] using hb
  have hloglim :
      Tendsto (fun b : ℝ => -Real.logb 2 b) (𝓝[>] 0) atTop := by
    simpa [Function.comp_def] using
      tendsto_neg_atBot_atTop.comp
        (Real.tendsto_logb_nhdsGT_zero (by norm_num : (1 : ℝ) < 2))
  have hlog :
      ∀ᶠ b : ℝ in 𝓝[>] 0, M < -Real.logb 2 b :=
    hloglim.eventually (eventually_gt_atTop M)
  filter_upwards [hupper, hlog, self_mem_nhdsWithin]
    with b hbound hlogb (hb : 0 < b)
  have houter_bound :
      MetricCodes.sphericalEntropy (sphericalImprovementPath a b) -
        MetricCodes.sphericalEntropy a < b * M := by
    calc
      MetricCodes.sphericalEntropy (sphericalImprovementPath a b) -
          MetricCodes.sphericalEntropy a =
        b * (b⁻¹ *
          (MetricCodes.sphericalEntropy (sphericalImprovementPath a b) -
            MetricCodes.sphericalEntropy a)) := by
          field_simp [hb.ne']
      _ < b * M := mul_lt_mul_of_pos_left hbound hb
  have hsingular :
      b * M < b * (-Real.logb 2 b) :=
    mul_lt_mul_of_pos_left hlogb hb
  have hentropy := neg_mul_logb_le_sphericalEntropy hb.le
  linarith

theorem exists_strict_improving_spherical_feasible
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    ∃ a b : ℝ, Feasible s a b ∧
      MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b <
        MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) := by
  let a₀ : ℝ := MetricCodes.classicalThreshold s
  have ha₀ : 0 < a₀ := MetricCodes.classicalThreshold_pos hs hs'
  have hgamma := eventually_Gamma_improvement ha₀
  have hentropy := eventually_sphericalEntropy_improvement ha₀
  have hc : 1 < sphericalImprovementSlope a₀ :=
    sphericalImprovementSlope_gt_one ha₀
  have hall :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        Feasible s (sphericalImprovementPath a₀ b) b ∧
          MetricCodes.sphericalEntropy (sphericalImprovementPath a₀ b) -
            MetricCodes.sphericalEntropy b <
              MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) := by
    filter_upwards [hgamma, hentropy, self_mem_nhdsWithin]
      with b hgamma' hentropy' (hb : 0 < b)
    have hbpath : b < sphericalImprovementPath a₀ b := by
      unfold sphericalImprovementPath
      nlinarith [mul_pos (sub_pos.mpr hc) hb]
    constructor
    · refine ⟨hb, hbpath, ?_⟩
      have hboundary : 2 * MetricCodes.Gamma a₀ 0 = s := by
        dsimp [a₀]
        exact classicalThreshold_spectral hs hs'
      nlinarith
    · simpa [a₀] using hentropy'
  obtain ⟨b, hb⟩ := hall.exists
  exact ⟨sphericalImprovementPath a₀ b, b, hb⟩

end MetricCodes.Spherical

end

end

section

noncomputable section

open Filter MeasureTheory Metric
open scoped ENNReal Pointwise

namespace SpherePacking

def UnitPacking.toGeneralPacking {n : ℕ} (P : UnitPacking n) :
    _root_.SpherePacking n where
  centers := P.centers
  separation := 2
  separation_pos := by norm_num
  centers_dist := by
    intro x y hxy
    apply P.separation x.property y.property
    exact fun h => hxy (Subtype.ext h)

theorem UnitPacking.covered_eq_toGeneralPacking_balls {n : ℕ}
    (P : UnitPacking n) :
    covered P = P.toGeneralPacking.occupiedBallRegion := by
  ext x
  simp [covered, _root_.SpherePacking.occupiedBallRegion, UnitPacking.toGeneralPacking]

theorem UnitPacking.toGeneralPacking_finiteDensity {n : ℕ}
    (P : UnitPacking n) (R : ℝ) :
    P.toGeneralPacking.densityInsideRadius R = unitFiniteDensity P R := by
  rw [_root_.SpherePacking.densityInsideRadius, unitFiniteDensity,
    ← P.covered_eq_toGeneralPacking_balls]

theorem UnitPacking.toGeneralPacking_density {n : ℕ} (P : UnitPacking n) :
    P.toGeneralPacking.upperPackingDensity = upperDensity P := by
  unfold _root_.SpherePacking.upperPackingDensity upperDensity
  congr 1
  funext R
  exact P.toGeneralPacking_finiteDensity R

def UnitPacking.ofGeneralPacking {n : ℕ} (S : _root_.SpherePacking n) :
    UnitPacking n := by
  let T : _root_.SpherePacking n :=
    S.rescaleConfiguration (c := 2 / S.separation)
      (div_pos (by norm_num : (0 : ℝ) < 2) S.separation_pos)
  refine { centers := T.centers, separation := ?_ }
  intro x hx y hy hxy
  have hxy' := T.distinct_centers_separation_bound x y hx hy hxy
  have htwo : T.separation = 2 := by
    dsimp [T, _root_.SpherePacking.rescaleConfiguration]
    exact div_mul_cancel₀ 2 S.separation_pos.ne'
  simpa [htwo] using hxy'

theorem UnitPacking.toGeneralPacking_ofGeneralPacking {n : ℕ}
    (S : _root_.SpherePacking n) :
    (UnitPacking.ofGeneralPacking S).toGeneralPacking =
      S.rescaleConfiguration (c := 2 / S.separation)
        (div_pos (by norm_num : (0 : ℝ) < 2) S.separation_pos) := by
  dsimp [UnitPacking.ofGeneralPacking, UnitPacking.toGeneralPacking,
    _root_.SpherePacking.rescaleConfiguration]
  simp only [div_mul_cancel₀ 2 S.separation_pos.ne']

theorem UnitPacking.ofGeneralPacking_upperDensity {n : ℕ}
    (S : _root_.SpherePacking n) :
    upperDensity (UnitPacking.ofGeneralPacking S) = S.upperPackingDensity := by
  rw [← UnitPacking.toGeneralPacking_density,
    UnitPacking.toGeneralPacking_ofGeneralPacking,
    _root_.SpherePacking.rescale_upper_packing_density]

theorem packingConstant_eq_SpherePackingConstant (n : ℕ) :
    packingConstant n = _root_.SpherePackingConstant n := by
  unfold packingConstant _root_.SpherePackingConstant
  apply le_antisymm
  · refine iSup_le fun P => ?_
    rw [← P.toGeneralPacking_density]
    exact le_iSup (fun S : _root_.SpherePacking n => S.upperPackingDensity)
      P.toGeneralPacking
  · refine iSup_le fun S => ?_
    rw [← UnitPacking.ofGeneralPacking_upperDensity S]
    exact le_iSup (fun P : UnitPacking n => upperDensity P)
      (UnitPacking.ofGeneralPacking S)

theorem packingConstant_le_radial_linear_program {n : ℕ} (hn : 0 < n) :
    packingConstant n ≤ ENNReal.ofReal (CohnElkies.linearProgram n) := by
  rw [packingConstant_eq_SpherePackingConstant]
  exact PackingBounds.PackingBridge.sphere_packing_le_radial_linear_program_ennreal hn

theorem packingConstant_sharp_binary_asymptotic_upper :
    ∃ e : ℕ → ℝ,
      Tendsto e atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        packingConstant n ≤
          ENNReal.ofReal
            ((2 : ℝ) ^
              (-(CohnElkies.criticalBinaryExponent + e n) * (n : ℝ))) := by
  obtain ⟨e, he, hformula⟩ := CohnElkies.exists_manuscriptBinaryIsLittleO
  refine ⟨e, (Asymptotics.isLittleO_one_iff ℝ).mp he, ?_⟩
  filter_upwards [hformula, eventually_gt_atTop (0 : ℕ)] with n hformula' hn
  rw [← hformula']
  exact packingConstant_le_radial_linear_program hn

end SpherePacking

end

end

section

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped Topology

namespace MetricCodes.Spherical

def classicalPackingObjective (s : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 (2 / (1 - s)) -
    MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s)

def classicalPackingExponent : EReal :=
  sSup {r : EReal | ∃ s : ℝ, 0 < s ∧ s < 1 ∧
    r = (classicalPackingObjective s : EReal)}

theorem classicalPackingObjective_lt_packingExponent
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (classicalPackingObjective s : EReal) < packingExponent := by
  obtain ⟨a, b, hfeasible, himprove⟩ :=
    exists_strict_improving_spherical_feasible hs hs'
  calc
    (classicalPackingObjective s : EReal) <
        (packingObjective s a b : EReal) := by
          apply EReal.coe_lt_coe
          unfold classicalPackingObjective packingObjective
          linarith
    _ ≤ packingExponent :=
      packingObjective_le_packingExponent hs hs' hfeasible

theorem classicalPackingExponent_lt_packingExponent_of_maximizer
    {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hmax : ∀ t : ℝ, 0 < t → t < 1 →
      classicalPackingObjective t ≤ classicalPackingObjective s) :
    classicalPackingExponent < packingExponent := by
  have heq : classicalPackingExponent =
      (classicalPackingObjective s : EReal) := by
    apply le_antisymm
    · unfold classicalPackingExponent
      apply sSup_le
      rintro r ⟨t, ht, ht', rfl⟩
      exact EReal.coe_le_coe_iff.mpr (hmax t ht ht')
    · unfold classicalPackingExponent
      exact le_sSup ⟨s, hs, hs', rfl⟩
  rw [heq]
  exact classicalPackingObjective_lt_packingExponent hs hs'

end MetricCodes.Spherical

end

end

section

noncomputable section

open Filter Topology
open scoped Topology

namespace MetricCodes.Spherical

theorem classicalThreshold_continuousAt
    {s : ℝ} (hs : -1 < s) (hs' : s < 1) :
    ContinuousAt MetricCodes.classicalThreshold s := by
  have hrad : 0 < 1 - s ^ 2 := by nlinarith
  have hroot : Real.sqrt (1 - s ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr hrad).ne'
  unfold MetricCodes.classicalThreshold
  fun_prop (disch := aesop)

theorem classicalPackingObjective_continuousAt
    {s : ℝ} (hs : -1 < s) (hs' : s < 1) :
    ContinuousAt classicalPackingObjective s := by
  have hden : (1 : ℝ) - s ≠ 0 := by linarith
  have harg : (2 : ℝ) / (1 - s) ≠ 0 := by positivity
  have hratio : ContinuousAt (fun t : ℝ => 2 / (1 - t)) s :=
    continuousAt_const.div
      (continuousAt_const.sub continuousAt_id) hden
  have hlog : ContinuousAt
      (fun t : ℝ => Real.logb 2 (2 / (1 - t))) s := by
    fun_prop (disch := aesop)
  unfold classicalPackingObjective
  exact ((continuousAt_const.mul hlog).sub
    (sphericalEntropy_continuous.continuousAt.comp
      (classicalThreshold_continuousAt hs hs')))

@[simp] theorem classicalPackingObjective_zero :
    classicalPackingObjective 0 = (1 : ℝ) / 2 := by
  simp [classicalPackingObjective, Real.logb_self_eq_one]

def classicalEndpointUpper (s : ℝ) : ℝ :=
  Real.logb 2
    (2 * Real.sqrt (2 * (1 + s)) /
      (1 + Real.sqrt (1 - s ^ 2))) -
    ((1 - Real.sqrt (1 - s ^ 2)) /
      (1 + Real.sqrt (1 - s ^ 2))) / Real.log 2

theorem classicalEndpointUpper_continuousAt_one :
    ContinuousAt classicalEndpointUpper 1 := by
  unfold classicalEndpointUpper
  have harg :
      (2 * Real.sqrt (2 * (1 + (1 : ℝ))) /
        (1 + Real.sqrt (1 - (1 : ℝ) ^ 2))) ≠ 0 := by norm_num
  have hden : 1 + Real.sqrt (1 - (1 : ℝ) ^ 2) ≠ 0 := by norm_num
  have hu : ContinuousAt
      (fun s : ℝ => Real.sqrt (1 - s ^ 2)) 1 := by fun_prop
  have hv : ContinuousAt
      (fun s : ℝ => Real.sqrt (2 * (1 + s))) 1 := by fun_prop
  have hquot : ContinuousAt
      (fun s : ℝ => 2 * Real.sqrt (2 * (1 + s)) /
        (1 + Real.sqrt (1 - s ^ 2))) 1 :=
    (continuousAt_const.mul hv).div (continuousAt_const.add hu) hden
  have hfraction : ContinuousAt
      (fun s : ℝ => (1 - Real.sqrt (1 - s ^ 2)) /
        (1 + Real.sqrt (1 - s ^ 2))) 1 :=
    (continuousAt_const.sub hu).div (continuousAt_const.add hu) hden
  unfold Real.logb
  exact (hquot.log harg).div_const (Real.log 2) |>.sub
    (hfraction.div_const (Real.log 2))

@[simp] theorem classicalEndpointUpper_one :
    classicalEndpointUpper 1 = 2 - 1 / Real.log 2 := by
  unfold classicalEndpointUpper
  norm_num
  have hfour : Real.logb 2 (4 : ℝ) = 2 := by
    convert Real.logb_pow 2 2 2 using 1
    · norm_num
    · norm_num
  exact hfour

theorem sphericalEntropy_eq_logb_add_mul_logb
    {a : ℝ} (ha : 0 < a) :
    MetricCodes.sphericalEntropy a =
      Real.logb 2 (1 + a) + a * Real.logb 2 ((1 + a) / a) := by
  unfold MetricCodes.sphericalEntropy
  rw [Real.logb_div (by positivity) ha.ne']
  ring

theorem sphericalEntropy_lower_logb_add_fraction
    {a : ℝ} (ha : 0 < a) :
    Real.logb 2 (1 + a) +
        (a / (1 + a)) / Real.log 2 ≤ MetricCodes.sphericalEntropy a := by
  rw [sphericalEntropy_eq_logb_add_mul_logb ha]
  have hlog := Real.one_sub_inv_le_log_of_pos
    (show 0 < (1 + a) / a by positivity)
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold Real.logb
  have hlower :
      a / (1 + a) ≤ a * Real.log ((1 + a) / a) := by
    have haux : a * (1 - ((1 + a) / a)⁻¹) =
        a / (1 + a) := by
      field_simp
      ring
    rw [← haux]
    exact mul_le_mul_of_nonneg_left hlog ha.le
  have hfraction : a / (1 + a) / Real.log 2 ≤
      a * (Real.log ((1 + a) / a) / Real.log 2) := by
    rw [← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hlogtwo).mpr hlower
  linarith

theorem classical_geometric_logarithm_cancellation
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (1 / 2 : ℝ) * Real.logb 2 (2 / (1 - s)) -
        Real.logb 2 (1 + MetricCodes.classicalThreshold s) =
      Real.logb 2
        (2 * Real.sqrt (2 * (1 + s)) /
          (1 + Real.sqrt (1 - s ^ 2))) := by
  let u : ℝ := Real.sqrt (1 - s ^ 2)
  let v : ℝ := Real.sqrt (2 * (1 + s))
  let a : ℝ := MetricCodes.classicalThreshold s
  have hrad : 0 < 1 - s ^ 2 := by nlinarith
  have hu : 0 < u := Real.sqrt_pos.mpr hrad
  have hu_sq : u ^ 2 = 1 - s ^ 2 := Real.sq_sqrt hrad.le
  have hv : 0 < v := Real.sqrt_pos.mpr (by positivity)
  have hv_sq : v ^ 2 = 2 * (1 + s) :=
    Real.sq_sqrt (by positivity)
  have ha : 0 < a := MetricCodes.classicalThreshold_pos hs hs'
  have hplus : 1 + a = (1 + u) / (2 * u) := by
    dsimp [a, u]
    unfold MetricCodes.classicalThreshold
    field_simp
    ring
  have hfactor :
      (2 : ℝ) / (1 - s) =
        (2 * v / (1 + u) * (1 + a)) ^ 2 := by
    rw [hplus]
    field_simp [hu.ne', (by linarith : 1 - s ≠ 0),
      (by positivity : 1 + u ≠ 0)]
    nlinarith [hu_sq, hv_sq]
  have hfirst : 2 * v / (1 + u) ≠ 0 := by positivity
  have hsecond : 1 + a ≠ 0 := by positivity
  change (1 / 2 : ℝ) * Real.logb 2 (2 / (1 - s)) -
    Real.logb 2 (1 + a) = Real.logb 2 (2 * v / (1 + u))
  rw [hfactor, Real.logb_pow,
    Real.logb_mul hfirst hsecond]
  ring

theorem classicalThreshold_fraction_eq
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    MetricCodes.classicalThreshold s / (1 + MetricCodes.classicalThreshold s) =
      (1 - Real.sqrt (1 - s ^ 2)) /
        (1 + Real.sqrt (1 - s ^ 2)) := by
  have hrad : 0 < 1 - s ^ 2 := by nlinarith
  have hroot : 0 < Real.sqrt (1 - s ^ 2) := Real.sqrt_pos.mpr hrad
  unfold MetricCodes.classicalThreshold
  field_simp [hroot.ne',
    (by positivity : 1 + Real.sqrt (1 - s ^ 2) ≠ 0)]
  apply (div_eq_iff (by nlinarith :
    Real.sqrt (1 - s ^ 2) * 2 + (1 - Real.sqrt (1 - s ^ 2)) ≠ 0)).2
  ring

theorem classicalPackingObjective_le_endpointUpper
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    classicalPackingObjective s ≤ classicalEndpointUpper s := by
  have ha := MetricCodes.classicalThreshold_pos hs hs'
  have hentropy := sphericalEntropy_lower_logb_add_fraction ha
  have hcancel := classical_geometric_logarithm_cancellation hs hs'
  have hfraction := classicalThreshold_fraction_eq hs hs'
  unfold classicalPackingObjective classicalEndpointUpper
  rw [← hfraction]
  linarith

theorem log_three_lt_1099_thousandths :
    Real.log 3 < (1099 : ℝ) / 1000 := by
  calc
    Real.log 3 = Real.log
        (((1 : ℝ) + 1 / 2) / (1 - 1 / 2)) := by norm_num
    _ ≤ MetricCodes.Numerics.logSeriesUpper (1 / 2) 10 :=
      MetricCodes.Numerics.log_ratio_upper (by norm_num) (by norm_num) 10
    _ < (1099 : ℝ) / 1000 := by
      norm_num [MetricCodes.Numerics.logSeriesUpper,
        MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]

theorem log_five_gt_1609_thousandths :
    (1609 : ℝ) / 1000 < Real.log 5 := by
  calc
    (1609 : ℝ) / 1000 <
        MetricCodes.Numerics.logSeriesLower (2 / 3) 14 := by
          norm_num [MetricCodes.Numerics.logSeriesLower,
            Finset.sum_range_succ]
    _ ≤ Real.log (((1 : ℝ) + 2 / 3) / (1 - 2 / 3)) :=
      MetricCodes.Numerics.log_ratio_lower (by norm_num) (by norm_num) 14
    _ = Real.log 5 := by norm_num

theorem classicalPackingObjective_three_fifths :
    classicalPackingObjective ((3 : ℝ) / 5) =
      3 + ((1 / 2 : ℝ) * Real.log 5 -
        (9 / 4 : ℝ) * Real.log 3) / Real.log 2 := by
  have hroot :
      Real.sqrt (1 - ((3 : ℝ) / 5) ^ 2) = (4 : ℝ) / 5 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
    norm_num
  have hdegree : MetricCodes.classicalThreshold ((3 : ℝ) / 5) =
      (1 : ℝ) / 8 := by
    unfold MetricCodes.classicalThreshold
    rw [hroot]
    norm_num
  have hthree : Real.logb 2 ((9 : ℝ) / 8) =
      2 * Real.logb 2 3 - 3 := by
    calc
      Real.logb 2 ((9 : ℝ) / 8) =
          Real.logb 2 ((3 : ℝ) ^ 2 / (2 : ℝ) ^ 3) := by norm_num
      _ = Real.logb 2 ((3 : ℝ) ^ 2) -
          Real.logb 2 ((2 : ℝ) ^ 3) := by
            rw [Real.logb_div] <;> norm_num
      _ = 2 * Real.logb 2 3 - 3 := by
            rw [Real.logb_pow, Real.logb_pow,
              Real.logb_self_eq_one (by norm_num)]
            norm_num
  have height : Real.logb 2 ((1 : ℝ) / 8) = -3 := by
    calc
      Real.logb 2 ((1 : ℝ) / 8) =
          Real.logb 2 (((2 : ℝ) ^ 3)⁻¹) := by norm_num
      _ = -Real.logb 2 ((2 : ℝ) ^ 3) := by
            rw [Real.logb_inv]
      _ = -3 := by
            rw [Real.logb_pow,
              Real.logb_self_eq_one (by norm_num)]
            norm_num
  unfold classicalPackingObjective
  rw [hdegree]
  unfold MetricCodes.sphericalEntropy
  norm_num
  rw [hthree, height]
  unfold Real.logb
  ring

theorem classicalPackingObjective_three_fifths_gt :
    (29 : ℝ) / 50 < classicalPackingObjective ((3 : ℝ) / 5) := by
  rw [classicalPackingObjective_three_fifths]
  have htwo := MetricCodes.Numerics.log_two_interval.1
  have hthree := log_three_lt_1099_thousandths
  have hfive := log_five_gt_1609_thousandths
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : (29 : ℝ) / 50 - 3 <
      ((1 / 2 : ℝ) * Real.log 5 - (9 / 4 : ℝ) * Real.log 3) /
        Real.log 2 := by
    apply (lt_div_iff₀ hlogtwo).mpr
    nlinarith [htwo, hthree, hfive]
  linarith

theorem classicalEndpointUpper_one_lt_witness :
    classicalEndpointUpper 1 <
      classicalPackingObjective ((3 : ℝ) / 5) := by
  rw [classicalEndpointUpper_one]
  have htwo := MetricCodes.Numerics.log_two_interval.2
  have hpositive : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hupper : 2 - 1 / Real.log 2 < (29 : ℝ) / 50 := by
    have hinv : (71 : ℝ) / 50 < 1 / Real.log 2 := by
      apply (lt_div_iff₀ hpositive).mpr
      nlinarith [htwo]
    linarith
  exact hupper.trans classicalPackingObjective_three_fifths_gt

theorem exists_classicalPackingObjective_interior_maximizer :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      ∀ t : ℝ, 0 < t → t < 1 →
        classicalPackingObjective t ≤ classicalPackingObjective s := by
  let witness : ℝ := (3 : ℝ) / 5
  have hwitness : 0 < witness ∧ witness < 1 := by
    dsimp [witness]
    constructor <;> norm_num
  have hzero : classicalPackingObjective 0 <
      classicalPackingObjective witness := by
    rw [classicalPackingObjective_zero]
    dsimp [witness]
    nlinarith [classicalPackingObjective_three_fifths_gt]
  have hnearZero :
      {t : ℝ | classicalPackingObjective t <
        classicalPackingObjective witness} ∈ 𝓝 (0 : ℝ) :=
    (classicalPackingObjective_continuousAt
      (by norm_num : (-1 : ℝ) < 0) (by norm_num)).tendsto
        (gt_mem_nhds hzero)
  obtain ⟨l₀, u₀, hinterval₀, hsubset₀⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hnearZero
  have hupper : classicalEndpointUpper 1 <
      classicalPackingObjective witness := by
    simpa [witness] using classicalEndpointUpper_one_lt_witness
  have hnearOne :
      {t : ℝ | classicalEndpointUpper t <
        classicalPackingObjective witness} ∈ 𝓝 (1 : ℝ) :=
    classicalEndpointUpper_continuousAt_one.tendsto
      (gt_mem_nhds hupper)
  obtain ⟨l₁, u₁, hinterval₁, hsubset₁⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hnearOne
  let lo : ℝ := min (u₀ / 2) witness
  let hi : ℝ := max ((l₁ + 1) / 2) witness
  have hlo : 0 < lo := by
    dsimp [lo]
    exact lt_min (by linarith [hinterval₀.2]) hwitness.1
  have hhi : hi < 1 := by
    dsimp [hi]
    exact max_lt (by linarith [hinterval₁.1]) hwitness.2
  have hlowitness : lo ≤ witness := min_le_right _ _
  have hhiwitness : witness ≤ hi := le_max_right _ _
  have hwitmem : witness ∈ Set.Icc lo hi :=
    ⟨hlowitness, hhiwitness⟩
  have hcontinuous : ContinuousOn classicalPackingObjective
      (Set.Icc lo hi) := by
    intro t ht
    exact (classicalPackingObjective_continuousAt
      (by linarith [ht.1, hlo]) (by linarith [ht.2, hhi])).continuousWithinAt
  obtain ⟨s, hs, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨witness, hwitmem⟩ hcontinuous
  refine ⟨s, lt_of_lt_of_le hlo hs.1,
    lt_of_le_of_lt hs.2 hhi, ?_⟩
  intro t ht ht'
  by_cases hbelow : t < lo
  · have hmem : t ∈ Set.Ioo l₀ u₀ := by
      constructor
      · linarith [hinterval₀.1]
      · have hlo₀ : lo ≤ u₀ / 2 := min_le_left _ _
        linarith [hinterval₀.2]
    have hless := hsubset₀ hmem
    exact hless.le.trans (hmax hwitmem)
  · by_cases habove : hi < t
    · have hmem : t ∈ Set.Ioo l₁ u₁ := by
        constructor
        · have hhi₁ : (l₁ + 1) / 2 ≤ hi := le_max_left _ _
          linarith [hinterval₁.1]
        · linarith [hinterval₁.2]
      have hless := hsubset₁ hmem
      exact (classicalPackingObjective_le_endpointUpper ht ht').trans
        (hless.le.trans (hmax hwitmem))
    · exact hmax ⟨le_of_not_gt hbelow, le_of_not_gt habove⟩

theorem classicalPackingExponent_lt_packingExponent :
    classicalPackingExponent < packingExponent := by
  obtain ⟨s, hs, hs', hmax⟩ :=
    exists_classicalPackingObjective_interior_maximizer
  exact classicalPackingExponent_lt_packingExponent_of_maximizer
    hs hs' hmax

end MetricCodes.Spherical

end

section

noncomputable section

open scoped BigOperators

namespace MetricCodes.Spherical.HigherHierarchy

def quadraticCoordinate (u : ℝ) : ℝ := u * (1 + u)

def spectralAtom (u : ℝ) : ℝ :=
  Real.sqrt (quadraticCoordinate u) / (1 + 2 * u)

def Interlacing {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : Prop :=
  0 ≤ a (Fin.last r) ∧
    ∀ i : Fin r, a i.castSucc > b i ∧ b i > a i.succ

def lagrangeNumerator {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (ℓ : Fin (r + 1)) : ℝ :=
  ∏ m : Fin r, (quadraticCoordinate (a ℓ) - quadraticCoordinate (b m))

def lagrangeDenominator {r : ℕ}
    (a : Fin (r + 1) → ℝ) (ℓ : Fin (r + 1)) : ℝ :=
  ∏ m : Fin r,
    (quadraticCoordinate (a ℓ) - quadraticCoordinate (a (ℓ.succAbove m)))

def lagrangeWeight {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (ℓ : Fin (r + 1)) : ℝ :=
  lagrangeNumerator a b ℓ / lagrangeDenominator a ℓ

def Gamma {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : ℝ :=
  ∑ ℓ : Fin (r + 1), lagrangeWeight a b ℓ * spectralAtom (a ℓ)

def Phi {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : ℝ :=
  (∑ ℓ : Fin (r + 1), MetricCodes.sphericalEntropy (a ℓ)) -
    ∑ m : Fin r, MetricCodes.sphericalEntropy (b m)

theorem Interlacing.strictAnti_ambient {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) : StrictAnti a := by
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro i
  exact (h.2 i).2.trans (h.2 i).1

theorem Interlacing.ambient_nonneg {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (i : Fin (r + 1)) : 0 ≤ a i := by
  exact h.1.trans (h.strictAnti_ambient.antitone i.le_last)

theorem Interlacing.stabilizer_pos {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (i : Fin r) : 0 < b i :=
  (h.ambient_nonneg i.succ).trans_lt (h.2 i).2

theorem quadraticCoordinate_strictMonoOn :
    StrictMonoOn quadraticCoordinate (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  dsimp [quadraticCoordinate]
  nlinarith [mul_pos (sub_pos.mpr hxy) (by linarith : 0 < 1 + x + y)]

theorem Interlacing.quadratic_injective {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) :
    Function.Injective (fun i => quadraticCoordinate (a i)) := by
  intro i j hij
  apply h.strictAnti_ambient.injective
  exact quadraticCoordinate_strictMonoOn.injOn
    (h.ambient_nonneg i) (h.ambient_nonneg j) hij

theorem lagrangeDenominator_eq_prod_erase {r : ℕ}
    (a : Fin (r + 1) → ℝ) (ℓ : Fin (r + 1)) :
    lagrangeDenominator a ℓ =
      ∏ j ∈ Finset.univ.erase ℓ,
        (quadraticCoordinate (a ℓ) - quadraticCoordinate (a j)) := by
  unfold lagrangeDenominator
  classical
  refine Finset.prod_bij (fun j _ => ℓ.succAbove j)
    (fun j _ => ?_) (fun i _ j _ hij => ?_) (fun j hj => ?_)
    (fun _ _ => rfl)
  · simp [Fin.succAbove_ne]
  · exact Fin.succAbove_right_injective hij
  · obtain ⟨hj', _⟩ := Finset.mem_erase.mp hj
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hj'
    exact ⟨i, Finset.mem_univ i, hi⟩

theorem Interlacing.lagrangeDenominator_ne_zero {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (ℓ : Fin (r + 1)) :
    lagrangeDenominator a ℓ ≠ 0 := by
  unfold lagrangeDenominator
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact sub_ne_zero.mpr
    (fun heq => Fin.ne_succAbove ℓ i (h.quadratic_injective heq))

theorem Interlacing.lagrangeFactor_pos {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (ℓ : Fin (r + 1)) (m : Fin r) :
    0 < (quadraticCoordinate (a ℓ) - quadraticCoordinate (b m)) /
      (quadraticCoordinate (a ℓ) -
        quadraticCoordinate (a (ℓ.succAbove m))) := by
  by_cases hm : m.castSucc < ℓ
  · rw [Fin.succAbove_of_castSucc_lt ℓ m hm]
    have hmiddle : a ℓ < b m := by
      exact
        (h.strictAnti_ambient.antitone (Fin.castSucc_lt_iff_succ_le.mp hm)).trans_lt
          (h.2 m).2
    have hleft :
        quadraticCoordinate (a ℓ) < quadraticCoordinate (b m) :=
      quadraticCoordinate_strictMonoOn (h.ambient_nonneg ℓ)
        (h.stabilizer_pos m).le hmiddle
    have hright :
        quadraticCoordinate (a ℓ) <
          quadraticCoordinate (a m.castSucc) :=
      quadraticCoordinate_strictMonoOn (h.ambient_nonneg ℓ)
        (h.ambient_nonneg m.castSucc) (h.strictAnti_ambient hm)
    exact div_pos_of_neg_of_neg (sub_neg.mpr hleft) (sub_neg.mpr hright)
  · have hm' : ℓ ≤ m.castSucc := le_of_not_gt hm
    rw [Fin.succAbove_of_le_castSucc ℓ m hm']
    have hmiddle : b m < a ℓ := by
      exact (h.2 m).1.trans_le (h.strictAnti_ambient.antitone hm')
    have hleft :
        quadraticCoordinate (b m) < quadraticCoordinate (a ℓ) :=
      quadraticCoordinate_strictMonoOn (h.stabilizer_pos m).le
        (h.ambient_nonneg ℓ) hmiddle
    have hright :
        quadraticCoordinate (a m.succ) < quadraticCoordinate (a ℓ) :=
      quadraticCoordinate_strictMonoOn (h.ambient_nonneg m.succ)
        (h.ambient_nonneg ℓ)
        (h.strictAnti_ambient (Fin.le_castSucc_iff.mp hm'))
    exact div_pos (sub_pos.mpr hleft) (sub_pos.mpr hright)

theorem Interlacing.lagrangeWeight_pos {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (ℓ : Fin (r + 1)) :
    0 < lagrangeWeight a b ℓ := by
  unfold lagrangeWeight lagrangeNumerator lagrangeDenominator
  rw [← Finset.prod_div_distrib]
  exact Finset.prod_pos fun i _ => h.lagrangeFactor_pos ℓ i

theorem Interlacing.lagrangeWeight_nonneg {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (ℓ : Fin (r + 1)) :
    0 ≤ lagrangeWeight a b ℓ := (h.lagrangeWeight_pos ℓ).le

def stabilizerPolynomial {r : ℕ} (b : Fin r → ℝ) : Polynomial ℝ :=
  ∏ m : Fin r, (Polynomial.X - Polynomial.C (quadraticCoordinate (b m)))

theorem stabilizerPolynomial_monic {r : ℕ} (b : Fin r → ℝ) :
    (stabilizerPolynomial b).Monic := by
  exact Polynomial.monic_prod_X_sub_C
    (fun m : Fin r => quadraticCoordinate (b m)) Finset.univ

theorem stabilizerPolynomial_natDegree {r : ℕ} (b : Fin r → ℝ) :
    (stabilizerPolynomial b).natDegree = r := by
  simp [stabilizerPolynomial,
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card]

theorem stabilizerPolynomial_eval {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (ℓ : Fin (r + 1)) :
    (stabilizerPolynomial b).eval (quadraticCoordinate (a ℓ)) =
      lagrangeNumerator a b ℓ := by
  unfold stabilizerPolynomial lagrangeNumerator
  rw [Polynomial.eval_prod]
  simp

theorem Interlacing.sum_lagrangeWeight {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) :
    (∑ ℓ : Fin (r + 1), lagrangeWeight a b ℓ) = 1 := by
  classical
  let P : Polynomial ℝ := stabilizerPolynomial b
  have hmonic : P.Monic := stabilizerPolynomial_monic b
  have hdegree : P.natDegree = r := stabilizerPolynomial_natDegree b
  have hdegree' :
      P.degree < (Finset.univ : Finset (Fin (r + 1))).card := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdegree]
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    exact_mod_cast Nat.lt_succ_self r
  have hlagrange := Lagrange.coeff_eq_sum
    (s := (Finset.univ : Finset (Fin (r + 1))))
    (v := fun ℓ : Fin (r + 1) => quadraticCoordinate (a ℓ))
    (P := P) h.quadratic_injective.injOn hdegree'
  have hcoeff : P.coeff r = 1 := by
    simpa [hdegree] using hmonic.coeff_natDegree
  rw [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel,
    hcoeff] at hlagrange
  symm
  calc
    1 = ∑ ℓ : Fin (r + 1),
        P.eval (quadraticCoordinate (a ℓ)) /
          ∏ j ∈ Finset.univ.erase ℓ,
            (quadraticCoordinate (a ℓ) - quadraticCoordinate (a j)) := by
          simpa using hlagrange
    _ = ∑ ℓ : Fin (r + 1), lagrangeWeight a b ℓ := by
          apply Finset.sum_congr rfl
          intro ℓ _
          rw [lagrangeWeight, lagrangeDenominator_eq_prod_erase,
            ← stabilizerPolynomial_eval]

theorem spectralAtom_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ spectralAtom u := by
  unfold spectralAtom quadraticCoordinate
  positivity

def hierarchyPackingObjective {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 (2 / (1 - 2 * Gamma a b)) - Phi a b

def hierarchyPackingExponentSet : Set EReal :=
  {z | ∃ (r : ℕ) (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
    Interlacing a b ∧ 0 < Gamma a b ∧
      z = (hierarchyPackingObjective a b : EReal)}

def hierarchyPackingExponent : EReal := sSup hierarchyPackingExponentSet

theorem hierarchyPackingObjective_le_hierarchyPackingExponent {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hpositive : 0 < Gamma a b) :
    (hierarchyPackingObjective a b : EReal) ≤ hierarchyPackingExponent := by
  exact le_sSup ⟨r, a, b, h, hpositive, rfl⟩

theorem hierarchyPackingExponent_le_of_forall {c : ℝ}
    (hupper : ∀ (r : ℕ) (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
      Interlacing a b → 0 < Gamma a b → hierarchyPackingObjective a b ≤ c) :
    hierarchyPackingExponent ≤ (c : EReal) := by
  unfold hierarchyPackingExponent
  apply sSup_le
  rintro _ ⟨r, a, b, h, hpositive, rfl⟩
  exact EReal.coe_le_coe_iff.mpr (hupper r a b h hpositive)

end MetricCodes.Spherical.HigherHierarchy

end

section

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal Interval

namespace MetricCodes.Spherical.HigherHierarchy.Arcsine

theorem beta_half_half_eq_pi :
    beta (1 / 2 : ℝ) (1 / 2 : ℝ) = Real.pi := by
  rw [beta, Real.Gamma_one_half_eq]
  norm_num [Real.Gamma_one]
  simpa [pow_two] using Real.sq_sqrt Real.pi_pos.le

theorem beta_one_half_eq_two :
    beta (1 : ℝ) (1 / 2 : ℝ) = 2 := by
  rw [beta, Real.Gamma_one]
  have hsum : (1 : ℝ) + 1 / 2 = 1 / 2 + 1 := by norm_num
  rw [hsum, Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0),
    Real.Gamma_one_half_eq]
  have hsqrt : Real.sqrt Real.pi ≠ 0 :=
    (Real.sqrt_pos.2 Real.pi_pos).ne'
  field_simp

theorem betaPDFReal_one_half_eq_mul_half_pi_sqrt (t : ℝ) :
    betaPDFReal 1 (1 / 2 : ℝ) t =
      betaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) t *
        (Real.pi / 2 * Real.sqrt t) := by
  by_cases ht : 0 < t ∧ t < 1
  · rw [betaPDFReal, betaPDFReal, if_pos ht, if_pos ht,
      beta_half_half_eq_pi, beta_one_half_eq_two]
    have hsqrt : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht.1).ne'
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hpow : t ^ ((1 / 2 : ℝ) - 1) = (Real.sqrt t)⁻¹ := by
      convert Real.rpow_neg ht.1.le (1 / 2 : ℝ) using 1 <;>
        norm_num [Real.sqrt_eq_rpow]
    rw [hpow]
    norm_num
    field_simp
  · simp [betaPDFReal, ht]

theorem betaPDF_one_half_eq_mul_half_pi_sqrt (t : ℝ) :
    betaPDF 1 (1 / 2 : ℝ) t =
      betaPDF (1 / 2 : ℝ) (1 / 2 : ℝ) t *
        ENNReal.ofReal (Real.pi / 2 * Real.sqrt t) := by
  rw [betaPDF, betaPDF, betaPDFReal_one_half_eq_mul_half_pi_sqrt,
    ENNReal.ofReal_mul' (mul_nonneg (div_nonneg Real.pi_pos.le (by norm_num))
      (Real.sqrt_nonneg t))]

theorem betaMeasure_one_half_eq_withDensity :
    betaMeasure 1 (1 / 2 : ℝ) =
      (betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).withDensity
        (fun t => ENNReal.ofReal (Real.pi / 2 * Real.sqrt t)) := by
  unfold betaMeasure
  have hbeta : Measurable (betaPDF (1 / 2 : ℝ) (1 / 2 : ℝ)) :=
    (measurable_betaPDFReal _ _).ennreal_ofReal
  have hweight :
      Measurable (fun t : ℝ => ENNReal.ofReal (Real.pi / 2 * Real.sqrt t)) := by
    fun_prop
  rw [← withDensity_mul volume hbeta hweight]
  congr 1
  funext t
  exact betaPDF_one_half_eq_mul_half_pi_sqrt t

theorem map_withDensity_comp {μ : Measure ℝ} {f : ℝ → ℝ}
    {w : ℝ → ℝ≥0∞} (hf : Measurable f) (hw : Measurable w) :
    (μ.withDensity (w ∘ f)).map f = (μ.map f).withDensity w := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs),
    withDensity_apply _ hs, ← lintegral_indicator hs,
    lintegral_map (hw.indicator hs) hf]
  rw [← lintegral_indicator (hf hs)]
  apply lintegral_congr
  intro t
  by_cases ht : f t ∈ s <;> simp [Function.comp_apply, ht]

theorem betaMap_one_half_eq_withDensity :
    (betaMeasure 1 (1 / 2 : ℝ)).map (fun t : ℝ => t / 4) =
      ((betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
        (fun t : ℝ => t / 4)).withDensity
        (fun t => ENNReal.ofReal (Real.pi * Real.sqrt t)) := by
  rw [betaMeasure_one_half_eq_withDensity]
  have hcomp :
      (fun t : ℝ => ENNReal.ofReal (Real.pi / 2 * Real.sqrt t)) =
        (fun t => ENNReal.ofReal (Real.pi * Real.sqrt t)) ∘
          (fun t : ℝ => t / 4) := by
    funext t
    congr 1
    change Real.pi / 2 * Real.sqrt t = Real.pi * Real.sqrt (t / 4)
    rw [Real.sqrt_div' t (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
    ring
  rw [hcomp]
  apply map_withDensity_comp
  · fun_prop
  · fun_prop

theorem comparisonDensity_log_intervalIntegral :
    (∫ t in (0 : ℝ)..(1 / 4 : ℝ),
      Real.log t / Real.sqrt (1 / 4 - t)) = -2 := by
  have hsubst := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (f := fun u : ℝ => (1 - u ^ 2) / 4)
    (f' := fun u : ℝ => -u / 2)
    (g := fun t : ℝ => Real.log t / Real.sqrt (1 / 4 - t))
    (by fun_prop)
    (by
      intro u hu
      convert (((hasDerivAt_id u).pow 2).const_sub 1).div_const 4 using 1 <;>
        try rfl
      norm_num [id]
      ring)
    (by
      intro u hu
      norm_num at hu
      linarith [hu.1])
  norm_num at hsubst
  have hleft :
      (∫ u in (0 : ℝ)..1,
        (-u / 2) *
          (Real.log ((1 - u ^ 2) / 4) /
            Real.sqrt (1 / 4 - (1 - u ^ 2) / 4))) =
        ∫ u in (0 : ℝ)..1, -Real.log ((1 - u ^ 2) / 4) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u hu
    change (-u / 2) *
      (Real.log ((1 - u ^ 2) / 4) /
        Real.sqrt (1 / 4 - (1 - u ^ 2) / 4)) =
      -Real.log ((1 - u ^ 2) / 4)
    have hu0 : 0 < u := hu.1
    have hsqrt : Real.sqrt (u ^ 2 / 4) = u / 2 := by
      rw [Real.sqrt_div' (u ^ 2) (by norm_num : (0 : ℝ) ≤ 4),
        Real.sqrt_sq hu0.le]
      norm_num
    have hrad : (1 / 4 : ℝ) - (1 - u ^ 2) / 4 = u ^ 2 / 4 := by ring
    rw [hrad, hsqrt]
    field_simp
  rw [hleft] at hsubst
  have hright :
      (∫ t in (1 / 4 : ℝ)..0,
        Real.log t / Real.sqrt (1 / 4 - t)) =
        -(∫ t in (0 : ℝ)..(1 / 4 : ℝ),
          Real.log t / Real.sqrt (1 / 4 - t)) :=
    intervalIntegral.integral_symm _ _
  rw [hright] at hsubst
  have hsplit :
      (∫ u in (0 : ℝ)..1, Real.log ((1 - u ^ 2) / 4)) = -2 := by
    have hminus :
        IntervalIntegrable (fun u : ℝ => Real.log (1 - u)) volume 0 1 := by
      simpa using
        ((intervalIntegral.intervalIntegrable_log'
          (a := (0 : ℝ)) (b := 1)).comp_sub_left 1).symm
    have hplus :
        IntervalIntegrable (fun u : ℝ => Real.log (1 + u)) volume 0 1 := by
      convert
        (intervalIntegral.intervalIntegrable_log'
          (a := (1 : ℝ)) (b := 2)).comp_add_left 1
        using 1 <;> norm_num
    calc
      (∫ u in (0 : ℝ)..1, Real.log ((1 - u ^ 2) / 4)) =
          ∫ u in (0 : ℝ)..1,
            (Real.log (1 - u) + Real.log (1 + u)) - Real.log 4 := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro u hu
        change Real.log ((1 - u ^ 2) / 4) =
          Real.log (1 - u) + Real.log (1 + u) - Real.log 4
        have hleft : 0 < 1 - u := sub_pos.mpr hu.2
        have hright : 0 < 1 + u := by linarith [hu.1]
        rw [show (1 - u ^ 2) / 4 = ((1 - u) * (1 + u)) / 4 by ring,
          Real.log_div (mul_pos hleft hright).ne' (by norm_num),
          Real.log_mul hleft.ne' hright.ne']
      _ =
          ((∫ u in (0 : ℝ)..1, Real.log (1 - u)) +
            (∫ u in (0 : ℝ)..1, Real.log (1 + u))) -
              (∫ _u in (0 : ℝ)..1, Real.log 4) := by
        rw [intervalIntegral.integral_sub (hminus.add hplus)
          (intervalIntegrable_const :
            IntervalIntegrable (fun _ : ℝ => Real.log 4) volume 0 1),
          intervalIntegral.integral_add hminus hplus]
      _ = -2 := by
        rw [intervalIntegral.integral_comp_sub_left Real.log 1,
          intervalIntegral.integral_comp_add_left Real.log 1,
          integral_log, integral_log]
        norm_num
        rw [show (4 : ℝ) = 2 * 2 by norm_num,
          Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num)]
        ring
  rw [intervalIntegral.integral_neg, hsplit] at hsubst
  linarith

theorem comparisonDensity_logAtom_intervalIntegral
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ t in (0 : ℝ)..(1 / 4 : ℝ),
      Real.log ((t + a * (1 + a)) / t) /
        Real.sqrt (1 / 4 - t)) =
      2 * ((1 + a) * Real.log (1 + a) - a * Real.log a) := by
  by_cases ha0 : a = 0
  · subst a
    have hzero :
        (∫ t in (0 : ℝ)..(1 / 4 : ℝ),
          Real.log ((t + 0 * (1 + 0)) / t) /
            Real.sqrt (1 / 4 - t)) = 0 := by
      calc
        (∫ t in (0 : ℝ)..(1 / 4 : ℝ),
          Real.log ((t + 0 * (1 + 0)) / t) /
            Real.sqrt (1 / 4 - t)) =
            ∫ _t in (0 : ℝ)..(1 / 4 : ℝ), 0 := by
          apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
          intro t ht
          change Real.log ((t + 0 * (1 + 0)) / t) /
            Real.sqrt (1 / 4 - t) = 0
          simp [ht.1.ne']
        _ = 0 := by simp
    simp at hzero ⊢
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  let b : ℝ := 2 * a + 1
  have hb : 1 < b := by dsimp [b]; linarith
  have hsubst := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (f := fun u : ℝ => (1 - u ^ 2) / 4)
    (f' := fun u : ℝ => -u / 2)
    (g := fun t : ℝ =>
      Real.log ((t + a * (1 + a)) / t) / Real.sqrt (1 / 4 - t))
    (by fun_prop)
    (by
      intro u hu
      convert (((hasDerivAt_id u).pow 2).const_sub 1).div_const 4 using 1 <;>
        try rfl
      norm_num [id]
      ring)
    (by
      intro u hu
      norm_num at hu
      linarith [hu.1])
  norm_num at hsubst
  have hleft :
      (∫ u in (0 : ℝ)..1,
        (-u / 2) *
          (Real.log (((1 - u ^ 2) / 4 + a * (1 + a)) /
            ((1 - u ^ 2) / 4)) /
            Real.sqrt (1 / 4 - (1 - u ^ 2) / 4))) =
        ∫ u in (0 : ℝ)..1,
          -Real.log (((1 - u ^ 2) / 4 + a * (1 + a)) /
            ((1 - u ^ 2) / 4)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u hu
    change (-u / 2) *
      (Real.log (((1 - u ^ 2) / 4 + a * (1 + a)) /
        ((1 - u ^ 2) / 4)) /
        Real.sqrt (1 / 4 - (1 - u ^ 2) / 4)) =
      -Real.log (((1 - u ^ 2) / 4 + a * (1 + a)) /
        ((1 - u ^ 2) / 4))
    have hu0 : 0 < u := hu.1
    have hsqrt : Real.sqrt (u ^ 2 / 4) = u / 2 := by
      rw [Real.sqrt_div' (u ^ 2) (by norm_num : (0 : ℝ) ≤ 4),
        Real.sqrt_sq hu0.le]
      norm_num
    have hrad : (1 / 4 : ℝ) - (1 - u ^ 2) / 4 = u ^ 2 / 4 := by ring
    rw [hrad, hsqrt]
    field_simp
  rw [hleft] at hsubst
  have hright :
      (∫ t in (1 / 4 : ℝ)..0,
        Real.log ((t + a * (1 + a)) / t) /
          Real.sqrt (1 / 4 - t)) =
        -(∫ t in (0 : ℝ)..(1 / 4 : ℝ),
          Real.log ((t + a * (1 + a)) / t) /
            Real.sqrt (1 / 4 - t)) :=
    intervalIntegral.integral_symm _ _
  rw [hright] at hsubst
  have hsplit :
      (∫ u in (0 : ℝ)..1,
        Real.log (((1 - u ^ 2) / 4 + a * (1 + a)) /
          ((1 - u ^ 2) / 4))) =
        2 * ((1 + a) * Real.log (1 + a) - a * Real.log a) := by
    have hminus1 :
        IntervalIntegrable (fun u : ℝ => Real.log (1 - u)) volume 0 1 := by
      simpa using
        ((intervalIntegral.intervalIntegrable_log'
          (a := (0 : ℝ)) (b := 1)).comp_sub_left 1).symm
    have hplus1 :
        IntervalIntegrable (fun u : ℝ => Real.log (1 + u)) volume 0 1 := by
      convert
        (intervalIntegral.intervalIntegrable_log'
          (a := (1 : ℝ)) (b := 2)).comp_add_left 1
        using 1 <;> norm_num
    have hminusB :
        IntervalIntegrable (fun u : ℝ => Real.log (b - u)) volume 0 1 := by
      refine (ContinuousOn.log
        (continuous_const.sub continuous_id).continuousOn ?_).intervalIntegrable
      intro u hu
      have hu' : u ≤ 1 := by simpa using hu.2
      exact (sub_pos.mpr (lt_of_le_of_lt hu' hb)).ne'
    have hplusB :
        IntervalIntegrable (fun u : ℝ => Real.log (b + u)) volume 0 1 := by
      refine (ContinuousOn.log
        (continuous_const.add continuous_id).continuousOn ?_).intervalIntegrable
      intro u hu
      have hu' : 0 ≤ u := by simpa using hu.1
      have hb' : 0 < b := lt_trans (by norm_num) hb
      exact (add_pos_of_pos_of_nonneg hb' hu').ne'
    calc
      (∫ u in (0 : ℝ)..1,
        Real.log (((1 - u ^ 2) / 4 + a * (1 + a)) /
          ((1 - u ^ 2) / 4))) =
          ∫ u in (0 : ℝ)..1,
            (Real.log (b - u) + Real.log (b + u)) -
              (Real.log (1 - u) + Real.log (1 + u)) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro u hu
        change Real.log (((1 - u ^ 2) / 4 + a * (1 + a)) /
          ((1 - u ^ 2) / 4)) =
          (Real.log (b - u) + Real.log (b + u)) -
            (Real.log (1 - u) + Real.log (1 + u))
        have hminus : 0 < 1 - u := sub_pos.mpr hu.2
        have hplus : 0 < 1 + u := by linarith [hu.1]
        have hbminus : 0 < b - u := by linarith [hb, hu.2]
        have hbplus : 0 < b + u := by linarith [hb, hu.1]
        have hratio :
            ((1 - u ^ 2) / 4 + a * (1 + a)) / ((1 - u ^ 2) / 4) =
              ((b - u) * (b + u)) / ((1 - u) * (1 + u)) := by
          dsimp [b]
          have hden : 1 - u ^ 2 ≠ 0 := by
            nlinarith [mul_pos hminus hplus]
          field_simp
          ring
        rw [hratio,
          Real.log_div (mul_pos hbminus hbplus).ne'
            (mul_pos hminus hplus).ne',
          Real.log_mul hbminus.ne' hbplus.ne',
          Real.log_mul hminus.ne' hplus.ne']
      _ =
          (((∫ u in (0 : ℝ)..1, Real.log (b - u)) +
            (∫ u in (0 : ℝ)..1, Real.log (b + u))) -
              ((∫ u in (0 : ℝ)..1, Real.log (1 - u)) +
                (∫ u in (0 : ℝ)..1, Real.log (1 + u)))) := by
        rw [intervalIntegral.integral_sub (hminusB.add hplusB)
          (hminus1.add hplus1),
          intervalIntegral.integral_add hminusB hplusB,
          intervalIntegral.integral_add hminus1 hplus1]
      _ = 2 * ((1 + a) * Real.log (1 + a) - a * Real.log a) := by
        rw [intervalIntegral.integral_comp_sub_left Real.log b,
          intervalIntegral.integral_comp_add_left Real.log b,
          intervalIntegral.integral_comp_sub_left Real.log 1,
          intervalIntegral.integral_comp_add_left Real.log 1,
          integral_log, integral_log, integral_log, integral_log]
        norm_num
        have hbminus : b - 1 = 2 * a := by dsimp [b]; ring
        have hbplus : b + 1 = 2 * (1 + a) := by dsimp [b]; ring
        rw [hbminus, hbplus,
          Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha0,
          Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
            (by linarith [ha'] : 1 + a ≠ 0)]
        ring
  rw [intervalIntegral.integral_neg, hsplit] at hsubst
  linarith

end MetricCodes.Spherical.HigherHierarchy.Arcsine

end

section

noncomputable section

open MeasureTheory Real Set
open scoped Interval

namespace MetricCodes.Spherical.HigherHierarchy.ArcsineIntegral

theorem integral_inv_add_mul_cos (a b : ℝ) (h : |b| < a) :
    (∫ θ in (0 : ℝ)..Real.pi, (a + b * Real.cos θ)⁻¹) =
      Real.pi / Real.sqrt (a ^ 2 - b ^ 2) := by
  have hab : -a < b ∧ b < a := abs_lt.mp h
  have hplus : 0 < a + b := by linarith [hab.1]
  have hminus : 0 < a - b := by linarith [hab.2]
  have hdisc : 0 < a ^ 2 - b ^ 2 := by
    nlinarith [mul_pos hplus hminus]
  let c : ℝ := Real.sqrt (a ^ 2 - b ^ 2)
  have hc : 0 < c := Real.sqrt_pos.2 hdisc
  have hden (θ : ℝ) : 0 < a + b * Real.cos θ := by
    have hbound : |b * Real.cos θ| ≤ |b| := by
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ)
        (abs_nonneg b)
    linarith [neg_le_of_abs_le hbound]
  let q : ℝ → ℝ := fun θ =>
    (a * Real.cos θ + b) / (a + b * Real.cos θ)
  let F : ℝ → ℝ := fun θ => -Real.arcsin (q θ) / c
  have hqcont : Continuous q := by
    exact ((continuous_const.mul Real.continuous_cos).add continuous_const).div
      (continuous_const.add (continuous_const.mul Real.continuous_cos))
      (fun θ => (hden θ).ne')
  have hFcont : Continuous F :=
    (Real.continuous_arcsin.comp hqcont).neg.div_const c
  have hintegrable :
      IntervalIntegrable (fun θ : ℝ => (a + b * Real.cos θ)⁻¹)
        volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    exact (continuous_const.add
      (continuous_const.mul Real.continuous_cos)).inv₀
        (fun θ => (hden θ).ne')
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi,
      HasDerivAt F ((a + b * Real.cos θ)⁻¹) θ := by
    intro θ hθ
    have hsin : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    have hqidentity :
        1 - (q θ) ^ 2 =
          (a ^ 2 - b ^ 2) * (Real.sin θ) ^ 2 /
            (a + b * Real.cos θ) ^ 2 := by
      have htrig : (Real.sin θ) ^ 2 = 1 - (Real.cos θ) ^ 2 := by
        linarith [Real.sin_sq_add_cos_sq θ]
      have hd2 : (a + b * Real.cos θ) ^ 2 ≠ 0 :=
        pow_ne_zero 2 (hden θ).ne'
      rw [htrig]
      dsimp [q]
      rw [div_pow]
      calc
        1 - (a * Real.cos θ + b) ^ 2 / (a + b * Real.cos θ) ^ 2 =
            ((a + b * Real.cos θ) ^ 2 -
              (a * Real.cos θ + b) ^ 2) /
              (a + b * Real.cos θ) ^ 2 := by
          rw [sub_div, div_self hd2]
        _ = (a ^ 2 - b ^ 2) * (1 - Real.cos θ ^ 2) /
              (a + b * Real.cos θ) ^ 2 := by
          congr 1
          ring
    have hqsmall : (q θ) ^ 2 < 1 := by
      have hpos : 0 <
          (a ^ 2 - b ^ 2) * (Real.sin θ) ^ 2 /
            (a + b * Real.cos θ) ^ 2 :=
        div_pos (mul_pos hdisc (sq_pos_of_pos hsin))
          (sq_pos_of_pos (hden θ))
      linarith [hqidentity]
    have hqlower : -1 < q θ := by nlinarith [sq_nonneg (q θ + 1)]
    have hqupper : q θ < 1 := by nlinarith [sq_nonneg (q θ - 1)]
    have hroot :
        Real.sqrt (1 - (q θ) ^ 2) =
          c * Real.sin θ / (a + b * Real.cos θ) := by
      rw [hqidentity, Real.sqrt_div (mul_nonneg hdisc.le (sq_nonneg _)),
        Real.sqrt_mul hdisc.le, Real.sqrt_sq hsin.le,
        Real.sqrt_sq (hden θ).le]
    have hqderiv :
        HasDerivAt q
          (-(a ^ 2 - b ^ 2) * Real.sin θ /
            (a + b * Real.cos θ) ^ 2) θ := by
      dsimp [q]
      refine ((((Real.hasDerivAt_cos θ).const_mul a).add_const b).div
        (((Real.hasDerivAt_cos θ).const_mul b).const_add a)
        (hden θ).ne').congr_deriv ?_
      ring
    have harcsin :=
      (Real.hasDerivAt_arcsin (ne_of_gt hqlower) (ne_of_lt hqupper)).comp
        θ hqderiv
    have hF :
        HasDerivAt F
          (-(1 / Real.sqrt (1 - (q θ) ^ 2) *
            (-(a ^ 2 - b ^ 2) * Real.sin θ /
              (a + b * Real.cos θ) ^ 2)) / c) θ := by
      simpa [F, Function.comp_def] using harcsin.neg.div_const c
    refine hF.congr_deriv ?_
    rw [hroot]
    have hcsq : c ^ 2 = a ^ 2 - b ^ 2 :=
      Real.sq_sqrt hdisc.le
    field_simp [hc.ne', (hden θ).ne', hsin.ne']
    nlinarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    Real.pi_pos.le hFcont.continuousOn hderiv hintegrable]
  dsimp [F, q]
  rw [Real.cos_pi, Real.cos_zero]
  have hqpi : (a * (-1) + b) / (a + b * (-1)) = -1 := by
    have hne : a + b * (-1) ≠ 0 := by
      simpa [sub_eq_add_neg] using hminus.ne'
    apply (div_eq_iff hne).2
    ring
  have hqzero : (a * 1 + b) / (a + b * 1) = 1 := by
    have hne : a + b * 1 ≠ 0 := by simpa using hplus.ne'
    apply (div_eq_iff hne).2
    ring
  rw [hqpi, hqzero, Real.arcsin_neg_one, Real.arcsin_one]
  dsimp [c]
  ring

end MetricCodes.Spherical.HigherHierarchy.ArcsineIntegral

end

section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal Interval Topology

namespace MetricCodes.Spherical.HigherHierarchy.ArcsineTransform

theorem betaPDFReal_half_half_eq (u : ℝ) (hu₀ : 0 < u) (hu₁ : u < 1) :
    betaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) u =
      (1 / Real.pi) * (Real.sqrt (u * (1 - u)))⁻¹ := by
  rw [betaPDFReal, if_pos ⟨hu₀, hu₁⟩,
    MetricCodes.Spherical.HigherHierarchy.Arcsine.beta_half_half_eq_pi]
  have hu : 0 ≤ u := hu₀.le
  have hv : 0 ≤ 1 - u := by linarith
  have hpow₁ : u ^ ((1 / 2 : ℝ) - 1) = (Real.sqrt u)⁻¹ := by
    convert Real.rpow_neg hu (1 / 2 : ℝ) using 1 <;>
      norm_num [Real.sqrt_eq_rpow]
  have hpow₂ : (1 - u) ^ ((1 / 2 : ℝ) - 1) =
      (Real.sqrt (1 - u))⁻¹ := by
    convert Real.rpow_neg hv (1 / 2 : ℝ) using 1 <;>
      norm_num [Real.sqrt_eq_rpow]
  rw [hpow₁, hpow₂, Real.sqrt_mul hu, mul_inv_rev]
  ring

theorem integral_beta_half_half_eq_integral_measureT (f : ℝ → ℝ) :
    (∫ u, f u ∂betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)) =
      (1 / Real.pi) *
        ∫ z, f ((z + 1) / 2) ∂Polynomial.Chebyshev.measureT := by
  have hmeas : Measurable (betaPDF (1 / 2 : ℝ) (1 / 2 : ℝ)) :=
    (measurable_betaPDFReal _ _).ennreal_ofReal
  have hfinite : ∀ᵐ u : ℝ ∂volume,
      betaPDF (1 / 2 : ℝ) (1 / 2 : ℝ) u < ⊤ := by
    filter_upwards [] with u
    simp [betaPDF]
  have hpdf (u : ℝ) :
      0 ≤ betaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) u := by
    by_cases hu : 0 < u ∧ u < 1
    · exact (betaPDFReal_pos hu.1 hu.2 (by norm_num) (by norm_num)).le
    · simp [betaPDFReal, hu]
  unfold betaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hmeas hfinite]
  simp_rw [betaPDF, ENNReal.toReal_ofReal (hpdf _), smul_eq_mul]
  rw [Polynomial.Chebyshev.integral_measureT,
    ← intervalIntegral.integral_const_mul]
  have hsupport :
      (∫ u : ℝ, betaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) u * f u) =
        ∫ u in (0 : ℝ)..1,
          betaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) u * f u := by
    rw [intervalIntegral.integral_of_le (by norm_num),
      integral_Ioc_eq_integral_Ioo, ← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    filter_upwards [] with u
    by_cases hu : u ∈ Set.Ioo (0 : ℝ) 1
    · simp [hu]
    · have hu' : ¬ (0 < u ∧ u < 1) := by simpa using hu
      simp [hu, betaPDFReal, hu']
  rw [hsupport]
  let g : ℝ → ℝ := fun z =>
    (1 / Real.pi) * (f ((z + 1) / 2) * (Real.sqrt (1 - z ^ 2))⁻¹)
  have hchange :
      (∫ u in (0 : ℝ)..1, g (2 * u - 1) * 2) =
        ∫ z in (-1 : ℝ)..1, g z := by
    convert intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0 : ℝ)) (b := 1)
      (f := fun u : ℝ => 2 * u - 1) (f' := fun _ : ℝ => 2)
      (g := g)
      (by fun_prop)
      (fun u _ => by
        simpa using
          (((hasDerivAt_const (x := u) (c := (2 : ℝ))).mul
            (hasDerivAt_id u)).sub_const 1))
      (fun _ _ => by norm_num) using 1 <;> norm_num
  dsimp [g] at hchange
  simp_rw [Real.sqrt_inv]
  rw [← hchange]
  apply intervalIntegral.integral_congr
  intro u hu
  change betaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) u * f u =
    (1 / Real.pi) *
      (f ((2 * u - 1 + 1) / 2) *
        (Real.sqrt (1 - (2 * u - 1) ^ 2))⁻¹) * 2
  have hu₀ : 0 ≤ u := by simpa using hu.1
  have hu₁ : u ≤ 1 := by simpa using hu.2
  by_cases hzero : u = 0 ∨ u = 1
  · rcases hzero with rfl | rfl <;> norm_num [betaPDFReal]
  · have hzero₀ : u ≠ 0 := fun h => hzero (Or.inl h)
    have hzero₁ : u ≠ 1 := fun h => hzero (Or.inr h)
    have hupos : 0 < u := lt_of_le_of_ne hu₀ (Ne.symm hzero₀)
    have huone : u < 1 := lt_of_le_of_ne hu₁ hzero₁
    rw [betaPDFReal_half_half_eq u hupos huone]
    have hquad : 1 - (2 * u - 1) ^ 2 = 4 * (u * (1 - u)) := by ring
    have hsqrt :
        Real.sqrt (1 - (2 * u - 1) ^ 2) =
          2 * Real.sqrt (u * (1 - u)) := by
      rw [hquad, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    rw [hsqrt]
    have harg : (2 * u - 1 + 1) / 2 = u := by ring
    rw [harg]
    field_simp

theorem integral_betaMap_half_half_eq_integral_cos
    (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ t, f t ∂(betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
      (fun t : ℝ => t / 4)) =
        (1 / Real.pi) *
          ∫ θ in (0 : ℝ)..Real.pi, f ((Real.cos θ + 1) / 8) := by
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable,
    integral_beta_half_half_eq_integral_measureT,
    Polynomial.Chebyshev.integral_measureT_eq_integral_cos]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  ring_nf

theorem betaMap_half_half_ae_pos :
    ∀ᵐ t ∂(betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
      (fun t : ℝ => t / 4), 0 < t := by
  rw [ae_map_iff (by fun_prop) measurableSet_Ioi]
  change ∀ᵐ t ∂volume.withDensity
    (betaPDF (1 / 2 : ℝ) (1 / 2 : ℝ)), 0 < t / 4
  have hmeas : Measurable (betaPDF (1 / 2 : ℝ) (1 / 2 : ℝ)) :=
    (measurable_betaPDFReal _ _).ennreal_ofReal
  rw [ae_withDensity_iff hmeas]
  filter_upwards [] with t ht
  by_contra hnot
  have htzero : t ≤ 0 := by
    have : t / 4 ≤ 0 := le_of_not_gt hnot
    linarith
  apply ht
  simp [betaPDF, betaPDFReal, not_lt_of_ge htzero]

instance betaMap_half_half_isProbabilityMeasure :
    IsProbabilityMeasure ((betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
      (fun t : ℝ => t / 4)) := by
  letI : IsProbabilityMeasure (betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem arcsine_stieltjes_integrable {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun t : ℝ => x / (x + t))
      ((betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
        (fun t : ℝ => t / 4)) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((by fun_prop : Measurable (fun t : ℝ => x / (x + t))).aestronglyMeasurable)
  filter_upwards [betaMap_half_half_ae_pos] with t ht
  have hden : 0 < x + t := by linarith
  have hnonneg : 0 ≤ x / (x + t) := div_nonneg hx hden.le
  simpa [norm_div, Real.norm_eq_abs, abs_of_nonneg hx, abs_of_pos hden] using
    ((div_le_one hden).2 (by linarith : x ≤ x + t))

theorem arcsine_integral_x_div_add {x : ℝ} (hx : 0 < x) :
    (∫ t, x / (x + t) ∂(betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
      (fun t : ℝ => t / 4)) =
        Real.sqrt (x / (x + 1 / 4)) := by
  rw [integral_betaMap_half_half_eq_integral_cos _ (by fun_prop)]
  have hrewrite :
      (∫ θ in (0 : ℝ)..Real.pi,
        x / (x + (Real.cos θ + 1) / 8)) =
          x * ∫ θ in (0 : ℝ)..Real.pi,
            ((x + 1 / 8) + (1 / 8) * Real.cos θ)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    change x / (x + (Real.cos θ + 1) / 8) =
      x * ((x + 1 / 8) + (1 / 8) * Real.cos θ)⁻¹
    rw [div_eq_mul_inv]
    congr 1
    ring
  rw [hrewrite,
    MetricCodes.Spherical.HigherHierarchy.ArcsineIntegral.integral_inv_add_mul_cos
      (x + 1 / 8) (1 / 8) (by
      norm_num [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8)]
      linarith)]
  have hquad : (x + 1 / 8) ^ 2 - (1 / 8 : ℝ) ^ 2 =
      x * (x + 1 / 4) := by ring
  rw [hquad, Real.sqrt_mul hx.le, Real.sqrt_div hx.le]
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hsy : Real.sqrt (x + 1 / 4) ≠ 0 :=
    (Real.sqrt_pos.mpr (by linarith)).ne'
  field_simp [Real.pi_pos.ne', hsx, hsy]
  nlinarith [Real.sq_sqrt hx.le]

theorem arcsine_integral_self_div_add {x : ℝ} (hx : 0 ≤ x) :
    (∫ t, t / (t + x) ∂(betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
      (fun t : ℝ => t / 4)) =
        1 - Real.sqrt (x / (x + 1 / 4)) := by
  by_cases hzero : x = 0
  · subst x
    calc
      (∫ t, t / (t + 0) ∂(betaMeasure (1 / 2 : ℝ)
        (1 / 2 : ℝ)).map (fun t : ℝ => t / 4)) =
          ∫ _t : ℝ, 1 ∂(betaMeasure (1 / 2 : ℝ)
            (1 / 2 : ℝ)).map (fun t : ℝ => t / 4) := by
            apply integral_congr_ae
            filter_upwards [betaMap_half_half_ae_pos] with t ht
            simp [ht.ne']
      _ = 1 - Real.sqrt (0 / (0 + 1 / 4)) := by norm_num
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
    calc
      (∫ t, t / (t + x) ∂(betaMeasure (1 / 2 : ℝ)
        (1 / 2 : ℝ)).map (fun t : ℝ => t / 4)) =
          ∫ t, (1 - x / (x + t)) ∂(betaMeasure (1 / 2 : ℝ)
            (1 / 2 : ℝ)).map (fun t : ℝ => t / 4) := by
            apply integral_congr_ae
            filter_upwards [betaMap_half_half_ae_pos] with t ht
            have hden : x + t ≠ 0 := ne_of_gt (by linarith)
            field_simp
            ring
      _ = 1 - (∫ t, x / (x + t) ∂(betaMeasure (1 / 2 : ℝ)
            (1 / 2 : ℝ)).map (fun t : ℝ => t / 4)) := by
            rw [integral_sub (integrable_const _)
              (arcsine_stieltjes_integrable hx)]
            rw [integral_const]
            have hprob : IsProbabilityMeasure
                ((betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
                  (fun t : ℝ => t / 4)) :=
              betaMap_half_half_isProbabilityMeasure
            letI := hprob
            simp only [smul_eq_mul, mul_one, measureReal_def]
            rw [measure_univ]
            norm_num
      _ = 1 - Real.sqrt (x / (x + 1 / 4)) := by
            rw [arcsine_integral_x_div_add hxpos]

end MetricCodes.Spherical.HigherHierarchy.ArcsineTransform

end

section

noncomputable section

open scoped BigOperators

namespace MetricCodes.Spherical.HigherHierarchyChebyshev

def poleAngle (N i : ℕ) : ℝ :=
  (((2 * i + 1 : ℕ) : ℝ) * Real.pi) / (2 * (N : ℝ))

def zeroAngle (N j : ℕ) : ℝ :=
  ((j : ℝ) * Real.pi) / (N : ℝ)

def pole (R : ℝ) (N i : ℕ) : ℝ :=
  R / 2 * (1 + Real.cos (poleAngle N i))

def zero (R : ℝ) (N j : ℕ) : ℝ :=
  R / 2 * (1 + Real.cos (zeroAngle N j))

def residue (N : ℕ) : ℝ := 1 / (N : ℝ)

def polePolynomial (R : ℝ) (N : ℕ) : Polynomial ℝ :=
  ∏ i ∈ Finset.range N, (Polynomial.X - Polynomial.C (pole R N i))

def inverseQuadratic (x : ℝ) : ℝ := (Real.sqrt (1 + 4 * x) - 1) / 2

def ambient (R : ℝ) (r : ℕ) (i : Fin (r + 1)) : ℝ :=
  inverseQuadratic (pole R (r + 1) i.val)

def stabilizer (R : ℝ) (r : ℕ) (i : Fin r) : ℝ :=
  inverseQuadratic (zero R (r + 1) (i.val + 1))

def affinePolynomial (R : ℝ) : Polynomial ℝ :=
  Polynomial.C (2 / R) * Polynomial.X + Polynomial.C (-1)

def shiftedChebyshev (R : ℝ) (N : ℕ) : Polynomial ℝ :=
  (Polynomial.Chebyshev.T ℝ (N : ℤ)).comp (affinePolynomial R)

theorem poleAngle_eq_midpoint {N : ℕ} (hN : 0 < N) (i : ℕ) :
    poleAngle N i = (((i : ℝ) + 1 / 2) * Real.pi) / (N : ℝ) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold poleAngle
  push_cast
  field_simp

theorem zeroAngle_nonneg (N j : ℕ) : 0 ≤ zeroAngle N j := by
  unfold zeroAngle
  positivity

theorem poleAngle_pos {N : ℕ} (hN : 0 < N) (i : ℕ) :
    0 < poleAngle N i := by
  rw [poleAngle_eq_midpoint hN]
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  positivity

theorem zeroAngle_le_pi {N j : ℕ} (hN : 0 < N) (hj : j ≤ N) :
    zeroAngle N j ≤ Real.pi := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hj' : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hj
  unfold zeroAngle
  apply (div_le_iff₀ hN').2
  nlinarith [mul_le_mul_of_nonneg_right hj' Real.pi_pos.le]

theorem zeroAngle_lt_poleAngle {N i : ℕ} (hN : 0 < N) :
    zeroAngle N i < poleAngle N i := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [poleAngle_eq_midpoint hN]
  unfold zeroAngle
  apply (div_lt_div_iff_of_pos_right hN').2
  exact mul_lt_mul_of_pos_right (by linarith) Real.pi_pos

theorem poleAngle_lt_succ_zeroAngle {N i : ℕ} (hN : 0 < N) :
    poleAngle N i < zeroAngle N (i + 1) := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [poleAngle_eq_midpoint hN]
  unfold zeroAngle
  push_cast
  apply (div_lt_div_iff_of_pos_right hN').2
  exact mul_lt_mul_of_pos_right (by linarith) Real.pi_pos

theorem poleAngle_lt_pi {N i : ℕ} (hN : 0 < N) (hi : i < N) :
    poleAngle N i < Real.pi :=
  (poleAngle_lt_succ_zeroAngle hN).trans_le
    (zeroAngle_le_pi hN (Nat.succ_le_of_lt hi))

theorem strict_interlacing {R : ℝ} (hR : 0 < R)
    {N i : ℕ} (hN : 0 < N) (hi : i < N) :
    zero R N (i + 1) < pole R N i ∧ pole R N i < zero R N i := by
  have hscale : 0 < R / 2 := by positivity
  constructor
  · unfold pole zero
    apply mul_lt_mul_of_pos_left _ hscale
    gcongr
    exact Real.cos_lt_cos_of_nonneg_of_le_pi
      (poleAngle_pos hN i).le
      (zeroAngle_le_pi hN (Nat.succ_le_of_lt hi))
      (poleAngle_lt_succ_zeroAngle hN)
  · unfold pole zero
    apply mul_lt_mul_of_pos_left _ hscale
    gcongr
    exact Real.cos_lt_cos_of_nonneg_of_le_pi
      (zeroAngle_nonneg N i)
      (poleAngle_lt_pi hN hi).le
      (zeroAngle_lt_poleAngle hN)

theorem pole_pos {R : ℝ} (hR : 0 < R)
    {N i : ℕ} (hN : 0 < N) (hi : i < N) :
    0 < pole R N i := by
  have hcos : -1 < Real.cos (poleAngle N i) := by
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi
      (poleAngle_pos hN i).le (le_refl Real.pi) (poleAngle_lt_pi hN hi)
  unfold pole
  exact mul_pos (by positivity) (by linarith)

theorem zero_nonneg {R : ℝ} (hR : 0 ≤ R) (N j : ℕ) :
    0 ≤ zero R N j := by
  unfold zero
  exact mul_nonneg (by positivity)
    (by linarith [Real.neg_one_le_cos (zeroAngle N j)])

theorem inverseQuadratic_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ inverseQuadratic x := by
  have hrad : 0 ≤ 1 + 4 * x := by linarith
  have hsqrt := Real.sqrt_nonneg (1 + 4 * x)
  have hsq := Real.sq_sqrt hrad
  unfold inverseQuadratic
  nlinarith

theorem quadraticCoordinate_inverseQuadratic {x : ℝ} (hx : 0 ≤ x) :
    MetricCodes.Spherical.HigherHierarchy.quadraticCoordinate
      (inverseQuadratic x) = x := by
  have hrad : 0 ≤ 1 + 4 * x := by linarith
  have hsq := Real.sq_sqrt hrad
  unfold MetricCodes.Spherical.HigherHierarchy.quadraticCoordinate
    inverseQuadratic
  nlinarith

theorem inverseQuadratic_strictMonoOn :
    StrictMonoOn inverseQuadratic (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  by_contra hnot
  have hle : inverseQuadratic y ≤ inverseQuadratic x := le_of_not_gt hnot
  have hquad :=
    MetricCodes.Spherical.HigherHierarchy.quadraticCoordinate_strictMonoOn.monotoneOn
      (inverseQuadratic_nonneg hy) (inverseQuadratic_nonneg hx) hle
  rw [quadraticCoordinate_inverseQuadratic hy,
    quadraticCoordinate_inverseQuadratic hx] at hquad
  linarith

theorem ambient_stabilizer_interlacing {R : ℝ} (hR : 0 < R) (r : ℕ) :
    MetricCodes.Spherical.HigherHierarchy.Interlacing
      (ambient R r) (stabilizer R r) := by
  have hN : 0 < r + 1 := Nat.zero_lt_succ r
  constructor
  · exact inverseQuadratic_nonneg
      (pole_pos hR hN (Fin.last r).isLt).le
  · intro i
    have hi : i.val < r + 1 := Nat.lt_trans i.isLt (Nat.lt_succ_self r)
    have hinext : i.val + 1 < r + 1 := by omega
    have hleft := (strict_interlacing hR hN hi).1
    have hright := (strict_interlacing hR hN hinext).2
    constructor
    · exact inverseQuadratic_strictMonoOn
        (zero_nonneg hR.le (r + 1) (i.val + 1))
        (pole_pos hR hN hi).le hleft
    · exact inverseQuadratic_strictMonoOn
        (pole_pos hR hN hinext).le
        (zero_nonneg hR.le (r + 1) (i.val + 1)) hright

theorem quadraticCoordinate_ambient {R : ℝ} (hR : 0 < R)
    (r : ℕ) (i : Fin (r + 1)) :
    MetricCodes.Spherical.HigherHierarchy.quadraticCoordinate
      (ambient R r i) = pole R (r + 1) i.val := by
  unfold ambient
  exact quadraticCoordinate_inverseQuadratic
    (pole_pos hR (Nat.zero_lt_succ r) i.isLt).le

theorem quadraticCoordinate_stabilizer {R : ℝ} (hR : 0 < R)
    (r : ℕ) (i : Fin r) :
    MetricCodes.Spherical.HigherHierarchy.quadraticCoordinate
      (stabilizer R r i) = zero R (r + 1) (i.val + 1) := by
  unfold stabilizer
  exact quadraticCoordinate_inverseQuadratic
    (zero_nonneg hR.le (r + 1) (i.val + 1))

theorem polePolynomial_monic (R : ℝ) (N : ℕ) :
    (polePolynomial R N).Monic := by
  unfold polePolynomial
  exact Polynomial.monic_prod_of_monic _ _
    (fun i _hi => Polynomial.monic_X_sub_C (pole R N i))

theorem polePolynomial_natDegree (R : ℝ) (N : ℕ) :
    (polePolynomial R N).natDegree = N := by
  unfold polePolynomial
  simp

theorem polePolynomial_roots (R : ℝ) (N : ℕ) :
    (polePolynomial R N).roots =
      (Finset.range N).val.map (pole R N) := by
  unfold polePolynomial
  rw [Polynomial.roots_prod]
  · simp
  · exact (Polynomial.monic_prod_X_sub_C (pole R N) (Finset.range N)).ne_zero

theorem shiftedChebyshev_roots {R : ℝ} (hR : 0 < R) (N : ℕ) :
    (shiftedChebyshev R N).roots = (polePolynomial R N).roots := by
  have hR' : R ≠ 0 := hR.ne'
  have hscale : 2 / R ≠ (0 : ℝ) := div_ne_zero (by norm_num) hR'
  rw [polePolynomial_roots]
  unfold shiftedChebyshev affinePolynomial
  rw [Polynomial.roots_comp_C_mul_X_add_C _ _ _
    (isUnit_iff_ne_zero.mpr hscale)]
  rw [Polynomial.Chebyshev.roots_T_real]
  have hinj : Set.InjOn
      (fun k : ℕ => Real.cos ((2 * (k : ℝ) + 1) * Real.pi / (2 * (N : ℝ))))
      (Finset.range N : Set ℕ) := by
    exact (Finset.range N).nodup_map_iff_injOn.mp
      (Polynomial.Chebyshev.roots_T_real_nodup N)
  rw [Finset.image_val_of_injOn hinj, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i _hi
  simp only [Function.comp_apply, Ring.inverse_eq_inv]
  change (2 / R)⁻¹ *
      (Real.cos ((2 * (i : ℝ) + 1) * Real.pi / (2 * (N : ℝ))) - -1) =
    pole R N i
  unfold pole poleAngle
  push_cast
  field_simp
  ring

theorem shiftedChebyshev_splits {R : ℝ} (hR : 0 < R) (N : ℕ) :
    (shiftedChebyshev R N).Splits := by
  apply Polynomial.splits_iff_card_roots.mpr
  rw [shiftedChebyshev_roots hR N, polePolynomial_roots]
  have hscale : 2 / R ≠ (0 : ℝ) := div_ne_zero (by norm_num) hR.ne'
  unfold shiftedChebyshev affinePolynomial
  rw [Polynomial.natDegree_comp, Polynomial.Chebyshev.natDegree_T,
    Polynomial.natDegree_linear hscale]
  simp

theorem polePolynomial_splits (R : ℝ) (N : ℕ) :
    (polePolynomial R N).Splits := by
  unfold polePolynomial
  exact Polynomial.Splits.prod
    (fun i _hi => Polynomial.Splits.X_sub_C (pole R N i))

theorem shiftedChebyshev_eq_leadingCoeff_mul_polePolynomial
    {R : ℝ} (hR : 0 < R) (N : ℕ) :
    shiftedChebyshev R N =
      Polynomial.C (shiftedChebyshev R N).leadingCoeff * polePolynomial R N := by
  calc
    shiftedChebyshev R N =
        Polynomial.C (shiftedChebyshev R N).leadingCoeff *
          ((shiftedChebyshev R N).roots.map
            (fun x => Polynomial.X - Polynomial.C x)).prod :=
      (shiftedChebyshev_splits hR N).eq_prod_roots
    _ = Polynomial.C (shiftedChebyshev R N).leadingCoeff *
          ((polePolynomial R N).roots.map
            (fun x => Polynomial.X - Polynomial.C x)).prod := by
      rw [shiftedChebyshev_roots hR N]
    _ = Polynomial.C (shiftedChebyshev R N).leadingCoeff *
          polePolynomial R N := by
      exact congrArg
        (fun P : Polynomial ℝ =>
          Polynomial.C (shiftedChebyshev R N).leadingCoeff * P)
        ((polePolynomial_splits R N).eq_prod_roots_of_monic
          (polePolynomial_monic R N)).symm

theorem zeroAngle_pos {N j : ℕ} (hN : 0 < N) (hj : 0 < j) :
    0 < zeroAngle N j := by
  unfold zeroAngle
  positivity

theorem zeroAngle_lt_pi {N j : ℕ} (hN : 0 < N) (hj : j < N) :
    zeroAngle N j < Real.pi := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hj' : (j : ℝ) < (N : ℝ) := by exact_mod_cast hj
  unfold zeroAngle
  apply (div_lt_iff₀ hN').2
  nlinarith [mul_lt_mul_of_pos_right hj' Real.pi_pos]

theorem affinePolynomial_eval_zero {R : ℝ} (hR : 0 < R)
    (N j : ℕ) :
    (affinePolynomial R).eval (zero R N j) =
      Real.cos (zeroAngle N j) := by
  have hR' : R ≠ 0 := hR.ne'
  simp [affinePolynomial, zero]
  field_simp
  ring

theorem shiftedChebyshev_derivative_eval_zero {R : ℝ} (hR : 0 < R)
    {N j : ℕ} (hjpos : 0 < j) (hj : j < N) :
    (shiftedChebyshev R N).derivative.eval (zero R N j) = 0 := by
  have hN : 0 < N := hjpos.trans hj
  have hsine : 0 < Real.sin (zeroAngle N j) :=
    Real.sin_pos_of_pos_of_lt_pi (zeroAngle_pos hN hjpos)
      (zeroAngle_lt_pi hN hj)
  have hmul : (N : ℝ) * zeroAngle N j = (j : ℝ) * Real.pi := by
    unfold zeroAngle
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  have hu := Polynomial.Chebyshev.U_real_cos
    (zeroAngle N j) ((N : ℤ) - 1)
  have harg : ((((N : ℤ) - 1 : ℤ) : ℝ) + 1) * zeroAngle N j =
      (j : ℝ) * Real.pi := by
    norm_num
    exact hmul
  rw [harg, Real.sin_nat_mul_pi] at hu
  have hU :
      (Polynomial.Chebyshev.U ℝ ((N : ℤ) - 1)).eval
        (Real.cos (zeroAngle N j)) = 0 :=
    (mul_eq_zero.mp hu).resolve_right hsine.ne'
  unfold shiftedChebyshev
  rw [Polynomial.derivative_comp, Polynomial.eval_mul, Polynomial.eval_comp,
    affinePolynomial_eval_zero hR]
  rw [Polynomial.Chebyshev.T_derivative_eq_U, Polynomial.eval_mul]
  simp [hU]

theorem shiftedChebyshev_leadingCoeff_ne_zero {R : ℝ} (hR : 0 < R)
    {N : ℕ} (hN : 0 < N) :
    (shiftedChebyshev R N).leadingCoeff ≠ 0 := by
  apply Polynomial.leadingCoeff_ne_zero.mpr
  intro hzero
  have hcard := (shiftedChebyshev_splits hR N).natDegree_eq_card_roots
  rw [shiftedChebyshev_roots hR N, polePolynomial_roots] at hcard
  simp at hcard
  simp [hzero] at hcard
  omega

theorem polePolynomial_derivative_eval_zero {R : ℝ} (hR : 0 < R)
    {N j : ℕ} (hjpos : 0 < j) (hj : j < N) :
    (polePolynomial R N).derivative.eval (zero R N j) = 0 := by
  have hN : 0 < N := hjpos.trans hj
  have heq := congrArg Polynomial.derivative
    (shiftedChebyshev_eq_leadingCoeff_mul_polePolynomial hR N)
  have hev := congrArg (Polynomial.eval (zero R N j)) heq
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C,
    zero_mul, Polynomial.eval_mul, Polynomial.eval_C, zero_add] at hev
  rw [shiftedChebyshev_derivative_eval_zero hR hjpos hj] at hev
  exact (mul_eq_zero.mp hev.symm).resolve_left
    (shiftedChebyshev_leadingCoeff_ne_zero hR hN)

theorem zero_strictAnti {R : ℝ} (hR : 0 < R)
    {N i j : ℕ} (hN : 0 < N) (hj : j ≤ N) (hij : i < j) :
    zero R N j < zero R N i := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hij' : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
  have hangles : zeroAngle N i < zeroAngle N j := by
    unfold zeroAngle
    apply (div_lt_div_iff_of_pos_right hN').2
    exact mul_lt_mul_of_pos_right hij' Real.pi_pos
  unfold zero
  apply mul_lt_mul_of_pos_left _ (by positivity : 0 < R / 2)
  gcongr
  exact Real.cos_lt_cos_of_nonneg_of_le_pi
    (zeroAngle_nonneg N i) (zeroAngle_le_pi hN hj) hangles

def normalizedDerivative (R : ℝ) (r : ℕ) : Polynomial ℝ :=
  Polynomial.C ((r + 1 : ℕ) : ℝ)⁻¹ *
    (polePolynomial R (r + 1)).derivative

theorem normalizedDerivative_monic (R : ℝ) (r : ℕ) :
    (normalizedDerivative R r).Monic := by
  unfold normalizedDerivative
  apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [Polynomial.leadingCoeff_derivative, polePolynomial_natDegree,
    (polePolynomial_monic R (r + 1)).leadingCoeff]
  have hN : (r : ℝ) + 1 ≠ 0 := by positivity
  simpa using inv_mul_cancel₀ hN

theorem normalizedDerivative_natDegree (R : ℝ) (r : ℕ) :
    (normalizedDerivative R r).natDegree = r := by
  unfold normalizedDerivative
  have hN : ((r + 1 : ℕ) : ℝ)⁻¹ ≠ 0 := by positivity
  rw [Polynomial.natDegree_C_mul hN, Polynomial.natDegree_derivative,
    polePolynomial_natDegree]
  omega

theorem zero_nodes_injective {R : ℝ} (hR : 0 < R) (r : ℕ) :
    Function.Injective (fun i : Fin r => zero R (r + 1) (i.val + 1)) := by
  have hanti : StrictAnti (fun i : Fin r => zero R (r + 1) (i.val + 1)) := by
    intro i j hij
    apply zero_strictAnti hR (Nat.zero_lt_succ r)
    · omega
    · have hval := Fin.mk_lt_mk.mp hij
      omega
  exact hanti.injective

theorem normalizedDerivative_eq_stabilizerPolynomial
    {R : ℝ} (hR : 0 < R) (r : ℕ) :
    normalizedDerivative R r =
      MetricCodes.Spherical.HigherHierarchy.stabilizerPolynomial
        (stabilizer R r) := by
  let P := normalizedDerivative R r
  let Q := MetricCodes.Spherical.HigherHierarchy.stabilizerPolynomial
    (stabilizer R r)
  have hP : Polynomial.IsMonicOfDegree P r :=
    ⟨normalizedDerivative_natDegree R r,
      normalizedDerivative_monic R r⟩
  have hQ : Polynomial.IsMonicOfDegree Q r :=
    ⟨MetricCodes.Spherical.HigherHierarchy.stabilizerPolynomial_natDegree
        (stabilizer R r),
      MetricCodes.Spherical.HigherHierarchy.stabilizerPolynomial_monic
        (stabilizer R r)⟩
  by_cases hr : r = 0
  · subst r
    exact (Polynomial.isMonicOfDegree_zero_iff.mp hP).trans
      (Polynomial.isMonicOfDegree_zero_iff.mp hQ).symm
  · have hdeg : (P - Q).natDegree < r := hP.natDegree_sub_lt hr hQ
    have hzero : P - Q = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
        (P - Q) (zero_nodes_injective hR r)
      · intro i
        rw [Polynomial.eval_sub]
        have hPi : P.eval (zero R (r + 1) (i.val + 1)) = 0 := by
          dsimp [P, normalizedDerivative]
          rw [Polynomial.eval_mul, Polynomial.eval_C]
          rw [polePolynomial_derivative_eval_zero hR (by omega)
            (by omega)]
          ring
        rw [hPi]
        have hQi : Q.eval (zero R (r + 1) (i.val + 1)) = 0 := by
          unfold Q MetricCodes.Spherical.HigherHierarchy.stabilizerPolynomial
          rw [Polynomial.eval_prod]
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          simp [quadraticCoordinate_stabilizer hR r i]
        rw [hQi]
        ring
      · simpa using hdeg
    exact sub_eq_zero.mp hzero

theorem polePolynomial_eq_fin_prod (R : ℝ) (r : ℕ) :
    polePolynomial R (r + 1) =
      ∏ i : Fin (r + 1),
        (Polynomial.X - Polynomial.C (pole R (r + 1) i.val)) := by
  unfold polePolynomial
  exact (Fin.prod_univ_eq_prod_range
    (fun i => Polynomial.X - Polynomial.C (pole R (r + 1) i))
    (r + 1)).symm

theorem polePolynomial_derivative_eval_pole
    (R : ℝ) (r : ℕ) (ℓ : Fin (r + 1)) :
    (polePolynomial R (r + 1)).derivative.eval
        (pole R (r + 1) ℓ.val) =
      ∏ m : Fin r,
        (pole R (r + 1) ℓ.val -
          pole R (r + 1) (ℓ.succAbove m).val) := by
  rw [polePolynomial_eq_fin_prod,
    Fin.prod_univ_succAbove
      (fun i : Fin (r + 1) =>
        Polynomial.X - Polynomial.C (pole R (r + 1) i.val)) ℓ]
  simp [Polynomial.derivative_mul, Polynomial.eval_prod]

theorem polePolynomial_derivative_eval_pole_eq_lagrangeDenominator
    {R : ℝ} (hR : 0 < R) (r : ℕ) (ℓ : Fin (r + 1)) :
    (polePolynomial R (r + 1)).derivative.eval
        (pole R (r + 1) ℓ.val) =
      MetricCodes.Spherical.HigherHierarchy.lagrangeDenominator
        (ambient R r) ℓ := by
  rw [polePolynomial_derivative_eval_pole]
  unfold MetricCodes.Spherical.HigherHierarchy.lagrangeDenominator
  apply Finset.prod_congr rfl
  intro m _hm
  rw [quadraticCoordinate_ambient hR r ℓ,
    quadraticCoordinate_ambient hR r (ℓ.succAbove m)]

theorem lagrangeWeight_eq_residue {R : ℝ} (hR : 0 < R)
    (r : ℕ) (ℓ : Fin (r + 1)) :
    MetricCodes.Spherical.HigherHierarchy.lagrangeWeight
      (ambient R r) (stabilizer R r) ℓ = residue (r + 1) := by
  have hden := (ambient_stabilizer_interlacing hR r).lagrangeDenominator_ne_zero ℓ
  have heq := congrArg (Polynomial.eval (pole R (r + 1) ℓ.val))
    (normalizedDerivative_eq_stabilizerPolynomial hR r)
  simp only [normalizedDerivative, Polynomial.eval_mul,
    Polynomial.eval_C] at heq
  rw [polePolynomial_derivative_eval_pole_eq_lagrangeDenominator
    hR r ℓ] at heq
  have hnum :
      MetricCodes.Spherical.HigherHierarchy.lagrangeNumerator
        (ambient R r) (stabilizer R r) ℓ =
      MetricCodes.Spherical.HigherHierarchy.lagrangeDenominator
        (ambient R r) ℓ / ((r + 1 : ℕ) : ℝ) := by
    rw [← MetricCodes.Spherical.HigherHierarchy.stabilizerPolynomial_eval]
    rw [quadraticCoordinate_ambient hR r ℓ]
    rw [← heq]
    ring
  unfold MetricCodes.Spherical.HigherHierarchy.lagrangeWeight residue
  rw [hnum]
  field_simp

theorem Gamma_eq_average_spectralAtom {R : ℝ} (hR : 0 < R)
    (r : ℕ) :
    MetricCodes.Spherical.HigherHierarchy.Gamma
      (ambient R r) (stabilizer R r) =
      (∑ ℓ : Fin (r + 1),
        MetricCodes.Spherical.HigherHierarchy.spectralAtom
          (ambient R r ℓ)) / ((r + 1 : ℕ) : ℝ) := by
  unfold MetricCodes.Spherical.HigherHierarchy.Gamma
  simp_rw [lagrangeWeight_eq_residue hR r]
  unfold residue
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

theorem spectralAtom_inverseQuadratic {x : ℝ} (hx : 0 ≤ x) :
    MetricCodes.Spherical.HigherHierarchy.spectralAtom
      (inverseQuadratic x) =
      Real.sqrt x / Real.sqrt (1 + 4 * x) := by
  unfold MetricCodes.Spherical.HigherHierarchy.spectralAtom
  rw [quadraticCoordinate_inverseQuadratic hx]
  unfold inverseQuadratic
  ring

theorem spectralAtom_inverseQuadratic_half {x : ℝ} (hx : 0 ≤ x) :
    MetricCodes.Spherical.HigherHierarchy.spectralAtom
      (inverseQuadratic x) =
      (1 / 2 : ℝ) * Real.sqrt (x / (x + 1 / 4)) := by
  rw [spectralAtom_inverseQuadratic hx, Real.sqrt_div hx]
  have hrad : 1 + 4 * x = 4 * (x + 1 / 4) := by ring
  rw [hrad, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num
  ring

end MetricCodes.Spherical.HigherHierarchyChebyshev

end

section

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace MetricCodes.Spherical.HigherHierarchy.Entropy

def endpoint : ℝ := 1 / 4

def arcsineMeasure : Measure ℝ :=
  (betaMeasure (1 / 2) (1 / 2)).map (fun t : ℝ => t / 4)

def comparisonMeasure : Measure ℝ :=
  (betaMeasure 1 (1 / 2)).map (fun t : ℝ => t / 4)

def comparisonLebesgueDensity (t : ℝ) : ℝ≥0∞ :=
  if 0 < t ∧ t < (1 / 4 : ℝ) then
    ENNReal.ofReal (1 / Real.sqrt (1 / 4 - t))
  else
    0

theorem comparisonLebesgueDensity_measurable :
    Measurable comparisonLebesgueDensity := by
  unfold comparisonLebesgueDensity
  apply Measurable.ite
    ((measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_lt measurable_id measurable_const))
  · fun_prop
  · fun_prop

instance arcsineMeasure_isProbabilityMeasure : IsProbabilityMeasure arcsineMeasure := by
  letI : IsProbabilityMeasure (betaMeasure (1 / 2) (1 / 2)) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  unfold arcsineMeasure
  exact Measure.isProbabilityMeasure_map (by fun_prop)

instance comparisonMeasure_isProbabilityMeasure : IsProbabilityMeasure comparisonMeasure := by
  letI : IsProbabilityMeasure (betaMeasure 1 (1 / 2)) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  unfold comparisonMeasure
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem comparisonMeasure_eq_volume_withDensity :
    comparisonMeasure = volume.withDensity comparisonLebesgueDensity := by
  let w : ℝ → ℝ≥0∞ := fun t => betaPDF 1 (1 / 2 : ℝ) (4 * t)
  have hw : Measurable w := by
    exact ((measurable_betaPDFReal 1 (1 / 2)).ennreal_ofReal).comp
      (by fun_prop)
  have hscale : volume.map (fun t : ℝ => t / 4) =
      ENNReal.ofReal 4 • (volume : Measure ℝ) := by
    convert Real.map_volume_mul_right
      (show (4 : ℝ)⁻¹ ≠ 0 by norm_num) using 1
    · congr 1
    · norm_num
  have hbeta : betaPDF 1 (1 / 2 : ℝ) =
      w ∘ (fun t : ℝ => t / 4) := by
    funext t
    dsimp [w, Function.comp_apply]
    congr 1
    ring
  have hdensity : (ENNReal.ofReal 4) • w = comparisonLebesgueDensity := by
    funext t
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases ht : 0 < t ∧ t < (1 / 4 : ℝ)
    · have ht₀ : 0 < 4 * t := mul_pos (by norm_num) ht.1
      have ht₁ : 4 * t < 1 := by nlinarith [ht.2]
      unfold comparisonLebesgueDensity
      rw [if_pos ht]
      dsimp [w]
      rw [betaPDF_of_pos_lt_one ht₀ ht₁,
        MetricCodes.Spherical.HigherHierarchy.Arcsine.beta_one_half_eq_two]
      have hremaining : 0 < 1 / 4 - t := by linarith [ht.2]
      have hradical : 1 - 4 * t = 4 * (1 / 4 - t) := by ring
      have hsqrt : Real.sqrt (1 - 4 * t) =
          2 * Real.sqrt (1 / 4 - t) := by
        rw [hradical, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
      have hpow : (1 - 4 * t) ^ ((1 / 2 : ℝ) - 1) =
          (Real.sqrt (1 - 4 * t))⁻¹ := by
        convert Real.rpow_neg (by linarith [ht₁] : 0 ≤ 1 - 4 * t)
          (1 / 2 : ℝ) using 1 <;> norm_num [Real.sqrt_eq_rpow]
      have hsqrt_ne : Real.sqrt (1 / 4 - t) ≠ 0 :=
        (Real.sqrt_pos.mpr hremaining).ne'
      rw [hpow, hsqrt]
      norm_num
      let v : ℝ≥0∞ := ENNReal.ofReal ((Real.sqrt (1 / 4 - t))⁻¹)
      change (4 : ℝ≥0∞) *
        (ENNReal.ofReal (1 / 2 : ℝ) *
          (v * ENNReal.ofReal (1 / 2 : ℝ))) = v
      calc
        (4 : ℝ≥0∞) *
            (ENNReal.ofReal (1 / 2 : ℝ) *
              (v * ENNReal.ofReal (1 / 2 : ℝ))) =
            (4 * ENNReal.ofReal (1 / 2 : ℝ) *
              ENNReal.ofReal (1 / 2 : ℝ)) * v := by ac_rfl
        _ = _ := by
          have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
            rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
            norm_num
          rw [hhalf]
          have hcancel : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 1 :=
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
          rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num]
          calc
            (2 * 2 : ℝ≥0∞) * 2⁻¹ * 2⁻¹ * v =
                ((2 * 2⁻¹) * (2 * 2⁻¹)) * v := by ac_rfl
            _ = v := by rw [hcancel]; simp
    · have hnot : ¬ (0 < 4 * t ∧ 4 * t < 1) := by
        intro h
        apply ht
        constructor
        · nlinarith [h.1]
        · nlinarith [h.2]
      change ENNReal.ofReal 4 * betaPDF 1 (1 / 2 : ℝ) (4 * t) =
        comparisonLebesgueDensity t
      rw [comparisonLebesgueDensity, if_neg ht, betaPDF, betaPDFReal,
        if_neg hnot]
      simp
  unfold comparisonMeasure betaMeasure
  rw [hbeta,
    MetricCodes.Spherical.HigherHierarchy.Arcsine.map_withDensity_comp
      (by fun_prop) hw,
    hscale, withDensity_smul_measure,
    ← withDensity_smul (ENNReal.ofReal 4) hw, hdensity]

theorem comparisonMeasure_integral_eq_intervalIntegral (f : ℝ → ℝ) :
    (∫ t, f t ∂comparisonMeasure) =
      ∫ t in (0 : ℝ)..(1 / 4 : ℝ),
        f t / Real.sqrt (1 / 4 - t) := by
  rw [comparisonMeasure_eq_volume_withDensity,
    integral_withDensity_eq_integral_toReal_smul
      comparisonLebesgueDensity_measurable (by
        filter_upwards [] with t
        unfold comparisonLebesgueDensity
        split_ifs <;> simp),
    intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Set.Ioo (0 : ℝ) (1 / 4)
  · have ht' : 0 < t ∧ t < (1 / 4 : ℝ) := ht
    change (comparisonLebesgueDensity t).toReal * f t =
      (Set.Ioo (0 : ℝ) (1 / 4)).indicator
        (fun t => f t / Real.sqrt (1 / 4 - t)) t
    rw [comparisonLebesgueDensity, if_pos ht', Set.indicator_of_mem ht,
      ENNReal.toReal_ofReal (by positivity)]
    ring
  · have ht' : ¬ (0 < t ∧ t < (1 / 4 : ℝ)) := by simpa using ht
    change (comparisonLebesgueDensity t).toReal * f t =
      (Set.Ioo (0 : ℝ) (1 / 4)).indicator
        (fun t => f t / Real.sqrt (1 / 4 - t)) t
    rw [comparisonLebesgueDensity, if_neg ht',
      Set.indicator_of_notMem ht]
    simp

theorem comparison_logMoment :
    (∫ t, Real.log t ∂comparisonMeasure) = -2 := by
  rw [comparisonMeasure_integral_eq_intervalIntegral]
  exact MetricCodes.Spherical.HigherHierarchy.Arcsine.comparisonDensity_log_intervalIntegral

theorem comparison_logAtom_integral {a : ℝ} (ha : 0 ≤ a) :
    (∫ t, Real.log ((t + a * (1 + a)) / t) ∂comparisonMeasure) =
      2 * ((1 + a) * Real.log (1 + a) - a * Real.log a) := by
  rw [comparisonMeasure_integral_eq_intervalIntegral]
  exact
    MetricCodes.Spherical.HigherHierarchy.Arcsine.comparisonDensity_logAtom_intervalIntegral ha

theorem betaMeasure_ae_mem_Ioo {α β : ℝ} :
    ∀ᵐ x ∂(betaMeasure α β), x ∈ Set.Ioo (0 : ℝ) 1 := by
  change ∀ᵐ x ∂(volume.withDensity (betaPDF α β)), x ∈ Set.Ioo (0 : ℝ) 1
  have hmeas : Measurable (betaPDF α β) :=
    (measurable_betaPDFReal α β).ennreal_ofReal
  rw [ae_withDensity_iff hmeas]
  filter_upwards [] with x hx
  by_contra h
  have h' : ¬ (0 < x ∧ x < 1) := by simpa using h
  exact hx (by simp [betaPDF, betaPDFReal, h'])

theorem betaMeasure_absolutelyContinuous_betaMeasure
    {α β γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) :
    betaMeasure α β ≪ betaMeasure γ δ := by
  intro s hs
  change (volume.withDensity (betaPDF γ δ)) s = 0 at hs
  change (volume.withDensity (betaPDF α β)) s = 0
  have hmeas₁ : Measurable (betaPDF α β) :=
    (measurable_betaPDFReal α β).ennreal_ofReal
  have hmeas₂ : Measurable (betaPDF γ δ) :=
    (measurable_betaPDFReal γ δ).ennreal_ofReal
  rw [withDensity_apply_eq_zero hmeas₂] at hs
  rw [withDensity_apply_eq_zero hmeas₁]
  apply measure_mono_null _ hs
  rintro x ⟨hx, hxs⟩
  refine ⟨?_, hxs⟩
  have hsupport : 0 < x ∧ x < 1 := by
    by_contra h
    exact hx (by simp [betaPDF, betaPDFReal, h])
  have hpos := betaPDFReal_pos hsupport.1 hsupport.2 hγ hδ
  intro hzero
  have hnonpos := ENNReal.ofReal_eq_zero.mp hzero
  exact (not_le_of_gt hpos) hnonpos

theorem comparisonMeasure_absolutelyContinuous_arcsineMeasure :
    comparisonMeasure ≪ arcsineMeasure := by
  have hbeta : betaMeasure 1 (1 / 2) ≪ betaMeasure (1 / 2) (1 / 2) :=
    betaMeasure_absolutelyContinuous_betaMeasure
      (by norm_num) (by norm_num)
  have hscale : MeasurableEmbedding (fun t : ℝ => t / 4) := by
    convert measurableEmbedding_mulRight₀
      (show (4 : ℝ)⁻¹ ≠ 0 by norm_num) using 1
    ext t
    simp [div_eq_mul_inv]
  exact hscale.absolutelyContinuous_map hbeta

theorem comparisonMeasure_eq_withDensity :
    comparisonMeasure = arcsineMeasure.withDensity
      (fun t => ENNReal.ofReal (Real.pi * Real.sqrt t)) := by
  simpa [comparisonMeasure, arcsineMeasure] using
    MetricCodes.Spherical.HigherHierarchy.Arcsine.betaMap_one_half_eq_withDensity

theorem comparisonMeasure_rnDeriv_arcsineMeasure :
    comparisonMeasure.rnDeriv arcsineMeasure =ᵐ[arcsineMeasure]
      fun t => ENNReal.ofReal (Real.pi * Real.sqrt t) := by
  rw [comparisonMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity arcsineMeasure (by fun_prop)

theorem comparisonMeasure_ae_mem_Ioo :
    ∀ᵐ t ∂comparisonMeasure, t ∈ Set.Ioo (0 : ℝ) endpoint := by
  unfold comparisonMeasure endpoint
  change ∀ᵐ t ∂(betaMeasure 1 (1 / 2)).map (fun t : ℝ => t / 4),
    0 < t ∧ t < (1 / 4 : ℝ)
  rw [ae_map_iff (by fun_prop) measurableSet_Ioo]
  filter_upwards [betaMeasure_ae_mem_Ioo] with t ht
  constructor <;> nlinarith [ht.1, ht.2]

theorem arcsineMeasure_ae_mem_Ioo :
    ∀ᵐ t ∂arcsineMeasure, t ∈ Set.Ioo (0 : ℝ) endpoint := by
  unfold arcsineMeasure endpoint
  change ∀ᵐ t ∂(betaMeasure (1 / 2) (1 / 2)).map (fun t : ℝ => t / 4),
    0 < t ∧ t < (1 / 4 : ℝ)
  rw [ae_map_iff (by fun_prop) measurableSet_Ioo]
  filter_upwards [betaMeasure_ae_mem_Ioo] with t ht
  constructor <;> nlinarith [ht.1, ht.2]

theorem comparison_logLikelihood_of_density
    (hdensity : comparisonMeasure.rnDeriv arcsineMeasure =ᵐ[arcsineMeasure]
      fun t => ENNReal.ofReal (Real.pi * Real.sqrt t)) :
    llr comparisonMeasure arcsineMeasure =ᵐ[comparisonMeasure]
      fun t => Real.log Real.pi + Real.log t / 2 := by
  have hdensity' := comparisonMeasure_absolutelyContinuous_arcsineMeasure.ae_le hdensity
  filter_upwards [hdensity', comparisonMeasure_ae_mem_Ioo] with t ht htpos
  unfold llr
  rw [ht, ENNReal.toReal_ofReal (mul_nonneg Real.pi_pos.le (Real.sqrt_nonneg _)),
    Real.log_mul Real.pi_pos.ne' (Real.sqrt_pos.mpr htpos.1).ne',
    Real.log_sqrt htpos.1.le]

theorem comparison_logLikelihood_integrable_of_density
    (hdensity : comparisonMeasure.rnDeriv arcsineMeasure =ᵐ[arcsineMeasure]
      fun t => ENNReal.ofReal (Real.pi * Real.sqrt t))
    (hlog : Integrable (fun t : ℝ => Real.log t) comparisonMeasure) :
    Integrable (llr comparisonMeasure arcsineMeasure) comparisonMeasure := by
  rw [integrable_congr (comparison_logLikelihood_of_density hdensity)]
  exact (integrable_const _).add (hlog.div_const 2)

theorem comparison_logLikelihood_integrable
    (hlog : Integrable (fun t : ℝ => Real.log t) comparisonMeasure) :
    Integrable (llr comparisonMeasure arcsineMeasure) comparisonMeasure :=
  comparison_logLikelihood_integrable_of_density
    comparisonMeasure_rnDeriv_arcsineMeasure hlog

theorem comparison_relativeEntropy_eq_log_pi_sub_one_of_density
    (hdensity : comparisonMeasure.rnDeriv arcsineMeasure =ᵐ[arcsineMeasure]
      fun t => ENNReal.ofReal (Real.pi * Real.sqrt t))
    (hlog : Integrable (fun t : ℝ => Real.log t) comparisonMeasure)
    (hmoment : (∫ t, Real.log t ∂comparisonMeasure) = -2) :
    (InformationTheory.klDiv comparisonMeasure arcsineMeasure).toReal =
      Real.log Real.pi - 1 := by
  rw [InformationTheory.toReal_klDiv_of_measure_eq
    comparisonMeasure_absolutelyContinuous_arcsineMeasure (by simp)]
  rw [integral_congr_ae (comparison_logLikelihood_of_density hdensity)]
  rw [integral_add (integrable_const _) (hlog.div_const 2),
    integral_const, probReal_univ, one_smul, integral_div, hmoment]
  ring

theorem comparison_relativeEntropy_eq_log_pi_sub_one
    (hlog : Integrable (fun t : ℝ => Real.log t) comparisonMeasure)
    (hmoment : (∫ t, Real.log t ∂comparisonMeasure) = -2) :
    (InformationTheory.klDiv comparisonMeasure arcsineMeasure).toReal =
      Real.log Real.pi - 1 :=
  comparison_relativeEntropy_eq_log_pi_sub_one_of_density
    comparisonMeasure_rnDeriv_arcsineMeasure hlog hmoment

theorem comparison_log_integrable_of_logMoment
    (hmoment : (∫ t, Real.log t ∂comparisonMeasure) = -2) :
    Integrable (fun t : ℝ => Real.log t) comparisonMeasure := by
  by_contra h
  have hzero := integral_undef h
  rw [hmoment] at hzero
  norm_num at hzero

def phaseNormalizer (K : ℝ → ℝ) : ℝ :=
  ∫ t, Real.exp (-K t) ∂arcsineMeasure

def phaseTilt (K : ℝ → ℝ) : Measure ℝ :=
  arcsineMeasure.tilted (fun t => -K t)

theorem phaseNormalizer_pos {K : ℝ → ℝ}
    (hK : Integrable (fun t => Real.exp (-K t)) arcsineMeasure) :
    0 < phaseNormalizer K := by
  exact integral_exp_pos hK

theorem toReal_klDiv_tilted_eq {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α → ℝ} (hμν : μ ≪ ν)
    (hfμ : Integrable f μ)
    (hfν : Integrable (fun x => Real.exp (f x)) ν)
    (hllr : Integrable (llr μ ν) μ) :
    (InformationTheory.klDiv μ (ν.tilted f)).toReal =
      (InformationTheory.klDiv μ ν).toReal - ∫ x, f x ∂μ +
        Real.log (∫ x, Real.exp (f x) ∂ν) := by
  letI : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted hfν
  have hac : μ ≪ ν.tilted f :=
    hμν.trans (absolutelyContinuous_tilted hfν)
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac (by simp),
    InformationTheory.toReal_klDiv_of_measure_eq hμν (by simp)]
  exact integral_llr_tilted_right hμν hfμ hfν hllr

theorem phase_relativeEntropy_eq_base_add_phase {K : ℝ → ℝ}
    (hac : comparisonMeasure ≪ arcsineMeasure)
    (hphase : Integrable K comparisonMeasure)
    (htilt : Integrable (fun t => Real.exp (-K t)) arcsineMeasure)
    (hllr : Integrable (llr comparisonMeasure arcsineMeasure) comparisonMeasure) :
    (InformationTheory.klDiv comparisonMeasure (phaseTilt K)).toReal =
      (InformationTheory.klDiv comparisonMeasure arcsineMeasure).toReal +
        (∫ t, K t ∂comparisonMeasure) + Real.log (phaseNormalizer K) := by
  have h := toReal_klDiv_tilted_eq comparisonMeasure arcsineMeasure
    hac hphase.neg htilt hllr
  change (InformationTheory.klDiv comparisonMeasure (phaseTilt K)).toReal =
    (InformationTheory.klDiv comparisonMeasure arcsineMeasure).toReal -
      (∫ x, -K x ∂comparisonMeasure) +
        Real.log (∫ x, Real.exp (-K x) ∂arcsineMeasure) at h
  rw [integral_neg] at h
  simpa [phaseNormalizer] using h

def packingObjective (Γ Φ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 (2 / (1 - 2 * Γ)) - Φ

def limitingPackingExponent : ℝ := CohnElkies.criticalBinaryExponent

theorem limitingPackingExponent_sub_packingObjective_eq
    {Γ Φ Z : ℝ} (hZ : 0 < Z) (hΓ : Z = 1 - 2 * Γ) :
    limitingPackingExponent - packingObjective Γ Φ =
      (Real.log Real.pi - 1 + 2 * Real.log 2 * Φ + Real.log Z) /
        (2 * Real.log 2) := by
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hcritical :
      Real.log (2 * Real.pi / Real.exp 1) =
        Real.log 2 + Real.log Real.pi - 1 := by
    rw [Real.log_div (mul_ne_zero htwo hpi) (Real.exp_pos 1).ne',
      Real.log_mul htwo hpi, Real.log_exp]
  have hscale : Real.log (2 / Z) = Real.log 2 - Real.log Z := by
    rw [Real.log_div htwo hZ.ne']
  unfold limitingPackingExponent packingObjective
  rw [CohnElkies.criticalBinaryExponent_eq_log_div, ← hΓ, Real.logb, hcritical,
    hscale]
  field_simp
  ring

theorem packingExponent_deficit_eq_relativeEntropy {Γ Φ : ℝ} {K : ℝ → ℝ}
    (hac : comparisonMeasure ≪ arcsineMeasure)
    (hphase : Integrable K comparisonMeasure)
    (htilt : Integrable (fun t => Real.exp (-K t)) arcsineMeasure)
    (hllr : Integrable (llr comparisonMeasure arcsineMeasure) comparisonMeasure)
    (hbase : (InformationTheory.klDiv comparisonMeasure arcsineMeasure).toReal =
      Real.log Real.pi - 1)
    (hnormalizer : phaseNormalizer K = 1 - 2 * Γ)
    (hphaseMoment : (∫ t, K t ∂comparisonMeasure) =
      2 * Real.log 2 * Φ) :
    limitingPackingExponent - packingObjective Γ Φ =
      (InformationTheory.klDiv comparisonMeasure (phaseTilt K)).toReal /
        (2 * Real.log 2) := by
  have hpositive := phaseNormalizer_pos htilt
  rw [limitingPackingExponent_sub_packingObjective_eq hpositive hnormalizer]
  rw [phase_relativeEntropy_eq_base_add_phase hac hphase htilt hllr,
    hbase, hphaseMoment]

theorem packingExponent_deficit_eq_relativeEntropy_of_logMoment
    {Γ Φ : ℝ} {K : ℝ → ℝ}
    (hlogMoment : (∫ t, Real.log t ∂comparisonMeasure) = -2)
    (hphase : Integrable K comparisonMeasure)
    (htilt : Integrable (fun t => Real.exp (-K t)) arcsineMeasure)
    (hnormalizer : phaseNormalizer K = 1 - 2 * Γ)
    (hphaseMoment : (∫ t, K t ∂comparisonMeasure) =
      2 * Real.log 2 * Φ) :
    limitingPackingExponent - packingObjective Γ Φ =
      (InformationTheory.klDiv comparisonMeasure (phaseTilt K)).toReal /
        (2 * Real.log 2) := by
  have hlog := comparison_log_integrable_of_logMoment hlogMoment
  exact packingExponent_deficit_eq_relativeEntropy
    comparisonMeasure_absolutelyContinuous_arcsineMeasure hphase htilt
    (comparison_logLikelihood_integrable hlog)
    (comparison_relativeEntropy_eq_log_pi_sub_one hlog hlogMoment)
    hnormalizer hphaseMoment

theorem packingObjective_le_limitingPackingExponent_of_logMoment
    {Γ Φ : ℝ} {K : ℝ → ℝ}
    (hlogMoment : (∫ t, Real.log t ∂comparisonMeasure) = -2)
    (hphase : Integrable K comparisonMeasure)
    (htilt : Integrable (fun t => Real.exp (-K t)) arcsineMeasure)
    (hnormalizer : phaseNormalizer K = 1 - 2 * Γ)
    (hphaseMoment : (∫ t, K t ∂comparisonMeasure) =
      2 * Real.log 2 * Φ) :
    packingObjective Γ Φ ≤ limitingPackingExponent := by
  have hgap := packingExponent_deficit_eq_relativeEntropy_of_logMoment
    hlogMoment hphase htilt hnormalizer hphaseMoment
  have hden : 0 < 2 * Real.log (2 : ℝ) := by
    exact mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hnonneg :
      0 ≤ (InformationTheory.klDiv comparisonMeasure (phaseTilt K)).toReal /
        (2 * Real.log 2) :=
    div_nonneg ENNReal.toReal_nonneg hden.le
  linarith

end MetricCodes.Spherical.HigherHierarchy.Entropy

end

section

noncomputable section

open Filter
open scoped Topology BigOperators Interval

namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic

def radiusNormalizer (R : ℝ) : ℝ :=
  (2 / Real.pi) * Real.arcsin (1 / Real.sqrt (4 * R + 1))

def radiusGamma (R : ℝ) : ℝ :=
  (1 - radiusNormalizer R) / 2

def radiusEntropy (R : ℝ) : ℝ :=
  MetricCodes.sphericalEntropy (inverseQuadratic R) / 2

def radiusPackingObjective (R : ℝ) : ℝ :=
  MetricCodes.Spherical.HigherHierarchy.Entropy.packingObjective
    (radiusGamma R) (radiusEntropy R)

theorem radiusNormalizer_pos {R : ℝ} (hR : 0 ≤ R) :
    0 < radiusNormalizer R := by
  unfold radiusNormalizer
  apply mul_pos (div_pos (by norm_num) Real.pi_pos)
  exact Real.arcsin_pos.mpr
    (div_pos (by norm_num) (Real.sqrt_pos.mpr (by nlinarith)))

theorem one_sub_two_mul_radiusGamma (R : ℝ) :
    1 - 2 * radiusGamma R = radiusNormalizer R := by
  unfold radiusGamma
  ring

theorem tendsto_inverseQuadratic_atTop :
    Tendsto inverseQuadratic atTop atTop := by
  unfold inverseQuadratic
  have hlinear : Tendsto (fun R : ℝ => 1 + 4 * R) atTop atTop := by
    exact tendsto_atTop_add_const_left atTop 1
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 4))
  have hroot : Tendsto (fun R : ℝ => Real.sqrt (1 + 4 * R)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlinear
  have hsub : Tendsto (fun R : ℝ => Real.sqrt (1 + 4 * R) + (-1))
      atTop atTop := tendsto_atTop_add_const_right atTop (-1) hroot
  simpa [sub_eq_add_neg] using
    hsub.atTop_div_const (by norm_num : (0 : ℝ) < 2)

theorem tendsto_arcsin_div_self_nhdsGT_zero :
    Tendsto (fun x : ℝ => Real.arcsin x / x)
      (𝓝[>] 0) (𝓝 1) := by
  have hderiv : HasDerivAt Real.arcsin 1 0 := by
    convert Real.hasDerivAt_arcsin (by norm_num : (0 : ℝ) ≠ -1)
      (by norm_num : (0 : ℝ) ≠ 1) using 1; norm_num
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using
    hderiv.tendsto_slope_zero_right

theorem inverseQuadratic_quadraticCoordinate {a : ℝ} (ha : 0 ≤ a) :
    inverseQuadratic (a * (1 + a)) = a := by
  unfold inverseQuadratic
  have hsquare : 1 + 4 * (a * (1 + a)) = (1 + 2 * a) ^ 2 := by
    ring
  rw [hsquare, Real.sqrt_sq (by linarith)]
  ring

theorem radiusNormalizer_quadraticCoordinate {a : ℝ} (ha : 0 ≤ a) :
    radiusNormalizer (a * (1 + a)) =
      (2 / Real.pi) * Real.arcsin (1 / (1 + 2 * a)) := by
  unfold radiusNormalizer
  have hsquare : 4 * (a * (1 + a)) + 1 = (1 + 2 * a) ^ 2 := by
    ring
  rw [hsquare, Real.sqrt_sq (by linarith)]

theorem log_two_mul_sphericalEntropy {a : ℝ} (ha : 0 < a) :
    Real.log 2 * MetricCodes.sphericalEntropy a =
      Real.log (1 + a) + a * Real.log (1 + 1 / a) := by
  rw [MetricCodes.sphericalEntropy_eq_log_add ha]
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hratio : (1 + a) / a = 1 + 1 / a := by
    field_simp
    ring
  unfold Real.logb
  rw [hratio]
  field_simp

def degreePackingObjective (a : ℝ) : ℝ :=
  (Real.log Real.pi + Real.log ((1 + 2 * a) / (1 + a)) -
      a * Real.log (1 + 1 / a) -
      Real.log (Real.arcsin (1 / (1 + 2 * a)) /
        (1 / (1 + 2 * a)))) /
    (2 * Real.log 2)

theorem radiusPackingObjective_quadraticCoordinate {a : ℝ} (ha : 0 < a) :
    radiusPackingObjective (a * (1 + a)) = degreePackingObjective a := by
  have ha' : 0 ≤ a := ha.le
  have hden : 0 < 1 + 2 * a := by linarith
  have hx : 0 < 1 / (1 + 2 * a) := by positivity
  have harcsin : 0 < Real.arcsin (1 / (1 + 2 * a)) :=
    Real.arcsin_pos.mpr hx
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hxne : 1 / (1 + 2 * a) ≠ 0 := hx.ne'
  have hlogratio :
      Real.log (1 + 2 * a) - Real.log (1 + a) =
        Real.log ((1 + 2 * a) / (1 + a)) := by
    rw [Real.log_div (by linarith : 1 + 2 * a ≠ 0)
      (by linarith : 1 + a ≠ 0)]
  have harcsin_factor :
      Real.arcsin (1 / (1 + 2 * a)) =
        (1 / (1 + 2 * a)) *
          (Real.arcsin (1 / (1 + 2 * a)) / (1 / (1 + 2 * a))) := by
    field_simp
  have hratio_pos :
      0 < Real.arcsin (1 / (1 + 2 * a)) / (1 / (1 + 2 * a)) :=
    div_pos harcsin hx
  have hlogarcsin :
      Real.log (Real.arcsin (1 / (1 + 2 * a))) =
        -Real.log (1 + 2 * a) +
          Real.log (Real.arcsin (1 / (1 + 2 * a)) /
            (1 / (1 + 2 * a))) := by
    nth_rewrite 1 [harcsin_factor]
    rw [Real.log_mul hxne hratio_pos.ne']
    simp [one_div, Real.log_inv]
  unfold radiusPackingObjective
    MetricCodes.Spherical.HigherHierarchy.Entropy.packingObjective
  rw [one_sub_two_mul_radiusGamma,
    radiusNormalizer_quadraticCoordinate ha',
    radiusEntropy, inverseQuadratic_quadraticCoordinate ha']
  have hdivision :
      2 / ((2 / Real.pi) * Real.arcsin (1 / (1 + 2 * a))) =
        Real.pi / Real.arcsin (1 / (1 + 2 * a)) := by
    field_simp
  rw [hdivision, Real.logb,
    Real.log_div hpi harcsin.ne', hlogarcsin]
  unfold degreePackingObjective
  rw [← hlogratio]
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hentropy :
      MetricCodes.sphericalEntropy a =
        (Real.log (1 + a) + a * Real.log (1 + 1 / a)) / Real.log 2 := by
    apply (eq_div_iff hlog).mpr
    nlinarith [log_two_mul_sphericalEntropy ha]
  rw [hentropy]
  ring

theorem tendsto_inverse_double_degree_nhdsGT_zero :
    Tendsto (fun a : ℝ => 1 / (1 + 2 * a)) atTop (𝓝[>] 0) := by
  have hlinear : Tendsto (fun a : ℝ => 1 + 2 * a) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hzero : Tendsto (fun a : ℝ => 1 / (1 + 2 * a)) atTop (𝓝 0) := by
    convert tendsto_inv_atTop_zero.comp hlinear using 1
    ext a
    simp [one_div]
  rw [tendsto_nhdsWithin_iff]
  refine ⟨hzero, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  change 0 < 1 / (1 + 2 * a)
  positivity

theorem tendsto_log_arcsin_correction :
    Tendsto (fun a : ℝ =>
      Real.log (Real.arcsin (1 / (1 + 2 * a)) /
        (1 / (1 + 2 * a)))) atTop (𝓝 0) := by
  have hratio := tendsto_arcsin_div_self_nhdsGT_zero.comp
    tendsto_inverse_double_degree_nhdsGT_zero
  convert (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
    hratio using 1
  · ext a
    rfl
  · norm_num

theorem tendsto_degree_ratio :
    Tendsto (fun a : ℝ => (1 + 2 * a) / (1 + a)) atTop (𝓝 2) := by
  have hinv : Tendsto (fun a : ℝ => a⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hratio :
      Tendsto (fun a : ℝ => (a⁻¹ + 2) / (a⁻¹ + 1)) atTop (𝓝 2) := by
    convert (hinv.add_const 2).div (hinv.add_const 1)
      (by norm_num : (0 : ℝ) + 1 ≠ 0) using 1
    · ext a
      rfl
    · norm_num
  apply hratio.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  field_simp

theorem tendsto_degreePackingObjective :
    Tendsto degreePackingObjective atTop
      (𝓝 CohnElkies.criticalBinaryExponent) := by
  have hlogratio :
      Tendsto (fun a : ℝ => Real.log ((1 + 2 * a) / (1 + a)))
        atTop (𝓝 (Real.log 2)) :=
    (Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp
      tendsto_degree_ratio
  have hentropy :
      Tendsto (fun a : ℝ => a * Real.log (1 + 1 / a)) atTop (𝓝 1) :=
    Real.tendsto_mul_log_one_add_div_atTop 1
  have hconstant : Tendsto (fun _ : ℝ => Real.log Real.pi) atTop
      (𝓝 (Real.log Real.pi)) := tendsto_const_nhds
  have hlimit :
      Tendsto (fun a : ℝ =>
        (Real.log Real.pi + Real.log ((1 + 2 * a) / (1 + a)) -
          a * Real.log (1 + 1 / a) -
          Real.log (Real.arcsin (1 / (1 + 2 * a)) /
            (1 / (1 + 2 * a)))) / (2 * Real.log 2)) atTop
        (𝓝 ((Real.log Real.pi + Real.log 2 - 1 - 0) /
          (2 * Real.log 2))) :=
    (((hconstant.add hlogratio).sub hentropy).sub
      tendsto_log_arcsin_correction).div_const (2 * Real.log 2)
  have hcritical :
      (Real.log Real.pi + Real.log 2 - 1 - 0) /
          (2 * Real.log 2) = CohnElkies.criticalBinaryExponent := by
    rw [CohnElkies.criticalBinaryExponent_eq_log_div,
      Real.log_div (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
        Real.pi_pos.ne') (Real.exp_pos 1).ne',
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_pos.ne',
      Real.log_exp]
    ring
  change Tendsto (fun a : ℝ =>
    (Real.log Real.pi + Real.log ((1 + 2 * a) / (1 + a)) -
      a * Real.log (1 + 1 / a) -
      Real.log (Real.arcsin (1 / (1 + 2 * a)) /
        (1 / (1 + 2 * a)))) / (2 * Real.log 2)) atTop
      (𝓝 CohnElkies.criticalBinaryExponent)
  rw [← hcritical]
  exact hlimit

theorem tendsto_radiusPackingObjective :
    Tendsto radiusPackingObjective atTop
      (𝓝 CohnElkies.criticalBinaryExponent) := by
  have hlimit := tendsto_degreePackingObjective.comp
    tendsto_inverseQuadratic_atTop
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hdegree : 0 < inverseQuadratic R := by
    have hsquare := quadraticCoordinate_inverseQuadratic hR.le
    have hnonneg := inverseQuadratic_nonneg hR.le
    by_contra hnot
    have hzero : inverseQuadratic R = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
    simp [hzero, MetricCodes.Spherical.HigherHierarchy.quadraticCoordinate] at hsquare
    linarith
  have hquadratic := quadraticCoordinate_inverseQuadratic hR.le
  unfold MetricCodes.Spherical.HigherHierarchy.quadraticCoordinate at hquadratic
  change degreePackingObjective (inverseQuadratic R) = radiusPackingObjective R
  symm
  calc
    radiusPackingObjective R =
        radiusPackingObjective
          (inverseQuadratic R * (1 + inverseQuadratic R)) := by rw [hquadratic]
    _ = degreePackingObjective (inverseQuadratic R) :=
      radiusPackingObjective_quadraticCoordinate hdegree

def midpointAverage (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  (∑ i ∈ Finset.range N, f (((i : ℝ) + 1 / 2) / N)) / N

theorem midpointAverage_integral_error_le
    {f : ℝ → ℝ} (hf : AntitoneOn f (Set.Icc (0 : ℝ) 1))
    {N : ℕ} (hN : 0 < N) :
    |midpointAverage f N - ∫ x in (0 : ℝ)..1, f x| ≤
      (f 0 - f 1) / N := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hscaled :
      AntitoneOn (fun x : ℝ => f (x / (N : ℝ)))
        (Set.Icc (0 : ℝ) (N : ℝ)) := by
    intro x hx y hy hxy
    apply hf
    · exact ⟨div_nonneg hx.1 hN'.le, (div_le_one hN').mpr hx.2⟩
    · exact ⟨div_nonneg hy.1 hN'.le, (div_le_one hN').mpr hy.2⟩
    · exact (div_le_div_iff_of_pos_right hN').mpr hxy
  have hleft_raw := AntitoneOn.integral_le_sum (a := N) (x₀ := (0 : ℝ))
    (f := fun x : ℝ => f (x / (N : ℝ))) (by simpa using hscaled)
  have hright_raw := AntitoneOn.sum_le_integral (a := N) (x₀ := (0 : ℝ))
    (f := fun x : ℝ => f (x / (N : ℝ))) (by simpa using hscaled)
  have hintegral :
      (∫ x in (0 : ℝ)..(N : ℝ), f (x / (N : ℝ))) =
        (N : ℝ) * ∫ x in (0 : ℝ)..1, f x := by
    rw [intervalIntegral.integral_comp_div f hN'.ne']
    simp [hN'.ne', smul_eq_mul]
  have hleft :
      (N : ℝ) * (∫ x in (0 : ℝ)..1, f x) ≤
        ∑ i ∈ Finset.range N, f ((i : ℝ) / N) := by
    simpa [hintegral] using hleft_raw
  have hright :
      (∑ i ∈ Finset.range N, f (((i : ℝ) + 1) / N)) ≤
        (N : ℝ) * (∫ x in (0 : ℝ)..1, f x) := by
    simpa [hintegral, Nat.cast_add, Nat.cast_one] using hright_raw
  have hmid_left :
      (∑ i ∈ Finset.range N, f (((i : ℝ) + 1 / 2) / N)) ≤
        ∑ i ∈ Finset.range N, f ((i : ℝ) / N) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i < N := Finset.mem_range.mp hi
    apply hf
    · constructor
      · positivity
      · apply (div_le_one hN').mpr
        exact_mod_cast (Nat.le_of_lt hi')
    · constructor
      · positivity
      · apply (div_le_one hN').mpr
        have hicast : (i : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt hi'
        linarith
    · exact (div_le_div_iff_of_pos_right hN').mpr (by linarith)
  have hmid_right :
      (∑ i ∈ Finset.range N, f (((i : ℝ) + 1) / N)) ≤
        ∑ i ∈ Finset.range N, f (((i : ℝ) + 1 / 2) / N) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i < N := Finset.mem_range.mp hi
    apply hf
    · constructor
      · positivity
      · apply (div_le_one hN').mpr
        have hicast : (i : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt hi'
        linarith
    · constructor
      · positivity
      · apply (div_le_one hN').mpr
        exact_mod_cast Nat.succ_le_of_lt hi'
    · exact (div_le_div_iff_of_pos_right hN').mpr (by linarith)
  have hgap :
      (∑ i ∈ Finset.range N, f ((i : ℝ) / N)) -
        (∑ i ∈ Finset.range N, f (((i : ℝ) + 1) / N)) = f 0 - f 1 := by
    rw [← Finset.sum_sub_distrib]
    have htel := Finset.sum_range_sub' (fun i : ℕ => f ((i : ℝ) / N)) N
    simpa [Nat.cast_add, Nat.cast_one, hN'.ne'] using htel
  unfold midpointAverage
  apply abs_le.mpr
  have hrewrite :
      (∑ i ∈ Finset.range N, f (((i : ℝ) + 1 / 2) / N)) / N -
          (∫ x in (0 : ℝ)..1, f x) =
        ((∑ i ∈ Finset.range N, f (((i : ℝ) + 1 / 2) / N)) -
          (N : ℝ) * (∫ x in (0 : ℝ)..1, f x)) / N := by
    rw [sub_div, mul_div_cancel_left₀ _ hN'.ne']
  constructor
  · rw [hrewrite, ← neg_div]
    apply (div_le_div_iff_of_pos_right hN').mpr
    nlinarith
  · rw [hrewrite]
    apply (div_le_div_iff_of_pos_right hN').mpr
    nlinarith

theorem tendsto_midpointAverage_integral
    {f : ℝ → ℝ} (hf : AntitoneOn f (Set.Icc (0 : ℝ) 1)) :
    Tendsto (midpointAverage f) atTop (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  refine squeeze_zero' (g := fun N : ℕ => (f 0 - f 1) / N)
    (Eventually.of_forall fun _ => abs_nonneg _) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact midpointAverage_integral_error_le hf hN
  · exact (tendsto_const_div_atTop_nhds_zero_nat (f 0 - f 1))

end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic

end

section

noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature

def midpointCorrection (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N,
    (f (((i : ℝ) + 1 / 2) / N) -
      (f ((i : ℝ) / N) + f (((i : ℝ) + 1) / N)) / 2)

def midpointEndpointDifference (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  (∑ i ∈ Finset.range N, f (((i : ℝ) + 1 / 2) / N)) -
    ∑ i ∈ Finset.range (N - 1), f (((i : ℝ) + 1) / N)

theorem midpoint_error_eq_derivative_difference
    {f g : ℝ → ℝ} {x y : ℝ} (hxy : x < y)
    (hf : ContinuousOn f (Set.Icc x y))
    (hderiv : ∀ z ∈ Set.Ioo x y, HasDerivAt f (g z) z) :
    ∃ u ∈ Set.Ioo x ((x + y) / 2),
      ∃ v ∈ Set.Ioo ((x + y) / 2) y,
        f ((x + y) / 2) - (f x + f y) / 2 =
          ((y - x) / 4) * (g u - g v) := by
  let m : ℝ := (x + y) / 2
  have hxm : x < m := by dsimp [m]; linarith
  have hmy : m < y := by dsimp [m]; linarith
  obtain ⟨u, hu, hfu⟩ := exists_hasDerivAt_eq_slope f g hxm
    (hf.mono (by intro z hz; exact ⟨hz.1, hz.2.trans hmy.le⟩))
    (by
      intro z hz
      exact hderiv z ⟨hz.1, hz.2.trans hmy⟩)
  obtain ⟨v, hv, hfv⟩ := exists_hasDerivAt_eq_slope f g hmy
    (hf.mono (by intro z hz; exact ⟨hxm.le.trans hz.1, hz.2⟩))
    (by
      intro z hz
      exact hderiv z ⟨hxm.trans hz.1, hz.2⟩)
  refine ⟨u, hu, v, hv, ?_⟩
  have hleft := (eq_div_iff (sub_ne_zero.mpr hxm.ne')).mp hfu
  have hright := (eq_div_iff (sub_ne_zero.mpr hmy.ne')).mp hfv
  dsimp [m] at hleft hright ⊢
  nlinarith

theorem midpointCorrection_abs_lt_of_uniform_derivative
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hderiv : ∀ x ∈ Set.Ioo 0 1, HasDerivAt f (g x) x)
    {ε δ : ℝ} (hε : 0 < ε)
    (huniform : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        dist x y < δ → dist (g x) (g y) < ε)
    {N : ℕ} (hN : 0 < N) (hmesh : 1 / (N : ℝ) < δ) :
    |midpointCorrection f N| < ε := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hterm : ∀ i ∈ Finset.range N,
      |f (((i : ℝ) + 1 / 2) / N) -
        (f ((i : ℝ) / N) + f (((i : ℝ) + 1) / N)) / 2| <
          ε / (4 * N) := by
    intro i hi
    have hi' : i < N := Finset.mem_range.mp hi
    have hi_cast : (i : ℝ) < N := by exact_mod_cast hi'
    let x : ℝ := (i : ℝ) / N
    let y : ℝ := ((i : ℝ) + 1) / N
    have hx0 : 0 ≤ x := by dsimp [x]; positivity
    have hy1 : y ≤ 1 := by
      dsimp [y]
      apply (div_le_one hN').mpr
      have hi_succ : i + 1 ≤ N := Nat.succ_le_of_lt hi'
      exact_mod_cast hi_succ
    have hxy : x < y := by
      dsimp [x, y]
      exact (div_lt_div_iff_of_pos_right hN').mpr (by linarith)
    have hsub : Set.Icc x y ⊆ Set.Icc (0 : ℝ) 1 := by
      intro z hz
      exact ⟨hx0.trans hz.1, hz.2.trans hy1⟩
    obtain ⟨u, hu, v, hv, heq⟩ :=
      midpoint_error_eq_derivative_difference hxy (hf.mono hsub)
        (by
          intro z hz
          exact hderiv z ⟨lt_of_le_of_lt hx0 hz.1,
            lt_of_lt_of_le hz.2 hy1⟩)
    have huI : u ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hx0.trans hu.1.le, ((hu.2.trans hv.1).trans hv.2).le.trans hy1⟩
    have hvI : v ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hx0.trans ((hu.1.trans hu.2).trans hv.1).le, hv.2.le.trans hy1⟩
    have huv : u < v := hu.2.trans hv.1
    have hwidth : y - x = 1 / (N : ℝ) := by
      dsimp [x, y]
      ring
    have hdist : dist u v < δ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith : u - v ≤ 0)]
      have hdiff : v - u < y - x := by linarith [hu.1, hv.2]
      rw [hwidth] at hdiff
      linarith
    have hderivdiff : |g u - g v| < ε := by
      simpa [Real.dist_eq] using huniform u huI v hvI hdist
    have hmid : (x + y) / 2 = ((i : ℝ) + 1 / 2) / N := by
      dsimp [x, y]
      ring
    rw [← hmid, heq, abs_mul, abs_of_pos (by linarith : 0 < (y - x) / 4)]
    calc
      ((y - x) / 4) * |g u - g v| < ((y - x) / 4) * ε :=
        mul_lt_mul_of_pos_left hderivdiff (by linarith)
      _ = ε / (4 * N) := by rw [hwidth]; ring
  have hsum :
      (∑ i ∈ Finset.range N,
        |f (((i : ℝ) + 1 / 2) / N) -
          (f ((i : ℝ) / N) + f (((i : ℝ) + 1) / N)) / 2|) <
        ε / 4 := by
    have hstrict := Finset.sum_lt_sum_of_nonempty
      (Finset.nonempty_range_iff.mpr hN.ne') hterm
    calc
      (∑ i ∈ Finset.range N,
        |f (((i : ℝ) + 1 / 2) / N) -
          (f ((i : ℝ) / N) + f (((i : ℝ) + 1) / N)) / 2|) <
        ∑ _i ∈ Finset.range N, ε / (4 * N) := hstrict
      _ = ε / 4 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
  calc
    |midpointCorrection f N| ≤
        ∑ i ∈ Finset.range N,
          |f (((i : ℝ) + 1 / 2) / N) -
            (f ((i : ℝ) / N) + f (((i : ℝ) + 1) / N)) / 2| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ < ε / 4 := hsum
    _ < ε := by linarith

theorem tendsto_midpointCorrection_zero
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hg : ContinuousOn g (Set.Icc 0 1))
    (hderiv : ∀ x ∈ Set.Ioo 0 1, HasDerivAt f (g x) x) :
    Tendsto (midpointCorrection f) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, huniform⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hg) ε hε
  have hevent : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) < δ :=
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).eventually
      (gt_mem_nhds hδ)
  obtain ⟨N₀, hN₀⟩ := hevent.exists_forall_of_atTop
  refine ⟨max N₀ 1, ?_⟩
  intro N hN
  have hpositive : 0 < N := by omega
  have hmesh : 1 / (N : ℝ) < δ := hN₀ N (by omega)
  rw [Real.dist_eq, sub_zero]
  exact midpointCorrection_abs_lt_of_uniform_derivative
    hf hderiv hε huniform hpositive hmesh

theorem midpointEndpointDifference_eq_correction_add
    (f : ℝ → ℝ) {N : ℕ} (hN : 0 < N) :
    midpointEndpointDifference f N =
      midpointCorrection f N + (f 0 + f 1) / 2 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpred : N - 1 + 1 = N := Nat.sub_add_cancel hN
  have hshift : ∀ k : ℕ,
      (∑ i ∈ Finset.range (k + 1), f ((i : ℝ) / N)) =
        f 0 + ∑ i ∈ Finset.range k, f (((i : ℝ) + 1) / N) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp [Nat.cast_add, Nat.cast_one, add_assoc]
  have hleft :
      (∑ i ∈ Finset.range N, f ((i : ℝ) / N)) =
        f 0 + ∑ i ∈ Finset.range (N - 1), f (((i : ℝ) + 1) / N) := by
    simpa [hpred] using hshift (N - 1)
  have hright :
      (∑ i ∈ Finset.range N, f (((i : ℝ) + 1) / N)) =
        (∑ i ∈ Finset.range (N - 1), f (((i : ℝ) + 1) / N)) + f 1 := by
    have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
      exact_mod_cast hpred
    have hsum := Finset.sum_range_succ
      (fun i : ℕ => f (((i : ℝ) + 1) / N)) (N - 1)
    simpa [hpred, Nat.cast_add, Nat.cast_one, hcast, hN'] using hsum
  unfold midpointEndpointDifference midpointCorrection
  rw [Finset.sum_sub_distrib]
  have hsplit :
      (∑ i ∈ Finset.range N,
        (f ((i : ℝ) / N) + f (((i : ℝ) + 1) / N)) / 2) =
        ((∑ i ∈ Finset.range N, f ((i : ℝ) / N)) +
          (∑ i ∈ Finset.range N, f (((i : ℝ) + 1) / N))) / 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_div]
  rw [hsplit, hleft, hright]
  ring

theorem tendsto_midpointEndpointDifference
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hg : ContinuousOn g (Set.Icc 0 1))
    (hderiv : ∀ x ∈ Set.Ioo 0 1, HasDerivAt f (g x) x) :
    Tendsto (midpointEndpointDifference f) atTop
      (𝓝 ((f 0 + f 1) / 2)) := by
  have hsum := (tendsto_midpointCorrection_zero hf hg hderiv).add_const
    ((f 0 + f 1) / 2)
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact (midpointEndpointDifference_eq_correction_add f hN).symm

end MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature

end

section

noncomputable section

open Filter
open MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature
open scoped BigOperators Topology Interval

namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic

private def angularCos (t : ℝ) : ℝ := Real.cos (Real.pi * t / 2)

private def angularSin (t : ℝ) : ℝ := Real.sin (Real.pi * t / 2)

private def angularCoordinate (R t : ℝ) : ℝ := R * angularCos t ^ 2

private def angularDegree (R t : ℝ) : ℝ := inverseQuadratic (angularCoordinate R t)

private def angularScale (R t : ℝ) : ℝ :=
  2 * R / (Real.sqrt (1 + 4 * angularCoordinate R t) + 1)

private def angularEntropy (R t : ℝ) : ℝ :=
  MetricCodes.sphericalEntropy (angularDegree R t)

private def angularEntropyDerivative (R t : ℝ) : ℝ :=
  -(R * Real.pi * angularSin t) /
    (Real.sqrt (1 + 4 * angularCoordinate R t) * Real.log 2) *
      (angularCos t * Real.log (1 + angularDegree R t) -
        angularCos t * Real.log (angularScale R t) -
        2 * (angularCos t * Real.log (angularCos t)))

private theorem angularCoordinate_nonneg {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    0 ≤ angularCoordinate R t := by
  unfold angularCoordinate
  positivity

private theorem angularScale_pos {R : ℝ} (hR : 0 < R) (t : ℝ) :
    0 < angularScale R t := by
  unfold angularScale
  positivity

private theorem angularDegree_nonneg {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    0 ≤ angularDegree R t :=
  inverseQuadratic_nonneg (angularCoordinate_nonneg hR t)

private theorem angularDegree_eq_scale {R : ℝ} (hR : 0 < R) (t : ℝ) :
    angularDegree R t = angularCos t ^ 2 * angularScale R t := by
  have hsquare :
      Real.sqrt (1 + 4 * R * angularCos t ^ 2) ^ 2 =
        1 + 4 * R * angularCos t ^ 2 := by
    apply Real.sq_sqrt
    positivity
  unfold angularDegree inverseQuadratic angularScale angularCoordinate
  field_simp
  nlinarith

private theorem angularCos_pos {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    0 < angularCos t := by
  unfold angularCos
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · nlinarith [Real.pi_pos, mul_pos Real.pi_pos ht.1]
  · nlinarith [Real.pi_pos, mul_lt_mul_of_pos_left ht.2 Real.pi_pos]

private theorem angularDegree_pos {R t : ℝ} (hR : 0 < R)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) : 0 < angularDegree R t := by
  rw [angularDegree_eq_scale hR t]
  exact mul_pos (sq_pos_of_pos (angularCos_pos ht)) (angularScale_pos hR t)

private theorem hasDerivAt_inverseQuadratic {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt inverseQuadratic
      (1 / Real.sqrt (1 + 4 * x)) x := by
  have hrad : 0 < 1 + 4 * x := by linarith
  have hinner : HasDerivAt (fun y : ℝ => 1 + 4 * y) 4 x := by
    convert (hasDerivAt_const x 1).add ((hasDerivAt_id x).const_mul 4)
      using 1 <;> first | rfl | ring
  have hsqrt := hinner.sqrt hrad.ne'
  have hresult := (hsqrt.sub_const 1).div_const 2
  unfold inverseQuadratic
  convert hresult using 1 <;> first | rfl | ring

private theorem hasDerivAt_angularCos (t : ℝ) :
    HasDerivAt angularCos (-angularSin t * (Real.pi / 2)) t := by
  unfold angularCos angularSin
  convert (Real.hasDerivAt_cos (Real.pi * t / 2)).comp t
    (((hasDerivAt_id t).const_mul Real.pi).div_const 2) using 1 <;>
      first | rfl | ring

private theorem hasDerivAt_angularCoordinate (R t : ℝ) :
    HasDerivAt (angularCoordinate R)
      (-(R * Real.pi * angularCos t * angularSin t)) t := by
  unfold angularCoordinate
  convert ((hasDerivAt_angularCos t).pow 2).const_mul R using 1 <;>
    first | rfl | ring

private theorem hasDerivAt_angularDegree {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    HasDerivAt (angularDegree R)
      (-(R * Real.pi * angularCos t * angularSin t) /
        Real.sqrt (1 + 4 * angularCoordinate R t)) t := by
  unfold angularDegree
  convert (hasDerivAt_inverseQuadratic (angularCoordinate_nonneg hR t)).comp t
    (hasDerivAt_angularCoordinate R t) using 1 <;>
      first | rfl | ring

private theorem hasDerivAt_angularEntropy {R t : ℝ} (hR : 0 < R)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (angularEntropy R) (angularEntropyDerivative R t) t := by
  have hdegree := angularDegree_pos hR ht
  have hscale := angularScale_pos hR t
  have hcos := angularCos_pos ht
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hderiv :=
    (MetricCodes.Spherical.hasDerivAt_sphericalEntropy hdegree).comp t
      (hasDerivAt_angularDegree hR.le t)
  have hlogdegree :
      Real.log (angularDegree R t) =
        2 * Real.log (angularCos t) + Real.log (angularScale R t) := by
    rw [angularDegree_eq_scale hR t,
      Real.log_mul (pow_ne_zero 2 hcos.ne') hscale.ne', Real.log_pow]
    norm_num
  have hscalar : angularEntropyDerivative R t =
      Real.logb 2 ((1 + angularDegree R t) / angularDegree R t) *
        (-(R * Real.pi * angularCos t * angularSin t) /
          Real.sqrt (1 + 4 * angularCoordinate R t)) := by
    unfold angularEntropyDerivative Real.logb
    rw [Real.log_div (by positivity : 1 + angularDegree R t ≠ 0) hdegree.ne',
      hlogdegree]
    ring
  unfold angularEntropy
  rw [hscalar]
  exact hderiv

private theorem angularEntropy_continuous (R : ℝ) :
    Continuous (angularEntropy R) := by
  have hdegree : Continuous (angularDegree R) := by
    unfold angularDegree inverseQuadratic angularCoordinate angularCos
    fun_prop
  exact MetricCodes.Spherical.sphericalEntropy_continuous.comp hdegree

private theorem angularEntropyDerivative_continuous {R : ℝ} (hR : 0 < R) :
    Continuous (angularEntropyDerivative R) := by
  have hcos : Continuous angularCos := by
    unfold angularCos
    fun_prop
  have hsin : Continuous angularSin := by
    unfold angularSin
    fun_prop
  have hcoord : Continuous (angularCoordinate R) := by
    unfold angularCoordinate
    fun_prop
  have hdegree : Continuous (angularDegree R) := by
    unfold angularDegree inverseQuadratic
    fun_prop
  have hscale : Continuous (angularScale R) := by
    unfold angularScale
    apply Continuous.div continuous_const
      ((Real.continuous_sqrt.comp (continuous_const.add (hcoord.const_mul 4))).add
        continuous_const)
    intro t
    have hroot := Real.sqrt_nonneg (1 + 4 * angularCoordinate R t)
    change Real.sqrt (1 + 4 * angularCoordinate R t) + 1 ≠ 0
    linarith
  have hlogdegree : Continuous (fun t => Real.log (1 + angularDegree R t)) := by
    apply Continuous.log (continuous_const.add hdegree)
    intro t
    change 1 + angularDegree R t ≠ 0
    have hnonneg := angularDegree_nonneg hR.le t
    linarith
  have hlogscale : Continuous (fun t => Real.log (angularScale R t)) := by
    apply Continuous.log hscale
    intro t
    exact (angularScale_pos hR t).ne'
  have hcoslog : Continuous (fun t => angularCos t * Real.log (angularCos t)) :=
    Real.continuous_mul_log.comp hcos
  unfold angularEntropyDerivative
  have hroot : Continuous (fun t => Real.sqrt (1 + 4 * angularCoordinate R t)) :=
    Real.continuous_sqrt.comp (continuous_const.add (hcoord.const_mul 4))
  have hfront :
      Continuous (fun t => -(R * Real.pi * angularSin t) /
        (Real.sqrt (1 + 4 * angularCoordinate R t) * Real.log 2)) := by
    apply Continuous.div
      ((continuous_const.mul hsin).neg)
      (hroot.mul continuous_const)
    intro t
    apply mul_ne_zero
    · apply (Real.sqrt_pos.mpr ?_).ne'
      nlinarith [angularCoordinate_nonneg hR.le t]
    · exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  exact hfront.mul
    (((hcos.mul hlogdegree).sub (hcos.mul hlogscale)).sub
      (hcoslog.const_mul 2))

private theorem angularCoordinate_eq_shiftedCos (R t : ℝ) :
    angularCoordinate R t = R / 2 * (1 + Real.cos (Real.pi * t)) := by
  unfold angularCoordinate angularCos
  have hdouble := Real.cos_two_mul (Real.pi * t / 2)
  have harg : 2 * (Real.pi * t / 2) = Real.pi * t := by ring
  rw [harg] at hdouble
  rw [hdouble]
  ring

private theorem angularCoordinate_midpoint_eq_pole
    {R : ℝ} {N : ℕ} (hN : 0 < N) (i : ℕ) :
    angularCoordinate R (((i : ℝ) + 1 / 2) / N) = pole R N i := by
  rw [angularCoordinate_eq_shiftedCos]
  unfold pole
  rw [poleAngle_eq_midpoint hN]
  congr 2
  congr 1
  ring

private theorem angularCoordinate_grid_eq_zero
    {R : ℝ} {N : ℕ} (j : ℕ) :
    angularCoordinate R ((j : ℝ) / N) = zero R N j := by
  rw [angularCoordinate_eq_shiftedCos]
  unfold zero zeroAngle
  congr 2
  congr 1
  ring

private theorem Phi_chebyshev_eq_midpoint_sub_interior {R : ℝ} (r : ℕ) :
    MetricCodes.Spherical.HigherHierarchy.Phi (ambient R r) (stabilizer R r) =
      (∑ i ∈ Finset.range (r + 1),
        angularEntropy R (((i : ℝ) + 1 / 2) / (r + 1))) -
      (∑ i ∈ Finset.range r,
        angularEntropy R (((i : ℝ) + 1) / (r + 1))) := by
  classical
  unfold MetricCodes.Spherical.HigherHierarchy.Phi
  rw [← Fin.sum_univ_eq_sum_range
    (fun i : ℕ => angularEntropy R (((i : ℝ) + 1 / 2) / (r + 1))),
    ← Fin.sum_univ_eq_sum_range
    (fun i : ℕ => angularEntropy R (((i : ℝ) + 1) / (r + 1)))]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    unfold ambient angularEntropy angularDegree
    congr 1
    simpa [Nat.cast_add, Nat.cast_one] using
      congrArg inverseQuadratic
        (angularCoordinate_midpoint_eq_pole (R := R) (Nat.zero_lt_succ r) i).symm
  · apply Finset.sum_congr rfl
    intro i hi
    unfold stabilizer angularEntropy angularDegree
    congr 1
    have hgrid := angularCoordinate_grid_eq_zero
      (R := R) (N := r + 1) (i + 1)
    norm_num [Nat.cast_add, Nat.cast_one] at hgrid ⊢
    exact congrArg inverseQuadratic hgrid.symm

private theorem angularEntropy_zero (R : ℝ) :
    angularEntropy R 0 = MetricCodes.sphericalEntropy (inverseQuadratic R) := by
  unfold angularEntropy angularDegree angularCoordinate angularCos
  norm_num

private theorem angularEntropy_one (R : ℝ) : angularEntropy R 1 = 0 := by
  unfold angularEntropy angularDegree angularCoordinate angularCos inverseQuadratic
  rw [mul_one, Real.cos_pi_div_two]
  norm_num

theorem tendsto_Phi_chebyshev {R : ℝ} (hR : 0 < R) :
    Tendsto
      (fun r : ℕ => MetricCodes.Spherical.HigherHierarchy.Phi
        (ambient R r) (stabilizer R r)) atTop (𝓝 (radiusEntropy R)) := by
  have hmid :=
    tendsto_midpointEndpointDifference
      (angularEntropy_continuous R).continuousOn
      (angularEntropyDerivative_continuous hR).continuousOn
      (fun t ht => hasDerivAt_angularEntropy hR ht)
  have hend : (angularEntropy R 0 + angularEntropy R 1) / 2 =
      radiusEntropy R := by
    rw [angularEntropy_zero, angularEntropy_one]
    simp [radiusEntropy]
  rw [hend] at hmid
  have hlimit := hmid.comp (tendsto_add_atTop_nat 1)
  refine hlimit.congr' ?_
  filter_upwards [] with r
  change
    midpointEndpointDifference (angularEntropy R) (r + 1) =
      MetricCodes.Spherical.HigherHierarchy.Phi (ambient R r) (stabilizer R r)
  rw [Phi_chebyshev_eq_midpoint_sub_interior]
  simp [midpointEndpointDifference, Nat.cast_add, Nat.cast_one]

end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic

end

section

noncomputable section

open scoped Interval

namespace MetricCodes.Spherical.HigherHierarchyChebyshev

def angularAmplitude (R : ℝ) : ℝ :=
  2 * Real.sqrt R / Real.sqrt (1 + 4 * R)

def angularQuadratic (R t : ℝ) : ℝ :=
  R / 2 * (1 + Real.cos (Real.pi * t))

def angularAtom (R t : ℝ) : ℝ :=
  MetricCodes.Spherical.HigherHierarchy.spectralAtom
    (inverseQuadratic (angularQuadratic R t))

theorem angularAmplitude_pos {R : ℝ} (hR : 0 < R) :
    0 < angularAmplitude R := by
  unfold angularAmplitude
  positivity

theorem angularAmplitude_lt_one {R : ℝ} (hR : 0 < R) :
    angularAmplitude R < 1 := by
  have hden : 0 < Real.sqrt (1 + 4 * R) := by positivity
  have hroot := Real.sqrt_pos.2 hR
  have hroot_sq := Real.sq_sqrt hR.le
  have hden_sq := Real.sq_sqrt (by positivity : 0 ≤ 1 + 4 * R)
  unfold angularAmplitude
  apply (div_lt_iff₀ hden).2
  nlinarith [sq_nonneg (Real.sqrt (1 + 4 * R) - 2 * Real.sqrt R)]

theorem angularQuadratic_nonneg {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    0 ≤ angularQuadratic R t := by
  unfold angularQuadratic
  exact mul_nonneg (by positivity)
    (by linarith [Real.neg_one_le_cos (Real.pi * t)])

theorem angularQuadratic_eq_cos_half_sq (R t : ℝ) :
    angularQuadratic R t =
      R * Real.cos (Real.pi * t / 2) ^ 2 := by
  have hcos := Real.cos_two_mul (Real.pi * t / 2)
  have harg : 2 * (Real.pi * t / 2) = Real.pi * t := by ring
  rw [harg] at hcos
  unfold angularQuadratic
  rw [hcos]
  ring

theorem angular_cos_nonneg {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ Real.cos (Real.pi * t / 2) := by
  apply Real.cos_nonneg_of_mem_Icc
  constructor
  · nlinarith [Real.pi_pos, ht.1]
  · nlinarith [Real.pi_pos, ht.2]

theorem sqrt_angularQuadratic {R : ℝ} (hR : 0 < R)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Real.sqrt (angularQuadratic R t) =
      Real.sqrt R * Real.cos (Real.pi * t / 2) := by
  rw [angularQuadratic_eq_cos_half_sq,
    Real.sqrt_mul hR.le, Real.sqrt_sq (angular_cos_nonneg ht)]

theorem angularAtom_eq {R : ℝ} (hR : 0 < R)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    angularAtom R t =
      Real.sqrt R * Real.cos (Real.pi * t / 2) /
        Real.sqrt (1 + 4 * R * Real.cos (Real.pi * t / 2) ^ 2) := by
  unfold angularAtom
  rw [spectralAtom_inverseQuadratic
    (angularQuadratic_nonneg hR.le t)]
  rw [sqrt_angularQuadratic hR ht,
    angularQuadratic_eq_cos_half_sq]
  ring_nf

theorem angularAmplitude_sin_mem {R : ℝ} (hR : 0 < R) (t : ℝ) :
    -(1 : ℝ) < angularAmplitude R * Real.sin (Real.pi * t / 2) ∧
      angularAmplitude R * Real.sin (Real.pi * t / 2) < 1 := by
  have ha := angularAmplitude_pos hR
  have ha' := angularAmplitude_lt_one hR
  have hsin := Real.neg_one_le_sin (Real.pi * t / 2)
  have hsin' := Real.sin_le_one (Real.pi * t / 2)
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hsin ha.le,
    mul_le_mul_of_nonneg_left hsin' ha.le]

theorem angularAmplitude_sqrt_complement {R : ℝ} (hR : 0 < R)
    (t : ℝ) :
    Real.sqrt
        (1 - (angularAmplitude R * Real.sin (Real.pi * t / 2)) ^ 2) =
      Real.sqrt (1 + 4 * R * Real.cos (Real.pi * t / 2) ^ 2) /
        Real.sqrt (1 + 4 * R) := by
  have hD : 0 < 1 + 4 * R := by positivity
  have hroot : 0 < Real.sqrt (1 + 4 * R) := Real.sqrt_pos.mpr hD
  have hroot_sq := Real.sq_sqrt hD.le
  have hRroot_sq := Real.sq_sqrt hR.le
  have htrig := Real.sin_sq_add_cos_sq (Real.pi * t / 2)
  have hins :
      1 - (angularAmplitude R * Real.sin (Real.pi * t / 2)) ^ 2 =
        (1 + 4 * R * Real.cos (Real.pi * t / 2) ^ 2) /
          (1 + 4 * R) := by
    unfold angularAmplitude
    field_simp
    rw [hroot_sq, hRroot_sq]
    linear_combination -(4 * R * (1 + 4 * R)) * htrig
  rw [hins, Real.sqrt_div (by positivity :
    0 ≤ 1 + 4 * R * Real.cos (Real.pi * t / 2) ^ 2)]

def angularAntiderivative (R t : ℝ) : ℝ :=
  (1 / Real.pi) *
    Real.arcsin (angularAmplitude R * Real.sin (Real.pi * t / 2))

theorem hasDerivAt_angularAntiderivative {R : ℝ} (hR : 0 < R)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (angularAntiderivative R) (angularAtom R t) t := by
  have harg := angularAmplitude_sin_mem hR t
  have hlin : HasDerivAt (fun x : ℝ => Real.pi * x / 2)
      (Real.pi / 2) t := by
    simpa using ((hasDerivAt_id t).const_mul Real.pi).div_const 2
  have hinner :
      HasDerivAt
        (fun x : ℝ => angularAmplitude R * Real.sin (Real.pi * x / 2))
        (angularAmplitude R *
          (Real.cos (Real.pi * t / 2) * (Real.pi / 2))) t := by
    simpa [Function.comp_def] using
      (((Real.hasDerivAt_sin (Real.pi * t / 2)).comp t hlin).const_mul
        (angularAmplitude R))
  have harc := (Real.hasDerivAt_arcsin
    (ne_of_gt harg.1) (ne_of_lt harg.2)).comp t hinner
  have hderiv := harc.const_mul (1 / Real.pi)
  have hformula :
      (1 / Real.pi) *
        (1 / Real.sqrt
            (1 - (angularAmplitude R * Real.sin (Real.pi * t / 2)) ^ 2) *
          (angularAmplitude R *
            (Real.cos (Real.pi * t / 2) * (Real.pi / 2)))) =
        angularAtom R t := by
    rw [angularAtom_eq hR ht,
      angularAmplitude_sqrt_complement hR t]
    unfold angularAmplitude
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hD : Real.sqrt (1 + 4 * R) ≠ 0 := by positivity
    have hA : Real.sqrt
        (1 + 4 * R * Real.cos (Real.pi * t / 2) ^ 2) ≠ 0 := by positivity
    field_simp
  rw [hformula] at hderiv
  change HasDerivAt
    (fun x : ℝ => (1 / Real.pi) *
      Real.arcsin (angularAmplitude R * Real.sin (Real.pi * x / 2)))
    (angularAtom R t) t
  simpa only [Function.comp_apply] using hderiv

theorem angularQuadratic_continuous (R : ℝ) :
    Continuous (angularQuadratic R) := by
  unfold angularQuadratic
  fun_prop

theorem angularAtom_continuous {R : ℝ} (hR : 0 < R) :
    Continuous (angularAtom R) := by
  have hq := angularQuadratic_continuous R
  have hnum : Continuous
      (fun t : ℝ => Real.sqrt (angularQuadratic R t)) :=
    Real.continuous_sqrt.comp hq
  have hden : Continuous
      (fun t : ℝ => Real.sqrt (1 + 4 * angularQuadratic R t)) := by
    fun_prop
  have hdiv := hnum.div hden (fun t => by
    exact (Real.sqrt_pos.mpr
      (by nlinarith [angularQuadratic_nonneg hR.le t])).ne')
  apply hdiv.congr
  intro t
  unfold angularAtom
  exact (spectralAtom_inverseQuadratic
    (angularQuadratic_nonneg hR.le t)).symm

theorem angularAtom_antitone {R : ℝ} (hR : 0 < R) :
    AntitoneOn (angularAtom R) (Set.Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hangles : Real.pi * x ≤ Real.pi * y :=
    mul_le_mul_of_nonneg_left hxy Real.pi_pos.le
  have hcos : Real.cos (Real.pi * y) ≤ Real.cos (Real.pi * x) :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      (mul_nonneg Real.pi_pos.le hx.1)
      (by nlinarith [Real.pi_pos, hy.2]) hangles
  have hquadratic : angularQuadratic R y ≤ angularQuadratic R x := by
    unfold angularQuadratic
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hxquad := angularQuadratic_nonneg hR.le x
  have hyquad := angularQuadratic_nonneg hR.le y
  unfold angularAtom
  rw [spectralAtom_inverseQuadratic_half hxquad,
    spectralAtom_inverseQuadratic_half hyquad]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

theorem integral_angularAtom_eq_arcsin {R : ℝ} (hR : 0 < R) :
    (∫ t in (0 : ℝ)..1, angularAtom R t) =
      Real.arcsin (angularAmplitude R) / Real.pi := by
  have hint : IntervalIntegrable (angularAtom R)
      MeasureTheory.volume 0 1 :=
    (angularAtom_continuous hR).intervalIntegrable 0 1
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (angularAntiderivative R) (angularAtom R t) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
    exact hasDerivAt_angularAntiderivative hR ht'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  unfold angularAntiderivative
  simp [Real.sin_pi_div_two]
  ring

theorem arcsin_angularAmplitude_eq {R : ℝ} (hR : 0 < R) :
    Real.arcsin (angularAmplitude R) =
      Real.pi / 2 - Real.arcsin (1 / Real.sqrt (1 + 4 * R)) := by
  have hD : 0 < 1 + 4 * R := by positivity
  have hroot := Real.sqrt_pos.mpr hD
  have hroot_sq := Real.sq_sqrt hD.le
  have hRroot_sq := Real.sq_sqrt hR.le
  have hcomplement :
      Real.sqrt (1 - (1 / Real.sqrt (1 + 4 * R)) ^ 2) =
        angularAmplitude R := by
    have hsquare :
        1 - (1 / Real.sqrt (1 + 4 * R)) ^ 2 =
          (angularAmplitude R) ^ 2 := by
      unfold angularAmplitude
      field_simp
      nlinarith
    rw [hsquare, Real.sqrt_sq (angularAmplitude_pos hR).le]
  calc
    Real.arcsin (angularAmplitude R) =
        Real.arccos (1 / Real.sqrt (1 + 4 * R)) := by
          symm
          rw [Real.arccos_eq_arcsin (by positivity), hcomplement]
    _ = Real.pi / 2 - Real.arcsin (1 / Real.sqrt (1 + 4 * R)) :=
      Real.arccos_eq_pi_div_two_sub_arcsin _

theorem integral_angularAtom_eq_formula {R : ℝ} (hR : 0 < R) :
    (∫ t in (0 : ℝ)..1, angularAtom R t) =
      (1 - (2 / Real.pi) *
        Real.arcsin (1 / Real.sqrt (4 * R + 1))) / 2 := by
  rw [integral_angularAtom_eq_arcsin hR,
    arcsin_angularAmplitude_eq hR]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hrad : 1 + 4 * R = 4 * R + 1 := by ring
  rw [hrad]
  field_simp

end MetricCodes.Spherical.HigherHierarchyChebyshev

open Filter
open scoped Topology BigOperators

namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic

theorem Gamma_eq_midpointAverage {R : ℝ} (hR : 0 < R)
    (r : ℕ) :
    MetricCodes.Spherical.HigherHierarchy.Gamma
      (ambient R r) (stabilizer R r) =
      midpointAverage (angularAtom R) (r + 1) := by
  rw [Gamma_eq_average_spectralAtom hR]
  unfold midpointAverage
  apply congrArg (fun x : ℝ => x / ((r + 1 : ℕ) : ℝ))
  change
    (∑ i : Fin (r + 1),
      MetricCodes.Spherical.HigherHierarchy.spectralAtom
        (inverseQuadratic (pole R (r + 1) i.val))) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => MetricCodes.Spherical.HigherHierarchy.spectralAtom
      (inverseQuadratic (pole R (r + 1) i))) (r + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  unfold angularAtom angularQuadratic
  congr 2
  unfold pole
  rw [poleAngle_eq_midpoint (Nat.zero_lt_succ r)]
  norm_num [Nat.cast_add, Nat.cast_one]
  left
  congr 1
  ring

theorem integral_angularAtom_eq_radiusGamma
    {R : ℝ} (hR : 0 < R) :
    (∫ t in (0 : ℝ)..1, angularAtom R t) = radiusGamma R := by
  rw [integral_angularAtom_eq_formula hR]
  rfl

theorem tendsto_Gamma_chebyshev {R : ℝ} (hR : 0 < R) :
    Tendsto
      (fun r : ℕ => MetricCodes.Spherical.HigherHierarchy.Gamma
        (ambient R r) (stabilizer R r))
      atTop (𝓝 (radiusGamma R)) := by
  have hmid := (tendsto_midpointAverage_integral
    (angularAtom_antitone hR)).comp (tendsto_add_atTop_nat 1)
  rw [integral_angularAtom_eq_radiusGamma hR] at hmid
  apply hmid.congr'
  exact Filter.Eventually.of_forall (fun r =>
    (Gamma_eq_midpointAverage hR r).symm)

end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic

end

section

noncomputable section

open Filter
open scoped Topology

namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic

theorem tendsto_packingObjective_of_limits
    {R : ℝ} (hR : 0 ≤ R) {G P : ℕ → ℝ}
    (hG : Tendsto G atTop (𝓝 (radiusGamma R)))
    (hP : Tendsto P atTop (𝓝 (radiusEntropy R))) :
    Tendsto
      (fun n => MetricCodes.Spherical.HigherHierarchy.Entropy.packingObjective
        (G n) (P n))
      atTop (𝓝 (radiusPackingObjective R)) := by
  have hnormalizer : 0 < 1 - 2 * radiusGamma R := by
    rw [one_sub_two_mul_radiusGamma]
    exact radiusNormalizer_pos hR
  have hdenominator :
      Tendsto (fun n => 1 - 2 * G n) atTop
        (𝓝 (1 - 2 * radiusGamma R)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hG)
  have hquotient :
      Tendsto (fun n => 2 / (1 - 2 * G n)) atTop
        (𝓝 (2 / (1 - 2 * radiusGamma R))) :=
    tendsto_const_nhds.div hdenominator hnormalizer.ne'
  have hquotient_ne : (2 : ℝ) / (1 - 2 * radiusGamma R) ≠ 0 :=
    div_ne_zero (by norm_num) hnormalizer.ne'
  have hlogarithm :
      Tendsto (fun n => Real.logb 2 (2 / (1 - 2 * G n))) atTop
        (𝓝 (Real.logb 2 (2 / (1 - 2 * radiusGamma R)))) :=
    (Real.continuousAt_logb hquotient_ne).tendsto.comp hquotient
  exact (tendsto_const_nhds.mul hlogarithm).sub hP

theorem tendsto_actual_chebyshevPackingObjective
    {R : ℝ} (hR : 0 ≤ R)
    (hG : Tendsto
      (fun r : ℕ => MetricCodes.Spherical.HigherHierarchy.Gamma
        (MetricCodes.Spherical.HigherHierarchyChebyshev.ambient R r)
        (MetricCodes.Spherical.HigherHierarchyChebyshev.stabilizer R r))
      atTop (𝓝 (radiusGamma R)))
    (hP : Tendsto
      (fun r : ℕ => MetricCodes.Spherical.HigherHierarchy.Phi
        (MetricCodes.Spherical.HigherHierarchyChebyshev.ambient R r)
        (MetricCodes.Spherical.HigherHierarchyChebyshev.stabilizer R r))
      atTop (𝓝 (radiusEntropy R))) :
    Tendsto
      (fun r : ℕ => MetricCodes.Spherical.HigherHierarchy.hierarchyPackingObjective
        (MetricCodes.Spherical.HigherHierarchyChebyshev.ambient R r)
        (MetricCodes.Spherical.HigherHierarchyChebyshev.stabilizer R r))
      atTop (𝓝 (radiusPackingObjective R)) :=
  tendsto_packingObjective_of_limits hR hG hP

end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic

end

section

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic

theorem chebyshevGamma_pos {R : ℝ} (hR : 0 < R) (r : ℕ) :
    0 < MetricCodes.Spherical.HigherHierarchy.Gamma
      (ambient R r) (stabilizer R r) := by
  classical
  have htuple := ambient_stabilizer_interlacing hR r
  have hpole : 0 < pole R (r + 1) 0 :=
    pole_pos hR (Nat.zero_lt_succ r) (by omega)
  have hzero : inverseQuadratic 0 = 0 := by
    norm_num [inverseQuadratic]
  have hambient : 0 < ambient R r 0 := by
    change 0 < inverseQuadratic (pole R (r + 1) 0)
    rw [← hzero]
    exact inverseQuadratic_strictMonoOn (by norm_num) hpole.le hpole
  have hatom :
      0 < MetricCodes.Spherical.HigherHierarchy.spectralAtom
        (ambient R r 0) := by
    unfold MetricCodes.Spherical.HigherHierarchy.spectralAtom
      MetricCodes.Spherical.HigherHierarchy.quadraticCoordinate
    positivity
  unfold MetricCodes.Spherical.HigherHierarchy.Gamma
  calc
    0 < MetricCodes.Spherical.HigherHierarchy.lagrangeWeight
          (ambient R r) (stabilizer R r) 0 *
        MetricCodes.Spherical.HigherHierarchy.spectralAtom
          (ambient R r 0) :=
      mul_pos (htuple.lagrangeWeight_pos 0) hatom
    _ ≤ ∑ i : Fin (r + 1),
        MetricCodes.Spherical.HigherHierarchy.lagrangeWeight
          (ambient R r) (stabilizer R r) i *
        MetricCodes.Spherical.HigherHierarchy.spectralAtom
          (ambient R r i) := by
      exact Finset.single_le_sum
        (fun i _ =>
          mul_nonneg (htuple.lagrangeWeight_nonneg i)
            (MetricCodes.Spherical.HigherHierarchy.spectralAtom_nonneg
              (htuple.ambient_nonneg i)))
        (Finset.mem_univ 0)

theorem radiusPackingObjective_le_hierarchyPackingExponent_of_convergence
    {R : ℝ} (hR : 0 < R)
    (hconvergence :
      Tendsto
        (fun r : ℕ =>
          MetricCodes.Spherical.HigherHierarchy.hierarchyPackingObjective
            (ambient R r) (stabilizer R r))
        atTop (𝓝 (radiusPackingObjective R))) :
    (radiusPackingObjective R : EReal) ≤
      MetricCodes.Spherical.HigherHierarchy.hierarchyPackingExponent := by
  have hereal :
      Tendsto
        (fun r : ℕ =>
          (MetricCodes.Spherical.HigherHierarchy.hierarchyPackingObjective
            (ambient R r) (stabilizer R r) : EReal))
        atTop (𝓝 (radiusPackingObjective R : EReal)) :=
    EReal.tendsto_coe.mpr hconvergence
  apply le_of_tendsto hereal
  exact Eventually.of_forall fun r =>
    MetricCodes.Spherical.HigherHierarchy.hierarchyPackingObjective_le_hierarchyPackingExponent
      (ambient_stabilizer_interlacing hR r) (chebyshevGamma_pos hR r)

theorem criticalExponent_le_of_chebyshev_objective_convergence
    (hconvergence :
      ∀ R : ℝ, 0 < R →
        Tendsto
          (fun r : ℕ =>
            MetricCodes.Spherical.HigherHierarchy.hierarchyPackingObjective
              (ambient R r) (stabilizer R r))
          atTop (𝓝 (radiusPackingObjective R))) :
    (CohnElkies.criticalBinaryExponent : EReal) ≤
      MetricCodes.Spherical.HigherHierarchy.hierarchyPackingExponent := by
  have hereal :
      Tendsto (fun R : ℝ => (radiusPackingObjective R : EReal))
        atTop (𝓝 (CohnElkies.criticalBinaryExponent : EReal)) :=
    EReal.tendsto_coe.mpr tendsto_radiusPackingObjective
  apply le_of_tendsto hereal
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact radiusPackingObjective_le_hierarchyPackingExponent_of_convergence
    hR (hconvergence R hR)

end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic

end

end

section

noncomputable section

namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic

theorem criticalExponent_le_hierarchyPackingExponent :
    (CohnElkies.criticalBinaryExponent : EReal) ≤
      MetricCodes.Spherical.HigherHierarchy.hierarchyPackingExponent := by
  apply criticalExponent_le_of_chebyshev_objective_convergence
  intro R hR
  exact tendsto_actual_chebyshevPackingObjective hR.le
    (tendsto_Gamma_chebyshev hR) (tendsto_Phi_chebyshev hR)

end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic

end

end

section

noncomputable section

open scoped BigOperators

namespace MetricCodes.Spherical.HigherHierarchy.Numerics

def kissingAmbient : Fin 3 → ℝ :=
  ![(0.090531 : ℝ), 0.000565957168637484, 0.00000249433171106134]

def kissingStabilizer : Fin 2 → ℝ :=
  ![(0.00693131464159807 : ℝ), 0.0000438056170666568]

@[simp] theorem kissingAmbient_apply (i : Fin 3) :
    kissingAmbient i =
      if i.val = 0 then (0.090531 : ℝ)
      else if i.val = 1 then 0.000565957168637484
      else 0.00000249433171106134 := by
  fin_cases i <;> rfl

@[simp] theorem kissingStabilizer_apply (i : Fin 2) :
    kissingStabilizer i =
      if i.val = 0 then (0.00693131464159807 : ℝ)
      else 0.0000438056170666568 := by
  fin_cases i <;> rfl

@[simp] theorem succAbove_three_20 :
    (2 : Fin 3).succAbove (0 : Fin 2) = 0 := by decide
@[simp] theorem succAbove_three_21 :
    (2 : Fin 3).succAbove (1 : Fin 2) = 1 := by decide

theorem kissing_interlacing :
    Interlacing kissingAmbient kissingStabilizer := by
  constructor
  · change 0 ≤ (0.00000249433171106134 : ℝ)
    norm_num
  · intro i
    fin_cases i <;> constructor <;> norm_num

theorem kissing_sqrt_lower :
    (0.31420830982168 : ℝ) <
        Real.sqrt (quadraticCoordinate (kissingAmbient 0)) ∧
      (0.02379658538854 : ℝ) <
        Real.sqrt (quadraticCoordinate (kissingAmbient 1)) ∧
      (0.00157934731226 : ℝ) <
        Real.sqrt (quadraticCoordinate (kissingAmbient 2)) := by
  constructor
  · apply Real.lt_sqrt_of_sq_lt
    norm_num [quadraticCoordinate]
  constructor
  · apply Real.lt_sqrt_of_sq_lt
    norm_num [quadraticCoordinate]
  · apply Real.lt_sqrt_of_sq_lt
    norm_num [quadraticCoordinate]

theorem kissing_spectral_certificate :
    (0.00000212 : ℝ) <
      2 * Gamma kissingAmbient kissingStabilizer - (1 / 2 : ℝ) := by
  obtain ⟨h₀, h₁, h₂⟩ := kissing_sqrt_lower
  unfold Gamma
  rw [Fin.sum_univ_three]
  norm_num [spectralAtom, lagrangeWeight, lagrangeNumerator,
    lagrangeDenominator, quadraticCoordinate,
    Fin.prod_univ_two]
    at h₀ h₁ h₂ ⊢
  norm_num [Fin.ext_iff] at h₀ h₁ h₂ ⊢
  linarith

theorem rational_log_lower {r lo : ℝ} (hr : 1 ≤ r) (m : ℕ)
    (hlo : lo < MetricCodes.Numerics.logSeriesLower
      ((r - 1) / (r + 1)) m) : lo < Real.log r := by
  have hden : 0 < r + 1 := by linarith
  have hx : 0 ≤ (r - 1) / (r + 1) :=
    div_nonneg (sub_nonneg.mpr hr) hden.le
  have hx' : (r - 1) / (r + 1) < 1 :=
    (div_lt_one hden).mpr (by linarith)
  calc
    lo < MetricCodes.Numerics.logSeriesLower
      ((r - 1) / (r + 1)) m := hlo
    _ ≤ Real.log
      ((1 + (r - 1) / (r + 1)) / (1 - (r - 1) / (r + 1))) :=
        MetricCodes.Numerics.log_ratio_lower hx hx' m
    _ = Real.log r := by
      congr 1
      field_simp; ring

theorem rational_log_upper {r hi : ℝ} (hr : 1 ≤ r) (m : ℕ)
    (hhi : MetricCodes.Numerics.logSeriesUpper
      ((r - 1) / (r + 1)) m < hi) : Real.log r < hi := by
  have hden : 0 < r + 1 := by linarith
  have hx : 0 ≤ (r - 1) / (r + 1) :=
    div_nonneg (sub_nonneg.mpr hr) hden.le
  have hx' : (r - 1) / (r + 1) < 1 :=
    (div_lt_one hden).mpr (by linarith)
  calc
    Real.log r = Real.log
      ((1 + (r - 1) / (r + 1)) / (1 - (r - 1) / (r + 1))) := by
        congr 1
        field_simp; ring
    _ ≤ MetricCodes.Numerics.logSeriesUpper
      ((r - 1) / (r + 1)) m :=
        MetricCodes.Numerics.log_ratio_upper hx hx' m
    _ < hi := hhi

theorem log_scaled_pow_two {u : ℝ} (hu : u ≠ 0) (k : ℕ) :
    Real.log u = Real.log ((2 : ℝ) ^ k * u) - k * Real.log 2 := by
  have h := Real.log_mul
    (pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0)) hu
  rw [Real.log_pow] at h
  linarith

theorem kissing_entropy_certificate :
    Phi kissingAmbient kissingStabilizer < (0.396605 : ℝ) := by
  have htwo := MetricCodes.Numerics.log_two_interval.1
  have ha₀plus : Real.log (1 + kissingAmbient 0) < (0.086664734 : ℝ) := by
    apply rational_log_upper (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesUpper,
        MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have ha₀scale : (0.370525776 : ℝ) < Real.log (16 * kissingAmbient 0) := by
    apply rational_log_lower (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have ha₁plus : Real.log (1 + kissingAmbient 1) < (0.000565798 : ℝ) := by
    apply rational_log_upper (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesUpper,
        MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have ha₁scale :
      (0.147626829 : ℝ) < Real.log (2048 * kissingAmbient 1) := by
    apply rational_log_lower (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have ha₂plus : Real.log (1 + kissingAmbient 2) < (0.000002495 : ℝ) := by
    apply rational_log_upper (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesUpper,
        MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have ha₂scale :
      (0.268306714 : ℝ) < Real.log (524288 * kissingAmbient 2) := by
    apply rational_log_lower (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have hb₀plus : (0.006907403 : ℝ) < Real.log (1 + kissingStabilizer 0) := by
    apply rational_log_lower (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have hb₀scale :
      Real.log (256 * kissingStabilizer 0) < (0.573471664 : ℝ) := by
    apply rational_log_upper (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesUpper,
        MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have hb₁plus :
      (0.000043804 : ℝ) < Real.log (1 + kissingStabilizer 1) := by
    apply rational_log_lower (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have hb₁scale :
      Real.log (32768 * kissingStabilizer 1) < (0.361459204 : ℝ) := by
    apply rational_log_upper (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesUpper,
        MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have hmain :
      (1 + kissingAmbient 0) * Real.log (1 + kissingAmbient 0) -
          kissingAmbient 0 *
            (Real.log (16 * kissingAmbient 0) - 4 * Real.log 2) +
        ((1 + kissingAmbient 1) * Real.log (1 + kissingAmbient 1) -
          kissingAmbient 1 *
            (Real.log (2048 * kissingAmbient 1) - 11 * Real.log 2)) +
        ((1 + kissingAmbient 2) * Real.log (1 + kissingAmbient 2) -
          kissingAmbient 2 *
            (Real.log (524288 * kissingAmbient 2) - 19 * Real.log 2)) -
        ((1 + kissingStabilizer 0) * Real.log (1 + kissingStabilizer 0) -
          kissingStabilizer 0 *
            (Real.log (256 * kissingStabilizer 0) - 8 * Real.log 2)) -
        ((1 + kissingStabilizer 1) * Real.log (1 + kissingStabilizer 1) -
          kissingStabilizer 1 *
            (Real.log (32768 * kissingStabilizer 1) - 15 * Real.log 2)) <
          (0.396605 : ℝ) * Real.log 2 := by
    norm_num at htwo ha₀plus ha₀scale ha₁plus ha₁scale ha₂plus ha₂scale hb₀plus hb₀scale hb₁plus hb₁scale ⊢
    linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    Phi kissingAmbient kissingStabilizer =
      ((1 + kissingAmbient 0) * Real.log (1 + kissingAmbient 0) -
          kissingAmbient 0 * Real.log (kissingAmbient 0) +
        ((1 + kissingAmbient 1) * Real.log (1 + kissingAmbient 1) -
          kissingAmbient 1 * Real.log (kissingAmbient 1)) +
        ((1 + kissingAmbient 2) * Real.log (1 + kissingAmbient 2) -
          kissingAmbient 2 * Real.log (kissingAmbient 2)) -
        ((1 + kissingStabilizer 0) * Real.log (1 + kissingStabilizer 0) -
          kissingStabilizer 0 * Real.log (kissingStabilizer 0)) -
        ((1 + kissingStabilizer 1) * Real.log (1 + kissingStabilizer 1) -
          kissingStabilizer 1 * Real.log (kissingStabilizer 1))) /
            Real.log 2 := by
      unfold Phi
      rw [Fin.sum_univ_three, Fin.sum_univ_two]
      unfold MetricCodes.sphericalEntropy Real.logb
      ring
    _ < (0.396605 : ℝ) := by
      apply (div_lt_iff₀ hlog).2
      rw [log_scaled_pow_two (u := kissingAmbient 0) (by norm_num) 4,
        log_scaled_pow_two (u := kissingAmbient 1) (by norm_num) 11,
        log_scaled_pow_two (u := kissingAmbient 2) (by norm_num) 19,
        log_scaled_pow_two (u := kissingStabilizer 0) (by norm_num) 8,
        log_scaled_pow_two (u := kissingStabilizer 1) (by norm_num) 15]
      norm_num at hmain ⊢
      exact hmain

end MetricCodes.Spherical.HigherHierarchy.Numerics

end

end

section

noncomputable section

open Filter Topology
open scoped BigOperators Topology

namespace MetricCodes.Spherical.HigherHierarchy

theorem Interlacing.Phi_nonneg {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) : 0 ≤ Phi a b := by
  have hlast :
      0 ≤ MetricCodes.sphericalEntropy (a (Fin.last r)) := by
    simpa using
      (MetricCodes.Spherical.sphericalEntropy_sub_nonneg
        (a := a (Fin.last r)) (b := 0) (by norm_num) h.1)
  have hrows :
      0 ≤ ∑ i : Fin r,
        (MetricCodes.sphericalEntropy (a i.castSucc) -
          MetricCodes.sphericalEntropy (b i)) := by
    apply Finset.sum_nonneg
    intro i _
    exact MetricCodes.Spherical.sphericalEntropy_sub_nonneg
      (h.stabilizer_pos i).le (h.2 i).1.le
  unfold Phi
  rw [Fin.sum_univ_castSucc]
  calc
    0 ≤ (∑ i : Fin r,
        (MetricCodes.sphericalEntropy (a i.castSucc) -
          MetricCodes.sphericalEntropy (b i))) +
        MetricCodes.sphericalEntropy (a (Fin.last r)) :=
      add_nonneg hrows hlast
    _ = (∑ i : Fin r,
          MetricCodes.sphericalEntropy (a i.castSucc)) +
        MetricCodes.sphericalEntropy (a (Fin.last r)) -
          ∑ i : Fin r, MetricCodes.sphericalEntropy (b i) := by
      rw [Finset.sum_sub_distrib]
      ring

def hierarchyRateSet (s : ℝ) : Set ℝ :=
  {z | ∃ (r : ℕ) (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
    Interlacing a b ∧ s < 2 * Gamma a b ∧ z = Phi a b}

def hierarchyVariationalRate (s : ℝ) : ℝ := sInf (hierarchyRateSet s)

theorem hierarchyRateSet_bddBelow (s : ℝ) :
    BddBelow (hierarchyRateSet s) := by
  refine ⟨0, ?_⟩
  rintro z ⟨r, a, b, h, _, rfl⟩
  exact h.Phi_nonneg

theorem hierarchyVariationalRate_le_of_feasible {r : ℕ}
    {s : ℝ} {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hgap : s < 2 * Gamma a b) :
    hierarchyVariationalRate s ≤ Phi a b := by
  exact csInf_le (hierarchyRateSet_bddBelow s)
    ⟨r, a, b, h, hgap, rfl⟩

def hierarchyKissingExponent : ℝ :=
  hierarchyVariationalRate ((1 : ℝ) / 2)

theorem kissing_levelTwo_feasible :
    Interlacing Numerics.kissingAmbient Numerics.kissingStabilizer ∧
      (1 / 2 : ℝ) <
        2 * Gamma Numerics.kissingAmbient Numerics.kissingStabilizer := by
  refine ⟨Numerics.kissing_interlacing, ?_⟩
  linarith [Numerics.kissing_spectral_certificate]

theorem hierarchyKissingExponent_lt_exact :
    hierarchyKissingExponent < (0.396605 : ℝ) := by
  unfold hierarchyKissingExponent
  exact lt_of_le_of_lt
    (hierarchyVariationalRate_le_of_feasible
      kissing_levelTwo_feasible.1 kissing_levelTwo_feasible.2)
    Numerics.kissing_entropy_certificate

theorem hierarchyKissingExponent_lt_published :
    hierarchyKissingExponent < (0.39661 : ℝ) :=
  hierarchyKissingExponent_lt_exact.trans (by norm_num)

end MetricCodes.Spherical.HigherHierarchy

end

end

section

noncomputable section

open MeasureTheory
open scoped BigOperators Interval

namespace MetricCodes.Spherical.HigherHierarchy

def stieltjesPhase {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (t : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..quadraticCoordinate (a (Fin.last r)), (t + u)⁻¹) +
    ∑ i : Fin r,
      ∫ u in quadraticCoordinate (b i)..quadraticCoordinate (a i.castSucc),
        (t + u)⁻¹

def stieltjesPhaseProduct {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (t : ℝ) : ℝ :=
  t * (∏ i : Fin r, (t + quadraticCoordinate (b i))) /
    (∏ i : Fin (r + 1), (t + quadraticCoordinate (a i)))

theorem Interlacing.ambient_quadratic_nonneg {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (i : Fin (r + 1)) :
    0 ≤ quadraticCoordinate (a i) := by
  unfold quadraticCoordinate
  exact mul_nonneg (h.ambient_nonneg i) (by linarith [h.ambient_nonneg i])

theorem Interlacing.stabilizer_quadratic_pos {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (i : Fin r) :
    0 < quadraticCoordinate (b i) := by
  unfold quadraticCoordinate
  exact mul_pos (h.stabilizer_pos i) (by linarith [h.stabilizer_pos i])

theorem integral_inv_add_eq_log_div
    {t p q : ℝ} (hp : 0 < t + p) (hq : 0 < t + q) :
    (∫ u in p..q, (t + u)⁻¹) = Real.log ((t + q) / (t + p)) := by
  have htranslate :=
    intervalIntegral.integral_comp_add_right (fun u : ℝ => u⁻¹) t
      (a := p) (b := q)
  have heq : (fun u : ℝ => (t + u)⁻¹) =
      (fun u : ℝ => (u + t)⁻¹) := by
    funext u
    rw [add_comm]
  rw [heq]
  rw [htranslate]
  simpa [add_comm] using
    integral_inv_of_pos hp hq

theorem stieltjesPhase_eq_log_sum {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {t : ℝ} (ht : 0 < t) :
    stieltjesPhase a b t =
      Real.log ((t + quadraticCoordinate (a (Fin.last r))) / t) +
        ∑ i : Fin r,
          Real.log ((t + quadraticCoordinate (a i.castSucc)) /
            (t + quadraticCoordinate (b i))) := by
  unfold stieltjesPhase
  rw [integral_inv_add_eq_log_div (by simpa using ht)
    (lt_of_lt_of_le ht (le_add_of_nonneg_right
      (h.ambient_quadratic_nonneg (Fin.last r))))]
  simp only [add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact integral_inv_add_eq_log_div
    (lt_of_lt_of_le ht (le_add_of_nonneg_right
      (h.stabilizer_quadratic_pos i).le))
    (lt_of_lt_of_le ht (le_add_of_nonneg_right
      (h.ambient_quadratic_nonneg i.castSucc)))

theorem exp_neg_stieltjesPhase_eq_product {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {t : ℝ} (ht : 0 < t) :
    Real.exp (-stieltjesPhase a b t) =
      stieltjesPhaseProduct a b t := by
  have hlast : 0 < t + quadraticCoordinate (a (Fin.last r)) := by
    linarith [h.ambient_quadratic_nonneg (Fin.last r)]
  have hambient (i : Fin (r + 1)) :
      0 < t + quadraticCoordinate (a i) := by
    linarith [h.ambient_quadratic_nonneg i]
  have hstabilizer (i : Fin r) :
      0 < t + quadraticCoordinate (b i) := by
    linarith [h.stabilizer_quadratic_pos i]
  have hexp :
      Real.exp (stieltjesPhase a b t) =
        ((t + quadraticCoordinate (a (Fin.last r))) / t) *
          ∏ i : Fin r,
            ((t + quadraticCoordinate (a i.castSucc)) /
              (t + quadraticCoordinate (b i))) := by
    rw [stieltjesPhase_eq_log_sum h ht, Real.exp_add]
    congr 1
    · exact Real.exp_log (div_pos hlast ht)
    · rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro i _
      exact Real.exp_log
        (div_pos (hambient i.castSucc) (hstabilizer i))
  rw [Real.exp_neg, hexp]
  unfold stieltjesPhaseProduct
  rw [Finset.prod_div_distrib, Fin.prod_univ_castSucc]
  have hcast :
      0 < ∏ i : Fin r, (t + quadraticCoordinate (a i.castSucc)) :=
    Finset.prod_pos fun i _ => hambient i.castSucc
  have hstabprod :
      0 < ∏ i : Fin r, (t + quadraticCoordinate (b i)) :=
    Finset.prod_pos fun i _ => hstabilizer i
  field_simp [ht.ne', hlast.ne', hcast.ne', hstabprod.ne']

theorem polynomial_partialFraction {r : ℕ}
    {x : Fin (r + 1) → ℝ} (hx : Function.Injective x)
    (P : Polynomial ℝ)
    (hdegree : P.degree <
      (Finset.univ : Finset (Fin (r + 1))).card)
    {z : ℝ} (hz : ∀ i : Fin (r + 1), z ≠ x i) :
    P.eval z / (∏ i : Fin (r + 1), (z - x i)) =
      ∑ i : Fin (r + 1),
        (P.eval (x i) /
          (∏ j ∈ Finset.univ.erase i, (x i - x j))) /
            (z - x i) := by
  classical
  have hinterpolate :
      P = Lagrange.interpolate
        (Finset.univ : Finset (Fin (r + 1))) x
        (fun i => P.eval (x i)) :=
    Lagrange.eq_interpolate hx.injOn hdegree
  have hvalue := Lagrange.eval_interpolate_not_at_node
    (s := (Finset.univ : Finset (Fin (r + 1))))
    (v := x) (x := z)
    (fun i => P.eval (x i))
    (fun i _ => hz i)
  rw [← hinterpolate] at hvalue
  have hprod : (∏ i : Fin (r + 1), (z - x i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact sub_ne_zero.mpr (hz i)
  have hnodal :
      (Lagrange.nodal
        (Finset.univ : Finset (Fin (r + 1))) x).eval z =
          ∏ i : Fin (r + 1), (z - x i) := by
    simp [Lagrange.nodal, Polynomial.eval_prod]
  rw [hnodal] at hvalue
  rw [hvalue, mul_div_cancel_left₀ _ hprod]
  apply Finset.sum_congr rfl
  intro i _
  rw [Lagrange.nodalWeight, Finset.prod_inv_distrib]
  ring

theorem stieltjesPartialFraction {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {t : ℝ} (ht : 0 < t) :
    (∏ i : Fin r, (t + quadraticCoordinate (b i))) /
        (∏ i : Fin (r + 1), (t + quadraticCoordinate (a i))) =
      ∑ i : Fin (r + 1),
        lagrangeWeight a b i / (t + quadraticCoordinate (a i)) := by
  classical
  let P := stabilizerPolynomial b
  have hdegree :
      P.degree < (Finset.univ : Finset (Fin (r + 1))).card := by
    rw [Polynomial.degree_eq_natDegree
      (stabilizerPolynomial_monic b).ne_zero,
      stabilizerPolynomial_natDegree]
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_add,
      Nat.cast_one]
    exact_mod_cast Nat.lt_succ_self r
  have hraw := polynomial_partialFraction h.quadratic_injective P hdegree
    (z := -t) (fun i => by
      have hnode := h.ambient_quadratic_nonneg i
      linarith)
  have hrewrite :
      (∏ i : Fin r, (-t - quadraticCoordinate (b i))) /
          (∏ i : Fin (r + 1), (-t - quadraticCoordinate (a i))) =
        ∑ i : Fin (r + 1),
          lagrangeWeight a b i / (-t - quadraticCoordinate (a i)) := by
    convert hraw using 1
    · simp [P, stabilizerPolynomial, Polynomial.eval_prod]
    · apply Finset.sum_congr rfl
      intro i _
      rw [stabilizerPolynomial_eval,
        ← lagrangeDenominator_eq_prod_erase]
      rfl
  have hneg (u : ℝ) : -t - u = -(t + u) := by ring
  simp_rw [hneg] at hrewrite
  rw [Finset.prod_neg, Finset.prod_neg] at hrewrite
  simp only [Finset.card_univ, Fintype.card_fin] at hrewrite
  have hsign : (-1 : ℝ) ^ r ≠ 0 := pow_ne_zero _ (by norm_num)
  have hden :
      (∏ i : Fin (r + 1),
        (t + quadraticCoordinate (a i))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have hnode := h.ambient_quadratic_nonneg i
    exact ne_of_gt (by linarith)
  have hleft :
      ((-1 : ℝ) ^ r * (∏ i : Fin r,
          (t + quadraticCoordinate (b i)))) /
        ((-1 : ℝ) ^ (r + 1) *
          (∏ i : Fin (r + 1),
            (t + quadraticCoordinate (a i)))) =
        -((∏ i : Fin r, (t + quadraticCoordinate (b i))) /
          (∏ i : Fin (r + 1), (t + quadraticCoordinate (a i)))) := by
    rw [pow_succ]
    field_simp [hsign, hden]
  rw [hleft] at hrewrite
  simpa only [div_neg, Finset.sum_neg_distrib, neg_inj] using hrewrite

theorem exp_neg_stieltjesPhase_eq_lagrange_sum {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {t : ℝ} (ht : 0 < t) :
    Real.exp (-stieltjesPhase a b t) =
      ∑ i : Fin (r + 1),
        lagrangeWeight a b i *
          (t / (t + quadraticCoordinate (a i))) := by
  rw [exp_neg_stieltjesPhase_eq_product h ht]
  unfold stieltjesPhaseProduct
  rw [show t * (∏ i : Fin r, (t + quadraticCoordinate (b i))) /
      (∏ i : Fin (r + 1), (t + quadraticCoordinate (a i))) =
        t * ((∏ i : Fin r, (t + quadraticCoordinate (b i))) /
          (∏ i : Fin (r + 1), (t + quadraticCoordinate (a i)))) by ring]
  rw [stieltjesPartialFraction h ht, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem quadratic_spectralAtom_identity {u : ℝ} (hu : 0 ≤ u) :
    Real.sqrt
      (quadraticCoordinate u / (quadraticCoordinate u + 1 / 4)) =
        2 * spectralAtom u := by
  have hA : 0 ≤ quadraticCoordinate u := by
    unfold quadraticCoordinate
    positivity
  have hlinear : 0 < 1 + 2 * u := by linarith
  have hden : 0 < quadraticCoordinate u + 1 / 4 := by linarith
  have hroot :
      Real.sqrt (quadraticCoordinate u + 1 / 4) =
        (1 + 2 * u) / 2 := by
    have hsquare := Real.sq_sqrt hden.le
    have hnonneg := Real.sqrt_nonneg
      (quadraticCoordinate u + 1 / 4)
    have htarget :
        ((1 + 2 * u) / 2) ^ 2 = quadraticCoordinate u + 1 / 4 := by
      unfold quadraticCoordinate
      ring
    nlinarith
  rw [Real.sqrt_div hA, hroot]
  unfold spectralAtom
  field_simp

theorem stieltjesKernel_integrable
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {x : ℝ} (hx : 0 ≤ x)
    (hpositive : ∀ᵐ t ∂μ, 0 < t) :
    Integrable (fun t : ℝ => t / (t + x)) μ := by
  apply (integrable_const (α := ℝ) (μ := μ) (c := (1 : ℝ))).mono'
    (measurable_id.div (measurable_id.add measurable_const)).aestronglyMeasurable
  filter_upwards [hpositive] with t ht
  have hden : 0 < t + x := by linarith
  have hnonneg : 0 ≤ t / (t + x) := div_nonneg ht.le hden.le
  simp only [Pi.div_apply, Pi.add_apply, id_eq]
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  simpa using (div_le_one hden).mpr (by linarith)

theorem exp_neg_stieltjesPhase_integrable {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hpositive : ∀ᵐ t ∂μ, 0 < t) :
    Integrable (fun t : ℝ => Real.exp (-stieltjesPhase a b t)) μ := by
  have hterm (i : Fin (r + 1)) :
      Integrable (fun t : ℝ =>
        lagrangeWeight a b i *
          (t / (t + quadraticCoordinate (a i)))) μ :=
    (stieltjesKernel_integrable μ (h.ambient_quadratic_nonneg i)
      hpositive).const_mul _
  apply (integrable_finsetSum _ (fun i _ => hterm i)).congr
  filter_upwards [hpositive] with t ht
  exact (exp_neg_stieltjesPhase_eq_lagrange_sum h ht).symm

theorem integral_exp_neg_stieltjesPhase_eq_one_sub_two_Gamma
    {r : ℕ} {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hpositive : ∀ᵐ t ∂μ, 0 < t)
    (hstieltjes : ∀ i : Fin (r + 1),
      (∫ t : ℝ, t / (t + quadraticCoordinate (a i)) ∂μ) =
        1 - 2 * spectralAtom (a i)) :
    (∫ t : ℝ, Real.exp (-stieltjesPhase a b t) ∂μ) =
      1 - 2 * Gamma a b := by
  have hterm (i : Fin (r + 1)) :
      Integrable (fun t : ℝ =>
        lagrangeWeight a b i *
          (t / (t + quadraticCoordinate (a i)))) μ :=
    (stieltjesKernel_integrable μ (h.ambient_quadratic_nonneg i)
      hpositive).const_mul _
  calc
    (∫ t : ℝ, Real.exp (-stieltjesPhase a b t) ∂μ) =
        ∫ t : ℝ, ∑ i : Fin (r + 1),
          lagrangeWeight a b i *
            (t / (t + quadraticCoordinate (a i))) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hpositive] with t ht
          exact exp_neg_stieltjesPhase_eq_lagrange_sum h ht
    _ = ∑ i : Fin (r + 1),
          lagrangeWeight a b i *
            (∫ t : ℝ, t / (t + quadraticCoordinate (a i)) ∂μ) := by
          rw [integral_finsetSum _ (fun i _ => hterm i)]
          apply Finset.sum_congr rfl
          intro i _
          rw [integral_const_mul]
    _ = ∑ i : Fin (r + 1),
          lagrangeWeight a b i *
            (1 - 2 * spectralAtom (a i)) := by
          congr 1
          funext i
          rw [hstieltjes i]
    _ = 1 - 2 * Gamma a b := by
          unfold Gamma
          simp_rw [mul_sub, mul_one]
          rw [Finset.sum_sub_distrib, h.sum_lagrangeWeight]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring

def stieltjesLogAtom (x t : ℝ) : ℝ :=
  Real.log ((t + x) / t)

theorem stieltjesPhase_eq_logAtom_sum {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {t : ℝ} (ht : 0 < t) :
    stieltjesPhase a b t =
      (∑ i : Fin (r + 1),
        stieltjesLogAtom (quadraticCoordinate (a i)) t) -
        ∑ i : Fin r,
          stieltjesLogAtom (quadraticCoordinate (b i)) t := by
  rw [stieltjesPhase_eq_log_sum h ht, Fin.sum_univ_castSucc]
  have hfactor (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      Real.log ((t + x) / (t + y)) =
        stieltjesLogAtom x t - stieltjesLogAtom y t := by
    unfold stieltjesLogAtom
    rw [Real.log_div (by linarith) (by linarith),
      Real.log_div (by linarith) ht.ne',
      Real.log_div (by linarith) ht.ne']
    ring
  simp_rw [hfactor _ _ (h.ambient_quadratic_nonneg _)
    (h.stabilizer_quadratic_pos _).le]
  unfold stieltjesLogAtom
  rw [Finset.sum_sub_distrib]
  ring

theorem stieltjesLogAtom_integrable_of_log
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {x : ℝ} (hx : 0 ≤ x)
    (hsupport : ∀ᵐ t ∂μ, 0 < t ∧ t ≤ 1)
    (hlog : Integrable (fun t : ℝ => Real.log t) μ) :
    Integrable (stieltjesLogAtom x) μ := by
  rcases hx.eq_or_lt with rfl | hx
  · have hzero : stieltjesLogAtom 0 = (0 : ℝ → ℝ) := by
      funext t
      by_cases ht : t = 0 <;> simp [stieltjesLogAtom, ht]
    rw [hzero]
    exact integrable_zero _ _ _
  · let C : ℝ := max |Real.log x| |Real.log (1 + x)|
    have hshift : Integrable (fun t : ℝ => Real.log (t + x)) μ := by
      apply (integrable_const (α := ℝ) (μ := μ) (c := C)).mono'
        (measurable_id.add measurable_const).log.aestronglyMeasurable
      filter_upwards [hsupport] with t ht
      have htx : 0 < t + x := add_pos ht.1 hx
      have hone : 0 < 1 + x := by linarith
      have hlower : Real.log x ≤ Real.log (t + x) :=
        Real.strictMonoOn_log.monotoneOn
          (show x ∈ Set.Ioi 0 from hx)
          (show t + x ∈ Set.Ioi 0 from htx)
          (by linarith [ht.1])
      have hupper : Real.log (t + x) ≤ Real.log (1 + x) :=
        Real.strictMonoOn_log.monotoneOn
          (show t + x ∈ Set.Ioi 0 from htx)
          (show 1 + x ∈ Set.Ioi 0 from hone)
          (by linarith [ht.2])
      simp only [Pi.add_apply, id_eq]
      change |Real.log (t + x)| ≤ C
      apply (abs_le).2
      constructor
      · exact (neg_le_neg (le_max_left _ _)).trans
          ((neg_abs_le (Real.log x)).trans hlower)
      · exact hupper.trans
          ((le_abs_self _).trans (le_max_right _ _))
    apply (hshift.sub hlog).congr
    filter_upwards [hsupport] with t ht
    unfold stieltjesLogAtom
    exact (Real.log_div (by linarith) ht.1.ne').symm

theorem stieltjesPhase_integrable_of_logAtoms {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b)
    (μ : Measure ℝ)
    (hpositive : ∀ᵐ t ∂μ, 0 < t)
    (ha : ∀ i : Fin (r + 1),
      Integrable (stieltjesLogAtom (quadraticCoordinate (a i))) μ)
    (hb : ∀ i : Fin r,
      Integrable (stieltjesLogAtom (quadraticCoordinate (b i))) μ) :
    Integrable (stieltjesPhase a b) μ := by
  apply ((integrable_finsetSum _ (fun i _ => ha i)).sub
    (integrable_finsetSum _ (fun i _ => hb i))).congr
  filter_upwards [hpositive] with t ht
  exact (stieltjesPhase_eq_logAtom_sum h ht).symm

theorem integral_stieltjesPhase_eq_two_log_mul_Phi {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b)
    (μ : Measure ℝ)
    (hpositive : ∀ᵐ t ∂μ, 0 < t)
    (ha : ∀ i : Fin (r + 1),
      Integrable (stieltjesLogAtom (quadraticCoordinate (a i))) μ)
    (hb : ∀ i : Fin r,
      Integrable (stieltjesLogAtom (quadraticCoordinate (b i))) μ)
    (hma : ∀ i : Fin (r + 1),
      (∫ t : ℝ, stieltjesLogAtom (quadraticCoordinate (a i)) t ∂μ) =
        2 * Real.log 2 * MetricCodes.sphericalEntropy (a i))
    (hmb : ∀ i : Fin r,
      (∫ t : ℝ, stieltjesLogAtom (quadraticCoordinate (b i)) t ∂μ) =
        2 * Real.log 2 * MetricCodes.sphericalEntropy (b i)) :
    (∫ t : ℝ, stieltjesPhase a b t ∂μ) =
      2 * Real.log 2 * Phi a b := by
  have hasum : Integrable (fun t : ℝ =>
      ∑ i : Fin (r + 1),
        stieltjesLogAtom (quadraticCoordinate (a i)) t) μ :=
    integrable_finsetSum _ (fun i _ => ha i)
  have hbsum : Integrable (fun t : ℝ =>
      ∑ i : Fin r,
        stieltjesLogAtom (quadraticCoordinate (b i)) t) μ :=
    integrable_finsetSum _ (fun i _ => hb i)
  calc
    (∫ t : ℝ, stieltjesPhase a b t ∂μ) =
        ∫ t : ℝ,
          ((∑ i : Fin (r + 1),
            stieltjesLogAtom (quadraticCoordinate (a i)) t) -
              ∑ i : Fin r,
                stieltjesLogAtom (quadraticCoordinate (b i)) t) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hpositive] with t ht
          exact stieltjesPhase_eq_logAtom_sum h ht
    _ = (∑ i : Fin (r + 1),
          ∫ t : ℝ, stieltjesLogAtom (quadraticCoordinate (a i)) t ∂μ) -
            ∑ i : Fin r,
              ∫ t : ℝ, stieltjesLogAtom (quadraticCoordinate (b i)) t ∂μ := by
          rw [integral_sub hasum hbsum,
            integral_finsetSum _ (fun i _ => ha i),
            integral_finsetSum _ (fun i _ => hb i)]
    _ = 2 * Real.log 2 * Phi a b := by
          simp_rw [hma, hmb]
          unfold Phi
          rw [← Finset.mul_sum, ← Finset.mul_sum]
          ring

end MetricCodes.Spherical.HigherHierarchy

end

section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace MetricCodes.Spherical.HigherHierarchy

theorem sphericalEntropy_naturalLogIdentity (u : ℝ) :
    2 * ((1 + u) * Real.log (1 + u) - u * Real.log u) =
      2 * Real.log 2 * MetricCodes.sphericalEntropy u := by
  have htwo : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  unfold MetricCodes.sphericalEntropy Real.logb
  field_simp

theorem comparisonLogAtom_moment {u : ℝ} (hu : 0 ≤ u) :
    (∫ t : ℝ,
      stieltjesLogAtom (quadraticCoordinate u) t
        ∂Entropy.comparisonMeasure) =
      2 * Real.log 2 * MetricCodes.sphericalEntropy u := by
  change (∫ t : ℝ,
    Real.log ((t + u * (1 + u)) / t)
      ∂Entropy.comparisonMeasure) = _
  rw [Entropy.comparison_logAtom_integral hu]
  exact sphericalEntropy_naturalLogIdentity u

theorem comparisonMeasure_ae_positive_le_one :
    ∀ᵐ t ∂Entropy.comparisonMeasure, 0 < t ∧ t ≤ 1 := by
  filter_upwards [Entropy.comparisonMeasure_ae_mem_Ioo] with t ht
  constructor
  · exact ht.1
  · have hendpoint : Entropy.endpoint = (1 / 4 : ℝ) := rfl
    rw [hendpoint] at ht
    linarith [ht.2]

theorem arcsineMeasure_ae_positive :
    ∀ᵐ t ∂Entropy.arcsineMeasure, 0 < t := by
  filter_upwards [Entropy.arcsineMeasure_ae_mem_Ioo] with t ht
  exact ht.1

theorem stieltjesPhase_comparison_integrable {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b)
    (hlogMoment :
      (∫ t : ℝ, Real.log t ∂Entropy.comparisonMeasure) = -2) :
    Integrable (stieltjesPhase a b) Entropy.comparisonMeasure := by
  have hlog := Entropy.comparison_log_integrable_of_logMoment hlogMoment
  apply stieltjesPhase_integrable_of_logAtoms h
    Entropy.comparisonMeasure
    (comparisonMeasure_ae_positive_le_one.mono (fun _ h => h.1))
  · intro i
    exact stieltjesLogAtom_integrable_of_log
      Entropy.comparisonMeasure (h.ambient_quadratic_nonneg i)
      comparisonMeasure_ae_positive_le_one hlog
  · intro i
    exact stieltjesLogAtom_integrable_of_log
      Entropy.comparisonMeasure (h.stabilizer_quadratic_pos i).le
      comparisonMeasure_ae_positive_le_one hlog

theorem exp_neg_stieltjesPhase_arcsine_integrable {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) :
    Integrable (fun t : ℝ => Real.exp (-stieltjesPhase a b t))
      Entropy.arcsineMeasure :=
  exp_neg_stieltjesPhase_integrable h Entropy.arcsineMeasure
    arcsineMeasure_ae_positive

theorem stieltjesPhase_arcsine_normalizer {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b)
    (harcsine : ∀ x : ℝ, 0 ≤ x →
      (∫ t : ℝ, t / (t + x) ∂Entropy.arcsineMeasure) =
        1 - Real.sqrt (x / (x + 1 / 4))) :
    Entropy.phaseNormalizer (stieltjesPhase a b) =
      1 - 2 * Gamma a b := by
  unfold Entropy.phaseNormalizer
  apply integral_exp_neg_stieltjesPhase_eq_one_sub_two_Gamma h
    Entropy.arcsineMeasure arcsineMeasure_ae_positive
  intro i
  rw [harcsine (quadraticCoordinate (a i))
    (h.ambient_quadratic_nonneg i),
    quadratic_spectralAtom_identity (h.ambient_nonneg i)]

theorem stieltjesPhase_comparison_moment {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b)
    (hlogMoment :
      (∫ t : ℝ, Real.log t ∂Entropy.comparisonMeasure) = -2)
    (hcomparison : ∀ u : ℝ, 0 ≤ u →
      (∫ t : ℝ,
        stieltjesLogAtom (quadraticCoordinate u) t
          ∂Entropy.comparisonMeasure) =
        2 * Real.log 2 * MetricCodes.sphericalEntropy u) :
    (∫ t : ℝ, stieltjesPhase a b t ∂Entropy.comparisonMeasure) =
      2 * Real.log 2 * Phi a b := by
  have hlog := Entropy.comparison_log_integrable_of_logMoment hlogMoment
  apply integral_stieltjesPhase_eq_two_log_mul_Phi h
    Entropy.comparisonMeasure
    (comparisonMeasure_ae_positive_le_one.mono (fun _ h => h.1))
  · intro i
    exact stieltjesLogAtom_integrable_of_log
      Entropy.comparisonMeasure (h.ambient_quadratic_nonneg i)
      comparisonMeasure_ae_positive_le_one hlog
  · intro i
    exact stieltjesLogAtom_integrable_of_log
      Entropy.comparisonMeasure (h.stabilizer_quadratic_pos i).le
      comparisonMeasure_ae_positive_le_one hlog
  · intro i
    exact hcomparison (a i) (h.ambient_nonneg i)
  · intro i
    exact hcomparison (b i) (h.stabilizer_pos i).le

theorem hierarchyPackingObjective_le_criticalExponent_of_betaIntegrals
    {r : ℕ} {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b)
    (hlogMoment :
      (∫ t : ℝ, Real.log t ∂Entropy.comparisonMeasure) = -2)
    (harcsine : ∀ x : ℝ, 0 ≤ x →
      (∫ t : ℝ, t / (t + x) ∂Entropy.arcsineMeasure) =
        1 - Real.sqrt (x / (x + 1 / 4)))
    (hcomparison : ∀ u : ℝ, 0 ≤ u →
      (∫ t : ℝ,
        stieltjesLogAtom (quadraticCoordinate u) t
          ∂Entropy.comparisonMeasure) =
        2 * Real.log 2 * MetricCodes.sphericalEntropy u) :
    hierarchyPackingObjective a b ≤ CohnElkies.criticalBinaryExponent := by
  exact Entropy.packingObjective_le_limitingPackingExponent_of_logMoment
    hlogMoment
    (stieltjesPhase_comparison_integrable h hlogMoment)
    (exp_neg_stieltjesPhase_arcsine_integrable h)
    (stieltjesPhase_arcsine_normalizer h harcsine)
    (stieltjesPhase_comparison_moment h hlogMoment hcomparison)

theorem hierarchyPackingExponent_le_criticalExponent_of_betaIntegrals
    (hlogMoment :
      (∫ t : ℝ, Real.log t ∂Entropy.comparisonMeasure) = -2)
    (harcsine : ∀ x : ℝ, 0 ≤ x →
      (∫ t : ℝ, t / (t + x) ∂Entropy.arcsineMeasure) =
        1 - Real.sqrt (x / (x + 1 / 4)))
    (hcomparison : ∀ u : ℝ, 0 ≤ u →
      (∫ t : ℝ,
        stieltjesLogAtom (quadraticCoordinate u) t
          ∂Entropy.comparisonMeasure) =
        2 * Real.log 2 * MetricCodes.sphericalEntropy u) :
    hierarchyPackingExponent ≤
      (CohnElkies.criticalBinaryExponent : EReal) := by
  apply hierarchyPackingExponent_le_of_forall
  intro r a b h _
  exact hierarchyPackingObjective_le_criticalExponent_of_betaIntegrals
    h hlogMoment harcsine hcomparison

theorem arcsineMeasure_stieltjesKernel {x : ℝ} (hx : 0 ≤ x) :
    (∫ t : ℝ, t / (t + x) ∂Entropy.arcsineMeasure) =
      1 - Real.sqrt (x / (x + 1 / 4)) := by
  simpa [Entropy.arcsineMeasure] using
    ArcsineTransform.arcsine_integral_self_div_add hx

theorem hierarchyPackingExponent_le_criticalExponent :
    hierarchyPackingExponent ≤
      (CohnElkies.criticalBinaryExponent : EReal) :=
  hierarchyPackingExponent_le_criticalExponent_of_betaIntegrals
    Entropy.comparison_logMoment
    (fun _ hx => arcsineMeasure_stieltjesKernel hx)
    (fun _ hu => comparisonLogAtom_moment hu)

end MetricCodes.Spherical.HigherHierarchy

end

section

noncomputable section

namespace MetricCodes.Spherical.HigherHierarchy

theorem hierarchyPackingExponent_eq_criticalBinaryExponent :
    hierarchyPackingExponent = (CohnElkies.criticalBinaryExponent : EReal) :=
  le_antisymm hierarchyPackingExponent_le_criticalExponent
    MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.criticalExponent_le_hierarchyPackingExponent

end MetricCodes.Spherical.HigherHierarchy

end

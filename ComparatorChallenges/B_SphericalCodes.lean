import Mathlib

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Metric
open scoped BigOperators ENNReal InnerProductSpace Topology

namespace CohnElkies

def criticalBinaryExponent : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1)

end CohnElkies

namespace MetricCodes

instance numeralTwoAtLeast : Nat.AtLeastTwo 2 := ⟨by decide⟩

def sphericalEntropy (u : ℝ) : ℝ :=
  (1 + u) * Real.logb 2 (1 + u) - u * Real.logb 2 u

def Gamma (a b : ℝ) : ℝ :=
  ((a - b) * (1 + a + b)) /
    ((1 + 2 * a) * Real.sqrt (a * (1 + a)))

def classicalThreshold (s : ℝ) : ℝ :=
  (1 / Real.sqrt (1 - s ^ 2) - 1) / 2

end MetricCodes

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

theorem packingConstant_sharp_binary_asymptotic_upper :
    ∃ e : ℕ → ℝ,
      Tendsto e atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        packingConstant n ≤
          ENNReal.ofReal
            ((2 : ℝ) ^
              (-(CohnElkies.criticalBinaryExponent + e n) * (n : ℝ))) := by
  sorry

end SpherePacking

namespace MetricCodes.Spherical

def Feasible (s a b : ℝ) : Prop :=
  0 < b ∧ b < a ∧ s < 2 * MetricCodes.Gamma a b

def rateSet (s : ℝ) : Set ℝ :=
  {r | ∃ a b : ℝ, Feasible s a b ∧
    r = MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b}

def variationalRate (s : ℝ) : ℝ := sInf (rateSet s)

theorem kissing_variationalRate_lt :
    variationalRate ((1 : ℝ) / 2) < (0.397305601680 : ℝ) := by
  sorry

def packingObjective (s a b : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 (2 / (1 - s)) -
    MetricCodes.sphericalEntropy a + MetricCodes.sphericalEntropy b

def packingExponentSet : Set EReal :=
  {r | ∃ s a b : ℝ, 0 < s ∧ s < 1 ∧ Feasible s a b ∧
    r = (packingObjective s a b : EReal)}

def packingExponent : EReal := sSup packingExponentSet

theorem packingExponent_gt :
    ((0.602872829455 : ℝ) : EReal) < packingExponent := by
  sorry

def classicalPackingObjective (s : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 (2 / (1 - s)) -
    MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s)

def classicalPackingExponent : EReal :=
  sSup {r : EReal | ∃ s : ℝ, 0 < s ∧ s < 1 ∧
    r = (classicalPackingObjective s : EReal)}

theorem classicalPackingObjective_lt_packingExponent
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (classicalPackingObjective s : EReal) < packingExponent := by
  sorry

theorem classicalPackingExponent_lt_packingExponent :
    classicalPackingExponent < packingExponent := by
  sorry

end MetricCodes.Spherical

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

def hierarchyRateSet (s : ℝ) : Set ℝ :=
  {z | ∃ (r : ℕ) (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
    Interlacing a b ∧ s < 2 * Gamma a b ∧ z = Phi a b}

def hierarchyVariationalRate (s : ℝ) : ℝ := sInf (hierarchyRateSet s)

def hierarchyKissingExponent : ℝ :=
  hierarchyVariationalRate ((1 : ℝ) / 2)

theorem hierarchyKissingExponent_lt_published :
    hierarchyKissingExponent < (0.39661 : ℝ) := by
  sorry

def hierarchyPackingObjective {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 (2 / (1 - 2 * Gamma a b)) - Phi a b

def hierarchyPackingExponentSet : Set EReal :=
  {z | ∃ (r : ℕ) (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
    Interlacing a b ∧ 0 < Gamma a b ∧
      z = (hierarchyPackingObjective a b : EReal)}

def hierarchyPackingExponent : EReal := sSup hierarchyPackingExponentSet

theorem hierarchyPackingExponent_eq_criticalBinaryExponent :
    hierarchyPackingExponent = (CohnElkies.criticalBinaryExponent : EReal) := by
  sorry

end MetricCodes.Spherical.HigherHierarchy

end

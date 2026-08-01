
import Mathlib.Order.MinMax

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

def profileBooleanMin {α : Type*} [LinearOrder α] (profile : Bool → α) : α :=
  min (profile false) (profile true)

@[simp] theorem profileBooleanMin_not {α : Type*} [LinearOrder α]
    (profile : Bool → α) :
    profileBooleanMin (fun sign => profile (!sign)) =
      profileBooleanMin profile := by
  simp [profileBooleanMin, min_comm]

theorem profileBooleanMin_equiv {α : Type*} [LinearOrder α]
    (profile : Bool → α) (equivalence : Bool ≃ Bool) :
    profileBooleanMin (fun sign => profile (equivalence sign)) =
      profileBooleanMin profile := by
  have hne : equivalence false ≠ equivalence true :=
    equivalence.injective.ne (by decide)
  cases hfalse : equivalence false <;>
    cases htrue : equivalence true <;>
      simp_all [profileBooleanMin, min_comm]

def profilePairMin {α : Type*} [LinearOrder α] (first second : α) : α :=
  min first second

@[simp] theorem profilePairMin_swap {α : Type*} [LinearOrder α]
    (first second : α) :
    profilePairMin second first = profilePairMin first second := by
  exact min_comm second first

def profileCanonicalPair {α : Type*} [LinearOrder α]
    (first second : α) : α × α :=
  (min first second, max first second)

@[simp] theorem profileCanonicalPair_swap {α : Type*} [LinearOrder α]
    (first second : α) :
    profileCanonicalPair second first =
      profileCanonicalPair first second := by
  simp [profileCanonicalPair, min_comm, max_comm]

@[simp] theorem profileCanonicalPair_idempotent {α : Type*} [LinearOrder α]
    (first second : α) :
    profileCanonicalPair (profileCanonicalPair first second).1
        (profileCanonicalPair first second).2 =
      profileCanonicalPair first second := by
  simp [profileCanonicalPair, min_le_max]

end ConnesRigidity.AffineSymplecticOrbitCertificate

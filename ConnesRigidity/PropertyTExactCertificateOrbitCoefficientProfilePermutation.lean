
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Multiset.Sort

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

def orbitProfileSort {α : Type*} [LinearOrder α]
    (profile : Fin 4 → α) : List α :=
  (List.ofFn profile).mergeSort (· ≤ ·)

theorem orbitProfileSort_comp_perm {α : Type*} [LinearOrder α]
    (profile : Fin 4 → α) (permutation : Equiv.Perm (Fin 4)) :
    orbitProfileSort (profile ∘ permutation) = orbitProfileSort profile := by
  unfold orbitProfileSort
  apply List.Perm.eq_of_pairwise'
    (List.pairwise_mergeSort' (· ≤ ·) (List.ofFn (profile ∘ permutation)))
    (List.pairwise_mergeSort' (· ≤ ·) (List.ofFn profile))
  exact (List.mergeSort_perm _ _).trans
    ((permutation.ofFn_comp_perm profile).trans
      (List.mergeSort_perm _ _).symm)

theorem orbitProfileSort_eq_of_perm {α : Type*} [LinearOrder α]
    (first second : Fin 4 → α) (permutation : Equiv.Perm (Fin 4))
    (hequivariance : ∀ index, first index = second (permutation index)) :
    orbitProfileSort first = orbitProfileSort second := by
  have hprofiles : first = second ∘ permutation := by
    funext index
    exact hequivariance index
  rw [hprofiles, orbitProfileSort_comp_perm]

theorem mem_orbitProfileSort {α : Type*} [LinearOrder α]
    (profile : Fin 4 → α) (value : α) :
    value ∈ orbitProfileSort profile ↔ ∃ index, profile index = value := by
  unfold orbitProfileSort
  rw [(List.mergeSort_perm _ _).mem_iff]
  exact List.mem_ofFn

end ConnesRigidity.AffineSymplecticOrbitCertificate

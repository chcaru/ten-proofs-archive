
import ConnesRigidity.PropertyTExactCertificateOrbitFiniteAverage
import ConnesRigidity.PropertyTExactCertificateOrbitFiniteGroup

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators

noncomputable def orbitSymmetryIndexPermutation (s : Fin 64) :
    Fin 64 ≃ Fin 64 :=
  OrbitSymmetry.equivFin.symm.trans
    ((Equiv.mulLeft (show OrbitSymmetry from ⟨s⟩)).trans
      OrbitSymmetry.equivFin)

noncomputable def groupRingOrbitAverage
    (value : RationalGroupRing constructedGammaZeroGroup) :
    RationalGroupRing constructedGammaZeroGroup :=
  groupRingSymmetryAverage (Finset.univ : Finset (Fin 64))
    orbitSymmetry value

theorem orbitSymmetry_comp_eq_indexPermutation
    (s i : Fin 64) :
    (orbitSymmetry i).trans (orbitSymmetry s) =
      orbitSymmetry (orbitSymmetryIndexPermutation s i) := by
  simpa [orbitSymmetryIndexPermutation, OrbitSymmetry.equivFin] using
    (orbitSymmetry_mul (show OrbitSymmetry from ⟨s⟩)
      (show OrbitSymmetry from ⟨i⟩)).symm

theorem groupRingOrbitAverage_invariant
    (value : RationalGroupRing constructedGammaZeroGroup)
    (s : Fin 64) :
    groupRingMap (orbitSymmetry s)
        (groupRingSymmetryAverage (Finset.univ : Finset (Fin 64))
          orbitSymmetry value) =
      groupRingSymmetryAverage (Finset.univ : Finset (Fin 64))
        orbitSymmetry value := by
  apply groupRingSymmetryAverage_univ_invariant_of_perm
    orbitSymmetry (orbitSymmetry s) (orbitSymmetryIndexPermutation s)
  intro i
  exact orbitSymmetry_comp_eq_indexPermutation s i

theorem groupRingOrbitAverage_groupRingMap
    (value : RationalGroupRing constructedGammaZeroGroup)
    (s : Fin 64) :
    groupRingMap (orbitSymmetry s) (groupRingOrbitAverage value) =
      groupRingOrbitAverage value := by
  exact groupRingOrbitAverage_invariant value s

theorem groupRingOrbitAverage_coeff_invariant
    (value : RationalGroupRing constructedGammaZeroGroup)
    (s : Fin 64) (g : constructedGammaZeroGroup) :
    (groupRingOrbitAverage value).coeff (orbitSymmetry s g) =
      (groupRingOrbitAverage value).coeff g := by
  exact groupRingSymmetryAverage_univ_coeff_invariant_of_perm
    orbitSymmetry (orbitSymmetry s) (orbitSymmetryIndexPermutation s)
    (orbitSymmetry_comp_eq_indexPermutation s) value g

end ConnesRigidity.AffineSymplecticOrbitCertificate

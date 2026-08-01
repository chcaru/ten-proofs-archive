
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedActionValidation
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedCoordinate

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

theorem canonicalPackedActionImageCoordinate_sound
    (symmetry : Fin 64) (row : Array Int)
    (hsize : row.size = 20)
    (hbound : targetCoordinateBounds row.toList = true)
    (coordinate : Fin 20) :
    canonicalPackedActionCoordinate
        (canonicalPackedActionCode symmetry.val)
        (canonicalPackedRow row) coordinate.val =
      signedAffineCoordinate
        (symmetryData.getD symmetry.val #[]) row coordinate.val := by
  have hsource :=
    (canonicalPackedActionRecord_sound symmetry coordinate).1
  have hsourceIndex :
      canonicalPackedActionSource
          (canonicalPackedActionCode symmetry.val) coordinate.val < row.size := by
    omega
  have hrowRange :
      ∀ (index : Nat) (hindex : index < row.size),
        -8 ≤ row[index]'hindex ∧ row[index]'hindex < 8 := by
    intro index hindex
    have hmember : row[index]'hindex ∈ row.toList :=
      Array.mem_toList_iff.mpr (Array.getElem_mem hindex)
    have hcoordinate := List.all_eq_true.mp hbound _ hmember
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using hcoordinate
  have hpacked := canonicalPackedCoordinate_eq_getD row
    (canonicalPackedActionSource
      (canonicalPackedActionCode symmetry.val) coordinate.val)
    hsourceIndex hrowRange
  have himage := canonicalPackedActionCoordinate_eq_arrayCoordinate
    (canonicalPackedActionCode symmetry.val) (canonicalPackedRow row)
    coordinate.val row hpacked
  exact himage.trans
    (canonicalPackedActionArrayCoordinate_sound symmetry row coordinate)

end

end ConnesRigidity.AffineSymplecticOrbitCertificate


import ConnesRigidity.PropertyTExactCertificateOrbitSymmetryWordData
import ConnesRigidity.PropertyTExactCertificateOrbitBasisTransport
import ConnesRigidity.PropertyTExactCertificateOrbitCheckers
import ConnesRigidity.PropertyTExactCertificateOrbitSymmetryWordInduction

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def orbitBasisDirectTransportCheck
    (symmetry source target : Array Int) : Bool :=
  (List.range 4).all fun i =>
    decide (vectorCoordinate target i =
      signedActionVectorCoordinate symmetry source i) &&
      (List.range 4).all fun j =>
        decide (matrixCoordinate target i j =
          signedActionMatrixCoordinate symmetry source i j)

theorem orbitBasisDirectTransportCheck_sound
    {symmetry source target : Array Int}
    (h : orbitBasisDirectTransportCheck symmetry source target = true) :
    signedTransportCheck symmetry source target = true := by
  unfold signedTransportCheck rawRowEq
  apply List.all_eq_true.mpr
  intro i hi
  have hi20 : i < 20 := List.mem_range.mp hi
  apply decide_eq_true_eq.mpr
  by_cases hm : i < 16
  · have hrow : i / 4 < 4 := by omega
    have hcolumn : i % 4 < 4 := Nat.mod_lt _ (by omega)
    have hcheck := List.all_eq_true.mp h (i / 4)
      (List.mem_range.mpr hrow)
    simp only [Bool.and_eq_true] at hcheck
    have hentry := List.all_eq_true.mp hcheck.2 (i % 4)
      (List.mem_range.mpr hcolumn)
    have hcoordinate := of_decide_eq_true hentry
    have hindex : 4 * (i / 4) + i % 4 = i := by omega
    simpa [signedRowAction, Array.getD, hm, hi20, matrixCoordinate, hindex]
      using hcoordinate.symm
  · have hv : i - 16 < 4 := by omega
    have hcheck := List.all_eq_true.mp h (i - 16)
      (List.mem_range.mpr hv)
    simp only [Bool.and_eq_true] at hcheck
    have hcoordinate := of_decide_eq_true hcheck.1
    have hindex : 16 + (i - 16) = i := by omega
    simpa [signedRowAction, Array.getD, hm, hi20, vectorCoordinate, hindex]
      using hcoordinate.symm

def orbitBasisGeneratorTransportEntries
    (symmetry : Array Int) : List (Array Int) → List Int → Bool
  | [], [] => true
  | source :: sources, target :: targets =>
      orbitIndexCheck target basisData.size &&
        orbitBasisDirectTransportCheck symmetry source
          (basisData.getD target.toNat #[]) &&
        orbitBasisGeneratorTransportEntries symmetry sources targets
  | _, _ => false

def orbitBasisGeneratorTransportRowCheck (generator : Int) : Bool :=
  orbitIndexCheck generator symmetryData.size &&
    match symmetryData[generator.toNat]?,
        basisPermutationData[generator.toNat]? with
    | some symmetry, some images =>
        decide (images.size = basisData.size) &&
          orbitBasisGeneratorTransportEntries symmetry
            basisData.toList images.toList
    | _, _ => false

theorem orbitBasisGeneratorTransportEntries_sound
    (symmetry : Array Int)
    (sources : List (Array Int)) (images : List Int)
    (hcheck : orbitBasisGeneratorTransportEntries
      symmetry sources images = true) :
    ∀ source image,
      (source, image) ∈ List.zip sources images →
        orbitBasisDirectTransportCheck symmetry source
          (basisData.getD image.toNat #[]) = true := by
  induction sources generalizing images with
  | nil => simp
  | cons source sources ih =>
      cases images with
      | nil => simp [orbitBasisGeneratorTransportEntries] at hcheck
      | cons image images =>
          simp only [orbitBasisGeneratorTransportEntries,
            Bool.and_eq_true] at hcheck
          intro source' image' hmem
          simp only [List.zip_cons_cons, List.mem_cons] at hmem
          rcases hmem with hfirst | hremaining
          · cases hfirst
            exact hcheck.1.2
          · exact ih images hcheck.2 source' image' hremaining

theorem orbitBasisGeneratorTransportRowCheck_sound
    (generator : Fin 64) (index : Fin 425)
    (hsymmetry : generator.val < symmetryData.size)
    (hpermutation : generator.val < basisPermutationData.size)
    (hbasis : basisData.size = 425)
    (hcheck : orbitBasisGeneratorTransportRowCheck
      (generator.val : Int) = true) :
    signedTransportCheck
      (symmetryData.getD generator.val #[])
      (basisData.getD index.val #[])
      (basisData.getD
        (symmetryBasisImage generator.val index.val) #[]) = true := by
  have hsymmetryRow : symmetryData[generator.val]? =
      some symmetryData[generator.val] := by
    simp [hsymmetry]
  have hpermutationRow : basisPermutationData[generator.val]? =
      some basisPermutationData[generator.val] := by
    simp [hpermutation]
  simp only [orbitBasisGeneratorTransportRowCheck,
    Int.toNat_natCast, hsymmetryRow, hpermutationRow,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have hsource : index.val < basisData.size := by
    simp [hbasis]
  have himage : index.val <
      (basisPermutationData[generator.val]).size := by
    rw [hcheck.2.1]
    exact hsource
  have hzip : index.val <
      (List.zip basisData.toList
        (basisPermutationData[generator.val]).toList).length := by
    simp [List.length_zip, hsource, himage]
  have hmem :
      (basisData[index.val],
        (basisPermutationData[generator.val])[index.val]) ∈
        List.zip basisData.toList
          (basisPermutationData[generator.val]).toList := by
    simpa [List.getElem_zip] using
      (List.getElem_mem
        (l := List.zip basisData.toList
          (basisPermutationData[generator.val]).toList)
        (n := index.val) hzip)
  have hcoordinates := orbitBasisGeneratorTransportEntries_sound
    symmetryData[generator.val]
    basisData.toList (basisPermutationData[generator.val]).toList
    hcheck.2.2 basisData[index.val]
    (basisPermutationData[generator.val])[index.val] hmem
  have htarget : symmetryBasisImage generator.val index.val =
      ((basisPermutationData[generator.val])[index.val]).toNat := by
    simp [symmetryBasisImage, dataEntry,
      Array.getD_eq_getD_getElem?, hpermutation, himage]
  apply orbitBasisDirectTransportCheck_sound
  simpa [Array.getD_eq_getD_getElem?, hsymmetry,
    hsource, htarget] using hcoordinates

theorem orbitBasisGeneratorTransport_24_valid :
    orbitBasisGeneratorTransportRowCheck 24 = true := by
  unfold orbitBasisGeneratorTransportRowCheck
    orbitBasisGeneratorTransportEntries orbitBasisDirectTransportCheck
    signedActionMatrixCoordinate signedActionVectorCoordinate
    matrixCoordinate vectorCoordinate symmetryPermutationCoordinate
    symmetrySignCoordinate orbitIndexCheck symmetryData basisData
    basisPermutationData
  decide +kernel

theorem orbitBasisGeneratorTransport_1_valid :
    orbitBasisGeneratorTransportRowCheck 1 = true := by
  unfold orbitBasisGeneratorTransportRowCheck
    orbitBasisGeneratorTransportEntries orbitBasisDirectTransportCheck
    signedActionMatrixCoordinate signedActionVectorCoordinate
    matrixCoordinate vectorCoordinate symmetryPermutationCoordinate
    symmetrySignCoordinate orbitIndexCheck symmetryData basisData
    basisPermutationData
  decide +kernel

theorem orbitBasisGeneratorTransport_8_valid :
    orbitBasisGeneratorTransportRowCheck 8 = true := by
  unfold orbitBasisGeneratorTransportRowCheck
    orbitBasisGeneratorTransportEntries orbitBasisDirectTransportCheck
    signedActionMatrixCoordinate signedActionVectorCoordinate
    matrixCoordinate vectorCoordinate symmetryPermutationCoordinate
    symmetrySignCoordinate orbitIndexCheck symmetryData basisData
    basisPermutationData
  decide +kernel

theorem orbitBasisTransport_source_symplectic (index : Fin 425) :
    isSymplecticRow (basisData.getD index.val #[]) = true := by
  have hindex : index.val < basisData.size := by
    simp [orbitBasisData_size]
  have hrow := Array.all_eq_true.mp
    (show basisData.all isSymplecticRow = true from
      orbitBasisRowsSymplecticCheck_valid) index.val hindex
  simpa [Array.getD_eq_getD_getElem?, hindex] using hrow

theorem orbitSymmetry_generator_basis
    (symmetry : OrbitSymmetry)
    (hgenerator : symmetry.index.val ∈ symmetryGeneratorIndices)
    (index : Fin 425) :
    orbitSymmetry symmetry.index (orbitBasis index) =
      orbitBasis
        ⟨symmetryBasisImage symmetry.index.val index.val,
          symmetryBasisImage_lt symmetry.index index⟩ := by
  have hcases : symmetry.index.val = 24 ∨
      symmetry.index.val = 1 ∨ symmetry.index.val = 8 := by
    unfold symmetryGeneratorIndices symmetryGeneratorData at hgenerator
    change symmetry.index.val ∈ [24, 1, 8] at hgenerator
    simpa using hgenerator
  have hcheck : orbitBasisGeneratorTransportRowCheck
      (symmetry.index.val : Int) = true := by
    rcases hcases with htwentyfour | hone | height
    · simpa [htwentyfour] using orbitBasisGeneratorTransport_24_valid
    · simpa [hone] using orbitBasisGeneratorTransport_1_valid
    · simpa [height] using orbitBasisGeneratorTransport_8_valid
  have hsymmetrySize : symmetryData.size = 64 := by
    simpa [symmetryCardinality] using
      (orbitSymmetryCompositionCheck_sound
        orbitSymmetryCompositionCheck_valid).1
  have hsymmetry : symmetry.index.val < symmetryData.size := by
    simp [hsymmetrySize]
  have hpermutation : symmetry.index.val < basisPermutationData.size := by
    rw [(orbitBasisPermutationCheck_sound
      orbitBasisPermutationCheck_valid).1]
    exact hsymmetry
  have htransport := orbitBasisGeneratorTransportRowCheck_sound
    symmetry.index index hsymmetry hpermutation
    orbitBasisData_size hcheck
  change
    (signedNormalizerOfRow
      (symmetryData.getD symmetry.index.val #[])).gammaZeroEquiv
        (gammaZeroOfRow (basisData.getD index.val #[])) =
      gammaZeroOfRow
        (basisData.getD
          (symmetryBasisImage symmetry.index.val index.val) #[])
  exact signedTransportCheck_sound
    (symmetryNormalizerRowChecks symmetry.index)
    (orbitBasisTransport_source_symplectic index) htransport

theorem symmetryBasisImage_one (index : Fin 425) :
    symmetryBasisImage 7 index.val = index.val := by
  have hpermutationSize : basisPermutationData.size = 64 := by
    rw [(orbitBasisPermutationCheck_sound
      orbitBasisPermutationCheck_valid).1]
    simpa [symmetryCardinality] using
      (orbitSymmetryCompositionCheck_sound
        orbitSymmetryCompositionCheck_valid).1
  have hpacked := pairWitnessPackedImage_eq_symmetryBasisImage
    7 index.val (by simp [hpermutationSize]) index.isLt
  rw [← hpacked]
  have hcheck :
      (List.range 425).all
        (fun i => decide (pairWitnessPackedImage 7 i = i)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hcheck index.val
    (List.mem_range.mpr index.isLt))

theorem orbitSymmetry_basis
    (symmetry : OrbitSymmetry) (index : Fin 425) :
    orbitSymmetry symmetry.index (orbitBasis index) =
      orbitBasis
        ⟨symmetryBasisImage symmetry.index.val index.val,
          symmetryBasisImage_lt symmetry.index index⟩ := by
  let property : OrbitSymmetry → Prop := fun element =>
    ∀ basisIndex : Fin 425,
      orbitSymmetry element.index (orbitBasis basisIndex) =
        orbitBasis
          ⟨symmetryBasisImage element.index.val basisIndex.val,
            symmetryBasisImage_lt element.index basisIndex⟩
  have hproperty : ∀ element : OrbitSymmetry, property element := by
    apply orbitSymmetry_word_induction property
    · intro basisIndex
      rw [OrbitSymmetry.automorphism_one]
      change orbitBasis basisIndex =
        orbitBasis
          ⟨symmetryBasisImage 7 basisIndex.val,
            symmetryBasisImage_lt 7 basisIndex⟩
      congr 1
      apply Fin.ext
      exact (symmetryBasisImage_one basisIndex).symm
    · intro generator hgenerator basisIndex
      exact orbitSymmetry_generator_basis generator hgenerator basisIndex
    · intro element hnonidentity hparent hgenerator basisIndex
      have hfactor := word_parent_mul_generator element hnonidentity
      rw [← hfactor, orbitSymmetry_mul, MulEquiv.trans_apply]
      rw [hgenerator basisIndex]
      rw [hparent
        ⟨symmetryBasisImage (wordGeneratorAsOrbit element).index.val
            basisIndex.val,
          symmetryBasisImage_lt
            (wordGeneratorAsOrbit element).index basisIndex⟩]
      congr 1
      apply Fin.ext
      change
        symmetryBasisImage (wordParentAsOrbit element).index.val
            (symmetryBasisImage
              (wordGeneratorAsOrbit element).index.val basisIndex.val) =
          symmetryBasisImage
            (wordParentAsOrbit element *
              wordGeneratorAsOrbit element).index.val basisIndex.val
      rw [word_parent_mul_generator element hnonidentity]
      exact (orbitBasisImage_mul_parent
        element hnonidentity basisIndex).symm
  exact hproperty symmetry index

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

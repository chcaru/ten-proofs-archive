


import ConnesRigidity.PropertyTExactCertificateOrbitSymmetryWordData
import ConnesRigidity.PropertyTExactCertificateOrbitFiniteGroup
import ConnesRigidity.PropertyTExactCertificateOrbitBasisTransport
import ConnesRigidity.PropertyTExactCertificateOrbitCheckerSoundness
import ConnesRigidity.PropertyTExactCertificateOrbitTransportValidation
import ConnesRigidity.PropertyTExactCertificateOrbitPairWitnessValidation











namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open Matrix

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0


theorem orbitBasisData_size : basisData.size = 425 := by
  decide +kernel


theorem orbitBasisRowsSymplecticCheck_valid :
    basisRowsSymplecticCheck = true := by
  decide +kernel


theorem symmetryBasisImage_lt (symmetry : Fin 64) (index : Fin 425) :
    symmetryBasisImage symmetry.val index.val < 425 := by
  have hchecks : basisPermutationData.size = symmetryData.size ∧
      ∀ index, index < basisPermutationData.size →
        orbitBasisPermutationRowCheck index = true := by
    simpa only [orbitBasisPermutationCheck, Bool.and_eq_true,
      decide_eq_true_eq, List.all_eq_true, List.mem_range] using
      orbitBasisPermutationCheck_valid
  have hsymmetrySize : symmetryData.size = 64 := by
    simpa [symmetryCardinality] using
      (orbitSymmetryCompositionCheck_sound
        orbitSymmetryCompositionCheck_valid).1
  have hsymmetry : symmetry.val < basisPermutationData.size := by
    rw [hchecks.1, hsymmetrySize]
    exact symmetry.isLt
  have hrow := hchecks.2 symmetry.val hsymmetry
  have hrowOption : basisPermutationData[symmetry.val]? =
      some basisPermutationData[symmetry.val] := by
    simp [hsymmetry]
  simp only [orbitBasisPermutationRowCheck, hrowOption,
    Bool.and_eq_true, decide_eq_true_eq] at hrow
  have hindex : index.val < (basisPermutationData[symmetry.val]).size := by
    rw [hrow.1, orbitBasisData_size]
    exact index.isLt
  have hentry := (List.all_eq_true.mp hrow.2)
    (basisPermutationData[symmetry.val])[index.val]
      (by simp)
  have hbound := orbitIndexCheck_sound
    (basisPermutationData[symmetry.val])[index.val]
    basisData.size hentry
  have hvalue : symmetryBasisImage symmetry.val index.val =
      ((basisPermutationData[symmetry.val])[index.val]).toNat := by
    simp [symmetryBasisImage, dataEntry,
      Array.getD_eq_getD_getElem?, hsymmetry, hindex]
  rw [hvalue]
  simpa [orbitBasisData_size] using (Int.toNat_lt hbound.1).2 hbound.2


def symmetryGeneratorIndices : List Nat :=
  symmetryGeneratorData.map fun row => (row.getD 0 0).toNat


def symmetryWordParent (index : Nat) : Nat :=
  ((symmetryWordParentData.getD index []).getD 0 0).toNat


def symmetryWordGenerator (index : Nat) : Nat :=
  ((symmetryWordParentData.getD index []).getD 1 0).toNat


def symmetryWordDepth (index : Nat) : Nat :=
  ((symmetryWordDepthData.getD index []).getD 0 0).toNat




def orbitSymmetryWordRowCheck (index : Nat) : Bool :=
  if index = symmetryIdentityIndex then
    decide (symmetryWordDepth index = 0)
  else
    decide (index < 64) &&
      (decide (symmetryWordParent index < 64) &&
        (decide (symmetryWordGenerator index < 64) &&
          (decide (symmetryWordGenerator index ∈ symmetryGeneratorIndices) &&
            (decide
              (symmetryWordDepth (symmetryWordParent index) <
                symmetryWordDepth index) &&
              decide
                (symmetryMulIndex (symmetryWordParent index)
                  (symmetryWordGenerator index) = index)))))


def orbitSymmetryWordCheck : Bool :=
  decide (symmetryGeneratorIndices.length = 3) &&
    (decide (symmetryWordParentData.length = 64) &&
      (decide (symmetryWordDepthData.length = 64) &&
        (List.range 64).all orbitSymmetryWordRowCheck))


theorem orbitSymmetryWordCheck_valid : orbitSymmetryWordCheck = true := by
  decide +kernel


theorem orbitSymmetryWordRowCheck_valid (index : Fin 64) :
    orbitSymmetryWordRowCheck index.val = true := by
  have hcheck := orbitSymmetryWordCheck_valid
  simp only [orbitSymmetryWordCheck, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  exact List.all_eq_true.mp hcheck.2.2.2 index.val
    (List.mem_range.mpr index.isLt)


theorem orbitSymmetryWordRowCheck_sound
    (index : Fin 64) (hindex : index.val ≠ symmetryIdentityIndex) :
    symmetryWordParent index.val < 64 ∧
      symmetryWordGenerator index.val < 64 ∧
      symmetryWordGenerator index.val ∈ symmetryGeneratorIndices ∧
      symmetryWordDepth (symmetryWordParent index.val) <
        symmetryWordDepth index.val ∧
      symmetryMulIndex (symmetryWordParent index.val)
        (symmetryWordGenerator index.val) = index.val := by
  have hcheck := orbitSymmetryWordRowCheck_valid index
  simp only [orbitSymmetryWordRowCheck, hindex, ↓reduceIte,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact hcheck.2



theorem orbitSymmetry_index_ne_identity {symmetry : OrbitSymmetry}
    (h : symmetry ≠ 1) :
    symmetry.index.val ≠ symmetryIdentityIndex := by
  intro hindex
  apply h
  apply OrbitSymmetry.ext
  apply Fin.ext
  simpa [symmetryIdentityIndex, OrbitSymmetry.one_index] using hindex


def wordParentAsOrbit (symmetry : OrbitSymmetry) : OrbitSymmetry :=
  ⟨Fin.ofNat 64 (symmetryWordParent symmetry.index.val)⟩


def wordGeneratorAsOrbit (symmetry : OrbitSymmetry) : OrbitSymmetry :=
  ⟨Fin.ofNat 64 (symmetryWordGenerator symmetry.index.val)⟩

@[simp] theorem wordParentAsOrbit_index_val
    {symmetry : OrbitSymmetry} (h : symmetry ≠ 1) :
    (wordParentAsOrbit symmetry).index.val =
      symmetryWordParent symmetry.index.val := by
  change symmetryWordParent symmetry.index.val % 64 =
    symmetryWordParent symmetry.index.val
  exact Nat.mod_eq_of_lt
    (orbitSymmetryWordRowCheck_sound symmetry.index
      (orbitSymmetry_index_ne_identity h)).1

@[simp] theorem wordGeneratorAsOrbit_index_val
    {symmetry : OrbitSymmetry} (h : symmetry ≠ 1) :
    (wordGeneratorAsOrbit symmetry).index.val =
      symmetryWordGenerator symmetry.index.val := by
  change symmetryWordGenerator symmetry.index.val % 64 =
    symmetryWordGenerator symmetry.index.val
  exact Nat.mod_eq_of_lt
    (orbitSymmetryWordRowCheck_sound symmetry.index
      (orbitSymmetry_index_ne_identity h)).2.1


theorem word_parent_mul_generator
    (symmetry : OrbitSymmetry) (h : symmetry ≠ 1) :
    wordParentAsOrbit symmetry * wordGeneratorAsOrbit symmetry = symmetry := by
  apply OrbitSymmetry.ext
  apply Fin.ext
  change
    symmetryMulIndex (wordParentAsOrbit symmetry).index.val
      (wordGeneratorAsOrbit symmetry).index.val = symmetry.index.val
  rw [wordParentAsOrbit_index_val h, wordGeneratorAsOrbit_index_val h]
  exact (orbitSymmetryWordRowCheck_sound symmetry.index
    (orbitSymmetry_index_ne_identity h)).2.2.2.2


theorem word_parent_depth_lt
    (symmetry : OrbitSymmetry) (h : symmetry ≠ 1) :
    symmetryWordDepth (wordParentAsOrbit symmetry).index.val <
      symmetryWordDepth symmetry.index.val := by
  rw [wordParentAsOrbit_index_val h]
  exact (orbitSymmetryWordRowCheck_sound symmetry.index
    (orbitSymmetry_index_ne_identity h)).2.2.2.1


theorem word_generator_mem
    (symmetry : OrbitSymmetry) (h : symmetry ≠ 1) :
    (wordGeneratorAsOrbit symmetry).index.val ∈ symmetryGeneratorIndices := by
  rw [wordGeneratorAsOrbit_index_val h]
  exact (orbitSymmetryWordRowCheck_sound symmetry.index
    (orbitSymmetry_index_ne_identity h)).2.2.1






theorem orbitSymmetry_word_induction
    (P : OrbitSymmetry → Prop)
    (hone : P 1)
    (hgenerator : ∀ generator : OrbitSymmetry,
      generator.index.val ∈ symmetryGeneratorIndices → P generator)
    (hstep : ∀ symmetry : OrbitSymmetry, symmetry ≠ 1 →
      P (wordParentAsOrbit symmetry) →
      P (wordGeneratorAsOrbit symmetry) → P symmetry) :
    ∀ symmetry : OrbitSymmetry, P symmetry := by
  have hinduction : ∀ depth : Nat, ∀ symmetry : OrbitSymmetry,
      symmetryWordDepth symmetry.index.val = depth → P symmetry := by
    intro depth
    induction depth using Nat.strong_induction_on with
    | h depth ih =>
        intro symmetry hdepth
        by_cases hidentity : symmetry = 1
        · simpa [hidentity] using hone
        · apply hstep symmetry hidentity
          · apply ih (symmetryWordDepth
              (wordParentAsOrbit symmetry).index.val)
            · rw [← hdepth]
              exact word_parent_depth_lt symmetry hidentity
            · rfl
          · exact hgenerator (wordGeneratorAsOrbit symmetry)
              (word_generator_mem symmetry hidentity)
  intro symmetry
  exact hinduction (symmetryWordDepth symmetry.index.val) symmetry rfl






def orbitBasisParentPermutationEntries (packedParent : Nat) :
    List Int → List Int → Bool
  | [], [] => true
  | image :: images, generator :: generators =>
      decide (image.toNat =
        pairWitnessPackedIndex packedParent generator.toNat) &&
        orbitBasisParentPermutationEntries packedParent images generators
  | _, _ => false



theorem orbitBasisParentPermutationEntries_sound
    (packedParent : Nat) (images generators : List Int)
    (hcheck : orbitBasisParentPermutationEntries
      packedParent images generators = true) :
    ∀ image generator,
      (image, generator) ∈ List.zip images generators →
        image.toNat =
          pairWitnessPackedIndex packedParent generator.toNat := by
  induction images generalizing generators with
  | nil => simp
  | cons image images ih =>
      cases generators with
      | nil => simp [orbitBasisParentPermutationEntries] at hcheck
      | cons generator generators =>
          simp only [orbitBasisParentPermutationEntries,
            Bool.and_eq_true, decide_eq_true_eq] at hcheck
          intro image' generator' hmem
          simp only [List.zip_cons_cons, List.mem_cons] at hmem
          rcases hmem with hfirst | hremaining
          · cases hfirst
            exact hcheck.1
          · exact ih generators hcheck.2
              image' generator' hremaining



def orbitBasisParentPermutationRowCheck (index : Nat) : Bool :=
  if index = symmetryIdentityIndex then true
  else
    match basisPermutationData[index]?,
        basisPermutationData[symmetryWordGenerator index]? with
    | some images, some generators =>
        decide (images.size = 425) &&
          (decide (generators.size = 425) &&
            orbitBasisParentPermutationEntries
              (pairWitnessPackedPermutationRows.getD
                (symmetryWordParent index) 0)
              images.toList generators.toList)
    | _, _ => false


def orbitBasisParentPermutationCheck : Bool :=
  (List.range 64).all orbitBasisParentPermutationRowCheck


theorem orbitBasisParentPermutationCheck_valid :
    orbitBasisParentPermutationCheck = true := by
  decide +kernel



theorem orbitBasisImage_mul_parent
    (symmetry : OrbitSymmetry) (h : symmetry ≠ 1)
    (index : Fin 425) :
    symmetryBasisImage symmetry.index.val index.val =
      symmetryBasisImage (wordParentAsOrbit symmetry).index.val
        (symmetryBasisImage (wordGeneratorAsOrbit symmetry).index.val
          index.val) := by
  have hcheck := List.all_eq_true.mp
    orbitBasisParentPermutationCheck_valid symmetry.index.val
      (List.mem_range.mpr symmetry.index.isLt)
  have hindex := orbitSymmetry_index_ne_identity h
  have hsymmetrySize : symmetryData.size = 64 := by
    simpa [symmetryCardinality] using
      (orbitSymmetryCompositionCheck_sound
        orbitSymmetryCompositionCheck_valid).1
  have hpermutationSize : basisPermutationData.size = 64 := by
    rw [(orbitBasisPermutationCheck_sound
      orbitBasisPermutationCheck_valid).1, hsymmetrySize]
  have hparentBound : symmetryWordParent symmetry.index.val <
      basisPermutationData.size := by
    rw [hpermutationSize]
    exact (orbitSymmetryWordRowCheck_sound symmetry.index hindex).1
  have hgeneratorBound : symmetryWordGenerator symmetry.index.val <
      basisPermutationData.size := by
    rw [hpermutationSize]
    exact (orbitSymmetryWordRowCheck_sound symmetry.index hindex).2.1
  have hsymmetryBound : symmetry.index.val <
      basisPermutationData.size := by
    simp [hpermutationSize]
  have hsymmetryRow : basisPermutationData[symmetry.index.val]? =
      some basisPermutationData[symmetry.index.val] := by
    simp [hsymmetryBound]
  have hgeneratorRow :
      basisPermutationData[symmetryWordGenerator symmetry.index.val]? =
        some basisPermutationData[
          symmetryWordGenerator symmetry.index.val] := by
    simp [hgeneratorBound]
  simp only [orbitBasisParentPermutationRowCheck, hindex,
    ↓reduceIte, hsymmetryRow, hgeneratorRow,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have himageIndex : index.val <
      (basisPermutationData[symmetry.index.val]).size := by
    rw [hcheck.1]
    exact index.isLt
  have hgeneratorIndex : index.val <
      (basisPermutationData[
        symmetryWordGenerator symmetry.index.val]).size := by
    rw [hcheck.2.1]
    exact index.isLt
  have hzip : index.val <
      (List.zip
        (basisPermutationData[symmetry.index.val]).toList
        (basisPermutationData[
          symmetryWordGenerator symmetry.index.val]).toList).length := by
    simp [List.length_zip, himageIndex, hgeneratorIndex]
  have hmem :
      ((basisPermutationData[symmetry.index.val])[index.val],
        (basisPermutationData[
          symmetryWordGenerator symmetry.index.val])[index.val]) ∈
        List.zip
          (basisPermutationData[symmetry.index.val]).toList
          (basisPermutationData[
            symmetryWordGenerator symmetry.index.val]).toList := by
    simpa [List.getElem_zip] using
      (List.getElem_mem
        (l := List.zip
          (basisPermutationData[symmetry.index.val]).toList
          (basisPermutationData[
            symmetryWordGenerator symmetry.index.val]).toList)
        (n := index.val) hzip)
  have heq := orbitBasisParentPermutationEntries_sound
    (pairWitnessPackedPermutationRows.getD
      (symmetryWordParent symmetry.index.val) 0)
    (basisPermutationData[symmetry.index.val]).toList
    (basisPermutationData[
      symmetryWordGenerator symmetry.index.val]).toList
    hcheck.2.2
    (basisPermutationData[symmetry.index.val])[index.val]
    (basisPermutationData[
      symmetryWordGenerator symmetry.index.val])[index.val]
    hmem
  simp only [wordParentAsOrbit_index_val h,
    wordGeneratorAsOrbit_index_val h]
  have hgeneratorValue :
      ((basisPermutationData[
        symmetryWordGenerator symmetry.index.val])[index.val]).toNat =
        symmetryBasisImage
          (symmetryWordGenerator symmetry.index.val) index.val := by
    simp [symmetryBasisImage, dataEntry,
      Array.getD_eq_getD_getElem?, hgeneratorBound, hgeneratorIndex]
  have hparentImageBound :
      symmetryBasisImage
        (symmetryWordGenerator symmetry.index.val) index.val < 425 := by
    simpa [wordGeneratorAsOrbit_index_val h] using
      symmetryBasisImage_lt (wordGeneratorAsOrbit symmetry).index index
  have hpacked := pairWitnessPackedImage_eq_symmetryBasisImage
    (symmetryWordParent symmetry.index.val)
    (symmetryBasisImage
      (symmetryWordGenerator symmetry.index.val) index.val)
    hparentBound hparentImageBound
  have himageValue :
      symmetryBasisImage symmetry.index.val index.val =
        ((basisPermutationData[
          symmetry.index.val])[index.val]).toNat := by
    simp [symmetryBasisImage, dataEntry,
      Array.getD_eq_getD_getElem?, hsymmetryBound, himageIndex]
  rw [himageValue]
  rw [← hpacked]
  simpa [pairWitnessPackedImage, hgeneratorValue] using heq

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

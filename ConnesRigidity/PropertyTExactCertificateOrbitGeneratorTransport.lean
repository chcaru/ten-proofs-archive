
import ConnesRigidity.PropertyTExactCertificateOrbitBasisTransport
import ConnesRigidity.PropertyTExactCertificateOrbitCheckers
import ConnesRigidity.PropertyTExactCertificateOrbitFiniteGroup
import ConnesRigidity.PropertyTExactCertificateOrbitGeneratorEnumeration

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

local instance generatorTransportDecidableEq :
    DecidableEq constructedGammaZeroGroup :=
  fun x y =>
    decidable_of_iff (x.fst = y.fst ∧ x.snd = y.snd)
      ⟨fun h => by
          cases x
          cases y
          simp_all,
        fun h =>
          ⟨congrArg CocycleExtension.fst h,
            congrArg CocycleExtension.snd h⟩⟩

def symmetryGeneratorImage (s i : Nat) : Nat :=
  (dataEntry generatorPermutationData s i).toNat

def orbitGeneratorDirectTransportCheck
    (symmetry source target : Array Int) : Bool :=
  (List.range 4).all fun i =>
    decide (vectorCoordinate target i =
      signedActionVectorCoordinate symmetry source i) &&
      (List.range 4).all fun j =>
        decide (matrixCoordinate target i j =
          signedActionMatrixCoordinate symmetry source i j)

theorem orbitGeneratorDirectTransportCheck_sound
    {symmetry source target : Array Int}
    (h : orbitGeneratorDirectTransportCheck symmetry source target = true) :
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

def orbitGeneratorTransportEntries
    (symmetry : Array Int) :
    List (Array Int) → List Int → Bool
  | [], [] => true
  | source :: sources, target :: targets =>
      orbitIndexCheck target generatorData.size &&
        orbitGeneratorDirectTransportCheck symmetry source
          (generatorData.getD target.toNat #[]) &&
        orbitGeneratorTransportEntries symmetry sources targets
  | _, _ => false

def orbitGeneratorTransportRows :
    List (Array Int) → List (Array Int) → Bool
  | [], [] => true
  | symmetry :: symmetries, targets :: remaining =>
      decide (targets.size = generatorData.size) &&
        orbitGeneratorTransportEntries symmetry generatorData.toList
          targets.toList &&
        orbitGeneratorTransportRows symmetries remaining
  | _, _ => false

def orbitGeneratorTransportCheck : Bool :=
  decide (symmetryData.size = 64) &&
    decide (generatorData.size = 24) &&
    decide (generatorPermutationData.size = symmetryData.size) &&
    orbitGeneratorTransportRows symmetryData.toList
      generatorPermutationData.toList

theorem orbitGeneratorTransportCheck_valid :
    orbitGeneratorTransportCheck = true := by
  unfold orbitGeneratorTransportCheck orbitGeneratorTransportRows
    orbitGeneratorTransportEntries orbitGeneratorDirectTransportCheck
    signedActionMatrixCoordinate signedActionVectorCoordinate
    matrixCoordinate vectorCoordinate symmetryPermutationCoordinate
    symmetrySignCoordinate orbitIndexCheck symmetryData generatorData
    generatorPermutationData
  decide +kernel

theorem orbitGeneratorTransportEntries_sound
    (symmetry : Array Int) (sources : List (Array Int))
    (targets : List Int)
    (hcheck : orbitGeneratorTransportEntries symmetry sources targets = true) :
    ∀ source target, (source, target) ∈ List.zip sources targets →
      orbitIndexCheck target generatorData.size = true ∧
        orbitGeneratorDirectTransportCheck symmetry source
          (generatorData.getD target.toNat #[]) = true := by
  induction sources generalizing targets with
  | nil => simp
  | cons source sources ih =>
      cases targets with
      | nil =>
          simp [orbitGeneratorTransportEntries] at hcheck
      | cons target targets =>
          simp only [orbitGeneratorTransportEntries, Bool.and_eq_true] at hcheck
          intro source' target' hmem
          simp only [List.zip_cons_cons, List.mem_cons] at hmem
          rcases hmem with hfirst | hrest
          · cases hfirst
            exact ⟨hcheck.1.1, hcheck.1.2⟩
          · exact ih targets hcheck.2 source' target' hrest

theorem orbitGeneratorTransportRows_sound
    (symmetries : List (Array Int)) (rows : List (Array Int))
    (hcheck : orbitGeneratorTransportRows symmetries rows = true) :
    ∀ symmetry targets, (symmetry, targets) ∈ List.zip symmetries rows →
      targets.size = generatorData.size ∧
        orbitGeneratorTransportEntries symmetry generatorData.toList
          targets.toList = true := by
  induction symmetries generalizing rows with
  | nil => simp
  | cons symmetry symmetries ih =>
      cases rows with
      | nil =>
          simp [orbitGeneratorTransportRows] at hcheck
      | cons targets rows =>
          simp only [orbitGeneratorTransportRows, Bool.and_eq_true,
            decide_eq_true_eq] at hcheck
          intro symmetry' targets' hmem
          simp only [List.zip_cons_cons, List.mem_cons] at hmem
          rcases hmem with hfirst | hrest
          · cases hfirst
            exact ⟨hcheck.1.1, hcheck.1.2⟩
          · exact ih rows hcheck.2 symmetry' targets' hrest

theorem orbitGeneratorTransport_index
    (symmetry generator : Nat) (hsymmetry : symmetry < 64)
    (hgenerator : generator < 24) :
    let target := symmetryGeneratorImage symmetry generator
    target < 24 ∧
      orbitGeneratorDirectTransportCheck
        (symmetryData.getD symmetry #[])
        (generatorData.getD generator #[])
        (generatorData.getD target #[]) = true := by
  have hcheck := orbitGeneratorTransportCheck_valid
  simp only [orbitGeneratorTransportCheck, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  have hsymmetrySize : symmetryData.size = 64 := hcheck.1.1.1
  have hgeneratorSize : generatorData.size = 24 := hcheck.1.1.2
  have hpermutationSize : generatorPermutationData.size =
      symmetryData.size := hcheck.1.2
  have hrows := hcheck.2
  have hs : symmetry < symmetryData.size := by omega
  have hp : symmetry < generatorPermutationData.size := by omega
  have hzip : symmetry <
      (List.zip symmetryData.toList generatorPermutationData.toList).length := by
    simp [List.length_zip, hsymmetrySize, hpermutationSize, hsymmetry]
  have hrowmem :
      (symmetryData[symmetry], generatorPermutationData[symmetry]) ∈
        List.zip symmetryData.toList generatorPermutationData.toList := by
    have hmem := List.getElem_mem hzip
    simpa [List.getElem_zip, Array.getElem_toList] using hmem
  obtain ⟨hwidth, hentries⟩ :=
    orbitGeneratorTransportRows_sound symmetryData.toList
      generatorPermutationData.toList hrows _ _ hrowmem
  have hg : generator < generatorData.size := by omega
  have ht : generator < generatorPermutationData[symmetry].size := by omega
  have hentryzip : generator <
      (List.zip generatorData.toList
        generatorPermutationData[symmetry].toList).length := by
    simp [List.length_zip, hgeneratorSize, hwidth, hgenerator]
  have hentrymem :
      (generatorData[generator],
        generatorPermutationData[symmetry][generator]) ∈
        List.zip generatorData.toList
          generatorPermutationData[symmetry].toList := by
    have hmem := List.getElem_mem hentryzip
    simpa [List.getElem_zip, Array.getElem_toList] using hmem
  obtain ⟨hbound, htransport⟩ :=
    orbitGeneratorTransportEntries_sound
      symmetryData[symmetry] generatorData.toList
      generatorPermutationData[symmetry].toList hentries
        _ _ hentrymem
  have hindex := orbitIndexCheck_sound _ _ hbound
  have htarget : (generatorPermutationData[symmetry][generator]).toNat < 24 := by
    have hlt := (Int.toNat_lt hindex.1).2 hindex.2
    omega
  have hlookup :
      symmetryGeneratorImage symmetry generator =
        (generatorPermutationData[symmetry][generator]).toNat := by
    simp [symmetryGeneratorImage, dataEntry,
      Array.getD_eq_getD_getElem?, hp, ht]
  change symmetryGeneratorImage symmetry generator < 24 ∧ _
  constructor
  · rwa [hlookup]
  · simpa [Array.getD_eq_getD_getElem?, hs, hg, hlookup] using htransport

theorem generatorRowsSymplecticCheck_valid :
    generatorRowsSymplecticCheck = true := by
  unfold generatorRowsSymplecticCheck generatorData
  decide +kernel

theorem generatorElement_row_symplectic
    (i : Nat) (hi : i < 24) :
    isSymplecticRow (generatorData.getD i #[]) = true := by
  have hsize : i < generatorData.size := by
    rw [generatorData_size]
    exact hi
  have hvalid : generatorData.all isSymplecticRow = true :=
    generatorRowsSymplecticCheck_valid
  have hrow := Array.all_eq_true.mp hvalid i hsize
  simpa [Array.getD_eq_getD_getElem?, hsize] using hrow

theorem orbitSymmetry_generatorElement
    (symmetry : Fin 64) (generator : Fin 24) :
    orbitSymmetry symmetry (generatorElement generator.val) =
      generatorElement
        (symmetryGeneratorImage symmetry.val generator.val) := by
  obtain ⟨htarget, htransport⟩ :=
    orbitGeneratorTransport_index symmetry.val generator.val
      symmetry.isLt generator.isLt
  unfold orbitSymmetry symmetryNormalizer generatorElement
  exact signedTransportCheck_sound
    (symmetryNormalizerRowChecks symmetry)
    (generatorElement_row_symplectic generator.val generator.isLt)
    (orbitGeneratorDirectTransportCheck_sound htransport)

theorem orbitSymmetry_generators_image
    (symmetry : Fin 64) :
    gammaZeroElementaryGenerators.image (orbitSymmetry symmetry) =
      gammaZeroElementaryGenerators := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨g, hg, himage⟩ := Finset.mem_image.mp hx
    subst x
    have hlist : g ∈ generatorElements := by
      apply List.mem_toFinset.mp
      rw [generatorElements_toFinset_eq]
      exact hg
    obtain ⟨i, hi, heq⟩ := exists_generatorElement_of_mem hlist
    have hi24 : i < 24 := by simpa [generatorData_size] using hi
    rw [← heq, orbitSymmetry_generatorElement symmetry ⟨i, hi24⟩]
    rw [← generatorElements_toFinset_eq]
    apply List.mem_toFinset.mpr
    apply generatorElement_mem
    rw [generatorData_size]
    exact (orbitGeneratorTransport_index symmetry.val i
      symmetry.isLt hi24).1
  · rw [Finset.card_image_of_injective _ (orbitSymmetry symmetry).injective]

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

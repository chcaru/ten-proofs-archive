
import ConnesRigidity.PropertyTExactCertificateOrbitBasis
import ConnesRigidity.PropertyTExactCertificateOrbitCheckers

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open Matrix

noncomputable section

def symmetryIdentityIndex : Nat := 7

def symmetryMulIndex (left right : Nat) : Nat :=
  (dataEntry symmetryMultiplicationData left right).toNat

def orbitSymmetryCompositionCoordinateCheck
    (left right product : Array Int) (coordinate : Nat) : Bool :=
  let source := symmetryPermutationCoordinate left coordinate
  decide (source < 4) &&
    decide
      (symmetryPermutationCoordinate product coordinate =
        symmetryPermutationCoordinate right source) &&
    decide
      (symmetrySignCoordinate product coordinate =
        symmetrySignCoordinate left coordinate *
          symmetrySignCoordinate right source)

def orbitSymmetryCompositionEntryCheck
    (left right : Array Int) (product : Int) : Bool :=
  orbitIndexCheck product symmetryData.size &&
    (List.range 4).all
      (orbitSymmetryCompositionCoordinateCheck left right
        (symmetryData.getD product.toNat #[]))

def orbitSymmetryCompositionRowListCheck
    (left : Array Int) (rights : List (Array Int))
    (products : List Int) : Bool :=
  match rights, products with
  | [], [] => true
  | right :: rights, product :: products =>
      orbitSymmetryCompositionEntryCheck left right product &&
        orbitSymmetryCompositionRowListCheck left rights products
  | _, _ => false

def orbitSymmetryCompositionRowCheck (left : Nat) : Bool :=
  match symmetryData[left]?, symmetryMultiplicationData[left]? with
  | some row, some products =>
      decide (products.size = symmetryData.size) &&
        orbitSymmetryCompositionRowListCheck row symmetryData.toList
          products.toList
  | _, _ => false

def orbitSymmetryCompositionCheck : Bool :=
  decide (symmetryData.size = symmetryCardinality) &&
    decide (symmetryMultiplicationData.size = symmetryData.size) &&
    (List.range symmetryMultiplicationData.size).all
      orbitSymmetryCompositionRowCheck

def orbitSymmetryNormalizerCheck : Bool :=
  symmetryData.toList.all isSignedNormalizerRow

def orbitSymmetryMultiplicationInverseRowCheck (symmetry : Nat) : Bool :=
  match symmetryInverseData[symmetry]? with
  | none => false
  | some row =>
      let inverse := row.getD 0 0
      decide (row.size = 1) &&
        orbitIndexCheck inverse symmetryData.size &&
        decide
          (symmetryMulIndex inverse.toNat symmetry =
            symmetryIdentityIndex) &&
        decide
          (symmetryMulIndex symmetry inverse.toNat =
            symmetryIdentityIndex)

def orbitSymmetryMultiplicationInverseCheck : Bool :=
  decide (symmetryInverseData.size = symmetryData.size) &&
    (List.range symmetryInverseData.size).all
      orbitSymmetryMultiplicationInverseRowCheck

theorem orbitSymmetryCompositionCoordinateCheck_sound
    (left right product : Array Int) (coordinate : Nat)
    (hcheck : orbitSymmetryCompositionCoordinateCheck
      left right product coordinate = true) :
    symmetryPermutationCoordinate left coordinate < 4 ∧
      symmetryPermutationCoordinate product coordinate =
        symmetryPermutationCoordinate right
          (symmetryPermutationCoordinate left coordinate) ∧
      symmetrySignCoordinate product coordinate =
        symmetrySignCoordinate left coordinate *
          symmetrySignCoordinate right
            (symmetryPermutationCoordinate left coordinate) := by
  simpa only [orbitSymmetryCompositionCoordinateCheck,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hcheck

theorem orbitSymmetryCompositionRowListCheck_sound
    (left : Array Int) (rights : List (Array Int)) (products : List Int)
    (hcheck : orbitSymmetryCompositionRowListCheck
      left rights products = true) :
    ∀ right product,
      (right, product) ∈ List.zip rights products →
        orbitSymmetryCompositionEntryCheck left right product = true := by
  induction rights generalizing products with
  | nil =>
      simp
  | cons right rights ih =>
      cases products with
      | nil => simp [orbitSymmetryCompositionRowListCheck] at hcheck
      | cons product products =>
          simp only [orbitSymmetryCompositionRowListCheck,
            Bool.and_eq_true] at hcheck
          intro right' product' hmem
          simp only [List.zip_cons_cons, List.mem_cons] at hmem
          rcases hmem with hfirst | hrest
          · cases hfirst
            exact hcheck.1
          · exact ih products hcheck.2 right' product' hrest

theorem orbitSymmetryCompositionRowCheck_sound
    (left right : Nat)
    (hleft : left < symmetryData.size)
    (hcheck : orbitSymmetryCompositionRowCheck left = true)
    (hright : right < symmetryData.size) :
    orbitSymmetryCompositionEntryCheck
      (symmetryData.getD left #[]) (symmetryData.getD right #[])
      (dataEntry symmetryMultiplicationData left right) = true := by
  have hleftrow : symmetryData[left]? = some symmetryData[left] := by
    simp [hleft]
  cases htable : symmetryMultiplicationData[left]? with
  | none => simp [orbitSymmetryCompositionRowCheck, hleftrow, htable] at hcheck
  | some products =>
      simp only [orbitSymmetryCompositionRowCheck, hleftrow, htable,
        Bool.and_eq_true, decide_eq_true_eq] at hcheck
      have hproduct : right < products.size := hcheck.1 ▸ hright
      have hmem : (symmetryData[right], products[right]) ∈
          List.zip symmetryData.toList products.toList := by
        have hzip : right <
            (List.zip symmetryData.toList products.toList).length := by
          simp [List.length_zip, hright, hproduct]
        simpa [List.getElem_zip] using
          (List.getElem_mem (l := List.zip symmetryData.toList products.toList)
            (n := right) hzip)
      have hentry := orbitSymmetryCompositionRowListCheck_sound
        symmetryData[left] symmetryData.toList products.toList
        hcheck.2 symmetryData[right] products[right] hmem
      simpa [dataEntry, Array.getD_eq_getD_getElem?, hleft, hright,
        htable, hproduct] using hentry

theorem orbitSymmetryCompositionEntryCheck_index_sound
    (left right : Array Int) (product : Int)
    (hcheck : orbitSymmetryCompositionEntryCheck left right product = true) :
    0 ≤ product ∧ product < (symmetryData.size : Int) := by
  simp only [orbitSymmetryCompositionEntryCheck, Bool.and_eq_true] at hcheck
  exact orbitIndexCheck_sound product symmetryData.size hcheck.1

theorem orbitSymmetryCompositionEntryCheck_coordinate_sound
    (left right : Array Int) (product : Int) (coordinate : Nat)
    (hcoordinate : coordinate < 4)
    (hcheck : orbitSymmetryCompositionEntryCheck left right product = true) :
    symmetryPermutationCoordinate left coordinate < 4 ∧
      symmetryPermutationCoordinate
        (symmetryData.getD product.toNat #[]) coordinate =
        symmetryPermutationCoordinate right
          (symmetryPermutationCoordinate left coordinate) ∧
      symmetrySignCoordinate
        (symmetryData.getD product.toNat #[]) coordinate =
        symmetrySignCoordinate left coordinate *
          symmetrySignCoordinate right
            (symmetryPermutationCoordinate left coordinate) := by
  simp only [orbitSymmetryCompositionEntryCheck, Bool.and_eq_true,
    List.all_eq_true, List.mem_range] at hcheck
  exact orbitSymmetryCompositionCoordinateCheck_sound left right
    (symmetryData.getD product.toNat #[]) coordinate
    (hcheck.2 coordinate hcoordinate)

theorem signedMatrixOfRow_mul_apply_of_coordinate_lt
    (left right : Array Int) (i j : SymplecticIndex)
    (hsource :
      symmetryPermutationCoordinate left (certificateIndex i).val < 4) :
    (signedMatrixOfRow left * signedMatrixOfRow right) i j =
      if (certificateIndex j).val =
          symmetryPermutationCoordinate right
            (symmetryPermutationCoordinate left (certificateIndex i).val) then
        symmetrySignCoordinate left (certificateIndex i).val *
          symmetrySignCoordinate right
            (symmetryPermutationCoordinate left (certificateIndex i).val)
      else 0 := by
  classical
  let source : Fin 4 :=
    ⟨symmetryPermutationCoordinate left (certificateIndex i).val, hsource⟩
  let selected : SymplecticIndex :=
    (finSumFinEquiv : (Fin 2 ⊕ Fin 2) ≃ Fin (2 + 2)).symm source
  have hselected : certificateIndex selected = source := by
    simp [certificateIndex, selected]
  rw [Matrix.mul_apply, Finset.sum_eq_single selected]
  · simp [signedMatrixOfRow, hselected, source, mul_ite]
  · intro other _ hne
    have hcoordinate :
        (certificateIndex other).val ≠
          symmetryPermutationCoordinate left (certificateIndex i).val := by
      intro heq
      apply hne
      apply (finSumFinEquiv :
        (Fin 2 ⊕ Fin 2) ≃ Fin (2 + 2)).injective
      apply Fin.ext
      change (certificateIndex other).val = (certificateIndex selected).val
      exact heq.trans (congrArg Fin.val hselected).symm
    simp [signedMatrixOfRow, hcoordinate]
  · simp

theorem orbitSymmetryCompositionEntryCheck_matrix_sound
    (left right : Array Int) (product : Int)
    (hcheck : orbitSymmetryCompositionEntryCheck left right product = true) :
    signedMatrixOfRow (symmetryData.getD product.toNat #[]) =
      signedMatrixOfRow left * signedMatrixOfRow right := by
  ext i j
  obtain ⟨hsource, hpermutation, hsign⟩ :=
    orbitSymmetryCompositionEntryCheck_coordinate_sound
      left right product (certificateIndex i).val
      (certificateIndex i).isLt hcheck
  rw [signedMatrixOfRow_mul_apply_of_coordinate_lt left right i j hsource]
  change
    (if (certificateIndex j).val =
        symmetryPermutationCoordinate
          (symmetryData.getD product.toNat #[])
          (certificateIndex i).val then
      symmetrySignCoordinate (symmetryData.getD product.toNat #[])
        (certificateIndex i).val
    else 0) = _
  rw [hpermutation, hsign]

theorem orbitSymmetryCompositionCheck_sound
    (hcheck : orbitSymmetryCompositionCheck = true) :
    symmetryData.size = symmetryCardinality ∧
      symmetryMultiplicationData.size = symmetryData.size ∧
      ∀ left, left < symmetryData.size →
        orbitSymmetryCompositionRowCheck left = true := by
  simp only [orbitSymmetryCompositionCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at hcheck
  exact ⟨hcheck.1.1, hcheck.1.2,
    fun left hleft => hcheck.2 left (hcheck.1.2 ▸ hleft)⟩

theorem orbitSymmetryNormalizerCheck_sound
    (hcheck : orbitSymmetryNormalizerCheck = true)
    (symmetry : Nat) (hsymmetry : symmetry < symmetryData.size) :
    isSignedNormalizerRow (symmetryData.getD symmetry #[]) = true := by
  have hrow : isSignedNormalizerRow symmetryData[symmetry] = true :=
    List.all_eq_true.mp hcheck _
      (Array.getElem_mem_toList hsymmetry)
  simpa [Array.getD_eq_getD_getElem?, hsymmetry] using hrow

theorem symmetryNormalizer_mul_matrix_of_checks
    (hcomposition : orbitSymmetryCompositionCheck = true)
    (hnormalizers : orbitSymmetryNormalizerCheck = true)
    (left right : Nat)
    (hleft : left < symmetryData.size)
    (hright : right < symmetryData.size) :
    (symmetryNormalizer (symmetryMulIndex left right)).matrix =
      (symmetryNormalizer left).matrix *
        (symmetryNormalizer right).matrix := by
  have hrow := (orbitSymmetryCompositionCheck_sound hcomposition).2.2
    left hleft
  have hentry := orbitSymmetryCompositionRowCheck_sound
    left right hleft hrow hright
  have hproduct := orbitSymmetryCompositionEntryCheck_index_sound
    (symmetryData.getD left #[]) (symmetryData.getD right #[])
    (dataEntry symmetryMultiplicationData left right) hentry
  have hproductBound : symmetryMulIndex left right < symmetryData.size := by
    unfold symmetryMulIndex
    exact (Int.toNat_lt hproduct.1).2 hproduct.2
  have hleftcheck := orbitSymmetryNormalizerCheck_sound
    hnormalizers left hleft
  have hrightcheck := orbitSymmetryNormalizerCheck_sound
    hnormalizers right hright
  have hproductcheck := orbitSymmetryNormalizerCheck_sound
    hnormalizers (symmetryMulIndex left right) hproductBound
  simp only [symmetryNormalizer,
    signedNormalizerOfRow_matrix_of_check hleftcheck,
    signedNormalizerOfRow_matrix_of_check hrightcheck,
    signedNormalizerOfRow_matrix_of_check hproductcheck]
  exact orbitSymmetryCompositionEntryCheck_matrix_sound
    (symmetryData.getD left #[]) (symmetryData.getD right #[])
    (dataEntry symmetryMultiplicationData left right) hentry

theorem orbitSymmetryNormalizerCheck_valid :
    orbitSymmetryNormalizerCheck = true := by
  set_option maxRecDepth 1000000 in
    decide +kernel

theorem orbitSymmetryCompositionCheck_valid :
    orbitSymmetryCompositionCheck = true := by
  set_option maxRecDepth 1000000 in
  set_option maxHeartbeats 0 in
    decide +kernel

theorem symmetryMulIndex_lt (left right : Fin 64) :
    symmetryMulIndex left.val right.val < 64 := by
  have hsize := (orbitSymmetryCompositionCheck_sound
    orbitSymmetryCompositionCheck_valid).1
  have hleft : left.val < symmetryData.size := by
    simp [hsize, symmetryCardinality]
  have hright : right.val < symmetryData.size := by
    simp [hsize, symmetryCardinality]
  have hrow := (orbitSymmetryCompositionCheck_sound
    orbitSymmetryCompositionCheck_valid).2.2 left.val hleft
  have hentry := orbitSymmetryCompositionRowCheck_sound
    left.val right.val hleft hrow hright
  have hproduct := orbitSymmetryCompositionEntryCheck_index_sound
    (symmetryData.getD left.val #[]) (symmetryData.getD right.val #[])
    (dataEntry symmetryMultiplicationData left.val right.val) hentry
  have hbound : symmetryMulIndex left.val right.val < symmetryData.size := by
    exact (Int.toNat_lt hproduct.1).2 hproduct.2
  simpa [hsize, symmetryCardinality] using hbound

theorem symmetryNormalizer_mul_matrix (left right : Fin 64) :
    (symmetryNormalizer (symmetryMulIndex left.val right.val)).matrix =
      (symmetryNormalizer left.val).matrix *
        (symmetryNormalizer right.val).matrix := by
  apply symmetryNormalizer_mul_matrix_of_checks
    orbitSymmetryCompositionCheck_valid orbitSymmetryNormalizerCheck_valid
  · simp [(orbitSymmetryCompositionCheck_sound
      orbitSymmetryCompositionCheck_valid).1, symmetryCardinality]
  · simp [(orbitSymmetryCompositionCheck_sound
      orbitSymmetryCompositionCheck_valid).1, symmetryCardinality]

theorem orbitSymmetryMultiplicationInverseRowCheck_sound
    (symmetry : Nat)
    (hcheck : orbitSymmetryMultiplicationInverseRowCheck symmetry = true) :
    inverseSymmetry symmetry < symmetryData.size ∧
      symmetryMulIndex (inverseSymmetry symmetry) symmetry =
        symmetryIdentityIndex ∧
      symmetryMulIndex symmetry (inverseSymmetry symmetry) =
        symmetryIdentityIndex := by
  cases hrow : symmetryInverseData[symmetry]? with
  | none =>
      simp [orbitSymmetryMultiplicationInverseRowCheck, hrow] at hcheck
  | some row =>
      simp only [orbitSymmetryMultiplicationInverseRowCheck, hrow,
        Bool.and_eq_true, decide_eq_true_eq] at hcheck
      have hindex := orbitIndexCheck_sound (row.getD 0 0)
        symmetryData.size hcheck.1.1.2
      have hinverse :
          inverseSymmetry symmetry = (row.getD 0 0).toNat := by
        simp [inverseSymmetry, dataEntry,
          Array.getD_eq_getD_getElem?, hrow]
      rw [hinverse]
      exact ⟨(Int.toNat_lt hindex.1).2 hindex.2,
        hcheck.1.2, hcheck.2⟩

theorem orbitSymmetryMultiplicationInverseCheck_valid :
    orbitSymmetryMultiplicationInverseCheck = true := by
  set_option maxRecDepth 1000000 in
  set_option maxHeartbeats 0 in
    decide +kernel

theorem orbitSymmetryMultiplicationInverseCheck_sound
    (hcheck : orbitSymmetryMultiplicationInverseCheck = true) :
    symmetryInverseData.size = symmetryData.size ∧
      ∀ symmetry, symmetry < symmetryInverseData.size →
        orbitSymmetryMultiplicationInverseRowCheck symmetry = true := by
  simpa only [orbitSymmetryMultiplicationInverseCheck,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] using hcheck

theorem symmetryInverseIndex_lt (symmetry : Fin 64) :
    inverseSymmetry symmetry.val < 64 := by
  have hsize := (orbitSymmetryCompositionCheck_sound
    orbitSymmetryCompositionCheck_valid).1
  have hinverse := orbitSymmetryMultiplicationInverseCheck_sound
    orbitSymmetryMultiplicationInverseCheck_valid
  have hinverseSize : symmetryInverseData.size = symmetryData.size :=
    hinverse.1
  have hsymmetry : symmetry.val < symmetryInverseData.size := by
    simp [hinverseSize, hsize, symmetryCardinality]
  have hrow : orbitSymmetryMultiplicationInverseRowCheck symmetry.val = true :=
    hinverse.2 symmetry.val hsymmetry
  have hbound :=
    (orbitSymmetryMultiplicationInverseRowCheck_sound symmetry.val hrow).1
  simpa [hsize, symmetryCardinality] using hbound

theorem symmetryMulIndex_inverse_left (symmetry : Fin 64) :
    symmetryMulIndex (inverseSymmetry symmetry.val) symmetry.val =
      symmetryIdentityIndex := by
  have hsize := (orbitSymmetryCompositionCheck_sound
    orbitSymmetryCompositionCheck_valid).1
  have hinverse := orbitSymmetryMultiplicationInverseCheck_sound
    orbitSymmetryMultiplicationInverseCheck_valid
  have hinverseSize : symmetryInverseData.size = symmetryData.size :=
    hinverse.1
  have hsymmetry : symmetry.val < symmetryInverseData.size := by
    simp [hinverseSize, hsize, symmetryCardinality]
  have hrow := hinverse.2 symmetry.val hsymmetry
  exact
    (orbitSymmetryMultiplicationInverseRowCheck_sound symmetry.val hrow).2.1

theorem symmetryMulIndex_inverse_right (symmetry : Fin 64) :
    symmetryMulIndex symmetry.val (inverseSymmetry symmetry.val) =
      symmetryIdentityIndex := by
  have hsize := (orbitSymmetryCompositionCheck_sound
    orbitSymmetryCompositionCheck_valid).1
  have hinverse := orbitSymmetryMultiplicationInverseCheck_sound
    orbitSymmetryMultiplicationInverseCheck_valid
  have hinverseSize : symmetryInverseData.size = symmetryData.size :=
    hinverse.1
  have hsymmetry : symmetry.val < symmetryInverseData.size := by
    simp [hinverseSize, hsize, symmetryCardinality]
  have hrow := hinverse.2 symmetry.val hsymmetry
  exact
    (orbitSymmetryMultiplicationInverseRowCheck_sound symmetry.val hrow).2.2

theorem symmetryNormalizer_identity_matrix :
    (symmetryNormalizer symmetryIdentityIndex).matrix =
      (1 : Matrix SymplecticIndex SymplecticIndex Int) := by
  have hsize := (orbitSymmetryCompositionCheck_sound
    orbitSymmetryCompositionCheck_valid).1
  have hindex : symmetryIdentityIndex < symmetryData.size := by
    simp [hsize, symmetryCardinality, symmetryIdentityIndex]
  rw [symmetryNormalizer, signedNormalizerOfRow_matrix_of_check
    (orbitSymmetryNormalizerCheck_sound
      orbitSymmetryNormalizerCheck_valid symmetryIdentityIndex hindex)]
  set_option maxRecDepth 1000000 in
    decide +kernel

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

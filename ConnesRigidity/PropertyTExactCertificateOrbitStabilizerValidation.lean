


import ConnesRigidity.PropertyTExactCertificateOrbitBasisTransport
import ConnesRigidity.PropertyTExactCertificateOrbitCheckers
import ConnesRigidity.PropertyTExactCertificateOrbitStabilizerData
import Mathlib.Data.Nat.Bitwise
















namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open Matrix
open scoped BigOperators

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0


theorem card_stabilizer_eq_two_sum
    {G X : Type*} [Group G] [Fintype G] [DecidableEq X]
    [MulAction (G × Multiplicative (ZMod 2)) X] (x : X) :
    Fintype.card (MulAction.stabilizer (G × Multiplicative (ZMod 2)) x) =
      ∑ s : G,
        ((if (s, Multiplicative.ofAdd (0 : ZMod 2)) • x = x then 1 else 0) +
          (if (s, Multiplicative.ofAdd (1 : ZMod 2)) • x = x then 1 else 0)) := by
  classical
  change Fintype.card {g : G × Multiplicative (ZMod 2) // g • x = x} = _
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro symmetry _
  let equivalence : Multiplicative (ZMod 2) ≃ Fin 2 :=
    (Multiplicative.toAdd).trans (ZMod.finEquiv 2).toEquiv.symm
  calc
    (∑ parity : Multiplicative (ZMod 2),
        if (symmetry, parity) • x = x then 1 else 0) =
        ∑ parity : Fin 2,
          if (symmetry, equivalence.symm parity) • x = x then 1 else 0 :=
      Fintype.sum_equiv equivalence _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fin.sum_univ_two]
      rfl


def orbitIdentityRow : Array Int :=
  #[1, 0, 0, 0,
    0, 1, 0, 0,
    0, 0, 1, 0,
    0, 0, 0, 1,
    0, 0, 0, 0]


theorem gammaZeroOfRow_orbitIdentityRow :
    gammaZeroOfRow orbitIdentityRow = 1 := by
  have hs : isSymplecticRow orbitIdentityRow = true := by decide
  unfold gammaZeroOfRow
  simp only [hs, dite_true]
  apply CocycleExtension.ext
  · funext i
    rcases i with i | i <;> fin_cases i <;> rfl
  · apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;> rfl



theorem rawProductCheck_orbitIdentity_inverse
    {row inverse : Array Int}
    (hrow : isSymplecticRow row = true)
    (hproduct : rawProductCheck row inverse orbitIdentityRow = true) :
    isSymplecticRow inverse = true ∧
      gammaZeroOfRow inverse = (gammaZeroOfRow row)⁻¹ := by
  let group : IntegralSymplecticGroup :=
    ⟨matrixOfRow row, matrixOfRow_mem_symplectic hrow⟩
  have hright : matrixOfRow row * matrixOfRow inverse = 1 := by
    ext i j
    have hij := rawProductCheck_matrix hproduct
      (certificateIndex i) (certificateIndex j)
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      norm_num [orbitIdentityRow, matrixCoordinate, matrixOfRow,
        certificateIndex, Matrix.mul_apply,
        rawProductMatrixCoordinate, Matrix.one_apply] at hij ⊢ <;>
      simp (config := { failIfUnchanged := false })
        [Sum.inl_ne_inr, Sum.inr_ne_inl] <;>
      linear_combination -hij
  have hleft :
      (↑(group⁻¹) : Matrix SymplecticIndex SymplecticIndex Int) *
        (↑group : Matrix SymplecticIndex SymplecticIndex Int) = 1 := by
    change
      (↑(group⁻¹ * group) : Matrix SymplecticIndex SymplecticIndex Int) = 1
    rw [inv_mul_cancel]
    rfl
  have hmatrix :
      matrixOfRow inverse =
        (↑(group⁻¹) : Matrix SymplecticIndex SymplecticIndex Int) :=
    Matrix.right_inv_eq_left_inv hright hleft
  have hmember :
      matrixOfRow inverse ∈ Matrix.symplecticGroup (Fin 2) Int := by
    rw [hmatrix]
    exact (group⁻¹).property
  have hinverse : isSymplecticRow inverse = true := by
    unfold isSymplecticRow
    apply decide_eq_true_eq.mpr
    have h := (SymplecticGroup.mem_iff).mp hmember
    intro i j
    exact congrFun (congrFun h i) j
  refine ⟨hinverse, ?_⟩
  have hidentity : isSymplecticRow orbitIdentityRow = true := by decide
  have hgroup := rawProductCheck_sound hrow hinverse hidentity hproduct
  rw [gammaZeroOfRow_orbitIdentityRow] at hgroup
  exact eq_inv_of_mul_eq_one_right hgroup


def orbitCoefficientDirectStabilizerCheck
    (symmetry representative : Array Int) : Bool :=
  rawRowEq (signedRowAction symmetry representative) representative


def orbitCoefficientInverseStabilizerCheck
    (symmetry representative : Array Int) : Bool :=
  rawProductCheck (signedRowAction symmetry representative)
    representative orbitIdentityRow


theorem orbitCoefficientDirectStabilizerCheck_iff
    {symmetry representative : Array Int}
    (hsymmetry : isSignedNormalizerRow symmetry = true)
    (hrepresentative : isSymplecticRow representative = true) :
    orbitCoefficientDirectStabilizerCheck symmetry representative = true ↔
      (signedNormalizerOfRow symmetry).gammaZeroEquiv
        (gammaZeroOfRow representative) = gammaZeroOfRow representative := by
  unfold orbitCoefficientDirectStabilizerCheck
  rw [rawRowEq_iff_gammaZeroOfRow
    (isSymplecticRow_signedRowAction hsymmetry hrepresentative)
    hrepresentative, signedRowAction_sound hsymmetry hrepresentative]
  rfl


theorem orbitCoefficientInverseTransportCheck_iff
    {symmetry representative inverse : Array Int}
    (hsymmetry : isSignedNormalizerRow symmetry = true)
    (hrepresentative : isSymplecticRow representative = true)
    (hproduct : rawProductCheck representative inverse orbitIdentityRow = true) :
    signedTransportCheck symmetry representative inverse = true ↔
      (signedNormalizerOfRow symmetry).gammaZeroEquiv
        (gammaZeroOfRow representative) =
          (gammaZeroOfRow representative)⁻¹ := by
  obtain ⟨hinverse, hvalue⟩ :=
    rawProductCheck_orbitIdentity_inverse hrepresentative hproduct
  unfold signedTransportCheck
  rw [rawRowEq_iff_gammaZeroOfRow
    (isSymplecticRow_signedRowAction hsymmetry hrepresentative) hinverse,
    signedRowAction_sound hsymmetry hrepresentative, hvalue]
  rfl


def orbitCoefficientStabilizerCountAux
    (symmetries : List (Array Int)) (representative : Array Int) : Nat :=
  symmetries.foldl
    (fun total symmetry =>
      total +
        (if orbitCoefficientDirectStabilizerCheck symmetry representative then
          1 else 0) +
        (if orbitCoefficientInverseStabilizerCheck symmetry representative then
          1 else 0))
    0


def orbitCoefficientStabilizerCount (orbit : Nat) : Nat :=
  orbitCoefficientStabilizerCountAux symmetryData.toList
    (coefficientRepresentativeData.getD orbit #[])


def orbitCoefficientStabilizerRowCheck (orbit : Nat) : Bool :=
  match coefficientRepresentativeData[orbit]?,
      coefficientOrbitSizeData[orbit]? with
  | some representative, some sizeRow =>
      decide (representative.size = 20) &&
        decide (sizeRow.size = 1) &&
        decide (0 < orbitEntry sizeRow 0) &&
        decide
          (orbitEntry sizeRow 0 *
              (orbitCoefficientStabilizerCountAux symmetryData.toList
                representative : Int) =
            (2 * symmetryData.size : Nat))
  | _, _ => false


def orbitCoefficientStabilizerCheck : Bool :=
  decide
      (coefficientRepresentativeData.size = coefficientOrbitSizeData.size) &&
    (List.range coefficientRepresentativeData.size).all
      orbitCoefficientStabilizerRowCheck


theorem orbitCoefficientStabilizerRowCheck_sound
    (orbit : Nat) (representative sizeRow : Array Int)
    (hrepresentative : coefficientRepresentativeData[orbit]? =
      some representative)
    (hsize : coefficientOrbitSizeData[orbit]? = some sizeRow)
    (hcheck : orbitCoefficientStabilizerRowCheck orbit = true) :
    representative.size = 20 ∧
      sizeRow.size = 1 ∧
      0 < orbitEntry sizeRow 0 ∧
      orbitEntry sizeRow 0 *
          (orbitCoefficientStabilizerCountAux symmetryData.toList
            representative : Int) =
        (2 * symmetryData.size : Nat) := by
  simp only [orbitCoefficientStabilizerRowCheck, hrepresentative, hsize,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨hwidth, hsizeWidth⟩, hpositive⟩, hidentity⟩
  exact ⟨hwidth, hsizeWidth, hpositive, hidentity⟩


theorem orbitCoefficientStabilizerCheck_sound
    (hcheck : orbitCoefficientStabilizerCheck = true) :
    coefficientRepresentativeData.size = coefficientOrbitSizeData.size ∧
      ∀ orbit, orbit < coefficientRepresentativeData.size →
        orbitCoefficientStabilizerRowCheck orbit = true := by
  simpa only [orbitCoefficientStabilizerCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] using hcheck


def orbitGramTransposeStep (left right : Nat) (total : Nat)
    (images : Int × Int) : Nat :=
  total +
    (if images.1.toNat = left ∧ images.2.toNat = right then 1 else 0) +
    (if images.1.toNat = right ∧ images.2.toNat = left then 1 else 0)


def orbitGramTransposeRow (leftImages rightImages : Array Int)
    (row : Array Int) : Bool :=
  let left := orbitEntry row 0
  let right := orbitEntry row 1
  let size := orbitEntry row 7
  orbitIndexCheck left basisData.size &&
    orbitIndexCheck right basisData.size &&
    decide (0 < size) &&
    decide
      (size *
          (↑((leftImages.toList.zip rightImages.toList).foldl
            (orbitGramTransposeStep left.toNat right.toNat) 0) : Int) =
        (2 * symmetryData.size : Nat))


def orbitFindImageRow (target : Nat) :
    List (Array Int) → Nat → Option (Array Int × List (Array Int) × Nat)
  | [], _ => none
  | row :: rows, position =>
      if target = position then
        some (row, rows, position + 1)
      else
        orbitFindImageRow target rows (position + 1)


def orbitGramTransposeAux (transpose : List (Array Int)) :
    List (Array Int) → Nat → Array Int → List (Array Int) → Nat → Bool
  | [], _, _, _, _ => true
  | row :: rows, previousLeft, leftImages, cursor, position =>
      let left := (orbitEntry row 0).toNat
      let right := (orbitEntry row 1).toNat
      if left = previousLeft then
        match orbitFindImageRow right cursor position with
        | none => false
        | some (rightImages, remaining, next) =>
            orbitGramTransposeRow leftImages rightImages row &&
              orbitGramTransposeAux transpose rows left leftImages remaining next
      else
        let currentLeft := basisPermutationTransposeData.getD left #[]
        match orbitFindImageRow right transpose 0 with
        | none => false
        | some (rightImages, remaining, next) =>
            orbitGramTransposeRow currentLeft rightImages row &&
              orbitGramTransposeAux transpose rows left currentLeft remaining next


def orbitGramTransposeCheck : Bool :=
  let transpose := basisPermutationTransposeData.toList
  orbitGramTransposeAux transpose gramOrbitData.toList 0
    (basisPermutationTransposeData.getD 0 #[]) transpose 0


theorem orbitGramTransposeCheck_valid : orbitGramTransposeCheck = true := by
  decide +kernel


def orbitTransposeCompatibilityColumn
    (symmetry : Nat) (permutation : Array Int) : Bool :=
  decide (permutation.size = basisData.size) &&
    (permutation.toList.zip basisPermutationTransposeData.toList).all
      fun entry => decide (entry.2.getD symmetry 0 = entry.1)


def orbitTransposeCompatibilityCheck : Bool :=
  decide (basisPermutationData.size = symmetryData.size) &&
    decide (basisPermutationTransposeData.size = basisData.size) &&
    basisPermutationTransposeData.toList.all
      (fun row => decide (row.size = symmetryData.size)) &&
    basisPermutationData.toList.zipIdx.all
      (fun entry => orbitTransposeCompatibilityColumn entry.2 entry.1)


theorem orbitTransposeCompatibilityCheck_sound
    (hcheck : orbitTransposeCompatibilityCheck = true) :
    basisPermutationData.size = symmetryData.size ∧
      basisPermutationTransposeData.size = basisData.size ∧
      (∀ index (hindex : index < basisPermutationTransposeData.size),
        basisPermutationTransposeData[index].size = symmetryData.size) ∧
      (∀ symmetry (_ : symmetry < basisPermutationData.size)
          index (_ : index < basisData.size),
        (basisPermutationTransposeData.getD index #[]).getD symmetry 0 =
          (basisPermutationData.getD symmetry #[]).getD index 0) := by
  simp only [orbitTransposeCompatibilityCheck, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨hpermutationSize, htransposeSize⟩, hwidths⟩, hcolumns⟩ := hcheck
  refine ⟨hpermutationSize, htransposeSize, ?_, ?_⟩
  · intro index hindex
    have hrow := List.all_eq_true.mp hwidths
      _ (Array.getElem_mem_toList hindex)
    exact of_decide_eq_true hrow
  · intro symmetry hsymmetry index hindex
    have hzipIndex : symmetry < basisPermutationData.toList.zipIdx.length := by
      simpa using hsymmetry
    have hcolumn := List.all_eq_true.mp hcolumns
      _ (List.getElem_mem hzipIndex)
    rw [List.getElem_zipIdx, Array.getElem_toList] at hcolumn
    simp only [Nat.zero_add, orbitTransposeCompatibilityColumn,
      Bool.and_eq_true, decide_eq_true_eq] at hcolumn
    obtain ⟨hpermutationWidth, hentries⟩ := hcolumn
    have hpairIndex :
        index <
          (basisPermutationData[symmetry].toList.zip
            basisPermutationTransposeData.toList).length := by
      simp [List.length_zip, Array.length_toList,
        hpermutationWidth, htransposeSize, hindex]
    have hentry := List.all_eq_true.mp hentries
      _ (List.getElem_mem hpairIndex)
    rw [List.getElem_zip, Array.getElem_toList, Array.getElem_toList] at hentry
    have htransposeIndex : index < basisPermutationTransposeData.size := by
      simpa [htransposeSize] using hindex
    rw [← Array.getElem_eq_getD (fallback := #[]) (h := htransposeIndex),
      ← Array.getElem_eq_getD (fallback := #[]) (h := hsymmetry)]
    have hinnerIndex : index < basisPermutationData[symmetry].size := by
      simpa [hpermutationWidth] using hindex
    calc
      (basisPermutationTransposeData[index]).getD symmetry 0 =
          basisPermutationData[symmetry][index] := by
            simpa only [Prod.fst, Prod.snd] using
              of_decide_eq_true hentry
      _ = (basisPermutationData[symmetry]).getD index 0 :=
        Array.getElem_eq_getD (fallback := 0) (h := hinnerIndex)


theorem orbitTransposeCompatibilityCheck_valid :
    orbitTransposeCompatibilityCheck = true := by
  decide +kernel


def orbitNegativeSignMask : Nat → Nat
  | 0 => 43690
  | 1 => 52428
  | 2 => 61680
  | _ => 65280


def orbitPositiveSignMask (index : Nat) : Nat :=
  Nat.xor (orbitNegativeSignMask index) 65535


def orbitSameSignMask (left right : Nat) : Nat :=
  Nat.xor (Nat.xor (orbitNegativeSignMask left)
    (orbitNegativeSignMask right)) 65535


def orbitImposeSign (candidates : Nat) (source target : Int)
    (positive : Nat) : Nat :=
  if source = 0 then
    if target = 0 then candidates else 0
  else if source = target then
    Nat.land candidates positive
  else if source = -target then
    Nat.land candidates (Nat.xor positive 65535)
  else
    0


def orbitMatrixRowSignMask (candidates : Nat)
    (row target : Array Int) (index source p0 p1 p2 p3 : Nat) : Nat :=
  let candidates := orbitImposeSign candidates
    (matrixCoordinate row source p0)
    (matrixCoordinate target index 0) (orbitSameSignMask index 0)
  let candidates := orbitImposeSign candidates
    (matrixCoordinate row source p1)
    (matrixCoordinate target index 1) (orbitSameSignMask index 1)
  let candidates := orbitImposeSign candidates
    (matrixCoordinate row source p2)
    (matrixCoordinate target index 2) (orbitSameSignMask index 2)
  orbitImposeSign candidates
    (matrixCoordinate row source p3)
    (matrixCoordinate target index 3) (orbitSameSignMask index 3)


def orbitAffineCoordinateSignMask (candidates : Nat)
    (row target : Array Int) (index source p0 p1 p2 p3 : Nat) : Nat :=
  let candidates := orbitImposeSign candidates
    (vectorCoordinate row source) (vectorCoordinate target index)
    (orbitPositiveSignMask index)
  if candidates = 0 then
    0
  else
    orbitMatrixRowSignMask candidates row target index source p0 p1 p2 p3


def orbitRowSignMask (symmetry row target : Array Int) : Nat :=
  let p0 := symmetryPermutationCoordinate symmetry 0
  let p1 := symmetryPermutationCoordinate symmetry 1
  let p2 := symmetryPermutationCoordinate symmetry 2
  let p3 := symmetryPermutationCoordinate symmetry 3
  let parity := symmetrySignCoordinate symmetry 0 *
    symmetrySignCoordinate symmetry 1 *
    symmetrySignCoordinate symmetry 2 *
    symmetrySignCoordinate symmetry 3
  let candidates := if parity = 1 then 38505 else 27030
  let candidates := orbitAffineCoordinateSignMask candidates
    row target 0 p0 p0 p1 p2 p3
  let candidates := orbitAffineCoordinateSignMask candidates
    row target 1 p1 p0 p1 p2 p3
  let candidates := orbitAffineCoordinateSignMask candidates
    row target 2 p2 p0 p1 p2 p3
  orbitAffineCoordinateSignMask candidates
    row target 3 p3 p0 p1 p2 p3


def orbitPermutationRepresentatives :
    List (Array Int) → List (Array Int)
  | first :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: remaining =>
      first :: orbitPermutationRepresentatives remaining
  | _ => []


def orbitMaskCountParity (mask : Nat) (even : Bool) : Nat :=
  let codes :=
    if even then [15, 3, 5, 9, 6, 10, 12, 0]
    else [7, 11, 13, 1, 14, 2, 4, 8]
  codes.foldl
    (fun total code => total + if Nat.testBit mask code then 1 else 0)
    0


def orbitSymmetrySignCode (symmetry : Array Int) : Nat :=
  (if symmetrySignCoordinate symmetry 0 = -1 then 1 else 0) +
    (if symmetrySignCoordinate symmetry 1 = -1 then 2 else 0) +
    (if symmetrySignCoordinate symmetry 2 = -1 then 4 else 0) +
    (if symmetrySignCoordinate symmetry 3 = -1 then 8 else 0)


def orbitSymmetryParityCodes (symmetry : Array Int) : List Nat :=
  if symmetrySignCoordinate symmetry 0 *
      symmetrySignCoordinate symmetry 1 *
      symmetrySignCoordinate symmetry 2 *
      symmetrySignCoordinate symmetry 3 = 1 then
    [15, 3, 5, 9, 6, 10, 12, 0]
  else
    [7, 11, 13, 1, 14, 2, 4, 8]


def orbitSymmetryGroupMemberCheck
    (base symmetry : Array Int) (code : Nat) : Bool :=
  (List.range 4).all (fun coordinate =>
    decide
        (symmetryPermutationCoordinate symmetry coordinate =
          symmetryPermutationCoordinate base coordinate) &&
      decide
        (symmetrySignCoordinate symmetry coordinate =
          if Nat.testBit code coordinate then -1 else 1)) &&
    decide (orbitSymmetrySignCode symmetry = code)


def orbitSymmetryGroupAlignmentCheck : List (Array Int) → Bool
  | base :: one :: two :: three :: four :: five :: six :: seven :: remaining =>
      (List.zip [base, one, two, three, four, five, six, seven]
        (orbitSymmetryParityCodes base)).all
          (fun pair => orbitSymmetryGroupMemberCheck base pair.1 pair.2) &&
        orbitSymmetryGroupAlignmentCheck remaining
  | [] => true
  | _ => false


theorem orbitSymmetryGroupAlignmentCheck_valid :
    orbitSymmetryGroupAlignmentCheck symmetryData.toList = true := by
  decide +kernel


theorem orbitSymmetryGroupMemberCheck_sound
    {base symmetry : Array Int} {code : Nat}
    (h : orbitSymmetryGroupMemberCheck base symmetry code = true) :
    orbitSymmetrySignCode symmetry = code ∧
      ∀ coordinate, coordinate < 4 →
        symmetryPermutationCoordinate symmetry coordinate =
          symmetryPermutationCoordinate base coordinate ∧
        symmetrySignCoordinate symmetry coordinate =
          if Nat.testBit code coordinate then -1 else 1 := by
  simp only [orbitSymmetryGroupMemberCheck, Bool.and_eq_true,
    decide_eq_true_eq] at h
  refine ⟨h.2, ?_⟩
  intro coordinate hcoordinate
  have hentry := List.all_eq_true.mp h.1 coordinate
    (List.mem_range.mpr hcoordinate)
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using hentry


def orbitCoefficientMaskStabilizerCount
    (permutations : List (Array Int))
    (representative inverse : Array Int) : Nat :=
  permutations.foldl
    (fun total symmetry =>
      let parity := symmetrySignCoordinate symmetry 0 *
        symmetrySignCoordinate symmetry 1 *
        symmetrySignCoordinate symmetry 2 *
        symmetrySignCoordinate symmetry 3
      total +
        orbitMaskCountParity
          (orbitRowSignMask symmetry representative representative)
          (parity = 1) +
        orbitMaskCountParity
          (orbitRowSignMask symmetry representative inverse)
          (parity = 1))
    0


def orbitCoefficientMaskStabilizerRowsCheck
    (permutations : List (Array Int)) :
    List (Array Int) → List (Array Int) → List (Array Int) → Bool
  | row :: rows, inverse :: inverses, size :: sizes =>
      decide
          (orbitEntry size 0 *
            (orbitCoefficientMaskStabilizerCount
              permutations row inverse : Int) = 128) &&
        orbitCoefficientMaskStabilizerRowsCheck
          permutations rows inverses sizes
  | [], [], [] => true
  | _, _, _ => false


theorem orbitCoefficientMaskStabilizerRowsCheck_valid :
    orbitCoefficientMaskStabilizerRowsCheck
      (orbitPermutationRepresentatives symmetryData.toList)
      coefficientRepresentativeData.toList
      coefficientInverseRepresentativeData.toList
      coefficientOrbitSizeData.toList = true := by
  decide +kernel


theorem orbitNegativeSignMask_testBit
    (coordinate code : Nat) (hcoordinate : coordinate < 4)
    (hcode : code < 16) :
    Nat.testBit (orbitNegativeSignMask coordinate) code =
      Nat.testBit code coordinate := by
  interval_cases coordinate <;> interval_cases code <;> decide

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

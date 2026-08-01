
import ConnesRigidity.PropertyTExactCertificateOrbitInvariantWitness
import ConnesRigidity.PropertyTExactCertificateOrbitIncidenceValidation
import ConnesRigidity.PropertyTExactCertificateOrbitStabilizerValidation
import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientInverseValidation

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def orbitCodeSign (code coordinate : Nat) : Int :=
  if Nat.testBit code coordinate then -1 else 1

theorem orbitFullSignMask_testBit (code : Nat) (hcode : code < 16) :
    Nat.testBit 65535 code = true := by
  interval_cases code <;> decide

theorem orbitPositiveSignMask_testBit
    (coordinate code : Nat) (hcoordinate : coordinate < 4)
    (hcode : code < 16) :
    Nat.testBit (orbitPositiveSignMask coordinate) code =
      !(Nat.testBit code coordinate) := by
  simp [orbitPositiveSignMask, Nat.testBit_xor,
    orbitNegativeSignMask_testBit coordinate code hcoordinate hcode,
    orbitFullSignMask_testBit code hcode]

theorem orbitSameSignMask_testBit
    (left right code : Nat) (hleft : left < 4) (hright : right < 4)
    (hcode : code < 16) :
    Nat.testBit (orbitSameSignMask left right) code =
      (Nat.testBit code left == Nat.testBit code right) := by
  simp [orbitSameSignMask, Nat.testBit_xor,
    orbitNegativeSignMask_testBit left code hleft hcode,
    orbitNegativeSignMask_testBit right code hright hcode,
    orbitFullSignMask_testBit code hcode]
  cases Nat.testBit code left <;> cases Nat.testBit code right <;> rfl

theorem orbitImposeSign_testBit
    (candidates : Nat) (source target : Int) (positive code : Nat)
    (hcode : code < 16) :
    Nat.testBit (orbitImposeSign candidates source target positive) code =
      (Nat.testBit candidates code &&
        decide
          ((if Nat.testBit positive code then (1 : Int) else -1) * source =
            target)) := by
  by_cases hsource : source = 0
  · subst source
    by_cases htarget : target = 0
    · subst target
      simp [orbitImposeSign]
    · simp [orbitImposeSign, htarget, Ne.symm htarget]
  · by_cases hsame : source = target
    · subst target
      have hnot : -source ≠ source := by omega
      cases hpositive : Nat.testBit positive code <;>
        simp [orbitImposeSign, hsource, hnot, hpositive]
    · by_cases hopposite : source = -target
      · have htarget : target ≠ 0 := by omega
        have hnot : -target ≠ target := by omega
        cases hpositive : Nat.testBit positive code <;>
          simp [orbitImposeSign, hopposite,
            htarget, hnot,
            Nat.testBit_xor,
            orbitFullSignMask_testBit code hcode, hpositive]
      · have hnot : -source ≠ target := by omega
        cases hpositive : Nat.testBit positive code <;>
          simp [orbitImposeSign, hsource, hsame, hopposite, hnot]

def orbitMatrixSignConstraint
    (code : Nat) (row target : Array Int)
    (index source p0 p1 p2 p3 : Nat) : Bool :=
  decide (orbitCodeSign code index * orbitCodeSign code 0 *
      matrixCoordinate row source p0 = matrixCoordinate target index 0) &&
    decide (orbitCodeSign code index * orbitCodeSign code 1 *
      matrixCoordinate row source p1 = matrixCoordinate target index 1) &&
    decide (orbitCodeSign code index * orbitCodeSign code 2 *
      matrixCoordinate row source p2 = matrixCoordinate target index 2) &&
    decide (orbitCodeSign code index * orbitCodeSign code 3 *
      matrixCoordinate row source p3 = matrixCoordinate target index 3)

theorem orbitSameSignMask_sign
    (left right code : Nat) (hleft : left < 4) (hright : right < 4)
    (hcode : code < 16) :
    (if Nat.testBit (orbitSameSignMask left right) code
      then (1 : Int) else -1) =
      orbitCodeSign code left * orbitCodeSign code right := by
  rw [orbitSameSignMask_testBit left right code hleft hright hcode]
  unfold orbitCodeSign
  cases Nat.testBit code left <;> cases Nat.testBit code right <;> decide

theorem orbitPositiveSignMask_sign
    (coordinate code : Nat) (hcoordinate : coordinate < 4)
    (hcode : code < 16) :
    (if Nat.testBit (orbitPositiveSignMask coordinate) code
      then (1 : Int) else -1) = orbitCodeSign code coordinate := by
  rw [orbitPositiveSignMask_testBit coordinate code hcoordinate hcode]
  unfold orbitCodeSign
  cases Nat.testBit code coordinate <;> rfl

theorem orbitMatrixRowSignMask_testBit
    (candidates code : Nat) (row target : Array Int)
    (index source p0 p1 p2 p3 : Nat)
    (hindex : index < 4) (hcode : code < 16) :
    Nat.testBit
        (orbitMatrixRowSignMask candidates row target index source
          p0 p1 p2 p3) code =
      (Nat.testBit candidates code &&
        orbitMatrixSignConstraint code row target index source
          p0 p1 p2 p3) := by
  unfold orbitMatrixRowSignMask orbitMatrixSignConstraint
  simp only [orbitImposeSign_testBit _ _ _ _ code hcode,
    orbitSameSignMask_sign index 0 code hindex (by decide) hcode,
    orbitSameSignMask_sign index 1 code hindex (by decide) hcode,
    orbitSameSignMask_sign index 2 code hindex (by decide) hcode,
    orbitSameSignMask_sign index 3 code hindex (by decide) hcode,
    Bool.and_assoc]

theorem orbitImposeSign_zero (source target : Int) (positive : Nat) :
    orbitImposeSign 0 source target positive = 0 := by
  unfold orbitImposeSign
  split_ifs <;> simp

theorem orbitMatrixRowSignMask_zero
    (row target : Array Int) (index source p0 p1 p2 p3 : Nat) :
    orbitMatrixRowSignMask 0 row target index source
      p0 p1 p2 p3 = 0 := by
  simp [orbitMatrixRowSignMask, orbitImposeSign_zero]

theorem orbitAffineCoordinateSignMask_testBit
    (candidates code : Nat) (row target : Array Int)
    (index source p0 p1 p2 p3 : Nat)
    (hindex : index < 4) (hcode : code < 16) :
    Nat.testBit
        (orbitAffineCoordinateSignMask candidates row target index source
          p0 p1 p2 p3) code =
      (Nat.testBit candidates code &&
        decide (orbitCodeSign code index * vectorCoordinate row source =
          vectorCoordinate target index) &&
        orbitMatrixSignConstraint code row target index source
          p0 p1 p2 p3) := by
  unfold orbitAffineCoordinateSignMask
  dsimp only []
  split_ifs with hzero
  · have hbit := congrArg (fun mask => Nat.testBit mask code) hzero
    rw [orbitImposeSign_testBit _ _ _ _ code hcode,
      orbitPositiveSignMask_sign index code hindex hcode] at hbit
    simp [hbit]
  · rw [orbitMatrixRowSignMask_testBit _ code row target index source
      p0 p1 p2 p3 hindex hcode,
      orbitImposeSign_testBit _ _ _ _ code hcode,
      orbitPositiveSignMask_sign index code hindex hcode]

theorem rawRowEq_iff_affineCoordinates (left right : Array Int) :
    rawRowEq left right = true ↔
      (∀ coordinate : Fin 4,
        vectorCoordinate left coordinate.val =
          vectorCoordinate right coordinate.val) ∧
      (∀ row column : Fin 4,
        matrixCoordinate left row.val column.val =
          matrixCoordinate right row.val column.val) := by
  constructor
  · intro hequal
    constructor
    · intro coordinate
      apply rawRowEq_getD hequal
      have hbound := coordinate.isLt
      omega
    · intro row column
      apply rawRowEq_getD hequal
      have hrow := row.isLt
      have hcolumn := column.isLt
      omega
  · rintro ⟨hvector, hmatrix⟩
    unfold rawRowEq
    apply List.all_eq_true.mpr
    intro coordinate hcoordinate
    apply decide_eq_true
    have hbound : coordinate < 20 := List.mem_range.mp hcoordinate
    by_cases hlinear : coordinate < 16
    · have hrow : coordinate / 4 < 4 := by omega
      have hcolumn : coordinate % 4 < 4 := Nat.mod_lt _ (by omega)
      have hvalue := hmatrix ⟨coordinate / 4, hrow⟩
        ⟨coordinate % 4, hcolumn⟩
      have hindex : 4 * (coordinate / 4) + coordinate % 4 = coordinate := by
        omega
      simpa [matrixCoordinate, hindex] using hvalue
    · have hindex : coordinate - 16 < 4 := by omega
      have hvalue := hvector ⟨coordinate - 16, hindex⟩
      have hcoordinate' : 16 + (coordinate - 16) = coordinate := by omega
      simpa [vectorCoordinate, hcoordinate'] using hvalue

theorem signedTransportCheck_iff_affineCoordinates
    (symmetry row target : Array Int) :
    signedTransportCheck symmetry row target = true ↔
      (∀ coordinate : Fin 4,
        signedActionVectorCoordinate symmetry row coordinate.val =
          vectorCoordinate target coordinate.val) ∧
      (∀ left right : Fin 4,
        signedActionMatrixCoordinate symmetry row left.val right.val =
          matrixCoordinate target left.val right.val) := by
  unfold signedTransportCheck
  rw [rawRowEq_iff_affineCoordinates]
  simp only [signedRowAction_vectorCoordinate,
    signedRowAction_matrixCoordinate]

theorem orbitSymmetryParityCodes_mem_lt
    (symmetry : Array Int) (code : Nat)
    (hcode : code ∈ orbitSymmetryParityCodes symmetry) : code < 16 := by
  unfold orbitSymmetryParityCodes at hcode
  split at hcode <;> simp at hcode <;> omega

theorem orbitParityMask_testBit
    (symmetry : Array Int) (code : Nat)
    (hcode : code ∈ orbitSymmetryParityCodes symmetry) :
    Nat.testBit
      (if symmetrySignCoordinate symmetry 0 *
          symmetrySignCoordinate symmetry 1 *
          symmetrySignCoordinate symmetry 2 *
          symmetrySignCoordinate symmetry 3 = 1
        then 38505 else 27030) code = true := by
  have hbound := orbitSymmetryParityCodes_mem_lt symmetry code hcode
  by_cases hparity : symmetrySignCoordinate symmetry 0 *
      symmetrySignCoordinate symmetry 1 *
      symmetrySignCoordinate symmetry 2 *
      symmetrySignCoordinate symmetry 3 = 1 <;>
    interval_cases code <;>
    simp_all [orbitSymmetryParityCodes] <;>
    decide

theorem orbitRowSignMask_testBit_iff_transport
    (base symmetry row target : Array Int) (code : Nat)
    (hcode : code ∈ orbitSymmetryParityCodes base)
    (hmember : orbitSymmetryGroupMemberCheck base symmetry code = true) :
    Nat.testBit (orbitRowSignMask base row target) code = true ↔
      signedTransportCheck symmetry row target = true := by
  have hbound := orbitSymmetryParityCodes_mem_lt base code hcode
  have hcoordinates := (orbitSymmetryGroupMemberCheck_sound hmember).2
  have hsign (coordinate : Nat) (hcoordinate : coordinate < 4) :
      symmetrySignCoordinate symmetry coordinate =
        orbitCodeSign code coordinate := by
    simpa only [orbitCodeSign] using
      (hcoordinates coordinate hcoordinate).2
  have hpermutation (coordinate : Nat) (hcoordinate : coordinate < 4) :
      symmetryPermutationCoordinate symmetry coordinate =
        symmetryPermutationCoordinate base coordinate :=
    (hcoordinates coordinate hcoordinate).1
  have hvector (coordinate : Fin 4) :
      signedActionVectorCoordinate symmetry row coordinate.val =
        orbitCodeSign code coordinate.val *
          vectorCoordinate row
            (symmetryPermutationCoordinate base coordinate.val) := by
    simp only [signedActionVectorCoordinate,
      hsign coordinate.val coordinate.isLt,
      hpermutation coordinate.val coordinate.isLt]
  have hmatrix (left right : Fin 4) :
      signedActionMatrixCoordinate symmetry row left.val right.val =
        orbitCodeSign code left.val * orbitCodeSign code right.val *
          matrixCoordinate row
            (symmetryPermutationCoordinate base left.val)
            (symmetryPermutationCoordinate base right.val) := by
    simp only [signedActionMatrixCoordinate,
      hsign left.val left.isLt, hsign right.val right.isLt,
      hpermutation left.val left.isLt,
      hpermutation right.val right.isLt]
  rw [signedTransportCheck_iff_affineCoordinates]
  simp_rw [hvector, hmatrix]
  unfold orbitRowSignMask
  simp only [orbitAffineCoordinateSignMask_testBit _ code row target 0 _
      _ _ _ _ (by decide) hbound,
    orbitAffineCoordinateSignMask_testBit _ code row target 1 _
      _ _ _ _ (by decide) hbound,
    orbitAffineCoordinateSignMask_testBit _ code row target 2 _
      _ _ _ _ (by decide) hbound,
    orbitAffineCoordinateSignMask_testBit _ code row target 3 _
      _ _ _ _ (by decide) hbound,
    orbitParityMask_testBit base code hcode,
    Bool.true_and, Bool.and_eq_true, decide_eq_true_eq,
    orbitMatrixSignConstraint]
  constructor
  · intro hconstraints
    rcases hconstraints with
      ⟨⟨⟨⟨⟨⟨⟨hv0, hm0⟩, hv1⟩, hm1⟩, hv2⟩, hm2⟩, hv3⟩, hm3⟩
    rcases hm0 with ⟨⟨⟨hm00, hm01⟩, hm02⟩, hm03⟩
    rcases hm1 with ⟨⟨⟨hm10, hm11⟩, hm12⟩, hm13⟩
    rcases hm2 with ⟨⟨⟨hm20, hm21⟩, hm22⟩, hm23⟩
    rcases hm3 with ⟨⟨⟨hm30, hm31⟩, hm32⟩, hm33⟩
    constructor
    · intro coordinate
      fin_cases coordinate <;> assumption
    · intro left right
      fin_cases left <;> fin_cases right <;> assumption
  · rintro ⟨hvectorConstraints, hmatrixConstraints⟩
    exact
      ⟨⟨⟨⟨⟨⟨⟨hvectorConstraints 0,
              ⟨⟨⟨hmatrixConstraints 0 0, hmatrixConstraints 0 1⟩,
                  hmatrixConstraints 0 2⟩, hmatrixConstraints 0 3⟩⟩,
            hvectorConstraints 1⟩,
          ⟨⟨⟨hmatrixConstraints 1 0, hmatrixConstraints 1 1⟩,
              hmatrixConstraints 1 2⟩, hmatrixConstraints 1 3⟩⟩,
        hvectorConstraints 2⟩,
      ⟨⟨⟨hmatrixConstraints 2 0, hmatrixConstraints 2 1⟩,
          hmatrixConstraints 2 2⟩, hmatrixConstraints 2 3⟩⟩,
    hvectorConstraints 3⟩,
      ⟨⟨⟨hmatrixConstraints 3 0, hmatrixConstraints 3 1⟩,
          hmatrixConstraints 3 2⟩, hmatrixConstraints 3 3⟩⟩

theorem orbitIndicatorFold_eq_of_zip
    {α β : Type*} (left : List α) (right : List β)
    (leftPredicate : α → Bool) (rightPredicate : β → Bool)
    (hlength : left.length = right.length)
    (hmatch : ∀ first second, (first, second) ∈ List.zip left right →
      leftPredicate first = rightPredicate second)
    (initial : Nat) :
    left.foldl
        (fun total value => total + if leftPredicate value then 1 else 0)
        initial =
      right.foldl
        (fun total value => total + if rightPredicate value then 1 else 0)
        initial := by
  induction left generalizing right initial with
  | nil =>
      cases right <;> simp_all
  | cons first left ih =>
      cases right with
      | nil => simp at hlength
      | cons second right =>
          have hfirst : leftPredicate first = rightPredicate second :=
            hmatch first second (by simp)
          simp only [List.foldl_cons]
          rw [hfirst]
          apply ih right (by simpa using hlength)
          intro first' second' hpair
          apply hmatch
          simp [hpair]

theorem orbitMaskCountParity_eq_transportFold
    (base : Array Int) (block : List (Array Int))
    (row target : Array Int)
    (hlength : block.length = (orbitSymmetryParityCodes base).length)
    (halignment :
      (List.zip block (orbitSymmetryParityCodes base)).all
        (fun pair => orbitSymmetryGroupMemberCheck base pair.1 pair.2) =
          true) :
    orbitMaskCountParity (orbitRowSignMask base row target)
        (symmetrySignCoordinate base 0 *
          symmetrySignCoordinate base 1 *
          symmetrySignCoordinate base 2 *
          symmetrySignCoordinate base 3 = 1) =
      block.foldl
        (fun total symmetry =>
          total + if signedTransportCheck symmetry row target then 1 else 0)
        0 := by
  unfold orbitMaskCountParity
  have hcodes :
      (if (symmetrySignCoordinate base 0 *
            symmetrySignCoordinate base 1 *
            symmetrySignCoordinate base 2 *
            symmetrySignCoordinate base 3 = 1 : Bool)
        then [15, 3, 5, 9, 6, 10, 12, 0]
        else [7, 11, 13, 1, 14, 2, 4, 8]) =
        orbitSymmetryParityCodes base := by
    simp [orbitSymmetryParityCodes]
  rw [hcodes]
  symm
  apply orbitIndicatorFold_eq_of_zip
    block (orbitSymmetryParityCodes base)
    (fun symmetry => signedTransportCheck symmetry row target)
    (fun code => Nat.testBit (orbitRowSignMask base row target) code)
    hlength
  intro symmetry code hpair
  have hmember := List.all_eq_true.mp halignment
    (symmetry, code) hpair
  have hcode : code ∈ orbitSymmetryParityCodes base :=
    (List.of_mem_zip hpair).2
  have hiff := orbitRowSignMask_testBit_iff_transport
    base symmetry row target code hcode hmember
  cases hleft : Nat.testBit (orbitRowSignMask base row target) code <;>
    cases hright : signedTransportCheck symmetry row target <;>
    simp_all

theorem orbitNatFoldl_add_initial
    {α : Type*} (rows : List α) (value : α → Nat) (initial : Nat) :
    rows.foldl (fun total row => total + value row) initial =
      initial + rows.foldl (fun total row => total + value row) 0 := by
  induction rows generalizing initial with
  | nil => simp
  | cons row rows ih =>
      simp only [List.foldl_cons, Nat.zero_add]
      rw [ih (initial + value row), ih (value row)]
      omega

def orbitCoefficientTransportValue
    (row inverse symmetry : Array Int) : Nat :=
  (if signedTransportCheck symmetry row row then 1 else 0) +
    (if signedTransportCheck symmetry row inverse then 1 else 0)

def orbitCoefficientTransportStabilizerCountAux
    (symmetries : List (Array Int)) (row inverse : Array Int) : Nat :=
  symmetries.foldl
    (fun total symmetry =>
      total + orbitCoefficientTransportValue row inverse symmetry)
    0

theorem orbitCoefficientTransportStabilizerCountAux_eq_add
    (symmetries : List (Array Int)) (row inverse : Array Int) :
    orbitCoefficientTransportStabilizerCountAux symmetries row inverse =
      symmetries.foldl
          (fun total symmetry => total +
            if signedTransportCheck symmetry row row then 1 else 0) 0 +
        symmetries.foldl
          (fun total symmetry => total +
            if signedTransportCheck symmetry row inverse then 1 else 0) 0 := by
  unfold orbitCoefficientTransportStabilizerCountAux
    orbitCoefficientTransportValue
  induction symmetries with
  | nil => simp
  | cons symmetry symmetries ih =>
      simp only [List.foldl_cons]
      rw [orbitNatFoldl_add_initial symmetries
          (fun symmetry =>
            (if signedTransportCheck symmetry row row then 1 else 0) +
              (if signedTransportCheck symmetry row inverse then 1 else 0)),
        orbitNatFoldl_add_initial symmetries
          (fun symmetry =>
            if signedTransportCheck symmetry row row then 1 else 0),
        orbitNatFoldl_add_initial symmetries
          (fun symmetry =>
            if signedTransportCheck symmetry row inverse then 1 else 0)]
      omega

theorem orbitCoefficientMaskBlock_eq_transport
    (base : Array Int) (block : List (Array Int))
    (row inverse : Array Int)
    (hlength : block.length = (orbitSymmetryParityCodes base).length)
    (halignment :
      (List.zip block (orbitSymmetryParityCodes base)).all
        (fun pair => orbitSymmetryGroupMemberCheck base pair.1 pair.2) =
          true) :
    orbitMaskCountParity (orbitRowSignMask base row row)
        (symmetrySignCoordinate base 0 *
          symmetrySignCoordinate base 1 *
          symmetrySignCoordinate base 2 *
          symmetrySignCoordinate base 3 = 1) +
      orbitMaskCountParity (orbitRowSignMask base row inverse)
        (symmetrySignCoordinate base 0 *
          symmetrySignCoordinate base 1 *
          symmetrySignCoordinate base 2 *
          symmetrySignCoordinate base 3 = 1) =
      orbitCoefficientTransportStabilizerCountAux block row inverse := by
  rw [orbitMaskCountParity_eq_transportFold
    base block row row hlength halignment,
    orbitMaskCountParity_eq_transportFold
      base block row inverse hlength halignment,
    orbitCoefficientTransportStabilizerCountAux_eq_add]

theorem orbitCoefficientMaskStabilizerCount_eq_transport
    (symmetries : List (Array Int)) (row inverse : Array Int)
    (halignment : orbitSymmetryGroupAlignmentCheck symmetries = true) :
    orbitCoefficientMaskStabilizerCount
        (orbitPermutationRepresentatives symmetries) row inverse =
      orbitCoefficientTransportStabilizerCountAux symmetries row inverse := by
  induction hlength : symmetries.length using Nat.strong_induction_on
      generalizing symmetries with
  | h length ih =>
      cases symmetries with
      | nil =>
          simp [orbitCoefficientMaskStabilizerCount,
            orbitPermutationRepresentatives,
            orbitCoefficientTransportStabilizerCountAux]
      | cons base remaining =>
          cases remaining with
          | nil => simp [orbitSymmetryGroupAlignmentCheck] at halignment
          | cons one remaining =>
              cases remaining with
              | nil => simp [orbitSymmetryGroupAlignmentCheck] at halignment
              | cons two remaining =>
                  cases remaining with
                  | nil => simp [orbitSymmetryGroupAlignmentCheck] at halignment
                  | cons three remaining =>
                      cases remaining with
                      | nil => simp [orbitSymmetryGroupAlignmentCheck] at halignment
                      | cons four remaining =>
                          cases remaining with
                          | nil => simp [orbitSymmetryGroupAlignmentCheck] at halignment
                          | cons five remaining =>
                              cases remaining with
                              | nil => simp [orbitSymmetryGroupAlignmentCheck] at halignment
                              | cons six remaining =>
                                  cases remaining with
                                  | nil => simp [orbitSymmetryGroupAlignmentCheck]
                                      at halignment
                                  | cons seven remaining =>
                                      have hparts :
                                          (List.zip
                                            [base, one, two, three,
                                              four, five, six, seven]
                                            (orbitSymmetryParityCodes base)).all
                                              (fun pair =>
                                                orbitSymmetryGroupMemberCheck
                                                  base pair.1 pair.2) = true ∧
                                            orbitSymmetryGroupAlignmentCheck
                                              remaining = true := by
                                        simpa [orbitSymmetryGroupAlignmentCheck,
                                          Bool.and_eq_true] using halignment
                                      have hcodeLength :
                                          [base, one, two, three,
                                            four, five, six, seven].length =
                                              (orbitSymmetryParityCodes
                                                base).length := by
                                        unfold orbitSymmetryParityCodes
                                        split <;> simp
                                      have hblock :=
                                        orbitCoefficientMaskBlock_eq_transport
                                          base [base, one, two, three,
                                            four, five, six, seven]
                                          row inverse hcodeLength hparts.1
                                      have hremaining := ih remaining.length
                                        (by
                                          have hshorter := hlength
                                          simp only [List.length_cons] at hshorter
                                          omega)
                                        remaining hparts.2 rfl
                                      unfold orbitCoefficientMaskStabilizerCount
                                        at hremaining ⊢
                                      unfold orbitPermutationRepresentatives
                                      simp only [List.foldl_cons]
                                      simp only [Nat.add_assoc] at hremaining ⊢
                                      rw [orbitNatFoldl_add_initial
                                        (orbitPermutationRepresentatives
                                          remaining)
                                        (fun symmetry =>
                                          let parity :=
                                            symmetrySignCoordinate symmetry 0 *
                                              symmetrySignCoordinate symmetry 1 *
                                              symmetrySignCoordinate symmetry 2 *
                                              symmetrySignCoordinate symmetry 3
                                          orbitMaskCountParity
                                              (orbitRowSignMask symmetry row row)
                                              (parity = 1) +
                                            orbitMaskCountParity
                                              (orbitRowSignMask symmetry row inverse)
                                              (parity = 1))]
                                      change
                                        _ + _ =
                                          orbitCoefficientTransportStabilizerCountAux
                                            ([base, one, two, three,
                                              four, five, six, seven] ++ remaining)
                                            row inverse
                                      unfold orbitCoefficientTransportStabilizerCountAux
                                      rw [List.foldl_append,
                                        orbitNatFoldl_add_initial remaining
                                          (orbitCoefficientTransportValue row inverse)]
                                      simp only [Nat.zero_add]
                                      rw [hremaining, hblock]
                                      rfl

theorem orbitCoefficientInverseRowsCheck_get
    (rows inverses : List (Array Int)) (index : Nat)
    (hindex : index < rows.length)
    (hlength : rows.length = inverses.length)
    (hcheck : orbitCoefficientInverseRowsCheck rows inverses = true) :
    isSymplecticRow rows[index] = true ∧
      rawProductCheck rows[index] inverses[index] orbitIdentityRow = true := by
  induction rows generalizing inverses index with
  | nil => simp at hindex
  | cons row rows ih =>
      cases inverses with
      | nil => simp at hlength
      | cons inverse inverses =>
          simp only [orbitCoefficientInverseRowsCheck,
            Bool.and_eq_true] at hcheck
          cases index with
          | zero =>
              exact ⟨hcheck.1.1, hcheck.1.2⟩
          | succ index =>
              apply ih inverses index (by simpa using hindex)
                (by simpa using hlength) hcheck.2

theorem orbitCoefficientMaskStabilizerRowsCheck_lengths
    (permutations : List (Array Int))
    (rows inverses sizes : List (Array Int))
    (hcheck : orbitCoefficientMaskStabilizerRowsCheck
      permutations rows inverses sizes = true) :
    rows.length = inverses.length ∧ rows.length = sizes.length := by
  induction rows generalizing inverses sizes with
  | nil =>
      cases inverses <;> cases sizes <;>
        simp_all [orbitCoefficientMaskStabilizerRowsCheck]
  | cons row rows ih =>
      cases inverses with
      | nil => simp [orbitCoefficientMaskStabilizerRowsCheck] at hcheck
      | cons inverse inverses =>
          cases sizes with
          | nil => simp [orbitCoefficientMaskStabilizerRowsCheck] at hcheck
          | cons size sizes =>
              simp only [orbitCoefficientMaskStabilizerRowsCheck,
                Bool.and_eq_true] at hcheck
              have htail := ih inverses sizes hcheck.2
              exact ⟨by simpa using htail.1, by simpa using htail.2⟩

theorem orbitCoefficientMaskStabilizerRowsCheck_get
    (permutations : List (Array Int))
    (rows inverses sizes : List (Array Int)) (index : Nat)
    (hindex : index < rows.length)
    (hcheck : orbitCoefficientMaskStabilizerRowsCheck
      permutations rows inverses sizes = true) :
    ∃ (hinverse : index < inverses.length) (hsize : index < sizes.length),
      orbitEntry sizes[index] 0 *
        (orbitCoefficientMaskStabilizerCount
          permutations rows[index] inverses[index] : Int) = 128 := by
  induction rows generalizing inverses sizes index with
  | nil => simp at hindex
  | cons row rows ih =>
      cases inverses with
      | nil => simp [orbitCoefficientMaskStabilizerRowsCheck] at hcheck
      | cons inverse inverses =>
          cases sizes with
          | nil => simp [orbitCoefficientMaskStabilizerRowsCheck] at hcheck
          | cons size sizes =>
              simp only [orbitCoefficientMaskStabilizerRowsCheck,
                Bool.and_eq_true, decide_eq_true_eq] at hcheck
              cases index with
              | zero =>
                  exact ⟨by simp, by simp, hcheck.1⟩
              | succ index =>
                  obtain ⟨hinverse, hsize, hentry⟩ :=
                    ih inverses sizes index (by simpa using hindex) hcheck.2
                  exact ⟨by simpa using hinverse,
                    by simpa using hsize, hentry⟩

theorem symmetryData_toList_eq_range_map :
    symmetryData.toList =
      (List.range 64).map (fun index => symmetryData.getD index #[]) := by
  have hsize : symmetryData.size = 64 := by
    simpa [symmetryCardinality] using
      (orbitSymmetryCompositionCheck_sound
        orbitSymmetryCompositionCheck_valid).1
  apply List.ext_getElem
  · simp [hsize]
  · intro index hleft hright
    simp only [Array.getElem_toList, List.getElem_map,
      List.getElem_range]
    exact Array.getElem_eq_getD #[]

noncomputable instance signedGroupStabilizerFintype
    (element : constructedGammaZeroGroup) :
    Fintype (MulAction.stabilizer OrbitSignedSymmetry element) :=
  Fintype.ofFinite _

theorem orbitCoefficientTransportStabilizerCountAux_eq_card
    (row inverse : Array Int)
    (hrow : isSymplecticRow row = true)
    (hinverse : rawProductCheck row inverse orbitIdentityRow = true) :
    orbitCoefficientTransportStabilizerCountAux
        symmetryData.toList row inverse =
      Fintype.card
        (MulAction.stabilizer OrbitSignedSymmetry (gammaZeroOfRow row)) := by
  classical
  have hcard :
      Fintype.card
          (MulAction.stabilizer OrbitSignedSymmetry (gammaZeroOfRow row)) =
        ∑ symmetry : OrbitSymmetry,
          ((if (symmetry, Multiplicative.ofAdd (0 : ZMod 2)) •
                gammaZeroOfRow row = gammaZeroOfRow row then 1 else 0) +
            (if (symmetry, Multiplicative.ofAdd (1 : ZMod 2)) •
                gammaZeroOfRow row = gammaZeroOfRow row then 1 else 0)) := by
    simpa only [← Nat.card_eq_fintype_card] using
      (card_stabilizer_eq_two_sum (gammaZeroOfRow row))
  rw [hcard]
  have hvalue (symmetry : OrbitSymmetry) :
      orbitCoefficientTransportValue row inverse
          (symmetryData.getD symmetry.index.val #[]) =
        (if (symmetry, Multiplicative.ofAdd (0 : ZMod 2)) •
              gammaZeroOfRow row = gammaZeroOfRow row then 1 else 0) +
          (if (symmetry, Multiplicative.ofAdd (1 : ZMod 2)) •
              gammaZeroOfRow row = gammaZeroOfRow row then 1 else 0) := by
    have hnormalizer := symmetryNormalizerRowChecks symmetry.index
    have hdirect :
        signedTransportCheck
            (symmetryData.getD symmetry.index.val #[]) row row = true ↔
          (symmetry, Multiplicative.ofAdd (0 : ZMod 2)) •
            gammaZeroOfRow row = gammaZeroOfRow row := by
      change
        orbitCoefficientDirectStabilizerCheck
            (symmetryData.getD symmetry.index.val #[]) row = true ↔ _
      rw [orbitCoefficientDirectStabilizerCheck_iff hnormalizer hrow]
      rfl
    have hinverse' :
        signedTransportCheck
            (symmetryData.getD symmetry.index.val #[]) row inverse = true ↔
          (symmetry, Multiplicative.ofAdd (1 : ZMod 2)) •
            gammaZeroOfRow row = gammaZeroOfRow row := by
      rw [orbitCoefficientInverseTransportCheck_iff
        hnormalizer hrow hinverse]
      change _ ↔ (orbitSymmetry symmetry.index (gammaZeroOfRow row))⁻¹ = _
      exact inv_eq_iff_eq_inv.symm
    have hindicator (condition : Bool) (proposition : Prop)
        [Decidable proposition]
        (hequivalence : condition = true ↔ proposition) :
        (if condition then (1 : Nat) else 0) =
          if proposition then 1 else 0 := by
      cases hcondition : condition with
      | false =>
          have hfalse : ¬ proposition := by
            intro hproposition
            have htrue := hequivalence.mpr hproposition
            simp [hcondition] at htrue
          simp [hfalse]
      | true =>
          have htrue : proposition := hequivalence.mp hcondition
          simp [htrue]
    unfold orbitCoefficientTransportValue
    rw [hindicator _ _ hdirect, hindicator _ _ hinverse']
  unfold orbitCoefficientTransportStabilizerCountAux
  rw [symmetryData_toList_eq_range_map, List.foldl_map]
  rw [← orbitSymmetry_sum_eq_range_foldl
    (fun index => orbitCoefficientTransportValue row inverse
      (symmetryData.getD index #[]))]
  exact Finset.sum_congr rfl (fun symmetry _ => hvalue symmetry)

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

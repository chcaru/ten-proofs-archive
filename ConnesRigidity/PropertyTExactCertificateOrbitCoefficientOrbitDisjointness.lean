


import ConnesRigidity.PropertyTExactCertificateOrbitInvariantWitness
import ConnesRigidity.PropertyTExactCertificateOrbitBasisTransport
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalData
import ConnesRigidity.PropertyTExactCertificateOrbitTargetRadix















namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000



def gammaZeroCoordinate (element : constructedGammaZeroGroup)
    (index : Fin 20) : Int :=
  if hmatrix : index.val < 16 then
    let row : Fin 4 := ⟨index.val / 4, by omega⟩
    let column : Fin 4 := ⟨index.val % 4, by omega⟩
    (element.snd : Matrix SymplecticIndex SymplecticIndex Int)
      (coordinateIndex row) (coordinateIndex column)
  else
    let coordinate : Fin 4 := ⟨index.val - 16, by omega⟩
    element.fst (coordinateIndex coordinate)



def gammaZeroCoordinates (element : constructedGammaZeroGroup) : List Int :=
  List.ofFn (gammaZeroCoordinate element)

@[simp] theorem gammaZeroCoordinates_length
    (element : constructedGammaZeroGroup) :
    (gammaZeroCoordinates element).length = 20 := by
  simp [gammaZeroCoordinates]



theorem gammaZeroCoordinates_gammaZeroOfRow
    {row : Array Int} (hrow : isSymplecticRow row = true)
    (hwidth : row.size = 20) :
    gammaZeroCoordinates (gammaZeroOfRow row) = row.toList := by
  apply List.ext_getElem
  · simp [gammaZeroCoordinates, hwidth]
  · intro index hleft hright
    have hindex : index < 20 := by
      simpa [gammaZeroCoordinates] using hleft
    have hrowIndex : index < row.size := by simpa using hright
    simp only [gammaZeroCoordinates, List.getElem_ofFn]
    change gammaZeroCoordinate (gammaZeroOfRow row) ⟨index, hindex⟩ =
      (row.toList)[index]
    unfold gammaZeroCoordinate
    split
    next hmatrix =>
      rw [gammaZeroOfRow_snd_of_symplectic hrow]
      simp only [matrixOfRow, certificateIndex_coordinateIndex]
      change row.getD (4 * (index / 4) + index % 4) 0 =
        (row.toList)[index]
      have hdivision : 4 * (index / 4) + index % 4 = index := by omega
      rw [hdivision]
      simp [getElem?_pos row index hrowIndex]
    next hmatrix =>
      change ¬ index < 16 at hmatrix
      rw [gammaZeroOfRow_fst_of_symplectic hrow]
      simp only [vectorOfRow, vectorCoordinate,
        certificateIndex_coordinateIndex]
      have hcoordinate : 16 + (index - 16) = index := by omega
      rw [hcoordinate]
      simp [getElem?_pos row index hrowIndex]



def gammaZeroCoordinateCode (element : constructedGammaZeroGroup) : Int :=
  targetCoordinateCode (gammaZeroCoordinates element)



theorem gammaZeroCoordinateCode_gammaZeroOfRow
    {row : Array Int} (hrow : isSymplecticRow row = true)
    (hwidth : row.size = 20) :
    gammaZeroCoordinateCode (gammaZeroOfRow row) =
      targetCoordinateCode row.toList := by
  simp [gammaZeroCoordinateCode,
    gammaZeroCoordinates_gammaZeroOfRow hrow hwidth]



def coefficientOrbitCodes (element : constructedGammaZeroGroup) :
    Finset Int :=
  Finset.univ.image fun symmetry : OrbitSignedSymmetry =>
    gammaZeroCoordinateCode (symmetry • element)


theorem coefficientOrbitCodes_nonempty
    (element : constructedGammaZeroGroup) :
    (coefficientOrbitCodes element).Nonempty := by
  refine ⟨gammaZeroCoordinateCode element, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨1, Finset.mem_univ _, by rw [one_smul]⟩



def coefficientCanonicalCode (element : constructedGammaZeroGroup) : Int :=
  (coefficientOrbitCodes element).min'
    (coefficientOrbitCodes_nonempty element)



theorem coefficientOrbitCodes_smul
    (symmetry : OrbitSignedSymmetry)
    (element : constructedGammaZeroGroup) :
    coefficientOrbitCodes (symmetry • element) =
      coefficientOrbitCodes element := by
  classical
  ext code
  simp only [coefficientOrbitCodes, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨other, hother⟩
    refine ⟨other * symmetry, ?_⟩
    rw [mul_smul]
    exact hother
  · rintro ⟨other, hother⟩
    refine ⟨other * symmetry⁻¹, ?_⟩
    rw [mul_smul, inv_smul_smul]
    exact hother


theorem coefficientCanonicalCode_smul
    (symmetry : OrbitSignedSymmetry)
    (element : constructedGammaZeroGroup) :
    coefficientCanonicalCode (symmetry • element) =
      coefficientCanonicalCode element := by
  unfold coefficientCanonicalCode
  simp only [coefficientOrbitCodes_smul]



theorem coefficientCanonicalCode_eq_of_minimum
    (element : constructedGammaZeroGroup) (candidate : Int)
    (hmember : ∃ symmetry : OrbitSignedSymmetry,
      gammaZeroCoordinateCode (symmetry • element) = candidate)
    (hminimum : ∀ symmetry : OrbitSignedSymmetry,
      candidate ≤ gammaZeroCoordinateCode (symmetry • element)) :
    coefficientCanonicalCode element = candidate := by
  have hcandidate : candidate ∈ coefficientOrbitCodes element := by
    obtain ⟨symmetry, hsymmetry⟩ := hmember
    exact Finset.mem_image.mpr ⟨symmetry, Finset.mem_univ _, hsymmetry⟩
  apply le_antisymm
  · exact Finset.min'_le _ _ hcandidate
  · apply Finset.le_min'
    intro code hcode
    obtain ⟨symmetry, _, rfl⟩ := Finset.mem_image.mp hcode
    exact hminimum symmetry




def gammaZeroDescendingCoordinates
    (element : constructedGammaZeroGroup) : List Int :=
  (gammaZeroCoordinates element).reverse




def coefficientOrbitDescendingCoordinates
    (element : constructedGammaZeroGroup) : Finset (List Int) :=
  Finset.univ.image fun symmetry : OrbitSignedSymmetry =>
    gammaZeroDescendingCoordinates (symmetry • element)



theorem coefficientOrbitDescendingCoordinates_nonempty
    (element : constructedGammaZeroGroup) :
    (coefficientOrbitDescendingCoordinates element).Nonempty := by
  refine ⟨gammaZeroDescendingCoordinates element, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨1, Finset.mem_univ _, by rw [one_smul]⟩


def coefficientCanonicalCoordinates
    (element : constructedGammaZeroGroup) : List Int :=
  (coefficientOrbitDescendingCoordinates element).min'
    (coefficientOrbitDescendingCoordinates_nonempty element)


theorem coefficientOrbitDescendingCoordinates_smul
    (symmetry : OrbitSignedSymmetry)
    (element : constructedGammaZeroGroup) :
    coefficientOrbitDescendingCoordinates (symmetry • element) =
      coefficientOrbitDescendingCoordinates element := by
  classical
  ext coordinates
  simp only [coefficientOrbitDescendingCoordinates,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨other, hother⟩
    refine ⟨other * symmetry, ?_⟩
    rw [mul_smul]
    exact hother
  · rintro ⟨other, hother⟩
    refine ⟨other * symmetry⁻¹, ?_⟩
    rw [mul_smul, inv_smul_smul]
    exact hother



theorem coefficientCanonicalCoordinates_smul
    (symmetry : OrbitSignedSymmetry)
    (element : constructedGammaZeroGroup) :
    coefficientCanonicalCoordinates (symmetry • element) =
      coefficientCanonicalCoordinates element := by
  unfold coefficientCanonicalCoordinates
  simp only [coefficientOrbitDescendingCoordinates_smul]


theorem coefficientCanonicalCoordinates_eq_of_minimum
    (element : constructedGammaZeroGroup) (candidate : List Int)
    (hmember : ∃ symmetry : OrbitSignedSymmetry,
      gammaZeroDescendingCoordinates (symmetry • element) = candidate)
    (hminimum : ∀ symmetry : OrbitSignedSymmetry,
      candidate ≤ gammaZeroDescendingCoordinates (symmetry • element)) :
    coefficientCanonicalCoordinates element = candidate := by
  have hcandidate : candidate ∈
      coefficientOrbitDescendingCoordinates element := by
    obtain ⟨symmetry, hsymmetry⟩ := hmember
    exact Finset.mem_image.mpr ⟨symmetry, Finset.mem_univ _, hsymmetry⟩
  apply le_antisymm
  · exact Finset.min'_le _ _ hcandidate
  · apply Finset.le_min'
    intro coordinates hcoordinates
    obtain ⟨symmetry, _, rfl⟩ := Finset.mem_image.mp hcoordinates
    exact hminimum symmetry




def signedAffineCoordinate
    (symmetry row : Array Int) (index : Nat) : Int :=
  if index < 16 then
    signedActionMatrixCoordinate symmetry row (index / 4) (index % 4)
  else
    signedActionVectorCoordinate symmetry row (index - 16)


def signedAffineDescendingCoordinates
    (symmetry row : Array Int) : List Int :=
  (List.range 20).reverse.map (signedAffineCoordinate symmetry row)


theorem signedAffineDescendingCoordinates_eq
    (symmetry row : Array Int) :
    signedAffineDescendingCoordinates symmetry row =
      (signedRowAction symmetry row).toList.reverse := by
  unfold signedAffineDescendingCoordinates
  rw [List.map_reverse]
  have hforward :
      (List.range 20).map (signedAffineCoordinate symmetry row) =
        (signedRowAction symmetry row).toList := by
    apply List.ext_getElem
    · simp [signedRowAction]
    · intro index hleft hright
      have hindex : index < 20 := by simpa using hleft
      simp only [List.getElem_map, List.getElem_range]
      rw [Array.getElem_toList]
      simp [signedRowAction, signedAffineCoordinate]
  exact congrArg List.reverse hforward



def coefficientCanonicalImagesCheck
    (canonical representative inverse : Array Int)
    (symmetries : List (Array Int)) : Bool :=
  let descending := canonical.toList.reverse
  symmetries.all fun symmetry =>
    decide (descending ≤
      signedAffineDescendingCoordinates symmetry representative) &&
      decide (descending ≤
        signedAffineDescendingCoordinates symmetry inverse)


def coefficientCanonicalWitnessRowCheck
    (orbit : Nat) (symmetries : List (Array Int))
    (witness : List Int) (representative inverse : Array Int) : Bool :=
  let index := witness.getD 2 0
  let inversion := witness.getD 3 0
  let source := if inversion = 0 then representative else inverse
  let symmetry := symmetryData.getD index.toNat #[]
  let canonical := signedRowAction symmetry source
  decide (witness.length = 4) &&
    decide (witness.getD 0 0 = (orbit : Int)) &&
    decide (0 ≤ index ∧ index < (64 : Int)) &&
    decide (inversion = 0 ∨ inversion = 1) &&
    decide (representative.size = 20) &&
    decide (inverse.size = 20) &&
    decide
      (targetCoordinateCode canonical.toList = witness.getD 1 0) &&
    coefficientCanonicalImagesCheck canonical representative inverse
      symmetries



def coefficientCanonicalWitnessRowsCheck
    (symmetries : List (Array Int)) :
    Nat → List (List Int) → List (Array Int) → List (Array Int) → Bool
  | _, [], [], [] => true
  | orbit, witness :: witnesses, representative :: representatives,
      inverse :: inverses =>
      coefficientCanonicalWitnessRowCheck orbit symmetries witness
        representative inverse &&
        coefficientCanonicalWitnessRowsCheck symmetries
          (orbit + 1) witnesses representatives inverses
  | _, _, _, _ => false


theorem coefficientCanonicalWitnessRowsCheck_get
    (symmetries : List (Array Int))
    (witnesses : List (List Int))
    (representatives inverses : List (Array Int))
    (start index : Nat)
    (hwitness : index < witnesses.length)
    (hrepresentative : witnesses.length = representatives.length)
    (hinverse : witnesses.length = inverses.length)
    (hcheck : coefficientCanonicalWitnessRowsCheck symmetries start
      witnesses representatives inverses = true) :
    coefficientCanonicalWitnessRowCheck (start + index) symmetries
      witnesses[index] representatives[index] inverses[index] = true := by
  induction witnesses generalizing representatives inverses start index with
  | nil => simp at hwitness
  | cons witness witnesses ih =>
      cases representatives with
      | nil => simp at hrepresentative
      | cons representative representatives =>
        cases inverses with
        | nil => simp at hinverse
        | cons inverse inverses =>
          simp only [coefficientCanonicalWitnessRowsCheck,
            Bool.and_eq_true] at hcheck
          cases index with
          | zero => simpa using hcheck.1
          | succ index =>
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              ih representatives inverses (start + 1) index
                (by simpa using hwitness)
                (by simpa using hrepresentative)
                (by simpa using hinverse) hcheck.2

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

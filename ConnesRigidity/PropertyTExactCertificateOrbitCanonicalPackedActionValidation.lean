
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedAction
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedData

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000

def canonicalPackedActionDescriptorCheck
    (symmetry : Array Int) (packed coordinate : Nat) : Bool :=
  decide (canonicalPackedActionSource packed coordinate < 20) &&
    decide (canonicalPackedActionSource packed coordinate =
      canonicalPackedActionExpectedSource symmetry coordinate) &&
    decide (canonicalPackedActionSign packed coordinate =
      canonicalPackedActionExpectedSign symmetry coordinate)

def canonicalPackedActionRecordCheck
    (position : Nat) (record : List Int) : Bool :=
  let index := record.getD 0 (-1)
  let packed := record.getD 1 0
  let symmetry := symmetryData.getD position #[]
  decide (record.length = 2) &&
    decide (index = (position : Int)) &&
    decide (0 ≤ packed) &&
    (List.range 20).all fun coordinate =>
      canonicalPackedActionDescriptorCheck symmetry packed.toNat coordinate

def canonicalPackedActionRowsCheck : Nat → List (List Int) → Bool
  | _, [] => true
  | position, record :: records =>
      canonicalPackedActionRecordCheck position record &&
        canonicalPackedActionRowsCheck (position + 1) records

theorem canonicalPackedActionData_length :
    canonicalPackedActionData.length = 64 := by
  unfold canonicalPackedActionData
  decide +kernel

set_option maxHeartbeats 0 in

theorem canonicalPackedActionRowsCheck_valid :
    canonicalPackedActionRowsCheck 0 canonicalPackedActionData = true := by
  unfold canonicalPackedActionRowsCheck canonicalPackedActionRecordCheck
    canonicalPackedActionDescriptorCheck canonicalPackedActionSource
    canonicalPackedActionSign canonicalPackedActionDigit
    canonicalPackedActionExpectedSource canonicalPackedActionExpectedSign
    symmetryPermutationCoordinate symmetrySignCoordinate
    canonicalPackedActionData symmetryData
  decide +kernel

theorem canonicalPackedActionRowsCheck_get
    (records : List (List Int)) (start index : Nat)
    (hindex : index < records.length)
    (hcheck : canonicalPackedActionRowsCheck start records = true) :
    canonicalPackedActionRecordCheck (start + index)
      (records.getD index []) = true := by
  induction records generalizing start index with
  | nil => simp at hindex
  | cons record records ih =>
      simp only [canonicalPackedActionRowsCheck, Bool.and_eq_true] at hcheck
      cases index with
      | zero => simpa using hcheck.1
      | succ index =>
          have hindex' : index < records.length := by simpa using hindex
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (start + 1) index hindex' hcheck.2

noncomputable def canonicalPackedActionCode (symmetry : Nat) : Nat :=
  ((canonicalPackedActionData.getD symmetry []).getD 1 0).toNat

theorem canonicalPackedActionRecord_sound
    (symmetry : Fin 64) (coordinate : Fin 20) :
    canonicalPackedActionSource
        (canonicalPackedActionCode symmetry.val) coordinate.val < 20 ∧
      canonicalPackedActionSource
          (canonicalPackedActionCode symmetry.val) coordinate.val =
        canonicalPackedActionExpectedSource
          (symmetryData.getD symmetry.val #[]) coordinate.val ∧
      canonicalPackedActionSign
          (canonicalPackedActionCode symmetry.val) coordinate.val =
        canonicalPackedActionExpectedSign
          (symmetryData.getD symmetry.val #[]) coordinate.val := by
  have hindex : symmetry.val < canonicalPackedActionData.length := by
    rw [canonicalPackedActionData_length]
    exact symmetry.isLt
  have hrecord := canonicalPackedActionRowsCheck_get
    canonicalPackedActionData 0 symmetry.val hindex
      canonicalPackedActionRowsCheck_valid
  simp only [canonicalPackedActionRecordCheck, Bool.and_eq_true,
    decide_eq_true_eq, Nat.zero_add] at hrecord
  have hcoordinate := List.all_eq_true.mp hrecord.2
    coordinate.val (List.mem_range.mpr coordinate.isLt)
  simpa only [canonicalPackedActionDescriptorCheck, Bool.and_eq_true,
    decide_eq_true_eq, canonicalPackedActionCode, and_assoc] using
      hcoordinate

theorem canonicalPackedActionArrayCoordinate_sound
    (symmetry : Fin 64) (row : Array Int) (coordinate : Fin 20) :
    canonicalPackedActionArrayCoordinate
        (canonicalPackedActionCode symmetry.val) row coordinate.val =
      signedAffineCoordinate
        (symmetryData.getD symmetry.val #[]) row coordinate.val := by
  obtain ⟨_, hsource, hsign⟩ :=
    canonicalPackedActionRecord_sound symmetry coordinate
  exact canonicalPackedActionArrayCoordinate_eq_signedAffineCoordinate
    (canonicalPackedActionCode symmetry.val)
    (symmetryData.getD symmetry.val #[]) row coordinate.val hsource hsign

end

end ConnesRigidity.AffineSymplecticOrbitCertificate




import ConnesRigidity.PropertyTExactCertificateOrbitData
import Mathlib.Data.Nat.Bits









namespace ConnesRigidity.AffineSymplecticOrbitCertificate


def canonicalPackedCoordinateDigit (coordinate : Int) : Nat :=
  (coordinate + 8).toNat


def canonicalPackedRowList : List Int → Nat
  | [] => 0
  | coordinate :: remaining =>
      canonicalPackedCoordinateDigit coordinate +
        16 * canonicalPackedRowList remaining


def canonicalPackedRow (row : Array Int) : Nat :=
  canonicalPackedRowList row.toList


def canonicalPackedCoordinate (packed index : Nat) : Int :=
  (((packed >>> (4 * index)) % 16 : Nat) : Int) - 8


theorem canonicalPackedCoordinateDigit_lt
    (coordinate : Int) (hlower : -8 ≤ coordinate)
    (hupper : coordinate < 8) :
    canonicalPackedCoordinateDigit coordinate < 16 := by
  unfold canonicalPackedCoordinateDigit
  apply (Int.toNat_lt (by omega : 0 ≤ coordinate + 8)).mpr
  omega


theorem canonicalPackedRowList_shiftRight_four
    (coordinate : Int) (remaining : List Int)
    (hlower : -8 ≤ coordinate) (hupper : coordinate < 8) :
    canonicalPackedRowList (coordinate :: remaining) >>> 4 =
      canonicalPackedRowList remaining := by
  rw [Nat.shiftRight_eq_div_pow]
  change
    (canonicalPackedCoordinateDigit coordinate +
      16 * canonicalPackedRowList remaining) / 16 =
        canonicalPackedRowList remaining
  have hdigit := canonicalPackedCoordinateDigit_lt
    coordinate hlower hupper
  omega


theorem canonicalPackedCoordinateList_get
    (rows : List Int) (index : Nat) (hindex : index < rows.length)
    (hrange : ∀ coordinate ∈ rows,
      -8 ≤ coordinate ∧ coordinate < 8) :
    canonicalPackedCoordinate (canonicalPackedRowList rows) index =
      rows[index] := by
  induction rows generalizing index with
  | nil => simp at hindex
  | cons coordinate rows ih =>
      have hcoordinate := hrange coordinate (by simp)
      cases index with
      | zero =>
          change
            (((canonicalPackedCoordinateDigit coordinate +
              16 * canonicalPackedRowList rows) % 16 : Nat) : Int) - 8 =
                coordinate
          have hdigit := canonicalPackedCoordinateDigit_lt
            coordinate hcoordinate.1 hcoordinate.2
          have hmod :
              (canonicalPackedCoordinateDigit coordinate +
                16 * canonicalPackedRowList rows) % 16 =
                  canonicalPackedCoordinateDigit coordinate := by
            omega
          rw [hmod]
          have hnonneg : 0 ≤ coordinate + 8 := by omega
          unfold canonicalPackedCoordinateDigit
          rw [Int.toNat_of_nonneg hnonneg]
          omega
      | succ index =>
          have hindex' : index < rows.length := by simpa using hindex
          have htail : ∀ value ∈ rows, -8 ≤ value ∧ value < 8 := by
            intro value hvalue
            exact hrange value (by simp [hvalue])
          unfold canonicalPackedCoordinate
          rw [show 4 * (index + 1) = 4 + 4 * index by omega,
            Nat.shiftRight_add,
            canonicalPackedRowList_shiftRight_four
              coordinate rows hcoordinate.1 hcoordinate.2]
          exact ih index hindex' htail


theorem canonicalPackedCoordinate_eq_getD
    (row : Array Int) (index : Nat) (hindex : index < row.size)
    (hrange : ∀ (coordinate : Nat) (hcoordinate : coordinate < row.size),
      -8 ≤ row[coordinate]'hcoordinate ∧ row[coordinate]'hcoordinate < 8) :
    canonicalPackedCoordinate (canonicalPackedRow row) index =
      row.getD index 0 := by
  have hlist : ∀ coordinate ∈ row.toList,
      -8 ≤ coordinate ∧ coordinate < 8 := by
    intro coordinate hcoordinate
    obtain ⟨index, hindex, rfl⟩ :=
      List.get_of_mem hcoordinate
    exact hrange index.val (by simp)
  have hcoordinate := canonicalPackedCoordinateList_get row.toList
    index (by simpa using hindex) hlist
  simpa [canonicalPackedRow, Array.getD_eq_getD_getElem?, hindex]
    using hcoordinate


def canonicalPackedDescendingCoordinates (packed : Nat) : List Int :=
  ((List.range 20).map (canonicalPackedCoordinate packed)).reverse


theorem canonicalPackedDescendingCoordinates_eq
    (row : Array Int) (hsize : row.size = 20)
    (hrange : ∀ (coordinate : Nat) (hcoordinate : coordinate < row.size),
      -8 ≤ row[coordinate]'hcoordinate ∧ row[coordinate]'hcoordinate < 8) :
    canonicalPackedDescendingCoordinates (canonicalPackedRow row) =
      row.toList.reverse := by
  have hforward :
      (List.range row.size).map
        (canonicalPackedCoordinate (canonicalPackedRow row)) =
          row.toList := by
    apply List.ext_getElem
    · simp
    · intro index hleft hright
      have hindex : index < row.size := by simpa using hright
      simpa [Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hindex] using
        canonicalPackedCoordinate_eq_getD row index hindex hrange
  unfold canonicalPackedDescendingCoordinates
  rw [← hsize, hforward]


def canonicalPackedDescendingLE (left right : Nat) : Bool :=
  decide (canonicalPackedDescendingCoordinates left ≤
    canonicalPackedDescendingCoordinates right)



theorem canonicalPackedDescendingLE_iff
    (left right : Array Int)
    (hleft : left.size = 20) (hright : right.size = 20)
    (hleftRange : ∀ (index : Nat) (hindex : index < left.size),
      -8 ≤ left[index]'hindex ∧ left[index]'hindex < 8)
    (hrightRange : ∀ (index : Nat) (hindex : index < right.size),
      -8 ≤ right[index]'hindex ∧ right[index]'hindex < 8) :
    canonicalPackedDescendingLE
      (canonicalPackedRow left) (canonicalPackedRow right) = true ↔
      left.toList.reverse ≤ right.toList.reverse := by
  simp [canonicalPackedDescendingLE,
    canonicalPackedDescendingCoordinates_eq left hleft hleftRange,
    canonicalPackedDescendingCoordinates_eq right hright hrightRange]

end ConnesRigidity.AffineSymplecticOrbitCertificate

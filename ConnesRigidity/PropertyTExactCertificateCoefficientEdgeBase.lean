
import Lean
import ConnesRigidity.GroupRingCertificateAlgebra

namespace ConnesRigidity

namespace AffineSymplecticCertificate

structure CoefficientNegativePacket where
  left : Int
  right : Int
  weight : Int
  keyLL : Int
  keyLR : Int
  keyRL : Int
  keyRR : Int

structure CoefficientPositivePacket where
  left : Int
  right : Int
  weight : Int
  key00 : Int
  key0L : Int
  key0R : Int
  keyL0 : Int
  keyLL : Int
  keyLR : Int
  keyR0 : Int
  keyRL : Int
  keyRR : Int

structure CoefficientDiagonalPacket where
  index : Int
  weight : Int
  key00 : Int
  key0I : Int
  keyI0 : Int
  keyII : Int

def decodeCoefficientNegativePacket :
    List Int → Option CoefficientNegativePacket
  | left :: right :: weight :: keyLL :: keyLR :: keyRL :: keyRR :: [] =>
      some { left, right, weight, keyLL, keyLR, keyRL, keyRR }
  | _ => none

def decodeCoefficientPositivePacket :
    List Int → Option CoefficientPositivePacket
  | left :: right :: weight :: key00 :: key0L :: key0R ::
      keyL0 :: keyLL :: keyLR :: keyR0 :: keyRL :: keyRR :: [] =>
      some {
        left, right, weight, key00, key0L, key0R,
        keyL0, keyLL, keyLR, keyR0, keyRL, keyRR }
  | _ => none

def decodeCoefficientDiagonalPacket :
    List Int → Option CoefficientDiagonalPacket
  | index :: weight :: key00 :: key0I :: keyI0 :: keyII :: [] =>
      some { index, weight, key00, key0I, keyI0, keyII }
  | _ => none

def coefficientEdgeTerm (key : Int) (numerator : Int) :
    IntegerTableTerm 73033 where
  key := Fin.ofNat 73033 key.toNat
  numerator := numerator

def coefficientNegativeDecodedPacketTerms
    (packet : CoefficientNegativePacket) :
    List (IntegerTableTerm 73033) :=
  let weight : Int := 4 * packet.weight.toNat
  [coefficientEdgeTerm packet.keyLL weight,
    coefficientEdgeTerm packet.keyLR (-weight),
    coefficientEdgeTerm packet.keyRL (-weight),
    coefficientEdgeTerm packet.keyRR weight]

def coefficientPositiveDecodedPacketTerms
    (packet : CoefficientPositivePacket) :
    List (IntegerTableTerm 73033) :=
  let weight : Int := 4 * packet.weight.toNat
  let term (key : Int) (coefficient : Int) :=
    coefficientEdgeTerm key (weight * coefficient)
  [term packet.key00 4,
    term packet.key0L (-2),
    term packet.key0R (-2),
    term packet.keyL0 (-2),
    term packet.keyLL 1,
    term packet.keyLR 1,
    term packet.keyR0 (-2),
    term packet.keyRL 1,
    term packet.keyRR 1]

def coefficientDiagonalDecodedPacketTerms
    (packet : CoefficientDiagonalPacket) :
    List (IntegerTableTerm 73033) :=
  let weight : Int := 4 * packet.weight.toNat
  [coefficientEdgeTerm packet.key00 weight,
    coefficientEdgeTerm packet.key0I (-weight),
    coefficientEdgeTerm packet.keyI0 (-weight),
    coefficientEdgeTerm packet.keyII weight]

def coefficientNegativePacketTerms
    (row : List Int) : List (IntegerTableTerm 73033) :=
  (decodeCoefficientNegativePacket row).map
    coefficientNegativeDecodedPacketTerms |>.getD []

def coefficientPositivePacketTerms
    (row : List Int) : List (IntegerTableTerm 73033) :=
  (decodeCoefficientPositivePacket row).map
    coefficientPositiveDecodedPacketTerms |>.getD []

def coefficientDiagonalPacketTerms
    (row : List Int) : List (IntegerTableTerm 73033) :=
  (decodeCoefficientDiagonalPacket row).map
    coefficientDiagonalDecodedPacketTerms |>.getD []

def coefficientNegativePacketsTerms
    (rows : List (List Int)) : List (IntegerTableTerm 73033) :=
  rows.flatMap coefficientNegativePacketTerms

def coefficientPositivePacketsTerms
    (rows : List (List Int)) : List (IntegerTableTerm 73033) :=
  rows.flatMap coefficientPositivePacketTerms

def coefficientDiagonalPacketsTerms
    (rows : List (List Int)) : List (IntegerTableTerm 73033) :=
  rows.flatMap coefficientDiagonalPacketTerms

def coefficientNegativePacketMatches
    (product : Fin 425 → Fin 425 → Fin 73033)
    (row : List Int) : Prop :=
  match decodeCoefficientNegativePacket row with
  | none => False
  | some packet =>
      let left := Fin.ofNat 425 packet.left.toNat
      let right := Fin.ofNat 425 packet.right.toNat
      Fin.ofNat 73033 packet.keyLL.toNat = product left left ∧
        Fin.ofNat 73033 packet.keyLR.toNat = product left right ∧
        Fin.ofNat 73033 packet.keyRL.toNat = product right left ∧
        Fin.ofNat 73033 packet.keyRR.toNat = product right right

def coefficientPositivePacketMatches
    (product : Fin 425 → Fin 425 → Fin 73033)
    (row : List Int) : Prop :=
  match decodeCoefficientPositivePacket row with
  | none => False
  | some packet =>
      let zero := Fin.ofNat 425 0
      let left := Fin.ofNat 425 packet.left.toNat
      let right := Fin.ofNat 425 packet.right.toNat
      Fin.ofNat 73033 packet.key00.toNat = product zero zero ∧
        Fin.ofNat 73033 packet.key0L.toNat = product zero left ∧
        Fin.ofNat 73033 packet.key0R.toNat = product zero right ∧
        Fin.ofNat 73033 packet.keyL0.toNat = product left zero ∧
        Fin.ofNat 73033 packet.keyLL.toNat = product left left ∧
        Fin.ofNat 73033 packet.keyLR.toNat = product left right ∧
        Fin.ofNat 73033 packet.keyR0.toNat = product right zero ∧
        Fin.ofNat 73033 packet.keyRL.toNat = product right left ∧
        Fin.ofNat 73033 packet.keyRR.toNat = product right right

def coefficientDiagonalPacketMatches
    (product : Fin 425 → Fin 425 → Fin 73033)
    (row : List Int) : Prop :=
  match decodeCoefficientDiagonalPacket row with
  | none => False
  | some packet =>
      let zero := Fin.ofNat 425 0
      let index := Fin.ofNat 425 packet.index.toNat.succ
      Fin.ofNat 73033 packet.key00.toNat = product zero zero ∧
        Fin.ofNat 73033 packet.key0I.toNat = product zero index ∧
        Fin.ofNat 73033 packet.keyI0.toNat = product index zero ∧
        Fin.ofNat 73033 packet.keyII.toNat = product index index

def coefficientNegativeCanonicalPacketTerms
    (product : Fin 425 → Fin 425 → Fin 73033)
    (row : List Int) : List (IntegerTableTerm 73033) :=
  match decodeCoefficientNegativePacket row with
  | none => []
  | some packet =>
      let left := Fin.ofNat 425 packet.left.toNat
      let right := Fin.ofNat 425 packet.right.toNat
      let weight : Int := 4 * packet.weight.toNat
      [{ key := product left left, numerator := weight },
        { key := product left right, numerator := -weight },
        { key := product right left, numerator := -weight },
        { key := product right right, numerator := weight }]

def coefficientPositiveCanonicalPacketTerms
    (product : Fin 425 → Fin 425 → Fin 73033)
    (row : List Int) : List (IntegerTableTerm 73033) :=
  match decodeCoefficientPositivePacket row with
  | none => []
  | some packet =>
      let zero := Fin.ofNat 425 0
      let left := Fin.ofNat 425 packet.left.toNat
      let right := Fin.ofNat 425 packet.right.toNat
      let weight : Int := 4 * packet.weight.toNat
      [{ key := product zero zero, numerator := weight * 4 },
        { key := product zero left, numerator := weight * (-2) },
        { key := product zero right, numerator := weight * (-2) },
        { key := product left zero, numerator := weight * (-2) },
        { key := product left left, numerator := weight },
        { key := product left right, numerator := weight },
        { key := product right zero, numerator := weight * (-2) },
        { key := product right left, numerator := weight },
        { key := product right right, numerator := weight }]

def coefficientDiagonalCanonicalPacketTerms
    (product : Fin 425 → Fin 425 → Fin 73033)
    (row : List Int) : List (IntegerTableTerm 73033) :=
  match decodeCoefficientDiagonalPacket row with
  | none => []
  | some packet =>
      let zero := Fin.ofNat 425 0
      let index := Fin.ofNat 425 packet.index.toNat.succ
      let weight : Int := 4 * packet.weight.toNat
      [{ key := product zero zero, numerator := weight },
        { key := product zero index, numerator := -weight },
        { key := product index zero, numerator := -weight },
        { key := product index index, numerator := weight }]

theorem coefficientNegativePacketTerms_eq_canonical
    (product : Fin 425 → Fin 425 → Fin 73033)
    (row : List Int)
    (h : coefficientNegativePacketMatches product row) :
    coefficientNegativePacketTerms row =
      coefficientNegativeCanonicalPacketTerms product row := by
  cases hpacket : decodeCoefficientNegativePacket row with
  | none =>
      simp [coefficientNegativePacketMatches, hpacket] at h
  | some packet =>
      simp only [coefficientNegativePacketMatches, hpacket] at h
      simpa [coefficientNegativePacketTerms,
        coefficientNegativeDecodedPacketTerms,
        coefficientNegativeCanonicalPacketTerms,
        coefficientEdgeTerm, hpacket] using h

theorem coefficientPositivePacketTerms_eq_canonical
    (product : Fin 425 → Fin 425 → Fin 73033)
    (row : List Int)
    (h : coefficientPositivePacketMatches product row) :
    coefficientPositivePacketTerms row =
      coefficientPositiveCanonicalPacketTerms product row := by
  cases hpacket : decodeCoefficientPositivePacket row with
  | none =>
      simp [coefficientPositivePacketMatches, hpacket] at h
  | some packet =>
      simp only [coefficientPositivePacketMatches, hpacket] at h
      simpa [coefficientPositivePacketTerms,
        coefficientPositiveDecodedPacketTerms,
        coefficientPositiveCanonicalPacketTerms,
        coefficientEdgeTerm, hpacket] using h

theorem coefficientDiagonalPacketTerms_eq_canonical
    (product : Fin 425 → Fin 425 → Fin 73033)
    (row : List Int)
    (h : coefficientDiagonalPacketMatches product row) :
    coefficientDiagonalPacketTerms row =
      coefficientDiagonalCanonicalPacketTerms product row := by
  cases hpacket : decodeCoefficientDiagonalPacket row with
  | none =>
      simp [coefficientDiagonalPacketMatches, hpacket] at h
  | some packet =>
      simp only [coefficientDiagonalPacketMatches, hpacket] at h
      simpa [coefficientDiagonalPacketTerms,
        coefficientDiagonalDecodedPacketTerms,
        coefficientDiagonalCanonicalPacketTerms,
        coefficientEdgeTerm, hpacket] using h

private theorem flatMap_eq_flatMap_of_forall_mem
    {α β : Type*} (left right : α → List β) :
    ∀ rows : List α,
      (∀ row ∈ rows, left row = right row) →
        rows.flatMap left = rows.flatMap right
  | [], _ => rfl
  | row :: rows, h => by
      rw [List.flatMap_cons, List.flatMap_cons,
        h row (by simp),
        flatMap_eq_flatMap_of_forall_mem left right rows]
      intro tail htail
      exact h tail (by simp [htail])

theorem coefficientNegativePacketsTerms_eq_canonical
    (product : Fin 425 → Fin 425 → Fin 73033)
    (rows : List (List Int))
    (h : ∀ row ∈ rows, coefficientNegativePacketMatches product row) :
    coefficientNegativePacketsTerms rows =
      rows.flatMap (coefficientNegativeCanonicalPacketTerms product) := by
  unfold coefficientNegativePacketsTerms
  apply flatMap_eq_flatMap_of_forall_mem
  intro row hrow
  exact coefficientNegativePacketTerms_eq_canonical
    product row (h row hrow)

theorem coefficientPositivePacketsTerms_eq_canonical
    (product : Fin 425 → Fin 425 → Fin 73033)
    (rows : List (List Int))
    (h : ∀ row ∈ rows, coefficientPositivePacketMatches product row) :
    coefficientPositivePacketsTerms rows =
      rows.flatMap (coefficientPositiveCanonicalPacketTerms product) := by
  unfold coefficientPositivePacketsTerms
  apply flatMap_eq_flatMap_of_forall_mem
  intro row hrow
  exact coefficientPositivePacketTerms_eq_canonical
    product row (h row hrow)

theorem coefficientDiagonalPacketsTerms_eq_canonical
    (product : Fin 425 → Fin 425 → Fin 73033)
    (rows : List (List Int))
    (h : ∀ row ∈ rows, coefficientDiagonalPacketMatches product row) :
    coefficientDiagonalPacketsTerms rows =
      rows.flatMap (coefficientDiagonalCanonicalPacketTerms product) := by
  unfold coefficientDiagonalPacketsTerms
  apply flatMap_eq_flatMap_of_forall_mem
  intro row hrow
  exact coefficientDiagonalPacketTerms_eq_canonical
    product row (h row hrow)

end AffineSymplecticCertificate

end ConnesRigidity

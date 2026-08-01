


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgeBase
import ConnesRigidity.PropertyTExactCertificateTerms










namespace ConnesRigidity

namespace AffineSymplecticCertificate



def coefficientNegativePacketEdge
    (packet : CoefficientNegativePacket) : Edge where
  left := packet.left.toNat
  right := packet.right.toNat
  weightNumerator := packet.weight.toNat



def coefficientPositivePacketEdge
    (packet : CoefficientPositivePacket) : Edge where
  left := packet.left.toNat
  right := packet.right.toNat
  weightNumerator := packet.weight.toNat



noncomputable def coefficientNegativePacketSourceTerms
    (row : List Int) : List (IntegerTableTerm 73033) :=
  (decodeCoefficientNegativePacket row).map
    (negativeEdgeTermRow ∘ coefficientNegativePacketEdge) |>.getD []



noncomputable def coefficientPositivePacketSourceTerms
    (row : List Int) : List (IntegerTableTerm 73033) :=
  (decodeCoefficientPositivePacket row).map
    (positiveEdgeTermRow ∘ coefficientPositivePacketEdge) |>.getD []



noncomputable def coefficientDiagonalPacketSourceTerms
    (row : List Int) : List (IntegerTableTerm 73033) :=
  match decodeCoefficientDiagonalPacket row with
  | none => []
  | some packet =>
      integerOuterTerms (4 * (packet.weight.toNat : Int))
        (diagonalEntries packet.index.toNat)



def coefficientPositivePacketIsNonSkipped (row : List Int) : Prop :=
  match decodeCoefficientPositivePacket row with
  | none => False
  | some packet =>
      packet.left.toNat ≠ 0 ∧ packet.right.toNat ≠ 0



theorem coefficientNegativeCanonicalPacketTerms_eq_source
    (row : List Int) :
    coefficientNegativeCanonicalPacketTerms tableIndex row =
      coefficientNegativePacketSourceTerms row := by
  cases hpacket : decodeCoefficientNegativePacket row with
  | none =>
      simp [coefficientNegativeCanonicalPacketTerms,
        coefficientNegativePacketSourceTerms, hpacket]
  | some packet =>
      simp [coefficientNegativeCanonicalPacketTerms,
        coefficientNegativePacketSourceTerms,
        coefficientNegativePacketEdge, negativeEdgeTermRow,
        negativeEdgeEntries, integerOuterTerms, basisIndex,
        hpacket]



theorem coefficientPositiveCanonicalPacketTerms_eq_source
    (row : List Int)
    (h : coefficientPositivePacketIsNonSkipped row) :
    coefficientPositiveCanonicalPacketTerms tableIndex row =
      coefficientPositivePacketSourceTerms row := by
  cases hpacket : decodeCoefficientPositivePacket row with
  | none =>
      simp [coefficientPositivePacketIsNonSkipped, hpacket] at h
  | some packet =>
      simp only [coefficientPositivePacketIsNonSkipped, hpacket] at h
      rcases h with ⟨hleft, hright⟩
      simp [coefficientPositiveCanonicalPacketTerms,
        coefficientPositivePacketSourceTerms,
        coefficientPositivePacketEdge, positiveEdgeTermRow,
        positiveEdgeEntries, integerOuterTerms, basisIndex,
        hpacket, hleft, hright]



theorem coefficientDiagonalCanonicalPacketTerms_eq_source
    (row : List Int) :
    coefficientDiagonalCanonicalPacketTerms tableIndex row =
      coefficientDiagonalPacketSourceTerms row := by
  cases hpacket : decodeCoefficientDiagonalPacket row with
  | none =>
      simp [coefficientDiagonalCanonicalPacketTerms,
        coefficientDiagonalPacketSourceTerms, hpacket]
  | some packet =>
      simp [coefficientDiagonalCanonicalPacketTerms,
        coefficientDiagonalPacketSourceTerms,
        diagonalEntries, integerOuterTerms, basisIndex,
        hpacket]


theorem coefficientNegativePacketTerms_eq_source
    (row : List Int)
    (h : coefficientNegativePacketMatches tableIndex row) :
    coefficientNegativePacketTerms row =
      coefficientNegativePacketSourceTerms row := by
  rw [coefficientNegativePacketTerms_eq_canonical tableIndex row h,
    coefficientNegativeCanonicalPacketTerms_eq_source]



theorem coefficientPositivePacketTerms_eq_source
    (row : List Int)
    (hkeys : coefficientPositivePacketMatches tableIndex row)
    (hskip : coefficientPositivePacketIsNonSkipped row) :
    coefficientPositivePacketTerms row =
      coefficientPositivePacketSourceTerms row := by
  rw [coefficientPositivePacketTerms_eq_canonical tableIndex row hkeys,
    coefficientPositiveCanonicalPacketTerms_eq_source row hskip]


theorem coefficientDiagonalPacketTerms_eq_source
    (row : List Int)
    (h : coefficientDiagonalPacketMatches tableIndex row) :
    coefficientDiagonalPacketTerms row =
      coefficientDiagonalPacketSourceTerms row := by
  rw [coefficientDiagonalPacketTerms_eq_canonical tableIndex row h,
    coefficientDiagonalCanonicalPacketTerms_eq_source]

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



theorem coefficientNegativePacketsTerms_eq_source
    (rows : List (List Int))
    (h : ∀ row ∈ rows, coefficientNegativePacketMatches tableIndex row) :
    coefficientNegativePacketsTerms rows =
      rows.flatMap coefficientNegativePacketSourceTerms := by
  unfold coefficientNegativePacketsTerms
  apply flatMap_eq_flatMap_of_forall_mem
  intro row hrow
  exact coefficientNegativePacketTerms_eq_source row (h row hrow)



theorem coefficientPositivePacketsTerms_eq_source
    (rows : List (List Int))
    (hkeys :
      ∀ row ∈ rows, coefficientPositivePacketMatches tableIndex row)
    (hskip :
      ∀ row ∈ rows, coefficientPositivePacketIsNonSkipped row) :
    coefficientPositivePacketsTerms rows =
      rows.flatMap coefficientPositivePacketSourceTerms := by
  unfold coefficientPositivePacketsTerms
  apply flatMap_eq_flatMap_of_forall_mem
  intro row hrow
  exact coefficientPositivePacketTerms_eq_source
    row (hkeys row hrow) (hskip row hrow)



theorem coefficientDiagonalPacketsTerms_eq_source
    (rows : List (List Int))
    (h : ∀ row ∈ rows, coefficientDiagonalPacketMatches tableIndex row) :
    coefficientDiagonalPacketsTerms rows =
      rows.flatMap coefficientDiagonalPacketSourceTerms := by
  unfold coefficientDiagonalPacketsTerms
  apply flatMap_eq_flatMap_of_forall_mem
  intro row hrow
  exact coefficientDiagonalPacketTerms_eq_source row (h row hrow)

end AffineSymplecticCertificate

end ConnesRigidity

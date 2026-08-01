


import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalData
import ConnesRigidity.PropertyTExactCertificateOrbitBasisTransport
import ConnesRigidity.PropertyTExactCertificateOrbitIncidenceValidation
















namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0


def orbitCoefficientPacketRow (packet : List Int) (offset : Nat) :
    Array Int :=
  ((packet.drop offset).take 20).toArray



def orbitCoefficientTransportPacketCheck
    (position : Nat) (gram : Array Int) (packet : List Int) : Bool :=
  let orbit := packet.getD 0 0
  let left := packet.getD 1 0
  let right := packet.getD 2 0
  let coefficient := packet.getD 3 0
  let symmetry := packet.getD 4 0
  let inversion := packet.getD 5 0
  let leftRow := orbitCoefficientPacketRow packet 6
  let rightRow := orbitCoefficientPacketRow packet 26
  let coefficientRow := orbitCoefficientPacketRow packet 46
  decide (packet.length = 66) &&
    decide (orbit = (position : Int)) &&
    decide (left = orbitEntry gram 0) &&
    decide (right = orbitEntry gram 1) &&
    decide (coefficient = orbitEntry gram 2) &&
    decide (symmetry = orbitEntry gram 5) &&
    decide (inversion = orbitEntry gram 6) &&
    rawRowEq leftRow (basisData.getD left.toNat #[]) &&
    rawRowEq rightRow (basisData.getD right.toNat #[]) &&
    rawRowEq coefficientRow
      (coefficientRepresentativeData.getD coefficient.toNat #[]) &&
    if inversion = 0 then
      rawProductCheck leftRow
        (signedRowAction (symmetryData.getD symmetry.toNat #[])
          coefficientRow) rightRow
    else
      rawProductCheck rightRow
        (signedRowAction (symmetryData.getD symmetry.toNat #[])
          coefficientRow) leftRow




def orbitCoefficientTransportPacketsCheck :
    Nat → List (Array Int) → List (List Int) → Bool
  | _, [], [] => true
  | position, gram :: grams, packet :: packets =>
      orbitCoefficientTransportPacketCheck position gram packet &&
        orbitCoefficientTransportPacketsCheck
          (position + 1) grams packets
  | _, _, _ => false



theorem orbitCoefficientTransportPacketCheck_sound
    (position : Nat) (gram : Array Int) (packet : List Int)
    (hcheck : orbitCoefficientTransportPacketCheck
      position gram packet = true) :
    let left := packet.getD 1 0
    let right := packet.getD 2 0
    let coefficient := packet.getD 3 0
    let symmetry := packet.getD 4 0
    let inversion := packet.getD 5 0
    let leftRow := orbitCoefficientPacketRow packet 6
    let rightRow := orbitCoefficientPacketRow packet 26
    let coefficientRow := orbitCoefficientPacketRow packet 46
    packet.length = 66 ∧
      packet.getD 0 0 = (position : Int) ∧
      left = orbitEntry gram 0 ∧
      right = orbitEntry gram 1 ∧
      coefficient = orbitEntry gram 2 ∧
      symmetry = orbitEntry gram 5 ∧
      inversion = orbitEntry gram 6 ∧
      rawRowEq leftRow (basisData.getD left.toNat #[]) = true ∧
      rawRowEq rightRow (basisData.getD right.toNat #[]) = true ∧
      rawRowEq coefficientRow
        (coefficientRepresentativeData.getD coefficient.toNat #[]) = true ∧
      (if inversion = 0 then
        rawProductCheck leftRow
          (signedRowAction (symmetryData.getD symmetry.toNat #[])
            coefficientRow) rightRow
      else
        rawProductCheck rightRow
          (signedRowAction (symmetryData.getD symmetry.toNat #[])
            coefficientRow) leftRow) = true := by
  simpa only [orbitCoefficientTransportPacketCheck, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc] using hcheck



theorem orbitCoefficientTransportPacketsCheck_get
    (position : Nat) (grams : List (Array Int))
    (packets : List (List Int)) (index : Nat)
    (hindex : index < grams.length)
    (hcheck : orbitCoefficientTransportPacketsCheck
      position grams packets = true) :
    ∃ hpacket : index < packets.length,
      orbitCoefficientTransportPacketCheck (position + index)
        grams[index] packets[index] = true := by
  induction grams generalizing position packets index with
  | nil => simp at hindex
  | cons gram grams ih =>
      cases packets with
      | nil => simp [orbitCoefficientTransportPacketsCheck] at hcheck
      | cons packet packets =>
          simp only [orbitCoefficientTransportPacketsCheck,
            Bool.and_eq_true] at hcheck
          cases index with
          | zero => exact ⟨by simp, by simpa using hcheck.1⟩
          | succ index =>
              have hindex' : index < grams.length := by
                simpa using hindex
              obtain ⟨hpacket, hsemantic⟩ :=
                ih (position + 1) packets index hindex' hcheck.2
              refine ⟨by simpa using hpacket, ?_⟩
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                using hsemantic

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

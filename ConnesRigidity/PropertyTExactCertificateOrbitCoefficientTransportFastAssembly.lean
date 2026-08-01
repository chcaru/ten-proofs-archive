import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientTransportValidation

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

theorem orbitCoefficientTransportPacketsCheck_append
    (position : Nat) (leftGrams rightGrams : List (Array Int))
    (leftPackets rightPackets : List (List Int))
    (hlength : leftGrams.length = leftPackets.length) :
    orbitCoefficientTransportPacketsCheck position
        (leftGrams ++ rightGrams) (leftPackets ++ rightPackets) =
      (orbitCoefficientTransportPacketsCheck position
        leftGrams leftPackets &&
        orbitCoefficientTransportPacketsCheck
          (position + leftGrams.length) rightGrams rightPackets) := by
  induction leftGrams generalizing position leftPackets with
  | nil =>
      have hnil : leftPackets = [] := by
        simpa using hlength.symm
      simp [hnil, orbitCoefficientTransportPacketsCheck]
  | cons gram grams ih =>
      cases leftPackets with
      | nil => simp at hlength
      | cons packet packets =>
          have hlength' : grams.length = packets.length := by
            simpa using hlength
          simp only [List.cons_append,
            orbitCoefficientTransportPacketsCheck,
            ih (position + 1) packets hlength', Bool.and_assoc,
            List.length_cons]
          congr 2
          congr 1
          omega

theorem orbitCoefficientTransportPacketsCheck_step
    (position : Nat) (grams : List (Array Int))
    (packets : List (List Int))
    (hgrams : 188 ≤ grams.length)
    (hpackets : 188 ≤ packets.length)
    (hhead : orbitCoefficientTransportPacketsCheck position
      (grams.take 188) (packets.take 188) = true)
    (htail : orbitCoefficientTransportPacketsCheck (position + 188)
      (grams.drop 188) (packets.drop 188) = true) :
    orbitCoefficientTransportPacketsCheck position grams packets = true := by
  conv_lhs =>
    arg 2
    rw [← List.take_append_drop 188 grams]
  conv_lhs =>
    arg 3
    rw [← List.take_append_drop 188 packets]
  rw [orbitCoefficientTransportPacketsCheck_append]
  · simpa [List.length_take, Nat.min_eq_left hgrams, hhead] using htail
  · simp [List.length_take, Nat.min_eq_left hgrams,
      Nat.min_eq_left hpackets]

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

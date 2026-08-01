


import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientTransportValidation
import ConnesRigidity.PropertyTExactCertificateOrbitCoefficientTransportFastValidation
import ConnesRigidity.PropertyTExactCertificateOrbitInvariantWitness
import ConnesRigidity.PropertyTExactCertificateOrbitTargetRepresentativeSoundness
import ConnesRigidity.PropertyTExactCertificateOrbitTargetValidation











namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0



theorem coefficientRepresentativeRow_symplectic (coefficient : Fin 995) :
    isSymplecticRow
      (coefficientRepresentativeData.getD coefficient.val #[]) = true := by
  obtain ⟨_, _, hrowsSize, hinverseSize, _, _, _, _, _, hinverse, _, hrows⟩ :=
    orbitTargetStreamingCheck_sound orbitTargetStreamingCheck_valid
  exact (orbitTargetRepresentativeRowsCheck_orbit coefficient
    hinverseSize hrowsSize hinverse hrows).2.2.1




theorem orbitCoefficientTransportPacket_semantics
    (left right : Fin 425) (coefficient : Fin 995)
    (symmetry : Fin 64) (inversion : Int)
    (leftRow rightRow coefficientRow : Array Int)
    (hleft : rawRowEq leftRow (basisData.getD left.val #[]) = true)
    (hright : rawRowEq rightRow (basisData.getD right.val #[]) = true)
    (hcoefficient : rawRowEq coefficientRow
      (coefficientRepresentativeData.getD coefficient.val #[]) = true)
    (hproduct :
      (if inversion = 0 then
        rawProductCheck leftRow
          (signedRowAction (symmetryData.getD symmetry.val #[])
            coefficientRow) rightRow
      else
        rawProductCheck rightRow
          (signedRowAction (symmetryData.getD symmetry.val #[])
            coefficientRow) leftRow) = true) :
    coefficientRepresentativeElement coefficient.val ∈
      MulAction.orbit OrbitSignedSymmetry
        ((orbitBasis left)⁻¹ * orbitBasis right) := by
  have hleftValid : isSymplecticRow leftRow = true :=
    (rawRowEq_isSymplecticRow hleft).trans (orbitBasisRows_symplectic left)
  have hrightValid : isSymplecticRow rightRow = true :=
    (rawRowEq_isSymplecticRow hright).trans
      (orbitBasisRows_symplectic right)
  have hcoefficientValid : isSymplecticRow coefficientRow = true :=
    (rawRowEq_isSymplecticRow hcoefficient).trans
      (coefficientRepresentativeRow_symplectic coefficient)
  have hnormalizer := symmetryNormalizerRowChecks symmetry
  have hactionValid := isSymplecticRow_signedRowAction
    hnormalizer hcoefficientValid
  have hleftElement : gammaZeroOfRow leftRow = orbitBasis left := by
    simpa [orbitBasis, basisElement] using rawRowEq_gammaZeroOfRow hleft
  have hrightElement : gammaZeroOfRow rightRow = orbitBasis right := by
    simpa [orbitBasis, basisElement] using rawRowEq_gammaZeroOfRow hright
  have hcoefficientElement : gammaZeroOfRow coefficientRow =
      coefficientRepresentativeElement coefficient.val := by
    simpa [coefficientRepresentativeElement] using
      rawRowEq_gammaZeroOfRow hcoefficient
  have haction : gammaZeroOfRow
      (signedRowAction (symmetryData.getD symmetry.val #[])
        coefficientRow) =
      orbitSymmetry symmetry
        (coefficientRepresentativeElement coefficient.val) := by
    rw [signedRowAction_sound hnormalizer hcoefficientValid,
      hcoefficientElement]
    rfl
  by_cases hinversion : inversion = 0
  · rw [if_pos hinversion] at hproduct
    have hgroup := rawProductCheck_sound hleftValid hactionValid
      hrightValid hproduct
    rw [hleftElement, haction, hrightElement] at hgroup
    have htransport : orbitSymmetry symmetry
        (coefficientRepresentativeElement coefficient.val) =
        (orbitBasis left)⁻¹ * orbitBasis right :=
      eq_inv_mul_iff_mul_eq.mpr hgroup
    let signed : OrbitSignedSymmetry :=
      (⟨symmetry⟩, Multiplicative.ofAdd (0 : ZMod 2))
    refine MulAction.mem_orbit_iff.mpr ⟨signed⁻¹, ?_⟩
    have hsigned : signed • coefficientRepresentativeElement coefficient.val =
        (orbitBasis left)⁻¹ * orbitBasis right := by
      simpa [signed, signedGroupAction_apply] using htransport
    rw [← hsigned, inv_smul_smul]
  · rw [if_neg hinversion] at hproduct
    have hgroup := rawProductCheck_sound hrightValid hactionValid
      hleftValid hproduct
    rw [hrightElement, haction, hleftElement] at hgroup
    have htransport : orbitSymmetry symmetry
        (coefficientRepresentativeElement coefficient.val) =
        (orbitBasis right)⁻¹ * orbitBasis left :=
      eq_inv_mul_iff_mul_eq.mpr hgroup
    let signed : OrbitSignedSymmetry :=
      (⟨symmetry⟩, Multiplicative.ofAdd (1 : ZMod 2))
    refine MulAction.mem_orbit_iff.mpr ⟨signed⁻¹, ?_⟩
    have hsigned : signed • coefficientRepresentativeElement coefficient.val =
        (orbitBasis left)⁻¹ * orbitBasis right := by
      change
        (if (1 : ZMod 2) = 0 then
          orbitSymmetry symmetry
            (coefficientRepresentativeElement coefficient.val)
        else
          (orbitSymmetry symmetry
            (coefficientRepresentativeElement coefficient.val))⁻¹) =
          (orbitBasis left)⁻¹ * orbitBasis right
      simp only [one_ne_zero, ↓reduceIte]
      rw [htransport, mul_inv_rev, inv_inv]
    rw [← hsigned, inv_smul_smul]



theorem orbitGram_coefficientRepresentative_mem_of_transport
    (hcheck : orbitCoefficientTransportPacketsCheck 0
      gramOrbitData.toList orbitCoefficientTransportPacketData = true)
    (gram : Fin 2256) :
    coefficientRepresentativeElement
        (gramOrbitCoefficientOrbit gram.val).toNat ∈
      MulAction.orbit OrbitSignedSymmetry
        ((orbitBasis (orbitGramRepresentative gram).1)⁻¹ *
          orbitBasis (orbitGramRepresentative gram).2) := by
  have hgramIndex : gram.val < gramOrbitData.size := by
    simp [gramOrbitData_size]
  have hlistIndex : gram.val < gramOrbitData.toList.length := by
    simpa using hgramIndex
  obtain ⟨hpacketIndex, hpacket⟩ :=
    orbitCoefficientTransportPacketsCheck_get 0 gramOrbitData.toList
      orbitCoefficientTransportPacketData gram.val hlistIndex hcheck
  let row : Array Int := gramOrbitData[gram.val]
  let packet : List Int := orbitCoefficientTransportPacketData[gram.val]
  have hpacket' : orbitCoefficientTransportPacketCheck
      gram.val row packet = true := by
    simpa [row, packet] using hpacket
  have hfields := orbitGramRepresentativeFields_valid gram.val hgramIndex
  change
    row.size = gramOrbitRowWidth ∧
      (0 ≤ orbitEntry row 0 ∧ orbitEntry row 0 < (basisData.size : Int)) ∧
      (0 ≤ orbitEntry row 1 ∧ orbitEntry row 1 < (basisData.size : Int)) ∧
      (0 ≤ orbitEntry row 2 ∧
        orbitEntry row 2 < (coefficientRepresentativeData.size : Int)) ∧
      0 ≤ orbitEntry row 3 ∧
      (0 ≤ orbitEntry row 5 ∧ orbitEntry row 5 < (symmetryData.size : Int)) ∧
      (orbitEntry row 6 = 0 ∨ orbitEntry row 6 = 1) ∧
      0 < orbitEntry row 7 at hfields
  obtain ⟨_, _, _, hcoefficientBounds, _, hsymmetryBounds, _, _⟩ := hfields
  have hsymmetrySize : symmetryData.size = 64 := by
    simpa [symmetryCardinality] using
      (orbitSymmetryCompositionCheck_sound
        orbitSymmetryCompositionCheck_valid).1
  have hcoefficientBound : (orbitEntry row 2).toNat < 995 := by
    apply (Int.toNat_lt hcoefficientBounds.1).mpr
    simpa [coefficientRepresentativeData_size] using hcoefficientBounds.2
  have hsymmetryBound : (orbitEntry row 5).toNat < 64 := by
    apply (Int.toNat_lt hsymmetryBounds.1).mpr
    simpa [hsymmetrySize] using hsymmetryBounds.2
  let coefficient : Fin 995 :=
    ⟨(orbitEntry row 2).toNat, hcoefficientBound⟩
  let symmetry : Fin 64 :=
    ⟨(orbitEntry row 5).toNat, hsymmetryBound⟩
  have hleftEntry : orbitEntry row 0 =
      gramOrbitRepresentativeLeft gram.val := by
    simp [row, gramOrbitRepresentativeLeft, dataEntry, orbitEntry,
      Array.getD_eq_getD_getElem?, hgramIndex]
  have hrightEntry : orbitEntry row 1 =
      gramOrbitRepresentativeRight gram.val := by
    simp [row, gramOrbitRepresentativeRight, dataEntry, orbitEntry,
      Array.getD_eq_getD_getElem?, hgramIndex]
  have hcoefficientEntry : orbitEntry row 2 =
      gramOrbitCoefficientOrbit gram.val := by
    simp [row, gramOrbitCoefficientOrbit, dataEntry, orbitEntry,
      Array.getD_eq_getD_getElem?, hgramIndex]
  have hsemantic := orbitCoefficientTransportPacketCheck_sound
    gram.val row packet hpacket'
  dsimp at hsemantic
  obtain ⟨_, _, hleft, hright, hcoefficient, hsymmetry, _,
    hleftRow, hrightRow, hcoefficientRow, hproduct⟩ := hsemantic
  have hleftIndex : (packet.getD 1 0).toNat =
      (orbitGramRepresentative gram).1.val := by
    rw [hleft, hleftEntry]
    rfl
  have hrightIndex : (packet.getD 2 0).toNat =
      (orbitGramRepresentative gram).2.val := by
    rw [hright, hrightEntry]
    rfl
  have hcoefficientIndex : (packet.getD 3 0).toNat = coefficient.val := by
    rw [hcoefficient]
  have hsymmetryIndex : (packet.getD 4 0).toNat = symmetry.val := by
    rw [hsymmetry]
  rw [hleftIndex] at hleftRow
  rw [hrightIndex] at hrightRow
  rw [hcoefficientIndex] at hcoefficientRow
  rw [hsymmetryIndex] at hproduct
  have htransport := orbitCoefficientTransportPacket_semantics
    (orbitGramRepresentative gram).1 (orbitGramRepresentative gram).2
    coefficient symmetry (packet.getD 5 0)
    (orbitCoefficientPacketRow packet 6)
    (orbitCoefficientPacketRow packet 26)
    (orbitCoefficientPacketRow packet 46)
    hleftRow hrightRow hcoefficientRow hproduct
  simpa [coefficient, hcoefficientEntry] using htransport



theorem orbitGram_coefficientRepresentative_mem (gram : Fin 2256) :
    coefficientRepresentativeElement
        (gramOrbitCoefficientOrbit gram.val).toNat ∈
      MulAction.orbit OrbitSignedSymmetry
        ((orbitBasis (orbitGramRepresentative gram).1)⁻¹ *
          orbitBasis (orbitGramRepresentative gram).2) :=
  orbitGram_coefficientRepresentative_mem_of_transport
    orbitCoefficientTransportPacketsCheck_valid gram

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

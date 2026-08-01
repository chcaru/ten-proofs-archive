


import ConnesRigidity.PropertyTExactCertificateOrbitInvariantWitness
import ConnesRigidity.PropertyTExactCertificateOrbitPairNormalization
import ConnesRigidity.PropertyTExactCertificateOrbitPairWitnessSoundness











namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000



theorem orbitNormalizedPair_mem_representative_orbit
    (basisOrbitIndex : Nat) (second representative : Fin 425)
    (hbasisOrbit : basisOrbitIndex < basisOrbitRepresentativeData.size)
    (hrepresentative : representative.val =
      orbitBasisRepresentative basisOrbitIndex)
    (orbit : Fin 2256)
    (horbit : orbit.val =
      (dataEntry pairOrbitIndexData basisOrbitIndex second.val).toNat) :
    (representative, second) ∈ MulAction.orbit OrbitSignedSymmetry
      (orbitGramRepresentative orbit) := by
  have hsecond : second.val < basisData.size := by
    simp [pairWitnessDataSizes_valid.1]
  have hentry := orbitPairWitnessEntryCheck_sound_full
    basisOrbitIndex second.val
    (orbitPairWitnessEntryCheck_valid
      basisOrbitIndex second.val hbasisOrbit hsecond)
  dsimp at hentry
  obtain ⟨_, _, hrawOrbit, hpacked, _, _, hfirst, hlast⟩ := hentry
  let packed := dataEntry pairOrbitWitnessData basisOrbitIndex second.val
  have hpackedBound : packed.toNat < 128 := by
    have hbound : packed < (128 : Int) := by
      simpa [pairWitnessDataSizes_valid.2.2.1] using hpacked.2
    exact (Int.toNat_lt hpacked.1).mpr hbound
  let symmetry : OrbitSymmetry :=
    ⟨⟨packed.toNat / 2, by omega⟩⟩
  have hleft : (orbitGramRepresentative orbit).1.val =
      (orbitEntry
        (gramOrbitData.getD
          (dataEntry pairOrbitIndexData basisOrbitIndex second.val).toNat #[])
        0).toNat := by
    simp [orbitGramRepresentative, gramOrbitRepresentativeLeft,
      dataEntry, orbitEntry, horbit]
  have hright : (orbitGramRepresentative orbit).2.val =
      (orbitEntry
        (gramOrbitData.getD
          (dataEntry pairOrbitIndexData basisOrbitIndex second.val).toNat #[])
        1).toNat := by
    simp [orbitGramRepresentative, gramOrbitRepresentativeRight,
      dataEntry, orbitEntry, horbit]
  by_cases htranspose : packed.toNat % 2 = 1
  · refine MulAction.mem_orbit_iff.mpr
      ⟨(symmetry, Multiplicative.ofAdd (1 : ZMod 2)), ?_⟩
    apply Prod.ext
    · apply Fin.ext
      change symmetryBasisImage symmetry.index.val
        (orbitGramRepresentative orbit).2.val = representative.val
      rw [hright, hrepresentative]
      simpa [packed, symmetry, htranspose] using hfirst
    · apply Fin.ext
      change symmetryBasisImage symmetry.index.val
        (orbitGramRepresentative orbit).1.val = second.val
      rw [hleft]
      simpa [packed, symmetry, htranspose] using hlast
  · refine MulAction.mem_orbit_iff.mpr
      ⟨(symmetry, Multiplicative.ofAdd (0 : ZMod 2)), ?_⟩
    apply Prod.ext
    · apply Fin.ext
      change symmetryBasisImage symmetry.index.val
        (orbitGramRepresentative orbit).1.val = representative.val
      rw [hleft, hrepresentative]
      simpa [packed, symmetry, htranspose] using hfirst
    · apply Fin.ext
      change symmetryBasisImage symmetry.index.val
        (orbitGramRepresentative orbit).2.val = second.val
      rw [hright]
      simpa [packed, symmetry, htranspose] using hlast



theorem orbitPair_mem_representative_orbit_of_normalization
    (left right representative normalized : Fin 425)
    (transport : OrbitSymmetry)
    (hrepresentative : representative.val =
      orbitBasisRepresentative (basisOrbit left.val))
    (hnormalized : normalized.val =
      normalizedPairRight left.val right.val)
    (hleft : transport • representative = left)
    (hright : transport • normalized = right) :
    (left, right) ∈ MulAction.orbit OrbitSignedSymmetry
      (orbitGramRepresentative (orbitPairKey left right)) := by
  have hbasisOrbit : basisOrbit left.val <
      basisOrbitRepresentativeData.size := by
    simpa [pairWitnessDataSizes_valid.2.2.2.2.1] using
      (orbitBasisTransportIndices_lt left).1
  have hkey : (orbitPairKey left right).val =
      (dataEntry pairOrbitIndexData
        (basisOrbit left.val) normalized.val).toNat := by
    simp [pairOrbit, hnormalized]
  have hnormalizedOrbit := orbitNormalizedPair_mem_representative_orbit
    (basisOrbit left.val) normalized representative
    hbasisOrbit hrepresentative (orbitPairKey left right) hkey
  obtain ⟨witness, hwitness⟩ :=
    MulAction.mem_orbit_iff.mp hnormalizedOrbit
  refine MulAction.mem_orbit_iff.mpr
    ⟨(transport, Multiplicative.ofAdd (0 : ZMod 2)) * witness, ?_⟩
  rw [mul_smul, hwitness]
  change (transport • representative, transport • normalized) = (left, right)
  exact Prod.ext hleft hright



theorem orbitPair_mem_representative_orbit (left right : Fin 425) :
    (left, right) ∈ MulAction.orbit OrbitSignedSymmetry
      (orbitGramRepresentative (orbitPairKey left right)) := by
  apply orbitPair_mem_representative_orbit_of_normalization
    left right (orbitBasisRepresentativeFin left)
    (orbitNormalizedRightFin left right)
    (orbitBasisTransportSymmetry left)
  · rfl
  · rfl
  · exact orbitBasisTransportSymmetry_smul_representative left
  · exact orbitBasisTransportSymmetry_smul_normalizedRight left right

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

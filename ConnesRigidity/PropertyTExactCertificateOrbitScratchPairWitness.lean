import ConnesRigidity.PropertyTExactCertificateOrbitInvariantWitness
import ConnesRigidity.PropertyTExactCertificateOrbitCheckerSoundness

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

theorem scratch_pair_mem_signed_orbit_of_transports
    [MulAction OrbitSymmetry (Fin 425)]
    (left right normalizedLeft normalizedRight i j : Fin 425)
    (symmetry transporter : OrbitSymmetry)
    (hwitness :
      (symmetry • left = normalizedLeft ∧
        symmetry • right = normalizedRight) ∨
      (symmetry • right = normalizedLeft ∧
        symmetry • left = normalizedRight))
    (hleft : transporter • normalizedLeft = i)
    (hright : transporter • normalizedRight = j) :
    (i, j) ∈ MulAction.orbit OrbitSignedSymmetry (left, right) := by
  rcases hwitness with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · refine ⟨(transporter * symmetry, Multiplicative.ofAdd (0 : ZMod 2)), ?_⟩
    change
      signedPairAction
        (transporter * symmetry, Multiplicative.ofAdd (0 : ZMod 2))
        (left, right) = (i, j)
    simp [signedPairAction, mul_smul, hfirst, hsecond, hleft, hright]
  · refine ⟨(transporter * symmetry, Multiplicative.ofAdd (1 : ZMod 2)), ?_⟩
    change
      signedPairAction
        (transporter * symmetry, Multiplicative.ofAdd (1 : ZMod 2))
        (left, right) = (i, j)
    simp [signedPairAction, mul_smul, hfirst, hsecond, hleft, hright]

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

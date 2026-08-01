


import ConnesRigidity.PropertyTExactCertificateOrbitPairKeyBound









namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section


theorem orbitBasisRepresentativeIndex_lt (orbit : Nat) (horbit : orbit < 26) :
    orbitBasisRepresentative orbit < 425 := by
  have hcheck :
      (List.range 26).all
        (fun index => decide (orbitBasisRepresentative index < 425)) = true := by
    decide +kernel
  exact of_decide_eq_true
    (List.all_eq_true.mp hcheck orbit (List.mem_range.mpr horbit))


noncomputable def orbitBasisTransportSymmetry (index : Fin 425) : OrbitSymmetry :=
  ⟨⟨basisTransportSymmetry index.val,
    (orbitBasisTransportIndices_lt index).2⟩⟩


noncomputable def orbitBasisRepresentativeFin (index : Fin 425) : Fin 425 :=
  ⟨orbitBasisRepresentative (basisOrbit index.val),
    orbitBasisRepresentativeIndex_lt (basisOrbit index.val)
      (orbitBasisTransportIndices_lt index).1⟩


noncomputable def orbitNormalizedRightFin
    (left right : Fin 425) : Fin 425 :=
  ⟨normalizedPairRight left.val right.val,
    normalizedPairRight_lt left right⟩

@[simp] theorem orbitBasisTransportSymmetry_index_val (index : Fin 425) :
    (orbitBasisTransportSymmetry index).index.val =
      basisTransportSymmetry index.val := rfl

@[simp] theorem orbitBasisRepresentativeFin_val (index : Fin 425) :
    (orbitBasisRepresentativeFin index).val =
      orbitBasisRepresentative (basisOrbit index.val) := rfl

@[simp] theorem orbitNormalizedRightFin_val
    (left right : Fin 425) :
    (orbitNormalizedRightFin left right).val =
      normalizedPairRight left.val right.val := rfl



theorem orbitBasisTransportSymmetry_smul_representative
    (index : Fin 425) :
    orbitBasisTransportSymmetry index •
      orbitBasisRepresentativeFin index = index := by
  have hcheck := orbitBasisTransportCheck_sound orbitBasisTransportCheck_valid
  have hindex : index.val < basisTransporterData.size := by
    rw [hcheck.1, orbitBasisData_size]
    exact index.isLt
  have hrow : basisTransporterData[index.val]? =
      some basisTransporterData[index.val] := by
    simp [hindex]
  have hvalid := orbitBasisTransportRowCheck_sound index.val
    basisTransporterData[index.val] hrow (hcheck.2 index.val hindex)
  have horbit : basisOrbit index.val =
      (orbitEntry basisTransporterData[index.val] 0).toNat := by
    simp [basisOrbit, dataEntry, Array.getD_eq_getD_getElem?,
      orbitEntry, hindex]
  have hsymmetry : basisTransportSymmetry index.val =
      (orbitEntry basisTransporterData[index.val] 1).toNat := by
    simp [basisTransportSymmetry, dataEntry,
      Array.getD_eq_getD_getElem?, orbitEntry, hindex]
  apply Fin.ext
  change
    symmetryBasisImage (basisTransportSymmetry index.val)
      (orbitBasisRepresentative (basisOrbit index.val)) = index.val
  simpa [horbit, hsymmetry] using hvalid.2.2.2


theorem orbitBasisTransportSymmetry_inv_smul_left (index : Fin 425) :
    (orbitBasisTransportSymmetry index)⁻¹ • index =
      orbitBasisRepresentativeFin index := by
  calc
    (orbitBasisTransportSymmetry index)⁻¹ • index =
        (orbitBasisTransportSymmetry index)⁻¹ •
          (orbitBasisTransportSymmetry index •
            orbitBasisRepresentativeFin index) :=
      congrArg (fun value : Fin 425 =>
        (orbitBasisTransportSymmetry index)⁻¹ • value)
        (orbitBasisTransportSymmetry_smul_representative index).symm
    _ = orbitBasisRepresentativeFin index :=
      inv_smul_smul (orbitBasisTransportSymmetry index)
        (orbitBasisRepresentativeFin index)


theorem orbitBasisTransportSymmetry_inv_smul_right
    (left right : Fin 425) :
    (orbitBasisTransportSymmetry left)⁻¹ • right =
      orbitNormalizedRightFin left right := by
  apply Fin.ext
  simp [normalizedPairRight]



theorem orbitBasisTransportSymmetry_smul_normalizedRight
    (left right : Fin 425) :
    orbitBasisTransportSymmetry left •
      orbitNormalizedRightFin left right = right := by
  rw [← orbitBasisTransportSymmetry_inv_smul_right left right]
  simp

end

end ConnesRigidity.AffineSymplecticOrbitCertificate

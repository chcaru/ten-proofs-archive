


import ConnesRigidity.PropertyTExactCertificateOrbitBasis









namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

local instance generatorEnumerationDecidableEq :
    DecidableEq constructedGammaZeroGroup :=
  fun x y =>
    decidable_of_iff (x.fst = y.fst ∧ x.snd = y.snd)
      ⟨fun h => by
          cases x
          cases y
          simp_all,
        fun h =>
          ⟨congrArg CocycleExtension.fst h,
            congrArg CocycleExtension.snd h⟩⟩


theorem generatorElement_mem (i : Nat) (hi : i < generatorData.size) :
    generatorElement i ∈ generatorElements := by
  apply List.mem_map.mpr
  refine ⟨generatorData[i]'hi,
    Array.mem_toList_iff.mpr (Array.getElem_mem hi), ?_⟩
  simp [generatorElement, Array.getD, hi]


theorem exists_generatorElement_of_mem {g : constructedGammaZeroGroup}
    (hg : g ∈ generatorElements) :
    ∃ i, i < generatorData.size ∧ generatorElement i = g := by
  obtain ⟨row, hrow, hdecode⟩ := List.mem_map.mp hg
  obtain ⟨i, hi, hrowi⟩ :=
    Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hrow)
  refine ⟨i, hi, ?_⟩
  simpa [generatorElement, Array.getD, hi, hrowi] using hdecode



theorem generatorElements_nodup : generatorElements.Nodup := by
  unfold generatorElements generatorData
  decide +kernel



private theorem generatorElements_explicit : generatorElements =
    [gammaZeroQuotientLift symplecticRootD12,
      gammaZeroQuotientLift symplecticRootD21,
      gammaZeroQuotientLift transvectionF1,
      gammaZeroQuotientLift transvectionF2,
      gammaZeroQuotientLift lowerCrossTransvection,
      gammaZeroQuotientLift upperTransvectionE1,
      gammaZeroQuotientLift upperTransvectionE2,
      gammaZeroQuotientLift upperCrossTransvection,
      (gammaZeroQuotientLift symplecticRootD12)⁻¹,
      (gammaZeroQuotientLift symplecticRootD21)⁻¹,
      (gammaZeroQuotientLift transvectionF1)⁻¹,
      (gammaZeroQuotientLift transvectionF2)⁻¹,
      (gammaZeroQuotientLift lowerCrossTransvection)⁻¹,
      (gammaZeroQuotientLift upperTransvectionE1)⁻¹,
      (gammaZeroQuotientLift upperTransvectionE2)⁻¹,
      (gammaZeroQuotientLift upperCrossTransvection)⁻¹,
      (gammaZeroBasisTranslation (Sum.inl 0))⁻¹,
      gammaZeroBasisTranslation (Sum.inl 0),
      (gammaZeroBasisTranslation (Sum.inl 1))⁻¹,
      gammaZeroBasisTranslation (Sum.inl 1),
      (gammaZeroBasisTranslation (Sum.inr 0))⁻¹,
      gammaZeroBasisTranslation (Sum.inr 0),
      (gammaZeroBasisTranslation (Sum.inr 1))⁻¹,
      gammaZeroBasisTranslation (Sum.inr 1)] := by
  unfold generatorElements generatorData
  decide +kernel



theorem generatorElements_toFinset_eq :
    generatorElements.toFinset = gammaZeroElementaryGenerators := by
  rw [generatorElements_explicit]
  ext g
  simp [gammaZeroElementaryGenerators,
    positiveElementarySymplecticGeneratorList]; aesop



theorem gammaZeroElementaryGenerators_card :
    gammaZeroElementaryGenerators.card = 24 := by
  rw [← generatorElements_toFinset_eq,
    List.toFinset_card_of_nodup generatorElements_nodup]
  unfold generatorElements generatorData
  decide +kernel


theorem generatorData_size : generatorData.size = 24 := by
  unfold generatorData
  decide +kernel



theorem generatorData_basisData_prefix (i : Nat) (hi : i < 24) :
    generatorData.getD i #[] = basisData.getD (i + 1) #[] := by
  interval_cases i <;>
    unfold generatorData basisData <;>
    rfl



theorem generatorElement_eq_orbitBasis (i : Fin 24) :
    generatorElement i.val = orbitBasis ⟨i.val + 1, by omega⟩ := by
  simp only [generatorElement, orbitBasis, basisElement,
    generatorData_basisData_prefix i.val i.isLt]



theorem orbitBasis_zero : orbitBasis (0 : Fin 425) = 1 := by
  unfold orbitBasis basisElement basisData
  decide +kernel



theorem generator_mem_orbitBasis
    (g : constructedGammaZeroGroup)
    (hg : g ∈ gammaZeroElementaryGenerators) :
    ∃ i : Fin 425, orbitBasis i = g := by
  have hlist : g ∈ generatorElements := by
    apply List.mem_toFinset.mp
    rw [generatorElements_toFinset_eq]
    exact hg
  obtain ⟨i, hi, heq⟩ := exists_generatorElement_of_mem hlist
  have hi24 : i < 24 := by
    rw [← generatorData_size]
    exact hi
  refine ⟨⟨i + 1, by omega⟩, ?_⟩
  exact (generatorElement_eq_orbitBasis ⟨i, hi24⟩).symm.trans heq

end ConnesRigidity.AffineSymplecticOrbitCertificate

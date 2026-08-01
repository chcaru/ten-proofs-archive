
import ConnesRigidity.PropertyTExactCertificate
import ConnesRigidity.GammaZeroGenerators

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

local instance gammaZeroDecidableEq :
    DecidableEq IntegralSymplecticCocycleInput.GammaZero :=
  fun x y =>
    decidable_of_iff (x.fst = y.fst ∧ x.snd = y.snd)
      ⟨fun h ↦ by cases x; cases y; simp_all,
       fun h ↦ ⟨congrArg CocycleExtension.fst h,
         congrArg CocycleExtension.snd h⟩⟩

set_option maxHeartbeats 0 in

private theorem generator_checks :
    (generatorData.map gammaZeroOfData).Nodup ∧
    generators.card = 24 ∧
    generators.image Inv.inv = generators ∧
    (∀ i : SymplecticIndex,
      gammaZeroBasisTranslation i ∈ generators) ∧
    gammaZeroQuotientLift upperTransvectionE1 ∈ generators ∧
    gammaZeroQuotientLift upperTransvectionE2 ∈ generators ∧
    gammaZeroQuotientLift upperCrossTransvection ∈ generators ∧
    gammaZeroQuotientLift transvectionF1 ∈ generators ∧
    gammaZeroQuotientLift transvectionF2 ∈ generators ∧
    gammaZeroQuotientLift lowerCrossTransvection ∈ generators ∧
    gammaZeroQuotientLift symplecticRootD12 ∈ generators ∧
    gammaZeroQuotientLift symplecticRootD21 ∈ generators := by
  decide +kernel

theorem basisElement_zero : basisElement 0 = 1 :=
  basisElement_zero_check

theorem basisElement_generatorList :
    (List.range 24).map (fun i ↦ basisElement (i + 1)) =
      generatorData.map gammaZeroOfData :=
  basisElement_generatorList_check

theorem generatorList_nodup :
    (generatorData.map gammaZeroOfData).Nodup :=
  generator_checks.1

theorem generators_card : generators.card = 24 :=
  generator_checks.2.1

theorem generators_inverse_closed :
    generators.image Inv.inv = generators :=
  generator_checks.2.2.1

theorem positiveSymplecticGenerators_mem :
    ∀ g ∈ positiveElementarySymplecticGeneratorList,
      gammaZeroQuotientLift g ∈ generators := by
  intro g hg
  simp only [positiveElementarySymplecticGeneratorList,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact generator_checks.2.2.2.2.1
  · exact generator_checks.2.2.2.2.2.1
  · exact generator_checks.2.2.2.2.2.2.1
  · exact generator_checks.2.2.2.2.2.2.2.1
  · exact generator_checks.2.2.2.2.2.2.2.2.1
  · exact generator_checks.2.2.2.2.2.2.2.2.2.1
  · exact generator_checks.2.2.2.2.2.2.2.2.2.2.1
  · exact generator_checks.2.2.2.2.2.2.2.2.2.2.2

theorem basisTranslations_mem :
    ∀ i : SymplecticIndex,
      gammaZeroBasisTranslation i ∈ generators :=
  generator_checks.2.2.2.1

end AffineSymplecticCertificate

end ConnesRigidity

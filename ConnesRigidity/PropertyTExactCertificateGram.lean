


import ConnesRigidity.PropertyTExactCertificateGramChecks
import ConnesRigidity.PropertyTExactCertificateGramColumnChecks
import ConnesRigidity.PropertyTExactCertificateGramSoundness
import ConnesRigidity.PropertyTExactCertificateData










namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in

private theorem gramCheckFactorData_length :
    GramCheckData.factorData.length = 424 := by
  unfold GramCheckData.factorData
  decide +kernel

private theorem gramCheckFullGram_valid :
    ∀ i j : Fin 425,
      GramCheckData.fullGramCoefficient i j =
        (GramCheckData.factorData.map fun row ↦
          GramCheckData.fullFactorCoefficient row i *
            GramCheckData.fullFactorCoefficient row j).sum :=
  fullGram_valid_of_encoding_checks gramCheckFactorData_length
    allFactorColumnChunkChecks allFactorRowEncodingChecks
    allFullGramRowEncodingChecks

private theorem gramCheckFactorData_eq :
    GramCheckData.factorData = factorData := by
  unfold GramCheckData.factorData factorData
  rfl

private theorem gramCheckFullGramData_eq :
    GramCheckData.fullGramData = fullGramData := by
  unfold GramCheckData.fullGramData fullGramData
  rfl


theorem fullGramDataRow_length (i : Fin 425) :
    (fullGramData.getD i []).length = 425 := by
  rw [← gramCheckFullGramData_eq]
  exact
    fullGramDataRow_length_of_encoding_checks
      allFullGramRowEncodingChecks i



theorem fullGram_valid :
    ∀ i j : Fin 425,
      fullGramCoefficient i j =
        (factorData.map fun row ↦
          fullFactorCoefficient row i *
            fullFactorCoefficient row j).sum := by
  intro i j
  simpa only [GramCheckData.fullGramCoefficient, fullGramCoefficient,
    gramCheckFullGramData_eq, gramCheckFactorData_eq,
    GramCheckData.fullFactorCoefficient, fullFactorCoefficient] using
    gramCheckFullGram_valid i j

end AffineSymplecticCertificate

end ConnesRigidity

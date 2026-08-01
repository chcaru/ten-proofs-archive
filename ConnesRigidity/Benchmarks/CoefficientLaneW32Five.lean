
import ConnesRigidity.Benchmarks.CoefficientLaneBase
import ConnesRigidity.CertificateLiterals.Benchmarks.CoefficientLaneW32Five.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def benchmarkFactorFiveW32Expected :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.Benchmarks.CoefficientLaneW32Five.Entry000.data

set_option maxHeartbeats 0 in

theorem benchmarkFactorFiveW32 :
    coefficientLaneCheckData 32 32
        benchmarkFactorRows260To264Terms =
      (benchmarkFactorFiveW32Expected, 419653985822832) := by
  unfold coefficientLaneCheckData
    benchmarkFactorRows260To264Terms
    benchmarkFactorFiveW32Expected
  unfold coefficientFactorTermRowData
    productIndexDataRow260
    productIndexDataRow261
    productIndexDataRow262
    productIndexDataRow263
    productIndexDataRow264
    coefficientFullGramDataRow260
    coefficientFullGramDataRow261
    coefficientFullGramDataRow262
    coefficientFullGramDataRow263
    coefficientFullGramDataRow264
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

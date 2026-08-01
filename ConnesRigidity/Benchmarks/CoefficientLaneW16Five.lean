
import ConnesRigidity.Benchmarks.CoefficientLaneBase
import ConnesRigidity.CertificateLiterals.Benchmarks.CoefficientLaneW16Five.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def benchmarkFactorFiveW16Expected :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.Benchmarks.CoefficientLaneW16Five.Entry000.data

set_option maxHeartbeats 0 in

theorem benchmarkFactorFiveW16 :
    coefficientLaneCheckData 16 63
        benchmarkFactorRows260To264Terms =
      (benchmarkFactorFiveW16Expected, 419653985822832) := by
  unfold coefficientLaneCheckData
    benchmarkFactorRows260To264Terms
    benchmarkFactorFiveW16Expected
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

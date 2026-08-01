


import ConnesRigidity.Benchmarks.CoefficientLaneBase
import ConnesRigidity.CertificateLiterals.Benchmarks.CoefficientLaneW32One.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def benchmarkFactorOneW32Expected :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.Benchmarks.CoefficientLaneW32One.Entry000.data

set_option maxHeartbeats 0 in

theorem benchmarkFactorOneW32 :
    coefficientLaneCheckData 32 32 benchmarkFactorRow260Terms =
      (benchmarkFactorOneW32Expected, 56795282410528) := by
  unfold coefficientLaneCheckData benchmarkFactorRow260Terms
    benchmarkFactorOneW32Expected
  unfold coefficientFactorTermRowData productIndexDataRow260
    coefficientFullGramDataRow260
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

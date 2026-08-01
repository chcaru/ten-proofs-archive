


import ConnesRigidity.Benchmarks.CoefficientLaneBase
import ConnesRigidity.CertificateLiterals.Benchmarks.CoefficientLaneW16One.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def benchmarkFactorOneW16Expected :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.Benchmarks.CoefficientLaneW16One.Entry000.data

set_option maxHeartbeats 0 in

theorem benchmarkFactorOneW16 :
    coefficientLaneCheckData 16 63 benchmarkFactorRow260Terms =
      (benchmarkFactorOneW16Expected, 56795282410528) := by
  unfold coefficientLaneCheckData benchmarkFactorRow260Terms
    benchmarkFactorOneW16Expected
  unfold coefficientFactorTermRowData productIndexDataRow260
    coefficientFullGramDataRow260
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity


import ConnesRigidity.Benchmarks.EdgeRadixCheckBase
import ConnesRigidity.CertificateLiterals.Benchmarks.PositiveEdgeRadixCheck.Entry000
import ConnesRigidity.CertificateLiterals.Benchmarks.PositiveEdgeRadixCheck.Entry001

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def benchmarkPositiveEdgeRadixPackets :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.Benchmarks.PositiveEdgeRadixCheck.Entry000.data

@[irreducible] noncomputable def benchmarkPositiveEdgeRadixExpected :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.Benchmarks.PositiveEdgeRadixCheck.Entry001.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem benchmarkPositiveEdgeRadixCheck :
    benchmarkEdgeCoefficientCheckData
        (coefficientPositivePacketsTerms
          benchmarkPositiveEdgeRadixPackets) =
      (benchmarkPositiveEdgeRadixExpected, 8514698112) := by
  unfold benchmarkEdgeCoefficientCheckData
    coefficientPositivePacketsTerms
    coefficientPositivePacketTerms
    coefficientPositiveDecodedPacketTerms
    decodeCoefficientPositivePacket
    coefficientEdgeTerm
    benchmarkPositiveEdgeRadixPackets
    benchmarkPositiveEdgeRadixExpected
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

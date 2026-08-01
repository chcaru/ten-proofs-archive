
import ConnesRigidity.Benchmarks.EdgeRadixCheckBase
import ConnesRigidity.CertificateLiterals.Benchmarks.NegativeEdgeRadixCheck.Entry000
import ConnesRigidity.CertificateLiterals.Benchmarks.NegativeEdgeRadixCheck.Entry001

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def benchmarkNegativeEdgeRadixPackets :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.Benchmarks.NegativeEdgeRadixCheck.Entry000.data

@[irreducible] noncomputable def benchmarkNegativeEdgeRadixExpected :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.Benchmarks.NegativeEdgeRadixCheck.Entry001.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem benchmarkNegativeEdgeRadixCheck :
    benchmarkEdgeCoefficientCheckData
        (coefficientNegativePacketsTerms
          benchmarkNegativeEdgeRadixPackets) =
      (benchmarkNegativeEdgeRadixExpected, 19054328576) := by
  unfold benchmarkEdgeCoefficientCheckData
    coefficientNegativePacketsTerms
    coefficientNegativePacketTerms
    coefficientNegativeDecodedPacketTerms
    decodeCoefficientNegativePacket
    coefficientEdgeTerm
    benchmarkNegativeEdgeRadixPackets
    benchmarkNegativeEdgeRadixExpected
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

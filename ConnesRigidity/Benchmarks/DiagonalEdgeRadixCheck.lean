
import ConnesRigidity.Benchmarks.EdgeRadixCheckBase
import ConnesRigidity.CertificateLiterals.Benchmarks.DiagonalEdgeRadixCheck.Entry000
import ConnesRigidity.CertificateLiterals.Benchmarks.DiagonalEdgeRadixCheck.Entry001

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def benchmarkDiagonalEdgeRadixPackets :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.Benchmarks.DiagonalEdgeRadixCheck.Entry000.data

@[irreducible] noncomputable def benchmarkDiagonalEdgeRadixExpected :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.Benchmarks.DiagonalEdgeRadixCheck.Entry001.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem benchmarkDiagonalEdgeRadixCheck :
    benchmarkEdgeCoefficientCheckData
        (coefficientDiagonalPacketsTerms
          benchmarkDiagonalEdgeRadixPackets) =
      (benchmarkDiagonalEdgeRadixExpected, 10027690853664) := by
  unfold benchmarkEdgeCoefficientCheckData
    coefficientDiagonalPacketsTerms
    coefficientDiagonalPacketTerms
    coefficientDiagonalDecodedPacketTerms
    decodeCoefficientDiagonalPacket
    coefficientEdgeTerm
    benchmarkDiagonalEdgeRadixPackets
    benchmarkDiagonalEdgeRadixExpected
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

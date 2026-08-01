


import ConnesRigidity.Benchmarks.PositiveEdgeDirectBase
import ConnesRigidity.CertificateLiterals.Benchmarks.PositiveEdgeDirectCheck.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

@[irreducible] noncomputable def benchmarkPositiveEdgeLaneExpected32 :
    List (List Int) :=
  (ConnesRigidity.CertificateLiterals.Benchmarks.PositiveEdgeDirectCheck.Entry000.data) ++
    List.replicate 69 (List.replicate 63 0)

set_option maxHeartbeats 0 in



theorem benchmarkDirectPositiveEdgeLane32 :
    benchmarkPositiveLaneCheckData benchmarkDirectPositiveTerms32 =
      (benchmarkPositiveEdgeLaneExpected32, 4835629568) := by
  unfold benchmarkPositiveLaneCheckData benchmarkDirectPositiveTerms32
    benchmarkPositivePacketTerms benchmarkPositiveEdgePackets32
    benchmarkPositiveEdgeLaneExpected32
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive103
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_103 :
    coefficientPositivePacketTerms103 =
      (positiveEdgeTerms.drop 59328).take 576 := by
  unfold coefficientPositivePacketTerms103 coefficientPositivePacketRows103
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

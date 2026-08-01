
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive244
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_244 :
    coefficientPositivePacketTerms244 =
      (positiveEdgeTerms.drop 140544).take 576 := by
  unfold coefficientPositivePacketTerms244 coefficientPositivePacketRows244
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

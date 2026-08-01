
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive122
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_122 :
    coefficientPositivePacketTerms122 =
      (positiveEdgeTerms.drop 70272).take 576 := by
  unfold coefficientPositivePacketTerms122 coefficientPositivePacketRows122
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

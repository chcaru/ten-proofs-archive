
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive184
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_184 :
    coefficientPositivePacketTerms184 =
      (positiveEdgeTerms.drop 105984).take 576 := by
  unfold coefficientPositivePacketTerms184 coefficientPositivePacketRows184
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

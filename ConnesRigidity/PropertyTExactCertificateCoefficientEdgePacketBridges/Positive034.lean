
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive034
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_034 :
    coefficientPositivePacketTerms034 =
      (positiveEdgeTerms.drop 19584).take 576 := by
  unfold coefficientPositivePacketTerms034 coefficientPositivePacketRows034
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

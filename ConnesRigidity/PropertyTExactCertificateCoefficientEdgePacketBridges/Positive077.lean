
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive077
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_077 :
    coefficientPositivePacketTerms077 =
      (positiveEdgeTerms.drop 44352).take 576 := by
  unfold coefficientPositivePacketTerms077 coefficientPositivePacketRows077
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

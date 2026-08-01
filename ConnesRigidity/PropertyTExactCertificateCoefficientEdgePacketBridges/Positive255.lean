
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive255
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_255 :
    coefficientPositivePacketTerms255 =
      (positiveEdgeTerms.drop 146880).take 576 := by
  unfold coefficientPositivePacketTerms255 coefficientPositivePacketRows255
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

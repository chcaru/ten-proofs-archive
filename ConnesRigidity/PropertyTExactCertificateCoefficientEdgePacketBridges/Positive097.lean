
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive097
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_097 :
    coefficientPositivePacketTerms097 =
      (positiveEdgeTerms.drop 55872).take 576 := by
  unfold coefficientPositivePacketTerms097 coefficientPositivePacketRows097
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive208
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_208 :
    coefficientPositivePacketTerms208 =
      (positiveEdgeTerms.drop 119808).take 576 := by
  unfold coefficientPositivePacketTerms208 coefficientPositivePacketRows208
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

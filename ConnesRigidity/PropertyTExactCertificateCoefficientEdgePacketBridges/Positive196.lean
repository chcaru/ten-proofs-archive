
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive196
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_196 :
    coefficientPositivePacketTerms196 =
      (positiveEdgeTerms.drop 112896).take 576 := by
  unfold coefficientPositivePacketTerms196 coefficientPositivePacketRows196
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

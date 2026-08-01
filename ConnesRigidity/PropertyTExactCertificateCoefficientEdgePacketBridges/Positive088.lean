
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive088
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_088 :
    coefficientPositivePacketTerms088 =
      (positiveEdgeTerms.drop 50688).take 576 := by
  unfold coefficientPositivePacketTerms088 coefficientPositivePacketRows088
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

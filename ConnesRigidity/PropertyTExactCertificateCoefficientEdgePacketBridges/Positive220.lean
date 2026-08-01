
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive220
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_220 :
    coefficientPositivePacketTerms220 =
      (positiveEdgeTerms.drop 126720).take 576 := by
  unfold coefficientPositivePacketTerms220 coefficientPositivePacketRows220
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

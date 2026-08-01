
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive009
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_009 :
    coefficientPositivePacketTerms009 =
      (positiveEdgeTerms.drop 5184).take 576 := by
  unfold coefficientPositivePacketTerms009 coefficientPositivePacketRows009
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

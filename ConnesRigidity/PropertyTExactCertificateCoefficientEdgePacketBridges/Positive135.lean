
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive135
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_135 :
    coefficientPositivePacketTerms135 =
      (positiveEdgeTerms.drop 77760).take 576 := by
  unfold coefficientPositivePacketTerms135 coefficientPositivePacketRows135
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

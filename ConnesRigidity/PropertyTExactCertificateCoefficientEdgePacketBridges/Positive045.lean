
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive045
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_045 :
    coefficientPositivePacketTerms045 =
      (positiveEdgeTerms.drop 25920).take 576 := by
  unfold coefficientPositivePacketTerms045 coefficientPositivePacketRows045
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

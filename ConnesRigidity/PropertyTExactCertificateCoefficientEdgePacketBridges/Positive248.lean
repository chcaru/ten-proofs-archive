
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive248
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_248 :
    coefficientPositivePacketTerms248 =
      (positiveEdgeTerms.drop 142848).take 576 := by
  unfold coefficientPositivePacketTerms248 coefficientPositivePacketRows248
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

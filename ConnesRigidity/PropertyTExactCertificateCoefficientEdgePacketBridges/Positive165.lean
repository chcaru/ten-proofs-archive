
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive165
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_165 :
    coefficientPositivePacketTerms165 =
      (positiveEdgeTerms.drop 95040).take 576 := by
  unfold coefficientPositivePacketTerms165 coefficientPositivePacketRows165
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

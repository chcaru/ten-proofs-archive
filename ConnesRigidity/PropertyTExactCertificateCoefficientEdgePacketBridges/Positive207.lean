
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive207
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_207 :
    coefficientPositivePacketTerms207 =
      (positiveEdgeTerms.drop 119232).take 576 := by
  unfold coefficientPositivePacketTerms207 coefficientPositivePacketRows207
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

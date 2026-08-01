
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive182
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_182 :
    coefficientPositivePacketTerms182 =
      (positiveEdgeTerms.drop 104832).take 576 := by
  unfold coefficientPositivePacketTerms182 coefficientPositivePacketRows182
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

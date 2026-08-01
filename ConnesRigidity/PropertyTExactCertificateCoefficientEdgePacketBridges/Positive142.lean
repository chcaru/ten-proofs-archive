
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive142
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_142 :
    coefficientPositivePacketTerms142 =
      (positiveEdgeTerms.drop 81792).take 576 := by
  unfold coefficientPositivePacketTerms142 coefficientPositivePacketRows142
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

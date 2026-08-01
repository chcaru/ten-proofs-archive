
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive087
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_087 :
    coefficientPositivePacketTerms087 =
      (positiveEdgeTerms.drop 50112).take 576 := by
  unfold coefficientPositivePacketTerms087 coefficientPositivePacketRows087
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive041
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_041 :
    coefficientPositivePacketTerms041 =
      (positiveEdgeTerms.drop 23616).take 576 := by
  unfold coefficientPositivePacketTerms041 coefficientPositivePacketRows041
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

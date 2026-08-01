
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive070
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_070 :
    coefficientPositivePacketTerms070 =
      (positiveEdgeTerms.drop 40320).take 576 := by
  unfold coefficientPositivePacketTerms070 coefficientPositivePacketRows070
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive205
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_205 :
    coefficientPositivePacketTerms205 =
      (positiveEdgeTerms.drop 118080).take 576 := by
  unfold coefficientPositivePacketTerms205 coefficientPositivePacketRows205
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

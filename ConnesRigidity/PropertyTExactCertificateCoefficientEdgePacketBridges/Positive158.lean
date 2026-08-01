
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive158
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_158 :
    coefficientPositivePacketTerms158 =
      (positiveEdgeTerms.drop 91008).take 576 := by
  unfold coefficientPositivePacketTerms158 coefficientPositivePacketRows158
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive241
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_241 :
    coefficientPositivePacketTerms241 =
      (positiveEdgeTerms.drop 138816).take 576 := by
  unfold coefficientPositivePacketTerms241 coefficientPositivePacketRows241
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

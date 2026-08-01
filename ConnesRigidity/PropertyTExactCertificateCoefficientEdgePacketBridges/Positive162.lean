
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive162
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_162 :
    coefficientPositivePacketTerms162 =
      (positiveEdgeTerms.drop 93312).take 576 := by
  unfold coefficientPositivePacketTerms162 coefficientPositivePacketRows162
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

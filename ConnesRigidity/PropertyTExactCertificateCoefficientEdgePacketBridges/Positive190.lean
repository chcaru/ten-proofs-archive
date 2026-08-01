
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive190
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_190 :
    coefficientPositivePacketTerms190 =
      (positiveEdgeTerms.drop 109440).take 576 := by
  unfold coefficientPositivePacketTerms190 coefficientPositivePacketRows190
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

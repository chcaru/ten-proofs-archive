
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive258
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_258 :
    coefficientPositivePacketTerms258 =
      (positiveEdgeTerms.drop 148608).take 576 := by
  unfold coefficientPositivePacketTerms258 coefficientPositivePacketRows258
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

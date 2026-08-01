
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive018
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_018 :
    coefficientPositivePacketTerms018 =
      (positiveEdgeTerms.drop 10368).take 576 := by
  unfold coefficientPositivePacketTerms018 coefficientPositivePacketRows018
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

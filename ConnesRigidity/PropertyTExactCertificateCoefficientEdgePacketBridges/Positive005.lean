
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive005
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_005 :
    coefficientPositivePacketTerms005 =
      (positiveEdgeTerms.drop 2880).take 576 := by
  unfold coefficientPositivePacketTerms005 coefficientPositivePacketRows005
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

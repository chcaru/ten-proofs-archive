
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive002
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_002 :
    coefficientPositivePacketTerms002 =
      (positiveEdgeTerms.drop 1152).take 576 := by
  unfold coefficientPositivePacketTerms002 coefficientPositivePacketRows002
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

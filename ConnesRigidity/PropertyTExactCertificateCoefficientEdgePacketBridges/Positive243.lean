
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive243
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_243 :
    coefficientPositivePacketTerms243 =
      (positiveEdgeTerms.drop 139968).take 576 := by
  unfold coefficientPositivePacketTerms243 coefficientPositivePacketRows243
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

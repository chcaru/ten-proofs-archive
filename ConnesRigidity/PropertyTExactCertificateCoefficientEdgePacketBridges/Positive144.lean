
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive144
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_144 :
    coefficientPositivePacketTerms144 =
      (positiveEdgeTerms.drop 82944).take 576 := by
  unfold coefficientPositivePacketTerms144 coefficientPositivePacketRows144
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

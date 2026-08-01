
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive136
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_136 :
    coefficientPositivePacketTerms136 =
      (positiveEdgeTerms.drop 78336).take 576 := by
  unfold coefficientPositivePacketTerms136 coefficientPositivePacketRows136
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive023
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_023 :
    coefficientPositivePacketTerms023 =
      (positiveEdgeTerms.drop 13248).take 576 := by
  unfold coefficientPositivePacketTerms023 coefficientPositivePacketRows023
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive107
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_107 :
    coefficientPositivePacketTerms107 =
      (positiveEdgeTerms.drop 61632).take 576 := by
  unfold coefficientPositivePacketTerms107 coefficientPositivePacketRows107
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

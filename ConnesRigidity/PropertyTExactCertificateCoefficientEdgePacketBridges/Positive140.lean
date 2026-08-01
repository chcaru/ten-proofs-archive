
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive140
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_140 :
    coefficientPositivePacketTerms140 =
      (positiveEdgeTerms.drop 80640).take 576 := by
  unfold coefficientPositivePacketTerms140 coefficientPositivePacketRows140
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive026
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_026 :
    coefficientPositivePacketTerms026 =
      (positiveEdgeTerms.drop 14976).take 576 := by
  unfold coefficientPositivePacketTerms026 coefficientPositivePacketRows026
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

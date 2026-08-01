


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive071
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_071 :
    coefficientPositivePacketTerms071 =
      (positiveEdgeTerms.drop 40896).take 576 := by
  unfold coefficientPositivePacketTerms071 coefficientPositivePacketRows071
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

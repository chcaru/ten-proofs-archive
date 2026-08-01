


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive210
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_210 :
    coefficientPositivePacketTerms210 =
      (positiveEdgeTerms.drop 120960).take 576 := by
  unfold coefficientPositivePacketTerms210 coefficientPositivePacketRows210
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

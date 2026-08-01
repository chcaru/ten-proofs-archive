


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive079
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_079 :
    coefficientPositivePacketTerms079 =
      (positiveEdgeTerms.drop 45504).take 576 := by
  unfold coefficientPositivePacketTerms079 coefficientPositivePacketRows079
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

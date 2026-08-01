


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive046
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_046 :
    coefficientPositivePacketTerms046 =
      (positiveEdgeTerms.drop 26496).take 576 := by
  unfold coefficientPositivePacketTerms046 coefficientPositivePacketRows046
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

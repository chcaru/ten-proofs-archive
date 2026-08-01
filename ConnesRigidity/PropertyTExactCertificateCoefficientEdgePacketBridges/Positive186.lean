


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive186
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_186 :
    coefficientPositivePacketTerms186 =
      (positiveEdgeTerms.drop 107136).take 576 := by
  unfold coefficientPositivePacketTerms186 coefficientPositivePacketRows186
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

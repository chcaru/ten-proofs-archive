


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive035
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_035 :
    coefficientPositivePacketTerms035 =
      (positiveEdgeTerms.drop 20160).take 576 := by
  unfold coefficientPositivePacketTerms035 coefficientPositivePacketRows035
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

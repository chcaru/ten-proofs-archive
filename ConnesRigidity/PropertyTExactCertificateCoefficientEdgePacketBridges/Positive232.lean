


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive232
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_232 :
    coefficientPositivePacketTerms232 =
      (positiveEdgeTerms.drop 133632).take 576 := by
  unfold coefficientPositivePacketTerms232 coefficientPositivePacketRows232
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

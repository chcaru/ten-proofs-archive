


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive198
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_198 :
    coefficientPositivePacketTerms198 =
      (positiveEdgeTerms.drop 114048).take 576 := by
  unfold coefficientPositivePacketTerms198 coefficientPositivePacketRows198
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

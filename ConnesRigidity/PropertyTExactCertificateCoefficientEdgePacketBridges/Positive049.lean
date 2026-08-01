


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive049
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_049 :
    coefficientPositivePacketTerms049 =
      (positiveEdgeTerms.drop 28224).take 576 := by
  unfold coefficientPositivePacketTerms049 coefficientPositivePacketRows049
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

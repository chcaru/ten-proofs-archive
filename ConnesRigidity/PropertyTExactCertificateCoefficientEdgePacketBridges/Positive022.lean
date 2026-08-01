


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive022
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_022 :
    coefficientPositivePacketTerms022 =
      (positiveEdgeTerms.drop 12672).take 576 := by
  unfold coefficientPositivePacketTerms022 coefficientPositivePacketRows022
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

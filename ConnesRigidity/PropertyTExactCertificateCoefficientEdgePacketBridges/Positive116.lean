


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive116
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_116 :
    coefficientPositivePacketTerms116 =
      (positiveEdgeTerms.drop 66816).take 576 := by
  unfold coefficientPositivePacketTerms116 coefficientPositivePacketRows116
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

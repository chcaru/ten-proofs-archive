


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive147
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_147 :
    coefficientPositivePacketTerms147 =
      (positiveEdgeTerms.drop 84672).take 576 := by
  unfold coefficientPositivePacketTerms147 coefficientPositivePacketRows147
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

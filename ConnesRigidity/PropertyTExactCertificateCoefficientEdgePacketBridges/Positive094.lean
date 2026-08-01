


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive094
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_094 :
    coefficientPositivePacketTerms094 =
      (positiveEdgeTerms.drop 54144).take 576 := by
  unfold coefficientPositivePacketTerms094 coefficientPositivePacketRows094
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity




import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive203
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_203 :
    coefficientPositivePacketTerms203 =
      (positiveEdgeTerms.drop 116928).take 576 := by
  unfold coefficientPositivePacketTerms203 coefficientPositivePacketRows203
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

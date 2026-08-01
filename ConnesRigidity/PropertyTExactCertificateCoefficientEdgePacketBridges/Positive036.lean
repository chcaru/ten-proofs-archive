


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive036
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_036 :
    coefficientPositivePacketTerms036 =
      (positiveEdgeTerms.drop 20736).take 576 := by
  unfold coefficientPositivePacketTerms036 coefficientPositivePacketRows036
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

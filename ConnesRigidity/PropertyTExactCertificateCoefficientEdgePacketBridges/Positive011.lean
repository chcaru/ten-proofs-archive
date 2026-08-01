


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive011
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_011 :
    coefficientPositivePacketTerms011 =
      (positiveEdgeTerms.drop 6336).take 576 := by
  unfold coefficientPositivePacketTerms011 coefficientPositivePacketRows011
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

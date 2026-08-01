


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive108
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_108 :
    coefficientPositivePacketTerms108 =
      (positiveEdgeTerms.drop 62208).take 576 := by
  unfold coefficientPositivePacketTerms108 coefficientPositivePacketRows108
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

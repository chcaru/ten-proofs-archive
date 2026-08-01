


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive052
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_052 :
    coefficientPositivePacketTerms052 =
      (positiveEdgeTerms.drop 29952).take 576 := by
  unfold coefficientPositivePacketTerms052 coefficientPositivePacketRows052
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

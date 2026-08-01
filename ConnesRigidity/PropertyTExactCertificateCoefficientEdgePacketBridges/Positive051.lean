


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive051
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_051 :
    coefficientPositivePacketTerms051 =
      (positiveEdgeTerms.drop 29376).take 576 := by
  unfold coefficientPositivePacketTerms051 coefficientPositivePacketRows051
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

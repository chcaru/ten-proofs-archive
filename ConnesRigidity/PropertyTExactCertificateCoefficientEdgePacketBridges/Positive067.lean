


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive067
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_067 :
    coefficientPositivePacketTerms067 =
      (positiveEdgeTerms.drop 38592).take 576 := by
  unfold coefficientPositivePacketTerms067 coefficientPositivePacketRows067
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

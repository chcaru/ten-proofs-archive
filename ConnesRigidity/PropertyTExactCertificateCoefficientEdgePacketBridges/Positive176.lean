


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive176
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_176 :
    coefficientPositivePacketTerms176 =
      (positiveEdgeTerms.drop 101376).take 576 := by
  unfold coefficientPositivePacketTerms176 coefficientPositivePacketRows176
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

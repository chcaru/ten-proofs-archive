


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive252
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_252 :
    coefficientPositivePacketTerms252 =
      (positiveEdgeTerms.drop 145152).take 576 := by
  unfold coefficientPositivePacketTerms252 coefficientPositivePacketRows252
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

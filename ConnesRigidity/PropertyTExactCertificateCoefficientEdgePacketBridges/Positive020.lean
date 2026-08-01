


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive020
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_020 :
    coefficientPositivePacketTerms020 =
      (positiveEdgeTerms.drop 11520).take 576 := by
  unfold coefficientPositivePacketTerms020 coefficientPositivePacketRows020
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

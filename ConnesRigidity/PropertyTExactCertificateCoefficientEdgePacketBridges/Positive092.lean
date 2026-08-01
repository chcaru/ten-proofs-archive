


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive092
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_092 :
    coefficientPositivePacketTerms092 =
      (positiveEdgeTerms.drop 52992).take 576 := by
  unfold coefficientPositivePacketTerms092 coefficientPositivePacketRows092
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity




import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive056
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_056 :
    coefficientPositivePacketTerms056 =
      (positiveEdgeTerms.drop 32256).take 576 := by
  unfold coefficientPositivePacketTerms056 coefficientPositivePacketRows056
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity




import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Diagonal000
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientDiagonalPacketTermsBridge_000 :
    coefficientDiagonalPacketTerms000 =
      (diagonalTerms.drop 0).take 256 := by
  unfold coefficientDiagonalPacketTerms000 coefficientDiagonalPacketRows000
  unfold coefficientDiagonalPacketsTerms
  unfold coefficientDiagonalPacketTerms
    decodeCoefficientDiagonalPacket
    coefficientDiagonalDecodedPacketTerms coefficientEdgeTerm
  unfold diagonalTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

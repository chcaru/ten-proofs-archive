
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Diagonal002
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientDiagonalPacketTermsBridge_002 :
    coefficientDiagonalPacketTerms002 =
      (diagonalTerms.drop 512).take 256 := by
  unfold coefficientDiagonalPacketTerms002 coefficientDiagonalPacketRows002
  unfold coefficientDiagonalPacketsTerms
  unfold coefficientDiagonalPacketTerms
    decodeCoefficientDiagonalPacket
    coefficientDiagonalDecodedPacketTerms coefficientEdgeTerm
  unfold diagonalTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

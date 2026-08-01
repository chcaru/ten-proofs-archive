
import ConnesRigidity.PropertyTExactCertificateCoefficientChecker
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Diagonal002
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Diagonal081Part002.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_081_002 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Diagonal081Part002.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingDiagonal081PartCheck_002 :
    coefficientCheckData coefficientDiagonalPacketTerms002 =
      (coefficientSourceEncoding_081_002, 10108972263776) := by
  unfold coefficientCheckData coefficientSourceEncoding_081_002
  unfold coefficientDiagonalPacketTerms002 coefficientDiagonalPacketRows002
  unfold coefficientDiagonalPacketsTerms coefficientDiagonalPacketTerms
    decodeCoefficientDiagonalPacket
    coefficientDiagonalDecodedPacketTerms coefficientEdgeTerm
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

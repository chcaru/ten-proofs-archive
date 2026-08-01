


import ConnesRigidity.PropertyTExactCertificateCoefficientChecker
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Diagonal006
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Diagonal081Part006.Entry000







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_081_006 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Diagonal081Part006.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingDiagonal081PartCheck_006 :
    coefficientCheckData coefficientDiagonalPacketTerms006 =
      (coefficientSourceEncoding_081_006, 6328005900832) := by
  unfold coefficientCheckData coefficientSourceEncoding_081_006
  unfold coefficientDiagonalPacketTerms006 coefficientDiagonalPacketRows006
  unfold coefficientDiagonalPacketsTerms coefficientDiagonalPacketTerms
    decodeCoefficientDiagonalPacket
    coefficientDiagonalDecodedPacketTerms coefficientEdgeTerm
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

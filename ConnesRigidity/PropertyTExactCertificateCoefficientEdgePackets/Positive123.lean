
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgeBase
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Positive123.Entry000

namespace ConnesRigidity

namespace AffineSymplecticCertificate

@[irreducible] noncomputable def coefficientPositivePacketRows123 :
    List (List Int) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEdgePackets.Positive123.Entry000.data

noncomputable def coefficientPositivePacketTerms123 :
    List (IntegerTableTerm 73033) :=
  coefficientPositivePacketsTerms coefficientPositivePacketRows123

end AffineSymplecticCertificate

end ConnesRigidity

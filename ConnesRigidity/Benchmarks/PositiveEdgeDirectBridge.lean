


import ConnesRigidity.Benchmarks.PositiveEdgeDirectBase
import ConnesRigidity.PropertyTExactCertificateCoefficientBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

def benchmarkOfIntegerTableTerm
    (term : IntegerTableTerm 73033) : BenchmarkIntegerTableTerm where
  key := term.key
  numerator := term.numerator

set_option maxRecDepth 1000000
set_option maxHeartbeats 0 in




theorem benchmarkDirectPositiveTerms32_eq_global :
    benchmarkDirectPositiveTerms32 =
      ((coefficientPositiveTermChunk 0).take 288).map
        benchmarkOfIntegerTableTerm := by
  unfold benchmarkDirectPositiveTerms32 benchmarkPositivePacketTerms
    benchmarkPositiveEdgePackets32 benchmarkOfIntegerTableTerm
    coefficientPositiveTermChunk coefficientPositiveEdgeChunks
    coefficientPositiveChunkSizes positiveEdges positiveEdgeData
    positiveEdgeTermRow positiveEdgeEntries integerOuterTerms
    edgeOfData tableIndex productIndex
    productIndexDataRow productIndexDataRows
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

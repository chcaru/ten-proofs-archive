


import ConnesRigidity.Benchmarks.PositiveEdgeDirectCheck
import ConnesRigidity.PropertyTExactCertificateCoefficientBase

namespace ConnesRigidity

namespace AffineSymplecticCertificate

def benchmarkOfIntegerTableTerm
    (term : IntegerTableTerm 73033) : BenchmarkIntegerTableTerm where
  key := term.key
  numerator := term.numerator

set_option maxRecDepth 1000000
set_option maxHeartbeats 0 in



theorem benchmarkGlobalPositiveEdgeLane32 :
    benchmarkPositiveLaneCheckData
        (((coefficientPositiveTermChunk 0).take 288).map
          benchmarkOfIntegerTableTerm) =
      (benchmarkPositiveEdgeLaneExpected32, 4835629568) := by
  unfold benchmarkPositiveLaneCheckData
    benchmarkOfIntegerTableTerm
    coefficientPositiveTermChunk coefficientPositiveEdgeChunks
    coefficientPositiveChunkSizes positiveEdges positiveEdgeData
    positiveEdgeTermRow positiveEdgeEntries integerOuterTerms
    edgeOfData tableIndex productIndex
    productIndexDataRow productIndexDataRows
    benchmarkPositiveEdgeLaneExpected32
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity

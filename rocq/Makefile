ROCQ ?= rocq
FLAGS := -Q . HallRay
FILES := MatrixAlgebra ReturnBranches ReturnIdentity Contraction StableBranches SymbolicCoding ScalarEstimates ConstantReturn FiberProducts EuclideanNorm ConcreteCocycle SymbolicCocycle MatrixLimits DefectLimit ConstantCoding RealIntervals DefectCertificate DefectNoncommuting EllipticConjugacy DefectPhases PeriodicReturns EllipticPowers IntegralCubic IntegralMatrices MarkedCocycle ReturnInfiniteOrder RealRotationDensity TrigRotations RotationDensity EllipticRecurrence StableCoding TwoSidedCoding NormalizedFlow Concatenation LatticeReturns LatticeBasis LatticeOrbit PaperTarget NormGeometry DaniCorrespondence LatticeSystole DaniSystole SystoleContinuity SystoleCurves StableForgetting ApproximationRealization PeriodicWords PeriodicOrbits PeriodicHeights LimitingWords LimitingFibers LimitingConvergence Matrix3Limits LimitingRepresentatives CompactMatrices PositionalSubsequences PositionalLimits ChartCompactness EllipticContinuity RoofLimits LimitingFamilies SegmentLimits PeakUpperLimits CirclePeaks LowerApproximations PeakConvergence PeakContinuity PeakLocalContinuity BulkFlow RotationAlignment ContractingCircle CuspVectors ParabolicDepth ParabolicPhases PeakPhasePath PhaseHeightRange AdjustedPeriodicPeaks UniformEllipticPowers BlockSelection IntervalPeaks ReturnSegmentPeaks UniformSegmentComparison ReturnBlocks BlockRealization WordPrefixes PrefixFibers NestedWords BlockConstruction ConstructedWords BoundaryWords ConstructedCodes ConstructedFibers ConstructedPeaks HallRayTheorem Audit

.PHONY: all check clean
all: $(addsuffix .vo,$(FILES))

MatrixAlgebra.vo: MatrixAlgebra.v

ReturnBranches.vo: ReturnBranches.v MatrixAlgebra.vo

ReturnIdentity.vo: ReturnIdentity.v ReturnBranches.vo

Contraction.vo: Contraction.v ReturnBranches.vo

StableBranches.vo: StableBranches.v ReturnIdentity.vo Contraction.vo

SymbolicCoding.vo: SymbolicCoding.v Contraction.vo

ScalarEstimates.vo: ScalarEstimates.v MatrixAlgebra.vo

Concatenation.vo: Concatenation.v ScalarEstimates.vo

FiberProducts.vo: FiberProducts.v ScalarEstimates.vo

EuclideanNorm.vo: EuclideanNorm.v FiberProducts.vo

ConcreteCocycle.vo: ConcreteCocycle.v EuclideanNorm.vo Contraction.vo

SymbolicCocycle.vo: SymbolicCocycle.v ConcreteCocycle.vo SymbolicCoding.vo

MatrixLimits.vo: MatrixLimits.v EuclideanNorm.vo

DefectLimit.vo: DefectLimit.v SymbolicCocycle.vo MatrixLimits.vo

ConstantCoding.vo: ConstantCoding.v ConstantReturn.vo DefectLimit.vo

RealIntervals.vo: RealIntervals.v

DefectCertificate.v: generate_defect_certificate.py
	python3 generate_defect_certificate.py

DefectCertificate.vo: DefectCertificate.v ConstantCoding.vo RealIntervals.vo

DefectNoncommuting.vo: DefectNoncommuting.v DefectCertificate.vo

EllipticConjugacy.vo: EllipticConjugacy.v DefectNoncommuting.vo

DefectPhases.vo: DefectPhases.v EllipticConjugacy.vo

PeriodicReturns.vo: PeriodicReturns.v DefectPhases.vo

EllipticPowers.vo: EllipticPowers.v PeriodicReturns.vo

IntegralCubic.vo: IntegralCubic.v

IntegralMatrices.vo: IntegralMatrices.v IntegralCubic.vo ReturnIdentity.vo

MarkedCocycle.vo: MarkedCocycle.v IntegralMatrices.vo SymbolicCocycle.vo

ReturnInfiniteOrder.vo: ReturnInfiniteOrder.v MarkedCocycle.vo PeriodicReturns.vo

RealRotationDensity.vo: RealRotationDensity.v

TrigRotations.vo: TrigRotations.v RealRotationDensity.vo EllipticConjugacy.vo

RotationDensity.vo: RotationDensity.v TrigRotations.vo ReturnInfiniteOrder.vo EllipticPowers.vo

EllipticRecurrence.vo: EllipticRecurrence.v RotationDensity.vo

StableCoding.vo: StableCoding.v StableBranches.vo SymbolicCoding.vo

TwoSidedCoding.vo: TwoSidedCoding.v StableCoding.vo

NormalizedFlow.vo: NormalizedFlow.v MarkedCocycle.vo StableBranches.vo

LatticeReturns.vo: LatticeReturns.v NormalizedFlow.vo TwoSidedCoding.vo PeriodicReturns.vo Concatenation.vo

LatticeBasis.vo: LatticeBasis.v IntegralMatrices.vo

LatticeOrbit.vo: LatticeOrbit.v LatticeReturns.vo LatticeBasis.vo

ConstantReturn.vo: ConstantReturn.v ScalarEstimates.vo ReturnBranches.vo

NormGeometry.vo: NormGeometry.v PaperTarget.vo

DaniCorrespondence.vo: DaniCorrespondence.v LatticeBasis.vo NormGeometry.vo ScalarEstimates.vo NormalizedFlow.vo

LatticeSystole.vo: LatticeSystole.v DaniCorrespondence.vo

DaniSystole.vo: DaniSystole.v LatticeSystole.vo

SystoleContinuity.vo: SystoleContinuity.v LatticeSystole.vo

SystoleCurves.vo: SystoleCurves.v SystoleContinuity.vo

StableForgetting.vo: StableForgetting.v SystoleCurves.vo LatticeReturns.vo

ApproximationRealization.vo: ApproximationRealization.v StableForgetting.vo DaniSystole.vo

PeriodicWords.vo: PeriodicWords.v LatticeReturns.vo

PeriodicOrbits.vo: PeriodicOrbits.v PeriodicWords.vo LatticeOrbit.vo StableForgetting.vo

PeriodicHeights.vo: PeriodicHeights.v PeriodicOrbits.vo EllipticRecurrence.vo

LimitingWords.vo: LimitingWords.v PeriodicWords.vo

LimitingFibers.vo: LimitingFibers.v LimitingWords.vo EllipticPowers.vo

LimitingConvergence.vo: LimitingConvergence.v LimitingFibers.vo

Matrix3Limits.vo: Matrix3Limits.v SystoleCurves.vo LatticeReturns.vo

LimitingRepresentatives.vo: LimitingRepresentatives.v LimitingConvergence.vo Matrix3Limits.vo

CompactMatrices.vo: CompactMatrices.v LimitingConvergence.vo Matrix3Limits.vo

PositionalSubsequences.vo: PositionalSubsequences.v CompactMatrices.vo

PositionalLimits.vo: PositionalLimits.v PositionalSubsequences.vo LimitingRepresentatives.vo

ChartCompactness.vo: ChartCompactness.v PositionalLimits.vo

EllipticContinuity.vo: EllipticContinuity.v EllipticRecurrence.vo Matrix3Limits.vo CompactMatrices.vo

RoofLimits.vo: RoofLimits.v EllipticContinuity.vo

LimitingFamilies.vo: LimitingFamilies.v ChartCompactness.vo RoofLimits.vo

SegmentLimits.vo: SegmentLimits.v LimitingFamilies.vo

PeakUpperLimits.vo: PeakUpperLimits.v SegmentLimits.vo PeriodicHeights.vo

CirclePeaks.vo: CirclePeaks.v PeriodicHeights.vo EllipticContinuity.vo PositionalLimits.vo RoofLimits.vo

LowerApproximations.vo: LowerApproximations.v CirclePeaks.vo LimitingFamilies.vo

PeakConvergence.vo: PeakConvergence.v LowerApproximations.vo PeakUpperLimits.vo

PeakContinuity.vo: PeakContinuity.v PeakConvergence.vo

PeakLocalContinuity.vo: PeakLocalContinuity.v PeakContinuity.vo

BulkFlow.vo: BulkFlow.v LimitingFamilies.vo LatticeOrbit.vo

RotationAlignment.vo: RotationAlignment.v DefectPhases.vo

ContractingCircle.vo: ContractingCircle.v RotationAlignment.vo EllipticContinuity.vo

CuspVectors.vo: CuspVectors.v ContractingCircle.vo RoofLimits.vo

ParabolicDepth.vo: ParabolicDepth.v CuspVectors.vo BulkFlow.vo DaniSystole.vo

ParabolicPhases.vo: ParabolicPhases.v CirclePeaks.vo DefectPhases.vo

PeakPhasePath.vo: PeakPhasePath.v ParabolicPhases.vo ParabolicDepth.vo PeakLocalContinuity.vo

PhaseHeightRange.vo: PhaseHeightRange.v PeakPhasePath.vo PeakContinuity.vo

AdjustedPeriodicPeaks.vo: AdjustedPeriodicPeaks.v PhaseHeightRange.vo PeakConvergence.vo

UniformEllipticPowers.vo: UniformEllipticPowers.v EllipticContinuity.vo EllipticPowers.vo

BlockSelection.vo: BlockSelection.v AdjustedPeriodicPeaks.vo UniformEllipticPowers.vo

IntervalPeaks.vo: IntervalPeaks.v LowerApproximations.vo ChartCompactness.vo

ReturnSegmentPeaks.vo: ReturnSegmentPeaks.v IntervalPeaks.vo RoofLimits.vo

UniformSegmentComparison.vo: UniformSegmentComparison.v ReturnSegmentPeaks.vo ChartCompactness.vo

ReturnBlocks.vo: ReturnBlocks.v UniformSegmentComparison.vo PeriodicHeights.vo

BlockRealization.vo: BlockRealization.v ReturnBlocks.vo ApproximationRealization.vo AdjustedPeriodicPeaks.vo

WordPrefixes.vo: WordPrefixes.v SymbolicCoding.vo SymbolicCocycle.vo PeriodicReturns.vo

PrefixFibers.vo: PrefixFibers.v WordPrefixes.vo MatrixLimits.vo ConcreteCocycle.vo

NestedWords.vo: NestedWords.v PrefixFibers.vo LimitingConvergence.vo

BlockConstruction.vo: BlockConstruction.v PrefixFibers.vo BlockSelection.vo

ConstructedWords.vo: ConstructedWords.v NestedWords.vo BlockConstruction.vo

BoundaryWords.vo: BoundaryWords.v WordPrefixes.vo PeriodicWords.vo

ConstructedCodes.vo: ConstructedCodes.v ConstructedWords.vo BoundaryWords.vo

ConstructedFibers.vo: ConstructedFibers.v ConstructedCodes.vo

ConstructedPeaks.vo: ConstructedPeaks.v ConstructedFibers.vo ReturnBlocks.vo

HallRayTheorem.vo: HallRayTheorem.v ConstructedPeaks.vo BlockRealization.vo

Audit.vo: Audit.v HallRayTheorem.vo

%.vo: %.v
	$(ROCQ) compile $(FLAGS) $<

check: all
	$(ROCQ) check -silent $(FLAGS) $(addprefix HallRay.,$(FILES))

clean:
	$(RM) $(addsuffix .vo,$(FILES)) $(addsuffix .vos,$(FILES)) $(addsuffix .vok,$(FILES)) $(addsuffix .glob,$(FILES)) $(addprefix .,$(addsuffix .aux,$(FILES)))

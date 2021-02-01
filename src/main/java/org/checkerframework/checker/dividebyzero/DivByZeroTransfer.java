package org.checkerframework.checker.dividebyzero;

import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.flow.CFTransfer;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.flow.CFStore;
import org.checkerframework.framework.flow.CFAnalysis;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.ConditionalTransferResult;
import org.checkerframework.dataflow.analysis.FlowExpressions;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;

import javax.lang.model.element.AnnotationMirror;
import java.lang.annotation.Annotation;

import java.util.Set;

import org.checkerframework.checker.dividebyzero.qual.*;

public class DivByZeroTransfer extends CFTransfer {

    enum Comparison {
        /** == */ EQ,
        /** != */ NE,
        /** <  */ LT,
        /** <= */ LE,
        /** >  */ GT,
        /** >= */ GE
    }

    enum BinaryOperator {
        /** + */ PLUS,
        /** - */ MINUS,
        /** * */ TIMES,
        /** / */ DIVIDE,
        /** % */ MOD
    }

    // ========================================================================
    // Transfer functions to implement

    /**
     * Assuming that a simple comparison (lhs `op` rhs) returns true, this
     * function should refine what we know about the left-hand side (lhs). (The
     * input value "lhs" is always a legal return value, but not a very useful
     * one.)
     *
     * <p>For example, given the code
     * <pre>
     * if (y != 0) { x = 1 / y; }
     * </pre>
     * the comparison "y != 0" causes us to learn the fact that "y is not zero"
     * inside the body of the if-statement. This function would be called with
     * "NE", "top", and "zero", and should return "not zero" (or the appropriate
     * result for your lattice).
     *
     * <p>Note that the returned value should always be lower in the lattice
     * than the given point for lhs. The "glb" helper function below will
     * probably be useful here.
     *
     * @param operator   a comparison operator
     * @param lhs        the lattice point for the left-hand side of the comparison expression
     * @param rhs        the lattice point for the right-hand side of the comparison expression
     * @return a refined type for lhs
     */
    private AnnotationMirror refineLhsOfComparison(
            Comparison operator,
            AnnotationMirror lhs,
            AnnotationMirror rhs) {
        switch (operator) {
            case EQ:
                if (isZero(rhs)) {
                    return zero();
                }
                break;
            case NE:
                if (isZero(rhs)) {
                    return nonzero();
                }
                break;
            case LT:
                if (isNeg(rhs) || isZero(rhs)) {
                    return neg();
                }
                break;
            case LE:
                if (isNeg(rhs)) {
                    return neg();
                }
                break;
            case GT:
                if (isPos(rhs) || isZero(rhs)) {
                    return pos();
                }
                break;
            case GE:
                if (isPos(rhs)) {
                    return pos();
                }
                break;
        }
        return lhs;
    }

    /**
     * For an arithmetic expression (lhs `op` rhs), compute the point in the
     * lattice for the result of evaluating the expression. ("Top" is always a
     * legal return value, but not a very useful one.)
     *
     * <p>For example,
     * <pre>x = 1 + 0</pre>
     * should cause us to conclude that "x is not zero".
     *
     * @param operator   a binary operator
     * @param lhs        the lattice point for the left-hand side of the expression
     * @param rhs        the lattice point for the right-hand side of the expression
     * @return the lattice point for the result of the expression
     */
    private AnnotationMirror arithmeticTransfer(
            BinaryOperator operator,
            AnnotationMirror lhs,
            AnnotationMirror rhs) {
        // TODO
        switch (operator) {
            case PLUS:
                if (isTop(lhs) || isTop(rhs)) {
                    break;
                } else if ((isZero(lhs) && isNonZero(rhs)) || (isZero(rhs) && isNonZero(lhs))) {
                    if (isNonZero(rhs)) {
                        return rhs;
                    } else {
                        return lhs;
                    }
                } else if (equal(lhs, rhs) && !equal(lhs, nonzero())) {
                    // Case where lhs, rhs are both equal to either Pos, Neg, or Zero
                    return lhs;
                }
                break;
            case MINUS:
                if (isPos(lhs) && isNeg(rhs)) {
                    return pos();
                } else if (isNeg(lhs) && isPos(rhs)) {
                    return neg();
                } else if (isZero(lhs)) {
                    if (equal(lhs, rhs)) {
                        return zero();
                    } else if (isPos(rhs)) {
                        return neg();
                    } else if (isNeg(rhs)) {
                        return pos();
                    } else if (isNonZero(rhs)) {
                        return nonzero();
                    }
                } else if (isZero(rhs)) {
                    // We know the rhs is not Zero
                    if (isPos(lhs) || isNeg(lhs) || isNonZero(lhs)) {
                        return lhs;
                    }
                }
                // All other cases are top
                break;
            case TIMES:
                if (isTop(lhs) || isTop(rhs)) {
                    break;
                } else if (areOpposites(lhs, rhs)) {
                    return neg();
                } else if (isZero(lhs) || isZero(rhs)) {
                    return zero();
                } else if (equal(lhs, nonzero()) || equal(rhs, nonzero())) {
                    return nonzero();
                }
                // Last remaining case: we have both neg or both pos
                return pos();
            case DIVIDE:
            case MOD:
                if (isTop(lhs) || isTop(rhs) || isZero(rhs)) break;
                if (areOpposites(lhs, rhs)) {
                    return neg();
                } else if (isNonZero(lhs)) {
                    // Only have the division by Pos, Neg, and NonZero
                    return nonzero();
                } else if (isZero(lhs)) {
                    // Only have division by Pos, Neg, and NonZero left
                    return zero();
                } else if (equal(lhs, rhs) && (isPos(lhs) || isNeg(lhs))) {
                    // Both Pos or both Neg
                    return pos();
                } else if (equal(rhs, nonzero())) {
                    // lhs can only be Pos or Neg
                    return nonzero();
                }
                break;
        }
        return top();
    }

    private boolean isNeg(AnnotationMirror t) {
        return equal(t, neg());
    }

    private boolean isPos(AnnotationMirror t) {
        return equal(t, pos());
    }

    private boolean isNonZero(AnnotationMirror t) {
        return !equal(t, bottom()) && equal(lub(t, nonzero()), nonzero());
    }

    private boolean isTop(AnnotationMirror t) {
        return equal(t, top());
    }

    private boolean isZero(AnnotationMirror t) {
        return equal(t, zero());
    }

    private AnnotationMirror nonzero() {
        return reflect(NonZero.class);
    }

    private AnnotationMirror zero() {
        return reflect(Zero.class);
    }

    private boolean areOpposites(AnnotationMirror a, AnnotationMirror b) {
        return (equal(a, pos()) && equal(b, neg())) || (equal(a, neg()) && equal(b, pos()));
    }

    private AnnotationMirror neg() {
        return reflect(Neg.class);
    }

    private AnnotationMirror pos() {
        return reflect(Pos.class);
    }

    // ========================================================================
    // Useful helpers

    /** Get the top of the lattice */
    private AnnotationMirror top() {
        return analysis.getTypeFactory().getQualifierHierarchy().getTopAnnotations().iterator().next();
    }

    /** Get the bottom of the lattice */
    private AnnotationMirror bottom() {
        return analysis.getTypeFactory().getQualifierHierarchy().getBottomAnnotations().iterator().next();
    }

    /** Compute the least-upper-bound of two points in the lattice */
    private AnnotationMirror lub(AnnotationMirror x, AnnotationMirror y) {
        return analysis.getTypeFactory().getQualifierHierarchy().leastUpperBound(x, y);
    }

    /** Compute the greatest-lower-bound of two points in the lattice */
    private AnnotationMirror glb(AnnotationMirror x, AnnotationMirror y) {
        return analysis.getTypeFactory().getQualifierHierarchy().greatestLowerBound(x, y);
    }

    /** Convert a "Class" object (e.g. "Top.class") to a point in the lattice */
    private AnnotationMirror reflect(Class<? extends Annotation> qualifier) {
        return AnnotationBuilder.fromClass(
            analysis.getTypeFactory().getProcessingEnv().getElementUtils(),
            qualifier);
    }

    /** Determine whether two AnnotationMirrors are the same point in the lattice */
    private boolean equal(AnnotationMirror x, AnnotationMirror y) {
        return AnnotationUtils.areSame(x, y);
    }

    /** `x op y` == `y flip(op) x` */
    private Comparison flip(Comparison op) {
        switch (op) {
            case EQ: return Comparison.EQ;
            case NE: return Comparison.NE;
            case LT: return Comparison.GT;
            case LE: return Comparison.GE;
            case GT: return Comparison.LT;
            case GE: return Comparison.LE;
            default: throw new IllegalArgumentException(op.toString());
        }
    }

    /** `x op y` == `!(x negate(op) y)` */
    private Comparison negate(Comparison op) {
        switch (op) {
            case EQ: return Comparison.NE;
            case NE: return Comparison.EQ;
            case LT: return Comparison.GE;
            case LE: return Comparison.GT;
            case GT: return Comparison.LE;
            case GE: return Comparison.LT;
            default: throw new IllegalArgumentException(op.toString());
        }
    }

    // ========================================================================
    // Checker Framework plumbing

    public DivByZeroTransfer(CFAnalysis analysis) {
        super(analysis);
    }

    private TransferResult<CFValue, CFStore> implementComparison(Comparison op, BinaryOperationNode n, TransferResult<CFValue, CFStore> out) {
        QualifierHierarchy hierarchy = analysis.getTypeFactory().getQualifierHierarchy();
        AnnotationMirror l = findAnnotation(analysis.getValue(n.getLeftOperand()).getAnnotations(), hierarchy);
        AnnotationMirror r = findAnnotation(analysis.getValue(n.getRightOperand()).getAnnotations(), hierarchy);

        if (l == null || r == null) {
            // this can happen for generic types
            return out;
        }

        CFStore thenStore = out.getThenStore().copy();
        CFStore elseStore = out.getElseStore().copy();

        thenStore.insertValue(
            FlowExpressions.internalReprOf(analysis.getTypeFactory(), n.getLeftOperand()),
            refineLhsOfComparison(op, l, r));

        thenStore.insertValue(
            FlowExpressions.internalReprOf(analysis.getTypeFactory(), n.getRightOperand()),
            refineLhsOfComparison(flip(op), r, l));

        elseStore.insertValue(
            FlowExpressions.internalReprOf(analysis.getTypeFactory(), n.getLeftOperand()),
            refineLhsOfComparison(negate(op), l, r));

        elseStore.insertValue(
            FlowExpressions.internalReprOf(analysis.getTypeFactory(), n.getRightOperand()),
            refineLhsOfComparison(flip(negate(op)), r, l));

        return new ConditionalTransferResult<>(out.getResultValue(), thenStore, elseStore);
    }

    private TransferResult<CFValue, CFStore> implementOperator(BinaryOperator op, BinaryOperationNode n, TransferResult<CFValue, CFStore> out) {
        QualifierHierarchy hierarchy = analysis.getTypeFactory().getQualifierHierarchy();
        AnnotationMirror l = findAnnotation(analysis.getValue(n.getLeftOperand()).getAnnotations(), hierarchy);
        AnnotationMirror r = findAnnotation(analysis.getValue(n.getRightOperand()).getAnnotations(), hierarchy);

        if (l == null || r == null) {
            // this can happen for generic types
            return out;
        }

        AnnotationMirror res = arithmeticTransfer(op, l, r);
        CFValue newResultValue = analysis.createSingleAnnotationValue(res, out.getResultValue().getUnderlyingType());
        return new RegularTransferResult<>(newResultValue, out.getRegularStore());
    }

    @Override
    public TransferResult<CFValue, CFStore> visitEqualTo(EqualToNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.EQ, n, super.visitEqualTo(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNotEqual(NotEqualNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.NE, n, super.visitNotEqual(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitGreaterThan(GreaterThanNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.GT, n, super.visitGreaterThan(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitGreaterThanOrEqual(GreaterThanOrEqualNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.GE, n, super.visitGreaterThanOrEqual(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitLessThan(LessThanNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.LT, n, super.visitLessThan(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitLessThanOrEqual(LessThanOrEqualNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.LE, n, super.visitLessThanOrEqual(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitIntegerDivision(IntegerDivisionNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.DIVIDE, n, super.visitIntegerDivision(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitIntegerRemainder(IntegerRemainderNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.MOD, n, super.visitIntegerRemainder(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitFloatingDivision(FloatingDivisionNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.DIVIDE, n, super.visitFloatingDivision(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitFloatingRemainder(FloatingRemainderNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.MOD, n, super.visitFloatingRemainder(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNumericalMultiplication(NumericalMultiplicationNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.TIMES, n, super.visitNumericalMultiplication(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNumericalAddition(NumericalAdditionNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.PLUS, n, super.visitNumericalAddition(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNumericalSubtraction(NumericalSubtractionNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.MINUS, n, super.visitNumericalSubtraction(n, p));
    }

    private static AnnotationMirror findAnnotation(
            Set<AnnotationMirror> set, QualifierHierarchy hierarchy) {
        if (set.size() == 0) {
            return null;
        }
        Set<? extends AnnotationMirror> tops = hierarchy.getTopAnnotations();
        return hierarchy.findAnnotationInSameHierarchy(set, tops.iterator().next());
    }

}

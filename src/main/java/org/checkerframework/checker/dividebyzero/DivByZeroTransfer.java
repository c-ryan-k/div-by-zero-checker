package org.checkerframework.checker.dividebyzero;

import java.lang.annotation.Annotation;
import java.util.Set;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.checker.dividebyzero.qual.*;
import org.checkerframework.dataflow.analysis.ConditionalTransferResult;
import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.flow.CFAnalysis;
import org.checkerframework.framework.flow.CFStore;
import org.checkerframework.framework.flow.CFTransfer;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;

public class DivByZeroTransfer extends CFTransfer {

  enum Comparison {
    /** == */
    EQ,
    /** != */
    NE,
    /** < */
    LT,
    /** <= */
    LE,
    /** > */
    GT,
    /** >= */
    GE
  }

  enum BinaryOperator {
    /** + */
    PLUS,
    /** - */
    MINUS,
    /** * */
    TIMES,
    /** / */
    DIVIDE,
    /** % */
    MOD
  }

  // ========================================================================
  // Transfer functions to implement

  /**
   * Assuming that a simple comparison (lhs `op` rhs) returns true, this function should refine what
   * we know about the left-hand side (lhs). (The input value "lhs" is always a legal return value,
   * but not a very useful one.)
   *
   * <p>For example, given the code
   *
   * <pre>
   * if (y != 0) { x = 1 / y; }
   * </pre>
   *
   * the comparison "y != 0" causes us to learn the fact that "y is not zero" inside the body of the
   * if-statement. This function would be called with "NE", "top", and "zero", and should return
   * "not zero" (or the appropriate result for your lattice).
   *
   * <p>Note that the returned value should always be lower in the lattice than the given point for
   * lhs. The "glb" helper function below will probably be useful here.
   *
   * @param operator a comparison operator
   * @param lhs the lattice point for the left-hand side of the comparison expression
   * @param rhs the lattice point for the right-hand side of the comparison expression
   * @return a refined type for lhs
   */
  private AnnotationMirror refineLhsOfComparison(
    Comparison operator, AnnotationMirror lhs, AnnotationMirror rhs) {
    AnnotationMirror result = bottom();
    switch (operator) {
      case LT:
        // anything less than zero or negative is negative
        if (isType(rhs, Zero.class) || isType(rhs, Negative.class)) {
          result = reflect(Negative.class);
        }
        // anything less than top / positive / NZ is unknown
        else if (rhs == top() || isType(rhs, Positive.class) || isType(rhs, NonZero.class)) {
          result = top();
        }
        // bottom is empty
        else if (rhs == bottom()) {
          result = rhs;
        }
        break;
      case GT:
        if (isType(rhs, Zero.class) || isType(rhs, Positive.class)) {
          result = reflect(Positive.class);
        }
        else if (rhs == top() || isType(rhs, NonZero.class) || isType(rhs, Negative.class)) {
          result = top();
        }
        else if (rhs == bottom()) {
          result = rhs;
        }
        break;
      case NE:
        // if x != 0, x == nz
        if(isType(rhs, Zero.class)) {
          result = reflect(NonZero.class);
        }
        else {
          result = glb(rhs, lhs);
        }
        break;
      case EQ:
        result = lub(rhs, lhs);
        break;
      case GE:
        if (isType(rhs, Positive.class)) {
          result = rhs;
        }
        else if (rhs == bottom()) {
          result = bottom();
        }
        else {
          result = top();
        }
        break;
      case LE:
        if (isType(rhs, Negative.class)) {
          result = rhs;
        }
        else if (rhs == bottom()) {
          result = rhs;
        }
        else {
          result = top();
        }
        break;
      default:
        // default - we dunno
        result = lub(rhs, lhs);
        break;
    }
    return result;
  }

  private boolean isType(AnnotationMirror anm, Class<? extends Annotation> c) {
    return analysis.getTypeFactory().areSameByClass(anm, c);
  }

  /**
   * For an arithmetic expression (lhs `op` rhs), compute the point in the lattice for the result of
   * evaluating the expression. ("Top" is always a legal return value, but not a very useful one.)
   *
   * <p>For example,
   *
   * <pre>x = 1 + 0</pre>
   *
   * should cause us to conclude that "x is not zero".
   *
   * @param operator a binary operator
   * @param lhs the lattice point for the left-hand side of the expression
   * @param rhs the lattice point for the right-hand side of the expression
   * @return the lattice point for the result of the expression
   */
  private AnnotationMirror arithmeticTransfer(
      BinaryOperator operator, AnnotationMirror lhs, AnnotationMirror rhs) {
    switch (operator) {
      case PLUS:
        return plusTransfer(lhs, rhs);
      case MINUS:
        return minusTransfer(lhs, rhs);
      case TIMES:
        return timesTransfer(lhs, rhs);
      case DIVIDE:
        return divideTransfer(lhs, rhs);
      case MOD:
        return modTransfer(lhs, rhs);
    }
    return top();
  }


  private AnnotationMirror plusTransfer(AnnotationMirror lhs, AnnotationMirror rhs) {
    // if either are bottom, return bottom
    if(rhs == bottom() || lhs == bottom()) {
      return bottom();
    }
    // if either are top, return top
    else if(rhs == top() || lhs == top()) {
      return top();
    }
    // if positive lhs, return positive if rhs is positive or zero, else top
    else if(isType(lhs, Positive.class)) {
      return (isType(rhs, Positive.class) || isType(rhs, Zero.class)) ? reflect(Positive.class) : top();
    }
    // if negative lhs, return hegative if rhs is negative or zero, else top
    else if(isType(lhs, Negative.class)) {
      return (isType(rhs, Negative.class) || isType(rhs, Zero.class)) ? reflect(Negative.class) : top();
    }
    // zero plus anything is that anything
    else if(isType(lhs, Zero.class)) {
      return rhs;
    }
    // otherwise we don't know
    else return top();
  }

  private AnnotationMirror minusTransfer(AnnotationMirror lhs, AnnotationMirror rhs) {
    // if either are bottom, return bottom
    if(rhs == bottom() || lhs == bottom()) {
      return bottom();
    }
    // if either are top, return top
    else if(rhs == top() || lhs == top()) {
      return top();
    }
    // if positive lhs, return positive if rhs is negative or zero, else top
    else if(isType(lhs, Positive.class)) {
      return (isType(rhs, Negative.class) || isType(rhs, Zero.class)) ? reflect(Positive.class) : top();
    }
    // if negative lhs, return negative if rhs is positive or zero, else top
    else if(isType(lhs, Negative.class)) {
      return (isType(rhs, Positive.class) || isType(rhs, Zero.class)) ? reflect(Negative.class) : top();
    }
    // zero minus something
    else if(isType(lhs, Zero.class)) {
      // 0 - 0 == 0
      if(isType(rhs, Zero.class)) {
        return reflect(Zero.class);
      }
      // zero - neg == pos, zero - pos == neg
      else return reflect(isType(rhs, Positive.class) ? Negative.class : Positive.class);
    }
    // otherwise we don't know
    else return top();
  }

  private AnnotationMirror timesTransfer(AnnotationMirror lhs, AnnotationMirror rhs) {
    // if either are bottom, return bottom
    if(rhs == bottom() || lhs == bottom()) {
      return bottom();
    }
    // if either are zero, return zero
    else if(isType(rhs, Zero.class) || isType(lhs, Zero.class)) {
      return reflect(Zero.class);
    }
    // negative * (+, -, nz, t)
    else if(isType(lhs, Negative.class)) {
      // - * (nz, t) == t
      if(isType(rhs, NonZero.class) || rhs == top()) {
        return top();
      }
      else return (isType(rhs, Negative.class)) ? reflect(Positive.class) : reflect(Negative.class);
    }
    // pos * (+, -, nz, t)
    else if(isType(lhs, Positive.class)) {
      // + * (nz, t) == t
      if(isType(rhs, NonZero.class) || rhs == top()) {
        return top();
      }
      else return (isType(rhs, Negative.class)) ? reflect(Negative.class) : reflect(Positive.class);
    }
    else return top();
  }
  private AnnotationMirror divideTransfer(AnnotationMirror lhs, AnnotationMirror rhs) {
    // if either are bottom, or bottom has zero (T, 0), return error state (bottom)
    if(rhs == bottom() || lhs == bottom() || rhs == top() || isType(rhs, Zero.class)) {
      return bottom();
    }
    // T / anything == T
    else if(lhs == top()) {
      return top();
    }
    // positive / 
    else if(isType(lhs, Positive.class)) {
      if(isType(rhs, NonZero.class)) {
        return top();
      }
      else return isType(rhs, Positive.class) ? reflect(Positive.class) : reflect(Negative.class);
    }
    // negative /
    else if(isType(lhs, Negative.class)) {
      if(isType(rhs, NonZero.class)) {
        return top();
      }
      else return isType(rhs, Positive.class) ? reflect(Negative.class) : reflect(Positive.class);
    }
    else return top();
  }
  private AnnotationMirror modTransfer(AnnotationMirror lhs, AnnotationMirror rhs) {
    // if either are bottom, or bottom has zero (T, 0), return error state (bottom)
    if(rhs == bottom() || lhs == bottom() || rhs == top() || isType(rhs, Zero.class)) {
      return bottom();
    }
    // T / anything == T
    else if(lhs == top()) {
      return top();
    }
    else return top();
  }
  // ========================================================================
  // Useful helpers

  /** Get the top of the lattice */
  private AnnotationMirror top() {
    return analysis.getTypeFactory().getQualifierHierarchy().getTopAnnotations().iterator().next();
  }

  /** Get the bottom of the lattice */
  private AnnotationMirror bottom() {
    return analysis
        .getTypeFactory()
        .getQualifierHierarchy()
        .getBottomAnnotations()
        .iterator()
        .next();
  }

  /** Compute the least-upper-bound of two points in the lattice */
  private AnnotationMirror lub(AnnotationMirror x, AnnotationMirror y) {
    return analysis.getTypeFactory().getQualifierHierarchy().leastUpperBoundQualifiersOnly(x, y);
  }

  /** Compute the greatest-lower-bound of two points in the lattice */
  private AnnotationMirror glb(AnnotationMirror x, AnnotationMirror y) {
    return analysis.getTypeFactory().getQualifierHierarchy().greatestLowerBoundQualifiersOnly(x, y);
  }

  /** Convert a "Class" object (e.g. "Top.class") to a point in the lattice */
  private AnnotationMirror reflect(Class<? extends Annotation> qualifier) {
    return AnnotationBuilder.fromClass(
        analysis.getTypeFactory().getProcessingEnv().getElementUtils(), qualifier);
  }

  /** Determine whether two AnnotationMirrors are the same point in the lattice */
  private boolean equal(AnnotationMirror x, AnnotationMirror y) {
    return AnnotationUtils.areSame(x, y);
  }

  /** `x op y` == `y flip(op) x` */
  private Comparison flip(Comparison op) {
    switch (op) {
      case EQ:
        return Comparison.EQ;
      case NE:
        return Comparison.NE;
      case LT:
        return Comparison.GT;
      case LE:
        return Comparison.GE;
      case GT:
        return Comparison.LT;
      case GE:
        return Comparison.LE;
      default:
        throw new IllegalArgumentException(op.toString());
    }
  }

  /** `x op y` == `!(x negate(op) y)` */
  private Comparison negate(Comparison op) {
    switch (op) {
      case EQ:
        return Comparison.NE;
      case NE:
        return Comparison.EQ;
      case LT:
        return Comparison.GE;
      case LE:
        return Comparison.GT;
      case GT:
        return Comparison.LE;
      case GE:
        return Comparison.LT;
      default:
        throw new IllegalArgumentException(op.toString());
    }
  }

  // ========================================================================
  // Checker Framework plumbing

  public DivByZeroTransfer(CFAnalysis analysis) {
    super(analysis);
  }

  private TransferResult<CFValue, CFStore> implementComparison(
      Comparison op, BinaryOperationNode n, TransferResult<CFValue, CFStore> out) {
    QualifierHierarchy hierarchy = analysis.getTypeFactory().getQualifierHierarchy();
    AnnotationMirror l =
        findAnnotation(analysis.getValue(n.getLeftOperand()).getAnnotations(), hierarchy);
    AnnotationMirror r =
        findAnnotation(analysis.getValue(n.getRightOperand()).getAnnotations(), hierarchy);

    if (l == null || r == null) {
      // this can happen for generic types
      return out;
    }

    CFStore thenStore = out.getThenStore().copy();
    CFStore elseStore = out.getElseStore().copy();

    thenStore.insertValue(
        JavaExpression.fromNode(n.getLeftOperand()), refineLhsOfComparison(op, l, r));

    thenStore.insertValue(
        JavaExpression.fromNode(n.getRightOperand()), refineLhsOfComparison(flip(op), r, l));

    elseStore.insertValue(
        JavaExpression.fromNode(n.getLeftOperand()), refineLhsOfComparison(negate(op), l, r));

    elseStore.insertValue(
        JavaExpression.fromNode(n.getRightOperand()),
        refineLhsOfComparison(flip(negate(op)), r, l));

    return new ConditionalTransferResult<>(out.getResultValue(), thenStore, elseStore);
  }

  private TransferResult<CFValue, CFStore> implementOperator(
      BinaryOperator op, BinaryOperationNode n, TransferResult<CFValue, CFStore> out) {
    QualifierHierarchy hierarchy = analysis.getTypeFactory().getQualifierHierarchy();
    AnnotationMirror l =
        findAnnotation(analysis.getValue(n.getLeftOperand()).getAnnotations(), hierarchy);
    AnnotationMirror r =
        findAnnotation(analysis.getValue(n.getRightOperand()).getAnnotations(), hierarchy);

    if (l == null || r == null) {
      // this can happen for generic types
      return out;
    }

    AnnotationMirror res = arithmeticTransfer(op, l, r);
    CFValue newResultValue =
        analysis.createSingleAnnotationValue(res, out.getResultValue().getUnderlyingType());
    return new RegularTransferResult<>(newResultValue, out.getRegularStore());
  }

  @Override
  public TransferResult<CFValue, CFStore> visitEqualTo(
      EqualToNode n, TransferInput<CFValue, CFStore> p) {
    return implementComparison(Comparison.EQ, n, super.visitEqualTo(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitNotEqual(
      NotEqualNode n, TransferInput<CFValue, CFStore> p) {
    return implementComparison(Comparison.NE, n, super.visitNotEqual(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitGreaterThan(
      GreaterThanNode n, TransferInput<CFValue, CFStore> p) {
    return implementComparison(Comparison.GT, n, super.visitGreaterThan(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitGreaterThanOrEqual(
      GreaterThanOrEqualNode n, TransferInput<CFValue, CFStore> p) {
    return implementComparison(Comparison.GE, n, super.visitGreaterThanOrEqual(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitLessThan(
      LessThanNode n, TransferInput<CFValue, CFStore> p) {
    return implementComparison(Comparison.LT, n, super.visitLessThan(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitLessThanOrEqual(
      LessThanOrEqualNode n, TransferInput<CFValue, CFStore> p) {
    return implementComparison(Comparison.LE, n, super.visitLessThanOrEqual(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitIntegerDivision(
      IntegerDivisionNode n, TransferInput<CFValue, CFStore> p) {
    return implementOperator(BinaryOperator.DIVIDE, n, super.visitIntegerDivision(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitIntegerRemainder(
      IntegerRemainderNode n, TransferInput<CFValue, CFStore> p) {
    return implementOperator(BinaryOperator.MOD, n, super.visitIntegerRemainder(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitFloatingDivision(
      FloatingDivisionNode n, TransferInput<CFValue, CFStore> p) {
    return implementOperator(BinaryOperator.DIVIDE, n, super.visitFloatingDivision(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitFloatingRemainder(
      FloatingRemainderNode n, TransferInput<CFValue, CFStore> p) {
    return implementOperator(BinaryOperator.MOD, n, super.visitFloatingRemainder(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitNumericalMultiplication(
      NumericalMultiplicationNode n, TransferInput<CFValue, CFStore> p) {
    return implementOperator(BinaryOperator.TIMES, n, super.visitNumericalMultiplication(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitNumericalAddition(
      NumericalAdditionNode n, TransferInput<CFValue, CFStore> p) {
    return implementOperator(BinaryOperator.PLUS, n, super.visitNumericalAddition(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitNumericalSubtraction(
      NumericalSubtractionNode n, TransferInput<CFValue, CFStore> p) {
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

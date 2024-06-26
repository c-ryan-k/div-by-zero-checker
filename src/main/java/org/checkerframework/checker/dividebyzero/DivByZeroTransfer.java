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

  private AnnotationMirror Zero = reflect(Zero.class);
  private AnnotationMirror Negative = reflect(Negative.class);
  private AnnotationMirror Positive = reflect(Positive.class);
  private AnnotationMirror NonZero = reflect(NonZero.class);
  private AnnotationMirror Bottom = bottom();
  private AnnotationMirror Top = top();

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
    switch (operator) {
      case LT:
        // anything less than zero or negative is negative
        if (equal(rhs, Zero) || equal(rhs, Negative)) {
          return Negative;
        }
        // anything less than top / positive / NZ is unknown
        else if (rhs == Top || equal(rhs, Positive) || equal(rhs, NonZero)) {
          return Top;
        }
        // bottom is empty
        else if (rhs == Bottom) {
          return rhs;
        }
        break;
      case GT:
        if (equal(rhs, Zero) || equal(rhs, Positive)) {
          return Positive;
        }
        else if (rhs == Top || equal(rhs, NonZero) || equal(rhs, Negative)) {
          return Top;
        }
        else if (rhs == Bottom) {
          return rhs;
        }
        break;
      case NE:
        // if x != 0, x == nz
        if(equal(rhs, Zero)) {
          return NonZero;
        }
        else {
          return glb(rhs, lhs);
        }
      case EQ:
        return lub(rhs, lhs);
      case GE:
        if (equal(rhs, Positive)) {
          return rhs;
        }
        else if (rhs == Bottom) {
          return Bottom;
        }
        else {
          return Top;
        }
      case LE:
        if (equal(rhs, Negative)) {
          return rhs;
        }
        else if (rhs == Bottom) {
          return rhs;
        }
        else {
          return Top;
        }
      default:
        // default - we dunno
        return lub(rhs, lhs);
    }
    return Bottom;
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
    if(equal(rhs, Bottom) || equal(lhs, Bottom)) {
      return Bottom;
    }
    // if either are top, return top
    else if(equal(rhs, Top) || equal(lhs, Top)) {
      return Top;
    }
    // if positive lhs, return positive if rhs is positive or zero, else top
    else if(equal(lhs, Positive)) {
      return (equal(rhs, Positive) || equal(rhs, Zero)) ? Positive : Top;
    }
    // if negative lhs, return hegative if rhs is negative or zero, else top
    else if(equal(lhs, Negative)) {
      return (equal(rhs, Negative) || equal(rhs, Zero)) ? Negative : Top;
    }
    // zero plus anything is that anything
    else if(equal(lhs, Zero)) {
      return rhs;
    }
    // nonzero plus zero is nonzero, otherwise top
    else if(equal(lhs, NonZero)) {
      return equal(rhs, Zero) ? NonZero : Top;
    }
    // otherwise we don't know
    else return Top;
  }

  private AnnotationMirror minusTransfer(AnnotationMirror lhs, AnnotationMirror rhs) {
    // if either are bottom, return bottom
    if(equal(rhs, Bottom) || equal(lhs, Bottom)) {
      return Bottom;
    }
    // if either are top, return top
    else if(equal(rhs, Top) || equal(lhs, Top)) {
      return Top;
    }
    // if positive lhs, return positive if rhs is negative or zero, else top
    else if(equal(lhs, Positive)) {
      return (equal(rhs, Negative) || equal(rhs, Zero)) ? Positive : Top;
    }
    // if negative lhs, return negative if rhs is positive or zero, else top
    else if(equal(lhs, Negative)) {
      return (equal(rhs, Positive) || equal(rhs, Zero)) ? Negative : Top;
    }
    // zero minus something
    else if(equal(lhs, Zero)) {
      // 0 - 0 == 0
      if(equal(rhs, Zero)) {
        return Zero;
      }
      // zero - neg == pos, zero - pos == neg
      else return equal(rhs, Positive) ? Negative : Positive;
    }
    // nonzero minus zero is nonzero, otherwise top
    else if(equal(lhs, NonZero)) {
      return equal(rhs, Zero) ? NonZero : Top;
    }
    // otherwise we don't know
    else return Top;
  }

  private AnnotationMirror timesTransfer(AnnotationMirror lhs, AnnotationMirror rhs) {
    // if either are bottom, return bottom
    if(equal(rhs, Bottom) || equal(lhs, Bottom)) {
      return Bottom;
    }
    // if either are zero, return zero
    else if(equal(rhs, Zero) || equal(lhs, Zero)) {
      return Zero;
    }
    // negative * (pos, neg, nz, t)
    else if(equal(lhs, Negative)) {
      // neg * (nz, t) == t
      if(equal(rhs, NonZero) || equal(rhs, Top)) {
        return Top;
      }
      else return (equal(rhs, Negative)) ? Positive : Negative;
    }
    // pos * (pos, neg, nz, t)
    else if(equal(lhs, Positive)) {
      // pos * (nz, t) == t
      if(equal(rhs, NonZero) || equal(rhs, Top)) {
        return Top;
      }
      // pos * neg == neg, pos * pos == pos
      else return (equal(rhs, Negative)) ? Negative : Positive;
    }
    else if(equal(lhs, NonZero)) {
      // nz * top == top
      if (equal(rhs, Top)) {
        return Top;
      }
      // nz * bottom == bottom
      else if (equal(rhs, Bottom)) {
        return Bottom;
      }
      // nz * nonzero (neg, pos, nz) == nz
      else if (equal(rhs, Negative) || equal(rhs, Positive) || equal(rhs, NonZero)) {
        return NonZero;
      }
      // nz * zero == zero
      else if (equal(rhs, Zero)) {
        return Zero;
      }
      else return Top;
    }
    else return Top;
  }
  private AnnotationMirror divideTransfer(AnnotationMirror lhs, AnnotationMirror rhs) {
    // if either are bottom, or bottom has zero (T, 0), return error state (bottom)
    if(equal(rhs, Bottom) || equal(lhs, Bottom) || equal(rhs, Top) || equal(rhs, Zero)) {
      return Bottom;
    }
    // T / anything == T
    else if(equal(lhs, Top)) {
      return Top;
    }
    // positive / 
    else if(equal(lhs, Positive)) {
      // pos / nz == top
      if(equal(rhs, NonZero)) {
        return Top;
      }
      // pos / pos == pos , pos / neg == neg
      else return equal(rhs, Positive) ? Positive : Negative;
    }
    // negative /
    else if(equal(lhs, Negative)) {
      // neg / nz == top
      if(equal(rhs, NonZero)) {
        return Top;
      }
      // neg / pos == neg, neg / neg == pos
      else return equal(rhs, Positive) ? Negative : Positive;
    }
    // nonzero /
    else if(equal(lhs, NonZero)) {
      // nonzero divided by top, bottom, zero, is bottom
      if (equal(rhs, Bottom) || equal(rhs, Top) || equal(rhs, Zero)) {
        return Bottom;
      }
      // otherwise, return top: neg/pos is top, (integer division n/z is top [1 / 7 == 0])
      else return Top;
    }
    else return Top;
  }

  private AnnotationMirror modTransfer(AnnotationMirror lhs, AnnotationMirror rhs) {
    // if either are bottom, or bottom has zero (T, 0), return error state (bottom)
    if(equal(rhs, Bottom) || equal(lhs, Bottom) || equal(rhs, Top) || equal(rhs, Zero)) {
      return Bottom;
    }
    // mod is indeterminate for non-zero values: pos % pos could be pos or zero, neg % neg could be neg or zero, etc
    else return Top;
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

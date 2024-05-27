package org.checkerframework.checker.dividebyzero;

import com.sun.source.tree.*;
import java.lang.annotation.Annotation;
import java.util.EnumSet;
import java.util.Set;
import javax.lang.model.type.TypeKind;
import org.checkerframework.checker.dividebyzero.qual.*;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;

public class DivByZeroVisitor extends BaseTypeVisitor<DivByZeroAnnotatedTypeFactory> {

  /** Set of operators we care about */
  private static final Set<Tree.Kind> DIVISION_OPERATORS =
      EnumSet.of(
          /* x /  y */ Tree.Kind.DIVIDE,
          /* x /= y */ Tree.Kind.DIVIDE_ASSIGNMENT,
          /* x %  y */ Tree.Kind.REMAINDER,
          /* x %= y */ Tree.Kind.REMAINDER_ASSIGNMENT);

  /**
   * Determine whether to report an error at the given binary AST node. The error text is defined in
   * the messages.properties file.
   *
   * @param node the AST node to inspect
   * @return true if an error should be reported, false otherwise
   */
  private boolean errorAt(BinaryTree node) {
    // A BinaryTree can represent any binary operator, including + or -.
    ExpressionTree left = node.getLeftOperand();
    ExpressionTree right = node.getRightOperand();
    
    boolean right_is_int = isInt(right);
    boolean right_is_top = hasAnnotation(right, Top.class);
    boolean right_is_zero = hasAnnotation(right, Zero.class);
    boolean right_is_bottom = hasAnnotation(right, Bottom.class);
    
    boolean retVal = (
      // error if left or right is null
      left == null || right == null ||
      // or we're doing integer division
          (
              right_is_int && DIVISION_OPERATORS.contains(node.getKind()) && (
              // and right is top
              right_is_top ||
              // or it's bottom
              right_is_bottom ||
              // or it's zero
              right_is_zero
            )
          )
    );
    return retVal;
  }

  /**
   * Determine whether to report an error at the given compound assignment AST node. The error text
   * is defined in the messages.properties file.
   *
   * @param node the AST node to inspect
   * @return true if an error should be reported, false otherwise
   */
  private boolean errorAt(CompoundAssignmentTree node) {
    // A CompoundAssignmentTree represents any binary operator combined with an assignment,
    // such as "x += 10".
    ExpressionTree right = node.getExpression();
    ExpressionTree left = node.getVariable();
    
    boolean right_is_int = isInt(right);
    boolean right_is_top = hasAnnotation(right, Top.class);
    boolean right_is_zero = hasAnnotation(right, Zero.class);
    boolean right_is_bottom = hasAnnotation(right, Bottom.class);
    
    boolean retVal = (
      // error if left or right is null
      left == null || right == null ||
      // or we're doing integer division
          (
              right_is_int && DIVISION_OPERATORS.contains(node.getKind()) && (
              // and right is top
              right_is_top ||
              // or it's bottom
              right_is_bottom ||
              // or it's zero
              right_is_zero
            )
          )
    );
    return retVal;
  }

  // ========================================================================
  // Useful helpers

  private static final Set<TypeKind> INT_TYPES = EnumSet.of(TypeKind.INT, TypeKind.LONG);

  private boolean isInt(Tree node) {
    return INT_TYPES.contains(atypeFactory.getAnnotatedType(node).getKind());
  }

  private boolean hasAnnotation(Tree node, Class<? extends Annotation> c) {
    return atypeFactory.getAnnotatedType(node).hasPrimaryAnnotation(c);
  }

  // ========================================================================
  // Checker Framework plumbing

  public DivByZeroVisitor(BaseTypeChecker c) {
    super(c);
  }

  @Override
  public Void visitBinary(BinaryTree node, Void p) {
    if (isInt(node)) {
      if (errorAt(node)) {
        checker.reportError(node, "divide.by.zero");
      }
    }
    return super.visitBinary(node, p);
  }

  @Override
  public Void visitCompoundAssignment(CompoundAssignmentTree node, Void p) {
    if (isInt(node.getExpression())) {
      if (errorAt(node)) {
        checker.reportError(node, "divide.by.zero");
      }
    }
    return super.visitCompoundAssignment(node, p);
  }
}

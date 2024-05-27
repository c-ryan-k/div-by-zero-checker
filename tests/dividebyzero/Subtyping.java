import org.checkerframework.checker.dividebyzero.qual.*;

// Test subtyping relationships for the Divide By Zero Checker.
// The file contains "// ::" comments to indicate expected errors and warnings.

class SubtypeTest {
  void topToTopRelationshipShouldNotError(@Top Integer x) {
    @Top Integer t = x;
  }

  void topToAnyRelationshipShouldError(@Top Integer x) {
    // :: error: assignment
    @Positive Integer a = x;
    // :: error: assignment
    @Negative Integer b = x;
    // :: error: assignment
    @Zero Integer c = x;
    // :: error: assignment
    @NonZero Integer d = x;
    // :: error: assignment
    @Bottom Integer f = x;
  }

  void bottomToAnyRelationshipShouldNotError(@Bottom Integer x) {
    @Positive Integer a = x;
    @Negative Integer b = x;
    @Zero Integer c = x;
    @NonZero Integer d = x;
    @Top Integer e = x;
    @Bottom Integer f = x;
  }

  void allToBottomRelationshipShouldError(@Top Integer a, @Positive Integer b, @Negative Integer c, @Zero Integer d, @NonZero Integer e) {
    // :: error: assignment
    @Bottom Integer m = a;
    // :: error: assignment
    @Bottom Integer n = b;
    // :: error: assignment
    @Bottom Integer o = c;
    // :: error: assignment
    @Bottom Integer p = d;
    // :: error: assignment
    @Bottom Integer q = e;
  }

  void positiveToPositiveRelationshipShouldNotError(@Positive Integer x) {
    @Positive Integer a = x;
  }

  void positiveToNegativeRelationshipShouldError(@Positive Integer x) {
    // :: error: assignment
    @Negative Integer a = x;
  }

  void negativeToNegativeRelationshipShouldNotError(@Negative Integer x) {
    @Negative Integer a = x;
  }

  void negativeToPositiveRelationshipShouldError(@Negative Integer x) {
    // :: error: assignment
    @Positive Integer a = x;
  }

  void zeroToZeroRelationshipShouldNotError(@Zero Integer x) {
    @Zero Integer a = x;
  }

  void zeroToNonZeroRelationshipShouldError(@Zero Integer x) {
    // :: error: assignment
    @NonZero Integer a = x;
  }

  void nonZeroToNonZeroRelationshipShouldNotError(@NonZero Integer x) {
    @NonZero Integer a = x;
  }

  void nonZeroToZeroRelationshipShouldError(@NonZero Integer x) {
    // :: error: assignment
    @Zero Integer a = x;
  }

  void positiveToNonZeroRelationshipShouldNotError(@Positive Integer x) {
    @NonZero Integer a = x;
  }

  void negativeToNonZeroRelationshipShouldNotError(@Negative Integer x) {
    @NonZero Integer a = x;
  }

  void nonZeroToPositiveRelationshipShouldError(@NonZero Integer x) {
    // :: error: assignment
    @Positive Integer a = x;
  }

  void nonZeroToNegativeRelationshipShouldError(@NonZero Integer x) {
    // :: error: assignment
    @Negative Integer a = x;
  }
}

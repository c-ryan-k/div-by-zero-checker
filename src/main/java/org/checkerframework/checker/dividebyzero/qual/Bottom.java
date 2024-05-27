package org.checkerframework.checker.dividebyzero.qual;

import java.lang.annotation.ElementType;
import java.lang.annotation.Target;
import org.checkerframework.framework.qual.SubtypeOf;

@SubtypeOf({ Negative.class, Zero.class, Positive.class })
@Target({ ElementType.TYPE_USE, ElementType.TYPE_PARAMETER })
public @interface Bottom {}

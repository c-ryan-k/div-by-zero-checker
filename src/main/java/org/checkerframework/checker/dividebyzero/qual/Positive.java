package org.checkerframework.checker.dividebyzero.qual;

import java.lang.annotation.ElementType;
import java.lang.annotation.Target;
import org.checkerframework.framework.qual.SubtypeOf;

@SubtypeOf({ NonZero.class })
@Target({ ElementType.TYPE_USE, ElementType.TYPE_PARAMETER })
public @interface Positive {}

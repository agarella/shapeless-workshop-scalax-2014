shapeless-workshop
==================

## Intro

Shapeless is about **generic programming**, not HLists :D

### What is generic programming?

Running question at ICFP Generic Programming workshop: "what is generic programming"... looking for general definition of the term.

 - Programming with kinds of polymorphism that your programming language doesn't support yet

 - Trying to write programs that parameterize over some aspect of the datatypes you're working with.

It's another type of polymorphism. Something more expressive and subtle than what we're used to in our language.

Early research in this area was called "polytypic programming". Programming "with many kinds of types".

Another term used often in this area is "shape polymorphism". We can think of datatypes as having a shape: sequences, lists, trees, graphs. We use the term "shape" here to capture some arrangement of these parts. Can we write programs that operate on values independently of their shape?

### What about HLists? (and Spray and Slick and so on)

HLists are only one part of shapeless. They're useful as an incidental data type. They're an implementation detail. They help get around wrinkles in Scala, e.g. the 22 limit.

*What is the relationship between Shapeless and the libraries that use it (e.g. Spray, Slick)?* Are these libraries also generic programming tools?

In Slick and Spray (and Parboiled 2), they're using HLists to encode an interesting and useful pattern. However, they're not necessarily doing generic programming. In fact, some of these libraries have their own implementation of HLists...

...however, the theory acquired by studying shapeless is useful for understanding these libraries and some of the things you can do with them.

## Part 1: HLists

Let's see an HList:

~~~ scala
scala> 123 :: "abc" :: true :: HNil
res0: shapeless.::[Int,shapeless.::[String,shapeless.::[Boolean,shapeless.HNil]]] = 123 :: abc :: true :: HNil
~~~

This is similar to a list -- for example we can take the head and tail:

~~~ scala
scala> res0.head
res2: Int = 123

scala> res0.tail
res3: shapeless.::[String,shapeless.::[Boolean,shapeless.HNil]] = abc :: true :: HNil
~~~

It's also similar to a tuple in that the element types are preserved:

~~~ scala
scala> res0.tail.head
res4: String = abc

scala> res0(1)
res6: String = abc

scala> res0(0)
res7: Int = 123
~~~

We can also perform more advanced list-like operations such as list concatenation:

~~~ scala
scala> res0 ++ (2.0 :: 'c' :: HNil)
res8: shapeless.::[Int,shapeless.::[String,shapeless.::[Boolean,shapeless.::[Double,shapeless.::[Char,shapeless.HNil]]]]] = 123 :: abc :: true :: 2.0 :: c :: HNil
~~~

<div class="callout callout-info">
*Infix type syntax*

The types printed on the console are rather ugly. In code we can write them infix, which is a lot nicer:

~~~ scala
scala> def x: Int :: String :: Boolean :: Double :: Char :: HNil = ???
x: shapeless.::[Int,shapeless.::[String,shapeless.::[Boolean,shapeless.::[Double,shapeless.::[Char,shapeless.HNil]]]]]
~~~

Note that infix types are not shapeless-specific -- you can write any binary generic type in Scala in infix notation:

~~~ scala
scala> def a: Map[Int, String] = ???
a: Map[Int,String]

scala> def b: Int Map String = ???
b: Map[Int,String]
~~~

This feature is used in one or two places in the Scala standard library (e.g. parser combinators).
</div>

What is an HList? Here's the essence of the definition:

~~~ scala
sealed trait HList
final case class ::[+H, +T <: Hlist](head: H, tail: T) extends HList
final case object HNil extends HList {
  def ::[H](head: H) = ::(head, this)
}
~~~

Like a linked list, an HList is made up of a chain of cons cells. Unlike an HList, however, each node maintains the types of the head and tail. This results in the *type* of an HList mirroring the *values* contained within it.

~~~ scala
scala> HNil
res9: shapeless.HNil.type = HNil

scala> 123 :: HNil
res10: shapeless.::[Int,shapeless.HNil] = 123 :: HNil

scala> "abc" :: 123 :: HNil
res11: shapeless.::[String,shapeless.::[Int,shapeless.HNil]] = abc :: 123 :: HNil
~~~

<div class="callout callout-info">
*Right associative methods*

Scala has a rather eccentric but rather useful syntactic sugar for right-associative operators. Methods ending with a `:` in Scala are right-associative when written in operator form. In other words, the code:

~~~ scala
scala> 123 :: HNil
res10: shapeless.::[Int,shapeless.HNil] = 123 :: HNil
~~~

desugars to:

~~~ scala
scala> HNil.::(123)
res12: shapeless.::[Int,shapeless.HNil] = 123 :: HNil
~~~

instead of `123.::(HNil)` as we might expect.
</div>

The *first* cons cell in an HList is constructed by the `::` method on `HNil`. When we construct the *second* cons cell, however, the `::` we're using is actually the `apply` method on the `::` case class:

~~~ scala
scala>  ::("123", HNil.::(123))
res0: shapeless.::[String,shapeless.::[Int,shapeless.HNil]] = 123 :: 123 :: HNil
~~~

### Head and tail

The `head` and `tail` methods on an HList are defined as *extension methods* on `HCons`. Because each `HCons` cell has its own type parameters, the result types of the methods are exactly the element types.

Another interesting property is that getting the `tail` of `HNil` is actually a compile error (as `HNil` doesn't have a `tail` method):

~~~ scala
scala> (123 :: "abc" :: HNil).tail.tail.tail
<console>:17: error: could not find implicit value for parameter c: shapeless.ops.hlist.IsHCons[shapeless.HNil]
              (123 :: "abc" :: HNil).tail.tail.tail
~~~

Methods like `head` and `tail` are defined as *extension methods*. They are defined in a class called `HListOps` and all take an implicit argument of the type class `IsHCons`. shapeless can construct an `IsHCons` for a given head and tail type. See the `hlistIsHCons` method on the `IsHCons` companion object:

~~~ scala
scala> import ops.hlist._
import ops.hlist._

scala> the[IsHCons[Int :: String :: Boolean :: HNil]]
res3: shapeless.ops.hlist.IsHCons.Aux[shapeless.::[Int,shapeless.::[String,shapeless.::[Boolean,shapeless.HNil]]],Int,shapeless.::[String,shapeless.::[Boolean,shapeless.HNil]]] = shapeless.ops.hlist$IsHCons$$anon$116@243e39b8

// Human readable version of this type signature:
// IsHCons.Aux[
//   Int :: String :: Boolean :: HNil,
//   Int,
//   String :: Boolean :: HNil]

scala> the[IsHCons[HNil]]
<console>:20: error: could not find implicit value for parameter t: shapeless.ops.hlist.IsHCons[shapeless.HNil]
              the[IsHCons[HNil]]
                 ^
~~~

**ASIDE:** The `the` method is a shapeless version of `implicitly`. It preserves more type information than `implicitly`, but the two are largely interchangeable.

**DOUBLE ASIDE:** The `Aux` type here is for two reasons: first it's slightly more syntactically convenient than `IsHCons[...] { type H = ...; type T = ... }`. Secondly it allows us to constrain types in certain ways, which we'll see later on.

This indirection is present because it works around problems involving covariance and contravanriance. HList is covariant, but we want to write operations involving head and tail types in contravariant positions. Defining these methods as extension methods allows us to do this kind of thing without type errors.

### Length of an HList

Let's look at something which is representative of a lot of the more advanced operations on HLists: the length of the list.

We can compute the length of an HList *at compile time*. shapeless has a type-level representation of natural numbers, and can compute list length as follows:

~~~ scala
scala> 123 :: "abc" :: true :: HNil
res6: shapeless.::[Int,shapeless.::[String,shapeless.::[Boolean,shapeless.HNil]]] = 123 :: abc :: true :: HNil

scala> res6.length
res7: shapeless.Succ[shapeless.Succ[shapeless.Succ[shapeless._0]]] = Succ()
~~~

Let's look at what's going on here. `Succ` and `_0` are subtypes of `Nat`, which are shapeless' implementation of piano numerals:

~~~ scala
trait Nat {
  type N <: Nat
}

case class Succ[P <: Nat]() extends Nat {
  type N = Succ[P]
}

class _0 extends Nat {
  type N = _0
}
~~~

Given these types, we can define types to represent any positive integer:

~~~ scala
// 1:
scala> def x: Succ[_0] = ???
x: shapeless.Succ[shapeless._0]

// 2:
scala> def y: Succ[Succ[_0]] = ???
x: shapeless.Succ[shapeless.Succ[shapeless._0]]
~~~

There is a trait `Length` that uses these types to compute the length of a list:

~~~ scala
trait Length[L <: HList] extends DepFn0 { type Out <: Nat }

object Length {
  def apply[L <: HList](implicit length: Length[L]): Aux[L, length.Out] = length

  import shapeless.nat._
  type Aux[L <: HList, N <: Nat] = Length[L] { type Out = N }
  implicit def hnilLength[L <: HNil]: Aux[L, _0] = new Length[L] {
    type Out = _0
    def apply(): Out = _0
  }

  implicit def hlistLength[H, T <: HList, N <: Nat](implicit lt : Aux[T, N], sn : Witness.Aux[Succ[N]]): Aux[H :: T, Succ[N]] = new Length[H :: T] {
    type Out = Succ[N]
    def apply(): Out = sn.value
  }
}
~~~

`Length.apply` takes a type parameter `L <: HList` and an implicit value of type `Length` and uses it to compute the length of `L`. The two methods `hnilLength` and `hlistLength` generate implicit `Lengths` for `HCons` and `HNil` types respectively.

Implicit resolution proceeds recursively, working down the `HList` type until it reaches `HNil`. In other words, `hnilLength` and `hlistLength` are essentially a type-level structural recursion, performed by the type-checker at compile time. The results of the computation are:

 - most importantly a type, and;
 - less importantly a run-time value to retrieve the corresponding length.

### Aside: Type-Level Natural Numbers

To convert a `Nat` to an `Int`, we use a `ToInt` type class. This recursively locates implicits and uses them to compute the run-time value of the type-level natural number:

~~~ scala
scala> import ops.nat._
import ops.nat._

scala> Succ[Succ[Succ[_0]]].toInt
<console>:23: error: value toInt is not a member of shapeless.Succ[shapeless.Succ[shapeless.Succ[shapeless._0]]]
              Succ[Succ[Succ[_0]]].toInt

// TODO: Fix this example!
~~~

The conversion of a type-level number to a run-time value is generally unimportant to shapeless. We're interested in types and type-level representations.

### Mapping onto a constant

The `mapConst` method is perhaps the next most complex example. It maps each item in the list onto a constant value:

~~~ scala
scala> (123 :: "abc" :: true :: HNil).mapConst(10)
res10: shapeless.::[Int,shapeless.::[Int,shapeless.::[Int,shapeless.HNil]]] = 10 :: 10 :: 10 :: HNil
~~~

A good use case for this is... suppose you have an HList representing a row in a table. You may want to generate an HList of the same length column headings, all of type `String`.

Let's look at the code:

~~~ scala
/**
 * Replaces each element of this `HList` with a constant value.
 */
def mapConst[C](c : C)(implicit mapper : ConstMapper[C, L]) : mapper.Out = mapper(c, l)

// ...

trait ConstMapper[C, L <: HList] extends DepFn2[C, L] { type Out <: HList }

object ConstMapper {
  def apply[C, L <: HList](implicit mapper: ConstMapper[C, L]): Aux[C, L, mapper.Out] = mapper

  type Aux[C, L <: HList, Out0 <: HList] = ConstMapper[C, L] { type Out = Out0 }

  implicit def hnilConstMapper[C]: Aux[C, HNil, HNil] =
    new ConstMapper[C, HNil] {
      type Out = HNil
      def apply(c : C, l : HNil): Out = l
    }

  implicit def hlistConstMapper[H, T <: HList, C]
  (implicit mct : ConstMapper[C, T]): Aux[C, H :: T, C :: mct.Out] =
      new ConstMapper[C, H :: T] {
        type Out = C :: mct.Out
        def apply(c : C, l : H :: T): Out = c :: mct(c, l.tail)
      }
}
~~~

This has a similar structure to before. The `apply` method of `ConstMapper` does the work by requiring an implicit value of type `ConstMapper`. `hnilConstMapper` and `hlistConsMapper` do the work for us by computing `ConsMappers` for `HNil` and `HCons` types respectively. Again, the implicit resolution is recursive and allows the compiler to compute the correct result type.

### Reversing an HList

Reversing an HList works similarly to calculating its length. Here's the code:

~~~ scala
trait Reverse[L <: HList] extends DepFn1[L] { type Out <: HList }

object Reverse {
  def apply[L <: HList](implicit reverse: Reverse[L]): Aux[L, reverse.Out] = reverse

  type Aux[L <: HList, Out0 <: HList] = Reverse[L] { type Out = Out0 }

  implicit def reverse[L <: HList, Out0 <: HList](implicit reverse : Reverse0[HNil, L, Out0]): Aux[L, Out0] =
    new Reverse[L] {
      type Out = Out0
      def apply(l : L) : Out = reverse(HNil, l)
    }

  trait Reverse0[Acc <: HList, L <: HList, Out <: HList] {
    def apply(acc : Acc, l : L) : Out
  }

  object Reverse0 {
    implicit def hnilReverse[Out <: HList]: Reverse0[Out, HNil, Out] =
      new Reverse0[Out, HNil, Out] {
        def apply(acc : Out, l : HNil) : Out = acc
      }

    implicit def hlistReverse[Acc <: HList, InH, InT <: HList, Out <: HList]
      (implicit rt : Reverse0[InH :: Acc, InT, Out]): Reverse0[Acc, InH :: InT, Out] =
        new Reverse0[Acc, InH :: InT, Out] {
          def apply(acc : Acc, l : InH :: InT) : Out = rt(l.head :: acc, l.tail)
        }
  }
}
~~~

### Polymorphic Map

So far we've seen `mapConst`, which is a fairly restrictive implementation of `map`. There's not a lot of difference between `mapConst` on an `HList` and `mapConst` on a `List`, in that "mapping function" returns the same type for each element in the list.

Now let's look at a full *polymorphic map* in shapeles. Let's create a shapeless `Poly` -- a polymorphic function:

~~~ scala
scala> import poly._
import poly._

scala> object singleton extends (Id ~> Set) {
     |   def apply[T](t: T) = Set(t)
     | }
defined object singleton

scala> singleton(1)
res11: scala.collection.immutable.Set[Int] = Set(1)

scala> singleton("abc")
res12: scala.collection.immutable.Set[String] = Set(abc)
~~~

Now -- why is this interesting? After all, we can implement the same behaviour with a standard generic method:

~~~ scala
scala> def sing[T](in: T): Set[T] = Set(in)
sing: [T](in: T)Set[T]

scala> sing(1)
res13: Set[Int] = Set(1)

scala> sing("abc")
res14: Set[String] = Set(abc)
~~~

Despite these superficial similarities, polymorphic functions in shapeless are in fact different to Scala methods in a couple of ways.

Scala methods, as we know, have 1:1 correspondence with JVM methods.   Scala does a great job of masking the difference between methods and   functions (objects with an `apply` method), but the differences still leak through in certain circumstances:

~~~ scala
scala> val sing2 = (in: Int) => Set(in)
sing2: Int => scala.collection.immutable.Set[Int] = <function1>

scala> sing.hashCode
<console>:27: error: missing arguments for method sing;
follow this method with `_' if you want to treat it as a partially applied function
              sing.hashCode
              ^

scala> sing2.hashCode
res16: Int = 1180035200
~~~

Now, methods are polymorphic but functions are monomorphic. There's no way of defining a polymorphic function in regular Scala:

~~~ scala
scala> val sing3: T => Set[T] = (in: T) => Set(in)
<console>:25: error: not found: type T
       val sing3: T => Set[T] = (in: T) => Set(in)
                  ^
<console>:25: error: not found: type T
       val sing3: T => Set[T] = (in: T) => Set(in)
                           ^
<console>:25: error: not found: type T
       val sing3: T => Set[T] = (in: T) => Set(in)
~~~

We can define a polymorphic method that *returns* a function, but this has limitations. For example, what if we want to write a function that accepts a polymorphic function as an input? The closes we can get is to possibly write:

~~~ scala
scala> def frob[T](fn: T => Int): Int = { fn(23) + fn("foo") }
<console>:25: error: type mismatch;
 found   : String("foo")
 required: T
       def frob[T](fn: T => Int): Int = { fn(23) + fn("foo") }
                                                      ^
~~~

but this binds `T` at the method level, not at the level of the argument function.

shapeless works around this by defining a *polymorphic function* that maps between generic type constructors:

~~~ scala
// TODO: Include some snippet of the definition of `Poly1`
~~~

Instances of `Poly1` use implicit values to locate implementations for specific parameter types:

~~~ scala
scala> the[singleton.Case[Int]]
res99: singleton.Case[Int] = // unimportant long toString output
~~~

We can `map` over an `HList` using a `Poly1` provided the compiler can locate an implicit `Case` for each element type:

~~~ scala
scala> (123 :: "abc" :: true :: HNil) map singleton
res0: shapeless.::[scala.collection.immutable.Set[Int],shapeless.::[scala.collection.immutable.Set[String],shapeless.::[scala.collection.immutable.Set[Boolean],shapeless.HNil]]] = Set(123) :: Set(abc) :: Set(true) :: HNil
~~~

TODO: Mention REPL bugs ??

Let's look at the implementation:

`map` is an extension method that takes a `Mapper` implicit:

~~~ scala
def map(f : Poly)(implicit mapper : Mapper[f.type, L]) : mapper.Out =
  mapper(l)
~~~

The `Mapper` does the job of mapping using the implicits available for `Poly`:

~~~ scala
trait Mapper[HF, In <: HList] extends DepFn1[In] { type Out <: HList }

object Mapper {
  def apply[F, L <: HList](implicit mapper: Mapper[F, L]): Aux[F, L, mapper.Out] = mapper

  type Aux[HF, In <: HList, Out0 <: HList] = Mapper[HF, In] { type Out = Out0 }

  implicit def hnilMapper1[HF]: Aux[HF, HNil, HNil] =
    new Mapper[HF, HNil] {
      type Out = HNil
      def apply(l : HNil): Out = HNil
    }

  implicit def hlistMapper1[HF <: Poly, InH, InT <: HList]
    (implicit hc : Case1[HF, InH], mt : Mapper[HF, InT]): Aux[HF, InH :: InT, hc.Result :: mt.Out] =
      new Mapper[HF, InH :: InT] {
        type Out = hc.Result :: mt.Out
        def apply(l : InH :: InT): Out = hc(l.head) :: mt(l.tail)
      }
}
~~~

Once again, the compiler is doing the work for us. In order to apply our `Poly` to the head of our list, we need to locate a `Case` for the `Poly` type and the head type. This is located implicitly (we'll discuss where in a moment) and we use it to build a `Mapper` that converts the head of the list. The other thing we need to build a `Mapper` is an implicitly resolved `Mapper` for the tail, and so the process recurses.

Now let's look at a general implementation of a `Poly`:

~~~ scala
object doRandomStuff extends Poly1 {
  implicit val caseInt     = at[Int](num => num * 1000)
  implicit val caseString  = at[String](str => str + "!!!")
  implicit def caseList[T] = at[List[T]](lis => lis.reverse)
}
~~~

The `at` method in this code comes from `Poly1`. It returns a `Case` for the singleton type of the function and the relevant argument type. Let's apply this function to a few arguments:

~~~ scala
scala> doRandomStuff(123)
res1: doRandomStuff.caseInt.Result = 123000

scala> doRandomStuff("abc")
res2: doRandomStuff.caseString.Result = abc!!!

scala> doRandomStuff(List(1, 2, 3))
res3: List[Int] = List(3, 2, 1)

scala> doRandomStuff(true)
<console>:18: error: could not find implicit value for parameter cse: shapeless.poly.Case[doRandomStuff.type,shapeless.::[Boolean,shapeless.HNil]]
              doRandomStuff(true)
                           ^
~~~

The `apply` method on `doRandomStuff` takes an explicit argument of type `T` and an implicit argument of type `Case[doRandomStuff.type, T]`. The return type of `apply` is determined by the return type of the `Case`.

There are implicit instances of `Case[doRandomStuff.type, T]` for `T` equal to `Int`, `String`, and any `List[X]`, but no instance for `Boolean`.

How does the compiler locate the implicit values for each `T`? Because the singleton type of the `Poly` is a type parameter on `Case`, the implicit scope for `Case` extends to the companion object for `doRandomStuff.type`... which turns out to be `doRandomStuff` itself. In other words, if we're looking for an implicit of type `Case[doRandomStuff.type, Int]`, then `doRandomStuff.caseInt` is implicitly available everywhere in our codebase.

## Generics

HLists are all well and good, but we typically don't want to use them directly in our code. Let's talk about something that links *useful* data types with HLists: `Generics`:

~~~ scala
scala> case class Foo(num: Int, str: String)
defined class Foo

scala> val fooGen = Generic[Foo]
fooGen: shapeless.Generic[Foo]{type Repr = shapeless.::[Int,shapeless.::[String,shapeless.HNil]]} = fresh$macro$5$1@6933ca1
~~~

The job of a `Generic` is to provide a bidirectional mapping between a "friendly" data type -- in this case `Foo` -- and a generic representation type. The representation type for `Foo` is an `Int :: String :: HNil`. We can convert back and forth between the two types using the `to` and `from` methods on the generic:

~~~ scala
scala> fooGen.to(Foo(123, "abc"))
res0: fooGen.Repr = 123 :: abc :: HNil

scala> fooGen.from(res0)
res1: Foo = Foo(123,abc)

scala> fooGen.from(321 :: res0.tail)
res2: Foo = Foo(321,abc)
~~~

This gives us easy data interchange between similar "friendly" data types:

~~~ scala
scala> case class Foo1(num: Int, str: String)
defined class Foo1

scala> val fooGen1 = Generic[Foo1]
fooGen1: shapeless.Generic[Foo1]{type Repr = shapeless.::[Int,shapeless.::[String,shapeless.HNil]]} = fresh$macro$10$1@6cffb4fc

scala> fooGen1.from(fooGen.to(Foo(123, "abc")))
res3
~~~

Here's another example. Let's define a mechanism to take any two-element case class and swap the elements:

~~~ scala
scala> case class Numbers(a: Int, b: Int)
defined class Numbers

scala> implicit val numGen = Generic[Numbers]
numGen: shapeless.Generic[Numbers]{type Repr = shapeless.::[Int,shapeless.::[Int,shapeless.HNil]]} = fresh$macro$22$1@297c3f1c

scala> def swap[T, E](value: T)(implicit gen: Generic.Aux[T, E :: E :: HNil]): T = {
     |   val a :: b :: HNil = gen.to(value)
     |   gen.from(b :: a :: HNil)
     | }
swap: [T, E](value: T)(implicit gen: shapeless.Generic.Aux[T,shapeless.::[E,shapeless.::[E,shapeless.HNil]]])T

scala> swap(Numbers(123, 456))
res6: Numbers = Numbers(456,123)
~~~

This works with any case class with two elements of the same type:

~~~ scala
scala> implicit val strGen = Generic[Strings]
strGen: shapeless.Generic[Strings]{type Repr = shapeless.::[String,shapeless.::[String,shapeless.HNil]]} = fresh$macro$27$1@eeacb66

scala> swap(Strings("Hello", "world"))
res7: Strings = Strings(world,Hello)
~~~

Let's relax things slightly by generalising. Now we'll swap the first two elements in a case class of *n* elements. This will work on any case class with the first two elements the same:

~~~ scala
scala> def swap2[T, U <: HList, H, T1 <: HList, T2 <: HList](value: T)(
     |   implicit
     |     gen: Generic.Aux[T, U],
     |     isc1: IsHCons.Aux[U, H, T1],
     |     isc2: IsHCons.Aux[T1, H, T2],
     |     ev: (H :: H :: T2) =:= U
     |   ): T = {
     |   val u = gen.to(value)
     |   gen.from(u.tail.head :: u.head :: u.tail.tail)
     | }
defined swap2

scala> case class Bar(a: Int, b: Int, c: String)
defined class Bar

scala> implicit val barGen = Generic[Bar]
barGen: shapeless.Generic[Bar]{type Repr = shapeless.::[Int,shapeless.::[Int,shapeless.::[String,shapeless.HNil]]]} = fresh$macro$34$1@48f19acf

scala> swap2(Bar(1, 2, "3"))
res8: Bar = Bar(2,1,3)

scala> swap2(Bar(1, 2, "abc"))
res9: Bar = Bar(2,1,abc)
~~~

The definition of `swap2` specifies a lot of constraints on the input types `T` and `U` using implicits. TODO: Include notes on the order of implicit resolution and its implications on how we order and design our constraints.

## Generics for Coproducts

shapeless is also able to generate generics for sealed families of case classes:

~~~ scala
scala> :paste
// Entering paste mode (ctrl-D to finish)

sealed trait Animal
final case class Dog(name: String) extends Animal
final case class Hamster(wheels: Int) extends Animal


// Exiting paste mode, now interpreting.

defined trait Animal
defined class Dog
defined class Hamster

scala> Generic[Animal]
res16: shapeless.Generic[Animal]{type Repr = shapeless.:+:[Dog,shapeless.:+:[Hamster,shapeless.CNil]]} = fresh$macro$67$1@2229a060
~~~

The resulting `Generic` here maps instances of `Animal` to shapeless Coproducts, written `:+:`:

~~~ scala
scala> def x : Dog :+: Hamster :+: CNil = ???
x: shapeless.:+:[Dog,shapeless.:+:[Hamster,shapeless.CNil]]
~~~

The definition of `Coproduct` is similar to the definition of `HList`. It allows us to represent arbitrary disjunctions of types:

~~~ scala
sealed trait Coproduct

sealed trait :+:[+H, +T <: Coproduct] extends Coproduct

final case class Inl[+H, +T <: Coproduct](head : H) extends :+:[H, T] {
  override def toString = head.toString
}

final case class Inr[+H, +T <: Coproduct](tail : T) extends :+:[H, T] {
  override def toString = tail.toString
}

sealed trait CNil extends Coproduct
~~~

Let's see the representations of some animals:

~~~ scala
scala> animalGen.to(Dog("Sparky"))
res17: animalGen.Repr = Dog(Sparky)

scala> animalGen.to(Hamster(1))
res18: animalGen.Repr = Hamster(1)

scala> animalGen.from(res17)
res19: Animal = Dog(Sparky)

scala> animalGen.from(res18)
res20: Animal = Hamster(1)
~~~

TODO: More on coproducts... I don't understand exactly what the values look like, which would undoubtedly help.

### Records and Labelled Generics

Shapeless has a *record* type that allows us to create named representations of data structures:

~~~ scala
scala> import syntax.singleton._
import syntax.singleton._

scala> val dog = 'name ->> "Tigger" :: HNil
dog: shapeless.::[String with shapeless.labelled.KeyTag[Symbol with shapeless.tag.Tagged[String("name")],String],shapeless.HNil] = Tigger :: HNil

scala> import record._
import record._

scala> dog('name)
res0: String = Tigger
~~~

If we specify an invalid symbolic field name, we get a compile error:

~~~ scala
scala> res2('foo)
<console>:28: error: No field Symbol with shapeless.tag.Tagged[String("foo")] in record shapeless.::[String with shapeless.labelled.KeyTag[Symbol with shapeless.tag.Tagged[String("name")],String],shapeless.HNil]
              res2('foo)
                  ^
~~~

We can define a `LabelledGeneric` for our `Dog` type that converts instances of that type to records:

~~~ scala
scala> val lgen = LabelledGeneric[Dog]
lgen: shapeless.LabelledGeneric[Dog]{type Repr = shapeless.::[String with shapeless.labelled.KeyTag[Symbol with shapeless.tag.Tagged[String("name")],String],shapeless.HNil]} = fresh$macro$7$1@59997770

scala> val ldog = lgen.to(Dog("Sparky"))
ldog: lgen.Repr = Sparky :: HNil

scala> ldog('name)
res3: String = Sparky
~~~

So what's going on here? A record is actually an HList-like data structure that contains type-level representations of field names as well as field values.

This relies on a concept called *singleton types*, which is a Scala thing not a shapeless thing. Here's an example in plain Scala:

~~~ scala
scala> def sing[T <: String](t: T): Option[t.type] = Some(t)
sing: [T <: String](t: T)Option[t.type]

scala> sing("foo")
res5: Option[String("foo")] = Some(foo)
~~~

Here, the type of the result contains a reference to the singleton type of the string `"foo"`. This is the type shapeless is using when we write `ldog('name)` -- it provides the means to recurse over the record structure at compile time and locate the item tagged with the relevant field name.

## HMaps

shapeless includes an implementation of heterogeneous maps, which associates keys with values provided there is implicit evidence to allow them to be associated:

~~~ scala
scala> trait AuthRel[K, V]
defined trait AuthRel

scala> trait OAuth
defined trait OAuth

scala> trait Basic
defined trait Basic

scala> case class OUser()
defined class OUser

scala> case class BUser()
defined class BUser

scala> implicit val oRel: AuthRel[OAuth, OUser] = new AuthRel[OAuth, OUser] {}
oRel: AuthRel[OAuth,OUser] = $anon$1@1bbc39bf

scala> implicit val bRel: AuthRel[Basic, BUser] = new AuthRel[Basic, BUser] {}
bRel: AuthRel[Basic,BUser] = $anon$1@5c8ce934

scala> val o1 = new OAuth {}
o1: OAuth = $anon$1@74576c13

scala> val b1 = new Basic {}
b1: Basic = $anon$1@4dce7e7f

scala> val ou1 = OUser()
ou1: OUser = OUser()

scala> val bu1 = BUser()
bu1: BUser = BUser()

scala> hm + (o1 -> ou1)
<console>:35: error: type mismatch;
 found   : (OAuth, OUser)
 required: String
              hm + (o1 -> ou1)
                       ^

scala> val hm = HMap[AuthRel].empty
<console>:31: error: value empty is not a member of shapeless.HMapBuilder[AuthRel]
       val hm = HMap[AuthRel].empty
                              ^

scala> val hm = HMap.empty[AuthRel]
hm: shapeless.HMap[AuthRel] = shapeless.HMap@7261ac56

scala> hm + (o1 -> ou1)
res10: shapeless.HMap[AuthRel] = shapeless.HMap@1d411294

scala> hm + (o1 -> ou1) + (b1 -> bu1)
res11: shapeless.HMap[AuthRel] = shapeless.HMap@5b84bdad

scala> hm + (o1 -> ou1) + (b1 -> bu1) + (o1 -> bu1)
<console>:37: error: could not find implicit value for parameter ev: AuthRel[OAuth,BUser]
              hm + (o1 -> ou1) + (b1 -> bu1) + (o1 -> bu1)
                                             ^

scala> res10.get(o1)
res15: Option[OUser] = Some(OUser())

scala> res10.get(b1)
res17: Option[BUser] = None
~~~

The map guarantees the type of the result given a particular key, but doesn't guarantee the presence of a value in the map.

## Automatic Type Class Instance Derivation

Big jump here. We're moving from low-level building blocks to a high-level abstraction. In many cases we can mechanically generate type class instances for case classes and sealed families of case classes, provided we already have instances for the leaf types.

Here's an example that auto-generates type classes for scalaz `Monoids`:

~~~ scala
implicit val monoidInstance: ProductTypeClass[Monoid] = new ProductTypeClass[Monoid] {
  def emptyProduct = new Monoid[HNil] {
    def zero = HNil
    def append(a : HNil, b : HNil) = HNil
  }

  def product[F, T <: HList](FHead : Monoid[F], FTail : Monoid[T]) = new Monoid[F :: T] {
    def zero = FHead.zero :: FTail.zero
    def append(a : F :: T, b : F :: T) = FHead.append(a.head, b.head) :: FTail.append(a.tail, b.tail)
  }

  def project[F, G](instance : => Monoid[G], to : F => G, from : G => F) = new Monoid[F] {
    def zero = from(instance.zero)
    def append(a : F, b : F) = from(instance.append(to(a), to(b)))
  }
}

// A pair of arbitrary case classes
case class Foo(i : Int, s : String)
case class Bar(b : Boolean, s : String, d : Double)

// Automatically they're monoids ...
{
  import Monoid.auto._
  val f = Foo(13, "foo") |+| Foo(23, "bar")
  assert(f == Foo(36, "foobar"))
}

// ... or explicitly
{
  implicit val barInstance = Monoid[Bar]

  val b = Bar(true, "foo", 1.0) |+| Bar(false, "bar", 3.0)
  assert(b == Bar(true, "foobar", 4.0))
}
~~~

The three things we need to define are:

 - a type class instance for `HNil`;
 - a type class instance for `HCons`;
 - a `project` method that generates a type class instance for a type `F` given an instance
   for a type `G` and a pair of bidirectional conversion functions.

Monoids are only defined for products (not coproducts). Let's see an example that takes coproducts into account -- generic serialization to/from s-expressions! See `sexp.scala`, which uses a type class called `LabelledTypeClass` to generate a generalized `SexprConvert` type class for products and coproducts. In other words, we get type classes for *all* families of case classes.

TODO: If you try to derive a type class instance for an intermediate type in a type hierarchy, shapeless will issue a warning telling you you may want to switch your code to the supertype. You can add an import to your code (`DeriveConstructors._` ??) to suppress the warning.
Note:
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



---
author: "Samuel Toth"
desc: "Explanation of foldr categorically"
keywords: "hakell, categories"
lang: "en"
title: "Foldr, datatypes and (scary sounding but not so scary) F-algebras"
---

# Foldr, datatypes and (scary sounding but not so scary) F-algebras

## Recap on Haskell data types and polynomials

As we learnt in the lectures, Haskell has a feature called algabraic data types. What this means is that there are product types, the tuples (including the empty tuple `()`), as well as sum types, written in Haskell with the bar notation `data MyType = A | B`.
They can be thought of as something like an 'or' type.(*1)

There exists an alternative notation for data types which hints at a suggestion to something we are all familiar with from school: Polnomials!

Instead of writing tuples `(a , b)`, we choose to write $a \times b$, and instead of sums such as `data Blah = Foo | Baz` we write
$Foo + Baz$. Additionally, the empty tuple `()` is written as just $1$. This seems strange maybe at first sight; however, when looking at finite types, you start to see the motivation: Consider `Bool` as a 2 element type. In this alternative notation we might write `Bool` as $\mathbb{2}$. After some consideration you might see that the type `data Three = A Bool | B ()` has three possible values... so now the notation $\mathbb{3} = \mathbb{2} + 1$ is starting to look very sensible indeed. (Consider what the type $\mathbb{2} \times \mathbb{1}$ represents... no prizes for getting that it is equal to $\mathbb{2}$)

Now almost every data type in haskell can be written as a combination of products and sums (and function types (4*)), however, there is one thorny case to consider - and sadly or happily, i'm not sure... these outliers are the most intersting and usefull kinds of data types, namely recursive types.

## Recursive data types

When we write a recursive data type such as `[a]` (defined for reference below), there doesn't seem to be a good way to turn it into a simple combination of products and sums of existing types or type variables.

```haskell
data [a] = [] | (::) a [a]
```
(^^ not exactly real haskell)

I am hoping the answer to this question of how to represent that data type mathmatically will give some insight onto why the foldr function works as it does and how you can derive similar functions for the data types you've cooked at home.

So... the solution is to write a polnomial function!!

$List_A(X) = 1 + A \times X$

For a fixed type `A`, this list is a polnomial function in 1 variable, X. The reason why this is the right choice of polynomial
is that if you imagined the type when you replace X with the desired recursive type, you get exactly the type you desire,
$List(A) = 1 + A \times List(A)$. You might then recognise that the type we desire is a fixed point for this function (although it doesn't matter if you have never encountered fix points before).

We shall now go on to explain, using Haskell code, how the list type relates to this polynomial and how this relationship gives us the foldr function for free!

## Algebra for Polynomials:

First a quick definition. An algebra for one of our polnomial type functions (call it `F`) is a particular choice of type, call it `b`, and function: `F b -> b`. Very simple so far!

Unfolding this definition in particular for lists, this means we want a function:
$$1 + a * b \to b$$ 
Now take a moment to understand how each of the following types are equivalent to the type above (hint think about how you would define them all as functions in haskell):


<details>
  <summary>Spoilers</summary>
  universal property of coproducts (sum types)
</details>

$$(1 \to b) \times (a \times b \to b)$$

<details>
  <summary>Spoilers</summary>
  `() -> a` is equivalent to just `a`. 
  Can also think about the type in the exponential notation $a^1 = a$
</details>

$$b \times (a \times b \to b)$$

<details>
  <summary>Spoilers</summary>
  currying right hand side of product
</details>

$$b \times (a \to b \to b)$$

<details>
  <summary>Spoilers</summary>
  we can happily swap the order of products
</details>

$$(a \to b \to b) \times b$$

For reasons that will become aparent very shortly (and you might already have spotted) this is the form of the type that we want.
```haskell
data ListAlgebra a b = ListAlgebra (a -> b -> b) b
```

We say that the haskell type `[a]` is the _initial_ list algebra.

Firstly, lets validate that there is a sensible definition of ListAlgebra for `[a]`:

```haskell
listListAlg :: ListAlgebra a [a]
listListAlg = ListAlgebra (::) []
```

This feels like a very sensible definition - which is always a good sign.

Now onto what it means for something to be an initial algebra. An algebra is initial when there is a map from it
to any other arbritary algebra. (*2)

```haskell
listListAlgInit :: ListAlgebra a b -> [a] -> b
listListAlgInit (ListAlgebra _ empty) [] = empty
listListAlgInit (ListAlgebra app empty) (x:xs) = app x (listListAlgInit (ListAlgebra app empty) xs)
``` 
(*3)

We can read the above type as for any listAlgebra `b` there is a function from `[a]` to `b`.

Et voila. We only have to a simple bit of rearranging and unfolding and currying to get to the fact that this type is equivalent to `foldr :: (a -> b -> b) -> b -> [a] -> b`.

Hopefully this helps understanding and motivating the foldr function and was interesting :)

Also note that we can pull this trick for any haskell data type we like and find the 'natural' 'fold' function by looking at it's type of algebras.
Maybe looking at the natural numbers and deriving the fold function for them could be a useful exersize.

hint: natural numbers are defined by the polynomial:
<details>
  <summary>hint</summary>
  $F(X) = 1 + X$
  
</details>

### An extra: A lazy thorn in the side

Lazyness in Haskell has a way of making the above story unfortunately slightly untrue :(
The particular gadget we have been talking about in full technicality are [initial algebras of polynomial endofunctors](https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor). But if you define a function using foldr on an infinite list, haskell won't be happy with you. The reason for this is that laziness in haskell in a sense conflates inductive and coinductive data types. A list in haskell can be both a list or a stream. Most other languages either don't have these infinite (coinductive) data types or choose to explicitely seperate when a data type can be infinite (total languages such as agda and idris and lean) often by being able to define `data SuchAndSuch ...` and `codata CoSuchAndSuch ...`. Semantically this can be achieved using the categorical dual to initial algebras, the creatively named final coalgebras. To go into detail is too much here but more info can be found at [the nlab](https://ncatlab.org/nlab/show/terminal+coalgebra+for+an+endofunctor). [This blog post](http://blog.sigfpe.com/2007/07/data-and-codata.html) is also a very interesting read on the topic.

### Technical details:
(*1): If you want to learn more about this I would reccomend looking up category theory and in particular trying to understand what it means when a category is (bi)cartesian closed. In category theory speak tuples correspond to finite products, sum types to finite coproducts and function types to exponential objects. If you are interested in category theory, I am always happy to chat about it in the discord :) - it's my favorite topics in maths/cs.


(*2): We can actually show that this is the only reasonable definition (up to unique isomorphism). This happens because we really want to place more restrictions on the type 
of map that counts as a map of F-algebras [more detail here](https://ncatlab.org/nlab/show/algebra+for+an+endofunctor). We also would need to show that the map witnessing initiality is unique (up to unique isomorphism).
It is possible (by [generalised abstract nonsense](https://en.wikipedia.org/wiki/Abstract_nonsense)) to show that the uniqueness of this map gives us the uniqueness of the initial algebra.

(*3): This could be equally - or arguably better-ly - implemented as a haskell typeclass, getting rid of a lot of noise in the definition.
But keeping it simple with a datatype seemed like a reasonable tradeoff.

(*4): Function types are written as exponentials in this notation `a -> b` corresponds to $b^a$. Again, it is worth verifying to yourself why this is the case by using finite types as intuition. E.g. how many functions are there from Bool to Bool.
module Syntax
export
  BaseExpr, ObExpr, MorExpr, head, args,
  as_sexpr, show_sexpr, as_infix, show_infix,
  ob, mor, dom, codom, id, compose, ∘,
  otimes, munit, ⊗

import Base: ==
using Match
using Typeclass
import ..Doctrine

# Expressions
#############

""" Base type for expressions in categorical languages.

We define Julia types for each "kind" or "metatype" in the language: currently
*object* and *morphism*, perhaps later *2-morphism*, *3-morphism*, etc. The
concrete types are structurally similar to the core type `Expr` in Julia.

**Design note**: An alternative approach would represent every kind with the
`Expr` type, using its `typ` field to distinguish objects and morphisms. I think
that would be a mistake. It would conflate the `Ob` and `Mor` type parameters in
the type classes. More fundamentally, it is always wrong to change the kind of
an expression at the syntactic level, e.g., any rewrite rule that transforms an
object expression to a morphism expression makes a category error. We should
enforce this constraint at the type level in Julia.

At the other extreme, we could create a concrete type for each syntactic element
(`GeneratorMor`, `IdMor`, `CompositeMor`, etc). This idea is better than the
last but leads to a large proliferation of types and makes it inconvenient to
write generic code operating on expressions as a homogeneous data structure
(analogous to S-expressions).
"""
abstract BaseExpr

immutable ObExpr <: BaseExpr
  head::Symbol
  args::Array
  ObExpr(head, args...) = new(head, [args...])
end

immutable MorExpr <: BaseExpr
  head::Symbol
  args::Array
  MorExpr(head, args...) = new(head, [args...])
end

head(expr::BaseExpr)::Symbol = expr.head
args(expr::BaseExpr)::Array = expr.args
=={E<:BaseExpr}(e1::E, e2::E)::Bool = head(e1)==head(e2) && args(e1)==args(e2)

""" Apply associative binary operation to two expressions.

Maintains the normal form E(:op, [e1,e2,..]) where e1,e2,... are expressions
that are *not* applications of :op.
"""
function associate{E<:BaseExpr}(op::Symbol, e1::E, e2::E)
  terms(expr::E) = head(expr) == op ? args(expr) : [expr]
  E(op, [terms(e1);terms(e2)]...)
end

# Category
##########

@doc """ Syntax for a *category*.

Although they implement the `Category` typeclass, the expressions do not
strictly speaking form a category because they don't satisfy the category laws,
e.g.,
```
compose(f, id(A)) != compose(f)
```
The expressions form a *syntax* for categories. Equational reasoning and the
conversion to normal form are handled by other components. (An exception is the
associativity of composition, which for convenience is handled at the syntactic
level.) Similar remarks apply to the other doctrines.
""" CategorySyntax

@instance! Doctrine.Category ObExpr MorExpr begin
  dom(f::MorExpr) = dom(f, Val{head(f)})
  codom(f::MorExpr) = codom(f, Val{head(f)})
  id(A::ObExpr) = MorExpr(:id, A)

  function compose(f::MorExpr, g::MorExpr)
    if codom(f) != dom(g)
      error("Incompatible domains $(codom(f)) and $(dom(f))")
    end
    associate(:compose, f, g)
  end
end

# Generators
ob(A::Symbol) = ObExpr(:gen, A)
mor(f::Symbol, dom::ObExpr, codom::ObExpr) = MorExpr(:gen, f, dom, codom)

dom(f::MorExpr, ::Type{Val{:gen}}) = args(f)[2]
dom(f::MorExpr, ::Type{Val{:compose}}) = dom(first(args(f)))
dom(f::MorExpr, ::Type{Val{:id}}) = args(f)[1]

codom(f::MorExpr, ::Type{Val{:gen}}) = args(f)[3]
codom(f::MorExpr, ::Type{Val{:compose}}) = codom(last(args(f)))
codom(f::MorExpr, ::Type{Val{:id}}) = args(f)[1]

# Monoidal category
###################

@doc """ Syntax for a (strict) *monoidal category*.

To satisfy the strictness requirement, monoidal products of objects are
automatically brought to normal form. No other equational reasoning is performed
at the syntactic level.
""" MonoidalCategorySyntax

@instance! Doctrine.MonoidalCategory ObExpr MorExpr begin
  function otimes(A::ObExpr, B::ObExpr)
    @match (A, B) begin
      (ObExpr(:unit,_), _) => B
      (_, ObExpr(:unit,_)) => A
      _ => associate(:otimes, A, B)
    end
  end
  otimes(f::MorExpr, g::MorExpr) = associate(:otimes, f, g)
  munit(::ObExpr) = ObExpr(:unit)
end

dom(f::MorExpr, ::Type{Val{:otimes}}) = otimes(map(dom, args(f))...)
codom(f::MorExpr, ::Type{Val{:otimes}}) = otimes(map(codom, args(f))...)

# Pretty-print
##############

""" Show the expression as an S-expression.

Cf. the standard library function `Meta.show_sexpr`.
"""
show_sexpr(expr::BaseExpr) = show_expr(STDOUT, expr)
show_sexpr(io::IO, expr::BaseExpr) = print(io, as_sexpr(expr))

""" Format the expression as an S-expression.

The transformation is *not* one-to-one since the domains and codomains are
discarded.
"""
function as_sexpr(expr::BaseExpr)::String
  if head(expr) == :gen
    repr(args(expr)[1])
  else
    string("(", join([head(expr), map(as_sexpr,args(expr))...], " "), ")")
  end
end

""" Show the expression in infix notation, using Unicode symbols for operators.
"""
show_infix(expr::BaseExpr) = show_infix(STDOUT, expr)
show_infix(io::IO, expr::BaseExpr) = print(io, as_infix(expr))

""" Format the expression in infix notation.
"""
as_infix(expr::ObExpr) = _as_infix(expr)
as_infix(expr::MorExpr) =
  "$(_as_infix(expr)) : $(_as_infix(dom(expr))) → $(_as_infix(codom(expr)))"

function _as_infix(expr::BaseExpr, paren::Bool=false)::String
  head, args = Syntax.head(expr), Syntax.args(expr)
  if head == :gen # special case: generator
    return string(args[1])
  end
  
  symbol = get(symbol_table, head, string(head))
  if length(symbol) <= 1 && length(args) >= 2 # case 1: infix
    result = join([_as_infix(a,true) for a in args], symbol)
    paren ? "($result)" : result
  elseif length(args) >= 1 # case 2: prefix
    string(symbol, "[", join(map(_as_infix, args), ","), "]")
  else # degenerate case: no arguments
    symbol
  end
end

const symbol_table = Dict{Symbol,String}(
  :compose => " ",
  :otimes => "⊗",
  :unit => "I",
)

end
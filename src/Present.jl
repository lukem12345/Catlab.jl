""" Finite presentations of a model of a generalized algebraic theory (GAT).

We support two methods for defining models of a GAT: as Julia objects using the
`@instance` macro and as syntactic objects using the `@present` macro.
Instances are useful for casting generic data structures, such as matrices,
abstract tensor systems, and wiring diagrams, in categorical language.
Presentations define small categories by generators and relations and are useful
for applications like knowledge representation.
"""
module Present
export @present, Presentation, Equation, generators, equations

import DataStructures: OrderedDict
using Match
using ..Meta, ..Syntax

# Data types
############

typealias GeneratorExpr BaseExpr{:generator}
typealias Equation{T<:BaseExpr} Pair{T}{T}

type Presentation
  generators::OrderedDict{Symbol,GeneratorExpr}
  equations::Vector{Equation}
end
Presentation() = Presentation(OrderedDict{Symbol,GeneratorExpr}(), Equation[])
generators(pres::Presentation) = pres.generators
equations(pres::Presentation) = pres.equations

# Presentations
###############

macro present(head, body)
  name, syntax_name = @match head begin
    Expr(:call, [name::Symbol, arg::Symbol], _) => (name, arg)
    _ => throw(ParseError("Ill-formed presentation header $head"))
  end
  code = Expr(:(=), name, Expr(:let, translate_presentation(syntax_name, body)))
  esc(code)
end

""" Add a generator to a presentation.
"""
function add_generator!(pres::Presentation, expr::GeneratorExpr)
  name = first(expr)
  if haskey(pres.generators, name)
    error("Name $name already defined in presentation")
  end
  pres.generators[name] = expr
  return expr
end
function add_generator!(pres::Presentation, name::Symbol, typ::Type, args...)
  add_generator!(pres, make_generator(typ, name, args...))
end

""" Add an equation between terms to a presentation.
"""
function add_equation!(pres::Presentation, lhs::BaseExpr, rhs::BaseExpr)
  push!(pres.equations, Equation(lhs, rhs))
end

""" Add a generator defined by an equation.
"""
function add_definition!(pres::Presentation, name::Symbol, rhs::BaseExpr)
  generator = make_generator_like(rhs, name)
  add_generator!(pres, generator)
  add_equation!(pres, generator, rhs)
  return generator
end

""" Translate a presentation in the DSL to a block of Julia code.
"""
function translate_presentation(syntax_name::Symbol, body::Expr)::Expr
  @assert body.head == :block
  code = Expr(:block)
  append_expr!(code, :(_presentation = $(module_ref(:Presentation))()))
  for expr in strip_lines(body).args
    append_expr!(code, translate_expr(syntax_name, expr))
  end
  append_expr!(code, :(_presentation))
  return code
end
module_ref(sym::Symbol) = GlobalRef(Present, sym)

""" Translate a single statement in the presentation DSL to Julia code.
"""
function translate_expr(syntax_name::Symbol, expr::Expr)::Expr
  @match expr begin
    Expr(:(::), [name::Symbol, type_expr], _) =>
      translate_generator(syntax_name, name, type_expr)
    Expr(:(:=), [name::Symbol, def_expr], _) =>
      translate_definition(name, def_expr)
    Expr(:(=), _, _) => expr
    Expr(:call, [:(==), lhs, rhs], _) => translate_equation(lhs, rhs)
    _ => throw(ParseError("Ill-formed presentation statement $expr"))
  end
end

""" Translate declaration of a generator.
"""
function translate_generator(syntax_name::Symbol, name::Symbol, type_expr)::Expr
  type_name, args = @match type_expr begin
    sym::Symbol => (sym, [])
    Expr(:call, [sym::Symbol, args...], _) => (sym, args)
    _ => throw(ParseError("Ill-formed type expression $type_expr"))
  end
  call_expr = Expr(:call, module_ref(:add_generator!), :_presentation,
                   QuoteNode(name), :($syntax_name.$type_name), args...)
  :(const $name = $call_expr)
end

""" Translate definition of generator in terms of other generators.
"""
function translate_definition(name::Symbol, def_expr)::Expr
  call_expr = Expr(:call, module_ref(:add_definition!), :_presentation,
                   QuoteNode(name), def_expr)
  :(const $name = $call_expr)
end

""" Translate declaration of equality between terms.
"""
function translate_equation(lhs, rhs)::Expr
  Expr(:call, module_ref(:add_equation!), :_presentation, lhs, rhs)
end

# FIXME: Put these functions in `Syntax` module? These don't belong here.
function make_generator(cons_type::Type, value, args...)
  cons = getfield(module_parent(cons_type.name.module),
                  Syntax.constructor_name_for_generator(cons_type.name.name))
  isempty(args) ? cons(cons_type, value) : cons(value, args...)
end
function make_generator_like(expr::BaseExpr, value)::GeneratorExpr
  make_generator(typeof(expr), value, type_args(expr)...)
end

end

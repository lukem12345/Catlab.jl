# # Meets in Preorders
#
#md # [![](https://img.shields.io/badge/show-nbviewer-579ACA.svg)](@__NBVIEWER_ROOT_URL__/generated/sketches/meets.ipynb)
#
# Our first example of a concept defined by a universal mapping property is a meet.
#

using Test

using Catlab.Theories, Catlab.CategoricalAlgebra, Catlab.Graphics

# `bfs_parents` performs breadth-first search on any ACSet graph.  It is
# more efficient than a hand-rolled BFS because it pre-allocates a single
# integer parent vector instead of using a separate queue and visited set.
using Catlab.Graphs: bfs_parents, outneighbors

# # Defining some basic preorders

@present P(FreeSchema) begin
  (a₁,a₂,a₃,a₄)::Ob
  f::Hom(a₁, a₂)
  g::Hom(a₁, a₃)
  h::Hom(a₂, a₄)
  k::Hom(a₃, a₄)
end

# We can draw a picture of our preorder as a Hasse Diagram.

to_graphviz(P)

# It is convenient to program with preorders using their Hasse diagram
# representation as a labeled graph, so we convert the
# `Presentation{Schema, Symbol}` into a `FreeDiagram`.  `FreeDiagram`s are
# implemented as ACSets, Catlab's in-memory relational database format.

g = FreeDiagram(P)

# ## Downsets and Upsets
#
# `bfs_parents(acset, s; dir)` returns a length-`nv` parent vector: entry `v`
# is nonzero iff vertex `v` was reached during BFS from `s`.  The `dir` keyword
# controls which edge endpoints are followed:
#
# * `dir=:out` follows each edge source → target, so the reachable set is the
#   *upset* ↑s = { y | s ≤ y }.
# * `dir=:in`  follows edges backwards (target → source), so the reachable set
#   is the *downset* ↓s = { y | y ≤ s }.
#
# `findall(!iszero, parents)` collects reachable vertex indices in sorted order,
# since `bfs_parents` explores each BFS frontier in sorted order.

function upset(g::FreeDiagram, x::Int)
  findall(!iszero, bfs_parents(getvalue(g), x; dir=:out))
end

function downset(g::FreeDiagram, x::Int)
  findall(!iszero, bfs_parents(getvalue(g), x; dir=:in))
end

upset(g, 1)

# We can use upsets to define the ≤ relation implied by any Hasse diagram.

function leq(g::FreeDiagram, x::Int, y::Int)
  y in upset(g, x)
end

# Multiple dispatch lets us also query by object name.

function leq(g::FreeDiagram, x::Symbol, y::Symbol)
  inner = getvalue(g)
  leq(g, incident(inner, x, :ob)[1], incident(inner, y, :ob)[1])
end

# ### Exercise 1
# `leq` as written recomputes the full upset of `x` just to test membership of `y`.
# Define a more efficient algorithm that stops BFS as soon as `y` is discovered.

# ## Meet (Greatest Lower Bound)
#
# The meet of two elements is the largest element in the intersection of their downsets.

function meet(g::FreeDiagram, x::Int, y::Int)
  D = downset(g, x) ∩ downset(g, y)
  return maximum(g, D)
end

function meet(g::FreeDiagram, x, y)
  meet(g, incident(getvalue(g), x, :ob)[1], incident(getvalue(g), y, :ob)[1])
end

# An element of a downset D is *maximal* if none of its out-neighbours
# are also in D.

function maxima(g::FreeDiagram, D::Vector{Int})
  X = Set(D)
  filter(D) do x
    isempty(outneighbors(getvalue(g), x) ∩ X)
  end
end

function hastop(g::FreeDiagram, xs::Vector{Int})
  length(maxima(g, xs)) == 1
end

# In a preorder (not necessarily a poset) there may be several mutually
# isomorphic maxima.  `maximum` returns the canonical first one, or `nothing`.

function maximum(g::FreeDiagram, xs::Vector{Int})
  m = maxima(g, xs)
  if length(m) == 1
    return m[1]
  end
  if length(m) > 1
    all_iso = all(m) do a
      a_le_allb = all(b -> b in upset(g, a), m)
      return a_le_allb
    end
    all_iso && return m[1]
  end
  return nothing
end

# Because `bfs_parents` is backed by Catlab's ACSet index, each call to
# `downset` or `upset` avoids rebuilding neighbour lists from scratch.
# If you need to perform many ≤ queries in a tight loop, see Exercise 2.

# ### Exercise 2
# Precompute the reachability matrix L where L[i,j] = 1 iff i ≤ j.
# One approach: call `upset(g, v)` for each vertex v and collect results.
# What is the time complexity compared to running one BFS per query?

# ## Testing it out

@testset "Upsets" begin
  @test upset(g, 3) == [3,4]
  @test upset(g, 2) == [2,4]
  @test upset(g, 1) == [1,2,3,4]
  @test upset(g, 4) == [4]
end

@testset "Downsets" begin
  @test downset(g, 3) == [1,3]
  @test downset(g, 2) == [1,2]
  @test downset(g, 4) == [1,2,3,4]
  @test downset(g, 1) == [1]
end

@testset "Meets" begin
  @test meet(g, 2,3) == 1
  @test meet(g, 1,2) == 1
  @test meet(g, 3,4) == 3
  @test meet(g, 1, 4) == 1
  @test meet(g, 1, 1) == 1
  @test meet(g, 2, 2) == 2
end

# ## Another Example:

@present P(FreeSchema) begin
  (a₁,a₂,a₃,a₄,a₅)::Ob
  f::Hom(a₁, a₂)
  g::Hom(a₁, a₃)
  h::Hom(a₂, a₄)
  k::Hom(a₃, a₄)
  l::Hom(a₅, a₂)
end

# Which can be viewed as a picture:

to_graphviz(P)

# Or, as tables:

g = FreeDiagram(P)

# ### Test suite

@testset "meets2" begin
  @test meet(g, 2,3) == 1
  @test meet(g, 1,2) == 1
  @test meet(g, 3,4) == 3
  @test meet(g, 1, 4) == 1
  @test meet(g, 1, 1) == 1
  @test meet(g, 2, 2) == 2
  @test meet(g, 3, 5) == nothing
  @test meet(g, 2, 5) == 5
end

# ### Exercise 3
# Make bigger preorders to test corner cases in the above code.
# If you find an example that breaks these implementations, please report it.

# ### Exercise 4
# Implement the dual constructions for joins.

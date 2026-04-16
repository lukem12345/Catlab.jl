# # Meets in Preorders
#
#md # [![](https://img.shields.io/badge/show-nbviewer-579ACA.svg)](@__NBVIEWER_ROOT_URL__/generated/sketches/meets.ipynb)
#
# Our first example of a concept defined by a universal mapping property is a meet.
#

using Test

using Catlab.Theories, Catlab.CategoricalAlgebra, Catlab.Graphics

# `enumerate_paths` from `Catlab.Graphs` computes all paths in a DAG via a
# single topological-order sweep — no breadth-first search involved.
using Catlab.Graphs: enumerate_paths

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

# ## Building the Reachability Relation
#
# `enumerate_paths(G)` topologically sorts the DAG and then accumulates, for
# each vertex `v` in reverse topological order, the set of all paths that
# start at `v`.  The output is a `ReflexiveEdgePropertyGraph` in which every
# edge `(s, t, edge_list)` records one path from `s` to `t`; reflexive edges
# (the `refl` part of the schema) encode the trivial length-0 path `s = t`.
#
# The reachability relation is the image of this graph under `(src, tgt)`:
# a pair `(s, t)` is in the relation iff there is some path from `s` to `t`,
# i.e. iff `s ≤ t` in the preorder.

function reachability(g::FreeDiagram)
  ps = enumerate_paths(getvalue(g))
  Set(s => t for (s, t, e) in zip(ps[:src], ps[:tgt], ps[:eprops])
             if s == t || !isempty(e))
end

reach = reachability(g)

# ## Downsets and Upsets
#
# With the full order relation precomputed, upsets and downsets are simple
# filter queries on `reach` — no graph traversal at query time.

# The *downset* ↓x = { y | y ≤ x } consists of all sources of paths that end at x:
function downset(reach::Set{Pair{Int,Int}}, x::Int)
  sort([s for (s, t) in reach if t == x])
end

# The *upset* ↑x = { y | x ≤ y } consists of all targets of paths that start at x:
function upset(reach::Set{Pair{Int,Int}}, x::Int)
  sort([t for (s, t) in reach if s == x])
end

upset(reach, 1)

# The ≤ relation is an O(1) membership test on the hash set:
leq(reach::Set{Pair{Int,Int}}, x::Int, y::Int) = (x => y) in reach

# ### Exercise 1
# `leq` is already O(1).  A BFS-based approach would recompute a traversal
# per call; here the cost is paid once in `reachability`.  Try implementing
# a version that builds `reach` lazily — only computing the rows it needs.

# ## Meet (Greatest Lower Bound)
#
# The meet of two elements is the largest element in the intersection of their downsets.

function meet(reach::Set{Pair{Int,Int}}, x::Int, y::Int)
  D = downset(reach, x) ∩ downset(reach, y)
  maximum_elt(reach, D)
end

# An element m ∈ D is *maximal* if no other element of D lies strictly above it.
# Using `reach` we can check this directly without inspecting graph edges:

function maxima(reach::Set{Pair{Int,Int}}, D::Vector{Int})
  filter(D) do x
    !any(y -> y != x && (x => y) in reach, D)
  end
end

function hastop(reach::Set{Pair{Int,Int}}, D::Vector{Int})
  length(maxima(reach, D)) == 1
end

# In a preorder (not necessarily a poset) there may be several mutually
# isomorphic maxima (each ≤ the other).  `maximum_elt` returns the canonical
# first one, or `nothing` if the set has no greatest element.
function maximum_elt(reach::Set{Pair{Int,Int}}, D::Vector{Int})
  m = maxima(reach, D)
  isempty(m) && return nothing
  length(m) == 1 && return m[1]
  all_iso = all(a -> all(b -> (a => b) in reach, m), m)
  all_iso ? m[1] : nothing
end

# Because `reach` is computed once by `enumerate_paths` and all subsequent
# operations are set queries, the cost of each downset, upset, leq, or meet
# call is proportional to `|reach|`, not to the structure of the graph.

# ### Exercise 2
# Precompute the full reachability matrix L where L[i,j] = 1 iff i ≤ j.
# Using `reach`, this is a single pass over the set.  What is the complexity?

# ## Testing it out

@testset "Upsets" begin
  @test upset(reach, 3) == [3,4]
  @test upset(reach, 2) == [2,4]
  @test upset(reach, 1) == [1,2,3,4]
  @test upset(reach, 4) == [4]
end

@testset "Downsets" begin
  @test downset(reach, 3) == [1,3]
  @test downset(reach, 2) == [1,2]
  @test downset(reach, 4) == [1,2,3,4]
  @test downset(reach, 1) == [1]
end

@testset "Meets" begin
  @test meet(reach, 2,3) == 1
  @test meet(reach, 1,2) == 1
  @test meet(reach, 3,4) == 3
  @test meet(reach, 1, 4) == 1
  @test meet(reach, 1, 1) == 1
  @test meet(reach, 2, 2) == 2
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
reach = reachability(g)

# ### Test suite

@testset "meets2" begin
  @test meet(reach, 2,3) == 1
  @test meet(reach, 1,2) == 1
  @test meet(reach, 3,4) == 3
  @test meet(reach, 1, 4) == 1
  @test meet(reach, 1, 1) == 1
  @test meet(reach, 2, 2) == 2
  @test meet(reach, 3, 5) == nothing
  @test meet(reach, 2, 5) == 5
end

# ### Exercise 3
# Make bigger preorders to test corner cases in the above code.
# If you find an example that breaks these implementations, please report it.

# ### Exercise 4
# Implement the dual constructions for joins.

# # Meets in Preorders
#
#md # [![](https://img.shields.io/badge/show-nbviewer-579ACA.svg)](@__NBVIEWER_ROOT_URL__/generated/sketches/meets.ipynb)
#
# Our first example of a concept defined by a universal mapping property is a meet.
# We represent each preorder as a `PreorderFinCat`, a thin category whose morphism
# set is the *transitive closure* of the covering relation.
#

using Test

using Catlab.Theories, Catlab.CategoricalAlgebra, Catlab.Graphics

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

# ## Representing a Preorder as a Category
#
# A preorder is a *thin category*: at most one morphism between any two objects,
# with morphism existence encoding the ≤ relation.  Catlab's `PreorderFinCat` builds
# this thin category by computing the *transitive closure* of the covering relation
# at construction time.  Internally it calls `enumerate_paths` (from `Catlab.Graphs`)
# on the Hasse-diagram DAG and records every reachable pair (i, j) — including
# reflexive ones — in the `rel` field as a `Set{Pair{Int,Int}}`.  An entry `i => j`
# means `genvec[i] ≤ genvec[j]`, where `genvec` is the sorted vector of object names.

function build_preorder(P::Presentation)
  pairs = [nameof(dom(f)) => nameof(codom(f)) for f in generators(P, :Hom)]
  PreorderFinCat(pairs)
end

pfc = build_preorder(P)

# Inspect the object ordering and the transitive closure:

pfc.genvec   # [:a₁, :a₂, :a₃, :a₄]

pfc.rel      # {1=>1, 1=>2, 1=>3, 1=>4, 2=>2, 2=>4, 3=>3, 3=>4, 4=>4}

# ## Downsets and Upsets via Relational Lookup
#
# Because the full order relation is precomputed in `pfc.rel`, upsets and downsets
# reduce to simple filter queries on that set — no graph traversal at query time.

# The *downset* ↓x = { y ∣ y ≤ x }:
function downset(pfc::PreorderFinCat, x::Symbol)
  xj = pfc.gendict[x]
  sort([pfc.genvec[i] for (i, j) in pfc.rel if j == xj])
end

# The *upset* ↑x = { y ∣ x ≤ y }:
function upset(pfc::PreorderFinCat, x::Symbol)
  xi = pfc.gendict[x]
  sort([pfc.genvec[j] for (i, j) in pfc.rel if i == xi])
end

upset(pfc, :a₁)

# The ≤ relation is an O(1) average-time membership test on the `rel` hash set:
function leq(pfc::PreorderFinCat, x::Symbol, y::Symbol)
  (pfc.gendict[x] => pfc.gendict[y]) in pfc.rel
end

# ### Exercise 1
# The `leq` above is already O(1) thanks to the precomputed transitive closure.
# By contrast, a BFS-based approach recomputes reachability on every call.
# Verify experimentally that `leq` here has constant-time behaviour by
# benchmarking it on increasingly large preorders (e.g. total orders of length n).

# ## Meet (Greatest Lower Bound)
#
# The meet x ∧ y is the largest element in downset(x) ∩ downset(y).
# With the full closure in `pfc.rel`, maximality is a direct relational query.

# An element m ∈ D is *maximal* if no other element of D lies strictly above it:
function maxima(pfc::PreorderFinCat, D::AbstractVector{Symbol})
  filter(D) do x
    xi = pfc.gendict[x]
    !any(D) do y
      y != x && (xi => pfc.gendict[y]) in pfc.rel
    end
  end
end

function hastop(pfc::PreorderFinCat, D::AbstractVector{Symbol})
  length(maxima(pfc, D)) == 1
end

# In a preorder (not necessarily a poset) there may be several mutually isomorphic
# maxima (each ≤ the other).  `maximum_elt` returns the canonical first one, or
# `nothing` if the set has no greatest element.
function maximum_elt(pfc::PreorderFinCat, D::AbstractVector{Symbol})
  m = maxima(pfc, D)
  isempty(m) && return nothing
  length(m) == 1 && return m[1]
  # All maxima must be mutually isomorphic for a unique equivalence class to exist.
  all_iso = all(m) do a
    ai = pfc.gendict[a]
    all(b -> (ai => pfc.gendict[b]) in pfc.rel, m)
  end
  all_iso ? m[1] : nothing
end

function meet(pfc::PreorderFinCat, x::Symbol, y::Symbol)
  D = intersect(downset(pfc, x), downset(pfc, y))
  maximum_elt(pfc, D)
end

# Because `pfc.rel` is built once at construction and every `leq` check inside
# `maximum_elt` is O(1), repeated meet queries on the same preorder reuse the
# transitive closure without additional graph traversal.

# ### Exercise 2
# Implement `leq_matrix(pfc)` returning a Boolean matrix L where L[i,j] is true
# iff `pfc.genvec[i] ≤ pfc.genvec[j]`.  What is the time and space complexity
# of building it directly from `pfc.rel`?

# ## Testing it out

@testset "Upsets" begin
  @test upset(pfc, :a₃) == [:a₃, :a₄]
  @test upset(pfc, :a₂) == [:a₂, :a₄]
  @test upset(pfc, :a₁) == [:a₁, :a₂, :a₃, :a₄]
  @test upset(pfc, :a₄) == [:a₄]
end

@testset "Downsets" begin
  @test downset(pfc, :a₃) == [:a₁, :a₃]
  @test downset(pfc, :a₂) == [:a₁, :a₂]
  @test downset(pfc, :a₄) == [:a₁, :a₂, :a₃, :a₄]
  @test downset(pfc, :a₁) == [:a₁]
end

@testset "Meets" begin
  @test meet(pfc, :a₂, :a₃) == :a₁
  @test meet(pfc, :a₁, :a₂) == :a₁
  @test meet(pfc, :a₃, :a₄) == :a₃
  @test meet(pfc, :a₁, :a₄) == :a₁
  @test meet(pfc, :a₁, :a₁) == :a₁
  @test meet(pfc, :a₂, :a₂) == :a₂
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

# Rebuild the preorder category for the new presentation:

pfc = build_preorder(P)

# ### Test suite

@testset "meets2" begin
  @test meet(pfc, :a₂, :a₃) == :a₁
  @test meet(pfc, :a₁, :a₂) == :a₁
  @test meet(pfc, :a₃, :a₄) == :a₃
  @test meet(pfc, :a₁, :a₄) == :a₁
  @test meet(pfc, :a₁, :a₁) == :a₁
  @test meet(pfc, :a₂, :a₂) == :a₂
  @test meet(pfc, :a₃, :a₅) == nothing
  @test meet(pfc, :a₂, :a₅) == :a₅
end

# ### Exercise 3
# Make bigger preorders to test corner cases in the above code.
# If you find an example that breaks these implementations, please report it.

# ### Exercise 4
# Implement the dual constructions for joins.

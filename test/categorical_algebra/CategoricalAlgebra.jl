module TestCategoricalAlgebra

using Test

@testset "ShapeDiagrams" begin
  include("ShapeDiagrams.jl")
end

@testset "Matrices" begin
  include("Matrices.jl")
end

@testset "FinSets" begin
  include("FinSets.jl")
end

@testset "FinRelations" begin
  include("FinRelations.jl")
end

@testset "Permutations" begin
  include("Permutations.jl")
end

end
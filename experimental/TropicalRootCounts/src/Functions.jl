
###
# These functions should probably be in OSCAR
###
import Oscar.coefficient_ring
function coefficient_ring(F::Vector{<:MPolyElem})
    return coefficient_ring(first(F))
end
import Oscar.ngens
function ngens(K::AbstractAlgebra.Generic.RationalFunctionField)
    return length(gens(K))
end
import Oscar.polynomial_ring
function polynomial_ring(F::Vector{<:MPolyElem})
    return polynomial_ring(first(F))
end
function polynomial_ring(f::MPolyElem)
    return parent(f)
end


###
# Our functions:
###
function construct_substitution_homomorphism(polynomialRing::MPolyRing,
                                             variablesToBeSubstituted::Vector{<:MPolyElem},
                                             polynomialsToSubstitute::Vector{<:MPolyElem})

    ###
    # Construct codomain of the substitution homomorphism
    ###
    variableIndicesRemaining = findall(x->(x∉variablesToBeSubstituted), gens(polynomialRing))
    substRing,substRingVars = polynomial_ring(coefficient_ring(polynomialRing),
                                              symbols(polynomialRing)[variableIndicesRemaining],
                                              ordering=polynomialRing.ord)

    ###
    # Construct images of the variables under the substituion homomorphism
    ###
    # Step 1: construct images of the variables which are not substituted
    substImages = substRingVars
    for (i,x) in enumerate(gens(polynomialRing))
        if x in variablesToBeSubstituted
            insert!(substImages,i,polynomialRing(0))
        end
    end
    # Step 2: construct images of the variables which are substituted
    for (i,x) in enumerate(gens(polynomialRing))
        j = findfirst(isequal(x),variablesToBeSubstituted)
        if !isnothing(j)
            substImages[i] = evaluate(polynomialsToSubstitute[j],substImages)
        end
    end

    return hom(polynomialRing,substRing,substImages)

end


function modify_vertically(polynomialSystem::Vector{<:MPolyElem})

    # Construct a list of distinct monomials (sorted for the sake of consistency)
    Kax = polynomial_ring(polynomialSystem)
    distinctMonomials = sort(unique(collect(Iterators.flatten(monomials.(polynomialSystem)))))

    # Construct a new polynomial ring, with an extra variable per distinct monomial
    Ka = coefficient_ring(Kax)
    Kaxy,xy = polynomial_ring(Ka,vcat(string.(symbols(Kax)),["y"*string(i) for i in 1:length(distinctMonomials)]))
    n = ngens(Kax)
    x = xy[1:n]
    y = xy[n+1:end]

    linearSystem = elem_type(Kaxy)[]
    for f in polynomialSystem
        # substitute monomial xAlpha by the corresponding w
        push!(linearSystem,sum([c*y[findfirst(isequal(xAlpha),distinctMonomials)] for (c,xAlpha) in zip(coefficients(f),monomials(f))]))
    end

    distinctMonomials = evaluate.(distinctMonomials,Ref(x))
    binomialSystem = [y[i]-mon for (i,mon) in enumerate(distinctMonomials)]

    return linearSystem, binomialSystem

end

function construct_specialization_homomorphism(Kax::MPolyRing; choiceOfCoefficients=nothing)

    Ka = coefficient_ring(Kax)
    @assert Ka isa AbstractAlgebra.Generic.RationalFunctionField
    K = base_ring(Ka)
    Kx,x = polynomial_ring(K,symbols(Kax))

    # pick random choice of coefficients, if not specified by user
    if isnothing(choiceOfCoefficients)
        choiceOfCoefficients = rand(Int,ngens(Ka))
    end



    return hom(Kax,Kx,c->K(evaluate(c,choiceOfCoefficients)),x)

end

function tropically_generic_specialization_linear(parametrizedLinearSystem::Vector{<:MPolyElem};
                                                  genericChoiceOfParameters::Vector{<:RingElem}=nothing,
                                                  check_genericity::Bool=true)

    Kax = polynomial_ring(parametrizedLinearSystem)
    Ka = coefficient_ring(parametrizedLinearSystem)
    K = base_ring(Ka)
    parametrizedMacaulayMatrix = zero_matrix(Ka,length(parametrizedLinearSystem),ngens(Kax))
    for (i,f) in enumerate(parametrizedLinearSystem)
        for (c,xAlpha) in zip(coefficients(f),monomials(f))
            j = findfirst(isequal(xAlpha),gens(Kax))
            @assert !isnothing(j)
            parametrizedMacaulayMatrix[i,j] = c
        end
    end

    if isnothing(genericChoiceOfParameters)
        genericChoiceOfParameters = rand(Int,ngens(Ka))
    end

    if check_genericity 
        macaulayMatrix = matrix(K,[[evaluate(parametrizedMacaulayMatrix[i,j],genericChoiceOfParameters) for j in 1:ncols(parametrizedMacaulayMatrix)]
                                for i in 1:nrows(parametrizedMacaulayMatrix)])

        for I in AbstractAlgebra.combinations(ncols(macaulayMatrix),nrows(macaulayMatrix))
            if det(macaulayMatrix[:,I])==0
                @req det(parametrizedMacaulayMatrix[:,I])==0 "genericChoiceOfParameters not generic"
            end
        end
    end

    Kx,x = polynomial_ring(K,symbols(Kax))
    phi = hom(Kax,Kx,c->evaluate(c,genericChoiceOfParameters),x)
    linearSystem = phi.(parametrizedLinearSystem)
    return linearSystem
end

function tropically_generic_specialization_binomial(parametrizedBinomialIdeal::Vector{<:MPolyElem};
                                                    choice_of_parameter::Vector{<:RingElem}=nothing,
                                                    check_genericity::Bool=true)

    Kax = polynomial_ring(parametrizedBinomialSystem)
    Ka = coefficient_ring(parametrizedBinomialSystem)
    K = base_ring(Ka)
    Kxy,xy = polynomial_ring(K,symbols(Kax))

    if isnothing(choice_of_parameters)
        choice_of_parameters = rand(Int,ngens(Ka))
    end
    phi = hom(Kax,Kxy,c->evaluate(c,choice_of_parameters),xy)
    binomialSystem = phi.(parametrizedBinomialSystem)

    if check_genericity
        @req all(isequal(2),length.(binomialSystem)) "choice of parameters not generic"
    end

    return binomialSystem
end

function tropically_generic_specialization(parametrizedPolynomialSystem::Vector{<:MPolyElem};
                                           choice_of_parameters::Vector{<:RingElem}=nothing,
                                           check_genericity::Bool=true)

    if all(isequal(1),total_degree.(parametrizedPolynomialSystem))
        return tropically_generic_specialization_linear(parametrizedPolynomialSystem,
                    choice_of_parameter=choice_of_parameter,check_genericity=check_genericity)
    elseif all(isequal(2),length.(parametrizedPolynomialSystem))
        return tropically_generic_specialization_binomial(parametrizedPolynomialSystem,
                    choice_of_parameter=choice_of_parameter,check_genericity=check_genericity)
    else
        error("input unsupported (neither linear nor binomial)")
    end

end


function bergman_fan_from_linear_equation_matrix(linearEquationsMatrix::fmpq_mat)
    ###
    # Compute the projection matrix onto the (orthogonal) complement of the linear space,
    # or in other words the images of the unit vectors projected onto the complement
    ###
    basisOfComplementTransposed = nullspace(linearEquationsMatrix)[2]
    basisOfComplement = transpose(basisOfComplementTransposed)
    projectionMatrix = basisOfComplementTransposed*inv(basisOfComplement*basisOfComplementTransposed)*basisOfComplement

    ###
    # Compute the Bergman fan in Polymake
    ###
    B = Polymake.tropical.matroid_fan{min}(Polymake.Matrix{Polymake.Rational}(projectionMatrix))

    ###
    # Construct the `PolyhedralFan` in OSCAR
    #   Note:
    #   1. We cast the output of `Polymake.tropical.matroid_fan` to `PolyhedralComplex`
    #      and not `PolyhedralFan` due to unexpected behaviour (bug?)
    #   2. The result is a `PolyhedralComplex` describing a polyhedral fan,
    #      i.e. `nvertices(B)==1` (the origin).
    #   3. However, the ambient dimension of the polyhedral complex is too high.
    #      We believe that the first coordinate is always zero and must be removed.
    ###
    # casting to `PolyhedralFan` yields something strange,
    # so we cast to `PolyhedralComplex` instead
    # the result is a `PolyhedralComplex` with only a single vertex: the origin
    B = PolyhedralComplex{fmpq}(B)

    bergmanRays = vertices_and_rays(B)
    # test that the last entry is a vertex
    @assert last(bergmanRays) isa PointVector
    # test that the last entry is the origin
    @assert iszero(last(bergmanRays))

    # remove last row (all zeroes by tests above)
    # TODO: remove Vector{fmpq}.() when following issue is resolved:
    #   https://github.com/oscar-system/Oscar.jl/issues/2313
    bergmanRays = matrix(QQ,Vector{fmpq}.(bergmanRays))[1:end-1,:]#2:end]

    # append the all ones vector, which somehow gets forgotten???
    bergmanLineality = vcat(matrix(QQ,ones(Int,1,ncols(bergmanRays))),matrix(QQ,lineality_space(B)))

    # remove last column which should be contain the vertex index
    bergmanIncidences = vertex_and_ray_indices(maximal_polyhedra(B))[:,1:end-1]
    return PolyhedralFan(bergmanRays,bergmanLineality,bergmanIncidences,non_redundant=true)
end


# Input:
# - a linear system that depends on parameters
# - a binomial system indepndent of parameters
# Output:
# - matrix of tropical intersection points
# - vector of tropical intersection multiplicities
# - vector representing a random perturbation
function tropical_stable_intersection_after_perturbation(TropL::TropicalLinearSpace,
                                                         TropV::TropicalVariety;
                                                         randomChoiceOfCoefficients=nothing,
                                                         randomDirection=nothing)

    # Todo: assume that TropV only consists of lineality
    # @req nmaxpolyhedra(TropV)==1

    # Todo: assume that TropL is a Bergman fan
    # @req nvertices(TropL)==1

    bergmanRays,bergmanLineality = rays_modulo_lineality(TropL)
    bergmanRays = matrix(QQ,bergmanRays)
    bergmanLineality = matrix(QQ,bergmanLineality)


    ###
    # Step 2: Construct a basis of the tropicalization of the solutions to the binomial system
    ###
    linearSpaceBasis = matrix(QQ,lineality_space(TropV))

    # # trivial case: the Bergman fan is a linear space.
    # if nrays(bergmanFan)==0
    #     return tropical_intersection_multiplicity(basisOfLinealitySpace,linearSpaceBasis)
    # end


    # compute the projection matrix onto the orthogonal complement of the euclidean linear space
    basisOfComplementTransposed = nullspace(linearSpaceBasis)[2]
    basisOfComplement = transpose(basisOfComplementTransposed)
    projectionMatrix = basisOfComplementTransposed*inv(basisOfComplement*basisOfComplementTransposed)*basisOfComplement


    # project the rays of the Bergman fan
    projectedRays = bergmanRays*projectionMatrix
    projectedLineality = bergmanLineality*projectionMatrix


    # pick random direction if it hasn't been specified and project it
    if isnothing(randomDirection)
        randomDirection = rand(Int,1,ncols(linearSpaceBasis))
    end
    projectedRandomDirection = matrix(QQ,randomDirection)*projectionMatrix


    stableIntersectionPoints = fmpq_mat[]
    stableIntersectionMults = fmpz[]
    indicesOfCones = ray_indices(maximal_polyhedra(TropL))
    nRaysPerCone = sum(indicesOfCones[1,:])
    for i in 1:nrows(indicesOfCones)
        # read off rays of the projected cone
        indicesOfCone = findall(indicesOfCones[i,:])
        projectedRaysOfCone = projectedRays[indicesOfCone,:]

        # test whether projected direction lies in projected cone
        can_solve,solution = can_solve_with_solution(vcat(projectedRaysOfCone,projectedLineality),
                                                     -projectedRandomDirection; side=:left)
        if can_solve
            firstZero = findfirst(isequal(0),solution)
            if (firstZero != nothing) && (firstZero[2] <= nRaysPerCone)
                # random direction lies on the boundary of the cone
                error("random direction not generic, fix work in progress")
            end
            firstNegative = findfirst(a->(a<0),solution)
            if (firstNegative == nothing) || (firstNegative[2] > nRaysPerCone)
                # random direction lies in the interior of the cone,
                # compute intersection point and intersection multiplicity
                push!(stableIntersectionPoints,solution*vcat(bergmanRays[indicesOfCone,:],bergmanLineality)+projectedRandomDirection)
                coneSpanBasis = vcat(bergmanRays[indicesOfCone,:],bergmanLineality)
                push!(stableIntersectionMults,tropical_intersection_multiplicity(coneSpanBasis,linearSpaceBasis))
            end
        end
    end
    return stableIntersectionPoints,stableIntersectionMults,projectedRandomDirection
end

function tropicalize_first_intersect_second(linearEquationsToBeTropicalized::fmpq_mat,
                                            linearEquationsNotToBeTropicalized::fmpq_mat;
                                            randomDirection=nothing,
                                            bergmanFan=nothing)


    # compute the Bergman fan if it hasn't been specified
    if isnothing(bergmanFan)
        println("constructing Bergman fan")
        bergmanFan = bergman_fan_from_linear_equation_matrix(linearEquationsToBeTropicalized)
    end
    bergmanRays,bergmanLineality = rays_modulo_lineality(bergmanFan)
    bergmanRays = matrix(QQ,bergmanRays)
    bergmanLineality = matrix(QQ,bergmanLineality)


    # # trivial case: the Bergman fan is a linear space.
    # if nrays(bergmanFan)==0
    #     return tropical_intersection_multiplicity(basisOfLinealitySpace,linearSpaceBasis)
    # end


    # compute the projection matrix onto the intersection of the orthogonal complements
    #   of the linear space and lineality space of the Bergman fan
    linearSpaceBasis = transpose(nullspace(linearEquationsNotToBeTropicalized)[2])
    basisOfComplementTransposed = nullspace(vcat(linearSpaceBasis,bergmanLineality))[2]
    basisOfComplement = transpose(basisOfComplementTransposed)
    projectionMatrix = basisOfComplementTransposed*inv(basisOfComplement*basisOfComplementTransposed)*basisOfComplement


    # project the rays of the Bergman fan
    projectedRays = bergmanRays*projectionMatrix


    # pick random direction if it hasn't been specified and project it
    if isnothing(randomDirection)
        randomDirection = matrix(QQ,rand(Int,1,ncols(linearSpaceBasis)))
    end
    projectedRandomDirection = randomDirection*projectionMatrix


    stableIntersectionPoints = fmpq_mat[]
    stableIntersectionMults = fmpz[]
    indicesOfCones = ray_indices(maximal_cones(bergmanFan))
    for i in 1:nrows(indicesOfCones)
        # read off rays of the projected cone
        indicesOfCone = findall(indicesOfCones[i,:])
        projectedRaysOfCone = projectedRays[indicesOfCone,:]

        # test whether projected direction lies in projected cone
        can_solve,solution = can_solve_with_solution(projectedRaysOfCone,projectedRandomDirection; side=:left)
        if can_solve
            if findfirst(isequal(0),solution) != nothing
                # random direction lies on the boundary of the cone
                error("random direction not generic, fix work in progress")
            elseif findfirst(a -> a<0,solution) == nothing
                # random direction lies in the interior of the cone,
                # compute intersection point and intersection multiplicity
                push!(stableIntersectionPoints,solution*bergmanRays[indicesOfCone,:])
                coneSpanBasis = vcat(bergmanRays[indicesOfCone,:],bergmanLineality)
                push!(stableIntersectionMults,tropical_intersection_multiplicity(coneSpanBasis,linearSpaceBasis))
            end
        end
    end
    return stableIntersectionPoints,stableIntersectionMults,randomDirection
end

# Input: B1, B2 matrices whose rows are generating sets of two euclidean linear spaces,
#               whose sum is the entire space
# Output: the tropical intersection number as defined in [Maclagan-Sturmfels, Definition 3.6.5]
function tropical_intersection_multiplicity(B1,B2)
    @assert ncols(B1) == ncols(B2) && nrows(B1)+nrows(B2) >= ncols(B1)

    # primitive scales every row by the lcm of the denominators, making the matrix integral
    # saturate computes a basis of the saturation of the sublattice spanned by the row vectors
    B1 = saturate(matrix(ZZ,Polymake.common.primitive(B1)))
    B2 = saturate(matrix(ZZ,Polymake.common.primitive(B2)))

    snfB12 = snf(vcat(B1,B2))
    return abs(prod([snfB12[i,i] for i in 1:ncols(snfB12)]))
end


test_function = (x,y) -> x+y;
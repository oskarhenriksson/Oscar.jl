

@doc raw"""
    tropically_generic_specialization(parametrizedPolynomialSystem::Vector{<:MPolyRingElem}; choice_of_parameters::Vector{<:RingElem}=nothing, check_genericity::Bool=true)

Specialize `parametrizedPolynomialSystem` at a random choice of parameters, or `choice_of_parameters` if specified. Return error if specialization is not tropically generic, if `check_genericity==true`.

!!! Warning
Requires `parametrizedPolynomialSystem` to be either linear or binomial.


```
"""
function tropically_generic_specialization(parametrizedPolynomialSystem::Vector{<:MPolyRingElem}; choice_of_parameters::Vector{<:RingElem}=nothing, check_genericity::Bool=true)

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

function tropically_generic_specialization_linear(parametrizedLinearSystem::Vector{<:MPolyRingElem};
                                                  genericChoiceOfParameters::Vector{<:RingElem}=nothing,
                                                  check_genericity::Bool=true)

    Kax = parent(first(parametrizedLinearSystem))
    Ka = coefficient_ring(first(parametrizedLinearSystem))
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

function tropically_generic_specialization_binomial(parametrizedBinomialSystem::Vector{<:MPolyRingElem};
                                                    choice_of_parameter::Vector{<:RingElem}=nothing,
                                                    check_genericity::Bool=true)

    Kax = polynomial_ring(first(parametrizedBinomialSystem))
    Ka = coefficient_ring(first(parametrizedBinomialSystem))
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



"""
    modify_vertically(polynomialSystem::Vector{<:MPolyRingElem})

    Carry out the vertical modification from [^HR23], where one introduces a new variable for each monomial appearing in the system. Outputs the linear system in the new variables, together with a binomial system.

    [^HS95]: https://browse.arxiv.org/abs/2206.07838

"""
function modify_vertically(polynomialSystem::Vector{<:MPolyRingElem})

    # Construct a list of distinct monomials (sorted for the sake of consistency)
    Kax = parent(first(polynomialSystem))
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



function tropical_stable_intersection_after_perturbation(Sigmas::Vector{<:TropicalVariety};
    randomDirections::Union{Vector{Vector{Int}},Nothing}=nothing)

    if isnothing(randomDirections)
        n = ambient_dim(first(Sigmas))
        randomDirections = vcat([zeros(Int,n)],[rand(Int,n) for i=2:length(Sigmas)])
    end

    shiftedMaximalPolyhedra = [maximal_polyhedra(Sigma).+Ref(v) 
                                    for (Sigma,v) in zip(Sigmas,randomDirections)]

    stableIntersectionMultiplicites = Int[]
    stableIntersectionPoints = PointVector{QQFieldElem}[]

    for sigmas in Iterators.product(shiftedMaximalPolyhedra...)
        sigma = intersect(sigmas...)
        @req dim(sigma)<=0 "randomDirection not generic (perturbed varieties are overlapping)"
        if dim(sigma)==0
            vertex = first(vertices(sigma))
            for s in sigmas
                @req all(is_negative, affine_inequality_matrix(facets(s))*vcat([1],vertex)) "randomDirection not generic (lower-dimensional skeleta are intersecting)"
            end
            push!(stableIntersectionPoints,vertex)
            mult = 1
            for i in 2:length(sigmas)
                mult *= Oscar.tropical_intersection_multiplicity(intersect(sigmas[1:(i-1)]...),sigmas[i])
            end
            push!(stableIntersectionMultiplicites,mult)
        end
    end
            
    return  stableIntersectionPoints, stableIntersectionMultiplicites, randomDirections
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


    stableIntersectionPoints = QQMatrix[]
    stableIntersectionMults = ZZRingElem[]
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

# Input: B1, B2 matrices whose rows are generating sets of two euclidean linear spaces,
#               whose sum is the entire space
# Output: the tropical intersection number as defined in [Maclagan-Sturmfels, Definition 3.6.5]
function tropical_intersection_multiplicity(B1,B2)
    @assert ncols(B1) == ncols(B2) && nrows(B1)+nrows(B2) >= ncols(B1)

    # primitive scales every row by the lcm of the denominators, making the matrix integral
    # saturate computes a basis of the saturation of the sublattice spanned by the row vectors
    B1 = saturate(matrix(ZZ,Polymake.common.primitive(B1)))
    B2 = saturate(matrix(ZZ,Polymake.common.primitive(B2)))

    return abs(prod(elementary_divisors(vcat(B1,B2))))
end


"""
    tropical_vertical_root_bound_with_auxilary_data(polynomialSystem::Vector{<:MPolyRingElem})

Returns the upper bound on the root count of `tropical_vertical_root_bound`, together with auxilarly data needed to construct start systems and homotopies for solving the system. This data consists of two tuples:
- A tuple consisting of the points and multiplicities of a tropical stable intersection, as well as a pertubation used for making the intersection finite.
- A vertical modification of `polynomialSystem`, consisting of a linear system and a binomial system.

"""
function tropical_vertical_root_bound_with_auxilary_data(polynomialSystem::Vector{<:MPolyRingElem})
    linearSystem, binomialSystem = modify_vertically(polynomialSystem)
    nu = tropical_semiring_map(QQ,min)
    TropL = tropical_linear_space(ideal(linearSystem),nu)
    TropV = tropical_variety(ideal(binomialSystem),nu)[1] #todo: tropical_varities
    pts, mults, pertubation = tropical_stable_intersection_after_perturbation(TropL,TropV)
    return sum(mults), (pts,mults,pertubation), (linearSystem,binomialSystem)
end

"""
    tropical_vertical_root_bound(polynomialSystem::Vector{<:MPolyRingElem})

Return an upper bound on the number of roots of `polynomialSystem` in the torus of the algebraic closure of the coefficient field (counted with multiplicity). This upper bound is always at most the mixed volume of the system. To obtain auxiliary data from the intermedaite tropical intersection that is computed, use `tropical_vertical_root_bound_with_intersection_data`. 

# Examples
```jldoctest
julia> Qx, x = polynomial_ring(QQ,"x"=>1:2);

julia> F = [5*x[1]^3*x[2] - 6*x[1]*x[2]^3 + x[1]*x[2], 5*x[1]^3*x[2] - 6*x[1]*x[2]^3 - x[1]*x[2]^2];

julia> tropical_vertical_root_bound(F)
2

```
"""
function tropical_vertical_root_bound(polynomialSystem::Vector{<:MPolyRingElem})
    return tropical_root_bound_with_intersection_data(polynomialSystem)[1]
end


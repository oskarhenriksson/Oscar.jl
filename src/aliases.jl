include(joinpath(pathof(AbstractAlgebra), "..", "Aliases.jl"))

import Nemo: is_cyclo_type
import Nemo: is_maxreal_type
import Nemo: ZZModRing  # FIXME: remove if/once Nemo exports this
import Nemo: zzModRing  # FIXME: remove if/once Nemo exports this
import Nemo: FpField  # FIXME: remove if/once Nemo exports this
import Nemo: fpField  # FIXME: remove if/once Nemo exports this
include(joinpath(pathof(Nemo), "..", "Aliases.jl"))

#import Hecke: quadratic_genera
#import Hecke: has_algebra
#import Hecke: has_embedding
#import Hecke: has_matrix_action
#import Hecke: has_root
#import Hecke: ...
#include(joinpath(pathof(Hecke), "..", "Aliases.jl"))

# make some Julia names compatible with our naming conventions
@alias is_subset issubset
@alias is_valid isvalid

# for backwards compatibility
Base.@deprecate_binding hall_subgroups_representatives hall_subgroup_reps
Base.@deprecate_binding hasrelshp has_relshp
Base.@deprecate_binding hastorusfactor has_torusfactor
Base.@deprecate_binding inner_automorphisms_group inner_automorphism_group
Base.@deprecate_binding isaffine is_affine
Base.@deprecate_binding isalmostsimple is_almost_simple
Base.@deprecate_binding isample is_ample
Base.@deprecate_binding isbicoset is_bicoset
Base.@deprecate_binding isbinomial is_binomial
Base.@deprecate_binding isbounded is_bounded
Base.@deprecate_binding iscartier is_cartier
Base.@deprecate_binding iscellular is_cellular
Base.@deprecate_binding iscomplete is_complete
Base.@deprecate_binding iscongruent is_congruent
Base.@deprecate_binding isconjugate_subgroup is_conjugate_subgroup
Base.@deprecate_binding isdecorated is_decorated
Base.@deprecate_binding isdihedral_group is_dihedral_group
Base.@deprecate_binding isfano is_fano
Base.@deprecate_binding isfeasible is_feasible
Base.@deprecate_binding isfiltered is_filtered
Base.@deprecate_binding isfinite_order is_finiteorder
Base.@deprecate_binding isfinitelygenerated is_finitely_generated
Base.@deprecate_binding isfull_direct_product is_full_direct_product
Base.@deprecate_binding isfull_semidirect_product is_full_semidirect_product
Base.@deprecate_binding isfull_wreath_product is_full_wreath_product
Base.@deprecate_binding isfulldimensional is_fulldimensional
Base.@deprecate_binding isgenerated_by_standard_unit_vectors is_generated_by_standard_unit_vectors
Base.@deprecate_binding isglobal is_global
Base.@deprecate_binding isgraded is_graded
Base.@deprecate_binding isinner_automorphism is_inner_automorphism
Base.@deprecate_binding isinvariant is_invariant
Base.@deprecate_binding isisomorphic_with_alternating_group is_isomorphic_to_alternating_group
Base.@deprecate_binding isisomorphic_with_symmetric_group is_isomorphic_to_symmetric_group
Base.@deprecate_binding isleft is_left
Base.@deprecate_binding islocal is_local
Base.@deprecate_binding ismixed is_mixed
Base.@deprecate_binding ismolien_series_implemented is_molien_series_implemented
Base.@deprecate_binding isnatural_alternating_group is_natural_alternating_group
Base.@deprecate_binding isnatural_symmetric_group is_natural_symmetric_group
Base.@deprecate_binding isnef is_nef
Base.@deprecate_binding isobviouslyabelian is_obviously_abelian false
Base.@deprecate_binding isorbifold is_orbifold
Base.@deprecate_binding isperfect is_perfect
Base.@deprecate_binding ispgroup is_pgroup
Base.@deprecate_binding ispointed is_pointed
Base.@deprecate_binding isprojective is_projective
Base.@deprecate_binding ispure is_pure
Base.@deprecate_binding isquaternion_group is_quaternion_group
Base.@deprecate_binding isright is_right
Base.@deprecate_binding issemiregular is_semiregular
Base.@deprecate_binding issemisimple is_semisimple
Base.@deprecate_binding issimplicial is_simplicial
Base.@deprecate_binding issingular is_singular
#Base.@deprecate_binding issmooth_curve is_smooth_curve
Base.@deprecate_binding issolvable is_solvable
Base.@deprecate_binding issupersolvable is_supersolvable
Base.@deprecate_binding istransitive is_transitive
Base.@deprecate_binding isunipotent is_unipotent
Base.@deprecate_binding isunital is_unital
Base.@deprecate_binding iswelldefined is_welldefined
Base.@deprecate_binding representative_action is_conjugate_with_data
Base.@deprecate_binding representative_action_in_gl_or_sl is_conjugate_with_data_in_gl_or_sl

Base.@deprecate_binding has_isfinite has_is_finite
Base.@deprecate_binding SymmetricGroup symmetric_group

# Allow backwards compatibility after removal of Oscar.Graphs module.
const Graphs = Oscar

# Compatibility with pre-0.12.x
Base.@deprecate_binding MPolyElem_dec MPolyDecRingElem
Base.@deprecate_binding MPolyRing_dec MPolyDecRing
Base.@deprecate_binding MPolyLocalizedRingElem MPolyLocRingElem
Base.@deprecate_binding MPolyLocalizedRing MPolyLocRing
Base.@deprecate_binding MPolyQuoElem MPolyQuoRingElem
Base.@deprecate_binding MPolyQuo MPolyQuoRing
Base.@deprecate_binding MPolyQuoLocalizedRingElem MPolyQuoLocRingElem
Base.@deprecate_binding MPolyQuoLocalizedRing MPolyQuoLocRing
Base.@deprecate_binding SubQuoElem SubquoModuleElem
Base.@deprecate_binding SubQuo SubquoModule
#@alias SubQuoElem_dec SubquoDecModuleElem
#@alias SubQuo_dec SubquoDecModule
Base.@deprecate_binding GradedPolynomialRing graded_polynomial_ring


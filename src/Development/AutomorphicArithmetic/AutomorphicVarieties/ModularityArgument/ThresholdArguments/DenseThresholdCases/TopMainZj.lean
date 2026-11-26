module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.SerreTate
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TemperedProductOfSquareIntegrable
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Batteries.Tactic.OpenPrivate
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.AbsNormConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DnEndsTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SeedIIZ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkedUnlE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KatoTwoWOfPublishedH
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.CuspOfCq

@[expose] public section

attribute [-instance]
  Formalism.LFunctionChainParameters.LChain6.FamC.indexKFirst
  Formalism.LFunctionChainParameters.LChain6.FamC.indexKSecond
  Formalism.LFunctionChainParameters.LChain6.FamC.indexKThird
  Formalism.LFunctionChainParameters.LChain6.FamC.indexKFourth
  Formalism.BasicNotions.NTypes.instMray
  Formalism.BasicNotions.NTypes.nfMray
  Formalism.BasicNotions.NTypes.algKM
  UpperTheory.V.Pr.IsCD.toIsDomain
  UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete
  UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Pr.IsCD.isLocalHom
  UpperTheory.V.Alg.IsCO.toIsLocalRing
  UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom
  UpperTheory.V.Alg.IsCO.self
  UpperTheory.V.UnitaryThreeInertia.Coef.isLocalRing

/-!
# Stage 3 — Tate–Shafarevich Window Bound Assembly (`automorphic_window_of_inputs` → `VWin`)

Packages the local representation-theory (`LitLocAlt`), automorphic (`LiteratureAutomorphyHypothesis`),
Galois-cohomology (`LitCoh`), and CM/abelian (`LiteratureCMHypothesis`) published inputs from
`TemperedProductOfSquareIntegrable.lean` into `v_window_of_literal_automorphy_n` to establish
the Tate–Shafarevich window bound `UpperTheory.Top.VWin` (`VVle E ⌊x^401⌋ √(exp(x^ε))` on
quadratic windows `[W, W^2]`), which Stage 4 rescales to `[Z, Z^(3/2)]` via `supplyChi`.
-/

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WindowBoundOfLiteratureLevel
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Sp4In0
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcIndCs
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IndAutLOfSplit
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthIndS
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EGPolMix
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Base UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E
open scoped Matrix
private theorem alg_closure_of (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (k₀ : IntermediateField ℚ Ω) :
    IsAlgClosure k₀ Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) k₀⟩
private theorem conj_el_ex (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (k₀ : IntermediateField ℚ Ω) [NumberField k₀]
    [IsTotallyReal k₀] : ∃ c : G k₀ Ω, IsConjEl c := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let j : Ω →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
  let c : Ω ≃ₐ[ℚ] Ω := τ.restrictNormal Ω
  have hc : ∀ x, algebraMap Ω ℂ (c x) = starRingEnd ℂ (algebraMap Ω ℂ x) := fun x => AlgEquiv.restrictNormal_commutes τ Ω x
  have hfix : ∀ y : k₀, c (y : Ω) = y := fun y => by
    apply (algebraMap Ω ℂ).injective
    rw [hc]
    let φ : k₀ →+* ℂ := (algebraMap Ω ℂ).comp (algebraMap k₀ Ω)
    have hr : ComplexEmbedding.IsReal φ :=
      InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal (InfinitePlace.mk φ))
    exact RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 hr) y
  refine ⟨AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun y => hfix y, algebraMap Ω ℂ, fun x => hc x⟩
private theorem pair_two {k : Type} [Field k] (A : Matrix (Fin 2) (Fin 2) k) :
    Aᵀ * !![0, 1; -1, 0] * A = A.det • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
private theorem pairing_two {F Ω k : Type} [Field F] [Field Ω] [Algebra F Ω] [Field k] (r : G F Ω →* GL (Fin 2) k) (c : G F Ω) :
    ∃ P, IsPairing c r ((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω)) P := by
  let J : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])
  refine ⟨J * r c⁻¹, fun s s' h => ?_⟩
  have h' : s' = c * s * c⁻¹ := h
  have e : r c⁻¹ * r s' = r s * r c⁻¹ := by rw [h', ← map_mul, ← map_mul]; congr 1; group
  have e' : (r c⁻¹).val * (r s').val = (r s).val * (r c⁻¹).val := congrArg Units.val e
  have hp : (r s).valᵀ * J.val * (r s).val = (r s).val.det • J.val := pair_two _
  have hd : (((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω) s : kˣ) : k) = (r s).val.det := rfl
  rw [hd, Units.val_mul, ← Matrix.smul_mul, ← hp]
  simp only [Matrix.mul_assoc, e']
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.polMix_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.PolMix := by
  intro H Ω _ _ _ l _ k₀ _ _ ι x k t r hd hm
  obtain ⟨m, hm0, hm⟩ := hm
  haveI : IsAlgClosure k₀ Ω := alg_closure_of Ω k₀
  have hdet : ∀ s, Matrix.GeneralLinearGroup.det (r s) = cycBar k₀ Ω l s ^ k * x (resQ k₀ s) := fun s =>
    DFunLike.congr_fun hd.det s
  have hcont : Continuous (Matrix.GeneralLinearGroup.det.comp r) :=
    Matrix.GeneralLinearGroup.continuous_det.comp hd.cont
  have halg : Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp r) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s H k₀ Ω l ι).1 _ hcont fun w _ => ?_
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    refine ⟨A, hA, k, m, hm0, fun s _ => ?_⟩
    have hx : x (resQ k₀ s) ^ m = 1 := by
      have := DFunLike.congr_fun hm (resQ k₀ s)
      simpa using this
    rw [MonoidHom.comp_apply, hdet, zpow_neg, zpow_natCast, mul_comm (cycBar k₀ Ω l s ^ k), mul_inv_cancel_right, hx]
  have hsign : Sol.SameSign (Matrix.GeneralLinearGroup.det.comp r) := by
    intro c c' hc hc'
    have hres : ∀ {a : G k₀ Ω}, IsConjEl a → IsConjEl (resQ k₀ a) := fun ⟨j, hj⟩ => ⟨j, hj⟩
    have hcj : IsConj (resQ k₀ c) (resQ k₀ c') := UpperTheory.complex_conjugations_are_conjugate Ω _ _ (hres hc) (hres hc')
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hdet, hdet, UpperTheory.cyclotomic_char_conj_invariant k₀ Ω l c hc, UpperTheory.cyclotomic_char_conj_invariant k₀ Ω l c' hc',
      isConj_iff_eq.1 (MonoidHom.map_isConj x hcj)]
  obtain ⟨c, hc⟩ := conj_el_ex Ω k₀
  obtain ⟨P, hP⟩ := pairing_two r c
  exact ⟨k₀, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, P, halg, hsign, hc, hP⟩
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Z.Bc UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E
private theorem deg_two {Ω : Type} [Field Ω] [CharZero Ω] (A B M : IntermediateField ℚ Ω) [FiniteDimensional ℚ A]
    [FiniteDimensional ℚ B] (hM : M = A ⊔ B) (hA : Module.finrank ℚ A = 2) (hn : ¬ A ≤ B) [Algebra B M] [IsScalarTower ℚ B M] :
    Module.finrank B M = 2 := by
  have h1 : Module.finrank ℚ M ≤ Module.finrank ℚ A * Module.finrank ℚ B := hM ▸ IntermediateField.finrank_sup_le A B
  haveI : FiniteDimensional ℚ M := hM ▸ IntermediateField.finiteDimensional_sup A B
  haveI : Module.Free B M := Module.Free.of_divisionRing B M
  have h2 := Module.finrank_mul_finrank ℚ B M
  have h3 : 0 < Module.finrank ℚ B := Module.finrank_pos
  have h4 : 0 < Module.finrank ℚ M := Module.finrank_pos
  have h5 : Module.finrank ℚ B ≠ Module.finrank ℚ M := fun e =>
    hn (IntermediateField.eq_of_le_of_finrank_eq (hM ▸ le_sup_right : B ≤ M) e ▸ (hM ▸ le_sup_left : A ≤ M))
  generalize Module.finrank B M = n at h2 ⊢
  rw [hA, ← h2, mul_comm 2] at h1
  have h6 := Nat.le_of_mul_le_mul_left h1 h3
  rw [← h2] at h4 h5
  interval_cases n <;> simp_all
private theorem two_places {k : Type} [Field k] [NumberField k] [IsTotallyReal k] (h : Module.finrank ℚ k = 2)
    {v v' : InfinitePlace k} (hv : v ≠ v') (w : InfinitePlace k) : w = v ∨ w = v' := by
  classical
  by_contra hw
  push Not at hw
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank k
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces k
  have h3 : ({w, v, v'} : Finset (InfinitePlace k)).card = 3 := Finset.card_eq_three.2 ⟨w, v, v', hw.1, hw.2, hv, rfl⟩
  have h4 := Finset.card_le_univ ({w, v, v'} : Finset (InfinitePlace k))
  omega
private theorem two_emb {L M : Type} [Field L] [Field M] [CharZero L] [Algebra L M] (h : Module.finrank L M = 2) (φ : L →+* ℂ) :
    ∃ τ τ' : M →+* ℂ, τ ≠ τ' ∧ τ.comp (algebraMap L M) = φ ∧ τ'.comp (algebraMap L M) = φ := by
  letI : Algebra L ℂ := φ.toAlgebra
  haveI : FiniteDimensional L M := Module.finite_of_finrank_pos (by omega)
  have hc := AlgHom.card L M ℂ
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := M →ₐ[L] ℂ) (by omega)
  exact ⟨a, b, fun e => hab (AlgHom.coe_ringHom_injective e), a.comp_algebraMap, b.comp_algebraMap⟩
private theorem hom_ext_sup {Ω : Type} [Field Ω] [CharZero Ω] (A B M : IntermediateField ℚ Ω) (hA : A ≤ M) (hB : B ≤ M)
    (hM : M ≤ A ⊔ B) (τ τ' : M →+* ℂ) (eA : ∀ x : A, τ ⟨x, hA x.2⟩ = τ' ⟨x, hA x.2⟩) (eB : ∀ x : B, τ ⟨x, hB x.2⟩ = τ' ⟨x, hB x.2⟩) :
    τ = τ' := by
  let S : IntermediateField ℚ M := (τ.eqLocusField τ').toIntermediateField fun q => by
    rw [RingHom.mem_eqLocusField]
    simp
  have h : M ≤ IntermediateField.lift S := hM.trans <| sup_le
    (fun x hx => (IntermediateField.mem_lift (⟨x, hA hx⟩ : M)).2 (eA ⟨x, hx⟩))
    (fun x hx => (IntermediateField.mem_lift (⟨x, hB hx⟩ : M)).2 (eB ⟨x, hx⟩))
  ext x
  exact (IntermediateField.mem_lift x).1 (h x.2)
private theorem inf_reg (m : Fin 2 → ℤ) (h : m 0 ≠ m 1) :
    (infOf m).Nodup ∧ ∀ z ∈ infOf m, ∃ n : ℤ, z = (n : ℂ) + (((2 : ℕ) : ℂ) - 1) / 2 := by
  refine ⟨Multiset.Nodup.map (fun i j e => ?_) Finset.univ.nodup, fun z hz => ?_⟩
  · have e' : m i = m j := by exact_mod_cast add_left_cancel e
    fin_cases i <;> fin_cases j <;> simp_all
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨m i, add_comm _ _⟩
private theorem val_of_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) (p : ℕ) : A.valuation (p : Ω) < 1 ↔ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  rw [← hA]
  simp
set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutLP_of_upQuad_upSol_indAutCs (H : _root_.UpperTheory.V.Af.HypothesesH') : UpQuadI → UpSolI → IndAutCs → IndAutLP := by
  intro hQ hS hI Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r α β R δ h hrw
  have hKL : T.K ≤ T.L := T.hL ▸ le_sup_right
  have hfix : ∀ g : G T.F Ω, g ∈ T.GalL → resQ T.F g ∈ T.L.fixingSubgroup := fun g hg => by
    rw [T.hL, IntermediateField.fixingSubgroup_sup]
    exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => g.commutes ⟨y, hy⟩, hg⟩
  have hirr : IsIrr ((R.comp (resQ T.F)).comp T.G'.subtype) := UpperTheory.induced_irreducible Ω l c D T k₀ φ ι k t r α β R δ h
  have hL : IsIrr (R.comp (resQ T.L)) := by
    obtain ⟨h1, -, h3⟩ := hirr
    refine ⟨h1, fun _ _ _ => Submodule.mem_top, fun W hW hi => h3 W hW fun g v hv => ?_⟩
    have hg : resQ T.F g ∈ galOf ℚ T.L Ω := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hfix g g.2.1) x x.2
    rw [← range_galEmb] at hg
    obtain ⟨g', hg'⟩ := hg
    have := hi g' v hv
    rwa [show (R.comp (resQ T.L)) g' = R (resQ T.F g) from congrArg R hg'] at this
  have hkL : ¬ k₀ ≤ T.L := fun hle => by
    obtain ⟨g, hg, hne⟩ := UpperTheory.residual_characters_psi_ne Ω l c D T h.hyp.good h.hyp.ok h.hyp.two
    exact hne ((h.hyp.ps g).2 (IntermediateField.fixingSubgroup_le hle (hfix g hg.1)))
  have hKk : ¬ T.K ≤ k₀ := fun hle => by
    letI : Algebra T.K k₀ := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    haveI : IsTotallyComplex k₀ := isTotallyComplex_of_algebra T.K k₀
    obtain ⟨w⟩ : Nonempty (InfinitePlace k₀) := inferInstance
    exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w) (IsTotallyReal.isReal w)
  haveI := T.nK.to_finiteDimensional
  haveI := T.nL.to_finiteDimensional
  haveI : FiniteDimensional ℚ k₀ := NumberField.to_finiteDimensional
  obtain ⟨E, hE⟩ : ∃ E : IntermediateField ℚ Ω, E = k₀ ⊔ T.K := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : IntermediateField ℚ Ω, M = k₀ ⊔ T.L := ⟨_, rfl⟩
  haveI : FiniteDimensional ℚ E := hE ▸ IntermediateField.finiteDimensional_sup k₀ T.K
  haveI : FiniteDimensional ℚ M := hM ▸ IntermediateField.finiteDimensional_sup k₀ T.L
  haveI : NumberField E := {}
  haveI : NumberField M := {}
  have hEM : E ≤ M := hE ▸ hM ▸ sup_le_sup_left hKL _
  have hKE : T.K ≤ E := hE ▸ le_sup_right
  have hkE : k₀ ≤ E := hE ▸ le_sup_left
  have hLM : T.L ≤ M := hM ▸ le_sup_right
  letI : Algebra T.K E := (IntermediateField.inclusion hKE).toRingHom.toAlgebra
  letI : Algebra k₀ E := (IntermediateField.inclusion hkE).toRingHom.toAlgebra
  letI : Algebra T.L M := (IntermediateField.inclusion hLM).toRingHom.toAlgebra
  letI : Algebra E M := (IntermediateField.inclusion hEM).toRingHom.toAlgebra
  haveI : IsScalarTower k₀ E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower T.L M Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower E M Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ k₀ E := IsScalarTower.of_algebraMap_eq fun _ => by simp
  haveI : IsScalarTower ℚ T.L M := IsScalarTower.of_algebraMap_eq fun _ => by simp
  haveI : IsScalarTower ℚ E M := IsScalarTower.of_algebraMap_eq fun _ => by simp
  haveI : IsTotallyComplex E := isTotallyComplex_of_algebra T.K _
  haveI : IsTotallyComplex M := isTotallyComplex_of_algebra T.L _
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : Algebra.IsQuadraticExtension ℚ T.K := { finrank_eq_two' := T.degK }
  haveI hK : IsAbelianGalois ℚ T.K := IsAbelianGalois.of_isCyclic ℚ T.K
  haveI : Algebra.IsQuadraticExtension ℚ k₀ := { finrank_eq_two' := h.hyp.deg }
  haveI hk₀ : IsAbelianGalois ℚ k₀ := IsAbelianGalois.of_isCyclic ℚ k₀
  haveI hLa : IsAbelianGalois ℚ T.L := by
    have h := @GroundTheory.Global.isAbelianGalois_sup ℚ Ω _ _ _ _ T.F T.K
      T.nF.to_finiteDimensional T.nK.to_finiteDimensional T.abF hK
    rw [← T.hL] at h
    exact h
  haveI : IsAbelianGalois ℚ M := hM ▸ @GroundTheory.Global.isAbelianGalois_sup ℚ Ω _ _ _ _ k₀ T.L ‹_› ‹_› hk₀ hLa
  haveI : IsAbelianGalois E M := IsAbelianGalois.tower_top ℚ _ _
  haveI : Group.IsSolvable (M ≃ₐ[E] M) := Group.isSolvable_of_comm fun a b => mul_comm' a b
  have dE : Module.finrank k₀ E = 2 := deg_two T.K k₀ _ (hE.trans (sup_comm _ _)) T.degK hKk
  have dM : Module.finrank T.L M = 2 := deg_two k₀ T.L _ hM h.hyp.deg hkL
  obtain ⟨π, hatt, v, v', hv, hi, hi'⟩ := h.dat.att
  have hk := h.dat.hk
  have ht := h.dat.ht
  have hreg : π.IsRegAlg := fun w => by
    rcases two_places h.hyp.deg hv w with rfl | rfl
    · exact ⟨_, hi, inf_reg _ (by simp; omega)⟩
    · exact ⟨_, hi', inf_reg _ (by simp; omega)⟩
  have RE := resFacts k₀ E Ω l 2 r
  have RM := resFacts E M Ω l 2 (r.comp (galEmb k₀ E Ω))
  obtain ⟨P₁, reg₁, att₁, inf₁⟩ := hQ k₀ E Ω l ι dE r π h.dat.cont hreg hatt (RE.2.2.2.1.1 (h.dat.irr _ RE.2.1))
  obtain ⟨P, reg, att, inf⟩ := hS E M Ω l ι _ P₁ (h.dat.cont.comp RE.1) reg₁ att₁
    (RM.2.2.2.1.1 (RE.2.2.2.2.1 h.dat.irr _ RM.2.1))
  haveI : IsCMField M := IsCMField.of_isAbelianGalois M
  haveI : IsAbelianGalois T.L M := IsAbelianGalois.tower_top ℚ _ _
  have hMfix : ∀ s : G T.L Ω, resQ T.L s ∈ k₀.fixingSubgroup → ∀ x : M, s (algebraMap M Ω x) = algebraMap M Ω x := fun s hs x => by
    have : resQ T.L s ∈ M.fixingSubgroup := by
      rw [hM, IntermediateField.fixingSubgroup_sup]
      exact ⟨hs, (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => s.commutes ⟨y, hy⟩⟩
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 this x x.2
  have hsp : ∀ (p : ℕ) (v : HeightOneSpectrum (𝓞 T.L)), S2.SplitIn p k₀ → ((p : ℕ) : 𝓞 T.L) ∈ v.asIdeal → UpperTheory.ConvolutionTheory.GM.Split M v :=
    fun p v hp hv => splitOfDec T.L M Ω v fun A hA s hs => hMfix s (hp A ((val_of_mem hA p).2 hv) hs)
  have hpol : Sol.Pol ι ((r.comp (galEmb k₀ E Ω)).comp (galEmb E M Ω)) := by
    obtain ⟨m, hm⟩ := h.hyp.two.ord
    refine UpperTheory.solvable_polarized_restriction E M Ω l ι 2 _ (UpperTheory.solvable_polarized_restriction k₀ E Ω l ι 2 r (_root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.polMix_alt H Ω l k₀ ι _ k t r h.dat ⟨2 ^ m, by positivity, ?_⟩))
    refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, S2.up, MonoidHom.comp_apply, ← map_pow, ← MonoidHom.pow_apply, hm, MonoidHom.one_apply, map_one,
      MonoidHom.one_apply]
  haveI : IsAbelianGalois ℚ E := IsAbelianGalois.tower_bot ℚ E M
  haveI : IsCMField E := IsCMField.of_isAbelianGalois E
  have hW : AllW ι ((r.comp (galEmb k₀ E Ω)).comp (galEmb E M Ω)) := by
    haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
    have h1 : Sd.IsAlgChar ι (1 : G E Ω →* (Qbar l)ˣ) := by simpa using (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results H.toClassicalTheorems E Ω l ι).1 0 1 (by rw [MonoidHom.ker_one]; exact isOpen_univ)
    have h2 := _root_.UpperTheory.V.Z.Win.Birth.awChain_of_printsH H k₀ E M Ω dE l ι r 1 h.dat.cont hrw h1 (RM.2.2.2.1.1 (RE.2.2.2.2.1 h.dat.irr _ RM.2.1))
    have e : tw (r.comp (galEmb k₀ E Ω)) 1 = r.comp (galEmb k₀ E Ω) := MonoidHom.ext fun g => Units.ext (by rw [tw_val]; simp)
    rwa [e] at h2
  have hbad : SplitBad T.L P := fun v hv => by
    refine ⟨unrOfIne T.L M Ω v fun A _ s hs => hMfix s ?_, fun w hw => ?_⟩
    · let g : G T.F Ω := AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun x => s.commutes ⟨x, T.F_le x.2⟩
      exact (h.hyp.ps g).1 (h.hyp.two.unr A g ⟨hs.1, hs.2⟩)
    · have hn : ∀ p : ℕ, S2.SplitIn p k₀ → ((p : ℕ) : 𝓞 M) ∉ w.asIdeal := fun p hp hm => hv (hsp p v hp (by
        rw [← hw]
        change algebraMap (𝓞 T.L) (𝓞 M) p ∈ w.asIdeal
        rwa [map_natCast]))
      obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
      haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
      refine _root_.UpperTheory.V.Z.Win.Birth.sphOfUnrW_alt H M Ω l ι 2 one_le_two _ P ((h.dat.cont.comp RE.1).comp RM.1) hpol reg att
        hW w (hn l h.hyp.spl) A hA fun s hs => ?_
      obtain ⟨g, hg⟩ := h.dat.away A (mt (val_of_mem hA l).1 (hn l h.hyp.spl))
      have h2 : D.ξ (resQ k₀ (galEmb k₀ E Ω (galEmb E M Ω s))) = 1 :=
        h.hyp.two.xi A (fun p hp => by
          rw [Finset.mem_singleton.1 hp]
          exact mt (val_of_mem hA 2).1 (hn 2 h.hyp.sp2)) ⟨hs.1, hs.2⟩
      have h3 := hg (galEmb k₀ E Ω (galEmb E M Ω s)) ⟨hs.1, hs.2⟩
      have h5 : (S2.up D.ξ).comp (resQ k₀) (galEmb k₀ E Ω (galEmb E M Ω s)) = 1 := by
        rw [MonoidHom.comp_apply, S2.up, MonoidHom.comp_apply, h2, map_one]
      generalize (S2.up D.ξ).comp (resQ k₀) = y at h3 h5
      have h4 : g * r (galEmb k₀ E Ω (galEmb E M Ω s)) * g⁻¹ = 1 := Units.ext (h3.trans (by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h5]))
      exact mul_left_cancel (a := g) (by rw [mul_one]; exact mul_inv_eq_one.1 h4)
  refine (fun h1 h2 => And.intro (hI T.L M Ω dM l ι P _ att h1 hbad _ ((UpperTheory.galoisRep_irreducibility_criterion.1 _ Unit _ 4 _).2.1 hL) h2)
    (awInd T.L M Ω dM l ι P _ att (hW P reg att) hbad _ h2)) (fun ψ => ?_) fun s hs => ?_
  · obtain ⟨τ, τ', hne, e, e'⟩ := two_emb dM ψ
    let pl : (M →+* ℂ) → InfinitePlace k₀ := fun τ =>
      InfinitePlace.mk ((τ.comp (algebraMap E M)).comp (algebraMap k₀ E))
    have hpl : ∀ τ m, π.HasInfChar (pl τ) m → P.HasInfChar τ m := fun τ m hm => inf τ m (inf₁ _ m hm)
    have hd : pl τ ≠ pl τ' := fun hp => by
      refine hne (hom_ext_sup k₀ T.L M (hkE.trans hEM) hLM hM.le τ τ' (fun x => ?_) fun x => DFunLike.congr_fun (e.trans e'.symm) x)
      rcases InfinitePlace.mk_eq_iff.1 hp with hp | hp
      · exact DFunLike.congr_fun hp x
      · rw [ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))] at hp
        exact DFunLike.congr_fun hp x
    have hinj : Function.Injective ![![(k : ℤ) + t, -(t : ℤ)] 0, ![(k : ℤ) + t, -(t : ℤ)] 1, ![(k : ℤ), 0] 0, ![(k : ℤ), 0] 1] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first | rfl | (simp at hij <;> omega)
    rcases two_places h.hyp.deg hv (pl τ) with p | p <;> rcases two_places h.hyp.deg hv (pl τ') with p' | p'
    · exact absurd (p.trans p'.symm) hd
    · exact ⟨_, _, τ, τ', hne, e, e', hpl _ _ (p ▸ hi), hpl _ _ (p' ▸ hi'), hinj⟩
    · exact ⟨_, _, τ', τ, hne.symm, e', e, hpl _ _ (p' ▸ hi), hpl _ _ (p ▸ hi'), hinj⟩
    · exact absurd (p.trans p'.symm) hd
  · have hs' : resQ T.L s ∉ (resQ k₀).range := by
      rintro ⟨u, hu⟩
      apply hs
      rw [range_galEmb]
      have : resQ T.L s ∈ M.fixingSubgroup := by
        rw [hM, IntermediateField.fixingSubgroup_sup]
        exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => hu ▸ u.commutes ⟨y, hy⟩,
          (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => s.commutes ⟨y, hy⟩⟩
      exact fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 this x x.2
    obtain ⟨c1, c2⟩ := UpperTheory.symmetric_square_mixed_charpoly _ _ _ _ _ _ _ _ _ h.mix _ hs'
    refine ⟨fun g g' e => c1 (galEmb k₀ E Ω (galEmb E M Ω g)) (galEmb k₀ E Ω (galEmb E M Ω g')) ?_,
      fun g e => c2 (galEmb k₀ E Ω (galEmb E M Ω g)) ?_⟩
    · have := congrArg (resQ T.L) e
      rw [map_mul, map_mul, map_inv] at this
      exact this
    · have := congrArg (resQ T.L) e
      rw [map_mul] at this
      exact this
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Z.Bc UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutLP_of_printsH_upQuad_upSol_indCs (H : _root_.UpperTheory.V.Af.HypothesesH') (hQ : UpQuadI) (hS : UpSolI) (hI : IndCs) : _root_.UpperTheory.V.Z.Win.Birth.IndAutLP :=
  _root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutLP_of_upQuad_upSol_indAutCs H hQ hS (_root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutCs_of_alt H.toClassicalTheorems hI)
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section -- restored from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.LatticePeriodicFunctionRangeFinite
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem isSB_range_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (N : ℕ)
    (Φ : (κ → F) → ℂ), 0 < N → IsSB N Φ → (Set.range Φ).Finite := by
  intro F _ _ κ _ _ N Φ hN hSB
  classical
  obtain ⟨hsupp, hper⟩ := hSB
  have memLL : ∀ y : κ → F, y ∈ LL F κ ↔ ∀ k, IsIntegral ℤ (y k) := by
    intro y
    simp [LL, AddSubgroup.mem_pi, mem_integralClosure_iff]
  have memaL : ∀ (c : F) (x : κ → F), x ∈ aL κ c ↔ ∃ y ∈ LL F κ, c • y = x := by
    intro c x
    simp [aL]
  have intB : ∀ c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ,
      IsIntegral ℤ (∑ i, c i • integralBasis F i) := by
    intro c
    have hmem : (∑ i, c i • integralBasis F i) ∈ Submodule.span ℤ (Set.range (integralBasis F)) :=
      (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, rfl⟩
    obtain ⟨a, ha⟩ := (mem_span_integralBasis F).mp hmem
    rw [← ha]
    exact RingOfIntegers.isIntegral_coe a
  have decomp : ∀ z : F, IsIntegral ℤ z →
      ∃ c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ, ∑ i, c i • integralBasis F i = z := by
    intro z hz
    have hmem : z ∈ Submodule.span ℤ (Set.range (integralBasis F)) :=
      (mem_span_integralBasis F).mpr ⟨⟨z, hz⟩, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem
  have hNF : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hM : (0 : ℤ) < ((N * N : ℕ) : ℤ) := by positivity
  let g : (κ → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → Fin (N * N)) → ℂ := fun r =>
    Φ (fun k => (N : F)⁻¹ * ∑ i, (((r k i : ℕ) : ℤ) • integralBasis F i))
  refine ((Set.finite_range g).insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  rw [Set.mem_insert_iff]
  by_cases h0 : Φ x = 0
  · exact Or.inl h0
  right
  obtain ⟨y, hy, rfl⟩ := (memaL _ x).mp (hsupp x h0)
  have hyi := (memLL y).mp hy
  choose c hc using fun k => decomp (y k) (hyi k)
  have hcast : ∀ k i, (((c k i % ((N * N : ℕ) : ℤ)).toNat : ℕ) : ℤ) = c k i % ((N * N : ℕ) : ℤ) :=
    fun k i => Int.toNat_of_nonneg (Int.emod_nonneg _ hM.ne')
  refine ⟨fun k i => ⟨(c k i % ((N * N : ℕ) : ℤ)).toNat, ?_⟩, ?_⟩
  · have h2 := Int.emod_lt_of_pos (c k i) hM
    have h3 := hcast k i
    omega
  · show Φ (fun k => (N : F)⁻¹ *
        ∑ i, ((((c k i % ((N * N : ℕ) : ℤ)).toNat : ℕ) : ℤ) • integralBasis F i)) = Φ ((N : F)⁻¹ • y)
    simp only [hcast]
    have hl : ((N : F)⁻¹ • y - fun k => (N : F)⁻¹ *
        ∑ i, ((c k i % ((N * N : ℕ) : ℤ)) • integralBasis F i)) ∈ aL κ (N : F) := by
      rw [memaL]
      refine ⟨fun k => ∑ i, (c k i / ((N * N : ℕ) : ℤ)) • integralBasis F i, ?_, ?_⟩
      · rw [memLL]
        intro k
        exact intB _
      · funext k
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rw [← hc k, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [zsmul_eq_mul]
        have hdiv : ((c k i : ℤ) : F) = ((N : F) * N) * ((c k i / ((N * N : ℕ) : ℤ) : ℤ) : F) +
            ((c k i % ((N * N : ℕ) : ℤ) : ℤ) : F) := by
          exact_mod_cast (Int.mul_ediv_add_emod (c k i) ((N * N : ℕ) : ℤ)).symm
        have key : ∀ (cF rF qF : F), cF = ((N : F) * N) * qF + rF →
            (N : F) * (qF * integralBasis F i) =
              (N : F)⁻¹ * (cF * integralBasis F i) - (N : F)⁻¹ * (rF * integralBasis F i) := by
          intro cF rF qF h
          rw [h]
          field_simp
          ring
        exact key _ _ _ hdiv
    have hp := hper (fun k => (N : F)⁻¹ *
        ∑ i, ((c k i % ((N * N : ℕ) : ℤ)) • integralBasis F i)) _ hl
    rw [add_sub_cancel] at hp
    exact hp.symm

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_periodic_function_range_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (N : ℕ) (Φ : (κ → F) → ℂ), 0 < N → IsSB N Φ → (Set.range Φ).Finite := by
  first | exact @GlobalTheory.HilbertThetaSeries.isSB_range_finite | exact GlobalTheory.HilbertThetaSeries.isSB_range_finite | (intros; apply GlobalTheory.HilbertThetaSeries.isSB_range_finite <;> assumption)
end

section -- restored from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IntegralTestFunctionMulTraceCharacterQuadFormOfD
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem et_pow_den_eq_one {F : Type} [Field F] [NumberField F] (y : F) :
    et y ^ (Algebra.trace ℚ F y).den = 1 := by
  unfold et
  set q : ℚ := Algebra.trace ℚ F y
  rw [← Complex.exp_nat_mul]
  have h : ((q.den : ℕ) : ℂ) * (q : ℂ) = (q.num : ℂ) := by
    have := Rat.den_mul_eq_num q
    exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) this
  have : ((q.den : ℕ) : ℂ) * (2 * Real.pi * Complex.I * (q : ℂ)) = (q.num : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [← h]; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem padic_norm_et_eq_one {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (y : F) :
    ‖ι.symm (et y)‖ = 1 := by
  have h := congrArg (fun z => ‖ι.symm z‖) (et_pow_den_eq_one y)
  simp only [map_pow, norm_pow, map_one, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Rat.den_nz _)).1 h

theorem QF_mulVec_of_iso {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]
    {G S : Matrix κ κ ℤ} (h : Sᵀ * G * S = G) (x : κ → F) :
    QF G (S.map (Int.cast : ℤ → F) *ᵥ x) = QF G x := by
  have h' : (S.map (Int.cast : ℤ → F))ᵀ * G.map (Int.cast : ℤ → F) * S.map (Int.cast : ℤ → F)
      = G.map (Int.cast : ℤ → F) := by
    have := congrArg (fun A : Matrix κ κ ℤ => A.map (Int.castRingHom F)) h
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    exact this
  unfold QF BF
  congr 1
  conv_rhs => rw [← h']
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x,
    Matrix.vecMul_transpose]

theorem good_mul_et_QF : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (δ : F), IsDel p δ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ Φ : (κ → F) → ℂ, Good ι S Φ → ∀ b : F, PInt p (δ * b) → Good ι S fun x => Φ x * et (b * QF G x) := by
  intro F _ _ p hp ι δ hδ κ _ _ G S t hL Φ hΦ b hb
  obtain ⟨⟨N, hN, hNp, hsupp, hper⟩, hS, hint, h0⟩ := hΦ
  obtain ⟨M, hM, hMp, htr⟩ := (GlobalTheory.HilbertThetaSeries.denominators_prime_to F p hp.out δ hδ).2.2.1 b hb
  obtain ⟨hadd, hsmul, -, hI, hLL, haL, het, -⟩ := GlobalTheory.HilbertThetaSeries.formLatticeProps F κ G hL.pos
  have hN' : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hM' : (M : F) ≠ 0 := by exact_mod_cast hM.ne'
  have hnat : ∀ (n : ℕ) (l : κ → F), l ∈ LL F κ → (n : F) • l ∈ LL F κ := by
    intro n l hl
    rw [Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_mem _ hl n
  refine ⟨⟨N * N * M, by positivity, Nat.Coprime.mul_left (Nat.Coprime.mul_left hNp hNp) hMp, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨l, hl, rfl⟩ := (haL _ _).1 (hsupp x (left_ne_zero_of_mul hx))
    refine (haL _ _).2 ⟨_, hnat (N * M) l hl, ?_⟩
    rw [smul_smul]
    congr 1
    push_cast
    field_simp
  · intro x l' hl'
    obtain ⟨l, hl, rfl⟩ := (haL _ _).1 hl'
    have h1 : Φ (x + ((N * N * M : ℕ) : F) • l) = Φ x := by
      refine hper x _ ((haL _ _).2 ⟨_, hnat (N * M) l hl, ?_⟩)
      rw [smul_smul]
      congr 1
      push_cast
      ring
    show Φ _ * _ = Φ x * _
    rw [h1]
    by_cases hx : Φ x = 0
    · simp [hx]
    obtain ⟨y, hy, rfl⟩ := (haL _ _).1 (hsupp x hx)
    congr 1
    have hz : IsIntegral ℤ ((N : F) * BF G y l + ((N * N * N * N * M : ℕ) : F) * QF G l) :=
      ((isIntegral_natCast N).mul ((hI y hy).2 l hl)).add ((isIntegral_natCast _).mul (hI l hl).1)
    have h2 : b * QF G ((N : F)⁻¹ • y + ((N * N * M : ℕ) : F) • l) = b * QF G ((N : F)⁻¹ • y) +
        (M : F) * b * ((N : F) * BF G y l + ((N * N * N * N * M : ℕ) : F) * QF G l) := by
      rw [(hadd _ _).2, (hsmul _ y _).1, (hadd y _).1, (hsmul _ l y).1, (hsmul _ l y).2.1, (hadd l y).1]
      push_cast
      field_simp
      ring
    rw [h2, (het _ _).1, (het _ 0).2.2.1.2 (htr _ hz), mul_one]
  · intro x
    show Φ _ * _ = Φ x * _
    rw [hS, QF_mulVec_of_iso hL.iso]
  · intro x
    show ‖ι.symm (Φ x * _)‖ ≤ 1
    rw [map_mul, norm_mul, padic_norm_et_eq_one, mul_one]
    exact hint x
  · show ‖ι.symm (Φ 0 * _) - 1‖ ≤ _
    have : et (b * QF G (0 : κ → F)) = 1 := by simp [et, QF, BF]
    rw [this, mul_one]
    exact h0

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_test_function_mul_trace_character_quad_form_of_delta_integral : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (δ : F), IsDel p δ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ Φ : (κ → F) → ℂ, Good ι S Φ → ∀ b : F, PInt p (δ * b) → Good ι S fun x => Φ x * et (b * QF G x) := by
  first | exact @GlobalTheory.HilbertThetaSeries.good_mul_et_QF | exact GlobalTheory.HilbertThetaSeries.good_mul_et_QF | (intros; apply GlobalTheory.HilbertThetaSeries.good_mul_et_QF <;> assumption)
end

section -- restored from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaSeriesCongrOneModPOfIsometry
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem th_congr_one : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ Φ : (κ → F) → ℂ, Good ι S Φ → Small ι (p : ℝ)⁻¹ (th G Φ - 1) := by
  intro F _ _ _ p _ ι κ _ _ G S t hL Φ hΦ
  obtain ⟨⟨N, hN, hNp, hSB⟩, hinv, hbd, h0⟩ := hΦ
  have hp : p.Prime := Fact.out
  obtain ⟨hQ, hact, -, -⟩ := _root_.GlobalTheory.T.intMatrix_isometry_prime_order_lattice_stability F p hp κ G S t hL
  obtain ⟨hTP, -, hfin⟩ := _root_.GlobalTheory.T.evenPosGram_quadForm_totallyPositive_properness F κ G hL.pos
  obtain ⟨B, hB⟩ := ((_root_.GlobalTheory.T.lattice_periodic_function_range_finite F κ N Φ hN hSB).image (fun w => ‖w‖)).bddAbove
  have hB' : ∀ x, ‖Φ x‖ ≤ B := fun x => hB ⟨Φ x, ⟨x, rfl⟩, rfl⟩
  obtain ⟨-, -, -, hq⟩ := _root_.GlobalTheory.T.thetaSeries_holomorphic_qExpansion_of_bounded_coeff F κ G hL.pos ((N:F)⁻¹) Φ B hSB.1 hB'
  have hc := (_root_.GlobalTheory.T.qExpansion_linear_combination F _ _ _ _ (1:ℂ) hq hq).2.2.2
  have hq1 := (_root_.GlobalTheory.T.qExpansion_linear_combination F _ _ _ _ (1:ℂ) hq hc).2.2.1
  refine ⟨_, hq1, fun ξ => ?_⟩
  simp only [Pi.sub_apply]
  have hfs := hfin ((N:F)⁻¹) ξ
  rw [finsum_mem_eq_finite_toFinset_sum _ hfs]
  by_cases hξ : ξ = 0
  · subst hξ
    have hz : hfs.toFinset = {0} := by
      ext x
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_singleton]
      constructor
      · rintro ⟨-, hx⟩
        by_contra hne
        have h1 := hTP x hne
        rw [hx] at h1
        obtain ⟨v⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace F))
        have h2 := h1 v
        simp [reAt] at h2
      · rintro rfl
        exact ⟨zero_mem _, by simp [QF, BF]⟩
    rw [hz, Finset.sum_singleton, if_pos rfl, map_sub, map_one]
    exact h0
  · rw [if_neg hξ, sub_zero]
    apply _root_.GlobalTheory.T.norm_sum_free_orbits_le_inv_prime p ι (κ → F) (fun x => S.map Int.cast *ᵥ x) hfs.toFinset Φ
    · intro x hx
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
      exact ⟨((hact x).2.2.2 _).2 hx.1, ((hQ x x).2).trans hx.2⟩
    · intro x _
      exact (hact x).1
    · intro x hx h
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
      apply hξ
      rw [← hx.2, (hact x).2.1 h]
      simp [QF, BF]
    · intro x _
      exact hinv x
    · intro x _
      exact hbd x

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_congr_one_mod_p_of_isometry : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ Φ : (κ → F) → ℂ, Good ι S Φ → Small ι (p : ℝ)⁻¹ (th G Φ - 1) := by
  first | exact @GlobalTheory.HilbertThetaSeries.th_congr_one | exact GlobalTheory.HilbertThetaSeries.th_congr_one | (intros; apply GlobalTheory.HilbertThetaSeries.th_congr_one <;> assumption)
end

section -- restored from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaTranslateIntegralCongruentOneModPrime
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem theta_translates_integral_one : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ γ : GL (Fin 2) F, InG p δ γ → Small ι (p : ℝ)⁻¹ (sl0 (p - 1) (toInf γ) (th G oneL) - 1) := by
  intro F _ _ _ p _ ι hp2 δ hδ κ _ _ G S t hL γ hγ

  have hPos : ∀ g : GL (Fin 2) F, TP g.val.det → Pos (toInf g) := fun g hg =>
    ((GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash F (p - 1) (th G oneL)).2.1 g).1.2 hg
  have hTP1 : TP (1 : F) := fun v => by simp [reAt]
  have hdetw : ∀ c : Fˣ, (wm c).val.det = 1 := fun c => by
    simp [wm, Matrix.det_fin_two]
  have hdeta : ∀ (e : Fˣ) (b : F), (aff e b).val.det = e := fun e b => by
    simp [aff, Matrix.det_fin_two]
  have hPw : ∀ c : Fˣ, Pos (toInf (wm c)) := fun c => hPos _ (by rw [hdetw]; exact hTP1)
  have hPa : ∀ b : F, Pos (toInf (aff 1 b)) := fun b => hPos _ (by rw [hdeta]; simpa using hTP1)

  have haL1 : ∀ x : κ → F, x ∈ aL κ (1 : F) ↔ x ∈ LL F κ := fun x => by
    simp [aL, AddSubgroup.mem_map]
  have hone : ∀ x y : κ → F, (x ∈ LL F κ ↔ y ∈ LL F κ) → oneL x = oneL y := fun x y h => by
    by_cases hy : y ∈ LL F κ
    · rw [oneL, oneL, if_pos hy, if_pos (h.2 hy)]
    · rw [oneL, oneL, if_neg hy, if_neg fun hx => hy (h.1 hx)]

  have hgood1 : Good ι S (oneL (F := F) (κ := κ)) := by
    have hS := (GlobalTheory.HilbertThetaSeries.IsoP.isometry_order_p F p Fact.out κ G S t hL).2.1
    refine ⟨⟨1, one_pos, Nat.coprime_one_left p, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro x hx
      have hx' : x ∈ LL F κ := by
        by_contra h; exact hx (by simp [oneL, h])
      simpa [haL1] using hx'
    · intro x l hl
      have hl' : l ∈ LL F κ := by simpa [haL1] using hl
      exact hone _ _ ((LL F κ).add_mem_cancel_right hl')
    · intro x
      have h1 := ((hS x).2.2.2 1)
      rw [haL1, haL1] at h1
      exact hone _ _ h1
    · intro x
      unfold oneL; split_ifs <;> simp
    · have h0 : (0 : κ → F) ∈ LL F κ := (LL F κ).zero_mem
      simp only [oneL, h0, if_true, map_one, sub_self, norm_zero]
      positivity

  have hW : ∀ (c : Fˣ) (Φ : (κ → F) → ℂ), Good ι S Φ → PUnit p ((c : F) / δ) →
      ∃ Ψ, Good ι S Ψ ∧ sl0 (p - 1) (toInf (wm c)) (th G Φ) = th G Ψ := by
    intro c Φ hΦ hc
    obtain ⟨N, hN, hNp, hSB⟩ := hΦ.1
    have hNF : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
    have hint : IsIntegral ℤ ((N : F) / (N : F)⁻¹) := by
      rw [div_inv_eq_mul, ← Nat.cast_mul]
      simpa using isIntegral_algebraMap (R := ℤ) (A := F) (x := ((N * N : ℕ) : ℤ))
    obtain ⟨T, hT, h0T, hle, -⟩ := GlobalTheory.HilbertThetaSeries.exists_isReps_aL F κ (N : F) (N : F)⁻¹ hNF (inv_ne_zero hNF) hint
    refine ⟨_, GlobalTheory.T.integral_test_function_finite_fourier_transform_of_odd_prime F p ι hp2 δ hδ κ G S t hL Φ N T c hΦ hN hNp hSB hT h0T hc, ?_⟩
    exact GlobalTheory.T.hilbertThetaSeries_periodic_inversion_formula F κ G hL.pos t hL.det (p - 1) hL.card (N : F) (N : F)⁻¹ c T Φ hNF (inv_ne_zero hNF) hle hT hSB.1 hSB.2

  have hA : ∀ (b : F) (Φ : (κ → F) → ℂ), Good ι S Φ → PInt p (δ * b) →
      ∃ Ψ, Good ι S Ψ ∧ sl0 (p - 1) (toInf (aff 1 b)) (th G Φ) = th G Ψ := fun b Φ hΦ hb =>
    ⟨_, GlobalTheory.T.integral_test_function_mul_trace_character_quad_form_of_delta_integral F p ι δ hδ κ G S t hL Φ hΦ b hb, GlobalTheory.HilbertThetaSeries.th_translate F κ G (p - 1) b Φ⟩

  let P : GL (Fin 2) F → Prop := fun g => Pos (toInf g) ∧
    ∃ Ψ, Good ι S Ψ ∧ sl0 (p - 1) (toInf g) (th G oneL) = th G Ψ
  have step : ∀ g g' : GL (Fin 2) F, P g → Pos (toInf g') →
      (∀ Ψ, Good ι S Ψ → ∃ Ψ', Good ι S Ψ' ∧ sl0 (p - 1) (toInf g') (th G Ψ) = th G Ψ') → P (g * g') := by
    intro g g' ⟨hg, Ψ, hΨ, he⟩ hg' hstep
    have hc := SlashCocycle.slash_cocycle F (p - 1) (toInf g) (toInf g') (th G oneL) hg hg'
    obtain ⟨Ψ', hΨ', he'⟩ := hstep Ψ hΨ
    refine ⟨by rw [map_mul]; exact hc.1, Ψ', hΨ', ?_⟩
    rw [map_mul, hc.2.2.1, he, he']
  obtain ⟨b₁, b₂, b₃, c₁, c₂, c₃, ε, hb₁, hb₂, hb₃, hc₁, hc₂, hc₃, hε, hγe⟩ := GlobalTheory.HilbertThetaSeries.gen_by_translations_inversions F p Fact.out δ hδ γ hγ
  have P1 : P (wm c₁) := by
    refine ⟨hPw c₁, ?_⟩
    exact hW c₁ oneL hgood1 hc₁
  have P6 := step _ _ (step _ _ (step _ _ (step _ _ (step _ _ P1 (hPa b₁) (fun Ψ h => hA b₁ Ψ h hb₁))
    (hPw c₂) (fun Ψ h => hW c₂ Ψ h hc₂)) (hPa b₂) (fun Ψ h => hA b₂ Ψ h hb₂))
    (hPw c₃) (fun Ψ h => hW c₃ Ψ h hc₃)) (hPa b₃) (fun Ψ h => hA b₃ Ψ h hb₃)
  obtain ⟨hX, Ψ, hΨ, hXe⟩ := P6
  have hE : Pos (toInf (aff ε 0)) := hPos _ (by rw [hdeta]; exact hε)
  have hc := SlashCocycle.slash_cocycle F (p - 1) (toInf (wm c₁ * aff 1 b₁ * wm c₂ * aff 1 b₂ * wm c₃ * aff 1 b₃)) (toInf (aff ε 0)) (th G oneL) hX hE
  rw [hγe, map_mul, hc.2.2.1, hXe]

  have hden : ∀ z : Hn F, (∏ v, UpperHalfPlane.denom (cmp v (toInf (aff ε 0))) (z v)) = 1 := by
    intro z
    refine Finset.prod_eq_one fun v _ => ?_
    simp [UpperHalfPlane.denom, cmp, toInf, aff, Matrix.GeneralLinearGroup.map]
  have hsub : sl0 (p - 1) (toInf (aff ε 0)) (th G Ψ - 1) = sl0 (p - 1) (toInf (aff ε 0)) (th G Ψ) - 1 := by
    funext z
    simp [sl0, hden]
  rw [← hsub]
  obtain ⟨a, hQ, hbd⟩ := GlobalTheory.T.thetaSeries_congr_one_mod_p_of_isometry F p ι κ G S t hL Ψ hΨ
  refine ⟨_, GlobalTheory.T.hasQExpansion_affineTranslate_coeff F (p - 1) (th G Ψ - 1) a ε 0 hε hQ, fun ξ => ?_⟩
  simpa [et] using hbd (ξ / ε)

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_translate_integral_congruent_one_mod_prime : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ γ : GL (Fin 2) F, InG p δ γ → Small ι (p : ℝ)⁻¹ (sl0 (p - 1) (toInf γ) (th G oneL) - 1) := by
  first | exact @GlobalTheory.HilbertThetaSeries.theta_translates_integral_one | exact GlobalTheory.HilbertThetaSeries.theta_translates_integral_one | (intros; apply GlobalTheory.HilbertThetaSeries.theta_translates_integral_one <;> assumption)
end

section -- restored from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsSeedThetaLatticeFixedPointFree
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem seed_exists : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∃ θ : Hn F → ℂ, Seed ι δ θ := by
  intro F _ _ _ p hp ι hp2 δ hδ
  obtain ⟨G, S, t, hL⟩ := GlobalTheory.T.exists_evenPositiveDefinite_intMatrix_det_sq p hp.out hp2
  have hsupp : ∀ x : (Fin (p - 1) ⊕ Fin (p - 1)) → F, (oneL x : ℂ) ≠ 0 → x ∈ aL (Fin (p - 1) ⊕ Fin (p - 1)) (1 : F) := by
    intro x hx
    have hx' : x ∈ LL F (Fin (p - 1) ⊕ Fin (p - 1)) := by
      by_contra h
      exact hx (by simp [oneL, h])
    exact ⟨x, hx', by simp⟩
  have hbd : ∀ x : (Fin (p - 1) ⊕ Fin (p - 1)) → F, ‖(oneL x : ℂ)‖ ≤ 1 := by
    intro x
    unfold oneL
    split_ifs <;> simp
  obtain ⟨-, hhol, hgr, -⟩ := GlobalTheory.T.thetaSeries_holomorphic_qExpansion_of_bounded_coeff F _ G hL.pos (1 : F) oneL 1 hsupp hbd
  obtain ⟨N, hN, hlev⟩ := GlobalTheory.T.theta_slash_eighth_root_of_square_det F _ G hL.pos t hL.det (p - 1) hL.card
  exact ⟨th G oneL, hhol, hgr, fun γ hγ => GlobalTheory.T.theta_translate_integral_congruent_one_mod_prime F p ι hp2 δ hδ _ G S t hL γ hγ, N, hN, hlev⟩

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_seed_theta_lattice_fixedPointFree : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∃ θ : Hn F → ℂ, Seed ι δ θ := by
  first | exact @GlobalTheory.HilbertThetaSeries.seed_exists | exact GlobalTheory.HilbertThetaSeries.seed_exists | (intros; apply GlobalTheory.HilbertThetaSeries.seed_exists <;> assumption)
end

section -- restored from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsIsHolAdelicLiftOfEvenWeightSystem
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem lift_isHol : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), Even k →
    ∀ (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ), Sys k Ψ → ∃ φ : TR.Sm F 2, IsLift k Ψ φ.1 ∧ IsHol k (fun _ => 0) 1 φ := by
  intro F _ _ _ k hk Ψ hΨ
  obtain ⟨φ₀, hL, hR, hZ⟩ := GlobalTheory.T.exists_adelic_lift_of_hilbert_system F k hk Ψ hΨ
  obtain ⟨hsm, hlie⟩ := GlobalTheory.T.adelic_lift_mem_smooth_killed_by_lowering F k Ψ φ₀ hΨ.hol hL
  let φ : TR.Sm F 2 := ⟨φ₀, hsm⟩
  have hfix : ∀ u ∈ KLev F 2 1, TR.finRep F 2 u φ = φ := fun u hu =>
    Subtype.ext (funext fun g => hR u hu g)
  have hlev : IsOpen {u | TR.finRep F 2 u φ = φ} := by
    let H : Subgroup (GL (Fin 2) (Af F)) :=
      { carrier := {u | TR.finRep F 2 u φ = φ}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, Module.End.mul_apply, hb, ha]
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    exact Subgroup.isOpen_mono (H₁ := KLev F 2 1) (H₂ := H) hfix (isOpen_KLev (F := F) (n := 2) (M := 1) le_rfl)
  have hcen : ∀ (z : Ideles F) (g : GA F 2),
      φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = (((1 : HChar F).1 z : ℂˣ) : ℂ) * φ.1 g := by
    intro z g
    simp only [OneMemClass.coe_one, MonoidHom.one_apply, Units.val_one, one_mul]
    exact hZ z g
  have haut : TR.IsAutForm φ :=
    ⟨hL.1, hlev, GlobalTheory.T.adelic_lift_kFinite_of_isLift F k Ψ φ hL,
      UpperTheory.V.Af.Nf.zFin F k 1 IsOfFinOrder.one φ hcen (fun v => (hlie v).1) (fun v => (hlie v).2),
      GlobalTheory.T.adelic_lift_has_moderate_growth F k Ψ φ₀ hΨ.gr hL⟩
  refine ⟨φ, hL, haut, fun w u hu => hfix _ ((GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F).2.2.1 w u hu), hcen, fun v => (hlie v).1,
    fun v => (hlie v).2⟩

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isHol_adelic_lift_of_even_weight_system : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), Even k → ∀ (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ), Sys k Ψ → ∃ φ : TR.Sm F 2, IsLift k Ψ φ.1 ∧ IsHol k (fun _ => 0) 1 φ := by
  first | exact @GlobalTheory.HilbertThetaSeries.lift_isHol | exact GlobalTheory.HilbertThetaSeries.lift_isHol | (intros; apply GlobalTheory.HilbertThetaSeries.lift_isHol <;> assumption)
end

section -- restored from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HasQOfSmallSubOne
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem hasQ_of_small_sub_one {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {p : ℕ} [Fact p.Prime] (ι : Qbar p ≃+* ℂ)
    {r : ℝ} (hr : r < 1) {g : Hn F → ℂ} (hg : Small ι r (g - 1)) :
    ∃ a, HasQ g a ∧ ‖ι.symm (a 0) - 1‖ < 1 ∧ ‖ι.symm (a 1)‖ < 1 := by
  classical
  obtain ⟨b, hb, hs⟩ := hg
  have h1 := (hasQ_lin F _ _ b b 1 hb hb).2.2.2
  have h2 := (hasQ_lin F _ _ _ _ 1 hb h1).1
  have e : (g - 1 + fun _ : Hn F => (1 : ℂ)) = g := by funext z; simp
  rw [e] at h2
  refine ⟨_, h2, ?_, ?_⟩
  · simpa using (hs 0).trans_lt hr
  · simpa using (hs 1).trans_lt hr

theorem hilbertOne : UpperTheory.V.Published.HilbertOne := by
  intro F _ _ _ p _ hp2 ι
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨δ, hδ⟩ := (GlobalTheory.T.exists_different_generator_totallyPositive_translate F p hp).1
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_seed_theta_lattice_fixedPointFree F p ι hp2 δ hδ
  obtain ⟨Y, hY, hrep⟩ := GlobalTheory.T.gl2_adelic_double_coset_decomposition_totally_real F p hp δ hδ
  have hav : ∀ y : (Af F)ˣ, ∃ N : ℕ, y ∈ Y → ∀ M : ℕ, p ^ N ∣ M → ∃ f : Hn F → ℂ, Comp ι δ ((p - 1) * M) (aff y 0) f := by
    intro y
    by_cases hy : y ∈ Y
    · obtain ⟨N, hN⟩ := GlobalTheory.T.exists_orbit_average_of_seed_powers_weight F p ι hp2 δ hδ θ hθ y (hY y hy)
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose n hn using hav
  refine ⟨Y.sup n, fun k _ hk => ?_⟩
  obtain ⟨m, rfl⟩ := hk
  rw [mul_assoc]
  set k := (p - 1) * (p ^ Y.sup n * m) with hkdef
  have hf : ∀ y : (Af F)ˣ, ∃ f : Hn F → ℂ, y ∈ Y → Comp ι δ k (aff y 0) f := by
    intro y
    by_cases hy : y ∈ Y
    · obtain ⟨f, hf⟩ := hn y hy (p ^ Y.sup n * m) ((pow_dvd_pow p (Finset.le_sup hy)).mul_right m)
      exact ⟨f, fun _ => hf⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose f hf using hf
  obtain ⟨Ψ, hΨ, hval⟩ := GlobalTheory.T.form_system_of_finitely_many_stabilizer_forms F k Y (fun y => ((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ) • f y) hrep (fun y hy =>
    ⟨(HolKeep.main F k _ _ _ (hf y hy).hol (hf y hy).hol).2.1, (Growth.gr_closed F k _ _ _ (hf y hy).gr (hf y hy).gr).2.1,
      fun γ hγ => by rw [(slash_add_smul_pow F k 0 _ _ (f y) _).2.2.2.2.1, (hf y hy).inv γ hγ]⟩)
  have hev : Even k := (hp.even_sub_one hp2).mul_right _
  obtain ⟨φ, hl, hφ⟩ := GlobalTheory.T.exists_isHol_adelic_lift_of_even_weight_system F k hev Ψ hΨ
  have hlt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hone : ∀ y : (Af F)ˣ, ∃ a, HasQ ((((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0)) a ∧
      ‖ι.symm (a 0) - 1‖ < 1 ∧ ‖ι.symm (a 1)‖ < 1 := by
    intro y
    obtain ⟨γ, z, hγ, y', hy', u, hu, h1, h2⟩ := hval (aff y 0)
    exact hasQ_of_small_sub_one ι hlt
      (GlobalTheory.T.system_cusp_infinity_component_congr_one F p ι hp2 δ hδ k (dvd_mul_right _ _) Ψ hΨ y y' z (f y') (hY y' hy') (hf y' hy').one γ u hγ hu h1 h2)
  choose a ha h0 h1 using hone
  obtain ⟨c, hc, hc'⟩ := GlobalTheory.T.exists_adelic_fourier_expansion_of_lift F k Ψ φ.1 a hΨ hl ha
  refine ⟨φ, fun y => a y 0, c, hφ, hc, h0, fun 𝔪 h𝔪 => ?_⟩
  obtain ⟨y, hy⟩ := hc' 𝔪 h𝔪
  rw [hy]
  exact h1 y

end GlobalTheory.HilbertThetaSeries
end

section -- restored from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsHilbertModularFormCongrOne
namespace UpperTheory.V

theorem Published.exists_hilbertModularForm_congr_one : Published.HilbertOne := GlobalTheory.HilbertThetaSeries.hilbertOne

theorem Lit.oneUse : Lit.OneUse := Lit.oneUse_of Published.exists_hilbertModularForm_congr_one

end UpperTheory.V
end

section
namespace UpperTheory.V.Z.Bc
theorem seedIIs_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Ws.SeedIIAlt :=
  have hA := hH.toClassicalTheorems
  _root_.UpperTheory.V.Z.Bc.seedII_Z_alt ⟨hH, Published.hilbert_eisenstein_weight_one_holds, Lit.oneUse⟩
    (_root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutLP_of_printsH_upQuad_upSol_indCs hH (_root_.UpperTheory.V.Z.Bc.upQuadI_of_alt hA (quadLiftRealToComplex_of_base_change hH.bc)) (_root_.UpperTheory.V.Z.Bc.upSolI_of_alt hA (cyclicLiftRankTwo_of_cyclic_base_change hH.cyc)) indCs)
end UpperTheory.V.Z.Bc
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Sp4In
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Cu
theorem sp4In_alt (hC : GradeZeroInterpolatingElement.CohomologyHyp) (hF : Published.FerreroWashington) (s2 : _root_.UpperTheory.V.Ws.SeedIIAlt) (s4 : _root_.UpperTheory.V.Cu.SeedIVAlt) (hP : _root_.UpperTheory.V.Ws.PMExAlt) : _root_.UpperTheory.V.Aut.SymplecticFourImageDense :=
  _root_.UpperTheory.V.Cu.main4_alt hC hF hFit s2 s4 hP
end UpperTheory.V.Cu
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.Top
namespace UpperTheory.V.HV.DescentVanishingReductions
theorem sp4In0_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') :
    _root_.UpperTheory.V.Aut.SymplecticFourImageDense :=
  _root_.UpperTheory.V.Cu.sp4In_alt (adjoint_lift_of_prints hH).coh
    _root_.UpperTheory.V.FW.ferreroWashington
    (_root_.UpperTheory.V.Z.Bc.seedIIs_alt hH)
    (_root_.UpperTheory.V.Z.Win.Birth.fourth_initial_of_prints_h hH)
    (pmEx_of_printsH hH)
end UpperTheory.V.HV.DescentVanishingReductions
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PublishedHypothesesFromPatching
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVPatch
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.InertiaLeRangeOfUnramified
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.QuadraticCharacterUnramified
end GlobalTheory.QuadraticCharacterUnramified
theorem _root_.GlobalTheory.T.inertia_le_range_of_unramified_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω], Module.finrank F K = 2 → ∀ η : HChar F, IsQuadCharOf K η → ∀ (u : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A u → η.UnrAt u → Ine (F := F) A ≤ (res F Ω K).range := by
  intro N F Ω _ _ _ _ _ K _ _ _ _ _ _ h2 η hq u A hA hu
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  obtain ⟨art, ha⟩ := N.aut.art F Ω
  obtain ⟨δ, hδc, hL⟩ := ha.exists_isLAdicOf ι
    (isAlgPos_zero_of_orderDvd two_pos (GlobalTheory.QuadraticCharacterUnramified.orderDvd_two hq))
  obtain ⟨ε, hεc, -, hε, hεu⟩ := UpperTheory.exists_quadratic_sign_character F K Ω 2 h2
  have hE : ∀ v, η.UnrAt v → CharEig ι δ v (η.val v : ℂˣ) := fun v hv B hB =>
    ⟨(hL.unr_iff ha (Or.inr rfl) hB).2 hv, fun σ hσ => by
      rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) hv hB hσ, inv_inv,
        RingEquiv.apply_symm_apply]⟩
  have hS := Filter.eventually_cofinite.1 ((GlobalTheory.QuadraticCharacterUnramified.good (K := K) hq).and hεu)
  have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS
    (f := fun s => δ s) (f' := fun s => ε s) hδc hεc fun v hv _ B hB σ hσ => by
      obtain ⟨⟨w, hwv, hu', hval⟩, hεv⟩ := not_not.1 hv
      subst hwv
      have h1 := (hE _ hu' B hB).2 σ hσ
      have h3 := (UpperTheory.frobenius_sign_compatibility F K Ω 2 ι ε hε w hεv B hB).2 σ hσ
      have e : δ σ⁻¹ = ε σ⁻¹ := Units.ext (ι.injective (by rw [h1, h3, hval]))
      rwa [map_inv, map_inv, inv_inj] at e
  intro s hs
  have h1 : δ s = 1 := (hL.unr_iff ha (Or.inr rfl) hA).2 hu s hs
  have h3 : ε s = 1 := by
    have e : δ s = ε s := congrFun key s
    rw [← e, h1]
  exact (hε.1 s).1 h3
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcRegAlgPolarizedPair
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcRegAlgPolarizedPair
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.BcPolar
theorem bc_regAlg_polarizedPair_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [IsCMField K] [Algebra F K], Module.finrank F K = 2 → ∀ (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (χ : HChar F) (P : CuspSub K a), π.IsRegAlg → π.Polarized χ → IsBC π P → (CG.mk P).IsRegAlg ∧ ∃ χ' : HChar (maximalRealSubfield K), GlobalTheory.ContraPair.PolarizedPair P χ' := by
  intro hL F K _ _ _ _ _ _ _ h2 a ha π χ P hreg hpol hBC
  refine ⟨(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, ?_⟩
  · obtain ⟨m, hm, hnd, hz⟩ := hreg (InfinitePlace.mk (τ.comp (algebraMap F K)))
    rw [CG.HasInfChar.infChar_eq (π := CG.mk P) (hBC.inf τ m hm)]
    exact ⟨hnd, hz⟩
  · obtain ⟨χ', hs, hd⟩ := GlobalTheory.T.base_change_dual_compatible hL.aut.js.1 hL.aut.gk F K h2 a ha π χ P hpol hBC
    obtain ⟨k, hk⟩ := GlobalTheory.BcPolar.exists_sign_twist χ' hs a
    refine ⟨χ' * quadChar K ^ k, fun v => (hk v).trans (zpow_natCast _ _), ?_⟩
    rwa [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
end GlobalTheory.BcPolar
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcRegAlgPolarizedPairStatement
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_algebraic_and_polarized_of_quadratic_base_change : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [IsCMField K] [Algebra F K], Module.finrank F K = 2 → ∀ (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (χ : HChar F) (P : CuspSub K a), π.IsRegAlg → π.Polarized χ → IsBC π P → (CG.mk P).IsRegAlg ∧ ∃ χ' : HChar (maximalRealSubfield K), GlobalTheory.ContraPair.PolarizedPair P χ' := by
  first | exact @_root_.GlobalTheory.BcPolar.bc_regAlg_polarizedPair_alt | exact _root_.GlobalTheory.BcPolar.bc_regAlg_polarizedPair_alt | (intros; apply _root_.GlobalTheory.BcPolar.bc_regAlg_polarizedPair_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsoComm
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsoComm
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LocCompCLit
open Matrix
section
variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
private theorem iso_comm (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (T : Module.End ℂ V)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) {x : V}
    (hx : x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) :
    T x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 := by
  refine Submodule.mem_comap.1 ((iSup_le (fun f => ?_) : _ ≤ Submodule.comap T _) hx)
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by simp only [LinearMap.comp_apply, f.2, hT]⟩ ⟨v, rfl⟩
private theorem iso_act (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (g : G) {x : V}
    (hx : x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) :
    ρ g x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 := by
  refine Submodule.mem_comap.1 ((iSup_le (fun f => ?_) : _ ≤ Submodule.comap (ρ g) _) hx)
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem f ⟨σ g v, f.2 g v⟩
end
theorem main_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → LocCompC := by
  intro H E _ _ _ a π w
  refine ⟨(LocEx.exists_isLocComp H.aut.fin E a π w).imp fun _ h => h.1, fun σ hσ => ?_⟩
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne_bot, ?_⟩
  obtain ⟨f, h0, hf⟩ := hσ
  change ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 = ⊤
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  have hop : ∀ (o : Op E a) (x : π.V),
      x ∈ (⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1) →
      π.op o x ∈ ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 := by
    intro o x hx
    cases o with
    | fin k =>
      have h1 := iso_act σ.ρ (π.locRep w) (GeneralLinearGroup.map (pLoc E w) k) (iso_comm σ.ρ (π.locRep w)
        (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k)) (fun g' y => by
        simp only [CuspSub.locRep, MonoidHom.comp_apply]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
          LocUniq.comm_locGL w (LocEx.map_pLoc_inv_mul w k)]) hx)
      have e : π.locRep w (GeneralLinearGroup.map (pLoc E w) k)
          (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k) x) = π.op (.fin k) x := by
        rw [CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
        rfl
      rwa [e] at h1
    | cpt k =>
      refine iso_comm _ _ _ (fun g y => Subtype.ext ?_) hx
      change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
        (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
      rw [← map_mul, ← map_mul, infGL_comm]
    | lie X =>
      refine iso_comm _ _ _ (fun g y => Subtype.ext ?_) hx
      exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1
  rcases π.irred (Submodule.map π.V.subtype _) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩) with h1 | h1
  · have h2 := hi (h1.trans (Submodule.map_bot _).symm)
    exact absurd (LinearMap.range_eq_bot.1 (le_bot_iff.1 (h2 ▸ le_iSup
      (fun f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)} => LinearMap.range f.1) ⟨f, hf⟩))) h0
  · exact hi (h1.trans (Submodule.map_subtype_top _).symm)
end GlobalTheory.LocCompCLit
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsoCommStatement
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_global_compatibility_complex_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → LocCompC := by
  first | exact @_root_.GlobalTheory.LocCompCLit.main_alt | exact _root_.GlobalTheory.LocCompCLit.main_alt | (intros; apply _root_.GlobalTheory.LocCompCLit.main_alt <;> assumption)
end
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Af.Bc GlobalTheory.RealGal UpperTheory.V.Af.ExLib
namespace UpperTheory.Gal.SV
theorem attRes_alt : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (P : CuspSub K a), IsBC π P → ∀ (r : G K Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (K →+* Qbar l) → Multiset ℤ), UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) P ι r wt HT → AttRes π ι K r := by
  intro L F Ω _ _ _ _ _ _ K _ _ _ _ _ _ _ l _ ι a ha π P hBC r wt HT H
  have hloc := _root_.GlobalTheory.T.local_global_compatibility_complex_alt L
  have hsl := GlobalTheory.T.satakeParameters_local
  refine (hBC.unr.and (eventually_not_mem K l)).mono ?_
  rintro w ⟨hu, hw⟩ f hf
  obtain ⟨B, hB, hBw⟩ := hu (w.under (𝓞 F)) rfl f hf
  refine ⟨B, hB, ?_⟩
  obtain ⟨⟨σ, hσ⟩, hi⟩ := hloc K a P w
  have hS := ((hsl K a w σ).2 _ P.finPart (hi σ hσ) _).1 hBw
  have h1 := frob_of (ι := ι) (r := r) hw σ hS fun A h rc hrc => by
    have g := gdOf K Ω A w h rc hrc a σ ((plainOf K a ha P w).2 ⟨_, hBw⟩ σ hσ)
    rw [← (H.away w hw A h rc hrc σ hσ).tor g.1 g.2]
    exact isWDOf_wdOf (h := h) hw ι (Units.continuous_val.comp H.cont)
  rwa [hf, GlobalTheory.RealGal.AttResProof.algSat_pow] at h1
section Descent
variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ}
theorem local_condition_at_place_of_decomposition_le_range (L : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (ha : 1 ≤ a) {K : Type} [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure K Ω] {ι : Qbar l ≃+* ℂ} {π : TR.CuspSub F a} {P : CuspSub K a} (hBC : IsBC π P)
    {r : G F Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (K →+* Qbar l) → Multiset ℤ}
    (hG : UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) P ι (r.comp (res F Ω K)) wt HT) {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A v) (hdec : Dec (F := F) A ≤ (res F Ω K).range) {HTF : (F →+* Qbar l) → Multiset ℤ}
    (hHT : ∀ τ : K →+* Qbar l, HT τ = HTF (τ.comp (algebraMap F K))) : At π ι r HTF h := by
  obtain ⟨w, h', i, hi⟩ := GlobalTheory.T.exists_place_completion_iso F Ω K v A h hdec
  have hlw : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ((l : ℕ) : 𝓞 K) ∉ w.asIdeal := fun hl hw => by
    apply hl
    have e1 := (h ((l : ℕ) : 𝓞 F))
    have e2 := (h' ((l : ℕ) : 𝓞 K))
    simp only [map_natCast] at e1 e2
    exact e1.1 (e2.2 hw)
  have ST := splitTr F K a ha π P hBC v w i ⟨hi.cont, hi.loc⟩
  obtain ⟨⟨σ', hσ'⟩, -⟩ := _root_.GlobalTheory.T.local_global_compatibility_complex_alt L K a P w
  obtain ⟨rc', hrc'⟩ := recTExists K Ω A w h'
  obtain ⟨S, hS, -⟩ := GlobalTheory.T.place_over_transport_ring_iso_symm F Ω A v h K Ω A w h' _ _ i hi
  have inj : ∀ {x y : WD h} {x' y' : WD h'}, WDRel (RingEquiv.refl Ω) x x' → WDRel (RingEquiv.refl Ω) y y' → x' = y' → x = y :=
    fun hx hy e => S.injective (by rw [(hS _ _).1 hx, (hS _ _).1 hy, e])
  have up : ∀ σ, π.IsLocComp v σ → GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) → Gd (rc' (algNorm σ')) := fun σ hσ hp => by
    obtain ⟨e, he⟩ := hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'
    have hplain : GlobalTheory.RoadU.PlainTor (IrrGL.of σ'.ρ σ'.smooth σ'.irred) := by
      have hi' := GlobalTheory.LocalFieldIso.continuous_symm i hi.cont
      obtain ⟨s, hS, h1, hU⟩ := hp
      have hρ := hS.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
      have hg (g : GL (Fin a) (w.adicCompletion K)) :
          Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) = g :=
        Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)
      let φ : Representation.Equiv
          (σ.ρ.comp (Matrix.GeneralLinearGroup.map (n := Fin a) i.symm.toRingHom)) σ'.ρ :=
        GlobalTheory.LocGL.equivOfBijective ⟨e.toLinearMap, fun g => LinearMap.ext fun x => by
          change e (σ.ρ (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) x) = σ'.ρ g (e x)
          rw [he, hg]⟩ e.bijective
      have hS' := (GlobalTheory.SuppIne.hasSupport_comp i hi.cont hi' hρ).of_equiv φ
      refine ⟨s.map (GlobalTheory.SuppIne.trGL i hi'), hS'.of_equiv (IrrGL.equivOf σ'.ρ σ'.smooth σ'.irred), ?_, ?_⟩
      · intro y hy
        obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
        exact h1 z hz
      · intro y hy z hz heq
        obtain ⟨y₀, hy₀, rfl⟩ := Multiset.mem_map.1 hy
        obtain ⟨z₀, hz₀, rfl⟩ := Multiset.mem_map.1 hz
        obtain ⟨χ, hχ, rfl⟩ := GlobalTheory.RoadU.PlainChars.exists_eq_ofChar y₀ (h1 y₀ hy₀)
        obtain ⟨ψ, hψ, rfl⟩ := GlobalTheory.RoadU.PlainChars.exists_eq_ofChar z₀ (h1 z₀ hz₀)
        have smooth_comp {θ : (v.adicCompletion F)ˣ →* ℂˣ} (hθ : GlobalTheory.SmGL.IsSmoothChar θ) :
            GlobalTheory.SmGL.IsSmoothChar (θ.comp (Units.map i.symm.toRingHom.toMonoidHom)) :=
          IsOpen.preimage (f := Units.map i.symm.toRingHom.toMonoidHom) (Continuous.units_map _ hi') hθ
        rw [GlobalTheory.DegOneChar.trGL_ofChar i hi' χ hχ (smooth_comp hχ),
          GlobalTheory.DegOneChar.trGL_ofChar i hi' ψ hψ (smooth_comp hψ), IrrGL.nu, IrrGL.tw_ofChar,
          IrrGL.ofChar_inj] at heq
        refine hU _ hy₀ _ hz₀ ?_
        rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]
        refine MonoidHom.ext fun t => ?_
        have h4 := DFunLike.congr_fun heq (Units.map i.toRingHom.toMonoidHom t)
        have h5 : Units.map i.symm.toRingHom.toMonoidHom (Units.map i.toRingHom.toMonoidHom t) = t :=
          Units.ext (i.symm_apply_apply _)
        rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, h5,
          GlobalTheory.LocalFieldIso.absPow_map i hi.cont] at h4
        exact h4
    exact gdOf K Ω A w h' rc' hrc' a σ' hplain
  have br : ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), Induces Bw →
      ∃ (Bw' : LocBridge l K Ω (Dec (F := K) A) O) (_ : Induces Bw'), Bw'.Kw = Bw.Kw ∧ Bw'.j = Bw.j ∧ Bw'.LL = Bw.LL :=
    fun O _ _ _ Bw hj => by
      obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge F K Ω l A O Bw (GlobalTheory.T.local_field_embedding_mem F Ω K l A O Bw hdec)
      exact ⟨Bw', fun x => by rw [e2]; exact hj x, e1, e2, e3⟩
  refine ⟨fun B hB => ST.1.2 ((plainOf K a ha P w).2 (ST.2 ⟨B, hB⟩)), fun σ hσ hp rc hrc => ?_, fun σ hσ hp O _ _ _ Bw hj => ?_,
    fun hl hp => ?_, fun O _ _ _ Bw hj σ hσ hs => ?_⟩
  · obtain ⟨e, he⟩ := hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'
    have hy := recTr L.aut.art hi σ σ' e he hrc hrc' hp
    have g := up σ hσ hp
    refine ⟨fun hl => ?_, fun O _ _ _ Bw hj _ => ?_⟩
    · obtain ⟨x, hx, hxx⟩ := GlobalTheory.T.galois_rep_restriction_local_completion F Ω K l ι a r A v w h h' i hi _
        (isWDOf_wdOf (h := h') (hlw hl) ι (Units.continuous_val.comp hG.cont))
      exact ⟨x, hx, fun _ => inj hxx hy ((hG.away w (hlw hl) A h' rc' hrc' σ' hσ').tor g.1 g.2)⟩
    · obtain ⟨Bw', hj', e1, e2, e3⟩ := br O Bw hj
      obtain ⟨-, a2, -, a4⟩ := (hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').nice σ' hσ' rc' hrc' (Or.inr g.1) g.2
      have hpst := (GlobalTheory.T.local_embedding_compatible_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r).2.2.2.1 a2
      exact ⟨hpst, inj (GlobalTheory.T.local_embedding_restrict_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r hpst ι v w h h' hj hj' i hi) hy (a4.tor g.1 g.2)⟩
  · have g := up σ hσ hp
    obtain ⟨Bw', hj', e1, e2, e3⟩ := br O Bw hj
    obtain ⟨a1, -, a3, -⟩ := (hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').nice σ' hσ' rc' hrc' (Or.inr g.1) g.2
    have D := GlobalTheory.T.local_embedding_compatible_extension F Ω K l (Loc.PP l) A O Bw Bw' e1 e2 e3 a r
    refine ⟨D.1 a1, fun τ LL' τ' hτ => ?_⟩
    obtain ⟨τK, τ'', hτK, hind⟩ := GlobalTheory.T.local_embedding_agree F Ω K l A O Bw Bw' e1 e2 τ LL' τ' hτ
    have hJ := D.2.2.2.2 τK (HT τK) (a3 τK LL' τ'' hind)
    rw [hHT τK, hτK] at hJ
    exact hJ
  · have hp' := ST.1.1 hp
    have g := gdOf K Ω A w h' rc' hrc' a σ' (hp' σ' hσ')
    obtain ⟨t, ht⟩ := winPt UpperTheory.V.Z.Gam.suppFacts UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winOf K a ha P
    obtain ⟨x, hx, hxx⟩ := GlobalTheory.T.galois_rep_restriction_local_completion F Ω K l ι a r A v w h h' i hi _
      (isWDOf_wdOf (h := h') (hlw hl) ι (Units.continuous_val.comp hG.cont))
    rw [hx.wdOf_eq hl]
    refine UpperTheory.GalN.V.RatioW.descend hi hxx ?_
    rw [(hG.away w (hlw hl) A h' rc' hrc' σ' hσ').tor g.1 g.2]
    exact ratioT K Ω A w h' rc' hrc' a P t (ht w hp') σ' hσ'
  · obtain ⟨e, he⟩ := hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'
    obtain ⟨Bw', hj', e1, e2, e3⟩ := br O Bw hj
    exact (GlobalTheory.T.local_embedding_compatible_extension F Ω K l _ A O Bw Bw' e1 e2 e3 a r).2.2.1
      ((hG.above _ _ (Loc.tiedP l) w A h' O Bw' hj').crys σ' hσ' ((GlobalTheory.T.aux_statement_23 F K v w i hi.cont a σ σ' e he).2 hs)).1
end Descent
theorem galois_rep_exists_totally_real_rank_two_of_base_change : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → UpperTheory.V.Z.Bc.QuadBC2 → AdmissibleReal → GaloisRepExistsTotallyRealGL2 := by
  intro litN qbc adm F Ω _ _ _ _ _ _ l _ ι a ha2 ha π χ hreg hpol
  let S : Set (QCM F Ω) := {Q | ∃ P : CuspSub ↥Q.K a, IsBC π P}
  have good : ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v →
      {Q : QCM F Ω | Dec (F := F) A ≤ (res F Ω ↥Q.K).range ∧ ∃ P : CuspSub ↥Q.K a, IsBC π P}.Infinite := by
    intro v A hA
    obtain rfl := ha2.out
    have hT := GlobalTheory.T.eventually_has_satake_parameters adm F 2 π
    refine (GlobalTheory.T.infinite_quadratic_fields_split_inertia F Ω (fun u => ∃ B, π.HasSat u B) hT v A hA).mono ?_
    rintro Q ⟨hdec, u, A', ⟨B, hB⟩, hA', hine⟩
    refine ⟨hdec, ?_⟩
    rcases qbc F Q.K Q.two π hreg with ⟨η, hq, htw⟩ | hP
    · exact absurd (_root_.GlobalTheory.T.inertia_le_range_of_unramified_alt litN F Ω Q.K Q.two η hq u A' hA' (unrAt_of_isoTwist adm F 2 ha π η htw u B hB)) hine
    · exact hP
  obtain ⟨v0⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩⟩
  obtain ⟨A0, hA0⟩ := ReciprocityTheory.Gal.exists_isPlaceOver (F := F) Ω v0
  have hS : S.Infinite := by
    refine (good v0 A0 hA0).mono ?_
    intro Q hQ
    exact hQ.2
  have key : ∀ Q : ↥S, ∃ (P : CuspSub ↥Q.1.K a)
      (r : G ↥Q.1.K Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (↥Q.1.K →+* Qbar l) → Multiset ℤ),
      IsBC π P ∧ UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) P ι r wt HT := by
    rintro ⟨Q, P, hP⟩
    obtain ⟨hregP, χ', hχ'⟩ := _root_.GlobalTheory.T.regular_algebraic_and_polarized_of_quadratic_base_change litN F ↥Q.K Q.two a ha π χ P hreg hpol hP
    obtain ⟨r, wt, HT, hr⟩ := _root_.UpperTheory.Gal.SV.rowOf' litN.aut.gal ↥Q.K Ω l ι a ha P χ' hregP hχ'
    exact ⟨P, r, wt, HT, hP, hr⟩
  choose P r wt HT hP hr using key
  have hatt : ∀ Q, Continuous (r Q) ∧ IsSSRep (r Q) ∧ AttRes π ι ↥Q.1.K (r Q) := fun Q =>
    ⟨(hr Q).cont, (hr Q).ss,
      _root_.UpperTheory.Gal.SV.attRes_alt litN F Ω ↥Q.1.K l ι a ha π (P Q) (hP Q) (r Q) (wt Q) (HT Q) (hr Q)⟩
  obtain ⟨ρ, hρc, hρs, hev⟩ := GlobalTheory.T.galois_rep_patching_infinite_family F Ω l ι a π S hS r hatt
  obtain ⟨HTF, hcard, hwts, hbc⟩ := hodgeTate F Ω l ι a π hreg
  have hgal : ∀ᶠ Q : ↥S in Filter.cofinite,
      UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) (P Q) ι (ρ.comp (res F Ω ↥Q.1.K)) (wt Q) (HT Q) :=
    hev.mono fun Q hQ => props_iso (hr Q) hQ.1 hQ.2
  have hHT : ∀ Q : ↥S, (∀ τ : ↥Q.1.K →+* Qbar l, HT Q τ = HTF (τ.comp (algebraMap F ↥Q.1.K))) ∧
      ∀ τ : F →+* Qbar l, HTF τ = (HTF τ).map (wt Q - ·) :=
    fun Q => hbc ↥Q.1.K Q.1.two (P Q) (hP Q) (r Q) (wt Q) (HT Q) (hr Q)
  obtain ⟨Q0⟩ : Nonempty ↥S := hS.nonempty.to_subtype
  let τ0 : F →+* Qbar l := ι.symm.toRingHom.comp (Classical.arbitrary (InfinitePlace F)).embedding
  have hwt : ∀ Q : ↥S, wt Q = wt Q0 := fun Q =>
    GlobalTheory.T.eq_of_multiset_symmetric_reflections (HTF τ0) (wt Q) (wt Q0) (by rw [← Multiset.card_pos, hcard]; exact ha) ((hHT Q).2 τ0) ((hHT Q0).2 τ0)
  have hpick : ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v →
      ∃ Q : ↥S, Dec (F := F) A ≤ (res F Ω ↥Q.1.K).range ∧
        UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) (P Q) ι (ρ.comp (res F Ω ↥Q.1.K)) (wt Q) (HT Q) := by
    intro v A hA
    have hfin := (Filter.eventually_cofinite.1 hgal).image Subtype.val
    obtain ⟨Q, hQ, hQn⟩ := ((good v A hA).sdiff hfin).nonempty
    refine ⟨⟨Q, hQ.2⟩, hQ.1, ?_⟩
    by_contra hc
    exact hQn ⟨⟨Q, hQ.2⟩, hc, rfl⟩
  have hD : ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A v), At π ι ρ HTF h := fun v A h => by
    obtain ⟨Q, hdec, hQ⟩ := hpick v A h
    exact _root_.UpperTheory.Gal.SV.local_condition_at_place_of_decomposition_le_range litN ha (hP Q) hQ h hdec (hHT Q).1
  have hpl : ∀ w B, π.HasSat w B → PlainAtR π w := fun w B hB => by
    obtain ⟨A, h⟩ := ReciprocityTheory.Gal.exists_isPlaceOver (F := F) Ω w
    exact (hD w A h).plain B hB
  refine ⟨ρ, wt Q0, HTF, hρc, hρs, hpl, fun w σ hσ hp => ⟨fun A h => (hD w A h).cmp σ hσ hp, fun A h => (hD w A h).ht σ hσ hp⟩,
    fun w hw B hB => ?_, fun w hw A h => (hD w A h).ratio hw, hwts, (hHT Q0).2, fun w A h => (hD w A h).crys⟩
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := GlobalTheory.T.local_global_compatibility_real adm F a π w
  have hS := ((GlobalTheory.T.satakeParameters_local F a w σ).2 _ π.finPart (hiso σ hσ) B).1 hB
  exact frob_of hw σ hS fun A h rc hrc => (((hD w A h).cmp σ hσ (hpl w B hB σ hσ) rc hrc).1 hw).isWDOf
    (gdOf F Ω A w h rc hrc a σ (hpl w B hB σ hσ))
end UpperTheory.Gal.SV
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPCohC
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
theorem UpperTheory.V.Af.clozelCohC_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → UpperTheory.V.Published.ClozelCohC := by
  intro lit E _ _ _ a ha π Ξ h
  choose m h1 h2 using h
  have hd : ∀ τ, GlobalTheory.WignerGL.HasDualInfChar Ξ τ (m τ) := fun τ => (dualIff E a Ξ τ _).1 (h2 τ)
  have hreg : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    obtain ⟨m', e1, e2, e3⟩ := GlobalTheory.AlgInfChar.exists_dualInfChar E a Ξ τ
    have e : m τ = m' := msetSep _ _ fun u => by
      haveI : Nonempty (Fin Ξ.d) := ⟨⟨0, Ξ.pos⟩⟩
      exact smul_left_injective ℂ one_ne_zero (((hd τ).2 u).symm.trans (e1.2 u))
    have h3 : (CG.mk π).HasInfChar τ (m τ) := h1 τ
    rw [h3.infChar_eq, e]
    exact ⟨e2, e3⟩
  obtain ⟨Ξ', hΞ'⟩ := lit.aut.coh E a ha π hreg
  choose m' g1 g2 g3 using GlobalTheory.AlgInfChar.exists_dualInfChar E a Ξ'
  have e : m = m' := by
    by_contra hne
    exact wigner E a π Ξ' m m' h1 g1 hne hΞ'
  subst e
  obtain ⟨T, hT⟩ := algIso E a Ξ' Ξ (fun τ => (m τ).map Neg.neg) (fun τ => (dualIff E a Ξ' τ _).2 (g1 τ)) h2
  exact cohTransport E a π Ξ' Ξ T hT hΞ'
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.GaloisCohomology UpperTheory.Top
namespace UpperTheory.V.HV.DescentVanishingReductions
open UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Lit UpperTheory.V.Z.Bc
theorem published_hypotheses_from_patching_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (desc : Z.Desc.DescWeak) : _root_.UpperTheory.V.Af.HypothesesH' :=
  { litN := hN, cohC := _root_.UpperTheory.V.Af.clozelCohC_alt hN, conjC := Z.Coh.clozelConjC, borelC := Z.Coh.borelInjC,
    galR := _root_.UpperTheory.Gal.SV.galois_rep_exists_totally_real_rank_two_of_base_change hN UpperTheory.ConvolutionTheory.R2.quadBC2 admissibleReal, smoR := strongMultOneReal,
    gkR := gelfandKazhdanReal strongMultOneReal, admR := admissibleReal, bc := Br.quadBC0_of_two UpperTheory.ConvolutionTheory.R2.quadBC2,
    newform := newformRepOf cuspSemisimpleReal admissibleReal,
    descU := desc, cyc := cycC_holds, cyc2 := Or.inl UpperTheory.ConvolutionTheory.RankTwoDescent.descS, quat := defQuatExists, ssR := cuspSemisimpleReal }
end UpperTheory.V.HV.DescentVanishingReductions
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KFinal
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LemmaKOfLitN
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.GaloisCohomology
namespace UpperTheory.V.ZK
theorem lemmaK_of_litN_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hB : BOdd) : ∃ CK, LemmaK CK :=
  lemmaK hB (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.lfK hN.coh.ltK
end UpperTheory.V.ZK
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.ZK
theorem lemmaK_litN_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : ∃ CK, LemmaK CK := _root_.UpperTheory.V.ZK.lemmaK_of_litN_alt hN bOdd
end UpperTheory.V.ZK
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.Top
namespace UpperTheory.V.HV.DescentVanishingReductions
theorem vwin_of_hypotheses_H_E_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') : VWin :=
  have hK := _root_.UpperTheory.V.ZK.lemmaK_litN_alt hH.litN
  have hE := _root_.UpperTheory.V.Z.Win.Dn.ends0_alt hH
  have h4 := _root_.UpperTheory.V.HV.DescentVanishingReductions.countII_and_countIII_of_printsH_of_sp4In hH hK (_root_.UpperTheory.V.HV.DescentVanishingReductions.sp4In0_alt hH)
  _root_.UpperTheory.V.HV.Core.of_four_alt hH.litN hK (_root_.UpperTheory.V.Z.J.count_i_of_printed_bound_k_kato_automorphy hH hK (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.katoTwoW_of_printsH hH) (_root_.UpperTheory.V.HV.Core0.automorphyUnramified_of_litN_of_gdEnd hH.litN hE.1)) h4.1 h4.2 (_root_.UpperTheory.V.Z.J.count_v_of_printed_bound_k_reduced_unitary_lift hH hK hE.2)
theorem v_window_of_automorphy_csd_ss_mono_odd (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : VWin :=
  _root_.UpperTheory.V.HV.DescentVanishingReductions.vwin_of_hypotheses_H_E_alt (_root_.UpperTheory.V.HV.DescentVanishingReductions.published_hypotheses_from_patching_alt hN UpperTheory.V.Z.Tf.SR.descWeak)
end UpperTheory.V.HV.DescentVanishingReductions
theorem UpperTheory.V.v_window_of_literal_automorphy_n (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : VWin :=
  _root_.UpperTheory.V.HV.DescentVanishingReductions.v_window_of_automorphy_csd_ss_mono_odd hN
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.One.Join.local_inputs_from_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenImageCondition) :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt :=
  { bz := (_root_.UpperTheory.LiteratureTheorems.bernstein_zelevinsky_finiteness_of_open O)
    bern := (_root_.UpperTheory.LiteratureTheorems.bernstein_unitary_product_irreducible_of_open O)
    geo := (_root_.UpperTheory.LiteratureTheorems.bernstein_zelevinsky_geometric_of_open O)
    zel := (_root_.UpperTheory.LiteratureTheorems.zelevinsky_polynomial_ring_of_open O)
    disj := (_root_.UpperTheory.LiteratureTheorems.totally_disjoint_product_irreducible_of_open O)
    mp := (_root_.UpperTheory.LiteratureTheorems.moy_prasad_jacquet_iso_of_open O)
    temp := (_root_.UpperTheory.LiteratureTheorems.tempered_product_of_square_integrable_of_open O)
    seg := (_root_.UpperTheory.LiteratureTheorems.ess_square_integrable_segments_of_open O)
    sq := (_root_.UpperTheory.LiteratureTheorems.square_integrable_segment_of_open O)
    gen := (_root_.UpperTheory.LiteratureTheorems.generic_unlinked_gl_of_open O)
    multi := (_root_.UpperTheory.LiteratureTheorems.langlands_multisegments_of_open O)
    exh := (_root_.UpperTheory.LiteratureTheorems.langlands_exhaustion_gl_of_open O)
    cos := (_root_.UpperTheory.LiteratureTheorems.standard_cosocle_gl_of_open O)
    conv := (_root_.UpperTheory.LiteratureTheorems.local_converse_gl_of_open O)
    dzi := (_root_.UpperTheory.LiteratureTheorems.depth_zero_induction_of_open O)
    brauer := (_root_.UpperTheory.LiteratureTheorems.brauer_degree_zero_of_open O)
    chev := (_root_.UpperTheory.LiteratureTheorems.chevalley_units_of_open O)
    green := (_root_.UpperTheory.LiteratureTheorems.green_regular_characters_of_open O) }
theorem UpperTheory.One.Join.automorphic_inputs_from_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenImageCondition) (bc : _root_.PositivityTheory.Rg.BcN.BaseChangeIsobaricN)
    (gal : _root_.UpperTheory.V.Z.Win.RowT) : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureAutomorphyHypothesis :=
  { decay := (_root_.UpperTheory.LiteratureTheorems.cusp_rapid_decay_of_open O)
    hc := (_root_.UpperTheory.LiteratureTheorems.harish_chandra_finite_of_open O)
    fin := (_root_.UpperTheory.LiteratureTheorems.automorphic_forms_finite_gl_of_open O)
    js := (_root_.UpperTheory.LiteratureTheorems.jacquet_shalika_of_open O)
    cusp := (_root_.UpperTheory.LiteratureTheorems.cuspidal_spectrum_gl_of_open O)
    bc := bc
    gk := (_root_.UpperTheory.LiteratureTheorems.gelfand_kazhdan_dual_of_open O)
    gal := gal
    pur := (_root_.UpperTheory.LiteratureTheorems.clozel_purity_of_open O)
    coh := (_root_.UpperTheory.LiteratureTheorems.clozel_cohomological_of_open O)
    art := (_root_.UpperTheory.LiteratureTheorems.global_artin_reciprocity_of_open O)
    ray := (_root_.UpperTheory.LiteratureTheorems.ray_class_field_st_of_open O)
    chA := (_root_.UpperTheory.LiteratureTheorems.hecke_ladic_character_above_of_open O)
    chW := (_root_.UpperTheory.LiteratureTheorems.algebraic_character_wd_of_open O)
    berger := (_root_.UpperTheory.LiteratureTheorems.de_rham_pot_semistable_of_open O) }
theorem UpperTheory.One.Join.v_window_of_depth_zero_residual_bc_cm (O : _root_.UpperTheory.LiteratureTheorems.OpenImageCondition)
 (bc : _root_.PositivityTheory.Rg.BcN.BaseChangeIsobaricN) (gal : _root_.UpperTheory.V.Z.Win.RowT) (cm : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureCMHypothesis) :
    UpperTheory.Top.VWin :=
  _root_.UpperTheory.V.v_window_of_literal_automorphy_n
    { loc := _root_.UpperTheory.One.Join.local_inputs_from_literature O
      aut := _root_.UpperTheory.One.Join.automorphic_inputs_from_literature O bc gal
      coh := _root_.UpperTheory.LiteratureTheorems.galois_cohomology_from_literature O
      cm := cm }
theorem UpperTheory.One.Join.cm_abelian_inputs_from_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenImageCondition) : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureCMHypothesis :=
  { gm := (_root_.UpperTheory.LiteratureTheorems.grothendieck_deformation_of_open O)
    dr := (_root_.UpperTheory.LiteratureTheorems.abelian_de_rham_of_open O)
    dual := ⟨_root_.UpperTheory.LiteratureTheorems.dual_abelian_scheme_of_open O,
      FubiniStudyChowHeightFormula₂.Adr.crystallineDeRham⟩
    per := (GlobalTheory.PeriodFamily.periodComparison_holds)
    gmp := (GlobalTheory.GaussManinTop.main)
    st := (UpperTheory.Lit.serreTateGoodReduction)
    cm := (_root_.UpperTheory.LiteratureTheorems.elliptic_main_theorem_cm_of_open O)
    hj := (_root_.UpperTheory.LiteratureTheorems.hilbert_class_field_j_of_open O)
    dri := (_root_.UpperTheory.LiteratureTheorems.siegel_klingen_deligne_ribet_of_open O)
    pz := (_root_.UpperTheory.LiteratureTheorems.partial_zeta_functional_equation_of_open O)
    fe := (_root_.UpperTheory.LiteratureTheorems.hecke_tate_functional_equation_of_open O) }
theorem UpperTheory.One.Join.automorphic_window_of_inputs (O : _root_.UpperTheory.LiteratureTheorems.OpenImageCondition)
 (bc : _root_.PositivityTheory.Rg.BcN.BaseChangeIsobaricN) (gal : _root_.UpperTheory.V.Z.Win.RowT) :
    UpperTheory.Top.VWin :=
  _root_.UpperTheory.One.Join.v_window_of_depth_zero_residual_bc_cm O bc gal (_root_.UpperTheory.One.Join.cm_abelian_inputs_from_literature O)
end

module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNsmulPaddedLatticeMemBasisProduct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCoefficientChangeCompareIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanSquareOrthoProductThetaEqProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TypeChangeInjectiveCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorRootSubOneLengthLeTameValue

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsUnitReprOne
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction
open scoped ENNReal nonZeroDivisors

namespace GlobalTheory.SelBaseChange

section Coord

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']

end Coord

section Coh

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R' M'] [Module R M'] [IsScalarTower R R' M']
  (ρ : Representation R G M) (ρ' : Representation R' G M') (u : M' →ₗ[R] M) (hu : Continuous u)
  (he : ∀ g m, u (ρ' g m) = ρ g (u m))

def cZ : Z1 ρ' →ₗ[R] Z1 ρ where
  toFun f := ⟨u ∘ f.1, hu.comp f.2.1, fun g h => by
    simp only [Function.comp_apply, f.2.2 g h, map_add (f := _), he]⟩
  map_add' f f' := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' r f := Subtype.ext (funext fun g => map_smul u _ _)

def cH : H1 ρ' →ₗ[R] H1 ρ :=
  Submodule.mapQ (((B1 ρ').comap (Z1 ρ').subtype).restrictScalars R) _ (cZ ρ ρ' u hu he)
    (fun f hf => by
      obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ' _).1 hf
      refine (mem_coboundaries1 _ _).2 ⟨u m, fun g => ?_⟩
      have e := hm g
      simp only [Submodule.coe_subtype] at e
      change u (f.1 g) = _
      rw [e, map_sub, he]) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R ((B1 ρ').comap (Z1 ρ').subtype)).symm.toLinearMap

theorem cH_mk (z : Z1 ρ') :
    cH ρ ρ' u hu he (Submodule.Quotient.mk z) = Submodule.Quotient.mk (cZ ρ ρ' u hu he z) := rfl

theorem res_cH {H : Type} [Group H] [TopologicalSpace H] (φ : H →* G) (hφ : Continuous φ)
    (x : H1 ρ') :
    resH1 ρ φ hφ (cH ρ ρ' u hu he x) =
      cH (ρ.comp φ) (ρ'.comp φ) u hu (fun _ _ => he _ _) (resH1 ρ' φ hφ x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem cH_mem_H1ur (J : Subgroup G) (x : H1 ρ') (hx : x ∈ H1ur ρ' J) :
    cH ρ ρ' u hu he x ∈ H1ur ρ J := by
  unfold H1ur at hx ⊢
  rw [LinearMap.mem_ker] at hx ⊢
  exact (res_cH ρ ρ' u hu he J.subtype continuous_subtype_val x).trans
    ((congrArg _ hx).trans (map_zero _))

theorem cH_mem_Sel {I : Type} {Dc : I → Type} [∀ v, Group (Dc v)] [∀ v, TopologicalSpace (Dc v)]
    (φ : ∀ v, Dc v →* G) (hφ : ∀ v, Continuous (φ v)) (L : LocCond ρ φ) (L' : LocCond ρ' φ)
    (h : ∀ v, ∀ x ∈ L' v, cH (ρ.comp (φ v)) (ρ'.comp (φ v)) u hu (fun _ _ => he _ _) x ∈ L v)
    (x : H1 ρ') (hx : x ∈ Sel ρ' φ hφ L') : cH ρ ρ' u hu he x ∈ Sel ρ φ hφ L := by
  rw [mem_Sel] at hx ⊢
  intro v
  rw [res_cH]
  exact h v _ (hx v)

theorem eq_zero_of_cH {ι : Type} (u : ι → (M' →ₗ[R] M)) (hu : ∀ i, Continuous (u i))
    (he : ∀ i g m, u i (ρ' g m) = ρ g (u i m))
    (hb : Function.Bijective fun (m : M') (i : ι) => u i m) (x : H1 ρ')
    (hx : ∀ i, cH ρ ρ' (u i) (hu i) (he i) x = 0) : x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [cH_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1] at hx ⊢
  choose m hm using hx
  obtain ⟨m', hm'⟩ := hb.2 m
  refine ⟨m', fun g => hb.1 (funext fun i => ?_)⟩
  have := hm i g
  rw [← congrFun hm' i] at this
  show u i _ = u i _
  rw [map_sub, he]
  exact this

end Coh

section Main

open Formalism.MainNotions.BlochKatoReduction.Gen

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (k k' : ℕ)

theorem trep_one_apply (g : Gen.GE N) (m : Fin D.R.r → KmodO (X.Ok i k)) (a : Fin D.R.r) :
    Trep i s k 1 g m a = ∑ j, phiK X i k (Tmat i s g a j) • m j := by
  simp [Trep, twRep, matAct, Tmat, Finset.smul_sum, smul_smul]

variable [Algebra (X.Ok i k) (X.Ok i k')] [IsScalarTower (X.O i) (X.Ok i k) (X.Ok i k')]

theorem phiK_eq (a : X.O0 i) :
    phiK X i k' a = algebraMap (X.Ok i k) (X.Ok i k') (phiK X i k a) :=
  IsScalarTower.algebraMap_apply (X.O i) (X.Ok i k) (X.Ok i k') _

variable (p : KmodO (X.Ok i k') →ₗ[X.Ok i k] KmodO (X.Ok i k))

theorem equivariant (g : Gen.GE N) (m : Fin D.R.r → KmodO (X.Ok i k')) :
    p.compLeft (Fin D.R.r) (Trep i s k' 1 g m) = Trep i s k 1 g (p.compLeft (Fin D.R.r) m) := by
  funext a
  show p (Trep i s k' 1 g m a) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [trep_one_apply, trep_one_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [phiK_eq i k k', algebraMap_smul, map_smul]
  rfl

end Main

end GlobalTheory.SelBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameCharEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedRhoConjLatTpsi
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceRankRPartEqTraceBaseChangeTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceRankRPartEqTraceBaseChangeTriple
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.TripleTrace

open GlobalTheory.BlockComplement

theorem continuous_twO (D : D7) (a : D.nd.Loc) : Continuous (D.ntw.twist₂ a) := by
  have hl := GlobalTheory.TwistedSelmerCompare.natCast_mem_maximalIdeal (l := D.nd.l a) (D.nd.O a)
  have hl0 : ((D.nd.l a : ℕ) : D.ntw.O0 (D.ntw.twOf a)) ≠ 0 := by
    intro h0
    have := congrArg ((iotaOQ D.nd D.naut a).comp (D.ntw.twist₂ a)) h0
    rw [map_natCast, map_zero] at this
    exact (D.nd.lPrime a).out.ne_zero (by exact_mod_cast this)
  have hp : ((IsLocalRing.maximalIdeal (D.nd.O a)).comap (D.ntw.twist₂ a)).IsPrime := Ideal.comap_isPrime _ _
  have hm : ((IsLocalRing.maximalIdeal (D.nd.O a)).comap (D.ntw.twist₂ a)).IsMaximal := hp.isMaximal fun h => by
    apply hl0
    rw [← Ideal.mem_bot, ← h, Ideal.mem_comap, map_natCast]
    exact hl
  have he := IsLocalRing.eq_maximalIdeal hm
  refine continuous_of_continuousAt_zero (D.ntw.twist₂ a) ?_
  rw [ContinuousAt, map_zero,
    (D.ntw.twistBaseCoefficientRing_isAdic _).hasBasis_nhds_zero.tendsto_iff (D.nd.O_adic a).hasBasis_nhds_zero]
  refine fun n _ => ⟨n, trivial, fun x hx => ?_⟩
  rw [← he] at hx
  exact Ideal.le_comap_pow _ n hx

theorem trace_of_block {K : Type} [Field K] {n a t : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (M' : Matrix (Fin a) (Fin a) K) (c : Fin t → K) (e : (Fin n → K) ≃ₗ[K] ((Fin a → K) × (Fin t → K)))
    (h : ∀ u, e (M.mulVec u) = (M'.mulVec (e u).1, fun j => c j * (e u).2 j)) :
    M.trace = M'.trace + ∑ j, c j := by
  have e1 : e.conj (Matrix.toLin' M) =
      LinearMap.prodMap (Matrix.toLin' M') (Matrix.toLin' (Matrix.diagonal c)) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨u, rfl⟩ := e.surjective x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, Matrix.toLin'_apply, h]
    refine Prod.ext rfl ?_
    funext j
    simp [Matrix.mulVec_diagonal]
  rw [← Matrix.trace_toLin'_eq, ← LinearMap.trace_conj' _ e, e1, LinearMap.trace_prodMap',
    Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, Matrix.trace_diagonal]

theorem trace_eq : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (a : D.nd.Loc) (π : D.nd.X a) (ρ : Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a)) (s : D.ntw.Sig (D.ntw.twOf a)) (Sg : List (Part D.naut.CG)), GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D a π ρ → HasParamX D.nd D.naut a π Sg → GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsTriple D a s Sg → ∀ g, ((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)).trace = D.ntw.twist₂ a ((D.ntw.rhoS _ s g : GL (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))).trace := by
  rintro hC D i π ρ s Sg ⟨hρ, r₀, ⟨-, -, hr3⟩, e, he⟩ ⟨P, hP, -, -, -, hB4, -⟩ ⟨-, -, -, hT⟩ g
  have hι := GlobalTheory.CoeffEmbedding.continuous_iotaOQ _ _ _ D.nd D.naut i
  have hinj : Function.Injective (iotaOQ D.nd D.naut i) :=
    (D.naut.iotaQ i).injective.comp (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)))
  apply hinj
  revert g
  rw [← funext_iff]
  refine AE.eq_of_continuous hC (hι.comp hρ.matrix_trace)
    (hι.comp ((continuous_twO D i).comp (D.ntw.rhoS_cont _ s).matrix_trace)) ?_
  filter_upwards [hT, ae_chiBar D.naut i, ae_epsBar D.naut i, eventually_out i,
    isoLoc_sum (A := D.naut) (twistIso D.nd D.naut (Sg ++ [muPart D.nd D.naut i]) D.naut.etaTinv),
    isoLoc_sum (A := D.naut) (twistIso D.nd D.naut Sg D.naut.etaTinv)]
    with w h1 h2 h3 h4 h5 h8 hw B σ hB hσ
  apply (D.naut.iotaQC i).injective
  have hq := normV_ne_zero w
  have h6 := D.naut.pt_loc i P π hP w (h4 hw)
  rw [← hr3 w (h4 hw) B σ hB hσ, ← hB4 w hw] at h6
  have h9 := map_trace_eq_sum _ _ _ h6
  have h10 := map_trace_eq_sum _ _ _ (h1 (h4 hw) B σ hB hσ)
  rw [D.naut.frobEig_tw _ _ h5.1, Multiset.sum_map_mul_right, Multiset.map_id', h5.2] at h9
  rw [D.naut.frobEig_tw _ _ h8.1, Multiset.sum_map_mul_right, Multiset.map_id', h8.2] at h10
  have h7 : ∑ c : Fin D.R.t, D.naut.iotaQC i (chiBar D.naut i (c.1 + 1) σ) =
      sumPart D.naut ⟨1, muEta D.naut i, D.R.t⟩ w *
        ((normV w : ℕ) : ℂ) ^ ((((1 - (D.R.nV : ℝ)) / 2 : ℝ)) : ℂ) := by
    rw [sumPart, ← List.sum_map_mul_right, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
      Finset.sum_range]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [chiBar_succ c.1 c.2, map_mul, map_zpow₀, h2 hw B σ hB hσ, h3 hw B σ hB hσ, ← Complex.cpow_intCast,
      mul_assoc, mul_assoc, ← Complex.cpow_add _ _ hq, ← Complex.cpow_add _ _ hq]
    congr 2
    push_cast
    ring
  have h11 := congrArg (fun x => D.naut.iotaQC i (D.naut.iotaQ i x)) (trace_of_block _ _ _ e (he σ))
  have h12 : iotaO D.nd D.naut i ((r₀ σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) _).trace =
      iotaO D.nd D.naut i ((ρ σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).trace +
        ∑ c : Fin D.R.t, D.naut.iotaQC i (chiBar D.naut i (c.1 + 1) σ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum] at h11
    refine Eq.trans ?_ (h11.trans ?_)
    · exact congrArg (fun x => D.naut.iotaQC i (D.naut.iotaQ i x)) (AddMonoidHom.map_trace (toK D.nd i) _)
    · congr 1
      exact congrArg (fun x => D.naut.iotaQC i (D.naut.iotaQ i x)) (AddMonoidHom.map_trace (toK D.nd i) _).symm
  refine Eq.trans ?_ h10.symm
  have h13 := h12.symm.trans h9
  rw [h7] at h13
  simp only [twistIso, muPart, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, add_zero, add_mul] at h13
  exact add_right_cancel h13

end GlobalTheory.TripleTrace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceRankRPartEqTraceBaseChangeTripleStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_rankRPart_eq_trace_baseChangeTriple : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (a : D.nd.Loc) (π : D.nd.X a) (ρ : Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a)) (s : D.ntw.Sig (D.ntw.twOf a)) (Sg : List (Part D.naut.CG)), GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D a π ρ → HasParamX D.nd D.naut a π Sg → GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsTriple D a s Sg → ∀ g, ((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)).trace = D.ntw.twist₂ a ((D.ntw.rhoS _ s g : GL (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))).trace := by
  first | exact @GlobalTheory.TripleTrace.trace_eq | exact GlobalTheory.TripleTrace.trace_eq | (intros; apply GlobalTheory.TripleTrace.trace_eq <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.PtCore

theorem twist_conj {Γ A B : Type} [Group Γ] [CommRing A] [CommRing B] {k : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin k) B) (ρ₀ : Γ →* GL (Fin k) A) (χ₀ : Γ →* Aˣ) (ψ χ : Γ →* Bˣ)
    (hχ : χ = (Units.map (f : A →* B)).comp χ₀ * ψ) (U : GL (Fin k) B)
    (hU : ∀ g, mapRep f ρ₀ g * U = U * ρ g) (g : Γ) :
    twistM ((Units.coeHom _).comp ρ) χ⁻¹ g * ((U⁻¹ : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) =
      ((U⁻¹ : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) *
        twistM (mapM f (twistM ((Units.coeHom _).comp ρ₀) χ₀⁻¹)) ψ⁻¹ g := by
  have h1 : ρ g * U⁻¹ = U⁻¹ * mapRep f ρ₀ g := by
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hU, mul_inv_cancel_right]
  have h2 : ((ρ g : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) * ((U⁻¹ : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) =
      ((U⁻¹ : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) *
        ((ρ₀ g : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).map f := congrArg Units.val h1
  have h3 : mapM f (twistM ((Units.coeHom _).comp ρ₀) χ₀⁻¹) g =
      f (((χ₀ g)⁻¹ : Aˣ) : A) • ((ρ₀ g : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).map f := by
    ext i j
    exact map_mul f _ _
  have h4 : (((χ g)⁻¹ : Bˣ) : B) = (((ψ g)⁻¹ : Bˣ) : B) * f (((χ₀ g)⁻¹ : Aˣ) : A) := by
    rw [hχ, MonoidHom.mul_apply, mul_inv_rev, Units.val_mul, MonoidHom.comp_apply, ← map_inv]
    rfl
  change ((((χ g)⁻¹ : Bˣ) : B) • ((ρ g : GL (Fin k) B) : Matrix (Fin k) (Fin k) B)) * _ =
    _ * ((((ψ g)⁻¹ : Bˣ) : B) • mapM f (twistM ((Units.coeHom _).comp ρ₀) χ₀⁻¹) g)
  rw [h3, smul_smul, ← h4, Matrix.smul_mul, Matrix.mul_smul, h2]

theorem twistedRho_conj_latTpsi : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (a : D.nd.Loc) (π : D.nd.X a) (ρ : D.nd.X a → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a))) (s : D.ntw.Sig (D.ntw.twOf a)) (Sg : List (Part D.naut.CG)), GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D a π (ρ π) → HasParamX D.nd D.naut a π Sg → GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsTriple D a s Sg → AbsIrrSub (redRep D.nd a (ρ π)) ⊤ → ∃ U : GL (Fin D.R.r) (D.nd.O a), ∀ g, WpO D.nd a ρ π g * (U : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) = (U : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) * GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.latTpsi D.ntw _ s (D.ntw.twist₂ a) (D.ntw.psiL a) g := by
  intro hC D a π ρ s Sg hρ hP hT hirr
  have htr := GlobalTheory.T.trace_rankRPart_eq_trace_baseChangeTriple hC D a π (ρ π) s Sg hρ hP hT
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_conj_of_trace_eq_residually_absIrreducible_DVR (D.nd.O a) (Formalism.MainNotions.N.GE D.nd) D.R.r (ρ π)
    (mapRep (D.ntw.twist₂ a) (D.ntw.rhoS _ s)) hirr (fun g => by
      rw [htr g]
      exact (AddMonoidHom.map_trace (D.ntw.twist₂ a) _))
  refine ⟨U⁻¹, fun g => ?_⟩
  refine twist_conj (D.ntw.twist₂ a) (ρ π) (D.ntw.rhoS _ s) _ (D.ntw.psiL a) (D.nd.chi a 1) ?_ U hU g
  rw [hT.1, hT.2.1]
  exact D.ntw.chi_tw a

end GlobalTheory.PtCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NlenLeLenN
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions GlobalTheory.SelBaseChange GlobalTheory.BlochKatoBaseChangeLe
open scoped ENNReal

namespace GlobalTheory.SelTwistLe

section Quot

variable (O : Type) [CommRing O] [IsDomain O] (k : ℕ)

def toPi : KOG O k →ₗ[O] (Fin k → KmodO O) :=
  (stdG O (FractionRing O) k).liftQ
    (LinearMap.compLeft (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ (Fin k)) (by
      rintro _ ⟨u, rfl⟩
      funext a
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨u a, rfl⟩)

variable {O k}

theorem toPi_bij : Function.Bijective (toPi O k) := by
  constructor
  · set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h : ∀ a, ∃ c, algebraMap O (FractionRing O) c = v a := fun a =>
      (Submodule.Quotient.mk_eq_zero _).1 (congrFun hx a)
    choose u hu using h
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨u, funext hu⟩
  · intro x
    choose v hv using fun a => Submodule.Quotient.mk_surjective _ (x a)
    exact ⟨Submodule.Quotient.mk v, funext hv⟩

theorem toPi_WKG {Γ : Type} [Group Γ] (M : Γ →* Matrix (Fin k) (Fin k) O) (g : Γ) (x : KOG O k) (a : Fin k) :
    toPi O k (WKG M g x) a = ∑ j, M g a j • toPi O k x j := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.mkQ _ (∑ j, algebraMap O (FractionRing O) (M g a j) * v j) =
    ∑ j, M g a j • Submodule.mkQ _ (v j)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, ← Algebra.smul_def, map_smul]

theorem push_WKG {O' : Type} [CommRing O'] [IsDomain O'] (f : O →+* O') (hf : Function.Injective f)
    {Γ Γ' : Type} [Group Γ] [Group Γ']
    (M : Γ →* Matrix (Fin k) (Fin k) O) (M' : Γ' →* Matrix (Fin k) (Fin k) O') (γ : Γ) (γ' : Γ')
    (h : M' γ' = (M γ).map f) (x : KOG O k) :
    pushKO f hf k (WKG M γ x) = WKG M' γ' (pushKO f hf k x) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (fun j => fracMap f hf
      (((M γ).map (algebraMap O (FractionRing O))).mulVec v j)) =
    Submodule.Quotient.mk (((M' γ').map (algebraMap O' (FractionRing O'))).mulVec fun j => fracMap f hf (v j))
  congr 1
  funext j
  simp [h, Matrix.mulVec, dotProduct, fracMap_alg]

end Quot

section Span

variable {R Γ A A' : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
  [AddCommGroup A] [Module R A] [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousConstSMul R A]
  [AddCommGroup A'] [Module R A'] (ρ : Representation R Γ A)

theorem mem_of_span (F : H1 ρ →ₗ[R] A') (S : Set (Γ → A)) (T : Submodule R A')
    (h : ∀ c ∈ S, ∃ hc : c ∈ Z1 ρ, F (Submodule.Quotient.mk ⟨c, hc⟩) ∈ T) (x : H1 ρ)
    (hx : x ∈ ((Submodule.span R S).comap (Z1 ρ).subtype).map (Submodule.mkQ _)) : F x ∈ T := by
  obtain ⟨z, hz, rfl⟩ := hx
  have key : Submodule.span R S ≤ ((T.comap F).comap (Submodule.mkQ _)).map (Z1 ρ).subtype := by
    refine Submodule.span_le.2 fun c hc => ?_
    obtain ⟨h1, h2⟩ := h c hc
    exact ⟨⟨c, h1⟩, h2, rfl⟩
  obtain ⟨z', hz', e⟩ := key hz
  rw [← Subtype.ext e]
  exact hz'

end Span

section Lift

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O] (B : LocBridge l E Ω Gw O)


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_lift {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O) (hM : ∀ a b, Continuous fun g => M g a b)
    (c : ↥(Z1 (WKG M))) (hc : Submodule.Quotient.mk c ∈ Br.bkG B P (WKG M) M) :
    ∃ z ∈ finiteCocycles (P.PD B.Kw) (matRep (Br.locM B M)), ∃ y : ↥Gw → Fin k → FractionRing O,
      (∀ g a, Br.toLLK B (y g a) = z (B.e g) a) ∧ ∀ g, c.1 g = Submodule.Quotient.mk (y g) := by
  obtain ⟨z, hz, m, h⟩ := (mem_HfD_iff P B M _).1 (phi_mem_of_mem_bkG P B M c hc)
  have hcob : cob (matRep (Br.locM B M)) m ∈ finiteCocycles (P.PD B.Kw) (matRep (Br.locM B M)) := by
    refine ⟨⟨?_, fun g h => ?_⟩, m ⊗ₜ 1, fun g => ?_⟩
    · refine continuous_pi fun a => ?_
      change Continuous fun g => (∑ j, ((B.eO (M (B.e.symm g) a j) : Br.Ow B) : Br.LLw B) * m j) - m a
      refine Continuous.sub (continuous_finsetSum _ fun j _ => Continuous.mul ?_ continuous_const)
        continuous_const
      exact continuous_subtype_val.comp (B.eO_cont.comp ((hM a j).comp B.e_symm_cont))
    · simp [cob]
    · simp [cob, actVB, TensorProduct.sub_tmul]
  refine ⟨_, add_mem hz hcob, ?_⟩
  have hy : ∀ g : ↥Gw, ∃ y : Fin k → FractionRing O, (∀ a, Br.toLLK B (y a) =
      (z + cob (matRep (Br.locM B M)) m) (B.e g) a) ∧ c.1 g = Submodule.Quotient.mk y := by
    intro g
    obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (c.1 g)
    have hg : Br.phi B k (c.1 (B.e.symm (B.e g))) = _ := h (B.e g)
    rw [MulEquiv.symm_apply_apply, ← hu] at hg
    obtain ⟨n, hn⟩ : Br.vecS B k u - (z (B.e g) + ((Br.locM B M (B.e g)).mulVec m - m)) ∈
      stdG (Br.Ow B) (Br.LLw B) k := (Submodule.Quotient.eq _).1 hg
    refine ⟨fun a => u a - algebraMap O _ (B.eO.symm (n a)), fun a => ?_, ?_⟩
    · have h1 : algebraMap (Br.Ow B) (Br.LLw B) (n a) =
        Br.toLLK B (u a) - (z + cob (matRep (Br.locM B M)) m) (B.e g) a := congrFun hn a
      rw [map_sub, Br.toLLK_alg, RingEquiv.apply_symm_apply, h1, sub_sub_cancel]
    · rw [← hu]
      refine (Submodule.Quotient.eq _).2 ⟨fun a => B.eO.symm (n a), funext fun a => ?_⟩
      simp
  choose y h1 h2 using hy
  exact ⟨y, h1, h2⟩

end Lift

theorem nlen_le_lenN {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ)
    (A A' : Type) [AddCommGroup A] [Module O A] [AddCommGroup A'] [Module O A']
    (h : Module.length O A ≤ Module.length O A') :
    (BlochKatoReduction.Gen.lenN O l A' ≠ ⊤ → nlen (O := O) l A ≠ ⊤) ∧
      ∀ q : ℚ, nlen (O := O) l A = (q : WithTop ℚ) → ENNReal.ofReal (q : ℝ) ≤ BlochKatoReduction.Gen.lenN O l A' := by
  unfold BlochKatoReduction.Gen.lenN nlen
  constructor
  · intro h1
    have h2 : Module.length O A ≠ ⊤ := fun h3 => h1 (by
      rw [(top_le_iff.1 (h3 ▸ h) : Module.length O A' = ⊤), ENat.toENNReal_top, ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top _)])
    rw [if_neg h2]
    exact WithTop.coe_ne_top
  · intro q hq
    split_ifs at hq with h2
    · exact absurd hq WithTop.top_ne_coe
    · rw [← WithTop.coe_injective hq, lenUnit, GlobalTheory.length_quotient_span_singleton_dvr]
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 h2
      rw [← hn] at h ⊢
      generalize (IsDiscreteValuationRing.addVal O (l : O)).toNat = a
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp
      · rw [ENat.toNat_coe, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast,
          ENNReal.ofReal_div_of_pos (by exact_mod_cast ha), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
        exact ENNReal.div_le_div_right (by simpa using ENat.toENNReal_le.2 h) _

section Main

open Formalism.MainNotions.BlochKatoReduction

variable (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i) (k : ℕ) (ψ : Formalism.MainNotions.N.GE D.nd →* (D.ntw.Ok i k)ˣ)

theorem equivariant (g : Formalism.MainNotions.N.GE D.nd) (x : KOG (D.ntw.Ok i k) D.R.r) :
    toPi _ _ (WKG (latTpsi D.ntw i s (toOk D.ntw i k) ψ) g x) = Gen.Trep i s k ψ g (toPi _ _ x) := by
  funext a
  rw [toPi_WKG]
  rw [show toOk D.ntw i k = Gen.phiK D.ntw i k from rfl]
  simp [Gen.Trep, twRep, matAct, latTpsi, latT, twistM, mapM, Gen.chiS, Finset.smul_sum, smul_smul, mul_assoc]

theorem latT_cont (a b : Fin D.R.r) : Continuous fun g => latT D.ntw i s g a b := by
  have h : (fun g => latT D.ntw i s g a b) = fun g =>
      ((D.ntw.chi1 i (D.ntw.jS i s) (D.ntw.side i s) g⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) *
        ((D.ntw.rhoS i s g : GL _ _) : Matrix _ _ _) a b := by
    funext g
    simp [latT, twistM]
  rw [h]
  exact ((D.ntw.twistCharacterFamily_continuous i _ _).comp continuous_inv).mul ((D.ntw.rhoS_cont i s).matrix_elem a b)

theorem rep_eq (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) :
    matRep (Br.locM (D.ntwbr i v hv) ((latT D.ntw i s).comp (decS D.nd v))) =
      Gen.repV (bk0 D) i v hv (Gen.Tgl i s) := by
  refine MonoidHom.ext fun g => ?_
  change Matrix.toLinAlgEquiv' _ = Matrix.toLinAlgEquiv' _
  congr 1
  refine Matrix.ext fun a b => ?_
  change (D.ntwbr i v hv).toLL (latT D.ntw i s ((D.ntwbr i v hv).e.symm g).1 a b) =
    (D.ntwbr i v hv).toLL (((Gen.Tgl i s ((D.ntwbr i v hv).e.symm g).1 : GL _ _) : Matrix _ _ _) a b)
  congr 1
  generalize ((D.ntwbr i v hv).e.symm g).1 = γ
  change _ = (Matrix.scalar (Fin D.R.r) ((Gen.chiS i s γ)⁻¹).val * (D.ntw.rhoS i s γ).val :
    Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)) a b
  simp [latT, twistM, Gen.chiS]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem cond_le (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i))
    (hψ : ∀ σ ∈ Dec (F := D.host.E) (D.nd.plOm.1 v), ψ σ = 1)
    (x : H1 ((WKG (latTpsi D.ntw i s (toOk D.ntw i k) ψ)).comp (Dec (F := D.host.E) (D.nd.plOm.1 v)).subtype))
    (hx : x ∈ condL D.loc D.ntwbr i s (toOk D.ntw i k) (toOk_inj D.ntw i k) ψ v) :
    cH ((Gen.Trep i s k ψ).comp (Dec (F := D.host.E) (D.nd.plOm.1 v)).subtype)
      ((WKG (latTpsi D.ntw i s (toOk D.ntw i k) ψ)).comp (Dec (F := D.host.E) (D.nd.plOm.1 v)).subtype)
      (toPi _ _) continuous_of_discreteTopology (fun _ _ => equivariant D i s k ψ _ _) x ∈
      Gen.bk (bk0 D) i s k ψ v := by
  unfold condL at hx
  rw [dite_eq_left hv] at hx
  unfold Gen.bk
  rw [dite_eq_left hv]
  refine mem_of_span _ _ _ _ ?_ x hx
  rintro _ ⟨c₀, h₀, rfl⟩
  have hM : ∀ g : Gw D.nd v, latTpsi D.ntw i s (toOk D.ntw i k) ψ g.1 =
      (latT D.ntw i s g.1).map (toOk D.ntw i k) := fun g => by
    simp [latTpsi, twistM, mapM, hψ g.1 g.2]
  obtain ⟨z, hz, y, hy, hc⟩ := exists_lift (D.loc (D.ntw.l i)) (D.ntwbr i v hv)
    ((latT D.ntw i s).comp (decS D.nd v)) (fun a b => (latT_cont D i s a b).comp continuous_subtype_val) c₀ h₀
  rw [rep_eq] at hz
  refine ⟨⟨(continuous_of_discreteTopology (f := pushKO _ (toOk_inj D.ntw i k) D.R.r)).comp c₀.2.1,
    fun g h => ?_⟩, Submodule.subset_span
      ⟨_, z, fun g a => fracMap _ (toOk_inj D.ntw i k) (y g a), hz, fun g a => ?_, fun g a => ?_, rfl⟩⟩
  · beta_reduce
    rw [c₀.2.2, map_add (f := _)]
    exact congrArg _ (push_WKG _ _ (latT D.ntw i s) _ g.1 g.1 (hM g) _)
  · obtain ⟨n, d, hd, e⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 i) (y g a)
    have hd0 := nonZeroDivisors.ne_zero hd
    have e' : algebraMap _ _ d * y g a = algebraMap _ (FractionRing (D.ntw.O0 i)) n := by
      rw [← e, mul_div_cancel₀ _ (by simpa using hd0)]
    refine ⟨n, d, ⟨hd0, ?_⟩, ?_⟩
    · have := congrArg (Br.toLLK (D.ntwbr i v hv)) e'
      rw [map_mul, Br.toLLK_alg, Br.toLLK_alg, hy] at this
      exact this
    · have := congrArg (fracMap _ (toOk_inj D.ntw i k)) e'
      rw [map_mul, fracMap_alg, fracMap_alg] at this
      exact this
  · change toPi _ _ (pushKO _ (toOk_inj D.ntw i k) D.R.r (c₀.1 g)) a = _
    rw [hc]
    rfl

theorem length_le (Q : Finset (PlE D.host))
    (hψ : ∀ v ∈ placesOver D.host.E (D.ntw.l i), ∀ σ ∈ Dec (F := D.host.E) (D.nd.plOm.1 v), ψ σ = 1) :
    Module.length (D.ntw.Ok i k) (selT D.loc D.ntwbr i s Q (toOk D.ntw i k) (toOk_inj D.ntw i k) ψ) ≤
      Module.length (D.ntw.Ok i k) (Gen.selT (bk0 D) i s k Q ψ) := by
  let c := cH (Gen.Trep i s k ψ) (WKG (latTpsi D.ntw i s (toOk D.ntw i k) ψ)) (toPi _ _)
    continuous_of_discreteTopology (equivariant D i s k ψ)
  have hS : setS D.ntw i = Gen.Spl i := by
    ext v
    simp [setS, Gen.Spl]
  have hc : ∀ x ∈ selT D.loc D.ntwbr i s Q (toOk D.ntw i k) (toOk_inj D.ntw i k) ψ,
      c x ∈ Gen.selT (bk0 D) i s k Q ψ := by
    intro x hx
    refine cH_mem_Sel _ _ _ _ _ _ _ _ _ (fun v y hv => ?_) x hx
    rw [hS] at hv
    unfold Formalism.GaloisCohomology.bkCond at hv ⊢
    split_ifs at hv ⊢ with h1 h2
    · exact cond_le D i s k ψ v h1 (hψ v h1) _ hv
    · trivial
    · exact cH_mem_H1ur _ _ _ _ _ _ _ hv
  refine Module.length_le_of_injective (c.restrict hc) ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  refine Subtype.ext (eq_zero_of_cH (ι := Unit) (Gen.Trep i s k ψ) _ (fun _ => toPi _ _)
    (fun _ => continuous_of_discreteTopology) (fun _ => equivariant D i s k ψ) ⟨?_, ?_⟩ x.1 fun _ => ?_)
  · exact fun m m' h => toPi_bij.1 (congrFun h ())
  · intro m
    obtain ⟨m', hm⟩ := toPi_bij.2 (m ())
    exact ⟨m', funext fun _ => hm⟩
  · exact congrArg Subtype.val hx

end Main

theorem sT_le_sLen : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.MainNotions.N.GE D.nd →* (D.ntw.Ok i k)ˣ), (∀ v ∈ placesOver D.host.E (D.ntw.l i), ∀ σ ∈ Dec (F := D.host.E) (D.nd.plOm.1 v), ψ σ = 1) → (BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) i s k Q ψ ≠ ⊤ → GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sT D.loc D.ntwbr i s Q (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk D.ntw i k) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk_inj D.ntw i k) ψ ≠ ⊤) ∧ ∀ q : ℚ, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sT D.loc D.ntwbr i s Q (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk D.ntw i k) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk_inj D.ntw i k) ψ = (q : WithTop ℚ) → ENNReal.ofReal (q : ℝ) ≤ BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) i s k Q ψ :=
  fun D i s k Q ψ hψ => nlen_le_lenN _ _ _ (length_le D i s k ψ Q hψ)

end GlobalTheory.SelTwistLe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalHomOfNatCast
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions GlobalTheory.TwistedSelmerCompare

namespace GlobalTheory.SelmerSameChar

theorem isLocalHom_of_natCast {O B : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing B]
    (f : O →+* B) (l : ℕ) (h0 : (l : O) ≠ 0) (h : ¬ IsUnit (l : B)) : IsLocalHom f := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hu : ¬ IsUnit (f ϖ) := fun hu => h (by
    obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    rw [← map_natCast f, hn, map_mul, map_pow]
    exact (u.isUnit.map f).mul (hu.pow n))
  refine ⟨fun x hx => ?_⟩
  by_contra hn
  have hm : x ∈ IsLocalRing.maximalIdeal O := hn
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hm
  obtain ⟨c, rfl⟩ := hm
  rw [map_mul] at hx
  exact hu (isUnit_of_mul_isUnit_right hx)

theorem isIntegral_of_finite {l₁ l₂ : ℕ} [i₁ : Fact l₁.Prime] [i₂ : Fact l₂.Prime] (h : l₁ = l₂) {O₀ O : Type}
    [CommRing O₀] [Algebra ℤ_[l₁] O₀] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l₂] O]
    [Module.Finite ℤ_[l₂] O] (f : O₀ →+* O) : f.IsIntegral := by
  subst h
  cases Subsingleton.elim i₁ i₂
  refine RingHom.IsIntegral.tower_top (algebraMap ℤ_[l₁] O₀) f ?_
  rw [padicInt_hom_ext (natCast_mem_maximalIdeal O) (f.comp (algebraMap ℤ_[l₁] O₀)) (algebraMap ℤ_[l₁] O)]
  exact algebraMap_isIntegral_iff.2 inferInstance

variable (D : D7)

theorem sT_congr (i : D.ntw.Tw) (s : D.ntw.Sig i) (Q : Finset (PlE D.host)) {O : Type} [CommRing O] [IsDomain O]
    {f f' : D.ntw.O0 i →+* O} (hf : Function.Injective f) (hf' : Function.Injective f')
    {ψ ψ' : Formalism.MainNotions.N.GE D.nd →* Oˣ} (h1 : f = f') (h2 : ψ = ψ') :
    sT D.loc D.ntwbr i s Q f hf ψ = sT D.loc D.ntwbr i s Q f' hf' ψ' := by
  subst h1 h2
  rfl

theorem toOk_local (i : D.ntw.Tw) (k : ℕ) : IsLocalHom (toOk D.ntw i k) := by
  have : CharZero (FractionRing (D.ntw.O0 i)) :=
    ((D.ntw.emb0 _).charZero_iff (D.ntw.emb0 _).injective).1 inferInstance
  have : CharZero (D.ntw.O0 i) := (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))).charZero
  refine isLocalHom_of_natCast _ (D.ntw.l i) (Nat.cast_ne_zero.2 (D.ntw.lPrime i).out.ne_zero) fun hu => ?_
  have := D.ntw.Ok_fin i k
  have := RingHom.IsIntegral.isLocalHom (f := algebraMap (D.ntw.O i) (D.ntw.Ok i k))
    (algebraMap_isIntegral_iff.2 inferInstance) (D.ntw.Ok_inj i k)
  rw [← map_natCast (algebraMap (D.ntw.O i) (D.ntw.Ok i k))] at hu
  exact D.ntw.O_l i (isUnit_of_map_unit _ _ hu)

theorem sTLoc_eq : ∀ (D : D7) (a : D.nd.Loc) (s : D.ntw.Sig (D.ntw.twOf a)) (k : ℕ) (ψ : Formalism.MainNotions.N.GE D.nd →* (D.ntw.Ok (D.ntw.twOf a) k)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar (D.ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk D.ntw (D.ntw.twOf a) k) (D.ntw.psiL a) ψ → GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sTLoc D a s = GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sT D.loc D.ntwbr (D.ntw.twOf a) s (D.nd.Q a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk D.ntw (D.ntw.twOf a) k) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk_inj D.ntw (D.ntw.twOf a) k) ψ := by
  intro D a s k ψ h
  obtain ⟨O₁, _, _, _, f, gA, gB, χ, iA, iB, lA, lB, cA, cB, eA, eB⟩ :=
    GlobalTheory.Proof.dvr_of_reflects_facts.common _ _ _ _ (D.ntw.twist₂ a) (toOk D.ntw _ k) (twO_inj D.ntw a)
      (isIntegral_of_finite (D.ntw.twOf_l a) _) (toOk_inj D.ntw _ k) (toOk_local D _ k) _ _ h
  have hf : Function.Injective f := Function.Injective.of_comp (f := gA) (by
    rw [← RingHom.coe_comp, cA]; exact twO_inj D.ntw a)
  exact (sT_congr D _ s _ _ (iA.comp hf) cA.symm eA.symm).trans
    ((GlobalTheory.SelmerFlat.sT_map_eq D _ s _ O₁ _ f hf gA iA χ).trans
      ((GlobalTheory.SelmerFlat.sT_map_eq D _ s _ O₁ _ f hf gB iB χ).symm.trans
        (sT_congr D _ s _ (iB.comp hf) _ cB eB)))

end GlobalTheory.SelmerSameChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SPiTopEqSTLoc
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions GlobalTheory.TwistedSelmerCompare

namespace GlobalTheory.ConjLatticeSelmer

theorem extCond_eq_bkG (L : LocTheory) {l₁ l₂ : ℕ} [i₁ : Fact l₁.Prime] [i₂ : Fact l₂.Prime] (h : l₁ = l₂)
    {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω)
    {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ O : Type} [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    [Algebra ℤ_[l₁] O₀] [Module.Finite ℤ_[l₁] O₀] [TopologicalSpace O₀] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l₂] O] [Module.Finite ℤ_[l₂] O] [TopologicalSpace O]
    (B₀ : LocBridge l₁ E Ω Gw O₀) (B : LocBridge l₂ E Ω Gw O) (h₀ : ∀ x, x ∈ A ↔ ‖B₀.j x‖ ≤ 1)
    (h₁ : ∀ x, x ∈ A ↔ ‖B.j x‖ ≤ 1) (f : O₀ →+* O) (hf : Function.Injective f) {k : ℕ}
    (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀) (M : ↥Gw →* Matrix (Fin k) (Fin k) O) (hM : M = mapM f M₀) :
    extCond f hf (WKG M₀) (Br.bkG B₀ (L l₁) (WKG M₀) M₀) (WKG M) = Br.bkG B (L l₂) (WKG M) M := by
  subst h hM
  cases Subsingleton.elim i₁ i₂
  obtain ⟨σ, hσ⟩ := GlobalTheory.EmbUnitBallConj.exists_conj l₁ Ω B₀.j B.j fun x => (h₀ x).symm.trans (h₁ x)
  have he : ∀ g : ↥Gw, ((B.e g : ↥(GK B.Kw)) : GQ l₁) = σ * ((B₀.e g : ↥(GK B₀.Kw)) : GQ l₁) * σ⁻¹ := by
    intro g
    refine GlobalTheory.padicAlgCl_algEquiv_eq_of_eq_on_isAlgClosed l₁ Ω B.j _ _ fun x => ?_
    rw [B.e_comm, ← hσ, ← hσ, ← B₀.e_comm]
    simp
  have hz := DFunLike.congr_fun
    (padicInt_hom_ext (natCast_mem_maximalIdeal O) (f.comp (algebraMap ℤ_[l₁] O₀)) (algebraMap ℤ_[l₁] O))
  exact le_antisymm (GlobalTheory.BlochKatoBaseChangeLe.extCond_le_bkG l₁ (L l₁) E Ω Gw O₀ O B₀ B σ he f hf hz k M₀)
    (GlobalTheory.BlochKatoBaseChange.bkG_le_extCond l₁ (L l₁) E Ω Gw O₀ O B₀ B σ he f hf hz k M₀)

variable (D : D7)

theorem selT_eq_selG (a : D.nd.Loc) (s : D.ntw.Sig (D.ntw.twOf a)) (ψ : Formalism.MainNotions.N.GE D.nd →* (D.nd.O a)ˣ)
    (hψ : ∀ v ∈ placesOver D.host.E (D.nd.l a), ∀ g ∈ Dec (F := D.host.E) (D.nd.plOm.1 v), ψ g = 1) :
    selT D.loc D.ntwbr _ s (D.nd.Q a) (D.ntw.twist₂ a) (twO_inj D.ntw a) ψ =
      Br.selG D.nd.plOm (D.nd.l a) (D.loc (D.nd.l a)) (D.nbr a) (↑(D.nd.S a) ∪ ↑(D.nd.Q a))
        (latTpsi D.ntw _ s (D.ntw.twist₂ a) ψ) := by
  have hl := D.ntw.twOf_l a
  have hS : setS D.ntw (D.ntw.twOf a) = ↑(D.nd.S a) := by
    rw [← TwistedTriples.badS_eq D a]
    unfold setS TwistedTriples.badS
    rw [hl]
  unfold selT Br.selG
  congr 1
  funext v
  unfold Formalism.GaloisCohomology.bkCond
  rw [hS]
  by_cases hv : v ∈ placesOver D.host.E (D.nd.l a)
  · have hv' : v ∈ placesOver D.host.E (D.ntw.l (D.ntw.twOf a)) := by rw [hl]; exact hv
    refine (if_pos hv').trans (Eq.trans ?_ (if_pos hv).symm)
    unfold condL Br.LlG
    rw [dite_eq_left hv, dite_eq_left hv']
    have := IsAlgClosure.isAlgClosed D.host.E (K := D.nd.Om)
    refine extCond_eq_bkG D.loc hl (D.nd.plOm.1 v) (D.ntwbr _ v hv') (D.nbr a v hv) (D.ntwbr_ind _ v hv')
      (D.nbr_ind a v hv) (D.ntw.twist₂ a) (twO_inj D.ntw a) ((latT D.ntw _ s).comp (decS D.nd v))
      ((latTpsi D.ntw _ s (D.ntw.twist₂ a) ψ).comp (decS D.nd v)) ?_
    ext g i j
    simp [latTpsi, twistM, mapM, hψ v hv g.1 g.2]
  · have hv' : v ∉ placesOver D.host.E (D.ntw.l (D.ntw.twOf a)) := by rw [hl]; exact hv
    exact (if_neg hv').trans (if_neg hv).symm

theorem nlen_congr {O : Type} [CommRing O] (l : ℕ) (M N : Type) [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (h : Module.length O M = Module.length O N) :
    nlen (O := O) l M = nlen (O := O) l N := by
  unfold nlen lenUnit
  rw [h]

theorem sPiTop_eq_sTLoc (a : D.nd.Loc) (π : D.nd.X a)
    (ρ : D.nd.X a → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a))) (s : D.ntw.Sig (D.ntw.twOf a))
    (U : GL (Fin D.R.r) (D.nd.O a))
    (hU : ∀ g, WpO D.nd a ρ π g * (U : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) =
      (U : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) * latTpsi D.ntw _ s (D.ntw.twist₂ a) (D.ntw.psiL a) g) :
    sPiTop D a ρ π = sTLoc D a s := by
  unfold sPiTop sTLoc sT
  rw [selT_eq_selG D a s _ fun v hv => D.ntw.psiL_l a v hv _ (D.nd.plOm.2 v), D.ntw.twOf_l]
  exact nlen_congr _ _ _ (GlobalTheory.T.selG_length_eq_of_conj _ _ D.nd.plOm (D.nd.l a) (D.nd.O a) (D.loc (D.nd.l a)) (D.nbr a)
    (↑(D.nd.S a) ∪ ↑(D.nd.Q a)) _ _ _ U hU).symm

end GlobalTheory.ConjLatticeSelmer

end
end

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.PtSel

theorem sameChar_eq_one {O₀ O₁ O₂ Γ : Type} [CommRing O₀] [CommRing O₁] [CommRing O₂] [Group Γ]
    {f₁ : O₀ →+* O₁} {f₂ : O₀ →+* O₂} {ψ₁ : Γ →* O₁ˣ} {ψ₂ : Γ →* O₂ˣ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar f₁ f₂ ψ₁ ψ₂) (g : Γ) (hg : ψ₁ g = 1) : ψ₂ g = 1 := by
  have h1 := h (Finsupp.single g 1 + Finsupp.single 1 (-1))
  rw [Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul]),
    Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul])] at h1
  simp only [Finsupp.sum_single_index, map_zero, zero_mul, map_one, one_mul, map_neg, hg, Units.val_one,
    mul_one, add_neg_cancel, true_iff] at h1
  ext
  rw [Units.val_one]
  exact add_neg_eq_zero.1 h1

theorem sel_at (hC : GlobalTheory.TwSys.Cheb) (D : D7) (hT : TriplesGood D) (hG : GoodPtRow D) (hR : ResAbsIrr D)
    (a : D.nd.Loc) (ρ : D.nd.X a → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a))) (π : D.nd.X a)
    (hπ : π ∈ D.nd.Zgood a) (hρ : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D a π (ρ π))
    (j : D.ntw.Tw) (hj : D.ntw.twOf a = j) (k : ℕ) (ψ : Formalism.MainNotions.N.GE D.nd →* (D.ntw.Ok j k)ˣ)
    (f : D.ntw.O0 j →+* D.nd.O a) (hf : HEq f (D.ntw.twist₂ a))
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar f (BlochKatoReduction.Gen.phiK D.ntw j k) (D.ntw.psiL a) ψ) :
    ∃ s : D.ntw.Sig j, BlochKatoReduction.Gen.goodS (BlochKatoReduction.bk0 D) j s ∧ D.ntw.side _ s = D.ntw.twSide a ∧
      (BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) j s k (D.nd.Q a) ψ ≠ ⊤ → Br.sFin D.loc D.nbr a ρ π) ∧
      ENNReal.ofReal (Br.sPi D.loc D.nbr a ρ π : ℝ) ≤ BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) j s k (D.nd.Q a) ψ ∧
      AttachedIn D a π j s := by
  subst hj
  obtain rfl := eq_of_heq hf
  obtain ⟨σ, Sg, hrow, hW, hX⟩ := hG a π hπ
  obtain ⟨s, htr, hgood⟩ := hT a σ Sg hrow hW
  obtain ⟨U, hU⟩ := GlobalTheory.PtCore.twistedRho_conj_latTpsi hC D a π ρ s Sg hρ hX htr (hR a π hπ _ hρ)
  have e1 := GlobalTheory.ConjLatticeSelmer.sPiTop_eq_sTLoc D a π ρ s U hU
  have e2 := GlobalTheory.SelmerSameChar.sTLoc_eq D a s k ψ hS
  have hψ : ∀ v ∈ placesOver D.host.E (D.ntw.l (D.ntw.twOf a)),
      ∀ g ∈ Dec (F := D.host.E) (D.nd.plOm.1 v), ψ g = 1 := by
    intro v hv g hg
    rw [D.ntw.twOf_l] at hv
    exact sameChar_eq_one hS g (D.ntw.psiL_l a v hv _ (D.nd.plOm.2 v) g hg)
  obtain ⟨h1, h2⟩ := GlobalTheory.SelTwistLe.sT_le_sLen D _ s k (D.nd.Q a) ψ hψ
  rw [← e2, ← e1] at h1 h2
  refine ⟨s, hgood, htr.2.1, ?_, ?_, ⟨rfl, σ, Sg, hrow, hW, hX, htr⟩⟩
  · intro hne
    have h3 := h1 hne
    unfold Br.sFin
    rw [lt_top_iff_ne_top]
    intro h4
    exact h3 (by simp only [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sPiTop, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.nlen, h4, if_true])
  · by_cases h4 : Module.length (D.nd.O a) ↥(Br.selPi D.loc D.nbr a ρ π) = ⊤
    · have h5 : BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) _ s k (D.nd.Q a) ψ = ⊤ := by
        by_contra hne
        exact h1 hne (by simp only [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sPiTop, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.nlen, h4, if_true])
      rw [h5]
      exact le_top
    · exact h2 _ (by simp only [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sPiTop, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.nlen, h4, if_false, Br.sPi])

theorem selCore : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (C : NChoice D), NChTie D C → TriplesGood D → GoodPtRow D →
    ResAbsIrr D → SameTwist D C →
    ∀ ρ : ∀ i : D.nd.Loc, D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i)),
      (∀ i, ∀ π ∈ D.nd.Zgood i, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D i π (ρ i π)) → SelCore D C ρ := by
  intro hC D C hTie hT hG hR hS ρ hρ i π hπ
  obtain ⟨f, hf, hs⟩ := hS.exists_heq i
  obtain ⟨s, h1, h2, h3⟩ := sel_at hC D hT hG hR i (ρ i) π hπ (hρ i π hπ) _ (hTie.twOf_eq i) _ _ f hf hs
  rw [hTie.Q_eq i] at h3
  exact ⟨s, h1, h2.trans (hTie.twSide_eq i), h3⟩

end GlobalTheory.PtSel

end
end

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.JointSix

theorem psiAt_psiW {D : D7} (C : NChoice D) (w : D.what₂.places.Pl) :
    BlochKatoReduction.Gen.psiAt (C.sd w) (KillingConditions.psiW C w) = GlobalTheory.PtCore.psiG D C w := by
  unfold KillingConditions.psiW GlobalTheory.PtCore.psiG
  cases h : C.sd w
  · ext g
    simp [BlochKatoReduction.Gen.psiAt]
  · simp [BlochKatoReduction.Gen.psiAt]

theorem main : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (C : NChoice D)
    (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))),
    GlobalTheory.PtCore.PtFam D r ρ → NChTie D C → GlobalTheory.PtCore.TriplesGood D → GlobalTheory.PtCore.SameTwist D C →
    GlobalTheory.PtCore.GoodPtRow D → GlobalTheory.PtCore.ResAbsIrr D → KillingConditions.SignatureChoiceCondition ρ C := by
  intro hC D C r ρ hF hT hTr hS hG hR i _
  have hsel := GlobalTheory.PtSel.selCore hC D C hT hTr hG hR hS ρ
    (fun i π hπ => hF.pt i π (Formalism.L2.zgoodSub D i hπ))
  refine ⟨fun π hπ => ?_, ?_⟩
  · obtain ⟨s, h1, h2, h3, h4, -⟩ := hsel i π hπ
    refine ⟨s, h1, ?_⟩
    rw [h2, psiAt_psiW]
    exact ⟨h3, h4⟩
  · rw [Rat.cast_sum, ← hT.Q_eq i]
    exact Finset.sum_le_sum fun v hv => GlobalTheory.T.conductorRoot_sub_one_length_le_tameValue D C hT i v hv

end GlobalTheory.JointSix

end

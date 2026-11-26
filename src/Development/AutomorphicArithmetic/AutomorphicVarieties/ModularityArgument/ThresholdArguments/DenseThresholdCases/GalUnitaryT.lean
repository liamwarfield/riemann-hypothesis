module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.MemOfProdEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.PlainGd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.FrobTwT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWBridge
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.GenericUnitaryDualGL

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self UpperTheory.V.UnitaryThreeInertia.Coef.isLocalRing

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Assemble
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Af.Gu
open UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
private theorem ev_notMem {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
theorem UpperTheory.V.Z.Win.Gu.assemble_s (H : _root_.UpperTheory.V.Af.HypothesesH') (hB : GlobalTheory.BcSpeh.BcSpeh) (hFam : SumFamG) (hHalf : HalfG) (hStr : Strings)
    (hUni : CompUnique) (hRec : RecTotT) (hFrob : FrobTotT) (hPol : PolOfFrob) (hLink : SatLink) (hConj : SatConj)
    (hIrr : IrrCaseT) (hPl : PlainGd) : GalUnitaryT := by
  intro E Ω _ _ _ _ _ _ hE l _ _ ι n hn π hπ
  obtain ⟨c, a, d, hsum, P, ρ, m, σ, hP, hS, hsplit⟩ := hB E hE n hn π hπ
  have hc : 1 ≤ c := by
    rcases c with _ | c
    · simp at hsum; omega
    · omega
  have hint : ∀ i (k : Fin (d i)) τ, (m i τ).Nodup ∧ ∀ z ∈ m i τ, ∃ j : ℤ, z + (ex n (d i) k : ℂ) / 2 = j := fun i k τ => by
    obtain ⟨lam, hl⟩ := GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary E n hn π hπ τ
    exact (hStr n c d (m · τ) lam (hP.weight τ lam hl)).1 i k
  choose r₀ HT₀ h₀ hw₀ using fun i (k : Fin (d i)) =>
    hHalf E Ω l ι (a i) (hP.pos i).1 (P i) (hP.csd i) (ρ i) (hP.loc i) (m i) (hP.inf i) (ex n (d i) k) (hint i k)
  choose r₁ h₁ hi₁ using fun i => hFam E Ω l ι (d i) (hP.pos i).2 (fun _ => a i) (fun _ => (hP.pos i).1) (d i * a i) (by simp)
    (r₀ i) _ (HT₀ i) (h₀ i)
  obtain ⟨r, hr, hi⟩ := hFam E Ω l ι c hc (fun i => d i * a i) (fun i => Nat.mul_pos (hP.pos i).2 (hP.pos i).1) n hsum r₁ _ _ h₁
  have hpar : ∀ w, ParAtT ι r w (totPar n d (ρ · w)) := hr.par
  have hF : ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ S : Fin c → Multiset ℂˣ,
      (∀ i, (CG.mk (P i)).HasSat w (S i)) → FrobEig ι r w (algSat n (normV w) (satTot w d S)) := fun w hw S hS =>
    hFrob E Ω l ι n c a d r hr.cont w hw (ρ · w) S (fun i => ((hLink E _ (P i)).1 w _ (hP.loc i w) _).1 (hS i)) (hpar w)
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      ∃ S : Fin c → Multiset ℂˣ, ∀ i, (CG.mk (P i)).HasSat w (S i) := by
    filter_upwards [ev_notMem (K := E) l, Filter.eventually_all.2 fun i => (hLink E _ (P i)).2] with w h1 h2
    exact ⟨h1, Classical.skolem.1 h2⟩
  have hsph : ∀ w, IsUnramU π w → ∀ i, ∃ B, GlobalTheory.LFun.HasSatGL w (ρ i w).ρ B := fun w hu i =>
    (_root_.UpperTheory.V.Af.satake_local_of_printed_results H.toClassicalTheorems E (a i) w (ρ i w)).1 (by
      obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1
        (GlobalTheory.SphBC.isSpherical_of_isUnramU E hE n π hπ c a d hsum P ρ m σ hP hS hsplit w hu i (ρ i w) (hP.loc i w))
      exact ⟨x, h0, GlobalTheory.LGrp.mem_fixed.1 hx⟩)
  refine ⟨r, fun τ => ∑ i, ∑ k, HT₀ i k τ, hr.cont, hr.ss, fun w hw hu A hA => ?_, fun τ lam hl => ?_, fun w hw τ hτ => ?_, ?_, fun hirr => ?_⟩
  · choose S hSat using hsph w hu
    exact (hFrob E Ω l ι n c a d r hr.cont w hw (ρ · w) S hSat (hpar w) A hA).1
  · rw [← (hStr n c d (m · (ι.toRingHom.comp τ)) lam (hP.weight _ lam hl)).2]
    simp only [← hw₀]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← Multiset.coe_mapAddMonoidHom, map_sum]
  · have e := hRec E Ω n c a d hsum P w (ρ · w) (σ · w) hP.pos (hP.loc · w) (hS · w) τ
      (hUni E n π hπ w hw _ _ _ _ hτ (hsplit w hw))
    refine ⟨fun A h rc hrc => e A h rc hrc ▸ hpar w A h rc hrc, fun hp => hr.ht w fun A h rc hrc => ?_⟩
    have g := hPl E Ω A w h rc hrc n τ hp
    rw [← e A h rc hrc] at g
    exact g
  · refine hPol E Ω l ι n r hr.cont hr.ss ?_
    filter_upwards [hev, (conjSrc_injective (IsCMField.complexConj E).toRingEquiv).tendsto_cofinite.eventually hev]
      with w ⟨hw, _⟩ ⟨hw', S, hS'⟩
    refine ⟨satTot (Bc.cPl w) d S, ?_, hF _ hw' S hS'⟩
    rw [← (hConj E w).2 c d S]
    exact hF w hw _ fun i => (hConj E w).1 _ (P i) (hP.csd i) _ (hS' i)
  · refine hIrr E Ω l ι n hn π hπ c a d hsum P ρ m σ hP (fun i w => (hS i w).2.2) hsplit
      (fun w hu i => (hsph w hu i).imp fun B hB => ((hLink E _ (P i)).1 w _ (hP.loc i w) B).2 hB) (hi hirr).1 (fun i => (hi₁ i ((hi hirr).2 i)).1) r hr.ss ?_
    filter_upwards [hev] with w ⟨hw, S, hS'⟩
    exact ⟨S, hS', hF w hw S hS'⟩
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuPolG
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Win.Gu.polG_of_printsH_of_rT :
    _root_.UpperTheory.V.Af.HypothesesH' → RowT → PolG := by
  intro PH hRow E Ω _ _ _ _ _ _ l _ ι a ha P χ hreg hpol σ hσ
  obtain ⟨r, wt, HT, H⟩ := hRow E Ω l ι a ha P χ hreg
    ⟨hpol.sign, GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a P (compNorm E χ) (PH.toClassicalTheorems.litN.aut.gk E a _) hpol.dual⟩
  have hRc : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l)) := Units.continuous_val.comp H.cont
  refine ⟨r, HT, ⟨H.cont, H.ss, fun w hg A h O _ _ _ Bw hj => ?_,
    fun w A h rc hrc => ⟨fun hw => ?_, fun O _ _ _ Bw hj g => ?_⟩⟩, H.weights⟩
  · obtain ⟨rc, hrc⟩ := UpperTheory.Zero.LLC.recTExists E Ω A w h
    obtain ⟨g1, g2⟩ := hg A h rc hrc
    obtain ⟨k1, -, k3, -⟩ := (H.above (Loc.PP l) _ (Loc.tiedP l) w A h O Bw hj).nice (σ w) (hσ w) rc hrc (Or.inr g1) g2
    exact ⟨k1, k3⟩
  · exact ⟨wdOf h hw ι r, isWDOf_wdOf hw ι hRc, fun g => (H.away w hw A h rc hrc (σ w) (hσ w)).tor g.1 g.2⟩
  · obtain ⟨-, k2, -, k4⟩ := (H.above (Loc.PP l) _ (Loc.tiedP l) w A h O Bw hj).nice (σ w) (hσ w) rc hrc (Or.inr g.1) g.2
    exact ⟨k2, k4.tor g.1 g.2⟩
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuSumTwoG
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open Module TensorProduct GlobalTheory.Pst.DpstMap
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section Split
variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}
  {V₀ V₁ V₂ : Type} [AddCommGroup V₀] [Module ↥LL.1 V₀] [Module ℚ_[l] V₀] [IsScalarTower ℚ_[l] ↥LL.1 V₀]
  [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁]
  [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂]
  {ρ₀ : Representation ↥LL.1 ↥(GK K) V₀} {ρ₁ : Representation ↥LL.1 ↥(GK K) V₁}
  {ρ₂ : Representation ↥LL.1 ↥(GK K) V₂}
private theorem tensV_section (p : V₁ →ₗ[↥LL.1] V₂) (s : V₂ →ₗ[↥LL.1] V₁) (hps : ∀ v, p (s v) = v)
    (x : V₂ ⊗[ℚ_[l]] Bst P) : tensV P p (tensV P s x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [tensV, hps]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
variable [FiniteDimensional ↥LL.1 V₀] [FiniteDimensional ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₂]
private theorem isPst_split {AI : LocAinf l P} (T : LocTied l P AI) {i : V₀ →ₗ[↥LL.1] V₁} {p : V₁ →ₗ[↥LL.1] V₂}
    {s : V₂ →ₗ[↥LL.1] V₁} (hi : ∀ g v, i (ρ₀ g v) = ρ₁ g (i v)) (hp : ∀ g v, p (ρ₁ g v) = ρ₂ g (p v))
    (hs : ∀ g v, s (ρ₂ g v) = ρ₁ g (s v)) (h1 : Function.Injective i) (h2 : Function.Exact i p)
    (hps : ∀ v, p (s v) = v) (hV₀ : IsPst P ρ₀) (hV₂ : IsPst P ρ₂) : IsPst P ρ₁ := by
  obtain ⟨hdom, hfrac, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
  haveI := LL.2
  haveI : FiniteDimensional ℚ_[l] V₀ := Module.Finite.trans ↥LL.1 V₀
  haveI : FiniteDimensional ℚ_[l] V₁ := Module.Finite.trans ↥LL.1 V₁
  haveI : FiniteDimensional ℚ_[l] V₂ := Module.Finite.trans ↥LL.1 V₂
  have b₁ := GlobalTheory.T.finrank_dpst_unramified_le_dim_representation P hdom hfrac ρ₁
  haveI f₁ : FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₁) :=
    Module.rank_lt_aleph0_iff.mp (b₁.trans_lt (Cardinal.natCast_lt_aleph0))
  obtain ⟨f₀, c₀⟩ := (isPst_iff P ρ₀).1 hV₀
  obtain ⟨f₂, c₂⟩ := (isPst_iff P ρ₂).1 hV₂
  obtain ⟨hinj, hex⟩ := UpperTheory.V.Loc.PstExact.dmap_exact P hi hp h1 h2
  have inj : Function.Injective (UpperTheory.V.Loc.PstExact.dUr P hi) := fun x y h => hinj h
  have sur : Function.Surjective (UpperTheory.V.Loc.PstExact.dUr P hp) := fun y =>
    ⟨toUr P ρ₁ (dmap P hs ((toUr P ρ₂).symm y)), Subtype.ext (tensV_section P p s hps _)⟩
  have ex : Function.Exact (UpperTheory.V.Loc.PstExact.dUr P hi) (UpperTheory.V.Loc.PstExact.dUr P hp) := fun y => hex y
  have e := (UpperTheory.V.Loc.PstExact.dUr P hp).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 sur, finrank_top, LinearMap.exact_iff.mp ex, LinearMap.finrank_range_of_inj inj] at e
  have e' := (p.restrictScalars ℚ_[l]).finrank_range_add_finrank_ker
  have exq : Function.Exact (i.restrictScalars ℚ_[l]) (p.restrictScalars ℚ_[l]) := h2
  rw [LinearMap.exact_iff.mp exq, LinearMap.finrank_range_of_inj (f := i.restrictScalars ℚ_[l]) h1,
    LinearMap.range_eq_top.2 (show Function.Surjective (p.restrictScalars ℚ_[l]) from fun v => ⟨s v, hps v⟩),
    finrank_top] at e'
  exact (isPst_iff P ρ₁).2 ⟨f₁, by omega⟩
end Split
section Sum
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) {a b : ℕ}
private theorem isPst_sum (T : LocTied l P AI) {L : FinExt l} (s : ↥Gw →* GL (Fin a) ↥L.1) (s' : ↥Gw →* GL (Fin b) ↥L.1)
    (h : IsPst P (Bw.repE L s)) (h' : IsPst P (Bw.repE L s')) : IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s')) := by
  let e : (Fin (a + b) → ↥L.1) ≃ₗ[↥L.1] (Fin a → ↥L.1) × (Fin b → ↥L.1) :=
    (LinearEquiv.funCongrLeft ↥L.1 ↥L.1 finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow _ _ ↥L.1 ↥L.1)
  have he : ∀ g v, e (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s') g v) =
      (Bw.repE L s g (e v).1, Bw.repE L s' g (e v).2) := by
    intro g v
    rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply, GlobalTheory.BCGal.sumRep_val]
    ext i <;>
      simp [e, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, LinearMap.funLeft] <;> rfl
  have he' : ∀ g x, e.symm (Bw.repE L s g x.1, Bw.repE L s' g x.2) =
      Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s') g (e.symm x) := by
    intro g x
    apply e.injective
    rw [he, e.apply_symm_apply, e.apply_symm_apply]
  refine isPst_split P T (i := e.symm.toLinearMap ∘ₗ LinearMap.inl ↥L.1 _ _)
    (p := LinearMap.snd ↥L.1 _ _ ∘ₗ e.toLinearMap) (s := e.symm.toLinearMap ∘ₗ LinearMap.inr ↥L.1 _ _)
    (ρ₀ := Bw.repE L s) (ρ₂ := Bw.repE L s') (fun g v => ?_) (fun g v => ?_) (fun g v => ?_) ?_ ?_ ?_ h h'
  · have := he' g (v, 0)
    simpa using this
  · simp [he]
  · have := he' g (0, v)
    simpa using this
  · intro x y hxy
    simpa using hxy
  · intro y
    constructor
    · intro hy
      refine ⟨(e y).1, ?_⟩
      apply e.injective
      have hy' : (e y).2 = 0 := hy
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.inl_apply, e.apply_symm_apply]
      exact Prod.ext rfl hy'.symm
    · rintro ⟨x, rfl⟩
      simp
  · intro v
    simp
private theorem isPstAt_sum (T : LocTied l P AI) {r : ↥Gw →* GL (Fin a) (Om l)} {r' : ↥Gw →* GL (Fin b) (Om l)}
    (h : IsPstAt P Bw r) (h' : IsPstAt P Bw r') : IsPstAt P Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') := by
  obtain ⟨L₁, r₁, m₁, p₁⟩ := h
  obtain ⟨L₂, r₂, m₂, p₂⟩ := h'
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have n₁ := m₁.enlarge l₁
  have n₂ := m₂.enlarge l₂
  exact ⟨supExt L₁ L₂, _, ⟨n₁.1, by rw [GlobalTheory.Pst.SumParam.mapRep_sumRep, n₁.2, n₂.2]⟩,
    isPst_sum Bw T _ _ (GlobalTheory.T.isPotentiallySemistable_coefficientField_enlarge P Bw l₁ r₁ p₁) (GlobalTheory.T.isPotentiallySemistable_coefficientField_enlarge P Bw l₂ r₂ p₂)⟩
end Sum
theorem UpperTheory.V.Z.Win.Gu.sumTwoG_of_printsH_gdLaws_sumAway_sumHTAt :
    _root_.UpperTheory.V.Af.HypothesesH' → GdLaws → SumAway → SumHTAt → SumTwoG := by
  intro _ hG hA hT E Ω _ _ _ _ _ l _ ι a b r r' p p' HT HT' C C'
  obtain ⟨T⟩ := Loc.tiedP l
  have hv := GlobalTheory.BCGal.cont_sumRep r r' (Units.continuous_val.comp C.cont) (Units.continuous_val.comp C'.cont)
  have hc : Continuous (Formalism.MainNotions.SumRepresentations.At.sumRep r r') := by
    refine Units.continuous_iff.2 ⟨hv, ?_⟩
    simp only [← map_inv]
    exact hv.comp continuous_inv
  refine ⟨hc, GlobalTheory.BCGal.ss_sumRep r r' C.ss C'.ss, fun w hg => ?_, fun w A h rc hrc => ?_⟩
  · exact hT E Ω l a b r r' C.cont C'.cont HT HT' w
      (C.ht w fun A h rc hrc => (((hG E Ω A w h).1 _ _).1 (hg A h rc hrc)).1)
      (C'.ht w fun A h rc hrc => (((hG E Ω A w h).1 _ _).1 (hg A h rc hrc)).2)
  · obtain ⟨a1, b1⟩ := C.par w A h rc hrc
    obtain ⟨a2, b2⟩ := C'.par w A h rc hrc
    have sp := ((hG E Ω A w h).1 (p w A h rc) (p' w A h rc)).1
    refine And.intro (fun hw => ?_) (fun O _ _ _ Bw hj hg => ?_)
    · obtain ⟨x, hx, kx⟩ := a1 hw
      obtain ⟨x', hx', kx'⟩ := a2 hw
      refine Exists.intro (x.lpSum x') (And.intro (hA E Ω l ι a b r r' C.cont C'.cont w hw A h _ _ hx hx') fun g => ?_)
      rw [kx (sp g).1, kx' (sp g).2]
    · obtain ⟨p1, e1⟩ := b1 O Bw hj (sp hg).1
      obtain ⟨p2, e2⟩ := b2 O Bw hj (sp hg).2
      have e : (Formalism.MainNotions.SumRepresentations.At.sumRep r r').comp (Dec (F := E) A).subtype =
          Formalism.MainNotions.SumRepresentations.At.sumRep (r.comp (Dec (F := E) A).subtype) (r'.comp (Dec (F := E) A).subtype) := by
        ext g i j
        rfl
      have p3 := isPstAt_sum Bw T p1 p2
      rw [e]
      exact ⟨p3, by rw [GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable l _ _ ⟨T⟩ ι E Ω A w O Bw h hj a b _ _ p1 p2 p3, e1, e2]⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuFrobTotT
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.PRep GlobalTheory.SmGL
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win.Gu
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
private theorem unr_lpSum {x y : WD h} (hx : x.unr) (hy : y.unr) : (x.lpSum y).unr := by
  induction x using Quotient.inductionOn with | h a => ?_
  induction y using Quotient.inductionOn with | h b => ?_
  have ha : a.2.Unr := hx
  have hb : b.2.Unr := hy
  show (WD.mk (a.2.sum b.2)).unr
  rw [WD.unr_mk]
  refine ⟨?_, fun σ => ?_⟩
  · rw [WDRep.sum_N, ha.1, hb.1, LinearMap.prodMap_zero]
  · rw [WDRep.sum_ρ, ha.2, hb.2]; exact LinearMap.prodMap_one
private theorem sumList_spec (g : Weil h) : ∀ (c : ℕ) (f : Fin c → WD h) (M : Fin c → Multiset ℂ),
    (∀ i, (f i).unr ∧ (f i).charPol g = ((M i).map fun b => X - C b).prod) →
    (sumList (List.ofFn f)).unr ∧ (sumList (List.ofFn f)).charPol g = ((∑ i, M i).map fun b => X - C b).prod := by
  intro c
  induction c with
  | zero =>
    intro f M _
    have e : sumList (List.ofFn f) = WD.lpZero (h := h) := by simp [sumList]
    rw [e, WD.lpZero, WD.unr_mk, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd]
    exact ⟨WDRep.unr_diag _, by simp⟩
  | succ c ih =>
    intro f M H
    obtain ⟨h1, h2⟩ := ih (fun i => f i.succ) (fun i => M i.succ) fun i => H i.succ
    have e : sumList (List.ofFn f) = (f 0).lpSum (sumList (List.ofFn fun i => f (Fin.succ i))) := by
      rw [List.ofFn_succ]; rfl
    rw [e, WD.charPol_lpSum, h2, (H 0).2, Fin.sum_univ_succ, Multiset.map_add (f := _), Multiset.prod_add]
    exact ⟨unr_lpSum (H 0).1 h1, rfl⟩
private theorem rec_eq_diagV {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRecV h rc) {a : ℕ}
    {σ : IrrRep (GL (Fin a) (w.adicCompletion E))} {α : Fin a → ℂˣ} (hα : HasSatake σ.ρ α) :
    rc (cls σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  obtain ⟨_, _, _, L⟩ := H
  have φ := equivRep σ
  exact L.sat (cls σ) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1,
    (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩
private theorem rec_tw_diag {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRecV h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) (s : ℝ) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      (rc (cl σ)).lpTw s = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w s) := by
  have hsph : IsSpherical (ParLaws.toRep σ).ρ := by
    have := hB.1
    unfold IsSpherical IsSphericalFor
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact this
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.main UpperTheory.Zero.LLC.Pr.bz (w.adicCompletion E) n
    ⟨_, σ.ρ, σ.smooth, σ.irred⟩ hsph
  refine ⟨α, hB.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα), ?_⟩
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    rec_eq_diagV H (σ := ParLaws.toRep σ) hα
  rw [e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]
private theorem val_inv_eq (n d k : ℕ) (a : ℂˣ) :
    (((a⁻¹ * qPow w ((ex n d k : ℝ) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ) =
      ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) *
        ((a * qPow w ((k : ℝ) - ((d : ℝ) - 1) / 2) : ℂˣ) : ℂ) := by
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (zero_lt_one.trans (GlobalTheory.WeilDeligne.one_lt_normV w)).ne'
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv,
    coe_qPow, ← Complex.cpow_neg, Units.val_mul, coe_qPow, mul_left_comm, Complex.ofReal_natCast, ← Complex.cpow_add _ _ hq]
  congr 2
  simp only [ex]
  push_cast
  ring
private theorem totPar_spec {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRecV h rc) (n c : ℕ) (a d : Fin c → ℕ)
    (ρ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E))) (S : Fin c → Multiset ℂˣ)
    (hS : ∀ i, GlobalTheory.LFun.HasSatGL w (ρ i).ρ (S i)) (g : Weil h) (hg : deg g = -1) :
    (totPar n d ρ A h rc).unr ∧
      (totPar n d ρ A h rc).charPol g = ((algSat n (normV w) (satTot w d S)).map fun b => X - C b).prod := by
  have e : algSat n (normV w) (satTot w d S) = ∑ i, ∑ k : Fin (d i),
      algSat n (normV w) ((S i).map (· * qPow w (((k : ℕ) : ℝ) - ((d i : ℝ) - 1) / 2))) := by
    have hm : ∀ {α β ι : Type} (f : α → β) (s : Finset ι) (M : ι → Multiset α),
        (∑ i ∈ s, M i).map f = ∑ i ∈ s, (M i).map f := fun f s M => map_sum (Multiset.mapAddMonoidHom f) M s
    simp only [algSat, satTot, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, hm]
  rw [e]
  refine sumList_spec g c _ _ fun i => sumList_spec g (d i) _ _ fun k => ?_
  obtain ⟨α, hα, e⟩ := rec_tw_diag H (ρ i) (S i) (hS i) ((ex n (d i) k : ℝ) / 2)
  rw [e, hα, WD.unr_mk, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, hg]
  refine ⟨WDRep.unr_diag _, ?_⟩
  simp only [val_inv_eq, algSat, Multiset.map_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]
  rfl
end UpperTheory.V.Z.Win.Gu
theorem UpperTheory.V.Z.Win.Gu.frobTotT_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ExtraV → GdLaws → FrobTotT := by
  intro _ hX hG F Ω _ _ _ _ _ l _ ι n c a d r _ w hl ρ S hS H A h
  obtain ⟨rc, hrc⟩ := UpperTheory.Zero.LLC.recTExists F Ω A w h
  have hsp := totPar_spec (hX F Ω A w h rc hrc) n c a d ρ S hS
  have hu := (hsp (frob h)⁻¹ (by rw [deg_inv, deg_frob])).1
  have hx := ((H A h rc hrc).1 hl).isWDOf ((hG F Ω A w h).2.2.2 _ hu)
  have hw := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, b, hN, -⟩ := hx
  refine ⟨(hN.unr_wdOf_iff hl ht ι).1 (by rw [hw]; exact hu), fun s hs => ?_⟩
  have hd : deg (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h) = 1 := deg_eq_one_iff.2 hs
  have := hN.charPol_wdOf hl ht ι (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h)⁻¹
  rw [hw, (hsp _ (by rw [deg_inv, hd])).2] at this
  exact this.symm
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuProdT
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.UnitaryBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem locProd_sum {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {ε : EpsFamily A} (L : LawsV a ha ε rc) :
    ∀ {c n : ℕ} {N : Fin c → ℕ} (hn : ∑ i, N i = n) (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
      (τ : SmIrr (GL (Fin n) (w.adicCompletion E))), Nonempty (τ.ρ.Equiv (locProd hn w σ)) →
      rc (cl τ) = sumList (List.ofFn fun i => rc (cl (σ i))) := by
  intro c
  induction c with
  | zero =>
    intro n N hn σ τ e
    obtain rfl : n = 0 := by simpa using hn.symm
    obtain ⟨e⟩ := e
    obtain ⟨φ⟩ := SupportRing.nonempty_equiv_unit (k := w.adicCompletion E) (stdBlocks N hn) fun i => (σ i).ρ
    have h1 := L.det 0 1 isSmoothChar_one
    simp only [List.range_zero, List.map_nil] at h1
    rw [List.ofFn_zero]
    refine (congrArg rc (IrrGL.of_eq_of.2 ⟨e.trans φ⟩)).trans h1
  | succ s ih =>
    intro n N hn σ τ e
    obtain rfl : n = N 0 + ∑ i : Fin s, N i.succ := hn.symm.trans (Fin.sum_univ_succ N)
    obtain ⟨e⟩ := e
    obtain ⟨E₁⟩ := MultiIrr.nonempty_prod₂_equiv_multiProd_succ (k := w.adicCompletion E) N hn fun i => (σ i).ρ
    have hs : IsSmooth (multiProd (stdBlocks (fun i : Fin s => N i.succ) rfl) fun i : Fin s => (σ i.succ).ρ) :=
      isSmooth_parInd _ _
    have hi := GlobalTheory.T.isIrreducible_second_factor_of_irreducible_product _ _ _ _ _ _ (σ 0).ρ _ τ.ρ (σ 0).smooth (σ 0).irred hs τ.irred ⟨e.trans E₁.symm⟩
    let σ' : SmIrr (GL (Fin (∑ i : Fin s, N i.succ)) (w.adicCompletion E)) := ⟨_, _, hs, hi⟩
    have h1 := L.prod (N 0) _ (ParLaws.toRep (σ 0)) (ParLaws.toRep σ') (ParLaws.toRep τ) ⟨e.trans E₁.symm⟩
    have h2 := ih (N := fun i : Fin s => N i.succ) rfl (fun i => σ i.succ) σ' ⟨.refl _⟩
    rw [List.ofFn_succ]
    exact h1.trans (congrArg _ h2)
theorem UpperTheory.V.Z.Win.Gu.prodT_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ExtraV → ProdT := by
  intro _ X E Ω _ _ _ _ _ n c N hn w σ _ τ e A h rc hrc
  obtain ⟨a, ha, ε, L⟩ := X E Ω A w h rc hrc
  exact locProd_sum L hn σ τ e
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuSpehT
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GlobalTheory.CuspRep GlobalTheory.DefiniteBC UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem segSum_nu {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (hnu : ∀ x (s : ℝ), rc (x.nu s) = (rc x).lpTw s)
    (l : List (Segment (w.adicCompletion E))) (c : ℝ) :
    segSum rc (l.map fun Γ => Γ.nu (c : ℂ)) = (segSum rc l).lpTw c := by
  simp only [segSum]
  rw [← GlobalTheory.NuShift.sumList_lpTw, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun Γ _ => ?_
  show ((rc (Γ.first.nu (c : ℂ))).lpTw _).lpChar _ = _
  rw [hnu, WD.lpTw_add, add_comm, ← WD.lpTw_add, GlobalTheory.NuShift.lpChar_lpTw]
  rfl
private theorem rec_spehQuotT {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (hrc : IsRecT h rc) (hTZ : GlobalTheory.Published.GenericUnitaryDualGL)
    (hLM : GlobalTheory.Published.StandardCosocleGL) (a d n : ℕ) (hd : ∑ _ : Fin d, a = n) (σ : LocIrr w a) (σ' : LocIrr w n)
    (hu : IsUnitarisable σ.ρ) (hg : IsGeneric σ.ρ) (hq : IsSpehQuot hd σ σ') :
    rc (cls (ParLaws.toRep σ')) =
      sumList ((List.range d).map fun k : ℕ => (rc (cls (ParLaws.toRep σ))).lpTw (((d : ℝ) - 1) / 2 - k)) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨m, δ, Δ, s, hΔ, hδu, hs, hd0, hφ⟩ := hTZ.exists_prod σ.smooth σ.irred hu hg
  have hA := GlobalTheory.T.isLanglandsQuotient_of_irreducible_unitary_segment_product _ (GlobalTheory.T.unitarisable_segment_twist_precedes_add_one_le _) a _ σ.ρ σ.irred m δ Δ s hΔ hδu hs hd0 hφ
  have hB := GlobalTheory.T.langlandsQuotient_of_speh_type_product_isL _ hLM (GlobalTheory.T.unitarisable_segment_twist_precedes_add_one_le _) (GlobalTheory.T.parabolicInduction_in_stages_product_of_products _) a _ σ.ρ m δ Δ s hΔ hδu hs hd0 hφ d n hd _ σ'.ρ σ'.irred hq
  obtain ⟨a', ha', L⟩ := hrc
  rw [L.langlands _ _ (GlobalTheory.SpehRec.isL_of_equiv hB (equivRep (ParLaws.toRep σ'))),
    L.langlands _ _ (GlobalTheory.SpehRec.isL_of_equiv hA (equivRep (ParLaws.toRep σ)))]
  simp only [segSum]
  rw [List.map_flatMap, GlobalTheory.SpehRec.sumList_flatMap]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact segSum_nu L.nu _ _
theorem UpperTheory.V.Z.Win.Gu.spehT_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ExtraV → SpehT := by
  intro H _ E Ω _ _ _ _ _ _ a d P w ρ σ _ _ hP hu hS A h rc hrc
  have L := H.litN.loc
  have hd : ∑ _ : Fin d, a = d * a := by simp
  exact rec_spehQuotT hrc (_root_.PositivityTheory.Gud.generic_unitary_dual_GL trivial L.sq L.gen L.multi L.cos) L.cos a d _ hd ρ σ hu
    (GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E a P w ρ hP)
    (GlobalTheory.DiscreteSpectrumCM.isSpehQuot_of_isSpeh hd ρ σ hS)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuIrrCaseT
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open NumberField Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep

noncomputable section

namespace GuIrrCaseTDualProof

open Matrix GlobalTheory.ContraPair

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

private def phiOp (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) : Module.End ℂ (Sm L a) :=
  act (.fin (PhiU a (Af L))) * act (.cpt (PhiK L a))

omit [NumberField L] [IsCMField L] in
private theorem barK_barK (k : Kinf L a) : barK (barK k) = k := Subtype.ext (by
  ext i j : 1
  exact star_star _)

private theorem fin_cpt (k : GL (Fin a) (Af L)) (u : Kinf L a) :
    act (.cpt u) * act (.fin k) = act (.fin k) * act (Op.cpt u : Op L a) := by
  change rt L a _ * rt L a _ = rt L a _ * rt L a _
  rw [← map_mul, ← map_mul]
  exact congrArg _ (infGL_comm _ _)

private theorem phiOp_mul (o : Op L a) : phiOp L a * act (invTOp (conjOp o)) = act (thetaOp o) * phiOp L a := by
  cases o with
  | fin k =>
    simp only [phiOp, conjOp, invTOp, thetaOp]
    rw [mul_assoc, fin_cpt, ← mul_assoc, ← mul_assoc]
    congr 1
    change finRep L a _ * finRep L a _ = finRep L a _ * finRep L a _
    rw [← map_mul, ← map_mul]
    congr 1
    change _ = PhiU a (Af L) * _ * (PhiU a (Af L))⁻¹ * _
    rw [inv_mul_cancel_right]
    rfl
  | cpt k =>
    simp only [phiOp, conjOp, invTOp, thetaOp, barK_barK]
    rw [← mul_assoc, fin_cpt, mul_assoc, mul_assoc]
    congr 1
    change cptRep L a _ * cptRep L a _ = cptRep L a _ * cptRep L a _
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  | lie X =>
    simp only [phiOp, conjOp, invTOp, thetaOp]
    have h1 := GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits (PhiK L a)) (-(Matrix.of X)ᴴ)
    have h2 := lie_rt_fin (E := L) (toL (-(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ)))
      (PhiU a (Af L))
    have e : Unitary.toUnits (PhiK L a) = PhiU a (Cinf L) := Units.ext rfl
    have e2 : (Unitary.toUnits (PhiK L a)).val * (-(Matrix.of X)ᴴ) * ((Unitary.toUnits (PhiK L a))⁻¹).val =
        -(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ) := by
      rw [e, mul_neg, neg_mul]; rfl
    rw [e2] at h1
    rw [mul_assoc, ← mul_assoc (act (Op.lie _))]
    exact (congrArg (act (.fin (PhiU a (Af L))) * ·) h1).trans ((mul_assoc _ _ _).symm.trans
      (congrArg (· * _) h2.symm))

private theorem dualIsConj_of_isCsd {π : CuspSub L a} (h : Paired π π invTOp) (hc : π.IsCsd) : DualIsConj π := by
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨T, hT⟩ := hc
  let P : Module.End ℂ π.V := π.op (.fin (PhiU a (Af L))) * π.op (.cpt (PhiK L a))
  let Q : Module.End ℂ π.V := π.op (.cpt (PhiK L a)⁻¹) * π.op (.fin (PhiU a (Af L))⁻¹)
  have f1 : ∀ k k' : GL (Fin a) (Af L), k * k' = 1 → ∀ φ, π.op (.fin k) (π.op (.fin k') φ) = φ := fun k k' e φ =>
    Subtype.ext (by
      change (finRep L a k * finRep L a k') φ.1 = φ.1
      rw [← map_mul, e, map_one]; rfl)
  have f2 : ∀ k k' : Kinf L a, k * k' = 1 → ∀ φ, π.op (.cpt k) (π.op (.cpt k') φ) = φ := fun k k' e φ =>
    Subtype.ext (by
      change (cptRep L a k * cptRep L a k') φ.1 = φ.1
      rw [← map_mul, e, map_one]; rfl)
  let Pe : π.V ≃ₗ[ℂ] π.V := LinearEquiv.ofLinearMap P Q
    (LinearMap.ext fun φ => by simp [P, Q, f1, f2]) (LinearMap.ext fun φ => by simp [P, Q, f1, f2])
  let S := Pe.trans T
  have hS : ∀ o φ, S (π.op (invTOp (conjOp o)) φ) = π.op o (S φ) := fun o φ => by
    change T _ = π.op o (T _)
    rw [← hT]
    exact congrArg T (Subtype.ext (LinearMap.congr_fun (phiOp_mul o) φ.1))
  have hS' : ∀ o φ, S.symm (π.op o φ) = π.op (invTOp (conjOp o)) (S.symm φ) := fun o φ => by
    rw [LinearEquiv.symm_apply_eq, hS, LinearEquiv.apply_symm_apply]
  refine ⟨B.flip ∘ₗ S.symm.toLinearMap, fun φ h => ?_, fun ψ h => h1 ψ fun x => ?_, fun k φ ψ => ?_, fun k φ ψ => ?_,
    fun X φ ψ => ?_⟩
  · exact (map_eq_zero_iff _ S.symm.injective).1 (h2 _ h)
  · simpa using h (S x)
  · change B _ (S.symm _) = B _ (S.symm _)
    rw [hS']; exact h3 _ _ _
  · change B _ (S.symm _) = B _ (S.symm _)
    rw [hS']; exact h4 _ _ _
  · change B _ (S.symm _) + B _ (S.symm _) = 0
    rw [hS', add_comm]; exact h5 _ _ _

end GuIrrCaseTDualProof

section
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem spehInf_one' (m : Multiset ℂ) : spehInf 1 m = m := by
  simp [spehInf]
private theorem satTot_one {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (S : Fin 1 → Multiset ℂˣ) :
    satTot w (fun _ => 1) S = S 0 := by
  simp [satTot, GlobalTheory.WeilDeligne.qPow_zero]
theorem UpperTheory.V.Z.Win.Gu.irrCaseT_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → IrrCaseT := by
  intro PH E Ω _ _ _ _ _ _ l _ ι n hn1 π hπ c a d hn P ρ m σ H hsp hsplit hun hc hd r hr hF
  subst hc
  obtain rfl : d = fun _ => 1 := funext hd
  obtain rfl : a = fun _ => n := funext fun i => by
    rw [Subsingleton.elim i 0]
    simpa using hn
  have hw : ∀ φ lam, HasWeightAt π φ lam → (P 0).HasInfChar φ (infOfWeight lam) := fun φ lam h => by
    have e := H.weight φ lam h
    rw [Fin.sum_univ_one, spehInf_one'] at e
    exact e ▸ H.inf 0 φ
  refine ⟨P 0, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, GuIrrCaseTDualProof.dualIsConj_of_isCsd (PH.toClassicalTheorems.litN.aut.gk E _ (P 0)) (H.csd 0),
    ⟨hr, hF.mono fun w ⟨S, h1, h2⟩ => ⟨S 0, h1 0, satTot_one w S ▸ h2⟩⟩, hw, fun w h => hun w h 0, fun w hs τ hτ => ?_⟩
  · obtain ⟨lam, hl⟩ := GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary E _ hn1 π hπ τ
    rw [CG.HasInfChar.infChar_eq (π := CG.mk (P 0)) (hw τ lam hl)]
    refine ⟨nodup_infOfWeight lam, fun z hz => ?_⟩
    rw [infOfWeight, Multiset.mem_map] at hz
    obtain ⟨j, -, rfl⟩ := hz
    exact ⟨lam.w j - (j : ℕ), by push_cast; ring⟩
  · obtain ⟨e₁⟩ := PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange.oneFactor E w n hn (ρ 0 w) (σ · w) (hsp 0 w)
    obtain ⟨e₂⟩ := LocUniq.isLocComp_unique (P 0) w _ _ (H.loc 0 w) hτ
    exact GlobalTheory.BaseChangeBridge.isCompAlong_of_equiv (e₁.trans e₂).toLinearEquiv
      (fun g x => LinearMap.congr_fun ((e₁.trans e₂).toIntertwiningMap.isIntertwining' g) x) τ.irred (hsplit w hs)
end
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V.Af UpperTheory.V.Af.Gu
namespace UpperTheory.V.Z.Win.Gu
theorem half_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (hR : RowT) : HalfG := halfG UpperTheory.twist_local_components_compatible (_root_.UpperTheory.V.Z.Win.Gu.polG_of_printsH_of_rT H hR)
theorem recTotT_of_printsH (H : _root_.UpperTheory.V.Af.HypothesesH') : RecTotT := recTotT (_root_.UpperTheory.V.Z.Win.Gu.prodT_alt H extraV) (_root_.UpperTheory.V.Z.Win.Gu.spehT_alt H extraV)
theorem galUnitaryT_of_printsH_of_bcSpeh_of_rT (H : _root_.UpperTheory.V.Af.HypothesesH') (hB : GlobalTheory.BcSpeh.BcSpeh) (hR : RowT) : GalUnitaryT :=
  _root_.UpperTheory.V.Z.Win.Gu.assemble_s H hB (sumFamG (_root_.UpperTheory.V.Z.Win.Gu.sumTwoG_of_printsH_gdLaws_sumAway_sumHTAt H gdLaws UpperTheory.galoisRep_direct_sum_away_from_places sumHTAt) UpperTheory.finiteSum_reduction) (_root_.UpperTheory.V.Z.Win.Gu.half_alt H hR) UpperTheory.speh_parameter_strings UpperTheory.building_component_uniqueness
    (_root_.UpperTheory.V.Z.Win.Gu.recTotT_of_printsH H) (_root_.UpperTheory.V.Z.Win.Gu.frobTotT_alt H extraV gdLaws) (UpperTheory.twistedDual_frobenius_compatibility (_root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results H.toClassicalTheorems)) (_root_.UpperTheory.satake_galois_link_of_printed_hida H) UpperTheory.satake_parameters_complex_conjugate
    (_root_.UpperTheory.V.Z.Win.Gu.irrCaseT_alt H) plainGd
theorem endShapeT' (H : _root_.UpperTheory.V.Af.HypothesesH') (hB : GlobalTheory.BcSpeh.BcSpeh) (hR : RowT) :
    type_of% (endShape_of hB (_root_.UpperTheory.satake_galois_link_of_printed_hida H) (_root_.UpperTheory.V.Z.Win.Gu.half_alt H hR) (_root_.UpperTheory.V.Z.Win.Gu.recTotT_of_printsH H) (_root_.UpperTheory.V.Z.Win.Gu.frobTotT_alt H extraV gdLaws) (frobTwT extraV gdLaws)) :=
  endShape_of hB (_root_.UpperTheory.satake_galois_link_of_printed_hida H) (_root_.UpperTheory.V.Z.Win.Gu.half_alt H hR) (_root_.UpperTheory.V.Z.Win.Gu.recTotT_of_printsH H) (_root_.UpperTheory.V.Z.Win.Gu.frobTotT_alt H extraV gdLaws) (frobTwT extraV gdLaws)
end UpperTheory.V.Z.Win.Gu
end

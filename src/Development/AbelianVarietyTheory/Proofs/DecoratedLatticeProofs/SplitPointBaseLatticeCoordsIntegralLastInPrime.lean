module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FunctionalValuesIntegralVectorsOfIntegerVectors
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointEqProdSplitComponentsMulOff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjBesselCharacterIsUnfoldingThetaFunctionOfGra
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedBesselJacobiIntegralAbsLe
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldOverFlagUnipotentThetaLift
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTranslate
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSupportSplitPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceReductionsConjOfNestedFrameStabilisers
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqUniformizerAndUnitAtPrime
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointBaseLatticeCoordsIntegralLastInPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointBaseLatticeCoordsIntegralLastInPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.SplitCoord

open GlobalTheory.FinPl


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem coord_int_last : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ (n : ℕ) (t : 𝓞 D.host.E), t ∈ P.asIdeal → ∀ (Lb : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), (∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = n → t ∣ r)) → ∀ y : Fin n → AE D, (fun r => Formalism.UG.prV (E := D.host.E) p.v (toEAf D (y r))) ∈ Formalism.UG.latS (F := D.host.F) (p.v.adicCompletion D.host.F) (intV D.host.E p.v) Lb → ∀ r, p.pr (y r) ∈ 𝒪[k] ∧ (r.1 + 1 = n → valuation k (p.pr (y r)) < 1) := by
  intro D k _ _ _ _ p P hP n t ht Lb hLb y hy
  obtain ⟨π₀, hπ₀, -, hint, -⟩ := GlobalTheory.LocMod.LevBack.exists_chart p hP

  have he : toEAf D p.e = Formalism.UG.P.afsplitEps D.host.E p.v * toEAf D p.e := by
    obtain ⟨ε, hε, hsum⟩ := p.above
    have hee : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
      rw [← hsum, add_mul, p.split.1, mul_comm (cA D p.e) p.e, p.split.2.1, add_zero]
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun w => ?_
    rw [map_sub, map_mul]
    by_cases hw : w = p.v
    · subst hw; rw [Formalism.UG.P.afsplit_prV_eps, one_mul, sub_self]
    · rw [← hee, GlobalTheory.AdForm.ChiStd.prV_toEAf_idem_mul hε hw, mul_zero, sub_zero]
  have hpe : π₀ (toEAf D p.e) = 1 := by rw [hπ₀]; exact GlobalTheory.LocMod.LevBack.pr_e p
  have heps : π₀ (Formalism.UG.P.afsplitEps D.host.E p.v) = 1 := by
    have h1 := congrArg π₀ he
    rw [map_mul, hpe, mul_one] at h1
    exact h1.symm

  let π : D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F →+* k :=
    { toFun := fun s => π₀ (Formalism.UG.P.afsplitIE p.v s)
      map_one' := heps
      map_mul' := fun a b => by
        show π₀ (Formalism.UG.P.afsplitIE p.v (a * b)) = π₀ (Formalism.UG.P.afsplitIE p.v a) * π₀ (Formalism.UG.P.afsplitIE p.v b)
        rw [map_mul (Formalism.UG.P.afsplitIE p.v), map_mul π₀]
      map_zero' := by
        show π₀ (Formalism.UG.P.afsplitIE p.v 0) = 0
        rw [map_zero (Formalism.UG.P.afsplitIE p.v), map_zero π₀]
      map_add' := fun a b => by
        show π₀ (Formalism.UG.P.afsplitIE p.v (a + b)) = π₀ (Formalism.UG.P.afsplitIE p.v a) + π₀ (Formalism.UG.P.afsplitIE p.v b)
        rw [map_add (Formalism.UG.P.afsplitIE p.v), map_add π₀] }
  have hπ : ∀ z, π (Formalism.UG.prV (E := D.host.E) p.v z) = π₀ z := fun z => by
    change π₀ (Formalism.UG.P.afsplitIE p.v _) = _
    rw [Formalism.UG.P.afsplit_decomp, map_mul, heps, one_mul]

  have hV : intV D.host.E p.v ≤ (𝒪[k]).comap π := by
    refine Subring.closure_le.2 ?_
    rintro s (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · change π (Formalism.UG.prV (E := D.host.E) p.v ((x : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F))) ∈ 𝒪[k]
      rw [hπ]
      exact hint ⟨_, Subring.subset_closure (Or.inl ⟨x, rfl⟩)⟩
    · change π₀ ((1 : D.host.E) ⊗ₜ[D.host.F] Formalism.UG.P.afsplitI p.v (x : p.v.adicCompletion D.host.F)) ∈ 𝒪[k]
      exact hint ⟨_, Subring.subset_closure (Or.inr ⟨⟨_, Formalism.UG.P.afsplitI_mem_intAd p.v _ x.2⟩, rfl⟩)⟩

  have key : ∀ w ∈ Formalism.UG.latS (F := D.host.F) (p.v.adicCompletion D.host.F) (intV D.host.E p.v) Lb,
      ∀ r : Fin n, π (w r) ∈ 𝒪[k] ∧ (r.1 + 1 = n → valuation k (π (w r)) < 1) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hxL, rfl⟩ := hx
      intro r
      obtain ⟨ρ, hρ, hlast⟩ := (hLb x).1 hxL r
      have h0 : π (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (x r)) = p.pr (incA D (ρ : D.host.E)) := by
        rw [hρ]
        change π (Formalism.UG.prV (E := D.host.E) p.v ((ρ : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F))) = _
        rw [hπ, ← hπ₀]
        rfl
      refine ⟨?_, fun hr => ?_⟩
      · change π (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (x r)) ∈ 𝒪[k]
        have hq : toEAf D (incA D (ρ : D.host.E)) =
            (ρ : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
          first | rfl | simp [toEAf, finPart, incA]
        have hm : toEAf D (incA D (ρ : D.host.E)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
          rw [hq]; exact Subring.subset_closure (Or.inl ⟨⟨(ρ : D.host.E), ρ, rfl⟩, rfl⟩)
        rw [h0, ← hπ₀]
        exact hint ⟨_, hm⟩
      · change valuation k (π (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (x r))) < 1
        rw [h0, ← GlobalTheory.LocMod.LevBack.pr_lt p hP]
        obtain ⟨c, hc⟩ := hlast hr
        rw [hc]; exact Ideal.mul_mem_right _ _ ht
    | zero =>
      intro r
      simp
    | add a b _ _ ha hb =>
      intro r
      refine ⟨?_, fun hr => ?_⟩
      · rw [Pi.add_apply, map_add (f := _)]; exact add_mem (ha r).1 (hb r).1
      · rw [Pi.add_apply, map_add (f := _)]; exact Valuation.map_add_lt _ ((ha r).2 hr) ((hb r).2 hr)
    | smul s a _ ha =>
      intro r
      have hs : π s ∈ 𝒪[k] := hV s.2
      have e1 : π ((s • a) r) = π s * π (a r) := by
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]
      refine ⟨?_, fun hr => ?_⟩
      · rw [e1]; exact mul_mem hs (ha r).1
      · rw [e1, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).1 hs)) ((ha r).2 hr)
  intro r
  have h := key _ hy r
  rw [hπ, hπ₀] at h
  exact h

end GlobalTheory.LocMod.SplitCoord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointBaseLatticeCoordsIntegralLastInPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPoint_baseLattice_coords_integral_last_in_prime : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ (n : ℕ) (t : 𝓞 D.host.E), t ∈ P.asIdeal → ∀ (Lb : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), (∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = n → t ∣ r)) → ∀ y : Fin n → AE D, (fun r => Formalism.UG.prV (E := D.host.E) p.v (toEAf D (y r))) ∈ Formalism.UG.latS (F := D.host.F) (p.v.adicCompletion D.host.F) (intV D.host.E p.v) Lb → ∀ r, p.pr (y r) ∈ 𝒪[k] ∧ (r.1 + 1 = n → valuation k (p.pr (y r)) < 1) := by
  first | exact @GlobalTheory.LocMod.SplitCoord.coord_int_last | exact GlobalTheory.LocMod.SplitCoord.coord_int_last | (intros; apply GlobalTheory.LocMod.SplitCoord.coord_int_last <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodThetaLiftUnfolding
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodThetaLiftEqIntegralKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodThetaLiftEqIntegralKernel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem enorm_fl_le {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (W : HSp D)
    (v : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (Th : GA D V → ℂ) (hTh : ∀ n, ‖Th n‖ ≤ 1)
    (x : Mx D W.rank ρ) (Ψ : WO V W → ℂ) :
    ‖fl ψ d W v vb vU Th x Ψ‖ₑ ≤
      ∫⁻ u, ∫⁻ b in vb.𝓕, ‖d.mixS W ψ v.μ v.𝓕 Ψ (x ⬝ u.1.1) (x ⬝ b)‖ₑ ∂vb.μ ∂vU.ν := by
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun u => ?_)
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun b => ?_)
  simp only [flFun]
  rw [enorm_mul]
  refine mul_le_of_le_one_left' ?_
  rw [← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_one.2 (hTh _)

theorem liftS_mul {D : D7} {V W : HSp D} (om : Om V W) (μ : Measure (GA D W)) (𝓕 : Set (GA D W)) (G : GA D W → ℂ)
    (Φ : WO V W → ℂ) (n g : GA D V) : liftS om μ 𝓕 G Φ (n * g) = liftS om μ 𝓕 G (om (g, 1) Φ) n := by
  have e : ∀ h, thetaKO om (n * g) h Φ = thetaKO om n h (om (g, 1) Φ) := fun h => by
    simp only [thetaKO]
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [liftS, Formalism.IndefR.Lift.liftInt, e]

theorem besPer_lift_eq_integral_kerBF : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → ∀ 𝓑 : Set (GA D J.W), IsFundamentalDomain (GQ J.W ⊓ jacGrp J.d : Subgroup (GA D J.W)) 𝓑 s.vW.μ → IntegrableOn (kerBF s φ G Φ) 𝓑 s.vW.μ ∧ B.per ψ φ (s.lift G Φ) = ∫ h in 𝓑, kerBF s φ G Φ h ∂s.vW.μ := by
  intro D hD ψ ρ B J s φ G Φ hφ hG hΦ 𝓑 h𝓑
  obtain ⟨om', hom'⟩ := (hD ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  obtain ⟨hb, hg, hx, hR, -, -⟩ := GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d
  have hemb : Continuous (embA B.d B.o) :=
    (GlobalTheory.T.unfolding_base_point_fourierJacobi_group D B.V B.V₀ ρ B.d).2.2.2.2.1.comp
      (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
  have hTh := GlobalTheory.T.conjBesselCharacter_isUnfoldingThetaFunction_of_gram_zero D ψ s.weil.std ρ B J.W J.d.e hg
  have h𝓑' := h𝓑
  rw [← hR] at h𝓑'
  set Th : GA D B.V → ℂ := fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) with hThd
  have hn : ∀ n, ‖Th n‖ ≤ 1 := fun n => by
    simp only [hThd, norm_star, psiBes, psiE]
    exact (s.weil.std.1.2.1 _).le
  have hfl : ∀ p, fl ψ B.d J.W s.vS s.vT s.vU Th (rat J.d.e) (s.om p Φ) = flatBF s (s.om p Φ) 0 := fun p => by
    rw [← hx]
    exact GlobalTheory.T.flagUnipotentUnfolding_besselFourierJacobi_eq D ψ ρ B J s _ (s.weil.om_pres p Φ hΦ)
  have hom : ∀ g h, s.om (1, h) (s.om (g, 1) Φ) = s.om (g, h) Φ := fun g h => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

  have h1 : ∀ g, ∫ n in B.vN.𝓝, Th n.1 * s.lift G Φ (n.1 * g) ∂B.vN.ν =
      ∫ h in 𝓑, G h * flatBF s (s.om (g, h) Φ) 0 ∂s.vW.μ := fun g => by
    have := (GlobalTheory.T.unfold_over_flagUnipotent_thetaLift D hD ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS B.vN s.vT s.vU s.vW J.d.e Th
      hb hTh G (s.om (g, 1) Φ) hG (s.weil.om_pres _ Φ hΦ) 𝓑 h𝓑').2
    simp only [hom, hfl] at this
    simp only [Step.lift, liftS_mul]
    exact this

  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D B.A
  obtain ⟨j1, j2, j3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W
  haveI : BorelSpace (GA D B.A) := ⟨rfl⟩
  haveI : BorelSpace (GA D J.W) := ⟨rfl⟩
  haveI := B.vA.haar
  haveI := s.vW.haar
  obtain ⟨hc, hd, -⟩ := GlobalTheory.T.rational_unitary_subgroup_countable_discrete_fundDomain D B.A (GQ B.A) le_rfl

  set f : GA D B.A → GA D J.W → ℂ := fun h₀ h => φ h₀ * (G h * flatBF s (s.om (embA B.d B.o h₀, h) Φ) 0) with hf
  have hcont : Continuous (Function.uncurry f) := by
    have h2 := GlobalTheory.T.continuous_flatMap_weilRepresentation_joint D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil s.vU J.d.e hb.1 Φ hΦ
    rw [← hx] at h2
    have h3 : Continuous fun p : GA D B.A × GA D J.W =>
        (((embA B.d B.o p.1, p.2), yZero B.V₀ ρ (vecB B.o B.ζ), 0) :
          (GA D B.V × GA D J.W) × Mx D B.V₀.rank ρ × WO B.V₀ J.W₀) :=
      ((hemb.comp continuous_fst).prodMk continuous_snd).prodMk continuous_const
    have h4 := h2.comp h3
    simp only [Function.comp_def] at h4
    have h5 : Continuous fun p : GA D B.A × GA D J.W => flatBF s (s.om (embA B.d B.o p.1, p.2) Φ) 0 := by
      simp only [flatBF, flat]
      exact h4
    exact (hφ.2.comp continuous_fst).mul ((hG.2.1.comp continuous_snd).mul h5)
  have hinv := (GlobalTheory.T.unfoldedBesselJacobiKernel_laws D ψ ρ B J s om' hom' φ G Φ hφ hG hΦ).2.2.1
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.unfolded_besselJacobi_integral_abs_le D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS s.vT s.vU s.vW J.d.e
    hb G Φ hG hΦ 𝓑 h𝓑'
  have hint : Integrable (Function.uncurry f) ((B.vA.μ.restrict B.vA.𝓕).prod (s.vW.μ.restrict 𝓑)) := by
    refine GlobalTheory.fubini_compact_quotient (GA D B.A) B.vA.μ (GQ B.A) hc hd B.cpt B.vA.𝓕 B.vA.fund (GA D J.W) _ f
      hcont.measurable (fun γ hγ h x => by simp only [hf, hφ.1 γ hγ, hinv γ hγ]) fun K hK => ?_
    have hq : Continuous fun h₀ => ‖φ h₀‖ * (C * height B.V (embA B.d B.o h₀) ^ A) :=
      hφ.2.norm.mul (continuous_const.mul (((continuous_height B.V).comp hemb).pow A))
    obtain ⟨M, hM⟩ := hK.bddAbove_image hq.continuousOn
    refine ⟨M.toNNReal, fun h₀ hh => ?_⟩
    calc ∫⁻ h in 𝓑, ‖f h₀ h‖ₑ ∂s.vW.μ
        = ‖φ h₀‖ₑ * ∫⁻ h in 𝓑, ‖G h‖ₑ * ‖flatBF s (s.om (embA B.d B.o h₀, h) Φ) 0‖ₑ ∂s.vW.μ := by
          rw [← lintegral_const_mul' _ _ enorm_ne_top]
          simp only [hf, enorm_mul]
      _ ≤ ‖φ h₀‖ₑ * ENNReal.ofReal (C * height B.V (embA B.d B.o h₀) ^ A) := by
          refine mul_le_mul_right (le_trans (lintegral_mono fun h => mul_le_mul_right ?_ _) (hC _)) _
          rw [← hfl]
          exact enorm_fl_le ψ B.d J.W s.vS s.vT s.vU Th hn _ _
      _ = ENNReal.ofReal (‖φ h₀‖ * (C * height B.V (embA B.d B.o h₀) ^ A)) := by
          rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm]
      _ ≤ M.toNNReal := ENNReal.ofReal_le_ofReal (hM ⟨h₀, hh, rfl⟩)
  have hker : kerBF s φ G Φ = fun h => ∫ h₀ in B.vA.𝓕, f h₀ h ∂B.vA.μ := by
    funext h
    simp only [kerBF, hf]
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_left_comm _ _ _)
  rw [hker]
  refine ⟨hint.integral_prod_right, ?_⟩
  rw [← integral_integral_swap hint]
  simp only [BesLev.per, besPer, besFun, hf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h₀ => ?_)
  simp only
  rw [integral_const_mul, ← h1, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  simp only [hThd]
  ring

end GlobalTheory.Unf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodThetaLiftEqIntegralKernelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriod_thetaLift_eq_integral_kernel : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → ∀ 𝓑 : Set (GA D J.W), IsFundamentalDomain (GQ J.W ⊓ jacGrp J.d : Subgroup (GA D J.W)) 𝓑 s.vW.μ → IntegrableOn (kerBF s φ G Φ) 𝓑 s.vW.μ ∧ B.per ψ φ (s.lift G Φ) = ∫ h in 𝓑, kerBF s φ G Φ h ∂s.vW.μ := by
  first | exact @GlobalTheory.Unf.besPer_lift_eq_integral_kerBF | exact GlobalTheory.Unf.besPer_lift_eq_integral_kerBF | (intros; apply GlobalTheory.Unf.besPer_lift_eq_integral_kerBF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodThetaLiftUnfolding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
noncomputable section

namespace GlobalTheory.UnfBessel

variable {D : D7}

def zeroSp (D : D7) : HSp D where
  V := Fin 0 → D.host.E
  hT := 0
  herm := ⟨fun _ _ => by simp⟩
  nondeg := ⟨fun x _ => Subsingleton.elim x 0, fun x _ => Subsingleton.elim x 0⟩
  rank := 0
  rank_eq := by simp
  frame := Pi.basisFun D.host.E (Fin 0)
  sig := fun _ => (0, 0)
  L0 := ⊥
  standardTuple_isLattice := Submodule.IsLattice.of_fg D.host.E Submodule.fg_bot
  baseLattice_isUnimodular := Subsingleton.elim _ _

def orthZero (S : HSp D) : OrthDec S S (zeroSp D) where
  iA := 1
  iB := 0
  isoA := by simp
  isoB := by ext i; exact Fin.elim0 (show Fin 0 from i)
  orth := by ext i; exact Fin.elim0 (show Fin 0 from i)
  rank_add := rfl

theorem unfBF_of_parts
    (hcpt : ∀ (D : D7) (ρ : ℕ) (J : JacLev D ρ) (K : GA D J.W → ℂ), Continuous K →
      (∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ h, K (γ * h) = K h) →
        ∀ h, AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 fun h' n => K (n.1 * J.d.emb0 h' * h))
    (hfub : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ)
      (s : StepBF ψ B J) (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G →
        IsThetaFunO ψ B.V J.W Φ → ∀ 𝓑 : Set (GA D J.W),
          IsFundamentalDomain (GQ J.W ⊓ jacGrp J.d : Subgroup (GA D J.W)) 𝓑 s.vW.μ →
            IntegrableOn (kerBF s φ G Φ) 𝓑 s.vW.μ ∧ B.per ψ φ (s.lift G Φ) = ∫ h in 𝓑, kerBF s φ G Φ h ∂s.vW.μ) :
    ∀ D : D7, Descent D → UnfBF D := by
  intro D hD ψ ρ B J s φ G Φ hφ hG hΦ
  obtain ⟨om', hom'⟩ := (hD ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  obtain ⟨hcont, hinv, -, hval⟩ := GlobalTheory.T.unfoldedBesselJacobiKernel_laws D ψ ρ B J s om' hom' φ G Φ hφ hG hΦ
  obtain ⟨hΓc, hΓd, hfd⟩ := GlobalTheory.T.rational_unitary_subgroup_countable_discrete_fundDomain D J.W (GQ J.W ⊓ jacGrp J.d) inf_le_left
  haveI := s.vW.haar
  obtain ⟨𝓑, h𝓑⟩ := hfd s.vW.μ s.vW.haar
  obtain ⟨hint, hper⟩ := hfub D hD ψ ρ B J s φ G Φ hφ hG hΦ 𝓑 h𝓑
  obtain ⟨-, -, -, -, hemb, hrat⟩ := GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d
  obtain ⟨-, -, -, -, hconj, hinj, -⟩ := GlobalTheory.MixPer.flag_jacobi_structure D J.W J.W₀ ρ J.d
  have hclN := (GlobalTheory.T.flag_subgroups_closed_normal_cocompact' D J.W J.W₀ ρ J.d).1
  obtain ⟨⟨hRcl, hRhaar⟩, -⟩ :=
    GlobalTheory.T.fourierJacobi_bessel_groups_closed_haar_product D J.W J.W₀ J.W₀ (zeroSp D) ρ J.d (orthZero J.W₀) J.vN.ν J.vN.𝓝 J.vN.unit
  obtain ⟨hνh, h𝓝, -⟩ := J.vN.unit
  have hμR : (semiMeas (flagN J.d) J.d.emb0 J.v0.μ J.vN.ν).IsHaarMeasure := hRhaar J.v0.μ J.v0.haar
  obtain ⟨𝓡, h𝓡, hsem⟩ := GlobalTheory.T.semidirect_haar_measure_fundamental_domain D J.W J.W₀ (flagN J.d) J.d.emb0 hemb hclN hconj hinj hrat J.v0 J.vN.ν J.vN.𝓝
    hνh h𝓝 hμR
  have hK : Measurable (kerBF s φ G Φ) := hcont.measurable
  have hmeas : ∀ h, Measurable fun g => kerBF s φ G Φ (g * h) := fun h =>
    (hcont.comp (continuous_mul_const h)).measurable
  have key := GlobalTheory.T.integral_quotient_eq_mean_intermediate_subgroup (GA D J.W) s.vW.μ (jacGrp J.d) (GQ J.W ⊓ jacGrp J.d) inf_le_right hRcl hΓc hΓd J.μR hμR 𝓡 𝓑
    h𝓡 h𝓑 (kerBF s φ G Φ) hK hinv hint
    (fun h => ((hsem (fun g => kerBF s φ G Φ (g * h)) (hmeas h)).1).2 (hcpt D ρ J _ hcont hinv h))
  have hfun : (fun h => ∫ r in 𝓡, kerBF s φ G Φ ((r : GA D J.W) * h) ∂J.μR) =
      fun h => J.perAll ψ B s.om₀ φ (rTrans h G) (flatBF s (s.om (1, h) Φ)) := by
    funext h
    refine ((hsem (fun g => kerBF s φ G Φ (g * h)) (hmeas h)).2 (hcpt D ρ J _ hcont hinv h)).trans ?_
    simp only [JacLev.perAll, fjAll]
    refine congrArg _ (funext fun h' => congrArg _ (funext fun n => ?_))
    exact hval h h' n
  rw [hfun, ← hper] at key
  exact key

theorem unfBF : ∀ D : D7, Descent D → UnfBF D :=
  unfBF_of_parts GlobalTheory.T.fourierJacobi_invariant_function_integrable GlobalTheory.T.besselPeriod_thetaLift_eq_integral_kernel

end GlobalTheory.UnfBessel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodThetaLiftUnfoldingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriod_thetaLift_unfolding : ∀ D : D7, Descent D → UnfBF D := by
  first | exact @GlobalTheory.UnfBessel.unfBF | exact GlobalTheory.UnfBessel.unfBF | (intros; apply GlobalTheory.UnfBessel.unfBF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRedIffIsPat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevZero

theorem exists_red_iff_isPat : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt G.q.e PP → ∀ g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP), (∃ x, GlobalTheory.LevZero.Red G PP x g) ↔ GlobalTheory.SymRes.IsPat D.R.rS D.R.k g := by
  intro D c v G PP hidem g
  obtain ⟨π', h1, h2, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D G.k G.q PP hidem
  have hr : D.R.r = D.R.k + (G.s + 1) := by
    have := G.hs
    unfold Ranks.r
    omega
  have hρ : D.R.rS = G.S.ρ := by
    have := G.hs
    have := G.S.odd
    unfold Ranks.rS
    omega
  let π : 𝓞 D.host.E →+* G.k :=
    (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).comp (oToS D.host.F D.host.E)
  have hπ : ∀ z : 𝓞 D.host.E, π z = (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) := fun z =>
    h1 (incA D (z : D.host.E))
  have h : GlobalTheory.FunObj.Comparison₂.IsRed (Ideal.Quotient.mk PP.asIdeal) π :=
    ⟨h2.field, fun z => h2.int _, fun z => (iff_of_eq (congrArg (· = 0) (resS_oToS (F := D.host.F) PP z).symm)).trans (h2.ker _)⟩
  have := GlobalTheory.SymRes.exists_red_iff_isPat PP.asIdeal π h hr G.S g
  simp only [hπ] at this
  rw [hρ]
  exact this

end GlobalTheory.LevZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryClassRelation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

noncomputable section

namespace GlobalTheory.FamTraceChiCol

theorem colLam_ne_zero {D : D7} {u : D.what₂.Word} (T : Formalism.L2.Forms.Forms0 D u)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F))
    (g : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : colLam T v g ≠ 0 := by
  unfold colLam
  split_ifs with h
  · simp only [Formalism.L2.Forms.lamJ, Finset.range_zero, Finset.prod_empty, mul_one]
    intro h0
    have e := (T.gl.psi0 h.choose v h.choose_spec).map_add_eq_mul
      (∑ x : Fin (D.R.N 0), ∑ y : Fin (D.R.N 0), if (x : ℕ) + 1 = y ∧ (y : ℕ) < D.R.k ∧ (y : ℕ) ≠ D.R.k then
        (Formalism.L2.Forms.redM D.host.F v (T.gl.mat h.choose v h.choose_spec (T.glev0.fr h.choose v h.choose_spec)
          (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) x y else 0)
      (-(∑ x : Fin (D.R.N 0), ∑ y : Fin (D.R.N 0), if (x : ℕ) + 1 = y ∧ (y : ℕ) < D.R.k ∧ (y : ℕ) ≠ D.R.k then
        (Formalism.L2.Forms.redM D.host.F v (T.gl.mat h.choose v h.choose_spec (T.glev0.fr h.choose v h.choose_spec)
          (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) g))) x y else 0))
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at e
    exact one_ne_zero e
  · exact one_ne_zero

theorem mem_type_prod_iff {D : D7} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)) :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ↔ ∃ j : Fin 2, (D.host.g j : 𝓞 D.host.F) ∈ v.asIdeal := by
  rw [Nat.cast_mul, v.isPrime.mul_mem_iff_mem_or_mem, Fin.exists_fin_two]

end GlobalTheory.FamTraceChiCol

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceMemLatticeCompletionIffParts
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceMemLatticeCompletionIffParts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SplitParts

theorem mem_latV_iff_parts : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (y : Fin S.rank → AE D), (∀ r, y r ∈ GlobalTheory.FinPl.idAt D (· = q.v)) → (y ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ (fun r => q.e * y r) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ∧ (fun r => cA D q.e * y r) ∈ GlobalTheory.FinPl.latV S L (· = q.v)) := by
  intro D k _ _ _ _ q S L y hy
  have he : finPart D q.e ∈ intAE D := GlobalTheory.UpMem.finPart_e_int q
  have hce : finPart D (cA D q.e) ∈ intAE D := (GlobalTheory.FinPl.FrameLat.cA_int_iff q.e).2 he
  constructor
  · intro h
    exact ⟨GlobalTheory.FinPl.LatIndHalf.mul_mem_latV he h, GlobalTheory.FinPl.LatIndHalf.mul_mem_latV hce h⟩
  · rintro ⟨h1, h2⟩
    have e : y = (fun r => q.e * y r) + (fun r => cA D q.e * y r) := by
      funext r
      rw [Pi.add_apply, ← add_mul, (GlobalTheory.FinPl.FrameLat.idem_iff q (y r)).1 (hy r)]
    rw [e]
    exact add_mem h1 h2

end GlobalTheory.FinPl.SplitParts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceMemLatticeCompletionIffPartsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_mem_latticeCompletion_iff_parts : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (y : Fin S.rank → AE D), (∀ r, y r ∈ GlobalTheory.FinPl.idAt D (· = q.v)) → (y ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ (fun r => q.e * y r) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ∧ (fun r => cA D q.e * y r) ∈ GlobalTheory.FinPl.latV S L (· = q.v)) := by
  first | exact @GlobalTheory.FinPl.SplitParts.mem_latV_iff_parts | exact GlobalTheory.FinPl.SplitParts.mem_latV_iff_parts | (intros; apply GlobalTheory.FinPl.SplitParts.mem_latV_iff_parts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StarCharacterSquareEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChrMatch

variable {D : D7}

theorem suppAt_conj (e : AE D) (V : HSp D) (a n : GA D V) (hn : Formalism.L2.Theta.SuppAt e V n) :
    Formalism.L2.Theta.SuppAt e V (a * n * a⁻¹) := by
  have h1 : Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1 =
      Formalism.L2.Theta.mt V a * (Formalism.L2.Theta.mt V n - 1) * Formalism.L2.Theta.mt V a⁻¹ := by
    rw [mt_mul, mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mt_mul_inv]
  have h2 : (e + cA D e) • (Formalism.L2.Theta.mt V n - 1) = Formalism.L2.Theta.mt V n - 1 := by
    ext i j; exact hn i j
  intro i j
  have h3 : (e + cA D e) • (Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1) = Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1 := by
    rw [h1, ← Matrix.smul_mul, ← Matrix.mul_smul, h2]
  exact congrFun (congrFun h3 i) j

theorem levChi_mul (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {k k' : GA D V}
    (hk : k ∈ levS V β L) (hk' : k' ∈ levS V β L) : levChi V β L (k * k') = levChi V β L k * levChi V β L k' := by
  have := (levChar D.sp.cm V.gram β L).map_mul ⟨finE V k, hk.2⟩ ⟨finE V k', hk'.2⟩
  unfold levChi
  rw [map_mul, ← Units.val_mul]
  exact congrArg Units.val this

theorem levChi_of_red_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (hs : L.s = 0)
    (hQ : L.Q = ∅) {k : GA D V} (hk : ∀ PP ∈ L.Pg, redFn β PP (finE V k) = 1) : levChi V β L k = 1 := by
  have h1 : rTup β L (finE V k) = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 (finE V k)) = 1
    rw [hk PP.1 PP.2]; exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levChi levFn
  rw [h1, blockDiagonalExtendByOnePrimeField_one, hs, hQ]
  simp

end GlobalTheory.ChrMatch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPrimeMemPl
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Imports
namespace GlobalTheory.ExistsPrimeMem

theorem exists_prime_mem {A : Type} [inst : CommRing A] (P : Ideal A) (hP : Ideal.IsPrime P) :
    ∀ (n : ℕ), n ≠ (0 : ℕ) → (↑n : A) ∈ P → ∃ (ℓ : ℕ), Nat.Prime ℓ ∧ (↑ℓ : A) ∈ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hnP
    by_cases h1 : n = 1
    · subst h1
      exact absurd ((Ideal.eq_top_iff_one P).2 (by simpa using hnP)) hP.ne_top
    · have hp := Nat.minFac_prime h1
      have hpos : 0 < n := Nat.pos_of_ne_zero hn
      have hsplit : ((n : ℕ) : A) = (n.minFac : A) * ((n / n.minFac : ℕ) : A) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.minFac_dvd n)]
      rw [hsplit] at hnP
      rcases hP.mem_or_mem hnP with h | h
      · exact ⟨n.minFac, hp, h⟩
      · exact ih (n / n.minFac) (Nat.div_lt_self hpos hp.one_lt)
          (Nat.div_pos (Nat.minFac_le hpos) (Nat.minFac_pos n)).ne' h

end GlobalTheory.ExistsPrimeMem
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XGeoPlace

theorem exists_prime_mem {A : Type} [CommRing A] (P : Ideal A) (hP : P.IsPrime) (n : ℕ) (hn : n ≠ 0)
    (h : (n : A) ∈ P) : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : A) ∈ P :=
  _root_.GlobalTheory.ExistsPrimeMem.exists_prime_mem P hP n hn h

theorem exists_prime_mem_pl {E : Type} [Field E] [NumberField E] (PP : HeightOneSpectrum (𝓞 E)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 E) ∈ PP.asIdeal :=
  exists_prime_mem PP.asIdeal PP.isPrime _ (fun h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) (Ideal.absNorm_mem _)

end GlobalTheory.XGeoPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsIntegralMulVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XGeoStd

theorem isIntegral_mulVec {E : Type} [Field E] {m n : ℕ} (M : Matrix (Fin m) (Fin n) E)
    (hM : ∀ i j, IsIntegral ℤ (M i j)) (x : Fin n → E) (hx : ∀ k, IsIntegral ℤ (x k)) (k : Fin m) :
    IsIntegral ℤ ((M *ᵥ x) k) := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subalgebra.sum_mem (integralClosure ℤ E) fun l _ => (hM k l).mul (hx l)

theorem isIntegral_ite {E : Type} [Field E] (p : Prop) [Decidable p] :
    IsIntegral ℤ (if p then (1 : E) else 0) := by
  split_ifs
  · exact isIntegral_one
  · exact isIntegral_zero

theorem orthAt_oTop : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} (hI : I.Ok) (n : ℕ) (h : n = (I.rec7 l Z).R.m) (x : GlobalTheory.FinPl.Pl (I.rec7 l Z)), GlobalTheory.FinPl.OrthAt (GlobalTheory.XGeoStd.oTop l Z hI n h) (GlobalTheory.PlaceModel.latFrame ((I.rec7 l Z).sp.X n)) (GlobalTheory.PlaceModel.latFrame (I.rec7 l Z).sp.X') (GlobalTheory.PlaceModel.latFrame (GlobalTheory.XGeoStd.lineZ (I.rec7 l Z))) x := by
  intro B X I l Z hI n h x
  subst h
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  have hS : ∀ y, y ∈ GlobalTheory.PlaceModel.latFrame ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) ↔ ∀ k, IsIntegral ℤ (y k) := fun y => by
    rw [← SetLike.mem_coe, GlobalTheory.AdForm.PinInhab.lat_X hI]; rfl
  have hA : ∀ y, y ∈ GlobalTheory.PlaceModel.latFrame (I.rec7 l Z).sp.X' ↔ ∀ k, IsIntegral ℤ (y k) := fun y => by
    rw [← SetLike.mem_coe, GlobalTheory.AdForm.VacStd.coe_latFrame_of_eq _ hs _ h2]; rfl
  have hB : ∀ y, y ∈ GlobalTheory.PlaceModel.latFrame (lineZ (I.rec7 l Z)) ↔ ∀ k, IsIntegral ℤ (y k) := fun y => by
    rw [← SetLike.mem_coe, GlobalTheory.AdForm.VacStd.coe_latFrame_of_eq _ Examples₂.star_isIntegral 1 rfl]; rfl
  have ho : oTop l Z hI _ rfl = GlobalTheory.AdForm.LiveModel.topDec (GlobalTheory.AdForm.PinInhab.gram_X hI _) (gram_X' hI) := rfl
  rw [ho]
  set o := GlobalTheory.AdForm.LiveModel.topDec (GlobalTheory.AdForm.PinInhab.gram_X (l := l) (Z := Z) hI (I.rec7 l Z).R.m) (gram_X' hI)
  have iA_int : ∀ i j, IsIntegral ℤ (o.iA i j) := fun i j => by
    simp only [o, GlobalTheory.AdForm.LiveModel.topDec, Matrix.of_apply]; exact isIntegral_ite _
  have iB_int : ∀ i j, IsIntegral ℤ (o.iB i j) := fun i j => by
    simp only [o, GlobalTheory.AdForm.LiveModel.topDec, Matrix.of_apply]; exact isIntegral_ite _
  have qA_eq : o.qA = o.iAᴴ := by
    rw [OrthDec.qA, gram_X' hI, GlobalTheory.AdForm.PinInhab.gram_X hI, inv_one, Matrix.one_mul, Matrix.mul_one]
  have qB_eq : o.qB = o.iBᴴ := by
    rw [OrthDec.qB, GlobalTheory.AdForm.PinInhab.gram_X hI, GlobalTheory.AdForm.LiveModel.gram_pos, inv_one, Matrix.one_mul, Matrix.mul_one]
  have qA_int : ∀ i j, IsIntegral ℤ (o.qA i j) := fun i j => by
    rw [qA_eq, Matrix.conjTranspose_apply]; exact hs _ (iA_int j i)
  have qB_int : ∀ i j, IsIntegral ℤ (o.qB i j) := fun i j => by
    rw [qB_eq, Matrix.conjTranspose_apply]; exact hs _ (iB_int j i)
  intro y
  constructor
  · intro hy
    refine ⟨GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.qA (fun z hz => ?_) _ hy,
      GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.qB (fun z hz => ?_) _ hy⟩
    · exact (hA _).2 (isIntegral_mulVec _ qA_int z ((hS z).1 hz))
    · exact (hB _).2 (isIntegral_mulVec _ qB_int z ((hS z).1 hz))
  · rintro ⟨hyA, hyB⟩
    have e : y = o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
      have := o.sum_eq_one
      rw [show o.jA * o.pA + o.jB * o.pB = 1 from this, Matrix.one_mulVec]
    rw [e]
    refine add_mem (GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.iA (fun z hz => ?_) _ hyA)
      (GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.iB (fun z hz => ?_) _ hyB)
    · exact (hS _).2 (isIntegral_mulVec _ iA_int z ((hA z).1 hz))
    · exact (hS _).2 (isIntegral_mulVec _ iB_int z ((hB z).1 hz))

end GlobalTheory.XGeoStd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelCharacterEqAddCharSuperdiagSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelCharacterEqAddCharSuperdiagSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

namespace GlobalTheory.SymChain.SymData.RowLam

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_sum_sum_lt {ι κ' : Type} [Fintype ι] [Fintype κ'] (f : ι → κ' → k)
    (hf : ∀ i j, valuation k (f i j) < 1) : valuation k (∑ i, ∑ j, f i j) < 1 := by
  apply Valuation.map_sum_lt _ one_ne_zero
  intro i _
  exact Valuation.map_sum_lt _ one_ne_zero (fun j _ => hf i j)

theorem psi_inv_mul_eq_one (ψ : AddChar k Circle) (ϖ : kˣ) (hψ : GlobalTheory.SplitWeil.HasConductor ψ 1)
    (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) {t : k} (ht : valuation k t < 1) :
    ψ (((ϖ⁻¹ : kˣ) : k) * t) = 1 := by
  have h1 := (hψ 1).2 (by simp)
  apply h1
  have hle : valuation k t ≤ valuation k (ϖ : k) := (hϖ t).1 ht
  rw [map_mul, map_one]
  calc valuation k ((ϖ⁻¹ : kˣ) : k) * valuation k t
      ≤ valuation k ((ϖ⁻¹ : kˣ) : k) * valuation k (ϖ : k) := by gcongr
    _ = 1 := by rw [← map_mul]; simp

end GlobalTheory.SymChain.SymData.RowLam

open GlobalTheory.SymChain.SymData.RowLam in
theorem GlobalTheory.SymChain.SymData.lam_eq_psi_superSum_of_near : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ} (S : SymData k s κ) (x : S.P.J) (M : Matrix (Fin κ) (Fin κ) k), (∀ a b, valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val (Sum.inl a) (Sum.inl b) - M a b) < 1) → (∀ i j : Fin (s + 1), j.val = i.val + 1 → valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val (Sum.inr i) (Sum.inr j)) < 1) → ((S.P.lam x : ℂˣ) : ℂ) = (S.ψ (((S.ϖ⁻¹ : kˣ) : k) * ∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then M a b else 0) : ℂ) := by
  intro k _ _ _ _ s κ S x M hM hsup
  have hS := S.sym.2 x
  have hsimple : valuation k (GlobalTheory.RootEx.simpleSum (x : GL (Fin κ ⊕ Fin (s + 1)) k)) < 1 := by
    unfold GlobalTheory.RootEx.simpleSum
    apply val_sum_sum_lt
    intro i j
    split_ifs with h
    · exact hsup i j h
    · simp
  have hdiff : valuation k (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val (x : GL (Fin κ ⊕ Fin (s + 1)) k).val.toBlocks₁₁ -
      ∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then M a b else 0) < 1 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    apply val_sum_sum_lt
    intro a b
    split_ifs with h
    · simpa [Matrix.toBlocks₁₁] using hM a b
    · simp
  have e1 := psi_inv_mul_eq_one S.ψ S.ϖ S.cond S.unif hsimple
  have e2 := psi_inv_mul_eq_one S.ψ S.ϖ S.cond S.unif hdiff
  have e3 : S.ψ (((S.ϖ⁻¹ : kˣ) : k) * GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val (x : GL (Fin κ ⊕ Fin (s + 1)) k).val.toBlocks₁₁) =
      S.ψ (((S.ϖ⁻¹ : kˣ) : k) * ∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then M a b else 0) := by
    rw [mul_sub, AddChar.map_sub_eq_div] at e2
    exact div_eq_one.mp e2
  rw [hS, e1, e3]
  simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelCharacterEqAddCharSuperdiagSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLevelCharacter_eq_addChar_superdiagSum : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ} (S : SymData k s κ) (x : S.P.J) (M : Matrix (Fin κ) (Fin κ) k), (∀ a b, valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val (Sum.inl a) (Sum.inl b) - M a b) < 1) → (∀ i j : Fin (s + 1), j.val = i.val + 1 → valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val (Sum.inr i) (Sum.inr j)) < 1) → ((S.P.lam x : ℂˣ) : ℂ) = (S.ψ (((S.ϖ⁻¹ : kˣ) : k) * ∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then M a b else 0) : ℂ) := by
  first | exact @GlobalTheory.SymChain.SymData.lam_eq_psi_superSum_of_near | exact GlobalTheory.SymChain.SymData.lam_eq_psi_superSum_of_near | (intros; apply GlobalTheory.SymChain.SymData.lam_eq_psi_superSum_of_near <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfAddCharTrivialOnHomLatticeLine
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfAddCharTrivialOnHomLatticeLine
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.InvLat

open GlobalTheory.FinPl.SuppShift

variable {D : D7}

theorem single_mul_mul_single {ρ : ℕ} (M : Mx D ρ ρ) (i : Fin ρ) :
    (Matrix.single i i 1 : Mx D ρ ρ) ⬝ (M ⬝ (Matrix.single i i 1 : Mx D ρ ρ)) = Matrix.single i i (M i i) := by
  rw [← Matrix.mul_assoc, Matrix.single_mul_mul_single, one_mul, mul_one]

theorem pairS_single {W W₀ : HSp D} {ρ : ℕ} (dW : HypDec W W₀ ρ) (i : Fin ρ) (c : AE D) (x : Mx D W.rank ρ) :
    pairS W (dW.jX ⬝ (Matrix.single i i c : Mx D ρ ρ)) x = cA D ((dW.pY ⬝ x) i i) * c := by
  have h : adj (dW.pY ⬝ x) = adj x ⬝ (gA W ⬝ dW.jX) := by
    rw [dW.pY_eq, adj_mul, adj_mul, adj_adj, adj_gA]
  rw [pairS, ← Matrix.mul_assoc (gA W), ← Matrix.mul_assoc, ← h, Matrix.trace_mul_single, op_smul_eq_mul]
  rfl


set_option maxHeartbeats 1600000 in
theorem int_of_psi_line : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : Pl D), Tame D v → IsSelfDualC V LV → IsSelfDualC W LW → MonoAt dV LV LV₀ v → MonoAt dW LW LW₀ v → ColsAt dV dW.jX LV LW v → ∀ (i : Fin ρ) (c : AE D), c - 1 ∈ idAt D (· = v) → (∀ b ∈ idAt D (· = v), dV.extY W (dW.jY ⬝ Matrix.single i i b) ∈ latO V W (LV : Set _) (LW : Set _) (· = v) → ψ (symplO V W (dV.extX W (dW.jX ⬝ Matrix.single i i c)) (dV.extY W (dW.jY ⬝ Matrix.single i i b))) = 1) → c - 1 ∈ intAt D (· = v) := by
  intro D ψ hψ V V₀ W W₀ ρ dV dW LV LV₀ LW LW₀ v _ hV hW hmV hmW hcols i c hc1 hyp
  have hU : SelfDualAt.cP (· = v) • dV.extX W (dW.jX ⬝ (Matrix.single i i c : Mx D ρ ρ)) ∈
      latO V W (LV : Set _) (LW : Set _) (· = v) := by
    refine (SelfDualAt.latO_ann_at D ψ hψ V W LV LW hV hW (· = v) _ fun k l => ?_).2 fun u hu => ?_
    · rw [Matrix.smul_apply, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (eps_idAt v)
    have hux := LatMem.latO_mxAt hu
    have hfixu : SelfDualAt.cP (· = v) • u = u := by
      ext k l
      rw [Matrix.smul_apply, Algebra.smul_def]
      exact eps_mul (hux k l)
    have hπ := sandwich_latO hV hW (dW.jY ⬝ (Matrix.single i i 1 : Mx D ρ ρ) ⬝ dW.pY) (fun z hz => by
        rw [← Matrix.mulVec_mulVec, single_mulVec', one_mul]
        exact ((hmW z).1 hz).2.1 i)
      (dV.jY ⬝ (Matrix.single i i 1 : Mx D ρ ρ) ⬝ dV.pY) (fun z hz => by
        rw [← Matrix.mulVec_mulVec, single_mulVec', one_mul]
        exact ((hmV z).1 hz).2.1 i) hu
    have e : dW.jY ⬝ (Matrix.single i i 1 : Mx D ρ ρ) ⬝ dW.pY ⬝ (u ⬝ (dV.jY ⬝ (Matrix.single i i 1 : Mx D ρ ρ) ⬝ dV.pY)) =
        dV.extY W (dW.jY ⬝ (Matrix.single i i ((dW.pY ⬝ (u ⬝ dV.jY)) i i) : Mx D ρ ρ)) := by
      rw [HypDec.extY_apply, ← single_mul_mul_single]
      simp only [Matrix.mul_assoc]
    rw [e] at hπ
    have h1 := hyp _ (mxAt_mul_left dW.pY (mxAt_mul_right hux dV.jY) i i) hπ
    rw [symplO_eq, hO_extX, pairS_single, HypDec.extY_apply, Matrix.mul_assoc, dV.pY_jY, Matrix.mul_one,
      ← Matrix.mul_assoc dW.pY dW.jY, dW.pY_jY, Matrix.one_mul, Matrix.single_apply_same] at h1
    rw [← SelfDualAt.symplO_smul_swap, hfixu, symplO_eq, hO_extX, pairS_single]
    exact h1
  have hint : finPart D c ∈ intAE D := by
    refine int_of_stable dV hV hmV i hc1 fun a ha => ?_
    have ha' := idAt_of_colMul dV ha
    have h := LatMem.latO_maps hV hU ha
    have e : (SelfDualAt.cP (· = v) • dV.extX W (dW.jX ⬝ (Matrix.single i i c : Mx D ρ ρ))) *ᵥ colMul dV.jX i a =
        colMul dW.jX i (c * a) := by
      have e0 : SelfDualAt.cP (· = v) • dV.extX W (dW.jX ⬝ (Matrix.single i i c : Mx D ρ ρ)) =
          eps v • dV.extX W (dW.jX ⬝ (Matrix.single i i c : Mx D ρ ρ)) := by
        ext k l
        rw [Matrix.smul_apply, Algebra.smul_def]
        rfl
      rw [e0, Matrix.smul_mulVec, HypDec.extX_apply, ← Matrix.mulVec_mulVec, single_mulVec', pX_colMul,
        ← colMul_mul, eps_mul (Ideal.mul_mem_left _ _ ha')]
    rw [e] at h
    exact (hcols i _ (Ideal.mul_mem_left _ _ ha')).2 h
  refine ⟨hc1, ?_⟩
  rw [RingHom.map_sub]
  exact sub_mem hint (int_of_idem (one_mul 1))

end GlobalTheory.FinPl.InvLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfAddCharTrivialOnHomLatticeLineStatement
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_of_addChar_trivial_on_homLattice_line : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : Pl D), Tame D v → IsSelfDualC V LV → IsSelfDualC W LW → MonoAt dV LV LV₀ v → MonoAt dW LW LW₀ v → ColsAt dV dW.jX LV LW v → ∀ (i : Fin ρ) (c : AE D), c - 1 ∈ idAt D (· = v) → (∀ b ∈ idAt D (· = v), dV.extY W (dW.jY ⬝ Matrix.single i i b) ∈ latO V W (LV : Set _) (LW : Set _) (· = v) → ψ (symplO V W (dV.extX W (dW.jX ⬝ Matrix.single i i c)) (dV.extY W (dW.jY ⬝ Matrix.single i i b))) = 1) → c - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.InvLat.int_of_psi_line | exact GlobalTheory.FinPl.InvLat.int_of_psi_line | (intros; apply GlobalTheory.FinPl.InvLat.int_of_psi_line <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualCOfGramOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms GlobalTheory.StepData
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.LocMod.IntFrameStd

variable {D : D7}

theorem isSelfDualC_of_gram_one {S : HSp D} (hG : S.gram = 1) (L : Lat S)
    (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank) : IsSelfDualC S L := by
  have hm : ∀ x : Fin S.rank → D.host.E, x ∈ Examples₂.stdLat _ ↔ ∀ i, IsIntegral ℤ (x i) := fun x => by
    rw [Examples₂.stdLat, Module.Basis.mem_span_iff_repr_mem]
    exact forall_congr' fun i => ⟨fun ⟨b, hb⟩ => by rw [← show _ = x i from hb]; exact b.2,
      fun h => ⟨⟨_, h⟩, rfl⟩⟩
  have hLe : L = Examples₂.stdLat _ := by
    ext z
    rw [hL z, hm]
    rfl
  subst hLe
  refine ⟨Examples₂.stdLat_isLattice _, fun y => GlobalTheory.Ker.Inhab.selfDual_diag (fun _ => false) _ (fun i k => ?_) y⟩
  rw [hG, Matrix.one_apply]
  simp [Examples₂.sgn]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.LocMod.IntFrameStd
end
end

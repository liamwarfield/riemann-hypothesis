module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.EvaluationAtUnitaryOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscSeedOfLocSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.OneSat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.UnitOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LRSplit
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LPermSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CuspSupportOf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CuspOrTwo
open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne


open PositivityTheory.Rg.Rs.PExpFin in
private theorem cusp_or_exp {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    (V : Submodule ℂ (Sm E N)) (hV : IsDiscrete V) :
    (∃ P : CuspSub E N, P.V = V) ∨ ∃ r, 0 < r ∧ r < N ∧ (ExpV r V).Nonempty := by
  obtain ⟨-, -, -, hDct⟩ := dict_holds E N
  by_cases hex : ∃ r, 0 < r ∧ r < N ∧ ∃ φ ∈ V, An.ctn r φ.1 ≠ 0
  · right
    obtain ⟨r, hr, hrN, φ, hφ, hne⟩ := hex
    obtain ⟨hct, -⟩ := hDct φ (hV.aut φ hφ) r hr hrN
    have hcont : ∀ g, Continuous fun t => An.ctn r φ.1 (aT E N r t * g) := by
      let _ : MeasurableSpace (BlockIx N r → Ad E) := _root_.borel _
      have _ : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
      obtain ⟨μ, 𝓕, hμ, h𝓕, e⟩ := hct
      obtain ⟨F, hF, -⟩ := GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E N r φ (hV.aut φ hφ).left (hV.aut φ hφ).level μ 𝓕 hμ h𝓕
      have e2 : An.ctn r φ.1 = F.1 := e.trans (funext fun g => (hF g).symm)
      intro g
      rw [e2]
      exact PDich.continuous_aT F r g
    obtain ⟨p, hp, hk, hroot⟩ := killPoly_holds (GA E N) (aT E N r) (An.ctn r φ.1) (fun u v => aT_add r u v) hcont
      (finTr_holds E N φ (hV.aut φ hφ) r hr hrN _ hct)
    have hdeg : 0 < p.degree := hp.degree_pos.2 fun h1 => hne (funext fun g => by
      have := hk g
      rw [h1] at this
      simpa [aT_zero] using this)
    obtain ⟨z, hz⟩ := Complex.exists_root hdeg
    obtain ⟨c, -, F, hF, hF0, hFe⟩ := hroot z hz
    exact ⟨r, hr, hrN, c, φ, hφ, An.ctn r φ.1, hct, F, hF, hF0, hFe⟩
  · left
    push Not at hex
    have hcusp : ∀ φ ∈ V, IsCuspForm φ := fun φ hφ => ⟨hV.aut φ hφ, by
      intro r hr hrN inst1 inst2 μ 𝓕 hμ hF g
      obtain rfl : inst1 = _root_.borel _ := inst2.measurable_eq
      obtain ⟨c, -, e⟩ := (hDct φ (hV.aut φ hφ) r hr hrN).2 _ ⟨μ, 𝓕, hμ, hF, rfl⟩
      have := congrFun e g
      rw [hex r hr hrN φ hφ] at this
      simpa [PositivityTheory.Affgl.CT.ct] using this⟩
    exact ⟨⟨V, hcusp, hV.stable, hV.ne_bot, hV.irred⟩, rfl⟩

private theorem pos_of_ascEmb {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r a d : ℕ}
    {V : Submodule ℂ (Sm E r)} {π : CuspSub E a} (hr : 0 < r) (h : AscEmb V π d) : 0 < a ∧ 0 < d := by
  obtain ⟨hs, -⟩ := h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  subst hs
  exact ⟨Nat.pos_of_mul_pos_left hr, Nat.pos_of_mul_pos_right hr⟩

private theorem two_of_exp {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    (V : Submodule ℂ (Sm E N)) (hV : IsDiscrete V) (τ : E →+* ℂ) (hτ : RegInt V τ)
    (hne : ∃ r, 0 < r ∧ r < N ∧ (ExpV r V).Nonempty) :
    ∃ (a d : ℕ) (P : CuspSub E a), 1 ≤ a ∧ 2 ≤ d ∧ P.IsUnitary ∧ IsNormalised P ∧ AscEmb V P d := by
  obtain ⟨r, c, lam, hr0, hrN, hc, hlam, hpc, hbd⟩ :=
    PAscAll.exists_extremal (expFin_of dict_holds finTr_holds) expNeg_holds V hV hne
  obtain ⟨s, rfl⟩ : ∃ s, N = r + s := ⟨N - r, by omega⟩
  have hs0 : 0 < s := by omega
  have hd : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := by exact_mod_cast Module.finrank_pos
  have hdC : (Module.finrank ℚ E : ℂ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hpc' : pE E (r + s) r c = -lam * (r * s) := by rw [hpc]; push_cast; ring
  obtain ⟨T, hT⟩ := slice_of dict_holds finTr_holds E r s hr0 hs0 V hV c hc
  have hL2 := chord_of expTw_holds sqIntCrit_holds E r s hr0 hs0 V c T lam hlam hT hpc' hbd
  obtain ⟨V₁, V₂, hV₁, hV₂, hemb⟩ :=
    proj_of pr_holds sliceTens_holds indMap_holds E r s hr0 hs0 V hV c _ _ T hT hL2
  obtain ⟨m, hm, hnd, hint⟩ := hτ
  obtain ⟨m₁, m₂, hm₁, hm₂, he⟩ := infInd2_holds E r s V V₁ V₂ _ _ hV hV₁ hV₂ hemb τ m hm
  have hτ₁ : RegInt V₁ τ := PAscAll.regInt_of_le hnd hint (he ▸ Multiset.le_add_right _ _) hm₁
  have hτ₂ : RegInt V₂ τ := PAscAll.regInt_of_le hnd hint (he ▸ Multiset.le_add_left _ _) hm₂
  obtain ⟨a₁, d₁, π₁, hu₁, hn₁, h₁⟩ := ascAll_holds E r hr0 V₁ hV₁ τ hτ₁
  obtain ⟨a₂, d₂, π₂, hu₂, hn₂, h₂⟩ := ascAll_holds E s hs0 V₂ hV₂ τ hτ₂
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hsum : (r : ℂ) * (c / (r * (Module.finrank ℚ E : ℂ))) + s * (-c / (s * (Module.finrank ℚ E : ℂ))) = 0 := by
    field_simp; ring
  have hre : (c / (r * (Module.finrank ℚ E : ℂ))).re < (s : ℝ) / 2 := by
    have e : (r : ℂ) * (Module.finrank ℚ E : ℂ) = (((r : ℝ) * (Module.finrank ℚ E : ℝ) : ℝ) : ℂ) := by push_cast; ring
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
    rw [e, Complex.div_ofReal_re, div_lt_iff₀ (mul_pos hrR hd)]
    have h3 : c.re / (Module.finrank ℚ E : ℝ) < (r : ℝ) * s / 2 := by
      have h4 := hpc'
      unfold pE at h4
      push_cast at h4
      nlinarith [mul_pos hlam (mul_pos hrR (show (0 : ℝ) < s by exact_mod_cast hs0))]
    rw [div_lt_iff₀ hd] at h3
    nlinarith
  have hsS : StringStep := stringStep_of PositivityTheory.AdelicQuotientData.jacquetShalika.1 PositivityTheory.AdelicQuotientData.jacquetShalika.2 infInd2_holds
    infAsc_holds satInd2_holds satAsc_holds satHerm_holds gap_holds
  have e₁ := h₁ π₁ (Setoid.refl π₁)
  have e₂ := h₂ π₂ (Setoid.refl π₂)
  obtain ⟨ha₁, hd₁⟩ := pos_of_ascEmb hr0 e₁
  obtain ⟨-, hd₂⟩ := pos_of_ascEmb hs0 e₂
  obtain ⟨hsig, hz₁, hz₂⟩ := hsS E r s hr0 hs0 V V₁ V₂ _ _ hV hV₁ hV₂ hemb τ ⟨m, hm, hnd, hint⟩ hsum hre
    a₁ d₁ a₂ d₂ π₁ π₂ hu₁ hn₁ e₁ hu₂ hn₂ e₂
  obtain ⟨rfl, hq⟩ := Sigma.mk.inj_iff.mp hsig
  have hiso : π₁.Iso π₂ := Quotient.exact (eq_of_heq hq)
  rw [hz₁, hz₂] at hemb
  refine ⟨a₁, d₁ + d₂, π₁, ha₁, by omega, hu₁, hn₁, ?_⟩
  exact stages_of indMap_holds E r s a₁ d₁ d₂ V V₁ V₂ π₁ hV hV₁ hV₂ hemb e₁
    (h₂ π₁ ((CuspSub.setoid E a₁).iseqv.symm hiso))

theorem UpperTheory.V.Z.Tf.GOne.cuspOrTwo :
    CuspOrTwo := by
  intro E _ _ _ N _ V hV τ hτ
  rcases cusp_or_exp V hV with h | hne
  · exact Or.inl h
  · exact Or.inr (two_of_exp V hV τ hτ hne)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.NotTwo
open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne

private theorem satV_of_locComp {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (Matrix.GeneralLinearGroup (Fin N) (w.adicCompletion E))} (hσ : IsLocCompGL V w σ) {B : Multiset ℂˣ}
    (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) {φ : Sm E N} (hφ : φ ∈ V) (h0 : φ ≠ 0)
    (hfix : ∀ k ∈ GlobalTheory.LFun.KGL w (n := N), finRep E N (locGL E N w k) φ = φ) : SatV V w B := by
  have hmem : ∀ ψ ∈ V, ψ ∈ ⨆ f : SatakeVectors.SatakeVectorEventually.MapsD V w σ, LinearMap.range f.1 := fun ψ hψ => by
    rw [SatakeVectors.SatakeVectorEventually.iSup_range_eq hV w σ hσ]; exact hψ
  have key : ∀ ψ ∈ V, (∀ k ∈ GlobalTheory.LFun.KGL w (n := N), finRep E N (locGL E N w k) ψ = ψ) → ψ ≠ 0 →
      GlobalTheory.LFun.IsSatVecGL w ((finRep E N).comp (locGL E N w)) ψ B := fun ψ hψ hψK hψ0 =>
    GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup σ.irred hB (fun f : SatakeVectors.SatakeVectorEventually.MapsD V w σ => f.1) (fun f => f.2.2)
      (hmem ψ hψ) (GlobalTheory.LGrp.mem_fixed.2 hψK) hψ0
  exact ⟨⟨φ, hφ, key φ hφ hfix h0⟩, key⟩

theorem UpperTheory.V.Z.Tf.GOne.notTwo :
    NotTwo := by
  intro E _ _ _ N a d V P π ha hd hV hA h
  have hNa : d * a = N := by
    obtain ⟨e, -⟩ := hA
    simpa using e
  have hN : 1 ≤ N := by
    rw [← hNa]
    exact Nat.mul_pos (by omega) ha
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  have hlev := GlobalTheory.CuspRep.LocSph.eventually_mem (E := E) ((hV.aut φ hφ).level.mem_nhds (by simp))
  have key : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      ∃ (B : Fin d → Multiset ℂˣ) (B' : Unit → Multiset ℂˣ),
        (∀ i, ((CG.mk P).twist (GlobalTheory.CuspRep.Model.absC E (spehExp d i : ℂ))).HasSat w (B i)) ∧
        (∀ _j : Unit, (CG.mk π).HasSat w (B' ())) ∧ ∑ i, B i = ∑ j, B' j := by
    filter_upwards [h, satAsc_holds E N a d V P hV hA, hlev] with w hw hs hl
    obtain ⟨σ, B, hσ, hB, hπ⟩ := hw
    obtain ⟨B₀, hB₀, hall⟩ := hs
    have hfix : ∀ k ∈ GlobalTheory.LFun.KGL w (n := N), finRep E N (locGL E N w k) φ = φ := fun k hk => by
      obtain ⟨g, rfl⟩ := hk
      exact hl g
    have e := hall B (satV_of_locComp hV hσ hB hφ h0 hfix)
    refine ⟨fun i => B₀.map (· * (GlobalTheory.CuspRep.Model.absC E (spehExp d i : ℂ)).val w), fun _ => B,
      fun i => StrStepB.hasSat_twist_absC P hB₀ _, fun _ => hπ, ?_⟩
    apply Multiset.map_injective (f := fun b : ℂˣ => (b : ℂ)) Units.val_injective
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [e, StrStepC.map_fsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SatakeVectors.satTw_eq]
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp [StrStepB.absC_val]
  obtain ⟨s, -⟩ := PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity E (Fin d) Unit (fun _ => a) (fun _ => N)
    (fun i => (CG.mk P).twist (GlobalTheory.CuspRep.Model.absC E (spehExp d i : ℂ))) (fun _ => CG.mk π)
    (fun _ => ha) (fun _ => hN) key
  have hc := Fintype.card_congr s
  simp at hc
  omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CsdDisc
open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne

theorem UpperTheory.V.Z.Tf.GOne.csdDisc :
    CsdDisc := by
  intro E _ _ _ n _ π h
  have hc : π.IsCsd := GlobalTheory.CsdBack.isCsd_of_paired CuspFormAutomorphicBounds.automorphicFormsFiniteGL E n π
    (PositivityTheory.JMult1.gelfandKazhdanDual_of_rigidity PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity
      GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E n π) h
  have hn : IsNormalised π := GlobalTheory.BcSpehCompare.isNormalised_of_isCsd hc
  refine isDiscrete_of_cuspSub π fun φ hφ => ?_
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL.of_invariant (π.cusp φ hφ) (hn φ hφ)
  exact GlobalTheory.DiscChar.isSqInt_of_bounded (hn φ hφ) (C := C) fun g => by simpa using hC g
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.OnlyOne
open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne

namespace UpperTheory.V.Z.Tf.GOne.saturation_regularity_aux

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

private theorem hasSat_of_comp {P : CuspSub E n} (hV : IsDiscrete P.V) {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin n) (w.adicCompletion E))} (hσ : IsLocCompGL P.V w σ) {B : Multiset ℂˣ}
    (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) : GlobalTheory.LFun.HasSatGL w (P.locRep w) B := by
  have hmem : ∀ ψ ∈ P.V, ψ ∈ ⨆ f : SatakeVectors.SatakeVectorEventually.MapsD P.V w σ, LinearMap.range f.1 := fun ψ hψ => by
    rw [SatakeVectors.SatakeVectorEventually.iSup_range_eq hV w σ hσ]; exact hψ
  constructor
  · obtain ⟨f, h0, hfV, hf⟩ := hσ
    obtain ⟨x, hx⟩ := hB.exists_vec
    have hi : LinearMap.ker f = ⊥ := ((GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters.isIrreducible_iff σ.ρ).1 σ.irred).2 _ (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hf, hv, map_zero]) |>.resolve_right fun e => h0 (LinearMap.ker_eq_top.1 e)
    have h1 := hx.map (ρ' := (finRep E n).comp (locGL E n w)) f hf
      ((map_ne_zero_iff f (LinearMap.ker_eq_bot.1 hi)).2 hx.1)
    refine (Submodule.ne_bot_iff _).2 ⟨⟨f x, hfV x⟩, GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext ?_,
      fun e => h1.1 (congrArg Subtype.val e)⟩
    exact GlobalTheory.LGrp.mem_fixed.1 h1.2.1 k hk
  · intro y hy h0
    have h2 := GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup (ρ := (finRep E n).comp (locGL E n w)) σ.irred hB
      (fun f : SatakeVectors.SatakeVectorEventually.MapsD P.V w σ => f.1) (fun f => f.2.2) (hmem y.1 y.2)
      (GlobalTheory.LGrp.mem_fixed.2 fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hy k hk))
      (fun e => h0 (Subtype.ext e))
    exact GlobalTheory.LFun.IsSatVecGL.of_map (ρ' := (finRep E n).comp (locGL E n w)) P.V.subtype (fun _ _ => rfl)
      Subtype.val_injective h2

private theorem regInt_of_weight {V : Submodule ℂ (Sm E n)} {τ : E →+* ℂ} {m : Multiset ℂ}
    (h : HasInfCharGL V τ m) (lam : Formalism.BasicNotions.DomWeight n) (e : m = infOfWeight lam) : RegInt V τ := by
  subst e
  refine ⟨_, h, GlobalTheory.DefiniteBC.nodup_infOfWeight lam, fun x hx y hy => ?_⟩
  obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hx
  obtain ⟨l, -, rfl⟩ := Multiset.mem_map.1 hy
  exact ⟨lam.w k - lam.w l - (k : ℕ) + (l : ℕ), by push_cast; ring⟩

private theorem key (hC : CuspOrTwo) (hT : NotTwo) {m : ℕ} (hn : 1 ≤ n) (π : CuspSub E n) (hm : m = n)
    {V : Submodule ℂ (Sm E m)} (σ : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin m) (w.adicCompletion E)))
    (mu : (E →+* ℂ) → Multiset ℂ) (hV : IsDiscrete V) (hl : ∀ w, IsLocCompGL V w (σ w))
    (hi : ∀ τ, HasInfCharGL V τ (mu τ)) (hr : ∀ τ, ∃ lam : Formalism.BasicNotions.DomWeight n, mu τ = infOfWeight lam)
    (hs : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      ∃ B, GlobalTheory.LFun.HasSatGL w (σ w).ρ B ∧ (CG.mk π).HasSat w B) :
    ∃ e : m = n, e ▸ V = π.V := by
  subst hm
  refine ⟨rfl, ?_⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨lam, hlam⟩ := hr τ
  rcases hC E m hn V hV τ (regInt_of_weight (hi τ) lam hlam) with ⟨P, rfl⟩ | ⟨a, d, P, ha, hd, -, -, hA⟩
  · exact UpperTheory.V.Af.strongMultOneC E m P π
      (hs.mono fun w ⟨B, h1, h2⟩ => ⟨B, hasSat_of_comp hV (hl w) h1, h2⟩)
  · exact absurd (hs.mono fun w ⟨B, h1, h2⟩ => ⟨σ w, B, hl w, h1, h2⟩) (hT E m a d V P π ha hd hV hA)

end UpperTheory.V.Z.Tf.GOne.saturation_regularity_aux

theorem UpperTheory.V.Z.Tf.GOne.onlyOne :
    CuspOrTwo → NotTwo → OneSat → OnlyOne := by
  intro hC hT hS E _ _ _ n hn π D D' e hR h1 hcls
  have hc : D.c = 1 := by
    have h := Fintype.card_congr e
    simp only [Fintype.card_fin] at h
    rw [h]
    exact h1.1
  refine ⟨hc, fun i => ?_⟩
  have hsum : ∀ {M : Type} [AddCommMonoid M] (f : Fin D.c → M), ∑ j, f j = f i := fun {M} _ f => by
    have hsub : Subsingleton (Fin D.c) := by rw [hc]; infer_instance
    exact Fintype.sum_subsingleton f i
  have hN : D.N i = n := (hsum D.N).symm.trans D.h
  have hsat : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      ∃ B, GlobalTheory.LFun.HasSatGL w (D.σ i w).ρ B ∧ (CG.mk π).HasSat w B := by
    filter_upwards [Rig.eventually_sat D] with w hw
    obtain ⟨S, hS1, -⟩ := hw
    have hB : D.Sat w (∑ j, S j) := ⟨S, fun j => hS1 j, rfl⟩
    refine ⟨S i, (hS1 i).2, ?_⟩
    rw [← hsum S]
    exact (hS E n hn π D' h1 w _).2 (Rig.permSat E n D D' e w (fun j => hcls j w) _ hB)
  have hreg : ∀ τ, ∃ lam : Formalism.BasicNotions.DomWeight n, D.m i τ = infOfWeight lam := fun τ =>
    (hR τ).imp fun lam h => (hsum (D.m · τ)).symm.trans h
  exact saturation_regularity_aux.key hC hT hn π hN (D.σ i) (D.m i) (D.discrete i) (D.loc i) (D.inf i) hreg hsat
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.OnePre
open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne

private theorem add_le_of_strictAnti {n : ℕ} {t : Fin n → ℤ} (ht : StrictAnti t) (d : ℕ) :
    ∀ a b : Fin n, (b : ℕ) = a + d → t b + d ≤ t a := by
  induction d with
  | zero =>
    intro a b h
    have : b = a := Fin.ext (by simpa using h)
    simp [this]
  | succ d ih =>
    intro a b h
    have hb := b.2
    have h1 := ih a ⟨a + d, by omega⟩ rfl
    have h2 : t b < t ⟨a + d, by omega⟩ := ht (Fin.lt_def.2 (by simp; omega))
    push_cast
    omega

private theorem exists_weight {n : ℕ} (m : Multiset ℂ) (hc : Multiset.card m = n) (hn : m.Nodup)
    (hz : ∀ z ∈ m, ∃ k : ℤ, z = (k : ℂ) + ((n : ℂ) - 1) / 2) : ∃ lam : Formalism.BasicNotions.DomWeight n, m = infOfWeight lam := by
  classical
  choose! f hf using hz
  let s : Finset ℤ := m.toFinset.image f
  have hinj : Set.InjOn f m.toFinset := fun a ha b hb e => by
    rw [hf a (by simpa using ha), hf b (by simpa using hb), e]
  have hcs : s.card = n := by
    rw [Finset.card_image_of_injOn hinj, Multiset.toFinset_card_of_nodup hn, hc]
  let e := s.orderEmbOfFin hcs
  let t : Fin n → ℤ := fun k => e k.rev
  have ht : StrictAnti t := fun a b h => e.strictMono (Fin.rev_lt_rev.2 h)
  refine ⟨⟨fun k => t k + (k : ℕ), fun a b hab => ?_⟩, ?_⟩
  · have hab' : (a : ℕ) ≤ b := hab
    have := add_le_of_strictAnti ht ((b : ℕ) - a) a b (by omega)
    have e1 : (((b : ℕ) - (a : ℕ) : ℕ) : ℤ) = (b : ℕ) - (a : ℕ) := by omega
    simp only
    omega
  · have h1 : (Finset.univ.val.map fun k : Fin n => e k) = s.val :=
      congrArg Finset.val (Finset.map_orderEmbOfFin_univ s hcs)
    have h2 : s.val = m.map f := by
      rw [Finset.image_val_of_injOn hinj, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hn]
    have h3 : m = (m.map f).map fun k : ℤ => (k : ℂ) + ((n : ℂ) - 1) / 2 := by
      rw [Multiset.map_map]
      conv_lhs => rw [← Multiset.map_id m]
      exact Multiset.map_congr rfl fun z hz => hf z hz
    refine h3.trans ?_
    rw [← h2, ← h1, Multiset.map_map, infOfWeight]
    conv_lhs => rw [← Finset.map_univ_equiv Fin.revPerm, Finset.map_val, Multiset.map_map]
    refine Multiset.map_congr rfl fun k _ => ?_
    simp only [Function.comp, Function.Embedding.coeFn_mk, Equiv.coe_toEmbedding, Fin.revPerm_apply]
    push_cast
    ring

theorem UpperTheory.V.Z.Tf.GOne.onePre :
    OnePre := by
  intro E _ _ _ n hn π hr hd
  have hl : ∀ w, ∃ σ, IsLocCompGL π.V w σ := fun w =>
    (GlobalTheory.CuspRep.LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL E n π w).imp fun σ h =>
      ((cuspSub_iff π).2.1 w σ).2 h.1
  choose σ hσ using hl
  refine ⟨⟨1, fun _ => n, by simp, fun _ => π.V, fun _ w => σ w, fun _ τ => (CG.mk π).infChar τ,
    fun _ => hn, fun _ => hd, fun _ w => hσ w, fun _ τ => ?_⟩, ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩, fun τ => ?_⟩
  · exact ((cuspSub_iff π).2.2 τ _).2 (GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) τ)
  · obtain ⟨h1, h2⟩ := hr τ
    obtain ⟨lam, hlam⟩ := exists_weight _ ((CG.mk π).card_infChar τ) h1 h2
    exact ⟨lam, by simpa using hlam⟩
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.DescentTheorem.DescentOf
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.G

open PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def Descent : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (p : ℕ), p.Prime → ∀ S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), S.Finite →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∈ S → IsSplitAt w) →
      (∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → w.under (𝓞 (maximalRealSubfield E)) ∈ S) →
    ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∉ S → ∃ B, (CG.mk π).HasSat w B) →
      ∃ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ ∧
        (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∉ S → IsUnramU σ w) ∧
        (∀ w, IsSplitAt w → ∀ τ, π.IsLocComp w τ → IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ) ∧
        ∀ φ : E →+* ℂ, ∃ lam, HasWeightAt σ φ lam ∧ π.HasInfChar φ (infOfWeight lam)

def IsOne (D : Pre E n) (π : CuspSub E n) : Prop := D.c = 1 ∧ ∀ i, ∃ e : D.N i = n, e ▸ D.V i = π.V

def SplitLike (D : Pre E n) (π : CuspSub E n) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B

end PositivityTheory.Rg.BcB.G

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical
open GroundTheory.Automorphic.AutomorphicForm (constantTerm)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

namespace UpperTheory.V.Z.Tf.GaloisFromTraceFormula

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

def ReadJ (bad : Set (Pl E)) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) (m₀ : (E →+* ℂ) → Multiset ℂ)
    (X : Set (CuspSub E N)) (P : Sm E N → Prop) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (D : J → CD E N) (C : J → Pl E → Multiset ℂˣ),
    (∀ j, (∀ π ∈ X, ¬ (D j).Has π) ∧ ∀ w ∉ bad, (D j).Sat w (C j w)) ∧
    ∀ (φ : ℕ → Sm E N) (m : ℕ → (E →+* ℂ) → Multiset ℂ) (B : ℕ → Pl E → Multiset ℂˣ),
      (∀ k, EigT bad K W (φ k) (m k) (B k) ∧ P (φ k)) → MTo m m₀ →
      ∃ (j : J) (s : ℕ → ℕ), StrictMono s ∧ (D j).Inf m₀ ∧ ∀ w ∉ bad, STo (qV E w) N (fun k => B (s k) w) (C j w)

end

def CuspCaseJ : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ), 1 ≤ N → ∀ (bad : Set (Pl E)) (K : Subgroup (GL (Fin N) (Af E)))
  (W : Submodule ℂ (Kinf E N → ℂ)) m₀ (X : Set (CuspSub E N)), bad.Finite → Lev bad K → FiniteDimensional ℂ W →
    (∀ π ∈ X, ∀ ψ ∈ π.V, ∀ t g, ψ.1 (splitCentre E N t * g) = ψ.1 g) → ReadJ bad K W m₀ X fun φ => IsCuspForm φ ∧ Excl X φ

def CtCaseJ : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ), 1 ≤ r → 1 ≤ s → ∀ bad : Set (Pl E),
  (∀ K (W : Submodule ℂ (Kinf E r → ℂ)) m₀, Lev bad K → FiniteDimensional ℂ W → ReadJ (N := r) bad K W m₀ ∅ fun _ => True) →
  (∀ K (W : Submodule ℂ (Kinf E s → ℂ)) m₀, Lev bad K → FiniteDimensional ℂ W → ReadJ (N := s) bad K W m₀ ∅ fun _ => True) →
  ∀ K (W : Submodule ℂ (Kinf E (r + s) → ℂ)) m₀ X, Lev bad K → FiniteDimensional ℂ W → ReadJ (N := r + s) bad K W m₀ X fun φ => ∃ g, constantTerm r φ.1 g ≠ 0

def CDAddG : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ) (D₁ : CD E r) (D₂ : CD E s) (ν ν' : HChar E),
  1 ≤ r → 1 ≤ s → ∃ D : CD E (r + s), (∀ π : CuspSub E (r + s), ¬ D.Has π) ∧ (∀ w B₁ B₂, ν.UnrAt w → ν'.UnrAt w → D₁.Sat w B₁ →
    D₂.Sat w B₂ → D.Sat w (B₁.map (· * ν.val w) + B₂.map (· * ν'.val w))) ∧
    ∀ τ, ∑ i, (D.P i).infChar τ = ∑ i, ((D₁.P i).twist ν).infChar τ + ∑ i, ((D₂.P i).twist ν').infChar τ

def AbsInf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (P : CG E N) (z : ℂ) (τ : E →+* ℂ),
  (P.twist (Model.absC E z)).infChar τ = (P.infChar τ).map (· + z) ∧
    (P.twist (GlobalTheory.Mem.Chr.CharModel.absChar E z)).infChar τ = (P.infChar τ).map (· + z)

def MToLaws : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
  (∀ (m : ℕ → (E →+* ℂ) → Multiset ℂ) x y, MTo m x → MTo m y → x = y) ∧
  (∀ (m : ℕ → (E →+* ℂ) → Multiset ℂ) x (z : ℕ → ℂ) (z₀ : ℂ), MTo m x → Tendsto z atTop (𝓝 z₀) →
    MTo (fun k t => (m k t).map (· + z k)) fun t => (x t).map (· + z₀)) ∧
  ∀ (m m' : ℕ → (E →+* ℂ) → Multiset ℂ) x x', MTo m x → MTo m' x' → MTo (fun k t => m k t + m' k t) fun t => x t + x' t

def RegOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (l : InfinitePlace E → DomWeight n) (D : CD E n),
  D.Inf (mW l) → D.Reg

def TwDataT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ), a + b = n → 1 ≤ a → 1 ≤ b →
  ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
    (lam : InfinitePlace E → DomWeight n),
    (∀ v, (infOfWeight (l₁ v)).map (· + (b : ℂ) * (e v : ℂ) / 2) + (infOfWeight (l₂ v)).map (· + (a : ℂ) * (e v : ℂ) / 2) =
      infOfWeight (lam v)) → ∀ (D₁ : CD E a) (D₂ : CD E b), D₁.Inf (mW l₁) → D₂.Inf (mW l₂) →
    ∃ D : CD E n, (∀ π : CuspSub E n, ¬ D.Has π) ∧ D.Reg ∧
      ∀ w B₁ B₂, μ.UnrAt w → D₁.Sat w B₁ → D₂.Sat w B₂ → D.Sat w (un μ a b w B₁ B₂)

def UnStable : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (a b : ℕ) (w : Pl E) (B₁ B₂ : Multiset ℂˣ),
  μ.val w = -1 → inv B₁ = B₁ → inv B₂ = B₂ → inv (un μ a b w B₁ B₂) = un μ a b w B₁ B₂

def CsdInert : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  GlobalTheory.ContraPair.DualIsConj π → ∀ᶠ w : Pl E in cofinite, ¬ IsSplitAt w → ∀ B, (CG.mk π).HasSat w B → inv B = B

def PreOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  GlobalTheory.ContraPair.DualIsConj π → ∀ D : CD E n, ¬ D.Has π → D.Reg →
    (∀ᶠ w : Pl E in cofinite, ¬ IsSplitAt w → ∃ B, D.Sat w B ∧ inv B = B) →
    (∀ᶠ w : Pl E in cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B) →
    ∃ D' : PositivityTheory.Rg.BcB.F.Pre E n, D'.Reg ∧ D'.ThetaStable ∧ PositivityTheory.Rg.BcB.G.SplitLike D' π ∧ ¬ PositivityTheory.Rg.BcB.G.IsOne D' π

end UpperTheory.V.Z.Tf.GaloisFromTraceFormula

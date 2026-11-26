module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodNonvanishingOfArchimedeanInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.FibreIntegralEqZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchDefs

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Period
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ExistsMultTEqPoin
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace UpperTheory.Lit.Cusp

theorem poin_isCuspFun : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, Nonempty D.what₂.Tau → ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, IsCuspFun V (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) := by
  intro D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c hT a
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  intro r C hC μ 𝓕 hμ h𝓕 g
  haveI := i1; haveI := i2; haveI := i3; haveI := i4; haveI := i5; haveI := i7
  haveI : LocallyCompactSpace (NI V C) := (GlobalTheory.CuspDecay.Model.isClosed_NI V hC).locallyCompactSpace
  haveI : SecondCountableTopology (NI V C) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI := hμ
  set K := congLev D.sp.cm V.gram Λ 𝔪 with hK
  have hm : Measurable (coef θ M K v fun τ => (a τ : M.H τ)) := GlobalTheory.T.measurable_level_indicator_coefficient_test_function D θ hθ V S M Λ 𝔪 hΛ h𝔪 v _
  set f : GA D V → ℂ := fun y => coef θ M K v (fun τ => (a τ : M.H τ)) (c * y * g) with hf
  have hfm : ∀ γ : GA D V, Measurable fun h : NI V C => f (γ * (NI V C).subtype h) := fun γ =>
    hm.comp ((continuous_const.mul (continuous_const.mul continuous_subtype_val)).mul continuous_const).measurable
  obtain ⟨-, Kc, hKc, hcov⟩ := GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V r C ⟨hC.2.1, hC.2.2⟩
  have hcov' : ∀ h : NI V C, ∃ δ ∈ (GQ V).comap (NI V C).subtype, δ * h ∈ Kc := fun h => by
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov h
    exact ⟨γ⁻¹, Subgroup.inv_mem _ hγ, by simpa using hk⟩
  obtain ⟨B, hB⟩ := GlobalTheory.T.poincareSeries_partialSums_bounded_compact D θ hθ V S M Λ 𝔪 hΛ v hv hT c a ((fun h : NI V C => (h : GA D V) * g) '' Kc)
    (hKc.image (continuous_subtype_val.mul continuous_const))
  have hpt : ∀ h ∈ Kc, ∑' γ : GQ V, ‖f (γ * (NI V C).subtype h) * 1‖ₑ ≤ ENNReal.ofReal B := by
    intro h hh
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    have e : ∀ γ : GQ V, f (↑γ * (NI V C).subtype h) * 1 =
        coef θ M K v (fun τ => (a τ : M.H τ)) (c * (γ : GA D V) * ((h : GA D V) * g)) := fun γ => by
      simp only [hf, mul_one, Subgroup.coe_subtype, mul_assoc]
    simp only [e, ← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hB _ ⟨h, hh, rfl⟩ s)
  have hfin : (∑' q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V),
      ∫⁻ h, ‖f ((q.out : GQ V) * (NI V C).subtype h) * 1‖ₑ ∂μ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (GlobalTheory.T.lintegral_unfolding_le_of_translate_cover (GA D V) (NI V C) μ (NI V C).subtype Subtype.val_injective (GQ V) Kc hcov'
      (fun y => ‖f y * 1‖ₑ) (fun γ => ((hfm γ).mul_const 1).enorm))
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := B)) (hKc.measure_lt_top (μ := μ)).ne) ?_
    calc _ ≤ ∫⁻ _ in Kc, ENNReal.ofReal B ∂μ := setLIntegral_mono measurable_const hpt
      _ = ENNReal.ofReal B * μ Kc := setLIntegral_const _ _
  have hunf := GlobalTheory.T.integrableOn_and_hasSum_tsum_subgroup (GA D V) (NI V C) μ (NI V C).subtype Subtype.val_injective (GQ V) 𝓕 h𝓕 f (fun _ => 1)
    hfm measurable_const (fun _ _ _ => rfl) hfin
  have hzero : ∀ q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V),
      ∫ h, f ((q.out : GQ V) * (NI V C).subtype h) * 1 ∂μ = 0 := by
    intro q
    obtain ⟨τ⟩ := hT
    obtain ⟨P, Q, hPc, hQc, hcomm, hgen, htriv, hvan⟩ := fibre_integral_eq_zero D θ hθ V S M K v (fun τ => (a τ : M.H τ))
      (fun τ => (hv τ).2 _ (hv τ).1) (fun τ => (hv τ).2 _ (a τ).2) τ r C hC
    have := GlobalTheory.T.integral_haar_eq_zero_of_fibre_integrals_eq_zero_alt (NI V C) μ hμ P Q hPc hQc hcomm hgen htriv
      (fun n => coef θ M K v (fun τ => (a τ : M.H τ)) ((c * (q.out : GQ V)) * (n : GA D V) * g))
      (fun ν hν q' hq' => hvan ν hν q' hq' _ g)
    simpa [hf, mul_assoc] using this
  have hsum0 : HasSum (fun q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V) =>
      ∫ h, f ((q.out : GQ V) * (NI V C).subtype h) * 1 ∂μ) 0 := by
    simpa only [hzero] using (hasSum_zero : HasSum (fun _ : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V) => (0:ℂ)) 0)
  have h0 := hunf.2.unique hsum0
  rw [← h0]
  refine integral_congr_ae (.of_forall fun n => ?_)
  simp only [poin, hf, mul_one, Subgroup.coe_subtype, mul_assoc]

open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension


open Classical in
theorem exists_multT_eq_poin : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, Nonempty D.what₂.Tau → ∃ y ∈ MultT θ M (Lev.levA V (congLev D.sp.cm V.gram Λ 𝔪) : Set _) 1, ∀ a : M.Vec, (∀ τ, (a τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → y (PiTensorProduct.tprod ℂ a) = poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ := by
  intro hHC hCW hRD D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c hτ
  obtain ⟨haut, ⟨T₀, hT₀⟩, hKeq⟩ := GlobalTheory.T.coefficientPoincareSeries_isAutomorphic D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c
  have hder := GlobalTheory.T.poincareSeries_smooth_moderateGrowth_deriv hHC D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c
  have hcusp := poin_isCuspFun D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c hτ
  obtain ⟨vol⟩ := (GlobalTheory.Unf.VolExist.measures_exist D).1 V
  have hGK : IsGKMap θ M (Lev.levA V (congLev D.sp.cm V.gram Λ 𝔪) : Set _) 1 vol.μ vol.𝓕 T₀ := by
    refine ⟨fun u => ?_, fun u => ?_, fun u => ?_, fun u => ?_, fun u => ?_, fun u k hk g => ?_, ?_, ?_⟩
    · rw [hT₀]; exact (haut u).1
    · rw [hT₀]; exact (hder u).1
    · rw [hT₀]; exact hcusp u
    · rw [hT₀]
      have hr := GlobalTheory.Grow.rapidDec_of_unifModGrowth hRD hθ (haut u).1 (hder u).1 (hder u).2.1 (hcusp u)
      exact GlobalTheory.CuspDecay.memLp_of_bounded hr.continuous hr.bounded _ _ vol.haar vol.fund 2
    · rw [hT₀]; exact (hder u).2.1
    · rw [hT₀, (haut u).2.2.2 k hk g]; simp
    · intro τ k hk u w hw
      rw [hT₀, hT₀]
      have e : (fun τ' => ((Function.update u τ w τ' : kFin M τ') : M.H τ')) =
          Function.update (fun τ' => (u τ' : M.H τ')) τ (M.rep τ k (u τ)) := by
        funext τ'
        by_cases h : τ' = τ
        · subst h; simp [hw]
        · simp [Function.update_of_ne h]
      rw [e]
      exact hKeq _ τ k (maxCpt_subset M τ hk)
    · intro τ X hX u w hw
      rw [hT₀, hT₀]
      exact (hder u).2.2 τ X hX w hw
  obtain ⟨T, ⟨hTm, hTe⟩, -⟩ := (GlobalTheory.GKExtensionToSmoothVectors.gkExtension hHC hCW D).1 θ hθ V S M _ 1 vol.μ vol.𝓕 vol.haar vol.fund T₀ hGK
  refine ⟨PiTensorProduct.lift T, ?_, fun a ha => ?_⟩
  · rw [mem_multT, LinearEquiv.symm_apply_apply]
    exact Submodule.subset_span hTm
  · rw [PiTensorProduct.lift.tprod, hTe a (fun τ => ⟨a τ, ha τ⟩) (fun τ => rfl), hT₀]

end UpperTheory.Lit.Cusp

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace UpperTheory.Lit.Cusp


set_option maxHeartbeats 1000000 in
open GlobalTheory.SepPer.PerNe in
theorem exists_cusp_form_theta_period_ne_zero : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    GlobalTheory.Published.CuspRapidDecay → PackEx → DepthPays →
    Ev fun {D} _ {L} {sc} {G} W M => ∀ (M₀ : DSModel (Yc D 0) (parB (Ptw D) 0))
      (MP : DSModel (G.V (.core 0)) (Node.par D sc.cGap (.core 0))), ∀ t ∈ Rows L W.θ M₀, t ≠ 0 →
        ∃ y ∈ CoreForms G W.θ 0 MP, ∃ v w, per0 G M (y v) (t w) ≠ 0 := by
  intro hHC hCW hCRD hPE hDP
  obtain ⟨C, hC, hPack⟩ := hPE
  intro ε CF hCF
  obtain ⟨x₁, hx₁⟩ := hPack ε CF hCF
  obtain ⟨x₂, hx₂⟩ := hDP C hC ε CF hCF
  refine ⟨max x₁ x₂, ?_⟩
  intro D large₂ hε hx hSz T L μ0 hL G W M hM M₀ MP t ht ht0
  obtain ⟨p, hp⟩ := hx₁ D large₂ hε (le_trans (le_max_left _ _) hx) hSz T L μ0 hL G W M hM M₀ MP
  obtain ⟨s, hs0, hs1, hsLip, hsN1, hsN2⟩ := hx₂ D large₂ hε (le_trans (le_max_right _ _) hx) hSz T L μ0 hL G W M hM
  obtain ⟨hsdY, hsdV, hlam, hz0, hJ, hrY, hrV, hmY⟩ :=
    GlobalTheory.T.thetaRowGrid_bottom_selfDual_lattices D (offQ_of_sizeRows hSz) T L μ0 hL _ G W M hM

  have hθ : IsInfFam W.θ := W.θ_is
  have hmod : G.modul ≠ ⊥ := G.pl.modul_ne_bot _
  have hRow := (hM.row 0 (Nat.zero_le _)).haar_fund
  obtain ⟨v, hvμ, hv𝓕⟩ : ∃ v : GlobalTheory.Unf.Vol (Yc D 0), v.μ = M.ν (.grid 0 0) ∧ v.𝓕 = M.fd (.grid 0 0) :=
    ⟨⟨_, _, hRow.1, hRow.2⟩, rfl, rfl⟩
  obtain ⟨b, x, hb, hbx⟩ := GlobalTheory.T.exists_bound_multiplicity_value_exceeds_half hCRD D W.θ hθ (Yc D 0) (parB (Ptw D) 0) M₀ (levRow L : Set (GA D (Yc D 0))) v t ht ht0 p.w hp.1.ne
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb x)
  obtain ⟨hAutSm, hCusp, -⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hCRD D (Yc D 0) _ M₀ W.θ hθ _ 1 t ht
    (PiTensorProduct.tprod ℂ p.w)
  have hLip := GlobalTheory.T.unipotentPeriod_value_lipschitz_realOneParameter hCRD D W.θ hθ (Yc D 0) (G.V (.core 0)) G.sp.dec0 _ _ M₀ MP p (loss D C large₂.sc.b) hp (levRow L : Set (GA D (Yc D 0))) 1 t ht b hb
  have hInv : ∀ k ∈ Lev.levA (Yc D 0) (congLev D.sp.cm (Yc D 0).gram (L.ΛY 0)
      (Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)})), ∀ y, t (PiTensorProduct.tprod ℂ p.w) (y * k) = t (PiTensorProduct.tprod ℂ p.w) y := by
    intro k hk y
    rw [multT_apply_mul_lev ht _ k hk y, Pi.one_apply, one_mul]
  have hLong : Long W.θ p.A (L.ΛY 0) x s := by
    by_contra hn
    have hg1 : 1 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
    have hm1 : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    have hr1 : 1 ≤ (Yc D 0).rank := by rw [hrY]; exact (odd_r D).pos
    have hmin : ∀ τ, min (Finset.univ.filter fun a => p.A.ε τ a = true).card
        (Finset.univ.filter fun a => p.A.ε τ a = false).card ≤ D.R.m := fun τ => min_le_of_right_le (hmY p.A τ)
    have h := GlobalTheory.T.norm_cuspForm_le_of_shortLine D W.θ hθ (Yc D 0) p.A (L.ΛY 0) hsdY (D.host.g 0 * D.host.g 1) D.R.m hg1 hm1 hr1 hmin (t (PiTensorProduct.tprod ℂ p.w))
      hAutSm.toIsAutFun hCusp hInv (Real.exp (loss D C large₂.sc.b) * b) (by positivity) hLip x s hs0 hs1 hn
    rw [hrY] at h
    have : ‖t (PiTensorProduct.tprod ℂ p.w) x‖ ≤ b / 2 := by
      refine h.trans ?_
      have := mul_le_mul_of_nonneg_left hsLip hb0
      nlinarith
    linarith
  rw [hlam] at hsdV hz0
  have hJ' : ∀ k ∈ GfC (Yc D 0), Lev.finE (G.V (.core 0)) (stabilizerEmbedding G.sp.dec0 k) ∈
      congLev D.sp.cm (G.V (.core 0)).gram (G.sp.dec0.lat (L.ΛY 0) fun _ => 1) G.modul → k ∈ (levRow L : Set (GA D (Yc D 0))) := by
    rw [← hlam]; exact hJ
  obtain ⟨c, hc⟩ := GlobalTheory.T.unipotentPeriod_adelic_clauses_of_real hCRD D W.θ hθ (Yc D 0) (G.V (.core 0)) G.sp.dec0 _ _ M₀ MP p (loss D C large₂.sc.b) hp
    (G.sp.dec0.lat (L.ΛY 0) fun _ => 1) G.modul hsdV hmod hz0 (levRow L : Set (GA D (Yc D 0))) hJ' t ht v.μ v.haar
  have hN1 : 2 * Real.exp (loss D C large₂.sc.b + (6 * ((G.V (.core 0)).rank : ℝ) + 9) * Fintype.card D.what₂.Tau) ≤
      s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm G.modul) := by
    rw [hrV]; push_cast; exact hsN1
  have hne := GlobalTheory.T.poincareSeries_pairing_ne_zero_of_large_level D W.θ hθ (Yc D 0) (G.V (.core 0)) G.sp.dec0 _ _ M₀ MP p (loss D C large₂.sc.b) hp.1 (L.ΛY 0) G.modul hsdY hmod v (t (PiTensorProduct.tprod ℂ p.w)) c b s
    x (GlobalTheory.Core.Mi.BotPin.isContAut_multT ht _) hb hbx hs0.le (by linarith) hLong hc hN1 hsN2
  have hKD : KDecay MP p.v₀ := fun τ => ⟨(hp.1.dec τ).1, fun a ha =>
    GlobalTheory.T.coefficientDecay_kFinite_second_vector hHC D _ _ MP τ (p.v₀ τ) _ (hp.1.dec τ).1 (hp.1.dec τ).2 a ha⟩
  obtain ⟨y, hy, hyv⟩ := exists_multT_eq_poin hHC hCW hCRD D W.θ hθ (G.V (.core 0)) _ MP (G.sp.dec0.lat (L.ΛY 0) fun _ => 1)
    G.modul hsdV hmod p.v₀ hKD (p.g₀⁻¹ * stabilizerEmbedding G.sp.dec0 x⁻¹) ⟨D.eTau.symm 1⟩
  obtain ⟨v₀', hv₀'⟩ : ∃ v₀' : MP.Vec, ∀ τ, (v₀' τ : MP.H τ) = p.v₀ τ :=
    ⟨fun τ => ⟨p.v₀ τ, GlobalTheory.Core.Mi.kFin_le_sm hHC MP τ (hp.1.dec τ).1⟩, fun _ => rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a' : MP.Vec, ∀ τ, (a' τ : MP.H τ) = MP.rep τ (cmp W.θ τ p.g₀) (v₀' τ) :=
    ⟨fun τ => ⟨MP.rep τ (cmp W.θ τ p.g₀) (v₀' τ),
      GlobalTheory.UnifEvery.rep_mem_sm MP τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ _ p.g₀ τ) (v₀' τ).2⟩, fun _ => rfl⟩
  have hv₀f : (fun τ => (v₀' τ : MP.H τ)) = p.v₀ := funext hv₀'
  have hU := (mem_multT W.θ MP _ 1 y).1 hy
  have key := GlobalTheory.RealEquiv.mult_realElt D (G.V (.core 0)) _ W.θ MP _ 1 _ hU (fun τ => cmp W.θ τ p.g₀)
    (fun τ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ _ p.g₀ τ) v₀' a' ha'
  rw [← GlobalTheory.RealTransSm.eq_realElt hθ hp.1.real] at key
  have hyg : ∀ g, y (PiTensorProduct.tprod ℂ a') g =
      poin W.θ MP (congLev D.sp.cm (G.V (.core 0)).gram (G.sp.dec0.lat (L.ΛY 0) fun _ => 1) G.modul) (p.v W.θ)
        (stabilizerEmbedding G.sp.dec0 x⁻¹) (p.v W.θ) g := by
    intro g
    rw [apply_tprod_eq, key]
    show PiTensorProduct.lift.symm y v₀' (g * p.g₀) = _
    rw [← apply_tprod_eq, hyv v₀' (fun τ => (hv₀' τ).symm ▸ (hp.1.dec τ).1), hv₀f]
    exact GlobalTheory.T.coefficientPoincareSeries_move_real_point D W.θ hθ (G.V (.core 0)) _ MP _ p.v₀ p.g₀ hp.1.real _ g
  have hmem : y ∈ CoreForms G W.θ 0 MP := by
    show y ∈ MultT W.θ MP (Lev.levA (G.V (.core 0)) (G.levCong (.core 0)) : Set (GA D (G.V (.core 0)))) 1
    unfold GridData.levCong
    rw [hlam]
    exact hy
  have hper : per0 G M (y (PiTensorProduct.tprod ℂ a')) (t (PiTensorProduct.tprod ℂ p.w)) ≠ 0 := by
    unfold per0
    simp_rw [hyg]
    rw [hvμ, hv𝓕] at hne
    exact hne
  exact ⟨y, hmem, _, _, hper⟩

end UpperTheory.Lit.Cusp

end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchPack
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace UpperTheory.Lit.Branch

open GlobalTheory.PackLoc

theorem realInputE_transport : RealInputE → ∃ C : ℝ, 0 < C ∧
  ∀ (m k N : ℕ) (hk : m = k) (hN : N = k + 1) (e : Option (Fin k) ≃ Fin (k + 1)) (ε : Fin N → Bool) (lam : Fin N → ℝ)
    (ε' : Fin m → Bool) (mu : Fin m → ℝ) (B : ℝ),
    GlobalTheory.SepReal.Par e (fun i => ε (Fin.cast hN.symm i)) (fun i => lam (Fin.cast hN.symm i))
      (fun i => ε' (Fin.cast hk.symm i)) (fun i => mu (Fin.cast hk.symm i)) B →
    ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      (π : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (σ : Matrix (Fin m) (Fin m) ℂ → (H' →L[ℂ] H')),
      Formalism.MainNotions.S.IsDS ε lam π → Formalism.MainNotions.S.IsDS ε' mu σ →
      ∃ (v₀ v : H) (g₀ : Matrix (Fin N) (Fin N) ℂ) (w' : H') (c : ℝ),
        Formalism.MainNotions.S.IsLowUnit ε lam π v₀ ∧ g₀ ∈ Formalism.MainNotions.S.UJset ε ∧ v = π g₀ v₀ ∧
        GlobalTheory.Ell.SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) π v ∧ GlobalTheory.Ell.SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε')) σ w' ∧
        ‖w'‖ = 1 ∧ 0 < c ∧
        (ε (((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) none) = true ∧ ∀ i, ε (((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) (some i)) = ε' i) ∧
        (∀ b : H', ∫ h, star ⟪v, π (GlobalTheory.PackLoc.embOpt ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) (Formalism.MainNotions.S.umat h)) v⟫_ℂ *
            ⟪b, σ (Formalism.MainNotions.S.umat h) w'⟫_ℂ ∂(Formalism.REAL.muG ε') = (c : ℂ) * (⟪w', w'⟫_ℂ * ⟪b, w'⟫_ℂ)) ∧
        (∀ g ∈ Formalism.MainNotions.S.UJset ε,
          Integrable (fun h => ⟪v, π (g * GlobalTheory.PackLoc.embOpt ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) (Formalism.MainNotions.S.umat h)) v⟫_ℂ)
            (Formalism.REAL.muG ε') ∧
          ∫ h, ‖⟪v, π (g * GlobalTheory.PackLoc.embOpt ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ε') ≤
            c * GlobalTheory.SepReal.big C k B *
              Real.sqrt (∑ a, ‖g a (((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) none)‖ ^ 2) ^ (-(2 * (k : ℝ) + 7))) ∧
        (∀ X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε'), GlobalTheory.SepReal.hsn X ≤ 1 →
          Integrable (fun h => ⟪GlobalTheory.Ell.dR π (GlobalTheory.PackLoc.embOptL ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) X) v,
            π (GlobalTheory.PackLoc.embOpt ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) (Formalism.MainNotions.S.umat h)) v⟫_ℂ) (Formalism.REAL.muG ε') ∧
          ∫ h, ‖⟪GlobalTheory.Ell.dR π (GlobalTheory.PackLoc.embOptL ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) X) v,
            π (GlobalTheory.PackLoc.embOpt ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ε') ≤
            c * GlobalTheory.SepReal.big C k B) ∧
        ∃ A : ℝ, ∀ g ∈ Formalism.MainNotions.S.UJset ε, ‖⟪v, π g v⟫_ℂ‖ ≤ A * GlobalTheory.SepReal.hsn g ^ (-(20 * ((k : ℝ) + 1) ^ 2)) := by
  rintro ⟨C, hC, hF⟩
  refine ⟨C, hC, ?_⟩
  intro m k N hk hN e ε lam ε' mu B hP H H' _ _ _ _ π σ hπ hσ
  subst hk
  subst hN
  have he : ((finCongr (rfl : m = m)).optionCongr.trans (e.trans (finCongr (rfl : m + 1 = m + 1).symm))) = e := by
    ext x
    cases x <;> simp
  rw [he]
  have hP' : GlobalTheory.SepReal.Par e ε lam ε' mu B := hP
  obtain ⟨v₀, v, g₀, w', c, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    hF m e ε lam ε' mu B hP' H H' π σ hπ hσ
  exact ⟨v₀, v, g₀, w', c, h1, h2, h3, h4, h5, h6, h7, hP'.signs, h8, h9, h10, h11⟩

theorem act_of_eigen : ∀ (D : D7) (θ : InfFam D) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S')
  (MP : DSModel V S) (τ : D.what₂.Tau) (e : Option (Fin Y.rank) ≃ Fin V.rank) (v₀ v : MP.H τ)
  (g₀ : Matrix (Fin V.rank) (Fin V.rank) ℂ) (w' : (GlobalTheory.ConjDS.conjModel M₀).H τ) (c₁ lam : ℝ),
  (∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
    ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ u, M₀.rep τ (GlobalTheory.PackLoc.ptY M₀ τ u) = M₀.σ τ (Formalism.MainNotions.S.umat u)) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℂ, ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG (M₀.ε τ)) =
    lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  ‖w'‖ = 1 →
  (∀ b : (GlobalTheory.ConjDS.conjModel M₀).H τ, ∫ h, star ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ *
      ⟪b, (GlobalTheory.ConjDS.conjModel M₀).σ τ (Formalism.MainNotions.S.umat h) w'⟫_ℂ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) =
    (c₁ : ℂ) * (⟪w', w'⟫_ℂ * ⟪b, w'⟫_ℂ)) →
  ∀ b : M₀.H τ, ∫ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) *
      ⟪b, M₀.rep τ (GlobalTheory.PackLoc.ptY M₀ τ u) (GlobalTheory.ConjDS.cj (M₀.H τ) w')⟫_ℂ ∂(Formalism.REAL.muG (M₀.ε τ)) =
    ((lam * c₁ : ℝ) : ℂ) * ⟪b, GlobalTheory.ConjDS.cj (M₀.H τ) w'⟫_ℂ := by
  intro D θ Y V d S S' M₀ MP τ e v₀ v g₀ w' c₁ lam h1 h2 hH hw ha b
  set b' : (GlobalTheory.ConjDS.conjModel M₀).H τ := (GlobalTheory.ConjDS.cj (M₀.H τ)).symm b with hb'
  have key : ∀ x : Matrix (Fin Y.rank) (Fin Y.rank) ℂ,
      ⟪b, M₀.σ τ (GlobalTheory.ConjDS.rv x) (GlobalTheory.ConjDS.cj (M₀.H τ) w')⟫_ℂ =
        star ⟪b', (GlobalTheory.ConjDS.conjModel M₀).σ τ x w'⟫_ℂ := by
    intro x
    exact (inner_conj_symm (𝕜 := ℂ) b (M₀.σ τ (GlobalTheory.ConjDS.rv x) (GlobalTheory.ConjDS.cj (M₀.H τ) w'))).symm
  let F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℂ := fun x => ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e x) v⟫_ℂ *
        ⟪b, M₀.σ τ (GlobalTheory.ConjDS.rv x) (GlobalTheory.ConjDS.cj (M₀.H τ) w')⟫_ℂ
  have e1 : ∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) *
      ⟪b, M₀.rep τ (GlobalTheory.PackLoc.ptY M₀ τ u) (GlobalTheory.ConjDS.cj (M₀.H τ) w')⟫_ℂ =
      F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) := by
    intro u
    simp only [F, h1, h2, GlobalTheory.ConjDS.rv_rv]
  have e2 : ∀ h : Formalism.REAL.UJ ((GlobalTheory.ConjDS.conjModel M₀).ε τ), F (Formalism.MainNotions.S.umat h) =
      star (star ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ *
        ⟪b', (GlobalTheory.ConjDS.conjModel M₀).σ τ (Formalism.MainNotions.S.umat h) w'⟫_ℂ) := by
    intro h; simp only [F, key, star_mul, star_star, mul_comm]
  have hww : ⟪w', w'⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]; simp
  have e4 : star ⟪b', w'⟫_ℂ = ⟪b, GlobalTheory.ConjDS.cj (M₀.H τ) w'⟫_ℂ :=
    inner_conj_symm (𝕜 := ℂ) b (GlobalTheory.ConjDS.cj (M₀.H τ) w')
  rw [integral_congr_ae (ae_of_all _ e1), hH F, integral_congr_ae (ae_of_all _ e2)]
  rw [show (∫ h : Formalism.REAL.UJ ((GlobalTheory.ConjDS.conjModel M₀).ε τ), star (star ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ *
        ⟪b', (GlobalTheory.ConjDS.conjModel M₀).σ τ (Formalism.MainNotions.S.umat h) w'⟫_ℂ) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)))
      = star (∫ h : Formalism.REAL.UJ ((GlobalTheory.ConjDS.conjModel M₀).ε τ), star ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ *
        ⟪b', (GlobalTheory.ConjDS.conjModel M₀).σ τ (Formalism.MainNotions.S.umat h) w'⟫_ℂ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)))
      from integral_conj]
  rw [ha b', hww, one_mul, star_mul, e4]
  simp [Complex.real_smul]
  ring

theorem locOK_of_eigen : RealInputE → ∃ C : ℝ, 0 ≤ C ∧ Ev fun {D} _ _ {sc} {G} W _ => ∀ (M₀ : DSModel (Yc D 0) (parB (Ptw D) 0))
  (MP : DSModel (G.V (.core 0)) (Node.par D sc.cGap (.core 0))) (τ : D.what₂.Tau),
  ∃ (εA : Fin (Yc D 0).rank → Bool) (A : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) ℂ) (εB : Fin (G.V (.core 0)).rank → Bool)
    (B : Matrix (Fin (G.V (.core 0)).rank) (Fin (G.V (.core 0)).rank) ℂ) (v₀ : MP.H τ)
    (g₀ : Matrix (Fin (G.V (.core 0)).rank) (Fin (G.V (.core 0)).rank) ℂ) (w : M₀.H τ) (c : ℂ),
    GlobalTheory.PackLoc.LocOK W.θ G.sp.dec0 M₀ MP τ (6 * C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log sc.b) εA A εB B v₀ g₀ w c := by
  intro hRI
  obtain ⟨C, hC, hT1⟩ := realInputE_transport hRI
  refine ⟨C, hC.le, ?_⟩
  intro ε0 CF hCF
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.branchingHypotheses_gridParameters_largeScale ε0 CF hCF
  refine ⟨x₀, fun D large₂ h1 h2 h3 T L μ0 hL G W M hM => ?_⟩
  have hP := hx₀ D large₂ h1 h2 h3 T L μ0 hL G W M hM
  intro M₀ MP τ
  have hY : (Yc D 0).rank = D.R.r := by
    have h := D.sp.Y_rank 0 (Nat.zero_le _)
    simpa [Yc, Ranks.rankY] using h
  have hN : (G.V (.core 0)).rank = D.R.r + 1 := by
    have h : (Yc D 0).rank + 1 = (G.V (.core 0)).rank := G.sp.dec0.rank
    omega
  obtain ⟨⟨e, hPar⟩, hlog, -⟩ := hP τ (fun i => MP.ε τ (Fin.cast hN.symm i)) (fun i => MP.lam τ (Fin.cast hN.symm i))
    (fun i => (GlobalTheory.ConjDS.conjModel M₀).ε τ (Fin.cast hY.symm i)) (fun i => (GlobalTheory.ConjDS.conjModel M₀).lam τ (Fin.cast hY.symm i))
    (isEnum_cast' hN.symm (MP.enum τ)) (isEnum_cast' hY.symm ((GlobalTheory.ConjDS.conjModel M₀).enum τ))
  obtain ⟨v₀, v, g₀', w', c₁, hlow, hg₀', hv, hsmv, hsmw, hw1, hc₁, ⟨hs0, hs1⟩, ha, hb, hc, A₀, hA₀⟩ :=
    hT1 (Yc D 0).rank D.R.r (G.V (.core 0)).rank hY hN e (MP.ε τ) (MP.lam τ) ((GlobalTheory.ConjDS.conjModel M₀).ε τ)
      ((GlobalTheory.ConjDS.conjModel M₀).lam τ) (large₂.sc.b ^ 2) hPar (MP.H τ) ((GlobalTheory.ConjDS.conjModel M₀).H τ) (MP.σ τ)
      ((GlobalTheory.ConjDS.conjModel M₀).σ τ) (MP.ds τ) ((GlobalTheory.ConjDS.conjModel M₀).ds τ)
  set e' : Option (Fin (Yc D 0).rank) ≃ Fin (G.V (.core 0)).rank :=
    (finCongr hY).optionCongr.trans (e.trans (finCongr hN.symm)) with he'
  obtain ⟨B, hBu, hBg, hBad, hBz, hBmem, hBemb⟩ := GlobalTheory.T.exists_signature_matrix_extension D W.θ W.θ_is (Yc D 0) (G.V (.core 0)) G.sp.dec0 τ
    ((GlobalTheory.ConjDS.conjModel M₀).ε τ) ((GlobalTheory.ConjDS.conjModel M₀).fr τ) (MP.ε τ) e'
    ((GlobalTheory.ConjDS.conjModel M₀).fr_unit τ) ((GlobalTheory.ConjDS.conjModel M₀).fr_gram τ) hs0 hs1
  obtain ⟨lam, hlam, hH⟩ := GlobalTheory.T.unitary_haar_coordinate_reversal_positive_multiple _ (M₀.ε τ)
  obtain ⟨hreal, hmco⟩ := GlobalTheory.T.translated_matrix_coefficient_in_adapted_frame D _ _ MP τ B g₀' v₀ hBu hBg hg₀'
  obtain ⟨hpt, hlieX⟩ := GlobalTheory.T.conjugate_model_frame_matrix_facts_at_place D W.θ W.θ_is (Yc D 0) _ M₀ τ
  have hAu := (GlobalTheory.ConjDS.conjModel M₀).fr_unit τ
  have hbig : GlobalTheory.SepReal.big C D.R.r (large₂.sc.b ^ 2) ≤ Real.exp (6 * C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log large₂.sc.b) := by
    unfold GlobalTheory.SepReal.big
    apply Real.exp_le_exp.2
    have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ C * ((D.R.r : ℝ) + 1) ^ 4 by positivity)
    calc C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log (8 * ((D.R.r : ℝ) + 1) * large₂.sc.b ^ 2)
        ≤ C * ((D.R.r : ℝ) + 1) ^ 4 * (6 * Real.log large₂.sc.b) := h
      _ = 6 * C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log large₂.sc.b := by ring
  have hm0 : ∀ u, GlobalTheory.PackLoc.mco MP τ (B⁻¹ * g₀' * MP.fr τ) v₀ (GlobalTheory.PackLoc.embAt W.θ G.sp.dec0 τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e' (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ := fun u => by
    rw [hmco _ (hBmem _ (hpt u).1), hBemb _ (hpt u).1, (hpt u).2.1, ← hv]
  have hmg : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V (.core 0)) τ), ∀ u,
      GlobalTheory.PackLoc.mco MP τ (B⁻¹ * g₀' * MP.fr τ) v₀ (g * GlobalTheory.PackLoc.embAt W.θ G.sp.dec0 τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
      ⟪v, MP.σ τ (B * g * B⁻¹ * GlobalTheory.PackLoc.embOpt e' (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ := by
    intro g hg u
    rw [hmco _ (UH_mul' hg (hBmem _ (hpt u).1)), conj_mul' hBu, hBemb _ (hpt u).1, (hpt u).2.1, ← hv]
  have hm1 : ∀ X ∈ lieAt (Yc D 0) τ, ∀ (s : ℝ) u,
      GlobalTheory.PackLoc.mco MP τ (B⁻¹ * g₀' * MP.fr τ) v₀
        (GlobalTheory.PackLoc.embAt W.θ G.sp.dec0 τ (cmp W.θ τ (oneP W.θ (Yc D 0) τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) =
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e'
        (NormedSpace.exp (s • ((GlobalTheory.ConjDS.conjModel M₀).fr τ * X * ((GlobalTheory.ConjDS.conjModel M₀).fr τ)⁻¹)) *
          GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ := by
    intro X hX s u
    have hmem := UH_mul' ((hlieX X hX).2 s).1 (hpt u).1
    rw [hmco _ (hBmem _ hmem), hBemb _ hmem, conj_mul' hAu, ((hlieX X hX).2 s).2, (hpt u).2.1, ← hv]
  have hK : lam * (c₁ * GlobalTheory.SepReal.big C D.R.r (large₂.sc.b ^ 2)) ≤
      Real.exp (6 * C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log large₂.sc.b) * ‖((lam * c₁ : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hlam hc₁)]
    calc lam * (c₁ * GlobalTheory.SepReal.big C D.R.r (large₂.sc.b ^ 2)) = (lam * c₁) * GlobalTheory.SepReal.big C D.R.r (large₂.sc.b ^ 2) := by ring
      _ ≤ (lam * c₁) * Real.exp (6 * C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log large₂.sc.b) :=
        mul_le_mul_of_nonneg_left hbig (mul_pos hlam hc₁).le
      _ = _ := by ring
  have hL := GlobalTheory.T.smooth_vector_matrixCoeff_integrable (Yc D 0).rank (G.V (.core 0)).rank e' (MP.ε τ) ((GlobalTheory.ConjDS.conjModel M₀).ε τ)
    (MP.H τ) (MP.σ τ) v (c₁ * GlobalTheory.SepReal.big C D.R.r (large₂.sc.b ^ 2)) (MP.ds τ).2.2.1 hs0 hs1 hsmv
    (fun g hg => (hb g hg).1) hc
  obtain ⟨Cd, hCd⟩ := GlobalTheory.T.matrix_coefficient_decay_in_frame_of_translate_decay D.R.r (G.V (.core 0)).rank hN (MP.ε τ) (MP.H τ) (MP.σ τ) v₀ g₀' (MP.fr τ)
    (gramAt D (G.V (.core 0)) τ) A₀ (MP.ds τ).2.2.1 hg₀' (MP.fr_unit τ) (MP.fr_gram τ)
    (fun g hg => by rw [← hv]; exact hA₀ g hg)
  refine ⟨(GlobalTheory.ConjDS.conjModel M₀).ε τ, (GlobalTheory.ConjDS.conjModel M₀).fr τ, MP.ε τ, B, v₀, B⁻¹ * g₀' * MP.fr τ,
    GlobalTheory.ConjDS.cj (M₀.H τ) w', ((lam * c₁ : ℝ) : ℂ), ?_⟩
  exact
    { unitA := hAu
      gramA := (GlobalTheory.ConjDS.conjModel M₀).fr_gram τ
      unitB := hBu
      gramB := hBg
      adapted := hBad
      real := hreal
      kfin := GlobalTheory.isKFin_of_mem_lowKSub _ _ _ _ _ _ hlow.2
      dec := ⟨Cd, hCd⟩
      sm := GlobalTheory.T.conj_smooth_vector_conjugate_model_mem_smooth D _ _ M₀ τ w' hsmw
      ne := by
        intro h
        have h' : ‖GlobalTheory.ConjDS.cj (M₀.H τ) w'‖ = 1 := (GlobalTheory.ConjDS.cj (M₀.H τ)).norm_map w' ▸ hw1
        rw [h, norm_zero] at h'
        exact zero_ne_one h'
      cne := Complex.ofReal_ne_zero.2 (mul_pos hlam hc₁).ne'
      act := act_of_eigen D W.θ _ _ G.sp.dec0 _ _ M₀ MP τ e' v₀ v (B⁻¹ * g₀' * MP.fr τ) w' c₁ lam
        hm0 (fun u => (hpt u).2.2) (fun F => (hH ℂ F).2) hw1 ha
      far := GlobalTheory.T.transversal_coefficient_decay_at_real_place D W.θ _ _ G.sp.dec0 _ _ M₀ MP τ e' v₀ v (B⁻¹ * g₀' * MP.fr τ) B c₁ lam
        _ _ D.R.r hBu hBg hBz hN hmg (fun F => (hH ℂ F).1) (fun F => (hH ℝ F).2) hc₁ hlam hbig hb
      lip := GlobalTheory.T.matrix_coefficient_lipschitz_at_real_place D W.θ _ _ G.sp.dec0 _ _ M₀ MP τ e' v₀ v (B⁻¹ * g₀' * MP.fr τ)
        ((GlobalTheory.ConjDS.conjModel M₀).fr τ) _ lam _ _ hm0 hm1 (fun X hX => (hlieX X hX).1) hL (fun F => hH ℝ F) hlam hK }

theorem packEx_of_eigen : RealInputE → PackEx := by
  intro hRI
  obtain ⟨C, hC, hloc⟩ := locOK_of_eigen hRI
  refine ⟨6 * C, by positivity, ?_⟩
  intro ε CF hCF
  obtain ⟨x₀, hx⟩ := hloc ε CF hCF
  refine ⟨x₀, ?_⟩
  intro D large₂ hε hx0 hS T L μ0 hL G W M hM M₀ MP
  have h := hx D large₂ hε hx0 hS T L μ0 hL G W M hM M₀ MP
  choose εA A εB B v₀ g₀ w c hOK using h
  obtain ⟨p, hp⟩ := GlobalTheory.T.realVectors_allPlaces_of_localData W.θ W.θ_is G.sp.dec0 M₀ MP _ εA A εB B v₀ g₀ w c hOK
  refine ⟨p, ?_⟩
  have e : loss D (6 * C) large₂.sc.b = Fintype.card D.what₂.Tau * (6 * C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log large₂.sc.b) := by
    unfold loss; ring
  rw [e]
  exact hp

end UpperTheory.Lit.Branch

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace UpperTheory.Lit.Branch

theorem periodNe_of_eigen : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    GlobalTheory.Published.CuspRapidDecay → RealInputE → PeriodNe := by
  intro hHC hCW hCR hR
  have h0 := Cusp.exists_cusp_form_theta_period_ne_zero hHC hCW hCR (packEx_of_eigen hR) GlobalTheory.T.gridDepth_pays_every_loss
  intro ε CF hCF
  obtain ⟨x, hx⟩ := h0 ε CF hCF
  refine ⟨x, fun D large₂ e a b T L μ0 hL G W M hM M₀ MP t ht t0 w w0 => ?_⟩
  obtain ⟨y, hy, v, w', hp⟩ := hx D large₂ e a b T L μ0 hL G W M hM M₀ MP t ht t0
  obtain ⟨a', ha', hp'⟩ := GlobalTheory.PeriodNePf.exists_kf W M hM hCR hHC M₀ MP ht hy v w' hp w w0
  exact ⟨y, hy, a', ha', hp'⟩

end UpperTheory.Lit.Branch

end

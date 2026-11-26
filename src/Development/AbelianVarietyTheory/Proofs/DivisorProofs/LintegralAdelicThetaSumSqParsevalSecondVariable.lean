module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceComponentAdeleNormEqLocalNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtZeroHeisenbergCMRealLineTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped Pointwise
namespace GlobalTheory.ThetaParsevalInner

theorem setIntegral_eq_zero_of_twist {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddLeftInvariant] (G : AddSubgroup V) [Countable G]
    {s : Set V} (hs : IsAddFundamentalDomain G s μ) {h : V → ℂ} (hper : ∀ g ∈ G, ∀ y, h (g + y) = h y)
    {c : V} {a : ℂ} (hc : ∀ y, h (c + y) = a * h y) (ha : a ≠ 1) : ∫ y in s, h y ∂μ = 0 := by
  have ht : IsAddFundamentalDomain G (c +ᵥ s) μ := hs.vadd_of_comm c
  have e1 : ∫ y in s, h y ∂μ = ∫ y in c +ᵥ s, h y ∂μ := hs.setIntegral_eq ht (fun g y => hper g g.2 y)
  have e2 : ∫ y in c +ᵥ s, h y ∂μ = ∫ y in s, h (c + y) ∂μ := by
    have := (measurePreserving_add_left μ c).setIntegral_preimage_emb (measurableEmbedding_addLeft c) h (c +ᵥ s)
    rw [← this]
    congr 2
    ext y
    simp [Set.mem_vadd_set_iff_neg_vadd_mem]
  have e3 : ∫ y in s, h (c + y) ∂μ = a * ∫ y in s, h y ∂μ := by
    simp_rw [hc]
    exact integral_const_mul a _
  have : (1 - a) * ∫ y in s, h y ∂μ = 0 := by rw [sub_mul, one_mul, ← e3, ← e2, ← e1, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm ha))

theorem countable_numberField (F : Type) [Field F] [NumberField F] : Countable F :=
  Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm

theorem lintegral_thetaSum_schr_sq : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ]
    (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (𝓕₁ : Set (κ → AF F)), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ →
      μ 𝓕₁ ≠ ⊤ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ x : (κ → AF F),
      ∫⁻ y in 𝓕₁, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ)‖ₑ ^ 2 ∂μ =
        μ 𝓕₁ * ∑' ξ : κ → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ₑ ^ 2 := by
  intro F _ _ ψ hψ κ _ μ hμ 𝓕₁ hF hfin Φ hΦ x
  classical
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : Countable F := countable_numberField F
  haveI : IsFiniteMeasure (μ.restrict 𝓕₁) := isFiniteMeasure_restrict.mpr hfin
  haveI := hμ
  obtain ⟨hcont, hnorm, htriv, s0, hs0⟩ := hψ
  obtain ⟨emb, hemb⟩ : ∃ emb : (κ → F) → (κ → AF F), emb = fun ξ i => algebraMap F (AF F) (ξ i) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : (κ → F) → ℂ, a = fun ξ => Φ (emb ξ + x) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : (κ → F) → (κ → AF F) → ℂ, e = fun ξ y => ψ (emb ξ ⬝ᵥ y) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : (κ → AF F) → ℂ, g = fun y => ∑' ξ, a ξ * e ξ y := ⟨_, rfl⟩
  have hsum : Summable fun ξ => ‖a ξ‖ := by
    have h0 := GlobalTheory.WeilM.summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F x hΦ)
    subst ha hemb
    exact h0
  have he_norm : ∀ ξ y, ‖e ξ y‖ = 1 := fun ξ y => by rw [he]; exact hnorm _
  have he_cont : ∀ ξ, Continuous (e ξ) := fun ξ => by
    rw [he]; exact hcont.comp (continuous_const.dotProduct continuous_id)
  have hconj : ∀ t, (starRingEnd ℂ) (ψ t) = ψ (-t) := fun t => by
    have h1 : ψ t * (starRingEnd ℂ) (ψ t) = 1 := by rw [Complex.mul_conj', hnorm]; simp
    have h2 : ψ t * ψ (-t) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    have h0 : ψ t ≠ 0 := fun h => by simpa [h] using hnorm t
    exact mul_left_cancel₀ h0 (h1.trans h2.symm)
  have hemb_sub : ∀ ξ η, emb (ξ - η) = emb ξ - emb η := by
    intro ξ η; rw [hemb]; funext i; simp [map_sub]
  have he_sub : ∀ ξ η y, e (ξ - η) y = e ξ y * (starRingEnd ℂ) (e η y) := by
    intro ξ η y
    simp only [he]
    rw [hconj, hemb_sub, sub_dotProduct, sub_eq_add_neg, AddChar.map_add_eq_mul]
  have hsum_e : ∀ y, Summable fun ξ => ‖a ξ * e ξ y‖ := fun y => by simpa [norm_mul, he_norm] using hsum
  have hg_bd : ∀ y, ‖g y‖ ≤ ∑' ξ, ‖a ξ‖ := fun y => by
    rw [hg]
    refine (norm_tsum_le_tsum_norm (hsum_e y)).trans (le_of_eq ?_)
    congr 1; funext ξ; rw [norm_mul, he_norm, mul_one]
  have hg_cont : Continuous g := by
    rw [hg]
    exact continuous_tsum (fun ξ => continuous_const.mul (he_cont ξ)) hsum
      (fun ξ y => by rw [norm_mul, he_norm, mul_one])
  have h1 : ∀ y, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ)‖ₑ = ‖g y‖ₑ := by
    intro y
    have : GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ) = ψ (⅟2 * (x ⬝ᵥ y)) * g y := by
      rw [hg, ← tsum_mul_left]
      unfold GlobalTheory.WeilM.thetaSum GlobalTheory.WeilM.schr
      congr 1; funext ξ
      subst ha he hemb
      simp only [AddChar.map_add_eq_mul]; ring
    rw [this, enorm_mul, ← ofReal_norm_eq_enorm (ψ _), hnorm, ENNReal.ofReal_one, one_mul]
  have hgsq_int : Integrable (fun y => ‖g y‖ ^ 2) (μ.restrict 𝓕₁) :=
    Integrable.of_bound (hg_cont.norm.pow 2).aestronglyMeasurable ((∑' ξ, ‖a ξ‖) ^ 2) (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hg_bd y) 2)
  have lhs : ∫⁻ y in 𝓕₁, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ)‖ₑ ^ 2 ∂μ =
      ENNReal.ofReal (∫ y in 𝓕₁, ‖g y‖ ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hgsq_int (ae_of_all _ fun y => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    rw [h1, ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hcomp : ∀ y, ((‖g y‖ ^ 2 : ℝ) : ℂ) =
      ∑' p : (κ → F) × (κ → F), a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y := by
    intro y
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [hg]
    rw [Complex.conj_tsum, tsum_mul_tsum_of_summable_norm (hsum_e y) (by simpa [norm_mul, he_norm] using hsum)]
    congr 1; funext p
    rw [he_sub, map_mul]; ring
  have hFint : ∀ p : (κ → F) × (κ → F),
      Integrable (fun y => a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y) (μ.restrict 𝓕₁) := fun p =>
    (Integrable.of_bound (he_cont _).aestronglyMeasurable 1 (ae_of_all _ fun y => (he_norm _ _).le)).const_mul _
  have hnormint : ∀ p : (κ → F) × (κ → F),
      ∫ y in 𝓕₁, ‖a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y‖ ∂μ = ‖a p.1‖ * ‖a p.2‖ * μ.real 𝓕₁ := by
    intro p
    simp only [norm_mul, he_norm, RCLike.norm_conj, mul_one]
    rw [setIntegral_const, smul_eq_mul]; ring
  have hsumint : Summable fun p : (κ → F) × (κ → F) =>
      ∫ y in 𝓕₁, ‖a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y‖ ∂μ := by
    simp_rw [hnormint]
    exact (hsum.mul_of_nonneg hsum (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_right _
  have horth : ∀ ζ : κ → F, ∫ y in 𝓕₁, e ζ y ∂μ = if ζ = 0 then (μ.real 𝓕₁ : ℂ) else 0 := by
    intro ζ
    split_ifs with hζ
    · subst hζ
      have : ∀ y, e 0 y = 1 := fun y => by simp [he, hemb]
      simp_rw [this]; rw [setIntegral_const]; simp
    · obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
        by_contra h; push_neg at h; exact hζ (funext h)
      haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := by
        refine Function.Surjective.countable (f := fun ρ : κ → F => (⟨emb ρ, ?_⟩ : GlobalTheory.ThetaParseval.ratVec F κ)) ?_
        · exact (GlobalTheory.ThetaParseval.mem_ratVec_iff _).2 ⟨ρ, by rw [hemb]⟩
        · rintro ⟨r, hr⟩
          obtain ⟨ρ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff r).1 hr
          exact ⟨ρ, by subst hemb; rfl⟩
      refine setIntegral_eq_zero_of_twist μ (GlobalTheory.ThetaParseval.ratVec F κ) hF (h := e ζ) ?_
        (c := Pi.single i (algebraMap F (AF F) (ζ i)⁻¹ * s0)) (a := ψ s0) ?_ hs0
      · intro r hr y
        obtain ⟨ρ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff r).1 hr
        simp only [he, dotProduct_add, AddChar.map_add_eq_mul]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [show emb ζ ⬝ᵥ (fun i => algebraMap F (AF F) (ρ i)) = algebraMap F (AF F) (ζ ⬝ᵥ ρ) by
          subst hemb; simp [dotProduct, map_sum, map_mul], htriv, one_mul]
      · intro y
        simp only [he, dotProduct_add, AddChar.map_add_eq_mul]
        congr 2
        rw [dotProduct_single, hemb]
        simp only
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
  have hFval : ∀ p : (κ → F) × (κ → F), ∫ y in 𝓕₁, a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y ∂μ =
      if p.1 = p.2 then ((‖a p.1‖ ^ 2 * μ.real 𝓕₁ : ℝ) : ℂ) else 0 := by
    intro p
    rw [integral_const_mul, horth]
    by_cases h : p.1 = p.2
    · rw [if_pos (sub_eq_zero.mpr h), if_pos h, h, Complex.mul_conj']; push_cast; ring
    · rw [if_neg (sub_ne_zero.mpr h), if_neg h, mul_zero]
  have hI : ∫ y in 𝓕₁, ‖g y‖ ^ 2 ∂μ = (∑' ξ, ‖a ξ‖ ^ 2) * μ.real 𝓕₁ := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    simp_rw [hcomp]
    rw [← integral_tsum_of_summable_integral_norm hFint hsumint]
    simp_rw [hFval]
    have hinj : Function.Injective (fun ξ : κ → F => (ξ, ξ)) := fun _ _ h => (Prod.ext_iff.1 h).1
    rw [← hinj.tsum_eq]
    · simp only [if_true]
      rw [← tsum_mul_right, Complex.ofReal_tsum]
    · intro p hp
      by_cases h : p.1 = p.2
      · exact ⟨p.1, Prod.ext rfl h⟩
      · exact absurd (if_neg h) hp
  have hsq : Summable fun ξ => ‖a ξ‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun ξ => by
        rw [sq]
        exact mul_le_mul_of_nonneg_right (hsum.le_tsum ξ (fun _ _ => norm_nonneg _)) (norm_nonneg _))
      (hsum.mul_left (∑' ξ, ‖a ξ‖))
  rw [lhs, hI, ENNReal.ofReal_mul (tsum_nonneg fun _ => sq_nonneg _), ofReal_measureReal hfin, mul_comm,
    ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsq]
  congr 1
  refine tsum_congr fun ξ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, ha, hemb]

end GlobalTheory.ThetaParsevalInner
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariableStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_adelicThetaSum_sq_parseval_second_variable : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (𝓕₁ : Set (κ → AF F)), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ x : (κ → AF F),
      ∫⁻ y in 𝓕₁, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ)‖ₑ ^ 2 ∂μ =
        μ 𝓕₁ * ∑' ξ : κ → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ₑ ^ 2 := by
  first | exact @GlobalTheory.ThetaParsevalInner.lintegral_thetaSum_schr_sq | exact GlobalTheory.ThetaParsevalInner.lintegral_thetaSum_schr_sq | (intros; apply GlobalTheory.ThetaParsevalInner.lintegral_thetaSum_schr_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsMulOfCondExp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqStepArith

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt)

theorem chrW_chs {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (x : (Fv D.host.F v)ˣ) :
    chrW (GlobalTheory.SqStep.chs G i j t).ν τ x = (nuH G t i j).loc (GlobalTheory.AdelicU.splitPrime τ)
      (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom x) := by
  have e : (GlobalTheory.SqStep.chs G i j t).ν = G.nu t i (j + 1) := by
    show (Lc.mu t (j + 1) * Lc.eta ^ _) / (G.ch.chi _ * Lc.eta ^ _) = _
    rw [mul_div_mul_right_eq_div]
    rfl
  show GlobalTheory.LFun.locChar (GlobalTheory.SqStep.chs G i j t).ν _ _ = _
  rw [e, GlobalTheory.LFun.locChar_eq_of_chrEq (chrEq_nu G t i j hL)]

theorem eps_mul_of_condExp {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)}
    (ν₀ ξ : (Fv F v)ˣ →* ℂˣ) (s : (Fv F v)ˣ) (z : ℤ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (ν₀ * ξ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀) :
    (ν₀ s : ℂ) * eps ψ ν₀ z * gauss ψ (ν₀ * ξ) =
      (((ξ (s * unifAt v ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀))⁻¹ : ℂˣ) : ℂ) * gauss ψ ν₀ *
        (((ν₀ * ξ) s : ℂ) * eps ψ (ν₀ * ξ) z) := by
  unfold eps
  rw [h]
  simp only [MonoidHom.mul_apply, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, mul_inv, Units.val_inv_eq_inv_val]
  have h1 : (ξ s : ℂ) ≠ 0 := Units.ne_zero _
  have h2 : (ξ (unifAt v) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp
  ring

theorem chs_T_base {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (i j : Fin D.R.m) : (GlobalTheory.SqStep.chs G i j μ₀).T = G.pl.S0 := by
  classical
  have hQ : Lc.Q μ₀ = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun PP hPP => ?_
    have h := (hL.Q_ram μ₀ PP).2 (Or.inl hPP)
    apply h
    rw [hL.xi_base]
    intro x _
    rfl
  have htw : twPl G μ₀ = ∅ := by
    unfold twPl locPl
    rw [hQ, Finset.union_empty]
    exact Finset.filter_false_of_mem fun w hw h => h hw
  show G.pl.S0 ∪ (twPl G μ₀).image _ = _
  rw [htw, Finset.image_empty, Finset.union_empty]

end GlobalTheory.SqStepArith
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterSizeConditionsNumericBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterSizeConditionsNumericBounds
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.SizesOfRows

theorem sizes_of_sizeRows : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → (bigN D : ℝ) ≤ large₂.sc.b ∧ (D.R.f : ℝ) ≤ large₂.sc.b ∧ 1 ≤ bigN D ∧ 1 ≤ D.R.f ∧ 2 ≤ D.R.m ∧ 1 ≤ D.host.rdE ∧ Real.log D.host.rdE ≤ Real.log large₂.sc.b / 100 ∧ 12 ≤ large₂.sc.b := by
  intro D large₂ h
  obtain ⟨_, _, hm4, hm44, _, hb, _, _, _, hrd, hcond, _, _, _⟩ := h
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have ht : D.R.k + D.R.m - 1 + 5 ≤ D.R.t := D.R.rank_add_five_le
  have hd : 1 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hf : 1 ≤ D.R.f := by
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hN1 : 1 ≤ D.R.N D.R.m := by simp only [Formalism.BasicNotions.Ranks.N]; omega
  have hbig2 : bigN D ≤ 2 * D.R.N D.R.m := by
    simp only [bigN, sLen, Formalism.BasicNotions.Ranks.N, Formalism.BasicNotions.Ranks.r]
    have h1 : D.R.k + D.R.m - 1 + 6 ≤ D.R.t + 1 := by omega
    have h2 : D.R.m * (D.R.k + D.R.m - 1 + 6) ≤ D.R.m * (D.R.t + 1) := Nat.mul_le_mul_left _ h1
    have e : D.R.m * (D.R.t + (D.R.k + D.R.m - 1 + 6) + 1) = D.R.m * (D.R.t + 1) + D.R.m * (D.R.k + D.R.m - 1 + 6) := by ring
    omega
  have hmR : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hm44
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hNR : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hN1
  have hdR : (1 : ℝ) ≤ (D.host.d : ℝ) := by exact_mod_cast hd
  have hbigR : (bigN D : ℝ) ≤ 2 * (D.R.N D.R.m : ℝ) := by exact_mod_cast hbig2
  have hN2 : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
  have hP1 : (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
    have a : (D.R.N D.R.m : ℝ) ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
      have : (D.R.N D.R.m : ℝ) ^ 2 ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
      have : D.R.f * (D.R.N D.R.m : ℝ) ^ 2 ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by nlinarith
      linarith
    have := mul_le_mul_of_nonneg_left a (by linarith : (0:ℝ) ≤ D.R.m)
    linarith
  have hP2 : (D.R.f : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
    have : (1 : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
      have : (1:ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
      nlinarith
    nlinarith
  have hmN : 2 * (D.R.N D.R.m : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) := by nlinarith
  have hrd1 : 1 ≤ D.host.rdE := Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Pm.one_le_rdE D
  have hlogb : Real.log large₂.sc.b = large₂.sc.L := by
    show Real.log (Real.exp large₂.sc.L) = large₂.sc.L
    exact Real.log_exp _
  refine ⟨by linarith, by linarith, by simp only [bigN]; omega, hf, by omega, hrd1, ?_, ?_⟩
  · rw [hlogb]; linarith
  · have : (12 : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) := by nlinarith
    linarith

end GlobalTheory.SizesOfRows
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterSizeConditionsNumericBoundsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameterSizeConditions_numericBounds : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → (bigN D : ℝ) ≤ large₂.sc.b ∧ (D.R.f : ℝ) ≤ large₂.sc.b ∧ 1 ≤ bigN D ∧ 1 ≤ D.R.f ∧ 2 ≤ D.R.m ∧ 1 ≤ D.host.rdE ∧ Real.log D.host.rdE ≤ Real.log large₂.sc.b / 100 ∧ 12 ≤ large₂.sc.b := by
  first | exact @GlobalTheory.SizesOfRows.sizes_of_sizeRows | exact GlobalTheory.SizesOfRows.sizes_of_sizeRows | (intros; apply GlobalTheory.SizesOfRows.sizes_of_sizeRows <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteModuleGradedQuantumDet
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.MidBlock

section Alg

variable {A A' : Type} [Ring A] [Algebra ℂ A] [Ring A'] [Algebra ℂ A']

theorem qdet_map (φ : A →ₐ[ℂ] A') {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) :
    φ (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => φ (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor Formalism.REAL.Tm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3
  funext k
  simp only [Function.comp_apply, map_add, apply_ite φ, AlgHom.commutes, map_zero]

theorem qdet_mem (S : Subalgebra ℂ A) {n : ℕ} {E : Fin n → Fin n → A} (h : ∀ a b, E a b ∈ S) (u : ℂ) :
    Formalism.REAL.qdet E u ∈ S := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  refine Subalgebra.sum_mem _ fun σ _ =>
    Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (Subalgebra.list_prod_mem _ ?_)
  intro x hx
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  unfold Formalism.REAL.Tm
  refine Subalgebra.add_mem _ ?_ (h _ _)
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.zero_mem _

theorem comm_qdet {n : ℕ} {E : Fin n → Fin n → A} {z : A} (h : ∀ a b, Commute z (E a b)) (u : ℂ) :
    Commute z (Formalism.REAL.qdet E u) := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  refine Commute.sum_right _ _ _ fun σ _ => Commute.mul_right (Int.cast_commute _ _).symm ?_
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hy
  unfold Formalism.REAL.Tm
  exact Commute.add_right (GlobalTheory.CapHC.ite_algebraMap_comm _ _ _).symm (h _ _)

theorem glComm {n : ℕ} {X : Fin n → Fin n → A} (hX : Formalism.REAL.GlRel X) {a b c d : Fin n} (hbc : b ≠ c)
    (hda : d ≠ a) : Commute (X a b) (X c d) := by
  have h := hX a b c d
  rw [if_neg hbc, if_neg hda, sub_zero] at h
  exact sub_eq_zero.1 h

end Alg

section Stab

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def stab (N : Submodule ℂ M) : Subalgebra ℂ (Module.End ℂ M) where
  carrier := {f | ∀ x ∈ N, f x ∈ N}
  mul_mem' := fun ha hb x hx => ha _ (hb x hx)
  add_mem' := fun ha hb x hx => N.add_mem (ha x hx) (hb x hx)
  algebraMap_mem' := fun c x hx => by simpa [Module.algebraMap_end_apply] using N.smul_mem c hx

theorem mem_stab {N : Submodule ℂ M} {f : Module.End ℂ M} : f ∈ stab N ↔ ∀ x ∈ N, f x ∈ N := Iff.rfl

theorem upperSpan_maps {N K : Submodule ℂ M} {r m : ℕ} (Y : Fin (r + m) → Fin (r + m) → stab N)
    (hY : ∀ p q, ∀ x ∈ N, (Y (Fin.castAdd m p) (Fin.natAdd r q) : Module.End ℂ M) x ∈ K)
    {y : stab N} (hy : y ∈ GlobalTheory.CapHC.upperSpan Y) : ∀ x ∈ N, (y : Module.End ℂ M) x ∈ K := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, q, w, rfl⟩ := hy
    intro x hx
    exact hY p q _ (mem_stab.1 w.2 x hx)
  | zero => intro x _; simp
  | add a b _ _ ha hb => intro x hx; simpa using K.add_mem (ha x hx) (hb x hx)
  | smul c a _ ha => intro x hx; simpa using K.smul_mem c (ha x hx)

end Stab

section Main

end Main

end GlobalTheory.LeviHC.MidBlock
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialHeckeLFunctionSquareEqPrimitive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialHeckeLFunctionSquareEqPrimitive
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqStep

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

theorem nuH_not_unrAt_above {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : P.under (𝓞 D.host.F) ∈ G.pl.S0) : ¬ (nuH G t i j).UnrAt P := by
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have e : G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH t * (nuH G t i j)⁻¹ := by
    rw [← div_eq_mul_inv, nuH, div_div_cancel]
  intro hn
  rcases G.pl.mem_S0_of_sum_eq.1 hP with hv | hv
  · have hmu : (L.C.mu0 j).UnrAt P := (L.C.isMu0 j).unr _ fun k hk => G.ch.basePlace_not_mem_chiGridBadPlaces (by
      have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
        show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
        rw [map_natCast]; exact hk
      rw [hv] at h
      refine (S1_mem_OmF D).2 ?_
      fin_cases k
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
    have hxi : (L.xiH t).UnrAt P := by
      by_contra hc
      rcases (hL.Q_ram t _).1 hc with h | ⟨PP', h, hc'⟩
      · exact G.pl.levelPlace_ne_basePlace t _ h hv
      · exact G.pl.levelPlace_ne_basePlace t PP' h ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc').trans hv)
    apply (G.ch.lev0 _ hm.1 hm.2 _ hv).2
    rw [e]
    exact (hmu.mul hxi).mul hn.inv
  · apply (G.ch.lev1 _ hm.1 hm.2 P hv).2
    rw [e]
    exact (Formalism.L2.Host.HChar.LevelLe.mul ((L.C.isMu0 j).tame P) (hL.xi_tame t P)).mul (hn.levelLe 1).inv

theorem heckeL_eq_of_ram {K : Type} [Field K] [NumberField K] {χ : HChar K} {S : Set (HeightOneSpectrum (𝓞 K))}
    (hr : ∀ w ∈ S, ¬ χ.UnrAt w) {Λ : ℂ → ℂ} (hΛ : IsHeckeL χ Λ) {s : ℂ} (hs : 1 < s.re) :
    GlobalTheory.LFun.heckeL S χ s = Λ s := by
  have e : ({w | w ∉ S} : Set (HeightOneSpectrum (𝓞 K))).mulIndicator (GlobalTheory.CMVal.eulerFactor χ s) =
      GlobalTheory.CMVal.eulerFactor χ s :=
    Set.mulIndicator_eq_self.2 fun w hw => by
      by_contra h
      exact hw (if_neg (hr w (not_not.1 h)))
  have h := (hasProd_subtype_iff_mulIndicator (s := {w | w ∉ S}) (f := GlobalTheory.CMVal.eulerFactor χ s)).2
    (by rw [e]; exact hΛ.2 s hs)
  unfold GlobalTheory.LFun.heckeL GlobalTheory.LFun.eulerProd
  simp only [GlobalTheory.LFun.locL_heckeFam]
  exact h.tprod_eq

theorem chs_nu (G : GridData L sc) (i j : Fin D.R.m) (t : T) : (chs G i j t).ν = G.nu t i (j + 1) :=
  mul_div_mul_right_eq_div _ _ _

theorem charL_chs_eq : GBig fun {D} T _ _ G _ _ _ _ => ∀ (i j : Fin D.R.m) (t : T) (s : ℕ) (Λ : ℂ → ℂ), 2 ≤ s → IsHeckeL (nuH G t i j) Λ →
    GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (s : ℂ) = Λ s := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D _ _ _ _ T Lc μ₀ hL G i j t s Λ hs hΛ => ?_⟩⟩
  rw [chs_nu, GlobalTheory.LFun.charL_eq_of_chrEq (chrEq_nu G t i j hL)]
  refine heckeL_eq_of_ram (fun w hw => nuH_not_unrAt_above hL G t i j w hw) hΛ ?_
  rw [Complex.natCast_re]
  exact_mod_cast (by omega : 1 < s)

end GlobalTheory.SqStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialHeckeLFunctionSquareEqPrimitiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialHeckeLFunction_square_eq_primitive : GBig fun {D} T _ _ G _ _ _ _ => ∀ (i j : Fin D.R.m) (t : T) (s : ℕ) (Λ : ℂ → ℂ), 2 ≤ s → IsHeckeL (nuH G t i j) Λ →
    GlobalTheory.LFun.charL (GlobalTheory.SqStep.chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) (s : ℂ) = Λ s := by
  first | exact @GlobalTheory.SqStep.charL_chs_eq | exact GlobalTheory.SqStep.charL_chs_eq | (intros; apply GlobalTheory.SqStep.charL_chs_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeAdditive
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

open Matrix GlobalTheory.SmoothForms
open GlobalTheory.Orb (archMat)

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.LeviHC.LineLie

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {w : InfinitePlace F}

section Chart

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

def sigA (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := A⁻¹ * Xᴴ * A
  map_add' X Y := by rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    change A⁻¹ * (c • X)ᴴ * A = c • (A⁻¹ * Xᴴ * A)
    rw [conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul]

abbrev LieL (A : Matrix (Fin n) (Fin n) ℂ) : Type := ↥(GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU A).toSubmodule

def jA (A : Matrix (Fin n) (Fin n) ℂ) : LieL A →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU A).toSubmodule.subtype


open Classical in
variable (σ J) in
def secA (τ : EmbOver E w) (u : Matrix (Fin n) (Fin n) ℂ) : GAd σ J :=
  if hu : ∃ y : GArch σ J w, archMat σ J τ y = u then embArch σ J w hu.choose else 1

theorem archMat_injective (h : IsCMExt F E σ) (τ : EmbOver E w) : Function.Injective (archMat σ J τ) := fun a b e => by
  rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, GlobalTheory.Orb.archMat_eq_archEquiv J h] at e
  exact (archEquiv J h τ).injective (Subtype.ext (Units.ext e))

theorem secA_archMat (h : IsCMExt F E σ) (τ : EmbOver E w) (y : GArch σ J w) :
    secA σ J τ (archMat σ J τ y) = embArch σ J w y := by
  have hu : ∃ y' : GArch σ J w, archMat σ J τ y' = archMat σ J τ y := ⟨y, rfl⟩
  rw [secA, dite_eq_left hu, archMat_injective h τ hu.choose_spec]

theorem exists_archMat (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) {u : Matrix (Fin n) (Fin n) ℂ}
    (hu : sigA (J.map τ.1) u * u = 1) : ∃ y : GArch σ J w, archMat σ J τ y = u := by
  have hA := isUnit_det_map hJ τ.1
  have hu1 : (J.map τ.1)⁻¹ * uᴴ * J.map τ.1 * u = 1 := hu
  have hu2 : uᴴ * J.map τ.1 * u = J.map τ.1 := by
    have := congrArg (J.map τ.1 * ·) hu1
    simpa only [← Matrix.mul_assoc, mul_nonsing_inv _ hA, Matrix.one_mul, Matrix.mul_one] using this
  let v : GL (Fin n) ℂ := ⟨u, (J.map τ.1)⁻¹ * uᴴ * J.map τ.1, mul_eq_one_comm.1 hu1, hu1⟩
  refine ⟨(archEquiv J h τ).symm ⟨v, show _ * _ * _ = _ from hu2⟩, ?_⟩
  rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, MulEquiv.apply_symm_apply]

theorem isLieData (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) :
    IsLieData (sigA (J.map τ.1)) (jA (J.map τ.1)) (secA σ J τ) := by
  have hA := isUnit_det_map hJ τ.1
  have hAh := conjTranspose_map h hJ τ.1
  have anti : ∀ a b, sigA (J.map τ.1) (a * b) = sigA (J.map τ.1) b * sigA (J.map τ.1) a := fun a b => by
    change _ * (a * b)ᴴ * _ = (_ * bᴴ * _) * (_ * aᴴ * _)
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hA]
  refine ⟨anti, ?_, fun a => ?_, Subtype.val_injective, fun X => ⟨fun hX => ?_, ?_⟩, fun a b ha hb => ?_⟩
  · change (J.map τ.1)⁻¹ * (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * J.map τ.1 = 1
    rw [conjTranspose_one, Matrix.mul_one, nonsing_inv_mul _ hA]
  · change _ * (_ * aᴴ * _)ᴴ * _ = a
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hAh]
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hA, nonsing_inv_mul _ hA, Matrix.mul_one]
  · refine ⟨⟨X, ?_⟩, rfl⟩
    have h1 : (J.map τ.1)⁻¹ * Xᴴ * J.map τ.1 = -X := hX
    change Xᴴ * J.map τ.1 + J.map τ.1 * X = 0
    rw [← mul_nonsing_inv_cancel_left _ (Xᴴ * J.map τ.1) hA, ← Matrix.mul_assoc (J.map τ.1)⁻¹, h1, Matrix.mul_neg,
      neg_add_cancel]
  · rintro ⟨Y, rfl⟩
    have h1 : Y.1ᴴ * J.map τ.1 + J.map τ.1 * Y.1 = 0 := Y.2
    change _ * Y.1ᴴ * _ = -Y.1
    rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h1, Matrix.mul_neg, nonsing_inv_mul_cancel_left _ _ hA]
  · have hab : sigA (J.map τ.1) (a * b) * (a * b) = 1 := by
      rw [anti, Matrix.mul_assoc, ← Matrix.mul_assoc (sigA (J.map τ.1) a), ha, Matrix.one_mul, hb]
    obtain ⟨ya, rfl⟩ := exists_archMat h hJ τ ha
    obtain ⟨yb, rfl⟩ := exists_archMat h hJ τ hb
    rw [← map_mul, secA_archMat h, secA_archMat h, secA_archMat h, map_mul]

theorem hasLog (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) :
    HasLog (sigA (J.map τ.1)) (jA (J.map τ.1)) :=
  GlobalTheory.T.hasSmoothLogNearOne_of_isUnitaryLieExpData _ _ _ _ _ _ (isLieData h hJ τ)

theorem isLineOf_expMap (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) (Y : LieL (J.map τ.1)) :
    IsLineOf σ J τ Y.1 fun t => expMap (jA (J.map τ.1)) (secA σ J τ) (t • Y) := fun t => by
  have hA := isUnit_det_map hJ τ.1
  have hY : (t • Y.1)ᴴ * J.map τ.1 + J.map τ.1 * (t • Y.1) = 0 := by
    have h1 : Y.1ᴴ * J.map τ.1 + J.map τ.1 * Y.1 = 0 := Y.2
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  have h1 : (NormedSpace.exp (t • Y.1))ᴴ * J.map τ.1 * NormedSpace.exp (t • Y.1) = J.map τ.1 :=
    GlobalTheory.SmoothForms.exp_mem_UH hA hY
  have hu : sigA (J.map τ.1) (NormedSpace.exp (t • Y.1)) * NormedSpace.exp (t • Y.1) = 1 := by
    change (J.map τ.1)⁻¹ * _ * J.map τ.1 * _ = 1
    rw [Matrix.mul_assoc _ _ (J.map τ.1), Matrix.mul_assoc, h1, nonsing_inv_mul _ hA]
  obtain ⟨y, hy⟩ := exists_archMat h hJ τ hu
  refine ⟨y, ?_, hy⟩
  change secA σ J τ (NormedSpace.exp (t • Y.1)) = _
  rw [← hy, secA_archMat h]

theorem sm_of_isSm (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) {f : GAd σ J → ℂ} (hf : IsSm σ J f) :
    Sm (expMap (jA (J.map τ.1)) (secA σ J τ)) f := by
  rw [GlobalTheory.T.smoothInExponentialCoords_iff_first_second_kind _ _ _ _ _ _ (isLieData h hJ τ) (hasLog h hJ τ) Set.univ Submodule.span_univ]
  intro k Y _ g
  exact hf k (fun i t => expMap (jA (J.map τ.1)) (secA σ J τ) (t • Y i))
    (fun i => (isLineOf_expMap h hJ τ (Y i)).isRealLine h) g

end Chart

end GlobalTheory.LeviHC.LineLie

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStepK

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Geo Plane Chars RealMaps IsMatched IsConst)

variable {D : D7}

def InLat (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (z : V.V) : Prop := V.frame.equivFun z ∈ Λ

def PlaneSplit (S S₁ : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V) (x y : S.V) : Prop :=
  S.rank = S₁.rank + 2 ∧ Formalism.BasicNotions.HSpace.IsIsomEmb S₁ S ι ∧ S.hD x x = 0 ∧ S.hD y y = 0 ∧ S.hD x y = 1 ∧
    (∀ u, S.hD (ι u) x = 0 ∧ S.hD (ι u) y = 0) ∧ (∀ u, InLat S₁ Λ₁ u ↔ InLat S Λ (ι u)) ∧
    ∀ z, InLat S Λ z → ∃ (s r : D.host.E) (u : S₁.V), InLat S Λ (s • x) ∧ InLat S Λ (r • y) ∧ InLat S₁ Λ₁ u ∧
      z = s • x + ι u + r • y

def IsStepB {T : Type} {A A' WW B' WW₁ : HSp D} (X : Tri T A A' WW) (Y : Tri T A B' WW₁) : Prop :=
  Y.rA = X.rA ∧ (∃ ι x y, PlaneSplit A' B' X.rA'.Λ Y.rA'.Λ ι x y) ∧ ∃ ι x y, PlaneSplit WW WW₁ X.rW.Λ Y.rW.Λ ι x y

def HasConstR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {a a' : ℕ} (Γ : Geo σ a a') (R : RealMaps F a a') (χ : Chars F E) (κ : ℂ) : Prop :=
  ∃ om om' Rf, IsMatched B Γ χ om om' R Rf ∧ IsConst B Γ χ om om' R Rf κ

end GlobalTheory.SqStepK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySmallHeisenbergLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySmallHeisenbergLattice
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.FinSuppHeis

theorem norm_le_of_finDiv {F : Type} [Field F] [NumberField F] {N : ℕ} {a : AF F} (h : GlobalTheory.FinSupp.FinDiv F N a)
    (v : HeightOneSpectrum (𝓞 F)) : ‖evFin F v a‖ ≤ ‖(N : Fv F v)‖ := by
  obtain ⟨b, hb, e⟩ := h v
  rw [e, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) ((GlobalTheory.SuppDen.norm_le_one_iff_mem v b).mpr hb)

theorem heis_fix_finDiv : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ Φ ∈ schA F κ, ∃ N : ℕ, 1 ≤ N ∧ ∀ w : (κ → AF F) × (κ → AF F),
      (∀ i, (w.1 i).1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N (w.1 i) ∧ (w.2 i).1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N (w.2 i)) →
      schr ψ w Φ = Φ := by
  intro F _ _ κ _ ψ hψ Φ hΦ
  obtain ⟨m₀, hm₀, h⟩ := GlobalTheory.ThetaLevel.heis_fix (F := F) (κ := κ) ψ hψ Φ hΦ
  refine ⟨m₀, hm₀, fun w hw => ?_⟩
  exact h w.1 w.2 ⟨fun i => (hw i).1, fun v i => norm_le_of_finDiv (hw i).2.1 v⟩
    ⟨fun i => (hw i).2.2.1, fun v i => norm_le_of_finDiv (hw i).2.2.2 v⟩

end GlobalTheory.FinSuppHeis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySmallHeisenbergLatticeStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartz_fixed_by_small_heisenberg_lattice : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ Φ ∈ schA F κ, ∃ N : ℕ, 1 ≤ N ∧ ∀ w : (κ → AF F) × (κ → AF F),
      (∀ i, (w.1 i).1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N (w.1 i) ∧ (w.2 i).1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N (w.2 i)) →
      schr ψ w Φ = Φ := by
  first | exact @GlobalTheory.FinSuppHeis.heis_fix_finDiv | exact GlobalTheory.FinSuppHeis.heis_fix_finDiv | (intros; apply GlobalTheory.FinSuppHeis.heis_fix_finDiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelWFormsEqPrincipalForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelWFormsEqPrincipalForms
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.LevW


open MeasureTheory IsDedekindDomain NumberField Matrix Polynomial in
open scoped TensorProduct InnerProductSpace in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.LevW.levW_of_parts : _root_.GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Hk3.HoweUnram → ∀ {D : _root_.Formalism.BasicNotions.D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : _root_.Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : _root_.Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : _root_.Formalism.IndefR.Links.Face3 D A3) {s : ℕ}, _root_.GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, _root_.Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, _root_.Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → _root_.Formalism.L2.DIV.GoodStable A3.A.X → _root_.GlobalTheory.CuspMult.CuspDecomp D → _root_.GlobalTheory.CuspMult.MultEq R.toRealDat → R.PGEquiv F → (∀ b, (_root_.Formalism.IndefR.Cx.lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmA → _root_.Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → R.toRealDat.LUnif → R.PLevW F := by
  intro hDecay hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hConv hOk hChar hEx hInert hStable hIrr hMult hEquiv hPos hScal hThmA hLift hUnif
  have hCarry := _root_.GlobalTheory.Hk3.carries_of_rows_top hDecay hHowe R F hConv hOk hChar hEx hInert hEquiv hPos
  have hSum := _root_.GlobalTheory.SpanW.iSup_wp3_eq_range_eH R F hOk hChar hEx
    (_root_.GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hDecay _) hStable hIrr hMult hCarry
  have hBlock := _root_.GlobalTheory.Hk3.inBlock_of_cuspRapidDecay hDecay R F hConv hOk hChar hEx hEquiv
  intro j
  rw [_root_.GlobalTheory.WType.range_w0C_type R F hOk hChar hEx hUnif j,
    _root_.GlobalTheory.WgLift.principal_lift_forms_eq_good_forms R F hOk hChar hEx hSum hScal hThmA hLift hBlock j]
  rfl

end GlobalTheory.LevW

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelWFormsEqPrincipalFormsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseLevelW_forms_eq_principalForms : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmA → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → R.toRealDat.LUnif → R.PLevW F := by
  first | exact @GlobalTheory.LevW.levW_of_parts | exact GlobalTheory.LevW.levW_of_parts | (intros; apply GlobalTheory.LevW.levW_of_parts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicEqSpanPure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicEqSpanPure
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylSpan

theorem pure_eq_pureA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) :
    pure f φ = pureA F (⇑f) (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => evalV F v (y i)) := by
  rfl

theorem schA_eq_span_pure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    schA F κ = Submodule.span ℂ {Φ | ∃ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) ∧
      (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) ∧ Φ = pure f φ} := by
  intro F _ _ κ _
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro Φ ⟨f, g, hg, rfl⟩
    let L : ((κ → FiniteAdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ → AdeleRing (𝓞 F) F) → ℂ) :=
      { toFun := fun g => pureA F (⇑f) g
        map_add' := fun a b => by funext x; simp [pureA, mul_add]
        map_smul' := fun c a => by funext x; simp [pureA]; ring }
    have h := GlobalTheory.SBSpan.mem_span_restrictedProd F κ g hg
    have h2 : L g ∈ Submodule.map L (Submodule.span ℂ _) := Submodule.mem_map_of_mem h
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨p, ⟨φ, hφ, hcof, rfl⟩, rfl⟩
    exact ⟨f, φ, hφ, hcof, (pure_eq_pureA f φ).symm⟩
  · refine Submodule.span_le.2 ?_
    rintro Φ ⟨f, φ, hφ, hcof, rfl⟩
    refine Submodule.subset_span ⟨f, _, ?_, pure_eq_pureA f φ⟩
    exact ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ hcof,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ hcof⟩

end GlobalTheory.WeylSpan

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicEqSpanPureStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_adelic_eq_span_pure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    schA F κ = Submodule.span ℂ {Φ | ∃ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) ∧
      (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) ∧ Φ = pure f φ} := by
  first | exact @GlobalTheory.WeylSpan.schA_eq_span_pure | exact GlobalTheory.WeylSpan.schA_eq_span_pure | (intros; apply GlobalTheory.WeylSpan.schA_eq_span_pure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrConjApply
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.FrameTransport

def adSwap (D : D7) : StandardLatticesGL3.AE D →+* Lev.EAf D :=
  (Lev.swapAE D).comp (GlobalTheory.BotFormula.toAfE D).toRingHom

def inclEAf (D : D7) : D.host.E →+* Lev.EAf D := Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F)

def frConj {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) : GL (Fin n) (StandardLatticesGL3.AE D) →* GL (Fin n) (Lev.EAf D) :=
  (MulAut.conj (Formalism.UG.bc (inclEAf D) fr)).toMonoidHom.comp (Formalism.UG.bc (adSwap D))

theorem frConj_apply {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (h : GL (Fin n) (StandardLatticesGL3.AE D)) :
    frConj fr h = Formalism.UG.bc (inclEAf D) fr * Formalism.UG.bc (adSwap D) h * (Formalism.UG.bc (inclEAf D) fr)⁻¹ := rfl

end GlobalTheory.FrameTransport

end
end

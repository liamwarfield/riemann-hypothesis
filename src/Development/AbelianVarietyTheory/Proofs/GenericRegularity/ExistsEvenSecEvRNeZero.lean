module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueExistsUniqueNaturalOfLaws
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaProductRuleValueEqProductFormOfTestRing
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormSectionEqFlagDomainNorm
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousOnHolomorphicFramedFamily

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsEvenSecEvRNeZero
set_option autoImplicit false

noncomputable section

open NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.EtaForm

namespace GlobalTheory.Reg

theorem exists_even_sec_evR_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)), ∃ n : ℕ, 0 < n ∧ Even n ∧ ∃ f ∈ sec Xo c 0 n, evR Xo c f y ≠ 0 := by
  intro E _ _ _ H Dw l Xo c σ y
  have hR : Odd 3 := by decide
  have h1 : 1 < 3 := by decide
  obtain ⟨hfG, hfL, -⟩ := GlobalTheory.EtaCard.card_levGrp_and_span E H Dw 3 h1
  letI hFin : Fintype (LatMod Dw 3) := Fintype.ofFinite _
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c
  obtain ⟨cf, -, hne⟩ := GlobalTheory.EtaForm.exists_small_coeff_etaValAt_ne_zero GlobalTheory.firstFiveLaws.1 E H Dw l Xo c 3 hR h1
    2 0 (CAt σ) 1 (fun _ => y)
  obtain ⟨⟨f, hrule, -⟩, hsec⟩ := GlobalTheory.EtaForm.isEtaRule_existsUnique_mem_sec GlobalTheory.firstFiveLaws.1 E H Dw l Xo c 3 hR
    (Fin 2 → LatMod Dw 3) 2 (fun j => (cf j : ℤ)) (shiftFam 3 0)
  refine ⟨2 * Nat.card (LevGrp Dw (3 ^ 4)), Nat.mul_pos two_pos Nat.card_pos, even_two_mul _, f, hsec f hrule, ?_⟩
  exact hne 0 _ (GlobalTheory.EtaForm.etaValAt_evR_of_fromTest E H Dw l Xo c 3 hR _ _ _ _ f hrule (CAt σ) y (hT _ _)).1

end GlobalTheory.Reg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormBddAboveISupEqCuspFormSupNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormBddAboveISupEqCuspFormSupNorm
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm.SupNorm

theorem bdd_and_iSup_eq {α β : Type} (g : α → ℝ) (h : β → ℝ) (C : ℝ) (hC : 0 ≤ C) (hh : ∀ b, 0 ≤ h b)
    (h1 : ∀ a, ∃ b, g a = C * h b) (h2 : ∀ b, ∃ a, g a = C * h b)
    (hfin : (⨆ b, ENNReal.ofReal (h b)) ≠ ⊤) :
    BddAbove (Set.range g) ∧ (⨆ a, g a) = C * (⨆ b, ENNReal.ofReal (h b)).toReal := by
  have hle : ∀ b, h b ≤ (⨆ b, ENNReal.ofReal (h b)).toReal := fun b =>
    (ENNReal.ofReal_le_iff_le_toReal hfin).1 (le_iSup (fun b => ENNReal.ofReal (h b)) b)
  have hr : Set.range g = Set.range fun b => C * h b := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := h1 a
      exact ⟨b, hb.symm⟩
    · rintro ⟨b, rfl⟩
      exact h2 b
  refine ⟨⟨C * (⨆ b, ENNReal.ofReal (h b)).toReal, ?_⟩, ?_⟩
  · rw [hr]
    rintro _ ⟨b, rfl⟩
    exact mul_le_mul_of_nonneg_left (hle b) hC
  · rw [ENNReal.toReal_iSup (fun b => ENNReal.ofReal_ne_top), Real.mul_iSup_of_nonneg hC]
    unfold iSup
    rw [hr]
    simp only [ENNReal.toReal_ofReal (hh _)]

theorem supBdd_and_supR_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ a n, Dom a n → ∀ f ∈ Formalism.L2.PjFree.cusp Xo c U a n, SupBdd Xo c fn a n f ∧ ∀ σ, supR Xo c fn σ a n f = Formalism.L2.PjFree.supC Xo c U xR (Formalism.L2.PjFree.goodOf c σ) a n f := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn hx hfn a n hd f hf
  obtain ⟨-, htie, hconj⟩ := GlobalTheory.T.pointwise_norm_section_eq_flagDomain_norm E H Dw l Xo c r U hU xR fn hx hfn
  have hs : f ∈ sec Xo c a n := Formalism.L2.PjFree.cusp_le_sec Xo c U a n hf
  have hB : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  let N : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → ℝ := fun σ =>
    ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f
  have hgood : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ →
      BddAbove (Set.range (N σ)) ∧ (⨆ y, N σ y) = Formalism.L2.PjFree.supC Xo c U xR σ a n f := by
    intro σ hσ
    refine bdd_and_iSup_eq (N σ)
      (fun p : Formalism.L2.PjFree.FPt (U σ).X =>
        ((U σ).X p.1).pnorm (Formalism.L2.PjFree.laU (U σ) a n p.1) (Formalism.L2.PjFree.rdU (U σ) f p.1) p.2)
      (Formalism.L2.PjFree.lieFac Dw xR a) (Formalism.L2.PjFree.lieFac_pos Dw xR a).le
      (fun p => mul_nonneg (norm_nonneg _) (Formalism.L2.PjFree.pnorm_fac_nonneg _ _ _)) (fun y => ?_) (fun p => ?_)
      (Formalism.L2.PjFree.supE_cusp_ne_top hσ hf)
    · obtain ⟨k, x, t, ht⟩ := (hU σ hσ).2.2.1 y
      exact ⟨⟨k, x⟩, htie σ hσ k x t y ht a n hd f hs⟩
    · exact ⟨(U σ).un p.1 p.2, htie σ hσ p.1 p.2 1 _
        ((GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)).1 _) a n hd f hs⟩
  have hsub : ∀ σ τ : c.F →+* ℂ, τ = (starRingEnd ℂ).comp σ → Set.range (N σ) ⊆ Set.range (N τ) := by
    rintro σ τ rfl _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c _ _ (conjAlg σ) y
    exact ⟨z, hconj σ y z hz a n f hs⟩
  have hr : ∀ σ : c.F →+* ℂ, Set.range (N σ) = Set.range (N (Formalism.L2.PjFree.goodOf c σ)) := by
    intro σ
    by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
    · have e : Formalism.L2.PjFree.goodOf c σ = σ := if_pos hσ
      exact (hsub _ _ rfl).trans (hsub _ _ (by rw [e]; ext x; simp)) |>.antisymm
        ((hsub _ _ rfl).trans (hsub _ _ (by rw [e]; ext x; simp)))
    · have e : Formalism.L2.PjFree.goodOf c σ = (starRingEnd ℂ).comp σ := if_neg hσ
      exact (hsub _ _ e).antisymm (hsub _ _ (by rw [e]; ext x; simp))
  refine ⟨fun σ => ?_, fun σ => ?_⟩
  · show BddAbove (Set.range (N σ))
    rw [hr σ]
    exact (hgood _ (Formalism.L2.PjFree.goodEmb_goodOf c σ)).1
  · show sSup (Set.range (N σ)) = _
    rw [hr σ]
    exact (hgood _ (Formalism.L2.PjFree.goodEmb_goodOf c σ)).2

end GlobalTheory.FrameNorm.SupNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormBddAboveISupEqCuspFormSupNormStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointwiseNorm_bddAbove_iSup_eq_cuspForm_supNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ a n, Dom a n → ∀ f ∈ Formalism.L2.PjFree.cusp Xo c U a n, SupBdd Xo c fn a n f ∧ ∀ σ, supR Xo c fn σ a n f = Formalism.L2.PjFree.supC Xo c U xR (Formalism.L2.PjFree.goodOf c σ) a n f := by
  first | exact @GlobalTheory.FrameNorm.SupNorm.supBdd_and_supR_eq | exact GlobalTheory.FrameNorm.SupNorm.supBdd_and_supR_eq | (intros; apply GlobalTheory.FrameNorm.SupNorm.supBdd_and_supR_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousOnSmoothChart
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousOnSmoothChart
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm

theorem fn_continuousOn_good {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r)
    (hU : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) (xR : ℝ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (hx : 0 < xR) (hfn : FnPin U xR fn)
    (σ : c.F →+* ℂ) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (A : Type) [CommRing A] [Algebra c.F A] [Algebra.Smooth c.F A]
    (yA : FrPt Xo c A) (X : Type) [TopologicalSpace X] (W : Set X) (φ : X → (A →ₐ[c.F] CAt σ))
    (y : X → FrPt Xo c (CAt σ)) (hφ : ∀ a, ContinuousOn (fun x => Formalism.L2.PjFree.toC (φ x a)) W)
    (hy : ∀ x ∈ W, FrMap (φ x) yA (y x)) (i : Ix Dw) : ContinuousOn (fun x => |fn σ (y x) i|) W := by
  classical
  intro x₀ hx₀
  let ρ : X → (A →+* ℂ) := fun x => (φ x).toRingHom
  have hρ : ∀ x, (ρ x).comp (algebraMap c.F A) = σ := fun x => RingHom.ext fun a => (φ x).commutes a
  have hρc : ∀ a, ContinuousOn (fun x => ρ x a) W := hφ
  obtain ⟨m, s, B, ψ, S, ε, hB, hε, hψ, hd, hnear⟩ := GlobalTheory.T.exists_holomorphic_family_of_ringHom_near c.F A σ (ρ x₀) (hρ x₀)
  let ψ' : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ) := fun b =>
    if h : b ∈ B then
      { (show A →+* CAt σ from ψ b) with commutes' := fun a => RingHom.congr_fun (hψ b h).1 a }
    else φ x₀
  have hψ' : ∀ b ∈ B, ∀ a, Formalism.L2.PjFree.toC (ψ' b a) = ψ b a := by
    intro b hb a
    simp only [ψ', dif_pos hb]
    rfl
  choose z hz using fun b => GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c A (CAt σ) (ψ' b) yA
  have hcont := GlobalTheory.T.frameNorms_continuousOn_holomorphic_framedFamily E H Dw l Xo c r U hU xR fn hx hfn σ hσ A yA m B ψ' z hB
    (fun a => (hd a).congr fun b hb => hψ' b hb a) (fun b _ => hz b) i
  let p : X → (Fin m → ℂ) := fun x j => ρ x (s j)
  have hp : ContinuousWithinAt p W x₀ := continuousWithinAt_pi.2 fun j => hρc (s j) x₀ hx₀
  have hev : ∀ᶠ x in nhdsWithin x₀ W, ∀ a ∈ S, ‖ρ x a - ρ x₀ a‖ < ε := by
    rw [Filter.eventually_all_finset]
    intro a _
    have := Metric.tendsto_nhds.1 (hρc a x₀ hx₀) ε hε
    simpa only [dist_eq_norm] using this
  have key : ∀ x ∈ W, (∀ a ∈ S, ‖ρ x a - ρ x₀ a‖ < ε) → p x ∈ B ∧ y x = z (p x) := by
    intro x hxW h
    obtain ⟨h1, h2⟩ := hnear (ρ x) (hρ x) h
    refine ⟨h1, ?_⟩
    have e : ψ' (p x) = φ x := by
      refine AlgHom.ext fun a => ?_
      have := hψ' (p x) h1 a
      rw [show ψ (p x) = ρ x from h2] at this
      exact this
    have h3 := hz (p x)
    rw [e] at h3
    exact (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c A (CAt σ) (φ x) yA).1 _ _ (hy x hxW) h3
  have h0 := key x₀ hx₀ (fun a _ => by simpa using hε)
  have hc : ContinuousWithinAt (fun x => |fn σ (z (p x)) i|) W x₀ :=
    ContinuousAt.comp_continuousWithinAt (f := p) (g := fun b => |fn σ (z b) i|)
      (hcont.continuousAt (hB.mem_nhds h0.1)) hp
  refine hc.congr_of_eventuallyEq ?_ (by rw [h0.2])
  filter_upwards [hev, self_mem_nhdsWithin] with x h hxW
  rw [(key x hxW h).2]

theorem fn_continuousOn_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ (σ : c.F →+* ℂ) (A : Type) [CommRing A] [Algebra c.F A] [Algebra.Smooth c.F A] (yA : FrPt Xo c A) (X : Type) [TopologicalSpace X] (W : Set X) (φ : X → (A →ₐ[c.F] CAt σ)) (y : X → FrPt Xo c (CAt σ)), (∀ a, ContinuousOn (fun x => Formalism.L2.PjFree.toC (φ x a)) W) → (∀ x ∈ W, FrMap (φ x) yA (y x)) → ∀ i, ContinuousOn (fun x => |fn σ (y x) i|) W := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn hx hfn σ A _ _ _ yA X _ W φ y hφ hy i
  by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
  · exact fn_continuousOn_good U hU xR fn hx hfn σ hσ A yA X W φ y hφ hy i
  · have hσ' : Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp σ) := by
      have := Formalism.L2.PjFree.goodEmb_goodOf c σ
      unfold Formalism.L2.PjFree.goodOf at this
      rwa [if_neg hσ] at this
    choose z hz using fun x => GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c (CAt σ)
      (CAt ((starRingEnd ℂ).comp σ)) (conjAlg σ) (y x)
    have h := fn_continuousOn_good U hU xR fn hx hfn _ hσ' A yA X W (fun x => (conjAlg σ).comp (φ x)) z
      (fun a => Complex.continuous_conj.comp_continuousOn (hφ a))
      (fun x hxW => frMap_trans (Xo := Xo) (c := c) _ _ _ (φ x) (conjAlg σ) yA (y x) (z x) (hy x hxW) (hz x)) i
    exact h.congr fun x _ => (hfn.2 σ (y x) (z x) (hz x) i).symm

end GlobalTheory.FrameNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousOnSmoothChartStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameNorms_continuousOn_smoothChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ (σ : c.F →+* ℂ) (A : Type) [CommRing A] [Algebra c.F A] [Algebra.Smooth c.F A] (yA : FrPt Xo c A) (X : Type) [TopologicalSpace X] (W : Set X) (φ : X → (A →ₐ[c.F] CAt σ)) (y : X → FrPt Xo c (CAt σ)), (∀ a, ContinuousOn (fun x => Formalism.L2.PjFree.toC (φ x a)) W) → (∀ x ∈ W, FrMap (φ x) yA (y x)) → ∀ i, ContinuousOn (fun x => |fn σ (y x) i|) W := by
  first | exact @GlobalTheory.FrameNorm.fn_continuousOn_smooth | exact GlobalTheory.FrameNorm.fn_continuousOn_smooth | (intros; apply GlobalTheory.FrameNorm.fn_continuousOn_smooth <;> assumption)
end
end

module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExponentialGluing.DecTranslate
noncomputable section

open NumberField MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.Rs.JExpNegGlue

section General

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace G] [T2Space G]

def Dec (μ : Measure G) (ρ : ℝ) (a : ℝ → G) (H : G → ℂ) : Prop :=
  Continuous H ∧ ∀ Q : Set G, IsCompact Q →
    Tendsto (fun t : ℝ => Real.exp (-(2 * ρ * t)) * ∫ g in Q, ‖H (a t * g)‖ ^ 2 ∂μ) atTop (𝓝 0)

variable (μ : Measure G) [μ.IsHaarMeasure] (ρ : ℝ) (a : ℝ → G)

theorem intOn {H : G → ℂ} (hH : Continuous H) {Q : Set G} (hQ : IsCompact Q) (t : ℝ) :
    IntegrableOn (fun g => ‖H (a t * g)‖ ^ 2) Q μ :=
  ((hH.comp (continuous_const.mul continuous_id)).norm.pow 2).continuousOn.integrableOn_compact hQ

theorem dec_zero : Dec μ ρ a 0 := by
  refine ⟨continuous_const, fun Q _ => ?_⟩
  simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))

theorem dec_add {H₁ H₂ : G → ℂ} (h₁ : Dec μ ρ a H₁) (h₂ : Dec μ ρ a H₂) : Dec μ ρ a (H₁ + H₂) := by
  refine ⟨h₁.1.add h₂.1, fun Q hQ => ?_⟩
  have hlim := ((h₁.2 Q hQ).const_mul 2).add ((h₂.2 Q hQ).const_mul 2)
  simp only [mul_zero, add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun t => ?_) (fun t => ?_)
  · exact mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => by positivity)
  · have hle : ∫ g in Q, ‖(H₁ + H₂) (a t * g)‖ ^ 2 ∂μ ≤
        ∫ g in Q, (2 * ‖H₁ (a t * g)‖ ^ 2 + 2 * ‖H₂ (a t * g)‖ ^ 2) ∂μ := by
      refine integral_mono (intOn μ a (h₁.1.add h₂.1) hQ t)
        (((intOn μ a h₁.1 hQ t).const_mul 2).add ((intOn μ a h₂.1 hQ t).const_mul 2)) (fun g => ?_)
      simp only [Pi.add_apply]
      have h := norm_add_le (H₁ (a t * g)) (H₂ (a t * g))
      have h' := mul_le_mul h h (norm_nonneg _) (by positivity)
      nlinarith [sq_nonneg (‖H₁ (a t * g)‖ - ‖H₂ (a t * g)‖)]
    rw [integral_add ((intOn μ a h₁.1 hQ t).const_mul 2) ((intOn μ a h₂.1 hQ t).const_mul 2),
      integral_const_mul, integral_const_mul] at hle
    have he := (Real.exp_pos (-(2 * ρ * t))).le
    calc _ ≤ Real.exp (-(2 * ρ * t)) * (2 * ∫ g in Q, ‖H₁ (a t * g)‖ ^ 2 ∂μ +
          2 * ∫ g in Q, ‖H₂ (a t * g)‖ ^ 2 ∂μ) := mul_le_mul_of_nonneg_left hle he
      _ = _ := by ring

theorem dec_smul (c : ℂ) {H : G → ℂ} (h : Dec μ ρ a H) : Dec μ ρ a (c • H) := by
  refine ⟨h.1.const_smul c, fun Q hQ => ?_⟩
  have e : ∀ t, Real.exp (-(2 * ρ * t)) * ∫ g in Q, ‖(c • H) (a t * g)‖ ^ 2 ∂μ =
      ‖c‖ ^ 2 * (Real.exp (-(2 * ρ * t)) * ∫ g in Q, ‖H (a t * g)‖ ^ 2 ∂μ) := by
    intro t
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
    rw [integral_const_mul]; ring
  refine (tendsto_congr e).2 ?_
  simpa using (h.2 Q hQ).const_mul (‖c‖ ^ 2)

theorem dec_translate (hcomm : ∀ s t, a s * a t = a t * a s) (s : ℝ) {H : G → ℂ} (h : Dec μ ρ a H) :
    Dec μ ρ a (fun g => H (a s * g)) := by
  refine ⟨h.1.comp (continuous_const.mul continuous_id), fun Q hQ => ?_⟩
  set S : Set G := (fun x => (a s)⁻¹ * x) ⁻¹' Q with hSdef
  have hS : IsCompact S := (Homeomorph.mulLeft (a s)⁻¹).isCompact_preimage.2 hQ
  have hpre : (fun x => a s * x) ⁻¹' S = Q := by ext x; simp [hSdef]
  have e : ∀ t, ∫ g in Q, ‖H (a s * (a t * g))‖ ^ 2 ∂μ = ∫ g in S, ‖H (a t * g)‖ ^ 2 ∂μ := by
    intro t
    have := (measurePreserving_mul_left μ (a s)).setIntegral_preimage_emb (measurableEmbedding_mulLeft (a s))
      (fun g => ‖H (a t * g)‖ ^ 2) S
    rw [hpre] at this
    rw [← this]
    congr 1; funext x
    rw [← mul_assoc, hcomm, mul_assoc]
  refine (tendsto_congr fun t => ?_).2 (h.2 S hS)
  simp only [e t]

end General
end PositivityTheory.Rg.Rs.JExpNegGlue
end
end

noncomputable section

open NumberField MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.Rs.JExpNegGlue

theorem aInf_comm (E : Type) [Field E] (N r : ℕ) (s t : ℝ) :
    aInf E N r s * aInf E N r t = aInf E N r t * aInf E N r s := by
  apply Units.ext
  show Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext i; exact mul_comm _ _

theorem aT_comm (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N r : ℕ) (s t : ℝ) :
    aT E N r s * aT E N r t = aT E N r t * aT E N r s := by
  unfold aT
  rw [← map_mul, aInf_comm, map_mul]

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm in
theorem continuous_ctn {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (r : ℕ)
    {φ : GA E N → ℂ} (hφ : Continuous φ) : Continuous (An.ctn (K := E) (n := N) r φ) := by
  set_option synthInstance.maxHeartbeats 200000 in
    haveI : SecondCountableTopology (GA E N) := inferInstance
    haveI : FirstCountableTopology (GA E N) := inferInstance
    obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := E) (n := N) (r := r)
    haveI : IsFiniteMeasure ((unipMeasure E N r).restrict (unipFundamentalDomain E N r)) :=
      isFiniteMeasure_restrict.2 (by rw [unipMeasure_unipFundamentalDomain]; exact ENNReal.one_ne_top)
    have hf : Continuous (Function.uncurry fun (g : GA E N) (X : UPos N r → AdeleRing (𝓞 E) E) =>
        φ (unipGL X * g)) :=
      hφ.comp ((continuous_unipGL.comp continuous_snd).mul continuous_fst)
    have h := continuous_parametric_integral_of_continuous
      (μ := (unipMeasure E N r).restrict (unipFundamentalDomain E N r)) hf hC
    have e : ∀ g : GA E N, constantTerm r φ g = ∫ X in C, φ (unipGL X * g)
        ∂((unipMeasure E N r).restrict (unipFundamentalDomain E N r)) := by
      intro g
      rw [Measure.restrict_restrict' measurableSet_unipFundamentalDomain, Set.inter_eq_right.2 hDC]
      rfl
    unfold An.ctn
    exact continuous_const.mul (h.congr fun g => (e g).symm)

theorem main : ExpNegGlue := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro hDict hL2 E _ _ _ N φ hA hSq r hr0 hrN c hc
    obtain ⟨haR, hsplit, hlat, hct⟩ := hDict E N
    have hctn := (hct φ hA r hr0 hrN).2
    obtain ⟨F₀, hF₀, F, hFspan, hF0, hFeq⟩ := hc
    obtain ⟨c₀, -, hF₀eq⟩ := hctn F₀ hF₀
    subst hF₀eq
    have hφc : Continuous φ.1 := GlobalTheory.CompanionTheory.ConstTerm.continuous_of_isOpen_stab φ hA.level
    obtain ⟨hcen, μ, 𝓕, hHaar, hFD, hfin⟩ := hSq
    haveI := hHaar
    have hleft : ∀ γ ∈ An.lat E N, ∀ g, φ.1 (γ * g) = φ.1 g := by
      let S : Subgroup (GA E N) :=
        { carrier := {γ | ∀ g, φ.1 (γ * g) = φ.1 g}
          mul_mem' := fun {x y} hx hy g => by
            simp only [Set.mem_setOf_eq] at hx hy ⊢; rw [mul_assoc, hx, hy]
          one_mem' := fun g => by simp
          inv_mem' := fun {x} hx g => by
            simp only [Set.mem_setOf_eq] at hx ⊢
            calc φ.1 (x⁻¹ * g) = φ.1 (x * (x⁻¹ * g)) := (hx _).symm
              _ = φ.1 g := by rw [mul_inv_cancel_left] }
      have hS : An.lat E N ≤ S := by
        refine sup_le ?_ ?_
        · rintro _ ⟨γ, rfl⟩ g
          exact GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E N φ hA γ g
        · rw [Subgroup.zpowers_le]
          intro g
          have := hcen 1 g
          rwa [hsplit 1] at this
      exact fun γ hγ => hS hγ
    set ρ := An.rho E N r with hρ
    set a : ℝ → GA E N := aT E N r with ha
    have hcomm : ∀ s t, a s * a t = a t * a s := aT_comm E N r
    have hdec_ctn : Dec μ ρ a (An.ctn r φ.1) := by
      refine ⟨continuous_ctn r hφc, fun Q hQ => ?_⟩
      have h := hL2 E N r hr0 hrN μ φ.1 𝓕 hφc hleft (hlat ▸ hFD) hfin Q hQ
      simp only [ha, haR]
      exact h
    have hdecF : Dec μ ρ a F := by
      refine Submodule.span_induction (p := fun H _ => Dec μ ρ a H) ?_ (dec_zero μ ρ a)
        (fun x y _ _ hx hy => dec_add μ ρ a hx hy) (fun b x _ hx => dec_smul μ ρ a b hx) hFspan
      rintro _ ⟨s, rfl⟩
      convert dec_smul μ ρ a c₀ (dec_translate μ ρ a hcomm s hdec_ctn) using 1
    obtain ⟨g₀, hg₀⟩ : ∃ g₀, F g₀ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hF0 (funext h)
    obtain ⟨Q, hQc, hQn⟩ := exists_compact_mem_nhds g₀
    have hFc := hdecF.1
    set I := ∫ g in Q, ‖F g‖ ^ 2 ∂μ with hI
    have hIpos : 0 < I := by
      have hint : IntegrableOn (fun g => ‖F g‖ ^ 2) Q μ := (hFc.norm.pow 2).continuousOn.integrableOn_compact hQc
      rw [hI, setIntegral_pos_iff_support_of_nonneg_ae
        (ae_of_all _ fun g => by show (0 : ℝ) ≤ ‖F g‖ ^ 2; positivity) hint]
      have hopen : IsOpen (Function.support (fun g => ‖F g‖ ^ 2) ∩ interior Q) :=
        (hFc.norm.pow 2).isOpen_support.inter isOpen_interior
      have hne : (Function.support (fun g => ‖F g‖ ^ 2) ∩ interior Q).Nonempty :=
        ⟨g₀, by simp [Function.mem_support, hg₀], mem_interior_iff_mem_nhds.2 hQn⟩
      exact lt_of_lt_of_le (hopen.measure_pos μ hne)
        (measure_mono (Set.inter_subset_inter_right _ interior_subset))
    have hval : ∀ t : ℝ, Real.exp (-(2 * ρ * t)) * ∫ g in Q, ‖F (a t * g)‖ ^ 2 ∂μ =
        Real.exp (2 * (c.re - ρ) * t) * I := by
      intro t
      have hre : (c * (t : ℂ)).re = c.re * t := by simp
      have hpt : ∀ g, ‖F (a t * g)‖ ^ 2 = Real.exp (c.re * t) ^ 2 * ‖F g‖ ^ 2 := by
        intro g
        rw [hFeq, norm_mul, Complex.norm_exp, mul_pow, hre]
      simp_rw [hpt]
      rw [integral_const_mul, ← mul_assoc, sq, ← Real.exp_add, ← Real.exp_add]
      congr 2; ring
    have hlim := hdecF.2 Q hQc
    rw [tendsto_congr hval] at hlim
    have hlt : c.re < ρ := by
      by_contra hge
      push_neg at hge
      have hev : ∀ᶠ t in atTop, I ≤ Real.exp (2 * (c.re - ρ) * t) * I := by
        filter_upwards [eventually_ge_atTop 0] with t ht
        have h1 : 1 ≤ Real.exp (2 * (c.re - ρ) * t) :=
          Real.one_le_exp (by nlinarith [mul_nonneg (sub_nonneg.2 hge) ht])
        nlinarith
      have := ge_of_tendsto hlim hev
      linarith
    have hd : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
    rw [hρ, An.rho] at hlt
    unfold pE
    have : c.re / (Module.finrank ℚ E : ℝ) < (r : ℝ) * ((N : ℝ) - r) / 2 := by
      rw [div_lt_iff₀ hd]; linarith
    linarith

end PositivityTheory.Rg.Rs.JExpNegGlue

theorem PositivityTheory.Rg.Rs.expNegGlue_holds : PositivityTheory.Rg.Rs.ExpNegGlue := PositivityTheory.Rg.Rs.JExpNegGlue.main

end

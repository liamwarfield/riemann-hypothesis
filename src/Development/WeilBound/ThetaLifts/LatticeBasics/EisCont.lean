module

public import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
public import Development.WeilBound.ThetaLifts.LatticeBasics.EulerProd
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.EvFinIdemSelf
public import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactOfUnits

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.EisCont
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem one_le_height_GL2 (x : G2 σ Y) : (1 : ℝ) ≤ ht2 x := one_le_heightGL F x.1

theorem modFun_spec {f : G2 σ Y → ℂ} (hf : f ∈ modFun σ Y) :
    Continuous f ∧ ∃ (C : ℝ) (N : ℕ), ∀ x, ‖f x‖ ≤ C * (ht2 x : ℝ) ^ N := by
  induction hf using Submodule.span_induction with
  | mem f h => exact ⟨h.1, 1, h.2.imp fun N h x => by simpa using h x⟩
  | zero => exact ⟨continuous_zero, 0, 0, by simp⟩
  | add f g _ _ a b =>
    obtain ⟨a, C, N, hC⟩ := a
    obtain ⟨b, C', N', hC'⟩ := b
    refine ⟨a.add b, max C 0 + max C' 0, max N N', fun x => (norm_add_le _ _).trans ?_⟩
    have := one_le_height_GL2 x
    rw [add_mul]
    refine add_le_add ((hC x).trans ?_) ((hC' x).trans ?_) <;> gcongr <;> simp
  | smul c f _ a =>
    obtain ⟨a, C, N, hC⟩ := a
    exact ⟨a.const_smul c, ‖c‖ * C, N, fun x => by
      rw [Pi.smul_apply, norm_smul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)⟩

theorem reg_of_weak {s₀ : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 s₀) {H : ℂ → modFun σ Y}
    (h : ∀ μ, IsGrowForm μ → DifferentiableOn ℂ (fun s => μ (H s)) U) :
    An.Reg (fun x : G2 σ Y => (ht2 x : ℝ)) (fun s => (H s).1) s₀ := by
  obtain ⟨D, hD, hU', cD⟩ := local_compact_nhds hU
  refine An.reg_of_bound (NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)) hD
    (fun x => (h ((LinearMap.proj x).comp (modFun σ Y).subtype) fun N => ⟨_, fun f hf => hf x⟩).mono hU')
    (fun s _ => (modFun_spec (H s).2).1) (An.unif_bound one_le_height_GL2 (fun f hf => (modFun_spec hf).2) fun μ hμ => ?_)
  exact cD.exists_bound_of_continuousOn ((h μ hμ).mono hU').continuousOn

theorem eisCont_of_reg {f Ê : ℂ → G2 σ Y → ℂ} {t : ℝ} (h1 : ∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (f s) x) (Ê s x))
    (h2 : ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re})
    (h3 : ∀ s₀, ∃ (k : ℕ) (H : ℂ → G2 σ Y → ℂ), An.Reg (fun x : G2 σ Y => (ht2 x : ℝ)) H s₀ ∧
      ∀ᶠ s in 𝓝[≠] s₀, ∀ x, H s x = (s - s₀) ^ k * Ê s x) :
    ∃ U, IsEisCont f U Ê ∧ ∀ s₀, ∃ k, IsRegAt Ê s₀ k := by
  have disc : ∀ s : ℂ, ∀ᶠ z in 𝓝[≠] s, z ∈ {s | An.Reg (fun x : G2 σ Y => (ht2 x : ℝ)) Ê s} := fun s =>
    let ⟨_, _, a, e⟩ := h3 s
    a.punct one_le_height_GL2 e
  refine ⟨{s | An.Reg (fun x : G2 σ Y => (ht2 x : ℝ)) Ê s}, ⟨isOpen_iff_mem_nhds.2 fun s hs => hs.eventually, An.preconn disc, disc, ⟨t, fun s hs => ⟨?_, h1 s hs⟩⟩,
    fun x s hs => ?_, fun y hy => (An.Reg.contAt hy.1 y.2).continuousWithinAt, fun s hs => ?_⟩, fun s => ?_⟩
  · obtain ⟨_, _, a, e⟩ := h3 s
    exact a.remove one_le_height_GL2 e ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs) h2
  · obtain ⟨S, hS, a⟩ := hs
    exact ((a.hol x).differentiableAt hS).differentiableWithinAt
  · obtain ⟨S, hS, -, -, C, N, hC⟩ := hs
    obtain ⟨r, r0, hr⟩ := Metric.mem_nhds_iff.1 hS
    exact ⟨r, C, N, r0, fun z hz => hC z (hr hz)⟩
  · obtain ⟨k, H, ⟨S, hS, a⟩, e⟩ := h3 s
    obtain ⟨r, r0, hr⟩ := Metric.mem_nhds_iff.1 (inter_mem hS (eventually_nhdsWithin_iff.1 e))
    have b := a.mono fun z hz => (hr hz).1
    exact ⟨k, r, H, r0, fun z hz => (hr hz).2, b.hol, b.cont, b.grow⟩

theorem eisContinues_of (h1 : EisBL) (h2 : FrameConj) : EisContinues := by
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY χ hχ c hc K a hK ha s₁ f hf
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨b, K₀, p, t, hb, hK₀, hp, hk⟩ := h2 F E σ B n Y r s hB hY K hK
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = absE F E (Matrix.GeneralLinearGroup.det t) := ⟨_, rfl⟩
  have d0 : 0 < d := hd ▸ absE_pos _
  have a0 : ∀ x, 0 < a x := fun x => by
    obtain ⟨q, u, hq, k, hk, rfl⟩ := ha.iwa x
    exact ha.val q u hq k hk ▸ absE_pos _
  have hk' : ∀ k ∈ K₀, p * k * p⁻¹ ∈ K := fun k h => (hk _).2 (by simpa [mul_assoc] using h)
  have ha₀ : IsHgt K₀ fun x => d * a (x * p⁻¹) := by
    refine ⟨fun x => ?_, fun q u hq k h => ?_⟩
    · obtain ⟨q, u, hq, k, h, e⟩ := ha.iwa (x * p⁻¹)
      exact ⟨q * p, _, hq.mul hp, _, (hk k).1 h, by rw [mul_inv_eq_iff_eq_mul.1 e]; group⟩
    · rw [show q * k * p⁻¹ = q * p⁻¹ * (p * k * p⁻¹) by group, ha.val _ _ (hq.mul hp.inv) _ (hk' k h), map_mul, map_mul, map_inv,
        map_inv, NNReal.coe_mul, NNReal.coe_inv, ← hd]
      field_simp
  have hf₀ : IsSec K₀ χ s₁ fun x => f (x * p⁻¹) := by
    refine ⟨hf.cont.comp (continuous_mul_const _), fun q u x hq => by rw [mul_assoc, hf.law q u _ hq], ?_⟩
    haveI := hf.fin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * k.1))).map
      (LinearMap.funLeft ℂ ℂ fun x => x * p⁻¹)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨⟨_, hk' k k.2⟩, rfl⟩, funext fun x => by simp [LinearMap.funLeft, mul_assoc]⟩
  obtain ⟨Ê, ⟨t₁, e1, e2⟩, e3⟩ := h1 F E σ B n Y r s hB hn hY χ hχ c hc b K₀ _ hb hK₀ ha₀ s₁ _ hf₀
  have dc : Differentiable ℂ fun z : ℂ => (d : ℂ) ^ (s₁ - z) :=
    (differentiable_id.const_sub s₁).const_cpow (.inl (Complex.ofReal_ne_zero.2 d0.ne'))
  refine (eisCont_of_reg (f := flat a f s₁) (Ê := fun z x => (d : ℂ) ^ (s₁ - z) * Ê z (x * p)) (t := t₁) (fun z hz x => ?_)
    (fun x => dc.differentiableOn.mul (e2 _)) fun s₀ => ?_).imp fun U hU => ⟨_, hU⟩
  · refine (congrArg (HasSum · _) (funext fun q => ?_)).mp ((e1 z hz (x * p)).mul_left ((d : ℂ) ^ (s₁ - z)))
    simp only [eisTerm, flat, ← mul_assoc, mul_inv_cancel_right]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg d0.le (a0 _).le, ← mul_assoc,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 d0.ne')]
    simp
  · obtain ⟨k, U, H, hU, e4, e5⟩ := e3 s₀
    refine ⟨k, _, (reg_of_weak hU e5).mul one_le_height_GL2 (dc.analyticAt s₀) (continuous_mul_const p) (b := ht2 p) fun x => ?_, ?_⟩
    · rw [mul_comm]; exact_mod_cast heightGL_mul_le F x.1 p.1
    · filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with z hz hz' x
      rw [e4 z hz hz', mul_left_comm]

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.NormZeta
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

theorem swFullX_of (h1 : SWAnisoX) (h2 : EisContinues) (h3 : BoxSecX) : SWFullX := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha μ D hμ hD Φ₁ p1 Φ₂ p2
  obtain ⟨U, Ê, hE, hR⟩ := h2 F E σ B n X r s hB hn (.inl hX) χ hχ d hr K a hK ha _ _
    (h3 F E σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha Φ₁ p1 Φ₂ p2)
  obtain ⟨k, hk⟩ := hR (((d : ℂ) - n) / 2)
  exact ⟨_, _, hE.update hk (h1 F E σ B n d X W M r s r' s' hB hn hd hX hW h0 hM χ hχ hr dd om S l c1 c2 K a hK ha μ D hμ hD Φ₁ p1 Φ₂ p2),
    Set.mem_insert _ _, fun x => by rw [Function.update_self]⟩

theorem inv_scale {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f : G → ℂ, (Integrable (fun g => f g⁻¹) μ → Integrable f μ) ∧ ∫ g, f g⁻¹ ∂μ = c * ∫ g, f g ∂μ := by
  have e := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have c0 : μ.inv.haarScalarFactor μ ≠ 0 := fun h => NeZero.ne μ (by rw [← μ.inv_inv, e, h, zero_smul]; exact Measure.map_zero _)
  refine ⟨((μ.inv.haarScalarFactor μ : ℝ) : ℂ), by simpa using c0, fun f => ⟨fun h => ?_, ?_⟩⟩
  · have : Integrable f μ.inv := (integrable_map_equiv (MeasurableEquiv.inv G) f).2 h
    rw [e] at this
    exact (integrable_smul_measure (ENNReal.coe_ne_zero.2 c0) ENNReal.coe_ne_top).1 this
  · have : ∫ g, f g ∂μ.inv = ∫ g, f g⁻¹ ∂μ := integral_map_equiv (MeasurableEquiv.inv G) f
    rw [← this]
    conv_lhs => rw [e]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem normZeta_of (hS : SWFullX) (hX : BoxSecX) (hW : DblX) (hH : HgtEx) (hT : HgtInt) (hK : Stab2Cpt) (hC : CptAll)
    (hB : ThetaBasic) (hP : PolSch) : NormZeta := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' T h0 h0' hn hd K a e k1 k2 he ν hν Φ hΦ
  have cX := hC F E σ B _ X _ _ T.base (.inl T.herm) h0
  have cW := hC F E σ B _ W _ _ T.base (.inr T.skew) h0'
  obtain ⟨μ, D, hμ, hD⟩ := cW.ex
  obtain ⟨⟨K', a', k1', k2', k3, k4⟩, e', ce, he'⟩ := hH F E σ B _ X _ _ T.base (.inl T.herm)
  obtain rfl : K' = K := Subgroup.ext fun k => (k1' k).trans (k1 k).symm
  obtain rfl : a' = a := funext fun x => by
    obtain ⟨p, t, hp, k, hk, rfl⟩ := k2.iwa x
    rw [k2.val p t hp k hk, k2'.val p t hp k hk]
  obtain rfl : e' = e := MonoidHom.ext fun x => Subtype.ext (Units.ext ((he' x.1 x.2).trans (he x.1 x.2).symm))
  have b := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ T).1 Φ (hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ T Φ hΦ)
  have s1 := hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ T Φ hΦ
  obtain ⟨dd, om₂, S, l, d1, d2, d3, d4⟩ := hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ T
  obtain ⟨c', c0, hc⟩ := d4 ν hν
  obtain ⟨t₀, hi⟩ := hT F E σ B _ X _ _ T.base (.inl T.herm) K' a' e' k1 k2 he M.μ T.good.haar
  have sec := hX F E σ B _ _ _ _ M _ _ _ _ T.base hn hd T.herm T.skew h0' T.good χW T.hW T.resW dd om₂ S l d3 d1 K' a' k1 k2 Φ hΦ Φ hΦ
  obtain ⟨U, Ê, hE, u, hv⟩ := hS F E σ B _ _ _ _ M _ _ _ _ T.base hn hd T.herm T.skew h0' T.good χW T.hW T.resW dd om₂ S l d3 d1
    K' a' k1 k2 μ D hμ hD Φ hΦ Φ hΦ
  obtain ⟨hol, t₁, far⟩ := kpair_cont T.base (.inl T.herm) h0 cX T.hW he ce (hK F E σ B _ X _ _ T.base (.inl T.herm) K' k1)
    k2 k3 k4 sec.cont sec.law hE T.good.haar T.good.dom hi
  haveI := cX.sc; haveI := cW.sc; haveI := cX.lc; haveI := cW.lc; haveI := T.good.haar; haveI := cX.right M.μ T.good.haar
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by rw [Measure.restrict_apply_univ]; exact cW.fin _ _ hμ hD⟩
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact cX.fin _ _ T.good.haar T.good.dom⟩
  obtain ⟨c, c1, hc1⟩ := inv_scale M.μ
  have rp : IsRapid (fun _ : UA σ X.J => (1 : ℂ)) := cX.rapid continuous_const fun _ _ _ => rfl
  have v0 := Complex.ofReal_ne_zero.2 (cX.vol_ne T.good.haar T.good.dom)
  have c2 := Complex.ofReal_ne_zero.2 c0.ne'
  have id : ∀ z g, flat a' (fun x => l (om₂ x (boxFun Φ (star Φ)))) (((d : ℂ) - n) / 2) z (e' (1, g)) * detInv χW g =
      c' * zint om ν a' e' Φ z g⁻¹ := fun z g => by
    have := (Law.flat (s₀ := ((d : ℂ) - n) / 2) (f := fun x => l (om₂ x (boxFun Φ (star Φ)))) sec.law k2 k4 z).diag (aniso_of T.base (.inl T.herm) h0) he g (e' (g⁻¹, 1))
    rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one] at this
    have e2 := ((d2 Φ s1 Φ s1).2 1 g⁻¹ 1 _ (he _ _)).2
    rw [detInv_rat T.hW (one_mem _), one_smul, show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl, map_one, Module.End.one_apply] at e2
    rw [this, flat, e2, hc _ (T.weil.isUSplitting.pres _ _ s1) _ s1, zint, coef]
    exact mul_left_comm _ _ _
  refine ⟨U, fun z => (c' * c * M.μ.real M.dom : ℂ)⁻¹ * kpair χW e' M.μ M.dom (Ê z) fun _ => 1, t₁, hE.isOpen, hE.disc, u,
    (hol _ rp).const_mul _, fun z hz => ⟨(far z hz).1, (hc1 _).1 ?_, ?_⟩, fun I0 => mul_eq_zero_of_right _ ?_⟩
  · simpa only [id, integrable_const_mul_iff c2.isUnit] using (far z hz).2.1
  · simp only [(far z hz).2.2 _ rp, id, pet, star_one, mul_one, setIntegral_const, integral_mul_const, integral_const_mul,
      (hc1 _).2, Complex.real_smul]
    field_simp
  · have cT : Continuous fun x : UA σ W.J × UA σ X.J => theta om Φ x.2 x.1 := b.1.comp continuous_swap
    have := An.at_value (φ := fun _ => 1) (M.μ.restrict M.dom) (μ.restrict D)
      ⟨cT, cW.bdd₂ cX cT fun γ hγ δ hδ g g' => b.2.1 δ hδ γ hγ _ _⟩ ⟨continuous_const, 1, by simp⟩
    have z : ∀ h, ∫ g in M.dom, 1 * star (theta om Φ g h) ∂M.μ = 0 := fun h => by
      simp only [one_mul, Complex.star_def, integral_conj]
      exact (map_eq_zero _).2 (congrFun I0 h)
    simp only [z, zero_mul, integral_zero] at this
    refine Eq.trans ?_ ((congrArg ((if n < d then 1 else 2) * (((μ.real D)⁻¹ : ℝ) : ℂ) * ·) this).trans (mul_zero _))
    simp only [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [hv, setAverage_eq, Complex.real_smul, ← fun g => (((d2 Φ s1 Φ s1).2 g y.1 y.2 _ (he _ _)).1), integral_const_mul]
    ring

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.CommuteTheta
noncomputable section

namespace GlobalTheory.ThK.Dbl.Bad

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc (idem)
open PositivityTheory.ThKG.Loc.Cone

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem cartan_pm {M θ : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (hs : HasSig M r s) (h0 : min r s = 0)
    (hM : ∀ i j, star (M j i) = M i j) (h : IsCartan M θ) : θ = 1 ∨ θ = -1 := by
  by_contra hn
  push Not at hn
  have ex : ∀ A : Matrix (Fin n) (Fin n) ℂ, A ≠ 0 → ∃ u, A *ᵥ u ≠ 0 := fun A hA => by
    by_contra c
    push Not at c
    exact hA (Matrix.ext_iff_mulVec.2 fun u => by rw [c, Matrix.zero_mulVec])
  obtain ⟨u, hu⟩ := ex _ (fun e => hn.2 (eq_neg_of_add_eq_zero_left e) : θ + 1 ≠ 0)
  obtain ⟨u', hu'⟩ := ex _ (sub_ne_zero.2 hn.1)
  set x := (θ + 1) *ᵥ u
  set y := (θ - 1) *ᵥ u'
  have hx : θ *ᵥ x = x := by rw [Matrix.mulVec_mulVec, mul_add, h.1, mul_one, add_comm]
  have hy : θ *ᵥ y = -y := by rw [Matrix.mulVec_mulVec, mul_sub, h.1, mul_one, ← Matrix.neg_mulVec, neg_sub]
  have iso : ∀ a b : Fin n → ℂ, (θ *ᵥ a) ⬝ᵥ M *ᵥ star (θ *ᵥ b) = a ⬝ᵥ M *ᵥ star b := fun a b => by
    have : star (θ *ᵥ b) = θ.map star *ᵥ star b := funext fun i => by simp [Matrix.mulVec, dotProduct]
    conv_rhs => rw [← h.2.1, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [this, Matrix.mulVec_mulVec]
  have re : ∀ a : Fin n → ℂ, a ⬝ᵥ M *ᵥ star a = ((a ⬝ᵥ M *ᵥ star a).re : ℂ) := fun a => by
    refine (Complex.conj_eq_iff_re.1 ?_).symm
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, map_sum, map_mul, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [← hM i j, Complex.star_def]; ring
  have p1 := h.2.2 x hu
  have p2 := h.2.2 y hu'
  have c1 := iso x y
  have c2 := iso y x
  rw [hx] at p1
  rw [hy, neg_dotProduct, Complex.neg_re] at p2
  rw [hx, hy] at c1 c2
  rw [star_neg, Matrix.mulVec_neg, dotProduct_neg, neg_eq_self] at c1
  rw [neg_dotProduct, neg_eq_self] at c2
  set a := (x ⬝ᵥ M *ᵥ star x).re
  set b := (y ⬝ᵥ M *ᵥ star y).re
  have z := HasSig.aniso hs h0 (x := (Real.sqrt (-b) : ℂ) • x + (Real.sqrt a : ℂ) • y) (by
    simp only [star_add, star_smul, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, c1, c2, smul_eq_mul, Complex.star_def, Complex.conj_ofReal, mul_zero, add_zero, zero_add]
    rw [re x, re y, ← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul (Real.sqrt a), Real.mul_self_sqrt p1.le,
      Real.mul_self_sqrt p2.le]
    change ((-b : ℝ) : ℂ) * a + a * b = 0
    push_cast
    ring)
  have z' := congrArg (θ *ᵥ ·) z
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hx, hy, Matrix.mulVec_zero] at z'
  have : (2 * Real.sqrt a : ℂ) • y = 0 := by linear_combination (norm := module) z - z'
  exact hu' ((smul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 p1).ne')))

variable {Y : Spc F E n} {B : Base F E} {v : Pl F} {r s : ℕ}

theorem theta_pm (hB : B.IsGood σ) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) (w) : Y.θ w = 1 ∨ Y.θ w = -1 :=
  cartan_pm (h.sig w) h0 (fun i j => (hB.cm.2.2.2 _ _).symm.trans (congrArg _ (h.herm i j))) (h.cartan w)

theorem commute_theta (hB : B.IsGood σ) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) (w) (A) : Commute A (Y.θ w) := by
  rcases theta_pm hB h h0 w with e | e <;> rw [e]
  exacts [Commute.one_right _, Commute.neg_one_right _]

omit [NumberField E] in
theorem real_latHat {z} (hz : z ∈ latHat Y) : realAd F 1 • z = 0 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, h0, -, x, -, rfl⟩ := hz
    rw [smul_smul, mul_comm, ← smul_smul, at_real _ b h0]
  | zero => exact smul_zero _
  | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | neg x _ hx => rw [smul_neg, hx, neg_zero]

theorem idem_int (v u : Pl F) : evFin F u (idem F v) ∈ u.adicCompletionIntegers F := by
  rcases eq_or_ne u v with rfl | h
  · rw [evFin_idem_self]; exact one_mem _
  · rw [evFin_idem_ne h]; exact zero_mem _

theorem mulVec_mem (hL : Y.L.IsLattice E) {A : Matrix (Fin n) (Fin n) (AE F E)}
    (h : ∀ v, ∀ z ∈ latHat Y, At (evFin F v) z → A *ᵥ z ∈ latHat Y) {z} (hz : z ∈ latHat Y) : A *ᵥ z ∈ latHat Y := by
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  have t := (tendsto_aS (F := F)).smul_const (A *ᵥ z)
  rw [one_smul] at t
  refine (Euler.isClosed_latHat hL).mem_of_tendsto t (.of_forall fun S => ?_)
  rw [aS, add_smul, ← Matrix.mulVec_smul, real_latHat hz, Matrix.mulVec_zero, zero_add, Finset.sum_smul]
  exact sum_mem fun v _ => by
    rw [← Matrix.mulVec_smul]; exact h v _ (latHat_smul (idem_int v) hz) (at_idem v z)

theorem stab_iff (hB : B.IsGood σ) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) {K : Subgroup (UA σ Y.J)} (hK : IsStab B K)
    {g : UA σ Y.J} : g ∈ K ↔ ∀ v, IntAt v g :=
  (hK g).trans ⟨fun a _ z hz _ => a.2 z hz, fun a => ⟨fun w => commute_theta hB h h0 w _, fun _ hz =>
    ⟨mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (a v z h1 h2).1) hz, mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (a v z h1 h2).2) hz⟩⟩⟩

theorem emb_mem (hB : B.IsGood σ) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) {K : Subgroup (G2 σ Y)} (hK : IsStab2 B K)
    {e : UA σ Y.J × UA σ Y.J →* G2 σ Y} (he : ∀ g g', IsEmb g g' (e (g, g'))) {g : UA σ Y.J} (hg : ∀ v, IntAt v g) :
    e (g, 1) ∈ K := by
  refine (hK _).2 ⟨fun w => ?_, fun z z' hz hz' k hk => ?_⟩
  · rw [he g 1, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _)]
    simp only [Commute, SemiconjBy, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      (commute_theta hB h h0 w _).eq, (commute_theta hB h h0 w _).neg_right.eq]
  · obtain ⟨g', e1, hg'⟩ : ∃ g', k = e (g', 1) ∧ mat g' *ᵥ z ∈ latHat Y := by
      rcases hk with rfl | rfl
      · exact ⟨g, rfl, mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (hg v z h1 h2).1) hz⟩
      · exact ⟨g⁻¹, by rw [← map_inv, Prod.inv_mk, inv_one], mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (hg v z h1 h2).2) hz⟩
    rw [e1, he g' 1, Matrix.fromBlocks_mulVec, show mat (1 : UA σ Y.J) = 1 from rfl]
    simpa using ⟨hg', hz'⟩

theorem int_nhds (hL : Y.L.IsFullLattice E) : {g : UA σ Y.J | ∀ v, IntAt v g} ∈ 𝓝 (1 : UA σ Y.J) := by
  classical
  obtain ⟨m, x, hs, hx⟩ := Euler.lat_gen hL.toIsLattice
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let U : Set (Fin m → AF F) := {a | ∀ i v, evFin F v (a i) ∈ v.adicCompletionIntegers F}
  have hO : IsOpen {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have hU : IsOpen U := by
    rw [show U = ⋂ i, {a | ∀ v, evFin F v (a i) ∈ v.adicCompletionIntegers F} from Set.ext fun _ => by
      rw [Set.mem_iInter]; rfl]
    exact isOpen_iInter_of_finite fun i => hO.preimage (continuous_snd.comp (continuous_apply i))
  have hV := IsModuleTopology.isOpenMap_of_surjective (Euler.gen_surj hL hs) U hU
  set V := (Fintype.linearCombination (AF F) fun i => incV F (x i).1) '' U with eV
  have key : ∀ A : Matrix (Fin n) (Fin n) (AE F E), (∀ i, A *ᵥ incV F (x i).1 ∈ V) → ∀ v, ∀ z ∈ latHat Y, At (evFin F v) z →
      A *ᵥ z ∈ latHat Y := fun A hA v z hz h => by
    obtain ⟨a, ha, rfl⟩ := (hx z).1 hz
    rw [← Euler.at_iff.1 h, Finset.smul_sum, Matrix.mulVec_sum]
    refine sum_mem fun i _ => ?_
    obtain ⟨b, hb, e⟩ := hA i
    rw [smul_smul, Matrix.mulVec_smul, ← e, Fintype.linearCombination_apply, Finset.smul_sum]
    refine sum_mem fun j _ => ?_
    rw [smul_smul, mul_assoc]
    exact Euler.gen_mem (Euler.idem_mem (by rw [map_mul]; exact mul_mem ((ha i).2 v) (hb j v))) (x j).2
  have o : IsOpen {g : UA σ Y.J | ∀ i, mat g *ᵥ incV F (x i).1 ∈ V} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => hV.preimage (Euler.cont_mat.matrix_mulVec continuous_const)
  have o1 : ∀ i, mat (1 : UA σ Y.J) *ᵥ incV F (x i).1 ∈ V := fun i => by
    rw [show mat (1 : UA σ Y.J) = 1 from rfl, Matrix.one_mulVec]
    refine ⟨Pi.single i 1, fun j v => ?_, by rw [Fintype.linearCombination_apply_single, one_smul]⟩
    rw [Pi.single_apply, apply_ite (evFin F v), map_one, map_zero]
    split_ifs
    exacts [one_mem _, zero_mem _]
  exact mem_of_superset ((o.inter (o.preimage continuous_inv)).mem_nhds ⟨o1, by rw [Set.mem_preimage, inv_one]; exact o1⟩)
    fun g hg v z hz h => ⟨key _ hg.1 v z hz h, key _ hg.2 v z hz h⟩

theorem idem_smul {M : Type} [AddCommGroup M] [Module (AF F) M] {z : M} (h : At (evFin F v) z) : idem F v • z = z :=
  Euler.at_iff.1 h

theorem idem_off {z : AE F E} (h : compFin F E v z = 0) : idem F v • z = 0 := by
  let j : Fv F v ⊗[F] E →ₗ[F] AE F E := TensorProduct.map (LinearMap.inr F (Ainf F) (Af F) ∘ₗ singleFin v) LinearMap.id
  have : ∀ z, idem F v • z = j (compFin F E v z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, map_zero]
    | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy]
    | tmul a x =>
      refine congrArg (· ⊗ₜ[F] x) (af_ext' ((evI_mul _ _).trans (by rw [evI_idem, zero_mul]; exact evI_zero.symm)) fun u => ?_)
      rcases eq_or_ne u v with rfl | h
      · rw [smul_eq_mul, map_mul, evFin_idem_self, one_mul]; exact (evalV_singleFin_self _ _).symm
      · rw [smul_eq_mul, map_mul, evFin_idem_ne h, zero_mul]; exact (evalV_singleFin_ne h _).symm
  rw [this, h, map_zero]

theorem comm_off {e : UA σ Y.J × UA σ Y.J →* G2 σ Y} (he : ∀ g g', IsEmb g g' (e (g, g'))) {g : UA σ Y.J} (hg : OffAt v g)
    {k : G2 σ Y} (hk : At (evFin F v) (mat2 k - 1)) : k * e (g, 1) = e (g, 1) * k := by
  have h1 : idem F v • (mat2 (e (g, 1)) - 1) = 0 := by
    have : idem F v • (mat g - 1) = 0 := Matrix.ext fun i j => idem_off (by
      have := congrFun₂ hg i j
      rw [Matrix.map_apply] at this
      simp [this, Matrix.one_apply, apply_ite (compFin F E v)])
    rw [he g 1, show mat (1 : UA σ Y.J) = 1 from rfl, ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg,
      Matrix.fromBlocks_add, Matrix.fromBlocks_smul, ← sub_eq_add_neg, this]
    simp
  have a1 : (mat2 k - 1) * (mat2 (e (g, 1)) - 1) = 0 := by rw [← idem_smul hk, smul_mul_assoc, ← mul_smul_comm, h1, mul_zero]
  have a2 : (mat2 (e (g, 1)) - 1) * (mat2 k - 1) = 0 := by rw [← idem_smul hk, mul_smul_comm, ← smul_mul_assoc, h1, zero_mul]
  refine Subtype.ext (Units.ext (show mat2 k * mat2 (e (g, 1)) = mat2 (e (g, 1)) * mat2 k from ?_))
  linear_combination (norm := noncomm_ring) a1 - a2

theorem loc_iwa {K : Subgroup (G2 σ Y)} (hK : IsStab2 B K) {a : G2 σ Y → ℝ} (ha : IsHgt K a) {x : G2 σ Y}
    (hx : At (evFin F v) (mat2 x - 1)) : ∃ p t k, IsPar p t ∧ k ∈ K ∧ At (evFin F v) (mat2 k - 1) ∧ x = p * k := by
  obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa x
  have h1 := idem_mul_self v
  let π : G2 σ Y →* G2 σ Y := MonoidHom.mk' (fun g => ⟨⟨Euler.cut (idem F v) (mat2 g), Euler.cut (idem F v) (mat2 g⁻¹),
    by rw [Euler.cut_mul h1, show mat2 g * mat2 g⁻¹ = 1 from g.1.mul_inv]; exact Euler.cut_one,
    by rw [Euler.cut_mul h1, show mat2 g⁻¹ * mat2 g = 1 from g.1.inv_mul]; exact Euler.cut_one⟩,
    Euler.cut_form h1 _ g.2⟩) fun g h => Subtype.ext (Units.ext (Euler.cut_mul h1 _ _).symm)
  have hπ : ∀ g, mat2 (π g) = (1 - idem F v) • 1 + idem F v • mat2 g := fun _ => rfl
  have h2 : ∀ g, mat2 (π g) - 1 = idem F v • (mat2 g - 1) := fun _ => Euler.cut_sub _
  refine ⟨π p, ⟨Euler.cut (idem F v) t.1, Euler.cut (idem F v) (t⁻¹).1,
    by rw [Euler.cut_mul h1, t.mul_inv]; exact Euler.cut_one, by rw [Euler.cut_mul h1, t.inv_mul]; exact Euler.cut_one⟩, π k, ?_,
    (hK _).2 ⟨fun w => ?_, fun z z' hz hz' k' hk' => ?_⟩, by rw [h2]; exact at_idem v _, ?_⟩
  · rw [isPar_iff] at hp ⊢
    change mat2 (π p) * _ = _ * Euler.cut (idem F v) t.1
    rw [hπ, Euler.cut, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, hp,
      Matrix.one_mul, Matrix.mul_one]
  · have : (mat2 (π k)).map (piInf (B.emb w)) = 1 := by
      rw [eq_add_of_sub_eq (h2 k), Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]
      exact add_eq_right.2 (Matrix.ext fun i j => piInf_idem _ v _)
    rw [this]; exact Commute.one_left _
  · obtain ⟨k₁, rfl, h3⟩ : ∃ k₁, k' = π k₁ ∧ k₁ ∈ ({k, k⁻¹} : Set (G2 σ Y)) := by
      rcases hk' with rfl | rfl
      exacts [⟨k, rfl, .inl rfl⟩, ⟨k⁻¹, (map_inv π k).symm, .inr rfl⟩]
    obtain ⟨b1, b2⟩ := ((hK k).1 hk).2 z z' hz hz' k₁ h3
    have i2 : ∀ u, evFin F u (1 - idem F v) ∈ u.adicCompletionIntegers F := fun u => by
      rw [map_sub, map_one]; exact sub_mem (one_mem _) (idem_int v u)
    rw [hπ, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact ⟨add_mem (latHat_smul i2 hz) (latHat_smul (idem_int v) b1), add_mem (latHat_smul i2 hz') (latHat_smul (idem_int v) b2)⟩
  · rw [← map_mul]
    exact Subtype.ext (Units.ext (Euler.cut_eq.2 (idem_smul hx)).symm)

end GlobalTheory.ThK.Dbl.Bad

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.CartanBound2
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

open PositivityTheory.ThKG.Tow St
open scoped Pointwise

theorem cartan_bound2 {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) :
    ∃ R : ℝ, ∀ A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ, Aᵀ * dbl M * A.map star = dbl M →
      Commute A (Matrix.fromBlocks θ 0 0 (-θ)) → ∀ i j, ‖A i j‖ ≤ R := by
  let e := (finSumFinEquiv (m := n) (n := n)).symm
  have c : IsCartan ((dbl M).submatrix e e) ((Matrix.fromBlocks θ 0 0 (-θ)).submatrix e e) := by
    refine ⟨?_, ?_, fun x hx => ?_⟩
    · simp [Matrix.fromBlocks_multiply, h.1]
    · rw [Matrix.transpose_submatrix, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
      have : θᵀ * M * θ.map (starRingEnd ℂ) = M := h.2.1
      simp [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.map_neg, this]
    · obtain ⟨y, z, rfl⟩ : ∃ y z, x = Sum.elim y z ∘ e := ⟨x ∘ e.symm ∘ .inl, x ∘ e.symm ∘ .inr, by
        ext i; obtain ⟨j, rfl⟩ := e.symm.surjective i; cases j <;> simp⟩
      have q : ∀ v, 0 ≤ ((θ *ᵥ v) ⬝ᵥ M *ᵥ star v).re := fun v => by
        by_cases hv : v = 0
        · simp [hv]
        · exact (h.2.2 v hv).le
      have : ((Matrix.fromBlocks θ 0 0 (-θ)).submatrix e e *ᵥ Sum.elim y z ∘ e) ⬝ᵥ (dbl M).submatrix e e *ᵥ star (Sum.elim y z ∘ e) =
          (θ *ᵥ y) ⬝ᵥ M *ᵥ star y + (θ *ᵥ z) ⬝ᵥ M *ᵥ star z := by
        rw [show star (Sum.elim y z ∘ e) = Sum.elim (star y) (star z) ∘ e by
          ext i; obtain ⟨j, rfl⟩ := e.symm.surjective i; cases j <;> simp]
        simp [Matrix.submatrix_mulVec_equiv, Function.comp_assoc, comp_equiv_dotProduct_comp_equiv, dbl, Matrix.fromBlocks_mulVec,
          Matrix.neg_mulVec]
      rw [this, Complex.add_re]
      by_cases hy : y = 0
      · exact add_pos_of_nonneg_of_pos (q y) (h.2.2 z fun hz => hx (by simp [hy, hz]))
      · exact add_pos_of_pos_of_nonneg (h.2.2 y hy) (q z)
  obtain ⟨R, hR⟩ := cartan_bound c
  refine ⟨R, fun A h1 h2 i j => ?_⟩
  simpa using hR (A.submatrix e e) (by
    rw [Matrix.transpose_submatrix, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h1])
    (by rw [Commute, SemiconjBy, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h2.eq]) (e.symm i) (e.symm j)

attribute [local instance] ae_ring ae_t2 ae_smul

theorem stab2Cpt : Stab2Cpt := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY K hK
  obtain ⟨hL, c, c0, hc⟩ : Y.L.IsFullLattice E ∧ ∃ c : ℂ, c ≠ 0 ∧ ∀ w, IsCartan (c • Y.J.map (B.emb w).1) (Y.θ w) :=
    hY.elim (fun h => ⟨h.lat, 1, one_ne_zero, fun w => by simpa using h.cartan w⟩) fun h => ⟨h.lat, _, Complex.I_ne_zero, h.cartan⟩
  obtain ⟨Φ, hΦ, eΦ⟩ := exists_section hB.cm B.emb
  choose C hC h using fin_bound (F := F) Y hL
  choose R hR using fun w => cartan_bound2 (hc w)
  have hD : IsCompact (Φ '' Set.univ.pi fun w => Metric.closedBall (0 : ℂ) (R w)) :=
    (isCompact_univ_pi fun w => isCompact_closedBall _ _).image hΦ
  have hm : Continuous fun g : G2 σ Y => mat2 g := Units.continuous_val.comp continuous_subtype_val
  have hp : ∀ w, Continuous (piInf (B.emb w)) := fun w => GlobalTheory.Grow.continuous_infEmb_compInf F w (B.emb w)
  have cc : Continuous (cA (F := F) σ) := IsModuleTopology.continuous_of_linearMap (cA (F := F) σ).toLinearMap
  have cl := (isCompact_latHat Y hL.fg).isClosed
  have key : ∀ k ∈ K, mat2 k ∈ Set.univ.pi fun i => Set.univ.pi fun j =>
      (Φ '' Set.univ.pi fun w => Metric.closedBall (0 : ℂ) (R w)) + C (Sum.elim id id i) (Sum.elim id id j) := fun k hk i _ j _ => by
    obtain ⟨k1, k2⟩ := (hK k).1 hk
    rw [eΦ (mat2 k i j)]
    refine Set.add_mem_add ⟨_, fun w _ => ?_, rfl⟩ ?_
    · rw [mem_closedBall_zero_iff]
      refine hR w ((mat2 k).map (piInf (B.emb w))) ?_ (k1 w) i j
      have e := congrArg (fun X => c • Matrix.map X (piInf (B.emb w)))
        (show (mat2 k)ᵀ * dbl (incM F Y.J) * (mat2 k).map (cA σ) = dbl (incM F Y.J) from k.2)
      have d : c • (dbl (incM F Y.J)).map (piInf (B.emb w)) = dbl (c • Y.J.map (B.emb w).1) := by
        ext (a | a) (b | b) <;> simp [dbl, incM, Levi.piInf_incl]
      have d2 : ((mat2 k).map (cA σ)).map (piInf (B.emb w)) = ((mat2 k).map (piInf (B.emb w))).map star :=
        Matrix.ext fun a b => Levi.piInf_cA hB.cm _ _
      simp only [Matrix.map_mul] at e
      rwa [← Matrix.smul_mul, ← Matrix.mul_smul, d, d2] at e
    · have a := fun y hy => k2 y 0 hy (zero_mem _) k (.inl rfl)
      have b := fun y hy => k2 0 y (zero_mem _) hy k (.inl rfl)
      rw [← Matrix.fromBlocks_toBlocks (mat2 k)] at a b
      simp only [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_zero, add_zero, zero_add] at a b
      rcases i with i | i <;> rcases j with j | j
      exacts [h i j _ fun y hy => (a y hy).1, h i j _ fun y hy => (b y hy).1, h i j _ fun y hy => (a y hy).2,
        h i j _ fun y hy => (b y hy).2]
  refine isCompact_of_units _ (isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.matrix_map cc)) continuous_const) _ ?_ _
    (isCompact_univ_pi fun i => isCompact_univ_pi fun j => hD.add (hC _ _)) fun k hk => ⟨key k hk, key _ (inv_mem hk)⟩
  rw [show (K : Set (G2 σ Y)) = {k | _} from Set.ext hK]
  simp only [Set.forall_mem_insert, Set.mem_singleton_iff, forall_eq]
  simp only [Set.setOf_and, Set.setOf_forall]
  have v : ∀ {f : G2 σ Y → G2 σ Y}, Continuous f → ∀ z, IsClosed ({k | (mat2 (f k) *ᵥ z) ∘ Sum.inl ∈ latHat Y} ∩
      {k | (mat2 (f k) *ᵥ z) ∘ Sum.inr ∈ latHat Y}) := fun hf z =>
    have t := (hm.comp hf).matrix_mulVec (continuous_const (y := z))
    (cl.preimage (continuous_pi fun i => (continuous_apply _).comp t)).inter
      (cl.preimage (continuous_pi fun i => (continuous_apply _).comp t))
  exact (isClosed_iInter fun w => isClosed_eq ((hm.matrix_map (hp w)).matrix_mul continuous_const)
      (continuous_const.matrix_mul (hm.matrix_map (hp w)))).inter
    (isClosed_iInter fun z => isClosed_iInter fun z' => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      (v continuous_id _).inter (v continuous_inv _))

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.CoefLine
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

theorem coefLine_of (hS : SWFull) (hX : BoxSec) (hW : DblW) (hH : HgtEx) (hT : HgtInt) (hK : Stab2Cpt) (hC : CptAll)
    (hR : PairsStable) (hM : MatchEx) (hB : ThetaBasic) (hI : PositivityTheory.ThKF.ICont) (hP : PolSch) : CoefLine := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf h hp hq μ D hμ hD s t lam hl y hy Ψ hΨ
  have T := h.triple
  have l1 := T.geo.lt
  have l2 := T.geo.aBig
  have cW := hC F E σ B _ G.W _ _ T.base (Or.inr T.geo.hW) (by omega)
  have cV := hC F E σ B _ G.V' _ _ T.base (Or.inl T.geo.hV') (by omega)
  obtain ⟨q1, q2⟩ := (hM F E σ B a a' G X om om' R Rf h).2.2 _ _ hy.1 hy.2
  have b1 := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T)).1
  have b2 := (hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)).1
  have s1 := hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T) _ q1
  have s2 := hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T) _ q2.1
  have s3 := hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T) _ hΨ
  have c1 := (hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T)).1 (Or.inr (by omega))
  have c2 := (hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)).1 (Or.inr (by omega))
  have rp : ∀ s u, IsRapid (comb G om om' s u y) := fun s u =>
    cW.rapid (((c1 _ s1).const_smul s).add ((c2 _ s2).const_smul u)) fun γ hγ g => by
      simp only [comb, Pi.add_apply, Pi.smul_apply, I_inv G.M (b1 _ s1).2.1 γ hγ, I_inv G.M' (b2 _ s2).2.1 γ hγ]
  have tr : ∀ s u g, (fun h => comb G om om' s u y (h * g)) = comb G om om' s u (om (1, g) y.1, om' (1, g) y.2) := fun s u g =>
    funext fun h => by simp only [comb, Pi.add_apply, Pi.smul_apply, I_right]
  obtain ⟨dd, om₂, S, l, d1, d2, d3, -⟩ := hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)
  obtain ⟨⟨K, ht, k1, k2, k3, k4⟩, e, ce, he⟩ := hH F E σ B _ G.W _ _ T.base (.inr T.geo.hW)
  obtain ⟨t₀, hi⟩ := hT F E σ B _ G.W _ _ T.base (.inr T.geo.hW) K ht e k1 k2 he μ hμ
  have sec := hX F E σ B _ _ _ _ G.M' _ _ _ _ T.base (by omega) (by omega) T.geo.hV' (by omega) T.geo.hW T.geo.hM' X.α
    T.chars.heckeα T.chars.resα dd om₂ S l d3 d1 K ht k1 k2 Ψ hΨ Ψ hΨ
  obtain ⟨U, Ê, hE, u, hv⟩ := hS F E σ B _ _ _ _ G.M' _ _ _ _ T.base (by omega) (by omega) T.geo.hV' (by omega) T.geo.hW T.geo.hM' X.α
    T.chars.heckeα T.chars.resα dd om₂ S l d3 d1 K ht k1 k2 Ψ hΨ Ψ hΨ
  obtain ⟨hol, t₁, far⟩ := kpair_cont T.base (.inr T.geo.hW) (by omega) cW T.chars.heckeα he ce
    (hK F E σ B _ G.W _ _ T.base (.inr T.geo.hW) K k1) k2 k3 k4 sec.cont sec.law hE hμ hD hi
  have key := An.ident hE.isOpen hE.conn (hol _ (rp s t)) ((hol _ (rp 0 1)).const_mul lam) (fun z hz => ⟨(far z hz).1, by
    simp only [(far z hz).2.2 _ (rp s t), (far z hz).2.2 _ (rp 0 1), tr, ← integral_const_mul,
      fun g => hl _ ((hR F E σ B a a' G X om om' R Rf h hp hq).2 y hy g) y hy]
    exact integral_congr_ae (.of_forall fun g => mul_left_comm _ _ _)⟩) u
  haveI := cW.sc; haveI := cV.sc; haveI := cW.lc; haveI := cV.lc
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by rw [Measure.restrict_apply_univ]; exact cW.fin _ _ hμ hD⟩
  haveI : IsFiniteMeasure (G.M'.μ.restrict G.M'.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact cV.fin _ _ T.geo.hM'.haar T.geo.hM'.dom⟩
  have val : ∀ φ, IsRapid φ → kpair X.α e μ D (Ê (((a' : ℂ) - (a + a' : ℕ)) / 2)) φ =
      2 * ((G.M'.μ.real G.M'.dom)⁻¹ : ℝ) * pet G.M'.μ G.M'.dom (th om' μ D φ Ψ) (th om' μ D φ Ψ) := fun φ hφ => by
    have := An.at_value (μ.restrict D) (G.M'.μ.restrict G.M'.dom) ⟨(b2 _ s3).1, cV.bdd₂ cW (b2 _ s3).1 (b2 _ s3).2.1⟩
      ⟨hφ.1, cW.bdd hφ.1 hφ.2.1⟩
    refine Eq.trans ?_ (congrArg _ this)
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [hv, if_neg (show ¬ a + a' < a' by omega), setAverage_eq, Complex.real_smul,
      ← fun g => (((d2 Ψ s3 Ψ s3).2 g y.1 y.2 _ (he _ _)).1), integral_const_mul]
    ring
  rw [val _ (rp s t), val _ (rp 0 1), mul_left_comm lam] at key
  exact mul_left_cancel₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 (inv_ne_zero (cV.vol_ne T.geo.hM'.haar T.geo.hM'.dom)))) key

end GlobalTheory.ThK.Dbl

end
end

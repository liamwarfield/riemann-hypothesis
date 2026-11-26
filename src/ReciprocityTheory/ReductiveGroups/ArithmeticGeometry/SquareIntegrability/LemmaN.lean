module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TBNFinal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TranslationZeroModeLift
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbelB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ZeroModeAddRealDirection

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaN
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

theorem lemmaN (_hd : DimStatement) : NStatement := thetaBasis_holds

end ReciprocityTheory.ChartRestriction.G.I2
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbelC
namespace ReciprocityTheory.ChartRestriction.G.I2

section

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {X : PT E}

theorem cab_emb_sep {σ τ : E →+* ℂ} (h : σ ≠ τ) : ∃ α : 𝓞 E, σ (α : E) ≠ τ (α : E) := by
  by_contra hc
  push Not at hc
  apply h
  exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => hc x)

omit [IsCMField E] in
theorem cab_conjugate_ne [_root_.NumberField.IsTotallyComplex E] (σ : E →+* ℂ) : ComplexEmbedding.conjugate σ ≠ σ := by
  intro h
  have hr : ComplexEmbedding.IsReal σ := ComplexEmbedding.isReal_iff.2 h
  have hc := IsTotallyComplex.isComplex (InfinitePlace.mk σ)
  exact (InfinitePlace.not_isReal_iff_isComplex.2 hc) (InfinitePlace.isReal_mk_iff.2 hr)

theorem cab_actE_inPart {σ : E →+* ℂ} {v : Vsp X.dim} (hv : InPart σ v) (β : E) :
    actE β v = σ β • v := by
  ext j
  simp only [actE_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases h : j.1 = σ
  · rw [h]
  · rw [hv j h, mul_zero, mul_zero]

theorem cab_Hf_K (K : Submodule ℝ (Vsp X.dim)) (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
    (v u : Vsp X.dim) (hu : u ∈ K) : Hf v u = ∑ j, Col.z K j u * Col.z K j v := by
  conv_lhs => rw [← Col.proj_one_of_mem hK hu]
  simp only [Col.p1, Col.Hf_sum_r, Col.Hf_smul_r]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hr : (starRingEnd ℂ) (Col.z K j u) = Col.z K j u := by
    apply Complex.conj_eq_iff_im.mpr
    exact hK u hu _ (Col.e_mem K j)
  rw [hr]; rfl

theorem cab_S_zero (K : Submodule ℝ (Vsp X.dim)) (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
    (hst : ∀ (α : 𝓞 E) a, a ∈ K → act α a ∈ K) (σ : E →+* ℂ) (v : Vsp X.dim) (hv : InPart σ v) :
    Col.S K v = 0 := by
  obtain ⟨α, hα⟩ := cab_emb_sep (σ := σ) (τ := ComplexEmbedding.conjugate σ) (cab_conjugate_ne σ).symm
  set a : E := (α : E) with ha
  set b : E := IsCMField.complexConj E a with hb
  have hba : IsCMField.complexConj E b = a := by simp [hb]
  have hKa : ∀ u ∈ K, actE a u ∈ K := fun u hu => hst α u hu
  have hKb : ∀ u ∈ K, actE b u ∈ K := fun u hu =>
    hst (IsCMField.ringOfIntegersComplexConj E α) u hu
  have hσb : σ b = (starRingEnd ℂ) (σ a) := by
    simp [hb, IsCMField.complexEmbedding_complexConj]

  have hent : ∀ j k, Col.z K j (actE b (Col.e K k)) = Col.z K k (actE a (Col.e K j)) := by
    intro j k
    simp only [Col.z]
    rw [Hf_actE, hba, Col.Hf_swap (actE a (Col.e K j))]
    apply Complex.conj_eq_iff_im.mpr
    exact hK _ (hKa _ (Col.e_mem K j)) _ (Col.e_mem K k)
  have h1 : σ a * Col.S K v =
      ∑ k, ∑ j, Col.z K j (actE b (Col.e K k)) * Col.z K j v * Col.z K k v := by
    have : ∀ k, Col.z K k (actE a v) = ∑ j, Col.z K j (actE b (Col.e K k)) * Col.z K j v := by
      intro k
      simp only [Col.z]
      rw [Hf_actE, ← hb]
      exact cab_Hf_K K hK v _ (hKb _ (Col.e_mem K k))
    have h2 : ∀ k, Col.z K k (actE a v) = σ a * Col.z K k v := by
      intro k; simp only [Col.z]; rw [cab_actE_inPart hv, Col.Hf_smul_l]
    simp only [Col.S, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul, ← this k, h2 k]; ring
  have h3 : (starRingEnd ℂ) (σ a) * Col.S K v =
      ∑ j, ∑ k, Col.z K k (actE a (Col.e K j)) * Col.z K k v * Col.z K j v := by
    have : ∀ j, Col.z K j (actE b v) = ∑ k, Col.z K k (actE a (Col.e K j)) * Col.z K k v := by
      intro j
      simp only [Col.z]
      rw [Hf_actE, hba]
      exact cab_Hf_K K hK v _ (hKa _ (Col.e_mem K j))
    have h2 : ∀ j, Col.z K j (actE b v) = (starRingEnd ℂ) (σ a) * Col.z K j v := by
      intro j; simp only [Col.z]; rw [cab_actE_inPart hv, Col.Hf_smul_l, hσb]
    simp only [Col.S, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, ← this j, h2 j]; ring
  have h4 : σ a * Col.S K v = (starRingEnd ℂ) (σ a) * Col.S K v := by
    rw [h1, h3, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hent]; ring
  have hne : σ a - (starRingEnd ℂ) (σ a) ≠ 0 := by
    rw [sub_ne_zero]
    simpa [ComplexEmbedding.conjugate_coe_eq] using hα
  have h5 : (σ a - (starRingEnd ℂ) (σ a)) * Col.S K v = 0 := by rw [sub_mul, h4, sub_self]
  exact (mul_eq_zero.mp h5).resolve_left hne

end

end

section

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E] {X : PT E}

def cabVP {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : Submodule ℂ (Vsp dim) where
  carrier := {v | InPart σ v}
  add_mem' := fun {a b} ha hb j hj => by simp [ha j hj, hb j hj]
  zero_mem' := fun j _ => rfl
  smul_mem' := fun c v hv j hj => by simp [hv j hj]

theorem cab_Hf_IR {I : Submodule ℤ (Vsp X.dim)} {ξ : Vsp X.dim} (hξ : ∀ a ∈ I, Hf ξ a = 0) :
    ∀ a ∈ IR I, Hf ξ a = 0 := by
  intro a ha
  induction ha using Submodule.span_induction with
  | mem x hx => exact hξ x hx
  | zero => simp [Hf]
  | add x y _ _ hx hy => rw [Col.Hf_add_r, hx, hy, add_zero]
  | smul r x _ hx => rw [Col.Hf_rsmul_r, hx, mul_zero]

theorem cab_z_xi {I : Submodule ℤ (Vsp X.dim)} {ξ : Vsp X.dim} (hξ : ∀ a ∈ I, Hf ξ a = 0)
    (k : Fin (Col.dK (IR I))) : Col.z (IR I) k ξ = 0 :=
  cab_Hf_IR hξ _ (Col.e_mem _ k)

theorem cab_Hf_wmap_xi {I : Submodule ℤ (Vsp X.dim)} (hK : ∀ a ∈ IR I, ∀ b ∈ IR I, (Hf a b).im = 0)
    {ξ : Vsp X.dim} (hξ : ∀ a ∈ I, Hf ξ a = 0) (x : Vsp X.dim) : Hf (Col.wmap (IR I) x) (Col.wmap (IR I) ξ) = Hf x ξ := by
  have hp1 : Col.p1 (IR I) ξ = 0 := by
    simp [Col.p1, cab_z_xi hξ]
  have hp2 : Col.p2 (IR I) ξ = ξ := by rw [Col.p2, hp1, sub_zero]
  rw [Col.Hf_wmap hK, hp2, Col.p2, Col.Hf_sub_l]
  have : Hf (Col.p1 (IR I) x) ξ = 0 := by
    simp only [Col.p1, Col.Hf_sum_l, Col.Hf_smul_l]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Col.Hf_swap, ← Col.z, cab_z_xi hξ, map_zero, mul_zero]
  rw [this, sub_zero]

theorem cab_norm_wmap_xi {I : Submodule ℤ (Vsp X.dim)} (hK : ∀ a ∈ IR I, ∀ b ∈ IR I, (Hf a b).im = 0)
    {ξ : Vsp X.dim} (hξ : ∀ a ∈ I, Hf ξ a = 0) :
    ‖Col.wmap (IR I) ξ‖ = ‖ξ‖ := by
  have hp1 : Col.p1 (IR I) ξ = 0 := by
    simp [Col.p1, cab_z_xi hξ]
  rw [Col.norm_wmap hK, Col.p2, hp1, sub_zero]

theorem cab_main {I : Submodule ℤ (Vsp X.dim)} (hK : ∀ a ∈ IR I, ∀ b ∈ IR I, (Hf a b).im = 0)
    {c : ℕ} (σ : E →+* ℂ) {ξ : Vsp X.dim}
    (hξ : ∀ a ∈ I, Hf ξ a = 0) (β : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ)
    (hβ : Differentiable ℂ β) {inst : DecidableEq (Fin (Col.gB (IR I)))}
    (hjet : ∀ α : Fin (Col.gB (IR I)) →₀ ℕ, α.degree ≤ c →
      polyDeriv (MvPolynomial.monomial α 1) (fun i => @EuclideanSpace.single _ ℂ _ inst i 1) β 0 =
        polyDeriv (MvPolynomial.monomial α 1) (fun i => @EuclideanSpace.single _ ℂ _ inst i 1)
          (fun t : EuclideanSpace ℂ (Fin (Col.gB (IR I))) =>
            MvPolynomial.eval (fun i => t i) (cabPoly (Col.wmap (IR I) ξ) c)) 0)
    (F0 : Vsp X.dim → ℂ) (hF0d : Differentiable ℂ F0)
    (hF0 : ∀ v, InPart σ v → F0 v = β (Col.wmap (IR I) v))
    (xs : Fin c → Vsp X.dim) (hxs : ∀ k, InPart σ (xs k)) :
    iteratedFDeriv ℂ c F0 0 xs = (c.factorial : ℂ) * ∏ k, Hf (xs k) ξ := by
  set W := Col.wmap (IR I)
  set η := W ξ
  have hg : Differentiable ℂ (β ∘ W) := hβ.comp W.differentiable
  have h1 : iteratedFDeriv ℂ c F0 0 xs = iteratedFDeriv ℂ c (β ∘ W) 0 xs :=
    cab_restrict (cabVP σ) (contDiff_of_differentiable_fd hF0d c) (contDiff_of_differentiable_fd hg c)
      (fun v hv => hF0 v hv) xs hxs
  have hβc : ContDiff ℂ (⊤ : WithTop ℕ∞) β := cab_contDiff_top hβ
  have h2 : iteratedFDeriv ℂ c (β ∘ W) 0 xs = iteratedFDeriv ℂ c β 0 (fun k => W (xs k)) := by
    rw [W.iteratedFDeriv_comp_right (hβc.of_le le_top) 0 (by exact_mod_cast le_top)]
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  let ℓ : EuclideanSpace ℂ (Fin (Col.gB (IR I))) →L[ℂ] ℂ := innerSL ℂ η
  have hℓ : ∀ t, ℓ t = Hf t η := by
    intro t; rw [Col.Hf_eq_inner]; rfl
  have hP : (fun t : EuclideanSpace ℂ (Fin (Col.gB (IR I))) =>
      MvPolynomial.eval (fun i => t i) (cabPoly η c)) = fun t => (ℓ t) ^ c := by
    funext t; rw [cabPoly_eval, hℓ]
  have hPd : ContDiff ℂ (⊤ : WithTop ℕ∞) (fun t : EuclideanSpace ℂ (Fin (Col.gB (IR I))) =>
      MvPolynomial.eval (fun i => t i) (cabPoly η c)) := by
    rw [hP]; exact cab_contDiff_top (ℓ.differentiable.pow c)
  let _ := inst
  have h3 := cab_jet_eq hβc hPd hjet
  rw [h1, h2, h3, hP, cab_iter_pow]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [hℓ]; exact cab_Hf_wmap_xi hK hξ (xs k)

end

end

section

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E] {X : PT E}

theorem cab_IR_stable {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I) :
    ∀ (α : 𝓞 E) a, a ∈ IR I → act α a ∈ IR I := by
  intro α a ha
  rw [act_eq_actE]
  exact actE_mem_of_span (α : E) (I : Set (Vsp X.dim)) (IR I)
    (fun v hv => Submodule.subset_span (hI.stable α v hv)) a ha

theorem cab_z_diff (K : Submodule ℝ (Vsp X.dim)) (k : Fin (Col.dK K)) :
    Differentiable ℂ (fun v => Col.z K k v) := by
  have : (fun v => Col.z K k v) = fun v => innerSL ℂ (Col.e K k) v := by
    funext v; simp only [Col.z]; rw [Col.Hf_eq_inner]; rfl
  rw [this]; exact (innerSL ℂ (Col.e K k)).differentiable

theorem differentiable_zeroModeLift (I : Submodule ℤ (Vsp X.dim)) (q : ℕ) (β : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ)
    (hβ : Differentiable ℂ β) : Differentiable ℂ (Col.F0 I q β) := by
  have hS : Differentiable ℂ (fun v => Col.S (IR I) v) := by
    have : (fun v => Col.S (IR I) v) = fun v => ∑ k, (Col.z (IR I) k v) ^ 2 := rfl
    rw [this]
    exact Differentiable.fun_sum fun k _ => (cab_z_diff _ k).pow 2
  have : Col.F0 I q β = fun v => cexp ((q * Real.pi / 2 : ℂ) * Col.S (IR I) v) * β (Col.wmap (IR I) v) := rfl
  rw [this]
  exact ((hS.const_mul _).cexp).mul (hβ.comp (Col.wmap (IR I)).differentiable)

theorem zeroModeLift_on_part [IsCMField E] {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I)
    (q : ℕ) (β : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ) (σ : E →+* ℂ) (v : Vsp X.dim)
    (hv : InPart σ v) : Col.F0 I q β v = β (Col.wmap (IR I) v) := by
  have h0 := cab_S_zero (IR I) (Col.hK_of hI) (cab_IR_stable hI) σ v hv
  simp only [Col.F0, h0, mul_zero, Complex.exp_zero, one_mul]

end

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ZeroModePointwiseBound
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ThetaSectionPointwiseNormSqEq
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

theorem uMap_eq_uc (x : Vsp X.dim) : uMap I x = uc (IR I) x :=
  (isU_uMap I x).unique (isU_uc x)

theorem z_uc (hI : IsSplit P I) (k : Fin (dK (IR I))) (v : Vsp X.dim) :
    z (IR I) k (uc (IR I) v) = ((z (IR I) k v).im : ℂ) := by
  have hK := hK_of hI
  rw [uc, z_sum]
  simp only [z_rsmul, z_e hK, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem norm_uc_sq (hI : IsSplit P I) (v : Vsp X.dim) :
    ‖uc (IR I) v‖ ^ 2 = ∑ k, (z (IR I) k v).im ^ 2 := by
  have hK := hK_of hI
  rw [norm_sq_decomp hK, proj_two_of_mem hK (uc_mem _ v), norm_zero]
  simp only [z_uc hI, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

theorem norm_sq_alt (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

theorem thetaSectionPointwiseNormSq_eq (hI : IsSplit P I) (s : (Fin 1 → Vsp X.dim) → ℂ) (v : Vsp X.dim) :
    X.ptN2 1 s (fun _ => v) = ‖zmG I s v‖ ^ 2 *
      Real.exp (-(2 * Real.pi) * ‖uc (IR I) v‖ ^ 2 - Real.pi * ‖p2 (IR I) v‖ ^ 2) := by
  have hK := hK_of hI
  rw [PT.ptN2, HC_one, Hf_self_re, zmG, norm_mul, Complex.norm_exp, mul_pow, mul_assoc,
    ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  have hA := norm_sq_decomp hK v
  simp only [norm_sq_alt, Finset.sum_add_distrib] at hA
  have hB : (-(Real.pi / 2 : ℂ) * S (IR I) v).re =
      -(Real.pi / 2) * (∑ k, (z (IR I) k v).re ^ 2 - ∑ k, (z (IR I) k v).im ^ 2) := by
    rw [S, ← Finset.sum_sub_distrib, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Complex.mul_re, pow_two]
  rw [hB, norm_uc_sq hI v, hA]
  push_cast
  ring

theorem re_gaugeExp (hI : IsSplit P I) (γ v : Vsp X.dim) :
    (gaugeExp I γ v).re = 2 * Real.pi * ∑ k, (z (IR I) k γ).im * (z (IR I) k v).im +
      Real.pi * ∑ k, (z (IR I) k γ).im ^ 2 + Real.pi * (Hf (p2 (IR I) v) (p2 (IR I) γ)).re +
      Real.pi / 2 * ‖p2 (IR I) γ‖ ^ 2 := by
  rw [gaugeExp]
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_sum, Complex.im_sum, Complex.mul_im,
    Complex.div_re, Hf_self_re]
  simp only [mul_zero, zero_mul, sub_zero, mul_one, zero_add, add_zero, Complex.re_ofNat,
    Complex.im_ofNat, Complex.normSq_ofNat]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  ring_nf

theorem norm_orthProj_add_sq (v γ : Vsp X.dim) :
    ‖p2 (IR I) v + p2 (IR I) γ‖ ^ 2 = ‖p2 (IR I) v‖ ^ 2 + 2 * (Hf (p2 (IR I) v) (p2 (IR I) γ)).re +
      ‖p2 (IR I) γ‖ ^ 2 := by
  rw [← Hf_self_re, ← Hf_self_re, ← Hf_self_re, Hf_add_l, Hf_add_r, Hf_add_r,
    Hf_swap (p2 (IR I) γ) (p2 (IR I) v)]
  simp only [Complex.add_re, Complex.conj_re]
  ring

theorem mode_norm (hI : IsSplit P I) (hP : Ext.PackingCount) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec 1 1) {γ : Vsp X.dim} (hγ : γ ∈ X.L) (m : Fin (Module.finrank ℝ (IR I)) → ℤ)
    (hm : ∀ i, (Hf γ ((Ib hI i : IR I) : Vsp X.dim)).im = m i) (v : Vsp X.dim) :
    ‖zmC hI s m v‖ * Real.exp (-Real.pi * ‖uc (IR I) v‖ ^ 2 - Real.pi / 2 * ‖p2 (IR I) v‖ ^ 2) =
      Real.sqrt ((YB hI hP 1).ptN2 1 (zmB hI s) (wmap (IR I) (v + γ))) *
        Real.exp (-Real.pi * ‖uc (IR I) v + uc (IR I) γ‖ ^ 2) := by
  have hK := hK_of hI
  have h := zmC_add hI hs hγ m hm 0 v
  rw [zero_add] at h
  have heps : ‖(X.eps γ : ℂ)‖ = 1 := by rcases X.eps_pm γ hγ with h | h <;> simp [h]
  have hn : ‖zmC hI s 0 (v + γ)‖ = Real.exp (gaugeExp I γ v).re * ‖zmC hI s m v‖ := by
    rw [h, norm_mul, norm_mul, heps, one_mul, Complex.norm_exp]
  have hβ : zmB hI s (wmap (IR I) (v + γ)) = zmC hI s 0 (v + γ) := by
    simp only [zmB]; rw [jj_wmap' hK, ← zeroMode_proj_two hI hs]
  have hpt : Real.sqrt ((YB hI hP 1).ptN2 1 (zmB hI s) (wmap (IR I) (v + γ))) =
      ‖zmC hI s 0 (v + γ)‖ * Real.exp (-(Real.pi / 2) * ‖p2 (IR I) (v + γ)‖ ^ 2) := by
    rw [GT.ptN2, hβ, norm_wmap hK, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    congr 1
    rw [show Real.exp (-(((1 : ℕ) : ℝ) * Real.pi) * ‖p2 (IR I) (v + γ)‖ ^ 2) =
        Real.exp (-(Real.pi / 2) * ‖p2 (IR I) (v + γ)‖ ^ 2) ^ 2 by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring]
    exact Real.sqrt_sq (Real.exp_pos _).le
  rw [hpt, hn]
  have hu : ‖uc (IR I) v + uc (IR I) γ‖ ^ 2 =
      ∑ k, ((z (IR I) k v).im + (z (IR I) k γ).im) ^ 2 := by
    rw [← uc_add, norm_uc_sq hI (v + γ)]
    simp [z_add]
  have hsq : ∑ k, ((z (IR I) k v).im + (z (IR I) k γ).im) ^ 2 =
      ∑ k, (z (IR I) k v).im ^ 2 + 2 * ∑ k, (z (IR I) k γ).im * (z (IR I) k v).im +
        ∑ k, (z (IR I) k γ).im ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hp := norm_orthProj_add_sq (I := I) v γ
  rw [← proj_two_add] at hp
  have hv := norm_uc_sq hI v
  have hg := re_gaugeExp hI γ v
  have key : -Real.pi * ‖uc (IR I) v‖ ^ 2 - Real.pi / 2 * ‖p2 (IR I) v‖ ^ 2 =
      (gaugeExp I γ v).re + -(Real.pi / 2) * ‖p2 (IR I) (v + γ)‖ ^ 2 +
        -Real.pi * ‖uc (IR I) v + uc (IR I) γ‖ ^ 2 := by
    rw [hu, hsq, hp, hv, hg]; ring
  rw [key, Real.exp_add, Real.exp_add]
  ring

theorem dual_lift (hI : IsSplit P I) (m : Fin (Module.finrank ℝ (IR I)) → ℤ) :
    ∃ γ ∈ X.L, ∀ i, (Hf γ ((Ib hI i : IR I) : Vsp X.dim)).im = m i := by
  haveI := IK_discrete hI
  haveI : IsZLattice ℝ (IK I) := ⟨IK_span⟩
  haveI := ZLattice.module_free ℝ (IK I)
  set e := Fintype.equivFinOfCardEq (α := Module.Free.ChooseBasisIndex ℤ (IK I))
    (n := Module.finrank ℝ (IR I)) (by rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ])
  set bZ := (Module.Free.chooseBasis ℤ (IK I)).reindex e with hbZ
  have hIb : ∀ i, (Ib hI i : IR I) = ((bZ i : IK I) : IR I) := fun i => by
    simp [Ib, bZ, Module.Basis.ofZLatticeBasis_apply]
    rfl
  let ψ : IK I →ₗ[ℤ] ℤ := bZ.constr ℤ (fun i => m i)
  let N : Submodule ℤ X.L := I.comap X.L.subtype
  have hsat : ∀ (k : ℤ) (x : X.L), k ≠ 0 → k • x ∈ N → x ∈ N := fun k x hk h =>
    hI.sat x x.2 k hk (by simpa [N] using h)
  let j : N →ₗ[ℤ] IK I :=
    { toFun := fun x => ⟨⟨((x : X.L) : Vsp X.dim), mem_IR x.2⟩, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  obtain ⟨Ψ, hΨ⟩ := Col.extend_hom N hsat (ψ.comp j)
  obtain ⟨γ, hγ, hγΨ⟩ := X.perfect Ψ.toAddMonoidHom
  refine ⟨γ, hγ, fun i => ?_⟩
  let y : X.L := ⟨((Ib hI i : IR I) : Vsp X.dim), hI.le (Ib_mem hI i)⟩
  have hyN : y ∈ N := Ib_mem hI i
  have h1 := hγΨ y
  have h2 : Ψ y = m i := by
    have := hΨ ⟨y, hyN⟩
    simp only at this
    rw [this, LinearMap.comp_apply]
    have hj : j ⟨y, hyN⟩ = bZ i := by
      apply Subtype.ext; apply Subtype.ext
      show ((Ib hI i : IR I) : Vsp X.dim) = (((bZ i : IK I) : IR I) : Vsp X.dim)
      rw [hIb]
    rw [hj]
    simp [ψ]
  rw [← h1]
  simp [h2]

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col ZM

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem zeroMode_pointwise_bound [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
    {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I) (hP : Ext.PackingCount)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) (w : Vsp X.dim) (T M : ℝ)
    (hT : ∀ F : Finset (Vsp X.dim), (∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x) →
      ∑ y ∈ F, Real.exp (-Real.pi * ‖uMap I w - y‖ ^ 2) ≤ T)
    (hM : ∀ t, (Col.YB hI hP 1).ptN2 1 (ZM.zmB hI s) t ≤ M) :
    Real.sqrt (X.ptN2 1 s fun _ => w) ≤ Real.sqrt M * T := by
  classical
  choose γ hγL hγ using fun m : Fin (Module.finrank ℝ (IR I)) → ℤ => dual_lift hI m
  obtain ⟨E0, hE0def⟩ : ∃ e : ℝ,
      Real.exp (-Real.pi * ‖uc (IR I) w‖ ^ 2 - Real.pi / 2 * ‖p2 (IR I) w‖ ^ 2) = e := ⟨_, rfl⟩
  have hE0 : 0 < E0 := hE0def ▸ Real.exp_pos _

  have hmode : ∀ m, ‖zmC hI s m w‖ * E0 ≤
      Real.sqrt M * Real.exp (-Real.pi * ‖uMap I w - uMap I (-γ m)‖ ^ 2) := by
    intro m
    rw [← hE0def, mode_norm hI hP hs (hγL m) m (hγ m) w]
    have h1 : uMap I w - uMap I (-γ m) = uc (IR I) w + uc (IR I) (γ m) := by
      rw [map_neg, sub_neg_eq_add, uMap_eq_uc, uMap_eq_uc]
    rw [h1]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hM _)) (Real.exp_pos _).le

  have hinj : Function.Injective (fun m => uMap I (-γ m)) := by
    intro m m' h
    have h' : uc (IR I) (γ m) = uc (IR I) (γ m') := by
      simp only [map_neg, uMap_eq_uc, neg_inj] at h
      exact h
    funext i
    have e1 := hγ m i
    have e2 := hγ m' i
    rw [← Col.inner_uc (K := IR I) (γ m) _ (Ib hI i).2, h',
      Col.inner_uc (K := IR I) (γ m') _ (Ib hI i).2, e2] at e1
    exact_mod_cast e1.symm
  have hfin : ∀ F : Finset (Fin (Module.finrank ℝ (IR I)) → ℤ),
      ∑ m ∈ F, ‖zmC hI s m w‖ * E0 ≤ Real.sqrt M * T := by
    intro F
    calc ∑ m ∈ F, ‖zmC hI s m w‖ * E0
        ≤ ∑ m ∈ F, Real.sqrt M * Real.exp (-Real.pi * ‖uMap I w - uMap I (-γ m)‖ ^ 2) :=
          Finset.sum_le_sum fun m _ => hmode m
      _ = Real.sqrt M * ∑ y ∈ F.image (fun m => uMap I (-γ m)),
            Real.exp (-Real.pi * ‖uMap I w - y‖ ^ 2) := by
          rw [Finset.mul_sum, Finset.sum_image (fun a _ b _ h => hinj h)]
      _ ≤ Real.sqrt M * T := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          apply hT
          intro y hy
          obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hy
          exact ⟨-γ m, X.L.neg_mem (hγL m), rfl⟩
  have hsumN : Summable fun m : Fin (Module.finrank ℝ (IR I)) → ℤ => ‖zmC hI s m w‖ := by
    apply summable_of_sum_le (c := Real.sqrt M * T / E0) (fun m => norm_nonneg _)
    intro F
    rw [le_div_iff₀ hE0, Finset.sum_mul]
    exact hfin F

  have hF := tof_torus_inversion (fun t : Fin (Module.finrank ℝ (IR I)) → ℝ => zmG I s (w + tb hI t))
    (fib_continuous hI hs w) (fun x n => fib_periodic hI hs w x n) hsumN.of_norm
  have hF' : HasSum (fun m => zmC hI s m w) (zmG I s w) := by
    have h0 : zmG I s w = zmG I s (w + tb hI 0) := by simp [tb]
    rw [h0]
    exact hF
  have hsq : Real.sqrt (X.ptN2 1 s fun _ => w) = ‖zmG I s w‖ * E0 := by
    rw [thetaSectionPointwiseNormSq_eq hI s w]
    have hexp : Real.exp (-(2 * Real.pi) * ‖uc (IR I) w‖ ^ 2 - Real.pi * ‖p2 (IR I) w‖ ^ 2) =
        E0 ^ 2 := by
      rw [← hE0def, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hexp, ← mul_pow, Real.sqrt_sq (mul_nonneg (norm_nonneg _) hE0.le)]
  calc Real.sqrt (X.ptN2 1 s fun _ => w) = ‖zmG I s w‖ * E0 := hsq
    _ ≤ (∑' m, ‖zmC hI s m w‖) * E0 := by
        gcongr
        rw [← hF'.tsum_eq]
        exact norm_tsum_le_tsum_norm hsumN
    _ = ∑' m, ‖zmC hI s m w‖ * E0 := tsum_mul_right.symm
    _ ≤ Real.sqrt M * T := (hsumN.mul_right _).tsum_le_of_sum_le hfin

end

end ReciprocityTheory.ChartRestriction.G.I2
end

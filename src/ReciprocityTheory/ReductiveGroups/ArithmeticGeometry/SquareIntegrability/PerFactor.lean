module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ShortVectorBoundLeKappa
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaN

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NonnegGT
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ZmNorm
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.WhatContinuous
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.CubeSplit
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PointNormSqNonnegQuotient
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TopLeSpanBf
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FibreParseval
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

theorem fibre_parseval (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (v : Vsp X.dim) :
    HasSum (fun n => ‖zmC hI s n v‖ ^ 2)
      (∫ t in zmBox (Module.finrank ℝ (IR I)), ‖zmG I s (v + tb hI t)‖ ^ 2) :=
  tof_torus_parseval (fun t => zmG I s (v + tb hI t)) (fib_continuous hI hs v)
    (fun t n => fib_periodic hI hs v t n)

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

theorem finrank_span1 (hI : IsSplit P I) : Module.finrank ℂ (span1 (IR I)) = dK (IR I) := by
  have hK := hK_of hI
  have ho : Orthonormal ℂ (e (IR I)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [← Hf_eq_inner, Hf_e hK]
    by_cases h : i = j <;> simp [h, eq_comm]
  rw [span1, finrank_span_eq_card ho.linearIndependent, Fintype.card_fin]

theorem dim_count (hI : IsSplit P I) :
    2 * Fintype.card (Idx X.dim) = dK (IR I) + (dK (IR I) + 2 * Fintype.card (Fin (gB (IR I)))) := by
  have h1 := Submodule.finrank_add_finrank_orthogonal (span1 (IR I))
  rw [finrank_euclideanSpace, finrank_span1 hI] at h1
  rw [Fintype.card_fin, gB, V2, ← h1]
  ring

def cp (hI : IsSplit P I) (j : Fin (Module.finrank ℝ (IR I))) : Vsp X.dim :=
  (dual_lift hI (Pi.single j 1)).choose

theorem cp_mem (hI : IsSplit P I) (j) : cp hI j ∈ X.L := (dual_lift hI (Pi.single j 1)).choose_spec.1

theorem cp_pair (hI : IsSplit P I) (j i) :
    (Hf (cp hI j) ((Ib hI i : IR I) : Vsp X.dim)).im = ((Pi.single j 1 : _ → ℤ) i : ℝ) := (dual_lift hI (Pi.single j 1)).choose_spec.2 i

theorem bB_mem_GB (hI : IsSplit P I) (hP : Ext.PackingCount) (l) : bB hI hP l ∈ GB X I := by
  rw [← lat_bB hI hP]; exact Submodule.subset_span ⟨l, rfl⟩

def cpp (hI : IsSplit P I) (hP : Ext.PackingCount) (l : Fin (2 * Fintype.card (Fin (gB (IR I))))) :
    Vsp X.dim :=
  (mem_GB.1 (bB_mem_GB hI hP l)).choose

theorem cpp_mem (hI : IsSplit P I) (hP : Ext.PackingCount) (l) : cpp hI hP l ∈ Ip X I := (mem_GB.1 (bB_mem_GB hI hP l)).choose_spec.1

theorem cpp_wmap (hI : IsSplit P I) (hP : Ext.PackingCount) (l) :
    wmap (IR I) (cpp hI hP l) = bB hI hP l := (mem_GB.1 (bB_mem_GB hI hP l)).choose_spec.2

def Bf (hI : IsSplit P I) (hP : Ext.PackingCount) :
    Fin (Module.finrank ℝ (IR I)) ⊕ (Fin (Module.finrank ℝ (IR I)) ⊕ Fin (2 * Fintype.card (Fin (gB (IR I))))) →
      Vsp X.dim :=
  Sum.elim (fun i => ((Ib hI i : IR I) : Vsp X.dim)) (Sum.elim (cp hI) (cpp hI hP))

theorem mem_I_span (hI : IsSplit P I) {a : Vsp X.dim} (ha : a ∈ I) :
    ∃ c : Fin (Module.finrank ℝ (IR I)) → ℤ, ∑ i, c i • ((Ib hI i : IR I) : Vsp X.dim) = a := by
  have h : (⟨a, mem_IR ha⟩ : IR I) ∈ Submodule.span ℤ (Set.range (Ib hI)) := by
    rw [Ib_span hI]; exact ha
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 h
  refine ⟨c, ?_⟩
  have := congrArg Subtype.val hc
  simpa [Submodule.coe_sum] using this

theorem span_Bf (hI : IsSplit P I) (hP : Ext.PackingCount) :
    Submodule.span ℤ (Set.range (Bf hI hP)) = X.L := by
  have hK := hK_of hI
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rcases k with i | j | l
    · exact hI.le (Ib_mem hI i)
    · exact cp_mem hI j
    · exact (cpp_mem hI hP l).1
  · intro x hx
    have hmem : ∀ v, v ∈ Set.range (Bf hI hP) → v ∈ Submodule.span ℤ (Set.range (Bf hI hP)) :=
      fun v hv => Submodule.subset_span hv
    have hb : ∀ i, ((Ib hI i : IR I) : Vsp X.dim) ∈ Submodule.span ℤ (Set.range (Bf hI hP)) :=
      fun i => hmem _ ⟨Sum.inl i, rfl⟩
    have hc : ∀ j, cp hI j ∈ Submodule.span ℤ (Set.range (Bf hI hP)) :=
      fun j => hmem _ ⟨Sum.inr (Sum.inl j), rfl⟩
    have hcc : ∀ l, cpp hI hP l ∈ Submodule.span ℤ (Set.range (Bf hI hP)) :=
      fun l => hmem _ ⟨Sum.inr (Sum.inr l), rfl⟩
    choose m hm using fun i => X.integral x _ hx (hI.le (Ib_mem hI i))
    set y := x - ∑ j, m j • cp hI j with hy
    have hyL : y ∈ X.L := X.L.sub_mem hx (X.L.sum_mem fun j _ => X.L.smul_mem _ (cp_mem hI j))
    have hyb : ∀ i, (Hf y ((Ib hI i : IR I) : Vsp X.dim)).im = 0 := fun i => by
      rw [hy, Hf_sub_l, Complex.sub_im, Hf_sum_l, Complex.im_sum, hm i]
      simp only [← Int.cast_smul_eq_zsmul ℂ, Hf_smul_l, Complex.mul_im, Complex.intCast_re,
        Complex.intCast_im, zero_mul, add_zero, cp_pair]
      simp [Pi.single_apply]
    have hyIp : y ∈ Ip X I := by
      refine ⟨hyL, fun a ha => ?_⟩
      obtain ⟨c, rfl⟩ := mem_I_span hI ha
      rw [Hf_sum_r, Complex.im_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℂ, Hf_smul_r]
      simp [Complex.mul_im, hyb i]
    have hwy : wmap (IR I) y ∈ Submodule.span ℤ (Set.range (bB hI hP)) := by
      rw [← lat, lat_bB hI hP]; exact wmap_mem_GB hyIp
    obtain ⟨k, hk⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hwy
    set z := y - ∑ l, k l • cpp hI hP l with hz
    have hzIp : z ∈ Ip X I := (Ip X I).sub_mem hyIp ((Ip X I).sum_mem fun l _ =>
      (Ip X I).smul_mem _ (cpp_mem hI hP l))
    have hwz : wmap (IR I) z = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hz, map_sub, map_sum, ← hk]
      simp only [map_zsmul, cpp_wmap, sub_self]
    have hp2 : p2 (IR I) z = 0 := by
      rw [← norm_eq_zero, ← norm_wmap hK, hwz, norm_zero]
    obtain ⟨c, hc'⟩ := mem_I_span hI (mem_of_proj_two_eq_zero hI hzIp hp2)
    have hxe : x = z + ∑ l, k l • cpp hI hP l + ∑ j, m j • cp hI j := by rw [hz, hy]; abel
    rw [hxe, ← hc']
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hb i)
    · exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hcc l)
    · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hc j)

theorem top_le_span_Bf (hI : IsSplit P I) (hP : Ext.PackingCount) :
    ⊤ ≤ Submodule.span ℝ (Set.range (Bf hI hP)) := by
  rw [← X.b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have h : X.b i ∈ Submodule.span ℤ (Set.range (Bf hI hP)) := by
    rw [span_Bf hI hP]; exact Submodule.subset_span ⟨i, rfl⟩
  exact Submodule.span_le_restrictScalars ℤ ℝ _ h

theorem Bf_li (hI : IsSplit P I) (hP : Ext.PackingCount) : LinearIndependent ℝ (Bf hI hP) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank (top_le_span_Bf hI hP)
  have h := dim_count hI
  rw [Fintype.card_fin] at h
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
    Module.finrank_eq_card_basis X.b, Fintype.card_fin]
  exact h.symm

def BB (hI : IsSplit P I) (hP : Ext.PackingCount) :
    Module.Basis (Fin (Module.finrank ℝ (IR I)) ⊕ (Fin (Module.finrank ℝ (IR I)) ⊕
      Fin (2 * Fintype.card (Fin (gB (IR I)))))) ℝ (Vsp X.dim) :=
  Module.Basis.mk (Bf_li hI hP) (top_le_span_Bf hI hP)

theorem BB_apply (hI : IsSplit P I) (hP : Ext.PackingCount) (k) : BB hI hP k = Bf hI hP k := Module.Basis.mk_apply _ _ _

theorem lat_BB (hI : IsSplit P I) (hP : Ext.PackingCount) :
    Submodule.span ℤ (Set.range (BB hI hP)) = X.L := by
  have h : ⇑(BB hI hP) = Bf hI hP := funext (BB_apply hI hP)
  rw [h]
  exact span_Bf hI hP

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

def gam (hI : IsSplit P I) (n : Fin (Module.finrank ℝ (IR I)) → ℤ) : Vsp X.dim := ∑ j, n j • cp hI j

theorem gam_mem (hI : IsSplit P I) (n) : gam hI n ∈ X.L := by
  unfold gam
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (cp_mem hI j)

theorem gam_pair (hI : IsSplit P I) (n) (i) :
    (Hf (gam hI n) ((Ib hI i : IR I) : Vsp X.dim)).im = n i := by
  unfold gam
  rw [Col.Hf_sum_l, Complex.im_sum]
  simp_rw [← Int.cast_smul_eq_zsmul ℂ, Col.Hf_smul_l, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, zero_mul, add_zero, cp_pair hI, Pi.single_apply]
  simp

theorem pointNormSq_nonneg_quotient (hP : Ext.PackingCount) (hI : IsSplit P I) (β) (t) :
    0 ≤ (YB hI hP 1).ptN2 1 β t := by
  unfold GT.ptN2
  positivity

theorem fibre_sum (hI : IsSplit P I) (hP : Ext.PackingCount) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec 1 1) (W : Vsp X.dim) :
    ∫⁻ t in cubeIco (Fin (Module.finrank ℝ (IR I))), ENNReal.ofReal (X.ptN2 1 s fun _ => W + tb hI t) =
      ∑' n, ENNReal.ofReal ((YB hI hP 1).ptN2 1 (zmB hI s) (wmap (IR I) (W + gam hI n)) *
        Real.exp (-(2 * Real.pi) * ‖uc (IR I) (W + gam hI n)‖ ^ 2)) := by
  have hK : ∀ a ∈ IR I, ∀ b ∈ IR I, (Hf a b).im = 0 := Col.iso_IR hI.iso
  have hE2 : ∀ a : ℝ, Real.exp a ^ 2 = Real.exp (2 * a) := fun a => by
    rw [sq, ← Real.exp_add, two_mul]
  have hp1add : ∀ a b, Col.p1 (IR I) (a + b) = Col.p1 (IR I) a + Col.p1 (IR I) b := by
    intro a b
    simp only [Col.p1, z_add, add_smul, Finset.sum_add_distrib]
  have hp2add : ∀ a b, Col.p2 (IR I) (a + b) = Col.p2 (IR I) a + Col.p2 (IR I) b := by
    intro a b
    simp only [Col.p2, hp1add]
    abel
  have hp2K : ∀ b ∈ IR I, Col.p2 (IR I) b = 0 := by
    intro b hb
    have h := congrArg Subtype.val ((Col.ob (IR I)).sum_repr' ⟨b, hb⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    rw [Col.p2, Col.p1, sub_eq_zero]
    conv_lhs => rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [z_of_K hI k hb, Complex.coe_smul]
    rfl
  have hucn : ∀ v, ‖Col.uc (IR I) v‖ ^ 2 = ∑ k, (Col.z (IR I) k v).im ^ 2 := by
    intro v
    rw [← Col.Hf_self_re, Col.uc, Col.Hf_sum_l]
    simp [Col.Hf_sum_r, Col.Hf_rsmul_l, Col.Hf_rsmul_r, Col.Hf_e hK, Complex.re_sum, sq]
  have hnadd : ∀ a b : Vsp X.dim, ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * (Hf a b).re + ‖b‖ ^ 2 := by
    intro a b
    rw [← Col.Hf_self_re, ← Col.Hf_self_re, ← Col.Hf_self_re, Col.Hf_add_l, Col.Hf_add_r,
      Col.Hf_add_r, Col.Hf_swap a b]
    simp only [Complex.add_re, Complex.conj_re]
    ring
  set c : ℝ := Real.exp (-Real.pi * (2 * ∑ k, (Col.z (IR I) k W).im ^ 2 + ‖Col.p2 (IR I) W‖ ^ 2))
    with hc
  have hpt : ∀ t, X.ptN2 1 s (fun _ => W + tb hI t) = ‖zmG I s (W + tb hI t)‖ ^ 2 * c := by
    intro t
    have hw := Col.norm_sq_decomp hK (W + tb hI t)
    have hy : ∀ k, (Col.z (IR I) k (W + tb hI t)).im = (Col.z (IR I) k W).im := fun k => by
      rw [z_add, Complex.add_im, z_of_K hI k (tb_mem hI t), Complex.ofReal_im, add_zero]
    have hp : Col.p2 (IR I) (W + tb hI t) = Col.p2 (IR I) W := by
      rw [hp2add, hp2K _ (tb_mem hI t), add_zero]
    have key : ‖W + tb hI t‖ ^ 2 = (Col.S (IR I) (W + tb hI t)).re +
        2 * ∑ k, (Col.z (IR I) k W).im ^ 2 + ‖Col.p2 (IR I) W‖ ^ 2 := by
      rw [hw, hp]
      have : ∑ k, ‖Col.z (IR I) k (W + tb hI t)‖ ^ 2 =
          (Col.S (IR I) (W + tb hI t)).re + 2 * ∑ k, (Col.z (IR I) k W).im ^ 2 := by
        rw [Col.S, Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← hy k, Complex.sq_norm, Complex.normSq_apply, sq, Complex.mul_re]
        ring
      rw [this]
    have e1 : X.ptN2 1 s (fun _ => W + tb hI t) =
        ‖s (fun _ => W + tb hI t)‖ ^ 2 * Real.exp (-Real.pi * ‖W + tb hI t‖ ^ 2) := by
      unfold PT.ptN2 HC
      simp [Col.Hf_self_re]
    have e2 : ‖zmG I s (W + tb hI t)‖ ^ 2 = ‖s (fun _ => W + tb hI t)‖ ^ 2 *
        Real.exp (-Real.pi * (Col.S (IR I) (W + tb hI t)).re) := by
      unfold zmG
      rw [norm_mul, mul_pow, Complex.norm_exp, hE2]
      congr 2
      simp [Complex.mul_re]
      ring
    rw [e1, e2, mul_assoc, hc, ← Real.exp_add, key]
    congr 2
    ring
  have hcont : Continuous fun t : Fin (Module.finrank ℝ (IR I)) → ℝ => ‖zmG I s (W + tb hI t)‖ ^ 2 * c :=
    (((zmG_continuous hs).comp (continuous_const.add (tb_continuous hI))).norm.pow 2).mul continuous_const
  have hint : IntegrableOn (fun t : Fin (Module.finrank ℝ (IR I)) → ℝ => ‖zmG I s (W + tb hI t)‖ ^ 2 * c)
      (cubeIco (Fin (Module.finrank ℝ (IR I)))) := by
    refine (hcont.continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1))).mono_set ?_
    rw [cubeIco_eq]
    exact Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self
  have hpar : HasSum (fun n => ‖zmC hI s n W‖ ^ 2)
      (∫ t in {x : Fin (Module.finrank ℝ (IR I)) → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
        ‖zmG I s (W + tb hI t)‖ ^ 2) := fibre_parseval hI hs W
  have hcube : ∫ t in cubeIco (Fin (Module.finrank ℝ (IR I))), ‖zmG I s (W + tb hI t)‖ ^ 2 * c =
      (∑' n, ‖zmC hI s n W‖ ^ 2) * c := by
    rw [integral_mul_const, setIntegral_congr_set (cube_ae_eq _), hpar.tsum_eq]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun t => by positivity),
    hcube, ← tsum_mul_right,
    ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hpar.summable.mul_right c)]
  congr 1
  funext n
  congr 1
  have hγ := gam_mem hI n
  have hadd := zmC_add hI hs hγ n (gam_pair hI n) 0 W
  rw [zero_add] at hadd
  have hB : zmB hI s (Col.wmap (IR I) (W + gam hI n)) = zmC hI s 0 (W + gam hI n) := by
    unfold zmB
    rw [Col.jj_wmap' hK, ← zeroMode_proj_two hI hs]
  have heps : ‖(X.eps (gam hI n) : ℂ)‖ = 1 := by
    rcases X.eps_pm _ hγ with h | h <;> simp [h]
  have hg : (gaugeExp I (gam hI n) W).re =
      2 * Real.pi * ∑ k, (Col.z (IR I) k (gam hI n)).im * (Col.z (IR I) k W).im +
        Real.pi * ∑ k, (Col.z (IR I) k (gam hI n)).im * (Col.z (IR I) k (gam hI n)).im +
        Real.pi * (Hf (Col.p2 (IR I) W) (Col.p2 (IR I) (gam hI n))).re +
        Real.pi * ‖Col.p2 (IR I) (gam hI n)‖ ^ 2 / 2 := by
    unfold gaugeExp
    simp [Complex.mul_re, Complex.mul_im, Complex.re_sum, Col.Hf_self_re, Finset.mul_sum]
  have hp2n := hnadd (Col.p2 (IR I) W) (Col.p2 (IR I) (gam hI n))
  rw [← hp2add] at hp2n
  have hucW : ‖Col.uc (IR I) (W + gam hI n)‖ ^ 2 =
      ∑ k, ((Col.z (IR I) k W).im + (Col.z (IR I) k (gam hI n)).im) ^ 2 := by
    rw [hucn]
    simp [z_add]
  have hsq : ∑ k, ((Col.z (IR I) k W).im + (Col.z (IR I) k (gam hI n)).im) ^ 2 =
      ∑ k, (Col.z (IR I) k W).im ^ 2 +
        2 * ∑ k, (Col.z (IR I) k (gam hI n)).im * (Col.z (IR I) k W).im +
        ∑ k, (Col.z (IR I) k (gam hI n)).im * (Col.z (IR I) k (gam hI n)).im := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  unfold GT.ptN2
  rw [hB, hadd, Col.norm_wmap hK, norm_mul, norm_mul, heps, one_mul, Complex.norm_exp, mul_pow, hE2,
    hp2n, hucW, hsq, hg, hc]
  rw [mul_comm (Real.exp _) (‖zmC hI s n W‖ ^ 2), mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 2
  push_cast
  ring

theorem YB_cube (hI : IsSplit P I) (hP : Ext.PackingCount) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec 1 1) (A0 : EuclideanSpace ℂ (Fin (gB (IR I)))) :
    ∫⁻ r in cubeIco (Fin (2 * Fintype.card (Fin (gB (IR I))))),
        ENNReal.ofReal ((YB hI hP 1).ptN2 1 (zmB hI s) (A0 + (bB hI hP).equivFun.symm r)) =
      ENNReal.ofReal ((YB hI hP 1).l2 1 (zmB hI s)) := by
  have hF : zmB hI s ∈ (Col.YB hI hP 1).Sec 1 := zeroMode_mem_sections hI hP hs
  have hE : ∀ a b : ℝ, Real.exp a ^ 2 * Real.exp b = Real.exp (2 * a + b) := fun a b => by
    rw [Real.exp_add, sq, ← Real.exp_add, two_mul]
  have hper : ∀ γ ∈ lat (Col.YB hI hP 1).b, ∀ v,
      (Col.YB hI hP 1).ptN2 1 (zmB hI s) (v + γ) = (Col.YB hI hP 1).ptN2 1 (zmB hI s) v := by
    intro γ hγ v
    have h1 := hF.2 γ hγ v
    have hka := (Col.YB hI hP 1).ka_abs γ hγ
    have hn : ‖v + γ‖ ^ 2 = ‖v‖ ^ 2 + 2 * (Hf v γ).re + ‖γ‖ ^ 2 := by
      rw [← Col.Hf_self_re, ← Col.Hf_self_re, ← Col.Hf_self_re, Col.Hf_add_l, Col.Hf_add_r,
        Col.Hf_add_r, Col.Hf_swap v γ]
      simp only [Complex.add_re, Complex.conj_re]
      ring
    have hre : ((((1 : ℕ) : ℂ) * (Real.pi : ℂ) * Hf v γ + ((1 : ℕ) : ℂ) * (Real.pi : ℂ) * Hf γ γ / 2)).re =
        Real.pi * (Hf v γ).re + Real.pi * ‖γ‖ ^ 2 / 2 := by
      rw [← Col.Hf_self_re]
      simp [Complex.add_re, Complex.mul_re]
    unfold GT.ptN2
    rw [h1, norm_mul, norm_mul, hka, one_mul, Complex.norm_exp, hre, mul_pow, mul_right_comm, hE, hn,
      mul_comm]
    congr 2
    push_cast
    ring
  have hBsymm : ∀ x : Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ,
      (Col.bB hI hP).equivFun.symm x = ∑ i, x i • (Col.bB hI hP) i := fun x =>
    Module.Basis.equivFun_symm_apply _ _
  have hBc : Continuous (Col.bB hI hP).equivFun.symm :=
    (Col.bB hI hP).equivFun.symm.toLinearMap.continuous_of_finiteDimensional
  have hcont : Continuous ((Col.YB hI hP 1).ptN2 1 (zmB hI s)) := by
    unfold GT.ptN2
    exact (hF.1.continuous.norm.pow 2).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  set g : (Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ) → ℝ :=
    fun x => (Col.YB hI hP 1).ptN2 1 (zmB hI s) ((Col.bB hI hP).equivFun.symm x) with hgdef
  have hgc : Continuous g := hcont.comp hBc
  have hgper : ∀ (x : Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ)
      (n : Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℤ), g (x + fun i => (n i : ℝ)) = g x := by
    intro x n
    simp only [hgdef, map_add (f := _)]
    apply hper
    rw [hBsymm]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  set a0 := (Col.bB hI hP).equivFun A0 with ha0
  have hshift : ∀ x, (Col.YB hI hP 1).ptN2 1 (zmB hI s) (A0 + (Col.bB hI hP).equivFun.symm x) =
      g (x + a0) := by
    intro x
    simp only [hgdef, map_add (f := _), ha0, LinearEquiv.symm_apply_apply]
    rw [add_comm]
  have hbox : ∫ x in {x : Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
      g (x + a0) = ∫ x in {x : Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
      g x := by
    have h := tof_box_shift (fun x => (g x : ℂ)) (Complex.continuous_ofReal.comp hgc)
      (fun x n => by simp only [hgper]) a0
    rw [integral_complex_ofReal, integral_complex_ofReal] at h
    exact_mod_cast h
  have hcube : ∫ x in cubeIco (Fin (2 * Fintype.card (Fin (gB (IR I))))), g (x + a0) =
      ∫ x in cubeIco (Fin (2 * Fintype.card (Fin (gB (IR I))))), g x := by
    rw [setIntegral_congr_set (cube_ae_eq _), setIntegral_congr_set (cube_ae_eq _)]
    exact hbox
  have hint : IntegrableOn (fun x => g (x + a0)) (cubeIco (Fin (2 * Fintype.card (Fin (gB (IR I)))))) := by
    refine ((hgc.comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1))).mono_set ?_
    rw [cubeIco_eq]
    exact Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self
  have hl2 : (Col.YB hI hP 1).l2 1 (zmB hI s) =
      ∫ x in cubeIco (Fin (2 * Fintype.card (Fin (gB (IR I))))), g (x + a0) := by
    unfold GT.l2
    rw [avg_fd_cube, hcube]
    rfl
  simp_rw [hshift]
  rw [hl2, ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => by simp only [hgdef]; unfold GT.ptN2; positivity)]

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

theorem cube_split {α β : Type} [Fintype α] [Fintype β] (f : (α ⊕ β → ℝ) → ENNReal)
    (hf : Measurable f) :
    ∫⁻ x in cubeIco (α ⊕ β), f x =
      ∫⁻ y in cubeIco β, ∫⁻ t in cubeIco α, f (fun k => Sum.elim t y k) := by
  have hmp := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : α ⊕ β => ℝ)
  rw [← hmp.setLIntegral_comp_preimage_emb
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : α ⊕ β => ℝ)).symm.measurableEmbedding]
  have hpre : (MeasurableEquiv.sumPiEquivProdPi (fun _ : α ⊕ β => ℝ)).symm ⁻¹' cubeIco (α ⊕ β) =
      cubeIco α ×ˢ cubeIco β := by
    ext ⟨t, y⟩
    simp [cubeIco, MeasurableEquiv.coe_sumPiEquivProdPi_symm, Sum.forall]
  rw [hpre, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm]
  · rfl
  · exact (hf.comp (MeasurableEquiv.sumPiEquivProdPi _).symm.measurable).aemeasurable

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

def What (hI : IsSplit P I) (hP : Ext.PackingCount) (a : Fin (Module.finrank ℝ (IR I)) → ℝ)
    (r : Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ) : Vsp X.dim :=
  ∑ j, a j • cp hI j + ∑ l, r l • cpp hI hP l

theorem uc_rsmul (c : ℝ) (v : Vsp X.dim) : uc (IR I) (c • v) = c • uc (IR I) v := by
  simp only [uc, z, Hf_rsmul_l, Complex.im_ofReal_mul, Finset.smul_sum, mul_smul]

theorem uc_sum {ι : Type} (F : Finset ι) (f : ι → Vsp X.dim) :
    uc (IR I) (∑ i ∈ F, f i) = ∑ i ∈ F, uc (IR I) (f i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using uc_rsmul (I := I) (0 : ℝ) (0 : Vsp X.dim)
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, uc_add, ih]

theorem uc_What (hI : IsSplit P I) (hP : Ext.PackingCount) (a r) :
    uc (IR I) (What hI hP a r) = ∑ j, a j • uc (IR I) (cp hI j) := by
  have h0 : ∀ l, uc (IR I) (cpp hI hP l) = 0 := fun l => uc_Ip (cpp_mem hI hP l)
  simp only [What, uc_add, uc_sum, uc_rsmul, h0, smul_zero, Finset.sum_const_zero, add_zero]

theorem wmap_What (hI : IsSplit P I) (hP : Ext.PackingCount) (a r) :
    wmap (IR I) (What hI hP a r) = wmap (IR I) (∑ j, a j • cp hI j) + (bB hI hP).equivFun.symm r := by
  rw [What, map_add (f := _)]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Module.Basis.equivFun_symm_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ContinuousLinearMap.map_smul_of_tower, cpp_wmap]

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

theorem uc_continuous : Continuous (uc (IR I) : Vsp X.dim → Vsp X.dim) := by
  let L : Vsp X.dim →ₗ[ℝ] Vsp X.dim :=
    { toFun := uc (IR I)
      map_add' := fun x y => uc_add x y
      map_smul' := fun c v => by simpa using uc_rsmul (I := I) c v }
  exact L.continuous_of_finiteDimensional

theorem What_continuous (hI : IsSplit P I) (hP : Ext.PackingCount) :
    Continuous fun p : (Fin (Module.finrank ℝ (IR I)) → ℝ) × (Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ) =>
      What hI hP p.1 p.2 := by
  unfold What
  fun_prop

theorem What_add (hI : IsSplit P I) (hP : Ext.PackingCount) (a r) (n : Fin (Module.finrank ℝ (IR I)) → ℤ) :
    What hI hP a r + gam hI n = What hI hP (a + fun i => (n i : ℝ)) r := by
  simp only [What, gam, Pi.add_apply, add_smul, Finset.sum_add_distrib, ← Int.cast_smul_eq_zsmul ℝ]
  abel

theorem zm_norm_eq (hI : IsSplit P I) (hP : Ext.PackingCount) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec 1 1) :
    X.l2 1 s = |(Col.ob (IR I)).toBasis.det (Ib hI)| *
      (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2) * (YB hI hP 1).l2 1 (zmB hI s) := by
  have hK := hK_of hI
  have hβm := zeroMode_mem_sections hI hP hs
  set g : Vsp X.dim → ℝ := fun v => X.ptN2 1 s (fun _ => v) with hg
  have hg' : g = fun v => ‖s (fun _ => v)‖ ^ 2 * Real.exp (-(((1 : ℕ) : ℝ) * Real.pi) * ‖v‖ ^ 2) := by
    funext v; simp only [hg, PT.ptN2, HC_one, Hf_self_re]
  have hgc : Continuous g := by
    rw [hg']
    exact ((hs.1.continuous.comp (continuous_pi fun _ => continuous_id)).norm.pow 2).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  have hg0 : ∀ v, 0 ≤ g v := fun v => by rw [hg']; positivity

  have h1 : X.l2 1 s = ∫ x in cubeIco _, g ((BB hI hP).equivFun.symm x) := by
    rw [X.l2_one_eq_toGT_l2_col1 s, GT.l2]
    have hper : ∀ γ ∈ Submodule.span ℤ (Set.range X.toGT.b), ∀ v,
        X.toGT.ptN2 1 (X.col1 s) (γ + v) = X.toGT.ptN2 1 (X.col1 s) v :=
      fun γ hγ v => lemS_periodic X.toGT 1 (X.column_mem_sections hs) hγ v
    rw [avg_fd_swap X.toGT.b (BB hI hP) (lat_BB hI hP).symm _ hper, avg_fd_cube]
    exact setIntegral_congr_fun (cubeIco_meas _) fun x _ => (X.pointNormSq_column s _).symm
  have hΦc : Continuous (BB hI hP).equivFun.symm := (BB hI hP).equivFun.symm.toContinuousLinearEquiv.continuous
  have hbox : ∀ κ : Type, [Fintype κ] → cubeIco κ ⊆ Set.Icc 0 1 := fun κ _ x hx =>
    ⟨fun i => (hx i).1, fun i => (hx i).2.le⟩
  have h2 : ENNReal.ofReal (X.l2 1 s) =
      ∫⁻ x in cubeIco _, ENNReal.ofReal (g ((BB hI hP).equivFun.symm x)) := by
    rw [h1]
    exact ofReal_integral_eq_lintegral_ofReal (f := fun x => g ((BB hI hP).equivFun.symm x))
      (((hgc.comp hΦc).continuousOn.integrableOn_compact isCompact_Icc).mono_set (hbox _))
      (Filter.Eventually.of_forall fun x => hg0 _)
  have hmeas1 : Measurable fun x => ENNReal.ofReal (g ((BB hI hP).equivFun.symm x)) :=
    ENNReal.measurable_ofReal.comp (hgc.comp hΦc).measurable
  rw [cube_split _ hmeas1] at h2
  have hΦ : ∀ t y, (BB hI hP).equivFun.symm (fun k => Sum.elim t y k) =
      What hI hP (fun j => y (Sum.inl j)) (fun l => y (Sum.inr l)) + tb hI t := by
    intro t y
    rw [Module.Basis.equivFun_symm_apply, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [BB_apply, Bf, Sum.elim_inl, Sum.elim_inr, What, tb]
    abel
  set Ψ : (Fin (Module.finrank ℝ (IR I)) → ℝ) → (Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ) → ℝ :=
    fun a r => (YB hI hP 1).ptN2 1 (zmB hI s) (wmap (IR I) (What hI hP a r)) *
      Real.exp (-(2 * Real.pi) * ‖uc (IR I) (What hI hP a r)‖ ^ 2) with hΨ
  have hΨc : Continuous fun p : (Fin (Module.finrank ℝ (IR I)) → ℝ) ×
      (Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ) => Ψ p.1 p.2 := by
    have hY : Continuous fun t => (YB hI hP 1).ptN2 1 (zmB hI s) t := by
      unfold GT.ptN2
      exact (hβm.1.continuous.norm.pow 2).mul (Real.continuous_exp.comp
        (continuous_const.mul (continuous_norm.pow 2)))
    have hW := What_continuous hI hP
    exact (hY.comp ((wmap (IR I)).continuous.comp hW)).mul (Real.continuous_exp.comp
      (continuous_const.mul ((continuous_norm.comp (uc_continuous.comp hW)).pow 2)))
  have hin : ∀ y : Fin (Module.finrank ℝ (IR I)) ⊕ Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ,
      ∫⁻ t in cubeIco _, ENNReal.ofReal (g ((BB hI hP).equivFun.symm (fun k => Sum.elim t y k))) =
        ∑' n : Fin (Module.finrank ℝ (IR I)) → ℤ, ENNReal.ofReal
          (Ψ ((fun j => y (Sum.inl j)) + fun i => (n i : ℝ)) (fun l => y (Sum.inr l))) := by
    intro y
    simp only [hΦ]
    refine (fibre_sum hI hP hs _).trans (tsum_congr fun n => ?_)
    rw [What_add]
  rw [lintegral_congr hin] at h2
  have hFm : Measurable fun y : Fin (Module.finrank ℝ (IR I)) ⊕ Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ =>
      ∑' n : Fin (Module.finrank ℝ (IR I)) → ℤ, ENNReal.ofReal
        (Ψ ((fun j => y (Sum.inl j)) + fun i => (n i : ℝ)) (fun l => y (Sum.inr l))) := by
    refine Measurable.tsum fun n => ENNReal.measurable_ofReal.comp ?_
    refine (hΨc.comp (Continuous.prodMk ?_ ?_)).measurable
    · exact (continuous_pi fun j => continuous_apply (Sum.inl j)).add continuous_const
    · exact continuous_pi fun l => continuous_apply (Sum.inr l)
  rw [cube_split _ hFm] at h2
  simp only [Sum.elim_inl, Sum.elim_inr] at h2
  have hΨm : ∀ r, Measurable fun a => ENNReal.ofReal (Ψ a r) := fun r =>
    ENNReal.measurable_ofReal.comp (hΨc.comp (continuous_id.prodMk continuous_const)).measurable
  have h3 : ∀ r : Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ,
      ∫⁻ a' in cubeIco _, ∑' n : Fin (Module.finrank ℝ (IR I)) → ℤ,
        ENNReal.ofReal (Ψ (a' + fun i => (n i : ℝ)) r) = ∫⁻ a, ENNReal.ofReal (Ψ a r) := by
    intro r
    rw [lintegral_tsum (f := fun (n : Fin (Module.finrank ℝ (IR I)) → ℤ)
        (a' : Fin (Module.finrank ℝ (IR I)) → ℝ) => ENNReal.ofReal (Ψ (a' + fun i => (n i : ℝ)) r))
        (fun n => ((hΨm r).comp (measurable_id.add_const _)).aemeasurable),
      unfold_Zn (fun a => ENNReal.ofReal (Ψ a r))]
  rw [lintegral_congr h3, lintegral_lintegral_swap (f := fun r a => ENNReal.ofReal (Ψ a r))
    (ENNReal.measurable_ofReal.comp (hΨc.comp (continuous_snd.prodMk continuous_fst)).measurable).aemeasurable] at h2
  have h4 : ∀ a : Fin (Module.finrank ℝ (IR I)) → ℝ,
      ∫⁻ r in cubeIco _, ENNReal.ofReal (Ψ a r) = ENNReal.ofReal ((YB hI hP 1).l2 1 (zmB hI s)) *
        ENNReal.ofReal (Real.exp (-(2 * Real.pi) * ‖∑ j, a j • uc (IR I) (cp hI j)‖ ^ 2)) := by
    intro a
    simp only [hΨ, uc_What, wmap_What]
    simp only [ENNReal.ofReal_mul (pointNormSq_nonneg_quotient hP hI _ _)]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, YB_cube hI hP hs]
  rw [lintegral_congr h4, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h2
  have hub : ∀ j i, inner ℝ ((⟨uc (IR I) (cp hI j), uc_mem _ _⟩ : IR I)) (Ib hI i) =
      if j = i then (1 : ℝ) else 0 := fun j i => by
    rw [Submodule.coe_inner, inner_uc (IR I) _ _ (Ib hI i).2, cp_pair]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Pi.single_apply, Ne.symm h]
  have hgl := gauss_lin (Col.ob (IR I)) (fun j => (⟨uc (IR I) (cp hI j), uc_mem _ _⟩ : IR I))
    (Ib hI) hub
  have hnorm : ∀ a : Fin (Module.finrank ℝ (IR I)) → ℝ,
      ‖∑ j, a j • (⟨uc (IR I) (cp hI j), uc_mem _ _⟩ : IR I)‖ = ‖∑ j, a j • uc (IR I) (cp hI j)‖ :=
    fun a => by
      have h : ((∑ j, a j • (⟨uc (IR I) (cp hI j), uc_mem _ _⟩ : IR I) : IR I) : Vsp X.dim) =
          ∑ j, a j • uc (IR I) (cp hI j) := by simp [Submodule.coe_sum]
      rw [← h]; rfl
  simp only [hnorm] at hgl
  have hl0 : 0 ≤ (YB hI hP 1).l2 1 (zmB hI s) := by
    rw [GT.l2, MeasureTheory.average_eq]
    exact smul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (integral_nonneg fun _ => by unfold GT.ptN2; positivity)
  have hX0 : 0 ≤ X.l2 1 s := by
    rw [X.l2_one_eq_toGT_l2_col1 s, GT.l2, MeasureTheory.average_eq]
    exact smul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (integral_nonneg fun _ => by unfold GT.ptN2; positivity)
  rw [hgl, ← ENNReal.ofReal_mul hl0] at h2
  have h' := (ENNReal.ofReal_eq_ofReal_iff hX0 (mul_nonneg hl0 (mul_nonneg (abs_nonneg _)
    (Real.rpow_nonneg (by norm_num) _)))).1 h2
  rw [h']
  simp only [dK]
  ring

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory

theorem zm_norm {E : Type} [Field E] [NumberField E] [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
    {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I) (hP : Ext.PackingCount)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    |(Col.ob (IR I)).toBasis.det (ZM.Ib hI)| * (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2) *
      (Col.YB hI hP 1).l2 1 (ZM.zmB hI s) ≤ X.l2 1 s :=
  le_of_eq (ZM.zm_norm_eq hI hP hs).symm

end ReciprocityTheory.ChartRestriction.G.I2
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ZmMem
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory

theorem zm_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
    {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I) (hP : Ext.PackingCount)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    ZM.zmB hI s ∈ (Col.YB hI hP 1).Sec 1 :=
  zeroMode_mem_sections hI hP hs

theorem zm_pt {E : Type} [Field E] [NumberField E] [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
    {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I) (hP : Ext.PackingCount)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) (w : Vsp X.dim) (T M : ℝ)
    (hT : ∀ F : Finset (Vsp X.dim), (∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x) →
      ∑ y ∈ F, Real.exp (-Real.pi * ‖uMap I w - y‖ ^ 2) ≤ T)
    (hM : ∀ t, (Col.YB hI hP 1).ptN2 1 (ZM.zmB hI s) t ≤ M) :
    Real.sqrt (X.ptN2 1 s fun _ => w) ≤ Real.sqrt M * T :=
  zeroMode_pointwise_bound hI hP hs w T M hT hM

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex MeasureTheory

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem l2_nonneg_GT {ι : Type} [Fintype ι] (Y : GT ι) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) :
    0 ≤ Y.l2 q F := by
  unfold GT.l2
  rw [MeasureTheory.setAverage_eq]
  refine smul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) (MeasureTheory.integral_nonneg fun v => ?_)
  unfold GT.ptN2
  exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem zeroMode [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    ∃ β ∈ (Col.YB hI hP 1).Sec 1,
      (∀ w : Vsp X.dim, ∀ T M : ℝ, (∀ F : Finset (Vsp X.dim), (∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x) →
          ∑ y ∈ F, Real.exp (-Real.pi * ‖uMap I w - y‖ ^ 2) ≤ T) →
        (∀ t, (Col.YB hI hP 1).ptN2 1 β t ≤ M) →
        Real.sqrt (X.ptN2 1 s fun _ => w) ≤ Real.sqrt M * T) ∧
      ∃ a : Fin (Module.finrank ℝ (IR I)) → IR I, (∀ i, (a i : Vsp X.dim) ∈ I) ∧
        (Col.ob (IR I)).toBasis.det a ≠ 0 ∧
        |(Col.ob (IR I)).toBasis.det a| * (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2) *
          (Col.YB hI hP 1).l2 1 β ≤ X.l2 1 s :=
  ⟨ZM.zmB hI s, zm_mem hI hP hs, fun w T M hT hM => zm_pt hI hP hs w T M hT hM, ZM.Ib hI,
    ZM.Ib_mem hI, ZM.Ib_det_ne hI, zm_norm hI hP hs⟩

theorem tof_yb_sup [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) (hS : GSupStatement) {β : EuclideanSpace ℂ
    (Fin (Col.gB (IR I))) → ℂ} (hβ : β ∈ (Col.YB hI hP 1).Sec 1) (t : EuclideanSpace ℂ (Fin (Col.gB (IR I)))) :
    (Col.YB hI hP 1).ptN2 1 β t ≤ Real.exp P.p1 ^ 2 * (Col.YB hI hP 1).l2 1 β := by
  set Y := Col.YB hI hP 1 with hY
  have key := hS (Fin (Col.gB (IR I))) Y 1 le_rfl β hβ t
  rw [Fintype.card_fin] at key
  set g : ℕ := X.gA with hg
  have hgbg : (Col.gB (IR I)) ≤ g := by
    have h1 := Submodule.finrank_le (Col.V2 (IR I))
    rw [finrank_euclideanSpace, X.card_idx] at h1
    exact h1
  have hg2 : 2 ≤ g := P.hfr
  have hgpos : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hqth := one_le_sqrt_q_th P
  have hth := Col.th_pos P
  set y : ℝ := 1 + 6 * Real.sqrt (g * P.q) with hy
  have hy1 : 1 ≤ y := by have := Real.sqrt_nonneg (g * P.q); linarith
  have hl0 := l2_nonneg_GT Y 1 β
  have hbase : 1 + 4 * Real.sqrt (2 * (Col.gB (IR I))) / (Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * Y.la1) ≤ y := by
    rcases Nat.eq_zero_or_pos (Col.gB (IR I)) with h0 | hpos
    · have h00 : Real.sqrt (2 * ((Col.gB (IR I)) : ℝ)) = 0 := by rw [h0]; simp
      rw [h00]; simp; linarith
    · have hla : P.th ≤ Y.la1 := by
        apply le_csInf
        · refine ⟨‖Y.b ⟨0, by rw [Fintype.card_fin]; omega⟩‖, Y.b ⟨0, by rw [Fintype.card_fin]; omega⟩, Submodule.subset_span ⟨_, rfl⟩,
            Y.b.ne_zero _, rfl⟩
        · rintro _ ⟨x, hx, hne, rfl⟩
          exact Col.GB_norm hI ((Col.YB_lat hI hP 1).1 hx) hne
      have hla0 : 0 < Y.la1 := lt_of_lt_of_le hth hla
      have hpi : 1 ≤ Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) := by
        rw [Nat.cast_one, one_mul, Real.one_le_sqrt]; linarith [Real.pi_gt_three]
      have hden : 0 < Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * Y.la1 := by positivity
      have hA : 4 * Real.sqrt (2 * (Col.gB (IR I))) / (Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * Y.la1) ≤
          6 * Real.sqrt (g * P.q) := by
        rw [div_le_iff₀ hden]
        have hgb' : Real.sqrt (2 * ((Col.gB (IR I)) : ℝ)) ≤ Real.sqrt (2 * g) := by
          apply Real.sqrt_le_sqrt; have : ((Col.gB (IR I)) : ℝ) ≤ g := by exact_mod_cast hgbg
          linarith
        rw [Real.sqrt_mul (by norm_num) (g : ℝ), Real.sqrt_mul hgpos.le] at *
        have hs2 : Real.sqrt 2 ≤ 1.5 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        have hsg := Real.sqrt_pos.2 hgpos
        have hsq := Real.sqrt_nonneg (P.q : ℝ)
        have h1 : 1 ≤ Real.sqrt P.q * Y.la1 :=
          le_trans hqth (mul_le_mul_of_nonneg_left hla hsq)
        have h2 : 1 ≤ Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * (Real.sqrt P.q * Y.la1) := by
          nlinarith
        nlinarith
      rw [hy]; linarith
  have hB : 2 * ((1 : ℕ) : ℝ) ^ (Col.gB (IR I)) * (1 + 4 * Real.sqrt (2 * (Col.gB (IR I))) /
      (Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * Y.la1)) ^ (2 * (Col.gB (IR I))) ≤ Real.exp P.p1 ^ 2 := by
    have hp : Real.exp P.p1 ^ 2 = Real.exp 2 * y ^ (2 * g) := by
      rw [← Real.exp_nat_mul, Par.p1, ← hg, ← hy]
      rw [show ((2 : ℕ) : ℝ) * (1 + g * Real.log y) = 2 + ((2 * g : ℕ) : ℝ) * Real.log y by
        push_cast; ring]
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by linarith)]
    rw [hp]
    have h2e : (2 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ); linarith
    have h0 : 0 ≤ 4 * Real.sqrt (2 * (Col.gB (IR I))) / (Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * Y.la1) := by
      apply div_nonneg (by positivity)
      apply mul_nonneg (Real.sqrt_nonneg _)
      rw [GT.la1]; apply Real.sInf_nonneg; rintro _ ⟨x, -, -, rfl⟩; exact norm_nonneg _
    have hb : (1 + 4 * Real.sqrt (2 * (Col.gB (IR I))) /
        (Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * Y.la1)) ^ (2 * (Col.gB (IR I))) ≤ y ^ (2 * g) := by
      calc _ ≤ y ^ (2 * (Col.gB (IR I))) := pow_le_pow_left₀ (by linarith) hbase _
        _ ≤ y ^ (2 * g) := pow_le_pow_right₀ hy1 (by omega)
    exact mul_le_mul (by rw [Nat.cast_one, one_pow, mul_one]; exact h2e) hb
      (pow_nonneg (by linarith) _) (by positivity)
  exact le_trans key (mul_le_mul_of_nonneg_right hB hl0)

theorem perFactor_of [IsCMField E] (hx : Ext.All) (hS : GSupStatement) {X : PT E} {DF : ℕ}
    (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hph : 0 < P.ph) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    PerFactor P I s := by
  have hP : Ext.PackingCount := hx.1
  have hG : Ext.GHadamard := hx.2.2.2.1
  obtain ⟨β, hβ, hpt, a, haI, hdet, hl2⟩ := zeroMode hI hP hs
  set Y := Col.YB hI hP 1 with hY
  have hLS := tof_yb_sup hI hP hS hβ
  have hl0 := l2_nonneg_GT Y 1 β
  intro w
  obtain ⟨y0, hy0, hsum⟩ := tof_gauss_min_sum P hI hP (uMap I w) (isU_uMap I w).1
  refine ⟨y0, hy0, ?_⟩
  set d := dstar (E := E) P.m with hd
  set Eg := Real.exp (-(Real.pi / 2) * ‖uMap I w - uMap I y0‖ ^ 2) with hEg
  set T := 2 * (3 * (d : ℝ)) ^ d * Eg with hT
  have hpw := hpt w T (Real.exp P.p1 ^ 2 * Y.l2 1 β) hsum hLS
  have hp2 : Real.exp P.p2 = 2 * (3 * (d : ℝ)) ^ d := by
    rw [Par.p2, Real.exp_log]
    have h := tof_two_le_dstar P
    have : (2 : ℝ) ≤ d := by exact_mod_cast h
    exact mul_pos two_pos (pow_pos (by linarith) _)
  have hRHS : 0 ≤ Real.exp (P.p1 + P.p2 + d) * (P.ka0 * P.ph) ^ ((d : ℝ) / 4) * Eg :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (Real.rpow_nonneg (mul_nonneg (Par_ka0_nonneg P) hph.le) _)) (Real.exp_pos _).le
  rcases hl0.lt_or_eq with hlpos | hleq
  · set c := |(Col.ob (IR I)).toBasis.det a| with hc
    have hcpos : 0 < c := abs_pos.2 hdet
    have h2pos : 0 < (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
    have hcl : 0 < c * (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2) := mul_pos hcpos h2pos
    have hsl : 0 < X.l2 1 s := lt_of_lt_of_le (by positivity) hl2
    have hcov := tof_covol_lb P hI hG (Col.ob (IR I)) a haI hdet
    have hinv := tof_inv_sqrt_le P hph (Module.finrank ℝ (IR I)) (tof_finrank_IR_le P hI) c hcpos hcov
    have hden : Real.sqrt (c * (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2)) * Real.sqrt (Y.l2 1 β) ≤
        Real.sqrt (X.l2 1 s) := by
      rw [← Real.sqrt_mul hcl.le]; exact Real.sqrt_le_sqrt hl2
    have hnum : Real.sqrt (X.ptN2 1 s fun _ => w) ≤
        Real.exp P.p1 * Real.sqrt (Y.l2 1 β) * T := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Real.exp_pos _).le] at hpw
      exact hpw
    have hsc := Real.sqrt_pos.2 hcl
    have hsb := Real.sqrt_pos.2 hlpos
    rw [div_le_iff₀ (Real.sqrt_pos.2 hsl)]
    calc Real.sqrt (X.ptN2 1 s fun _ => w) ≤ Real.exp P.p1 * Real.sqrt (Y.l2 1 β) * T := hnum
      _ = Real.exp P.p1 * T * (1 / Real.sqrt (c * (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2))) *
            (Real.sqrt (c * (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2)) * Real.sqrt (Y.l2 1 β)) := by
          field_simp
      _ ≤ Real.exp P.p1 * T * (Real.exp d * (P.ka0 * P.ph) ^ ((d : ℝ) / 4)) *
            Real.sqrt (X.l2 1 s) := by
          have hTn : 0 ≤ T := by
            rw [hT]
            have h := tof_two_le_dstar P
            have : (2 : ℝ) ≤ d := by exact_mod_cast h
            exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by linarith) _))
              (Real.exp_pos _).le
          have hA : 0 ≤ Real.exp P.p1 * T := mul_nonneg (Real.exp_pos _).le hTn
          exact mul_le_mul (mul_le_mul_of_nonneg_left hinv hA) hden (by positivity)
            (mul_nonneg hA (mul_nonneg (Real.exp_pos _).le
              (Real.rpow_nonneg (mul_nonneg (Par_ka0_nonneg P) hph.le) _)))
      _ = Real.exp (P.p1 + P.p2 + d) * (P.ka0 * P.ph) ^ ((d : ℝ) / 4) * Eg *
            Real.sqrt (X.l2 1 s) := by
          rw [hT, ← hp2, Real.exp_add, Real.exp_add]; ring
  · rw [← hleq, mul_zero, Real.sqrt_zero, zero_mul] at hpw
    have : Real.sqrt (X.ptN2 1 s fun _ => w) = 0 := le_antisymm hpw (Real.sqrt_nonneg _)
    rw [this, zero_div]; exact hRHS

end

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex NumberField

theorem tOf (hx : Ext.All) (hs : SplitStatement) (hS : GSupStatement) (hd : DimStatement) :
    TStatement := by
  intro E _ _ _ X DF P r1 hr1 a ha hgen s hsmem hs0
  refine ⟨fun hph => ?_, fun h0 => ?_⟩
  · obtain ⟨I, hI⟩ := hs E X DF P
    exact t_assemble P hI (perFactor_of hx hS P hI hph hsmem) r1 hr1 a ha hgen hph
  · calc ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a j) / Real.sqrt (X.l2 1 s)
        ≤ ∏ _j : Fin X.r, Real.exp P.p1 :=
          Finset.prod_le_prod₀ (fun j _ => div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            (fun j _ => sup_ratio_le_of_phase_zero P hS hsmem h0 (a j))
      _ = Real.exp (X.r * P.p1) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]

end ReciprocityTheory.ChartRestriction.G.I2

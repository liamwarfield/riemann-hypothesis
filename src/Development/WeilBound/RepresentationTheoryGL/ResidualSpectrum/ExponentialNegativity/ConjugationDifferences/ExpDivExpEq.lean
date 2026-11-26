module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConjugationDifferences.ExistsNormConjArchLe
open Set Filter Topology
open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing Pointwise
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
  GroundTheory.Automorphic.CuspidalSpectrum

noncomputable section

namespace PositivityTheory.Rg.Rs.diffstep

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem conjArch_mul_right {r : ℕ} (y q : AdelicGLn.AdelicGL K n) (P : UPos n r → 𝔸[K]) :
    conjArch K n (y * q) P =
      archMat K n ((q⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * conjArch K n y P *
        archMat K n (q : Matrix (Fin n) (Fin n) 𝔸[K]) := by
  have h : (((y * q)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * blockEntry P *
      ((y * q : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      ((q⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        (((y⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * blockEntry P *
          (y : Matrix (Fin n) (Fin n) 𝔸[K])) * (q : Matrix (Fin n) (Fin n) 𝔸[K]) := by
    rw [_root_.mul_inv_rev]
    simp only [Units.val_mul, Matrix.mul_assoc]
  change archMat K n _ = archMat K n _ * archMat K n _ * archMat K n _
  rw [h, map_mul, map_mul]

theorem exists_norm_conjArch_le {ω Q : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω)
    (hωB : ω ⊆ ((adelicBorel : Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)))
    (hQ : IsCompact Q) {t : ℝ} (ht : 0 < t) {r : ℕ} (hr : 0 < r) (hrn : r < n)
    {𝒮 : Set (InfiniteAdeleRing K)} (h𝒮 : IsCompact 𝒮) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i),
      (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ q ∈ Q, ∀ P : UPos n r → 𝔸[K], (∀ p, (P p).2 = 0) → (∀ p, (P p).1 ∈ 𝒮) →
        ‖conjArch K n (b * diagUnits n (fun i => posIdele (ρ i) (hρ i)) * q) P‖ ≤
          C * (ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩) := by
  obtain ⟨C₁, hC₁⟩ := exists_norm_archMat_conj_le hω hωB ht hr hrn h𝒮
  obtain ⟨c1, hc1⟩ := hQ.exists_bound_of_continuousOn
    (f := fun k : AdelicGLn.AdelicGL K n => archMat K n (k : Matrix (Fin n) (Fin n) 𝔸[K]))
    (continuous_archMat.comp Units.continuous_val).continuousOn
  obtain ⟨c2, hc2⟩ := hQ.exists_bound_of_continuousOn
    (f := fun k : AdelicGLn.AdelicGL K n =>
      archMat K n ((k⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))
    (continuous_archMat.comp Units.continuous_coe_inv).continuousOn
  set c := max (max c1 c2) 0
  have hc0 : 0 ≤ c := le_max_right _ _
  set C₁' := max C₁ 0
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  refine ⟨c * C₁' * c, by positivity, ?_⟩
  intro b hb ρ hρ hsieg q hq P hP2 hP1
  set a := diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i))
  set s := ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩
  have hs : 0 ≤ s := div_nonneg (hρ _).le (hρ _).le
  have h1 := hC₁ b hb ρ hρ hsieg 1 (maxCompact (K := K) (n := n)).one_mem P hP2 hP1
  rw [mul_one] at h1
  have hY : ‖conjArch K n (b * a) P‖ ≤ C₁' * s :=
    h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hs)
  have hq1 : ‖archMat K n (q : Matrix (Fin n) (Fin n) 𝔸[K])‖ ≤ c :=
    (hc1 q hq).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hq2 : ‖archMat K n ((q⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])‖ ≤ c :=
    (hc2 q hq).trans ((le_max_right _ _).trans (le_max_left _ _))
  rw [conjArch_mul_right]
  calc ‖archMat K n ((q⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        conjArch K n (b * a) P * archMat K n (q : Matrix (Fin n) (Fin n) 𝔸[K])‖
      ≤ ‖archMat K n ((q⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])‖ *
          ‖conjArch K n (b * a) P‖ * ‖archMat K n (q : Matrix (Fin n) (Fin n) 𝔸[K])‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ c * (C₁' * s) * c := by gcongr
    _ = c * C₁' * c * s := by ring

end PositivityTheory.Rg.Rs.diffstep

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConjugationDifferences.ExistsNatCastConjMem
open Set Filter Topology
open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing Pointwise
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
  GroundTheory.Automorphic.CuspidalSpectrum

noncomputable section

namespace PositivityTheory.Rg.Rs.diffstep

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem exists_natCast_conj_mem (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))) {ω Q : Set (AdelicGLn.AdelicGL K n)}
    (hω : IsCompact ω) (hQ : IsCompact Q) (r : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i),
      ∀ k ∈ Q, ∀ z : UPos n r → 𝔸[K], (∀ p, (z p).1 = 0) →
        (∀ p, ∃ a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K,
          (z p).2 = (M : FiniteAdeleRing (𝓞 K) K) * a) →
        ∃ u : U, ((b * diagUnits n (fun i => posIdele (ρ i) (hρ i)) * k)⁻¹ :
            AdelicGLn.AdelicGL K n) * unipGL z * (b * diagUnits n (fun i => posIdele (ρ i) (hρ i)) * k) =
          finEmb K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) := by
  classical
  set U' : Set (AdelicGLn.FiniteAdelicGL K n) :=
    Subtype.val '' (U : Set (AdelicGLn.integralFiniteGL K n))
  have hU' : IsOpen U' := (AdelicGLn.isOpen_integralFiniteGL K n).isOpenMap_subtype_val _ hU
  have h1U' : (1 : AdelicGLn.FiniteAdelicGL K n) ∈ U' := ⟨1, U.one_mem, rfl⟩
  set Cf : Set (AdelicGLn.FiniteAdelicGL K n) :=
    (fun p : AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n => (AdelicGLn.prodEquiv K n (p.1 * p.2)).2) ''
      (ω ×ˢ Q)
  have hCf : IsCompact Cf := (hω.prod hQ).image
    (continuous_snd.comp ((AdelicGLn.prodEquiv K n).continuous.comp (continuous_fst.mul continuous_snd)))
  have hcont : Continuous fun q : (UPos n r → FiniteAdeleRing (𝓞 K) K) × AdelicGLn.FiniteAdelicGL K n =>
      q.2⁻¹ * unipGL q.1 * q.2 :=
    (continuous_snd.inv.mul (continuous_unipGL'.comp continuous_fst)).mul continuous_snd
  have hev : ∀ᶠ w in 𝓝 (0 : UPos n r → FiniteAdeleRing (𝓞 K) K), ∀ c ∈ Cf,
      c⁻¹ * unipGL w * c ∈ U' := by
    refine hCf.eventually_forall_of_forall_eventually fun c _ => ?_
    refine (hcont.tendsto ((0 : UPos n r → FiniteAdeleRing (𝓞 K) K), c)).eventually
      (hU'.mem_nhds ?_)
    simp only [unipGL_zero, mul_one, inv_mul_cancel]
    exact h1U'
  rw [nhds_pi] at hev
  have hev' : {w : UPos n r → FiniteAdeleRing (𝓞 K) K | ∀ c ∈ Cf, c⁻¹ * unipGL w * c ∈ U'} ∈
      Filter.pi fun _ => 𝓝 (0 : FiniteAdeleRing (𝓞 K) K) := hev
  rw [Filter.mem_pi] at hev'
  obtain ⟨I, -, tt, htt, hIt⟩ := hev'
  obtain ⟨M, hM, hMW⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_natCast_mul_mem_of_mem_nhds K (Filter.iInter_mem.2 htt)
  refine ⟨M, hM, fun b hb ρ hρ k hk z hz1 hz2 => ?_⟩
  set w : UPos n r → FiniteAdeleRing (𝓞 K) K := fun p => (z p).2
  have hw : w ∈ I.pi tt := fun p _ => by
    obtain ⟨a, ha, hza⟩ := hz2 p
    have := hMW a ha
    rw [mem_iInter] at this
    change (z p).2 ∈ tt p
    rw [hza]
    exact this p
  set c := (AdelicGLn.prodEquiv K n (b * k)).2
  have hc : c ∈ Cf := ⟨(b, k), ⟨hb, hk⟩, rfl⟩
  obtain ⟨u, huU, hu⟩ := hIt hw c hc
  refine ⟨⟨u, huU⟩, ?_⟩
  apply (AdelicGLn.prodEquiv K n).injective
  rw [prodEquiv_finEmb]
  refine Prod.ext ?_ ?_
  · rw [map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, Prod.fst_inv,
      prodEquiv_unipGL_fst z hz1, mul_one, inv_mul_cancel]
  · change _ = (u : AdelicGLn.FiniteAdelicGL K n)
    rw [hu, map_mul, map_mul, map_inv, Prod.snd_mul, Prod.snd_mul, Prod.snd_inv,
      prodEquiv_unipGL_snd]
    simp only [c, map_mul, Prod.snd_mul, prodEquiv_diagUnits_posIdele_snd ρ hρ, mul_one]
    rfl

end PositivityTheory.Rg.Rs.diffstep

end
end

noncomputable section

open NumberField MeasureTheory Filter Topology
open scoped NumberField.AdeleRing Pointwise
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
  GroundTheory.Automorphic.CuspidalSpectrum

namespace PositivityTheory.Rg.Rs

namespace diffstep

theorem sum_update_sub {n r : ℕ} (hrn : r < n) (m s : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, Function.update m r (m r - 1) i * s i =
      ∑ i ∈ Finset.range n, m i * s i - s r := by
  have h : ∀ i, Function.update m r (m r - 1) i * s i = m i * s i - (if r = i then s i else 0) := by
    intro i
    by_cases hi : i = r
    · subst hi
      simp only [Function.update_self, if_true]
      ring
    · simp [Function.update_of_ne hi, Ne.symm hi]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    if_pos (Finset.mem_range.2 hrn)]

theorem siegel_of_sr {n : ℕ} {x : Fin n → ℝ} {t₀ : ℝ} (hx : ∀ r, -t₀ ≤ An.sr x r) :
    ∀ i j : Fin n, (j : ℕ) = i + 1 → Real.exp (-t₀) * Real.exp (x j) ≤ Real.exp (x i) := by
  intro i j hij
  have h := hx j
  simp only [An.sr] at h
  rw [dite_eq_left (show 0 < (j : ℕ) ∧ (j : ℕ) < n from ⟨by omega, j.2⟩)] at h
  have e : x ⟨(j : ℕ) - 1, by omega⟩ = x i := congrArg x (Fin.ext (by simp; omega))
  rw [e] at h
  rw [← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith)

theorem exp_div_exp_eq {n r : ℕ} (hr : 0 < r) (hrn : r < n) (x : Fin n → ℝ) :
    Real.exp (x ⟨r, hrn⟩) / Real.exp (x ⟨r - 1, by omega⟩) = Real.exp (-An.sr x r) := by
  rw [An.sr, dite_eq_left ⟨hr, hrn⟩, ← Real.exp_sub]
  congr 1
  ring

end diffstep

open diffstep in
theorem diffstep_holds : An.DiffStep := by
  intro K _ _ n φ m r hr hrn hN hB ω hω hωB t₀ Q hQ
  obtain ⟨U, hU, hlev⟩ := hN.level
  obtain ⟨M, hM, hMc⟩ := exists_natCast_conj_mem U hU hω hQ r
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_conjArch_le hω hωB hQ (Real.exp_pos (-t₀)) hr hrn
    (isCompact_scaledInfSet (K := K) M)
  obtain ⟨Q₀, C₂, hQ₀, hC₂, hlip⟩ := hN.lip (C₁ * Real.exp t₀)
  obtain ⟨C₃, hC₃⟩ := hB ω hω hωB t₀ (Q * Q₀) (hQ.mul hQ₀)
  set C₃' := max C₃ 0 with hC₃'
  have hC₃'0 : 0 ≤ C₃' := le_max_right _ _
  refine ⟨C₂ * C₁ * C₃', ?_⟩
  intro b hb x hx q hq
  set g := b * An.tor K x * q with hg
  set S := ∑ i ∈ Finset.range n, m i * An.sr x i with hS
  have hsieg := siegel_of_sr hx
  have hpt : ∀ X ∈ scaledUnipFD K n r M, ‖φ g - φ (unipGL X * g)‖ ≤
      C₂ * (C₁ * Real.exp (-An.sr x r)) * (C₃' * Real.exp S) := by
    intro X hX
    set Y := conjArch K n g (truncInf X) with hY
    have hYn : ‖Y‖ ≤ C₁ * Real.exp (-An.sr x r) := by
      have h := hC₁ b hb (fun i => Real.exp (x i)) (fun i => Real.exp_pos _) hsieg q hq (truncInf X)
        (fun p => rfl) (fun p => infinite_mem_scaledInfSet hM hX p)
      rw [exp_div_exp_eq hr hrn x] at h
      exact h
    have hYR : ‖Y‖ ≤ C₁ * Real.exp t₀ :=
      hYn.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith [hx r])) hC₁0)
    obtain ⟨u, hu⟩ := hMc b hb (fun i => Real.exp (x i)) (fun i => Real.exp_pos _) q hq (truncFin X)
      (fun p => rfl) (fun p => exists_finite_eq_natCast_mul hM hX p)
    have hu' : g⁻¹ * unipGL (truncFin X) * g =
        finEmb K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) := hu
    have hdecomp : unipGL X * g = g * archExp Y * (g⁻¹ * unipGL (truncFin X) * g) := by
      rw [hY, ← conj_unipGL_eq_archExp g (truncInf X) (fun p => rfl)]
      conv_lhs => rw [← truncInf_add_truncFin X, unipGL_add]
      group
    have heq : φ (unipGL X * g) = φ (g * archExp Y) := by rw [hdecomp, hu', hlev]
    have hMg : ∀ q' ∈ Q₀, ‖φ (g * q')‖ ≤ C₃' * Real.exp S := by
      intro q' hq'
      have h := hC₃ b hb x hx (q * q') (Set.mul_mem_mul hq hq')
      rw [show g * q' = b * An.tor K x * (q * q') by rw [hg, mul_assoc]]
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have hl := hlip g Y (C₃' * Real.exp S) (conjArch_mul_conjArch _ _ _) hYR hMg
    rw [norm_sub_rev, heq]
    calc _ ≤ C₂ * ‖Y‖ * (C₃' * Real.exp S) := hl
      _ ≤ _ := by gcongr
  have hD := isAddFundamentalDomain_scaledUnipFD (K := K) (n := n) (r := r) hM
  have hD1 := unipMeasure_scaledUnipFD (K := K) (n := n) (r := r) hM
  obtain ⟨Cc, hCc, hDC⟩ := exists_isCompact_superset_scaledUnipFD (K := K) (n := n) r hM
  have hint : IntegrableOn (fun X => φ (unipGL X * g)) (scaledUnipFD K n r M) (unipMeasure K n r) :=
    ((hN.cont.comp (continuous_unipGL.mul continuous_const)).continuousOn.integrableOn_compact
      hCc).mono_set hDC
  have hfin : unipMeasure K n r (scaledUnipFD K n r M) < ⊤ := by
    rw [hD1]
    exact ENNReal.one_lt_top
  have hct : An.ctn r φ g = ∫ X in scaledUnipFD K n r M, φ (unipGL X * g) ∂unipMeasure K n r := by
    rw [An.ctn, measureReal_def, unipMeasure_unipFundamentalDomain, ENNReal.toReal_one,
      Complex.ofReal_one, inv_one, one_mul]
    exact constantTerm_eq_setIntegral hN.left hD g
  have hdiff : φ g - An.ctn r φ g =
      ∫ X in scaledUnipFD K n r M, (φ g - φ (unipGL X * g)) ∂unipMeasure K n r := by
    have hconst : IntegrableOn (fun _ => φ g) (scaledUnipFD K n r M) (unipMeasure K n r) :=
      integrableOn_const hfin.ne enorm_ne_top
    rw [hct, integral_sub hconst hint, setIntegral_const, measureReal_def, hD1,
      ENNReal.toReal_one, one_smul]
  change ‖φ g - An.ctn r φ g‖ ≤ _
  rw [hdiff]
  refine (norm_setIntegral_le_of_norm_le_const hfin hpt).trans (le_of_eq ?_)
  rw [measureReal_def, hD1, ENNReal.toReal_one, mul_one, sum_update_sub hrn, ← hS, sub_eq_add_neg,
    Real.exp_add]
  ring

end PositivityTheory.Rg.Rs

end

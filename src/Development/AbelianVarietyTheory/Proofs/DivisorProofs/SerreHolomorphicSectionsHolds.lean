module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSectionPolynomialGrowth
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEqMulOfContinuousOnQuotient

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfEvEqOfSmoothOfRelativeDimension
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory

theorem eq_of_ev_eq_of_smoothOfRelativeDimension :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → ∀ (W : Y.Opens) (a b : Γ(Y, W)), (∀ y ∈ ptsIn p (RingHom.id ℂ) W, ev p (RingHom.id ℂ) W a y = ev p (RingHom.id ℂ) W b y) → a = b := by
  intro Y p D hp W a b hab
  have hsm : Smooth p := SmoothOfRelativeDimension.smooth D p
  have hred : IsReduced Y :=
    (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ Y p hsm).1
  refine TopCat.Presheaf.IsSheaf.section_ext Y.IsSheaf fun x hx => ?_
  obtain ⟨U, hU, hxU, hUW⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (show x ∈ W from hx)
  replace hU : IsAffineOpen U := hU
  refine ⟨U, hUW, hxU, ?_⟩
  have hc : (algX p U).FiniteType := by
    have h1 : (p.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  let : Algebra ℂ Γ(Y, U) := (algX p U).toAlgebra
  have : Algebra.FiniteType ℂ Γ(Y, U) := hc
  change resG Y hUW a = resG Y hUW b
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_algHom_complex _ fun e => ?_
  have hm := ofHom_mem (p := p) (σ := RingHom.id ℂ) hU e.toRingHom (fun c => e.commutes c)
  have h := hab _ (ptsIn_mono hUW hm)
  rw [← ev_res hUW hm, ← ev_res hUW hm, ev_ofHom, ev_ofHom] at h
  rw [map_sub, sub_eq_zero]
  exact h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineBoundaryFunctionsOfIsProjOver
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open ProjSpace

theorem IsAmpleLB.exists_affine_boundary_functions {Y : Scheme.{0}} {L : LB Y} (h : IsAmpleLB L) (U : Y.Opens)
    (x : Y) (hx : x ∈ U) : ∃ (V : Y.Opens) (n : ℕ) (u : Fin n → Γ(Y, V)), x ∈ V ∧ V ≤ U ∧ IsAffineOpen V ∧
      ∀ z : Y, ∃ (Q : Y.Opens) (η : Γ(Y, Q)) (l : Fin n), z ∈ Q ∧ Y.basicOpen η = Q ⊓ V ∧
        resG Y (inf_le_right : Q ⊓ V ≤ V) (u l) * resG Y (inf_le_left : Q ⊓ V ≤ Q) η = 1 := by
  obtain ⟨k, hk, hg⟩ := h.exists_isGenerated_pow
  obtain ⟨d, -, t, hxt, hle, ha⟩ := ((isAmpleLB_pow_iff h.isLB hk).2 h).exists_affine_le hx
  obtain ⟨n, s, hs⟩ := hg.pow d
  refine ⟨nonzeroLocus t, n, fun l => secRatio t (s l), hxt, hle, ha, fun z => ?_⟩
  obtain ⟨l, hl⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ z))
  refine ⟨nonzeroLocus (s l), secRatio (s l) t, l, hl, basicOpen_secRatio _ _, ?_⟩
  rw [secRatio_mul_secRatio t (s l) t inf_le_right inf_le_left, secRatio_self, map_one]

theorem exists_affine_boundary_functions_of_isProjOver :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsProjOver p → ∀ (U : Y.Opens) (x : Y), x ∈ U →
      ∃ (V : Y.Opens) (n : ℕ) (u : Fin n → Γ(Y, V)), x ∈ V ∧ V ≤ U ∧ IsAffineOpen V ∧
        ∀ z : Y, ∃ (Q : Y.Opens) (η : Γ(Y, Q)) (l : Fin n), z ∈ Q ∧ Y.basicOpen η = Q ⊓ V ∧
          resG Y (inf_le_right : Q ⊓ V ≤ V) (u l) * resG Y (inf_le_left : Q ⊓ V ≤ Q) η = 1 := by
  rintro Y p ⟨N, i, hi, -⟩ U x hx
  exact ((isAmple_projective_O_one ℂ N).pull_of_isAffineHom i).exists_affine_boundary_functions U x hx

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenIsDomainOfSmoothComplex
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory

theorem exists_open_isDomain_of_smooth_complex :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → ∀ x : Y,
      ∃ U : Y.Opens, x ∈ U ∧ ∀ V : Y.Opens, V ≤ U → x ∈ V → IsDomain Γ(Y, V) := by
  intro Y p D hp x
  have hs : Smooth p := SmoothOfRelativeDimension.smooth D p
  obtain ⟨-, hn, hl⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ Y p hs
  have := IsNormalScheme.of_pred (fun y => ⟨hn.1 y, hn.2 y⟩)
  obtain ⟨U, hx, hU⟩ := GlobalTheory.ModelChart.exists_open_isDomain Y x
  exact ⟨U, hx, fun V hV hxV => hU V hxV hV⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEqOfPolynomialGrowth
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.CxPts

namespace GlobalTheory.SerreSections

theorem exists_ringHom_of_denominator {P A : Type*} [CommRing P] [CommRing A] (α : P →+* A) (e : P →+* ℂ) (q : P)
    (hq : e q ≠ 0) (hk : ∀ s, α s = 0 → e s = 0) (r : A → P) (hr : ∀ b, α q * b = α (r b)) :
    ∃ χ : A →+* ℂ, (∀ b, χ b = e (r b) / e q) ∧ ∀ s, χ (α s) = e s := by
  have hk' (s s' : P) (h : α s = α s') : e s = e s' :=
    sub_eq_zero.1 ((map_sub e s s').symm.trans (hk _ (by rw [map_sub, h, sub_self])))
  have h1 (s : P) : e (r (α s)) / e q = e s := by
    rw [div_eq_iff hq, ← map_mul]
    exact hk' _ _ (by rw [← hr, map_mul, mul_comm])
  refine ⟨{ toFun := fun b => e (r b) / e q, map_one' := ?_, map_mul' := fun a b => ?_,
            map_zero' := ?_, map_add' := fun a b => ?_ }, fun _ => rfl, h1⟩
  · simpa using h1 1
  · have := hk' (q * r (a * b)) (r a * r b) (by simp only [map_mul, ← hr]; ring)
    simp only [map_mul] at this
    field_simp
    linear_combination this
  · simpa using h1 0
  · rw [← add_div, ← map_add (f := _)]
    congr 1
    exact hk' _ _ (by simp only [map_add (f := _), ← hr]; ring)

section Along

variable {Y : Scheme.{0}} {p : Y ⟶ Sp ℂ} {σ : ℂ →+* ℂ} {D : ℕ} {E : Type} [NormedAddCommGroup E]
  [NormedSpace ℂ E] {U : Y.Opens} {Z : Set E} {z : E} {s : E → CxPts p σ}

theorem exists_analyticAt_ev (hU : IsAffineOpen U) (hz : z ∈ Z) (hs : ∀ w ∈ Z, s w ∈ ptsIn p σ U)
    (hc : ContinuousWithinAt s Z z)
    (hd : ∀ a : Γ(Y, U), ∃ F : E → ℂ, AnalyticAt ℂ F z ∧ ∀ w ∈ Z, ev p σ U a (s w) = F w)
    {W : Y.Opens} (hW : s z ∈ ptsIn p σ W) (f : Γ(Y, W)) :
    ∃ F : E → ℂ, AnalyticAt ℂ F z ∧ ∀ᶠ w in 𝓝[Z] z, ev p σ W f (s w) = F w := by
  obtain ⟨h, hhW, hh⟩ := hU.exists_basicOpen_le (V := W) ⟨_, mem_ptsIn.1 hW⟩ (mem_ptsIn.1 (hs z hz))
  have hB : s z ∈ ptsIn p σ (Y.basicOpen h) := mem_ptsIn.2 hh
  have := hU.isLocalization_basicOpen h
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h (resG Y hhW f)
  obtain ⟨Fa, hFa, ea⟩ := hd a
  obtain ⟨Fh, hFh, eh⟩ := hd h
  refine ⟨fun w => Fa w * (Fh w ^ n)⁻¹, hFa.mul ((hFh.pow n).inv (pow_ne_zero n
    (eh z hz ▸ (mem_ptsIn_basicOpen (hs z hz) h).1 hB))), ?_⟩
  filter_upwards [hc.preimage_mem_nhdsWithin ((isOpen_ptsIn _).mem_nhds hB), self_mem_nhdsWithin] with w hw hwZ
  have ha' : resG Y hhW f * resG Y (Y.basicOpen_le h) h ^ n = resG Y (Y.basicOpen_le h) a := ha
  have e := congrArg (evHom hw) ha'
  rw [map_mul, map_pow, ← ev_eq, ← ev_eq, ← ev_eq, ev_res _ hw, ev_res _ hw, ev_res _ hw] at e
  rw [← ea w hwZ, ← eh w hwZ]
  exact (eq_mul_inv_iff_mul_eq₀
    (pow_ne_zero n ((mem_ptsIn_basicOpen (ptsIn_mono (Y.basicOpen_le h) hw) h).1 hw))).2 e

theorem exists_analyticAt_holo (R : AnRead p σ D) (hU : IsAffineOpen U) (hz : z ∈ Z)
    (hs : ∀ w ∈ Z, s w ∈ ptsIn p σ U)
    (hd : ∀ a : Γ(Y, U), ∃ F : E → ℂ, AnalyticAt ℂ F z ∧ ∀ w ∈ Z, ev p σ U a (s w) = F w)
    {φ : CxPts p σ → ℂ} (hφ : R.HoloOn (ptsIn p σ U) φ) :
    ∃ F : E → ℂ, AnalyticAt ℂ F z ∧ ∀ᶠ w in 𝓝[Z] z, φ (s w) = F w := by
  have hc : ContinuousWithinAt s Z z := tendsto_subtype_rng.2
    (Points.tendsto_of_isAffineOpen hU (hs z hz) (eventually_of_mem self_mem_nhdsWithin hs) fun a => by
      obtain ⟨F, hF, e⟩ := hd a
      exact hF.continuousAt.continuousWithinAt.congr e (e z hz))
  obtain ⟨i, hi⟩ := R.cover (s z)
  set c := R.chart i
  choose F hF e using fun a => exists_analyticAt_ev hU hz hs hc hd (c.source_subset hi) (c.x a)
  let X : E → ReciprocityTheory.L2DbarEstimates.V D := fun w => (EuclideanSpace.equiv (Fin D) ℂ).symm fun a => F a w
  have hX : AnalyticAt ℂ X z :=
    ((EuclideanSpace.equiv (Fin D) ℂ).symm.analyticAt _).comp (analyticAt_pi_iff.2 hF)
  have hev : ∀ᶠ w in 𝓝[Z] z, s w ∈ c.e.source ∧ X w = c.e (s w) := by
    filter_upwards [eventually_all.2 e, hc.preimage_mem_nhdsWithin (c.e.open_source.mem_nhds hi)] with w h₁ h₂
    refine ⟨h₂, ?_⟩
    ext a
    exact (h₁ a).symm.trans (c.apply_eq _ h₂ a).symm
  have hG : AnalyticAt ℂ (φ ∘ c.e.symm) (X z) := by
    rw [(hev.self_of_nhdsWithin hz).2]
    exact SCV.analyticAt_of_differentiableOn (hφ i)
      ((ChartGlue.isOpen_over _ (isOpen_ptsIn U)).mem_nhds (ChartGlue.mem_over _ hi (hs z hz)))
  refine ⟨(φ ∘ c.e.symm) ∘ X, hG.comp hX, hev.mono fun w hw => ?_⟩
  simp only [Function.comp_apply, hw.2, c.e.left_inv hw.1]

end Along

theorem analyticAt_eval_map {d : ℕ} (r : Polynomial (MvPolynomial (Fin d) ℂ)) (z : (Fin d → ℂ) × ℂ) :
    AnalyticAt ℂ (fun w : (Fin d → ℂ) × ℂ => (r.map (MvPolynomial.eval w.1)).eval w.2) z :=
  SCV.analyticOnNhd_of_differentiable ((FiniteCoverGrowth.contDiff_eval_map r).differentiable one_ne_zero)
    univ z trivial

theorem exists_sum_norm_le {A : Type*} [CommRing A] {d n : ℕ} (j : MvPolynomial (Fin d) ℂ →+* A)
    (hj : j.IsIntegral) (u : Fin n → A) : ∃ (K : ℝ) (M : ℕ), ∀ (x : Fin d → ℂ) (χ : A →+* ℂ),
      χ.comp j = MvPolynomial.eval x → 1 + ∑ l, ‖χ (u l)‖ ≤ K * (1 + ‖x‖) ^ M := by
  choose s hs hs' using fun l => hj (u l)
  choose K M hK h using fun l => FiniteCoverGrowth.exists_norm_root_le (s l) (hs l)
  refine ⟨1 + ∑ l, K l, ∑ l, M l, fun x χ hχ => ?_⟩
  have h0 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  rw [add_mul, one_mul, Finset.sum_mul]
  refine add_le_add (one_le_pow₀ h0) (Finset.sum_le_sum fun l _ => (h l x _ ?_).trans ?_)
  · rw [Polynomial.eval_map, ← hχ, ← Polynomial.hom_eval₂, hs', map_zero]
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h0
      (Finset.single_le_sum (f := M) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l))) (hK l)

theorem exists_mul_eq_of_polynomial_growth : ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → ∀ (R : AnRead p (RingHom.id ℂ) D) (V : Y.Opens), IsAffineOpen V → IsDomain Γ(Y, V) → ∀ φ : CxPts p (RingHom.id ℂ) → ℂ, R.HoloOn (ptsIn p (RingHom.id ℂ) V) φ → ∀ (n : ℕ) (u : Fin n → Γ(Y, V)) (C : ℝ) (m : ℕ), (∀ y ∈ ptsIn p (RingHom.id ℂ) V, ‖φ y‖ ≤ C * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m) → ∃ a b : Γ(Y, V), b ≠ 0 ∧ ∀ y ∈ ptsIn p (RingHom.id ℂ) V, ev p (RingHom.id ℂ) V b y * φ y = ev p (RingHom.id ℂ) V a y := by
  intro Y p D hs R V hV hd φ hφ n u C m hb
  classical
  have hsm : Smooth p := SmoothOfRelativeDimension.smooth D p
  have hc : (algX p V).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _).comp
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  letI : Algebra ℂ Γ(Y, V) := (algX p V).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(Y, V) := hc
  obtain ⟨d, j, a, P, q, -, hinj, hfin, hP, -, hdvd, hq, hqP, hr⟩ := noetherNormalization_primitive Γ(Y, V)
  choose r hr using hr
  let α := Polynomial.eval₂RingHom j.toRingHom a
  let e (z : (Fin d → ℂ) × ℂ) := Polynomial.eval₂RingHom (MvPolynomial.eval z.1) z.2
  have he (z) (s) : e z s = (s.map (MvPolynomial.eval z.1)).eval z.2 := (Polynomial.eval_map _ _).symm
  have hα (f) : α (Polynomial.C f) = j f := Polynomial.eval₂_C _ _
  have heC (z) (f) : e z (Polynomial.C f) = MvPolynomial.eval z.1 f := Polynomial.eval₂_C _ _
  set Z : Set ((Fin d → ℂ) × ℂ) := {z | MvPolynomial.eval z.1 q ≠ 0 ∧
    (P.map (MvPolynomial.eval z.1)).eval z.2 = 0}
  have hχ (z) (hz : z ∈ Z) := exists_ringHom_of_denominator α (e z) (Polynomial.C q) (heC z q ▸ hz.1)
    (fun s h => by
      obtain ⟨t, rfl⟩ := (hdvd s).1 h
      rw [map_mul, he, hz.2, zero_mul]) r fun b => by rw [hα]; exact hr b
  choose χ hχ hχ' using hχ
  have hχj (z) (hz : z ∈ Z) (f) : χ z hz (j f) = MvPolynomial.eval z.1 f := by rw [← hα, hχ', heC]
  have hχc (z) (hz : z ∈ Z) (c : ℂ) : χ z hz (algX p V c) = RingHom.id ℂ c :=
    (congrArg _ (j.commutes c).symm).trans ((hχj z hz _).trans (MvPolynomial.eval_C _))
  have hb0 : j q * α P.derivative ≠ 0 := by
    have h0 : j q ≠ 0 := (map_ne_zero_iff _ hinj).2 hq
    refine mul_ne_zero h0 fun h => h0 ?_
    obtain ⟨v, w, hvw⟩ := Ideal.mem_span_pair.1 hqP
    rw [← hα, ← hvw, map_add (f := _), map_mul, map_mul, h, show α P = 0 from (hdvd P).2 dvd_rfl]
    simp
  rcases (ptsIn p (RingHom.id ℂ) V).eq_empty_or_nonempty with hE | ⟨y₀, -⟩
  · exact ⟨0, 1, one_ne_zero, by simp [hE]⟩
  let s (z : (Fin d → ℂ) × ℂ) : CxPts p (RingHom.id ℂ) :=
    if hz : z ∈ Z then ofHom hV (χ z hz) (hχc z hz) else y₀
  have hsV (z) (hz : z ∈ Z) : s z ∈ ptsIn p (RingHom.id ℂ) V := by
    simp only [s, dif_pos hz]; exact ofHom_mem _ _ _
  have hsv (z) (hz : z ∈ Z) (b) : ev p (RingHom.id ℂ) V b (s z) = χ z hz b := by
    simp only [s, dif_pos hz]; exact ev_ofHom _ _ _ b
  obtain ⟨K, M, hK⟩ := exists_sum_norm_le j.toRingHom hfin.to_isIntegral u
  obtain ⟨-, t, ht⟩ := FiniteCoverGrowth.integral_and_rational_of_polynomial_growth
    isConnected_and_dense_compl_hypersurface exists_mvPolynomial_of_poly_bound_off_hypersurface
    d (M * m) P q (fun z => φ (s z)) (|C| * K ^ m) hP hq hqP
    (fun z hz => exists_analyticAt_holo R hV hz hsV (fun b => ⟨fun w => e w (r b) / e w (Polynomial.C q), by
      simp only [he]
      exact (analyticAt_eval_map _ z).div (analyticAt_eval_map _ z) (by rw [← he, heC]; exact hz.1),
      fun w hw => (hsv w hw b).trans (hχ w hw b)⟩) hφ)
    fun z hz => by
      refine (hb _ (hsV z hz)).trans ?_
      simp only [hsv z hz]
      rw [mul_assoc, pow_mul, ← mul_pow]
      exact mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by positivity)
        (hK z.1 _ (RingHom.ext (hχj z hz))) m) (by positivity) (abs_nonneg C)
  refine ⟨j q * α t, j q * α P.derivative, hb0, fun y hy => ?_⟩
  simp only [ev_eq hy, map_mul]
  by_cases h0 : evHom hy (j q) = 0
  · simp [h0]
  let z : (Fin d → ℂ) × ℂ := (fun k => evHom hy (j (MvPolynomial.X k)), evHom hy a)
  have hj : (evHom hy).comp j.toRingHom = MvPolynomial.eval z.1 :=
    MvPolynomial.ringHom_ext (fun c => by
      rw [MvPolynomial.eval_C]
      exact (congrArg _ (j.commutes c)).trans ((ev_eq hy _).symm.trans (ev_algX hy c))) fun k => by simp [z]
  have hez (f) : evHom hy (α f) = e z f := by
    change _ = Polynomial.eval₂ _ _ _
    rw [← hj]
    exact Polynomial.hom_eval₂ _ _ _ _
  have hz : z ∈ Z := ⟨by rwa [← heC, ← hez, hα], by
    rw [← he, ← hez, show α P = 0 from (hdvd P).2 dvd_rfl, map_zero]⟩
  have hsz : s z = y := Subtype.ext (Points.ext_of_valR hV (hsV z hz) hy fun b => by
    refine (hsv z hz b).trans (Eq.trans ?_ (ev_eq hy b).symm)
    rw [hχ, ← hez, ← hez, hα, div_eq_iff h0, ← map_mul, mul_comm, hr]
    rfl)
  rw [mul_assoc, hez, hez, he, he, ← ht z hz, hsz]

end GlobalTheory.SerreSections
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqOfContinuousQuotientAlgHom
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory


open AffinePoints in
theorem exists_eq_of_continuous_quotient_algHom {A : Type} [CommRing A] [IsDomain A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] [IsIntegrallyClosed A] {ψ : (A →ₐ[ℂ] ℂ) → ℂ} (hψ : Continuous ψ)
    {a b : A} (hb : b ≠ 0) (hab : ∀ e : A →ₐ[ℂ] ℂ, e b * ψ e = e a) :
    ∃ c : A, ∀ e : A →ₐ[ℂ] ℂ, e c = ψ e := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have key (s r : A) (h : b * s = a * r) (e : A →ₐ[ℂ] ℂ) : e s = ψ e * e r := by
    refine congrFun (Continuous.ext_on (dense_nonvanishing hb) (continuous_eval s)
      (hψ.mul (continuous_eval r)) fun w hw => mul_left_cancel₀ hw ?_) e
    have h1 := congrArg w h
    rw [map_mul, map_mul, ← hab w] at h1
    exact h1.trans (_root_.mul_assoc _ _ _)
  by_cases H : b ∣ a
  · obtain ⟨c, hc⟩ := H
    exact ⟨c, fun e => by rw [key c 1 (by rw [hc, _root_.mul_one]) e, map_one, _root_.mul_one]⟩
  obtain ⟨p, hp, s, r, hs, hr, h⟩ := ContinuousQuotient.exists_prime_of_not_dvd hb H
  have h0 : Ideal.Quotient.mkₐ ℂ p s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨e, he⟩ := not_forall.mp fun h => h0 (eq_zero_of_forall_algHom_complex _ h)
  refine (he ((key s r h (e.comp (Ideal.Quotient.mkₐ ℂ p))).trans ?_)).elim
  change _ * e (Ideal.Quotient.mk p r) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero, mul_zero]

theorem isIntegrallyClosed_sections_of_isDomain {Y : Scheme.{0}}
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) {U : Y.Opens} (hU : IsAffineOpen U)
    [IsDomain Γ(Y, U)] : IsIntegrallyClosed Γ(Y, U) := by
  refine IsIntegrallyClosed.of_localization_maximal fun p _ hp ↦ ?_
  let P : Spec Γ(Y, U) := ⟨p, hp.isPrime⟩
  have hy : hU.fromSpec P ∈ U := hU.range_fromSpec.le ⟨P, rfl⟩
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk (hU.fromSpec P)) :=
    Y.presheaf.algebra_section_stalk (U := U) ⟨_, hy⟩
  have h : IsLocalization p.primeCompl (Y.presheaf.stalk (hU.fromSpec P)) :=
    hU.isLocalization_stalk' P hy
  have := hY (hU.fromSpec P)
  exact IsIntegrallyClosed.of_equiv (R := Y.presheaf.stalk (hU.fromSpec P))
    (IsLocalization.algEquiv p.primeCompl (Y.presheaf.stalk (hU.fromSpec P))
      (Localization.AtPrime p)).toRingEquiv


open AffinePoints in
theorem exists_ev_eq_of_continuousOn_quotient :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → ∀ (V : Y.Opens), IsAffineOpen V → IsDomain Γ(Y, V) → ∀ φ : CxPts p (RingHom.id ℂ) → ℂ, ContinuousOn φ (ptsIn p (RingHom.id ℂ) V) → ∀ a b : Γ(Y, V), b ≠ 0 → (∀ y ∈ ptsIn p (RingHom.id ℂ) V, ev p (RingHom.id ℂ) V b y * φ y = ev p (RingHom.id ℂ) V a y) → ∃ c : Γ(Y, V), ∀ y ∈ ptsIn p (RingHom.id ℂ) V, ev p (RingHom.id ℂ) V c y = φ y := by
  intro Y p D hp U hU hdom φ hφ a b hb hab
  have hsm : Smooth p := SmoothOfRelativeDimension.smooth D p
  have hN := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ Y p hsm).2.1
  have := isIntegrallyClosed_sections_of_isDomain hN.2 hU
  have hc : (algX p U).FiniteType := by
    have h1 : (p.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  let : Algebra ℂ Γ(Y, U) := (algX p U).toAlgebra
  have : Algebra.FiniteType ℂ Γ(Y, U) := hc
  let s (e : Γ(Y, U) →ₐ[ℂ] ℂ) : CxPts p (RingHom.id ℂ) := ofHom hU e.toRingHom fun c => e.commutes c
  have hm (e) : s e ∈ ptsIn p (RingHom.id ℂ) U := ofHom_mem _ _ _
  have hv (e) (f) : ev p (RingHom.id ℂ) U f (s e) = e f := ev_ofHom _ _ _ _
  have hs : Continuous s := continuous_iff_continuousAt.2 fun e => tendsto_subtype_rng.2
    (Points.tendsto_of_isAffineOpen hU (hm e) (Filter.Eventually.of_forall hm) fun f => by
      have h : Continuous fun w => ev p (RingHom.id ℂ) U f (s w) := by
        simp only [hv]; exact continuous_eval f
      exact h.continuousAt)
  obtain ⟨c, hc⟩ := exists_eq_of_continuous_quotient_algHom (hφ.comp_continuous hs hm) (a := a) hb
    fun e => by rw [← hv, ← hv]; exact hab _ (hm e)
  refine ⟨c, fun y hy => ?_⟩
  let e : Γ(Y, U) →ₐ[ℂ] ℂ :=
    { evHom hy with commutes' := fun t => (ev_eq hy _).symm.trans (ev_algX hy t) }
  have he : s e = y := Subtype.ext (Points.ext_of_valR hU (hm e) hy fun f =>
    (hv e f).trans (ev_eq hy f).symm)
  rw [← he, hv]
  exact hc e

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

theorem GlobalTheory.Published.serreHolomorphicSections_holds : GlobalTheory.Published.SerreHolomorphicSections := by
  intro Y p D hs hp R B hB
  refine ⟨fun s t h => ?_, fun s => ?_⟩
  · have e : s.f = t.f := funext fun i => GlobalTheory.eq_of_ev_eq_of_smoothOfRelativeDimension Y p D hs _ _ _ fun y _ =>
      congrFun₂ (congrArg Subtype.val h) i y
    cases s; cases t; congr
  have loc (i : B.ι) (x : B.U i) : ∃ V : Y.Opens, x.1 ∈ V ∧ V ≤ B.U i ∧ ∃ c : Γ(Y, V),
      ∀ y ∈ ptsIn p (RingHom.id ℂ) V, ev p (RingHom.id ℂ) V c y = s.1 i y := by
    obtain ⟨U, hxU, hU⟩ := GlobalTheory.exists_open_isDomain_of_smooth_complex Y p D hs x
    obtain ⟨V, n, u, hx, hV, ha, h⟩ := GlobalTheory.exists_affine_boundary_functions_of_isProjOver Y p hp (U ⊓ B.U i) x ⟨hxU, x.2⟩
    have hi := hV.trans inf_le_right
    have hd := hU V (hV.trans inf_le_left) hx
    have hh := (s.2.2 i).mono (ptsIn_mono hi)
    obtain ⟨C, m, hC⟩ := GlobalTheory.continuous_section_polynomial_growth Y p hp B hB s.1 s.2.1
      (fun j => (s.2.2 j).continuousOn (isOpen_ptsIn _)) i V n u hi h
    obtain ⟨a, b, hb, e⟩ := SerreSections.exists_mul_eq_of_polynomial_growth Y p D hs R V ha hd _ hh n u C m hC
    exact ⟨V, hx, hi, GlobalTheory.exists_ev_eq_of_continuousOn_quotient Y p D hs V ha hd _ (hh.continuousOn (isOpen_ptsIn _)) a b hb e⟩
  choose V hx hV c hc using loc
  have glue (i : B.ι) : ∃ f : Γ(Y, B.U i), ∀ y ∈ ptsIn p (RingHom.id ℂ) (B.U i),
      ev p (RingHom.id ℂ) _ f y = s.1 i y := by
    obtain ⟨f, hf, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf (V i) (B.U i)
      (fun x => homOfLE (hV i x)) (fun x h => Opens.mem_iSup.2 ⟨⟨x, h⟩, hx i _⟩) (c i) fun x x' =>
        GlobalTheory.eq_of_ev_eq_of_smoothOfRelativeDimension Y p D hs (V i x ⊓ V i x') _ _ fun y hy =>
          ((ev_res inf_le_left hy _).trans (hc i x y (mem_ptsIn_inf.1 hy).1)).trans
            ((ev_res inf_le_right hy _).trans (hc i x' y (mem_ptsIn_inf.1 hy).2)).symm
    refine ⟨f, fun y hy => ?_⟩
    have hy' : y ∈ ptsIn p (RingHom.id ℂ) (V i ⟨_, mem_ptsIn.1 hy⟩) := mem_ptsIn.2 (hx i _)
    rw [← hc i _ y hy', ← hf]
    exact (ev_res _ hy' _).symm
  choose f hf using glue
  refine ⟨⟨f, fun i j => GlobalTheory.eq_of_ev_eq_of_smoothOfRelativeDimension Y p D hs _ _ _ fun y hy => ?_⟩, Subtype.ext (funext₂ fun i y => ?_)⟩
  · have h := mem_ptsIn_inf.1 hy
    refine (ev_res inf_le_left hy _).trans (Eq.trans ?_ (ev_mul _ _ _).symm)
    rw [hf i y h.1, s.2.1.1 i j y h.1 h.2, ← hf j y h.2]
    exact congrArg _ (ev_res inf_le_right hy _).symm
  · by_cases h : y ∈ ptsIn p (RingHom.id ℂ) (B.U i)
    · exact hf i y h
    · exact (ev_of_notMem h _).trans (s.2.1.2 i y h).symm

theorem GlobalTheory.AnRead.bijective_valC {F : Type} [Field F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {σ : F →+* ℂ} {D : ℕ}
    [SmoothOfRelativeDimension D p] (hp : IsProjOver p) (R : AnRead p σ D) {B : LB Y} (hB : B.IsLB) :
    Function.Bijective (R.valC B) :=
  GlobalTheory.Published.serreHolomorphicSections_holds.bijective_valC hp R hB

module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeExpOfLogLe
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IndepSpanRankTransferLargeFieldComplex
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DivisionOrderOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShareRhoROfAnFacts
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem finite_sum_le (D a : ℕ) : {α : Fin D → ℕ | ∑ i, α i ≤ a}.Finite := by
  refine (Set.Finite.pi' (fun _ : Fin D => Set.finite_Iic a)).subset ?_
  intro α hα i
  exact (Finset.single_le_sum (f := α) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hα

theorem graded_prod_pow_mul {A ι : Type} [CommRing A] (Q : ℕ → A → Prop) (s : ι → A)
    (h : ∀ n i x, Q n x → Q (n + 1) (s i * x)) (α : ι → ℕ) (F : Finset ι) (n : ℕ) (x : A) (hx : Q n x) :
    Q (n + ∑ i ∈ F, α i) ((∏ i ∈ F, s i ^ α i) * x) := by
  classical
  have hp : ∀ i m n x, Q n x → Q (n + m) (s i ^ m * x) := by
    intro i m
    induction m with
    | zero => intro n x hx; simpa using hx
    | succ m ih => intro n x hx; rw [pow_succ', mul_assoc, ← add_assoc]; exact h _ _ _ (ih n x hx)
  induction F using Finset.induction_on with
  | empty => simpa using hx
  | insert i F hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, mul_assoc, add_comm (α i), ← add_assoc]
    exact hp _ _ _ _ ih

theorem addL_zero' {D : D7} {j : ℕ} (u wL : WeightFamilies.Wt D j) : addL u wL 0 = u := by
  cases u
  unfold addL wadd wsmul
  simp

theorem shareRhoR_of_anFacts : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData X ka wL wF) (R : Rdg X) (t : Idx D j G.N → ℂ) (T : ℕ) (Mg : Submodule B.KO (B.Cusp j ka)) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t → AnFacts R G.w t ka wF T Mg xs → addL wF wL T = ka → 2 ≤ WeightFamilies.dimY D j → 11 * WeightFamilies.dimY D j ^ 2 ≤ T → LatAt B j ka → ∀ S : Scal B, ShareRhoR G S T (X.rk ka (B.Mlat j ka)) := by
  intro D B P j X ka wL wF G R t T Mg δ xs hgen hA hka hD hT hLat S la
  classical
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la G.N wL G.w t
  have hDT : WeightFamilies.dimY D j < T := by nlinarith
  obtain ⟨b1, b2⟩ := GlobalTheory.T.card_exponents_and_choose_ratio_bounds_pair (WeightFamilies.dimY D j) T
  obtain ⟨θ, -, hθ⟩ := GlobalTheory.T.exists_valueBasis_in_spanning_forms D B P j X ka wL wF G.N G.w R t T Mg δ xs hA Set.univ Submodule.span_univ

  have hd : X.rk ka (B.Mlat j ka) = Module.finrank ℂ (R.sp ka Set.univ) := by
    have h1 := (d8 ka ⊤).2
    rw [Submodule.top_coe] at h1
    rw [h1]
    unfold PJ.rk
    have : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤ := Submodule.IsFullLattice.span_eq_top (self := hLat)
    rw [this]
  haveI hfin : FiniteDimensional ℂ (R.sp ka Set.univ) := by
    have h1 := (d8 ka ⊤).1
    rwa [Submodule.top_coe] at h1

  set a := a0 D j T with ha
  have haD : WeightFamilies.dimY D j + a = T := by rw [ha]; unfold a0; omega
  let p1 : Fin (WeightFamilies.dimY D j + 1) → MvPolynomial (Idx D j G.N) X.Forms := fun i =>
    ∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (G.w k))
  let pm : (Fin (WeightFamilies.dimY D j) → ℕ) → MvPolynomial (Idx D j G.N) X.Forms := fun α => ∏ i, p1 i.succ ^ α i
  have pmK : ∀ α, toRp X la G.N (pm α) = Formalism.MainNotions.Gaps.EtaleWeightGaps.secPow X la G.w α := by
    intro α
    simp only [pm, map_prod, map_pow, Formalism.MainNotions.Gaps.EtaleWeightGaps.secPow]
    exact Finset.prod_congr rfl fun i _ => by rw [(d1 i.succ).1]
  have pmC : ∀ α, R.toFn t (pm α) = R.mon G.w t α := by
    intro α
    simp only [pm, map_prod, map_pow, Rdg.mon]
    exact Finset.prod_congr rfl fun i _ => by rw [(d1 i.succ).2.1]
  have hstep : ∀ n i x, OfWt X (addL wF wL n) x → OfWt X (addL wF wL (n + 1)) (p1 i * x) := by
    intro n i x hx
    rw [← wadd_addL]
    exact d4 _ _ _ _ (d1 i).2.2 hx
  have hpm : ∀ α n x, OfWt X (addL wF wL n) x → OfWt X (addL wF wL (n + ∑ i, α i)) (pm α * x) := fun α n x hx =>
    graded_prod_pow_mul (fun n x => OfWt X (addL wF wL n) x) (fun i : Fin (WeightFamilies.dimY D j) => p1 i.succ)
      (fun n i x hx => hstep n i.succ x hx) α Finset.univ n x hx
  have hp0 : ∀ m n x, OfWt X (addL wF wL n) x → OfWt X (addL wF wL (n + m)) (p1 0 ^ m * x) := fun m n x hx => by
    simpa using graded_prod_pow_mul (fun n x => OfWt X (addL wF wL n) x) (fun _ : Unit => p1 0)
      (fun n _ x hx => hstep n 0 x hx) (fun _ => m) Finset.univ n x hx
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := B.KO) (M := B.Cusp j (X.wF0 wL wF))
  haveI : Finite {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i = a} :=
    ((finite_sum_le (WeightFamilies.dimY D j) a).subset (t := {α | ∑ i, α i = a}) fun α (h : ∑ i, α i = a) => h.le).to_subtype
  haveI : Finite {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a} :=
    ((finite_sum_le (WeightFamilies.dimY D j) a).subset (t := {α | ∑ i, α i < a}) fun α (h : ∑ i, α i < a) => h.le).to_subtype
  letI := Fintype.ofFinite {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i = a}
  letI := Fintype.ofFinite {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a}
  let q : {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i = a} × Fin n → MvPolynomial (Idx D j G.N) X.Forms := fun p =>
    pm p.1.1 * MvPolynomial.C (X.inc (X.wF0 wL wF) (b p.2))
  have hq : ∀ p, OfWt X ka (q p) := by
    intro p
    have := hpm p.1.1 (WeightFamilies.dimY D j) _ (d3 (X.wF0 wL wF) (b p.2))
    rwa [p.1.2, haD, hka] at this
  have htr := (GlobalTheory.T.indep_span_rank_transfer_largeField_complex D B P j X R la G.N t hgen ka _ q hq).2.2

  have hK : Submodule.span (Kp X la G.N) (zAll G la S T) ≤
      Submodule.span (Kp X la G.N) (Set.range fun p => toRp X la G.N (q p)) := by
    rw [Submodule.span_le]
    rintro _ ⟨α, F, hα, -, rfl⟩
    have hF := emb_mem_Vw X la G.N _ F
    rw [Vw_eq_span_image X la G.N _ hb] at hF
    have := Submodule.mem_map_of_mem (f := LinearMap.mulLeft (Kp X la G.N) (Formalism.MainNotions.Gaps.EtaleWeightGaps.secPow X la G.w α)) hF
    rw [Submodule.map_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨_, ⟨k, rfl⟩, rfl⟩, rfl⟩
    refine ⟨(⟨α, hα⟩, k), ?_⟩
    simp only [q, map_mul, pmK, (d2 _).1, LinearMap.mulLeft_apply]

  have hC : Submodule.span ℂ (Set.range fun p => R.toFn t (q p)) ≤ R.deep G.w t (X.wF0 wL wF) a := by
    refine Submodule.span_mono ?_
    rintro _ ⟨p, rfl⟩
    refine ⟨p.1.1, R.ev (X.inc _ (b p.2)), p.1.2, Submodule.subset_span ⟨b p.2, trivial, rfl⟩, ?_⟩
    simp only [q, map_mul, pmC, (d2 _).2]
  have hCk : Submodule.span ℂ (Set.range fun p => R.toFn t (q p)) ≤ R.sp ka Set.univ := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact (d5 ka _ (hq p)).2
  obtain ⟨hli, hdis⟩ := hA.indep δ (fun i => R.ev (X.inc wF (θ i)))
    (fun i => Submodule.subset_span ⟨θ i, trivial, rfl⟩) hθ
  rw [← ha] at hli hdis
  have hLk : Submodule.span ℂ (Set.range (R.lead G.w t T a fun i => R.ev (X.inc wF (θ i)))) ≤ R.sp ka Set.univ := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    have h0 : OfWt X (addL wF wL 0) (MvPolynomial.C (X.inc wF (θ p.2)) : MvPolynomial (Idx D j G.N) X.Forms) := by
      rw [addL_zero']; exact d3 _ _
    have h1 := hpm p.1.1 _ _ (hp0 (T - ∑ i, p.1.1 i) _ _ h0)
    have h2 := p.1.2
    rw [show 0 + (T - ∑ i, p.1.1 i) + ∑ i, p.1.1 i = T by omega, hka] at h1
    have h3 := (d5 ka _ h1).2
    rw [map_mul, map_mul, map_pow, pmC, (d1 0).2.1, (d2 _).2, ← mul_assoc] at h3
    exact h3
  have hrk := finrank_span_eq_card hli
  rw [Fintype.card_prod, Fintype.card_fin, ← Nat.card_eq_fintype_card] at hrk
  have hcard : Nat.card {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a} = (T - 1).choose (WeightFamilies.dimY D j) :=
    b1 (by omega) hDT
  rw [hcard] at hrk
  haveI := Submodule.finiteDimensional_of_le hLk
  haveI := Submodule.finiteDimensional_of_le hCk
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℂ (Set.range (R.lead G.w t T a fun i => R.ev (X.inc wF (θ i)))))
    (Submodule.span ℂ (Set.range fun p => R.toFn t (q p)))
  rw [(hdis.mono_right hC).eq_bot, finrank_bot, add_zero, hrk] at hsum
  have hle := Submodule.finrank_mono (sup_le hLk hCk)
  haveI : FiniteDimensional (Kp X la G.N)
      (Submodule.span (Kp X la G.N) (Set.range fun p => toRp X la G.N (q p))) :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hKle := Submodule.finrank_mono hK
  rw [hd]
  refine (b2 δ _ _ hD hT hA.upper).1 ?_
  rw [mul_comm δ]
  omega

end GlobalTheory.Shares
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormVanishingAtPointsMulPowMemSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormVanishingAtPointsMulPowMemSpan
namespace GlobalTheory.Shares.VanDiv

section Model

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem leviO_phla_add_nsmul (x0 : Frame X.Ψ r) (F L : Wt X.Ψ r) (k : ℕ) {z : V (nd X)} (hz : z ∈ OmF X x0)
    (ξ : Fin (nd X) → ℂ) :
    leviO X x0 (phla X (F + k • L)) z ξ = leviO X x0 (phla X F) z ξ + k * leviO X x0 (phla X L) z ξ := by
  have h1 := (IW.phla_cpt_cdAt X x0 hz F).of_le HE.two_le_inf
  have h3 := (IW.phla_cpt_cdAt X x0 hz L).of_le HE.two_le_inf
  have e : (fun w => ((phla X (F + k • L) (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[nhds z]
      fun w => ((phla X F (cpt X x0 w) + (k : ℝ) * phla X L (cpt X x0 w) : ℝ) : ℂ) := by
    filter_upwards [(ExF.isOpen_OmF X x0).mem_nhds hz] with w hw
    rw [OW.phla_add_nsmul X hw]
  unfold leviO leviM
  rw [Y.fc_leviV_congr _ _ _ _ e, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 (contDiffAt_const.mul h3),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h3]
  simp only [Complex.add_re, Complex.re_ofReal_mul]

theorem pnorm_mul_pow_sq (F L : Wt X.Ψ r) (m : ℕ) (g w : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.pnorm (F + m • L) (fun x => g x * w x ^ m) x ^ 2 = X.pnorm F g x ^ 2 * (X.pnorm L w x ^ 2) ^ m := by
  rw [OW.pnorm_sq X _ _ hx, OW.pnorm_sq X _ _ hx, OW.pnorm_sq X _ _ hx, OW.phla_add_nsmul X hx, neg_add,
    Real.exp_add, ← mul_neg, Real.exp_nat_mul, map_mul, map_pow]
  ring

theorem model_division (Xa : ArchInM X) (Fl : FlatM X Xa) (hm : Margins X Xa) (k : ℕ)
    (hfin : ∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS (Xa.Fp + (k + (nd X + 1)) • Xa.L),
      ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x)
    (g : Frame X.Ψ r → ℂ) (hg : X.IsBddSec (Xa.Fp + k • Xa.L) g) (hv : ∀ j, g (Fl.xs j) = 0) :
    ∃ h : Fin (nd X) → Frame X.Ψ r → ℂ, (∀ i, h i ∈ X.SS (Xa.Fp + (k + nd X) • Xa.L)) ∧
      ∀ x ∈ X.dom, g x * Fl.w0 x ^ (nd X + 1) = ∑ i, Fl.s i x * h i x := by
  obtain ⟨-, ⟨bb, m, hbb, hbm, hmar⟩, hL, -, hcusp⟩ := hm
  have e : ∀ a : ℕ, Xa.Fp + k • Xa.L + a • Xa.L = Xa.Fp + (k + a) • Xa.L := fun a => by
    rw [add_nsmul, add_assoc]
  obtain ⟨C, hC⟩ := hg.2
  have hC2 : ∀ x ∈ X.dom, X.pnorm (Xa.Fp + k • Xa.L) g x ^ 2 ≤ C ^ 2 := fun x hx =>
    pow_le_pow_left₀ (BoundedSectionAlgebra.pnorm_nonneg X _ _ _) (hC x hx) 2
  obtain ⟨B, hB⟩ := Fl.weightForm_vanishes.1.1.2
  obtain ⟨K, hK⟩ := Fl.denom_le_family
  obtain ⟨h, hh, hs⟩ := GlobalTheory.DivFreeWeight.division_order_one E r X Xa Fl (Xa.Fp + k • Xa.L)
    ⟨bb, m, hbb, hbm, fun x0 ho z hz ξ => by
      have h1 := hmar x0 ho z hz ξ
      have h2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (hL x0 ho z hz ξ)
      rw [leviO_phla_add_nsmul x0 _ _ k hz]
      linarith⟩
    (by rw [e]; exact hcusp _) (by rw [e]; exact hfin)
    (fun x => g x * Fl.w0 x ^ (nd X + 1))
    ⟨GlobalTheory.Up.DivCorePf.isSec_mul hg.1 (GlobalTheory.Up.DivCorePf.isSec_pow Fl.weightForm_vanishes.1.1.1 _),
      √(C ^ 2 * (B ^ 2) ^ (nd X + 1)), fun x hx => by
        refine Real.le_sqrt_of_sq_le ?_
        rw [pnorm_mul_pow_sq _ _ _ _ _ hx]
        exact mul_le_mul (hC2 x hx) (pow_le_pow_left₀ (sq_nonneg _)
          (pow_le_pow_left₀ (BoundedSectionAlgebra.pnorm_nonneg X _ _ _) (hB x hx) 2) _) (by positivity) (by positivity)⟩
    ⟨C ^ 2 * |K| ^ (nd X + 1), fun x hx => by
      rw [pnorm_mul_pow_sq _ _ _ _ _ hx, mul_assoc, ← mul_pow]
      refine mul_le_mul (hC2 x hx) (pow_le_pow_left₀ (sq_nonneg _) ((hK x hx).trans ?_) _)
        (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)⟩
    (fun j => by simp [hv j])
  exact ⟨h, fun i => hcusp _ _ (e _ ▸ hh i), hs⟩

end Model

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem sp_le_span {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} (R : Rdg X)
    (u : WeightFamilies.Wt D j) : ∃ (K : ℕ) (b : Fin K → B.Cusp j u),
      R.sp u Set.univ ≤ Submodule.span ℂ (Set.range fun i => R.ev (X.inc u (b i))) := by
  obtain ⟨K, b, hb⟩ := Module.Finite.exists_fin (R := B.KO) (M := B.Cusp j u)
  refine ⟨K, b, Submodule.span_le.2 ?_⟩
  rintro _ ⟨F, -, rfl⟩
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun B.KO).1 (hb ▸ Submodule.mem_top : F ∈ _)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, R.ev_smul]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem vanishing_division : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → ∀ k : ℕ, ∀ g ∈ R.sp (addL wF wL k) Set.univ, (∀ q, g (xs q) = 0) → ∃ m : ℕ, R.s w t 0 ^ (m + 1) * g ∈ R.deep w t (addL wF wL (k + m)) 1 := by
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en hen honto k g hg hv
  classical
  have hwt : ∀ (a : ℕ) c, laR T j (addL wF wL a) c = (A.Xa c).Fp + a • (A.Xa c).L := fun a c => by
    rw [(GlobalTheory.Shares.WtDic.weights_dictionary D T h j hj c).2.2.1, A.hF, A.hL]
  obtain ⟨f, hf, hgf⟩ := (GlobalTheory.Shares.span_readings_components D T h j hj n R e hR (addL wF wL k)).1 g hg
  have hfin : ∀ (a : ℕ) (c : (T.U j T.σ₀).Comp), ∃ (K : ℕ) (b : Fin K → Frame ((T.U j T.σ₀).X c).Ψ D.R.r → ℂ),
      ∀ f ∈ ((T.U j T.σ₀).X c).SS ((A.Xa c).Fp + a • (A.Xa c).L),
      ∃ cc : Fin K → ℂ, ∀ x ∈ ((T.U j T.σ₀).X c).dom, f x = ∑ i, cc i * b i x := by
    intro a c
    obtain ⟨K, b, hb⟩ := sp_le_span R (addL wF wL a)
    refine ⟨K, fun i => rdR h j (b i) c, fun p hp => ?_⟩
    have h1 := (GlobalTheory.Shares.span_readings_components D T h j hj n R e hR _).2.1 _ _ (honto a)
      (Function.update (fun _ => 0) c p) (fun c' => by
        by_cases hc : c' = c
        · subst hc
          rw [Function.update_self, hwt]
          exact hp
        · rw [Function.update_of_ne hc]
          exact (siegelSpaceAlgebra_holds _ _ _ 0 0).2.2.1.1.1)
    obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hb h1)
    refine ⟨cc, fun x hx => ?_⟩
    have h2 := congrFun hcc (e.symm ⟨c, ⟨x, hx⟩⟩)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2] at h2
    rw [Equiv.apply_symm_apply] at h2
    simpa using h2.symm
  have hdiv := fun c => model_division (A.Xa c) (Fl.Fl c) (A.mar c) k (hfin _ c) (f c)
    (hwt k c ▸ (hf c).1.1) (fun i => by
      have h1 := hv (en.symm ⟨c, i⟩)
      rw [hgf, hen, Equiv.apply_symm_apply] at h1
      exact h1)
  choose H hH hsum using hdiv
  refine ⟨WeightFamilies.dimY D j, ?_⟩
  have hs : ∀ i y, R.s w t i y = ∑ a, t (i, a) * rdR h j (w a) (e y).1 (e y).2.1 := fun i y => by
    simp only [Rdg.s, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2]
  have hmem : ∀ i : Fin (WeightFamilies.dimY D j),
      (fun y => H (e y).1 (Fin.cast (A.dim _).symm i) (e y).2.1) ∈ R.sp (addL wF wL (k + WeightFamilies.dimY D j)) Set.univ :=
    fun i => (GlobalTheory.Shares.span_readings_components D T h j hj n R e hR _).2.1 _ _ (honto _) (fun c => H c (Fin.cast (A.dim c).symm i))
      (fun c => by
        rw [hwt]
        have h1 := hH c (Fin.cast (A.dim c).symm i)
        rwa [show k + nd ((T.U j T.σ₀).X c) = k + WeightFamilies.dimY D j by rw [A.dim c]] at h1)
  have heq : R.s w t 0 ^ (WeightFamilies.dimY D j + 1) * g =
      ∑ i : Fin (WeightFamilies.dimY D j), R.mon w t (Pi.single i 1) * fun y => H (e y).1 (Fin.cast (A.dim _).symm i) (e y).2.1 := by
    have hmon : ∀ i : Fin (WeightFamilies.dimY D j), R.mon w t (Pi.single i 1) = R.s w t i.succ := fun i => by
      unfold Rdg.mon
      rw [Finset.prod_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
      simp
    funext y
    simp only [hmon, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, hs]
    have h1 := hsum _ _ (e y).2.2
    rw [show nd ((T.U j T.σ₀).X (e y).1) + 1 = WeightFamilies.dimY D j + 1 by rw [A.dim]] at h1
    rw [← Fl.h0, hgf, mul_comm, h1]
    refine Fintype.sum_equiv (finCongr (A.dim (e y).1)) _ _ fun a => ?_
    rw [Fl.hs]
    rfl
  rw [heq]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨Pi.single i 1, _, by simp, hmem i, rfl⟩

end GlobalTheory.Shares.VanDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormVanishingAtPointsMulPowMemSpanStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_vanishing_at_points_mul_pow_mem_span : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → ∀ k : ℕ, ∀ g ∈ R.sp (addL wF wL k) Set.univ, (∀ q, g (xs q) = 0) → ∃ m : ℕ, R.s w t 0 ^ (m + 1) * g ∈ R.deep w t (addL wF wL (k + m)) 1 := by
  first | exact @GlobalTheory.Shares.VanDiv.vanishing_division | exact GlobalTheory.Shares.VanDiv.vanishing_division | (intros; apply GlobalTheory.Shares.VanDiv.vanishing_division <;> assumption)
end
end

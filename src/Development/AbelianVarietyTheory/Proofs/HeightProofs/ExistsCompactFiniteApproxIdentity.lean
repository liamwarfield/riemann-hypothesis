module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefExtendsHolomorphically
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
public import Formalism.LocalToGlobal.ProjectiveLattices.PtOfSPf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactFiniteApproxIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfOrthKfin
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

noncomputable section

namespace GlobalTheory.KFinSep

variable {n : ℕ} {ε : Fin n → Bool}

lemma kfin_of_span {ι : Type} [Finite ι] (b : ι → KG ε → ℂ) (hc : ∀ i, Continuous (b i))
    (ht : ∀ i (k₀ : KG ε), (fun k => b i (k₀ * k)) ∈ Submodule.span ℂ (Set.range b) ∧
      (fun k => b i (k * k₀)) ∈ Submodule.span ℂ (Set.range b)) (i : ι) : KFinFun ε (b i) := by
  refine ⟨Submodule.span ℂ (Set.range b), FiniteDimensional.span_of_finite ℂ (Set.finite_range b),
    Submodule.subset_span ⟨i, rfl⟩, ?_, ?_⟩
  · intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hc j
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul a x _ hx => exact hx.const_smul a
  · intro φ hφ k₀
    induction hφ using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact ht j k₀
    | zero => exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
    | add x y _ _ hx hy => exact ⟨Submodule.add_mem _ hx.1 hy.1, Submodule.add_mem _ hx.2 hy.2⟩
    | smul a x _ hx => exact ⟨Submodule.smul_mem _ a hx.1, Submodule.smul_mem _ a hx.2⟩

lemma kfin_const (c : ℂ) : KFinFun ε (fun _ => c) :=
  kfin_of_span (ε := ε) (ι := Unit) (fun _ _ => c) (fun _ => continuous_const)
    (fun i _ => ⟨Submodule.subset_span ⟨i, rfl⟩, Submodule.subset_span ⟨i, rfl⟩⟩) ()

lemma kfin_add {p q : KG ε → ℂ} (hp : KFinFun ε p) (hq : KFinFun ε q) : KFinFun ε (p + q) := by
  obtain ⟨F, _, hpF, hFc, hF⟩ := hp
  obtain ⟨G, _, hqG, hGc, hG⟩ := hq
  refine ⟨F ⊔ G, inferInstance, Submodule.add_mem_sup hpF hqG, ?_, ?_⟩
  · intro φ hφ
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hφ
    exact (hFc x hx).add (hGc y hy)
  · intro φ hφ k₀
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hφ
    exact ⟨Submodule.add_mem_sup (hF x hx k₀).1 (hG y hy k₀).1, Submodule.add_mem_sup (hF x hx k₀).2 (hG y hy k₀).2⟩

lemma kfin_mul {p q : KG ε → ℂ} (hp : KFinFun ε p) (hq : KFinFun ε q) : KFinFun ε (p * q) := by
  obtain ⟨F, hFf, hpF, hFc, hF⟩ := hp
  obtain ⟨G, hGf, hqG, hGc, hG⟩ := hq
  refine ⟨F * G, ?_, Submodule.mul_mem_mul hpF hqG, ?_, ?_⟩
  · exact Module.Finite.iff_fg.2 ((Module.Finite.iff_fg.1 hFf).mul (Module.Finite.iff_fg.1 hGf))
  · intro φ hφ
    refine Submodule.mul_induction_on hφ (fun x hx y hy => (hFc x hx).mul (hGc y hy)) (fun x y hx hy => hx.add hy)
  · intro φ hφ k₀
    refine Submodule.mul_induction_on (C := fun φ => (fun k => φ (k₀ * k)) ∈ F * G ∧ (fun k => φ (k * k₀)) ∈ F * G)
      hφ (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · exact ⟨Submodule.mul_mem_mul (hF x hx k₀).1 (hG y hy k₀).1, Submodule.mul_mem_mul (hF x hx k₀).2 (hG y hy k₀).2⟩
    · exact ⟨Submodule.add_mem _ hx.1 hy.1, Submodule.add_mem _ hx.2 hy.2⟩

lemma mem_span_of_sum {ι κ : Type} [Fintype κ] (b : ι → KG ε → ℂ) (f : KG ε → ℂ) (c : κ → ℂ) (j : κ → ι)
    (h : ∀ k, f k = ∑ l, c l * b (j l) k) : f ∈ Submodule.span ℂ (Set.range b) := by
  have : f = ∑ l, c l • b (j l) := by
    funext k; simp [h, Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j l, rfl⟩)

lemma kfin_entry (i j : Fin n) : KFinFun ε (fun k => toMK k i j) := by
  refine kfin_of_span (ε := ε) (ι := Fin n × Fin n) (fun a k => toMK k a.1 a.2)
    (fun a => (GlobalTheory.KHolExt.ent ε a.1 a.2).continuous) (fun a k₀ => ⟨?_, ?_⟩) (i, j)
  · refine mem_span_of_sum _ _ (fun l => toMK k₀ a.1 l) (fun l => (l, a.2)) fun k => ?_
    simp only [GlobalTheory.KHolExt.toMK_mul, Matrix.mul_apply]
  · refine mem_span_of_sum _ _ (fun l => toMK k₀ l a.2) (fun l => (a.1, l)) fun k => ?_
    simp only [GlobalTheory.KHolExt.toMK_mul, Matrix.mul_apply, mul_comm]

lemma kfin_conjEntry (i j : Fin n) : KFinFun ε (fun k => star (toMK k i j)) := by
  refine kfin_of_span (ε := ε) (ι := Fin n × Fin n) (fun a k => star (toMK k a.1 a.2))
    (fun a => (GlobalTheory.KHolExt.ent ε a.1 a.2).continuous.star) (fun a k₀ => ⟨?_, ?_⟩) (i, j)
  · refine mem_span_of_sum _ _ (fun l => star (toMK k₀ a.1 l)) (fun l => (l, a.2)) fun k => ?_
    simp only [GlobalTheory.KHolExt.toMK_mul, Matrix.mul_apply, star_sum, star_mul']
  · refine mem_span_of_sum _ _ (fun l => star (toMK k₀ l a.2)) (fun l => (a.1, l)) fun k => ?_
    simp only [GlobalTheory.KHolExt.toMK_mul, Matrix.mul_apply, star_sum, star_mul', mul_comm]

def finAlg (ε : Fin n → Bool) : StarSubalgebra ℂ C(KG ε, ℂ) where
  carrier := {p | KFinFun ε p ∧ KFinFun ε (star p : C(KG ε, ℂ))}
  mul_mem' := fun {p q} hp hq => ⟨kfin_mul hp.1 hq.1, by
    rw [star_mul']; exact kfin_mul hp.2 hq.2⟩
  add_mem' := fun {p q} hp hq => ⟨kfin_add hp.1 hq.1, by
    rw [star_add]; exact kfin_add hp.2 hq.2⟩
  algebraMap_mem' := fun c => ⟨by
    have : ((algebraMap ℂ C(KG ε, ℂ) c : C(KG ε, ℂ)) : KG ε → ℂ) = fun _ => c := by
      funext k; simp
    rw [this]; exact kfin_const c, by
    have : ((star (algebraMap ℂ C(KG ε, ℂ) c) : C(KG ε, ℂ)) : KG ε → ℂ) = fun _ => star c := by
      funext k; simp
    rw [this]; exact kfin_const _⟩
  star_mem' := fun {p} hp => ⟨hp.2, by rw [star_star]; exact hp.1⟩

lemma finAlg_dense (ε : Fin n → Bool) : (finAlg ε).topologicalClosure = ⊤ := by
  refine ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ ?_
  intro x y hxy
  have h : toMK x ≠ toMK y := fun h => hxy ((GlobalTheory.KHolExt.isEmb ε).injective h)
  obtain ⟨i, j, hij⟩ : ∃ i j, toMK x i j ≠ toMK y i j := by
    by_contra hc
    push Not at hc
    exact h (Matrix.ext hc)
  exact ⟨GlobalTheory.KHolExt.ent ε i j, ⟨GlobalTheory.KHolExt.ent ε i j, ⟨kfin_entry i j, kfin_conjEntry i j⟩, rfl⟩, hij⟩

end GlobalTheory.KFinSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactFiniteApproxIdentity
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

noncomputable section
namespace GlobalTheory.KFinApprox

theorem approx_identity : ∀ (n : ℕ) (ε : Fin n → Bool) (X : Type) [TopologicalSpace X] (F : X → KG ε → ℂ),
    (Continuous fun p : X × KG ε => F p.1 p.2) → ∀ C : Set X, IsCompact C → ∀ δ : ℝ, 0 < δ →
    ∃ e : KG ε → ℂ, KFinFun ε e ∧ ∀ x ∈ C, ‖F x 1 - ∫ k, e k * F x k ∂(muK ε)‖ < δ := by
  intro n ε X _ F hF C hC δ hδ

  have hFx : ∀ x, Continuous (F x) := fun x =>
    hF.comp (Continuous.prodMk continuous_const continuous_id)
  have hintC : ∀ g : KG ε → ℂ, Continuous g → Integrable g (muK ε) := fun g hg =>
    hg.integrable_of_hasCompactSupport (isClosed_tsupport g).isCompact
  have hintR : ∀ g : KG ε → ℝ, Continuous g → Integrable g (muK ε) := fun g hg =>
    hg.integrable_of_hasCompactSupport (isClosed_tsupport g).isCompact

  have hG : Continuous fun z : KG ε × X => ‖F z.2 z.1 - F z.2 1‖ :=
    ((hF.comp (Continuous.prodMk continuous_snd continuous_fst)).sub
      (hF.comp (Continuous.prodMk continuous_snd continuous_const))).norm
  have hev : ∀ᶠ k in 𝓝 (1 : KG ε), ∀ x ∈ C, ‖F x k - F x 1‖ < δ / 3 := by
    refine hC.eventually_forall_of_forall_eventually (fun y _ => ?_)
    have ht := hG.tendsto ((1 : KG ε), y)
    simp only [sub_self, norm_zero] at ht
    exact ht.eventually_lt_const (by positivity)
  obtain ⟨U, hUP, hUo, hU1⟩ := eventually_nhds_iff.1 hev

  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed hUo.isClosed_compl
    (isClosed_singleton (x := (1 : KG ε))) (Set.disjoint_singleton_right.2 (fun h => h hU1))
  have hf1' : f 1 = 1 := by simpa using hf1 (Set.mem_singleton (1 : KG ε))
  have hfnn : ∀ k, 0 ≤ f k := fun k => (hf01 k).1
  have hfU : ∀ k, k ∉ U → f k = 0 := fun k hk => by simpa using hf0 hk
  have hIpos : 0 < ∫ k, f k ∂(muK ε) :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero f.continuous
      (isClosed_tsupport _).isCompact (fun k => hfnn k) (x := 1) (by rw [hf1']; norm_num)
  obtain ⟨I, hIdef⟩ : ∃ I, ∫ k, f k ∂(muK ε) = I := ⟨_, rfl⟩
  rw [hIdef] at hIpos

  let ψ : C(KG ε, ℂ) := ⟨fun k => ((f k / I : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (f.continuous.div_const I)⟩
  have hψ : ∀ k, ψ k = ((f k / I : ℝ) : ℂ) := fun k => rfl
  have hψint : ∫ k, ψ k ∂(muK ε) = 1 := by
    simp only [hψ]
    rw [integral_complex_ofReal, integral_div, hIdef, div_self hIpos.ne']
    simp
  have hψnorm : ∀ k, ‖ψ k‖ = f k / I := fun k => by
    rw [hψ, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hfnn k) hIpos.le)]
  have h7 := GlobalTheory.KFinSep.finAlg_dense ε

  obtain ⟨M, hM⟩ := (hC.prod isCompact_univ).exists_bound_of_continuousOn hF.continuousOn
  obtain ⟨A, hA, hMA⟩ : ∃ A : ℝ, 0 < A ∧ M * (muK ε).real Set.univ ≤ A := by
    have hm : 0 ≤ (muK ε).real Set.univ := measureReal_nonneg
    refine ⟨(|M| + 1) * ((muK ε).real Set.univ + 1), by positivity, ?_⟩
    nlinarith [le_abs_self M, abs_nonneg M]
  have hη : 0 < δ / (3 * A) := div_pos hδ (by linarith)

  have hmem : ψ ∈ (GlobalTheory.KFinSep.finAlg ε).topologicalClosure := by
    rw [h7]; exact StarSubalgebra.mem_top
  have hmem' : ψ ∈ closure ((GlobalTheory.KFinSep.finAlg ε : Set C(KG ε, ℂ))) := hmem
  obtain ⟨p, hp, hpd⟩ := Metric.mem_closure_iff.1 hmem' (δ / (3 * A)) hη
  have hpK : KFinFun ε p := hp.1
  have hpk : ∀ k, ‖ψ k - p k‖ ≤ δ / (3 * A) := fun k => by
    have h := ContinuousMap.norm_coe_le_norm (ψ - p) k
    rw [← dist_eq_norm] at h
    simpa using h.trans hpd.le
  refine ⟨p, hpK, fun x hx => ?_⟩
  have i1 : Integrable (fun k => ψ k * F x 1) (muK ε) := hintC _ (ψ.continuous.mul continuous_const)
  have i2 : Integrable (fun k => ψ k * F x k) (muK ε) := hintC _ (ψ.continuous.mul (hFx x))
  have i3 : Integrable (fun k => p k * F x k) (muK ε) := hintC _ (p.continuous.mul (hFx x))
  have e1 : ∫ k, ψ k * (F x 1 - F x k) ∂(muK ε) = F x 1 - ∫ k, ψ k * F x k ∂(muK ε) := by
    simp_rw [mul_sub]
    rw [integral_sub i1 i2, integral_mul_const, hψint, one_mul]
  have e2 : ∫ k, (ψ k - p k) * F x k ∂(muK ε) =
      ∫ k, ψ k * F x k ∂(muK ε) - ∫ k, p k * F x k ∂(muK ε) := by
    simp_rw [sub_mul]
    exact integral_sub i2 i3
  have e3 : F x 1 - ∫ k, p k * F x k ∂(muK ε) =
      ∫ k, ψ k * (F x 1 - F x k) ∂(muK ε) + ∫ k, (ψ k - p k) * F x k ∂(muK ε) := by
    rw [e1, e2]; ring
  have b1 : ‖∫ k, ψ k * (F x 1 - F x k) ∂(muK ε)‖ ≤ δ / 3 := by
    have hg : Integrable (fun k => f k / I * (δ / 3)) (muK ε) :=
      hintR _ ((f.continuous.div_const I).mul continuous_const)
    refine (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun k => ?_)).trans_eq ?_
    · rw [norm_mul, hψnorm]
      by_cases hk : k ∈ U
      · have := hUP k hk x hx
        rw [norm_sub_rev] at this
        exact mul_le_mul_of_nonneg_left this.le (div_nonneg (hfnn k) hIpos.le)
      · rw [hfU k hk]; simp
    · rw [integral_mul_const, integral_div, hIdef, div_self hIpos.ne', one_mul]
  have b2 : ‖∫ k, (ψ k - p k) * F x k ∂(muK ε)‖ ≤ δ / 3 := by
    refine (norm_integral_le_of_norm_le_const (C := δ / (3 * A) * M)
      (Filter.Eventually.of_forall fun k => ?_)).trans ?_
    · rw [norm_mul]
      exact mul_le_mul (hpk k) (hM (x, k) ⟨hx, Set.mem_univ _⟩) (norm_nonneg _) hη.le
    · calc δ / (3 * A) * M * (muK ε).real Set.univ
          = δ / (3 * A) * (M * (muK ε).real Set.univ) := by ring
        _ ≤ δ / (3 * A) * A := mul_le_mul_of_nonneg_left hMA hη.le
        _ = δ / 3 := by field_simp
  rw [e3]
  calc ‖∫ k, ψ k * (F x 1 - F x k) ∂(muK ε) + ∫ k, (ψ k - p k) * F x k ∂(muK ε)‖
      ≤ δ / 3 + δ / 3 := (norm_add_le _ _).trans (add_le_add b1 b2)
    _ < δ := by linarith

end GlobalTheory.KFinApprox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactFiniteApproxIdentityStatement
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compactFinite_approxIdentity : ∀ (n : ℕ) (ε : Fin n → Bool) (X : Type) [TopologicalSpace X] (F : X → KG ε → ℂ), (Continuous fun p : X × KG ε => F p.1 p.2) → ∀ C : Set X, IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ e : KG ε → ℂ, KFinFun ε e ∧ ∀ x ∈ C, ‖F x 1 - ∫ k, e k * F x k ∂(muK ε)‖ < δ := by
  first | exact @GlobalTheory.KFinApprox.approx_identity | exact GlobalTheory.KFinApprox.approx_identity | (intros; apply GlobalTheory.KFinApprox.approx_identity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.IterateOnePlusCasOfEq
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

def onePlusCas (σ : Mx n → (H →L[ℂ] H)) {d : ℕ} (X : Fin d → Mx n) (v : H) : H :=
  v - ∑ i, dRep σ (X i) (dRep σ (X i) v)

theorem sm_onePlusCas (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n} (hX : ∀ i, X i ∈ lieSet ε)
    {v : H} (hv : Sm ε σ v) : Sm ε σ (onePlusCas σ X v) := by
  have h1 : ∀ i, Sm ε σ (dRep σ (X i) (dRep σ (X i) v)) := fun i =>
    dRep_mem (isUnit_Jm ε) hσ (dRep_mem (isUnit_Jm ε) hσ hv (hX i)) (hX i)
  exact (smooth (Jm ε) σ).sub_mem hv ((smooth (Jm ε) σ).sum_mem fun i _ => h1 i)

theorem sm_iterate_onePlusCas (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n} (hX : ∀ i, X i ∈ lieSet ε)
    {v : H} (hv : Sm ε σ v) (r : ℕ) : Sm ε σ ((onePlusCas σ X)^[r] v) := by
  induction r with
  | zero => simpa using hv
  | succ r ih => rw [Function.iterate_succ_apply']; exact sm_onePlusCas hσ hX ih

theorem inner_onePlusCas (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n} (hX : ∀ i, X i ∈ lieSet ε)
    {b v : H} (hb : Sm ε σ b) (hv : Sm ε σ v) : ⟪b, onePlusCas σ X v⟫_ℂ = ⟪onePlusCas σ X b, v⟫_ℂ := by
  have key : ∀ i, ⟪b, dRep σ (X i) (dRep σ (X i) v)⟫_ℂ = ⟪dRep σ (X i) (dRep σ (X i) b), v⟫_ℂ := fun i => by
    have hv1 := dRep_mem (isUnit_Jm ε) hσ hv (hX i)
    have hb1 := dRep_mem (isUnit_Jm ε) hσ hb (hX i)
    rw [inner_dRep (isUnit_Jm ε) hσ hb hv1 (hX i), inner_dRep (isUnit_Jm ε) hσ hb1 hv (hX i), neg_neg]
  simp only [onePlusCas, inner_sub_left, inner_sub_right, inner_sum, sum_inner, key]

theorem inner_iterate_onePlusCas (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n}
    (hX : ∀ i, X i ∈ lieSet ε) {b v : H} (hb : Sm ε σ b) (hv : Sm ε σ v) (r : ℕ) :
    ⟪b, (onePlusCas σ X)^[r] v⟫_ℂ = ⟪(onePlusCas σ X)^[r] b, v⟫_ℂ := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply, ih (sm_onePlusCas hσ hX hv), Function.iterate_succ_apply',
      inner_onePlusCas hσ hX (sm_iterate_onePlusCas hσ hX hb r) hv]

theorem onePlusCas_smul (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n} (hX : ∀ i, X i ∈ lieSet ε)
    (c : ℂ) {v : H} (hv : Sm ε σ v) : onePlusCas σ X (c • v) = c • onePlusCas σ X v := by
  have h : ∀ i, dRep σ (X i) (dRep σ (X i) (c • v)) = c • dRep σ (X i) (dRep σ (X i) v) := fun i =>
    Dw_smul hσ (l := [X i, X i]) (by simp [hX i]) c hv
  simp only [onePlusCas, h, smul_sub, Finset.smul_sum]

theorem iterate_onePlusCas_of_eq (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n}
    (hX : ∀ i, X i ∈ lieSet ε) {v : H} (hv : Sm ε σ v) {μ : ℂ} (h : onePlusCas σ X v = μ • v) (r : ℕ) :
    (onePlusCas σ X)^[r] v = μ ^ r • v := by
  induction r with
  | zero => simp
  | succ r ih => rw [Function.iterate_succ_apply', ih, onePlusCas_smul hσ hX _ hv, h, smul_smul, pow_succ]

end GlobalTheory.TypeSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.NotMemOfMulExp
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

namespace GlobalTheory.TypeSum.CoefClos

variable {n : ℕ}

abbrev Ltr (ε : Fin n → Bool) : Type := {X : Mx n // X ∈ lieSet ε} ⊕ {k : Mx n // k ∈ Kset ε}

section Vec

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def ltrV (σ : Mx n → (H →L[ℂ] H)) {ε : Fin n → Bool} : Ltr ε → H → H
  | Sum.inl X => dRep σ X.1
  | Sum.inr k => σ k.1

def wordV (σ : Mx n → (H →L[ℂ] H)) {ε : Fin n → Bool} (u : List (Ltr ε)) (v : H) : H := u.foldr (ltrV σ) v

end Vec

def rder (X : Mx n) (f : Mx n → ℂ) (g : Mx n) : ℂ := deriv (fun t : ℝ => f (g * NormedSpace.exp (t • X))) 0

def ltrF {ε : Fin n → Bool} : Ltr ε → (Mx n → ℂ) → Mx n → ℂ
  | Sum.inl X => rder X.1
  | Sum.inr k => fun f g => f (g * k.1)

def wordF {ε : Fin n → Bool} (u : List (Ltr ε)) (f : Mx n → ℂ) : Mx n → ℂ := u.foldr ltrF f

def wordE {M : Type} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool} (τ : Ltr ε → Module.End ℂ M)
    (u : List (Ltr ε)) (m : M) : M := u.foldr (fun x => τ x) m

def CSm (ε : Fin n → Bool) (f : Mx n → ℂ) : Prop :=
  ∃ F : List (Mx n) → Mx n → ℂ, (∀ g ∈ UJset ε, F [] g = f g) ∧ IsDerFam ε F ∧
    ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ContinuousOn (F l) (UJset ε)

variable {ε : Fin n → Bool}

theorem CSm.congr {f f' : Mx n → ℂ} (h : CSm ε f) (e : ∀ g ∈ UJset ε, f g = f' g) : CSm ε f' := by
  obtain ⟨F, h1, h2, h3⟩ := h
  exact ⟨F, fun g hg => (h1 g hg).trans (e g hg), h2, h3⟩

theorem CSm.add {f f' : Mx n → ℂ} (h : CSm ε f) (h' : CSm ε f') : CSm ε (f + f') := by
  obtain ⟨F, h1, h2, h3⟩ := h
  obtain ⟨F', k1, k2, k3⟩ := h'
  refine ⟨fun l g => F l g + F' l g, fun g hg => by simp [h1 g hg, k1 g hg], fun l hl X hX g hg => ?_,
    fun l hl => (h3 l hl).add (k3 l hl)⟩
  exact (h2 l hl X hX g hg).add (k2 l hl X hX g hg)

theorem CSm.smul {f : Mx n → ℂ} (h : CSm ε f) (c : ℂ) : CSm ε (c • f) := by
  obtain ⟨F, h1, h2, h3⟩ := h
  refine ⟨fun l g => c * F l g, fun g hg => by simp [h1 g hg], fun l hl X hX g hg => ?_,
    fun l hl => continuousOn_const.mul (h3 l hl)⟩
  exact (h2 l hl X hX g hg).const_mul c

theorem CSm.zero : CSm ε (0 : Mx n → ℂ) :=
  ⟨fun _ _ => 0, fun _ _ => rfl, fun _ _ _ _ _ _ => hasDerivAt_const _ _, fun _ _ => continuousOn_const⟩

theorem CSm.hasDerivAt {f : Mx n → ℂ} (h : CSm ε f) {X : Mx n} (hX : X ∈ lieSet ε) {g : Mx n} (hg : g ∈ UJset ε) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp (t • X))) (rder X f g) 0 := by
  obtain ⟨F, h1, h2, -⟩ := h
  have h0 : HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp (t • X))) (F [X] g) 0 := by
    refine (h2 [] (by simp) X hX g hg).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    exact (h1 _ (mul_mem_UJ hg (exp_mem_UJ hX t))).symm
  rwa [rder, h0.deriv]

theorem CSm.rder_eq {f : Mx n → ℂ} {F : List (Mx n) → Mx n → ℂ} (h1 : ∀ g ∈ UJset ε, F [] g = f g)
    (h2 : IsDerFam ε F) {X : Mx n} (hX : X ∈ lieSet ε) {g : Mx n} (hg : g ∈ UJset ε) : rder X f g = F [X] g := by
  have h0 : HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp (t • X))) (F [X] g) 0 := by
    refine (h2 [] (by simp) X hX g hg).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    exact (h1 _ (mul_mem_UJ hg (exp_mem_UJ hX t))).symm
  rw [rder, h0.deriv]

theorem CSm.rder {f : Mx n → ℂ} (h : CSm ε f) {X : Mx n} (hX : X ∈ lieSet ε) : CSm ε (rder X f) := by
  obtain ⟨F, h1, h2, h3⟩ := h
  refine ⟨fun l => F (l ++ [X]), fun g hg => (CSm.rder_eq h1 h2 hX hg).symm, fun l hl Y hY g hg => ?_,
    fun l hl => h3 _ ?_⟩
  · exact h2 (l ++ [X]) (fun Z hZ => (List.mem_append.1 hZ).elim (hl Z) (by simp_all)) Y hY g hg
  · exact fun Z hZ => (List.mem_append.1 hZ).elim (hl Z) (by simp_all)

theorem exp_conj_smul {k : Mx n} (hk : k ∈ UJset ε) (Y : Mx n) (t : ℝ) :
    k⁻¹ * NormedSpace.exp (t • Y) * k = NormedSpace.exp (t • (k⁻¹ * Y * k)) := by
  have hu : IsUnit k⁻¹ := (isUnit_of_UJ (inv_mem_UJ hk))
  have e := Matrix.exp_conj k⁻¹ (t • Y) hu
  rw [Matrix.nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (isUnit_of_UJ hk))] at e
  rw [← e, Matrix.mul_smul, Matrix.smul_mul]

theorem CSm.rt {f : Mx n → ℂ} (h : CSm ε f) {k : Mx n} (hk : k ∈ Kset ε) : CSm ε (fun g => f (g * k)) := by
  obtain ⟨F, h1, h2, h3⟩ := h
  have hkU := K_le_UJ hk
  refine ⟨fun l g => F (l.map fun Y => k⁻¹ * Y * k) (g * k), fun g hg => by simpa using h1 _ (mul_mem_UJ hg hkU),
    fun l hl Y hY g hg => ?_, fun l hl => ?_⟩
  · have hl' : ∀ Z ∈ l.map (fun Y => k⁻¹ * Y * k), Z ∈ lieSet ε := by
      intro Z hZ
      obtain ⟨Z, hZ', rfl⟩ := List.mem_map.1 hZ
      exact conj_mem_lie (isUnit_Jm ε) hkU (hl Z hZ')
    have hY' : k⁻¹ * Y * k ∈ lieSet ε := conj_mem_lie (isUnit_Jm ε) hkU hY
    have := h2 _ hl' _ hY' (g * k) (mul_mem_UJ hg hkU)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    show F _ (g * NormedSpace.exp (t • Y) * k) = F _ (g * k * NormedSpace.exp (t • (k⁻¹ * Y * k)))
    rw [← exp_conj_smul hkU Y t]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc g k, mul_inv_UJ hkU, Matrix.mul_one]
  · have hl' : ∀ Z ∈ l.map (fun Y => k⁻¹ * Y * k), Z ∈ lieSet ε := by
      intro Z hZ
      obtain ⟨Z, hZ', rfl⟩ := List.mem_map.1 hZ
      exact conj_mem_lie (isUnit_Jm ε) hkU (hl Z hZ')
    exact (h3 _ hl').comp (continuous_id.mul continuous_const).continuousOn fun g hg => mul_mem_UJ hg hkU

theorem CSm.ltrF {f : Mx n → ℂ} (h : CSm ε f) (x : Ltr ε) : CSm ε (ltrF x f) := by
  rcases x with X | k
  · exact h.rder X.2
  · exact h.rt k.2

theorem CSm.wordF {f : Mx n → ℂ} (h : CSm ε f) (u : List (Ltr ε)) : CSm ε (wordF u f) := by
  induction u with
  | nil => exact h
  | cons x u ih => exact ih.ltrF x

def Smo (ε : Fin n → Bool) : Submodule ℂ (Mx n → ℂ) where
  carrier := {f | (∀ g ∉ UJset ε, f g = 0) ∧ CSm ε f}
  add_mem' := fun {f f'} hf hf' => ⟨fun g hg => by simp [hf.1 g hg, hf'.1 g hg], hf.2.add hf'.2⟩
  zero_mem' := ⟨fun _ _ => rfl, CSm.zero⟩
  smul_mem' := fun c f hf => ⟨fun g hg => by simp [hf.1 g hg], hf.2.smul c⟩

theorem not_mem_of_mul_exp {X : Mx n} (hX : X ∈ lieSet ε) {g : Mx n} (hg : g ∉ UJset ε) (t : ℝ) :
    g * NormedSpace.exp (t • X) ∉ UJset ε := by
  intro h
  apply hg
  have := mul_mem_UJ h (exp_mem_UJ hX (-t))
  rwa [Matrix.mul_assoc, ← exp_add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at this

theorem rder_off {f : Mx n → ℂ} (hf : ∀ g ∉ UJset ε, f g = 0) {X : Mx n} (hX : X ∈ lieSet ε) {g : Mx n}
    (hg : g ∉ UJset ε) : rder X f g = 0 := by
  have : (fun t : ℝ => f (g * NormedSpace.exp (t • X))) = fun _ => 0 :=
    funext fun t => hf _ (not_mem_of_mul_exp hX hg t)
  rw [rder, this, deriv_const]

theorem rt_off {f : Mx n → ℂ} (hf : ∀ g ∉ UJset ε, f g = 0) {k : Mx n} (hk : k ∈ Kset ε) {g : Mx n}
    (hg : g ∉ UJset ε) : f (g * k) = 0 := by
  refine hf _ fun h => hg ?_
  have := mul_mem_UJ h (inv_mem_UJ (K_le_UJ hk))
  rwa [Matrix.mul_assoc, mul_inv_UJ (K_le_UJ hk), Matrix.mul_one] at this

theorem ltrF_mem {f : Mx n → ℂ} (hf : f ∈ Smo ε) (x : Ltr ε) : ltrF x f ∈ Smo ε := by
  refine ⟨fun g hg => ?_, hf.2.ltrF x⟩
  rcases x with X | k
  · exact rder_off hf.1 X.2 hg
  · exact rt_off hf.1 k.2 hg

theorem rder_add {f f' : Mx n → ℂ} (hf : f ∈ Smo ε) (hf' : f' ∈ Smo ε) {X : Mx n} (hX : X ∈ lieSet ε) :
    rder X (f + f') = rder X f + rder X f' := by
  funext g
  by_cases hg : g ∈ UJset ε
  · exact ((hf.2.hasDerivAt hX hg).add (hf'.2.hasDerivAt hX hg)).deriv
  · simp [rder_off (Submodule.add_mem _ hf hf').1 hX hg, rder_off hf.1 hX hg, rder_off hf'.1 hX hg]

theorem rder_smul {f : Mx n → ℂ} (hf : f ∈ Smo ε) (c : ℂ) {X : Mx n} (hX : X ∈ lieSet ε) :
    rder X (c • f) = c • rder X f := by
  funext g
  by_cases hg : g ∈ UJset ε
  · exact ((hf.2.hasDerivAt hX hg).const_mul c).deriv
  · simp [rder_off (Submodule.smul_mem _ c hf).1 hX hg, rder_off hf.1 hX hg]

def ltrM (x : Ltr ε) : Module.End ℂ (Smo ε) where
  toFun f := ⟨ltrF x f.1, ltrF_mem f.2 x⟩
  map_add' f f' := by
    apply Subtype.ext
    rcases x with X | k
    · exact rder_add f.2 f'.2 X.2
    · rfl
  map_smul' c f := by
    apply Subtype.ext
    rcases x with X | k
    · exact rder_smul f.2 c X.2
    · rfl

theorem coe_wordE (u : List (Ltr ε)) (f : Smo ε) : ((wordE ltrM u f : Smo ε) : Mx n → ℂ) = wordF u f := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    show ltrF x (wordE ltrM u f : Smo ε).1 = ltrF x (wordF u f.1)
    rw [ih]

theorem wordF_congr {f f' : Mx n → ℂ} (e : ∀ g ∈ UJset ε, f g = f' g) (u : List (Ltr ε)) :
    ∀ g ∈ UJset ε, wordF u f g = wordF u f' g := by
  induction u with
  | nil => exact e
  | cons x u ih =>
    intro g hg
    rcases x with X | k
    · show deriv _ 0 = deriv _ 0
      congr 1
      funext t
      exact ih _ (mul_mem_UJ hg (exp_mem_UJ X.2 t))
    · exact ih _ (mul_mem_UJ hg (K_le_UJ k.2))

end GlobalTheory.TypeSum.CoefClos

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.RangeMulStep
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.T0

namespace GlobalTheory.SecPoint

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem range_mul_step {m : ℕ} {x y : X.Forms} (hx : x ∈ LinearMap.range (X.inc (addL (wt0 D j) wL m)))
    (hy : y ∈ LinearMap.range (X.inc wL)) : x * y ∈ LinearMap.range (X.inc (addL (wt0 D j) wL (m + 1))) := by
  obtain ⟨F, rfl⟩ := hx
  obtain ⟨G, rfl⟩ := hy
  obtain ⟨H, hH⟩ := X.inc_mul wL _ G F
  rw [← wadd_addL, mul_comm, hH]
  exact ⟨H, rfl⟩

theorem range_pow {m : ℕ} {y x : X.Forms} (hy : y ∈ LinearMap.range (X.inc (addL (wt0 D j) wL m)))
    (hx : x ∈ LinearMap.range (X.inc wL)) (e : ℕ) :
    y * x ^ e ∈ LinearMap.range (X.inc (addL (wt0 D j) wL (m + e))) := by
  induction e with
  | zero => simpa using hy
  | succ e ih =>
    rw [pow_succ, ← mul_assoc, ← add_assoc]
    exact range_mul_step X ih hx

theorem range_prod (d : Fin N →₀ ℕ) {m : ℕ} {y : X.Forms}
    (hy : y ∈ LinearMap.range (X.inc (addL (wt0 D j) wL m))) (s : Finset (Fin N)) :
    y * ∏ i ∈ s, X.inc wL (w i) ^ d i ∈ LinearMap.range (X.inc (addL (wt0 D j) wL (m + ∑ i ∈ s, d i))) := by
  classical
  refine Finset.induction_on s (by rwa [Finset.prod_empty, Finset.sum_empty, mul_one, add_zero]) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  have e1 : y * (X.inc wL (w a) ^ d a * ∏ i ∈ s, X.inc wL (w i) ^ d i) =
      (y * ∏ i ∈ s, X.inc wL (w i) ^ d i) * X.inc wL (w a) ^ d a := by ring
  have e2 : m + (d a + ∑ i ∈ s, d i) = m + ∑ i ∈ s, d i + d a := by ring
  rw [e1, e2]
  exact range_pow X ih ⟨w a, rfl⟩ (d a)

theorem range_aeval {k : ℕ} (Pw : MvPolynomial (Fin N) B.KO) (hPw : Pw.IsHomogeneous k) {m : ℕ} {y : X.Forms}
    (hy : y ∈ LinearMap.range (X.inc (addL (wt0 D j) wL m))) :
    y * MvPolynomial.aeval (fun i => X.inc wL (w i)) Pw ∈ LinearMap.range (X.inc (addL (wt0 D j) wL (m + k))) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Pw.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial, mul_left_comm, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have hdeg : ∑ i ∈ d.support, d i = k := by
    have := hPw (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have h := range_prod X N w d hy d.support
  rw [hdeg] at h
  exact h

theorem exists_ratio {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)
    (hB : CurveLoc.BirAt X N w gF) (hk : ∃ k, gF (X.inc wL (w k)) ≠ 0) (a : Ω) :
    ∃ (m : ℕ) (p q : B.Cusp j (addL (wt0 D j) wL m)), gF (X.inc _ p) ≠ 0 ∧ a * gF (X.inc _ p) = gF (X.inc _ q) := by
  obtain ⟨k0, hk0⟩ := hk
  obtain ⟨k, g, Pw, hPw, hne, he⟩ := hB a
  have h1 : X.inc wL (w k0) ∈ LinearMap.range (X.inc (addL (wt0 D j) wL 1)) := by
    rw [add_zero_weight_one_eq]; exact ⟨_, rfl⟩
  obtain ⟨p, hp⟩ := range_aeval X N w Pw hPw h1
  have hG : X.inc wL (w k0) * X.inc (wsmul k wL) g ∈ LinearMap.range (X.inc (addL (wt0 D j) wL (1 + k))) := by
    obtain ⟨H, hH⟩ := X.inc_mul wL _ (w k0) g
    rw [add_comm, ← wadd_addL, addL, zero_weight_add, hH]
    exact ⟨H, rfl⟩
  obtain ⟨q, hq⟩ := hG
  have hPv : gF (MvPolynomial.aeval (fun i => X.inc wL (w i)) Pw) =
      MvPolynomial.aeval (fun i => gF (X.inc wL (w i))) Pw :=
    MvPolynomial.comp_aeval_apply (fun i => X.inc wL (w i)) gF Pw
  refine ⟨1 + k, p, q, ?_, ?_⟩
  · rw [hp, map_mul, hPv]
    exact mul_ne_zero hk0 hne
  · rw [hp, hq, map_mul, map_mul, hPv, ← he]
    ring

def evK {F : Type} [Field F] (ev : Rp X la N →+* F) : Kp X la N →+* F :=
  ev.comp (algebraMap (Kp X la N) (Rp X la N))

theorem ev_smul {F : Type} [Field F] (ev : Rp X la N →+* F) (c : Kp X la N) (g : Rp X la N) :
    ev (c • g) = evK X la N ev c * ev g := by
  rw [Algebra.smul_def, map_mul]; rfl

theorem lift_algKp {F : Type} [Field F] (ev : Rp X la N →+* F) (hu : IsUnit (ev (sec X la w 0))) (c : Kp X la N) :
    IsLocalization.Away.lift (sec X la w 0) hu
      ((algebraMap (Kp X la N) ↥(Frac0 X la w) c : ↥(Frac0 X la w)) : Lw X la w) = evK X la N ev c := by
  show IsLocalization.Away.lift (sec X la w 0) hu (algebraMap (Kp X la N) (Lw X la w) c) = _
  rw [IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w), liftEv_alg]
  rfl

section Fam

variable {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)

theorem exists_point [Finite ι]
    (hinj : ∀ (u : WeightFamilies.Wt D j) (G : B.Cusp j u), (∀ Z, gF Z (X.inc u G) = 0) → G = 0)
    (hsplit : ∀ (Z : ι) (k : Fin N), ∃ g : B.Cusp j wL, gF Z (X.inc wL g) = gF Z (X.inc wL (w k)) ∧
      ∀ Z', Z' ≠ Z → gF Z' (X.inc wL g) = 0)
    (hB : ∀ Z, CurveLoc.BirAt X N w (gF Z)) (hC : ∀ Z, CurveLoc.CountQAt X la N w (gF Z))
    {F : Type} [Field F] (ev : Rp X la N →+* F) (hu : IsUnit (ev (sec X la w 0)))
    (honS : ∀ i : Fin (WeightFamilies.dimY D j), ev (sec X la w i.succ) = 0) :
    ∃ (Z : ι) (τ : Ω Z →+* F) (σ : F), σ ≠ 0 ∧
      (∀ (u : WeightFamilies.Wt D j) (G : B.Cusp j u), gF Z (X.inc u G) = 0 → ev (emb X la N (X.inc u G)) = 0) ∧
      (∀ a : B.KO, τ (algebraMap B.KO (Ω Z) a) =
        evK X la N ev (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a))) ∧
      ∀ (k : ℕ) (G : X.Forms), emb X la N G ∈ Vw X la N (addL (wt0 D j) wL k) →
        ev (emb X la N G) = τ (gF Z G) * σ ^ k := by
  classical
  have := Fintype.ofFinite ι
  letI : Algebra (Kp X la N) F := (evK X la N ev).toAlgebra
  let ψ : ↥(Frac0 X la w) →ₐ[Kp X la N] F :=
    { (IsLocalization.Away.lift (sec X la w 0) hu).comp (Frac0 X la w).val.toRingHom with
      commutes' := fun c => lift_algKp X la N w ev hu c }
  have hψ : ∀ (x : ↥(Frac0 X la w)) (k : ℕ) (g : Rp X la N), (x : Lw X la w) = frac X la w k g →
      ψ x = ev g * (ev (sec X la w 0))⁻¹ ^ k := fun x k g hx => by
    show IsLocalization.Away.lift (sec X la w 0) hu (x : Lw X la w) = _
    rw [hx, liftEv_frac]
  have hQ : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime _
  have hJ : Jid X la w ≤ RingHom.ker ψ := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, hψ _ 1 _ (coe_sfr X la w i.succ), honS, zero_mul]
  have hinf : (Finset.univ : Finset ι).inf (fun Z => RingHom.ker (phiZ X la N (Ω Z) (gF Z) w)) ≤ RingHom.ker ψ := by
    intro f hf
    have hf' : ∀ Z, phiZ X la N (Ω Z) (gF Z) w f = 0 := fun Z =>
      RingHom.mem_ker.1 (Finset.inf_le (f := fun Z => RingHom.ker (phiZ X la N (Ω Z) (gF Z) w))
        (Finset.mem_univ Z) hf)
    rw [CurveInj.fraction_zero_injective X la N Ω gF w hinj f hf']
    exact Ideal.zero_mem _
  obtain ⟨Z, -, hZ⟩ := (Ideal.IsPrime.inf_le' hQ).1 hinf
  obtain ⟨χ, hχ⟩ := pos_factor (phiZ X la N (Ω Z) (gF Z) w) ψ
    (fun f hf => RingHom.mem_ker.1 (hZ (RingHom.mem_ker.2 hf))) (fun r => by
      obtain ⟨a, p, hp, hr⟩ := CurveLoc.loc_of_bir X la N w (gF Z) (hB Z) (hC Z) r
      exact ⟨a, p, fun h0 => hp _ hQ hJ hZ (RingHom.mem_ker.2 h0), hr⟩)
  have hs := pos_sec_ne X la N w (gF Z) χ
  have hs0 := hu.ne_zero
  refine ⟨Z, χ.toRingHom.comp (CurveLoc.psiZ X la N w (gF Z)), ev (sec X la w 0) *
    (χ (algebraMap (RZ X la N (Ω Z)) (RZs X la N (Ω Z) (gF Z) w) (rzMap X la N (Ω Z) (gF Z) (sec X la w 0))))⁻¹,
    mul_ne_zero hs0 (inv_ne_zero hs), fun u G h0 => ?_,
    fun a => (congrArg χ (pos_psiZ_alg X la N w (gF Z) a)).trans (χ.commutes _), fun k G hG => ?_⟩
  · choose g hg using hsplit Z
    have hmem : frac X la w 1 (CurveLoc.secOf X la N g) ∈ Frac0 X la w :=
      Algebra.subset_adjoin (frac_mem_Hfr X la w (by rw [add_zero_weight_one_eq]; exact CurveLoc.secOf_mem X la N g))
    have h1 : (⟨_, hmem⟩ : ↥(Frac0 X la w)) - 1 ∈ RingHom.ker (phiZ X la N (Ω Z) (gF Z) w) := by
      rw [RingHom.mem_ker, map_sub, map_one, CurveLoc.phiZ_of_eq X la N w (gF Z) _ 1 _ rfl,
        CurveLoc.rzMap_secOf X la N (gF Z) g w (fun k => (hg k).1), CurveLoc.secOf_self, pow_one,
        CurveLoc.weight_zero_section_mul_inv, sub_self]
    have h2 := hZ h1
    rw [RingHom.mem_ker, map_sub, map_one, hψ _ 1 _ rfl, pow_one, sub_eq_zero] at h2
    have he : ev (CurveLoc.secOf X la N g) ≠ 0 := left_ne_zero_of_mul_eq_one h2
    have hHe : emb X la N (X.inc u G) * CurveLoc.secOf X la N g = 0 :=
      CurveInj.vw_inj X la N Ω gF (wadd u wL) (hinj _)
        (mul_mem_Vw X la N (emb_mem_Vw X la N u G) (CurveLoc.secOf_mem X la N g))
        fun Z' => by
          rw [map_mul]
          by_cases hZ' : Z' = Z
          · subst hZ'
            rw [rzMap_emb, h0, TensorProduct.tmul_zero, TensorProduct.tmul_zero, zero_mul]
          · rw [CurveLoc.rzMap_secOf_zero X la N (gF Z') g (fun k => (hg k).2 Z' hZ'), mul_zero]
    have h3 := congrArg ev hHe
    rw [map_mul, map_zero] at h3
    exact (mul_eq_zero.1 h3).resolve_right he
  · have h1 := ((hχ _).trans (hψ _ k _ rfl)).symm.trans (phi_fraction_base_value X la N w (gF Z) χ k G hG)
    show _ = χ (CurveLoc.psiZ X la N w (gF Z) (gF Z G)) * _
    rw [mul_pow, mul_left_comm, ← h1, mul_left_comm, ← mul_pow, mul_inv_cancel₀ hs0, one_pow, mul_one]

end Fam

section One

variable {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)

theorem ev_sec {F : Type} [Field F] (ev : Rp X la N →+* F) (τ : Ω →+* F) (σ : F)
    (hc : ∀ (k : ℕ) (G : X.Forms), emb X la N G ∈ Vw X la N (addL (wt0 D j) wL k) →
      ev (emb X la N G) = τ (gF G) * σ ^ k) (i : Fin (WeightFamilies.dimY D j + 1)) :
    ev (sec X la w i) = (∑ k, evK X la N ev (@algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N (i, k))) *
      τ (gF (X.inc wL (w k)))) * σ := by
  unfold Formalism.MainNotions.Gaps.EtaleWeightGaps.sec
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ev_smul, hc 1 _ (by rw [add_zero_weight_one_eq]; exact emb_mem_Vw X la N wL (w k)), pow_one, mul_assoc]

end One

end Rec

end GlobalTheory.SecPoint
end
end

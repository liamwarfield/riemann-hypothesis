module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HwvLoweringSpanLower
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk30.GLOps.{u_2, u_3} :
    ℕ → (K : Type u_2) → (V : Type u_3) → [inst : Field K] → [inst_1 : AddCommGroup V] → [_root_.Module K V] → Type u_3 :=
    fun (n : ℕ) (K : Type u_2) (V : Type u_3) [Field K] [AddCommGroup V] [_root_.Module K V] ↦
      Fin n → Fin n → Module.End K V

noncomputable def UpperTheory.Reformulated.B.Qk30.loweringMonoid.{u_1, u_2} :
    {n : ℕ} →
      {K : Type u_1} →
        {V : Type u_2} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qk30.GLOps n K V → Submonoid (Module.End K V) :=
    fun {n : ℕ} {K : Type u_1} {V : Type u_2} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qk30.GLOps n K V) ↦
      Submonoid.closure {g : Module.End K V | ∃ (c : Fin n), ∃ d < c, g = E c d}

noncomputable def UpperTheory.Reformulated.B.Qk30.weightSp.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qk30.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qk30.GLOps n K V) (mu : Fin n → ℤ) ↦
      ⨅ (a : Fin n), LinearMap.ker (E a a - (↑(mu a) : K) • (1 : Module.End K V))

noncomputable def UpperTheory.Reformulated.B.Qk30.IsHWV.{u_2, u_3} :
    {n : ℕ} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qk30.GLOps n K V → (Fin n → ℤ) → V → Prop :=
    fun {n : ℕ} {K : Type u_2} {V : Type u_3} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qk30.GLOps n K V) (lam : Fin n → ℤ) (v : V) ↦
      v ≠ (0 : V) ∧ v ∈ UpperTheory.Reformulated.B.Qk30.weightSp E lam ∧ ∀ (a b : Fin n), a < b → (E a b : V → V) v = (0 : V)

noncomputable def UpperTheory.Reformulated.B.Qk30.hwvLoweringSpan.{u_1, u_2} :
    {n : ℕ} →
      {K : Type u_1} →
        {V : Type u_2} →
          [inst : Field K] →
            [inst_1 : AddCommGroup V] →
              [inst_2 : _root_.Module K V] → UpperTheory.Reformulated.B.Qk30.GLOps n K V → (Fin n → ℤ) → Submodule K V :=
    fun {n : ℕ} {K : Type u_1} {V : Type u_2} [Field K] [AddCommGroup V] [_root_.Module K V]
        (E : UpperTheory.Reformulated.B.Qk30.GLOps n K V) (mu : Fin n → ℤ) ↦
      Submodule.span K
        {x : V | ∃ u ∈ UpperTheory.Reformulated.B.Qk30.loweringMonoid E, ∃ (w : V), UpperTheory.Reformulated.B.Qk30.IsHWV E mu w ∧ x = (u : V → V) w}

theorem UpperTheory.Reformulated.B.Qk30.hwv_lowering_span_lower.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      (E : UpperTheory.Reformulated.B.Qk30.GLOps n K V) (mu : Fin n → ℤ) {a b : Fin n},
      b < a → ∀ {x : V}, x ∈ UpperTheory.Reformulated.B.Qk30.hwvLoweringSpan E mu → (E a b : V → V) x ∈ UpperTheory.Reformulated.B.Qk30.hwvLoweringSpan E mu := by
  intro n K V _ _ _ E mu a b hab x hx
  unfold UpperTheory.Reformulated.B.Qk30.hwvLoweringSpan at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, w, hw, rfl⟩ := hy
    refine Submodule.subset_span ⟨E a b * u, ?_, w, hw, rfl⟩
    exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨a, b, hab, rfl⟩) hu
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hy
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProductFirstParts
noncomputable def UpperTheory.Reformulated.B.product_first_partition.blockEmb.{u_1, u_2} :
    (K : Type u_1) →
      [inst : CommRing K] →
        {S : Type u_2} → {k n : ℕ} → S → MvPolynomial (Fin k × Fin n) K →ₐ[K] MvPolynomial (S × Fin k × Fin n) K :=
    fun (K : Type u_1) [CommRing K] {S : Type u_2} {k n : ℕ} (s : S) ↦ MvPolynomial.rename fun (v : Fin k × Fin n) ↦ (s, v)

noncomputable def UpperTheory.Reformulated.B.product_first_partition.tensorLat.{u_1, u_2, u_3} :
    (R : Type u_1) →
      (K : Type u_2) →
        [inst : CommRing R] →
          [inst_1 : CommRing K] →
            [inst_2 : Algebra R K] →
              {S : Type u_3} →
                [Fintype S] →
                  {k n : ℕ} →
                    (S → Submodule R (MvPolynomial (Fin k × Fin n) K)) → Submodule R (MvPolynomial (S × Fin k × Fin n) K) :=
    fun (R : Type u_1) (K : Type u_2) [CommRing R] [CommRing K] [Algebra R K] {S : Type u_3} [Fintype S] {k n : ℕ}
        (M : S → Submodule R (MvPolynomial (Fin k × Fin n) K)) ↦
      Submodule.span R
        {P : MvPolynomial (S × Fin k × Fin n) K |
          ∃ (F : S → MvPolynomial (Fin k × Fin n) K),
            (∀ (s : S), F s ∈ M s) ∧
              P =
                ∏ s : S,
                  (UpperTheory.Reformulated.B.product_first_partition.blockEmb K s : MvPolynomial (Fin k × Fin n) K → MvPolynomial (S × Fin k × Fin n) K)
                    (F s)}

private theorem UpperTheory.Reformulated.B.product_first_partition.span_mul_eq {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (M N : Submodule R A) :
    Submodule.span R {X : A | ∃ F ∈ M, ∃ G ∈ N, X = F * G} = M * N := by
  rw [Submodule.mul_def]
  congr 1
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_mul, SetLike.mem_coe, eq_comm]

private theorem UpperTheory.Reformulated.B.product_first_partition.tensorLat_eq {R K : Type} [CommRing R] [CommRing K] [Algebra R K]
    {S : Type} [Fintype S] [DecidableEq S] {k n : ℕ}
    (N : S → Submodule R (MvPolynomial (Fin k × Fin n) K)) :
    UpperTheory.Reformulated.B.product_first_partition.tensorLat R K N =
      ∏ s : S, (N s).map ((UpperTheory.Reformulated.B.product_first_partition.blockEmb K s).restrictScalars R).toLinearMap := by
  have h : ∀ s : S, (N s).map ((UpperTheory.Reformulated.B.product_first_partition.blockEmb K s).restrictScalars R).toLinearMap =
      Submodule.span R (((N s).map
        ((UpperTheory.Reformulated.B.product_first_partition.blockEmb K s).restrictScalars R).toLinearMap : Submodule R _) : Set _) :=
    fun s => (Submodule.span_eq _).symm
  rw [Finset.prod_congr rfl fun s _ => h s, Submodule.prod_span]
  unfold UpperTheory.Reformulated.B.product_first_partition.tensorLat
  congr 1
  ext P
  rw [Set.mem_fintype_prod]
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨fun s => UpperTheory.Reformulated.B.product_first_partition.blockEmb K s (F s), fun s => ⟨F s, hF s, rfl⟩, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    choose F hF hFg using hg
    exact ⟨F, hF, Finset.prod_congr rfl fun s _ => (hFg s).symm⟩

theorem UpperTheory.Reformulated.B.product_first_partition.tensor_onto :
    ∀ {R K : Type} [inst : CommRing R] [inst_1 : Field K] [inst_2 : Algebra R K] {S : Type} [inst_3 : Fintype S]
      [DecidableEq S] {k n : ℕ} (A B M : S → Submodule R (MvPolynomial (Fin k × Fin n) K)),
      (∀ (s : S), M s ≤ Submodule.span R {X : MvPolynomial (Fin k × Fin n) K | ∃ F ∈ A s, ∃ G ∈ B s, X = F * G}) →
        UpperTheory.Reformulated.B.product_first_partition.tensorLat R K M ≤
          Submodule.span R
            {X : MvPolynomial (S × Fin k × Fin n) K |
              ∃ P ∈ UpperTheory.Reformulated.B.product_first_partition.tensorLat R K A, ∃ Q ∈ UpperTheory.Reformulated.B.product_first_partition.tensorLat R K B, X = P * Q} := by
  intro R K _ _ _ S _ _ k n A B M h
  rw [UpperTheory.Reformulated.B.product_first_partition.span_mul_eq, UpperTheory.Reformulated.B.product_first_partition.tensorLat_eq, UpperTheory.Reformulated.B.product_first_partition.tensorLat_eq,
    UpperTheory.Reformulated.B.product_first_partition.tensorLat_eq, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod' fun s _ => ?_
  rw [← Submodule.map_mul]
  refine Submodule.map_mono ?_
  rw [← UpperTheory.Reformulated.B.product_first_partition.span_mul_eq]
  exact h s
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WeightsCompactStabilizer
noncomputable def UpperTheory.Reformulated.B.WeightsCompactStabilizer.GlRel.{u_1} :
    {A : Type u_1} → [Ring A] → {n : ℕ} → (Fin n → Fin n → A) → Prop :=
    fun {A : Type u_1} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) ↦
      ∀ (a b c d : Fin n),
        E a b * E c d - E c d * E a b = (if b = c then E a d else (0 : A)) - if d = a then E c b else (0 : A)

noncomputable def UpperTheory.Reformulated.B.WeightsCompactStabilizer.KUnit :
    {n : ℕ} →
      {V : Type} →
        [inst : NormedAddCommGroup V] →
          [inst_1 : InnerProductSpace ℂ V] → (Fin n → Bool) → (Fin n → Fin n → Module.End ℂ V) → Prop :=
    fun {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ε : Fin n → Bool)
        (E : Fin n → Fin n → Module.End ℂ V) ↦
      ∀ (a b : Fin n), ε a = ε b → ∀ (x y : V), Inner.inner ℂ ((E a b : V → V) x) y = Inner.inner ℂ x ((E b a : V → V) y)

noncomputable def UpperTheory.Reformulated.B.WeightsCompactStabilizer.KStab :
    {n : ℕ} →
      {V : Type} →
        [inst : AddCommGroup V] →
          [inst_1 : _root_.Module ℂ V] → (Fin n → Bool) → (Fin n → Fin n → Module.End ℂ V) → Submodule ℂ V → Prop :=
    fun {n : ℕ} {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
        (S : Submodule ℂ V) ↦
      ∀ (a b : Fin n), ε a = ε b → ∀ v ∈ S, (E a b : V → V) v ∈ S

noncomputable def UpperTheory.Reformulated.B.WeightsCompactStabilizer.IsWeight.{u_1} :
    {V : Type u_1} →
      [inst : AddCommGroup V] →
        [inst_1 : _root_.Module ℂ V] → {n : ℕ} → (Fin n → Fin n → Module.End ℂ V) → (Fin n → ℝ) → V → Prop :=
    fun {V : Type u_1} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ)
        (w : V) ↦
      ∀ (a : Fin n), (E a a : V → V) w = (↑(μ a) : ℂ) • w

theorem UpperTheory.Reformulated.B.WeightsCompactStabilizer.exists_weight :
    ∀ {n : ℕ} {ε : Fin n → Bool} {V : Type} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℂ V]
      {E : Fin n → Fin n → Module.End ℂ V},
      UpperTheory.Reformulated.B.WeightsCompactStabilizer.GlRel E →
        UpperTheory.Reformulated.B.WeightsCompactStabilizer.KUnit ε E →
          ∀ {Q : Submodule ℂ V} [FiniteDimensional ℂ ↥Q],
            UpperTheory.Reformulated.B.WeightsCompactStabilizer.KStab ε E Q → Q ≠ ⊥ → ∃ (ν : Fin n → ℝ), ∃ x ∈ Q, x ≠ (0 : V) ∧ UpperTheory.Reformulated.B.WeightsCompactStabilizer.IsWeight E ν x := by
  intro n ε V _ _ E hG hU Q _ hS hQ
  classical
  let T : Fin n → Module.End ℂ Q := fun a => (E a a).restrict (fun v hv => hS a a rfl v hv)
  have hT : ∀ a (x : Q), ((T a x : Q) : V) = E a a x := fun a x => rfl
  have hsym : ∀ a, (T a).IsSymmetric := by
    intro a x y
    rw [Submodule.coe_inner, Submodule.coe_inner, hT, hT]
    exact hU a a rfl x y
  have hcomm : Pairwise (Function.onFun Commute T) := by
    intro a b hab
    have h := hG a a b b
    rw [if_neg hab, if_neg hab.symm, sub_zero, sub_eq_zero] at h
    change T a * T b = T b * T a
    ext x
    have := congrArg (fun f : Module.End ℂ V => f x) h
    simpa [hT] using this
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym hcomm
  have hex : ∃ α : Fin n → ℂ, (⨅ j, Module.End.eigenspace (T j) (α j)) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    rw [iSup_eq_bot.mpr hcon] at htop
    have : Nontrivial Q := Submodule.nontrivial_iff_ne_bot.mpr hQ
    exact bot_ne_top htop
  obtain ⟨α, hα⟩ := hex
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα
  have hx' : ∀ a, x ∈ Module.End.eigenspace (T a) (α a) := fun a =>
    (Submodule.mem_iInf _).mp hx a
  have hre : ∀ a, (((α a).re : ℝ) : ℂ) = α a := fun a =>
    Complex.conj_eq_iff_re.mp
      ((hsym a).conj_eigenvalue_eq_self
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx' a, hx0⟩))
  refine ⟨fun a => (α a).re, x, x.2, fun h => hx0 (Subtype.ext h), fun a => ?_⟩
  have h := congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp (hx' a))
  rw [hT] at h
  rw [hre a, h]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MulIntegralStatement
namespace OneParameterGroupMulIntegral
open intervalIntegral

private lemma mul_integral {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (c : A) (f : ℝ → A) (a b : ℝ) (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    c * (∫ s in a..b, f s) = ∫ s in a..b, c * f s := by
  have := (ContinuousLinearMap.mul ℝ A c).intervalIntegral_comp_comm (μ := MeasureTheory.volume)
    (a := a) (b := b) (f := f)
  simpa using (this hf).symm

end OneParameterGroupMulIntegral

open OneParameterGroupMulIntegral in
theorem UpperTheory.Reformulated.B.OneParameterGroupDifferentiableAtZero.main.{u_1} :
    ∀ {W : Type u_1} [inst : NormedAddCommGroup W]
    [inst_1 : NormedSpace ℂ W] [CompleteSpace W] (φ : ℝ → W →L[ℂ] W),
    Continuous φ → φ (0 : ℝ) = (1 : W →L[ℂ] W) → (∀ (s t : ℝ), φ (s + t) = φ s * φ t) → DifferentiableAt ℝ φ (0 : ℝ) := by
  intro W _ _ _ φ hc h0 hmul

  obtain ⟨ε, εpos, hε⟩ := Metric.continuous_iff.mp hc 0 (1/2) (by norm_num)
  set δ : ℝ := ε / 2 with hδ
  have δpos : 0 < δ := by positivity
  set A : W →L[ℂ] W := ∫ s in (0:ℝ)..δ, φ s with hA
  have hint : ∀ a b : ℝ, IntervalIntegrable φ MeasureTheory.volume a b :=
    fun a b => hc.intervalIntegrable a b
  have hest : ‖A - δ • (1 : W →L[ℂ] W)‖ ≤ 1/2 * δ := by
    have e1 : A - δ • (1 : W →L[ℂ] W) = ∫ s in (0:ℝ)..δ, (φ s - 1) := by
      rw [intervalIntegral.integral_sub (hint 0 δ) intervalIntegrable_const,
        intervalIntegral.integral_const]
      simp <;> rfl
    rw [e1]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := δ) (C := 1/2)
      (f := fun s => φ s - 1) (by
        intro x hx
        rw [Set.uIoc_of_le δpos.le] at hx
        have hxd : dist x 0 < ε := by
          rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]; linarith [hx.2]
        have := hε x hxd
        rw [dist_eq_norm, h0] at this
        exact this.le)
    simpa [abs_of_pos δpos] using this
  have hsmall : ‖1 - δ⁻¹ • A‖ < 1 := by
    have : 1 - δ⁻¹ • A = -(δ⁻¹ • (A - δ • (1 : W →L[ℂ] W))) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ δpos.ne']; simp
    rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr δpos)]
    calc δ⁻¹ * ‖A - δ • (1 : W →L[ℂ] W)‖ ≤ δ⁻¹ * (1/2 * δ) :=
          mul_le_mul_of_nonneg_left hest (inv_pos.mpr δpos).le
      _ = 1/2 := by field_simp
      _ < 1 := by norm_num
  set u := Units.oneSub (1 - δ⁻¹ • A) hsmall
  have hu : (u : W →L[ℂ] W) = δ⁻¹ • A := by simp [u, Units.val_oneSub]
  set B : W →L[ℂ] W := δ⁻¹ • ((u⁻¹ : (W →L[ℂ] W)ˣ) : W →L[ℂ] W)
  have hAB : A * B = 1 := by
    simp only [B, mul_smul_comm, ← smul_mul_assoc, ← hu]
    exact u.mul_inv
  set F : ℝ → W →L[ℂ] W := fun u => ∫ s in (0:ℝ)..u, φ s
  have key : ∀ t, φ t = (F (t + δ) - F t) * B := by
    intro t
    have h1 : φ t * A = F (t + δ) - F t := by
      rw [hA, mul_integral _ _ _ _ (hint 0 δ)]
      have : (fun s => φ t * φ s) = fun s => φ (t + s) := by
        funext s; rw [hmul]
      rw [this, intervalIntegral.integral_comp_add_left (fun s => φ s) t]
      simp only [add_zero, F]
      rw [intervalIntegral.integral_interval_sub_left (hint 0 (t + δ)) (hint 0 t)]
    calc φ t = φ t * A * B := by rw [mul_assoc, hAB, mul_one]
      _ = _ := by rw [h1]
  have hF : ∀ x, HasDerivAt F (φ x) x := fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hd : HasDerivAt (fun t => (F (t + δ) - F t) * B) ((φ (0 + δ) - φ 0) * B) 0 := by
    apply HasDerivAt.mul_const
    apply HasDerivAt.sub
    · exact (hF (0 + δ)).comp_add_const 0 δ
    · exact hF 0
  have : φ = fun t => (F (t + δ) - F t) * B := funext key
  rw [this]
  exact hd.differentiableAt
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestAlt
namespace AevalSpecializationAlgHom

open MvPolynomial

private theorem key {Ω : Type} [Field Ω] [Algebra ℚ Ω] {σ : Type} (τ : σ → Ω) (F : MvPolynomial σ ℚ)
    {E : Type} [CommRing E] [Algebra ℚ E] (u : σ → E) (hF : aeval τ F ≠ (0 : Ω))
    (v : E) (hv : v * aeval u F = 1) (P : MvPolynomial (Option σ) ℚ) :
    ∃ (N : ℕ) (G : MvPolynomial σ ℚ),
      aeval (fun o => Option.elim o (aeval τ F)⁻¹ τ) P * (aeval τ F) ^ N = aeval τ G ∧
      aeval (fun o => Option.elim o v u) P * (aeval u F) ^ N = aeval u G := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, by simp, by simp⟩
  | add p q hp hq =>
    obtain ⟨N1, G1, h1, h1'⟩ := hp
    obtain ⟨N2, G2, h2, h2'⟩ := hq
    refine ⟨N1 + N2, G1 * F ^ N2 + G2 * F ^ N1, ?_, ?_⟩
    · simp only [map_add (f := _), map_mul, map_pow, ← h1, ← h2]; ring
    · simp only [map_add (f := _), map_mul, map_pow, ← h1', ← h2']; ring
  | mul_X p o hp =>
    obtain ⟨N, G, h1, h1'⟩ := hp
    cases o with
    | none =>
      refine ⟨N + 1, G, ?_, ?_⟩
      · simp only [map_mul, aeval_X, Option.elim_none]
        rw [← h1, pow_succ]
        field_simp
      · simp only [map_mul, aeval_X, Option.elim_none]
        rw [← h1', pow_succ]
        linear_combination (aeval (fun o => Option.elim o v u) p * aeval u F ^ N) * hv
    | some i =>
      refine ⟨N, G * X i, ?_, ?_⟩
      · simp only [map_mul, aeval_X, Option.elim_some, ← h1]; ring
      · simp only [map_mul, aeval_X, Option.elim_some, ← h1']; ring

end AevalSpecializationAlgHom

theorem UpperTheory.Reformulated.B.Yde9.main :
    ∀ (Ω : Type) [inst : Field Ω] [inst_1 : Algebra ℚ Ω] (σ : Type) (τ : σ → Ω) (F : MvPolynomial σ ℚ) (S : Subalgebra ℚ Ω)
      (E : Type) [inst_2 : CommRing E] [inst_3 : Algebra ℚ E] (u : σ → E),
      (MvPolynomial.aeval τ : MvPolynomial σ ℚ → Ω) F ≠ (0 : Ω) →
        S = Algebra.adjoin ℚ (Insert.insert ((MvPolynomial.aeval τ : MvPolynomial σ ℚ → Ω) F)⁻¹ (Set.range τ)) →
          (∀ (G : MvPolynomial σ ℚ),
              (MvPolynomial.aeval τ : MvPolynomial σ ℚ → Ω) G = (0 : Ω) →
                (MvPolynomial.aeval u : MvPolynomial σ ℚ → E) G = (0 : E)) →
            IsUnit ((MvPolynomial.aeval u : MvPolynomial σ ℚ → E) F) →
              ∃ (φ : ↥S →ₐ[ℚ] E),
                ∀ (G : MvPolynomial σ ℚ) (s : ↥S),
                  (↑s : Ω) = (MvPolynomial.aeval τ : MvPolynomial σ ℚ → Ω) G →
                    (φ : ↥S → E) s = (MvPolynomial.aeval u : MvPolynomial σ ℚ → E) G := by
  intro Ω _ _ σ τ F S E _ _ u hF hS hker hU
  obtain ⟨w, hw⟩ := hU
  set v : E := ((w⁻¹ : Eˣ) : E) with hvdef
  have hv : v * MvPolynomial.aeval u F = 1 := by rw [← hw]; simp [v]
  set τ' : Option σ → Ω := fun o => Option.elim o (MvPolynomial.aeval τ F)⁻¹ τ with hτ'
  set u' : Option σ → E := fun o => Option.elim o v u with hu'
  have hS' : S = (MvPolynomial.aeval τ').range := by
    rw [hS, ← Algebra.adjoin_range_eq_range_aeval, Option.range_eq]
    rfl
  subst hS'
  have hsurj := AlgHom.rangeRestrict_surjective (MvPolynomial.aeval τ' : MvPolynomial (Option σ) ℚ →ₐ[ℚ] Ω)
  have hK : ∀ P ∈ RingHom.ker (MvPolynomial.aeval τ' : MvPolynomial (Option σ) ℚ →ₐ[ℚ] Ω).rangeRestrict,
      (MvPolynomial.aeval u') P = 0 := by
    intro P hP
    rw [RingHom.mem_ker] at hP
    have hP' : MvPolynomial.aeval τ' P = 0 := congrArg Subtype.val hP
    obtain ⟨N, G, h1, h1'⟩ := AevalSpecializationAlgHom.key τ F u hF v hv P
    have h0 : MvPolynomial.aeval τ G = 0 := by
      rw [← h1]; simp only [τ'] at hP'; simp [hP']
    have h2 := hker G h0
    rw [h2] at h1'
    have hunit : IsUnit (MvPolynomial.aeval u F ^ N) := by
      rw [← hw]; exact (w.isUnit).pow N
    exact (hunit.mul_left_eq_zero).mp h1'
  let e := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let L := Ideal.Quotient.liftₐ (RingHom.ker (MvPolynomial.aeval τ' : MvPolynomial (Option σ) ℚ →ₐ[ℚ] Ω).rangeRestrict) (MvPolynomial.aeval u') hK
  refine ⟨L.comp e.symm.toAlgHom, ?_⟩
  intro G s hs
  have hs' : s = (MvPolynomial.aeval τ').rangeRestrict (MvPolynomial.rename some G) := by
    apply Subtype.ext
    rw [hs]
    simp [MvPolynomial.aeval_rename]
    rfl
  rw [hs']
  have he : e.symm ((MvPolynomial.aeval τ').rangeRestrict (MvPolynomial.rename some G)) =
      Ideal.Quotient.mk _ (MvPolynomial.rename some G) :=
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply hsurj _
  change L (e.symm ((MvPolynomial.aeval τ').rangeRestrict (MvPolynomial.rename some G))) = _
  rw [he]
  change MvPolynomial.aeval u' (MvPolynomial.rename some G) = _
  rw [MvPolynomial.aeval_rename]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SmoothOnGroupSum
noncomputable def UpperTheory.Reformulated.B.Qh27.Jm :
    {n : Nat} → (Fin n → Bool) → Matrix (Fin n) (Fin n) Complex :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @Matrix.diagonal (Fin n) Complex (instDecidableEqFin n) Complex.instZero fun (a : Fin n) ↦
        @ite Complex (@Eq Bool (ε a) Bool.true) (instDecidableEqBool (ε a) Bool.true)
          (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))
          (@Neg.neg Complex Complex.instNeg (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne)))

noncomputable def UpperTheory.Reformulated.B.Qh27.inUJ :
    {n : Nat} → (Fin n → Bool) → Matrix (Fin n) (Fin n) Complex → Prop :=
    fun {n : Nat} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) Complex) ↦
      @Eq (Matrix (Fin n) (Fin n) Complex)
        (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
            Complex.instAddCommMonoid)
          (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
              Complex.instAddCommMonoid)
            (@Matrix.conjTranspose (Fin n) (Fin n) Complex
              (@InvolutiveStar.toStar Complex
                (@StarAddMonoid.toInvolutiveStar Complex
                  (@AddCommMonoid.toAddMonoid Complex
                    (@NonUnitalNonAssocSemiring.toAddCommMonoid Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))))
                  (@StarRing.toStarAddMonoid Complex
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                    Complex.instStarRing)))
              g)
            (@UpperTheory.Reformulated.B.Qh27.Jm n ε))
          g)
        (@UpperTheory.Reformulated.B.Qh27.Jm n ε)

noncomputable def UpperTheory.Reformulated.B.Qh27.SmoothOnG :
    {n : Nat} → (Fin n → Bool) → (Matrix (Fin n) (Fin n) Complex → Complex) → Prop :=
    fun {n : Nat} (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) Complex → Complex) ↦
      ∀ (g₀ : Matrix (Fin n) (Fin n) Complex),
        @UpperTheory.Reformulated.B.Qh27.inUJ n ε g₀ →
          ∃ (U : Set (Matrix (Fin n) (Fin n) Complex)) (F : Matrix (Fin n) (Fin n) Complex → Complex),
            And
              (@IsOpen (Matrix (Fin n) (Fin n) Complex)
                (@instTopologicalSpaceMatrix (Fin n) (Fin n) Complex
                  (@UniformSpace.toTopologicalSpace Complex
                    (@PseudoMetricSpace.toUniformSpace Complex
                      (@SeminormedRing.toPseudoMetricSpace Complex
                        (@SeminormedCommRing.toSeminormedRing Complex
                          (@NormedCommRing.toSeminormedCommRing Complex
                            (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))
                U)
              (And
                (@Membership.mem (Matrix (Fin n) (Fin n) Complex) (Set (Matrix (Fin n) (Fin n) Complex))
                  (@Set.instMembership (Matrix (Fin n) (Fin n) Complex)) U g₀)
                (And
                  (@ContDiffOn Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField)
                    (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.normedAddCommGroup (Fin n) (Fin n) Complex (Fin.fintype n) (Fin.fintype n)
                      Complex.instNormedAddCommGroup)
                    (@Matrix.normedSpace Real (Fin n) (Fin n) Complex (Fin.fintype n) (Fin.fintype n)
                      (@NontriviallyNormedField.toNormedField Real
                        (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField))
                      (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
                      (@InnerProductSpace.toNormedSpace Real Complex Real.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
                        instInnerProductSpaceRealComplex))
                    Complex Complex.instNormedAddCommGroup
                    (@InnerProductSpace.toNormedSpace Real Complex Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
                      instInnerProductSpaceRealComplex)
                    (@WithTop.some ENat (@Top.top ENat instTopENat)) F U)
                  (∀ (g : Matrix (Fin n) (Fin n) Complex),
                    @Membership.mem (Matrix (Fin n) (Fin n) Complex) (Set (Matrix (Fin n) (Fin n) Complex))
                        (@Set.instMembership (Matrix (Fin n) (Fin n) Complex)) U g →
                      @UpperTheory.Reformulated.B.Qh27.inUJ n ε g → @Eq Complex (f g) (F g))))

theorem UpperTheory.Reformulated.B.Qh27.smooth_on_group_sum.{u_1} :
    ∀ {n : Nat} {ε : Fin n → Bool} {ι : Type u_1} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) Complex → Complex),
      (∀ (i : ι),
          @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) s i →
            @UpperTheory.Reformulated.B.Qh27.SmoothOnG n ε (f i)) →
        @UpperTheory.Reformulated.B.Qh27.SmoothOnG n ε fun (x : Matrix (Fin n) (Fin n) Complex) ↦ ∑ i ∈ s, f i x := by
  intro n ε ι s f h g₀ hg₀
  letI := @Matrix.normedAddCommGroup (Fin n) (Fin n) Complex _ _ _
  letI := @Matrix.normedSpace Real (Fin n) (Fin n) Complex _ _ _ _ _
  choose! U F hU hmem hF heq using fun i hi ↦ h i hi g₀ hg₀
  refine ⟨⋂ i ∈ s, U i, fun x ↦ ∑ i ∈ s, F i x, isOpen_biInter_finset hU,
    Set.mem_iInter₂.2 hmem, ?_, ?_⟩
  · exact ContDiffOn.sum fun i hi ↦ (hF i hi).mono (Set.biInter_subset_of_mem (Finset.mem_coe.2 hi))
  · intro g hg hgu
    exact Finset.sum_congr rfl fun i hi ↦ heq i hi g (Set.mem_iInter₂.1 hg i hi) hgu
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TmASmSum
noncomputable def UpperTheory.Reformulated.B.Qf26.Jm :
    {n : Nat} → (Fin n → Bool) → Matrix (Fin n) (Fin n) Complex :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @Matrix.diagonal (Fin n) Complex (instDecidableEqFin n) Complex.instZero fun (a : Fin n) ↦
        @ite Complex (@Eq Bool (ε a) Bool.true) (instDecidableEqBool (ε a) Bool.true)
          (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))
          (@Neg.neg Complex Complex.instNeg (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne)))

noncomputable def UpperTheory.Reformulated.B.Qf26.inUJ :
    {n : Nat} → (Fin n → Bool) → Matrix (Fin n) (Fin n) Complex → Prop :=
    fun {n : Nat} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) Complex) ↦
      @Eq (Matrix (Fin n) (Fin n) Complex)
        (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
            Complex.instAddCommMonoid)
          (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
              Complex.instAddCommMonoid)
            (@Matrix.conjTranspose (Fin n) (Fin n) Complex
              (@InvolutiveStar.toStar Complex
                (@StarAddMonoid.toInvolutiveStar Complex
                  (@AddCommMonoid.toAddMonoid Complex
                    (@NonUnitalNonAssocSemiring.toAddCommMonoid Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))))
                  (@StarRing.toStarAddMonoid Complex
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                    Complex.instStarRing)))
              g)
            (@UpperTheory.Reformulated.B.Qf26.Jm n ε))
          g)
        (@UpperTheory.Reformulated.B.Qf26.Jm n ε)

noncomputable def UpperTheory.Reformulated.B.Qf26.SmoothOnG :
    {n : Nat} → (Fin n → Bool) → (Matrix (Fin n) (Fin n) Complex → Complex) → Prop :=
    fun {n : Nat} (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) Complex → Complex) ↦
      ∀ (g₀ : Matrix (Fin n) (Fin n) Complex),
        @UpperTheory.Reformulated.B.Qf26.inUJ n ε g₀ →
          ∃ (U : Set (Matrix (Fin n) (Fin n) Complex)) (F : Matrix (Fin n) (Fin n) Complex → Complex),
            And
              (@IsOpen (Matrix (Fin n) (Fin n) Complex)
                (@instTopologicalSpaceMatrix (Fin n) (Fin n) Complex
                  (@UniformSpace.toTopologicalSpace Complex
                    (@PseudoMetricSpace.toUniformSpace Complex
                      (@SeminormedRing.toPseudoMetricSpace Complex
                        (@SeminormedCommRing.toSeminormedRing Complex
                          (@NormedCommRing.toSeminormedCommRing Complex
                            (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))
                U)
              (And
                (@Membership.mem (Matrix (Fin n) (Fin n) Complex) (Set (Matrix (Fin n) (Fin n) Complex))
                  (@Set.instMembership (Matrix (Fin n) (Fin n) Complex)) U g₀)
                (And
                  (@ContDiffOn Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField)
                    (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.normedAddCommGroup (Fin n) (Fin n) Complex (Fin.fintype n) (Fin.fintype n)
                      Complex.instNormedAddCommGroup)
                    (@Matrix.normedSpace Real (Fin n) (Fin n) Complex (Fin.fintype n) (Fin.fintype n)
                      (@NontriviallyNormedField.toNormedField Real
                        (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField))
                      (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
                      (@InnerProductSpace.toNormedSpace Real Complex Real.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
                        instInnerProductSpaceRealComplex))
                    Complex Complex.instNormedAddCommGroup
                    (@InnerProductSpace.toNormedSpace Real Complex Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
                      instInnerProductSpaceRealComplex)
                    (@WithTop.some ENat (@Top.top ENat instTopENat)) F U)
                  (∀ (g : Matrix (Fin n) (Fin n) Complex),
                    @Membership.mem (Matrix (Fin n) (Fin n) Complex) (Set (Matrix (Fin n) (Fin n) Complex))
                        (@Set.instMembership (Matrix (Fin n) (Fin n) Complex)) U g →
                      @UpperTheory.Reformulated.B.Qf26.inUJ n ε g → @Eq Complex (f g) (F g))))

theorem UpperTheory.Reformulated.B.Qf26.tmA_sm_sum.{u_1} :
    ∀ {n : Nat} {ε : Fin n → Bool} {ι : Type u_1} (s : Finset ι) (F : ι → Matrix (Fin n) (Fin n) Complex → Complex),
      (∀ (i : ι),
          @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) s i →
            @UpperTheory.Reformulated.B.Qf26.SmoothOnG n ε (F i)) →
        @UpperTheory.Reformulated.B.Qf26.SmoothOnG n ε fun (x : Matrix (Fin n) (Fin n) Complex) ↦ ∑ i ∈ s, F i x := by
  intro n ε ι s F h g₀ hg
  classical
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
  choose! U G hUo hUm hG hE using fun i hi => h i hi g₀ hg
  refine ⟨⋂ i ∈ s, U i, fun x => ∑ i ∈ s, G i x, isOpen_biInter_finset hUo, ?_, ?_, ?_⟩
  · exact Set.mem_iInter₂.2 hUm
  · exact ContDiffOn.sum fun i hi => (hG i hi).mono (Set.biInter_subset_of_mem hi)
  · intro g hgU hgJ
    exact Finset.sum_congr rfl fun i hi => hE i hi g (Set.mem_iInter₂.1 hgU i hi) hgJ
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsAnti
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh37.Lp :
    (L : Type) → [Field L] → Type :=
    fun (L : Type) [Field L] ↦ ↥(NumberField.maximalRealSubfield L)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh37.Lsq :
    (R : Type) → [CommRing R] → R → Type :=
    fun (R : Type) [CommRing R] (Δ : R) ↦ QuadraticAlgebra R Δ (0 : R)


open NumberField NumberField.IsCMField in
private theorem UpperTheory.Reformulated.B.Qh37.exists_anti (L : Type) [Field L] [NumberField L] [IsCMField L] :
    ∃ δ : L, δ ≠ 0 ∧ complexConj L δ = -δ := by
  have h : ∃ x : L, complexConj L x ≠ x := by
    by_contra h
    push Not at h
    exact complexConj_ne_one L (AlgEquiv.ext h)
  obtain ⟨x, hx⟩ := h
  refine ⟨x - complexConj L x, sub_ne_zero.mpr hx.symm, ?_⟩
  rw [map_sub, complexConj_apply_apply, neg_sub]

theorem UpperTheory.Reformulated.B.Qh37.globEx :
    ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] [inst_2 : NumberField.IsCMField L],
      ∃ (Δ : UpperTheory.Reformulated.B.Qh37.Lp L) (e : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ ≃+* L),
        (∀ (x : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ),
            (e : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ → L) (Star.star x) =
              (NumberField.IsCMField.complexConj L : L → L) ((e : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ → L) x)) ∧
          (∀ (a : UpperTheory.Reformulated.B.Qh37.Lp L),
              (e : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ → L)
                  ((Algebra.algebraMap (UpperTheory.Reformulated.B.Qh37.Lp L) (UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ) :
                      UpperTheory.Reformulated.B.Qh37.Lp L → UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ)
                    a) =
                (Algebra.algebraMap (UpperTheory.Reformulated.B.Qh37.Lp L) L : UpperTheory.Reformulated.B.Qh37.Lp L → L) a) ∧
            ∀ (σ : UpperTheory.Reformulated.B.Qh37.Lp L →+* ℝ), (σ : UpperTheory.Reformulated.B.Qh37.Lp L → ℝ) Δ < (0 : ℝ) := by
  intro L _ _ _
  obtain ⟨δ, hδ0, hδ⟩ := UpperTheory.Reformulated.B.Qh37.exists_anti L
  have hmem : δ * δ ∈ NumberField.maximalRealSubfield L := by
    rw [← NumberField.IsCMField.complexConj_eq_self_iff, map_mul, hδ, neg_mul_neg]
  let Δ : NumberField.maximalRealSubfield L := ⟨δ * δ, hmem⟩
  have hΔ : algebraMap (NumberField.maximalRealSubfield L) L Δ = δ * δ := rfl
  let f : QuadraticAlgebra (NumberField.maximalRealSubfield L) Δ 0 →ₐ[NumberField.maximalRealSubfield L] L :=
    QuadraticAlgebra.lift ⟨δ, by rw [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one, hΔ]⟩
  have hω : f QuadraticAlgebra.omega = δ := by
    have := (QuadraticAlgebra.lift (R := NumberField.maximalRealSubfield L) (a := Δ) (b := 0)
      (A := L)).symm_apply_apply ⟨δ, by rw [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one, hΔ]⟩
    exact congrArg Subtype.val this
  have hf : ∀ x y, f ⟨x, y⟩ = algebraMap _ L x + algebraMap _ L y * δ := by
    intro x y
    rw [QuadraticAlgebra.mk_eq_add_smul_omega, map_add (f := _), map_smul, AlgHom.commutes, hω,
      Algebra.smul_def]
  have hstar : ∀ z, f (star z) = NumberField.IsCMField.complexConj L (f z) := by
    rintro ⟨x, y⟩
    rw [QuadraticAlgebra.star_mk, hf, hf, map_add (f := _), map_add (f := _), map_mul, map_mul,
      AlgEquiv.commutes, AlgEquiv.commutes, hδ, map_neg, map_zero]
    ring
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨x, y⟩ h
    have h' := hstar ⟨x, y⟩
    rw [h, map_zero, QuadraticAlgebra.star_mk, hf, map_add (f := _), map_mul, map_neg, map_zero] at h'
    rw [hf] at h
    have hx : algebraMap _ L x = 0 := by linear_combination (h + h') / 2
    have hy : algebraMap _ L y * δ = 0 := by linear_combination (h - h') / 2
    have hy' := (mul_eq_zero.mp hy).resolve_right hδ0
    rw [map_eq_zero] at hx hy'
    subst hx hy'
    rfl
  have hsurj : Function.Surjective f := by
    intro z
    have h1 : (z + NumberField.IsCMField.complexConj L z) / 2 ∈
        NumberField.maximalRealSubfield L := by
      rw [← NumberField.IsCMField.complexConj_eq_self_iff, map_div₀, map_add (f := _), map_ofNat,
        NumberField.IsCMField.complexConj_apply_apply, add_comm]
    have h2 : (z - NumberField.IsCMField.complexConj L z) / (2 * δ) ∈
        NumberField.maximalRealSubfield L := by
      rw [← NumberField.IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul, map_ofNat,
        NumberField.IsCMField.complexConj_apply_apply, hδ]
      field_simp
      ring
    refine ⟨⟨⟨_, h1⟩, ⟨_, h2⟩⟩, ?_⟩
    rw [hf]
    change (z + NumberField.IsCMField.complexConj L z) / 2 +
      (z - NumberField.IsCMField.complexConj L z) / (2 * δ) * δ = z
    field_simp
    ring
  refine ⟨Δ, RingEquiv.ofBijective f.toRingHom ⟨hinj, hsurj⟩, hstar, f.commutes, fun σ ↦ ?_⟩
  let φ : L →+* ℂ := NumberField.ComplexEmbedding.lift L (Complex.ofRealHom.comp σ)
  have h1 : φ δ * φ δ = (σ Δ : ℂ) := by
    rw [← map_mul, ← hΔ]
    exact NumberField.ComplexEmbedding.lift_algebraMap_apply L (Complex.ofRealHom.comp σ) Δ
  have h2 : (starRingEnd ℂ) (φ δ) = -φ δ := by
    rw [← NumberField.IsCMField.complexEmbedding_complexConj, hδ, map_neg]
  have h3 : ((Complex.normSq (φ δ) : ℝ) : ℂ) = ((-σ Δ : ℝ) : ℂ) := by
    rw [← Complex.mul_conj, h2, mul_neg, h1, Complex.ofReal_neg]
  have h4 : 0 < Complex.normSq (φ δ) := Complex.normSq_pos.mpr ((map_ne_zero φ).mpr hδ0)
  rw [Complex.ofReal_injective h3] at h4
  exact neg_pos.mp h4
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CovariantDegrees
/-!
# Continuity of the Galois Restriction Homomorphism `rHom`

Condensed from 6,175 lines of `pp.explicit`-dumped auto-extracted obligations
down to ~95 lines of idiomatic Lean 4.
-/

namespace UpperTheory.Reformulated.B.CovariantDegrees

abbrev Om (l : ℕ) [Fact l.Prime] : Type := PadicAlgCl l
abbrev GQ (l : ℕ) [Fact l.Prime] : Type := Om l ≃ₐ[ℚ_[l]] Om l
abbrev G (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] : Type := Ω ≃ₐ[F] Ω

noncomputable def Dec {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) : Subgroup (G F Ω) :=
  A.decompositionSubgroup F

section
variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E]
  [Field Ω] [Algebra E Ω]

noncomputable def jE (j : Ω →+* PadicAlgCl l) : E →+* PadicAlgCl l :=
  j.comp (algebraMap E Ω)

noncomputable def KwF (j : Ω →+* PadicAlgCl l) : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  IntermediateField.adjoin ℚ_[l] (Set.range fun i => jE j (Module.finBasis ℚ E i))

lemma jE_mem (j : Ω →+* PadicAlgCl l) (x : E) : jE j x ∈ KwF (E := E) j := by
  rw [← (Module.finBasis ℚ E).sum_repr x, map_sum]
  refine sum_mem fun i _ => ?_
  rw [Rat.smul_def, map_mul, map_ratCast]
  exact mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)

variable [CharZero Ω] [IsAlgClosure ℚ Ω]

noncomputable def resQ (j : Ω →+* PadicAlgCl l) (σ : GQ l) : Ω ≃ₐ[ℚ] Ω :=
  letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  haveI : IsScalarTower ℚ Ω (PadicAlgCl l) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  (σ.restrictScalars ℚ).restrictNormal Ω

lemma j_resQ (j : Ω →+* PadicAlgCl l) (σ : GQ l) (x : Ω) :
    j (resQ j σ x) = σ (j x) := by
  letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  haveI : IsScalarTower ℚ Ω (PadicAlgCl l) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  exact AlgHom.restrictNormal_commutes (σ.restrictScalars ℚ).toAlgHom Ω x

noncomputable def resE (j : Ω →+* PadicAlgCl l) (σ : GQ l)
    (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) : G E Ω :=
  { resQ j σ with
    commutes' := fun x => j.injective <|
      (j_resQ j σ _).trans ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ (jE_mem j x)) }

lemma j_resE (j : Ω →+* PadicAlgCl l) (σ : GQ l)
    (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) (x : Ω) :
    j (resE j σ hσ x) = σ (j x) := j_resQ j σ x

open Pointwise in
lemma resE_mem {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω}
    (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (σ : GQ l)
    (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) : resE j σ hσ ∈ Dec A := by
  have hn : ∀ x, ‖j (resE j σ hσ x)‖ = ‖j x‖ := fun x => by
    rw [j_resE]; exact (spectralNorm_eq_of_equiv σ (j x)).symm
  refine MulAction.mem_stabilizer_iff.2 (SetLike.ext fun x => ?_)
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hj, hj, ← hn]; simp

noncomputable def rHom [IsAlgClosure E Ω] {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω}
    (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) : (KwF (E := E) j).fixingSubgroup →* Dec (F := E) A where
  toFun σ := ⟨resE j σ.1 σ.2, resE_mem hj σ.1 σ.2⟩
  map_one' := Subtype.ext (AlgEquiv.ext fun x => j.injective (j_resE (E := E) j 1 (Subgroup.one_mem _) x))
  map_mul' σ τ := Subtype.ext (AlgEquiv.ext fun x => j.injective <| by
    rw [j_resE (E := E), Subgroup.coe_mul, AlgEquiv.mul_apply,
      ← j_resE (E := E) j τ.1 τ.2, ← j_resE (E := E) j σ.1 σ.2]; rfl)

theorem continuous_rHom [IsAlgClosure E Ω] {j : Ω →+* PadicAlgCl l} {A : ValuationSubring Ω}
    (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) : Continuous (rHom (E := E) hj) := by
  have h : Continuous ((Dec (F := E) A).subtype.comp (rHom (E := E) hj)) := by
    apply continuous_of_continuousAt_one
    rw [ContinuousAt, map_one]
    intro s hs
    obtain ⟨L, hL, hLs⟩ := (krullTopology_mem_nhds_one_iff E Ω s).1 hs
    let b := Module.finBasis E L
    have hU : ∀ᶠ σ : (KwF (E := E) j).fixingSubgroup in nhds 1,
        ∀ i, σ.1 (j (b i)) = j (b i) := by
      refine Filter.eventually_all.2 fun i => ?_
      have ho := (stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) (j (b i))).preimage
        (continuous_subtype_val (p := fun σ => σ ∈ (KwF (E := E) j).fixingSubgroup))
      exact ho.mem_nhds (Subgroup.one_mem (MulAction.stabilizer _ _))
    refine hU.mono fun σ hσ => hLs ?_
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
    have key : (resE j σ.1 σ.2).toLinearMap ∘ₗ L.val.toLinearMap = L.val.toLinearMap :=
      b.ext fun i => j.injective ((j_resE j σ.1 σ.2 (b i)).trans (hσ i))
    exact LinearMap.congr_fun key ⟨x, hx⟩
  exact continuous_induced_rng.2 h

end
end UpperTheory.Reformulated.B.CovariantDegrees
end

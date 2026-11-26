module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelThetaTransformationLawMul
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInvariantIntegralMatrixMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergOperatorRationalPointLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergOperatorRationalPointLaws
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW

theorem heisS_exists_den {κ ι : Type} [Fintype κ] [Fintype ι] (a : Matrix κ ι ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ k i, IsIntegral ℤ ((D : ℚ) * a k i) := by
  classical
  refine ⟨∏ p : κ × ι, (a p.1 p.2).den, Finset.prod_pos fun p _ => (a p.1 p.2).den_pos, ?_⟩
  intro k i
  obtain ⟨c, hc⟩ : (a k i).den ∣ ∏ p : κ × ι, (a p.1 p.2).den :=
    Finset.dvd_prod_of_mem (fun p : κ × ι => (a p.1 p.2).den) (Finset.mem_univ (k, i))
  have : ((∏ p : κ × ι, (a p.1 p.2).den : ℕ) : ℚ) * a k i
      = algebraMap ℤ ℚ ((c : ℤ) * (a k i).num) := by
    rw [hc]
    have h := Rat.mul_den_eq_num (a k i)
    simp only [eq_intCast, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    rw [← h]; ring
  rw [this]
  exact isIntegral_algebraMap

theorem isSB_mul_char {κ ι : Type} [Fintype κ] [Fintype ι] (a b : Matrix κ ι ℚ)
    (ψ : Matrix κ ι ℚ → ℂ) (h : IsSB ψ) :
    IsSB (fun x : Matrix κ ι ℚ => ψ x *
      cexp (Real.pi * I * ((∑ k, (2 * (x k ⬝ᵥ a k) - a k ⬝ᵥ b k) : ℚ) : ℂ))) := by
  obtain ⟨R, hR, hs, hp⟩ := h
  obtain ⟨D, hD, ha⟩ := heisS_exists_den a
  have hn : ∀ n : ℕ, IsIntegral ℤ (n : ℚ) := fun n => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℚ) (x := (n : ℤ)))
  refine ⟨R * D, Nat.mul_pos hR hD, ?_, ?_⟩
  · intro x hx k i
    have h1 := hs x (left_ne_zero_of_mul hx) k i
    have : (((R * D : ℕ) : ℚ) • x) k i = (D : ℚ) * ((R : ℚ) • x) k i := by
      simp only [Matrix.smul_apply, smul_eq_mul, Nat.cast_mul]; ring
    rw [this]; exact (hn D).mul h1
  · intro x y hy
    have e1 : x + ((R * D : ℕ) : ℚ) • y = x + (R : ℚ) • ((D : ℚ) • y) := by
      rw [smul_smul, Nat.cast_mul]
    have hy' : IntM ((D : ℚ) • y) := fun k i => by
      simpa using (hn D).mul (hy k i)
    have hint : IsIntegral ℤ (∑ k, ∑ i, (R : ℚ) * (y k i * ((D : ℚ) * a k i))) :=
      IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun i _ => (hn R).mul ((hy k i).mul (ha k i))
    obtain ⟨n, hn'⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    have e2 : (∑ k, (2 * ((x + ((R * D : ℕ) : ℚ) • y) k ⬝ᵥ a k) - a k ⬝ᵥ b k) : ℚ)
        = (∑ k, (2 * (x k ⬝ᵥ a k) - a k ⬝ᵥ b k) : ℚ) + 2 * n := by
      have : (n : ℚ) = ∑ k, ∑ i, (R : ℚ) * (y k i * ((D : ℚ) * a k i)) := by simpa using hn'
      rw [this, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : (x + ((R * D : ℕ) : ℚ) • y) k ⬝ᵥ a k
          = x k ⬝ᵥ a k + ∑ i, (R : ℚ) * (y k i * ((D : ℚ) * a k i)) := by
        simp only [dotProduct, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Nat.cast_mul]; ring
      rw [this]; ring
    simp only []
    rw [e2, e1, hp x _ hy']
    congr 1
    rw [Rat.cast_add, mul_add, Complex.exp_add]
    have : (π : ℂ) * I * ((2 * n : ℚ) : ℂ) = n * (2 * π * I) := by push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem heisS_laws : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (a b : Matrix κ ι ℚ) (φ : Matrix κ ι ℚ → ℂ), IsSB φ → IsSB (heisS a b φ) ∧ (∀ τ ∈ Siegel ι, ∀ ζ, thS (heisS a b φ) τ ζ = cexp (π * I * ∑ k, (qv (b k) ⬝ᵥ τ *ᵥ qv (b k) + 2 * (qv (b k) ⬝ᵥ ζ k) + qv (a k) ⬝ᵥ qv (b k))) * thS φ τ (fun k => ζ k + qv (a k) + τ *ᵥ qv (b k))) ∧ (∀ a' b', heisS a b (heisS a' b' φ) = cexp (π * I * ((∑ k, (a k ⬝ᵥ b' k - a' k ⬝ᵥ b k) : ℚ) : ℂ)) • heisS (a + a') (b + b') φ) ∧ heisS 0 0 φ = φ ∧ ∀ ψ, IsSB ψ → ip (heisS a b φ) (heisS a b ψ) = ip φ ψ := by
  intro κ ι _ _ _ a b φ hφ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact isSB_mul_char a b _ ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι φ φ hφ hφ).2.2.2.2.2.2.2 b).1
  · intro τ hτ ζ
    unfold thS
    rw [← tsum_mul_left, ← (Equiv.addRight b).tsum_eq]
    refine tsum_congr fun y => ?_
    simp only [Equiv.coe_addRight, heisS, add_sub_cancel_right]
    rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
    congr 2
    rw [← mul_add, ← mul_add, Rat.cast_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have hq : ∀ u v : ι → ℚ, ((u ⬝ᵥ v : ℚ) : ℂ) = qv u ⬝ᵥ qv v := fun u v => by
      simp [dotProduct, qv]
    have hadd : qv ((y + b) k) = qv (y k) + qv (b k) := by
      ext i; simp [qv]
    have hsym : qv (b k) ⬝ᵥ τ *ᵥ qv (y k) = qv (y k) ⬝ᵥ τ *ᵥ qv (b k) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hτ.1.eq, dotProduct_comm]
    rw [Rat.cast_sub, Rat.cast_mul, hq, hq, hadd]
    simp only [add_dotProduct, dotProduct_add, mulVec_add, hsym, dotProduct_comm (qv (b k)) (qv (a k))]
    push_cast; ring
  · intro a' b'
    funext x
    simp only [heisS, Pi.smul_apply, smul_eq_mul]
    rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, sub_sub]
    congr 2
    rw [← mul_add, ← mul_add, ← Rat.cast_add, ← Rat.cast_add, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.add_apply, Matrix.sub_apply]; ring
  · funext x
    simp [heisS, dotProduct]
  · intro ψ hψ
    have h1 : IsSB (fun x : Matrix κ ι ℚ => conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι ψ ψ hψ hψ).2.2.2.1
    have h2 := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι φ _ hφ h1).2.2.1
    have h3 := ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι _ _ h2 h2).2.2.2.2.2.2.2 b).2
    unfold ip
    refine Eq.trans ?_ h3
    congr 1
    funext x
    simp only [heisS, Pi.mul_apply, map_mul]
    rw [← Complex.exp_conj, mul_mul_mul_comm, ← Complex.exp_add]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ratCast]
    simp

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergOperatorRationalPointLawsStatement
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperatorRationalPoint_laws : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (a b : Matrix κ ι ℚ) (φ : Matrix κ ι ℚ → ℂ), IsSB φ → IsSB (heisS a b φ) ∧ (∀ τ ∈ Siegel ι, ∀ ζ, thS (heisS a b φ) τ ζ = cexp (π * I * ∑ k, (qv (b k) ⬝ᵥ τ *ᵥ qv (b k) + 2 * (qv (b k) ⬝ᵥ ζ k) + qv (a k) ⬝ᵥ qv (b k))) * thS φ τ (fun k => ζ k + qv (a k) + τ *ᵥ qv (b k))) ∧ (∀ a' b', heisS a b (heisS a' b' φ) = cexp (π * I * ((∑ k, (a k ⬝ᵥ b' k - a' k ⬝ᵥ b k) : ℚ) : ℂ)) • heisS (a + a') (b + b') φ) ∧ heisS 0 0 φ = φ ∧ ∀ ψ, IsSB ψ → ip (heisS a b φ) (heisS a b ψ) = ip φ ψ := by
  first | exact @GlobalTheory.SW.heisS_laws | exact GlobalTheory.SW.heisS_laws | (intros; apply GlobalTheory.SW.heisS_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatIntegralGaussianShapeRootOfUnityPh
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatIntegralGaussianShapeRootOfUnityPh
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase

private theorem quotient_out_sub_mem' {G : Type} [AddCommGroup G] (N : AddSubgroup G) (x : G) :
    (x : G ⧸ N).out - x ∈ N := by
  have h := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (x : G ⧸ N)).symm
  rwa [neg_add_eq_sub] at h


open scoped Classical in
open Classical in
theorem ph_finsum_quotient {A : Type} [AddCommGroup A] (P S : AddSubgroup A) (φ f : A → ℂ) (c : ℂ) (a : A)
    (hper : ∀ x, ∀ y ∈ P, φ (x + y) = φ x)
    (hfin : (Function.support fun q : A ⧸ P => φ q.out).Finite)
    (hc : Ph c) (hf : Quad S f) (hφ : ∀ x, φ x = if x - a ∈ S then c * f (x - a) else 0) :
    Ph (∑ᶠ q : A ⧸ P, φ q.out) := by
  by_cases hc0 : c = 0
  · have h0 : ∀ x, φ x = 0 := fun x => by rw [hφ x]; split_ifs <;> simp [hc0]
    simp only [h0, finsum_zero]
    exact ph_zero

  have hfper : ∀ s ∈ S, ∀ t ∈ S, t ∈ P → f (s + t) = f s := by
    intro s hs t htS htP
    have h1 := hφ (a + (s + t))
    have h2 := hφ (a + s)
    rw [add_sub_cancel_left, if_pos (S.add_mem hs htS)] at h1
    rw [add_sub_cancel_left, if_pos hs] at h2
    have h3 : φ (a + (s + t)) = φ (a + s) := by rw [← add_assoc]; exact hper _ t htP
    exact mul_left_cancel₀ hc0 (h1.symm.trans (h3.trans h2))

  let ψ : S →+ A ⧸ P := (QuotientAddGroup.mk' P).comp S.subtype
  have hker : ∀ u : S, u ∈ ψ.ker ↔ (u : A) ∈ P := fun u => by
    simp [ψ, AddMonoidHom.mem_ker, QuotientAddGroup.eq_zero_iff]
  let ι' : S ⧸ ψ.ker →+ A ⧸ P := QuotientAddGroup.kerLift ψ
  have hι : Function.Injective ι' := QuotientAddGroup.kerLift_injective ψ
  let j : S ⧸ ψ.ker → A ⧸ P := fun m => (a : A ⧸ P) + ι' m
  have hj : Function.Injective j := fun m m' h => hι (add_left_cancel h)
  have hjmk : ∀ u : S, j (u : S ⧸ ψ.ker) = ((a + u : A) : A ⧸ P) := fun u => by
    simp [j, ι', ψ]
  let fb : S ⧸ ψ.ker → ℂ := fun m => f (m.out : A)
  have hfb : ∀ u : S, fb (u : S ⧸ ψ.ker) = f u := by
    intro u
    have hk := (hker _).mp (quotient_out_sub_mem' ψ.ker u)
    have e : (((u : S ⧸ ψ.ker).out : S) : A) = u + (((u : S ⧸ ψ.ker).out - u : S) : A) := by simp
    show f (((u : S ⧸ ψ.ker).out : S) : A) = f u
    rw [e]
    exact hfper _ u.2 _ ((u : S ⧸ ψ.ker).out - u).2 hk
  have hval : ∀ m, φ (j m).out = c * fb m := by
    intro m
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective m
    rw [hjmk, hfb]
    have hk := quotient_out_sub_mem' P (a + (u : A))
    have e : ((a + (u : A) : A) : A ⧸ P).out =
        (a + u) + (((a + (u : A) : A) : A ⧸ P).out - (a + u)) := by abel
    rw [e, hper _ _ hk, hφ, add_sub_cancel_left, if_pos u.2]
  have hfbne : ∀ m, fb m ≠ 0 := fun m h => by
    have h1 := (hf.1 _ (m.out).2).norm_eq_one
    simp [fb] at h
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hrange : Set.range j ⊆ Function.support (fun q : A ⧸ P => φ q.out) := by
    rintro _ ⟨m, rfl⟩
    rw [Function.mem_support, hval]
    exact mul_ne_zero hc0 (hfbne m)
  have : Finite (S ⧸ ψ.ker) := by
    have := hfin.to_subtype
    exact Finite.of_injective
      (fun m => (⟨j m, hrange ⟨m, rfl⟩⟩ : Function.support (fun q : A ⧸ P => φ q.out)))
      (fun m m' h => hj (congrArg Subtype.val h))
  haveI := Fintype.ofFinite (S ⧸ ψ.ker)

  have hsupp : Function.support (fun q : A ⧸ P => φ q.out) ⊆ Set.range j := by
    intro q hq
    rw [Function.mem_support, hφ] at hq
    split_ifs at hq with hmem
    · refine ⟨((⟨q.out - a, hmem⟩ : S) : S ⧸ ψ.ker), ?_⟩
      rw [hjmk]
      simp
    · exact absurd rfl hq
  have hsum : ∑ᶠ q : A ⧸ P, φ q.out = c * ∑ m : S ⧸ ψ.ker, fb m := by
    rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ Set.univ (Set.range j)
        (fun q hq => ⟨fun _ => hsupp hq, fun _ => Set.mem_univ q⟩), finsum_mem_range hj,
      finsum_eq_sum_of_fintype, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => hval m
  rw [hsum]
  refine Ph.mul hc (GlobalTheory.T.isZeroOrPosMulRootOfUnity_finite_gaussSum (S ⧸ ψ.ker) fb ⟨fun x _ => hf.1 _ (x.out).2, fun x _ y _ z _ => ?_⟩)
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective y
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
  have h0 : fb 0 = f 0 := by simpa using hfb 0
  have e2 : ∀ x y : S, ((x : S ⧸ ψ.ker) + y) = ((x + y : S) : S ⧸ ψ.ker) := fun x y => rfl
  rw [e2 u v, e2 (u + v) w, e2 v w, e2 u w, h0]
  simp only [hfb]
  simpa using hf.2 _ u.2 _ v.2 _ w.2

theorem ph_haar_of_shape : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι],
    ∀ φ : Matrix κ ι ℚ → ℂ, Shape φ → Ph (haar φ) := by
  intro κ ι _ _ _ φ hφ
  obtain ⟨hsb, c, a, S, f, hc, hf, hφx⟩ := hφ
  have hR := hsb.choose_spec
  unfold haar
  rw [dite_eq_left hsb]
  unfold haarAt
  refine Ph.mul ?_ (ph_finsum_quotient (perSub ℚ κ ι hsb.choose) S φ f c a
    (GlobalTheory.SW.HaarLevel.periodic hR.2) (GlobalTheory.SW.HaarLevel.finite_support hR.1 hR.2) hc hf hφx)

  have h := GlobalTheory.T.complex_phase_calculus_rootOfUnity.2.2.1
    (((hsb.choose : ℝ) ^ (Module.finrank ℚ ℚ * (Fintype.card κ * Fintype.card ι)))⁻¹)
  convert h using 1
  push_cast
  rfl

end GlobalTheory.Phase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatIntegralGaussianShapeRootOfUnityPhStatement
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhatIntegral_gaussianShape_rootOfUnityPhase : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], ∀ φ : Matrix κ ι ℚ → ℂ, Shape φ → Ph (haar φ) := by
  first | exact @GlobalTheory.Phase.ph_haar_of_shape | exact GlobalTheory.Phase.ph_haar_of_shape | (intros; apply GlobalTheory.Phase.ph_haar_of_shape <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsCosetQuadraticPhaseTestFunctionConjCharacterMu
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsCosetQuadraticPhaseTestFunctionConjCharacterMu
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.ShapeOps

theorem mu_mul {a b : ℂ} (ha : IsMu a) (hb : IsMu b) : IsMu (a * b) := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨n, hn, hb⟩ := hb
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  rw [mul_pow, pow_mul, ha, mul_comm m n, pow_mul, hb]; simp

theorem mu_inv {a : ℂ} (ha : IsMu a) : IsMu a⁻¹ := by
  obtain ⟨m, hm, ha⟩ := ha
  exact ⟨m, hm, by rw [inv_pow, ha, inv_one]⟩

theorem mu_conj {a : ℂ} (ha : IsMu a) : IsMu (conj a) := by
  obtain ⟨m, hm, ha⟩ := ha
  exact ⟨m, hm, by rw [← map_pow, ha, map_one]⟩

theorem mu_ne {a : ℂ} (ha : IsMu a) : a ≠ 0 := by
  obtain ⟨m, hm, ha⟩ := ha
  rintro rfl
  rw [zero_pow hm.ne'] at ha
  exact zero_ne_one ha

theorem ph_mul {a b : ℂ} (ha : Ph a) (hb : Ph b) : Ph (a * b) := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨n, hn, hb⟩ := hb
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  rw [norm_mul, Complex.ofReal_mul, mul_pow, mul_pow, pow_mul a, ha, ← pow_mul, mul_comm m n, pow_mul b, hb,
    ← pow_mul]

theorem ph_conj {a : ℂ} (ha : Ph a) : Ph (conj a) := by
  obtain ⟨m, hm, ha⟩ := ha
  refine ⟨m, hm, ?_⟩
  rw [← map_pow, ha, map_pow, Complex.conj_ofReal, Complex.norm_conj]

section Quad

variable {M : Type} [AddCommGroup M]

theorem quad_mul {S : AddSubgroup M} {f g : M → ℂ} (hf : Quad S f) (hg : Quad S g) :
    Quad S (fun x => f x * g x) := by
  refine ⟨fun x hx => mu_mul (hf.1 x hx) (hg.1 x hx), fun x hx y hy z hz => ?_⟩
  have h1 := hf.2 x hx y hy z hz
  have h2 := hg.2 x hx y hy z hz
  calc _ = (f (x + y + z) * f x * f y * f z) * (g (x + y + z) * g x * g y * g z) := by ring
    _ = _ := by rw [h1, h2]; ring

theorem quad_conj {S : AddSubgroup M} {f : M → ℂ} (hf : Quad S f) : Quad S (fun x => conj (f x)) := by
  refine ⟨fun x hx => mu_conj (hf.1 x hx), fun x hx y hy z hz => ?_⟩
  have h1 := congrArg conj (hf.2 x hx y hy z hz)
  simpa only [map_mul] using h1

theorem quad_mono {S S' : AddSubgroup M} {f : M → ℂ} (h : S' ≤ S) (hf : Quad S f) : Quad S' f :=
  ⟨fun x hx => hf.1 x (h hx), fun x hx y hy z hz => hf.2 x (h hx) y (h hy) z (h hz)⟩

theorem quad_affine {S : AddSubgroup M} {h : M → ℂ} (h1 : ∀ x ∈ S, IsMu (h x))
    (h2 : ∀ x ∈ S, ∀ y ∈ S, h (x + y) * h 0 = h x * h y) : Quad S h := by
  refine ⟨h1, fun x hx y hy z hz => ?_⟩
  have h0 : h 0 ≠ 0 := mu_ne (h1 0 S.zero_mem)
  have e1 : h (x + y) = h x * h y / h 0 := by rw [eq_div_iff h0]; exact h2 x hx y hy
  have e2 : h (y + z) = h y * h z / h 0 := by rw [eq_div_iff h0]; exact h2 y hy z hz
  have e3 : h (x + z) = h x * h z / h 0 := by rw [eq_div_iff h0]; exact h2 x hx z hz
  have e4 : h (x + y + z) = h (x + y) * h z / h 0 := by
    rw [eq_div_iff h0]; exact h2 _ (S.add_mem hx hy) z hz
  rw [e4, e1, e2, e3]
  field_simp

theorem quad_shift {S : AddSubgroup M} {f : M → ℂ} (hf : Quad S f) {d : M} (hd : d ∈ S) :
    Quad S (fun x => f (x + d)) := by
  have hq : Quad S (fun x => f (x + d) * (f x)⁻¹) := by
    refine quad_affine (fun x hx => mu_mul (hf.1 _ (S.add_mem hx hd)) (mu_inv (hf.1 x hx)))
      fun x hx y hy => ?_
    have h := hf.2 x hx y hy d hd
    have n0 := mu_ne (hf.1 0 S.zero_mem)
    have nx := mu_ne (hf.1 x hx)
    have ny := mu_ne (hf.1 y hy)
    have nxy := mu_ne (hf.1 _ (S.add_mem hx hy))
    simp only [zero_add]
    field_simp
    linear_combination h
  have hm := quad_mul hf hq
  have key : ∀ x ∈ S, f (x + d) = f x * (f (x + d) * (f x)⁻¹) := fun x hx => by
    have nx := mu_ne (hf.1 x hx)
    field_simp
  refine ⟨fun x hx => hf.1 _ (S.add_mem hx hd), fun x hx y hy z hz => ?_⟩
  have := hm.2 x hx y hy z hz
  simp only at this ⊢
  rw [← key _ hx, ← key _ hy, ← key _ hz, ← key _ S.zero_mem, ← key _ (S.add_mem hx hy),
    ← key _ (S.add_mem hy hz), ← key _ (S.add_mem hx hz),
    ← key _ (S.add_mem (S.add_mem hx hy) hz)] at this
  exact this

end Quad

variable {κ ι : Type} [Fintype κ] [Fintype ι]

theorem chr_add (y x x' : Matrix κ ι ℚ) : chr y (x + x') = chr y x * chr y x' := by
  unfold chr
  rw [← Complex.exp_add, ← mul_add, ← Rat.cast_add, ← Finset.sum_add_distrib]
  congr 3
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← add_dotProduct]; rfl

theorem mu_exp (q : ℚ) : IsMu (cexp (2 * Real.pi * I * (q : ℂ))) := by
  refine ⟨q.den, q.den_pos, ?_⟩
  rw [← Complex.exp_nat_mul]
  have h : ((q.den : ℚ) * q) = q.num := Rat.den_mul_eq_num q
  have h' : ((q.den : ℂ) * q) = q.num := by exact_mod_cast congrArg (fun t : ℚ => (t : ℂ)) h
  rw [show (q.den : ℂ) * (2 * Real.pi * I * (q : ℂ)) = ((q.den : ℂ) * q) * (2 * Real.pi * I) by ring, h']
  exact Complex.exp_int_mul_two_pi_mul_I _

theorem intM_nsmul (N : ℕ) {z : Matrix κ ι ℚ} (hz : IntM z) : IntM ((N : ℚ) • z) := fun k i => by
  rw [Matrix.smul_apply, smul_eq_mul]
  exact (isIntegral_algebraMap (R := ℤ) (x := (N : ℤ)) |>.mul (hz k i) : IsIntegral ℤ (_ * _))

theorem exists_den (y : Matrix κ ι ℚ) : ∃ N : ℕ, 0 < N ∧ IntM ((N : ℚ) • y) := by
  classical
  refine ⟨∏ p : κ × ι, (y p.1 p.2).den, Finset.prod_pos fun p _ => Rat.den_pos _, fun k i => ?_⟩
  obtain ⟨c, hc⟩ : (y k i).den ∣ ∏ p : κ × ι, (y p.1 p.2).den :=
    Finset.dvd_prod_of_mem (fun p : κ × ι => (y p.1 p.2).den) (Finset.mem_univ (k, i))
  rw [hc, Matrix.smul_apply, smul_eq_mul]
  have : (((y k i).den * c : ℕ) : ℚ) * y k i = algebraMap ℤ ℚ (c * (y k i).num) := by
    have h := Rat.den_mul_eq_num (y k i)
    simp only [eq_intCast]
    push_cast
    rw [← h]; ring
  rw [this]
  exact isIntegral_algebraMap

theorem chr_eq_one {y z : Matrix κ ι ℚ} {N : ℕ} (hy : IntM ((N : ℚ) • y)) (hz : IntM z) :
    chr y ((N : ℚ) • z) = 1 := by
  have h : IsIntegral ℤ (∑ k, ((N : ℚ) • z) k ⬝ᵥ y k) := by
    refine IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun i _ => ?_
    have := (hz k i).mul (hy k i)
    rw [Matrix.smul_apply, smul_eq_mul] at this
    rw [Matrix.smul_apply, smul_eq_mul]
    convert this using 1; ring
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  unfold chr
  rw [← hn, mul_comm]
  simp only [eq_intCast, Rat.cast_intCast]
  exact Complex.exp_int_mul_two_pi_mul_I _

theorem isSB_mul_chr {φ : Matrix κ ι ℚ → ℂ} (h : IsSB φ) (y : Matrix κ ι ℚ) :
    IsSB (fun x => φ x * chr y x) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  obtain ⟨N, hN, hy⟩ := exists_den y
  refine ⟨N * R, Nat.mul_pos hN hR, fun x hx => ?_, fun x z hz => ?_⟩
  · have := intM_nsmul N (h1 x (left_ne_zero_of_mul hx))
    rwa [smul_smul, ← Nat.cast_mul] at this
  · have e1 : ((N * R : ℕ) : ℚ) • z = (R : ℚ) • ((N : ℚ) • z) := by
      rw [smul_smul, Nat.cast_mul, mul_comm]
    have e2 : ((N * R : ℕ) : ℚ) • z = (N : ℚ) • ((R : ℚ) • z) := by
      rw [smul_smul, Nat.cast_mul]
    have a1 : φ (x + ((N * R : ℕ) : ℚ) • z) = φ x := by rw [e1]; exact h2 x _ (intM_nsmul N hz)
    have a2 : chr y (x + ((N * R : ℕ) : ℚ) • z) = chr y x := by
      rw [chr_add, e2, chr_eq_one hy (intM_nsmul R hz), mul_one]
    simp only [a1, a2]

theorem shape_conj {φ : Matrix κ ι ℚ → ℂ} (h : Shape φ) : Shape (fun x => conj (φ x)) := by
  obtain ⟨hs, c, a, S, f, hc, hf, hφ⟩ := h
  refine ⟨(isSB_algebra_haar_linear ℚ κ ι φ φ hs hs).2.2.2.1, conj c, a, S, _, ph_conj hc, quad_conj hf,
    fun x => ?_⟩
  simp only [hφ x]
  split_ifs <;> simp

theorem shape_chr {φ : Matrix κ ι ℚ → ℂ} (h : Shape φ) (y : Matrix κ ι ℚ) :
    Shape (fun x => φ x * chr y x) := by
  obtain ⟨hs, c, a, S, f, hc, hf, hφ⟩ := h
  have hq : Quad S (fun x => chr y (x + a)) := by
    refine quad_affine (fun x _ => mu_exp _) fun x _ x' _ => ?_
    simp only [← chr_add]
    congr 1; abel
  refine ⟨isSB_mul_chr hs y, c, a, S, _, hc, quad_mul hf hq, fun x => ?_⟩
  simp only [hφ x, sub_add_cancel]
  split_ifs <;> simp [mul_assoc]

theorem shape_mul {φ ψ : Matrix κ ι ℚ → ℂ} (h : Shape φ) (h' : Shape ψ) :
    Shape (fun x => φ x * ψ x) := by
  obtain ⟨hs, c, a, S, f, hc, hf, hφ⟩ := h
  obtain ⟨hs', c', a', S', f', hc', hf', hψ⟩ := h'
  refine ⟨(isSB_algebra_haar_linear ℚ κ ι φ ψ hs hs').2.2.1, ?_⟩
  by_cases hb : ∃ b, b - a ∈ S ∧ b - a' ∈ S'
  · obtain ⟨b, hb, hb'⟩ := hb
    refine ⟨c * c', b, S ⊓ S', _, ph_mul hc hc',
      quad_mul (quad_mono inf_le_left (quad_shift hf hb)) (quad_mono inf_le_right (quad_shift hf' hb')),
      fun x => ?_⟩
    have i1 : x - a ∈ S ↔ x - b ∈ S := by
      rw [show x - a = x - b + (b - a) by abel]; exact S.add_mem_cancel_right hb
    have i2 : x - a' ∈ S' ↔ x - b ∈ S' := by
      rw [show x - a' = x - b + (b - a') by abel]; exact S'.add_mem_cancel_right hb'
    simp only [hφ x, hψ x, sub_add_sub_cancel]
    by_cases p : x - b ∈ S
    · by_cases p' : x - b ∈ S'
      · rw [if_pos (i1.2 p), if_pos (i2.2 p'), if_pos (AddSubgroup.mem_inf.2 ⟨p, p'⟩)]; ring
      · rw [if_neg (mt i2.1 p'), mul_zero, if_neg (fun q => p' (AddSubgroup.mem_inf.1 q).2)]
    · rw [if_neg (mt i1.1 p), zero_mul, if_neg (fun q => p (AddSubgroup.mem_inf.1 q).1)]
  · refine ⟨0, 0, ⊥, fun _ => 1, ph_zero, ⟨fun _ _ => isMu_one, fun _ _ _ _ _ _ => rfl⟩, fun x => ?_⟩
    have : φ x * ψ x = 0 := by
      rw [hφ x, hψ x]
      by_cases p : x - a ∈ S
      · have p' : x - a' ∉ S' := fun p' => hb ⟨x, p, p'⟩
        simp [p']
      · simp [p]
    simp [this]

end GlobalTheory.Phase.ShapeOps

theorem GlobalTheory.Phase.shape_conj_chr_mul : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], ∀ φ : Matrix κ ι ℚ → ℂ, Shape φ → Shape (fun x => conj (φ x)) ∧ (∀ y, Shape (fun x => φ x * chr y x)) ∧ ∀ ψ, Shape ψ → Shape (fun x => φ x * ψ x) :=
  fun _ _ _ _ _ _ h => ⟨ShapeOps.shape_conj h, ShapeOps.shape_chr h, fun _ h' => ShapeOps.shape_mul h h'⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsCosetQuadraticPhaseTestFunctionConjCharacterMuStatement
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCosetQuadraticPhaseTestFunction_conj_character_mul : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], ∀ φ : Matrix κ ι ℚ → ℂ, Shape φ → Shape (fun x => conj (φ x)) ∧ (∀ y, Shape (fun x => φ x * chr y x)) ∧ ∀ ψ, Shape ψ → Shape (fun x => φ x * ψ x) := by
  first | exact @GlobalTheory.Phase.shape_conj_chr_mul | exact GlobalTheory.Phase.shape_conj_chr_mul | (intros; apply GlobalTheory.Phase.shape_conj_chr_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelThetaTransformationSiegelParabolic
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelThetaTransformationSiegelParabolic
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.Parab

noncomputable def parChar {κ ι : Type} [Fintype κ] [Fintype ι] (S : Matrix ι ι ℚ)
    (x : Matrix κ ι ℚ) : ℂ :=
  cexp (-(Real.pi * I * ((∑ k, x k ⬝ᵥ S *ᵥ x k : ℚ) : ℂ)))

open Matrix Complex in
open scoped ComplexConjugate Real in
lemma _root_.GlobalTheory.SW.Parab.parChar_mul_conj {κ ι : Type} [Fintype κ] [Fintype ι]
    (S : Matrix ι ι ℚ) (x : Matrix κ ι ℚ) :
    _root_.GlobalTheory.SW.Parab.parChar S x * conj (_root_.GlobalTheory.SW.Parab.parChar S x) = 1 := by
  unfold _root_.GlobalTheory.SW.Parab.parChar
  rw [← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  simp [Complex.conj_I, map_ratCast]

open Matrix Complex in
open scoped ComplexConjugate Real in
private lemma exists_pos_nat_mul_eq_int {ι : Type} [Fintype ι] (S : Matrix ι ι ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ T : Matrix ι ι ℤ, ∀ i j, (T i j : ℚ) = d * S i j := by
  refine ⟨∏ i, ∏ j, (S i j).den, Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => (S i j).den_pos, ?_⟩
  have key : ∀ i j, ∃ t : ℤ, (t : ℚ) = ((∏ i, ∏ j, (S i j).den : ℕ) : ℚ) * S i j := by
    intro i j
    obtain ⟨m, hm⟩ : (S i j).den ∣ ∏ i, ∏ j, (S i j).den :=
      (Finset.dvd_prod_of_mem (fun j => (S i j).den) (Finset.mem_univ j)).trans
        (Finset.dvd_prod_of_mem (fun i => ∏ j, (S i j).den) (Finset.mem_univ i))
    refine ⟨m * (S i j).num, ?_⟩
    rw [hm]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  choose T hT using key
  exact ⟨T, hT⟩

open Matrix Complex in
open scoped ComplexConjugate Real in
private lemma isIntegral_int_rat_iff_exists_int (q : ℚ) : IsIntegral ℤ q ↔ ∃ n : ℤ, (n : ℚ) = q := by
  rw [IsIntegrallyClosed.isIntegral_iff]
  simp

open Matrix Complex in
open scoped ComplexConjugate Real in
theorem _root_.GlobalTheory.SW.Parab.isSB_parChar_mul {κ ι : Type} [Fintype κ] [Fintype ι] (S : Matrix ι ι ℚ)
    (φ : Matrix κ ι ℚ → ℂ) (h : _root_.GlobalTheory.SW.IsSB φ) :
    _root_.GlobalTheory.SW.IsSB fun x => _root_.GlobalTheory.SW.Parab.parChar S x * φ x := by
  obtain ⟨R, hR, hsupp, hper⟩ := h
  obtain ⟨d, hd, T, hT⟩ := exists_pos_nat_mul_eq_int S
  refine ⟨2 * d * R, by positivity, ?_, ?_⟩
  · intro x hx
    have hint := hsupp x (right_ne_zero_of_mul hx)
    intro k i
    obtain ⟨n, hn⟩ := (isIntegral_int_rat_iff_exists_int _).1 (hint k i)
    refine (isIntegral_int_rat_iff_exists_int _).2 ⟨2 * d * n, ?_⟩
    simp only [Matrix.smul_apply, smul_eq_mul] at hn ⊢
    push_cast at hn ⊢
    linear_combination (2 * d : ℚ) * hn

  · intro x y hy
    have hy' : _root_.GlobalTheory.SW.IntM (((2 * d : ℕ) : ℚ) • y) := by
      intro k i
      obtain ⟨n, hn⟩ := (isIntegral_int_rat_iff_exists_int _).1 (hy k i)
      refine (isIntegral_int_rat_iff_exists_int _).2 ⟨2 * d * n, ?_⟩
      simp only [Matrix.smul_apply, smul_eq_mul]
      push_cast
      rw [hn]
    have hφ : φ (x + ((2 * d * R : ℕ) : ℚ) • y) = φ x := by
      rw [← hper x _ hy', smul_smul]
      push_cast
      ring_nf
    simp only
    rw [hφ]
    by_cases h0 : φ x = 0
    · simp [h0]
    congr 1
    have hU : ∀ k i, ∃ n : ℤ, (n : ℚ) = R * x k i := fun k i => by
      simpa using (isIntegral_int_rat_iff_exists_int _).1 (hsupp x h0 k i)
    choose U hU using hU
    have hY : ∀ k i, ∃ n : ℤ, (n : ℚ) = y k i := fun k i =>
      (isIntegral_int_rat_iff_exists_int _).1 (hy k i)
    choose Y hY using hY
    have hQ : ∑ k, (x + ((2 * d * R : ℕ) : ℚ) • y) k ⬝ᵥ S *ᵥ (x + ((2 * d * R : ℕ) : ℚ) • y) k =
        ∑ k, x k ⬝ᵥ S *ᵥ x k + 2 * ((∑ k, ∑ i, ∑ j, (U k i * T i j * Y k j + Y k i * T i j * U k j +
          2 * d * R ^ 2 * Y k i * T i j * Y k j) : ℤ) : ℚ) := by
      push_cast
      simp only [dotProduct, mulVec, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hR' : (R : ℚ) ≠ 0 := by positivity
      have hd' : (d : ℚ) ≠ 0 := by positivity
      have hx1 : x k i = U k i / R := by rw [hU]; field_simp
      have hx2 : x k j = U k j / R := by rw [hU]; field_simp
      have hS : S i j = T i j / d := by rw [hT]; field_simp
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast
      rw [hx1, hx2, hS, ← hY k i, ← hY k j]
      field_simp
      ring
    unfold _root_.GlobalTheory.SW.Parab.parChar
    rw [hQ]
    set m : ℤ := ∑ k, ∑ i, ∑ j, (U k i * T i j * Y k j + Y k i * T i j * U k j +
          2 * d * R ^ 2 * Y k i * T i j * Y k j)
    have : -(↑π * I * (((∑ k, x k ⬝ᵥ S *ᵥ x k + 2 * (m : ℚ) : ℚ)) : ℂ)) =
        -(↑π * I * ((∑ k, x k ⬝ᵥ S *ᵥ x k : ℚ) : ℂ)) + ((-m : ℤ) : ℂ) * (2 * π * I) := by
      push_cast
      ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

open Matrix Complex in
open scoped ComplexConjugate Real in
theorem _root_.GlobalTheory.SW.Parab.qv_row_mul {κ ι : Type} [Fintype ι] (x : Matrix κ ι ℚ) (A : Matrix ι ι ℚ) (k : κ) :
    _root_.GlobalTheory.SW.qv ((x * A) k) = _root_.GlobalTheory.SW.qv (x k) ᵥ* _root_.GlobalTheory.SW.qm A := by
  funext j
  simp [_root_.GlobalTheory.SW.qv, _root_.GlobalTheory.SW.qm, vecMul, dotProduct, Matrix.mul_apply]

open Matrix Complex in
open scoped ComplexConjugate Real in
theorem _root_.GlobalTheory.SW.Parab.qv_bilin {ι : Type} [Fintype ι] (S : Matrix ι ι ℚ) (v : ι → ℚ) :
    ((v ⬝ᵥ S *ᵥ v : ℚ) : ℂ) = _root_.GlobalTheory.SW.qv v ⬝ᵥ _root_.GlobalTheory.SW.qm S *ᵥ _root_.GlobalTheory.SW.qv v := by
  simp [_root_.GlobalTheory.SW.qv, _root_.GlobalTheory.SW.qm, mulVec, dotProduct]

open Matrix Complex in
open scoped ComplexConjugate Real in
theorem _root_.GlobalTheory.SW.Parab.qm_mul' {α β γ : Type} [Fintype β] (A : Matrix α β ℚ) (B : Matrix β γ ℚ) :
    _root_.GlobalTheory.SW.qm (A * B) = _root_.GlobalTheory.SW.qm A * _root_.GlobalTheory.SW.qm B := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm, Matrix.mul_apply]

open Matrix Complex in
open scoped ComplexConjugate Real in
private lemma parabolic_exponent_term_eq {ι : Type} [Fintype ι] (A B : Matrix ι ι ℚ) (τ : Matrix ι ι ℂ)
    (v : ι → ℚ) (z : ι → ℂ) :
    _root_.GlobalTheory.SW.qv v ⬝ᵥ ((_root_.GlobalTheory.SW.qm A * τ + _root_.GlobalTheory.SW.qm B) *
        _root_.GlobalTheory.SW.qm Aᵀ) *ᵥ _root_.GlobalTheory.SW.qv v +
      2 * _root_.GlobalTheory.SW.qv v ⬝ᵥ (z ᵥ* _root_.GlobalTheory.SW.qm Aᵀ) =
    (_root_.GlobalTheory.SW.qv v ᵥ* _root_.GlobalTheory.SW.qm A) ⬝ᵥ τ *ᵥ
        (_root_.GlobalTheory.SW.qv v ᵥ* _root_.GlobalTheory.SW.qm A) +
      2 * (_root_.GlobalTheory.SW.qv v ᵥ* _root_.GlobalTheory.SW.qm A) ⬝ᵥ z +
      ((v ⬝ᵥ (B * Aᵀ) *ᵥ v : ℚ) : ℂ) := by
  rw [_root_.GlobalTheory.SW.Parab.qv_bilin, _root_.GlobalTheory.SW.Parab.qm_mul']
  have hT : _root_.GlobalTheory.SW.qm Aᵀ = (_root_.GlobalTheory.SW.qm A)ᵀ := by
    ext i j
    simp [_root_.GlobalTheory.SW.qm]
  rw [hT, add_mul, add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose,
    dotProduct_mulVec, vecMul_transpose, dotProduct_mulVec _ (_root_.GlobalTheory.SW.qm A) z]
  ring


open Matrix Complex in
open scoped ComplexConjugate Real in
theorem _root_.GlobalTheory.SW.Parab.trans_parabolic : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι]
    (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), Even (Fintype.card κ) → σ ∈ Matrix.symplecticGroup ι ℚ →
    σ.toBlocks₂₁ = 0 → ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, _root_.GlobalTheory.SW.IsSB φ →
    _root_.GlobalTheory.SW.IsSB (ω φ) ∧ _root_.GlobalTheory.SW.TransS σ φ (ω φ) ∧
    ∀ φ', _root_.GlobalTheory.SW.IsSB φ' → _root_.GlobalTheory.SW.ip (ω φ) (ω φ') =
      _root_.GlobalTheory.SW.ip φ φ' := by
  intro κ ι _ _ _ σ hev hσ hC
  classical
  have hDA : σ.toBlocks₂₂ * σ.toBlocks₁₁ᵀ = 1 := by
    have h := hσ
    rw [SymplecticGroup.mem_iff, ← fromBlocks_toBlocks σ, hC] at h
    simp only [J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_inj] at h
    simpa using h.2.2.1
  set A := σ.toBlocks₁₁ with hA
  set B := σ.toBlocks₁₂ with hB
  set D := σ.toBlocks₂₂ with hD
  have hAD : Aᵀ * D = 1 := mul_eq_one_comm.mp hDA
  have hDtA : Dᵀ * A = 1 := by simpa [Matrix.transpose_mul] using congrArg Matrix.transpose hAD
  have hADt : A * Dᵀ = 1 := mul_eq_one_comm.mp hDtA
  have hdet : D.det * A.det = 1 := by
    have h := congrArg Matrix.det hDA
    rwa [det_mul, det_transpose, det_one] at h
  have hdetA : A.det ≠ 0 := fun h => by simp [h] at hdet
  let e : Matrix κ ι ℚ ≃ Matrix κ ι ℚ :=
    { toFun := fun x => x * A
      invFun := fun x => x * Dᵀ
      left_inv := fun x => by simp [Matrix.mul_assoc, hADt]
      right_inv := fun x => by simp [Matrix.mul_assoc, hDtA] }
  let c : ℂ := (_root_.GlobalTheory.SW.qm D).det ^ (Fintype.card κ / 2)
  refine ⟨fun φ => c • fun x => _root_.GlobalTheory.SW.Parab.parChar (B * Aᵀ) x * φ (x * A), fun φ hφ => ?_⟩
  have hφA := (_root_.GlobalTheory.SW.LinChange.haar_mul ℚ κ ι φ hφ).1 A hdetA
  have hf := _root_.GlobalTheory.SW.Parab.isSB_parChar_mul (B * Aᵀ) _ hφA.1
  refine ⟨(_root_.GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι _ _ hf hf).2.1 c, ?_, ?_⟩
  · intro τ hτ ζ
    have hqD : (_root_.GlobalTheory.SW.qm D)⁻¹ = _root_.GlobalTheory.SW.qm Aᵀ := by
      refine Matrix.inv_eq_right_inv ?_
      rw [← _root_.GlobalTheory.SW.Parab.qm_mul', hDA]
      exact Matrix.map_one (Rat.castHom ℂ) (map_zero _) (map_one _)
    have h0 : _root_.GlobalTheory.SW.qm σ.toBlocks₂₁ = 0 := by
      rw [hC]
      ext i j
      simp [_root_.GlobalTheory.SW.qm]
    unfold _root_.GlobalTheory.SW.thS _root_.GlobalTheory.SW.spAct _root_.GlobalTheory.SW.spDen
    rw [h0, ← hA, ← hB, ← hD]
    simp only [zero_mul, zero_add, Matrix.mul_zero, zero_mulVec, dotProduct_zero, Finset.sum_const_zero,
      mul_zero, Complex.exp_zero, mul_one, hqD, Pi.smul_apply, smul_eq_mul]
    conv_rhs => rw [← e.tsum_eq, ← tsum_mul_left]
    congr 1
    funext x
    simp only [e, Equiv.coe_fn_mk, _root_.GlobalTheory.SW.Parab.qv_row_mul, parabolic_exponent_term_eq,
      Finset.sum_add_distrib]
    unfold _root_.GlobalTheory.SW.Parab.parChar
    rw [Rat.cast_sum, mul_add, Complex.exp_add, Complex.exp_neg]
    field_simp
    exact mul_comm _ _
  · intro φ' hφ'
    have hconj := (_root_.GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι φ' φ' hφ' hφ').2.2.2.1
    have hg : _root_.GlobalTheory.SW.IsSB fun x => φ x * conj (φ' x) :=
      (_root_.GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι _ _ hφ hconj).2.2.1
    have hgA := (_root_.GlobalTheory.SW.LinChange.haar_mul ℚ κ ι _ hg).1 A hdetA
    have hgA' := (_root_.GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι _ _ hgA.1 hgA.1).2.2.2.2.2.1
    unfold _root_.GlobalTheory.SW.ip
    have hpt : (fun x => (c • fun x => _root_.GlobalTheory.SW.Parab.parChar (B * Aᵀ) x * φ (x * A)) x *
        conj ((c • fun x => _root_.GlobalTheory.SW.Parab.parChar (B * Aᵀ) x * φ' (x * A)) x)) =
        (c * conj c) • fun x => φ (x * A) * conj (φ' (x * A)) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      linear_combination (c * conj c * φ (x * A) * conj (φ' (x * A))) *
        _root_.GlobalTheory.SW.Parab.parChar_mul_conj (B * Aᵀ) x
    rw [hpt, hgA', hgA.2, ← mul_assoc]
    have hdetD : (_root_.GlobalTheory.SW.qm D).det = (D.det : ℂ) := by
      rw [_root_.GlobalTheory.SW.qm]
      exact ((Rat.castHom ℂ).map_det D).symm
    obtain ⟨r, hr⟩ := hev
    have hn : Fintype.card κ / 2 = r := by omega
    have hq : (D.det ^ r * D.det ^ r * |A.det| ^ (r + r) : ℚ) = 1 := by
      rw [Even.pow_abs ⟨r, rfl⟩, ← pow_add, ← mul_pow, hdet, one_pow]
    have hconst : ∀ N : ℚ, N = A.det → c * conj c * ((|N| : ℚ) : ℂ) ^ Fintype.card κ = 1 := by
      rintro N rfl
      simp only [c, hdetD, hn, map_pow, map_ratCast]
      rw [hr]
      exact_mod_cast hq
    rw [hconst _ ?_, one_mul]
    exact congrFun (congrArg DFunLike.coe (Algebra.norm_self ℚ)) A.det

end GlobalTheory.SW.Parab
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelThetaTransformationSiegelParabolicStatement
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelTheta_transformation_siegelParabolic : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), Even (Fintype.card κ) → σ ∈ Matrix.symplecticGroup ι ℚ → σ.toBlocks₂₁ = 0 → ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ → IsSB (ω φ) ∧ TransS σ φ (ω φ) ∧ ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ' := by
  first | exact @GlobalTheory.SW.Parab.trans_parabolic | exact GlobalTheory.SW.Parab.trans_parabolic | (intros; apply GlobalTheory.SW.Parab.trans_parabolic <;> assumption)
end
end

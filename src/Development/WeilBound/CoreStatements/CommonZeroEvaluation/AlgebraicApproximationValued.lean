module

public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.CommonZeroEvaluation.IsAlgebraicStd
section -- merged from Development.WeilBound.CoreStatements.CommonZeroEvaluation.EventuallyRoot
open Polynomial Filter Topology

namespace ModelDimension.Alg

def HenselN (K : Type) [NormedField K] : Prop :=
  ∀ (h : K[X]) (α : K), (∀ k, ‖h.coeff k‖ ≤ 1) → ‖α‖ ≤ 1 → ‖h.eval α‖ < ‖h.derivative.eval α‖ ^ 2 →
    ∃ β, h.eval β = 0 ∧ ‖β - α‖ ≤ ‖h.eval α‖ / ‖h.derivative.eval α‖ ^ 2

variable {K : Type} [NormedField K]

theorem exists_deriv (α : K) (ε : ℝ) (hε : 0 < ε) (m : ℕ) (c : ℝ) (hc : 0 < c) : ∃ δ > 0, ∀ P : ℤ[X],
    c ≤ ‖aeval α (derivative^[m] P)‖ → ‖aeval α P‖ < δ →
      ∃ Q : ℤ[X], ‖aeval α Q‖ < ε * ‖aeval α (derivative Q)‖ ^ 2 := by
  by_cases H : ∃ Q : ℤ[X], ‖aeval α Q‖ < ε * ‖aeval α (derivative Q)‖ ^ 2
  · exact ⟨1, one_pos, fun _ _ _ => H⟩
  · push_neg at H
    have key : ∀ m : ℕ, ∀ c : ℝ, 0 < c → ∃ δ > 0, ∀ P : ℤ[X],
        ‖aeval α P‖ < δ → ‖aeval α (derivative^[m] P)‖ < c := by
      intro m
      induction m with
      | zero =>
        intro c hc
        exact ⟨c, hc, fun P hP => by simpa using hP⟩
      | succ m ih =>
        intro c hc
        obtain ⟨δ₁, hδ₁, h₁⟩ := ih c hc
        refine ⟨ε * δ₁ ^ 2, by positivity, fun P hP => ?_⟩
        rw [Function.iterate_succ_apply]
        apply h₁
        by_contra hle
        push_neg at hle
        have h2 : δ₁ ^ 2 ≤ ‖aeval α (derivative P)‖ ^ 2 := pow_le_pow_left₀ hδ₁.le hle 2
        have h3 := H P
        have h4 := mul_le_mul_of_nonneg_left h2 hε.le
        linarith
    obtain ⟨δ, hδ, hP⟩ := key m c hc
    exact ⟨δ, hδ, fun P h1 h2 => absurd h1 (not_le.mpr (hP P h2))⟩

theorem exists_small {π : K} (h0 : π ≠ 0) (h1 : ‖π‖ < 1) {ι : Type} (S : Finset ι) (z : ι → K) :
    ∃ N : ℕ, π ^ N ≠ 0 ∧ ∀ k ∈ S, ‖π ^ N * z k‖ < 1 := by
  have h : ∀ k ∈ S, ∀ᶠ n in atTop, ‖π ^ n * z k‖ < 1 := by
    intro k _
    have ht : Tendsto (fun n : ℕ => π ^ n * z k) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one h1).mul_const (z k)
      rwa [zero_mul] at this
    have hn := ht.norm
    rw [norm_zero] at hn
    exact hn.eventually (gt_mem_nhds one_pos)
  have hall : ∀ᶠ n in atTop, ∀ k ∈ S, ‖π ^ n * z k‖ < 1 := (Filter.eventually_all_finset S).2 h
  obtain ⟨N, hN⟩ := hall.exists
  exact ⟨N, pow_ne_zero N h0, hN⟩

theorem dense_algebraic [CharZero K] (hH : HenselN K) (hZ : ∀ z : ℤ, ‖(z : K)‖ ≤ 1) (N : ℕ) (hN0 : N ≠ 0)
    (hN : ‖(N : K)‖ < 1)
    (hC : ∀ α : K, ‖α‖ ≤ 1 → ∃ m : ℕ, ∀ δ > 0, ∃ P : ℤ[X], P.Monic ∧ P.natDegree = m ∧ ‖aeval α P‖ < δ) :
    Dense {x : K | IsAlgebraic ℤ x} := by
  have hloc : ∀ α : K, ‖α‖ ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ β : K, IsAlgebraic ℤ β ∧ ‖β - α‖ < ε := by
    intro α hα ε hε
    obtain ⟨m, hm⟩ := hC α hα
    have hε' : 0 < min ε 1 := lt_min hε one_pos
    have hfac : 0 < ‖(m.factorial : K)‖ :=
      norm_pos_iff.2 (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m))
    obtain ⟨δ, hδ, hQ⟩ :=
      ModelDimension.Alg.exists_deriv α (min ε 1) hε' m _ hfac
    obtain ⟨P, hPm, hPd, hPδ⟩ := hm δ hδ
    have hcoeff : P.coeff m = 1 := by
      rw [← hPd]
      exact hPm.coeff_natDegree
    have hDP : derivative^[m] P = C ((m.factorial : ℕ) : ℤ) := by
      have hdeg : (derivative^[m] P).natDegree ≤ 0 := by
        have := natDegree_iterate_derivative P m
        rw [hPd, Nat.sub_self] at this
        exact this
      rw [eq_C_of_natDegree_le_zero hdeg, coeff_iterate_derivative, zero_add,
        Nat.descFactorial_self, hcoeff]
      simp
    have hval : aeval α (derivative^[m] P) = (m.factorial : K) := by
      rw [hDP]
      simp
    obtain ⟨Q, hQ'⟩ := hQ P (le_of_eq (by rw [hval])) hPδ
    have hpos : 0 < ‖aeval α (derivative Q)‖ ^ 2 :=
      (mul_pos_iff_of_pos_left hε').1 (lt_of_le_of_lt (norm_nonneg _) hQ')
    have hev : ∀ y : K, (Q.map (algebraMap ℤ K)).eval y = aeval y Q :=
      fun y => eval_map_algebraMap Q y
    have hev' : (Q.map (algebraMap ℤ K)).derivative.eval α = aeval α (derivative Q) := by
      rw [derivative_map, eval_map_algebraMap]
    have hcoef : ∀ k, ‖(Q.map (algebraMap ℤ K)).coeff k‖ ≤ 1 := fun k => by
      rw [coeff_map]
      simpa using hZ (Q.coeff k)
    have hlt : ‖(Q.map (algebraMap ℤ K)).eval α‖ <
        ‖(Q.map (algebraMap ℤ K)).derivative.eval α‖ ^ 2 := by
      rw [hev, hev']
      exact lt_of_lt_of_le hQ' (mul_le_of_le_one_left (sq_nonneg _) (min_le_right _ _))
    obtain ⟨β, hβ, hβα⟩ := hH _ α hcoef hα hlt
    refine ⟨β, ⟨Q, ?_, ?_⟩, ?_⟩
    · rintro rfl
      simp at hQ'
    · rw [← hev]
      exact hβ
    · calc ‖β - α‖ ≤ ‖(Q.map (algebraMap ℤ K)).eval α‖ /
              ‖(Q.map (algebraMap ℤ K)).derivative.eval α‖ ^ 2 := hβα
        _ = ‖aeval α Q‖ / ‖aeval α (derivative Q)‖ ^ 2 := by rw [hev, hev']
        _ < min ε 1 := (div_lt_iff₀ hpos).2 hQ'
        _ ≤ ε := min_le_left _ _
  rw [Metric.dense_iff]
  intro x r hr
  have hν : ((N : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hN0
  obtain ⟨M, hM0, hM⟩ :=
    ModelDimension.Alg.exists_small hν hN ({()} : Finset Unit) (fun _ => x)
  have hMx : ‖(N : K) ^ M * x‖ < 1 := hM () (Finset.mem_singleton_self _)
  have htpos : 0 < ‖(N : K) ^ M‖ := norm_pos_iff.2 hM0
  obtain ⟨β, hβ, hβx⟩ := hloc _ hMx.le (r * ‖(N : K) ^ M‖) (mul_pos hr htpos)
  have hNa : IsAlgebraic ℤ ((N : K) ^ M) := (isAlgebraic_natCast N).pow M
  refine ⟨β / (N : K) ^ M, ?_, ?_⟩
  · rw [mem_ball_iff_norm]
    have h : β / (N : K) ^ M - x = (β - (N : K) ^ M * x) / (N : K) ^ M := by
      rw [sub_div, mul_div_cancel_left₀ x hM0]
    rw [h, norm_div, div_lt_iff₀ htpos]
    exact hβx
  · show IsAlgebraic ℤ (β / (N : K) ^ M)
    rw [div_eq_mul_inv]
    exact hβ.mul hNa.inv

theorem eventually_root (hH : HenselN K) {π : K} (h0 : π ≠ 0) (h1 : ‖π‖ < 1) {T A : Type} [TopologicalSpace T]
    [CommRing A] (ev : T → (A →+* K)) (hev : ∀ r, Continuous fun t => ev t r) (f : A[X]) (t₀ : T) (x₀ : K)
    (hf : f.eval₂ (ev t₀) x₀ = 0) (hf' : f.derivative.eval₂ (ev t₀) x₀ ≠ 0) (r : ℝ) (hr : 0 < r) :
    ∀ᶠ t in 𝓝 t₀, ∃ x, ‖x - x₀‖ < r ∧ f.eval₂ (ev t) x = 0 := by
  classical
  have hcont : ∀ (p : A[X]) (y : K), Continuous fun t => p.eval₂ (ev t) y := by
    intro p y
    have h : ∀ t, p.eval₂ (ev t) y = ∑ n ∈ p.support, ev t (p.coeff n) * y ^ n := fun t => by
      rw [eval₂_eq_sum, Polynomial.sum]
    exact (continuous_finsetSum _ fun n _ => (hev _).mul continuous_const).congr
      fun t => (h t).symm
  have hcoef : ∀ (q : K[X]) (k : ℕ), Continuous fun t => ((f.map (ev t)).comp q).coeff k := by
    intro q k
    have h : ∀ t, ((f.map (ev t)).comp q).coeff k =
        ∑ n ∈ f.support, ev t (f.coeff n) * (q ^ n).coeff k := fun t => by
      rw [Polynomial.comp, eval₂_map, eval₂_eq_sum, Polynomial.sum, finsetSum_coeff]
      simp only [RingHom.coe_comp, RingHom.comp_apply, Function.comp_apply, coeff_C_mul]
    exact (continuous_finsetSum _ fun n _ => (hev _).mul continuous_const).congr
      fun t => (h t).symm
  obtain ⟨p, hp⟩ : ∃ p : T → K[X], ∀ t, p t = (f.map (ev t)).comp (C x₀ + X) :=
    ⟨_, fun _ => rfl⟩
  have hpc : ∀ k, Continuous fun t => (p t).coeff k := fun k =>
    (hcoef (C x₀ + X) k).congr fun t => by rw [hp]
  have hpdeg : ∀ t, (p t).natDegree ≤ f.natDegree := by
    intro t
    rw [hp]
    refine natDegree_comp_le.trans ?_
    have hq : (C x₀ + X : K[X]).natDegree ≤ 1 :=
      (natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)
    calc (f.map (ev t)).natDegree * (C x₀ + X).natDegree ≤ f.natDegree * 1 :=
          Nat.mul_le_mul natDegree_map_le hq
      _ = f.natDegree := mul_one _
  have hpeval : ∀ t y, (p t).eval y = f.eval₂ (ev t) (x₀ + y) := by
    intro t y
    rw [hp, eval_comp, eval_map]
    simp
  have hpderiv : ∀ t, (derivative (p t)).eval 0 = f.derivative.eval₂ (ev t) x₀ := by
    intro t
    rw [hp, derivative_comp, eval_mul, eval_comp, derivative_map, eval_map]
    simp
  have hb0 : (p t₀).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, hpeval, add_zero, hf]
  obtain ⟨N, hN0, hN⟩ := ModelDimension.Alg.exists_small h0 h1
    (Finset.range (f.natDegree + 1)) (fun k => (p t₀).coeff k)
  have hl1 : ‖π ^ N‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) h1.le
  generalize π ^ N = l at hN0 hN hl1
  have hat : ∀ k ∈ Finset.range (f.natDegree + 1), ‖l ^ k * (p t₀).coeff k‖ < 1 := by
    intro k hk
    cases k with
    | zero => simp [hb0]
    | succ j =>
      rw [pow_succ, mul_assoc, norm_mul]
      calc ‖l ^ j‖ * ‖l * (p t₀).coeff (j + 1)‖ ≤ ‖l * (p t₀).coeff (j + 1)‖ :=
            mul_le_of_le_one_left (norm_nonneg _)
              (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hl1)
        _ < 1 := hN _ hk
  have E1 : ∀ᶠ t in 𝓝 t₀, ∀ k ∈ Finset.range (f.natDegree + 1), ‖l ^ k * (p t).coeff k‖ < 1 := by
    refine (Filter.eventually_all_finset _).2 fun k hk => ?_
    have hck : Continuous fun t => ‖l ^ k * (p t).coeff k‖ := (continuous_const.mul (hpc k)).norm
    exact hck.continuousAt.eventually_lt continuousAt_const (hat k hk)
  have hu : Continuous fun t => ‖f.eval₂ (ev t) x₀‖ := (hcont f x₀).norm
  have hw : Continuous fun t => ‖l * f.derivative.eval₂ (ev t) x₀‖ ^ 2 :=
    ((continuous_const.mul (hcont _ x₀)).norm).pow 2
  have hw0 : 0 < ‖l * f.derivative.eval₂ (ev t₀) x₀‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 (mul_ne_zero hN0 hf')) 2
  have E2 : ∀ᶠ t in 𝓝 t₀, ‖f.eval₂ (ev t) x₀‖ < ‖l * f.derivative.eval₂ (ev t) x₀‖ ^ 2 := by
    refine hu.continuousAt.eventually_lt hw.continuousAt ?_
    show ‖f.eval₂ (ev t₀) x₀‖ < ‖l * f.derivative.eval₂ (ev t₀) x₀‖ ^ 2
    rw [hf, norm_zero]
    exact hw0
  have hu' : Continuous fun t => ‖f.eval₂ (ev t) x₀‖ * ‖l‖ := hu.mul continuous_const
  have hw' : Continuous fun t => r * ‖l * f.derivative.eval₂ (ev t) x₀‖ ^ 2 :=
    continuous_const.mul hw
  have E3 : ∀ᶠ t in 𝓝 t₀,
      ‖f.eval₂ (ev t) x₀‖ * ‖l‖ < r * ‖l * f.derivative.eval₂ (ev t) x₀‖ ^ 2 := by
    refine hu'.continuousAt.eventually_lt hw'.continuousAt ?_
    show ‖f.eval₂ (ev t₀) x₀‖ * ‖l‖ < r * ‖l * f.derivative.eval₂ (ev t₀) x₀‖ ^ 2
    rw [hf, norm_zero, zero_mul]
    exact mul_pos hr hw0
  filter_upwards [E1, E2, E3] with t hE1 hE2 hE3
  obtain ⟨G, hG⟩ : ∃ G : K[X], G = (p t).comp (C l * X) := ⟨_, rfl⟩
  have hGc : ∀ k, ‖G.coeff k‖ ≤ 1 := by
    intro k
    rw [hG, comp_C_mul_X_coeff, mul_comm]
    by_cases hk : k ∈ Finset.range (f.natDegree + 1)
    · exact (hE1 k hk).le
    · rw [coeff_eq_zero_of_natDegree_lt, mul_zero, norm_zero]
      · exact zero_le_one
      · have := hpdeg t
        simp only [Finset.mem_range, not_lt] at hk
        omega
  have hG0 : G.eval 0 = f.eval₂ (ev t) x₀ := by
    rw [hG, eval_comp, hpeval]
    simp
  have hG1 : (derivative G).eval 0 = l * f.derivative.eval₂ (ev t) x₀ := by
    rw [hG, derivative_comp, eval_mul, eval_comp, derivative_C_mul_X, eval_C]
    simp [hpderiv]
  have hlt : ‖G.eval 0‖ < ‖(derivative G).eval 0‖ ^ 2 := by
    rw [hG0, hG1]
    exact hE2
  obtain ⟨y, hy, hyb⟩ := hH G 0 hGc (by simp) hlt
  refine ⟨x₀ + l * y, ?_, ?_⟩
  · rw [hG0, hG1, sub_zero] at hyb
    have hwpos : 0 < ‖l * f.derivative.eval₂ (ev t) x₀‖ ^ 2 :=
      lt_of_le_of_lt (norm_nonneg _) hE2
    rw [le_div_iff₀ hwpos] at hyb
    rw [add_sub_cancel_left, norm_mul]
    by_contra hge
    push_neg at hge
    have h1' := mul_le_mul_of_nonneg_right hge hwpos.le
    have h2' := mul_le_mul_of_nonneg_left hyb (norm_nonneg l)
    nlinarith
  · have hGy : G.eval y = (p t).eval (l * y) := by
      rw [hG, eval_comp]
      simp
    rw [← hpeval t (l * y), ← hGy]
    exact hy

theorem infinite_inter {π : K} (h0 : π ≠ 0) (h1 : ‖π‖ < 1) {D : Set K} (hD : Dense D) (x : K) (r : ℝ)
    (hr : 0 < r) : (D ∩ Metric.ball x r).Infinite := by
  letI : NontriviallyNormedField K := NontriviallyNormedField.ofNormNeOne ⟨π, h0, h1.ne⟩
  intro hfin
  have hU : IsOpen (Metric.ball x r \ (D ∩ Metric.ball x r)) :=
    Metric.isOpen_ball.sdiff hfin.isClosed
  have hne : (Metric.ball x r \ (D ∩ Metric.ball x r)).Nonempty :=
    ((infinite_of_mem_nhds x (Metric.ball_mem_nhds x hr)).diff hfin).nonempty
  obtain ⟨y, hyU, hyD⟩ := hD.inter_open_nonempty _ hU hne
  exact hyU.2 ⟨hyD, hyU.1⟩

end ModelDimension.Alg
end

open Polynomial Filter Topology

namespace ModelDimension.Alg

theorem isAlgebraic_std {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
    (P : StandardEtalePresentation A B) (g : B) : IsAlgebraic A g := by
  haveI : Algebra.IsStandardEtale A B := ⟨⟨P⟩⟩
  have hx : IsIntegral A P.x := ⟨P.f, P.monic_f, P.hasMap.1⟩
  have hp : ∀ p : A[X], IsAlgebraic A (aeval P.x p) := fun p =>
    (IsIntegral.of_mem_of_fg _ hx.fg_adjoin_singleton _ (aeval_mem_adjoin_singleton _ _)).isAlgebraic
  obtain ⟨p, n, h⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x g
  have hu : aeval P.x P.g ^ n ≠ 0 := (P.hasMap.2.pow n).ne_zero
  refine IsAlgebraic.of_mul (y := aeval P.x P.g ^ n) (mem_nonZeroDivisors_of_ne_zero hu) ((hp _).pow n) ?_
  rw [mul_comm, h]
  exact hp p

theorem approx_std {F K : Type} [Field F] [NormedField K] [Algebra F K] (hH : HenselN K) {π : K} (h0 : π ≠ 0)
    (h1 : ‖π‖ < 1) (hD : Dense {x : K | IsAlgebraic F x}) {n : ℕ} {B : Type} [CommRing B] [IsDomain B] [Algebra F B]
    [Algebra (MvPolynomial (Fin n) F) B] [IsScalarTower F (MvPolynomial (Fin n) F) B]
    [Algebra.IsStandardEtale (MvPolynomial (Fin n) F) B] (ψ : B →ₐ[F] K) (S : Finset B) (ε : ℝ) (hε : 0 < ε) (g : B)
    (hg : g ≠ 0) : ∃ ψ' : B →ₐ[F] K, (∀ x, IsAlgebraic F (ψ' x)) ∧ (∀ s ∈ S, ‖ψ' s - ψ s‖ < ε) ∧ ψ' g ≠ 0 := by
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := MvPolynomial (Fin n) F) (S := B)
  obtain ⟨c, hc0, hc⟩ := (isAlgebraic_std P g).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hg)
  let ev : (Fin n → K) → (MvPolynomial (Fin n) F →+* K) := fun b => (MvPolynomial.aeval b : _ →ₐ[F] K)
  have hev : ∀ r, Continuous fun b => ev b r := by
    intro r
    induction r using MvPolynomial.induction_on with
    | C a => simpa [ev] using continuous_const
    | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
    | mul_X p i hp =>
      have : Continuous fun b : Fin n → K => ev b p * b i := hp.mul (continuous_apply i)
      simpa [ev] using this
  let a : Fin n → K := fun i => ψ (algebraMap (MvPolynomial (Fin n) F) B (MvPolynomial.X i))
  have ha : ev a = (ψ : B →+* K).comp (algebraMap (MvPolynomial (Fin n) F) B) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => by simp [ev, a])
    have : algebraMap (MvPolynomial (Fin n) F) B (MvPolynomial.C r) = algebraMap F B r :=
      (IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n) F) B r).symm
    simp [ev, this]
  have hψ : ∀ p : (MvPolynomial (Fin n) F)[X], p.eval₂ (ev a) (ψ P.x) = ψ (aeval P.x p) := by
    intro p
    rw [ha, aeval_def]
    exact (hom_eval₂ p _ (ψ : B →+* K) P.x).symm
  have hc2 : ∀ p : (MvPolynomial (Fin n) F)[X],
      Continuous fun t : (Fin n → K) × K => p.eval₂ (ev t.1) t.2 := by
    intro p
    simp only [eval₂_eq_sum, Polynomial.sum]
    exact continuous_finsetSum _ fun k _ => ((hev _).comp continuous_fst).mul (continuous_snd.pow _)
  choose p m hpm using P.exists_mul_aeval_x_g_pow_eq_aeval_x
  have hg0 : P.g.eval₂ (ev a) (ψ P.x) ≠ 0 := by
    rw [hψ]; exact (P.hasMap.2.map ψ).ne_zero
  have E1 : ∀ᶠ t : (Fin n → K) × K in 𝓝 (a, ψ P.x), P.g.eval₂ (ev t.1) t.2 ≠ 0 :=
    (hc2 P.g).continuousAt.eventually_ne hg0
  have E2 : ∀ᶠ t : (Fin n → K) × K in 𝓝 (a, ψ P.x), ∀ s ∈ S,
      ‖(p s).eval₂ (ev t.1) t.2 / P.g.eval₂ (ev t.1) t.2 ^ m s - ψ s‖ < ε := by
    rw [eventually_all_finset]
    intro s _
    have hca : ContinuousAt (fun t : (Fin n → K) × K =>
        ‖(p s).eval₂ (ev t.1) t.2 / P.g.eval₂ (ev t.1) t.2 ^ m s - ψ s‖) (a, ψ P.x) := by
      have h3 : ContinuousAt (fun t : (Fin n → K) × K => P.g.eval₂ (ev t.1) t.2 ^ m s) (a, ψ P.x) :=
        ((hc2 P.g).pow (m s)).continuousAt
      have h4 := (hc2 (p s)).continuousAt.div h3 (pow_ne_zero (m s) hg0)
      exact (h4.sub continuousAt_const).norm
    refine hca.eventually (gt_mem_nhds ?_)
    show ‖(p s).eval₂ (ev a) (ψ P.x) / P.g.eval₂ (ev a) (ψ P.x) ^ m s - ψ s‖ < ε
    rw [hψ (p s), ← hpm, map_mul, map_pow, ← hψ, mul_div_cancel_right₀ _ (pow_ne_zero _ hg0), sub_self, norm_zero]
    exact hε
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (E1.and E2)
  have E3 := eventually_root hH h0 h1 ev hev P.f a (ψ P.x) (by rw [hψ, P.hasMap.1, map_zero])
    (by rw [hψ]; exact (P.hasMap.isUnit_derivative_f.map ψ).ne_zero) r hr
  obtain ⟨r', hr', hball'⟩ := Metric.eventually_nhds_iff.1 E3
  have hb : ∃ b : Fin n → K, (∀ i, b i ∈ {x : K | IsAlgebraic F x} ∩ Metric.ball (a i) (min r r')) ∧ ev b c ≠ 0 := by
    by_contra hne
    push Not at hne
    apply hc0
    apply MvPolynomial.map_injective (algebraMap F K) (algebraMap F K).injective
    refine MvPolynomial.funext_set (fun i => {x : K | IsAlgebraic F x} ∩ Metric.ball (a i) (min r r'))
      (fun i => infinite_inter h0 h1 hD _ _ (lt_min hr hr')) fun b hb => ?_
    rw [map_zero, map_zero, MvPolynomial.eval_map]
    exact hne b fun i => hb i trivial
  obtain ⟨b, hb, hbc⟩ := hb
  have hba : dist b a < min r r' := (dist_pi_lt_iff (lt_min hr hr')).2 fun i => (hb i).2
  obtain ⟨x, hx, hfx⟩ := hball' (hba.trans_le (min_le_right _ _))
  obtain ⟨e1, e2⟩ := hball (y := (b, x)) (by
    rw [Prod.dist_eq]
    exact max_lt (hba.trans_le (min_le_left _ _)) (by rwa [dist_eq_norm]))
  let L := algebraicClosure F K
  let φ : MvPolynomial (Fin n) F →ₐ[F] L := MvPolynomial.aeval fun i => ⟨b i, mem_algebraicClosure_iff.2 (hb i).1⟩
  have hφ : (algebraMap L K).comp (φ : _ →+* L) = ev b := by
    refine MvPolynomial.ringHom_ext (fun r => by simp [ev, φ]) (fun i => by simp [ev, φ])
  have hxL : x ∈ L := by
    have : IsIntegral L x := ⟨P.f.map (φ : _ →+* L), P.monic_f.map _, by rw [eval₂_map, hφ, hfx]⟩
    exact mem_algebraicClosure_iff.2 (this.isAlgebraic.restrictScalars F)
  letI : Algebra (MvPolynomial (Fin n) F) L := (φ : _ →+* L).toAlgebra
  haveI : IsScalarTower F (MvPolynomial (Fin n) F) L := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have hval : ∀ q : (MvPolynomial (Fin n) F)[X], algebraMap L K (aeval (⟨x, hxL⟩ : L) q) = q.eval₂ (ev b) x := by
    intro q
    rw [aeval_def, hom_eval₂, ← hφ]
    rfl
  have hm : P.HasMap (⟨x, hxL⟩ : L) := by
    refine ⟨(algebraMap L K).injective (by rw [hval, hfx, map_zero]), Ne.isUnit fun h => e1 ?_⟩
    rw [← hval, h, map_zero]
  let χ : B →ₐ[MvPolynomial (Fin n) F] L := (P.lift _ hm).comp P.equivRing.toAlgHom
  have hχ : χ P.x = ⟨x, hxL⟩ := by simp [χ]
  have hχ' : ∀ q : (MvPolynomial (Fin n) F)[X], algebraMap L K (χ (aeval P.x q)) = q.eval₂ (ev b) x := by
    intro q
    rw [← aeval_algHom_apply, hχ, hval]
  refine ⟨L.val.comp (χ.restrictScalars F), fun y => mem_algebraicClosure_iff.1 (χ y).2, fun s hs => ?_, ?_⟩
  · have h2 := e2 s hs
    have h3 := hχ' (p s)
    rw [← hpm, map_mul, map_pow, map_mul, map_pow, hχ'] at h3
    dsimp only at h2 e1
    rw [← h3, mul_div_cancel_right₀ _ (pow_ne_zero _ e1)] at h2
    exact h2
  · intro h
    obtain ⟨u, hu⟩ := hc
    apply hbc
    have h2 : ev b c = algebraMap L K (χ (algebraMap _ B c)) := by
      rw [χ.commutes, ← hφ]; rfl
    have h3 : algebraMap L K (χ g) = 0 := h
    rw [h2, hu, map_mul, map_mul, h3, zero_mul]

theorem approx_smooth {F K : Type} [Field F] [NormedField K] [Algebra F K] (hH : HenselN K) {π : K} (h0 : π ≠ 0)
    (h1 : ‖π‖ < 1) (hD : Dense {x : K | IsAlgebraic F x}) {R : Type} [CommRing R] [IsDomain R] [Algebra F R]
    [Algebra.Smooth F R] (ψ : R →ₐ[F] K) (S : Finset R) (ε : ℝ) (hε : 0 < ε) (g : R)
    (hg : g ≠ 0) : ∃ ψ' : R →ₐ[F] K, (∀ x, IsAlgebraic F (ψ' x)) ∧ (∀ s ∈ S, ‖ψ' s - ψ s‖ < ε) ∧ ψ' g ≠ 0 := by
  classical
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime _
  haveI : Algebra.IsSmoothAt F (RingHom.ker ψ) := by
    unfold Algebra.IsSmoothAt
    infer_instance
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := F) (p := RingHom.ker ψ)
  have hψf : ψ f ≠ 0 := hf
  have hf0 : f ≠ 0 := fun h => hψf (by rw [h, map_zero])
  have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  have hinj : Function.Injective (algebraMap R (Localization.Away f)) := IsLocalization.injective _ hle
  let ψ₁ : Localization.Away f →ₐ[F] K := IsLocalization.Away.liftAlgHom f (f := ψ) hψf.isUnit
  have hψ₁ : ∀ s, ψ₁ (algebraMap R _ s) = ψ s := fun s => by simp [ψ₁]
  obtain ⟨ψ', ha, hs, hg'⟩ := approx_std (n := n) hH h0 h1 hD ψ₁ (S.image (algebraMap R _)) ε hε (algebraMap R _ g)
    ((map_ne_zero_iff _ hinj).2 hg)
  refine ⟨ψ'.comp (IsScalarTower.toAlgHom F R _), fun x => ha _, fun s h => ?_, hg'⟩
  rw [← hψ₁]
  exact hs _ (Finset.mem_image_of_mem _ h)

end ModelDimension.Alg
end

section -- merged from Development.WeilBound.CoreStatements.CommonZeroEvaluation.ExistsRootAdicComplete
open Polynomial

namespace ModelDimension.Alg

theorem exists_root_adic_complete {V : Type} [CommRing V] (I : Ideal V) [IsAdicComplete I V] (e : V) (he : e ∈ I)
    (q : V[X]) : ∃ y ∈ I, e + y + y ^ 2 * q.eval y = 0 := by
  let c : ℕ → V := fun n => Nat.rec 0 (fun _ b => -e - b ^ 2 * q.eval b) n
  have hc : ∀ n, c (n + 1) = -e - c n ^ 2 * q.eval (c n) := fun n => rfl
  have hI : ∀ n, c n ∈ I := by
    intro n
    induction n with
    | zero => exact I.zero_mem
    | succ n ih =>
      rw [hc]
      exact I.sub_mem (I.neg_mem he) (I.mul_mem_right _ (I.pow_mem_of_mem ih 2 (by norm_num)))
  have key : ∀ (y z : V) (n : ℕ), y ∈ I → z ∈ I → y - z ∈ I ^ n →
      y ^ 2 * q.eval y - z ^ 2 * q.eval z ∈ I ^ (n + 1) := by
    intro y z n hy hz h
    obtain ⟨k, hk⟩ := Polynomial.sub_dvd_eval_sub y z q
    have : y ^ 2 * q.eval y - z ^ 2 * q.eval z = (y - z) * ((y + z) * q.eval y + z * (z * k)) := by
      linear_combination z ^ 2 * hk
    rw [this, pow_succ]
    exact Ideal.mul_mem_mul h (I.add_mem (I.mul_mem_right _ (I.add_mem hy hz)) (I.mul_mem_right _ hz))
  have hstep : ∀ n, c (n + 1) - c n ∈ I ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := key _ _ n (hI (n + 1)) (hI n) ih
      have e2 : c (n + 1 + 1) - c (n + 1) =
          -(c (n + 1) ^ 2 * q.eval (c (n + 1)) - c n ^ 2 * q.eval (c n)) := by
        rw [hc (n + 1)]
        linear_combination -(hc n)
      rw [e2]
      exact (I ^ (n + 1)).neg_mem this
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal V)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have : c m - c (n + 1) = (c m - c n) - (c (n + 1) - c n) := by ring
      rw [this]
      exact (I ^ m).sub_mem ih (Ideal.pow_le_pow_right hmn (hstep n))
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  have ha' : ∀ n, c n - a ∈ I ^ n := fun n => by
    have := ha n
    rwa [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem] at this
  have haI : a ∈ I := by
    have h1 := ha' 1
    rw [pow_one] at h1
    have : a = c 1 - (c 1 - a) := by ring
    rw [this]
    exact I.sub_mem (hI 1) h1
  refine ⟨a, haI, IsHausdorff.haus' (I := I) _ fun n => ?_⟩
  rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.zero]
  have h1 := key _ _ n (hI n) haI (ha' n)
  have h2 := ha' (n + 1)
  have : e + a + a ^ 2 * q.eval a = -(c (n + 1) - a) - (c n ^ 2 * q.eval (c n) - a ^ 2 * q.eval a) := by
    rw [hc]; ring
  rw [this]
  exact Ideal.pow_le_pow_right (Nat.le_succ n) ((I ^ (n + 1)).sub_mem ((I ^ (n + 1)).neg_mem h2) h1)

theorem exists_root {V : Type} [CommRing V] [IsLocalRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    (f : V[X]) (α e : V) (he : e ∈ IsLocalRing.maximalIdeal V)
    (h : f.eval α = (f.derivative.eval α) ^ 2 * e) : ∃ β, f.eval β = 0 ∧ e ∣ β - α := by
  set d := f.derivative.eval α with hd
  obtain ⟨k, hk⟩ := (f.map (C : V →+* V[X])).binomExpansion (C α) (C d * X)
  obtain ⟨y, hy, hq⟩ := exists_root_adic_complete _ e he k
  have h1 := congrArg (Polynomial.evalRingHom y) hk
  have hev : ∀ (p : V[X]) (z : V[X]), (evalRingHom y) ((p.map (C : V →+* V[X])).eval z) = p.eval (z.eval y) := by
    intro p z
    rw [eval_map, hom_eval₂]
    have : (evalRingHom y).comp (C : V →+* V[X]) = RingHom.id V := by ext; simp
    rw [this]
    rfl
  rw [derivative_map] at h1
  simp only [map_add (f := _), map_mul, map_pow, hev] at h1
  simp only [coe_evalRingHom, eval_C, eval_X, eval_add, eval_mul, ← hd] at h1
  refine ⟨α + d * y, ?_, ?_⟩
  · rw [h1, h]
    linear_combination d ^ 2 * hq
  · have hu : IsUnit (1 + y * k.eval y) := by
      have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(y * k.eval y))
        ((IsLocalRing.mem_maximalIdeal _).1 (Submodule.neg_mem _ (Ideal.mul_mem_right _ _ hy)))
      simpa using this
    have : e ∣ y * (1 + y * k.eval y) := ⟨-1, by linear_combination hq⟩
    rw [add_sub_cancel_left]
    exact Dvd.dvd.mul_left ((hu.dvd_mul_right).1 this) d

theorem exists_monic {V : Type} [CommRing V] (N : ℕ) [Finite (V ⧸ Ideal.span {(N : V)})] :
    ∃ m : ℕ, ∀ (α : V) (k : ℕ), ∃ P : ℤ[X], P.Monic ∧ P.natDegree = m ∧ (N : V) ^ k ∣ aeval α P := by
  classical
  let s : Set V := Set.range (Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {(N : V)})))
  have hs : s.Finite := Set.finite_range _
  have hsp : ∀ (k : ℕ) (x : V), ∃ y ∈ Submodule.span ℤ s, (N : V) ^ k ∣ x - y := by
    intro k
    induction k with
    | zero => exact fun x => ⟨0, Submodule.zero_mem _, by simp⟩
    | succ k ih =>
      intro x
      obtain ⟨y, hy, z, hz⟩ := ih x
      let w := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {(N : V)})) (Ideal.Quotient.mk _ z)
      have hw : Ideal.Quotient.mk (Ideal.span {(N : V)}) w = Ideal.Quotient.mk _ z := Function.surjInv_eq _ _
      obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hw.symm)
      refine ⟨y + ((N : ℤ) ^ k) • w, Submodule.add_mem _ hy
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)), u, ?_⟩
      rw [zsmul_eq_mul]
      push_cast
      linear_combination hz + (N : V) ^ k * hu
  refine ⟨s.ncard, fun α k => ?_⟩
  let J : Ideal V := Ideal.span {(N : V) ^ k}
  have htop : Submodule.span ℤ (Ideal.Quotient.mk J '' s) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, hy, hd⟩ := hsp k x
    have : Ideal.Quotient.mk J x = Ideal.Quotient.mk J y := Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 hd)
    rw [this]
    have := Submodule.mem_map_of_mem (f := (Ideal.Quotient.mkₐ ℤ J).toLinearMap) hy
    rwa [Submodule.map_span] at this
  haveI : Module.Finite ℤ (V ⧸ J) := ⟨htop ▸ Submodule.fg_span (hs.image _)⟩
  obtain ⟨p, hp, hdeg, h0⟩ := LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero ℤ
    (Algebra.lmul ℤ (V ⧸ J) (Ideal.Quotient.mk J α))
  have hle : p.natDegree ≤ s.ncard := by
    rw [hdeg, ← htop]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (hs.image _)).trans (Set.ncard_image_le hs)
  have h1 : aeval (Ideal.Quotient.mk J α) p = 0 := by
    rw [aeval_algHom_apply] at h0
    exact Algebra.lmul_injective (h0.trans (map_zero _).symm)
  have h2 : (N : V) ^ k ∣ aeval α p := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
    exact (aeval_algHom_apply (Ideal.Quotient.mkₐ ℤ J) α p).symm.trans h1
  refine ⟨p * X ^ (s.ncard - p.natDegree), hp.mul (monic_X_pow _), ?_, ?_⟩
  · rw [hp.natDegree_mul (monic_X_pow _), natDegree_X_pow]; omega
  · rw [map_mul]; exact h2.mul_right _

end ModelDimension.Alg
end

open Formalism.L2.Pj

open Polynomial IsDedekindDomain

theorem ModelDimension.Alg.approx_dvr (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra F R]
    [Algebra.Smooth F R] (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V] [Field K] [Algebra V K] [IsFractionRing V K]
    (hT : Finite (IsLocalRing.ResidueField V)) (io : F →+* K) (ψ : R →+* K) (hψ : ψ.comp (algebraMap F R) = io)
    (S : Finset R) (n : ℕ) (g : R) (hg : g ≠ 0) : ∃ ψ' : R →+* K, ψ'.comp (algebraMap F R) = io ∧
      (∀ x, IsAlgebraic ℤ (ψ' x)) ∧ (∀ s ∈ S, ψ' s = ψ s ∨ (n : ℤ) ≤ vV V (ψ' s - ψ s)) ∧ ψ' g ≠ 0 := by
  classical
  set P := IsDiscreteValuationRing.maximalIdeal V with hP
  have hb : (1 : NNReal) < 2 := one_lt_two
  letI nK : NormedField K := (P.adicAbv (K := K) hb).toNormedField
  have hnorm : ∀ x : K, ‖x‖ = (WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (valV V x) : ℝ) :=
    fun x => rfl
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective V K)
  have hint : ∀ a : V, ‖algebraMap V K a‖ ≤ 1 := by
    intro a
    rw [hnorm]
    exact_mod_cast (WithZeroMulInt.toNNReal_le_one_iff hb).mpr (P.valuation_le_one (K := K) a)
  have hintlt : ∀ a : V, ‖algebraMap V K a‖ < 1 ↔ a ∈ IsLocalRing.maximalIdeal V := by
    intro a
    rw [hnorm]
    have h := WithZeroMulInt.toNNReal_lt_one_iff (m := P.valuation K (algebraMap V K a)) hb
    rw [P.valuation_lt_one_iff_mem] at h
    exact_mod_cast h
  have hmem : ∀ x : K, ‖x‖ ≤ 1 → ∃ a : V, algebraMap V K a = x := by
    intro x hx
    have hv : P.valuation K x ≤ 1 := by
      rw [hnorm] at hx
      exact (WithZeroMulInt.toNNReal_le_one_iff hb).mp (by exact_mod_cast hx)
    have huniq : ∀ w : HeightOneSpectrum V, w = P := by
      intro w
      ext1
      exact IsLocalRing.eq_maximalIdeal w.isMaximal
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K x
      (fun w => by rw [huniq w]; exact hv)
    exact ⟨a, ha⟩
  have hev : ∀ (q : Polynomial V) (a : V),
      Polynomial.eval (algebraMap V K a) (q.map (algebraMap V K)) = algebraMap V K (Polynomial.eval a q) := by
    intro q a
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have hH : ModelDimension.Alg.HenselN K := by
    intro h α hco hα hlt
    obtain ⟨f, rfl⟩ : ∃ f : Polynomial V, f.map (algebraMap V K) = h := by
      have hl : h ∈ Polynomial.lifts (algebraMap V K) :=
        (Polynomial.lifts_iff_coeff_lifts h).mpr (fun k => hmem _ (hco k))
      exact Polynomial.mem_lifts h |>.mp hl
    obtain ⟨a, rfl⟩ := hmem α hα
    rw [Polynomial.derivative_map, hev, hev] at hlt
    rw [Polynomial.derivative_map, hev, hev]
    set y := Polynomial.eval a f
    set d := Polynomial.eval a (Polynomial.derivative f)
    have hd : algebraMap V K d ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hlt
      have := norm_nonneg (algebraMap V K y)
      nlinarith
    have hdpos : 0 < ‖algebraMap V K d‖ ^ 2 := by positivity
    have hq : ‖algebraMap V K y / algebraMap V K d ^ 2‖ < 1 := by
      rw [norm_div, norm_pow, div_lt_one hdpos]
      exact hlt
    obtain ⟨e, he⟩ := hmem _ hq.le
    have hem : e ∈ IsLocalRing.maximalIdeal V := (hintlt e).mp (by rw [he]; exact hq)
    have hy : y = d ^ 2 * e := by
      apply IsFractionRing.injective V K
      rw [map_mul, map_pow, he]
      field_simp
    obtain ⟨β, hβ, c, hc⟩ := ModelDimension.Alg.exists_root f a e hem hy
    refine ⟨algebraMap V K β, ?_, ?_⟩
    · rw [hev, hβ, map_zero]
    · rw [← map_sub, hc, map_mul, norm_mul, he, norm_div, norm_pow]
      calc ‖algebraMap V K y‖ / ‖algebraMap V K d‖ ^ 2 * ‖algebraMap V K c‖
          ≤ ‖algebraMap V K y‖ / ‖algebraMap V K d‖ ^ 2 * 1 := by
            gcongr
            exact hint c
        _ = _ := mul_one _
  obtain ⟨N, hN0, hNm, hNf⟩ : ∃ N : ℕ, N ≠ 0 ∧ (N : V) ∈ IsLocalRing.maximalIdeal V ∧
      Finite (V ⧸ Ideal.span {(N : V)}) := by
    haveI : CharP (IsLocalRing.ResidueField V) (ringChar (IsLocalRing.ResidueField V)) :=
      ringChar.charP _
    refine ⟨ringChar (IsLocalRing.ResidueField V),
      CharP.char_ne_zero_of_finite (IsLocalRing.ResidueField V) _, ?_, ?_⟩
    · rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
      exact ringChar.Nat.cast_ringChar
    · have hne : Ideal.span {((ringChar (IsLocalRing.ResidueField V) : ℕ) : V)} ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact Nat.cast_ne_zero.mpr (CharP.char_ne_zero_of_finite (IsLocalRing.ResidueField V) _)
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
      obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
      haveI : Finite (V ⧸ IsLocalRing.maximalIdeal V) := hT
      have hfin := Ideal.finite_quotient_pow (IsNoetherian.noetherian (IsLocalRing.maximalIdeal V)) k
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, ← hk] at hfin
      exact hfin
  have hNK : ‖(N : K)‖ < 1 := by
    have := (hintlt (N : V)).mpr hNm
    simpa using this
  have hNne : (N : K) ≠ 0 := Nat.cast_ne_zero.mpr hN0
  have hdense : Dense {x : K | IsAlgebraic ℤ x} := by
    refine ModelDimension.Alg.dense_algebraic hH (fun z => ?_) N hN0 hNK (fun α hα => ?_)
    · simpa using hint (z : V)
    · haveI := hNf
      obtain ⟨m, hm⟩ := ModelDimension.Alg.exists_monic (V := V) N
      refine ⟨m, fun δ hδ => ?_⟩
      obtain ⟨a, rfl⟩ := hmem α hα
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ hNK
      obtain ⟨Q, hQm, hQd, c, hc⟩ := hm a k
      refine ⟨Q, hQm, hQd, ?_⟩
      rw [Polynomial.aeval_algebraMap_apply, hc, map_mul, norm_mul, map_pow, norm_pow, map_natCast]
      calc ‖(N : K)‖ ^ k * ‖algebraMap V K c‖ ≤ ‖(N : K)‖ ^ k * 1 := by
            gcongr
            exact hint c
        _ < δ := by rw [mul_one]; exact hk
  letI : Algebra F K := io.toAlgebra
  have hdF : Dense {x : K | IsAlgebraic F x} :=
    hdense.mono (fun x hx => IsAlgebraic.extendScalars (algebraMap ℤ F).injective_int hx)
  let ψa : R →ₐ[F] K := { ψ with commutes' := fun r => by exact RingHom.congr_fun hψ r }
  have hFZ : Algebra.IsAlgebraic ℤ F :=
    (IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).mpr inferInstance
  obtain ⟨ε, hε, hεn⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ d : K, ‖d‖ < ε → d = 0 ∨ (n : ℤ) ≤ vV V d := by
    refine ⟨(WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (WithZero.exp (-(n : ℤ))) : ℝ), ?_, ?_⟩
    · exact_mod_cast WithZeroMulInt.toNNReal_pos _ WithZero.exp_ne_zero
    · intro d hd
      by_cases h0 : d = 0
      · exact Or.inl h0
      right
      rw [hnorm] at hd
      have hlt : valV V d < WithZero.exp (-(n : ℤ)) :=
        (WithZeroMulInt.toNNReal_strictMono hb).lt_iff_lt.mp (by exact_mod_cast hd)
      have hne : valV V d ≠ 0 := (Valuation.ne_zero_iff _).mpr h0
      rw [← WithZero.exp_log hne, WithZero.exp_lt_exp] at hlt
      show (n : ℤ) ≤ -(valV V d).log
      omega
  obtain ⟨ψ', h1, h2, h3⟩ := ModelDimension.Alg.approx_smooth hH hNne hNK hdF ψa S ε hε g hg
  refine ⟨ψ'.toRingHom, ?_, fun x => ?_, fun s hs => ?_, h3⟩
  · ext r
    exact ψ'.commutes r
  · exact (h1 x).restrictScalars ℤ
  · rcases hεn _ (h2 s hs) with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr h

theorem ModelDimension.algebraic_approximation_valued : ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra F R] [Algebra.Smooth F R] (T : CDVR), T.FinRes → ∀ (io : F →+* T.Fr) (ψ : R →+* T.Fr), ψ.comp (algebraMap F R) = io → ∀ (S : Finset R) (n : ℕ) (g : R), g ≠ 0 → ∃ ψ' : R →+* T.Fr, ψ'.comp (algebraMap F R) = io ∧ (∀ x, IsAlgebraic ℤ (ψ' x)) ∧ (∀ s ∈ S, ψ' s = ψ s ∨ (n : ℤ) ≤ vV T.V (ψ' s - ψ s)) ∧ ψ' g ≠ 0 := by
  intro F _ _ R _ _ _ _ T hT io ψ hψ S n g hg
  letI := T.cr; letI := T.dom; letI := T.dvr; letI := T.cpl; letI := T.ch0
  obtain ⟨ψ', h1, h2, h3, h4⟩ :=
    ModelDimension.Alg.approx_dvr F R T.V (FractionRing T.V) hT io ψ hψ S n g hg
  refine ⟨ψ', h1, fun x => ?_, h3, h4⟩
  obtain ⟨p, hp, hpx⟩ := h2 x
  refine ⟨p, hp, ?_⟩
  simp only [Polynomial.aeval_def, algebraMap_int_eq] at hpx
  rw [Polynomial.aeval_def, show algebraMap ℤ T.Fr = Int.castRingHom T.Fr from RingHom.ext_int _ _]
  exact hpx

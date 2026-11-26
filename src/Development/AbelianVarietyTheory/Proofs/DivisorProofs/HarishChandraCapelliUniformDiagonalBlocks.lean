module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneFormSkew

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingMonicOperatorPolynomials
open Matrix GlobalTheory.LeviHC
open Formalism.REAL (GlRel qdet)

noncomputable section

namespace GlobalTheory.LeviHC.FactorMod

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem finMod_mono {K₁ K₂ : Submodule ℂ M} (h : K₁ ≤ K₂) {A : Subalgebra ℂ (Module.End ℂ M)} {v : M}
    (hf : FinMod K₁ A v) : FinMod K₂ A v := by
  unfold FinMod at *
  have e : Submodule.span ℂ {y : M ⧸ K₂ | ∃ a ∈ A, y = K₂.mkQ (a v)} =
      (Submodule.span ℂ {y : M ⧸ K₁ | ∃ a ∈ A, y = K₁.mkQ (a v)}).map (Submodule.factor h) := by
    rw [Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨K₁.mkQ (a v), ⟨a, ha, rfl⟩, Submodule.factor_mk h _⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, Submodule.factor_mk h _⟩
  rw [e]
  infer_instance

theorem comm_of_mem_adjoin {s : Set (Module.End ℂ M)} {f b : Module.End ℂ M} (hb : b ∈ Algebra.adjoin ℂ s)
    (h : ∀ g ∈ s, Commute f g) : Commute f b := by
  have hle : Algebra.adjoin ℂ s ≤ Subalgebra.centralizer ℂ {f} :=
    Algebra.adjoin_le fun g hg => (Subalgebra.mem_centralizer_iff ℂ).2 fun y hy => by
      rw [Set.mem_singleton_iff.1 hy]; exact (h g hg)
  exact (((Subalgebra.mem_centralizer_iff ℂ).1 (hle hb)) f rfl)

def core (K : Submodule ℂ M) (S : Subalgebra ℂ (Module.End ℂ M)) : Submodule ℂ M where
  carrier := {x | ∀ b ∈ S, b x ∈ K}
  add_mem' := fun hx hy b hb => by rw [map_add (f := _)]; exact K.add_mem (hx b hb) (hy b hb)
  zero_mem' := fun b _ => by rw [map_zero]; exact K.zero_mem
  smul_mem' := fun c x hx b hb => by rw [map_smul]; exact K.smul_mem c (hx b hb)

theorem core_le (K : Submodule ℂ M) (S : Subalgebra ℂ (Module.End ℂ M)) : core K S ≤ K := fun x hx => by
  simpa using hx 1 S.one_mem

theorem finMod_factor : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (M' K : Submodule ℂ M) (c p q : ℂ → Module.End ℂ M),
 (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
 (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, q u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
 (∀ u u', Commute (p u) (p u')) → (∀ u u', Commute (q u) (q u')) → (∀ u u', Commute (p u) (q u')) → (∀ u u', Commute (c u) (q u')) →
 (∀ u, ∀ x ∈ M', c u x ∈ M' ∧ p u x ∈ M' ∧ q u x ∈ M') → (∀ u, ∀ x ∈ K, p u x ∈ K) →
 (∀ u, ∀ x ∈ M', c u x - p u (q u x) ∈ K) →
 ∀ v ∈ M', FinMod ⊥ (Algebra.adjoin ℂ (Set.range c)) v → FinMod K (Algebra.adjoin ℂ (Set.range p)) v := by
  intro M _ _ M' K c p q hp hq hpp hqq hpq hcq hM hK hrel v hv hfin
  set S := Algebra.adjoin ℂ (Set.range q) with hS

  have cb : ∀ u, ∀ b ∈ S, Commute (c u) b := fun u b hb =>
    comm_of_mem_adjoin hb (by rintro _ ⟨u', rfl⟩; exact hcq u u')
  have pb : ∀ u, ∀ b ∈ S, Commute (p u) b := fun u b hb =>
    comm_of_mem_adjoin hb (by rintro _ ⟨u', rfl⟩; exact hpq u u')
  have qb : ∀ u, ∀ b ∈ S, Commute (q u) b := fun u b hb =>
    comm_of_mem_adjoin hb (by rintro _ ⟨u', rfl⟩; exact hqq u u')

  have hSM : ∀ b ∈ S, ∀ x ∈ M', b x ∈ M' := by
    have hle : S ≤ GlobalTheory.LeviHC.MidBlock.stab M' :=
      Algebra.adjoin_le (by rintro _ ⟨u, rfl⟩ x hx; exact (hM u x hx).2.2)
    intro b hb x hx
    exact hle hb x hx
  set K' := core K S
  have hK'p : ∀ u, ∀ x ∈ K', p u x ∈ K' ∧ q u x ∈ K' := by
    intro u x hx
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · have e : b (p u x) = p u (b x) := by
        have := (pb u b hb).eq
        exact (congrArg (fun f : Module.End ℂ M => f x) this).symm
      rw [e]; exact hK u _ (hx b hb)
    · have : b * q u ∈ S := S.mul_mem hb (Algebra.subset_adjoin ⟨u, rfl⟩)
      exact hx _ this
  have hrel' : ∀ u, ∀ x ∈ M', c u x - p u (q u x) ∈ K' := by
    intro u x hx b hb
    have e1 : b (c u x) = c u (b x) := (congrArg (fun f : Module.End ℂ M => f x) (cb u b hb).eq).symm
    have e2 : b (q u x) = q u (b x) := (congrArg (fun f : Module.End ℂ M => f x) (qb u b hb).eq).symm
    have e3 : b (p u (q u x)) = p u (b (q u x)) :=
      (congrArg (fun f : Module.End ℂ M => f (q u x)) (pb u b hb).eq).symm
    rw [map_sub, e1, e3, e2]
    exact hrel u _ (hSM b hb x hx)
  have h1 : FinMod K' (Algebra.adjoin ℂ (Set.range c)) v := finMod_mono bot_le hfin
  have h2 := GlobalTheory.LeviHC.QuotMonic.monicFactorFiniteMod_of GlobalTheory.LeviHC.monicFactorFinite M M' K' c p q hp hq hpp hqq hpq
    hM hK'p hrel' v hv h1
  exact finMod_mono (core_le K S) h2

end GlobalTheory.LeviHC.FactorMod

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyMapOfSum
open Matrix GlobalTheory.LeviHC
open Formalism.REAL (GlRel qdet)

noncomputable section

namespace GlobalTheory.LeviHC.MidThree

open GlobalTheory.LeviHC.MidBlock (stab mem_stab glComm comm_qdet)
open Polynomial

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem polyMap_of_sum {ι : Type} (s : Finset ι) (f : ι → ℂ[X]) (a : ι → A) (d : ℕ) (k₀ : ι) (hk₀ : k₀ ∈ s)
    (hm : (f k₀).Monic) (hd : (f k₀).natDegree = d) (hlt : ∀ k ∈ s, k ≠ k₀ → (f k).natDegree < d) :
    ∃ b : ℕ → A, b d = a k₀ ∧ ∀ u, ∑ k ∈ s, (f k).eval u • a k = ∑ i ∈ Finset.range (d + 1), u ^ i • b i := by
  refine ⟨fun i => ∑ k ∈ s, (f k).coeff i • a k, ?_, fun u => ?_⟩
  · show ∑ k ∈ s, (f k).coeff d • a k = a k₀
    rw [Finset.sum_eq_single_of_mem k₀ hk₀ fun k hk hne => by
      rw [coeff_eq_zero_of_natDegree_lt (hlt k hk hne), zero_smul]]
    rw [← hd, hm.coeff_natDegree, one_smul]
  · simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : (f k).natDegree < d + 1 := by
      by_cases h : k = k₀
      · rw [h, hd]; omega
      · have := hlt k hk h; omega
    rw [eval_eq_sum_range' hk', Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]

theorem monic_shift {p : ℂ → A} (t : ℂ)
    (hp : ∃ (d : ℕ) (a : ℕ → A), a d = 1 ∧ ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) :
    ∃ (d : ℕ) (a : ℕ → A), a d = 1 ∧ ∀ u, p (u - t) = ∑ i ∈ Finset.range (d + 1), u ^ i • a i := by
  obtain ⟨d, a, ha, hp⟩ := hp
  have hdeg : ∀ i, ((X - C t) ^ i).natDegree = i := fun i => by
    rw [(monic_X_sub_C t).natDegree_pow, natDegree_X_sub_C, mul_one]
  obtain ⟨b, hb, e⟩ := polyMap_of_sum (Finset.range (d + 1)) (fun i => (X - C t) ^ i) a d d
    (Finset.self_mem_range_succ d) ((monic_X_sub_C t).pow d) (hdeg d) fun k hk hne => by
      rw [hdeg]; have := Finset.mem_range.1 hk; omega
  refine ⟨d, b, hb.trans ha, fun u => ?_⟩
  rw [hp, ← e]
  simp

end Alg

end GlobalTheory.LeviHC.MidThree

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanAdjoin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanAdjoin
open NumberField

noncomputable section

open Polynomial

namespace GlobalTheory.CycSpanFin

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem commute_aeval_left {x y : Module.End ℂ V} (h : Commute x y) (p : ℂ[X]) : Commute (aeval x p) y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_left hq
  | monomial n a => rw [aeval_monomial]; exact (Algebra.commute_algebraMap_left a y).mul_left (h.pow_left n)

theorem coeff_mem_span_fin {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} {a : ℕ → M} {p : ℂ → M}
    (hp : ∀ u, p u = ∑ i ∈ Finset.range (n + 1), u ^ i • a i) {i : ℕ} (hi : i < n + 1) :
    a i ∈ Submodule.span ℂ (Set.range fun j : Fin (n + 1) => p ((j : ℕ) : ℂ)) := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  set Q : ℂ[X] := ∑ j ∈ Finset.range (n + 1), monomial j (φ (a j)) with hQdef
  have hev : ∀ u, Q.eval u = φ (p u) := by
    intro u
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hp, map_sum]
    simp only [Q, Polynomial.eval_finsetSum, eval_monomial]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, mul_comm]
  have hdeg : Q.natDegree ≤ n := by
    apply natDegree_sum_le_of_forall_le
    intro j hj
    exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  have h0 : Q = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q
      (f := fun j : Fin (n + 1) => ((j : ℕ) : ℂ)) (Nat.cast_injective.comp Fin.val_injective) ?_ ?_
    · intro j
      rw [hev]
      exact (Submodule.mem_dualAnnihilator φ).1 hφ _ (Submodule.subset_span ⟨j, rfl⟩)
    · simpa using Nat.lt_succ_of_le hdeg
  have hcoeff : Q.coeff i = 0 := by rw [h0, Polynomial.coeff_zero]
  rw [hQdef, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single_of_mem i (Finset.mem_range.2 hi), Polynomial.coeff_monomial_same] at hcoeff
  · exact hcoeff
  · intro j _ hji
    exact Polynomial.coeff_monomial_of_ne _ hji.symm

def stabAlg (N : Submodule ℂ V) : Subalgebra ℂ (Module.End ℂ V) where
  carrier := {T | ∀ v ∈ N, T v ∈ N}
  mul_mem' ha hb v hv := ha _ (hb v hv)
  add_mem' ha hb v hv := N.add_mem (ha v hv) (hb v hv)
  algebraMap_mem' r v hv := by
    rw [Module.algebraMap_end_apply]
    exact N.smul_mem r hv

def ext (T : Module.End ℂ V) (d : ℕ) (N : Submodule ℂ V) : Submodule ℂ V :=
  ⨆ k : Fin (d + 1), N.map (T ^ (k : ℕ))

theorem le_ext (T : Module.End ℂ V) (d : ℕ) (N : Submodule ℂ V) : N ≤ ext T d N := fun v hv =>
  Submodule.mem_iSup_of_mem (0 : Fin (d + 1)) ⟨v, hv, by simp⟩

theorem pow_mem_ext (T : Module.End ℂ V) {d k : ℕ} (hk : k ≤ d) {N : Submodule ℂ V} {v : V} (hv : v ∈ N) :
    (T ^ k) v ∈ ext T d N :=
  Submodule.mem_iSup_of_mem (⟨k, by omega⟩ : Fin (d + 1)) (Submodule.mem_map_of_mem hv)

theorem aeval_mem_ext (T : Module.End ℂ V) {Q : ℂ[X]} (hQ : Q ≠ 0) {N : Submodule ℂ V}
    (hN : ∀ v ∈ N, aeval T Q v = 0) (p : ℂ[X]) {v : V} (hv : v ∈ N) : aeval T p v ∈ ext T Q.natDegree N := by
  set Q' := Q * C Q.leadingCoeff⁻¹ with hQ'
  have hm : Q'.Monic := monic_mul_leadingCoeff_inv hQ
  have hdeg : Q'.natDegree = Q.natDegree := by
    rw [hQ', natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.2 hQ))]
  have hQ'v : aeval T Q' v = 0 := by
    rw [hQ', mul_comm, map_mul, mul_apply_eq_comp, hN v hv, map_zero]
  have hsplit : p = p %ₘ Q' + (p /ₘ Q') * Q' := by
    rw [mul_comm]; exact (modByMonic_add_div p Q').symm
  rw [hsplit, map_add (f := _), LinearMap.add_apply, map_mul, mul_apply_eq_comp, hQ'v, map_zero, add_zero]
  have hlt : (p %ₘ Q').natDegree < Q.natDegree + 1 := by
    have := natDegree_modByMonic_le p hm
    omega
  rw [aeval_eq_sum_range' hlt, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (pow_mem_ext T (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hv)

theorem ext_stable (T : Module.End ℂ V) {Q : ℂ[X]} (hQ : Q ≠ 0) {N : Submodule ℂ V}
    (hN : ∀ v ∈ N, aeval T Q v = 0) : ∀ v ∈ ext T Q.natDegree N, T v ∈ ext T Q.natDegree N := by
  have : ext T Q.natDegree N ≤ (ext T Q.natDegree N).comap T := by
    unfold ext
    refine iSup_le fun k => ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    rw [Submodule.mem_comap]
    change T ((T ^ (k : ℕ)) x) ∈ ext T Q.natDegree N
    have := aeval_mem_ext T hQ hN (X ^ ((k : ℕ) + 1)) hx
    rwa [map_pow, aeval_X, pow_succ', mul_apply_eq_comp] at this
  exact fun v hv => this hv

theorem ext_stable_comm (T S : Module.End ℂ V) (d : ℕ) (hST : Commute S T) {N : Submodule ℂ V}
    (hS : ∀ v ∈ N, S v ∈ N) : ∀ v ∈ ext T d N, S v ∈ ext T d N := by
  have : ext T d N ≤ (ext T d N).comap S := by
    unfold ext
    refine iSup_le fun k => ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    rw [Submodule.mem_comap]
    change S ((T ^ (k : ℕ)) x) ∈ ext T d N
    have h := congrArg (fun F : Module.End ℂ V => F x) (hST.pow_right (k : ℕ)).eq
    simp only [mul_apply_eq_comp] at h
    rw [h]
    exact pow_mem_ext T (Nat.lt_succ_iff.1 k.2) (hS x hx)
  exact fun v hv => this hv

theorem ext_kill (T R : Module.End ℂ V) (d : ℕ) (hRT : Commute R T) {N : Submodule ℂ V}
    (hN : ∀ v ∈ N, R v = 0) : ∀ v ∈ ext T d N, R v = 0 := by
  have : ext T d N ≤ LinearMap.ker R := by
    unfold ext
    refine iSup_le fun k => ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    rw [LinearMap.mem_ker]
    have h := congrArg (fun F : Module.End ℂ V => F x) (hRT.pow_right (k : ℕ)).eq
    simp only [mul_apply_eq_comp] at h
    rw [h, hN x hx, map_zero]
  exact fun v hv => this hv

theorem exists_stable (a : ℕ → Module.End ℂ V) (Q : ℕ → ℂ[X]) (hc : ∀ i j, Commute (a i) (a j))
    (hQ : ∀ j, Q j ≠ 0) (w : V) (hw : ∀ j, aeval (a j) (Q j) w = 0) : ∀ m : ℕ, ∃ N : Submodule ℂ V,
      FiniteDimensional ℂ N ∧ w ∈ N ∧ (∀ j < m, ∀ v ∈ N, a j v ∈ N) ∧ (∀ j, ∀ v ∈ N, aeval (a j) (Q j) v = 0) := by
  intro m
  induction m with
  | zero =>
    exact ⟨Submodule.span ℂ {w}, inferInstance, Submodule.mem_span_singleton_self w, by simp, fun j v hv => by
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hv
      rw [map_smul, hw, smul_zero]⟩
  | succ m ih =>
    obtain ⟨N, hf, hwN, hst, hk⟩ := ih
    refine ⟨ext (a m) (Q m).natDegree N, ?_, le_ext _ _ _ hwN, ?_, ?_⟩
    · unfold ext
      infer_instance
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
      · exact ext_stable_comm (a m) (a j) _ (hc j m) (hst j h)
      · subst j
        exact ext_stable (a m) (hQ m) (hk m)
    · intro j
      exact ext_kill (a m) _ _ (commute_aeval_left (hc j m) _) (hk j)

theorem finiteDimensional_span_adjoin : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (c : ℕ → Module.End ℂ V)
    (g : ℂ → Module.End ℂ V), (∀ u, g u = ∑ i ∈ Finset.range (n + 1), u ^ i • c i) → (∀ u u', Commute (g u) (g u')) →
    ∀ (w : V) (P : ℂ → Polynomial ℂ), (∀ u, P u ≠ 0) → (∀ u, Polynomial.aeval (g u) (P u) w = 0) →
    FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ b ∈ Algebra.adjoin ℂ (Set.range g), y = b w}) := by
  intro V _ _ n c g hg hc w P hP hw
  obtain ⟨N, hf, hwN, hst, -⟩ := exists_stable (fun j : ℕ => g (j : ℂ)) (fun j => P (j : ℂ))
    (fun i j => hc _ _) (fun j => hP _) w (fun j => hw _) (n + 1)
  have hgS : ∀ u, g u ∈ stabAlg N := by
    intro u
    have hspan : Submodule.span ℂ (Set.range fun j : Fin (n + 1) => g ((j : ℕ) : ℂ)) ≤
        Subalgebra.toSubmodule (stabAlg N) :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact fun v hv => hst j j.2 v hv)
    apply hspan
    rw [hg u]
    exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (coeff_mem_span_fin hg (Finset.mem_range.1 hi))
  have hA : Algebra.adjoin ℂ (Set.range g) ≤ stabAlg N :=
    Algebra.adjoin_le (by rintro _ ⟨u, rfl⟩; exact hgS u)
  have hle : Submodule.span ℂ {y | ∃ b ∈ Algebra.adjoin ℂ (Set.range g), y = b w} ≤ N :=
    Submodule.span_le.2 (by rintro _ ⟨b, hb, rfl⟩; exact hA hb w hwN)
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.CycSpanFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanAdjoinStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_span_adjoin_apply_of_annihilating : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (c : ℕ → Module.End ℂ V) (g : ℂ → Module.End ℂ V), (∀ u, g u = ∑ i ∈ Finset.range (n + 1), u ^ i • c i) → (∀ u u', Commute (g u) (g u')) → ∀ (w : V) (P : ℂ → Polynomial ℂ), (∀ u, P u ≠ 0) → (∀ u, Polynomial.aeval (g u) (P u) w = 0) → FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ b ∈ Algebra.adjoin ℂ (Set.range g), y = b w}) := by
  first | exact @GlobalTheory.CycSpanFin.finiteDimensional_span_adjoin | exact GlobalTheory.CycSpanFin.finiteDimensional_span_adjoin | (intros; apply GlobalTheory.CycSpanFin.finiteDimensional_span_adjoin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraCapelliUniformDiagonalBlocks
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.LeviHC.CapAlg

open GlobalTheory.LeviHC.MidBlock (stab mem_stab comm_qdet qdet_map)

theorem twoBlocks : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (r m : ℕ) (X : Fin (r + m) → Fin (r + m) → Module.End ℂ M), Formalism.REAL.GlRel X → ∀ M' K : Submodule ℂ M, (∀ i j, ∀ x ∈ M', X i j x ∈ M') → (∀ (p : Fin r) (q : Fin m), ∀ x ∈ M', X (Fin.castAdd m p) (Fin.natAdd r q) x ∈ K) → (∀ p q : Fin r, ∀ x ∈ K, X (Fin.castAdd m p) (Fin.castAdd m q) x ∈ K) → (∀ p q : Fin m, ∀ x ∈ K, X (Fin.natAdd r p) (Fin.natAdd r q) x ∈ K) → ∀ v ∈ M', GlobalTheory.LeviHC.FinMod ⊥ (Algebra.adjoin ℂ (Set.range (Formalism.REAL.qdet X))) v → GlobalTheory.LeviHC.FinMod K (Algebra.adjoin ℂ (Set.range (Formalism.REAL.qdet fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q)))) v ∧ GlobalTheory.LeviHC.FinMod K (Algebra.adjoin ℂ (Set.range (Formalism.REAL.qdet fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)))) v := by
  intro M _ _ r m X hX M' K hM hup hK1 hK2 v hv hfin
  let X' : Fin (r + m) → Fin (r + m) → stab M' := fun a b => ⟨X a b, mem_stab.2 (hM a b)⟩
  have hX' : Formalism.REAL.GlRel X' := by
    intro a b c d
    apply Subtype.ext
    have := hX a b c d
    split_ifs at this ⊢ <;> simpa [X'] using this
  have inj1 : Function.Injective (Fin.castAdd m : Fin r → Fin (r + m)) :=
    fun a b h => Fin.ext (by simpa using congrArg Fin.val h)
  have inj2 : Function.Injective (Fin.natAdd r : Fin m → Fin (r + m)) :=
    fun a b h => Fin.ext (by simpa using congrArg Fin.val h)
  have hX1 : Formalism.REAL.GlRel fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q) :=
    GlobalTheory.CapHC.glRel_restrict hX _ inj1
  have hX2 : Formalism.REAL.GlRel fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q) :=
    GlobalTheory.CapHC.glRel_restrict hX _ inj2
  set q₁ : ℂ → Module.End ℂ M := fun u => Formalism.REAL.qdet (fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q)) u
    with hq₁
  set q₂ : ℂ → Module.End ℂ M := fun u => Formalism.REAL.qdet (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)) u
    with hq₂
  have e : ∀ u, ∀ x ∈ M', Formalism.REAL.qdet X u x - q₂ u (q₁ (u - m) x) ∈ K := by
    intro u x hx
    have h := GlobalTheory.LeviHC.MidBlock.upperSpan_maps (K := K) X' (fun p q x hx => hup p q x hx)
      (GlobalTheory.CapHC.two_block X' hX' u) x hx
    change (stab M').val (_ - _ * _) x ∈ K at h
    rw [map_sub, map_mul, qdet_map, qdet_map, qdet_map] at h
    exact h
  have c12 : ∀ u u', Commute (q₁ u) (q₂ u') := fun u u' => (GlobalTheory.CapHC.qdet_comm hX u' u).symm
  have c11 : ∀ u u', Commute (q₁ u) (q₁ u') := fun u u' =>
    comm_qdet (fun a b => Formalism.REAL.qDetCentral _ r _ hX1 u a b) u'
  have c22 : ∀ u u', Commute (q₂ u) (q₂ u') := fun u u' =>
    comm_qdet (fun a b => Formalism.REAL.qDetCentral _ m _ hX2 u a b) u'
  have constantCoeff_threeGroupsFirstVariables_eq_zero : ∀ u u', Commute (Formalism.REAL.qdet X u) (q₁ u') := fun u u' =>
    comm_qdet (fun a b => Formalism.REAL.qDetCentral _ _ _ hX u _ _) u'
  have constantCoeff_threeGroupsSecondVariables_eq_zero : ∀ u u', Commute (Formalism.REAL.qdet X u) (q₂ u') := fun u u' =>
    comm_qdet (fun a b => Formalism.REAL.qDetCentral _ _ _ hX u _ _) u'
  have mon1 : ∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, q₁ u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i := by
    obtain ⟨c, hc1, hc⟩ := GlobalTheory.qdet_polyMap_monic (Module.End ℂ M) r (fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q))
    exact ⟨r, c, hc1, hc⟩
  have mon2 : ∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, q₂ u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i := by
    obtain ⟨c, hc1, hc⟩ := GlobalTheory.qdet_polyMap_monic (Module.End ℂ M) m (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q))
    exact ⟨m, c, hc1, hc⟩
  have mon1' := GlobalTheory.LeviHC.MidThree.monic_shift (m : ℂ) mon1
  have sM : ∀ {n : ℕ} (f : Fin n → Fin (r + m)) (u : ℂ), ∀ x ∈ M',
      Formalism.REAL.qdet (fun p q : Fin n => X (f p) (f q)) u x ∈ M' :=
    fun f u => mem_stab.1 (GlobalTheory.LeviHC.MidBlock.qdet_mem (stab M') (fun a b => mem_stab.2 (hM _ _)) u)
  have sMX : ∀ u, ∀ x ∈ M', Formalism.REAL.qdet X u x ∈ M' :=
    fun u => mem_stab.1 (GlobalTheory.LeviHC.MidBlock.qdet_mem (stab M') (fun a b => mem_stab.2 (hM a b)) u)
  have sK1 : ∀ u, ∀ x ∈ K, q₁ u x ∈ K :=
    fun u => mem_stab.1 (GlobalTheory.LeviHC.MidBlock.qdet_mem (stab K) (fun a b => mem_stab.2 (hK1 a b)) u)
  have sK2 : ∀ u, ∀ x ∈ K, q₂ u x ∈ K :=
    fun u => mem_stab.1 (GlobalTheory.LeviHC.MidBlock.qdet_mem (stab K) (fun a b => mem_stab.2 (hK2 a b)) u)
  have hr1 : Set.range (fun u => q₁ (u - m)) = Set.range q₁ := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨u, rfl⟩; exact ⟨u + m, by simp⟩
  refine ⟨?_, ?_⟩
  · have h := GlobalTheory.LeviHC.FactorMod.finMod_factor M M' K (Formalism.REAL.qdet X) (fun u => q₁ (u - m)) q₂ mon1' mon2
      (fun u u' => c11 _ _) c22 (fun u u' => c12 _ _) constantCoeff_threeGroupsSecondVariables_eq_zero
      (fun u x hx => ⟨sMX u x hx, sM _ _ x hx, sM _ _ x hx⟩) (fun u x hx => sK1 _ x hx)
      (fun u x hx => by
        have h := e u x hx
        have hc := LinearMap.congr_fun (c12 (u - m) u).eq x
        simp only [Module.End.mul_apply] at hc
        rwa [hc]) v hv hfin
    rwa [hr1] at h
  · exact GlobalTheory.LeviHC.FactorMod.finMod_factor M M' K (Formalism.REAL.qdet X) q₂ (fun u => q₁ (u - m)) mon2 mon1'
      c22 (fun u u' => c11 _ _) (fun u u' => (c12 _ _).symm) (fun u u' => constantCoeff_threeGroupsFirstVariables_eq_zero _ _)
      (fun u x hx => ⟨sMX u x hx, sM _ _ x hx, sM _ _ x hx⟩) (fun u x hx => sK2 _ x hx) e v hv hfin

theorem finDim : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (c : ℕ → Module.End ℂ V) (g : ℂ → Module.End ℂ V), (∀ u, g u = ∑ i ∈ Finset.range (n + 1), u ^ i • c i) → (∀ u u', Commute (g u) (g u')) → ∀ (w : V) (P : ℂ → Polynomial ℂ), (∀ u, P u ≠ 0) → (∀ u, Polynomial.aeval (g u) (P u) w = 0) → FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ b ∈ Algebra.adjoin ℂ (Set.range g), y = b w}) := GlobalTheory.T.finiteDimensional_span_adjoin_apply_of_annihilating

theorem exists_poly {V : Type} [AddCommGroup V] [Module ℂ V] (K : Submodule ℂ V) (A : Subalgebra ℂ (Module.End ℂ V))
    {T : Module.End ℂ V} (hT : T ∈ A) (w : V) (hf : FinMod K A w) :
    ∃ p : Polynomial ℂ, p ≠ 0 ∧ Polynomial.aeval T p w ∈ K := by
  unfold FinMod at hf
  set W := Submodule.span ℂ {y : V ⧸ K | ∃ a ∈ A, y = K.mkQ (a w)}
  let f : ℕ → W := fun k => ⟨K.mkQ ((T ^ k) w), Submodule.subset_span ⟨T ^ k, A.pow_mem hT k, rfl⟩⟩
  have hnli : ¬ LinearIndependent ℂ f := Module.Finite.not_linearIndependent_of_infinite f
  obtain ⟨s, c, hs, i, hi, hci⟩ := not_linearIndependent_iff.1 hnli
  refine ⟨∑ k ∈ s, Polynomial.monomial k (c k), fun h0 => hci ?_, ?_⟩
  · have := congrArg (fun p : Polynomial ℂ => p.coeff i) h0
    simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply, hi] using this
  · have ev : (Polynomial.aeval T (∑ k ∈ s, Polynomial.monomial k (c k))) w = ∑ k ∈ s, c k • (T ^ k) w := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, Polynomial.aeval_monomial, Module.algebraMap_end_apply]
    have := congrArg Subtype.val hs
    simp only [Submodule.coe_sum, Submodule.coe_smul, f, ZeroMemClass.coe_zero] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, ev, map_sum]
    simpa using this

def liftHom (I : Type) (M : Type) [AddCommGroup M] [Module ℂ M] : Module.End ℂ M →ₐ[ℂ] Module.End ℂ (I → M) where
  toFun f := f.compLeft I
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' c := by
    ext g i
    simp [Module.algebraMap_end_apply]

theorem glRel_map {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) {n : ℕ}
    {X : Fin n → Fin n → A} (hX : Formalism.REAL.GlRel X) : Formalism.REAL.GlRel fun i j => φ (X i j) := by
  intro a b c d
  have := congrArg φ (hX a b c d)
  simp only [map_sub, map_mul] at this
  rw [this]
  split_ifs <;> simp

theorem stab_aeval {M : Type} [AddCommGroup M] [Module ℂ M] {K : Submodule ℂ M} {T : Module.End ℂ M}
    (hT : ∀ x ∈ K, T x ∈ K) (p : Polynomial ℂ) : ∀ x ∈ K, Polynomial.aeval T p x ∈ K := by
  have h : Polynomial.aeval T p ∈ stab K :=
    Algebra.adjoin_le (s := {T}) (by rintro _ rfl; exact mem_stab.2 hT) (Polynomial.aeval_mem_adjoin_singleton ℂ T)
  exact mem_stab.1 h

theorem core (M : Type) [AddCommGroup M] [Module ℂ M] (r m : ℕ) (X : Fin (r + m) → Fin (r + m) → Module.End ℂ M)
    (hX : Formalism.REAL.GlRel X) (M' K : Submodule ℂ M) (hM : ∀ i j, ∀ x ∈ M', X i j x ∈ M')
    (hup : ∀ (p : Fin r) (q : Fin m), ∀ x ∈ M', X (Fin.castAdd m p) (Fin.natAdd r q) x ∈ K)
    (hK1 : ∀ p q : Fin r, ∀ x ∈ K, X (Fin.castAdd m p) (Fin.castAdd m q) x ∈ K)
    (hK2 : ∀ p q : Fin m, ∀ x ∈ K, X (Fin.natAdd r p) (Fin.natAdd r q) x ∈ K)
    (Q : ℂ → Polynomial ℂ) (hQ : ∀ u, Q u ≠ 0) :
    ∃ q : ℂ → Polynomial ℂ, (∀ u, q u ≠ 0) ∧ ∀ v ∈ M', (∀ u, Polynomial.aeval (Formalism.REAL.qdet X u) (Q u) v = 0) →
      ∀ u, Polynomial.aeval (Formalism.REAL.qdet (fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q)) u) (q u) v ∈ K ∧
        Polynomial.aeval (Formalism.REAL.qdet (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)) u) (q u) v ∈ K := by

  let I := {v : M // v ∈ M' ∧ ∀ u, Polynomial.aeval (Formalism.REAL.qdet X u) (Q u) v = 0}
  let φ := liftHom I M
  let Y : Fin (r + m) → Fin (r + m) → Module.End ℂ (I → M) := fun i j => φ (X i j)
  have hY : Formalism.REAL.GlRel Y := glRel_map φ hX
  let M'' : Submodule ℂ (I → M) := Submodule.pi Set.univ fun _ => M'
  let K'' : Submodule ℂ (I → M) := Submodule.pi Set.univ fun _ => K
  have memM : ∀ g : I → M, g ∈ M'' ↔ ∀ i, g i ∈ M' := fun g => by simp [M'', Submodule.mem_pi]
  have memK : ∀ g : I → M, g ∈ K'' ↔ ∀ i, g i ∈ K := fun g => by simp [K'', Submodule.mem_pi]
  let w : I → M := fun i => i.1
  have hw : w ∈ M'' := (memM w).2 fun i => i.2.1
  have hqY : ∀ {n : ℕ} (f : Fin n → Fin (r + m)) (u : ℂ),
      Formalism.REAL.qdet (fun p q => Y (f p) (f q)) u = φ (Formalism.REAL.qdet (fun p q => X (f p) (f q)) u) :=
    fun f u => (qdet_map φ _ u).symm
  have hq0 : ∀ u, Formalism.REAL.qdet Y u = φ (Formalism.REAL.qdet X u) := fun u => (qdet_map φ X u).symm

  have hfin : FinMod ⊥ (Algebra.adjoin ℂ (Set.range (Formalism.REAL.qdet Y))) w := by
    obtain ⟨c, -, hc⟩ := GlobalTheory.qdet_polyMap_monic (Module.End ℂ M) (r + m) X
    have hd := finDim (I → M) (r + m) (fun i => φ (c i)) (Formalism.REAL.qdet Y)
      (fun u => by rw [hq0 u]; simp only [hc u, map_sum, map_smul])
      (fun u u' => by
        rw [hq0 u, hq0 u']
        exact (comm_qdet (fun a b => Formalism.REAL.qDetCentral _ _ _ hX u a b) u').map φ)
      w Q hQ (fun u => by
        rw [hq0 u, Polynomial.aeval_algHom_apply]
        funext i
        exact i.2.2 u)
    unfold FinMod
    have e : Submodule.span ℂ {y : (I → M) ⧸ (⊥ : Submodule ℂ (I → M)) |
        ∃ a ∈ Algebra.adjoin ℂ (Set.range (Formalism.REAL.qdet Y)), y = (⊥ : Submodule ℂ (I → M)).mkQ (a w)} =
        (Submodule.span ℂ {y | ∃ b ∈ Algebra.adjoin ℂ (Set.range (Formalism.REAL.qdet Y)), y = b w}).map
          (⊥ : Submodule ℂ (I → M)).mkQ := by
      rw [Submodule.map_span]
      congr 1
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ⟨a w, ⟨a, ha, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨a, ha, rfl⟩
    rw [e]
    infer_instance
  obtain ⟨h1, h2⟩ := twoBlocks (I → M) r m Y hY M'' K''
    (fun i j g hg => (memM _).2 fun k => hM i j _ ((memM g).1 hg k))
    (fun p q g hg => (memK _).2 fun k => hup p q _ ((memM g).1 hg k))
    (fun p q g hg => (memK _).2 fun k => hK1 p q _ ((memK g).1 hg k))
    (fun p q g hg => (memK _).2 fun k => hK2 p q _ ((memK g).1 hg k)) w hw hfin
  have P1 : ∀ u, ∃ p : Polynomial ℂ, p ≠ 0 ∧ Polynomial.aeval
      (Formalism.REAL.qdet (fun p q : Fin r => Y (Fin.castAdd m p) (Fin.castAdd m q)) u) p w ∈ K'' :=
    fun u => exists_poly K'' _ (Algebra.subset_adjoin (Set.mem_range_self u)) w h1
  have P2 : ∀ u, ∃ p : Polynomial ℂ, p ≠ 0 ∧ Polynomial.aeval
      (Formalism.REAL.qdet (fun p q : Fin m => Y (Fin.natAdd r p) (Fin.natAdd r q)) u) p w ∈ K'' :=
    fun u => exists_poly K'' _ (Algebra.subset_adjoin (Set.mem_range_self u)) w h2
  choose p₁ hp₁ hk₁ using P1
  choose p₂ hp₂ hk₂ using P2
  refine ⟨fun u => p₁ u * p₂ u, fun u => mul_ne_zero (hp₁ u) (hp₂ u), fun v hv hQv u => ?_⟩
  let i : I := ⟨v, hv, hQv⟩
  have e1 : Polynomial.aeval (Formalism.REAL.qdet (fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q)) u) (p₁ u) v ∈ K := by
    have := (memK _).1 (hk₁ u) i
    rwa [hqY (fun p => Fin.castAdd m p) u, Polynomial.aeval_algHom_apply] at this
  have e2 : Polynomial.aeval (Formalism.REAL.qdet (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)) u) (p₂ u) v ∈ K := by
    have := (memK _).1 (hk₂ u) i
    rwa [hqY (fun p => Fin.natAdd r p) u, Polynomial.aeval_algHom_apply] at this
  have s1 : ∀ x ∈ K, Formalism.REAL.qdet (fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q)) u x ∈ K :=
    mem_stab.1 (GlobalTheory.LeviHC.MidBlock.qdet_mem (stab K) (fun a b => mem_stab.2 (hK1 a b)) u)
  have s2 : ∀ x ∈ K, Formalism.REAL.qdet (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)) u x ∈ K :=
    mem_stab.1 (GlobalTheory.LeviHC.MidBlock.qdet_mem (stab K) (fun a b => mem_stab.2 (hK2 a b)) u)
  refine ⟨?_, ?_⟩ <;> dsimp only
  · rw [mul_comm, Polynomial.aeval_mul, Module.End.mul_apply]
    exact stab_aeval s1 _ _ e1
  · rw [Polynomial.aeval_mul, Module.End.mul_apply]
    exact stab_aeval s2 _ _ e2

theorem qdet_cast {A : Type} [Ring A] [Algebra ℂ A] {k m : ℕ} (h : k = m) (Z : Fin m → Fin m → A) (u : ℂ) :
    Formalism.REAL.qdet (fun p q : Fin k => Z (Fin.cast h p) (Fin.cast h q)) u = Formalism.REAL.qdet Z u := by
  subst h; rfl

theorem capalg : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (a r : ℕ) (hr : r ≤ a) (X : Fin a → Fin a → Module.End ℂ M), Formalism.REAL.GlRel X → ∀ M' K : Submodule ℂ M, (∀ i j, ∀ x ∈ M', X i j x ∈ M') → (∀ i j : Fin a, (i : ℕ) < r → r ≤ (j : ℕ) → ∀ x ∈ M', X i j x ∈ K) → (∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) → ∀ x ∈ K, X i j x ∈ K) → ∀ Q : ℂ → Polynomial ℂ, (∀ u, Q u ≠ 0) → ∃ q : ℂ → Polynomial ℂ, (∀ u, q u ≠ 0) ∧ ∀ v ∈ M', (∀ u, Polynomial.aeval (Formalism.REAL.qdet X u) (Q u) v = 0) → ∀ u, Polynomial.aeval (Formalism.REAL.qdet (fun p p' : Fin r => X (GlobalTheory.LeviGA.blkEquiv hr (Sum.inl p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inl p'))) u) (q u) v ∈ K ∧ Polynomial.aeval (Formalism.REAL.qdet (fun p p' : Fin (a - r) => X (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p'))) u) (q u) v ∈ K := by
  intro M _ _ a r hr X hX M' K hM hup hK Q hQ
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hr
  obtain ⟨q, hq, h⟩ := core M r m X hX M' K hM
    (fun p q x hx => hup _ _ (by simp) (by simp) x hx)
    (fun p q x hx => hK _ _ (by simp) x hx) (fun p q x hx => hK _ _ (by simp) x hx) Q hQ
  refine ⟨q, hq, fun v hv hQv u => ?_⟩
  obtain ⟨h1, h2⟩ := h v hv hQv u
  have e1 : (fun p p' : Fin r => X (GlobalTheory.LeviGA.blkEquiv hr (Sum.inl p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inl p'))) =
      fun p q => X (Fin.castAdd m p) (Fin.castAdd m q) := by
    funext p p'
    congr 1 <;> exact Fin.ext (by simp)
  have hm : r + m - r = m := by omega
  have e2 : (fun p p' : Fin (r + m - r) => X (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p'))) =
      fun p p' => (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)) (Fin.cast hm p) (Fin.cast hm p') := by
    funext p p'
    congr 1 <;> exact Fin.ext (by simp)
  have e3 : Formalism.REAL.qdet (fun p p' : Fin (r + m - r) => X (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p))
      (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p'))) u = Formalism.REAL.qdet (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)) u := by
    rw [e2]; exact qdet_cast hm (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)) u
  rw [e1, e3]
  exact ⟨h1, h2⟩

end GlobalTheory.LeviHC.CapAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraCapelliUniformDiagonalBlocksStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandra_capelli_uniform_diagonalBlocks : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (a r : ℕ) (hr : r ≤ a) (X : Fin a → Fin a → Module.End ℂ M), Formalism.REAL.GlRel X → ∀ M' K : Submodule ℂ M, (∀ i j, ∀ x ∈ M', X i j x ∈ M') → (∀ i j : Fin a, (i : ℕ) < r → r ≤ (j : ℕ) → ∀ x ∈ M', X i j x ∈ K) → (∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) → ∀ x ∈ K, X i j x ∈ K) → ∀ Q : ℂ → Polynomial ℂ, (∀ u, Q u ≠ 0) → ∃ q : ℂ → Polynomial ℂ, (∀ u, q u ≠ 0) ∧ ∀ v ∈ M', (∀ u, Polynomial.aeval (Formalism.REAL.qdet X u) (Q u) v = 0) → ∀ u, Polynomial.aeval (Formalism.REAL.qdet (fun p p' : Fin r => X (GlobalTheory.LeviGA.blkEquiv hr (Sum.inl p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inl p'))) u) (q u) v ∈ K ∧ Polynomial.aeval (Formalism.REAL.qdet (fun p p' : Fin (a - r) => X (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p'))) u) (q u) v ∈ K := by
  first | exact @GlobalTheory.LeviHC.CapAlg.capalg | exact GlobalTheory.LeviHC.CapAlg.capalg | (intros; apply GlobalTheory.LeviHC.CapAlg.capalg <;> assumption)
end

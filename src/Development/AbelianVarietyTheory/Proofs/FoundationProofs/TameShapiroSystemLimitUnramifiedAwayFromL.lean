module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnivNormUnramOfOrderOf
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

noncomputable section

namespace GlobalTheory.KA.UnivNorm

theorem norm_nat_eq {l : ℕ} [Fact l.Prime] (n : ℕ) : ‖(n : Qbar l)‖ = ‖(n : ℚ_[l])‖ := by
  rw [← PadicAlgCl.norm_extends l (n : ℚ_[l])]; simp

theorem norm_l_lt_one {l : ℕ} [Fact l.Prime] : ‖(l : Qbar l)‖ < 1 := by
  rw [norm_nat_eq]; exact Padic.norm_p_lt_one

theorem norm_nat_of_coprime {l : ℕ} [Fact l.Prime] {n : ℕ} (h : n.Coprime l) : ‖(n : Qbar l)‖ = 1 := by
  rw [norm_nat_eq]; exact Padic.norm_natCast_eq_one_iff.2 h.symm

def Bd {l : ℕ} [Fact l.Prime] {n : Type} (δ : ℝ) (X : Matrix n n (Qbar l)) : Prop := ∀ i k, ‖X i k‖ ≤ δ

theorem Bd.mul {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] {a b : ℝ} {X Y : Matrix n n (Qbar l)} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hX : Bd a X) (hY : Bd b Y) : Bd (a * b) (X * Y) := fun i k => by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun j _ => ?_
  rw [norm_mul]; exact mul_le_mul (hX i j) (hY j k) (norm_nonneg _) ha

theorem Bd.add {l : ℕ} [Fact l.Prime] {n : Type} {a : ℝ} {X Y : Matrix n n (Qbar l)}
    (hX : Bd a X) (hY : Bd a Y) : Bd a (X + Y) := fun i k =>
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hX i k) (hY i k))

theorem exists_open_ker {Γ : Type} [Group Γ] [TopologicalSpace Γ] {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] [DecidableEq n]
    (M : Γ →* Matrix n n (Qbar l)) (hcop : ∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) → U.index.Coprime l)
    (hc : ∀ i k, Continuous fun s => M s i k) (h1 : ∀ s, Bd 1 (M s)) :
    ∃ N : Subgroup Γ, N.Normal ∧ IsOpen (N : Set Γ) ∧ ∀ s ∈ N, M s = 1 := by
  have hinv : ∀ g, M g * M g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  have hinv' : ∀ g, M g⁻¹ * M g = 1 := fun g => by rw [← map_mul, inv_mul_cancel, map_one]
  let N : ∀ ε : ℝ, 0 < ε → Subgroup Γ := fun ε hε =>
    { carrier := {s | Bd ε (M s - 1)}
      one_mem' := fun i k => by simp [hε.le]
      mul_mem' := fun {a b} ha hb => by
        have e : M (a * b) - 1 = M a * (M b - 1) + (M a - 1) := by rw [map_mul, mul_sub, mul_one]; abel
        have := Bd.mul zero_le_one hε.le (h1 a) hb
        rw [one_mul] at this
        show Bd ε _
        rw [e]; exact this.add ha
      inv_mem' := fun {a} ha i k => by
        have e : M a⁻¹ - 1 = -(M a⁻¹ * (M a - 1)) := by rw [mul_sub, mul_one, hinv', neg_sub]
        have := Bd.mul zero_le_one hε.le (h1 a⁻¹) ha i k
        rw [one_mul] at this
        rw [e, Matrix.neg_apply, norm_neg]; exact this }
  have hn : ∀ ε hε, (N ε hε).Normal := fun ε hε => ⟨fun a ha g => by
    have e : M (g * a * g⁻¹) - 1 = M g * (M a - 1) * M g⁻¹ := by
      rw [map_mul, map_mul, mul_sub, sub_mul, mul_one, hinv]
    have := Bd.mul (mul_nonneg zero_le_one hε.le) zero_le_one (Bd.mul zero_le_one hε.le (h1 g) ha) (h1 g⁻¹)
    rw [one_mul, mul_one] at this
    show Bd ε _
    rw [e]; exact this⟩
  have ho : ∀ ε hε, IsOpen (N ε hε : Set Γ) := fun ε hε => by
    have e : (N ε hε : Set Γ) = ⋂ i, ⋂ k, (fun s => M s i k) ⁻¹' Metric.closedBall ((1 : Matrix n n (Qbar l)) i k) ε := by
      ext s
      simp only [Set.mem_iInter, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
      rfl
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k =>
      (IsUltrametricDist.isOpen_closedBall _ hε.ne').preimage (hc i k)
  have hc0 : 0 < ‖(l : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have step : ∀ ε hε, ε ≤ ‖(l : Qbar l)‖ → ∀ s ∈ N ε hε, s ∈ N (‖(l : Qbar l)‖ * ε) (mul_pos hc0 hε) := by
    intro ε hε hle s hs
    have h2 : Bd ‖(l : Qbar l)‖ (∑ i ∈ Finset.range l, M s ^ i) := by
      have e : ∑ i ∈ Finset.range l, M s ^ i = ∑ i ∈ Finset.range l, (M (s ^ i) - 1) + (l : Matrix n n (Qbar l)) := by
        simp [Finset.sum_sub_distrib]
      rw [e]
      refine Bd.add (fun i k => ?_) (fun i k => ?_)
      · rw [Matrix.sum_apply]
        exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc0.le fun j _ =>
          (((N ε hε).pow_mem hs j) i k).trans hle
      · rw [Matrix.natCast_apply]; split_ifs <;> simp
    have h3 : s ^ l ∈ N _ (mul_pos hc0 hε) := by
      show Bd _ _
      rw [map_pow, ← geom_sum_mul]
      exact Bd.mul hc0.le hε.le h2 hs
    have := hn _ (mul_pos hc0 hε)
    have h4 : (QuotientGroup.mk s : Γ ⧸ N _ (mul_pos hc0 hε)) ^ l = 1 := (QuotientGroup.eq_one_iff _).2 h3
    have h5 : (QuotientGroup.mk s : Γ ⧸ N _ (mul_pos hc0 hε)) ^ (N _ (mul_pos hc0 hε)).index = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.pow_index_mem _ s)
    exact (QuotientGroup.eq_one_iff _).1 ((pow_eq_one_iff_of_coprime (hcop _ this (ho _ (mul_pos hc0 hε)))).1 ⟨h5, h4⟩)
  refine ⟨N _ hc0, hn _ hc0, ho _ hc0, fun s hs => ?_⟩
  have hk : ∀ k : ℕ, s ∈ N (‖(l : Qbar l)‖ ^ (k + 1)) (pow_pos hc0 _) := fun k => by
    induction k with
    | zero => show Bd _ _; rw [zero_add, pow_one]; exact hs
    | succ k ih =>
      have := step _ (pow_pos hc0 _) (pow_le_of_le_one hc0.le norm_l_lt_one.le k.succ_ne_zero) s ih
      show Bd _ _
      rw [pow_succ']; exact this
  rw [← sub_eq_zero]
  ext i k
  by_contra hne
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hne) (norm_l_lt_one (l := l))
  exact absurd ((hk m i k).trans (pow_le_pow_of_le_one hc0.le norm_l_lt_one.le m.le_succ)) (not_le.2 hm)

theorem exists_cob_of_index {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] (ρ : Γ → Matrix (Fin 2) (Fin 2) (Qbar l))
    (z : Γ → Fin 2 → Qbar l) (N : Subgroup Γ) (hN : N.index.Coprime l) (h0 : ∀ s ∈ N, z s = 0)
    (hz : ∀ s i, ‖z s i‖ ≤ 1) (hc : ∀ s t, z (s * t) = z s + ρ s *ᵥ z t) :
    ∃ v : Fin 2 → Qbar l, (∀ i, ‖v i‖ ≤ 1) ∧ ∀ j, z j = ρ j *ᵥ v - v := by
  have hn1 := norm_nat_of_coprime hN
  have hn0 : (N.index : Qbar l) ≠ 0 := fun h => by simp [h] at hn1
  have : N.FiniteIndex := ⟨fun h => hn0 (by simp [h])⟩
  let : Fintype (Γ ⧸ N) := Fintype.ofFinite _
  have hq : ∀ a b : Γ, (a : Γ ⧸ N) = b → z b = z a := fun a b h => by
    have := hc a (a⁻¹ * b)
    rwa [mul_inv_cancel_left, h0 _ (QuotientGroup.eq.1 h), Matrix.mulVec_zero, add_zero] at this
  set S := ∑ ω : Γ ⧸ N, z ω.out with hS
  have key : ∀ g, (N.index : Qbar l) • z g + ρ g *ᵥ S = S := fun g => by
    have e1 : ∑ ω : Γ ⧸ N, z (g * ω.out) = S := by
      rw [hS, ← Equiv.sum_comp (MulAction.toPerm g) fun ω : Γ ⧸ N => z ω.out]
      refine Finset.sum_congr rfl fun ω _ => hq _ _ ?_
      rw [QuotientGroup.out_eq', MulAction.toPerm_apply]
      exact (MulAction.Quotient.coe_smul_out N g ω).symm
    conv_rhs => rw [← e1]
    simp only [hc, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hS, Matrix.mulVec_sum]
    rw [Nat.cast_smul_eq_nsmul, Subgroup.index, Nat.card_eq_fintype_card]
  refine ⟨-((N.index : Qbar l)⁻¹ • S), fun i => ?_, fun j => ?_⟩
  · rw [Pi.neg_apply, norm_neg, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, hn1, inv_one, one_mul, hS, Finset.sum_apply]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun ω _ => hz _ i
  · have := eq_sub_of_add_eq (key j)
    rw [Matrix.mulVec_neg, Matrix.mulVec_smul, neg_sub_neg, ← smul_sub, ← this, inv_smul_smul₀ hn0]

theorem exists_pow_fix {K C : Type} [Field K] [AddCommGroup C] [Module K C] [FiniteDimensional K C] (T : Module.End K C) :
    ∃ E, 0 < E ∧ ∀ d, 0 < d → ∀ c, (T ^ d) c = c → (T ^ E) c = c := by
  have hm : ∀ d m c, (T ^ d) c = c → (T ^ (d * m)) c = c := fun d m c h => by
    induction m with
    | zero => simp
    | succ m ih => rw [mul_add, mul_one, pow_add, Module.End.mul_apply, h, ih]
  obtain ⟨_, ⟨E, hE, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian K C)
    {U | ∃ n, 0 < n ∧ U = LinearMap.eqLocus (T ^ n) LinearMap.id} ⟨_, 1, one_pos, rfl⟩
  refine ⟨E, hE, fun d hd c hc => ?_⟩
  have h1 : LinearMap.eqLocus (T ^ E) LinearMap.id ≤ LinearMap.eqLocus (T ^ (E * d)) LinearMap.id := fun x hx => hm E d x hx
  have h2 := eq_of_le_of_not_lt h1 (hmax _ ⟨E * d, mul_pos hE hd, rfl⟩)
  have h3 : c ∈ LinearMap.eqLocus (T ^ (E * d)) LinearMap.id := by rw [mul_comm]; exact hm d E c hc
  rw [← h2] at h3
  exact h3

theorem isClosed_submodule {l : ℕ} [Fact l.Prime] (U : Submodule (Qbar l) (Fin 2 → Qbar l)) :
    IsClosed (U : Set (Fin 2 → Qbar l)) := by
  refine isClosed_of_closure_subset fun b hb => ?_
  by_contra h
  obtain ⟨f, h1, h2⟩ := U.exists_le_ker_of_notMem h
  exact h1 (closure_minimal (t := {x | f x = 0}) h2 (isClosed_eq f.continuous_on_pi continuous_const) hb)

theorem sum_eq_orderOf_smul {X C : Type} [Group X] [Fintype X] [AddCommMonoid C] (h : X) (f : X → C)
    (hf : ∀ x, f (x * h) = f x) [Fintype (X ⧸ Subgroup.zpowers h)] :
    ∑ x, f x = orderOf h • ∑ ω : X ⧸ Subgroup.zpowers h, f ω.out := by
  classical
  have h1 : ∀ x, ∀ t ∈ Subgroup.zpowers h, f (x * t) = f x := fun x t ht => by
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 ht)
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, hf, ih (pow_mem (Subgroup.mem_zpowers h) n)]
  have h2 : Function.Bijective fun p : (X ⧸ Subgroup.zpowers h) × Subgroup.zpowers h => p.1.out * (p.2 : X) := by
    rw [Fintype.bijective_iff_surjective_and_card]
    refine ⟨fun x => ⟨(x, ⟨(x : X ⧸ Subgroup.zpowers h).out⁻¹ * x, QuotientGroup.eq.1 (QuotientGroup.out_eq' _)⟩), by simp⟩, ?_⟩
    simp only [← Nat.card_eq_fintype_card, Nat.card_prod]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm
  rw [← h2.sum_comp f, Fintype.sum_prod_type, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [h1 _ _ (Subtype.prop _), Finset.sum_const, Finset.card_univ, Fintype.card_zpowers]

theorem eq_zero_of_gen : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (l : ℕ) [Fact l.Prime] (ρ : Γ →* GL (Fin 2) (Qbar l)) (z : Γ → Fin 2 → Qbar l) (I J : Subgroup Γ) (γ : Γ), IsClosed (I : Set Γ) → J ≤ I → γ ∈ I → (∀ i, Continuous fun s => z s i) → (∀ s ∈ I, ∀ t ∈ I, z (s * t) = z s + (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ z t) → z γ = 0 → (∀ j ∈ J, z j = 0) → I ≤ (Subgroup.zpowers γ ⊔ J).topologicalClosure → ∀ s ∈ I, z s = 0 := by
  intro Γ _ _ _ l _ ρ z I J γ hI hJI hγ hz hc h0 hJ hgen s hs
  have h1 : z 1 = 0 := hJ 1 J.one_mem
  let S : Subgroup Γ :=
    { carrier := {s | s ∈ I ∧ z s = 0}
      one_mem' := ⟨I.one_mem, h1⟩
      mul_mem' := fun {a b} ha hb => ⟨I.mul_mem ha.1 hb.1, by rw [hc a ha.1 b hb.1, ha.2, hb.2]; simp⟩
      inv_mem' := fun {a} ha => ⟨I.inv_mem ha.1, by
        have := hc a⁻¹ (I.inv_mem ha.1) a ha.1
        rw [inv_mul_cancel, h1, ha.2] at this
        simpa using this.symm⟩ }
  have hS : IsClosed (S : Set Γ) := hI.inter (isClosed_eq (continuous_pi hz) continuous_const)
  exact (Subgroup.topologicalClosure_minimal (Subgroup.zpowers γ ⊔ J) (t := S)
    (sup_le (Subgroup.zpowers_le.2 ⟨hγ, h0⟩) fun j hj => ⟨hJI hj, hJ j hj⟩) hS (hgen hs)).2

theorem exists_cob_of_coprime : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (l : ℕ) [Fact l.Prime] (ρ : Γ →* GL (Fin 2) (Qbar l)) (z : Γ → Fin 2 → Qbar l) (J : Subgroup Γ), (∀ U : Subgroup J, U.Normal → IsOpen (U : Set J) → U.index.Coprime l) → (∀ i k, Continuous fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) i k) → (∀ s i k, ‖(ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) i k‖ ≤ 1) → (∀ i, Continuous fun s => z s i) → (∀ s i, ‖z s i‖ ≤ 1) → (∀ s ∈ J, ∀ t ∈ J, z (s * t) = z s + (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ z t) → ∃ v : Fin 2 → Qbar l, (∀ i, ‖v i‖ ≤ 1) ∧ ∀ j ∈ J, z j = (ρ j : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ v - v := by
  intro Γ _ _ _ l _ ρ z J hcop hρc hρ1 hzc hz1 hc
  have h1 : z 1 = 0 := by simpa using hc 1 J.one_mem 1 J.one_mem
  let M : J →* Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) (Qbar l) :=
    { toFun := fun s => Matrix.fromBlocks (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) (Matrix.of fun i _ => z s i) 0 1
      map_one' := by
        rw [← Matrix.fromBlocks_one]
        congr 1
        · simp
        · ext i k; simp [h1]
      map_mul' := fun s t => by
        rw [Matrix.fromBlocks_multiply]
        congr 1
        · simp
        · ext i k
          fin_cases i <;> simp [hc s s.2 t t.2, Matrix.mul_apply, Matrix.mulVec, dotProduct, add_comm]
        · simp
        · simp }
  obtain ⟨N, hn, ho, hN⟩ := exists_open_ker M hcop
    (by
      rintro (i | i) (k | k)
      · exact (hρc i k).comp continuous_subtype_val
      · exact (hzc i).comp continuous_subtype_val
      · exact continuous_const
      · exact continuous_const)
    (by
      rintro s (i | i) (k | k)
      · exact hρ1 s i k
      · exact hz1 s i
      · simp [M]
      · simp [M])
  obtain ⟨v, hv, hv'⟩ := exists_cob_of_index (fun s : J => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l))) (fun s => z s) N
    (hcop N hn ho) (fun s hs => funext fun i => by simpa [M] using congrFun (congrFun (hN s hs) (.inl i)) (.inr ()))
    (fun s => hz1 s) (fun s t => hc s s.2 t t.2)
  exact ⟨v, hv, fun j hj => hv' ⟨j, hj⟩⟩

theorem exists_conj_norm : ∀ (Γ : Type) [Group Γ] (K : Type) [Field K] (X : Type) [Monoid X] (ρ : Γ →* GL (Fin 2) K) (κ : Γ →* X) (Y : Γ → X → Fin 2 → K) (I J : Subgroup Γ) (γ φ : Γ) (N : ℕ) (x : X) (v : Fin 2 → K), ShCoc (fun s => (ρ s : Matrix (Fin 2) (Fin 2) K)) κ Y → (∀ s ∈ I, κ s = 1) → J ≤ I → γ ∈ I → (∀ j ∈ J, φ * j * φ⁻¹ ∈ J) → (∃ j ∈ J, φ * γ * φ⁻¹ = γ ^ N * j) → (∀ j ∈ J, Y j x = (ρ j : Matrix (Fin 2) (Fin 2) K) *ᵥ v - v) → ∃ v' : Fin 2 → K, (∀ j ∈ J, Y j (x * κ φ) = (ρ j : Matrix (Fin 2) (Fin 2) K) *ᵥ v' - v') ∧ Y γ (x * κ φ) - (((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v' - v') = (((ρ φ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ∑ i ∈ Finset.range N, ((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ i) *ᵥ (Y γ x - (((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v - v)) := by
  intro Γ _ K _ X _ ρ κ Y I J γ φ N x v hY hκ hJI hγ hJ ⟨j₁, hj₁, e⟩ hv
  set R : Γ → Matrix (Fin 2) (Fin 2) K := fun s => (ρ s : Matrix (Fin 2) (Fin 2) K) with hR
  have hm : ∀ s t w, R (s * t) *ᵥ w = R s *ᵥ (R t *ᵥ w) := fun s t w => by
    simp only [hR, map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hp : ∀ n, R (γ ^ n) = R γ ^ n := fun n => by simp only [hR, map_pow, Units.val_pow_eq_pow_val]
  have h1 : ∀ w, R 1 *ᵥ w = w := fun w => by simp [hR]
  let z : Γ → Fin 2 → K := fun t => Y t x - (R t *ᵥ v - v)
  have hz0 : ∀ j ∈ J, z j = 0 := fun j hj => sub_eq_zero.2 (hv j hj)
  have hzc : ∀ s ∈ I, ∀ t, z (s * t) = z s + R s *ᵥ z t := fun s hs t => by
    simp only [z]
    rw [hY s t x, hκ s hs, mul_one, hm, Matrix.mulVec_sub, Matrix.mulVec_sub]; abel
  have hzp : ∀ n, z (γ ^ n) = (∑ i ∈ Finset.range n, R γ ^ i) *ᵥ z γ := fun n => by
    induction n with
    | zero => simpa using hz0 1 J.one_mem
    | succ n ih => rw [pow_succ, hzc _ (I.pow_mem hγ n), ih, hp, Finset.sum_range_succ, Matrix.add_mulVec]
  have key : ∀ s, φ * s * φ⁻¹ ∈ I → Y s (x * κ φ) - (R s *ᵥ (R φ⁻¹ *ᵥ (v + Y φ x)) - R φ⁻¹ *ᵥ (v + Y φ x))
      = R φ⁻¹ *ᵥ z (φ * s * φ⁻¹) := fun s hs => by
    have a1 := hY φ s x
    have a2 := hY (φ * s * φ⁻¹) φ x
    rw [inv_mul_cancel_right, hκ _ hs, mul_one, a1] at a2
    have a3 : Y s (x * κ φ) = R φ⁻¹ *ᵥ (Y (φ * s * φ⁻¹) x + R (φ * s * φ⁻¹) *ᵥ Y φ x - Y φ x) := by
      rw [← a2, add_sub_cancel_left, ← hm, inv_mul_cancel, h1]
    have a4 : ∀ w, R φ⁻¹ *ᵥ (R (φ * s * φ⁻¹) *ᵥ w) = R s *ᵥ (R φ⁻¹ *ᵥ w) := fun w => by
      rw [← hm, ← hm, mul_assoc φ, inv_mul_cancel_left]
    simp only [z, a3, Matrix.mulVec_sub, Matrix.mulVec_add, a4]; abel
  refine ⟨R φ⁻¹ *ᵥ (v + Y φ x), fun j hj => ?_, ?_⟩
  · have := key j (hJI (hJ j hj))
    rw [hz0 _ (hJ j hj), Matrix.mulVec_zero] at this
    exact sub_eq_zero.1 this
  · have := key γ (e ▸ I.mul_mem (I.pow_mem hγ N) (hJI hj₁))
    rw [e, hzc _ (I.pow_mem hγ N), hz0 _ hj₁, Matrix.mulVec_zero, add_zero, hzp] at this
    rw [← Matrix.mulVec_mulVec]
    exact this

theorem frob_mulVec_cob : ∀ (Γ : Type) [Group Γ] (K : Type) [Field K] (ρ : Γ →* GL (Fin 2) K) (J : Subgroup Γ) (γ φ : Γ) (N : ℕ), (∃ j ∈ J, φ * γ * φ⁻¹ = γ ^ N * j) → ∀ u : Fin 2 → K, (∀ j ∈ J, ((ρ j : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ u = u) → (((ρ φ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ∑ i ∈ Finset.range N, ((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ i) *ᵥ (((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ u - u) = ((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ (((ρ φ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ u) - ((ρ φ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ u := by
  intro Γ _ K _ ρ J γ φ N ⟨j, hj, e⟩ u hu
  have e1 : ((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ u - u =
      (((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) - 1) *ᵥ u := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [e1, Matrix.mulVec_mulVec, Matrix.mul_assoc, geom_sum_mul, mul_sub, mul_one, Matrix.sub_mulVec]
  congr 1
  conv_lhs => rw [← hu j hj]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_pow_eq_pow_val, ← map_pow, ← Units.val_mul, ← Units.val_mul,
    ← Units.val_mul, ← map_mul, ← map_mul, ← map_mul, mul_assoc, ← e, mul_assoc, inv_mul_cancel_left]

theorem exists_pow_dvd_orderOf : ∀ (l : ℕ) [Fact l.Prime] (N : ℕ), 2 ≤ N → ∀ (u : ∀ r : ℕ, (ZMod (l ^ r))ˣ), (∀ r, ((u r : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) = (N : ZMod (l ^ r))) → ∀ k : ℕ, ∃ r, l ^ k ∣ orderOf (u r) := by
  intro l hl N hN u hu k
  have hp : l.Prime := hl.out
  by_contra h
  push Not at h
  have hM : 0 < l ^ k * (l - 1) := mul_pos (pow_pos hp.pos k) (Nat.sub_pos_of_lt hp.one_lt)
  set M := l ^ k * (l - 1) with hMd
  set r := N ^ M + 1 with hr
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have h1 : orderOf (u r) ∣ l ^ (r - 1) * (l - 1) := by
    rw [← Nat.totient_prime_pow hp (Nat.succ_pos _), ← ZMod.card_units_eq_totient]
    exact orderOf_dvd_card
  obtain ⟨d₁, d₂, h2, h3, h4⟩ := exists_dvd_and_dvd_of_dvd_mul h1
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 h2
  have h5 : a ≤ k := by
    by_contra h6
    exact h r (h4 ▸ (pow_dvd_pow l (not_le.1 h6).le).mul_right d₂)
  have h6 : u r ^ M = 1 := orderOf_dvd_iff_pow_eq_one.1 (h4 ▸ mul_dvd_mul (pow_dvd_pow l h5) h3)
  have h7 : ((N ^ M : ℕ) : ZMod (l ^ r)) = ((1 : ℕ) : ZMod (l ^ r)) := by
    rw [Nat.cast_pow, ← hu r, ← Units.val_pow_eq_pow_val, h6, Units.val_one, Nat.cast_one]
  have h8 : 1 < N ^ M := Nat.one_lt_pow hM.ne' hN
  have h9 := Nat.le_of_dvd (by omega) ((Nat.modEq_iff_dvd' h8.le).1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 h7).symm)
  have h10 := Nat.lt_pow_self (n := r) hp.one_lt
  omega

theorem norm_mulVec_le {l : ℕ} [Fact l.Prime] {A : Matrix (Fin 2) (Fin 2) (Qbar l)} {v : Fin 2 → Qbar l}
    (hA : ∀ i k, ‖A i k‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) (i : Fin 2) : ‖(A *ᵥ v) i‖ ≤ 1 := by
  show ‖∑ k, A i k * v k‖ ≤ 1
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]; exact mul_le_one₀ (hA i k) (norm_nonneg _) (hv k)

theorem norm_sub_le_one {l : ℕ} [Fact l.Prime] {a b : Qbar l} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))

def cobSp {Γ K : Type} [Group Γ] [Field K] (ρ : Γ → Matrix (Fin 2) (Fin 2) K) (J : Subgroup Γ) (γ : Γ) :
    Submodule K (Fin 2 → K) where
  carrier := {w | ∃ u, (∀ j ∈ J, ρ j *ᵥ u = u) ∧ w = ρ γ *ᵥ u - u}
  zero_mem' := ⟨0, fun j _ => Matrix.mulVec_zero _, by simp⟩
  add_mem' := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
    refine ⟨u + u', fun j hj => by rw [Matrix.mulVec_add, hu j hj, hu' j hj], ?_⟩
    rw [Matrix.mulVec_add]; abel
  smul_mem' := by
    rintro a _ ⟨u, hu, rfl⟩
    refine ⟨a • u, fun j hj => by rw [Matrix.mulVec_smul, hu j hj], ?_⟩
    rw [Matrix.mulVec_smul, smul_sub]

theorem sub_mem_cobSp {Γ K : Type} [Group Γ] [Field K] {ρ : Γ → Matrix (Fin 2) (Fin 2) K} {J : Subgroup Γ} {γ : Γ}
    {v v' : Fin 2 → K} (y : Fin 2 → K) (h : ∀ j ∈ J, ρ j *ᵥ v - v = ρ j *ᵥ v' - v') :
    (y - (ρ γ *ᵥ v - v)) - (y - (ρ γ *ᵥ v' - v')) ∈ cobSp ρ J γ := by
  refine ⟨v' - v, fun j hj => ?_, ?_⟩
  · rw [Matrix.mulVec_sub, eq_add_of_sub_eq (h j hj)]; abel
  · rw [Matrix.mulVec_sub]; abel

end GlobalTheory.KA.UnivNorm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameShapiroSystemLimitUnramifiedAwayFromL
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

noncomputable section

namespace GlobalTheory.KA.TameUnr

open GlobalTheory.KA.UnivNorm

theorem mem_of_fibre_sums {l : ℕ} [Fact l.Prime] {X : ℕ → Type} [∀ r, Group (X r)] [∀ r, Fintype (X r)] (u : ∀ r, X r) (M : ℕ)
    (hu : ∀ k : ℕ, ∃ r, l ^ k ∣ orderOf (u r ^ M)) (Wo : Submodule (Qbar l) (Fin 2 → Qbar l))
    (T : Matrix (Fin 2) (Fin 2) (Qbar l)) (hT : ∀ w ∈ Wo, T *ᵥ w ∈ Wo) (b : Fin 2 → Qbar l)
    (a : ∀ r, X r → Fin 2 → Qbar l) (F : ∀ r, X r → Prop) [∀ r, DecidablePred (F r)]
    (hF : ∀ r z, F r (z * u r ^ M) ↔ F r z) (ha : ∀ r z i, ‖a r z i‖ ≤ 1)
    (hrel : ∀ r z, a r (z * u r) - T *ᵥ a r z ∈ Wo) (hb : ∀ r, b - ∑ z, (if F r z then a r z else 0) ∈ Wo) : b ∈ Wo := by
  classical
  let S : Module.End (Qbar l) ((Fin 2 → Qbar l) ⧸ Wo) := Wo.mapQ Wo (Matrix.toLin' T) fun w hw => hT w hw
  obtain ⟨E, hE, hfix⟩ := exists_pow_fix S
  have h1 : ∀ r n x, Wo.mkQ (a r (x * u r ^ n)) = (S ^ n) (Wo.mkQ (a r x)) := fun r n x => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← mul_assoc, pow_succ', Module.End.mul_apply, ← ih]
      exact (Submodule.Quotient.eq Wo).2 (hrel r _)
  have h2 : ∀ r x, Wo.mkQ (a r (x * u r ^ E)) = Wo.mkQ (a r x) := fun r x => by
    rw [h1]
    refine hfix (orderOf (u r)) (orderOf_pos _) _ ?_
    rw [← h1, pow_orderOf_eq_one, mul_one]
  have h2a : ∀ r m x, Wo.mkQ (a r (x * (u r ^ E) ^ m)) = Wo.mkQ (a r x) := fun r m x => by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ← mul_assoc, h2, ih]
  have h2b : ∀ r m x, F r (x * (u r ^ M) ^ m) ↔ F r x := fun r m x => by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ← mul_assoc, hF, ih]
  set a' : ∀ r, X r → Fin 2 → Qbar l := fun r z => if F r z then a r z else 0 with ha'
  have h2c : ∀ r x, Wo.mkQ (a' r (x * (u r ^ M) ^ E)) = Wo.mkQ (a' r x) := fun r x => by
    simp only [ha', h2b]
    split_ifs
    · rw [← pow_mul, mul_comm M, pow_mul, h2a]
    · rfl
  have ha1 : ∀ r z i, ‖a' r z i‖ ≤ 1 := fun r z i => by
    simp only [ha']
    split_ifs
    · exact ha r z i
    · simp
  have hE0 : 0 < ‖(E : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hE.ne')
  refine (isClosed_submodule Wo).closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (mul_pos hE0 hε) (norm_l_lt_one (l := l))
  obtain ⟨r, hr⟩ := hu k
  let : Fintype (X r ⧸ Subgroup.zpowers ((u r ^ M) ^ E)) := Fintype.ofFinite _
  have h3 := sum_eq_orderOf_smul ((u r ^ M) ^ E) (fun x => Wo.mkQ (a' r x)) (h2c r)
  set o := orderOf ((u r ^ M) ^ E) with ho
  set y := ∑ ω : X r ⧸ Subgroup.zpowers ((u r ^ M) ^ E), a' r ω.out with hy
  have h4 : l ^ k ∣ E * o := hr.trans (orderOf_dvd_of_pow_eq_one (by rw [pow_mul, pow_orderOf_eq_one]))
  have h5 : ‖(o : Qbar l)‖ < ε := by
    obtain ⟨m, hm⟩ := h4
    have : ‖(E : Qbar l)‖ * ‖(o : Qbar l)‖ ≤ ‖(l : Qbar l)‖ ^ k := by
      rw [← norm_mul, ← Nat.cast_mul, hm, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (IsUltrametricDist.norm_natCast_le_one _ m)
    exact lt_of_mul_lt_mul_left (this.trans_lt hk) hE0.le
  refine ⟨b - o • y, ?_, ?_⟩
  · have h3' : Wo.mkQ (∑ x, a' r x) = Wo.mkQ (o • y) := by
      rw [map_nsmul, hy, map_sum, map_sum]
      exact h3
    have := Wo.add_mem (hb r) ((Submodule.Quotient.eq Wo).1 h3')
    rwa [sub_add_sub_cancel] at this
  · rw [dist_eq_norm, sub_sub_cancel, ← Nat.cast_smul_eq_nsmul (Qbar l), norm_smul]
    refine (mul_le_of_le_one_right (norm_nonneg _) ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_)).trans_lt h5
    rw [hy, Finset.sum_apply]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun ω _ => ha1 r _ i

theorem exists_cob_of_limit {l : ℕ} [Fact l.Prime] {ι : Type} (M : ι → Matrix (Fin 2) (Fin 2) (Qbar l))
    (f : ι → Fin 2 → Qbar l) (P : ℕ → Fin 2 → Qbar l)
    (h : ∀ r s i, ‖f s i - (M s *ᵥ P r - P r) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) : ∃ v, ∀ s, f s = M s *ᵥ v - v := by
  let row : ι × Fin 2 → (Fin 2 → Qbar l) × Qbar l := fun p => ((M p.1 - 1) p.2, f p.1 p.2)
  have hlim : ∀ w ∈ Submodule.span (Qbar l) (Set.range row),
      Filter.Tendsto (fun r => w.2 - w.1 ⬝ᵥ P r) Filter.atTop (nhds 0) := fun w hw => by
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨s, i⟩, rfl⟩ := hx
      refine squeeze_zero_norm (a := fun r => ‖((l : ℕ) : Qbar l)‖ ^ r) (fun r => ?_)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) norm_l_lt_one)
      have := h r s i
      rw [norm_pow, ← Matrix.one_mulVec (P r), Matrix.mulVec_mulVec, mul_one, ← Matrix.sub_mulVec] at this
      exact this
    | zero => simp
    | add x y _ _ hx hy =>
      have := hx.add hy
      rw [add_zero] at this
      refine this.congr fun r => ?_
      rw [Prod.fst_add, Prod.snd_add, add_dotProduct]; ring
    | smul a x _ hx =>
      have := hx.const_mul a
      rw [mul_zero] at this
      refine this.congr fun r => ?_
      rw [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, smul_eq_mul, smul_eq_mul]; ring
  have hn : ((0, 1) : (Fin 2 → Qbar l) × Qbar l) ∉ Submodule.span (Qbar l) (Set.range row) := fun hm => by
    simpa using hlim _ hm
  obtain ⟨g, hg, hk⟩ := Submodule.exists_le_ker_of_notMem hn
  refine ⟨fun k => -(g (Pi.single k 1, 0) / g (0, 1)), fun s => funext fun i => ?_⟩
  have h0 : g (row (s, i)) = 0 := hk (Submodule.subset_span ⟨_, rfl⟩)
  have e : row (s, i) = (M s - 1) i 0 • ((Pi.single 0 1, 0) : (Fin 2 → Qbar l) × Qbar l) +
      (M s - 1) i 1 • ((Pi.single 1 1, 0) : (Fin 2 → Qbar l) × Qbar l) + f s i • ((0, 1) : (Fin 2 → Qbar l) × Qbar l) := by
    refine Prod.ext (funext fun k => ?_) (by simp [row])
    fin_cases k <;> simp [row]
  rw [e, map_add (f := _), map_add (f := _), map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at h0
  conv_rhs => rw [← Matrix.one_mulVec (fun k => -(g (Pi.single k 1, 0) / g (0, 1))), Matrix.mulVec_mulVec, mul_one, ← Matrix.sub_mulVec]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  field_simp
  linear_combination h0

theorem sum_ite_fibre {X Y M : Type} [Fintype X] [Fintype Y] [DecidableEq X] [AddCommMonoid M] (π : Y → X) (p : X → Prop)
    [DecidablePred p] (f : Y → M) :
    ∑ x, (if p x then ∑ y ∈ Finset.univ.filter (fun y => π y = x), f y else 0) = ∑ y, if p (π y) then f y else 0 := by
  rw [← Finset.sum_fiberwise Finset.univ π]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_congr rfl fun y hy => (by rw [(Finset.mem_filter.1 hy).2] : (if p (π y) then f y else 0) = if p x then f y else 0)]
  split_ifs <;> simp

def red (l : ℕ) {a b : ℕ} (h : a ≤ b) : (ZMod (l ^ b))ˣ →* (ZMod (l ^ a))ˣ :=
  Units.map (ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ a))).toMonoidHom

theorem red_self (l a : ℕ) (x : (ZMod (l ^ a))ˣ) : red l (le_refl a) x = x := by
  ext; simp [red]

theorem red_red (l : ℕ) {a b d : ℕ} (h : a ≤ b) (h' : b ≤ d) (x : (ZMod (l ^ d))ˣ) :
    red l h (red l h' x) = red l (h.trans h') x :=
  Units.ext (DFunLike.congr_fun (ZMod.castHom_comp (pow_dvd_pow l h) (pow_dvd_pow l h')) (x : ZMod (l ^ d)))

theorem red_cycMod {Ω : Type} [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] {a b : ℕ} (h : a ≤ b) (s : G ℚ Ω) :
    red l h (cycMod ℚ Ω l b s) = cycMod ℚ Ω l a s :=
  Units.ext (DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow a b h) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]))

theorem sum_fibre_level {l : ℕ} [Fact l.Prime] {Γ A M : Type} [Group Γ] [Fintype A] [DecidableEq A] [AddCommMonoid M]
    (Y : ∀ r : ℕ, Γ → A × (ZMod (l ^ r))ˣ → M)
    (h : ∀ r s, Y r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Y (r + 1)) s)
    (r : ℕ) (z₀ : A × (ZMod (l ^ r))ˣ) (j : ℕ) (s : Γ) :
    Y r s z₀ = ∑ z : A × (ZMod (l ^ (r + j)))ˣ, if (z.1, red l (Nat.le_add_right r j) z.2) = z₀ then Y (r + j) s z else 0 := by
  induction j with
  | zero =>
    show _ = ∑ z : A × (ZMod (l ^ r))ˣ, if (z.1, red l (le_refl r) z.2) = z₀ then Y r s z else 0
    simp [red_self]
  | succ j ih =>
    rw [ih, h (r + j) s]
    refine (sum_ite_fibre _ (fun z : A × (ZMod (l ^ (r + j)))ˣ => (z.1, red l (Nat.le_add_right r j) z.2) = z₀) _).trans
      (Finset.sum_congr rfl fun z _ => if_congr ?_ rfl rfl)
    rw [← red_red l (Nat.le_add_right r j) (Nat.le_succ (r + j))]
    rfl

theorem slice_unram : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (n : ℕ)
    (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)))
    (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (q : Pl) (B : ValuationSubring Ω),
  ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → IsPlaceOver B q → (∀ s ∈ Ine (F := ℚ) B, ψ s = 1 ∧ θ s = 1) →
  Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) →
  (∀ r, ShCoc ρ (ψ.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) → (∀ r x i, Continuous fun s => Yw r s x i) →
  (∀ r s x i, Yw r s x i ∈ c.O) → (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) →
  ∀ r z, ∃ v : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, Yw r s z = mat W s *ᵥ v - v := by
  intro l _ Ω _ _ _ W c n θ ρ ψ Yw q B hq hB hI hW hWO hWρ hSh hYc hYO hpush r₀ z₀
  obtain ⟨φ, hφ⟩ := exists_isFrob hB
  obtain ⟨-, hJn, hJcop, -, ⟨γ, hγ⟩, hrel⟩ := GlobalTheory.Published.TameQuotient_holds ℚ Ω l B q hB hq
  obtain ⟨-, hcj, -⟩ := hrel ⟨φ, hφ.1⟩ ⟨γ, Ine_le_Dec B hγ.1⟩ hφ hγ
  have hJI := GlobalTheory.TameQuot.ineKer_le_Ine (F := ℚ) B l
  have hγI := hγ.1
  have hgen := hγ.2
  set J := GlobalTheory.TameQuot.ineKer ℚ B l with hJ
  have hc1 : ∀ j ∈ J, φ * j * φ⁻¹ ∈ J := fun j hj =>
    hJn.conj_mem ⟨j, Ine_le_Dec B (hJI hj)⟩ hj ⟨φ, hφ.1⟩
  have hc2 : ∃ j ∈ J, φ * γ * φ⁻¹ = γ ^ normV q * j :=
    ⟨(γ ^ normV q)⁻¹ * (φ * γ * φ⁻¹), by simpa using hcj, by rw [mul_inv_cancel_left]⟩
  have hκ : ∀ r, ∀ s ∈ Ine (F := ℚ) B, (ψ.prod (cycMod ℚ Ω l r)⁻¹) s = 1 := fun r s hs => by
    rw [MonoidHom.prod_apply, MonoidHom.inv_apply, (hI s hs).1, GlobalTheory.StringRepresentationDecomposition.cycMod_eq_one_of_mem_Ine r hq hB hs, inv_one]
    rfl
  have hu : ∀ r, ((cycMod ℚ Ω l r φ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) = (normV q : ZMod (l ^ r)) := fun r => by
    change PadicInt.toZModPow r ((cycZ ℚ Ω l φ : ℤ_[l]ˣ) : ℤ_[l]) = _
    rw [cycZ_of_isFrob hq hB hφ, map_natCast]
  have hW1 : ∀ s i k, ‖mat W s i k‖ ≤ 1 := fun s i k => norm_le_one_of_mem_coefO c ⟨_, hWO s i k⟩
  have hY1 : ∀ r s x i, ‖Yw r s x i‖ ≤ 1 := fun r s x i => norm_le_one_of_mem_coefO c ⟨_, hYO r s x i⟩
  have hWc : ∀ i k, Continuous fun s => mat W s i k := fun i k =>
    Continuous.matrix_elem (A := fun s => mat W s) (Units.continuous_val.comp hW) i k
  have hWmul : ∀ s t, mat W (s * t) = mat W s * mat W t := fun s t => by
    simp only [mat, map_mul, Units.val_mul]
  have hρ : ∀ s, ρ s = (((θ s)⁻¹ : (Qbar l)ˣ) : Qbar l) • mat W s := fun s => by
    rw [hWρ, smul_smul, Units.inv_mul, one_smul]
  have hmul : ∀ s t, ρ (s * t) = ρ s * ρ t := fun s t => by
    rw [hρ, hρ, hρ, hWmul, map_mul, mul_inv, Units.val_mul, smul_mul_smul_comm]
  have hρI : ∀ s ∈ Ine (F := ℚ) B, ρ s = mat W s := fun s hs => by
    rw [hWρ, (hI s hs).2, Units.val_one, one_smul]
  let R : G ℚ Ω →* GL (Fin 2) (Qbar l) := MonoidHom.toHomUnits
    { toFun := ρ
      map_one' := by rw [hρI 1 (one_mem _)]; simp [mat]
      map_mul' := hmul }
  have hcoc : ∀ r x, ∀ s ∈ Ine (F := ℚ) B, ∀ t, Yw r (s * t) x = Yw r s x + mat W s *ᵥ Yw r t x := fun r x s hs t => by
    rw [hSh r s t x, hκ r s hs, mul_one, hρI s hs]
  choose v hv1 hv' using fun r x => exists_cob_of_coprime (G ℚ Ω) l W (fun s => Yw r s x) J hJcop hWc hW1 (hYc r x)
    (fun s i => hY1 r s x i) (fun s hs t _ => hcoc r x s (hJI hs) t)
  have hv : ∀ r x, ∀ j ∈ J, Yw r j x = ρ j *ᵥ v r x - v r x := fun r x j hj => by
    rw [hρI j (hJI hj)]; exact hv' r x j hj
  set M := orderOf ((ψ.prod (cycMod ℚ Ω l r₀)⁻¹) φ) with hM
  have hM0 : 0 < M := orderOf_pos _
  have hM1 : ψ φ ^ M = 1 ∧ (cycMod ℚ Ω l r₀ φ)⁻¹ ^ M = 1 :=
    Prod.ext_iff.1 (pow_orderOf_eq_one ((ψ.prod (cycMod ℚ Ω l r₀)⁻¹) φ))
  have hb : Yw r₀ γ z₀ - (ρ γ *ᵥ v r₀ z₀ - v r₀ z₀) ∈ cobSp ρ J γ := by
    refine mem_of_fibre_sums (X := fun j => Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ (r₀ + j)))ˣ)
      (fun j => (ψ.prod (cycMod ℚ Ω l (r₀ + j))⁻¹) φ) M (fun k => ?_) _
      (ρ φ⁻¹ * ∑ i ∈ Finset.range (normV q), ρ γ ^ i) ?_ _
      (fun j x => Yw (r₀ + j) γ x - (ρ γ *ᵥ v (r₀ + j) x - v (r₀ + j) x))
      (fun j z => (z.1, red l (Nat.le_add_right r₀ j) z.2) = z₀) ?_ ?_ ?_ ?_
    · obtain ⟨r, hr⟩ := exists_pow_dvd_orderOf l (normV q ^ M)
        (Nat.one_lt_pow hM0.ne' (GlobalTheory.WeilDeligne.one_lt_normV q)) (fun r => cycMod ℚ Ω l r φ ^ M)
        (fun r => by rw [Units.val_pow_eq_pow_val, hu, Nat.cast_pow]) k
      refine ⟨r, hr.trans ?_⟩
      have e : cycMod ℚ Ω l r φ ^ M = ((red l (Nat.le_add_left r r₀)).comp (MonoidHom.snd _ _))
          (((ψ.prod (cycMod ℚ Ω l (r₀ + r))⁻¹) φ ^ M)⁻¹) := by
        rw [map_inv, map_pow, MonoidHom.comp_apply, MonoidHom.prod_apply, MonoidHom.coe_snd, MonoidHom.inv_apply, map_inv,
          red_cycMod, inv_pow, inv_inv]
      rw [e]
      exact (orderOf_map_dvd _ _).trans (orderOf_inv _).dvd
    · rintro _ ⟨u, hu', rfl⟩
      refine ⟨ρ φ⁻¹ *ᵥ u, fun j hj => ?_, frob_mulVec_cob (G ℚ Ω) (Qbar l) R J γ φ _ hc2 u hu'⟩
      have e : j * φ⁻¹ = φ⁻¹ * (φ * j * φ⁻¹) := by group
      rw [Matrix.mulVec_mulVec, ← hmul, e, hmul, ← Matrix.mulVec_mulVec, hu' _ (hc1 j hj)]
    · intro j z
      rw [MonoidHom.prod_apply, MonoidHom.inv_apply, Prod.pow_mk, Prod.fst_mul, Prod.snd_mul, map_mul, map_pow, map_inv,
        red_cycMod, hM1.1, hM1.2, mul_one, mul_one]
    · intro r x i
      rw [hρI γ hγI]
      exact norm_sub_le_one (hY1 _ γ x i) (norm_sub_le_one (norm_mulVec_le (hW1 γ) (hv1 _ x) i) (hv1 _ x i))
    · intro j x
      obtain ⟨v', h1, h2⟩ := exists_conj_norm (G ℚ Ω) (Qbar l) _ R _ (Yw (r₀ + j)) (Ine (F := ℚ) B) J γ φ (normV q) x
        (v _ x) (hSh _) (hκ _) hJI hγI hc1 hc2 (hv _ x)
      have h3 := sub_mem_cobSp (ρ := ρ) (γ := γ) (Yw (r₀ + j) γ (x * (ψ.prod (cycMod ℚ Ω l (r₀ + j))⁻¹) φ))
        (fun j' hj => (hv (r₀ + j) (x * (ψ.prod (cycMod ℚ Ω l (r₀ + j))⁻¹) φ) j' hj).symm.trans (h1 j' hj))
      erw [h2] at h3
      exact h3
    · intro j
      have hs := sum_fibre_level Yw hpush r₀ z₀ j
      set V := ∑ z : Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ (r₀ + j)))ˣ,
        if (z.1, red l (Nat.le_add_right r₀ j) z.2) = z₀ then v (r₀ + j) z else 0 with hV
      have e : ∀ s, Yw r₀ s z₀ - (ρ s *ᵥ V - V) = ∑ z : Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ (r₀ + j)))ˣ,
          if (z.1, red l (Nat.le_add_right r₀ j) z.2) = z₀ then
            Yw (r₀ + j) s z - (ρ s *ᵥ v (r₀ + j) z - v (r₀ + j) z) else 0 := fun s => by
        rw [hs s, hV, Matrix.mulVec_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun z _ => ?_
        split_ifs <;> simp
      rw [← e]
      refine sub_mem_cobSp _ fun j' hj => ?_
      rw [← hv r₀ z₀ j' hj, ← sub_eq_zero, e]
      refine Finset.sum_eq_zero fun z _ => ?_
      rw [← hv _ z j' hj, sub_self, ite_self]
  obtain ⟨w, hw, hb⟩ := hb
  rw [hρI γ hγI] at hb
  refine ⟨v r₀ z₀ + w, fun s hs => sub_eq_zero.1 ?_⟩
  refine eq_zero_of_gen (G ℚ Ω) l W (fun s => Yw r₀ s z₀ - (mat W s *ᵥ (v r₀ z₀ + w) - (v r₀ z₀ + w))) (Ine (F := ℚ) B) J γ
    (isClosed_Ine B) hJI hγI (fun i => ?_) (fun s hs t _ => ?_) ?_ (fun j hj => ?_) hgen s hs
  · show Continuous fun s => Yw r₀ s z₀ i - (∑ k, mat W s i k * (v r₀ z₀ + w) k - (v r₀ z₀ + w) i)
    exact (hYc r₀ z₀ i).sub ((continuous_finsetSum _ fun k _ => (hWc i k).mul continuous_const).sub continuous_const)
  · show _ = _ + mat W s *ᵥ _
    rw [hcoc r₀ z₀ s hs t, hWmul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_sub]; abel
  · show Yw r₀ γ z₀ - _ = 0
    rw [eq_add_of_sub_eq hb, Matrix.mulVec_add]; abel
  · show Yw r₀ j z₀ - _ = 0
    rw [hv r₀ z₀ j hj, ← hρI j (hJI hj), Matrix.mulVec_add, hw j hj]; abel

theorem tame_limit_unram : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (n e : ℕ)
    (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l))
    (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)))
    (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (Yt : G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l) (q : Pl) (B : ValuationSubring Ω),
  ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → IsPlaceOver B q → (∀ s ∈ Ine (F := ℚ) B, ψ s = 1 ∧ θ s = 1) →
  Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) → (∀ s i j, ρ s i j ∈ c.O) →
  (∀ r x, χ r x ∈ c.O) →
  (∀ r, ShCoc ρ (ψ.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) → (∀ r x i, Continuous fun s => Yw r s x i) →
  (∀ r s x i, Yw r s x i ∈ c.O) → (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) →
  (∀ r s a i, ‖Yt s a i - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Yw r s (a, x)) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) →
  ∃ v : Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, ∀ a, Yt s a = mat W s *ᵥ v a - v a := by
  intro l _ Ω _ _ _ W c n e χ θ ρ ψ Yw Yt q B hq hB hI hW hWO hWρ _ _ hSh hYc hYO hpush hspec
  choose V hV using slice_unram l Ω W c n θ ρ ψ Yw q B hq hB hI hW hWO hWρ hSh hYc hYO hpush
  have key : ∀ a, ∃ v : Fin 2 → Qbar l, ∀ s : Ine (F := ℚ) B, Yt s a = mat W s *ᵥ v - v := fun a => by
    refine exists_cob_of_limit (fun s : Ine (F := ℚ) B => mat W s) (fun s => Yt s a)
      (fun r => ∑ x : (ZMod (l ^ r))ˣ, (((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) • V r (a, x)) fun r s i => ?_
    refine le_of_eq_of_le ?_ (hspec r s a i)
    refine congrArg (fun w : Fin 2 → Qbar l => ‖Yt s a i - w i‖) ?_
    rw [Matrix.mulVec_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.mulVec_smul, ← smul_sub, ← hV r (a, x) s s.2]
  choose v hv using key
  exact ⟨v, fun s hs a => hv a ⟨s, hs⟩⟩

end GlobalTheory.KA.TameUnr

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameShapiroSystemLimitUnramifiedAwayFromLStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameShapiroSystem_limit_unramified_away_from_l : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (n e : ℕ)
    (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l))
    (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)))
    (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (Yt : G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l) (q : Pl) (B : ValuationSubring Ω),
  ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → IsPlaceOver B q → (∀ s ∈ Ine (F := ℚ) B, ψ s = 1 ∧ θ s = 1) →
  Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) → (∀ s i j, ρ s i j ∈ c.O) →
  (∀ r x, χ r x ∈ c.O) →
  (∀ r, ShCoc ρ (ψ.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) → (∀ r x i, Continuous fun s => Yw r s x i) →
  (∀ r s x i, Yw r s x i ∈ c.O) → (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) →
  (∀ r s a i, ‖Yt s a i - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Yw r s (a, x)) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) →
  ∃ v : Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, ∀ a, Yt s a = mat W s *ᵥ v a - v a := by
  first | exact @GlobalTheory.KA.TameUnr.tame_limit_unram | exact GlobalTheory.KA.TameUnr.tame_limit_unram | (intros; apply GlobalTheory.KA.TameUnr.tame_limit_unram <;> assumption)
end

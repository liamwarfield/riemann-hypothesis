module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.EvalSmulCong
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.SlFixPoly
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.ProdEqNorm

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.NegOneNot
section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.CauchyFar
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

namespace UpperTheory.Kd.K4

section Adic

variable {R : Type*} [CommRing R] {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]

private lemma ev_le {x : AdicCompletion I M} {s m : ℕ} (h : s ≤ m)
    (e : AdicCompletion.eval I M m x = 0) : AdicCompletion.eval I M s x = 0 := by
  have hx := x.2 h
  rw [AdicCompletion.eval_apply] at e ⊢
  rw [← hx, e, map_zero]

private lemma cauchy_far (d : ℕ → AdicCompletion I M) (n : ℕ)
    (hd : ∀ k, AdicCompletion.eval I M (n + k) (d (k + 1) - d k) = 0) (k j : ℕ) :
    AdicCompletion.eval I M (n + k) (d (k + j) - d k) = 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := ev_le (show n + k ≤ n + (k + j) by omega) (hd (k + j))
    have e : d (k + (j + 1)) - d k = (d (k + j + 1) - d (k + j)) + (d (k + j) - d k) := by
      rw [← add_assoc]; abel
    rw [e, map_add (f := _), h1, ih, add_zero]

private lemma lim_exists (d : ℕ → AdicCompletion I M) (n : ℕ)
    (hd : ∀ k, AdicCompletion.eval I M (n + k) (d (k + 1) - d k) = 0) :
    ∃ L : AdicCompletion I M, ∀ k, AdicCompletion.eval I M (n + k) (L - d k) = 0 := by
  have hc : ∀ s j, AdicCompletion.eval I M s (d (s + j)) = AdicCompletion.eval I M s (d s) :=
    fun s j => sub_eq_zero.1 (by
      rw [← map_sub]; exact ev_le (by omega) (cauchy_far d n hd s j))
  obtain ⟨L, hLe⟩ : ∃ L : AdicCompletion I M, ∀ s, AdicCompletion.eval I M s L =
      AdicCompletion.eval I M s (d s) := by
    refine ⟨⟨fun s => AdicCompletion.eval I M s (d s), ?_⟩, fun _ => rfl⟩
    intro m p hmp
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmp
    have hx := (d (m + j)).2 hmp
    have hy := hc m j
    simp only [AdicCompletion.eval_apply] at hy ⊢
    rw [hx, hy]
  refine ⟨L, fun k => ?_⟩
  have h := cauchy_far d n hd k n
  rw [map_sub, sub_eq_zero, add_comm k n] at h
  rw [map_sub, sub_eq_zero, hLe, h]

end Adic

private lemma vand (l : ℕ) [Fact l.Prime] (w : ℕ) : ∃ (c : ℕ) (E : Fin (w + 1) → Fin (w + 1) → ℤ_[l]),
    ∀ i i' : Fin (w + 1), ∑ j : Fin (w + 1), E i j * (((j : ℕ) : ℤ_[l]) ^ (i' : ℕ)) =
      if i = i' then (l : ℤ_[l]) ^ c else 0 := by
  set V : Matrix (Fin (w + 1)) (Fin (w + 1)) ℤ_[l] :=
    Matrix.vandermonde (fun j : Fin (w + 1) => ((j : ℕ) : ℤ_[l])) with hV
  have hdet : V.det ≠ 0 := by
    rw [hV, Matrix.det_vandermonde_ne_zero_iff]
    intro a b h
    exact Fin.ext (Nat.cast_injective h)
  refine ⟨V.det.valuation, fun i j => ((PadicInt.unitCoeff hdet)⁻¹ : (ℤ_[l])ˣ) * V.adjugate i j, ?_⟩
  intro i i'
  have h1 : (V.adjugate * V) i i' = ∑ j, V.adjugate i j * V j i' := Matrix.mul_apply
  rw [Matrix.adjugate_mul] at h1
  have h2 := PadicInt.unitCoeff_spec hdet
  have h3 : ∑ j : Fin (w + 1), ((PadicInt.unitCoeff hdet)⁻¹ : (ℤ_[l])ˣ) * V.adjugate i j * (((j : ℕ) : ℤ_[l]) ^ (i' : ℕ))
      = ((PadicInt.unitCoeff hdet)⁻¹ : (ℤ_[l])ˣ) * ∑ j, V.adjugate i j * V j i' := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hV, Matrix.vandermonde_apply, mul_assoc]
  rw [h3, ← h1]
  by_cases hii : i = i'
  · subst hii
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, if_true]
    exact (Units.inv_mul_eq_iff_eq_mul _).2 h2
  · simp [Matrix.smul_apply, Matrix.one_apply_ne hii, hii]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private lemma un_pow (X : Tower Ω ε) {l a b P : ℕ} {f : X.Kˣ} (hf : f ∈ X.Un (l ^ (a + b))) :
    f ^ P ∈ X.Un (l ^ b) := by
  intro W hW
  obtain ⟨g, hg⟩ := hf W hW
  refine ⟨(g ^ (l ^ a)) ^ P, ?_⟩
  have e : (((f ^ P : X.Kˣ) : X.K) / (((g ^ (l ^ a)) ^ P : X.Kˣ) : X.K) ^ (l ^ b)) =
      ((f : X.K) / (g : X.K) ^ (l ^ (a + b))) ^ P := by
    push_cast
    rw [div_pow, pow_add]
    congr 1
    ring
  rw [e, map_pow, hg, one_pow]

private lemma cls_pow (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s P : ℕ) (f : X.Kˣ) :
    X.cls l s (f ^ P) = (P : ℤ_[l]) • X.cls l s f := by
  unfold Tower.cls
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  rw [ofMul_pow, Nat.cast_smul_eq_nsmul ℤ_[l]]
  exact map_nsmul (TensorProduct.mk ℤ ℤ_[l] (Additive X.Kˣ) 1) P (Additive.ofMul f)

private lemma cls_le (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {s m : ℕ} (h : s ≤ m) (f : X.Kˣ) {x : X.Khat l}
    (e : AdicCompletion.eval (idl l) (X.Kl l) m x = X.cls l m f) :
    AdicCompletion.eval (idl l) (X.Kl l) s x = X.cls l s f := by
  have hx := x.2 h
  rw [AdicCompletion.eval_apply] at e ⊢
  rw [← hx, e]
  rfl

private lemma kmap_cong (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) {s : ℕ} {x : X.Khat l}
    (e : AdicCompletion.eval (idl l) (X.Kl l) s x = 0) :
    AdicCompletion.eval (idl l) (X.Kl l) s (X.kmap l φ x) = 0 := by
  rw [AdicCompletion.eval_apply] at e ⊢
  unfold Tower.kmap
  simp only [LinearMap.restrictScalars_apply]
  rw [AdicCompletion.map_val_apply, e, map_zero]

end UpperTheory.Kd.K4

theorem UpperTheory.Kd.K4.lim :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l : ℕ) [Fact l.Prime] (N w : ℕ), ∃ c : ℕ, ∀ (n : ℕ) (t : ℕ → X.Fn l), (∀ k, PolMod X l w (n + k) (t k)) →
      (∀ k, CgF X l (n + k) (t (k + 1)) (t k)) → (∀ k, ∀ γ ∈ Gam N l, CgF X l (n + k) (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (t k)) (t k)) →
      ∃ b, LiftB X l N w n c (t 0) b := by
  intro Ω _ _ _ ε X l _ N w
  obtain ⟨c, E, hE⟩ := vand l w
  refine ⟨c, fun n t hP hC hI => ?_⟩
  choose a hp using hP
  have ht := fun k => (hp k).2
  have hrec : ∀ k i, ((l : ℤ_[l]) ^ c) • a k i =
      ∑ j : Fin (w + 1), E i j • t k ![((j : ℕ) : ℤ_[l]), 1] := by
    intro k i
    have e : ∀ j : Fin (w + 1), E i j • t k ![((j : ℕ) : ℤ_[l]), 1] =
        ∑ i' : Fin (w + 1), (E i j * (((j : ℕ) : ℤ_[l]) ^ (i' : ℕ))) • a k i' := by
      intro j
      rw [ht k, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i' _ => ?_
      simp [smul_smul]
    simp_rw [e]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hE]
    simp
  have hd : ∀ i k, AdicCompletion.eval (idl l) (X.Kl l) (n + k)
      (((l : ℤ_[l]) ^ c) • a (k + 1) i - ((l : ℤ_[l]) ^ c) • a k i) = 0 := by
    intro i k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hrec, hrec, ← Finset.sum_sub_distrib, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← smul_sub, map_smul, hC k _, smul_zero]
  choose L hL using fun i => lim_exists (fun k => ((l : ℤ_[l]) ^ c) • a k i) n (hd i)
  let b : X.Fn l := fun u => ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • L i
  have hb : ∀ k u, AdicCompletion.eval (idl l) (X.Kl l) (n + k) (b u - ((l : ℤ_[l]) ^ c) • t k u) = 0 := by
    intro k u
    show AdicCompletion.eval (idl l) (X.Kl l) (n + k)
      ((∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • L i) - ((l : ℤ_[l]) ^ c) • t k u) = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ht k u, Finset.smul_sum, ← Finset.sum_sub_distrib, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [smul_comm ((l : ℤ_[l]) ^ c), ← smul_sub, map_smul, hL i k, smul_zero]
  have hA : ∀ i, L i ∈ X.ASet l := by
    intro i s
    obtain ⟨f, hf, hr⟩ := (hp s).1 i
    refine ⟨f ^ (l ^ c), un_pow X hf, ?_⟩
    have h1 := ev_le (show s ≤ n + s by omega) (hL i s)
    rw [map_sub, sub_eq_zero, map_smul] at h1
    rw [h1, cls_le X l (show s ≤ n + s by omega) f hr, cls_pow]
    push_cast
    rfl
  have hpol : b ∈ X.Pol l w :=
    ⟨L, fun i => Submodule.subset_span (hA i), fun u => rfl⟩
  have hinv : ∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
    intro γ hγ
    funext u
    apply AdicCompletion.ext
    intro s
    have h1 := ev_le (show s ≤ n + s by omega) (hb s u)
    have h2 := ev_le (show s ≤ n + s by omega) (hb s (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u))
    have h3 := kmap_cong X l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv h2
    have h4 := ev_le (show s ≤ n + s by omega) (hI s γ hγ u)
    have e : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b u - b u =
        (X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
          (b (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) - ((l : ℤ_[l]) ^ c) • t s (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)))
        + ((l : ℤ_[l]) ^ c) • (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (t s) u - t s u)
        - (b u - ((l : ℤ_[l]) ^ c) • t s u) := by
      show X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (b (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)) - b u = _ + ((l : ℤ_[l]) ^ c) • (X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (t s (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)) - t s u) - _
      rw [map_sub, map_smul, smul_sub]
      abel
    have h5 : AdicCompletion.eval (idl l) (X.Kl l) s (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b u - b u) = 0 := by
      rw [e, map_sub, map_add (f := _), map_smul, h3, h4, h1]
      simp
    rw [map_sub, sub_eq_zero] at h5
    exact h5
  exact ⟨b, Submodule.subset_span ⟨hpol, hinv⟩, fun u => hb 0 u⟩
end

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

private theorem exTr (H G : Subgroup SL(2, ℤ)) [G.FiniteIndex] :
    ∃ (κ : Type) (_ : Fintype κ) (δ : κ → SL(2, ℤ)), IsTr (H ⊓ G) H δ := by
  classical
  refine ⟨H ⧸ G.subgroupOf H, Fintype.ofFinite _, fun q => ((q.out⁻¹ : H) : SL(2, ℤ)), fun q => (q.out⁻¹).2, fun d hd => ?_⟩
  have key : ∀ q : H ⧸ G.subgroupOf H, d * (((q.out⁻¹ : H) : SL(2, ℤ)))⁻¹ ∈ H ⊓ G ↔
      (QuotientGroup.mk (⟨d, hd⟩⁻¹ : H) : H ⧸ G.subgroupOf H) = q := by
    intro q
    conv_rhs => rw [← QuotientGroup.out_eq' q, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.mem_inf, Subgroup.coe_inv, inv_inv, Subgroup.coe_mul]
    exact ⟨fun h => h.2, fun h => ⟨H.mul_mem hd q.out.2, h⟩⟩
  exact ⟨_, (key _).2 rfl, fun q hq => ((key q).1 hq).symm⟩

private theorem gamma_le {M M' : ℕ} (h : M ∣ M') : CongruenceSubgroup.Gamma M' ≤ CongruenceSubgroup.Gamma M := by
  intro g hg
  rw [CongruenceSubgroup.Gamma_mem] at hg ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hg
  have e : ∀ z : ℤ, ((z : ℤ) : ZMod M) = ZMod.castHom h (ZMod M) (z : ZMod M') := fun z => (map_intCast _ z).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e, h1, map_one]
  · rw [e, h2, map_zero]
  · rw [e, h3, map_zero]
  · rw [e, h4, map_one]

private theorem neg_one_not (l n : ℕ) [hl : Fact l.Prime] (h2 : l ≠ 2) (hn : 1 ≤ n) :
    (-1 : SL(2, ℤ)) ∉ CongruenceSubgroup.Gamma (l ^ n) := by
  intro h
  have h' := gamma_le (dvd_pow_self l (by omega : n ≠ 0)) h
  rw [CongruenceSubgroup.Gamma_mem] at h'
  have h1 := h'.1
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply, Matrix.one_apply_eq,
    Int.cast_neg, Int.cast_one] at h1
  have h3 : ((2 : ℕ) : ZMod l) = 0 := by
    push_cast
    linear_combination -h1
  rw [ZMod.natCast_eq_zero_iff] at h3
  exact h2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h3)

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem un_of (X : Tower Ω ε) {H : Subgroup SL(2, ℤ)} {m : ℕ} {a : X.Kˣ} (h : LUnH X H m (a : X.K)) : a ∈ X.Un m := by
  intro W hW
  obtain ⟨c, -, hc, hv⟩ := h.2.2 W hW
  exact ⟨Units.mk0 c hc, hv⟩

private theorem inv_of (X : Tower Ω ε) {H : Subgroup SL(2, ℤ)} {m : ℕ} {a : X.Kˣ} (h : LUnH X H m (a : X.K)) : InvH X H m a := by
  intro g hg
  exact ⟨1, by simpa using (mem_lev_iff X H _).1 h.2.1 g hg⟩

private def St (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ) (lam : Fin 2 → ℤ) (n : ℕ) (t : X.Fn l) : Prop :=
  ∃ (H : Subgroup SL(2, ℤ)) (M : ℕ) (ι : Type) (_ : Fintype ι) (γ : ι → SL(2, ℤ)) (a : X.Kˣ) (x : X.Khat l),
    0 < M ∧ CongruenceSubgroup.Gamma M ≤ H ∧ H ≤ Gam N l ⊓ CongruenceSubgroup.Gamma (l ^ n) ∧ IsTr H (Gam N l) γ ∧
      LUnH X H (l ^ n) (a : X.K) ∧ Rep X l n a x ∧ t = trH X l w γ lam x

private theorem St.next [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l : ℕ) [hl : Fact l.Prime] (N w : ℕ) (lam : Fin 2 → ℤ) (h2 : l ≠ 2)
    (n : ℕ) (hn : 1 ≤ n) (t : X.Fn l) (ht : St X l N w lam n t) : ∃ t', St X l N w lam (n + 1) t' ∧ CgF X l n t' t := by
  obtain ⟨H, M, ι, _, γ, a, x, hM, hMH, hH, hγ, ha, hx, rfl⟩ := ht
  have hl0 : 0 < l := hl.out.pos
  haveI : NeZero (l ^ (n + 1)) := ⟨(pow_pos hl0 _).ne'⟩
  obtain ⟨κ, _, δ, hδ⟩ := exTr H (CongruenceSubgroup.Gamma (l ^ (n + 1)))
  have hM' : CongruenceSubgroup.Gamma (M * l ^ (n + 1)) ≤ H ⊓ CongruenceSubgroup.Gamma (l ^ (n + 1)) :=
    le_inf ((gamma_le (dvd_mul_right _ _)).trans hMH) (gamma_le (dvd_mul_left _ _))
  have hMp : 0 < M * l ^ (n + 1) := Nat.mul_pos hM (pow_pos hl0 _)
  obtain ⟨f', hf', h, hh, hprod⟩ := step ε X H (H ⊓ CongruenceSubgroup.Gamma (l ^ (n + 1))) (M * l ^ (n + 1)) (l ^ n) l hMp
    (pow_pos hl0 _) hl0 hM' inf_le_left (fun h => neg_one_not l n h2 hn (hH h).2)
    (fun g hg d hd => ⟨H.mul_mem (H.mul_mem hg hd.1) (H.inv_mem hg),
      (CongruenceSubgroup.Gamma_normal _).conj_mem d hd.2 g⟩) κ δ hδ a ha
  rw [← pow_succ] at hf'
  let a' : X.Kˣ := Units.mk0 f' hf'.1
  let x' : X.Khat l := AdicCompletion.of (idl l) (X.Kl l) ((1 : ℤ_[l]) ⊗ₜ Additive.ofMul a')
  have hx' : ∀ k, Rep X l k a' x' := fun k => rfl
  obtain ⟨htr, hc⟩ := (trc ε X l N w n H hH ι γ hγ lam a x hx).2.2.2 _ κ δ inf_le_left hδ
  refine ⟨_, ⟨_, M * l ^ (n + 1), κ × ι, inferInstance, _, a', x', hMp, hM', ?_, htr, hf', hx' _, rfl⟩,
    hc a' (Units.mk0 h hh) x' (hx' _) hprod⟩
  exact inf_le_inf_right _ (hH.trans inf_le_left)

end

theorem UpperTheory.Kd.K4.liftL :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l : ℕ) [Fact l.Prime] (N w : ℕ), l ≠ 2 → ∃ c : ℕ, ∀ (n : ℕ) (H : Subgroup SL(2, ℤ)) (M : ℕ), 1 ≤ n → 0 < M → CongruenceSubgroup.Gamma M ≤ H →
      H ≤ Gam N l ⊓ CongruenceSubgroup.Gamma (l ^ n) → ∀ (ι : Type) [Fintype ι] (γ : ι → SL(2, ℤ)), IsTr H (Gam N l) γ →
      ∀ (lam : Fin 2 → ℤ) (a : X.Kˣ) (x : X.Khat l), LUnH X H (l ^ n) (a : X.K) → Rep X l n a x → ∃ b, LiftB X l N w n c (trH X l w γ lam x) b := by
  intro Ω _ _ _ ε X l _ N w h2
  obtain ⟨c, hc⟩ := lim ε X l N w
  refine ⟨c, fun n H M hn hM hMH hH ι _ γ hγ lam a x ha hx => ?_⟩
  have hs : ∀ (k : ℕ) (t : {t // St X l N w lam (n + k) t}), ∃ t' : {t // St X l N w lam (n + (k + 1)) t},
      CgF X l (n + k) t'.1 t.1 := fun k t => by
    obtain ⟨t', h1, h3⟩ := St.next X l N w lam h2 (n + k) (by omega) t.1 t.2
    exact ⟨⟨t', h1⟩, h3⟩
  choose F hF using hs
  let s : ∀ k : ℕ, {t // St X l N w lam (n + k) t} := fun k =>
    Nat.rec (motive := fun k => {t // St X l N w lam (n + k) t})
      ⟨trH X l w γ lam x, H, M, ι, inferInstance, γ, a, x, hM, hMH, hH, hγ, ha, hx, rfl⟩ F k
  refine hc n (fun k => (s k).1) (fun k => ?_) (fun k => hF k (s k)) (fun k => ?_)
  · obtain ⟨H, M, ι, _, γ, a, x, hM, hMH, hH, hγ, ha, hx, e⟩ := (s k).2
    show PolMod X l w (n + k) (s k).1
    rw [e]
    exact (trc ε X l N w (n + k) H hH ι γ hγ lam a x hx).1 (un_of X ha)
  · obtain ⟨H, M, ι, _, γ, a, x, hM, hMH, hH, hγ, ha, hx, e⟩ := (s k).2
    intro g hg
    show CgF X l (n + k) (X.act l _ (s k).1) (s k).1
    rw [e]
    exact (trc ε X l N w (n + k) H hH ι γ hγ lam a x hx).2.1 (inv_of X ha) g hg
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.GamMono
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

private theorem one_eq_zero_of_products_vanish (N : ℕ) (γ : SL(2, ℤ)) :
    γ ∈ CongruenceSubgroup.Gamma N ↔
      ((N : ℤ) ∣ γ 0 0 - 1 ∧ (N : ℤ) ∣ γ 0 1 ∧ (N : ℤ) ∣ γ 1 0 ∧ (N : ℤ) ∣ γ 1 1 - 1) := by
  rw [CongruenceSubgroup.Gamma_mem]
  simp only [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_one, sub_eq_zero]

private theorem mem_gamma_of_dvd_of_mem_gamma {N P : ℕ} (h : N ∣ P) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma P) :
    γ ∈ CongruenceSubgroup.Gamma N := by
  have h' : (N : ℤ) ∣ (P : ℤ) := Int.natCast_dvd_natCast.2 h
  rw [one_eq_zero_of_products_vanish] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  exact ⟨h'.trans h1, h'.trans h2, h'.trans h3, h'.trans h4⟩

private theorem exists_sl2_neg_mem_gamma_commutator_mem_gamma_mul (A R : ℕ) (hAR : Nat.Coprime A R) :
    ∃ z : SL(2, ℤ), -z ∈ CongruenceSubgroup.Gamma A ∧ z ∈ CongruenceSubgroup.Gamma R ∧
      ∀ γ : SL(2, ℤ), γ * z * γ⁻¹ * z⁻¹ ∈ CongruenceSubgroup.Gamma (A * R) := by
  obtain ⟨s, r, hsr⟩ := Nat.isCoprime_iff_coprime.2 hAR
  set P : ℤ := (A : ℤ) * R with hP
  set c : ℤ := s * A - r * R with hcdef
  set j : ℤ := -4 * s * r with hj
  have hc : c ^ 2 = 1 + P * j := by
    rw [hcdef, hP, hj]; linear_combination (s * A + r * R + 1) * hsr
  have hdet : Matrix.det !![c, P; -P * j ^ 2, c * (1 - P * j)] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination (1 - P * j) * hc
  let z : SL(2, ℤ) := ⟨!![c, P; -P * j ^ 2, c * (1 - P * j)], hdet⟩
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [one_eq_zero_of_products_vanish]
    refine ⟨⟨-2 * s, ?_⟩, ⟨-(R : ℤ), ?_⟩, ⟨R * j ^ 2, ?_⟩, ⟨-2 * s + c * R * j, ?_⟩⟩
    · show -c - 1 = (A : ℤ) * (-2 * s)
      linear_combination hsr - hcdef
    · show -P = (A : ℤ) * (-(R : ℤ))
      linear_combination -hP
    · show -(-P * j ^ 2) = (A : ℤ) * (R * j ^ 2)
      linear_combination j ^ 2 * hP
    · show -(c * (1 - P * j)) - 1 = (A : ℤ) * (-2 * s + c * R * j)
      linear_combination hsr - hcdef + c * j * hP
  · rw [one_eq_zero_of_products_vanish]
    refine ⟨⟨-2 * r, ?_⟩, ⟨(A : ℤ), ?_⟩, ⟨-(A : ℤ) * j ^ 2, ?_⟩, ⟨-2 * r - c * A * j, ?_⟩⟩
    · show c - 1 = (R : ℤ) * (-2 * r)
      linear_combination hcdef + hsr
    · show P = (R : ℤ) * A
      linear_combination hP
    · show -P * j ^ 2 = (R : ℤ) * (-(A : ℤ) * j ^ 2)
      linear_combination -j ^ 2 * hP
    · show c * (1 - P * j) - 1 = (R : ℤ) * (-2 * r - c * A * j)
      linear_combination hcdef + hsr - c * j * hP
  · intro γ
    set π : SL(2, ℤ) →* SL(2, ZMod (A * R)) :=
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (A * R))) with hπ
    have hz : ((π z : SL(2, ZMod (A * R))) : Matrix (Fin 2) (Fin 2) (ZMod (A * R))) =
        (c : ZMod (A * R)) • (1 : Matrix (Fin 2) (Fin 2) (ZMod (A * R))) := by
      have hP0 : ((P : ℤ) : ZMod (A * R)) = 0 := by
        rw [hP]; push_cast; exact_mod_cast ZMod.natCast_self (A * R)
      have hentry : ∀ i k, ((π z : SL(2, ZMod (A * R))) : Matrix (Fin 2) (Fin 2) (ZMod (A * R))) i k =
          (((z : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ) : ZMod (A * R)) := fun _ _ => rfl
      ext i k
      rw [hentry]
      fin_cases i <;> fin_cases k <;> simp [z, hP0]
    have hcomm : ∀ g : SL(2, ZMod (A * R)), g * π z = π z * g := by
      intro g
      ext1
      simp only [Matrix.SpecialLinearGroup.coe_mul, hz, Matrix.mul_smul, Matrix.smul_mul, mul_one,
        one_mul]
    show γ * z * γ⁻¹ * z⁻¹ ∈ π.ker
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm, mul_assoc (π z),
      mul_inv_cancel (π γ), mul_one, mul_inv_cancel]

private theorem exists_ne_zero_act_eq_mul_of_cocycle {K : Type} [Field K] {Q : Type} [Group Q] (E : Type) [Monoid E]
    (act : Q → K ≃+* K) (res : Q → (E →* K))
    (hres : ∀ p q x, res (p * q) x = act q (res p x))
    (hfin : (Set.range res).Finite)
    (t : Q → K) (ht0 : ∀ q, t q ≠ 0)
    (hcoc : ∀ p q, t (p * q) = t q * act q (t p))
    (hwd : ∀ p q, res p = res q → t p = t q) :
    ∃ β : K, β ≠ 0 ∧ ∀ q, act q β = t q * β := by
  classical
  set S := hfin.toFinset with hS
  have memS : ∀ s, s ∈ S ↔ ∃ p, res p = s := fun s => by
    rw [hS, Set.Finite.mem_toFinset, Set.mem_range]
  let tt : (E →* K) → K := fun s => if h : ∃ p, res p = s then t h.choose else 0
  have htt : ∀ q, tt (res q) = t q := fun q => by
    have h : ∃ p, res p = res q := ⟨q, rfl⟩
    simp only [tt, dif_pos h]
    exact hwd _ _ h.choose_spec
  obtain ⟨y, hy⟩ : ∃ y : E, ∑ s ∈ S, tt s * s y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hli := linearIndependent_iff'.1 (linearIndependent_monoidHom E K) S (fun s => tt s) (by
      funext y
      simpa [Finset.sum_apply, smul_eq_mul] using hcon y)
    have h1 := hli (res 1) ((memS _).2 ⟨1, rfl⟩)
    rw [htt] at h1
    exact ht0 1 h1
  have hres' : ∀ p q, (act q).toMonoidHom.comp (res p) = res (p * q) := fun p q => by
    ext x; simp [hres]
  have key : ∀ q, act q (∑ s ∈ S, tt s * s y) = (t q)⁻¹ * ∑ s ∈ S, tt s * s y := by
    intro q
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.mul_sum]
    refine Finset.sum_nbij' (fun s => (act q).toMonoidHom.comp s)
      (fun s => (act q⁻¹).toMonoidHom.comp s) ?_ ?_ ?_ ?_ ?_
    · intro s hs
      obtain ⟨p, rfl⟩ := (memS s).1 hs
      exact (memS _).2 ⟨p * q, (hres' p q).symm⟩
    · intro s hs
      obtain ⟨p, rfl⟩ := (memS s).1 hs
      exact (memS _).2 ⟨p * q⁻¹, (hres' p q⁻¹).symm⟩
    · intro s hs
      obtain ⟨p, rfl⟩ := (memS s).1 hs
      rw [hres', hres', mul_inv_cancel_right]
    · intro s hs
      obtain ⟨p, rfl⟩ := (memS s).1 hs
      rw [hres', hres', inv_mul_cancel_right]
    · intro s hs
      obtain ⟨p, rfl⟩ := (memS s).1 hs
      rw [hres', htt, htt, map_mul, hcoc]
      have : ((act q).toMonoidHom.comp (res p)) y = act q (res p y) := rfl
      rw [← hres] at this
      rw [← hres]
      field_simp [ht0 q]
  refine ⟨(∑ s ∈ S, tt s * s y)⁻¹, inv_ne_zero hy, fun q => ?_⟩
  rw [map_inv₀, key, mul_inv, inv_inv]

private theorem sl_apply_eq_of_pow_eq_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}
    (X : Tower Ω ε) (g : GQ) (m : ℕ) (hm : 0 < m) (r : X.K) (hr : r ^ m = 1) :
    X.sl g r = r := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hint : IsIntegral Ω r := IsIntegral.of_pow hm (by rw [hr]; exact isIntegral_one)
  have hdeg : (minpoly Ω r).natDegree = 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some
      (IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hint))
  obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.1 hdeg
  rw [← hc]
  exact (X.sl g).commutes c

theorem UpperTheory.Kd.K4.h90 :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (H : Subgroup SL(2, ℤ)) (M L m : ℕ) (a : X.Kˣ), 0 < M → 0 < m → L.Prime → CongruenceSubgroup.Gamma M ≤ H → -1 ∉ H → InvH X H m a → ∀ v N : ℕ, 0 < N → Nat.Coprime L N →
      ∃ z : SL(2, ℤ), -z ∈ CongruenceSubgroup.Gamma (L ^ v) ∧ z ∈ CongruenceSubgroup.Gamma N ∧ (∀ γ : SL(2, ℤ), γ * z * γ⁻¹ * z⁻¹ ∈ H) ∧
        (∀ γ : SL(2, ℤ), X.sl (ofSL (γ * z)) (a : X.K) = X.sl (ofSL (z * γ)) (a : X.K)) ∧
        ∃ f ∈ lev X H, ∃ h : X.K, h ≠ 0 ∧ (a : X.K) / X.sl (ofSL z) (a : X.K) = f * h ^ m := by
  intro Ω _ _ _ ε X H M L m a hM hm hL hMH _hneg hInv v N hN hLN
  classical
  have hmul : ∀ (γ δ : SL(2, ℤ)) (f : X.K),
      X.sl (ofSL (γ * δ)) f = X.sl (ofSL δ) (X.sl (ofSL γ) f) := by
    intro γ δ f; rw [map_mul]; exact X.sl_mul _ _ f
  have ha0 : (a : X.K) ≠ 0 := a.ne_zero
  obtain ⟨Ma, hMa, hfixa⟩ := X.level (a : X.K)
  set W0 := M * Ma with hW0
  have hW0pos : 0 < W0 := Nat.mul_pos hM hMa
  haveI : NeZero W0 := ⟨hW0pos.ne'⟩
  set π0 : SL(2, ℤ) →* SL(2, ZMod W0) :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod W0)) with hπ0
  have hrep : ∀ w : SL(2, ZMod W0), ∃ g : SL(2, ℤ), (∃ γ ∈ H, π0 γ = w) → (g ∈ H ∧ π0 g = w) := by
    intro w
    by_cases h : ∃ γ ∈ H, π0 γ = w
    · obtain ⟨γ, hγ, hw⟩ := h
      exact ⟨γ, fun _ => ⟨hγ, hw⟩⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose rep hrep using hrep
  have hu : ∀ w : SL(2, ZMod W0), ∃ u : X.K, u ≠ 0 ∧
      (rep w ∈ H → X.sl (ofSL (rep w)) (a : X.K) = (a : X.K) * u ^ m) := by
    intro w
    by_cases h : rep w ∈ H
    · obtain ⟨u, hu⟩ := hInv _ h
      exact ⟨u, u.ne_zero, fun _ => hu⟩
    · exact ⟨1, one_ne_zero, fun h' => absurd h' h⟩
  choose uq huq0 huq using hu
  have hlev : ∀ w : SL(2, ZMod W0), ∃ Lw : ℕ, 0 < Lw ∧
      ∀ γ ∈ CongruenceSubgroup.Gamma Lw, X.sl (ofSL γ) (uq w) = uq w := fun w => X.level (uq w)
  choose Lw hLw0 hLw using hlev
  set W := W0 * ∏ w, Lw w with hWdef
  have hWpos : 0 < W := Nat.mul_pos hW0pos (Finset.prod_pos fun w _ => hLw0 w)
  have hW0W : W0 ∣ W := Dvd.intro _ rfl
  have hLwW : ∀ w, Lw w ∣ W := fun w =>
    (Finset.dvd_prod_of_mem Lw (Finset.mem_univ w)).trans (Dvd.intro_left _ rfl)
  have hfixW : ∀ c ∈ CongruenceSubgroup.Gamma W, X.sl (ofSL c) (a : X.K) = a := fun c hc =>
    hfixa c (mem_gamma_of_dvd_of_mem_gamma ((Dvd.intro_left _ rfl : Ma ∣ W0).trans hW0W) c hc)
  have hWH : ∀ c ∈ CongruenceSubgroup.Gamma W, c ∈ H := fun c hc =>
    hMH (mem_gamma_of_dvd_of_mem_gamma ((Dvd.intro _ rfl : M ∣ W0).trans hW0W) c hc)
  have hUfix : ∀ w, ∀ c ∈ CongruenceSubgroup.Gamma W, X.sl (ofSL c) (uq w) = uq w := fun w c hc =>
    hLw w c (mem_gamma_of_dvd_of_mem_gamma (hLwW w) c hc)
  have hU : ∀ γ ∈ H, X.sl (ofSL γ) (a : X.K) = (a : X.K) * uq (π0 γ) ^ m := by
    intro γ hγ
    obtain ⟨hr1, hr2⟩ := hrep (π0 γ) ⟨γ, hγ, rfl⟩
    have hc : rep (π0 γ) * γ⁻¹ ∈ CongruenceSubgroup.Gamma W0 := by
      show rep (π0 γ) * γ⁻¹ ∈ π0.ker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hr2, mul_inv_cancel]
    rw [← huq _ hr1]
    have : rep (π0 γ) = (rep (π0 γ) * γ⁻¹) * γ := by group
    rw [this, hmul, hfixa _ (mem_gamma_of_dvd_of_mem_gamma (Dvd.intro_left _ rfl) _ hc)]
  set P := W * N * L ^ v with hPdef
  have hP0 : P ≠ 0 := by
    have : 0 < P := Nat.mul_pos (Nat.mul_pos hWpos hN) (pow_pos hL.pos v)
    exact this.ne'
  set A := L ^ P.factorization L with hAdef
  set R := P / A with hRdef
  have hAR : A * R = P := Nat.ordProj_mul_ordCompl_eq_self P L
  have hcop : Nat.Coprime A R := (Nat.coprime_ordCompl hL hP0).pow_left _
  obtain ⟨z, hz1, hz2, hz3⟩ := exists_sl2_neg_mem_gamma_commutator_mem_gamma_mul A R hcop
  have hLvA : L ^ v ∣ A := by
    apply pow_dvd_pow
    exact (hL.pow_dvd_iff_le_factorization hP0).1 (Dvd.intro_left _ rfl)
  have hNR : N ∣ R := by
    have hNA : Nat.Coprime N A := Nat.Coprime.pow_right _ hLN.symm
    have hNP : N ∣ A * R := by rw [hAR, hPdef]; exact ⟨W * L ^ v, by ring⟩
    exact (Nat.Coprime.dvd_mul_left hNA).1 hNP
  have hWP : W ∣ A * R := by rw [hAR, hPdef]; exact ⟨N * L ^ v, by ring⟩
  have hcomm : ∀ γ : SL(2, ℤ), γ * z * γ⁻¹ * z⁻¹ ∈ CongruenceSubgroup.Gamma W := fun γ =>
    mem_gamma_of_dvd_of_mem_gamma hWP _ (hz3 γ)
  have hcz : ∀ (γ : SL(2, ℤ)) (x : X.K), (∀ c ∈ CongruenceSubgroup.Gamma W, X.sl (ofSL c) x = x) →
      X.sl (ofSL z) (X.sl (ofSL γ) x) = X.sl (ofSL γ) (X.sl (ofSL z) x) := by
    intro γ x hx
    rw [← hmul, ← hmul]
    have : γ * z = (γ * z * γ⁻¹ * z⁻¹) * (z * γ) := by group
    rw [this, hmul, hx _ (hcomm γ)]
  haveI : NeZero W := ⟨hWpos.ne'⟩
  set πW : SL(2, ℤ) →* SL(2, ZMod W) :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod W)) with hπW
  let E : Submonoid X.K :=
    { carrier := {x | ∀ c ∈ CongruenceSubgroup.Gamma W, X.sl (ofSL c) x = x}
      mul_mem' := by
        intro x y hx hy c hc
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_mul, hx c hc, hy c hc]
      one_mem' := by
        intro c _
        simp }
  let act : H → X.K ≃+* X.K := fun q => (X.sl (ofSL (q : SL(2, ℤ)))).toRingEquiv
  let res : H → (E →* X.K) := fun q =>
    { toFun := fun x => X.sl (ofSL (q : SL(2, ℤ))) (x : X.K)
      map_one' := by simp
      map_mul' := by intro x y; simp }
  let U : H → X.K := fun q => uq (π0 q)
  let t : H → X.K := fun q => U q / X.sl (ofSL z) (U q)
  have hszne : ∀ x : X.K, x ≠ 0 → X.sl (ofSL z) x ≠ 0 := fun x hx => (_root_.map_ne_zero _).2 hx
  have hres : ∀ p q x, res (p * q) x = act q (res p x) := fun p q x => hmul _ _ _
  have hfin : (Set.range res).Finite := by
    let g : SL(2, ZMod W) → (E →* X.K) := fun w =>
      if h : ∃ q : H, πW q = w then res h.choose else 1
    have hg : ∀ q, res q = g (πW q) := by
      intro q
      have h : ∃ q' : H, πW q' = πW q := ⟨q, rfl⟩
      simp only [g, dif_pos h]
      ext x
      have hc : (h.choose : SL(2, ℤ)) * (q : SL(2, ℤ))⁻¹ ∈ CongruenceSubgroup.Gamma W := by
        show _ ∈ πW.ker
        rw [MonoidHom.mem_ker, map_mul, map_inv, h.choose_spec, mul_inv_cancel]
      show X.sl (ofSL q) x = X.sl (ofSL h.choose) x
      have e : (h.choose : SL(2, ℤ)) = ((h.choose : SL(2, ℤ)) * (q : SL(2, ℤ))⁻¹) * q := by group
      rw [e, hmul, x.2 _ hc]
    refine (Set.finite_range g).subset ?_
    rintro _ ⟨q, rfl⟩
    exact ⟨πW q, (hg q).symm⟩
  have ht0 : ∀ q, t q ≠ 0 := fun q => div_ne_zero (huq0 _) (hszne _ (huq0 _))
  have hcoc : ∀ p q, t (p * q) = t q * act q (t p) := by
    intro p q
    have e1 := hU _ (p * q).2
    have e2 : ((p * q : H) : SL(2, ℤ)) = (p : SL(2, ℤ)) * q := rfl
    rw [e2, hmul, hU _ p.2, map_mul, map_pow, hU _ q.2] at e1
    have hpq : U (p * q) ^ m = (U q * X.sl (ofSL (q : SL(2, ℤ))) (U p)) ^ m := by
      apply mul_left_cancel₀ ha0
      show (a : X.K) * uq (π0 ((p * q : H) : SL(2, ℤ))) ^ m = _
      rw [e2, ← e1]
      ring
    have hden : U q * X.sl (ofSL (q : SL(2, ℤ))) (U p) ≠ 0 :=
      mul_ne_zero (huq0 _) ((_root_.map_ne_zero _).2 (huq0 _))
    set ζ := U (p * q) / (U q * X.sl (ofSL (q : SL(2, ℤ))) (U p)) with hζdef
    have hζm : ζ ^ m = 1 := by rw [hζdef, div_pow, hpq, div_self (pow_ne_zero _ hden)]
    have hζ : X.sl (ofSL z) ζ = ζ := sl_apply_eq_of_pow_eq_one X _ m hm ζ hζm
    have hζ0 : ζ ≠ 0 := div_ne_zero (huq0 _) hden
    have hUpq : U (p * q) = ζ * (U q * X.sl (ofSL (q : SL(2, ℤ))) (U p)) := by
      rw [hζdef, div_mul_cancel₀ _ hden]
    show U (p * q) / X.sl (ofSL z) (U (p * q)) =
      U q / X.sl (ofSL z) (U q) * X.sl (ofSL (q : SL(2, ℤ))) (U p / X.sl (ofSL z) (U p))
    rw [hUpq, map_mul, map_mul, hζ, map_div₀, ← hcz q (U p) (hUfix _)]
    have h3 : X.sl (ofSL z) (X.sl (ofSL (q : SL(2, ℤ))) (U p)) ≠ 0 :=
      hszne _ ((_root_.map_ne_zero _).2 (huq0 _))
    have h4 := hszne _ (huq0 (π0 q))
    field_simp
  have hwd : ∀ p q, res p = res q → t p = t q := by
    intro p q h
    have e : X.sl (ofSL (p : SL(2, ℤ))) (a : X.K) = X.sl (ofSL (q : SL(2, ℤ))) (a : X.K) :=
      DFunLike.congr_fun h ⟨(a : X.K), hfixW⟩
    rw [hU _ p.2, hU _ q.2] at e
    have hpq : U p ^ m = U q ^ m := mul_left_cancel₀ ha0 e
    set ζ := U p / U q with hζdef
    have hζm : ζ ^ m = 1 := by rw [hζdef, div_pow, hpq, div_self (pow_ne_zero _ (huq0 _))]
    have hζ : X.sl (ofSL z) ζ = ζ := sl_apply_eq_of_pow_eq_one X _ m hm ζ hζm
    have hζ0 : ζ ≠ 0 := div_ne_zero (huq0 _) (huq0 _)
    have hUp : U p = ζ * U q := by rw [hζdef, div_mul_cancel₀ _ (huq0 _)]
    show U p / X.sl (ofSL z) (U p) = U q / X.sl (ofSL z) (U q)
    rw [hUp, map_mul, hζ, mul_div_mul_left _ _ hζ0]
  obtain ⟨β, hβ0, hβ⟩ := exists_ne_zero_act_eq_mul_of_cocycle (↥E) act res hres hfin t ht0 hcoc hwd
  have hinv : ∀ γ ∈ H, X.sl (ofSL γ) ((a : X.K) / X.sl (ofSL z) (a : X.K) / β ^ m) =
      (a : X.K) / X.sl (ofSL z) (a : X.K) / β ^ m := by
    intro γ hγ
    have hb : X.sl (ofSL γ) β = t ⟨γ, hγ⟩ * β := hβ ⟨γ, hγ⟩
    rw [map_div₀, map_div₀, map_pow, hb, ← hcz γ _ hfixW, hU γ hγ, map_mul, map_pow]
    have h1 := hszne _ ha0
    have h2 := hszne _ (huq0 (π0 γ))
    have h3 := huq0 (π0 γ)
    show (a : X.K) * uq (π0 γ) ^ m / (X.sl (ofSL z) (a : X.K) * X.sl (ofSL z) (uq (π0 γ)) ^ m) /
        (uq (π0 γ) / X.sl (ofSL z) (uq (π0 γ)) * β) ^ m = _
    rw [mul_pow, div_pow]
    field_simp
  refine ⟨z, mem_gamma_of_dvd_of_mem_gamma hLvA _ hz1, mem_gamma_of_dvd_of_mem_gamma hNR _ hz2, fun γ => hWH _ (hcomm γ), ?_,
    (a : X.K) / X.sl (ofSL z) (a : X.K) / β ^ m, ?_, β, hβ0, ?_⟩
  · intro γ
    rw [hmul, hmul]
    exact hcz γ _ hfixW
  · simp only [GlobalTheory.K4.lev, Subfield.mem_iInf]
    intro γ hγ
    exact hinv γ hγ
  · rw [div_mul_cancel₀ _ (pow_ne_zero _ hβ0)]
end

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

namespace UpperTheory.Kd.K4.LiftH

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem toGQ_sl (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  have h : 0 < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by simp
  unfold toGQ
  rw [dite_eq_left h]
  ext i j
  simp [ofSL]

private theorem ev_smul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (s : ℤ_[l]) (hs : PadicInt.toZModPow n s = 0)
    (y : X.Khat l) : AdicCompletion.eval (idl l) (X.Kl l) n (s • y) = 0 := by
  rw [map_smul]
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n y)
  rw [← hz, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact GlobalTheory.KZ.ClsMod.smul_mem_of_toZModPow hs z

private theorem tr_sub (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w : ℕ) {ι : Type} [Fintype ι] (γ : ι → SL(2, ℤ))
    (lam : Fin 2 → ℤ) (c : ℤ_[l]) (x y : X.Khat l) (u : Fin 2 → ℤ_[l]) :
    trH X l w γ lam (c • (x - y)) u = c • (trH X l w γ lam x u - trH X l w γ lam y u) := by
  have e : sec X l w lam (c • (x - y)) = c • (sec X l w lam x - sec X l w lam y) := by
    funext v
    simp only [sec, Pi.smul_apply, Pi.sub_apply]
    rw [smul_comm, smul_sub]
  have : trH X l w γ lam (c • (x - y)) = c • (trH X l w γ lam x - trH X l w γ lam y) := by
    unfold trH
    rw [e, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_sub]
  rw [this]; rfl

private theorem tr_z_eq_transfer (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (hw : Odd w) {ι : Type} [Fintype ι] (γ : ι → SL(2, ℤ))
    (lam : Fin 2 → ℤ) (x : X.Khat l) (z : SL(2, ℤ)) (hz : -z ∈ CongruenceSubgroup.Gamma (l ^ n)) (u : Fin 2 → ℤ_[l]) :
    AdicCompletion.eval (idl l) (X.Kl l) n (trH X l w (fun i => z * γ i) lam x u +
      trH X l w γ lam (X.kmap l (X.sl (ofSL z)).toRingEquiv x) u) = 0 := by
  unfold trH
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_apply, Finset.sum_apply, ← Finset.sum_add_distrib, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [Tower.act, LinearMap.coe_mk, AddHom.coe_mk, sec, map_smul]
  rw [toGQ_sl, toGQ_sl, map_mul ofSL, Tower.sl_mul_toRingEquiv, ← Tower.kmap_kmap, ← add_smul]
  apply ev_smul
  rw [Matrix.SpecialLinearGroup.coe_mul, mZl_mul, ← Matrix.mulVec_mulVec]
  generalize mZl l (γ i : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u = v
  rw [CongruenceSubgroup.Gamma_mem] at hz
  obtain ⟨h00, h01, h10, h11⟩ := hz
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, neg_eq_zero] at h00 h01 h10 h11
  have g00 := neg_eq_iff_eq_neg.1 h00
  have g11 := neg_eq_iff_eq_neg.1 h11
  have e : PadicInt.toZModPow n ((lam 0 : ℤ_[l]) * (mZl l (z : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) 0 +
      (lam 1 : ℤ_[l]) * (mZl l (z : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) 1) =
      - PadicInt.toZModPow n ((lam 0 : ℤ_[l]) * v 0 + (lam 1 : ℤ_[l]) * v 1) := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mZl, Matrix.map_apply, map_add (f := _), map_mul, map_intCast,
      eq_intCast]
    rw [g00, g11, h01, h10]; ring
  rw [map_add (f := _), map_pow, map_pow, e, hw.neg_pow, neg_add_cancel]

private theorem isTransversal_left_mul (H Γ : Subgroup SL(2, ℤ)) {ι : Type} (γ : ι → SL(2, ℤ)) (h : IsTr H Γ γ) (z : SL(2, ℤ)) (hz : z ∈ Γ)
    (hc : ∀ g : SL(2, ℤ), g * z * g⁻¹ * z⁻¹ ∈ H) : IsTr H Γ fun i => z * γ i := by
  refine ⟨fun i => Γ.mul_mem hz (h.1 i), fun δ hδ => ?_⟩
  have key : ∀ i, δ * (z * γ i)⁻¹ ∈ H ↔ z⁻¹ * δ * (γ i)⁻¹ ∈ H := by
    intro i
    have h1 := hc (z⁻¹ * δ * (γ i)⁻¹)
    have e : z⁻¹ * δ * (γ i)⁻¹ = ((z⁻¹ * δ * (γ i)⁻¹) * z * (z⁻¹ * δ * (γ i)⁻¹)⁻¹ * z⁻¹) * (δ * (z * γ i)⁻¹) := by
      group
    rw [e, H.mul_mem_cancel_left h1]
  simp only [key]
  exact h.2 _ (Γ.mul_mem (Γ.inv_mem hz) hδ)

private theorem overY_comap (X : Tower Ω ε) (z : SL(2, ℤ)) (W : ValuationSubring X.K) (hW : X.OverY W) :
    X.OverY (W.comap (X.sl (ofSL z)).toRingEquiv.toRingHom) := by
  refine ⟨fun c => ValuationSubring.mem_comap.2 ?_, ValuationSubring.mem_comap.2 ?_⟩
  · have : (X.sl (ofSL z)).toRingEquiv.toRingHom (algebraMap Ω X.K c) = algebraMap Ω X.K c := (X.sl (ofSL z)).commutes c
    rw [this]; exact hW.1 c
  · have : (X.sl (ofSL z)).toRingEquiv.toRingHom X.jK = X.jK := X.j_inv z
    rw [this]; exact hW.2

end UpperTheory.Kd.K4.LiftH

open UpperTheory.Kd.K4.LiftH in
theorem UpperTheory.Kd.K4.liftH :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l : ℕ) [Fact l.Prime] (N w : ℕ), l ≠ 2 → 0 < N → Nat.Coprime l N → Odd w → ∃ c : ℕ, ∀ (n : ℕ) (H : Subgroup SL(2, ℤ)) (M : ℕ), 0 < M →
      CongruenceSubgroup.Gamma M ≤ H → H ≤ Gam N l ⊓ CongruenceSubgroup.Gamma (l ^ n) → ∀ (ι : Type) [Fintype ι] (γ : ι → SL(2, ℤ)), IsTr H (Gam N l) γ →
      ∀ (lam : Fin 2 → ℤ) (a : X.Kˣ) (x : X.Khat l), a ∈ X.Un (l ^ n) → InvH X H (l ^ n) a → Rep X l n a x →
        ∃ b, LiftB X l N w n c (trH X l w γ lam x) b := by
  intro Ω _ _ _ ε X l _ N w hl2 hN hlN hw
  have hp : l.Prime := Fact.out
  obtain ⟨c, hc⟩ := liftL ε X l N w hl2
  obtain ⟨E, hE, heb⟩ := eb ε X
  have h2E : ((2 * E : ℕ) : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hu := PadicInt.unitCoeff_spec h2E
  set s := ((2 * E : ℕ) : ℤ_[l]).valuation
  set un := PadicInt.unitCoeff h2E
  refine ⟨c + s, ?_⟩
  intro n H M hM hMH hH ι _ γ hγ lam a x haU hinv hrep
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, Submodule.zero_mem _, fun u => ?_⟩
    rw [← one_smul ℤ_[l] (_ - _)]
    apply ev_smul
    haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  have hm1 : (-1 : SL(2, ℤ)) ∉ H := by
    intro h
    have h1 := (CongruenceSubgroup.Gamma_mem.1 (hH h).2).1
    have h2 : ((2 : ℕ) : ZMod (l ^ n)) = 0 := by
      simp at h1
      push_cast
      linear_combination -h1
    rw [ZMod.natCast_eq_zero_iff] at h2
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ((dvd_pow_self l hn.ne').trans h2))
  obtain ⟨z, hz1, hzN, hzc, -, f, hfH, h, hh, hfe⟩ :=
    h90 ε X H M l (l ^ n) a hM (pow_pos hp.pos n) hp hMH hm1 hinv n N hN hlN
  have hzG : z ∈ Gam N l := by
    refine ⟨?_, ?_⟩
    · have := CongruenceSubgroup.Gamma_mem.1 hzN
      exact (CongruenceSubgroup.Gamma1_mem N z).2 ⟨this.1, this.2.2.2, this.2.2.1⟩
    · have h10 := (CongruenceSubgroup.Gamma_mem.1 hz1).2.2.1
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, neg_eq_zero] at h10
      refine CongruenceSubgroup.Gamma0_mem.2 ?_
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 ⊢
      exact (Int.natCast_dvd_natCast.2 (dvd_pow_self l hn.ne')).trans h10
  set φ := (X.sl (ofSL z)).toRingEquiv with hφ
  set a' : X.Kˣ := Units.map φ.toMonoidHom a with ha'
  have ha'v : (a' : X.K) = X.sl (ofSL z) (a : X.K) := rfl
  have ha'U : a' ∈ X.Un (l ^ n) := GlobalTheory.KZ.KmapA.un_map X φ (overY_comap X z) _ a haU
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [← ha'v, zero_mul] at hfe
    exact div_ne_zero a.ne_zero a'.ne_zero hfe
  set fu : X.Kˣ := Units.mk0 f hf0 with hfu
  have hae : a = (fu * a') * (Units.mk0 h hh) ^ (l ^ n) := by
    apply Units.ext
    rw [← ha'v, div_eq_iff a'.ne_zero] at hfe
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, hfu, Units.val_mk0]
    rw [hfe]; ring
  obtain ⟨-, p2, p3, p4, -, p6, -⟩ := GlobalTheory.KZ.H3.cls_props Ω ε X l n
  have hrf : AdicCompletion.eval (idl l) (X.Kl l) n (x - X.kmap l φ x) = X.cls l n fu := by
    rw [map_sub, p6 φ x a hrep, hrep, (p2 a _).2 ⟨_, hae⟩, p3, add_sub_cancel_right]
  have hpow : ∀ k : ℕ, X.cls l n (fu ^ k) = (k : ℤ_[l]) • X.cls l n fu := by
    intro k
    induction k with
    | zero => simp [p4]
    | succ k ih => rw [pow_succ, p3, ih, Nat.cast_succ, add_smul, one_smul]
  have hrE : Rep X l n (fu ^ E) ((E : ℤ_[l]) • (x - X.kmap l φ x)) := by
    unfold Rep
    rw [map_smul, hrf, hpow]
  have hL : LUnH X H (l ^ n) ((fu ^ E : X.Kˣ) : X.K) := by
    refine ⟨Units.ne_zero _, ?_, fun W hW => ?_⟩
    · rw [Units.val_pow_eq_pow_val]; exact pow_mem hfH E
    · obtain ⟨g, hg⟩ := haU W hW
      obtain ⟨g', hg'⟩ := ha'U W hW
      have hne : (g : X.K) / g' / h ≠ 0 := div_ne_zero (div_ne_zero g.ne_zero g'.ne_zero) hh
      obtain ⟨y, hy, hy0, hyv⟩ := heb W hW _ hne
      refine ⟨y, (mem_lev_iff X H y).2 fun δ _ => (mem_lev_iff X ⊤ y).1 hy δ trivial, hy0, ?_⟩
      have hfe' : f = (a : X.K) / a' / h ^ (l ^ n) := by
        rw [ha'v, hfe, mul_div_assoc, div_self (pow_ne_zero _ hh), mul_one]
      have e : ((fu ^ E : X.Kˣ) : X.K) / y ^ (l ^ n) =
          (((a : X.K) / (g : X.K) ^ (l ^ n)) / ((a' : X.K) / (g' : X.K) ^ (l ^ n))) ^ E *
            (((g : X.K) / g' / h) ^ E / y) ^ (l ^ n) := by
        rw [Units.val_pow_eq_pow_val, hfu, Units.val_mk0, hfe', div_pow (_ ^ E) y, ← pow_mul, mul_comm E, pow_mul,
          ← mul_div_assoc, ← mul_pow]
        congr 2
        have := g.ne_zero
        have := g'.ne_zero
        have := a'.ne_zero
        simp only [div_pow]
        field_simp
      rw [e, map_mul, map_pow, map_pow, map_div₀, hg, hg', hyv]; simp
  obtain ⟨b, hbB, hb⟩ := hc n H M hn hM hMH hH ι γ hγ lam (fu ^ E) _ hL hrE
  refine ⟨((un⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • b, Submodule.smul_mem _ _ hbB, fun u => ?_⟩
  have t1 := ((trc ε X l N w n H hH ι γ hγ lam a x hrep).2.2.1 hinv ι _ (isTransversal_left_mul H _ γ hγ z hzG hzc) x hrep) u
  have t2 := tr_z_eq_transfer X l w n hw γ lam x z hz1 u
  have t3 := hb u
  rw [tr_sub] at t3
  have hv : ((un⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * (2 * (E : ℤ_[l])) = (l : ℤ_[l]) ^ s := by
    have e : (2 * (E : ℤ_[l])) = (un : ℤ_[l]) * (l : ℤ_[l]) ^ s := by
      rw [← hu]; push_cast; ring
    rw [e, ← mul_assoc, Units.inv_mul, one_mul]
  generalize ((un⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = v at hv ⊢
  generalize hA : trH X l w γ lam x u = A at t1 t3 ⊢
  generalize trH X l w (fun i => z * γ i) lam x u = B at t1 t2
  generalize trH X l w γ lam (X.kmap l φ x) u = C at t2 t3
  have key : (v • b) u - ((l : ℤ_[l]) ^ (c + s)) • A =
      v • (b u - ((l : ℤ_[l]) ^ c) • ((E : ℤ_[l]) • (A - C))) -
        (v * (l : ℤ_[l]) ^ c * (E : ℤ_[l])) • (A - B) - (v * (l : ℤ_[l]) ^ c * (E : ℤ_[l])) • (B + C) := by
    rw [pow_add, ← hv, Pi.smul_apply]
    module
  rw [key, map_sub, map_sub, map_smul, map_smul, map_smul, t1, t2, t3]
  simp

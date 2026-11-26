module

public import ReciprocityTheory.DualLattices.EqZeroOfIsoZero
public import ReciprocityTheory.DualLattices.ElementaryDivisorStatement
public import ReciprocityTheory.DualLattices.RankEqRankOfPermAndZero
public import ReciprocityTheory.DualLattices.FrobeniusBlock
public import ReciprocityTheory.DualLattices.SumX
public import ReciprocityTheory.DualLattices.EigPowEqOne

@[expose] public section

section -- merged from ReciprocityTheory.DualLattices.MonomialsSpanOfProdEq
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Basis

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

private lemma col_mem_span {X : Type} [Fintype X] (B' : Matrix X X C) (V : Matrix X X R) (j : X) :
    (fun x => (B' * V.map (algebraMap R C)) x j) ∈
      Submodule.span R (Set.range fun α x => B' x α) := by
  have e : (fun x => (B' * V.map (algebraMap R C)) x j) = ∑ α, V α j • (fun x => B' x α) := by
    ext x
    simp [Matrix.mul_apply, Finset.sum_apply, Algebra.smul_def, mul_comm]
  rw [e]
  exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

private lemma exists_factor {X : Type} [Fintype X] (B B' : Matrix X X C)
    (h : ∀ α, (fun x => B' x α) ∈ Submodule.span R (Set.range fun j x => B x j)) :
    ∃ W : Matrix X X R, B' = B * W.map (algebraMap R C) := by
  choose c hc using fun α => (Submodule.mem_span_range_iff_exists_fun R).1 (h α)
  refine ⟨Matrix.of fun j α => c α j, ?_⟩
  ext x α
  have h1 := congrFun (hc α) x
  simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def] at h1
  rw [Matrix.mul_apply, ← h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm]

private lemma prod_pow_mem {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (A : HopfOrder (C := C) R N) {ι : Type} [Fintype ι] (f : ι → N → C)
    (hf : ∀ j, f j ∈ A.carrier) (n : ι → ℕ) : (fun y => ∏ j, f j y ^ n j) ∈ A.carrier := by
  have hpow : ∀ j k, f j ^ k ∈ A.carrier := by
    intro j k
    induction k with
    | zero => simpa using A.one_mem
    | succ k ih => rw [pow_succ]; exact A.mul_mem _ _ ih (hf j)
  have : (fun y => ∏ j, f j y ^ n j) = ∏ j, f j ^ n j := by
    ext y; simp [Finset.prod_apply]
  rw [this]
  exact Finset.prod_induction _ (· ∈ A.carrier) (fun a b ha hb => A.mul_mem a b ha hb)
    A.one_mem (fun j _ => hpow j (n j))

private lemma hasLen_om {p : ℕ} [Fact p.Prime] {g : ℕ} {v : Valuation C NNReal} [Algebra ℤ_[p] R]
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
    (H : HodgeTateDatum p g v R O σ cp) :
    HasLen v R (OmAA H.AA.carrier) (v (algebraMap R C (p : R)) ^ g) := by
  refine ⟨g, fun _ => (p : R), ⟨?_⟩, by simp⟩
  exact (Submodule.quotEquivOfEq _ _ H.cotangent_ker_eq.symm).trans
    ((LinearMap.quotKerEquivOfSurjective H.φ H.cotangent_surjective).trans (PullbackHopfOrder.qPi p g))

private lemma exp_eq (p g : ℕ) :
    g * (p ^ (g + g - 1) * (p * (p - 1) / 2)) * 2 = (p - 1) * g * p ^ (g + g) := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp
  have h2 : p * (p - 1) / 2 * 2 = p * (p - 1) := Nat.div_mul_cancel (Nat.even_mul_pred_self p).two_dvd
  have h3 : p ^ (g + g - 1) * p = p ^ (g + g) := by
    rw [← pow_succ]
    congr 1
    omega
  calc g * (p ^ (g + g - 1) * (p * (p - 1) / 2)) * 2 = g * p ^ (g + g - 1) * (p * (p - 1) / 2 * 2) := by ring
    _ = g * p ^ (g + g - 1) * (p * (p - 1)) := by rw [h2]
    _ = (p - 1) * g * (p ^ (g + g - 1) * p) := by ring
    _ = (p - 1) * g * p ^ (g + g) := by rw [h3]

end Basis

theorem monomials_span_of_prod_eq : EigenLiftsBasisStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H U X hprod D
  classical
  have hv := hS.integers
  have hp1 : v (p : C) < 1 := by simpa [map_natCast] using hS.p_lt

  let B' : Matrix (Nb p g) (Nb p g) C := Matrix.of fun (x α : Nb p g) =>
    ∏ j, (algebraMap R C (D.ε j) * D.u j x) ^ (α j).val
  have hB'v : v B'.det = ∏ j, v (algebraMap R C (D.ε j)) ^
      (p ^ (Fintype.card (Ix g) - 1) * (p * (p - 1) / 2)) :=
    (u5 p C v R hv hp1 (Ix g) D.Λ D.u D.Λ_det D.u_int D.u_cong).2 fun j => algebraMap R C (D.ε j)
  have hε : ∏ j, v (algebraMap R C (D.ε j)) = v (algebraMap R C cp) ^ g := by
    rw [← Finset.prod_fiberwise Finset.univ D.κ, ← hprod]
    exact Finset.prod_congr rfl fun i _ => D.ε_prod i
  have hcard : Fintype.card (Nb p g) = p ^ (g + g) := by
    simp [ZMod.card, Fintype.card_sum, Fintype.card_fin]
  have hsq : v B'.det ^ 2 = (v (algebraMap R C (p : R)) ^ g) ^ Fintype.card (Nb p g) := by
    rw [hB'v, Finset.prod_pow, hε, ← hS.cp_val, hcard]
    simp only [Fintype.card_sum, Fintype.card_fin, ← pow_mul]
    congr 1
    exact exp_eq p g

  obtain ⟨B, hBu, hAA⟩ := H.AA.lat
  have hcol : HasColen R v H.AA.carrier (v B.det) := ⟨B, hAA, rfl⟩
  have hN : ∀ x : Nb p g, p • x = 0 := by
    intro x; ext i; simp
  have hdeg := u4 p C v R hv hp1 (Nb p g) hN H.AA (v B.det) _ hcol (hasLen_om H)

  have hmem : ∀ α : Nb p g, (fun x => B' x α) ∈ H.AA.carrier := by
    intro α
    exact prod_pow_mem H.AA (fun j y => algebraMap R C (D.ε j) * D.u j y)
      (fun j => (Submodule.mem_inf.1 (D.x_mem j)).1) (fun j => (α j).val)
  obtain ⟨W, hW⟩ := exists_factor B B' (fun α => hAA ▸ hmem α)
  have hdet : v B'.det = v B.det * v (algebraMap R C W.det) := by
    rw [hW, Matrix.det_mul, map_mul, RingHom.map_det]; rfl
  have ha : v B.det ≠ 0 := (Valuation.ne_zero_iff v).2 hBu.ne_zero
  have hw1 : v (algebraMap R C W.det) ≤ 1 := hv.map_le_one W.det
  have hw : v (algebraMap R C W.det) = 1 := by
    by_contra hne
    have hlt : v (algebraMap R C W.det) < 1 := lt_of_le_of_ne hw1 hne
    have hpos : 0 < v B.det ^ 2 := pow_pos (pos_iff_ne_zero.2 ha) 2
    have : v B'.det ^ 2 < v B.det ^ 2 := by
      rw [hdet, mul_pow]
      exact mul_lt_of_lt_one_right hpos (pow_lt_one₀ zero_le hlt two_ne_zero)
    rw [hsq] at this
    exact absurd hdeg (not_le.2 this)
  have hWu : IsUnit W.det :=
    hv.isUnit_of_one (isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hw) hw
  have hBeq : B' * (W⁻¹).map (algebraMap R C) = B := by
    rw [hW, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hWu,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  have hspan : Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val) =
      Submodule.span R (Set.range fun α x => B' x α) := rfl
  rw [hspan]
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rw [hAA]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    have := col_mem_span B' (W⁻¹) j
    rwa [hBeq] at this
  · rintro _ ⟨α, rfl⟩
    exact hmem α

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.EmbeddingSeparatingGroup
section -- merged from ReciprocityTheory.DualLattices.SgAlgebraMap
section -- merged from ReciprocityTheory.DualLattices.IsAdicCompleteOfBasis
noncomputable section

open Polynomial IsLocalRing

namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField

variable {p : ℕ} [hp : Fact p.Prime]

theorem smul_top_self (k : ℕ) :
    ((maximalIdeal ℤ_[p]) ^ k • ⊤ : Submodule ℤ_[p] ℤ_[p]) = (maximalIdeal ℤ_[p]) ^ k := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem mem_pow_smul_top_iff {M : Type} [AddCommGroup M] [Module ℤ_[p] M] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ_[p] M) (k : ℕ) (x : M) :
    x ∈ ((maximalIdeal ℤ_[p]) ^ k • ⊤ : Submodule ℤ_[p] M) ↔
      ∀ i, b.repr x i ∈ (maximalIdeal ℤ_[p]) ^ k := by
  constructor
  · intro hx i
    have hle : ((maximalIdeal ℤ_[p]) ^ k • ⊤ : Submodule ℤ_[p] M) ≤
        Submodule.comap (b.coord i) ((maximalIdeal ℤ_[p]) ^ k) :=
      Submodule.smul_le.2 fun r hr m _ => by
        rw [Submodule.mem_comap, map_smul, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
    exact hle hx
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem isPrecomplete_of_basis {M : Type} [AddCommGroup M] [Module ℤ_[p] M] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ_[p] M) : IsPrecomplete (maximalIdeal ℤ_[p]) M := by
  rw [isPrecomplete_iff]
  intro F hF
  have hP := (inferInstance : IsPrecomplete (maximalIdeal ℤ_[p]) ℤ_[p])
  rw [isPrecomplete_iff] at hP
  have hc : ∀ i, ∃ L : ℤ_[p], ∀ k, b.repr (F k) i ≡ L
      [SMOD ((maximalIdeal ℤ_[p]) ^ k • ⊤ : Submodule ℤ_[p] ℤ_[p])] := by
    intro i
    refine hP (fun k => b.repr (F k) i) fun {m n} hmn => ?_
    have := hF hmn
    rw [SModEq.sub_mem, mem_pow_smul_top_iff b] at this
    rw [SModEq.sub_mem, smul_top_self]
    simpa using this i
  choose L hL using hc
  refine ⟨∑ i, L i • b i, fun k => ?_⟩
  rw [SModEq.sub_mem, mem_pow_smul_top_iff b]
  intro i
  have := hL i k
  rw [SModEq.sub_mem, smul_top_self] at this
  have hr : b.repr (∑ j, L j • b j) i = L i := by
    have h := congrFun (b.equivFun.apply_symm_apply L) i
    rwa [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_apply] at h
  rw [map_sub, Finsupp.sub_apply, hr]
  exact this

theorem span_p_eq (S : Type) [CommRing S] [Algebra ℤ_[p] S] :
    (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S) = Ideal.span {(p : S)} := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]

theorem isAdicComplete_of_basis (S : Type) [CommRing S] [Algebra ℤ_[p] S] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ_[p] S) : IsAdicComplete (Ideal.span {(p : S)}) S := by
  have : Module.Finite ℤ_[p] S := Module.Finite.of_basis b
  have hH : IsHausdorff (maximalIdeal ℤ_[p]) S := inferInstance
  have hP : IsPrecomplete (maximalIdeal ℤ_[p]) S := isPrecomplete_of_basis b
  rw [← span_p_eq S]
  exact { toIsHausdorff := IsHausdorff.map_algebraMap_iff.2 hH
          toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.2 hP }

theorem hensel (f : ℤ_[p][X]) (hf : f.Monic) {m : ℕ} (hm0 : 0 < m) (hmp : ¬ p ∣ m) (Q0 : ℤ_[p][X])
    (h0 : ∃ K : ℤ_[p][X], AdjoinRoot.mk f (Q0 ^ m - 1) = (p : AdjoinRoot f) * AdjoinRoot.mk f K) :
    ∃ Q K : ℤ_[p][X], f ∣ Q ^ m - 1 ∧
      AdjoinRoot.mk f (Q - Q0) = (p : AdjoinRoot f) * AdjoinRoot.mk f K := by
  let S := AdjoinRoot f
  let J : Ideal S := Ideal.span {(p : S)}
  have : IsAdicComplete J S := isAdicComplete_of_basis S (AdjoinRoot.powerBasis' hf).basis
  have hHen : HenselianRing S J := inferInstance
  obtain ⟨K0, hK0⟩ := h0
  set a0 : S := AdjoinRoot.mk f Q0
  have ha0 : a0 ^ m - 1 ∈ J := by
    have : a0 ^ m - 1 = AdjoinRoot.mk f (Q0 ^ m - 1) := by simp [a0]
    rw [this, hK0]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hmon : (X ^ m - C (1 : S)).Monic := monic_X_pow_sub_C _ hm0.ne'
  have hev : (X ^ m - C (1 : S)).eval a0 ∈ J := by simpa using ha0
  have hu0 : IsUnit (Ideal.Quotient.mk J a0) := by
    have h1 : (Ideal.Quotient.mk J a0) ^ m = 1 := by
      rw [← map_pow, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk J), ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.2 ha0
    exact IsUnit.of_pow_eq_one h1 hm0.ne'
  have hum : IsUnit (m : S ⧸ J) := by
    have hcop : Nat.Coprime m p :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hmp)
    have hg := Nat.gcd_eq_gcd_ab m p
    rw [hcop, Nat.cast_one] at hg
    have hp0 : (p : S ⧸ J) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk J)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    refine IsUnit.of_mul_eq_one ((Nat.gcdA m p : ℤ) : S ⧸ J) ?_
    have := congrArg (fun z : ℤ => (z : S ⧸ J)) hg
    simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast, hp0, zero_mul,
      add_zero] at this
    exact this.symm
  have hder : IsUnit (Ideal.Quotient.mk J ((X ^ m - C (1 : S)).derivative.eval a0)) := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_natCast,
      eval_pow, eval_X, map_mul, map_pow, map_natCast]
    exact hum.mul (hu0.pow _)
  obtain ⟨a, ha, haJ⟩ := hHen.is_henselian _ hmon a0 hev hder
  obtain ⟨Q, rfl⟩ := AdjoinRoot.mk_surjective a
  refine ⟨Q, ?_⟩
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 haJ
  obtain ⟨K, rfl⟩ := AdjoinRoot.mk_surjective s
  refine ⟨K, ?_, ?_⟩
  · rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, map_one]
    simpa [IsRoot, sub_eq_zero] using ha
  · rw [map_sub, ← hs, mul_comm]

theorem finite_quot (f : ℤ_[p][X]) (hf : f.Monic) :
    Finite (AdjoinRoot f ⧸ Ideal.span {(p : AdjoinRoot f)}) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  let S := AdjoinRoot f
  let J : Ideal S := Ideal.span {(p : S)}
  let b := (AdjoinRoot.powerBasis' hf).basis
  let Φ : (Fin (AdjoinRoot.powerBasis' hf).dim → ZMod p) → S ⧸ J := fun c =>
    Ideal.Quotient.mk J (∑ i, (((c i).val : ℕ) : ℤ_[p]) • b i)
  refine Finite.of_surjective Φ fun y => ?_
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨fun i => PadicInt.toZMod (b.repr s i), ?_⟩
  simp only [Φ]
  rw [Ideal.Quotient.eq]
  have key : (∑ i, (((PadicInt.toZMod (b.repr s i)).val : ℕ) : ℤ_[p]) • b i) - s =
      ∑ i, ((((PadicInt.toZMod (b.repr s i)).val : ℕ) : ℤ_[p]) - b.repr s i) • b i := by
    simp only [sub_smul, Finset.sum_sub_distrib, b.sum_repr]
  rw [key]
  refine Ideal.sum_mem _ fun i _ => ?_
  have hz := PadicInt.toZMod_spec (b.repr s i)
  rw [ZMod.cast_eq_val, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hz
  obtain ⟨w, hw⟩ := hz
  have : (((PadicInt.toZMod (b.repr s i)).val : ℕ) : ℤ_[p]) - b.repr s i = -(w * p) := by
    rw [hw]; ring
  rw [this, neg_smul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  exact J.neg_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))

theorem exists_pow_idem {S : Type} [Monoid S] [Finite S] (x : S) :
    ∃ M : ℕ, 0 < M ∧ x ^ (2 * M) = x ^ M := by
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => x ^ n)
  wlog h : a < b generalizing a b
  · exact this b a hab.symm he.symm (lt_of_le_of_ne (not_lt.1 h) hab.symm)
  set d := b - a with hd
  have hd0 : 0 < d := by omega
  have hstep : ∀ n, a ≤ n → x ^ (n + d) = x ^ n := by
    intro n hn
    have : n + d = (n - a) + b := by omega
    rw [this, pow_add, ← he, ← pow_add]; congr 1; omega
  have hk : ∀ k n, a ≤ n → x ^ (n + k * d) = x ^ n := by
    intro k
    induction k with
    | zero => intro n _; simp
    | succ k ih =>
      intro n hn
      rw [show n + (k + 1) * d = (n + k * d) + d by ring, hstep _ (by omega), ih n hn]
  refine ⟨d * (a + 1), Nat.mul_pos hd0 (Nat.succ_pos a), ?_⟩
  rw [show 2 * (d * (a + 1)) = d * (a + 1) + (a + 1) * d by ring]
  exact hk _ _ (by nlinarith)

end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
end
end

noncomputable section

open Finset Matrix Polynomial

namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem sg_algebraMap (hv : v.Integers R) {p : ℕ} [Fact p.Prime]
    [Algebra ℤ_[p] R] {n : Type} [Fintype n] [DecidableEq n] {ι : Type}
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] (ρ : O →ₐ[ℤ_[p]] Matrix n n ℤ_[p])
    (εT : ι → Matrix n n R) (sg : ι → O →+* R)
    (heig : ∀ a j, (ρ a).map (algebraMap ℤ_[p] R) * εT j = sg j a • εT j) (j : ι) (hj : εT j ≠ 0)
    (z : ℤ_[p]) : sg j (algebraMap ℤ_[p] O z) = algebraMap ℤ_[p] R z := by
  haveI : IsDomain R := hv.hom_inj.isDomain (algebraMap R C)
  have hm : (ρ (algebraMap ℤ_[p] O z)).map (algebraMap ℤ_[p] R) = algebraMap ℤ_[p] (Matrix n n R) z := by
    ext i k
    rw [AlgHom.commutes, Matrix.map_apply, Matrix.algebraMap_matrix_apply, Matrix.algebraMap_matrix_apply]
    split_ifs <;> simp
  have h := heig (algebraMap ℤ_[p] O z) j
  rw [hm, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← algebraMap_smul R z (εT j)] at h
  have h2 : (algebraMap ℤ_[p] R z - sg j (algebraMap ℤ_[p] O z)) • εT j = 0 := by
    rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact (sub_eq_zero.mp h3).symm
  · exact absurd h3 hj

theorem sg_aeval (hv : v.Integers R) {p : ℕ} [Fact p.Prime]
    [Algebra ℤ_[p] R] {n : Type} [Fintype n] [DecidableEq n] {ι : Type}
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] (ρ : O →ₐ[ℤ_[p]] Matrix n n ℤ_[p])
    (εT : ι → Matrix n n R) (sg : ι → O →+* R)
    (heig : ∀ a j, (ρ a).map (algebraMap ℤ_[p] R) * εT j = sg j a • εT j) (j : ι) (hj : εT j ≠ 0)
    (a : O) (Q : ℤ_[p][X]) : sg j (aeval a Q) = aeval (sg j a) Q := by
  have hc : (sg j).comp (algebraMap ℤ_[p] O) = algebraMap ℤ_[p] R :=
    RingHom.ext fun z => sg_algebraMap hv ρ εT sg heig j hj z
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, hc]

theorem seed (p : ℕ) [Fact p.Prime] (hv : v.Integers R) (hpv : v (algebraMap R C (p : R)) < 1)
    [Algebra ℤ_[p] R] {n : Type} [Fintype n] [DecidableEq n] {ι : Type}
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] (ρ : O →ₐ[ℤ_[p]] Matrix n n ℤ_[p])
    (εT : ι → Matrix n n R) (sg : ι → O →+* R)
    (heig : ∀ a j, (ρ a).map (algebraMap ℤ_[p] R) * εT j = sg j a • εT j) (a : O) (c : ℤ) :
    ∃ (b : O) (m s : ℕ), 0 < m ∧ ¬ p ∣ m ∧ ρ b ^ m = 1 ∧
      ∀ j, εT j ≠ 0 → res hv (sg j a + c) ≠ 0 → res hv (sg j b) = res hv (sg j a + c) ^ p ^ s := by
  classical
  have hpr : p.Prime := Fact.out
  have := isDomain hv
  let _ : Field (R ⧸ mI hv) := instField hv
  have hch : CharP (R ⧸ mI hv) p := charP p hv hpv
  set f : ℤ_[p][X] := (ρ a).charpoly with hfdef
  have hf : f.Monic := Matrix.charpoly_monic _
  have hfa : aeval (ρ a) f = 0 := Matrix.aeval_self_charpoly _
  let S := AdjoinRoot f
  let J : Ideal S := Ideal.span {(p : S)}
  have : Finite (S ⧸ J) := finite_quot f hf
  let r : S := AdjoinRoot.root f + (c : S)
  let xq : S ⧸ J := Ideal.Quotient.mk J r
  obtain ⟨M, hM0, hM⟩ := exists_pow_idem xq
  obtain ⟨N, rfl⟩ : ∃ N, M = N + 1 := ⟨M - 1, by omega⟩
  let uq : S ⧸ J := xq ^ (N + 1 + 1) + 1 - xq ^ (N + 1)
  have huq : IsUnit uq := by
    refine IsUnit.of_mul_eq_one (xq ^ N * xq ^ (N + 1) + 1 - xq ^ (N + 1)) ?_
    have he : xq ^ (N + 1) * xq ^ (N + 1) = xq ^ (N + 1) := by rw [← pow_add, ← hM]; ring_nf
    have hx : xq * xq ^ N = xq ^ (N + 1) := by ring
    simp only [uq]
    linear_combination (xq * xq ^ N - xq - xq ^ N + 2) * he + xq ^ (N + 1) * hx

  have hU : Nat.card (S ⧸ J)ˣ ≠ 0 := Nat.card_pos.ne'
  obtain ⟨s, m0, hm0p, hUeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hU p hpr.one_lt.ne'
  have hm0 : 0 < m0 := Nat.pos_of_ne_zero (by rintro rfl; simp at hUeq; exact hU hUeq)
  have hw : (uq ^ p ^ s) ^ m0 = 1 := by
    have h1 := pow_card_eq_one' (x := huq.unit)
    rw [hUeq, pow_mul] at h1
    have := congrArg (fun u : (S ⧸ J)ˣ => (u : S ⧸ J)) h1
    simpa using this

  let Q0 : ℤ_[p][X] := ((X + (c : ℤ_[p][X])) ^ (N + 1 + 1) + 1 - (X + (c : ℤ_[p][X])) ^ (N + 1)) ^ p ^ s
  have hQ0 : AdjoinRoot.mk f Q0 = (r ^ (N + 1 + 1) + 1 - r ^ (N + 1)) ^ p ^ s := by
    simp [Q0, r]
  have hH0 : ∃ K : ℤ_[p][X], AdjoinRoot.mk f (Q0 ^ m0 - 1) = (p : S) * AdjoinRoot.mk f K := by
    have hmem : AdjoinRoot.mk f (Q0 ^ m0 - 1) ∈ J := by
      have e1 : AdjoinRoot.mk f (Q0 ^ m0 - 1) = ((r ^ (N + 1 + 1) + 1 - r ^ (N + 1)) ^ p ^ s) ^ m0 - 1 := by
        rw [map_sub, map_pow, hQ0, map_one]
      rw [e1, ← Ideal.Quotient.eq_zero_iff_mem]
      simp only [map_pow, map_add (f := _), map_sub, map_one]
      rw [sub_eq_zero]
      exact hw
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hmem
    obtain ⟨K, rfl⟩ := AdjoinRoot.mk_surjective t
    exact ⟨K, by rw [← ht, mul_comm]⟩
  obtain ⟨Q, K, hQdvd, hQK⟩ := hensel f hf hm0 hm0p Q0 hH0
  refine ⟨aeval a Q, m0, s, hm0, hm0p, ?_, ?_⟩
  · obtain ⟨g, hg⟩ := hQdvd
    have := congrArg (aeval (ρ a)) hg
    rw [map_mul, hfa, zero_mul, map_sub, map_pow, map_one, sub_eq_zero] at this
    rw [← aeval_algHom_apply, this]
  · intro j hj hres

    have hfj : f.eval₂ (algebraMap ℤ_[p] R) (sg j a) = 0 := by
      have h1 := heig (aeval a f) j
      rw [← aeval_algHom_apply, hfa, Matrix.map_zero _ (map_zero _), Matrix.zero_mul,
        sg_aeval hv ρ εT sg heig j hj] at h1
      have := smul_cancel hv hj (h1.symm.trans (zero_smul R (εT j)).symm)
      rwa [aeval_def] at this
    let ev : S →+* R := AdjoinRoot.lift (algebraMap ℤ_[p] R) (sg j a) hfj
    have hevJ : ∀ t ∈ J, res hv (ev t) = 0 := by
      intro t ht
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 ht
      rw [map_mul, map_natCast, map_mul, map_natCast]
      have : (p : R ⧸ mI hv) = 0 := by
        rw [← map_natCast (res hv)]; exact (res_eq_zero hv _).2 hpv
      rw [this, mul_zero]
    have hevr : ev r = sg j a + c := by
      show ev (AdjoinRoot.root f + (c : S)) = _
      rw [map_add (f := _), map_intCast]
      simp only [ev]
      rw [AdjoinRoot.lift_root]
    have hb : sg j (aeval a Q) = ev (AdjoinRoot.mk f Q) := by
      rw [sg_aeval hv ρ εT sg heig j hj, AdjoinRoot.lift_mk, aeval_def]
    set x := res hv (sg j a + c) with hxdef
    have hxM : x ^ (N + 1) = 1 := by
      have hmem : r ^ (2 * (N + 1)) - r ^ (N + 1) ∈ J := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_pow, sub_eq_zero]
        exact hM
      have h0 := hevJ _ hmem
      rw [map_sub, map_pow, map_pow, hevr, map_sub, map_pow, map_pow, ← hxdef, sub_eq_zero,
        pow_mul', sq] at h0
      have hx0 : x ^ (N + 1) ≠ 0 := pow_ne_zero _ hres
      exact mul_left_cancel₀ hx0 (h0.trans (mul_one _).symm)
    have hdiff : AdjoinRoot.mk f Q - AdjoinRoot.mk f Q0 ∈ J := by
      rw [← map_sub, hQK]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    have h2 := hevJ _ hdiff
    rw [map_sub, map_sub, sub_eq_zero, hQ0] at h2
    have hT : ∀ {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (z : A),
        φ ((z ^ (N + 1 + 1) + 1 - z ^ (N + 1)) ^ p ^ s) =
          (φ z ^ (N + 1 + 1) + 1 - φ z ^ (N + 1)) ^ p ^ s := by
      intros; simp
    rw [hb, h2, hT, hT, hevr, ← hxdef, pow_succ x (N + 1), hxM, one_mul, add_sub_cancel_right]

theorem pair (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hv : v.Integers R)
    (hpv : v (algebraMap R C (p : R)) < 1)
    [Algebra ℤ_[p] R] {n : Type} [Fintype n] [DecidableEq n] {ι : Type}
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] (ρ : O →ₐ[ℤ_[p]] Matrix n n ℤ_[p])
    (εT : ι → Matrix n n R) (sg : ι → O →+* R)
    (heig : ∀ a j, (ρ a).map (algebraMap ℤ_[p] R) * εT j = sg j a • εT j) (a : O) (t : ℕ)
    (i j : ι) (hi : εT i ≠ 0) (hj : εT j ≠ 0) (h : res hv (sg j a) ≠ res hv (sg i a) ^ p ^ t) :
    ∃ (b : O) (m : ℕ), 0 < m ∧ ¬ p ∣ m ∧ ρ b ^ m = 1 ∧
      res hv (sg j b) ≠ res hv (sg i b) ^ p ^ t := by
  have hpr : p.Prime := Fact.out
  let _ : Field (R ⧸ mI hv) := instField hv
  have hch : CharP (R ⧸ mI hv) p := charP p hv hpv
  set yi := res hv (sg i a)
  set yj := res hv (sg j a)
  have h10 : (1 : R ⧸ mI hv) ≠ 0 := one_ne_zero
  have h20 : (2 : R ⧸ mI hv) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff (R ⧸ mI hv) p 2).1 (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).1 this)
  have hc : ∃ c : ℤ, yi + (c : R ⧸ mI hv) ≠ 0 ∧ yj + (c : R ⧸ mI hv) ≠ 0 := by
    by_contra hno
    push Not at hno
    have h0 := hno 0
    have h1 := hno 1
    have h2 := hno 2
    simp only [Int.cast_zero, Int.cast_one, Int.cast_ofNat, add_zero] at h0 h1 h2
    by_cases a0 : yi = 0
    · have b1 := h1 (by rw [a0, zero_add]; exact h10)
      have b2 := h2 (by rw [a0, zero_add]; exact h20)
      exact h10 (by linear_combination b2 - b1)
    · have b0 := h0 a0
      by_cases a1 : yi + 1 = 0
      · have b2 := h2 (fun e => h10 (by linear_combination e - a1))
        exact h20 (by linear_combination b2 - b0)
      · have b1 := h1 a1
        exact h10 (by linear_combination b1 - b0)
  obtain ⟨c, hci, hcj⟩ := hc
  obtain ⟨b, m, s, hm0, hmp, hbm, hbres⟩ := seed p hv hpv ρ εT sg heig a c
  refine ⟨b, m, hm0, hmp, hbm, fun heq => h ?_⟩
  have hri : res hv (sg i a + c) = yi + c := by rw [map_add (f := _), map_intCast]
  have hrj : res hv (sg j a + c) = yj + c := by rw [map_add (f := _), map_intCast]
  rw [hbres j hj (by rwa [hrj]), hbres i hi (by rwa [hri]), hri, hrj, ← pow_mul, mul_comm,
    pow_mul] at heq
  have hcfix : ∀ k : ℕ, ((c : R ⧸ mI hv)) ^ p ^ k = c := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_mul, ih]
      have := map_intCast (frobenius (R ⧸ mI hv) p) c
      rwa [frobenius_def] at this
  have hrhs : (yi + c) ^ p ^ t = yi ^ p ^ t + c := by rw [add_pow_char_pow, hcfix]
  rw [hrhs] at heq
  have hsub : (yj + c - (yi ^ p ^ t + c)) ^ p ^ s = 0 := by
    rw [sub_pow_char_pow, heq, sub_self]
  have := pow_eq_zero_iff (pow_ne_zero s hpr.ne_zero) |>.1 hsub
  linear_combination this

end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
end
end

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

theorem embeddingSeparatingGroup : EmbeddingSeparatingGroupStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U
  have hv : v.Integers R := hS.integers
  have hpv : v (algebraMap R C (p : R)) < 1 := hS.p_lt
  have hp : p.Prime := Fact.out

  have hvnat : ∀ n : ℕ, ¬ p ∣ n → v (algebraMap R C (n : R)) = 1 := by
    intro n hn
    by_contra hne
    have hlt : v (algebraMap R C (n : R)) < 1 := lt_of_le_of_ne (hv.map_le_one _) hne
    have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).2 hn
    have h1 : ((p : ℤ) * Nat.gcdA p n + (n : ℤ) * Nat.gcdB p n) = 1 := by
      rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hcop, Nat.cast_one]
    have h2 : (p : R) * (Nat.gcdA p n : R) + (n : R) * (Nat.gcdB p n : R) = 1 := by
      have := congrArg (fun z : ℤ => (z : R)) h1
      push_cast at this
      exact this
    have h3 : v (algebraMap R C ((p : R) * (Nat.gcdA p n : R) + (n : R) * (Nat.gcdB p n : R))) < 1 := by
      rw [map_add (f := _)]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [map_mul, Valuation.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le (hv.map_le_one _)) hpv
      · rw [map_mul, Valuation.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le (hv.map_le_one _)) hlt
    rw [h2, map_one, Valuation.map_one] at h3
    exact lt_irrefl _ h3
  have hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : R) := by
    intro n hn
    have hn0 : (n : C) ≠ 0 := by
      have : n ≠ 0 := fun h => hn (h ▸ dvd_zero p)
      exact_mod_cast this
    exact hv.isUnit_of_one (isUnit_iff_ne_zero.2 (by rw [map_natCast]; exact hn0)) (hvnat n hn)
  have hp2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have heig : ∀ a j, (H.ρ a).map (algebraMap ℤ_[p] R) * U.εT j = U.sg j a • U.εT j := U.εT_eig
  have hres1 : FrobeniusGroupField.res hv 1 ≠ 0 := (FrobeniusGroupField.res_ne_zero hv 1).2 (by simp)

  have hex : ∀ t : Option (Fin U.m × Fin U.m × Bool), ∃ (b : O) (m : ℕ), 0 < m ∧ ¬ p ∣ m ∧
      H.ρ b ^ m = 1 ∧
      (match t with
        | none => ∀ j, U.εT j ≠ 0 → v (algebraMap R C (U.sg j b - 1)) = 1
        | some (i, k, e) => U.εT i ≠ 0 → U.εT k ≠ 0 → cond e (k ≠ U.φ i) (i ≠ k) →
            FrobeniusGroupField.res hv (U.sg k b) ≠ FrobeniusGroupField.res hv (U.sg i b) ^ p ^ e.toNat) := by
    intro t
    rcases t with _ | ⟨i, k, e⟩
    · obtain ⟨b, m, s, hm, hmp, hbm, hb⟩ := FrobeniusGroupField.seed p hv hpv H.ρ U.εT U.sg heig 0 2
      refine ⟨b, m, hm, hmp, hbm, ?_⟩
      intro j hj
      have h2 : FrobeniusGroupField.res hv (U.sg j 0 + ((2 : ℤ) : R)) = FrobeniusGroupField.res hv 2 := by simp
      have hr2 : FrobeniusGroupField.res hv 2 ≠ 0 := (FrobeniusGroupField.res_ne_zero hv 2).2 (by simpa using hvnat 2 hp2')
      have hfer : ∀ s : ℕ, FrobeniusGroupField.res hv 2 ^ p ^ s = FrobeniusGroupField.res hv 2 := by
        intro s
        induction s with
        | zero => simp
        | succ s ih =>
          have hf := FrobeniusGroupField.fermat p hv hpv (2 : ℤ_[p])
          rw [map_ofNat] at hf
          rw [pow_succ, pow_mul, ih, hf]
      have hbj := hb j hj (by rw [h2]; exact hr2)
      rw [h2, hfer] at hbj
      apply (FrobeniusGroupField.res_ne_zero hv _).1
      rw [map_sub, hbj, map_one]
      have h21 : FrobeniusGroupField.res hv 2 - 1 = FrobeniusGroupField.res hv 1 := by
        rw [← map_one (FrobeniusGroupField.res hv), ← map_sub]
        norm_num
      rw [h21]
      exact hres1
    · by_cases hall : U.εT i ≠ 0 ∧ U.εT k ≠ 0 ∧ cond e (k ≠ U.φ i) (i ≠ k)
      · obtain ⟨hi, hk, hik⟩ := hall
        have ha : ∃ a, FrobeniusGroupField.res hv (U.sg k a) ≠ FrobeniusGroupField.res hv (U.sg i a) ^ p ^ e.toNat := by
          cases e
          · simp only [cond_false, Bool.toNat_false, pow_zero, pow_one] at hik ⊢
            obtain ⟨a, ha⟩ := U.distinct i k hik
            refine ⟨a, fun heq => ?_⟩
            have h0 : FrobeniusGroupField.res hv (U.sg i a - U.sg k a) = 0 := by rw [map_sub, heq, sub_self]
            exact ((FrobeniusGroupField.res_ne_zero hv _).2 ha) h0
          · simp only [cond_true, Bool.toNat_true, pow_one] at hik ⊢
            obtain ⟨a, ha⟩ := U.distinct k (U.φ i) hik
            refine ⟨a, ?_⟩
            have hfr : FrobeniusGroupField.res hv (U.sg (U.φ i) a) = FrobeniusGroupField.res hv (U.sg i a) ^ p := by
              have h0 := (FrobeniusGroupField.res_eq_zero hv _).2 (U.frob i a)
              rw [map_sub, map_pow, sub_eq_zero] at h0
              exact h0
            rw [← hfr]
            intro heq
            have h0 : FrobeniusGroupField.res hv (U.sg k a - U.sg (U.φ i) a) = 0 := by rw [map_sub, heq, sub_self]
            exact ((FrobeniusGroupField.res_ne_zero hv _).2 ha) h0
        obtain ⟨a, ha⟩ := ha
        obtain ⟨b, m, hm, hmp, hbm, hb⟩ :=
          FrobeniusGroupField.pair p hp2 hv hpv H.ρ U.εT U.sg heig a e.toNat i k hi hk ha
        exact ⟨b, m, hm, hmp, hbm, fun _ _ _ => hb⟩
      · exact ⟨1, 1, one_pos, hp.not_dvd_one, by simp, fun hi hk hik => absurd ⟨hi, hk, hik⟩ hall⟩
  choose b m0 hm0 hmp0 hbm0 hQ using hex

  let m : Option (Fin U.m × Fin U.m × Bool) → ℕ := fun t => 2 * m0 t
  have hm : ∀ t, 0 < m t := fun t => by
    have := hm0 t
    show 0 < 2 * m0 t
    omega
  have hmp : ∀ t, ¬ p ∣ m t := fun t h => ((Nat.Prime.dvd_mul hp).1 h).elim hp2' (hmp0 t)
  have hbm : ∀ t, H.ρ (b t) ^ m t = 1 := fun t => by
    show H.ρ (b t) ^ (2 * m0 t) = 1
    rw [mul_comm, pow_mul, hbm0 t, one_pow]
  haveI : ∀ t, NeZero (m t) := fun t => ⟨(hm t).ne'⟩
  have hone : ∀ t, (1 : ZMod (m t)).val = 1 := fun t => by
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_eq_of_lt (by have := hm0 t; show 1 < 2 * m0 t; omega)
  let G := ∀ t : Option (Fin U.m × Fin U.m × Bool), Multiplicative (ZMod (m t))
  let β : G → O := fun γ => ∏ t, b t ^ (Multiplicative.toAdd (γ t)).val
  have key : ∀ (s : Finset (Option (Fin U.m × Fin U.m × Bool)))
      (n : Option (Fin U.m × Fin U.m × Bool) → ℕ),
      H.ρ (∏ t ∈ s, b t ^ n t) = H.ρ (∏ t ∈ s, b t ^ (n t % m t)) := by
    intro s n
    refine Finset.induction_on s (by simp) ?_
    intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, map_mul, map_mul, ih, map_pow, map_pow,
      ← pow_eq_pow_mod _ (hbm a)]
  have hmul : ∀ γ γ' : G, H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ') := by
    intro γ γ'
    have e1 : β (γ * γ') = ∏ t, b t ^ (((Multiplicative.toAdd (γ t)).val +
        (Multiplicative.toAdd (γ' t)).val) % m t) := by
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [Pi.mul_apply, toAdd_mul, ZMod.val_add]
    have k2 := key Finset.univ
      (fun t => (Multiplicative.toAdd (γ t)).val + (Multiplicative.toAdd (γ' t)).val)
    beta_reduce at k2
    rw [e1, ← k2, ← map_mul]
    congr 1
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun t _ => pow_add _ _ _
  have h1 : H.ρ (β 1) = 1 := by
    have hb1 : β 1 = 1 := by
      refine (Finset.prod_congr rfl fun t _ => ?_).trans Finset.prod_const_one
      show b t ^ (Multiplicative.toAdd ((1 : G) t)).val = 1
      rw [Pi.one_apply, toAdd_one, ZMod.val_zero, pow_zero]
    rw [hb1, map_one]
  have hcard : IsUnit (Fintype.card G : R) := by
    rw [Fintype.card_pi, Nat.cast_prod]
    refine Finset.prod_induction _ IsUnit (fun x y hx hy => hx.mul hy) isUnit_one fun t _ => ?_
    have hc : Fintype.card (Multiplicative (ZMod (m t))) = m t := by simp
    rw [hc]
    exact hunit _ (hmp t)
  let gen : Option (Fin U.m × Fin U.m × Bool) → G := fun t =>
    Pi.mulSingle (M := fun t => Multiplicative (ZMod (m t))) t (Multiplicative.ofAdd (1 : ZMod (m t)))
  have hgen : ∀ t, β (gen t) = b t := by
    intro t
    show ∏ u, b u ^ (Multiplicative.toAdd
      (Pi.mulSingle (M := fun t => Multiplicative (ZMod (m t))) t (Multiplicative.ofAdd (1 : ZMod (m t))) u)).val
      = b t
    rw [Finset.prod_eq_single t]
    · rw [Pi.mulSingle_eq_same, toAdd_ofAdd, hone, pow_one]
    · intro u _ hu
      rw [Pi.mulSingle_eq_of_ne hu, toAdd_one, ZMod.val_zero, pow_zero]
    · intro h
      exact absurd (Finset.mem_univ t) h
  have hsep' : ∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
      FrobeniusGroupField.res hv (U.sg k (b (some (i, k, false)))) ≠ FrobeniusGroupField.res hv (U.sg i (b (some (i, k, false)))) := by
    intro i k hi hk hik
    have hq := hQ (some (i, k, false)) hi hk (by simpa using hik)
    simpa using hq
  have hsepψ : ∀ j k, U.εT j ≠ 0 → U.εT k ≠ 0 → j ≠ k → ∃ γ : G, U.sg j (β γ) ≠ U.sg k (β γ) := by
    intro j k hj hk hjk
    refine ⟨gen (some (j, k, false)), ?_⟩
    rw [hgen]
    intro heq
    exact hsep' j k hj hk hjk (by rw [heq])
  refine ⟨G, inferInstance, inferInstance, β, hmul, h1, hcard, ?_, ?_, ?_⟩
  · intro i γ hi
    obtain ⟨j, hj, hψ⟩ := FrobeniusGroupField.proj p hv hpv hcard (fun γ => H.ρ (β γ)) hmul h1 U.εT U.εT_orth
      U.εT_sum (fun j γ => U.sg j (β γ)) (fun j γ => U.εT_eig (β γ) j)
      (fun j k hj hk hjk => hsepψ j k hj hk hjk) i hi
    have hjφ : j = U.φ i := by
      by_contra hne
      have hq := hQ (some (i, j, true)) hi hj (by simpa using hne)
      simp only [Bool.toNat_true, pow_one] at hq
      have h2 := hψ (gen (some (i, j, true)))
      simp only [hgen] at h2
      exact hq (by rw [h2, map_pow])
    rw [← hjφ]
    exact hψ γ
  · intro i k hi hk hik
    refine ⟨gen (some (i, k, false)), ?_⟩
    rw [hgen]
    apply (FrobeniusGroupField.res_ne_zero hv _).1
    rw [map_sub, sub_ne_zero]
    exact (hsep' i k hi hk hik).symm
  · intro i hi
    exact ⟨gen none, by rw [hgen]; exact hQ none i hi⟩

end ReciprocityTheory.PGsh.Up
end
end

namespace ReciprocityTheory.PGsh.Up

theorem frobenius_of_length_lifts (hLen : LenIdStatement) (hEx : LenExStatement) (hTot : EigenLengthProductStatement)
    (hG : EmbeddingSeparatingGroupStatement) (hE : EigenElementaryDivisorStatement) (hR : EigenRankStatement)
    (hB : EigenLiftsBasisStatement) (hF : EigenLiftsFrobeniusStatement) : UnramifiedCokernelLengthStatement :=
  unramifiedCokernelLength_of_length_eigenLengthProduct hLen hEx hTot (core_of (lifts_of hG hE hR) hB hF)

theorem unramifiedCokernelLength_of_eigen_elementaryDivisor_rank_lifts (hG : EmbeddingSeparatingGroupStatement) (hE : EigenElementaryDivisorStatement)
    (hR : EigenRankStatement) (hB : EigenLiftsBasisStatement) (hF : EigenLiftsFrobeniusStatement) : UnramifiedCokernelLengthStatement :=
  frobenius_of_length_lifts lenId lenEx eigenLengthProductStatement_holds hG hE hR hB hF

theorem frobenius_of_group_divisors_rank (hG : EmbeddingSeparatingGroupStatement) (hE : EigenElementaryDivisorStatement) (hR : EigenRankStatement)
    (hF1 : LiftMonomialDeterminantStatement) (hF2 : FrobeniusBlockStatement) (hF3 : FrobeniusLengthBoundStatement) : UnramifiedCokernelLengthStatement :=
  unramifiedCokernelLength_of_eigen_elementaryDivisor_rank_lifts hG hE hR monomials_span_of_prod_eq (frob_of hF1 hF2 hF3)

theorem unramifiedCokernelLength_of_monomialDeterminant_frobeniusBlock_lengthBound (hG : EmbeddingSeparatingGroupStatement) (hF1 : LiftMonomialDeterminantStatement) (hF2 : FrobeniusBlockStatement)
    (hF3 : FrobeniusLengthBoundStatement) : UnramifiedCokernelLengthStatement :=
  frobenius_of_group_divisors_rank hG elementary_divisor_statement rank_eq_rank_of_perm_and_zero hF1 hF2 hF3

theorem unramifiedCokernelLength_of_frobeniusLengthBound (hG : EmbeddingSeparatingGroupStatement) (hF3 : FrobeniusLengthBoundStatement) : UnramifiedCokernelLengthStatement :=
  unramifiedCokernelLength_of_monomialDeterminant_frobeniusBlock_lengthBound hG liftMonomialDeterminantStatement_holds frobeniusBlock hF3

theorem frobenius_of_group (hG : EmbeddingSeparatingGroupStatement) : UnramifiedCokernelLengthStatement :=
  unramifiedCokernelLength_of_frobeniusLengthBound hG u7F3

theorem u7 : UnramifiedCokernelLengthStatement :=
  frobenius_of_group embeddingSeparatingGroup

end ReciprocityTheory.PGsh.Up

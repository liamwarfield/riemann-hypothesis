module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.PtSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpecIntIff

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.ExtendPt
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExtendPt
theorem UpperTheory.Reformulated.B.Qi4.extendPt :
    ∀ (O Λ T K : Type) [inst : CommRing O] [inst_1 : CommRing Λ] [inst_2 : CommRing T]
    [inst_3 : Field K] [IsAlgClosed K] [inst_5 : Algebra O Λ] [inst_6 : Algebra O T] [inst_7 : Algebra Λ T]
    [IsScalarTower O Λ T] [inst_9 : Algebra O K] [Algebra.IsIntegral Λ T] (P : Ideal T) (y : Λ →ₐ[O] K),
    Ideal.comap (Algebra.algebraMap Λ T) P ≤ RingHom.ker y →
      ∃ (x : T →ₐ[O] K),
        P ≤ RingHom.ker x ∧ ∀ (a : Λ), (x : T → K) ((Algebra.algebraMap Λ T : Λ → T) a) = (y : Λ → K) a := by
  intro O Λ T K _ _ _ _ _ _ _ _ _ _ _ P y hP
  haveI hprime : (RingHom.ker y).IsPrime := RingHom.ker_isPrime y
  obtain ⟨Q, hPQ, hQ, hQc⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker y) P hP
  change Q.comap (algebraMap Λ T) = RingHom.ker y at hQc
  have hker : ∀ a ∈ Q.comap (algebraMap Λ T), (y : Λ →+* K) a = 0 := by
    intro a ha
    rw [hQc] at ha
    exact ha
  let ybar : (Λ ⧸ Q.comap (algebraMap Λ T)) →+* K := Ideal.Quotient.lift _ (y : Λ →+* K) hker
  have hinj : Function.Injective ybar := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem, hQc]
    exact ha
  letI : Algebra (Λ ⧸ Q.comap (algebraMap Λ T)) K := ybar.toAlgebra
  haveI : FaithfulSMul (Λ ⧸ Q.comap (algebraMap Λ T)) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : FaithfulSMul (Λ ⧸ Q.comap (algebraMap Λ T)) (T ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Ideal.algebraMap_quotient_injective
  haveI : Module.IsTorsionFree (Λ ⧸ Q.comap (algebraMap Λ T)) (T ⧸ Q) :=
    FaithfulSMul.to_isTorsionFree _ _
  haveI : Module.IsTorsionFree (Λ ⧸ Q.comap (algebraMap Λ T)) K :=
    FaithfulSMul.to_isTorsionFree _ _
  haveI hint : Algebra.IsIntegral (Λ ⧸ Q.comap (algebraMap Λ T)) (T ⧸ Q) :=
    Algebra.IsIntegral.quotient
  haveI : Algebra.IsAlgebraic (Λ ⧸ Q.comap (algebraMap Λ T)) (T ⧸ Q) :=
    Algebra.IsIntegral.isAlgebraic
  let z : (T ⧸ Q) →ₐ[Λ ⧸ Q.comap (algebraMap Λ T)] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hz : ∀ a : Λ, z (Ideal.Quotient.mk Q (algebraMap Λ T a)) = y a := fun a =>
    z.commutes (Ideal.Quotient.mk _ a)
  refine ⟨{ (z : (T ⧸ Q) →+* K).comp (Ideal.Quotient.mk Q) with commutes' := fun o => ?_ }, ?_, hz⟩
  · have h := hz (algebraMap O Λ o)
    rw [← IsScalarTower.algebraMap_apply, y.commutes] at h
    exact h
  · intro t ht
    have h0 : Ideal.Quotient.mk Q t = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hPQ ht)
    show z (Ideal.Quotient.mk Q t) = 0
    rw [h0, map_zero]
end

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.extendPt :
    ∀ (O Λ T K : Type) [CommRing O] [CommRing Λ] [CommRing T] [Field K] [IsAlgClosed K] [Algebra O Λ] [Algebra O T] [Algebra Λ T] [IsScalarTower O Λ T] [Algebra O K] [Algebra.IsIntegral Λ T] (P : Ideal T) (y : Λ →ₐ[O] K), P.comap (algebraMap Λ T) ≤ RingHom.ker y → ∃ x : T →ₐ[O] K, P ≤ RingHom.ker x ∧ ∀ a, x (algebraMap Λ T a) = y a :=
  _root_.UpperTheory.Reformulated.B.Qi4.extendPt
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2LocSub
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem ls_le {A T K : Type} [CommRing A] [CommRing T] [Algebra A T] [Algebra.IsIntegral A T] [NormedField K]
    [IsUltrametricDist K] (z : T →+* K) (h1 : ∀ b, ‖z (algebraMap A T b)‖ ≤ 1) (s : T) : ‖z s‖ ≤ 1 := by
  obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := A) s
  by_contra hgt
  push_neg at hgt
  have hev := congrArg z hp
  rw [Polynomial.hom_eval₂, map_zero, Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ,
    ← Polynomial.leadingCoeff, hpm.leadingCoeff, map_one, one_mul] at hev
  set N := p.natDegree
  have hx1 : 1 ≤ ‖z s‖ := hgt.le
  rcases Nat.eq_zero_or_pos N with hN | hN
  · rw [hN, Finset.sum_range_zero, pow_zero, zero_add] at hev
    exact one_ne_zero hev
  have hsum : ‖∑ i ∈ Finset.range N, (z.comp (algebraMap A T)) (p.coeff i) * z s ^ i‖ ≤ ‖z s‖ ^ (N - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow, RingHom.comp_apply]
    have hiN : i ≤ N - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc ‖z (algebraMap A T (p.coeff i))‖ * ‖z s‖ ^ i ≤ 1 * ‖z s‖ ^ (N - 1) := by
          apply mul_le_mul (h1 _) (pow_le_pow_right₀ hx1 hiN) (by positivity) zero_le_one
      _ = ‖z s‖ ^ (N - 1) := one_mul _
  have heq : z s ^ N = -∑ i ∈ Finset.range N, (z.comp (algebraMap A T)) (p.coeff i) * z s ^ i :=
    eq_neg_of_add_eq_zero_right hev
  have hlt : ‖z s‖ ^ (N - 1) < ‖z s‖ ^ N := pow_lt_pow_right₀ hgt (by omega)
  rw [← norm_pow (z s) N, heq, norm_neg] at hlt
  linarith

private theorem ls_small {T K : Type} [CommRing T] [NormedField K] [IsUltrametricDist K] (z : T →+* K)
    (h1 : ∀ s, ‖z s‖ ≤ 1) : ∃ J : Ideal T, ∀ s, s ∈ J ↔ ‖z s‖ < 1 := by
  refine ⟨{ carrier := {s | ‖z s‖ < 1}
            add_mem' := fun {a b} ha hb => ?_
            zero_mem' := by simp
            smul_mem' := fun c x hx => ?_ }, fun s => Iff.rfl⟩
  · show ‖z (a + b)‖ < 1
    rw [map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  · show ‖z (c * x)‖ < 1
    rw [map_mul, norm_mul]
    calc ‖z c‖ * ‖z x‖ ≤ 1 * ‖z x‖ := by gcongr; exact h1 c
      _ < 1 := by rw [one_mul]; exact hx

private theorem ls_core {A T K ι ι' : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] [CommRing T] [Algebra A T] [Module.Finite A T] [NormedField K]
    [IsUltrametricDist K] [IsAlgClosed K] (x : A →+* K) (hx1 : ∀ b, ‖x b‖ ≤ 1) (hx2 : ∀ b ∈ maximalIdeal A, ‖x b‖ < 1)
    (htf : ∀ (b : A) (f : T), algebraMap A T b * f = 0 → b = 0 ∨ f = 0) (t : ι → T) (a : ι → A) (j : ι' → ι)
    (htop : Algebra.adjoin A (Set.range t) = ⊤)
    (H : ∀ z : T →+* K, z.comp (algebraMap A T) = x → (∀ i, ‖z (t (j i) - algebraMap A T (a (j i)))‖ < 1) →
      ∀ i, ‖z (t i - algebraMap A T (a i))‖ < 1) :
    ∃ e : T, IsIdempotentElem e ∧
      (∀ i, ∃ n : ℕ, (t i - algebraMap A T (a i)) ^ n * e ∈ (maximalIdeal A).map (algebraMap A T)) ∧
      1 - e ∈ (maximalIdeal A).map (algebraMap A T) ⊔
        Ideal.span (Set.range fun i => t (j i) - algebraMap A T (a (j i))) := by
  classical
  haveI : Algebra.IsIntegral A T := Algebra.IsIntegral.of_finite A T
  haveI : IsNoetherian A T := isNoetherian_of_isNoetherianRing_of_finite A T
  obtain ⟨e, he, hen, he1, -, -⟩ := AlgebraTools.AnnihilatorQuotientFinite.locAbs A T ι t a htop
  set T0 := Algebra.adjoin A (Set.range (fun i => t (j i))) with hT0
  have t0mem : ∀ i, t (j i) ∈ T0 := fun i => Algebra.subset_adjoin ⟨i, rfl⟩
  haveI : Module.Finite A T0 := Module.Finite.of_injective T0.val.toLinearMap Subtype.val_injective
  have hset : Set.range (fun i => (⟨t (j i), t0mem i⟩ : T0)) =
      ((↑) : T0 → T) ⁻¹' Set.range (fun i => t (j i)) := by
    ext ⟨y, hy⟩
    simp only [Set.mem_range, Set.mem_preimage, Subtype.mk.injEq]
  have htop0 : Algebra.adjoin A (Set.range (fun i => (⟨t (j i), t0mem i⟩ : T0))) = ⊤ := by
    rw [hset]
    exact Algebra.adjoin_adjoin_coe_preimage
  obtain ⟨e0, he0, he0n, he01, -, -⟩ := AlgebraTools.AnnihilatorQuotientFinite.locAbs A T0 ι' (fun i => ⟨t (j i), t0mem i⟩)
    (fun i => a (j i)) htop0
  have hmm : ((maximalIdeal A).map (algebraMap A T0)) ≤
      ((maximalIdeal A).map (algebraMap A T)).comap (T0.val : T0 →+* T) := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, Ideal.mem_comap]
    exact Ideal.mem_map_of_mem _ hb
  have hIj : ((maximalIdeal A).map (algebraMap A T0) ⊔ Ideal.span (Set.range fun i =>
      (⟨t (j i), t0mem i⟩ : T0) - algebraMap A T0 (a (j i)))) ≤
      ((maximalIdeal A).map (algebraMap A T) ⊔ Ideal.span (Set.range fun i =>
        t (j i) - algebraMap A T (a (j i)))).comap (T0.val : T0 →+* T) := by
    refine sup_le (hmm.trans (Ideal.comap_mono le_sup_left)) ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
  set e0' : T := (e0 : T) with he0'
  have he0i : IsIdempotentElem e0' := he0.map T0.val
  have h1e0 : 1 - e0' ∈ (maximalIdeal A).map (algebraMap A T) ⊔ Ideal.span (Set.range fun i =>
      t (j i) - algebraMap A T (a (j i))) := by
    have := hIj he01
    rw [Ideal.mem_comap] at this
    simpa using this
  set f := e0' * (1 - e) with hf
  have hfi : IsIdempotentElem f := he0i.mul he.one_sub
  have hf0 : f = 0 := by
    by_contra hfne
    have hnil : f ∉ nilradical T := by
      intro hn
      obtain ⟨k, hk⟩ := hn
      apply hfne
      rcases k with _ | k
      · rw [pow_zero] at hk
        have := congrArg (· * f) hk
        simpa using this
      · rwa [hfi.pow_succ_eq] at hk
    rw [nilradical_eq_sInf, Ideal.mem_sInf] at hnil
    push_neg at hnil
    obtain ⟨P, hP, hfP⟩ := hnil
    haveI : P.IsPrime := hP
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := P) bot_le
    have hfQ : f ∉ Q := fun h => hfP (hQP h)
    haveI hQp : Q.IsPrime := hQ.1.1
    have hQA : Ideal.comap (algebraMap A T) Q ≤ RingHom.ker x.toIntAlgHom := by
      intro b hb
      rw [Ideal.mem_comap] at hb
      have hd := Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hQ
      have hnz : algebraMap A T b ∉ nonZeroDivisors T := Set.disjoint_left.mp hd hb
      rw [mem_nonZeroDivisors_iff, not_and_or] at hnz
      have hex : ∃ y : T, algebraMap A T b * y = 0 ∧ y ≠ 0 := by
        rcases hnz with h | h
        · push_neg at h
          exact h
        · push_neg at h
          obtain ⟨y, hy, hy0⟩ := h
          exact ⟨y, by rw [mul_comm]; exact hy, hy0⟩
      obtain ⟨y, hy, hy0⟩ := hex
      rcases htf b y hy with hb0 | hyz
      · rw [RingHom.mem_ker, hb0, map_zero]
      · exact absurd hyz hy0
    obtain ⟨z, hQz, hzx⟩ := AlgebraTools.AnnihilatorQuotientFinite.extendPt ℤ A T K Q x.toIntAlgHom hQA
    let zr : T →+* K := z.toRingHom
    have hzx' : ∀ b, zr (algebraMap A T b) = x b := hzx
    have hbd : ∀ s, ‖zr s‖ ≤ 1 := ls_le zr (fun b => by rw [hzx']; exact hx1 b)
    obtain ⟨J, hJ⟩ := ls_small zr hbd
    have hmJ : (maximalIdeal A).map (algebraMap A T) ≤ J := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, hJ, hzx']
      exact hx2 b hb
    have hzf : zr f = 1 := by
      have h0 : f * (1 - f) ∈ Q := by
        rw [mul_sub, mul_one, hfi.eq, sub_self]
        exact Q.zero_mem
      have h1 : 1 - f ∈ Q := (hQp.mem_or_mem h0).resolve_left hfQ
      have h2 : zr (1 - f) = 0 := hQz h1
      rw [map_sub, map_one, sub_eq_zero] at h2
      exact h2.symm
    have hze0 : zr e0' = 1 ∧ zr (1 - e) = 1 := by
      have hp : zr e0' * zr (1 - e) = 1 := by rw [← map_mul]; exact hzf
      rcases IsIdempotentElem.iff_eq_zero_or_one.mp (he0i.map zr) with h | h
      · rw [h, zero_mul] at hp
        exact absurd hp zero_ne_one
      · rw [h, one_mul] at hp
        exact ⟨h, hp⟩
    have hj : ∀ i, ‖zr (t (j i) - algebraMap A T (a (j i)))‖ < 1 := by
      intro i
      obtain ⟨n, hn⟩ := he0n i
      have hn' := hmm hn
      rw [Ideal.mem_comap] at hn'
      have hn'' : (t (j i) - algebraMap A T (a (j i))) ^ n * e0' ∈
          (maximalIdeal A).map (algebraMap A T) := by simpa using hn'
      have hs := (hJ _).1 (hmJ hn'')
      rw [map_mul, map_pow, hze0.1, mul_one, norm_pow] at hs
      rcases n with _ | n
      · rw [pow_zero] at hs
        exact absurd hs (lt_irrefl 1)
      · exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) (Nat.succ_ne_zero n)).1 hs
    have hall := H zr (RingHom.ext hzx') hj
    have h1e : 1 - e ∈ J := by
      refine (sup_le hmJ ?_) he1
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (hJ _).2 (hall i)
    have hlt := (hJ _).1 h1e
    rw [hze0.2, norm_one] at hlt
    exact lt_irrefl 1 hlt
  refine ⟨e, he, hen, ?_⟩
  have : 1 - e = (1 - e0') * (1 - e) + f := by rw [hf]; ring
  rw [this, hf0, add_zero]
  exact Ideal.mul_mem_right _ _ h1e0

private theorem ls_restr_pow {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {Y : Submodule A M}
    {t : Module.End A Y} {φ : Module.End A M} (h : Restr t φ) (n : ℕ) : Restr (t ^ n) (φ ^ n) := by
  induction n with
  | zero => intro y; simp
  | succ n ih => intro y; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

private theorem ls_mem {A M ι : Type} [CommRing A] [IsLocalRing A] [AddCommGroup M] [Module A M]
    {Y : Submodule A M} {op : ι → Module.End A M} {a : ι → A} (u : ι → Module.End A Y)
    (hu : ∀ i, Restr (u i) (op i - algebraMap A _ (a i))) (y : Y) :
    (y : M) ∈ locPart Y op a ↔
      ∀ (i : ι) (k : ℕ), ∃ n : ℕ, (u i ^ n) y ∈ maximalIdeal A ^ k • (⊤ : Submodule A Y) := by
  have hY : ∀ i, ∀ x ∈ Y, (op i - algebraMap A (Module.End A M) (a i)) x ∈ Y := fun i x hx => by
    rw [← hu i ⟨x, hx⟩]
    exact (u i ⟨x, hx⟩).2
  have hP : ∀ i k, ∀ z ∈ maximalIdeal A ^ k • Y,
      (op i - algebraMap A (Module.End A M) (a i)) z ∈ maximalIdeal A ^ k • Y := by
    intro i k z hz
    have hle : maximalIdeal A ^ k • Y ≤
        (maximalIdeal A ^ k • Y).comap (op i - algebraMap A (Module.End A M) (a i)) := by
      rw [Submodule.smul_le]
      intro r hr x hx
      rw [Submodule.mem_comap, map_smul]
      exact Submodule.smul_mem_smul hr (hY i x hx)
    exact hle hz
  have hdir : ∀ i k, Directed (· ≤ ·) (fun n : ℕ =>
      (maximalIdeal A ^ k • Y).comap ((op i - algebraMap A (Module.End A M) (a i)) ^ n)) := by
    intro i k
    apply Monotone.directed_le
    apply monotone_nat_of_le_succ
    intro n x hx
    rw [Submodule.mem_comap] at hx ⊢
    rw [pow_succ', Module.End.mul_apply]
    exact hP i k _ hx
  have hsm : ∀ k (z : Y), z ∈ maximalIdeal A ^ k • (⊤ : Submodule A Y) ↔ (z : M) ∈ maximalIdeal A ^ k • Y := by
    intro k z
    have hmap : (maximalIdeal A ^ k • (⊤ : Submodule A Y)).map Y.subtype = maximalIdeal A ^ k • Y := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top]
    rw [← hmap]
    constructor
    · intro hz
      exact Submodule.mem_map_of_mem hz
    · rintro ⟨w, hw, hwz⟩
      have hwz' : w = z := Subtype.ext hwz
      rwa [← hwz']
  rw [locPart, Submodule.mem_inf]
  simp only [Submodule.mem_iInf]
  constructor
  · rintro ⟨-, h⟩ i k
    obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ (hdir i k)).1 (h i k)
    refine ⟨n, (hsm k _).2 ?_⟩
    rw [ls_restr_pow (hu i) n y]
    exact hn
  · intro h
    refine ⟨y.2, fun i k => ?_⟩
    obtain ⟨n, hn⟩ := h i k
    refine (Submodule.mem_iSup_of_directed _ (hdir i k)).2 ⟨n, ?_⟩
    rw [Submodule.mem_comap, ← ls_restr_pow (hu i) n y]
    exact (hsm k _).1 hn

theorem UpperTheory.V.Hi.levelUR2LocSub :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (A M ι ι' : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] [IsDomain A] [AddCommGroup M] [Module A M] (Y : Submodule A M) [Module.Finite A Y] [Module.Free A Y] (op : ι → Module.End A M) [Fact (CommOn Y op)] (j : ι' → ι) (a : ι → c.O) (x : A →ₐ[c.O] Qbar l), (∀ z : heckeAlg Y op →+* Qbar l, z.comp (algebraMap A _) = x.toRingHom → (∀ i, ‖z (heckeGen Y op (j i)) - algebraMap c.O (Qbar l) (a (j i))‖ < 1) → ∀ i, ‖z (heckeGen Y op i) - algebraMap c.O (Qbar l) (a i)‖ < 1) → locPart Y (fun i => op (j i)) (fun i => algebraMap c.O A (a (j i))) = locPart Y op fun i => algebraMap c.O A (a i) := by
  intro l _ c A M ι ι' _ _ _ _ _ _ Y _ _ op _ j a x hH
  haveI := Alg.IsCO.toIsLocalRing c.O (R := A)
  haveI : IsNoetherianRing A := Alg.IsCO.toIsNoetherian (O := c.O)
  haveI : IsAdicComplete (maximalIdeal A) A := Alg.IsCO.complete (O := c.O)
  haveI : Module.Finite A (heckeAlg Y op) :=
    Module.IsNoetherian.finite A (Subalgebra.toSubmodule (heckeAlg Y op))
  let ρ : heckeAlg Y op →+* Module.End A Y := (heckeAlg Y op).val.toRingHom
  let u : ι → heckeAlg Y op := fun i => heckeGen Y op i - algebraMap A _ (algebraMap c.O A (a i))
  have hR : ∀ i, Restr (ρ (u i)) (op i - algebraMap A (Module.End A M) (algebraMap c.O A (a i))) := by
    intro i y
    simp [ρ, u, heckeGen, Module.algebraMap_end_apply]
  have htf : ∀ (b : A) (f : heckeAlg Y op), algebraMap A _ b * f = 0 → b = 0 ∨ f = 0 := by
    intro b f hbf
    by_cases hb : b = 0
    · exact Or.inl hb
    right
    apply Subtype.ext
    apply LinearMap.ext
    intro y
    have h := congrArg (fun g : heckeAlg Y op => (g : Module.End A Y) y) hbf
    simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Module.End.mul_apply,
      Module.algebraMap_end_apply, ZeroMemClass.coe_zero, LinearMap.zero_apply] at h
    simpa [hb] using h
  have htop : Algebra.adjoin A (Set.range (heckeGen Y op)) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨g, hg⟩ -
    have key : heckeAlg Y op ≤ (Algebra.adjoin A (Set.range (heckeGen Y op))).map (heckeAlg Y op).val := by
      refine Algebra.adjoin_le ?_
      rintro t ⟨i, hi⟩
      refine ⟨heckeGen Y op i, Algebra.subset_adjoin ⟨i, rfl⟩, ?_⟩
      apply LinearMap.ext
      intro y
      apply Subtype.ext
      rw [hi y]
      rfl
    obtain ⟨g', hg', hgg⟩ := key hg
    have : g' = ⟨g, hg⟩ := Subtype.ext hgg
    rwa [← this]
  have hza : ∀ z : heckeAlg Y op →+* Qbar l, z.comp (algebraMap A _) = x.toRingHom →
      ∀ i, z (algebraMap A _ (algebraMap c.O A (a i))) = algebraMap c.O (Qbar l) (a i) := by
    intro z hz i
    rw [← RingHom.comp_apply, hz]
    exact x.commutes _
  obtain ⟨e, he, hpow, hone⟩ := ls_core x.toRingHom (fun b => Up.pt_le x b) (fun b hb => Up.pt_lt x b hb) htf
    (heckeGen Y op) (fun i => algebraMap c.O A (a i)) j htop (by
      intro z hz hj i
      have h := hH z hz (fun i => by simpa only [map_sub, hza z hz] using hj i) i
      simpa only [map_sub, hza z hz] using h)
  have hI : ∀ μ ∈ (maximalIdeal A).map (algebraMap A (heckeAlg Y op)), ∀ y, ρ μ y ∈ maximalIdeal A • (⊤ : Submodule A Y) := by
    intro μ hμ
    induction hμ using Submodule.span_induction with
    | mem μ hμ =>
      obtain ⟨b, hb, rfl⟩ := hμ
      intro y
      have : ρ (algebraMap A _ b) y = b • y := by
        simp [ρ, Module.algebraMap_end_apply]
      rw [this]
      exact Submodule.smul_mem_smul hb trivial
    | zero => intro y; simp
    | add μ ν _ _ ihμ ihν =>
      intro y
      rw [map_add (f := _), LinearMap.add_apply]
      exact add_mem (ihμ y) (ihν y)
    | smul s μ _ ih =>
      intro y
      rw [smul_eq_mul, mul_comm, map_mul, Module.End.mul_apply]
      exact ih _
  have hone' : 1 - e ∈ (maximalIdeal A).map (algebraMap A (heckeAlg Y op)) ⊔ Ideal.span (Set.range u) := by
    have hle : Ideal.span (Set.range fun i => u (j i)) ≤ Ideal.span (Set.range u) :=
      Ideal.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨j i, rfl⟩)
    exact sup_le_sup_left hle _ hone
  have hfull := AlgebraTools.AnnihilatorQuotientFinite.locChar A Y (heckeAlg Y op) ι ρ _ u e hI he hpow hone'
  have hjj := AlgebraTools.AnnihilatorQuotientFinite.locChar A Y (heckeAlg Y op) ι' ρ _ (fun i => u (j i)) e hI he (fun i => hpow (j i)) hone
  ext m
  constructor
  · intro hm
    have hmY : m ∈ Y := (Submodule.mem_inf.mp hm).1
    have h1 := (ls_mem (fun i => ρ (u (j i))) (fun i => hR (j i)) ⟨m, hmY⟩).1 hm
    exact (ls_mem (fun i => ρ (u i)) hR ⟨m, hmY⟩).2 ((hfull _).1 ((hjj _).2 h1))
  · intro hm
    have hmY : m ∈ Y := (Submodule.mem_inf.mp hm).1
    have h1 := (ls_mem (fun i => ρ (u i)) hR ⟨m, hmY⟩).1 hm
    exact (ls_mem (fun i => ρ (u (j i))) (fun i => hR (j i)) ⟨m, hmY⟩).2 ((hjj _).1 ((hfull _).2 h1))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GalResContCoeff
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem galResContCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem UpperTheory.V.Hi.levelUR2GalRes :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (G : Type) [Group G] [TopologicalSpace G] (n : ℕ) (r : G →* GL (Fin n) (Qbar l)), Continuous r → ∀ φ : G → (ResidueField c.O)[X], IsLocallyConstant φ → ∀ S : Set G, Dense S → (∀ g ∈ S, ∀ (i : ℕ) (b : c.O), residue c.O b = (φ g).coeff i → ‖(r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i - algebraMap c.O (Qbar l) b‖ < 1) → ∀ g (i : ℕ) (b : c.O), residue c.O b = (φ g).coeff i → ‖(r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i - algebraMap c.O (Qbar l) b‖ < 1 := by
  intro l _ c G _ _ n r hr φ hφ S hS hSb g i b hb
  have hc : Continuous fun h : G => (r h : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
    (galResContCoeff n i).comp (Units.continuous_val.comp hr)
  have hU : IsOpen {h : G | φ h = φ g} := hφ.isOpen_fiber _
  have hW : IsOpen {h : G | ‖(r h : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i -
      (r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i‖ < 1} :=
    isOpen_lt (continuous_norm.comp (hc.sub continuous_const)) continuous_const
  obtain ⟨h, ⟨hh1, hh2⟩, hhS⟩ := hS.inter_open_nonempty _ (hU.inter hW) ⟨g, rfl, by simp⟩
  have key := hSb h hhS i b (by rw [hb, Set.mem_setOf_eq.mp hh1])
  have hh2' := Set.mem_setOf_eq.mp hh2
  rw [norm_sub_rev] at hh2'
  calc ‖(r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i - algebraMap c.O (Qbar l) b‖
      = ‖((r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i -
          (r h : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i) +
        ((r h : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i -
          algebraMap c.O (Qbar l) b)‖ := by congr 1; abel
    _ ≤ max _ _ := IsUltrametricDist.norm_add_le_max _ _
    _ < 1 := max_lt hh2' key
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance 2000] UpperTheory.V.W.coefLocal
set_option synthInstance.maxHeartbeats 200000

private theorem hecke_poly_coeff_formula {A : Type} [CommRing A] (n q : ℕ) (a : ℕ → A) (j : ℕ) (hj : j ≤ n) :
    (heckePol n q a).coeff (n - j) = (-1) ^ j * (q : A) ^ (j * (j - 1) / 2) * a j := by
  rw [mul_assoc, ← JEx.heckePol_coeff n q a j hj, ← mul_assoc, ← mul_pow]
  simp

private theorem hecke_poly_coeff_zero {A : Type} [CommRing A] (n q : ℕ) (a : ℕ → A) (i : ℕ) (hi : n < i) :
    (heckePol n q a).coeff i = 0 := by
  rw [Hi.heckePol, finsetSum_coeff]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [coeff_C_mul_X_pow, if_neg]
  omega

private theorem norm_lt_one_of_residue_zero {l : ℕ} [Fact l.Prime] (c : Coef l) (b : c.O) (hb : residue c.O b = 0) :
    ‖algebraMap c.O (Qbar l) b‖ < 1 := by
  have e : algebraMap c.O (Qbar l) b = (b : PadicAlgCl l) := rfl
  rw [e]
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at hb
  rcases eq_or_ne b 0 with rfl | h0
  · simp
  have h := UpperTheory.V.Base.normO l c.O b h0
  have hl : ((l : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hv : (IsDiscreteValuationRing.addVal c.O b).toNat ≠ 0 := by
    rw [Ne, ENat.toNat_eq_zero, IsDiscreteValuationRing.addVal_eq_zero_iff, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact fun h => h.elim hb h0
  have h1 := pow_lt_one₀ (by positivity) hl hv
  rw [← h] at h1
  by_contra hn
  exact absurd h1 (not_lt.2 (one_le_pow₀ (not_lt.1 hn)))

private theorem hecke_poly_coeff_congruence_iff {l : ℕ} [Fact l.Prime] (c : Coef l) (n q : ℕ) (hq : ‖(q : Qbar l)‖ = 1) (a : ℕ → Qbar l) (b : ℕ → c.O) :
    (∀ j ≤ n, ‖a j - algebraMap c.O (Qbar l) (b j)‖ < 1) ↔
      ∀ (i : ℕ) (b' : c.O), residue c.O b' = (heckePol n q fun j => residue c.O (b j)).coeff i →
        ‖(heckePol n q a).coeff i - algebraMap c.O (Qbar l) b'‖ < 1 := by
  have e : ∀ j ≤ n, ‖(heckePol n q a).coeff (n - j) - algebraMap c.O (Qbar l) ((heckePol n q b).coeff (n - j))‖ =
      ‖a j - algebraMap c.O (Qbar l) (b j)‖ := fun j hj => by
    rw [← coeff_map, JEx.heckePol_map, hecke_poly_coeff_formula _ _ _ _ hj, hecke_poly_coeff_formula _ _ _ _ hj, ← mul_sub]
    simp [hq]
  rw [← JEx.heckePol_map]
  constructor
  · intro h i b' hb
    rw [coeff_map] at hb
    have h1 : ‖algebraMap c.O (Qbar l) ((heckePol n q b).coeff i) - algebraMap c.O (Qbar l) b'‖ < 1 := by
      rw [← map_sub]
      exact norm_lt_one_of_residue_zero c _ (by rw [map_sub, hb, sub_self])
    have h2 : ‖(heckePol n q a).coeff i - algebraMap c.O (Qbar l) ((heckePol n q b).coeff i)‖ < 1 := by
      rcases le_or_gt i n with hi | hi
      · have := e (n - i) (Nat.sub_le _ _)
        rw [Nat.sub_sub_self hi] at this
        rw [this]
        exact h _ (Nat.sub_le _ _)
      · rw [hecke_poly_coeff_zero _ _ _ _ hi, hecke_poly_coeff_zero _ _ _ _ hi]
        simp
    rw [← sub_add_sub_cancel _ (algebraMap c.O (Qbar l) ((heckePol n q b).coeff i))]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h2 h1)
  · intro h j hj
    rw [← e j hj]
    exact h _ _ (coeff_map _ _).symm

private theorem hecke_part_frobenius {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hH : H.Ax) (ι : Qbar l ≃+* ℂ) {lam : Wt L l n} {d : ℕ}
    {ξ : GV n H.Sl →* GL (Fin d) ℂ} (Y : H.Part ι lam ξ) (a : H.Op → c.O) (w : H.Wp) (B : ValuationSubring Ω) (σ : G L Ω)
    (hB : IsPlaceOver B w.1) (hσ : IsFrob B (normV w.1) σ) :
    (∀ k : Fin n, ‖ι.symm (Y.a w (k + 1)) - algebraMap c.O (Qbar l) (a (.inl (w, k)))‖ < 1) ↔
      ∀ (i : ℕ) (b : c.O), residue c.O b = (heckePol n (normV w.1) fun j =>
          if h : 0 < j ∧ j - 1 < n then residue c.O (a (.inl (w, ⟨j - 1, h.2⟩))) else 1).coeff i →
        ‖(Y.r (H.prj σ⁻¹) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i - algebraMap c.O (Qbar l) b‖ < 1 := by
  have hq : ‖((normV w.1 : ℕ) : Qbar l)‖ = 1 := by
    have h0 := (cycZ L Ω l σ).isUnit
    rw [cycZ_of_isFrob (hH.Wp_away w.1 w.2) hB hσ, PadicInt.isUnit_iff] at h0
    rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap', ← h0, PadicInt.norm_def, PadicInt.coe_natCast]
  have e : (Y.r (H.prj σ⁻¹) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly = heckePol n (normV w.1) fun j => ι.symm (Y.a w j) := by
    refine Polynomial.map_injective ι.toRingHom ι.injective ?_
    rw [Y.frob w B σ hB hσ, JEx.heckePol_map]
    simp
  have e2 : (fun j => if h : 0 < j ∧ j - 1 < n then residue c.O (a (.inl (w, ⟨j - 1, h.2⟩))) else 1) =
      fun j => residue c.O (if h : 0 < j ∧ j - 1 < n then a (.inl (w, ⟨j - 1, h.2⟩)) else 1) := by
    funext j
    split_ifs
    · rfl
    · exact (map_one _).symm
  rw [e, e2, ← hecke_poly_coeff_congruence_iff c n _ hq]
  constructor
  · intro h j hj
    rcases j with _ | j
    · rw [Y.a_zero, dite_eq_right (by omega)]
      simp
    · rw [dite_eq_left ⟨Nat.succ_pos _, hj⟩]
      exact h ⟨j, hj⟩
  · intro h k
    have := h (k + 1) k.2
    rw [dite_eq_left ⟨Nat.succ_pos _, k.2⟩] at this
    exact this

theorem UpperTheory.V.Hi.levelUR2H3Abs :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    IsDomain A → ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.Aut ι P → ∀ lam0 ∈ H.admitted, H.DenseWt θ lam0 → ∀ (a : H.Op → c.O) (K : H.Lev) (φ : H.Gq → (ResidueField c.O)[X]), IsLocallyConstant φ → (∀ (w : H.Wp) (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) σ → φ (H.prj σ⁻¹) = heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then residue c.O (a (.inl (w, ⟨j - 1, h.2⟩))) else 1) → ∀ (ι' : Type) (j : ι' → H.Op), (∀ x, Sum.inr x ∈ Set.range j) → Dense {g : H.Gq | ∃ w : H.Wp, (∀ k, Sum.inl (w, k) ∈ Set.range j) ∧ ∃ (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 ∧ IsFrob B (normV w.1) σ ∧ g = H.prj σ⁻¹} → locPart (H.X.Ord (H.τA A) θ (H.lev K)) (fun i => H.op A (j i)) (fun i => algebraMap c.O A (a (j i))) = H.MK θ a K := by
  intro _ L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ hA ι P hP lam0 _ hd a K φ hφ hφ2 ι' j hj hD
  obtain ⟨hC, hfi, hfr, -⟩ := hiComm L Ω l n c H hH A θ hθ K
  haveI : Fact (CommOn (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A)) := ⟨hC⟩
  obtain ⟨x, hx⟩ : ∃ x : A →ₐ[c.O] Qbar l, H.Good θ x lam0 := by
    by_contra h
    exact one_ne_zero (hd 1 fun x hx => absurd ⟨x, hx⟩ h)
  obtain ⟨d, ξ, c0, sp, hsp⟩ := spec L Ω l n c H hH A θ hθ ι x lam0 hx.2.1
  refine levelUR2LocSub l c A _ _ ι' _ (H.op A) j a x fun z hz h => ?_
  obtain ⟨Y, hY⟩ := levelUR2OrdPt L Ω l n c H hH A θ hθ ι P hP x lam0 d ξ c0 sp hsp hx.1 K z hz
  have hall := levelUR2GalRes l c H.Gq n Y.r Y.cont φ hφ _ hD (by
    rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
    rw [hφ2 w B σ hB hσ]
    refine (hecke_part_frobenius H hH ι Y a w B σ hB hσ).1 fun k => ?_
    obtain ⟨i, hi⟩ := hw k
    rw [hY, ι.symm_apply_apply, ← hi]
    exact h i)
  rintro (⟨w, k⟩ | y)
  · obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w.1
    obtain ⟨σ, hσ⟩ := exists_isFrob hB
    have := (hecke_part_frobenius H hH ι Y a w B σ hB hσ).2 (by
      rw [← hφ2 w B σ hB hσ]
      exact hall _) k
    rwa [hY, ι.symm_apply_apply] at this
  · obtain ⟨i, hi⟩ := hj y
    rw [← hi]
    exact h i

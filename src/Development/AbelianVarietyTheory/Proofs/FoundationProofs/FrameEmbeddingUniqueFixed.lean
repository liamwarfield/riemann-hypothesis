module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeierstrassPFormalGroupLogUniformises
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCoverUpqKsetGeneratedByExp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumTaylorCoordinateSpaceEntire

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrameEmbeddingUniqueFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimeDvdMem
universe u_1

namespace GlobalTheory.PrimeDivisorMembership

theorem exists_prime_dvd_mem : ∀ {R : Type u_1} [inst : CommRing R] (P : Ideal R), Ideal.IsPrime P → ∀ (n : ℕ), n ≠ (0 : ℕ) → (↑n : R) ∈ P → ∃ (q : ℕ), Nat.Prime q ∧ q ∣ n ∧ (↑q : R) ∈ P := by
  intro R _ P hP n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hmem
    by_cases h1 : n = 1
    · subst h1
      rw [Nat.cast_one] at hmem
      exact absurd ((Ideal.eq_top_iff_one P).2 hmem) hP.ne_top
    · have hmin := Nat.minFac_prime h1
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      have hmem' : (n.minFac : R) * (m : R) ∈ P := by
        rw [← Nat.cast_mul, ← hm]
        exact hmem
      rcases hP.mem_or_mem hmem' with hq | hq
      · exact ⟨n.minFac, hmin, Nat.minFac_dvd n, hq⟩
      · have hm0 : m ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hm
          exact hn hm
        have hlt : m < n := by
          calc m < 2 * m := by omega
            _ ≤ n.minFac * m := Nat.mul_le_mul_right _ hmin.two_le
            _ = n := hm.symm
        obtain ⟨q, hq1, hq2, hq3⟩ := ih m hlt hm0 hq
        exact ⟨q, hq1, hq2.trans (Dvd.intro_left _ hm.symm), hq3⟩

end GlobalTheory.PrimeDivisorMembership
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrameEmbeddingUniqueFixed
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

namespace GlobalTheory.InertParity.FiniteOrder

theorem exists_prime_mem {R : Type*} [CommRing R] (P : Ideal R) (hP : P.IsPrime) (n : ℕ) (hn : n ≠ 0)
    (h : (n : R) ∈ P) : ∃ q : ℕ, q.Prime ∧ q ∣ n ∧ (q : R) ∈ P := by
  first
  | exact @_root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem
  | exact _root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem
  | (apply _root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem ..)

theorem simple_case (D : D7) (S : Type) [AddCommGroup S] [Module (𝓞 D.host.E) S] [Finite S]
    [IsSimpleModule (𝓞 D.host.E) S] :
    Ev D (Nat.card S) ∧ ((∀ q : ℕ, q.Prime → q ∣ Nat.card S → InertQ D q) → sgn D (Nat.card S) = -1) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := 𝓞 D.host.E) (M := S)).1 ‹_›
  have hc : Nat.card S = Ideal.absNorm P := by
    rw [Nat.card_congr e.toEquiv, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h0 : Ideal.absNorm P ≠ 0 := hc ▸ Nat.card_pos.ne'
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.absNorm_cmPrime_inertPrime_sign D P hP
  rw [hc]
  refine ⟨h1, fun h => ?_⟩
  by_cases hs : D.host.conj • P = P
  · exact (h2 hs).1
  · obtain ⟨q, hq, hd, hm⟩ := exists_prime_mem P hP.isPrime _ h0 (Ideal.absNorm_mem P)
    exact absurd (h q hq hd) ((h3 hs).2 q hq hm)

theorem card_parity_sign_length_of_eq (D : D7) (n : ℕ) : ∀ (M : Type) [AddCommGroup M] [Module (𝓞 D.host.E) M] [Finite M],
    Nat.card M = n → Ev D (Nat.card M) ∧ ((∀ q : ℕ, q.Prime → q ∣ Nat.card M → InertQ D q) →
      sgn D (Nat.card M) = (-1 : ℂ) ^ (Module.length (𝓞 D.host.E) M).toNat) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M _ _ _ hn
    rcases subsingleton_or_nontrivial M with hM | hM
    · have h1 : Nat.card M = 1 := Nat.card_of_subsingleton (0 : M)
      rw [h1, Module.length_eq_zero]
      exact ⟨Ev.one, fun _ => by simp [sgn_one]⟩
    · obtain ⟨N, hN⟩ : ∃ N : Submodule (𝓞 D.host.E) M, IsCoatom N := by
        rcases eq_top_or_exists_le_coatom (⊥ : Submodule (𝓞 D.host.E) M) with h | ⟨N, hN, -⟩
        · exact absurd h bot_ne_top
        · exact ⟨N, hN⟩
      haveI : Finite (M ⧸ N) := Finite.of_surjective _ N.mkQ_surjective
      haveI : IsSimpleModule (𝓞 D.host.E) (M ⧸ N) := isSimpleModule_iff_isCoatom.2 hN
      haveI : Nontrivial (M ⧸ N) := IsSimpleModule.nontrivial (𝓞 D.host.E) (M ⧸ N)
      have hc : Nat.card M = Nat.card N * Nat.card (M ⧸ N) := Submodule.card_eq_card_quotient_mul_card N
      have hq : 1 < Nat.card (M ⧸ N) := Finite.one_lt_card
      have hp : 0 < Nat.card N := Nat.card_pos
      obtain ⟨a1, a2⟩ := ih (Nat.card N) (by rw [← hn, hc]; exact lt_mul_of_one_lt_right hp hq) N rfl
      obtain ⟨b1, b2⟩ := simple_case D (M ⧸ N)
      have hl : Module.length (𝓞 D.host.E) M =
          Module.length (𝓞 D.host.E) N + Module.length (𝓞 D.host.E) (M ⧸ N) :=
        Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
          (LinearMap.exact_subtype_mkQ N)
      have hfin : Module.length (𝓞 D.host.E) N ≠ ⊤ := Module.length_ne_top
      rw [hl, Module.length_eq_one (R := 𝓞 D.host.E) (M := M ⧸ N), ENat.toNat_add hfin (by simp), hc]
      refine ⟨a1.mul b1 hp.ne' (by omega), fun h => ?_⟩
      rw [sgn_mul a1 b1 hp.ne' (by omega), a2 fun q hq hd => h q hq (hd.mul_right _),
        b2 fun q hq hd => h q hq (hd.mul_left _), pow_add]
      simp

theorem ev_card_and_sgn_card : ∀ (D : D7) (M : Type) [AddCommGroup M] [Module (𝓞 D.host.E) M] [Finite M], Ev D (Nat.card M) ∧ ((∀ q : ℕ, q.Prime → q ∣ Nat.card M → InertQ D q) → sgn D (Nat.card M) = (-1 : ℂ) ^ (Module.length (𝓞 D.host.E) M).toNat) :=
  fun D M _ _ _ => card_parity_sign_length_of_eq D _ M rfl

end GlobalTheory.InertParity.FiniteOrder
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrameEmbeddingUniqueFixedStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_module_sign_eq_neg_one_pow_length : ∀ (D : D7) (M : Type) [AddCommGroup M] [Module (𝓞 D.host.E) M] [Finite M], Ev D (Nat.card M) ∧ ((∀ q : ℕ, q.Prime → q ∣ Nat.card M → InertQ D q) → sgn D (Nat.card M) = (-1 : ℂ) ^ (Module.length (𝓞 D.host.E) M).toNat) := by
  first | exact @GlobalTheory.InertParity.FiniteOrder.ev_card_and_sgn_card | exact GlobalTheory.InertParity.FiniteOrder.ev_card_and_sgn_card | (intros; apply GlobalTheory.InertParity.FiniteOrder.ev_card_and_sgn_card <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactCoverUnHcModuleFiniteDimIrreducible
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactCoverUnHcModuleFiniteDimIrreducible
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.CompactCoverIrr

theorem isKC_of_compact {n : ℕ} (X : Mat n 0) : IsKC X := by
  rintro (a | a) (b | b) hab
  · exact (hab trivial).elim
  · exact b.elim0
  · exact a.elim0
  · exact a.elim0

theorem map_stable {n : ℕ} (hn : 1 ≤ n) (T : GrpData n 0) (τ : URep T) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H)
    (hj : IsHCMod τ M j) (N : Submodule ℂ M.V) [FiniteDimensional ℂ N]
    (hN : ∀ Z, ∀ y ∈ N, M.act Z y ∈ N) (g : T.G) : ∀ x ∈ N.map j, τ.π g x ∈ N.map j := by
  have hg := GlobalTheory.CoverKGen.kset_gen n 0 (by omega) T g (isKC_of_compact _)
  have key : (∀ x ∈ N.map j, τ.π g x ∈ N.map j) ∧ (∀ x ∈ N.map j, τ.π g⁻¹ x ∈ N.map j) := by
    induction hg using Subgroup.closure_induction with
    | mem k hk =>
      obtain ⟨X, ⟨hX, -⟩, rfl⟩ := hk
      have hf := GlobalTheory.RealPar.flow_mem_map j (M.act X) N (hN X) (fun t => τ.π (T.expt (t • X)))
        (by simp [T.expt_zero]) (fun s t => by simp only [T.expt_add X hX, map_mul]) (hj.2.2 X hX)
      have hinv : (T.expt X)⁻¹ = T.expt ((-1 : ℝ) • X) := by
        have h := T.expt_add X hX 1 (-1)
        rw [add_neg_cancel, zero_smul, T.expt_zero, one_smul] at h
        exact (eq_inv_of_mul_eq_one_right h.symm).symm
      refine ⟨?_, ?_⟩
      · have := hf 1
        rwa [one_smul] at this
      · rw [hinv]
        exact hf (-1)
    | one => refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> simpa using hx
    | mul a b _ _ ha hb =>
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [map_mul]
        exact ha.1 _ (hb.1 x hx)
      · rw [mul_inv_rev, map_mul]
        exact hb.2 _ (ha.2 x hx)
    | inv a _ ha => exact ⟨ha.2, by rw [inv_inv]; exact ha.1⟩
  exact key.1

theorem eq_bot_or_top {n : ℕ} (T : GrpData n 0) (τ : URep T) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H)
    (hτ : IrrU τ) (hj : Function.Injective j) (N : Submodule ℂ M.V) [FiniteDimensional ℂ N]
    (hN : ∀ g, ∀ x ∈ N.map j, τ.π g x ∈ N.map j) : N = ⊥ ∨ (N = ⊤ ∧ N.map j = ⊤) := by
  rcases hτ.2 (N.map j) (Submodule.closed_of_finiteDimensional _) hN with h | h
  · left
    apply Submodule.map_injective_of_injective hj
    rw [h, Submodule.map_bot]
  · right
    refine ⟨?_, h⟩
    rw [eq_top_iff]
    intro v _
    obtain ⟨w, hw, hwv⟩ : j v ∈ N.map j := h ▸ Submodule.mem_top
    exact hj hwv ▸ hw

theorem hcMod_finite_irr : ∀ (n : ℕ), 1 ≤ n → ∀ (T : GrpData n 0) (τ : URep T) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H), IrrU τ → IsHCMod τ M j → Nontrivial M.V → FiniteDimensional ℂ M.V ∧ IrrGK M ∧ (∀ h v, ∃ v', j v' = τ.π h (j v)) ∧ ∀ N : Submodule ℂ M.V, (∀ h, ∀ v ∈ N, ∀ v', j v' = τ.π h (j v) → v' ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro n hn T τ M j hτ hj hM
  obtain ⟨v, hv⟩ := exists_ne (0 : M.V)
  obtain ⟨W, hWf, hvW, hWs⟩ := M.kfin v
  have hW := (eq_bot_or_top T τ M j hτ hj.1 W
    (map_stable hn T τ M j hj W fun Z => hWs Z (isKC_of_compact Z))).resolve_left
    (fun h => hv (by rw [h] at hvW; exact hvW))
  have hfin : FiniteDimensional ℂ M.V := by
    rw [hW.1] at hWf
    exact Module.Finite.equiv (Submodule.topEquiv : (⊤ : Submodule ℂ M.V) ≃ₗ[ℂ] M.V)
  have hsurj : ∀ x, ∃ v', j v' = x := fun x => by
    obtain ⟨w, -, hw⟩ : x ∈ W.map j := hW.2 ▸ Submodule.mem_top
    exact ⟨w, hw⟩
  refine ⟨hfin, ⟨hM, fun N hN => ?_⟩, fun h v => hsurj _, fun N hN => ?_⟩
  · exact (eq_bot_or_top T τ M j hτ hj.1 N (map_stable hn T τ M j hj N hN)).imp_right And.left
  · refine (eq_bot_or_top T τ M j hτ hj.1 N ?_).imp_right And.left
    rintro g _ ⟨w, hw, rfl⟩
    obtain ⟨v', hv'⟩ := hsurj (τ.π g (j w))
    exact ⟨v', hN g w hw v' hv', hv'⟩

end GlobalTheory.CompactCoverIrr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactCoverUnHcModuleFiniteDimIrreducibleStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactCoverUn_hcModule_finiteDim_irreducible : ∀ (n : ℕ), 1 ≤ n → ∀ (T : GrpData n 0) (τ : URep T) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H), IrrU τ → IsHCMod τ M j → Nontrivial M.V → FiniteDimensional ℂ M.V ∧ IrrGK M ∧ (∀ h v, ∃ v', j v' = τ.π h (j v)) ∧ ∀ N : Submodule ℂ M.V, (∀ h, ∀ v ∈ N, ∀ v', j v' = τ.π h (j v) → v' ∈ N) → N = ⊥ ∨ N = ⊤ := by
  first | exact @GlobalTheory.CompactCoverIrr.hcMod_finite_irr | exact GlobalTheory.CompactCoverIrr.hcMod_finite_irr | (intros; apply GlobalTheory.CompactCoverIrr.hcMod_finite_irr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergRelativeIndexTranslateCompletedLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergRelativeIndexTranslateCompletedLattice
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.MovedIdx

theorem common_denom {A ι : Type} [CommRing A] [Fintype ι] (S : Subring A) (f : ι → A) (P : ℕ → Prop) (h1 : P 1)
    (hm : ∀ a b, P a → P b → P (a * b)) (h : ∀ i, ∃ n : ℕ, P n ∧ (n : A) * f i ∈ S) :
    ∃ n : ℕ, P n ∧ ∀ i, (n : A) * f i ∈ S := by
  choose n hn hf using h
  refine ⟨∏ i, n i, Finset.prod_induction _ P hm h1 fun i _ => hn i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  rw [hc, mul_comm (n i), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem S c) (hf i)

theorem dvd_of_dvd_idx {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (A B : Submodule R X) (n q : ℕ)
    (hq : q.Prime) (h0 : idx A B ≠ 0) (hn : ∀ x ∈ B, n • x ∈ A) (hd : q ∣ idx A B) : q ∣ n := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) := Nat.finite_of_card_ne_zero h0
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) q hd
  rw [← hx, addOrderOf_dvd_iff_nsmul_eq_zero]
  induction x using QuotientAddGroup.induction_on with
  | H y =>
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact hn y.1 y.2

theorem denom_mul (D : D7) {q : ℕ} (hq : q.Prime) {x : AE D} (hx : ZeroAt D q x) (y : AE D) :
    ∃ n : ℕ, n.Coprime q ∧ (n : AE D) * (y * x) ∈ OhE D := by
  obtain ⟨n, hn, hy⟩ := GlobalTheory.HeckeVal.exists_denom D y
  obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.ne_one
  obtain ⟨m, -, hmq, s, hs, h⟩ := hx a
  refine ⟨m * n', Nat.Coprime.mul_left hmq ((Nat.Prime.coprime_iff_not_dvd hq).2 hn').symm, ?_⟩
  convert mul_mem hs hy using 1
  push_cast
  linear_combination (n' : AE D) * y * h

theorem one_entry_mem (D : D7) {N : ℕ} (i j : Fin N) : (1 : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem denom_triv (D : D7) {q N : ℕ} {g : GL (Fin N) (AE D)} (hg : TrivAt D q g) :
    ∃ n : ℕ, n.Coprime q ∧ ∀ i j, (n : AE D) * (g : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  obtain ⟨n, hn, h⟩ := common_denom (OhE D) (fun p : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) (AE D)) p.1 p.2)
    (fun n => n.Coprime q) (by simp) (fun a b => Nat.Coprime.mul_left) (by
      rintro ⟨i, j⟩
      obtain ⟨m, -, hm, s, hs, e⟩ := hg i j 0
      refine ⟨m, hm, ?_⟩
      convert add_mem hs (mul_mem (natCast_mem _ m) (one_entry_mem D i j)) using 1
      linear_combination e)
  exact ⟨n, hn, fun i j => h (i, j)⟩

theorem denom_triv_inv (D : D7) {q N : ℕ} (hq : q.Prime) {g : GL (Fin N) (AE D)} (hg : TrivAt D q g) :
    ∃ n : ℕ, n.Coprime q ∧ ∀ i j, (n : AE D) * ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  obtain ⟨n, hn, h⟩ := common_denom (OhE D) (fun p : Fin N × Fin N × Fin N =>
      ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) p.1 p.2.1 *
      ((g : Matrix (Fin N) (Fin N) (AE D)) p.2.1 p.2.2 - (1 : Matrix (Fin N) (Fin N) (AE D)) p.2.1 p.2.2))
    (fun n => n.Coprime q) (by simp) (fun a b => Nat.Coprime.mul_left) (fun p => denom_mul D hq (hg _ _) _)
  refine ⟨n, hn, fun i j => ?_⟩
  have e : ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) =
      1 - ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) * ((g : Matrix (Fin N) (Fin N) (AE D)) - 1) := by
    rw [Matrix.mul_sub, Units.inv_mul, Matrix.mul_one, sub_sub_cancel]
  rw [e, Matrix.sub_apply, Matrix.mul_apply, mul_sub, Finset.mul_sum]
  exact sub_mem (mul_mem (natCast_mem _ n) (one_entry_mem D i j)) (sum_mem fun l _ => h (i, l, j))

theorem denom_mat (D : D7) {N : ℕ} (M : Matrix (Fin N) (Fin N) (AE D)) :
    ∃ n : ℕ, 0 < n ∧ ∀ i j, (n : AE D) * M i j ∈ OhE D := by
  obtain ⟨n, hn, h⟩ := common_denom (OhE D) (fun p : Fin N × Fin N => M p.1 p.2)
    (fun n => 0 < n) one_pos (fun a b => Nat.mul_pos) (fun p => GlobalTheory.HeckeVal.exists_denom D _)
  exact ⟨n, hn, fun i j => h (i, j)⟩

theorem nsmul_mem_latA (D : D7) (cc : Ideal (𝓞 D.host.K)) {N N' : ℕ} (g : GA D N) (g' : GA D N') {n n' : ℕ}
    (h : ∀ i j, (n : AE D) * (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D)
    (h' : ∀ i j, (n' : AE D) * ((g' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) i j ∈ OhE D) :
    ∀ ζ ∈ (latA D cc N N').map (actA D N N' (g, g')), (n * n') • ζ ∈ latA D cc N N' := by
  rintro _ ⟨ζ, hζ, rfl⟩ i j
  rw [actA_apply, Matrix.smul_apply, Matrix.mul_apply, Finset.smul_sum]
  refine sum_mem fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.smul_sum]
  refine sum_mem fun k _ => ?_
  convert ihE_mul D cc (mul_mem (h l j) (h' i k)) (hζ k l) using 1
  rw [nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.FinWeil.MovedIdx


open GlobalTheory.FinWeil.MovedIdx in
theorem GlobalTheory.FinWeil.idx_map_actA : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N'), idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) ≠ 0 ∧ (∀ q : ℕ, q.Prime → TrivAt D q (g : GL (Fin N) (AE D)) → TrivAt D q (g' : GL (Fin N') (AE D)) → ¬ q ∣ idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g')))) ∧ (IntG D (g : GL (Fin N) (AE D)) → IntG D (g' : GL (Fin N') (AE D)) → (latA D cc N N').map (actA D N N' (g, g')) ≤ latA D cc N N') := by
  intro D hD cc δ hC N N' g g'
  have h0 : idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) ≠ 0 := by
    obtain ⟨n, hn, h⟩ := denom_mat D (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
    obtain ⟨n', hn', h'⟩ := denom_mat D ((g' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D))
    exact GlobalTheory.T.heisenbergRelativeIndex_completedStandard_ne_zero D hD cc δ hC N N' _ (Nat.mul_pos hn hn') _ (nsmul_mem_latA D cc g g' h h')
  refine ⟨h0, fun q hq hg hg' hd => ?_, fun hg hg' ζ hζ => ?_⟩
  · obtain ⟨n, hn, h⟩ := denom_triv_inv D hq hg
    obtain ⟨n', hn', h'⟩ := denom_triv D hg'
    exact (Nat.Prime.coprime_iff_not_dvd hq).1 (Nat.Coprime.mul_left hn hn').symm
      (dvd_of_dvd_idx _ _ _ q hq h0 (nsmul_mem_latA D cc g g' h h') hd)
  · have := nsmul_mem_latA D cc g g' (n := 1) (n' := 1) (fun i j => by simpa using (hg i j).2)
      (fun i j => by simpa using (hg' i j).1) ζ hζ
    simpa using this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergRelativeIndexTranslateCompletedLatticeStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergRelativeIndex_translate_completed_lattice : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N'), idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) ≠ 0 ∧ (∀ q : ℕ, q.Prime → TrivAt D q (g : GL (Fin N) (AE D)) → TrivAt D q (g' : GL (Fin N') (AE D)) → ¬ q ∣ idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g')))) ∧ (IntG D (g : GL (Fin N) (AE D)) → IntG D (g' : GL (Fin N') (AE D)) → (latA D cc N N').map (actA D N N' (g, g')) ≤ latA D cc N N') := by
  first | exact @GlobalTheory.FinWeil.idx_map_actA | exact GlobalTheory.FinWeil.idx_map_actA | (intros; apply GlobalTheory.FinWeil.idx_map_actA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsogenyFibresEvenThetaSigmaStarSquareQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsogenyFibresEvenThetaSigmaStarSquareQuotient
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenTheta.Fibres

def trFac (Λ : AddSubgroup ℂ) (z ω : ℂ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) -
    (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ)))

variable {Λ : AddSubgroup ℂ}

theorem thetaTranslationOperator_apply (ω : ℂ) (G : ℂ → ℂ) (z : ℂ) : U1 Λ ω G z = G (z + ω) * trFac Λ z ω := rfl

theorem trFac_mul {β : ℂ} {n : ℕ} (hb : β * starRingEnd ℂ β = (n : ℂ)) (z ω : ℂ) :
    trFac Λ (β * z) (β * ω) = trFac Λ z ω ^ n := by
  simp only [trFac]
  rw [← Complex.exp_nat_mul, ← hb, map_mul]
  congr 1
  ring

theorem trFac_add_sub (v z ω : ℂ) :
    trFac Λ (v + z) ω * trFac Λ (z - v) ω = trFac Λ z ω ^ 2 := by
  simp only [trFac]
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem sg_sq (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) (z : ℂ) :
    sgStar Λ (z + ω) ^ 2 * trFac Λ z ω ^ 2 = sgStar Λ z ^ 2 := by
  rw [← mul_pow, ← thetaTranslationOperator_apply, h.sg_law hω]
  split_ifs <;> ring

theorem sqTh_law (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) (v z : ℂ) :
    sqTh Λ v (z + ω) * trFac Λ z ω ^ 2 = sqTh Λ v z := by
  have h1 := h.sg_law hω (v + z)
  have h2 := h.sg_law hω (z - v)
  rw [thetaTranslationOperator_apply] at h1 h2
  have e1 : sgStar Λ (v - (z + ω)) = -sgStar Λ (z - v + ω) := by
    rw [← h.sg_neg]; congr 1; ring
  have e2 : sgStar Λ (v - z) = -sgStar Λ (z - v) := by
    rw [← h.sg_neg]; congr 1; ring
  have e3 : sgStar Λ (v + z + ω) * sgStar Λ (z - v + ω) * trFac Λ z ω ^ 2 =
      sgStar Λ (v + z) * sgStar Λ (z - v) := by
    rw [← trFac_add_sub v, mul_mul_mul_comm, h1, h2]
    split_ifs <;> ring
  simp only [sqTh]
  rw [e1, e2, ← add_assoc]
  linear_combination (-1 / sgStar Λ v ^ 2) * e3

theorem law_of_fac (h : IsLat Λ) {F : ℂ → ℂ} {k : ℕ} {ω : ℂ} (hω : ω ∈ Λ) (z : ℂ)
    (hF : F (z + ω) * trFac Λ z ω ^ (2 * k) = F z) :
    F (z + ω) * sgStar Λ z ^ (2 * k) = F z * sgStar Λ (z + ω) ^ (2 * k) := by
  rw [← hF, pow_mul (sgStar Λ z), ← sg_sq h hω z]
  ring

theorem isogeny_fibres : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (β t₀ : ℂ) (k : ℕ), (∀ ω ∈ Λ, β * ω ∈ Λ) → β + starRingEnd ℂ β = 1 → β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ) → 2 * t₀ ∈ Λ → β * t₀ ∉ Λ → (1 - β) * t₀ ∉ Λ → ∃ (Q : Fin k → ℂ) (Q' : Fin (2 * k) → ℂ), (∀ i, Q i ∉ Λ ∧ InRationalLattice Λ (Q i)) ∧ (∀ j, Q' j ∉ Λ ∧ InRationalLattice Λ (Q' j)) ∧ (∀ z, GL3Theta.th0 Λ t₀ (β * z) = ∏ i, sqTh Λ (Q i) z) ∧ (∀ z, sqTh Λ (β * t₀) (β * z) = ∏ j, sqTh Λ (Q' j) z) ∧ (∀ i j, wpF Λ (Q i) ≠ wpF Λ (Q' j)) ∧ (∃ j, wpF Λ (Q' j) = wpF Λ t₀) ∧ (∃ j, wpF Λ (Q' j) = wpF Λ (β * t₀)) ∧ wpF Λ t₀ ≠ wpF Λ (β * t₀) := by
  intro Λ h β t₀ k hβ htr hN h2 h1 h1'
  have hβ' : ∀ ω ∈ Λ, (1 - β) * ω ∈ Λ := fun ω hω => by
    rw [sub_mul, one_mul]; exact Λ.sub_mem hω (hβ ω hω)
  have hN' : β * (1 - β) = 2 * (k : ℂ) := by
    rw [← htr, add_sub_cancel_left, hN]; push_cast; ring
  have ht₀ : t₀ ∉ Λ := fun hh => h1 (hβ _ hh)
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exfalso
      simp only [Nat.cast_zero, mul_zero, mul_eq_zero] at hN'
      rcases hN' with h0 | h0
      · exact h1 (by rw [h0, zero_mul]; exact Λ.zero_mem)
      · exact h1' (by rw [h0, zero_mul]; exact Λ.zero_mem)
    · exact hk
  have hnat : ∀ (n : ℕ) (x : ℂ), x ∈ Λ → (n : ℂ) * x ∈ Λ := fun n x hx => by
    rw [← nsmul_eq_mul]; exact Λ.nsmul_mem hx n
  have h2t₁ : 2 * (β * t₀) ∈ Λ := by
    convert hβ _ h2 using 1; ring
  have hplus : t₀ + β * t₀ ∉ Λ := fun hh => h1' (by
    convert Λ.sub_mem hh h2t₁ using 1; ring)
  have hminus : t₀ - β * t₀ ∉ Λ := fun hh => h1' (by
    convert hh using 1; ring)
  have hla : ∀ x : ℂ, 2 * (β * x) ∈ Λ → InRationalLattice Λ x := fun x hx =>
    ⟨4 * k, by omega, by
      convert hβ' _ hx using 1
      push_cast
      linear_combination (-2 * x) * hN'⟩
  obtain ⟨hd, h0, hev, -, hz, hU⟩ := GlobalTheory.T.th0_zero_even_sq_zeros_and_periodicity Λ h t₀ ht₀ h2
  obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.T.evenTheta_eq_prod_sigmaStarSquareQuotient Λ h k (fun z => GL3Theta.th0 Λ t₀ (β * z))
    (hd.comp (by fun_prop)) (fun z => by rw [mul_neg, hev]) (by rw [mul_zero, h0])
    (fun ω hω z => law_of_fac h (F := fun z => GL3Theta.th0 Λ t₀ (β * z)) hω z (by
      have hn : β * ω / 2 + t₀ ∉ Λ := fun hh => h1' (by
        convert Λ.sub_mem (hβ' _ hh) (hnat k ω hω) using 1
        linear_combination (-ω / 2) * hN')
      have := hU _ (hβ ω hω) hn (β * z)
      rw [thetaTranslationOperator_apply, trFac_mul hN] at this
      simpa only [mul_add] using this))
  obtain ⟨Q', hQ', hQe'⟩ := GlobalTheory.T.evenTheta_eq_prod_sigmaStarSquareQuotient Λ h (2 * k) (fun z => sqTh Λ (β * t₀) (β * z))
    ((h.differentiable_sqTh _).comp (by fun_prop)) (fun z => by rw [mul_neg, sqTh_neg])
    (by rw [mul_zero, h.sqTh_zero h1])
    (fun ω hω z => law_of_fac h (F := fun z => sqTh Λ (β * t₀) (β * z)) hω z (by
      have := sqTh_law h (hβ ω hω) (β * t₀) (β * z)
      rw [trFac_mul hN, ← pow_mul, mul_comm (2 * k) 2] at this
      simpa only [mul_add] using this))
  have hA : ∀ i, β * Q i + t₀ ∈ Λ := fun i => by
    rw [← hz, hQe]
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      ((h.sqTh_eq_zero (hQ i) _).2 (Or.inr (by rw [sub_self]; exact Λ.zero_mem)))
  have hB : ∀ j, β * t₀ + β * Q' j ∈ Λ ∨ β * t₀ - β * Q' j ∈ Λ := fun j => by
    rw [← h.sqTh_eq_zero h1, hQe']
    exact Finset.prod_eq_zero (Finset.mem_univ j)
      ((h.sqTh_eq_zero (hQ' j) _).2 (Or.inr (by rw [sub_self]; exact Λ.zero_mem)))
  have hC : ∀ x : ℂ, x ∉ Λ → β * t₀ - β * x ∈ Λ → ∃ j, wpF Λ (Q' j) = wpF Λ x := fun x hx hx' => by
    have h3 := (h.sqTh_eq_zero h1 (β * x)).2 (Or.inr hx')
    rw [hQe', Finset.prod_eq_zero_iff] at h3
    obtain ⟨j, -, hj⟩ := h3
    exact ⟨j, ((h.wp_eq_iff (hQ' j) hx).2 ((h.sqTh_eq_zero (hQ' j) x).1 hj)).symm⟩
  refine ⟨Q, Q', fun i => ⟨hQ i, hla _ ?_⟩, fun j => ⟨hQ' j, hla _ ?_⟩, hQe, hQe', ?_,
    hC _ ht₀ (by rw [sub_self]; exact Λ.zero_mem), hC _ h1 ?_, ?_⟩
  · convert Λ.sub_mem (hnat 2 _ (hA i)) h2 using 1
    push_cast; ring
  · rcases hB j with hj | hj
    · convert Λ.sub_mem (hnat 2 _ hj) h2t₁ using 1
      push_cast; ring
    · convert Λ.sub_mem h2t₁ (hnat 2 _ hj) using 1
      push_cast; ring
  · intro i j hij
    have ha := hA i
    rcases (h.wp_eq_iff (hQ i) (hQ' j)).1 hij.symm with hc | hc <;> rcases hB j with hj | hj
    · exact hplus (by convert Λ.sub_mem (Λ.add_mem ha hj) (hβ _ hc) using 1; ring)
    · exact hminus (by convert Λ.sub_mem (Λ.sub_mem ha hj) (hβ _ hc) using 1; ring)
    · exact hminus (by convert Λ.sub_mem (Λ.sub_mem ha hj) (hβ _ hc) using 1; ring)
    · exact hplus (by convert Λ.sub_mem (Λ.add_mem ha hj) (hβ _ hc) using 1; ring)
  · convert hnat k _ h2 using 1
    linear_combination t₀ * hN'
  · intro he
    rcases (h.wp_eq_iff ht₀ h1).1 he.symm with hc | hc
    · exact hplus hc
    · exact hminus hc

end GlobalTheory.EvenTheta.Fibres
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsogenyFibresEvenThetaSigmaStarSquareQuotientStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_fibres_even_theta_sigmaStarSquareQuotient : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (β t₀ : ℂ) (k : ℕ), (∀ ω ∈ Λ, β * ω ∈ Λ) → β + starRingEnd ℂ β = 1 → β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ) → 2 * t₀ ∈ Λ → β * t₀ ∉ Λ → (1 - β) * t₀ ∉ Λ → ∃ (Q : Fin k → ℂ) (Q' : Fin (2 * k) → ℂ), (∀ i, Q i ∉ Λ ∧ InRationalLattice Λ (Q i)) ∧ (∀ j, Q' j ∉ Λ ∧ InRationalLattice Λ (Q' j)) ∧ (∀ z, GL3Theta.th0 Λ t₀ (β * z) = ∏ i, sqTh Λ (Q i) z) ∧ (∀ z, sqTh Λ (β * t₀) (β * z) = ∏ j, sqTh Λ (Q' j) z) ∧ (∀ i j, wpF Λ (Q i) ≠ wpF Λ (Q' j)) ∧ (∃ j, wpF Λ (Q' j) = wpF Λ t₀) ∧ (∃ j, wpF Λ (Q' j) = wpF Λ (β * t₀)) ∧ wpF Λ t₀ ≠ wpF Λ (β * t₀) := by
  first | exact @GlobalTheory.EvenTheta.Fibres.isogeny_fibres | exact GlobalTheory.EvenTheta.Fibres.isogeny_fibres | (intros; apply GlobalTheory.EvenTheta.Fibres.isogeny_fibres <;> assumption)
end
end

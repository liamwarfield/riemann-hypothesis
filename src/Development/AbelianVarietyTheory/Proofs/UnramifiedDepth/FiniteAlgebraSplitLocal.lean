module

public import ReciprocityTheory.DualLattices.SubMemOfCompat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FiniteAlgebraSplitLocal
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem finSplit_max_eq {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A]
    [Algebra O A] (φ : A →ₐ[O] O) (N : Ideal A) (hN : N.IsMaximal)
    (h : RingHom.ker φ ≤ N) : N = (maximalIdeal O).comap φ := by
  refine hN.eq_of_le ?_ ?_
  · intro htop
    have h1 : (1 : A) ∈ (maximalIdeal O).comap φ := htop ▸ Submodule.mem_top
    rw [Ideal.mem_comap, map_one] at h1
    exact mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 h1) isUnit_one
  · intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hN.ne_top
    rw [Ideal.eq_top_iff_one]
    have hy : algebraMap O A (↑hu.unit⁻¹) * x ∈ N := N.mul_mem_left _ hx
    have hφy : φ (algebraMap O A (↑hu.unit⁻¹) * x) = 1 := by
      rw [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
      exact hu.val_inv_mul
    have hk : 1 - algebraMap O A (↑hu.unit⁻¹) * x ∈ N :=
      h (by rw [RingHom.mem_ker, map_sub, map_one, hφy, sub_self])
    simpa using N.add_mem hk hy

private theorem finSplit_exists {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A]
    [Algebra O A] [Finite (A →ₐ[O] O)] (M : Ideal A) :
    ∃ e : A, ∀ φ : A →ₐ[O] O, ((maximalIdeal O).comap φ = M → φ e = 1) ∧
      ((maximalIdeal O).comap φ ≠ M → φ e = 0) := by
  classical
  have := Fintype.ofFinite (A →ₐ[O] O)
  have key : ∀ φ ψ : A →ₐ[O] O, ∃ x : A, (maximalIdeal O).comap φ = M →
      (maximalIdeal O).comap ψ ≠ M → φ x = 1 ∧ ψ x = 0 := by
    intro φ ψ
    by_cases hφ : (maximalIdeal O).comap φ = M
    swap
    · exact ⟨0, fun h => absurd h hφ⟩
    by_cases hψ : (maximalIdeal O).comap ψ = M
    · exact ⟨0, fun _ h => absurd hψ h⟩
    have htop : RingHom.ker φ ⊔ RingHom.ker ψ = ⊤ := by
      by_contra hne
      obtain ⟨N, hN, hle⟩ := Ideal.exists_le_maximal _ hne
      have e1 := finSplit_max_eq φ N hN (le_sup_left.trans hle)
      have e2 := finSplit_max_eq ψ N hN (le_sup_right.trans hle)
      exact hψ (e2.symm.trans (e1.trans hφ))
    have h1 : (1 : A) ∈ RingHom.ker φ ⊔ RingHom.ker ψ := htop ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    refine ⟨b, fun _ _ => ⟨?_, RingHom.mem_ker.1 hb⟩⟩
    have hφab := congrArg φ hab
    rw [map_add (f := _), RingHom.mem_ker.1 ha, zero_add, map_one] at hφab
    exact hφab
  choose x hx using key
  refine ⟨1 - ∏ φ ∈ Finset.univ.filter (fun φ : A →ₐ[O] O => (maximalIdeal O).comap φ = M),
      (1 - ∏ ψ ∈ Finset.univ.filter (fun ψ : A →ₐ[O] O => (maximalIdeal O).comap ψ ≠ M), x φ ψ),
      fun φ0 => ⟨fun h0 => ?_, fun h0 => ?_⟩⟩
  · rw [map_sub, map_one, map_prod, sub_eq_self]
    apply Finset.prod_eq_zero (i := φ0) (by simp [h0])
    rw [map_sub, map_one, map_prod, sub_eq_zero, eq_comm]
    apply Finset.prod_eq_one
    intro ψ hψ
    exact (hx φ0 ψ h0 (Finset.mem_filter.1 hψ).2).1
  · rw [map_sub, map_one, map_prod, sub_eq_zero, eq_comm]
    apply Finset.prod_eq_one
    intro φ hφ
    rw [map_sub, map_one, map_prod, sub_eq_self]
    apply Finset.prod_eq_zero (i := φ0) (by simp [h0])
    exact (hx φ φ0 (Finset.mem_filter.1 hφ).2 h0).2

theorem finite_algebra_split_local :
  (∀ (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Finite (A →ₐ[O] O)],
    (∀ f : A, (∀ φ : A →ₐ[O] O, φ f = 0) → f = 0) →
    ∃ (n : ℕ) (ε : Fin n → A), CompleteOrthogonalIdempotents ε ∧ ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - ε i})) := by
  intro O A _ _ _ _ _ _ hsep
  classical
  have := Fintype.ofFinite (A →ₐ[O] O)
  have hone : (1 : O) ∉ maximalIdeal O := fun h =>
    mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 h) isUnit_one
  let Pts := Set.range (fun φ : A →ₐ[O] O => (maximalIdeal O).comap φ)
  let eqv : Fin (Fintype.card Pts) ≃ Pts := (Fintype.equivFin Pts).symm
  choose e he using fun M : Ideal A => finSplit_exists (O := O) M
  have hval : ∀ (M : Ideal A) (φ : A →ₐ[O] O),
      φ (e M) = if (maximalIdeal O).comap φ = M then 1 else 0 := by
    intro M φ
    split_ifs with h
    · exact (he M φ).1 h
    · exact (he M φ).2 h
  have ext : ∀ a b : A, (∀ φ : A →ₐ[O] O, φ a = φ b) → a = b := fun a b h =>
    sub_eq_zero.1 (hsep _ fun φ => by rw [map_sub, h φ, sub_self])
  have hmax : ∀ N : Ideal A, N.IsMaximal → ∃ φ : A →ₐ[O] O, (maximalIdeal O).comap φ = N := by
    intro N hN
    by_contra hcon
    simp only [not_exists] at hcon
    have hnot : ∀ φ : A →ₐ[O] O, ¬ RingHom.ker φ ≤ N := fun φ hle =>
      hcon φ (finSplit_max_eq φ N hN hle).symm
    simp only [SetLike.not_le_iff_exists] at hnot
    choose a ha haN using hnot
    have := hN.isPrime
    have h0 : ∏ φ, a φ = 0 := hsep _ fun ψ => by
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ ψ) (RingHom.mem_ker.1 (ha ψ))
    have hin : ∏ φ, a φ ∈ N := h0 ▸ N.zero_mem
    obtain ⟨φ, -, hφ⟩ := Ideal.IsPrime.prod_mem_iff.1 hin
    exact haN φ hφ
  refine ⟨Fintype.card Pts, fun i => e (eqv i).1, ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, fun i => ?_⟩
  · show e (eqv i).1 * e (eqv i).1 = e (eqv i).1
    apply ext
    intro φ
    rw [map_mul, hval]
    split_ifs <;> simp
  · show e (eqv i).1 * e (eqv j).1 = 0
    have hne : (eqv i).1 ≠ (eqv j).1 := fun h => hij (eqv.injective (Subtype.ext h))
    apply ext
    intro φ
    rw [map_mul, hval, hval, map_zero]
    split_ifs with h1 h2 h2
    · exact absurd (h1.symm.trans h2) hne
    all_goals simp
  · apply ext
    intro φ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one]
    simp only [hval]
    rw [Fintype.sum_equiv eqv _
      (fun M : Pts => if (maximalIdeal O).comap φ = M.1 then (1 : O) else 0) (fun _ => rfl)]
    rw [Finset.sum_eq_single ⟨(maximalIdeal O).comap φ, φ, rfl⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Subtype.ext h.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · obtain ⟨φ0, hφ0⟩ := (eqv i).2
    replace hφ0 : (maximalIdeal O).comap φ0 = (eqv i).1 := hφ0
    have hmem : ∀ ψ : A →ₐ[O] O,
        1 - e (eqv i).1 ∈ (maximalIdeal O).comap ψ ↔ (maximalIdeal O).comap ψ = (eqv i).1 := by
      intro ψ
      rw [Ideal.mem_comap, map_sub, map_one, hval]
      split_ifs with h
      · simp [h]
      · simp only [sub_zero, h, iff_false]
        exact hone
    have hJM : Ideal.span {1 - e (eqv i).1} ≤ (eqv i).1 := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      have h := (hmem φ0).2 hφ0
      rw [hφ0] at h
      exact h
    have hMtop : (eqv i).1 ≠ ⊤ := by
      rw [← hφ0]
      intro h
      have h1 : (1 : A) ∈ (maximalIdeal O).comap φ0 := h ▸ Submodule.mem_top
      rw [Ideal.mem_comap, map_one] at h1
      exact hone h1
    have hJ : Ideal.span {1 - e (eqv i).1} ≠ ⊤ := fun h => hMtop (top_le_iff.1 (h ▸ hJM))
    have := Ideal.Quotient.nontrivial_iff.2 hJ
    obtain ⟨Q0, hQ0⟩ := Ideal.exists_maximal (A ⧸ Ideal.span {1 - e (eqv i).1})
    have hcomap : ∀ Q : Ideal (A ⧸ Ideal.span {1 - e (eqv i).1}), Q.IsMaximal →
        Q = (eqv i).1.map (Ideal.Quotient.mk _) := by
      intro Q hQ
      have := hQ
      have hQ' : (Q.comap (Ideal.Quotient.mk (Ideal.span {1 - e (eqv i).1}))).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      obtain ⟨ψ, hψ⟩ := hmax _ hQ'
      have hin : 1 - e (eqv i).1 ∈ Q.comap (Ideal.Quotient.mk (Ideal.span {1 - e (eqv i).1})) := by
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_singleton _))]
        exact Q.zero_mem
      rw [← hψ] at hin
      have hψM := (hmem ψ).1 hin
      rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q, ← hψ, hψM]
    exact IsLocalRing.of_unique_max_ideal
      ⟨Q0, hQ0, fun Q hQ => (hcomap Q hQ).trans (hcomap Q0 hQ0).symm⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TateBasisMatrix
namespace GlobalTheory

private theorem tateMat_val_smul {Γ : Type} [AddCommGroup Γ] {N : ℕ} [NeZero N] {x : Γ}
    (hx : N • x = 0) (a : ℤ) : ((a : ZMod N).val) • x = a • x := by
  have h : (N : ℤ) ∣ a - ((a : ZMod N).val : ℤ) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]; simp
  obtain ⟨c, hc⟩ := h
  have h2 : a = ((a : ZMod N).val : ℤ) + c * N := by linarith
  conv_rhs => rw [h2, add_smul, mul_smul, natCast_zsmul, natCast_zsmul, hx, smul_zero, add_zero]

section
variable {p : ℕ} [hp : Fact p.Prime] {κ Γ : Type} [Fintype κ] [AddCommGroup Γ] {τ : κ → ℕ → Γ}

private theorem tateMat_zero (h2 : ∀ i n, τ i n = p • τ i (n + 1)) (j : κ) (n : ℕ) :
    τ j 0 = (p ^ n) • τ j n := by
  induction n with
  | zero => simp
  | succ n ih => rw [ih, h2 j n, pow_succ, mul_smul]

private theorem tateMat_step (h2 : ∀ i n, τ i n = p • τ i (n + 1)) (a : κ → ℤ) (n : ℕ) :
    ∑ j, a j • τ j n = p • ∑ j, a j • τ j (n + 1) := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h2 j n, smul_comm]

private theorem tateMat_exists (h2 : ∀ i n, τ i n = p • τ i (n + 1))
    (h3 : ∀ x : Γ, p • x = 0 → ∃! t : κ → ZMod p, x = ∑ j, (t j).val • τ j 0) (n : ℕ) :
    ∀ x : Γ, (p ^ (n + 1)) • x = 0 → ∃ a : κ → ℤ, x = ∑ j, a j • τ j n := by
  induction n with
  | zero =>
    intro x hx
    obtain ⟨t, ht, -⟩ := h3 x (by simpa using hx)
    exact ⟨fun j => ((t j).val : ℤ), by simpa only [natCast_zsmul] using ht⟩
  | succ n ih =>
    intro x hx
    obtain ⟨a, ha⟩ := ih (p • x) (by rw [← mul_smul, ← pow_succ, hx])
    obtain ⟨t, ht, -⟩ := h3 (x - ∑ j, a j • τ j (n + 1)) (by
      rw [smul_sub, ← tateMat_step h2, ha, sub_self])
    refine ⟨fun j => a j + (((t j).val * p ^ (n + 1) : ℕ) : ℤ), ?_⟩
    simp only [add_smul, Finset.sum_add_distrib, natCast_zsmul, mul_smul, ← tateMat_zero h2]
    rw [← ht]; abel

private theorem tateMat_dvd (h1 : ∀ i n, (p ^ (n + 1)) • τ i n = 0)
    (h2 : ∀ i n, τ i n = p • τ i (n + 1))
    (h3 : ∀ x : Γ, p • x = 0 → ∃! t : κ → ZMod p, x = ∑ j, (t j).val • τ j 0) (n : ℕ) :
    ∀ a : κ → ℤ, ∑ j, a j • τ j n = 0 → ∀ j, ((p ^ (n + 1) : ℕ) : ℤ) ∣ a j := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have base : ∀ a : κ → ℤ, ∑ j, a j • τ j 0 = 0 → ∀ j, (p : ℤ) ∣ a j := by
    intro a ha j
    have hu := (h3 0 (smul_zero _)).unique (y₁ := fun j => (a j : ZMod p)) (y₂ := fun _ => 0)
      (by
        rw [← ha]
        refine Finset.sum_congr rfl fun k _ => ?_
        exact (tateMat_val_smul (by simpa using h1 k 0) _).symm)
      (by simp)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (congrFun hu j)
  induction n with
  | zero => intro a ha j; simpa using base a ha j
  | succ n ih =>
    intro a ha j
    have hd := ih a (by rw [tateMat_step h2, ha, smul_zero])
    choose b hb using hd
    have := base b (by
      rw [← ha]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb k, tateMat_zero h2 k (n + 1), mul_comm, mul_smul, natCast_zsmul]) j
    rw [hb j, pow_succ p (n + 1)]
    push_cast
    exact mul_dvd_mul_left _ this

private theorem tateMat_congr (h1 : ∀ i n, (p ^ (n + 1)) • τ i n = 0)
    (h2 : ∀ i n, τ i n = p • τ i (n + 1))
    (h3 : ∀ x : Γ, p • x = 0 → ∃! t : κ → ZMod p, x = ∑ j, (t j).val • τ j 0) (n : ℕ)
    (a b : κ → ℤ) (h : ∑ j, a j • τ j n = ∑ j, b j • τ j n) (j : κ) :
    ((p ^ (n + 1) : ℕ) : ℤ) ∣ b j - a j := by
  refine tateMat_dvd h1 h2 h3 n (fun j => b j - a j) ?_ j
  simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]

private theorem tateMat_limit (h1 : ∀ i n, (p ^ (n + 1)) • τ i n = 0)
    (h2 : ∀ i n, τ i n = p • τ i (n + 1))
    (h3 : ∀ x : Γ, p • x = 0 → ∃! t : κ → ZMod p, x = ∑ j, (t j).val • τ j 0)
    (f : AddMonoid.End Γ) (j : κ) :
    ∃ c : κ → ℤ_[p], ∀ n, f (τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (c k)).val • τ k n := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hex : ∀ n, ∃ a : κ → ℤ, f (τ j n) = ∑ k, a k • τ k n := fun n =>
    tateMat_exists h2 h3 n _ (by rw [← map_nsmul, h1, map_zero])
  choose a ha using hex
  have hc : ∀ k i, (p : ℤ) ^ i ∣ (fun i => a (i - 1) k) (i + 1) - (fun i => a (i - 1) k) i := by
    intro k i
    cases i with
    | zero => simp
    | succ m =>
      have := tateMat_congr h1 h2 h3 m (a m) (a (m + 1)) (by
        rw [← ha, tateMat_step h2, ← ha, ← map_nsmul, ← h2]) k
      simpa using this
  refine ⟨fun k => PadicInt.ofIntSeq _
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun i => a (i - 1) k) p (hc k)), fun n => ?_⟩
  rw [ha n]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun i => a (i - 1) k) p (hc k) (n + 1)]
  exact (tateMat_val_smul (h1 k n) _).symm

private theorem tateMat_unique (h1 : ∀ i n, (p ^ (n + 1)) • τ i n = 0)
    (h2 : ∀ i n, τ i n = p • τ i (n + 1))
    (h3 : ∀ x : Γ, p • x = 0 → ∃! t : κ → ZMod p, x = ∑ j, (t j).val • τ j 0)
    (c d : κ → ℤ_[p]) (b : ℕ → κ → ℤ)
    (hb : ∀ n k, (b n k : ZMod (p ^ (n + 1))) = PadicInt.toZModPow (n + 1) (d k))
    (h : ∀ n, ∑ k, (PadicInt.toZModPow (n + 1) (c k)).val • τ k n = ∑ k, b n k • τ k n)
    (k : κ) : c k = d k := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  cases n with
  | zero =>
    haveI : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ n =>
    have := tateMat_congr h1 h2 h3 n
      (fun k => ((PadicInt.toZModPow (n + 1) (c k)).val : ℤ)) (b n)
      (by simpa only [natCast_zsmul] using h n) k
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, hb] at this
    simpa using this

end

theorem tate_basis_matrix :
    (∀ (p : ℕ) [Fact p.Prime] (κ Γ : Type) [Fintype κ] [DecidableEq κ] [AddCommGroup Γ] (τ : κ → ℕ → Γ),
    (∀ i n, (p ^ (n + 1)) • τ i n = 0) → (∀ i n, τ i n = p • τ i (n + 1)) →
    (∀ x : Γ, p • x = 0 → ∃! t : κ → ZMod p, x = ∑ j, (t j).val • τ j 0) →
    (∀ n (x : Γ), (p ^ (n + 1)) • x = 0 → ∃! t : κ → ZMod (p ^ (n + 1)), x = ∑ j, (t j).val • τ j n) ∧
    ∃ ρ : AddMonoid.End Γ →+* Matrix κ κ ℤ_[p], ∀ (f : AddMonoid.End Γ) j n,
      f (τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (ρ f k j)).val • τ k n) := by
  intro p hp κ Γ _ _ _ τ h1 h2 h3
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  refine ⟨fun n x hx => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := tateMat_exists h2 h3 n x hx
    have key : ∀ t : κ → ZMod (p ^ (n + 1)), x = ∑ j, (t j).val • τ j n →
        t = fun j => (a j : ZMod (p ^ (n + 1))) := by
      intro t ht
      funext j
      have := tateMat_congr h1 h2 h3 n (fun j => ((t j).val : ℤ)) a
        (by simpa only [natCast_zsmul, ← ha] using ht.symm) j
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub] at this
      simpa using this
    refine ⟨fun j => (a j : ZMod (p ^ (n + 1))), ?_, key⟩
    rw [ha]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (tateMat_val_smul (h1 k n) _).symm
  · choose c hc using tateMat_limit h1 h2 h3
    let r : AddMonoid.End Γ → Matrix κ κ ℤ_[p] := fun f => Matrix.of fun k j => c f j k
    have hr : ∀ f k j, r f k j = c f j k := fun _ _ _ => rfl
    refine ⟨⟨⟨⟨r, ?_⟩, ?_⟩, ?_, ?_⟩, fun f j n => hc f j n⟩
    · apply Matrix.ext
      intro k j
      refine tateMat_unique h1 h2 h3 (c 1 j) (fun k => (1 : Matrix κ κ ℤ_[p]) k j)
        (fun _ k => if k = j then 1 else 0) (fun n k => ?_) (fun n => ?_) k
      · by_cases h : k = j <;> simp [Matrix.one_apply, h]
      · rw [← hc]; simp
    · intro f g
      apply Matrix.ext
      intro k j
      refine tateMat_unique h1 h2 h3 (c (f * g) j) (fun k => (r f * r g) k j)
        (fun n k => ∑ l, ((PadicInt.toZModPow (n + 1) (c f l k)).val : ℤ) *
          ((PadicInt.toZModPow (n + 1) (c g j l)).val : ℤ)) (fun n k => ?_) (fun n => ?_) k
      · simp [Matrix.mul_apply, hr]
      set_option synthInstance.maxHeartbeats 100000 in
        · rw [← hc, AddMonoid.End.coe_mul, Function.comp_apply, hc g j n, map_sum]
          simp only [Finset.sum_smul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [map_nsmul, hc f l n, Finset.smul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_comm, mul_smul, natCast_zsmul, natCast_zsmul]
    · apply Matrix.ext
      intro k j
      refine tateMat_unique h1 h2 h3 (c 0 j) (fun _ => 0)
        (fun _ _ => 0) (fun n k => ?_) (fun n => ?_) k
      · simp
      · rw [← hc]; simp
    · intro f g
      apply Matrix.ext
      intro k j
      refine tateMat_unique h1 h2 h3 (c (f + g) j) (fun k => c f j k + c g j k)
        (fun n k => ((PadicInt.toZModPow (n + 1) (c f j k)).val : ℤ) +
          ((PadicInt.toZModPow (n + 1) (c g j k)).val : ℤ)) (fun n k => ?_) (fun n => ?_) k
      · simp
      · rw [← hc]
        simp only [add_smul, Finset.sum_add_distrib, natCast_zsmul, ← hc]
        rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FinEtaleFormallyUnramified
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj in
open scoped CategoryTheory.Obj CategoryTheory.MonObj in
attribute [local instance] Over.cartesianMonoidalCategory in
private theorem exists_algHom_apply_ne_zero_of_pointDerivation_eq_zero {C B : Type} [Field C] [IsAlgClosed C]
    [CommRing B] [Algebra C B] [FiniteDimensional C B]
    (hder : ∀ (φ : B →ₐ[C] C) (D : B →ₗ[C] C),
      (∀ a b, D (a * b) = φ a * D b + φ b * D a) → D = 0)
    {y : B} (hy : y ≠ 0) : ∃ φ : B →ₐ[C] C, φ y ≠ 0 := by
  classical
  set I : Ideal B := LinearMap.ker (LinearMap.mulRight B y) with hI
  have hItop : I ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ I := h ▸ Submodule.mem_top
    apply hy
    simpa [hI] using h1
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hItop
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.IsIntegral C (B ⧸ m) := Algebra.IsIntegral.of_finite C (B ⧸ m)
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := C) (K := B ⧸ m)
  let e := AlgEquiv.ofBijective (Algebra.ofId C (B ⧸ m)) hbij
  let φ : B →ₐ[C] C := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ C m)
  have hφ : ∀ b, φ b = 0 ↔ b ∈ m := by
    intro b
    simp [φ, Ideal.Quotient.eq_zero_iff_mem]
  have hφa : ∀ b, b - algebraMap C B (φ b) ∈ m := by
    intro b
    rw [← hφ, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  refine ⟨φ, fun hy0 => ?_⟩
  have hym : y ∈ m := (hφ y).1 hy0
  have hmm : m ≤ m * m := by
    intro x hx
    by_contra hx2
    obtain ⟨ℓ, hℓx, hℓ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
      (p := (m * m).restrictScalars C) hx2 inferInstance
    have hℓ0 : ∀ z ∈ m * m, ℓ z = 0 := by
      intro z hz
      have hmem := Submodule.mem_map_of_mem (f := ℓ)
        (show z ∈ (m * m).restrictScalars C from hz)
      rw [hℓ] at hmem
      exact (Submodule.mem_bot C).1 hmem
    let D : B →ₗ[C] C := ℓ.comp (LinearMap.id - (Algebra.linearMap C B).comp φ.toLinearMap)
    have hDapp : ∀ b, D b = ℓ (b - algebraMap C B (φ b)) := fun b => rfl
    have hD : ∀ a b, D (a * b) = φ a * D b + φ b * D a := by
      intro a b
      have key : a * b - algebraMap C B (φ (a * b)) =
          φ a • (b - algebraMap C B (φ b)) + φ b • (a - algebraMap C B (φ a)) +
            (a - algebraMap C B (φ a)) * (b - algebraMap C B (φ b)) := by
        rw [map_mul, map_mul, Algebra.smul_def, Algebra.smul_def]
        ring
      rw [hDapp, hDapp, hDapp, key, map_add (f := _), map_add (f := _), map_smul, map_smul,
        hℓ0 _ (Ideal.mul_mem_mul (hφa a) (hφa b)), smul_eq_mul, smul_eq_mul, add_zero]
    have hD0 := hder φ D hD
    apply hℓx
    have h2 : D x = ℓ x := by
      rw [hDapp, (hφ x).2 hx, map_zero, sub_zero]
    rw [← h2, hD0, LinearMap.zero_apply]
  haveI : IsNoetherianRing B := isNoetherian_of_tower C inferInstance
  have hidem : IsIdempotentElem m := le_antisymm Ideal.mul_le_left hmm
  obtain ⟨e', _he', hme⟩ := (Ideal.isIdempotentElem_iff_of_fg m (IsNoetherian.noetherian m)).1 hidem
  have he'm : e' ∈ m := hme ▸ Submodule.mem_span_singleton_self e'
  have hyspan : y ∈ B ∙ e' := hme ▸ hym
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.1 hyspan
  have hey : e' * y = y := by
    rw [← hz, smul_eq_mul, ← _root_.mul_assoc, mul_comm e' z, _root_.mul_assoc, _he'.eq]
  have h1e : 1 - e' ∈ m := hIm (by
    rw [hI, LinearMap.mem_ker, LinearMap.mulRight_apply, sub_mul, _root_.one_mul, hey, sub_self])
  exact hm.ne_top ((Ideal.eq_top_iff_one m).2 (by simpa using m.add_mem h1e he'm))

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj in
open scoped CategoryTheory.Obj CategoryTheory.MonObj in
attribute [local instance] Over.cartesianMonoidalCategory in
private theorem finrank_eq_card_algHom_of_pointDerivation_eq_zero {C B : Type} [Field C] [IsAlgClosed C]
    [CommRing B] [Algebra C B] [FiniteDimensional C B]
    (hder : ∀ (φ : B →ₐ[C] C) (D : B →ₗ[C] C),
      (∀ a b, D (a * b) = φ a * D b + φ b * D a) → D = 0) :
    Finite (B →ₐ[C] C) ∧ Module.finrank C B = Nat.card (B →ₐ[C] C) := by
  classical
  haveI hfin : Finite (B →ₐ[C] C) :=
    (linearIndependent_algHom_toLinearMap C B C).finite_of_isNoetherian
  refine ⟨hfin, le_antisymm ?_ (card_algHom_le_finrank C B C)⟩
  letI := Fintype.ofFinite (B →ₐ[C] C)
  let ev : B →ₗ[C] ((B →ₐ[C] C) → C) := LinearMap.pi fun φ => φ.toLinearMap
  have hev : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    by_contra hb0
    obtain ⟨φ, hφ⟩ := exists_algHom_apply_ne_zero_of_pointDerivation_eq_zero hder hb0
    exact hφ (congrFun hb φ)
  calc Module.finrank C B ≤ Module.finrank C ((B →ₐ[C] C) → C) :=
        LinearMap.finrank_le_finrank_of_injective hev
    _ = Nat.card (B →ₐ[C] C) := by
        rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]


open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj in
open scoped CategoryTheory.Obj CategoryTheory.MonObj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.finEtale_main :
    (∀ (C O A : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) [CommRing O]
      [Algebra O C], v.Integers O →
      ∀ [CommRing A] [Algebra O A] [Module.Free O A] [Module.Finite O A],
      (∀ φ φ' : A →ₐ[O] DualNumber C, (∀ a, (φ a).fst = (φ' a).fst) → φ = φ') →
      Finite (A →ₐ[O] O) ∧ (∀ f : A, (∀ φ : A →ₐ[O] O, φ f = 0) → f = 0) ∧
        Module.finrank O A = Nat.card (A →ₐ[O] O)) := by
  intro C O A _ _ v _ _ hv _ _ _ _ hpts
  classical
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have hder : ∀ (φ : C ⊗[O] A →ₐ[C] C) (D : C ⊗[O] A →ₗ[C] C),
      (∀ a b, D (a * b) = φ a * D b + φ b * D a) → D = 0 := by
    intro φ D hD
    have hD1 : D 1 = 0 := by
      have h11 := hD 1 1
      rw [_root_.mul_one, map_one φ, _root_.one_mul] at h11
      linear_combination -h11
    let L : C ⊗[O] A →ₗ[C] DualNumber C :=
      (Algebra.linearMap C (DualNumber C)).comp φ.toLinearMap + (TrivSqZeroExt.inrHom C C).comp D
    have hLfst : ∀ b, (L b).fst = φ b := by
      intro b; simp [L, TrivSqZeroExt.algebraMap_eq_inl]
    have hLsnd : ∀ b, (L b).snd = D b := by
      intro b; simp [L, TrivSqZeroExt.algebraMap_eq_inl]
    let F : C ⊗[O] A →ₐ[C] DualNumber C := AlgHom.ofLinearMap L
      (TrivSqZeroExt.ext (by rw [hLfst, map_one]; rfl) (by rw [hLsnd, hD1]; rfl))
      (fun a b => TrivSqZeroExt.ext (by rw [TrivSqZeroExt.fst_mul, hLfst, hLfst, hLfst, map_mul])
        (by
          rw [TrivSqZeroExt.snd_mul, hLsnd, hLsnd, hLsnd, hLfst, hLfst, hD, smul_eq_mul,
            MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
          ring))
    let χ₁ : A →ₐ[O] DualNumber C := (F.restrictScalars O).comp Algebra.TensorProduct.includeRight
    let χ₀ : A →ₐ[O] DualNumber C :=
      (((Algebra.ofId C (DualNumber C)).comp φ).restrictScalars O).comp
        Algebra.TensorProduct.includeRight
    have hχ : χ₁ = χ₀ := hpts χ₁ χ₀ (fun a => by
      show (L _).fst = _
      rw [hLfst]
      rfl)
    have hDA : ∀ a : A, D ((1 : C) ⊗ₜ[O] a) = 0 := by
      intro a
      have h1 := congrArg TrivSqZeroExt.snd (DFunLike.congr_fun hχ a)
      change (L ((1 : C) ⊗ₜ[O] a)).snd =
        (algebraMap C (DualNumber C) (φ ((1 : C) ⊗ₜ[O] a))).snd at h1
      rw [hLsnd, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl] at h1
      exact h1
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c a =>
      have hca : c ⊗ₜ[O] a = c • ((1 : C) ⊗ₜ[O] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [hca, map_smul, hDA, smul_zero, LinearMap.zero_apply]
    | add x y hx hy => simp only [map_add (f := _), hx, hy, LinearMap.zero_apply, add_zero]
  obtain ⟨_, hrankB⟩ := finrank_eq_card_algHom_of_pointDerivation_eq_zero hder
  let Ψ : (A →ₐ[O] O) → (C ⊗[O] A →ₐ[C] C) := fun ψ =>
    Algebra.TensorProduct.lift (Algebra.ofId C C) ((Algebra.ofId O C).comp ψ)
      (fun _ _ => Commute.all _ _)
  have hΨapp : ∀ ψ a, Ψ ψ ((1 : C) ⊗ₜ[O] a) = algebraMap O C (ψ a) := by
    intro ψ a; simp [Ψ]
  have hΨ : Function.Bijective Ψ := by
    refine ⟨fun ψ₁ ψ₂ h => AlgHom.ext fun a => hinj (by rw [← hΨapp, ← hΨapp, h]), fun φ => ?_⟩
    let φA : A →ₐ[O] C := (φ.restrictScalars O).comp Algebra.TensorProduct.includeRight
    have hmem : ∀ a, φA a ∈ (Algebra.ofId O C).range := by
      intro a
      have hint : IsIntegral O (φA a) := (Algebra.IsIntegral.isIntegral a).map φA
      obtain ⟨x, hx⟩ := hv.exists_of_le_one (hv.mem_of_integral hint)
      exact ⟨x, hx⟩
    let eO := AlgEquiv.ofInjective (Algebra.ofId O C) hinj
    refine ⟨eO.symm.toAlgHom.comp (φA.codRestrict _ hmem), ?_⟩
    apply Algebra.TensorProduct.ext (AlgHom.ext fun c => (AlgHom.commutes _ c).trans (AlgHom.commutes _ c).symm)
    refine AlgHom.ext fun a => ?_
    show Ψ _ ((1 : C) ⊗ₜ[O] a) = φ ((1 : C) ⊗ₜ[O] a)
    rw [hΨapp]
    show algebraMap O C (eO.symm ⟨φA a, hmem a⟩) = φA a
    have h1 := congrArg Subtype.val (eO.apply_symm_apply ⟨φA a, hmem a⟩)
    exact h1
  haveI hfinA : Finite (A →ₐ[O] O) := Finite.of_injective Ψ hΨ.1
  refine ⟨hfinA, fun f hf => ?_, ?_⟩
  · have h1 : (1 : C) ⊗ₜ[O] f = 0 := by
      by_contra hne
      obtain ⟨φ, hφ⟩ := exists_algHom_apply_ne_zero_of_pointDerivation_eq_zero hder hne
      obtain ⟨ψ, rfl⟩ := hΨ.2 φ
      apply hφ
      rw [hΨapp, hf ψ, map_zero]
    have hflat : Function.Injective ((Algebra.linearMap O C).rTensor A) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hinj
    have h2 : ((Algebra.linearMap O C).rTensor A) ((1 : O) ⊗ₜ[O] f) = 0 := by
      rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
      exact h1
    have h3 : (1 : O) ⊗ₜ[O] f = 0 := hflat (by rw [h2, map_zero])
    simpa using congrArg (TensorProduct.lid O A) h3
  · haveI : Nontrivial O := (algebraMap O C).domain_nontrivial
    rw [← Module.finrank_baseChange (R := C), hrankB, Nat.card_eq_of_bijective Ψ hΨ]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValNatCastSmul
noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory.EvAct

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

private lemma val_natCast_smul {M : Type} [AddCommGroup M] (x : M) (hx : p • x = 0) (n : ℕ) :
    ((n : ZMod p)).val • x = n • x := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div n p, add_smul, mul_comm, mul_smul, hx, smul_zero, add_zero]

private lemma val_sum_mul_smul {M ι : Type} [AddCommGroup M] [Fintype ι] (x : M) (hx : p • x = 0)
    (u v : ι → ZMod p) : (∑ j, u j * v j).val • x = ∑ j, (v j).val • (u j).val • x := by
  have h : (∑ j, u j * v j) = ((∑ j, (v j).val * (u j).val : ℕ) : ZMod p) := by
    push_cast
    simp [mul_comm]
  rw [h, val_natCast_smul x hx, Finset.sum_smul]
  simp only [mul_smul]

private lemma ptMap_spec (D : Dat p g B Tw Dt Oe σ cp) (t : Nb p g) :
    (D.ptMap t).comp (D.fin.sO _) = LHom.id Tw.O ∧ B.map (D.ptMap t) (D.fin.y _) = ptOf B D.L.τ t ∧
      ∀ j (φ' : LHom (D.fin.AAx j) Tw.O), φ'.comp (D.fin.sO j) = LHom.id Tw.O →
        B.map φ' (D.fin.y j) = ptOf B D.L.τ t → j = D.ptIdx t ∧ HEq φ' (D.ptMap t) :=
  Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ t) (D.pt_p t)))

private lemma tau_p (D : Dat p g B Tw Dt Oe σ cp) (j : Ix g) : p • D.L.τ j 0 = 0 := by
  have h := D.L.τ_tors j 0
  rwa [zero_add, pow_one] at h

private lemma act_ptOf (D : Dat p g B Tw Dt Oe σ cp) (a : Oe) (t : Nb p g) :
    (D.A.act a Tw.O (LHom.id Tw.O) ⟨ptOf B D.L.τ t, (mem_torP B p _).2 (D.pt_p t)⟩ : B.G Tw.O) =
      ptOf B D.L.τ (((D.H.ρ a).map PadicInt.toZMod) *ᵥ t) := by
  have h : (⟨ptOf B D.L.τ t, (mem_torP B p _).2 (D.pt_p t)⟩ : torP B p Tw.O) =
      ∑ j, (t j).val • (⟨D.L.τ j 0, (mem_torP B p _).2 (tau_p D j)⟩ : torP B p Tw.O) := by
    apply Subtype.ext
    simp [ptOf]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum, AddSubgroup.val_finsetSum]
  simp only [map_nsmul, AddSubgroup.coe_nsmul]
  simp only [D.L.ρ_spec, Finset.smul_sum]
  rw [Finset.sum_comm, ptOf]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mulVec, dotProduct, val_sum_mul_smul _ (tau_p D k)]
  rfl

private lemma red_mulVec (M : Matrix (Ix g) (Ix g) ℤ_[p]) (t : TT p g) :
    red p g (M *ᵥ t) = (M.map PadicInt.toZMod) *ᵥ red p g t := by
  funext k
  exact (RingHom.map_mulVec PadicInt.toZMod M t k)

private lemma eval_congr (D : Dat p g B Tw Dt Oe σ cp) (F : ∀ i, (D.fin.AAx i : Type))
    {i j : D.fin.ι} (φ : LHom (D.fin.AAx i) Tw.O) (φ' : LHom (D.fin.AAx j) Tw.O) (h : i = j)
    (h' : HEq φ φ') : φ.1 (F i) = φ'.1 (F j) := by
  subst h
  rw [eq_of_heq h']

private lemma evAll_act (D : Dat p g B Tw Dt Oe σ cp) (C : Type) [Field C]
    [Algebra (Tw.O : Type) C] (a : Oe) (F : ∀ i, (D.fin.AAx i : Type)) :
    ∃ F' : ∀ i, (D.fin.AAx i : Type), ∀ t : Nb p g,
      D.evAll C F' t = D.evAll C F (((D.H.ρ a).map PadicInt.toZMod) *ᵥ t) := by
  have key := fun i => D.fin.univ (D.fin.AAx i) (D.fin.sO i)
    (D.A.act a (D.fin.AAx i) (D.fin.sO i) ⟨D.fin.y i, (mem_torP B p _).2 (D.fin.y_p i)⟩ : B.G _)
    ((mem_torP B p _).1 (Subtype.property _))
  choose m α hs hy _ using key
  refine ⟨fun i => (α i).1 (F (m i)), fun t => ?_⟩
  obtain ⟨h1, h2, -⟩ := ptMap_spec D t
  obtain ⟨-, -, h3⟩ := ptMap_spec D (((D.H.ρ a).map PadicInt.toZMod) *ᵥ t)
  have e1 : ((D.ptMap t).comp (α (D.ptIdx t))).comp (D.fin.sO _) = LHom.id Tw.O := by
    rw [← h1, ← hs (D.ptIdx t)]
    rfl
  have e2 : B.map ((D.ptMap t).comp (α (D.ptIdx t))) (D.fin.y _) =
      ptOf B D.L.τ (((D.H.ρ a).map PadicInt.toZMod) *ᵥ t) := by
    rw [B.map_comp, hy, D.A.act_nat a _ _ _ h1, ← act_ptOf]
    congr 2
    exact Subtype.ext h2
  obtain ⟨h4, h5⟩ := h3 _ _ e1 e2
  unfold Dat.evAll
  rw [← eval_congr D F _ _ h4 h5]
  rfl

theorem evImg_act_stable :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), EvActStatement D) := by
  intro R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D C _ _ a f hf
  refine ⟨fun t => f (((D.H.ρ a).map PadicInt.toZMod) *ᵥ t), ?_, fun t => by rw [red_mulVec]⟩
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, rfl⟩ := hx
    obtain ⟨F', hF'⟩ := evAll_act D C a F
    exact Submodule.subset_span ⟨F', funext hF'⟩
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

end GlobalTheory.EvAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NsmulFAddSqZeroEq
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

private lemma fgInv_span_le_nil {S ι : Type} [CommRing S] (a : ι → S) (ha : ∀ i, IsNilpotent (a i)) :
    Ideal.span (Set.range a) ≤ nilradical S := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact mem_nilradical.2 (ha i)

private lemma fgInv_elim_nil {S ι κ : Type} [CommRing S] (a : ι → S) (b : κ → S)
    (ha : ∀ i, IsNilpotent (a i)) (hb : ∀ i, IsNilpotent (b i)) :
    ∀ i, IsNilpotent (Sum.elim a b i) := by
  rintro (i | i)
  · exact ha i
  · exact hb i

private lemma fgInv_det_unit {S : Type} [CommRing S] {g : ℕ} (M : Matrix (Fin g) (Fin g) S)
    (hM : ∀ k j, M k j - (1 : Matrix (Fin g) (Fin g) S) k j ∈ nilradical S) : IsUnit M.det := by
  have h1 : (Ideal.Quotient.mk (nilradical S)).mapMatrix M =
      (Ideal.Quotient.mk (nilradical S)).mapMatrix 1 := by
    ext k j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact Ideal.Quotient.eq.2 (hM k j)
  have h2 : Ideal.Quotient.mk (nilradical S) M.det = Ideal.Quotient.mk (nilradical S) 1 := by
    rw [RingHom.map_det, h1, map_one, Matrix.det_one, map_one]
  have h3 : IsNilpotent (M.det - 1) := mem_nilradical.1 (Ideal.Quotient.eq.1 h2)
  have h4 := h3.isUnit_add_one
  simpa using h4

private lemma fgInv_mulVec_sq {S : Type} [CommRing S] {g : ℕ} (N : Matrix (Fin g) (Fin g) S)
    (e : Fin g → S) (he : ∀ i j, e i * e j = 0) : ∀ i j, (N *ᵥ e) i * (N *ᵥ e) j = 0 := by
  intro i j
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
  rw [mul_mul_mul_comm, he, mul_zero]

private lemma fgInv_mulVec_eq {S : Type} [CommRing S] {g : ℕ} (M : Matrix (Fin g) (Fin g) S)
    (v u : Fin g → S) (hvu : ∀ i j, v i * u j = 0)
    (hM : ∀ k j, M k j - (1 : Matrix (Fin g) (Fin g) S) k j ∈ Ideal.span (Set.range v)) :
    M *ᵥ u = u := by
  have h : (M - 1) *ᵥ u = 0 := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have key : ∀ x ∈ Ideal.span (Set.range v), x * u j = 0 := by
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hx
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun l _ => by rw [mul_assoc, hvu, mul_zero]
    exact key _ (hM k j)
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h

theorem nsmulF_add_sqZero_eq :
  (∀ {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : ι → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
    ∃ M : Matrix (Fin g) (Fin g) S, (∀ k j, M k j - (1 : Matrix (Fin g) (Fin g) S) k j ∈ Ideal.span (Set.range a)) ∧
      ∀ e : Fin g → S, (∀ i j, e i * e j = 0) → fAdd ch.F a e = a + M *ᵥ e) →
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (n : ℕ) (S : Type) [CommRing S] [Algebra R₀ S], (n : S) = 0 → ∀ a e : Fin g → S, (∀ i, IsNilpotent (a i)) →
    (∀ i j, e i * e j = 0) → nsmulF ch.F (a + e) n = nsmulF ch.F a n) := by
  intro H1 H2 R₀ _ g B K ch n S _ _ hn a e ha he
  have h0 : ∀ i : Fin g, IsNilpotent ((0 : Fin g → S) i) := fun _ => IsNilpotent.zero
  have hnil : ∀ x y : Fin g → S, (∀ i, IsNilpotent (x i)) → (∀ i, IsNilpotent (y i)) →
      ∀ i, IsNilpotent (fAdd ch.F x y i) := by
    intro x y hx hy k
    have hxy := fgInv_elim_nil x y hx hy
    have h00 := fgInv_elim_nil (0 : Fin g → S) (0 : Fin g → S) h0 h0
    have e1 := fgInv_span_le_nil _ hxy (((H1 (ch.F k) S (Sum.elim x y)).2 hxy).2)
    have e2 := fgInv_span_le_nil _ h00 (((H1 (ch.F k) S (Sum.elim 0 0)).2 h00).2)
    have e3 : nEval (ch.F k) (Sum.elim (0 : Fin g → S) (0 : Fin g → S)) = 0 :=
      congrFun (ch.F_unit S 0 h0) k
    rw [e3] at e2
    have e4 := (nilradical S).sub_mem e1 e2
    rw [sub_sub_sub_cancel_right, sub_zero] at e4
    exact mem_nilradical.1 e4
  have hns : ∀ x : Fin g → S, (∀ i, IsNilpotent (x i)) → ∀ m,
      ∀ i, IsNilpotent (nsmulF ch.F x m i) := by
    intro x hx m
    induction m with
    | zero => exact h0
    | succ m ih => exact hnil _ _ ih hx
  have hdist : ∀ x y : Fin g → S, (∀ i, IsNilpotent (x i)) → (∀ i, IsNilpotent (y i)) → ∀ m,
      nsmulF ch.F (fAdd ch.F x y) m = fAdd ch.F (nsmulF ch.F x m) (nsmulF ch.F y m) := by
    intro x y hx hy m
    induction m with
    | zero => exact (ch.F_unit S 0 h0).symm
    | succ m ih =>
      have hX := hns x hx m
      have hY := hns y hy m
      show fAdd ch.F (nsmulF ch.F (fAdd ch.F x y) m) (fAdd ch.F x y) =
        fAdd ch.F (fAdd ch.F (nsmulF ch.F x m) x) (fAdd ch.F (nsmulF ch.F y m) y)
      rw [ih, ch.F_assoc S _ _ _ hX hY (hnil _ _ hx hy),
        ch.F_assoc S _ _ _ hX hx (hnil _ _ hY hy),
        ← ch.F_assoc S _ _ _ hY hx hy, ← ch.F_assoc S _ _ _ hx hY hy, ch.F_comm S _ _ hY hx]
  obtain ⟨M, hM, hMe⟩ := H2 ch S a ha
  have hdet : IsUnit M.det :=
    fgInv_det_unit M fun k j => fgInv_span_le_nil a ha (hM k j)
  set u : Fin g → S := M⁻¹ *ᵥ e with hu
  have huu : ∀ i j, u i * u j = 0 := fgInv_mulVec_sq _ e he
  have hun : ∀ i, IsNilpotent (u i) := fun i => ⟨2, by rw [pow_two, huu]⟩
  have hau : fAdd ch.F a u = a + e := by
    rw [hMe u huu, hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hmu : ∀ m : ℕ, nsmulF ch.F u m = (m : S) • u := by
    intro m
    induction m with
    | zero => simp [nsmulF]
    | succ m ih =>
      show fAdd ch.F (nsmulF ch.F u m) u = _
      obtain ⟨N, hN, hNe⟩ := H2 ch S (nsmulF ch.F u m) (hns u hun m)
      rw [hNe u huu, fgInv_mulVec_eq N _ u _ hN, ih, Nat.cast_succ, add_smul, one_smul]
      intro i j
      rw [ih, Pi.smul_apply, smul_eq_mul, mul_assoc, huu, mul_zero]
  rw [← hau, hdist a u ha hun, hmu, hn, zero_smul, ch.F_unit S _ (hns a ha n)]

end GlobalTheory
end

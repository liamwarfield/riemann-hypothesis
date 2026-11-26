module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeWildJumpSumOfElementaryAbelian
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachPrismOverIntegers

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProjectiveOfFreeLatticeOverFiniteFreeRing
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProjectiveOfFreeLatticeOverFiniteFreeRing
namespace GlobalTheory

theorem projective_compHom_of_free_of_finite_free :
    ∀ (Z S A D : Type) [CommRing Z] [CommRing S] [CommRing A] [AddCommGroup D] [Module A D] (z : Z →+* S) (a : S →+* A) (N : Submodule A D) (q : ℕ) (x : Fin q → D), (∀ y, y ∈ N ↔ ∃ s : Fin q → S, y = ∑ i, a (s i) • x i) → (∀ s : Fin q → S, ∑ i, a (s i) • x i = 0 → s = 0) → (∃ (d : ℕ) (w : Fin d → S), ∀ y : S, ∃! c : Fin d → Z, y = ∑ i, z (c i) * w i) → @Module.Projective Z _ ↥N _ (Module.compHom _ (a.comp z)) := by
  intro Z S A D _ _ _ _ _ z a N q x hN hli ⟨d, w, hw⟩
  letI : Module Z N := Module.compHom _ (a.comp z)
  have hsm : ∀ (r : Z) (n : N), ((r • n : N) : D) = a (z r) • (n : D) := fun _ _ => rfl
  let f : (Fin q → Fin d → Z) →ₗ[Z] N :=
    { toFun := fun c => ⟨∑ i, a (∑ m, z (c i m) * w m) • x i, (hN _).2 ⟨_, rfl⟩⟩
      map_add' := fun c c' => by
        apply Subtype.ext
        simp [add_mul, Finset.sum_add_distrib, add_smul]
      map_smul' := fun r c => by
        apply Subtype.ext
        rw [hsm]
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Finset.smul_sum,
          smul_smul, mul_assoc, ← Finset.mul_sum] }
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    have h1 := hli (fun i => ∑ m, z (c i m) * w m) (congrArg Subtype.val hc)
    funext i
    have h2 : (0 : S) = ∑ m, z (c i m) * w m := (congrFun h1 i).symm
    exact (hw 0).unique h2 (by simp)
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨s, rfl⟩ := (hN y).1 hy
    choose c hc _ using fun i => hw (s i)
    refine ⟨c, Subtype.ext ?_⟩
    change ∑ i, a (∑ m, z (c i m) * w m) • x i = ∑ i, a (s i) • x i
    exact Finset.sum_congr rfl fun i _ => by rw [← hc i]
  exact Module.Projective.of_equiv (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProjectiveOfFreeLatticeOverFiniteFreeRingStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_of_free_lattice_over_finite_free_ring : ∀ (Z S A D : Type) [CommRing Z] [CommRing S] [CommRing A] [AddCommGroup D] [Module A D] (z : Z →+* S) (a : S →+* A) (N : Submodule A D) (q : ℕ) (x : Fin q → D), (∀ y, y ∈ N ↔ ∃ s : Fin q → S, y = ∑ i, a (s i) • x i) → (∀ s : Fin q → S, ∑ i, a (s i) • x i = 0 → s = 0) → (∃ (d : ℕ) (w : Fin d → S), ∀ y : S, ∃! c : Fin d → Z, y = ∑ i, z (c i) * w i) → @Module.Projective Z _ ↥N _ (Module.compHom _ (a.comp z)) := by
  first | exact @GlobalTheory.projective_compHom_of_free_of_finite_free | exact GlobalTheory.projective_compHom_of_free_of_finite_free | (intros; apply GlobalTheory.projective_compHom_of_free_of_finite_free <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicCoordinatesOfBasisModP
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicCoordinatesOfBasisModP
namespace GlobalTheory.AdicCoord

theorem eq_zero_of_forall_pow_dvd {R : Type} [CommRing R] (x : R)
    [IsHausdorff (Ideal.span {x}) R] (y : R) (h : ∀ N : ℕ, x ^ N ∣ y) : y = 0 := by
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {x}) R) y fun N => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact h N

theorem exists_sum_series {R : Type} [CommRing R] (x : R)
    [IsPrecomplete (Ideal.span {x}) R] (a : ℕ → R) :
    ∃ L : R, ∀ N : ℕ, x ^ N ∣ (∑ k ∈ Finset.range N, x ^ k * a k) - L := by
  have key : ∀ (N : ℕ) (u v : R), u ≡ v [SMOD ((Ideal.span {x}) ^ N • ⊤ : Submodule R R)] ↔
      x ^ N ∣ u - v := by
    intro N u v
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {x}) R)
    (f := fun N => ∑ k ∈ Finset.range N, x ^ k * a k) (by
      intro m n hmn
      rw [key, ← dvd_neg, neg_sub, ← Finset.sum_Ico_eq_sub _ hmn]
      refine Finset.dvd_sum fun k hk => ?_
      exact Dvd.dvd.mul_right (pow_dvd_pow x (Finset.mem_Ico.1 hk).1) _)
  exact ⟨L, fun N => (key N _ _).1 (hL N)⟩

theorem exists_coord : ∀ (p : ℕ) (O EE W RW : Type) [CommRing O] [CommRing EE] [CommRing W] [CommRing RW] [Algebra O EE] [Algebra O RW] (ι : EE →ₐ[O] RW) (c : W →+* RW) (d : ℕ) (o : Fin d → O), (∀ r : RW, ∃! w : Fin d → W, r = ∑ j, o j • c (w j)) → IsAdicComplete (Ideal.span {(p : EE)}) EE → IsAdicComplete (Ideal.span {(p : W)}) W → (∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e - ∑ j, o j • e' j ∈ Ideal.span {(p : EE)}) → ∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j := by
  intro p O EE W RW _ _ _ _ _ _ ι c d o huniq hE hW hstep e
  choose g hg1 hg2 using hstep
  choose w hw using hg1
  simp only [Ideal.mem_span_singleton] at hg2
  choose h hh using hg2

  have hsep : ∀ r : RW, (∀ N : ℕ, (p : RW) ^ N ∣ r) → r = 0 := by
    intro r hr
    obtain ⟨u, hu, huu⟩ := huniq r
    have hu0 : ∀ j, u j = 0 := by
      intro j
      refine eq_zero_of_forall_pow_dvd (p : W) _ fun N => ?_
      obtain ⟨r', hr'⟩ := hr N
      obtain ⟨u', hu', -⟩ := huniq r'
      have : (fun j => (p : W) ^ N * u' j) = u := by
        apply huu
        rw [hr', hu', Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp
      exact ⟨u' j, by rw [← this]⟩
    rw [hu]
    simp [hu0]
  choose F hF using fun j => exists_sum_series (p : EE) (fun k => g (h^[k] e) j)
  choose V hV using fun j => exists_sum_series (p : W) (fun k => w (h^[k] e) j)
  refine ⟨F, fun j => ⟨V j, ?_⟩, ?_⟩
  · rw [← sub_eq_zero]
    refine hsep _ fun N => ?_
    have h1 := map_dvd ι (hF j N)
    have h2 := map_dvd c (hV j N)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_pow, map_natCast, map_sub, map_sum, map_mul, hw] at h1 h2
    have := dvd_sub h1 h2
    convert this using 1
    ring
  · have hiter : ∀ N : ℕ, e = ∑ j, o j • (∑ k ∈ Finset.range N, (p : EE) ^ k * g (h^[k] e) j)
        + (p : EE) ^ N * h^[N] e := by
      intro N
      induction N with
      | zero => simp
      | succ n ih =>
        have h3 := hh (h^[n] e)
        rw [sub_eq_iff_eq_add] at h3
        rw [Function.iterate_succ_apply']
        simp only [Finset.sum_range_succ, smul_add, Finset.sum_add_distrib]
        have h4 : ∑ j, o j • ((p : EE) ^ n * g (h^[n] e) j)
            = (p : EE) ^ n * ∑ j, o j • g (h^[n] e) j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => (mul_smul_comm _ _ _).symm
        rw [h4]
        linear_combination ih + (p : EE) ^ n * h3
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_pow_dvd (p : EE) _ fun N => ?_
    have h5 : e - ∑ j, o j • F j =
        ∑ j, o j • ((∑ k ∈ Finset.range N, (p : EE) ^ k * g (h^[k] e) j) - F j)
        + (p : EE) ^ N * h^[N] e := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      linear_combination hiter N
    rw [h5]
    refine dvd_add (Finset.dvd_sum fun j _ => ?_) (dvd_mul_right _ _)
    rw [Algebra.smul_def]
    exact Dvd.dvd.mul_left (hF j N) _

end GlobalTheory.AdicCoord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicCoordinatesOfBasisModPStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adic_coordinates_of_basis_mod_p : ∀ (p : ℕ) (O EE W RW : Type) [CommRing O] [CommRing EE] [CommRing W] [CommRing RW] [Algebra O EE] [Algebra O RW] (ι : EE →ₐ[O] RW) (c : W →+* RW) (d : ℕ) (o : Fin d → O), (∀ r : RW, ∃! w : Fin d → W, r = ∑ j, o j • c (w j)) → IsAdicComplete (Ideal.span {(p : EE)}) EE → IsAdicComplete (Ideal.span {(p : W)}) W → (∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e - ∑ j, o j • e' j ∈ Ideal.span {(p : EE)}) → ∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j := by
  first | exact @GlobalTheory.AdicCoord.exists_coord | exact GlobalTheory.AdicCoord.exists_coord | (intros; apply GlobalTheory.AdicCoord.exists_coord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitMatrixOfPowSmulSpanInvert
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitMatrixOfPowSmulSpanInvert
namespace GlobalTheory

def powDenomSubring {S EE : Type} [CommRing S] [CommRing EE] (a : S →+* EE) (Q : S) :
    Subring EE where
  carrier := {e | ∃ (n : ℕ) (t : S), a Q ^ n * e = a t}
  mul_mem' := by
    rintro e f ⟨n, t, ht⟩ ⟨m, r, hr⟩
    refine ⟨n + m, t * r, ?_⟩
    rw [map_mul, ← ht, ← hr]; ring
  one_mem' := ⟨0, 1, by simp⟩
  add_mem' := by
    rintro e f ⟨n, t, ht⟩ ⟨m, r, hr⟩
    refine ⟨n + m, Q ^ m * t + Q ^ n * r, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, ← ht, ← hr]; ring
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro e ⟨n, t, ht⟩
    refine ⟨n, -t, ?_⟩
    rw [map_neg, ← ht]; ring

theorem eq_zero_of_sum_smul_eq_zero_of_powDenom {S EE W RW Y : Type} [CommRing S] [CommRing EE]
    [CommRing W] [CommRing RW] [AddCommGroup Y] [Module RW Y] (a : S →+* EE) (ι : EE →+* RW)
    (c : W →+* RW) (ψ : S →+* W) (Q : S) (hι : Function.Injective ι)
    (hc : ∀ s, ι (a s) = c (ψ s)) (hQ : IsUnit (a Q)) {q : ℕ} (x : Fin q → Y)
    (hx : ∀ w : Fin q → W, ∑ i, c (w i) • x i = 0 → w = 0) (E : Fin q → EE)
    (hE : ∀ m, E m ∈ powDenomSubring a Q) (h0 : ∑ m, ι (E m) • x m = 0) (m : Fin q) :
    E m = 0 := by
  choose n t ht using hE
  set N := ∑ m, n m with hN
  have hle : ∀ m, n m ≤ N := fun m =>
    Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
  have h1 : ∀ m, a Q ^ N * E m = a (Q ^ (N - n m) * t m) := by
    intro m
    rw [map_mul, map_pow, ← ht, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hle m)]
  have h2 := hx (fun m => ψ (Q ^ (N - n m) * t m)) (by
    have : ∀ m, c (ψ (Q ^ (N - n m) * t m)) • x m = ι (a Q ^ N) • (ι (E m) • x m) := by
      intro m
      rw [← hc, ← h1, map_mul, mul_smul]
    simp only [this]
    rw [← Finset.smul_sum, h0, smul_zero])
  have h3 : ψ (Q ^ (N - n m) * t m) = 0 := congrFun h2 m
  have h4 : a Q ^ N * E m = 0 := by
    apply hι
    rw [h1, hc, h3, map_zero, map_zero]
  exact ((hQ.pow N).mul_right_eq_zero).1 h4

theorem exists_coeff_powDenom {S EE W RW Y : Type} [CommRing S] [CommRing EE]
    [CommRing W] [CommRing RW] [AddCommGroup Y] [Module RW Y] (a : S →+* EE) (ι : EE →+* RW)
    (c : W →+* RW) (ψ : S →+* W) (Q : S)
    (hc : ∀ s, ι (a s) = c (ψ s)) (hQ : IsUnit (a Q)) {q : ℕ} (x : Fin q → Y) (y : Y)
    (hy : ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • y = ∑ i, c (ψ (s i)) • x i) :
    ∃ E : Fin q → EE, (∀ i, E i ∈ powDenomSubring a Q) ∧ y = ∑ i, ι (E i) • x i := by
  obtain ⟨k, s, hs⟩ := hy
  obtain ⟨v, hv⟩ := (hQ.pow k).exists_left_inv
  refine ⟨fun i => v * a (s i), fun i => ⟨k, s i, ?_⟩, ?_⟩
  · rw [← mul_assoc, mul_comm _ v, hv, one_mul]
  · have : ∀ i, ι (v * a (s i)) • x i = ι v • (c (ψ (s i)) • x i) := by
      intro i
      rw [map_mul, mul_smul, hc]
    simp only [this]
    rw [← Finset.smul_sum, ← hs, ← hc, ← map_pow, ← mul_smul, ← map_mul, hv, map_one, one_smul]

theorem exists_isUnit_matrix_of_pow_smul_span : ∀ (S EE W RW Y : Type) [CommRing S] [CommRing EE] [CommRing W] [CommRing RW] [AddCommGroup Y] [Module RW Y] (a : S →+* EE) (ι : EE →+* RW) (c : W →+* RW) (ψ : S →+* W) (Q : S), Function.Injective ι → (∀ s, ι (a s) = c (ψ s)) → IsUnit (a Q) → ∀ (q : ℕ) (x z : Fin q → Y), (∀ w : Fin q → W, ∑ i, c (w i) • x i = 0 → w = 0) → (∀ j, ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • z j = ∑ i, c (ψ (s i)) • x i) → (∀ i, ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • x i = ∑ j, c (ψ (s j)) • z j) → ∃ A : Matrix (Fin q) (Fin q) EE, IsUnit A ∧ ∀ j, z j = ∑ i, ι (A i j) • x i := by
  intro S EE W RW Y _ _ _ _ _ _ a ι c ψ Q hι hc hQ q x z hx hz hx'
  choose A hAm hA using fun j => exists_coeff_powDenom a ι c ψ Q hc hQ x (z j) (hz j)
  choose B hBm hB using fun i => exists_coeff_powDenom a ι c ψ Q hc hQ z (x i) (hx' i)
  refine ⟨Matrix.of fun i j => A j i, ?_, fun j => by simpa using hA j⟩
  have hAB : (Matrix.of fun i j => A j i) * (Matrix.of fun j i => B i j)
      = (1 : Matrix (Fin q) (Fin q) EE) := by
    ext m i
    rw [← sub_eq_zero]
    refine eq_zero_of_sum_smul_eq_zero_of_powDenom a ι c ψ Q hι hc hQ x hx
      (fun m => ((Matrix.of fun i j => A j i) * (Matrix.of fun j i => B i j)) m i
        - (1 : Matrix (Fin q) (Fin q) EE) m i) ?_ ?_ m
    · intro m
      refine sub_mem ?_ ?_
      · rw [Matrix.mul_apply]
        exact sum_mem fun j _ => mul_mem (hAm j m) (hBm i j)
      · rw [Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
    · simp only [map_sub, sub_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      have h1 : ∑ m, ι ((1 : Matrix (Fin q) (Fin q) EE) m i) • x m = x i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro m _ hm
          simp [Matrix.one_apply_ne hm]
        · simp
      rw [h1]
      conv_rhs => rw [hB i]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hA j, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, mul_comm, mul_smul]
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hAB)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitMatrixOfPowSmulSpanInvertStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isUnit_matrix_of_pow_smul_span_invert : ∀ (S EE W RW Y : Type) [CommRing S] [CommRing EE] [CommRing W] [CommRing RW] [AddCommGroup Y] [Module RW Y] (a : S →+* EE) (ι : EE →+* RW) (c : W →+* RW) (ψ : S →+* W) (Q : S), Function.Injective ι → (∀ s, ι (a s) = c (ψ s)) → IsUnit (a Q) → ∀ (q : ℕ) (x z : Fin q → Y), (∀ w : Fin q → W, ∑ i, c (w i) • x i = 0 → w = 0) → (∀ j, ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • z j = ∑ i, c (ψ (s i)) • x i) → (∀ i, ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • x i = ∑ j, c (ψ (s j)) • z j) → ∃ A : Matrix (Fin q) (Fin q) EE, IsUnit A ∧ ∀ j, z j = ∑ i, ι (A i j) • x i := by
  first | exact @GlobalTheory.exists_isUnit_matrix_of_pow_smul_span | exact GlobalTheory.exists_isUnit_matrix_of_pow_smul_span | (intros; apply GlobalTheory.exists_isUnit_matrix_of_pow_smul_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeLatticeOfBasisAfterExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeLatticeOfBasisAfterExtension
open TensorProduct

namespace GlobalTheory

theorem isBaseChange_subtype_of_basis_after_extension : ∀ (S A EE O W RW D Y : Type) [CommRing S] [CommRing A] [CommRing EE] [CommRing O] [CommRing W] [CommRing RW] [Algebra O A] [Algebra A EE] [Algebra O EE] [IsScalarTower O A EE] [Algebra O RW] [AddCommGroup D] [Module EE D] [Module A D] [IsScalarTower A EE D] [AddCommGroup Y] [Module RW Y] (a : S →+* A) (ι : EE →ₐ[O] RW) (c : W →+* RW) (jD : D →+ Y), Function.Injective ι → (∀ e, IsUnit (ι e) → IsUnit e) → (∀ (e : EE) (x : D), jD (e • x) = ι e • jD x) → (∀ s, ι (algebraMap A EE (a s)) ∈ Set.range c) → ∀ (d r : ℕ) (o : Fin d → O), (∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j) → Nonempty (Module.Basis (Fin r) EE D) → ∀ (q : ℕ) (x : Fin q → D), q = d * r → (∀ y : Y, ∃! w : Fin q → W, y = ∑ i, c (w i) • jD (x i)) → ∀ N : Submodule A D, (∀ y, y ∈ N ↔ ∃ s : Fin q → S, y = ∑ i, a (s i) • x i) → IsBaseChange EE N.subtype := by
  intro S A EE O W RW D Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a ι c jD hinj hunit hjD ha d r o ho
    ⟨b⟩ q x hq huniq N hN
  classical
  subst hq
  have hxN : ∀ i, x i ∈ N := by
    intro i
    refine (hN _).2 ⟨Pi.single i 1, ?_⟩
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  have hjsum : ∀ e : Fin (d * r) → EE, ∀ v : Fin (d * r) → D,
      jD (∑ i, e i • v i) = ∑ i, ι (e i) • jD (v i) := by
    intro e v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hjD _ _

  have hspan : ∀ y : D, y ∈ Submodule.span EE (Set.range x) := by
    choose e' he' hdec using ho
    choose w' hw' using he'
    let u : Fin (d * r) → D := fun l =>
      algebraMap O EE (o (finProdFinEquiv.symm l).1) • b (finProdFinEquiv.symm l).2
    let C' : Matrix (Fin (d * r)) (Fin (d * r)) EE := fun i l =>
      e' (b.repr (x i) (finProdFinEquiv.symm l).2) (finProdFinEquiv.symm l).1
    let C : Matrix (Fin (d * r)) (Fin (d * r)) W := fun i l =>
      w' (b.repr (x i) (finProdFinEquiv.symm l).2) (finProdFinEquiv.symm l).1
    have hCC : ∀ i l, c (C i l) = ι (C' i l) := fun i l => hw' _ _
    have hx : ∀ i, x i = ∑ l, C' i l • u l := by
      intro i
      rw [← finProdFinEquiv.sum_comp]
      simp only [C', u, Equiv.symm_apply_apply]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      conv_lhs => rw [← b.sum_repr (x i)]
      refine Finset.sum_congr rfl fun k _ => ?_
      conv_lhs => rw [hdec (b.repr (x i) k)]
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, Algebra.smul_def, mul_comm]
    choose B hB using fun l => (huniq (jD (u l))).exists
    have hCB : C * Matrix.of B = 1 := by
      ext i m
      have h1 : jD (x i) = ∑ m, c ((C * Matrix.of B) i m) • jD (x m) := by
        conv_lhs => rw [hx i, hjsum]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_smul, Matrix.of_apply]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hB l, Finset.smul_sum, ← hCC]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [smul_smul]
      have h2 : jD (x i) = ∑ m, c ((1 : Matrix _ _ W) i m) • jD (x m) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          simp [Matrix.one_apply_ne hj.symm]
        · simp
      exact congrFun ((huniq _).unique h1 h2) m
    have hdetC : IsUnit C.det := Matrix.isUnit_det_of_right_inverse hCB
    have hdetC' : IsUnit C'.det := by
      apply hunit
      have h1 : ι C'.det = c C.det := by
        rw [RingHom.map_det, AlgHom.map_det]
        congr 1
        ext i l
        simp [hCC]
      rw [h1]
      exact hdetC.map c
    have hu : ∀ l, u l ∈ Submodule.span EE (Set.range x) := by
      intro l
      have h1 : u l = ∑ i, C'⁻¹ l i • x i := by
        have h2 : ∑ i, C'⁻¹ l i • x i = ∑ m, (C'⁻¹ * C') l m • u m := by
          simp only [Matrix.mul_apply, Finset.sum_smul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hx i, Finset.smul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [smul_smul]
        rw [h2, Matrix.nonsing_inv_mul _ hdetC', Finset.sum_eq_single l]
        · simp
        · intro j _ hj
          simp [Matrix.one_apply_ne hj.symm]
        · simp
      rw [h1]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hb : ∀ k, b k ∈ Submodule.span EE (Set.range x) := by
      intro k
      have h1 : b k = ∑ j, e' 1 j • u (finProdFinEquiv (j, k)) := by
        conv_lhs => rw [← one_smul EE (b k), hdec 1, Finset.sum_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [u, Equiv.symm_apply_apply]
        rw [smul_smul, Algebra.smul_def, mul_comm]
      rw [h1]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hu _)
    intro y
    rw [← b.sum_repr y]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hb k)

  have hnf : ∀ t : EE ⊗[A] N, ∃ e : Fin (d * r) → EE, (∀ i, ι (e i) ∈ c.range) ∧
      t = ∑ i, e i ⊗ₜ[A] (⟨x i, hxN i⟩ : N) := by
    let P : AddSubmonoid (EE ⊗[A] N) :=
      { carrier := {t | ∃ e : Fin (d * r) → EE, (∀ i, ι (e i) ∈ c.range) ∧
          t = ∑ i, e i ⊗ₜ[A] (⟨x i, hxN i⟩ : N)}
        zero_mem' := ⟨0, fun i => by simp, by simp⟩
        add_mem' := by
          rintro _ _ ⟨e₁, h₁, rfl⟩ ⟨e₂, h₂, rfl⟩
          refine ⟨e₁ + e₂, fun i => ?_, ?_⟩
          · rw [Pi.add_apply, map_add (f := _)]
            exact add_mem (h₁ i) (h₂ i)
          · simp [TensorProduct.add_tmul, Finset.sum_add_distrib] }
    have hP : ∀ (e : EE) (n : N), ι e ∈ c.range → e ⊗ₜ[A] n ∈ P := by
      intro e n he
      obtain ⟨s, hs⟩ := (hN n).1 n.2
      have hn : n = ∑ i, a (s i) • (⟨x i, hxN i⟩ : N) := by
        apply Subtype.ext
        rw [hs]
        simp
      refine ⟨fun i => a (s i) • e, fun i => ?_, ?_⟩
      · beta_reduce
        rw [Algebra.smul_def, map_mul]
        exact mul_mem (ha (s i)) he
      · rw [hn, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [TensorProduct.smul_tmul]
    intro t
    change t ∈ P
    induction t using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add _ _ h₁ h₂ => exact add_mem h₁ h₂
    | tmul e n =>
      obtain ⟨e', he', hdec⟩ := ho e
      rw [hdec, TensorProduct.sum_tmul]
      refine sum_mem fun j _ => ?_
      rw [← algebraMap_smul A (o j) (e' j), TensorProduct.smul_tmul]
      exact hP _ _ (he' j)
  have hbij : Function.Bijective (N.subtype.liftBaseChange EE) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro t ht
      obtain ⟨e, he, rfl⟩ := hnf t
      choose w hw using he
      have h1 : ∑ i, e i • x i = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          simpa [map_sum, LinearMap.liftBaseChange_tmul] using ht
      have h2 : (0 : Y) = ∑ i, c (w i) • jD (x i) := by
        simp only [hw]
        rw [← hjsum, h1, map_zero]
      have h3 : (0 : Y) = ∑ i, c ((0 : Fin (d * r) → W) i) • jD (x i) := by simp
      have h4 : w = 0 := (huniq 0).unique h2 h3
      have h5 : ∀ i, e i = 0 := by
        intro i
        apply hinj
        rw [← hw, h4]
        simp
      simp [h5]
    · rw [← LinearMap.range_eq_top, eq_top_iff]
      intro y _
      refine Submodule.span_le.2 ?_ (hspan y)
      rintro _ ⟨i, rfl⟩
      exact ⟨1 ⊗ₜ[A] (⟨x i, hxN i⟩ : N), by simp [LinearMap.liftBaseChange_tmul]⟩
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hbij) fun n => ?_
  simp [LinearMap.liftBaseChange_tmul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeLatticeOfBasisAfterExtensionStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBaseChange_lattice_of_basis_after_extension : ∀ (S A EE O W RW D Y : Type) [CommRing S] [CommRing A] [CommRing EE] [CommRing O] [CommRing W] [CommRing RW] [Algebra O A] [Algebra A EE] [Algebra O EE] [IsScalarTower O A EE] [Algebra O RW] [AddCommGroup D] [Module EE D] [Module A D] [IsScalarTower A EE D] [AddCommGroup Y] [Module RW Y] (a : S →+* A) (ι : EE →ₐ[O] RW) (c : W →+* RW) (jD : D →+ Y), Function.Injective ι → (∀ e, IsUnit (ι e) → IsUnit e) → (∀ (e : EE) (x : D), jD (e • x) = ι e • jD x) → (∀ s, ι (algebraMap A EE (a s)) ∈ Set.range c) → ∀ (d r : ℕ) (o : Fin d → O), (∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j) → Nonempty (Module.Basis (Fin r) EE D) → ∀ (q : ℕ) (x : Fin q → D), q = d * r → (∀ y : Y, ∃! w : Fin q → W, y = ∑ i, c (w i) • jD (x i)) → ∀ N : Submodule A D, (∀ y, y ∈ N ↔ ∃ s : Fin q → S, y = ∑ i, a (s i) • x i) → IsBaseChange EE N.subtype := by
  first | exact @GlobalTheory.isBaseChange_subtype_of_basis_after_extension | exact GlobalTheory.isBaseChange_subtype_of_basis_after_extension | (intros; apply GlobalTheory.isBaseChange_subtype_of_basis_after_extension <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism

namespace GlobalTheory.WachLattice

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s} {R : WSer Γ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {I : WIo R RA RW inclR φR gR πA}

theorem jD_smulA (E : WEt I) (T : LocLat G Qp LL O) (α : LetA O n) (x : E.DD T) :
    E.jD T (α • x) = I.ioE (algebraMap _ R.EE α) • E.jD T x := by
  rw [← E.jD_smul, algebraMap_smul]

theorem isUnit_Q (R : WSer Γ) : IsUnit (algebraMap (LetA O n) R.EE R.Q) := by
  have h0 : IsUnit (algebraMap (LetA O n) R.EE (fun _ => R.q₀)) := by
    have h := R.EE_π.map R.φE
    rw [R.φE_ext] at h
    have e : letφ (n := n) R.φ₀ letπ = letπ * (fun _ => R.q₀) := funext fun i => R.φ₀_X
    rw [e, map_mul] at h
    exact isUnit_of_mul_isUnit_right h
  unfold WSer.Q
  induction (s - 1) with
  | zero => simpa using h0
  | succ k ih =>
    rw [pow_succ', AlgHom.mul_apply, ← R.φE_ext]
    exact ih.map R.φE


set_option maxHeartbeats 1000000 in
theorem build (E : WEt I) [Nontrivial R.EE] {Zl S W : Type} [CommRing Zl] [CommRing S] [CommRing W]
    (a : S →+* LetA O n) (z : PowerSeries Zl →+* S) (c : W →+* RW) (ψ : S →+* W) (π Q : S)
    (hψ : ∀ s, I.ioE (algebraMap _ R.EE (a s)) = c (ψ s)) (ha : Function.Injective a)
    (hinj : Function.Injective I.ioE) (hunit : ∀ x : R.EE, IsUnit (I.ioE x) → IsUnit x)
    (hπ : a π = letπ) (hQ : a Q = R.Q)
    (hz : ∃ (d : ℕ) (w : Fin d → S), ∀ y : S, ∃! c : Fin d → PowerSeries Zl, y = ∑ i, z (c i) * w i)
    (d : ℕ) (o : Fin d → O) (hA : ∀ α : LetA O n, ∃ s : Fin d → S, α = ∑ j, o j • a (s j))
    (hE : ∀ e : R.EE, ∃ e' : Fin d → R.EE, (∀ j, I.ioE (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j)
    (L : ∀ T : LocLat G Qp LL O, Set (TW RW T))
    (hB : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∃ (q : ℕ) (x : Fin q → E.DD T),
      q = d * Module.finrank O ↥T.L.T ∧ (∀ y, ∃! w : Fin q → W, y = ∑ i, c (w i) • E.jD T (x i)) ∧
      ∀ y, y ∈ L T ↔ ∃ s : Fin q → S, y = ∑ i, c (ψ (s i)) • E.jD T (x i))
    (hφ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ y ∈ L T, ∃ k : ℕ, c (ψ Q) ^ k • TWmap φR T y ∈ L T)
    (hφi : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ y ∈ L T, ∃ (k q : ℕ) (s : Fin q → S) (u : Fin q → TW RW T),
      (∀ i, u i ∈ L T) ∧ c (ψ Q) ^ k • y = ∑ i, c (ψ (s i)) • TWmap φR T (u i))
    (hΓ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : G), ∀ y ∈ L T, ∃ u ∈ L T,
      TWact (gR g) T g y - y = c (ψ π) • u)
    (hmap : ∀ (T T' : LocLat G Qp LL O) (f : LatHom T.L T'.L), IsCrys PD T.ρ → IsCrys PD T'.ρ → ∀ y ∈ L T,
      TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) ((f.f.restrictScalars O).restrict f.T_le) y ∈ L T')
    (hone : IsCrys PD Γ.one.ρ) (e₀ : ↥Γ.one.L.T) (he₀ : Submodule.span O {e₀} = ⊤)
    (hLone : ∀ y, y ∈ L Γ.one ↔ ∃ α : LetA O n, y = I.ioE (algebraMap _ R.EE α) • ((1 : RW) ⊗ₜ[O] e₀)) :
    Nonempty (WN E (a.comp z)) := by
  classical
  have hj : ∀ T (t : S) (x : E.DD T), E.jD T (a t • x) = c (ψ t) • E.jD T x := fun T t x => by
    rw [jD_smulA, hψ]
  choose q x hq hbas hL using hB
  have hsum : ∀ T hT (t : Fin (q T hT) → S),
      E.jD T (∑ i, a (t i) • x T hT i) = ∑ i, c (ψ (t i)) • E.jD T (x T hT i) := fun T hT t => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; exact Finset.sum_congr rfl fun i _ => hj _ _ _
  have hD : ∀ T hT (y : E.DD T), E.jD T y ∈ L T ↔ ∃ t : Fin (q T hT) → S, y = ∑ i, a (t i) • x T hT i :=
    fun T hT y => by
      rw [hL T hT]
      refine exists_congr fun t => ?_
      rw [← hsum, (E.jD_inj T).eq_iff]
  have hlift : ∀ T, IsCrys PD T.ρ → ∀ y ∈ L T, ∃ y', E.jD T y' = y := fun T hT y hy => by
    obtain ⟨t, rfl⟩ := (hL T hT y).1 hy
    exact ⟨_, hsum T hT t⟩
  have hadd : ∀ T, IsCrys PD T.ρ → ∀ y y' : E.DD T, E.jD T y ∈ L T → E.jD T y' ∈ L T →
      E.jD T (y + y') ∈ L T := fun T hT y y' hy hy' => by
    obtain ⟨t, rfl⟩ := (hD T hT y).1 hy
    obtain ⟨t', rfl⟩ := (hD T hT y').1 hy'
    refine (hD T hT _).2 ⟨t + t', ?_⟩
    simp only [Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib]
  have hzero : ∀ T, IsCrys PD T.ρ → E.jD T 0 ∈ L T := fun T hT => (hD T hT _).2 ⟨0, by simp⟩
  have hS : ∀ T, IsCrys PD T.ρ → ∀ (t : S) (y : E.DD T), E.jD T y ∈ L T → E.jD T (a t • y) ∈ L T :=
    fun T hT t y hy => by
    obtain ⟨t', rfl⟩ := (hD T hT y).1 hy
    refine (hD T hT _).2 ⟨fun i => t * t' i, ?_⟩
    simp only [map_mul, mul_smul, Finset.smul_sum]
  have hO : ∀ T, IsCrys PD T.ρ → ∀ (t : O) (y : E.DD T), E.jD T y ∈ L T → E.jD T (t • y) ∈ L T :=
    fun T hT t y hy => by
    rw [← E.map_latSmul, E.jD_map]
    exact hmap T T _ hT hT _ hy
  let N₀ : ∀ T, IsCrys PD T.ρ → Submodule (LetA O n) (E.DD T) := fun T hT =>
    { carrier := {y | E.jD T y ∈ L T}
      add_mem' := fun hy hy' => hadd T hT _ _ hy hy'
      zero_mem' := hzero T hT
      smul_mem' := fun α y hy => by
        obtain ⟨t, rfl⟩ := hA α
        rw [Finset.sum_smul]
        refine Finset.sum_induction _ (fun y => E.jD T y ∈ L T) (hadd T hT) (hzero T hT) fun j _ => ?_
        rw [smul_assoc]
        exact hO T hT _ _ (hS T hT _ _ hy) }
  let N : ∀ T, Submodule (LetA O n) (E.DD T) := fun T => if hT : IsCrys PD T.ρ then N₀ T hT else ⊥
  have hN : ∀ T, IsCrys PD T.ρ → ∀ y, y ∈ N T ↔ E.jD T y ∈ L T := fun T hT y => by
    simp only [N, dif_pos hT]; rfl
  have hN0 : ∀ T, ¬ IsCrys PD T.ρ → N T = ⊥ := fun T hT => dif_neg hT
  have hNx : ∀ T hT (y : E.DD T), y ∈ N T ↔ ∃ t : Fin (q T hT) → S, y = ∑ i, a (t i) • x T hT i :=
    fun T hT y => (hN T hT y).trans (hD T hT y)
  have hQk : ∀ T (k : ℕ) (y : E.DD T), E.jD T (R.Q ^ k • y) = c (ψ Q) ^ k • E.jD T y := fun T k y => by
    rw [← hQ, ← map_pow, hj, map_pow, map_pow]
  have hNπ : ∀ T (g : Γ.Gam), ∀ y ∈ N T, ∃ y' ∈ N T, E.γD T g y - y = (letπ : LetA O n) • y' := by
    intro T g y hy
    by_cases hT : IsCrys PD T.ρ
    · obtain ⟨g, rfl⟩ := Γ.resΓ_onto g
      obtain ⟨u, hu, h⟩ := hΓ T hT g _ ((hN T hT y).1 hy)
      obtain ⟨y', rfl⟩ := hlift T hT u hu
      refine ⟨y', (hN T hT _).2 hu, E.jD_inj T ?_⟩
      rw [map_sub, E.jD_act, h, ← hπ, hj]
    · rw [hN0 T hT] at hy ⊢
      rw [Submodule.mem_bot] at hy
      exact ⟨0, Submodule.zero_mem _, by simp [hy]⟩
  refine ⟨{ N := N, N_base := ?_, N_φ := ?_, N_φinv := ?_, N_fg := ?_, N_Γ := ?_, N_π := hNπ, map_N := ?_,
            one_e := ?_, N_proj := ?_, N_junk := hN0 }⟩
  · intro T hT
    have hfree := (E.DD_free T).1
    have hfin : Module.Finite R.EE (E.DD T) := by
      rcases Nat.eq_zero_or_pos (Module.finrank R.EE (E.DD T)) with h0 | h0
      · have hq0 : q T hT = 0 := by rw [hq, ← (E.DD_free T).2, h0, mul_zero]
        have : Subsingleton (E.DD T) := ⟨fun y y' => E.jD_inj T (by
          obtain ⟨w, hw, -⟩ := hbas T hT (E.jD T y)
          obtain ⟨w', hw', -⟩ := hbas T hT (E.jD T y')
          have : IsEmpty (Fin (q T hT)) := by rw [hq0]; infer_instance
          rw [hw, hw', Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_empty])⟩
        infer_instance
      · exact Module.finite_of_finrank_pos h0
    exact GlobalTheory.T.isBaseChange_lattice_of_basis_after_extension S (LetA O n) R.EE O W RW (E.DD T) (TW RW T) a I.ioE c (E.jD T).toAddMonoidHom hinj hunit
      (E.jD_smul T) (fun t => ⟨_, (hψ t).symm⟩) d _ o hE ⟨Module.finBasis R.EE (E.DD T)⟩ _ (x T hT)
      (by rw [hq, (E.DD_free T).2]) (hbas T hT) _ (hNx T hT)
  · intro T y hy
    by_cases hT : IsCrys PD T.ρ
    · obtain ⟨k, hk⟩ := hφ T hT _ ((hN T hT y).1 hy)
      refine ⟨k, (hN T hT _).2 ?_⟩
      rw [← E.jD_φ, ← hQk] at hk
      exact hk
    · rw [hN0 T hT] at hy ⊢
      rw [Submodule.mem_bot] at hy
      exact ⟨0, by simp [hy]⟩
  · intro T y hy
    by_cases hT : IsCrys PD T.ρ
    · obtain ⟨k, m, t, u, hu, hk⟩ := hφi T hT _ ((hN T hT y).1 hy)
      choose u' hu' using fun i => hlift T hT _ (hu i)
      have e : R.Q ^ k • y = ∑ i, a (t i) • E.φD T (u' i) := E.jD_inj T (by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hQk, hk, map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hj, E.jD_φ, hu'])
      refine ⟨k, ?_⟩
      change R.Q ^ k • y ∈ _
      rw [e]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨u' i, (hN T hT _).2 (by rw [hu']; exact hu i), rfl⟩)
    · rw [hN0 T hT, Submodule.mem_bot] at hy
      exact ⟨0, by simp [hy]⟩
  · intro T
    by_cases hT : IsCrys PD T.ρ
    · have e : N T = Submodule.span (LetA O n) (Set.range (x T hT)) := by
        refine le_antisymm (fun y hy => ?_) (Submodule.span_le.2 ?_)
        · obtain ⟨t, rfl⟩ := (hNx T hT y).1 hy
          exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
        · rintro _ ⟨i, rfl⟩
          refine (hNx T hT _).2 ⟨Pi.single i 1, ?_⟩
          rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
          simp
      rw [e]
      exact Submodule.fg_span (Set.finite_range _)
    · rw [hN0 T hT]; exact Submodule.fg_bot
  · intro T g y hy
    obtain ⟨y', hy', h⟩ := hNπ T g y hy
    rw [sub_eq_iff_eq_add] at h
    rw [h]
    exact (N T).add_mem ((N T).smul_mem _ hy') hy
  · intro T T' f hT hT' y hy
    rw [hN T' hT', E.jD_map]
    exact hmap T T' f hT hT' _ ((hN T hT y).1 hy)
  · obtain ⟨e, he⟩ := hlift _ hone _ ((hLone ((1 : RW) ⊗ₜ[O] e₀)).2 ⟨1, by simp⟩)
    refine ⟨e, e₀, he₀, he, Submodule.ext fun y => ?_⟩
    rw [hN _ hone, hLone, Submodule.mem_span_singleton]
    refine exists_congr fun α => ?_
    rw [← he, ← jD_smulA, (E.jD_inj _).eq_iff, eq_comm]
  · intro T
    by_cases hT : IsCrys PD T.ρ
    · refine GlobalTheory.T.projective_of_free_lattice_over_finite_free_ring _ S _ _ z a (N T) _ (x T hT) (hNx T hT) (fun t ht => ?_) hz
      have h1 := congrArg (E.jD T) ht
      rw [hsum, map_zero] at h1
      have h2 := (hbas T hT 0).unique (y₁ := fun i => ψ (t i)) (y₂ := 0) h1.symm (by simp)
      funext i
      apply ha
      apply R.EE_inj
      apply hinj
      rw [hψ, congrFun h2 i]
      simp
    · let _ := Module.compHom ↥(N T) (a.comp z)
      have : Subsingleton ↥(N T) := by rw [hN0 T hT]; infer_instance
      infer_instance

end Generic

section Realisation

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {PS : Obj l ↥(OL K)} (ioH : Hom PS (ainfObj K))

theorem full (BS : GlobalTheory.Published.BhattScholzeCrystallineLattices) {T T' : Type} [AddCommGroup T] [Module ℤ_[l] T]
    [AddCommGroup T'] [Module ℤ_[l] T'] {ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)} {ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T')}
    {E E' : FCrys l ↥(OL K)}
    {j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)}
    {j' : E'.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T')}
    (H : Realises K E (ainfObj K) (ainfId K) T ρ j) (H' : Realises K E' (ainfObj K) (ainfId K) T' ρ' j')
    (f : T →ₗ[ℤ_[l]] T') (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (x : E.M PS) :
    ∃ x' : E'.M PS, j' (E'.tr ioH x') = f.lTensor (WCb l) (j (E.tr ioH x)) := by
  obtain ⟨u, hu, -⟩ := (BS l K _ _ (isAinf_ainfObj K)).2 T T' ρ ρ' E E' j j' H H' f hf
  exact ⟨u.u PS x, by rw [← u.u_tr, hu]⟩

theorem range_trivial (BS : GlobalTheory.Published.BhattScholzeCrystallineLattices) {T : Type} [AddCommGroup T] [Module ℤ_[l] T]
    {ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)} {E : FCrys l ↥(OL K)}
    {j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)}
    (H : Realises K E (ainfObj K) (ainfId K) T ρ j) (hρ : ∀ g x, ρ g x = x) {d : ℕ}
    (b : Module.Basis (Fin d) ℤ_[l] T) (y : WCb l ⊗[ℤ_[l]] T) :
    (∃ x : E.M PS, y = j (E.tr ioH x)) ↔
      ∃ t : Fin d → PS.A, y = ∑ i, inclW l (ainfId K (ioH.f (t i))) ⊗ₜ[ℤ_[l]] b i := by
  have U := (isAinf_ainfObj K).realises_unit
  have h1 : ∀ (w : WCb l) i, (LinearMap.toSpanSingleton ℤ_[l] T (b i)).lTensor (WCb l) (w ⊗ₜ[ℤ_[l]] (1 : ℤ_[l])) =
      w ⊗ₜ[ℤ_[l]] b i := fun w i => by
    rw [LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply, one_smul]
  have h2 : ∀ t : PS.A, unitMap (ainfObj K) (ainfId K) ((FCrys.unit l ↥(OL K)).tr ioH t) =
      inclW l (ainfId K (ioH.f t)) ⊗ₜ[ℤ_[l]] (1 : ℤ_[l]) := fun t => unitMap_apply _ _ _
  constructor
  · rintro ⟨x, rfl⟩
    choose t ht using fun i => full ioH BS H U (b.coord i) (fun g x => by rw [hρ]; rfl) x
    refine ⟨t, ?_⟩
    have key : ∀ y : WCb l ⊗[ℤ_[l]] T, y = ∑ i,
        (LinearMap.toSpanSingleton ℤ_[l] T (b i)).lTensor (WCb l) ((b.coord i).lTensor (WCb l) y) := fun y => by
      induction y with
      | tmul w t =>
        simp only [LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply, Module.Basis.coord_apply]
        rw [← TensorProduct.tmul_sum, b.sum_repr]
      | add y y' h h' =>
        simp only [map_add (f := _), Finset.sum_add_distrib]
        rw [← h, ← h']
    rw [key (j (E.tr ioH x))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ht]
    exact (congrArg _ (h2 (t i))).trans (h1 _ _)
  · rintro ⟨t, rfl⟩
    choose x hx using fun i => full ioH BS U H (LinearMap.toSpanSingleton ℤ_[l] T (b i))
      (fun g x => by rw [hρ]; rfl) (t i)
    refine ⟨∑ i, x i, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hx, h2, h1]

end Realisation

section Kappa

variable {Z O W RW T T' : Type} [CommRing Z] [CommRing O] [CommRing W] [CommRing RW] [Algebra Z W] [Algebra O RW]
  [AddCommGroup T] [Module Z T] [Module O T] [AddCommGroup T'] [Module Z T'] [Module O T'] (c : W →+* RW)

theorem kappa_smul (κ : W ⊗[Z] T ≃+ RW ⊗[O] T) (hκ : ∀ w t, κ (w ⊗ₜ t) = c w ⊗ₜ t) (w : W) (y : W ⊗[Z] T) :
    κ (w • y) = c w • κ y := by
  induction y with
  | tmul w' t => rw [TensorProduct.smul_tmul', hκ, hκ, TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
  | add y y' h h' => rw [smul_add, map_add (f := _), map_add (f := _), smul_add, h, h']

theorem kappa_map (κ : W ⊗[Z] T ≃+ RW ⊗[O] T) (hκ : ∀ w t, κ (w ⊗ₜ t) = c w ⊗ₜ t)
    (κ' : W ⊗[Z] T' ≃+ RW ⊗[O] T') (hκ' : ∀ w t, κ' (w ⊗ₜ t) = c w ⊗ₜ t)
    (σ : W →ₗ[Z] W) (σ' : RW →ₗ[O] RW) (hσ : ∀ w, σ' (c w) = c (σ w))
    (f : T →ₗ[Z] T') (f' : T →ₗ[O] T') (hf : ∀ t, f' t = f t) (y : W ⊗[Z] T) :
    κ' (TensorProduct.map σ f y) = TensorProduct.map σ' f' (κ y) := by
  induction y with
  | tmul w' t => rw [TensorProduct.map_tmul, hκ, hκ', TensorProduct.map_tmul, hσ, hf]
  | add y y' h h' => simp only [map_add (f := _), h, h']

theorem kappa_basis (κ : W ⊗[Z] T ≃+ RW ⊗[O] T) (hκ : ∀ w t, κ (w ⊗ₜ t) = c w ⊗ₜ t) {q : ℕ}
    (b : Module.Basis (Fin q) W (W ⊗[Z] T)) (y : RW ⊗[O] T) :
    ∃! w : Fin q → W, y = ∑ i, c (w i) • κ (b i) := by
  have key : ∀ w : Fin q → W, ∑ i, c (w i) • κ (b i) = κ (b.equivFun.symm w) := fun w => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [b.equivFun_symm_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => (kappa_smul c κ hκ _ _).symm
  refine ⟨b.equivFun (κ.symm y), by simp only [key]; simp, fun w hw => ?_⟩
  rw [hw, key, AddEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]


omit [Module Z T] in
theorem map_mulLeft (r : RW) (y : RW ⊗[O] T) :
    TensorProduct.map (LinearMap.mulLeft O r) (LinearMap.id : T →ₗ[O] T) y = r • y := by
  induction y with
  | tmul w' t => rw [TensorProduct.map_tmul, TensorProduct.smul_tmul']; rfl
  | add y y' h h' => rw [map_add (f := _), smul_add, h, h']

end Kappa

section Rings

variable {Z O W : Type} [CommRing Z] [CommRing O] [CommRing W] [Algebra Z O] [Algebra Z W]

theorem coord_tensor {d : ℕ} (o : Module.Basis (Fin d) Z O) (r : O ⊗[Z] W) :
    ∃! w : Fin d → W, r = ∑ j, o j • (Algebra.TensorProduct.includeRight : W →ₐ[Z] O ⊗[Z] W).toRingHom (w j) := by
  let b := o.baseChange W
  have key : ∀ w : Fin d → W,
      ∑ j, o j • (Algebra.TensorProduct.includeRight : W →ₐ[Z] O ⊗[Z] W).toRingHom (w j) =
        TensorProduct.comm Z W O (b.equivFun.symm w) := fun w => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [b.equivFun_symm_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [b, TensorProduct.smul_tmul']
  refine ⟨b.equivFun ((TensorProduct.comm Z W O).symm r), by simp only [key]; simp, fun w hw => ?_⟩
  rw [hw, key, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

theorem isUnit_of_one_tmul [Module.Free Z O] [Module.Finite Z O] [Nontrivial (O ⊗[Z] W)] (w : W)
    (h : IsUnit ((1 : O) ⊗ₜ[Z] w)) : IsUnit w := by
  have : Nontrivial (W ⊗[Z] O) := (TensorProduct.comm Z O W).injective.nontrivial
  have h1 : IsUnit (algebraMap W (W ⊗[Z] O) w) := h.map (Algebra.TensorProduct.comm Z O W)
  exact isUnit_of_map_unit _ _ h1

end Rings

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s} {R : WSer Γ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {I : WIo R RA RW inclR φR gR πA}

theorem coord_EE (I : WIo R RA RW inclR φR gR πA) {S W : Type} [CommRing S] [CommRing W]
    (a : S →+* LetA O n) (c : W →+* RW) (ψ : S →+* W) (π : S)
    (hψ : ∀ s, I.ioE (algebraMap _ R.EE (a s)) = c (ψ s)) (hπ : a π = letπ)
    (hcu : ∀ w, IsUnit (c w) → IsUnit w) (hW : IsAdicComplete (Ideal.span {((PD.p : ℕ) : W)}) W)
    {d : ℕ} (o : Fin d → O) (hRW : ∀ r : RW, ∃! w : Fin d → W, r = ∑ j, o j • c (w j))
    (hA : ∀ α : LetA O n, ∃ s : Fin d → S, α = ∑ j, o j • a (s j))
    (e : R.EE) : ∃ e' : Fin d → R.EE, (∀ j, I.ioE (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j := by
  refine GlobalTheory.T.exists_adic_coordinates_of_basis_mod_p PD.p _ R.EE W RW I.ioE c d o hRW R.EE_complete hW (fun e => ?_) e
  obtain ⟨α, m, h⟩ := R.EE_dense e 1
  obtain ⟨t, rfl⟩ := hA α
  obtain ⟨u, hu⟩ := R.EE_π
  have h1 : I.ioE u = c (ψ π) := by rw [hu, ← hπ, hψ]
  obtain ⟨w, hw⟩ : IsUnit (ψ π) := hcu _ (by rw [← h1]; exact u.isUnit.map I.ioE)
  have h2 : I.ioE ((u⁻¹ : R.EEˣ) : R.EE) = c ((w⁻¹ : Wˣ) : W) := by
    have h3 : I.ioE u * c ((w⁻¹ : Wˣ) : W) = 1 := by
      rw [h1, ← hw, ← map_mul, Units.mul_inv, map_one]
    rw [← mul_one (I.ioE _), ← h3, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  refine ⟨fun j => ((u⁻¹ : R.EEˣ) : R.EE) ^ m * algebraMap _ R.EE (a (t j)),
    fun j => ⟨((w⁻¹ : Wˣ) : W) ^ m * ψ (t j), by simp only [map_mul, map_pow, h2, hψ]⟩, ?_⟩
  rw [pow_one, map_pow, ← hu] at h
  convert Ideal.mul_mem_left _ (((u⁻¹ : R.EEˣ) : R.EE) ^ m) h using 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [mul_sub, mul_left_comm, ← mul_pow, Units.inv_mul, one_pow, mul_one, map_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_left_comm]

theorem card_basis {Z W : Type} [CommRing Z] [CommRing W] [Nontrivial Z] [Nontrivial W] [Nontrivial O] [Algebra Z O]
    [Algebra Z W] (T : LocLat G Qp LL O) {d q : ℕ} (o : Module.Basis (Fin d) Z O) :
    letI : Module Z ↥T.L.T := Module.compHom ↥T.L.T (algebraMap Z O)
    Module.Basis (Fin q) W (W ⊗[Z] ↥T.L.T) → q = d * Module.finrank O ↥T.L.T := by
  let _ : Module Z ↥T.L.T := Module.compHom ↥T.L.T (algebraMap Z O)
  intro b
  have := Module.Free.of_basis o
  have := T.L.free
  have : IsScalarTower Z O ↥T.L.T := ⟨fun z x t => by
    rw [Algebra.smul_def, mul_smul]; rfl⟩
  have : Module.Free Z ↥T.L.T := Module.Free.trans (S := O)
  have h1 := Module.finrank_eq_card_basis b
  rw [Module.finrank_baseChange, ← Module.finrank_mul_finrank Z O ↥T.L.T,
    Module.finrank_eq_card_basis o, Fintype.card_fin, Fintype.card_fin] at h1
  exact h1.symm

theorem one_basis {Z : Type} [CommRing Z] [Algebra Z O] (Γ : WGam PD LL O v n s)
    (hO : Function.Injective (algebraMap O LL)) {d : ℕ} (o : Module.Basis (Fin d) Z O) :
    letI : Module Z ↥Γ.one.L.T := Module.compHom ↥Γ.one.L.T (algebraMap Z O)
    ∃ (e₀ : ↥Γ.one.L.T) (b : Module.Basis (Fin d) Z ↥Γ.one.L.T),
      Submodule.span O {e₀} = ⊤ ∧ ∀ i, b i = o i • e₀ := by
  let _ : Module Z ↥Γ.one.L.T := Module.compHom ↥Γ.one.L.T (algebraMap Z O)
  obtain ⟨e, he, h⟩ := Γ.one_line
  let e₀ : ↥Γ.one.L.T := ⟨e, by rw [h]; exact Submodule.mem_span_singleton_self e⟩
  have hs : ∀ t : ↥Γ.one.L.T, ∃ x : O, x • e₀ = t := fun t => by
    have ht : (t : Γ.one.V) ∈ Submodule.span O {e} := h ▸ t.2
    obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.1 ht
    exact ⟨x, Subtype.ext hx⟩
  let f : O →ₗ[Z] ↥Γ.one.L.T :=
    { toFun := fun x => x • e₀
      map_add' := fun x y => add_smul x y e₀
      map_smul' := fun z x => by rw [Algebra.smul_def, mul_smul]; rfl }
  have hf : Function.Bijective f := by
    refine ⟨(injective_iff_map_eq_zero f).2 fun x hx => ?_, hs⟩
    have h1 : x • e = 0 := congrArg Subtype.val hx
    rw [← algebraMap_smul LL x e] at h1
    exact hO (((smul_eq_zero.1 h1).resolve_right he).trans (map_zero _).symm)
  exact ⟨e₀, o.map (LinearEquiv.ofBijective f hf),
    eq_top_iff.2 fun t _ => Submodule.mem_span_singleton.2 (hs t), fun i => rfl⟩

theorem exists_restrict {Z : Type} [CommRing Z] [Algebra Z O] {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) :
    letI : Module Z ↥T.L.T := Module.compHom ↥T.L.T (algebraMap Z O)
    letI : Module Z ↥T'.L.T := Module.compHom ↥T'.L.T (algebraMap Z O)
    ∃ f' : ↥T.L.T →ₗ[Z] ↥T'.L.T, (∀ t, (f.f.restrictScalars O).restrict f.T_le t = f' t) ∧
      ∀ g t, f' (T.actT g t) = T'.actT g (f' t) := by
  let _ : Module Z ↥T.L.T := Module.compHom ↥T.L.T (algebraMap Z O)
  let _ : Module Z ↥T'.L.T := Module.compHom ↥T'.L.T (algebraMap Z O)
  exact ⟨{ toFun := (f.f.restrictScalars O).restrict f.T_le
           map_add' := map_add _
           map_smul' := fun z x => ((f.f.restrictScalars O).restrict f.T_le).map_smul (algebraMap Z O z) x },
    fun _ => rfl, fun g t => Subtype.ext (f.equiv g t)⟩

theorem resΓ_eq_one (Γ : WGam PD LL O v n s) (hO : Function.Injective (algebraMap O LL)) (g : G)
    (hg : ((PD.χ g : Qpˣ) : Qp) = 1) : Γ.resΓ g = 1 := by
  apply Γ.χΓ_inj
  rw [map_one]
  apply Units.ext
  apply hO
  rw [Γ.χΓ_res g, hg, Units.val_one, map_one, map_one]

end Generic

theorem perfect_tilt {l : ℕ} [Fact l.Prime] : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  obtain ⟨a', rfl⟩ := surjective_frobenius (OCb l) l a
  obtain ⟨b', rfl⟩ := surjective_frobenius (OCb l) l b
  refine ⟨algebraMap _ _ a' / algebraMap _ _ b', ?_⟩
  simp [frobenius_def, div_pow]

theorem exists_basis_OL {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    ∃ d, Nonempty (Module.Basis (Fin d) ℤ_[l] ↥(OL LL)) := by
  have := LL.2
  have : Module.IsTorsionFree ℤ_[l] ↥LL.1 := Module.isTorsionFree_iff_algebraMap_injective.mpr (by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]
    exact (algebraMap ℚ_[l] ↥LL.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l]))
  have : Module.Free ℤ_[l] ↥(OL LL) :=
    IsIntegralClosure.module_free ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)
  have : Module.Finite ℤ_[l] ↥(OL LL) :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)
  exact ⟨_, ⟨Module.finBasis ℤ_[l] ↥(OL LL)⟩⟩

end GlobalTheory.WachLattice

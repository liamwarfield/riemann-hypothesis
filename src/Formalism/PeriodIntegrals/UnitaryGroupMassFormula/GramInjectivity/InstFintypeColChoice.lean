module

public import Formalism.PeriodIntegrals.UnimodGenus
public import Formalism.PeriodIntegrals.QuotInv

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramInjectivity.GramVanish
noncomputable section

namespace PI.WwInjectiveWork

open MvPolynomial

theorem gram_vanish {σ ι K : Type*} [Fintype ι] [Field K] [CharZero K]
    (f : ι → MvPolynomial σ ℤ) (ph : MvPolynomial σ K →ₗ[K] K)
    (h : ∑ i, ph (map (Int.castRingHom K) (f i)) • map (Int.castRingHom K) (f i) = 0)
    (i : ι) : ph (map (Int.castRingHom K) (f i)) = 0 := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : ι → MvPolynomial σ K, ∀ j, g j = map (Int.castRingHom K) (f j) :=
    ⟨_, fun _ => rfl⟩
  simp only [← hg] at h ⊢
  have key : ∀ l : Module.Dual ℚ K, ∀ j, l (ph (g j)) = 0 := by
    intro l
    have lin : ∀ (x : K) (n : ℤ), algebraMap ℚ K (l x) * (n : K) = algebraMap ℚ K (l (x * n)) := by
      intro x n
      rw [show x * (n : K) = n • x by rw [zsmul_eq_mul, mul_comm], map_zsmul, zsmul_eq_mul,
        map_mul, map_intCast, mul_comm]
    have hrel : ∑ j, algebraMap ℚ K (l (ph (g j))) • g j = 0 := by
      ext s
      have hs := congrArg (fun p => l (AddMonoidAlgebra.coeff p s)) h
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [coeff_sum, coeff_smul, smul_eq_mul, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_sum, map_zero] at hs
      have e : ∀ j, AddMonoidAlgebra.coeff (g j) s = ((AddMonoidAlgebra.coeff (f j) s : ℤ) : K) := fun j => by
        rw [hg, coeff_map, eq_intCast]
      rw [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      simp only [coeff_smul, smul_eq_mul]
      calc ∑ j, algebraMap ℚ K (l (ph (g j))) * AddMonoidAlgebra.coeff (g j) s
          = ∑ j, algebraMap ℚ K (l (ph (g j) * AddMonoidAlgebra.coeff (g j) s)) := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [e j, lin]
        _ = algebraMap ℚ K (∑ j, l (ph (g j) * AddMonoidAlgebra.coeff (g j) s)) := by rw [map_sum]
        _ = 0 := by rw [hs, map_zero]
    have hsum : ∑ j, l (ph (g j)) ^ 2 = 0 := by
      have h1 : l (ph (∑ j, algebraMap ℚ K (l (ph (g j))) • g j)) = 0 := by
        rw [hrel, map_zero, map_zero]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum] at h1
      rw [← h1]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul, smul_eq_mul, sq]
    intro j
    have hnn : ∀ k ∈ (Finset.univ : Finset ι), 0 ≤ l (ph (g k)) ^ 2 := fun k _ => sq_nonneg _
    have hj := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum j (Finset.mem_univ j)
    exact (pow_eq_zero_iff two_ne_zero).mp hj
  exact (Module.forall_dual_apply_eq_zero_iff ℚ (ph (g i))).mp (fun l => key l i)

end PI.WwInjectiveWork
end
end

noncomputable section

namespace PI.WwInjectiveWork

open MvPolynomial PI.WwInjective PI.WwInjective.KM

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)

noncomputable instance instFintypeColChoice : Fintype (ColChoice N nu) := by
  unfold ColChoice; infer_instance

theorem eval_map_nablaX {K : Type} [CommRing K] (J : ColChoice N nu)
    (pt : Lt × ℕ × Fin N → K) :
    eval pt (map (Int.castRingHom K) (nablaX N nu J)) = minY N nu J (fun s a i => pt (s, i, a)) := by
  unfold nablaX minY
  simp only [map_prod, RingHom.map_det]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  simp [Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem deX_eq_sum (hCB : PI.WwCauchyBinet.WwCauchyBinet) {K : Type} [CommRing K]
    (y : Lt → Fin N → ℕ → K) :
    DeX N nu y = ∑ J : ColChoice N nu, C (minY N nu J y) *
      map (Int.castRingHom K) (nablaX N nu J) := by
  have h := hCB Lt K N nu y
  have h' : (∑ᶠ J : ColChoice N nu, C (minY N nu J y) * map (Int.castRingHom K) (nablaX N nu J)) =
      ∑ J : ColChoice N nu, C (minY N nu J y) * map (Int.castRingHom K) (nablaX N nu J) :=
    finsum_eq_sum_of_fintype _
  rw [← h']
  exact h

theorem sum_smul_eq_zero (hCB : PI.WwCauchyBinet.WwCauchyBinet) (l : ℕ) [Fact l.Prime]
    (ph : Module.Dual ℂ_[l] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[l]))
    (hph : ∀ y, ph (DeX N nu y) = 0) :
    ∑ J : ColChoice N nu, ph (map (Int.castRingHom ℂ_[l]) (nablaX N nu J)) •
      map (Int.castRingHom ℂ_[l]) (nablaX N nu J) = 0 := by
  haveI : Infinite ℂ_[l] := Infinite.of_injective (Nat.cast : ℕ → ℂ_[l]) Nat.cast_injective
  apply MvPolynomial.funext
  intro x
  have hx := hph (fun s a i => x (s, i, a))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [deX_eq_sum N nu hCB, map_sum] at hx
  simp only [MvPolynomial.C_mul', map_smul, smul_eq_mul] at hx
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    eval_map_nablaX, map_zero]
  refine Eq.trans ?_ hx
  exact Finset.sum_congr rfl fun J _ => mul_comm _ _

theorem wwInjective_of (hCB : PI.WwCauchyBinet.WwCauchyBinet) : PI.WwInjective.WwInjective := by
  unfold PI.WwInjective.WwInjective
  intro Lt _ _ l _ N nu ph hph J
  exact gram_vanish (fun J => nablaX N nu J) ph (sum_smul_eq_zero N nu hCB l ph hph) J

end PI.WwInjectiveWork

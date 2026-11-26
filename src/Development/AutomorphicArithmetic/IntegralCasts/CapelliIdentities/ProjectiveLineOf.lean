module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProjectiveLineOf
noncomputable def UpperTheory.Reformulated.B.ProjectiveLineOf.P1 :
    Prop :=
    ∀ (k : Type) [inst : NontriviallyNormedField k] [LocallyCompactSpace k] [CharZero k] (n : ℕ) (γ : GL (Fin n) k),
      (↑γ : Matrix (Fin n) (Fin n) k).charpoly.Separable →
        ∀ (D : Set (GL (Fin n) k)),
          IsCompact D →
            ∃ (C : Set (GL (Fin n) k)),
              IsCompact C ∧ ∀ (x : GL (Fin n) k), x⁻¹ * γ * x ∈ D → ∃ (t : GL (Fin n) k), t * γ = γ * t ∧ ∃ y ∈ C, x = t * y

section

open Polynomial Matrix

private theorem charpoly_dvd_of_aeval {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (hA : A.charpoly.Separable) (p : k[X]) (hp : aeval A p = 0) : A.charpoly ∣ p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  let K := AlgebraicClosure k
  let f := algebraMap k K
  rw [← Polynomial.map_dvd_map' f]
  have hsep : (A.charpoly.map f).Separable := hA.map
  refine (IsAlgClosed.splits _).dvd_of_roots_le_roots hsep.ne_zero ?_
  rw [Multiset.le_iff_subset (nodup_roots hsep)]
  intro r hr
  have hr' : (A.map f).charpoly.IsRoot r := by
    rw [Matrix.charpoly_map]; exact isRoot_of_mem_roots hr
  rw [← Matrix.mem_spectrum_iff_isRoot_charpoly] at hr'
  have h1 := spectrum.subset_polynomial_aeval (A.map f) (p.map f) ⟨r, hr', rfl⟩
  have h2 : aeval (A.map f) (p.map f) = 0 := by
    have h3 : aeval ((Algebra.ofId k K).mapMatrix A) p = 0 := by
      rw [aeval_algHom_apply, hp, map_zero]
    rw [aeval_map_algebraMap]
    exact h3
  rw [mem_roots (Polynomial.map_ne_zero hp0)]
  by_contra hne
  rw [h2, spectrum.mem_iff, sub_zero] at h1
  exact h1 ((IsUnit.mk0 _ hne).map _)

private def krylov {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k) (v : Fin n → k) :
    Matrix (Fin n) (Fin n) k :=
  Matrix.of fun i j => ((A ^ (j : ℕ)) *ᵥ v) i

private theorem krylov_mulVec {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (v : Fin n → k) (p : k[X]) (hp : p.degree < n) :
    krylov A v *ᵥ (fun j => p.coeff j) = aeval A p *ᵥ v := by
  have h : aeval A p = ∑ j : Fin n, p.coeff j • A ^ (j : ℕ) := by
    conv_lhs => rw [← p.sum_C_mul_X_pow_eq, ← Polynomial.sum_fin _ (by simp) hp]
    simp [Algebra.smul_def]
  rw [h, Matrix.sum_mulVec]
  ext i
  simp [krylov, Matrix.mulVec, dotProduct, Finset.sum_apply, Finset.mul_sum, mul_comm, mul_left_comm,
    mul_assoc]

private theorem exists_krylov_det_ne_zero {k : Type} [Field k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (hA : A.charpoly.Separable) :
    ∃ v, (krylov A v).det ≠ 0 := by
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator k[X]
    (Module.AEval' (Matrix.toLin' A))
  obtain ⟨v, rfl⟩ := (Module.AEval'.of _).surjective x
  refine ⟨v, fun hdet => ?_⟩
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let p : k[X] := (degreeLTEquiv k n).symm c
  have hpdeg : p.degree < n := mem_degreeLT.mp ((degreeLTEquiv k n).symm c).2
  have hpc : (fun j : Fin n => p.coeff j) = c := (degreeLTEquiv k n).apply_symm_apply c
  have hlin : aeval (Matrix.toLin' A) p = Matrix.toLin' (aeval A p) :=
    aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)) A p
  have h1 : aeval A p *ᵥ v = 0 := by rw [← krylov_mulVec A v p hpdeg, hpc, hc]
  have h2 : p ∈ Module.annihilator k[X] (Module.AEval' (Matrix.toLin' A)) := by
    rw [← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply,
      ← Module.AEval.of_aeval_smul, Module.End.smul_def, hlin, Matrix.toLin'_apply, h1, map_zero]
  rw [Module.AEval.annihilator_eq_ker_aeval, RingHom.mem_ker, hlin, map_eq_zero_iff _ Matrix.toLin'.injective] at h2
  have h3 := charpoly_dvd_of_aeval A hA p h2
  have h4 : p = 0 := by
    refine eq_zero_of_dvd_of_degree_lt h3 ?_
    simpa [Matrix.charpoly_degree_eq_dim] using hpdeg
  apply hc0
  rw [← hpc, h4]
  rfl

private theorem mul_krylov {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (v : Fin n → k) :
    A * krylov A v = krylov A v *
      Matrix.of fun i j : Fin n => (X ^ ((j : ℕ) + 1) %ₘ A.charpoly).coeff i := by
  ext i j
  have hdeg : (X ^ ((j : ℕ) + 1) %ₘ A.charpoly).degree < n := by
    simpa [Matrix.charpoly_degree_eq_dim] using
      degree_modByMonic_lt (X ^ ((j : ℕ) + 1)) A.charpoly_monic
  have h := congrFun (krylov_mulVec A v _ hdeg) i
  rw [← Matrix.pow_eq_aeval_mod_charpoly, pow_succ' A, ← Matrix.mulVec_mulVec] at h
  exact h.symm

private theorem continuous_krylov {k : Type} [NontriviallyNormedField k] {n : ℕ} (v : Fin n → k) :
    Continuous fun δ : GL (Fin n) k => krylov (δ : Matrix (Fin n) (Fin n) k) v := by
  refine continuous_matrix fun i j => ?_
  exact (continuous_apply i).comp ((Units.continuous_val.pow _).matrix_mulVec continuous_const)

private theorem exists_compact_krylov {k : Type} [NontriviallyNormedField k] {n : ℕ}
    (v : Fin n → k) (S : Set (GL (Fin n) k)) (hS : IsCompact S)
    (h : ∀ δ ∈ S, (krylov (δ : Matrix (Fin n) (Fin n) k) v).det ≠ 0) :
    ∃ C : Set (GL (Fin n) k), IsCompact C ∧
      ∀ δ ∈ S, ∃ u ∈ C, (u : Matrix (Fin n) (Fin n) k) = krylov (δ : Matrix (Fin n) (Fin n) k) v := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let Φ : S → GL (Fin n) k := fun δ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (h δ.1 δ.2)
  have hval : ∀ δ : S, (Φ δ : Matrix (Fin n) (Fin n) k) =
      krylov (δ.1 : Matrix (Fin n) (Fin n) k) v := fun δ => rfl
  have hc : Continuous fun δ : S => krylov (δ.1 : Matrix (Fin n) (Fin n) k) v :=
    (continuous_krylov v).comp continuous_subtype_val
  have hΦ : Continuous Φ := by
    rw [Units.continuous_iff]
    refine ⟨hc, ?_⟩
    simp_rw [Matrix.coe_units_inv, hval, Matrix.inv_def, Ring.inverse_eq_inv']
    exact (hc.matrix_det.inv₀ fun δ => h δ.1 δ.2).smul hc.matrix_adjugate
  exact ⟨Set.range Φ, isCompact_range hΦ, fun δ hδ => ⟨Φ ⟨δ, hδ⟩, ⟨_, rfl⟩, rfl⟩⟩

private theorem isClosed_charpoly_eq {k : Type} [NontriviallyNormedField k] [CharZero k] {n : ℕ}
    (χ : k[X]) :
    IsClosed {δ : GL (Fin n) k | (δ : Matrix (Fin n) (Fin n) k).charpoly = χ} := by
  have h : {δ : GL (Fin n) k | (δ : Matrix (Fin n) (Fin n) k).charpoly = χ} =
      ⋂ r : k, {δ : GL (Fin n) k |
        (Matrix.scalar (Fin n) r - (δ : Matrix (Fin n) (Fin n) k)).det = χ.eval r} := by
    ext δ
    simp only [Set.mem_setOf_eq, Set.mem_iInter, ← Matrix.eval_charpoly]
    exact ⟨fun h r => by rw [h], Polynomial.funext⟩
  rw [h]
  exact isClosed_iInter fun r =>
    isClosed_eq (continuous_const.sub Units.continuous_val).matrix_det continuous_const

end

theorem UpperTheory.Reformulated.B.ProjectiveLineOf.p1_holds :
    UpperTheory.Reformulated.B.ProjectiveLineOf.P1 := by
  intro k _ _ _ n γ hγ D hD
  classical
  set χ := (γ : Matrix (Fin n) (Fin n) k).charpoly with hχ
  have hD' := hD.inter_right (isClosed_charpoly_eq (n := n) χ)
  let U : (Fin n → k) → Set (GL (Fin n) k) := fun v =>
    {δ | (krylov (δ : Matrix (Fin n) (Fin n) k) v).det ≠ 0}
  have hU : ∀ v, IsOpen (U v) := fun v =>
    isOpen_ne_fun (continuous_krylov v).matrix_det continuous_const
  obtain ⟨s, hs⟩ := hD'.elim_finite_subcover U hU (by
    rintro δ ⟨-, hδ⟩
    exact Set.mem_iUnion.mpr (exists_krylov_det_ne_zero _ (by rw [hδ]; exact hγ)))
  obtain ⟨S, hSc, hSU, hS⟩ := hD'.finite_compact_cover s U (fun v _ => hU v) hs
  choose C hCc hC using fun v => exists_compact_krylov v (S v) (hSc v) (hSU v)
  obtain ⟨v₀, hv₀⟩ := exists_krylov_det_ne_zero _ hγ
  let u₀ : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hv₀
  have hu₀ : (u₀ : Matrix (Fin n) (Fin n) k) = krylov (γ : Matrix (Fin n) (Fin n) k) v₀ := rfl
  refine ⟨⋃ v ∈ s, (fun u => u₀ * u⁻¹) '' C v,
    s.isCompact_biUnion fun v _ => (hCc v).image (by fun_prop), fun x hx => ?_⟩
  have hch : ((x⁻¹ * γ * x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly = χ := by
    rw [Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, mul_inv_cancel_left]
  have hmem : x⁻¹ * γ * x ∈ ⋃ v ∈ s, S v := hS ▸ ⟨hx, hch⟩
  obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hmem
  obtain ⟨u, huC, hu⟩ := hC v _ hxv
  have h1 := mul_krylov ((x⁻¹ * γ * x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) v
  have h2 := mul_krylov (γ : Matrix (Fin n) (Fin n) k) v₀
  rw [← hu, hch] at h1
  rw [← hu₀, ← hχ] at h2
  have h3 : u⁻¹ * (x⁻¹ * γ * x) * u = u₀⁻¹ * γ * u₀ := by
    apply Units.ext
    rw [mul_assoc, mul_assoc u₀⁻¹, Units.val_mul, Units.val_mul, h1, Units.val_mul,
      Units.val_mul, h2, Units.inv_mul_cancel_left, Units.inv_mul_cancel_left]
  refine ⟨x * u * u₀⁻¹, ?_, u₀ * u⁻¹, Set.mem_iUnion₂.mpr ⟨v, hv, u, huC, rfl⟩, by group⟩
  calc x * u * u₀⁻¹ * γ = x * u * (u₀⁻¹ * γ * u₀) * u₀⁻¹ := by group
    _ = γ * (x * u * u₀⁻¹) := by rw [← h3]; group
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GenericGradient
noncomputable def UpperTheory.Reformulated.B.Qf34.genericGradient :
    {n : ℕ} →
      (J : Ideal (MvPolynomial (Fin n) ℂ)) → MvPolynomial (Fin n) ℂ → Fin n → FractionRing (MvPolynomial (Fin n) ℂ ⧸ J) :=
    fun {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) (l : Fin n) ↦
      (Algebra.algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)) :
          MvPolynomial (Fin n) ℂ ⧸ J → FractionRing (MvPolynomial (Fin n) ℂ ⧸ J))
        ((Ideal.Quotient.mk J : MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ ⧸ J)
          ((MvPolynomial.pderiv l : MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ) f))

noncomputable def UpperTheory.Reformulated.B.Qf34.Statement :
    Prop :=
    ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] (ι : Type) [Fintype ι] (f : ι → MvPolynomial (Fin n) ℂ),
      (∀ (i : ι), f i ∈ J) →
        Submodule.span (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)) (Set.range (UpperTheory.Reformulated.B.Qf34.genericGradient J ∘ f)) =
            Submodule.span (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J))
              (UpperTheory.Reformulated.B.Qf34.genericGradient J '' (↑J : Set (MvPolynomial (Fin n) ℂ))) →
          ∃ s ∉ J, ∀ p ∈ J, s * p ∈ Ideal.span (Set.range f)

open MvPolynomial in
private theorem UpperTheory.Reformulated.B.Qf34.taylor {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]
    {n : ℕ} (φ ψ : MvPolynomial (Fin n) k →ₐ[k] B)
    (h : ∀ p q, (φ p - ψ p) * (φ q - ψ q) = 0) (p : MvPolynomial (Fin n) k) :
    φ p - ψ p = ∑ l, φ (pderiv l p) * (φ (X l) - ψ (X l)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algHom_C]
  | add p q hp hq =>
    simp only [map_add (f := _), add_mul, Finset.sum_add_distrib, ← hp, ← hq]
    ring
  | mul_X p i hp =>
    have e : ∀ l, φ (pderiv l (p * X i)) * (φ (X l) - ψ (X l)) =
        φ (X i) * (φ (pderiv l p) * (φ (X l) - ψ (X l))) +
          (if l = i then φ p * (φ (X i) - ψ (X i)) else 0) := by
      intro l
      rw [pderiv_mul, map_add (f := _), map_mul, map_mul]
      split_ifs with hl
      · subst hl
        rw [pderiv_X_self, map_one]
        ring
      · rw [pderiv_X_of_ne (Ne.symm hl), map_zero]
        ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, ← hp, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, map_mul]
    linear_combination - h p (X i)

open MvPolynomial in
private theorem UpperTheory.Reformulated.B.Qf34.sq_zero_case {k B K ι : Type*} [CommRing k] [CommRing B]
    [Algebra k B] [CommRing K] [Algebra k K] [Fintype ι] {n : ℕ}
    (π : B →ₐ[k] K) (σ : K →ₐ[k] B) (hσ : ∀ x, π (σ x) = x)
    (hsq : ∀ a b, π a = 0 → π b = 0 → a * b = 0)
    (φ : MvPolynomial (Fin n) k →ₐ[k] B) (p : MvPolynomial (Fin n) k)
    (f : ι → MvPolynomial (Fin n) k) (c : ι → K) (hp : π (φ p) = 0) (hf : ∀ i, π (φ (f i)) = 0)
    (hc : ∀ l, π (φ (pderiv l p)) = ∑ i, c i * π (φ (pderiv l (f i)))) :
    φ p = ∑ i, σ (c i) * φ (f i) := by
  have hd : ∀ q, π (φ q - (σ.comp (π.comp φ)) q) = 0 := by
    intro q
    simp [hσ]
  have ht := UpperTheory.Reformulated.B.Qf34.taylor φ (σ.comp (π.comp φ)) fun p q => hsq _ _ (hd p) (hd q)
  have ht' : ∀ q, π (φ q) = 0 →
      φ q = ∑ l, φ (pderiv l q) * (φ (X l) - (σ.comp (π.comp φ)) (X l)) := by
    intro q hq
    rw [← ht q]
    simp [hq]
  rw [ht' p hp, Finset.sum_congr rfl fun i _ => congrArg (σ (c i) * ·) (ht' _ (hf i))]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [← mul_assoc]
  rw [← Finset.sum_mul, ← sub_eq_zero, ← sub_mul]
  refine hsq _ _ ?_ (hd _)
  simp [hσ, hc]

open MvPolynomial in
private theorem UpperTheory.Reformulated.B.Qf34.mem_sup_sq {k A K ι : Type*} [CommRing k] [CommRing A]
    [Algebra k A] [CommRing K] [Algebra k K] [Algebra.FormallySmooth k K] [Fintype ι] {n : ℕ}
    (π : A →ₐ[k] K) (hπ : Function.Surjective π)
    (φ : MvPolynomial (Fin n) k →ₐ[k] A) (p : MvPolynomial (Fin n) k)
    (f : ι → MvPolynomial (Fin n) k) (c : ι → K) (hp : π (φ p) = 0) (hf : ∀ i, π (φ (f i)) = 0)
    (hc : ∀ l, π (φ (pderiv l p)) = ∑ i, c i * π (φ (pderiv l (f i)))) :
    φ p ∈ Ideal.span (Set.range fun i => φ (f i)) ⊔ RingHom.ker π * RingHom.ker π := by
  set m : Ideal A := RingHom.ker π with hm
  let π' : (A ⧸ m * m) →ₐ[k] K := Ideal.Quotient.liftₐ (m * m) π fun a ha => Ideal.mul_le_left ha
  have hπ' : ∀ a, π' (Ideal.Quotient.mk _ a) = π a := fun a => rfl
  have hs : Function.Surjective π' := fun x => by
    obtain ⟨a, rfl⟩ := hπ x
    exact ⟨_, hπ' a⟩
  have hsq : ∀ a b, π' a = 0 → π' b = 0 → a * b = 0 := by
    intro a b ha hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_mul ha hb
  have hn : IsNilpotent (RingHom.ker (π' : (A ⧸ m * m) →+* K)) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro a ha b hb
    exact hsq a b ha hb
  let σ := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k K) π' hs hn
  have hσ : ∀ x, π' (σ x) = x :=
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id k K) π' hs hn
  have key := UpperTheory.Reformulated.B.Qf34.sq_zero_case π' σ hσ hsq ((Ideal.Quotient.mkₐ k (m * m)).comp φ)
    p f c hp hf hc
  choose a ha using fun i => Ideal.Quotient.mk_surjective (I := m * m) (σ (c i))
  have h2 : φ p - ∑ i, a i * φ (f i) ∈ m * m := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Ideal.Quotient.eq, map_sum]
    simpa [← ha] using key
  rw [← add_sub_cancel (∑ i, a i * φ (f i)) (φ p)]
  refine Submodule.add_mem_sup (Ideal.sum_mem _ fun i _ => ?_) h2
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem UpperTheory.Reformulated.B.Qf34.proof :
    UpperTheory.Reformulated.B.Qf34.Statement := by
  intro n J _ ι _ f hf hspan
  let R := MvPolynomial (Fin n) ℂ
  let K := FractionRing (R ⧸ J)
  let A := Localization.AtPrime J
  let g : R →ₐ[ℂ] K := (IsScalarTower.toAlgHom ℂ (R ⧸ J) K).comp (Ideal.Quotient.mkₐ ℂ J)
  have hg : ∀ r, g r = algebraMap (R ⧸ J) K (Ideal.Quotient.mk J r) := fun r => rfl
  have hg0 : ∀ r, g r = 0 ↔ r ∈ J := fun r => by
    rw [hg, map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ J) K), Ideal.Quotient.eq_zero_iff_mem]
  have hu : ∀ y : J.primeCompl, IsUnit (g y) := fun y =>
    isUnit_iff_ne_zero.mpr fun h => y.2 ((hg0 _).mp h)
  let π : A →ₐ[ℂ] K := IsLocalization.liftAlgHom (M := J.primeCompl) hu
  let φ : R →ₐ[ℂ] A := IsScalarTower.toAlgHom ℂ R A
  have hπφ : ∀ r, π (φ r) = g r := fun r => IsLocalization.lift_eq hu r
  have hπ : Function.Surjective π := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (R ⧸ J) x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hb' : b ∈ J.primeCompl := fun h =>
      nonZeroDivisors.ne_zero hb (Ideal.Quotient.eq_zero_iff_mem.mpr h)
    refine ⟨IsLocalization.mk' A a ⟨b, hb'⟩, ?_⟩
    rw [← hg, ← hg, eq_div_iff (hu ⟨b, hb'⟩).ne_zero, ← hπφ, ← hπφ, ← map_mul]
    exact congrArg π (IsLocalization.mk'_spec A a ⟨b, hb'⟩)
  haveI : Algebra.EssFiniteType (R ⧸ J) K :=
    Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors (R ⧸ J))
  haveI : Algebra.EssFiniteType ℂ K := Algebra.EssFiniteType.comp ℂ (R ⧸ J) K
  haveI : Algebra.FormallySmooth ℂ K := Algebra.FormallySmooth.of_perfectField
  have hker : RingHom.ker π = IsLocalRing.maximalIdeal A :=
    IsLocalRing.ker_eq_maximalIdeal (π : A →+* K) hπ
  have hN : IsLocalRing.maximalIdeal A ≤ (Ideal.span (Set.range f)).map (algebraMap R A) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal A)
      (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    conv_lhs => rw [← Localization.AtPrime.map_eq_maximalIdeal]
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    have hmem : UpperTheory.Reformulated.B.Qf34.genericGradient J p ∈
        Submodule.span K (Set.range (UpperTheory.Reformulated.B.Qf34.genericGradient J ∘ f)) := by
      rw [hspan]
      exact Submodule.subset_span ⟨p, hp, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
    have := UpperTheory.Reformulated.B.Qf34.mem_sup_sq π hπ φ p f c (by rw [hπφ, hg0]; exact hp)
      (fun i => by rw [hπφ, hg0]; exact hf i) (fun l => by
        have h := congrFun hc l
        rw [Finset.sum_apply] at h
        simp only [hπφ]
        exact h.symm)
    rw [hker] at this
    rw [Ideal.mem_comap, Ideal.map_span, ← Set.range_comp, smul_eq_mul]
    exact this
  obtain ⟨t, ht⟩ : J.FG := IsNoetherian.noetherian J
  have hs : ∀ p ∈ J, ∃ s ∈ J.primeCompl, s * p ∈ Ideal.span (Set.range f) := by
    intro p hp
    rw [← IsLocalization.algebraMap_mem_map_algebraMap_iff J.primeCompl A]
    apply hN
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hp
  choose! s hs hs' using hs
  have htJ : ∀ p ∈ t, p ∈ J := fun p hp => ht ▸ Ideal.subset_span hp
  refine ⟨∏ p ∈ t, s p, Submonoid.prod_mem J.primeCompl fun p hp => hs p (htJ p hp), ?_⟩
  intro p hp
  rw [← ht] at hp
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem s hx
    rw [hu, mul_comm (s x), mul_assoc]
    exact Ideal.mul_mem_left _ _ (hs' x (htJ x hx))
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Ideal.add_mem _ hx hy
  | smul a x _ hx => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hx
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InverseOmegaHolds
noncomputable def UpperTheory.Reformulated.B.Gwa1.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.Gwa1.IsWq :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → WeierstrassCurve ℂ_[p] → PowerSeries ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) ↦
      have c : ℂ_[p] →+* PowerSeries ℂ_[p] := Algebra.algebraMap ℂ_[p] (PowerSeries ℂ_[p]);
      have X : PowerSeries ℂ_[p] := PowerSeries.X;
      wq =
        (1 : PowerSeries ℂ_[p]) + (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₁ * X * wq +
                (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₂ * X ^ (2 : ℕ) * wq +
              (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₃ * X ^ (3 : ℕ) * wq ^ (2 : ℕ) +
            (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₄ * X ^ (4 : ℕ) * wq ^ (2 : ℕ) +
          (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₆ * X ^ (6 : ℕ) * wq ^ (3 : ℕ)

noncomputable def UpperTheory.Reformulated.B.Gwa1.dX.{u_1} :
    {A : Type u_1} → [CommRing A] → PowerSeries A → PowerSeries A :=
    fun {A : Type u_1} [CommRing A] (f : PowerSeries A) ↦
      PowerSeries.mk fun (n : ℕ) ↦ ((↑n : A) + (1 : A)) * (PowerSeries.coeff (n + (1 : ℕ)) : PowerSeries A → A) f

noncomputable def UpperTheory.Reformulated.B.Gwa1.omegaW :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → WeierstrassCurve ℂ_[p] → PowerSeries ℂ_[p] → PowerSeries ℂ_[p] :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) ↦
      have c : ℂ_[p] →+* PowerSeries ℂ_[p] := Algebra.algebraMap ℂ_[p] (PowerSeries ℂ_[p]);
      have X : PowerSeries ℂ_[p] := PowerSeries.X;
      ((-2 : PowerSeries ℂ_[p]) * wq - X * UpperTheory.Reformulated.B.Gwa1.dX wq) *
        (wq *
            ((c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₁ * X + (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₃ * X ^ (3 : ℕ) * wq -
              (2 : PowerSeries ℂ_[p])))⁻¹

noncomputable def UpperTheory.Reformulated.B.Gwa1.flog :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → WeierstrassCurve ℂ_[p] → PowerSeries ℂ_[p] → PowerSeries ℂ_[p] :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) ↦
      PowerSeries.mk fun (n : ℕ) ↦
        if n = (0 : ℕ) then (0 : ℂ_[p])
        else (PowerSeries.coeff (n - (1 : ℕ)) : PowerSeries ℂ_[p] → ℂ_[p]) (UpperTheory.Reformulated.B.Gwa1.omegaW W wq) / (↑n : ℂ_[p])

noncomputable def UpperTheory.Reformulated.B.Gwa1.InvOmega :
    Prop :=
    ∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]),
      UpperTheory.Reformulated.B.Gwa1.IsIntP W.a₁ →
        UpperTheory.Reformulated.B.Gwa1.IsIntP W.a₂ →
          UpperTheory.Reformulated.B.Gwa1.IsIntP W.a₃ →
            UpperTheory.Reformulated.B.Gwa1.IsIntP W.a₄ →
              UpperTheory.Reformulated.B.Gwa1.IsIntP W.a₆ →
                UpperTheory.Reformulated.B.Gwa1.IsWq W wq →
                  ∃ (v : PowerSeries ℂ_[p]),
                    (∀ (n : ℕ), UpperTheory.Reformulated.B.Gwa1.IsIntP ((PowerSeries.coeff n : PowerSeries ℂ_[p] → ℂ_[p]) v)) ∧
                      v * UpperTheory.Reformulated.B.Gwa1.dX (UpperTheory.Reformulated.B.Gwa1.flog W wq) = (1 : PowerSeries ℂ_[p])

namespace UpperTheory.Reformulated.B.Gwa1

open PowerSeries

private def lowIn {R : Type*} [CommRing R] (O : Subring R) (n : ℕ) : Subring R⟦X⟧ where
  carrier := {f | ∀ k < n, coeff k f ∈ O}
  mul_mem' := by
    intro f g hf hg k hk
    rw [coeff_mul]
    refine O.sum_mem fun x hx => ?_
    have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    exact O.mul_mem (hf _ (by omega)) (hg _ (by omega))
  one_mem' := by
    intro k _
    rw [coeff_one]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  add_mem' := by
    intro f g hf hg k hk
    rw [map_add (f := _)]
    exact O.add_mem (hf k hk) (hg k hk)
  zero_mem' := by
    intro k _
    rw [map_zero]
    exact O.zero_mem
  neg_mem' := by
    intro f hf k hk
    rw [map_neg]
    exact O.neg_mem (hf k hk)

private theorem C_mem {R : Type*} [CommRing R] {O : Subring R} (n : ℕ) {a : R} (ha : a ∈ O) :
    (C a : R⟦X⟧) ∈ lowIn O n := by
  intro k _
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact O.zero_mem

private theorem X_mem {R : Type*} [CommRing R] (O : Subring R) (n : ℕ) :
    (X : R⟦X⟧) ∈ lowIn O n := by
  intro k _
  rw [coeff_X]
  split_ifs
  · exact O.one_mem
  · exact O.zero_mem

private theorem X_mul_mem {R : Type*} [CommRing R] {O : Subring R} {n : ℕ} {f : R⟦X⟧}
    (hf : f ∈ lowIn O n) : X * f ∈ lowIn O (n + 1) := by
  intro k hk
  cases k with
  | zero => rw [coeff_zero_X_mul]; exact O.zero_mem
  | succ k => rw [coeff_succ_X_mul]; exact hf k (by omega)

private theorem w_mem {R : Type*} [CommRing R] {O : Subring R} {a₁ a₂ a₃ a₄ a₆ : R}
    (h₁ : a₁ ∈ O) (h₂ : a₂ ∈ O) (h₃ : a₃ ∈ O) (h₄ : a₄ ∈ O) (h₆ : a₆ ∈ O) {w : R⟦X⟧}
    (hw : w = 1 + C a₁ * X * w + C a₂ * X ^ 2 * w + C a₃ * X ^ 3 * w ^ 2 + C a₄ * X ^ 4 * w ^ 2
      + C a₆ * X ^ 6 * w ^ 3) (n : ℕ) : w ∈ lowIn O n := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    have e : w = 1 + X * (C a₁ * w + C a₂ * X * w + C a₃ * X ^ 2 * w ^ 2 + C a₄ * X ^ 3 * w ^ 2
      + C a₆ * X ^ 5 * w ^ 3) := by linear_combination hw
    have hX := X_mem O n
    rw [e]
    exact add_mem (one_mem _) (X_mul_mem (add_mem (add_mem (add_mem (add_mem
      (mul_mem (C_mem n h₁) ih)
      (mul_mem (mul_mem (C_mem n h₂) hX) ih))
      (mul_mem (mul_mem (C_mem n h₃) (pow_mem hX _)) (pow_mem ih _)))
      (mul_mem (mul_mem (C_mem n h₄) (pow_mem hX _)) (pow_mem ih _)))
      (mul_mem (mul_mem (C_mem n h₆) (pow_mem hX _)) (pow_mem ih _))))

private theorem dX_eq {R : Type*} [CommRing R] (f : R⟦X⟧) : dX f = derivative f := by
  ext n
  rw [coeff_derivative, dX, coeff_mk, mul_comm]

private theorem key {R : Type*} [CommRing R] {a₁ a₂ a₃ a₄ a₆ : R} {w : R⟦X⟧}
    (hw : w = 1 + C a₁ * X * w + C a₂ * X ^ 2 * w + C a₃ * X ^ 3 * w ^ 2 + C a₄ * X ^ 4 * w ^ 2
      + C a₆ * X ^ 6 * w ^ 3) :
    (1 - C a₁ * X - C a₂ * X ^ 2 - 2 * (C a₃ * X ^ 3 * w) - 2 * (C a₄ * X ^ 4 * w)
      - 3 * (C a₆ * X ^ 6 * w ^ 2)) * (-2 * w - X * dX w)
      = w * (C a₁ * X + C a₃ * X ^ 3 * w - 2) := by
  have h := congrArg (derivative (R := R)) hw
  simp only [map_add (f := _), Derivation.leibniz, Derivation.leibniz_pow, derivative_C, derivative_X,
    Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul] at h
  rw [dX_eq]
  push_cast at h
  linear_combination (-X) * h

private noncomputable def ball (p : ℕ) [Fact (Nat.Prime p)] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro x y hx hy
    change ‖x * y‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy
  one_mem' := by
    change ‖(1 : ℂ_[p])‖ ≤ 1
    rw [norm_one]
  add_mem' := by
    intro x y hx hy
    exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  zero_mem' := by
    change ‖(0 : ℂ_[p])‖ ≤ 1
    rw [norm_zero]
    exact zero_le_one
  neg_mem' := by
    intro x hx
    change ‖-x‖ ≤ 1
    rw [norm_neg]
    exact hx

private theorem dX_flog {p : ℕ} [Fact (Nat.Prime p)] (W : WeierstrassCurve ℂ_[p])
    (w : ℂ_[p]⟦X⟧) : dX (flog W w) = omegaW W w := by
  ext n
  have hn : ((n : ℂ_[p]) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  rw [dX, coeff_mk, flog, coeff_mk, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel,
    Nat.cast_add_one, mul_div_cancel₀ _ hn]

end UpperTheory.Reformulated.B.Gwa1

open PowerSeries in
theorem UpperTheory.Reformulated.B.Gwa1.inverse_omega_holds :
    UpperTheory.Reformulated.B.Gwa1.InvOmega := by
  intro p _ W w h₁ h₂ h₃ h₄ h₆ hw
  have hw' : w = 1 + C W.a₁ * X * w + C W.a₂ * X ^ 2 * w + C W.a₃ * X ^ 3 * w ^ 2
      + C W.a₄ * X ^ 4 * w ^ 2 + C W.a₆ * X ^ 6 * w ^ 3 := hw
  refine ⟨1 - C W.a₁ * X - C W.a₂ * X ^ 2 - 2 * (C W.a₃ * X ^ 3 * w) - 2 * (C W.a₄ * X ^ 4 * w)
      - 3 * (C W.a₆ * X ^ 6 * w ^ 2), fun n => ?_, ?_⟩
  · have hX := X_mem (ball p) (n + 1)
    have ih := w_mem (O := ball p) h₁ h₂ h₃ h₄ h₆ hw' (n + 1)
    have c₁ := C_mem (O := ball p) (n + 1) h₁
    have c₂ := C_mem (O := ball p) (n + 1) h₂
    have c₃ := C_mem (O := ball p) (n + 1) h₃
    have c₄ := C_mem (O := ball p) (n + 1) h₄
    have c₆ := C_mem (O := ball p) (n + 1) h₆
    exact (sub_mem (sub_mem (sub_mem (sub_mem (sub_mem (one_mem _) (mul_mem c₁ hX))
      (mul_mem c₂ (pow_mem hX _)))
      (mul_mem (ofNat_mem _ 2) (mul_mem (mul_mem c₃ (pow_mem hX _)) ih)))
      (mul_mem (ofNat_mem _ 2) (mul_mem (mul_mem c₄ (pow_mem hX _)) ih)))
      (mul_mem (ofNat_mem _ 3) (mul_mem (mul_mem c₆ (pow_mem hX _)) (pow_mem ih _))) :
        _ ∈ lowIn (ball p) (n + 1)) n (Nat.lt_succ_self n)
  · have h0 : constantCoeff w = 1 := by
      have h := congrArg constantCoeff hw'
      simpa using h
    have hu : constantCoeff (w * (C W.a₁ * X + C W.a₃ * X ^ 3 * w - 2)) ≠ 0 := by
      simp [h0, map_ofNat]
    have ho : omegaW W w = (-2 * w - X * dX w) * (w * (C W.a₁ * X + C W.a₃ * X ^ 3 * w - 2))⁻¹ :=
      rfl
    rw [dX_flog, ho, ← mul_assoc, key hw']
    exact PowerSeries.mul_inv_cancel _ hu
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ContDiffHerm
namespace UpperTheory.Reformulated.B.Qj20

@[reducible] noncomputable def Mat (k r : ℕ) : Type :=
  Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

noncomputable def Hpk (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  fun i j =>
    if (i : ℕ) < r ∧ (i : ℕ) + (j : ℕ) = 2 * r + k then 1
    else if (j : ℕ) < r ∧ (i : ℕ) + (j : ℕ) = 2 * r + k then 1
    else if r ≤ (i : ℕ) ∧ (i : ℕ) ≤ r + k ∧ i = j then
      if (i : ℕ) = r + k then -1 else 1
    else 0

noncomputable def inLie (k r : ℕ) (X : Mat k r) : Prop :=
  X.conjTranspose * Hpk k r + Hpk k r * X = 0

theorem aux4 (n : ℕ) : IsTopologicalRing (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstance

noncomputable def RdV.{u_1} {n : ℕ} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (g : Matrix (Fin n) (Fin n) ℂ) : E :=
  letI : NormedSpace ℝ E := NormedSpace.complexToReal
  deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0

noncomputable def herm.{u_1} {ι : Type u_1} [Fintype ι] (H : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ :=
  star w ⬝ᵥ H.mulVec v

noncomputable def bvec {m : ℕ} (i : Fin m) : Fin m → ℂ :=
  Pi.single i 1

theorem aux8 (k r : ℕ) (a : Fin r) : (a : ℕ) < 2 * r + k + 1 := by
  have := a.isLt
  omega

noncomputable def eI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) :=
  ⟨a.val, aux8 k r a⟩

noncomputable def Top.{u_1} {n : ℕ} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → Matrix (Fin n) (Fin n) ℂ → E)
    (u : ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (g : Matrix (Fin n) (Fin n) ℂ) : E :=
  (if a = b then u • f g else 0) + Eop a b f g

noncomputable def qminorOp.{u_1} {n : ℕ} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {t : ℕ} (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → Matrix (Fin n) (Fin n) ℂ → E)
    (a b : Fin t → Fin n) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  ∑ σ : Equiv.Perm (Fin t),
    ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun k : Fin t => Top Eop (u - (k : ℂ)) (a (σ k)) (b k)).foldr
        (fun T h => T h) f

theorem aux12 : (1 + 1).AtLeastTwo :=
  ⟨by decide⟩

noncomputable def hpart1 {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Z - H⁻¹ * Z.conjTranspose * H)

noncomputable def hpart2 {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (1 / (2 * Complex.I) : ℂ) • (Z + H⁻¹ * Z.conjTranspose * H)

noncomputable def EabH.{u_1} {n : ℕ} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (g : Matrix (Fin n) (Fin n) ℂ) : E :=
  RdV (hpart1 H (Matrix.single a b 1)) f g +
    Complex.I • RdV (hpart2 H (Matrix.single a b 1)) f g

noncomputable def xR (k r m : ℕ) (h : m ≤ r) (l : Fin m) : Fin (2 * r + k + 1) :=
  eI k r (Fin.castLE h l)

noncomputable def AAop.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (k r m : ℕ) (hm : m ≤ r) (u : ℂ) (f : Mat k r → E) (g : Mat k r) : E :=
  ∑ c : Fin m → Fin (2 * r + k + 1),
    if StrictMono c then
      (Matrix.of fun a l : Fin m =>
        herm (Hpk k r) (g.mulVec (bvec (c l))) (bvec (eI k r (Fin.castLE hm a)))).det •
      qminorOp (EabH (Hpk k r)) (xR k r m hm) c u f g
    else 0

section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem Hpk_herm (k r : ℕ) : (Hpk k r).conjTranspose = Hpk k r := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Hpk, Fin.ext_iff]
  split_ifs <;> first | omega | simp

private theorem Hpk_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Matrix.mul_apply]
  obtain ⟨s, hs⟩ : ∃ s : Fin (2 * r + k + 1),
      (s : ℕ) = if r ≤ (i : ℕ) ∧ (i : ℕ) ≤ r + k then (i : ℕ) else 2 * r + k - i :=
    ⟨⟨if r ≤ (i : ℕ) ∧ (i : ℕ) ≤ r + k then (i : ℕ) else 2 * r + k - i,
      by split_ifs <;> omega⟩, rfl⟩
  rw [Finset.sum_eq_single s]
  · simp only [Hpk, Matrix.one_apply, Fin.ext_iff]
    split_ifs at hs <;> split_ifs <;> first | omega | simp
  · intro b _ hb
    have hb' : (b : ℕ) ≠ s := fun h => hb (Fin.ext h)
    have h0 : Hpk k r i b = 0 := by
      simp only [Hpk, Fin.ext_iff]
      split_ifs at hs <;> split_ifs <;> first | omega | rfl
    rw [h0, zero_mul]
  · simp

private theorem Hpk_inv (k r : ℕ) : (Hpk k r)⁻¹ = Hpk k r :=
  Matrix.inv_eq_right_inv (Hpk_sq k r)

private theorem inLie_hpart1 (k r : ℕ) (Z : Mat k r) : inLie k r (hpart1 (Hpk k r) Z) := by
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  simp only [inLie, hpart1, Hpk_inv, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Hpk_herm, h2,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Hpk_sq,
    Matrix.mul_one]
  rw [← Matrix.mul_assoc (Hpk k r) (Hpk k r), Hpk_sq, Matrix.one_mul, ← smul_add]
  simp

private theorem inLie_hpart2 (k r : ℕ) (Z : Mat k r) : inLie k r (hpart2 (Hpk k r) Z) := by
  have h2 : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp
  simp only [inLie, hpart2, Hpk_inv, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Hpk_herm, h2,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Hpk_sq,
    Matrix.mul_one]
  rw [← Matrix.mul_assoc (Hpk k r) (Hpk k r), Hpk_sq, Matrix.one_mul, neg_smul,
    add_comm (Hpk k r * Z), neg_add_cancel]

private theorem contDiff_entry {n : ℕ} (i j : Fin n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : Matrix (Fin n) (Fin n) ℂ => g i j) :=
  contDiff_apply_apply ℝ i j

private theorem contDiff_cst {n : ℕ} (c : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : Matrix (Fin n) (Fin n) ℂ => c) :=
  contDiff_const

private theorem contDiff_herm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun g : Matrix (Fin n) (Fin n) ℂ => herm H (g.mulVec v) w) := by
  simp only [herm, dotProduct, Matrix.mulVec]
  refine ContDiff.sum fun a _ => contDiff_const.mul ?_
  refine ContDiff.sum fun b _ => contDiff_const.mul ?_
  exact ContDiff.sum fun c _ => (contDiff_entry b c).mul contDiff_const

private theorem contDiff_det {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ → Fin m → Fin m → ℂ)
    (hA : ∀ a l, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => A g a l)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (Matrix.of (A g)).det) := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun l _ => hA _ _)

private theorem closed_sum {X E ι : Type*} [AddCommMonoid E] (P : (X → E) → Prop)
    (hadd : ∀ f₁ f₂, P f₁ → P f₂ → P fun x => f₁ x + f₂ x) (h0 : P fun _ => 0)
    (s : Finset ι) (F : ι → X → E) (hF : ∀ i, P (F i)) : P fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact hadd _ _ (hF a) ih

private theorem closed_foldr {Y : Type*} (P : Y → Prop) (f : Y) (hf : P f) (L : List (Y → Y))
    (hL : ∀ T ∈ L, ∀ y, P y → P (T y)) : P (L.foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact hf
  | cons T L ih =>
    exact hL T (List.mem_cons_self ..) _ (ih fun S hS => hL S (List.mem_cons_of_mem _ hS))

theorem aa_closed.{u_1} {k r : ℕ} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : (Mat k r → E) → Prop)
    (hR : ∀ (X : Mat k r) (f : Mat k r → E), inLie k r X → P f → P (RdV X f))
    (hadd : ∀ f₁ f₂ : Mat k r → E, P f₁ → P f₂ → P fun x => f₁ x + f₂ x)
    (hmul : ∀ φ : Mat k r → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      ∀ f : Mat k r → E, P f → P fun x => φ x • f x)
    (h0 : P fun _ => 0) (m : ℕ) (hm : m ≤ r) (u : ℂ) (f : Mat k r → E) (hf : P f) :
    P (AAop k r m hm u f) := by
  have hc : ∀ (c : ℂ) (f : Mat k r → E), P f → P fun x => c • f x :=
    fun c f hf => hmul (fun _ => c) (contDiff_cst c) f hf
  have hE : ∀ a b (f : Mat k r → E), P f → P (EabH (Hpk k r) a b f) := fun a b f hf =>
    hadd _ _ (hR _ f (inLie_hpart1 k r _) hf) (hc _ _ (hR _ f (inLie_hpart2 k r _) hf))
  have hT : ∀ (v : ℂ) a b (f : Mat k r → E), P f → P (Top (EabH (Hpk k r)) v a b f) := by
    intro v a b f hf
    refine hadd (fun g => if a = b then v • f g else 0) _ ?_ (hE a b f hf)
    by_cases hab : a = b
    · simp only [if_pos hab]; exact hc v f hf
    · simp only [if_neg hab]; exact h0
  have hQ : ∀ (a b : Fin m → Fin (2 * r + k + 1)),
      P (qminorOp (EabH (Hpk k r)) a b u f) := by
    intro a b
    unfold qminorOp
    rw [Finset.sum_fn]
    refine closed_sum P hadd h0 _ _ fun σ => ?_
    refine hc _ _ (closed_foldr P f hf _ fun T hTm => ?_)
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hTm
    exact hT _ _ _
  unfold AAop
  refine closed_sum P hadd h0 _ _ fun c => ?_
  by_cases hcm : StrictMono c
  · simp only [if_pos hcm]
    exact hmul _ (contDiff_det _ fun a l => contDiff_herm _ _ _) _ (hQ _ c)
  · simp only [if_neg hcm]
    exact h0

end

end UpperTheory.Reformulated.B.Qj20
end

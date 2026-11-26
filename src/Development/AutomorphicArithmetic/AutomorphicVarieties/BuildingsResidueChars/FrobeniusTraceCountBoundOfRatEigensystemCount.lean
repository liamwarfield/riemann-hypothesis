module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsNormVEqPrimePowLeFinrank
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.MultiCentre
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockEmbeddingFiniteAdelicGLCompatContinuous

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusTraceCountBoundOfRatEigensystemCount
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TracesFromEigenvaluesRank2
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.traces_from_eigenvalues_rank2 :
    ∀ (p h e : ℕ), ∀ D : EigData 2 p ![(e : ℤ), -(e : ℤ)] 0, ∃ (T : TrData (p ^ h) e) (u : D.S ≃ T.S), ∀ s, T.t (u s) = 1 + ((D.β s).map fun b => b⁻¹ ^ h).sum := by
  intro p h e D
  refine ⟨⟨D.S, D.fin, fun s => 1 + ((D.β s).map fun b => b⁻¹ ^ h).sum, ?_, ?_, ?_⟩, Equiv.refl _, fun s => rfl⟩
  · intro σ
    obtain ⟨u, hu⟩ := D.conj σ
    refine ⟨u, fun s => ?_⟩
    rw [hu, map_add (f := _), map_one, map_multiset_sum, Multiset.map_map, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp, map_pow, map_inv₀]
  · intro s
    obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.1 (D.card s)
    have hx : ‖x‖ = 1 := by simpa using D.pure s x (by rw [hxy]; simp)
    have hy : ‖y‖ = 1 := by simpa using D.pure s y (by rw [hxy]; simp)
    have e1 : ((D.β s).map fun b => b⁻¹ ^ h).sum = x⁻¹ ^ h + y⁻¹ ^ h := by
      rw [hxy]; simp
    have h1 : ‖x⁻¹ ^ h‖ = 1 := by simp [hx]
    have h2 : ‖y⁻¹ ^ h‖ = 1 := by simp [hy]
    rw [e1]
    have h3 := norm_add_le (1 : ℂ) (x⁻¹ ^ h + y⁻¹ ^ h)
    have h4 := norm_add_le (x⁻¹ ^ h) (y⁻¹ ^ h)
    rw [norm_one] at h3
    linarith
  · intro s
    obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.1 (D.card s)
    have hm : ∀ i, (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i ≤ (e : ℤ) := by
      intro i
      fin_cases i
      · simp
      · simp
    have hx := D.intInv e hm s x (by rw [hxy]; simp)
    have hy := D.intInv e hm s y (by rw [hxy]; simp)
    rw [zpow_natCast] at hx hy
    have e1 : ((D.β s).map fun b => b⁻¹ ^ h).sum = x⁻¹ ^ h + y⁻¹ ^ h := by
      rw [hxy]; simp
    have e2 : (((p ^ h : ℕ) : ℂ)) ^ e * (1 + (x⁻¹ ^ h + y⁻¹ ^ h)) =
        ((p ^ (h * e) : ℕ) : ℂ) + (((p : ℂ) ^ e * x⁻¹) ^ h + ((p : ℂ) ^ e * y⁻¹) ^ h) := by
      push_cast; ring
    rw [e1, e2]
    refine IsIntegral.add ?_ ((hx.pow h).add (hy.pow h))
    exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ((p ^ (h * e) : ℕ) : ℤ)))
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusTraceNormNonzeroLogBound
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinTraceDifferenceLogBound
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.eisenstein_trace_difference_log_bound :
    ∀ (q e k : ℕ), 7 ≤ q → 1 ≤ e → 0 < k → ∀ z t : ℂ, z ^ k = 1 → ‖t‖ ≤ 3 → IsIntegral ℤ ((q : ℂ) ^ e * t) → t ≠ eis3 q e z ∧ IsIntegral ℤ ((q : ℂ) ^ e * (t - eis3 q e z)) ∧ Real.log ‖(q : ℂ) ^ e * (t - eis3 q e z)‖ ≤ 2 * e * Real.log q + 1 := by
  intro q e k hq he hk z t hz ht hI
  have hzn : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz hk.ne'
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hzn
  have hQN : 7 ≤ q ^ e := le_trans hq (Nat.le_self_pow (by omega) q)
  have hlogQ : Real.log ((q ^ e : ℕ) : ℝ) = e * Real.log q := by
    rw [Nat.cast_pow, Real.log_pow]
  have hcast : (q : ℂ) ^ e = ((q ^ e : ℕ) : ℂ) := by push_cast; rfl
  unfold eis3
  rw [hcast] at hI ⊢
  generalize q ^ e = N at hQN hlogQ hI
  have hN : (7 : ℝ) ≤ N := by exact_mod_cast hQN
  have hN0 : (N : ℂ) ≠ 0 := by
    have : N ≠ 0 := by omega
    exact_mod_cast this
  have hexp : (N : ℂ) * (t - ((N : ℂ)⁻¹ * z + 1 + (N : ℂ) * z⁻¹)) =
      (N : ℂ) * t - z - N - (N : ℂ) * N * z⁻¹ := by
    field_simp
    ring
  have hnA : ‖(N : ℂ) * t - z - N‖ ≤ 4 * N + 1 := by
    have h1 : ‖(N : ℂ) * t‖ ≤ 3 * N := by
      rw [norm_mul, Complex.norm_natCast]
      nlinarith
    have h2 := norm_sub_le ((N : ℂ) * t - z) (N : ℂ)
    have h3 := norm_sub_le ((N : ℂ) * t) z
    rw [Complex.norm_natCast] at h2
    linarith
  have hnB : ‖(N : ℂ) * N * z⁻¹‖ = N * N := by
    simp [hzn]
  have hne : (N : ℂ) * t - z - N - (N : ℂ) * N * z⁻¹ ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h, hnB] at hnA
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hne
    rw [← hexp, ← h, sub_self, mul_zero]
  · rw [hexp]
    have hzI : IsIntegral ℤ z := IsIntegral.of_pow hk (by rw [hz]; exact isIntegral_one)
    have hzI' : IsIntegral ℤ z⁻¹ :=
      IsIntegral.of_pow hk (by rw [inv_pow, hz, inv_one]; exact isIntegral_one)
    have hNI : IsIntegral ℤ (N : ℂ) := by
      have := isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ))
      simpa using this
    exact ((hI.sub hzI).sub hNI).sub ((hNI.mul hNI).mul hzI')
  · rw [hexp]
    have hb : ‖(N : ℂ) * t - z - N - (N : ℂ) * N * z⁻¹‖ ≤ 2 * ((N : ℝ) * N) := by
      have := norm_sub_le ((N : ℂ) * t - z - N) ((N : ℂ) * N * z⁻¹)
      nlinarith
    have hNpos : (0 : ℝ) < N := by linarith
    have h1 := Real.log_le_log (norm_pos_iff.mpr hne) hb
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul hNpos.ne' hNpos.ne', hlogQ] at h1
    have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.frobenius_trace_norm_nonzero_log_bound :
    ∀ (q e : ℕ), 7 ≤ q → 1 ≤ e → ∀ (D : TrData q e) (Orb : Type) [Fintype Orb] (z : Orb → ℂ), (∀ o, ∃ k : ℕ, 0 < k ∧ z o ^ k = 1) → (∀ σ : ℂ ≃+* ℂ, ∃ u : Orb ≃ Orb, ∀ o, z (u o) = σ (z o)) → ∃ NN : ℤ, NN ≠ 0 ∧ Real.log |(NN : ℝ)| ≤ Fintype.card Orb * Nat.card D.S * (2 * e * Real.log q + 1) ∧ ∀ (l : ℕ) [Fact l.Prime], ¬ l ∣ q → ∀ (ι : Qbar l ≃+* ℂ) (Γ : Type) [Group Γ] (g : Γ) (admitted : (Γ →* GL (Fin 3) (Qbar l)) → Prop), D.Classifies ι g admitted → ∀ X : Orb → Finset (Γ →* GL (Fin 3) (Qbar l)), (∀ o, ∀ ρ ∈ X o, admitted ρ) → (∀ o, ∀ ρ ∈ X o, ∀ ρ' ∈ X o, RepIso ρ ρ' → ρ = ρ') → (∀ o, ∀ ρ ∈ X o, (ρ g : Matrix (Fin 3) (Fin 3) (Qbar l)).trace ≠ ι.symm (eis3 q e (z o))) ∧ ‖((NN : ℤ) : Qbar l)‖ ≤ ∏ o, ∏ ρ ∈ X o, ‖(ρ g : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - ι.symm (eis3 q e (z o))‖ := by
  intro q e hq he D Orb _ z hz hσ
  classical
  have := D.fin
  letI : Fintype D.S := Fintype.ofFinite D.S
  let f : Orb → D.S → ℂ := fun o s => (q : ℂ) ^ e * (D.t s - eis3 q e (z o))
  have key : ∀ o s, D.t s ≠ eis3 q e (z o) ∧ IsIntegral ℤ (f o s) ∧
      Real.log ‖f o s‖ ≤ 2 * e * Real.log q + 1 := by
    intro o s
    obtain ⟨k, hk, hzk⟩ := hz o
    exact UpperTheory.eisenstein_trace_difference_log_bound q e k hq he hk (z o) (D.t s) hzk (D.bd s) (D.int s)
  have hq0 : (q : ℂ) ≠ 0 := by
    have : q ≠ 0 := by omega
    exact_mod_cast this
  have hf0 : ∀ o s, f o s ≠ 0 := fun o s =>
    mul_ne_zero (pow_ne_zero _ hq0) (sub_ne_zero.2 (key o s).1)
  obtain ⟨n, hn⟩ := UpperTheory.exists_int_eq_prod_of_galois_permuted_integral (Orb × D.S) (fun p => f p.1 p.2) (fun p => (key p.1 p.2).2.1) (by
    intro σ
    obtain ⟨u, hu⟩ := hσ σ
    obtain ⟨v, hv⟩ := D.conj σ
    refine ⟨u.prodCongr v, fun p => ?_⟩
    simp [f, eis3, hu, hv])
  refine ⟨n, ?_, ?_, ?_⟩
  · intro h
    rw [h, Int.cast_zero] at hn
    exact Finset.prod_ne_zero_iff.2 (fun p _ => hf0 p.1 p.2) hn.symm
  · have h1 : |(n : ℝ)| = ∏ p : Orb × D.S, ‖f p.1 p.2‖ := by
      rw [← norm_prod, ← hn, Complex.norm_intCast]
    rw [h1, Real.log_prod (fun p _ => norm_ne_zero_iff.2 (hf0 p.1 p.2))]
    refine (Finset.sum_le_sum (fun p _ => (key p.1 p.2).2.2)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Nat.card_eq_fintype_card, nsmul_eq_mul]
    push_cast
    exact le_rfl
  · intro l _ hl ι Γ _ g admitted hcl X hX hinj
    obtain ⟨cl, hc1, hc2⟩ := hcl
    refine ⟨fun o ρ hρ h => ?_, ?_⟩
    · rw [hc2 ⟨ρ, hX o ρ hρ⟩] at h
      exact (key o _).1 (ι.symm.injective h)
    · have hq1 : ‖(q : Qbar l)‖ = 1 := by
        rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
        exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hl
      have h2 := UpperTheory.adicNorm_prod_le_prod_of_injective_classes l ι Orb D.S _ f (fun o s => (key o s).2.1) X
        (fun o r => cl ⟨r.1, hX o r.1 r.2⟩)
        (fun o r r' h => Subtype.ext (hinj o _ r.2 _ r'.2 (hc1 _ _ h)))
      rw [← Fintype.prod_prod_type', ← hn, map_intCast] at h2
      refine h2.trans (le_of_eq (Finset.prod_congr rfl fun o _ => ?_))
      rw [← Finset.prod_coe_sort (X o)]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [hc2 ⟨r.1, hX o r.1 r.2⟩]
      simp only [f, map_mul, map_pow, map_natCast, map_sub, norm_mul, norm_pow, hq1, one_pow, one_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CenterUActionMemAdjoinCapOp
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.centerU_action_mem_adjoin_capOp :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι), ∀ z ∈ (isExpLieAlgebra K n).centerU, uAction z ∈ Algebra.adjoin ℂ {x | ∃ τ u, x = capOp D n τ u} := by
  intro K _ _ n ι _ D z hz
  obtain ⟨hrel, hcomm⟩ := UpperTheory.gen_glRelations_and_commute_of_isLie (mixedSpace K) ι n _ D (lam K n) (isLie_lam K n)
  have h1 : ∀ u : UEnv K n,
      uAction u ∈ Algebra.adjoin ℂ {x | ∃ τ i j, x = gen D (lam K n) τ i j} := by
    intro u
    induction u using UEnv.induction with
    | halg r =>
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply ℝ ℂ]
      exact Subalgebra.algebraMap_mem _ _
    | hι Y =>
      obtain ⟨X, rfl⟩ := (toLie K n).surjective Y
      rw [← lam_apply, UpperTheory.lieMap_eq_sum_idempotent_gen (mixedSpace K) ι n _ D (lam K n) X]
      exact sum_mem fun τ _ => sum_mem fun i _ => sum_mem fun j _ =>
        Subalgebra.smul_mem _ (Algebra.subset_adjoin (by exact ⟨τ, i, j, rfl⟩)) _
    | hmul x y hx hy => rw [map_mul]; exact mul_mem hx hy
    | hadd x y hx hy => rw [map_add]; exact add_mem hx hy
  refine UpperTheory.V.Fb.multiCentre (gen D (lam K n)) hrel hcomm (h1 z) fun τ i j => ?_
  have h2 := gen_mem D (lam K n) τ i j
    (Subalgebra.toSubmodule (Subalgebra.centralizer ℂ {uAction z})) fun x => by
      rintro _ rfl
      rw [lam_apply, ← map_mul, ← map_mul, Subalgebra.mem_center_iff.1 hz]
  exact (h2 _ rfl).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.QdetGeneratesUniversalEnvelopingCentre
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem qdet_mem' {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (S : Subalgebra ℂ A) (X : Fin n → Fin n → A)
    (h : ∀ a b, X a b ∈ S) (u : ℂ) : Formalism.REAL.qdet X u ∈ S := by
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (h _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

private theorem aux {R : Type} [CommRing R] [Algebra ℝ R] {ι : Type} [Fintype ι] {n : ℕ} {A : Type} [Ring A]
    [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] {B : Type} [Ring B] [Algebra ℝ B] (D : Idem R ι)
    (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] B) (hl : ∀ X Y, l X * l Y - l Y * l X = l (X * Y - Y * X))
    (htop : Algebra.adjoin ℝ (Set.range l) = ⊤) (ρ : B →ₐ[ℝ] A) (τ : ι) (u : ℂ) :
    Formalism.REAL.qdet (gen D (ρ.toLinearMap ∘ₗ l) τ) u ∈
      Submodule.span ℂ (ρ '' (Subalgebra.center ℝ B : Set B)) := by
  let j : B →ₐ[ℝ] ℂ ⊗[ℝ] B := Algebra.TensorProduct.includeRight
  let ψ : ℂ ⊗[ℝ] B →ₐ[ℂ] A := Algebra.TensorProduct.lift (Algebra.ofId ℂ A) ρ fun c x => Algebra.commutes c (ρ x)
  have hψ : ∀ c x, ψ (c ⊗ₜ x) = c • ρ x := fun c x =>
    (Algebra.TensorProduct.lift_tmul _ _ _ c x).trans (Algebra.smul_def c (ρ x)).symm
  let l' : Matrix (Fin n) (Fin n) R →ₗ[ℝ] ℂ ⊗[ℝ] B := j.toLinearMap ∘ₗ l
  have hl' : IsLie l' := fun X Y => by
    change j (l X) * j (l Y) - j (l Y) * j (l X) = j (l (X * Y - Y * X))
    rw [← hl, map_sub, map_mul, map_mul]
  obtain ⟨hrel, hc⟩ := UpperTheory.gen_glRelations_and_commute_of_isLie R ι n _ D l' hl'
  set w := Formalism.REAL.qdet (gen D l' τ) u with hw
  have h0 : ∀ σ a b, gen D l' σ a b ∈ Subalgebra.centralizer ℂ {w} := fun σ a b => by
    rintro _ rfl
    by_cases e : σ = τ
    · subst e
      exact (Formalism.REAL.qDetCentral _ n _ (hrel σ) u a b)
    · refine (qdet_mem' (Subalgebra.centralizer ℂ {gen D l' σ a b}) _ (fun c d => ?_) u _ rfl).symm
      rintro _ rfl
      exact hc σ τ e a b c d
  have h1 : ∀ x : B, j x * w = w * j x := fun x => by
    have : Algebra.adjoin ℝ (Set.range l) ≤ (Subalgebra.centralizer ℝ {w}).comap j := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨X, rfl⟩
      have h2 : l' X ∈ Subalgebra.centralizer ℂ {w} := by
        rw [UpperTheory.lieMap_eq_sum_idempotent_gen R ι n _ D l' X]
        exact sum_mem fun σ _ => sum_mem fun a _ => sum_mem fun b _ => Subalgebra.smul_mem _ (h0 σ a b) _
      exact h2
    exact (this (htop ▸ Algebra.mem_top) w rfl).symm
  obtain ⟨p, hp, q, hq, e⟩ := UpperTheory.V.Fb.exists_re_im w h1
  have h2 : ψ w = Formalism.REAL.qdet (gen D (ρ.toLinearMap ∘ₗ l) τ) u := by
    rw [hw, UpperTheory.V.Fb.map_qdet]
    congr 1
    funext a b
    exact gen_inter D l' (ρ.toLinearMap ∘ₗ l) τ a b a b ψ.toLinearMap LinearMap.id fun x =>
      (hψ 1 _).trans (one_smul _ _)
  rw [← h2, e, map_add (f := _), hψ, hψ]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, hp, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, hq, rfl⟩))

theorem UpperTheory.qdet_generates_universalEnveloping_centre :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι) (τ : ι) (u : ℂ), capOp D n τ u ∈ Zc K n := by
  intro K _ _ n ι _ D τ u
  let l : Matrix (Fin n) (Fin n) (mixedSpace K) →ₗ[ℝ] UEnv K n :=
    (UniversalEnvelopingAlgebra.ι ℝ (L := (isExpLieAlgebra K n).lieSubalgebra)).toLinearMap ∘ₗ (toLie K n).toLinearMap
  have hl : ∀ X Y, l X * l Y - l Y * l X = l (X * Y - Y * X) := fun X Y => by
    change UniversalEnvelopingAlgebra.ι ℝ (toLie K n X) * UniversalEnvelopingAlgebra.ι ℝ (toLie K n Y) -
      UniversalEnvelopingAlgebra.ι ℝ (toLie K n Y) * UniversalEnvelopingAlgebra.ι ℝ (toLie K n X) =
      UniversalEnvelopingAlgebra.ι ℝ (toLie K n (X * Y - Y * X))
    rw [← Ring.lie_def, ← LieHom.map_lie]
    rfl
  have htop : Algebra.adjoin ℝ (Set.range l) = ⊤ := by
    refine eq_top_iff.2 fun z hz => ?_
    clear hz
    induction z using UEnv.induction with
    | halg r => exact Subalgebra.algebraMap_mem _ r
    | hι X => exact Algebra.subset_adjoin ⟨(toLie K n).symm X, by simp [l]⟩
    | hmul a b ha hb => exact mul_mem ha hb
    | hadd a b ha hb => exact add_mem ha hb
  have h := aux D l hl htop (uAction (K := K) (n := n)) τ u
  exact Algebra.span_le_adjoin ℂ _ h
end

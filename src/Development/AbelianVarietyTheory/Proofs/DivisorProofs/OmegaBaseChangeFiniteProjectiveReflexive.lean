module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperLiftTraitOfGenericLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIteratedDerivHilbertEisensteinSplitLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeFiniteProjectiveReflexive
noncomputable section

open TensorProduct

namespace GlobalTheory

section AdicAux

variable {S : Type*} [CommRing S] (a : S)

theorem mem_span_singleton_pow_smul_top_iff_exists {N : Type*} [AddCommGroup N] [Module S N] (n : ℕ)
    (x : N) : x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule S N) ↔ ∃ y : N, x = a ^ n • y := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  exact exists_congr fun v => by simp [eq_comm]

theorem isAdicComplete_fin_pi [IsAdicComplete (Ideal.span {a}) S] (k : ℕ) :
    IsAdicComplete (Ideal.span {a}) (Fin k → S) := by
  refine { haus' := ?_, toIsPrecomplete := ⟨?_⟩ }
  · intro x hx
    funext i
    refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {a}) S) (x i) fun n => ?_
    have h := hx n
    rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h ⊢
    obtain ⟨y, hy⟩ := h
    exact ⟨y i, by simpa using congrFun hy i⟩
  · intro f hf
    have key : ∀ i, ∃ L : S, ∀ n,
        f n i ≡ L [SMOD (Ideal.span {a} ^ n • ⊤ : Submodule S S)] := fun i =>
      IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {a}) S) fun {m n} hmn => by
        have h := hf hmn
        rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h ⊢
        obtain ⟨y, hy⟩ := h
        exact ⟨y i, by simpa using congrFun hy i⟩
    choose L hL using key
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists]
    have h := fun i => (mem_span_singleton_pow_smul_top_iff_exists a n _).1 (SModEq.sub_mem.1 (hL i n))
    choose y hy using h
    exact ⟨y, funext fun i => by simpa using hy i⟩

theorem isAdicComplete_of_retraction {N F : Type*} [AddCommGroup N] [Module S N]
    [AddCommGroup F] [Module S F] [IsAdicComplete (Ideal.span {a}) F] (i : N →ₗ[S] F)
    (r : F →ₗ[S] N) (h : r ∘ₗ i = LinearMap.id) : IsAdicComplete (Ideal.span {a}) N := by
  refine { haus' := ?_, toIsPrecomplete := ⟨?_⟩ }
  · intro x hx
    have h1 : i x = 0 := IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {a}) F) (i x) fun n => by
      have h2 := hx n
      rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h2 ⊢
      obtain ⟨y, hy⟩ := h2
      rw [sub_zero] at hy ⊢
      exact ⟨i y, by rw [hy, map_smul]⟩
    have h3 := LinearMap.congr_fun h x
    rw [LinearMap.comp_apply, h1, map_zero, LinearMap.id_apply] at h3
    exact h3.symm
  · intro f hf
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (f := fun n => i (f n))
      (inferInstance : IsPrecomplete (Ideal.span {a}) F) fun {m n} hmn => by
        have h2 := hf hmn
        rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h2 ⊢
        obtain ⟨y, hy⟩ := h2
        exact ⟨i y, by rw [← map_sub, hy, map_smul]⟩
    refine ⟨r L, fun n => ?_⟩
    have h2 := hL n
    rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h2 ⊢
    obtain ⟨y, hy⟩ := h2
    refine ⟨r y, ?_⟩
    have h3 := LinearMap.congr_fun h (f n)
    rw [LinearMap.comp_apply, LinearMap.id_apply] at h3
    rw [← map_smul, ← hy, map_sub, h3]

theorem isAdicComplete_of_finite_projective [IsAdicComplete (Ideal.span {a}) S] (N : Type*)
    [AddCommGroup N] [Module S N] [Module.Finite S N] [Module.Projective S N] :
    IsAdicComplete (Ideal.span {a}) N := by
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' S N
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  haveI := isAdicComplete_fin_pi a k
  exact isAdicComplete_of_retraction a s f hs

end AdicAux

namespace PDivGroup

open PDiv Coalgebra Bialgebra

variable {p : ℕ} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : PDivGroup p R)

variable {M : Type} [AddCommGroup M] [Module R M] (c : M →ₗ[R] G.omega)

end PDivGroup

end GlobalTheory

namespace GlobalTheory

namespace PDivGroup

open PDiv

end PDivGroup

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianIff
open IsLocalRing Polynomial

namespace GlobalTheory.StrictHensel

theorem henselian_of_sections {R : Type} [CommRing R] [IsLocalRing R]
    (H : ∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime],
      q.comap (algebraMap R A) = maximalIdeal R →
        ∃ s : A →ₐ[R] R, (maximalIdeal R).comap s.toRingHom = q) :
    HenselianLocalRing R := by
  refine ⟨fun f hf a₀ h₁ h₂ => ?_⟩
  let P : StandardEtalePair R := ⟨f, hf, derivative f, 1, 0, 1, by simp⟩
  have e : ∀ p : R[X], aeval (residue R a₀) p = residue R (p.eval a₀) := fun p => by
    rw [← ResidueField.algebraMap_eq]; exact aeval_algebraMap_apply_eq_algebraMap_eval _ _
  have hP : P.HasMap (residue R a₀) := by
    refine ⟨?_, ?_⟩
    · change aeval (residue R a₀) f = 0
      rw [e]; exact (residue_eq_zero_iff _).mpr h₁
    · change IsUnit (aeval (residue R a₀) (derivative f))
      rw [e]; exact h₂.map (residue R)
  let ψ := P.lift (residue R a₀) hP
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have hq : (RingHom.ker ψ).comap (algebraMap R P.Ring) = maximalIdeal R := by
    ext r
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, ResidueField.algebraMap_eq,
      residue_eq_zero_iff]
  obtain ⟨s, hs⟩ := H P.Ring (RingHom.ker ψ) hq
  refine ⟨s P.X, ?_, ?_⟩
  · have h := (P.hasMap_X.map s).1
    simpa [P, IsRoot, coe_aeval_eq_eval] using h
  · have hmem : P.X - algebraMap R P.Ring a₀ ∈ RingHom.ker ψ := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, ResidueField.algebraMap_eq]
      simp [ψ]
    rw [← hs, Ideal.mem_comap] at hmem
    simpa using hmem

theorem isSepClosed_of_sections {R : Type} [CommRing R] [IsLocalRing R]
    (H : ∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime],
      q.comap (algebraMap R A) = maximalIdeal R →
        ∃ s : A →ₐ[R] R, (maximalIdeal R).comap s.toRingHom = q) :
    IsSepClosed (ResidueField R) := by
  refine IsSepClosed.of_exists_root _ fun g hm hirr hsep => ?_
  obtain ⟨f, hf, -, hfm⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts g).2 (map_surjective _ residue_surjective g)) hm
  haveI : Fact (Irreducible g) := ⟨hirr⟩
  let P : StandardEtalePair R := ⟨f, hfm, derivative f, 1, 0, 1, by simp⟩
  have e : ∀ p : R[X], aeval (AdjoinRoot.root g) p =
      AdjoinRoot.mk g (p.map (residue R)) := fun p => by
    rw [← AdjoinRoot.aeval_eq, ← ResidueField.algebraMap_eq, aeval_map_algebraMap]
  have hP : P.HasMap (AdjoinRoot.root g) := by
    refine ⟨?_, ?_⟩
    · change aeval (AdjoinRoot.root g) f = 0
      rw [e, hf, AdjoinRoot.mk_self]
    · change IsUnit (aeval (AdjoinRoot.root g) (derivative f))
      rw [e, ← derivative_map, hf, isUnit_iff_ne_zero, Ne, AdjoinRoot.mk_eq_zero]
      rintro ⟨c, hc⟩
      obtain ⟨a, b, hab⟩ := hsep
      exact hirr.not_isUnit (isUnit_of_dvd_one ⟨a + b * c, by rw [← hab, hc]; ring⟩)
  let ψ := P.lift (AdjoinRoot.root g) hP
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have hq : (RingHom.ker ψ).comap (algebraMap R P.Ring) = maximalIdeal R := by
    ext r
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply R (ResidueField R) (AdjoinRoot g),
      map_eq_zero_iff _ (algebraMap (ResidueField R) (AdjoinRoot g)).injective,
      ResidueField.algebraMap_eq, residue_eq_zero_iff]
  obtain ⟨s, -⟩ := H P.Ring (RingHom.ker ψ) hq
  have ha : f.eval (s P.X) = 0 := by
    have h := (P.hasMap_X.map s).1
    simpa [P, coe_aeval_eq_eval] using h
  exact ⟨residue R (s P.X), by rw [← hf, eval_map, eval₂_hom, ha, map_zero]⟩

end GlobalTheory.StrictHensel

namespace GlobalTheory.StrictHensel

theorem sections_of_henselian_sepClosed {R : Type} [CommRing R] [IsLocalRing R]
    [HenselianLocalRing R] [IsSepClosed (ResidueField R)]
    (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime]
    (hq : q.comap (algebraMap R A) = maximalIdeal R) :
    ∃ s : A →ₐ[R] R, (maximalIdeal R).comap s.toRingHom = q := by
  let S := Localization.AtPrime q
  haveI : IsLocalHom (algebraMap R S) := ⟨fun r hr => by
    rw [IsScalarTower.algebraMap_apply R A S, IsLocalization.AtPrime.isUnit_to_map_iff S q] at hr
    exact (notMem_maximalIdeal).mp fun h => hr (by
      have : r ∈ q.comap (algebraMap R A) := hq ▸ h
      exact this)⟩
  haveI : Algebra.FormallyUnramified R S := Algebra.FormallyUnramified.comp R A S
  haveI : Algebra.EssFiniteType R S := Algebra.EssFiniteType.comp R A S
  have hsurj := IsSepClosed.algebraMap_surjective (ResidueField R) (ResidueField S)
  let e : ResidueField R ≃ₐ[ResidueField R] ResidueField S :=
    AlgEquiv.ofBijective (Algebra.ofId _ _) ⟨fun a b h => (algebraMap (ResidueField R) (ResidueField S)).injective h, hsurj⟩
  let φ : A →ₐ[R] ResidueField R := ((e.symm.restrictScalars R).toAlgHom).comp
    ((IsScalarTower.toAlgHom R S (ResidueField S)).comp (IsScalarTower.toAlgHom R A S))
  obtain ⟨s, hs⟩ := (GlobalTheory.T.bijective_residue_comp_etale_henselian R A R).2 φ
  refine ⟨s, ?_⟩
  ext x
  have hx := congrArg (fun ψ : A →ₐ[R] ResidueField R => ψ x) hs
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at hx
  rw [Ideal.mem_comap, ← residue_eq_zero_iff, ← ResidueField.algebraMap_eq]
  change algebraMap R (ResidueField R) (s x) = 0 ↔ x ∈ q
  rw [hx]
  simp only [φ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe,
    IsScalarTower.coe_toAlgHom', ResidueField.algebraMap_eq]
  change e.symm (residue S (algebraMap A S x)) = 0 ↔ x ∈ q
  rw [map_eq_zero_iff _ e.symm.injective, residue_eq_zero_iff,
    IsLocalization.AtPrime.to_map_mem_maximal_iff S q]

end GlobalTheory.StrictHensel

namespace GlobalTheory.StrictHensel

theorem strictlyHenselian_iff : ∀ (R : Type) [CommRing R] [IsLocalRing R],
    (∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime],
      q.comap (algebraMap R A) = maximalIdeal R →
        ∃ s : A →ₐ[R] R, (maximalIdeal R).comap s.toRingHom = q) ↔
      (HenselianLocalRing R ∧ IsSepClosed (ResidueField R)) := by
  intro R _ _
  refine ⟨fun H => ⟨henselian_of_sections H, isSepClosed_of_sections H⟩, fun ⟨h₁, h₂⟩ => ?_⟩
  intro A _ _ _ q _ hq
  exact sections_of_henselian_sepClosed A q hq

end GlobalTheory.StrictHensel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianIffStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_section_iff_henselian_and_isSepClosed : ∀ (R : Type) [CommRing R] [IsLocalRing R], (∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime], q.comap (algebraMap R A) = maximalIdeal R → ∃ s : A →ₐ[R] R, (maximalIdeal R).comap s.toRingHom = q) ↔ (HenselianLocalRing R ∧ IsSepClosed (ResidueField R)) := by
  first | exact @GlobalTheory.StrictHensel.strictlyHenselian_iff | exact GlobalTheory.StrictHensel.strictlyHenselian_iff | (intros; apply GlobalTheory.StrictHensel.strictlyHenselian_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesHarishChandra
open Finset

namespace GlobalTheory.DSParam

open Finset in
private theorem diagonal_exp_single_two_pi_eq_one {n : ℕ} (a : Fin n) :
    (Matrix.diagonal fun b ↦
      Complex.exp (↑((Pi.single a (2 * Real.pi) : Fin n → ℝ) b) * Complex.I)) = 1 := by
  rw [← Matrix.diagonal_one]
  congr 1
  funext b
  by_cases h : b = a
  · subst h; simp [Complex.exp_two_pi_mul_I]
  · simp [Pi.single_apply, h]

open Finset in
private theorem exists_int_eq_weight_of_isWtOn {n : ℕ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hK : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ K)
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {μ : Fin n → ℝ} {v : H} (hv0 : v ≠ 0)
    (hv : _root_.Formalism.MainNotions.S.IsWtOn K σ μ v) (a : Fin n) : ∃ m : ℤ, μ a = m := by
  unfold _root_.Formalism.MainNotions.S.IsWtOn at hv
  have h1 := hv 0 (by simpa using hK)
  have h2 := hv (Pi.single a (2 * Real.pi)) (by rw [diagonal_exp_single_two_pi_eq_one]; exact hK)
  rw [diagonal_exp_single_two_pi_eq_one] at h2
  simp only [Pi.zero_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    Matrix.diagonal_one, mul_zero, Finset.sum_const_zero, one_smul] at h1
  rw [h1] at h2
  have hsum : (∑ b, μ b * (Pi.single a (2 * Real.pi) : Fin n → ℝ) b) = μ a * (2 * Real.pi) := by
    simp [Pi.single_apply, mul_ite]
  rw [hsum] at h2
  have he : Complex.exp (↑(μ a * (2 * Real.pi)) * Complex.I) = 1 := by
    by_contra hne
    apply hv0
    have : (Complex.exp (↑(μ a * (2 * Real.pi)) * Complex.I) - 1) • v = 0 := by
      rw [sub_smul, ← h2, one_smul, sub_self]
    exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp he
  refine ⟨m, ?_⟩
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  have : ((μ a : ℝ) : ℂ) = (m : ℂ) := by
    apply mul_right_cancel₀ hpi
    push_cast at hm
    linear_combination hm
  exact_mod_cast this

open Finset in
private theorem one_mem_Kset_divisor {n : ℕ} (ε : Fin n → Bool) :
    (1 : Matrix (Fin n) (Fin n) ℂ) ∈ _root_.Formalism.REAL.Kset ε := by
  unfold _root_.Formalism.REAL.Kset
  exact ⟨one_mem _, by simp⟩

open Finset in
private theorem card_same_diff_sign_lt_gt_add_one_eq {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    #{b | a < b ∧ ε b = ε a} + #{b | b < a ∧ ε b = ε a} + #{b | a < b ∧ ε b ≠ ε a}
      + #{b | b < a ∧ ε b ≠ ε a} + 1 = n := by
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have key : ∀ b, ((if a < b ∧ ε b = ε a then 1 else 0) + (if b < a ∧ ε b = ε a then 1 else 0) +
      (if a < b ∧ ε b ≠ ε a then 1 else 0) + (if b < a ∧ ε b ≠ ε a then 1 else 0) : ℕ)
      = if b = a then 0 else 1 := by
    intro b
    rcases lt_trichotomy a b with h | h | h
    · have h1 : b ≠ a := ne_of_gt h
      have h2 : ¬ b < a := not_lt.mpr h.le
      by_cases he : ε b = ε a <;> simp [h, h1, h2, he]
    · subst h; simp
    · have h1 : b ≠ a := ne_of_lt h
      have h2 : ¬ a < b := not_lt.mpr h.le
      by_cases he : ε b = ε a <;> simp [h, h1, h2, he]
  rw [Finset.sum_congr rfl (fun b _ => key b)]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
    Fintype.card_fin]
  have := a.isLt
  omega

open Finset in
private theorem exists_int_rhoC_sub_rhoN_sub_half {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    ∃ m : ℤ, _root_.Formalism.REAL.rhoC ε a - _root_.Formalism.REAL.rhoN ε a - ((n : ℝ) - 1) / 2 = m := by
  have h := card_same_diff_sign_lt_gt_add_one_eq ε a
  unfold _root_.Formalism.REAL.rhoC _root_.Formalism.REAL.rhoN
  refine ⟨-((#{b | b < a ∧ ε b = ε a} : ℕ) + (#{b | a < b ∧ ε b ≠ ε a} : ℕ) : ℤ), ?_⟩
  have hr : ((#{b | a < b ∧ ε b = ε a} : ℕ) : ℝ) + #{b | b < a ∧ ε b = ε a}
      + #{b | a < b ∧ ε b ≠ ε a} + #{b | b < a ∧ ε b ≠ ε a} + 1 = n := by
    exact_mod_cast h
  push_cast
  linear_combination hr / 2


open Finset in
theorem _root_.GlobalTheory.DSParam.isHCParam_of_isDS : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    StrictAnti lam → _root_.Formalism.MainNotions.S.IsDS ε lam σ → _root_.Formalism.QuantumDeterminants.IsHCParam lam := by
  intro n H _ _ ε lam σ hlam hds
  unfold _root_.Formalism.MainNotions.S.IsDS at hds
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hds
  unfold _root_.Formalism.MainNotions.S.IsKTypeOf at hS
  obtain ⟨-, -, -, ⟨v, -, hv0, hv⟩, -⟩ := hS
  unfold _root_.Formalism.QuantumDeterminants.IsHCParam
  refine ⟨hlam, fun a => ?_⟩
  obtain ⟨k, hk⟩ := exists_int_eq_weight_of_isWtOn (one_mem_Kset_divisor ε) hv0 hv a
  obtain ⟨m, hm⟩ := exists_int_rhoC_sub_rhoN_sub_half ε a
  refine ⟨k + m, ?_⟩
  have hl : _root_.Formalism.QuantumDeterminants.lowK ε lam a = lam a + _root_.Formalism.REAL.rhoN ε a - _root_.Formalism.REAL.rhoC ε a := by
    unfold _root_.Formalism.QuantumDeterminants.lowK; simp
  push_cast
  linarith

end GlobalTheory.DSParam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomExtLocalization
open IsLocalRing

namespace GlobalTheory.IndEtaleHensel

theorem algHom_ext_localization {R A P : Type} [CommRing R] [CommRing A] [CommRing P]
    [Algebra R A] [Algebra R P] (q : Ideal A) [q.IsPrime]
    (φ₁ φ₂ : Localization.AtPrime q →ₐ[R] P)
    (h : φ₁.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q)) =
      φ₂.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q))) : φ₁ = φ₂ := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext q.primeCompl
  exact RingHom.ext fun a => DFunLike.congr_fun h a

theorem bijective_of_algEquiv {R X Y T : Type} [CommRing R] [CommRing X] [CommRing Y] [CommRing T]
    [Algebra R X] [Algebra R Y] [Algebra R T] [IsLocalRing T] (e : X ≃ₐ[R] Y)
    (h : Function.Bijective
      (fun φ : X →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ)) :
    Function.Bijective
      (fun φ : Y →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ) := by
  constructor
  · intro φ₁ φ₂ hφ
    have hc : φ₁.comp (e : X →ₐ[R] Y) = φ₂.comp (e : X →ₐ[R] Y) := by
      apply h.1
      simp only at hφ ⊢
      rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hφ]
    ext y
    have := DFunLike.congr_fun hc (e.symm y)
    simpa using this
  · intro ψ
    obtain ⟨φ, hφ⟩ := h.2 (ψ.comp (e : X →ₐ[R] Y))
    refine ⟨φ.comp (e.symm : Y →ₐ[R] X), ?_⟩
    simp only at hφ ⊢
    rw [← AlgHom.comp_assoc, hφ]
    ext y; simp

theorem bijective_localization {R A T : Type} [CommRing R] [CommRing A] [CommRing T]
    [Algebra R A] [Algebra R T] [IsLocalRing T] (q : Ideal A) [q.IsPrime]
    (hA : Function.Bijective
      (fun φ : A →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ)) :
    Function.Bijective (fun φ : Localization.AtPrime q →ₐ[R] T =>
      (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ) := by
  set π := IsScalarTower.toAlgHom R T (ResidueField T)
  set ι := IsScalarTower.toAlgHom R A (Localization.AtPrime q)
  constructor
  · intro φ₁ φ₂ hφ
    apply algHom_ext_localization q
    apply hA.1
    simp only at hφ ⊢
    rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hφ]
  · intro ψ
    obtain ⟨φ, hφ⟩ := hA.2 (ψ.comp ι)
    simp only at hφ
    have hu : ∀ y : q.primeCompl, IsUnit (φ y) := by
      intro y
      have h1 : IsUnit (ψ (algebraMap A (Localization.AtPrime q) y)) :=
        (IsLocalization.map_units (Localization.AtPrime q) y).map ψ
      have h2 : π (φ y) = ψ (algebraMap A (Localization.AtPrime q) y) := DFunLike.congr_fun hφ (y : A)
      rw [← h2] at h1
      have h3 : π (φ y) = residue T (φ y) := by
        simp [π, IsScalarTower.toAlgHom_apply, ResidueField.algebraMap_eq]
      rw [h3] at h1
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp h1.ne_zero
    refine ⟨IsLocalization.liftAlgHom (M := q.primeCompl) (S := Localization.AtPrime q) hu, ?_⟩
    apply algHom_ext_localization q
    ext a
    have := DFunLike.congr_fun hφ a
    simp only [AlgHom.comp_apply] at this ⊢
    rw [← this]
    congr 1
    simp [ι, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]

theorem bijective_residue_comp : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [HenselianLocalRing T], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) → Function.Bijective (fun φ : S →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ) := by
  intro R S T _ _ _ _ _ _ hS
  obtain ⟨ι, _, _, _, Si, hmono, hcov, hloc⟩ := hS
  have hbij : ∀ i, Function.Bijective (fun φ : Si i →ₐ[R] T =>
      (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ) := by
    intro i
    obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hloc i
    exact bijective_of_algEquiv e (bijective_localization q (GlobalTheory.T.bijective_residue_comp_etale_henselian R A T))
  have dir : Directed (· ≤ ·) Si := hmono.directed_le
  have htop : (⊤ : Subalgebra R S) ≤ iSup Si := fun s _ => by
    obtain ⟨i, hi⟩ := hcov s
    exact le_iSup Si i hi
  constructor
  · intro φ₁ φ₂ h
    simp only at h
    ext s
    obtain ⟨i, hi⟩ := hcov s
    have hc : φ₁.comp (Si i).val = φ₂.comp (Si i).val := by
      apply (hbij i).1
      simp only
      rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, h]
    exact DFunLike.congr_fun hc ⟨s, hi⟩
  · intro ψ
    choose f hf using fun i => (hbij i).2 (ψ.comp (Si i).val)
    simp only at hf
    have compat : ∀ i j (h : Si i ≤ Si j), f i = (f j).comp (Subalgebra.inclusion h) := by
      intro i j h
      apply (hbij i).1
      simp only
      rw [hf i, ← AlgHom.comp_assoc, hf j]
      ext x; rfl
    refine ⟨(Subalgebra.iSupLift Si dir f compat ⊤ htop).comp
      (Subalgebra.topEquiv.symm : S ≃ₐ[R] (⊤ : Subalgebra R S)).toAlgHom, ?_⟩
    ext s
    obtain ⟨i, hi⟩ := hcov s
    have h1 := DFunLike.congr_fun (hf i) ⟨s, hi⟩
    simp only [AlgHom.comp_apply] at h1 ⊢
    refine Eq.trans ?_ h1
    congr 1
    exact Subalgebra.iSupLift_of_mem (K := Si) (dir := dir) (f := f) (hf := compat)
      (T := ⊤) (hT := htop) ⟨s, trivial⟩ hi

end GlobalTheory.IndEtaleHensel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockQuadraticActionMapLieBracket
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PderivPderivCommFock
open Formalism.BasicNotions.TH MvPolynomial

namespace GlobalTheory

theorem pderiv_pderiv_comm_fock {σ : Type} (i j : σ) (P : MvPolynomial σ ℂ) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  have hc : ∀ (a b k : σ), pderiv a (pderiv b (X k : MvPolynomial σ ℂ)) = 0 := by
    intro a b k
    rw [pderiv_X, Pi.single_apply]
    split_ifs
    · exact pderiv_one
    · exact map_zero _
  refine MvPolynomial.induction_on (motive := fun P => pderiv i (pderiv j P) = pderiv j (pderiv i P)) P ?_ ?_ ?_
  · intro a
    simp
  · intro p q hp hq
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  · intro p k hp
    simp only [pderiv_mul, map_add (f := _), hc, mul_zero, add_zero]
    rw [hp]
    ring

theorem fock_letters_ccr (p q r s : ℕ) (l m : Ln p q r s) :
    (lowB l * raiB m - raiB m * lowB l = if l = m then (1 : Module.End ℂ (Pol p q r s)) else 0) ∧
      lowB l * lowB m = lowB m * lowB l ∧ raiB l * raiB m = raiB m * raiB l := by
  classical
  have hcomm : ∀ (i j : Ln p q r s) (P : Pol p q r s), pderiv i (pderiv j P) = pderiv j (pderiv i P) :=
    fun i j P => pderiv_pderiv_comm_fock i j P
  have hX : ∀ (i j : Ln p q r s), pderiv i (X j : Pol p q r s) = if j = i then 1 else 0 := by
    intro i j
    rw [pderiv_X, Pi.single_apply]
  have hne : ∀ l m : Ln p q r s, linePos l ≠ linePos m → l ≠ m := by
    rintro l m h rfl
    exact h rfl
  refine ⟨?_, ?_, ?_⟩
  · by_cases hlm : l = m
    · subst hlm
      rw [if_pos rfl]
      cases hl : linePos l <;> simp only [lowB, raiB, hl, Bool.false_eq_true, ↓reduceIte] <;>
        refine LinearMap.ext fun f => ?_ <;>
        simp [Module.End.mul_apply, hX]
    · rw [if_neg hlm]
      cases hl : linePos l <;> cases hm : linePos m <;>
        simp only [lowB, raiB, hl, hm, Bool.false_eq_true, ↓reduceIte] <;>
        refine LinearMap.ext fun f => ?_ <;>
        simp [Module.End.mul_apply, hX, hcomm, Ne.symm hlm, hlm] <;> ring
  · cases hl : linePos l <;> cases hm : linePos m <;>
      simp only [lowB, hl, hm, Bool.false_eq_true, ↓reduceIte] <;>
      refine LinearMap.ext fun f => ?_ <;>
      simp [Module.End.mul_apply, hX, hcomm] <;> (try ring_nf) <;> (try (intro h; subst h; exact absurd (hl.symm.trans hm) (by decide)))
  · cases hl : linePos l <;> cases hm : linePos m <;>
      simp only [raiB, hl, hm, Bool.false_eq_true, ↓reduceIte] <;>
      refine LinearMap.ext fun f => ?_ <;>
      simp [Module.End.mul_apply, hX, hcomm] <;> (try ring_nf) <;> (try (intro h; subst h; exact absurd (hl.symm.trans hm) (by decide)))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockQuadraticActionMapLieBracket
open Formalism.BasicNotions.TH

namespace GlobalTheory.FockLie

theorem weyl_comm {A : Type*} [Ring A] [Algebra ℂ A] {ι : Type*} [DecidableEq ι] (a b : ι → A)
    (h : ∀ l m, (b l * a m - a m * b l = if l = m then (1 : A) else 0) ∧
      b l * b m = b m * b l ∧ a l * a m = a m * a l) (i j k l : ι) :
    (a i * b j) * (a k * b l) - (a k * b l) * (a i * b j) =
      (if j = k then a i * b l else 0) - (if l = i then a k * b j else 0) := by
  have h1 : b j * a k = a k * b j + if j = k then (1 : A) else 0 := by
    rw [← (h j k).1]; abel
  have h2 : b l * a i = a i * b l + if l = i then (1 : A) else 0 := by
    rw [← (h l i).1]; abel
  have e1 : (a i * b j) * (a k * b l) = a i * (b j * a k) * b l := by simp only [mul_assoc]
  have e2 : (a k * b l) * (a i * b j) = a k * (b l * a i) * b j := by simp only [mul_assoc]
  have e3 : a i * (a k * b j) * b l = a k * (a i * b l) * b j := by
    calc a i * (a k * b j) * b l = (a i * a k) * (b j * b l) := by simp only [mul_assoc]
      _ = (a k * a i) * (b l * b j) := by rw [(h i k).2.2, (h j l).2.1]
      _ = _ := by simp only [mul_assoc]
  rw [e1, e2, h1, h2, mul_add, mul_add, add_mul, add_mul, e3]
  split_ifs <;> simp

theorem omE_comm {p q r s : ℕ} (i j k l : Ln p q r s) :
    omE i j * omE k l - omE k l * omE i j =
      (if j = k then omE i l else 0) - (if l = i then omE k j else 0) := by
  have h := weyl_comm (raiB : Ln p q r s → _) lowB (GlobalTheory.fock_letters_ccr p q r s) i j k l
  have e : omE i j * omE k l - omE k l * omE i j =
      (raiB i * lowB j) * (raiB k * lowB l) - (raiB k * lowB l) * (raiB i * lowB j) := by
    simp only [omE]
    split_ifs <;>
      simp only [add_zero, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] <;>
      module
  rw [e, h]
  simp only [omE]
  by_cases h1 : j = k <;> by_cases h2 : l = i
  · subst h1; subst h2; simp
  · have h3 : ¬ i = l := fun h => h2 h.symm
    simp [h1, h2, h3]
  · have h3 : ¬ k = j := fun h => h1 h.symm
    simp [h1, h2, h3]
  · simp [h1, h2]

theorem omAct_single {p q r s : ℕ} (i j : Ln p q r s) (x : ℂ) :
    omAct p q r s (Matrix.single i j x) = x • omE i j := by
  rw [omAct_apply]
  simp [Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_smul]

theorem omAct_single_mul {p q r s : ℕ} (i j k l : Ln p q r s) (x y : ℂ) :
    omAct p q r s (Matrix.single i j x * Matrix.single k l y) =
      (x * y) • (if j = k then omE i l else 0) := by
  by_cases h : j = k
  · subst h
    rw [Matrix.single_mul_single_same, omAct_single, if_pos rfl]
  · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, if_neg h, map_zero, smul_zero]

theorem omAct_lie (p q r s : ℕ) (Y Z : Matrix (Ln p q r s) (Ln p q r s) ℂ) :
    omAct p q r s (Y * Z - Z * Y) =
      omAct p q r s Y * omAct p q r s Z - omAct p q r s Z * omAct p q r s Y := by
  induction Y using Matrix.induction_on' with
  | h_zero => simp
  | h_add Y Y' hY hY' =>
    have : (Y + Y') * Z - Z * (Y + Y') = (Y * Z - Z * Y) + (Y' * Z - Z * Y') := by
      rw [add_mul, mul_add]; abel
    rw [this, map_add (f := _), hY, hY', map_add (f := _), add_mul, mul_add]; abel
  | h_std_basis i j x =>
    induction Z using Matrix.induction_on' with
    | h_zero => simp
    | h_add Z Z' hZ hZ' =>
      have : Matrix.single i j x * (Z + Z') - (Z + Z') * Matrix.single i j x =
          (Matrix.single i j x * Z - Z * Matrix.single i j x) +
            (Matrix.single i j x * Z' - Z' * Matrix.single i j x) := by
        rw [add_mul, mul_add]; abel
      rw [this, map_add (f := _), hZ, hZ', map_add (f := _), add_mul, mul_add]; abel
    | h_std_basis k l y =>
      rw [map_sub, omAct_single_mul, omAct_single_mul, omAct_single, omAct_single,
        smul_mul_smul_comm, smul_mul_smul_comm, mul_comm y x, ← smul_sub, ← smul_sub, omE_comm]

end GlobalTheory.FockLie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockQuadraticActionMapLieBracketStatement
open Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockQuadraticAction_map_lie_bracket : ∀ (p q r s : ℕ) (Y Z : Matrix (Ln p q r s) (Ln p q r s) ℂ), omAct p q r s (Y * Z - Z * Y) = omAct p q r s Y * omAct p q r s Z - omAct p q r s Z * omAct p q r s Y := by
  first | exact @GlobalTheory.FockLie.omAct_lie | exact GlobalTheory.FockLie.omAct_lie | (intros; apply GlobalTheory.FockLie.omAct_lie <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClopenIntegralOfSmoothOverField
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem exists_clopen_integral_of_smooth_over_field :
    ∀ (F : Type) [Field F] (Z : Scheme.{0}) (q : Z ⟶ Sp F), Smooth q → ∀ z : Z,
      ∃ (W' : Scheme.{0}) (j : W' ⟶ Z), IsClosedImmersion j ∧ IsOpenImmersion j ∧ IsIntegral W' ∧
        z ∈ Set.range j := by
  intro F _ Z q hq z
  obtain ⟨hR, hN, hL⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F Z q hq
  have : GlobalTheory.IsNormalScheme Z := by first | exact hN | exact IsNormalScheme.of_pred hN
  have hC : irreducibleComponent z ∈ irreducibleComponents Z := irreducibleComponent_mem_irreducibleComponents z
  let C : Z.Opens := ⟨irreducibleComponent z, IsNormalScheme.isOpen_of_mem_irreducibleComponents hC⟩
  have hzC : z ∈ C := mem_irreducibleComponent
  have hrange : Set.range C.ι = (C : Set Z) := Scheme.Opens.range_ι C
  refine ⟨C.toScheme, C.ι, ?_, inferInstance, ?_, by rw [hrange]; exact hzC⟩
  · apply IsClosedImmersion.of_isPreimmersion
    rw [hrange]
    exact isClosed_of_mem_irreducibleComponents _ hC
  · have : IrreducibleSpace C := Subtype.irreducibleSpace isIrreducible_irreducibleComponent
    have : Nonempty C := ⟨⟨z, hzC⟩⟩
    exact isIntegral_of_irreducibleSpace_of_isReduced C.toScheme

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersi
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem preRes_bijective : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (φ : X' ⟶ X) [IsClosedImmersion φ] (s' : X' ⟶ Sp R'), Function.Bijective (preRes φ s').pull1 ∧ Function.Bijective (preRes φ s').pull2 ∧ (CohomZeroIsConstants (OAff s') → CohomZeroIsConstants (OPre φ s')) := by
  intro R' _ X X' φ _ s'
  have hB : ∀ {U : TopologicalSpace.Opens X} {x : X}, x ∈ U → ∃ U' ∈ X.affineOpens, x ∈ U' ∧ U' ≤ U :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
  refine GlobalTheory.T.structureSheafCohomology_basis_bijective R' X' s' X.affineOpens (preU φ) (preU_mono φ) ?_ ?_
  · intro U x hx
    obtain ⟨W, hW, hWU⟩ := (φ.isClosedEmbedding).isInducing.isOpen_iff.mp U.1.2
    have hxW : φ.base x ∈ W := by
      have : x ∈ φ.base ⁻¹' W := by rw [hWU]; exact hx
      exact this
    obtain ⟨V, hV, hxV, hVW⟩ := hB (U := ⟨W, hW⟩) hxW
    refine ⟨⟨V, hV⟩, hxV, ?_⟩
    intro y hy
    have : y ∈ φ.base ⁻¹' W := hVW hy
    rw [hWU] at this
    exact this
  · intro a b x ha hb
    obtain ⟨V, hV, hxV, hVW⟩ := hB (U := a.1 ⊓ b.1) ⟨ha, hb⟩
    exact ⟨⟨V, hV⟩, fun y hy ↦ (hVW hy).1, fun y hy ↦ (hVW hy).2, hxV⟩

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersiStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimageCochainRestriction_bijective_closedImmersion : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (φ : X' ⟶ X) [IsClosedImmersion φ] (s' : X' ⟶ Sp R'), Function.Bijective (preRes φ s').pull1 ∧ Function.Bijective (preRes φ s').pull2 ∧ (CohomZeroIsConstants (OAff s') → CohomZeroIsConstants (OPre φ s')) := by
  first | exact @GlobalTheory.AbCoh.preRes_bijective | exact GlobalTheory.AbCoh.preRes_bijective | (intros; apply GlobalTheory.AbCoh.preRes_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGNeZero
noncomputable section

open MvPolynomial

namespace GlobalTheory.MinorFrame

def rsub {σ σ' : Type} [Fintype σ'] (M : Matrix σ' σ ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ' ℂ :=
  aeval fun v => ∑ w, C (M w v) * X w

theorem rsub_X {σ σ' : Type} [Fintype σ'] (M : Matrix σ' σ ℂ) (v : σ) :
    rsub M (X v) = ∑ w, C (M w v) * X w := aeval_X _ _

variable {ι : Type}

open Classical in
def frameMat {d a : ℕ} (x₀ : Var ι d a → ℂ) : Matrix (ι × Fin a × Fin a) (Var ι d a) ℂ :=
  by
    classical
    exact fun w v => if w.1 = v.1 ∧ w.2.2 = v.2.2 then x₀ (v.1, v.2.1, w.2.1) else 0

def detG [Fintype ι] (a : ℕ) (n : ι → ℕ) : MvPolynomial (ι × Fin a × Fin a) ℂ :=
  ∏ τ, (Matrix.of fun i j : Fin a => (X (τ, i, j) : MvPolynomial (ι × Fin a × Fin a) ℂ)).det ^ n τ

theorem eval_detG [Fintype ι] (a : ℕ) (n : ι → ℕ) (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    eval (fun v : ι × Fin a × Fin a => g v.1 v.2.1 v.2.2) (detG a n) = detChar n g := by
  unfold detG detChar
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext i j
  simp

theorem detG_ne_zero [Fintype ι] (a : ℕ) (n : ι → ℕ) : detG (ι := ι) a n ≠ 0 := by
  intro h
  have := eval_detG (ι := ι) a n (fun _ => 1)
  rw [h, map_zero] at this
  simp [detChar] at this

end GlobalTheory.MinorFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinJetSplitLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinJetSplitLattice
set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma omegaFactor_ne_zero' {F : Type} [Field F] [NumberField F] (𝔞 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 ≠ 0 := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm
  refine mul_ne_zero ?_ ?_
  · have h : (0:ℝ) < |((discr F : ℤ) : ℝ)| := by
      rw [abs_pos]; exact_mod_cast discr_ne_zero F
    positivity
  · rw [Rat.cast_ne_zero, Ne, FractionalIdeal.absNorm_eq_zero_iff]
    exact 𝔞.ne_zero


set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.hasSum_jet_split : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ), Even k → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → HasSum (fun ξ : F ↦ ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ)) ^ k * (a ξ * _root_.GlobalTheory.HilbFam.eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, _root_.GlobalTheory.HilbFam.lag k (κ i) c ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t))) (_root_.GlobalTheory.HilbFam.jet k (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) κ τ c t) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t κ hk ha hτ
  have h := (_root_.GlobalTheory.HilbFam.hasSum_iterD_gval_split F k 𝔞 𝔟 a₀ a x τ c t
    (_root_.GlobalTheory.HilbFam.word κ) hk ha hτ).mul_left
    (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ)) ^ k)
  have hC : ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F *
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ)) ^ k ≠ 0 := by
    refine pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ ?_) ?_)
    · simp [Real.pi_ne_zero, Complex.I_ne_zero]
    · exact_mod_cast omegaFactor_ne_zero' 𝔞
  simp only [_root_.GlobalTheory.HilbFam.count_word_eq, mul_div_cancel₀ _ hC] at h
  exact h

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinJetSplitLatticeStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_hilbertEisenstein_jet_split_lattice : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (κ : Emb F → ℕ), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → HasSum (fun ξ : F ↦ ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k * (a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, lag k (κ i) c ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t))) (jet k (split 𝔞 𝔟 x) κ τ c t) := by
  first | exact @GlobalTheory.HilbFam.hasSum_jet_split | exact GlobalTheory.HilbFam.hasSum_jet_split | (intros; apply GlobalTheory.HilbFam.hasSum_jet_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairFstPreimageRestrictionBijectiveClosedImmersi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairFstPreimageRestrictionBijectiveClosedImmersi
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

private theorem exAff (Z : Scheme.{0}) {O : Z.Opens} {z : Z} (hz : z ∈ O) :
    ∃ V : Z.affineOpens, z ∈ V.1 ∧ V.1 ≤ O := by
  obtain ⟨V, hV, hzV, hVO⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens hz
  exact ⟨⟨V, hV⟩, hzV, hVO⟩

theorem pair_pre_bijective : ∀ (R' : Type) [CommRing R'] (X Y Y' : Scheme.{0}) (ψ : Y ⟶ X) (χ : Y' ⟶ Y) [IsClosedImmersion χ] (q' : Y' ⟶ Sp R'), Function.Bijective (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 ∧ Function.Bijective (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 ∧ (CohomZeroIsConstants (OAff q') → CohomZeroIsConstants (pairFst ψ ⋙ OPre χ q')) := by
  intro R' _ X Y Y' ψ χ _ q'
  have hG : Monotone (fun p : Pair ψ ↦ preU χ p.1.1) := fun _ _ h ↦ preU_mono χ (Pair.le_fst h)
  have hF : pairFst ψ ⋙ preAff χ = hG.functor.op := rfl
  have key := GlobalTheory.T.structureSheafCohomology_basis_bijective R' Y' q' (Pair ψ) (fun p ↦ preU χ p.1.1) hG ?cov ?dir
  · rw [hF]
    exact key
  case cov =>
    intro U x hx
    obtain ⟨t, ht, hte⟩ := χ.isClosedEmbedding.isInducing.isOpen_iff.1 U.1.2
    have hxt : χ x ∈ (⟨t, ht⟩ : Y.Opens) := by
      show χ x ∈ t
      rw [← Set.mem_preimage, hte]; exact hx
    obtain ⟨W, hW, -⟩ := exAff X (show ψ (χ x) ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨V, hV, hVle⟩ := exAff Y (show χ x ∈ (⟨t, ht⟩ : Y.Opens) ⊓ ψ ⁻¹ᵁ W.1 from ⟨hxt, hW⟩)
    refine ⟨⟨(V, W), fun y hy ↦ (hVle hy).2⟩, hV, ?_⟩
    intro y hy
    have : χ y ∈ t := (hVle hy).1
    rw [← Set.mem_preimage, hte] at this
    exact this
  case dir =>
    intro a b x ha hb
    have hya : ψ (χ x) ∈ a.1.2.1 := a.2 ha
    have hyb : ψ (χ x) ∈ b.1.2.1 := b.2 hb
    obtain ⟨W, hW, hWle⟩ := exAff X (show ψ (χ x) ∈ a.1.2.1 ⊓ b.1.2.1 from ⟨hya, hyb⟩)
    obtain ⟨V, hV, hVle⟩ := exAff Y
      (show χ x ∈ (a.1.1.1 ⊓ b.1.1.1) ⊓ ψ ⁻¹ᵁ W.1 from ⟨⟨ha, hb⟩, hW⟩)
    refine ⟨⟨(V, W), fun y hy ↦ (hVle hy).2⟩, ?_, ?_, hV⟩
    · exact ⟨fun y hy ↦ (hVle hy).1.1, fun y hy ↦ (hWle hy).1⟩
    · exact ⟨fun y hy ↦ (hVle hy).1.2, fun y hy ↦ (hWle hy).2⟩

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairFstPreimageRestrictionBijectiveClosedImmersiStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairFst_preimage_restriction_bijective_closedImmersion : ∀ (R' : Type) [CommRing R'] (X Y Y' : Scheme.{0}) (ψ : Y ⟶ X) (χ : Y' ⟶ Y) [IsClosedImmersion χ] (q' : Y' ⟶ Sp R'), Function.Bijective (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 ∧ Function.Bijective (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 ∧ (CohomZeroIsConstants (OAff q') → CohomZeroIsConstants (pairFst ψ ⋙ OPre χ q')) := by
  first | exact @GlobalTheory.AbCoh.pair_pre_bijective | exact GlobalTheory.AbCoh.pair_pre_bijective | (intros; apply GlobalTheory.AbCoh.pair_pre_bijective <;> assumption)
end
end

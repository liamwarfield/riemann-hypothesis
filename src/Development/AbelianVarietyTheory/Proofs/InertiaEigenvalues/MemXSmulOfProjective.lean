module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

namespace GlobalTheory.WachFree

theorem mem_X_smul_of_projective {D M : Type} [CommRing D] [IsDomain D] [AddCommGroup M]
    [Module D⟦X⟧ M] [Module.Projective D⟦X⟧ M] (c : D) (hc : c ≠ 0) (x y : M)
    (h : (C c : D⟦X⟧) • x = (X : D⟦X⟧) • y) : ∃ z : M, x = (X : D⟦X⟧) • z := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective D⟦X⟧ M›
  have hs' : ∀ m, Finsupp.linearCombination D⟦X⟧ id (s m) = m := fun m => LinearMap.congr_fun hs m
  have hd : ∀ m, (X : D⟦X⟧) ∣ s x m := by
    intro m
    have h1 := congrArg (fun w => constantCoeff (s w m)) h
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, constantCoeff_C,
      constantCoeff_X, zero_mul] at h1
    exact X_dvd_iff.mpr ((mul_eq_zero.mp h1).resolve_left hc)
  have : x ∈ LinearMap.range ((X : D⟦X⟧) • (LinearMap.id : M →ₗ[D⟦X⟧] M)) := by
    rw [← hs' x, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    obtain ⟨d, hd⟩ := hd m
    exact ⟨d • m, by rw [hd, mul_smul]; rfl⟩
  obtain ⟨z, hz⟩ := this
  exact ⟨z, by simpa using hz.symm⟩

theorem free_of_regular {O M : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] (c : O) (hc : c ≠ 0) (hc' : ¬ IsUnit c)
    (hX : IsSMulRegular M (X : O⟦X⟧))
    (h : ∀ x y : M, (C c : O⟦X⟧) • x = (X : O⟦X⟧) • y → ∃ z : M, x = (X : O⟦X⟧) • z) :
    Module.Free O⟦X⟧ M := by
  haveI : Module.FinitePresentation O⟦X⟧ M := Module.finitePresentation_of_finite _ _
  have hker : Ideal.span {(X : O⟦X⟧)} = RingHom.ker (constantCoeff (R := O)) := by
    ext f
    rw [Ideal.mem_span_singleton, RingHom.mem_ker, X_dvd_iff]
  let e : (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) ≃+* O :=
    (Ideal.quotEquivOfEq hker).trans
      (RingHom.quotientKerEquivOfSurjective (f := constantCoeff (R := O))
        fun a => ⟨C a, by simp⟩)
  haveI : IsDomain (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) := e.toMulEquiv.isDomain
  haveI : IsPrincipalIdealRing (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) :=
    IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective
  have hpow : ∀ (k : ℕ) (x y : M), (C (c ^ k) : O⟦X⟧) • x = (X : O⟦X⟧) • y →
      ∃ z : M, x = (X : O⟦X⟧) • z := by
    intro k
    induction k with
    | zero => intro x y hxy; exact ⟨y, by simpa using hxy⟩
    | succ k ih =>
      intro x y hxy
      rw [pow_succ, map_mul, mul_smul] at hxy
      obtain ⟨z, hz⟩ := ih _ _ hxy
      exact h _ _ hz
  have hdvd : ∀ a : O, a ≠ 0 → ∃ k : ℕ, a ∣ c ^ k := by
    intro a ha
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    obtain ⟨j, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    have hj : j ≠ 0 := by
      rintro rfl
      exact hc' (by simp)
    refine ⟨k, ?_⟩
    rw [Units.mul_left_dvd]
    exact pow_dvd_pow_of_dvd (Dvd.dvd.mul_left (dvd_pow_self _ hj) _) _
  haveI := Module.Finite.of_restrictScalars_finite O⟦X⟧ (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)})
    (QuotSMulTop (X : O⟦X⟧) M)
  haveI : Module.IsTorsionFree (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) (QuotSMulTop (X : O⟦X⟧) M) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m hrm => ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    by_cases hr : constantCoeff r = 0
    · left
      rw [Ideal.Quotient.eq_zero_iff_mem, hker]
      exact hr
    right
    have h1 : (Submodule.Quotient.mk (r • m) : QuotSMulTop (X : O⟦X⟧) M) = 0 := hrm
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at h1 ⊢
    obtain ⟨y, -, hy⟩ := h1
    obtain ⟨k, b, hb⟩ := hdvd _ hr
    obtain ⟨d, hd⟩ : (X : O⟦X⟧) ∣ C (c ^ k) - C b * r := by
      rw [X_dvd_iff]
      simp [hb, mul_comm]
    obtain ⟨z, hz⟩ := hpow k m (d • m + (C b : O⟦X⟧) • y) (by
      rw [smul_add, smul_comm (X : O⟦X⟧) (C b : O⟦X⟧) y, hy, smul_smul, smul_smul, ← hd, ← add_smul,
        sub_add_cancel])
    exact ⟨z, trivial, hz.symm⟩
  refine (Module.free_quotSMulTop_iff_free O⟦X⟧ M ?_ hX).mp inferInstance
  rw [IsLocalRing.ringJacobson_eq_maximalIdeal, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, isUnit_iff_constantCoeff]
  simp

theorem finrank_fibre {ι R N : Type} [DecidableEq ι] [CommRing R] [IsLocalRing R] [AddCommGroup N]
    [Module (ι → R) N] [Module.Finite (ι → R) N] [Module.Flat (ι → R) N] (i : ι) :
    ∃ r : ℕ, ∀ (S : Type) [CommRing S] [Nontrivial S] [Algebra (ι → R) S],
      algebraMap (ι → R) S (Pi.single i 1) = 1 → Module.finrank S (S ⊗[ι → R] N) = r := by
  letI : Algebra (ι → R) R := (Pi.evalRingHom (fun _ : ι => R) i).toAlgebra
  haveI : Module.Free R (R ⊗[ι → R] N) := Module.free_of_flat_of_isLocalRing
  refine ⟨Module.finrank R (R ⊗[ι → R] N), fun S _ _ _ hS => ?_⟩
  letI : Algebra R S := ((algebraMap (ι → R) S).comp (Pi.constRingHom ι R)).toAlgebra
  haveI : IsScalarTower (ι → R) R S := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap (ι → R) S a = algebraMap (ι → R) S (fun _ => a i)
    have : a * Pi.single i 1 = (fun _ => a i) * Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    have h2 := congrArg (algebraMap (ι → R) S) this
    rwa [map_mul, map_mul, hS, mul_one, mul_one] at h2
  rw [← (AlgebraTensorModule.cancelBaseChange (ι → R) R S S N).finrank_eq,
    Module.finrank_baseChange]

theorem basis_of_baseChange {ι R N E D : Type} [Finite ι] [CommRing R] [IsLocalRing R]
    [AddCommGroup N] [Module (ι → R) N] [Module.Finite (ι → R) N] [Module R N]
    [IsScalarTower R (ι → R) N] [Module.Flat R N] [CommRing E] [Algebra (ι → R) E]
    (hE : Function.Injective (algebraMap (ι → R) E)) [AddCommGroup D] [Module E D]
    [Module (ι → R) D] [IsScalarTower (ι → R) E D] [Module.Free E D] (f : N →ₗ[ι → R] D)
    (hf : IsBaseChange E f) : Nonempty (Module.Basis (Fin (Module.finrank E D)) (ι → R) N) := by
  classical
  haveI := Fintype.ofFinite ι
  haveI : Module.Flat (ι → R) N := Algebra.FormallyUnramified.flat_of_restrictScalars R (ι → R) N
  haveI : Finite (MaximalSpectrum (ι → R)) := by
    haveI := (Algebra.QuasiFinite.finite_primesOver (S := ι → R)
      (IsLocalRing.maximalIdeal R)).to_subtype
    refine Finite.of_injective (fun n : MaximalSpectrum (ι → R) =>
      (⟨n.asIdeal, n.isMaximal.isPrime, ⟨(IsLocalRing.eq_maximalIdeal
        (@Ideal.isMaximal_comap_of_isIntegral_of_isMaximal R _ _ _ _
          (algebraMap_isIntegral_iff.mpr inferInstance) n.asIdeal n.isMaximal)).symm⟩⟩ :
        (IsLocalRing.maximalIdeal R).primesOver (ι → R))) fun a b hab => ?_
    exact MaximalSpectrum.ext (congrArg Subtype.val hab)
  refine Module.nonempty_basis_of_flat_of_finrank_eq _ _ _ fun P => ?_
  haveI := P.isMaximal
  have hee : ∀ i : ι, (Pi.single i 1 : ι → R) * (Pi.single i 1 - 1) = 0 := by
    intro i
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  obtain ⟨i, hi⟩ : ∃ i : ι, (Pi.single i 1 : ι → R) ∉ P.asIdeal := by
    by_contra hcon
    push Not at hcon
    apply P.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one, ← Finset.univ_sum_single (1 : ι → R)]
    exact Ideal.sum_mem _ fun j _ => hcon j
  have hi' : (Pi.single i 1 - 1 : ι → R) ∈ P.asIdeal :=
    (P.isMaximal.isPrime.mem_or_mem (by rw [hee i]; exact Ideal.zero_mem _)).resolve_left hi
  obtain ⟨r, hr⟩ := finrank_fibre (R := R) (N := N) i
  rw [hr ((ι → R) ⧸ P.asIdeal) (by
    rw [Ideal.Quotient.algebraMap_eq, ← map_one (Ideal.Quotient.mk P.asIdeal), Ideal.Quotient.eq]
    exact hi')]
  let I : Ideal E := Ideal.span {algebraMap (ι → R) E (Pi.single i 1 - 1)}
  haveI : Nontrivial (E ⧸ I) := by
    rw [Ideal.Quotient.nontrivial_iff]
    intro hI
    rw [Ideal.span_singleton_eq_top] at hI
    apply hi
    have : algebraMap (ι → R) E (Pi.single i 1) = 0 := by
      rw [← hI.mul_left_eq_zero, ← map_mul, hee, map_zero]
    rw [hE (this.trans (map_zero _).symm)]
    exact Ideal.zero_mem _
  haveI : Nontrivial E := (algebraMap E (E ⧸ I)).domain_nontrivial
  rw [← hr (E ⧸ I) (by
    rw [IsScalarTower.algebraMap_apply (ι → R) E (E ⧸ I), Ideal.Quotient.algebraMap_eq,
      ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    exact Ideal.subset_span (by simp)),
    ← (AlgebraTensorModule.cancelBaseChange (ι → R) E (E ⧸ I) (E ⧸ I) N).finrank_eq,
    (AlgebraTensorModule.congr (LinearEquiv.refl (E ⧸ I) (E ⧸ I)) hf.equiv).finrank_eq,
    Module.finrank_baseChange]

theorem basis_of_regular {ι O N E D : Type} [Finite ι] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [AddCommGroup N] [Module (ι → O⟦X⟧) N] [Module.Finite (ι → O⟦X⟧) N]
    [CommRing E] [Algebra (ι → O⟦X⟧) E]
    (hE : Function.Injective (algebraMap (ι → O⟦X⟧) E)) [AddCommGroup D] [Module E D]
    [Module (ι → O⟦X⟧) D] [IsScalarTower (ι → O⟦X⟧) E D] [Module.Free E D]
    (f : N →ₗ[ι → O⟦X⟧] D) (hf : IsBaseChange E f) (c : O) (hc : c ≠ 0) (hc' : ¬ IsUnit c)
    (hX : IsSMulRegular N (fun _ => X : ι → O⟦X⟧))
    (h : ∀ x y : N, (fun _ => C c : ι → O⟦X⟧) • x = (fun _ => X : ι → O⟦X⟧) • y →
      ∃ z : N, x = (fun _ => X : ι → O⟦X⟧) • z) :
    Nonempty (Module.Basis (Fin (Module.finrank E D)) (ι → O⟦X⟧) N) := by
  letI : Module O⟦X⟧ N := Module.compHom _ (algebraMap O⟦X⟧ (ι → O⟦X⟧))
  haveI : IsScalarTower O⟦X⟧ (ι → O⟦X⟧) N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite O⟦X⟧ N := Module.Finite.trans (ι → O⟦X⟧) _
  haveI : Module.Free O⟦X⟧ N := free_of_regular c hc hc' hX h
  exact basis_of_baseChange hE f hf


set_option maxHeartbeats 1600000 in
theorem wach_free {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hT : IsCrys (P.PD K) T.ρ) :
    Nonempty (Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T))
      (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K s LL h).N T)) := by
  obtain ⟨_, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hproj := H.W_proj K s LL h T
  generalize H.W K s LL h = W at hproj ⊢
  obtain ⟨hfree, hrk⟩ := W.DD_free T
  rw [← hrk]
  haveI : Module.Finite (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(W.N T) :=
    Module.Finite.iff_fg.mpr (W.N_fg T)
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp [(Fact.out : l.Prime).ne_zero] at this
  refine basis_of_regular (ι := ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (O := ↥(OL LL))
    (N := ↥(W.N T)) (E := W.EE) (D := W.DD T) W.EE_inj (W.N T).subtype (W.N_base T hT)
    ((l : ℕ) : ↥(OL LL)) hl0 hl ?_ ?_
  · intro x y hxy
    have h1 : (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • (x : W.DD T) =
        (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • (y : W.DD T) :=
      congrArg Subtype.val hxy
    rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE letπ (y : W.DD T)] at h1
    exact Subtype.ext (W.EE_π.smul_left_cancel.mp h1)
  · intro x y hxy
    have e1 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (C ((l : ℕ) : ℤ_[l])) =
        fun _ => C ((l : ℕ) : ↥(OL LL)) := by
      funext i
      simp
    have e2 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X = fun _ => X := by
      funext i
      simp [zlA]
    obtain ⟨z, hz⟩ := @mem_X_smul_of_projective ℤ_[l] ↥(W.N T) _ _ _
      (Module.compHom _ (zlA LL (Module.finrank ℚ_[l] ↥(K0 K)))) hproj ((l : ℕ) : ℤ_[l])
      (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) x y (by
        change zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (C ((l : ℕ) : ℤ_[l])) • x =
          zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X • y
        rw [e1, e2]
        exact hxy)
    refine ⟨z, ?_⟩
    change x = zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X • z at hz
    rw [e2] at hz
    exact hz

end GlobalTheory.WachFree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisPlusFrobeniusStableSubringInFilZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisPlusFrobeniusStableSubringInFilZero
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.CrisPlus

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)

theorem plus_phi {b : P.R.B} (h : Plus T b) : Plus T (P.φB b) := by
  obtain ⟨N, x, hx⟩ := h
  refine ⟨N, GlobalTheory.MemLoc.phiA l x, ?_⟩
  have e : (l : P.R.B) ^ N * P.φB b = P.φB ((l : P.R.B) ^ N * b) := by
    rw [map_mul, map_pow, map_natCast]
  rw [e, T.frob, hx]
  exact GlobalTheory.CrisMaps.φB_phiA l x

theorem plus_iterate {b : P.R.B} (h : Plus T b) (j : ℕ) : Plus T (P.φB^[j] b) := by
  induction j with
  | zero => exact h
  | succ j ih => rw [Function.iterate_succ_apply']; exact plus_phi T ih

theorem plus_add_mul {a b : P.R.B} (ha : Plus T a) (hb : Plus T b) : Plus T (a + b) ∧ Plus T (a * b) := by
  obtain ⟨N, x, hx⟩ := ha
  obtain ⟨M, y, hy⟩ := hb
  refine ⟨⟨N + M, (l : Formalism.Per.Acris l) ^ M * x + (l : Formalism.Per.Acris l) ^ N * y, ?_⟩, ⟨N + M, x * y, ?_⟩⟩
  · have e : (l : P.R.B) ^ (N + M) * (a + b) = (l : P.R.B) ^ M * ((l : P.R.B) ^ N * a) + (l : P.R.B) ^ N * ((l : P.R.B) ^ M * b) := by
      ring
    rw [e, map_add (f := _), map_mul T.eB ((l : P.R.B) ^ M) ((l : P.R.B) ^ N * a),
      map_mul T.eB ((l : P.R.B) ^ N) ((l : P.R.B) ^ M * b), hx, hy]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  · have e : (l : P.R.B) ^ (N + M) * (a * b) = ((l : P.R.B) ^ N * a) * ((l : P.R.B) ^ M * b) := by ring
    rw [e, map_mul, hx, hy, map_mul]

theorem plus_alg (q : ℚ_[l]) : Plus T (algebraMap ℚ_[l] P.R.B q) := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ‖q‖ hl
  have hz : ‖(l : ℚ_[l]) ^ N * q‖ ≤ 1 := by
    rw [norm_mul, Padic.norm_p_pow]
    have hp : (0 : ℝ) < (l : ℝ) ^ N := by positivity
    rw [zpow_neg, zpow_natCast]
    rw [inv_mul_le_iff₀ hp, mul_one]
    exact hN.le
  let z : ℤ_[l] := ⟨(l : ℚ_[l]) ^ N * q, hz⟩
  refine ⟨N, algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.zA l z), ?_⟩
  have e : (l : P.R.B) ^ N * algebraMap ℚ_[l] P.R.B q = algebraMap ℚ_[l] P.R.B (z : ℚ_[l]) := by
    change _ = algebraMap ℚ_[l] P.R.B ((l : ℚ_[l]) ^ N * q)
    rw [map_mul, map_pow, map_natCast]
  rw [e, T.zB, GlobalTheory.RingIface.zB_eq_aB_zA l z, GlobalTheory.RingIface.aB_eq_alg l]

theorem plus_ainf (x : Formalism.Per.Ainf l) : Plus T (T.eB.symm (Formalism.Per.aB l x)) :=
  ⟨0, algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) x, by rw [pow_zero, one_mul, RingEquiv.apply_symm_apply]; exact GlobalTheory.RingIface.aB_eq_alg l x⟩

theorem plus_alt : Plus T P.tB := by
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  exact ⟨0, C.t, by rw [pow_zero, one_mul, hC.t]; rfl⟩

theorem plus_fil {b : P.R.B} (h : Plus T b) : P.ιB b ∈ Fil P 0 := by
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨N, x, hx⟩ := h
  obtain ⟨u, hu⟩ := (GlobalTheory.MemLoc.isUnit_l_BdRp l).exists_left_inv
  have e1 : T.eD (P.ιB ((l : P.R.B) ^ N * b)) = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (C.j x) := by
    rw [hC.ι, hx, C.ι_j]
  simp only [map_mul, map_pow, map_natCast] at e1
  have e2 : T.eD (P.ιB b) = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (u ^ N * C.j x) := by
    calc T.eD (P.ιB b)
        = (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) u * (l : Formalism.Per.BdR l)) ^ N * T.eD (P.ιB b) := by
          rw [← map_natCast (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l)) l, ← map_mul, hu, map_one, one_pow, one_mul]
      _ = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (u ^ N) * ((l : Formalism.Per.BdR l) ^ N * T.eD (P.ιB b)) := by
          rw [map_pow]; ring
      _ = _ := by rw [e1, ← map_mul]
  show P.ιB b ∈ (P.PD (botExt l)).Fil 0
  refine (T.fil (botExt l) 0 _).2 ?_
  rw [e2]
  exact GlobalTheory.RingIface.alg_mem_FilD_zero l _

theorem plus_props : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    (∀ b, Plus T b → Plus T (P.φB b)) ∧ (∀ b, Plus T b → ∀ j, ev P j b ∈ Fil P 0) ∧
    (∀ a b, Plus T a → Plus T b → Plus T (a + b) ∧ Plus T (a * b)) ∧
    (∀ q : ℚ_[l], Plus T (algebraMap ℚ_[l] P.R.B q)) ∧
    (∀ x : Formalism.Per.Ainf l, Plus T (T.eB.symm (Formalism.Per.aB l x))) ∧ Plus T P.tB := by
  intro l _ P AI T
  exact ⟨fun b h => plus_phi T h, fun b h j => plus_fil T (plus_iterate T h j), fun a b ha hb => plus_add_mul T ha hb,
    plus_alg T, plus_ainf T, plus_alt T⟩

end GlobalTheory.PMon.CrisPlus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisPlusFrobeniusStableSubringInFilZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcrisPlus_frobeniusStable_subring_in_filZero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), (∀ b, Plus T b → Plus T (P.φB b)) ∧ (∀ b, Plus T b → ∀ j, ev P j b ∈ Fil P 0) ∧ (∀ a b, Plus T a → Plus T b → Plus T (a + b) ∧ Plus T (a * b)) ∧ (∀ q : ℚ_[l], Plus T (algebraMap ℚ_[l] P.R.B q)) ∧ (∀ x : Formalism.Per.Ainf l, Plus T (T.eB.symm (Formalism.Per.aB l x))) ∧ Plus T P.tB := by
  first | exact @GlobalTheory.PMon.CrisPlus.plus_props | exact GlobalTheory.PMon.CrisPlus.plus_props | (intros; apply GlobalTheory.PMon.CrisPlus.plus_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListDegree
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.HcDeg

variable {g : ℕ} [Fact g.Prime]

theorem prod_Icc_eq_range (f : ℕ → ℂ) (d : ℕ) : ∏ i ∈ Finset.Icc 1 d, f i = ∏ i ∈ Finset.range d, f (i + 1) := by
  induction d with
  | zero => simp
  | succ d ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

theorem card_GL_C (d : ℕ) : (Fintype.card (Gn g d) : ℂ) =
    (∏ i ∈ Finset.range d, (g : ℂ) ^ i) * ∏ i ∈ Finset.Icc 1 d, ((g : ℂ) ^ i - 1) := by
  rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field, ZMod.card, Nat.cast_prod,
    Fin.prod_univ_eq_prod_range (fun i => (((g ^ d - g ^ i : ℕ)) : ℂ)) d]
  have h1 : ∀ i ∈ Finset.range d, (((g ^ d - g ^ i : ℕ)) : ℂ) = (g : ℂ) ^ i * ((g : ℂ) ^ (d - 1 - i + 1) - 1) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hle : g ^ i ≤ g ^ d := Nat.pow_le_pow_right (Fact.out : g.Prime).pos hi'.le
    rw [Nat.cast_sub hle, mul_sub, mul_one, ← pow_add]
    push_cast
    congr 2
    omega
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, prod_Icc_eq_range,
    Finset.prod_range_reflect (fun i => (g : ℂ) ^ (i + 1) - 1) d]

theorem prod_pow_add (a b : ℕ) : ∏ i ∈ Finset.range (a + b), (g : ℂ) ^ i =
    (∏ i ∈ Finset.range a, (g : ℂ) ^ i) * (∏ i ∈ Finset.range b, (g : ℂ) ^ i) * (g : ℂ) ^ (a * b) := by
  rw [Finset.prod_range_add]
  simp only [pow_add, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
  ring

theorem toG_one (n : ℕ) : toG (1 : Mt g n) = 1 := by
  apply Units.ext
  rw [toG, dite_eq_left isUnit_one, IsUnit.unit_spec]
  rfl

theorem tl_one (a b : ℕ) : tl a (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [GlobalTheory.GLm.ParBasic.tl_apply]
  simp [Matrix.one_apply, Fin.castAdd_inj]

theorem br_one (a b : ℕ) : br a b (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [GlobalTheory.GLm.ParBasic.br_apply]
  simp [Matrix.one_apply, Fin.natAdd_inj]

theorem hc_one (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) :
    hc a b α β (a + b) 1 * (Fintype.card (Gn g a) * Fintype.card (Gn g b) * (g : ℂ) ^ (a * b)) =
      Fintype.card (Gn g (a + b)) * (α 1 * β 1) := by
  have hP := GlobalTheory.GLm.ParBasic.card_par (g := g) (a := a) (b := b)
  have hne : ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
    exact ⟨1, by simpa using GlobalTheory.GLm.ParBasic.inPar_one (g := g) a (a + b)⟩
  have hs : hc a b α β (a + b) 1 = ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ)⁻¹ *
      (Fintype.card (Gn g (a + b)) * (α 1 * β 1)) := by
    simp only [hc, hcT, mul_one, inv_mul_cancel, Units.val_one, GlobalTheory.GLm.ParBasic.inPar_one, if_true, tl_one, br_one,
      toG_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hP' : ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ) =
      Fintype.card (Gn g a) * Fintype.card (Gn g b) * (g : ℂ) ^ (a * b) := by
    rw [hP]; push_cast; ring
  rw [hs, ← hP']
  field_simp

theorem prodIcc_ne (d : ℕ) : ∏ i ∈ Finset.Icc 1 d, ((g : ℂ) ^ i - 1) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  have : (1 : ℕ) < g ^ i := Nat.one_lt_pow (by omega) hg
  rw [sub_ne_zero]
  exact_mod_cast this.ne'

theorem hc_degree : ∀ (g : ℕ) [Fact g.Prime] (L : List (Pc g)) (n : ℕ), n = degL L → hcL L n 1 * (L.map fun p => ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)).prod = (∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1)) * (L.map fun p => p.2 1).prod := by
  intro g _ L
  induction L with
  | nil =>
    intro n hn
    subst hn
    simp [hcL_nil, degL]
  | cons p L ih =>
    intro n hn
    have hn' : n = p.1 + degL L := by rw [hn]; simp [degL]
    subst hn'
    have h1 := hc_one p.1 (degL L) p.2 (hcL L (degL L))
    have h2 := ih (degL L) rfl
    rw [card_GL_C, card_GL_C, card_GL_C, prod_pow_add] at h1
    have hA := prodIcc_ne (g := g) p.1
    have hB := prodIcc_ne (g := g) (degL L)
    have hG : ∀ d, ∏ i ∈ Finset.range d, (g : ℂ) ^ i ≠ 0 := fun d =>
      Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (by exact_mod_cast (Fact.out : g.Prime).ne_zero)
    have hg0 : (g : ℂ) ^ (p.1 * degL L) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : g.Prime).ne_zero)
    simp only [List.map_cons, List.prod_cons, hcL_cons]
    set A := ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)
    set B := ∏ i ∈ Finset.Icc 1 (degL L), ((g : ℂ) ^ i - 1)
    set C := ∏ i ∈ Finset.Icc 1 (p.1 + degL L), ((g : ℂ) ^ i - 1)
    set Ga := ∏ i ∈ Finset.range p.1, (g : ℂ) ^ i
    set Gb := ∏ i ∈ Finset.range (degL L), (g : ℂ) ^ i
    set X := hc p.1 (degL L) p.2 (hcL L (degL L)) (p.1 + degL L) 1
    set Y := (L.map fun p => ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)).prod
    set Z := (L.map fun p => p.2 1).prod

    have key : X * (A * B) = C * (p.2 1 * hcL L (degL L) 1) := by
      apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (hG p.1) (hG (degL L))) hg0)
      linear_combination h1
    calc X * (A * Y) = X * (A * B) * Y / B := by field_simp
      _ = C * (p.2 1 * (hcL L (degL L) 1 * Y)) / B := by rw [key]; ring
      _ = C * (p.2 1 * Z) := by rw [h2]; field_simp

end GlobalTheory.GLq.HcDeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListDegreeStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraProductList_degree : ∀ (g : ℕ) [Fact g.Prime] (L : List (Pc g)) (n : ℕ), n = degL L → hcL L n 1 * (L.map fun p => ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)).prod = (∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1)) * (L.map fun p => p.2 1).prod := by
  first | exact @GlobalTheory.GLq.HcDeg.hc_degree | exact GlobalTheory.GLq.HcDeg.hc_degree | (intros; apply GlobalTheory.GLq.HcDeg.hc_degree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbWInjective
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

namespace GlobalTheory.PrismS

variable {l : ℕ} [Fact l.Prime]

abbrev unr (K : FinExt l) : FinExt l :=
  ⟨K0 K, by
    have := K.2
    exact FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))⟩

abbrev WK (K : FinExt l) : Type := ↥(OL (unr K))

def embW {K LL : FinExt l} (e : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) : WK K →ₐ[ℤ_[l]] ↥(OL LL) :=
  (e.restrictScalars ℤ_[l]).mapIntegralClosure

theorem embW_injective {K LL : FinExt l} (e : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) : Function.Injective (embW e) :=
  fun _ _ h => Subtype.ext (e.toRingHom.injective (congrArg Subtype.val h))

def letEmb {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) :
    PowerSeries (WK K) →+* LetA ↥(OL LL) n :=
  RingHom.pi fun i => PowerSeries.map (embW (emb i)).toRingHom

theorem letEmb_apply {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (x : PowerSeries (WK K)) (i : ZMod n) :
    letEmb emb x i = PowerSeries.map (embW (emb i)).toRingHom x := rfl

end GlobalTheory.PrismS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatFinrankKs
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

theorem padicValNat_finrank_Ks : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), (∀ m : ℕ, 0 < m → padicValNat l (finrank ℚ_[l] ↥(Loc.Ks K m)) - padicValNat l (finrank ℚ_[l] ↥(Loc.Ks K 1)) = m - 1) ∧ (K.1 ≤ Loc.MaximalUnramifiedExtension l → padicValNat l (finrank ℚ_[l] ↥(Loc.Ks K 1)) - padicValNat l (finrank ℚ_[l] ↥K.1) = 0) := by
  intro l _ K
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl1 : l - 1 ≠ 0 := by omega
  have hpow : ∀ n : ℕ, l ^ n ≠ 0 := fun n => pow_ne_zero n (by omega)

  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hle : Loc.K0 K ≤ K.1 := by unfold Loc.K0; exact inf_le_left
  haveI : FiniteDimensional ℚ_[l] ↥(Loc.K0 K) :=
    Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  have hk0 : finrank ℚ_[l] ↥(Loc.K0 K) ≠ 0 := Module.finrank_pos.ne'
  refine ⟨fun m hm => ?_, fun hK => ?_⟩
  ·
    rw [finrank_Ks_eq l K m hm, finrank_Ks_eq l K 1 one_pos,
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hk0 (Nat.mul_ne_zero (hpow _) hl1),
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hk0 (Nat.mul_ne_zero (hpow _) hl1),
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (hpow _) hl1, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (hpow _) hl1,
      (show ∀ n : ℕ, padicValNat l (l ^ n) = n from fun n => by simpa only [Nat.padicValNat_def] using Nat.multiplicity_prime_pow (p := l) n),
      (show ∀ n : ℕ, padicValNat l (l ^ n) = n from fun n => by simpa only [Nat.padicValNat_def] using Nat.multiplicity_prime_pow (p := l) n)]
    omega
  ·
    have heq : Loc.K0 K = K.1 := by unfold Loc.K0; exact inf_eq_left.mpr hK
    have hK1 : finrank ℚ_[l] ↥K.1 ≠ 0 := Module.finrank_pos.ne'
    have hv : padicValNat l (l - 1) = 0 :=
      by
        apply (Nat.padicValNat_def).trans
        exact padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    rw [finrank_Ks_eq l K 1 one_pos, heq, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hK1 (Nat.mul_ne_zero (hpow _) hl1),
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (hpow _) hl1, (show ∀ n : ℕ, padicValNat l (l ^ n) = n from fun n => by simpa only [Nat.padicValNat_def] using Nat.multiplicity_prime_pow (p := l) n), hv]
    omega

end GlobalTheory.HubLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDetResMat
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR

variable {l : ℕ} [Fact l.Prime] {r : ℕ}

def frobMat (ω : Fin r → ↥(MaximalUnramifiedExtension l)) : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l) := Matrix.of fun m k => fr l m (ω k)

def resMat (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l)) :
    Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) :=
  Matrix.kroneckerMap (· * ·) (1 : Matrix n n ↥(MaximalUnramifiedExtension l)) (frobMat ω)

theorem resMat_apply (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (a b : n × Fin r) :
    resMat n ω a b = if a.1 = b.1 then fr l a.2 (ω b.2) else 0 := by
  simp [resMat, frobMat, Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem isUnit_det_resMat (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l))
    (hdet : (frobMat ω).det ≠ 0) : IsUnit (resMat n ω).det := by
  rw [resMat, Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul]
  exact (isUnit_iff_ne_zero.2 hdet).pow _

def resGL (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hdet : (frobMat ω).det ≠ 0) :
    GL (n × Fin r) ↥(MaximalUnramifiedExtension l) :=
  Matrix.GeneralLinearGroup.mk'' (resMat n ω) (isUnit_det_resMat n ω hdet)

def blockGL {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (U : Fin r → GL n R) :
    GL (n × Fin r) R where
  val := Matrix.blockDiagonal fun m => (U m : Matrix n n R)
  inv := Matrix.blockDiagonal fun m => (((U m)⁻¹ : GL n R) : Matrix n n R)
  val_inv := by rw [← Matrix.blockDiagonal_mul]; simp only [Units.mul_inv]; exact Matrix.blockDiagonal_one
  inv_val := by rw [← Matrix.blockDiagonal_mul]; simp only [Units.inv_mul]; exact Matrix.blockDiagonal_one

variable (P : LocPrime l) {n : Type} [Fintype n] [DecidableEq n]

def U0 (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hdet : (frobMat ω).det ≠ 0) (U : Fin r → GL n P.R.BdR) : GL (n × Fin r) P.R.BdR :=
  (Units.map ((kd P).mapMatrix : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) →+* Matrix (n × Fin r) (n × Fin r) P.R.BdR).toMonoidHom
    (resGL n ω hdet))⁻¹ * blockGL U

def Ymat (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (A₀ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B :=
  (resMat n ω).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) * (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B)

def colv (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (A₀ : GL (n × Fin r) P.R.B) (c : n × Fin r) (i : n) : P.R.B :=
  ∑ k, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (ω k) * (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) (i, k) c

def LatC (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (a : n → P.R.B) : Prop :=
  (∀ i, P.φB^[r] (a i) = a i) ∧ ∀ m : Fin r, ∃ w : n → P.R.BdR, (∀ i, w i ∈ Fil P 0) ∧
    (fun i => ev P m (a i)) = ((U m : Matrix n n P.R.BdR) * Matrix.diagonal fun j => tz P (eps x y (m, j))).mulVec w

end GlobalTheory.PMon.ResR

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusDoubleSeriesHasSumAndNormBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusDoubleSeriesHasSumAndNormBounds
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem Lam_main : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (y : ℕ → Fl l), 1 ≤ h → r < 1 → (∀ k, ‖sh (y k)‖ ≤ r) → HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) ∧ ‖abelian₂ h j y - lam h j (y 0)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r ∧ ‖abelian₂ h j y‖ ≤ gam l h j r ∧ ∀ N : ℕ, abelian₂ h j (fun k => y k ^ l ^ (h * N)) = (l : ℂ_[l]) ^ N * abelian₂ h j y := by
  intro l _ h j r y hh hr hy
  have hl : ‖(l : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt
  have hl0 : 0 ≤ ‖(l : ℂ_[l])‖ := norm_nonneg _
  have hlam : ∀ k, ‖lam h j (y k)‖ ≤ gam l h j r := fun k =>
    (GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h j r (y k) hh hr (hy k)).2.1
  have hterm : ∀ k : ℕ, ‖(l : ℂ_[l]) ^ k * lam h j (y k)‖ ≤ ‖(l : ℂ_[l])‖ ^ k * gam l h j r := by
    intro k
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (hlam k) (pow_nonneg hl0 k)
  have hsum : Summable (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hl0 hl).mul_right _) hterm
  have hHas : HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) := hsum.hasSum
  have hg0 : 0 ≤ gam l h j r := le_trans (norm_nonneg _) (hlam 0)
  refine ⟨hHas, ?_, ?_, ?_⟩
  · have := GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le ℂ_[l] ℕ (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) {0}
      (‖(l : ℂ_[l])‖ * gam l h j r) (mul_nonneg hl0 hg0) hHas (by
        intro k hk
        have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by simpa using hk)
        refine le_trans (hterm k) (mul_le_mul_of_nonneg_right ?_ hg0)
        simpa using pow_le_pow_of_le_one hl0 hl.le hk1)
    simpa using this
  · have := GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le ℂ_[l] ℕ (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) ∅
      (gam l h j r) hg0 hHas (by
        intro k _
        refine le_trans (hterm k) ?_
        calc ‖(l : ℂ_[l])‖ ^ k * gam l h j r ≤ 1 * gam l h j r :=
              mul_le_mul_of_nonneg_right (pow_le_one₀ hl0 hl.le) hg0
          _ = gam l h j r := one_mul _)
    simpa using this
  · have hsh := GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l

    have key : ∀ (N : ℕ) (x : Fl l), ‖sh x‖ ≤ r → lam h j (x ^ l ^ (h * N)) = (l : ℂ_[l]) ^ N * lam h j x := by
      intro N
      induction N with
      | zero => intro x _; simp
      | succ N ih =>
        intro x hx
        have hx' : ‖sh (x ^ l ^ (h * N))‖ ≤ r := by
          rw [hsh.2.2.2.1, norm_pow]
          have h1 : ‖sh x‖ ≤ 1 := hsh.2.2.2.2.1 x
          have hpos : 1 ≤ l ^ (h * N) := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
          exact le_trans (pow_le_of_le_one (norm_nonneg _) h1 (by omega)) hx
        have e : x ^ l ^ (h * (N + 1)) = (x ^ l ^ (h * N)) ^ l ^ h := by
          rw [← pow_mul, ← pow_add, Nat.mul_succ]
        rw [e, (GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h j r _ hh hr hx').2.2.1, ih x hx, pow_succ]
        ring
    intro N
    unfold abelian₂
    rw [← tsum_mul_left]
    congr 1
    funext k
    rw [key N (y k) (hy k)]
    ring

end GlobalTheory.PSer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusDoubleSeriesHasSumAndNormBoundsStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untiltFrobeniusDoubleSeries_hasSum_and_norm_bounds : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (y : ℕ → Fl l), 1 ≤ h → r < 1 → (∀ k, ‖sh (y k)‖ ≤ r) → HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) ∧ ‖abelian₂ h j y - lam h j (y 0)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r ∧ ‖abelian₂ h j y‖ ≤ gam l h j r ∧ ∀ N : ℕ, abelian₂ h j (fun k => y k ^ l ^ (h * N)) = (l : ℂ_[l]) ^ N * abelian₂ h j y := by
  first | exact @GlobalTheory.PSer.Lam_main | exact GlobalTheory.PSer.Lam_main | (intros; apply GlobalTheory.PSer.Lam_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltAddEstimateLe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltInjectiveAndDvdOfNormLe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltInjectiveAndDvdOfNormLe
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem untilt_injective_zero_and_dvd_of_norm_sh_le :
    ∀ (l : ℕ) [Fact l.Prime], (∀ x : Fl l, sh x = 0 → x = 0) ∧
      ∀ x y : Fl l, ‖sh x‖ ≤ ‖sh y‖ → y ∣ x := by
  intro l _
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_tiltIntegersCpEquiv_compatible_untilt l
  refine ⟨fun x hx => ?_, fun x y hxy => ?_⟩
  · have h0 : e x = 0 := GroundTheory.PAdicHodge.untilt_eq_zero_iff.1 (by rw [he]; exact hx)
    exact e.injective (by rw [h0, map_zero])
  · have hd : e y ∣ e x := by
      rw [GroundTheory.PAdicHodge.preTilt_dvd_iff_norm_le, GroundTheory.PAdicHodge.preTilt_norm_def,
        GroundTheory.PAdicHodge.preTilt_norm_def, he, he]
      exact hxy
    obtain ⟨c, hc⟩ := hd
    exact ⟨e.symm c, e.injective (by rw [map_mul, e.apply_symm_apply, hc])⟩

end GlobalTheory.PSer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltInjectiveAndDvdOfNormLeStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_untilt_injective_and_dvd_of_norm_le : ∀ (l : ℕ) [Fact l.Prime], (∀ x : Fl l, sh x = 0 → x = 0) ∧ ∀ x y : Fl l, ‖sh x‖ ≤ ‖sh y‖ → y ∣ x := by
  first | exact @GlobalTheory.PSer.untilt_injective_zero_and_dvd_of_norm_sh_le | exact GlobalTheory.PSer.untilt_injective_zero_and_dvd_of_norm_sh_le | (intros; apply GlobalTheory.PSer.untilt_injective_zero_and_dvd_of_norm_sh_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltAddEstimateLe
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem tiltUntilt_add_estimate_of_norm_le (l : ℕ) [Fact l.Prime] (x y : Fl l) (hxy : ‖sh x‖ ≤ ‖sh y‖) :
    ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖ * ‖sh y‖ ∧ ‖sh (x + y)‖ ≤ ‖sh y‖ := by
  obtain ⟨h1, -, hmul, -, hle1, -, hadd, -⟩ := GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l
  obtain ⟨u, rfl⟩ := (GlobalTheory.T.tilt_untilt_injective_and_dvd_of_norm_le l).2 x y hxy
  have hsum : y * u + y = y * (u + 1) := by ring
  rw [hsum, hmul, hmul]
  constructor
  · have key : sh y * sh (u + 1) - sh y * sh u - sh y
        = sh y * (sh (u + 1) - sh u - sh (1 : Fl l)) := by rw [h1]; ring
    rw [key, norm_mul, mul_comm ‖(l : ℂ_[l])‖]
    exact mul_le_mul_of_nonneg_left (hadd u 1) (norm_nonneg _)
  · rw [norm_mul]
    calc ‖sh y‖ * ‖sh (u + 1)‖ ≤ ‖sh y‖ * 1 :=
          mul_le_mul_of_nonneg_left (hle1 _) (norm_nonneg _)
      _ = ‖sh y‖ := mul_one _

theorem sh_add_le : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ) (x y : Fl l), ‖sh x‖ ≤ r → ‖sh y‖ ≤ r →
    ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖ * r ∧ ‖sh (x + y)‖ ≤ r := by
  intro l _ r x y hx hy
  have hl : 0 ≤ ‖(l : ℂ_[l])‖ := norm_nonneg _
  rcases le_total ‖sh x‖ ‖sh y‖ with h | h
  · obtain ⟨h1, h2⟩ := tiltUntilt_add_estimate_of_norm_le l x y h
    exact ⟨h1.trans (mul_le_mul_of_nonneg_left hy hl), h2.trans hy⟩
  · obtain ⟨h1, h2⟩ := tiltUntilt_add_estimate_of_norm_le l y x h
    rw [add_comm x y]
    refine ⟨?_, h2.trans hx⟩
    have e : sh (y + x) - sh x - sh y = sh (y + x) - sh y - sh x := by ring
    rw [e]
    exact h1.trans (mul_le_mul_of_nonneg_left hx hl)

end GlobalTheory.PSer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltAddEstimateLeStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tiltUntilt_add_estimate_le : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ) (x y : Fl l), ‖sh x‖ ≤ r → ‖sh y‖ ≤ r → ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖ * r ∧ ‖sh (x + y)‖ ≤ r := by
  first | exact @GlobalTheory.PSer.sh_add_le | exact GlobalTheory.PSer.sh_add_le | (intros; apply GlobalTheory.PSer.sh_add_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedSubringTensorWittSaturatedComplete
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedSubringTensorWittSaturatedComplete
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl.FixL

theorem fix_of_mul {R : Type} [CommRing R] (p : ℕ) (h : ∀ x : R, (p : R) * x = 0 → x = 0)
    (f : R →+* R) (x : R) (hx : f ((p : R) * x) = (p : R) * x) : f x = x := by
  have hf : f (p : R) = (p : R) := map_natCast f p
  have h2 : (p : R) * (f x - x) = 0 := by
    rw [mul_sub, ← hf, ← map_mul, hx, hf, sub_self]
  exact sub_eq_zero.mp (h _ h2)

theorem fix_of_sum {R : Type} [CommRing R] (p : ℕ)
    (h : ∀ x : R, (∀ k : ℕ, ∃ r, x = (p : R) ^ k * r) → x = 0)
    (f : R →+* R) (x : ℕ → R) (hx : ∀ i, f (x i) = x i) (y : R)
    (hy : ∀ k : ℕ, ∃ r, y - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r) :
    f y = y := by
  apply sub_eq_zero.mp
  apply h
  intro k
  obtain ⟨r, hr⟩ := hy k
  have hsum : f (∑ i ∈ Finset.range k, (p : R) ^ i * x i) = ∑ i ∈ Finset.range k, (p : R) ^ i * x i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_mul, map_pow, map_natCast, hx]
  have hfy : f y - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * f r := by
    rw [← hsum, ← map_sub, hr, map_mul, map_pow, map_natCast]
  refine ⟨f r - r, ?_⟩
  rw [mul_sub, ← hfy, ← hr]
  ring

theorem frob_comm {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l)
    (g : GQ l) (x : RW LL) : AI.gRW LL g (φRW LL x) = φRW LL (AI.gRW LL g x) := by
  have key : ∀ w : WCb l, AI.actWCbHom g (frobW l w) = frobW l (AI.actWCbHom g w) := by
    intro w
    unfold LocAinf.actWCbHom frobW
    simp only [MonoidHom.coe_mk, OneHom.coe_mk]
    unfold mapAlgEquivW
    ext n
    dsimp only [AlgEquiv.ofRingEquiv]
    simp [mapEquivW, WittVector.map_coeff, frobenius_def]
  have hc : ((AI.actWCbHom g : WCb l →ₐ[ℤ_[l]] WCb l).comp (frobW l)) =
      (frobW l).comp (AI.actWCbHom g : WCb l →ₐ[ℤ_[l]] WCb l) := AlgHom.ext key
  unfold LocAinf.gRW φRW
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp,
    ← Algebra.TensorProduct.map_comp, hc]

private theorem mem_fixSub_lemma {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
    (LL : FinExt l) (H : Set (GQ l)) (x : RW LL) :
    x ∈ fixSub AI LL H ↔ ∀ g ∈ H, AI.gRW LL g x = x := by
  unfold fixSub
  simp [Subring.mem_iInf, RingHom.mem_eqLocus]

theorem fixSub_ladic (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l)
    (H : Set (GQ l)) :
    (∀ x, (l : RW LL) * x ∈ fixSub AI LL H → x ∈ fixSub AI LL H) ∧
    (∀ x ∈ fixSub AI LL H, φRW LL x ∈ fixSub AI LL H) ∧
    ∀ x : ℕ → RW LL, (∀ i, x i ∈ fixSub AI LL H) → ∃ y ∈ fixSub AI LL H, ∀ k : ℕ, ∃ r,
      y - ∑ i ∈ Finset.range k, (l : RW LL) ^ i * x i = (l : RW LL) ^ k * r := by
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.Decompl.LAdic.ladic_RW l LL
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [mem_fixSub_lemma] at hx ⊢
    intro g hg
    exact fix_of_mul l h0 (AI.gRW LL g : RW LL →+* RW LL) x (hx g hg)
  · intro x hx
    rw [mem_fixSub_lemma] at hx ⊢
    intro g hg
    rw [frob_comm, hx g hg]
  · intro x hx
    obtain ⟨s, hs⟩ := h2 x
    refine ⟨s, ?_, hs⟩
    rw [mem_fixSub_lemma]
    intro g hg
    exact fix_of_sum l h1 (AI.gRW LL g : RW LL →+* RW LL) x
      (fun i => (mem_fixSub_lemma AI LL H (x i)).1 (hx i) g hg) s hs

end GlobalTheory.Decompl.FixL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedSubringTensorWittSaturatedCompleteStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisFixedSubringTensorWitt_saturated_complete : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (H : Set (GQ l)), (∀ x, (l : RW LL) * x ∈ fixSub AI LL H → x ∈ fixSub AI LL H) ∧ (∀ x ∈ fixSub AI LL H, φRW LL x ∈ fixSub AI LL H) ∧ ∀ x : ℕ → RW LL, (∀ i, x i ∈ fixSub AI LL H) → ∃ y ∈ fixSub AI LL H, ∀ k : ℕ, ∃ r, y - ∑ i ∈ Finset.range k, (l : RW LL) ^ i * x i = (l : RW LL) ^ k * r := by
  first | exact @GlobalTheory.Decompl.FixL.fixSub_ladic | exact GlobalTheory.Decompl.FixL.fixSub_ladic | (intros; apply GlobalTheory.Decompl.FixL.fixSub_ladic <;> assumption)
end
end

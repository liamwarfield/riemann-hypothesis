module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCSDOfIsEtaT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetNeZeroOfLowestFormNeZeroPresentation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalCocycleRowsRelationNewPlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityRelaxedSelmerDualSelmerNewPlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteLocalRingPolyDividesVarPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmIntOfSupLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDualSelmerClassNotKilled
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerOrderFormulaDualSelmer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmallSubgroupCocycleFormNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqZeroOfLowCoeffOfNilpotentMultipleStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqZeroOfLowCoeffOfNilpotentMultiple
namespace GlobalTheory.NewPrime

theorem aeval_eq_zero_of_low_coeff_of_pow_eq_zero :
    ∀ (O B : Type) [CommRing O] [CommRing B] [Algebra O B] (ι : Type) (t : B) (K : ℕ) (ξ : ι → B)
      (F : MvPolynomial ι O), t ^ K = 0 → (∀ q, t ∣ ξ q) →
      (∀ u : ι →₀ ℕ, u.degree < K → algebraMap O B (F.coeff u) = 0) →
      MvPolynomial.aeval ξ F = 0 := by
  intro O B _ _ _ ι t K ξ F htK hdvd hlow
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Finset.sum_eq_zero fun u _ => ?_
  by_cases hu : u.degree < K
  · rw [hlow u hu, zero_mul]
  ·
    have hmon : t ^ u.degree ∣ ∏ i ∈ u.support, ξ i ^ u i := by
      rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ => pow_dvd_pow_of_dvd (hdvd i) _
    have hK : t ^ K ∣ ∏ i ∈ u.support, ξ i ^ u i :=
      (pow_dvd_pow t (not_lt.mp hu)).trans hmon
    rw [htK, zero_dvd_iff] at hK
    rw [hK, mul_zero]

end GlobalTheory.NewPrime
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_eq_zero_of_low_coeff_of_nilpotent_multiple : ∀ (O B : Type) [CommRing O] [CommRing B] [Algebra O B] (ι : Type) (t : B) (K : ℕ) (ξ : ι → B) (F : MvPolynomial ι O), t ^ K = 0 → (∀ q, t ∣ ξ q) → (∀ u : ι →₀ ℕ, u.degree < K → algebraMap O B (F.coeff u) = 0) → MvPolynomial.aeval ξ F = 0 := by
  first | exact @GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_pow_eq_zero | exact GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_pow_eq_zero | (intros; apply GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_pow_eq_zero <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRingSqZeroNilpotentAugmentedStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRingSqZeroNilpotentAugmented
open Polynomial

namespace GlobalTheory.SqZeroPow

theorem dual_decomp {R : Type} [CommRing R] (b : DualNumber R) (r s : R) (h : r * s = b.fst) :
    TrivSqZeroExt.inl b.snd * (DualNumber.eps : DualNumber R)
      + TrivSqZeroExt.inl s * TrivSqZeroExt.inl r = b := by
  ext <;> simp [← h, mul_comm]

theorem dual_fst_of_eps_mul {R : Type} [CommRing R] (f : DualNumber R) (r : R) (n : ℕ)
    (h : (DualNumber.eps : DualNumber R) * (TrivSqZeroExt.inl r) ^ n * f = 0) :
    r ^ n * f.fst = 0 := by
  have hs := congrArg TrivSqZeroExt.snd h
  simpa [mul_comm] using hs

theorem dual_inl_pow {R : Type} [CommRing R] (r : R) (n : ℕ) (h : r ^ n = 0) :
    (TrivSqZeroExt.inl r : DualNumber R) ^ n = 0 := by
  rw [TrivSqZeroExt.inl_pow, h, TrivSqZeroExt.inl_zero]

theorem exists_ring (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (m : ℕ) (hm : 0 < m) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra O B) (j : A →ₐ[O] B) (π : B →ₐ[O] A) (x y : B),
      (∀ a, π (j a) = a) ∧ (∀ b, π b = 0 → b ∈ Ideal.span {x, y}) ∧ π x = 0 ∧ π y = 0 ∧
      x * x = 0 ∧ y ^ m = 0 ∧ ∀ f, x * y ^ (m - 1) * f = 0 → π f = 0 := by
  classical
  have h0 : (X ^ m : A[X]).eval₂ (AlgHom.id O A : A →+* A) 0 = 0 := by
    simp [zero_pow (Nat.pos_iff_ne_zero.mp hm)]
  obtain ⟨g, hg⟩ : ∃ g : AdjoinRoot (X ^ m : A[X]) →ₐ[O] A,
      ∀ p : A[X], g (AdjoinRoot.mk _ p) = p.coeff 0 :=
    ⟨AdjoinRoot.liftAlgHom _ (AlgHom.id O A) 0 h0, fun p => by
      rw [AdjoinRoot.liftAlgHom_mk, Polynomial.eval₂_at_zero]
      rfl⟩
  have hroot : (AdjoinRoot.root (X ^ m : A[X])) ^ m = 0 := by
    have hself : AdjoinRoot.mk (X ^ m : A[X]) (X ^ m) = 0 := AdjoinRoot.mk_self
    rwa [map_pow, AdjoinRoot.mk_X] at hself
  refine ⟨DualNumber (AdjoinRoot (X ^ m : A[X])), inferInstance, inferInstance,
    (TrivSqZeroExt.inlAlgHom O _ _).comp (IsScalarTower.toAlgHom O A _),
    g.comp (TrivSqZeroExt.fstHom O _ _),
    DualNumber.eps, TrivSqZeroExt.inl (AdjoinRoot.root _), ?_, ?_, ?_, ?_,
    DualNumber.eps_mul_eps, dual_inl_pow _ _ hroot, ?_⟩
  · intro a
    simp only [AlgHom.comp_apply, TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.fstHom_apply,
      TrivSqZeroExt.fst_inl, IsScalarTower.toAlgHom_apply]
    rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, hg, Polynomial.coeff_C_zero]
  · intro b hb
    simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply] at hb
    obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective b.fst
    rw [← hp, hg] at hb
    obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.mpr hb
    have hq : AdjoinRoot.root (X ^ m : A[X]) * AdjoinRoot.mk _ q = b.fst := by
      rw [← hp, map_mul, AdjoinRoot.mk_X]
    have e := dual_decomp b _ _ hq
    rw [← e]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)) <;> simp
  · simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply, DualNumber.fst_eps, map_zero]
  · simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply, TrivSqZeroExt.fst_inl]
    rw [← AdjoinRoot.mk_X, hg, Polynomial.coeff_X_zero]
  · intro f hf
    have h1 := dual_fst_of_eps_mul f _ (m - 1) hf
    simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply]
    obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective f.fst
    have e : AdjoinRoot.root (X ^ m : A[X]) ^ (m - 1) * AdjoinRoot.mk _ p
        = AdjoinRoot.mk _ (X ^ (m - 1) * p) := by
      rw [map_mul, map_pow, AdjoinRoot.mk_X]
    rw [← hp, e, AdjoinRoot.mk_eq_zero, Polynomial.X_pow_dvd_iff] at h1
    have h2 := h1 (m - 1) (Nat.sub_lt hm Nat.one_pos)
    rw [Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self] at h2
    rw [← hp, hg]
    exact h2

end GlobalTheory.SqZeroPow
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ring_sq_zero_nilpotent_augmented : ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (m : ℕ), 0 < m → ∃ (B : Type) (_ : CommRing B) (_ : Algebra O B) (j : A →ₐ[O] B) (π : B →ₐ[O] A) (x y : B), (∀ a, π (j a) = a) ∧ (∀ b, π b = 0 → b ∈ Ideal.span {x, y}) ∧ π x = 0 ∧ π y = 0 ∧ x * x = 0 ∧ y ^ m = 0 ∧ ∀ f, x * y ^ (m - 1) * f = 0 → π f = 0 := by
  first | exact @GlobalTheory.SqZeroPow.exists_ring | exact GlobalTheory.SqZeroPow.exists_ring | (intros; apply GlobalTheory.SqZeroPow.exists_ring <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCConj
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet

namespace GlobalTheory.NewPrime

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem exists_isDual (i : X.Tw) (s : X.Sig i) : ∃ ρ, IsDual i s ρ := by
  have hu : ∀ g, IsUnit (Tmat i s g).det := fun g => by
    rw [← Tgl_coe]; exact Matrix.isUnits_det_units _
  let τ : GE N →* Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) :=
    { toFun := Tdual i s
      map_one' := by
        rw [Tdual, ← Tgl_coe, map_one, map_one]; simp
      map_mul' := fun g h => by
        simp only [Tdual, ← Tgl_coe, map_mul, Units.val_mul, Matrix.mul_inv_rev, Matrix.transpose_mul, smul_mul_smul_comm] }
  exact ⟨τ.toHomUnits, fun g => rfl⟩


end GlobalTheory.NewPrime
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupOfFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupOfFactor
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime

theorem setup_of_factor : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (M : ℕ) (ι : Type) [Fintype ι] (P : ι → PlE D.host) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ Q : Finset (PlE D.host)), SlopeTestRemainingChoices X i M A₀ P d → IsQ P Q → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ), Kills i A → (∀ g, (∀ q, d q g = 1) → κ g = 1) → Setup bkP i s κ Q ∧ AntiHom X.cc κ ∧ ∀ z, IsTameInertiaElementAtTwistPrime X i z → κ z = 1 := by
  intro D N X bkP i s hG M ι _ P d A₀ Q hA hQ A _ _ _ _ κ _ h1
  have hfin : Module.Finite (X.O0 i) A := Module.Finite.of_finite
  refine ⟨⟨hG, ⟨fun x hx => ?_⟩, hfin, ?_, fun g => ⟨M, ?_⟩, fun v hv B hB σ hσ => h1 σ fun q => ?_, fun v hv hl => ?_,
    fun v hv B hB σ hσ => h1 σ fun q => ?_⟩, fun g g' hg => ?_, ?_⟩
  · by_contra hn
    have h : IsLocalRing.maximalIdeal (X.O0 i) ≤ (IsLocalRing.maximalIdeal A).comap (algebraMap (X.O0 i) A) :=
      (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
        Algebra.IsIntegral.isIntegral (IsLocalRing.maximalIdeal A))).ge
    exact h hn hx
  · refine Subgroup.isOpen_mono (H₁ := ⨅ q, (d q).ker) (fun g hg => h1 g fun q => Subgroup.mem_iInf.1 hg q) ?_
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun q => (hA.2.2 q).1
  · rw [← map_pow]
    refine h1 _ fun q => ?_
    rw [map_pow]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, toAdd_one]
  · exact (hA.2.2 q).2.2.1 v hv B hB σ hσ
  · obtain ⟨q, hq⟩ := (hQ v).1 hv
    exact (hA.1 q v hq).2.2.2.1 (X.twistExcludedPlaces_contains_residueChar i hl)
  · exact (hA.2.2 q).2.2.2.1 v (fun hq => hv ((hQ v).2 ⟨q, hq⟩)) B hB σ hσ
  · rw [eq_inv_iff_mul_eq_one, ← map_mul]
    refine h1 _ fun q => ?_
    rw [map_mul, (hA.2.2 q).2.1 g g' hg, inv_mul_cancel]
  · rintro z ⟨v, hv, B, hB, hz, -⟩
    exact h1 z fun q => (hA.2.2 q).2.2.2.1 v (fun hq => (hA.1 q v hq).2.2.2.1 (X.primes_subset_exceptional i hv)) B hB z hz

end GlobalTheory.NewPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupOfFactorStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setup_and_antiHom_of_kills : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (M : ℕ) (ι : Type) [Fintype ι] (P : ι → PlE D.host) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ Q : Finset (PlE D.host)), SlopeTestRemainingChoices X i M A₀ P d → IsQ P Q → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ), Kills i A → (∀ g, (∀ q, d q g = 1) → κ g = 1) → Setup bkP i s κ Q ∧ AntiHom X.cc κ ∧ ∀ z, IsTameInertiaElementAtTwistPrime X i z → κ z = 1 := by
  first | exact @GlobalTheory.NewPrime.setup_of_factor | exact GlobalTheory.NewPrime.setup_of_factor | (intros; apply GlobalTheory.NewPrime.setup_of_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLambdaAlgebraHomEvaluation
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLambdaAlgebraHomEvaluation
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.LamHom

def chr {B ι : Type} [CommRing B] [Fintype ι] {n : ℕ} [NeZero n] (u : ι → B) (hu : ∀ q, u q ^ n = 1) :
    Multiplicative (ι → ZMod n) →* B := GlobalTheory.RootCharacter.rootChar u hu

theorem chr_single {B ι : Type} [CommRing B] [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n] (hn : 1 < n) (u : ι → B)
    (hu : ∀ q, u q ^ n = 1) (q : ι) : chr u hu (Multiplicative.ofAdd (Pi.single q 1)) = u q := by
  haveI : Fact (1 < n) := ⟨hn⟩
  change ∏ p, u p ^ ((Pi.single q (1 : ZMod n) : ι → ZMod n) p).val = u q
  rw [Finset.prod_eq_single q]
  · simp [ZMod.val_one]
  · intro p _ hp
    simp [Pi.single_eq_of_ne hp]
  · simp

theorem exists_lamHom : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (B : Type) [CommRing B] [Algebra (X.O0 i) B] (ξ : ι → B), 0 < nu X i → nu X i + 1 ≤ M → Kills i B → (∀ q, ξ q ^ X.l i ^ (M - nu X i - 1) = 0) → ∃ φ : abelian₂ X i M ι →ₐ[X.O0 i] B, (∀ F, φ (toLam X i M ι F) = MvPolynomial.aeval ξ F) ∧ ∀ d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M))), ∃ κ : GE N →* Bˣ, (∀ g, ((κ g : Bˣ) : B) = φ (delInv i M d g : (abelian₂ X i M ι)ˣ)) ∧ IsChar i κ ξ d := by
  intro D N X i M ι _ B _ _ ξ _ hM hK hξ
  classical
  have hp : (X.l i).Prime := (X.lPrime i).out
  have hm : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := fun hu =>
    X.O_l i (by simpa using hu.map (algebraMap (X.O0 i) (X.O i)))
  have h4 : ((X.l i : ℕ) : B) ^ (nu X i + 1) = 0 := by
    have h := hK _ (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hm)
    rw [map_mul, map_pow, map_natCast] at h
    rw [pow_succ]
    exact h
  have hn : 1 < X.l i ^ M := Nat.one_lt_pow (by omega) hp.one_lt
  haveI : NeZero (X.l i ^ M) := ⟨by omega⟩
  have hu : ∀ q, (1 + ξ q) ^ (X.l i ^ M) = 1 := fun q =>
    KStar.Tree.one_add_pow_prime_pow_eq_one hp h4 hM (hξ q)
  let φ : abelian₂ X i M ι →ₐ[X.O0 i] B := MonoidAlgebra.lift (X.O0 i) B (Del X i M ι) (chr (fun q => 1 + ξ q) hu)
  have hφ : ∀ x, φ (MonoidAlgebra.of (X.O0 i) (Del X i M ι) x) = chr (fun q => 1 + ξ q) hu x := fun x =>
    MonoidAlgebra.lift_of _ x
  refine ⟨φ, fun F => ?_, fun d => ⟨(Units.map (φ : abelian₂ X i M ι →* B)).comp (delInv i M d), fun g => rfl, fun g => ?_⟩⟩
  · have : φ.comp (toLam X i M ι) = MvPolynomial.aeval ξ := by
      refine MvPolynomial.algHom_ext fun q => ?_
      rw [AlgHom.comp_apply, toLam, MvPolynomial.aeval_X, MvPolynomial.aeval_X, map_sub, map_one, hφ]
      have := chr_single hn (fun q => 1 + ξ q) hu q
      rw [sub_eq_iff_eq_add']
      convert this
    exact DFunLike.congr_fun this F
  · have h1 : ((delInv i M d g : (abelian₂ X i M ι)ˣ) : abelian₂ X i M ι) *
        MonoidAlgebra.of (X.O0 i) (Del X i M ι) (delAll X i M d g) = 1 :=
      Units.inv_mul ((MonoidAlgebra.of (X.O0 i) (Del X i M ι)).toHomUnits (delAll X i M d g))
    have h2 := congrArg φ h1
    rw [map_mul, map_one, hφ] at h2
    exact h2

end GlobalTheory.NewPrime.LamHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLambdaAlgebraHomEvaluationStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lambda_algebra_hom_evaluation : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (B : Type) [CommRing B] [Algebra (X.O0 i) B] (ξ : ι → B), 0 < nu X i → nu X i + 1 ≤ M → Kills i B → (∀ q, ξ q ^ X.l i ^ (M - nu X i - 1) = 0) → ∃ φ : abelian₂ X i M ι →ₐ[X.O0 i] B, (∀ F, φ (toLam X i M ι F) = MvPolynomial.aeval ξ F) ∧ ∀ d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M))), ∃ κ : GE N →* Bˣ, (∀ g, ((κ g : Bˣ) : B) = φ (delInv i M d g : (abelian₂ X i M ι)ˣ)) ∧ IsChar i κ ξ d := by
  first | exact @GlobalTheory.NewPrime.LamHom.exists_lamHom | exact GlobalTheory.NewPrime.LamHom.exists_lamHom | (intros; apply GlobalTheory.NewPrime.LamHom.exists_lamHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqZeroLowCoeffThreeNilpotents
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqZeroLowCoeffThreeNilpotents
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime

theorem exists_pow_mul_pow_mul_pow_dvd_prod_pow {B : Type} [CommRing B] {ι : Type} (t x y : B)
    (ξ : ι → B) (hξ : ∀ q, t ∣ ξ q ∨ ξ q = x ∨ ξ q = y) (u : ι → ℕ) (s : Finset ι) :
    ∃ a b c : ℕ, a + b + c = ∑ q ∈ s, u q ∧ t ^ a * x ^ b * y ^ c ∣ ∏ q ∈ s, ξ q ^ u q := by
  classical
  induction s using Finset.induction_on
  case empty => exact ⟨0, 0, 0, by simp, by simp⟩
  case insert q s hq ih =>
    obtain ⟨a, b, c, habc, hd⟩ := ih
    rw [Finset.sum_insert hq, Finset.prod_insert hq]
    rcases hξ q with ⟨r, hr⟩ | hx | hy
    · refine ⟨u q + a, b, c, by omega, ?_⟩
      have h := mul_dvd_mul (dvd_mul_right (t ^ u q) (r ^ u q)) hd
      rw [hr, mul_pow]
      convert h using 1
      ring
    · refine ⟨a, u q + b, c, by omega, ?_⟩
      have h := mul_dvd_mul_left (x ^ u q) hd
      rw [hx]
      convert h using 1
      ring
    · refine ⟨a, b, u q + c, by omega, ?_⟩
      have h := mul_dvd_mul_left (y ^ u q) hd
      rw [hy]
      convert h using 1
      ring

theorem aeval_eq_zero_of_low_coeff_of_three_nilpotent :
    ∀ (O B : Type) [CommRing O] [CommRing B] [Algebra O B] (ι : Type) (t x y : B) (K m : ℕ)
      (ξ : ι → B) (F : MvPolynomial ι O), t ^ K = 0 → x * x = 0 → y ^ m = 0 →
      (∀ q, t ∣ ξ q ∨ ξ q = x ∨ ξ q = y) →
      (∀ u : ι →₀ ℕ, u.degree < K + m → algebraMap O B (F.coeff u) = 0) →
      MvPolynomial.aeval ξ F = 0 := by
  intro O B _ _ _ ι t x y K m ξ F ht hx hy hξ hF
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [F.as_sum, map_sum]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [MvPolynomial.aeval_monomial]
  by_cases hu : u.degree < K + m
  · rw [hF u hu, zero_mul]
  · obtain ⟨a, b, c, habc, hd⟩ := exists_pow_mul_pow_mul_pow_dvd_prod_pow t x y ξ hξ u u.support
    have hdeg : u.degree = ∑ q ∈ u.support, u q := rfl
    have hzero : t ^ a * x ^ b * y ^ c = 0 := by
      by_cases hc : m ≤ c
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
        rw [pow_add, hy]
        simp
      · by_cases hb : 2 ≤ b
        · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
          rw [pow_add, pow_two, hx]
          simp
        · have hK : K ≤ a := by omega
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hK
          rw [pow_add, ht]
          simp
    rw [hzero, zero_dvd_iff] at hd
    rw [Finsupp.prod]
    simp only [hd, mul_zero]

end GlobalTheory.NewPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqZeroLowCoeffThreeNilpotentsStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_eq_zero_low_coeff_three_nilpotents : ∀ (O B : Type) [CommRing O] [CommRing B] [Algebra O B] (ι : Type) (t x y : B) (K m : ℕ) (ξ : ι → B) (F : MvPolynomial ι O), t ^ K = 0 → x * x = 0 → y ^ m = 0 → (∀ q, t ∣ ξ q ∨ ξ q = x ∨ ξ q = y) → (∀ u : ι →₀ ℕ, u.degree < K + m → algebraMap O B (F.coeff u) = 0) → MvPolynomial.aeval ξ F = 0 := by
  first | exact @GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_three_nilpotent | exact GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_three_nilpotent | (intros; apply GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_three_nilpotent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PerfectPairingFiniteModuleRowsCriterion
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PerfectPairingFiniteModuleRowsCriterion
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun
  GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.CharDual

theorem exists_char_ne_zero (n : ℕ) (hn : n ≠ 0) {G : Type} [AddCommGroup G]
    (hG : ∀ g : G, n • g = 0) {g : G} (hg : g ≠ 0) : ∃ φ : G →+ ZMod n, φ g ≠ 0 := by
  haveI : NeZero n := ⟨hn⟩
  letI : Module (ZMod n) G := AddCommGroup.zmodModule hG
  obtain ⟨f, hf⟩ := GlobalTheory.ZModPerp.exists_dual_ne_zero (n := n) hg
  exact ⟨f.toAddMonoidHom, hf⟩

variable (A : Type) [CommRing A] (n : ℕ)

def charModule : Module A (A →+ ZMod n) where
  smul a φ := φ.comp (AddMonoidHom.mulLeft a)
  one_smul φ := by
    ext b
    show φ (1 * b) = φ b
    rw [one_mul]
  mul_smul a a' φ := by
    ext b
    show φ (a * a' * b) = φ (a' * (a * b))
    rw [mul_left_comm, mul_assoc]
  smul_zero a := by ext b; rfl
  smul_add a φ ψ := by ext b; rfl
  add_smul a a' φ := by
    ext b
    show φ ((a + a') * b) = φ (a * b) + φ (a' * b)
    rw [add_mul, map_add (f := _)]
  zero_smul φ := by
    ext b
    show φ (0 * b) = 0
    rw [zero_mul, map_zero]

end GlobalTheory.NewPrime.CharDual

namespace GlobalTheory.NewPrime


open GlobalTheory.NewPrime.CharDual in
theorem charDual_cogenerator : ∀ (A : Type) [CommRing A] [Finite A] (n : ℕ), n ≠ 0 → (n : A) = 0 →
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module A Y) (_ : Finite Y) (β : Y →+ A →+ ZMod n),
      Perf A β ∧ ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) (v : Fin a → A),
        (∀ x : Fin a → Y, matAct Φ x = 0 → ∑ j, v j • x j = 0) → v ∈ what₂ Φ := by
  intro A _ _ n hn hnA
  haveI : NeZero n := ⟨hn⟩
  letI : Module A (A →+ ZMod n) := charModule A n
  haveI : Finite (A →+ ZMod n) :=
    Finite.of_injective (fun φ : A →+ ZMod n => (φ : A → ZMod n)) DFunLike.coe_injective
  refine ⟨A →+ ZMod n, inferInstance, inferInstance, inferInstance, AddMonoidHom.id _, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a y y'
    rfl
  · intro y hy
    ext b
    exact hy b
  · intro y' hy'
    by_contra h
    obtain ⟨φ, hφ⟩ := exists_char_ne_zero n hn (G := A) (fun g => by
      rw [nsmul_eq_mul, hnA, zero_mul]) h
    exact hφ (hy' φ)
  · intro a Φ v hv
    by_contra hvr
    set Q := (Fin a → A) ⧸ what₂ Φ
    have hQ : ∀ q : Q, n • q = 0 := by
      intro q
      induction q using Submodule.Quotient.induction_on with
      | H w =>
        show n • (Submodule.Quotient.mk w : Q) = 0
        rw [← Nat.cast_smul_eq_nsmul A, ← Submodule.Quotient.mk_smul, hnA, zero_smul,
          Submodule.Quotient.mk_zero]
    have hmk : (Submodule.Quotient.mk v : Q) ≠ 0 := by
      rwa [Ne, Submodule.Quotient.mk_eq_zero]
    obtain ⟨ψ, hψ⟩ := exists_char_ne_zero n hn hQ hmk
    let L : (Fin a → A) →+ ZMod n := ψ.comp (what₂ Φ).mkQ.toAddMonoidHom
    let x : Fin a → (A →+ ZMod n) := fun j => L.comp (AddMonoidHom.single (fun _ => A) j)
    have key : ∀ (w : Fin a → A) (b : A), (∑ j, w j • x j) b = L (fun k => w k * b) := by
      intro w b
      have hsum (s : Finset (Fin a)) : (∑ j ∈ s, w j • x j) b = ∑ j ∈ s, (w j • x j) b := by
        classical
        induction s using Finset.induction_on with
        | empty => simp
        | @insert j s hj ih => simp [hj, ih]
      rw [hsum]
      have : (fun k => w k * b) = ∑ j, Pi.single j (w j * b) := (Finset.univ_sum_single _).symm
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, map_sum]
      rfl
    have hx : matAct Φ x = 0 := by
      funext i
      ext b
      show (∑ j, Φ i j • x j) b = 0
      rw [key]
      have : (fun k => Φ i k * b) = b • Φ i := by
        funext k
        simp [mul_comm]
      rw [this]
      have hmem : b • Φ i ∈ what₂ Φ := Submodule.smul_mem _ b (Submodule.subset_span ⟨i, rfl⟩)
      show ψ (Submodule.Quotient.mk _) = 0
      rw [(Submodule.Quotient.mk_eq_zero _).2 hmem, map_zero]
    have h1 := congrArg (fun f : A →+ ZMod n => f 1) (hv x hx)
    rw [key] at h1
    simp only [mul_one] at h1
    exact hψ h1

end GlobalTheory.NewPrime
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PerfectPairingFiniteModuleRowsCriterionStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfect_pairing_finite_module_rows_criterion : ∀ (A : Type) [CommRing A] [Finite A] (n : ℕ), n ≠ 0 → (n : A) = 0 → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module A Y) (_ : Finite Y) (β : Y →+ A →+ ZMod n), Perf A β ∧ ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) (v : Fin a → A), (∀ x : Fin a → Y, matAct Φ x = 0 → ∑ j, v j • x j = 0) → v ∈ what₂ Φ := by
  first | exact @GlobalTheory.NewPrime.charDual_cogenerator | exact GlobalTheory.NewPrime.charDual_cogenerator | (intros; apply GlobalTheory.NewPrime.charDual_cogenerator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonCocycles
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonCocycles
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

noncomputable section

namespace GlobalTheory.NewPrime

section
variable {A : Type} [CommRing A] {a r : ℕ}

theorem rect_map {B B' : Type} [AddCommGroup B] [Module A B] [AddCommGroup B'] [Module A B'] (p : B →ₗ[A] B')
    (Z : Matrix (Fin r) (Fin a) A) (x : Fin a → B) : p.compLeft (Fin r) (rect Z x) = rect Z (p ∘ x) := by
  funext c
  set_option synthInstance.maxHeartbeats 100000 in
    simp [rect, map_sum]

theorem matAct_map {B B' : Type} [AddCommGroup B] [Module A B] [AddCommGroup B'] [Module A B'] (p : B →ₗ[A] B')
    (Φ : Matrix (Fin a) (Fin a) A) (x : Fin a → B) : p ∘ matAct Φ x = matAct Φ (p ∘ x) := by
  funext c
  set_option synthInstance.maxHeartbeats 100000 in
    simp [matAct, map_sum]

end

theorem comparison_cocycles : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q Q' : Finset (PlE D.host)) (a a' : ℕ) (Φ : Matrix (Fin a) (Fin a) A) (Φ' : Matrix (Fin a') (Fin a') A) Z Z' (γ σ : Bool → GE N), Univ bkP i s κ Q Φ Z → Univ bkP i s κ Q' Φ' Z' → (∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (f : GE N → Fin D.R.r → Y), SelC bkP i s κ Y Q' f → (∀ b, f (γ b) = 0) → SelC bkP i s κ Y Q f) → (∀ (Y : Type) [AddCommGroup Y] [Module A Y] b m, repOn (Tgl i s) κ Y (σ b) m = m) → ∃ E : Matrix (Fin a) (Fin a') A, what₂ E ⊔ (what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2)) = ⊤ ∧ (∀ b, (Φ * E) b ∈ what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2)) ∧ ∀ j : Bool × Fin D.R.r, Z' (σ j.1) j.2 - Matrix.vecMul (Z (σ j.1) j.2) E ∈ what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2) := by
  intro D N X bkP i s A _ _ κ Q Q' a a' Φ Φ' Z Z' γ σ hU hU' hSel hσ
  set W : Submodule A (Fin a' → A) := what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2) with hW
  letI tY : TopologicalSpace ((Fin a' → A) ⧸ W) := ⊥
  haveI : DiscreteTopology ((Fin a' → A) ⧸ W) := ⟨rfl⟩
  let gens : Fin a' → (Fin a' → A) ⧸ W := fun j => W.mkQ (Pi.single j 1)
  have hsum : ∀ v : Fin a' → A, ∑ j, v j • gens j = W.mkQ v := by
    intro v
    have : v = ∑ j, v j • (Pi.single j (1 : A) : Fin a' → A) := by
      funext c
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [this]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [gens, map_sum]
  have hrect : ∀ g c, rect (Z' g) gens c = W.mkQ (Z' g c) := fun g c => hsum _
  have hgens : matAct Φ' gens = 0 := by
    funext b
    have : matAct Φ' gens b = W.mkQ (Φ' b) := hsum (Φ' b)
    rw [this]
    exact (Submodule.Quotient.mk_eq_zero W).2 ((le_sup_left : what₂ Φ' ≤ W) (Submodule.subset_span ⟨b, rfl⟩))
  have hf' := (hU' ((Fin a' → A) ⧸ W)).1 gens hgens
  have hγ : ∀ b, (fun g => rect (Z' g) gens) (γ b) = 0 := by
    intro b
    funext c
    show rect (Z' (γ b)) gens c = 0
    rw [hrect]
    exact (Submodule.Quotient.mk_eq_zero W).2
      ((le_sup_right : what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2) ≤ W) (Submodule.subset_span ⟨(b, c), rfl⟩))
  have hf := hSel _ _ hf' hγ
  obtain ⟨x, hx, m, hm⟩ := (hU ((Fin a' → A) ⧸ W)).2.2 _ hf
  obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin a) (Fin a') A, ∀ b, W.mkQ (E b) = x b :=
    ⟨fun b => (Submodule.mkQ_surjective W (x b)).choose, fun b => (Submodule.mkQ_surjective W (x b)).choose_spec⟩
  have hvm : ∀ v : Fin a → A, W.mkQ (∑ k, v k • E k) = ∑ k, v k • x k := fun v => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smul, hE]
  refine ⟨E, ?_, ?_, ?_⟩
  · let S : Submodule A ((Fin a' → A) ⧸ W) := Submodule.span A (Set.range x)
    letI tS : TopologicalSpace (((Fin a' → A) ⧸ W) ⧸ S) := ⊥
    haveI : DiscreteTopology (((Fin a' → A) ⧸ W) ⧸ S) := ⟨rfl⟩
    have hpx : S.mkQ ∘ x = 0 := by
      funext b
      exact (Submodule.Quotient.mk_eq_zero S).2 (Submodule.subset_span ⟨b, rfl⟩)
    have hz : S.mkQ ∘ gens = 0 := by
      refine (hU' (((Fin a' → A) ⧸ W) ⧸ S)).2.1 _ ?_ ⟨S.mkQ.compLeft (Fin D.R.r) m, fun g => ?_⟩
      · rw [← matAct_map, hgens]
        funext b
        simp
      · have e := congrArg (S.mkQ.compLeft (Fin D.R.r)) (hm g)
        rw [map_sub, map_sub, rect_map, rect_map, hpx, repOn_map] at e
        have h0 : rect (Z g) (0 : Fin a → ((Fin a' → A) ⧸ W) ⧸ S) = 0 := by
          funext c
          simp [rect]
        rw [h0, sub_zero] at e
        exact e
    have hgS : ∀ j, gens j ∈ S := fun j =>
      (Submodule.Quotient.mk_eq_zero S).1 (congrFun hz j)
    rw [eq_top_iff]
    intro v _
    have hvS : W.mkQ v ∈ S := by
      rw [← hsum]
      exact S.sum_mem fun j _ => S.smul_mem _ (hgS j)
    have hSm : S = (what₂ E).map W.mkQ := by
      show Submodule.span A (Set.range x) = (Submodule.span A (Set.range E)).map W.mkQ
      rw [Submodule.map_span]
      congr 1
      ext y
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨E b, ⟨b, rfl⟩, hE b⟩
      · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
        exact ⟨b, (hE b).symm⟩
    rw [hSm] at hvS
    obtain ⟨e, he, hev⟩ := hvS
    have hd : v - e ∈ W := by
      rw [← Submodule.Quotient.mk_eq_zero W, ← Submodule.mkQ_apply, map_sub, hev, sub_self]
    have : v = e + (v - e) := by abel
    rw [this]
    exact Submodule.add_mem_sup he hd
  · intro b
    rw [← Submodule.Quotient.mk_eq_zero W, ← Submodule.mkQ_apply]
    have e1 : (Φ * E) b = ∑ k, Φ b k • E k := by
      funext c
      simp [Matrix.mul_apply, Finset.sum_apply]
    rw [e1, hvm (Φ b)]
    exact congrFun hx b
  · rintro ⟨b, c⟩
    rw [← Submodule.Quotient.mk_eq_zero W, ← Submodule.mkQ_apply]
    have e1 : Matrix.vecMul (Z (σ b) c) E = ∑ k, Z (σ b) c k • E k := by
      funext t
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
    have e2 := congrFun (hm (σ b)) c
    rw [hσ, sub_self] at e2
    show W.mkQ (Z' (σ b) c - Matrix.vecMul (Z (σ b) c) E) = 0
    rw [map_sub, e1, hvm (Z (σ b) c), ← hrect]
    exact e2

end GlobalTheory.NewPrime
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonCocyclesStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparison_cocycles_alt : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q Q' : Finset (PlE D.host)) (a a' : ℕ) (Φ : Matrix (Fin a) (Fin a) A) (Φ' : Matrix (Fin a') (Fin a') A) Z Z' (γ σ : Bool → GE N), Univ bkP i s κ Q Φ Z → Univ bkP i s κ Q' Φ' Z' → (∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (f : GE N → Fin D.R.r → Y), SelC bkP i s κ Y Q' f → (∀ b, f (γ b) = 0) → SelC bkP i s κ Y Q f) → (∀ (Y : Type) [AddCommGroup Y] [Module A Y] b m, repOn (Tgl i s) κ Y (σ b) m = m) → ∃ E : Matrix (Fin a) (Fin a') A, what₂ E ⊔ (what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2)) = ⊤ ∧ (∀ b, (Φ * E) b ∈ what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2)) ∧ ∀ j : Bool × Fin D.R.r, Z' (σ j.1) j.2 - Matrix.vecMul (Z (σ j.1) j.2) E ∈ what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2) := by
  first | exact @GlobalTheory.NewPrime.comparison_cocycles | exact GlobalTheory.NewPrime.comparison_cocycles | (intros; apply GlobalTheory.NewPrime.comparison_cocycles <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet

noncomputable section

namespace GlobalTheory.NewPrime

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {bkP : BKPh X}
  {i : X.Tw} {s : X.Sig i}

theorem small_inf {M : ℕ} {L : Subgroup (GE N)} {z : GE N} (hL : Small2 i s M L z) {ι C : Type} [Finite ι] [CommGroup C]
    (d : ι → (GE N →* C)) (ho : ∀ q, IsOpen ((d q).ker : Set (GE N))) (ha : ∀ q, AntiHom X.cc (d q)) :
    Small2 i s M (L ⊓ ⨅ q, (d q).ker) z := by
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩ := hL
  refine ⟨⟨?_, ?_, fun g g' hg => ?_, fun g => ⟨h4 g, ?_⟩, fun g hg => h5 g hg.1⟩, fun g hg => h6 g hg.1,
    fun g hg => h7 g hg.1⟩
  · refine h1.inter ?_
    show IsOpen ((⨅ q, (d q).ker : Subgroup (GE N)) : Set (GE N))
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite ho
  · have : (⨅ q, (d q).ker).Normal := Subgroup.normal_iInf_normal fun b => inferInstance
    infer_instance
  · simp only [Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, h3 g g' hg]
    refine and_congr_right fun _ => forall_congr' fun q => ?_
    rw [ha q g g' hg, inv_eq_one]
  · refine Subgroup.mem_iInf.2 fun q => ?_
    simp [MonoidHom.mem_ker]

theorem anti_of_ker {ι C C' : Type} [CommGroup C] [CommGroup C'] (d : ι → (GE N →* C)) (ha : ∀ q, AntiHom X.cc (d q))
    (κ : GE N →* C') (h : ∀ g, (∀ q, d q g = 1) → κ g = 1) : AntiHom X.cc κ := fun g g' hg => by
  rw [eq_inv_iff_mul_eq_one, ← map_mul]
  exact h _ fun q => by rw [map_mul, ha q g g' hg, inv_mul_cancel]

theorem IsChar.eq_one {Λ : Type} [CommRing Λ] {κ : GE N →* Λˣ} {M : ℕ} {ι : Type} [Fintype ι] {ξ : ι → Λ}
    {d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))} (h : IsChar i κ ξ d) {g : GE N}
    (hg : ∀ q, ξ q = 0 ∨ d q g = 1) : κ g = 1 := by
  have e := h g
  rw [Finset.prod_eq_one, mul_one] at e
  · exact Units.ext e
  · intro q _
    rcases hg q with h0 | h0 <;> simp [h0]

theorem IsChar.single {Λ : Type} [CommRing Λ] {κ : GE N →* Λˣ} {M : ℕ} {ι : Type} [Fintype ι] {ξ : ι → Λ}
    {d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))} (h : IsChar i κ ξ d) {g : GE N} (q₀ : ι)
    (hg : ∀ q, q ≠ q₀ → ξ q = 0 ∨ d q g = 1) :
    ((κ g : Λˣ) : Λ) * (1 + ξ q₀) ^ (Multiplicative.toAdd (d q₀ g)).val = 1 := by
  have e := h g
  rwa [Finset.prod_eq_single q₀ (fun q _ hq => by rcases hg q hq with h0 | h0 <;> simp [h0]) (by simp)] at e

theorem det_ne_zero (hPT : PoitouTateTotallyComplex) (hT : TameLocal) (hl : 0 < nu X i) {M : ℕ} {L : Subgroup (GE N)} {z : GE N}
    {p : PlE D.host} {d : GE N →* Multiplicative (ZMod (X.l i ^ M))} {σ γ : GE N} (h3 : nu X i + 2 ≤ M) (hL : Small2 i s M L z)
    (hp : NewPl i M L p d σ γ) {A : Type} [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A]
    [TopologicalSpace A] [DiscreteTopology A] {κ : GE N →* Aˣ} {Q Q' : Finset (PlE D.host)}
    {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (hS : Setup bkP i s κ Q) (hK : Kills i A) (hρ : IsDual i s ρ)
    (ha : AntiHom X.cc κ) (hκ : ∀ g ∈ DecV N p, κ g = 1) (hQ : ∀ v, v ∈ Q' ↔ v ∈ Q ∨ Over p v)
    {Y : Type} [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y]
    {β : Y →+ A →+ ZMod (X.l i ^ (nu X i + 1))} (hβ : Perf A β)
    (hcog : ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) (v : Fin a → A),
      (∀ x : Fin a → Y, matAct Φ x = 0 → ∑ j, v j • x j = 0) → v ∈ what₂ Φ)
    {a : ℕ} {Ψ : Matrix (Fin a) (Fin a) A} {Z : GE N → Matrix (Fin D.R.r) (Fin a) A} (hZ : Univ bkP i s κ Q Ψ Z)
    {y : Z1 (repOn ρ κ⁻¹ A)} (hy : DualSel bkP i s κ ρ β Q y) (l₀ : Fin a)
    (hB : bform (X := X) (fun g => rect (Z g) fun c => Ψ.adjugate c l₀) y.1 σ ≠ 0)
    {B : Type} [CommRing B] [Algebra (X.O0 i) B] (π : B →ₐ[X.O0 i] A) {x₁ x₂ : B} (hπ : Function.Surjective π)
    (hker : ∀ b, π b = 0 → b ∈ Ideal.span {x₁, x₂}) (h1 : π x₁ = 0) (h2 : π x₂ = 0) (h11 : x₁ * x₁ = 0)
    (h22 : x₂ ^ (2 * D.R.r) = 0) (h12 : ∀ f, x₁ * x₂ ^ (2 * D.R.r - 1) * f = 0 → π f = 0)
    {κ' : GE N →* Bˣ} (hκ' : ∀ g, ((κ g : Aˣ) : A) = π (κ' g : Bˣ)) (hK' : Kills i B) (ha' : AntiHom X.cc κ')
    (hI : ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p), ((κ' τ : Bˣ) : B) * (1 + x₁) ^ (Multiplicative.toAdd (d τ)).val = 1)
    (hσ : ((κ' σ : Bˣ) : B) * (1 + x₂) = 1) {a' : ℕ} {Φ' : Matrix (Fin a') (Fin a') B}
    {Z' : GE N → Matrix (Fin D.R.r) (Fin a') B} (hZ' : Univ bkP i s κ' Q' Φ' Z') : Φ'.det ≠ 0 := by
  have hZA := GlobalTheory.T.universalSelmerCocycle_map_algHom D N X bkP i s B A π κ' κ hκ' Q' a' Φ' Z' hZ'
  have hσD : σ ∈ DecV N p := hp.2.2.2.2.2.1.1
  have hσL : σ ∈ L := hp.2.2.2.1 hσD
  obtain ⟨E, hE1, hE2, hE3⟩ := GlobalTheory.T.comparison_cocycles_alt D N X bkP i s A κ Q Q' a a' Ψ (Φ'.map π) Z (fun g => (Z' g).map π) (two X γ) (two X σ)
    hZ hZA (GlobalTheory.T.selmer_unramified_of_vanish_inertia_generators hT D N X bkP i s hl M L z p d σ γ h3 hL hp A κ hK ha hκ Q Q' hQ) (fun W _ _ b m => by
      cases b
      · show repOn (Tgl i s) κ W σ m = m
        rw [(GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl M L z (by omega) hL A κ ρ hK hρ W σ hσL).1, hκ σ hσD, Units.val_one, one_smul]
      · show repOn (Tgl i s) κ W (cConj X σ) m = m
        rw [(GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl M L z (by omega) hL A κ ρ hK hρ W _
          ((hL.1.2.2.1 σ _ (cConj_apply X σ)).1 hσL)).1, antiHom_cConj X ha, hκ σ hσD, inv_one, Units.val_one, one_smul])
  have hcard : Fintype.card (Bool × Fin D.R.r) = 2 * D.R.r := by simp
  refine GlobalTheory.T.det_ne_zero_of_lowestForm_ne_zero_presentation A B (π : B →+* A) x₁ x₂ (Bool × Fin D.R.r) a a' Φ' (fun j => Z' (two X σ j.1) j.2)
    (fun j => Z' (two X γ j.1) j.2) (fun j => if j.1 then 1 else ((κ' σ : Bˣ) : B)) Ψ E (fun j => Z (two X σ j.1) j.2)
    (fun j => if j.1 then - y.1 (cConj X σ) j.2 else y.1 σ j.2) l₀ hπ hker h1 h2 h11 (hcard ▸ h22) (hcard ▸ h12)
    (fun j => ?_) (GlobalTheory.T.universal_cocycle_rows_relation_newPlace hT D N X bkP i s hl M L z p d σ γ h3 hL hp B κ' x₁ x₂ hK' ha' h11 hI hσ Q' a' Φ' Z' hZ')
    hE1 hE2 hE3 (hcog _ _ _ fun x hx => ?_) ?_
  · split_ifs
    · exact map_one _
    · show π _ = 1
      rw [← hκ', hκ σ hσD, Units.val_one]
  · refine hβ.2.1 _ fun c => ?_
    have hcx : matAct (Φ'.map π) (c • x) = 0 := by
      have hx' : matAct (Φ'.map π) x = 0 := hx
      rw [map_smul, hx', smul_zero]
    have e := GlobalTheory.T.reciprocity_relaxedSelmer_dualSelmer_newPlace hPT hT D N X bkP i s hl M L z p d σ γ h3 hL hp A κ Q Q' ρ hS hK hρ ha hκ hQ Y A β hβ.1 y _ hy
      ((hZA Y).1 _ hcx)
    have key : ∀ (g : GE N) (k : Fin D.R.r → A), vecPair D.R.r β (rect ((Z' g).map π) (c • x)) k =
        β (∑ j, (∑ u, k u * π (Z' g u j)) • x j) c := fun g k => by
      rw [vecPair_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [rect, Finset.sum_smul, map_sum, AddMonoidHom.finsetSum_apply, Pi.smul_apply, Matrix.map_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun u _ => ?_
      rw [hβ.1, hβ.1, hβ.1, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      congr 1
      ring
    rw [key, key, ← sub_eq_zero, ← AddMonoidHom.sub_apply, ← map_sub, ← Finset.sum_sub_distrib] at e
    rw [← e]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sub_smul, Finset.sum_apply, Fintype.sum_prod_type, Fintype.sum_bool, sub_eq_neg_add, ← Finset.sum_neg_distrib]
    simp only [← neg_mul]
    rfl
  · refine fun h0 => hB ?_
    rw [← h0, Fintype.sum_prod_type, Fintype.sum_bool, bform, sub_eq_neg_add, dotProduct_comm, dotProduct_comm _ (y.1 σ),
      ← neg_dotProduct]
    rfl

theorem step : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ThmS bkP → ∀ (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → Step bkP i s := by
  intro hC hPT _ hT hLF hLD hLE hGF hGE _ h4 D N X bkP hS i s hG hl M R n H S d A₀ L z P w e hn he hM h3 hAdm hLH hz hL hSt hFit
  classical
  have hM1 : 1 ≤ M := by omega
  have hMν : nu X i + 1 ≤ M := by omega
  have hp : (X.l i).Prime := (X.lPrime i).out
  by_cases hNF : NF bkP i s M d P (2 * (e + 1) * w + 2)
  · obtain ⟨P', hE, hSt', -⟩ := GlobalTheory.T.exists_newPlace_frobeniusConjugate_modOpenNormalSubgroup hC D N X i s M R n d A₀ L z P hM1 hz hL hSt hn H S hAdm hLH L 1 hL.1.1 hL.1.2.1
      le_rfl L.one_mem (fun _ _ => map_one _) (fun b _ => (hSt.2.1 b).1 _ (over_refl _) _ (N.plOm.2 _))
    exact ⟨P', hE, hSt', (GlobalTheory.T.chebotarevInductionGrowBound_of_presentation hT D N X bkP hS i s hG hl M R n d A₀ L z P P' _ hn hM h3 hz hL hSt' hE).1 hNF⟩
  unfold NF at hNF
  push Not at hNF
  obtain ⟨Q, hQ, a, Φ, hΦ, F₀, hF₀, hc₀⟩ := hNF
  rcases hFit Q hQ a Φ hΦ with rfl | ⟨b, b', hb⟩
  · exfalso
    have hK : Kills i (X.O0 i ⧸ idl i) := fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 hx
    obtain ⟨φ, hφ, -⟩ := GlobalTheory.T.exists_lambda_algebra_hom_evaluation D N X i M (Fin R ⊕ Fin n) _ (fun _ => (0 : X.O0 i ⧸ idl i)) hl hMν hK
      (fun _ => zero_pow (pow_ne_zero _ hp.ne_zero))
    have e1 := hφ F₀
    rw [hF₀, Matrix.det_isEmpty, map_one, GlobalTheory.T.aeval_eq_zero_of_low_coeff_of_nilpotent_multiple _ _ _ (0 : X.O0 i ⧸ idl i) 1 (fun _ => 0) F₀ (pow_one _) (fun _ => dvd_rfl)
      (fun u hu => hK _ (hc₀ u (by omega)))] at e1
    have e2 : (1 : X.O0 i) ∈ Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i) :=
      Ideal.Quotient.eq_zero_iff_mem.1 e1
    exact (IsLocalRing.maximalIdeal.isMaximal (X.O0 i)).ne_top ((Ideal.eq_top_iff_one _).2 (Ideal.mul_le_inf e2).2)
  obtain ⟨F₁, hF₁⟩ := GlobalTheory.TwSys.toLam_surjective X i M (Fin R ⊕ Fin n) (Φ.adjugate b b')
  let K : Set (Fin R ⊕ Fin n) := {q | ∃ j : Fin R, n ≤ j.val ∧ q = .inl j}
  have := X.twistBaseCoefficientRing_residueField_finite i
  obtain ⟨A, _, _, _, _, t, a₀, hK, htK, ht2, haK, hau, hdvd⟩ := GlobalTheory.T.exists_finiteLocalRing_poly_divides_var_pow (X.O0 i) ((X.l i : X.O0 i) ^ nu X i) e w _ K F₁ he (by
    obtain ⟨m, h1, h2, h3⟩ := hb F₁ hF₁
    exact ⟨m, h1, by rintro q ⟨j, hj, rfl⟩; exact h2 j hj, h3⟩)
  change Kills i A at hK
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  have ht0 : t ^ X.l i ^ (M - nu X i - 1) = 0 := pow_eq_zero_of_le (by omega) htK
  obtain ⟨φ, hφ, hκ⟩ := GlobalTheory.T.exists_lambda_algebra_hom_evaluation D N X i M _ A (fun q => a₀ q * t) hl hMν hK (fun q => by rw [mul_pow, ht0, mul_zero])
  obtain ⟨κ, hκφ, hκ⟩ := hκ (fun q => d (P q))
  have hker : ∀ g, (∀ q ∉ K, d (P q) g = 1) → κ g = 1 := fun g hg => hκ.eq_one fun q => by
    by_cases hq : q ∈ K
    · exact Or.inl (by rw [haK q hq, zero_mul])
    · exact Or.inr (hg q hq)
  obtain ⟨hSet, hAnti, hκz⟩ := GlobalTheory.T.setup_and_antiHom_of_kills D N X bkP i s hG M _ P _ A₀ Q hSt.1 hQ A κ hK (fun g hg => hker g fun q _ => hg q)
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.exists_universalSelmerCocycle_baseChange D N X bkP i s M _ _ Q a Φ hΦ A φ κ hκφ hK
  have hdet : (Φ.map φ).det = 0 := by
    have e1 := (φ : _ →+* A).map_det Φ
    rw [RingHom.coe_coe, ← hF₀, hφ, GlobalTheory.T.aeval_eq_zero_of_low_coeff_of_nilpotent_multiple _ _ _ t _ _ F₀ htK (fun _ => dvd_mul_left _ _)
      (fun u hu => hK _ (hc₀ u hu))] at e1
    exact e1.symm
  have hadj : (Φ.map φ).adjugate b b' ∣ t ^ ((e + 1) * w) := by
    have e1 := congrFun (congrFun ((φ : _ →+* A).map_adjugate Φ) b) b'
    rw [← hφ, hF₁] at hdvd
    exact e1 ▸ hdvd
  generalize Φ.map φ = Ψ at hZ hdet hadj
  obtain ⟨ρ, hρ⟩ := exists_isDual i s
  have hl0 : X.l i ^ (nu X i + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  obtain ⟨Y, _, _, _, β, hβ, hcog⟩ := GlobalTheory.T.perfect_pairing_finite_module_rows_criterion A (X.l i ^ (nu X i + 1)) hl0 (by
    have e1 := hK _ (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (GlobalTheory.ResSel.SmallSub.l_mem X i))
    rw [map_mul, map_pow, map_natCast] at e1
    rw [Nat.cast_pow, pow_succ, e1])
  letI : TopologicalSpace Y := ⊥
  haveI : DiscreteTopology Y := ⟨rfl⟩
  have hNI := GlobalTheory.T.noInvDual_of_setup_of_isDual_of_tame_inertia D N X bkP i s A κ Q ρ z hSet hρ hz
  obtain ⟨y, hy, hyc⟩ := GlobalTheory.T.exists_dual_selmer_class_not_killed D N X bkP i s A κ Q ρ hSet hK hρ hNI
    (GlobalTheory.T.selmer_order_formula_dual_selmer hPT hLF hLD hLE hGF hGE h4 D N X bkP i s A κ Q ρ hSet hK hρ hNI) Y β hβ a Ψ Z hZ ((X.l i : A) ^ nu X i * t ^ ((e + 1) * w)) t
    (Ψ.adjugate b) b'
    (GlobalTheory.T.local_invariants_killed_alt hT D N X bkP i s hl M R n d A₀ L z P hM1 hz hL hSt A κ Q ρ t a₀ hQ hSet hK hρ hκ
      (fun q => hau _ (by rintro ⟨j, -, h⟩; cases h)) A)
    (by
      have e1 := congrFun (Matrix.adjugate_mul Ψ) b
      rw [hdet, zero_smul] at e1
      exact e1)
    (fun h0 => ht2 (by
      obtain ⟨c, hc⟩ := hadj
      rw [map_pow, map_natCast]
      have e1 : t ^ (2 * (e + 1) * w + 1) = t ^ ((e + 1) * w) * t * t ^ ((e + 1) * w) := by ring
      rw [e1]
      nth_rewrite 2 [hc]
      linear_combination c * h0))
  let L' : Subgroup (GE N) := L ⊓ ⨅ q : {q // q ∉ K}, (d (P q.1)).ker
  have hL' : Small2 i s M L' z := small_inf hL (fun q : {q // q ∉ K} => d (P q.1)) (fun q => (hSt.1.2.2 q.1).1)
    (fun q => (hSt.1.2.2 q.1).2.1)
  have hmem : ∀ g, g ∈ L' ↔ g ∈ L ∧ ∀ q ∉ K, d (P q) g = 1 := fun g => by
    simp [L', Subgroup.mem_iInf, MonoidHom.mem_ker, -Sum.forall]
  have hκL : ∀ g ∈ L', κ g = 1 := fun g hg => hker g ((hmem g).1 hg).2
  have hx₀ : matAct Ψ (fun c => Ψ.adjugate c b') = 0 := by
    funext u
    have e1 := congrFun (congrFun (Matrix.mul_adjugate Ψ) u) b'
    rw [hdet, zero_smul] at e1
    exact e1
  obtain ⟨h, hh, hB⟩ := GlobalTheory.T.exists_smallSubgroup_cocycleForm_ne_zero D N X bkP i s hl M L' z hMν hz hL' A κ Q ρ hSet hK hρ hAnti (hκz z hz) hκL a Ψ Z hZ _ b _ y
    hx₀ hadj hyc
  obtain ⟨x, hx, -⟩ := (hZ A).1 _ hx₀
  rw [← hx] at hB
  obtain ⟨U, hUo, hUn, hUL, hUm, hUB⟩ := GlobalTheory.T.exists_open_normal_subgroup_two_cocycles D N X i s hl M L' z hMν hL' A κ ρ hK hρ hκL x y h hh hB
  obtain ⟨P', hE, hSt', σ, γ, g, hNew, hdσ, hg⟩ := GlobalTheory.T.exists_newPlace_frobeniusConjugate_modOpenNormalSubgroup hC D N X i s M R n d A₀ L z P hM1 hz hL hSt hn H S hAdm hLH U h
    hUo hUn (hUL.trans inf_le_left) hh.1
    (fun c hc => ((hmem h).1 hh).2 _ (by rintro ⟨j, hj, h⟩; cases h; omega))
    (fun c hc => by
      have hI : ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inl c))), τ ∈ L' := fun τ hτ =>
        (hmem τ).2 ⟨(hSt.2.1 c).1 _ (over_refl _) _ (N.plOm.2 _) hτ, fun q hq =>
          (hSt.1.2.2 q).2.2.2.1 _ (fun h => hq ⟨c, hc, hSt.1.2.1 _ _ h⟩) _ (N.plOm.2 _) τ hτ⟩
      intro τ hτ
      have e1 := (GlobalTheory.T.inertiaVanishing_noInvariants_firstHalfPlaces hT D N X bkP i s hG hl M R n d A₀ L z P hMν hz hL hSt A κ _ hK hSet.2.2.2.2.1 (Or.inl rfl) A c).2
        hAnti (fun τ hτ => hκL τ (hI τ hτ)) x τ hτ
      have e2 := (GlobalTheory.T.inertiaVanishing_noInvariants_firstHalfPlaces hT D N X bkP i s hG hl M R n d A₀ L z P hMν hz hL hSt A κ⁻¹ ρ hK
        (fun g => (hSet.2.2.2.2.1 g).imp fun k hk => by rw [MonoidHom.inv_apply, inv_pow, hk, inv_one]) (Or.inr hρ) A c).2
        (fun g g' hg => by rw [MonoidHom.inv_apply, MonoidHom.inv_apply, hAnti g g' hg])
        (fun τ hτ => by rw [MonoidHom.inv_apply, hκL τ (hI τ hτ), inv_one]) y τ hτ
      exact hUm τ (hI τ hτ) e1.1 e1.2 e2.1 e2.2)
  refine ⟨P', hE, hSt', fun Q' hQ' a' Φ' hΦ' F' hF' => ?_⟩
  by_contra hcon
  push Not at hcon
  have hr : 0 < 2 * D.R.r := by have := hG.2.2.2.2.2.2; omega
  obtain ⟨B, _, _, j, π, x₁, x₂, hπj, hπk, h1, h2, h11, h22, h12⟩ := GlobalTheory.T.exists_ring_sq_zero_nilpotent_augmented (X.O0 i) A _ hr
  have hK' : Kills i B := fun u hu => by rw [← j.commutes, hK u hu, map_zero]
  let q₀ : Fin R ⊕ Fin (n + 1) := .inr (Fin.last n)
  let q₁ : Fin R ⊕ Fin n := .inl ⟨n, hn⟩
  let em : Fin R ⊕ Fin n → Fin R ⊕ Fin (n + 1) := Sum.map id Fin.castSucc
  let ξ : Fin R ⊕ Fin (n + 1) → B := Sum.elim (fun c => if c = ⟨n, hn⟩ then x₂ else j (a₀ (.inl c) * t))
    (Fin.lastCases x₁ fun c => j (a₀ (.inr c) * t))
  have hcases : ∀ q', q' = q₀ ∨ ∃ q, q' = em q := by
    rintro (c | c)
    · exact Or.inr ⟨.inl c, rfl⟩
    · exact Fin.lastCases (Or.inl rfl) (fun c => Or.inr ⟨.inr c, rfl⟩) c
  have hne : ∀ q, em q ≠ q₀ := by
    rintro (c | c) h
    · exact Sum.inl_ne_inr h
    · exact Fin.castSucc_ne_last c (Sum.inr.inj h)
  have hξ0 : ξ q₀ = x₁ := by simp [ξ, q₀]
  have hξ1 : ξ (em q₁) = x₂ := by simp [ξ, q₁, em]
  have hξ : ∀ q, q ≠ q₁ → ξ (em q) = j (a₀ q * t) := by
    rintro (c | c) h
    · have : c ≠ ⟨n, hn⟩ := fun h' => h (congrArg _ h')
      simp [ξ, em, this]
    · simp [ξ, em]
  have hξ3 : ∀ q, j t ∣ ξ q ∨ ξ q = x₁ ∨ ξ q = x₂ := fun q' => by
    rcases hcases q' with rfl | ⟨q, rfl⟩
    · exact Or.inr (Or.inl hξ0)
    · by_cases hq : q = q₁
      · exact Or.inr (Or.inr (hq ▸ hξ1))
      · exact Or.inl (by rw [hξ q hq, map_mul]; exact dvd_mul_left _ _)
  obtain ⟨φ', hφ', hκ'⟩ := GlobalTheory.T.exists_lambda_algebra_hom_evaluation D N X i M _ B ξ hl hMν hK' (fun q => by
    rcases hξ3 q with ⟨c, hc⟩ | hc | hc <;> rw [hc]
    · rw [mul_pow, ← map_pow, ht0, map_zero, zero_mul]
    · exact pow_eq_zero_of_le (m := 2) (by omega) (by rw [sq, h11])
    · exact pow_eq_zero_of_le (by omega) h22)
  obtain ⟨κ', hκφ', hκ'⟩ := hκ' (fun q => d (P' q))
  obtain ⟨Z', hZ'⟩ := GlobalTheory.T.exists_universalSelmerCocycle_baseChange D N X bkP i s M _ _ Q' a' Φ' hΦ' B φ' κ' hκφ' hK'
  have hP' : ∀ q, P' (em q) = P q := hE
  have hσL : σ ∈ L' := by
    have e1 := hL'.1.2.1.conj_mem _ (L'.mul_mem (hUL hg) hh) g⁻¹
    rwa [show g⁻¹ * (g * σ * g⁻¹ * h⁻¹ * h) * g⁻¹⁻¹ = σ by group] at e1
  have hunr : ∀ q', q' ≠ q₀ → ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 (P' q₀)), d (P' q') τ = 1 := fun q' hq' τ hτ =>
    (hSt'.1.2.2 q').2.2.2.1 _ (fun h => hq' (hSt'.1.2.1 _ _ h)) _ (N.plOm.2 _) τ hτ
  have hDec : DecV N (P' q₀) ≤ L' := GlobalTheory.ChosenPrimes.dec_le (N.plOm.2 _) hL'.1.1
    (fun τ hτ => (hmem τ).2 ⟨hNew.2.2.2.1 hτ.1, fun q _ => hP' q ▸ hunr _ (hne q) τ hτ⟩) hNew.2.2.2.2.2.1 hσL
  refine det_ne_zero hPT hT hl h3 hL hNew (Q' := Q') hSet hK hρ hAnti (fun g hg => hκL g (hDec hg)) (fun v => ?_) hβ hcog hZ hy b'
    (hx ▸ hUB σ g hg) π (fun u => ⟨j u, hπj u⟩) hπk h1 h2 h11 h22 h12 (κ' := κ') (fun g => ?_) hK'
    (anti_of_ker (fun q => d (P' q)) (fun q => (hSt'.1.2.2 q).2.1) κ' fun g hg => hκ'.eq_one fun q => Or.inr (hg q))
    (fun τ hτ => hξ0 ▸ hκ'.single q₀ fun q hq => Or.inr (hunr q hq τ hτ)) ?_ hZ' ?_
  · rw [hQ', hQ]
    constructor
    · rintro ⟨q', hq'⟩
      rcases hcases q' with rfl | ⟨q, rfl⟩
      · exact Or.inr hq'
      · exact Or.inl ⟨q, hP' q ▸ hq'⟩
    · rintro (⟨q, hq⟩ | hq)
      · exact ⟨em q, (hP' q).symm ▸ hq⟩
      · exact ⟨q₀, hq⟩
  · have e1 := congrArg π (hκ' g)
    have e2 := hκ g
    have hπξ : ∀ q, π (ξ (em q)) = a₀ q * t := fun q => by
      by_cases hq : q = q₁
      · rw [hq, hξ1, h2, haK q₁ ⟨_, le_rfl, rfl⟩, zero_mul]
      · rw [hξ q hq, hπj]
    have e3 : π (∏ q, (1 + ξ q) ^ (Multiplicative.toAdd (d (P' q) g)).val) =
        ∏ q, (1 + a₀ q * t) ^ (Multiplicative.toAdd (d (P q) g)).val := by
      simp only [map_prod, map_pow, map_add (f := _), map_one]
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fin.prod_univ_castSucc]
      have e4 : π (ξ (.inr (Fin.last n))) = 0 := by rw [← h1, ← hξ0]
      rw [e4, add_zero, one_pow, mul_one]
      congr 1 <;> refine Finset.prod_congr rfl fun c _ => ?_
      · rw [← hπξ, ← hP']; rfl
      · rw [← hπξ, ← hP']; rfl
    rw [map_mul, map_one, e3] at e1
    exact (left_inv_eq_right_inv e2 (by rw [mul_comm]; exact e1))
  · have e1 := hκ'.single (g := σ) (em q₁) fun q' hq' => by
      rcases hcases q' with rfl | ⟨q, rfl⟩
      · exact Or.inr hdσ
      · by_cases hq : q ∈ K
        · exact Or.inl (by rw [hξ q (fun h => hq' (congrArg em h)), haK q hq, zero_mul, map_zero])
        · exact Or.inr (by rw [hP']; exact ((hmem σ).1 hσL).2 q hq)
    have e2 : d (P' (em q₁)) σ = Multiplicative.ofAdd 1 := by
      have := (hSt'.2.2 (Fin.last n)).2 ⟨n, hn⟩ σ hNew.2.2.2.2.2.1
      rwa [if_pos (by simp)] at this
    have : Fact (1 < X.l i ^ M) := ⟨Nat.one_lt_pow (by omega) hp.one_lt⟩
    rwa [hξ1, e2, toAdd_ofAdd, ZMod.val_one, pow_one] at e1
  · have e1 := (φ' : _ →+* B).map_det Φ'
    rw [RingHom.coe_coe, ← hF', hφ', GlobalTheory.T.aeval_eq_zero_low_coeff_three_nilpotents _ _ _ (j t) x₁ x₂ (2 * (e + 1) * w + 2) (2 * D.R.r) ξ F'
      (by rw [← map_pow, htK, map_zero]) h11 h22 hξ3 (fun u hu => hK' _ (hcon u hu))] at e1
    exact e1.symm

end GlobalTheory.NewPrime

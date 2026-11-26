module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffTensorAcrisWithFrobeniusGalois
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffTensorAcrisWithFrobeniusGalois
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.MemLoc GlobalTheory.ExpImage
open scoped Formalism.Per

namespace GlobalTheory.HWLCris

section

variable {l : ℕ} [Fact l.Prime]

theorem alg_alg (a : Per.Ainf l) : algebraMap (Per.Acris0 l) (Per.Acris l)
    (algebraMap (Per.Ainf l) (Per.Acris0 l) a) = algebraMap (Per.Ainf l) (Per.Acris l) a :=
  (GlobalTheory.RingIface.tower l a).symm

theorem exists_acris (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) :
    ∃ (W : Type) (_ : CommRing W) (a : Ainf l →+* W) (c : W →+* P.R.B) (φ : W →+* W)
      (γ : GQ l → (W →+* W)) (t : W), GlobalTheory.Decompl.LAdic.Good l W ∧ (∀ w, c (a w) = AI.ιA w) ∧
      (∀ w, φ (a w) = a (WittVector.frobenius w)) ∧ (∀ x, c (φ x) = P.φB (c x)) ∧
      (∀ g w, γ g (a w) = a (AI.actW g w)) ∧ (∀ g x, c (γ g x) = P.actQ g (c x)) ∧ c t = P.tB ∧
      (l : W) ∣ a AI.μ ^ (l - 1) ∧
      (∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ u z : W, ((n.factorial : ℕ) : W) * u =
        ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : W) * a AI.μ ^ (k + 1) ∧
        t - u = (l : W) ^ r * z) ∧
      ∀ m : ℕ, ∃ N : ℕ, ∀ x : W, (l : P.R.BdR) ^ N * P.ιB (c x) ∈ Lat AI m 0 := by
  obtain ⟨C, hC⟩ := FitsEx.exists_fits l P AI T
  have he : IsEps AI.ε := hC.ε ▸ core_isEps l C
  have hlog : IsLogA AI.ε C.t := hC.ε ▸ C.t_log
  have hc : ∀ x, T.eB ((T.eB.symm.toRingHom.comp (algebraMap (Per.Acris l) (Per.Bcris l))) x) =
      algebraMap (Per.Acris l) (Per.Bcris l) x := fun x => T.eB.apply_symm_apply _
  haveI := (acris_basic l).1
  refine ⟨Per.Acris l, inferInstance, algebraMap (Per.Ainf l) (Per.Acris l),
    T.eB.symm.toRingHom.comp (algebraMap (Per.Acris l) (Per.Bcris l)), phiA l, fun g => sigA g, C.t,
    GlobalTheory.Decompl.LAdic.good_of_complete l _ (acris_basic l).2.1, fun w => T.eB.injective ?_, fun w => ?_,
    fun x => T.eB.injective ?_, fun g w => ?_, fun g x => T.eB.injective ?_, T.eB.injective ?_, ?_,
    fun r => ?_, fun m => ?_⟩
  · rw [hc, T.ιA]
    exact (GlobalTheory.RingIface.aB_eq_alg l w).symm
  · rw [← GlobalTheory.RingBasics.φA_apply]
    exact (GlobalTheory.CrisMaps.phiA_extends l).alg w
  · rw [T.frob, hc, hc]
    exact ((ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.2 x).symm
  · rw [locAinf_actW]
    exact (GlobalTheory.CrisMaps.sigA_extends g).alg w
  · rw [T.actB, hc, hc]
    exact ((ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.1 g x).symm
  · rw [hc, hC.t]
    rfl
  · obtain ⟨w, hw, -⟩ := exists_mu_pow_div l AI.ε he.1
    have hw' : ((l : ℕ) : Per.Acris0 l) * w =
        algebraMap (Per.Ainf l) (Per.Acris0 l) (mu AI.ε) ^ (l - 1) :=
      Subtype.ext (by simpa using hw)
    have h2 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) hw'
    rw [map_mul, map_natCast, map_pow, alg_alg] at h2
    exact ⟨_, h2.symm⟩
  · obtain ⟨N, hN⟩ := hlog r
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨s, hs, z, hz⟩ := hN n hn
    refine ⟨_, z, ?_, hz⟩
    have hs' : ((n.factorial : ℕ) : Per.Acris0 l) * s =
        ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.Acris0 l) *
          (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu AI.ε)) ^ (k + 1) := by
      apply Subtype.val_injective
      rw [← Subalgebra.val_apply, ← Subalgebra.val_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast, AlgHom.commutes]
      exact hs
    have h2 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) hs'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast, alg_alg] at h2
    exact h2
  · obtain ⟨j, hj, -, hb⟩ := GlobalTheory.CrisIncl.exists_restrict l _ T.incl
    obtain ⟨N, hN⟩ := hb m
    refine ⟨N, fun x => ?_⟩
    obtain ⟨a, h'⟩ := hN x
    refine ⟨a, ?_⟩
    have h1 : T.eD (P.ιB ((T.eB.symm.toRingHom.comp (algebraMap (Per.Acris l) (Per.Bcris l))) x)) =
        algebraMap (Per.BdRp l) (Per.BdR l) (j x) := hj x
    rw [T.fil, pow_zero, one_mul, map_sub, map_mul, map_pow, map_natCast, h1, io_apply,
      TiedUnif.eD_ιA T, ← map_natCast (algebraMap (Per.BdRp l) (Per.BdR l)), ← map_pow, ← map_mul,
      ← map_sub]
    refine TiedUnif.alg_mem_FilD m ?_
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_sub, h', TiedUnif.ev_aDp, sub_self]

end

variable {l : ℕ} [Fact l.Prime]

theorem root_pow {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) : AI.εroot s ^ l ^ s = AI.ε := by
  induction s with
  | zero => simp [LocAinf.εroot]
  | succ s ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem dvd_sub_pow {R : Type} [CommRing R] (x : R) (s : ℕ) :
    (l : R) ∣ (x - 1) ^ l ^ s - (x ^ l ^ s - 1) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq (Fact.out : l.Prime) (x - 1) 1 s
  rw [sub_add_cancel, one_pow] at hr
  rw [hr]
  exact ⟨-((x - 1) * 1 * r), by ring⟩

theorem bounded_OL (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (LL : FinExt l)
    (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (m : ℕ) :
    ∃ k : ℕ, ∀ o : ↥(OL LL), (l : P.R.BdR) ^ k * ι (o : ↥LL.1) ∈ Lat AI m 0 := by
  let e := GlobalTheory.Decompl.basisO LL
  have hfil (x : ↥LL.1) : ι x ∈ FilB P 0 := by
    have := (GlobalTheory.Per.TiedField.tied_field l P AI T).1.isDomain
    have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
    obtain ⟨a, ha⟩ := IsAlgClosed.algebraMap_bijective_of_isIntegral
      (k := Om l) (K := integralClosure (Om l) P.R.BdR) |>.2
        ⟨ι x, ((IsIntegral.of_finite ℚ_[l] x).map ι).tower_top⟩
    have ha' : algebraMap (Om l) P.R.BdR a = ι x := congrArg Subtype.val ha
    rw [← ha']
    obtain ⟨y, h1, -⟩ := T.om a
    obtain ⟨-, hone, -⟩ := GlobalTheory.MemLoc.filD_laws l
    refine (T.fil _ 0 _).2 ?_
    have := Submodule.smul_mem _ y hone
    rwa [Algebra.smul_def, mul_one, ← h1] at this
  choose k hk using fun i : Fin (Module.finrank ℤ_[l] ↥(OL LL)) => (bounded_and_eventually_sub_mem_Lat l P AI T _
    (hfil (e i : ↥LL.1)) m 0).1
  refine ⟨∑ i, k i, fun o => ?_⟩
  have ho : o ∈ Submodule.span ℤ_[l] (Set.range e) := e.mem_span o
  induction ho using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le'
      (Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    rw [hj, pow_add, mul_assoc]
    exact Lat_anti AI (Nat.zero_le _) ((pow_mul_mem_Lat_iff AI).2 (hk i))
  | zero => simpa using zero_mem _
  | add x y _ _ hx hy =>
    rw [Subalgebra.coe_add, map_add (f := _), mul_add]
    exact add_mem hx hy
  | smul z x _ hx =>
    have := qB_mul_mem_Lat AI T z hx
    rw [Subalgebra.coe_smul, ← algebraMap_smul ℚ_[l] z, map_smul, Algebra.smul_def, mul_left_comm]
    exact this

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 4000000 in
theorem exists_tensor_acris : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (LL : FinExt l) (β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B), IsBeta AI β → ∃ (A : Type) (_ : CommRing A) (b : RA LL →+* A) (κ : A →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B) (φ : A →+* A) (γ : GQ l → (A →+* A)) (t : A), GlobalTheory.Decompl.LAdic.Good l A ∧ ((∀ y, κ (b y) = β y) ∧ (∀ o w, φ (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) ∧ (∀ x, κ (φ x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) P.φB (κ x)) ∧ (∀ g o w, γ g (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] AI.actW g w)) ∧ (∀ g x, κ (γ g x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) (P.actQ g).toAlgHom (κ x)) ∧ κ t = (1 : ↥LL.1) ⊗ₜ[ℚ_[l]] P.tB) ∧ (∀ s : ℕ, ∃ d : ℕ, 0 < d ∧ (l : A) ∣ b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)) ^ d) ∧ (∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ u z : A, ((n.factorial : ℕ) : A) * u = ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : A) * b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.μ) ^ (k + 1) ∧ t - u = (l : A) ^ r * z) ∧ ∀ (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (m : ℕ), ∃ C : ℕ, ∀ y : A, (l : P.R.BdR) ^ C * Algebra.TensorProduct.productMap ι P.ιB (κ y) ∈ GlobalTheory.ExpImage.Lat AI m 0 := by
  intro l _ P AI T LL β hβ
  obtain ⟨W, _, a, c, φ, γ, t, hg, hca, hφa, hcφ, hγa, hcγ, hct, hμ, hlog, hb⟩ := exists_acris P AI T
  let _ : Algebra ℤ_[l] W := (a.comp (algebraMap ℤ_[l] (Ainf l))).toAlgebra
  have hz : ∀ z : ℤ_[l], algebraMap ℤ_[l] W z = a (algebraMap ℤ_[l] (Ainf l) z) := fun _ => rfl
  let _ : Algebra ℤ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) :=
    ((algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B)).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  let f₁ : ↥(OL LL) →ₐ[ℤ_[l]] ↥LL.1 ⊗[ℚ_[l]] P.R.B :=
    { toRingHom := (Algebra.TensorProduct.includeLeftRingHom).comp (OL LL).val.toRingHom
      commutes' := fun z => by
        show ((algebraMap ℤ_[l] ↥LL.1 z) ⊗ₜ[ℚ_[l]] (1 : P.R.B)) =
          algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) (algebraMap ℤ_[l] ℚ_[l] z)
        rw [Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1] }
  let f₂ : W →ₐ[ℤ_[l]] ↥LL.1 ⊗[ℚ_[l]] P.R.B :=
    { toRingHom := (Algebra.TensorProduct.includeRight (R := ℚ_[l]) (A := ↥LL.1)).toRingHom.comp c
      commutes' := fun z => by
        show Algebra.TensorProduct.includeRight (R := ℚ_[l]) (A := ↥LL.1)
            (c (a (algebraMap ℤ_[l] (Ainf l) z))) =
          algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) (algebraMap ℤ_[l] ℚ_[l] z)
        rw [hca, ιA_zl AI T, AlgHom.commutes]
        rfl }
  obtain ⟨κ, hκ⟩ : ∃ κ : ↥(OL LL) ⊗[ℤ_[l]] W →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B,
      ∀ o x, κ (o ⊗ₜ[ℤ_[l]] x) = (o : ↥LL.1) ⊗ₜ[ℚ_[l]] c x := by
    refine ⟨(Algebra.TensorProduct.productMap f₁ f₂).toRingHom, fun o x => ?_⟩
    show Algebra.TensorProduct.productMap f₁ f₂ (o ⊗ₜ[ℤ_[l]] x) = _
    rw [Algebra.TensorProduct.productMap_apply_tmul]
    show ((o : ↥LL.1) ⊗ₜ[ℚ_[l]] (1 : P.R.B)) * ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] c x) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  obtain ⟨b, hb'⟩ : ∃ b : RA LL →+* ↥(OL LL) ⊗[ℤ_[l]] W,
      ∀ o w, b (o ⊗ₜ[ℤ_[l]] w) = o ⊗ₜ[ℤ_[l]] a w :=
    ⟨(Algebra.TensorProduct.map (AlgHom.id ℤ_[l] ↥(OL LL))
      ({ toRingHom := a, commutes' := fun _ => rfl } : Ainf l →ₐ[ℤ_[l]] W)).toRingHom, fun _ _ => rfl⟩
  have ext : ∀ f : W →+* W, (∀ z, f (algebraMap ℤ_[l] W z) = algebraMap ℤ_[l] W z) →
      ∃ F : ↥(OL LL) ⊗[ℤ_[l]] W →+* ↥(OL LL) ⊗[ℤ_[l]] W,
        ∀ o x, F (o ⊗ₜ[ℤ_[l]] x) = o ⊗ₜ[ℤ_[l]] f x := fun f hf =>
    ⟨(Algebra.TensorProduct.map (AlgHom.id ℤ_[l] ↥(OL LL))
      ({ toRingHom := f, commutes' := hf } : W →ₐ[ℤ_[l]] W)).toRingHom, fun _ _ => rfl⟩
  obtain ⟨Φ, hΦ⟩ := ext φ fun z => by
    rw [hz, hφa, WittVector.frobenius_eq_map_frobenius]
    exact congrArg a (map_zlW l _ z)
  choose Γ hΓ using fun g => ext (γ g) fun z => by rw [hz, hγa, actW_zl]
  let j : W →+* ↥(OL LL) ⊗[ℤ_[l]] W := (Algebra.TensorProduct.includeRight (R := ℤ_[l])).toRingHom
  have hj : ∀ w, b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w) = j (a w) := fun w => hb' 1 w
  refine ⟨↥(OL LL) ⊗[ℤ_[l]] W, inferInstance, b, κ, Φ, Γ, j t,
    GlobalTheory.Decompl.LAdic.good_tensor (GlobalTheory.Decompl.basisO LL) l hg, ⟨fun y => ?_, fun o w => ?_, fun x => ?_,
    fun g o w => ?_, fun g x => ?_, ?_⟩, fun s => ?_, fun r => ?_, fun ι m => ?_⟩
  · induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul o w => rw [hb', hκ, hca, hβ]
    | add x y hx hy => simp only [map_add, hx, hy]
  · rw [hb', hb', hΦ, hφa]
  · induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul o w => rw [hΦ, hκ, hκ, hcφ]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  · rw [hb', hb', hΓ, hγa]
  · induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul o w => rw [hΓ, hκ, hκ, hcγ]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  · rw [← hct]
    exact hκ 1 t
  · have hl : 1 < l := (Fact.out : l.Prime).one_lt
    refine ⟨l ^ s * (l - 1), Nat.mul_pos (by positivity) (by omega), ?_⟩
    have h1 := dvd_sub_pow (l := l) (WittVector.teichmuller l (AI.εroot s)) s
    rw [← map_pow, root_pow] at h1
    have h2 := map_dvd a (h1.trans (sub_dvd_pow_sub_pow _ _ (l - 1)))
    rw [map_natCast, map_sub, map_pow a (_ - 1) (l - 1)] at h2
    have h3 := map_dvd j (dvd_add h2 hμ)
    rw [LocAinf.μ, sub_add_cancel, map_natCast, ← pow_mul, map_pow, map_pow] at h3
    rwa [hj]
  · obtain ⟨N, hN⟩ := hlog r
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨u, z, h1, h2⟩ := hN n hn
    refine ⟨j u, j z, ?_, ?_⟩
    · have := congrArg j h1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast] at this
      rwa [hj]
    · have := congrArg j h2
      rwa [map_sub, map_mul, map_pow, map_natCast] at this
  · obtain ⟨k, hk⟩ := bounded_OL P AI T LL ι m
    obtain ⟨N, hN⟩ := hb m
    refine ⟨k + N, fun y => ?_⟩
    induction y using TensorProduct.induction_on with
    | zero =>
      rw [map_zero, map_zero, mul_zero]
      exact zero_mem _
    | tmul o w =>
      rw [hκ, Algebra.TensorProduct.productMap_apply_tmul, pow_add, mul_mul_mul_comm]
      exact Lat_anti AI (Nat.zero_le _) (Lat_mul AI (hk o) (hN w))
    | add x y hx hy =>
      rw [map_add κ, map_add, mul_add]
      exact add_mem hx hy

end GlobalTheory.HWLCris
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffTensorAcrisWithFrobeniusGaloisStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeffTensorAcris_with_frobenius_galois : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (LL : FinExt l) (β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B), IsBeta AI β → ∃ (A : Type) (_ : CommRing A) (b : RA LL →+* A) (κ : A →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B) (φ : A →+* A) (γ : GQ l → (A →+* A)) (t : A), GlobalTheory.Decompl.LAdic.Good l A ∧ ((∀ y, κ (b y) = β y) ∧ (∀ o w, φ (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) ∧ (∀ x, κ (φ x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) P.φB (κ x)) ∧ (∀ g o w, γ g (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] AI.actW g w)) ∧ (∀ g x, κ (γ g x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) (P.actQ g).toAlgHom (κ x)) ∧ κ t = (1 : ↥LL.1) ⊗ₜ[ℚ_[l]] P.tB) ∧ (∀ s : ℕ, ∃ d : ℕ, 0 < d ∧ (l : A) ∣ b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)) ^ d) ∧ (∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ u z : A, ((n.factorial : ℕ) : A) * u = ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : A) * b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.μ) ^ (k + 1) ∧ t - u = (l : A) ^ r * z) ∧ ∀ (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (m : ℕ), ∃ C : ℕ, ∀ y : A, (l : P.R.BdR) ^ C * Algebra.TensorProduct.productMap ι P.ιB (κ y) ∈ GlobalTheory.ExpImage.Lat AI m 0 := by
  first | exact @GlobalTheory.HWLCris.exists_tensor_acris | exact GlobalTheory.HWLCris.exists_tensor_acris | (intros; apply GlobalTheory.HWLCris.exists_tensor_acris <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormedAway
namespace GlobalTheory.AwayNorm

variable {R N : Type} [CommRing R] [CommRing N] [Algebra R N]

theorem _root_.GlobalTheory.AwayNorm.exists_normed_away : ∀ (p : ℕ) (R : Type) [CommRing R],
    2 ≤ p →
    _root_.GlobalTheory.Decompl.LAdic.Good p R →
    ∃ (N : Type) (_ : NormedCommRing N) (_ : CompleteSpace N) (_ : Algebra R N),
      IsLocalization.Away (p : R) N ∧
      (∀ (x : N) (r : ℕ), ‖x‖ ≤ ((p : ℝ)⁻¹) ^ r ↔ ∃ y : R, x = (p : N) ^ r * algebraMap R N y) ∧
      ∀ x : N, ‖(p : N) * x‖ = (p : ℝ)⁻¹ * ‖x‖ := by
  intro p R _ hp hR
  obtain ⟨htf, hsep, hcomp⟩ := hR
  let L := Localization.Away (p : R)
  have hunit : IsUnit (algebraMap R L (p : R)) := IsLocalization.Away.algebraMap_isUnit (p : R)
  set u : Lˣ := hunit.unit with hu
  have hu' : (u : L) = (p : L) := by rw [hu, IsUnit.unit_spec, map_natCast]
  have hp0 : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    positivity
  have hp1 : (p : ℝ)⁻¹ < 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    exact inv_lt_one_of_one_lt₀ (by linarith)
  have hpne : (p : ℝ)⁻¹ ≠ 0 := hp0.ne'
  have hpn : ∀ n : ℕ, ∀ x : R, (p : R) ^ n * x = 0 → x = 0 := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      apply ih
      apply htf
      rw [← mul_assoc, ← pow_succ']
      exact hx
  have hinj : Function.Injective (algebraMap R L) := by
    refine IsLocalization.injective L (M := Submonoid.powers (p : R)) ?_
    rintro _ ⟨n, rfl⟩
    rw [mem_nonZeroDivisors_iff]
    exact ⟨fun x hx => hpn n x hx, fun x hx => hpn n x (by rw [mul_comm]; exact hx)⟩
  obtain ⟨D, hD⟩ : ∃ D : L → ℤ → Prop,
      ∀ x r, D x r ↔ ∃ y : R, x = ((u ^ r : Lˣ) : L) * algebraMap R L y :=
    ⟨_, fun _ _ => Iff.rfl⟩
  have hDnat : ∀ (x : L) (n : ℕ), D x n ↔ ∃ y : R, x = (p : L) ^ n * algebraMap R L y := by
    intro x n
    rw [hD, zpow_natCast, Units.val_pow_eq_pow_val, hu']
  have hmono : ∀ x r s, s ≤ r → D x r → D x s := by
    intro x r s hsr hx
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = s + n := ⟨(r - s).toNat, by omega⟩
    rw [hD] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    refine ⟨(p : R) ^ n * y, ?_⟩
    rw [zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val, hu', map_mul, map_pow,
      map_natCast]
    ring
  have hadd : ∀ x y r, D x r → D y r → D (x + y) r := by
    intro x y r hx hy
    rw [hD] at hx hy ⊢
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, by rw [map_add (f := _), mul_add]⟩
  have hneg : ∀ x r, D x r → D (-x) r := by
    intro x r hx
    rw [hD] at hx ⊢
    obtain ⟨a, rfl⟩ := hx
    exact ⟨-a, by rw [map_neg, mul_neg]⟩
  have hmul : ∀ x y r s, D x r → D y s → D (x * y) (r + s) := by
    intro x y r s hx hy
    rw [hD] at hx hy ⊢
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, by rw [zpow_add, Units.val_mul, map_mul]; ring⟩
  have hup : ∀ x r, D x r → D ((p : L) * x) (r + 1) := by
    intro x r hx
    rw [hD] at hx ⊢
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, by rw [zpow_add_one, Units.val_mul, hu']; ring⟩
  have hdown : ∀ x r, D ((p : L) * x) r → D x (r - 1) := by
    intro x r hx
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by ring⟩
    rw [add_sub_cancel_right]
    rw [hD] at hx ⊢
    obtain ⟨a, ha⟩ := hx
    refine ⟨a, ?_⟩
    have hpu : IsUnit (p : L) := hu' ▸ u.isUnit
    apply hpu.mul_left_cancel
    rw [ha, zpow_add_one, Units.val_mul, hu']
    ring
  have hex : ∀ x : L, ∃ r, D x r := by
    intro x
    obtain ⟨z, hz⟩ := IsLocalization.surj (Submonoid.powers (p : R)) x
    obtain ⟨n, hn⟩ := z.2.2
    refine ⟨-(n : ℤ), ?_⟩
    rw [hD]
    refine ⟨z.1, ?_⟩
    rw [← hz, ← hn, map_pow, map_natCast, ← hu', zpow_neg, zpow_natCast,
      ← Units.val_pow_eq_pow_val, mul_comm x, Units.inv_mul_cancel_left]
  have hzero : ∀ r, D 0 r := fun r => (hD 0 r).2 ⟨0, by simp⟩
  have hsepL : ∀ x : L, (∀ n : ℕ, D x n) → x = 0 := by
    intro x hx
    obtain ⟨y0, hy0⟩ := (hDnat x 0).1 (hx 0)
    rw [pow_zero, one_mul] at hy0
    have hy : y0 = 0 := by
      apply hsep
      intro k
      obtain ⟨yk, hyk⟩ := (hDnat x k).1 (hx k)
      refine ⟨yk, hinj ?_⟩
      rw [← hy0, hyk, map_mul, map_pow, map_natCast]
    rw [hy0, hy, map_zero]

  let nrm : L → ℝ := fun x => ⨅ r : {r : ℤ // D x r}, (p : ℝ)⁻¹ ^ (r : ℤ)
  have hne : ∀ x, Nonempty {r : ℤ // D x r} := fun x =>
    let ⟨r, hr⟩ := hex x
    ⟨⟨r, hr⟩⟩
  have hbdd : ∀ x, BddBelow (Set.range fun r : {r : ℤ // D x r} => (p : ℝ)⁻¹ ^ (r : ℤ)) :=
    fun x => ⟨0, by rintro _ ⟨r, rfl⟩; positivity⟩
  have hle1 : ∀ x r, D x r → nrm x ≤ (p : ℝ)⁻¹ ^ r := fun x r h =>
    ciInf_le (hbdd x) ⟨r, h⟩
  have hge1 : ∀ x (c : ℝ), (∀ r, D x r → c ≤ (p : ℝ)⁻¹ ^ r) → c ≤ nrm x := by
    intro x c h
    haveI := hne x
    exact le_ciInf fun r => h r.1 r.2
  have hnn : ∀ x, 0 ≤ nrm x := fun x => hge1 x 0 fun r _ => by positivity
  have hlow : ∀ x r, ¬ D x r → (p : ℝ)⁻¹ ^ (r - 1) ≤ nrm x := by
    intro x r hr
    refine hge1 x _ fun s hs => ?_
    have hsr : s ≤ r - 1 := by
      by_contra h
      exact hr (hmono x s r (by omega) hs)
    exact zpow_le_zpow_right_of_le_one₀ hp0 hp1.le hsr
  have hchar : ∀ x r, nrm x ≤ (p : ℝ)⁻¹ ^ r ↔ D x r := by
    intro x r
    refine ⟨fun h => ?_, hle1 x r⟩
    by_contra hr
    have h1 := hlow x r hr
    have h2 : (p : ℝ)⁻¹ ^ r < (p : ℝ)⁻¹ ^ (r - 1) :=
      zpow_lt_zpow_right_of_lt_one₀ hp0 hp1 (by omega)
    linarith
  have hnz : nrm 0 = 0 := by
    refine le_antisymm ?_ (hnn 0)
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h hp1
    have := hle1 0 n (hzero n)
    rw [zpow_natCast] at this
    linarith
  have hnorm_mono : ∀ x y, (∀ r, D x r → D y r) → nrm y ≤ nrm x := fun x y h =>
    hge1 x _ fun r hr => hle1 y r (h r hr)
  have hnneg : ∀ x, nrm (-x) = nrm x := fun x =>
    le_antisymm (hnorm_mono _ _ fun r hr => hneg x r hr)
      (hnorm_mono _ _ fun r hr => by have := hneg (-x) r hr; rwa [neg_neg] at this)
  have hnadd : ∀ x y, nrm (x + y) ≤ nrm x + nrm y := by
    intro x y
    have key : ∀ r s, D x r → D y s →
        nrm (x + y) ≤ (p : ℝ)⁻¹ ^ r + (p : ℝ)⁻¹ ^ s := by
      intro r s hr hs
      have hr0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ ^ r := by positivity
      have hs0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ ^ s := by positivity
      rcases le_total r s with h | h
      · have := hle1 _ _ (hadd x y r hr (hmono y s r h hs))
        linarith
      · have := hle1 _ _ (hadd x y s (hmono x r s h hr) hs)
        linarith
    have h1 : ∀ s, D y s → nrm (x + y) - (p : ℝ)⁻¹ ^ s ≤ nrm x := fun s hs =>
      hge1 x _ fun r hr => by have := key r s hr hs; linarith
    have h2 : nrm (x + y) - nrm x ≤ nrm y :=
      hge1 y _ fun s hs => by have := h1 s hs; linarith
    linarith
  have hnmul : ∀ x y, nrm (x * y) ≤ nrm x * nrm y := by
    intro x y
    have key : ∀ r s, D x r → D y s → nrm (x * y) ≤ (p : ℝ)⁻¹ ^ r * (p : ℝ)⁻¹ ^ s := by
      intro r s hr hs
      rw [← zpow_add₀ hpne]
      exact hle1 _ _ (hmul x y r s hr hs)
    have h1 : ∀ s, D y s → nrm (x * y) ≤ nrm x * (p : ℝ)⁻¹ ^ s := by
      intro s hs
      have hq : (0 : ℝ) < (p : ℝ)⁻¹ ^ s := by positivity
      rw [← div_le_iff₀ hq]
      exact hge1 x _ fun r hr => by rw [div_le_iff₀ hq]; exact key r s hr hs
    rcases (hnn x).eq_or_lt with h0 | h0
    · obtain ⟨s, hs⟩ := hex y
      have := h1 s hs
      rw [← h0, zero_mul] at this
      rw [← h0, zero_mul]
      exact this
    · rw [← div_le_iff₀' h0]
      exact hge1 y _ fun s hs => by rw [div_le_iff₀' h0]; exact h1 s hs
  have hnpos : ∀ x, nrm x = 0 → x = 0 := fun x h =>
    hsepL x fun n => (hchar x n).1 (by rw [h]; positivity)
  let f : RingNorm L :=
    { toFun := nrm
      map_zero' := hnz
      add_le' := hnadd
      neg' := hnneg
      mul_le' := hnmul
      eq_zero_of_map_eq_zero' := hnpos }
  letI inst : NormedCommRing L := { f.toNormedRing with mul_comm := mul_comm }
  have hnorm : ∀ x : L, ‖x‖ = nrm x := fun _ => rfl
  have hcharN : ∀ (x : L) (r : ℕ), ‖x‖ ≤ ((p : ℝ)⁻¹) ^ r ↔
      ∃ y : R, x = (p : L) ^ r * algebraMap R L y := by
    intro x r
    rw [hnorm, ← zpow_natCast, hchar, hDnat]
  have hcomplete : CompleteSpace L := by
    refine Metric.complete_of_convergent_controlled_sequences (fun n => (p : ℝ)⁻¹ ^ n)
      (fun n => pow_pos hp0 n) fun v hv => ?_
    have hstep : ∀ k : ℕ, ∃ z : R, v (k + 1) - v k = (p : L) ^ (k + 1) * algebraMap R L z := by
      intro k
      rw [← hDnat]
      by_contra h
      have h1 := hlow _ _ h
      rw [Nat.cast_succ, add_sub_cancel_right, zpow_natCast] at h1
      have h2 := hv k (k + 1) k (Nat.le_succ k) le_rfl
      rw [dist_eq_norm, hnorm] at h2
      linarith
    choose z hz using hstep
    obtain ⟨s, hs⟩ := hcomp z
    choose r hr using hs
    have htel : ∀ n, v n = v 0 + (p : L) *
        algebraMap R L (∑ i ∈ Finset.range n, (p : R) ^ i * z i) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, map_add (f := _), mul_add, ← add_assoc, ← ih, map_mul, map_pow,
          map_natCast]
        linear_combination hz n
    refine ⟨v 0 + (p : L) * algebraMap R L s, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε hp1
    refine ⟨M, fun n hn => ?_⟩
    have hdiff : v n - (v 0 + (p : L) * algebraMap R L s) =
        (p : L) ^ (n + 1) * algebraMap R L (-r n) := by
      rw [htel n, map_neg]
      have := congrArg (algebraMap R L) (hr n)
      rw [map_sub, map_mul, map_pow, map_natCast] at this
      linear_combination (-(p : L)) * this
    have hb : ‖v n - (v 0 + (p : L) * algebraMap R L s)‖ ≤ (p : ℝ)⁻¹ ^ (n + 1) :=
      (hcharN _ _).2 ⟨_, hdiff⟩
    have hc : (p : ℝ)⁻¹ ^ (n + 1) ≤ (p : ℝ)⁻¹ ^ M :=
      pow_le_pow_of_le_one hp0.le hp1.le (by omega)
    rw [dist_eq_norm]
    linarith
  refine ⟨L, inst, hcomplete, inferInstance, inferInstance, hcharN, fun x => ?_⟩
  rw [hnorm, hnorm]
  refine le_antisymm ?_ ?_
  · have h : nrm ((p : L) * x) / (p : ℝ)⁻¹ ≤ nrm x :=
      hge1 x _ fun r hr => by
        rw [div_le_iff₀ hp0, ← zpow_add_one₀ hpne]
        exact hle1 _ _ (hup x r hr)
    rw [div_le_iff₀ hp0] at h
    linarith
  · refine hge1 _ _ fun r hr => ?_
    have h := hle1 _ _ (hdown x r hr)
    have e : (p : ℝ)⁻¹ ^ r = (p : ℝ)⁻¹ * (p : ℝ)⁻¹ ^ (r - 1) := by
      rw [mul_comm, ← zpow_add_one₀ hpne, sub_add_cancel]
    rw [e]
    exact mul_le_mul_of_nonneg_left h hp0.le

end GlobalTheory.AwayNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBanachModelTensorAcris
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.BanachModel

theorem norm_pow_mul {p : ℕ} {N : Type} [NormedRing N] (hm : ∀ x : N, ‖(p : N) * x‖ = (p : ℝ)⁻¹ * ‖x‖)
    (n : ℕ) (x : N) : ‖(p : N) ^ n * x‖ = ((p : ℝ)⁻¹) ^ n * ‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, hm, ih, pow_succ', mul_assoc]

theorem inv_pos' {p : ℕ} (hp : 2 ≤ p) : (0 : ℝ) < (p : ℝ)⁻¹ := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  positivity

theorem inv_lt_one' {p : ℕ} (hp : 2 ≤ p) : (p : ℝ)⁻¹ < 1 := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  exact inv_lt_one_of_one_lt₀ (by linarith)

theorem bounded {p : ℕ} (hp : 2 ≤ p) {L N : Type} [NormedField L] [NormedRing N]
    (hL : ‖(p : L)‖ = (p : ℝ)⁻¹) (hm : ∀ x : N, ‖(p : N) * x‖ = (p : ℝ)⁻¹ * ‖x‖) (c : L →+* N)
    (h1 : ∀ x, ‖x‖ ≤ 1 → ‖c x‖ ≤ 1) (x : L) : ‖c x‖ ≤ p * ‖x‖ := by
  have h0 := inv_pos' hp
  have hlt := inv_lt_one' hp
  have hp0 : (0 : ℝ) < p := inv_pos.mp h0
  have hpL : (p : L) ≠ 0 := by
    intro h; rw [h, norm_zero] at hL; exact h0.ne hL
  have hLm : ∀ x : L, ‖(p : L) * x‖ = (p : ℝ)⁻¹ * ‖x‖ := fun x => by rw [norm_mul, hL]
  have key : ∀ y : L, ‖y‖ ≤ 1 → ‖c y‖ ≤ p * ‖y‖ := by
    intro y hy
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one (norm_pos_iff.mpr hy0) hy h0 hlt
    have e : y = (p : L) ^ n * (y / (p : L) ^ n) := by field_simp
    have hz : ‖y / (p : L) ^ n‖ ≤ 1 := by
      rw [norm_div, norm_pow, hL]
      exact (div_le_one (pow_pos h0 n)).mpr hn2
    have e2 : ‖c y‖ ≤ ((p : ℝ)⁻¹) ^ n := by
      rw [e, map_mul, map_pow, map_natCast, norm_pow_mul hm]
      exact mul_le_of_le_one_right (pow_pos h0 n).le (h1 _ hz)
    refine e2.trans ?_
    have : ((p : ℝ)⁻¹) ^ n = p * ((p : ℝ)⁻¹) ^ (n + 1) := by rw [pow_succ]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hn1.le hp0.le
  obtain ⟨m, hm'⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (‖x‖ + 1)⁻¹ by positivity) hlt
  have hx : ‖(p : L) ^ m * x‖ ≤ 1 := by
    rw [norm_pow_mul hLm]
    calc _ ≤ (‖x‖ + 1)⁻¹ * (‖x‖ + 1) := by gcongr; linarith
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have := key _ hx
  rw [map_mul, map_pow, map_natCast, norm_pow_mul hm, norm_pow_mul hLm, mul_left_comm] at this
  exact le_of_mul_le_mul_left this (pow_pos h0 m)

section
variable {p : ℕ} {A N : Type} [CommRing A] [NormedCommRing N] [Algebra A N]

theorem continuous_of_alg (hp : 2 ≤ p)
    (hn : ∀ (x : N) (r : ℕ), ‖x‖ ≤ ((p : ℝ)⁻¹) ^ r ↔ ∃ y : A, x = (p : N) ^ r * algebraMap A N y)
    (f : N →+* N) (f₀ : A →+* A) (hf : ∀ y, f (algebraMap A N y) = algebraMap A N (f₀ y)) :
    Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one' hp)
  refine ⟨_, pow_pos (inv_pos' hp) r, fun x hx => ?_⟩
  rw [dist_zero_right] at hx
  obtain ⟨y, rfl⟩ := (hn x r).mp hx.le
  rw [map_zero, dist_zero_right]
  refine lt_of_le_of_lt ((hn _ r).mpr ⟨f₀ y, ?_⟩) hr
  rw [map_mul, map_pow, map_natCast, hf]

theorem pow_decay (hp : 2 ≤ p)
    (hn : ∀ (x : N) (r : ℕ), ‖x‖ ≤ ((p : ℝ)⁻¹) ^ r ↔ ∃ y : A, x = (p : N) ^ r * algebraMap A N y)
    (a : A) (d : ℕ) (hd : 0 < d) (h : (p : A) ∣ a ^ d) :
    ∃ C r : ℝ, 0 < r ∧ r < 1 ∧ ∀ k : ℕ, ‖algebraMap A N a ^ k‖ ≤ C * r ^ k := by
  have h0 := inv_pos' hp
  have hlt := inv_lt_one' hp
  have hp0 : (0 : ℝ) < p := inv_pos.mp h0
  set r : ℝ := ((p : ℝ)⁻¹) ^ ((d : ℝ)⁻¹) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos h0 _
  have hr1 : r < 1 := Real.rpow_lt_one h0.le hlt (by positivity)
  have hrd : r ^ d = (p : ℝ)⁻¹ := Real.rpow_inv_natCast_pow h0.le hd.ne'
  refine ⟨p, r, hr0, hr1, fun k => ?_⟩
  obtain ⟨y, hy⟩ := h
  have e : ‖algebraMap A N a ^ k‖ ≤ ((p : ℝ)⁻¹) ^ (k / d) := by
    refine (hn _ _).mpr ⟨y ^ (k / d) * a ^ (k % d), ?_⟩
    conv_lhs => rw [← Nat.div_add_mod k d, ← map_pow, pow_add, pow_mul, hy]
    simp only [map_mul, map_pow, map_natCast, mul_pow, mul_assoc]
  refine e.trans ?_
  have e2 : ((p : ℝ)⁻¹) ^ (k / d) = p * r ^ (d * (k / d) + d) := by
    rw [pow_add, pow_mul, hrd]; field_simp
  rw [e2]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0.le hr1.le ?_) hp0.le
  have := Nat.div_add_mod k d
  have := Nat.mod_lt k hd
  omega

theorem log_tendsto (hp : 2 ≤ p)
    (hn : ∀ (x : N) (r : ℕ), ‖x‖ ≤ ((p : ℝ)⁻¹) ^ r ↔ ∃ y : A, x = (p : N) ^ r * algebraMap A N y)
    {L : Type} [Field L] [CharZero L] (c : L →+* N) (μ t : A)
    (h : ∀ r : ℕ, ∃ M : ℕ, ∀ n ≥ M, ∃ u z : A, ((n.factorial : ℕ) : A) * u =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : A) * μ ^ (k + 1) ∧
        t - u = (p : A) ^ r * z) :
    Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
      c ((-1 : L) ^ (k + 1) / (k : L)) * algebraMap A N μ ^ k) Filter.atTop (nhds (algebraMap A N t)) := by
  rw [← Filter.tendsto_add_atTop_iff_nat 1, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one' hp)
  obtain ⟨M, hM⟩ := h r
  refine ⟨M, fun n hnM => ?_⟩
  obtain ⟨u, z, hu, hz⟩ := hM n hnM
  have hf : ((n.factorial : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have e : ∑ k ∈ Finset.range (n + 1), c ((-1 : L) ^ (k + 1) / (k : L)) * algebraMap A N μ ^ k
      = algebraMap A N u := by
    have h1 : c ((n.factorial : L)⁻¹) * ((n.factorial : ℕ) : N) = 1 := by
      rw [← map_natCast c, ← map_mul, inv_mul_cancel₀ hf, map_one]
    have h2 := congrArg (algebraMap A N) hu
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_natCast, map_sum] at h2
    rw [← one_mul (algebraMap A N u), ← h1, mul_assoc, h2, Finset.mul_sum, Finset.sum_range_succ']
    simp only [Nat.cast_zero, div_zero, map_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k + 1 ∣ n.factorial := Nat.dvd_factorial (Nat.succ_pos k) (Finset.mem_range.mp hk)
    have hk0 : ((k + 1 : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    have h3 : (-1 : L) ^ (k + 1 + 1) / ((k + 1 : ℕ) : L) =
        (n.factorial : L)⁻¹ * ((-1) ^ k * ((n.factorial / (k + 1) : ℕ) : L)) := by
      rw [Nat.cast_div hk' hk0, pow_succ, pow_succ]
      field_simp
    rw [h3]
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast, mul_assoc]
  rw [e, dist_comm, dist_eq_norm, ← map_sub, hz]
  refine lt_of_le_of_lt ((hn _ r).mpr ⟨z, ?_⟩) hr
  rw [map_mul, map_pow, map_natCast]

theorem closed_of_lat (hp : 2 ≤ p)
    (hn : ∀ (x : N) (r : ℕ), ‖x‖ ≤ ((p : ℝ)⁻¹) ^ r ↔ ∃ y : A, x = (p : N) ^ r * algebraMap A N y)
    {B : Type} [CommRing B] (F : N →+* B) (S : Set B) (Λ : ℕ → AddSubgroup B)
    (h1 : ∀ n, ∀ b ∈ S, b ∈ Λ n) (h2 : ∀ b, (∀ n, b ∈ Λ n) → b ∈ S)
    (h3 : ∀ n, ∀ b ∈ Λ 0, (p : B) ^ n * b ∈ Λ n) (C : ℕ)
    (hC : ∀ y : A, (p : B) ^ C * F (algebraMap A N y) ∈ Λ 0) : IsClosed {x : N | F x ∈ S} := by
  refine isClosed_of_closure_subset fun x hx => h2 _ fun n => ?_
  obtain ⟨x', hx', hd⟩ := Metric.mem_closure_iff.mp hx _ (pow_pos (inv_pos' hp) (n + C))
  rw [dist_eq_norm] at hd
  obtain ⟨y, hy⟩ := (hn _ _).mp hd.le
  have e : F x = F x' + (p : B) ^ n * ((p : B) ^ C * F (algebraMap A N y)) := by
    rw [← mul_assoc, ← pow_add, ← map_natCast F, ← map_pow, ← map_mul, ← hy, map_sub]
    ring
  rw [e]
  exact add_mem (h1 n _ hx') (h3 n _ (hC y))

end

theorem norm_l {l : ℕ} [Fact l.Prime] (LL : FinExt l) : ‖(l : ↥LL.1)‖ = (l : ℝ)⁻¹ := by
  change ‖(LL.1.val (l : ↥LL.1))‖ = _
  rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (Om l)) l, norm_algebraMap', Padic.norm_p]

theorem exists_scale {p : ℕ} (hp : 2 ≤ p) {L : Type} [NormedField L]
    (hL : ‖(p : L)‖ = (p : ℝ)⁻¹) (x : L) : ∃ m : ℕ, ‖x * (p : L) ^ m‖ ≤ 1 := by
  obtain ⟨m, hm'⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (‖x‖ + 1)⁻¹ by positivity) (inv_lt_one' hp)
  refine ⟨m, ?_⟩
  rw [norm_mul, norm_pow, hL, mul_comm]
  calc _ ≤ (‖x‖ + 1)⁻¹ * (‖x‖ + 1) := by gcongr; linarith
    _ = 1 := inv_mul_cancel₀ (by positivity)

theorem away_sub {p : ℕ} {Z L : Type} [CommRing Z] [Field L] [Algebra Z L] (O : Subalgebra Z L)
    (h0 : (p : L) ≠ 0) (h : ∀ x : L, ∃ m : ℕ, x * (p : L) ^ m ∈ O) :
    IsLocalization.Away ((p : ℕ) : ↥O) L := by
  refine IsLocalization.Away.mk _ ?_ (fun x => ?_) (fun a b h => ⟨0, ?_⟩)
  · rw [map_natCast]
    exact h0.isUnit
  · obtain ⟨m, hx⟩ := h x
    exact ⟨m, ⟨_, hx⟩, by rw [map_natCast]; rfl⟩
  · rw [Subtype.val_injective h]

theorem away_OL {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    IsLocalization.Away ((l : ℕ) : ↥(OL LL)) ↥LL.1 := by
  refine away_sub (OL LL) (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) fun x => ?_
  obtain ⟨m, hm⟩ := exists_scale (Fact.out : l.Prime).two_le (norm_l LL) x
  exact ⟨m, (GlobalTheory.Per.Val.mem_OL_iff LL _).mpr hm⟩

theorem exists_ext {p : ℕ} {A N B : Type} [CommRing A] [CommRing N] [CommRing B] [Algebra A N]
    [IsLocalization.Away (p : A) N] (f : A →+* B) (h : IsUnit (p : B)) :
    ∃ g : N →+* B, ∀ y, g (algebraMap A N y) = f y :=
  ⟨IsLocalization.Away.lift (p : A) (g := f) (by rwa [map_natCast]), fun y =>
    IsLocalization.Away.lift_eq _ _ y⟩

theorem ext_away {p : ℕ} {A N B : Type} [CommRing A] [CommRing N] [CommRing B] [Algebra A N]
    [IsLocalization.Away (p : A) N] (f g : N →+* B)
    (h : ∀ y, f (algebraMap A N y) = g (algebraMap A N y)) (x : N) : f x = g x :=
  RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (p : A)) (RingHom.ext h)) x

set_option maxHeartbeats 2000000 in
theorem exists_banach_model : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (LL : FinExt l) (β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B), IsBeta AI β → ∃ (N : Type) (_ : NormedCommRing N) (_ : CompleteSpace N) (c : ↥LL.1 →+* N) (b : RA LL →+* N) (κ : N →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B) (φ : N →+* N) (γ : GQ l → (N →+* N)) (t : N), ((∀ y, κ (b y) = β y) ∧ (∀ o w, φ (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) ∧ (∀ x, κ (φ x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) P.φB (κ x)) ∧ (∀ g o w, γ g (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] AI.actW g w)) ∧ (∀ g x, κ (γ g x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) (P.actQ g).toAlgHom (κ x)) ∧ κ t = (1 : ↥LL.1) ⊗ₜ[ℚ_[l]] P.tB) ∧ (∃ C : ℝ, ∀ x : ↥LL.1, ‖c x‖ ≤ C * ‖x‖) ∧ (∀ y, ‖b y‖ ≤ 1) ∧ (∀ o : ↥(OL LL), b (o ⊗ₜ[ℤ_[l]] (1 : Ainf l)) = c (o : ↥LL.1)) ∧ (∀ x, κ (c x) = x ⊗ₜ[ℚ_[l]] (1 : P.R.B)) ∧ (Continuous φ ∧ ∀ x, φ (c x) = c x) ∧ (∀ g, Continuous (γ g) ∧ ∀ x, γ g (c x) = c x) ∧ (∀ s : ℕ, ∃ C r : ℝ, 0 < r ∧ r < 1 ∧ ∀ k : ℕ, ‖b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)) ^ k‖ ≤ C * r ^ k) ∧ Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, c (PowerSeries.coeff k (logS LL)) * b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.μ) ^ k) Filter.atTop (nhds t) ∧ ∀ (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (m : ℕ), IsClosed {x : N | Algebra.TensorProduct.productMap ι P.ιB (κ x) ∈ GlobalTheory.ExpImage.FilB P (m : ℤ)} := by
  intro l _ P AI T LL β hβ
  have hp : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨A, iA, b, κ, φ, γ, t, hG, ⟨h1, h2, h3, h4, h5, h6⟩, hnil, hlog, hbd⟩ :=
    GlobalTheory.T.exists_coeffTensorAcris_with_frobenius_galois l P AI T LL β hβ
  obtain ⟨N, iN, cN, aN, hloc, hn, hm⟩ := GlobalTheory.AwayNorm.exists_normed_away l A hp hG
  haveI := away_OL LL
  have uN : IsUnit (l : N) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := N) (l : A)
    rwa [map_natCast] at this
  have uB : IsUnit (l : ↥LL.1 ⊗[ℚ_[l]] P.R.B) := by
    have : IsUnit (l : ℚ_[l]) := (Nat.cast_ne_zero.mpr (by omega)).isUnit
    have := this.map (algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B))
    rwa [map_natCast] at this
  obtain ⟨κ', hκ⟩ := exists_ext (p := l) (N := N) κ uB
  obtain ⟨φ', hφ⟩ := exists_ext (p := l) (N := N) ((algebraMap A N).comp φ) uN
  choose γ' hγ using fun g => exists_ext (p := l) (N := N) ((algebraMap A N).comp (γ g)) uN
  obtain ⟨c, hc⟩ := exists_ext (p := l) (N := ↥LL.1) ((algebraMap A N).comp (b.comp
    (Algebra.TensorProduct.includeLeftRingHom : ↥(OL LL) →+* ↥(OL LL) ⊗[ℤ_[l]] Ainf l))) uN
  have hc' : ∀ o : ↥(OL LL), c (algebraMap ↥(OL LL) ↥LL.1 o) =
      algebraMap A N (b (o ⊗ₜ[ℤ_[l]] (1 : Ainf l))) := hc
  have hφ' : ∀ y, φ' (algebraMap A N y) = algebraMap A N (φ y) := hφ
  have hγ' : ∀ g y, γ' g (algebraMap A N y) = algebraMap A N (γ g y) := hγ
  have hone : ∀ y : A, ‖algebraMap A N y‖ ≤ 1 := fun y => by
    simpa using (hn (algebraMap A N y) 0).mpr ⟨y, by simp⟩
  refine ⟨N, iN, cN, c, (algebraMap A N).comp b, κ', φ', γ', algebraMap A N t,
    ⟨fun y => ?_, fun o w => ?_, fun x => ?_, fun g o w => ?_, fun g x => ?_, ?_⟩,
    ⟨l, bounded hp (norm_l LL) hm c fun x hx => ?_⟩, fun y => hone _, fun o => (hc' o).symm, fun x => ?_,
    ⟨continuous_of_alg hp hn φ' φ hφ', fun x => ?_⟩,
    fun g => ⟨continuous_of_alg hp hn (γ' g) (γ g) (hγ' g), fun x => ?_⟩, fun s => ?_, ?_, fun ι m => ?_⟩
  · rw [RingHom.comp_apply, hκ, h1]
  · rw [RingHom.comp_apply, RingHom.comp_apply, hφ', h2]
  · refine ext_away (p := l) (A := A) (κ'.comp φ')
      ((Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) P.φB).toRingHom.comp κ') (fun y => ?_) x
    rw [RingHom.comp_apply, RingHom.comp_apply, hφ', hκ, hκ, h3]
    rfl
  · rw [RingHom.comp_apply, RingHom.comp_apply, hγ', h4]
  · refine ext_away (p := l) (A := A) (κ'.comp (γ' g))
      ((Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) (P.actQ g).toAlgHom).toRingHom.comp κ')
      (fun y => ?_) x
    rw [RingHom.comp_apply, RingHom.comp_apply, hγ', hκ, hκ, h5]
    rfl
  · rw [hκ, h6]
  · have := hc' ⟨x, (GlobalTheory.Per.Val.mem_OL_iff LL x).mpr hx⟩
    exact (congrArg norm this).trans_le (hone _)
  · refine ext_away (p := l) (A := ↥(OL LL)) (κ'.comp c)
      (Algebra.TensorProduct.includeLeftRingHom : ↥LL.1 →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B) (fun o => ?_) x
    rw [RingHom.comp_apply, hc', hκ, h1, hβ, map_one]
    rfl
  · refine ext_away (p := l) (A := ↥(OL LL)) (φ'.comp c) c (fun o => ?_) x
    rw [RingHom.comp_apply, hc', hφ', h2, map_one]
  · refine ext_away (p := l) (A := ↥(OL LL)) ((γ' g).comp c) c (fun o => ?_) x
    rw [RingHom.comp_apply, hc', hγ', h4, map_one]
  · obtain ⟨d, hd, hdv⟩ := hnil s
    exact pow_decay hp hn _ d hd hdv
  · simp only [logS, PowerSeries.coeff_mk]
    exact log_tendsto hp hn c _ t hlog
  · obtain ⟨C, hC⟩ := hbd ι m
    refine closed_of_lat hp hn ((Algebra.TensorProduct.productMap ι P.ιB).toRingHom.comp κ')
      (GlobalTheory.ExpImage.FilB P (m : ℤ)) (fun n => GlobalTheory.ExpImage.Lat AI m n)
      (fun n b hb => GlobalTheory.ExpImage.FilB_le_Lat AI hb)
      (fun b hb => GlobalTheory.ExpImage.mem_FilB_of_forall_Lat l P AI T m b hb)
      (fun n b hb => (GlobalTheory.ExpImage.pow_mul_mem_Lat_iff AI (n := 0)).mpr hb) C fun y => ?_
    rw [RingHom.comp_apply, hκ]
    exact hC y

end GlobalTheory.HWL.BanachModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBanachModelTensorAcrisStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_banachModel_tensor_Acris : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (LL : FinExt l) (β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B), IsBeta AI β → ∃ (N : Type) (_ : NormedCommRing N) (_ : CompleteSpace N) (c : ↥LL.1 →+* N) (b : RA LL →+* N) (κ : N →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B) (φ : N →+* N) (γ : GQ l → (N →+* N)) (t : N), ((∀ y, κ (b y) = β y) ∧ (∀ o w, φ (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) ∧ (∀ x, κ (φ x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) P.φB (κ x)) ∧ (∀ g o w, γ g (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] AI.actW g w)) ∧ (∀ g x, κ (γ g x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) (P.actQ g).toAlgHom (κ x)) ∧ κ t = (1 : ↥LL.1) ⊗ₜ[ℚ_[l]] P.tB) ∧ (∃ C : ℝ, ∀ x : ↥LL.1, ‖c x‖ ≤ C * ‖x‖) ∧ (∀ y, ‖b y‖ ≤ 1) ∧ (∀ o : ↥(OL LL), b (o ⊗ₜ[ℤ_[l]] (1 : Ainf l)) = c (o : ↥LL.1)) ∧ (∀ x, κ (c x) = x ⊗ₜ[ℚ_[l]] (1 : P.R.B)) ∧ (Continuous φ ∧ ∀ x, φ (c x) = c x) ∧ (∀ g, Continuous (γ g) ∧ ∀ x, γ g (c x) = c x) ∧ (∀ s : ℕ, ∃ C r : ℝ, 0 < r ∧ r < 1 ∧ ∀ k : ℕ, ‖b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)) ^ k‖ ≤ C * r ^ k) ∧ Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, c (PowerSeries.coeff k (logS LL)) * b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.μ) ^ k) Filter.atTop (nhds t) ∧ ∀ (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (m : ℕ), IsClosed {x : N | Algebra.TensorProduct.productMap ι P.ιB (κ x) ∈ GlobalTheory.ExpImage.FilB P (m : ℤ)} := by
  first | exact @GlobalTheory.HWL.BanachModel.exists_banach_model | exact GlobalTheory.HWL.BanachModel.exists_banach_model | (intros; apply GlobalTheory.HWL.BanachModel.exists_banach_model <;> assumption)
end

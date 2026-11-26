module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeKurOfNorm
namespace GlobalTheory.UnramValue

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct IsLocalRing Polynomial

theorem exists_pow_card_eq {S : Type*} [CommRing S] [IsLocalRing S]
    [IsAdicComplete (maximalIdeal S) S] [Fintype (ResidueField S)] (x : S) :
    ∃ t : S, t ^ Fintype.card (ResidueField S) = t ∧ t - x ∈ maximalIdeal S := by
  have h1 : 1 < Fintype.card (ResidueField S) := Fintype.one_lt_card
  have hm : (X ^ Fintype.card (ResidueField S) - X : S[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1)
  obtain ⟨t, ht, htx⟩ := (IsAdicComplete.henselianRing S (maximalIdeal S)).is_henselian _ hm x
    (by
      rw [← residue_eq_zero_iff]
      simp [FiniteField.pow_card])
    (by
      change IsUnit (residue S _)
      rw [derivative_sub, derivative_X_pow]
      simp)
  refine ⟨t, ?_, htx⟩
  simpa [sub_eq_zero] using ht

variable {l : ℕ} [Fact l.Prime]

theorem norm_natCast_l : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap', Padic.norm_p]

theorem integral_mem (L : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] L]
    (h : ∀ x ∈ L, x ≠ 0 → ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k) (x : integralClosure ℤ_[l] L) :
    ((x : L) : Om l) ∈ MaximalUnramifiedExtension l := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : L) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hmax : ∀ y : integralClosure ℤ_[l] L,
      y ∈ maximalIdeal (integralClosure ℤ_[l] L) ↔ ‖((y : L) : Om l)‖ < 1 := fun y => by
    rw [GlobalTheory.DiscEval.mem_maximalIdeal_iff_norm, GlobalTheory.DiscEval.intEmb_apply,
      GlobalTheory.DiscEval.fieldEmb_apply, PadicComplex.norm_extends]
  have hint : ∀ y : L, y ∈ integralClosure ℤ_[l] L ↔ ‖(y : Om l)‖ ≤ 1 := fun y => by
    rw [GlobalTheory.DiscEval.mem_integralClosure_iff_norm, GlobalTheory.DiscEval.fieldEmb_apply,
      PadicComplex.norm_extends]
  let N : Submodule ℤ_[l] (integralClosure ℤ_[l] L) :=
    { carrier := {y | ((y : L) : Om l) ∈ MaximalUnramifiedExtension l}
      add_mem' := fun ha hb => (MaximalUnramifiedExtension l).add_mem ha hb
      zero_mem' := (MaximalUnramifiedExtension l).zero_mem
      smul_mem' := fun c y hy => (MaximalUnramifiedExtension l).smul_mem (x := (c : ℚ_[l])) hy }
  have := GlobalTheory.DiscEval.isAdicComplete_integralClosure L
  have := GlobalTheory.DiscEval.finite_residueField_integralClosure L
  let _ := Fintype.ofFinite (ResidueField (integralClosure ℤ_[l] L))
  have hle : (⊤ : Submodule ℤ_[l] (integralClosure ℤ_[l] L)) ≤ N := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal ℤ_[l])
      Module.Finite.fg_top (maximalIdeal_le_jacobson _) fun y _ => ?_
    obtain ⟨t, ht, hty⟩ := exists_pow_card_eq y
    have htN : t ∈ N := by
      change ((t : L) : Om l) ∈ MaximalUnramifiedExtension l
      by_cases h0 : ((t : L) : Om l) = 0
      · rw [h0]; exact zero_mem _
      have h1 : 1 < Fintype.card (ResidueField (integralClosure ℤ_[l] L)) := Fintype.one_lt_card
      refine IntermediateField.subset_adjoin _ _
        ⟨Fintype.card (ResidueField (integralClosure ℤ_[l] L)) - 1, by omega, ?_, ?_⟩
      · rintro ⟨c, hc⟩
        have h2 : (l : ResidueField (integralClosure ℤ_[l] L)) = 0 := by
          rw [← map_natCast (residue _), residue_eq_zero_iff, hmax]
          push_cast
          rw [norm_natCast_l]
          exact inv_lt_one_of_one_lt₀ hl1
        have h3 := congrArg (Nat.cast : ℕ → ResidueField (integralClosure ℤ_[l] L)) hc
        rw [Nat.cast_sub h1.le] at h3
        simp [h2] at h3
      · have h2 := congrArg (fun z : integralClosure ℤ_[l] L => ((z : L) : Om l)) ht
        push_cast at h2
        apply mul_right_cancel₀ h0
        rw [← pow_succ, Nat.sub_add_cancel h1.le, h2, one_mul]
    have hd : ((t - y : integralClosure ℤ_[l] L) : L) / l ∈ integralClosure ℤ_[l] L := by
      rw [hint]
      rw [hmax] at hty
      generalize ((t - y : integralClosure ℤ_[l] L) : L) = z at hty
      push_cast
      by_cases h0 : (z : Om l) = 0
      · simp [h0]
      obtain ⟨k, hk⟩ := h _ z.2 h0
      rw [hk, zpow_lt_one_iff_right₀ hl1] at hty
      rw [norm_div, hk, norm_natCast_l, div_inv_eq_mul, ← zpow_add_one₀ (by positivity)]
      exact zpow_le_one_of_nonpos₀ hl1.le (by omega)
    have he : y = t - (l : ℤ_[l]) • (⟨_, hd⟩ : integralClosure ℤ_[l] L) := by
      apply Subtype.ext
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
      push_cast
      field_simp
      ring
    rw [he]
    refine sub_mem (Submodule.mem_sup_left htN) (Submodule.mem_sup_right
      (Submodule.smul_mem_smul ?_ Submodule.mem_top))
    exact PadicInt.irreducible_p.not_isUnit
  exact hle Submodule.mem_top

theorem le_Kur_of_norm : ∀ (l : ℕ) [Fact l.Prime] (M : FinExt l),
    (∀ x ∈ M.1, x ≠ 0 → ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k) → M.1 ≤ MaximalUnramifiedExtension l := by
  intro l _ M h x hx
  obtain ⟨L, hL⟩ := M
  obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (A := integralClosure ℤ_[l] L) (⟨x, hx⟩ : L)
  have h1 : x = ((a : L) : Om l) / ((b : L) : Om l) := (congrArg Subtype.val hab).symm
  rw [h1]
  exact div_mem (integral_mem L h a) (integral_mem L h b)

end GlobalTheory.UnramValue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemUnramifiedOfFrobeniusIterateFixedFil
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemUnramifiedOfFrobeniusIterateFixedFil
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.CrisPerFix

variable {l : ℕ} [Fact l.Prime]

def maxUnramifiedFrobenius (P : LocPrime l) (K : FinExt l) : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥(K0 K) :=
  AlgEquiv.ofBijective (P.PD K).σ (P.PD K).σ_bij

theorem frobK0_apply (P : LocPrime l) (K : FinExt l) (x : ↥(K0 K)) :
    maxUnramifiedFrobenius P K x = (P.PD K).σ x := rfl

theorem nontrivial_B (P : LocPrime l) (K : FinExt l) : Nontrivial P.R.B := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact (P.PD K).not_mem_filtration_two (by rw [Subsingleton.elim ((P.PD K).t) 0, map_zero]; exact Submodule.zero_mem _)

theorem ιB_algebraMap (P : LocPrime l) (K : FinExt l) (a : ↥(K0 K)) :
    P.ιB (algebraMap ↥(K0 K) P.R.B a) = algebraMap ↥(K0 K) P.R.BdR a := by
  rw [← P.PD_ι K]
  exact (P.PD K).ι.commutes a

theorem orderOf_frobK0 (P : LocPrime l) (K : FinExt l) :
    orderOf (maxUnramifiedFrobenius P K) = finrank ℚ_[l] ↥(K0 K) := by
  haveI := (P.PD K).finK₀
  haveI := nontrivial_B P K
  have hfix : IntermediateField.fixedField (Subgroup.zpowers (maxUnramifiedFrobenius P K)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hσ : (P.PD K).σ x = x := hx _ (Subgroup.mem_zpowers _)
    obtain ⟨q, hq⟩ := (P.PD K).fund (algebraMap ↥(K0 K) P.R.B x)
      (by rw [(P.PD K).φ_K₀, hσ])
      (by
        rw [(P.PD K).ι.commutes, Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_of_tower_mem _ x (P.PD K).one_mem)
    rw [IntermediateField.mem_bot]
    refine ⟨q, (algebraMap ↥(K0 K) P.R.B).injective ?_⟩
    rw [← IsScalarTower.algebraMap_apply]
    exact hq
  have h := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers (maxUnramifiedFrobenius P K))
  rw [hfix, IntermediateField.finrank_bot', Nat.card_zpowers] at h
  exact h.symm

theorem iterate_φB_mul (P : LocPrime l) (K : FinExt l) (j : ℕ) (b : ↥(K0 K)) (x : P.R.B) :
    (⇑P.φB)^[j] (algebraMap ↥(K0 K) P.R.B b * x) =
      algebraMap ↥(K0 K) P.R.B ((maxUnramifiedFrobenius P K ^ j) b) * (⇑P.φB)^[j] x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, map_mul, ← P.PD_φ K (algebraMap _ _ _), (P.PD K).φ_K₀,
      Function.iterate_succ_apply', pow_succ', AlgEquiv.mul_apply, frobK0_apply]

theorem det_ne_zero (P : LocPrime l) (K : FinExt l)
    (bas : Module.Basis (Fin (finrank ℚ_[l] ↥(K0 K))) ℚ_[l] ↥(K0 K)) :
    (Matrix.of fun i j : Fin (finrank ℚ_[l] ↥(K0 K)) => (maxUnramifiedFrobenius P K ^ (j : ℕ)) (bas i)).det ≠ 0 := by
  set τ := maxUnramifiedFrobenius P K
  intro h
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  let L : ↥(K0 K) →ₗ[ℚ_[l]] ↥(K0 K) :=
    { toFun := fun x => ∑ j : Fin (finrank ℚ_[l] ↥(K0 K)), u j * (τ ^ (j : ℕ)) x
      map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_smul_comm]
        congr 1
        exact (τ ^ (j : ℕ)).toLinearEquiv.map_smul r x }
  have hL : L = 0 := by
    refine bas.ext fun i => ?_
    have := congrFun hu i
    simpa [L, Matrix.mulVec, dotProduct, mul_comm] using this
  let f : Fin (finrank ℚ_[l] ↥(K0 K)) → (↥(K0 K) →* ↥(K0 K)) := fun j => ((τ ^ (j : ℕ)).toRingEquiv : _ ≃+* _).toMonoidHom
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : τ ^ (i : ℕ) = τ ^ (j : ℕ) := AlgEquiv.ext fun x => DFunLike.congr_fun hij x
    have hi : (i : ℕ) ∈ Set.Iio (orderOf τ) := by rw [orderOf_frobK0]; exact i.2
    have hj : (j : ℕ) ∈ Set.Iio (orderOf τ) := by rw [orderOf_frobK0]; exact j.2
    exact Fin.ext (pow_injOn_Iio_orderOf hi hj h1)
  have li := (linearIndependent_monoidHom ↥(K0 K) ↥(K0 K)).comp f hf
  rw [Fintype.linearIndependent_iff] at li
  apply hu0
  funext j
  refine li u ?_ j
  funext x
  have := LinearMap.congr_fun hL x
  simpa [L, f, Finset.sum_apply, smul_eq_mul] using this

theorem mem_unramified_of_frobenius_iterate_fixed_fil_alt :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K : FinExt l) (c : P.R.B), (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] c = c →
    (∀ j : ℕ, P.ιB ((⇑P.φB)^[j] c) ∈ (P.PD K).Fil 0) →
    ∃ a : ↥(K0 K), c = algebraMap ↥(K0 K) P.R.B a := by
  intro l _ P _ _ K c hn hF
  set n := finrank ℚ_[l] ↥(K0 K) with hn_def
  haveI := (P.PD K).finK₀
  set τ := maxUnramifiedFrobenius P K
  have hord : orderOf τ = n := orderOf_frobK0 P K
  have hn0 : 0 < n := Module.finrank_pos
  let bas := Module.finBasisOfFinrankEq ℚ_[l] ↥(K0 K) hn_def.symm
  let A : Matrix (Fin n) (Fin n) ↥(K0 K) := Matrix.of fun i j => (τ ^ (j : ℕ)) (bas i)
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.2 (det_ne_zero P K bas)
  have hs : ∀ b : ↥(K0 K), ∃ q : ℚ_[l], algebraMap ℚ_[l] P.R.B q =
      ∑ j ∈ Finset.range n, (⇑P.φB)^[j] (algebraMap ↥(K0 K) P.R.B b * c) := by
    intro b
    apply (P.PD K).fund
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [P.PD_φ, map_sum]
        have e1 : ∀ j, P.φB ((⇑P.φB)^[j] (algebraMap ↥(K0 K) P.R.B b * c)) =
            (⇑P.φB)^[j + 1] (algebraMap ↥(K0 K) P.R.B b * c) :=
          fun j => (Function.iterate_succ_apply' _ _ _).symm
        simp_rw [e1]
        have hfn : (⇑P.φB)^[n] (algebraMap ↥(K0 K) P.R.B b * c) =
            (⇑P.φB)^[0] (algebraMap ↥(K0 K) P.R.B b * c) := by
          rw [iterate_φB_mul, hn, ← hord, pow_orderOf_eq_one, AlgEquiv.one_apply, Function.iterate_zero, id]
        have h := Finset.sum_range_succ' (fun j => (⇑P.φB)^[j] (algebraMap ↥(K0 K) P.R.B b * c)) n
        rw [Finset.sum_range_succ, hfn] at h
        exact (add_right_cancel h).symm
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [P.PD_ι, map_sum]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [iterate_φB_mul, map_mul, ιB_algebraMap, ← Algebra.smul_def]
        exact Submodule.smul_of_tower_mem _ _ (hF j)
  choose q hq using fun i => hs (bas i)
  let v : Fin n → P.R.B := fun j => (⇑P.φB)^[(j : ℕ)] c
  have hAv : Matrix.mulVec (A.map (algebraMap ↥(K0 K) P.R.B)) v =
      fun i => algebraMap ↥(K0 K) P.R.B (algebraMap ℚ_[l] ↥(K0 K) (q i)) := by
    funext i
    rw [← IsScalarTower.algebraMap_apply, hq i, Finset.sum_range]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, A, v, Matrix.of_apply, iterate_φB_mul]
    rfl
  have hinv : (A⁻¹.map (algebraMap ↥(K0 K) P.R.B)) * (A.map (algebraMap ↥(K0 K) P.R.B)) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hv : v = Matrix.mulVec (A⁻¹.map (algebraMap ↥(K0 K) P.R.B))
      (fun i => algebraMap ↥(K0 K) P.R.B (algebraMap ℚ_[l] ↥(K0 K) (q i))) := by
    rw [← hAv, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  refine ⟨∑ i, A⁻¹ ⟨0, hn0⟩ i * algebraMap ℚ_[l] ↥(K0 K) (q i), ?_⟩
  have h0 := congrFun hv ⟨0, hn0⟩
  simp only [v, Function.iterate_zero, id] at h0
  rw [h0]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

end GlobalTheory.CrisPerFix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemUnramifiedOfFrobeniusIterateFixedFilStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_unramified_of_frobenius_iterate_fixed_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (c : P.R.B), (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] c = c → (∀ j : ℕ, P.ιB ((⇑P.φB)^[j] c) ∈ (P.PD K).Fil 0) → ∃ a : ↥(K0 K), c = algebraMap ↥(K0 K) P.R.B a := by
  first | exact @GlobalTheory.CrisPerFix.mem_unramified_of_frobenius_iterate_fixed_fil_alt | exact GlobalTheory.CrisPerFix.mem_unramified_of_frobenius_iterate_fixed_fil_alt | (intros; apply GlobalTheory.CrisPerFix.mem_unramified_of_frobenius_iterate_fixed_fil_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittTiltLatticeTensorCancel
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittTiltLatticeTensorCancel
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL

theorem exists_cancel_tensor {R O A T : Type} [CommRing R] [CommRing O] [CommRing A] [Algebra R O]
    [Algebra R A] [AddCommGroup T] [Module O T] [Module R T] [IsScalarTower R O T] :
    ∃ κ : (A ⊗[R] T) ≃+ ((O ⊗[R] A) ⊗[O] T), ∀ (w : A) (t : T),
      κ (w ⊗ₜ[R] t) = ((1 : O) ⊗ₜ[R] w) ⊗ₜ[O] t := by
  haveI : SMulCommClass R O T := IsScalarTower.to_smulCommClass
  refine ⟨(TensorProduct.comm R A T).toAddEquiv.trans
    (((TensorProduct.AlgebraTensorModule.cancelBaseChange R O O T A).symm.toAddEquiv).trans
      (TensorProduct.comm O T (O ⊗[R] A)).toAddEquiv), fun w t => ?_⟩
  simp

theorem exists_cancel_tensor_compHom (R O A T : Type) [CommRing R] [CommRing O] [CommRing A] [Algebra R O]
    [Algebra R A] [AddCommGroup T] [Module O T] :
    letI : Module R T := Module.compHom T (algebraMap R O)
    ∃ κ : (A ⊗[R] T) ≃+ ((O ⊗[R] A) ⊗[O] T), ∀ (w : A) (t : T),
      κ (w ⊗ₜ[R] t) = ((1 : O) ⊗ₜ[R] w) ⊗ₜ[O] t := by
  letI : Module R T := Module.compHom T (algebraMap R O)
  haveI : IsScalarTower R O T := IsScalarTower.of_compHom R O T
  exact exists_cancel_tensor

theorem exists_kappa : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), letI := Formalism.MainNotions.LocalSituation.zlMod LL T; ∃ κ : (WCb l ⊗[ℤ_[l]] ↥T.L.T) ≃+ TW (RW LL) T, ∀ (w : WCb l) (t : ↥T.L.T), κ (w ⊗ₜ[ℤ_[l]] t) = TensorProduct.tmul ↥(OL LL) ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w : RW LL) t := by
  intro l _ K LL T
  exact exists_cancel_tensor_compHom ℤ_[l] ↥(OL LL) (WCb l) ↥T.L.T

end GlobalTheory.HWL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittTiltLatticeTensorCancelStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wittTilt_lattice_tensor_cancel : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), letI := Formalism.MainNotions.LocalSituation.zlMod LL T; ∃ κ : (WCb l ⊗[ℤ_[l]] ↥T.L.T) ≃+ TW (RW LL) T, ∀ (w : WCb l) (t : ↥T.L.T), κ (w ⊗ₜ[ℤ_[l]] t) = TensorProduct.tmul ↥(OL LL) ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w : RW LL) t := by
  first | exact @GlobalTheory.HWL.exists_kappa | exact GlobalTheory.HWL.exists_kappa | (intros; apply GlobalTheory.HWL.exists_kappa <;> assumption)
end
end

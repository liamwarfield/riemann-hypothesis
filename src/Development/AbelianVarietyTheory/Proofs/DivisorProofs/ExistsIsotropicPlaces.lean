module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactSpecialUnitarySupportedAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalVectorIsotropicNondegeneratePlanes

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormSolutionAdelicFromArchimedean
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormSolutionAdelicFromArchimedean
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

noncomputable section
namespace GlobalTheory
open Classical

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

theorem ainf_single_mul (a b : w.Completion) :
    (show Ainf F from Pi.single w (a * b)) = (show Ainf F from Pi.single w a) * (show Ainf F from Pi.single w b) := by
  funext u
  change (Pi.single w (a*b) : ∀ v : InfinitePlace F, v.Completion) u =
    (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u * (Pi.single w b : ∀ v : InfinitePlace F, v.Completion) u
  by_cases h : u = w
  · subst h; simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne h, mul_zero]

theorem ainf_idem_mul (e : Ainf F) (h1 : e w = 1) (h0 : ∀ u, u ≠ w → e u = 0) (a : w.Completion) :
    e * (show Ainf F from Pi.single w a) = (show Ainf F from Pi.single w a) := by
  funext u
  change (e : ∀ v : InfinitePlace F, v.Completion) u * (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u = (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u
  by_cases h : u = w
  · subst h; rw [h1, one_mul]
  · simp only [Pi.single_eq_of_ne h, mul_zero]

theorem ainf_single_one (e : Ainf F) (h1 : e w = 1) (h0 : ∀ u, u ≠ w → e u = 0) :
    (show Ainf F from Pi.single w 1) = e := by
  funext u
  change (Pi.single w 1 : ∀ v : InfinitePlace F, v.Completion) u = e u
  by_cases h : u = w
  · subst h; rw [h1, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, h0 u h]

theorem af_zero (y : Af F) (h : ∀ v, evalV F v y = 0) : y = 0 := by
  ext v
  exact congrArg _ (h v)

theorem af_ext {p q : AF F} (h1 : fstA F p = fstA F q) (h2 : sndA F p = sndA F q) : p = q :=
  Prod.ext h1 h2

def placeAtInf : w.Completion →ₗ[F] AF F :=
  (LinearMap.inl F (Ainf F) (Af F)).comp (LinearMap.single F (fun u : InfinitePlace F => u.Completion) w)

theorem fstA_placeAtInf (a : w.Completion) : fstA F (placeAtInf F w a) = (show Ainf F from Pi.single w a) := rfl
theorem sndA_placeAtInf (a : w.Completion) : sndA F (placeAtInf F w a) = 0 := rfl

theorem placeAtInf_mul (a b : w.Completion) :
    placeAtInf F w (a * b) = placeAtInf F w a * placeAtInf F w b := by
  apply af_ext
  · have e2 : fstA F (placeAtInf F w a * placeAtInf F w b) =
        fstA F (placeAtInf F w a) * fstA F (placeAtInf F w b) := map_mul (fstA F) _ _
    exact (fstA_placeAtInf F w (a * b)).trans ((ainf_single_mul F w a b).trans
      (e2.trans (congrArg₂ (· * ·) (fstA_placeAtInf F w a) (fstA_placeAtInf F w b))).symm)
  · have e2 : sndA F (placeAtInf F w a * placeAtInf F w b) =
        sndA F (placeAtInf F w a) * sndA F (placeAtInf F w b) := map_mul (sndA F) _ _
    exact (sndA_placeAtInf F w (a * b)).trans ((mul_zero (0 : Af F)).symm.trans
      (e2.trans (congrArg₂ (· * ·) (sndA_placeAtInf F w a) (sndA_placeAtInf F w b))).symm)

variable {F w}

theorem idem_mul_placeAtInf {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) (a : w.Completion) :
    ε * placeAtInf F w a = placeAtInf F w a := by
  apply af_ext
  · have e2 : fstA F (ε * placeAtInf F w a) = fstA F ε * fstA F (placeAtInf F w a) := map_mul (fstA F) _ _
    exact e2.trans ((congrArg (fstA F ε * ·) (fstA_placeAtInf F w a)).trans
      ((ainf_idem_mul F w _ (hε.1 w (Finset.mem_singleton_self w))
        (fun u hu => hε.2.1 u (by simpa using hu)) a).trans (fstA_placeAtInf F w a).symm))
  · have e2 : sndA F (ε * placeAtInf F w a) = sndA F ε * sndA F (placeAtInf F w a) := map_mul (sndA F) _ _
    exact e2.trans ((congrArg (sndA F ε * ·) (sndA_placeAtInf F w a)).trans
      ((mul_zero _).trans (sndA_placeAtInf F w a).symm))

theorem placeAtInf_one {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) : placeAtInf F w 1 = ε := by
  apply af_ext
  · refine (fstA_placeAtInf F w 1).trans ?_
    exact ainf_single_one F w _ (hε.1 w (Finset.mem_singleton_self w))
      (fun u hu => hε.2.1 u (by simpa using hu))
  · refine (sndA_placeAtInf F w 1).trans ?_
    exact (af_zero F _ (fun v => hε.2.2.2 v (Finset.notMem_empty v))).symm

variable (F w) (E : Type) [Field E] [Algebra F E]

def placeAtInfE : w.Completion ⊗[F] E →ₗ[F] AF F ⊗[F] E :=
  LinearMap.rTensor E (placeAtInf F w)

theorem placeAtInfE_tmul (a : w.Completion) (e : E) :
    placeAtInfE F w E (a ⊗ₜ e) = placeAtInf F w a ⊗ₜ e := rfl

theorem placeAtInfE_mul (x y : w.Completion ⊗[F] E) :
    placeAtInfE F w E (x * y) = placeAtInfE F w E x * placeAtInfE F w E y := by
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | add a b ha hb => rw [add_mul, map_add (f := _), map_add (f := _), ha, hb, add_mul]
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | add c d hc hd => rw [mul_add, map_add (f := _), map_add (f := _), hc, hd, mul_add]
    | tmul b f =>
      unfold placeAtInfE
      rw [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
        LinearMap.rTensor_tmul, Algebra.TensorProduct.tmul_mul_tmul, placeAtInf_mul]

theorem placeAtInfE_sig (σ : E →ₐ[F] E) (x : w.Completion ⊗[F] E) :
    placeAtInfE F w E (sigR w.Completion σ x) = sigR (AF F) σ (placeAtInfE F w E x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂]
  | tmul a e =>
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, placeAtInfE_tmul]

variable {F w E}

theorem idem_mul_placeAtInfE {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) (x : w.Completion ⊗[F] E) :
    algebraMap (AF F) (AF F ⊗[F] E) ε * placeAtInfE F w E x = placeAtInfE F w E x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [mul_add, map_add (f := _), h₁, h₂]
  | tmul a e =>
    rw [placeAtInfE_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, Algebra.algebraMap_self, RingHom.id_apply, idem_mul_placeAtInf hε]

theorem placeAtInfE_incl {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) (c : E) :
    placeAtInfE F w E (inclR w.Completion c) = algebraMap (AF F) (AF F ⊗[F] E) ε * inclR (AF F) c := by
  simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    placeAtInfE_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    mul_one, Algebra.algebraMap_self, RingHom.id_apply, placeAtInf_one hε]

theorem normEq_inf_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (w : InfinitePlace F) (ε : AF F), IsPlacesIdem {w} ∅ ε → ∀ c : E,
    (∃ t : w.Completion ⊗[F] E, t * sigR w.Completion σ t + inclR w.Completion c = 0) →
    ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) c) = 0 := by
  intro F E _ _ _ _ σ w ε hε c ⟨t, ht⟩
  refine ⟨placeAtInfE F w E t, ?_⟩
  rw [← placeAtInfE_sig, ← placeAtInfE_mul, mul_add, idem_mul_placeAtInfE hε, ← placeAtInfE_incl hε,
    ← map_add, ht, map_zero]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormSolutionAdelicFromArchimedeanStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_solution_adelic_from_archimedean : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (w : InfinitePlace F) (ε : AF F), IsPlacesIdem {w} ∅ ε → ∀ c : E, (∃ t : w.Completion ⊗[F] E, t * sigR w.Completion σ t + inclR w.Completion c = 0) → ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) c) = 0 := by
  first | exact @GlobalTheory.normEq_inf_place | exact GlobalTheory.normEq_inf_place | (intros; apply GlobalTheory.normEq_inf_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentAdelicNormEqOfLocalNormEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentAdelicNormEqOfLocalNormEq
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open GlobalTheory.Published.StrongApprox
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.NormFin

variable {F : Type} [Field F] [NumberField F]

theorem af_ext {x y : Af F} (h : ∀ w, evalV F w x = evalV F w y) : x = y :=
  by
  apply RestrictedProduct.ext
  intro w
  exact h w

def iotaL (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] AF F where
  toFun a := pairA F 0 (singleV F v a)
  map_add' a b := by
    refine Prod.ext (by change (0 : Ainf F) = 0 + 0; simp) ?_
    change singleV F v (a + b) = singleV F v a + singleV F v b
    refine af_ext fun w => ?_
    rw [map_add (f := _)]
    by_cases hw : w = v
    · subst hw; simp only [evalV_single_same]
    · simp only [evalV_single_ne hw, add_zero]
  map_smul' c a := by
    refine Prod.ext (by change (0 : Ainf F) = c • 0; simp) ?_
    change singleV F v (c • a) = c • singleV F v a
    refine af_ext fun w => ?_
    rw [map_smul]
    by_cases hw : w = v
    · subst hw; simp only [evalV_single_same]
    · simp only [evalV_single_ne hw, smul_zero]

theorem iotaL_mul (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) :
    iotaL v (a * b) = iotaL v a * iotaL v b := by
  refine Prod.ext (by change (0 : Ainf F) = 0 * 0; simp) ?_
  change singleV F v (a * b) = singleV F v a * singleV F v b
  refine af_ext fun w => ?_
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; simp only [evalV_single_same]
  · simp only [evalV_single_ne hw, mul_zero]

theorem idem_mul_iotaL (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : IsPlacesIdem ∅ {v} ε) (a : Fv F v) :
    ε * iotaL v a = iotaL v a := by
  refine Prod.ext (by change fstA F ε * 0 = 0; simp) ?_
  change sndA F ε * singleV F v a = singleV F v a
  refine af_ext fun w => ?_
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rw [hε.2.2.1 w (Finset.mem_singleton_self w), one_mul]
  · simp only [evalV_single_ne hw, mul_zero]

theorem iotaL_one (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : IsPlacesIdem ∅ {v} ε) :
    iotaL v 1 = ε := by
  refine Prod.ext ?_ ?_
  · funext w
    exact (hε.2.1 w (Finset.notMem_empty w)).symm
  · change singleV F v 1 = sndA F ε
    refine af_ext fun w => ?_
    by_cases hw : w = v
    · subst hw; rw [evalV_single_same, hε.2.2.1 w (Finset.mem_singleton_self w)]
    · rw [evalV_single_ne hw, hε.2.2.2 w (fun h => hw (Finset.mem_singleton.1 h))]

section Tensor

variable {E : Type} [Field E] [Algebra F E]

def phi (v : HeightOneSpectrum (𝓞 F)) : Fv F v ⊗[F] E →ₗ[F] AF F ⊗[F] E :=
  TensorProduct.map (iotaL v) LinearMap.id

theorem phi_tmul (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (e : E) :
    phi v (a ⊗ₜ[F] e) = iotaL v a ⊗ₜ[F] e := TensorProduct.map_tmul _ _ _ _

theorem phi_mul (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v ⊗[F] E) :
    phi v (x * y) = phi v x * phi v y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b f =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, phi_tmul, phi_tmul, phi_tmul, iotaL_mul,
        Algebra.TensorProduct.tmul_mul_tmul]
    | add y z hy hz => rw [mul_add, map_add (f := _), hy, hz, map_add (f := _), mul_add]
  | add x z hx hz => rw [add_mul, map_add (f := _), hx, hz, map_add (f := _), add_mul]

theorem phi_sig (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v ⊗[F] E) :
    phi v (sigR (Fv F v) σ x) = sigR (AF F) σ (phi v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, phi_tmul]
  | add x z hx hz => rw [map_add (f := _), map_add (f := _), hx, hz, map_add (f := _), map_add (f := _)]

theorem idem_mul_phi (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : IsPlacesIdem ∅ {v} ε)
    (x : Fv F v ⊗[F] E) : algebraMap (AF F) (AF F ⊗[F] E) ε * phi v x = phi v x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, phi_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, idem_mul_iotaL v ε hε]
  | add x z hx hz => rw [map_add (f := _), mul_add, hx, hz]

theorem phi_inclR (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : IsPlacesIdem ∅ {v} ε) (c : E) :
    phi v (inclR (Fv F v) c) = algebraMap (AF F) (AF F ⊗[F] E) ε * inclR (AF F) c := by
  change phi v ((1 : Fv F v) ⊗ₜ[F] c) = algebraMap (AF F) (AF F ⊗[F] E) ε * ((1 : AF F) ⊗ₜ[F] c)
  rw [phi_tmul, iotaL_one v ε hε, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end Tensor

theorem idem_norm_eq_of_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (ε : AF F), IsPlacesIdem ∅ {v} ε → ∀ c : E,
    (∃ t : Fv F v ⊗[F] E, t * sigR (Fv F v) σ t + inclR (Fv F v) c = 0) →
    ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) c) = 0 := by
  intro F E _ _ _ _ σ v ε hε c ⟨t, ht⟩
  refine ⟨phi v t, ?_⟩
  rw [← phi_sig, ← phi_mul, mul_add, idem_mul_phi v ε hε, ← phi_inclR v ε hε, ← map_add (f := _), ht, map_zero]

end GlobalTheory.NormFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentAdelicNormEqOfLocalNormEqStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_adelic_norm_eq_of_local_norm_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (ε : AF F), IsPlacesIdem ∅ {v} ε → ∀ c : E, (∃ t : Fv F v ⊗[F] E, t * sigR (Fv F v) σ t + inclR (Fv F v) c = 0) → ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) c) = 0 := by
  first | exact @GlobalTheory.NormFin.idem_norm_eq_of_local | exact GlobalTheory.NormFin.idem_norm_eq_of_local | (intros; apply GlobalTheory.NormFin.idem_norm_eq_of_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSetUnitaryHermitianReal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSetUnitaryHermitianReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.AnisoCpt

open Metric Matrix

section Gen

variable {K : Type} [NontriviallyNormedField K] [ProperSpace K] {n m : ℕ}

theorem exists_mul_sq_le (Q : (Fin n → K) → (Fin m → K)) (hc : Continuous Q)
    (hs : ∀ (c : K) y, Q (c • y) = (c * c) • Q y) (h0 : ∀ y, Q y = 0 → y = 0) :
    ∃ a > 0, ∀ y, a * ‖y‖ ^ 2 ≤ ‖Q y‖ := by
  have hns : ∀ (c : K) y, ‖Q (c • y)‖ = ‖c‖ * ‖c‖ * ‖Q y‖ := fun c y => by
    rw [hs, norm_smul, norm_mul]
  obtain ⟨c, hc1⟩ := NormedField.exists_one_lt_norm K
  have hc0 : 0 < ‖c‖ := lt_trans one_pos hc1
  let S : Set (Fin n → K) := {y | 1 / ‖c‖ ≤ ‖y‖ ∧ ‖y‖ ≤ 1}
  have hSc : IsCompact S := (isCompact_closedBall (0 : Fin n → K) 1).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
    (fun y hy => mem_closedBall_zero_iff.2 hy.2)
  have hcont : Continuous fun y => ‖Q y‖ := hc.norm
  by_cases hS : S.Nonempty
  · obtain ⟨y₀, hy₀S, hmin⟩ := hSc.exists_isMinOn hS hcont.continuousOn
    have hy₀ : y₀ ≠ 0 := by
      intro h
      have := hy₀S.1
      rw [h, norm_zero] at this
      exact absurd this (not_le.2 (by positivity))
    refine ⟨‖Q y₀‖, norm_pos_iff.2 (fun h => hy₀ (h0 _ h)), fun y => ?_⟩
    by_cases hy : y = 0
    · rw [hy, norm_zero]
      simp
    obtain ⟨d, hd0, hdlt, hdge, -⟩ := rescale_to_shell hc1 one_pos hy
    have hdS : d • y ∈ S := ⟨hdge, hdlt.le⟩
    have h1 : ‖Q y₀‖ ≤ ‖d‖ * ‖d‖ * ‖Q y‖ := by
      rw [← hns]
      exact hmin hdS
    have h2 : ‖d‖ * ‖y‖ < 1 := by
      rw [← norm_smul]
      exact hdlt
    have hn := norm_nonneg y
    have hd := norm_nonneg d
    have hf := norm_nonneg (Q y)
    have h3 : (‖d‖ * ‖y‖) ^ 2 ≤ 1 := by nlinarith [mul_nonneg hd hn]
    calc ‖Q y₀‖ * ‖y‖ ^ 2 ≤ ‖d‖ * ‖d‖ * ‖Q y‖ * ‖y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = ‖Q y‖ * (‖d‖ * ‖y‖) ^ 2 := by ring
      _ ≤ ‖Q y‖ * 1 := mul_le_mul_of_nonneg_left h3 hf
      _ = ‖Q y‖ := mul_one _
  · refine ⟨1, one_pos, fun y => ?_⟩
    by_cases hy : y = 0
    · rw [hy, norm_zero]
      simp
    obtain ⟨d, -, hdlt, hdge, -⟩ := rescale_to_shell hc1 one_pos hy
    exact absurd ⟨d • y, hdge, hdlt.le⟩ hS

theorem exists_le_mul_sq (Q : (Fin n → K) → (Fin m → K)) (hc : Continuous Q)
    (hs : ∀ (c : K) y, Q (c • y) = (c * c) • Q y) :
    ∃ B ≥ 0, ∀ y, ‖Q y‖ ≤ B * ‖y‖ ^ 2 := by
  have hns : ∀ (c : K) y, ‖Q (c • y)‖ = ‖c‖ * ‖c‖ * ‖Q y‖ := fun c y => by
    rw [hs, norm_smul, norm_mul]
  have hQ0 : Q 0 = 0 := by simpa using hs 0 0
  obtain ⟨c, hc1⟩ := NormedField.exists_one_lt_norm K
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : Fin n → K) 1).exists_bound_of_continuousOn
    hc.continuousOn
  have hM₀0 : 0 ≤ M₀ := le_trans (norm_nonneg _) (hM₀ 0 (mem_closedBall_self zero_le_one))
  refine ⟨M₀ * ‖c‖ ^ 2, by positivity, fun y => ?_⟩
  by_cases hy : y = 0
  · rw [hy, hQ0, norm_zero]
    positivity
  obtain ⟨d, hd0, hdlt, -, hdinv⟩ := rescale_to_shell hc1 one_pos hy
  have h1 := hM₀ (d • y) (mem_closedBall_zero_iff.2 hdlt.le)
  rw [hns] at h1
  have ht : ‖d‖⁻¹ ≤ ‖c‖ * ‖y‖ := by simpa using hdinv
  have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hd0
  have hf : ‖Q y‖ = ‖d‖⁻¹ ^ 2 * (‖d‖ * ‖d‖ * ‖Q y‖) := by
    field_simp
  calc ‖Q y‖ = ‖d‖⁻¹ ^ 2 * (‖d‖ * ‖d‖ * ‖Q y‖) := hf
    _ ≤ ‖d‖⁻¹ ^ 2 * M₀ := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ ≤ (‖c‖ * ‖y‖) ^ 2 * M₀ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (inv_nonneg.2 hdpos.le) ht 2) hM₀0
    _ = M₀ * ‖c‖ ^ 2 * ‖y‖ ^ 2 := by ring

end Gen

theorem hform_eq {A : Type} [CommRing A] {n : Type} [Fintype n] (c : A →+* A) (J : Matrix n n A)
    (x y : n → A) : Formalism.UG.hform c J x y = (fun i => c (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] (c : A →+* A)
    (J g : Matrix n n A) (x : n → A) :
    Formalism.UG.hform c J (g *ᵥ x) (g *ᵥ x) = Formalism.UG.hform c (Formalism.UG.cT c g * J * g) x x := by
  have h1 : (fun i => c ((g *ᵥ x) i)) = (g.map c) *ᵥ (fun i => c (x i)) := by
    funext i
    exact RingHom.map_mulVec _ _ _ i
  rw [hform_eq, hform_eq, h1, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc, Matrix.dotProduct_mulVec]
  rfl

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E] (K : Type) [Field K] [Algebra F K]

theorem sigR_smul (σ : E →ₐ[F] E) (c : K) (z : K ⊗[F] E) : sigR K σ (c • z) = c • sigR K σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]

def sigL (σ : E →ₐ[F] E) : K ⊗[F] E →ₗ[K] K ⊗[F] E where
  toFun := sigR K σ
  map_add' := map_add _
  map_smul' := sigR_smul K σ

theorem hR_smul (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : K)
    (x : Fin M → K ⊗[F] E) : hR K σ J (c • x) (c • x) = (c * c) • hR K σ J x x := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, sigR_smul, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum, smul_smul]

end Tens

end GlobalTheory.AnisoCpt

namespace GlobalTheory.AnisoCpt

open Metric Matrix

theorem exists_isCompact_entries_of_anisotropic :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (K : Type) [NontriviallyNormedField K] [ProperSpace K] [Algebra F K] (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ u : Fin M → K ⊗[F] E, hR K σ J u u = 0 → u = 0) →
    ∃ C : Set (K ⊗[F] E), IsCompact C ∧ ∀ g : Matrix (Fin M) (Fin M) (K ⊗[F] E),
      Formalism.UG.cT (sigR K σ) g * JR K J * g = JR K J → ∀ i j, g i j ∈ C := by
  intro F E _ _ _ _ _ σ hcm K _ _ _ M J _ haniso
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hcm.2.2.1]; norm_num)
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (K ⊗[F] E) := IsModuleTopology.isTopologicalRing K _
  let bV := Module.finBasis K (Fin M → K ⊗[F] E)
  let bE := Module.finBasis K (K ⊗[F] E)
  let φ := bV.equivFun
  let ψ := bE.equivFun
  have hφs : Continuous φ.symm := IsModuleTopology.continuous_of_linearMap φ.symm.toLinearMap
  have hψ : Continuous ψ := IsModuleTopology.continuous_of_linearMap ψ.toLinearMap
  have hs : Continuous (sigR K σ) := IsModuleTopology.continuous_of_linearMap (sigL K σ)
  have hhc : Continuous fun x : Fin M → K ⊗[F] E => hR K σ J x x := by
    show Continuous fun x => Formalism.UG.hform (sigR K σ) (JR K J) x x
    unfold Formalism.UG.hform
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((hs.comp (continuous_apply i)).mul continuous_const).mul (continuous_apply j)
  let Q : (Fin (Module.finrank K (Fin M → K ⊗[F] E)) → K) → (Fin (Module.finrank K (K ⊗[F] E)) → K) :=
    fun y => ψ (hR K σ J (φ.symm y) (φ.symm y))
  have hQc : Continuous Q := hψ.comp (hhc.comp hφs)
  have hQs : ∀ (c : K) y, Q (c • y) = (c * c) • Q y := by
    intro c y
    simp only [Q, map_smul, hR_smul]
  have hQ0 : ∀ y, Q y = 0 → y = 0 := by
    intro y hy
    have h1 : hR K σ J (φ.symm y) (φ.symm y) = 0 := by
      exact ψ.injective (hy.trans (map_zero ψ).symm)
    have h2 := haniso _ h1
    simpa using congrArg φ h2
  obtain ⟨a, ha, hlow⟩ := exists_mul_sq_le Q hQc hQs hQ0
  obtain ⟨B, hB, hup⟩ := exists_le_mul_sq Q hQc hQs
  have hunit : ∀ g : Matrix (Fin M) (Fin M) (K ⊗[F] E),
      Formalism.UG.cT (sigR K σ) g * JR K J * g = JR K J → ∀ x, hR K σ J (g *ᵥ x) (g *ᵥ x) = hR K σ J x x := by
    intro g hg x
    show Formalism.UG.hform _ _ _ _ = Formalism.UG.hform _ _ _ _
    rw [hform_mulVec, hg]
  let e : Fin M → Fin (Module.finrank K (Fin M → K ⊗[F] E)) → K := fun j => φ (Pi.single j 1)
  let D := ∑ j, ‖e j‖ ^ 2
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun j _ => sq_nonneg _
  let r := B / a * D + 1
  refine ⟨⋃ i : Fin M, (fun y => φ.symm y i) '' closedBall 0 r,
    isCompact_iUnion fun i => (isCompact_closedBall _ _).image ((continuous_apply i).comp hφs), ?_⟩
  intro g hg i j
  refine Set.mem_iUnion.2 ⟨i, φ (g *ᵥ Pi.single j 1), ?_, ?_⟩
  · rw [mem_closedBall_zero_iff]
    set t := ‖φ (g *ᵥ Pi.single j 1)‖
    have ht : 0 ≤ t := norm_nonneg _
    have h1 := hlow (φ (g *ᵥ Pi.single j 1))
    have hQeq : Q (φ (g *ᵥ Pi.single j 1)) = Q (e j) := by
      simp only [Q, e, LinearEquiv.symm_apply_apply, hunit g hg]
    rw [hQeq] at h1
    have h2 := hup (e j)
    have hej : ‖e j‖ ^ 2 ≤ D :=
      Finset.single_le_sum (f := fun j => ‖e j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j)
    have h3 : t ^ 2 ≤ B / a * D := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ha]
      nlinarith
    have h4 : 0 ≤ B / a * D := mul_nonneg (div_nonneg hB ha.le) hD0
    nlinarith [sq_nonneg (t - 1)]
  · simp only [LinearEquiv.symm_apply_apply]
    rw [Matrix.mulVec_single_one]
    rfl

end GlobalTheory.AnisoCpt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSetUnitaryHermitianRealStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_set_unitary_hermitian_real : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [NontriviallyNormedField K] [ProperSpace K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ u : Fin M → K ⊗[F] E, hR K σ J u u = 0 → u = 0) → ∃ C : Set (K ⊗[F] E), IsCompact C ∧ ∀ g : Matrix (Fin M) (Fin M) (K ⊗[F] E), Formalism.UG.cT (sigR K σ) g * JR K J * g = JR K J → ∀ i j, g i j ∈ C := by
  first | exact @GlobalTheory.AnisoCpt.exists_isCompact_entries_of_anisotropic | exact GlobalTheory.AnisoCpt.exists_isCompact_entries_of_anisotropic | (intros; apply GlobalTheory.AnisoCpt.exists_isCompact_entries_of_anisotropic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicPlaces
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.PlaceIso

theorem denseRange_algebraMap_completion : ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), DenseRange (algebraMap F w.Completion) := by
  intro F _ _ w y
  have h := InfinitePlace.Completion.denseRange_coe w y
  convert h using 2
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(WithAbs.equiv w.1).symm x, ?_⟩
    simp [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
  · rintro ⟨x, rfl⟩
    refine ⟨WithAbs.equiv w.1 x, ?_⟩
    simp [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]

theorem exists_isotropic_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∃ (S₁' : Finset (InfinitePlace F)) (S₂' : Finset (HeightOneSpectrum (𝓞 F))) (ε' : AF F), S₁' ⊆ S₁ ∧ S₂' ⊆ S₂ ∧ (S₁'.Nonempty ∨ S₂'.Nonempty) ∧ IsPlacesIdem S₁' S₂' ε' ∧ ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0) := by
  intro F E _ _ _ _ _ σ hσ M J hM hJ S₁ S₂ ε hε hnc
  classical
  have key : (∃ w ∈ S₁, ∃ u : Fin M → w.Completion ⊗[F] E, u ≠ 0 ∧ hR w.Completion σ J u u = 0) ∨
      (∃ v ∈ S₂, ∃ u : Fin M → Fv F v ⊗[F] E, u ≠ 0 ∧ hR (Fv F v) σ J u u = 0) := by
    by_contra hno
    push_neg at hno
    apply hnc
    apply GlobalTheory.T.isCompact_specialUnitary_supportedAtPlaces F E σ hσ M J hJ S₁ S₂ ε hε
    · intro w hw
      letI := GroundTheory.Automorphic.completionNontriviallyNormedField (K := F) w
      exact GlobalTheory.T.exists_compact_set_unitary_hermitian_real F E σ hσ w.Completion M J hJ (fun u hu => by
        by_contra h
        exact hno.1 w hw u h hu)
    · intro v hv
      letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
      haveI := Formalism.BasicNotions.Examples₂.LocF.proper v
      exact GlobalTheory.T.exists_compact_set_unitary_hermitian_real F E σ hσ (Fv F v) M J hJ (fun u hu => by
        by_contra h
        exact hno.2 v hv u h hu)
  rcases key with ⟨w, hw, u, hu0, hu⟩ | ⟨v, hv, u, hu0, hu⟩
  · obtain ⟨ε', hε'⟩ := GlobalTheory.Published.StrongApprox.exists_isPlacesIdem (F := F) {w} ∅
    refine ⟨{w}, ∅, ε', Finset.singleton_subset_iff.2 hw, Finset.empty_subset _,
      Or.inl (Finset.singleton_nonempty w), hε', ?_⟩
    intro x y hx hy
    letI := GroundTheory.Automorphic.completionNontriviallyNormedField (K := F) w
    obtain ⟨z, hz, ⟨h1, ht1⟩, ⟨h2, ht2⟩⟩ :=
      GlobalTheory.T.exists_rational_vector_isotropic_nondegenerate_planes_at_place F E σ hσ w.Completion (denseRange_algebraMap_completion F w) M J hM hJ ⟨u, hu0, hu⟩ x y hx hy
    exact ⟨z, hz, ⟨h1, GlobalTheory.T.exists_norm_solution_adelic_from_archimedean F E σ w ε' hε' _ ht1⟩, ⟨h2, GlobalTheory.T.exists_norm_solution_adelic_from_archimedean F E σ w ε' hε' _ ht2⟩⟩
  · obtain ⟨ε', hε'⟩ := GlobalTheory.Published.StrongApprox.exists_isPlacesIdem (F := F) ∅ {v}
    refine ⟨∅, {v}, ε', Finset.empty_subset _, Finset.singleton_subset_iff.2 hv,
      Or.inr (Finset.singleton_nonempty v), hε', ?_⟩
    intro x y hx hy
    letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
    obtain ⟨z, hz, ⟨h1, ht1⟩, ⟨h2, ht2⟩⟩ :=
      GlobalTheory.T.exists_rational_vector_isotropic_nondegenerate_planes_at_place F E σ hσ (Fv F v) (HeightOneSpectrum.denseRange_algebraMap F v) M J hM hJ ⟨u, hu0, hu⟩ x y hx hy
    exact ⟨z, hz, ⟨h1, GlobalTheory.T.idempotent_adelic_norm_eq_of_local_norm_eq F E σ v ε' hε' _ ht1⟩, ⟨h2, GlobalTheory.T.idempotent_adelic_norm_eq_of_local_norm_eq F E σ v ε' hε' _ ht2⟩⟩
end GlobalTheory.PlaceIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicPlacesStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_places_alt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∃ (S₁' : Finset (InfinitePlace F)) (S₂' : Finset (HeightOneSpectrum (𝓞 F))) (ε' : AF F), S₁' ⊆ S₁ ∧ S₂' ⊆ S₂ ∧ (S₁'.Nonempty ∨ S₂'.Nonempty) ∧ IsPlacesIdem S₁' S₂' ε' ∧ ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0) := by
  first | exact @GlobalTheory.PlaceIso.exists_isotropic_places | exact GlobalTheory.PlaceIso.exists_isotropic_places | (intros; apply GlobalTheory.PlaceIso.exists_isotropic_places <;> assumption)
end

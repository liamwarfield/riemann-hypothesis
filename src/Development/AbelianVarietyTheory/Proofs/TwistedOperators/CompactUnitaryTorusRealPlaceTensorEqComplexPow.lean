module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CxRootsInjective
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RealTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}
  (P : PPol σ r) {w : InfinitePlace F} (τ : EmbOver E w)

theorem cxRoots_root (i : Fin r) : eval₂ τ.1 (cxRoots τ.1 P i) P.1 = 0 := by
  rw [← eval_map, cxRoots_spec, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

theorem cxRoots_injective : Function.Injective (cxRoots τ.1 P) := by
  have hs : (P.1.map τ.1).Separable := (PerfectField.separable_of_irreducible P.2.2.1).map
  have hn := nodup_roots hs
  rw [cxRoots_spec, ← Finset.prod_map_val,
    show Multiset.map (fun i => X - C (cxRoots τ.1 P i)) Finset.univ.val =
      Multiset.map (fun a => X - C a) (Finset.univ.val.map (cxRoots τ.1 P)) by rw [Multiset.map_map]; rfl,
    roots_multiset_prod_X_sub_C] at hn
  exact fun i j h => (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).1 hn i (by simp) j (by simp) h

theorem finrank_Fld : Module.finrank E (Fld P) = r :=
  ((AdjoinRoot.powerBasis P.2.2.1.ne_zero).finrank.trans (AdjoinRoot.powerBasis_dim _)).trans P.2.2.2.1

def psiL (i : Fin r) : Fld P →+* ℂ := AdjoinRoot.lift τ.1 (cxRoots τ.1 P i) (cxRoots_root P τ i)

@[simp] theorem psiL_algebraMap (i : Fin r) (e : E) : psiL P τ i (algebraMap E (Fld P) e) = τ.1 e :=
  AdjoinRoot.lift_of _

@[simp] theorem psiL_alpha (i : Fin r) : psiL P τ i (alpha P) = cxRoots τ.1 P i := AdjoinRoot.lift_root _

theorem psiL_algebraMap_F (i : Fin r) (a : F) : psiL P τ i (algebraMap F (Fld P) a) = w.embedding a := by
  rw [IsScalarTower.algebraMap_apply F E (Fld P), psiL_algebraMap]
  exact RingHom.congr_fun τ.2 a

def Psi (i : Fin r) : w.Completion ⊗[F] Fld P →+* ℂ :=
  letI : Algebra F ℂ := w.embedding.toAlgebra
  (Algebra.TensorProduct.productMap
    ({ InfinitePlace.Completion.extensionEmbedding w with
        commutes' := fun a => by
          change InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion a) = w.embedding a
          rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
            Algebra.algebraMap_self_apply, InfinitePlace.Completion.extensionEmbedding_coe,
            ← WithAbs.equiv_symm_apply, RingEquiv.apply_symm_apply] } :
      w.Completion →ₐ[F] ℂ)
    ({ psiL P τ i with commutes' := fun a => psiL_algebraMap_F P τ i a } : Fld P →ₐ[F] ℂ)).toRingHom

@[simp] theorem Psi_tmul (i : Fin r) (a : w.Completion) (y : Fld P) :
    Psi P τ i (a ⊗ₜ[F] y) = InfinitePlace.Completion.extensionEmbedding w a * psiL P τ i y := rfl

def PsiAll : w.Completion ⊗[F] Fld P →+* (Fin r → ℂ) := Pi.ringHom (Psi P τ)

@[simp] theorem PsiAll_apply (y : w.Completion ⊗[F] Fld P) (i : Fin r) : PsiAll P τ y i = Psi P τ i y := rfl

end GlobalTheory.TrEll.RealTorus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusFieldComplexRootsNormEqOneCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusFieldComplexRootsNormEqOneCompact
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll GlobalTheory.TrEll.RealTorus
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RealTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}
  (P : PPol σ r) {w : InfinitePlace F} (τ : EmbOver E w)

theorem exists_conjInv_root (hCM : IsCMExt F E σ) (m : Fin r) :
    ∃ j, cxRoots τ.1 P j = (conj (cxRoots τ.1 P m))⁻¹ := by
  let φ : Fld P →+* ℂ := (starRingEnd ℂ).comp ((psiL P τ m).comp (star' P : Fld P →+* Fld P))
  have hE : φ.comp (algebraMap E (Fld P)) = τ.1 := by
    ext e
    change conj (psiL P τ m (star' P (algebraMap E (Fld P) e))) = τ.1 e
    rw [star'_algebraMap, psiL_algebraMap, hCM.2.2.2 τ.1 e]
    simp
  have hα : φ (alpha P) = (conj (cxRoots τ.1 P m))⁻¹ := by
    change conj (psiL P τ m (star' P (alpha P))) = _
    rw [star'_alpha, map_inv₀, psiL_alpha, map_inv₀]
  have h0 := congrArg φ (eval_alpha P)
  rw [hom_eval₂, hE, hα, map_zero, ← eval_map, cxRoots_spec, eval_prod, Finset.prod_eq_zero_iff] at h0
  obtain ⟨j, -, hj⟩ := h0
  refine ⟨j, ?_⟩
  rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hj
  exact hj.symm

end GlobalTheory.TrEll.RealTorus

theorem GlobalTheory.TrEll.realTorus_norm_cxRoots : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), Function.Bijective (PsiAll P τ) → CompactSpace (Tor P w.Completion) → ∀ i, ‖cxRoots τ.1 P i‖ = 1 := by
  intro F E _ _ _ _ _ σ hCM r P w τ hB hK i
  have hw : w.IsReal := by haveI := hCM.1; exact IsTotallyReal.isReal w
  obtain ⟨π, hπ⟩ : ∃ π : Fin r → Fin r, ∀ m, cxRoots τ.1 P (π m) = (conj (cxRoots τ.1 P m))⁻¹ :=
    ⟨fun m => (exists_conjInv_root P τ hCM m).choose, fun m => (exists_conjInv_root P τ hCM m).choose_spec⟩
  have hinv : ∀ m, π (π m) = m := fun m =>
    cxRoots_injective P τ (by rw [hπ, hπ, map_inv₀, Complex.conj_conj, inv_inv])
  have hpsi : ∀ m, (psiL P τ m).comp (star' P : Fld P →+* Fld P) = (starRingEnd ℂ).comp (psiL P τ (π m)) := by
    intro m
    refine AdjoinRoot.ringHom_ext (RingHom.ext fun e => ?_) ?_
    · change psiL P τ m (star' P (algebraMap E (Fld P) e)) = conj (psiL P τ (π m) (algebraMap E (Fld P) e))
      rw [star'_algebraMap, psiL_algebraMap, psiL_algebraMap]
      exact hCM.2.2.2 τ.1 e
    · change psiL P τ m (star' P (alpha P)) = conj (psiL P τ (π m) (alpha P))
      rw [star'_alpha, map_inv₀, psiL_alpha, psiL_alpha, hπ, map_inv₀, Complex.conj_conj]
  have hsig : ∀ m y, Psi P τ m (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion (star' P) y) = conj (Psi P τ (π m) y) := by
    intro m y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a l =>
      change Psi P τ m (a ⊗ₜ[F] star' P l) = _
      rw [Psi_tmul, Psi_tmul, map_mul, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw a,
        Complex.conj_ofReal]
      exact congrArg _ (RingHom.congr_fun (hpsi m) l)
  have h0 : cxRoots τ.1 P i ≠ 0 := by
    rw [← psiL_alpha P τ i]; exact (_root_.map_ne_zero _).2 (alpha_ne_zero P)
  suffices hfix : π i = i by
    have e := hπ i
    rw [hfix] at e
    have h1 : cxRoots τ.1 P i * conj (cxRoots τ.1 P i) = 1 := by
      nth_rw 1 [e]
      exact inv_mul_cancel₀ ((_root_.map_ne_zero _).2 h0)
    rw [Complex.mul_conj, ← Complex.sq_norm] at h1
    have h2 : ‖cxRoots τ.1 P i‖ ^ 2 = 1 := by exact_mod_cast h1
    nlinarith [norm_nonneg (cxRoots τ.1 P i)]

  by_contra hji

  have hcont : Continuous (fun g : Tor P w.Completion => ‖Psi P τ i (g.1.1 0 0)‖) := by
    letI : Algebra w.Completion ℂ := (InfinitePlace.Completion.extensionEmbedding w).toAlgebra
    haveI : ContinuousSMul w.Completion ℂ :=
      continuousSMul_of_algebraMap _ _ (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
    haveI : IsModuleTopology w.Completion (w.Completion ⊗[F] Fld P) := ⟨rfl⟩
    let L : w.Completion ⊗[F] Fld P →ₗ[w.Completion] ℂ :=
      { toFun := Psi P τ i
        map_add' := map_add _
        map_smul' := by
          intro c y
          have : c • y = (c ⊗ₜ[F] (1 : Fld P)) * y := by
            rw [Algebra.smul_def]; rfl
          rw [this, map_mul, Psi_tmul, map_one, mul_one]; rfl }
    have hL : Continuous L := IsModuleTopology.continuous_of_linearMap L
    have hv : Continuous (fun g : Tor P w.Completion => (g.1.1 : Matrix (Fin 1) (Fin 1) (w.Completion ⊗[F] Fld P))) :=
      Units.continuous_val.comp continuous_subtype_val
    exact continuous_norm.comp (hL.comp (hv.matrix_elem 0 0))
  obtain ⟨M, hM⟩ := (isCompact_range hcont).bddAbove
  obtain ⟨j, hj⟩ : ∃ j, π i = j := ⟨_, rfl⟩
  have hji' : j ≠ i := by rw [← hj]; exact hji
  have hπj : π j = i := by rw [← hj]; exact hinv i
  have hne : ∀ m, m ≠ j → π m ≠ i := fun m hm h => hm (by have := hinv m; rw [h, hj] at this; exact this.symm)
  have hne' : ∀ m, m ≠ i → π m ≠ j := fun m hm h => hm (by have := hinv m; rw [h, hπj] at this; exact this.symm)
  set t : ℝ := max M 0 + 1 with ht
  have ht0 : 0 < t := by positivity
  let v : Fin r → ℂ := fun m => if m = i then (t : ℂ) else if m = j then (t : ℂ)⁻¹ else 1
  obtain ⟨y, hy⟩ := hB.2 v
  have hyv : ∀ m, Psi P τ m y = v m := fun m => congrFun hy m
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have hyy : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion (star' P) y * y = 1 := by
    apply hB.1
    funext m
    rw [map_mul, map_one, Pi.mul_apply, PsiAll_apply, PsiAll_apply, hsig, hyv, hyv, Pi.one_apply]
    by_cases hmi : m = i
    · rw [hmi, hj]
      simp [v, hji', htc]
    · by_cases hmj : m = j
      · rw [hmj, hπj]
        simp [v, hji', htc]
      · simp [v, hmi, hmj, hne m hmj, hne' m hmi]
  let u : (w.Completion ⊗[F] Fld P)ˣ := ⟨y, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion (star' P) y, by rw [mul_comm]; exact hyy, hyy⟩
  let g : Tor P w.Completion := ⟨Matrix.GeneralLinearGroup.scalar (Fin 1) u, by
    change Formalism.UG.cT _ _ * _ * _ = _
    ext a b
    simp [Formalism.UG.cT, Matrix.mul_apply, Subsingleton.elim a 0, Subsingleton.elim b 0, JR, inclR, u, ← Algebra.TensorProduct.one_def, hyy]⟩
  have hg : ‖Psi P τ i (g.1.1 0 0)‖ = t := by
    have : g.1.1 0 0 = y := by simp [g, u]
    rw [this, hyv]
    simp [v, abs_of_pos ht0]
  have hle : ‖Psi P τ i (g.1.1 0 0)‖ ≤ M := hM ⟨g, rfl⟩
  rw [hg] at hle
  have : M < t := by rw [ht]; linarith [le_max_left M 0]
  linarith
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusFieldComplexRootsNormEqOneCompactStatement
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll GlobalTheory.TrEll.RealTorus
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusFieldComplexRoots_norm_eq_one_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), Function.Bijective (PsiAll P τ) → CompactSpace (Tor P w.Completion) → ∀ i, ‖cxRoots τ.1 P i‖ = 1 := by
  first | exact @GlobalTheory.TrEll.realTorus_norm_cxRoots | exact GlobalTheory.TrEll.realTorus_norm_cxRoots | (intros; apply GlobalTheory.TrEll.realTorus_norm_cxRoots <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletionTensorAllRootsMapBijectiveCm
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletionTensorAllRootsMapBijectiveCm
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll GlobalTheory.TrEll.RealTorus
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RealTorus

theorem subring_pi_mem_of_const_of_injective {ι : Type} [Fintype ι] [DecidableEq ι] (R : Subring (ι → ℂ))
    (hc : ∀ c : ℂ, (fun _ => c) ∈ R) (a : ι → ℂ) (ha : Function.Injective a) (haR : a ∈ R) (x : ι → ℂ) :
    x ∈ R := by
  have hp : ∀ p : ℂ[X], (fun i => p.eval (a i)) ∈ R := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      have := R.add_mem hp hq
      convert this using 1
      ext i; simp
    | monomial n c =>
      have := R.mul_mem (hc c) (R.pow_mem haR n)
      convert this using 1
      ext i; simp [eval_monomial]
  have := hp (Lagrange.interpolate Finset.univ a x)
  convert this using 1
  ext i
  exact (Lagrange.eval_interpolate_at_node x ha.injOn (Finset.mem_univ i)).symm

theorem exists_extensionEmbedding_eq_ofReal {F : Type} [Field F] [NumberField F] {w : InfinitePlace F}
    (hw : w.IsReal) (t : ℝ) : ∃ a : w.Completion, InfinitePlace.Completion.extensionEmbedding w a = (t : ℂ) := by
  refine ⟨(InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t, ?_⟩
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw,
    ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply]

theorem PsiAll_surjective {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} [_root_.NumberField.IsTotallyComplex E] {r : ℕ} (P : PPol σ r) {w : InfinitePlace F} (hw : w.IsReal)
    (τ : EmbOver E w) : Function.Surjective (PsiAll P τ) := by
  intro x
  have hτ : ¬ ComplexEmbedding.IsReal τ.1 := IsTotallyComplex.complexEmbedding_not_isReal τ.1
  have : ∃ e : E, (τ.1 e).im ≠ 0 := by
    by_contra h
    push_neg at h
    apply hτ
    rw [ComplexEmbedding.isReal_iff]
    ext e
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_eq_iff_im.2 (h e)
  obtain ⟨e, he⟩ := this
  refine subring_pi_mem_of_const_of_injective (PsiAll P τ).range ?_ (cxRoots τ.1 P) (cxRoots_injective P τ) ?_ x
  · intro c
    obtain ⟨a, ha⟩ := exists_extensionEmbedding_eq_ofReal hw (c.re - c.im / (τ.1 e).im * (τ.1 e).re)
    obtain ⟨b, hb⟩ := exists_extensionEmbedding_eq_ofReal hw (c.im / (τ.1 e).im)
    refine ⟨a ⊗ₜ[F] 1 + b ⊗ₜ[F] algebraMap E (Fld P) e, ?_⟩
    ext i : 1
    rw [PsiAll_apply, map_add (f := _), Psi_tmul, Psi_tmul, psiL_algebraMap, map_one, ha, hb, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]; ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul]; field_simp; ring
  · refine ⟨1 ⊗ₜ[F] alpha P, ?_⟩
    ext i : 1
    rw [PsiAll_apply, Psi_tmul, psiL_alpha, map_one, one_mul]

theorem PsiAll_bijective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), Function.Bijective (PsiAll P τ) := by
  intro F E _ _ _ _ _ σ hCM r P w τ
  haveI : IsTotallyReal F := hCM.1
  haveI : IsTotallyComplex E := hCM.2.1
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  have hw : w.IsReal := IsTotallyReal.isReal w
  have hs := PsiAll_surjective P hw τ
  refine ⟨?_, hs⟩
  letI : Algebra w.Completion ℂ := (InfinitePlace.Completion.extensionEmbedding w).toAlgebra
  let f : w.Completion ⊗[F] Fld P →ₗ[w.Completion] (Fin r → ℂ) :=
    { toFun := PsiAll P τ
      map_add' := map_add _
      map_smul' := fun a y => by
        rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply]
        ext i
        rw [Pi.mul_apply, PsiAll_apply, Psi_tmul, map_one, mul_one, Pi.smul_apply, Algebra.smul_def]
        rfl }
  have hk : Module.finrank w.Completion ℂ = 2 := by
    rw [Algebra.finrank_eq_of_equiv_equiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (RingEquiv.refl ℂ) ?_,
      Complex.finrank_real_complex]
    ext x
    exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw x
  haveI : Module.Finite w.Completion ℂ := Module.finite_of_finrank_pos (by omega)
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  haveI : Module.Finite E (Fld P) := (AdjoinRoot.powerBasis P.2.2.1.ne_zero).finite
  haveI : Module.Finite F (Fld P) := Module.Finite.trans E (Fld P)
  have hd : Module.finrank w.Completion (w.Completion ⊗[F] Fld P) = Module.finrank w.Completion (Fin r → ℂ) := by
    rw [Module.finrank_baseChange, ← Module.finrank_mul_finrank F E (Fld P), h2, finrank_Fld,
      Module.finrank_pi_fintype]
    simp [hk, mul_comm]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f) hd).2 hs

end GlobalTheory.TrEll.RealTorus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletionTensorAllRootsMapBijectiveCmStatement
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll GlobalTheory.TrEll.RealTorus
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completionTensorAllRootsMap_bijective_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), Function.Bijective (PsiAll P τ) := by
  first | exact @GlobalTheory.TrEll.RealTorus.PsiAll_bijective | exact GlobalTheory.TrEll.RealTorus.PsiAll_bijective | (intros; apply GlobalTheory.TrEll.RealTorus.PsiAll_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryTorusRealPlaceTensorEqComplexPow
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RealTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}
  (P : PPol σ r) {w : InfinitePlace F} (τ : EmbOver E w)

theorem trace_eq_sum (y : Fld P) : τ.1 (Algebra.trace E (Fld P) y) = ∑ i, psiL P τ i y := by
  letI : Algebra E ℂ := τ.1.toAlgebra
  haveI : Algebra.IsSeparable E (Fld P) := Algebra.IsAlgebraic.isSeparable_of_perfectField

  let emb : Fin r → (Fld P →ₐ[E] ℂ) := fun i =>
    { psiL P τ i with commutes' := fun e => psiL_algebraMap P τ i e }
  have hinj : Function.Injective emb := by
    intro i j h
    apply cxRoots_injective P τ
    have h' := congrArg (fun f : Fld P →ₐ[E] ℂ => f (alpha P)) h
    simpa [emb] using h'
  have hcard : Fintype.card (Fin r) = Fintype.card (Fld P →ₐ[E] ℂ) := by
    rw [Fintype.card_fin, AlgHom.card, finrank_Fld]
  have hbij : Function.Bijective emb :=
    (Fintype.bijective_iff_injective_and_card emb).2 ⟨hinj, hcard⟩
  have htr := trace_eq_sum_embeddings (K := E) (L := Fld P) (E := ℂ) (x := y)
  rw [show τ.1 (Algebra.trace E (Fld P) y) = algebraMap E ℂ (Algebra.trace E (Fld P) y) from rfl, htr]
  exact (Fintype.sum_bijective emb hbij (fun i => psiL P τ i y) (fun g => g y) (fun i => rfl)).symm

theorem psiL_star (hCM : IsCMExt F E σ) (i : Fin r) (hi : ‖cxRoots τ.1 P i‖ = 1) (y : Fld P) :
    psiL P τ i (star' P y) = conj (psiL P τ i y) := by
  have key : ((psiL P τ i).comp (star' P : Fld P →+* Fld P) : AdjoinRoot P.1 →+* ℂ) =
      ((starRingEnd ℂ).comp (psiL P τ i) : AdjoinRoot P.1 →+* ℂ) := by
    apply AdjoinRoot.ringHom_ext
    · ext e
      show psiL P τ i (star' P (algebraMap E (Fld P) e)) = conj (psiL P τ i (algebraMap E (Fld P) e))
      rw [star'_algebraMap, psiL_algebraMap, psiL_algebraMap]
      exact hCM.2.2.2 τ.1 e
    · show psiL P τ i (star' P (alpha P)) = conj (psiL P τ i (alpha P))
      rw [star'_alpha, map_inv₀, psiL_alpha]

      have h1 : cxRoots τ.1 P i * conj (cxRoots τ.1 P i) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hi]
        norm_num
      exact (eq_inv_of_mul_eq_one_right h1).symm
  exact RingHom.congr_fun key y

theorem ext_real (a : w.Completion) (hw : w.IsReal) :
    conj (InfinitePlace.Completion.extensionEmbedding w a) = InfinitePlace.Completion.extensionEmbedding w a := by

  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw a, Complex.conj_ofReal]

end GlobalTheory.TrEll.RealTorus

open GlobalTheory.TrEll.RealTorus in
theorem GlobalTheory.TrEll.realTorus_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), CompactSpace (Tor P w.Completion) → ∃ Ψ : w.Completion ⊗[F] Fld P ≃+* (Fin r → ℂ), (∀ y i, Ψ (sigR w.Completion (star' P) y) i = conj (Ψ y i)) ∧ (∀ e i, Ψ (algebraMap (w.Completion ⊗[F] E) _ e) i = infEmb τ e) ∧ Ψ (1 ⊗ₜ[F] alpha P) = cxRoots τ.1 P ∧ (∀ y, infEmb τ (trBase P w.Completion y) = ∑ i, Ψ y i) ∧ Function.Injective (cxRoots τ.1 P) ∧ ∀ i, ‖cxRoots τ.1 P i‖ = 1 := by
  intro F E _ _ _ _ _ σ hCM r P w τ hc
  have hbij := GlobalTheory.T.completionTensorAllRootsMap_bijective_cm F E σ hCM r P w τ
  have hnorm := GlobalTheory.T.torusFieldComplexRoots_norm_eq_one_compact F E σ hCM r P w τ hbij hc
  have hw : w.IsReal := hCM.1.isReal w
  refine ⟨RingEquiv.ofBijective (PsiAll P τ) hbij, ?_, ?_, ?_, ?_, cxRoots_injective P τ, hnorm⟩
  · intro y i
    simp only [RingEquiv.ofBijective_apply, PsiAll_apply]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      rw [show sigR w.Completion (star' P) (a ⊗ₜ[F] y) = a ⊗ₜ[F] star' P y from rfl]
      rw [Psi_tmul, Psi_tmul, psiL_star P τ hCM i (hnorm i), map_mul, ext_real a hw]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · intro e i
    simp only [RingEquiv.ofBijective_apply, PsiAll_apply]
    induction e using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [show algebraMap (w.Completion ⊗[F] E) (w.Completion ⊗[F] Fld P) (a ⊗ₜ[F] e) =
        a ⊗ₜ[F] algebraMap E (Fld P) e from rfl]
      rw [Psi_tmul, infEmb_tmul, psiL_algebraMap]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · funext i
    simp only [RingEquiv.ofBijective_apply, PsiAll_apply, Psi_tmul, map_one, psiL_alpha, one_mul]
  · intro y
    simp only [RingEquiv.ofBijective_apply, PsiAll_apply]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      rw [show trBase P w.Completion (a ⊗ₜ[F] y) = a ⊗ₜ[F] Algebra.trace E (Fld P) y from rfl]
      rw [infEmb_tmul, trace_eq_sum P τ y, Finset.mul_sum]
      simp only [Psi_tmul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy, Finset.sum_add_distrib]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryTorusRealPlaceTensorEqComplexPowStatement
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_unitaryTorus_real_place_tensor_eq_complex_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), CompactSpace (Tor P w.Completion) → ∃ Ψ : w.Completion ⊗[F] Fld P ≃+* (Fin r → ℂ), (∀ y i, Ψ (sigR w.Completion (star' P) y) i = conj (Ψ y i)) ∧ (∀ e i, Ψ (algebraMap (w.Completion ⊗[F] E) _ e) i = infEmb τ e) ∧ Ψ (1 ⊗ₜ[F] alpha P) = cxRoots τ.1 P ∧ (∀ y, infEmb τ (trBase P w.Completion y) = ∑ i, Ψ y i) ∧ Function.Injective (cxRoots τ.1 P) ∧ ∀ i, ‖cxRoots τ.1 P i‖ = 1 := by
  first | exact @GlobalTheory.TrEll.realTorus_split | exact GlobalTheory.TrEll.realTorus_split | (intros; apply GlobalTheory.TrEll.realTorus_split <;> assumption)
end

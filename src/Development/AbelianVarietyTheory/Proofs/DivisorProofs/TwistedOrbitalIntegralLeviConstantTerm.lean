module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralParabolicUnfoldLevi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimFieldBaseChangeLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUpperParabolicMulIntegralGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUpperParabolicMulIntegralGL
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

open ValuativeRel

theorem mem_integer_iff_mem_Ov {E : Type} [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) :
    x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ Ov E w := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _)
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

theorem integralGL_le_KGL {E : Type} [Field E] [NumberField E] (w : Pl E) (n : ℕ) :
    GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) n ≤ GlobalTheory.LFun.KGL w (n := n) := by
  intro g hg
  obtain ⟨h1, h2⟩ := (GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff _ n).1 hg
  let A : Matrix (Fin n) (Fin n) (Ov E w) :=
    Matrix.of fun i j => ⟨g i j, (mem_integer_iff_mem_Ov w _).1 (h1 i j)⟩
  let B : Matrix (Fin n) (Fin n) (Ov E w) :=
    Matrix.of fun i j => ⟨(g⁻¹ : GL (Fin n) (w.adicCompletion E)) i j, (mem_integer_iff_mem_Ov w _).1 (h2 i j)⟩
  have hinj : Function.Injective (RingHom.mapMatrix (m := Fin n) (Ov E w).subtype) :=
    fun M N h => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
  have hA : RingHom.mapMatrix (Ov E w).subtype A = (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := rfl
  have hB : RingHom.mapMatrix (Ov E w).subtype B =
      ((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := rfl
  have hAB : A * B = 1 := hinj (by rw [map_mul, map_one, hA, hB, Units.mul_inv])
  have hBA : B * A = 1 := hinj (by rw [map_mul, map_one, hA, hB, Units.inv_mul])
  exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

theorem exists_parabolic_mul_maximalCompact : ∀ (E : Type) [Field E] [NumberField E] (a n : ℕ) (w : Pl E) (g : GLw n w),
    ∃ p ∈ GlobalTheory.LeviDesc.parP a n w, ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), g = p * k := by
  intro E _ _ a n w g
  have hβ : Monotone fun i : Fin n => decide (a ≤ (i : ℕ)) := by
    intro i j hij
    by_cases h : a ≤ (i : ℕ)
    · have : a ≤ (j : ℕ) := h.trans (Fin.le_iff_val_le_val.1 hij)
      simp [h, this]
    · simp [h]
  obtain ⟨p, hp, k, hk, rfl⟩ :=
    GroundTheory.Automorphic.Iwasawa.exists_blockUpper_mul_integralGL (w.adicCompletion E) n hβ g
  exact ⟨p, hp, k, integralGL_le_KGL w n hk, rfl⟩

end GlobalTheory.LeviDesc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUpperParabolicMulIntegralGLStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockUpperParabolic_mul_integralGL : ∀ (E : Type) [Field E] [NumberField E] (a n : ℕ) (w : Pl E) (g : GLw n w), ∃ p ∈ GlobalTheory.LeviDesc.parP a n w, ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), g = p * k := by
  first | exact @GlobalTheory.LeviDesc.exists_parabolic_mul_maximalCompact | exact GlobalTheory.LeviDesc.exists_parabolic_mul_maximalCompact | (intros; apply GlobalTheory.LeviDesc.exists_parabolic_mul_maximalCompact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTwistedSylvesterSqMulDetPowEqResultantSq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTwistedSylvesterSqMulDetPowEqResultantSq
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

theorem sign_sq_eq_one_of_pow {k : Type} [Field k] (n : ℕ) : ((-1 : k) ^ n) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

theorem det_adL_sq_mul_det_pow : ∀ (k : Type) [Field k] (a b : ℕ) (A : GL (Fin a) k)
    (B : Matrix (Fin b) (Fin b) k),
    LinearMap.det (GlobalTheory.LeviDesc.adL A B) ^ 2 * A.val.det ^ (2 * b)
      = resultant A.val.charpoly B.charpoly ^ 2 := by
  intro k _ a b A B
  let e : Matrix (Fin a) (Fin b) k ≃ₗ[k] ((Fin b → k) →ₗ[k] (Fin a → k)) := Matrix.toLin'
  let F : ((Fin b → k) →ₗ[k] (Fin a → k)) →ₗ[k] ((Fin b → k) →ₗ[k] (Fin a → k)) :=
    LinearMap.llcomp k (Fin b → k) (Fin a → k) (Fin a → k) (Matrix.toLin' A.val)
  let G : ((Fin b → k) →ₗ[k] (Fin a → k)) →ₗ[k] ((Fin b → k) →ₗ[k] (Fin a → k)) :=
    LinearMap.lcomp k (Fin a → k) (Matrix.toLin' B)
  have hcomp : F ∘ₗ ((e : _ →ₗ[k] _) ∘ₗ GlobalTheory.LeviDesc.adL A B ∘ₗ (e.symm : _ →ₗ[k] _)) = F - G := by
    apply LinearMap.ext
    intro ψ
    obtain ⟨X, rfl⟩ := e.surjective ψ
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.sub_apply, F, G, e, LinearMap.llcomp_apply, LinearMap.lcomp_apply,
      GlobalTheory.LeviDesc.adL, LinearMap.coe_mk, AddHom.coe_mk]
    change Matrix.toLin' A.val ∘ₗ Matrix.toLin' (X - (A⁻¹ : GL (Fin a) k).val * X * B)
      = Matrix.toLin' A.val ∘ₗ Matrix.toLin' X - Matrix.toLin' X ∘ₗ Matrix.toLin' B
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← map_sub]
    congr 1
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul]
  have h1 := congrArg LinearMap.det hcomp
  rw [LinearMap.det_comp, LinearMap.det_conj, GlobalTheory.DetAdResultant.det_ad_eq_resultant,
    Matrix.charpoly_toLin', Matrix.charpoly_toLin'] at h1
  have hz : (0 : (Fin b → k) →ₗ[k] (Fin b → k)).charpoly = X ^ b := by
    rw [← (Matrix.toLin' : Matrix (Fin b) (Fin b) k ≃ₗ[k] _).map_zero, Matrix.charpoly_toLin',
      Matrix.charpoly_zero, Fintype.card_fin]
  have hF0 : F - LinearMap.lcomp k (Fin a → k) (0 : (Fin b → k) →ₗ[k] (Fin b → k)) = F := by
    apply LinearMap.ext
    intro ψ
    apply LinearMap.ext
    intro v
    simp [F]
  have h0 : LinearMap.det F = (-1) ^ (a * b) * A.val.charpoly.coeff 0 ^ b := by
    have h := GlobalTheory.DetAdResultant.det_ad_eq_resultant k (Fin a → k) (Fin b → k) (Matrix.toLin' A.val) 0
    rw [hF0, Matrix.charpoly_toLin', hz] at h
    rw [h, natDegree_X_pow, resultant_X_pow_right _ _ _ le_rfl, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  rw [← h1, h0, pow_mul, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, mul_pow ((-1 : k) ^ a),
    sign_sq_eq_one_of_pow, one_mul]
  have hs := sign_sq_eq_one_of_pow (k := k) (a * b)
  linear_combination (-(LinearMap.det (GlobalTheory.LeviDesc.adL A B) ^ 2 * (A.val.charpoly.coeff 0 ^ b) ^ 2)) * hs

end GlobalTheory.LeviDesc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTwistedSylvesterSqMulDetPowEqResultantSqStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_twistedSylvester_sq_mul_det_pow_eq_resultant_sq : ∀ (k : Type) [Field k] (a b : ℕ) (A : GL (Fin a) k) (B : Matrix (Fin b) (Fin b) k), LinearMap.det (GlobalTheory.LeviDesc.adL A B) ^ 2 * A.val.det ^ (2 * b) = resultant A.val.charpoly B.charpoly ^ 2 := by
  first | exact @GlobalTheory.LeviDesc.det_adL_sq_mul_det_pow | exact GlobalTheory.LeviDesc.det_adL_sq_mul_det_pow | (intros; apply GlobalTheory.LeviDesc.det_adL_sq_mul_det_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResultantNeZeroOfSeparableMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResultantNeZeroOfSeparableMul
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem resultant_ne_zero_of_separable_mul :
    ∀ (k : Type) [Field k] (P Q : k[X]), P.Monic → Q.Monic → (P * Q).Separable →
      resultant P Q ≠ 0 := by
  intro k _ P Q _ _ h
  exact Polynomial.resultant_ne_zero P Q h.isCoprime

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResultantNeZeroOfSeparableMulStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.resultant_ne_zero_of_monic_of_separable_mul : ∀ (k : Type) [Field k] (P Q : k[X]), P.Monic → Q.Monic → (P * Q).Separable → resultant P Q ≠ 0 := by
  first | exact @GlobalTheory.resultant_ne_zero_of_separable_mul | exact GlobalTheory.resultant_ne_zero_of_separable_mul | (intros; apply GlobalTheory.resultant_ne_zero_of_separable_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralLeviConstantTerm
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

theorem absHalf_mul : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (x y : w.adicCompletion E), x ≠ 0 → y ≠ 0 → absHalf w (x * y) = absHalf w x * absHalf w y := by
  intro E _ _ w x y hx hy
  have hq : (0 : ℝ) < (qV E w : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero w)
  have ho : Formalism.UG.ordL (x * y) = Formalism.UG.ordL x + Formalism.UG.ordL y := by
    unfold Formalism.UG.ordL
    have h1 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    have h2 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
    have h3 : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
    rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right h3]
    have : WithZero.unzero h3 = WithZero.unzero h1 * WithZero.unzero h2 := by
      apply WithZero.coe_injective
      simp [map_mul]
    rw [this, toAdd_mul]
    ring
  unfold absHalf
  rw [ho, neg_add, zpow_add₀ hq.ne', Real.sqrt_mul (zpow_pos hq _).le]
  push_cast
  ring

theorem isClosed_parP : ∀ (E : Type) [Field E] [NumberField E] (a n : ℕ) (w : Pl E), IsClosed (GlobalTheory.LeviDesc.parP a n w : Set (GLw n w)) := by
  intro E _ _ a n w
  have : (parP a n w : Set (GLw n w)) = ⋂ i : Fin n, ⋂ j : Fin n,
      {g : GLw n w | decide (a ≤ (j : ℕ)) < decide (a ≤ (i : ℕ)) → (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j = 0} := by
    ext g
    simp only [Set.mem_iInter]
    rfl
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  by_cases hij : decide (a ≤ (j : ℕ)) < decide (a ≤ (i : ℕ))
  · simp only [hij, true_implies]
    exact isClosed_eq (Continuous.matrix_elem (Units.continuous_val (M := Matrix (Fin n) (Fin n) (w.adicCompletion E))) i j) continuous_const
  · simp only [hij, false_implies, Set.ofPred_true]
    exact isClosed_univ

theorem blk_mem_parP : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), blk h w m X ∈ GlobalTheory.LeviDesc.parP a n w := by
  intro E _ _ n a b h w m X
  unfold blk
  simp only []
  split_ifs with hM
  · change (hM.unit : Matrix (Fin n) (Fin n) (w.adicCompletion E)).BlockTriangular _
    rw [IsUnit.unit_spec]
    intro i j hij
    have hj : (j : ℕ) < a := by
      by_contra hc
      push_neg at hc
      simp only [hc, decide_true] at hij
      exact (by decide : ∀ c : Bool, ¬ (true < c)) _ hij
    have hi : a ≤ (i : ℕ) := by
      by_contra hc
      push_neg at hc
      simp only [not_le.2 hc, decide_false] at hij
      exact (by decide : ∀ c : Bool, ¬ (c < false)) _ hij
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases hi' : (finSumFinEquiv.trans (finCongr h)).symm i with i' | i'
    · exfalso
      have := congrArg (finSumFinEquiv.trans (finCongr h)) hi'
      rw [Equiv.apply_symm_apply] at this
      have hv := congrArg Fin.val this
      simp at hv
      omega
    · rcases hj' : (finSumFinEquiv.trans (finCongr h)).symm j with j' | j'
      · simp
      · exfalso
        have := congrArg (finSumFinEquiv.trans (finCongr h)) hj'
        rw [Equiv.apply_symm_apply] at this
        have hv := congrArg Fin.val this
        simp at hv
        omega
  · exact (parP a n w).one_mem

theorem avg_const_mul {H : Type} [Group H] (u : H → ℂ) {c : ℂ} (hc : c ≠ 0) :
    avg (fun x => c * u x) = c * avg u := by
  have hs : rStab (fun x => c * u x) = rStab u := by
    ext k
    change (∀ x, c * u (x * k) = c * u x) ↔ (∀ x, u (x * k) = u x)
    exact ⟨fun h x => mul_left_cancel₀ hc (h x), fun h x => by rw [h x]⟩
  unfold avg
  rw [hs, ← mul_finsum]
  ring

theorem absHalf_ne_zero' {E : Type} [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) : absHalf w x ≠ 0 := by
  unfold absHalf
  have hq : (0 : ℝ) < (qV E w : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (GlobalTheory.LFun.qV_ne_zero w)
  exact_mod_cast (Real.sqrt_pos.2 (zpow_pos hq _)).ne'

theorem ct_eq_mul_orbN : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw (n - a) w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ct (Nat.add_sub_cancel' ha) w f m = absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) * GlobalTheory.LeviDesc.orbN (Nat.add_sub_cancel' ha) w f m := by
  intro E _ _ _ n a ha w f hf m hsep
  obtain ⟨hU, hcs⟩ := GlobalTheory.T.conjAverage_unipotent_locallyConstant_compactSupport E n a (n - a) (Nat.add_sub_cancel' ha) w f hf m
  have hR := GlobalTheory.T.resultant_ne_zero_of_monic_of_separable_mul (w.adicCompletion E) _ _ (Matrix.charpoly_monic _) (Matrix.charpoly_monic _) hsep
  have hD := GlobalTheory.T.det_twistedSylvester_sq_mul_det_pow_eq_resultant_sq (w.adicCompletion E) a (n - a) m.1 m.2.val
  have hd1 : m.1.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).ne_zero
  have hd2 : m.2.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit).ne_zero
  have hL : LinearMap.det (adL m.1 m.2.val) ≠ 0 := by
    intro h0
    rw [h0] at hD
    apply hR
    have : resultant m.1.val.charpoly m.2.val.charpoly ^ 2 = 0 := by rw [← hD]; ring
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have hJ := GlobalTheory.T.normalisedMatrixIntegral_comp_linearEquiv_det E w a (n - a) (adL m.1 m.2.val)
    (fun X => cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk (Nat.add_sub_cancel' ha) w m X)) hL hU hcs
  have hI : orbN (Nat.add_sub_cancel' ha) w f m = hint (intMat a (n - a) w)
      (fun X => cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk (Nat.add_sub_cancel' ha) w m (adL m.1 m.2.val (Multiplicative.toAdd X)))) := by
    unfold orbN
    simp only [GlobalTheory.T.unipotent_conj_levi_eq_blockUpperTwistedSylvester]
  rw [hI, hJ]
  change absHalf w (m.1.val.det ^ (n - a) / m.2.val.det ^ a) * hint (intMat a (n - a) w)
      (fun X => cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk (Nat.add_sub_cancel' ha) w m (Multiplicative.toAdd X))) = _
  have hq : resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a) =
      LinearMap.det (adL m.1 m.2.val) * (LinearMap.det (adL m.1 m.2.val) * (m.1.val.det ^ (n - a) / m.2.val.det ^ a)) := by
    rw [← hD]
    field_simp
    ring
  have hq0 : m.1.val.det ^ (n - a) / m.2.val.det ^ a ≠ 0 := div_ne_zero (pow_ne_zero _ hd1) (pow_ne_zero _ hd2)
  rw [hq, absHalf_mul E w _ _ hL (mul_ne_zero hL hq0), absHalf_mul E w _ _ hL hq0]
  have h0 := absHalf_ne_zero' w (LinearMap.det (adL m.1 m.2.val))
  field_simp

theorem conjP_charpoly {k : Type} [Field k] {a : ℕ} (g m : GL (Fin a) k) : (g⁻¹ * m * g).val.charpoly = m.val.charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' g m.val

theorem conjP_det {k : Type} [Field k] {a : ℕ} (g m : GL (Fin a) k) : (g⁻¹ * m * g).val.det = m.val.det := by
  rw [Units.val_mul, Units.val_mul]
  exact Matrix.det_units_conj' g m.val

theorem orbInt_descent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ), IsHecke (GlobalTheory.LFun.KGL w (n := n)) f ∨ (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw (n - a) w, (m.1.val.charpoly * m.2.val.charpoly).Separable → twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := (n - a)))) m (ct (Nat.add_sub_cancel' ha) w f) = absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) * twOrb (MonoidHom.id _) (GlobalTheory.LFun.KGL w (n := n)) (blk (Nat.add_sub_cancel' ha) w m 0) f := by
  intro E _ _ _ n a ha w f hf m hsep
  have hf' : ∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f := by
    rcases hf with h | h
    · exact ⟨_, (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1, h⟩
    · exact h
  have hc0 := absHalf_ne_zero' w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a))
  have h1 : twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := (n - a)))) m (ct (Nat.add_sub_cancel' ha) w f) =
      twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := (n - a)))) m
        (fun m' => absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) *
          orbN (Nat.add_sub_cancel' ha) w f m') := by
    unfold twOrb
    refine finsum_congr fun q => ?_
    congr 2
    funext k
    have e1 : ∀ g : GLw a w × GLw (n - a) w, ((g⁻¹ * m * (MonoidHom.id _) g).1).val.charpoly = m.1.val.charpoly :=
      fun g => conjP_charpoly g.1 m.1
    have e2 : ∀ g : GLw a w × GLw (n - a) w, ((g⁻¹ * m * (MonoidHom.id _) g).2).val.charpoly = m.2.val.charpoly :=
      fun g => conjP_charpoly g.2 m.2
    have d1 : ∀ g : GLw a w × GLw (n - a) w, ((g⁻¹ * m * (MonoidHom.id _) g).1).val.det = m.1.val.det :=
      fun g => conjP_det g.1 m.1
    have d2 : ∀ g : GLw a w × GLw (n - a) w, ((g⁻¹ * m * (MonoidHom.id _) g).2).val.det = m.2.val.det :=
      fun g => conjP_det g.2 m.2
    set g := Quotient.out q * (k : GLw a w × GLw (n - a) w)
    rw [ct_eq_mul_orbN E n a ha w f hf' _ (by rw [e1, e2]; exact hsep), e1, e2, d1, d2]
  have h2 : twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := (n - a)))) m
        (fun m' => absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) *
          orbN (Nat.add_sub_cancel' ha) w f m') =
      absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) *
        twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := (n - a)))) m (orbN (Nat.add_sub_cancel' ha) w f) := by
    unfold twOrb
    rw [mul_finsum]
    refine finsum_congr fun q => ?_
    rw [avg_const_mul _ hc0]
    ring
  have hγ := blk_mem_parP E n a (n - a) (Nat.add_sub_cancel' ha) w m 0
  have hKG := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  rw [h1, h2, ← GlobalTheory.T.twistedOrbitalIntegral_parabolic_unfold_levi E n a ha w f hf' m hsep hγ,
    ← GlobalTheory.T.orbitalIntegral_eq_closedSubgroup_conjAverage (GLw n w) (GlobalTheory.LFun.KGL w (n := n)) (parP a n w) hKG.1 hKG.2 (isClosed_parP E a n w) (GlobalTheory.T.exists_blockUpperParabolic_mul_integralGL E a n w) _ hγ
      (GlobalTheory.T.twisted_centralizer_block_le_parabolic E n a (n - a) _ w m hsep) f hf']

end GlobalTheory.LeviDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralLeviConstantTermStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_orbital_integral_levi_constant_term : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ), IsHecke (GlobalTheory.LFun.KGL w (n := n)) f ∨ (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw (n - a) w, (m.1.val.charpoly * m.2.val.charpoly).Separable → twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := (n - a)))) m (ct (Nat.add_sub_cancel' ha) w f) = absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) * twOrb (MonoidHom.id _) (GlobalTheory.LFun.KGL w (n := n)) (blk (Nat.add_sub_cancel' ha) w m 0) f := by
  first | exact @GlobalTheory.LeviDesc.orbInt_descent | exact GlobalTheory.LeviDesc.orbInt_descent | (intros; apply GlobalTheory.LeviDesc.orbInt_descent <;> assumption)
end

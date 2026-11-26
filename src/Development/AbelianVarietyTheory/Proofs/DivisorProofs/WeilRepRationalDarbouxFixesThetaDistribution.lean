module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumDoubledWeilFixedDiagonalStabilizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjSkewDetUnitOfAvoidanceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCornerUnitOfRightInverseStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumDoubledWeilAntidiagonalInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumDoubledWeilAntidiagonalInvariant
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.ThetaOppParab

variable {κ : Type}

def negSnd {M : Type} [Neg M] (x : κ ⊕ κ → M) : κ ⊕ κ → M := Sum.elim (fun i => x (Sum.inl i)) (fun i => -x (Sum.inr i))

theorem negSnd_negSnd {M : Type} [InvolutiveNeg M] (x : κ ⊕ κ → M) : negSnd (negSnd x) = x :=
  funext fun i => by cases i <;> simp [negSnd]

theorem negSnd_add {M : Type} [AddCommGroup M] (x y : κ ⊕ κ → M) : negSnd (x + y) = negSnd x + negSnd y :=
  funext fun i => by cases i <;> simp [negSnd, add_comm]

theorem negSnd_dot {R : Type} [CommRing R] [Fintype κ] (x y : κ ⊕ κ → R) : negSnd x ⬝ᵥ y = x ⬝ᵥ negSnd y := by
  simp [negSnd, dotProduct, Fintype.sum_sum_type]

theorem negSnd_dot_negSnd {R : Type} [CommRing R] [Fintype κ] (x y : κ ⊕ κ → R) : negSnd x ⬝ᵥ negSnd y = x ⬝ᵥ y := by
  simp [negSnd, dotProduct, Fintype.sum_sum_type]

def negSndL (R M : Type) [Semiring R] [AddCommGroup M] [Module R M] : (κ ⊕ κ → M) ≃ₗ[R] (κ ⊕ κ → M) where
  toFun := negSnd
  invFun := negSnd
  map_add' := negSnd_add
  map_smul' c x := funext fun i => by cases i <;> simp [negSnd, Pi.smul_apply, smul_neg]
  left_inv := negSnd_negSnd
  right_inv := negSnd_negSnd

def negSndH (M : Type) [TopologicalSpace M] [AddGroup M] [ContinuousNeg M] : (κ ⊕ κ → M) ≃ₜ (κ ⊕ κ → M) where
  toFun := negSnd
  invFun := negSnd
  left_inv := negSnd_negSnd
  right_inv := negSnd_negSnd
  continuous_toFun := continuous_pi fun i => by
    cases i
    · exact continuous_apply _
    · exact (continuous_apply _).neg
  continuous_invFun := continuous_pi fun i => by
    cases i
    · exact continuous_apply _
    · exact (continuous_apply _).neg

theorem map_neg_one_mat {n R S G : Type} [DecidableEq n] [Ring R] [Ring S] [FunLike G R S] [RingHomClass G R S]
    (f : G) : (-1 : Matrix n n R).map f = -1 := by
  rw [Matrix.map_neg _ (map_neg f), Matrix.map_one _ (map_zero f) (map_one f)]

variable (F : Type) [Field F] [NumberField F]
open scoped Classical

def negOp : Module.End ℂ ((κ ⊕ κ → AF F) → ℂ) := LinearMap.funLeft ℂ ℂ negSnd

theorem negOp_apply (φ : (κ ⊕ κ → AF F) → ℂ) (x) : negOp F φ x = φ (negSnd x) := rfl

theorem negOp_negOp (φ : (κ ⊕ κ → AF F) → ℂ) : negOp F (negOp F φ) = φ :=
  funext fun x => by simp [negOp_apply, negSnd_negSnd]

theorem negOp_schr [Fintype κ] (ψ : AddChar (AF F) ℂ) (w : (κ ⊕ κ → AF F) × (κ ⊕ κ → AF F)) (φ : (κ ⊕ κ → AF F) → ℂ) :
    negOp F (schr ψ w φ) = schr ψ (negSnd w.1, negSnd w.2) (negOp F φ) := by
  funext x
  simp only [negOp_apply, schr, negSnd_dot, negSnd_add, negSnd_negSnd]

theorem pureA_negSnd [Fintype κ] (f : (κ ⊕ κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    negOp F (pureA F f g) = pureA F (f ∘ negSnd) (g ∘ negSnd) := by
  funext x
  simp only [negOp_apply, pureA, Function.comp_apply]
  congr 2
  · funext i
    cases i with
    | inl i => rfl
    | inr i => exact map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x (Sum.inr i)).1
  · funext i
    cases i with
    | inl i => rfl
    | inr i => rfl

theorem comp_negOp_mem_adm [Fintype κ] {l : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm (κ ⊕ κ)) :
    l ∘ₗ negOp F ∈ (adeleClass F).adm (κ ⊕ κ) := by
  intro g hg
  let A : (κ ⊕ κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ ⊕ κ → mixedEmbedding.mixedSpace F) :=
    (negSndL ℝ (mixedEmbedding.mixedSpace F)).toContinuousLinearEquiv
  let B := negSndH (κ := κ) (FiniteAdeleRing (𝓞 F) F)
  obtain ⟨T, hT⟩ := hl (g ∘ B) ⟨hg.1.comp_continuous B.continuous, hg.2.comp_homeomorph B⟩
  refine ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A), fun f => ?_⟩
  rw [LinearMap.comp_apply, pureA_negSnd, ContinuousLinearMap.comp_apply, ← hT]
  rfl

theorem thetaSum_negOp [Fintype κ] (φ : (κ ⊕ κ → AF F) → ℂ) : thetaSum F (negOp F φ) = thetaSum F φ := by
  unfold thetaSum
  have e := Equiv.tsum_eq (negSndL (κ := κ) F F).toEquiv (fun ξ : κ ⊕ κ → F => φ fun i => algebraMap F (AF F) (ξ i))
  refine Eq.trans (tsum_congr fun ξ => ?_) e
  show φ (negSnd _) = φ (fun i => algebraMap F (AF F) (negSnd ξ i))
  congr 1
  funext i
  cases i <;> simp [negSnd]


open scoped Classical in
theorem thetaSum_omd_antidiag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (κ : Type) [Fintype κ], Fintype.card κ = a * b → ∀ (d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ), (∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F, d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ)), IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd → ∀ (χ : Chr F E), IsHecke F E χ → ∀ (omd : UG (cA σ) (dbl (incM F JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)), IsSplitting (adeleClass F) ψ dd (actB (cA σ)) omd → SiegelRule (cA σ) (adeleClass F) ψ (-1) (incM F JA) (dbl (incM F JB)) dd χ (diagCols (Fin b)) omd → ∀ (q : UG (cA σ) (dbl (incM F JB))) (q₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E), ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F q₀ → ∀ (s : GL (Fin b) (AE F E)), ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) = Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) * (s : Matrix (Fin b) (Fin b) (AE F E)) → ∀ φ ∈ schA F (κ ⊕ κ), thetaSum F (omd q φ) = thetaSum F φ := by
  intro F E _ _ _ _ _ σ hσ ψ hψ a b JA JB κ _ hcard d hd dd hdd χ hχ omd hS hR q q₀ hq s hqs φ hφ
  let M₀' : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E := Matrix.fromBlocks 1 0 0 (-1)
  let M₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E) := Matrix.fromBlocks 1 0 0 (-1)
  have hM₀sq : M₀ * M₀ = 1 := by simp [M₀, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  have hM₀' : incM F M₀' = M₀ := by
    simp only [M₀, M₀', incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _),
      map_neg_one_mat, Matrix.map_one _ (map_zero _) (map_one _)]
  let w₀g : GL (Fin b ⊕ Fin b) (AE F E) := ⟨M₀, M₀, hM₀sq, hM₀sq⟩
  have hw₀mem : w₀g ∈ UG (cA σ) (dbl (incM F JB)) := by
    show M₀ᵀ * dbl (incM F JB) * M₀.map (cA σ) = dbl (incM F JB)
    simp only [M₀, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _),
      map_neg_one_mat, Matrix.map_one _ (map_zero _) (map_one _)]
    simp [Matrix.fromBlocks_multiply]
  let w₀ : UG (cA σ) (dbl (incM F JB)) := ⟨w₀g, hw₀mem⟩
  have hw₀v : ((w₀ : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = M₀ := rfl
  have hw₀w₀ : w₀ * w₀ = 1 := Subtype.ext (Units.ext hM₀sq)
  let p : UG (cA σ) (dbl (incM F JB)) := w₀ * q * w₀
  have hpv : ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) =
      M₀ * ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * M₀ := rfl
  have hp₀ : ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) =
      incM F (M₀' * q₀ * M₀') := by
    rw [hpv, hq, ← hM₀']
    simp only [incM, Matrix.map_mul]
  have hMd : M₀ * (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) =
      (Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) := by
    simp only [M₀, diagCols]
    rw [Matrix.fromBlocks_mul_fromRows]; simp
  have hMa : M₀ * (Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) =
      (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) := by
    simp only [M₀, diagCols]
    rw [Matrix.fromBlocks_mul_fromRows]; simp
  have hqs' : ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) *
      (Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) =
      (Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) *
        (s : Matrix (Fin b) (Fin b) (AE F E)) := hqs
  have hps : ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) *
      (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) =
      (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)) * (s : Matrix (Fin b) (Fin b) (AE F E)) := by
    rw [hpv]
    simp only [Matrix.mul_assoc]
    rw [hMd, hqs', ← Matrix.mul_assoc, hMa]
  have hsieg := GlobalTheory.T.thetaSum_doubledWeil_fixed_diagonalStabilizer F E σ hσ ψ hψ a b JA JB κ hcard d hd dd hdd χ hχ omd hS hR p (M₀' * q₀ * M₀') hp₀ s hps
  have hrel : ∀ v, dd.e (actB (cA σ) w₀ v) = (negSnd (dd.e v).1, negSnd (dd.e v).2) := by
    intro v
    have hv : actB (cA σ) w₀ v = Matrix.fromCols v.toCols₁ (-v.toCols₂) := by
      rw [actB, hw₀v]
      conv_lhs => rw [← Matrix.fromCols_toCols v]
      rw [Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]
      simp
    conv_rhs => rw [← Matrix.fromCols_toCols v]
    rw [hv, hdd, hdd, map_neg]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> cases i <;> simp [negSnd]
  obtain ⟨c, hc⟩ := GlobalTheory.WeilSchUnique.scalar_of_commute ψ hψ (negOp F * omd w₀)
    (fun l hl => by
      rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
      exact hS.adm w₀ _ (comp_negOp_mem_adm F hl))
    (fun w φ hφ => by
      obtain ⟨v, rfl⟩ := dd.e.surjective w
      have e1 : schr ψ (dd.e v) = dd.rho ψ v := rfl
      rw [e1, mul_apply_eq_comp, mul_apply_eq_comp, hS.impl w₀ v φ hφ, Darboux.rho, hrel, negOp_schr]
      simp only [negSnd_negSnd]
      rfl)
  have hsm : ∀ (c : ℂ) (f : (κ ⊕ κ → AF F) → ℂ), thetaSum F (c • f) = c * thetaSum F f := fun c f => by
    simp only [thetaSum, Pi.smul_apply, smul_eq_mul]
    exact tsum_mul_left
  have hΘw : ∀ X ∈ schA F (κ ⊕ κ), thetaSum F (omd w₀ X) = c * thetaSum F X := fun X hX => by
    have h1 := congrArg (negOp F) (hc X hX)
    rw [mul_apply_eq_comp, negOp_negOp, map_smul] at h1
    rw [h1, hsm, thetaSum_negOp]
  have hq' : q = w₀ * p * w₀ := by
    show q = w₀ * (w₀ * q * w₀) * w₀
    rw [show w₀ * (w₀ * q * w₀) * w₀ = (w₀ * w₀) * q * (w₀ * w₀) by group, hw₀w₀, one_mul, mul_one]
  calc thetaSum F (omd q φ) = thetaSum F (omd w₀ (omd p (omd w₀ φ))) := by
        rw [hq', map_mul, map_mul]; rfl
    _ = c * thetaSum F (omd p (omd w₀ φ)) := hΘw _ (hS.pres _ _ (hS.pres _ _ hφ))
    _ = c * thetaSum F (omd w₀ φ) :=
      congrArg (fun z => c * z) (hsieg (omd w₀ φ) (hS.pres w₀ φ hφ))
    _ = thetaSum F (omd w₀ (omd w₀ φ)) := (hΘw _ (hS.pres _ _ hφ)).symm
    _ = thetaSum F φ := by rw [← mul_apply_eq_comp, ← map_mul, hw₀w₀, map_one, one_apply_eq_self]

end GlobalTheory.ThetaOppParab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumDoubledWeilAntidiagonalInvariantStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicThetaSum_doubledWeil_antidiagonal_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) → ∀ (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (κ : Type) [Fintype κ], Fintype.card κ = a * b → ∀ (d : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ), (∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F, d.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ (dd : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB))) (κ ⊕ κ)), IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) d dd → ∀ (χ : Chr F E), IsHecke F E χ → ∀ (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)), IsSplitting (adeleClass F) ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd → SiegelRule (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) dd χ (diagCols (Fin b)) omd → ∀ (q : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB))) (q₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E), ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = (_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) q₀ → ∀ (s : GL (Fin b) (AE F E)), ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) = Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) * (s : Matrix (Fin b) (Fin b) (AE F E)) → ∀ φ ∈ schA F (κ ⊕ κ), thetaSum F (omd q φ) = thetaSum F φ := by
  first | exact @GlobalTheory.ThetaOppParab.thetaSum_omd_antidiag | exact GlobalTheory.ThetaOppParab.thetaSum_omd_antidiag | (intros; apply GlobalTheory.ThetaOppParab.thetaSum_omd_antidiag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryRationalEqDiagonalFixersProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryRationalEqDiagonalFixersProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.ThetaRatGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 F) (K := F))

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem exists_eval_ne (ψ : Polynomial E) (hψ : ψ ≠ 0) : ∃ t : F, ψ.eval (algebraMap F E t) ≠ 0 := by
  classical
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  have hinf : (Set.range (algebraMap F E)).Infinite := Set.infinite_range_of_injective (algebraMap F E).injective
  obtain ⟨y, ⟨t, rfl⟩, hy⟩ := hinf.exists_notMem_finset ψ.roots.toFinset
  refine ⟨t, fun h => hy ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hψ]
  exact h

theorem hyp1 : ∀ ψ : Polynomial E, (∀ (Ω : Type) [Field Ω] (φ : E →+* Ω), φ 1 = 1 → ψ.map φ ≠ 0) →
    ∃ t : F, IsUnit ((1 : E) * ψ.eval (algebraMap F E t) + (1 - 1)) := by
  intro ψ h
  have hψ : ψ ≠ 0 := by simpa using h E (RingHom.id E) (map_one _)
  obtain ⟨t, ht⟩ := exists_eval_ne (F := F) ψ hψ
  exact ⟨t, by simpa using ht⟩

theorem invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_anti {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ ρ : E, ρ ≠ 0 ∧ σ ρ = -ρ := by
  have hne : σ ≠ AlgHom.id F E := by
    intro hσ
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := h.2.1
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := h.2.2.2 τ x
    rw [hσ] at this
    simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra hc
    push_neg at hc
    exact hne (AlgHom.ext hc)
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, invol h]
  ring

variable (F) in
theorem incM_mul {m n k : Type} [Fintype n] (A : Matrix m n E) (B : Matrix n k E) :
    incM F (A * B) = incM F A * incM F B := Matrix.map_mul

variable (F) in
theorem incM_dbl {β : Type} (J : Matrix β β E) : incM F (dbl J) = dbl (incM F J) := by
  ext i j
  cases i <;> cases j <;> simp [incM, dbl]

theorem incM_map (σ : E →ₐ[F] E) {m n : Type} (A : Matrix m n E) : (incM F A).map (cA σ) = incM F (A.map σ) := by
  ext i j
  simp [incM, cA_inclR]

variable (F) in
theorem incM_transpose {m n : Type} (A : Matrix m n E) : (incM F A)ᵀ = incM F Aᵀ := rfl

variable (F) in
theorem incM_diag {β : Type} [DecidableEq β] :
    incM F (Matrix.fromRows (1 : Matrix β β E) (1 : Matrix β β E)) = Matrix.fromRows (1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) 1 := by
  simp [incM, Matrix.fromRows_map]

variable (F) in
theorem incM_nabla {β : Type} [DecidableEq β] :
    incM F (Matrix.fromRows (1 : Matrix β β E) (-1 : Matrix β β E)) = Matrix.fromRows (1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (-1) := by
  simp [incM, Matrix.fromRows_map, Matrix.map_neg _ (map_neg (inclR (F := F) (E := E) (AF F)))]

theorem incM_inj {m n : Type} {A B : Matrix m n E} (h : incM F A = incM F B) : A = B := by
  ext i j
  exact inclR_inj (congrFun (congrFun h i) j)

def up (σ : E →ₐ[F] E) {b : ℕ} (JB : Matrix (Fin b) (Fin b) E) (p : UG σ (dbl JB)) : UG (cA σ) (dbl (incM F JB)) :=
  ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) p.1, by
    have hp : ((p.1 : Matrix _ _ E))ᵀ * dbl JB * (p.1 : Matrix _ _ E).map σ = dbl JB := p.2
    show (incM F (p.1 : Matrix _ _ E))ᵀ * dbl (incM F JB) * (incM F (p.1 : Matrix _ _ E)).map (cA σ) = dbl (incM F JB)
    rw [incM_map, ← incM_dbl, incM_transpose, ← incM_mul, ← incM_mul, hp]⟩

theorem up_mul (σ : E →ₐ[F] E) {b : ℕ} (JB : Matrix (Fin b) (Fin b) E) (p q : UG σ (dbl JB)) :
    up σ JB (p * q) = up σ JB p * up σ JB q :=
  Subtype.ext (map_mul _ _ _)

theorem down (σ : E →ₐ[F] E) {b : ℕ} (JB : Matrix (Fin b) (Fin b) E) (g : UG (cA σ) (dbl (incM F JB)))
    (g₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E)
    (hg : ((g : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix _ _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F g₀) :
    ∃ g₁ : UG σ (dbl JB), ((g₁ : GL (Fin b ⊕ Fin b) E) : Matrix _ _ E) = g₀ ∧ g = up σ JB g₁ := by
  have hdet : IsUnit g₀.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hu : IsUnit (g.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).det :=
      (Matrix.isUnit_iff_isUnit_det (g.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))).mp (Units.isUnit _)
    have e : (incM F g₀).det = inclR (F := F) (AF F) g₀.det := (RingHom.map_det _ _).symm
    rw [hg, e, h0, map_zero, isUnit_zero_iff] at hu
    exact zero_ne_one (inclR_inj (F := F) (E := E) (by rw [map_zero, map_one]; exact hu))
  have hu : IsUnit g₀ := (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  have hmem : hu.unit ∈ UG σ (dbl JB) := by
    show (hu.unit : Matrix _ _ E)ᵀ * dbl JB * (hu.unit : Matrix _ _ E).map σ = dbl JB
    rw [IsUnit.unit_spec]
    have h2 : ((g : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix _ _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ * dbl (incM F JB) *
        ((g : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix _ _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).map (cA σ) = dbl (incM F JB) := g.2
    rw [hg, incM_map, ← incM_dbl, incM_transpose, ← incM_mul, ← incM_mul] at h2
    exact incM_inj h2
  refine ⟨⟨hu.unit, hmem⟩, IsUnit.unit_spec hu, Subtype.ext (Units.ext ?_)⟩
  rw [hg]
  exact (congrArg (incM F) (IsUnit.unit_spec hu)).symm

end GlobalTheory.ThetaRatGen

namespace GlobalTheory.ThetaRatGen

theorem gen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (b : ℕ) (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ), (∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) → JB.det ≠ 0 → ∀ (g : UG (cA σ) (dbl (incM F JB))) (g₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E), ((g : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F g₀ → ∃ (p q p' : UG (cA σ) (dbl (incM F JB))) (p₀ q₀ p₀' : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) (t s t' : GL (Fin b) (AE F E)), ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F p₀ ∧ ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F q₀ ∧ ((p' : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F p₀' ∧ ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * (t : Matrix (Fin b) (Fin b) (AE F E)) ∧ ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) = Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) * (s : Matrix (Fin b) (Fin b) (AE F E)) ∧ ((p' : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * (t' : Matrix (Fin b) (Fin b) (AE F E)) ∧ g = p * q * p' := by
  intro F E _ _ _ _ _ σ hσ b JB ε hJ hdet g g₀ hg
  haveI : Invertible (2 : E) := invertibleOfNonzero two_ne_zero
  obtain ⟨g₁, -, rfl⟩ := down σ JB g g₀ hg
  set G : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E := (g₁.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) with hG
  set H : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E :=
    ((g₁.1⁻¹ : GL (Fin b ⊕ Fin b) E) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) with hH
  set Nt : Matrix (Fin b) (Fin b ⊕ Fin b) E := Matrix.fromCols 1 (-1) with hNt
  set N : Matrix (Fin b ⊕ Fin b) (Fin b) E := Matrix.fromRows 1 (-1) with hN
  set Dt : Matrix (Fin b) (Fin b ⊕ Fin b) E := Matrix.fromCols 1 1 with hDt
  set Δ : Matrix (Fin b ⊕ Fin b) (Fin b) E := Matrix.fromRows 1 1 with hΔ
  have hGH : G * H = 1 := by rw [hG, hH, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNN : Nt * N = (2 : E) • 1 := by
    rw [hNt, hN, Matrix.fromCols_mul_fromRows]
    simp [two_smul]
  have e2' : Δ * Dt + N * Nt = (2 : E) • 1 := GlobalTheory.BigCell.e2
  have hPQ : (Nt * G * N) * ((4 : E)⁻¹ • (Nt * H * N)) + (Nt * G * Δ) * ((4 : E)⁻¹ • (Dt * H * N)) = 1 := by
    calc _ = (4 : E)⁻¹ • (Nt * G * (Δ * Dt + N * Nt) * H * N) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, smul_add, Matrix.mul_assoc]
          abel
      _ = 1 := by
          rw [e2']
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
          rw [show Nt * G * H * N = Nt * N by rw [Matrix.mul_assoc Nt G H, hGH, Matrix.mul_one], hNN, smul_smul]
          norm_num
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.exists_corner_unit_of_right_inverse' (F := F) (1 : E) (mul_one 1) hyp1 _ _ _ _ hPQ
  obtain ⟨ρ, hρ0, hρ⟩ := exists_anti hσ
  have hJ' : (JB.map (σ : E →+* E))ᵀ = ((ε : ℤ) : E) • JB := by
    ext i j
    simp [hJ]
  obtain ⟨x, hxS, hx⟩ := GlobalTheory.T.exists_conj_skew_det_unit_of_avoidance' (F := F) (σ : E →+* E) (invol hσ) (fun t => σ.commutes t) 1 hyp1 ρ
    (isUnit_iff_ne_zero.mpr hρ0) hρ JB ε hJ' (isUnit_iff_ne_zero.mpr hdet) _ _ x₀ hx₀
  obtain ⟨p, hpΔ, hcorner⟩ := GlobalTheory.T.siegelUnipotent_antidiagonal_corner (R₀ := F) σ JB x hxS
  have hunit : IsUnit (Matrix.fromCols (1 : Matrix (Fin b) (Fin b) E) (-1 : Matrix (Fin b) (Fin b) E) *
      (((g₁ * p : UG σ (dbl JB)) : GL (Fin b ⊕ Fin b) E) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) *
      Matrix.fromRows (1 : Matrix (Fin b) (Fin b) E) (-1 : Matrix (Fin b) (Fin b) E)).det := by
    rw [Subgroup.coe_mul, Units.val_mul, hcorner]
    have hx' : IsUnit (Nt * G * N + Nt * G * Δ * x).det := by simpa using hx
    exact hx'
  obtain ⟨p₀, q₀, t, s, hp₀, hq₀, hpq⟩ := GlobalTheory.BigCell.bigCell_factor F E σ (Fin b) JB (g₁ * p) hunit
  have hg₁ : g₁ = p₀ * q₀ * p⁻¹ := eq_mul_inv_of_mul_eq hpq
  have hpinv : ((p⁻¹ : UG σ (dbl JB)).1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) *
      (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E) = (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E) := by
    have h1 : (p.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) * (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E) =
        (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E) := by
      exact hpΔ.trans (Matrix.mul_one _)
    calc _ = ((p⁻¹ : UG σ (dbl JB)).1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) *
          ((p.1 : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) *
            (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) E)) := by rw [h1]
      _ = diagCols (Fin b) := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one,
            Matrix.one_mul]
  refine ⟨up σ JB p₀, up σ JB q₀, up σ JB p⁻¹, p₀.1, q₀.1, (p⁻¹).1,
    Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) t,
    Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) s, 1, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · have h := congrArg (incM F) hp₀
    rw [incM_mul, incM_mul, incM_diag] at h
    exact h
  · have h := congrArg (incM F) hq₀
    rw [incM_mul, incM_mul, incM_nabla] at h
    exact h
  · have h := congrArg (incM F) hpinv
    rw [incM_mul, diagCols, incM_diag] at h
    exact h.trans (Matrix.mul_one _).symm
  · rw [hg₁, up_mul, up_mul]

end GlobalTheory.ThetaRatGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryRationalEqDiagonalFixersProductStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledUnitary_rational_eq_diagonalFixers_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (b : ℕ) (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ), (∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) → JB.det ≠ 0 → ∀ (g : UG (cA σ) (dbl (incM F JB))) (g₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E), ((g : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F g₀ → ∃ (p q p' : UG (cA σ) (dbl (incM F JB))) (p₀ q₀ p₀' : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) (t s t' : GL (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), ((p : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F p₀ ∧ ((q : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F q₀ ∧ ((p' : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F p₀' ∧ ((p : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * diagCols (Fin b) = diagCols (Fin b) * (t : Matrix (Fin b) (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) ∧ ((q : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (-1) = Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (-1) * (s : Matrix (Fin b) (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) ∧ ((p' : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * diagCols (Fin b) = diagCols (Fin b) * (t' : Matrix (Fin b) (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) ∧ g = p * q * p' := by
  first | exact @GlobalTheory.ThetaRatGen.gen | exact GlobalTheory.ThetaRatGen.gen | (intros; apply GlobalTheory.ThetaRatGen.gen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalDarbouxFixesThetaDistribution
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.WeilThetaRat

theorem dbl_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ) (hJ : ∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) (hdet : JB.det ≠ 0)
    {κ : Type} [Fintype κ] (hκ : Fintype.card κ = a * b)
    (d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ)
    (hd : ∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F,
      d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ))
    (hdd : IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd) (χ : Chr F E) (hχ : IsHecke F E χ)
    (omd : UG (cA σ) (dbl (incM F JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ))
    (hS : IsSplitting (adeleClass F) ψ dd (actB (cA σ)) omd)
    (hR : SiegelRule (cA σ) (adeleClass F) ψ (-1) (incM F JA) (dbl (incM F JB)) dd χ (diagCols (Fin b)) omd)
    (g : UG (cA σ) (dbl (incM F JB))) (g₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) (hg : ((g : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F g₀) :
    ∀ φ ∈ schA F (κ ⊕ κ), thetaSum F (omd g φ) = thetaSum F φ := by
  intro φ hφ
  obtain ⟨p, q, p', p₀, q₀, p₀', t, s, t', hp, hq, hp', ht, hs, ht', rfl⟩ :=
    GlobalTheory.T.doubledUnitary_rational_eq_diagonalFixers_product F E σ hσ b JB ε hJ hdet g g₀ hg
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  calc
    _ = thetaSum F (omd q (omd p' φ)) :=
      GlobalTheory.T.thetaSum_doubledWeil_fixed_diagonalStabilizer F E σ hσ ψ hψ a b JA JB κ hκ d hd dd hdd χ hχ omd hS hR p p₀ hp t ht (omd q (omd p' φ)) (hS.pres q _ (hS.pres p' _ hφ))
    _ = thetaSum F (omd p' φ) :=
      GlobalTheory.T.adelicThetaSum_doubledWeil_antidiagonal_invariant F E σ hσ ψ hψ a b JA JB κ hκ d hd dd hdd χ hχ omd hS hR q q₀ hq s hs (omd p' φ) (hS.pres p' _ hφ)
    _ = thetaSum F φ :=
      GlobalTheory.T.thetaSum_doubledWeil_fixed_diagonalStabilizer F E σ hσ ψ hψ a b JA JB κ hκ d hd dd hdd χ hχ omd hS hR p' p₀' hp' t' ht' φ hφ

theorem member_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ) (hJ : ∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) (hdet : JB.det ≠ 0)
    {κ : Type} [Fintype κ] (hκ : Fintype.card κ = a * b)
    (d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ)
    (hd : ∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F,
      d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    (χ : Chr F E) (hχ : IsHecke F E χ) (om : UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ))
    (h : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d χ om)
    (γ : UG (cA σ) (incM F JB)) (γ₀ : Matrix (Fin b) (Fin b) E)
    (hγ : ((γ : GL (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b) (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F γ₀) :
    ∀ Φ ∈ schA F κ, thetaSum F (om γ Φ) = thetaSum F Φ := by
  intro Φ hΦ
  obtain ⟨hom, dd, omd, hdd, ⟨-, hS, hR⟩, hres⟩ := h
  obtain ⟨gd, hgd⟩ := GlobalTheory.unitary_diag_one_mem_dbl (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (cA σ) (Fin b) (incM F JB) γ
  have hgd0 : ((gd : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F (Matrix.fromBlocks γ₀ 0 0 1) := by
    rw [hgd, hγ]
    simp only [incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨φ₂, hφ₂, hθ⟩ := GlobalTheory.T.exists_adelicSchwartz_thetaDistributionSum_ne_zero F κ
  have hb := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ Φ hΦ φ₂ hφ₂
  have e1 := dbl_rat σ hσ ψ hψ JA JB ε hJ hdet hκ d hd dd hdd χ hχ omd hS.toIsSplitting hR gd _ hgd0 _ hb
  rw [hres γ gd hgd Φ hΦ φ₂ hφ₂, GlobalTheory.T.adelicThetaDistributionSum_productFunction F κ κ _ (hom.pres γ Φ hΦ) φ₂ hφ₂, GlobalTheory.T.adelicThetaDistributionSum_productFunction F κ κ Φ hΦ φ₂ hφ₂] at e1
  exact mul_right_cancel₀ hθ e1

theorem rat_mat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {γ : UA σ J} (hγ : γ ∈ ratU σ J) :
    ∃ γ₀ : Matrix (Fin n) (Fin n) E, ((γ.1 : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F γ₀ := by
  obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.mp hγ
  refine ⟨(g₀ : Matrix (Fin n) (Fin n) E), ?_⟩
  rw [← hg₀]
  ext i j
  rfl

theorem thetaSum_om_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (n d : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E), (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → (∀ i j, σ (JW j i) = -JW i j) → JW.det ≠ 0 → ∀ (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)) (Fin n × Fin d)), (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW → ∀ om : UA σ JX × UA σ JW →* Module.End ℂ ((Fin n × Fin d → AF F) → ℂ), IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F JX) (incM F JW) co χX χW om → ∀ γ ∈ ratU σ JX, ∀ γ' ∈ ratU σ JW, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  intro F E _ _ _ _ _ σ hσ ψ hψ n d JX JW hX hXd hW hWd co hco χX χW hχX hχW om hom γ hγ γ' hγ' Φ hΦ
  obtain ⟨hB, ⟨d', hd', hA⟩, -⟩ := hom
  obtain ⟨g₀, hg₀⟩ := rat_mat hγ
  obtain ⟨g₀', hg₀'⟩ := rat_mat hγ'
  have eW : ∀ i j, σ (JW j i) = (((-1 : ℤˣ) : ℤ) : E) * JW i j := fun i j => by simp [hW i j]
  have eX : ∀ i j, σ (JX j i) = (((1 : ℤˣ) : ℤ) : E) * JX i j := fun i j => by simp [hX i j]
  have hco' : ∀ x : Matrix (Fin d) (Fin n) E, ∃ y z : Fin n × Fin d → F,
      d'.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := fun x => by
    have e : incM F x = (incM F xᵀ)ᵀ := by simp [incM, Matrix.transpose_map]
    rw [e, hd']
    exact hco xᵀ
  have hx : (γ, γ') = (γ, 1) * (1, γ') := by simp
  rw [hx, map_mul, Module.End.mul_apply]
  have e1 : om (γ, 1) = (om.comp (MonoidHom.inl _ _)) γ := rfl
  have e2 : om (1, γ') = (om.comp (MonoidHom.inr _ _)) γ' := rfl
  have hΦ' : om (1, γ') Φ ∈ schA F (Fin n × Fin d) := hB.1.pres γ' Φ hΦ
  rw [e1, member_rat σ hσ ψ hψ JW JX 1 eX hXd (by simp [Nat.mul_comm]) d' hco' χW hχW _ hA γ g₀ hg₀ _ hΦ', e2]
  exact member_rat σ hσ ψ hψ JX JW (-1) eW hWd (by simp) co hco χX hχX _ hB γ' g₀' hg₀' Φ hΦ

end GlobalTheory.WeilThetaRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalDarbouxFixesThetaDistributionStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_rationalDarboux_fixes_thetaDistribution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) → ∀ (n d : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E), (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → (∀ i j, σ (JW j i) = -JW i j) → JW.det ≠ 0 → ∀ (co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW)) (Fin n × Fin d)), (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW → ∀ om : UA σ JX × UA σ JW →* Module.End ℂ ((Fin n × Fin d → AF F) → ℂ), IsUWeilPair (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW) co χX χW om → ∀ γ ∈ ratU σ JX, ∀ γ' ∈ ratU σ JW, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  first | exact @GlobalTheory.WeilThetaRat.thetaSum_om_rat | exact GlobalTheory.WeilThetaRat.thetaSum_om_rat | (intros; apply GlobalTheory.WeilThetaRat.thetaSum_om_rat <;> assumption)
end

module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalEigenvectorGeneratesIrreducibleSubrepre
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSpherical
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergEquivariantIsometry
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridHeckeCharactersExist

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage

variable {D : D7}

scoped instance lcAE : LocallyCompactSpace (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.1
scoped instance t2AE : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1

def halfMx (a : AE D) (m n : ℕ) : AddSubgroup (Mx D m n) where
  carrier := {t | IsHalf a t}
  add_mem' {x y} hx hy i j := by
    show a * (x i j + y i j) = x i j + y i j
    rw [mul_add, hx i j, hy i j]
  zero_mem' i j := mul_zero a
  neg_mem' {x} hx i j := by
    show a * (-x i j) = -x i j
    rw [mul_neg, hx i j]

theorem mem_halfMx {a : AE D} {m n : ℕ} {t : Mx D m n} : t ∈ halfMx a m n ↔ IsHalf a t := Iff.rfl

theorem isClosed_halfMx (a : AE D) (m n : ℕ) : IsClosed (halfMx a m n : Set (Mx D m n)) := by
  have : (halfMx a m n : Set (Mx D m n)) = ⋂ i, ⋂ j, {t : Mx D m n | a * t i j = t i j} := by
    ext t; simp only [SetLike.mem_coe, mem_halfMx, IsHalf, Set.mem_iInter, Set.mem_setOf_eq]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))
      ((continuous_apply j).comp (continuous_apply i))

scoped instance lcMx (m n : ℕ) : LocallyCompactSpace (Mx D m n) :=
  inferInstanceAs (LocallyCompactSpace (Fin m → Fin n → AE D))

scoped instance tagMx (m n : ℕ) : IsTopologicalAddGroup (Mx D m n) :=
  inferInstanceAs (IsTopologicalAddGroup (Fin m → Fin n → AE D))

scoped instance t2Mx (m n : ℕ) : T2Space (Mx D m n) :=
  inferInstanceAs (T2Space (Fin m → Fin n → AE D))

scoped instance tagHalf (a : AE D) (m n : ℕ) : IsTopologicalAddGroup (halfMx a m n) :=
  inferInstance

scoped instance t2Space_halfAdelicMatrixAddSubgroup (a : AE D) (m n : ℕ) : T2Space (halfMx a m n) := inferInstance

scoped instance lcHalf (a : AE D) (m n : ℕ) : LocallyCompactSpace (halfMx a m n) :=
  (isClosed_halfMx a m n).isClosedEmbedding_subtypeVal.locallyCompactSpace

scoped instance measHalf (a : AE D) (m n : ℕ) : MeasurableSpace (halfMx a m n) := borel _

scoped instance borelHalf (a : AE D) (m n : ℕ) : BorelSpace (halfMx a m n) := ⟨rfl⟩

def haarHalf (a : AE D) (m n : ℕ) : Measure (halfMx a m n) := Measure.addHaar

instance (a : AE D) (m n : ℕ) : (haarHalf a m n).IsAddHaarMeasure := by
  unfold haarHalf; infer_instance

def restEmb (V W : HSp D) {r : ℕ} (K : Matrix (Fin r) (Fin V.rank) D.host.E) (t : Mx D W.rank r) : WO V W :=
  HMul.hMul (t : Matrix (Fin W.rank) (Fin r) (AE D)) (K.map (incA D))

def avgForm (ψ : AddChar (AF D.host.F) ℂ) (V V' W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (K : Matrix (Fin r) (Fin V.rank) D.host.E) (e : AE D) (ℓ' : (WO V' W → ℂ) →ₗ[ℂ] ℂ) (f : WO V W → ℂ) : ℂ :=
  ∫ t : halfMx (cA D e) W.rank r,
    ℓ' (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) f)) ∂haarHalf (cA D e) W.rank r

end GlobalTheory.HalfAverage

namespace GlobalTheory.HalfAverage

variable {D : D7}

theorem isHalf_mul {a : AE D} {m n k : ℕ} {t : Mx D m n} (ht : IsHalf a t) (M : Matrix (Fin n) (Fin k) (AE D)) :
    IsHalf a (HMul.hMul t M : Mx D m k) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, ht i _]

theorem mul_isHalf {a : AE D} {m n : ℕ} {t : Mx D m n} (ht : IsHalf a t) (M : Matrix (Fin m) (Fin m) (AE D)) :
    IsHalf a (HMul.hMul M t : Mx D m n) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_left_comm, ht k j]

def leftMul (a : AE D) {m n : ℕ} (M : Matrix (Fin m) (Fin m) (AE D)) (t : halfMx a m n) : halfMx a m n :=
  ⟨HMul.hMul M (t : Mx D m n), mul_isHalf t.2 M⟩

theorem leftMul_coe (a : AE D) {m n : ℕ} (M : Matrix (Fin m) (Fin m) (AE D)) (t : halfMx a m n) :
    (leftMul a M t : Mx D m n) = HMul.hMul M (t : Mx D m n) := rfl

theorem restEmb_add (V W : HSp D) {r : ℕ} (K : Matrix (Fin r) (Fin V.rank) D.host.E) (t t' : Mx D W.rank r) :
    restEmb V W K (t + t') = restEmb V W K t + restEmb V W K t' := Matrix.add_mul _ _ _

end GlobalTheory.HalfAverage
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsotropicDualFrameOfSplitEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FromColsMulVecEqZero
namespace GlobalTheory.TwistDual

open Matrix

variable {E : Type} [Field E] [StarRing E] [CharZero E]

theorem fromCols_mulVec_eq_zero {n r m : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : Gᴴ = G)
    {C : Matrix (Fin n) (Fin r) E} {B : Matrix (Fin n) (Fin m) E} (hC : LinearIndependent E Cᵀ)
    (hBB : (Bᴴ * G * B).det ≠ 0) (hCB : Cᴴ * G * B = 0)
    (u : Fin r ⊕ Fin m → E) (hu : Matrix.fromCols C B *ᵥ u = 0) : u = 0 := by
  have hBC : Bᴴ * G * C = 0 := by
    have := congrArg conjTranspose hCB
    simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have hsplit : C *ᵥ (u ∘ Sum.inl) + B *ᵥ (u ∘ Sum.inr) = 0 := by
    rw [← hu]; funext i
    simp [mulVec, dotProduct, Fintype.sum_sum_type]
  have hb : u ∘ Sum.inr = 0 := by
    have h2 := congrArg (fun w => (Bᴴ * G) *ᵥ w) hsplit
    simp only [mulVec_add, mulVec_mulVec, hBC, zero_mulVec, zero_add, mulVec_zero] at h2
    exact Matrix.eq_zero_of_mulVec_eq_zero hBB h2
  have ha : u ∘ Sum.inl = 0 := by
    rw [hb, mulVec_zero, add_zero] at hsplit
    have hC' := Fintype.linearIndependent_iff.1 hC
    funext k
    refine hC' _ ?_ k
    rw [← hsplit]; funext i
    simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
  funext x
  rcases x with k | k
  · exact congrFun ha k
  · exact congrFun hb k

theorem mulVec_surjective {n r m : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : Gᴴ = G) (hGd : G.det ≠ 0)
    {C : Matrix (Fin n) (Fin r) E} {B : Matrix (Fin n) (Fin m) E} (hC : LinearIndependent E Cᵀ)
    (hBB : (Bᴴ * G * B).det ≠ 0) (hCB : Cᴴ * G * B = 0) :
    Function.Surjective ((Matrix.fromCols C B)ᴴ * G).mulVecLin := by
  set M := (Matrix.fromCols C B)ᴴ * G
  have hinj : Function.Injective Mᵀ.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    rw [Matrix.mulVecLin_apply, mulVec_transpose] at hw
    have h1 := congrArg star hw
    rw [star_vecMul, star_zero, conjTranspose_mul, hG, conjTranspose_conjTranspose, ← mulVec_mulVec] at h1
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hGd h1
    have h3 := fromCols_mulVec_eq_zero hG hC hBB hCB _ h2
    simpa using congrArg star h3
  have hr : Mᵀ.rank = Fintype.card (Fin r ⊕ Fin m) := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  rw [Matrix.rank_transpose] at hr
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, ← hr]
  rfl

theorem exists_dual {n r m : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : Gᴴ = G) (hGd : G.det ≠ 0)
    {C : Matrix (Fin n) (Fin r) E} {B : Matrix (Fin n) (Fin m) E} (hC : LinearIndependent E Cᵀ)
    (hCC : Cᴴ * G * C = 0) (hBB : (Bᴴ * G * B).det ≠ 0) (hCB : Cᴴ * G * B = 0) :
    ∃ C' : Matrix (Fin n) (Fin r) E, Cᴴ * G * C' = 1 ∧ C'ᴴ * G * C' = 0 ∧ C'ᴴ * G * B = 0 := by
  have hs := mulVec_surjective hG hGd hC hBB hCB
  choose v hv using fun k : Fin r => hs (Pi.single (Sum.inl k) (1 : E))
  set C₁ : Matrix (Fin n) (Fin r) E := Matrix.of fun i k => v k i
  have key : ∀ a k, ∑ i, ((Matrix.fromCols C B)ᴴ * G) a i * C₁ i k = (Pi.single (Sum.inl k) (1 : E) : Fin r ⊕ Fin m → E) a := by
    intro a k
    rw [← hv k]
    simp only [C₁, Matrix.mulVecLin_apply, mulVec, dotProduct, Matrix.of_apply]
  have hC1 : Cᴴ * (G * C₁) = 1 := by
    ext j k
    have := key (Sum.inl j) k
    rw [← Matrix.mul_assoc]
    simp only [Matrix.mul_apply, conjTranspose_apply, fromCols_apply_inl] at this ⊢
    rw [this, Pi.single_apply, Matrix.one_apply]
    simp [eq_comm]
  have hB1 : Bᴴ * (G * C₁) = 0 := by
    ext j k
    have := key (Sum.inr j) k
    rw [← Matrix.mul_assoc]
    simp only [Matrix.mul_apply, conjTranspose_apply, fromCols_apply_inr] at this ⊢
    rw [this]
    simp
  have hGc : ∀ (p q : ℕ) (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E),
      Yᴴ * (G * X) = (Xᴴ * (G * Y))ᴴ := by
    intro p q X Y
    simp [conjTranspose_mul, hG, Matrix.mul_assoc]
  have hCC' : Cᴴ * (G * C) = 0 := by rw [← Matrix.mul_assoc]; exact hCC
  have hCB' : Cᴴ * (G * B) = 0 := by rw [← Matrix.mul_assoc]; exact hCB
  have h1C : C₁ᴴ * (G * C) = 1 := by rw [hGc, hC1, conjTranspose_one]
  have h1B : C₁ᴴ * (G * B) = 0 := by
    have := congrArg conjTranspose hB1
    rw [conjTranspose_zero, ← hGc] at this
    exact this
  set S := C₁ᴴ * (G * C₁) with hSdef
  have hS : Sᴴ = S := by rw [hSdef, ← hGc]
  set X : Matrix (Fin r) (Fin r) E := (2 : E)⁻¹ • S with hXdef
  have hX : Xᴴ = X := by
    rw [hXdef, conjTranspose_smul, hS, star_inv₀, star_ofNat]
  have hXX : X + X = S := by
    rw [hXdef, ← add_smul, ← two_mul, mul_inv_cancel₀ (two_ne_zero), one_smul]
  have a1 : ∀ Y : Matrix (Fin r) (Fin r) E, Cᴴ * (G * (C * Y)) = 0 := fun Y => by
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, hCC', Matrix.zero_mul]
  have a2 : ∀ Y : Matrix (Fin r) (Fin r) E, C₁ᴴ * (G * (C * Y)) = Y := fun Y => by
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, h1C, Matrix.one_mul]
  refine ⟨C₁ - C * X, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hC1, a1, sub_zero]
  · simp only [conjTranspose_sub, conjTranspose_mul, hX, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      hC1, a1, a2, Matrix.mul_one, Matrix.mul_zero, sub_zero]
    rw [← hSdef, ← hXX]; abel
  · simp only [conjTranspose_sub, conjTranspose_mul, hX, Matrix.sub_mul, Matrix.mul_assoc, h1B, hCB',
      Matrix.mul_zero, sub_zero]

end GlobalTheory.TwistDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsotropicDualFrameOfSplitEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistDual

variable {D : D7}

theorem adj_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D A = Aᴴ := by
  funext i j
  rfl

theorem hT_coord (V : HSp D) (x y : V.V) :
    V.hT x y = ∑ i, ∑ j, star (V.frame.repr x i) * V.gram i j * V.frame.repr y j := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, HSpace.gram]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RingHom.id_apply, starRingEnd_apply, mul_comm]

theorem gram_det_ne (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    rw [hT_coord]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : ∑ j, V.gram i j * v j = 0 := congr_fun h0 i
    have h2 : ∀ j, V.frame.repr (V.frame.equivFun.symm v) j = v j := fun j =>
      congr_fun (V.frame.equivFun.apply_symm_apply v) j
    simp only [h2, mul_assoc, ← Finset.mul_sum, h1, mul_zero]
  exact V.frame.equivFun.symm.map_eq_zero_iff.1 this

theorem gram_ct (V : HSp D) : V.gramᴴ = V.gram := by
  funext i j
  exact V.herm.eq (V.frame j) (V.frame i)

theorem exists_isotropic_dual : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B →
    ∃ C' : Matrix (Fin V.rank) (Fin r) D.host.E,
      adj D C * V.gram * C' = 1 ∧ adj D C' * V.gram * C' = 0 ∧ adj D C' * V.gram * B = 0 := by
  intro D V V' r C B hs
  simp only [adj_eq]
  have hCC : Cᴴ * V.gram * C = 0 := by rw [← adj_eq]; exact hs.frame.2.2
  have hBB : (Bᴴ * V.gram * B).det ≠ 0 := by rw [← adj_eq, hs.isom]; exact gram_det_ne V'
  have hCB : Cᴴ * V.gram * B = 0 := by rw [← adj_eq]; exact hs.orth
  exact exists_dual (gram_ct V) (gram_det_ne V) hs.frame.2.1 hCC hBB hCB

end GlobalTheory.TwistDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsotropicDualFrameOfSplitEmbeddingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropicDualFrame_of_splitEmbedding : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∃ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 ∧ adj D C' * V.gram * C' = 0 ∧ adj D C' * V.gram * B = 0 := by
  first | exact @GlobalTheory.TwistDual.exists_isotropic_dual | exact GlobalTheory.TwistDual.exists_isotropic_dual | (intros; apply GlobalTheory.TwistDual.exists_isotropic_dual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParamTrivialBoundUnitaryGL
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParamTrivialBoundUnitaryGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.ParGL

theorem exists_isSatVecGL_bound : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V), IsUnitarisable ρ → ∀ x : V, x ≠ 0 → x ∈ fixed ρ (KGL w (n := n)) → (∀ h ∈ Hecke ℂ (KGL w (n := n)), ∃ c : ℂ, heckeVec ρ (KGL w (n := n)) h x = c • x) → ∃ B, IsSatVecGL w ρ x B ∧ ∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((n : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  intro E _ _ w n V _ _ ρ hun x hx0 hxf hs
  have hK : IsCommensurated (KGL w (n := n)) := Formalism.UG.Final.GLintComm E w n
  obtain ⟨U, hU, hxU, hirr, hunU, hline⟩ :=
    GlobalTheory.T.spherical_eigenvector_generates_irreducible_subrepresentation ρ (KGL w (n := n)) (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1 hK hun x hx0 hxf hs
  set π := GlobalTheory.PRep.sub ρ U hU with hπ
  let x' : U := ⟨x, hxU⟩
  have hx'0 : x' ≠ 0 := fun e => hx0 (congrArg Subtype.val e)
  have hx'f : x' ∈ fixed π (KGL w (n := n)) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hxf k hk)
  have hsub : ∀ g (y : U), U.subtype (π g y) = ρ g (U.subtype y) := fun _ _ => rfl
  have heig : ∀ h ∈ Hecke ℂ (KGL w (n := n)), ∃ c : ℂ, ∀ y ∈ fixed π (KGL w (n := n)), heckeVec π (KGL w (n := n)) h y = c • y := by
    intro h hh
    obtain ⟨c, hc⟩ := hs h hh
    have e1 : heckeVec π (KGL w (n := n)) h x' = c • x' := Subtype.val_injective (by
      have := map_heckeVec hK hh U.subtype hsub (x := x')
      exact this.trans hc)
    refine ⟨c, fun y hy => ?_⟩
    obtain ⟨a, rfl⟩ := hline y hy
    have := map_heckeVec hK hh (ρ := π) (ρ' := π) (a • LinearMap.id) (fun g y => by simp) (x := x')
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at this
    rw [← this, e1, smul_comm]
  obtain ⟨B, hB⟩ := GlobalTheory.LFun.ExSatGL.exists_hasSatGL E w n U π
    ((Submodule.ne_bot_iff _).2 ⟨x', hx'f, hx'0⟩) heig
  have hx' : IsSatVecGL w π x' B := hB.2 x' hx'f hx'0
  have hup := GlobalTheory.T.norm_satake_le_of_unitary_spherical_GL GlobalTheory.SatakeBound.satakeTrivialBound E w n _ π B hirr hunU hB
  refine ⟨B, hx'.map U.subtype hsub hx0, fun β hβ => ⟨hup β hβ, ?_⟩⟩
  have hst := GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv E w n _ π x' B hunU hx'
  have h1 : β⁻¹ ∈ B.map star := hst ▸ Multiset.mem_map_of_mem _ hβ
  obtain ⟨β', hβ', e⟩ := Multiset.mem_map.1 h1
  have h2 : ‖((β⁻¹ : ℂˣ) : ℂ)‖ = ‖(β' : ℂ)‖ := by
    rw [← e]
    simp
  rw [h2]
  exact hup β' hβ'

end GlobalTheory.FinZeta.ParGL

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParamTrivialBoundUnitaryGLStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_satakeParam_trivialBound_unitaryGL : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V), IsUnitarisable ρ → ∀ x : V, x ≠ 0 → x ∈ fixed ρ (KGL w (n := n)) → (∀ h ∈ Hecke ℂ (KGL w (n := n)), ∃ c : ℂ, heckeVec ρ (KGL w (n := n)) h x = c • x) → ∃ B, IsSatVecGL w ρ x B ∧ ∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((n : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  first | exact @GlobalTheory.FinZeta.ParGL.exists_isSatVecGL_bound | exact GlobalTheory.FinZeta.ParGL.exists_isSatVecGL_bound | (intros; apply GlobalTheory.FinZeta.ParGL.exists_isSatVecGL_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedHeisenbergTermsPermutedRationalUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedHeisenbergTermsPermutedRationalUnitary
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistEquiRat

variable {D : D7}

theorem integral_mul_left {m n : ℕ} (μ : Measure (Mx D m n)) (𝓨 : Set (Mx D m n))
    (h : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) μ 𝓨) (P Q : Mx D m m) (hP : P ∈ GlobalTheory.MixModel.ratMx D m m)
    (hQ : Q ∈ GlobalTheory.MixModel.ratMx D m m) (hPQ : P * Q = 1) (hQP : Q * P = 1) (φ : Mx D m n → ℂ)
    (hφ : ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∀ a, φ (γ + a) = φ a) :
    ∫ a in 𝓨, φ (P * a) ∂μ = ∫ a in 𝓨, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  let eA : Mx D m n ≃+ Mx D m n :=
    { toFun := fun a => P * a
      invFun := fun a => Q * a
      left_inv := fun a => by show Q * (P * a) = a; rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
      right_inv := fun a => by show P * (Q * a) = a; rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
      map_add' := fun a b => Matrix.mul_add P a b }
  have hc : Continuous (fun a : Mx D m n => P * a) := continuous_const.matrix_mul continuous_id
  have hc' : Continuous (fun a : Mx D m n => Q * a) := continuous_const.matrix_mul continuous_id
  let eH : Mx D m n ≃ₜ Mx D m n := ⟨eA.toEquiv, hc, hc'⟩
  let eM : Mx D m n ≃ᵐ Mx D m n := eH.toMeasurableEquiv
  haveI := h.1
  have hHaar : (μ.map eM).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ eA hc hc'
  have hmp : MeasurePreserving eM μ (μ.map eM) := ⟨eM.measurable, rfl⟩
  have hmp' : MeasurePreserving eM.symm (μ.map eM) μ := MeasurePreserving.symm eM hmp
  let eG : GlobalTheory.MixModel.ratMx D m n → GlobalTheory.MixModel.ratMx D m n :=
    fun g => ⟨P * (g : Mx D m n), GlobalTheory.MixModel.ratMx_mul hP g.2⟩
  have hbij : Function.Bijective eG := by
    refine ⟨fun g g' hg => ?_, fun g => ⟨⟨Q * (g : Mx D m n), GlobalTheory.MixModel.ratMx_mul hQ g.2⟩, ?_⟩⟩
    · have e := congrArg (fun x : GlobalTheory.MixModel.ratMx D m n => Q * (x : Mx D m n)) hg
      simp only [eG, ← Matrix.mul_assoc, hQP, Matrix.one_mul] at e
      exact Subtype.ext e
    · apply Subtype.ext
      show P * (Q * (g : Mx D m n)) = g
      rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hF : IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D m n) (eM.symm ⁻¹' 𝓨) (μ.map eM) := by
    refine h.2.1.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
    show Q * (P * (g : Mx D m n) + x) = (g : Mx D m n) + Q * x
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hpre : eM ⁻¹' (eM.symm ⁻¹' 𝓨) = 𝓨 := by
    ext a; simp
  have hvol : (μ.map eM) (eM.symm ⁻¹' 𝓨) = 1 := by
    rw [MeasurableEquiv.map_apply, hpre]; exact h.2.2
  have e1 := hmp.setIntegral_preimage_emb eM.measurableEmbedding φ (eM.symm ⁻¹' 𝓨)
  rw [hpre] at e1
  exact e1.trans (GlobalTheory.MixModel.covolOne_integral_eq h ⟨hHaar, hF, hvol⟩ φ hφ)

theorem symplOH_isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (hC : IsIsoFrame V C)
    (q₀ : Matrix (Fin W.rank) (Fin r) D.host.E) (a : Mx D W.rank r) :
    symplOH V W (isoPart V W C (q₀.map (incA D))) (isoPart V W C a) = 0 := by
  set X : Mx D r V.rank := (adj D C * V.gram).map (incA D) with hXdef
  have hM : (adj D C * V.gram)ᴴ = V.gram * C := by
    rw [Matrix.conjTranspose_mul, GlobalTheory.MixModel.gram_conjTranspose]
    show V.gram * (Cᴴ)ᴴ = V.gram * C
    rw [Matrix.conjTranspose_conjTranspose]
  have hX0 : X * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj X = 0 := by
    have e : GlobalTheory.MixModel.adj X = GlobalTheory.MixModel.rat (V.gram * C) := by
      rw [hXdef, ← hM]; rfl
    rw [e, hXdef]
    show GlobalTheory.MixModel.rat (adj D C * V.gram) * GlobalTheory.MixModel.rat V.gram⁻¹ * GlobalTheory.MixModel.rat (V.gram * C) = 0
    rw [← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul]
    have : adj D C * V.gram * V.gram⁻¹ * (V.gram * C) = adj D C * V.gram * C := by
      rw [Matrix.mul_assoc (adj D C * V.gram), ← Matrix.mul_assoc V.gram⁻¹,
        Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
    rw [this]
    exact (congrArg GlobalTheory.MixModel.rat hC.2.2).trans GlobalTheory.MixModel.rat_zero
  rw [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace]
  have e2 : isoPart V W C (q₀.map (incA D)) = q₀.map (incA D) * X := rfl
  have e3 : isoPart V W C a = a * X := rfl
  rw [e2, e3, GlobalTheory.MixModel.adj_mul]
  have e4 : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj X * GlobalTheory.MixModel.adj a * (GlobalTheory.MixModel.gA W * (q₀.map (incA D) * X)))
      = (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj X * GlobalTheory.MixModel.adj a * GlobalTheory.MixModel.gA W * q₀.map (incA D)) * X := by
    simp only [Matrix.mul_assoc]
  rw [e4, Matrix.trace_mul_comm]
  have e5 : X * (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj X * GlobalTheory.MixModel.adj a * GlobalTheory.MixModel.gA W * q₀.map (incA D))
      = (X * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj X) * (GlobalTheory.MixModel.adj a * GlobalTheory.MixModel.gA W * q₀.map (incA D)) := by
    simp only [Matrix.mul_assoc]
  rw [e5, hX0, Matrix.zero_mul, Matrix.trace_zero, map_zero]

theorem isoPart_add (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (y z : Mx D W.rank r) :
    isoPart V W C (y + z) = isoPart V W C y + isoPart V W C z := by
  unfold isoPart; exact Matrix.add_mul _ _ _

theorem ratW_eq_isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (q₀ : Matrix (Fin W.rank) (Fin r) D.host.E) :
    ratW W V (q₀ * (adj D C * V.gram)) = isoPart V W C (q₀.map (incA D)) := by
  unfold isoPart ratW; exact Matrix.map_mul

end GlobalTheory.TwistEquiRat

namespace GlobalTheory.TwistEquiRat

theorem res_heisO_rat_equi : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (γ : GA D W) (γ₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), γ ∈ GQ W → Formalism.L2.Theta.mt W γ = γ₀.map (incA D) → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map (γ₀ * y) (incA D))) (ω (1, γ) f)) 0 = res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) f) 0 := by
  intro D V V' W r C C' B hs _ _ _ ψ χS χT ω hω μ 𝓨 hμ γ γ₀ hγ hγ₀ y f hf
  have hstd := hω.std
  set w₀ := isoPart V W C' (Matrix.map y (incA D)) with hw₀
  have hact : ∀ x : WO V W, actO V W 1 γ x = Formalism.L2.Theta.mt W γ * x := by
    intro x
    rw [GlobalTheory.MixModel.actO_eq, inv_one, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have e1 : isoPart V W C' (Matrix.map (γ₀ * y) (incA D)) = actO V W 1 γ w₀ := by
    rw [hact, hw₀]
    show Matrix.map (γ₀ * y) (incA D) * (((adj D C' * V.gram).map (incA D)) : Mx D r V.rank) = Formalism.L2.Theta.mt W γ * (Matrix.map y (incA D) * (((adj D C' * V.gram).map (incA D)) : Mx D r V.rank))
    rw [Matrix.map_mul, ← hγ₀, Matrix.mul_assoc]
  have e2 : heisO ψ V W (isoPart V W C' (Matrix.map (γ₀ * y) (incA D))) (ω (1, γ) f) =
      ω (1, γ) (heisO ψ V W w₀ f) := by
    rw [e1]; exact (hω.om_heis 1 γ w₀ f hf).symm
  rw [e2]
  set G := heisO ψ V W w₀ f with hGdef
  have hG : IsThetaFunO ψ V W G := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hstd V W).1 w₀ f hf
  have hrat := GlobalTheory.WeilRat.om_rat_actO D ψ hstd V W χS χT ω hω 1 (one_mem _) γ hγ G hG
  have hQP : Formalism.L2.Theta.mt W γ * Formalism.L2.Theta.mt W γ⁻¹ = 1 := GlobalTheory.MixModel.mt_mul_inv W γ
  have hPQ : Formalism.L2.Theta.mt W γ⁻¹ * Formalism.L2.Theta.mt W γ = 1 := GlobalTheory.MixModel.mt_inv_mul W γ
  have hmid : midPart V V' W B 0 = 0 := by
    show HMul.hMul (0 : Matrix (Fin W.rank) (Fin V'.rank) (AE D)) _ = 0
    exact Matrix.zero_mul _
  have hpt : ∀ a, ω (1, γ) G (isoPart V W C a + midPart V V' W B 0) =
      G (isoPart V W C (Formalism.L2.Theta.mt W γ⁻¹ * a) + midPart V V' W B 0) := by
    intro a
    rw [hmid, add_zero, add_zero, ← hrat, hact]
    refine congrArg (ω (1, γ) G) ?_
    show a * (((adj D C * V.gram).map (incA D)) : Mx D r V.rank) = Formalism.L2.Theta.mt W γ * (Formalism.L2.Theta.mt W γ⁻¹ * a * (((adj D C * V.gram).map (incA D)) : Mx D r V.rank))
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  show ∫ a in 𝓨, ω (1, γ) G (isoPart V W C a + midPart V V' W B 0) ∂μ =
    ∫ a in 𝓨, G (isoPart V W C a + midPart V V' W B 0) ∂μ
  simp only [hpt]
  have hper : ∀ q ∈ GlobalTheory.MixModel.ratMx D W.rank r, ∀ a,
      G (isoPart V W C (q + a) + midPart V V' W B 0) = G (isoPart V W C a + midPart V V' W B 0) := by
    intro q hq a
    obtain ⟨q₀, rfl⟩ := hq
    have e3 : (incA D).toAddMonoidHom.mapMatrix q₀ = q₀.map (incA D) := rfl
    rw [hmid, add_zero, add_zero, e3, isoPart_add, ← ratW_eq_isoPart, hG.quasi, ratW_eq_isoPart, symplOH_isoPart V W C hs.frame, neg_zero, AddChar.map_zero_eq_one,
      one_mul]
  exact integral_mul_left μ 𝓨 hμ _ _ ((GlobalTheory.MixModel.mem_GQ_iff W γ⁻¹).1 (inv_mem hγ))
    ((GlobalTheory.MixModel.mem_GQ_iff W γ).1 hγ) hPQ hQP (fun a => G (isoPart V W C a + midPart V V' W B 0)) hper

end GlobalTheory.TwistEquiRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedHeisenbergTermsPermutedRationalUnitaryStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictedHeisenbergTerms_permuted_rationalUnitary : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (γ : GA D W) (γ₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), γ ∈ GQ W → Formalism.L2.Theta.mt W γ = γ₀.map (incA D) → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map (γ₀ * y) (incA D))) (ω (1, γ) f)) 0 = res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) f) 0 := by
  first | exact @GlobalTheory.TwistEquiRat.res_heisO_rat_equi | exact GlobalTheory.TwistEquiRat.res_heisO_rat_equi | (intros; apply GlobalTheory.TwistEquiRat.res_heisO_rat_equi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelAndTwistPlacesSplitDistinct
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelAndTwistPlacesSplitDistinct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.TwistTypePlaces

theorem card_quot_of_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hr : Module.finrank F E = 2) (P : HeightOneSpectrum (𝓞 E))
    (h2 : (Ideal.primesOver (P.under (𝓞 F)).asIdeal (𝓞 E)).ncard = 2) :
    Nat.card (𝓞 E ⧸ P.asIdeal) = Ideal.absNorm (P.under (𝓞 F)).asIdeal := by
  classical
  set p := (P.under (𝓞 F)).asIdeal with hp
  have hp0 : p ≠ ⊥ := (P.under (𝓞 F)).ne_bot
  have : p.IsMaximal := (P.under (𝓞 F)).isMaximal
  have : P.asIdeal.LiesOver p := ⟨by rw [hp, HeightOneSpectrum.under_asIdeal]⟩
  have hsum := Ideal.sum_ramification_inertia (𝓞 E) F E (p := p) hp0
  have hcard : (IsDedekindDomain.primesOverFinset p (𝓞 E)).card = 2 := by
    rw [← h2, ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 E), Set.ncard_coe_finset]
  have hle : ∀ Q ∈ IsDedekindDomain.primesOverFinset p (𝓞 E), 1 ≤ p.ramificationIdx' Q * p.inertiaDeg' Q := by
    intro Q hQ
    obtain ⟨hQp, hQl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 E)).1 hQ
    have h1 : 0 < p.inertiaDeg' Q := Ideal.inertiaDeg'_pos p Q
    have h2 : 0 < p.ramificationIdx' Q := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx p Q hp0]
      exact Ideal.ramificationIdx_pos (R := 𝓞 F) Q
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero h2.ne' h1.ne')
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 (by rw [hsum, hr, Finset.sum_const, hcard]; rfl)
  have hPm : P.asIdeal ∈ IsDedekindDomain.primesOverFinset p (𝓞 E) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 E)).2 ⟨P.isPrime, inferInstance⟩
  have hf : p.inertiaDeg' P.asIdeal = 1 := Nat.eq_one_of_mul_eq_one_left (heq _ hPm).symm
  have hn := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal p (P.under (𝓞 F)).isPrime hp0
  rw [hf, pow_one, Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
  exact hn

end GlobalTheory.TwistTypePlaces

namespace GlobalTheory.TwistTypePlaces

theorem under_conjPl {D : D7} (P : Pl D.host.E) :
    (conjPl P).under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := by
  have hfix : ∀ x : 𝓞 D.host.F,
      Formalism.DivisionValues.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := by
    intro x
    apply RingOfIntegers.ext
    show star ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E) = _
    exact (D.sp.cm.fixed _).2 ⟨(x : D.host.F), rfl⟩
  have hinv : ∀ z, Formalism.DivisionValues.cO D.host.E (Formalism.DivisionValues.cO D.host.E z) = z :=
    fun z => RingOfIntegers.ext (star_star (z : D.host.E))
  apply HeightOneSpectrum.ext
  ext x
  simp only [HeightOneSpectrum.under_asIdeal, Ideal.mem_comap]
  change algebraMap _ _ x ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) ↔ _
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have e : z = algebraMap _ _ x := by rw [← hinv z, hzx, hfix]
    rwa [← e]
  · intro h
    exact ⟨_, h, hfix x⟩

theorem natCast_mem_conjPl {D : D7} (P : Pl D.host.E) (n : ℕ) (h : (n : 𝓞 D.host.E) ∈ P.asIdeal) :
    (n : 𝓞 D.host.E) ∈ (conjPl P).asIdeal := by
  have := Ideal.mem_map_of_mem (Formalism.DivisionValues.cO D.host.E) h
  rwa [map_natCast] at this

theorem ncard_primesOver_two {D : D7} (P : Pl D.host.E) (h : conjPl P ≠ P) :
    (Ideal.primesOver (P.under (𝓞 D.host.F)).asIdeal (𝓞 D.host.E)).ncard = 2 := by
  rw [GlobalTheory.QuadSignLocal.ncard_primesOver]
  have hs : {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)} = {P, conjPl P} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · exact GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq
    · rintro (rfl | rfl)
      · rfl
      · exact under_conjPl P
  rw [hs, Set.ncard_pair h.symm]

theorem natCast_not_mem_of_card {E : Type} [Field E] [NumberField E] (PP : Pl E) {q g : ℕ} (hq : q.Prime) (hg : g.Prime)
    (hc : Nat.card (kP PP) = q) (hne : q ≠ g) : ((g : ℕ) : 𝓞 E) ∉ PP.asIdeal := by
  intro hm
  have hnt : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
  have hq0 : ((q : ℕ) : kP PP) = 0 := by
    have := card_nsmul_eq_zero' (G := kP PP) (x := 1)
    rwa [hc, nsmul_one] at this
  have hg0 : ((g : ℕ) : kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  obtain ⟨a, b, hab⟩ : IsCoprime (q : ℤ) (g : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hg).2 hne)
  have h1 : ((a * q + b * g : ℤ) : kP PP) = 1 := by rw [hab, Int.cast_one]
  push_cast at h1
  rw [hq0, hg0, mul_zero, mul_zero, add_zero] at h1
  exact zero_ne_one h1

end GlobalTheory.TwistTypePlaces

namespace GlobalTheory.TwistTypePlaces

theorem places_split : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ t : T, Disjoint R.Pg (R.Q t) ∧ Set.InjOn (fun PP : Pl D.host.E => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ↑(R.Pg ∪ R.Q t) ∧ ∀ PP ∈ R.Pg ∪ R.Q t, (Ideal.primesOver ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal (𝓞 D.host.E)).ncard = 2 ∧ Nat.card (kP PP) = Ideal.absNorm ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t
  have hL := hC.lev
  have hPg := hL.Pg
  have hQ := hL.Q_pl t
  have gP : ∀ PP ∈ R.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP h
    obtain ⟨k, hk⟩ := (hPg PP).1 h
    exact ⟨k, R.C.P.overP hk⟩
  have qN : ∀ PP ∈ R.Q t, ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP h k
    obtain ⟨q, hq, hc, -, hne⟩ := (hQ PP h).1
    exact natCast_not_mem_of_card PP hq (D.host.g_prime k) hc (hne k)
  have hdis : Disjoint R.Pg (R.Q t) := by
    rw [Finset.disjoint_left]
    intro PP h1 h2
    obtain ⟨k, hk⟩ := gP PP h1
    exact qN PP h2 k hk
  have cross : ∀ PP ∈ R.Pg, ∀ PP' ∈ R.Q t, PP' ≠ conjPl PP := by
    rintro PP h PP' h' rfl
    obtain ⟨k, hk⟩ := gP PP h
    exact qN _ h' k (natCast_mem_conjPl PP _ hk)
  have hnc : ∀ PP ∈ R.Pg ∪ R.Q t, ∀ PP' ∈ R.Pg ∪ R.Q t, PP' ≠ conjPl PP := by
    intro PP h PP' h' e
    rcases Finset.mem_union.1 h with h | h <;> rcases Finset.mem_union.1 h' with h' | h'
    · exact GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hPg PP h PP' h' (GlobalTheory.GoodPrimes.isConjPl_iff.2 e)
    · exact cross PP h PP' h' e
    · refine cross PP' h' PP h ?_
      rw [e, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
    · exact (hQ PP h).2 PP' h' (GlobalTheory.GoodPrimes.isConjPl_iff.2 e)
  refine ⟨hdis, ?_, ?_⟩
  · intro PP h PP' h' e
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with e' | e'
    · exact e'.symm
    · exact absurd e' (hnc PP h PP' h')
  · intro PP h
    have h2 := ncard_primesOver_two PP (fun e => hnc PP h PP h e.symm)
    exact ⟨h2, card_quot_of_two D.sp.cm.deg2 PP h2⟩

end GlobalTheory.TwistTypePlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelAndTwistPlacesSplitDistinctStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelAndTwistPlaces_split_distinct : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ t : T, Disjoint R.Pg (R.Q t) ∧ Set.InjOn (fun PP : Pl D.host.E => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ↑(R.Pg ∪ R.Q t) ∧ ∀ PP ∈ R.Pg ∪ R.Q t, (Ideal.primesOver ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal (𝓞 D.host.E)).ncard = 2 ∧ Nat.card (kP PP) = Ideal.absNorm ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
  first | exact @GlobalTheory.TwistTypePlaces.places_split | exact GlobalTheory.TwistTypePlaces.places_split | (intros; apply GlobalTheory.TwistTypePlaces.places_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspFunOfTendstoModerateGrowthSize
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspFunOfTendstoModerateGrowthSize
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspLimit

theorem integral_eq_zero_of_approx {X : Type} [MeasurableSpace X] {μ : Measure X} {u : ℕ → X → ℂ} {v : X → ℂ}
    {w : X → ℝ} (hu : ∀ n, Integrable (u n) μ) (hv : Integrable v μ) (hw : Integrable w μ)
    (h0 : ∀ n, ∫ x, u n x ∂μ = 0) (h : ∀ ε : ℝ, 0 < ε → ∃ n, ∀ x, ‖u n x - v x‖ ≤ ε * w x) :
    ∫ x, v x ∂μ = 0 := by
  have key : ∀ ε : ℝ, 0 < ε → ‖∫ x, v x ∂μ‖ ≤ ε * ∫ x, w x ∂μ := fun ε hε => by
    obtain ⟨n, hn⟩ := h ε hε
    have e : ∫ x, (u n x - v x) ∂μ = -∫ x, v x ∂μ := by rw [integral_sub (hu n) hv, h0, zero_sub]
    rw [← norm_neg, ← e, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hw.const_mul ε) (Filter.Eventually.of_forall hn)
  have t : Filter.Tendsto (fun ε : ℝ => ε * ∫ x, w x ∂μ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 * ∫ x, w x ∂μ)) :=
    ((continuous_id.mul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [zero_mul] at t
  exact norm_le_zero_iff.1 (ge_of_tendsto t (eventually_nhdsWithin_of_forall key))

theorem isCuspFun_of_tendsto : ∀ (D : D7) (V : HSp D) (N : ℕ) (ψ : ℕ → GA D V → ℂ) (f : GA D V → ℂ), (∀ n, Continuous (ψ n) ∧ (∀ γ ∈ GQ V, ∀ g, ψ n (γ * g) = ψ n g) ∧ IsCuspFun V (ψ n)) → Continuous f → (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) → Filter.Tendsto (fun n => GlobalTheory.Size.growthSize V N (ψ n - f)) Filter.atTop (nhds 0) → IsCuspFun V f := by
  intro D V N ψ f hψ hf hl ht
  have hint : ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) →
      ∀ W, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W → ∀ μ : Measure (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W), μ.IsHaarMeasure →
      ∀ 𝓕, IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRat D.sp.cm V W) 𝓕 μ → ∀ g : GA D V,
        IntegrableOn (fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => φ (n.1 * g)) 𝓕 μ := by
    intro φ hc hl W hW μ hμ 𝓕 h𝓕 g
    rw [GlobalTheory.AutFunCompare.GQ_eq] at hl
    exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V W hW φ hc hl μ hμ 𝓕 h𝓕 g
  rw [GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm]
  intro W hW μ hμ 𝓕 h𝓕 g
  obtain ⟨h1, h2, -, h4⟩ := GlobalTheory.Size.quotHeight_laws V
  have hw := (hint (fun x => ((GlobalTheory.Grow.quotHeight V x ^ N : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (h4.pow N)) (fun γ hγ x => by rw [h2 γ hγ]) W hW μ hμ 𝓕 h𝓕 g).re
  refine integral_eq_zero_of_approx (μ := μ.restrict 𝓕) (u := fun k n => ψ k (n.1 * g)) (v := fun n => f (n.1 * g))
    (fun k => hint _ (hψ k).1 (hψ k).2.1 W hW μ hμ 𝓕 h𝓕 g) (hint _ hf hl W hW μ hμ 𝓕 h𝓕 g) hw
    (fun k => (GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm V _).1 (hψ k).2.2 W hW μ hμ 𝓕 h𝓕 g) fun ε hε => ?_
  obtain ⟨k, hk⟩ := (ht.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 hε))).exists
  refine ⟨k, fun n => ?_⟩
  rw [GlobalTheory.Size.growthSize_eq_quot (fun γ hγ x => by
    rw [Pi.sub_apply, Pi.sub_apply, (hψ k).2.1 γ hγ, hl γ hγ])] at hk
  have := (ENNReal.ofReal_le_ofReal_iff hε.le).1 ((le_iSup _ (n.1 * g)).trans hk)
  exact (div_le_iff₀ (pow_pos (lt_of_lt_of_le one_pos (h1 _).1) N)).1 this

end GlobalTheory.CuspLimit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspFunOfTendstoModerateGrowthSizeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspFun_of_tendsto_moderateGrowthSize : ∀ (D : D7) (V : HSp D) (N : ℕ) (ψ : ℕ → GA D V → ℂ) (f : GA D V → ℂ), (∀ n, Continuous (ψ n) ∧ (∀ γ ∈ GQ V, ∀ g, ψ n (γ * g) = ψ n g) ∧ IsCuspFun V (ψ n)) → Continuous f → (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) → Filter.Tendsto (fun n => GlobalTheory.Size.growthSize V N (ψ n - f)) Filter.atTop (nhds 0) → IsCuspFun V f := by
  first | exact @GlobalTheory.CuspLimit.isCuspFun_of_tendsto | exact GlobalTheory.CuspLimit.isCuspFun_of_tendsto | (intros; apply GlobalTheory.CuspLimit.isCuspFun_of_tendsto <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionTrivialOfConjugatePlaceSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionTrivialOfConjugatePlaceSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjPlaceRedGen


set_option maxHeartbeats 1000000 in
theorem redFn_eq_one_of_conj : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank), IsSelfDualC V L → ∀ β : GL (Fin V.rank) (Lev.EAf D), Formalism.L2.DIV.IsFrame β L → ∀ k : GA D V, Lev.finE V k ∈ Formalism.L2.DIV.St β → ∀ (PP PP' : Formalism.L2.DIV.Pl D.host.E), Formalism.IndefR.Lev.IsConjPl PP' PP → Formalism.L2.DIV.redFn β PP' (Lev.finE V k) = 1 → Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  intro D V L hsd β hβ k hk PP PP' hc h1
  obtain ⟨m, s, s', hs, hd⟩ := GlobalTheory.LatVacDual.dualFamily D V L hsd
  obtain ⟨G, hG⟩ := GlobalTheory.FrameGram.exists_unit_adelic star (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (fun _ => GlobalTheory.LevSplit.sigR_int) (fun _ => rfl) V.gram β _ hβ (fun y hy => (hsd.2 y).1 hy) s s' hs hd
  obtain ⟨h, hh⟩ := hk
  have hU : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype h * β⁻¹ ∈
      Formalism.UG.UJ (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
        (V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) := by
    have e : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype h * β⁻¹ = Lev.finE V k := hh
    rw [e]
    exact GlobalTheory.LevSplit.finE_mem_UA V k
  have key := GlobalTheory.FrameMove.conj_gram_sub (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (Formalism.L2.Herm.intAf D.host.F D.host.E) _ β G h hG hU
  rw [← hh, Formalism.L2.DIV.redFn_frGL] at h1 ⊢
  have h1' : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP') h⁻¹ = 1 := by rw [map_inv, h1, inv_one]
  have h2 : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) (G * h * G⁻¹) = 1 := by
    apply Units.ext
    ext i j
    have hz : Formalism.L2.DIV.resS D.host.F PP' ((h⁻¹).val j i) = if j = i then 1 else 0 := by
      have e : ((Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP') h⁻¹ : GL (Fin V.rank) (Formalism.L2.DIV.kP PP')) : Matrix _ _ (Formalism.L2.DIV.kP PP')) j i =
          Formalism.L2.DIV.resS D.host.F PP' ((h⁻¹).val j i) := rfl
      rw [← e, h1', Units.val_one, Matrix.one_apply]
    have h0 := GlobalTheory.ConjPlaceRed.resS_conj_ite D.sp.cm.sig PP' PP hc _ _ (key i j) (j = i) hz
    refine h0.trans ?_
    rw [Units.val_one, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  rw [map_mul, map_mul, map_inv] at h2
  exact _root_.conj_eq_one_iff.1 h2

end GlobalTheory.ConjPlaceRedGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionTrivialOfConjugatePlaceSelfDualStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reductionTrivial_of_conjugatePlace_selfDual : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank), IsSelfDualC V L → ∀ β : GL (Fin V.rank) (Lev.EAf D), Formalism.L2.DIV.IsFrame β L → ∀ k : GA D V, Lev.finE V k ∈ Formalism.L2.DIV.St β → ∀ (PP PP' : Formalism.L2.DIV.Pl D.host.E), Formalism.IndefR.Lev.IsConjPl PP' PP → Formalism.L2.DIV.redFn β PP' (Lev.finE V k) = 1 → Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  first | exact @GlobalTheory.ConjPlaceRedGen.redFn_eq_one_of_conj | exact GlobalTheory.ConjPlaceRedGen.redFn_eq_one_of_conj | (intros; apply GlobalTheory.ConjPlaceRedGen.redFn_eq_one_of_conj <;> assumption)
end
end

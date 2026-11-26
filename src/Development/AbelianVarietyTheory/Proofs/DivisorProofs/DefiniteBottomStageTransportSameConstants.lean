module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualSkewIdealLatticeIsSelfDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetOneMulBlockUnitaryDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilDatumSignedHomPairTransportIsometries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurableLevelIndicatorCoefficientTestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianGrowthConjTorsionTranslatesVacuum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaAtIdempotentHermitianHomIsometryTransport
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.MixModel
open scoped TensorProduct

namespace GlobalTheory.ThetaAtMove

variable {D : D7}

section Generic

variable {S T S' T' : HSp D}

private def rd (φ : WO S T ≃+ WO S' T') : (WO S T → ℂ) ≃ₗ[ℂ] (WO S' T' → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ φ.symm.toEquiv

private theorem rd_apply (φ : WO S T ≃+ WO S' T') (f : WO S T → ℂ) (w : WO S' T') : rd φ f w = f (φ.symm w) := rfl

private theorem rd_symm_apply (φ : WO S T ≃+ WO S' T') (g : WO S' T' → ℂ) (t : WO S T) : (rd φ).symm g t = g (φ t) := rfl

private theorem rd_symm_rd (φ : WO S T ≃+ WO S' T') (g : WO S T → ℂ) : rd φ.symm (rd φ g) = g := by
  funext w; simp [rd_apply]

private theorem rd_rd_symm (φ : WO S T ≃+ WO S' T') (g : WO S' T' → ℂ) : rd φ (rd φ.symm g) = g := by
  funext w; simp [rd_apply]

private theorem heisO_move (ψ : AddChar (AF D.host.F) ℂ) (φ : WO S T ≃+ WO S' T')
    (hB : ∀ x y, symplO S' T' (φ x) (φ y) = symplO S T x y) (w₀ : WO S T) (f : WO S T → ℂ) :
    heisO ψ S' T' (φ w₀) (rd φ f) = rd φ (heisO ψ S T w₀ f) := by
  funext w
  simp only [heisO, rd_apply, symplOH, map_add (f := _), AddEquiv.symm_apply_apply]
  rw [← hB (φ.symm w) w₀, AddEquiv.apply_symm_apply]

private theorem placeModel_move (ψ : AddChar (AF D.host.F) ℂ) (e : AE D) (Λ : AddSubgroup (WO S T))
    (Λ' : AddSubgroup (WO S' T')) (c : ℂ) (f₀ : WO S T → ℂ) (φ : WO S T ≃+ WO S' T')
    (hB : ∀ x y, symplO S' T' (φ x) (φ y) = symplO S T x y) (hH : ∀ a x, IsHalf a (φ x) ↔ IsHalf a x)
    (hΛ : ∀ x, φ x ∈ Λ' ↔ x ∈ Λ) {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Tm) :
    IsPlaceModel ψ (symplO S' T') (heisO ψ S' T') e Λ' c (rd φ f₀)
      ((rd φ).toLinearMap ∘ₗ Tm ∘ₗ (rd φ).symm.toLinearMap) := by
  have hSB : ∀ Φ', IsSBHalf e Λ' Φ' → IsSBHalf e Λ ((rd φ).symm Φ') := by
    rintro Φ' ⟨h1, k, hk, h2, h3⟩
    refine ⟨fun t ht => (hH e t).1 (h1 _ ht), k, hk, fun u hu hue t => ?_, fun t ht => ?_⟩
    · simp only [rd_symm_apply, map_add (f := _), map_nsmul]
      exact h2 _ ((hΛ u).2 hu) ((hH e u).2 hue) _
    · have := h3 _ ht
      change k • φ t ∈ Λ' at this
      rw [← map_nsmul] at this
      exact (hΛ _).1 this
  refine ⟨fun Φ' hΦ x hx => ?_, fun Φ' hΦ y hy => ?_, ?_⟩
  · have e1 : (rd φ).symm (fun t => Φ' (t + x)) = fun t => (rd φ).symm Φ' (t + φ.symm x) := by
      funext t; simp only [rd_symm_apply, map_add (f := _), AddEquiv.apply_symm_apply]
    have hx' : IsHalf e (φ.symm x) := (hH e _).1 (by rwa [AddEquiv.apply_symm_apply])
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [e1, hT.trans _ (hSB Φ' hΦ) _ hx', ← heisO_move ψ φ hB, AddEquiv.apply_symm_apply]
  · have e1 : (rd φ).symm (fun t => ψ (symplO S' T' t y) * Φ' t) =
        fun t => ψ (symplO S T t (φ.symm y)) * (rd φ).symm Φ' t := by
      funext t; simp only [rd_symm_apply]; rw [← hB, AddEquiv.apply_symm_apply]
    have hy' : IsHalf (cA D e) (φ.symm y) := (hH _ _).1 (by rwa [AddEquiv.apply_symm_apply])
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [e1, hT.modul _ (hSB Φ' hΦ) _ hy', ← heisO_move ψ φ hB, AddEquiv.apply_symm_apply]
  · have e1 : (rd φ).symm (c • halfInd e Λ') = c • halfInd e Λ := by
      funext t
      simp only [rd_symm_apply, Pi.smul_apply, halfInd]
      congr 1
      have key := and_congr (hΛ t) (hH e t)
      by_cases h : t ∈ Λ ∧ IsHalf e t
      · simp [key.2 h, h]
      · have h' : ¬ (φ t ∈ Λ' ∧ IsHalf e (φ t)) := fun ht => h (key.1 ht)
        simp [h', h]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [e1, hT.vac]

private theorem thetaAt_move (ψ : AddChar (AF D.host.F) ℂ) (e : AE D) (Λ : AddSubgroup (WO S T))
    (Λ' : AddSubgroup (WO S' T')) (c : ℂ) (φ : WO S T ≃+ WO S' T')
    (hB : ∀ x y, symplO S' T' (φ x) (φ y) = symplO S T x y) (hH : ∀ a x, IsHalf a (φ x) ↔ IsHalf a x)
    (hΛ : ∀ x, φ x ∈ Λ' ↔ x ∈ Λ) (f₀ Φ f : WO S T → ℂ)
    (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f) :
    IsThetaAt ψ (symplO S' T') (heisO ψ S' T') e Λ' c (rd φ f₀) (rd φ Φ) (rd φ f) := by
  have hB' : ∀ x y, symplO S T (φ.symm x) (φ.symm y) = symplO S' T' x y := fun x y => by
    rw [← hB, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have hH' : ∀ a x, IsHalf a (φ.symm x) ↔ IsHalf a x := fun a x => by
    rw [← hH, AddEquiv.apply_symm_apply]
  have hΛ' : ∀ x, φ.symm x ∈ Λ ↔ x ∈ Λ' := fun x => by
    rw [← hΛ, AddEquiv.apply_symm_apply]
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := h
  refine ⟨⟨_, placeModel_move ψ e Λ Λ' c f₀ φ hB hH hΛ hTm⟩, fun Tn hTn => ?_⟩
  have h2 := placeModel_move ψ e Λ' Λ c (rd φ f₀) φ.symm hB' hH' hΛ' hTn
  rw [rd_symm_rd] at h2
  have h3 := hall _ h2
  rw [h3]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have e1 : (rd φ.symm).symm Φ = rd φ Φ := rfl
  rw [e1, rd_rd_symm]

end Generic

section Concrete

open GlobalTheory.Mem.Isom GlobalTheory.TriMove

variable {S S' T T' : HSp D}

private def sgnIso (ε : Bool) (I : IsoMat S S') : IsoMat (GlobalTheory.Grid.sgn ε S) (GlobalTheory.Grid.sgn ε S') where
  P := I.P
  Q := I.Q
  PQ := I.PQ
  QP := I.QP
  gram := by
    cases ε
    · exact I.gram
    · show Formalism.UG.cT _ I.P * (-S'.gram) * I.P = -S.gram
      rw [Matrix.mul_neg, Matrix.neg_mul, I.gram]

private theorem aP_eq_rat (I : IsoMat S S') : I.aP = rat I.P := rfl

private theorem aQ_eq (I : IsoMat S S') : I.aQ = rat I.Q := rfl

private theorem gram_mul_Q (I : IsoMat S S') : S.gram * I.Q = Matrix.conjTranspose I.P * S'.gram := by
  have h : Matrix.conjTranspose I.P * S'.gram * I.P = S.gram := I.gram
  rw [← h]
  simp only [Matrix.mul_assoc, I.PQ, Matrix.mul_one]

private theorem ginv_mul_Qh (I : IsoMat S S') : S'.gram⁻¹ * Matrix.conjTranspose I.Q = I.P * S.gram⁻¹ := by
  have h2 : S'.gram * I.P = Matrix.conjTranspose I.Q * S.gram := gram_mul_Q I.symm
  calc S'.gram⁻¹ * Matrix.conjTranspose I.Q = S'.gram⁻¹ * (Matrix.conjTranspose I.Q * S.gram) * S.gram⁻¹ := by
        simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_isUnit_det S), Matrix.mul_one]
    _ = S'.gram⁻¹ * (S'.gram * I.P) * S.gram⁻¹ := by rw [h2]
    _ = I.P * S.gram⁻¹ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gram_isUnit_det S'), Matrix.one_mul]

private theorem symplO_eq' (S T : HSp D) (x y : WO S T) :
    symplO S T x y = Algebra.trace (AF D.host.F) (AE D) (HMul.hMul (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T y) x).trace := by
  unfold symplO GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj hO
  congr 1
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, giA, gA, adj, rat, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

private theorem symplO_homMap (IS : IsoMat S S') (IT : IsoMat T T') (x y : WO S T) :
    symplO S' T' (homMap IS IT x) (homMap IS IT y) = symplO S T x y := by
  have hA : giA S' ⬝ adj IS.aQ = IS.aP ⬝ giA S := by
    rw [aQ_eq, aP_eq_rat, giA, giA, ← rat_conjTranspose, ← rat_mul, ← rat_mul, ginv_mul_Qh]
  have hB : adj IT.aP ⬝ gA T' ⬝ IT.aP = gA T := by
    rw [aP_eq_rat, gA, gA, ← rat_conjTranspose, ← rat_mul, ← rat_mul]
    congr 1
    exact IT.gram
  have hA' : ∀ {k : ℕ} (M : Mx D S.rank k), giA S' ⬝ (adj IS.aQ ⬝ M) = IS.aP ⬝ (giA S ⬝ M) := by
    intro k M; rw [← Matrix.mul_assoc, hA, Matrix.mul_assoc]
  have hB' : ∀ {k : ℕ} (M : Mx D T.rank k), adj IT.aP ⬝ (gA T' ⬝ (IT.aP ⬝ M)) = gA T ⬝ M := by
    intro k M; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hB]
  rw [symplO_eq', symplO_eq', homMap_apply, homMap_apply]
  congr 1
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj, Matrix.smul_mul, Matrix.trace_smul]
  congr 1
  rw [adj_mul, adj_mul]
  simp only [Matrix.mul_assoc, hA', hB']
  rw [Matrix.trace_mul_comm IS.aP]
  simp only [Matrix.mul_assoc, IS.aQ_aP, Matrix.mul_one]

private theorem isHalf_homMap (IS : IsoMat S S') (IT : IsoMat T T') (a : AE D) (x : WO S T) :
    IsHalf a (homMap IS IT x) ↔ IsHalf a x := by
  have key : ∀ {m n : ℕ} (u : Mx D m n), IsHalf a u ↔ a • u = u := fun u =>
    ⟨fun h => by ext i j; exact h i j, fun h i j => congrFun (congrFun h i) j⟩
  have e : a • homMap IS IT x = homMap IS IT (a • x) := by
    rw [homMap_apply, homMap_apply, Matrix.mul_smul, Matrix.smul_mul]
  rw [key, key, e, (homMap IS IT).injective.eq_iff]

private theorem latMove_symm (I : IsoMat S S') (L : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) :
    latMove I.symm (latMove I L) = L := by
  rw [latMove, latMove, ← Submodule.map_comp]
  refine (congrArg (fun g => Submodule.map g L) ?_).trans (Submodule.map_id L)
  apply LinearMap.ext
  intro v
  show Matrix.mulVec I.Q (Matrix.mulVec I.P v) = v
  rw [Matrix.mulVec_mulVec, I.QP, Matrix.one_mulVec]

private theorem homMap_symm_homMap (IS : IsoMat S S') (IT : IsoMat T T') (x : WO S T) :
    homMap IS.symm IT.symm (homMap IS IT x) = x :=
  (homMap IS IT).symm_apply_apply x

private theorem homMap_gen (IS : IsoMat S S') (IT : IsoMat T T') (x : AF D.host.F) (a : D.host.E)
    (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    homMap IS IT (Matrix.of fun i j => x ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      Matrix.of fun i j => x ⊗ₜ[D.host.F] (a * (Matrix.mulVec IT.P t) i * ∑ k, star ((Matrix.mulVec IS.P s) k) * S'.gram k j) := by
  have e : ∀ {U V : HSp D} (t : Fin V.rank → D.host.E) (s : Fin U.rank → D.host.E),
      (Matrix.of fun i j => x ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * U.gram k j) : WO U V) =
        GlobalTheory.AdjLatO.tensM x ((a • Matrix.vecMulVec t (star s)) * U.gram) := by
    intro U V t s
    ext i j
    simp only [GlobalTheory.AdjLatO.tensM, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [e, e, homMap_apply, aP_eq_rat, aQ_eq, GlobalTheory.AdjLatO.rat_mul_tensM, GlobalTheory.AdjLatO.tensM_mul_rat]
  congr 1
  simp only [Matrix.mul_assoc, gram_mul_Q IS]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

private theorem homMap_mem_latO (IS : IsoMat S S') (IT : IsoMat T T') (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (x : WO S T)
    (hx : x ∈ latO S T (LS : Set _) (LT : Set _) P) :
    homMap IS IT x ∈ latO S' T' (latMove IS LS : Set _) (latMove IT LT : Set _) P := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    apply AddSubgroup.subset_closure
    exact ⟨α, hα, hP, a, ha, Matrix.mulVec IS.P s, ⟨s, hs, rfl⟩, Matrix.mulVec IT.P t, ⟨t, ht, rfl⟩, homMap_gen IS IT _ a s t⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

private theorem homMap_mem_latO_iff (IS : IsoMat S S') (IT : IsoMat T T') (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (x : WO S T) :
    homMap IS IT x ∈ latO S' T' (latMove IS LS : Set _) (latMove IT LT : Set _) P ↔
      x ∈ latO S T (LS : Set _) (LT : Set _) P := by
  refine ⟨fun hx => ?_, homMap_mem_latO IS IT LS LT P x⟩
  have h := homMap_mem_latO IS.symm IT.symm _ _ P _ hx
  rwa [latMove_symm, latMove_symm, homMap_symm_homMap] at h

theorem _root_.GlobalTheory.T.thetaAtIdempotent_hermitianHomIsometry_transport : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (e : AE D) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ Φ f : WO S T → ℂ),
  IsThetaAt ψ (symplO (GlobalTheory.Grid.sgn ε S) T) (heisO ψ (GlobalTheory.Grid.sgn ε S) T) e (latO (GlobalTheory.Grid.sgn ε S) T LS LT fun _ => True) 1 f₀ Φ f →
  IsThetaAt ψ (symplO (GlobalTheory.Grid.sgn ε S') T') (heisO ψ (GlobalTheory.Grid.sgn ε S') T') e (latO (GlobalTheory.Grid.sgn ε S') T' (GlobalTheory.TriMove.latMove (S' := S') IS LS) (GlobalTheory.TriMove.latMove (S' := T') IT LT) fun _ => True) 1 (GlobalTheory.TriMove.trH (S := S) (S' := S') (T := T) (T' := T') IS IT f₀) (GlobalTheory.TriMove.trH (S := S) (S' := S') (T := T) (T' := T') IS IT Φ) (GlobalTheory.TriMove.trH (S := S) (S' := S') (T := T) (T' := T') IS IT f) := by
  intro D ψ ε S S' T T' IS IT e LS LT f₀ Φ f h
  exact thetaAt_move ψ e _ _ 1 (homMap (sgnIso ε IS) IT) (symplO_homMap _ _) (isHalf_homMap _ _)
    (homMap_mem_latO_iff (sgnIso ε IS) IT LS LT _) f₀ Φ f h

end Concrete

end GlobalTheory.ThetaAtMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairSecondMemberHalfIsometryMoved
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TriMove

open GlobalTheory.Mem.Isom
open Formalism.UG (cT cT_mul cT_one)

variable {D : D7}

private theorem gram_inv_cT {V V' : HSp D} (I : IsoMat V V') :
    HMul.hMul (V'.gram⁻¹) (cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q) = HMul.hMul I.P (V.gram⁻¹) := by
  set σ : D.host.E →+* D.host.E := ↑D.sp.cm.sig with hσ
  have hg : cT σ I.P * V'.gram * I.P = V.gram := I.gram
  have hg' : cT σ I.Q * V.gram * I.Q = V'.gram := I.symm.gram
  have hPQh : cT σ I.Q * cT σ I.P = 1 := by rw [← cT_mul, I.PQ, cT_one]
  have hQPh : cT σ I.P * cT σ I.Q = 1 := by rw [← cT_mul, I.QP, cT_one]
  by_cases hu : IsUnit V.gram.det
  · have hinv : V'.gram⁻¹ = I.P * V.gram⁻¹ * cT σ I.P := by
      refine Matrix.inv_eq_right_inv ?_
      rw [← hg']
      calc cT σ I.Q * V.gram * I.Q * (I.P * V.gram⁻¹ * cT σ I.P)
          = cT σ I.Q * (V.gram * (I.Q * I.P) * V.gram⁻¹) * cT σ I.P := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [I.QP, Matrix.mul_one, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, hPQh]
    show V'.gram⁻¹ * cT σ I.Q = I.P * V.gram⁻¹
    rw [hinv, Matrix.mul_assoc, hQPh, Matrix.mul_one]
  · have hu' : ¬ IsUnit V'.gram.det := by
      intro h'
      apply hu
      refine Matrix.isUnit_det_of_right_inverse (B := I.Q * V'.gram⁻¹ * cT σ I.Q) ?_
      rw [← hg]
      calc cT σ I.P * V'.gram * I.P * (I.Q * V'.gram⁻¹ * cT σ I.Q)
          = cT σ I.P * (V'.gram * (I.P * I.Q) * V'.gram⁻¹) * cT σ I.Q := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [I.PQ, Matrix.mul_one, Matrix.mul_nonsing_inv _ h', Matrix.mul_one, hQPh]
    show V'.gram⁻¹ * cT σ I.Q = I.P * V.gram⁻¹
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hu, Matrix.nonsing_inv_apply_not_isUnit _ hu', Matrix.zero_mul,
      Matrix.mul_zero]

private theorem cT_gram {V V' : HSp D} (I : IsoMat V V') :
    HMul.hMul (cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.P) V'.gram = HMul.hMul V.gram I.Q := by
  show cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.P * V'.gram = V.gram * I.Q
  rw [← I.gram, Matrix.mul_assoc _ I.P, I.PQ, Matrix.mul_one]

private theorem sandwich {R : Type} [CommRing R] {s s' t t' : ℕ} (aQ : Matrix (Fin s) (Fin s') R) (aP : Matrix (Fin s') (Fin s) R)
    (G' : Matrix (Fin s') (Fin s') R) (cQ : Matrix (Fin s') (Fin s) R) (G : Matrix (Fin s) (Fin s) R) (Y : Matrix (Fin s) (Fin t) R)
    (cP : Matrix (Fin t) (Fin t') R) (H' : Matrix (Fin t') (Fin t') R) (H : Matrix (Fin t) (Fin t) R)
    (tQ : Matrix (Fin t) (Fin t') R) (tP : Matrix (Fin t') (Fin t) R)
    (h1 : G' * cQ = aP * G) (h2 : cP * H' = H * tQ) (hs : aQ * aP = 1) (ht : tQ * tP = 1) :
    aQ * (G' * (cQ * (Y * cP)) * H') * tP = G * Y * H := by
  calc _ = aQ * (G' * cQ) * Y * (cP * H') * tP := by simp only [Matrix.mul_assoc]
    _ = (aQ * aP) * G * Y * H * (tQ * tP) := by rw [h1, h2]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hs, ht, Matrix.one_mul, Matrix.mul_one]

private theorem adj_homMap {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T') (y : WO S T) :
    HMul.hMul (HMul.hMul IS.aQ (HMul.hMul (HMul.hMul ((S'.gram⁻¹).map (incA D))
      (((homMap IS IT y : Matrix (Fin T'.rank) (Fin S'.rank) (AE D)).map (cA D)).transpose)) (T'.gram.map (incA D)))) IT.aP
      = HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D)) (((y : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose))
          (T.gram.map (incA D)) := by
  set σ : D.host.E →+* D.host.E := ↑D.sp.cm.sig with hσ
  have hc : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E), (M.map (incA D)).map (cA D) = (M.map σ).map (incA D) := by
    intro m n M; ext i j; exact (rfl : cA D (incA D (M i j)) = incA D (σ (M i j)))
  have h1 : HMul.hMul ((S'.gram⁻¹).map (incA D)) ((IS.aQ.map (cA D)).transpose) = HMul.hMul IS.aP ((S.gram⁻¹).map (incA D)) := by
    rewrite [IsoMat.aQ, hc, ← Matrix.transpose_map, ← Matrix.map_mul, IsoMat.aP, ← Matrix.map_mul]
    exact congrArg (Matrix.map · (incA D)) (gram_inv_cT IS)
  have h2 : HMul.hMul ((IT.aP.map (cA D)).transpose) (T'.gram.map (incA D)) = HMul.hMul (T.gram.map (incA D)) IT.aQ := by
    rewrite [IsoMat.aP, hc, ← Matrix.transpose_map, ← Matrix.map_mul, IsoMat.aQ, ← Matrix.map_mul]
    exact congrArg (Matrix.map · (incA D)) (cT_gram IT)
  have hy : (((homMap IS IT y : Matrix (Fin T'.rank) (Fin S'.rank) (AE D)).map (cA D)).transpose) =
      HMul.hMul ((IS.aQ.map (cA D)).transpose) (HMul.hMul (((y : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose) ((IT.aP.map (cA D)).transpose)) := by
    rw [homMap_apply, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  rewrite [hy]
  exact sandwich _ _ _ _ _ _ _ _ _ _ _ h1 h2 IS.aQ_aP IT.aQ_aP

private theorem sandwich2 {R : Type} [CommRing R] {s s' t t' : ℕ} (ri : Matrix (Fin s') (Fin s) R) (bi : Matrix (Fin s) (Fin s) R)
    (fq : Matrix (Fin s) (Fin s') R) (N' : Matrix (Fin s') (Fin t') R) (fp : Matrix (Fin t') (Fin t) R)
    (b : Matrix (Fin t) (Fin t) R) (rx : Matrix (Fin t) (Fin t') R) (N : Matrix (Fin s) (Fin t) R) (h : fq * N' * fp = N) :
    ri * bi * fq * N' * (fp * b * rx) = ri * (bi * N * b) * rx := by
  rw [← h]; simp only [Matrix.mul_assoc]

private theorem fQ_eq {V V' : HSp D} (I : IsoMat V V') : fQ I = I.aQ.map (toEAf D) := by
  ext i j; rfl

private theorem fP_eq {V V' : HSp D} (I : IsoMat V V') : fP I = I.aP.map (toEAf D) := by
  ext i j; rfl

private theorem frMapAdj_homMap {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T') (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) (y : WO S T) :
    frMapAdj S' T' (betaMove IS βS) (betaMove IT βT) (homMap IS IT y) =
      HMul.hMul (HMul.hMul (rdi (K := Lev.EAf D) IS.rank_eq) (frMapAdj S T βS βT y)) (rdx (K := Lev.EAf D) IT.rank_eq) := by
  have hk := congrArg (Matrix.map · (toEAf D)) (adj_homMap IS IT y)
  rewrite [Matrix.map_mul, Matrix.map_mul, ← fQ_eq, ← fP_eq] at hk
  exact sandwich2 (rdi (K := Lev.EAf D) IS.rank_eq) (βS⁻¹).val (fQ IS) _ (fP IT) βT.val (rdx (K := Lev.EAf D) IT.rank_eq) _ hk

private theorem rdi_mul_mul_rdx {K : Type} [CommRing K] {m m' n n' : ℕ} (h1 : m = m') (h2 : n = n') (N : Matrix (Fin m) (Fin n) K) :
    HMul.hMul (HMul.hMul (rdi (K := K) h1) N) (rdx (K := K) h2) = N.submatrix (finCongr h1).symm (finCongr h2).symm := by
  subst h1 h2
  ext i j
  simp [rdi, rdx, Matrix.one_apply]

private theorem dualCoord_homMap {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T') (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) (y : WO S T) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord S' T' (betaMove IS βS) (betaMove IT βT) (homMap IS IT y) =
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord S T βS βT y).submatrix (finCongr IS.rank_eq).symm (finCongr IT.rank_eq).symm := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord
  rw [frMapAdj_homMap, rdi_mul_mul_rdx]
  rfl

private theorem isHalf_homMap {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T') (c : AE D) (y : WO S T) :
    IsHalf c (homMap IS IT y) ↔ IsHalf c y := by
  have hs : ∀ {m n : ℕ} (u : Mx D m n), IsHalf c u ↔ c • u = u := fun u =>
    ⟨fun h => Matrix.ext fun i j => (h i j : _), fun h i j => (congrFun (congrFun h i) j : _)⟩
  rw [hs, hs]
  have hm : c • homMap IS IT y = homMap IS IT (c • y) := by
    rw [homMap_apply, homMap_apply, Matrix.mul_smul, Matrix.smul_mul]
  rw [hm, (homMap IS IT).injective.eq_iff]

private theorem read_cond {m m' n n' : ℕ} (h1 : m = m') (h2 : n = n') (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E))
    (a : ℕ) (N : Matrix (Fin m) (Fin n) (Lev.EAf D)) :
    ((Formalism.IndefR.Datum.IsIntM (N.submatrix (finCongr h1).symm (finCongr h2).symm) ∧
        ∀ i j, j.1 < a → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (N.submatrix (finCongr h1).symm (finCongr h2).symm i j)) ↔
      (Formalism.IndefR.Datum.IsIntM N ∧ ∀ i j, j.1 < a → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (N i j))) ∧
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν e (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.rightBlock a (N.submatrix (finCongr h1).symm (finCongr h2).symm)) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν e (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.rightBlock a N) := by
  subst h1 h2
  have e0 : N.submatrix (finCongr (rfl : m = m)).symm (finCongr (rfl : n = n)).symm = N := by
    ext i j; rfl
  rw [e0]
  exact ⟨Iff.rfl, rfl⟩

theorem _root_.GlobalTheory.T.standardPairSecondMemberHalf_isometry_moved : ∀ {D : D7} {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (a : ℕ) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)),
  GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a S' T' (GlobalTheory.TriMove.betaMove IS βS) (GlobalTheory.TriMove.betaMove IT βT) = GlobalTheory.TriMove.trH IS IT (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a S T βS βT) := by
  intro D S S' T T' IS IT ν e I a βS βT
  funext w
  obtain ⟨y, rfl⟩ : ∃ y, w = homMap IS IT y := ⟨(homMap IS IT).symm w, ((homMap IS IT).apply_symm_apply w).symm⟩
  have hy : GlobalTheory.TriMove.trH IS IT (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a S T βS βT) (homMap IS IT y) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a S T βS βT y := by
    show GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a S T βS βT ((homMap IS IT).symm (homMap IS IT y)) = _
    rw [(homMap IS IT).symm_apply_apply]
  rw [hy]
  obtain ⟨h1, h2⟩ := read_cond IS.rank_eq IT.rank_eq ν e I a (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord S T βS βT y)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd
  split_ifs with hA hB hB
  · rw [dualCoord_homMap, h2]
  · exfalso; apply hB; rw [isHalf_homMap, dualCoord_homMap, h1] at hA; exact hA
  · exfalso; apply hA; rw [isHalf_homMap, dualCoord_homMap, h1]; exact hB
  · rfl

end GlobalTheory.TriMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarFundamentalDomainMapIsometryConj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.haar_fundamentalDomain_map_isometry_conj : ∀ {D : D7} {S S' : HSp D} (I : GlobalTheory.Mem.Isom.IsoMat S S') (m : MeasureTheory.Measure (GA D S)) (fd : Set (GA D S)),
  m.IsHaarMeasure ∧ MeasureTheory.IsFundamentalDomain (GQ S) fd m →
  (m.map I.kap).IsHaarMeasure ∧ MeasureTheory.IsFundamentalDomain (GQ S') (I.kap.symm ⁻¹' fd) (m.map I.kap) := by
  intro D S S' I m fd ⟨h1, h2⟩
  haveI : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : IsTopologicalGroup (GA D S') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  haveI : BorelSpace (GA D S') := ⟨rfl⟩
  refine ⟨I.kap.isHaarMeasure_map m I.continuous_kap I.continuous_kap_symm, ?_⟩
  have hm : Measurable I.kap := I.continuous_kap.measurable
  have hm' : Measurable I.kap.symm := I.continuous_kap_symm.measurable
  have hq : MeasureTheory.Measure.QuasiMeasurePreserving I.kap.symm (m.map I.kap) m := by
    refine ⟨hm'.aemeasurable, ?_⟩
    rw [MeasureTheory.Measure.map_map hm' hm]
    have : (I.kap.symm : GA D S' → GA D S) ∘ I.kap = id := funext fun x => I.kap.symm_apply_apply x
    rw [this, MeasureTheory.Measure.map_id]
  let e : GQ S ≃ GQ S' :=
    { toFun := fun γ => ⟨I.kap γ, I.kap_mem_GQ γ.2⟩
      invFun := fun γ => ⟨I.kap.symm γ, I.symm.kap_mem_GQ γ.2⟩
      left_inv := fun γ => Subtype.ext (I.kap.symm_apply_apply _)
      right_inv := fun γ => Subtype.ext (I.kap.apply_symm_apply _) }
  refine h2.preimage_of_equiv hq (e := e) e.bijective fun γ x => ?_
  show I.kap.symm (I.kap γ * x) = (γ : GA D S) * I.kap.symm x
  rw [map_mul, MulEquiv.symm_apply_apply]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOrientedVacuumIsometryMovedLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOrientedVacuumIsometryMovedLattices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Matrix GlobalTheory.Mem.Isom GlobalTheory.TriMove
open Formalism.UG (cT cT_mul cT_one)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.VacMove

variable {D : D7} {S S' T T' : HSp D}

theorem gramInv_conj (I : IsoMat S S') :
    I.Q * S'.gram⁻¹ * cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q = S.gram⁻¹ := by
  have hu : IsUnit S'.gram.det := (GlobalTheory.SmoothAutCheck.gram_det_ne S').isUnit
  have h : cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q * S.gram * I.Q = S'.gram := I.symm.gram
  refine (Matrix.inv_eq_left_inv ?_).symm
  calc _ = I.Q * (S'.gram⁻¹ * (cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q * S.gram * I.Q)) * I.P := by
        simp only [Matrix.mul_assoc, I.QP, Matrix.mul_one]
    _ = 1 := by rw [h, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, I.QP]

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (HMul.hMul ((S.gram⁻¹).map (incA D))
      (HMul.hMul (HMul.hMul (cT (cA D) y) (T.gram.map (incA D))) x)) := by
  unfold hO
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun b _ => sum_form (cA D) (T.gram.map (incA D)) x y (incA D (S.gram⁻¹ a b)) a b

theorem trace_conj {A : Type} [CommRing A] {m n k l : ℕ} (s : A →+* A) {H : Matrix (Fin n) (Fin n) A} {H' : Matrix (Fin m) (Fin m) A}
    {Q : Matrix (Fin n) (Fin m) A} (hQ : Q * H' * cT s Q = H) {J : Matrix (Fin k) (Fin k) A} {J' : Matrix (Fin l) (Fin l) A}
    {P : Matrix (Fin l) (Fin k) A} (hP : cT s P * J' * P = J) (x y : Matrix (Fin k) (Fin n) A) :
    Matrix.trace (H' * (cT s (P * y * Q) * J' * (P * x * Q))) = Matrix.trace (H * (cT s y * J * x)) := by
  rw [← hQ, ← hP]
  calc _ = Matrix.trace ((H' * cT s Q * (cT s y * (cT s P * J' * P) * x)) * Q) := by
        simp only [cT_mul, Matrix.mul_assoc]
    _ = _ := by
        rw [Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]

theorem hO_homMap (IS : IsoMat S S') (IT : IsoMat T T') (x y : WO S T) :
    hO S' T' (homMap IS IT x) (homMap IS IT y) = hO S T x y := by
  rw [hO_eq_trace, hO_eq_trace]
  have e : cT (cA D) (IS.Q.map (incA D)) = (cT (D.sp.cm.sig : D.host.E →+* D.host.E) IS.Q).map (incA D) := by
    ext i j
    rfl
  have hQ : HMul.hMul (HMul.hMul IS.aQ ((S'.gram⁻¹).map (incA D))) (cT (cA D) IS.aQ) = (S.gram⁻¹).map (incA D) := by
    rw [← gramInv_conj IS, Matrix.map_mul, Matrix.map_mul, ← e]
    rfl
  exact trace_conj (cA D) hQ (map_gram (incA D) _ (cA D) (fun _ => rfl) IT.gram) x y

theorem symplOH_homMap (IS : IsoMat S S') (IT : IsoMat T T') (x y : WO S T) :
    symplOH S' T' (homMap IS IT x) (homMap IS IT y) = symplOH S T x y := by
  unfold symplOH symplO
  rw [hO_homMap]

theorem homMap_symm_apply (IS : IsoMat S S') (IT : IsoMat T T') (y : WO S' T') :
    (homMap IS IT).symm y = homMap IS.symm IT.symm y := rfl

theorem continuous_homMap (IS : IsoMat S S') (IT : IsoMat T T') : Continuous (homMap IS IT) := by
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem continuous_homMap_symm (IS : IsoMat S S') (IT : IsoMat T T') : Continuous (homMap IS IT).symm :=
  continuous_homMap IS.symm IT.symm

theorem homMap_ratW (IS : IsoMat S S') (IT : IsoMat T T') (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    homMap IS IT (ratW T S γ) = ratW T' S' (IT.P * γ * IS.Q) := by
  show HMul.hMul (HMul.hMul (IT.P.map (incA D)) (γ.map (incA D))) (IS.Q.map (incA D)) = (IT.P * γ * IS.Q).map (incA D)
  rw [Matrix.map_mul, Matrix.map_mul]

theorem homMap_mem_ratL (IS : IsoMat S S') (IT : IsoMat T T') {x : WO S T} (hx : x ∈ ratL T S) : homMap IS IT x ∈ ratL T' S' := by
  obtain ⟨z, hz⟩ := hx
  have h2 : ratW T S z = x := hz
  rw [← h2, homMap_ratW]
  exact ⟨_, rfl⟩

theorem map_homMap_zero (IS : IsoMat S S') (IT : IsoMat T T') {B : Type} [CommRing B] (ρ : AE D →+* B) {w : WO S T}
    (h : w.map ρ = 0) : (homMap IS IT w).map ρ = 0 := by
  rw [homMap_apply, Matrix.map_mul, Matrix.map_mul, h, Matrix.mul_zero, Matrix.zero_mul]

theorem heisO_trH (IS : IsoMat S S') (IT : IsoMat T T') (ψ : AddChar (AF D.host.F) ℂ) (u : WO S T) (f : WO S T → ℂ) :
    heisO ψ S' T' (homMap IS IT u) (trH IS IT f) = trH IS IT (heisO ψ S T u f) := by
  funext w
  obtain ⟨w, rfl⟩ := (homMap IS IT).surjective w
  simp only [heisO, trH, ← map_add (f := _), AddEquiv.symm_apply_apply, symplOH_homMap]

theorem isThetaFunO_trH (IS : IsoMat S S') (IT : IsoMat T T') {ψ : AddChar (AF D.host.F) ℂ} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S' T' (trH IS IT f) := by
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp (continuous_homMap_symm IS IT), fun k L hL h0 w => ?_⟩
  · obtain ⟨w, rfl⟩ := (homMap IS IT).surjective w
    have e : ratW T' S' γ = homMap IS IT (ratW T S (IT.Q * γ * IS.P)) := by
      have := homMap_ratW IS.symm IT.symm γ
      rw [← homMap_symm_apply] at this
      exact ((homMap IS IT).symm_apply_eq.1 this)
    rw [e, ← map_add (f := _), symplOH_homMap]
    simp only [trH, AddEquiv.symm_apply_apply]
    exact hf.quasi _ _
  · obtain ⟨U, hU, e⟩ := hf.level
    refine ⟨U.comap (homMap IS IT).symm.toAddMonoidHom, hU.preimage (continuous_homMap_symm IS IT), fun u hu h0 => ?_⟩
    obtain ⟨u, rfl⟩ := (homMap IS IT).surjective u
    have hu' : u ∈ U := by simpa using hu
    have h1 : u.map (infPart D) = 0 := by
      have := map_homMap_zero IS.symm IT.symm _ h0
      rwa [← homMap_symm_apply, AddEquiv.symm_apply_apply] at this
    rw [heisO_trH, e u hu' h1]
  · have := hf.smooth k ((homMap IS IT).symm.toAddMonoidHom.comp L) ((continuous_homMap_symm IS IT).comp hL)
      (fun t => map_homMap_zero IS.symm IT.symm _ (h0 t)) ((homMap IS IT).symm w)
    simpa [trH] using this

theorem compAt_homMap (IS : IsoMat S S') (IT : IsoMat T T') {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (w : WO S T) :
    compAt θ τ (homMap IS IT w) = IT.pT τ * compAt θ τ w * IS.qT τ := by
  let ρ : AE D →+* ℂ := (θ τ).comp (infPart D)
  have hρ : ∀ x : D.host.E, ρ (incA D x) = tauE D τ x := fun x => by
    have := (hθ τ).1 x
    rw [← this]
    simp [ρ, incA, inclR, infPart]
  have e1 : IT.aP.map ρ = IT.pT τ := by ext i j; exact hρ _
  have e2 : IS.aQ.map ρ = IS.qT τ := by ext i j; exact hρ _
  show (homMap IS IT w).map ρ = IT.pT τ * w.map ρ * IS.qT τ
  rw [homMap_apply, Matrix.map_mul, Matrix.map_mul, e1, e2]

theorem lineAt_homMap (IS : IsoMat S S') (IT : IsoMat T T') {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    lineAt θ τ (IT.pT τ * z * IS.qT τ) t = homMap IS IT (lineAt θ τ z t) := by
  have hL : IsLineAt θ τ z (lineAt θ τ z) := Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ τ z)
  have hL0 : IsLineAt θ τ (IT.pT τ * z * IS.qT τ) (lineAt θ τ (IT.pT τ * z * IS.qT τ)) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ τ _)
  have hN : IsLineAt θ τ (IT.pT τ * z * IS.qT τ) ((homMap IS IT).toAddMonoidHom.comp (lineAt θ τ z)) := by
    refine ⟨(continuous_homMap IS IT).comp hL.1, fun t => map_homMap_zero IS IT _ (hL.2.1 t), fun t τ' => ?_⟩
    show compAt θ τ' (homMap IS IT (lineAt θ τ z t)) = _
    rw [compAt_homMap IS IT hθ, hL.2.2 t τ']
    split_ifs with c
    · subst c
      rw [Matrix.mul_smul, Matrix.smul_mul]
    · rw [Matrix.mul_zero, Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ hL0 hN]
  rfl

theorem dRho_trH (IS : IsoMat S S') (IT : IsoMat T T') (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ S' T') θ τ (IT.pT τ * z * IS.qT τ) (trH IS IT f) =
      trH IS IT (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
  funext x
  unfold Formalism.IndefR.Datum.dRho
  simp only [lineAt_homMap IS IT hθ, heisO_trH]
  rfl

theorem cplxO_move (IS : IsoMat S S') (IT : IsoMat T T') (τ : D.what₂.Tau) (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    cplxO (cartMove IS τ sS) (cartMove IT τ sT) (IT.pT τ * z * IS.qT τ) = IT.pT τ * cplxO sS sT z * IS.qT τ := by
  unfold cplxO cartMove
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc _ = IT.pT τ * sT * (IT.qT τ * IT.pT τ) * z * (IS.qT τ * IS.pT τ) * sS * IS.qT τ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [IT.qT_pT, IS.qT_pT]; simp only [Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]

theorem isFockVacAt_trH (IS : IsoMat S S') (IT : IsoMat T T') (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ)
    (τ : D.what₂.Tau) (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f) :
    IsFockVacAt (heisO ψ S' T') θ τ (cplxO (cartMove IS τ sS) (cartMove IT τ sT)) (trH IS IT f) := by
  intro z'
  obtain ⟨z, rfl⟩ : ∃ z : Matrix (Fin T.rank) (Fin S.rank) ℂ, z' = IT.pT τ * z * IS.qT τ := by
    refine ⟨IT.qT τ * z' * IS.pT τ, ?_⟩
    calc z' = (IT.pT τ * IT.qT τ) * z' * (IS.pT τ * IS.qT τ) := by rw [IT.pT_qT, IS.pT_qT, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  unfold annih
  rw [cplxO_move, dRho_trH IS IT ψ hθ, dRho_trH IS IT ψ hθ]
  funext x
  exact congrFun (hf z) ((homMap IS IT).symm x)

theorem tmul_conj {m n k l : ℕ} (β : AF D.host.F) (P : Matrix (Fin l) (Fin k) D.host.E) (M : Matrix (Fin k) (Fin n) D.host.E)
    (Q : Matrix (Fin n) (Fin m) D.host.E) :
    HMul.hMul (HMul.hMul (P.map (incA D)) (M.map fun e => (β ⊗ₜ[D.host.F] e : AE D))) (Q.map (incA D)) =
      (P * M * Q).map fun e => (β ⊗ₜ[D.host.F] e : AE D) := by
  have e : ∀ {a b : ℕ} (N : Matrix (Fin a) (Fin b) D.host.E), (N.map fun e => (β ⊗ₜ[D.host.F] e : AE D)) =
      (β ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • N.map (incA D) := by
    intro a b N
    ext i j
    simp [incA, inclR, Algebra.TensorProduct.tmul_mul_tmul]
  rw [e, e, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul, Matrix.map_mul]

theorem gen_conj {A : Type} [CommRing A] {m n k l : ℕ} (σ : A →+* A) {G : Matrix (Fin n) (Fin n) A} {G' : Matrix (Fin m) (Fin m) A}
    {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A} (h : cT σ P * G' = G * Q) (R : Matrix (Fin l) (Fin k) A) (a : A)
    (s : Fin n → A) (t : Fin k → A) :
    R * (Matrix.of fun i j => a * t i * ∑ c, σ (s c) * G c j) * Q =
      Matrix.of fun i j => a * (R *ᵥ t) i * ∑ c, σ ((P *ᵥ s) c) * G' c j := by
  have e : ∀ {p q : ℕ} (H : Matrix (Fin p) (Fin p) A) (s : Fin p → A) (t : Fin q → A),
      (Matrix.of fun i j => a * t i * ∑ c, σ (s c) * H c j) =
        a • (Matrix.replicateCol (Fin 1) t * (cT σ (Matrix.replicateCol (Fin 1) s) * H)) := by
    intro p q H s t
    ext i j
    simp [Matrix.mul_apply, cT, mul_assoc]
  rw [e, e, Matrix.replicateCol_mulVec, Matrix.replicateCol_mulVec, cT_mul, Matrix.mul_smul, Matrix.smul_mul]
  simp only [Matrix.mul_assoc, h]

theorem symm_mem_latO (IS : IsoMat S S') (IT : IsoMat T T') (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (p : HeightOneSpectrum (𝓞 D.host.F) → Prop) {u : WO S' T'}
    (hu : u ∈ latO S' T' (latMove IS LS) (latMove IT LT) p) : (homMap IS IT).symm u ∈ latO S T LS LT p := by
  have hle : latO S' T' (latMove IS LS) (latMove IT LT) p ≤ (latO S T LS LT p).comap (homMap IS IT).symm.toAddMonoidHom := by
    unfold latO
    rw [AddSubgroup.closure_le]
    rintro w ⟨α, hα, hP, a, ha, _, ⟨s, hs, rfl⟩, _, ⟨t, ht, rfl⟩, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩
    refine (homMap IS IT).symm_apply_eq.2 ?_
    have h : cT (D.sp.cm.sig : D.host.E →+* D.host.E) IS.P * S'.gram = S.gram * IS.Q := by
      rw [← IS.gram, Matrix.mul_assoc _ IS.P, IS.PQ, Matrix.mul_one]
    have h1 := tmul_conj (pairA D.host.F 0 α) IT.P
      (Matrix.of fun i j => a * t i * ∑ c, (D.sp.cm.sig : D.host.E →+* D.host.E) (s c) * S.gram c j) IS.Q
    rw [gen_conj _ h] at h1
    exact h1.symm
  exact hle hu

theorem isHalf_homMap (IS : IsoMat S S') (IT : IsoMat T T') {e : AE D} {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (homMap IS IT u) := by
  intro i j
  have h : e • u = u := by
    ext i j
    exact hu i j
  have h2 : e • homMap IS IT u = homMap IS IT u := by
    rw [homMap_apply, ← Matrix.smul_mul, ← Matrix.mul_smul, h]
  exact congrFun (congrFun h2 i) j

theorem isLatVac_trH (IS : IsoMat S S') (IT : IsoMat T T') (ψ : AddChar (AF D.host.F) ℂ)
    (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (p : HeightOneSpectrum (𝓞 D.host.F) → Prop) {f : WO S T → ℂ} (hf : IsLatVac (heisO ψ S T) (latO S T LS LT p) f) :
    IsLatVac (heisO ψ S' T') (latO S' T' (latMove IS LS) (latMove IT LT) p) (trH IS IT f) := by
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have h := symm_mem_latO IS IT LS LT p hu
    obtain ⟨u, rfl⟩ := (homMap IS IT).surjective u
    rw [AddEquiv.symm_apply_apply] at h
    rw [← map_nsmul, heisO_trH, hf.1 u h]
  · have h := symm_mem_latO IS IT LS LT p hu
    have h' := isHalf_homMap IS.symm IT.symm hh
    rw [← homMap_symm_apply] at h'
    obtain ⟨u, rfl⟩ := (homMap IS IT).surjective u
    rw [AddEquiv.symm_apply_apply] at h h'
    rw [heisO_trH, hf.2 e he u h h']

theorem exists_covolOne (IS : IsoMat S S') (IT : IsoMat T T') {μ : Measure (WO S' T')} {𝓕 : Set (WO S' T')}
    (h : IsCovolOne (ratL T' S') μ 𝓕) : ∃ (ν : Measure (WO S T)) (𝓖 : Set (WO S T)), IsCovolOne (ratL T S) ν 𝓖 ∧
      ∀ f : WO S T → ℂ, nrm2 μ 𝓕 (trH IS IT f) = nrm2 ν 𝓖 f := by
  obtain ⟨hμ, h𝓕, h1⟩ := h
  haveI hB : BorelSpace (WO S T) := ⟨rfl⟩
  haveI hB' : BorelSpace (WO S' T') := ⟨rfl⟩
  have hc := continuous_homMap IS IT
  have hcs := continuous_homMap_symm IS IT
  let m : WO S T ≃ᵐ WO S' T' :=
    { toEquiv := (homMap IS IT).toEquiv
      measurable_toFun := hc.measurable
      measurable_invFun := hcs.measurable }
  have hmp : MeasurePreserving m (μ.map m.symm) μ :=
    (MeasurePreserving.symm m.symm ⟨m.symm.measurable, rfl⟩)
  have hmp' : MeasurePreserving (homMap IS IT) (μ.map (homMap IS IT).symm) μ := hmp
  refine ⟨μ.map (homMap IS IT).symm, homMap IS IT ⁻¹' 𝓕,
    ⟨AddEquiv.isAddHaarMeasure_map μ (homMap IS IT).symm hcs (by simpa using hc), ?_, ?_⟩, fun f => ?_⟩
  · let g : ratL T' S' → ratL T S := fun y => ⟨(homMap IS IT).symm y, homMap_mem_ratL IS.symm IT.symm y.2⟩
    have hg : Function.Bijective g := by
      constructor
      · intro a b hab
        exact Subtype.ext ((homMap IS IT).symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨homMap IS IT x, homMap_mem_ratL IS IT x.2⟩, Subtype.ext (by simp [g])⟩
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hg ?_
    intro y x
    simp [g, AddSubgroup.vadd_def]
  · exact (hmp'.measure_preimage_emb m.measurableEmbedding 𝓕).trans h1
  · have := hmp'.setIntegral_preimage_emb m.measurableEmbedding (fun b => ‖trH IS IT f b‖ ^ 2) 𝓕
    unfold nrm2
    rw [← this]
    simp only [trH, AddEquiv.symm_apply_apply]

theorem isVacO_trH (IS : IsoMat S S') (IT : IsoMat T T') (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    {f : WO S T → ℂ} (hf : IsVacO ψ θ S T sS sT LS LT f) :
    IsVacO ψ θ S' T' (fun τ => cartMove IS τ (sS τ)) (fun τ => cartMove IT τ (sT τ)) (latMove IS LS) (latMove IT LT)
      (trH IS IT f) := by
  obtain ⟨hψ, hv⟩ := hf
  refine ⟨hψ, hv.inf, isThetaFunO_trH IS IT hv.theta, isLatVac_trH IS IT ψ LS LT _ hv.lat,
    fun τ => isFockVacAt_trH IS IT ψ hv.inf τ _ _ (hv.fock τ), ?_, fun p hp => ?_⟩
  · obtain ⟨p, hp⟩ := hv.norm.1
    obtain ⟨ν, 𝓖, h, -⟩ := exists_covolOne IS.symm IT.symm hp
    exact ⟨(ν, 𝓖), h⟩
  · obtain ⟨ν, 𝓖, h, e⟩ := exists_covolOne IS IT hp
    exact (e f).trans (hv.norm.2 (ν, 𝓖) h)

def isoSgn (ε : Bool) (I : IsoMat S S') : IsoMat (GlobalTheory.Grid.sgn ε S) (GlobalTheory.Grid.sgn ε S') where
  P := I.P
  Q := I.Q
  PQ := I.PQ
  QP := I.QP
  gram := by
    cases ε
    · exact I.gram
    · show cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.P * (-S'.gram) * I.P = -S.gram
      rw [Matrix.mul_neg, Matrix.neg_mul, I.gram]

theorem sgnM_cartMove (ε : Bool) (I : IsoMat S S') (τ : D.what₂.Tau) (s : Matrix (Fin S.rank) (Fin S.rank) ℂ) :
    GlobalTheory.Grid.sgnM ε (cartMove I τ s) = cartMove I τ (GlobalTheory.Grid.sgnM ε s) := by
  cases ε
  · rfl
  · show -(I.pT τ * s * I.qT τ) = I.pT τ * (-s) * I.qT τ
    rw [Matrix.mul_neg, Matrix.neg_mul]

theorem isVacO_move : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (ε : Bool) {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f : WO S T → ℂ),
  IsVacO ψ θ (GlobalTheory.Grid.sgn ε S) T (fun τ => GlobalTheory.Grid.sgnM ε (sS τ)) sT LS LT f →
  IsVacO ψ θ (GlobalTheory.Grid.sgn ε S') T' (fun τ => GlobalTheory.Grid.sgnM ε (GlobalTheory.TriMove.cartMove (S' := S') IS τ (sS τ))) (fun τ => GlobalTheory.TriMove.cartMove (S' := T') IT τ (sT τ)) (GlobalTheory.TriMove.latMove (S' := S') IS LS) (GlobalTheory.TriMove.latMove (S' := T') IT LT) (GlobalTheory.TriMove.trH (S := S) (S' := S') (T := T) (T' := T') IS IT f) := by
  intro D ψ θ ε S S' T T' IS IT sS sT LS LT f hf
  simp only [sgnM_cartMove]
  exact isVacO_trH (isoSgn ε IS) IT ψ θ (fun τ => GlobalTheory.Grid.sgnM ε (sS τ)) sT LS LT hf

end GlobalTheory.VacMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOrientedVacuumIsometryMovedLatticesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOrientedVacuum_isometry_moved_lattices : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (ε : Bool) {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f : WO S T → ℂ),
  IsVacO ψ θ (GlobalTheory.Grid.sgn ε S) T (fun τ => GlobalTheory.Grid.sgnM ε (sS τ)) sT LS LT f →
  IsVacO ψ θ (GlobalTheory.Grid.sgn ε S') T' (fun τ => GlobalTheory.Grid.sgnM ε (GlobalTheory.TriMove.cartMove (S' := S') IS τ (sS τ))) (fun τ => GlobalTheory.TriMove.cartMove (S' := T') IT τ (sT τ)) (GlobalTheory.TriMove.latMove (S' := S') IS LS) (GlobalTheory.TriMove.latMove (S' := T') IT LT) (GlobalTheory.TriMove.trH (S := S) (S' := S') (T := T) (T' := T') IS IT f) := by
  first | exact @GlobalTheory.VacMove.isVacO_move | exact GlobalTheory.VacMove.isVacO_move | (intros; apply GlobalTheory.VacMove.isVacO_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomStageTransportSameConstants
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.TriMove in
theorem GlobalTheory.TriMove.transport_bottom : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (W : G.Weil) (i j : Fin D.R.m) {A A' WW B B' WW₁ : HSp D} (X : Tri T A A' WW) (Y : Tri T B B' WW₁),
  IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y →
  ∃ Y' : Tri T A A' WW, GlobalTheory.SqTower.IsStageC W i j 0 0 Y' ∧ ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → Y'.IsConst W.ψ W.θ c := by
  intro D T Lc sc G W i j A A' WW B B' WW₁ X Y hX hY
  obtain ⟨hp, hq, rX1, negRightMulLetterShift, nX1, nX2, nX3, isX⟩ := GlobalTheory.SqTower.IsBottomTri.isStageC hX
  obtain ⟨-, -, rY1, rY2, nY1, nY2, nY3, isY⟩ := hY
  have e1 : B.rank = A.rank := by omega
  have e2 : B'.rank = A'.rank := by omega
  have e3 : WW₁.rank = WW.rank := by rw [← isY.rank, ← isX.rank, e1, e2]
  obtain ⟨IA⟩ := GlobalTheory.T.exists_isometry_posDef_hermitian_same_rank e1 nY1 nX1
  obtain ⟨IA'⟩ := GlobalTheory.T.exists_isometry_posDef_hermitian_same_rank e2 nY2 nX2
  obtain ⟨IW⟩ := GlobalTheory.T.exists_isometry_posDef_hermitian_same_rank e3 nY3 nX3
  refine ⟨triMove IA IA' IW Y, ⟨hp, hq, rX1, negRightMulLetterShift, nX1, nX2, nX3, ?_⟩,
    fun c hc => GlobalTheory.T.isConst_seesawTriple_transport_isometries IA IA' IW Y W.ψ W.θ isY.isVac.2.inf c hc⟩
  exact
    { rank := isX.rank
      rigA := GlobalTheory.T.isometryMovedRigging_is IA _ isY.rigA
      rigA' := GlobalTheory.T.isometryMovedRigging_is IA' _ isY.rigA'
      rigW := GlobalTheory.T.isometryMovedRigging_is IW _ isY.rigW
      weil := fun t => GlobalTheory.T.isWeilDatumSignedHomPair_transport_isometries W.ψ true IA IW _ _ (Y.ω t) (isY.weil t)
      weil' := fun t => GlobalTheory.T.isWeilDatumSignedHomPair_transport_isometries W.ψ false IA' IW _ _ (Y.ω' t) (isY.weil' t)
      isVac := GlobalTheory.T.isOrientedVacuum_isometry_moved_lattices W.ψ W.θ true IA IW Y.rA.s Y.rW.s Y.rA.Λ Y.rW.Λ Y.vac isY.isVac
      isVac' := GlobalTheory.T.isOrientedVacuum_isometry_moved_lattices W.ψ W.θ false IA' IW Y.rA'.s Y.rW.s Y.rA'.Λ Y.rW.Λ Y.vac' isY.isVac'
      idem := isY.idem
      expo := isY.expo
      fst := fun t => by
        have h5 := GlobalTheory.T.thetaAtIdempotent_hermitianHomIsometry_transport W.ψ true IA IW (Y.e t) Y.rA.Λ Y.rW.Λ Y.vac _ (Y.f t) (isY.fst t)
        rw [← GlobalTheory.T.standardPairFirstMemberHalf_isometry_moved] at h5
        exact h5
      snd := fun t => by
        have h5 := GlobalTheory.T.thetaAtIdempotent_hermitianHomIsometry_transport W.ψ false IA' IW _ Y.rA'.Λ Y.rW.Λ Y.vac' _ (Y.f' t) (isY.snd t)
        rw [← GlobalTheory.T.standardPairSecondMemberHalf_isometry_moved, e1] at h5
        exact h5
      meas := GlobalTheory.T.haar_fundamentalDomain_map_isometry_conj IA Y.m Y.fd isY.meas
      meas' := GlobalTheory.T.haar_fundamentalDomain_map_isometry_conj IA' Y.m' Y.fd' isY.meas' }
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomStageTransportSameConstantsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottom_stage_transport_same_constants : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (W : G.Weil) (i j : Fin D.R.m) {A A' WW B B' WW₁ : HSp D} (X : Tri T A A' WW) (Y : Tri T B B' WW₁),
  IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y →
  ∃ Y' : Tri T A A' WW, GlobalTheory.SqTower.IsStageC W i j 0 0 Y' ∧ ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → Y'.IsConst W.ψ W.θ c := by
  first | exact @GlobalTheory.TriMove.transport_bottom | exact GlobalTheory.TriMove.transport_bottom | (intros; apply GlobalTheory.TriMove.transport_bottom <;> assumption)
end

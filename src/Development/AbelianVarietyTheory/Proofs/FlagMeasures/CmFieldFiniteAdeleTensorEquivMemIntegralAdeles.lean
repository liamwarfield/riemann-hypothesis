module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftExists
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldFiniteAdeleTensorEquivMemIntegralAdeles
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldFiniteAdeleTensorEquivMemIntegralAdeles
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

open IsDedekindDomain

namespace GlobalTheory.FixedConj

theorem comm_tensCastR_symm_mem_intAf {E : Type} [Field E] [NumberField E] {F₁ F₂ : Subfield E} (h : F₁ = F₂)
    (x : E ⊗[F₂] FiniteAdeleRing (𝓞 F₂) F₂)
    (hx : x ∈ Subring.closure ({x | ∃ y : 𝓞 E, x = (y : E) ⊗ₜ[F₂] (1 : FiniteAdeleRing (𝓞 F₂) F₂)} ∪
      {x | ∃ a : FiniteAdeleRing (𝓞 F₂) F₂, (∀ v, a v ∈ v.adicCompletionIntegers F₂) ∧ x = (1 : E) ⊗ₜ[F₂] a})) :
    (Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E).toRingEquiv
      ((GlobalTheory.StdFrame.tensCastR h).symm x) ∈ Formalism.L2.Herm.intAf (↥F₁) E := by
  subst h
  have hS : Subring.closure ({x | ∃ y : 𝓞 E, x = (y : E) ⊗ₜ[F₁] (1 : FiniteAdeleRing (𝓞 F₁) F₁)} ∪
      {x | ∃ a : FiniteAdeleRing (𝓞 F₁) F₁, (∀ v, a v ∈ v.adicCompletionIntegers F₁) ∧ x = (1 : E) ⊗ₜ[F₁] a}) ≤
      (Formalism.L2.Herm.intAf (↥F₁) E).comap
        (((GlobalTheory.StdFrame.tensCastR (rfl : F₁ = F₁)).symm.trans
          (Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E).toRingEquiv : _ ≃+* _) : _ →+* _) := by
    rw [Subring.closure_le]
    rintro z (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · show (Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E)
          ((Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E).symm ((y : E) ⊗ₜ[F₁] 1)) ∈ _
      rw [AlgEquiv.apply_symm_apply]
      exact Subring.subset_closure (Or.inl ⟨⟨(y : E), ⟨y, rfl⟩⟩, rfl⟩)
    · show (Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E)
          ((Algebra.TensorProduct.comm (↥F₁) (FiniteAdeleRing (𝓞 F₁) F₁) E).symm ((1 : E) ⊗ₜ[F₁] a)) ∈ _
      rw [AlgEquiv.apply_symm_apply]
      exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  exact hS hx

theorem adeleEquiv_mem_intAf : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (a : ReciprocityTheory.Aut.AL D.host.E),
    a ∈ ReciprocityTheory.Aut.ALint D.host.E → GlobalTheory.FixedConj.adeleEquiv D hF a ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E := by
  intro D hF a ha
  exact comm_tensCastR_symm_mem_intAf hF a ha

end GlobalTheory.FixedConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldFiniteAdeleTensorEquivMemIntegralAdelesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmFieldFiniteAdeleTensorEquiv_mem_integralAdeles : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (a : ReciprocityTheory.Aut.AL D.host.E), a ∈ ReciprocityTheory.Aut.ALint D.host.E → GlobalTheory.FixedConj.adeleEquiv D hF a ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E := by
  first | exact @GlobalTheory.FixedConj.adeleEquiv_mem_intAf | exact GlobalTheory.FixedConj.adeleEquiv_mem_intAf | (intros; apply GlobalTheory.FixedConj.adeleEquiv_mem_intAf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRectangularConjInstanceMatrixStandardPsi
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRectangularConjInstanceMatrixStandardPsi
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.FixedConjMat

theorem fmat_iota (D : D7) (x : Formalism.L2.Theta.GA D (D.sp.Y 0)) :
    (Formalism.L2.SG.InstExistsPf.instOf D).fmat ((Formalism.IndefR.RationalEmbedding.iota D x).2) =
      (Formalism.IndefR.Lev.finE (D.sp.Y 0) x).1 := by
  have hb := (Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D x)).2
  have e : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D x) = x :=
    (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply x
  rw [hb]
  erw [e]
  ext i j
  exact GlobalTheory.RedFrame.tauF_gen (Formalism.IndefR.RationalEmbedding.inst D) _

theorem finE_val_eq (D : D7) (V : HSp D) (g : Formalism.L2.Theta.GA D V) :
    (Formalism.IndefR.Lev.finE V g).1 = (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g).map (Formalism.IndefR.Lev.swapAE D) := rfl

theorem map_cast_swap (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) {m n : Type}
    (M : Matrix m n (ReciprocityTheory.Aut.AL D.host.E)) :
    (M.map (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm).map (Formalism.IndefR.Lev.swapAE D) =
      M.map (GlobalTheory.FixedConj.adeleEquiv D hF) := by
  ext i j
  rfl

theorem map_mul_eq_one {k l R S : Type} [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] [CommRing R]
    [CommRing S] (f : R →+* S) {A : Matrix k l R} {B : Matrix l k R} (h : A * B = 1) :
    A.map f * B.map f = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero f) (map_one f)]

theorem conj_map {k l R S : Type} [Fintype k] [Fintype l] [CommRing R] [CommRing S] (f : R →+* S)
    (T : Matrix k k S) (Ti : Matrix k k S) (B : Matrix k l R) (Y : Matrix l l R) (B' : Matrix l k R)
    (g : Matrix l l S) (hg : Y.map f = g) :
    T * (B * Y * B').map f * Ti = T * B.map f * g * (B'.map f * Ti) := by
  rw [Matrix.map_mul, Matrix.map_mul, hg]
  simp only [Matrix.mul_assoc]


set_option maxHeartbeats 1000000 in
theorem finE_conj_stdPsi (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (PY : RowPsi (Yc D 0) D.R.r)
    (t : Formalism.L2.Theta.GA D (Yc D 0)) (hP : StdPsi hF PY) :
    ∃ (U : Matrix (Fin (Yc D 0).rank) (Fin D.R.r) (Formalism.IndefR.Lev.EAf D))
      (U' : Matrix (Fin D.R.r) (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)), U * U' = 1 ∧ U' * U = 1 ∧
      ∀ y : Formalism.AUTREP.GAf D.host.E D.R.r, (Formalism.IndefR.Lev.finE (Yc D 0) (MulAut.conj t (PY.ψ y))).1 =
        HMul.hMul (HMul.hMul U (((y : GL (Fin D.R.r) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r)
          (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.FixedConj.adeleEquiv D hF))) U' := by
  obtain ⟨⟨β, β', h1, h2, hβ⟩, -⟩ := hP
  have hbb := map_mul_eq_one (Formalism.IndefR.Lev.swapAE D) h1
  have hbb' := map_mul_eq_one (Formalism.IndefR.Lev.swapAE D) h2
  refine ⟨HMul.hMul (Formalism.IndefR.Lev.finE (Yc D 0) t).1 (β.map (Formalism.IndefR.Lev.swapAE D)),
    HMul.hMul (β'.map (Formalism.IndefR.Lev.swapAE D)) ((Formalism.IndefR.Lev.finE (Yc D 0) t)⁻¹).1, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (β.map _), hbb, Matrix.one_mul, Units.mul_inv]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (((Formalism.IndefR.Lev.finE (Yc D 0) t)⁻¹).1), Units.inv_mul,
      Matrix.one_mul, hbb']
  · intro y
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]
    have e1 := finE_val_eq D (Yc D 0) (PY.ψ y)
    have e3 := e1.trans (congrArg (fun M => M.map (Formalism.IndefR.Lev.swapAE D)) (hβ y))
    rw [e3]
    exact conj_map _ _ _ _ _ _ _ (map_cast_swap D hF _)

theorem fmat_iota_conj_stdPsi : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (PY : RowPsi (Yc D 0) D.R.r) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)), StdPsi hF PY → ∃ (U : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin D.R.r) (Formalism.IndefR.Lev.EAf D)) (U' : Matrix (Fin D.R.r) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Formalism.IndefR.Lev.EAf D)), U * U' = 1 ∧ U' * U = 1 ∧ ∀ y : Formalism.AUTREP.GAf D.host.E D.R.r, (Formalism.L2.SG.InstExistsPf.instOf D).fmat ((Formalism.IndefR.RationalEmbedding.iota D (MulAut.conj t (PY.ψ y))).2) = U * ((y : GL (Fin D.R.r) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.FixedConj.adeleEquiv D hF) * U' := by
  intro D hF PY t hP
  obtain ⟨U, U', h1, h2, h3⟩ := finE_conj_stdPsi D hF PY t hP
  exact ⟨U, U', h1, h2, fun y => (fmat_iota D _).trans (h3 y)⟩

end GlobalTheory.FixedConjMat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRectangularConjInstanceMatrixStandardPsiStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rectangular_conj_instanceMatrix_standardPsi : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (PY : RowPsi (Yc D 0) D.R.r) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)), StdPsi hF PY → ∃ (U : Matrix (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Fin D.R.r) (Formalism.IndefR.Lev.EAf D)) (U' : Matrix (Fin D.R.r) (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) (Formalism.IndefR.Lev.EAf D)), U * U' = 1 ∧ U' * U = 1 ∧ ∀ y : Formalism.AUTREP.GAf D.host.E D.R.r, (Formalism.L2.SG.InstExistsPf.instOf D).fmat ((Formalism.IndefR.RationalEmbedding.iota D (MulAut.conj t (PY.ψ y))).2) = U * ((y : GL (Fin D.R.r) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin D.R.r) (Fin D.R.r) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.FixedConj.adeleEquiv D hF) * U' := by
  first | exact @GlobalTheory.FixedConjMat.fmat_iota_conj_stdPsi | exact GlobalTheory.FixedConjMat.fmat_iota_conj_stdPsi | (intros; apply GlobalTheory.FixedConjMat.fmat_iota_conj_stdPsi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ResidueCmFieldFiniteAdeleTensorEquivEqNatCast
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ResidueCmFieldFiniteAdeleTensorEquivEqNatCast
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.SplitRes

open IsDedekindDomain

section Cast

variable {E : Type} [Field E] [NumberField E]

theorem tensCastR_comm_symm_tmul_one {F₁ F₂ : Subfield E} (h : F₁ = F₂) (y : E) :
    GlobalTheory.StdFrame.tensCastR h ((Algebra.TensorProduct.comm F₁ (FiniteAdeleRing (𝓞 F₁) F₁) E).symm
      (y ⊗ₜ[F₁] (1 : FiniteAdeleRing (𝓞 F₁) F₁))) = y ⊗ₜ[F₂] (1 : FiniteAdeleRing (𝓞 F₂) F₂) := by
  subst h
  exact (Algebra.TensorProduct.comm F₁ (FiniteAdeleRing (𝓞 F₁) F₁) E).apply_symm_apply _

theorem tensCastR_comm_symm_one_tmul {F₁ F₂ : Subfield E} (h : F₁ = F₂) (c : FiniteAdeleRing (𝓞 F₁) F₁)
    (hc : ∀ v, c v ∈ v.adicCompletionIntegers F₁) :
    ∃ c' : FiniteAdeleRing (𝓞 F₂) F₂, (∀ v, c' v ∈ v.adicCompletionIntegers F₂) ∧
      GlobalTheory.StdFrame.tensCastR h ((Algebra.TensorProduct.comm F₁ (FiniteAdeleRing (𝓞 F₁) F₁) E).symm
        ((1 : E) ⊗ₜ[F₁] c)) = (1 : E) ⊗ₜ[F₂] c' := by
  subst h
  exact ⟨c, hc, (Algebra.TensorProduct.comm F₁ (FiniteAdeleRing (𝓞 F₁) F₁) E).apply_symm_apply _⟩

end Cast

def projE (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) :
    Formalism.IndefR.Lev.EAf D →+* s.v.adicCompletion (maximalRealSubfield D.host.E) :=
  s.proj.comp (GlobalTheory.FixedConj.adeleEquiv D hF).symm.toRingHom

theorem projE_apply (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (x : Formalism.IndefR.Lev.EAf D) :
    projE D hF s x = s.proj (GlobalTheory.StdFrame.tensCastR hF
      ((Algebra.TensorProduct.comm (↥D.host.F) (FiniteAdeleRing (𝓞 ↥D.host.F) ↥D.host.F) D.host.E).symm x)) := rfl

theorem projE_adeleEquiv (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (a : ReciprocityTheory.Aut.AL D.host.E) : projE D hF s (GlobalTheory.FixedConj.adeleEquiv D hF a) = s.proj a := by
  simp [projE]

theorem projE_tmul_one (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (y : D.host.E) : projE D hF s (y ⊗ₜ[↥D.host.F] (1 : Formalism.L2.Herm.Af ↥D.host.F)) = s.i y := by
  rw [projE_apply, tensCastR_comm_symm_tmul_one]
  simp [SplitPlace.proj, Algebra.TensorProduct.lift_tmul]

theorem projE_le_one (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (z : Formalism.IndefR.Lev.EAf D) (hz : z ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) : Valued.v (projE D hF s z) ≤ 1 := by
  have hle : Formalism.L2.Herm.intAf (↥D.host.F) D.host.E ≤
      (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring.comap (projE D hF s) := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨⟨_, y, rfl⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · show projE D hF s _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, projE_tmul_one]
      exact s.split_le_one y
    · show projE D hF s _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)
      obtain ⟨c', hc', e⟩ := tensCastR_comm_symm_one_tmul hF c hc
      rw [projE_apply, e]
      simp only [SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact hc' s.v
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hle hz)

theorem projE_lt_one (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (z : Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) (hz : z ∈ Formalism.L2.DIV.idS (↥D.host.F) s.w.asIdeal) :
    Valued.v (projE D hF s (z : Formalism.IndefR.Lev.EAf D)) < 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Formalism.L2.DIV.oToS_coe, projE_tmul_one]
    exact hy
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add (f := _)]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul c x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    calc Valued.v (projE D hF s (c : Formalism.IndefR.Lev.EAf D)) * Valued.v (projE D hF s (x : Formalism.IndefR.Lev.EAf D))
        ≤ 1 * Valued.v (projE D hF s (x : Formalism.IndefR.Lev.EAf D)) := by
          gcongr
          exact projE_le_one D hF s _ c.2
      _ < 1 := by rwa [one_mul]

theorem resS_adeleEquiv_eq_natCast : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a : ReciprocityTheory.Aut.AL D.host.E) (ha : GlobalTheory.FixedConj.adeleEquiv D hF a ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) (m : ℕ), a ∈ ReciprocityTheory.Aut.ALint D.host.E → Valued.v (s.proj a - (m : s.v.adicCompletion (maximalRealSubfield D.host.E))) < 1 → Formalism.L2.DIV.resS (↥D.host.F) s.w ⟨_, ha⟩ = (m : Formalism.L2.DIV.kP s.w) := by
  intro D hF s a ha m _hA hm
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (Formalism.L2.DIV.resS (↥D.host.F) s.w ⟨_, ha⟩)
  have e1 : Formalism.L2.DIV.cmpS (↥D.host.F) s.w.asIdeal (Formalism.L2.DIV.resS (↥D.host.F) s.w ⟨_, ha⟩) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS (↥D.host.F) s.w.asIdeal) ⟨_, ha⟩ :=
    (RingEquiv.ofBijective (Formalism.L2.DIV.cmpS (↥D.host.F) s.w.asIdeal)
      (Formalism.L2.DIV.cmpS_bij (F := ↥D.host.F) s.w.asIdeal s.w.ne_bot)).apply_symm_apply _
  have e2 : Formalism.L2.DIV.cmpS (↥D.host.F) s.w.asIdeal (Ideal.Quotient.mk s.w.asIdeal b) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS (↥D.host.F) s.w.asIdeal) (Formalism.L2.DIV.oToS (↥D.host.F) D.host.E b) :=
    Ideal.quotientMap_mk
  have hmem : (⟨_, ha⟩ : Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) - Formalism.L2.DIV.oToS (↥D.host.F) D.host.E b ∈
      Formalism.L2.DIV.idS (↥D.host.F) s.w.asIdeal := by
    refine Ideal.Quotient.eq.1 ?_
    exact e1.symm.trans ((congrArg (Formalism.L2.DIV.cmpS (↥D.host.F) s.w.asIdeal) hb.symm).trans e2)
  have h1 : Valued.v (s.proj a - s.i (algebraMap (𝓞 D.host.E) D.host.E b)) < 1 := by
    have := projE_lt_one D hF s _ hmem
    rwa [AddSubgroupClass.coe_sub, map_sub, Formalism.L2.DIV.oToS_coe, projE_tmul_one, projE_adeleEquiv] at this
  have h2 : b - (m : 𝓞 D.host.E) ∈ s.w.asIdeal := by
    show Valued.v (s.i ((b - (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E)) < 1
    have e : s.i ((b - (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) =
        (s.proj a - (m : s.v.adicCompletion (maximalRealSubfield D.host.E))) -
          (s.proj a - s.i (algebraMap (𝓞 D.host.E) D.host.E b)) := by
      rw [RingOfIntegers.coe_eq_algebraMap, map_sub, map_sub, map_natCast, map_natCast]
      ring
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hm h1)
  rw [← hb, ← map_natCast (Ideal.Quotient.mk s.w.asIdeal) m, Ideal.Quotient.eq]
  exact h2

end GlobalTheory.SplitRes

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ResidueCmFieldFiniteAdeleTensorEquivEqNatCastStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_cmFieldFiniteAdeleTensorEquiv_eq_natCast : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a : ReciprocityTheory.Aut.AL D.host.E) (ha : GlobalTheory.FixedConj.adeleEquiv D hF a ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) (m : ℕ), a ∈ ReciprocityTheory.Aut.ALint D.host.E → Valued.v (s.proj a - (m : s.v.adicCompletion (maximalRealSubfield D.host.E))) < 1 → Formalism.L2.DIV.resS (↥D.host.F) s.w ⟨_, ha⟩ = (m : Formalism.L2.DIV.kP s.w) := by
  first | exact @GlobalTheory.SplitRes.resS_adeleEquiv_eq_natCast | exact GlobalTheory.SplitRes.resS_adeleEquiv_eq_natCast | (intros; apply GlobalTheory.SplitRes.resS_adeleEquiv_eq_natCast <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaximalCompactOfTrivialOffSplitPair
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaximalCompactOfTrivialOffSplitPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.SplitPairK

open Matrix Formalism.MainNotions.S GlobalTheory.RowLev
open scoped TensorProduct

theorem hform_mulVec_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J M : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) x y := by
  have e : ∀ (N : Matrix n n A) (u v : n → A), Formalism.UG.hform σ N u v = (σ ∘ u) ⬝ᵥ (N *ᵥ v) := by
    intro N u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]
  have hσ : σ ∘ (M *ᵥ x) = M.map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ M x i
  rw [e, e, hσ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, Formalism.UG.cT, Matrix.mul_assoc]

variable (I : AutInst)

theorem fmat_mul_inv (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  simp [AutInst.fmat]

theorem fmat_inv_mul (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  simp [AutInst.fmat]

theorem hAf_unitary (x : I.Gf) (v w : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hAf I (I.fmat x *ᵥ v) (I.fmat x *ᵥ w) = hAf I v w := by
  unfold hAf
  rw [hform_mulVec_mulVec]
  have h : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.fmat x) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
      I.fmat x = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := x.2
  rw [h]

theorem hAf_move (x : I.Gf) (v w : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hAf I v (I.fmat x *ᵥ w) = hAf I (I.fmat x⁻¹ *ᵥ v) w := by
  rw [← hAf_unitary I x (I.fmat x⁻¹ *ᵥ v) w, mulVec_mulVec, fmat_mul_inv, one_mulVec]

theorem hAf_smul_right (v w : Fin I.n → I.E ⊗[I.F] Af I.F) (c : I.E ⊗[I.F] Af I.F) :
    hAf I v (c • w) = c * hAf I v w := by
  simp only [hAf, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hAf_smul_left (v w : Fin I.n → I.E ⊗[I.F] Af I.F) (c : I.E ⊗[I.F] Af I.F) :
    hAf I (c • v) w = sigA I c * hAf I v w := by
  simp only [hAf, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hAf_sub_right (u v w : Fin I.n → I.E ⊗[I.F] Af I.F) : hAf I u (v - w) = hAf I u v - hAf I u w := by
  simp only [hAf, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hAf_sub_left (u u' w : Fin I.n → I.E ⊗[I.F] Af I.F) : hAf I (u - u') w = hAf I u w - hAf I u' w := by
  simp only [hAf, Formalism.UG.hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem lf_iff {β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hβ : Formalism.L2.DIV.IsFrame β₀ I.L)
    (y : Fin I.n → I.E ⊗[I.F] Af I.F) :
    y ∈ I.Lf ↔ ∀ i, (((β₀⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
      *ᵥ y) i ∈ IntAf I.F I.E := by
  have e : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
    show Submodule.span _ _ = Submodule.span _ _
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z.1, z.2, rfl⟩
  rw [← e]
  exact hβ y

theorem eps_mem {β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hβ : Formalism.L2.DIV.IsFrame β₀ I.L)
    {ε : I.E ⊗[I.F] Af I.F} (hεi : ε ∈ IntAf I.F I.E) (x : I.Gf)
    (hx : ∀ i j, ε * ((β₀⁻¹ * (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j ∈ IntAf I.F I.E)
    {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    ε • ((I.fmat x - 1) *ᵥ y) ∈ I.Lf := by
  rw [lf_iff I hβ] at hy ⊢
  intro i
  set Bi : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
    ((β₀⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) with hBi
  set B : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
    ((β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) with hB
  have hBB : B * Bi = 1 := by rw [hB, hBi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hM : ∀ i j, ε * (Bi * I.fmat x * B) i j ∈ IntAf I.F I.E := by
    intro i j
    have := hx i j
    rwa [Units.val_mul, Units.val_mul] at this
  have key : Bi *ᵥ ((I.fmat x - 1) *ᵥ y) = (Bi * I.fmat x * B) *ᵥ (Bi *ᵥ y) - Bi *ᵥ y := by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc (Bi * I.fmat x), hBB, Matrix.mul_one, Matrix.mul_sub,
      Matrix.mul_one, sub_mulVec]
  rw [mulVec_smul, key]
  generalize Bi *ᵥ y = z at hy ⊢
  show ε * ((Bi * I.fmat x * B) *ᵥ z - z) i ∈ IntAf I.F I.E
  rw [Pi.sub_apply, mul_sub]
  refine sub_mem ?_ (mul_mem hεi (hy i))
  simp only [mulVec, dotProduct, Finset.mul_sum]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [← mul_assoc]
  exact mul_mem (hM i j) (hy j)

theorem sig_mem {β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hβ : Formalism.L2.DIV.IsFrame β₀ I.L)
    {ε : I.E ⊗[I.F] Af I.F} (hεi : ε ∈ IntAf I.F I.E) (x : I.Gf)
    (hxi : ∀ i j, ε * ((β₀⁻¹ * ((x⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j ∈ IntAf I.F I.E)
    {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    sigA I ε • ((I.fmat x - 1) *ᵥ y) ∈ I.Lf := by
  rw [GlobalTheory.AdelicLattice.adelicLattice_selfDual]
  intro y' hy'
  have h1 := eps_mem I hβ hεi x⁻¹ hxi hy'
  have h2 := (GlobalTheory.AdelicLattice.adelicLattice_selfDual I y).1 hy _ h1
  have e : hAf I y' (sigA I ε • ((I.fmat x - 1) *ᵥ y)) = hAf I (ε • ((I.fmat x⁻¹ - 1) *ᵥ y')) y := by
    rw [hAf_smul_right, hAf_smul_left, sub_mulVec, sub_mulVec, one_mulVec, one_mulVec, hAf_sub_right,
      hAf_sub_left, hAf_move]
  rw [e]
  exact h2

theorem mv_mem {β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hβ : Formalism.L2.DIV.IsFrame β₀ I.L)
    {ε : I.E ⊗[I.F] Af I.F} (hεi : ε ∈ IntAf I.F I.E) (x : I.Gf)
    (h1 : ∀ i j, (1 - ε - sigA I ε) * (I.fmat x - 1) i j = 0)
    (hx : ∀ i j, ε * ((β₀⁻¹ * (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j ∈ IntAf I.F I.E)
    (hxi : ∀ i j, ε * ((β₀⁻¹ * ((x⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j ∈ IntAf I.F I.E)
    {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    I.fmat x *ᵥ y ∈ I.Lf := by
  set w := (I.fmat x - 1) *ᵥ y with hw
  have hxy : I.fmat x *ᵥ y = y + w := by
    rw [hw, sub_mulVec, one_mulVec]
    abel
  have h0 : (1 - ε - sigA I ε) • w = 0 := by
    funext i
    simp only [hw, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Finset.mul_sum, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← mul_assoc, h1 i j, zero_mul]
  have hsplit : w = ε • w + sigA I ε • w + (1 - ε - sigA I ε) • w := by
    rw [← add_smul, ← add_smul, show ε + sigA I ε + (1 - ε - sigA I ε) = 1 by ring, one_smul]
  rw [hxy, hsplit, h0, add_zero, ← add_assoc]
  exact add_mem (add_mem hy (eps_mem I hβ hεi x hx hy)) (sig_mem I hβ hεi x hxi hy)

end GlobalTheory.SplitPairK


open GlobalTheory.SplitPairK in
theorem GlobalTheory.SplitPairK.mem_kset_of_split : ∀ (I : Formalism.MainNotions.S.AutInst) (β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), Formalism.L2.DIV.IsFrame β₀ I.L → ∀ (ε : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), ε * ε = ε → ε * Formalism.L2.SG.HidaSetting.sigA I ε = 0 → ε ∈ Formalism.MainNotions.S.IntAf I.F I.E → ∀ (k : I.Gf), (∀ i j, (1 - ε - Formalism.L2.SG.HidaSetting.sigA I ε) * (I.fmat k - 1) i j = 0) → (∀ i j, ε * ((β₀⁻¹ * (k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈ Formalism.MainNotions.S.IntAf I.F I.E) → (∀ i j, ε * ((β₀⁻¹ * ((k⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈ Formalism.MainNotions.S.IntAf I.F I.E) → k ∈ I.Kset := by
  intro I β₀ hβ ε _ _ hεi k h1 h2 h3
  have h1' : ∀ i j, (1 - ε - sigA I ε) * (I.fmat k⁻¹ - 1) i j = 0 := by
    intro i j
    have e : I.fmat k⁻¹ - 1 = -(I.fmat k⁻¹ * (I.fmat k - 1)) := by
      rw [Matrix.mul_sub, fmat_inv_mul, Matrix.mul_one]
      abel
    rw [e, Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum, neg_eq_zero]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [mul_left_comm, h1 l j, mul_zero]
  have h3' : ∀ i j, ε * ((β₀⁻¹ * ((k⁻¹⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ :
      GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈
      Formalism.MainNotions.S.IntAf I.F I.E := by
    simpa only [inv_inv] using h2
  show ((k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))) ∈ Formalism.UG.stabGL I.Lf
  intro y
  refine ⟨fun hy => mv_mem I hβ hεi k h1 h2 h3 hy, fun hy => ?_⟩
  have := mv_mem I hβ hεi k⁻¹ h1' h3 h3' hy
  rwa [Matrix.mulVec_mulVec, fmat_inv_mul, Matrix.one_mulVec] at this

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaximalCompactOfTrivialOffSplitPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_maximalCompact_of_trivial_off_splitPair : ∀ (I : Formalism.MainNotions.S.AutInst) (β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), Formalism.L2.DIV.IsFrame β₀ I.L → ∀ (ε : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), ε * ε = ε → ε * Formalism.L2.SG.HidaSetting.sigA I ε = 0 → ε ∈ Formalism.MainNotions.S.IntAf I.F I.E → ∀ (k : I.Gf), (∀ i j, (1 - ε - Formalism.L2.SG.HidaSetting.sigA I ε) * (I.fmat k - 1) i j = 0) → (∀ i j, ε * ((β₀⁻¹ * (k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈ Formalism.MainNotions.S.IntAf I.F I.E) → (∀ i j, ε * ((β₀⁻¹ * ((k⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈ Formalism.MainNotions.S.IntAf I.F I.E) → k ∈ I.Kset := by
  first | exact @GlobalTheory.SplitPairK.mem_kset_of_split | exact GlobalTheory.SplitPairK.mem_kset_of_split | (intros; apply GlobalTheory.SplitPairK.mem_kset_of_split <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralConjCuspFormParameterTransfer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLeftInvariantRepConjugateTensor
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesOfHasParamCover
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdditiveCharNeOneAtEachPrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOHZeroRight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ContrComb

variable {D : D7}

theorem symplOH_zero_right (S T : HSp D) (x : WO S T) : symplOH S T x 0 = 0 := by
  simp [symplOH, symplO, hO]

theorem symplOH_zero_left (S T : HSp D) (x : WO S T) : symplOH S T 0 x = 0 := by
  simp [symplOH, symplO, hO]

theorem heis_left {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (ψ : AddChar (AF D.host.F) ℂ) (l : Link B B'.L B'.ζ)
    (S : HSp D) (vL : VolM D B'.L.rank S.rank) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) (a : WO B.A S)
    (u : WO B.A S) (v : WO S B'.A) :
    heisO ψ B.A S a (fun u' => contr l S vL f₁ f₂ u' v) u =
      contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (a, 0)) f₁) f₂ u v := by
  simp only [heisO, contr]
  rw [← integral_const_mul]
  congr 1
  funext w
  have h1 : (B.o.resS S).symm (u, l.κ S w) + (B.o.resS S).symm (a, 0) = (B.o.resS S).symm (u + a, l.κ S w) := by
    rw [← map_add (f := _)]; simp
  rw [B.o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_right, add_zero, h1]
  ring

theorem heis_right {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (ψ : AddChar (AF D.host.F) ℂ) (l : Link B B'.L B'.ζ)
    (S : HSp D) (vL : VolM D B'.L.rank S.rank) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) (b : WO S B'.A)
    (u : WO B.A S) (v : WO S B'.A) :
    heisO ψ S B'.A b (contr l S vL f₁ f₂ u) v =
      contr l S vL f₁ (heisO ψ S B'.V₀ ((B'.o.resT S).symm (b, 0)) f₂) u v := by
  simp only [heisO, contr]
  rw [← integral_const_mul]
  congr 1
  funext w
  have h1 : (B'.o.resT S).symm (v, w) + (B'.o.resT S).symm (b, 0) = (B'.o.resT S).symm (v + b, w) := by
    rw [← map_add (f := _)]; simp
  rw [B'.o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_right, add_zero, h1]
  ring

end GlobalTheory.ContrComb
end

noncomputable section
namespace GlobalTheory.ContrComb

variable {D : D7}

def extL {V₀ A L S : HSp D} (o : OrthDec V₀ A L) : WO A S →+ WO V₀ S :=
  (o.resS S).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)

def extR {V₀ A L S : HSp D} (o : OrthDec V₀ A L) : WO S A →+ WO S V₀ :=
  (o.resT S).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)

theorem extL_apply {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO A S) : extL (S := S) o u = (o.resS S).symm (u, 0) := rfl

theorem extR_apply {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO S A) : extR (S := S) o u = (o.resT S).symm (u, 0) := rfl

theorem continuous_extL {V₀ A L S : HSp D} (o : OrthDec V₀ A L) : Continuous (extL (S := S) o) :=
  (o.continuous_resS_symm S).comp (continuous_id.prodMk continuous_const)

theorem continuous_extR {V₀ A L S : HSp D} (o : OrthDec V₀ A L) : Continuous (extR (S := S) o) :=
  (o.continuous_resT_symm S).comp (continuous_id.prodMk continuous_const)

theorem extL_inf {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO A S) (h : u.map (infPart D) = 0) :
    (extL (S := S) o u).map (infPart D) = 0 := by
  rw [extL_apply, OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
  change (u * o.pA).map (infPart D) = 0
  rw [Matrix.map_mul, h, Matrix.zero_mul]

theorem extR_inf {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO S A) (h : u.map (infPart D) = 0) :
    (extR (S := S) o u).map (infPart D) = 0 := by
  rw [extR_apply, OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]
  change (o.jA * u).map (infPart D) = 0
  rw [Matrix.map_mul, h, Matrix.mul_zero]

theorem extL_half {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (e : AE D) (u : WO A S) (h : IsHalf e u) :
    IsHalf e (extL (S := S) o u) := by
  intro i j
  rw [extL_apply, OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
  change e * (u * o.pA) i j = (u * o.pA) i j
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, h i]

theorem extR_half {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (e : AE D) (u : WO S A) (h : IsHalf e u) :
    IsHalf e (extR (S := S) o u) := by
  intro i j
  rw [extR_apply, OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]
  change e * (o.jA * u) i j = (o.jA * u) i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, h k j]

end GlobalTheory.ContrComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelFinitePartFrameActionMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelFinitePartFrameActionMatrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.AdBridge

namespace GlobalTheory.Core.Mi.FinFrame

theorem eq_self_of_rat_of_int (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ι : E ⊗[F] Formalism.MainNotions.S.Af F →+* E ⊗[F] Formalism.MainNotions.S.Af F)
    (hι : ∀ x, ι (Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) x) = Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) x)
    (hO : ∀ a ∈ IntAf F E, ι a ∈ IntAf F E) (a : E ⊗[F] Formalism.MainNotions.S.Af F) : ι a = a := by
  obtain ⟨-, hden, hzero, hdenom, -⟩ := GlobalTheory.St.G.IntAd.integral_adeles_properties F E
  have key : ∀ b ∈ IntAf F E, ι b = b := by
    intro b hb
    rw [← sub_eq_zero]
    refine hzero _ fun m hm => ?_
    obtain ⟨x, t, ht, rfl⟩ := hden b hb m hm
    refine ⟨ι t - t, (IntAf F E).sub_mem (hO _ ht) ht, ?_⟩
    simp only [map_add (f := _), map_mul, map_natCast, hι]
    ring
  obtain ⟨m, hm, hma⟩ := hdenom a
  have h := key _ hma
  simp only [map_mul, map_natCast] at h
  have hu : IsUnit (m : E ⊗[F] Formalism.MainNotions.S.Af F) := by
    have : IsUnit (m : F) := (Nat.cast_ne_zero.2 hm.ne').isUnit
    simpa using this.map (algebraMap F (E ⊗[F] Formalism.MainNotions.S.Af F))
  exact hu.mul_left_cancel h

theorem tauF_eq (D : D7) (z : AE D) : tauF (Formalism.L2.SG.InstExistsPf.instOf D) z = toEAf D z := by
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero (toEAf D)).symm
  | tmul a x => exact tauF_tmul (Formalism.L2.SG.InstExistsPf.instOf D) a x
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add (toEAf D) x y).symm)

theorem fmat_iota (D : D7) (g : GA D (D.sp.Y 0)) :
    (Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 = (mt (D.sp.Y 0) g).map (toEAf D) := by
  have hb := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D g)
  have key : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D g) = g :=
    (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply g
  refine (hb.2.trans (congrArg (fun q => ofHAFin (Formalism.IndefR.RationalEmbedding.inst D) q) key)).trans ?_
  ext i j
  exact tauF_eq D _

theorem toEAf_incA (D : D7) (y : D.host.E) :
    toEAf D (incA D y) = Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) y :=
  (tauF_eq D _).symm.trans (tauF_tmul (Formalism.L2.SG.InstExistsPf.instOf D) 1 y)

theorem map_cols {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) {m n : ℕ} (M : Matrix (Fin m) (Fin m) A)
    (N : Matrix (Fin m) (Fin n) A) (P : Matrix (Fin n) (Fin n) A) (h : M * N = N * P) (j : Fin n) :
    M.map f *ᵥ (fun k => f (N k j)) = ∑ i, f (P i j) • fun k => f (N k i) := by
  funext k
  have h3 := congrArg f (congrFun (congrFun h k) j)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul] at h3
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h3]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem embA_cols {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (a : GA D A)
    (j : Fin A.rank) :
    (mt S (embA d o a)).map (toEAf D) *ᵥ
        (fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) ((d.i₀ * o.iA) k j)) =
      ∑ i, toEAf D (mt A a i j) • fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) ((d.i₀ * o.iA) k i) := by
  have h1 : mt S (embA d o a) ⬝ (d.j0 ⬝ o.jA) = (d.j0 ⬝ o.jA) ⬝ mt A a := by
    change mt S (d.emb0 (o.emb (a, 1))) ⬝ (d.j0 ⬝ o.jA) = _
    rw [← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_assoc, o.emb_jA, Matrix.mul_assoc]
  have h2 : d.j0 ⬝ o.jA = (d.i₀ * o.iA).map (incA D) := (Matrix.map_mul (f := incA D)).symm
  rw [h2] at h1
  have h3 := map_cols (toEAf D) _ _ _ h1 j
  simp only [Matrix.map_apply, toEAf_incA] at h3
  exact h3

theorem transport (D : D7) (I : AutInst) (ιE : I.E ≃+* D.host.E) (hId : ∀ y, HEq (ιE y) y)
    (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (hr : (D.sp.Y 0).rank = I.n)
    (ιA : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (hrat : ∀ x : I.E, ιA (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) =
      Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιE x))
    (hint : ∀ a, a ∈ IntAf I.F I.E ↔ ιA a ∈ IntAf D.host.F D.host.E)
    {n : ℕ} (q : Fin n → Fin I.n → I.E) (g : GA D (D.sp.Y 0)) (c : Fin n → GlobalTheory.AdForm.EF D) (j : Fin n)
    (H : (mt (D.sp.Y 0) g).map (toEAf D) *ᵥ
        (fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) (ιE (q j (Fin.cast hr k)))) =
      ∑ i, c i • fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) (ιE (q i (Fin.cast hr k)))) :
    I.fmat (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D g)).2 *ᵥ incl I (q j) = ∑ i, ιA.symm (c i) • incl I (q i) := by
  generalize hI.symm = e
  subst hI
  have hid : ∀ y, ιE y = y := fun y => eq_of_heq (hId y)
  have hA : ∀ a, ιA a = a := eq_self_of_rat_of_int (Formalism.L2.SG.InstExistsPf.instOf D).F (Formalism.L2.SG.InstExistsPf.instOf D).E ιA.toRingHom
    (fun x => (hrat x).trans (congrArg _ (hid x))) (fun a ha => (hint a).1 ha)
  have hA' : ∀ a, ιA.symm a = a := fun a => (hA _).symm.trans (ιA.apply_symm_apply a)
  simp only [hid] at H
  simp only [hA']
  change (Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 *ᵥ _ = _
  rw [fmat_iota]
  exact H

theorem repM_toH : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F), GlobalTheory.Core.Mi.IdE X → B.Adapted tr.wt → ∀ a : GA D (D.sp.X 0), RepM X tr.wt tr.ιA ((B.toH a).2 : X.B.I.Gf) (GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a) := by
  intro D X h u ψ B F tr hId hAd a j
  have hn := Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)
  refine transport D X.B.I X.ιE hId h (rank_eq X h) tr.ιA tr.ιA_rat tr.ιA_int
    (fun i => X.crd (Formalism.L2.SG.ColDict.qFr tr.wt i)) (embA B.d B.o a)
    (fun i => GlobalTheory.AdForm.finM (D.sp.X 0) hn a i j) j ?_
  have H := embA_cols B.d B.o a (Fin.cast hn.symm j)
  simp only [hAd _ _] at H
  refine H.trans ?_
  exact Fintype.sum_equiv (finCongr hn) _ _ fun i => rfl

end GlobalTheory.Core.Mi.FinFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelFinitePartFrameActionMatrixStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondModel_finitePart_frameActionMatrix : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F), GlobalTheory.Core.Mi.IdE X → B.Adapted tr.wt → ∀ a : GA D (D.sp.X 0), RepM X tr.wt tr.ιA ((B.toH a).2 : X.B.I.Gf) (GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a) := by
  first | exact @GlobalTheory.Core.Mi.FinFrame.repM_toH | exact GlobalTheory.Core.Mi.FinFrame.repM_toH | (intros; apply GlobalTheory.Core.Mi.FinFrame.repM_toH <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealParOfIsCharAF
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.StdUnn


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_realPar_of_isCharAF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
    ∀ θ : InfFam D, IsInfFam θ → ∃ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l := by
  intro D ψ hψ θ hθ
  obtain ⟨ψ₀, h₀, a, -, ha⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  set y : D.host.E := algebraMap D.host.F D.host.E a with hy_def
  have hyc : IsCMField.complexConj D.host.E y = y :=
    (IsCMField.complexConj_eq_self_iff D.host.E y).2 a.2
  have hreal : ∀ τ, (tauE D τ y).im = 0 := by
    intro τ
    have h := IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) y
    rw [hyc] at h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith
  refine ⟨fun τ => -(tauE D τ y).re, ?_⟩
  intro x
  have e1 : psiInf D.host.F ψ x = psiInf D.host.F ψ₀ (algebraMap D.host.F (Ainf D.host.F) a * x) := by
    simp only [psiInf]
    rw [ha]
    congr 1
    show (algebraMap D.host.F (Ainf D.host.F) a * x, algebraMap D.host.F (Af D.host.F) a * 0) = _
    rw [mul_zero]; rfl
  rw [e1, h₀.2.2 θ hθ]
  congr 1
  have e2 : ∀ ρ, θ ρ ((algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D ρ y := by
    intro ρ
    have e3 : (algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E) =
        (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← Algebra.smul_def, ← TensorProduct.smul_tmul',
        ← TensorProduct.tmul_smul, Algebra.smul_def, mul_one]
    rw [e3, map_mul, (hθ ρ).1]
  simp only [e2]
  have e4 : ∀ ρ, (((-(tauE D ρ y).re : ℝ)) : ℂ) = -tauE D ρ y := by
    intro ρ
    apply Complex.ext <;> simp [hreal ρ]
  simp only [e4, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun ρ _ => ?_
  ring

end GlobalTheory.StdUnn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledPairThetaFunctionEqZeroOfSchrodingerEqZer
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledPairThetaFunctionEqZeroOfSchrodingerEqZer
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

namespace GlobalTheory.Core.Rk.SchwInj

theorem sch_heisO_extY {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D)
    {ν : Measure (WO A B)} {𝓨 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓨) {f : WO (dblSp A) B → ℂ}
    (hf : IsThetaFunO ψ (dblSp A) B f) (x y : Mx D B.rank A.rank) :
    sch ψ A B ν 𝓨 (heisO ψ (dblSp A) B ((dblDec A).extY B y) f) x =
      ψ (symplO (dblSp A) B ((dblDec A).extX B x) ((dblDec A).extY B y)) * sch ψ A B ν 𝓨 f x :=
  congrFun ((GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) ⟨ν, 𝓨, hν⟩ f hf).2.1 x y) 0

theorem exists_extX_add_extY {D : D7} (A B : HSp D) (w : WO (dblSp A) B) :
    ∃ x y : Mx D B.rank A.rank, w = (dblDec A).extX B x + (dblDec A).extY B y := by
  obtain ⟨⟨x, w₀, y⟩, rfl⟩ := ((dblDec A).coordS B).symm.surjective w
  have hw : w₀ = 0 := Matrix.ext fun _ j => Fin.elim0 j
  subst hw
  refine ⟨x, y, ?_⟩
  show (dblDec A).extX B x + (dblDec A).ext0 B 0 + (dblDec A).extY B y = _
  rw [map_zero, add_zero]

theorem eq_zero_of_sch_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → sch ψ A B ν 𝓨 f = 0 → f = 0 := by
  intro D ψ hψ A B ν 𝓨 hν f hf hs
  funext w
  obtain ⟨x, y, rfl⟩ := exists_extX_add_extY A B w
  have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf ((dblDec A).extY B y)
  have hsum := (GlobalTheory.T.doubledTheta_eq_sum_schrodingerFunction_periodisation D ψ hψ A B ν 𝓨 hν _ hg x).2
  simp only [sch_heisO_extY hψ A B hν hf, hs, Pi.zero_apply, mul_zero] at hsum
  have h0 : ψ (symplOH (dblSp A) B ((dblDec A).extX B x) ((dblDec A).extY B y)) *
      f ((dblDec A).extX B x + (dblDec A).extY B y) = 0 := hsum.unique hasSum_zero
  refine (mul_eq_zero.1 h0).resolve_left fun h => ?_
  have h1 := ψ.map_add_eq_mul (symplOH (dblSp A) B ((dblDec A).extX B x) ((dblDec A).extY B y))
    (-symplOH (dblSp A) B ((dblDec A).extX B x) ((dblDec A).extY B y))
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at h1
  exact one_ne_zero h1

end GlobalTheory.Core.Rk.SchwInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledPairThetaFunctionEqZeroOfSchrodingerEqZerStatement
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledPairThetaFunction_eq_zero_of_schrodinger_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → sch ψ A B ν 𝓨 f = 0 → f = 0 := by
  first | exact @GlobalTheory.Core.Rk.SchwInj.eq_zero_of_sch_eq_zero | exact GlobalTheory.Core.Rk.SchwInj.eq_zero_of_sch_eq_zero | (intros; apply GlobalTheory.Core.Rk.SchwInj.eq_zero_of_sch_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumRestrictionRankZero
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.ChainOnto
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.RankZeroVac

variable {D : D7}

theorem incA_tmul' (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

section
variable {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (T : HSp D)

theorem continuous_wittExtendByZero : Continuous (d.ext0 T) := continuous_id.matrix_mul continuous_const

theorem heisenbergOperator_wittExtendByZero (ψ : AddChar (AF D.host.F) ℂ) (u : WO W₀ T) (f : WO W T → ℂ) :
    heisO ψ W₀ T u (fun w => f (d.ext0 T w)) = fun w => heisO ψ W T (d.ext0 T u) f (d.ext0 T w) := by
  funext w
  simp only [heisO, map_add (f := _), d.wittDecomp_sympl_extAnisotropic_extAnisotropic]

theorem isThetaFunction_comp_wittExtendByZero {ψ : AddChar (AF D.host.F) ℂ} {f : WO W T → ℂ} (hf : IsThetaFunO ψ W T f) :
    IsThetaFunO ψ W₀ T (fun w => f (d.ext0 T w)) := {
  quasi γ w := by
    have h := hf.quasi (γ * d.q0) (d.ext0 T w)
    have hr : ratW T W (γ * d.q0) = d.ext0 T (ratW T W₀ γ) := by
      rw [ratW_eq, ratW_eq, rat_mul, d.matrixExtendByZero_apply]; rfl
    rw [hr, d.wittDecomp_sympl_extAnisotropic_extAnisotropic] at h
    simp only [map_add (f := _)]
    exact h
  level := by
    obtain ⟨U, hU, hfix⟩ := hf.level
    refine ⟨U.comap (d.ext0 T), hU.preimage (continuous_wittExtendByZero d T), fun u hu hinf => ?_⟩
    rw [heisenbergOperator_wittExtendByZero]
    have h0 : (d.ext0 T u).map (infPart D) = 0 := by
      rw [d.matrixExtendByZero_apply, Matrix.map_mul, hinf, Matrix.zero_mul]
    rw [hfix _ hu h0]
  cont := hf.cont.comp (continuous_wittExtendByZero d T)
  smooth k L hL hLf w := by
    have h := hf.smooth k ((d.ext0 T).comp L) ((continuous_wittExtendByZero d T).comp hL) (fun t => by
      show (d.ext0 T (L t)).map (finPart D) = 0
      rw [d.matrixExtendByZero_apply, Matrix.map_mul, hLf t, Matrix.zero_mul]) (d.ext0 T w)
    simpa only [AddMonoidHom.comp_apply, map_add (f := _)] using h }

theorem isHalf_wittHyperbolicExtendByZero_apply {e : AE D} {u : WO W₀ T} (h : IsHalf e u) : IsHalf e (d.ext0 T u) := by
  intro i j
  have hl : ∀ l, e * ((u : Matrix (Fin T.rank) (Fin W₀.rank) (AE D)) i l * d.p0 l j) =
      (u : Matrix (Fin T.rank) (Fin W₀.rank) (AE D)) i l * d.p0 l j := fun l => by rw [← mul_assoc, h i l]
  rw [d.matrixExtendByZero_apply, Matrix.mul_apply]
  show e * ∑ l, _ = _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => hl l

end

end GlobalTheory.RankZeroVac

namespace GlobalTheory.RankZeroVac

variable {D : D7}

section
variable {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (T : HSp D)

theorem wittDecomposition_gram_projection_identity (s : Fin W₀.rank → D.host.E) (j : Fin W.rank) :
    ∑ l, (∑ k, star (s k) * W₀.gram k l) * d.q0 l j = ∑ m, star ((Matrix.mulVec d.i₀ s) m) * W.gram m j := by
  have h : Matrix.vecMul (Matrix.vecMul (star s) W₀.gram) d.q0 = Matrix.vecMul (star (Matrix.mulVec d.i₀ s)) W.gram := by
    rw [Matrix.vecMul_vecMul, HypDec.q0, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_isUnit_det W₀),
      Matrix.one_mul, ← Matrix.vecMul_vecMul, Matrix.star_mulVec]
  have hj := congrFun h j
  simpa only [Matrix.vecMul, dotProduct, Pi.star_apply] using hj

end

end GlobalTheory.RankZeroVac

namespace GlobalTheory.RankZeroVac

variable {D : D7}

section
variable {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (T : HSp D)

end

end GlobalTheory.RankZeroVac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesDetSqrtCoverOfUnitaryClassificatio
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsParamCoverDiscreteSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsParamCoverDiscreteSeries
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.CoverExhaust

variable {p q n : ℕ}

theorem blockOrd_std (p q : ℕ) :
    BlockOrd (finSumFinEquiv : Ix p q ≃ Fin (p + q)) fun i => (finSumFinEquiv.symm i).isLeft := by
  refine ⟨fun i => by simp, fun j => by simp, ?_⟩
  rintro (a | a) (b | b) hab
  · exact hab
  · exact hab.elim
  · exact hab.elim
  · exact Nat.add_lt_add_left hab p

theorem blockOrd_perm {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (s : Equiv.Perm (Fin n))
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) : BlockOrd (e.trans s.symm) (ε ∘ s) := by
  refine ⟨fun i => by simpa using h.1 i, fun j => by simpa using h.2.1 j, ?_⟩
  intro a b hab
  obtain ⟨hlt, hε⟩ := (h.posC_iff a b).1 hab
  simp only [Equiv.trans_apply]
  rcases lt_trichotomy (s.symm (e a)) (s.symm (e b)) with h1 | h1 | h1
  · exact h1
  · exact absurd (s.symm.injective h1) (ne_of_lt hlt)
  · have h2 := hs _ _ h1 (by simp only [Equiv.apply_symm_apply]; exact hε.symm)
    simp only [Equiv.apply_symm_apply] at h2
    exact absurd h2 (not_lt.2 hlt.le)

theorem exists_param_of_trivial (hE : GlobalTheory.Dec.DSExhaust) {T : GrpData p q} (R : DSRep T)
    (k : ∀ x, T.cov x = 1 → R.U.π x = 1) :
    ∃ (P : SignedPar (p + q)) (e : Ix p q ≃ Fin (p + q)), BlockOrd e P.sgn ∧ HasParam R (blockPar P e) := by
  obtain ⟨σ, hF⟩ := exists_factors R.U (finSumFinEquiv : Ix p q ≃ Fin (p + q)) k
  have hB0 := blockOrd_std p q
  have hIrr : GlobalTheory.Dec.IsSqIntIrr (fun i : Fin (p + q) => (finSumFinEquiv.symm i).isLeft) σ :=
    ⟨R.U.cs, R.nontriv,
      (GlobalTheory.T.discreteSeries_cover_irreducibleUnitary p q (p + q) _ _ T R σ hB0 hF).1,
      (GlobalTheory.T.discreteSeries_cover_irreducibleUnitary p q (p + q) _ _ T R σ hB0 hF).2,
      GlobalTheory.T.block_ordered_square_integrable p q (p + q) _ _ T R σ hB0 hF⟩
  obtain ⟨s, mu, hc, hs, hDS⟩ := hE (p + q) _ R.U.H σ hIrr
  let P : SignedPar (p + q) := ⟨mu, (fun i : Fin (p + q) => (finSumFinEquiv.symm i).isLeft) ∘ s, hc⟩
  have hB : BlockOrd ((finSumFinEquiv : Ix p q ≃ Fin (p + q)).trans s.symm) P.sgn := blockOrd_perm hB0 s hs
  have hF' : Factors R.U ((finSumFinEquiv : Ix p q ≃ Fin (p + q)).trans s.symm)
      (fun g => σ (g.submatrix s.symm s.symm)) := by
    intro x
    rw [hF x]
    congr 1
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact ⟨P, _, hB, (hasParam_iff_isDSPar R P hB hF').2 hDS⟩

theorem exists_param : GlobalTheory.Dec.DSExhaust → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R : DSRep T), ∃ lam, IsParam lam ∧ HasParam R lam := by
  intro hE p q _ T R
  rcases Cover.trivial_or_twist R with k | k
  · obtain ⟨P, e, h1, h2⟩ := exists_param_of_trivial hE R k
    exact ⟨_, isParam_blockPar P h1, h2⟩
  · obtain ⟨P, e, h1, h2⟩ := exists_param_of_trivial hE (Cover.twist R) k
    exact ⟨_, isParam_half P h1, (Cover.hasParam_twist R _).1 h2⟩

end GlobalTheory.CoverExhaust
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsParamCoverDiscreteSeriesStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_param_coverDiscreteSeries : GlobalTheory.Dec.DSExhaust → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R : DSRep T), ∃ lam, IsParam lam ∧ HasParam R lam := by
  first | exact @GlobalTheory.CoverExhaust.exists_param | exact GlobalTheory.CoverExhaust.exists_param | (intros; apply GlobalTheory.CoverExhaust.exists_param <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesDetSqrtCoverOfUnitaryClassificatio
open Formalism.BasicNotions.TH GlobalTheory.RealPar

noncomputable section

namespace GlobalTheory.CoverDS

theorem discreteSeriesCover_of_classification :
    GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCover := by
  intro hcl
  obtain ⟨hExists, hExhaust, hUnique, hInfChar, hLowK, hKTypes, -⟩ :=
    GlobalTheory.ClassificationConsequences.consequences_of_dsClass
      (GlobalTheory.Published.discreteSeriesClassification_iff.1 hcl)
  have hC : GlobalTheory.Published.DiscreteSeriesCoverExists :=
    GlobalTheory.Published.CoverSeries.of_upq
      (GlobalTheory.Published.discreteSeriesUpqExists_iff_dsExists.2 hExists)
      (fun p q h T U hU => ((GlobalTheory.T.harishChandraModules_indefiniteUnitaryGroup.1 p q h T).1 U hU).2.1)
  intro p q hn T
  choose D hD using fun lam : {lam : Ix p q → ℚ // IsParam lam} => hC p q T lam.1 lam.2
  refine ⟨D, ?_, ?_⟩
  · intro lam
    exact GlobalTheory.T.hasDiscreteSeriesKTypes_of_hasParam_cover
      hLowK hKTypes hInfChar p q hn T (D lam) lam.1 lam.2 (hD lam)
  · intro R
    obtain ⟨lam, hl, hR⟩ := GlobalTheory.T.exists_param_coverDiscreteSeries hExhaust p q hn T R
    exact ⟨⟨lam, hl⟩, GlobalTheory.T.coverDiscreteSeriesUnitarilyEquiv_of_sameParam
      hUnique p q hn T R (D ⟨lam, hl⟩) lam hl hR (hD ⟨lam, hl⟩)⟩

end GlobalTheory.CoverDS

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesDetSqrtCoverOfUnitaryClassificatioStatement
theorem GlobalTheory.T.discreteSeries_detSqrtCover_of_unitary_classification :
    GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCover :=
  GlobalTheory.CoverDS.discreteSeriesCover_of_classification
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralSplitPlaceAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LvTwDivDvSplit
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LocValSplit
open GlobalTheory.LFun (LvTw_eq eulerFac_eq_prod etaU locL etaFam_of_unram eulerFac_singleton mem_aboveF)

theorem LvTw_div_dv_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (v : HeightOneSpectrum (𝓞 F)) (w w' : HeightOneSpectrum (𝓞 E)) (r b : ℕ) (s : ℂ), IsSplit (E := E) v → Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v → w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = w ∨ u = w') → Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal → Ideal.absNorm w'.asIdeal = Ideal.absNorm v.asIdeal → B w' = (B w).map (·⁻¹) → m w * m w' = 1 → LvTw B m v (s + 1 / 2) / dv E r b v s = eulerFac ((B w).map ((m w)⁻¹ * ·)) (GlobalTheory.LFun.npow w (-(s + 1 / 2))) * eulerFac ((B w).map fun β => ((m w)⁻¹ * β)⁻¹) (GlobalTheory.LFun.npow w (-(s + 1 / 2))) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ (-(2 * s + r - i))) := by
  intro F E _ _ _ _ _ B m v w w' r b s hsplit hunr hne hv hqw hqw' hB' hm1
  classical
  set X : ℂ := GlobalTheory.LFun.npow w (-(s + 1 / 2)) with hXdef
  set μ : ℂ := (m w : ℂ) with hμ
  have hX' : GlobalTheory.LFun.npow w' (-(s + 1 / 2)) = X := by rw [hXdef, GlobalTheory.LFun.npow, GlobalTheory.LFun.npow, hqw, hqw']
  have hinv : ((m w' : ℂ))⁻¹ = μ := inv_eq_of_mul_eq_one_left (by rw [hμ, ← Units.val_mul, hm1, Units.val_one])
  have e : Formalism.L2.Host.aboveF (L := E) F v = {w, w'} := by ext u; simp [mem_aboveF, hv]
  have hL : LvTw B m v (s + 1 / 2) = ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod *
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [LvTw_eq, e, Finset.prod_pair hne, hB', Multiset.map_map, hX', hinv]
    simp only [Function.comp_def, Units.val_inv_eq_inv_val]
    rfl
  have hr1 : eulerFac ((B w).map ((m w)⁻¹ * ·)) X = ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod := by
    rw [eulerFac_eq_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
    simp only [Function.comp_apply, Units.val_mul, Units.val_inv_eq_inv_val, hμ]
    ring
  have hr2 : eulerFac ((B w).map fun β => ((m w)⁻¹ * β)⁻¹) X =
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [eulerFac_eq_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
    simp only [Function.comp_apply, Units.val_inv_eq_inv_val, Units.val_mul, mul_inv, inv_inv, hμ]
    ring
  have hd : dv E r b v s = (∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ (-(2 * s + r - i))))⁻¹ := by
    rw [← Finset.prod_inv_distrib, dv]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hu : etaU E v = 1 := by unfold etaU; rw [if_pos hsplit]
    rw [locL, etaFam_of_unram hunr, hu, one_pow, eulerFac_singleton, Units.val_one, one_mul, GlobalTheory.LFun.npow, qV, hqw]
  rw [hd, div_inv_eq_mul, hL, hr1, hr2]

end GlobalTheory.LocValSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralSplitPlaceAdelic
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

open Formalism.UG (IsUnifV qV)
open GlobalTheory.LFun (KGL IsSatVecGL eulerFac UnrAt LvTw)
open GlobalTheory.LFun (locChar IsSplitChart IsInertChart KGL UnrAt toCompl locMat IsFrameAt IsSatVecU eulerFac LvTw dv Fam)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.Doubling (ioH_mem_KFin)

namespace GlobalTheory.Core.Rk.IP


set_option maxHeartbeats 2000000 in
theorem localZetaOn_split : GlobalTheory.Published.UnramifiedDoublingGL →
    ∀ D : D7, LocalZetaOn D fun v => Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  intro hP D A L hL χ b hχ hb v hv hU μ hμH hK s hs φ hφ par c hc
  classical
  have hcm := isCMExt_host D
  have h2 : Module.finrank D.host.F D.host.E = 2 := hcm.2.2.1
  have hJ : IsHermND D.sp.cm.sig A.gram := GlobalTheory.Doubling.isHermND_gram A
  haveI : Submodule.IsFullLattice D.host.E L :=
    Formalism.IndefR.Fin.PDA.selfDual_isFullLattice A L hL
  have hd : IsSelfDualAt D.sp.cm.sig A.gram L v :=
    (SelfDual.forall_isSelfDualAt_iff (σ := D.sp.cm.sig) (GlobalTheory.Doubling.isHermND_gram A).2
      inferInstance).2
      (fun y => hL.2 y) v
  obtain ⟨w, h⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hc' := hc
  obtain ⟨⟨C, hC⟩, V, _, _, ρ, x, ℓ, hpar, -, hcx⟩ := hc
  obtain ⟨w', hne, hall, hN, hN', -⟩ := GlobalTheory.LFun.SplitChart.exists_conj_place hcm h hv
  have h' : w'.under (𝓞 D.host.F) = v := (hall w').2 (Or.inr rfl)
  obtain ⟨e, he, hsat⟩ : ∃ e, IsSplitChart D.sp.cm.sig A.gram L h e ∧
      IsSatVecGL w (ρ.comp e.symm.toMonoidHom) x (par w) := by
    rcases hpar w h with ⟨-, e, he, hsat⟩ | ⟨hw, -⟩
    · exact ⟨e, he, hsat⟩
    · exact absurd hv (GlobalTheory.LFun.not_isSplit_of_isInertAt hw)
  have hB' : par w' = (par w).map (·⁻¹) :=
    GlobalTheory.LFun.ConjPlace.eq_map_inv_of_isParamVec hcm hJ hd hne (hpar w h) (hpar w' h')
  have hm : GlobalTheory.LFun.val χ w * GlobalTheory.LFun.val χ w' = 1 :=
    GlobalTheory.LFun.ResEta.val_mul_val h2 ((GlobalTheory.LFun.resEta_iff χ _).1 hb) hne h h' (hU w h) (hU w' h')
  have hfix : ∀ k ∈ stabLoc D.sp.cm.sig A.gram L v, ρ k x = x :=
    GlobalTheory.LGrp.mem_fixed.1 (hpar w h).mem_fixed
  have hz1 : ‖(((GlobalTheory.LFun.val χ w)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, GlobalTheory.LFun.norm_val, inv_one]
  have hker := GlobalTheory.T.sphericalSection_graph_splitPlace D A L hL χ b hb v hv hU s φ hφ w h e he
  have hbd : ℓ x ≠ 0 → ∀ β ∈ par w, ‖(β : ℂ)‖ ≤ (qV D.host.E w : ℝ) ^ ((A.rank : ℝ) / 2) ∧
      ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV D.host.E w : ℝ) ^ ((A.rank : ℝ) / 2) := by
    intro h0 β hβ
    have hc1 : c 1 ≠ 0 := by rw [hcx, map_one, Module.End.one_apply]; exact h0
    have Hb := GlobalTheory.T.sphericalParameterBound_split_place D A L hL v hv par c hc' hc1
    refine ⟨(Hb w h).2 β hβ, ?_⟩
    have H2 := (Hb w' h').2 β⁻¹ (hB' ▸ Multiset.mem_map_of_mem _ hβ)
    have e2 : ((Ideal.absNorm w'.asIdeal : ℕ) : ℝ) = (qV D.host.E w : ℝ) := by
      rw [hN', ← hN]; rfl
    rwa [e2] at H2
  have hsum := GlobalTheory.ZetaGL.zeta_sum_GL_complex hP D.host.E w A.rank s (by have : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _; linarith)
    (GlobalTheory.LFun.val χ w)⁻¹ (fun g => φ (ioAt A v (e.symm g))) hz1 hker V (ρ.comp e.symm.toMonoidHom) x (par w) hsat ℓ
    ⟨C, fun g => by have := hC (e.symm g); rwa [hcx] at this⟩ hbd
  have hval := GlobalTheory.LocValSplit.LvTw_div_dv_split D.host.F D.host.E par (GlobalTheory.LFun.val χ) v w w' A.rank b s hv
    (GlobalTheory.LFun.isUnram_of_isSplit h2 hv) hne hall hN hN' hB' hm
  have hinv : ∀ y, ∀ k ∈ stabLoc D.sp.cm.sig A.gram L v,
      φ (ioAt A v (y * k)) * c (y * k) = φ (ioAt A v y) * c y := by
    intro y k hk
    have e1 : ioAt A v (y * k) = ioAt A v y * ioAt A v k := by
      unfold ioAt
      rw [← map_mul]
      simp
    have hk' : ioAt A v k ∈ KFin D.sp.cm.sig (dblSp A).gram L v :=
      (ioH_mem_KFin (gram_hdbl A)).2 ⟨hk, one_mem _⟩
    rw [e1, hφ.2.1 _ hk', hcx, hcx, map_mul, Module.End.mul_apply, hfix k hk]
  have hsum' := GlobalTheory.T.hasSum_quotient_of_hasSum_mulEquiv_quotient _ _ e (stabLoc D.sp.cm.sig A.gram L v) (KGL w (n := A.rank)) he.2
    (fun y => φ (ioAt A v y) * c y) hinv _ (by
      refine hsum.congr_fun ?_
      intro a
      simp [hcx])
  obtain ⟨hI, hE⟩ := GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets (Gv A v) μ (stabLoc D.sp.cm.sig A.gram L v)
    (GlobalTheory.AdelicU.isOpen_stabLoc _ _ _ v) hK (fun y => φ (ioAt A v y) * c y) _ hinv hsum'
  refine ⟨hI, ?_⟩
  rw [hE, hval, hcx, map_one, Module.End.one_apply]

end GlobalTheory.Core.Rk.IP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralSplitPlaceAdelicStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedDoublingIntegral_splitPlace_adelic : GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, LocalZetaOn D fun v => Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.Core.Rk.IP.localZetaOn_split | exact GlobalTheory.Core.Rk.IP.localZetaOn_split | (intros; apply GlobalTheory.Core.Rk.IP.localZetaOn_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HolomorphicContinuationValueNnrealPowFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HolomorphicContinuationValueNnrealPowFactor
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem holValueAt_npow_sub_mul : ∀ (h h' : ℂ → ℂ) (s₀ c : ℂ) (r : ℝ≥0) (σ : ℝ), 0 < r → HolValueAt h s₀ c →
    (∀ s : ℂ, σ < s.re → h' s = npow r (s₀ - s) * h s) → HolValueAt h' s₀ c := by
  intro h h' s₀ c r σ hr hh e
  have ha : AnalyticOnNhd ℂ (fun s => npow r (s₀ - s)) (GlobalTheory.Cont.rightOf (s₀.re - 1)) := by
    intro s _
    rw [funext fun s => npow_eq_exp hr (s₀ - s)]
    fun_prop
  have hg := GlobalTheory.Cont.holValueAt_self ha (s₀ := s₀) (by linarith)
  have h1 : npow r (s₀ - s₀) = 1 := by simp [npow_eq_exp hr]
  have hm := hg.mul hh
  simp only [h1, one_mul] at hm
  exact hm.congr ⟨σ, fun s hs => (e s hs).symm⟩

end GlobalTheory.StdUnn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HolomorphicContinuationValueNnrealPowFactorStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicContinuationValue_nnrealPow_factor : ∀ (h h' : ℂ → ℂ) (s₀ c : ℂ) (r : ℝ≥0) (σ : ℝ), 0 < r → HolValueAt h s₀ c → (∀ s : ℂ, σ < s.re → h' s = npow r (s₀ - s) * h s) → HolValueAt h' s₀ c := by
  first | exact @GlobalTheory.StdUnn.holValueAt_npow_sub_mul | exact GlobalTheory.StdUnn.holValueAt_npow_sub_mul | (intros; apply GlobalTheory.StdUnn.holValueAt_npow_sub_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousTraceMul
noncomputable section

section Cont

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta

theorem GlobalTheory.Core.Rk.SplitPsi.continuous_trace_mul (D : D7) (a : AE D) :
    Continuous fun z : AE D => Algebra.trace (AF D.host.F) (AE D) (a * z) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have hT : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  exact hT.comp (continuous_const.mul continuous_id)

end Cont

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW GlobalTheory.Core.Rk.SWQ
open Formalism.UG (IsUnifV qV Ov ordL diagJ)
open GlobalTheory.LFun (KGL toCompl IsSplitChart IsSatVecGL satEig)
open scoped Classical

namespace GlobalTheory.Core.Rk.SplitPsi

variable {D : D7} {q : FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)}

end GlobalTheory.Core.Rk.SplitPsi

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalAdelicPointOfUnitaryBaseSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalAdelicPointOfUnitaryBaseSpace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem exists_GQ_of_unitary {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {n : ℕ} (hn : V.rank = n)
    (γ : GL (Fin n) D.host.E)
    (hγ : γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)
      (Matrix.reindex (finCongr hn) (finCongr hn) (HSpace.gram V))) :
    ∃ a : GA D V, a ∈ GQ V ∧
      GlobalTheory.AdForm.finM V hn a =
        (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ).1 ∧
      ∀ τ, GlobalTheory.AdForm.infM θ V hn a τ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ : Matrix _ _ _) τ := by
  subst hn
  have hγ' : Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) γ.1 * HSpace.gram V * γ.1 = HSpace.gram V := hγ
  have hmem : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ ∈
      HR (AF D.host.F) (Formalism.L2.Forms.sigD D) (HSpace.gram V) := by
    change Formalism.UG.cT (sigR (AF D.host.F) (Formalism.L2.Forms.sigD D)) (γ.1.map (inclR (F := D.host.F) (AF D.host.F))) *
      (HSpace.gram V).map (inclR (F := D.host.F) (AF D.host.F)) * γ.1.map (inclR (F := D.host.F) (AF D.host.F)) =
      (HSpace.gram V).map (inclR (F := D.host.F) (AF D.host.F))
    have e : Formalism.UG.cT (sigR (AF D.host.F) (Formalism.L2.Forms.sigD D)) (γ.1.map (inclR (F := D.host.F) (AF D.host.F))) =
        (Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) γ.1).map (inclR (F := D.host.F) (AF D.host.F)) := by
      ext i j
      rfl
    rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hγ']
  refine ⟨⟨_, hmem⟩, ⟨γ, hγ', rfl⟩, ?_, fun τ => ?_⟩
  · ext i j
    rfl
  · ext i j
    exact (hθ τ).1 (γ.1 i j)

theorem exists_GQ_of_unitary0 : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ γ : GL (Fin (D.R.N 0)) D.host.E, γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) → ∃ a : GA D (D.sp.X 0), a ∈ GQ (D.sp.X 0) ∧ GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ).1 ∧ ∀ τ, GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ : Matrix _ _ _) τ :=
  fun D θ hθ γ hγ => exists_GQ_of_unitary θ hθ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) γ hγ

end GlobalTheory.Core.Mi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalAdelicPointOfUnitaryBaseSpaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalAdelicPoint_of_unitary_baseSpace : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ γ : GL (Fin (D.R.N 0)) D.host.E, γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) → ∃ a : GA D (D.sp.X 0), a ∈ GQ (D.sp.X 0) ∧ GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ).1 ∧ ∀ τ, GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (γ : Matrix _ _ _) τ := by
  first | exact @GlobalTheory.Core.Mi.exists_GQ_of_unitary0 | exact GlobalTheory.Core.Mi.exists_GQ_of_unitary0 | (intros; apply GlobalTheory.Core.Mi.exists_GQ_of_unitary0 <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedOfIsCMUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeSublatticePullbackAlongEmbedding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsKActOfStable
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

namespace GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isKAct_of_stable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (hs : ∀ x ∈ kFin M τ, x ∈ GlobalTheory.SmVec.smSub (gramAt D V τ) (M.rep τ))
    (hd : ∀ X ∈ lieAt V τ, ∀ x ∈ kFin M τ, dRep (M.rep τ) X x ∈ kFin M τ) :
    ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ), IsKAct M τ a := by
  have hU : IsUnit (M.fr τ) := M.fr_unit τ
  have hG : IsUnit (gramAt D V τ) := GlobalTheory.SmVec.gram_unit hU (M.fr_gram τ)
  have hπ := GlobalTheory.SmVec.isURepOn_trRep hU (M.fr_gram τ) (M.ds τ).2.2.1
  refine ⟨fun X => if hX : X ∈ lieAt V τ then
    { toFun := fun v => ⟨dRep (M.rep τ) X v, hd X hX v v.2⟩
      map_add' := fun v w => Subtype.ext (GlobalTheory.SmVec.dRep_add (hs v v.2) (hs w w.2) hX)
      map_smul' := fun c v => Subtype.ext (GlobalTheory.SmVec.dRep_smul c (hs v v.2) hX) } else 0, ⟨?_, ?_⟩⟩
  · intro X hX v
    rw [dite_eq_left hX]
    exact GlobalTheory.SmVec.hasDerivAt_dRep (hs v v.2) hX
  · intro X hX v w
    rw [dite_eq_left hX, Submodule.coe_inner, Submodule.coe_inner]
    have key : ⟪(v : M.H τ), dRep (M.rep τ) X w⟫_ℂ = -⟪dRep (M.rep τ) X v, (w : M.H τ)⟫_ℂ :=
      GlobalTheory.SmVec.inner_dRep hG hπ (hs v v.2) (hs w w.2) hX
    change ⟪dRep (M.rep τ) X v, (w : M.H τ)⟫_ℂ + ⟪(v : M.H τ), dRep (M.rep τ) X w⟫_ℂ = 0
    linear_combination key

theorem kFin_smooth_isKAct : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ) (m : ℤ) (U : M.H τ → R.U.H), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R M τ φ m U → kFin M τ ≤ M.sm τ ∧ ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ), IsKAct M τ a := by
  intro D V S M τ p q T R φ m U hM
  have hk : ∀ y : M.H τ, y ∈ kFin M τ ↔ U y ∈ Set.range R.ι := fun y => hM.kfin y
  have hsm : ∀ y ∈ kFin M τ, y ∈ GlobalTheory.SmVec.smSub (gramAt D V τ) (M.rep τ) := fun y hy =>
    GlobalTheory.SmVec.mem_smSub.2 (hM.smooth y ((hk y).1 hy))
  refine ⟨fun y hy => Submodule.subset_span (hM.smooth y ((hk y).1 hy)), exists_isKAct_of_stable M τ hsm ?_⟩
  intro X hX y hy
  rw [← hM.lie] at hX
  obtain ⟨Z, hZ, rfl⟩ := hX
  obtain ⟨v, hv⟩ := (hk y).1 hy
  exact (hk _).2 ⟨_, (hM.der Z hZ v y hv.symm).symm⟩

end GlobalTheory.Chain.IoLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSumFiniteCoordsOfInfinitePartZero
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSumFiniteCoordsOfInfinitePartZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InfZeroFinSum

open Module

theorem repr_map_id {F A A' E ι : Type*} [Field F] [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A']
    [CommRing E] [Algebra F E] [Fintype ι] [DecidableEq ι] (b : Basis ι F E) (f : A →ₐ[F] A')
    (z : A ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis A' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) z) k
      = f ((Algebra.TensorProduct.basis A b).repr z k) := by
  have hz : z = ∑ i, (Algebra.TensorProduct.basis A b).repr z i • (Algebra.TensorProduct.basis A b) i :=
    ((Algebra.TensorProduct.basis A b).sum_repr z).symm
  have hm : Algebra.TensorProduct.map f (AlgHom.id F E) z
      = ∑ i, f ((Algebra.TensorProduct.basis A b).repr z i) • (Algebra.TensorProduct.basis A' b) i := by
    conv_lhs => rw [hz]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rw [hm, (Algebra.TensorProduct.basis A' b).repr_sum_self]

theorem eq_sum_of_fst_zero {F Ai Afn E ι : Type*} [Field F] [CommRing Ai] [Algebra F Ai] [CommRing Afn]
    [Algebra F Afn] [CommRing E] [Algebra F E] [Fintype ι] [DecidableEq ι] (b : Basis ι F E)
    (z : (Ai × Afn) ⊗[F] E)
    (hz : Algebra.TensorProduct.map (AlgHom.fst F Ai Afn) (AlgHom.id F E) z = 0) :
    z = ∑ k, ((0 : Ai), (Algebra.TensorProduct.basis Afn b).repr
      (Algebra.TensorProduct.map (AlgHom.snd F Ai Afn) (AlgHom.id F E) z) k) ⊗ₜ[F] b k := by
  have h1 : ∀ k, ((Algebra.TensorProduct.basis (Ai × Afn) b).repr z k).1 = 0 := by
    intro k
    have := repr_map_id b (AlgHom.fst F Ai Afn) z k
    rw [hz, map_zero] at this
    simpa using this.symm
  conv_lhs => rw [← (Algebra.TensorProduct.basis (Ai × Afn) b).sum_repr z]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [repr_map_id b (AlgHom.snd F Ai Afn) z k]
  have hc : (Algebra.TensorProduct.basis (Ai × Afn) b).repr z k
      = ((0 : Ai), AlgHom.snd F Ai Afn ((Algebra.TensorProduct.basis (Ai × Afn) b).repr z k)) :=
    Prod.ext (h1 k) rfl
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact congrArg (fun x => x ⊗ₜ[F] b k) hc

end GlobalTheory.InfZeroFinSum

theorem GlobalTheory.InfZeroFinSum.eq_sum_finCoord_of_infPart_eq_zero : ∀ (D : D7) (z : AE D), infPart D z = 0 → z = ∑ k, pairA D.host.F 0 (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (GlobalTheory.HolDict.ShortVec.finPr D z) k) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k := by
  intro D z hz
  exact GlobalTheory.InfZeroFinSum.eq_sum_of_fst_zero (Module.finBasis D.host.F D.host.E) z hz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSumFiniteCoordsOfInfinitePartZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_sum_finiteCoords_of_infinitePart_zero : ∀ (D : D7) (z : AE D), infPart D z = 0 → z = ∑ k, pairA D.host.F 0 (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (GlobalTheory.HolDict.ShortVec.finPr D z) k) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k := by
  first | exact @GlobalTheory.InfZeroFinSum.eq_sum_finCoord_of_infPart_eq_zero | exact GlobalTheory.InfZeroFinSum.eq_sum_finCoord_of_infPart_eq_zero | (intros; apply GlobalTheory.InfZeroFinSum.eq_sum_finCoord_of_infPart_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartEqSumTraceTraceDualBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartEqSumTraceTraceDualBasis
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistCoords

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem trace_tmul_base {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [CommRing R] [Algebra F R] (r : R) (x : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] x) = r * algebraMap F R (Algebra.trace F E x) := by
  have h1 : (r ⊗ₜ[F] x : R ⊗[F] E) = r • ((1 : R) ⊗ₜ[F] x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem repr_eq_trace {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (x : E) (l : ι) :
    Algebra.trace F E
        ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b l * x) = b.repr x l := by
  have h := congrArg (Algebra.traceForm F E
      ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b l)) (b.sum_repr x)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h
  simp only [map_smul, LinearMap.BilinForm.apply_dualBasis_left, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [Algebra.traceForm_apply] at h
  exact h.symm

theorem coords_gen (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃ (d : ℕ) (c e : Fin d → E), ∀ w : AF F ⊗[F] E,
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) w =
        ∑ l, sndA F (Algebra.trace (AF F) (AF F ⊗[F] E) (((1 : AF F) ⊗ₜ[F] c l) * w)) ⊗ₜ[F] e l := by
  classical
  let b := Module.finBasis F E
  refine ⟨_, fun l => (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b l, b, ?_⟩
  intro w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_tmul_base, map_mul,
      AlgHom.commutes, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    simp only [repr_eq_trace]
    conv_lhs => rw [← b.sum_repr x]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, mul_add, ← Finset.sum_add_distrib, TensorProduct.add_tmul]

end GlobalTheory.TwistCoords

namespace GlobalTheory.TwistCoords

theorem finPart_eq_sum_trace :
    ∀ (D : D7), ∃ (d : ℕ) (c e : Fin d → D.host.E), ∀ w : AE D, finPart D w =
      ∑ l, sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) (incA D (c l) * w)) ⊗ₜ[D.host.F] e l := by
  intro D
  obtain ⟨d, c, e, h⟩ := coords_gen D.host.F D.host.E
  exact ⟨d, c, e, fun w => h w⟩

end GlobalTheory.TwistCoords
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartEqSumTraceTraceDualBasisStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePart_eq_sum_trace_traceDualBasis : ∀ (D : D7), ∃ (d : ℕ) (c e : Fin d → D.host.E), ∀ w : AE D, finPart D w = ∑ l, sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) (incA D (c l) * w)) ⊗ₜ[D.host.F] e l := by
  first | exact @GlobalTheory.TwistCoords.finPart_eq_sum_trace | exact GlobalTheory.TwistCoords.finPart_eq_sum_trace | (intros; apply GlobalTheory.TwistCoords.finPart_eq_sum_trace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSpacesIsometricOfRankSignature
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSpacesIsometricOfRankSignature
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.RationalIsometry
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus GlobalTheory.LocalConjugacy

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem exists_congr (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) {r : ℕ} {J J' : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (Jᵀ a b) = Jᵀ b a) (hG' : ∀ a b, cc (J'ᵀ a b) = J'ᵀ b a)
    (hd : J.det ≠ 0) (hd' : J'.det ≠ 0) {L L' : Submodule (𝓞 E) (Fin r → E)}
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L')
    (hsd : ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm Jᵀ x y))
    (hsd' : ∀ x, x ∈ L' ↔ ∀ y ∈ L', IsIntegral ℤ (herm J'ᵀ x y))
    (hs : ∀ τ : E →+* ℂ, ∃ p q, Formalism.UG.HasSignature (J.map τ) p q ∧ Formalism.UG.HasSignature (J'.map τ) p q) :
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ ∀ x y, herm Jᵀ (P *ᵥ x) (P *ᵥ y) = herm J'ᵀ x y := by
  haveI := GlobalTheory.DefiniteMass.unramified_of_isCMUnram hc
  have hone : ∀ z : E, z ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ IsIntegral ℤ z := fun z =>
    (FractionalIdeal.mem_one_iff _).trans ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  obtain ⟨P, hP0, hP⟩ := congr_of_modular (G := Jᵀ) (G' := J'ᵀ) (L := L) (L' := L') (𝔟 := 1)
    (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt one_ne_zero
    (fun z hz => by
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hz
      exact (FractionalIdeal.mem_one_iff _).2 ⟨IsCMField.ringOfIntegersComplexConj E a, rfl⟩)
    hG hG' (by rwa [Matrix.det_transpose]) (by rwa [Matrix.det_transpose]) hL hL'
    (by simpa only [hone] using hsd) (by simpa only [hone] using hsd')
    (fun τ => by
      obtain ⟨p, q, h, h'⟩ := hs τ
      obtain ⟨f⟩ : Nonempty (Fin r ≃ Fin p ⊕ Fin q) := ⟨h.choose⟩
      obtain ⟨A, hA, e⟩ := GlobalTheory.FlagMeas.exists_congr_of_hasSignature h f
      obtain ⟨A', hA', e'⟩ := GlobalTheory.FlagMeas.exists_congr_of_hasSignature h' f
      refine GlobalTheory.Published.Landherr.congr_of_gram_eq τ hA hA' ?_
      rw [GlobalTheory.Published.gram_eq, GlobalTheory.Published.gram_eq]
      exact e.trans e'.symm)
  exact ⟨P, hP0, fun x y => by rw [herm_mulVec, ← hP]⟩

theorem gram_herm (W : HSpace E) (a b : Fin W.rank) : cc (W.gramᵀ a b) = W.gramᵀ b a :=
  W.herm.eq (W.frame b) (W.frame a)

theorem exists_isometry (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) (W Y : HSpace E) (hW : W.SigOK) (hY : Y.SigOK)
    (hr : W.rank = Y.rank) (hs : ∀ τ, W.sig τ = Y.sig τ) :
    ∃ φ : W.V ≃ₗ[E] Y.V, HSpace.IsIsomEmb W Y φ.toLinearMap := by
  obtain @⟨V, i1, i2, i3, i4, i5, hT, hh, hn, r, hrk, fr, sg, L, hL, hu⟩ := Y
  change W.rank = r at hr
  subst hr
  let Y : HSpace E := ⟨V, hT, hh, hn, W.rank, hrk, fr, sg, L, hL, hu⟩
  obtain ⟨P, hP0, hP⟩ := exists_congr hc (r := W.rank) (J := Y.gram) (J' := W.gram) (gram_herm Y) (gram_herm W)
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit Y).ne_zero (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W).ne_zero
    (isLattice_coordLat Y Y.L0 Y.standardTuple_isLattice Y.baseLattice_isUnimodular)
    (isLattice_coordLat W W.L0 W.standardTuple_isLattice W.baseLattice_isUnimodular)
    (selfDual_coordLat Y Y.L0 Y.baseLattice_isUnimodular) (selfDual_coordLat W W.L0 W.baseLattice_isUnimodular)
    (fun τ => ⟨_, _, hY τ, by have := hW τ; rwa [hs τ] at this⟩)
  refine ⟨(W.frame.equivFun.trans (Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP0.isUnit))).trans
    Y.frame.equivFun.symm, fun x y => ?_⟩
  change Y.hT (Y.frame.equivFun.symm (P *ᵥ W.frame.equivFun x))
    (Y.frame.equivFun.symm (P *ᵥ W.frame.equivFun y)) = _
  rw [← herm_coord, ← herm_coord, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact hP _ _

end

theorem rationalSt (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RationalSt D :=
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  fun W Y hW hY hr hs => exists_isometry (E := D.host.E) D.sp.cm.cmUnram W Y hW hY hr hs

end GlobalTheory.RationalIsometry

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSpacesIsometricOfRankSignatureStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianSpaces_isometric_of_rank_signature : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RationalSt D := by
  first | exact @GlobalTheory.RationalIsometry.rationalSt | exact GlobalTheory.RationalIsometry.rationalSt | (intros; apply GlobalTheory.RationalIsometry.rationalSt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ApplyMulTorProd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ConjHol

variable {D : D7} {S T : HSp D}

def torProd (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (s : D.what₂.Tau → Fin V.rank → ℝ) : GA D V :=
  (Finset.univ.toList.map fun ρ => torAt θ V B ρ (s ρ)).prod

def conjL {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} : Frame Ψ r →ₗ[ℝ] Frame Ψ r where
  toFun Z := fun τ a b => conj (Z τ a b)
  map_add' Z Z' := funext fun τ => funext fun a => funext fun b => map_add (starRingEnd ℂ) _ _
  map_smul' c Z := funext fun τ => funext fun a => funext fun b => by
    change conj ((c : ℂ) * Z τ a b) = (c : ℂ) * conj (Z τ a b)
    rw [map_mul, Complex.conj_ofReal]

theorem mat_conjL {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (Z : Frame Ψ r) (τ : Ψ) :
    mat (conjL Z) τ = (mat Z τ).map (starRingEnd ℂ) := rfl

def toLieC (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas) :
    Frame C.X.Ψ T.rank →ₗ[ℝ] GlobalTheory.SmoothForms.LieN T :=
  (GlobalTheory.HolRead.AdExt.toLie R B (fun ρ => C.m.e ρ)).comp conjL

theorem isUnit_det_B (C : Ctx S T) {B : C.Bas} (hB : C.IsB B) (ρ : D.what₂.Tau) : IsUnit (B ρ).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have := congrArg det (hB ρ)
  rw [det_mul, det_mul, h0, mul_zero, sgnM, det_diagonal] at this
  refine Finset.prod_ne_zero_iff.2 (fun c _ => ?_) this.symm
  unfold sgn
  split_ifs <;> norm_num

theorem exp_map_conj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (NormedSpace.exp A).map (starRingEnd ℂ) = NormedSpace.exp (A.map (starRingEnd ℂ)) := by
  have h : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.map (starRingEnd ℂ) = Mᴴᵀ := fun M => by
    ext i j
    simp [conjTranspose_apply]
  rw [h, h, Matrix.exp_transpose, Matrix.exp_conjTranspose]

def trLin (V : HSp D) (m : D.what₂.Tau → ℤ) : GlobalTheory.SmoothForms.LieN V →ₗ[ℝ] ℂ where
  toFun Y := ∑ ρ, (m ρ : ℂ) * trace (Y ρ).1
  map_add' Y Y' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    change (m ρ : ℂ) * trace ((Y ρ).1 + (Y' ρ).1) = _
    rw [trace_add, mul_add]
  map_smul' c Y := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    change (m ρ : ℂ) * trace (c • (Y ρ).1) = c • ((m ρ : ℂ) * trace (Y ρ).1)
    rw [trace_smul, mul_smul_comm]

def trCL (V : HSp D) (m : D.what₂.Tau → ℤ) : GlobalTheory.SmoothForms.LieN V →L[ℝ] ℂ where
  toLinearMap := trLin V m
  cont := continuous_finsetSum _ fun ρ _ =>
    continuous_const.mul ((continuous_subtype_val.comp (continuous_apply ρ)).matrix_trace)

theorem trCL_apply (V : HSp D) (m : D.what₂.Tau → ℤ) (Y : GlobalTheory.SmoothForms.LieN V) : trCL V m Y = trLin V m Y := rfl

end GlobalTheory.AdSpan.ConjHol

namespace GlobalTheory.AdSpan.ConjHol

variable {D : D7} {S T : HSp D}

theorem apply_mul_torProd (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (w : D.what₂.Tau → Fin V.rank → ℤ) (ψ : GA D V → ℂ)
    (h : ∀ (ρ : D.what₂.Tau) (t : Fin V.rank → ℝ) (g : GA D V),
      ψ (g * torAt θ V B ρ t) = cexp (((∑ a, (w ρ a : ℝ) * t a : ℝ) : ℂ) * I) * ψ g)
    (s : D.what₂.Tau → Fin V.rank → ℝ) (g : GA D V) :
    ψ (g * torProd θ V B s) = cexp (((∑ ρ, ∑ a, (w ρ a : ℝ) * s ρ a : ℝ) : ℂ) * I) * ψ g := by
  unfold torProd
  suffices H : ∀ l : List D.what₂.Tau, l.Nodup → ∀ g, ψ (g * (l.map fun ρ => torAt θ V B ρ (s ρ)).prod) =
      cexp (((∑ ρ ∈ l.toFinset, ∑ a, (w ρ a : ℝ) * s ρ a : ℝ) : ℂ) * I) * ψ g by
    have := H (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _) g
    rwa [Finset.toList_toFinset] at this
  intro l hl
  induction l with
  | nil => intro g; simp
  | cons ρ l ih =>
    intro g
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, ← mul_assoc, ih hl.2, h, List.toFinset_cons,
      Finset.sum_insert (by simpa using hl.1), ← mul_assoc, ← Complex.exp_add, ← add_mul]
    congr 3
    push_cast
    ring

theorem xB_mvB_mul (C : Ctx S T) (B : C.Bas) (hB : C.IsB B) (a k : GA D T) (b : Frame C.X.Ψ T.rank)
    (hk : ∀ ρ, compAt C.θ ρ (Formalism.L2.Theta.mt T k) = B ρ * (mat b (C.m.e ρ)).map (starRingEnd ℂ) * (B ρ)⁻¹) :
    C.xB (C.mvB (a * k) B) = rmul (C.xB (C.mvB a B)) b := by
  have R : GlobalTheory.SmoothForms.RealPoints C.θ T := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T
  funext σ i j
  obtain ⟨ρ, rfl⟩ := C.m.e.surjective σ
  have e1 : C.mvB (a * k) B ρ = C.mvB a B ρ * (mat b (C.m.e ρ)).map (starRingEnd ℂ) := by
    have hm : compAt C.θ ρ (Formalism.L2.Theta.mt T (a * k)) =
        compAt C.θ ρ (Formalism.L2.Theta.mt T a) * compAt C.θ ρ (Formalism.L2.Theta.mt T k) := R.2.2.2.1 a k ρ
    simp only [Ctx.mvB]
    rw [hm, hk]
    simp only [Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det_B C hB ρ), Matrix.mul_one]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Ctx.xB, rmul, mat, Equiv.symm_apply_apply, e1, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply,
    map_sum, map_mul, Complex.conj_conj]

end GlobalTheory.AdSpan.ConjHol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsIrrOfEquiv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFinIrr

private lemma act_mem_of_forall_upq_act_mem {p q : ℕ} (N : GKMod p q) (W : Submodule ℂ N.V)
    (h : ∀ Z ∈ upq p q, ∀ y ∈ W, N.act Z y ∈ W) : ∀ Z, ∀ y ∈ W, N.act Z y ∈ W := by
  intro Z y hy
  have hre := h _ (GlobalTheory.AdjDescent.re_mem_upq Z) y hy
  have him := h _ (GlobalTheory.AdjDescent.im_mem_upq Z) y hy
  have hZ := GlobalTheory.AdjDescent.decomp Z
  generalize Z + conjR Z = A at hZ hre
  generalize Complex.I • (Z - conjR Z) = B at hZ him
  rw [hZ, map_add (f := _), map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
  exact W.add_mem (W.smul_mem _ hre) (W.smul_mem _ him)

private lemma comm_act_of_comm_act_upq {p q : ℕ} (N : GKMod p q) (T : N.V →ₗ[ℂ] N.V)
    (h : ∀ Z ∈ upq p q, T ∘ₗ N.act Z = N.act Z ∘ₗ T) : ∀ Z, T ∘ₗ N.act Z = N.act Z ∘ₗ T := by
  intro Z
  have hre := h _ (GlobalTheory.AdjDescent.re_mem_upq Z)
  have him := h _ (GlobalTheory.AdjDescent.im_mem_upq Z)
  have hZ := GlobalTheory.AdjDescent.decomp Z
  generalize Z + conjR Z = A at hZ hre
  generalize Complex.I • (Z - conjR Z) = B at hZ him
  rw [hZ, map_add (f := _), map_smul, map_smul, LinearMap.comp_add, LinearMap.add_comp,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.smul_comp, hre, him]

theorem absIrr_of_equiv {p q : ℕ} (N : GKMod p q) (hI : Formalism.MainNotions.SchurIrreducible.IrrGK N) (hA : Formalism.MainNotions.SchurIrreducible.AdmGK N)
    {G K : Type} [AddCommGroup K] [Module ℂ K] (a : G → Module.End ℂ K) (e : K ≃ₗ[ℂ] N.V)
    (h : ∀ Z ∈ upq p q, ∃ (g : G) (c : ℂ), ∀ x, e (a g x) = N.act Z (e x) + c • e x) : AbsIrr a := by
  have hy : ∀ Z ∈ upq p q, ∃ (g : G) (c : ℂ), ∀ x, N.act Z (e x) = e (a g x - c • x) := by
    intro Z hZ
    obtain ⟨g, c, hg⟩ := h Z hZ
    refine ⟨g, c, fun x => ?_⟩
    rw [map_sub, map_smul, hg, add_sub_cancel_right]
  refine ⟨fun W hW => ?_, fun T hT => ?_⟩
  · have hst : ∀ Z ∈ upq p q, ∀ y ∈ W.map (e : K →ₗ[ℂ] N.V), N.act Z y ∈ W.map (e : K →ₗ[ℂ] N.V) := by
      rintro Z hZ _ ⟨x, hx, rfl⟩
      obtain ⟨g, c, hg⟩ := hy Z hZ
      have hmem : a g x - c • x ∈ W := W.sub_mem (hW g x hx) (W.smul_mem c hx)
      have hout := Submodule.mem_map_of_mem (f := (e : K →ₗ[ℂ] N.V)) hmem
      simpa [hg] using hout
    rcases hI.2 _ (act_mem_of_forall_upq_act_mem N _ hst) with h0 | h1
    · left
      rw [eq_bot_iff]
      intro x hx
      have hx' : (e : K →ₗ[ℂ] N.V) x ∈ W.map (e : K →ₗ[ℂ] N.V) := Submodule.mem_map_of_mem hx
      rw [h0, Submodule.mem_bot] at hx'
      rw [Submodule.mem_bot]
      simpa using hx'
    · right
      rw [eq_top_iff]
      intro x _
      have hx' : (e : K →ₗ[ℂ] N.V) x ∈ W.map (e : K →ₗ[ℂ] N.V) := by rw [h1]; trivial
      obtain ⟨y, hyW, hyx⟩ := Submodule.mem_map.mp hx'
      have hxy : y = x := e.injective hyx
      exact hxy ▸ hyW
  · have hc : ∀ Z ∈ upq p q, ((e : K →ₗ[ℂ] N.V) ∘ₗ T ∘ₗ (e.symm : N.V →ₗ[ℂ] K)) ∘ₗ N.act Z =
        N.act Z ∘ₗ ((e : K →ₗ[ℂ] N.V) ∘ₗ T ∘ₗ (e.symm : N.V →ₗ[ℂ] K)) := by
      intro Z hZ
      obtain ⟨g, c, hg⟩ := hy Z hZ
      have hTg : ∀ x, T (a g x) = a g (T x) := fun x => LinearMap.congr_fun (hT g) x
      ext y
      obtain ⟨x, rfl⟩ := e.surjective y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hg, LinearEquiv.symm_apply_apply, map_sub, map_smul, hTg]
    obtain ⟨c, hc'⟩ := GlobalTheory.IrrTensor.schur N hI hA _ (comm_act_of_comm_act_upq N _ hc)
    refine ⟨c, LinearMap.ext fun x => e.injective ?_⟩
    have hx := LinearMap.congr_fun hc' (e x)
    simpa using hx

theorem absIrr_kFin : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ) (m : ℤ) (U : M.H τ ≃ₗ[ℂ] R.U.H) (a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R M τ φ m U → Formalism.MainNotions.SchurIrreducible.IrrGK R.HK → Formalism.MainNotions.SchurIrreducible.AdmGK R.HK → IsKAct M τ a → AbsIrr fun X : lieAt V τ => a X := by
  intro D V S M τ p q T R φ m U a hM hI hA hK
  have hfin : ∀ x : kFin M τ, U x ∈ LinearMap.range R.ι := fun x =>
    LinearMap.mem_range.mpr ((hM.kfin x.1).mp x.2)
  have hequiv : ∃ e : kFin M τ ≃ₗ[ℂ] R.HK.V, ∀ y, R.ι (e y) = U y := by
    let f : kFin M τ →ₗ[ℂ] LinearMap.range R.ι :=
      LinearMap.codRestrict (LinearMap.range R.ι) ((U : M.H τ →ₗ[ℂ] R.U.H) ∘ₗ (kFin M τ).subtype) hfin
    have hf : ∀ y, (f y : R.U.H) = U y := fun y => rfl
    have hbij : Function.Bijective f := by
      constructor
      · intro x y hxy
        have hv : U x = U y := by rw [← hf, ← hf, hxy]
        exact Subtype.ext (U.injective hv)
      · rintro ⟨y, hy⟩
        have hk : U.symm y ∈ kFin M τ := by
          refine (hM.kfin _).mpr ?_
          rw [U.apply_symm_apply]
          exact LinearMap.mem_range.mp hy
        refine ⟨⟨U.symm y, hk⟩, Subtype.ext ?_⟩
        rw [hf]
        exact U.apply_symm_apply y
    let e2 := LinearEquiv.ofInjective R.ι R.ι_inj
    refine ⟨(LinearEquiv.ofBijective f hbij).trans e2.symm, fun y => ?_⟩
    have h3 := congrArg Subtype.val (e2.apply_symm_apply (f y))
    rw [LinearEquiv.ofInjective_apply, hf] at h3
    exact h3
  obtain ⟨e, hιe⟩ := hequiv
  refine absIrr_of_equiv R.HK hI hA (fun X : lieAt V τ => a X) e ?_
  intro Z hZ
  have hX : IndefiniteRowSideFullHecke.BarMatrix.toFrame M τ (φ Z) ∈ lieAt V τ := by
    rw [← hM.lie]
    exact ⟨Z, hZ, rfl⟩
  have hd : ∀ x : kFin M τ, dRep (M.rep τ) (IndefiniteRowSideFullHecke.BarMatrix.toFrame M τ (φ Z)) (x : M.H τ) =
      (a (IndefiniteRowSideFullHecke.BarMatrix.toFrame M τ (φ Z)) x : M.H τ) := fun x =>
    (hK.der _ hX x).deriv
  refine ⟨⟨_, hX⟩, (m : ℂ) / 2 * Z.trace, fun x => R.ι_inj ?_⟩
  show R.ι (e (a (IndefiniteRowSideFullHecke.BarMatrix.toFrame M τ (φ Z)) x)) = R.ι (R.HK.act Z (e x) + ((m : ℂ) / 2 * Z.trace) • e x)
  rw [hιe, ← hM.der Z hZ (e x) x (hιe x).symm, hd x]

end GlobalTheory.KFinIrr

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermHeisenbergIsotropicCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermHeisenbergIsotropicCharacter
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTermTranslate

variable {D : D7}

theorem symplOH_isoPart_isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (hC : IsIsoFrame V C)
    (b a : Mx D W.rank r) : symplOH V W (isoPart V W C b) (isoPart V W C a) = 0 := by
  have rat_mul {l m n : ℕ} (M : Matrix (Fin l) (Fin m) D.host.E)
      (N : Matrix (Fin m) (Fin n) D.host.E) :
      GlobalTheory.MixModel.rat (M * N) = GlobalTheory.MixModel.rat M * GlobalTheory.MixModel.rat N := Matrix.map_mul
  have adj_mul {l m n : ℕ} (x : Mx D l m) (y : Mx D m n) :
      GlobalTheory.MixModel.adj (x * y) = GlobalTheory.MixModel.adj y * GlobalTheory.MixModel.adj x :=
    Formalism.UG.cT_mul (cA D) x y
  have hO_eq_trace (x y : WO V W) :
      hO V W x y = (GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.gA W * x))).trace := by
    simp only [hO, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
    rfl
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
    rw [← rat_mul, ← rat_mul]
    have : adj D C * V.gram * V.gram⁻¹ * (V.gram * C) = adj D C * V.gram * C := by
      rw [Matrix.mul_assoc (adj D C * V.gram), ← Matrix.mul_assoc V.gram⁻¹,
        Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
    rw [this]
    exact (congrArg GlobalTheory.MixModel.rat hC.2.2).trans GlobalTheory.MixModel.rat_zero
  rw [GlobalTheory.MixModel.symplOH_eq, hO_eq_trace]
  have e2 : isoPart V W C b = b * X := rfl
  have e3 : isoPart V W C a = a * X := rfl
  rw [e2, e3, adj_mul]
  have e4 : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj X * GlobalTheory.MixModel.adj a * (GlobalTheory.MixModel.gA W * (b * X)))
      = (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj X * GlobalTheory.MixModel.adj a * GlobalTheory.MixModel.gA W * b) * X := by
    simp only [Matrix.mul_assoc]
  rw [e4, Matrix.trace_mul_comm]
  have e5 : X * (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj X * GlobalTheory.MixModel.adj a * GlobalTheory.MixModel.gA W * b)
      = (X * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj X) * (GlobalTheory.MixModel.adj a * GlobalTheory.MixModel.gA W * b) := by
    simp only [Matrix.mul_assoc]
  rw [e5, hX0, Matrix.zero_mul, Matrix.trace_zero, map_zero]

theorem symplO_eq_add (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add (f := _)]
  norm_num

theorem heisO_heisO_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (G : WO S T → ℂ) (u v a : WO S T)
    (hav : symplOH S T a v = 0) :
    heisO ψ S T u (heisO ψ S T v G) a =
      ψ (symplO S T u v) * (ψ (symplOH S T (a + v) u) * G (a + v + u)) := by
  simp only [heisO]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_right_comm a u v]
  congr 2
  rw [GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_left, hav, symplO_eq_add,
    GlobalTheory.FinTranslate.symplOH_skew S T v u]
  ring

end GlobalTheory.MixedTermTranslate

namespace GlobalTheory.MixedTermTranslate

theorem term_heisO_isoPart : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r), term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (isoPart V W C κ) G) y = phase ψ V W C C' y κ * term ψ V V' W C C' B μ 𝓨 G y := by
  intro D V V' W r C C' B hs ψ _ μ 𝓨 hμ G hG y κ
  have hμ' : IsCovolOne (GlobalTheory.MixModel.ratMx D W.rank r) μ 𝓨 := hμ
  have hmid : midPart V V' W B 0 = 0 := by
    show HMul.hMul (0 : Matrix (Fin W.rank) (Fin V'.rank) (AE D)) _ = 0
    exact Matrix.zero_mul _
  have iso := symplOH_isoPart_isoPart V W C hs.frame
  obtain ⟨u, hu⟩ : ∃ u, u = isoPart V W C' (Matrix.map y (incA D)) := ⟨_, rfl⟩
  have hterm : ∀ F : WO V W → ℂ, term ψ V V' W C C' B μ 𝓨 F y =
      ∫ s in 𝓨, heisO ψ V W u F (isoPart V W C s) ∂μ := by
    intro F
    show ∫ s in 𝓨, heisO ψ V W _ F (isoPart V W C s + midPart V V' W B 0) ∂μ = _
    rw [hmid, hu]
    simp only [add_zero]
  let Ψ : Mx D W.rank r → ℂ := fun s => ψ (symplOH V W (isoPart V W C s) u) * G (isoPart V W C s + u)
  have hper : ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank r, ∀ s, Ψ (γ + s) = Ψ s := by
    rintro _ ⟨q₀, rfl⟩ s
    have e3 : (incA D).toAddMonoidHom.mapMatrix q₀ = q₀.map (incA D) := rfl
    simp only [Ψ]
    rw [e3, GlobalTheory.TwistEquiRat.isoPart_add, add_assoc (isoPart V W C (q₀.map (incA D))),
      ← GlobalTheory.TwistEquiRat.ratW_eq_isoPart V W C q₀, hG.quasi, GlobalTheory.TwistEquiRat.ratW_eq_isoPart V W C q₀,
      GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_right, iso, zero_add, AddChar.map_add_eq_mul]
    have h1 : ψ (symplOH V W (isoPart V W C (q₀.map (incA D))) u) *
        ψ (-(symplOH V W (isoPart V W C (q₀.map (incA D))) u)) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    linear_combination (ψ (symplOH V W (isoPart V W C s) u) * G (isoPart V W C s + u)) * h1
  have hph : phase ψ V W C C' y κ = ψ (symplO V W u (isoPart V W C κ)) := by rw [hu]; rfl
  have key : ∀ s, heisO ψ V W u (heisO ψ V W (isoPart V W C κ) G) (isoPart V W C s) =
      phase ψ V W C C' y κ * Ψ (s + κ) := by
    intro s
    rw [heisO_heisO_apply ψ V W G u _ _ (iso s κ), hph]
    show _ = _ * (ψ (symplOH V W (isoPart V W C (s + κ)) u) * G (isoPart V W C (s + κ) + u))
    rw [GlobalTheory.TwistEquiRat.isoPart_add]
  rw [hterm, hterm]
  simp only [key]
  rw [integral_const_mul, GlobalTheory.MixModel.covolOne_integral_add hμ' Ψ hper κ]
  rfl

end GlobalTheory.MixedTermTranslate

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermHeisenbergIsotropicCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelTerm_heisenbergIsotropic_character : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r), term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (isoPart V W C κ) G) y = phase ψ V W C C' y κ * term ψ V V' W C C' B μ 𝓨 G y := by
  first | exact @GlobalTheory.MixedTermTranslate.term_heisO_isoPart | exact GlobalTheory.MixedTermTranslate.term_heisO_isoPart | (intros; apply GlobalTheory.MixedTermTranslate.term_heisO_isoPart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryImage
open Formalism.BasicNotions Formalism.BasicNotions.TH
open scoped TensorProduct InnerProductSpace Classical Kronecker
open GlobalTheory.Chain.IoLift

noncomputable section

namespace GlobalTheory.Chain.IoLift.UImg

variable {p q : ℕ}

def sumAct (M : GKMod p q) (Y : Type) : Mat p q →ₗ[ℂ] Module.End ℂ (Y →₀ M.V) where
  toFun X := Finsupp.mapRange.linearMap (M.act X)
  map_add' X X' := by
    refine LinearMap.ext fun v => Finsupp.ext fun y => ?_
    simp
  map_smul' c X := by
    refine LinearMap.ext fun v => Finsupp.ext fun y => ?_
    simp

theorem sumAct_apply (M : GKMod p q) (Y : Type) (X : Mat p q) (v : Y →₀ M.V) (y : Y) :
    sumAct M Y X v y = M.act X (v y) := by
  simp [sumAct]

theorem sumAct_single (M : GKMod p q) (Y : Type) (X : Mat p q) (y : Y) (x : M.V) :
    sumAct M Y X (Finsupp.single y x) = Finsupp.single y (M.act X x) := by
  simp [sumAct]

def sumMod (M : GKMod p q) (Y : Type) : GKMod p q where
  V := Y →₀ M.V
  act := sumAct M Y
  lie X X' := by
    refine LinearMap.ext fun v => Finsupp.ext fun y => ?_
    rw [sumAct_apply, M.lie X X']
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Finsupp.sub_apply, sumAct_apply]
  kfin v := by
    induction v using Finsupp.induction_linear with
    | zero => exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun X _ w hw => by
        rw [Submodule.mem_bot] at hw ⊢; rw [hw, map_zero]⟩
    | add f g hf hg =>
      obtain ⟨W, hW, hf, hK⟩ := hf
      obtain ⟨W', hW', hg, hK'⟩ := hg
      refine ⟨W ⊔ W', inferInstance, Submodule.add_mem_sup hf hg, fun X hX w hw => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (hK X hX a ha) (hK' X hX b hb)
    | single y x =>
      obtain ⟨W, hW, hx, hK⟩ := M.kfin x
      refine ⟨W.map (Finsupp.lsingle y), inferInstance, Submodule.mem_map_of_mem hx, ?_⟩
      rintro X hX _ ⟨w, hw, rfl⟩
      rw [Finsupp.lsingle_apply, sumAct_single]
      exact Submodule.mem_map_of_mem (f := Finsupp.lsingle y) (hK X hX w hw)
  wts v := by
    induction v using Finsupp.induction_linear with
    | zero => exact Submodule.zero_mem _
    | add f g hf hg => exact Submodule.add_mem _ hf hg
    | single y x =>
      have h : (⨆ μ : Ix p q → ℚ, wtSub M.act μ) ≤
          (⨆ μ : Ix p q → ℚ, wtSub (sumAct M Y) μ).comap (Finsupp.lsingle y) := by
        refine iSup_le fun μ x hx => ?_
        rw [Submodule.mem_comap]
        refine Submodule.mem_iSup_of_mem μ ?_
        simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
        intro a
        rw [Finsupp.lsingle_apply, sumAct_single, Finsupp.smul_single, ← Finsupp.single_sub, hx a,
          Finsupp.single_zero]
      exact h (M.wts x)

def fockMod (p q r s : ℕ) : GKMod p q where
  V := Pol p q r s
  act := fockAct1 p q r s
  lie X X' := by
    have h : ∀ U : Mat p q, fockAct1 p q r s U = omAct p q r s (U ⊗ₖ (1 : Mat r s)) := fun _ => rfl
    rw [map_sub]
    simp only [h]
    rw [← GlobalTheory.FockLie.omAct_lie, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, map_sub]
  kfin P := ((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).1 P).1
  wts P := ((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).1 P).2

theorem exists_unitary_image (M : GKMod p q) (Y Z : Type) [AddCommGroup Y] [Module ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] (B : M.V →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z)
    (hB : ∀ (X : Mat p q) P P' y y',
      ⟪B (M.act X P) y, B P' y'⟫_ℂ = ⟪B P y, B (M.act (adjZ X) P') y'⟫_ℂ) :
    ∃ (A : UGKMod p q) (j : A.M.V →ₗ[ℂ] Z) (B' : M.V →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] A.M.V),
      Function.Injective j ∧ (∀ P y, j (B' P y) = B P y) ∧
        Submodule.span ℂ {x | ∃ P y, B' P y = x} = ⊤ ∧
        ∀ X P y, B' (M.act X P) y = A.M.act X (B' P y) := by
  let E : (Y →₀ M.V) →ₗ[ℂ] Z := Finsupp.lsum ℂ fun y => B.flip y
  have hE1 : ∀ y P, E (Finsupp.single y P) = B P y := fun y P => by
    simp [E]
  have hE : ∀ X (x x' : Y →₀ M.V), ⟪E (sumAct M Y X x), E x'⟫_ℂ =
      ⟪E x, E (sumAct M Y (adjZ X) x')⟫_ℂ := by
    intro X x x'
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add (f := _), inner_add_left, hf, hg]
    | single y P =>
      induction x' using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => simp only [map_add (f := _), inner_add_right, hf, hg]
      | single y' P' => simp only [sumAct_single, hE1, hB]
  obtain ⟨A, f, j, hf, hj, hjf, hact⟩ :=
    GlobalTheory.GKQuot.exists_unitary_quotient p q (sumMod M Y) Z E hE
  let g : (Y →₀ M.V) →ₗ[ℂ] A.M.V := f
  have hjg : ∀ y P, j (g (Finsupp.single y P)) = B P y := fun y P => (hjf _).trans (hE1 y P)
  let B' : M.V →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] A.M.V :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun P y => g (Finsupp.single y P))
      (fun P P' y => by rw [Finsupp.single_add, map_add (f := _)])
      (fun c P y => by rw [← Finsupp.smul_single, map_smul, RingHom.id_apply])
      (fun P y y' => hj (by rw [map_add (f := _), hjg, hjg, hjg, map_add (f := _)]))
      (fun c P y => hj (by rw [map_smul, hjg, hjg, map_smulₛₗ]))
  have hB' : ∀ P y, B' P y = g (Finsupp.single y P) := fun _ _ => rfl
  refine ⟨A, j, B', hj, fun P y => hjg y P, ?_, fun X P y => ?_⟩
  · rw [eq_top_iff]
    rintro x -
    obtain ⟨v, rfl⟩ : ∃ v, g v = x := hf x
    induction v using Finsupp.induction_linear with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
    | single y P => exact Submodule.subset_span ⟨P, y, rfl⟩
  · rw [hB', hB', ← sumAct_single]
    exact hact X _

theorem unitaryImage : ∀ p q r s : ℕ, UnitaryImage p q r s :=
  fun p q r s Y Z _ _ _ _ B hB => exists_unitary_image (fockMod p q r s) Y Z B hB

end GlobalTheory.Chain.IoLift.UImg

end
end

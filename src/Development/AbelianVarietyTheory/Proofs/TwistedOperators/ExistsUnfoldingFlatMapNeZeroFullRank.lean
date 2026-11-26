module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatMapProductDatumEqUnitriangularIntegralBumpStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassConditionsIsotropicHomFromFirstMixedCoordinStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassConditionsCoreFromMixedCoordinateFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingConditionsFromSecondMixedCoordinateStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterEqRealPartCharOnBumpSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterEqRealPartCharOnBumpSupport
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFinSupp

theorem eq_zero_of_parts {D : D7} {m n : ℕ} (z : Mx D m n) (h1 : z.map (infPart D) = 0) (h2 : z.map (finPart D) = 0) : z = 0 := by
  apply (GlobalTheory.AscFinInhab.coordH D m n).injective
  rw [GlobalTheory.AscFinInhab.coordH_apply, GlobalTheory.AscFinInhab.coordH_apply, (GlobalTheory.AscFinInhab.RCh_eq_zero_iff z).2 h1,
    (GlobalTheory.AscFinInhab.FCh_eq_zero_iff z).2 h2, map_zero, map_zero]

theorem smul_eInf_eq_zero {D : D7} {m n : ℕ} (a : Mx D m n) (h : a.map (infPart D) = 0) :
    GlobalTheory.FinTranslate.eInf D • a = 0 := by
  apply eq_zero_of_parts
  · ext i j
    have h0 : infPart D (a i j) = 0 := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, map_mul, h0, mul_zero]
  · ext i j
    exact GlobalTheory.ThetaClosed.finPart_eInf_smul (a i j)

theorem smul_one_sub_eInf_eq_zero {D : D7} {m n : ℕ} (r : Mx D m n) (h : r.map (finPart D) = 0) :
    (1 - GlobalTheory.FinTranslate.eInf D) • r = 0 := by
  apply eq_zero_of_parts
  · ext i j
    exact GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul (r i j)
  · ext i j
    have h0 : finPart D (r i j) = 0 := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, map_mul, h0, mul_zero]

theorem upper_of_UX {D : D7} {ρ : ℕ} (u : UX D ρ) : ∀ i j, j ≤ i → ((u.1.1 : Mx D ρ ρ) - 1) i j = 0 := by
  have hU : (u.1 : GL (Fin ρ) (AE D)) ∈ GlobalTheory.UniIndexPrime.uniSub ρ (AE D) := u.2
  rw [GlobalTheory.UniIndexPrime.mem_uniSub] at hU
  obtain ⟨h1, h2⟩ := hU
  intro i j hij
  rcases hij.lt_or_eq with h | h
  · have e1 : (u.1.1 : Mx D ρ ρ) i j = 0 := h1 i j h
    have e2 : (1 : Mx D ρ ρ) i j = 0 := Matrix.one_apply_ne (ne_of_gt h)
    rw [Matrix.sub_apply, e1, e2, sub_zero]
  · subst h
    have e1 : (u.1.1 : Mx D ρ ρ) j j = 1 := h2 j
    rw [Matrix.sub_apply, e1, Matrix.one_apply_eq, sub_self]

theorem split_parts {D : D7} {m ρ : ℕ} (x : Mx D m ρ) (N : Mx D ρ ρ) (r a : Mx D m ρ) (hxN : x ⬝ N = r + a)
    (hr : r.map (finPart D) = 0) (ha : a.map (infPart D) = 0) :
    x ⬝ ((1 - GlobalTheory.FinTranslate.eInf D) • N) = a ∧ x ⬝ (GlobalTheory.FinTranslate.eInf D • N) = r := by
  have hea := smul_eInf_eq_zero a ha
  have her := smul_one_sub_eInf_eq_zero r hr
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_smul, hxN, smul_add, her, zero_add, sub_smul, one_smul, hea, sub_zero]
  · rw [Matrix.mul_smul, hxN, smul_add, hea, add_zero]
    have h := her
    rw [sub_smul, one_smul, sub_eq_zero] at h
    exact h.symm

theorem main_part {D : D7} {ρ : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (u : UX D ρ) (N : Mx D ρ ρ) (hN : (u.1.1 : Mx D ρ ρ) = 1 + N)
    (h1 : psiE ψ (upSum ((1 - GlobalTheory.FinTranslate.eInf D) • N)) = 1) :
    psiUni ψ u.1 = psiE ψ (upSum (GlobalTheory.FinTranslate.eInf D • N)) := by
  have hsplit : N = GlobalTheory.FinTranslate.eInf D • N + (1 - GlobalTheory.FinTranslate.eInf D) • N := by
    rw [sub_smul, one_smul, add_sub_cancel]
  show psiE ψ (upSum u.1.1) = _
  rw [hN, GlobalTheory.AscFinInhab.upSum_add', GlobalTheory.AscFinInhab.upSum_one', zero_add, hsplit,
    GlobalTheory.AscFinInhab.upSum_add', psiE_add, h1, mul_one, ← hsplit]

theorem charOnSupport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (L : Matrix (Fin ρ) (Fin W.rank) D.host.E), L * x₀ = 1 → p.Is dV dW (rat x₀) ψ → ∀ (u : UX D ρ) (r : Mx D W.rank ρ), r.map (finPart D) = 0 → rat x₀ ⬝ u.1.1 - (rat x₀ + r) ∈ p.A₁ → psiUni ψ u.1 = psiE ψ (upSum (rat L ⬝ r)) := by
  intro D ψ V V₀ W W₀ ρ σ dV dW p x₀ L hL hp u r hr ha
  have haInf : (rat x₀ ⬝ u.1.1 - (rat x₀ + r)).map (infPart D) = 0 :=
    (GlobalTheory.AscFinInhab.mxAt_true_iff _).1 (hp.a₁.fin _ ha)
  have hxN : rat x₀ ⬝ ((u.1.1 : Mx D ρ ρ) - 1) = r + (rat x₀ ⬝ u.1.1 - (rat x₀ + r)) := by
    rw [Matrix.mul_sub, Matrix.mul_one]; abel
  obtain ⟨h1e, he⟩ := split_parts _ _ _ _ hxN hr haInf
  have hLr : rat L ⬝ r = GlobalTheory.FinTranslate.eInf D • ((u.1.1 : Mx D ρ ρ) - 1) := by
    rw [← he, ← Matrix.mul_assoc, ← rat_mul, hL, rat_one, Matrix.one_mul]
  have hfin : MxAt (fun _ => True) ((1 - GlobalTheory.FinTranslate.eInf D) • ((u.1.1 : Mx D ρ ρ) - 1)) := by
    rw [GlobalTheory.AscFinInhab.mxAt_true_iff]
    ext i j
    exact GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul _
  have hup' : ∀ i j, j ≤ i → ((1 - GlobalTheory.FinTranslate.eInf D) • ((u.1.1 : Mx D ρ ρ) - 1)) i j = 0 := by
    intro i j hij
    rw [Matrix.smul_apply, upper_of_UX u i j hij, smul_zero]
  have hmem : Formalism.L2.Theta.mt W (1 : GA D W)⁻¹ ⬝ (rat x₀ ⬝ ((1 - GlobalTheory.FinTranslate.eInf D) • ((u.1.1 : Mx D ρ ρ) - 1))) ∈ p.A₁ := by
    rw [inv_one, GlobalTheory.AscFinInhab.mt_one_, Matrix.one_mul, h1e]; exact ha
  have hshift := (GlobalTheory.AscFin.cond_one hp (0 : Mx D V₀.rank σ)).shift _ hfin hup' hmem
  rw [hLr]
  exact main_part ψ u _ (by rw [add_sub_cancel]) hshift

end GlobalTheory.AscFinSupp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterEqRealPartCharOnBumpSupportStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericCharacter_eq_realPartChar_on_bumpSupport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (L : Matrix (Fin ρ) (Fin W.rank) D.host.E), L * x₀ = 1 → p.Is dV dW (rat x₀) ψ → ∀ (u : UX D ρ) (r : Mx D W.rank ρ), r.map (finPart D) = 0 → rat x₀ ⬝ u.1.1 - (rat x₀ + r) ∈ p.A₁ → psiUni ψ u.1 = psiE ψ (upSum (rat L ⬝ r)) := by
  first | exact @GlobalTheory.AscFinSupp.charOnSupport | exact GlobalTheory.AscFinSupp.charOnSupport | (intros; apply GlobalTheory.AscFinSupp.charOnSupport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicBumpPeriodicUnderAdjointLatticeStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicBumpPeriodicUnderAdjointLattice
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFinBumpAdj

variable {D : D7}

theorem infPart_conj_eq_zero {a : AE D} (h : infPart D a = 0) : infPart D (cA D a) = 0 := by
  have e : ∀ z : AE D, infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => rfl
    | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]
  rw [e, h, map_zero]

theorem adj_fin {m n : ℕ} {x : Mx D m n} (h : x.map (infPart D) = 0) : (adj x).map (infPart D) = 0 := by
  funext i j
  exact infPart_conj_eq_zero (a := x j i) (congrFun (congrFun h j) i)

theorem smul_fin {m n : ℕ} (c : AE D) {x : Mx D m n} (h : x.map (infPart D) = 0) : (c • x).map (infPart D) = 0 := by
  funext i j
  show infPart D (c * x i j) = 0
  rw [map_mul, show infPart D (x i j) = 0 from congrFun (congrFun h i) j, mul_zero]

theorem continuous_smul_mx {X : Type} [TopologicalSpace X] {m n : ℕ} (c : AE D) {f : X → Mx D m n} (hf : Continuous f) :
    Continuous fun x => c • f x :=
  continuous_matrix fun i j => continuous_const.mul (hf.matrix_elem i j)

variable (S : HSp D) (σ : ℕ)

def adjMap : Mx D S.rank σ →+ Mx D σ S.rank where
  toFun y := incA D (-D.host.xi0⁻¹) • (adj y * gA S)
  map_zero' := by rw [adj_zero, Matrix.zero_mul, smul_zero]
  map_add' _ _ := by rw [adj_add, Matrix.add_mul, smul_add]

def adjInv (η : Mx D σ S.rank) : Mx D S.rank σ := incA D D.host.xi0 • (giA S * adj η)

theorem adjMap_apply (y : Mx D S.rank σ) : adjMap S σ y = incA D (-D.host.xi0⁻¹) • (adj y * gA S) := rfl

theorem adjInv_adjMap (y : Mx D S.rank σ) : adjInv S σ (adjMap S σ y) = y := by
  rw [adjInv, adjMap_apply, adj_smul, adj_mul, adj_adj, adj_gA, Matrix.mul_smul, giA_gA_cancel, smul_smul,
    HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv, one_smul]

theorem adjMap_adjInv (η : Mx D σ S.rank) : adjMap S σ (adjInv S σ η) = η := by
  have h : incA D (-D.host.xi0⁻¹) * cA D (incA D D.host.xi0) = 1 := by
    have h1 := congrArg (cA D) (HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv (D := D))
    rw [map_mul, map_one, GlobalTheory.DualPairCheck.cA_cA] at h1
    rw [mul_comm, h1]
  rw [adjInv, adjMap_apply, adj_smul, adj_mul, adj_adj, adj_giA, Matrix.smul_mul, Matrix.mul_assoc, giA_mul_gA,
    Matrix.mul_one, smul_smul, h, one_smul]

theorem continuous_adjMap : Continuous (adjMap S σ) :=
  continuous_smul_mx _ (f := fun y : Mx D S.rank σ => (adj y * gA S : Mx D σ S.rank))
    (continuous_adj.matrix_mul continuous_const)

theorem continuous_adjInv : Continuous (adjInv S σ) :=
  continuous_smul_mx _ (f := fun η : Mx D σ S.rank => (giA S * adj η : Mx D S.rank σ))
    (continuous_const.matrix_mul continuous_adj)

theorem adjMap_fin {y : Mx D S.rank σ} (h : y.map (infPart D) = 0) : (adjMap S σ y).map (infPart D) = 0 :=
  smul_fin _ (by rw [Matrix.map_mul, adj_fin h, Matrix.zero_mul])

theorem adjInv_fin {η : Mx D σ S.rank} (h : η.map (infPart D) = 0) : (adjInv S σ η).map (infPart D) = 0 :=
  smul_fin _ (by rw [Matrix.map_mul, adj_fin h, Matrix.mul_zero])

theorem finLat_comap {B : AddSubgroup (Mx D σ S.rank)} (hB : FinLat B) : FinLat (B.comap (adjMap S σ)) := by
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · rw [← adjInv_adjMap S σ a]
    exact (GlobalTheory.AscFinInhab.mxAt_true_iff _).2 (adjInv_fin S σ ((GlobalTheory.AscFinInhab.mxAt_true_iff _).1 (hB.fin _ ha)))
  · have e : ((B.comap (adjMap S σ) : AddSubgroup _) : Set (Mx D S.rank σ)) = adjInv S σ '' (B : Set _) := by
      ext a
      constructor
      · intro ha
        exact ⟨_, ha, adjInv_adjMap S σ a⟩
      · rintro ⟨η, hη, rfl⟩
        show adjMap S σ (adjInv S σ η) ∈ B
        rw [adjMap_adjInv]
        exact hη
    rw [e]
    exact hB.cpt.image (continuous_adjInv S σ)
  · obtain ⟨U, hU, h0, hUB⟩ := hB.opn
    refine ⟨adjMap S σ ⁻¹' U, hU.preimage (continuous_adjMap S σ), by rw [Set.mem_preimage, map_zero]; exact h0,
      fun a ha hf => ?_⟩
    exact hUB _ ha ((GlobalTheory.AscFinInhab.mxAt_true_iff _).2 (adjMap_fin S σ ((GlobalTheory.AscFinInhab.mxAt_true_iff _).1 hf)))

theorem exists_bump_adj : ∀ (D : D7) (V₀ W W₀ : HSp D) (σ : ℕ) (dW : HypDec W W₀ σ) (B₂ : AddSubgroup (Mx D σ V₀.rank)), FinLat B₂ → ∀ y : Mx D V₀.rank σ, ∃ β : Mx D V₀.rank σ → ℂ, IsBump β ∧ β y ≠ 0 ∧ (∀ η ∈ B₂, ∀ b, dW.incAdj V₀ b = dW.incY V₀ η → ∀ z, β (z + b) = β z) ∧ ∀ z, β z ≠ 0 → ∃ r : Mx D V₀.rank σ, r.map (finPart D) = 0 ∧ ∃ η ∈ B₂, dW.incAdj V₀ (z - (y + r)) = dW.incY V₀ η := by
  intro D V₀ W W₀ σ dW B₂ hB y
  obtain ⟨b, hb, hby, -, hs, hp⟩ := exists_bump_le y (B₂.comap (adjMap V₀ σ)) (finLat_comap V₀ σ hB) Set.univ Filter.univ_mem
  refine ⟨fun z => (b z : ℂ), hb, by simp [hby], fun η hη c hc z => ?_, fun z hz => ?_⟩
  · have h1 : dW.pY * (dW.jY * adjMap V₀ σ c) = dW.pY * (dW.jY * η) := congrArg (fun w : WO V₀ W => dW.pY * (show Mx D W.rank V₀.rank from w)) hc
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, dW.pY_jY, Matrix.one_mul, Matrix.one_mul] at h1
    have h2 : c ∈ B₂.comap (adjMap V₀ σ) := by
      rw [AddSubgroup.mem_comap, h1]; exact hη
    beta_reduce
    rw [hp c h2 z]
  · obtain ⟨r, hr, -, hz'⟩ := hs z (fun h => hz (by simp [h]))
    exact ⟨r, hr, _, hz', rfl⟩

end GlobalTheory.AscFinBumpAdj

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicBump_periodic_under_adjointLattice : ∀ (D : D7) (V₀ W W₀ : HSp D) (σ : ℕ) (dW : HypDec W W₀ σ) (B₂ : AddSubgroup (Mx D σ V₀.rank)), FinLat B₂ → ∀ y : Mx D V₀.rank σ, ∃ β : Mx D V₀.rank σ → ℂ, IsBump β ∧ β y ≠ 0 ∧ (∀ η ∈ B₂, ∀ b, dW.incAdj V₀ b = dW.incY V₀ η → ∀ z, β (z + b) = β z) ∧ ∀ z, β z ≠ 0 → ∃ r : Mx D V₀.rank σ, r.map (finPart D) = 0 ∧ ∃ η ∈ B₂, dW.incAdj V₀ (z - (y + r)) = dW.incY V₀ η := by
  first | exact @GlobalTheory.AscFinBumpAdj.exists_bump_adj | exact GlobalTheory.AscFinBumpAdj.exists_bump_adj | (intros; apply GlobalTheory.AscFinBumpAdj.exists_bump_adj <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactUnitriangularOfRationalMulMemCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactUnitriangularOfRationalMulMemCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin

theorem det_eq_one_of_upperUni {A : Type} [CommRing A] {ρ : ℕ} {M : Matrix (Fin ρ) (Fin ρ) A}
    (h : ∀ i j : Fin ρ, (j < i → M i j = 0) ∧ M i i = 1) : M.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => (h i j).1 hij)]
  simp [fun i => (h i i).2]

theorem mem_UX_iff_entries {D : D7} {ρ : ℕ} (v : GL (Fin ρ) (AE D)) :
    v ∈ UX D ρ ↔ ∀ i j : Fin ρ, (j < i → v.val i j = 0) ∧ v.val i i = 1 := Iff.rfl

theorem exists_unit_of_upperUni {A : Type} [CommRing A] {ρ : ℕ} {M : Matrix (Fin ρ) (Fin ρ) A}
    (h : ∀ i j : Fin ρ, (j < i → M i j = 0) ∧ M i i = 1) :
    ∃ v : GL (Fin ρ) A, v.val = M ∧ (v⁻¹).val = M.adjugate := by
  have hdet := det_eq_one_of_upperUni h
  refine ⟨⟨M, M.adjugate, ?_, ?_⟩, rfl, rfl⟩
  · rw [Matrix.mul_adjugate, hdet, one_smul]
  · rw [Matrix.adjugate_mul, hdet, one_smul]

theorem isCompact_setOf_rat_mul_mem : ∀ (D : D7) (n ρ : ℕ) (x₀ : Matrix (Fin n) (Fin ρ) D.host.E), LinearIndependent D.host.E x₀.transpose → ∀ K : Set (Mx D n ρ), IsCompact K → IsCompact {u : UX D ρ | rat x₀ ⬝ u.1.1 ∈ K} := by
  intro D n ρ x₀ hx K hK
  obtain ⟨-, hT2, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hinj : Function.Injective x₀.mulVec := Matrix.mulVec_injective_iff.2 hx
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin x₀) (LinearMap.ker_eq_bot.2 hinj)
  have hL : LinearMap.toMatrix' g * x₀ = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  have hLr : rat (LinearMap.toMatrix' g) ⬝ rat x₀ = (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) := by
    simp only [rat]
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  set S' : Set (Matrix (Fin ρ) (Fin ρ) (AE D)) :=
    {M | (∀ i j : Fin ρ, (j < i → M i j = 0) ∧ M i i = 1) ∧ rat x₀ ⬝ M ∈ K} with hS'def
  have hC : IsCompact ((fun N : Mx D n ρ => rat (LinearMap.toMatrix' g) ⬝ N) '' K) :=
    hK.image (continuous_const.matrix_mul continuous_id)
  have hsub : S' ⊆ (fun N : Mx D n ρ => rat (LinearMap.toMatrix' g) ⬝ N) '' K := by
    rintro M ⟨-, hM⟩
    exact ⟨_, hM, by simp only [← Matrix.mul_assoc, hLr, Matrix.one_mul]⟩
  have hcl : IsClosed S' := by
    rw [hS'def, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter (isClosed_iInter fun i => ?_) (hK.isClosed.preimage ((continuous_const (y := (rat x₀ : Mx D n ρ))).matrix_mul (continuous_id (X := Matrix (Fin ρ) (Fin ρ) (AE D)))))
    rw [Set.setOf_forall]
    refine isClosed_iInter fun j => ?_
    rw [Set.setOf_and]
    exact (isClosed_imp isOpen_const (isClosed_eq (by fun_prop) continuous_const)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  have hS' : IsCompact S' := hC.of_isClosed_subset hcl hsub
  let ι : UX D ρ → Matrix (Fin ρ) (Fin ρ) (AE D) × (Matrix (Fin ρ) (Fin ρ) (AE D))ᵐᵒᵖ := fun u => Units.embedProduct _ u.1
  have hι : Topology.IsEmbedding ι := Units.isEmbedding_embedProduct.comp Topology.IsEmbedding.subtypeVal
  have hF : Continuous (fun M : Matrix (Fin ρ) (Fin ρ) (AE D) => (M, MulOpposite.op M.adjugate)) :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_adjugate)
  have heq : ι '' {u : UX D ρ | rat x₀ ⬝ u.1.1 ∈ K} = (fun M : Matrix (Fin ρ) (Fin ρ) (AE D) => (M, MulOpposite.op M.adjugate)) '' S' := by
    ext p
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hU : ∀ i j : Fin ρ, (j < i → u.1.1 i j = 0) ∧ u.1.1 i i = 1 := u.2
      refine ⟨u.1.1, ⟨hU, hu⟩, ?_⟩
      have hdet := det_eq_one_of_upperUni hU
      refine Prod.ext rfl ?_
      show MulOpposite.op u.1.1.adjugate = MulOpposite.op (Units.val (u.1)⁻¹)
      congr 1
      rw [Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
    · rintro ⟨M, ⟨hU, hM⟩, rfl⟩
      have hdet := det_eq_one_of_upperUni hU
      obtain ⟨v, hv1, hv2⟩ := exists_unit_of_upperUni hU
      subst hv1
      have hmem : v ∈ UX D ρ := (mem_UX_iff_entries v).2 hU
      refine ⟨⟨v, hmem⟩, hM, ?_⟩
      exact Prod.ext rfl (congrArg MulOpposite.op hv2)
  rw [hι.isInducing.isCompact_iff, heq]
  exact hS'.image hF

end GlobalTheory.AscFin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactUnitriangularOfRationalMulMemCompactStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_unitriangular_of_rational_mul_mem_compact : ∀ (D : D7) (n ρ : ℕ) (x₀ : Matrix (Fin n) (Fin ρ) D.host.E), LinearIndependent D.host.E x₀.transpose → ∀ K : Set (Mx D n ρ), IsCompact K → IsCompact {u : UX D ρ | rat x₀ ⬝ u.1.1 ∈ K} := by
  first | exact @GlobalTheory.AscFin.isCompact_setOf_rat_mul_mem | exact GlobalTheory.AscFin.isCompact_setOf_rat_mul_mem | (intros; apply GlobalTheory.AscFin.isCompact_setOf_rat_mul_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PositiveRealPartTraceCharacterMemNhds
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PositiveRealPartTraceCharacterMemNhds
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.PosNhdsChar

theorem posNhds : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (n ρ : ℕ) (L : Mx D ρ n) (x : Mx D n ρ), {z : Mx D n ρ | 0 < (star (psiE ψ (upSum (L ⬝ (z - x))))).re} ∈ nhds x := by
  intro D ψ hψ n ρ L x
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)
  have hlin : ∀ c : AE D, Continuous fun a : AE D => c * a := fun c =>
    IsModuleTopology.continuous_of_linearMap (LinearMap.mulLeft (AF D.host.F) c)
  have htr : Continuous fun a : AE D => Algebra.trace (AF D.host.F) (AE D) a :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hψc : Continuous ψ := hψ.1.1
  have hcont : Continuous fun z : Mx D n ρ => star (psiE ψ (upSum (L ⬝ (z - x)))) := by
    refine continuous_star.comp (hψc.comp (htr.comp ?_))
    unfold upSum
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    split_ifs
    · simp only [Matrix.mul_apply, Matrix.sub_apply]
      refine continuous_finsetSum _ fun k _ => ?_
      have hk : Continuous fun z : Mx D n ρ => z k j - x k j := by
        simp only [sub_eq_add_neg]
        exact (continuous_id.matrix_elem k j).add continuous_const
      exact (hlin (L i k)).comp hk
    · exact continuous_const
  refine IsOpen.mem_nhds (isOpen_lt continuous_const (Complex.continuous_re.comp hcont)) ?_
  show (0:ℝ) < (star (psiE ψ (upSum (L ⬝ (x - x))))).re
  simp [upSum, psiE]

end GlobalTheory.PosNhdsChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PositiveRealPartTraceCharacterMemNhdsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positiveRealPart_traceCharacter_mem_nhds : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (n ρ : ℕ) (L : Mx D ρ n) (x : Mx D n ρ), {z : Mx D n ρ | 0 < (star (psiE ψ (upSum (L ⬝ (z - x))))).re} ∈ nhds x := by
  first | exact @GlobalTheory.PosNhdsChar.posNhds | exact GlobalTheory.PosNhdsChar.posNhds | (intros; apply GlobalTheory.PosNhdsChar.posNhds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnfoldingFlatMapNeZeroFullRank
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFinNe

variable {D : D7}

theorem left_inv_of_li {n ρ : ℕ} (x₀ : Matrix (Fin n) (Fin ρ) D.host.E) (h : LinearIndependent D.host.E x₀.transpose) :
    ∃ L : Matrix (Fin ρ) (Fin n) D.host.E, L * x₀ = 1 := by
  have hinj : Function.Injective (Matrix.toLin' x₀) := by
    show Function.Injective x₀.mulVec
    exact mulVec_injective_iff.mpr h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' x₀) (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  conv_lhs => rw [← LinearMap.toMatrix'_toLin' x₀]
  rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

theorem flat_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ p : Pieces V₀ W W₀ ρ σ, p.Is dV dW (rat x₀) ψ → ∃ Φ ∈ cls dV dW p (rat x₀) y ψ, flatS dV dW s (rat x₀) y Φ ≠ 0 := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW s x₀ y hx₀ p hp
  obtain ⟨g, hgv, hg0⟩ := hp.vac₀
  obtain ⟨β₂, hβ₂, hβ₂y, hβ₂per, hβ₂supp⟩ := GlobalTheory.T.exists_adelicBump_periodic_under_adjointLattice D V₀ W W₀ σ dW p.B₂ hp.b₂ y
  obtain ⟨L, hL⟩ := left_inv_of_li x₀ hx₀
  obtain ⟨b, hb, hbx, hb01, hbsupp, hbper⟩ := exists_bump_le (rat x₀) p.A₁ hp.a₁ _
    (GlobalTheory.T.positiveRealPart_traceCharacter_mem_nhds D ψ hψ W.rank ρ (rat L) (rat x₀))
  have hpos : ∀ u : UX D ρ, b (rat x₀ ⬝ u.1.1) ≠ 0 → 0 < (star (psiUni ψ u.1)).re := by
    intro u hu
    obtain ⟨r, hr, hrU, hrA⟩ := hbsupp _ hu
    rw [GlobalTheory.T.genericCharacter_eq_realPartChar_on_bumpSupport D ψ V V₀ W W₀ ρ σ dV dW p x₀ L hL hp u r hr hrA]
    simpa only [Set.mem_setOf_eq, add_sub_cancel_left] using hrU
  have hcpt : HasCompactSupport (fun u : UX D ρ => b (rat x₀ ⬝ u.1.1)) := by
    refine HasCompactSupport.intro' (GlobalTheory.T.isCompact_unitriangular_of_rational_mul_mem_compact D W.rank ρ x₀ hx₀ _ (HasCompactSupport.isCompact (f := fun z => (b z : ℂ)) hb.supp))
      ((isClosed_tsupport _).preimage (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val))) ?_
    intro u hu
    by_contra h
    exact hu (subset_tsupport _ (by simpa using h))
  obtain ⟨g', hg', hg'm⟩ := GlobalTheory.T.mixedModelTarget_bump_mul_coreTheta_exists D ψ hψ V₀ W W₀ σ dW s.vT β₂ g hβ₂ hgv.1
  obtain ⟨Φ, hΦ, hΦm⟩ := GlobalTheory.T.exists_thetaFunction_mixedCoordinate_bump_mul_core D ψ hψ V V₀ W ρ dV s.vS (fun z => (b z : ℂ)) g' hb hg'
  have hbper' : ∀ a ∈ p.A₁, ∀ z, (fun z => (b z : ℂ)) (z + a) = (fun z => (b z : ℂ)) z := fun a ha z => by
    simp only [hbper a ha z]
  have hbsupp' : ∀ z, (fun z => (b z : ℂ)) z ≠ 0 → ∃ r : Mx D W.rank ρ, r.map (finPart D) = 0 ∧ z - (rat x₀ + r) ∈ p.A₁ :=
    fun z hz => by
      obtain ⟨r, hr, -, hrA⟩ := hbsupp z (by simpa using hz)
      exact ⟨r, hr, hrA⟩
  obtain ⟨hB₁, hB₂, hvac⟩ := GlobalTheory.T.unfolding_conditions_from_second_mixedCoordinate D ψ hψ V V₀ W W₀ ρ σ dV dW s.vT p (rat x₀) y hp β₂ g g' hgv hg' hg'm hβ₂per hβ₂supp
  obtain ⟨hA₁, hA₂⟩ := GlobalTheory.T.class_conditions_isotropicHom_from_firstMixedCoordinate D ψ hψ V V₀ W W₀ ρ σ dV dW s.vS p (rat x₀) hp _ g' Φ hΦ hΦm hbper' hbsupp'
  obtain ⟨hC₁, hC₂, hCv⟩ := GlobalTheory.T.class_conditions_core_from_mixedCoordinateFunction D ψ hψ V V₀ W W₀ ρ σ dV dW s.vS p y _ g' Φ hg' hΦ hΦm hB₁ hB₂ hvac
  refine ⟨Φ, ⟨hΦ, hA₁, hA₂, hC₁, hC₂, hCv⟩, ?_⟩
  exact GlobalTheory.T.flatMap_productDatum_eq_unitriangularIntegral_bump D ψ hψ V V₀ W W₀ ρ σ dV dW s (rat x₀) y b β₂ g g' Φ hg0 hβ₂y hΦm hg'm
    (Complex.continuous_re.comp hb.cont |>.congr fun z => by simp) hbx (fun z => (hb01 z).1) hpos hcpt

end GlobalTheory.AscFinNe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnfoldingFlatMapNeZeroFullRankStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unfolding_flatMap_ne_zero_fullRank : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ p : Pieces V₀ W W₀ ρ σ, p.Is dV dW (rat x₀) ψ → ∃ Φ ∈ cls dV dW p (rat x₀) y ψ, flatS dV dW s (rat x₀) y Φ ≠ 0 := by
  first | exact @GlobalTheory.AscFinNe.flat_ne_zero | exact GlobalTheory.AscFinNe.flat_ne_zero | (intros; apply GlobalTheory.AscFinNe.flat_ne_zero <;> assumption)
end

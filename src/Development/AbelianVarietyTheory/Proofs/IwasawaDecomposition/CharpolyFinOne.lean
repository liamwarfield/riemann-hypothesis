module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegreeEqTotDeg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeColPts
public import Formalism.LocalToGlobal.Columns.InputsGenus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyFinOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.FitRho

open Formalism.L2.NR

def castQ {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) : Qbar p ≃+* Qbar q := by
  subst h; exact RingEquiv.refl _

theorem exists_heq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (z : ℤ_[p]) : ∃ z' : ℤ_[q], HEq z z' := by
  subst h; exact ⟨z, HEq.rfl⟩

theorem castQ_alg {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (z : ℤ_[p]) (z' : ℤ_[q]) (hz : HEq z z') :
    (castQ h).symm (algebraMap ℚ_[q] (Qbar q) (z' : ℚ_[q])) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p]) := by
  subst h
  obtain rfl := eq_of_heq hz
  rfl

theorem mapRep_mapRep {Γ A B C : Type} [Group Γ] [CommRing A] [CommRing B] [CommRing C] {n : ℕ} (f : A →+* B)
    (g : B →+* C) (ρ : Γ →* GL (Fin n) A) : mapRep g (mapRep f ρ) = mapRep (g.comp f) ρ := by
  ext x i j
  rfl

theorem isRepOf_cast (D : D7) {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (ι : Qbar q ≃+* ℂ) {n : ℕ}
    (π : D.naut.CG n) (s : ℝ) (ρ : G D.host.E D.nd.Om →* GL (Fin n) (Qbar q))
    (hρ : IsRepOf D p ((castQ h).trans ι) π s (mapRep (castQ h).symm.toRingHom ρ)) : IsRepOf D q ι π s ρ := by
  subst h
  have e1 : (castQ (rfl : p = p)).trans ι = ι := by ext x; rfl
  have e2 : mapRep (castQ (rfl : p = p)).symm.toRingHom ρ = ρ := by ext g i j; rfl
  rw [e1, e2] at hρ
  exact hρ

theorem conj_of_isRepOf (D : D7) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (π : D.naut.CG n) (s : ℝ)
    (hC : GlobalTheory.RowTie.ChebSplit D.nd) (ρ₁ ρ₂ : G D.host.E D.nd.Om →* GL (Fin n) (Qbar l))
    (h₁ : IsRepOf D l ι π s ρ₁) (h₂ : IsRepOf D l ι π s ρ₂) : IsConjRep ρ₁ ρ₂ := by
  obtain ⟨c₁, s₁, f₁⟩ := h₁
  obtain ⟨c₂, s₂, f₂⟩ := h₂
  have hfin := (Filter.eventually_cofinite.mp f₁).union (Filter.eventually_cofinite.mp f₂)
  have hcp := GlobalTheory.TwistLG.charpoly_eq_of_dense ρ₁ ρ₂ c₁ c₂ _ (hC hfin.toFinset).closure_eq (by
    rintro g ⟨w, hw, -, B, hB, hg⟩
    rw [Set.Finite.mem_toFinset] at hw
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hw
    apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [hw.1 B g hB hg, hw.2 B g hB hg])
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ₂ ρ₁ s₂ s₁ (fun g => (hcp g).symm)
  exact ⟨P⁻¹, fun g => by rw [hP g, inv_inv]⟩

theorem charpoly_fin_one {k : Type} [CommRing k] (M : Matrix (Fin 1) (Fin 1) k) : M.charpoly = X - C (M 0 0) := by
  rw [Matrix.charpoly, Matrix.det_unique, Matrix.charmatrix_apply_eq]
  rfl

theorem rhoOfRow_isRepOf (D : D7) (hG : GalRepEx D) (hC : ClassFieldHeckeAlgebraic D) (hη : EtaShiftInt D) (a : D.nd.Loc)
    (π : D.naut.CG D.R.r) (hc : D.naut.csd π) (hr : D.naut.ralg π) :
    IsRepOf D (D.nd.l a) (D.naut.iotaQC a) (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2)
      (rhoOfRow D hG hC hη a π hc hr) := by
  obtain ⟨c1, ss1, f1⟩ := rowRho_spec D hG a π hc hr
  obtain ⟨cχ, awayχ, -⟩ := Classical.choose_spec (hC a D.naut.etaTinv (-(D.R.t : ℝ) / 2) hη)
  set χ1 := Classical.choose (hC a D.naut.etaTinv (-(D.R.t : ℝ) / 2) hη) with hχ1
  have e0 : rhoOfRow D hG hC hη a π hc hr =
      Formalism.MainNotions.SumRepresentations.At.twGL (rowRho D hG a π hc hr) (Matrix.GeneralLinearGroup.det.comp χ1) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e0]; exact GlobalTheory.TwistLG.cont_twGL _ _ c1 cχ
  · rw [e0]; exact GlobalTheory.TwistLG.isSSRep_twGL _ _ ss1
  have hfin := placesOver_finite D.host.E (D.nd.l a) (Fact.out : (D.nd.l a).Prime).ne_zero
  filter_upwards [f1, D.naut.locG_unr_ae π, hfin.compl_mem_cofinite] with w hw1 hu hwl
  intro B σ hB hσ
  have hwl' : w ∉ placesOver D.host.E (D.nd.l a) := hwl

  have hue : D.naut.unr (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) :=
    (D.naut.unr_tw _ _).2 (D.naut.etaTinv_def w).1
  obtain ⟨u, hu1⟩ : ∃ u, D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) = {u} := by
    apply Multiset.card_eq_one.mp
    rw [D.naut.frobEig_tw _ _ (D.naut.etaTinv_def w).1, Multiset.card_map,
      D.naut.frobEig_card _ (D.naut.etaTinv_def w).1, D.naut.locG_dim]
  have hwd := D.naut.wdOf_frob a χ1 w hwl' cχ (by rw [awayχ w hwl']; exact hue) B σ hB hσ
  rw [awayχ w hwl', hu1, Multiset.map_singleton, Multiset.prod_singleton, charpoly_fin_one, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C] at hwd
  have hχu : D.naut.iotaQC a ((Matrix.GeneralLinearGroup.det.comp χ1 σ : (Qbar (D.nd.l a))ˣ) : Qbar (D.nd.l a)) = u := by
    have := congrArg (fun p : Polynomial ℂ => p.coeff 0) hwd
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub, neg_inj] at this
    show D.naut.iotaQC a ((χ1 σ : Matrix (Fin 1) (Fin 1) _).det) = u
    rw [Matrix.det_unique]
    exact this

  have h1 := hw1 B σ hB hσ
  rw [isoLoc_single] at h1
  rw [e0, GlobalTheory.TwistLG.twGL_val, ← Matrix.charpoly_map, GlobalTheory.ParamRep.map_smul_matrix,
    GlobalTheory.ParamRep.galPol_twist D.nd D.naut π hu u hu1]
  have h2 : ((((rowRho D hG a π hc hr) σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).map
      (D.naut.iotaQC a).toRingHom).charpoly =
      ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2))).map fun α => X - C α).prod := by
    rw [Matrix.charpoly_map]; exact h1
  have h3 := GlobalTheory.ParamRep.charpoly_smul_of_prod _ u _ h2
  have hχu' : (D.naut.iotaQC a).toRingHom ((Matrix.GeneralLinearGroup.det.comp χ1 σ : (Qbar (D.nd.l a))ˣ) :
      Qbar (D.nd.l a)) = u := hχu
  rw [hχu']
  exact h3

end GlobalTheory.HeightCounting.FitRho

namespace GlobalTheory.HeightCounting.FitRho

open Formalism.L2.NR

theorem fracMap_eq {O0 O : Type} [CommRing O0] [IsDomain O0] [ValuationRing O0] [CommRing O] [IsDomain O]
    (f : O0 →+* O) (hf : Function.Injective f) {F : Type} [Field F] (e : F →+* FractionRing O0)
    (e' : F →+* FractionRing O) (h : ∀ x y, algebraMap O0 _ y = e x → e' x = algebraMap O _ (f y)) (x : F) :
    GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf (e x) = e' x := by
  rcases ValuationRing.isInteger_or_isInteger O0 (e x) with ⟨y, hy⟩ | ⟨y, hy⟩
  · rw [← hy, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg, h x y hy]
  · have hy' : algebraMap O0 (FractionRing O0) y = e x⁻¹ := by rw [map_inv₀]; exact hy
    have h1 := h x⁻¹ y hy'
    have h2 : e x = (algebraMap O0 (FractionRing O0) y)⁻¹ := by rw [hy, inv_inv]
    rw [h2, map_inv₀, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg, ← h1, map_inv₀, inv_inv]

end GlobalTheory.HeightCounting.FitRho

namespace GlobalTheory.HeightCounting.FitRho

open Formalism.L2.NR


end GlobalTheory.HeightCounting.FitRho

namespace GlobalTheory.HeightCounting


end GlobalTheory.HeightCounting
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColInJetsIn
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Col2

namespace JetEx

theorem hasLetters_of_over {K : Ctx} {P : Pre} (h : K.Over P) : StagesInhab.HasLetters P := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  have hx : 0 < K.s.x := zero_lt_one.trans K.s.one_lt_alt
  refine ⟨(Delv K.s K.cD : ℚ), K.c, Nat.cast_pos.2 (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hx _)), K.ok.inj,
    fun w τ l hl => ?_, K.ok.code⟩
  have h1 := (K.ok.hc w).1 τ
  change l + 1 < K.P.R.k - 1 at hl
  show (K.P.hcW w τ).v ⟨l, by omega⟩ - (K.P.hcW w τ).v ⟨l + 1, hl⟩ = _
  rw [h1, h1, show K.P.R.k - 2 - l = K.P.R.k - 2 - (l + 1) + 1 by omega]
  push_cast
  ring

end JetEx

end GlobalTheory.Mem.Col2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseWeightEqForcedLiftWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseWeightEqForcedLiftWeight
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open Formalism.L2.Col

namespace GlobalTheory.Mem.LiftWt

theorem lamLdef_eq_lamV (X : Stages) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ X.B.R.m) (τ) (i : Fin (X.toD7.sp.V j).rank)
    (i' : Fin X.B.R.nV) (e : (i : ℕ) = i') :
    (Bridge.lamLdef (D := X.toD7) (X.toD7.sp.V j).rank j τ).w i = (X.B.wts.lamV j τ).w i' := by
  obtain ⟨hj, W, hk, hm, ht, hjj, he, hv, hb, hw⟩ := GlobalTheory.ForcedWeights.lamLForced X.toD7 j h1 h2 τ
  have hk : W.k = X.B.R.k := hk
  have hm : W.m = X.B.R.m := hm
  have ht : W.t = X.B.R.t := ht
  have he : (W.e : ℚ) = (X.B.hc τ).e ⟨j - 1, hj.2⟩ := he
  have hv : ∀ a : Fin (X.B.R.k - 1), (W.v (a + 2) : ℚ) = (X.B.hc τ).v a := hv
  have hb : ∀ a : Fin X.B.R.m, (W.b (a + 1) : ℚ) = (X.B.hc τ).b a := hb
  have hkm := X.B.R.m_add_three_le_k
  have q := RowPar.lamV_eq (X.B.hc τ) h1 h2 i'
  have hi := i'.2
  have hE : (RowPar.of (X.B.hc τ)).eAt (j - 1) = W.e := by
    rw [he]; exact dif_pos hj.2
  have hB : ∀ n, n < X.B.R.m → (RowPar.of (X.B.hc τ)).bAt n = W.b (n + 1) := fun n hn => by
    rw [hb ⟨n, hn⟩]; exact dif_pos hn
  have key : W.lamPrime (i'.1 + 1) = (RowPar.of (X.B.hc τ)).lamVQ j i' := by
    unfold Ranks.nV Ranks.r at hi
    unfold IndefiniteWeightData.WeightData.lamPrime IndefiniteWeightData.WeightData.thetaWt IndefiniteWeightData.WeightData.dTau IndefiniteWeightData.WeightData.aPlus IndefiniteWeightData.WeightData.aMinus
      IndefiniteWeightData.WeightData.lam IndefiniteWeightData.WeightData.nV IndefiniteWeightData.WeightData.r IndefiniteWeightData.WeightData.p IndefiniteWeightData.WeightData.q
      RowPar.lamVQ RowPar.aPlus RowPar.aMinusRev RowPar.dV RowPar.vb RowPar.pOf RowPar.qOf
    rw [hk, hm, ht, hjj, hE]
    congr 1
    by_cases a : i'.1 < X.B.R.k + j - 1
    · rw [if_pos a, if_pos (show i'.1 + 1 ≤ _ from a), Nat.add_sub_cancel]
      by_cases b : i'.1 < X.B.R.k - 1
      · rw [dif_pos b, if_pos (show i'.1 + 1 ≤ _ from b), hv ⟨_, b⟩]
        rfl
      · rw [dite_eq_right b, if_neg (show ¬ i'.1 + 1 ≤ _ from b), hB _ (by omega), Int.cast_neg,
          show i'.1 + 1 - (X.B.R.k - 1) = i'.1 - (X.B.R.k - 1) + 1 by omega]
        rfl
    · rw [if_neg a, if_neg (show ¬ i'.1 + 1 ≤ _ from a)]
      by_cases b : i'.1 < X.B.R.k + j - 1 + X.B.R.t
      · rw [if_pos b, if_pos (show i'.1 + 1 ≤ _ from b)]
      · rw [if_neg b, if_neg (show ¬ i'.1 + 1 ≤ _ from b), hB _ (by omega),
          show X.B.R.m - j + 1 - (X.B.R.m - j + 1 - (i'.1 + 1 - (X.B.R.k + j - 1) - X.B.R.t)) =
            i'.1 - (X.B.R.k + j - 1 + X.B.R.t) + 1 by omega,
          show j + (i'.1 - (X.B.R.k + j - 1 + X.B.R.t) + 1) - 1 + 1 = j + (i'.1 - (X.B.R.k + j - 1 + X.B.R.t) + 1) by omega]
  have := (hw i).trans ((e ▸ key).trans q.symm)
  exact_mod_cast this

theorem lamV_eq_lamLdef : ∀ (X : Stages) (i : Fin X.toD7.R.m) (τ : X.B.fields.Tau) (a : Fin X.B.R.nV),
    (X.B.wts.lamV ((i : ℕ) + 1) τ).w a =
      (Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ).w (Fin.cast (LiftBrg.rkEq X i) a) := by
  intro X i τ a
  exact (lamLdef_eq_lamV X ((i : ℕ) + 1) (by omega) i.2 τ _ a rfl).symm

end GlobalTheory.Mem.LiftWt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseWeightEqForcedLiftWeightStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseWeight_eq_forcedLiftWeight : ∀ (X : Stages) (i : Fin X.toD7.R.m) (τ : X.B.fields.Tau) (a : Fin X.B.R.nV),
    (X.B.wts.lamV ((i : ℕ) + 1) τ).w a =
      (Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ).w (Fin.cast (LiftBrg.rkEq X i) a) := by
  first | exact @GlobalTheory.Mem.LiftWt.lamV_eq_lamLdef | exact GlobalTheory.Mem.LiftWt.lamV_eq_lamLdef | (intros; apply GlobalTheory.Mem.LiftWt.lamV_eq_lamLdef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterIffIsCuspidalGLnFiniteField
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterIffIsCuspidalGLnFiniteField
open CategoryTheory Polynomial

noncomputable section

namespace GlobalTheory.CuspCharRep

open Formalism.IrreducibleCountingLemmas.TYPES GlobalTheory.GLq GlobalTheory.FiniteGL

variable {g : ℕ} [Fact g.Prime]

theorem mem_unipRadical_twoBlocks_iff {d a : ℕ} (had : a ≤ d) (x : Gn g d) :
    x ∈ unipRadical (ZMod g) (twoBlocks d a) ↔
      (InPar a (x : Mt g d) ∧ tl a (x : Mt g d) = 1 ∧ br a (d - a) (x : Mt g d) = 1) := by
  rw [mem_unipRadical]
  constructor
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_, ?_⟩
    · have := h i j (by simp [twoBlocks]; split_ifs <;> omega)
      have hne : i ≠ j := fun e => by rw [e] at hi; omega
      rwa [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at this
    · funext i j
      have := h ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp [twoBlocks, i.2, j.2])
      rw [Matrix.sub_apply, sub_eq_zero] at this
      simp only [tl, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (show (i : ℕ) < d ∧ (j : ℕ) < d by omega)]
      rw [this]
      simp [Matrix.one_apply, Fin.ext_iff]
    · funext i j
      have := h ⟨a + i, by omega⟩ ⟨a + j, by omega⟩ (by simp [twoBlocks])
      rw [Matrix.sub_apply, sub_eq_zero] at this
      simp only [br, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (show a + (i : ℕ) < d ∧ a + (j : ℕ) < d by omega)]
      rw [this]
      simp [Matrix.one_apply, Fin.ext_iff]
  · rintro ⟨hP, htl, hbr⟩ i j hij
    rw [Matrix.sub_apply, sub_eq_zero]
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
    · have := congrFun (congrFun htl ⟨i, hi⟩) ⟨j, hj⟩
      simp only [tl, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (show (i : ℕ) < d ∧ (j : ℕ) < d from ⟨i.2, j.2⟩)] at this
      rw [this]
      simp [Matrix.one_apply, Fin.ext_iff]
    · exfalso
      simp [twoBlocks, hi, hj] at hij
    · have hne : i ≠ j := fun e => by rw [e] at hi; exact hi hj
      rw [hP i j hj (not_lt.1 hi), Matrix.one_apply_ne hne]
    · have := congrFun (congrFun hbr ⟨i - a, by omega⟩) ⟨j - a, by omega⟩
      simp only [br, Formalism.MainNotions.ArithmeticCylinders.entN] at this
      rw [dif_pos (show a + ((i : ℕ) - a) < d ∧ a + ((j : ℕ) - a) < d by omega)] at this
      have ei : (⟨a + ((i : ℕ) - a), by omega⟩ : Fin d) = i := Fin.ext (by simp; omega)
      have ej : (⟨a + ((j : ℕ) - a), by omega⟩ : Fin d) = j := Fin.ext (by simp; omega)
      rw [ei, ej] at this
      rw [this, Matrix.one_apply, Matrix.one_apply]
      simp only [Fin.ext_iff]
      split_ifs with h1 h2 h2 <;> first | rfl | omega


open scoped Classical in
theorem res_one_one_eq {d a : ℕ} (had : a ≤ d) (χ : Gn g d → ℂ) :
    res a (d - a) χ 1 1 =
      ((g : ℂ) ^ (a * (d - a)))⁻¹ * ∑ u : unipRadical (ZMod g) (twoBlocks d a), χ u := by
  unfold res
  congr 1
  rw [← Finset.sum_filter]
  refine Finset.sum_subtype _ (fun x => ?_) χ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Units.val_one]
  exact (mem_unipRadical_twoBlocks_iff had x).symm


open scoped Classical in
theorem res_character_eq_zero_iff {d a : ℕ} (had : a ≤ d) (V : FDRep ℂ (Gn g d)) :
    res a (d - a) (fun x => V.character x) 1 1 = 0 ↔
      ∀ v : V, (∀ u ∈ unipRadical (ZMod g) (twoBlocks d a), V.ρ u v = v) → v = 0 := by
  rw [res_one_one_eq had, mul_eq_zero]
  have hg : ((g : ℂ) ^ (a * (d - a)))⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero))
  simp only [hg, false_or]
  have h := GlobalTheory.GoodTypeGeneric.sum_character_eq_zero_iff
    (V.ρ.comp (unipRadical (ZMod g) (twoBlocks d a)).subtype)
  have e : ∀ u : unipRadical (ZMod g) (twoBlocks d a),
      Representation.character (V.ρ.comp (unipRadical (ZMod g) (twoBlocks d a)).subtype) u = V.character u := fun u => rfl
  simp only [e] at h
  rw [h]
  constructor
  · intro H v hv
    exact H v fun u => hv u u.2
  · intro H v hv
    exact H v fun u hu => hv ⟨u, hu⟩

def cb (d a : ℕ) : Fin d → Fin 2 := fun i => if (i : ℕ) < a then 0 else 1

theorem val_cb (d a : ℕ) (i : Fin d) : ((cb d a i : Fin 2) : ℕ) = twoBlocks d a i := by
  simp only [cb, twoBlocks]
  split_ifs <;> rfl

theorem mem_unipRadical_of_mem_unip {d a : ℕ} {u : Gn g d} (hu : u ∈ unip (ZMod g) (cb d a)) :
    u ∈ unipRadical (ZMod g) (twoBlocks d a) := by
  obtain ⟨⟨hA, -⟩, hD⟩ := hu
  rw [mem_unipRadical]
  intro i j hij
  rw [Matrix.sub_apply, Matrix.one_apply]
  by_cases e : cb d a i = cb d a j
  · rw [hD i j e]
    simp
  · have hlt : cb d a j < cb d a i := by
      rw [Fin.lt_iff_val_lt_val, val_cb, val_cb]
      have e' : twoBlocks d a i ≠ twoBlocks d a j := fun h => e (Fin.ext (by rw [val_cb, val_cb, h]))
      omega
    have hne : i ≠ j := fun h => e (by rw [h])
    rw [hA i j hlt, if_neg hne, sub_zero]

theorem glEquiv_mem_unip {d a s : ℕ} (b : Fin d → Fin s) (z : Fin s) (hz : ∀ i, z ≤ b i) (σ : Fin d ≃ Fin d)
    (hσ : ∀ k : Fin d, (k : ℕ) < a ↔ b (σ k) = z) {u : Gn g d} (hu : u ∈ unipRadical (ZMod g) (twoBlocks d a)) :
    glEquiv (ZMod g) σ u ∈ unip (ZMod g) b := by
  have htb : ∀ i, twoBlocks d a (σ.symm i) = if b i = z then 0 else 1 := by
    intro i
    have h := hσ (σ.symm i)
    rw [Equiv.apply_symm_apply] at h
    simp only [twoBlocks]
    by_cases hb : b i = z
    · simp [hb, h.2 hb]
    · simp [hb, mt h.1 hb]
  have hent : ∀ w : Gn g d, w ∈ unipRadical (ZMod g) (twoBlocks d a) → ∀ i j, (b j = z ∨ b i ≠ z) →
      ((glEquiv (ZMod g) σ w : Gn g d) : Mt g d) i j = if i = j then 1 else 0 := by
    intro w hw i j hij
    rw [Formalism.L2.PT.coe_glEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]
    have h0 := (mem_unipRadical.1 hw) (σ.symm i) (σ.symm j) (by
      rw [htb, htb]
      rcases hij with h | h
      · by_cases h' : b j = z <;> simp [h, h']
      · by_cases h' : b j = z <;> simp [h, h'])
    rw [Matrix.sub_apply, sub_eq_zero, Matrix.one_apply] at h0
    rw [h0]
    simp [σ.symm.injective.eq_iff]
  have hlt : ∀ i j, b j < b i → b i ≠ z := fun i j h e => by
    have := hz j
    rw [e] at h
    exact absurd (lt_of_le_of_lt this h) (lt_irrefl _)
  have hne : ∀ i j : Fin d, b j < b i → i ≠ j := fun i j h e => by rw [e] at h; exact lt_irrefl _ h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i j h
    rw [hent u hu i j (Or.inr (hlt i j h)), if_neg (hne i j h)]
  · intro i j h
    rw [← map_inv, hent u⁻¹ (inv_mem hu) i j (Or.inr (hlt i j h)), if_neg (hne i j h)]
  · intro i j h
    rw [hent u hu i j (by by_cases e : b i = z <;> simp_all)]

theorem exists_perm_first {d s : ℕ} (b : Fin d → Fin s) (z : Fin s) :
    ∃ σ : Fin d ≃ Fin d, ∀ k : Fin d, (k : ℕ) < Fintype.card {i // b i = z} ↔ b (σ k) = z := by
  classical
  set a := Fintype.card {i // b i = z} with ha
  have had : a ≤ d := (Fintype.card_subtype_le _).trans (by simp)
  have hca : Fintype.card {k : Fin d // (k : ℕ) < a} = a := by
    rw [Fintype.card_congr (show {k : Fin d // (k : ℕ) < a} ≃ Fin a from
      { toFun := fun k => ⟨k.1, k.2⟩
        invFun := fun i => ⟨⟨i, lt_of_lt_of_le i.2 had⟩, i.2⟩
        left_inv := fun k => rfl
        right_inv := fun i => rfl }), Fintype.card_fin]
  let e1 : {k : Fin d // (k : ℕ) < a} ≃ {i // b i = z} := Fintype.equivOfCardEq (by rw [hca])
  let e2 : {k : Fin d // ¬ (k : ℕ) < a} ≃ {i // ¬ b i = z} := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hca])
  refine ⟨((Equiv.sumCompl fun k : Fin d => (k : ℕ) < a).symm.trans
    ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl fun i => b i = z))), fun k => ?_⟩
  by_cases hk : (k : ℕ) < a
  · have e : ((Equiv.sumCompl fun k : Fin d => (k : ℕ) < a).symm.trans
        ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl fun i => b i = z))) k = (e1 ⟨k, hk⟩ : Fin d) := by
      simp only [Equiv.trans_apply]
      rw [Equiv.sumCompl_symm_apply_of_pos (p := fun k : Fin d => (k : ℕ) < a) hk]
      rfl
    rw [e]
    exact ⟨fun _ => (e1 ⟨k, hk⟩).2, fun _ => hk⟩
  · have e : ((Equiv.sumCompl fun k : Fin d => (k : ℕ) < a).symm.trans
        ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl fun i => b i = z))) k = (e2 ⟨k, hk⟩ : Fin d) := by
      simp only [Equiv.trans_apply]
      rw [Equiv.sumCompl_symm_apply_of_neg (p := fun k : Fin d => (k : ℕ) < a) hk]
      rfl
    rw [e]
    exact ⟨fun h => absurd h hk, fun h => absurd h (e2 ⟨k, hk⟩).2⟩

end GlobalTheory.CuspCharRep

namespace GlobalTheory.CuspCharRep

open Formalism.IrreducibleCountingLemmas.TYPES GlobalTheory.GLq GlobalTheory.FiniteGL

theorem isCusp_character_iff_isCuspidal : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))),
    1 ≤ d → CategoryTheory.Simple V →
      (GlobalTheory.GLq.IsCusp (fun x => V.character x) ↔ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V) := by
  intro g _ d V hd hV
  unfold GlobalTheory.GLq.IsCusp
  constructor
  · rintro ⟨-, -, hres⟩ s b hb hs v hv
    let z : Fin s := ⟨0, by omega⟩
    have hz : ∀ i, z ≤ b i := fun i => show (0 : ℕ) ≤ (b i : ℕ) from Nat.zero_le _
    obtain ⟨σ, hσ⟩ := exists_perm_first b z
    have ha0 : 0 < Fintype.card {i // b i = z} :=
      Fintype.card_pos_iff.2 ⟨⟨(hb z).choose, (hb z).choose_spec⟩⟩
    have had : Fintype.card {i // b i = z} < d := by
      obtain ⟨j, hj⟩ := hb ⟨1, by omega⟩
      have h := Fintype.card_subtype_lt (p := fun i => b i = z) (x := j)
        (by rw [hj]; simp [Fin.ext_iff, z])
      simpa using h
    have hw := (res_character_eq_zero_iff had.le V).1 (hres _ ha0 had)
    let P := GlobalTheory.SerOSys.TranspLabel.permGL (K := ZMod g) σ
    have key : V.ρ P⁻¹ v = 0 := hw _ fun u hu => by
      have h1 := hv _ (glEquiv_mem_unip b z hz σ hσ hu)
      have hperm : glEquiv (ZMod g) σ u = P * u * P⁻¹ := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul]
        show Matrix.reindex σ σ (u : Matrix (Fin d) (Fin d) (ZMod g)) =
          σ.symm.toPEquiv.toMatrix * (u : Matrix (Fin d) (Fin d) (ZMod g)) *
            σ.toPEquiv.toMatrix
        rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
        rfl
      rw [hperm] at h1
      calc V.ρ u (V.ρ P⁻¹ v) = V.ρ (P⁻¹ * (P * u * P⁻¹)) v := by
            rw [show P⁻¹ * (P * u * P⁻¹) = u * P⁻¹ by group, map_mul, Module.End.mul_apply]
        _ = V.ρ P⁻¹ v := by rw [map_mul, Module.End.mul_apply, h1]
    calc v = V.ρ (P * P⁻¹) v := by rw [mul_inv_cancel, map_one, Module.End.one_apply]
      _ = 0 := by rw [map_mul, Module.End.mul_apply, key, map_zero]
  · intro hc
    refine ⟨by omega, ⟨V, hV, fun _ => rfl⟩, fun a ha had => ?_⟩
    rw [res_character_eq_zero_iff had.le V]
    intro v hv
    refine hc 2 (cb d a) ?_ le_rfl v fun u hu => hv u (mem_unipRadical_of_mem_unip hu)
    intro k
    fin_cases k
    · exact ⟨⟨0, by omega⟩, by simp [cb, ha]⟩
    · exact ⟨⟨a, had⟩, by simp [cb]⟩

end GlobalTheory.CuspCharRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterIffIsCuspidalGLnFiniteFieldStatement
open CategoryTheory Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple V → (GlobalTheory.GLq.IsCusp (fun x => V.character x) ↔ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V) := by
  first | exact @GlobalTheory.CuspCharRep.isCusp_character_iff_isCuspidal | exact GlobalTheory.CuspCharRep.isCusp_character_iff_isCuspidal | (intros; apply GlobalTheory.CuspCharRep.isCusp_character_iff_isCuspidal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLiftReadingOfDecoratedLatticePresentatio
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLiftReadingOfDecoratedLatticePresentatio
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.LiftBrg

theorem castGL_of_matEq {A : Type} [CommRing A] {a b : ℕ} (h : a = b) (x : GL (Fin a) A) (y : GL (Fin b) A)
    (hm : MatEq x y) : y = castGL h x := by
  subst h
  ext i j
  simp only [castGL, Units.coe_mapEquiv, MulEquiv.coe_toMonoidHom]
  simp [Matrix.reindexAlgEquiv_apply]
  exact (hm.2 i j i j rfl rfl).symm

theorem matEq_castGL {A : Type} [CommRing A] {a b : ℕ} (h : a = b) (x : GL (Fin a) A) : MatEq x (castGL h x) := by
  subst h
  refine ⟨rfl, fun i j i' j' hi hj => ?_⟩
  obtain rfl := Fin.ext hi
  obtain rfl := Fin.ext hj
  simp [castGL]

theorem castGL_mem_UA_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {a b : ℕ} (h : a = b) (x : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ Formalism.L2.DIV.UA hc 1) :
    castGL h x ∈ Formalism.L2.DIV.UA hc 1 := by
  subst h
  have e : castGL (rfl : a = a) x = x := by
    ext i j
    simp [castGL]
  rwa [e]


set_option maxHeartbeats 1000000 in
theorem brgStdV_of_readsStd_one : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m), L.βV i = 1 → (Vc X.toD7 i).gram = 1 →
    ∀ c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W, (∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v)) →
    ∀ P : ∀ t, LiftBrg.PresL X I hX U Xg tr L cV i t, (∀ t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t 1 1 (P t)) →
      (∀ t v, (P t).coef v = c v) → BrgStdV X I hX U Xg tr L i (cV i) (fun t φ => (P t).extL φ) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i hβ hgram c hc P hR hcoef
  unfold BrgStdV StdSide
  refine ⟨c, ?_, ?_, ?_, X.toD7.sp.cm, ?_⟩
  · intro γ γE g hr hm v
    have hg : g = castGL (rkEq X i).symm γE := castGL_of_matEq _ γE g hm
    subst hg
    exact hc γ γE hr v
  · intro hcm t φ h x hm
    refine ((hR t _ h).trans (hcoef t _)).trans ?_
    congr 1
    rw [Formalism.L2.Col.decoPt_mk]
    unfold ptL
    congr 1
    rw [hβ] at hm
    have hx := castGL_of_matEq (rkEq X i).symm _ _ hm
    rw [hx]
    simp only [matIn, mul_one, inv_one, one_mul, Equiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    rfl
  · have hli := (P (Formalism.L2.DIV.mu0F _)).coef_li
    simp only [hcoef] at hli
    exact hli
  · intro h
    obtain ⟨g, hg⟩ := h.2
    have h1 : Formalism.UG.bc (swapAE X.toD7) h.1 ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram := by
      rw [← hg]; exact GlobalTheory.LevSplit.finE_mem_UA _ g
    rw [hgram] at h1
    refine ⟨⟨castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) h.1), castGL_mem_UA_std _ _ _ h1⟩, ?_⟩
    rw [hβ]
    have hm := matEq_castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) h.1)
    simp only [matIn, mul_one]
    exact hm

end GlobalTheory.Mem.R3.LiftBrg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLiftReadingOfDecoratedLatticePresentatioStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardLiftReading_of_decoratedLatticePresentations : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m), L.βV i = 1 → (Vc X.toD7 i).gram = 1 →
    ∀ c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W, (∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v)) →
    ∀ P : ∀ t, LiftBrg.PresL X I hX U Xg tr L cV i t, (∀ t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t 1 1 (P t)) →
      (∀ t v, (P t).coef v = c v) → BrgStdV X I hX U Xg tr L i (cV i) (fun t φ => (P t).extL φ) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.brgStdV_of_readsStd_one | exact GlobalTheory.Mem.R3.LiftBrg.brgStdV_of_readsStd_one | (intros; apply GlobalTheory.Mem.R3.LiftBrg.brgStdV_of_readsStd_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapRealSubfieldEqIffEqOrIsConjPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapRealSubfieldEqIffEqOrIsConjPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
noncomputable section

namespace GlobalTheory.PlacePair

theorem hostConj_eq (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

theorem cO_cO (D : D7) (x : 𝓞 D.host.E) :
    IsCMField.ringOfIntegersComplexConj D.host.E (IsCMField.ringOfIntegersComplexConj D.host.E x) = x := by
  apply RingOfIntegers.ext
  rw [IsCMField.coe_ringOfIntegersComplexConj, IsCMField.coe_ringOfIntegersComplexConj]
  exact IsCMField.complexConj_apply_apply D.host.E (x : D.host.E)

theorem cO_algebraMap (D : D7) (a : 𝓞 (maximalRealSubfield D.host.E)) :
    IsCMField.ringOfIntegersComplexConj D.host.E
        (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a) =
      algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a :=
  (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).2 ⟨a, rfl⟩

theorem isConjPl_iff (D : D7) (P P' : PlE D.host) :
    IsConjPl D.host P P' ↔
      ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ IsCMField.ringOfIntegersComplexConj D.host.E x ∈ P'.asIdeal := by
  constructor
  · intro h x
    exact h x _ (by rw [IsCMField.coe_ringOfIntegersComplexConj, hostConj_eq])
  · intro h x y hxy
    have : y = IsCMField.ringOfIntegersComplexConj D.host.E x := by
      apply RingOfIntegers.ext
      rw [hxy, hostConj_eq, IsCMField.coe_ringOfIntegersComplexConj]
    rw [this]; exact h x

theorem eq_or_eq_conj (D : D7) (P w : PlE D.host)
    (hw : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))) :
    w.asIdeal = P.asIdeal ∨
      w.asIdeal = P.asIdeal.comap (IsCMField.ringOfIntegersComplexConj D.host.E : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
  set Q : Ideal (𝓞 D.host.E) :=
    P.asIdeal.comap (IsCMField.ringOfIntegersComplexConj D.host.E : 𝓞 D.host.E →+* 𝓞 D.host.E) with hQ
  have hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  by_contra hne
  push_neg at hne
  obtain ⟨h1, h2⟩ := hne
  have nle : ∀ I : Ideal (𝓞 D.host.E), I.IsPrime → w.asIdeal ≠ I → ¬ w.asIdeal ≤ I := fun I hI h hle =>
    h (w.isMaximal.eq_of_le hI.ne_top hle)
  obtain ⟨a, ha, haP⟩ := Set.not_subset.mp (nle P.asIdeal P.isPrime h1)
  obtain ⟨b, hb, hbQ⟩ := Set.not_subset.mp (nle Q hQp h2)
  have key : ∃ x ∈ w.asIdeal, x ∉ P.asIdeal ∧ x ∉ Q := by
    by_cases haQ : a ∈ Q
    · by_cases hbP : b ∈ P.asIdeal
      · refine ⟨a + b, w.asIdeal.add_mem ha hb, fun h => haP ?_, fun h => hbQ ?_⟩
        · simpa using P.asIdeal.sub_mem h hbP
        · simpa using Q.sub_mem h haQ
      · exact ⟨b, hb, hbP, hbQ⟩
    · exact ⟨a, ha, haP, haQ⟩
  obtain ⟨x, hx, hxP, hxQ⟩ := key
  have hxQ' : IsCMField.ringOfIntegersComplexConj D.host.E x ∉ P.asIdeal := hxQ
  have hfix : IsCMField.ringOfIntegersComplexConj D.host.E (x * IsCMField.ringOfIntegersComplexConj D.host.E x) =
      x * IsCMField.ringOfIntegersComplexConj D.host.E x := by
    rw [map_mul, cO_cO, mul_comm]
  obtain ⟨y, hy⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).1 hfix
  have hyw : y ∈ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, hy]; exact w.asIdeal.mul_mem_right _ hx
  rw [hw, Ideal.mem_comap, hy] at hyw
  rcases P.isPrime.mem_or_mem hyw with h | h
  · exact hxP h
  · exact hxQ' h

theorem comap_eq_iff : ∀ (D : D7) (P P' : PlE D.host),
    P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ↔
        (P = P' ∨ IsConjPl D.host P P') := by
  intro D P P'
  constructor
  · intro h
    rcases eq_or_eq_conj D P P' h.symm with e | e
    · exact Or.inl (HeightOneSpectrum.ext e.symm)
    · refine Or.inr ((isConjPl_iff D P P').2 fun x => ?_)
      rw [e, Ideal.mem_comap, RingHom.coe_coe, cO_cO]
  · rintro (rfl | h)
    · rfl
    · rw [isConjPl_iff] at h
      ext a
      rw [Ideal.mem_comap, Ideal.mem_comap, h, cO_algebraMap]

end GlobalTheory.PlacePair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapRealSubfieldEqIffEqOrIsConjPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comap_realSubfield_eq_iff_eq_or_isConjPlace : ∀ (D : D7) (P P' : PlE D.host),
    P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ↔ (P = P' ∨ IsConjPl D.host P P') := by
  first | exact @GlobalTheory.PlacePair.comap_eq_iff | exact GlobalTheory.PlacePair.comap_eq_iff | (intros; apply GlobalTheory.PlacePair.comap_eq_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFramedLevelIffTwoAdelicPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFramedLevelIffTwoAdelicPoints
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TopCh

section FrLev

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
  {hc : CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem frDiv_mem_GLint (p p' : DecoF E n ST SG Q) (hN : p.deco.1.N = p'.deco.1.N) (P : Q) :
    (p.fr P)⁻¹ * p'.fr P ∈ GLint E n P.1 := by
  intro v
  have h1 := p.2 P (((p.fr P)⁻¹ * p'.fr P) v)
  have h2 := p'.2 P v
  have e : p.1.2 P (((p.fr P)⁻¹ * p'.fr P) v) = p'.fr P v := by
    show p.fr P ((p.fr P).symm (p'.fr P v)) = p'.fr P v
    exact LinearEquiv.apply_symm_apply _ _
  rw [e] at h1
  rw [← h1, ← h2]
  show p'.fr P v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.deco.1.N ↔ p'.fr P v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p'.deco.1.N
  rw [hN]

theorem rhoP_eq_fr {g : GL (Fin n) (AfE F E)} {q : DecoF E n ST SG Q} (hq : IsPtOf hc g q) (P : Q) :
    rhoP F P.1 g = bc (algebraMap E (P.1.adicCompletion E)) (toGLm E n (q.fr P)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show adAt F P.1 ((g : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ (((toGLm E n (q.fr P) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)
  rw [hq.fr P i j, qsp_toGLm_apply]

end FrLev

end GlobalTheory.Mem.Col2.TopCh

namespace GlobalTheory.Mem.Col2.TopCh

theorem mem_topU_iff : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (U : Subgroup (GL (Fin n) (AfE F E))) (k t y x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ x ∈ UAd hc n, x ∈ U ↔ k⁻¹ * x * k ∈ levU hc n ST SG Λ.grp) → IsPtOf hc (y * (k * t)) p → IsPtOf hc (y * x * (k * t)) p' → (x ∈ topU U t Θ d ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = p') := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q Λ Θ d hd N hdN hΘ U k t y x p p' hk hkP ht hU hp hp'
  set g := y * (k * t) with hg
  set z := (k * t)⁻¹ * x * (k * t) with hz
  have hgz : y * x * (k * t) = g * z := by rw [hg, hz]; group
  rw [hgz] at hp'
  have step := fun h : GLG (E := E) (n := n) (SG := SG) => ((GlobalTheory.T.isPtOf_mul_J0_decoration F E hc n ST SG Q g z p p' h).1 hp hp')
  have htU : t ∈ UAd hc n := principal_le_adelic_unitary hc n ST SG ht
  have hktU : k * t ∈ UAd hc n := mul_mem hk htU
  have hgU : g ∈ UAd hc n := hp.uni
  have hgzU : g * z ∈ UAd hc n := hp'.uni
  have hyU : y ∈ UAd hc n := by
    have e : y = g * (k * t)⁻¹ := by rw [hg]; group
    rw [e]; exact mul_mem hgU (inv_mem hktU)
  have hxU : x ∈ UAd hc n := by
    have e : x = y⁻¹ * (g * z) * (k * t)⁻¹ := by rw [hg, hz]; group
    rw [e]; exact mul_mem (mul_mem (inv_mem hyU) hgzU) (inv_mem hktU)
  have hU' : x ∈ U ↔ z ∈ levU hc n ST SG Λ.grp := by
    rw [hU x hxU]
    have e : k⁻¹ * x * k = t * z * t⁻¹ := by rw [hz]; group
    rw [e]
    have htL : t ∈ levU hc n ST SG Λ.grp := kOne_le_unipotentLevel hc n ST SG _ ht
    constructor
    · intro h
      have h2 := mul_mem (mul_mem (inv_mem htL) h) htL
      have e2 : t⁻¹ * (t * z * t⁻¹) * t = z := by group
      rwa [e2] at h2
    · intro h
      exact mul_mem (mul_mem htL h) (inv_mem htL)
  have hT : ∀ P : Q, rhoT F P.1 t x = rhoP F P.1 z := by
    intro P
    show rhoP F P.1 (t⁻¹ * x * t⁻¹⁻¹) = rhoP F P.1 z
    rw [hz]
    simp only [map_mul, map_inv, hkP P, one_mul, inv_inv, _root_.mul_inv_rev, inv_one, mul_one]
  have hZ : ∀ (hN : p.deco.1.N = p'.deco.1.N) (P : Q),
      rhoP F P.1 z = iotaP P.1 ⟨_, frDiv_mem_GLint p p' hN P⟩ := by
    intro hN P
    have e : rhoP F P.1 z = (rhoP F P.1 g)⁻¹ * rhoP F P.1 (g * z) := by
      rw [← map_inv, ← map_mul, inv_mul_cancel_left]
    rw [e, rhoP_eq_fr hp P, rhoP_eq_fr hp' P, ← map_inv, ← map_mul, ← map_inv, ← map_mul]
    rfl
  have hL : ∀ (hN : p.deco.1.N = p'.deco.1.N) (P : Q),
      rhoT F P.1 t x ∈ locLev P.1 (Θ P) (d P) ↔ (⟨_, frDiv_mem_GLint p p' hN P⟩ : ↥(GLint E n P.1)) ∈ (Θ P).H := by
    intro hN P
    rw [hT P, hZ hN P]
    exact qbU_rat (F := E) P.1 (algebraMap E (P.1.adicCompletion E)) (phi_int P.1) (phi_lt P.1) (Θ P) (d P) (hd P) (hdN P)
      (hΘ P) _
  have hNs : ∀ h : GLG (E := E) (n := n) (SG := SG), p'.deco = ((1, h) : UF E n × GLG (E := E) (n := n) (SG := SG)) • p.deco → p.deco.1.N = p'.deco.1.N := by
    intro h e
    rw [e]
    show p.deco.1.N = Formalism.HermitianLatticesTheory.gmap (1 : Sp E n ≃ₗ[E] Sp E n) p.deco.1.N
    exact (Formalism.L2.Col.gmap_one _).symm
  constructor
  · intro hx
    obtain ⟨hz0, hzr⟩ := (mem_levU hc n ST SG _).1 (hU'.1 hx.1)
    let h : Λ.grp := ⟨(redG hc n ST SG ⟨z, hz0⟩)⁻¹, inv_mem hzr⟩
    have hdeco : p'.deco = ((1, h.1) : UF E n × GLG (E := E) (n := n) (SG := SG)) • p.deco := (step h.1).1 ⟨hz0, (inv_inv _).symm⟩
    have hN := hNs h.1 hdeco
    have hc' : ∀ P : Q, (⟨_, frDiv_mem_GLint p p' hN P⟩ : ↥(GLint E n P.1)) ∈ (Θ P).H := fun P =>
      (hL hN P).1 (rhoT_mem hx P)
    let θ : Θ.grp := ⟨fun P => (⟨_, frDiv_mem_GLint p p' hN P⟩ : ↥(GLint E n P.1))⁻¹, fun P _ => inv_mem (hc' P)⟩
    refine ⟨h, θ, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hdeco.symm
    · funext P
      show (1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * (((θ.1 P)⁻¹ : ↥(GLint E n P.1)) : Sp E n ≃ₗ[E] Sp E n) = p'.fr P
      show (1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * ((p.fr P)⁻¹ * p'.fr P) = p'.fr P
      rw [one_mul, mul_inv_cancel_left]
  · rintro ⟨h, θ, hθ⟩
    have hdeco : p'.deco = ((1, h.1) : UF E n × GLG (E := E) (n := n) (SG := SG)) • p.deco := by rw [← hθ]; rfl
    obtain ⟨hz0, hzr⟩ := (step h.1).2 hdeco
    have hN := hNs h.1 hdeco
    refine ⟨hU'.2 ((mem_levU hc n ST SG _).2 ⟨hz0, by rw [hzr]; exact inv_mem h.2⟩), ?_⟩
    refine Subgroup.mem_iInf.2 fun P => Subgroup.mem_comap.2 ((hL hN P).2 ?_)
    have hfr : p'.fr P = p.fr P * (((θ.1 P)⁻¹ : ↥(GLint E n P.1)) : Sp E n ≃ₗ[E] Sp E n) := by
      rw [← hθ]
      show (1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * _ = _
      rw [one_mul]
    have e : (⟨_, frDiv_mem_GLint p p' hN P⟩ : ↥(GLint E n P.1)) = (θ.1 P)⁻¹ := by
      apply Subtype.ext
      show (p.fr P)⁻¹ * p'.fr P = _
      rw [hfr, inv_mul_cancel_left]
    rw [e]
    exact inv_mem (θ.2 P (Set.mem_univ _))

end GlobalTheory.Mem.Col2.TopCh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFramedLevelIffTwoAdelicPointsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_framedLevel_iff_two_adelic_points : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (U : Subgroup (GL (Fin n) (AfE F E))) (k t y x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ x ∈ UAd hc n, x ∈ U ↔ k⁻¹ * x * k ∈ levU hc n ST SG Λ.grp) → IsPtOf hc (y * (k * t)) p → IsPtOf hc (y * x * (k * t)) p' → (x ∈ topU U t Θ d ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = p') := by
  exact @GlobalTheory.Mem.Col2.TopCh.mem_topU_iff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NTiedLocTiedOfBuilt
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HeightCounting

theorem locTied_any (D' : D7) : Nonempty (Formalism.L2.LocTied D') :=
  ⟨⟨fun l _ => GlobalTheory.LocArith.arithTied l (D'.loc l), fun i w hw => D'.nbr_ind i w hw,
    fun i w hw => D'.ntwbr_ind i w hw⟩⟩

end GlobalTheory.HeightCounting

end
end

module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelBaseValueEquivariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumCentralCharacter
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselThetaContractionExtendByZeroVacuumSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaUnfoldingEquivariantUnitaryGroups
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepEqTwoThetaColumnLifts
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelsCommuteTwisted
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearModelLatticeVacuumBase
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepExponents
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralFiniteAdeleOfSplitPlaceComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralFiniteAdeleOfSplitPlaceComponents
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

theorem GlobalTheory.IntPlaces.mem_of_idem_sum {R : Type} [CommRing R] {n : ℕ} (S : Set R) (hS0 : (0 : R) ∈ S)
    (E : Fin n → R) (hEE : ∀ i, E i * E i = E i) (hE : ∀ i j, i ≠ j → E i * E j = 0) (G : Fin n → R → Prop)
    (hint : ∀ i z, z ∈ S ↔ (1 - E i) * z ∈ S ∧ G i z) (hG : ∀ i j z, i ≠ j → G i z → G i ((1 - E j) * z)) :
    ∀ z, (∑ i, E i) * z = z → (∀ i, G i z) → z ∈ S := by
  have key : ∀ s : Finset (Fin n), ∀ z, (∑ i ∈ s, E i) * z = z → (∀ i ∈ s, G i z) → z ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro z hz _
      rw [Finset.sum_empty, zero_mul] at hz
      rw [← hz]
      exact hS0
    | insert a s ha ih =>
      intro z hz hzi
      rw [Finset.sum_insert ha] at hz
      refine (hint a z).2 ⟨?_, hzi a (Finset.mem_insert_self a s)⟩
      have hET : E a * ∑ i ∈ s, E i = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun i hi => hE a i fun h => ha (h ▸ hi)
      have hw : (1 - E a) * z = (∑ i ∈ s, E i) * z := by
        calc (1 - E a) * z = (1 - E a) * ((E a + ∑ i ∈ s, E i) * z) := by rw [hz]
          _ = (∑ i ∈ s, E i) * z := by linear_combination (-z) * hEE a + (-z) * hET
      refine ih _ ?_ fun i hi => ?_
      · linear_combination (-1 : R) * hw + (-z) * hET
      · exact hG i a z (fun h => ha (h ▸ hi)) (hzi i (Finset.mem_insert_of_mem hi))
  exact fun z hz hzi => key Finset.univ z hz fun i _ => hzi i


open GlobalTheory.IdemSupport in
theorem GlobalTheory.IntPlaces.mem_intAf_of_split : ∀ (D : D7) (n : ℕ) (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (P : Fin n → Formalism.L2.DIV.Pl D.host.E), (∀ i, Formalism.L2.NTheta.IsIdemAt (q i).e (P i)) → Function.Injective P → ∀ (π' : ∀ i, Formalism.IndefR.Datum.EAf D →+* k i), (∀ i a, π' i (Formalism.IndefR.Datum.toEAf D a) = (q i).pr a) → (∀ i (z : Formalism.IndefR.Datum.EAf D), z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ (1 - Formalism.IndefR.Datum.toEAf D (q i).e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ π' i z ∈ 𝒪[k i]) → ∀ z : Formalism.IndefR.Datum.EAf D, Formalism.IndefR.Datum.toEAf D (∑ i, (q i).e) * z = z → (∀ i, π' i z ∈ 𝒪[k i]) → z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D n k _ _ _ _ q P hI hP π' hπ hint z0 hz0 hzi0
  have hΦ := GlobalTheory.StdFrames.comp_toAd D
  have hd : ∀ i, IsDelta ((GlobalTheory.StdFrames.toAd D).comp (Formalism.IndefR.Datum.toEAf D)) (P i) (q i).e :=
    fun i => delta_of_isIdemAt hΦ (hI i)
  have horth : ∀ i j, i ≠ j → (q i).e * (q j).e = 0 := by
    intro i j hij
    refine hΦ.ext' (by rw [RingHom.map_mul, (hd i).1, zero_mul, RingHom.map_zero]) fun Q => ?_
    rw [ev_mul, ev_zero]
    by_cases hQ : Q = P i
    · rw [(hd j).2.2 Q (fun h => hij (hP (hQ.symm.trans h))), mul_zero]
    · rw [(hd i).2.2 Q hQ, zero_mul]
  have hidem : ∀ i, (q i).e * (q i).e = (q i).e := by
    intro i
    refine hΦ.ext' (by rw [RingHom.map_mul, (hd i).1, zero_mul]) fun Q => ?_
    rw [ev_mul]
    by_cases hQ : Q = P i
    · rw [hQ, (hd i).2.1, mul_one]
    · rw [(hd i).2.2 Q hQ, zero_mul]
  have hpr : ∀ i j, i ≠ j → π' i (Formalism.IndefR.Datum.toEAf D (q j).e) = 0 := by
    intro i j hij
    rw [hπ, ← (q i).pr_sec ((q i).pr (q j).e), (q i).sec_pr, horth i j hij, map_zero]
  refine GlobalTheory.IntPlaces.mem_of_idem_sum (Formalism.L2.Herm.intAf D.host.F D.host.E : Set _) (zero_mem _)
    (fun i => Formalism.IndefR.Datum.toEAf D (q i).e) (fun i => by rw [← RingHom.map_mul, hidem])
    (fun i j hij => by rw [← RingHom.map_mul, horth i j hij, RingHom.map_zero]) (fun i z => π' i z ∈ 𝒪[k i])
    hint (fun i j z hij hz => ?_) z0 (by rw [show (∑ i, Formalism.IndefR.Datum.toEAf D (q i).e) = Formalism.IndefR.Datum.toEAf D (∑ i, (q i).e) from
      (map_sum (Formalism.IndefR.Datum.toEAf D).toAddMonoidHom (fun i => (q i).e) Finset.univ).symm]; exact hz0) hzi0
  rw [RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hpr i j hij, sub_zero, one_mul]
  exact hz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralFiniteAdeleOfSplitPlaceComponentsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_finiteAdele_of_split_place_components : ∀ (D : D7) (n : ℕ) (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (P : Fin n → Formalism.L2.DIV.Pl D.host.E), (∀ i, Formalism.L2.NTheta.IsIdemAt (q i).e (P i)) → Function.Injective P → ∀ (π' : ∀ i, Formalism.IndefR.Datum.EAf D →+* k i), (∀ i a, π' i (Formalism.IndefR.Datum.toEAf D a) = (q i).pr a) → (∀ i (z : Formalism.IndefR.Datum.EAf D), z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ (1 - Formalism.IndefR.Datum.toEAf D (q i).e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ π' i z ∈ 𝒪[k i]) → ∀ z : Formalism.IndefR.Datum.EAf D, Formalism.IndefR.Datum.toEAf D (∑ i, (q i).e) * z = z → (∀ i, π' i z ∈ 𝒪[k i]) → z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.IntPlaces.mem_intAf_of_split | exact GlobalTheory.IntPlaces.mem_intAf_of_split | (intros; apply GlobalTheory.IntPlaces.mem_intAf_of_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLocalFactorEqIteratedChainDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLocalFactorEqIteratedChainDatum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

namespace GlobalTheory.MovedDat

open GlobalTheory.LocMod.StepVec

theorem rank_first_loc {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) : D.R.k + (G.s + 1) = D.R.r := by
  have := G.hs
  unfold Ranks.r
  omega

theorem rdAt_iff {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) {w : Formalism.L2.DIV.Pl D.host.E} {π' : Formalism.IndefR.Datum.EAf D →+* G.k}
    (hπ : ∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = G.q.pr a)
    (hred : GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F w) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) (x : G.S.P.J)
    (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP w))
    (M : Matrix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.k ⊕ Fin (G.s + 1)) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hM : g.val.submatrix (firstOrd (rank_first_loc G)) (firstOrd (rank_first_loc G)) = M.map (Formalism.L2.DIV.resS D.host.F w)) :
    RdAt G w x g ↔ MaxM ((x : GL _ G.k).val - M.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) := by
  have key : ∀ a b (z : 𝓞 D.host.E),
      Ideal.Quotient.mk w.asIdeal z = g.val (firstOrd (rank_first_loc G) a) (firstOrd (rank_first_loc G) b) →
      valuation G.k ((π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (M a b) - (ofSplit G.q).pr (z : D.host.E)) < 1 :=
    fun a b z hz => by
      have h1 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) =
          (ofSplit G.q).pr (z : D.host.E) := hπ (incA D (z : D.host.E))
      rw [← h1, ← RingHom.map_sub, ← hred.ker, RingHom.map_sub, Formalism.L2.DIV.resS_oToS, sub_eq_zero]
      exact (hz.trans (congrFun (congrFun hM a) b)).symm
  constructor
  · intro h a b
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (g.val (firstOrd (rank_first_loc G) a) (firstOrd (rank_first_loc G) b))
    have := Valuation.map_sub_lt _ (h a b _ _ (firstOrd_val _ a) (firstOrd_val _ b) z hz) (key a b z hz)
    rwa [sub_sub_sub_cancel_right] at this
  · intro h a b a' b' ha hb z hz
    obtain rfl : a' = firstOrd (rank_first_loc G) a := Fin.ext (ha.trans (firstOrd_val _ a).symm)
    obtain rfl : b' = firstOrd (rank_first_loc G) b := Fin.ext (hb.trans (firstOrd_val _ b).symm)
    have := Valuation.map_add_lt _ (h a b) (key a b z hz)
    rwa [Matrix.sub_apply, Matrix.map_apply, sub_add_sub_cancel] at this

theorem card_of_ix {κ l r t j a : ℕ} (h : κ + l = r) (e : Ix (Fin κ ⊕ Fin l) (Fin t) j ≃ Fin a) : a = r + j * t := by
  have e' : (Fin κ ⊕ Fin l) ⊕ (Fin j × Fin t) ≃ Fin a := e
  have := Fintype.card_congr e'
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at this
  rw [← this, h]

theorem locF_eq_iterPhi : ∀ (D : D7) (c : Comm D) (v : VCom c) (G0 : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (π' : Formalism.IndefR.Datum.EAf D →+* G0.k), (∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = G0.q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (j : ℕ), (∀ c, c ≤ j → GlobalTheory.FunObj.Comparison₂.Compat (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (χ (c + 1) PP) (G0.S.μ (c + 1))) → ∀ (a b : ℕ) (hr : D.R.r ≤ a) (ea : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) j ≃ Fin a) (eb : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) (j + 1) ≃ Fin b), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos ea → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eb → ∀ N : Matrix (Fin b) (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E), GlobalTheory.LocMod.StepVec.locF D.R.t j hr (GlobalTheory.MovedDat.RdAt G0 PP) (fun x => G0.S.P.lam x) (fun c => χ c PP) (N.map (Formalism.L2.DIV.resS D.host.F PP)) = G0.S.P.iterPhi (Fin D.R.t) G0.S.μ G0.S.tame j ((N.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)).submatrix eb ea) := by
  intro D c v G0 PP π' hπ hred χ j hχ a b hr ea eb ha hb N
  exact locF_eq (GlobalTheory.FunObj.TieLev.iterPhi_read _ _ _ _ _ hred _ _ _ _ _ _ (firstOrd (rank_first_loc G0)) ea eb
    (isIx_of_isOrd _ (card_of_ix (rank_first_loc G0) ea) ha) (isIx_of_isOrd _ (card_of_ix (rank_first_loc G0) eb) hb) hr _ _ _
    (fun i => χ i PP) hχ _ (rdAt_iff G0 hπ hred) N)

end GlobalTheory.MovedDat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLocalFactorEqIteratedChainDatumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_local_factor_eq_iterated_chain_datum : ∀ (D : D7) (c : Comm D) (v : VCom c) (G0 : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (π' : Formalism.IndefR.Datum.EAf D →+* G0.k), (∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = G0.q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (j : ℕ), (∀ c, c ≤ j → GlobalTheory.FunObj.Comparison₂.Compat (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (χ (c + 1) PP) (G0.S.μ (c + 1))) → ∀ (a b : ℕ) (hr : D.R.r ≤ a) (ea : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) j ≃ Fin a) (eb : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) (j + 1) ≃ Fin b), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos ea → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eb → ∀ N : Matrix (Fin b) (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E), GlobalTheory.LocMod.StepVec.locF D.R.t j hr (GlobalTheory.MovedDat.RdAt G0 PP) (fun x => G0.S.P.lam x) (fun c => χ c PP) (N.map (Formalism.L2.DIV.resS D.host.F PP)) = G0.S.P.iterPhi (Fin D.R.t) G0.S.μ G0.S.tame j ((N.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)).submatrix eb ea) := by
  exact @GlobalTheory.MovedDat.locF_eq_iterPhi
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.MovedDat

open GlobalTheory.LocMod.StepVec

theorem mt_mul {D : D7} (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one {D : D7} (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem mt_inv_mul {D : D7} (V : HSp D) (a : GA D V) : mt V a⁻¹ * mt V a = 1 := by
  rw [← mt_mul, inv_mul_cancel, mt_one]

theorem isHalf_mul {D : D7} {S T : HSp D} (e : AE D) (A : Matrix (Fin T.rank) (Fin T.rank) (AE D))
    (B : Matrix (Fin S.rank) (Fin S.rank) (AE D)) (y : WO S T) (hy : IsHalf e y) :
    IsHalf e (HMul.hMul (HMul.hMul A (y : Matrix (Fin T.rank) (Fin S.rank) (AE D))) B : WO S T) := by
  intro i j
  have hy' : e • (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) :=
    Matrix.ext fun i j => hy i j
  have := congrFun (congrFun (congrArg (fun M : Matrix (Fin T.rank) (Fin S.rank) (AE D) => HMul.hMul (HMul.hMul A M) B) hy') i) j
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul] at this
  exact this

theorem isHalf_actO_iff {D : D7} (S T : HSp D) (g : GA D S) (h : GA D T) (e : AE D) (x : WO S T) :
    IsHalf e (actO S T g h x) ↔ IsHalf e x := by
  constructor
  · intro hx
    have e1 : x = actO S T g⁻¹ h⁻¹ (actO S T g h x) := by
      unfold actO
      rw [inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul, Matrix.mul_assoc,
        mt_inv_mul, Matrix.mul_one]
    rw [e1]
    exact isHalf_mul e _ _ _ hx
  · intro hx
    exact isHalf_mul e _ _ _ hx

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

theorem down_moved_actO (p : Place D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (g : GA D S) (h : GA D T) (x : WO S T) :
    p.down (moved p FS g⁻¹) (moved p FT h⁻¹) (actO S T g⁻¹ h⁻¹ x) = p.down FS FT x := by
  have hm : ∀ (V : HSp D) (a : GA D V), (mt V a⁻¹⁻¹).map p.π * (mt V a⁻¹).map p.π = 1 := fun V a => by
    rw [← Matrix.map_mul, mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  unfold Place.down moved actO
  simp only [Matrix.map_mul]
  have e1 : FT.γ * (mt T h⁻¹⁻¹).map p.π * ((mt T h⁻¹).map p.π * (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π *
      (mt S g⁻¹⁻¹).map p.π) * ((mt S g⁻¹).map p.π * FS.β) =
      FT.γ * ((mt T h⁻¹⁻¹).map p.π * (mt T h⁻¹).map p.π) * (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π *
        ((mt S g⁻¹⁻¹).map p.π * (mt S g⁻¹).map p.π) * FS.β := by
    simp only [Matrix.mul_assoc]
  rw [e1, hm, hm, Matrix.mul_one, Matrix.mul_one]

end GlobalTheory.MovedDat

namespace GlobalTheory.MovedDat

open GlobalTheory.LocMod.StepVec

end GlobalTheory.MovedDat

namespace GlobalTheory.MovedDat

end GlobalTheory.MovedDat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsIteratedQuotientIntegralFinsetSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Vac Moves InK Lat Pl latV idAt idOff intAt grpAt grpOff MxAt hand0 SplitPt extS extT)

noncomputable section
namespace GlobalTheory.QLawPf

section Iter
variable {G₁ G₂ : Type} [Group G₁] [MeasurableSpace G₁] [TopologicalSpace G₁] [Group G₂] [MeasurableSpace G₂]
    [TopologicalSpace G₂] {R₁ : Subgroup G₁} {R₂ : Subgroup G₂} {ρ₁ : Measure R₁} {μ₁ : Measure G₁} {ρ₂ : Measure R₂}
    {μ₂ : Measure G₂}

theorem isIteratedQuotientIntegral_finset_sum {ι : Type} (s : Finset ι) (F : ι → G₁ → G₂ → ℂ) (z : ι → ℂ)
    (hF : ∀ i ∈ s, Iter2 ρ₁ μ₁ ρ₂ μ₂ (F i) (z i)) :
    Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun x y => ∑ i ∈ s, F i x y) (∑ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨0, IsQuotIntL1.zero, fun q => IsQuotIntL1.zero⟩
  | insert a s ha ih =>
    obtain ⟨g, hg, hq⟩ := hF a (Finset.mem_insert_self a s)
    obtain ⟨g', hg', hq'⟩ := ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    simp only [Finset.sum_insert ha]
    exact ⟨g + g', hg.add hg', fun q => (hq q).add (hq' q)⟩

theorem isIteratedQuotientIntegral_const_mul {F : G₁ → G₂ → ℂ} {z : ℂ} (a : ℂ) (hF : Iter2 ρ₁ μ₁ ρ₂ μ₂ F z) :
    Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun x y => a * F x y) (a * z) := by
  obtain ⟨g, hg, hq⟩ := hF
  exact ⟨a • g, hg.smul a, fun q => (hq q).smul a⟩

end Iter

variable {D : D7}

theorem moves_iff_forall {S : HSp D} {L : Lat S} (hL : IsSelfDualC S L) (P : Pl D → Prop) (g : GA D S) :
    Moves S g L L P ↔ ∀ v, P v → Moves S g L L (· = v) := by
  have hP := fun z => ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 S).2.2.2 L z hL.1
  have hmv := fun (R : Pl D → Prop) (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D R) =>
    GlobalTheory.FinPl.PlacesAdeles.supp_mulVec S R g hy
  constructor
  · intro h v hv y hy
    have key : ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = v)) → (z ∈ latV S L P ↔ z ∈ latV S L (· = v)) := by
      intro z hz
      rw [hP, ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).2 S).2.2.2 L z hL.1]
      constructor
      · rintro ⟨_, h⟩
        exact ⟨hz, fun w hw e he => h w (hw ▸ hv) e he⟩
      · rintro ⟨_, h⟩
        refine ⟨fun i => GlobalTheory.FinPl.PlacesAdeles.idAt_single_le hv (hz i), fun w _ e he => ?_⟩
        by_cases hwv : w = v
        · exact h w hwv e he
        · obtain ⟨ε, -, -, -, hAt, hOff⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = w)).1
          have hzero : e • z = 0 := by
            funext i
            have h1 : ε * e = e := (hAt e).1 he.1
            have h2 : ε * z i = 0 := (hOff (z i)).1 (GlobalTheory.FinPl.PlacesAdeles.idAt_le_idOff hwv (hz i))
            show e * z i = 0
            rw [← h1, mul_comm ε e, mul_assoc, h2, mul_zero]
          rw [hzero]
          exact (latV S L (· = w)).zero_mem
    rw [← key y hy, ← key _ (hmv _ y hy)]
    exact h y fun i => GlobalTheory.FinPl.PlacesAdeles.idAt_single_le hv (hy i)
  · intro h y hy
    rw [hP y, hP (mt S g *ᵥ y)]
    constructor
    · rintro ⟨_, hy'⟩
      refine ⟨hmv _ y hy, fun w hw e he => ?_⟩
      have hey : ∀ i, (e • y) i ∈ idAt D (· = w) := fun i => Ideal.mul_mem_right _ _ he.1
      rw [← Matrix.mulVec_smul]
      exact (h w hw (e • y) hey).1 (hy' w hw e he)
    · rintro ⟨_, hy'⟩
      refine ⟨hy, fun w hw e he => ?_⟩
      have hey : ∀ i, (e • y) i ∈ idAt D (· = w) := fun i => Ideal.mul_mem_right _ _ he.1
      refine (h w hw (e • y) hey).2 ?_
      rw [Matrix.mulVec_smul]
      exact hy' w hw e he

theorem intAt_iff_moves {V : HSp D} {L : Lat V} {k Y : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Fintype Y] [DecidableEq Y] (v : Pl D) (gl : GL Y k →* GA D V)
    (hr : gl.range = grpAt V (· = v)) (hx : ∀ x : GA D V, ∃! g, x * (gl g)⁻¹ ∈ grpOff V (· = v))
    (hK : ∀ g, g ∈ KO k Y ↔ InK V L (· = v) (gl g)) (x : GA D V) : IntAt v gl x ↔ Moves V x L L (· = v) := by
  constructor
  · rintro ⟨κ, hκ, hy⟩
    have := GlobalTheory.FinPl.PlacesAdeles.moves_mul (GlobalTheory.FinPl.PlacesAdeles.moves_off (L := L) hy) ((hK κ).1 hκ).2
    simpa using this
  · intro h
    obtain ⟨g, hg, -⟩ := hx x
    refine ⟨g, (hK g).2 ⟨hr ▸ ⟨g, rfl⟩, ?_⟩, hg⟩
    have := GlobalTheory.FinPl.PlacesAdeles.moves_mul (GlobalTheory.FinPl.PlacesAdeles.moves_off (L := L) (inv_mem hg)) h
    simpa using this

variable {ψ : AddChar (AF D.host.F) ℂ}

theorem vac_single (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) {P : Pl D → Prop} {v : Pl D} (hv : P v) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) :
    Vac ψ S T LS LT (· = v) f := by
  have key := (GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D ψ hψ S T (· = v) (fun p => P p ∧ p ≠ v) (fun p hp hn => hn.2 hp)).2.2.2.2 LS LT f hS hT
  have e : (fun p => p = v ∨ (P p ∧ p ≠ v)) = P := funext fun p => propext
    ⟨fun h => h.elim (fun h => h ▸ hv) (·.1), fun h => (em (p = v)).imp id fun h' => ⟨h, h'⟩⟩
  rw [e] at key
  exact (key.1 hf).1

theorem isFinComb_of_half {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) {S T : HSp D} {c : WO S T →₀ ℂ} (hc : ∀ u ∈ c.support, IsHalf (q.e + cA D q.e) u) : IsFinComb c := by
  intro u hu
  ext i j
  exact (RingHom.mem_ker).1 (Ideal.mem_inf.1 (GlobalTheory.FinPl.SplitHalfSupp.mxAt_of_isHalf_above D k q _ _ u (hc u hu) i j)).1

theorem isFinComb_aconv {S T : HSp D} (l : List (WO S T →₀ ℂ)) (hl : ∀ c ∈ l, IsFinComb c) : IsFinComb (aconv l) := by
  induction l with
  | nil =>
    intro u hu
    have : u = 0 := by simpa [aconv] using hu
    subst this
    ext i j
    simp
  | cons c l ih =>
    intro u hu
    have e1 : aconv [aconv l] = aconv l := by
      show (aconv l).sum (fun g a => (Finsupp.single (0 : WO S T) (1 : ℂ)).sum fun h b => Finsupp.single (g + h) (a * b)) = aconv l
      have : ∀ (g : WO S T) (a : ℂ), ((Finsupp.single (0 : WO S T) (1 : ℂ)).sum fun h b => Finsupp.single (g + h) (a * b)) =
          Finsupp.single g a := fun g a => by rw [Finsupp.sum_single_index (by simp), add_zero, mul_one]
      simp only [this, Finsupp.sum_single]
    have e2 : aconv (c :: l) = aconv [c, aconv l] := by
      show _ = c.sum fun g a => (aconv [aconv l]).sum fun h b => Finsupp.single (g + h) (a * b)
      rw [e1]; rfl
    rw [e2] at hu
    obtain ⟨a, ha, b, hb, rfl⟩ := GlobalTheory.QValOuter.mem_support_aconv_pair _ _ hu
    have h1 := hl c List.mem_cons_self a ha
    have h2 := ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)) b hb
    ext i j
    have h3 : infPart D (a i j) = 0 := congrFun (congrFun h1 i) j
    have h4 : infPart D (b i j) = 0 := congrFun (congrFun h2 i) j
    show infPart D (a i j + b i j) = 0
    rw [RingHom.map_add (f := _), h3, h4, add_zero]

theorem aconv_single_cons {G : Type} [AddMonoid G] (l : List (G →₀ ℂ)) : aconv (Finsupp.single 0 1 :: l) = aconv l := by
  show (Finsupp.single (0 : G) (1 : ℂ)).sum (fun g a => (aconv l).sum fun h b => Finsupp.single (g + h) (a * b)) = aconv l
  rw [Finsupp.sum_single_index (by simp)]
  simp

theorem comb_single_zero (S T : HSp D) (f : WO S T → ℂ) : comb ψ S T (Finsupp.single 0 1) f = f := by
  simp [comb, Finsupp.support_single_ne_zero, GlobalTheory.BoxSlice.heisO_zero']

theorem biComb_single_zero (A S A' : HSp D) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' (Finsupp.single 0 1) (Finsupp.single 0 1) C = C := by
  funext u v
  simp only [biComb, comb_single_zero]

theorem sum_support_smul {G M : Type} [AddCommMonoid M] [Module ℂ M] (a : ℂ) (e : G →₀ ℂ) (F : G → M) :
    ∑ g ∈ (a • e).support, (a • e) g • F g = a • ∑ g ∈ e.support, e g • F g := by
  show (a • e).sum (fun g b => b • F g) = _
  rw [Finsupp.sum_smul_index' (h := fun g b => b • F g) (fun _ => zero_smul _ _), Finset.smul_sum]
  exact Finset.sum_congr rfl fun g _ => by simp [mul_smul]

theorem comb_smul_left (S T : HSp D) (a : ℂ) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) : comb ψ S T (a • c) f = a • comb ψ S T c f :=
  sum_support_smul a c fun u => heisO ψ S T u f

theorem trc_smul_left {V : HSp D} (a : ℂ) (e : GA D V →₀ ℂ) (f : GA D V → ℂ) : trc (a • e) f = a • trc e f :=
  sum_support_smul a e fun g => rTrans g f

theorem biComb_smul_left (A S A' : HSp D) (a b : ℂ) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' (a • c) (b • c') C = (a * b) • biComb ψ A S A' c c' C := by
  funext u v
  simp only [biComb, comb_smul_left]
  have : (fun u' => (b • comb ψ S A' c' (C u')) v) = b • fun u' => comb ψ S A' c' (C u') v := rfl
  rw [this, GlobalTheory.AvgMid.comb_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, biComb]

theorem isFinComb_extS {S A L : HSp D} (o : OrthDec S A L) (T : HSp D) {c : WO A T →₀ ℂ} (hc : IsFinComb c) :
    IsFinComb (extS o T c) := by
  intro u hu
  classical
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hu)
  change (w ⬝ o.pA + (0 : WO L T) ⬝ o.pB).map (infPart D) = 0
  rw [Matrix.zero_mul, add_zero, Matrix.map_mul, hc w hw, Matrix.zero_mul]

theorem isFinComb_extT {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) {c : WO S A →₀ ℂ} (hc : IsFinComb c) :
    IsFinComb (extT o S c) := by
  intro u hu
  classical
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hu)
  change (o.jA ⬝ w + o.jB ⬝ (0 : WO S L)).map (infPart D) = 0
  rw [Matrix.mul_zero, add_zero, Matrix.map_mul, hc w hw, Matrix.mul_zero]

theorem per_sum (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (B : BesLev D ρ) {f : GA D B.V → ℂ} (hf : IsContAut B.V f) {I : Type}
    [Fintype I] (φ : I → GA D B.A → ℂ) (hφ : ∀ i, IsContAut B.A (φ i)) : B.per ψ (∑ i, φ i) f = ∑ i, B.per ψ (φ i) f := by
  simpa using perSum_all D ψ hψ ρ B f hf I Finset.univ (fun _ => 1) φ fun i _ => hφ i

section Step
variable {σ : ℕ} (S : Dbl2 ψ σ)

def HandIsLift : Prop :=
  ∀ (φ : GA D S.B.A → ℂ) (Ξ₁ : WO S.B.V₀ S.J.W₀ → ℂ) (Ξ₂ : WO S.J.W₀ S.B'.V₀ → ℂ), IsContAut S.B.A φ →
    IsThetaFunO ψ _ _ Ξ₁ → IsThetaFunO ψ _ _ Ξ₂ →
      hand0 S.s₁ S.s₂ S.l S.vL φ Ξ₁ Ξ₂ = biLift S.oma S.omb S.B.vA S.J.v0 φ (GlobalTheory.Unf.contr S.l S.J.W₀ S.vL Ξ₁ Ξ₂)

variable {S}

theorem theta_flatBF {f : WO S.B.V S.J.W → ℂ} (hf : IsThetaFunO ψ _ _ f) : IsThetaFunO ψ _ _ (flatBF S.s₁ f) :=
  (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) ψ).1 _ _ _ S.s₁ f hf

theorem theta_flatFB {f : WO S.J.W S.B'.V → ℂ} (hf : IsThetaFunO ψ _ _ f) : IsThetaFunO ψ _ _ (flatFB S.s₂ f) :=
  (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) ψ).2 _ _ _ S.s₂ f hf

theorem val_eq_hand (hS : HandIsLift S) {Φ₁ : WO S.B.V S.J.W → ℂ} {Φ₂ : WO S.J.W S.B'.V → ℂ} (h₁ : IsThetaFunO ψ _ _ Φ₁)
    (h₂ : IsThetaFunO ψ _ _ Φ₂) {φ : GA D S.B.A → ℂ} (hφ : IsContAut _ φ) (f : GA D S.B'.V → ℂ) (g x y) :
    S.val (Finsupp.single 0 1) (Finsupp.single 0 1) Φ₁ Φ₂ φ f g x y =
      S.B'.per ψ (Chain.hand S.s₁ S.s₂ S.l S.vL Φ₁ Φ₂ φ g x y) (rTrans y f) := by
  unfold Dbl2.val Dbl2.con
  rw [biComb_single_zero, ← hS φ _ _ hφ (theta_flatBF (S.s₁.weil.om_pres _ _ h₁)) (theta_flatFB (S.s₂.weil.om_pres _ _ h₂))]
  rfl

theorem val_one (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (Φ₁ : WO S.B.V S.J.W → ℂ) (Φ₂ : WO S.J.W S.B'.V → ℂ)
    (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ) :
    S.val c₁ c₂ Φ₁ Φ₂ φ f 1 1 1 = S.B'.per ψ (biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ _ _ _ c₁ c₂
      (GlobalTheory.Unf.contr S.l S.J.W₀ S.vL (flatBF S.s₁ Φ₁) (flatFB S.s₂ Φ₂)))) f := by
  unfold Dbl2.val Dbl2.con
  have e1 : S.s₁.om (1, 1) Φ₁ = Φ₁ := by rw [Prod.mk_one_one, map_one]; rfl
  have e2 : S.s₂.om (1, 1) Φ₂ = Φ₂ := by rw [Prod.mk_one_one, map_one]; rfl
  have e3 : rTrans 1 f = f := by funext z; simp [rTrans]
  rw [e1, e2, e3]

theorem contAut_lift (hψ : IsStdChar D ψ (-1)) (hS : HandIsLift S) {c₁ : WO S.B.A S.J.W₀ →₀ ℂ} {c₂ : WO S.J.W₀ S.B'.A →₀ ℂ}
    (hc₁ : IsFinComb c₁) (hc₂ : IsFinComb c₂) {Φ₁ : WO S.B.V S.J.W → ℂ} {Φ₂ : WO S.J.W S.B'.V → ℂ} (h₁ : IsThetaFunO ψ _ _ Φ₁)
    (h₂ : IsThetaFunO ψ _ _ Φ₂) {φ : GA D S.B.A → ℂ} (hφ : IsContAut _ φ) :
    IsContAut S.B'.A (biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ _ _ _ c₁ c₂
      (GlobalTheory.Unf.contr S.l S.J.W₀ S.vL (flatBF S.s₁ Φ₁) (flatFB S.s₂ Φ₂)))) := by
  have t₁ := GlobalTheory.AvgMid.theta_comb hψ (isFinComb_extS S.B.o S.J.W₀ hc₁) (theta_flatBF h₁)
  have t₂ := GlobalTheory.AvgMid.theta_comb hψ (isFinComb_extT S.B'.o S.J.W₀ hc₂) (theta_flatFB h₂)
  rw [← (GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D ψ hψ _ _ S.B S.B' S.l S.J.W₀ S.vL _ _ (theta_flatBF h₁) (theta_flatFB h₂)).2.1, ← hS φ _ _ hφ t₁ t₂]
  exact GlobalTheory.FinPl.Comm.contAut_hand0 _ _ _ _ hφ t₁ t₂

end Step

end GlobalTheory.QLawPf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedThetaLiftCommutesSplitPlaceOperators
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedThetaLiftCommutesSplitPlaceOperators
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing MeasureTheory

noncomputable section

namespace GlobalTheory.FinPl.LiftRam

variable {D : D7}

def contAutSub (S : HSp D) : Submodule ℂ (GA D S → ℂ) where
  carrier := {φ | IsContAut S φ}
  add_mem' := fun {a b} ha hb =>
    ⟨fun γ hγ g => by simp only [Pi.add_apply, ha.1 γ hγ g, hb.1 γ hγ g], ha.2.add hb.2⟩
  zero_mem' := ⟨fun _ _ _ => rfl, continuous_const⟩
  smul_mem' := fun c a ha => ⟨fun γ hγ g => by simp only [Pi.smul_apply, ha.1 γ hγ g], ha.2.const_smul c⟩

theorem isContAut_mul_right {S : HSp D} {φ : GA D S → ℂ} (hφ : IsContAut S φ) (a : GA D S) :
    IsContAut S (fun x => φ (x * a)) :=
  ⟨fun γ hγ g => by simp only [mul_assoc]; exact hφ.1 γ hγ (g * a), hφ.2.comp (continuous_mul_const a)⟩

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

def repAut (α : Frame p S n) : Representation ℂ (GL n k) (contAutSub S) where
  toFun g := (α.rep g).restrict (p := contAutSub S) (q := contAutSub S)
    (fun v hv => isContAut_mul_right hv (α.gl g))
  map_one' := by
    apply LinearMap.ext; intro v; apply Subtype.ext; funext x
    simp [Frame.rep, LinearMap.restrict_apply]
  map_mul' g h := by
    apply LinearMap.ext; intro v; apply Subtype.ext; funext x
    simp [Frame.rep, LinearMap.restrict_apply, mul_assoc]

theorem repAut_val (α : Frame p S n) (g : GL n k) (v : contAutSub S) : (repAut α g v).1 = α.rep g v.1 := rfl

theorem rep_apply (α : Frame p S n) (g : GL n k) (v : GA D S → ℂ) (x : GA D S) : α.rep g v x = v (x * α.gl g) := rfl

end Rep

end GlobalTheory.FinPl.LiftRam

namespace GlobalTheory.FinPl.LiftRam

variable {D : D7}

section Kernel

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}

theorem om_left (hW : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D S}
    (hγ : γ ∈ GQ S) (g : GA D S) (h : GA D T) : om (γ * g, h) f 0 = om (g, h) f 0 := by
  have e : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hW.om_aut γ hγ 1 (one_mem _) _ (hW.om_pres _ _ hf)

theorem weilRep_thetaValue_leftInvariant_rational_second (hW : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D T}
    (hγ : γ ∈ GQ T) (g : GA D S) (h : GA D T) : om (g, γ * h) f 0 = om (g, h) f 0 := by
  have e : ((g, γ * h) : GA D S × GA D T) = (1, γ) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hW.om_aut 1 (one_mem _) γ hγ _ (hW.om_pres _ _ hf)

theorem om_mul (g a : GA D S) (h b : GA D T) (f : WO S T → ℂ) : om (g, h) (om (a, b) f) = om (g * a, h * b) f := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]

theorem setIntegral_mul_right (hS : CoCpt S) (v : Vol S) (G : GA D S → ℂ) (hG : ∀ γ ∈ GQ S, ∀ h, G (γ * h) = G h)
    (a : GA D S) : ∫ h in v.𝓕, G (h * a) ∂v.μ = ∫ h in v.𝓕, G h ∂v.μ := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  haveI := v.haar
  obtain ⟨K, hK, hcov⟩ := hS
  have hmap : ∀ b : GA D S, v.μ.map (· * b) = v.μ := fun b =>
    Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice v.μ (GQ S) hK hcov b
  have hmp : MeasurePreserving (· * a) v.μ v.μ := ⟨measurable_mul_const a, hmap a⟩
  have hmp' : MeasurePreserving (· * a⁻¹) v.μ v.μ := ⟨measurable_mul_const a⁻¹, hmap a⁻¹⟩
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight a) G v.𝓕, Set.image_mul_right]
  have hF : IsFundamentalDomain (GQ S) ((· * a⁻¹) ⁻¹' v.𝓕) v.μ :=
    v.fund.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (v.fund.setIntegral_eq hF fun γ x => hG γ γ.2 x).symm

theorem lift_facts (hS : CoCpt S) (vS : Vol S) (hW : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {φ : GA D S → ℂ} (hφ : IsContAut S φ) :
    (∀ h, IntegrableOn (fun g => om (g, h) f 0 * φ g) vS.𝓕 vS.μ) ∧ IsContAut T (liftT om vS.μ vS.𝓕 φ f) := by
  have hK := GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D S hS vS (GA D T) (fun g h => om (g, h) f 0 * φ g)
    ((hW.om_cont f hf 0).mul (hφ.2.comp continuous_fst))
    (fun γ hγ g h => by rw [om_left hW hf hγ, hφ.1 γ hγ g])
  refine ⟨hK.1, fun γ hγ h => ?_, ?_⟩
  · simp only [liftT_apply]
    congr 1
    funext g
    rw [weilRep_thetaValue_leftInvariant_rational_second hW hf hγ]
  · have e : liftT om vS.μ vS.𝓕 φ f = fun h => ∫ g in vS.𝓕, om (g, h) f 0 * φ g ∂vS.μ :=
      funext fun h => liftT_apply _ _ _ _ _ h
    rw [e]
    exact hK.2.1

end Kernel

end GlobalTheory.FinPl.LiftRam

namespace GlobalTheory.FinPl.LiftRam

variable {D : D7}

section Forms

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem formAt_eq (β : Frame p S n) {φ : Form k n (GA D S → ℂ)} (hφ : φ ∈ EqForm β.rep) (P : Pair k n) :
    formAt β P (φ P) = φ := by
  funext P₁
  have hex := MulAction.exists_smul_eq (GL n k) P P₁
  have hs := Classical.epsilon_spec hex
  simp only [formAt]
  rw [← hφ, hs]

def toAut {φ : Form k n (GA D S → ℂ)} (hφ : ∀ P, IsContAut S (φ P)) : Form k n (contAutSub S) :=
  fun P => ⟨φ P, hφ P⟩

theorem toAut_FFStar (q : Unif k) (χ : AddChar 𝓀[k] ℂ) {φ : Form k n (GA D S → ℂ)} (hφ : ∀ P, IsContAut S (φ P))
    (P : Pair k n) : (FFStar q χ (toAut hφ) P).1 = FFStar q χ φ P := by
  simp only [FFStar_apply, Submodule.coe_sum, Submodule.coe_smul]
  rfl

end Forms

end GlobalTheory.FinPl.LiftRam

namespace GlobalTheory.FinPl


open GlobalTheory.FinPl.LiftRam in
theorem lift_sOp_comm : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), CoCpt S → ∀ (vS : Vol S) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS p.v → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT p.v → ∀ (α : Frame p S n') (β : Frame p T n) (P : Pair k n') (Q : Pair k n), ∃ c : ℂ, c ≠ 0 ∧ ∀ (LS : Lat S) (LT : Lat T) (f₀ f : WO S T → ℂ), Over ψ α β LS LT f₀ (phiOne P Q) f → ∀ φ₀, RamAt α P φ₀ → RamAt β Q (liftT om vS.μ vS.𝓕 φ₀ f) ∧ ∀ ε : 𝓀[k]ˣ, liftT om vS.μ vS.𝓕 (sOp α P q (resChar χ hχ q) ε φ₀) f = c • sOp β Q q (resChar χ hχ q) ε (liftT om vS.μ vS.𝓕 φ₀ f) := by
  intro D k _ _ _ _ p n n' _ _ _ _ q χ hχ ψ S T hS vS χS χT om hW hχS hχT α β P Q
  obtain ⟨lS, lT, hlS, hlT, hlin⟩ := GlobalTheory.T.splitPlace_linearModel_latticeVacuum_base D k p ψ S T χS χT om hW
  obtain ⟨c, hc0, hK⟩ := GlobalTheory.T.kernelsCommuteTwistedAlt k n n' q χ hχ lS lT (hlS hχT) (hlT hχS) P Q
  refine ⟨c, hc0, ?_⟩
  intro LS LT f₀ f hOv φ₀ hφ₀
  have hOv2 := hOv
  obtain ⟨hLS, hLT, hVac, -, -⟩ := hOv2
  obtain ⟨hex, hth, -⟩ := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hW.std S T α β LS LT hLS hLT f₀ hVac

  let F : SB (Matrix n n' k) → WO S T → ℂ := fun Ψ => (hex Ψ.1 Ψ.2).exists.choose
  have hF : ∀ Ψ : SB (Matrix n n' k), Over ψ α β LS LT f₀ Ψ.1 (F Ψ) := fun Ψ => (hex Ψ.1 Ψ.2).exists.choose_spec
  have hFu : ∀ (Ψ : SB (Matrix n n' k)) g, Over ψ α β LS LT f₀ Ψ.1 g → g = F Ψ :=
    fun Ψ g hg => (hex Ψ.1 Ψ.2).unique hg (hF Ψ)
  have hFth : ∀ Ψ, IsThetaFunO ψ S T (F Ψ) := fun Ψ => (hth _ _ (hF Ψ)).1
  have hFlin : ∀ (a : ℂ) (Ψ Ψ' : SB (Matrix n n' k)), F (a • Ψ + Ψ') = a • F Ψ + F Ψ' := fun a Ψ Ψ' =>
    (hFu (a • Ψ + Ψ') _ ((hlin n n' α β LS LT f₀ Ψ.1 (F Ψ) (hF Ψ)).2.2 a Ψ'.1 (F Ψ') (hF Ψ'))).symm
  have hF0 : F 0 = 0 := by
    have h1 := hFlin 1 0 0
    simp only [one_smul, add_zero] at h1
    have h2 : F 0 + F 0 = F 0 + 0 := by rw [← h1, add_zero]
    exact add_left_cancel h2
  have hFadd : ∀ Ψ Ψ' : SB (Matrix n n' k), F (Ψ + Ψ') = F Ψ + F Ψ' := fun Ψ Ψ' => by
    simpa using hFlin 1 Ψ Ψ'
  have hFsmul : ∀ (a : ℂ) (Ψ : SB (Matrix n n' k)), F (a • Ψ) = a • F Ψ := fun a Ψ => by
    simpa [hF0] using hFlin a Ψ 0
  have hint : ∀ (v : contAutSub S) (Ψ : SB (Matrix n n' k)) h,
      IntegrableOn (fun g => om (g, h) (F Ψ) 0 * v.1 g) vS.𝓕 vS.μ :=
    fun v Ψ h => (lift_facts hS vS hW (hFth Ψ) v.2).1 h

  let θ : contAutSub S →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] (GA D T → ℂ) :=
    LinearMap.mk₂ ℂ (fun v Ψ => liftT om vS.μ vS.𝓕 v.1 (F Ψ))
      (fun v₁ v₂ Ψ => by
        funext h
        simp only [liftT_apply, Pi.add_apply, Submodule.coe_add, mul_add]
        exact integral_add (hint v₁ Ψ h) (hint v₂ Ψ h))
      (fun a v Ψ => by
        funext h
        simp only [liftT_apply, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, mul_left_comm _ a]
        exact integral_const_mul a _)
      (fun v Ψ₁ Ψ₂ => by
        funext h
        simp only [liftT_apply, Pi.add_apply, hFadd, map_add (f := _), add_mul]
        exact integral_add (hint v Ψ₁ h) (hint v Ψ₂ h))
      (fun a v Ψ => by
        funext h
        simp only [liftT_apply, Pi.smul_apply, hFsmul, map_smul, smul_eq_mul, mul_assoc]
        exact integral_const_mul a _)
  have hθ : ∀ v Ψ, θ v Ψ = liftT om vS.μ vS.𝓕 v.1 (F Ψ) := fun v Ψ => rfl
  have hEq : ∀ (g : GL n' k) (h : GL n k) (v : contAutSub S) (Ψ Ψ' : SB (Matrix n n' k)),
      (∀ x, Ψ'.1 x = (lS (Matrix.GeneralLinearGroup.det g) : ℂ) * (lT (Matrix.GeneralLinearGroup.det h) : ℂ) *
        Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (repAut α g v) Ψ' = β.rep h (θ v Ψ) := by
    intro g h v Ψ Ψ' hΨ
    have e : F Ψ' = om (α.gl g, β.gl h) (F Ψ) := by
      refine (hFu Ψ' _ ?_).symm
      have := (hlin n n' α β LS LT f₀ Ψ.1 (F Ψ) (hF Ψ)).1 g h
      convert this using 1
      funext x
      exact hΨ x
    funext h₁
    rw [hθ, hθ, rep_apply, liftT_apply, liftT_apply, e, repAut_val]
    simp only [rep_apply, om_mul]
    exact setIntegral_mul_right hS vS (fun x => om (x, h₁ * β.gl h) (F Ψ) 0 * v.1 x)
      (fun γ hγ x => by rw [om_left hW (hFth Ψ) hγ, v.2.1 γ hγ x]) (α.gl g)
  obtain ⟨K, hKval, hKdia, hKram⟩ := hK (contAutSub S) (GA D T → ℂ) (repAut α) β.rep θ hEq
  obtain ⟨φ, ⟨hφE, hφM, hφC⟩, rfl⟩ := hφ₀
  let φ' : EqForm (repAut α) := ⟨toAut hφC, fun g P₁ => Subtype.ext (hφE g P₁)⟩
  have hφ'M : φ'.1 ∈ Mram k n' (contAutSub S) := by
    letI := Fintype.ofFinite 𝓀[k]ˣ
    refine (mem_Mram _).2 fun P₁ => Subtype.ext ?_
    have := (mem_Mram _).1 hφM P₁
    simpa [φ', toAut, Submodule.coe_sum] using this
  have hFf : F (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOneSB P Q) = f := (hFu _ f hOv).symm
  have hfth : IsThetaFunO ψ S T f := hFf ▸ hFth _
  set φT : Form k n (GA D T → ℂ) := (K φ').1 with hφT
  have hφTQ : φT Q = liftT om vS.μ vS.𝓕 (φ P) f := by
    rw [hφT, hKval φ', hθ, hFf]
    rfl
  have hcQ : IsContAut T (φT Q) := by
    rw [hφTQ]
    exact (lift_facts hS vS hW hfth (hφC P)).2
  have hRam : IsRam β φT := by
    refine ⟨(K φ').2, (hKram φ' hφ'M).1, fun Q' => ?_⟩
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q Q'
    have e : φT (g • Q) = β.rep g (φT Q) := (K φ').2 g Q
    rw [e]
    exact isContAut_mul_right hcQ (β.gl g)
  refine ⟨⟨φT, hRam, hφTQ⟩, fun ε => ?_⟩
  have h1 := (hKram φ' hφ'M).2
  have h2 := hKdia ε ⟨FFStar q (resChar χ hχ q) φ'.1, FFStar_mem_EqForm q _ φ'.2⟩
  have h3 := hKval ⟨dia ε (FFStar q (resChar χ hχ q) φ'.1), dia_mem_EqForm ε (FFStar_mem_EqForm q _ φ'.2)⟩
  have key : liftT om vS.μ vS.𝓕 (FFStar q (resChar χ hχ q) φ (ε • P)) f =
      c • FFStar q (resChar χ hχ q) φT (ε • Q) := by
    calc liftT om vS.μ vS.𝓕 (FFStar q (resChar χ hχ q) φ (ε • P)) f
        = θ (dia ε (FFStar q (resChar χ hχ q) φ'.1) P) (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOneSB P Q) := by
          rw [hθ, hFf, dia_apply]
          exact congrArg (liftT om vS.μ vS.𝓕 · f) (toAut_FFStar q _ hφC (ε • P)).symm
      _ = (K ⟨dia ε (FFStar q (resChar χ hχ q) φ'.1), dia_mem_EqForm ε (FFStar_mem_EqForm q _ φ'.2)⟩).1 Q := h3.symm
      _ = dia ε (K ⟨FFStar q (resChar χ hχ q) φ'.1, FFStar_mem_EqForm q _ φ'.2⟩).1 Q := by rw [h2]
      _ = c • FFStar q (resChar χ hχ q) φT (ε • Q) := by rw [h1, dia_apply]; rfl
  rw [← hφTQ]
  unfold sOp
  rw [formAt_eq α hφE P, formAt_eq β hRam.1 Q, dia_apply, dia_apply]
  exact key

end GlobalTheory.FinPl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedThetaLiftCommutesSplitPlaceOperatorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedThetaLift_commutes_splitPlace_operators : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), CoCpt S → ∀ (vS : Vol S) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS p.v → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT p.v → ∀ (α : Frame p S n') (β : Frame p T n) (P : Pair k n') (Q : Pair k n), ∃ c : ℂ, c ≠ 0 ∧ ∀ (LS : Lat S) (LT : Lat T) (f₀ f : WO S T → ℂ), Over ψ α β LS LT f₀ (phiOne P Q) f → ∀ φ₀, RamAt α P φ₀ → RamAt β Q (liftT om vS.μ vS.𝓕 φ₀ f) ∧ ∀ ε : 𝓀[k]ˣ, liftT om vS.μ vS.𝓕 (sOp α P q (resChar χ hχ q) ε φ₀) f = c • sOp β Q q (resChar χ hχ q) ε (liftT om vS.μ vS.𝓕 φ₀ f) := by
  first | exact @GlobalTheory.FinPl.lift_sOp_comm | exact GlobalTheory.FinPl.lift_sOp_comm | (intros; apply GlobalTheory.FinPl.lift_sOp_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPNotMemOfIdemSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerLift

theorem conjP_notMem_of_isIdemSum {D : D7} {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e SS) :
    ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS := by
  intro P hP hP'
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := he
  have horth := Formalism.IndefR.Fin.LevelGroupLemmas.idemSum_conj_orth hes hsum hc P hP (Formalism.L2.Col.conjPrime₂ P) hP'
  have h1 : Formalism.L2.NTheta.IsIdemAt (cA D (es (Formalism.L2.Col.conjPrime₂ P))) P := by
    refine GlobalTheory.MovedIdem.isIdemAt_conj (hes _ hP') fun x => ?_
    show x ∈ P.asIdeal ↔ Formalism.L2.Col.cO D.host.E (Formalism.L2.Col.cO D.host.E x) ∈ P.asIdeal
    have : Formalism.L2.Col.cO D.host.E (Formalism.L2.Col.cO D.host.E x) = x := by
      apply RingOfIntegers.ext
      simp [Formalism.L2.Col.cO]
    rw [this]
  have heq : cA D (es (Formalism.L2.Col.conjPrime₂ P)) = es P :=
    (GlobalTheory.ExportSeries.idemAt_eq h1).symm.trans (GlobalTheory.ExportSeries.idemAt_eq (hes P hP))
  rw [heq, (hes P hP).1.1] at horth
  have hI := hes P hP
  rw [horth] at hI
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have := (hI.2 x hx0).1 hxP
  rw [zero_mul, map_zero] at this
  exact this (zero_mem _)

theorem natCast_smul_inv_smul {E : Type} [Field E] [NumberField E] {a b : ℕ} (c : ℕ) (hc : 0 < c)
    (y : Formalism.L2.Col.HomE E a b) : ((c : 𝓞 E)) • ((c : E)⁻¹ • y) = y := by
  have hc0 : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  rw [Nat.cast_smul_eq_nsmul (𝓞 E), ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hc0, one_smul]


set_option maxHeartbeats 800000 in
theorem exists_rep_add_mem : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ c : ℕ, 0 < c → ∀ (SX : Finset (VV D.what₂.Tau S.rank T.rank)), Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) SX → ∀ (px : VV D.what₂.Tau S.rank T.rank → Formalism.L2.Col.HomE D.host.E S.rank T.rank), (∀ x ∈ SX, px x ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c ∧ embH (tauE D) δ (px x) = x) → ∀ g : Formalism.L2.Col.HomE D.host.E S.rank T.rank, (∀ P ∈ SS, (c : D.host.E) • g ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) → ∃ x ∈ SX, ∀ P ∈ SS, g + px x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D ψ θ S T δ sc hP e SS he N N' hN hN' c hc SX hSX px hpx g hg
  have hSS := conjP_notMem_of_isIdemSum he
  have hAA : (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ≠ ⊥ := fun h =>
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.leading_constant_ne_zero D (FractionalIdeal.coeToSubmodule_eq_bot.1 h)
  have hspan : ∀ x : Formalism.L2.Col.HomE D.host.E S.rank T.rank, ∃ n : ℕ, 0 < n ∧ (n : D.host.E) • x ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' :=
    by
      have hfull : Submodule.span D.host.E (N' : Set (Fin T.rank → D.host.E)) = ⊤ := by
        obtain ⟨n, s, s', hs, hd⟩ := GlobalTheory.T.exists_dual_family_selfDual_hermitianSpace D T N' hN'
        apply top_unique
        intro v _
        have hv : v = ∑ i, (∑ j, (∑ k, star (s' i k) * T.gram k j) * v j) • s i := by
          ext a
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          calc
            v a = ∑ j : Fin T.rank, (if a = j then 1 else 0) * v j := by simp
            _ = ∑ j, (∑ i, s i a * (∑ k, star (s' i k) * T.gram k j)) * v j := by simp_rw [hd]
            _ = ∑ i, (∑ j, (∑ k, star (s' i k) * T.gram k j) * v j) * s i a := by
              simp only [Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              apply Finset.sum_congr rfl
              intro k _
              ring
        rw [hv]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs i).1)
      exact Formalism.L2.Ker.lf_span _ hAA N N' hN.1.fg hfull
  have hneg : ∀ P ∈ SS, (c : D.host.E) • (-g) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := fun P hP' => by
    rw [smul_neg]; exact neg_mem (hg P hP')
  have hL := Formalism.L2.Ker.lift_exists_alt D.host.E S.rank T.rank SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c hc hSS hspan (-g) hneg
  obtain ⟨hsA, hsP⟩ := hL
  generalize Formalism.L2.Ker.liftS SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c (-g) = s at hsA hsP
  have hmem : embH (tauE D) δ s ∈ AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c :=
    ⟨s, hsA, rfl⟩
  obtain ⟨x, hxS, hxL⟩ := hSX.2.2 _ hmem
  obtain ⟨β, hβ, hβe⟩ := hxL
  have hne : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hβs : β = s - px x := by
    apply Formalism.L2.Ker.embH_inj (tauE D) hP.ne
    rw [map_sub, (hpx x hxS).2]
    exact hβe
  refine ⟨x, hxS, fun P hPS => ?_⟩
  have h1 : s + g ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
    have h2 := hsP P hPS
    rw [sub_neg_eq_add] at h2
    have h3 : ((c : 𝓞 D.host.E)) • ((c : D.host.E)⁻¹ • (s + g)) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :=
      Submodule.smul_mem _ _ h2
    have e3 := natCast_smul_inv_smul c hc (s + g)
    rwa [e3] at h3
  have h4 : β ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hβ⟩
  have e5 : g + px x = (s + g) - β := by rw [hβs]; abel
  rw [e5]
  exact sub_mem h1 h4

end GlobalTheory.PerLift
end

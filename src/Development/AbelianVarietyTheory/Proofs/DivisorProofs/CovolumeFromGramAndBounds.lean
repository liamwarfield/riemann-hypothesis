module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeepsCuspLatticeNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionDualNumberPointEqConstantCharZero
public import Formalism.LocalToGlobal.ProjectiveLattices.TieGenDense
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupremumConstantLogBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentPhiLinear

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFromGramAndBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajAtAddRight
open NumberField GlobalTheory.AllWt

namespace GlobalTheory.CutNum

open Module Formalism.HermitianLatticesTheory

section Maj

variable {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
  (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)

theorem fcoord_add' (x y : V) : fcoord b X v (x + y) = fcoord b X v x + fcoord b X v y := by
  have hv : vecAt b v (x + y) = vecAt b v x + vecAt b v y := by
    funext i
    simp [vecAt]
  simp only [fcoord, hv, Matrix.mulVec_add]

theorem fcoord_smul' (a : K) (x : V) : fcoord b X v (a • x) = v.embedding a • fcoord b X v x := by
  have hv : vecAt b v (a • x) = v.embedding a • vecAt b v x := by
    funext i
    simp [vecAt]
  simp only [fcoord, hv, Matrix.mulVec_smul]

theorem normAt_add_sq (x y : V) :
    normAt b X v (x + y) ^ 2 = normAt b X v x ^ 2 + normAt b X v y ^ 2 + 2 * (majAt b X v x y).re := by
  simp only [normAt, cnorm, majAt, fcoord_add']
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Complex.re_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem majAt_smul_left' (a : K) (x y : V) :
    majAt b X v (a • x) y = star (v.embedding a) * majAt b X v x y := by
  simp only [majAt, fcoord_smul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring

theorem majAt_add_right' (x y z : V) : majAt b X v x (y + z) = majAt b X v x y + majAt b X v x z := by
  simp only [majAt, fcoord_add', Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem star_majAt' (x y : V) : star (majAt b X v x y) = majAt b X v y x := by
  simp only [majAt, star_sum, star_mul', star_star]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem selfAdj_of_pyth (hv : v.IsComplex) (e : V →ₗ[K] V)
    (h : ∀ x y, normAt b X v (e x + (y - e y)) ^ 2 = normAt b X v (e x) ^ 2 + normAt b X v (y - e y) ^ 2) (x y : V) :
    majAt b X v (e x) y = majAt b X v x (e y) := by
  have hre : ∀ x y, (majAt b X v (e x) (y - e y)).re = 0 := by
    intro x y
    have h1 := normAt_add_sq b X v (e x) (y - e y)
    have h2 := h x y
    linarith
  obtain ⟨a, ha⟩ : ∃ a : K, (v.embedding a).im ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply InfinitePlace.isComplex_iff.mp hv
    first
    | exact fun t => Complex.conj_eq_iff_im.mpr (hcon t)
    | (rw [ComplexEmbedding.isReal_iff]; ext t; exact Complex.conj_eq_iff_im.mpr (hcon t))
  have hzero : ∀ x y, majAt b X v (e x) (y - e y) = 0 := by
    intro x y
    have h0 := hre x y
    have h1 := hre (a • x) y
    rw [map_smul, majAt_smul_left'] at h1
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, h0] at h1
    have hm : (v.embedding a).im * (majAt b X v (e x) (y - e y)).im = 0 := by linarith
    refine Complex.ext (by simpa using h0) ?_
    rcases mul_eq_zero.mp hm with hm | hm
    · exact absurd hm ha
    · simpa using hm
  have hL : majAt b X v (e x) y = majAt b X v (e x) (e y) := by
    have := majAt_add_right' b X v (e x) (e y) (y - e y)
    rw [hzero, add_zero, show e y + (y - e y) = y by abel] at this
    exact this
  have hR : majAt b X v x (e y) = majAt b X v (e x) (e y) := by
    have := majAt_add_right' b X v (e y) (e x) (x - e x)
    rw [hzero, add_zero, show e x + (x - e x) = x by abel] at this
    rw [← star_majAt' b X v (e y) x, this, star_majAt']
  rw [hL, hR]

end Maj

theorem numeric {dg db μ μg m lg δ Q : ℝ} (hd : 0 < dg + db) (hdg : 0 ≤ dg) (hdb : 0 ≤ db)
    (hcut : (dg + db) * μ ≤ dg * μg + db * (m + lg)) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 12) (hb : db ≤ 3 * δ * (dg + db))
    (hm : m ≤ Q) (hμ : -Q ≤ μ) (hlg : lg ≤ Q) (hlg0 : 0 ≤ lg) : μ - 12 * δ * Q ≤ μg := by
  have hQ : 0 ≤ Q := by linarith
  have hδdb : δ * db ≤ 1 / 12 * db := mul_le_mul_of_nonneg_right hδ' hdb
  have hdg0 : 0 < dg := by
    rcases lt_or_eq_of_le hdg with h | h
    · exact h
    · subst h
      nlinarith
  have h4 : db ≤ 4 * δ * dg := by nlinarith
  have k1 : db * (-Q) ≤ db * μ := mul_le_mul_of_nonneg_left hμ hdb
  have k2 : db * Q ≤ 4 * δ * dg * Q := mul_le_mul_of_nonneg_right h4 hQ
  have k3 : db * m ≤ db * Q := mul_le_mul_of_nonneg_left hm hdb
  have k4 : db * lg ≤ db * Q := mul_le_mul_of_nonneg_left hlg hdb
  have key : dg * (μ - 12 * δ * Q) ≤ dg * μg := by nlinarith
  exact le_of_mul_le_mul_left key hdg0

theorem slope_good_ge : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ) (L M : Submodule (𝓞 K) V) (e : V →ₗ[K] V) (g : ℕ) (δ Q : ℝ), HasGram N → M.FG → L ≤ M → L ≠ ⊥ → e ∘ₗ e = e → (∀ σ x y, N σ (e x + (y - e y)) ^ 2 = N σ (e x) ^ 2 + N σ (y - e y) ^ 2) → 1 ≤ g → (∀ x ∈ L, (g : K) • e x ∈ L) → 0 ≤ δ → δ ≤ 1 / 12 → (Formalism.HN.rkK (L ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) ≤ 3 * δ * Formalism.HN.rkK L → slopeMax_sq N M ≤ Q → -Q ≤ slope_sq N L → 2 * Real.log g ≤ Q → slope_sq N L - 12 * δ * Q ≤ slope_sq N (L ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) := by
  intro K V _ _ _ _ _ _ _ N L M e g δ Q hGram hM hLM hL0 hee hpyth hg hint hδ hδ' hrk hmax hmin hlog
  letI : StarRing K := starRingOfComm
  obtain ⟨F⟩ := hGram
  obtain ⟨n, ⟨⟨b, X⟩, hG⟩⟩ := F
  have hX : ∀ v, IsUnit (X v).det := fun v => (hG v).1
  have hLfg : L.FG := Submodule.FG.of_le hM hLM
  have hRfg : (L ⊓ (LinearMap.range e).restrictScalars (𝓞 K)).FG :=
    Submodule.FG.of_le hM (inf_le_left.trans hLM)
  have hsa : ∀ v x y, majAt b X v (e x) y = majAt b X v x (e y) := by
    intro v
    apply selfAdj_of_pyth b X v (IsTotallyComplex.isComplex v) e
    intro x y
    simp only [(hG v).2]
    exact hpyth v.embedding x y
  obtain ⟨hrkadd, hcut, hmaj⟩ := Formalism.ExtensionFiltration.goodBadCut K V (Fin n) b X hX e g L hLfg hg hee hsa hint
  have hM0 : M ≠ ⊥ := fun h => hL0 (le_bot_iff.mp (h ▸ hLM))
  rw [slope_sq_eq hG hLfg] at hmin ⊢
  rw [slope_sq_eq hG hRfg]
  rw [(slopeMax_slopeMin_eq hG hM hM0).1] at hmax
  have hne := Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero b L hL0
  have hrkR : (Formalism.HN.rkK L : ℝ) = (Formalism.HN.rkK (L ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) : ℝ) +
      (Formalism.HN.rkK (L ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) := by
    exact_mod_cast hrkadd.symm
  have hpos : (0 : ℝ) < Formalism.HN.rkK L := by exact_mod_cast Nat.pos_of_ne_zero hne
  have hmj := hmaj M hM hLM
  have hlg0 : 0 ≤ 2 * Real.log g := by
    have : (1 : ℝ) ≤ g := by exact_mod_cast hg
    have := Real.log_nonneg this
    linarith
  rw [hrkR] at hcut hrk hpos
  exact numeric hpos (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith) hδ hδ' hrk hmax hmin hlog hlg0

end GlobalTheory.CutNum
end

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.AllWt GlobalTheory.BigTop Filter Topology

namespace GlobalTheory.CovTop.Assembly

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tendsto_exp_mul_rpow {c : ℝ} (hc : 0 < c) (A : ℝ) :
    Tendsto (fun x : ℝ => Real.exp (-(x ^ c)) * x ^ A) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / c) 1 one_pos).comp (tendsto_rpow_atTop hc)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  simp only [Function.comp]
  rw [← Real.rpow_mul hx, mul_div_cancel₀ _ hc.ne', mul_comm, neg_mul, one_mul]

theorem exists_loss_le {c : ℝ} (hc : 0 < c) (A B C : ℝ) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → 12 * Real.exp (-(x ^ c)) * (x ^ A + x ^ B + C) ≤ 1 := by
  have h := ((((tendsto_exp_mul_rpow hc A).add (tendsto_exp_mul_rpow hc B)).add
    ((tendsto_exp_mul_rpow hc 0).mul_const C)).const_mul 12)
  have h1 : (12 : ℝ) * (0 + 0 + 0 * C) < 1 := by norm_num
  obtain ⟨x0, hx0⟩ := eventually_atTop.1 (h.eventually (gt_mem_nhds h1))
  refine ⟨x0, fun x hx => ?_⟩
  have := hx0 x hx
  simp only [Real.rpow_zero] at this
  nlinarith

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem lcv_le {A B PP C1 C2 : ℝ} (hx : 0 < L.sc.x) (h1 : 0 ≤ C1) (h2 : 0 ≤ C2)
    (hs : 12 * Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) * (L.sc.x ^ A + L.sc.x ^ B + (C1 + C2 + 1)) ≤ 1)
    (hG : GramAt p i) (hR : RecAt p i) (hC : CutAt p i) (hB : BadAt p i) (hL : LamAt p i A) (hS : SizeAt p i PP B)
    (hK : CoreAt p i C1) (hW : LowAt p i C2) :
    Formalism.DivisionValues.lcv ((p.S false).XW i) ((p.S false).M i) / ((p.S false).D : ℝ) ≤ mainT p i + (C1 + C2 + 1) * unitE p := by
  haveI : IsTotallyComplex D.what₂.LL := D.tcLL
  obtain ⟨g1, g2, g3, -⟩ := hG
  obtain ⟨c1, c2, c3, c4⟩ := hC
  obtain ⟨s1, s2, -, s4, -⟩ := hS
  unfold RecAt at hR
  unfold LamAt at hL
  unfold CoreAt at hK
  unfold LowAt at hW
  have hA := Real.rpow_pos_of_pos hx A
  have hB' := Real.rpow_pos_of_pos hx B
  have hδ := Real.exp_pos (-(L.sc.x ^ (L.sc.ez / 7)))
  have hm := (abs_le.1 s4).2
  have key := GlobalTheory.CutNum.slope_good_ge D.what₂.LL _ (nrmR p.R.toRealDat i) (latType p.R.toRealDat p.F.lv2 i)
    (latAll p.R.toRealDat i) (eGood p.R.toRealDat i) (Fintype.card p.P.Gp) (Real.exp (-(L.sc.x ^ (L.sc.ez / 7))))
    ((L.sc.x ^ A + L.sc.x ^ B + (C1 + C2 + 1)) * unitE p) g1 g2 inf_le_left
    (fun h => g3 (le_bot_iff.1 (h ▸ latGood_le p.R.toRealDat p.F.lv2 i))) c1 c2 Fintype.card_pos c3 hδ.le
  have key' : slope_sq (nrmR p.R.toRealDat i) (latType p.R.toRealDat p.F.lv2 i) -
      12 * Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) * ((L.sc.x ^ A + L.sc.x ^ B + (C1 + C2 + 1)) * unitE p) ≤
      slope_sq (nrmR p.R.toRealDat i) (latGood p.R.toRealDat p.F.lv2 i) := by
    refine key ?_ hB ?_ ?_ ?_
    all_goals
      clear key hR
      generalize Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) = δ at *
      generalize L.sc.x ^ A = a at *
      generalize L.sc.x ^ B = b at *
      generalize unitE p = E at *
      have hE : 0 ≤ E := by linarith
      have ea := mul_le_mul_of_nonneg_left s2 hA.le
      have eb := mul_le_mul_of_nonneg_left s2 hB'.le
      have e1 := mul_nonneg h1 hE
      have e2 := mul_nonneg h2 hE
      have e3 := mul_nonneg hA.le hE
      have e4 := mul_nonneg hB'.le hE
    · nlinarith [mul_nonneg hδ.le hA.le, mul_nonneg hδ.le hB'.le, mul_nonneg hδ.le h1, mul_nonneg hδ.le h2]
    · linarith
    · linarith
    · linarith
  have hE : 0 ≤ unitE p := by linarith
  have := mul_le_mul_of_nonneg_right hs hE
  rw [mul_assoc] at this
  linarith

end GlobalTheory.CovTop.Assembly

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceBlockBound
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameAut

theorem norm_val_of_orderDvd {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n)
    (v : HeightOneSpectrum (𝓞 E)) : ‖((χ.val v : ℂˣ) : ℂ)‖ = 1 := by
  have h1 : (χ.val v) ^ n = 1 := by
    have h2 := congrArg (fun ψ : Formalism.L2.Host.HChar E => ψ.val v) h
    simpa [Formalism.L2.Host.HChar.val, Formalism.L2.Host.HChar.locK, Formalism.L2.Host.HChar.loc] using h2
  have h3 : ((χ.val v : ℂˣ) : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h3 hn.ne'

theorem norm_sq_valTw_half {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (h : χ.IsUnitary)
    (v : HeightOneSpectrum (𝓞 E)) : ‖χ.valTw (1 / 2) v‖ ^ 2 = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  have h1 : ‖((χ.val v : ℂˣ) : ℂ)‖ = 1 := h _
  have hq : 0 < Ideal.absNorm v.asIdeal := Nat.pos_of_ne_zero fun e => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
  have hq' : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by exact_mod_cast hq
  rw [Formalism.L2.Host.HChar.valTw, norm_mul, h1, one_mul, Complex.norm_natCast_cpow_of_pos hq, Complex.neg_re, Complex.ofReal_re,
    ← Real.rpow_natCast, ← Real.rpow_mul hq'.le, ← Real.rpow_neg_one]
  norm_num

theorem norm_sq_firstValA {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam)
    (j : Fin D.R.m) (t : T) (P : Pl0) (hP : P ∈ A.ok t) :
    ‖D.what₂.embLL (Formalism.L2.Col.firstValA (A.muVal j t) A.etaVal A.q A.r P)‖ ^ 2 = (A.q P : ℝ) ^ A.r := by
  obtain ⟨hQ, -, -, h4⟩ := GlobalTheory.GoodPrimes.good_primes R F hL
  have hq := (h4 hF t P hP).2.2
  obtain ⟨gramR, c0R, c0L, hT⟩ := hF.tie
  have hP0 : P ∈ A.ok A.μ0 := by
    obtain ⟨h1, h2, h3⟩ := (hT.ok t P).1 hP
    refine (hT.ok _ P).2 ?_
    rw [hQ, Finset.coe_empty, Set.union_empty]
    exact ⟨h1, fun h => h2 (Or.inl h), fun Q h => h3 Q (Or.inl h)⟩
  have hmu : ‖D.what₂.embLL (A.muVal j t P : D.what₂.LL)‖ = 1 := by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    rw [hF.muVal j t P hP, Formalism.L2.Host.HChar.val_mul, Units.val_mul, norm_mul, norm_val_of_orderDvd _ hn ho, mul_one]
    exact (R.C.isMu0 j).unitary _
  have heta : ‖D.what₂.embLL (A.etaVal P : D.what₂.LL)‖ ^ 2 = (A.q P : ℝ)⁻¹ := by
    rw [hF.etaVal P hP0, hq]
    exact norm_sq_valTw_half _ R.C.isEta.unitary _
  have hq0 : (A.q P : ℝ) ≠ 0 := by
    rw [hq]
    exact_mod_cast fun e => (R.pl P).ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
  obtain ⟨s, hs⟩ : Odd A.r := hT.ranks.2.1 ▸ Formalism.L2.NTheta.odd_r D.R
  have hd : (A.r + 1) / 2 = s + 1 := by omega
  unfold Formalism.L2.Col.firstValA
  rw [hd, hs]
  simp only [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Units.val_inv_eq_inv_val, map_inv₀, norm_inv, hmu, inv_one, one_mul,
    mul_pow, heta, Complex.norm_natCast]
  field_simp
  ring

end GlobalTheory.FrameAut
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffQCartierNumEquivMultipleNonnegSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffQCartierNumEquivMultipleNonnegSmul
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PairStep

theorem mult_nsmul' {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D : CartierDiv X) (n : ℕ) (z : X) :
    (n • D).mult z = n * D.mult z := by
  induction n with
  | zero =>
    have h := CartierDiv.mult_add (0 : CartierDiv X) 0 z
    rw [add_zero] at h
    rw [zero_nsmul]; push_cast; omega
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem eff_nsmul' {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} (h : D.Eff) (n : ℕ) :
    (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

theorem qNum_smul : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (a c : ℚ) (D : X → ℚ), 0 ≤ c → QNum p N a D → QNum p N (c * a) (c • D) := by
  intro X _ _ p hp N a c D hc hD
  letI := algebraΓOfHom p
  obtain ⟨m, D₀, hm, hE, rfl, hI⟩ := hD
  obtain ⟨u, v, hv, rfl⟩ : ∃ u v : ℕ, 0 < v ∧ c = (u : ℚ) / v := by
    refine ⟨c.num.toNat, c.den, c.den_pos, ?_⟩
    have h0 : ((c.num.toNat : ℕ) : ℤ) = c.num := Int.toNat_of_nonneg (Rat.num_nonneg.2 hc)
    have hd : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_pos.ne'
    rw [eq_div_iff hd, Rat.mul_den_eq_num]
    exact_mod_cast h0.symm
  have hv' : (v : ℚ) ≠ 0 := by exact_mod_cast hv.ne'
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨v * m, u • D₀, Nat.mul_pos hv hm, eff_nsmul' hE u, ?_, fun C hC => ?_⟩
  · funext z
    simp only [qWeil, Pi.smul_apply, smul_eq_mul, mult_nsmul']
    push_cast
    field_simp
  · have e := interNumRed_of_cls_eq_nsmul_add ℂ X p hp (toLB (u • D₀)) (toLB D₀) (toLB D₀)
      (isLB_toLB _) (isLB_toLB _) (isLB_toLB _) u 0 C hC
      (by rw [← toPic_apply, ← toPic_apply, map_nsmul, zero_nsmul, add_zero])
    rw [e, Nat.cast_zero, zero_mul, add_zero]
    have h1 := hI C hC
    push_cast
    rw [mul_assoc, ← h1]
    field_simp

end GlobalTheory.PairStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffQCartierNumEquivMultipleNonnegSmulStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.effQCartierNumEquivMultiple_nonneg_smul : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (a c : ℚ) (D : X → ℚ), 0 ≤ c → QNum p N a D → QNum p N (c * a) (c • D) := by
  first | exact @GlobalTheory.PairStep.qNum_smul | exact GlobalTheory.PairStep.qNum_smul | (intros; apply GlobalTheory.PairStep.qNum_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtSmallPlace
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelCharExp

open Formalism.BasicNotions.TH Formalism.IndefR.Lev

theorem pow_of_dvd {G : Type} [Monoid G] {x : G} {n M : ℕ} (h : x ^ n = 1) (hd : n ∣ M) : x ^ M = 1 := by
  obtain ⟨k, rfl⟩ := hd
  rw [pow_mul, h, one_pow]

theorem prod_pow_eq_one {ι G : Type} [CommMonoid G] (s : Finset ι) (f : ι → G) (M : ℕ) (h : ∀ i ∈ s, f i ^ M = 1) :
    (∏ i ∈ s, f i) ^ M = 1 := by
  rw [← Finset.prod_pow]
  exact Finset.prod_eq_one h

theorem residue_char_pow {E : Type} [Field E] [NumberField E] (PP : Formalism.L2.DIV.Pl E) {LL : Type} [Monoid LL]
    (χ : (Formalism.L2.DIV.kP PP)ˣ →* LL) (u : (Formalism.L2.DIV.kP PP)ˣ) : χ u ^ Nat.card (Formalism.L2.DIV.kP PP)ˣ = 1 := by
  rw [← map_pow, pow_card_eq_one', map_one]

theorem card_units_pos {E : Type} [Field E] [NumberField E] (PP : Formalism.L2.DIV.Pl E) : 0 < Nat.card (Formalism.L2.DIV.kP PP)ˣ := by
  have : Finite (Formalism.L2.DIV.kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  exact Nat.card_pos


open Classical in
def expOf {D : D7} {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) : ℕ :=
  ∏ PP ∈ L.Pg ∪ L.Q, Nat.card (Formalism.L2.DIV.kP PP)ˣ

theorem expOf_pos {D : D7} {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) : 0 < expOf L :=
  Finset.prod_pos fun PP _ => card_units_pos PP

open Classical in
theorem levFn_flag1_pow {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (x : GL (Fin V.rank) (Lev.EAf D)) :
    Formalism.L2.DIV.levFn β (flag1L L) x ^ expOf L = 1 := by
  have h1 : Formalism.L2.DIV.ext1 (flag1L L).P.H (flag1L L).P.chi (Formalism.L2.DIV.rTup β (flag1L L) x) = 1 :=
    Formalism.IndefR.Lev.subgroupCharExtension_one_apply _ _
  unfold Formalism.L2.DIV.levFn
  rw [h1, one_mul, mul_pow]
  have hd : ∀ PP ∈ L.Pg ∪ L.Q, Nat.card (Formalism.L2.DIV.kP PP)ˣ ∣ expOf L := fun PP hP =>
    Finset.dvd_prod_of_mem (fun PP => Nat.card (Formalism.L2.DIV.kP PP)ˣ) hP
  rw [prod_pow_eq_one _ _ _ ?_, prod_pow_eq_one _ _ _ ?_, one_mul]
  · intro PP hP
    exact pow_of_dvd (residue_char_pow PP _ _) (hd PP (Finset.mem_union_right _ hP))
  · intro PP hP
    refine prod_pow_eq_one _ _ _ fun c _ => ?_
    exact pow_of_dvd (residue_char_pow PP _ _) (hd PP (Finset.mem_union_left _ hP))

theorem levEnv_chi_pow : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J), (levEnv V β L).χ k ^ expOf L = 1 := by
  intro D V β L k
  exact levFn_flag1_pow V β L _

end GlobalTheory.LevelCharExp

end

namespace GlobalTheory.LevelCharExp

end GlobalTheory.LevelCharExp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisRealBasisOfHolomorphicFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisRealBasisOfHolomorphicFamily
open GlobalTheory.ShFam.Hor.LogCh

set_option autoImplicit false

open Topology

namespace GlobalTheory.LatReal

theorem isRealBasis_of_isLatFam : ∀ (n g r : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ))
    (b₀ : Fin n → ℂ) (lam : Fin r → Fin g → ℂ), IsLatFam B K → b₀ ∈ B → Submodule.span ℝ (K b₀) = ⊤ →
    LinearIndependent ℤ lam → (∀ w, w ∈ K b₀ ↔ ∃ k : Fin r → ℤ, w = ∑ j, k j • lam j) →
    LinearIndependent ℝ lam ∧ Submodule.span ℝ (Set.range lam) = ⊤ := by
  intro n g r B K b₀ lam hF hb hspan hli hK
  have hmemL : ∀ w, w ∈ Submodule.span ℤ (Set.range lam) ↔ w ∈ K b₀ := by
    intro w
    rw [Submodule.mem_span_range_iff_exists_fun, hK]
    constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, hk.symm⟩
  have hsub : K b₀ ⊆ Submodule.span ℝ (Set.range lam) := by
    intro w hw
    obtain ⟨k, rfl⟩ := (hK w).1 hw
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have htop : Submodule.span ℝ (Set.range lam) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    exact Submodule.span_le.2 hsub
  refine ⟨?_, htop⟩
  have h0 : (0 : Fin g → ℂ) ∈ K b₀ := (hK 0).2 ⟨0, by simp⟩
  obtain ⟨ζ, hζ0, -, hev⟩ := hF.2.2.2 b₀ hb 0 h0
  have ht : Filter.Tendsto (fun w : Fin g → ℂ => (b₀, w)) (𝓝 0) (𝓝 (b₀, 0)) :=
    (continuous_const.prodMk continuous_id).tendsto' 0 (b₀, 0) rfl
  have hev' : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), (w ∈ K b₀ ↔ w = 0) := by
    filter_upwards [ht.eventually hev] with w hw
    simpa [hζ0] using hw
  obtain ⟨U, hU, hUo, hU0⟩ := mem_nhds_iff.1 hev'
  set L := Submodule.span ℤ (Set.range lam) with hLdef
  haveI : DiscreteTopology L := by
    apply discreteTopology_of_isOpen_singleton_zero
    rw [isOpen_induced_iff]
    refine ⟨U, hUo, ?_⟩
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      exact Subtype.ext ((hU hx).1 ((hmemL x).1 x.2))
    · rintro rfl
      exact hU0
  have hLset : (L : Set (Fin g → ℂ)) = K b₀ := by
    ext w
    exact hmemL w
  haveI : IsZLattice ℝ L := ⟨by rw [hLset, hspan]⟩
  have hrank := ZLattice.rank ℝ L
  have hcard : Module.finrank ℤ L = r := by
    rw [Module.finrank_eq_card_basis (Module.Basis.span hli)]
    simp
  apply linearIndependent_of_top_le_span_of_card_eq_finrank htop.ge
  rw [Fintype.card_fin]
  omega

end GlobalTheory.LatReal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisRealBasisOfHolomorphicFamilyStatement
open GlobalTheory.ShFam.Hor.LogCh

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeBasis_realBasis_of_holomorphic_family : ∀ (n g r : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (b₀ : Fin n → ℂ) (lam : Fin r → Fin g → ℂ), IsLatFam B K → b₀ ∈ B → Submodule.span ℝ (K b₀) = ⊤ → LinearIndependent ℤ lam → (∀ w, w ∈ K b₀ ↔ ∃ k : Fin r → ℤ, w = ∑ j, k j • lam j) → LinearIndependent ℝ lam ∧ Submodule.span ℝ (Set.range lam) = ⊤ := by
  first | exact @GlobalTheory.LatReal.isRealBasis_of_isLatFam | exact GlobalTheory.LatReal.isRealBasis_of_isLatFam | (intros; apply GlobalTheory.LatReal.isRealBasis_of_isLatFam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaAtSmallPlace
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)

namespace GlobalTheory.FrameOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Int

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {l : ℕ} [Fact l.Prime]

theorem norm_ev_intAf_le {i : E →+* PadicAlgCl l} {ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l} (h : EvOk i ev)
    (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F) (hz : z ∈ Formalism.L2.Herm.intAf F E) :
    ‖ev ((Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm z)‖ ≤ 1 := by
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨_, b, rfl⟩, rfl⟩ | ⟨y, rfl⟩
    · rw [Algebra.TensorProduct.comm_symm_tmul, h.1]
      exact GlobalTheory.AdeleEv.norm_int_le i b
    · rw [Algebra.TensorProduct.comm_symm_tmul]
      exact h.2.1 _ y.2
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | neg x _ hx => rwa [map_neg, map_neg, norm_neg]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

end Int

end GlobalTheory.FrameOf

namespace GlobalTheory.FrameOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pt

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem incOf_mem_range {l : ℕ} [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) (b : Bool) (τ : D.what₂.Tau) (x : D.host.E) :
    incOf D e0 b τ x ∈ Set.range e0 := by
  cases b
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem kapAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : KapAt p j P w := by
  intro _ e0 b ev rk _ hev
  obtain ⟨y, hy⟩ := exists_levInt p j (p.R.mu w)
  refine ⟨fun _ => 1, fun _ => rfl, fun κ τ a c => ?_⟩
  have hk : kapMat p j (p.R.mu w) ev (fun _ => 1) rk κ τ a c = ev τ (matOf j κ.1 (rk a) (rk c)) := by
    simp [kapMat, Matrix.submatrix_apply, Matrix.map_apply]
  rw [hk]
  refine ⟨?_, ?_⟩
  · refine IntermediateField.adjoin.mono _ _ _ ?_ ((hev τ).2.2.2 _)
    rintro _ ⟨x, rfl⟩
    exact incOf_mem_range e0 b τ x
  · have hz : Formalism.IndefR.Lev.swapAE D (matOf j κ.1 (rk a) (rk c)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [← hy κ (rk a) (rk c)]
      exact ((y κ).val (rk a) (rk c)).2
    have h := norm_ev_intAf_le (hev τ) _ hz
    have he : (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm
        (Formalism.IndefR.Lev.swapAE D (matOf j κ.1 (rk a) (rk c))) = matOf j κ.1 (rk a) (rk c) :=
      (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm_apply_apply _
    rwa [he] at h

end Pt

end GlobalTheory.FrameOf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspSectionAnnihilator
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore Filter Topology

namespace GlobalTheory.FlatCore

theorem exists_ringHom_ne_zero_of_not_isNilpotent {K R : Type} [Field K] [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (σ : K →+* ℂ) {b : R} (hb : ¬ IsNilpotent b) :
    ∃ φ : R →+* ℂ, φ.comp (algebraMap K R) = σ ∧ φ b ≠ 0 := by
  haveI hJ : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  have hrad : b ∉ (⊥ : Ideal R).jacobson := by
    rw [← Ideal.radical_eq_jacobson]
    intro h
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.1 h
    exact hb ⟨n, by simpa using hn⟩
  rw [Ideal.jacobson, Submodule.mem_sInf] at hrad
  push_neg at hrad
  obtain ⟨m, ⟨-, hm⟩, hbm⟩ := hrad
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType K (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective _ _)
  haveI : Module.Finite K (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ m)
  haveI : Algebra.IsAlgebraic K (R ⧸ m) := Algebra.IsAlgebraic.of_finite K (R ⧸ m)
  letI : Algebra K ℂ := σ.toAlgebra
  let ψ : (R ⧸ m) →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨ψ.toRingHom.comp (Ideal.Quotient.mk m), ?_, ?_⟩
  · ext a
    show ψ (Ideal.Quotient.mkₐ K m (algebraMap K R a)) = σ a
    rw [AlgHom.commutes, AlgHom.commutes]
    rfl
  · show ψ (Ideal.Quotient.mk m b) ≠ 0
    rw [map_ne_zero_iff ψ ψ.toRingHom.injective]
    exact fun h => hbm (Ideal.Quotient.eq_zero_iff_mem.1 h)

theorem differentiableOn_of_mem_holSub {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {C : Type}
    {X : C → Data E r} {la : ∀ k, Wt (X k).Ψ r} {P : FDSec X} (hP : P ∈ holSub X la) (k : C) :
    DifferentiableOn ℂ (P k) (X k).dom := by
  induction hP using Submodule.span_induction with
  | mem P h => exact (h k).1.1.1
  | zero => exact differentiableOn_const 0
  | add P Q _ _ hP hQ => exact hP.add hQ
  | smul a P _ hP => exact hP.const_smul a

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c}

theorem genVal_ne_zero_of_mem_cuspOn (hf : f ∈ cuspOn U Z G) (hf0 : f ≠ 0) : genVal Z f ≠ 0 := by
  have hG : GenFrEx Xo c := (GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  intro h0
  refine hf0 (secZ_eq_zero_of_genVal (cuspW_le_secZ G (Submodule.mem_inf.1 hf).1) fun Z' => ?_)
  by_cases hZ : Z' = Z
  · rw [hZ]; exact h0
  · rw [genVal_apply hG]; exact evC_eq_zero hG hZ (Submodule.mem_inf.1 hf).2

theorem idem_mul_eq_zero_of_mul_eq_zero (hf : f ∈ cuspOn U Z G) (hf0 : f ≠ 0) {e' : Ix Dw → ℤ} {s : Rul Xo c}
    (hs : s ∈ secZ Xo c e') (hsf : s * f = 0) : idem Z * s = 0 := by
  have hG : GenFrEx Xo c := (GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  have h1 : genVal Z s = 0 := by
    have h2 := congrArg (genVal Z) hsf
    rw [map_mul, map_zero] at h2
    exact (mul_eq_zero.1 h2).resolve_right (genVal_ne_zero_of_mem_cuspOn hf hf0)
  refine secZ_eq_zero_of_genVal (mul_mem_secZ (idem_mem_secZ Z) hs) fun Z' => ?_
  rw [map_mul]
  by_cases hZ : Z' = Z
  · rw [hZ, h1, mul_zero]
  · rw [genVal_apply hG Z' (idem Z), evC_eq_zero hG hZ (idem_mem_suppOn Z), zero_mul]

end GlobalTheory.FlatCore

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupConstantLogBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupConstantLogBound
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.ConstSzRows

theorem supConst_size_rows : ∀ (D : D7) (M : ℕ) (Lb w : ℝ), 1 ≤ M → 1 ≤ Lb → Real.log M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → 1 ≤ w → Real.log w ≤ 25 * Lb → 1 ≤ GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d M w ∧ Real.log (GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d M w) ≤ 4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by
  intro D M Lb w hM hLb hMl hsz hfrl hw hwl
  haveI : IsCMField D.host.E := inferInstance
  have hfd := GlobalTheory.FramedCMPointCompare.fdeg_host D
  have hf0 : 1 ≤ D.R.f := by have : 0 < D.R.n := D.R.ord_pos; unfold Formalism.BasicNotions.Ranks.f; omega
  have hr2 : 2 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Formalism.BasicNotions.Ranks.r; omega
  have hqd := D.host.qd_big
  have hd1 : 1 ≤ D.host.d := by omega
  have hq1 : 1 ≤ D.host.q := by omega
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf0
  have hrR : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 1 ≤ D.R.r)
  have hnR : (Module.finrank ℚ D.host.E : ℝ) = 2 * D.R.f := by exact_mod_cast D.host.finrank_E'
  have hnpos : (0 : ℝ) < Module.finrank ℚ D.host.E := by rw [hnR]; linarith
  have hrd := (GlobalTheory.CovTop.log_rd_le_fieldSz D.host.E).trans hsz
  have hld : Real.log |(discr D.host.E : ℝ)| ≤ 6 * D.R.f * Lb := by
    have h := (div_le_iff₀ hnpos).1 hrd
    rw [hnR] at h; linarith
  set L : ℝ := 25 * Lb / 2 with hL
  have hdE : Real.log (ReciprocityTheory.ChartRestriction.G.FD.dE D.host.E) ≤ 4 * (ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E : ℝ) * L := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.dE; rw [hfd]; nlinarith
  have hdpow : D.host.d ^ D.R.f ≤ (discr D.host.E).natAbs :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.2 (discr_ne_zero _))) (UpperTheory.HF.rad_bounds2 D.host.toHostAx).2.2.1
  have hdpowR : ((D.host.d : ℝ)) ^ D.R.f ≤ |(discr D.host.E : ℝ)| := by
    have : (((discr D.host.E).natAbs : ℕ) : ℝ) = |(discr D.host.E : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [← this]; exact_mod_cast hdpow
  have hdR : (0 : ℝ) < D.host.d := by exact_mod_cast hd1
  have hlogd : Real.log D.host.d ≤ 4 * L := by
    have h1 := Real.log_le_log (by positivity) hdpowR
    rw [Real.log_pow] at h1
    have h3 : (D.R.f : ℝ) * Real.log D.host.d ≤ D.R.f * (6 * Lb) := by linarith
    have h4 := le_of_mul_le_mul_left h3 (by linarith)
    linarith
  have hlogfr : Real.log ((ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E : ℝ) * D.R.r) ≤ L := by
    rw [hfd]; push_cast at hfrl; linarith
  have hmain := GlobalTheory.T.supremum_constant_log_bound D.host.E D.R.r D.host.d M w L hr2 hd1 hM (by linarith) hw hlogfr
    (by linarith) hdE hlogd (by linarith)
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  rw [hfd]
  have hx : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le hfR hrR
  have h1 : ((D.R.f : ℝ) * D.R.r) ^ 2 * Lb ≤ ((D.R.f : ℝ) * D.R.r) ^ 3 * Lb ^ 3 :=
    mul_le_mul (pow_le_pow_right₀ hx (by norm_num)) (le_self_pow₀ hLb (by norm_num)) (by linarith) (by positivity)
  have h2 : (0 : ℝ) ≤ ((D.R.f : ℝ) * D.R.r) ^ 2 * Lb := by positivity
  calc 250 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 2 * L = 3125 * (((D.R.f : ℝ) * D.R.r) ^ 2 * Lb) := by rw [hL]; ring
    _ ≤ 4000 * (((D.R.f : ℝ) * D.R.r) ^ 3 * Lb ^ 3) := by linarith
    _ = 4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by ring

end GlobalTheory.ConstSzRows
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupConstantLogBoundStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sup_constant_log_bound : ∀ (D : D7) (M : ℕ) (Lb w : ℝ), 1 ≤ M → 1 ≤ Lb → Real.log M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → 1 ≤ w → Real.log w ≤ 25 * Lb → 1 ≤ GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d M w ∧ Real.log (GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d M w) ≤ 4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by
  first | exact @GlobalTheory.ConstSzRows.supConst_size_rows | exact GlobalTheory.ConstSzRows.supConst_size_rows | (intros; apply GlobalTheory.ConstSzRows.supConst_size_rows <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceFiniteSet
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameAutCof

theorem sub_mem_of_prime_norm {K : Type} [Field K] [NumberField K] (σ : 𝓞 K →+* 𝓞 K) (I : Ideal (𝓞 K))
    (hp : (Ideal.absNorm I).Prime) (hI : I.map σ ≤ I) (x : 𝓞 K) : σ x - x ∈ I := by
  have hc : Nat.card (𝓞 K ⧸ I) = Ideal.absNorm I := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Fact (Ideal.absNorm I).Prime := ⟨hp⟩
  have : Finite (𝓞 K ⧸ I) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)
  have := Fintype.ofFinite (𝓞 K ⧸ I)
  let e := ZMod.ringEquivOfPrime (𝓞 K ⧸ I) hp (by rw [← Nat.card_eq_fintype_card, hc])
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective (e.symm (Ideal.Quotient.mk I x))
  have h1 : x - (n : 𝓞 K) ∈ I := by
    rw [← Ideal.Quotient.eq, map_intCast]
    apply e.symm.injective
    rw [map_intCast, hn]
  have h2 : σ x - (n : 𝓞 K) ∈ I := by
    have := hI (Ideal.mem_map_of_mem σ h1)
    rwa [map_sub, map_intCast] at this
  have := I.sub_mem h2 h1
  rwa [sub_sub_sub_cancel_right] at this

theorem finite_fixed {K : Type} [Field K] [NumberField K] [StarRing K] (h : ∃ x : K, star x ≠ x) :
    {v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal).Prime ∧ Formalism.DivisionValues.conjPl v = v}.Finite := by
  have hx : ∃ x : 𝓞 K, Formalism.DivisionValues.cO K x - x ≠ 0 := by
    by_contra hn
    push Not at hn
    obtain ⟨y, hy⟩ := h
    apply hy
    have h0 : ∀ a : 𝓞 K, star (a : K) = a := fun a => congrArg (fun z : 𝓞 K => (z : K)) (sub_eq_zero.1 (hn a))
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
    rw [star_div₀]
    exact congrArg₂ (· / ·) (h0 a) (h0 b)
  obtain ⟨x, hx⟩ := hx
  refine (Ideal.finite_factors (I := Ideal.span {Formalism.DivisionValues.cO K x - x}) (by simpa using hx)).subset ?_
  rintro v ⟨hp, hv⟩
  show v.asIdeal ∣ _
  rw [Ideal.dvd_span_singleton]
  exact sub_mem_of_prime_norm (Formalism.DivisionValues.cO K : 𝓞 K →+* 𝓞 K) v.asIdeal hp
    (le_of_eq (congrArg HeightOneSpectrum.asIdeal hv)) x

theorem exists_star_ne (D : D7) : ∃ x : D.host.E, star x ≠ x := by
  by_contra hn
  push Not at hn
  apply IsCMField.complexConj_ne_one D.host.E
  refine AlgEquiv.ext fun x => ?_
  exact hn x

theorem cofinite_labels {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
    (j : Fin D.R.m) (t : p.P.T) {l : ℕ} (hl : l ≠ 0) :
    {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
      ¬ ∃ Q : (GlobalTheory.ExpTie.blk p j t).Pl, ((l : ℕ) : 𝓞 D.host.E) ∉ (plOf p j t Q).asIdeal ∧ labOf p j t Q = v}.Finite := by
  obtain ⟨gR, c0R, c0L, hTie⟩ := p.charW.base.fam.tie
  have honto := p.charW.base.fam.pl_onto
  have hcc : ∀ v : HeightOneSpectrum (𝓞 D.host.E), Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl v) = v := Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl
  have hinj : Function.Injective (Formalism.DivisionValues.conjPl (K := D.host.E)) := Function.Involutive.injective hcc
  set S : Set (HeightOneSpectrum (𝓞 D.host.E)) := (p.R.Sb : Set (Pl D.host.E)) ∪ (p.R.Q t : Set (Pl D.host.E)) with hS
  have hSf : S.Finite := hTie.S_fin.union (Finset.finite_toSet _)
  have hlf : {v : HeightOneSpectrum (𝓞 D.host.E) | v.asIdeal ∣ Ideal.span {((l : ℕ) : 𝓞 D.host.E)}}.Finite :=
    Ideal.finite_factors (by simpa using hl)
  refine (((finite_fixed (exists_star_ne D)).union hSf).union ((hSf.union hlf).preimage hinj.injOn)).subset ?_
  rintro v ⟨hp, hv⟩
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_preimage, not_or, not_and, Ideal.dvd_span_singleton] at hn
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hn
  have hci : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (Formalism.DivisionValues.conjPl v).asIdeal = v.asIdeal := by
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, hcc]
  have hoff : Bridge.SplitOff (D := D) (Formalism.DivisionValues.conjPl v) S := by
    refine ⟨?_, h3, fun Q hQ he => h2 ?_⟩
    · rw [hci]
      exact fun he => h1 hp (HeightOneSpectrum.ext he).symm
    · rw [hci] at he
      exact HeightOneSpectrum.ext he ▸ hQ
  obtain ⟨P, hP⟩ := honto (Formalism.DivisionValues.conjPl v) ⟨hoff.1, fun h => hoff.2.1 (Or.inl h), fun Q hQ => hoff.2.2 Q (Or.inl hQ)⟩
  have hok := (hTie.ok t P).2 (hP ▸ hoff)
  have e1 : plOf p j t ⟨P, hok⟩ = Formalism.DivisionValues.conjPl v := hP
  refine hv ⟨⟨P, hok⟩, ?_, ?_⟩
  · rw [e1]; exact h4
  · show Formalism.DivisionValues.conjPl (plOf p j t ⟨P, hok⟩) = v
    rw [e1, hcc]

end GlobalTheory.FrameAutCof
end

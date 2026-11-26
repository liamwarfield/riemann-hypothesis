module

public import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtDataPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtPf
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 Formalism.BasicNotions Formalism.MainNotions

section Mean

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

theorem htI2et_of_pt (d : Data K ι Ω WT A)
    (hpt : ∀ sg, Real.log (d.supN sg (d.n1 • d.wde) d.et) / d.i ≤ d.Pet) : d.HeightIntegralEstimateTrivialPlace := by
  unfold Data.HeightIntegralEstimateTrivialPlace meanK
  have hN : (0 : ℝ) < (Fintype.card (K →+* ℂ) : ℝ) := by
    first
    | exact_mod_cast Fintype.card_pos
    | (haveI : Nonempty (K →+* ℂ) := ⟨(IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom⟩
       exact_mod_cast Fintype.card_pos)
  rw [div_right_comm, Finset.sum_div, div_le_iff₀ hN]
  calc ∑ sg, (fun sg => Real.log (d.supN sg (d.n1 • d.wde) d.et)) sg / (d.i : ℝ)
      ≤ ∑ _sg : K →+* ℂ, d.Pet := Finset.sum_le_sum (fun sg _ => hpt sg)
    _ = d.Pet * (Fintype.card (K →+* ℂ) : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

end Mean

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def recNrm {σ : c.F →+* ℂ} {rU : ℕ} (U : Unf Xo c σ rU) (xR : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c)
    (k : U.Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ rU) : ℝ :=
  lieFac Dw xR a * (U.X k).pnorm (laU U a n k) (rdU U f k) x

def I2AtFramePoints {rU : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU) (xR : ℝ) {N : ℕ} (wR : Fin (N + 1) → Rul Xo c)
    (uL : WtR E) (th tableLineDegreeFive DF cc : ℝ) : Prop :=
  ∀ σ, GoodEmb c σ → ∀ (k : (U σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ rU), x ∈ ((U σ).X k).dom →
    -Real.log (Real.sqrt (∑ j, recNrm (U σ) xR uL.1 uL.2 (wR j) k x ^ 2)) ≤
      tableLineDegreeFive * DF + cc * ReciprocityTheory.ChartRestriction.G.I2.phiFD ((U σ).X k) th x

def NrmTieU (h : GenFrEx Xo c) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    {rU : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU) (xR : ℝ) {N : ℕ} (wR : Fin (N + 1) → Rul Xo c) (uL : WtR E)
    (etR : Rul Xo c) (uet : WtR E) : Prop :=
  ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ), ∃ σ, GoodEmb c σ ∧ ∃ (k : (U σ).Comp)
    (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ rU), x ∈ ((U σ).X k).dom ∧
    (∀ j, nrmC fn (yP Z) (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z) P = recNrm (U σ) xR uL.1 uL.2 (wR j) k x) ∧
    nrmC fn (yP Z) (wtZ uet.1 uet.2) (valC h uet.1 uet.2 etR Z) P ≤ recNrm (U σ) xR uet.1 uet.2 etR k x

variable [Fintype (Comp Xo c)]

theorem supN_dataOf_nonneg (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ) (sg : c.F →+* ℂ) (G : WTZ E) (x : ∀ Z : Comp Xo c, AC Z) :
    0 ≤ (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).supN sg G x := by
  unfold Data.supN
  apply Real.iSup_nonneg
  intro p
  unfold dataOf nrmC
  dsimp only
  first
  | positivity
  | exact (rfl : (0 : ℕ) = 0)

theorem htI2be_of (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    {rU : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU) (xR th : ℝ)
    (hi : 0 < i) (hcc : 0 ≤ cc) (hfn : FnNe Xo c fn) (het : NZAt h etR)
    (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2)
    (htie : NrmTieU h fn yP U xR wR uL etR uet) (hI2 : I2AtFramePoints U xR wR uL th tableLineDegreeFive DF cc)
    (harch : ∀ σ, GoodEmb c σ → ∀ (k : (U σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ rU),
      x ∈ ((U σ).X k).dom → recNrm (U σ) xR uet.1 uet.2 etR k x ≤
        Real.exp (-(i : ℝ) * (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((U σ).X k) th x - tableLineDegreeTwo))) :
    (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HeightIntegralBoundEstimate := by
  intro Z P
  obtain ⟨σ, hσ, k, x, hx, hw, he⟩ := htie Z P
  have h1 := hI2 σ hσ k x hx
  have h2 := harch σ hσ k x hx
  show -Real.log (Real.sqrt (∑ j, nrmC fn (yP Z) (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z) P ^ 2)) ≤
    tableLineDegreeFive * DF + cc / (i : ℝ) * (-Real.log (nrmC fn (yP Z) ((i * g0) • wtZ ude.1 ude.2) (valC h uet.1 uet.2 etR Z) P)) +
      cc * tableLineDegreeTwo
  have hbe : (∑ j, nrmC fn (yP Z) (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z) P ^ 2) =
      ∑ j, recNrm (U σ) xR uL.1 uL.2 (wR j) k x ^ 2 :=
    Finset.sum_congr rfl fun j _ => by rw [hw j]
  rw [hbe]
  have hm := valC_mem h uet.1 uet.2 etR Z
  rw [huet] at hm
  have hpos : 0 < nrmC fn (yP Z) ((i * g0) • wtZ ude.1 ude.2) (valC h uet.1 uet.2 etR Z) P :=
    nrmC_pos fn (yP Z) hfn P hm (valC_ne_zero (het Z))
  have he' : nrmC fn (yP Z) ((i * g0) • wtZ ude.1 ude.2) (valC h uet.1 uet.2 etR Z) P ≤
      recNrm (U σ) xR uet.1 uet.2 etR k x := by
    rw [← huet]; exact he
  have hlog := Real.log_le_log hpos (he'.trans h2)
  rw [Real.log_exp] at hlog
  set e := Real.log (nrmC fn (yP Z) ((i * g0) • wtZ ude.1 ude.2) (valC h uet.1 uet.2 etR Z) P)
  set φ := ReciprocityTheory.ChartRestriction.G.I2.phiFD ((U σ).X k) th x
  have hi' : (0 : ℝ) < i := Nat.cast_pos.2 hi
  have h3 : φ - tableLineDegreeTwo ≤ -e / i := by
    rw [le_div_iff₀ hi']; nlinarith
  have key : cc * φ ≤ cc / (i : ℝ) * (-e) + cc * tableLineDegreeTwo :=
    calc cc * φ = cc * (φ - tableLineDegreeTwo) + cc * tableLineDegreeTwo := by ring
      _ ≤ cc * (-e / i) + cc * tableLineDegreeTwo := by gcongr
      _ = cc / (i : ℝ) * (-e) + cc * tableLineDegreeTwo := by ring
  linarith

end Gen

section Rec

variable {D : D7} {T : Top D} (hL : LawsP T)

variable (j : ℕ) [IsCMField D.host.E] [Fintype (Comp (T.Q.Xo j) T.Q.c)]

end Rec

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.TieInst
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j}

def wRat (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (k : Fin G.N) :
    ↥(Frac0 (xplus X E hM) la G.w) :=
  ⟨frac (xplus X E hM) la G.w 1 (emb (xplus X E hM) la G.N (X.inc wL (G.w k))),
    Algebra.subset_adjoin (frac_mem_Hfr (xplus X E hM) la G.w (by
      rw [add_zero_weight_one_eq]; exact emb_mem_Vw (xplus X E hM) la G.N wL (G.w k)))⟩

def GenericSectionMinimumIntegral (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) →
    IsReduced (OsK (xplus X E hM) la G.w) → ∀ ζ : PtsG G la, (∀ k, 0 ≤ ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w (wRat G la k))) ∧
    ∃ k, ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w (wRat G la k)) = 0

lemma nval_nonneg_iff {T : CDVR} {e : ℕ} (he : 0 < e) (z : T.Fr) : 0 ≤ nval T.V e z ↔ 0 ≤ nval T.V 1 z := by
  by_cases hz : z = 0
  · simp [hz, nval_zero]
  · rw [nval_of_ne hz, nval_of_ne hz, EReal.coe_nonneg, EReal.coe_nonneg]
    have : (0 : ℝ) < e := by exact_mod_cast he
    constructor
    · intro h; simpa using (div_nonneg_iff.1 h).elim (fun h' => h'.1) (fun h' => absurd h'.2 (not_le.2 this))
    · intro h; exact div_nonneg (by simpa using h) this.le

lemma nval_eq_zero_iff {T : CDVR} {e : ℕ} (he : 0 < e) (z : T.Fr) : nval T.V e z = 0 ↔ nval T.V 1 z = 0 := by
  by_cases hz : z = 0
  · simp [hz, nval_zero]
  · rw [nval_of_ne hz, nval_of_ne hz]
    have : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    simp [div_eq_zero_iff, this]

theorem depthAtSec_of {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (S : Scal B)
    (hspan : SpanW (xplus X E hM) G.w S) (h0 : GenericSectionMinimumIntegral G la)
    (hfd : FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))
    (hred : IsReduced (OsK (xplus X E hM) la G.w)) (y : PtsG G la → E.Pt' la) (hs : ∀ ζ, SecPt ζ (y ζ))
    (ζ : PtsG G la) :
    (xplus X E hM).depth S.sW wL la (.inr (y ζ)) =
      nval (hs ζ).T.V (ep (unifO (xplus X E hM) la G.N) ζ) ((hs ζ).ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0)) := by
  set h := hs ζ with hh
  have hb : h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0) ≠ 0 := h.s0.ne_zero
  have he := h.ep_pos

  have hwk : ∀ k, E.vAt' la (y ζ) (X.inc wL (G.w k)) =
      nval h.T.V (ep (unifO (xplus X E hM) la G.N) ζ) (h.ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (xplus X E hM) la G.w 0)) +
        nval h.T.V (ep (unifO (xplus X E hM) la G.N) ζ) (h.lift (wRat G la k : Lw (xplus X E hM) la G.w)) := by
    intro k
    rw [h.hv, ← nval_mul]
    congr 1
    show _ = _ * h.lift (frac (xplus X E hM) la G.w 1 _)
    rw [h.lift_frac, pow_one, mul_comm, mul_assoc, inv_mul_cancel₀ hb, mul_one]
  have hord : ∀ k, nval h.T.V 1 (h.lift (wRat G la k : Lw (xplus X E hM) la G.w)) =
      toE (ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w (wRat G la k))) :=
    fun k => (h.ord (wRat G la k)).symm
  obtain ⟨hint, k0, hk0⟩ := h0 hfd hred ζ
  have hnn : ∀ k, 0 ≤ nval h.T.V (ep (unifO (xplus X E hM) la G.N) ζ) (h.lift (wRat G la k : Lw _ la G.w)) := by
    intro k
    rw [nval_nonneg_iff he, hord]
    have := hint k
    generalize ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w (wRat G la k)) = o at this ⊢
    cases o with
    | top => simp [toE]
    | coe n => simp only [toE]; exact_mod_cast (WithTop.coe_nonneg.1 this)
  have hz0 : nval h.T.V (ep (unifO (xplus X E hM) la G.N) ζ) (h.lift (wRat G la k0 : Lw _ la G.w)) = 0 := by
    rw [nval_eq_zero_iff he, hord, hk0]
    show toE ((0 : ℤ) : WithTop ℤ) = 0
    simp [toE]
  apply le_antisymm
  · refine (iInf₂_le (G.w k0) (by rw [← hspan]; exact Submodule.subset_span ⟨k0, rfl⟩)).trans_eq ?_
    show E.vAt' la (y ζ) (X.inc wL (G.w k0)) = _
    rw [hwk, hz0, add_zero]
  · refine le_iInf₂ fun F hF => ?_
    rw [← hspan] at hF
    show _ ≤ E.vAt' la (y ζ) (X.inc wL F)
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [hwk]
      exact le_add_of_nonneg_right (hnn k)
    | zero => rw [map_zero, E.vAt'_zero]; exact le_top
    | add x z _ _ hx hz =>
      rw [map_add (f := _)]
      exact (le_min hx hz).trans (E.vAt'_add la _ _ _)
    | smul a x _ hx =>
      by_cases ha : ((a : 𝓞 B.KO) : B.KO) = 0
      · have : a = 0 := by exact_mod_cast ha
        rw [this, zero_smul, map_zero, E.vAt'_zero]; exact le_top
      · rw [← algebraMap_smul B.KO a x, map_smul, E.vAt'_smul la _ _ _ ha]
        exact le_add_of_nonneg_of_le (by exact_mod_cast vAdd_int_nonneg la ha) hx

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CurveComp
section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CurveFr
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j}

lemma weight_add_shift {e k : ℕ} {w' : WeightFamilies.Wt D j} (hw : wadd wF w' = wsmul e wL) :
    wadd (addL wF wL k) w' = addL (wt0 D j) wL (k + e) := by
  have h1 := congrArg WeightFamilies.Wt.aP hw
  have h2 := congrArg WeightFamilies.Wt.aM hw
  have h3 := congrArg WeightFamilies.Wt.n hw
  simp only [wadd, wsmul] at h1 h2 h3
  unfold addL wadd wsmul wt0 wscalar
  simp only [WeightFamilies.Wt.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext τ i
    have := congrFun (congrFun h1 τ) i
    linarith
  · funext τ i
    have := congrFun (congrFun h2 τ) i
    linarith
  · linarith

variable (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (g0 : B.Cusp j wF)

lemma product_cusp_forms_mem_weight {e : ℕ} {w' : WeightFamilies.Wt D j} (θ : B.Cusp j w') (hw : wadd wF w' = wsmul e wL) :
    emb (xplus X E hM) la G.N (X.inc wF g0) * emb (xplus X E hM) la G.N (X.inc w' θ) ∈
      Vw (xplus X E hM) la G.N (addL (wt0 D j) wL e) := by
  have := mul_mem_Vw (xplus X E hM) la G.N (emb_mem_Vw (xplus X E hM) la G.N wF g0)
    (emb_mem_Vw (xplus X E hM) la G.N w' θ)
  have hw' : addL (wt0 D j) wL e = wadd wF w' := by rw [hw]; exact zero_weight_add _
  rw [hw']
  exact this

def u0 {e : ℕ} {w' : WeightFamilies.Wt D j} (θ : B.Cusp j w') (hw : wadd wF w' = wsmul e wL) :
    ↥(Frac0 (xplus X E hM) la G.w) :=
  ⟨frac (xplus X E hM) la G.w e (emb (xplus X E hM) la G.N (X.inc wF g0) * emb (xplus X E hM) la G.N (X.inc w' θ)),
    Algebra.subset_adjoin (frac_mem_Hfr _ _ _ (product_cusp_forms_mem_weight G la g0 θ hw))⟩

lemma top_span_mem {z : ↥(Frac0 (xplus X E hM) la G.w)} (hz : z ∈ Jid (xplus X E hM) la G.w) :
    (⟨z, Algebra.mem_top⟩ : ↥(⊤ : Subalgebra (Kp (xplus X E hM) la G.N) ↥(Frac0 (xplus X E hM) la G.w))) ∈
      Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
        (⟨sfr (xplus X E hM) la G.w i.succ, Algebra.mem_top⟩ :
          ↥(⊤ : Subalgebra (Kp (xplus X E hM) la G.N) ↥(Frac0 (xplus X E hM) la G.w)))) := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Ideal.subset_span ⟨i, rfl⟩
  | zero => exact Ideal.zero_mem _
  | add a b _ _ ha hb => exact Ideal.add_mem _ ha hb
  | smul a b _ hb =>
    have : (⟨a • b, Algebra.mem_top⟩ :
        ↥(⊤ : Subalgebra (Kp (xplus X E hM) la G.N) ↥(Frac0 (xplus X E hM) la G.w))) =
        ⟨a, Algebra.mem_top⟩ * ⟨b, Algebra.mem_top⟩ := rfl
    rw [this]
    exact Ideal.mul_mem_left _ _ hb

theorem curveModel_of_fr
    (hfd : FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))
    (hred : IsReduced (OsK (xplus X E hM) la G.w))
    {e : ℕ} {w' : WeightFamilies.Wt D j} (θ : B.Cusp j w') (hw : wadd wF w' = wsmul e wL)
    (hu0 : IsUnit (toOsK (xplus X E hM) la G.w (u0 G la g0 θ hw)))
    (hinj : ∀ b : ↥(Frac0 (xplus X E hM) la G.w),
      (b : Lw (xplus X E hM) la G.w) *
        algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) (emb (xplus X E hM) la G.N (X.inc wF g0)) = 0 →
        b = 0) :
    Nonempty (CurveModel G la g0) := by
  obtain ⟨v, hv⟩ := hu0
  obtain ⟨c, hc⟩ := toOsK_surjective (xplus X E hM) la G.w (↑v⁻¹)
  set A : Subalgebra (Kp (xplus X E hM) la G.N) ↥(Frac0 (xplus X E hM) la G.w) := ⊤ with hA
  have hJh : c * u0 G la g0 θ hw - 1 ∈ Jid (xplus X E hM) la G.w := by
    rw [← toOsK_eq_zero_iff, map_sub, map_mul, map_one, hc, ← hv, Units.inv_mul, sub_self]

  have hspan : Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      (⟨sfr (xplus X E hM) la G.w i.succ, Algebra.mem_top⟩ : ↥A)) =
      (Jid (xplus X E hM) la G.w).map (Subalgebra.topEquiv (R := Kp (xplus X E hM) la G.N)).symm := by
    rw [Jid, Ideal.map_span, ← Set.range_comp]
    rfl
  let qe := Ideal.quotientEquivAlg (R₁ := Kp (xplus X E hM) la G.N) (Jid (xplus X E hM) la G.w) _
    (Subalgebra.topEquiv (R := Kp (xplus X E hM) la G.N) (A := ↥(Frac0 (xplus X E hM) la G.w))).symm hspan
  have hfd' : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥(Frac0 (xplus X E hM) la G.w) ⧸ Jid (xplus X E hM) la G.w) :=
    hfd
  have hred' : IsReduced (↥(Frac0 (xplus X E hM) la G.w) ⧸ Jid (xplus X E hM) la G.w) := hred
  refine ⟨{ A' := A
            sA := fun _ => Algebra.mem_top
            h := ⟨c * u0 G la g0 θ hw, Algebra.mem_top⟩
            h_one := ?_
            fin := ?_
            red := ?_
            loc := fun b => ⟨0, ⟨b, Algebra.mem_top⟩, by rw [pow_zero, one_mul]⟩
            base_form_injective := ?_
            base_form_local := ?_ }⟩
  · have := top_span_mem G la hJh
    convert this using 1
  · exact LinearEquiv.finiteDimensional qe.toLinearEquiv
  · exact isReduced_of_injective qe.symm.toRingEquiv.toRingHom qe.symm.injective
  · intro a₁ a₂ h12
    apply Subtype.ext
    have h0 : (((a₁ : ↥(Frac0 (xplus X E hM) la G.w)) - (a₂ : ↥(Frac0 (xplus X E hM) la G.w)) :
        ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) *
        algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w)
          (emb (xplus X E hM) la G.N (X.inc wF g0)) = 0 := by
      rw [Subalgebra.coe_sub, sub_mul, sub_eq_zero]
      exact h12
    exact sub_eq_zero.1 (hinj _ h0)
  · intro x
    obtain ⟨k, g, hg, hx⟩ := (mem_Hfr (xplus X E hM) la G.w).1 ((mem_HK (xplus X E hM) la G.w).1 x.2)
    have hgθ : g * emb (xplus X E hM) la G.N (X.inc w' θ) ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL (k + e)) := by
      rw [← weight_add_shift (k := k) hw]
      exact mul_mem_Vw _ _ _ hg (emb_mem_Vw _ _ _ w' θ)
    let b : ↥(Frac0 (xplus X E hM) la G.w) :=
      ⟨frac (xplus X E hM) la G.w (k + e) (g * emb (xplus X E hM) la G.N (X.inc w' θ)),
        Algebra.subset_adjoin (frac_mem_Hfr _ _ _ hgθ)⟩
    refine ⟨1, ⟨c * b, Algebra.mem_top⟩, ?_⟩
    show ((c * u0 G la g0 θ hw : ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) ^ 1 *
        (x : Lw (xplus X E hM) la G.w) =
      ((c * b : ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) *
        algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) (emb (xplus X E hM) la G.N (X.inc wF g0))
    rw [pow_one, Subalgebra.coe_mul, Subalgebra.coe_mul, hx, ← frac_zero, mul_assoc, mul_assoc]
    congr 1
    show frac _ _ _ e _ * frac _ _ _ k g = frac _ _ _ (k + e) _ * frac _ _ _ 0 _
    rw [frac_mul, frac_mul, add_zero, add_comm e k]
    congr 1
    ring

end Formalism.L2.Pj
end
end

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def evCAlg (hG : GenFrEx Xo c) (hT : GenFromTest Xo c hG) (Z : Comp Xo c) : Rul Xo c →ₐ[c.F] Om Z where
  toFun := evC hG Z
  map_one' := evalAt_one _ _ (genFr hG Z) (hT Z)
  map_mul' f g := evalAt_mul _ _ f g (genFr hG Z)
  map_zero' := evalAt_zero _ _ (genFr hG Z)
  map_add' f g := evalAt_add _ _ f g (genFr hG Z)
  commutes' a := by
    show evC hG Z (algebraMap c.F (Rul Xo c) a) = algebraMap c.F (Om Z) a
    rw [Algebra.algebraMap_eq_smul_one]
    show evalAt _ _ (a • (1 : Rul Xo c)) (genFr hG Z) = _
    rw [evalAt_smul, evalAt_one _ _ _ (hT Z), mul_one]

lemma evCAlg_apply (hG : GenFrEx Xo c) (hT : GenFromTest Xo c hG) (Z : Comp Xo c) (f : Rul Xo c) :
    evCAlg hG hT Z f = evC hG Z f := rfl

end Gen

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) (Ω : Type) [CommRing Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)

abbrev RZ : Type := Kp X la N ⊗[X.Kl la] (X.Kl la ⊗[B.KO] Ω)

def rzMap : Rp X la N →ₐ[Kp X la N] RZ X la N Ω :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (Algebra.TensorProduct.map (AlgHom.id _ _) gF)

lemma rzMap_emb (F : X.Forms) :
    rzMap X la N Ω gF (emb X la N F) = (1 : Kp X la N) ⊗ₜ ((1 : X.Kl la) ⊗ₜ gF F) := by
  show Algebra.TensorProduct.map (AlgHom.id _ _) (Algebra.TensorProduct.map (AlgHom.id _ _) gF)
      ((1 : Kp X la N) ⊗ₜ[X.Kl la] ((1 : X.Kl la) ⊗ₜ[B.KO] F)) = _
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
  rfl

variable {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

abbrev RZs : Type := Localization.Away (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))

def lwZ : Lw X la w →+* RZs X la N Ω gF w :=
  Localization.awayMap (rzMap X la N Ω gF).toRingHom (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)

lemma lwZ_alg (r : Rp X la N) :
    lwZ X la N Ω gF w (algebraMap (Rp X la N) (Lw X la w) r) =
      algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF r) := by
  show (Localization.awayMap (rzMap X la N Ω gF).toRingHom (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))
      (algebraMap (Rp X la N) (Localization.Away (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)) r) = _
  exact IsLocalization.map_eq _ _

def phiZ : ↥(Frac0 X la w) →ₐ[Kp X la N] RZs X la N Ω gF w where
  toRingHom := (lwZ X la N Ω gF w).comp (Frac0 X la w).val.toRingHom
  commutes' k := by
    show lwZ X la N Ω gF w (algebraMap (Kp X la N) (Lw X la w) k) = _
    rw [IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w), lwZ_alg, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]

lemma phiZ_apply (x : ↥(Frac0 X la w)) : phiZ X la N Ω gF w x = lwZ X la N Ω gF w (x : Lw X la w) := rfl

end Rec

section Inst

variable {D : D7} {T : Top D} (j : ℕ)
  (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) (Z : Comp (T.Q.Xo j) T.Q.c)

def formsEvR : AddMonoidAlgebra (T.R j) (Deg D j) →ₐ[T.Q.c.F] Om Z :=
  AddMonoidAlgebra.liftNCAlgHom (evCAlg hG hT Z) 1 (fun _ _ => Commute.all _ _)

lemma formsEvR_single (d : Deg D j) (f : T.R j) :
    formsEvR j hG hT Z (AddMonoidAlgebra.single d f) = evC hG Z f := by
  show AddMonoidAlgebra.liftNC (evCAlg hG hT Z).toRingHom.toAddMonoidHom
      ((1 : Multiplicative (Deg D j) →* Om Z) : Multiplicative (Deg D j) → Om Z) (AddMonoidAlgebra.single d f) = _
  rw [AddMonoidAlgebra.liftNC_single]
  simp [evCAlg_apply]

end Inst

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.FibreUniformisationLevelTwo
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section PerFr

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem perFr_add {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : Frame X.Ψ r) (v w : Fin r → E) (τ : E →+* ℂ)
    (i : ℕ) : perFr X x (v + w) τ i = perFr X x v τ i + perFr X x w τ i := by
  have he : ∀ σ : E →+* ℂ, Data.emb σ (v + w) = Data.emb σ v + Data.emb σ w := by
    intro σ
    first
      | (funext k; simp [Data.emb]; done)
      | (simp [Data.emb]; done)
      | exact map_add _ _ _
  unfold perFr
  simp only [he]
  split_ifs <;> first
    | (simp; done)
    | (simp [Matrix.mulVec_add]; done)
    | (simp [hermC, Matrix.dotProduct_add, Matrix.mulVec_add, mul_add, add_mul, Finset.sum_add_distrib]; done)
    | (unfold hermC; simp [Matrix.dotProduct_add, Matrix.mulVec_add, mul_add, add_mul, Finset.sum_add_distrib]; done)
    | (unfold hermC; simp [mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)])

theorem perFr_zero {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : Frame X.Ψ r) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x 0 τ i = 0 := by
  have he : ∀ σ : E →+* ℂ, Data.emb σ (0 : Fin r → E) = 0 := by
    intro σ
    first
      | (funext k; simp [Data.emb]; done)
      | (simp [Data.emb]; done)
      | exact map_zero _
  unfold perFr
  simp only [he]
  split_ifs <;> first
    | (simp; done)
    | (simp [hermC]; done)
    | (unfold hermC; simp)

end PerFr

section Lin

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

def eb {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) : Fin g → ℂ :=
  Pi.single (e.symm ⟨τ, i⟩) 1

theorem eb_apply {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (τ : E →+* ℂ) (i : Fin (Dw.mult τ))
    (q : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : eb e τ i (e.symm q) = if q = ⟨τ, i⟩ then 1 else 0 := by
  by_cases hq : q = ⟨τ, i⟩
  · subst hq
    simp [eb]
  · simp [eb, hq, Pi.single_apply, e.symm.injective.eq_iff]

theorem sum_eb_apply {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (τ : E →+* ℂ)
    (c : Fin (Dw.mult τ) → ℂ) (l : Fin (Dw.mult τ)) : (∑ j, c j • eb e τ j) (e.symm ⟨τ, l⟩) = c l := by
  simp [Finset.sum_apply, eb_apply]

end Lin

section Der

theorem isDerivAt0_comp {g : ℕ} {X : Scheme.{0}} {e1 e2 : (Fin g → ℂ) → (Sp ℂ ⟶ X)}
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (he : ∀ z, e2 (h z) = e1 z) {w : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ X} (hv : IsDerivAt0 e1 w v) : IsDerivAt0 e2 (h w) v := by
  unfold IsDerivAt0 at hv ⊢
  obtain ⟨h1, h2⟩ := hv
  have h0 : h 0 = 0 := map_zero h
  have h3 : e2 0 = e1 0 := by simpa [h0] using he 0
  refine ⟨h1.trans h3.symm, ?_⟩
  intro U hU f
  refine (h2 U hU f).trans ?_
  have hfun : (fun z => valAt' (e1 z) U f) =
      (fun y => valAt' (e2 y) U f) ∘ (LinearEquiv.toContinuousLinearEquiv h) := by
    funext z
    simp [he]
  rw [hfun, ContinuousLinearEquiv.comp_right_fderiv]
  simp [h0]

end Der

section Fam

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def pmOf {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    (M : ModelsOf F r) (k : Fin F.n) (x : Frame (M.X k).Ψ r) : (F.Di k).La →+ (Fin g → ℂ) where
  toFun a := fun j => perFr (M.X k) x (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2
  map_zero' := by
    funext j
    simp [perFr_zero]
  map_add' a b := by
    funext j
    simp [perFr_add]

def ExpUniq {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) : Prop :=
  ∀ i (P P' : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P' →
    ∀ (gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (F.Di i).EF (gam a) (gam b) = (F.Di i).EF a b) →
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di i).La), ∃ b, gam a = a + l.M • b) →
      (∀ a, ∃ b, gam a = a + l.A • b) → (∀ a, P' (gam a) = h (P a)) →
      ∀ z, (F.ex i P' (h z)).left = (F.ex i P z).left

def ExpLin {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) : Prop :=
  ∀ i (P : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    ∀ (m : ℕ) (w : Fin m → (Fin g → ℂ)) (vs : Fin m → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left))
      (cf : Fin m → ℂ) (v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left),
      (∀ j, IsDerivAt0 (fun z => (F.ex i P z).left) (w j) (vs j)) →
      IsDerivAt0 (fun z => (F.ex i P z).left) (∑ j, cf j • w j) v → IsCombAt (F.u i P) vs cf v

def ExpTan {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) : Prop :=
  ∀ i (P : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    ∀ (w : Fin g → ℂ) (v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left),
      IsDerivAt0 (fun z => (F.ex i P z).left) w v →
      IsTanAt (F.u i P) v ∧ ∀ j, w = Pi.single j 1 → IsEigAt c (e j).1 v

variable {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}

theorem derivAt_exists {i : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P) (w : Fin g → ℂ) :
    ∃ v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left, IsDerivAt0 (fun z => (F.ex i P z).left) w v := by
  obtain ⟨v, hv, -⟩ := (F.ex_diff i P hP).1 w
  exact ⟨_, hv⟩

end Fam

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Main

section Rows

variable {D : D7}

end Rows

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.EtArchPf
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Torus

open ReciprocityTheory.ChartRestriction.G.I2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def thRat (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ) (a : Fin X.r → Vsp X.dim) : ℝ :=
  ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a j) / Real.sqrt (X.l2 1 s)






end Torus

variable {D : D7} {T : Top D} (h : LawsP T)

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.PtOfSInst
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {T : Top D}

def PtOfSSt (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) : Prop :=
  0 < wL.n → ∀ (L : Type) [Field L] [Algebra (Kp (recPlus h j hj) la G.N) L]
    (φ : OsK (recPlus h j hj) la G.w →ₐ[Kp (recPlus h j hj) la G.N] L),
    ∃ (alg : T.Q.c.F →+* L) (y : letI := alg.toAlgebra; FrPt (T.Q.Xo j) T.Q.c L),
      (letI := alg.toAlgebra; ∃ (Z : Comp (T.Q.Xo j) T.Q.c) (ψ : Om Z →ₐ[T.Q.c.F] L), FrMap ψ (genFr hG Z) y) ∧
      (∀ a : T.Q.c.F, alg a = algebraMap (Kp (recPlus h j hj) la G.N) L
        (@algebraMap ((recPlus h j hj).Kl la) (Kp (recPlus h j hj) la G.N) _ _ (Kp.algKl (recPlus h j hj) la G.N)
          (algebraMap T.Q.c.F ((recPlus h j hj).Kl la) a))) ∧
      letI := alg.toAlgebra
      (∑ k, algebraMap (Kp (recPlus h j hj) la G.N) L
          (@algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) _ _ _ (Tv (recPlus h j hj) la G.N (0, k))) *
          evR (T.Q.Xo j) T.Q.c ((G.w k : T.R j)) y) ≠ 0 ∧
      ∀ (k : ℕ) (g : (recB h.toLawsCore).Cusp j (addL (wt0 D j) wL k)),
        φ (toOsK (recPlus h j hj) la G.w (fr0 (recPlus h j hj) la G.w k
          ⟨emb (recPlus h j hj) la G.N ((recPlus h j hj).inc _ g), emb_mem_Vw (recPlus h j hj) la G.N _ g⟩)) =
        evR (T.Q.Xo j) T.Q.c ((g : T.R j)) y /
          (∑ k', algebraMap (Kp (recPlus h j hj) la G.N) L
            (@algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) _ _ _ (Tv (recPlus h j hj) la G.N (0, k'))) *
            evR (T.Q.Xo j) T.Q.c ((G.w k' : T.R j)) y) ^ k

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.AdelicContinuousOfUniform
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section BC

theorem bcSp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def bcPm {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) : Gx (spMap ψ ≫ x) ⟶ Gx x :=
  pullback.lift (pullback.fst (Over.mk (spMap ψ ≫ x)).hom Xo.univ.t.G.hom ≫ spMap ψ)
    (pullback.snd (Over.mk (spMap ψ ≫ x)).hom Xo.univ.t.G.hom)
    (by rw [Category.assoc]; exact pullback.condition)

theorem bcPm_snd {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    bcPm ψ x ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
  rw [Over.snd_left, Over.snd_left]
  exact pullback.lift_snd _ _ _

theorem bcPm_fst {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    bcPm ψ x ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left ≫ spMap ψ := by
  rw [Over.fst_left, Over.fst_left]
  exact pullback.lift_fst _ _ _

theorem bcOver {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    {x : Sp S ⟶ Xo.X} (h : x ≫ Xo.s = sOf c S) : (spMap ψ.toRingHom ≫ x) ≫ Xo.s = sOf c T := by
  rw [Category.assoc, h]
  unfold sOf
  rw [bcSp]
  congr 1
  ext a
  simp



end BC

section Loc

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

end Loc

end Formalism.L2.Pj
end
end

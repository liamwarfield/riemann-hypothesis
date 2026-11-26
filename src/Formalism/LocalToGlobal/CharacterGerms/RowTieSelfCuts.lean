module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieLab
public import Formalism.LocalToGlobal.CharacterGerms.RankMaximalOfNondegenerate
public import Formalism.LocalToGlobal.CharacterGerms.ChartHypothesisOfCharacters
public import Formalism.LocalToGlobal.CharacterGerms.UncurryLogConstantCoeff
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePIndAr

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieSelfCuts
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

section Core

variable {Orb : Type} {d : ℕ} [NeZero d]

structure LabSGeoCore (C3 : IntChart T io y) (ι : T.Fr →+* C) (Y : FBChart C V (𝓞 E) (chD C3.ch))
    (lab : LabS E C Orb d) : Prop where
  e_eig : ∀ o (x : lab.II Dw o) a, linAct (Y.B.A.act a) (selfLieBasisVector C3 ι lab o x) =
    emA3 io ι (lab.tau o x.1) a • selfLieBasisVector C3 ι lab o x
  e_sat : ∀ o, ∃ w : Fin (chD C3.ch) → lab.II Dw o → C, (∀ x q, V.Ge 0 (w x q)) ∧
    ∀ q q' : lab.II Dw o, ∑ x, selfLieBasisVector C3 ι lab o q x * w x q' = if q = q' then 1 else 0
  e_full : ∀ o a (v : Fin (chD C3.ch) → C), (∀ x, linAct (Y.B.A.act x) v = emA3 io ι (lab.tau o a) x • v) →
    ∃ b : lab.II Dw o → C, (∀ q, q.1 ≠ a → b q = 0) ∧ v = ∑ q, b q • selfLieBasisVector C3 ι lab o q

theorem labSGeo_of (hstar : ∀ a : 𝓞 E, star a = H.bar a) {C3 : IntChart T io y} {ι : T.Fr →+* C} (hι : EmbOK T V ι)
    {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb d} (ha : LabSArith V io ι lab)
    (h : LabSGeoCore C3 ι Y lab) : LabSGeo C3 ι Y lab := by
  refine {
    em_int := fun _ _ x => embedding_integral ι _ x
    em_conj := ?_
    e_int := fun _ _ i => a3uvec_int C3 hι _ i
    e_eig := h.e_eig
    e_sat := h.e_sat
    e_full := h.e_full }
  intro o a x
  rw [← ha.conj o a]
  exact (embedding_conjugate hstar ι _ x).symm

end Core

def RankMaximalSelfOfNondegenerate : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0),
    NDG Y → (Y.rawSelf p).RankHyp → ∀ Hc : ∀ g, (Y.rawSelf p).CartHyp V g, RawChart.RankMaximalCondition Hc

variable (Xo c)

theorem rank_maximal_self_charts_of_nondegenerate (h1 : RankMaximalSelfOfNondegenerate) (h2 : NondegenerateCharts Xo c) : RankMaximalSelfCharts Xo c :=
  fun hstar T io y C3 C _ _ V ι hι k Y hY _ d _ lab ha hg hr o Hc => by
    have hrank : (Y.rawSelf (selfOfLab ha hg o)).RankHyp := by
      refine { big_compl := (hr o).1, rk_big := ?_, rk_small := ?_ }
      · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
        · intro a hb
          simp only [FBChart.rawSelf, selfOfLab]
          convert (card_sigma_fst (fun b => Dw.mult (lab.tau o b)) a).trans ((hr o).2.1 a hb) using 2
          exact Finset.filter_congr (fun _ _ => Iff.rfl)
        · intro a hb
          simp only [FBChart.rawSelf, selfOfLab, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
          exact (card_sigma_shift (fun b => Dw.mult (lab.tau o b)) lab.hd a).trans ((hr o).2.2.2.1 a hb)
      · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
        · intro a hb
          simp only [FBChart.rawSelf, selfOfLab]
          convert (card_sigma_fst (fun b => Dw.mult (lab.tau o b)) a).trans ((hr o).2.2.1 a hb) using 2
          exact Finset.filter_congr (fun _ _ => Iff.rfl)
        · intro a hb
          simp only [FBChart.rawSelf, selfOfLab, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
          exact (card_sigma_shift (fun b => Dw.mult (lab.tau o b)) lab.hd a).trans ((hr o).2.2.2.2 a hb)
    exact h1 C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) (h2 hstar T io y C3 C V ι hι k Y hY) hrank Hc

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.FirstStepSecondHalfCondition
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Defs

variable {C : Type} [Field C]

def frobTw {σ : Type} (l : ℕ) (c : MvPowerSeries σ C) : MvPowerSeries σ C :=
  fun μ => if ∀ s, l ∣ μ s then (MvPowerSeries.coeff (μ.mapRange (fun n => n / l) (Nat.zero_div l)) c) ^ l else 0

def cobd {dd : ℕ} (F : Fin dd → PS C 2 dd) (b : PS C 1 dd) : PS C 2 dd :=
  ev (n := 2) ![addOf F (pt C dd 0) (pt C dd 1)] b - ev (n := 2) ![pt C dd 0] b - ev (n := 2) ![pt C dd 1] b

end Defs

def FirstStepFirstHalfCondition : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I),
    (Y.raw p).RankHyp → ∀ Hc : ∀ g, (Y.raw p).CartHyp V g, (Y.raw p).AltC →
    ∀ (g : Fin 2) (a : ZMod d), (Y.raw p).big g a →
    ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (Hc g)).Good a w x →
    (∀ q, V.MM ((RawChart.cart (Hc g)).c0' x q)) →
    ∀ (γ : Fin dd → PowerSeries C) (lam : JJ I g → PowerSeries C), (Y.raw p).TyWit V g x γ lam →
      ∃ A : PS C 1 dd, IntS V A ∧
        (∀ j : Fin dd, V.MM (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) A)) ∧
        ∀ μ, V.MM (MvPowerSeries.coeff μ
          (cobd Y.B.G.F A - frobTw V.l (Y.chartLinearTerm (fun i => PowerSeries.coeff 1 (γ i)))))

def FirstStepSecondHalfCondition : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C), IsAlgClosed C →
    ∀ (dd : ℕ) (G : FGLaw C dd), (∀ i, IntS V (G.F i)) →
    ∀ (A : PS C 1 dd) (c : PS C 2 dd), IntS V A → IntS V c →
      (∀ j : Fin dd, V.MM (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) A)) →
      (∀ μ, V.MM (MvPowerSeries.coeff μ (cobd G.F A - frobTw V.l c))) →
      ∃ b : PS C 1 dd, IntS V b ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ (c - cobd G.F b))

theorem intS_c2lin {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) (u : Fin dd → C) (hu : ∀ i, V.Ge 0 (u i)) : IntS V (Y.chartLinearTerm u) := by
  intro μ
  show V.Ge 0 (∑ i, u i * MvPowerSeries.coeff
    (μ.mapDomain (fun p : Fin 2 × Fin dd => (p.1.succ, p.2)) + Finsupp.single ((0 : Fin 3), i) 1) Y.B.ph2)
  exact VF.Ge.sum fun i _ => by simpa using (hu i).mul (Y.intPh2 _)

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieCharS
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I0 : Type} [Fintype I0]

def SelfData.yOf {Y : FBChart C V O dd} (p : SelfData Y d I0) (g : Fin 2) (χ : Fin 2 → PS C 1 dd) (x : I0) : C :=
  ∑ col, ∑ i, dlogC (χ col) i * (Y.rawSelf p).u g x (col, i)

def CharGermSelfSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0)
    (Hc : ∀ g, (Y.rawSelf p).CartHyp V g) (χ : Fin 2 → PS C 1 dd), (∀ col, Y.IsChar (χ col)) →
    ∀ (g : Fin 2) (S : ∀ g, Sys (RawChart.cart (Hc g))) (t : ∀ _ : Fin 2, I0 → MvPowerSeries I0 C),
      (∀ g, (S g).IsT (t g)) →
      upG (I := fun _ => I0) g (mvExp (∑ x : I0, p.yOf g χ x • (MvPowerSeries.X x : MvPowerSeries I0 C))) ∈ IntGerm V t

namespace ChG

open VP

theorem subst_linU_linF {ι : Type} [Fintype ι] (U : ι → Fin dd → C) (y : Fin dd → C) :
    MvPowerSeries.subst (fun i => ∑ c, U c i • (MvPowerSeries.X c : MvPowerSeries ι C)) (linF y) =
      ∑ x : ι, (∑ i, y i * U x i) • (MvPowerSeries.X x : MvPowerSeries ι C) := by
  have ha : MvPowerSeries.HasSubst (fun i => ∑ c, U c i • (MvPowerSeries.X c : MvPowerSeries ι C)) :=
    VP.hs (fun i => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero])
  set_option synthInstance.maxHeartbeats 100000 in
    rw [linF, ← MvPowerSeries.coe_substAlgHom ha, map_sum]
  simp only [map_smul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X ha]
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem cc_linU {ι κ : Type} [Fintype ι] (U : ι → κ → C) (i : κ) :
    MvPowerSeries.constantCoeff (∑ c, U c i • (MvPowerSeries.X c : MvPowerSeries ι C)) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero]

end ChG

theorem SelfData.yOf_int {Y : FBChart C V O dd} (p : SelfData Y d I0) (g : Fin 2) {χ : Fin 2 → PS C 1 dd}
    (h : ∀ col, Y.IsChar (χ col)) (x : I0) : V.Ge 0 (p.yOf g χ x) := by
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → C), (∀ i ∈ s, V.Ge 0 (f i)) → V.Ge 0 (∑ i ∈ s, f i) :=
    fun s f hf => Finset.sum_induction f (fun z => V.Ge 0 z) (fun _ _ ha hb => VF.Ge.add ha hb)
      (VF.Ge.zero 0) hf
  have hgm : ∀ a r s, V.Ge 0 (p.gm a r s) := by
    intro a r s
    obtain ⟨M, hM⟩ := p.gm_lim 0
    have h1 : V.Ge 0 (p.gm a r s - p.em a (M r s)) := by simpa using hM a r s
    have h2 := VF.Ge.add h1 (p.em_int a (M r s))
    simpa using h2
  unfold SelfData.yOf
  refine hsum _ _ fun col _ => hsum _ _ fun i _ => ?_
  refine VF.Ge.mul_int ((h col).1 _) ?_
  exact VF.Ge.mul_int (hgm _ _ _) (p.e_int _ _)

open ChG VP in
theorem charGermSelf_holds : CharGermSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p Hc χ hχ g S t ht
  obtain ⟨P, hP0, hPI, -, hPt⟩ := GeneralGermZero.sysK_P (Y.rawSelf p) (SelfConjugateGermZero.lawS Y) (SelfConjugateGermZero.lawS_const Y) (SelfConjugateGermZero.lawS_int Y)
    (SelfConjugateGermZero.lgS_add Y p) (SelfConjugateGermZero.lgS_lin Y p) (SelfConjugateGermZero.exS_lg Y p) (Hc g) (S g)
  have ht0 : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0 := fun g c => (ht g).1 c
  set U : I0 → Fin 2 × Fin dd → C := fun c' i => (Y.rawSelf p).u g c' i with hU
  set γ0 : MvPowerSeries I0 C := ∏ col : Fin 2, MvPowerSeries.subst (fun i => P (col, i)) (un1 (χ col)) with hγ0
  have hI : IntS V γ0 := IntS_prod _ fun col _ =>
    IntS.subst (fun i => hP0 (col, i)) (fun i => hPI (col, i)) (integralSeries_uncurry_one (hχ col).1)
  have hcol : ∀ col : Fin 2, MvPowerSeries.subst (t g) (MvPowerSeries.subst (fun i => P (col, i)) (un1 (χ col))) =
      mvExp (∑ x : I0, (∑ i, dlogC (χ col) i * U x (col, i)) • (MvPowerSeries.X x : MvPowerSeries I0 C)) := by
    intro col
    rw [subst_subst (fun i => hP0 (col, i)) (ht0 g)]
    have h1 : (fun i => MvPowerSeries.subst (t g) (P (col, i))) = fun i =>
        MvPowerSeries.subst (fun k : Fin dd => ∑ c', U c' (col, k) • (MvPowerSeries.X c' : MvPowerSeries I0 C)) (e Y i) := by
      funext i
      rw [hPt (t g) (ht g) (col, i)]
      show MvPowerSeries.subst (fun k : Fin 2 × Fin dd => ∑ c', U c' k • (MvPowerSeries.X c' : MvPowerSeries I0 C))
        (MvPowerSeries.subst (fun x : Fin dd => (MvPowerSeries.X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C))
          (un1 (Y.ex i))) = _
      rw [subst_subst (fun _ => cc_X _) (cc_linU U)]
      congr 1
      funext k
      rw [subst_X (cc_linU U)]
    rw [h1, ← subst_subst (cc_e Y) (fun k => cc_linU U (col, k))]
    show MvPowerSeries.subst _ (Psi Y (χ col)) = _
    rw [chi_exp Y (hχ col), subst_exp (fun k => cc_linU U (col, k)) (constantCoeff_linF _),
      subst_linU_linF (fun c' k => U c' (col, k))]
  have key : MvPowerSeries.subst (t g) γ0 =
      mvExp (∑ x : I0, p.yOf g χ x • (MvPowerSeries.X x : MvPowerSeries I0 C)) := by
    rw [hγ0, subst_prod (ht0 g), Finset.prod_congr rfl fun col _ => hcol col,
      ← Formalism.UnitaryBoundIntegral.ubint_mvExp_sum Finset.univ _ (fun col _ => cc_linU (fun x (_ : Unit) => ∑ i, dlogC (χ col) i * U x (col, i)) ()),
      Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_smul]
    rfl
  refine ⟨upG (I := fun _ => I0) g γ0, ?_, ?_⟩
  · exact IntS.subst (fun _ => cc_X _) (fun _ => IntS_X _) hI
  · rw [AbstractGermZero.upG_subst (I := fun _ => I0) t ht0 g, key]

section Chart

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

end Chart

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieP_TCoord
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds
namespace TCoord

open Formalism.IncomingBounds FormalGermZero GeneralGermZero

variable {C : Type} [Field C] {κ : Type} [Fintype κ]

theorem tcoord_abs {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (X : RawChart C d I κ) (g : Fin 2)
    (w : κ → I g → C) (hwI : ∀ x c, V.Ge 0 (w x c))
    (hw : ∀ c c' : I g, ∑ x, X.u g c x * w x c' = if c = c' then 1 else 0)
    (tan : I g → I g → C) (hun : V.v (Matrix.of tan).det = 0)
    (P : κ → MvPowerSeries (I g) C) (hP0 : ∀ j, MvPowerSeries.constantCoeff (P j) = 0) (hPI : ∀ j, IntS V (P j))
    (hPlin : ∀ j c, MvPowerSeries.coeff (Finsupp.single c 1) (P j) = ∑ c', X.u g c' j * tan c c')
    (t : I g → MvPowerSeries (I g) C) (ht0 : ∀ c, MvPowerSeries.constantCoeff (t c) = 0)
    (hPt : ∀ j, MvPowerSeries.subst t (P j) =
      MvPowerSeries.subst (fun i => ∑ c', X.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C)) (X.ex j))
    (c : I g) :
    ∃ T : MvPowerSeries κ C, IntS V T ∧ MvPowerSeries.constantCoeff T = 0 ∧
      MvPowerSeries.subst (fun x => X.expPt g x) T = upG g (t c) := by

  set E : κ → MvPowerSeries (I g) C := fun j =>
    MvPowerSeries.subst (fun i => ∑ c', X.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C)) (X.ex j) with hE
  have hE0 : ∀ j, MvPowerSeries.constantCoeff (E j) = 0 := fun j => by
    rw [hE]; simp only; rw [← hPt j]; exact constantCoeff_subst_zero ht0 (hP0 j)
  have hlin0 : ∀ i : κ, MvPowerSeries.constantCoeff
      (∑ c', X.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C)) = 0 := fun i => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun c' _ => by
      rw [MvPowerSeries.constantCoeff_smul, MvPowerSeries.constantCoeff_X, smul_zero]
  have hXg : MvPowerSeries.HasSubst
      (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => MvPowerSeries.constantCoeff_X _
  have hupE : ∀ j, X.expPt g j = upG g (E j) := by
    intro j
    show _ = MvPowerSeries.subst (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) (E j)
    rw [hE]
    simp only
    rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hlin0) hXg]
    unfold RawChart.expPt
    congr 1
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← MvPowerSeries.coe_substAlgHom hXg, map_sum]
    simp only [map_smul, MvPowerSeries.coe_substAlgHom hXg, MvPowerSeries.subst_X hXg]

  set φ : I g → MvPowerSeries (I g) C := fun k => ∑ j, w j k • P j with hφ
  set t₂ : I g → MvPowerSeries (I g) C := fun k => ∑ j, w j k • E j with ht₂
  have hφ0 : ∀ k, MvPowerSeries.constantCoeff (φ k) = 0 := fun k => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hφ]; simp only; rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [MvPowerSeries.constantCoeff_smul, hP0 j, smul_zero]
  have ht₂0 : ∀ k, MvPowerSeries.constantCoeff (t₂ k) = 0 := fun k => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ht₂]; simp only; rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [MvPowerSeries.constantCoeff_smul, hE0 j, smul_zero]
  have hφI : ∀ k, IntS V (φ k) := fun k μ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hφ]; simp only; rw [map_sum]
    exact VF.Ge.sum fun j _ => by rw [MvPowerSeries.coeff_smul]; exact (hwI j k).mul_int (hPI j μ)
  have hL : (Matrix.of fun k c : I g => MvPowerSeries.coeff (Finsupp.single c 1) (φ k)) = (Matrix.of tan).transpose := by
    ext k c
    rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply, hφ]
    simp only
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [MvPowerSeries.coeff_smul, hPlin]
    have e : ∑ j, w j k * ∑ c', X.u g c' j * tan c c' = ∑ c', tan c c' * ∑ j, X.u g c' j * w j k := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    simp only [hw, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hts := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
  have ht₂s := MvPowerSeries.hasSubst_of_constantCoeff_zero ht₂0
  have heq : ∀ k, MvPowerSeries.subst t (φ k) = MvPowerSeries.subst t₂ (MvPowerSeries.X k : MvPowerSeries (I g) C) := by
    intro k
    rw [MvPowerSeries.subst_X ht₂s, hφ, ht₂]
    simp only
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← MvPowerSeries.coe_substAlgHom hts, map_sum]
    simp only [map_smul, MvPowerSeries.coe_substAlgHom hts, hPt]
    rfl
  obtain ⟨h, hh0, hhI, hth⟩ := AbstractGermZero.one_group V t t₂ φ (fun k => MvPowerSeries.X k) ht₂0 ht0 hφ0 hφI
    (by rw [hL, Matrix.det_transpose]; exact hun) (fun k => MvPowerSeries.constantCoeff_X k) (fun k => intS_X k) heq

  set ℓ : I g → MvPowerSeries κ C := fun k => ∑ j, w j k • (MvPowerSeries.X j : MvPowerSeries κ C) with hℓ
  have hℓ0 : ∀ k, MvPowerSeries.constantCoeff (ℓ k) = 0 := fun k => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hℓ]; simp only; rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => by
      rw [MvPowerSeries.constantCoeff_smul, MvPowerSeries.constantCoeff_X, smul_zero]
  have hℓI : ∀ k, IntS V (ℓ k) := fun k μ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hℓ]; simp only; rw [map_sum]
    exact VF.Ge.sum fun j _ => by rw [MvPowerSeries.coeff_smul]; exact (hwI j k).mul_int (intS_X j μ)
  have hpt0 : ∀ x, MvPowerSeries.constantCoeff (X.expPt g x) = 0 := fun x => by
    rw [hupE x]
    exact constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) (hE0 x)
  have hpts := MvPowerSeries.hasSubst_of_constantCoeff_zero hpt0
  refine ⟨MvPowerSeries.subst ℓ (h c), IntS.subst hℓ0 hℓI (hhI c), constantCoeff_subst_zero hℓ0 (hh0 c), ?_⟩
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hℓ0) hpts, hth c]
  show _ = MvPowerSeries.subst (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C))
    (MvPowerSeries.subst t₂ (h c))
  rw [MvPowerSeries.subst_comp_subst_apply ht₂s hXg]
  congr 1
  funext k
  rw [hℓ, ht₂]
  simp only
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.coe_substAlgHom hpts, map_sum, ← MvPowerSeries.coe_substAlgHom hXg, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul, MvPowerSeries.coe_substAlgHom hpts, MvPowerSeries.subst_X hpts,
    MvPowerSeries.coe_substAlgHom hXg, hupE j]
  rfl

theorem tcoord_gen {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (X : RawChart C d I κ)
    (F : κ → MvPowerSeries (Fin 2 × κ) C) (hF0 : ∀ k, MvPowerSeries.constantCoeff (F k) = 0)
    (hFI : ∀ k, IntS V (F k)) (hadd : LgAdd F X.lg)
    (hlin : ∀ k (μ : κ →₀ ℕ), μ.degree ≤ 1 →
      MvPowerSeries.coeff μ (X.lg k) = MvPowerSeries.coeff μ (MvPowerSeries.X k))
    (hexlg : ∀ k, MvPowerSeries.subst X.lg (X.ex k) = (MvPowerSeries.X k : MvPowerSeries κ C))
    (hsat : ∀ g, ∃ w : κ → I g → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I g, ∑ x, X.u g c x * w x c' = if c = c' then 1 else 0)
    (H : ∀ g, X.CartHyp V g) : RawChart.TCoordSt H := by
  intro S t ht g c
  obtain ⟨w, hwI, hw⟩ := hsat g
  obtain ⟨P, hP0, hPI, hPlin, hPt⟩ := sysK_P X F hF0 hFI hadd hlin hexlg (H g) (S g)
  exact tcoord_abs X g w hwI hw (S g).tan (S g).unimod P hP0 hPI hPlin (t g) (ht g).1 (hPt (t g) (ht g)) c

end TCoord

def TCoordSelfSt : Prop := AllSelf fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.TCoordSt Hc

theorem tcoordSelf_holds : TCoordSelfSt := by
  unfold TCoordSelfSt AllSelf
  intro C _ _ V O _ _ dd Y d _ I0 _ p H
  exact TCoord.tcoord_gen (Y.rawSelf p) (SelfConjugateGermZero.lawS Y) (SelfConjugateGermZero.lawS_const Y) (SelfConjugateGermZero.lawS_int Y) (SelfConjugateGermZero.lgS_add Y p)
    (SelfConjugateGermZero.lgS_lin Y p) (SelfConjugateGermZero.exS_lg Y p) (SelfConjugateGermZero.sat_self Y p) H

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePPTSelf
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

def PTExSelfSt : Prop :=
  AllSelf fun C _ V d I _ _ X => ∀ (g : Fin 2) (a : ZMod d) (w : I g → C), (∀ c, V.Ge 0 (w c)) →
    (∀ c, X.tyC g (Sum.inl c) ≠ a → w c = 0) →
    ∃ x ∈ X.TySet V g, ∀ c, x 0 (Sum.inl c) = w c

def PTAvgSelfSt : Prop :=
  AllSelf fun C _ V d I _ _ X => ∀ (g : Fin 2) (a : ZMod d) (x : ℕ → I g ⊕ JJ I g → C), x ∈ X.TySet V g →
    (∀ n, X.tyC g n ≠ a → x 0 n = 0) →
    ∃ x' ∈ X.TySet V g, x' 0 = x 0 ∧ ∀ (i : ℕ) n, X.tyC g n ≠ a + i → x' i n = 0

def OActSelfSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0)
    (g : Fin 2) (α : O) (x : ℕ → I0 ⊕ I0 → C), x ∈ (Y.rawSelf p).TySet V g →
    (fun s n => p.em ((Y.rawSelf p).tyC g n) α * x s n) ∈ (Y.rawSelf p).TySet V g

def LimSelfSt : Prop :=
  AllSelf fun C _ V _ I _ _ X => ∀ (g : Fin 2) (x : ℕ → ℕ → I g ⊕ JJ I g → C) (x' : ℕ → I g ⊕ JJ I g → C),
    (∀ k, x k ∈ X.TySet V g) → VLim V x x' → x' ∈ X.TySet V g

private theorem ge_zero_mul_field {C : Type} [Field C] (V : VF C) {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) :
    V.Ge 0 (a * b) := by
  unfold VF.Ge at *
  rw [V.v.map_mul]
  simp only [WithTop.coe_zero] at *
  exact add_nonneg ha hb

private theorem ge_zero_finset_sum_field {C : Type} [Field C] (V : VF C) {ι : Type} (s : Finset ι) (f : ι → C)
    (h : ∀ i ∈ s, V.Ge 0 (f i)) : V.Ge 0 (∑ i ∈ s, f i) := by
  refine Finset.sum_induction f (fun z => V.Ge 0 z) (fun a b ha hb => ?_) ?_ h
  · exact le_trans (le_min ha hb) (V.v.map_add a b)
  · show ((0 : ℝ) : WithTop ℝ) ≤ V.v 0
    rw [AddValuation.map_zero]
    exact le_top

private theorem tyS_sub_ite_zero_eq_sub_C_mul_X {C : Type} [Field C] (l : ℕ) (a : ℕ → C) (c : C) :
    tyS l (fun s => a s - if s = 0 then c else 0) = tyS l a - PowerSeries.C c * PowerSeries.X := by
  ext m
  rw [map_sub, ← pow_one (PowerSeries.X : PowerSeries C), PowerSeries.coeff_C_mul_X_pow]
  simp only [tyS, PowerSeries.coeff_mk]
  have h1 : ∀ s, (if l ^ s = m then a s - (if s = 0 then c else 0) else 0) =
      (if l ^ s = m then a s else 0) - (if s = 0 then (if m = 1 then c else 0) else 0) := by
    intro s
    by_cases hs : s = 0
    · subst hs
      by_cases hm : m = 1
      · subst hm
        simp
      · have hm' : (1 : ℕ) ≠ m := fun h => hm h.symm
        simp [hm, hm']
    · simp [hs]
  rw [Finset.sum_congr rfl (fun s _ => h1 s), Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp

theorem ptSelf_of (hEx : PTExSelfSt) (hAvg : PTAvgSelfSt) (hStab : HStabSelfSt) : PTSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g a w hw hty
  obtain ⟨x, hx, hx0⟩ := hEx C V O dd Y d I0 p g a w hw hty
  obtain ⟨γ, lam, hγ, hlam, hlg, hq⟩ := hx
  have hl1 : V.l ≠ 1 := V.l_prime.one_lt.ne'
  have hγ0 : ∀ i, ∀ m < 1, PowerSeries.coeff m (γ i) = 0 := by
    intro i m hm
    rw [Nat.lt_one_iff.mp hm, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hγ i).1
  have c1 : ∀ f : ℕ → C, PowerSeries.coeff 1 (tyS V.l f) = f 0 := by
    intro f
    simp [tyS, PowerSeries.coeff_mk, Finset.sum_range_succ, hl1]
  have hdeg : ∀ j : Fin 2 × Fin dd, (Finsupp.single j 1).degree ≤ 1 := by
    intro j
    first
    | simp [Finsupp.degree_single]
    | (unfold Finsupp.degree; simp)
  have hγ1 : ∀ i, PowerSeries.coeff 1 (γ i) = ∑ c, (Y.rawSelf p).u g c i * w c := by
    intro i
    have h1 := congrArg (PowerSeries.coeff 1) (hlg i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [coeff_alongCv_low le_rfl hγ0 (FBChart.self_chart_log_constantCoeff (Y := Y) (p := p) i), map_sum] at h1
    simp only [PowerSeries.coeff_smul, c1, hx0, smul_eq_mul] at h1
    rw [← h1, Finset.sum_eq_single i]
    · rw [FBChart.rawSelf_lin (Y := Y) (p := p) i _ (hdeg i), MvPowerSeries.coeff_X, if_pos rfl, one_mul]
    · intro j _ hji
      rw [FBChart.rawSelf_lin (Y := Y) (p := p) i _ (hdeg j), MvPowerSeries.coeff_X, if_neg, zero_mul]
      intro h
      exact hji (Finsupp.single_left_injective one_ne_zero h)
    · intro h
      exact absurd (Finset.mem_univ i) h
  have key : ∀ q : I0, V.Ge 0 (PowerSeries.coeff 1 (lam q) - x 0 (Sum.inr q)) := by
    intro q
    have h2 := congrArg (PowerSeries.coeff 1) (hq q)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [c1, map_add (f := _), map_sub, map_sum,
      coeff_alongCv_low le_rfl hγ0 (RawChart.constantCoeff_sg (Y.rawSelf p) (fun e he => FBChart.rawSelf_axis0 (Y := Y) (p := p) e he) _)] at h2
    simp only [hγ1] at h2
    have hA : ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) ((Y.rawSelf p).sg ((Y.rawSelf p).u (1 - g) q)) *
        ∑ c, (Y.rawSelf p).u g c i * w c =
        ∑ c, w c * (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) := by
      simp only [RawChart.sg1, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun i _ => by ring))
    rw [hA] at h2
    have hS : ∀ c, PowerSeries.coeff 1 (if (Y.rawSelf p).ty g c = (Y.rawSelf p).ty (1 - g) q then
        (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c))
        else 0) = if (Y.rawSelf p).ty g c = (Y.rawSelf p).ty (1 - g) q then
        (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) * w c else 0 := by
      intro c
      split_ifs
      · simp only [PowerSeries.coeff_smul, c1, hx0, smul_eq_mul]
      · exact map_zero _
    simp only [hS] at h2
    have h3 : PowerSeries.coeff 1 (lam q) - x 0 (Sum.inr q) =
        ∑ c, if (Y.rawSelf p).ty g c = (Y.rawSelf p).ty (1 - g) q then 0 else
          w c * (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) := by
      rw [h2, show ∀ L A S : C, L - (L - A + S) = A - S from fun L A S => by ring, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      split_ifs <;> ring
    rw [h3]
    refine ge_zero_finset_sum_field V _ _ (fun c _ => ?_)
    split_ifs with hne
    · show ((0 : ℝ) : WithTop ℝ) ≤ V.v 0
      rw [AddValuation.map_zero]
      exact le_top
    · exact ge_zero_mul_field V (hw c) (hStab C V O dd Y d I0 p g c q hne)
  have hyT : (fun s n => Sum.elim (fun c => x s (Sum.inl c))
      (fun q => x s (Sum.inr q) - if s = 0 then x 0 (Sum.inr q) else 0) n : ℕ → I0 ⊕ I0 → C) ∈
      (Y.rawSelf p).TySet V g := by
    refine ⟨γ, fun q => lam q - PowerSeries.C (x 0 (Sum.inr q)) * PowerSeries.X, hγ, ?_, ?_, ?_⟩
    · intro q
      refine ⟨?_, ?_⟩
      · simp [(hlam q).1]
      · intro m
        rcases eq_or_ne m 1 with rfl | hm
        · have h4 : PowerSeries.coeff 1 (lam q - PowerSeries.C (x 0 (Sum.inr q)) * PowerSeries.X) =
              PowerSeries.coeff 1 (lam q) - x 0 (Sum.inr q) := by
            simp
          rw [h4]
          exact key q
        · have h4 : PowerSeries.coeff m (lam q - PowerSeries.C (x 0 (Sum.inr q)) * PowerSeries.X) =
              PowerSeries.coeff m (lam q) := by
            rw [map_sub, ← pow_one (PowerSeries.X : PowerSeries C), PowerSeries.coeff_C_mul_X_pow, if_neg hm,
              sub_zero]
          rw [h4]
          exact (hlam q).2 m
    · intro i
      exact hlg i
    · intro q
      show tyS V.l (fun s => x s (Sum.inr q) - if s = 0 then x 0 (Sum.inr q) else 0) =
        (lam q - PowerSeries.C (x 0 (Sum.inr q)) * PowerSeries.X) -
          alongCv γ ((Y.rawSelf p).sg ((Y.rawSelf p).u (1 - g) q)) +
          ∑ c, if (Y.rawSelf p).ty g c = (Y.rawSelf p).ty (1 - g) q then
            (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c))
            else 0
      rw [tyS_sub_ite_zero_eq_sub_C_mul_X, hq q]
      ring
  obtain ⟨x', hx', h0, hvan⟩ := hAvg C V O dd Y d I0 p g a _ hyT (by
    intro n hn
    rcases n with c | q
    · show x 0 (Sum.inl c) = 0
      rw [hx0]
      exact hty c hn
    · show x 0 (Sum.inr q) - (if (0 : ℕ) = 0 then x 0 (Sum.inr q) else 0) = 0
      simp)
  refine ⟨x', hx', ?_, hvan⟩
  rw [h0]
  funext n
  rcases n with c | q
  · exact hx0 c
  · show x 0 (Sum.inr q) - (if (0 : ℕ) = 0 then x 0 (Sum.inr q) else 0) = 0
    simp

theorem ptAvgSelf_of (hAct : OActSelfSt) (hLim : LimSelfSt) : PTAvgSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g a x hx hx0
  set X := Y.rawSelf p with hX
  let M : Set (ℕ → I0 ⊕ I0 → C) := {m | ∀ y ∈ X.TySet V g, m * y ∈ X.TySet V g}
  have hAdd := addCvSelf_holds C V O dd Y d I0 p
  have h1 : (1 : ℕ → I0 ⊕ I0 → C) ∈ M := fun y hy => by rwa [one_mul]
  have hadd : ∀ m m', m ∈ M → m' ∈ M → m + m' ∈ M := fun m m' hm hm' y hy => by
    rw [add_mul]; exact X.add_mem V g hAdd (fun g c x => Y.rawSelf_u_integral p g c x) _ _ (hm y hy) (hm' y hy)
  have hneg : ∀ m, m ∈ M → -m ∈ M := fun m hm y hy => by
    rw [neg_mul]; exact X.neg_mem V g Y.l_odd _ (hm y hy)
  have hmul : ∀ m m', m ∈ M → m' ∈ M → m * m' ∈ M := fun m m' hm hm' y hy => by
    rw [mul_assoc]; exact hm _ (hm' y hy)
  have hteich : ∀ c : C, V.Ge 0 c → (fun s (_ : I0 ⊕ I0) => c ^ (V.l ^ s)) ∈ M := fun c hc y hy =>
    X.teich_mem V g c hc y hy
  have hact : ∀ α : O, (fun (_ : ℕ) n => p.em (X.tyC g n) α) ∈ M := fun α y hy =>
    hAct C V O dd Y d I0 p g α y hy
  have hlim : ∀ (m : ℕ → ℕ → I0 ⊕ I0 → C) (m' : ℕ → I0 ⊕ I0 → C), (∀ k, m k ∈ M) → VLim V m m' → m' ∈ M :=
    fun m m' hm hmm' y hy => hLim C V O dd Y d I0 p g (fun k => m k * y) (m' * y) (fun k => hm k y hy) (hmm'.mul_right y)
  have hI := IndAr.ind_gen p.em p.em_int p.em_frob p.em_sep (I0 ⊕ I0) (X.tyC g) M h1 hadd hneg hmul hteich hact hlim a
  refine ⟨_, hI x hx, ?_, ?_⟩
  · funext n
    simp only [Pi.mul_apply, Nat.cast_zero, add_zero]
    by_cases hn : X.tyC g n = a
    · rw [if_pos hn, one_mul]
    · rw [if_neg hn, zero_mul, hx0 n hn]
  · intro i n hn
    simp only [Pi.mul_apply]
    rw [if_neg hn, zero_mul]

theorem ptSelf_of_act (hEx : PTExSelfSt) (hAct : OActSelfSt) (hLim : LimSelfSt) (hStab : HStabSelfSt) : PTSelfSt :=
  ptSelf_of hEx (ptAvgSelf_of hAct hLim) hStab

end Formalism.L2.FormalSeriesBounds
end
end

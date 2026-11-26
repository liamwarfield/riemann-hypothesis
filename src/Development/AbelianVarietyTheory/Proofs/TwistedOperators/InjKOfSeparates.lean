module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfConjMemOfPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationThetaFunctionSupLeQuotientHeig
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowStableWittTargetProjections
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmSplitHalves
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualFullLatticeShared

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjKOfSeparates
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqAdFormsOfValues
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus posDef_dual Cols levPlus mem_cols)

namespace GlobalTheory.RowTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

section Generic

variable {G Γ W Cl ι : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Finite Cl]


open Classical in
theorem eq_adForms_of_values (ιG : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (y : Cl → G)
    (hdec : ∀ g, ∃ (γ : Γ) (c : Cl) (k : J), g = ιG γ * y c * k) (S : Submodule ℂ (G → W))
    (hS : S ≤ Bridge.AdForms ιG ρ J 1) (w : ι → W) (hw : Submodule.span ℂ (Set.range w) = ⊤)
    (hsingle : ∀ c i, ∃ s ∈ S, ∀ c', s (y c') = if c' = c then w i else 0) : S = Bridge.AdForms ιG ρ J 1 := by
  classical
  have : Fintype Cl := Fintype.ofFinite _
  refine le_antisymm hS fun F hF => ?_
  let ev : (G → W) →ₗ[ℂ] (Cl → W) := LinearMap.pi fun c => LinearMap.proj (y c)
  have hev : ∀ f c, ev f c = f (y c) := fun _ _ => rfl
  have hinj : ∀ f ∈ Bridge.AdForms ιG ρ J 1, ev f = 0 → f = 0 := by
    intro f hf h0
    funext g
    obtain ⟨γ, c, k, rfl⟩ := hdec g
    have h1 : f (y c) = 0 := congrFun h0 c
    have h2 := hf γ (y c) k
    rw [h2, h1, map_zero, smul_zero]
    rfl
  have hsurj : S.map ev = ⊤ := by
    refine eq_top_iff.2 fun f _ => ?_
    rw [← Finset.univ_sum_single f]
    refine Submodule.sum_mem _ fun c _ => ?_
    have hfc : f c ∈ Submodule.span ℂ (Set.range w) := by rw [hw]; trivial
    have e : Pi.single c (f c) = LinearMap.single ℂ (fun _ : Cl => W) c (f c) := rfl
    rw [e]
    refine Submodule.mem_comap.1 (((Submodule.span_le (p := (S.map ev).comap (LinearMap.single ℂ (fun _ : Cl => W) c))).2 ?_) hfc)
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hsv⟩ := hsingle c i
    refine Submodule.mem_comap.2 ⟨s, hs, funext fun c' => ?_⟩
    rw [hev, hsv]
    by_cases h : c' = c
    · subst h; simp
    · simp [h]
  obtain ⟨s, hs, hse⟩ : ev F ∈ S.map ev := by rw [hsurj]; trivial
  have h0 : F - s = 0 := hinj _ (sub_mem hF (hS hs)) (by rw [map_sub, hse, sub_self])
  rwa [sub_eq_zero.1 h0]

end Generic

section Reps

variable {T' : Type} {L : LevCh D T'} {sc : Consts} {G : GridData L sc}

theorem exists_gf_reps (rp : ClassReps G) :
    ∃ y : G.ClPlus → Bridge.Gf (G.V (.top 0)),
      (∀ c, Formalism.UG.bc (Lev.swapAE D) ((y c : Bridge.Gf (G.V (.top 0))) : GL _ _) = (rp.x c : GLf G)) ∧
      ∀ g : Bridge.Gf (G.V (.top 0)), ∃ (γ : GQ (G.V (.top 0))) (c : G.ClPlus) (k : levPlus G),
        g = Bridge.ratF (G.V (.top 0)) γ * y c * k := by
  obtain ⟨hfin, -, -, -, hcl⟩ := GlobalTheory.DefFree.AdelCls.adelic_classes D (G.V (.top 0))
  choose h _ hh using fun c => hfin (rp.x c)
  refine ⟨fun c => (finHom (G.V (.top 0))).rangeRestrict (h c), fun c => ?_, fun g => ?_⟩
  · have := congrArg Subtype.val (hh c)
    exact this
  · have hg0 : ∃ h0 : GA D (G.V (.top 0)), finHom (G.V (.top 0)) h0 = g.1 := g.2
    obtain ⟨h0, hg⟩ := hg0
    have hc : GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus (h (GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0)) =
        GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0 := by
      show (Quotient.mk'' (GlobalTheory.DefFree.finU (G.V (.top 0)) (h (GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0))) :
        Cl D.sp.cm (G.V (.top 0)).gram G.Kplus) = _
      rw [hh]
      exact rp.classRepresentative_mk _
    have hx := (hcl G.Kplus (h (GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0)) h0).1 hc
    obtain ⟨γ, hγ, hx⟩ := hx
    obtain ⟨κ, hκ, k, hk, e⟩ := hx
    have hκ' : (finHom (G.V (.top 0))).rangeRestrict κ ∈ levPlus G := by
      show Formalism.UG.bc (Lev.swapAE D) (finHom (G.V (.top 0)) κ) ∈ G.Kplus
      exact hκ.2
    refine ⟨⟨γ, hγ⟩, GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0, ⟨_, hκ'⟩, Subtype.ext ?_⟩
    have hk1 : finHom (G.V (.top 0)) k = 1 := hk
    show g.1 = finHom (G.V (.top 0)) γ * finHom (G.V (.top 0)) (h (GlobalTheory.DefFree.clsA (G.V (.top 0)) G.Kplus h0)) *
      finHom (G.V (.top 0)) κ
    have e2 := congrArg (finHom (G.V (.top 0))) e
    simp only [map_mul (finHom (G.V (.top 0))), hk1, mul_one] at e2
    exact hg.symm.trans e2


open Classical in
theorem span_colOf_psi {θ : InfFam D} (hθ : IsInfFam θ) (rp : ClassReps G) {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G))
    (Φ : G.Datum) :
    Submodule.span ℂ ((fun a => colOf θ (psi rp e a)) '' {a | datumOf e a = Φ}) = Cols G θ := by
  classical
  obtain ⟨y, hy, hdec⟩ := exists_gf_reps rp
  have hspan : Submodule.span ℂ (Set.range fun i => GlobalTheory.CoefModel.toHilb (LaP G) (posDef_dual G)
      (GlobalTheory.CoefModel.mapVV D.what₂.embLL (LaP G) (bVV D.what₂.LL (LaP G) i))) = ⊤ := by
    have := congrArg (Submodule.map (GlobalTheory.CoefModel.toHilb (LaP G) (posDef_dual G)).toLinearMap)
      (GlobalTheory.CoefModel.span_mapVV D.what₂.embLL (LaP G))
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range, ← Set.range_comp] at this
    exact this
  refine eq_adForms_of_values (W := (coefPlus G θ).W) (Bridge.ratF (G.V (.top 0))) (coefPlus G θ).coef.ρ
    (levPlus G) y hdec _ ?_ _ hspan fun c i => ?_
  · rw [Submodule.span_le]
    rintro _ ⟨a, -, rfl⟩
    exact colOf_mem hθ (psi_left _ _ a) fun g _ hk => psi_right _ _ a g hk
  · refine ⟨colOf θ (psi rp e (e.symm ((Φ, c), i))), Submodule.subset_span ⟨_, ?_, rfl⟩, fun c' => ?_⟩
    · show (e (e.symm ((Φ, c), i))).1.1 = Φ
      rw [Equiv.apply_symm_apply]
    · unfold colOf psi
      rw [hy c', Equiv.apply_symm_apply, rp.gridClassReps_delta_apply_rep (ClassReps.neat rp)]
      by_cases h : c' = c <;> simp [h] <;> rfl

end Reps

variable (ch : Choice R)

theorem span_col_eq_cols (Φ : ch.G.Datum) :
    Submodule.span ℂ (ch.col '' {a | ch.Phi a = Φ}) = Cols ch.G ch.W.θ :=
  span_colOf_psi ch.W.θ_is ch.rp ch.e Φ

end GlobalTheory.RowTest

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols Separates rowForm)

namespace GlobalTheory.RowTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Period

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)

theorem bplusConv_add {φ φ' : Fn G (.top 0)} {F : Fn G (.grid D.R.m 0)} (h : BplusConv W M φ F)
    (h' : BplusConv W M φ' F) :
    BplusConv W M (φ + φ') F ∧ Bplus W M (φ + φ') F = Bplus W M φ F + Bplus W M φ' F := by
  have e : ∀ x, besInt W (φ + φ') F x = fun n => besInt W φ F x n + besInt W φ' F x n := fun x => funext fun n => by
    simp only [besInt, Pi.add_apply]; ring
  have ei : ∀ x, ∫ n in M.fdN, besInt W (φ + φ') F x n ∂M.νN =
      (∫ n in M.fdN, besInt W φ F x n ∂M.νN) + ∫ n in M.fdN, besInt W φ' F x n ∂M.νN := fun x => by
    rw [e x]; exact integral_add (h.1 x) (h'.1 x)
  refine ⟨⟨fun x => ?_, ?_⟩, ?_⟩
  · rw [e x]; exact (h.1 x).add (h'.1 x)
  · simp only [ei]; exact h.2.add h'.2
  · simp only [Bplus, ei]; exact integral_add h.2 h'.2

theorem bplusConv_smul (c : ℂ) {φ : Fn G (.top 0)} {F : Fn G (.grid D.R.m 0)} (h : BplusConv W M φ F) :
    BplusConv W M (c • φ) F ∧ Bplus W M (c • φ) F = c * Bplus W M φ F := by
  have e : ∀ x, besInt W (c • φ) F x = fun n => c * besInt W φ F x n := fun x => funext fun n => by
    simp only [besInt, Pi.smul_apply, smul_eq_mul]; ring
  have ei : ∀ x, ∫ n in M.fdN, besInt W (c • φ) F x n ∂M.νN = c * ∫ n in M.fdN, besInt W φ F x n ∂M.νN := fun x => by
    rw [e x]; exact integral_const_mul _ _
  refine ⟨⟨fun x => ?_, ?_⟩, ?_⟩
  · rw [e x]; exact (h.1 x).const_mul c
  · simp only [ei]; exact h.2.const_mul c
  · simp only [Bplus, ei]; exact integral_const_mul _ _

theorem bplusConv_zero (F : Fn G (.grid D.R.m 0)) : BplusConv W M 0 F ∧ Bplus W M 0 F = 0 := by
  have e : ∀ x, besInt W (0 : Fn G (.top 0)) F x = fun _ => 0 := fun x => funext fun n => by simp [besInt]
  refine ⟨⟨fun x => by rw [e x]; exact integrableOn_zero, ?_⟩, ?_⟩
  · simp only [e, integral_zero]; exact integrableOn_zero
  · simp only [Bplus, e, integral_zero]

end Period

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}


set_option maxHeartbeats 1000000 in
theorem inj_of_separates {ch : Choice R} (hIs : ch.Is) (hM : R.IsModels) {ρ : ch.G.RealVec}
    {ξ : Module.Dual ℂ (coefPlus ch.G ch.W.θ).W} (hsep : Separates R ch.W ch.M ch.w ρ ξ)
    (hconv : ∀ a u, ConvK (ch.withReal ρ ξ) a u) (u : R.HE.H) (hu : ∀ a, psiK ch a u = 0) : u = 0 := by
  have hu' : ∀ a, psiK (ch.withReal ρ ξ) a u = 0 := fun a => hIs.real u hu ρ ξ a
  by_contra h0
  have hmem : R.HE.e u ∈ R.EEat R.triv := hM.HE.2.1 ▸ LinearMap.mem_range_self _ u
  have hne : R.HE.e u ≠ 0 := fun h => h0 (hM.HE.1 (h.trans (map_zero _).symm))
  obtain ⟨Ψ, hΨ, Φ, -, hf⟩ := hsep _ hmem hne
  apply hf
  rw [← span_col_eq_cols ch Φ] at hΨ
  have key : ∀ x ∈ Submodule.span ℂ (ch.col '' {a | ch.Phi a = Φ}),
      BplusConv ch.W ch.M (pairVec (coefPlus ch.G ch.W.θ) ξ x) (thetaChi ch.W ch.M ρ Φ (rowForm R ch.w (R.HE.e u))) ∧
        Bplus ch.W ch.M (pairVec (coefPlus ch.G ch.W.θ) ξ x) (thetaChi ch.W ch.M ρ Φ (rowForm R ch.w (R.HE.e u))) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have ha' : ch.Phi a = Φ := ha
      have h1 : FConv ch.W ch.M ρ ξ (ch.col a) (ch.Phi a) (ch.form u) := hconv a u
      have h2 : fPsiPhi ch.W ch.M ρ ξ (ch.col a) (ch.Phi a) (ch.form u) = 0 := hu' a
      rw [ha'] at h1 h2
      exact ⟨h1.2, h2⟩
    | zero =>
      rw [LinearMap.map_zero (pairVec (coefPlus ch.G ch.W.θ) ξ)]; exact bplusConv_zero ch.W ch.M _
    | add x y _ _ hx hy =>
      rw [LinearMap.map_add (pairVec (coefPlus ch.G ch.W.θ) ξ) x y]
      obtain ⟨hc, he⟩ := bplusConv_add ch.W ch.M hx.1 hy.1
      exact ⟨hc, by rw [he, hx.2, hy.2, add_zero]⟩
    | smul c x _ hx =>
      rw [LinearMap.map_smul (pairVec (coefPlus ch.G ch.W.θ) ξ) c x]
      obtain ⟨hc, he⟩ := bplusConv_smul ch.W ch.M c hx.1
      exact ⟨hc, by rw [he, hx.2, mul_zero]⟩
  exact (key Ψ hΨ).2

theorem injK_of_separates (hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate)
    (hL : GlobalTheory.RowClaim.Big fun ch => ∀ ρ ξ a u, ConvK (ch.withReal ρ ξ) a u) : GlobalTheory.RowClaim.InjK := by
  obtain ⟨C1, hL⟩ := hL
  refine ⟨max 6510 C1, fun ε CF hCF => ?_⟩
  obtain ⟨x1, hS⟩ := hS ε CF (le_of_max_le_left hCF)
  obtain ⟨x2, hL⟩ := hL ε CF (le_of_max_le_right hCF)
  refine ⟨max x1 x2, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hset ch hch hsc u hu => ?_⟩
  have hconv := hL D large₂ hε (le_of_max_le_right hx) Γ Pl0 T A Ks R F hset ch hch hsc
  obtain ⟨sc, G, W, M, ρ0, ξ0, cv, rm, S, rp, n, e, c⟩ := ch
  change sc = _ at hsc
  subst hsc
  obtain ⟨ρ, ξ, hsep⟩ := hS D large₂ hε (le_of_max_le_left hx) hset.size hset.eser Γ Pl0 T A Ks R hset.core.lev hset.grp G W
    hch.weil M hch.vol _ hch.w_ne
  exact inj_of_separates hch hset.core.models hsep (hconv ρ ξ) u hu

end GlobalTheory.RowTest

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianPairingFourierJacobiStepBasePointColumn
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianPairingFourierJacobiStepBasePointColumn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.SepRows GlobalTheory.Asc
open GlobalTheory.FunObj hiding Frames
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section
namespace GlobalTheory.CharXFB

variable {D : D7}

theorem hA_smul_left (T : HSp D) (c : AE D) (y z : Fin T.rank → AE D) : hA T (c • y) z = c * hA T y z := by
  simp only [hA, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem hA_smul_right (T : HSp D) (c : AE D) (y z : Fin T.rank → AE D) : hA T y (c • z) = cA D c * hA T y z := by
  simp only [hA, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem ratV_smul' {n : ℕ} (c : D.host.E) (v : Fin n → D.host.E) : ratV (c • v) = incA D c • ratV v := by
  funext i; simp [ratV, map_mul]

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem xFB_col (F : Frames G) (hF : Std F) (σ : ℕ) (h' : 2 * σ + 2 ≤ D.R.m) (p : Fin (σ + 1)) :
    (fun k => xFB F σ h' k p) = incA D ((-D.host.xi0) ^ (p.1 + 1)) •
      ratV (fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) := by
  obtain ⟨h2, he, -⟩ := hF.hB σ h'
  induction p using Fin.lastCases with
  | last =>
    have hc : (Fin.castLE (by omega) (Fin.last σ) : Fin (2 * σ + 2 - 1)) = ⟨σ, by omega⟩ := Fin.ext (by simp)
    funext k
    simp only [xFB, xLast, Matrix.of_apply, Fin.snoc_last, vecB, HypDec.j0, ← ratV_mulVec, Matrix.mulVec_mulVec,
      hF.ζ (σ + 1), Matrix.mulVec_smul, hF.zB' σ h', ratV_smul', Fin.val_last, hc]
  | cast i =>
    funext k
    simp only [xFB, xLast, Matrix.of_apply, Fin.snoc_castSucc, HypDec.jX, rat, Matrix.map_apply, he, colsOf,
      Pi.smul_apply, smul_eq_mul, ratV, map_mul, Fin.val_castSucc]
    rfl

theorem extY_col (F : Frames G) (hF : Std F) (σ : ℕ) (h : 2 * (σ + 1) + 2 ≤ D.R.m)
    (a' : Mx D (G.V (.grid (2 * σ + 2) 0)).rank (σ + 1)) (p : Fin (σ + 1)) :
    (F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a' *ᵥ
        ratV (fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k
          (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) =
      incA D (star ((-D.host.xi0) ^ (p.1 + 1))) • fun k => a' k p := by
  obtain ⟨h2, he, -⟩ := hF.hJ (σ + 1) h
  have hq := ProjTgt.qY_mul_a (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)) (F.dJ (σ + 1) h) (by omega) h2 he

  rw [HypDec.extY_apply, ← Matrix.mulVec_mulVec, HypDec.pY, ← ratV_mulVec]
  have hv : ∀ (M : Matrix (Fin (σ + 1)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank) D.host.E)
      (N : Matrix (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank) (Fin (2 * (σ + 1) + 1 - 1)) D.host.E) (q : Fin (2 * (σ + 1) + 1 - 1)),
      M *ᵥ (fun k => N k q) = fun r => (M * N) r q := fun M N q => by
    funext r; simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [hv, hq]
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ratV, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single p]
  · simp only [ite_true, mul_one]; ring
  · intro r _ hr
    have : ¬ ((Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev = (Fin.castLE (by omega) r).rev) := by
      intro e; apply hr; rw [Fin.rev_inj] at e; exact Fin.ext (by simpa [Fin.ext_iff] using e.symm)
    simp only [this, ite_false, mul_zero, map_zero]
  · intro hp; exact absurd (Finset.mem_univ p) hp

theorem hA_xFB_col : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m)
    (a' : Mx D (G.V (.grid (2 * σ + 2) 0)).rank (σ + 1)) (p : Fin (σ + 1)),
    hA _ (fun k => xFB F σ h' k p) (fun k => a' k p) =
      hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p))
        ((F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a' *ᵥ
          ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k
            (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) := by
  intro D _ T L _ _ sc G _ _ _ F hF σ h h' a' p
  rw [xFB_col F hF σ h' p, extY_col F hF σ h a' p, hA_smul_left, hA_smul_right, GlobalTheory.DualPairCheck.cA_incA, star_star]

end GlobalTheory.CharXFB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianPairingFourierJacobiStepBasePointColumnStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.SepRows GlobalTheory.Asc
open GlobalTheory.FunObj hiding Frames
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianPairing_fourierJacobi_step_basePoint_columns : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (a' : Mx D (G.V (.grid (2 * σ + 2) 0)).rank (σ + 1)) (p : Fin (σ + 1)), hA _ (fun k => xFB F σ h' k p) (fun k => a' k p) = hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) ((F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a' *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) := by
  first | exact @GlobalTheory.CharXFB.hA_xFB_col | exact GlobalTheory.CharXFB.hA_xFB_col | (intros; apply GlobalTheory.CharXFB.hA_xFB_col <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceLatticeStabilisersFixWeilVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceLatticeStabilisersFixWeilVacuum
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

private theorem selfDual_full {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : Submodule.IsFullLattice D.host.E Λ := _root_.DedupShared.selfDual_isFullLattice V Λ hΛ

private theorem det_int {D : D7} {V : HSp D} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hL : Submodule.IsFullLattice D.host.E L) (g : GA D V)
    (h : ∀ y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)),
      (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E))) :
    finPart D (Formalism.L2.Theta.mt V g).det ∈ intAE D := by
  have hd : finPart D (Formalism.L2.Theta.mt V g).det = (finMat D.sp.cm.sig V.gram g).det :=
    RingHom.map_det (finPart D) (Formalism.L2.Theta.mt V g)
  rw [hd, GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers]
  exact GlobalTheory.DetTranslate.det_mem_int D.host.F L _ hL.toIsLattice.fg hL.span_eq_top h

private theorem unram_detAt {D : D7} {V : HSp D} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hL : Submodule.IsFullLattice D.host.E L) {g : GA D V}
    (h : ∀ y, y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)) ↔
      (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)))
    {e : AE D} (he : e * e = e) {ε : AF D.host.F} (hs : algebraMap (AF D.host.F) (AE D) ε * e = e)
    {χ : (AE D)ˣ →* Circle} (hχ : GlobalTheory.WeilParts.UnramAt ε χ) : χ (GlobalTheory.VecInv.detAt e he V g) = 1 := by
  refine hχ _ ?_ (GlobalTheory.Mem.DetUnit.part_mem_intAE he (det_int hL g fun y hy => (h y).1 hy)) ?_
  · change _ * (e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1
    linear_combination ((Formalism.L2.Theta.mt V g).det - 1) * hs
  · rw [← MonoidHom.map_inv]
    exact GlobalTheory.Mem.DetUnit.part_mem_intAE he (det_int hL g⁻¹ (GlobalTheory.LocalLatStab.inv_keeps V _ g h))


theorem splitVacuumFixed : ∀ D : D7, SplitVacuumFixed D := by
  intro D ψ S T χS χT om ΛS ΛT hW hS hT v hv uS uT f hf hvac k hk k' hk'
  obtain ⟨e, he, hb⟩ := hv
  have hε : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _, fun _ hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
  have hb' : e + cA D e = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := hb
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have s1 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) * e = e := by
    rw [← hb']; linear_combination he.1 + he.2.1
  have s2 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) * cA D e = cA D e := by
    rw [← hb']; linear_combination he'.1 + he.2.1
  have sk := suppPl_emb S v k
  have sk' := suppPl_emb T v k'
  have kS := emb_keeps_latHat S hS.1.fg v hk
  have kT := emb_keeps_latHat T hT.1.fg v hk'
  have key := GlobalTheory.VacStabFixed.om_split_halves hW hS hT he (fun i j => by rw [hb']; exact sk i j)
    (fun i j => by rw [hb']; exact sk' i j)
    (fun u hu => ⟨GlobalTheory.LocalLatStab.actO_mem S T _ _ _ _ _ (fun y hy => (kS y).1 hy) (fun y hy => (kT y).1 hy) u hu,
      GlobalTheory.LocalLatStab.actO_mem S T _ _ _ _ _ (GlobalTheory.LocalLatStab.inv_keeps S _ _ kS)
        (GlobalTheory.LocalLatStab.inv_keeps T _ _ kT) u hu⟩)
    (GlobalTheory.VecInv.isDetAt_detAt e he.1 S _) (GlobalTheory.VecInv.isDetAt_detAt e he.1 T _) hf
    (fun u hu hh => hvac.2 e he u (GlobalTheory.VacStabFixed.half_mem_place hε s1 hu hh) hh)
    (fun u hu hh => hvac.2 _ he' u (GlobalTheory.VacStabFixed.half_mem_place hε s2 hu hh) hh)
  rwa [splitFacO, unram_detAt (selfDual_full S ΛS hS) kS he.1 s1 uT, unram_detAt (selfDual_full T ΛT hT) kT he.1 s1 uS,
    inv_one, mul_one, Circle.coe_one, one_smul] at key

end GlobalTheory.PlaceTensor

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceLatticeStabilisersFixWeilVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_latticeStabilisers_fix_weilVacuum : ∀ D : D7, SplitVacuumFixed D := by
  first | exact @GlobalTheory.PlaceTensor.splitVacuumFixed | exact GlobalTheory.PlaceTensor.splitVacuumFixed | (intros; apply GlobalTheory.PlaceTensor.splitVacuumFixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockRealPointTransportContinuousIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockRealPointTransportContinuousIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransport

variable {D : D7}

def sg (b : Bool) : ℝ := if b then 1 else -1

theorem sg_mul_self (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

def cf (b b' : Bool) (c : ℂ) : ℂ := (c.re : ℂ) + ((sg b * sg b' * c.im : ℝ) : ℂ) * Complex.I

theorem cf_cf (b b' : Bool) (c : ℂ) : cf b b' (cf b b' c) = c := by
  have h : sg b * sg b' * (sg b * sg b') = 1 := by
    rw [mul_mul_mul_comm, sg_mul_self, sg_mul_self, one_mul]
  apply Complex.ext <;> simp [cf, h, ← mul_assoc]

theorem continuous_cf (b b' : Bool) : Continuous (cf b b') := by
  unfold cf; fun_prop

theorem jm_mul_single_mul_jm {m n : ℕ} (εB : Fin m → Bool) (εA : Fin n → Bool) (i : Fin m) (j : Fin n) :
    Formalism.REAL.Jm εB * Matrix.single i j (1 : ℂ) * Formalism.REAL.Jm εA =
      Matrix.single i j (((sg (εB i) * sg (εA j) : ℝ)) : ℂ) := by
  ext a b
  simp only [Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply, sg]
  by_cases ha : i = a <;> by_cases hb : j = b <;> subst_vars <;> simp_all <;> split_ifs <;> simp

variable {S T : HSp D}

theorem det_fr_unit {V : HSp D} (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau) : IsUnit (A.fr τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)

theorem unitMap_fr (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) (i : Fin T.rank) (j : Fin S.rank) :
    unitMap (A.onb τ) (B.onb τ) i j = (B.fr τ)⁻¹ * Matrix.single i j (1 : ℂ) * A.fr τ := by
  simp only [unitMap, GlobalTheory.ChainFr.Fr.onb, Matrix.nonsing_inv_nonsing_inv _ (det_fr_unit A τ)]

theorem cplxO_unitMap_fr (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) (i : Fin T.rank)
    (j : Fin S.rank) :
    cplxO (A.cart τ) (B.cart τ) (unitMap (A.onb τ) (B.onb τ) i j) =
      (B.fr τ)⁻¹ * Matrix.single i j ((((sg (B.ε τ i) * sg (A.ε τ j) : ℝ)) : ℂ) * Complex.I) * A.fr τ := by
  rw [unitMap_fr]
  have e : B.cart τ * ((B.fr τ)⁻¹ * Matrix.single i j (1 : ℂ) * A.fr τ) * A.cart τ =
      (B.fr τ)⁻¹ * (Formalism.REAL.Jm (B.ε τ) * Matrix.single i j (1 : ℂ) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
    simp only [GlobalTheory.ChainFr.Fr.cart, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (det_fr_unit B τ),
      Matrix.mul_nonsing_inv_cancel_left _ _ (det_fr_unit A τ)]
  rw [cplxO, e, jm_mul_single_mul_jm, ← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.smul_single, smul_eq_mul, mul_comm]

theorem fockMat_eq (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) (z : Fin T.rank → Fin S.rank → ℂ) :
    fockMat A B τ z = (B.fr τ)⁻¹ * Matrix.of (fun i j => cf (B.ε τ i) (A.ε τ j) (z i j)) * A.fr τ := by
  have ht : ∀ i j, (((z i j).re : ℂ) • unitMap (A.onb τ) (B.onb τ) i j +
      ((z i j).im : ℂ) • cplxO (A.cart τ) (B.cart τ) (unitMap (A.onb τ) (B.onb τ) i j)) =
      (B.fr τ)⁻¹ * Matrix.single i j (cf (B.ε τ i) (A.ε τ j) (z i j)) * A.fr τ := by
    intro i j
    rw [cplxO_unitMap_fr, unitMap_fr, ← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.mul_smul,
      ← Matrix.add_mul, ← Matrix.mul_add, Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add]
    congr 3
    simp only [cf, smul_eq_mul, mul_one, Complex.ofReal_mul]
    ring
  rw [fockMat]
  simp only [ht]
  simp only [← Matrix.sum_mul, ← Matrix.mul_sum]
  congr 2
  conv_rhs => rw [Matrix.matrix_eq_sum_single (Matrix.of _)]
  simp only [Matrix.of_apply]

def fockInvMat (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau)
    (X : Matrix (Fin T.rank) (Fin S.rank) ℂ) : Fin T.rank → Fin S.rank → ℂ :=
  fun i j => cf (B.ε τ i) (A.ε τ j) ((B.fr τ * X * (A.fr τ)⁻¹) i j)

theorem fockInvMat_fockMat (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau)
    (z : Fin T.rank → Fin S.rank → ℂ) : fockInvMat A B τ (fockMat A B τ z) = z := by
  funext i j
  rw [fockInvMat, fockMat_eq]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (det_fr_unit B τ),
    Matrix.mul_nonsing_inv _ (det_fr_unit A τ), Matrix.mul_one, Matrix.of_apply, cf_cf]

theorem fockMat_fockInvMat (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau)
    (X : Matrix (Fin T.rank) (Fin S.rank) ℂ) : fockMat A B τ (fockInvMat A B τ X) = X := by
  rw [fockMat_eq]
  have e : (Matrix.of fun i j => cf (B.ε τ i) (A.ε τ j) (fockInvMat A B τ X i j)) = B.fr τ * X * (A.fr τ)⁻¹ := by
    ext i j; simp only [Matrix.of_apply, fockInvMat, cf_cf]
  rw [e, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (det_fr_unit A τ), Matrix.mul_one,
    Matrix.nonsing_inv_mul_cancel_left _ _ (det_fr_unit B τ)]

theorem continuous_fockMat (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) :
    Continuous (fockMat A B τ) := by
  unfold fockMat; fun_prop

theorem continuous_fockInvMat (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) :
    Continuous (fockInvMat A B τ) :=
  continuous_pi fun i => continuous_pi fun j => (continuous_cf _ _).comp
    (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem i j)

def fockInv (θ : InfFam D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (w : WO S T) :
    VCx D.what₂.Tau S.rank T.rank :=
  fun τ => fockInvMat A B τ (GlobalTheory.FockCompare.piW θ T S w τ)

theorem fockInv_fockPt {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z : VCx D.what₂.Tau S.rank T.rank) :
    fockInv θ A B (fockPt σ A B z) = z := by
  funext τ
  have e : GlobalTheory.FockCompare.piW θ T S (fockPt σ A B z) τ = fockMat A B τ (z τ) := congrFun (h.pi_iota T S _) τ
  show fockInvMat A B τ (GlobalTheory.FockCompare.piW θ T S (fockPt σ A B z) τ) = z τ
  rw [e, fockInvMat_fockMat]

theorem fockPt_fockInv {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) {w : WO S T} (hw : w.map (finPart D) = 0) :
    fockPt σ A B (fockInv θ A B w) = w := by
  have e : (fun τ => fockMat A B τ (fockInv θ A B w τ)) = GlobalTheory.FockCompare.piW θ T S w :=
    funext fun τ => fockMat_fockInvMat A B τ _
  rw [fockPt, e]
  exact h.iota_pi hw

theorem fockPt_transport : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ →
    ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T), Continuous (fockPt σ A B) ∧
      (∀ w : WO S T, w.map (finPart D) = 0 → ∃ z, fockPt σ A B z = w) ∧
      ∀ g : VCx D.what₂.Tau S.rank T.rank → ℂ, Integrable g → ∃ (m : Measure (WO S T)) (α : WO S T → ℂ),
        SFinite m ∧ Integrable α m ∧ ∀ H : WO S T → ℂ, ∫ w, α w * H w ∂m = ∫ z, g z * H (fockPt σ A B z) := by
  intro D θ σ h S T A B
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : T2Space (WO S T) := (GlobalTheory.MixModel.lattice_Mx D T.rank S.rank).2.2.2.1
  have hc : Continuous (fockPt σ A B) :=
    (h.continuous_iota T S).comp (continuous_pi fun τ => (continuous_fockMat A B τ).comp (continuous_apply τ))
  have hic : Continuous (fockInv θ A B) := continuous_pi fun τ =>
    (continuous_fockInvMat A B τ).comp ((continuous_apply τ).comp (GlobalTheory.FockCompare.continuous_pi' h.inf T S))
  have hl : Function.LeftInverse (fockInv θ A B) (fockPt σ A B) := fun z => fockInv_fockPt h A B z
  have hr : Set.range (fockPt σ A B) = {w | fockPt σ A B (fockInv θ A B w) = w} := by
    ext w
    constructor
    · rintro ⟨z, rfl⟩
      exact congrArg (fockPt σ A B) (hl z)
    · intro hw
      exact ⟨_, hw⟩
  have hme : MeasurableEmbedding (fockPt σ A B) :=
    MeasurableEmbedding.of_measurable_inverse hc.measurable
      (by rw [hr]; exact (isClosed_eq (hc.comp hic) continuous_id).measurableSet) hic.measurable hl
  refine ⟨hc, fun w hw => ⟨_, fockPt_fockInv h A B hw⟩, fun g hg => ?_⟩
  haveI : SigmaFinite (volume : Measure (Fin S.rank → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin T.rank → Fin S.rank → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (VCx D.what₂.Tau S.rank T.rank)) := inferInstance
  refine ⟨Measure.map (fockPt σ A B) volume, g ∘ fockInv θ A B, MeasureTheory.Measure.instSFiniteMap _ _, ?_, fun H => ?_⟩
  · rw [hme.integrable_map_iff]
    have e : (g ∘ fockInv θ A B) ∘ fockPt σ A B = g := funext fun z => congrArg g (hl z)
    rw [e]; exact hg
  · rw [hme.integral_map]
    simp only [Function.comp_apply, hl _]

end GlobalTheory.FockTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockRealPointTransportContinuousIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockRealPoint_transport_continuous_integral : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T), Continuous (fockPt σ A B) ∧ (∀ w : WO S T, w.map (finPart D) = 0 → ∃ z, fockPt σ A B z = w) ∧ ∀ g : VCx D.what₂.Tau S.rank T.rank → ℂ, Integrable g → ∃ (m : Measure (WO S T)) (α : WO S T → ℂ), SFinite m ∧ Integrable α m ∧ ∀ H : WO S T → ℂ, ∫ w, α w * H w ∂m = ∫ z, g z * H (fockPt σ A B z) := by
  first | exact @GlobalTheory.FockTransport.fockPt_transport | exact GlobalTheory.FockTransport.fockPt_transport | (intros; apply GlobalTheory.FockTransport.fockPt_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPoincareSumOverRationalHomBump
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPoincareSumOverRationalHomBump
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.SepRows GlobalTheory.Asc
open GlobalTheory.FunObj hiding Frames
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

namespace GlobalTheory.BumpMix

theorem finite_rat_mem_of_isCompact {D : D7} {m n : ℕ} (K : Set (Mx D m n)) (hK : IsCompact K) :
    {γ : Matrix (Fin m) (Fin n) D.host.E | rat γ ∈ K}.Finite := by
  obtain ⟨hg, -, -, ht2, hdisc, -⟩ := lattice_Mx D m n
  haveI : IsTopologicalAddGroup (Mx D m n) := hg
  haveI : T2Space (Mx D m n) := ht2
  haveI : T1Space (Mx D m n) := @T2Space.t1Space _ _ ht2
  haveI : DiscreteTopology (ratMx D m n) := hdisc
  have hcl : IsClosed (ratMx D m n : Set (Mx D m n)) := AddSubgroup.isClosed_of_discrete
  have hS : IsCompact ((Subtype.val : ratMx D m n → Mx D m n) ⁻¹' K) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hfin := (hS.finite_of_discrete.image Subtype.val).preimage (rat_injective (D := D) (m := m) (n := n)).injOn
  refine hfin.subset fun γ hγ => ?_
  exact ⟨⟨rat γ, rat_mem γ⟩, hγ, rfl⟩

theorem poinX_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → Continuous (poinX ψ d T β) := by
  intro D ψ hψ S S₀ T ρ d β hβ
  obtain ⟨hg, hlc, -, -, -, -⟩ := lattice_Mx D T.rank S.rank
  haveI : IsTopologicalAddGroup (WO S T) := hg
  haveI : LocallyCompactSpace (WO S T) := hlc
  obtain ⟨hg', -, -, -, -, -⟩ := lattice_Mx D T.rank ρ
  haveI : IsTopologicalAddGroup (Mx D T.rank ρ) := hg'
  haveI : ContinuousSub (Mx D T.rank ρ) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hg'
  have hjX : Continuous fun u : WO S T => u ⬝ d.jX := Continuous.matrix_mul (A := fun u : WO S T => u) continuous_id continuous_const
  have hjY : Continuous fun u : WO S T => u ⬝ d.jY := Continuous.matrix_mul (A := fun u : WO S T => u) continuous_id continuous_const
  have hterm : ∀ γ : Matrix (Fin T.rank) (Fin ρ) D.host.E, Continuous fun u : WO S T =>
      ψ (trHalf D (pairS T (u ⬝ d.jX + 2 • rat γ) (u ⬝ d.jY))) * β (u ⬝ d.jX + rat γ) := by
    intro γ
    have e : (fun u : WO S T => trHalf D (pairS T (u ⬝ d.jX + 2 • rat γ) (u ⬝ d.jY))) =
        fun u : WO S T => symplOH S T (d.extX T (u ⬝ d.jX + 2 • rat γ)) (d.extY T (u ⬝ d.jY)) :=
      funext fun u => (d.symplOH_extX_extY T _ _).symm
    have hc : Continuous fun u : WO S T => trHalf D (pairS T (u ⬝ d.jX + 2 • rat γ) (u ⬝ d.jY)) := by
      rw [e]
      refine GlobalTheory.OrientedHeis.continuous_symplOH ?_ ?_
      · simp only [HypDec.extX_apply]
        exact (hjX.add continuous_const).matrix_mul continuous_const
      · simp only [HypDec.extY_apply]
        exact hjY.matrix_mul continuous_const
    exact (hψ.1.1.comp hc).mul (hβ.cont.comp (hjX.add continuous_const))
  refine continuous_iff_continuousAt.2 fun u₀ => ?_
  obtain ⟨U, hU, hUn⟩ := exists_compact_mem_nhds u₀
  have hK : IsCompact ((fun p : Mx D T.rank ρ × WO S T => p.1 - p.2 ⬝ d.jX) '' (tsupport β ×ˢ U)) :=
    (hβ.supp.isCompact.prod hU).image (continuous_fst.sub (Continuous.matrix_mul (A := fun p : Mx D T.rank ρ × WO S T => p.2) continuous_snd continuous_const))
  have hF := finite_rat_mem_of_isCompact _ hK
  have vanish : ∀ u ∈ U, ∀ γ, γ ∉ hF.toFinset → β (u ⬝ d.jX + rat γ) = 0 := by
    intro u hu γ hγ
    by_contra hne
    exact hγ (hF.mem_toFinset.2 ⟨(u ⬝ d.jX + rat γ, u), ⟨subset_tsupport β hne, hu⟩, add_sub_cancel_left _ _⟩)
  refine (continuous_finsetSum hF.toFinset fun γ _ => hterm γ).continuousAt.congr
    (Filter.eventually_of_mem hUn fun u hu => ?_)
  show _ = poinX ψ d T β u
  unfold poinX
  refine (tsum_eq_sum fun γ hγ => ?_).symm
  rw [vanish u hu γ hγ, mul_zero]

end GlobalTheory.BumpMix

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPoincareSumOverRationalHomBumpStatement
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.SepRows GlobalTheory.Asc
open GlobalTheory.FunObj hiding Frames
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_poincareSumOverRationalHom_bump : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → Continuous (poinX ψ d T β) := by
  first | exact @GlobalTheory.BumpMix.poinX_continuous | exact GlobalTheory.BumpMix.poinX_continuous | (intros; apply GlobalTheory.BumpMix.poinX_continuous <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionUnipotentLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionUnipotentLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc GlobalTheory.Unf.FB GlobalTheory.Unf.FB.ThLaws

noncomputable section

namespace GlobalTheory.Unf.FB.ThLawsL

variable {D : D7}

theorem zEll_rat {σ : ℕ} (B : BesL D σ) :
    ∃ z0 : Matrix (Fin B.L.rank) (Fin (σ + 1)) D.host.E, zEll B.L (σ + 1) B.ζ = rat z0 := by
  refine ⟨Matrix.vecMulVec B.ζ (fun i : Fin (σ + 1) => if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0), ?_⟩
  funext i j
  simp only [zEll, rat, Matrix.map_apply, Matrix.vecMulVec_apply, ell, map_mul, ratV]
  congr 1
  split_ifs <;> simp

theorem th_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (y : WO J.W₀ B.L → ℂ), GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → Continuous (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) ∧ (∃ M : ℝ, (∀ w, ‖y w‖ ≤ M) ∧ ∀ n, ‖(fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) n‖ ≤ M) ∧ (∀ γ ∈ flagN J.d, γ ∈ GQ J.W → ∀ n ∈ flagN J.d, (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (γ * n) = (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) n) ∧ (∀ c, ∀ n ∈ flagN J.d, (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (J.d.nC c * n) = star (ψ (J.d.qS B.L c (zEll B.L (σ + 1) B.ζ))) * (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) n) ∧ (∀ n ∈ flagN J.d, ∀ u ∈ UX D (σ + 1), (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (n * J.d.levi u) = (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) n * star (psiUni ψ u)) ∧ ∀ b, ∀ u ∈ UX D (σ + 1), (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (J.d.nB b * J.d.levi u) = star (psiUni ψ u) * star (y (zEll B.L (σ + 1) B.ζ ⬝ b)) := by
  intro D ψ hψs σ J B y hy
  have hψ : IsCharAF D.host.F ψ := hψs.1
  have hx : ∀ u ∈ UX D (σ + 1), zEll B.L (σ + 1) B.ζ ⬝ u.1 = zEll B.L (σ + 1) B.ζ := fun u hu => zEll_mul B.L B.ζ hu
  obtain ⟨hcen, hmul, hlevi, -⟩ := GlobalTheory.JacHom.jacS_hom D ψ J.W J.W₀ B.L (σ + 1) J.d (zEll B.L (σ + 1) B.ζ) hx
  obtain ⟨M, hM⟩ := exists_bound_quasi hψ hy
  have hval : ∀ n, star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n) =
      star (ψ (cenS J.d B.L (zEll B.L (σ + 1) B.ζ) n) * y (ptS J.d B.L (zEll B.L (σ + 1) B.ζ) n)) * star (psiFlag ψ J.d n) := fun n => by
    rw [jacS_zero_apply]
  have hnorm : ∀ a, ‖ψ a‖ = 1 := hψ.2.1
  have hflag1 : ∀ n, ‖psiFlag ψ J.d n‖ = 1 := fun n => hnorm _
  refine ⟨?_, ⟨M, hM, fun n => ?_⟩, ?_, ?_, ?_, ?_⟩
  · have e : (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) = fun n =>
        star (ψ (cenS J.d B.L (zEll B.L (σ + 1) B.ζ) n) * y (ptS J.d B.L (zEll B.L (σ + 1) B.ζ) n)) * star (psiFlag ψ J.d n) := funext hval
    rw [e]
    exact (((hψ.1.comp (continuous_cenS _ _ _)).mul (hy.2.comp (continuous_ptS _ _ _))).star).mul
      (continuous_psiFlag hψ.1 _).star
  · show ‖star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)‖ ≤ M
    rw [hval, norm_mul, norm_star, norm_star, norm_mul, hnorm, hflag1, one_mul, mul_one]
    exact hM _
  · intro γ hγN hγQ n hn
    obtain ⟨z0, hz0⟩ := zEll_rat B
    have hp := hmul γ hγN n hn
    obtain ⟨g0, hg0⟩ := ptS_rat J.d B.L z0 hγQ
    rw [← hz0] at hg0
    have hc : ψ (cenS J.d B.L (zEll B.L (σ + 1) B.ζ) γ) = 1 := by rw [hz0]; exact psi_cenS_rat hψ J.d B.L z0 hγQ
    show star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (γ * n) y 0) * star (psiFlag ψ J.d (γ * n)) =
      star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)
    rw [hval, hval, hp.1, hp.2.1, psiFlag_mul J.d ψ hγN hn, psiFlag_rat hψ J.d hγQ, one_mul, hg0, hy.1 g0]
    congr 2
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel_right, AddChar.map_add_eq_mul, hc, one_mul]
  · intro c n hn
    have hc : J.d.nC c ∈ flagN J.d := J.d.nC_mem_NFlag c
    show star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.nC c * n) y 0) * star (psiFlag ψ J.d (J.d.nC c * n)) =
      _ * (star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n))
    rw [(hmul _ hc n hn).2.2, psiFlag_mul J.d ψ hc hn, psiFlag_nC, jacS_nC]
    simp only [Pi.smul_apply, smul_eq_mul, star_mul', one_mul, star_one]
    ring
  · intro n hn u hu
    have hl : J.d.levi u ∈ flagN J.d := J.d.levi_mem_NFlag hu
    show star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (n * J.d.levi u) y 0) * star (psiFlag ψ J.d (n * J.d.levi u)) =
      star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n) * _
    rw [hlevi n hn u hu, psiFlag_mul J.d ψ hn hl, psiFlag_levi, star_mul', mul_assoc]
  · intro b u hu
    have hb : J.d.nB b ∈ flagN J.d := J.d.nB_mem_NFlag b
    have hl : J.d.levi u ∈ flagN J.d := J.d.levi_mem_NFlag hu
    have hp : ptS J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.nB b) = zEll B.L (σ + 1) B.ζ ⬝ b := by
      have := ptS_nB_mul_nC J.d B.L (zEll B.L (σ + 1) B.ζ) b 0
      rwa [J.d.nC_zero, mul_one] at this
    have hc : cenS J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.nB b) = 0 := by
      have := hcen b 0
      rw [J.d.nC_zero, mul_one] at this
      rw [this, HypDec.qS]
      simp [GlobalTheory.MixModel.symplOH_zero_right]
    show star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.nB b * J.d.levi u) y 0) * star (psiFlag ψ J.d (J.d.nB b * J.d.levi u)) = _
    rw [hlevi _ hb u hu, psiFlag_mul J.d ψ hb hl, jacS_zero_apply, hp, hc, AddChar.map_zero_eq_one, one_mul,
      psiFlag_nB, one_mul, psiFlag_levi]
    ring

end GlobalTheory.Unf.FB.ThLawsL

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionUnipotentLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobiActionUnipotent_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (y : WO J.W₀ B.L → ℂ), GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → Continuous (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) ∧ (∃ M : ℝ, (∀ w, ‖y w‖ ≤ M) ∧ ∀ n, ‖(fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) n‖ ≤ M) ∧ (∀ γ ∈ flagN J.d, γ ∈ GQ J.W → ∀ n ∈ flagN J.d, (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (γ * n) = (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) n) ∧ (∀ c, ∀ n ∈ flagN J.d, (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (J.d.nC c * n) = star (ψ (J.d.qS B.L c (zEll B.L (σ + 1) B.ζ))) * (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) n) ∧ (∀ n ∈ flagN J.d, ∀ u ∈ UX D (σ + 1), (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (n * J.d.levi u) = (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) n * star (psiUni ψ u)) ∧ ∀ b, ∀ u ∈ UX D (σ + 1), (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (J.d.nB b * J.d.levi u) = star (psiUni ψ u) * star (y (zEll B.L (σ + 1) B.ζ ⬝ b)) := by
  first | exact @GlobalTheory.Unf.FB.ThLawsL.th_laws | exact GlobalTheory.Unf.FB.ThLawsL.th_laws | (intros; apply GlobalTheory.Unf.FB.ThLawsL.th_laws <;> assumption)
end
end

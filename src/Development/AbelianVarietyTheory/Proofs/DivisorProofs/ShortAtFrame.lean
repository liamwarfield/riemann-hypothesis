module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfRhoEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelClassScalarIntegralStandard

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortValueAtPoint
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section

namespace GlobalTheory.ShortPtVal


set_option maxHeartbeats 2000000 in
theorem short_value_at_point : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (χ : (AE D)ˣ →* Circle) (c0' : ℂ), (∀ (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))) (k : GA D (Wc D i)) (xk : (AE D)ˣ) (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), GlobalTheory.AdTh.IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → GlobalTheory.ThFr.IsSympl X bas → GlobalTheory.AdTh.IdxIs T.Q.c (O i).s0 X idx e → GlobalTheory.AdTh.latR (rank_Wc i) (latG (Wc D i) k) = X.Λ → IsDetRoot (Wc D i) k xk → GlobalTheory.Dict.IsMark (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ X.Λ mk → GlobalTheory.AdTh.MarkAd (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ (Wc D i) (rank_Wc i) (iotaW T.J i) k mk → letI : Algebra (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ := ((O i).s0.comp ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F →+* T.Q.c.F)).toAlgebra; ∀ (y₂ : FrPt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).Xo₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ ℂ) (A₂ : GlobalTheory.Dict.AnFib X bas idx e (GlobalTheory.AdTh.frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.J.x₀ ((i : ℕ) + 1) (O i).s0 τ.1)) X.Λ y₂), A₂.Marked mk → evR (T.dδ ((i : ℕ) + 1) (Vc D i).rank).Xo₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).cδ y₂ = c0' * ((χ xk : Circle) : ℂ)) → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → ∀ (ζ : ℂ) (φc : (Fin (Vc D i).rank → LevQc (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) → ℂ), ζ ≠ 0 → GlobalTheory.AdTh.hatC (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ φc = (fun q => ζ * (O i).s0 ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).w x₀ q))) → ∀ (F₀ : Rul (T.Q.Xo ((i : ℕ) + 1)) T.Q.c), IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x₀ P F₀ → ∀ (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r) (g' : ℕ) (Dc : GlobalTheory.Dict.Dic (T.Q.Dw ((i : ℕ) + 1)) T.Q.c (O i).s0 X g' (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i))) (k : GA D (Wc D i)) (xk : (AE D)ˣ), IsDetRoot (Wc D i) k xk → GlobalTheory.AdTh.IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → GlobalTheory.AdTh.latR (rank_Wc i) (latG (Wc D i) k) = X.Λ → GlobalTheory.SW.SelfD X X.Λ → ∀ (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ D.R.r), x ∈ X.dom → x = GlobalTheory.AdTh.frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.J.x₀ ((i : ℕ) + 1) (O i).s0 τ.1) → ∀ (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), GlobalTheory.Dict.IsMark T.Q.l X.Λ mk → GlobalTheory.AdTh.MarkAd T.Q.l (Wc D i) (rank_Wc i) (iotaW T.J i) k mk → ∀ (v : GlobalTheory.SW.TF (Vc D i).rank g') (ϑ : (Fin g' → ℂ) → ℂ) (κ' : ℂ), GlobalTheory.SW.IsVac X Dc.bas (T.Q.H.w0 : D.host.E) (GlobalTheory.SW.tens (GlobalTheory.SW.stdL D.host.E (Vc D i).rank) X.Λ) v → (∀ z : Fin (Vc D i).rank → Fin g' → ℂ, ∏ b, ϑ (z b) = κ' * GlobalTheory.SW.thA X Dc.bas Dc.idx v x z) → letI : Algebra T.Q.c.F ℂ := (O i).s0.toAlgebra; ∀ (y : FrPt (T.Q.Xo ((i : ℕ) + 1)) T.Q.c ℂ) (B : GlobalTheory.Dict.AnFib X Dc.bas Dc.idx Dc.e x X.Λ y), B.Marked mk → B.Reads 1 y.s ϑ → ∃ (mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) (Y : (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E), GlobalTheory.Dict.IsMark (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ X.Λ mk₂ ∧ GlobalTheory.AdTh.MarkAd (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ (Wc D i) (rank_Wc i) (iotaW T.J i) k mk₂ ∧ GlobalTheory.Dict.IsRoots (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ X.Λ mk₂ N Y ∧ evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c F₀ y = c0' * ((χ xk : Circle) : ℂ) * ((((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * ((Λ.mIdx N D.R.r : ℂ))⁻¹ * ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) : ℂ))⁻¹ * (Λ.zCard N D.R.r : ℂ)) * κ' * ζ⁻¹ * GlobalTheory.SW.thP X Dc.hr Dc.bas Dc.idx (GlobalTheory.Dict.gphi X Dc.bas (T.Q.H.w0 : D.host.E) Λ.La X.Λ v (GlobalTheory.AdTh.hatC (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ φc) Y) (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)) x) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hpins χ c0' hcov Λ N x₀ P hUn hTb hTl hLev hAdm hP ζ φc hζ hhat F₀ hF₀
    X g' Dc k xk hk hX hp hΛ hsd x hx hxk mk hm hma v ϑ κ' hv hκ
  intro y B hB hϑ
  subst hxk
  letI : Algebra T.Q.c.F ℂ := (O i).s0.toAlgebra
  letI : Algebra (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ :=
    ((O i).s0.comp ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm :
      (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F →+* T.Q.c.F)).toAlgebra
  have hj := inR i
  have halg : ∀ t : T.Q.c.F, algebraMap (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ
      ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF t) = algebraMap T.Q.c.F ℂ t := fun t => rfl
  have hTie : TieIn T.J R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hs : (O i).s0 = T.J.toCore.σ₀ := sOv_eq _ _ _
  have hσ : GoodEmb T.J.Q.c (O i).s0 := hs ▸ T.J.toCore.good_σ₀
  have hmod := GlobalTheory.AdTh.models_at_record_core D G Pl0 T0 A T.J R F κ v₀ hC hTie i (O i).s0 hs
  obtain ⟨-, -, -, -, hrk, hpq, -, -, -, -, hD, -⟩ := hmod ((O i).dict k).1
  obtain ⟨hemb, -, -, -⟩ := GlobalTheory.PtId.dict_cast T.J hT.j _ hj (O i).s0 hσ (Wc D i) (O i).hV (rank_Wc i)
  have hlev := hT.sh.dLev _ hj (Vc D i).rank
  have hA₂ := hT.lvA _ hj (Vc D i).rank
  have hA : T.Q.l.A = 1 := hT.j.pins.2.1.2
  obtain ⟨mk₂, hm₂, ha₂, hov⟩ := GlobalTheory.AdMark.exists_marking D _ _ T.Q.l (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ (Wc D i) _
    (rank_Wc i) (iotaW T.J i) hemb (hlev.2.1 ▸ dvd_mul_right _ _) (hlev.2.2.2.1 ▸ Ideal.mul_le_left) k
  rw [hΛ] at hm₂ hov
  have hM : 0 < (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M := lt_of_lt_of_le (by norm_num) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.three_le
  obtain ⟨Y, hY⟩ := (GlobalTheory.Dict.DualMark.dual_marking _ _ _ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ _ _ _ mk₂ _ hsd hm₂
    (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 (Vc D i).rank N hLev.1.pos
  refine ⟨mk₂, Y, hm₂, ha₂, hY, ?_⟩
  obtain ⟨y₂, B₂, hov₂, hB₂, hrd⟩ := GlobalTheory.Dict.MarkLift.exists_lift_marked _ _ _ _ _ T.Q.c _
    (T.dδ ((i : ℕ) + 1) (Vc D i).rank) halg hlev hA hA₂ (fun e0 => absurd e0 hpq) _ g' X Dc.bas Dc.idx Dc.e _ X.Λ y B
    Dc.sympl hx hsd mk mk₂ hm hB hm₂ (hov mk hm.mem hma)
  obtain ⟨vv, hvv, hev⟩ := hF₀ ℂ halg y y₂ hov₂
  obtain ⟨_, hnab'⟩ := hT.sh.dNab _ hj (Vc D i).rank
  have hVset : Λ.La ∈ GlobalTheory.SW.Vset D.host.E (Vc D i).rank (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M :=
    (GlobalTheory.Dict.GenLatCmp.genLat_vset _ _ Λ.La).2.1 _ N hM hUn hTl hLev
  have hP2 := (GlobalTheory.admissible_columns_le_and_harmonic_map_cover _ _ _ _ _ _ _ (T.dδ ((i : ℕ) + 1) (Vc D i).rank)).2 (wtA (κ i)) _ hP.1
  have e1 := GlobalTheory.Dict.shortValAt_eq_thP GlobalTheory.ChartFree.chartIndep _ _ _ _ _ _ D.R.r g' X Dc.bas Dc.idx Dc.e _ X.Λ y₂ B₂
    Dc.sympl hx hsd _ (Vc D i).rank Dc.hr Dc.eL hrk hD.2 Dc.dir_eq _ hnab' ϑ v κ' (hrd ϑ hϑ) hv hκ mk₂ hm₂ hB₂
    Λ.La hVset N hLev Y hY (wtA (κ i)) _ hP2 _ _ vv hvv
  have hc := hcov X g' Dc.bas Dc.idx Dc.e k xk mk₂ hX hp Dc.sympl ⟨Dc.per_eq, Dc.ty_eq⟩ hΛ hk hm₂ ha₂ y₂ B₂ hB₂
  rw [hev, e1, hc]
  have hW : (fun q => algebraMap (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).w x₀ q)) =
      ζ⁻¹ • GlobalTheory.AdTh.hatC (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ φc := by
    funext q
    rw [hhat, Pi.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ hζ]
    rfl
  have hpoly : MvPolynomial.map (algebraMap (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ)
      (MvPolynomial.map ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF : T.Q.c.F →+* (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F) P) =
      MvPolynomial.map (O i).s0 P := by
    rw [MvPolynomial.map_map]
    congr 1
  have hg : ∀ (W : (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) → ℂ) (a : ℂ),
      GlobalTheory.Dict.gphi X Dc.bas (T.Q.H.w0 : D.host.E) Λ.La X.Λ v (a • W) Y =
        a • GlobalTheory.Dict.gphi X Dc.bas (T.Q.H.w0 : D.host.E) Λ.La X.Λ v W Y := fun W a => by
    simp only [GlobalTheory.Dict.gphi, Pi.smul_apply, smul_eq_mul, mul_smul]
    rw [smul_finsum]
  have hs0 : ∀ t : T.Q.c.F, algebraMap T.Q.c.F ℂ t = (O i).s0 t := fun t => rfl
  rw [hW, hpoly, hg, GlobalTheory.Dict.ShortPt.theta_smul₂]
  simp only [map_mul, map_inv₀, map_natCast, halg, hs0]
  ring

end GlobalTheory.ShortPtVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SingleSeriesEqPhaseThetaKO
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
noncomputable section

namespace GlobalTheory.AdTh.VecSeries
open GlobalTheory.AdTh GlobalTheory.AdTh.PhaseMap


set_option maxHeartbeats 2000000 in
theorem singleSeries_eq_phase_thetaKO : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → IoExt R → ∀ (χ : (AE D)ˣ →* Circle) (ω : WeilRep D i), IsWeilTw R i χ ω → ∀ (Q : Finset (Pl D.host.E)) (Ω : DatFn D i) (φ' : WO (Vc D i) (Wc D i) → ℂ), VecOf R i Q Ω φ' → ∀ (ka : ℂ), GlobalTheory.PtId.IoAt (O i) (v₀ i (sg0 D A)) ka → ∀ (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (y : VsV D i (O i).c'.F), (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r) (g' : ℕ) (Dc : GlobalTheory.Dict.Dic (T.Q.Dw ((i : ℕ) + 1)) T.Q.c (O i).s0 X g' (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i))) (vr : GlobalTheory.Harm.Var X.Ψ (T.Q.Dw ((i : ℕ) + 1)).p X.p0 (Fin (Vc D i).rank) ≃ FVar D (Wc D i).rank (Vc D i).rank), GlobalTheory.AdTh.IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → GlobalTheory.AdTh.IsVarOf (Vc D i) (Wc D i) X (T.Q.Dw ((i : ℕ) + 1)).p vr → ∀ (h : GA D (Vc D i)) (w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → ∀ (g γ : GA D (Wc D i)), γ ∈ GQ (Wc D i) → singleSeries R i ω φ' h ((O i).c0' y) w g = ka * thetaKO ω h (γ * g) (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) φ' (MvPolynomial.rename vr (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)))) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hR i hOP hE χ ω hω Q Ω φ' hφ ka hka P y hy X g' Dc vr hM hp hv h w hw g γ hγ
  have hθ : IsInfFam R.θ := hR.models.inf
  have hstd := hOP.2.lift.std
  have hPr := (GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A _ R F hR i A.μ0 hstd).1
  have hψ := hPr.weil.std
  obtain ⟨f1, f2, f3, f4, f5⟩ := GlobalTheory.AdTh.VecFockCore.vec_fock_core D G Pl0 T0 A _ R F hR i A.μ0 hstd
  have hBV : ∀ τ, (R.BV i τ)ᴴ * R.BV i τ = 1 := fun τ => by
    obtain ⟨ε, hε, h1, -⟩ := hR.models.BV i τ
    rw [gramAt_one hPr.std, Matrix.mul_one] at h1
    rw [h1, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with h | h
    · rw [h.1]; rfl
    · exact absurd a.2 (not_lt.2 h.2)
  have hon : ∀ τ, IsONBasis (gramAt D (Vc D i) τ) 1 1 (Vc D i).rank := fun τ =>
    ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, by simp [gramAt_one hPr.std], by simp⟩

  have hthφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ' := by
    obtain ⟨⟨hψ', h0⟩, e, -, hth⟩ := hφ
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ' hθ hth h0.theta

  have hsub : ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ P',
      pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f P' =
        pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) f
          (MvPolynomial.aeval (fun k => ∑ b, MvPolynomial.C
              (if (k.2.1 : ℕ) < ((Wc D i).sig (tauE D k.1)).1 then (R.BV i k.1)⁻¹ k.2.2 b
                else (starRingEnd ℂ) ((R.BV i k.1)⁻¹ k.2.2 b)) * MvPolynomial.X (k.1, k.2.1, b)) P') := by
    intro f hf P'
    have h := GlobalTheory.AdTh.SourceBasis.pureTensorO_mul_source D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ (fun _ => 1) (R.BV i) _ _ _ f5
      (fun τ => (trace_parity (f5 τ)).1) (fun τ => by simp) (fun τ => det_ne_zero (hBV τ)) f hf P'
    simp only [Matrix.one_mul] at h
    exact h
  have hinj : Function.Injective (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (R.vP i A.μ0)) :=
    GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ _ _ _ _ _ _ f4 f3 hon f5 hPr.sigV hPr.sigW _ f1 f2
      (GlobalTheory.AdTh.VecNeCore.thetaVector_ne_zero_core D G Pl0 T0 A _ R F hR i hstd)

  have hlt : ∀ ℓ : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank, (vr (Dc.eL ℓ)).2.2 = ℓ.2.2 ∧
      ((ℓ.1 = tauE D (vr (Dc.eL ℓ)).1 ∧ ((vr (Dc.eL ℓ)).2.1 : ℕ) = ℓ.2.1) ∨
        (ℓ.1 = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (tauE D (vr (Dc.eL ℓ)).1) ∧
          ((vr (Dc.eL ℓ)).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1)) := by
    intro ℓ
    have hP := hT.j.pins
    have hm : ∀ τ, τ ∉ X.Ψ → (T.Q.Dw ((i : ℕ) + 1)).mult τ ≤ X.p0 := fun τ hτ => by
      unfold Datum.mult
      rw [if_neg fun h : τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 => hτ ((hM.psi τ).2
        (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hP.1 τ h)), hp]
    obtain ⟨h1, h2⟩ := GlobalTheory.AdTh.Dic.letter Dc (fun τ => RingHom.ext fun _ => rfl) hm ℓ
    obtain ⟨g1, g2, g3⟩ := hv (Dc.eL ℓ)
    refine ⟨g2.trans h1, ?_⟩
    rcases h2 with ⟨k, e1, e2, e3⟩ | ⟨k, e1, e2, e3⟩
    · rw [e1, Sum.elim_inl] at g3
      exact Or.inl ⟨e2.trans g1, g3.trans e3⟩
    · rw [e1, Sum.elim_inr] at g3
      exact Or.inr ⟨by rw [← g1]; exact e2, by rw [g3, e3]⟩

  have hio := hka (fun ℓ => vr (Dc.eL ℓ)) hlt w hw A.μ0 y
  have hpol : MvPolynomial.rename (fun ℓ => vr (Dc.eL ℓ)) (MvPolynomial.map (inC (O i).c') ((O i).io y)) =
      MvPolynomial.rename vr (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)) := by
    rw [hy, MvPolynomial.rename_rename]
    exact congrArg (MvPolynomial.rename _) (MvPolynomial.map_map _ _ _)

  have hS : (MvPolynomial.aeval (fun k => ∑ b, MvPolynomial.C
              (if (k.2.1 : ℕ) < ((Wc D i).sig (tauE D k.1)).1 then (R.BV i k.1)⁻¹ k.2.2 b
                else (starRingEnd ℂ) ((R.BV i k.1)⁻¹ k.2.2 b)) * MvPolynomial.X (k.1, k.2.1, b))) (R.ioP i (PiTensorProduct.tprod ℂ w) ((O i).c0' y)) =
      ka • MvPolynomial.rename vr (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)) := by
    apply hinj
    rw [map_smul, ← hsub _ f1, ← hpol]
    exact hio

  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i)
      (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) φ' (MvPolynomial.rename vr (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)))) :=
    GlobalTheory.FockTheta.ptStable D R.ψ R.θ hψ hθ _ _ _ _ _ _ φ' _ hthφ
  have hmove : ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → thetaKO ω h g f = thetaKO ω h (γ * g) f := fun f hf => by
    have e1 : ((h, γ * g) : GA D (Vc D i) × GA D (Wc D i)) = (1, γ) * (h, g) := by simp
    rw [thetaKO, thetaKO, e1, map_mul]
    exact (hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ f hf)).symm
  have hsm : ∀ k f, thetaKO ω h k (ka • f) = ka * thetaKO ω h k f := fun k f => by
    rw [thetaKO, thetaKO, map_smul]
    rfl
  show thetaKO ω h g (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i)
    (onb (R.MW i (sg0 D A))) φ' (R.ioP i (PiTensorProduct.tprod ℂ w) ((O i).c0' y))) = _
  rw [hsub _ hthφ, hS, map_smul, hsm, hmove _ hth]

end GlobalTheory.AdTh.VecSeries
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulEqOfHatCNeZeroOf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecOfEqSumHeis
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DatumFourierOnCmp

open GlobalTheory.DatumFourier


set_option maxHeartbeats 1600000 in
theorem vecOf_eq_sum_heis : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (χ : (AE D)ˣ →* Circle) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (Ω : GlobalTheory.OnCmp.DatFn D i) (ω : GlobalTheory.OnTies.WeilRep D i) (φv : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.OnCmp.IsWeilTw R i χ ω → Formalism.IndefR.Lev.IsTwistPlaces D.host.g Q → GlobalTheory.OnCmp.ReadsOnly (R.Pg ∪ Q) Ω → GlobalTheory.OnCmp.VecOf R i Q Ω φv → ∀ (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), GlobalTheory.OnCmp.PhiOf R i Q Ω ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ Q → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (R.Pg ∪ Q) → φv = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (Matrix.of fun a b => e * incA D (((δ : ℤ) : D.host.E) * ι (cSep l₂ • levRep (q b)) a / (l₂.M : D.host.E))) (R.vacP i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hI
  obtain ⟨ε, hε⟩ := hI
  refine ⟨ε, fun χ Q Ω ω φv _ _ hRO hVec l φ hφ hP e he => ?_⟩
  obtain ⟨hvac, e₁, he₁, hθ⟩ := hVec
  obtain ⟨e₂, he₂, hφ⟩ := hφ
  obtain rfl := idemSum_unique (Vc D i) he₁ he
  obtain rfl := idemSum_unique (Vc D i) he₂ he
  have hβV := hR.lev.βV i
  have hβW := hR.lev.βW i
  have hS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβV
  have hT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβW
  have hstd : R.ΛV i = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβV, ← GlobalTheory.SplitReps.hLat_one, hV.2]
  have hlat := mem_latRat_iff hV.1 hstd hβW
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hM' : (l.M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hsurj : ∀ M ∈ GlobalTheory.LatVac.latRat (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)), ∃ x : Fin (Vc D i).rank → Dw.La, M = Matrix.of fun a b => ι (x b) a := by
    intro M hM
    choose x hx using fun b => hι.2.ge ((hlat M).1 hM b)
    exact ⟨x, Matrix.ext fun a b => (congrFun (hx b) a).symm⟩
  have hint : ∀ u ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True),
      IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u)) := fun u hu =>
    int_of_mem_latO (fun M hM => by
      obtain ⟨x, rfl⟩ := hsurj M hM
      exact (hφ x).1) hu
  have : Finite (LevQ Dw l) := GlobalTheory.LevelPairing.finite_LevQ
  have := Fintype.ofFinite (Fin (Vc D i).rank → LevQ Dw l)
  rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
  simp only [smul_smul]
  refine thetaAt_eq_sum _ _ hθ (fun q a b => ?_) fun w => ?_
  · rw [GlobalTheory.LatVac.cA_cA, Matrix.of_apply, ← mul_assoc, GlobalTheory.PlaceVec.idemSum_mul_self he]
  by_cases hw : w ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True) ∧ IsHalf (cA D e) w
  swap
  · rw [halfInd, if_neg hw, zero_mul, if_neg]
    rintro ⟨h1, h2⟩
    have hN : ∀ PP ∈ R.Pg ∪ Q, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP h =>
      (hP PP (Finset.mem_union.1 hPP)).2 (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
    exact hw ⟨mem_latO_of_int hS hT hβV.choose_spec.1 hβW.choose_spec.1 he (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D) hN h1 h2, h1⟩
  have hw' : cA D e • w = w := Matrix.ext hw.2
  obtain ⟨M, hM0, u, hu, hwM⟩ := approx_mod (Nat.pos_of_ne_zero hM) hw.1
  obtain ⟨x, rfl⟩ := hsurj M hM0
  have hfr : frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w =
      uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b)) +
        l.M • frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u) := by
    rw [← hw', hwM, smul_add, GlobalTheory.PlaceVec.frMapAdj_add, frMapAdj_half, smul_comm]
    congr 1
    · exact one_smul _ _
    · exact (AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add _ _ (R.βV i) (R.βW i))).map_nsmul _ _
  have hred : ∀ PP, PP ∈ R.Pg ∨ PP ∈ Q → redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) =
      redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b))) := fun PP hPP => by
    rw [hfr]
    have : Ideal.span {(l.M : 𝓞 D.host.E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact GlobalTheory.PlaceVec.redM_add_nsmul PP ((hP PP hPP).1 (this (Ideal.subset_span rfl))) (hφ x).1 (hint u hu)
  rw [halfInd, if_pos hw, one_mul, if_pos ⟨hw.2, hw' ▸ hint w hw.1⟩,
    hRO _ (fun PP => redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b))))
      (fun PP h => hred PP (Finset.mem_union.1 h)), ← (hφ x).2, ← inversion l φ x]
  refine Finset.sum_congr rfl fun q _ => congrArg _ ?_
  have hY : (Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E)) =
      Matrix.of fun a b => (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) * ι (cSep l • levRep (q b)) a :=
    Matrix.ext fun a b => by simp only [Matrix.of_apply]; ring
  refine Eq.trans ?_ (char_eq (Y := Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E))
    hvac.1 hS hT (GlobalTheory.PlaceVec.idemSum_infPart he) hw.2 hu hwM ((hlat _).2 fun b => ?_)).symm
  · rw [hY, hRat_std hV.1 _ _ _ (by rw [star_div₀, star_intCast, star_natCast]), ← Complex.exp_int_mul]
    congr 1
    have h1 : ∀ c : ℚ, ∀ z : D.host.E, Algebra.trace ℚ D.host.E (D.host.xi0 * ((c : D.host.E) * z)) =
        c * Algebra.trace ℚ D.host.E (D.host.xi0 * z) := fun c z => by
      rw [mul_left_comm, ← Rat.smul_def, map_smul, smul_eq_mul]
    have h2 : ∀ y z, Dw.EF y z = -Dw.EF z y := fun y z => (LinearMap.IsAlt.neg Dw.alt z y).symm
    have h3 : ((pairL (l := l) x (fun b => levRep (q b)) : ℤ) : ℚ) = -(((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 *
        ∑ b, (Wc D i).hT ((Wc D i).frame.equivFun.symm (ι (cSep l • levRep (q b)))) ((Wc D i).frame.equivFun.symm (ι (x b))))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [pairL, Int.cast_sum, Finset.mul_sum, map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => by rw [h2, Int.cast_neg, hε]
    have h4 := congrArg (fun z : ℚ => (z : ℂ)) h3
    rw [show (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) = ((((ε : ℤ) : ℚ) / (l.M : ℚ) : ℚ) : D.host.E) by push_cast; rfl, h1]
    push_cast at h4 ⊢
    rw [h4]
    ring
  · have h1 := hι.2.le (LinearMap.mem_range_self ι ((ε : ℤ) • cSep l • levRep (q b)))
    convert h1 using 1
    funext a
    rw [map_zsmul, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, mul_div_cancel₀ _ hM', Pi.smul_apply, zsmul_eq_mul]

end GlobalTheory.DatumFourierOnCmp

end
end

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.ShortSeriesTw
open GlobalTheory.AdTh.MovedDatum GlobalTheory.AdTh.ShortSeries

theorem smul_eq_of_hatC_ne_zero_of (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type)
    (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (i : Fin D.R.m) (H : Geo.Tor.Host D.host.E) (Dw : Datum H)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (Ω : GlobalTheory.OnCmp.DatFn D i) (hΩ : GlobalTheory.OnCmp.ReadsOnly (R.Pg ∪ Q) Ω) (l₂ : Geo.Tor.Level H)
    (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ) (hφ : GlobalTheory.OnCmp.PhiOf R i Q Ω ι (Mfr l₂ • ⊤) φ)
    (q : Fin (Vc D i).rank → LevQ Dw l₂) (hq : hatC l₂ φ q ≠ 0) (s : 𝓞 D.host.E)
    (hs : ∀ PP ∈ R.Pg ∪ Q, s ∈ PP.asIdeal) (b : Fin (Vc D i).rank) :
    ∃ z : Dw.La, s • (cSep l₂ • levRep (q b)) = l₂.M • z := by
  obtain ⟨e, -, he⟩ := hφ
  have hM : l₂.M ≠ 0 := by have := l₂.three_le; omega
  have hdvd : ∀ w : Dw.La, (l₂.M : ℤ) ∣ Dw.EF w (s • (cSep l₂ • levRep (q b))) := by
    intro w
    have h1 := GlobalTheory.HatInt.dvd_of_invariant l₂ φ q hq (fun b' => H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b') (by
      intro x
      obtain ⟨x, rfl⟩ : ∃ x' : Fin (Vc D i).rank → Dw.La, x = fun b => Submodule.Quotient.mk (x' b) :=
        ⟨fun b => qRep (x b), funext fun b => (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (x b))).symm⟩
      have e1 := (he (fun b' => x b' + H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b')).2
      have e2 := (he x).2
      have e3 : ∀ PP ∈ R.Pg ∪ Q,
          Datum.redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e
            fun b' => ι (x b' + H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b')) =
          Datum.redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b' => ι (x b')) := by
        intro PP hP
        have e4 : (fun b' => ι (x b' + H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b')) =
            fun b' => ι (x b') + ((H.bar s : 𝓞 D.host.E) : D.host.E) •
              ι ((Pi.single b w : Fin (Vc D i).rank → Dw.La) b') := by
          funext b'
          rw [map_add (f := _), map_smul]
          rfl
        rw [e4, GlobalTheory.HatInt.uMat_add_smul, GlobalTheory.HatInt.sig_bar]
        exact GlobalTheory.HatInt.redM_add_smul PP _ _ (he x).1 (he _).1 s (hs PP hP)
      rw [hΩ _ _ e3, ← e2] at e1
      exact e1)
    unfold Formalism.L2.Pj.pairL at h1
    rw [Finset.sum_eq_single b] at h1
    · simpa [Dw.adj, LevelPairing.bar_bar] using h1
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · simp
  obtain ⟨z, hz⟩ := LevelPairing.exists_eq_smul_of_dvd (s • (cSep l₂ • levRep (q b))) l₂.M hM (fun y => by
    have h2 := Dw.alt (y + s • (cSep l₂ • levRep (q b)))
    simp only [map_add (f := _), LinearMap.add_apply, Dw.alt, zero_add, add_zero] at h2
    have h3 := hdvd y
    have : Dw.EF (s • (cSep l₂ • levRep (q b))) y = -Dw.EF y (s • (cSep l₂ • levRep (q b))) := by linarith
    rw [this]; exact h3.neg_right)
  exact ⟨z, by rw [hz, natCast_zsmul]⟩

theorem isPair_tw (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type)
    (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A) (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (hV : VStd D i)
    (χ : (AE D)ˣ →* Circle) (ω : GlobalTheory.OnTies.WeilRep D i) (hω : GlobalTheory.OnCmp.IsWeilTw R i χ ω)
    (ξ : Formalism.L2.Host.HChar D.host.E) (hchr : ChrEq χ ξ) (hfin : ∃ n : ℕ, 0 < n ∧ ξ.OrderDvd n)
    (Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (hram : ∀ PP, ¬ ξ.UnrAt PP ↔ PP ∈ Q ∨ ∃ PP' ∈ Q, Formalism.IndefR.Lev.IsConjPl PP' PP)
    (e : AE D) (he : IsIdemSum e (R.Pg ∪ Q)) :
    IsPair R.ψ R.θ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ω := by
  have hL := hC.lev
  have hW : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ω := hω
  have hr : Odd D.R.r := by
    have := D.R.m_add_three_le_k
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hev : Even (Vc D i).rank := rV ▸ hr.add_odd D.R.t_odd
  have hη : GlobalTheory.WeilParts.IsEtaTilde D R.eta :=
    GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hL.eta R.C.isEta _ _ _ hW.resS hW.resT (hev.add_odd (rW ▸ hr))
  have hexp : ∀ τ, ∃ a : ℤ, HasInfExp D (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).1 τ a := fun τ => by
    have h1 : HasInfExp D (R.mu0 ((i : ℕ) + 1)) τ (-(D.hc τ).e i) := by
      obtain ⟨n, hn, hi⟩ := (R.C.isMu0 i).inf
      refine GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => -(D.hc τ).e i) (hL.mu0 i)
        ⟨fun τ => n (D.eTau τ), fun τ => ?_, fun k => ?_⟩ τ
      · simp only [hn, Formalism.L2.Host.eExp, Equiv.symm_apply_apply]
      · rw [hi k]
        exact (Equiv.prod_comp D.eTau (fun g => (Formalism.L2.Host.embPsi D.host g (k : D.host.E) /
          ((‖Formalism.L2.Host.embPsi D.host g (k : D.host.E)‖ : ℝ) : ℂ)) ^ n g)).symm
    have h2 : HasInfExp D χ τ 0 := by
      obtain ⟨n, hn, ho⟩ := hfin
      have := D.host.isCMField_hostE
      refine GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun _ => 0) hchr ⟨fun _ => 0, fun _ => by norm_num, fun k => ?_⟩ τ
      rw [GlobalTheory.TypeValues.inf_eq_one _ hn ho k]
      simp
    obtain ⟨z, hz⟩ := (D.hc τ).e_int i
    refine ⟨-z, ?_⟩
    have h3 := GlobalTheory.Mem.HeckeExp.hasInfExp_mul h1 h2
    rw [hz, add_zero, ← Int.cast_neg] at h3
    exact h3
  refine ⟨hW, hC.models.inf, hV.1, hev, D.sp.V_sig _, D.sp.W_sig _, hexp, fun τ => ?_, fun v ε hv => ?_, ⟨_, hη⟩⟩
  · obtain ⟨a, ha⟩ := hexp τ
    obtain ⟨s, hs⟩ := hr
    refine ⟨a - s - 1, ?_⟩
    have h3 := GlobalTheory.Mem.HeckeExp.hasInfExp_mul ha (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hη.2.2.2 τ))
    have e : ((a - s - 1 : ℤ) : ℚ) + ((Wc D i).rank : ℚ) / 2 = (a : ℚ) + -(1 / 2) := by
      rw [rW, hs]; push_cast; ring
    rw [e]
    exact h3
  · obtain ⟨⟨es, hes, -⟩, -⟩ := he
    have hne : ∀ PP ∈ R.Pg ∪ Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v := fun PP hPP =>
      GlobalTheory.AdTh.RecPair.under_ne (hes PP hPP) hv
    have kx : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v → ξ.UnrAt P := fun P hP => by
      by_contra hc
      rcases (hram P).1 hc with h' | ⟨PP', h', hc'⟩
      · exact hne P (Finset.mem_union_right _ h') hP
      · exact hne PP' (Finset.mem_union_right _ h') ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc').trans hP)
    have km : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v → (R.C.mu0 i).UnrAt P := fun P hP => by
      refine (R.C.isMu0 i).unr P fun k hk => ?_
      rcases GlobalTheory.LevelPlaces.div_or_div_conj R.C.P k P hk with h | h
      · exact hne P (Finset.mem_union_left _ ((hL.Pg P).2 ⟨k, h⟩)) hP
      · exact hne _ (Finset.mem_union_left _ ((hL.Pg _).2 ⟨k, h⟩))
          ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl (GlobalTheory.LevelPlaces.isConjPl_conjSpec P)).symm.trans hP)
    have u1 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.mu0 i) v ε hv.1 km
    have u2 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ hchr v ε hv.1 kx
    have u3 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ hL.eta v ε hv.1 fun P _ => R.C.isEta.unr P
    have u4 : GlobalTheory.WeilParts.UnramAt ε (Lift.tup R.mu0 χ ((i : ℕ) + 1)) := fun x a b c => by
      show R.mu0 ((i : ℕ) + 1) x * χ x = 1
      rw [u1 x a b c, u2 x a b c, one_mul]
    refine ⟨u4, fun x a b c => ?_⟩
    show Lift.tup R.mu0 χ ((i : ℕ) + 1) x * (R.eta x)⁻¹ = 1
    rw [u4 x a b c, u3 x a b c, inv_one, one_mul]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem moved_datum_tw : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (χ : (AE D)ˣ →* Circle) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (Ω : GlobalTheory.OnCmp.DatFn D i) (ω : GlobalTheory.OnTies.WeilRep D i) (φv : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.OnCmp.IsWeilTw R i χ ω → ∀ (ξ : Formalism.L2.Host.HChar D.host.E), ChrEq χ ξ → (∃ n : ℕ, 0 < n ∧ ξ.OrderDvd n) → (∀ PP, ¬ ξ.UnrAt PP ↔ PP ∈ Q ∨ ∃ PP' ∈ Q, Formalism.IndefR.Lev.IsConjPl PP' PP) → Formalism.IndefR.Lev.IsTwistPlaces D.host.g Q → GlobalTheory.OnCmp.ReadsOnly (R.Pg ∪ Q) Ω → GlobalTheory.OnCmp.VecOf R i Q Ω φv → ∀ (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), GlobalTheory.OnCmp.PhiOf R i Q Ω ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ Q → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ (bad N : ℕ) (h : GA D (Vc D i)) (k : GA D (Wc D i)) (Λ : GenLat D.host.E (Vc D i).rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), (∀ PP, PP ∈ R.Pg ∨ PP ∈ Q → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → SplitOffBad (Vc D i) bad h → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ (Wc D i) (rank_Wc i) ι k mk → ∀ (Y : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E) (γ : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (u : (Fin (Vc D i).rank → LevQ Dw l₂) → WO (Vc D i) (Wc D i)), IsRoots l₂ (latR (rank_Wc i) (latG (Wc D i) k)) mk N Y → (∀ q, colsR (rank_Wc i) (γ q) = (δ : ℤ) • Y q ∧ IsFinOf (Vc D i) (Wc D i) (γ q) (u q)) → ω (h, k) φv = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (u q) (ω (h, k) (R.vacP i)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hiso
  obtain ⟨δ, hδ⟩ := GlobalTheory.DatumFourierOnCmp.vecOf_eq_sum_heis D G Pl0 T0 A Ks R F hR i hV H Dw ι hι hiso
  refine ⟨δ, fun χ Q Ω ω φv hω ξ hchr hfin hram hQ hΩ hvec l φ hφ hP bad N h k Λ mk hbad hh hΛ hT hL hmk Y γ u hY hu => ?_⟩
  obtain ⟨e, he, -⟩ := id hφ
  have hp := isPair_tw D G Pl0 T0 A Ks R F hR i hV χ ω hω ξ hchr hfin Q hram e he
  obtain ⟨-, -, a1, a2, a3, a4, a5⟩ := GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A Ks R F hR i A.μ0 hV
  obtain ⟨hψ, hvac⟩ := hvec.1
  rw [hδ χ Q Ω ω φv hω hQ hΩ hvec l φ hφ hP e he, map_smul]
  by_cases hfin' : Finite (Fin (Vc D i).rank → LevQ Dw l)
  swap
  · haveI := not_finite_iff_infinite.1 hfin'
    rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero, _root_.inv_zero, zero_smul, zero_smul]
  rw [map_finsum _ (Set.toFinite _)]
  congr 1
  refine finsum_congr fun q => ?_
  rw [map_smul]
  by_cases hq : hatC l φ q = 0
  · rw [hq, zero_smul, zero_smul]
  obtain ⟨c, hc, h1, h2⟩ := GlobalTheory.AdTh.MovedDatum.step R.ψ hψ (Vc D i) (Wc D i) hp.std (rank_Wc i) (R.ΛV i) (R.ΛW i) a1 a2 a3 a4 a5 l ι hι δ
    _ e he (fun PP hPP => ⟨(hP PP (Finset.mem_union.1 hPP)).1, fun h2 => (hP PP (Finset.mem_union.1 hPP)).2 (by
      obtain ⟨t, ht⟩ : 2 ∣ D.host.QS := (dvd_pow_self 2 (by omega)).trans D.host.tower_dvd
      rw [ht, mul_assoc, mul_assoc, Nat.cast_mul, Nat.cast_ofNat]; exact Ideal.mul_mem_right _ _ h2)⟩)
    bad N h k Λ mk (fun PP hPP => hbad PP (Finset.mem_union.1 hPP)) hh hΛ hT hL hmk Y hY q
    (fun s hs => smul_eq_of_hatC_ne_zero_of D G Pl0 T0 A Ks R i H Dw ι Q Ω hΩ l φ hφ q hq s hs)
    (γ q) (u q) (hu q).1 (hu q).2
  have h3 : heisO R.ψ (Vc D i) (Wc D i) (2 • actO (Vc D i) (Wc D i) h k c) (ω (h, k) (R.vacP i)) =
      ω (h, k) (R.vacP i) := by
    rw [← actO_two, ← hp.weil.om_heis h k _ _ hvac.theta, hvac.lat.1 c hc]
  have h4 := GlobalTheory.PlaceModel.heisL_heisL (Vc D i) (Wc D i) R.ψ _ _ (ω (h, k) (R.vacP i)) |>.trans
    (congrArg (· • _) h2)
  rw [one_smul, ← h1] at h4
  rw [hp.weil.om_heis h k _ _ hvac.theta]
  congr 1
  refine Eq.trans ?_ h4
  exact congrArg _ h3.symm


set_option maxHeartbeats 1000000 in
theorem thetaKO_eq_short_series_tw : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (χ : (AE D)ˣ →* Circle) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (Ω : GlobalTheory.OnCmp.DatFn D i) (ω : GlobalTheory.OnTies.WeilRep D i) (φv : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.OnCmp.IsWeilTw R i χ ω → ∀ (ξ : Formalism.L2.Host.HChar D.host.E), ChrEq χ ξ → (∃ n : ℕ, 0 < n ∧ ξ.OrderDvd n) → (∀ PP, ¬ ξ.UnrAt PP ↔ PP ∈ Q ∨ ∃ PP' ∈ Q, Formalism.IndefR.Lev.IsConjPl PP' PP) → Formalism.IndefR.Lev.IsTwistPlaces D.host.g Q → GlobalTheory.OnCmp.ReadsOnly (R.Pg ∪ Q) Ω → GlobalTheory.OnCmp.VecOf R i Q Ω φv → ∀ (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), GlobalTheory.OnCmp.PhiOf R i Q Ω ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ Q → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (g q0 : ℕ) (X : Data D.host.E D.R.r) (hq : X.p0 + q0 = D.R.r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (x₀ : Frame X.Ψ D.R.r) (vr : Harm.Var X.Ψ q0 X.p0 (Fin (Vc D i).rank) ≃ FVar D (Wc D i).rank (Vc D i).rank), IsMod (Wc D i) (rank_Wc i) X → IsSympl X bas → IsONFr X x₀ → IsInvOf (Wc D i) (rank_Wc i) X x₀ (cart (R.MW i (sg0 D A))) → IsBasOf (Wc D i) (rank_Wc i) X hq x₀ (onb (R.MW i (sg0 D A))) → IsVarOf (Vc D i) (Wc D i) X q0 vr → ∀ (bad N : ℕ) (h : GA D (Vc D i)) (k : GA D (Wc D i)) (Λ : GenLat D.host.E (Vc D i).rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) (e : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), (∀ PP, PP ∈ R.Pg ∨ PP ∈ Q → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → h ∈ GfC (Vc D i) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h y → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ (Wc D i) (rank_Wc i) ι k mk → ∀ Y : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E, IsRoots l₂ (latR (rank_Wc i) (latG (Wc D i) k)) mk N Y → ∀ (v : TF (Vc D i).rank g) (a : ℂ), IsVac X bas (H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) (latR (rank_Wc i) (latG (Wc D i) k))) v → Reads R.θ (Vc D i) (Wc D i) (rank_Wc i) X bas idx (ω (1, k) (R.vacP i)) (a • v) (frMove R.θ (Wc D i) (rank_Wc i) X k x₀) → ∀ (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin (Vc D i).rank)) (d : ℕ), P.IsHomogeneous d → thetaKO (ω) h k (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (φv) (MvPolynomial.rename vr P)) = ((δ : ℤ) : ℂ) ^ d * (-1) ^ d * ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d * a * ((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) * ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ * thP X hq bas idx (gphi X bas (H.w0 : D.host.E) Λ.La (latR (rank_Wc i) (latG (Wc D i) k)) v (hatC l₂ φ) Y) P (frMove R.θ (Wc D i) (rank_Wc i) X k x₀) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i hstd H Dw ι hι hiso
  obtain ⟨δ, hδ⟩ := moved_datum_tw D G Pl0 T0 A Ks R F hC i hstd H Dw ι hι hiso
  refine ⟨δ, ?_⟩
  intro χ Q Ω ω φv hω ξ hchr hfin hram hQ hΩ hvec l₂ φ hφ hl hrt g q0 X hq bas idx x₀ vr hM hS hx hinv hbas hvr bad N h k Λ mk e
    Ps y hbad he hPs hh hsupp hdet hΛ htriv hlev hmk Y hY v a hv hR P d hd
  obtain ⟨e₀, he₀, -⟩ := hvec.2
  have hP := isPair_tw D G Pl0 T0 A Ks R F hC i hstd χ ω hω ξ hchr hfin Q hram e₀ he₀
  obtain ⟨-, -, hV0, hW0, hVs, hWs, hVstd⟩ := GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A Ks R F hC i A.μ0 hstd
  have hψ := hP.weil.std
  have hvac : IsVacO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.vacP i) :=
    hvec.1
  choose p hp using fun q => exists_finOf (Vc D i) (Wc D i) (rank_Wc i) ((δ : ℤ) • Y q)
  have hdat := hδ χ Q Ω ω φv hω ξ hchr hfin hram hQ hΩ hvec l₂ φ hφ hl bad N h k Λ mk hbad ⟨hh, e, Ps, he, hPs, hsupp⟩ hΛ
    htriv hlev hmk Y (fun q => (p q).1) (fun q => (p q).2) hY hp
  haveI := finite_levQ Dw l₂
  letI : Fintype (Fin (Vc D i).rank → LevQ Dw l₂) := Fintype.ofFinite _
  obtain ⟨hhs, hks, -, hlat, hV1, -⟩ := GlobalTheory.MovedLat.moved_lattices D _ _ _ _ hV0 hW0 hVs hWs h k
  obtain ⟨-, -, hmv, -⟩ := GlobalTheory.MovedLat.moved_lattices D _ _ _ _ hV0 hW0 hVs hWs 1 k
  rw [show fin (Vc D i) 1 = 1 from map_one _, hV1] at hmv
  have hx' := isONFr_move hψ hP.inf hP.std hP.even (rank_Wc i) X bas idx hM hS hx k
  have hvac' := GlobalTheory.WeilVacMove.isVacO_om D _ _ _ _ _ _ _ hP.weil hP.inf (fun _ => 1) (fun _ => 1) _
    (fun τ => compAt R.θ τ (Formalism.L2.Theta.mt _ k) * cart (R.MW i (sg0 D A)) τ * compAt R.θ τ (Formalism.L2.Theta.mt _ k⁻¹))
    _ _ _ _ 1 k (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.mul_assoc, GlobalTheory.WeilVacMove.compAt_mt_inv_mul, Matrix.mul_one]) hmv _ hvac
  have hL : ∀ L₀ : Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E),
      L₀ = Submodule.span (𝓞 D.host.E)
        {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ Bridge.hLat (Wc D i) (fin (Wc D i) k), w = a • v} →
      latR (rank_Wc i) (latG (Wc D i) k) = latR (rank_Wc i) L₀ := fun L₀ h₀ => by rw [h₀, hlat]
  have hcl := GlobalTheory.T.weilRepresentation_split_support_projects_vacuum D _ _ _ _ _ _ _ hP _ g (rank_Wc i) X bas idx hM hS H hrt _ _ Λ.La _ hV0 hVs hks hVstd hL _ _ hx'
    (isInvOf_move (rank_Wc i) X hinv k) _ hvac' _ hR e Ps h y he hsupp hdet hΛ
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul, projA_smul, smul_smul] at hcl
  obtain ⟨-, hsd, huni, hfg⟩ := LatOf.isLatOf_tens D _ _ _ _ _ g (rank_Wc i) X bas idx hψ hP.inf hP.std hP.even hM hS
    _ _ Λ.La _ hhs hks hΛ hL
  obtain ⟨hth, hsum⟩ := reads_sum hψ hP.inf hP.std hP.even (rank_Wc i) X bas idx hM hS hx'
    (hP.weil.om_pres (h, k) _ hvac.2.theta) hcl (hatC l₂ φ) (fun q => (p q).1) (fun q => (p q).2) (fun q => (hp q).2)
    Finset.univ
  rw [finsum_eq_sum_of_fintype] at hdat
  have hthP : IsThetaFunO R.ψ (Vc D i) (Wc D i) φv := by
    have h1 := hP.weil.om_pres (h, k)⁻¹ _ (hdat ▸ GlobalTheory.OrientedHeis.theta_smul _ hth :
      IsThetaFunO R.ψ (Vc D i) (Wc D i) (ω (h, k) φv))
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h1
  have hrd := (reads_linear_injective D _ _ _ _ _ g (rank_Wc i) X bas idx hψ hP.inf hP.std hP.even hM hS _ hx'
    _ _ _ _ hsum hsum).1 ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ 0
  rw [zero_smul, zero_smul, add_zero, add_zero, ← hdat] at hrd
  simp only [heisG_smul, (hp _).1] at hrd
  simp only [smul_comm (hatC l₂ φ _)] at hrd
  rw [← Finset.smul_sum, smul_smul, ← finsum_eq_sum_of_fintype] at hrd
  rw [kernel_of_reads hP (rank_Wc i) X bas idx hM hS hq hx hinv hbas hvr hh k hthP hrd P d hd,
    theta_smul₂ idx hS hP.even hq hx'.mem_dom _ _ hrd.1]
  have hpar := Parity.thP_gphi_neg _ _ g _ X bas idx hS hP.even q0 hq (H.w0 : D.host.E) H.w0.isIntegral_coe (cmHost_idempotent_trace_eq_one H)
    _ hsd v hv Λ huni hfg _ (hatC l₂ φ) Y P d hd _ hx'.mem_dom
  unfold gphi at hpar ⊢
  rcases Int.units_eq_one_or δ with rfl | rfl
  · simp only [Units.val_one, one_smul]
    rw [hpar]
    push_cast
    ring
  · simp only [Units.val_neg, Units.val_one, neg_smul, one_smul, neg_neg, Int.cast_neg, Int.cast_one, ← mul_pow]
    rw [neg_mul_neg, one_mul, one_mul]
    ring

end GlobalTheory.AdTh.ShortSeriesTw
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section
namespace GlobalTheory.FrameShort


open GlobalTheory.PtId GlobalTheory.AdTh in
set_option maxHeartbeats 4000000 in
theorem short_at_frame : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (cc : (T.J.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ka : ℂ) (δ : ℤˣ) (c0 : ℂ), GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.J.U ((i : ℕ) + 1) (O i).s0) (O i).dict (O i).mu (T.J.x₀ ((i : ℕ) + 1) (O i).s0) (R.ωP i A.μ0) (R.vacP i) cc → GlobalTheory.PtId.IoAt (O i) (v₀ i (sg0 D A)) ka → GlobalTheory.PtId.ClsAt R i (iotaW T.J i) δ → GlobalTheory.PtId.CovAt (O i) c0 → ‖ka‖ = 1 → ‖c0‖ = 1 → ∀ c0' : ℂ, c0' * c0⁻¹ ∈ D.what₂.embLL.range → (∃ m : ℕ, 0 < m ∧ (c0' * c0⁻¹) ^ m = 1) → (∀ (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))) (k : GA D (Wc D i)) (xk : (AE D)ˣ) (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), GlobalTheory.AdTh.IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → GlobalTheory.ThFr.IsSympl X bas → GlobalTheory.AdTh.IdxIs T.Q.c (O i).s0 X idx e → GlobalTheory.AdTh.latR (rank_Wc i) (latG (Wc D i) k) = X.Λ → IsDetRoot (Wc D i) k xk → GlobalTheory.Dict.IsMark (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ X.Λ mk → GlobalTheory.AdTh.MarkAd (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ (Wc D i) (rank_Wc i) (iotaW T.J i) k mk → letI : Algebra (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ := ((O i).s0.comp ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F →+* T.Q.c.F)).toAlgebra; ∀ (y₂ : FrPt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).Xo₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ ℂ) (A₂ : GlobalTheory.Dict.AnFib X bas idx e (GlobalTheory.AdTh.frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.J.x₀ ((i : ℕ) + 1) (O i).s0 τ.1)) X.Λ y₂), A₂.Marked mk → evR (T.dδ ((i : ℕ) + 1) (Vc D i).rank).Xo₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).cδ y₂ = c0' * ((χ xk : Circle) : ℂ)) → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → ∀ F₀ : (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i), IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x₀ P ((F₀).1 : T.R ((i : ℕ) + 1)) → ∀ g : GA D (Wc D i), (lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * (O i).phi ((ka * (-((δ : ℤ) : ℂ)) ^ GlobalTheory.PtId.degW (T.J.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) * c0⁻¹) • cc) ((F₀).1 : T.R ((i : ℕ) + 1)) g = D.what₂.embLL c * singleSeries R i ω φ' h ((O i).c0' y) w g := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hOP hβ hU hIo hRow hPh hSp v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK Λ h hSB hLa N x₀ P y hUm hTb hTd hLev hAdm hPh' hio cc ka δ c0 hcc hka hδ hcov hka1 hc01 c0' hρ hρm hcT
  have hTi : TieIn T.J R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hP := hOP.2
  have hs : (O i).s0 = T.J.toCore.σ₀ := sOv_eq _ _ _
  have hσ : GoodEmb T.J.Q.c (O i).s0 := hs ▸ T.J.toCore.good_σ₀
  have hmod := models_at_record_core D G Pl0 T0 A T.J R F κ v₀ hC hTi i (O i).s0 hs
  obtain ⟨hemb, hisom, hroot, hmk⟩ := dict_cast T.J hTi.laws _ (inR i) (O i).s0 hσ (Wc D i) (O i).hV (rank_Wc i)
  obtain ⟨δ', hδ'⟩ := GlobalTheory.AdTh.ShortSeriesTw.thetaKO_eq_short_series_tw D G Pl0 T0 A _ R F hC i hP.lift.std _ _ (iotaW T.J i) hemb hisom
  obtain ⟨y₀, ζ, φc, hrk, hζL, hζm, hhat, hphi, hhalf, hbadP⟩ := GlobalTheory.CoverDatum.datum_eq_hat_free D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP hβ v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK x₀ hAdm
  obtain ⟨hGf, e, Ps, he, hPs0, hsupp⟩ := hSB
  have hPs : ∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP hm =>
    hPs0 PP hPP (by rw [Nat.cast_mul]; exact PP.asIdeal.mul_mem_right _ hm)
  have hPsO : ∀ PP ∈ Ps, (((O i).bad () : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP hm =>
    hPs0 PP hPP (by rw [Nat.cast_mul]; exact PP.asIdeal.mul_mem_left _ hm)
  obtain ⟨yd, hyd⟩ := exists_isDetAt he (Vc D i) h
  obtain ⟨c1, hc1, hint1⟩ := GlobalTheory.T.twisted_kernel_class_scalar_integral_standard D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK Λ h N hUm hTb hTd hLev hLa e Ps yd hGf he hPs hPsO hsupp hyd
  obtain ⟨ρ, hρ'⟩ := hρ
  obtain ⟨ζL, hζL'⟩ := hζL
  have hρm' : ∃ m : ℕ, 0 < m ∧ ρ ^ m = 1 := by
    obtain ⟨m, hm, hm1⟩ := hρm
    refine ⟨m, hm, D.what₂.embLL.injective ?_⟩
    rw [map_pow, hρ', hm1, map_one]
  have hζm' : ∃ m : ℕ, 0 < m ∧ ζL ^ m = 1 := by
    obtain ⟨m, hm, hm1⟩ := hζm
    refine ⟨m, hm, D.what₂.embLL.injective ?_⟩
    rw [map_pow, hζL', hm1, map_one]
  have hroot_int : ∀ z : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ z ^ m = 1) → IsIntegral ℤ z ∧ IsIntegral ℤ z⁻¹ := by
    rintro z ⟨m, hm, hz⟩
    have hzI : IsIntegral ℤ z := IsIntegral.of_pow hm (hz ▸ isIntegral_one)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hm.ne'] at hz
      exact zero_ne_one hz
    refine ⟨hzI, ?_⟩
    have e : z⁻¹ = z ^ (m - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ hz0, ← pow_succ, Nat.sub_add_cancel hm]
      exact hz
    rw [e]
    exact hzI.pow _
  set d := degW (T.J.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) with hd
  refine ⟨y₀, ((((δ : ℤ) * (δ' : ℤ)) ^ d : ℤ) : D.what₂.LL) * ρ * ζL⁻¹ * c1, hrk, fun lam hlam => ?_, ?_⟩
  · obtain ⟨s, hs, hsi⟩ := hint1 lam hlam
    refine ⟨s, hs, ?_⟩
    have e : (s : D.what₂.LL) * (((((δ : ℤ) * (δ' : ℤ)) ^ d : ℤ) : D.what₂.LL) * ρ * ζL⁻¹ * c1) =
        ((((δ : ℤ) * (δ' : ℤ)) ^ d : ℤ) : D.what₂.LL) * ρ * ζL⁻¹ * ((s : D.what₂.LL) * c1) := by ring
    rw [e]
    exact (((isIntegral_algebraMap (R := ℤ) (x := (((δ : ℤ) * (δ' : ℤ)) ^ d : ℤ))).mul (hroot_int ρ hρm').1).mul
      (hroot_int ζL hζm').2).mul hsi
  intro φ' hφ' w hw F₀ hF₀ g
  have hU' : IsUnf (T.J.U ((i : ℕ) + 1) (O i).s0) := hTi.laws.unf _ (inR i) (O i).s0 hσ
  obtain ⟨hX, hon, hinv, hp, hrk', hpq, h1, hrt, -, hbas, hD, -⟩ := hmod ((O i).dict g).1
  obtain ⟨hx, g', Dc, γ, mk, vv, ϑ, κ', B, hat, hsd, hm, hBm, hma, hϑ, hvv, hκ, hrd⟩ :=
    exists_point (T.J.U ((i : ℕ) + 1) (O i).s0) hσ hU' h1 hTi.laws.pins.2.1.2 R.θ (Vc D i) (Wc D i) (rank_Wc i) (O i).dict
      (iotaW T.J i) (T.J.x₀ ((i : ℕ) + 1) (O i).s0) (fun Wt k => hmk R.θ hC.models.inf (fun k => (hmod k).1) h1 Wt k)
      (wtA (κ i)) hD (O i).mu (R.ωP i A.μ0) (R.vacP i) cc hcc g
  obtain ⟨hγ, hΛ, hfr⟩ := hat
  obtain ⟨xk, hxk⟩ := hroot (γ * g)
  have hζ0 : ζ ≠ 0 := by
    obtain ⟨m, hm, hm1⟩ := hζm
    rintro rfl
    rw [zero_pow hm.ne'] at hm1
    exact zero_ne_one hm1
  letI : Algebra T.Q.c.F ℂ := (O i).s0.toAlgebra
  obtain ⟨mk₂, Y, hm₂, ha₂, hY, hgeo⟩ := GlobalTheory.ShortPtVal.short_value_at_point D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP χ c0' hcT Λ N x₀ P hUm hTb hTd hLev hAdm
    hPh' ζ φc hζ0 hhat F₀.1 hF₀ _ g' Dc (γ * g) xk hxk hX hp hΛ hsd _ hx hfr mk hm hma vv ϑ κ' hvv hκ _ B hBm hϑ
  obtain ⟨vr, hvr⟩ := exists_isVarOf (Vc D i) (Wc D i) (rank_Wc i) _ hX _ Dc.hr
  have hCs := GlobalTheory.AdTh.VecSeries.singleSeries_eq_phase_thetaKO D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP hIo χ ω hK.weil _ _ φ' hφ' ka hka P y hio _ g' Dc vr hX hp hvr h w hw g γ hγ
  have htw := GlobalTheory.OnCmp.weil_twist_base_of D G Pl0 T0 A _ R F hC i χ ω hK.weil (γ * g) xk hxk (R.vacP i) (hC.thP.vP i A.μ0).1.2.theta
  have hrd' : Reads R.θ (Vc D i) (Wc D i) (rank_Wc i) ((T.J.U ((i : ℕ) + 1) (O i).s0).X ((O i).dict g).1) Dc.bas Dc.idx
      (ω (1, γ * g) (R.vacP i)) ((((χ xk : Circle) : ℂ) * (cc ((O i).dict g).1 * (O i).mu g * κ')) • vv) ((O i).dict g).2 := by
    obtain ⟨s1, s2⟩ := ((thA_heis_entire_linear_injective _ _ g' _ _ Dc.bas Dc.idx Dc.sympl hD.2 _ hx _ hrd.1).2.2 vv hvv.1).1
      ((χ xk : Circle) : ℂ) 0
    rw [zero_smul, add_zero, smul_smul] at s1 s2
    rw [zero_smul, add_zero] at s2
    refine ⟨s1, fun z hz => ?_⟩
    rw [htw, s2, Pi.smul_apply, Pi.smul_apply, hrd.2 z hz, smul_eq_mul, smul_eq_mul]
    ring
  have hH := hPh'.1
  have hhom : (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)).IsHomogeneous d :=
    ((GlobalTheory.isHomogeneous_of_rowDeg hH.2.2).map _).rename_isHomogeneous
  have hser := hδ' χ _ _ ω φ' hK.weil _ hK.chr hK.fin hK.ram hK.pl (GlobalTheory.OnCmp.readsOnly_omegaFree R i _ ξR y₀) hφ' _ φc hphi
    hhalf hrt g' _ _ Dc.hr Dc.bas Dc.idx _ vr hX Dc.sympl hon hinv (hbas _) hvr
    (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M) N h (γ * g) Λ mk₂ e Ps yd hbadP he hPs hGf hsupp hyd hLa hTd hLev ha₂
    Y (hΛ ▸ hY) vv _ (hΛ ▸ hvv) (hfr ▸ hrd') _ d hhom
  rw [hΛ, ← hfr] at hser
  have hx0 : 0 < xiR D := norm_pos_iff.2 ((_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hrdU : rdU (T.J.U ((i : ℕ) + 1) (O i).s0) (F₀.1 : T.R ((i : ℕ) + 1)) ((O i).dict g).1 ((O i).dict g).2 = _ :=
    (dif_pos hx).trans hgeo
  have hphiE : (O i).phi ((ka * (-((δ : ℤ) : ℂ)) ^ d * c0⁻¹) • cc) (F₀.1 : T.R ((i : ℕ) + 1)) g =
      ((ka * (-((δ : ℤ) : ℂ)) ^ d * c0⁻¹) * cc ((O i).dict g).1) * (O i).mu g *
        rdU (T.J.U ((i : ℕ) + 1) (O i).s0) (F₀.1 : T.R ((i : ℕ) + 1)) ((O i).dict g).1 ((O i).dict g).2 := rfl
  have hSS := hCs.trans (congrArg (fun z => ka * z) hser)
  rw [hphiE, hrdU, hSS, GlobalTheory.AdTh.SerCore.lieFac_eq_sqrt_pow _ hx0, ← hc1]
  simp only [map_mul, map_inv₀, map_intCast, hρ', hζL']
  have hδ2 : ((δ' : ℤ) : ℂ) ^ d * ((δ' : ℤ) : ℂ) ^ d = 1 := by
    rw [← mul_pow]
    rcases Int.units_eq_one_or δ' with e | e <;> rw [e] <;> simp
  push_cast
  have alg : ∀ (s ka δc δc' c0 c0' k m x c1 a b q κ' ζ TH : ℂ) (n : ℕ), δc' ^ n * δc' ^ n = 1 →
      s ^ n * (ka * (-δc) ^ n * c0⁻¹ * k * m * (c0' * x * (c1 * (a * b * q) * κ' * ζ⁻¹ * TH))) =
        (δc * δc') ^ n * (c0' * c0⁻¹) * ζ⁻¹ * c1 * (ka * (δc' ^ n * (-1) ^ n * s ^ n * (x * (k * m * κ')) * (a * b) * q * TH)) := by
    intro s ka δc δc' c0 c0' k m x c1 a b q κ' ζ TH n hn
    rw [neg_pow, mul_pow]
    linear_combination (-(s ^ n * ka * (-1) ^ n * δc ^ n * c0⁻¹ * k * m * c0' * x * c1 * a * b * q * κ' * ζ⁻¹ * TH)) * hn
  exact alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hδ2

end GlobalTheory.FrameShort

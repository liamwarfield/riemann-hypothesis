module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaConstantUniformisedChartFibreEqFamilyConsta
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaConstantUniformisedChartFibreEqFamilyConsta
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace GlobalTheory.ArcThetaFib

theorem val_res {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    (res h u).val = (X.presheaf.map (homOfLE h).op).hom u.val := rfl

theorem val_linComb {X Y : Scheme.{0}} {L M : LB X} (w : LB.Iso L M) (e : Y ⟶ X)
    (jM : PUnit → M.ι) (jL : PUnit → L.ι) :
    ((LB.linCombIso w (K := PUnit) (fun _ => e) (fun _ => 1)).s (jM, jL)).val =
      (Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le M (fun _ => e) jM PUnit.unit))
        (inf_le_right.trans (LB.wchart_le L (fun _ => e) jL PUnit.unit)) :
          LB.wchart M (fun _ => e) jM ⊓ LB.wchart L (fun _ => e) jL ≤
            e ⁻¹ᵁ ((LB.div M L).U (jM PUnit.unit, jL PUnit.unit)))).op).hom
        ((e.app _).hom (w.s (jM PUnit.unit, jL PUnit.unit)).val) := by
  show Units.val (∏ _k : PUnit, (res _ (pullU e _ (w.s (jM _k, jL _k)))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  rfl

theorem val_rigPullOf {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (F : G'.left ⟶ G.left) (f : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left)
    (he : eSec G' ≫ F = f ≫ eSec G) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) (j : PUnit → PUnit → L.ι) :
    ((rigPullOf F f he L r).s j).val = ((𝟙_ (Over S')).left.presheaf.map (homOfLE (rigPull_le F f he L j)).op).hom
      ((f.app _).hom (r.s (fun _ => j PUnit.unit PUnit.unit)).val) := rfl

theorem maps_val {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (F : G'.left ⟶ G.left) (f : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left)
    (he : eSec G' ≫ F = f ≫ eSec G) (L : LB G.left)
    (r : LB.Gen (L.pull (eSec G))) (L' : LB G'.left) (w : LB.Iso L' (L.pull F)) (a : LB.Gen (L'.pull (eSec G')))
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) a (rigPullOf F f he L r))
    (t : Sp ℂ ⟶ (𝟙_ (Over S')).left) (j : L.ι) (i : L'.ι) (hj : ⊤ ≤ (t ≫ eSec G' ≫ F) ⁻¹ᵁ L.U j)
    (hi : ⊤ ≤ (t ≫ eSec G') ⁻¹ᵁ L'.U i) :
    valAt' (t ≫ f) ((L.pull (eSec G)).U (fun _ => j)) (r.s (fun _ => j)).val =
      valAt' (t ≫ eSec G') ((LB.div (L.pull F) L').U (fun _ => j, i)) (w.s (fun _ => j, i)).val *
        valAt' t ((L'.pull (eSec G')).U (fun _ => i)) (a.s (fun _ => i)).val := by
  have hB : ⊤ ≤ t ⁻¹ᵁ ((L.pull F).pull (eSec G')).U (fun _ _ => j) :=
    fun q hq => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => hj hq
  have hA : ⊤ ≤ t ⁻¹ᵁ (L'.pull (eSec G')).U (fun _ => i) := fun q hq => Set.mem_iInter.2 fun _ => hi hq
  have hBA : ⊤ ≤ t ⁻¹ᵁ (((L.pull F).pull (eSec G')).U (fun _ _ => j) ⊓ (L'.pull (eSec G')).U (fun _ => i)) :=
    fun q hq => ⟨hB hq, hA hq⟩
  have e := congrArg (fun v => valAt' t _ (Units.val v)) (h (fun _ _ => j, fun _ => i))
  dsimp only at e
  rw [val_res, GlobalTheory.ThetaFn.valAt'_res t _ hBA, val_rigPullOf] at e
  erw [GlobalTheory.ThetaFn.valAt'_res t _ hB] at e
  erw [GlobalTheory.ThetaFn.valAt'_app] at e
  rw [Units.val_mul, ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_mul] at e
  erw [val_linComb, GlobalTheory.ThetaFn.valAt'_res t _ hBA] at e
  refine e.trans ?_
  congr 1
  rw [val_res]; exact GlobalTheory.ThetaFn.valAt'_res t _ hBA _

theorem maps_val' {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (F : G'.left ⟶ G.left) (f : S' ⟶ S)
    (he : eSec G' ≫ F = f ≫ eSec G) (L : LB G.left)
    (r : LB.Gen (L.pull (eSec G))) (L' : LB G'.left) (w : LB.Iso L' (L.pull F)) (a : LB.Gen (L'.pull (eSec G')))
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) a (rigPullOf F f he L r))
    (t : Sp ℂ ⟶ S') (j : L.ι) (i : L'.ι) (hj : ⊤ ≤ (t ≫ eSec G' ≫ F) ⁻¹ᵁ L.U j)
    (hi : ⊤ ≤ (t ≫ eSec G') ⁻¹ᵁ L'.U i) :
    valAt' (t ≫ f) ((L.pull (eSec G)).U (fun _ => j)) (r.s (fun _ => j)).val =
      valAt' (t ≫ eSec G') ((LB.div (L.pull F) L').U (fun _ => j, i)) (w.s (fun _ => j, i)).val *
        valAt' t ((L'.pull (eSec G')).U (fun _ => i)) (a.s (fun _ => i)).val :=
  maps_val F f he L r L' w a h t j i hj hi


set_option maxHeartbeats 1600000 in
theorem const_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∀ (w : ℂ), Ha.T < w.im → ∀ (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)), IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ → IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ → ∀ K : ℂ, (∀ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u Ha.i (Ha.Pw w)) (fun z => (Fu.ex Ha.i (Ha.Pw w) z).left) (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) fr → ∀ (z : Fin g → ℂ) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw w) z).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap σ → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (M.θ j) = valAt' x _ (w₁.s (fun _ => j, k)).val * (K * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) * fr j₀ z)) → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig → GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) → c₀ = K := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha th Θ M hGE hty hPI hχ hgen hM w hw w₀ w₁ h₀ h₁ K hK yF hyF1 hyF2 hz x φ hkey u c₀ hrig hfib hfn
  obtain ⟨he, wx, hg, hpb, hwgen, hrigx, hfun, -⟩ := hkey
  have hP := Ha.period w hw
  have hw1 : φ ≫ Y.t.G.hom = (x.P.A.hom ≫ yF) ≫ (Y.jQ ≫ pullback.fst _ _) := by
    rw [hpb.1.w, Category.assoc]; rfl
  obtain ⟨Φ, hΦ1, hΦ2⟩ : ∃ Φ : x.P.A.left ⟶ Y.oF.t.G.left, Φ ≫ Y.m.φ = φ ∧ Φ ≫ Y.oF.t.G.hom = x.P.A.hom ≫ yF :=
    ⟨_, Y.m.cart.1.lift_fst _ _ hw1, Y.m.cart.1.lift_snd _ _ hw1⟩
  have hfib' : ∀ z, ∃ ψ : Sp ℂ ⟶ Y.oF.t.G.left, ψ ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw w) z).left ∧
      ψ ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap σ ∧ (u.ex z).left ≫ φ = ψ ≫ Y.m.φ := hfib
  choose ψ hψ1 hψ2 hψ3 using hfib'
  have hexA : ∀ z, (u.ex z).left ≫ x.P.A.hom = 𝟙 _ := fun z => Over.w (u.ex z)
  have hψF : ∀ z, ψ z ≫ Y.oF.t.G.hom = yF := fun z => by
    apply pullback.hom_ext
    · rw [Category.assoc, ← Y.m0.toSABMap.cart.1.w, ← Category.assoc, hψ1 z, hyF1]
      exact Over.w (Fu.ex Ha.i (Ha.Pw w) z)
    · rw [Category.assoc, hψ2 z, hyF2]
  have hψ : ∀ z, ψ z = (u.ex z).left ≫ Φ := fun z => by
    apply Y.m.cart.1.hom_ext
    · rw [Category.assoc]; exact (hψ3 z).symm.trans (by rw [hΦ1])
    · rw [hψF z, Category.assoc, hΦ2, ← Category.assoc, hexA z]; exact (Category.id_comp yF).symm
  have hu0' : (u.ex 0).left = eSec x.P.A := by
    rw [(u.ker 0).2 u.Λ.zero_mem]
    change (toUnit _ ≫ η[x.P.A]).left = η[x.P.A].left
    rw [toUnit_unit, Category.id_comp]
  obtain ⟨hsym, hpos⟩ := Θ.pos w hw
  obtain ⟨hd, v₀, hv₀⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g Θ.c₁ Θ.c₂ Θ.half₁ Θ.half₂).1 _ hsym hpos
  have hθd : Differentiable ℂ (fun v => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec v)) :=
    hd.comp (LinearMap.toContinuousLinearMap (Matrix.mulVecLin Θ.h)).differentiable
  have hθ : ∃ v, thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec v) ≠ 0 := by
    refine ⟨∑ k, v₀ k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1)), ?_⟩
    have : Θ.h.mulVec (∑ k, v₀ k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1))) = v₀ := by
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, (Θ.per w _).1]
      exact (pi_eq_sum_univ' v₀).symm
    rwa [this]
  obtain ⟨fr, hfr⟩ := Θ.frame w hw
  have hKf := hK fr hfr
  let pt : Sp ℂ := IsLocalRing.closedPoint ℂ
  have top_iff : ∀ {X : Scheme.{0}} (f : Sp ℂ ⟶ X) (U : X.Opens), ⊤ ≤ f ⁻¹ᵁ U ↔ f pt ∈ U := fun f U =>
    ⟨fun h => h (x := pt) trivial, fun h q _ => (Subsingleton.elim (α := PrimeSpectrum ℂ) pt q) ▸ h⟩
  have exch : ∀ {X : Scheme.{0}} {L : LB X}, L.IsLB → ∀ y : X, ∃ i, y ∈ L.U i := fun hL y =>
    TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, _ by rw [hL.cover]; trivial)
  set y₀ := (u.ex 0).left pt with hy₀
  obtain ⟨i, hi⟩ := exch x.P.isLB y₀
  obtain ⟨j, hj⟩ := exch Y.t.PP.isLB (φ y₀)
  obtain ⟨k, hk⟩ := exch Y.oF.t.PP.isLB (Φ y₀)
  obtain ⟨j₀, hj₀⟩ := exch Xo.univ.t.PP.isLB (Y.m0.toSABMap.φ (Φ y₀))
  let Ω : x.P.A.left.Opens := Φ ⁻¹ᵁ ((LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) ⊓ Φ ⁻¹ᵁ ((LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k)) ⊓ ((LB.div (Y.t.PP.L.pull φ) x.P.L).U (fun _ => j, i)) ⊓ (Φ ≫ Y.m0.toSABMap.φ) ⁻¹ᵁ Xo.univ.t.PP.L.U j₀
  have hΦφ : ∀ y, Y.m.φ (Φ y) = φ y := fun y => by rw [← hΦ1]; rfl
  have hy₀Ω : y₀ ∈ Ω := by
    refine ⟨⟨⟨⟨Set.mem_iInter.2 fun _ => hj₀, hk⟩, ⟨Set.mem_iInter.2 fun _ => ?_, hk⟩⟩, ⟨Set.mem_iInter.2 fun _ => hj, hi⟩⟩, hj₀⟩
    show Y.m.φ (Φ y₀) ∈ Y.t.PP.L.U j
    rw [hΦφ]; exact hj
  let N : Set (Fin g → ℂ) := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ Ω}
  have hN : N ∈ nhds (0 : Fin g → ℂ) := ((u.hol Ω 1).1).mem_nhds ((top_iff _ _).2 hy₀Ω)
  have hle : (Y.t.PP.L.pull φ).U (fun _ => j) ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j) := by
    intro y hy
    refine ⟨?_, Set.mem_iInter.1 hy.1 PUnit.unit⟩
    show (φ ≫ Y.t.G.hom) y ∈ M.U
    rw [hpb.1.w]
    exact hz (x := x.P.A.hom y) trivial
  have key : ∀ z ∈ N, thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) *
      (c₀ * (valAt' ((u.ex z).left ≫ Φ) ((LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) (w₀.s (fun _ => j₀, k)).val *
        valAt' (u.ex z).left ((Y.t.PP.L.pull φ).U (fun _ => j) ⊓ x.P.L.U i) (wx.s (fun _ => j, i)).val * u.fr i z) -
       K * (valAt' ((u.ex z).left ≫ Φ) ((LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k)) (w₁.s (fun _ => j, k)).val * fr j₀ z)) = 0 := by
    intro z hzN
    have hz0 : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (Φ ⁻¹ᵁ ((LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k))) := fun q hq => (hzN hq).1.1.1
    have hz1 : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (Φ ⁻¹ᵁ ((LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k))) := fun q hq => (hzN hq).1.1.2
    have hDx : ⊤ ≤ (u.ex z).left ⁻¹ᵁ ((LB.div (Y.t.PP.L.pull φ) x.P.L).U (fun _ => j, i)) := fun q hq => (hzN hq).1.2
    have hUi : ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i := fun q hq => (hzN hq).1.2.2
    have e : valAt' ((u.ex z).left ≫ Φ) ((LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) (w₀.s (fun _ => j₀, k)).val *
        valAt' ((u.ex z).left ≫ φ) (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j) (M.θ j) =
        valAt' ((u.ex z).left ≫ Φ) ((LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k)) (w₁.s (fun _ => j, k)).val * (K * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) * fr j₀ z) := by
      have := hKf z (ψ z) j k j₀ (hψ1 z) (hψ2 z) (by rw [hψ z]; exact hz1) (by rw [hψ z]; exact hz0)
      rw [hψ z, Category.assoc, hΦ1] at this
      exact this
    have a2 := GlobalTheory.ThetaFn.valAt'_appLE' (u.ex z).left φ hle hDx (M.θ j)
    rw [hfun (fun _ => j) i hle, ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_mul] at a2
    dsimp only at a2
    have r2 := GlobalTheory.ThetaFn.valAt'_res (u.ex z).left (inf_le_right : ((LB.div (Y.t.PP.L.pull φ) x.P.L).U (fun _ => j, i)) ≤ x.P.L.U i) hDx (x.th.f i)
    rw [hfn i z hUi] at r2
    erw [r2] at a2
    linear_combination valAt' ((u.ex z).left ≫ Φ) ((LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) (w₀.s (fun _ => j₀, k)).val * a2 + e
  have hη : eSec Y.oF.t.G ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w η[Y.oF.t.G]
  have hψ0 : (u.ex 0).left ≫ Φ = yF ≫ eSec Y.oF.t.G := by
    apply Y.m.cart.1.hom_ext
    · refine ((Category.assoc _ _ _).trans (congrArg _ hΦ1)).trans ?_
      refine (congrArg (· ≫ φ) hu0').trans (he.trans ?_)
      refine Eq.trans ?_ (congrArg (yF ≫ ·) Y.m.cm.e_comm.symm |>.trans (Category.assoc _ _ _).symm)
      rw [Y.m.base, Category.assoc]
      rfl
    · refine ((Category.assoc _ _ _).trans ((congrArg _ hΦ2).trans (((Category.assoc _ _ _).symm).trans
        ((congrArg (· ≫ yF) (hexA 0)).trans (Category.id_comp yF))))).trans ?_
      exact ((Category.comp_id yF).symm.trans (congrArg (yF ≫ ·) hη.symm)).trans (Category.assoc _ _ _).symm
  have memE : ∀ U : x.P.A.left.Opens, y₀ ∈ U → ⊤ ≤ (eSec x.P.A) ⁻¹ᵁ U := fun U h => by
    rw [← hu0']; exact (top_iff _ _).2 h
  have R1 : u.fr i 0 = valAt' (𝟙 (Sp ℂ)) ((x.P.L.pull (eSec x.P.A)).U (fun _ => i)) (x.rig.s (fun _ => i)).val := by
    refine hrig (fun _ => i) fun q hq => Set.mem_iInter.2 fun _ => ?_
    exact memE _ hi hq
  have R2 := maps_val' φ (yF ≫ Y.j) he Y.t.PP.L Y.t.PP.rig x.P.L wx x.rig hrigx (𝟙 _) j i
    (fun q hq => memE (φ ⁻¹ᵁ Y.t.PP.L.U j) hj hq) (fun q hq => memE _ hi hq)
  rw [Category.id_comp, Category.id_comp] at R2
  have R3 := maps_val' Y.m.φ Y.m.cm.e Y.m.cm.e_comm Y.t.PP.L Y.t.PP.rig Y.oF.t.PP.L w₁ Y.oF.t.PP.rig h₁.2 yF j k
    (by rw [← Category.assoc, ← hψ0, Category.assoc, hΦ1]; exact (top_iff _ _).2 hj)
    (by rw [← hψ0]; exact (top_iff _ _).2 hk)
  rw [Y.m.base] at R3
  have R4 := maps_val' Y.m0.toSABMap.φ Y.m0.cm.e Y.m0.cm.e_comm Xo.univ.t.PP.L Xo.univ.t.PP.rig Y.oF.t.PP.L w₀
    Y.oF.t.PP.rig h₀.2 yF j₀ k
    (by rw [← Category.assoc, ← hψ0]; exact (top_iff _ _).2 hj₀)
    (by rw [← hψ0]; exact (top_iff _ _).2 hk)
  rw [Y.m0.base, hyF1] at R4
  have h5 : ⊤ ≤ (Fu.ex Ha.i (Ha.Pw w) 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j₀ := by
    rw [← hψ1 0, hψ 0]; exact (top_iff _ _).2 hj₀
  have R5 := hfr.2.2.2.1 j₀ h5
  have hF : valAt' ((u.ex 0).left ≫ Φ) ((LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) (w₀.s (fun _ => j₀, k)).val *
      valAt' (u.ex 0).left ((Y.t.PP.L.pull φ).U (fun _ => j) ⊓ x.P.L.U i) (wx.s (fun _ => j, i)).val * u.fr i 0 =
      valAt' ((u.ex 0).left ≫ Φ) ((LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k)) (w₁.s (fun _ => j, k)).val * fr j₀ 0 := by
    rw [hψ0, R5, R1, hu0', R4]
    rw [show valAt' (eSec x.P.A) ((Y.t.PP.L.pull φ).U (fun _ => j) ⊓ x.P.L.U i) (wx.s (fun _ => j, i)).val =
      valAt' (eSec x.P.A) ((LB.div (Y.t.PP.L.pull φ) x.P.L).U (fun _ => j, i)) (wx.s (fun _ => j, i)).val from rfl]
    have R3' : valAt' (yF ≫ Y.j) ((Y.t.PP.L.pull (eSec Y.t.G)).U (fun _ => j)) (Y.t.PP.rig.s (fun _ => j)).val = _ := R3
    linear_combination valAt' (yF ≫ eSec Y.oF.t.G) ((LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) (w₀.s (fun _ => j₀, k)).val * (R3' - R2)
  have hne : valAt' ((u.ex 0).left ≫ Φ) ((LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k)) (w₁.s (fun _ => j, k)).val * fr j₀ 0 ≠ 0 :=
    mul_ne_zero (GlobalTheory.AbelianLetters.valAt'_unit_ne_zero ((u.ex 0).left ≫ Φ)
      ((top_iff ((u.ex 0).left ≫ Φ) _).2 hy₀Ω.1.1.2) _) (hfr.2.1 j₀ 0 h5)
  have cont : ∀ (U : x.P.A.left.Opens) (f : Γ(x.P.A.left, U)), (∀ z ∈ N, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U) →
      ContinuousAt (fun z => valAt' (u.ex z).left U f) 0 := fun U f hU =>
    ((u.hol U f).2.differentiableAt (Filter.mem_of_superset hN hU)).continuousAt
  have cΦ : ∀ (U : Y.oF.t.G.left.Opens) (f : Γ(Y.oF.t.G.left, U)), (∀ z ∈ N, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (Φ ⁻¹ᵁ U)) →
      ContinuousAt (fun z => valAt' ((u.ex z).left ≫ Φ) U f) 0 := fun U f hU =>
    (cont _ ((Φ.app U).hom f) hU).congr (Filter.Eventually.of_forall fun z => GlobalTheory.ThetaFn.valAt'_app _ Φ U f)
  have c0 := cΦ ((LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) (w₀.s (fun _ => j₀, k)).val (fun z hz q hq => (hz hq).1.1.1)
  have c1 := cΦ ((LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k)) (w₁.s (fun _ => j, k)).val (fun z hz q hq => (hz hq).1.1.2)
  have cW := cont ((Y.t.PP.L.pull φ).U (fun _ => j) ⊓ x.P.L.U i) (wx.s (fun _ => j, i)).val (fun z hz q hq => (hz hq).1.2)
  have cu : ContinuousAt (u.fr i) 0 :=
    ((u.fr_hol i).differentiableAt (Filter.mem_of_superset hN fun z hz q hq => (hz hq).1.2.2)).continuousAt
  have cf : ContinuousAt (fr j₀) 0 := by
    refine ((hfr.1 j₀).differentiableAt (Filter.mem_of_superset hN fun z (hz : z ∈ N) => ?_)).continuousAt
    show ⊤ ≤ (Fu.ex Ha.i (Ha.Pw w) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j₀
    rw [← hψ1 z, hψ z]
    exact fun q hq => (hz hq).2
  have hlim := GlobalTheory.ArcQ.AnFrEx.eq_zero_of_mul_eventually (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z))
    (fun z => c₀ * (valAt' ((u.ex z).left ≫ Φ) ((LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) (w₀.s (fun _ => j₀, k)).val *
        valAt' (u.ex z).left ((Y.t.PP.L.pull φ).U (fun _ => j) ⊓ x.P.L.U i) (wx.s (fun _ => j, i)).val * u.fr i z) -
       K * (valAt' ((u.ex z).left ≫ Φ) ((LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k)) (w₁.s (fun _ => j, k)).val * fr j₀ z)) hθd hθ
    ((continuousAt_const.mul ((c0.mul cW).mul cu)).sub (continuousAt_const.mul (c1.mul cf)))
    (by filter_upwards [hN] with z hz using key z hz)
  beta_reduce at hlim
  rw [hF] at hlim
  have h2 : (c₀ - K) * (valAt' ((u.ex 0).left ≫ Φ) ((LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k)) (w₁.s (fun _ => j, k)).val * fr j₀ 0) = 0 := by
    linear_combination hlim
  exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hne)

end GlobalTheory.ArcThetaFib
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaConstantUniformisedChartFibreEqFamilyConstaStatement
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstant_uniformisedChartFibre_eq_familyConstant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∀ (w : ℂ), Ha.T < w.im → ∀ (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)), IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ → IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ → ∀ K : ℂ, (∀ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u Ha.i (Ha.Pw w)) (fun z => (Fu.ex Ha.i (Ha.Pw w) z).left) (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) fr → ∀ (z : Fin g → ℂ) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw w) z).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap σ → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (M.θ j) = valAt' x _ (w₁.s (fun _ => j, k)).val * (K * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) * fr j₀ z)) → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig → GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) → c₀ = K := by
  first | exact @GlobalTheory.ArcThetaFib.const_eq | exact GlobalTheory.ArcThetaFib.const_eq | (intros; apply GlobalTheory.ArcThetaFib.const_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegenerationCharMapEqOnEvenCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegenerationCharMapEqOnEvenCharacters
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.SqCompare


open GlobalTheory.CoordCompare GlobalTheory.PrimNorm GlobalTheory.MulPull in
theorem sq_law {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {M : LB A.left} (hM : M.IsLB)
    (hT : ∃ t : LB.Gen (Theta A M), t.IsGen) {Y : Over S} (y : Y ⟶ A) (a b : 𝟙_ (Over S) ⟶ A)
    (v : LB.Gen (LB.LinComb M (diffφ y a b) ![2, -2, 2, -2])) (hv : v.IsGen) :
    ∃ v' : LB.Gen (LB.LinComb M (diffφ y (a * a) (b * b)) ![1, -1, 1, -1]), v'.IsGen := by
  have hc := fun p q s : Y ⟶ A => diff₃_ptCls (T := Y) hM hT p q s
  have h := (hasGen_iff hM _ _).1 ⟨v, hv⟩
  rw [Fin.prod_univ_four] at h
  refine (hasGen_iff hM _ _).2 ?_
  rw [Fin.prod_univ_four]
  set m := ptCls M Y with hm
  set α := toUnit Y ≫ a
  set β := toUnit Y ≫ b
  have cα : toUnit Y ≫ (a * a) = α * α := MonObj.comp_mul _ _ _
  have cβ : toUnit Y ≫ (b * b) = β * β := MonObj.comp_mul _ _ _
  change m (y * β) ^ (2 : ℤ) * m (y * α) ^ (-2 : ℤ) * m α ^ (2 : ℤ) * m β ^ (-2 : ℤ) = 1 at h
  change m (y * (toUnit Y ≫ (b * b))) ^ (1 : ℤ) * m (y * (toUnit Y ≫ (a * a))) ^ (-1 : ℤ) *
    m (toUnit Y ≫ (a * a)) ^ (1 : ℤ) * m (toUnit Y ≫ (b * b)) ^ (-1 : ℤ) = 1
  rw [cα, cβ]
  have kα := diff₂_mul_right hc y α α
  have kβ := diff₂_mul_right hc y β β
  calc _ = (diff₂ m y (β * β) * (diff₂ m y β * diff₂ m y β)⁻¹) *
        (diff₂ m y (α * α) * (diff₂ m y α * diff₂ m y α)⁻¹)⁻¹ *
        (m (y * β) ^ (2 : ℤ) * m (y * α) ^ (-2 : ℤ) * m α ^ (2 : ℤ) * m β ^ (-2 : ℤ)) := by
        apply Additive.ofMul.injective
        simp only [diff₂, ofMul_mul, ofMul_inv, ofMul_zpow]
        abel
    _ = 1 := by rw [← kα, ← kβ, h, mul_inv_cancel, mul_inv_cancel, inv_one, _root_.mul_one, _root_.mul_one]


open GlobalTheory.CoordCompare TorusCoord in
theorem sq_desc {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g' : GtCoord I D' e G)
    (Φ : D'.P.A ⟶ D.P.A) [IsMonHom Φ] [Mono Φ.left] (hp : g'.pG ≫ Φ = g.pG)
    (w : LB.Iso (LB.LinComb D'.P.L (K := Fin 1) (fun _ => 𝟙 D'.P.A.left) (fun _ => 2))
      ((LB.LinComb D.P.L (K := Fin 1) (fun _ => 𝟙 D.P.A.left) (fun _ => 2)).pull Φ.left)) (hw : w.IsGen)
    (χ : D.X) (χ' : D'.X)
    (hker : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (J'), Good D.P.L z J →
      Good D'.P.L z J' → r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A →
      r ≫ g'.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D'.P.A →
      val (g.t χ) r z J = val (g'.t χ') r z J') :
    ∃ v : LB.Gen (LB.LinComb D.P.L (diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ)) ![2, -2, 2, -2]), v.IsGen := by
  obtain ⟨t, ht, W, hW⟩ := GlobalTheory.T.exists_square_generator_through_squareIso D.P.isLB D'.P.isLB w hw (D'.Oφ g'.pG χ') Oinvε (g'.t χ') (g'.t_gen χ')
  obtain ⟨u, hu, hu'⟩ := exists_gen D.P.isLB
    (φ' := fun k => g.q.left ≫ diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) k) (ε' := ![2, -2, 2, -2])
    (fun U _ h => by
      have e2 := prod_diff (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) ((Over.map (thick R I e)).map g.q) h
      have e3 : ∏ k, h (g.q.left ≫ diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) k) ^ (![2, -2, 2, -2] : Fin 4 → ℤ) k =
          (∏ k, h (((Over.map (thick R I e)).map g.q).left ≫ diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) k) ^
            (![1, -1, 1, -1] : Fin 4 → ℤ) k) ^ (2 : ℤ) := by
        simp only [Fin.prod_univ_four, mul_zpow, ← zpow_mul]
        rfl
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (e3.trans (congrArg (· ^ (2 : ℤ)) e2)).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, Oφ_comp_hom, hp, Fintype.prod_sum_type]
      simp only [Fin.prod_univ_four]
      let T := (Over.map (thick R I e)).obj (thickObj R I e G)
      show h (g.pG * (toUnit T ≫ D'.c χ' ≫ Φ)).left ^ (2 * (-1 : ℤ)) * h (toUnit T ≫ D'.c χ' ≫ Φ).left ^ (2 * (1 : ℤ)) *
          h g.pG.left ^ (2 * (1 : ℤ)) * h (1 : T ⟶ D.P.A).left ^ (2 * (-1 : ℤ)) *
        ((h (g.pG * (toUnit T ≫ D.c χ)).left ^ (- -1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (-1 : ℤ) *
          h g.pG.left ^ (-1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (- -1 : ℤ)) *
         (h (g.pG * (toUnit T ≫ D.c χ)).left ^ (- -1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (-1 : ℤ) *
          h g.pG.left ^ (-1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (- -1 : ℤ))) =
        (h (g.pG * (toUnit T ≫ D.c χ)).left * (h (g.pG * (toUnit T ≫ D'.c χ' ≫ Φ)).left)⁻¹ *
          h (toUnit T ≫ D'.c χ' ≫ Φ).left * (h (toUnit T ≫ D.c χ).left)⁻¹) ^ (2 : ℤ)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      abel)
    (LB.mulGen D.P.L _ _ _ _ t (LB.mulGen D.P.L _ _ _ _ (LB.invGen D.P.L _ _ (g.t χ)) (LB.invGen D.P.L _ _ (g.t χ))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ (g.t_gen χ))
      (DVR.invGen_isGen _ _ _ _ (g.t_gen χ))))
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  obtain ⟨v, hv, -⟩ := exists_gen_of_val_eq D.P.isLB _ _ g.q.left u hu (fun Z r r' z J hJ h => by
    obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D'.P.L D'.P.isLB z
    obtain ⟨h₁, h₂⟩ := ratio_invariant g g' Φ hp χ χ' hker r r' z J J' hJ hJ' h
    have hWeq : (fun k => r ≫ D'.Oφ g'.pG χ' k) = (fun k => r' ≫ D'.Oφ g'.pG χ' k) :=
      funext (Oφ_congr χ' g'.pG r r' h₁)
    rw [hu' Z r z J hJ, hu' Z r' z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv,
      hW Z r z J J' hJ hJ', hW Z r' z J J' hJ hJ', hWeq]
    calc _ = W Z z (fun k => r' ≫ D'.Oφ g'.pG χ' k) J J' *
          (val (g'.t χ') r z J' * (val (g.t χ) r z J)⁻¹) ^ 2 := by
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv, ofMul_pow]
          abel
      _ = _ := by
          rw [h₂]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv, ofMul_pow]
          abel)
  exact ⟨v, hv⟩

end GlobalTheory.SqCompare


open GlobalTheory.CoordCompare in
theorem GlobalTheory.SqCompare.c_two_comp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x)) := by
  intro R _ _ _ hR G _ _ hG D D' A A' U U' hL Φ w hw hΦ hpG xe hval x
  obtain ⟨hN, -, hC, -⟩ := hR
  have hp' : ∀ e, (U'.gt e).pG ≫ Φ.hom = (U.gt e).pG := fun e => Over.OverMorphism.ext (hpG e)
  have hmono : Mono Φ.hom.left := inferInstance
  set a := D'.toPre.c x ≫ Φ.hom
  set b := D.toPre.c (xe x)
  have desc : ∀ n, ∃ v : LB.Gen (LB.LinComb D.toPre.P.L
      (diffφ (D.toPre.prBe (maximalIdeal R) n) (a * a) (b * b)) ![1, -1, 1, -1]), v.IsGen := fun n => by
    obtain ⟨v, hv⟩ := GlobalTheory.SqCompare.sq_desc (U.gt n) (U'.gt n) Φ.hom (hp' n) w hw (xe x) x
      (fun Z r z J J' hJ hJ' h h' => hval n Z r z J J' hJ hJ' h h' x)
    exact GlobalTheory.SqCompare.sq_law D.toPre.P.isLB ⟨D.toPre.cub.t, D.toPre.cub.isGen⟩ _ _ _ v hv
  have hab : a * a = b * b := by
    have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.geomConnected
    have := D.toPre.P.isAb.proper
    have h := (sec_eq_zero_and_hom_eq_of_thickenings R (maximalIdeal R) (IsAdicComplete.le_jacobson_bot _)
      D.toPre.P.A).2 D.toPre.P.A (toUnit _ ≫ (a * a)) (toUnit _ ≫ (b * b)) fun n => by
        obtain ⟨v, hv⟩ := desc n
        have h₁ := thick_eq _ _ v hv
        have h₂ : (fstG (maximalIdeal R) n D.toPre.P.A).left ≫ (toUnit D.toPre.P.A).left =
            pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) n) ≫ thick R (maximalIdeal R) n := pullback.condition
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₂).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) h₁).trans ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ _) h₂.symm).trans (Category.assoc _ _ _))))))
    simpa using congrArg (η[D.toPre.P.A] ≫ ·) h
  have e1 : D'.toPre.c (2 • x) ≫ Φ.hom = a * a := by
    rw [two_nsmul, D'.toPre.c_add, padd, ← Hom.mul_def, MonObj.mul_comp]
  have e2 : D.toPre.c (xe (2 • x)) = b * b := by
    rw [map_nsmul, two_nsmul, D.toPre.c_add, padd, ← Hom.mul_def]
  rw [e1, e2, hab]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegenerationCharMapEqOnEvenCharactersStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationCharMap_eq_on_even_characters : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x)) := by
  first | exact @GlobalTheory.SqCompare.c_two_comp | exact GlobalTheory.SqCompare.c_two_comp | (intros; apply GlobalTheory.SqCompare.c_two_comp <;> assumption)
end
end

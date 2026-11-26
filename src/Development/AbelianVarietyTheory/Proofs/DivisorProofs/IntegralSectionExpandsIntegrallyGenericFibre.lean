module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineC1LogBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantNormFlatSectionEqNormDivNormDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingFrameUnitChangeToChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumDoubledTargetRestrictsToPair

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSectionExpandsIntegrallyGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSectionExpandsIntegrallyGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaSpecialise

namespace GlobalTheory.IntExpand

theorem gs_secPull {X Y Z : Scheme.{0}} {L : LB X} (s : L.Sec) (φ : Y ⟶ X) (r : Z ⟶ Y) (z : Z)
    (j : (L.pull φ).ι) (hz : r z ∈ (L.pull φ).U j) :
    gs r z ((L.pull φ).U j) ((GlobalTheory.Cartier.secPull s φ).f j) = gs (r ≫ φ) z (L.U (j PUnit.unit)) (s.f (j PUnit.unit)) := by
  unfold GlobalTheory.Cartier.secPull
  exact (gs_res r z _ hz _).trans (gs_pull r φ z _ (Set.mem_iInter.1 hz PUnit.unit) _)

theorem gs_secMaps {X Z : Scheme.{0}} {A B : LB X} {w : LB.Iso A B} {a : A.Sec} {b : B.Sec}
    (h : GlobalTheory.Cartier.SecMaps w a b) (r : Z ⟶ X) (z : Z) (p : B.ι) (q : A.ι) (hp : r z ∈ B.U p)
    (hq : r z ∈ A.U q) :
    gs r z (B.U p) (b.f p) = ↑(gm r z ((B.div A).U (p, q)) (w.s (p, q))) * gs r z (A.U q) (a.f q) := by
  have e := congrArg (gs r z (B.U p ⊓ A.U q)) (h.on p q (W := B.U p ⊓ A.U q) inf_le_left inf_le_right)
  have hm : r z ∈ B.U p ⊓ A.U q := ⟨hp, hq⟩
  rw [gs_mul r z _ hm] at e
  unfold resG at e
  rw [gs_res r z _ hm, gs_res r z _ hm, gs_res r z _ hm] at e
  rw [e, gs_unit r z _ (by exact hm)]
  rfl

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D A G), ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre), w₀.IsGen → ∀ (s : A.L.Sec) (σ : U.LG.L.Sec), GlobalTheory.Cartier.SecMaps w₀ (GlobalTheory.Cartier.secPull s U.gen.hom.left) (GlobalTheory.Cartier.secPull σ (pullback.fst G.hom (jK V))) → ∀ (C : Type) [Field C] [Algebra (FractionRing V) C], ∃ (σ₁ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (th : GlobalTheory.UT.SecA A C 1) (ϑ : Fam D.toPre C 1), (∀ (i : U.LG.L.ι) (h : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i), σ₁.f (fun _ => i) = resG _ h (σ.f i)) ∧ (∀ e, U.ExpandsAt e 1 σ₁ f) ∧ MBLow.IsPolAVSectionInverseImage A (TFK (R := V) C) s th ∧ U.ExpandsF C 1 w₀ th ϑ ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C α) (DegPre.famε 1) (ϑ.s α) (D.toPre.famφB α) (DegPre.famε 1) (f α) (DegPre.prB D.toPre C).left 1 := by
  intro V _ _ _ _ hV D A G _ _ hG U w₀ hw s σ hS C _ _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let σ₁ : H0 U.LG.L 1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.secOne U.LG.L σ
  have h1 : ∀ (i : U.LG.L.ι) (h : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i), σ₁.f (fun _ => i) = resG _ h (σ.f i) := fun i h =>
    fn_ext fun x hx => (ReciprocityTheory.ChartRestriction.G.PullbackSections.gs_pull1 U.LG.L (𝟙 _) σ (𝟙 _) x _ hx).trans (by
      rw [Category.comp_id]; exact (gs_res (𝟙 _) x h hx (σ.f i)).symm)
  let sK : U.SecK 1 := genericSec U.toUnifPre 1 σ₁
  have hsK : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => ((1 : ℕ) : ℤ)) sK (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) σ₁ (pullback.fst G.hom (jK V)) 1 :=
    (secScal_one_iff U.LG.isLB).2 fun y J hJ => (sval_pullOver _ _ _ _ hJ).symm
  obtain ⟨E, hE, -⟩ := (U.expand 1 le_rfl).1 sK
  obtain ⟨f, hf, hEf⟩ := GlobalTheory.ExpInt.main V ϖ hϖ D A G U.toUnifPre 1 σ₁ sK hsK E hE
  obtain ⟨ϑ, hϑ⟩ := GlobalTheory.FamBaseChange.main GlobalTheory.globalFns_holds V _ D 1 E f hEf C
  let th : GlobalTheory.UT.SecA A C 1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.pull1 A.L (snd (TFK (R := V) C) A.A).left s
  have hth : MBLow.IsPolAVSectionInverseImage A (TFK (R := V) C) s th := by
    refine fun i h => fn_ext fun x hx => ?_
    exact (ReciprocityTheory.ChartRestriction.G.PullbackSections.gs_pull1 A.L _ s (𝟙 _) x _ hx).trans (gs_appLE _ _ _ h (𝟙 _) x hx (s.f i)).symm
  have n₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  obtain ⟨u, hu, hu₁⟩ := GlobalTheory.ThetaBaseChange.exists_unpull hw _ n₁ rfl
  have ht : PSec u (fun _ : Fin 1 => (snd (TFK (R := V) C) A.A).left) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ))
      ((snd (TFK (R := V) C) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V)) th σ₁ := by
    intro Z r z p q hp hq
    obtain ⟨p0, rfl⟩ : ∃ p0, p = fun _ => p0 := ⟨p 0, funext fun k => congrArg p (Subsingleton.elim k 0)⟩
    obtain ⟨q0, rfl⟩ : ∃ q0, q = fun _ => q0 := ⟨q 0, funext fun k => congrArg q (Subsingleton.elim k 0)⟩
    have hp0 := hp 0
    have hq0 := hq 0
    have e1 := hu₁ Z (r ≫ (snd (TFK (R := V) C) A.A).left) z p0 q0 hp0 hq0
    have c2 : ((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) ≫ U.gen.hom.left =
        r ≫ (snd (TFK (R := V) C) A.A).left := by
      rw [Category.assoc, n₁, Category.comp_id]
    have mB : ((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) z ∈
        (U.LG.L.pull (pullback.fst G.hom (jK V))).U (fun _ => p0) := Set.mem_iInter.2 fun _ => hp0
    have mA : ((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) z ∈
        (A.L.pull U.gen.hom.left).U (fun _ => q0) := Set.mem_iInter.2 fun _ => by
      show (((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) ≫ U.gen.hom.left) z ∈ A.L.U q0
      rw [c2]; exact hq0
    have e2 := GlobalTheory.IntExpand.gs_secMaps hS _ z (fun _ => p0) (fun _ => q0) mB mA
    rw [GlobalTheory.IntExpand.gs_secPull _ _ _ _ _ mB, GlobalTheory.IntExpand.gs_secPull _ _ _ _ _ mA, c2] at e2
    refine (ReciprocityTheory.ChartRestriction.G.PullbackSections.gs_pull1 U.LG.L (𝟙 _) σ
      (r ≫ (snd (TFK (R := V) C) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V)) z (fun _ => p0)
      (Set.mem_iInter.2 fun _ => by exact hp0)).trans ?_
    refine Eq.trans ?_ (congrArg (fun t => _ * t)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.gs_pull1 A.L _ s r z (fun _ => q0) (Set.mem_iInter.2 fun _ => hq0)).symm)
    rw [Fin.prod_univ_one]
    dsimp only
    rw [Nat.cast_one, zpow_one, e1]
    have c1 : (r ≫ (snd (TFK (R := V) C) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V)) ≫ 𝟙 G.left =
        ((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) ≫ pullback.fst G.hom (jK V) := by
      simp only [Category.assoc, Category.comp_id]
    rw [c1]
    exact e2
  refine ⟨σ₁, f, th, ϑ, h1, hf, hth, expandsF_of_integral U.toUnifPre C hu₁ σ₁ f hf ϑ ?_ th ht, hϑ⟩
  intro α y J hJ
  exact (((secScal_one_iff D.toPre.P.isLB).1 (hϑ α)) y J hJ).symm

end GlobalTheory.IntExpand
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSectionExpandsIntegrallyGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralSection_expands_integrally_genericFibre : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D A G), ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre), w₀.IsGen → ∀ (s : A.L.Sec) (σ : U.LG.L.Sec), GlobalTheory.Cartier.SecMaps w₀ (GlobalTheory.Cartier.secPull s U.gen.hom.left) (GlobalTheory.Cartier.secPull σ (pullback.fst G.hom (jK V))) → ∀ (C : Type) [Field C] [Algebra (FractionRing V) C], ∃ (σ₁ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (th : GlobalTheory.UT.SecA A C 1) (ϑ : Fam D.toPre C 1), (∀ (i : U.LG.L.ι) (h : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i), σ₁.f (fun _ => i) = resG _ h (σ.f i)) ∧ (∀ e, U.ExpandsAt e 1 σ₁ f) ∧ MBLow.IsPolAVSectionInverseImage A (TFK (R := V) C) s th ∧ U.ExpandsF C 1 w₀ th ϑ ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C α) (DegPre.famε 1) (ϑ.s α) (D.toPre.famφB α) (DegPre.famε 1) (f α) (DegPre.prB D.toPre C).left 1 := by
  first | exact @GlobalTheory.IntExpand.main | exact GlobalTheory.IntExpand.main | (intros; apply GlobalTheory.IntExpand.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueWeightSectionFlagSpaceEqRuleAtFramedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueWeightSectionFlagSpaceEqRuleAtFramedPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHS.BridgeValue

theorem exists_gen_unit {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (P P' : FrPt Xo c S) (e : P'.x = P.x) : ∃ u : Sˣ, ∀ i, (e ▸ P'.s).f i = scal P.x (u : S) i * P.s.f i := by
  obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := P'
  dsimp only at e
  subst e
  exact gen_unit P.s s' P.gen t4'

end GlobalTheory.CompHS.BridgeValue

namespace GlobalTheory.CompHS.BridgeValue

theorem val_sec₀_eq_evR : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (la : AllWt.Weight Dw) (σ : c.F →+* ℂ) (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι) (φ : c.F →+* Γ(Y₀ TF.X Z, W)) (x : Sp Γ(Y₀ TF.X Z, W) ⟶ gen TF.Y) (hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x ≫ genι TF.Y) (hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U (i PUnit.unit)) (fr : GlobalTheory.ShFam.EigFrame TF.Y φ (x ≫ genι TF.Y)), (∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)), fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (TF.X.F.vecAt (i PUnit.unit) _ hz hx τ j)).left) → ∀ (ψ : Γ(Y₀ TF.X Z, W) →+* ℂ) (y : FrPt Xo c (CAt σ)), ψ.comp φ = σ → GlobalTheory.ShFam.BdArc.Matches fr ψ y → ∀ (g : AllWt.secZ Xo c (AllWt.exOf Dw la 0)) (hO : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ U₀ TF.X Z) (hi : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ TF.X Z la).U i), H0.val (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) i hO hi (sec₀ TF.X Z _ g) = toC (evR Xo c g.1 y) := by
  intro E _ _ _ H Dw l Xo c TF Z la σ W hW i φ x hx hz fr hfr ψ y hψ hm g hO hi
  let k := i PUnit.unit
  let ψ' : Γ(Y₀ TF.X Z, W) →+* CAt σ := ψ
  let q : Sp Γ(Y₀ TF.X Z, W) ⟶ TF.X.YY := (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z
  let z' : Sp (CAt σ) ⟶ TF.X.YY := spMap ψ' ≫ q
  have hz' : ⊤ ≤ z' ⁻¹ᵁ TF.X.F.U k := GlobalTheory.FlagMod.le_preimage_comp _ hz
  have hO' : ⊤ ≤ z' ⁻¹ᵁ flagOpen TF.X := fun s hs => hO hs
  have hpt : AllWt.ptF y = GlobalTheory.FlagMod.frX y := rfl
  have ex : spMap ψ' ≫ (x ≫ genι TF.Y) = z' ≫ TF.X.π := by
    rw [← hx]; exact (Category.assoc _ _ _).symm
  have hxy : GlobalTheory.FlagMod.frX y ≫ TF.Y.j = z' ≫ TF.X.π := by
    calc GlobalTheory.FlagMod.frX y ≫ TF.Y.j = (AllWt.ptF y ≫ TF.Y.jQ) ≫ genι TF.Y := by rw [Category.assoc]; rfl
    _ = spMap ψ' ≫ (x ≫ genι TF.Y) := by rw [hm.1, Category.assoc]
    _ = z' ≫ TF.X.π := ex
  obtain ⟨Q, hQ⟩ := TF.X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd y) hxy.symm k hz'
  have hv : ∀ τ j, GlobalTheory.FlagMod.frVec TF.Y y hxy τ j = GlobalTheory.FlagMod.frVec TF.Y Q hQ.over τ j := fun τ j => by
    rw [hQ.frVec_eq rfl hQ.over τ]
    refine (GlobalTheory.FlagMod.toModel_eq_iff _ _ _ _ _).2 ?_
    obtain ⟨w, h1, h2, h3⟩ := hm.2 τ j
    refine ⟨w, h1, h2, h3.trans ?_⟩
    rw [hfr τ j, ← TF.X.F.tanPull_vecAt k ψ' q hz hz' hx rfl ex]
    rfl
  have eQ : y.x = Q.x := by
    rw [← GlobalTheory.FlagMod.frX_fst, ← GlobalTheory.FlagMod.frX_fst,
      GlobalTheory.FlagMod.xF_ext (Y := TF.Y) (GlobalTheory.FlagMod.frX_snd y) (GlobalTheory.FlagMod.frX_snd Q) (hxy.trans hQ.over.symm)]
  obtain ⟨u0, hu0⟩ := exists_gen_unit Q y eQ
  let t : Ix Dw → (CAt σ)ˣ := fun ix => ix.elim u0 fun _ => 1
  have ht : FrBor t Q y := GlobalTheory.FlagMod.frBor_of_frVec (TF.X.F.inM hz' rfl) hQ.over hxy t (fun _ => 1)
    (fun _ => Matrix.blockTriangular_one) (fun _ i => Matrix.one_apply_eq i)
    (fun τ j => by
      rw [hv τ j]
      refine ((Fintype.sum_eq_single j fun j' hj' => ?_).trans ?_).symm
      · show (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) j' j • _ = 0
        rw [Matrix.one_apply_ne hj', zero_smul]
      · show (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) j j • _ = _
        rw [Matrix.one_apply_eq, one_smul]) (fun _ => hu0)
  have he := evR_eq_val_secOf (X := TF.X) g hO' hQ ht
  have hprod : (∏ ix, t ix ^ AllWt.exOf Dw la 0 ix) = 1 := by
    rw [Fintype.prod_option, GlobalTheory.FlagMod.exOf_none, zpow_zero, _root_.one_mul]
    exact Finset.prod_eq_one fun _ _ => one_zpow _
  rw [hprod, Units.val_one, _root_.one_mul] at he
  have key : ∀ (a b : Sp (CAt σ) ⟶ TF.X.YY), a = b → ∀ hOa hia hOb hib,
      H0.val (B := TF.X.LL (AllWt.exOf Dw la 0)) a k hOa hia (secOf TF.X _ g) =
        H0.val (B := TF.X.LL (AllWt.exOf Dw la 0)) b k hOb hib (secOf TF.X _ g) := by
    intro a b hab; subst hab; intros; rfl
  refine (H0.val_pull (inc₀ TF.X Z) le_rfl _ i hO hi (fun s hs => hO' hs) (fun s hs => hz' hs) _).trans ?_
  refine (key _ _ (Category.assoc _ _ _) _ _ hO' hz').trans ?_
  exact he.symm

end GlobalTheory.CompHS.BridgeValue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueWeightSectionFlagSpaceEqRuleAtFramedPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_weightSection_flagSpace_eq_rule_at_framedPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (la : AllWt.Weight Dw) (σ : c.F →+* ℂ) (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι) (φ : c.F →+* Γ(Y₀ TF.X Z, W)) (x : Sp Γ(Y₀ TF.X Z, W) ⟶ gen TF.Y) (hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x ≫ genι TF.Y) (hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U (i PUnit.unit)) (fr : GlobalTheory.ShFam.EigFrame TF.Y φ (x ≫ genι TF.Y)), (∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)), fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (TF.X.F.vecAt (i PUnit.unit) _ hz hx τ j)).left) → ∀ (ψ : Γ(Y₀ TF.X Z, W) →+* ℂ) (y : FrPt Xo c (CAt σ)), ψ.comp φ = σ → GlobalTheory.ShFam.BdArc.Matches fr ψ y → ∀ (g : AllWt.secZ Xo c (AllWt.exOf Dw la 0)) (hO : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ U₀ TF.X Z) (hi : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ TF.X Z la).U i), H0.val (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) i hO hi (sec₀ TF.X Z _ g) = toC (evR Xo c g.1 y) := by
  first | exact @GlobalTheory.CompHS.BridgeValue.val_sec₀_eq_evR | exact GlobalTheory.CompHS.BridgeValue.val_sec₀_eq_evR | (intros; apply GlobalTheory.CompHS.BridgeValue.val_sec₀_eq_evR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsComponentSamePeriodSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsComponentSamePeriodSpace
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open GlobalTheory.CxPts

namespace GlobalTheory.DetLine.SameIndex

theorem exists_lift {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j] (x : Sp ℂ ⟶ Y)
    (hx : x (IsLocalRing.closedPoint ℂ) ∈ Set.range j) : ∃ y : Sp ℂ ⟶ X, y ≫ j = x := by
  refine ⟨IsOpenImmersion.lift j x ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨p, rfl⟩
  obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact hx

theorem isHolTo_chart_symm {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}
    (c : AlgChart p σ d) {B : Set (ReciprocityTheory.L2DbarEstimates.V d)} (hB : IsOpen B) (h : B ⊆ c.e.target) :
    IsHolTo B fun b => (c.e.symm b).1 := fun U f => by
  refine ⟨?_, (c.holo U f).mono fun b hb => ⟨h hb.1, hb.2⟩⟩
  exact (c.e.continuousOn_symm.mono h).isOpen_inter_preimage hB (isOpen_ptsIn U)

theorem index_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (e : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (e.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i i' : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (P' : (Fu.Di i').La →+ (Fin g → ℂ)) (y y' : Sp ℂ ⟶ Xo.XF c) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsClosed (U : Set (Xo.XF c)) → IsOpenImmersion io → Set.range io = compactOf Y U → io ≫ genStr Y = B.str → y ≫ toF Xo c = spMap e → y' ≫ toF Xo c = spMap e → Set.range y ⊆ U → Set.range y' ⊆ U → IsPeriod (Fu.Di i) ty P → IsPeriod (Fu.Di i') ty P' → y ≫ toX Xo c = Fu.u i P → y' ≫ toX Xo c = Fu.u i' P' → i = i' := by
  intro E _ _ _ H D l Xo c O _ β Y U e g ty Fu i i' P P' y y' B io _ hio hr hs hy hy' hU hU' hP hP' hu hu'
  classical
  haveI := Y.jQ_open
  let W : B.X.Opens := io ⁻¹ᵁ Y.jQ.opensRange
  haveI : Nonempty (Sp ℂ ⟶ Xo.XF c) := ⟨y⟩
  have hl : ∀ z : CxPts B.str e, z ∈ ptsIn B.str e W → ∃ w : Sp ℂ ⟶ Xo.XF c, w ≫ Y.jQ = z.1 ≫ io :=
    fun z hz => exists_lift Y.jQ _ (mem_ptsIn.1 hz)
  choose! w hw using hl
  have hwσ : ∀ z ∈ ptsIn B.str e W,
      (w z ≫ toX Xo c) ≫ Xo.s = spMap (e.comp (IntermediateField.inclusion c.le).toRingHom) := fun z hz => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← Y.jQ_over, ← Category.assoc, hw z hz,
      ← OpenReg.spMap_comp, Category.assoc _ io]
    exact congrArg (· ≫ _) ((congrArg (z.1 ≫ ·) hs).trans z.2)
  have hex : ∀ z : CxPts B.str e, ∃ k : Fin Fu.n, z ∈ ptsIn B.str e W →
      ∃ Q, IsPeriod (Fu.Di k) ty Q ∧ Fu.u k Q = w z ≫ toX Xo c := fun z => by
    by_cases hz : z ∈ ptsIn B.str e W
    · obtain ⟨k, Q, h⟩ := Fu.onto _ (hwσ z hz)
      exact ⟨k, fun _ => ⟨Q, h⟩⟩
    · exact ⟨i, fun h => absurd h hz⟩
  choose k hk using hex
  have hcont : ContinuousOn k (ptsIn B.str e W) := by
    intro z₀ hz₀
    obtain ⟨ch, hch⟩ := AlgChart.exists_mem_source (p := B.str) (σ := e) (D := B.dim) z₀
    let T := ch.e.target ∩ ch.e.symm ⁻¹' ptsIn B.str e W
    have hT : IsOpen T := ChartGlue.isOpen_over ch.e (isOpen_ptsIn W)
    have h1 : IsHolTo T fun b => w (ch.e.symm b) :=
      HorLift.isHolTo_of_comp_open Y.jQ (LocLift.isHolTo_congr
        (LocLift.isHolTo_comp_hom (isHolTo_chart_symm ch hT Set.inter_subset_left) io) fun b hb => hw _ hb.2)
    let φ : ReciprocityTheory.L2DbarEstimates.V B.dim ≃L[ℂ] (Fin B.dim → ℂ) := EuclideanSpace.equiv (Fin B.dim) ℂ
    have hTφ : IsOpen (φ.symm ⁻¹' T) := hT.preimage φ.symm.continuous
    obtain ⟨B₁, k₀, Q, hB₁, hb₁, hsub, hQ, hQu⟩ := Fu.lift _ (φ.symm ⁻¹' T)
      (fun t => w (ch.e.symm (φ.symm t)) ≫ toX Xo c) hTφ (fun t ht => hwσ _ ht.2)
      (LocLift.isHolTo_comp (LocLift.isHolTo_comp_hom h1 _) hTφ φ.symm.differentiableOn fun _ h => h)
      (φ (ch.e z₀)) (by
        rw [Set.mem_preimage, φ.symm_apply_apply]
        exact ChartGlue.mem_over ch.e hch hz₀)
    have hc : ContinuousAt (fun z => φ (ch.e z)) z₀ := φ.continuous.continuousAt.comp (ch.e.continuousAt hch)
    have hev : k =ᶠ[nhds z₀] fun _ => k₀ := by
      filter_upwards [hc.eventually (hB₁.mem_nhds hb₁), ch.e.open_source.mem_nhds hch,
        (isOpen_ptsIn W).mem_nhds hz₀] with z h₁ h₂ h₃
      obtain ⟨Q', hQ', hQu'⟩ := hk z h₃
      refine Fu.disj _ _ Q' (Q _) hQ' (hQ.1 _ h₁) (hQu'.trans ?_)
      rw [hQu _ h₁, φ.symm_apply_apply, ch.e.left_inv h₂]
    exact (continuousAt_const.congr hev.symm).continuousWithinAt
  have hpt : ∀ (j : Fin Fu.n) (R : (Fu.Di j).La →+ (Fin g → ℂ)) (x : Sp ℂ ⟶ Xo.XF c), x ≫ toF Xo c = spMap e →
      Set.range x ⊆ U → IsPeriod (Fu.Di j) ty R → x ≫ toX Xo c = Fu.u j R → ∃ z ∈ ptsIn B.str e W, k z = j := by
    intro j R x hx hxU hR hxu
    obtain ⟨z, hz⟩ := exists_lift io (x ≫ Y.jQ) (by
      rw [hr]
      exact subset_closure ⟨_, hxU ⟨_, rfl⟩, rfl⟩)
    have hze : z ≫ B.str = spMap e := by
      rw [← hs, ← Category.assoc, hz, Category.assoc]
      exact (congrArg (x ≫ ·) Y.jQ_over).trans hx
    have hzW : (⟨z, hze⟩ : CxPts B.str e) ∈ ptsIn B.str e W :=
      mem_ptsIn.2 ⟨x (IsLocalRing.closedPoint ℂ), (congrArg (fun f => f (IsLocalRing.closedPoint ℂ)) hz).symm⟩
    refine ⟨_, hzW, ?_⟩
    obtain ⟨Q', hQ', hQu'⟩ := hk _ hzW
    have hwx : w ⟨z, hze⟩ = x := (cancel_mono Y.jQ).1 ((hw _ hzW).trans hz)
    exact Fu.disj _ _ Q' R hQ' hR (hQu'.trans (by rw [hwx, hxu]))
  obtain ⟨z, hz, rfl⟩ := hpt i P y hy hU hP hu
  obtain ⟨z', hz', rfl⟩ := hpt i' P' y' hy' hU' hP' hu'
  exact (GlobalTheory.T.isPreconnected_complexPoints_open_variety c.F B e W).constant hcont hz hz'

end GlobalTheory.DetLine.SameIndex
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsComponentSamePeriodSpaceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexPoints_component_same_periodSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (e : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (e.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i i' : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (P' : (Fu.Di i').La →+ (Fin g → ℂ)) (y y' : Sp ℂ ⟶ Xo.XF c) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsClosed (U : Set (Xo.XF c)) → IsOpenImmersion io → Set.range io = compactOf Y U → io ≫ genStr Y = B.str → y ≫ toF Xo c = spMap e → y' ≫ toF Xo c = spMap e → Set.range y ⊆ U → Set.range y' ⊆ U → IsPeriod (Fu.Di i) ty P → IsPeriod (Fu.Di i') ty P' → y ≫ toX Xo c = Fu.u i P → y' ≫ toX Xo c = Fu.u i' P' → i = i' := by
  first | exact @GlobalTheory.DetLine.SameIndex.index_eq | exact GlobalTheory.DetLine.SameIndex.index_eq | (intros; apply GlobalTheory.DetLine.SameIndex.index_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroFibresUnitMultipleThetaSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroFibresUnitMultipleThetaSeries
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven.ThetaNorm

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D A G), ∀ (σ : U.LG.L.Sec) (σ₁ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α), NzFib σ → (∀ (i : U.LG.L.ι) (h : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i), σ₁.f (fun _ => i) = resG _ h (σ.f i)) → (∀ e, U.ExpandsAt e 1 σ₁ f) → ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (ϑ : Fam D.toPre C 1) (c : C), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C α) (DegPre.famε 1) (ϑ.s α) (D.toPre.famφB α) (DegPre.famε 1) (f α) (DegPre.prB D.toPre C).left 1) → ν.FamV ϑ (c • N.vth) → ‖c‖ = 1 := by
  intro V _ _ _ _ hc D A G _ _ hG U σ σ₁ f hNz hch hE C _ _ _ _ _ _ hC N ν hI ϑ c hϑ hV
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hL4 : Laws4 := GlobalTheory.allSixLaws.2.2.2.1
  have hS : SecBaseChangeSt := hL.secBaseChange
  have h1 : ReciprocityTheory.ChartRestriction.G.DVR.NonzeroOnSpecial U σ₁ := by
    obtain ⟨z, hz, hzn⟩ := hNz (IsLocalRing.closedPoint V)
    refine GlobalTheory.ThetaUnit.nonzeroOnSpecial_of_mem U σ₁ z hz ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hzn
    have hle : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i :=
      fun y hy => Set.mem_iInter.1 hy 0
    have hzi : z ∈ U.LG.L.U i := G.left.basicOpen_le _ hi
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, ?_⟩
    rw [hch i hle]
    change z ∈ G.left.basicOpen ((G.left.presheaf.map (homOfLE hle).op) (σ.f i))
    rw [Scheme.basicOpen_res]
    exact ⟨fun _ ⟨k, hk⟩ => hk ▸ hzi, hi⟩
  have hCL : CLND V := (GlobalTheory.ThetaCompare.clnd_iff_of_dvr V).2 hc
  obtain ⟨f', hf', hgen'⟩ := ReciprocityTheory.ChartRestriction.G.DVR.isTheta_of_nonzeroOnSpecial' hL hL4 hCL rfl U σ₁ h1 0
  have hgen := GlobalTheory.ThetaCompare.secBGenerates_of_expandsAt hS le_rfl U.toUnifPre hf' (hE 0) hgen'
  obtain ⟨g, hg⟩ := GlobalTheory.ThetaCompare.exists_corr_right D.toPre ν.th
  have hgg := (GlobalTheory.ThetaCompare.generates_iff_secBGenerates hS hg).1 (fun s => ν.th_gen s)
  have hgs := (GlobalTheory.ThetaCompare.secBGenerates_iff_smul (g : GlobalTheory.ConstFam.SecBMod D.toPre 1 0)).1 hgg
  have hfs := (GlobalTheory.ThetaCompare.secBGenerates_iff_smul ((f 0 : D.toPre.SecB 1 0) : GlobalTheory.ConstFam.SecBMod D.toPre 1 0)).1 hgen
  obtain ⟨u, hu⟩ := (GlobalTheory.ThetaCompare.generates_iff_unit_smul (fun s => (hgs s).exists) _).1 (fun s => (hfs s).exists)
  have hum : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul D.toPre.P.A.hom (u : V) (f 0) g :=
    (GlobalTheory.ThetaUnit.secIsMul_iff _ _ _ _).2 hu

  let z : Sp C := IsLocalRing.closedPoint C
  have hJ := GlobalTheory.Ex.FamVal.good ν z
  have hcst : ∀ a : C, cst (𝟙 (Sp C)) z a = toStk z a := fun a => by
    rw [cst, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_eq _ _ ⊤ trivial, toStk]
    rfl
  have hc0 : N.c 0 = 1 := by
    have h := N.c_add 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have hx : ∀ x, c * N.th x * ν.rg = algebraMap (FractionRing V) C (algebraMap V _ (u : V)) * (N.th x * ν.rg) := by
    intro x
    have H := (GlobalTheory.Ex.FamVal.famV_iff ν z ϑ _).1 hV 0 x
    have e1 := ReciprocityTheory.ChartRestriction.G.H1.sval_scal (hϑ 0) (GlobalTheory.Ex.FamVal.pt ν x).left z hJ
    have e2 := GlobalTheory.IndivisibleSection.sval_of_secIsMul hum
      ((GlobalTheory.Ex.FamVal.pt ν x).left ≫ (DegPre.prB D.toPre C).left) z hJ
    have e3 := ReciprocityTheory.ChartRestriction.G.H1.sval_scal hg ((GlobalTheory.Ex.FamVal.pt ν x).left ≫ (DegPre.prB D.toPre C).left) z hJ
    have e4 : toStk z (N.th x * ν.rg) = sval ν.th (ν.eA x).left z ν.J :=
      (congrArg (toStk z) (ν.th_eq x)).trans (GlobalTheory.Ex.FamVal.toStk_sF hJ _ _)
    have ep : (GlobalTheory.Ex.FamVal.pt ν x).left ≫ (DegPre.prB D.toPre C).left = (ν.eA x).left := by
      rw [← Over.comp_left, lift_snd]
    rw [map_zero] at H
    rw [Category.comp_id, ep, ← e4] at e3
    rw [ep] at e2
    rw [e1, ep, e2, ← e3] at H
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, pow_one] at H
    have ec : cst ((ν.eA x).left ≫ D.toPre.P.A.hom) z (u : V) =
        toStk z (algebraMap (FractionRing V) C (algebraMap V _ (u : V))) := by
      have ew : (ν.eA x).left ≫ D.toPre.P.A.hom =
          (𝟙 (Sp C) ≫ spMap (algebraMap (FractionRing V) C)) ≫ spMap (algebraMap V (FractionRing V)) := by
        rw [Category.id_comp]; exact Over.w (ν.eA x)
      rw [ew, cst_comp, cst_comp, hcst]
    have ev : N.vth 0 x = N.th x := by
      simp [NumD.vth, N.ψ_zero, hc0]
    rw [ev, ← GlobalTheory.Ex.FamVal.rg_eq, ec, ← map_mul, ← map_mul] at H
    exact (toStk z).injective H
  have hL2 : Laws2 := GlobalTheory.abelianSchemeLaws_all.2
  have hB := GlobalTheory.Ex.brFam hL hL2 V D.toPre D.psi_even D.tau_bimult C N ν 1 le_rfl
  obtain ⟨x, hx0⟩ : ∃ x, N.th x ≠ 0 := by
    by_contra hno
    push_neg at hno
    obtain ⟨s, f0, hf0, hne⟩ := hB.2.2.2.1
    obtain ⟨c', hc'⟩ := hB.2.2.2.2.1 s f0 hf0
    refine hne ?_
    rw [hc']
    funext α y
    simp [NumD.vth, hno]
  have hcu : c = algebraMap (FractionRing V) C (algebraMap V _ (u : V)) := by
    have h := hx x
    rw [_root_.mul_assoc] at h
    exact mul_right_cancel₀ (mul_ne_zero hx0 (GlobalTheory.Ex.FamVal.rg_ne ν)) h
  have n1 := hC.1 (u : V)
  have n2 := hC.1 ((u⁻¹ : Vˣ) : V)
  have hprod : ‖algebraMap (FractionRing V) C (algebraMap V _ (u : V))‖ *
      ‖algebraMap (FractionRing V) C (algebraMap V _ ((u⁻¹ : Vˣ) : V))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
  rw [hcu]
  nlinarith [norm_nonneg (algebraMap (FractionRing V) C (algebraMap V _ ((u⁻¹ : Vˣ) : V))),
    norm_nonneg (algebraMap (FractionRing V) C (algebraMap V _ (u : V)))]

end GlobalTheory.KeyEven.ThetaNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroFibresUnitMultipleThetaSeriesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_nonzero_fibres_unit_multiple_thetaSeries : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D A G), ∀ (σ : U.LG.L.Sec) (σ₁ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α), NzFib σ → (∀ (i : U.LG.L.ι) (h : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i), σ₁.f (fun _ => i) = resG _ h (σ.f i)) → (∀ e, U.ExpandsAt e 1 σ₁ f) → ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (ϑ : Fam D.toPre C 1) (c : C), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C α) (DegPre.famε 1) (ϑ.s α) (D.toPre.famφB α) (DegPre.famε 1) (f α) (DegPre.prB D.toPre C).left 1) → ν.FamV ϑ (c • N.vth) → ‖c‖ = 1 := by
  first | exact @GlobalTheory.KeyEven.ThetaNorm.main | exact GlobalTheory.KeyEven.ThetaNorm.main | (intros; apply GlobalTheory.KeyEven.ThetaNorm.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeIffUniformiserReductionVanishes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeIffUniformiserReductionVanishes
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
namespace GlobalTheory.DilKer

open GlobalTheory.StdFrames (cpt)

theorem frMapO_dil {D : D7} (i : Fin D.R.m) (βS : GL (Fin (Vc D i).rank) (EAf D)) (βT : GL (Fin (Wc D i).rank) (EAf D))
    (a : D.host.E) (z : WO (Vc D i) (Wc D i)) :
    frMapO (Vc D i) (Wc D i) βS βT (dil i a z) = eToEAf D a • frMapO (Vc D i) (Wc D i) βS βT z := by
  have h : (dil i a z).map (toEAf D) = eToEAf D a • z.map (toEAf D) := by
    ext k l
    simp only [dil, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, GlobalTheory.IdemIntegral.toEAf_incA]
  simp only [frMapO, h, Matrix.mul_smul, Matrix.smul_mul]

theorem isHalf_dil {D : D7} (i : Fin D.R.m) (e : AE D) (a : D.host.E) {z : WO (Vc D i) (Wc D i)} (hz : IsHalf e z) :
    IsHalf e (dil i a z) := fun k l => by
  simp only [dil, Matrix.map_apply]
  rw [mul_left_comm, hz k l]

theorem frMapO_half {D : D7} (i : Fin D.R.m) (βS : GL (Fin (Vc D i).rank) (EAf D)) (βT : GL (Fin (Wc D i).rank) (EAf D))
    {e : AE D} {z : WO (Vc D i) (Wc D i)} (hz : IsHalf e z) (k l) :
    toEAf D e * frMapO (Vc D i) (Wc D i) βS βT z k l = frMapO (Vc D i) (Wc D i) βS βT z k l := by
  have h : z.map (toEAf D) = toEAf D e • z.map (toEAf D) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, ← RingHom.map_mul, hz a b]
  have h2 : frMapO (Vc D i) (Wc D i) βS βT z = toEAf D e • frMapO (Vc D i) (Wc D i) βS βT z := by
    conv_lhs => rw [frMapO, h]
    simp only [frMapO, Matrix.mul_smul, Matrix.smul_mul]
  conv_rhs => rw [h2]
  rfl

theorem val_cpt_eToEAf {D : D7} (PP : Pl D.host.E) (x : D.host.E) :
    Valued.v (cpt PP (eToEAf D x)) = PP.valuation D.host.E x := by
  have : eToEAf D x = GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D x := rfl
  rw [this, GlobalTheory.AdIsom.cpt_inc, Formalism.UG.P.levelaf_valued_algebraMap]

theorem mem_int_of_mul {D : D7} {Q : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e Q) {ϖ : 𝓞 D.host.E}
    (hϖ : ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) {m : EAf D} (hm : toEAf D e * m = m)
    (hy : eToEAf D (ϖ : D.host.E) * m ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hr : ∀ PP ∈ Q, Valued.v (cpt PP (eToEAf D (ϖ : D.host.E) * m)) < 1) :
    m ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  refine (GlobalTheory.AdIsom.mem_OA m).2 fun P => ?_
  by_cases hP : P ∈ Q
  · have h1 := hr P hP
    rw [RingHom.map_mul, Valuation.map_mul, val_cpt_eToEAf, GlobalTheory.HeckeDetChar.val_unif (hϖ P hP).1 (hϖ P hP).2] at h1
    by_cases h0 : Valued.v (cpt P m) = 0
    · rw [h0]; exact zero_le'
    obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v (cpt P m) = WithZero.exp k := ⟨_, (WithZero.exp_log h0).symm⟩
    rw [hk] at h1 ⊢
    rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  · have h0 : cpt P (toEAf D (∑ PP ∈ Q, es PP)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum]
      exact Finset.sum_eq_zero fun PP hPP => (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes PP hPP)).2 P fun h => hP (h ▸ hPP)
    have := congrArg (cpt P) hm
    rw [RingHom.map_mul, h0, zero_mul] at this
    rw [← this, Valuation.map_zero]
    exact zero_le'

theorem mem_localLattice_iff_redM : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : WO (Vc D i) (Wc D i), IsHalf eQ z → dil i (ϖ : D.host.E) z ∈ lattice₂ R i → (z ∈ lattice₂ R i ↔ ∀ PP ∈ Q, redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) z)) = 0) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i hV Q hQ eQ he ϖ hϖ0 hϖ z hz hϖz
  have hI := GlobalTheory.T.mem_completedPairLattice_iff_frameMatrix_integral_on_half D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ he
  rw [frMapO_dil]
  constructor
  · intro hzL PP hPP
    have hM := (hI z hz).2 hzL
    ext k l
    have hϖi : eToEAf D (ϖ : D.host.E) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [← GlobalTheory.IdemIntegral.toEAf_incA]
      exact GlobalTheory.IdemIntegral.toEAf_mem_of_finPart (GlobalTheory.SplitIndex.finPart_incA_mem ϖ)
    have hint : eToEAf D (ϖ : D.host.E) * frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) z k l ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E := mul_mem hϖi (hM k l)
    simp only [redM, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, dif_pos hint]
    refine (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP ⟨_, hint⟩).2 ?_
    change Valued.v (cpt PP (eToEAf D (ϖ : D.host.E) * _)) < 1
    rw [RingHom.map_mul, Valuation.map_mul, val_cpt_eToEAf, GlobalTheory.HeckeDetChar.val_unif (hϖ PP hPP).1 (hϖ PP hPP).2]
    calc WithZero.exp (-1 : ℤ) * Valued.v (cpt PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) z k l))
        ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr; exact (GlobalTheory.AdIsom.mem_OA _).1 (hM k l) PP
      _ < 1 := by rw [mul_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  · intro hred
    have hN := (hI _ (isHalf_dil i eQ _ hz)).2 hϖz
    rw [frMapO_dil] at hN
    have hN' : ∀ k l, eToEAf D (ϖ : D.host.E) * frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) z k l ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E := fun k l => hN k l
    refine (hI z hz).1 fun k l => mem_int_of_mul he hϖ (frMapO_half i _ _ hz k l) (hN' k l) fun PP hPP => ?_
    have h1 := congrFun (congrFun (hred PP hPP) k) l
    simp only [redM, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, dif_pos (hN' k l)] at h1
    exact (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP ⟨_, hN' k l⟩).1 h1

end GlobalTheory.DilKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeIffUniformiserReductionVanishesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_lattice_iff_uniformiser_reduction_vanishes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : WO (Vc D i) (Wc D i), IsHalf eQ z → dil i (ϖ : D.host.E) z ∈ lattice₂ R i → (z ∈ lattice₂ R i ↔ ∀ PP ∈ Q, redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) z)) = 0) := by
  first | exact @GlobalTheory.DilKer.mem_localLattice_iff_redM | exact GlobalTheory.DilKer.mem_localLattice_iff_redM | (intros; apply GlobalTheory.DilKer.mem_localLattice_iff_redM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingDeterminedAtGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingDeterminedAtGenericPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilGeneric

open GlobalTheory.CechPic GlobalTheory.DiagPairing

theorem weilIs_of_generic : ∀ (O : Type) [CommRing O] [IsDomain O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (A ⊗ A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (N : ℕ), 0 < N → IsUnit (N : O) → ∀ (u v : 𝟙_ (Over (Sp O)) ⟶ A), u ^ N = 1 → v ^ N = 1 → ∀ (c : Oˣ) (k₀ : Type) [Field k₀] (j : O →+* k₀), Function.Injective j → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap j)) ≫ u) (toUnit (Over.mk (spMap j)) ≫ v) (unitOn (Units.map j.toMonoidHom c)) → ∀ (k : Type) [Field k] (ρ : O →+* k), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap ρ)) ≫ u) (toUnit (Over.mk (spMap ρ)) ≫ v) (unitOn (Units.map ρ.toMonoidHom c)) := by
  intro O _ _ A _ _ hA P hP h₁ h₂ hamp N hN _ u v hu hv c k₀ _ j hj H k _ ρ
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  let pc {T : Over (Sp O)} (a b : T ⟶ A) : Pic T.left := pull (lift a b).left (cls P hP)
  have hB : ∀ (T : Over (Sp O)) (x x' y : T ⟶ A), pc (x * x') y = pc x y + pc x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG (Sp O) A _ hA hD hamp P hP h₁ h₂
        T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over (Sp O)) (x y y' : T ⟶ A), pc x (y * y') = pc x y + pc x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG (Sp O) A _ hA hD hamp P hP h₁ h₂
        T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have pc_pow_left : ∀ {T : Over (Sp O)} (x y : T ⟶ A) (k : ℕ), pc (x ^ k) y = k • pc x y := by
    intro T x y k
    have one : pc (1 : T ⟶ A) y = 0 := by
      have e := hB T 1 1 y
      rwa [_root_.mul_one, left_eq_add] at e
    induction k with
    | zero => rw [pow_zero, one, zero_smul]
    | succ k ih => rw [pow_succ, hB, ih, succ_nsmul]
  have pc_pow_right : ∀ {T : Over (Sp O)} (x y : T ⟶ A) (k : ℕ), pc x (y ^ k) = k • pc x y := by
    intro T x y k
    have one : pc x (1 : T ⟶ A) = 0 := by
      have e := hB' T x 1 1
      rwa [_root_.mul_one, left_eq_add] at e
    induction k with
    | zero => rw [pow_zero, one, zero_smul]
    | succ k ih => rw [pow_succ, hB', ih, succ_nsmul]
  have exists_theta_diag : ∀ {k : ℕ} {T : Over (Sp O)} (x : T ⟶ A), x ^ k = 1 →
      ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) k T, θ.pt = x := by
    intro k T x hx
    have e : ∀ g : T ⊗ A ⟶ A, pull g.left (cls _ hD) = pc g g := fun g => by
      rw [cls_pull hP, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
    have ha : (fst T A ≫ x) ^ k = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    have h1 : k • pc (fst T A ≫ x) (fst T A ≫ x) = 0 := by
      rw [← pc_pow_left, ha]
      have e := hB (T ⊗ A) 1 1 (fst T A ≫ x)
      rwa [_root_.mul_one, left_eq_add] at e
    have h2 : k • pc (fst T A ≫ x) (snd T A) = 0 := by
      rw [← pc_pow_left, ha]
      have e := hB (T ⊗ A) 1 1 (snd T A)
      rwa [_root_.mul_one, left_eq_add] at e
    have h3 : k • pc (snd T A) (fst T A ≫ x) = 0 := by
      rw [← pc_pow_right, ha]
      have e := hB' (T ⊗ A) (snd T A) 1 1
      rwa [_root_.mul_one, left_eq_add] at e
    obtain ⟨t, ht⟩ : ∃ t : LB.Gen (Out.thetaLB A (P.pull (lift (𝟙 A) (𝟙 A)).left) k x), t.IsGen := by
      refine (cls_eq_zero_iff (LB.isLB_linComb hD _ _)).1 ?_
      rw [cls_linComb hD, Fin.sum_univ_two]
      show (k : ℤ) • pull (snd T A).left _ + (-(k : ℤ)) • pull ((fst T A ≫ x) * snd T A).left _ = 0
      rw [e, e, hB, hB', hB']
      simp only [natCast_zsmul, neg_smul, smul_add, h1, h2, h3]
      abel
    exact ⟨⟨x, t, ht⟩, rfl⟩
  have lifts : ∀ z : 𝟙_ (Over (Sp O)) ⟶ A, z ^ N = 1 → ∀ p : (𝟙_ (Over (Sp O))).left, ∃ V : (𝟙_ (Over (Sp O))).left.Opens,
      p ∈ V ∧ ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (Out.overRes V), θ.pt = Out.overResι V ≫ z :=
    fun z hz p => by
      obtain ⟨θ, hθ⟩ := exists_theta_diag (k := N) (Out.overResι ⊤ ≫ z)
        (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
      exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG hA hD (lifts u hu) (lifts v hv)
  obtain ⟨w, rfl⟩ := GlobalTheory.Ex.Specialise.unitOn_bijective.2 c₀
  have spec : ∀ (F : Type) [Field F] (σ : O →+* F), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N
      (toUnit (Over.mk (spMap σ)) ≫ u) (toUnit (Over.mk (spMap σ)) ≫ v) (unitOn (Units.map σ.toMonoidHom w)) := by
    intro F _ σ
    have hN' := CommPairing.weilIs_pull hG hA hD (toUnit (Over.mk (spMap σ))) hc₀
    have hl : (toUnit (Over.mk (spMap σ))).left = spMap σ := rfl
    rw [hl, GlobalTheory.Ex.Specialise.map_unitOn] at hN'
    exact hN'
  have e := GlobalTheory.Ex.Specialise.unitOn_bijective.1 (CommutatorPairing.weilIs_unique hG hA hD (spec k₀ j) H)
  have e' : w = c := Units.map_injective hj e
  rw [← e']
  exact spec k ρ

end GlobalTheory.WeilGeneric

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingDeterminedAtGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_determined_at_genericPoint : ∀ (O : Type) [CommRing O] [IsDomain O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (A ⊗ A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (N : ℕ), 0 < N → IsUnit (N : O) → ∀ (u v : 𝟙_ (Over (Sp O)) ⟶ A), u ^ N = 1 → v ^ N = 1 → ∀ (c : Oˣ) (k₀ : Type) [Field k₀] (j : O →+* k₀), Function.Injective j → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap j)) ≫ u) (toUnit (Over.mk (spMap j)) ≫ v) (unitOn (Units.map j.toMonoidHom c)) → ∀ (k : Type) [Field k] (ρ : O →+* k), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap ρ)) ≫ u) (toUnit (Over.mk (spMap ρ)) ≫ v) (unitOn (Units.map ρ.toMonoidHom c)) := by
  first | exact @GlobalTheory.WeilGeneric.weilIs_of_generic | exact GlobalTheory.WeilGeneric.weilIs_of_generic | (intros; apply GlobalTheory.WeilGeneric.weilIs_of_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledTargetWeilTransportRestrictFirstFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledTargetWeilTransportRestrictFirstFactor
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DblTargetRestrict

theorem restrict_boxFun : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
      ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E) (hA : JA = JTᵀ),
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
        GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
          Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ omp : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
          Module.End ℂ ((κ ⊕ κ → AF F) → ℂ),
        GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) ωd omp →
      ∀ (g : UG (cA σ) (incM F JA)) (gd : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)),
        gd.1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1.1 0 0 1) →
        ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omp (gd, 1) (boxFun φ₁ φ₂) = boxFun (om (g, 1) φ₁) φ₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ χS χT _ _ _ _ ω hω JA JB ξ hA hB' κ _ co hrat om hom
    ωd hωd omp homp g gd hgd φ₁ hφ₁ φ₂ hφ₂
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := hω.std.1
  let h : Formalism.IndefR.DatumF.GAF σ JT := ⟨g.1, GlobalTheory.TransportF.mem_HR_target hA g⟩
  let hd : Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) := ⟨gd.1, GlobalTheory.TransportF.mem_HR_target rfl gd⟩
  have hh : Formalism.IndefR.DatumF.mtF σ JT h = g.1.1 := rfl
  have hhd : Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hd = gd.1.1 := rfl
  have h1 : Formalism.IndefR.DatumF.mtF σ JS 1 = ((1 : UG (cA σ) (incM F JB))⁻¹).1.1ᵀ := by
    show (Formalism.IndefR.DatumF.matHomF σ JS 1).1 = _
    rw [map_one, inv_one]
    first | rfl | simp | exact Matrix.transpose_one.symm
  have hdm : Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hd =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ JT h) 0 0 1) := by
    rw [hhd, hgd, hh]
  have t1 := hom g 1 1 h hh h1 φ₁ hφ₁
  have hΦ := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ φ₁ hφ₁ φ₂ hφ₂
  have hΦ' := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ _ t1.1 φ₂ hφ₂
  have t2 := homp gd 1 1 hd hhd h1 _ hΦ
  have hφ₂' := GlobalTheory.T.adelicSchwartzSpace_closed_under_conj_reflection F κ φ₂ hφ₂
  let τ := Fintype.equivFin κ
  have he : ∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' =
      GlobalTheory.ThetaTransform.symV (GlobalTheory.TransportF.numCoordF co τ w) (GlobalTheory.TransportF.numCoordF co τ w') := fun w w' => by
    rw [GlobalTheory.TransportF.symplOF_eq_symp hA hB', co.form]
    simp only [GlobalTheory.ThetaTransform.symV, GlobalTheory.TransportF.numCoordF_apply, comp_equiv_dotProduct_comp_equiv]
  have hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card κ) → F,
      GlobalTheory.TransportF.numCoordF co τ (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨y ∘ τ.symm, z ∘ τ.symm, by rw [GlobalTheory.TransportF.numCoordF_apply]; erw [h]; rfl⟩
  have thf : ∀ Φ ∈ schA F κ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ
      (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := fun Φ hΦ => by
    rw [GlobalTheory.TransportF.thetaTr_eqF co τ]
    exact GlobalTheory.T.isThetaFunction_thetaTransform_rational_coords_CM F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hω.std _ (GlobalTheory.TransportF.numCoordF co τ) he hr _
      (GlobalTheory.TransportF.comp_mem_schA τ hΦ)
  have key := t2.2.trans ((congrArg (ωd (1, hd)) (GlobalTheory.T.thetaTransform_doubledTarget_boxProduct F E σ B hB hω.std nS nT JT JA JB ξ hA κ co φ₁ hφ₁ φ₂ hφ₂)).trans
    ((GlobalTheory.T.weilDatum_doubled_target_restricts_to_pair F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ χS χT ω hω ωd hωd h hd hdm _ _ (thf φ₁ hφ₁) (thf _ hφ₂')).trans
      ((congrArg (fun f => GlobalTheory.DblTargetDelta.deltaT f
        (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (fun x => starRingEnd ℂ (φ₂ (-x))))) t1.2.symm).trans
        (GlobalTheory.T.thetaTransform_doubledTarget_boxProduct F E σ B hB hω.std nS nT JT JA JB ξ hA κ co _ t1.1 φ₂ hφ₂).symm)))
  let τ' := Fintype.equivFin (κ ⊕ κ)
  have key' := (GlobalTheory.TransportF.thetaTr_eqF (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) τ' ((omp (gd, 1)) (boxFun φ₁ φ₂))).symm.trans
    (key.trans (GlobalTheory.TransportF.thetaTr_eqF (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) τ' (boxFun ((om (g, 1)) φ₁) φ₂)))
  have h2 := GlobalTheory.TransportF.thV_injOn hR hψ (GlobalTheory.TransportF.comp_mem_schA τ' t2.1) (GlobalTheory.TransportF.comp_mem_schA τ' hΦ')
    ((GlobalTheory.TransportF.numCoordF (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) τ').surjective.injective_comp_right key')
  funext x
  have hx : (x ∘ τ'.symm) ∘ τ' = x := by
    funext i
    simp
  have hhx := congrFun h2 (x ∘ τ'.symm)
  rw [hx] at hhx
  exact hhx

end GlobalTheory.DblTargetRestrict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledTargetWeilTransportRestrictFirstFactorStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.doubled_target_weil_transport_restrict_first_factor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
      ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E) (hA : JA = JTᵀ),
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
        GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
          Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ omp : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
          Module.End ℂ ((κ ⊕ κ → AF F) → ℂ),
        GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) ωd omp →
      ∀ (g : UG (cA σ) (incM F JA)) (gd : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)),
        gd.1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1.1 0 0 1) →
        ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omp (gd, 1) (boxFun φ₁ φ₂) = boxFun (om (g, 1) φ₁) φ₂ := by
  first | exact @GlobalTheory.DblTargetRestrict.restrict_boxFun | exact GlobalTheory.DblTargetRestrict.restrict_boxFun | (intros; apply GlobalTheory.DblTargetRestrict.restrict_boxFun <;> assumption)
end
end

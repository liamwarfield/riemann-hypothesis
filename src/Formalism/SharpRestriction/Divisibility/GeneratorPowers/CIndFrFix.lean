module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.PderivSecondEvFirstPointEqZero
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
  Formalism.L2.Pj

namespace CIndFrFix

open ReciprocityTheory.ChartRestriction.G.TB.LogPf (logOf)

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

def lg (G : FGLaw S d) {n : ℕ} (j : Fin n) : Pt S n d := fun i => ev (n := n) ![pt S d j] (logOf G i)

def bilL (G : FGLaw S d) (cc : Fin d → Fin d → S) : PS S 2 d :=
  ∑ i, ∑ l, cc i l • (lg G (0 : Fin 2) i * lg G (1 : Fin 2) l)

def expP {n : ℕ} (f : PS S n d) : PS S n d := PowerSeries.subst f (PowerSeries.exp S)

def diagL {O : Type} [CommRing O] [StarRing O] (B : FB S d O) (w0 : O) (cc : Fin d → Fin d → S) : PS S 1 d :=
  ev (n := 1) ![pt S d 0, comp1 (B.A.act w0) (pt S d 0)] (bilL B.G cc)

end CIndFrFix

open CIndFrFix

def FrTruncFixSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y),
    ∃ (e' : ∀ m, FrTy y C.d C.x m) (hfr : IsFrame y C.d C.x C.B.G.F C.B.A.act C.B.ph1 C.B.ph2 C.B.sy C.B.ad e')
      (hrig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act e' C.wP 0)
          (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1))
      (cc : ℕ → Fin C.d → Fin C.d → S),
      FrTruncC y { C with e := e', frame := hfr, rig0 := hrig } ∧ cc 0 = 0 ∧ (∀ m i j, cc m i j = cc m j i) ∧
      (∀ m (a : 𝓞 E), Matrix.transpose (ReciprocityTheory.ChartRestriction.G.TB.dLin (C.B.A.act a)) * Matrix.of (cc m) =
        Matrix.of (cc m) * ReciprocityTheory.ChartRestriction.G.TB.dLin (C.B.A.act (H.bar a))) ∧
      ∀ m, ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ,
        (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (expP (-bilL C.B.G (cc m))) ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ u) (C.e m))

def GermFixSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
      (e' : ∀ m, FrTy y C.d C.x m) (hfr : IsFrame y C.d C.x C.B.G.F C.B.A.act C.B.ph1 C.B.ph2 C.B.sy C.B.ad e')
      (hrig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act e' C.wP 0)
          (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1))
      (cc : ℕ → Fin C.d → Fin C.d → S),
      FrTruncC y { C with e := e', frame := hfr, rig0 := hrig } →
      (∀ m, ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ,
        (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (expP (-bilL C.B.G (cc m))) ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ u) (C.e m))) →
      ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : MvPowerSeries (Fin 1 × Fin C.d) S),
        IsGerm y C.d C.x C.B.A.act C.e C.wP k F f →
        ∃ f' : MvPowerSeries (Fin 1 × Fin C.d) S, IsGerm y C.d C.x C.B.A.act e' C.wP k F f' ∧
          ∀ D, psJet D f' = psJet D (f * expP ((k : S) • diagL C.B H.w0 (cc D)))

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartTransportSt
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

def ChartTransportSt : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (d : ℕ)
    (B : Germ.FB T.V d (𝓞 E)) (tgT : Fin d → (Sp (DualNumber T.V) ⟶ I.G.G.left)) (uvecT : Lt1 Dw → Fin d → T.V)
    (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G) (eT : ∀ m, FrTyG I.G (𝟙 (Sp T.V)) d xT m) (wPT : PrimTyG I.G),
    ((∀ j, IsTanAtG I.G (𝟙 (Sp T.V)) (tgT j)) ∧
      ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin d → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) tgT a w) →
    IsChartG I.G (𝟙 (Sp T.V)) d B.G.F B.A.act tgT (fun j : Fin d => Pi.single j (1 : T.V)) xT →
    (∀ ℓ : Lt1 Dw, IsCombAtG I.G (𝟙 (Sp T.V))
      (fun j : Fin d => (homAt (𝟙 (Sp T.V))
        (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left)
      (uvecT ℓ) (I.ub ℓ.1 ℓ.2).left) →
    IsFrameG I.G (𝟙 (Sp T.V)) d xT B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad eT → IsPrimG I.G wPT →
    FrTrunc I.G (𝟙 (Sp T.V)) d xT eT → Rig0G I.G (𝟙 (Sp T.V)) d xT B.A.act eT wPT →
    letI := io.toAlgebra
    ∃ (B' : Germ.FB T.Fr d (𝓞 E)) (uvec : Lt1 Dw → Fin d → T.Fr) (x : ∀ m, jO y.1 d m 1 ⟶ Xo.univ.t.G)
      (e : ∀ m, FrTy y.1 d x m) (wP : PrimTy H Xo) (h : Germ.PS T.Fr 2 d)
      (hch : IsChart y.1 d B'.G.F B'.A.act uvec x)
      (hfr : IsFrame y.1 d x B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e) (hpr : IsPrim wP)
      (hg : B'.IsCanonGauge T.Fr h)
      (hr : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y.1 d x B'.A.act e wP 0)
          (homAt y.1.x (jetAug : Jet T.Fr (Fin 1 × Fin d) 0 →ₐ[T.Fr] T.Fr)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.1.x T.Fr) 1)),
      IsGenFibreChart (⟨d, B', uvec, x, e, wP, h, hch, hfr, hpr, hg, hr⟩ : ChartAt Xo c y.1) I
        B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad uvecT xT eT wPT

def FBMapSt : Prop :=
  ∀ (R R' : Type) [CommRing R] [CommRing R'] (ψ : R →+* R') (d : ℕ) (O : Type) [CommRing O] [StarRing O]
    (B : Germ.FB R d O), ∃ B' : Germ.FB R' d O,
      (∀ j, B'.G.F j = MvPowerSeries.map ψ (B.G.F j)) ∧ (∀ a j, B'.A.act a j = MvPowerSeries.map ψ (B.A.act a j)) ∧
      B'.ph1 = MvPowerSeries.map ψ B.ph1 ∧ B'.ph2 = MvPowerSeries.map ψ B.ph2 ∧ B'.sy = MvPowerSeries.map ψ B.sy ∧
      ∀ a, B'.ad a = MvPowerSeries.map ψ (B.ad a)

def ChartJetTrSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (d : ℕ)
    (FT : Fin d → Germ.PS T.V 2 d) (actT : 𝓞 E → Fin d → Germ.PS T.V 1 d)
    (tgT : Fin d → (Sp (DualNumber T.V) ⟶ I.G.G.left)) (uvecT : Lt1 Dw → Fin d → T.V)
    (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G),
    ((∀ j, IsTanAtG I.G (𝟙 (Sp T.V)) (tgT j)) ∧
      ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin d → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) tgT a w) →
    IsChartG I.G (𝟙 (Sp T.V)) d FT actT tgT (fun j : Fin d => Pi.single j (1 : T.V)) xT →
    (∀ ℓ : Lt1 Dw, IsCombAtG I.G (𝟙 (Sp T.V))
      (fun j : Fin d => (homAt (𝟙 (Sp T.V))
        (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left)
      (uvecT ℓ) (I.ub ℓ.1 ℓ.2).left) →
    letI := io.toAlgebra
    ∃ (x : ∀ m, jO y.1 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, jOG (𝟙 (Sp T.Fr)) d m 1 ⟶ I.t'.G),
      IsChart y.1 d (fun j => MvPowerSeries.map (algebraMap T.V T.Fr) (FT j))
        (fun a j => MvPowerSeries.map (algebraMap T.V T.Fr) (actT a j))
        (fun ℓ i => algebraMap T.V T.Fr (uvecT ℓ i)) x ∧
      (∀ m, (x' m).left ≫ I.m2.φ = spMap (jetCoef (algebraMap T.V T.Fr) (Fin 1 × Fin d) m) ≫ (xT m).left) ∧
      ∀ m, (x' m).left ≫ I.m1.φ = (x m).left

def ChartFrameTrSt : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (d : ℕ)
    (B : Germ.FB T.V d (𝓞 E)) (B' : Germ.FB T.Fr d (𝓞 E)) (tgT : Fin d → (Sp (DualNumber T.V) ⟶ I.G.G.left))
    (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G) (eT : ∀ m, FrTyG I.G (𝟙 (Sp T.V)) d xT m) (wPT : PrimTyG I.G),
    (∀ j, B'.G.F j = MvPowerSeries.map (algebraMap T.V T.Fr) (B.G.F j)) →
    (∀ a j, B'.A.act a j = MvPowerSeries.map (algebraMap T.V T.Fr) (B.A.act a j)) →
    B'.ph1 = MvPowerSeries.map (algebraMap T.V T.Fr) B.ph1 → B'.ph2 = MvPowerSeries.map (algebraMap T.V T.Fr) B.ph2 →
    B'.sy = MvPowerSeries.map (algebraMap T.V T.Fr) B.sy →
    (∀ a, B'.ad a = MvPowerSeries.map (algebraMap T.V T.Fr) (B.ad a)) →
    IsChartG I.G (𝟙 (Sp T.V)) d B.G.F B.A.act tgT (fun j : Fin d => Pi.single j (1 : T.V)) xT →
    IsFrameG I.G (𝟙 (Sp T.V)) d xT B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad eT → IsPrimG I.G wPT →
    FrTrunc I.G (𝟙 (Sp T.V)) d xT eT → Rig0G I.G (𝟙 (Sp T.V)) d xT B.A.act eT wPT →
    letI := io.toAlgebra
    ∀ (x : ∀ m, jO y.1 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, jOG (𝟙 (Sp T.Fr)) d m 1 ⟶ I.t'.G),
      (∀ m, (x' m).left ≫ I.m2.φ = spMap (jetCoef (algebraMap T.V T.Fr) (Fin 1 × Fin d) m) ≫ (xT m).left) →
      (∀ m, (x' m).left ≫ I.m1.φ = (x m).left) →
      ∃ (e : ∀ m, FrTy y.1 d x m) (wP : PrimTy H Xo),
        IsFrame y.1 d x B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e ∧ IsPrim wP ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
          (LB.pullGen Xo.univ.t.PP.L _ _ (eL y.1 d x B'.A.act e wP 0)
            (homAt y.1.x (jetAug : Jet T.Fr (Fin 1 × Fin d) 0 →ₐ[T.Fr] T.Fr)).left)
          (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.1.x T.Fr) 1) ∧
        (∃ e' : ∀ m, FrTyG I.t' (𝟙 (Sp T.Fr)) d x' m, ∀ m, (e' m).IsGen ∧
          (∃ c₂ : LB.Gen (LB.LinComb I.G.PP.L
              (fun J => cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) d x' m (0 : Fin 2),
                jptG I.t' (𝟙 (Sp T.Fr)) d x' m (1 : Fin 2)] J ≫ I.m2.φ) (cε 2)),
            LB.Gen.Corr I.G.PP.L _ _ _ _ c₂
              (LB.pullGen I.G.PP.L _ _ (eT m) (spMap (jetCoef (algebraMap T.V T.Fr) (Fin 2 × Fin d) m))) ∧
            LB.Gen.Maps (LB.linCombIso I.w2 (cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) d x' m (0 : Fin 2),
                jptG I.t' (𝟙 (Sp T.Fr)) d x' m (1 : Fin 2)]) (cε 2)) (e' m)
              (flatGen I.G.PP.L I.m2.φ _ _ c₂)) ∧
          ∃ c₁ : LB.Gen (LB.LinComb Xo.univ.t.PP.L
              (fun J => cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) d x' m (0 : Fin 2),
                jptG I.t' (𝟙 (Sp T.Fr)) d x' m (1 : Fin 2)] J ≫ I.m1.φ) (cε 2)),
            LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ c₁ (e m) ∧
            LB.Gen.Maps (LB.linCombIso I.w1 (cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) d x' m (0 : Fin 2),
                jptG I.t' (𝟙 (Sp T.Fr)) d x' m (1 : Fin 2)]) (cε 2)) (e' m)
              (flatGen Xo.univ.t.PP.L I.m1.φ _ _ c₁)) ∧
        ∃ wP' : LB.Gen (LB.LinComb I.t'.PP.L (primφ I.t') primε), wP'.IsGen ∧
          (∃ c₂ : LB.Gen (LB.LinComb I.G.PP.L (fun k => primφ I.t' k ≫ I.m2.φ) primε),
            LB.Gen.Corr I.G.PP.L _ _ _ _ c₂ (LB.pullGen I.G.PP.L _ _ wPT I.m2.φ) ∧
            LB.Gen.Maps (LB.linCombIso I.w2 (primφ I.t') primε) wP' (flatGen I.G.PP.L I.m2.φ _ _ c₂)) ∧
          ∃ c₁ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (fun k => primφ I.t' k ≫ I.m1.φ) primε),
            LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ c₁ (LB.pullGen Xo.univ.t.PP.L _ _ wP I.m1.φ) ∧
            LB.Gen.Maps (LB.linCombIso I.w1 (primφ I.t') primε) wP' (flatGen Xo.univ.t.PP.L I.m1.φ _ _ c₁)


omit [StarRing (𝓞 E)] in
def FrTanBasisSt : Prop :=
  ∀ (S : Type) [Field S] [Algebra c.F S] (y : FrPt Xo c S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left),
    IsTanAt y.x w →
    ∃! a : Lt1 Dw → S, IsCombAt y.x (m := Fintype.card (Lt1 Dw))
      (fun i => y.u ((Fintype.equivFin (Lt1 Dw)).symm i).1 ((Fintype.equivFin (Lt1 Dw)).symm i).2)
      (fun i => a ((Fintype.equivFin (Lt1 Dw)).symm i)) w

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdLB
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {Y Z : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']

theorem res_top_mul {U V : Y.Opens} (hV : V ≤ U) (a : Γ(Y, ⊤)ˣ) (x : Γ(Y, U)ˣ) :
    res hV (res le_top a * x) = res le_top a * res hV x := by
  rw [map_mul, DVR.res_res']

theorem pull_top_res (h : Z ⟶ Y) {U : Y.Opens} {W : Z.Opens} (hW : W ≤ h ⁻¹ᵁ U) (a : Γ(Y, ⊤)ˣ) :
    res hW (pullU h U (res le_top a)) = res le_top (Units.map h.appTop.hom.toMonoidHom a) := by
  ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 1
  simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  erw [Scheme.Hom.appLE_map]

theorem scaleGenG_one (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    scaleGenG t φ ε 1 g = g := by
  cases g
  simp only [scaleGenG, map_one, one_mul]

theorem pullGen_scaleGenG (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (v : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (h : Z ⟶ Y) :
    LB.pullGen t.PP.L φ ε (scaleGenG t φ ε v g) h =
      scaleGenG t (fun k => h ≫ φ k) ε (Units.map h.appTop.hom.toMonoidHom v) (LB.pullGen t.PP.L φ ε g h) := by
  unfold LB.pullGen scaleGenG
  congr 1
  funext j
  erw [map_mul, map_mul, pull_top_res]

theorem mulGen_scaleGenG (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (φ' : K' → (Y ⟶ t.G.left)) (ε' : K' → ℤ)
    (v v' : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (g' : LB.Gen (LB.LinComb t.PP.L φ' ε')) :
    LB.mulGen t.PP.L φ ε φ' ε' (scaleGenG t φ ε v g) (scaleGenG t φ' ε' v' g') =
      scaleGenG t _ _ (v * v') (LB.mulGen t.PP.L φ ε φ' ε' g g') := by
  unfold LB.mulGen scaleGenG
  congr 1
  funext j
  erw [res_top_mul, res_top_mul, map_mul, mul_mul_mul_comm]
  rfl

theorem invGen_scaleGenG (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (v : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    LB.invGen t.PP.L φ ε (scaleGenG t φ ε v g) = scaleGenG t φ _ v⁻¹ (LB.invGen t.PP.L φ ε g) := by
  unfold LB.invGen scaleGenG
  congr 1
  funext j
  erw [map_inv, mul_inv_rev, mul_comm]
  rfl

theorem corr_scaleGenG {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ t.G.left)} {ε' : K' → ℤ}
    {g : LB.Gen (LB.LinComb t.PP.L φ ε)} {g' : LB.Gen (LB.LinComb t.PP.L φ' ε')}
    (hc : LB.Gen.Corr t.PP.L φ ε φ' ε' g g') (v : Γ(Y, ⊤)ˣ) :
    LB.Gen.Corr t.PP.L φ ε φ' ε' (scaleGenG t φ ε v g) (scaleGenG t φ' ε' v g') := by
  intro j j' hj hj' hm
  have e := hc j j' hj hj' hm
  unfold scaleGenG
  dsimp only
  erw [res_top_mul, res_top_mul, e]

variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

theorem unitΓ_homAt {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] (f : A →ₐ[S] B)
    (u : Aˣ) :
    Units.map (homAt x0 f).left.appTop.hom.toMonoidHom (unitΓ u) = unitΓ (Units.map f.toMonoidHom u) := by
  ext
  simp only [unitΓ, toΓ, L2.Pj.homAt, Over.homMk_left, spMap, Units.coe_map, MonoidHom.coe_coe,
    RingHom.toMonoidHom_eq_coe]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartSt
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def IntChartStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V →
    ∀ (t : SAB H (Sp V)),
    IsProper ((Over.pullback (spMap (algebraMap V (FractionRing V)))).obj t.G).hom →
    ∀ {κ : Type} [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)),
      (∀ ℓ, IsTanAtG t (𝟙 (Sp V)) (tg ℓ)) →
      (∀ w, IsTanAtG t (𝟙 (Sp V)) w →
        ∃! a : κ → V, IsCombAtG t (𝟙 (Sp V)) (m := Fintype.card κ)
          (fun i => tg ((Fintype.equivFin κ).symm i)) (fun i => a ((Fintype.equivFin κ).symm i)) w) →
      ∀ [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
      ∃ (d : ℕ) (B : Germ.FB V d (𝓞 E)) (uvec : κ → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
        (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (wP : PrimTyG t),
        d = Fintype.card κ ∧ (∀ ℓ (j : Fin d), uvec ℓ j = if (j : ℕ) = (Fintype.equivFin κ ℓ : ℕ) then 1 else 0) ∧
        IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uvec x ∧
        IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e ∧
        IsPrimG t wP ∧ FrTrunc t (𝟙 (Sp V)) d x e ∧ Rig0G t (𝟙 (Sp V)) d x B.A.act e wP ∧
        ∀ (k : ℕ) (F : LB.Sec (LPow t.G t.PP.L k (Over.mk (𝟙 (Sp V))))),
          ∃ f, IsGermG t (𝟙 (Sp V)) d x B.A.act e wP k F f

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpAct
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def ExpActOfSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (y : FrPt Xo c S) (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S),
    IsExpOf C.B.G.F C.uvec φ → ∀ (a : 𝓞 E) (j : Fin C.d),
      MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
        MvPowerSeries.subst (fun q : Fin 1 × Fin (dL Dw) =>
          algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 a) •
            (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) (φ j)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.UnitIdSt
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {S : Type} [CommRing S]

def actPS (c : Coeff l) [Algebra c.F S] (a : 𝓞 E) : Fin 1 × Fin (dL Dw) → MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  fun q => algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 a) • MvPowerSeries.X q

def φa (c : Coeff l) [Algebra c.F S] {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (a : 𝓞 E) :
    Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  fun j => MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j)

def atP {d n : ℕ} (P : Fin n → Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (f : MvPowerSeries (Fin n × Fin d) S) : MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  MvPowerSeries.subst (fun p : Fin n × Fin d => P p.1 p.2) f

end Defs

def UnitIdSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
      (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), IsExpOf C.B.G.F C.uvec φ →
      (∀ (a : 𝓞 E) (j : Fin C.d), MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
        MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j)) →
      ∀ a : 𝓞 E,
        Germ.FB.expS S (-(compL (φa c φ (1 + a * H.bar a)) (C.B.hL S C.h H.w0))) *
            atP ![φa c φ a, φa c φ H.w0] (C.B.ad (H.bar a)) =
          atP ![φ, φa c φ (a * H.bar a), φa c φ ((1 + a * H.bar a) * H.w0)] C.B.ph1 *
            atP ![φ, φa c φ H.w0, φa c φ (a * H.bar a * H.w0)] C.B.ph2 *
            atP ![φa c φ (a * H.bar a), φa c φ H.w0, φa c φ (a * H.bar a * H.w0)] C.B.ph2 *
            atP ![φ, φa c φ (a * H.w0)] (C.B.ad a) *
            Germ.FB.expS S (-(compL (φa c φ a) (C.B.hL S C.h H.w0))) ^ 2 *
            Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0))) *
            Germ.FB.expS S (-(compL (φa c φ (a * H.bar a)) (C.B.hL S C.h H.w0)))

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeBeta
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField TopologicalSpace Opposite MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def BetaUniqSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (a : 𝓞 E) (β β' : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε)),
    β.IsGen → β'.IsGen →
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (eSec Xo.univ.t.G))
      (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) →
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β' (eSec Xo.univ.t.G))
      (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) →
    β = β'

namespace GaugeBeta

theorem pull_unit_eq_one_k {X Y S0 : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : S0 ⟶ Y) (ψ : S0 ⟶ X) (k : ℤ)
    (rig : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => ψ) fun _ => k))
    (t t' : LB.Gen (LB.LinComb L φ ε)) (u : Γ(Y, ⊤)ˣ)
    (hu : ∀ j, t.s j = res (le_top : (LB.LinComb L φ ε).U j ≤ ⊤) u * t'.s j)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t h) rig)
    (hc' : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t' h) rig) :
    (h.app ⊤).hom (u : Γ(Y, ⊤)) = 1 := by

  let rig1 : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => ψ) fun _ => 1) := ⟨rig.s⟩
  exact pull_unit_eq_one L hL φ ε h ψ rig1 t t' u hu hc hc'

end GaugeBeta

theorem betaUniq_of_global (hglob : GlobalFnsSt) : BetaUniqSt := by
  intro E _ _ _ H Dw l Xo a β β' hβ hβ' hc hc'
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  obtain ⟨u, hu⟩ := gen_ratio _ (wchart_cover Xo.univ.t.PP.L hL _) β β' hβ hβ'
  have h1 := GaugeBeta.pull_unit_eq_one_k Xo.univ.t.PP.L hL _ _ (eSec Xo.univ.t.G)
    (eSec Xo.univ.t.G) (-3) (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) β β' u hu hc hc'
  have hu1 : u = 1 := by
    obtain ⟨v, hv⟩ := (hglob _ Xo.univ.t.G (isAbelianScheme_univ Xo)).2 (u : Γ(Xo.univ.t.G.left, ⊤))
    have hw : eSec Xo.univ.t.G ≫ Xo.univ.t.G.hom = 𝟙 _ := by
      unfold eSec
      exact Over.w _
    have e1 : (Scheme.Hom.app (eSec Xo.univ.t.G) ⊤).hom
        ((Scheme.Hom.appTop Xo.univ.t.G.hom).hom v) = v := by
      have := congrArg (fun f => (Scheme.Hom.appTop f).hom v) hw
      simp at this
      exact this
    rw [hv] at e1
    have hv1 : v = 1 := e1.symm.trans h1
    apply Units.ext
    rw [← hv, hv1, map_one]
    rfl
  cases β
  cases β'
  congr 1
  funext j
  have hj := hu j
  rw [hu1, map_one, one_mul] at hj
  exact hj

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqA
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GaugeR

def IsScaled {Y : Scheme.{0}} {M : LB Y} (u : Γ(Y, ⊤)ˣ) (t t' : LB.Gen M) : Prop :=
  ∀ j, t'.s j = res le_top u * t.s j

def pullUnit {Y Z : Scheme.{0}} (h : Z ⟶ Y) (u : Γ(Y, ⊤)ˣ) : Γ(Z, ⊤)ˣ :=
  pullU h ⊤ u

variable {X Y Z : Scheme.{0}} (L : LB X)

theorem ratio_of_gen (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t t' : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (ht' : t'.IsGen) : ∃ u, IsScaled u t t' := by
  exact gen_ratio (LB.LinComb L φ ε) (wchart_cover L hL φ) t' t ht' ht

theorem scaled_one {M : LB Y} (t : LB.Gen M) : IsScaled 1 t t := by
  intro j
  rw [map_one, one_mul]

theorem scaled_mul {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) {u v : Γ(Y, ⊤)ˣ} {t t' : LB.Gen (LB.LinComb L φ ε)}
    {s s' : LB.Gen (LB.LinComb L φ' ε')} (h1 : IsScaled u t t') (h2 : IsScaled v s s') :
    IsScaled (u * v) (LB.mulGen L φ ε φ' ε' t s) (LB.mulGen L φ ε φ' ε' t' s') := by
  have h1' : ∀ j, t'.s j = res le_top u * t.s j := h1
  have h2' : ∀ j, s'.s j = res le_top v * s.s j := h2
  intro j
  simp only [LB.mulGen]
  erw [h1' (j ∘ Sum.inl), h2' (j ∘ Sum.inr)]
  simp only [map_mul]
  erw [res_res, res_res]
  rw [mul_mul_mul_comm]
  rfl

theorem pullUnit_res (h : Z ⟶ Y) {V : Y.Opens} {W : Z.Opens} (hWV : W ≤ h ⁻¹ᵁ V) (u : Γ(Y, ⊤)ˣ) :
    res hWV (pullU h V (res (le_top : V ≤ ⊤) u)) = res le_top (pullUnit h u) := by
  rw [ReciprocityTheory.ChartRestriction.G.DVR.pullU_res, res_res]
  rfl

theorem scaled_pull {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Z ⟶ Y) {u : Γ(Y, ⊤)ˣ}
    {t t' : LB.Gen (LB.LinComb L φ ε)} (hs : IsScaled u t t') :
    IsScaled (pullUnit h u) (LB.pullGen L φ ε t h) (LB.pullGen L φ ε t' h) := by
  have hs' : ∀ j, t'.s j = res le_top u * t.s j := hs
  intro j
  simp only [LB.pullGen]
  erw [hs' j, map_mul, map_mul, pullUnit_res]

theorem corr_scaled (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (t₁ t₁' : LB.Gen (LB.LinComb L φ ε))
    (t₂ t₂' : LB.Gen (LB.LinComb L φ' ε')) (U₁ U₂ : Γ(Y, ⊤)ˣ) (h₁ : IsScaled U₁ t₁ t₁')
    (h₂ : IsScaled U₂ t₂ t₂') (c : LB.Gen.Corr L φ ε φ' ε' t₁ t₂) (c' : LB.Gen.Corr L φ ε φ' ε' t₁' t₂') :
    U₁ = U₂ := by
  classical
  have h₁' : ∀ j, t₁'.s j = res le_top U₁ * t₁.s j := h₁
  have h₂' : ∀ j, t₂'.s j = res le_top U₂ * t₂.s j := h₂
  have key : ∀ {U V : Y.Opens} (hle : V ≤ U) (a b : Γ(Y, U)ˣ), res hle (a * b) = res hle a * res hle b :=
    fun hle a b => map_mul _ a b
  have hch : ∀ (ψ : Y ⟶ X) (y : Y), ∃ i, ψ y ∈ L.U i := by
    intro ψ y
    have hy := wchart_cover L hL (fun _ : Fin 1 => ψ) (show y ∈ (⊤ : Y.Opens) from trivial)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    exact ⟨j 0, Set.mem_iInter.1 hj 0⟩
  apply Units.ext
  have hcov : ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧
      (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (U₁ : Γ(Y, ⊤)) =
        (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (U₂ : Γ(Y, ⊤)) := by
    intro y
    choose ch hc using fun ψ => hch ψ y
    let j : K → L.ι := fun k => ch (φ k)
    let j' : K' → L.ι := fun k => ch (φ' k)
    have hj : LB.Coh L φ j := fun k1 k2 e => show ch (φ k1) = ch (φ k2) by rw [e]
    have hj' : LB.Coh L φ' j' := fun k1 k2 e => show ch (φ' k1) = ch (φ' k2) by rw [e]
    have hjj : ∀ k k', φ k = φ' k' → j k = j' k' := fun k k' e => show ch (φ k) = ch (φ' k') by rw [e]
    have hyW : y ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' :=
      ⟨Set.mem_iInter.2 fun k => hc (φ k), Set.mem_iInter.2 fun k => hc (φ' k)⟩
    have E := c j j' hj hj' hjj
    have E' := c' j j' hj hj' hjj
    rw [h₁' j, h₂' j'] at E'
    erw [key, key, res_res, res_res, E] at E'
    have E2 := mul_right_cancel E'
    exact ⟨_, hyW, congrArg Units.val E2⟩
  choose W hyW hW using hcov
  exact TopCat.Sheaf.eq_of_locally_eq' Y.sheaf W ⊤ (fun y => homOfLE le_top)
    (fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyW y⟩) _ _ hW

theorem corr_scaled_left (hL : L.IsLB) (ψ : Y ⟶ X) (a : ℤ) {K' : Type} [Fintype K'] (φ' : K' → (Y ⟶ X))
    (ε' : K' → ℤ) (τ τ' : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => ψ) fun _ => a))
    (t₂ t₂' : LB.Gen (LB.LinComb L φ' ε')) (U : Γ(Y, ⊤)ˣ) (h₂ : IsScaled U t₂ t₂')
    (c : LB.Gen.Corr L _ _ _ _ τ t₂) (c' : LB.Gen.Corr L _ _ _ _ τ' t₂') : IsScaled U τ τ' := by
  let τ'' : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => ψ) fun _ => a) :=
    ⟨fun j => res le_top U * τ.s j⟩
  have h₂' : ∀ j, t₂'.s j = res le_top U * t₂.s j := h₂
  have hc'' : LB.Gen.Corr L _ _ _ _ τ'' t₂' := by
    intro j j' hj hj' hm
    have := c j j' hj hj' hm
    show res _ (res le_top U * τ.s j) = res _ (t₂'.s j')
    rw [h₂' j']
    erw [map_mul, map_mul, this, res_res, res_res]
    rfl
  have he := GermFun.gen_eq_of_corr L hL ψ a φ' ε' τ'' τ' t₂' hc'' c'
  intro j
  rw [← he]

end GaugeR

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

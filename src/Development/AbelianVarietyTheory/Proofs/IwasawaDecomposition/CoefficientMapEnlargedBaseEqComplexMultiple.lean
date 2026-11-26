module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralOfLine
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientMapEnlargedBaseEqComplexMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientMapEnlargedBaseEqComplexMultiple
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.OmExt

def mapVVι {K K' : Type} [Field K] [Field K'] (ι : K →+* K') {T : Type} [Fintype T] {n : ℕ} (lam : T → DomWeight n)
    (v : VV K lam) : VV K' lam :=
  ⟨MvPolynomial.map ι v.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV ι lam _ v.2⟩

theorem exists_smul_eq_enl {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) {K' : Type} [Field K'] (ι : D.what₂.LL →+* K')
    (emb' : K' →+* ℂ) (hι : ∀ x, emb' (ι x) = D.what₂.embLL x) (tau : D.what₂.Tau → D.host.E →+* D.what₂.LL)
    (tau' : D.what₂.Tau → D.host.E →+* K') (htau : ∀ τ, emb'.comp (tau' τ) = D.what₂.embLL.comp (tau τ))
    {lam : D.what₂.Tau → DomWeight V.rank}
    (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) (h0 : Bridge.CoefMapTie V c.coef c0 (rhoVr tau lam))
    (c' : CoefA V) (hcc : c' = c) (c0' : VV K' lam →ₛₗ[emb'] c'.W)
    (h1 : ∀ γ γE, Bridge.IsRatMat V γ γE → ∀ v, c0' (rhoVr tau' lam γE v) = c'.coef.ρ γ (c0' v)) :
    ∃ μ : ℂ, ∀ (v : VV D.what₂.LL lam) (v' : VV K' lam),
      MvPolynomial.map emb' v'.1 = MvPolynomial.map D.what₂.embLL v.1 → HEq (c0' v') (μ • c0 v) := by
  subst c'
  have hcomp : emb'.comp ι = D.what₂.embLL := RingHom.ext hι
  have hinj : ∀ a b : VV K' lam, MvPolynomial.map emb' a.1 = MvPolynomial.map emb' b.1 → a = b := fun a b h =>
    Subtype.ext (MvPolynomial.map_injective emb' emb'.injective h)
  have hmap : ∀ v : VV D.what₂.LL lam, MvPolynomial.map emb' (mapVVι ι lam v).1 = MvPolynomial.map D.what₂.embLL v.1 := fun v => by
    show MvPolynomial.map emb' (MvPolynomial.map ι v.1) = _
    rw [MvPolynomial.map_map, hcomp]
  have hsm : ∀ (a : D.what₂.LL) (v : VV D.what₂.LL lam), mapVVι ι lam (a • v) = ι a • mapVVι ι lam v := fun a v =>
    Subtype.ext (by
      show MvPolynomial.map ι (a • v.1) = ι a • MvPolynomial.map ι v.1
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul])
  let c1 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W :=
    { toFun := fun v => c0' (mapVVι ι lam v)
      map_add' := fun a b => by
        rw [← map_add (f := _)]
        congr 1
        exact Subtype.ext (map_add _ _ _)
      map_smul' := fun a v => by
        show c0' (mapVVι ι lam (a • v)) = D.what₂.embLL a • c0' (mapVVι ι lam v)
        rw [hsm, map_smulₛₗ, hι] }
  have hrho : ∀ γE v, mapVVι ι lam (rhoVr tau lam γE v) = rhoVr tau' lam γE (mapVVι ι lam v) := fun γE v => by
    refine hinj _ _ ?_
    rw [hmap]
    have e1 := congrArg Subtype.val (GlobalTheory.ConjTwist.mapVV_rhoVr D.what₂.embLL tau lam γE v)
    have e2 := congrArg Subtype.val (GlobalTheory.ConjTwist.mapVV_rhoVr emb' tau' lam γE (mapVVι ι lam v))
    rw [GlobalTheory.CoefModel.mapVV_coe] at e1 e2
    rw [e1, e2]
    have e3 : (fun τ => emb'.comp (tau' τ)) = fun τ => D.what₂.embLL.comp (tau τ) := funext htau
    have e4 : GlobalTheory.CoefModel.mapVV emb' lam (mapVVι ι lam v) = GlobalTheory.CoefModel.mapVV D.what₂.embLL lam v :=
      Subtype.ext (hmap v)
    rw [e3, e4]
  obtain ⟨μ, hμ⟩ := RowCoord.exists_smul_eq c hc h0 c1 fun γ γE hγ v => by
    show c0' (mapVVι ι lam (rhoVr tau lam γE v)) = c.coef.ρ γ (c0' (mapVVι ι lam v))
    rw [hrho]
    exact h1 γ γE hγ _
  refine ⟨μ, fun v v' hv => heq_of_eq ?_⟩
  have : v' = mapVVι ι lam v := hinj _ _ (hv.trans (hmap v).symm)
  subst this
  exact hμ v

end GlobalTheory.Mem.R3.Rw.OmExt
end

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.OmExt

theorem coefA_eq {D : D7} {V : HSp D} (c c' : CoefA V) (hW : HEq c'.W c.W) (hρ : HEq c'.ρ c.ρ) (hn : HEq c'.nW c.nW)
    (hi : HEq c'.iW c.iW) : c' = c := by
  cases c
  cases c'
  dsimp only at hW hρ hn hi
  cases hW
  cases hn
  cases hi
  cases hρ
  rfl


set_option maxHeartbeats 4000000 in
theorem coef_schur : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
  ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks)
    (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
    Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
    BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSideW z Wt' R' →
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ c0L, GlobalTheory.Mem.R3.Rw.OmExt.CoefFam z.R.toRealDat c0L →
    ∀ c0L'', GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L'' →
    ∃ μ : ℂ, ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
      HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) → HEq (c0L'' i' v') (μ • c0L i v) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hff hpx hstd Ks _ _ _ Xg tr R' cG' hP hL hB hRS i i' hii c0L hc c0L'' hc''
  obtain ⟨gR, c0R, ht⟩ := hc
  obtain ⟨gR', c0R', ht'⟩ := hc''
  have hs := hRS.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hii
  have hW := hs.1
  have hρ := hs.2.1
  have hnW := hs.2.2.1
  have hiW := hs.2.2.2.1
  have hcI := z.pins.char.base.models.cV i
  have hmapL := ht.mapL i
  have hmapL' := ht'.mapL i'
  have htau := ht.tauL_ok
  have htau' := ht'.tauL_ok
  obtain ⟨hpre, -, -, hR⟩ := hE
  cases B with | mk P => cases B' with | mk P' =>
  dsimp only at hpre
  subst hpre
  obtain rfl : i = i' := Fin.ext hii
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL := (enlEmb hR)
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := (enlEmb_spec hR)
  let c'' : CoefA (Vc (w.st Z).toD7 i) :=
    { W := (R'.cV i).W, nW := (R'.cV i).nW, iW := (R'.cV i).iW, fW := (R'.cV i).fW, ρ := (R'.cV i).ρ }
  have hcc : c'' = z.R.cV i := coefA_eq _ _ hW hρ hnW hiW
  obtain ⟨μ, hμ⟩ := exists_smul_eq_enl (z.R.cV i) hcI ι (w'.st Z').toD7.what₂.embLL hι (labLL (w.st Z).toD7)
    (labLL (w'.st Z').toD7) (fun τ => (htau' τ).trans (htau τ).symm) (c0L i) hmapL c'' hcc (c0L'' i) hmapL'.1
  exact ⟨μ, fun v v' hv => hμ v v' (eq_of_heq hv)⟩

end GlobalTheory.Mem.R3.Rw.OmExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientMapEnlargedBaseEqComplexMultipleStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientMap_enlargedBase_eq_complexMultiple : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
  ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks)
    (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
    Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
    BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSideW z Wt' R' →
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ c0L, GlobalTheory.Mem.R3.Rw.OmExt.CoefFam z.R.toRealDat c0L →
    ∀ c0L'', GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L'' →
    ∃ μ : ℂ, ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
      HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) → HEq (c0L'' i' v') (μ • c0L i v) := by
  exact @GlobalTheory.Mem.R3.Rw.OmExt.coef_schur
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinateTwoNsmulAssociatedPowFour
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinateTwoNsmulAssociatedPowFour
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiDoubleCoord

open GlobalTheory.PeriodBalance GlobalTheory.PsiTauCoordRel MonoidalCategory CartesianMonoidalCategory MonObj GrpObj

section
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem val_cub (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J : (Spec (CommRingCat.of (FractionRing R)) ⟶ D.P.A.left) → D.P.L.ι}
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (a a' b : D.X) :
    ∃ w : Rˣ, val (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t (𝟙 (Spec (CommRingCat.of (FractionRing R))) ≫ D.pt3 a a' b) ξ J =
      Units.map (cst ξ).toMonoidHom w := by
  have hp : 𝟙 (Spec (CommRingCat.of (FractionRing R))) ≫ D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left := by
    simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]
  rw [hp]
  refine val_int (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) ξ hJc D.cub.t _ fun k => ?_
  show (_ ≫ (psum _ _ _).left) ≫ _ = _
  rw [Category.assoc, Over.w, Over.w]; rfl

theorem val_sym (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (y : D.X) :
    ∃ w : Rˣ, val (LB.pullGen D.P.L _ _ D.sym (D.xK y)) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J = Units.map (cst ξ).toMonoidHom w := by
  rw [val_pull hJ]
  have hx : 𝟙 (Spec (CommRingCat.of (FractionRing R))) ≫ D.xK y = jK R ≫ (D.c y).left := by rw [Category.id_comp]; exact DVR.QForm.ptK_eq D y
  rw [hx]
  refine val_int ξ hJc D.sym _ fun k => ?_
  obtain ⟨q, hq⟩ : ∃ q : D.P.A ⟶ D.P.A, (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k = q.left := by
    fin_cases k
    · exact ⟨_, rfl⟩
    · exact ⟨𝟙 _, rfl⟩
  rw [hq, Category.assoc, Over.w q, Over.w]; rfl

theorem val_rig (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) :
    ∃ w : Rˣ, val D.rigK (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J = Units.map (cst ξ).toMonoidHom w := by
  unfold DegPre.rigK
  rw [val_pull hJ]
  have : 𝟙 (Spec (CommRingCat.of (FractionRing R))) ≫ (toUnit (TK R)).left = jK R ≫ 𝟙 _ := by rw [toUnit_left]; simp
  rw [this]
  exact val_int ξ hJc D.rig (𝟙 _) fun _ => by rw [Category.id_comp]; exact Over.w η[D.P.A]

end

theorem alg {G : Type} [CommGroup G] (A0 Ay Am A2 Vr C0 C1 S : G)
    (h1 : Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹ * C0 = Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹ * (Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹))
    (h2 : Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹ * C1 = A2 * Ay⁻¹ * Ay⁻¹ * Vr⁻¹ * (A0 * Am⁻¹ * Ay⁻¹ * Vr⁻¹))
    (h3 : Am * S = Ay) :
    A2 = C0 * C0 * C1 * Vr * Vr * Vr * S⁻¹ * Ay ^ 4 := by
  have hC0 := mul_left_cancel h1
  have hAm : Am = Ay * S⁻¹ := eq_mul_inv_of_mul_eq h3
  subst hC0 hAm
  have e : A2 = Ay * A0⁻¹ * Ay⁻¹ * Vr⁻¹ * C1 * (Ay⁻¹ * Ay⁻¹ * Vr⁻¹ * (A0 * (Ay * S⁻¹)⁻¹ * Ay⁻¹ * Vr⁻¹))⁻¹ := by
    rw [h2]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

theorem val_cubP {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (a a' b : D.X) :
    ∃ w : Rˣ, val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b))
      (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J = Units.map (cst ξ).toMonoidHom w := by
  obtain ⟨w, hw⟩ := val_cub D ξ hJc a a' b
  exact ⟨w, (val_pull hJ _ _ _).trans hw⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegData R I)
    (y : D.toPre.X) (r s : R), PsiCoord D.toPre y r → PsiCoord D.toPre (2 • y) s → Associated s (r ^ 4) := by
  intro R _ _ _ I D y r s hr hs
  haveI : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.toPre.P.isLB D.toPre.P.A.hom
  have b1 := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (D.tau_bimult 0 0 y) (𝟙 _)).trans (val_mul hJ _ _ _))
  have b2 := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (D.tau_bimult y (-y) y) (𝟙 _)).trans (val_mul hJ _ _ _))
  have ev := (val_mul hJ _ _ _).symm.trans (val_corr hJ (D.psi_even y) (𝟙 _))
  have vt : ∀ a b : D.toPre.X, val (D.toPre.tau a b) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J = val (D.toPre.psi (a + b)) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J *
      (val (D.toPre.psi a) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J)⁻¹ * (val (D.toPre.psi b) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J)⁻¹ * (val D.toPre.rigK (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J)⁻¹ :=
    fun a b => GlobalTheory.PeriodBalance.val_tau D.toPre ξ hJ a b
  obtain ⟨w0, hw0⟩ := val_cubP D.toPre ξ hJ hJc 0 0 y
  obtain ⟨w1, hw1⟩ := val_cubP D.toPre ξ hJ hJc y (-y) y
  obtain ⟨w5, hw5⟩ := val_rig D.toPre ξ hJ hJc
  obtain ⟨w6, hw6⟩ := val_sym D.toPre ξ hJ hJc y
  rw [hw6] at ev
  rw [hw0, vt, vt, hw5] at b1
  rw [hw1, vt, vt, vt, hw5] at b2
  rw [add_zero, zero_add] at b1
  rw [add_neg_cancel, zero_add, neg_add_cancel, ← two_nsmul] at b2
  have key := alg _ _ _ _ _ _ _ _ b1 b2 ev
  obtain ⟨u1, g1⟩ : ∃ u : Rˣ, (val (D.toPre.psi y) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J).val = cst ξ (u * r) := val_psi D.toPre ξ hJ hJc y r hr
  obtain ⟨u2, g2⟩ : ∃ u : Rˣ, (val (D.toPre.psi (2 • y)) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J).val = cst ξ (u * s) := val_psi D.toPre ξ hJ hJc (2 • y) s hs
  obtain ⟨W, key2⟩ : ∃ W : Rˣ, val (D.toPre.psi (2 • y)) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J =
      Units.map (cst ξ).toMonoidHom W * (val (D.toPre.psi y) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ J) ^ 4 :=
    ⟨w0 * w0 * w1 * w5 * w5 * w5 * w6⁻¹, by rw [key]; simp only [map_mul, map_inv]⟩
  have e : cst ξ (u2 * s) = cst ξ (W * (u1 * r) ^ 4) := by
    rw [← g2, key2, map_mul, map_pow, ← g1, Units.val_mul, Units.val_pow_eq_pow_val]; rfl
  have e2 := cst_injective ξ e
  refine ⟨u2 * (W * u1 ^ 4)⁻¹, ?_⟩
  have h3 : ((W * u1 ^ 4 : Rˣ) : R) * r ^ 4 = u2 * s := by push_cast; rw [e2]; ring
  rw [Units.val_mul, ← _root_.mul_assoc, _root_.mul_comm s, ← h3, _root_.mul_comm, ← _root_.mul_assoc, Units.inv_mul,
    _root_.one_mul]

end GlobalTheory.PsiDoubleCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinateTwoNsmulAssociatedPowFourStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiCoordinate_two_nsmul_associated_pow_four : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegData R I) (y : D.toPre.X) (r s : R), PsiCoord D.toPre y r → PsiCoord D.toPre (2 • y) s → Associated s (r ^ 4) := by
  first | exact @GlobalTheory.PsiDoubleCoord.main | exact GlobalTheory.PsiDoubleCoord.main | (intros; apply GlobalTheory.PsiDoubleCoord.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCastMap
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct nonZeroDivisors
open Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.RealGeo GlobalTheory.OneMapAll GlobalTheory.FieldBC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmExt

section Alg

theorem coef_agree {L K L' K' I W W' : Type} [Field L] [Field K] [Field L'] [Field K'] [Fintype I] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] {n : ℕ} (lam : I → DomWeight n) {σL : L →+* ℂ} {σK : K →+* ℂ} {σL' : L' →+* ℂ} {σK' : K' →+* ℂ}
    (jL : L →+* K) (jL' : L' →+* K') (inc : K →+* K') (h : σK.comp jL = σL) (h' : σK'.comp jL' = σL') (hi : σK'.comp inc = σK)
    (s : Function.Surjective jL) (s' : Function.Surjective jL')
    {cL : VV L lam →ₛₗ[σL] W} {cK : VV K lam →ₛₗ[σK] W} {cL' : VV L' lam →ₛₗ[σL'] W'} {cK' : VV K' lam →ₛₗ[σK'] W'}
    (hc : ∀ v : VV L lam, ∃ v' : VV K lam, (v' : Pol K I n) = MvPolynomial.map jL (v : Pol L I n) ∧ cK v' = cL v)
    (hc' : ∀ v : VV L' lam, ∃ v' : VV K' lam, (v' : Pol K' I n) = MvPolynomial.map jL' (v : Pol L' I n) ∧ cK' v' = cL' v)
    (ha : ∀ (v : VV L lam) (v' : VV L' lam), HEq (MvPolynomial.map σL' v'.1) (MvPolynomial.map σL v.1) → HEq (cL' v') (cL v))
    (v : VV K lam) (v' : VV K' lam) (e : (v' : Pol K' I n) = MvPolynomial.map inc (v : Pol K I n)) : HEq (cK' v') (cK v) := by
  have key : ∀ {L K : Type} [Field L] [Field K] (jL : L →+* K), Function.Surjective jL → ∀ v : VV K lam,
      ∃ u : VV L lam, (v : Pol K I n) = MvPolynomial.map jL (u : Pol L I n) := by
    intro L K _ _ jL s v
    let q := (RingEquiv.ofBijective jL ⟨jL.injective, s⟩).symm
    refine ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV q.toRingHom lam _ v.2⟩, ?_⟩
    have : jL.comp q.toRingHom = RingHom.id K := RingHom.ext fun x => (RingEquiv.ofBijective jL ⟨jL.injective, s⟩).apply_symm_apply x
    rw [MvPolynomial.map_map, this, MvPolynomial.map_id]
  obtain ⟨u, hu⟩ := key jL s v
  obtain ⟨u', hu'⟩ := key jL' s' v'
  obtain ⟨a, a1, a2⟩ := hc u
  obtain ⟨b, b1, b2⟩ := hc' u'
  obtain rfl : a = v := Subtype.ext (a1.trans hu.symm)
  obtain rfl : b = v' := Subtype.ext (b1.trans hu'.symm)
  rw [a2, b2]
  refine ha u u' (heq_of_eq ?_)
  rw [← h, ← h', ← MvPolynomial.map_map, ← MvPolynomial.map_map, ← hu, ← hu', e, MvPolynomial.map_map, hi]

theorem exists_cast_map {K V W W' : Type} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* ℂ}
    (n : NormedAddCommGroup W) (p : InnerProductSpace ℂ W) (n' : NormedAddCommGroup W') (p' : InnerProductSpace ℂ W')
    (hW : HEq W' W) (hn : HEq n' n) (hp : HEq p' p) (c' : V →ₛₗ[σ] W') :
    ∃ c : V →ₛₗ[σ] W, HEq c' c ∧ ∀ v, HEq (c' v) (c v) := by
  cases hW; cases hn; cases hp
  exact ⟨c', HEq.rfl, fun _ => HEq.rfl⟩

end Alg

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Change

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  (O : OMDat C R i Unit (fun _ => A.μ0)) (c₃ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff C.Q.l) (hs : O.c'.F ≤ c₃.F)
  (c0₃ : VsV D i c₃.F →ₛₗ[inC c₃] (R.cV i).W)
  (io₃ : VsV D i c₃.F →ₗ[c₃.F] MvPolynomial (LtN (C.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c₃.F) (hw₃ : VsV D i c₃.F)
  (h : O.Cl' () → GA D (Vc D i)) (v₀ : (R.MW i (sg0 D A)).Vec)

abbrev bc : OMDat C R i Unit (fun _ => A.μ0) :=
  merge (tup := fun _ : Unit => A.μ0) (fun _ => O) c₃ (O.hle.trans hs) (fun _ => hs) ((incF O.c' c₃ hs).comp O.jL) O.hV c0₃ O.lev
    io₃ hw₃ (fun _ => 1) (fun _ => h) v₀

structure IsBC (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) (J' : Subgroup (Bridge.Gf (Vc D i))) : Prop where
  c0 : ∀ (v : VsV D i O.c'.F) (v' : VsV D i c₃.F), (v' : Pol c₃.F D.what₂.Tau (Vc D i).rank) =
    MvPolynomial.map (incF O.c' c₃ hs) (v : Pol O.c'.F D.what₂.Tau (Vc D i).rank) → c0₃ v' = O.c0' v
  io : IoOver hs (lamV D i) O.io io₃
  reps : RepsR R i A.μ0 h (O.bad ()) J' (O.Lh ()) (O.gam ()) (O.vol ())
  placeEx : PlaceEx R i A.μ0 h O.c0'
  thAd : ThAdIs R i A.μ0 h O.c0' v₀ (O.thAd ())
  plc : ∀ x, O.Plc () x ↔ ∃ x₀, Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x
  pins : (bc O c₃ hs c0₃ io₃ hw₃ h v₀).Pins κ v₀ ι x₀


set_option maxHeartbeats 1600000 in
theorem exists_isBC (hV : R.models_HV) {κ ι x₀} (hO : O.Pins κ v₀ ι x₀)
    (hc0 : ∀ (v : VsV D i O.c'.F) (v' : VsV D i c₃.F), (v' : Pol c₃.F D.what₂.Tau (Vc D i).rank) =
      MvPolynomial.map (incF O.c' c₃ hs) (v : Pol O.c'.F D.what₂.Tau (Vc D i).rank) → c0₃ v' = O.c0' v) :
    ∃ io₃ hw₃ h J', IsBC O c₃ hs c0₃ io₃ hw₃ h v₀ κ ι x₀ J' := by
  obtain ⟨io₃, hw₃, hio, hover⟩ := GlobalTheory.IoExtend.exists_ioLFRec_over _ _ _ _ O.c' c₃ hs _ _ (tauE D) (lamV D i) (wtA κ) O.io O.hw hO.io
  obtain ⟨h, J', hr, hpl, hth, hplc⟩ := (hO.tuple ()).reps
  obtain ⟨a, ha, hca⟩ := (cXiVal_iff _ _ _ _ _ _ _ _ _).1 hO.cxi
  refine ⟨io₃, hw₃, h, J', hc0, hover, hr, hpl, hth, hplc, ⟨?_, hO.lift.std, hO.lift.v0, ?_, hO.lift.lev⟩,
    fun j => ⟨?_, (hO.tuple ()).B, (hO.tuple ()).xi, (hO.tuple ()).phi, (hO.tuple ()).half⟩,
    ⟨hO.act.1, (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ (O.hle.trans hs) _ _ hO.act.1).1⟩, fun j => hO.bad (), fun j => hO.reps (),
    fun j => ⟨fun k => congrArg (incF _ c₃ hs) ((hO.ep ()).1 k), epIs_map hs (hO.ep ()).2⟩, hio,
    fun j k q => phiHat_covBC hs _ 1 _ _ q (hO.w () k q),
    fun j => covPin_covBC hs _ one_ne_zero (hO.cov ()), ?_, fun j => hO.model₂ ()⟩
  · exact (RingHom.ext fun _ => rfl : _ = (inC O.c').comp O.jL).trans hO.lift.field
  · obtain ⟨g, r, c0L, hT, hc⟩ := hO.lift.c0
    refine ⟨g, r, c0L, hT, fun v => ?_⟩
    obtain ⟨v', hv', e⟩ := hc v
    exact ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV (incF O.c' c₃ hs) _ _ v'.2⟩, (congrArg (MvPolynomial.map (incF O.c' c₃ hs)) hv').trans (MvPolynomial.map_map _ _ _),
      (hc0 v' _ rfl).trans e⟩
  · refine ⟨h, J', repsR_map _ hr, fun x₀ => ?_, thAdIs_thAdOf R i A.μ0 h c0₃ hV hr.2.2.1 hr.2.2.2.2.2.1 v₀, fun _ => Iff.rfl⟩
    obtain ⟨x, hx⟩ := hpl x₀
    exact ⟨fun k => ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV (incF O.c' c₃ hs) _ _ (x k).2⟩, fun k => (hx k).trans (hc0 _ _ rfl).symm⟩
  · refine (cXiVal_iff _ _ _ _ _ _ _ _ _).2 ⟨a, ha, fun j => ?_⟩
    have key := GlobalTheory.OneMapAll.cXiAt_covBC D _ _ _ _ _ _ _ _ hs _ _ _ 1 _ _ _ _ _ _ (hO.cov ()).1.2.2.2.2.2.2.2.1 (hca ())
    exact (congrArg (GlobalTheory.OneMapAll.CXiAt _ _ _ _ _ _ _ _ _) (one_mul a)).mp key

end Change

section Tuple


open Classical in
variable (D) in
def TupOver (i : Fin D.R.m) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (βV : ∀ i, GL (Fin (Vc D i).rank) (Lev.EAf D))
    (βW : ∀ i, GL (Fin (Wc D i).rank) (Lev.EAf D)) (χ : Formalism.L2.Host.HChar D.host.E) (ξ : (AE D)ˣ →* Circle)
    (ξR : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ) {K' : Type} [Field K'] (σ' : K' →+* ℂ)
    {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (bad : ℕ) (Mb I : Ideal (𝓞 D.host.E)) (N : Submodule (𝓞 D.host.E) La) {Cl : Type} (h : Cl → GA D (Vc D i))
    (J' : Subgroup (Bridge.Gf (Vc D i))) (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : K')
    (B : Ideal (𝓞 D.host.E) → K') (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (φ : (Fin (Vc D i).rank → La ⧸ N) → K') : Prop :=
  (bad ≠ 0 ∧ (∀ PP, PP ∈ Pg ∨ PP ∈ Q → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
    J' ≤ (levEnv (Vc D i) (βV i) (datY _ D.R.r D.R.t 1 (r_le_V i) Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.A)).J ∧
    J'.relIndex (levEnv (Vc D i) (βV i)
      (datY _ D.R.r D.R.t 1 (r_le_V i) Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.A)).J ≠ 0 ∧
    vol = ((J'.relIndex (levEnv (Vc D i) (βV i)
      (datY _ D.R.r D.R.t 1 (r_le_V i) Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.A)).J : ℕ) : K')⁻¹ ∧
    Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k)) ∧
    ∀ k, SplitOffBad (Vc D i) bad (h k) ∧ Lh k = Bridge.hLat (Vc D i) (fin _ (h k)) ∧
      gam k = Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) J' (fin _ (h k)))) ∧
  (∀ cc : Ideal (𝓞 D.host.E), cc ≠ ⊥ → cc ⊔ Ideal.span {((bad : ℕ) : 𝓞 D.host.E)} = ⊤ →
    σ' (B cc) = ((χ.onId (cc : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ)) ∧
  (∀ (g : GA D (Wc D i)) (x : (AE D)ˣ), IsDetRoot (Wc D i) g x →
    ((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) : ℂˣ) : ℂ) = ((ξ x : Circle) : ℂ)) ∧
  (∃ e : AE D, IsIdemSum e (Pg ∪ Q) ∧ ∀ x : Fin (Vc D i).rank → La,
    IsIntM (uMat (Vc D i) (Wc D i) (βV i) (βW i) e fun b => ι (x b)) ∧
    σ' (φ fun b => Submodule.Quotient.mk (x b)) =
      omegaK Pg (fun PP => redM PP (uMat (Vc D i) (Wc D i) (βV i) (βW i) e fun b => ι (x b))) *
        omegaQ Q (Wc D i).rank ξR (-1) (fun PP => redM PP (uMat (Vc D i) (Wc D i) (βV i) (βW i) e fun b => ι (x b)))) ∧
  (Mb = ∏ PP ∈ Pg, PP.asIdeal ∧ (∀ PP ∈ Q, I ≤ PP.asIdeal) ∧
    ∀ PP, PP ∈ Pg ∨ PP ∈ Q → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)

variable {i : Fin D.R.m} {K' : Type} [Field K'] {σ' : K' →+* ℂ}
  {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] {ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {bad : ℕ} {Mb I : Ideal (𝓞 D.host.E)} {N : Submodule (𝓞 D.host.E) La} {Cl : Type} {h : Cl → GA D (Vc D i)}
  {J' : Subgroup (Bridge.Gf (Vc D i))} {Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)} {gam : Cl → ℕ} {vol : K'}
  {B : Ideal (𝓞 D.host.E) → K'} {xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ} {φ : (Fin (Vc D i).rank → La ⧸ N) → K'}


set_option maxHeartbeats 1000000 in
theorem tupOver_iff {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T0) :
    TupOver D i R.Pg (R.Q t) R.βV R.βW (R.C.mu0 i * R.xiH t * R.C.eta⁻¹) (R.xi t) (R.xiR t) σ' ι bad Mb I N h J' Lh gam vol B xi φ ↔
      RepsR R i t h bad J' Lh gam vol ∧ BIs R i σ' t bad B ∧ XiIs R i t xi ∧ PhiIs R i σ' t ι N φ ∧ HalfIs R t Mb I := Iff.rfl

theorem tupOver_cast {Pg₁ Pg₂ Q₁ Q₂ : Finset (Formalism.L2.DIV.Pl D.host.E)} {βV₁ βV₂ βW₁ βW₂ χ₁ χ₂ ξ₁ ξ₂ ξR₁ ξR₂}
    (hP : HEq Pg₂ Pg₁) (hQ₁ : Q₁ = ∅) (hQ₂ : Q₂ = ∅) (hV : HEq βV₂ βV₁) (hW : HEq βW₂ βW₁) (hχ : χ₂ = χ₁) (hξ : ξ₂ = ξ₁)
    (H : TupOver D i Pg₁ Q₁ βV₁ βW₁ χ₁ ξ₁ ξR₁ σ' ι bad Mb I N h J' Lh gam vol B xi φ) :
    TupOver D i Pg₂ Q₂ βV₂ βW₂ χ₂ ξ₂ ξR₂ σ' ι bad Mb I N h J' Lh gam vol B xi φ := by
  cases hP; cases hV; cases hW
  subst hQ₁ hQ₂ hχ hξ
  obtain ⟨h1, h2, h3, ⟨e, he, h4⟩, h5⟩ := H
  refine ⟨h1, h2, h3, ⟨e, he, fun x => ⟨(h4 x).1, (h4 x).2.trans ?_⟩⟩, h5⟩
  simp [omegaQ]

end Tuple

section Same

variable {D' : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0' T0' : Type} {A' : FamIn D'.what₂.LL G' Pl0' T0' D'.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  {C' : Core D'} [Algebra C'.Q.c.F D'.what₂.LL] {R' : RealDat D' A' C'.Q.c.F} {i' : Fin D'.R.m}

structure SameGeo (O' : OMDat C' R' i' Unit (fun _ => A'.μ0)) (M : OMDat C R i Unit (fun _ => A.μ0)) : Prop where
  c' : HEq O'.c' M.c'
  lev : HEq O'.lev M.lev
  dδ : HEq O'.dδ M.dδ
  Cl' : O'.Cl' = M.Cl'
  fCl : HEq O'.fCl M.fCl
  bad : O'.bad = M.bad
  Lh : HEq O'.Lh M.Lh
  La : HEq O'.La M.La
  Nc : HEq O'.Nc M.Nc
  gam : HEq O'.gam M.gam
  vol : HEq O'.vol M.vol
  ep : HEq O'.ep M.ep
  B : HEq O'.B M.B
  epF : HEq O'.epF M.epF
  io : HEq O'.io M.io
  hw : HEq O'.hw M.hw
  φ : HEq O'.φ M.φ
  w : HEq O'.w M.w
  U₂ : HEq O'.U₂ M.U₂
  dict₂ : HEq O'.dict₂ M.dict₂
  xi : HEq O'.xi M.xi

def IsBCOf (O' : OMDat C' R' i' Unit (fun _ => A'.μ0)) (v₀' : (R'.MW i' (sg0 D' A')).Vec) (O : OMDat C R i Unit (fun _ => A.μ0))
    (v₀ : (R.MW i (sg0 D A)).Vec) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))
    (ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) (P : Prop) : Prop :=
  ∃ c₃ hs c0₃ io₃ hw₃ h J', IsBC O c₃ hs c0₃ io₃ hw₃ h v₀ κ ι x₀ J' ∧ SameGeo O' (bc O c₃ hs c0₃ io₃ hw₃ h v₀) ∧
    (HEq O'.c0' c0₃ ∨ P) ∧ ∃ (h' : O'.Cl' () → GA D' (Vc D' i')) (J'' : Subgroup (Bridge.Gf (Vc D' i'))), HEq h' h ∧ HEq J'' J' ∧
      RepsR R' i' A'.μ0 h' (O'.bad ()) J'' (O'.Lh ()) (O'.gam ()) (O'.vol ()) ∧ PlaceEx R' i' A'.μ0 h' O'.c0' ∧
      ThAdIs R' i' A'.μ0 h' O'.c0' v₀' (O'.thAd ()) ∧ ∀ x, O'.Plc () x ↔ ∃ x₀, Place R' i' A'.μ0 h' O'.c0' (jVx R' i' A'.μ0 x₀) x

theorem IsBCOf.lev {O' : OMDat C' R' i' Unit (fun _ => A'.μ0)} {v₀'} {O : OMDat C R i Unit (fun _ => A.μ0)} {v₀ κ ι x₀ P}
    (h : IsBCOf O' v₀' O v₀ κ ι x₀ P) : HEq O'.lev O.lev := by
  obtain ⟨_, _, _, _, _, _, _, -, hs, -⟩ := h
  exact hs.lev

end Same

theorem wtA_eq {j : ℕ} (κ κ' : WeightFamilies.Wt D j) (hP : κ'.aP = κ.aP) (hM : κ'.aM = κ.aM) : wtA κ' = wtA κ := by
  funext x
  simp only [wtA, hP, hM]

end GlobalTheory.Mem.R3.Rw.OmExt

end
end

module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescentFromCompleteRegularCharts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitsOfModuliPointHaveIsomorphicProportionalLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedSymmetricCubicalBundleExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidCubicalExtensionPullbackOfToricChartStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SabBaseChangeStIffFree
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SabPullCompare

variable {S S' : Scheme.{0}}

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem lbIso_cubeLB {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L M : LB G.left} (h : LBIso L M) : LBIso (cubeLB G x L) (cubeLB G x M) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨_, DVR.linCombIso_isGen w hw _ _⟩

theorem cubeLB_isLB {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L : LB G.left} (h : L.IsLB) : (cubeLB G x L).IsLB := DVR.linComb_isLB _ h _ _

end GlobalTheory.SabPullCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleOnDescendedGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointnessIsoExtendsDescendedGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointnessIsoExtendsDescendedGroup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ExtAdj

section Gen
variable {X Y B : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_normalized {ψ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ B) (e : B ⟶ Y) (he : e ≫ p = 𝟙 B)
    (s : LB.Gen (LB.LinComb L ψ ε)) (hs : s.IsGen) :
    ∃ s₂ : LB.Gen (LB.LinComb L (Sum.elim ψ (fun k => p ≫ e ≫ ψ k)) (Sum.elim ε (fun k => -ε k))),
      s₂.IsGen ∧ ∀ y J, Good L y J → val s₂ e y J = 1 := by
  refine ⟨LB.mulGen L _ _ _ _ s (LB.pullGen L _ _ (LB.invGen L _ _ (LB.pullGen L ψ ε s e)) p),
    DVR.mulGen_isGen _ _ _ _ _ _ _ hs (DVR.pullGen_isGen _ _ _ _ (DVR.invGen_isGen _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ hs e)) p), fun y J hJ => ?_⟩
  rw [val_mul hJ, val_pull hJ, val_inv, val_pull hJ, he, Category.id_comp, mul_inv_cancel]

theorem formEq_sec {ψ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ B) (e : B ⟶ Y) (he : e ≫ p = 𝟙 B) :
    FormEq (K := PEmpty) (PEmpty.elim : PEmpty → (B ⟶ X)) PEmpty.elim
      (fun k => e ≫ Sum.elim ψ (fun k => p ≫ e ≫ ψ k) k) (Sum.elim ε (fun k => -ε k)) := by
  intro U _ h
  rw [Fintype.prod_empty, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, ← Category.assoc, he, Category.id_comp, zpow_neg, Finset.prod_inv_distrib,
    mul_inv_cancel]
end Gen

section Cube
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S}

def cφ (x : Fin 2 → (T ⟶ G)) : ULift.{0} (Finset (Fin 2)) → (T.left ⟶ G.left) := fun I => (psum G x I.down).left

def cε : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

theorem cls_diff {L : LB G.left} (hL : L.IsLB) (x₁ x₂ : Fin 2 → (T ⟶ G))
    (h : (LB.LinComb L (Sum.elim (cφ x₁) (cφ x₂)) (Sum.elim cε (fun I => -cε I))).IsLB) :
    CechPic.cls _ h = CechPic.cls (LB.LinComb L (cφ x₁) cε) (LB.isLB_linComb hL _ _) -
      CechPic.cls (LB.LinComb L (cφ x₂) cε) (LB.isLB_linComb hL _ _) := by
  rw [CechPic.cls_linComb hL, CechPic.cls_linComb hL, CechPic.cls_linComb hL, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem lbIso_of_gen {L : LB G.left} (hL : L.IsLB) (x₁ x₂ : Fin 2 → (T ⟶ G))
    (t : LB.Gen (LB.LinComb L (Sum.elim (cφ x₁) (cφ x₂)) (Sum.elim cε (fun I => -cε I)))) (ht : t.IsGen) :
    LBIso (cubeLB G x₁ L) (cubeLB G x₂ L) := by
  have z := (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨t, ht⟩
  rw [cls_diff hL x₁ x₂, sub_eq_zero] at z
  exact (CechPic.cls_eq_iff _ _).1 z

theorem gen_of_lbIso {L : LB G.left} (hL : L.IsLB) (x₁ x₂ : Fin 2 → (T ⟶ G))
    (H : LBIso (cubeLB G x₁ L) (cubeLB G x₂ L)) :
    ∃ t : LB.Gen (LB.LinComb L (Sum.elim (cφ x₁) (cφ x₂)) (Sum.elim cε (fun I => -cε I))), t.IsGen := by
  refine (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
  rw [cls_diff hL x₁ x₂, sub_eq_zero]
  exact (CechPic.cls_eq_iff (LB.isLB_linComb hL (cφ x₁) cε) (LB.isLB_linComb hL (cφ x₂) cε)).2 H

end Cube

section Origin
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem eSec_cφ (x : Fin 2 → (G2 G ⟶ G)) (hx : ∀ i, η[G2 G] ≫ x i = 1) (I : ULift.{0} (Finset (Fin 2))) :
    eSec (G2 G) ≫ cφ x I = eSec G := by
  have h1 : η[G2 G] ≫ psum G x I.down = 1 := by
    have a := psum_hom (preHom (G := G) η[G2 G]) x I.down
    have b := psum_hom (1 : (𝟙_ (Over S) ⟶ G) →* (𝟙_ (Over S) ⟶ G)) (fun _ => 1) I.down
    simp only [MonoidHom.one_apply] at b
    exact a.trans ((congrArg (fun z => psum G z I.down) (funext hx)).trans b.symm)
  have h2 := congrArg (fun z => z.left) h1
  simp only [Over.comp_left] at h2
  refine h2.trans ?_
  simp [Hom.one_def, eSec]

theorem eSec_x2 (i : Fin 2) : η[G2 G] ≫ x2 G i = η[G] := by
  fin_cases i <;> simp [x2]

theorem one_cube₁ (f : G ⟶ G) [IsMonHom f] (i : Fin 2) : η[G2 G] ≫ (![fst G G ≫ f, snd G G] : Fin 2 → (G2 G ⟶ G)) i = 1 := by
  fin_cases i <;> simp [Hom.one_def]

theorem one_cube₂ (f : G ⟶ G) [IsMonHom f] (i : Fin 2) : η[G2 G] ≫ (![fst G G, snd G G ≫ f] : Fin 2 → (G2 G ⟶ G)) i = 1 := by
  fin_cases i <;> simp [Hom.one_def]
end Origin

section Push
variable {S U : Scheme.{0}} {j : U ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G]
  {A : Over U} [GrpObj A] [IsCommMonObj A] {e : A.left ⟶ G.left}

abbrev jTwo (he : IsGrpPullback A G j e) : (G2 A).left ⟶ (G2 G).left :=
  (lift (pushPt he.1.w (fst A A)) (pushPt he.1.w (snd A A))).left

theorem doubleProductMapOfGrpPullback_comp_doubleCoordinate (he : IsGrpPullback A G j e) (i : Fin 2) : jTwo he ≫ (x2 G i).left = (x2 A i).left ≫ e := by
  fin_cases i
  · exact congrArg (fun z => z.left) (lift_fst (pushPt he.1.w (fst A A)) (pushPt he.1.w (snd A A)))
  · exact congrArg (fun z => z.left) (lift_snd (pushPt he.1.w (fst A A)) (pushPt he.1.w (snd A A)))

theorem eSec_jTwo (he : IsGrpPullback A G j e) : eSec (G2 A) ≫ jTwo he = j ≫ eSec (G2 G) := by
  refine GlobalTheory.Mum.PowCart.square_over_hom_ext _ fun i => ?_
  have a : eSec (G2 A) ≫ (x2 A i).left = eSec A := congrArg (fun z => Over.Hom.left z) (eSec_x2 (G := A) i)
  have b : eSec (G2 G) ≫ (x2 G i).left = eSec G := congrArg (fun z => Over.Hom.left z) (eSec_x2 (G := G) i)
  rw [Category.assoc, doubleProductMapOfGrpPullback_comp_doubleCoordinate, ← Category.assoc, a, Category.assoc, b]
  exact (cubeMapOf he).e_comm

theorem cφ_push (he : IsGrpPullback A G j e) (x' : Fin 2 → (G2 A ⟶ A)) (x : Fin 2 → (G2 G ⟶ G))
    (hx : ∀ i, (x' i).left ≫ e = jTwo he ≫ (x i).left) (I : ULift.{0} (Finset (Fin 2))) :
    cφ x' I ≫ e = jTwo he ≫ cφ x I :=
  psum_push he x' x (lift (pushPt he.1.w (fst A A)) (pushPt he.1.w (snd A A)))
    (fun i => Over.OverMorphism.ext (by rw [Over.comp_left]; exact hx i)) I.down
end Push

section Drop
variable {X Y B : Scheme.{0}} {K0 : Type} [Fintype K0]

theorem formEq_drop {ψ : K0 ⊕ K0 → (Y ⟶ X)} {ε₀ : K0 → ℤ} (p : Y ⟶ B) (e : B ⟶ Y) (z : B ⟶ X)
    (hz : ∀ k, e ≫ ψ k = z) :
    FormEq (Sum.elim ψ (fun k => p ≫ e ≫ ψ k))
      (Sum.elim (Sum.elim ε₀ (fun k => -ε₀ k)) (fun k => -(Sum.elim ε₀ (fun k => -ε₀ k)) k))
      ψ (Sum.elim ε₀ (fun k => -ε₀ k)) := by
  intro U _ h
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hz, zpow_neg, neg_neg, inv_inv,
    Finset.prod_inv_distrib]
  group
end Drop

theorem adj_extends : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∀ (act : OAct (𝓞 E) G), (∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left) → ∀ (PP : RigLB G) (cub : CubicalStr G PP) (cm : CubeMap tF.G G), cm.F = e → cm.e = j → cm.IsPullCubical tF.cub cub → ∀ a, LBIso (cubeLB G ![fst G G ≫ act.act a, snd G G] PP.L) (cubeLB G ![fst G G, snd G G ≫ act.act (H.bar a)] PP.L) := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hU _ tF _ G _ _ e hsa he _ act hact PP cub cm hF _ hpc a
  obtain ⟨⟨-, -, -, -, -, -⟩, -, -, -, ⟨⟨hnorm, -⟩, hproj, -, hdense, -, -⟩, -⟩ := hU
  have := hsa.smooth
  have := hsa.geomConnected
  haveI : LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    infer_instance
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  haveI : IsDominant j := ⟨hdense⟩
  have hS : Geo.Tor.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff_pred S).mp hnorm
  obtain ⟨w, hw, -, -⟩ := hpc
  have hw' := (isGen_iff w).1 hw
  haveI := act.hom a
  haveI := act.hom (H.bar a)
  haveI := tF.act.hom a
  haveI := tF.act.hom (H.bar a)
  let x₁ : Fin 2 → (G2 G ⟶ G) := ![fst G G ≫ act.act a, snd G G]
  let x₂ : Fin 2 → (G2 G ⟶ G) := ![fst G G, snd G G ≫ act.act (H.bar a)]
  let y₁ : Fin 2 → (G2 tF.G ⟶ tF.G) := ![fst tF.G tF.G ≫ tF.act.act a, snd tF.G tF.G]
  let y₂ : Fin 2 → (G2 tF.G ⟶ tF.G) := ![fst tF.G tF.G, snd tF.G tF.G ≫ tF.act.act (H.bar a)]
  let ψ := Sum.elim (cφ x₁) (cφ x₂)
  let ψ' := Sum.elim (cφ y₁) (cφ y₂)
  let ε₁ : ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)) → ℤ := Sum.elim cε (fun I => -cε I)
  obtain ⟨s, hs⟩ := gen_of_lbIso tF.PP.isLB y₁ y₂ (tF.adj a)
  obtain ⟨s₂, hs₂, h1⟩ := exists_normalized (G2 tF.G).hom (eSec (G2 tF.G)) (CubeExtension.eSec_comp _) s hs
  have hsm := CubeExtension.smooth_tensor G G
  have hgc := CubeExtension.geometricallyConnected_tensor G G
  have hpb : IsPullback (jTwo he) (G2 tF.G).hom (G2 G).hom j := GlobalTheory.Mum.PowCart.isPullback_two he.1
  have f0 : jTwo he ≫ (fst G G).left = (fst tF.G tF.G).left ≫ e := doubleProductMapOfGrpPullback_comp_doubleCoordinate he 0
  have f1 : jTwo he ≫ (snd G G).left = (snd tF.G tF.G).left ≫ e := doubleProductMapOfGrpPullback_comp_doubleCoordinate he 1
  have hψ : ∀ k, ψ' k ≫ e = jTwo he ≫ ψ k := by
    rintro (I | I)
    · refine cφ_push he y₁ x₁ (fun i => ?_) I
      fin_cases i
      · show (fst tF.G tF.G ≫ tF.act.act a).left ≫ e = jTwo he ≫ (fst G G ≫ act.act a).left
        rw [Over.comp_left, Over.comp_left, Category.assoc, hact a, ← Category.assoc, ← f0, Category.assoc]
      · exact f1.symm
    · refine cφ_push he y₂ x₂ (fun i => ?_) I
      fin_cases i
      · exact f0.symm
      · show (snd tF.G tF.G ≫ tF.act.act (H.bar a)).left ≫ e = jTwo he ≫ (snd G G ≫ act.act (H.bar a)).left
        rw [Over.comp_left, Over.comp_left, Category.assoc, hact (H.bar a), ← Category.assoc, ← f1, Category.assoc]
  have hφ : ∀ k, Sum.elim ψ' (fun k => (G2 tF.G).hom ≫ eSec (G2 tF.G) ≫ ψ' k) k ≫ cm.F =
      jTwo he ≫ Sum.elim ψ (fun k => (G2 G).hom ≫ eSec (G2 G) ≫ ψ k) k := by
    rw [hF]
    rintro (k | k)
    · exact hψ k
    · simp only [Sum.elim_inr, Category.assoc]
      rw [hψ k, ← Category.assoc (eSec (G2 tF.G)), eSec_jTwo he, Category.assoc, ← Category.assoc (G2 tF.G).hom,
        ← hpb.w, Category.assoc]
  obtain ⟨c', hc', -⟩ := DenseCubeExt.exists_extension hS j (G2 G).hom (eSec (G2 G)) (jTwo he) (G2 tF.G).hom
    (eSec (G2 tF.G)) hsm hgc (CubeExtension.eSec_comp _) hpb (eSec_jTwo he) PP.isLB tF.PP.isLB hw'
    (Sum.elim ψ (fun k => (G2 G).hom ≫ eSec (G2 G) ≫ ψ k)) (Sum.elim ψ' (fun k => (G2 tF.G).hom ≫ eSec (G2 tF.G) ≫ ψ' k))
    (Sum.elim ε₁ (fun k => -ε₁ k)) hφ (formEq_sec _ _ (CubeExtension.eSec_comp _))
    (formEq_sec _ _ (CubeExtension.eSec_comp _)) s₂ hs₂ h1
  have hz : ∀ k, eSec (G2 G) ≫ ψ k = eSec G := by
    rintro (I | I)
    · exact eSec_cφ x₁ (one_cube₁ (act.act a)) I
    · exact eSec_cφ x₂ (one_cube₂ (act.act (H.bar a))) I
  obtain ⟨t, ht, -⟩ := exists_gen PP.isLB (formEq_drop (ε₀ := cε) (G2 G).hom (eSec (G2 G)) (eSec G) hz) c' hc'
  exact lbIso_of_gen PP.isLB x₁ x₂ t ht

end GlobalTheory.ExtAdj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointnessIsoExtendsDescendedGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianAdjointnessIso_extends_descendedGroup : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∀ (act : OAct (𝓞 E) G), (∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left) → ∀ (PP : RigLB G) (cub : CubicalStr G PP) (cm : CubeMap tF.G G), cm.F = e → cm.e = j → cm.IsPullCubical tF.cub cub → ∀ a, LBIso (cubeLB G ![fst G G ≫ act.act a, snd G G] PP.L) (cubeLB G ![fst G G, snd G G ≫ act.act (H.bar a)] PP.L) := by
  first | exact @GlobalTheory.ExtAdj.adj_extends | exact GlobalTheory.ExtAdj.adj_extends | (intros; apply GlobalTheory.ExtAdj.adj_extends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationIsoExtendsDescendedGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationIsoExtendsDescendedGroup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PrimExt

theorem refl_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem lbIso_pull_of_range_subset {X Y Y' : Scheme.{0}} (e : Y ⟶ X) [IsOpenImmersion e] (f : Y' ⟶ X)
    (hf : Set.range f.base ⊆ Set.range e.base) (L M : LB X) (h : LBIso (L.pull e) (M.pull e)) :
    LBIso (L.pull f) (M.pull f) := by
  have hc : f = IsOpenImmersion.lift e f hf ≫ e := (IsOpenImmersion.lift_fac e f hf).symm
  exact LBIso.chartPull (chartPullSame L _ _ _ _ fun _ => hc) (chartPullSame M _ _ _ _ fun _ => hc) h

theorem prim_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    (tF : SAB H S') (G : Over S) [GrpObj G] [IsCommMonObj G] (j : S' ⟶ S) (e : tF.G.left ⟶ G.left)
    (he : IsGrpPullback tF.G G j e) (act : OAct (𝓞 E) G)
    (hact : ∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left) (PP : RigLB G)
    (hw : LBIso tF.PP.L (PP.L.pull e)) :
    LBIso (PP.L.pull e) ((cubeLB G ![𝟙 G, act.act H.w0] PP.L).pull e) := by
  have hP : (PP.L.pull e).IsLB := pull_isLB PP.isLB e
  have hC : (cubeLB G ![𝟙 G, act.act H.w0] PP.L).IsLB := GlobalTheory.SabPullCompare.cubeLB_isLB _ PP.isLB
  let U := pushPt he.1.w (𝟙 tF.G)
  have hU : U.left = e := by simp [U, pushPt]
  have hc : ∀ I : ULift.{0} (Finset (Fin 2)),
      (psum tF.G ![𝟙 tF.G, tF.act.act H.w0] I.down).left ≫ e = e ≫ (psum G ![𝟙 G, act.act H.w0] I.down).left :=
    fun I => (psum_push he ![𝟙 tF.G, tF.act.act H.w0] ![𝟙 G, act.act H.w0] U (fun i => by
      fin_cases i
      · apply Over.OverMorphism.ext
        simp [U, pushPt]
      · apply Over.OverMorphism.ext
        simp [U, pushPt, hact]) I.down).trans (by rw [hU])
  have h4 : LBIso (cubeLB tF.G ![𝟙 tF.G, tF.act.act H.w0] (PP.L.pull e))
      ((cubeLB G ![𝟙 G, act.act H.w0] PP.L).pull e) :=
    LBIso.chartPull (chartPullLinComb PP.L e _ _ _ e hc) (chartPullPull _ e) (refl_of_isLB hC)
  refine LBIso.trans hP tF.PP.isLB (pull_isLB hC e) hw.symm ?_
  refine LBIso.trans tF.PP.isLB (GlobalTheory.SabPullCompare.cubeLB_isLB _ tF.PP.isLB) (pull_isLB hC e) tF.prim ?_
  exact LBIso.trans (GlobalTheory.SabPullCompare.cubeLB_isLB _ tF.PP.isLB) (GlobalTheory.SabPullCompare.cubeLB_isLB _ hP)
    (pull_isLB hC e) (GlobalTheory.SabPullCompare.lbIso_cubeLB _ hw) h4

theorem lbIso_prim_ext : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∀ (act : OAct (𝓞 E) G), (∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left) → ∀ (PP : RigLB G) (cub : CubicalStr G PP) (cm : CubeMap tF.G G), cm.F = e → cm.e = j → cm.IsPullCubical tF.cub cub → LBIso PP.L (cubeLB G ![𝟙 G, act.act H.w0] PP.L) := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hUP _ tF _ G _ _ e hG he _ act hact PP cub cm hF _ hlin
  obtain ⟨-, -, -, -, ⟨⟨hS, -⟩, hproj, -, hdense, -⟩, -⟩ := hUP
  have : IsLocallyNoetherian S := by
    obtain ⟨N', im, _, h⟩ := hproj
    have : LocallyOfFiniteType (π ≫ zs) := h ▸ inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  have hS' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S := by haveI := hS; exact GlobalTheory.IsNormalScheme.pred S
  have hw : LBIso tF.PP.L (PP.L.pull e) := by
    obtain ⟨w, hw, -⟩ := hlin
    exact hF ▸ ⟨w, hw⟩
  have : IsOpenImmersion e := MorphismProperty.of_isPullback he.1.flip inferInstance
  have hr : Set.range e.base = G.hom.base ⁻¹' Set.range j.base := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      show (e ≫ G.hom) y ∈ Set.range j
      rw [he.1.w]
      exact ⟨_, rfl⟩
    · intro hx
      have hx' : x ∈ Set.range (pullback.fst G.hom j) := by
        rw [Scheme.Pullback.range_fst]
        exact hx
      obtain ⟨z, rfl⟩ := hx'
      refine ⟨he.1.isoPullback.inv z, ?_⟩
      rw [← Scheme.Hom.comp_apply, he.1.isoPullback_inv_fst]
  haveI := act.hom H.w0
  haveI := hG.smooth
  haveI : GeometricallyIntegral G.hom := @GlobalTheory.geometricallyIntegral_of_isSemiAbelian _ G _ hG
  let V : S.Opens := j.opensRange
  haveI : IsDominant V.ι := ⟨by
    show Dense (Set.range V.ι)
    rw [Scheme.Opens.range_ι]
    simpa [V] using hdense⟩
  have hC : (cubeLB G ![𝟙 G, act.act H.w0] PP.L).IsLB := GlobalTheory.SabPullCompare.cubeLB_isLB _ PP.isLB
  have hsec : eSec G ≫ G.hom = 𝟙 S := Over.w η[G]
  have hrig : CechPic.pull (eSec G) (CechPic.cls PP.L PP.isLB) = 0 :=
    (CechPic.cls_eq_zero_iff (pull_isLB PP.isLB _)).2 ⟨PP.rig, PP.rigGen⟩
  refine (CechPic.cls_eq_iff PP.isLB hC).1 (GlobalTheory.ZH.EndoExtend.pic_ext V.ι hS' G (eSec G) hsec ?_ ?_)
  · rw [hrig, GlobalTheory.ZH.EndoExtend.cls_cubeLB G _ PP.isLB]
    have hp := GlobalTheory.ZH.EndoExtend.pull_cubeCls G ![𝟙 G, act.act H.w0]
      (fun _ : Fin 2 => (η[G] : 𝟙_ (Over S) ⟶ G)) η[G]
      (fun i => by
        fin_cases i
        · simp
        · simp [IsMonHom.one_hom]) (CechPic.cls PP.L PP.isLB)
    exact (GlobalTheory.ZH.EndoExtend.cubeCls_one G _ hrig).symm.trans hp.symm
  · refine (CechPic.cls_eq_iff (pull_isLB PP.isLB _) (pull_isLB hC _)).2 ?_
    refine lbIso_pull_of_range_subset e _ ?_ _ _ (prim_pull tF G j e he act hact PP hw)
    rw [Scheme.Pullback.range_fst, hr, Scheme.Opens.range_ι]
    rfl

end GlobalTheory.PrimExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationIsoExtendsDescendedGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalPolarisationIso_extends_descendedGroup : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∀ (act : OAct (𝓞 E) G), (∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left) → ∀ (PP : RigLB G) (cub : CubicalStr G PP) (cm : CubeMap tF.G G), cm.F = e → cm.e = j → cm.IsPullCubical tF.cub cub → LBIso PP.L (cubeLB G ![𝟙 G, act.act H.w0] PP.L) := by
  first | exact @GlobalTheory.PrimExt.lbIso_prim_ext | exact GlobalTheory.PrimExt.lbIso_prim_ext | (intros; apply GlobalTheory.PrimExt.lbIso_prim_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRingActionCompatibleExtended
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRingActionCompatibleExtended
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChart

theorem denseRange_jK (R : Type) [CommRing R] [IsDomain R] : DenseRange (jK R) := by
  let ξ : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  intro y
  have hs : jK R ξ ⤳ y := (PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => by
    have h₁ : algebraMap R (FractionRing R) a ∈ IsLocalRing.maximalIdeal (FractionRing R) := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h₁
    obtain rfl : a = 0 := IsFractionRing.injective R (FractionRing R) (h₁.trans (map_zero _).symm)
    exact Ideal.zero_mem _
  exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self (f := jK R) ξ)) (specializes_iff_mem_closure.1 hs)

theorem isDominant_of_isPullback_jK {R : Type} [CommRing R] [IsDomain R] {X X' : Scheme.{0}}
    (p : X ⟶ Sp R) [Smooth p] (p' : X' ⟶ Sp (FractionRing R)) (φ : X' ⟶ X) (h : IsPullback φ p' p (jK R)) :
    IsDominant φ := by
  have hd : IsDominant (pullback.fst p (jK R)) := by
    refine ⟨?_⟩
    rw [DenseRange, Scheme.Pullback.range_fst]
    exact (denseRange_jK R).preimage p.isOpenMap
  have e : h.isoPullback.hom ≫ pullback.fst p (jK R) = φ := h.isoPullback_hom_fst
  rw [← e]
  infer_instance

theorem act_chart_compat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R]
    [IsDomain R] (tC : SAB H (Sp R)) {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (ξ : Sp R ⟶ S)
    (πC : tC.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tC.G G ξ πC → ∀ (act : OAct (𝓞 E) G)
    (tK : SAB H (Sp (FractionRing R))) (a : SABMap tK tC (jK R)) (ψ : tK.G.left ⟶ G.left),
    (∀ u, (tK.act.act u).left ≫ ψ = ψ ≫ (act.act u).left) → a.φ ≫ πC = ψ →
    ∀ u, (tC.act.act u).left ≫ πC = πC ≫ (act.act u).left := by
  intro E _ _ _ H R _ _ tC S G _ _ ξ πC hG hP act tK a ψ hψ hφ u
  haveI : IsSeparated G.hom := hG.separated
  haveI : Smooth tC.G.hom := tC.semi.smooth
  haveI : IsReduced tC.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced tC.G.hom
  haveI : IsDominant a.φ := isDominant_of_isPullback_jK tC.G.hom tK.G.hom a.φ a.cart.1
  have hw : πC ≫ G.hom = tC.G.hom ≫ ξ := hP.1.w
  refine ext_of_isDominant_of_isSeparated G.hom ?_ a.φ ?_
  · rw [Category.assoc, Category.assoc, hw, Over.w (act.act u), hw, ← Category.assoc, Over.w (tC.act.act u)]
  · have e : (tK.act.act u).left ≫ a.φ = a.φ ≫ (tC.act.act u).left := a.act u
    rw [← Category.assoc, ← e, Category.assoc, hφ, hψ, ← hφ, Category.assoc]

end GlobalTheory.UChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRingActionCompatibleExtendedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_ringAction_compatible_extended : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] [IsDomain R] (tC : SAB H (Sp R)) {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (ξ : Sp R ⟶ S) (πC : tC.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tC.G G ξ πC → ∀ (act : OAct (𝓞 E) G) (tK : SAB H (Sp (FractionRing R))) (a : SABMap tK tC (jK R)) (ψ : tK.G.left ⟶ G.left), (∀ u, (tK.act.act u).left ≫ ψ = ψ ≫ (act.act u).left) → a.φ ≫ πC = ψ → ∀ u, (tC.act.act u).left ≫ πC = πC ≫ (act.act u).left := by
  first | exact @GlobalTheory.UChart.act_chart_compat | exact GlobalTheory.UChart.act_chart_compat | (intros; apply GlobalTheory.UChart.act_chart_compat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionExtendDescendedSemiAbelian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionExtendDescendedSemiAbelian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DescAct

theorem exists_oAct_extend_toSemiAbelian_normBl : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∃ act : OAct (𝓞 E) G, ∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hU _ tF _ G _ _ e hG he _
  obtain ⟨-, -, -, -, ⟨hBl, hP, -, hd, -⟩, -⟩ := hU
  have : AlgebraicGeometry.IsNoetherian S := GlobalTheory.isNoetherian_of_isProjOver hP
  have : IsDominant j := ⟨hd⟩
  haveI : GlobalTheory.IsNormalScheme S := hBl.1
  obtain ⟨a, ha, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.existsUnique_oAct_of_isGrpPullback
    GlobalTheory.semiAbelianHomExtension_holds (GlobalTheory.IsNormalScheme.pred S) hG he tF.act
  exact ⟨a, ha⟩

end GlobalTheory.DescAct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionExtendDescendedSemiAbelianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringAction_extend_descended_semiAbelian : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∃ act : OAct (𝓞 E) G, ∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left := by
  first | exact @GlobalTheory.DescAct.exists_oAct_extend_toSemiAbelian_normBl | exact GlobalTheory.DescAct.exists_oAct_extend_toSemiAbelian_normBl | (intros; apply GlobalTheory.DescAct.exists_oAct_extend_toSemiAbelian_normBl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleOnDescendedGroup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DescTriple

theorem exists_triple_of_group_sepB : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∃ t : SAB H S, abLocus t.G = abLocus G ∧ Nonempty (SABMap tF t j) ∧ ∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → Nonempty (SABMap C.t t ξ) := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hns Z zs i OZ N d J S π j _ BD hU _hSep hPre tF mF G _ _ e hsemi he hch
  obtain ⟨act, hact⟩ := GlobalTheory.T.exists_ringAction_extend_descended_semiAbelian Xo c φ hpq hfan hns zs i OZ N d J π j BD hU hPre tF mF G e hsemi he hch
  obtain ⟨PP, cub, sym, cm, hcm, hce, hlin⟩ :=
    GlobalTheory.T.exists_rigidified_symmetric_cubicalBundle_extension Xo c φ hpq hfan hns zs i OZ N d J π j BD hU hPre tF mF G e hsemi he hch
  have adj := GlobalTheory.T.hermitianAdjointnessIso_extends_descendedGroup Xo c φ hpq hfan hns zs i OZ N d J π j BD hU hPre tF mF G e hsemi he hch act hact PP cub cm
    hcm hce hlin
  have prim := GlobalTheory.T.principalPolarisationIso_extends_descendedGroup Xo c φ hpq hfan hns zs i OZ N d J π j BD hU hPre tF mF G e hsemi he hch act hact PP cub cm
    hcm hce hlin
  let t : SAB H S := ⟨G, hsemi, act, PP, cub, sym, adj, prim⟩
  refine ⟨t, rfl, ⟨⟨cm, hcm ▸ he, hce, fun a => by rw [hcm]; exact hact a, hlin⟩⟩, ?_⟩
  intro k _ m n C hC ξ hξ
  obtain ⟨tK, ⟨a⟩, ⟨mU⟩⟩ := C.gen
  obtain ⟨b, -⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t tF tK (pullback.fst _ _) C.y mF mU
  obtain ⟨πC, hπ, hab⟩ := hch C hC ξ hξ tK a b
  have hactC := GlobalTheory.T.chart_ringAction_compatible_extended C.t G ξ πC hsemi hπ act tK a (b.φ ≫ e) (fun u => by
    rw [← Category.assoc, b.act u, Category.assoc, hact u, Category.assoc]) hab
  obtain ⟨cm', hcm', hce', hlin'⟩ :=
    GlobalTheory.T.rigidCubicalExtension_pullback_of_toricChart C.t G ξ πC hsemi hπ PP cub tF j e cm hcm hce hlin C.y hξ tK a b hab
  exact ⟨⟨cm', hcm' ▸ hπ, hce', fun u => by rw [hcm']; exact hactC u, hlin'⟩⟩

end GlobalTheory.DescTriple
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleOnDescendedGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_triple_on_descended_group : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∃ t : SAB H S, abLocus t.G = abLocus G ∧ Nonempty (SABMap tF t j) ∧ ∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → Nonempty (SABMap C.t t ξ) := by
  first | exact @GlobalTheory.DescTriple.exists_triple_of_group_sepB | exact GlobalTheory.DescTriple.exists_triple_of_group_sepB | (intros; apply GlobalTheory.DescTriple.exists_triple_of_group_sepB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianDescentOfToricChartsCorrectedSe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidifiedBundlePullbackUniversalTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidifiedBundlePullbackUniversalTriple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullAmpleXF

theorem relAmple_XF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (tF : SAB H (Xo.XF c)) :
    SABMap tF Xo.univ.t (pullback.fst _ _) → RelAmple tF.G tF.PP.L := by
  intro mF
  have hP : IsProper tF.G.hom := MorphismProperty.of_isPullback (P := @IsProper) mF.cart.1 Xo.univ.proper
  obtain ⟨w, hw, -⟩ := mF.lin
  refine GlobalTheory.AmpleLocal.relAmple_of_locally _ tF.G tF.PP.L tF.PP.isLB inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := Xo.X) (U := ⊤)
    (x := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) s) trivial
  let f := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)
  let U := f ⁻¹ᵁ V
  refine ⟨U, hs, ?_⟩
  have H : IsPullback ((tF.G.hom ⁻¹ᵁ U).ι ≫ mF.φ) (tF.G.hom ∣_ U) Xo.univ.t.G.hom (U.ι ≫ f) :=
    (isPullback_morphismRestrict tF.G.hom U).flip.paste_horiz mF.cart.1
  obtain ⟨w', hw'⟩ : LBIso (tF.PP.L.pull (tF.G.hom ⁻¹ᵁ U).ι) (Xo.univ.t.PP.L.pull ((tF.G.hom ⁻¹ᵁ U).ι ≫ mF.φ)) :=
    LBIso.chartPull (chartPullPull _ _)
      (chartPullSame Xo.univ.t.PP.L (fun _ : PUnit => (tF.G.hom ⁻¹ᵁ U).ι ≫ mF.φ) (fun _ => mF.φ) (fun _ => 1)
        (tF.G.hom ⁻¹ᵁ U).ι fun _ => rfl) ⟨w, hw⟩
  exact relAmple_pull (A' := Over.mk (tF.G.hom ∣_ U)) H Xo.univ.t.PP.isLB (pull_isLB tF.PP.isLB _)
    ((isGen_iff w').1 hw') V hV (fun y => y.2) Xo.univ.ample

end GlobalTheory.PullAmpleXF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidifiedBundlePullbackUniversalTripleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_rigidifiedBundle_pullback_universalTriple : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → RelAmple tF.G tF.PP.L := by
  first | exact @GlobalTheory.PullAmpleXF.relAmple_XF | exact GlobalTheory.PullAmpleXF.relAmple_XF | (intros; apply GlobalTheory.PullAmpleXF.relAmple_XF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIsGrpPullbackOfUniversalTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIsGrpPullbackOfUniversalTriple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem genOf_isGrpPullback : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] (y : Sp (FractionRing R) ⟶ Xo.XF c) (t : SAB H (Sp R)) (tF : SAB H (Xo.XF c)), GlobalTheory.UPoinc.GenOf Xo c y t → SABMap tF Xo.univ.t (pullback.fst _ _) → ∃ α : pullback t.G.hom (jK R) ⟶ tF.G.left, IsGrpPullback ((Over.pullback (jK R)).obj t.G) tF.G y α := by
  intro E _ _ _ H Dw l Xo c R _ _ y t tF hy mF
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := hy
  obtain ⟨b⟩ := GlobalTheory.TraitOrder.cancel rfl mF m₂
  obtain ⟨e, he, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.grpPullback_iso (isGrpPullback_pullback t.G (jK R)) m₁.cart
  haveI := he
  exact ⟨e.hom.left ≫ b.φ,
    ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso e).comp b.cart).congr (Category.id_comp _) rfl⟩

end GlobalTheory.UPoinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIsGrpPullbackOfUniversalTripleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_isGrpPullback_of_universalTriple : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] (y : Sp (FractionRing R) ⟶ Xo.XF c) (t : SAB H (Sp R)) (tF : SAB H (Xo.XF c)), GlobalTheory.UPoinc.GenOf Xo c y t → SABMap tF Xo.univ.t (pullback.fst _ _) → ∃ α : pullback t.G.hom (jK R) ⟶ tF.G.left, IsGrpPullback ((Over.pullback (jK R)).obj t.G) tF.G y α := by
  first | exact @GlobalTheory.UPoinc.genOf_isGrpPullback | exact GlobalTheory.UPoinc.genOf_isGrpPullback | (intros; apply GlobalTheory.UPoinc.genOf_isGrpPullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySemiAbelianCompletionChartOfOpenPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySemiAbelianCompletionChartOfOpenPart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Desc.OpenChart

theorem completedStalk_chart (X : Scheme.{0}) (x : X) [IsNoetherianRing (X.presheaf.stalk x)] :
    GlobalTheory.fromSpecCompletedStalk X x (closedPoint _) = x ∧
    IsEtaleCompletion (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x)).hom ∧
      Function.Surjective ((residue (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
        (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x)).hom) := by
  have fg : (maximalIdeal (X.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  let φ := algebraMap (X.presheaf.stalk x) (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
  haveI : IsLocalHom φ := ((IsLocalRing.local_hom_tfae φ).out 1 3).mpr hm.symm.le
  have hres : Function.Surjective ((residue _).comp φ) := by
    intro r
    obtain ⟨a, ha⟩ := (AdicCompletion.residueField_map_bijective (X.presheaf.stalk x)).2 r
    obtain ⟨b, rfl⟩ := residue_surjective a
    refine ⟨b, ?_⟩
    rw [← ha, RingHom.comp_apply, ResidueField.map_residue]
  have hx : GlobalTheory.fromSpecCompletedStalk X x (closedPoint _) = x := by
    rw [GlobalTheory.fromSpecCompletedStalk]
    erw [Scheme.Hom.comp_apply]
    have hc : Spec.map (CommRingCat.ofHom φ) (closedPoint _) = closedPoint (X.presheaf.stalk x) :=
      IsLocalRing.comap_closedPoint φ
    erw [hc]
    exact Scheme.fromSpecStalk_closedPoint
  obtain ⟨e, he, hψ⟩ := GlobalTheory.GenFan.stalk_factor_eq hx (CommRingCat.ofHom φ)
    (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x))
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _)
  refine ⟨hx, ?_, ?_⟩
  · rw [hψ]
    exact GlobalTheory.TorRef.isEtaleCompletion_comp_bij e he φ ⟨RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _),
      hm.symm, RingHom.Finite.of_surjective _ hres⟩
  · rw [hψ, ← RingHom.comp_assoc]
    exact hres.comp he.2

theorem nonempty_chart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) {S : Scheme.{0}} (j : Xo.XF c ⟶ S) [IsOpenImmersion j]
    (A : Over (Xo.XF c)) [GrpObj A], IsSemiAbelian A → ∀ x ∈ Set.range j, Nonempty (GlobalTheory.Desc.Chart j A x) := by
  intro E _ _ _ H Dw l Xo c S j _ A _ hA x hx
  obtain ⟨x', rfl⟩ := hx
  haveI : Smooth Xo.s := by haveI := Xo.smooth; exact SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  haveI hreg : IsRegularLocalRing ((Xo.XF c).presheaf.stalk x') :=
    GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth_field
      (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) x'
  obtain ⟨hcen, hEt, hres⟩ := completedStalk_chart (Xo.XF c) x'
  obtain ⟨ιF⟩ := GlobalTheory.GenFan.exists_ringHom_stalk c.F (Xo.XF c)
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) x'
  set St := (Xo.XF c).presheaf.stalk x'
  set R := AdicCompletion (maximalIdeal St) St
  haveI : IsRegularLocalRing R := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion St
  haveI : IsDomain R := GlobalTheory.isDomain_of_isRegularLocalRing R
  let g : Sp R ⟶ Xo.XF c := GlobalTheory.fromSpecCompletedStalk (Xo.XF c) x'
  have hcz : CharZero R := (RingHom.charZero_iff ((algebraMap St R).comp ιF).injective).1 inferInstance
  have hb : Function.Bijective (j.stalkMap (g (closedPoint R))).hom :=
    ConcreteCategory.bijective_of_isIso _
  refine ⟨{
    R := R
    complete := inferInstance
    charZero := hcz
    ξ := g ≫ j
    centre := by
      show j (g (closedPoint R)) = j x'
      rw [hcen]
    etc := GlobalTheory.MemberEt.isEtaleCompletion_comp_openImmersion _ _ j R g hEt
    unr := by
      apply RingHom.FormallyUnramified.of_surjective
      rw [Scheme.stalkClosedPointTo_comp]
      exact hres.comp hb.2
    G := (Over.pullback g).obj A
    semi := IsSemiAbelian.pullback (f := g) A hA
    y := jK R ≫ g
    hy := Category.assoc _ _ _
    α := pullback.fst ((Over.pullback g).obj A).hom (jK R) ≫ pullback.fst A.hom g
    gen := IsGrpPullback.comp (isGrpPullback_pullback _ (jK R)) (isGrpPullback_pullback A g) }⟩

end GlobalTheory.Desc.OpenChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySemiAbelianCompletionChartOfOpenPartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_semiAbelianCompletionChart_of_openPart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) {S : Scheme.{0}} (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (A : Over (Xo.XF c)) [GrpObj A], IsSemiAbelian A → ∀ x ∈ Set.range j, Nonempty (GlobalTheory.Desc.Chart j A x) := by
  first | exact @GlobalTheory.Desc.OpenChart.nonempty_chart | exact GlobalTheory.Desc.OpenChart.nonempty_chart | (intros; apply GlobalTheory.Desc.OpenChart.nonempty_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianDescentOfToricChartsCorrectedSe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChartDesc

theorem exists_semiAbelian_of_charts : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∃ (G : Over S) (_ : GrpObj G) (_ : IsCommMonObj G) (e : tF.G.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback tF.G G j e ∧ abLocus G = Set.range j ∧ ∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hnsi Z zs i OZ N d J S π j _ BD hP hpre tF mF
  have hNoeth : AlgebraicGeometry.IsNoetherian S := GlobalTheory.isNoetherian_of_isProjOver hP.2.2.2.2.1.2.1
  have hNorm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff_pred S).1 hP.2.2.2.2.1.1.1
  have hdom : IsDominant j := ⟨hP.2.2.2.2.1.2.2.2.1⟩
  have hAab : IsAbelianScheme tF.G :=
    ⟨tF.comm, tF.semi.smooth, MorphismProperty.of_isPullback (P := @IsProper) mF.cart.1 Xo.univ.proper, tF.semi.geomConnected⟩
  have hLB : tF.PP.L.IsLB := tF.PP.isLB
  have hAmp : RelAmple tF.G tF.PP.L := GlobalTheory.T.relAmple_rigidifiedBundle_pullback_universalTriple Xo c tF mF
  have hkc : ∀ (k : Type) [Field k], IsAdicComplete (maximalIdeal k) k := fun k _ => by
    rw [maximalIdeal_eq_bot]; infer_instance

  have bdChart : ∀ (x : S) (k : Type) [Field k] (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e))
      (ξ : Sp (ChartRing k m e) ⟶ S), C.y ≫ j = jK _ ≫ ξ → ξ (closedPoint _) = x →
      IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom →
      ∃ Ch : GlobalTheory.Desc.Chart j tF.G x, ∀ (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ π : Ch.G.left ⟶ G.left,
        IsGrpPullback Ch.G G Ch.ξ π → (x ∈ abLocus G ↔ closedPoint (ChartRing k m e) ∈ abLocus C.t.G) := by
    intro x k _ m e C ξ hy hcl het
    haveI : CharZero (ChartRing k m e) := charZero_of_injective_ringHom C.b.injective
    haveI := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin e)
    haveI := hkc k
    obtain ⟨α, hα⟩ := GlobalTheory.T.genericFibre_isGrpPullback_of_universalTriple Xo c (ChartRing k m e) C.y C.t tF C.gen mF
    refine ⟨{ R := ChartRing k m e
              complete := GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
              charZero := inferInstance
              ξ := ξ
              centre := hcl
              etc := het
              unr := GlobalTheory.GenFan.formallyUnramified_residue_comp_of_isEtaleCompletion k m e _ het
              G := C.t.G
              semi := C.t.semi
              y := C.y
              hy := hy
              α := α
              gen := hα }, ?_⟩
    intro G _ hG π hπ
    rw [← hcl]
    exact abLocus_pullback abLocusOne hG hπ.1 (closedPoint _)
  have hch : ∀ x : S, Nonempty (GlobalTheory.Desc.Chart j tF.G x) := by
    intro x
    by_cases hx : x ∈ Set.range j
    · exact GlobalTheory.T.nonempty_semiAbelianCompletionChart_of_openPart Xo c j tF.G tF.semi x hx
    · obtain ⟨k, _, m, e, C, ξ, a, htaut, hy, hcl, het, -⟩ := hpre x hx
      obtain ⟨Ch, -⟩ := bdChart x k m e C ξ hy hcl het
      exact ⟨Ch⟩
  obtain ⟨G, _, e, hG, hpb, hmap⟩ := GlobalTheory.T.semiAbelian_descent_from_complete_regular_charts (Xo.XF c) S hNorm j hdom tF.G hAab tF.PP.L hLB hAmp hch
  haveI : IsCommMonObj G := hG.comm
  refine ⟨G, inferInstance, hG.comm, e, hG, hpb, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      by_contra hxj
      obtain ⟨k, _, m, e', C, ξ, a, htaut, hy, hcl, het, -, hset, -⟩ := hpre x hxj
      obtain ⟨Ch, hCh⟩ := bdChart x k m e' C ξ hy hcl het
      obtain ⟨π', hπ', -⟩ := hmap x Ch
      have hcp := (hCh G hG π' hπ').1 hx
      have hprod : ∏ i, C.s i ∈ (closedPoint (ChartRing k m e')).asIdeal := by
        by_contra hn
        exact hxj (hcl ▸ (hset _).2 hn)
      have hm : 1 ≤ C.m := by
        rcases Nat.eq_zero_or_pos C.m with h0 | h0
        · exfalso
          haveI : IsEmpty (Fin C.m) := by rw [h0]; infer_instance
          rw [Finset.univ_eq_empty, Finset.prod_empty] at hprod
          exact (maximalIdeal (ChartRing k m e')).ne_top_iff_one.1 (maximalIdeal.isMaximal _).ne_top hprod
        · exact h0
      exact GlobalTheory.T.closedPoint_notMem_abelianLocus_tautologicalBoundaryChart Xo c φ k m e' C htaut hm hcp
    · rintro ⟨x', rfl⟩
      rw [abLocus_pullback abLocusOne hG hpb.1 x']
      intro K _ _ t _
      haveI := hAab.proper
      infer_instance
  · intro k _ m n C hC ξ hξ tK a b
    haveI := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin n)
    haveI := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (ChartRing k m n)).2
    exact GlobalTheory.T.exists_grpPullback_map_semiAbelian_normalDomain (ChartRing k m n) j tF.G G e hG hpb C.t.G C.t.semi ξ C.y hξ tK.G a.φ b.φ a.cart b.cart

theorem exists_semiAbelian_of_charts_sepB : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∃ (G : Over S) (_ : GrpObj G) (_ : IsCommMonObj G) (e : tF.G.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback tF.G G j e ∧ abLocus G = Set.range j ∧ ∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hnsi Z zs i OZ N d J S π j _ BD hP _ hpre tF mF
  exact exists_semiAbelian_of_charts Xo c φ hpq hfan hnsi zs i OZ N d J π j BD hP hpre tF mF

end GlobalTheory.UChartDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianDescentOfToricChartsCorrectedSeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelian_descent_of_toricCharts_corrected_sep : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∃ (G : Over S) (_ : GrpObj G) (_ : IsCommMonObj G) (e : tF.G.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback tF.G G j e ∧ abLocus G = Set.range j ∧ ∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e := by
  first | exact @GlobalTheory.UChartDesc.exists_semiAbelian_of_charts_sepB | exact GlobalTheory.UChartDesc.exists_semiAbelian_of_charts_sepB | (intros; apply GlobalTheory.UChartDesc.exists_semiAbelian_of_charts_sepB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactificationIsModelOfCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChart

theorem exists_model_of_charts : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∃ (Y : Model Xo c (RingHom.id c.F)) (ε : Y.X ≅ S), Y.j ≫ ε.hom = j ∧ Y.s = ε.hom ≫ π ≫ zs ∧ ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → Nonempty (SABMap C.t Y.t (ξ ≫ ε.inv)) := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hsi Z zs i OZ N d J S π j _ BD hU hSep hPre
  obtain ⟨oF, ⟨m0⟩⟩ := GlobalTheory.LevelQuotRep.obj_pull_same Xo.univ
    (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
  obtain ⟨G, _, _, e, hGs, hGp, hGab, hGc⟩ := GlobalTheory.T.exists_semiAbelian_descent_of_toricCharts_corrected_sep Xo c φ hpq hfan hsi zs i OZ N d J π j BD hU hSep hPre oF.t m0.toSABMap
  obtain ⟨t, htab, ⟨mt⟩, htc⟩ := GlobalTheory.T.exists_triple_on_descended_group Xo c φ hpq hfan hsi zs i OZ N d J π j BD hU hSep hPre oF.t m0.toSABMap G e hGs hGp hGc
  obtain ⟨⟨-, -, -, -, hiz, -, -⟩, -, -, -, ⟨hNB, hproj, -, hjd, hji, -, -, -⟩, -⟩ := hU
  have eid : spMap (RingHom.id c.F) = 𝟙 _ := by simp [spMap]
  have hid : IsIso (spMap (RingHom.id c.F)) := by rw [eid]; infer_instance
  let g := pullback.fst (π ≫ zs) (spMap (RingHom.id c.F))
  have hg : IsIso g := inferInstance
  let jQ : Xo.XF c ⟶ pullback (π ≫ zs) (spMap (RingHom.id c.F)) := j ≫ inv g
  have hjQ : jQ ≫ g = j := by simp [jQ]
  have hab : abLocus t.G = Set.range j := htab.trans hGab
  let Y : Model Xo c (RingHom.id c.F) :=
    { X := S
      s := π ≫ zs
      normal := (GlobalTheory.isNormalScheme_iff S).1 hNB.1
      proj := hproj
      flat := inferInstance
      jQ := jQ
      jQ_over := by
        rw [← cancel_mono (spMap (RingHom.id c.F)), Category.assoc, ← pullback.condition, ← Category.assoc, hjQ,
          ← Category.assoc, hji, hiz, eid, Category.comp_id]
      jQ_open := inferInstance
      jQ_dense := by
        have hc : (⇑jQ) = (⇑(inv g)) ∘ ⇑j := by
          funext x
          simp [jQ]
        have h1 : DenseRange (⇑(inv g)) := (inv g).surjective.denseRange
        show DenseRange (⇑jQ)
        rw [hc]
        exact h1.comp hjd (inv g).continuous
      t := t
      oF := oF
      m0 := m0
      m := hjQ ▸ mt
      ab_gen := by
        show g ⁻¹' abLocus t.G = Set.range jQ
        rw [hab]
        ext x
        constructor
        · rintro ⟨y, hy⟩
          refine ⟨y, ?_⟩
          have h2 : (inv g) (g x) = x := by
            rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
          rw [← h2, ← hy]
          simp [jQ]
        · rintro ⟨y, rfl⟩
          refine ⟨y, ?_⟩
          rw [← Scheme.Hom.comp_apply, hjQ] }
  refine ⟨Y, Iso.refl S, ?_, ?_, ?_⟩
  · show (jQ ≫ g) ≫ 𝟙 S = j
    rw [hjQ, Category.comp_id]
  · show π ≫ zs = 𝟙 S ≫ π ≫ zs
    rw [Category.id_comp]
  · intro k _ m n C hC ξ hξ
    have := htc C hC ξ hξ
    simpa using this

end GlobalTheory.UChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactificationIsModelOfChartsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_compactification_isModel_of_charts : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∃ (Y : Model Xo c (RingHom.id c.F)) (ε : Y.X ≅ S), Y.j ≫ ε.hom = j ∧ Y.s = ε.hom ≫ π ≫ zs ∧ ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → Nonempty (SABMap C.t Y.t (ξ ≫ ε.inv)) := by
  first | exact @GlobalTheory.UChart.exists_model_of_charts | exact GlobalTheory.UChart.exists_model_of_charts | (intros; apply GlobalTheory.UChart.exists_model_of_charts <;> assumption)
end

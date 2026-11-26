module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerIntertwinerScalar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineSectionsExternalTensorPowerFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineSectionsExternalTensorPowerFibre
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
namespace GlobalTheory.BoxLine

theorem exists_isPullback_pow {S S' : Scheme.{0}} (g : S' ⟶ S) (G : Over S) (A B : Over S')
    (φ₀ : A.left ⟶ G.left) (h : IsPullback φ₀ A.hom G.hom g) (N : ℕ) (q : Fin N → (B ⟶ A))
    (hl : IsLimit (Fan.mk B q)) :
    ∃ φ : B.left ⟶ (pow G N).left, IsPullback φ B.hom (pow G N).hom g ∧
      ∀ k, φ ≫ pr G N k = (q k).left ≫ φ₀ := by
  let ψ : Over.mk (B.hom ≫ g) ⟶ pow G N := Pi.lift fun k =>
    Over.homMk ((q k).left ≫ φ₀) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [h.w, ← Category.assoc, Over.w])
  have hψ : ∀ k, ψ.left ≫ pr G N k = (q k).left ≫ φ₀ := fun k => by
    have : ψ ≫ Pi.π (fun _ => G) k = _ := Pi.lift_comp_π _ k
    exact congrArg (fun t => Over.Hom.left t) this
  have hw : ψ.left ≫ (pow G N).hom = B.hom ≫ g := Over.w ψ
  have hpr : ∀ k, pr G N k ≫ G.hom = (pow G N).hom := fun k => Over.w (Pi.π (fun _ => G) k)
  refine ⟨ψ.left, ⟨⟨hw⟩, ⟨?_⟩⟩, hψ⟩
  let c : ∀ s : PullbackCone (pow G N).hom g, Fin N → (Over.mk s.snd ⟶ A) := fun s k =>
    Over.homMk (h.lift (s.fst ≫ pr G N k) s.snd (by rw [Category.assoc, hpr, s.condition]))
      (h.lift_snd _ _ _)
  have hc : ∀ s k, (c s k).left ≫ φ₀ = s.fst ≫ pr G N k := fun s k => h.lift_fst _ _ _
  let m : ∀ s : PullbackCone (pow G N).hom g, Over.mk s.snd ⟶ B := fun s =>
    hl.lift (Fan.mk _ (c s))
  have hm : ∀ s k, (m s).left ≫ (q k).left = (c s k).left := fun s k =>
    congrArg (fun t => Over.Hom.left t) (hl.fac (Fan.mk _ (c s)) ⟨k⟩)
  refine PullbackCone.IsLimit.mk _ (fun s => (m s).left) ?_ ?_ ?_
  · intro s
    have hs : (m s).left ≫ B.hom = s.snd := Over.w (m s)
    let u : Over.mk (s.snd ≫ g) ⟶ pow G N := Over.homMk ((m s).left ≫ ψ.left) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [hw, ← Category.assoc, hs])
    let v : Over.mk (s.snd ≫ g) ⟶ pow G N := Over.homMk s.fst s.condition
    have huv : u = v := by
      refine Pi.hom_ext _ _ fun k => ?_
      ext1
      change ((m s).left ≫ ψ.left) ≫ pr G N k = s.fst ≫ pr G N k
      rw [Category.assoc, hψ, ← Category.assoc, hm, hc]
    exact congrArg (fun t => Over.Hom.left t) huv
  · intro s
    exact Over.w (m s)
  · intro s t h1 h2
    let u : Over.mk s.snd ⟶ B := Over.homMk t h2
    have : u = m s := by
      refine hl.uniq (Fan.mk _ (c s)) u ?_
      rintro ⟨k⟩
      ext1
      change t ≫ (q k).left = (c s k).left
      refine h.hom_ext ?_ ?_
      · rw [hc, Category.assoc, ← hψ, ← Category.assoc, h1]
      · rw [Category.assoc, Over.w, h2]
        exact (Over.w (c s k)).symm
    exact congrArg (fun t => Over.Hom.left t) this


open GlobalTheory.CechPic in
theorem cls_pull_box {S : Scheme.{0}} (G : Over S) (L : LB G.left) (hL : L.IsLB) (N : ℕ)
    {X : Scheme.{0}} (φ : X ⟶ (pow G N).left) (h : ((boxLB G L N).pull φ).IsLB) :
    cls ((boxLB G L N).pull φ) h = ∑ k, pull (φ ≫ pr G N k) (cls L hL) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cls_pull (LB.isLB_linComb hL _ _), cls_linComb hL, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_smul, pull_comp]

theorem isLB_triv (X : Scheme.{0}) : (LB.triv X).IsLB :=
  ⟨by simp, fun _ => map_one _, fun _ _ _ => by simp⟩


open GlobalTheory.CechPic in
theorem sections_line : ∀ (V K : Type) [CommRing V] [Field K] (f : V →+* K) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (rig : LB.Gen (L.pull (eSec G))) (θ : L.Sec) (n : ℕ) (w : Fin n → (epsR V ⟶ G)) (x : KeyIn K), L.IsLB → IsFibreOf x G L rig θ w f → ∀ N : ℕ, ∃ (X' : Scheme.{0}) (p' : X' ⟶ Sp K) (φ : X' ⟶ (pow G N).left) (L' : LB X') (b : L'.Sec), IsPullback φ p' (pow G N).hom (spMap f) ∧ L'.IsLB ∧ LBIso L' ((boxLB G L N).pull φ) ∧ ∀ s : L'.Sec, ∃ a : K, ∀ i, s.f i = constFn p' _ a * b.f i := by
  intro V K _ _ f G _ _ L rig θ n w x hL hx N
  obtain ⟨φ₀, he, e, hg, F, hpb, hegen, -⟩ := hx
  have hbox : ∀ {X : Scheme.{0}} (φ : X ⟶ (pow G N).left), ((boxLB G L N).pull φ).IsLB :=
    fun φ => LB.isLB_linComb (LB.isLB_linComb hL _ _) _ _
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain ⟨φ, hφ, -⟩ := exists_isPullback_pow (spMap f) G x.P.A (Over.mk (𝟙 (Sp K))) φ₀ hpb.1 0
      (fun k => k.elim0)
      (Fan.IsLimit.mk _ (fun s => Over.mkIdTerminal.from _) (fun _ k => k.elim0)
        (fun _ _ _ => Over.mkIdTerminal.hom_ext _ _))
    refine ⟨Sp K, 𝟙 _, φ, LB.triv _, ⟨fun _ => 1, fun _ _ => by simp⟩, hφ, isLB_triv _, ?_, ?_⟩
    · rw [iso_triv_iff, ← cls_eq_zero_iff (hbox φ), cls_pull_box G L hL]
      simp
    · intro s
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (s.f PUnit.unit), fun i => ?_⟩
      obtain rfl : i = PUnit.unit := rfl
      have h0 : ∀ (h : (⊤ : (Sp K).Opens) ≤ ⊤) (t : Γ(Sp K, ⊤)),
          ((Sp K).presheaf.map (homOfLE h).op).hom t = t := fun h t => by
        rw [show homOfLE h = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
        rfl
      simp [constFn, Scheme.Hom.appLE]
      exact (h0 _ _).symm
  · obtain ⟨y, p, -⟩ := GlobalTheory.KeyPow.exists_isKeyPow K x N hN
    obtain ⟨φ, hφ, hc⟩ := exists_isPullback_pow (spMap f) G x.P.A y.P.A φ₀ hpb.1 N p.pr p.lim
    obtain ⟨b, hb⟩ := principalPolarisation_exists_unique_section GlobalTheory.firstFiveLaws.2.1.secTwist y.P
    refine ⟨y.P.A.left, y.P.A.hom, φ, y.P.L, b, hφ, y.P.isLB, ?_, fun s => (hb s).exists⟩
    have h1 : cls x.P.L x.P.isLB = pull φ₀ (cls L hL) := by
      rw [← cls_pull hL φ₀ (LB.isLB_linComb hL _ _), cls_eq_iff]
      exact ⟨e, hegen⟩
    have h2 : cls y.P.L y.P.isLB
        = cls (Out.boxLB x.P.L p.pr) (LB.isLB_linComb x.P.isLB _ _) := by
      rw [cls_eq_iff]
      exact ⟨p.w, p.w_gen⟩
    rw [← cls_eq_iff y.P.isLB (hbox φ), cls_pull_box G L hL, h2, cls_linComb x.P.isLB]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_smul, hc, pull_comp, h1]

end GlobalTheory.BoxLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineSectionsExternalTensorPowerFibreStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_line_sections_externalTensorPower_fibre : ∀ (V K : Type) [CommRing V] [Field K] (f : V →+* K) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (rig : LB.Gen (L.pull (eSec G))) (θ : L.Sec) (n : ℕ) (w : Fin n → (epsR V ⟶ G)) (x : KeyIn K), L.IsLB → IsFibreOf x G L rig θ w f → ∀ N : ℕ, ∃ (X' : Scheme.{0}) (p' : X' ⟶ Sp K) (φ : X' ⟶ (pow G N).left) (L' : LB X') (b : L'.Sec), IsPullback φ p' (pow G N).hom (spMap f) ∧ L'.IsLB ∧ LBIso L' ((boxLB G L N).pull φ) ∧ ∀ s : L'.Sec, ∃ a : K, ∀ i, s.f i = constFn p' _ a * b.f i := by
  first | exact @GlobalTheory.BoxLine.sections_line | exact GlobalTheory.BoxLine.sections_line | (intros; apply GlobalTheory.BoxLine.sections_line <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricThetaTranslatesExpandSeriesFamilies
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricThetaTranslatesExpandSeriesFamilies
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.MBLow
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.UT.CoefBasic GlobalTheory.UT.SymFrame GlobalTheory.Ex.GtValues GlobalTheory.Ex.CoordSeries

theorem symTranslate_expandsF : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U.toUnifPre w₀ ρ → ∀ (th : GlobalTheory.UT.SecA A C 1) (ϑ : Fam D.toPre C 1) (c : C), U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) → ∀ m : ℕ, Odd m → ∀ (p : QkPt D.toPre C (m ^ 2)) (q : N.QT (m ^ 2)) (z : TFK (R := V) C ⟶ A.A), ν.QPt p q → QkToAkU U.toUnifPre C (m ^ 2) p z → ∃ (Θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := V) C)) (t : GlobalTheory.UT.SecA A C (m ^ 2)) (s : Fam D.toPre C (m ^ 2)) (f : N.X → N.A → C), SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) z Θ ∧ Tr A ρ m th Θ t ∧ U.ExpandsF C (m ^ 2) w₀ t s ∧ IsEvFam N m q f ∧ ν.FamV s (c • f) := by
  intro V _ _ _ _ hcpl D A G _ _ hG U C _ _ _ _ _ _ hC N ν _ w₀ ρ hN th ϑ c hth hϑ m hm p q z hq hz
  have hL : GlobalTheory.UT.LL := GlobalTheory.Ex.hv_holds.1
  have hfam : BrFamSt := GlobalTheory.Ex.brFam hL.1 hL.2.1
  have hB : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcpl⟩
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  have hLB := A.isLB
  let y : Sp C := IsLocalRing.closedPoint C

  have hgt : ∀ b : N.A, ∃ h : N.Gt, h.b = b := fun b => by
    obtain ⟨g, hg⟩ := GlobalTheory.TorusExt.exists_lift (D := D.toPre) (F := C) (ν.eA b)
    obtain ⟨h, hh⟩ := GtValues.exists_val ν g
    exact ⟨h, ν.eA.injective (hh.1.trans hg)⟩
  have main : ∀ (th : GlobalTheory.UT.SecA A C 1) (ϑ : Fam D.toPre C 1) (c : C), U.ExpandsF C 1 w₀ th ϑ →
      ν.FamV ϑ (c • N.vth) → ∃ (Θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := V) C)) (t : GlobalTheory.UT.SecA A C (m ^ 2))
        (s : Fam D.toPre C (m ^ 2)) (f : N.X → N.A → C),
        SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) z Θ ∧ Tr A ρ m th Θ t ∧ U.ExpandsF C (m ^ 2) w₀ t s ∧ ν.FamV s f ∧
        (∀ (h : N.Gt) (χ : N.X), f (q.1.1.toAdd + m • χ) h.b * h.s (q.1.1.toAdd + m • χ) = c * N.evT m q h χ) ∧
        ∀ β, (∀ χ, β ≠ q.1.1.toAdd + m • χ) → ∀ x, f β x = 0 := by
    intro th ϑ c hth hϑ
    obtain ⟨⟨_, _⟩, ⟨α, s₁, -, hα, hαn, hs₁, -⟩, -⟩ :=
      GlobalTheory.existsUnique_thetaConst hL V A C ρ hN.2.1 m hm th 1 (one_pow _)
    have hbij := (expBijF_and_expandsF_lin hL V _ hB D A G hG U).1 C (m ^ 2) hm2 w₀ hN.1
    obtain ⟨σ₁, hσ₁, -⟩ := hbij.1 s₁
    obtain ⟨hv₁, -, -, -, -, hv₂⟩ := hfam V D.toPre D.psi_even D.tau_bimult C N ν (m ^ 2) hm2
    obtain ⟨f₁, hf₁, -⟩ := hv₁ σ₁
    obtain ⟨E, hEG, hEA, hEB, hEh, hEact⟩ := (IntEnd.exists_nsmul_and_neg hL V _ hB D A G hG U).1 m
    have hsm : ∀ {X : Type} [AddCommGroup X] [Module.Free ℤ X], Function.Injective fun χ : X => m • χ := by
      intro X _ _ a b h
      have h' : (m : ℤ) • a = (m : ℤ) • b := by simpa only [natCast_zsmul] using h
      exact smul_right_injective _ (Int.natCast_ne_zero.2 hm0) h'
    have hinj : Function.Injective E.h := fun a b h => hsm (by simpa only [hEh] using h)
    have hpull := (PullExp.main hL V _ hB D A G hG U C E hinj (m ^ 2) 1 le_rfl hm2
      (GlobalTheory.UT.ThetaSum.exists_gen_pow U.LG U.cubG U.symG U.symG_gen m E.aG hEG)).2 w₀ ρ hN (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _)
      (lift_fst _ _) (by rw [hEA, MonObj.comp_pow, Category.comp_id]) α hα hαn th s₁ ϑ σ₁ hth hσ₁ hs₁
    rw [hEB] at hpull
    obtain ⟨κ, hκ⟩ := exists_kap (D := D.toPre) hL.1.mulPull m
    have pull : ∀ h : N.Gt, (∀ χ, f₁ (m • χ) h.b * h.s (m • χ) =
        c * N.vt (h ^ m) χ * ((mulq N.θ N.σ m h.b)⁻¹ : Cˣ)) ∧ ∀ β, (∀ χ, β ≠ m • χ) → f₁ β h.b = 0 := fun h => by
      obtain ⟨g, hg⟩ := GtValues.exists_pt ν h
      obtain ⟨g', hg'⟩ := GtValues.exists_pt ν (h ^ m)
      have act := (hEact C g g').2 ((isNsmul_val ν m hg hg').2 rfl)
      obtain ⟨W, hW⟩ := (coef_basic V D.toPre C (m ^ 2) g).1
      obtain ⟨w, hw, hwv⟩ := exists_frm_kap (act.1.trans (congrArg _ hEB)) W hW κ hκ.1
      obtain ⟨r₁, r₂⟩ := hpull κ hκ g g' act W w hW hw hwv
      have hJ := good ν y
      have e₁ : val κ g.b.left y ν.J = _ := hg.1 ▸ kap_eq ν hL.1.globalFns hκ y h.b
      have e₂ : vF w (𝟙 (Sp C)) ν.J = vF W (𝟙 (Sp C)) ν.J * ((mulq N.θ N.σ m h.b)⁻¹ : Cˣ) :=
        (toStk y).injective ((GtValues.toStk_vF _ _ hJ).trans ((congrArg Units.val (hwv y ν.J hJ)).symm.trans
          (((Units.val_mul _ _).trans (congrArg₂ (· * ·) (GtValues.toStk_vF _ _ hJ).symm (congrArg Units.val e₁))).trans
            (map_mul (toStk y) _ _).symm)))
      refine ⟨fun χ => mul_right_cancel₀ (vF_ne ν W) ?_, fun β hβ => ?_⟩
      · have a := r₁ (ν.eX χ)
        rw [hEh, ← map_nsmul, coef_val ν hf₁ hg hW, coef_theta ν hϑ hg' hw, e₂] at a
        rw [a]; ring
      · have a := r₂ (ν.eX β) (by
          rintro ⟨χ, e⟩
          exact hβ (ν.eX.symm χ) (ν.eX.injective (by rw [map_nsmul, ν.eX.apply_symm_apply, ← hEh, e])))
        rw [coef_val ν hf₁ hg hW] at a
        exact (mul_eq_zero.1 ((mul_eq_zero.1 a).resolve_right (vF_ne ν W))).resolve_right (Units.ne_zero _)
    obtain ⟨⟨_, _⟩, ⟨_, _, θ, -, -, -, hθ, -⟩, -⟩ :=
      GlobalTheory.existsUnique_thetaConst hL V A C ρ hN.2.1 m hm th z (hz w₀ hN.1).1
    obtain ⟨t, ht⟩ := ThetaPtExist.exists_isTwistPull hLB (translT A.A θ.pt) (translPt A.A θ.pt) (lift_snd _ _)
      ((m ^ 2 : ℕ) : ℤ) ((m ^ 2 : ℕ) : ℤ) θ.φ θ.isGen s₁
    obtain ⟨σ, hσ, -⟩ := hbij.1 t
    obtain ⟨f, hf, -⟩ := hv₁ σ
    obtain ⟨w, hw⟩ := (SymFrame.main hL V _ hB D C (m ^ 2) hm.pow p).1
    have hΦ := symLift_acts_as_phi hL V _ hB D A G hG U C (m ^ 2) hm.pow p z hz θ hθ w₀ hN.1 w hw s₁ t σ₁ σ
      hσ₁ hσ ht
    obtain rfl := (hv₂ p q w _ σ₁ σ f₁ f hq hw.1 (txFrame_val ν hL.1 hm.pow hq hw) hf₁ hf).1 hΦ
    have on : ∀ (h : N.Gt) (χ : N.X), N.phi q (N.wQ q) f₁ (q.1.1.toAdd + m • χ) h.b * h.s (q.1.1.toAdd + m • χ) =
        c * N.evT m q h χ := fun h χ => by
      rw [add_comm]
      exact phi_term N m q h f₁ c χ ((pull _).1 χ)
    have off : ∀ β, (∀ χ, β ≠ q.1.1.toAdd + m • χ) → ∀ x, N.phi q (N.wQ q) f₁ β x = 0 := fun β hβ x => by
      obtain ⟨h, hh⟩ := hgt (x * q.1.2.b)
      have a := (pull h).2 (β - q.1.1.toAdd) fun χ e => hβ χ (by rw [← e, add_sub_cancel])
      rw [hh] at a
      rw [NumD.phi, a, mul_zero]
    exact ⟨θ, t, σ, _, hθ, ⟨α, s₁, hα, hαn, hs₁, ht⟩, hσ, hf, on, off⟩
  obtain ⟨Θ, t, s, f, h1, h2, h3, h4, h5, h6⟩ := main th ϑ c hth hϑ
  refine ⟨Θ, t, s, ?_⟩
  by_cases hc : c = 0
  · subst hc
    obtain ⟨th', ϑ', c₀, hc₀, hth', hϑ', -⟩ := exists_theta hL hfam U hN.1 ν
    obtain ⟨-, -, -, f', -, -, -, -, h5', h6'⟩ := main th' ϑ' c₀ hth' hϑ'
    refine ⟨c₀⁻¹ • f', h1, h2, h3, ⟨fun h χ => ?_, fun β hβ x => ?_⟩, ?_⟩
    · rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, h5', inv_mul_cancel_left₀ hc₀]
    · rw [Pi.smul_apply, Pi.smul_apply, h6' β hβ x, smul_zero]
    · rw [zero_smul]
      convert h4 using 1
      funext β x
      rw [Pi.zero_apply, Pi.zero_apply]
      by_cases hβ : ∃ χ, β = q.1.1.toAdd + m • χ
      · obtain ⟨χ, rfl⟩ := hβ
        obtain ⟨h, rfl⟩ := hgt x
        have e := h5 h χ
        rw [zero_mul] at e
        exact ((mul_eq_zero.1 e).resolve_right (Units.ne_zero _)).symm
      · push_neg at hβ
        exact (h6 β hβ x).symm
  · refine ⟨c⁻¹ • f, h1, h2, h3, ⟨fun h χ => ?_, fun β hβ x => ?_⟩, ?_⟩
    · rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, h5, inv_mul_cancel_left₀ hc]
    · rw [Pi.smul_apply, Pi.smul_apply, h6 β hβ x, smul_zero]
    · rwa [smul_smul, mul_inv_cancel₀ hc, one_smul]

end GlobalTheory.MBLow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricThetaTranslatesExpandSeriesFamiliesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricThetaTranslates_expand_seriesFamilies : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U.toUnifPre w₀ ρ → ∀ (th : GlobalTheory.UT.SecA A C 1) (ϑ : Fam D.toPre C 1) (c : C), U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) → ∀ m : ℕ, Odd m → ∀ (p : QkPt D.toPre C (m ^ 2)) (q : N.QT (m ^ 2)) (z : TFK (R := V) C ⟶ A.A), ν.QPt p q → QkToAkU U.toUnifPre C (m ^ 2) p z → ∃ (Θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := V) C)) (t : GlobalTheory.UT.SecA A C (m ^ 2)) (s : Fam D.toPre C (m ^ 2)) (f : N.X → N.A → C), SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) z Θ ∧ Tr A ρ m th Θ t ∧ U.ExpandsF C (m ^ 2) w₀ t s ∧ IsEvFam N m q f ∧ ν.FamV s (c • f) := by
  first | exact @GlobalTheory.MBLow.symTranslate_expandsF | exact GlobalTheory.MBLow.symTranslate_expandsF | (intros; apply GlobalTheory.MBLow.symTranslate_expandsF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesDeformationOfBoundedLatticeSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesReparamBoundedCoefficients
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem regroup_fib_tsum {X M : Type} [AddCommMonoid M] [TopologicalSpace M] (n : X → ℕ) (i : ℕ)
    (h : {α | n α = i}.Finite) (f : X → M) :
    ∑' b : n ⁻¹' {i}, f b = ∑ α ∈ h.toFinset, f α := by
  have hs : n ⁻¹' {i} = (h.toFinset : Set X) := by ext; simp
  rw [← Finset.tsum_subtype', ← hs]

theorem lattice_series_regroup : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (X : Type) (n : X → ℕ) (π : C) (a : X → C) (b : ℝ), π ≠ 0 → ‖π‖ < 1 → (∀ i, {α | n α = i}.Finite) → (∀ α, ‖a α‖ ≤ b * ‖π‖ ^ n α) → ∃ Θ : PowerSeries C, (∀ i, ‖PowerSeries.coeff i Θ‖ ≤ max b 0) ∧ ∑' i, PowerSeries.coeff i Θ * π ^ i = ∑' α, a α ∧ ∀ (e : C →+* ℂ) (u : ℂ), (Summable fun α => ‖e (a α) * (u / e π) ^ n α‖) → (Summable fun i => ‖e (PowerSeries.coeff i Θ) * u ^ i‖) ∧ ∑' i, e (PowerSeries.coeff i Θ) * u ^ i = ∑' α, e (a α) * (u / e π) ^ n α := by
  intro C _ _ _ X n π a b hπ0 hπ1 hfin hb
  classical
  have hmem : ∀ i α, α ∈ (hfin i).toFinset ↔ n α = i := fun i α => by simp
  have hn : Filter.Tendsto n Filter.cofinite Filter.atTop := by
    refine Filter.tendsto_atTop.2 fun N => Filter.eventually_cofinite.2 ?_
    refine ((Set.finite_lt_nat N).biUnion fun i _ => hfin i).subset ?_
    intro α hα
    simp only [Set.mem_setOf_eq, not_le] at hα
    exact Set.mem_biUnion (x := n α) hα rfl
  have hpow : Filter.Tendsto (fun α => b * ‖π‖ ^ n α) Filter.cofinite (nhds 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg π) hπ1).comp hn).const_mul b
  have ha0 : Filter.Tendsto a Filter.cofinite (nhds 0) := squeeze_zero_norm hb hpow
  have ha : Summable a := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ha0
  refine ⟨PowerSeries.mk fun i => ∑ α ∈ (hfin i).toFinset, a α / π ^ i, ?_, ?_, ?_⟩
  · intro i
    rw [PowerSeries.coeff_mk]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (le_max_right _ _) fun α hα => ?_
    have hpi : 0 < ‖π‖ ^ i := pow_pos (norm_pos_iff.2 hπ0) _
    rw [norm_div, norm_pow, div_le_iff₀ hpi]
    have := hb α
    rw [(hmem i α).1 hα] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpi.le)
  · rw [← ((ha.hasSum.tsum_fiberwise n).tsum_eq)]
    refine tsum_congr fun i => ?_
    rw [PowerSeries.coeff_mk, regroup_fib_tsum n i (hfin i), Finset.sum_mul]
    exact Finset.sum_congr rfl fun α _ => div_mul_cancel₀ _ (pow_ne_zero _ hπ0)
  · intro e u hsum
    have heπ : e π ≠ 0 := (map_ne_zero e).2 hπ0
    have hkey : ∀ i, e (PowerSeries.coeff i (PowerSeries.mk fun i => ∑ α ∈ (hfin i).toFinset, a α / π ^ i)) * u ^ i
        = ∑ α ∈ (hfin i).toFinset, e (a α) * (u / e π) ^ n α := by
      intro i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [PowerSeries.coeff_mk, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [(hmem i α).1 hα, map_div₀, map_pow, div_pow]
      field_simp
    simp_rw [hkey]
    have hf : Summable fun α => e (a α) * (u / e π) ^ n α := hsum.of_norm
    refine ⟨?_, ?_⟩
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => norm_sum_le _ _) ?_
      have := (hsum.hasSum.tsum_fiberwise n).summable
      exact this.congr fun i => regroup_fib_tsum n i (hfin i) (fun α => ‖e (a α) * (u / e π) ^ n α‖)
    · rw [← ((hf.hasSum.tsum_fiberwise n).tsum_eq)]
      exact tsum_congr fun i => (regroup_fib_tsum n i (hfin i) _).symm

end GlobalTheory.MBLow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesDeformationOfBoundedLatticeSeries
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem deform_of_lattice_series : ∀ (κ : Rule) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [CharZero C] (e : C →+* ℂ) (x : KeyIn C) (g : ℕ) (hg : x.P.g = g) (m : ℕ) (ζ : Cˣ)
    (lev : Out.Level x.P (m ^ 2) (unitOn ζ)) (k : C) (X : Type) (n : X → ℕ) (π : C) (B : ℝ)
    (a : (Fin (2 * g) → ZMod (m ^ 2)) → X → C) (b : (Fin (2 * g) → ZMod (m ^ 2)) → Fin g → X → C),
    π ≠ 0 → ‖π‖ < 1 → (∀ i, {α | n α = i}.Finite) → (∀ i α, ‖a i α‖ ≤ B * ‖π‖ ^ n α) →
    (∀ i j α, ‖b i j α‖ ≤ B * ‖π‖ ^ n α) →
    ThJet x hg m (levelPoint lev hg) (fun i => ∑' α, a i α) (fun i j => ∑' α, b i j α) →
    (∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      ((∀ i, Summable fun α => ‖e (a i α) * u ^ n α‖) ∧ ∀ i j, Summable fun α => ‖e (b i j α) * u ^ n α‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map e.toMonoidHom ζ))),
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) (fun i => ∑' α, e (a i α) * u ^ n α)
          (fun i j => ∑' α, e (b i j α) * u ^ n α) ∧ (κ ℂ x₀ : ℂ) = e k) →
    Deform κ e x hg m ζ lev k := by
  intro κ C _ _ _ _ e x g hg m ζ lev k X n π B a b hπ0 hπ1 hfin ha hb hJ hE
  have hA := fun i => lattice_series_regroup C X n π (a i) B hπ0 hπ1 hfin (ha i)
  have hB := fun i j => lattice_series_regroup C X n π (b i j) B hπ0 hπ1 hfin (hb i j)
  choose Θ hΘb hΘs hΘc using hA
  choose Γ hΓb hΓs hΓc using hB
  obtain ⟨ε, hε, hu⟩ := hE
  have heπ : e π ≠ 0 := (map_ne_zero e).2 hπ0
  have hnπ : 0 < ‖e π‖ := norm_pos_iff.2 heπ
  refine ⟨Θ, Γ, π, max B 0, hπ1, fun i l => ⟨hΘb i l, fun j => hΓb i j l⟩, ?_, ε * ‖e π‖, mul_pos hε hnπ, ?_⟩
  · have h1 : (fun i => ∑' l, PowerSeries.coeff l (Θ i) * π ^ l) = fun i => ∑' α, a i α := funext hΘs
    have h2 : (fun i j => ∑' l, PowerSeries.coeff l (Γ i j) * π ^ l) = fun i j => ∑' α, b i j α :=
      funext fun i => funext (hΓs i)
    rw [h1, h2]; exact hJ
  · intro u hu0 hul
    have hv0 : u / e π ≠ 0 := div_ne_zero hu0 heπ
    have hvl : ‖u / e π‖ < ε := by rw [norm_div, div_lt_iff₀ hnπ]; exact hul
    obtain ⟨⟨hsa, hsb⟩, x₀, hg₀, lev₀, hJ₀, hk⟩ := hu (u / e π) hv0 hvl
    refine ⟨fun i => ⟨(hΘc i e u (hsa i)).1, fun j => (hΓc i j e u (hsb i j)).1⟩, x₀, hg₀, lev₀, ?_, hk⟩
    have h1 : (fun i => ∑' l, e (PowerSeries.coeff l (Θ i)) * u ^ l) = fun i => ∑' α, e (a i α) * (u / e π) ^ n α :=
      funext fun i => (hΘc i e u (hsa i)).2
    have h2 : (fun i j => ∑' l, e (PowerSeries.coeff l (Γ i j)) * u ^ l) =
        fun i j => ∑' α, e (b i j α) * (u / e π) ^ n α :=
      funext fun i => funext fun j => (hΓc i j e u (hsb i j)).2
    rw [h1, h2]; exact hJ₀

end GlobalTheory.MBLow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesDeformationOfBoundedLatticeSeriesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesDeformation_of_boundedLatticeSeries : ∀ (κ : Rule) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [CharZero C] (e : C →+* ℂ) (x : KeyIn C) (g : ℕ) (hg : x.P.g = g) (m : ℕ) (ζ : Cˣ)
    (lev : Out.Level x.P (m ^ 2) (unitOn ζ)) (k : C) (X : Type) (n : X → ℕ) (π : C) (B : ℝ)
    (a : (Fin (2 * g) → ZMod (m ^ 2)) → X → C) (b : (Fin (2 * g) → ZMod (m ^ 2)) → Fin g → X → C),
    π ≠ 0 → ‖π‖ < 1 → (∀ i, {α | n α = i}.Finite) → (∀ i α, ‖a i α‖ ≤ B * ‖π‖ ^ n α) →
    (∀ i j α, ‖b i j α‖ ≤ B * ‖π‖ ^ n α) →
    ThJet x hg m (levelPoint lev hg) (fun i => ∑' α, a i α) (fun i j => ∑' α, b i j α) →
    (∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      ((∀ i, Summable fun α => ‖e (a i α) * u ^ n α‖) ∧ ∀ i j, Summable fun α => ‖e (b i j α) * u ^ n α‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map e.toMonoidHom ζ))),
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) (fun i => ∑' α, e (a i α) * u ^ n α)
          (fun i j => ∑' α, e (b i j α) * u ^ n α) ∧ (κ ℂ x₀ : ℂ) = e k) →
    Deform κ e x hg m ζ lev k := by
  first | exact @GlobalTheory.MBLow.deform_of_lattice_series | exact GlobalTheory.MBLow.deform_of_lattice_series | (intros; apply GlobalTheory.MBLow.deform_of_lattice_series <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharBlockPeriodMatrixFourierJacobiExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharBlockPeriodMatrixFourierJacobiExpansion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.FJ

theorem dot_split {g g' r : ℕ} (σ : Fin g ≃ Fin g' ⊕ Fin r) (u v : Fin g → ℂ) :
    u ⬝ᵥ v = zP σ u ⬝ᵥ zP σ v + tP σ u ⬝ᵥ tP σ v := by
  simp only [dotProduct, zP, tP]
  rw [← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]

theorem quad_full {g g' r : ℕ} (σ : Fin g ≃ Fin g' ⊕ Fin r) (A : Matrix (Fin g') (Fin g') ℂ)
    (B : Matrix (Fin g') (Fin r) ℂ) (D : Matrix (Fin r) (Fin r) ℂ) (v : Fin g → ℂ) :
    v ⬝ᵥ (Matrix.fromBlocks A B Bᵀ D).submatrix σ σ *ᵥ v =
      zP σ v ⬝ᵥ A *ᵥ zP σ v + 2 * (zP σ v ⬝ᵥ B *ᵥ tP σ v) + tP σ v ⬝ᵥ D *ᵥ tP σ v := by
  rw [dot_split σ]
  have h1 : zP σ ((Matrix.fromBlocks A B Bᵀ D).submatrix σ σ *ᵥ v) = A *ᵥ zP σ v + B *ᵥ tP σ v := by
    funext i
    simp only [zP, tP, mulVec, dotProduct, submatrix_apply, Pi.add_apply]
    rw [← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]
    simp
  have h2 : tP σ ((Matrix.fromBlocks A B Bᵀ D).submatrix σ σ *ᵥ v) = Bᵀ *ᵥ zP σ v + D *ᵥ tP σ v := by
    funext i
    simp only [zP, tP, mulVec, dotProduct, submatrix_apply, Pi.add_apply]
    rw [← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]
    simp
  rw [h1, h2, dotProduct_add, dotProduct_add, mulVec_transpose, dotProduct_comm (tP σ v) (vecMul _ _),
    ← dotProduct_mulVec]
  ring

def thT {k : ℕ} (τ : Matrix (Fin k) (Fin k) ℂ) (a b z : Fin k → ℂ) (n : Fin k → ℤ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ τ.mulVec ((fun i => (n i : ℂ)) + a)) +
    2 * Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ (z + b)))

theorem thetaChar_eq_tsum {k : ℕ} (τ : Matrix (Fin k) (Fin k) ℂ) (a b z : Fin k → ℂ) :
    thetaChar τ a b z = ∑' n, thT τ a b z n := rfl

theorem summable_thT {k : ℕ} {τ : Matrix (Fin k) (Fin k) ℂ} (hτ : (τ.map Complex.im).PosDef) {a : Fin k → ℂ}
    (ha : ∀ i, ((a i).re : ℂ) = a i) (b z : Fin k → ℂ) : Summable fun n => ‖thT τ a b z n‖ := by
  have hd : τ ∈ ReciprocityTheory.PTheta.ThetaDomain (Fin k) := hτ.add hτ.transpose
  refine (GlobalTheory.thetaSummable_holds (Fin k) (fun i => (a i).re) 0 (z + b) τ hd).congr fun n => ?_
  congr 1
  have hs : ReciprocityTheory.PTheta.shiftVec (fun i => (a i).re) n = (fun i => (n i : ℂ)) + a :=
    funext fun i => by simp [ReciprocityTheory.PTheta.shiftVec, ha i]
  have h0 : ReciprocityTheory.PTheta.ofRealVec (0 : Fin k → ℝ) = 0 := funext fun i => by simp [ReciprocityTheory.PTheta.ofRealVec]
  simp only [ReciprocityTheory.PTheta.thetaTerm, ReciprocityTheory.PTheta.eC, thT]
  rw [hs, h0, add_zero]
  congr 1
  ring

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

theorem thT_full (S : Matrix (Fin r) (Fin r) ℂ) (Z : Fin g → ℂ) (n : Fin g → ℤ) :
    thT (d.full σ S) (d.aF σ) (d.bF σ) Z n =
      Complex.exp (Real.pi * Complex.I * (cv (tP σ n) ⬝ᵥ (d.t22 + S) *ᵥ cv (tP σ n)) +
        2 * Real.pi * Complex.I * (cv (tP σ n) ⬝ᵥ (tP σ Z + d.b2))) *
      thT d.τ d.a d.b (zP σ Z + d.t12 *ᵥ cv (tP σ n)) (zP σ n) := by
  have hz : zP σ ((fun i => (n i : ℂ)) + d.aF σ) = (fun i => ((zP σ n i : ℤ) : ℂ)) + d.a := by
    funext i; simp [zP, CD.aF]
  have ht : tP σ ((fun i => (n i : ℂ)) + d.aF σ) = cv (tP σ n) := by
    funext i; simp [tP, CD.aF, cv]
  have hz' : zP σ (Z + d.bF σ) = zP σ Z + d.b := by
    funext i; simp [zP, CD.bF]
  have ht' : tP σ (Z + d.bF σ) = tP σ Z + d.b2 := by
    funext i; simp [tP, CD.bF]
  unfold thT CD.full
  rw [quad_full, dot_split σ _ (Z + d.bF σ), hz, ht, hz', ht', ← Complex.exp_add]
  congr 1
  simp only [dotProduct_add]
  ring

end GlobalTheory.MBLow.Cl.FJ


open GlobalTheory.MBLow.Cl.FJ in
theorem GlobalTheory.MBLow.Cl.fj_expansion : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ S : Matrix (Fin r) (Fin r) ℂ, S.IsSymm →
    ((d.full σ S).map Complex.im).PosDef → ∀ Z, (Summable fun χ => ‖d.fj σ S χ Z‖) ∧
      ∑' χ, d.fj σ S χ Z = thetaChar (d.full σ S) (d.aF σ) (d.bF σ) Z := by
  intro N g' r g bX d σ S _ hpos Z
  let e : (Fin g → ℤ) ≃ (Fin r → ℤ) × (Fin g' → ℤ) :=
    { toFun := fun n => (tP σ n, zP σ n)
      invFun := fun p j => Sum.elim p.2 p.1 (σ j)
      left_inv := fun n => by
        funext j
        rcases h : σ j with i | l
        · simp only [h, Sum.elim_inl, zP]; rw [σ.symm_apply_eq.mpr h.symm]
        · simp only [h, Sum.elim_inr, tP]; rw [σ.symm_apply_eq.mpr h.symm]
      right_inv := fun p => by ext <;> simp [zP, tP] }
  have haF : ∀ j, ((d.aF σ j).re : ℂ) = d.aF σ j := by
    intro j
    simp only [CD.aF]
    rcases σ j with i | l
    · rcases d.ha i with h | h <;> simp [h]
    · simp
  let F : (Fin r → ℤ) × (Fin g' → ℤ) → ℂ := fun p => thT (d.full σ S) (d.aF σ) (d.bF σ) Z (e.symm p)
  have hF : Summable fun p => ‖F p‖ :=
    (e.symm.summable_iff (f := fun n => ‖thT (d.full σ S) (d.aF σ) (d.bF σ) Z n‖)).mpr
      (summable_thT hpos haF (d.bF σ) Z)
  have hFc : Summable F := hF.of_norm
  have hkey : ∀ χ, d.fj σ S χ Z = ∑' m, F (bX.equivFun χ, m) := by
    intro χ
    have hcv : cv (bX.equivFun χ) = co bX χ := by
      funext l; simp [cv, co, Module.Basis.equivFun_apply]
    have hsymm : ∀ p, e (e.symm p) = p := e.apply_symm_apply
    simp only [CD.fj, thetaChar_eq_tsum, ← tsum_mul_left, F]
    congr 1
    funext m
    have h1 : tP σ (e.symm (bX.equivFun χ, m)) = bX.equivFun χ := congrArg Prod.fst (hsymm (bX.equivFun χ, m))
    have h2 : zP σ (e.symm (bX.equivFun χ, m)) = m := congrArg Prod.snd (hsymm (bX.equivFun χ, m))
    rw [thT_full, h1, h2, hcv]
  refine ⟨?_, ?_⟩
  · refine ((hF.prod).comp_injective bX.equivFun.injective).of_nonneg_of_le (fun _ => norm_nonneg _) fun χ => ?_
    rw [hkey χ]
    exact norm_tsum_le_tsum_norm (hF.prod_factor _)
  · have hre := bX.equivFun.toEquiv.tsum_eq (fun k => ∑' m, F (k, m))
    simp only [LinearEquiv.coe_toEquiv] at hre
    rw [tsum_congr hkey, hre, ← hFc.tsum_prod, thetaChar_eq_tsum, ← e.symm.tsum_eq]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharBlockPeriodMatrixFourierJacobiExpansionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChar_blockPeriodMatrix_fourierJacobiExpansion : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ S : Matrix (Fin r) (Fin r) ℂ, S.IsSymm → ((d.full σ S).map Complex.im).PosDef → ∀ Z, (Summable fun χ => ‖d.fj σ S χ Z‖) ∧ ∑' χ, d.fj σ S χ Z = thetaChar (d.full σ S) (d.aF σ) (d.bF σ) Z := by
  first | exact @GlobalTheory.MBLow.Cl.fj_expansion | exact GlobalTheory.MBLow.Cl.fj_expansion | (intros; apply GlobalTheory.MBLow.Cl.fj_expansion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSeparatingClosedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSeparatingClosedPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
open GlobalTheory.Twist GlobalTheory.SerreCriterion

set_option autoImplicit false
noncomputable section
namespace GlobalTheory
namespace IsolatedSecZero
variable {X : Scheme.{0}}

theorem exists_germ_eq_zero_of_isolated {F : X.Modules} {y : X} (hy : IsClosed ({y} : Set X))
    {U : X.Opens} (hyU : y ∈ U) (hF : ∀ z ∈ U, z ∈ support F → z = y)
    (t : (F.presheaf.stalk y :)) : ∃ s : Γ(F, ⊤), F.presheaf.germ ⊤ y trivial s = t ∧
      ∀ z, z ≠ y → F.presheaf.germ ⊤ z trivial s = 0 := by
  obtain ⟨V, hyV, s, rfl⟩ := F.presheaf.exists_germ_eq t
  let W : X.Opens := ⟨{y}ᶜ, hy.isOpen_compl⟩
  let C : Bool → X.Opens := fun b => if b then V ⊓ U else W
  have hzero : ∀ (O : X.Opens), O ≤ V ⊓ U ⊓ W → ∀ r : Γ(F, O), r = 0 := fun O hO r => by
    refine TopCat.Presheaf.section_ext (abSheaf F) O r 0 fun z hz => ?_
    have hz' := hO hz
    have hns : z ∉ support F := fun h => hz'.2 (hF z hz'.1.2 h)
    exact (notMem_support_iff.1 hns).elim _ _
  obtain ⟨g, hg⟩ := exists_sec_of_cover (F := F) C (fun _ => le_top)
    (fun z _ => by
      by_cases h : z = y
      · subst h; exact Opens.mem_iSup.2 ⟨true, ⟨hyV, hyU⟩⟩
      · exact Opens.mem_iSup.2 ⟨false, h⟩)
    (fun b => match b with
      | true => resM F (inf_le_left : V ⊓ U ≤ V) s
      | false => 0)
    (fun k l => by
      cases k <;> cases l
      · rfl
      · exact (hzero _ (le_inf inf_le_right inf_le_left) _).trans (hzero _ (le_inf inf_le_right inf_le_left) _).symm
      · exact (hzero _ (le_inf inf_le_left inf_le_right) _).trans (hzero _ (le_inf inf_le_left inf_le_right) _).symm
      · rfl)
  refine ⟨g, ?_, fun z hz => ?_⟩
  · have hyVU : y ∈ V ⊓ U := ⟨hyV, hyU⟩
    have := congrArg (F.presheaf.germ (V ⊓ U) y hyVU) (hg true)
    dsimp only at this
    rw [germ_resM, germ_resM] at this
    exact this
  · have hzW : z ∈ W := hz
    have := congrArg (F.presheaf.germ W z hzW) (hg false)
    dsimp only at this
    rw [germ_resM, map_zero] at this
    exact this
end IsolatedSecZero

theorem exists_sec_mem_nonzeroLocus_of_isolated_zero_else : ∀ (k : Type) [Field k] (X : Scheme.{0})
    [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → ∀ (L : LB X), L.IsLB →
    ∀ (J : X.IdealSheafData) (x : X) (U : X.Opens), IsClosed ({x} : Set X) → x ∈ U →
    (∀ y ∈ U, y ∈ J.support ↔ y = x) → Subsingleton (coh (twist (idealModule J) L) 1) →
    ∃ s : L.Sec, x ∈ nonzeroLocus s ∧ ∀ y ∈ J.support, y ≠ x → y ∉ nonzeroLocus s := by
  intro k _ X _ q _ N hN J x U hxc hxU hJ h
  set φ := toSubscheme J with hφ
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (kernel.ι φ) (cokernel.π (kernel.ι φ)) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hS' : (S.map (twistFunctor N)).ShortExact := Twist.shortExact_map hN hS
  have hsurj := cohOn.app_surjective hS' ⊤ h
  have hQ : ∀ z ∈ U, z ∈ support (twist S.X₃ N) → z = x := by
    intro z hzU hz
    rw [support_twist hN] at hz
    have := mem_support_iff.1 hz
    refine (hJ z hzU).1 (support_pushforward_subscheme_subset J ?_)
    exact mem_support_iff.2 (stalkLinear_injective (Abelian.factorThruCoimage φ) z).nontrivial
  have hx : x ∈ J.support := (hJ x hxU).2 rfl
  obtain ⟨c, hc⟩ := exists_chart hN x
  let one : Γ(QCoh.structureModule X, ⊤) := (structureModuleSectionsEquiv ⊤).symm 1
  obtain ⟨b, hb, hb0⟩ := IsolatedSecZero.exists_germ_eq_zero_of_isolated hxc hxU hQ
    ((stalkEquiv S.X₃ hN c hc).symm
      (stalkLinear S.g x ((QCoh.structureModule X).presheaf.germ ⊤ x trivial one)))
  obtain ⟨a, rfl⟩ := hsurj b
  refine ⟨secOfTwist (𝟙 _) a, ?_, ?_⟩
  · have hm : x ∈ ⊤ ⊓ N.U c := ⟨trivial, hc⟩
    replace hb := (stalkEquiv_germ hN c hc (V := ⊤) trivial _).symm.trans
      ((LinearEquiv.eq_symm_apply _).1 hb)
    have h₁ : stalkLinear S.g x ((QCoh.structureModule X).presheaf.germ _ x hm
        (coord (F := QCoh.structureModule X) a c)) =
        stalkLinear S.g x ((QCoh.structureModule X).presheaf.germ ⊤ x trivial one) :=
      (stalkLinear_germ S.g x hm _).trans hb
    have h₂ : stalkLinear φ x ((QCoh.structureModule X).presheaf.germ ⊤ x trivial one -
        (QCoh.structureModule X).presheaf.germ _ x hm (coord (F := QCoh.structureModule X) a c)) = 0 := by
      rw [← Abelian.coimage.fac φ, stalkLinear_comp, LinearMap.comp_apply, map_sub]
      exact (congrArg _ (sub_eq_zero.2 h₁.symm)).trans (map_zero _)
    have h₃ := not_isUnit_of_toSubscheme_eq_zero J hx _ h₂
    rw [map_sub] at h₃
    erw [structureModuleStalkEquiv_germ, structureModuleStalkEquiv_germ] at h₃
    have h1 : structureModuleSectionsEquiv ⊤ one = 1 := by simp [one]
    rw [h1, map_one] at h₃
    have hu := (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_right h₃
    refine basicOpen_le_nonzeroLocus _ c ((X.mem_basicOpen _ x hc).2 ?_)
    erw [secOfTwist_f]
    exact (congrArg IsUnit (X.presheaf.germ_res_apply (homOfLE _) x hc _)).mpr hu
  · intro y hy hyx hmem
    obtain ⟨d, hd⟩ := Opens.mem_iSup.1 hmem
    have hyd : y ∈ N.U d := X.basicOpen_le _ hd
    have hm : y ∈ ⊤ ⊓ N.U d := ⟨trivial, hyd⟩
    have e0 := hb0 y hyx
    have h₁ : stalkLinear S.g y ((QCoh.structureModule X).presheaf.germ _ y hm
        (coord (F := QCoh.structureModule X) a d)) = 0 := by
      have := (stalkEquiv_germ hN d hyd (V := ⊤) trivial _).symm.trans
        (congrArg (stalkEquiv S.X₃ hN d hyd) e0)
      rw [map_zero] at this
      exact (stalkLinear_germ S.g y hm _).trans this
    have h₂ : stalkLinear φ y ((QCoh.structureModule X).presheaf.germ _ y hm
        (coord (F := QCoh.structureModule X) a d)) = 0 := by
      rw [← Abelian.coimage.fac φ, stalkLinear_comp, LinearMap.comp_apply]
      exact (congrArg _ h₁).trans (map_zero _)
    have h₃ := not_isUnit_of_toSubscheme_eq_zero J hy _ h₂
    rw [structureModuleStalkEquiv_germ] at h₃
    apply h₃
    erw [secOfTwist_f] at hd
    exact (congrArg IsUnit (X.presheaf.germ_res_apply (homOfLE _) y hyd _)).mp
      ((X.mem_basicOpen _ y hyd).1 hd)
end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSeparatingClosedPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_separating_closed_point : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → ∀ (L : LB X), L.IsLB → ∀ (J : X.IdealSheafData) (x : X) (U : X.Opens), IsClosed ({x} : Set X) → x ∈ U → (∀ y ∈ U, y ∈ J.support ↔ y = x) → Subsingleton (coh (twist (idealModule J) L) 1) → ∃ s : L.Sec, x ∈ nonzeroLocus s ∧ ∀ y ∈ J.support, y ≠ x → y ∉ nonzeroLocus s := by
  first | exact @GlobalTheory.exists_sec_mem_nonzeroLocus_of_isolated_zero_else | exact GlobalTheory.exists_sec_mem_nonzeroLocus_of_isolated_zero_else | (intros; apply GlobalTheory.exists_sec_mem_nonzeroLocus_of_isolated_zero_else <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFormParameterOfDiscreteNorms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFormParameterOfDiscreteNorms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem exists_form_of_discrete_norms : ∀ (C : Type) [NormedField C] [IsAlgClosed C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ) (t : C), N.Int q → t ≠ 0 → ‖t‖ < 1 → (∀ χ, ∃ n : ℤ, ‖(N.ψ χ : C)‖ = ‖t‖ ^ n) → ∀ m : ℕ, 1 ≤ m → ∃ (β : N.Form (m ^ 2)) (π : C), π ≠ 0 ∧ ‖π‖ < 1 ∧ (∀ n : ℕ, {α | (β.be α α / (2 * m ^ 2)).toNat = n}.Finite) ∧ ∀ α, Real.exp (-(q α / (m : ℝ) ^ 2)) = ‖π‖ ^ (β.be α α / (2 * m ^ 2)).toNat := by
  intro C _ _ N q t hI ht0 ht1 hψ m hm
  have htpos : 0 < ‖t‖ := norm_pos_iff.2 ht0
  set L : ℝ := -Real.log ‖t‖ with hL
  have hLpos : 0 < L := by
    have := Real.log_neg htpos ht1
    linarith
  clear_value L
  choose Q hQ using hψ
  have hq : ∀ χ, q χ = (Q χ : ℝ) * L := by
    intro χ
    have h1 := hI.ψ χ
    rw [hQ χ] at h1
    have h2 : Real.log (‖t‖ ^ Q χ) = -q χ := by rw [h1, Real.log_exp]
    rw [Real.log_zpow] at h2
    rw [hL]; linarith
  set Bf : N.X → N.X → ℤ := fun x y => Q (x + y) - Q x - Q y with hBf
  have hB : ∀ x y, (Bf x y : ℝ) = QuadraticMap.polar q x y / L := by
    intro x y
    rw [eq_div_iff hLpos.ne']
    simp only [hBf, QuadraticMap.polar, hq]
    push_cast; ring
  have inj : ∀ a b : ℤ, (a : ℝ) = b → a = b := fun a b h => Int.cast_inj.1 h
  let Bm : LinearMap.BilinForm ℤ N.X := LinearMap.mk₂ ℤ Bf
    (fun x x' y => inj _ _ (by rw [Int.cast_add, hB, hB, hB, QuadraticMap.polar_add_left, add_div]))
    (fun c x y => inj _ _ (by rw [smul_eq_mul, Int.cast_mul, hB, hB, QuadraticMap.polar_smul_left, zsmul_eq_mul, mul_div_assoc]))
    (fun x y y' => inj _ _ (by rw [Int.cast_add, hB, hB, hB, QuadraticMap.polar_add_right, add_div]))
    (fun c x y => inj _ _ (by rw [smul_eq_mul, Int.cast_mul, hB, hB, QuadraticMap.polar_smul_right, zsmul_eq_mul, mul_div_assoc]))
  have hBm : ∀ x y, Bm x y = Bf x y := fun x y => rfl
  have hdiag : ∀ x, Bf x x = 2 * Q x := by
    intro x
    apply inj
    rw [hB, QuadraticMap.polar_self, hq, nsmul_eq_mul]
    push_cast
    field_simp
    try ring
  have hsymm : ∀ x y, Bf x y = Bf y x := by
    intro x y; simp only [hBf, add_comm x y]; ring
  have hpos : ∀ y, y ≠ 0 → 0 < q y := by
    intro y hy
    by_contra hn
    push_neg at hn
    have hfin : {α | ¬ (0 < q α)}.Finite :=
      Filter.eventually_cofinite.1 (hI.pos.eventually (Filter.eventually_gt_atTop 0))
    have hinf : (Set.range fun c : ℤ => c • y).Infinite :=
      Set.infinite_range_of_injective (smul_left_injective ℤ hy)
    refine hinf (hfin.subset ?_)
    rintro _ ⟨c, rfl⟩
    simp only [Set.mem_setOf_eq, not_lt]
    rw [QuadraticMap.map_smul, zsmul_eq_mul]
    push_cast
    nlinarith [mul_self_nonneg (c : ℝ)]
  have hQnn : ∀ y, 0 ≤ Q y := by
    intro y
    by_cases hy : y = 0
    · subst hy
      have : (Q 0 : ℝ) * L = 0 := by rw [← hq, QuadraticMap.map_zero]
      have : (Q 0 : ℝ) = 0 := by
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · exact absurd h hLpos.ne'
      exact_mod_cast this.ge
    · have := hpos y hy
      rw [hq] at this
      have : (0 : ℝ) < Q y := pos_of_mul_pos_left this hLpos.le
      exact_mod_cast this.le
  have hQpos : ∀ y, y ≠ 0 → 0 < Q y := by
    intro y hy
    have := hpos y hy
    rw [hq] at this
    have : (0 : ℝ) < Q y := pos_of_mul_pos_left this hLpos.le
    exact_mod_cast this
  have hm0 : (2 * (m : ℤ) ^ 2) ≠ 0 := by positivity
  let β : N.Form (m ^ 2) :=
    { be := (2 * (m : ℤ) ^ 2) • Bm
      symm := fun y z => by
        simp only [LinearMap.smul_apply, hBm, hsymm y z]
      pos := fun y hy => by
        simp only [LinearMap.smul_apply, hBm, hdiag, smul_eq_mul]
        have := hQpos y hy
        positivity
      dvd := fun y z => ⟨Bf y z, by simp [LinearMap.smul_apply, hBm, smul_eq_mul]⟩ }
  have hβ : ∀ α, β.be α α / (2 * m ^ 2) = 2 * Q α := by
    intro α
    show ((2 * (m : ℤ) ^ 2) • Bm) α α / (2 * m ^ 2) = 2 * Q α
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, hBm, hdiag, Int.mul_ediv_cancel_left _ hm0]
  have hn : 0 < 2 * m ^ 2 := by positivity
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq t hn
  have hπ0 : π ≠ 0 := by rintro rfl; exact ht0 (by rw [← hπ, zero_pow hn.ne'])
  have hπn : ‖π‖ ^ (2 * m ^ 2) = ‖t‖ := by rw [← norm_pow, hπ]
  have hπpos : 0 < ‖π‖ := norm_pos_iff.2 hπ0
  have hπ1 : ‖π‖ < 1 := by
    by_contra h
    push_neg at h
    have := one_le_pow₀ (n := 2 * m ^ 2) h
    rw [hπn] at this
    linarith
  have hlp : Real.log ‖π‖ * (2 * (m : ℝ) ^ 2) = -L := by
    rw [hL, ← hπn, Real.log_pow]; push_cast; ring
  refine ⟨β, π, hπ0, hπ1, fun n => ?_, fun α => ?_⟩
  · have hfin : {α | ¬ ((n : ℝ) * L < q α)}.Finite :=
      Filter.eventually_cofinite.1 (hI.pos.eventually (Filter.eventually_gt_atTop _))
    refine hfin.subset fun α hα => ?_
    simp only [Set.mem_setOf_eq, hβ] at hα ⊢
    rw [not_lt, hq]
    have h1 : (2 * Q α) = (n : ℤ) := by
      rw [← hα, Int.toNat_of_nonneg (by linarith [hQnn α])]
    have h2 : (Q α : ℝ) ≤ n := by
      have : Q α ≤ (n : ℤ) := by linarith [hQnn α]
      exact_mod_cast this
    nlinarith
  · have hc : ((2 * Q α).toNat : ℝ) = 2 * (Q α : ℝ) := by
      have := Int.toNat_of_nonneg (show 0 ≤ 2 * Q α by linarith [hQnn α])
      exact_mod_cast this
    rw [hβ, ← Real.exp_log hπpos, ← Real.exp_nat_mul, hc, hq]
    congr 1
    have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by
      have : (0 : ℝ) < m := by exact_mod_cast hm
      positivity
    have e : Real.log ‖π‖ = -L / (2 * (m : ℝ) ^ 2) := by
      rw [eq_div_iff (by positivity)]; exact hlp
    rw [e]
    field_simp

end GlobalTheory.MBLow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFormParameterOfDiscreteNormsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralForm_parameter_of_discreteNorms : ∀ (C : Type) [NormedField C] [IsAlgClosed C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ) (t : C), N.Int q → t ≠ 0 → ‖t‖ < 1 → (∀ χ, ∃ n : ℤ, ‖(N.ψ χ : C)‖ = ‖t‖ ^ n) → ∀ m : ℕ, 1 ≤ m → ∃ (β : N.Form (m ^ 2)) (π : C), π ≠ 0 ∧ ‖π‖ < 1 ∧ (∀ n : ℕ, {α | (β.be α α / (2 * m ^ 2)).toNat = n}.Finite) ∧ ∀ α, Real.exp (-(q α / (m : ℝ) ^ 2)) = ‖π‖ ^ (β.be α α / (2 * m ^ 2)).toNat := by
  first | exact @GlobalTheory.MBLow.exists_form_of_discrete_norms | exact GlobalTheory.MBLow.exists_form_of_discrete_norms | (intros; apply GlobalTheory.MBLow.exists_form_of_discrete_norms <;> assumption)
end
end

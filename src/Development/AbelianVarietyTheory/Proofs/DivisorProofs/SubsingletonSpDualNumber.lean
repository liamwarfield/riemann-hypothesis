module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleWeightGap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumAbelianLocusPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonSpDualNumber
set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InteriorKS

theorem subsingleton_sp_dualNumber (K : Type) [Field K] : Subsingleton (Sp (DualNumber K)) := by
  have h : ∀ p : PrimeSpectrum (DualNumber K),
      p.asIdeal = IsLocalRing.maximalIdeal (DualNumber K) := by
    intro p
    refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun x hx => ?_
    have hn : IsNilpotent x := by
      rw [TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst]
      have : ¬ IsUnit x.fst := fun hu => hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hu)
      have h0 : x.fst = 0 := by simpa using this
      rw [h0]; exact IsNilpotent.zero
    obtain ⟨n, hn⟩ := hn
    exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext ((h p).trans (h q).symm)⟩

theorem rigidity_dualNumber {K : Type} [Field K] (A₀ : Over (Sp K)) (A' G' : Over (Sp (DualNumber K))) [GrpObj A']
    [GrpObj G'] (j : A₀.left ⟶ A'.left) (a b : A' ⟶ G') (hA : IsAbelianScheme A')
    (hj : IsPullback j A₀.hom A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (hab : j ≫ a.left = j ≫ b.left) (hη : η[A'] ≫ a = η[A'] ≫ b) : a = b := by
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  haveI := subsingleton_sp_dualNumber K
  let c : A' ⟶ G' := a * b⁻¹
  let j' : Over.mk (j ≫ A'.hom) ⟶ A' := Over.homMk j rfl
  have h1 : j' ≫ a = j' ≫ b := Over.OverMorphism.ext hab
  have h2 : j' ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]
  have h3 : η[A'] ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]
  obtain ⟨t₀⟩ : Nonempty (Sp K) := inferInstance
  let t : Sp (DualNumber K) := spMap (TrivSqZeroExt.fstHom K K K).toRingHom t₀
  have hc : ∀ x : A'.left, c.left x = (η[G'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ G').left t := by
    intro x
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hj x t₀ (Subsingleton.elim _ _)
    have e : j ≫ c.left = (j' ≫ c).left := rfl
    rw [← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    congr 1
    exact Subsingleton.elim (α := Sp (DualNumber K)) _ _
  have hη' : (η[A'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ A').left ≫ A'.hom = 𝟙 _ := Over.w η[A']
  have key := GlobalTheory.DualRigidity.eq_comp_section_of_const A'.hom _ c.left hη' (hL.globalFns _ A' hA).2 _ hc
  have key' : c = toUnit A' ≫ η[A'] ≫ c := Over.OverMorphism.ext key
  rw [h3, MonObj.comp_one] at key'
  exact mul_inv_eq_one.1 key'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {K : Type} [Field K] {x₀ : Sp K ⟶ Xo.X} {x' : Sp (DualNumber K) ⟶ Xo.X}
  {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {π : A.left ⟶ Xo.univ.t.G.left}
  {π' : A'.left ⟶ Xo.univ.t.G.left} {i : A.left ⟶ A'.left} {q : A'.left ⟶ A.left}

theorem act_const (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (hπ : IsGrpPullback A Xo.univ.t.G x₀ π)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiπ : i ≫ π' = π) (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q)
    (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left)
    (hg : g ≫ π' = m.cm.F) (hgw : g ≫ A'.hom = o.t.G.hom) (a : 𝓞 E) :
    (o.t.act.act a).left ≫ (g ≫ q ≫ π) = (g ≫ q ≫ π) ≫ (Xo.univ.t.act.act a).left := by
  haveI := Xo.univ.t.act.hom a
  have wβ : (π ≫ (Xo.univ.t.act.act a).left) ≫ Xo.univ.t.G.hom = A.hom ≫ x₀ := by
    rw [Category.assoc, Over.w (Xo.univ.t.act.act a), hπ.1.w]
  let β : A ⟶ A := Over.homMk (hπ.1.lift _ A.hom wβ) (hπ.1.lift_snd _ _ _)
  have hβ : β.left ≫ π = π ≫ (Xo.univ.t.act.act a).left := hπ.1.lift_fst _ _ _
  haveI : IsMonHom β := GlobalTheory.UU.isMonHom_of_over_isMonHom hπ hπ (Xo.univ.t.act.act a) β hβ
  have wα : (π' ≫ (Xo.univ.t.act.act a).left) ≫ Xo.univ.t.G.hom = A'.hom ≫ x' := by
    rw [Category.assoc, Over.w (Xo.univ.t.act.act a), hπ'.1.w]
  let α : A' ⟶ A' := Over.homMk (hπ'.1.lift _ A'.hom wα) (hπ'.1.lift_snd _ _ _)
  have hα : α.left ≫ π' = π' ≫ (Xo.univ.t.act.act a).left := hπ'.1.lift_fst _ _ _
  haveI : IsMonHom α := GlobalTheory.UU.isMonHom_of_over_isMonHom hπ' hπ' (Xo.univ.t.act.act a) α hα
  have wδ : (q ≫ β.left) ≫ A.hom = A'.hom ≫ spMap (algebraMap K (DualNumber K)) := by
    rw [Category.assoc, Over.w β, hq.1.w]
  let δ : A' ⟶ A' := Over.homMk (hq.1.lift _ A'.hom wδ) (hq.1.lift_snd _ _ _)
  have hδ : δ.left ≫ q = q ≫ β.left := hq.1.lift_fst _ _ _
  haveI : IsMonHom δ := GlobalTheory.UU.isMonHom_of_over_isMonHom hq hq β δ hδ
  have hA' : IsAbelianScheme A' := by
    have hG := ObjDim.isAbelianScheme Xo.univ
    have := hG.comm
    have hc : IsCommMonObj A' := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hπ'.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hπ'.2 T x y (pushPt hπ'.1.w x) (pushPt hπ'.1.w y) rfl rfl,
        ← hπ'.2 T y x (pushPt hπ'.1.w y) (pushPt hπ'.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) hπ'.1 hG.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hπ'.1 hG.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hπ'.1 hG.geomConnected⟩
  have e1 : i ≫ α.left = β.left ≫ i := by
    apply hπ'.1.hom_ext
    · simp only [Category.assoc]
      rw [hα, reassoc_of% hiπ, hiπ, hβ]
    · simp only [Category.assoc]
      rw [Over.w α, hi.1.w, reassoc_of% (Over.w β)]
  have e2 : i ≫ δ.left = β.left ≫ i := by
    apply hq.1.hom_ext
    · simp only [Category.assoc]
      rw [hδ, reassoc_of% hiq, hiq, Category.comp_id]
    · simp only [Category.assoc]
      rw [Over.w δ, hi.1.w, reassoc_of% (Over.w β)]
  have hαδ : α = δ := rigidity_dualNumber A A' A' i α δ hA' hi.1 (e1.trans e2.symm)
    (by rw [IsMonHom.one_hom, IsMonHom.one_hom])
  have hga : (o.t.act.act a).left ≫ g = g ≫ α.left := by
    apply hπ'.1.hom_ext
    · simp only [Category.assoc]
      rw [hα, hg, reassoc_of% hg]
      exact m.act a
    · simp only [Category.assoc]
      rw [hgw, Over.w α, hgw, Over.w (o.t.act.act a)]
  calc (o.t.act.act a).left ≫ (g ≫ q ≫ π) = g ≫ α.left ≫ q ≫ π := by rw [reassoc_of% hga]
    _ = g ≫ q ≫ π ≫ (Xo.univ.t.act.act a).left := by rw [hαδ, reassoc_of% hδ, hβ]
    _ = (g ≫ q ≫ π) ≫ (Xo.univ.t.act.act a).left := by simp only [Category.assoc]

theorem cub_const (c : Coeff l) [Algebra c.F K] (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i)
    (hπ : IsGrpPullback A Xo.univ.t.G x₀ π)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiπ : i ≫ π' = π) (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q)
    (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left)
    (hg1 : g ≫ π' = m.cm.F) (hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π)) :
    (cubeMapOf hF).IsPullCubical o.t.cub Xo.univ.t.cub := by
  haveI : IsProper o.t.G.hom := o.proper
  have hA : IsAbelianScheme o.t.G := AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi
  refine GlobalTheory.TripleModel.isPullCubical_of_lbIso GlobalTheory.SemiRigid.globalFns hA hF o.t.cub Xo.univ.t.cub ?_
  obtain ⟨w, -, hw, -⟩ := rigIso_congr rfl m.cm m.lin rfl rfl
  have K2 : LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π)) :=
    GlobalTheory.TangentConstLB.lbIso_tangent_const E H Dw l Xo c K x₀ x' A A' π π' i q hi hπ hπ' hiπ hiq hq
  have hM := Xo.univ.t.PP.isLB
  have h1 : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull (g ≫ π')) := hg1 ▸ ⟨w, hw⟩
  have h2 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ q ≫ π)) :=
    GlobalTheory.Ex.GenericFibre.lbIso_pull K2 g rfl
  have h3 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ π')) :=
    GlobalTheory.FamRep.lbIso_pull_pull hM π' g
  exact LBIso.trans o.t.PP.isLB (pull_isLB hM _) (pull_isLB hM _) h1
    (LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) h3.symm h2)

theorem objMap_const (c : Coeff l) [Algebra c.F K] (hx : GlobalTheory.DeRham.epsRed K ≫ x' = x₀)
    (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (hπ : IsGrpPullback A Xo.univ.t.G x₀ π)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiπ : i ≫ π' = π) (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q)
    (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') : Nonempty (ObjMap o Xo.univ (constPt x')) := by
  have hw : m.cm.F ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ x' := m.cart.1.w
  let g : o.t.G.left ⟶ A'.left := hπ'.1.lift m.cm.F o.t.G.hom hw
  have hg : g ≫ π' = m.cm.F := hπ'.1.lift_fst _ _ _
  have hgw : g ≫ A'.hom = o.t.G.hom := hπ'.1.lift_snd _ _ _
  have hgc : IsGrpPullback o.t.G A' (𝟙 _) g :=
    hπ'.cancel (m.cart.congr (Category.id_comp _).symm hg.symm) (by rw [hgw, Category.comp_id])
  have hred : spMap (algebraMap K (DualNumber K)) ≫ x₀ = constPt x' := by
    rw [← hx]; rfl
  have hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π) :=
    (hgc.comp (hq.comp hπ)).congr (by rw [Category.id_comp, hred]) rfl
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap c.F K).injective).1 inferInstance
  have hgq := hgc.comp hq
  have hcomm : ∀ (T : Over (Sp K)) (x y : T ⟶ A), x * y = y * x := by
    intro T x y
    apply Over.OverMorphism.ext
    apply hπ.1.hom_ext
    · have e1 := hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl
      have e2 := hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl
      rw [← e1, ← e2, _root_.mul_comm]
    · rw [Over.w (x * y), Over.w (y * x)]
  have key : ∀ (σ : 𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G) (τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (n : ℕ),
      0 < n → σ ^ n = 1 → σ.left ≫ m.cm.F = x' ≫ τ.left →
      σ.left ≫ (g ≫ q ≫ π) = constPt x' ≫ τ.left := by
    intro σ τ n hn hσ hστ
    let u := pushHom hgq (𝟙_ (Over (Sp (DualNumber K)))) σ
    have hu : u ^ n = 1 := by rw [← map_pow, hσ, map_one]
    have e := GlobalTheory.TorsConst.torsion_eq_const K A _ (by simp) (hcomm _) u n hn hu
    have hul : u.left = σ.left ≫ g ≫ q := by
      show σ.left ≫ (g ≫ q) = _; rfl
    rw [hul] at e
    let w := spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ g
    have hw' : w ≫ A'.hom = 𝟙 _ ≫ GlobalTheory.DeRham.epsRed K := by
      simp only [w, Category.assoc, hgw, Category.id_comp]
      rw [Over.w σ]; rfl
    let s₀ := hi.1.lift w (𝟙 _) hw'
    have hs₀ : s₀ ≫ i = w := hi.1.lift_fst _ _ _
    calc σ.left ≫ (g ≫ q ≫ π) = (σ.left ≫ g ≫ q) ≫ π := by simp only [Category.assoc]
      _ = (spMap (algebraMap K (DualNumber K)) ≫ w ≫ q) ≫ π := by rw [e]; simp only [w, Category.assoc]
      _ = spMap (algebraMap K (DualNumber K)) ≫ s₀ ≫ i ≫ π' := by
          rw [← hs₀]; simp only [Category.assoc]; rw [reassoc_of% hiq, hiπ]
      _ = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ m.cm.F := by
          rw [reassoc_of% hs₀]; simp only [w, Category.assoc, hg]
      _ = constPt x' ≫ τ.left := by rw [hστ]; rfl
  have hpow : ∀ (f : Dw.La → (𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G)), (∀ a b, f (a + b) = f a * f b) →
      ∀ (n : ℕ) a, f (n • a) = f a ^ n := by
    intro f hf n a
    induction n with
    | zero =>
      have h0 := hf 0 0
      rw [add_zero] at h0
      rw [zero_smul, pow_zero]
      exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)
    | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h1
  exact ⟨{
    cm := cubeMapOf hF
    cart := hF
    base := rfl
    act := act_const hi hπ hπ' hiπ hiq hq o m g hg hgw
    lin := cub_const c hi hπ hπ' hiπ hiq hq o m g hg hF
    eta := fun a => key (o.eta a) (Xo.univ.eta a) l.M (by have := l.three_le; omega)
      (by rw [← hpow _ o.eta_add]; exact o.eta_ker _ (by
        rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact Submodule.smul_mem_smul hM Submodule.mem_top))
      (m.eta a)
    etaA := fun a => key (o.etaA a) (Xo.univ.etaA a) l.A l.A_pos
      (by rw [← hpow _ o.etaA_add]; exact o.etaA_ker a) (m.etaA a) }⟩

theorem eq_constPt (c : Coeff l) [Algebra c.F K] (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q) : x' = constPt x' := by
  obtain ⟨o, ⟨m⟩⟩ := GlobalTheory.obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (x' ≫ Xo.s) x' rfl rfl
    (by rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ
  exact Xo.unram K x' o ⟨m⟩ (objMap_const c rfl hi (hi.comp hπ') hπ' rfl hiq hq o m)

end GlobalTheory.InteriorKS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIdealIntegralFiniteAdelesOfMemCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIdealIntegralFiniteAdelesOfMemCompletion
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

namespace GlobalTheory.CosetOrth

theorem mem_hatId_of_inHat : ∀ {D : D7} (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ x : Formalism.MainNotions.StandardLatticesGL3.AE D,
  InHat (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (GlobalTheory.BotFormula.toFinE D x) → x ∈ hatId D 𝔪 := by
  intro D 𝔪 h𝔪 x hx
  have hI : (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔪
  have hN : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔪)
  obtain ⟨a, s, hs, e⟩ := GlobalTheory.Mem.Col2.SplitChar.exists_approx x hN
  have hNm : ((Ideal.absNorm 𝔪 : ℕ) : D.host.E) ∈ (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.absNorm_mem 𝔪, map_natCast _ _⟩
  have ha : a ∈ (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    refine (GlobalTheory.NumeratorIdeal.mem_iff_valuation D.host.E hI a).2 fun w => ?_
    rw [← GlobalTheory.Mem.Col2.SplitChar.vl_inc, eq_sub_of_add_eq e.symm]
    refine Valuation.map_sub_le _ ?_ ?_
    · rw [GlobalTheory.Mem.Col2.SplitChar.vl_apply, GlobalTheory.NormRatio.ChrFin.adEquiv_eq]
      exact hx w
    · rw [map_mul, GlobalTheory.Mem.Col2.SplitChar.vl_nat]
      exact (mul_le_of_le_one_right' (GlobalTheory.Mem.Col2.SplitChar.vl_le hs w)).trans
        ((GlobalTheory.NumeratorIdeal.mem_iff_valuation D.host.E hI _).1 hNm w)
  obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
  rw [e]
  refine add_mem (AddSubgroup.subset_closure ⟨b, hb, 1, one_mem _, (mul_one _).symm⟩)
    (AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem 𝔪, s, hs, ?_⟩)
  exact congrArg (· * s) (map_natCast ((Formalism.MainNotions.StandardLatticesGL3.inc D).comp (algebraMap (𝓞 D.host.E) D.host.E)) _).symm

end GlobalTheory.CosetOrth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIdealIntegralFiniteAdelesOfMemCompletionStatement
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_idealIntegralFiniteAdeles_of_memCompletion : ∀ {D : D7} (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ x : Formalism.MainNotions.StandardLatticesGL3.AE D,
  InHat (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (GlobalTheory.BotFormula.toFinE D x) → x ∈ hatId D 𝔪 := by
  first | exact @GlobalTheory.CosetOrth.mem_hatId_of_inHat | exact GlobalTheory.CosetOrth.mem_hatId_of_inHat | (intros; apply GlobalTheory.CosetOrth.mem_hatId_of_inHat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationBundleSymmetricPullbackOfUniformisat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationBundleSymmetricPullbackOfUniformisat
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.PrimDescent

theorem isPrim_of_unif : AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, LBIso U.LG.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → GlobalTheory.PolDeg.IsPrim D.toPre.P (o.onB.act w) := by
  intro R _ _ _ I hI D A G _ _ hS U O _ _ _ o oA oG hlin w hprim
  have := hI.2.2.2
  haveI := oG.hom w
  haveI := oG.hom (1 + w)
  haveI := o.onB.hom w
  haveI := o.onB.hom (1 + w)
  obtain ⟨⟨ρ, hρ, -⟩, -⟩ := GlobalTheory.JetSer.exists_unique_normPrim _ G U.LG (oG.act w) hprim
  have hRig := GlobalTheory.PullGenG.hasGen_one U.LG
  have h0 := (HasGen.of_gen ρ hρ).neg.add hRig
  obtain ⟨uΨ, huΨ⟩ := h0.gen U.LG.isLB (K' := Fin 4)
    ![(padd G (𝟙 _) (oG.act w)).left, 𝟙 G.left, (oG.act w).left, (toUnit G ≫ η[G]).left] ![1, -2, -1, 2] (by
      have h1' : (toUnit G ≫ η[G] : G ⟶ G) = 1 := rfl
      simp [fsum, Fin.sum_univ_four, Fin.sum_univ_five, GlobalTheory.JetSer.primφ, GlobalTheory.JetSer.primε, lf_single, padd_eq_mul, h1',
        Finsupp.single_neg, single_two, single_neg_two, Matrix.vecHead, Matrix.vecTail]
      abel)
  obtain ⟨u, hu, hn⟩ := GlobalTheory.PsiRescale.exists_normalised U.LG.isLB (oG.act w) uΨ huΨ
  have iG : ∀ i, IsMonHom ((![oG.act (1 + w), 𝟙 G, oG.act w, 1] : Fin 4 → (G ⟶ G)) i) := fun i => by
    fin_cases i
    exacts [oG.hom (1 + w), inferInstanceAs (IsMonHom (𝟙 G)), oG.hom w, inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))]
  have iB : ∀ i, IsMonHom ((![o.onB.act (1 + w), 𝟙 _, o.onB.act w, 1] : Fin 4 → (D.toPre.P.A ⟶ D.toPre.P.A)) i) :=
    fun i => by
    fin_cases i
    exacts [o.onB.hom (1 + w), inferInstanceAs (IsMonHom (𝟙 _)), o.onB.hom w,
      inferInstanceAs (IsMonHom (toUnit _ ≫ η[D.toPre.P.A]))]
  obtain ⟨κ, hκ, -⟩ := GlobalTheory.UT.PullDescent.exists_descent U.toUnifPre GlobalTheory.allSixLaws.1.globalFns hS (fun V _ c => by
      rw [Fin.prod_univ_four]
      show c ^ (1 : ℤ) * c ^ (-2 : ℤ) * c ^ (-1 : ℤ) * c ^ (2 : ℤ) = 1
      group)
    ![oG.act (1 + w), 𝟙 G, oG.act w, 1] ![o.onB.act (1 + w), 𝟙 _, o.onB.act w, 1] (fun e i => by
      have := (U.gt e).q_hom
      fin_cases i
      · exact hlin.q_lin e (1 + w)
      · show (Over.pullback (thick R I e)).map (𝟙 G) ≫ _ = _ ≫ (Over.pullback (thick R I e)).map (𝟙 _)
        rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      · exact hlin.q_lin e w
      · show (Over.pullback (thick R I e)).map (1 : G ⟶ G) ≫ _ =
          _ ≫ (Over.pullback (thick R I e)).map (1 : D.toPre.P.A ⟶ D.toPre.P.A)
        rw [CategoryTheory.Functor.map_one, CategoryTheory.Functor.map_one, MonObj.one_comp, MonObj.comp_one])
    (fun i => by
      fin_cases i
      · show (oG.act (1 + w)).left = (padd G (𝟙 _) (oG.act w)).left
        rw [oG.map_add, oG.map_one]
      all_goals rfl)
    (ψ := ![(padd D.toPre.P.A (𝟙 _) (o.onB.act w)).left, 𝟙 D.toPre.P.A.left, (o.onB.act w).left,
      (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left])
    (fun i => by
      fin_cases i
      · show (o.onB.act (1 + w)).left = (padd D.toPre.P.A (𝟙 _) (o.onB.act w)).left
        rw [o.onB.map_add, o.onB.map_one]
      all_goals rfl) u hu hn
  exact ⟨κ, hκ.1⟩

end GlobalTheory.PrimDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationBundleSymmetricPullbackOfUniformisatStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisationBundle_symmetric_pullback_of_uniformisation : AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, LBIso U.LG.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → GlobalTheory.PolDeg.IsPrim D.toPre.P (o.onB.act w) := by
  first | exact @GlobalTheory.PrimDescent.isPrim_of_unif | exact GlobalTheory.PrimDescent.isPrim_of_unif | (intros; apply GlobalTheory.PrimDescent.isPrim_of_unif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfCompletedLatticeSelfDualRankOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfCompletedLatticeSelfDualRankOne
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

namespace GlobalTheory.CosetOrth

variable {D : D7}

theorem hO_single_of_gram_one {S T : HSp D} (hS : S.gram = 1) (hT : T.gram = 1) (p : Fin T.rank) (q : Fin S.rank)
    (x : AE D) (y : WO S T) : hO S T (Matrix.single p q x) y = cA D (y p q) * x := by
  unfold hO
  rw [hS, hT, inv_one, Finset.sum_eq_single q, Finset.sum_eq_single q, Finset.sum_eq_single p, Finset.sum_eq_single p]
  · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.single_apply_same, map_one, one_mul, mul_one]
  · intro b _ hb; simp [Matrix.one_apply_ne hb.symm]
  · exact fun h => absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun d _ => ?_
    by_cases h : d = p
    · subst h; simp [Matrix.one_apply_ne hb]
    · simp [Matrix.single_apply_of_row_ne (Ne.symm h)]
  · exact fun h => absurd (Finset.mem_univ _) h
  · intro b _ hb; simp [Matrix.one_apply_ne hb.symm]
  · exact fun h => absurd (Finset.mem_univ _) h
  · intro b _ hb; simp [Matrix.single_apply_of_col_ne _ _ (Ne.symm hb)]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem fe_incA_mul (a : D.host.E) (z : AE D) : fe D (incA D a * z) = algebraMap D.host.E (FA D) a * fe D z := by
  rw [map_mul, fe_apply (incA D a), GlobalTheory.LatVac.finPart_incA, GlobalTheory.FinIdlRead.finAdEquiv_one_tmul]

theorem inHat_one_fe_iff (z : AE D) : InHat 1 (fe D z) ↔ finPart D z ∈ intAE D := by
  rw [inHat_one_iff, GlobalTheory.FinIdlRead.mem_intAE_iff_finAdEquiv]
  rfl

theorem inHat_of_char_dual : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (r : D.host.E) (LB : Lat T) (n : ℕ), IsStdChar D ψ (-1) →
  S.gram = 1 → T.gram = 1 → IsSelfDualC S (stdLat S) → IsSelfDualC T LB → r ≠ 0 →
  (∀ u ∈ (latO S T (stdLat S) LB fun _ => True), HatPt ((n : D.host.E) * r) 1 u) →
  ∀ (p : Fin T.rank) (q : Fin S.rank) (c : AE D), infPart D c = 0 →
  (∀ t : AE D, infPart D t = 0 → InHat 1 (fe D t) →
    ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (incA D (star r⁻¹) * (t * c)))) = 1) →
  InHat 1 (algebraMap D.host.E (FA D) ((n : D.host.E) * n * r) * fe D c) := by
  intro D ψ S T r LB n hψ hS hT hΛS hΛT hr hL p q c hc h
  have hmem : (Matrix.single p q (incA D (n : D.host.E) * c) : WO S T) ∈
      latO S T (stdLat S) LB fun _ => True := by
    refine GlobalTheory.LatVac.mem_of_char hψ hΛS hΛT ?_ fun u' hu' => ?_
    · rw [Matrix.map_single, map_mul, hc, mul_zero, Matrix.single_zero]
    · obtain ⟨h0, h1⟩ := hL u' hu'
      have h0' : infPart D (u' p q) = 0 := congrFun (congrFun h0 p) q
      have ht := h (cA D (incA D ((n : D.host.E) * r) * u' p q))
        (by rw [(GlobalTheory.IdemSupport.parts_cA _).1, map_mul, h0', mul_zero, map_zero])
        (by
          rw [inHat_one_fe_iff]
          refine GlobalTheory.IdemSupport.finPart_cA_mem ?_
          rw [← inHat_one_fe_iff, fe_incA_mul]
          exact h1 p q)
      have e : incA D (star r⁻¹) * (cA D (incA D ((n : D.host.E) * r) * u' p q) * c) =
          cA D (u' p q) * (incA D (n : D.host.E) * c) := by
        have e1 : incA D (star r⁻¹) * incA D (star ((n : D.host.E) * r)) = incA D (n : D.host.E) := by
          rw [← map_mul, ← star_mul, mul_assoc, mul_inv_cancel₀ hr, mul_one, star_natCast]
        rw [map_mul, GlobalTheory.IdemSupport.cA_incA, ← e1]
        ring
      rw [e] at ht
      unfold symplO
      rw [hO_single_of_gram_one hS hT]
      exact ht
  have h2 := (hL _ hmem).2 p q
  rw [Matrix.single_apply_same, fe_incA_mul, ← mul_assoc, ← map_mul] at h2
  rw [mul_right_comm]
  exact h2

end GlobalTheory.CosetOrth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfCompletedLatticeSelfDualRankOneStatement
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_of_completedLattice_selfDual_rankOne : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (r : D.host.E) (LB : Lat T) (n : ℕ), IsStdChar D ψ (-1) →
  S.gram = 1 → T.gram = 1 → IsSelfDualC S (stdLat S) → IsSelfDualC T LB → r ≠ 0 →
  (∀ u ∈ (latO S T (stdLat S) LB fun _ => True), HatPt ((n : D.host.E) * r) 1 u) →
  ∀ (p : Fin T.rank) (q : Fin S.rank) (c : AE D), infPart D c = 0 →
  (∀ t : AE D, infPart D t = 0 → InHat 1 (fe D t) →
    ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (incA D (star r⁻¹) * (t * c)))) = 1) →
  InHat 1 (algebraMap D.host.E (FA D) ((n : D.host.E) * n * r) * fe D c) := by
  first | exact @GlobalTheory.CosetOrth.inHat_of_char_dual | exact GlobalTheory.CosetOrth.inHat_of_char_dual | (intros; apply GlobalTheory.CosetOrth.inHat_of_char_dual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPairingDiagRelAmple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FactorAmple

open GlobalTheory.CechPic

theorem lam_rosati {K : Type} [Field K] {B : Over (Sp K)} [GrpObj B] [IsCommMonObj B] {M : LB B.left} (hM : M.IsLB)
    {u v : B ⟶ B} (h : RosatiAdj B M u v) {T : Over (Sp K)} (x y : T ⟶ B) :
    lam (cls M hM) (x ≫ u) y = lam (cls M hM) x (y ≫ v) := by
  have e := GlobalTheory.AdjPolLocal.lbIso_of_rosatiAdj_local K B M u v hM h
  have h1 : (cubeLB B ![fst B B ≫ u, snd B B] M).IsLB := LB.isLB_linComb hM _ _
  have h2 : (cubeLB B ![fst B B, snd B B ≫ v] M).IsLB := LB.isLB_linComb hM _ _
  have e' := (cls_eq_iff h1 h2).2 e
  rw [cls_cube_two hM, cls_cube_two hM] at e'
  have e'' := congrArg (pull (lift x y : T ⟶ G2 B).left) e'
  rw [pull_lam, pull_lam] at e''
  simpa using e''

theorem act_nsmul {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {O : Type} [Ring O] (ρ : RingAct A O)
    (u : O) (n : ℕ) : ρ.act (n • u) = ρ.act u ^ n := by
  have h0 : ρ.act 0 = 1 := by
    have e := ρ.map_add 0 0
    rw [add_zero] at e
    have e' : ρ.act 0 * 1 = ρ.act 0 * ρ.act 0 := by rw [_root_.mul_one]; exact e.trans (Hom.mul_def _ _).symm
    exact (mul_left_cancel e').symm
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, ρ.map_add, ih, pow_succ]; exact (Hom.mul_def _ _).symm

theorem lam_push {S S' : Scheme.{0}} {G : Over S} {H : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj H]
    [IsCommMonObj H] {f : S' ⟶ S} {φ : H.left ⟶ G.left} (hp : IsGrpPullback H G f φ) (c : Pic G.left)
    {T : Over S'} (z w : T ⟶ H) :
    lam c (pushHom hp T z) (pushHom hp T w) = lam (pull φ c) z w := by
  simp only [lam, ← map_mul, ← map_one (pushHom hp T)]
  simp only [← pull_comp]
  rfl

end GlobalTheory.Mum.FactorAmple

namespace GlobalTheory.Mum

open GlobalTheory.CechPic GlobalTheory.Mum.FactorAmple

theorem factorPairing_diag_relAmple : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → Out.RelAmple ((Over.pullback (jK R)).obj G) ((((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀).pull (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left) := by
  intro R _ _ _ hR D D' F hF A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi κ₀ hκ
  have := A'.isAb.comm
  have hp := isGrpPullback_pullback G (jK R)
  have hp' := isGrpPullback_pullback G' (jK R)
  let X := (Over.pullback (jK R)).obj G
  let ιK : X ⟶ (Over.pullback (jK R)).obj G' := (Over.pullback (jK R)).map inc
  let a : X ⟶ A'.A := ιK ≫ U'.gen.hom
  have hM := A'.isLB
  have hL' : U'.LG.L.IsLB := U'.LG.isLB
  have hΛ : (abelian₂ G' U'.LG.L).IsLB := LB.isLB_linComb hL' _ _
  have h1 := pull_isLB hΛ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left
  have h2 := pull_isLB h1 κ₀
  have h3 := pull_isLB h2 (lift (𝟙 X) (𝟙 X) : X ⟶ G2 X).left
  have e1 : pushHom hp X (𝟙 X) ≫ inc = pushHom hp' X ιK := by
    ext1
    show (𝟙 _ ≫ pullback.fst G.hom (jK R)) ≫ inc.left = ιK.left ≫ pullback.fst G'.hom (jK R)
    rw [Category.id_comp]
    exact (pullback.lift_fst _ _ _).symm
  have e2 : pushHom hp X (𝟙 X) ≫ inc ≫ oG.act F.f =
      pushHom hp' X (ιK ≫ (Over.pullback (jK R)).map (oG.act F.f)) := by
    rw [← Category.assoc, e1]
    ext1
    show (ιK.left ≫ pullback.fst G'.hom (jK R)) ≫ (oG.act F.f).left =
      (ιK ≫ (Over.pullback (jK R)).map (oG.act F.f)).left ≫ pullback.fst G'.hom (jK R)
    rw [Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg (ιK.left ≫ ·) (pullback.lift_fst _ _ _).symm
  have eN : cls _ h3 = lam (cls _ hL') (pushHom hp X (𝟙 X) ≫ inc) (pushHom hp X (𝟙 X) ≫ inc ≫ oG.act F.f) := by
    rw [cls_pull h2, cls_pull h1, cls_pull hΛ, ← pull_comp, ← pull_comp]
    rw [← Category.assoc, FactorAdd.lift_square hp hκ, ← Over.comp_left]
    have e : cls (abelian₂ G' U'.LG.L) hΛ = lam (cls _ hL') (fst G' G') (snd G' G') := cls_cube_two hL' _ _ hΛ
    rw [e, pull_lam]
    simp
  have hgen := U'.gen_hom
  have eT : pull (pullback.fst G'.hom (jK R)) (cls _ hL') = pull U'.gen.hom.left (cls _ hM) := by
    obtain ⟨w, hw⟩ := U'.ext
    rw [← cls_pull hL' _ (pull_isLB hL' _), ← cls_pull hM _ (pull_isLB hM _)]
    exact ((cls_eq_iff (pull_isLB hM _) (pull_isLB hL' _)).2 ⟨w, hw⟩).symm
  have eN' : cls _ h3 = lam (cls _ hM) a (a ≫ oA.act F.f) := by
    rw [eN, e2, e1, lam_push hp', eT, lam_pull]
    congr 1
    rw [Category.assoc, Category.assoc, hlin.ext F.f]
  have hie : inc ≫ oG.act F.e = inc := by rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  have ha : a ≫ oA.act F.e = a := by
    show (ιK ≫ U'.gen.hom) ≫ oA.act F.e = ιK ≫ U'.gen.hom
    rw [Category.assoc, ← hlin.ext F.e, ← Category.assoc, ← Functor.map_comp, hie]
  have hΘ : ∃ t : LB.Gen (Theta A'.A A'.L), t.IsGen := GlobalTheory.GenericAmpleDvr.triv_theta A'.isAb hM
  obtain ⟨⟨b, hb, hbe⟩, -, -⟩ := hF
  have rosE : ∀ x y : X ⟶ A'.A, lam (cls _ hM) (x ≫ oA.act F.e) y = lam (cls _ hM) x (y ≫ oA.act (star F.e)) :=
    fun x y => lam_rosati hM (oA.rosati F.e) x y
  have hpow : ∀ (u : F.O) (n : ℕ), (a ≫ oA.act u) ^ n = a ≫ oA.act (n • u) := by
    intro u n
    rw [act_nsmul oA.toRingAct]
    exact (map_pow (preHom (G := A'.A) a) (oA.act u) n).symm
  have eb : b • cls _ h3 = lam (cls _ hM) a a := by
    rw [eN']
    calc b • lam (cls _ hM) a (a ≫ oA.act F.f)
        = b • lam (cls _ hM) (a ≫ oA.act F.e) ((a ≫ oA.act F.e) ≫ oA.act F.f) := by rw [ha]
      _ = b • lam (cls _ hM) a (a ≫ oA.act (star F.e * F.f * F.e)) := by
          rw [rosE, oA.map_mul, oA.map_mul]; simp only [Category.assoc]
      _ = lam (cls _ hM) a ((a ≫ oA.act (star F.e * F.f * F.e)) ^ b) := (lam_pow_right hM hΘ _ _ b).symm
      _ = lam (cls _ hM) a (a ≫ oA.act (star F.e * F.e)) := by rw [hpow, hbe]
      _ = lam (cls _ hM) (a ≫ oA.act F.e) (a ≫ oA.act F.e) := by
          rw [oA.map_mul, ← Category.assoc, ← rosE]
      _ = lam (cls _ hM) a a := by rw [ha]
  have hΛA : (abelian₂ A'.A A'.L).IsLB := LB.isLB_linComb hM _ _
  have hDg := pull_isLB hΛA (lift (𝟙 A'.A) (𝟙 A'.A) : A'.A ⟶ G2 A'.A).left
  have eD : lam (cls _ hM) a a = cls _ (pull_isLB hDg a.left) := by
    have e : cls (abelian₂ A'.A A'.L) hΛA = lam (cls _ hM) (fst A'.A A'.A) (snd A'.A A'.A) := cls_cube_two hM _ _ hΛA
    rw [cls_pull hDg, cls_pull hΛA, e, pull_lam, pull_lam]
    simp
  have hNb := isLB_lbPow h3 b
  have iso := (cls_eq_iff hNb (pull_isLB hDg a.left)).1 (by rw [cls_lbPow h3, eb, eD])
  have := hG'.separated
  have : IsSeparated ((Over.pullback (jK R)).obj G').hom := by dsimp; infer_instance
  let prK : (Over.pullback (jK R)).obj G' ⟶ X := (Over.pullback (jK R)).map pr
  have hs : ιK ≫ prK = 𝟙 X := by rw [← Functor.map_comp, hip]; exact (Over.pullback (jK R)).map_id G
  have : IsSeparated prK.left := by
    have e : prK.left ≫ X.hom = ((Over.pullback (jK R)).obj G').hom := Over.w prK
    have : IsSeparated (prK.left ≫ X.hom) := by rw [e]; infer_instance
    exact IsSeparated.of_comp prK.left X.hom
  have : IsClosedImmersion ιK.left := by
    have : IsClosedImmersion (ιK.left ≫ prK.left) := by
      rw [← Over.comp_left, hs]; exact inferInstanceAs (IsClosedImmersion (𝟙 _))
    exact IsClosedImmersion.of_comp ιK.left prK.left
  have : IsIso U'.gen.hom.left := ((Over.forget _).mapIso U'.gen).isIso_hom
  have : IsFinite a.left := by
    show IsFinite (ιK ≫ U'.gen.hom).left
    rw [Over.comp_left]; infer_instance
  have := A'.isAb.proper
  have : IsProper X.hom := by
    have e : a.left ≫ A'.A.hom = X.hom := Over.w a
    rw [← e]; infer_instance
  have hDgA := GlobalTheory.isAmpleLB_of_relAmple_of_isAffine A'.A hDg
    (GlobalTheory.EighthPowerFactor.relAmple_diag_lam A'.isAb hM hΘ A'.ample)
  have hNa := (hDgA.pull_of_isFinite a.left).of_lbIso hNb iso
  exact (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine X h3).2 ((GlobalTheory.isAmpleLB_pow_iff h3 hb).1 hNa)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowIntegralCompletedHomLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowIntegralCompletedHomLattice
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CosetOrth.LatInt

theorem exists_pow_mem (D : D7) : ∃ k : ℕ, (((D.host.QS * D.host.q) ^ k : ℕ) : 𝓞 D.host.E) ∈ D.host.𝔟 := by
  have hb := ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D
  have h : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∈ D.host.𝔟.radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro J ⟨hJ, hp⟩
    have hne : J ≠ ⊥ := fun e => hb (le_bot_iff.1 (e ▸ hJ))
    exact GlobalTheory.HalfCompare.two_q_mem (P := ⟨J, hp, hne⟩) (Ideal.dvd_iff_le.2 hJ)
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [Nat.cast_pow]; exact hk⟩

theorem homL_entry {D : D7} {N N' : ℕ} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ Formalism.MainNotions.TaylorLogMetric.homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) (i : Fin N') (j : Fin N) :
    A i j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    have h1 : (Pi.single j (1 : D.host.E) : Fin N → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
      intro l _
      by_cases h : l = j
      · subst h
        rw [Pi.single_eq_same]
        exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · rw [Pi.single_eq_of_ne h]
        exact zero_mem _
    have h2 := hA _ h1 i trivial
    rw [Matrix.mulVec_single_one] at h2
    exact h2
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

theorem YYl_entry {D : D7} {N N' : ℕ} {B : Matrix (Fin N') (Fin N) D.host.E}
    (hB : B ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) (i : Fin N') (j : Fin N) :
    B i j ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 (homL_entry hA i j)
    have : (a • A) i j = c • a := by
      rw [Matrix.smul_apply, smul_eq_mul, ← hc, Algebra.smul_def, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ c ha
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

theorem mul_int {D : D7} {n : 𝓞 D.host.E} (hn : n ∈ D.host.𝔟) {x : D.host.E}
    (hx : x ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) :
    ∃ b : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E b = algebraMap (𝓞 D.host.E) D.host.E n * x := by
  have hb := ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D
  have h1 : algebraMap (𝓞 D.host.E) D.host.E n * x ∈
      (D.host.𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * D.host.AA0 :=
    FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hn) hx
  rw [Formalism.BasicNotions.Host.AA0, mul_inv_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.2 hb)] at h1
  exact (FractionalIdeal.mem_one_iff _).1 h1

theorem inHat_tmul {D : D7} {α : Af D.host.F} (hα : α ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F) (c x : D.host.E) (b : 𝓞 D.host.E)
    (hb : algebraMap (𝓞 D.host.E) D.host.E b = c * x) :
    InHat 1 (algebraMap D.host.E (FA D) c * fe D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x)) := by
  have e : fe D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) =
      GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E α * algebraMap D.host.E (FA D) x := rfl
  rw [e, mul_left_comm, ← map_mul, ← hb]
  refine InHat.mul_left ((inHat_one_iff _).2 fun w => ?_) ((inHat_one_iff _).2 fun w => ?_)
  · exact GlobalTheory.AdeleBaseChange.adMap_int (F := D.host.F) (E := D.host.E) hα w
  · change Valued.v ((algebraMap (𝓞 D.host.E) D.host.E b : D.host.E) : w.adicCompletion D.host.E) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact w.valuation_le_one b

theorem exists_hatPt_of_mem_latO : ∀ {D : D7} (S T : HSp D) (r : D.host.E) (LB : Lat T), r ≠ 0 →
  (∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finPt (S := S) (T := T) rfl rfl r z ∈ (latO S T (stdLat S) LB fun _ => True) →
    z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank)) →
  ∃ k : ℕ, ∀ u ∈ (latO S T (stdLat S) LB fun _ => True), HatPt ((((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E) * r) 1 u := by
  intro D S T r LB hr hz
  obtain ⟨k, hk⟩ := exists_pow_mem D
  refine ⟨k, fun u hu => ⟨Matrix.ext fun i j => GlobalTheory.LatVac.infPart_of_mem hu i j, fun i j => ?_⟩⟩
  refine GlobalTheory.LatVac.latO_induction (p := fun u => InHat 1
    (algebraMap D.host.E (FA D) ((((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E) * r) * fe D (u i j))) ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    have h1 := GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) hM
    have e : finPt (S := S) (T := T) rfl rfl r (-r • M) = GlobalTheory.LatVac.finTens 1 M := by
      have : (Matrix.of fun i j => -(r⁻¹ * (-r • M) (Fin.cast rfl i) (Fin.cast rfl j))) = M := by
        ext i j
        simp [hr]
      unfold finPt
      rw [this]
      rfl
    obtain ⟨b, hb⟩ := mul_int hk (YYl_entry (hz _ (e ▸ h1)) i j)
    refine inHat_tmul hα _ _ (-b) ?_
    rw [map_neg, hb, map_natCast, Matrix.smul_apply, smul_eq_mul]
    ring
  · rw [Matrix.zero_apply, map_zero, mul_zero]
    exact inHat_zero _
  · intro x y hx hy
    rw [Matrix.add_apply, map_add (f := _), mul_add]
    exact hx.add hy
  · intro x hx
    rw [Matrix.neg_apply, map_neg, mul_neg]
    exact hx.neg

end GlobalTheory.CosetOrth.LatInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowIntegralCompletedHomLatticeStatement
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_integral_completedHomLattice : ∀ {D : D7} (S T : HSp D) (r : D.host.E) (LB : Lat T), r ≠ 0 →
  (∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finPt (S := S) (T := T) rfl rfl r z ∈ (latO S T (stdLat S) LB fun _ => True) →
    z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank)) →
  ∃ k : ℕ, ∀ u ∈ (latO S T (stdLat S) LB fun _ => True), HatPt ((((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E) * r) 1 u := by
  first | exact @GlobalTheory.CosetOrth.LatInt.exists_hatPt_of_mem_latO | exact GlobalTheory.CosetOrth.LatInt.exists_hatPt_of_mem_latO | (intros; apply GlobalTheory.CosetOrth.LatInt.exists_hatPt_of_mem_latO <;> assumption)
end
end

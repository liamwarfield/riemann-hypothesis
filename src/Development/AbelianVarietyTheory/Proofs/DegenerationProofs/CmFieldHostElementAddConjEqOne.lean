module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfield
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumDHomDegenerationValuesFieldExtension

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CmFieldHostElementAddConjEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.AbVal

theorem cmField_host_element_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.w0 + H.bar H.w0 = 1 := by
  have h1 : H.bar H.rt ^ 2 = H.rt ^ 2 := by
    rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have h2 : 2 * H.bar H.w0 = 1 + H.bar H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    simpa [map_ofNat] using this
  have h3 : H.bar H.rt = -H.rt := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with e | e
    · exfalso
      have e' : IsCMField.complexConj E (H.rt : E) = H.rt := by rw [← H.bar_eq, e]
      obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have c := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
      rw [e'] at c
      have r : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
        have := congrArg (fun z : 𝓞 E => φ (z : E)) H.rt_sq
        simpa using this
      obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 c.symm
      rw [hx] at r
      have r' : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast r
      have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      nlinarith [sq_nonneg x]
    · exact e
  have : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    rw [mul_add, h2, H.two_weight_eq_one_add_root, h3]; ring
  exact mul_left_cancel₀ two_ne_zero this

theorem rg_ne_zero {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) : ν.rg ≠ 0 := fun h =>
  (((Units.isUnit _).map _).map _).ne_zero ((dif_pos (fun z _ =>
    Good.mem (L := D.P.L) (z := z) (J := ν.J) (fun ψ => ν.good ψ trivial) (fun _ : PUnit => eSec D.P.A)
      (TF (R := R) F).hom)).symm.trans h)

theorem exists_ringHom_lift {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {O : Type} [CommRing O]
    (act : RingAct A O) {V : Type} [AddCommGroup V] [Module ℂ V] (ex : V → (T ⟶ A))
    (hadd : ∀ z w, ex (z + w) = ex z * ex w)
    (hlift : ∀ f : A ⟶ A, IsMonHom f → ∃! F : V →ₗ[ℂ] V, ∀ z, ex (F z) = ex z ≫ f) :
    ∃ F : O →+* Module.End ℂ V, ∀ a z, ex (F a z) = ex z ≫ act.act a := by
  choose F hF hU using fun a => hlift (act.act a) (act.hom a)
  have add : ∀ a b, F (a + b) = F a + F b := fun a b => (hU _ _ fun z => by
    rw [LinearMap.add_apply, hadd, hF, hF, act.map_add]
    exact (MonObj.comp_mul _ _ _).symm).symm
  refine ⟨RingHom.mk' ⟨⟨F, (hU _ _ fun z => ?_).symm⟩, fun a b => (hU _ _ fun z => ?_).symm⟩ add, hF⟩
  · rw [act.map_one, Category.comp_id]; rfl
  · rw [act.map_mul, Module.End.mul_apply, hF, hF, Category.assoc]

theorem valSt (hL : Laws) (hFam : BrFamSt) (hEx : FibExSt) (hGrp : FibGrpSt) (hCube : FibCubeSt) (hSym : FibSymSt)
    (hRos : FibRosSt) (hPrim : FibPrimSt) (hSec : FibSecSt) (hLie : FibLieSt) : ValSt := by
  intro E _ _ _ H D R _ _ _ A
  letI := H.starRing
  obtain ⟨g, Λ, Hm, χ, Ef, ex, fr, hf, hEf, hbij⟩ := hEx R A.D₀.P A.ν.J A.ν.good
  obtain ⟨hdisc, hfull, hherm, hpos, hnorm, hχ, hadd, hsurj, hker, hfr, hlift⟩ := hGrp R A.D₀ _ g Λ Hm χ ex fr hf
  have hcube := hCube R A.D₀ _ g Λ Hm χ ex fr hf
  obtain ⟨hsym, hneg⟩ := hSym R A.D₀ _ g Λ Hm χ ex fr hf
  have hros := hRos R A.D₀ _ g Λ Hm χ ex fr hf
  have hprim := hPrim R A.D₀ _ g Λ Hm χ ex fr hf
  obtain ⟨θ, hθ, hθv⟩ := hSec R A.D₀ _ g Λ Hm χ ex fr hf A.ν.th
  have hlie := hLie R A.D₀ _ g Λ Hm χ ex fr hf
  obtain ⟨F, hF⟩ := exists_ringHom_lift A.oa.onB.toRingAct ex hadd hlift
  have hmem : ∀ a, ∀ l ∈ Λ, F a l ∈ Λ := fun a l hl => by
    haveI := A.oa.onB.hom a
    rw [← hker, hF, (hker l).2 hl, MonObj.one_comp]
  have hadj : ∀ a z w, hermForm Hm (F a z) w = hermForm Hm z (F (star a) w) := fun a => by
    haveI := A.oa.onB.hom a
    haveI := A.oa.onB.hom (star a)
    obtain ⟨r, hr⟩ := exists_ros hL.globalFns A.D₀.P.isAb A.D₀.P.isLB _ _ (A.oa.onB.rosati a)
    exact (hros _ _ (A.oa.onB.hom a) (A.oa.onB.hom (star a)) _ _ (hF a) (hF (star a)) r hr).1
  let B : An H :=
    { gB := g, abelian₂ := Λ, discrete := hdisc, full := hfull, Hm := Hm, Hm_herm := hherm, Hm_pos := hpos, Ef := Ef,
      Ef_eq := hEf, Ef_bij := hbij, chi := χ, chi_norm := hnorm, chi_add := hχ, chi_neg := hneg, F := F,
      F_mem := hmem, F_adj := hadj, X := PUnit, ct := 0, ct_smul := fun a _ => (map_zero (F a)).symm, T := 0,
      T_symm := fun _ _ => rfl, T_adj := fun _ _ _ => rfl, psi := fun _ => 1, psi_neg := fun _ => rfl,
      psi_add := fun _ _ => by simp, be := 0, be_symm := fun _ _ => rfl, be_pos := fun _ h => (h rfl).elim,
      be_adj := fun _ _ _ => rfl, be_even := fun _ => dvd_zero _ }
  have hrg := rg_ne_zero A.ν
  have h0 := (fr 0).ne_zero
  have hw : ∀ z w, hermForm Hm z w = hermForm Hm z (F H.w0 w) + hermForm Hm (F H.w0 z) w := fun z w => by
    rw [hadj]
    refine Eq.trans ?_ (B.H_add_right z (F H.w0 w) (F (star H.w0) w))
    rw [← LinearMap.add_apply, ← map_add (f := _), show H.w0 + star H.w0 = 1 from cmField_host_element_add_conj_eq_one H, map_one]
    rfl
  have hp := hprim _ (A.oa.onB.hom H.w0) (F H.w0) (hmem H.w0) (hF H.w0) hw Ef hEf
  have hth : ∀ z, A.N.th (A.ν.eA.symm (ex z)) = θ z * fr 0 / A.ν.rg * ((fr z / fr 0 : ℂˣ) : ℂ) := fun z => by
    have e := A.ν.th_eq (A.ν.eA.symm (ex z))
    rw [MulEquiv.apply_symm_apply, hθv] at e
    change _ * A.ν.rg = _ at e
    rw [Units.val_div_eq_div_val, eq_div_of_mul_eq hrg e]
    field_simp
  refine ⟨B, fun z => A.ν.eA.symm (ex z), fun z => fr z / fr 0, fun z => θ z * fr 0 / A.ν.rg,
    ⟨fun z w => (congrArg A.ν.eA.symm (hadd z w)).trans (map_mul _ _ _), A.ν.eA.symm.surjective.comp hsurj,
      fun z => (map_eq_one_iff _ A.ν.eA.symm.injective).trans (hker z), div_self' _, fun l z => ?_, fun x y z => ?_,
      fun x => ?_, ⟨by simp only [div_eq_mul_inv]; exact (hθ.mul_const _).mul_const _, fun l z => ?_⟩, hth⟩, ?_, ?_, fun τ => ?_, fun a z => ?_,
      fun a b r hr x z => ?_, fun t ht z => ?_⟩
  · beta_reduce
    rw [Units.val_div_eq_div_val, Units.val_div_eq_div_val, hfr l z, mul_div_assoc]
    rfl
  · refine Units.ext ?_
    have e := hcube x y z
    simp only [Units.val_mul, Units.val_div_eq_div_val, A.ν.θ_eq, MulEquiv.apply_symm_apply]
    field_simp
    linear_combination e
  · refine Units.ext ?_
    have e := hsym x
    simp only [Units.val_mul, Units.val_div_eq_div_val, A.ν.σ_eq, MulEquiv.apply_symm_apply]
    rw [← e, mul_div_assoc]
  · have e₁ := hθv (z + l)
    rw [hadd, (hker l).2 l.2, _root_.mul_one, hθv, hfr l z, ← _root_.mul_assoc] at e₁
    have e₂ := mul_right_cancel₀ (fr (z + l)).ne_zero e₁
    change θ (z + l) * fr 0 / A.ν.rg = (χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l)) ^ 1 *
      Complex.exp (Real.pi * B.H 0 l) * (θ z * fr 0 / A.ν.rg)
    rw [← e₂, B.H_zero_left, mul_zero, Complex.exp_zero]
    ring
  · intro hz
    haveI := A.closed
    obtain ⟨-, -, -, ⟨s, f, hs, hf0⟩, hv, -⟩ := hFam R A.D₀ A.even A.bimult ℂ A.N A.ν 1 le_rfl
    obtain ⟨c, rfl⟩ := hv s f hs
    refine hf0 (funext fun α => funext fun x => ?_)
    obtain ⟨z, hz'⟩ := hsurj (A.ν.eA (x * A.N.c α))
    have e := hth z
    rw [hz', MulEquiv.symm_apply_apply, congrFun hz z] at e
    simp [NumD.vth, e]
  · obtain ⟨t, h₁, h₂, -⟩ := A.w0
    exact (hp t ⟨h₁, h₂⟩).1
  · obtain ⟨n, h₁, h₂⟩ := A.det τ
    rw [← h₂]
    exact congrArg (· + _) (hlie _ (ofRingAct A.oa.onB.toRingAct) (fun a => F a) hF τ n h₁)
  · simp only [MulEquiv.apply_symm_apply]
    exact hF a z
  · have e := (hros _ _ (A.oa.onB.hom a) (A.oa.onB.hom b) _ _ (hF a) (hF b) r hr).2 x z
    simp only [Units.val_div_eq_div_val, MulEquiv.apply_symm_apply]
    change _ * ((fr (F a x) : ℂ) / _) * _ * ((fr (x + F b z) : ℂ) / _) = (fr (F a x + z) : ℂ) / _ * _ * ((fr (F b z) : ℂ) / _)
    field_simp
    linear_combination e
  · have e := (hp t ht).2 z
    simp only [Units.val_div_eq_div_val, MulEquiv.apply_symm_apply]
    change _ * _ * ((fr (F H.w0 z) : ℂ) / _) = (fr (z + F H.w0 z) : ℂ) / _
    field_simp
    linear_combination e

end GlobalTheory.Ex.Arch.AbVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPrimitiveRootUnitOnIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section

namespace GlobalTheory.SymLevelDescent

open GlobalTheory.ThetaDescent

theorem hypS_descend {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) {A₀ : Over (Sp K₀)} {A : Over (Sp K)}
    [GrpObj A₀] [IsCommMonObj A₀] [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A₀) {φ : A.left ⟶ A₀.left}
    (h : IsGrpPullback A A₀ (spMap i) φ) {L₀ : LB A₀.left} {L : LB A.left} (hL₀ : L₀.IsLB) (hL : L.IsLB)
    (hb : LBIso L (L₀.pull φ)) {w wd : A ⟶ A} {w₀ wd₀ : A₀ ⟶ A₀} (e : φ ≫ w₀.left = w.left ≫ φ)
    (ed : φ ≫ wd₀.left = wd.left ≫ φ) (hw : IsMonHom w) (hwd : IsMonHom wd) (hs : w * wd = 𝟙 A)
    (hp : LBIso L (cubeLB A ![𝟙 A, w] L))
    (ha : LBIso (cubeLB A ![fst A A ≫ w, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ wd] L)) :
    GlobalTheory.ZH.HypS A₀ L₀ := by
  have F := GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K₀ K i
  have pa := fun {T : Over (Sp K)} (x : T ⟶ A) => GlobalTheory.SymSpread.pushPt_comp h e x
  have pd := fun {T : Over (Sp K)} (x : T ⟶ A) => GlobalTheory.SymSpread.pushPt_comp h ed x
  have hc : ∀ {T : Over (Sp K)} {n : ℕ} (x : Fin n → (T ⟶ A)), (cubeLB A x L).IsLB :=
    fun x => DVR.linComb_isLB _ hL _ _
  have hc₀ : ∀ {T : Over (Sp K₀)} {n : ℕ} (x : Fin n → (T ⟶ A₀)), (cubeLB A₀ x L₀).IsLB :=
    fun x => DVR.linComb_isLB _ hL₀ _ _
  refine ⟨w₀, wd₀, (F.2 A₀ A₀ A A φ φ w₀ w h h e).1 hw, (F.2 A₀ A₀ A A φ φ wd₀ wd h h ed).1 hwd, ?_, ?_, ?_⟩
  · let U := pushPt h.1.w (𝟙 A)
    have hU : U.left = φ := Category.id_comp _
    haveI : Epi U.left := hU ▸ (F.1 _ _ _ _ φ h.1).1
    apply preHom_injective U
    have b : pushPt h.1.w (w * wd) = pushPt h.1.w w * pushPt h.1.w wd := map_mul (pushHom h A) _ _
    have c := pa (𝟙 A)
    have d := pd (𝟙 A)
    rw [Category.id_comp] at c d
    rw [hs, c, d, ← MonObj.comp_mul] at b
    exact b.symm.trans (Category.comp_id _).symm
  · let U := pushPt h.1.w (𝟙 A)
    have hU : U.left = φ := Category.id_comp _
    have h₁ := GlobalTheory.SymSpread.lbIso_cube h hL₀ hL hb ![𝟙 A₀, w₀] ![𝟙 A, w] U (fun i => by
      fin_cases i
      · simp [U]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _))
    rw [hU] at h₁
    refine (lb_gen_iso_descend_field K₀ K i _ _ A₀.hom A.hom φ hA.smooth hA.proper hA.geomConnected h.1).2 _ _ hL₀
      (hc₀ _) ?_
    exact LBIso.trans (pull_isLB hL₀ _) hL (pull_isLB (hc₀ _) _) hb.symm
      (LBIso.trans hL (hc _) (pull_isLB (hc₀ _) _) hp h₁)
  · have A₂ := AbelianSchemeGerms.isAbelianScheme_tensor A₀ A₀ hA hA
    let U := lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))
    have h₁ := GlobalTheory.SymSpread.lbIso_cube h hL₀ hL hb ![fst A₀ A₀ ≫ w₀, snd A₀ A₀] ![fst A A ≫ w, snd A A] U (fun i => by
      fin_cases i
      · exact (pa _).trans (by simp [U])
      · simp [U])
    have h₂ := GlobalTheory.SymSpread.lbIso_cube h hL₀ hL hb ![fst A₀ A₀, snd A₀ A₀ ≫ wd₀] ![fst A A, snd A A ≫ wd] U (fun i => by
      fin_cases i
      · simp [U]
      · exact (pd _).trans (by simp [U]))
    refine (lb_gen_iso_descend_field K₀ K i _ _ (A₀ ⊗ A₀).hom (A ⊗ A).hom U.left A₂.smooth A₂.proper A₂.geomConnected
      (GlobalTheory.SymSpread.isPullback_square h)).2 _ _ (hc₀ _) (hc₀ _) ?_
    exact LBIso.trans (pull_isLB (hc₀ _) _) (hc _) (pull_isLB (hc₀ _) _) h₁.symm
      (LBIso.trans (hc _) (hc _) (pull_isLB (hc₀ _) _) ha h₂)

theorem unitOn_zpow {R : Type} [CommRing R] (u : Rˣ) (n : ℤ) : unitOn u ^ n = unitOn (u ^ n) :=
  (map_zpow (Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom) _ n).symm

theorem isPrimitiveRoot_unitOn_iff {R : Type} [CommRing R] (u : Rˣ) (k : ℕ) :
    IsPrimitiveRoot (unitOn u) k ↔ IsPrimitiveRoot u k :=
  IsPrimitiveRoot.map_iff_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom)
    (Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1)

theorem level_descend {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) (Q : Out.PolAV (Sp K))
    (A₀ : Over (Sp K₀)) [GrpObj A₀] (hab : IsAbelianScheme A₀) (hdim : SmoothOfRelativeDimension Q.g A₀.hom)
    (L₀ : LB A₀.left) (hL : L₀.IsLB) (hr : Out.Rigidified A₀ L₀) (hs : Out.Sym A₀ L₀) (hamp : Out.RelAmple A₀ L₀)
    (hk : Out.KTriv A₀ L₀) {φ : Q.A.left ⟶ A₀.left} (hp : IsGrpPullback Q.A A₀ (spMap i) φ)
    (hw : LBIso Q.L (L₀.pull φ)) (k : ℕ) (z : K₀ˣ) (t : Out.Level Q k (unitOn (Units.map i.toMonoidHom z)))
    (pt₀ : Fin (2 * Q.g) → (Out.baseOver (Sp K₀) ⟶ A₀)) (hpt : ∀ a, (t.pt a).left ≫ φ = spMap i ≫ (pt₀ a).left) :
    Nonempty (Out.Level ⟨A₀, hab, Q.g, hdim, L₀, hL, hr, hs, hamp, hk⟩ k (unitOn z)) := by
  let U : Over.mk ((Out.baseOver (Sp K)).hom ≫ spMap i) ⟶ Out.baseOver (Sp K₀) := Over.homMk (spMap i) (by simp)
  haveI : Epi U.left := epi_spMap i
  have hU : ∀ a, pushHom hp _ (t.pt a) = preHom U (pt₀ a) := fun a => Over.OverMorphism.ext (hpt a)
  have key : ∀ (K' : Type) [Field K'] (x : Sp K' ⟶ Sp K₀), ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (s : Sp Ω ⟶ Sp K) (N : Type) (_ : Monoid N) (P : (Over.mk s ⟶ Q.A) →* N) (R : (Over.mk x ⟶ A₀) →* N),
      Function.Bijective P ∧ Function.Injective R ∧
      ∀ a, P ((Over.homMk s (by simp) : Over.mk s ⟶ Out.baseOver _) ≫ t.pt a) =
        R ((Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver _) ≫ pt₀ a) := by
    intro K' _ x
    obtain ⟨x', rfl⟩ := Spec.map_surjective x
    obtain ⟨Ω, _, _, j, j', hj⟩ := GlobalTheory.exists_algClosed_join_of_two_field_extensions K₀ K K' i x'.hom
    have hc : spMap j' ≫ Spec.map x' = spMap j ≫ spMap i := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext hj.symm
    let V : Over.mk ((Over.mk (spMap j)).hom ≫ spMap i) ⟶ Over.mk (Spec.map x') := Over.homMk (spMap j') hc
    haveI : Epi V.left := epi_spMap j'
    refine ⟨Ω, inferInstance, inferInstance, spMap j, _, inferInstance, pushHom hp (Over.mk (spMap j)), preHom V,
      pushHom_bijective hp _, preHom_injective V, fun a => ?_⟩
    apply Over.OverMorphism.ext
    show (spMap j ≫ (t.pt a).left) ≫ φ = spMap j' ≫ Spec.map x' ≫ (pt₀ a).left
    rw [Category.assoc, hpt, ← Category.assoc, ← hc, Category.assoc]
  refine ⟨{ pt := pt₀, prim := ?_, torsion := fun a => ?_, indep := ?_, span := ?_, pairing := fun a a' => ?_ }⟩
  · exact (isPrimitiveRoot_unitOn_iff _ _).2 (((isPrimitiveRoot_unitOn_iff _ _).1 t.prim).of_map_of_injective
      (Units.map_injective i.injective))
  · apply preHom_injective U
    rw [map_pow, ← hU, ← map_pow, t.torsion, map_one, map_one]
  · intro K' _ _ x c c' hc
    obtain ⟨Ω, _, _, s, N, _, P, R, hP, hR, H⟩ := key K' x
    refine t.indep Ω s c c' (hP.1 ?_)
    have := congrArg R hc
    unfold Out.linComb at this ⊢
    rw [map_prod_pow, map_prod_pow] at this ⊢
    simpa only [H] using this
  · intro K' _ _ x y₀ hy
    obtain ⟨Ω, _, _, s, N, _, P, R, hP, hR, H⟩ := key K' x
    obtain ⟨y, hy'⟩ := hP.2 (R y₀)
    obtain ⟨c, hc⟩ := t.span Ω s y (hP.1 (by rw [map_pow, hy', ← map_pow, hy, map_one, map_one]))
    refine ⟨c, hR ?_⟩
    have := (congrArg P hc).trans hy'
    unfold Out.linComb at this ⊢
    rw [map_prod_pow] at this ⊢
    simpa only [H] using this
  · haveI := hab.comm
    have h₁ := (GlobalTheory.weilIs_grpPullback_of_comm _ _ A₀ Q.A (spMap i) φ L₀ Q.L hL Q.isLB hp hw _ k (t.pt a) (t.pt a')
      (U ≫ pt₀ a) (U ≫ pt₀ a') _ (hpt a).symm (hpt a').symm).1 (t.pairing a a')
    rw [unitOn_zpow] at h₁ ⊢
    refine (GlobalTheory.T.weilPairing_fieldExtension_iff _ A₀ K₀ K i (𝟙 _) L₀ k (pt₀ a) (pt₀ a') _ hab hL).1 ?_
    rw [map_zpow]
    exact (weilIs_congr (by simp) L₀ k _ _ _ _ rfl rfl _).1 h₁

theorem exists_fg_subalgebra {o K : Type} [CommRing o] [Field K] (β : o →+* K) (s : Finset K) :
    letI : Algebra o (gen β s) := (β.codRestrict _ (mem_gen β s)).toAlgebra
    ∃ R₀ : Subalgebra o (gen β s), R₀.FG ∧ ∀ x : gen β s, ∃ a ∈ R₀, ∃ b ∈ R₀, x = a / b := by
  letI : Algebra o (gen β s) := (β.codRestrict _ (mem_gen β s)).toAlgebra
  let s₀ : Set (gen β s) := (gen β s).subtype ⁻¹' (s : Set K)
  have hfin : s₀.Finite := s.finite_toSet.preimage (gen β s).subtype.injective.injOn
  refine ⟨Algebra.adjoin o s₀, Subalgebra.fg_def.2 ⟨s₀, hfin, rfl⟩, fun x => ?_⟩
  have hle : Subring.closure (Set.range β ∪ (s : Set K)) ≤
      (Algebra.adjoin o s₀).toSubring.map (gen β s).subtype := by
    refine Subring.closure_le.2 ?_
    rintro y (⟨a, rfl⟩ | hy)
    · exact ⟨algebraMap o _ a, Subalgebra.algebraMap_mem _ a, rfl⟩
    · exact ⟨⟨y, subset_gen β le_rfl hy⟩, Algebra.subset_adjoin hy, rfl⟩
  obtain ⟨a, ha, b, hb, e⟩ := Subfield.mem_closure_iff.1 x.2
  obtain ⟨a, ha', rfl⟩ := hle ha
  obtain ⟨b, hb', rfl⟩ := hle hb
  exact ⟨a, ha', b, hb', Subtype.ext e.symm⟩

theorem descends_to_fg_field : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Q : Out.PolAV (Sp Ω)) (M : ℕ) (ze : oˣ), (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) → Nonempty (Out.Level Q M (unitOn (Units.map (algebraMap o Ω).toMonoidHom ze))) → ∃ (Ω₀ : Type) (_ : Field Ω₀) (_ : Algebra o Ω₀) (j : Ω₀ →ₐ[o] Ω) (R₀ : Subalgebra o Ω₀) (Q₀ : Out.PolAV (Sp Ω₀)) (φ : Q.A.left ⟶ Q₀.A.left), R₀.FG ∧ (∀ x : Ω₀, ∃ a ∈ R₀, ∃ b ∈ R₀, x = a / b) ∧ Q₀.g = Q.g ∧ IsGrpPullback Q.A Q₀.A (spMap j.toRingHom) φ ∧ (letI := Q₀.isAb.comm; GlobalTheory.ZH.HypS Q₀.A Q₀.L) ∧ Nonempty (Out.Level Q₀ M (unitOn (Units.map (algebraMap o Ω₀).toMonoidHom ze))) := by
  intro o K _ _ _ t M ze ⟨w, wd, hw, hwd, hsum, hpol, hadj⟩ ⟨lev⟩
  classical
  let β : o →+* K := algebraMap o K
  let act : Bool → (t.A ⟶ t.A) := fun j => cond j w wd
  obtain ⟨s₀, H₀⟩ := GlobalTheory.T.exists_finset_isProjOver_descends_to_subfield K (gen β ∅) t.A.left t.A.hom (GlobalTheory.ProjSpace.isProjOver_of_relAmple t.ample)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ (gen β s₀) (gen_mono β (Finset.empty_subset _)) (subset_gen β le_rfl)
  have : IsProper p₀ := isProper_of_isProjOver hp₀
  have : LocallyOfFinitePresentation p₀ := inferInstance
  have : QuasiCompact (Over.mk p₀).hom := inferInstanceAs (QuasiCompact p₀)
  have : QuasiSeparated (Over.mk p₀).hom := inferInstanceAs (QuasiSeparated p₀)
  have : LocallyOfFinitePresentation (Over.mk p₀).hom := inferInstanceAs (LocallyOfFinitePresentation p₀)
  obtain ⟨s₁, H₁⟩ := GlobalTheory.grpObj_descends_to_large_subfield K (gen β s₀) (Over.mk p₀) t.A φ sq
  obtain ⟨s₂, H₂⟩ := GlobalTheory.T.exists_lineBundle_descent_to_subfield K (gen β s₀) X₀ t.A.left p₀ t.A.hom φ t.L t.isLB sq
  obtain ⟨s₃, H₃⟩ := GlobalTheory.T.exists_descent_of_morphisms_to_subfield K (gen β s₀) X₀ t.A.left p₀ t.A.hom φ X₀ p₀ Bool (fun j => (act j).left ≫ φ) sq
    (fun j => by rw [Category.assoc, sq.w, ← Category.assoc, Over.w])
  obtain ⟨s₄, H₄⟩ := GlobalTheory.T.exists_descent_of_morphisms_to_subfield K (gen β s₀) (Sp (gen β s₀)) (Sp K) (𝟙 _) (𝟙 _) (spMap (gen β s₀).subtype) X₀ p₀
    (Fin (2 * t.g)) (fun a => (lev.pt a).left ≫ φ) (IsPullback.of_vert_isIso ⟨by simp⟩)
    (fun a => by
      have e : (lev.pt a).left ≫ t.A.hom = 𝟙 _ := Over.w (lev.pt a)
      rw [Category.assoc, sq.w, ← Category.assoc, e]; simp)
  let s : Finset K := s₀ ∪ s₁ ∪ s₂ ∪ s₃ ∪ s₄
  have h : gen β s₀ ≤ gen β s := gen_mono β (fun x hx => by simp [s, hx])
  let inc := spMap (Subfield.inclusion h)
  let A₁ : Over (Sp (gen β s)) := Over.mk (pullback.snd p₀ inc)
  let φ₁ : A₁.left ⟶ X₀ := pullback.fst p₀ inc
  have sq₁ : IsPullback φ₁ A₁.hom p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : t.A.left ⟶ A₁.left := sq₁.lift φ (t.A.hom ≫ spMap (gen β s).subtype)
    (by rw [Category.assoc, spMap_subtype h, sq.w])
  have hψ₁ : ψ ≫ φ₁ = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = t.A.hom ≫ spMap (gen β s).subtype := sq₁.lift_snd _ _ _
  obtain ⟨gr₁, hG⟩ := H₁ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁ φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨L₁, hL₁, hL⟩ := H₂ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨f₁, hf₁⟩ := H₃ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨x₁, hx₁⟩ := H₄ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) (Sp (gen β s)) (𝟙 _) inc
    (spMap (gen β s).subtype) (IsPullback.of_vert_isIso ⟨by simp [inc]⟩) (spMap_subtype h) (by simp)
  let act₁ : Bool → (A₁ ⟶ A₁) := fun j =>
    Over.homMk (sq₁.lift (f₁ j) A₁.hom (by rw [(hf₁ j).2, sq₁.w])) (sq₁.lift_snd _ _ _)
  let pt₁ : Fin (2 * t.g) → (Out.baseOver (Sp (gen β s)) ⟶ A₁) := fun a =>
    Over.homMk (sq₁.lift (x₁ a) (𝟙 _) (by rw [(hx₁ a).2]; simp)) (sq₁.lift_snd _ _ _)
  have hpt : ∀ a, (lev.pt a).left ≫ ψ = spMap (gen β s).subtype ≫ (pt₁ a).left := fun a => by
    have e : (lev.pt a).left ≫ t.A.hom = 𝟙 _ := Over.w (lev.pt a)
    have e₁ : (pt₁ a).left ≫ φ₁ = x₁ a := sq₁.lift_fst _ _ _
    have e₂ : (pt₁ a).left ≫ A₁.hom = 𝟙 _ := sq₁.lift_snd _ _ _
    apply sq₁.hom_ext
    · rw [Category.assoc, hψ₁]
      exact ((hx₁ a).1.symm.trans (congrArg _ e₁.symm)).trans (Category.assoc _ _ _).symm
    · rw [Category.assoc, hψ₂, ← Category.assoc, e]
      refine (Category.id_comp _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      exact ((congrArg _ e₂).trans (Category.comp_id _)).symm
  have hact : ∀ j, (act j).left ≫ ψ = ψ ≫ (act₁ j).left := fun j => by
    have e₁ : (act₁ j).left ≫ φ₁ = f₁ j := sq₁.lift_fst _ _ _
    apply sq₁.hom_ext
    · rw [Category.assoc, hψ₁, Category.assoc, e₁, (hf₁ j).1]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hψ₂]
  obtain ⟨hab, hdim⟩ := GlobalTheory.T.abelian_scheme_descent_smooth_dimension _ K (gen β s).subtype A₁ t.A ψ hG t.isAb
  obtain ⟨hr, hs, hk⟩ := GlobalTheory.T.rigidified_symmetric_kernelTrivial_descend_fieldExt _ K (gen β s).subtype A₁ t.A ψ L₁ t.L hab hG hL₁ t.isLB hL
  have hamp := GlobalTheory.AmpleDescent.relAmple_of_fieldExtension _ K (gen β s).subtype A₁ t.A ψ L₁ t.L hab hG hL₁ t.isLB hL
    t.ample
  letI : Algebra o (gen β s) := (β.codRestrict _ (mem_gen β s)).toAlgebra
  obtain ⟨R₀, hfg, hfrac⟩ := exists_fg_subalgebra β s
  refine ⟨gen β s, inferInstance, inferInstance, ⟨(gen β s).subtype, fun _ => rfl⟩, R₀,
    ⟨A₁, hab, t.g, hdim _ t.smoothDim, L₁, hL₁, hr t.rigid, hs t.sym, hamp, hk t.ktriv⟩, ψ, hfg, hfrac, rfl, hG, ?_, ?_⟩
  · have := t.isAb.comm
    have := hab.comm
    exact hypS_descend (gen β s).subtype hab hG hL₁ t.isLB hL (hact true).symm (hact false).symm hw hwd hsum hpol hadj
  · exact level_descend (gen β s).subtype t A₁ hab _ L₁ hL₁ _ _ _ _ hG hL M _ lev pt₁ hpt

end GlobalTheory.SymLevelDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQuotientAbelianByFinitePoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory

namespace FiniteQuot

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]

lemma translHom_eq (c : 𝟙_ (Over (Sp K)) ⟶ A) : (transl c).hom = (toUnit A ≫ c) * 𝟙 A := rfl

lemma comp_translHom {Z : Over (Sp K)} (g : Z ⟶ A) (c : 𝟙_ (Over (Sp K)) ⟶ A) :
    g ≫ (transl c).hom = (toUnit Z ≫ c) * g := by
  rw [translHom_eq, MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]

lemma translHom_one : (transl (1 : 𝟙_ (Over (Sp K)) ⟶ A)).hom = 𝟙 A := by
  rw [translHom_eq, MonObj.comp_one, _root_.one_mul]

lemma translHom_mul (a c : 𝟙_ (Over (Sp K)) ⟶ A) :
    (transl (a * c)).hom = (transl a).hom ≫ (transl c).hom := by
  rw [comp_translHom, translHom_eq, translHom_eq, MonObj.comp_mul, ← _root_.mul_assoc,
    _root_.mul_comm (toUnit A ≫ c)]

end FiniteQuot


open FiniteQuot PointQuot AbelianQuotient in
theorem exists_quotient_abelian_by_finite_points :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ C : Subgroup (𝟙_ (Over (Sp k)) ⟶ A), Finite C → ∃ (B : Over (Sp k)) (_ : GrpObj B) (ψ : A ⟶ B), IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (t : Sp k' ⟶ Sp k) (x : Over.mk t ⟶ A), x ≫ ψ = 1 ↔ ∃ c ∈ C, x = toUnit _ ≫ c := by
  open FiniteQuot PointQuot in
  intro k _ _ A _ hA C hC
  have := hA.comm
  have hq : IsQProjOver A.hom := by
    obtain ⟨N, i, hi, e⟩ := (ProjSpace.isProjBy_iff_isProjOver A.hom).1
      (AbelianProjective.isProjBy_of_isAbelianScheme k A hA)
    exact ⟨N, i, inferInstance, inferInstance, e⟩
  obtain ⟨Y, π, sY, hw, hG, hsep, hlft, -⟩ :=
    ZM.exists_isGaloisCover_of_isQProjOver k A.left A.hom C (fun c => ((transl c.1).hom).left) hq
      (congrArg CommaMorphism.left (translHom_one (A := A)))
      (fun a c => congrArg CommaMorphism.left (translHom_mul a.1 c.1))
      (fun a => Over.w _) (by
        intro K _ _ y a h
        let y' : Over.mk (y ≫ A.hom) ⟶ A := Over.homMk y rfl
        have h' : y' ≫ (transl a.1).hom = y' := Over.OverMorphism.ext h
        have : Nonempty (Over.mk (y ≫ A.hom)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
        have := epi_toUnit (Over.mk (y ≫ A.hom))
        rw [comp_translHom, mul_eq_right, ← MonObj.comp_one (toUnit _), cancel_epi] at h'
        exact Subtype.ext h')
  let B : Over (Sp k) := Over.mk sY
  let q : A ⟶ B := Over.homMk π hw
  have hfin : IsFinite q.left := hG.fin
  have het : Etale q.left := hG.etale
  have hsurj : Surjective q.left := hG.onto
  have hinv : ∀ c : C, (transl c.1).hom ≫ q = q := fun c => Over.OverMorphism.ext (hG.inv c)
  let x : C → (𝟙_ (Over (Sp k)) ⟶ A) := Subtype.val
  have hmono := mono_constDesc x Subtype.val_injective
  obtain ⟨_, hi⟩ := exists_grpObj_constObj x C Subtype.range_coe
  obtain ⟨_, hcomm, hhom, -⟩ := grpObj_of_flat_coset_quotient _ A _ B (constDesc x) q hi hmono
    inferInstance hsurj inferInstance (by
      intro Z g g'
      constructor
      · intro h
        obtain ⟨t, ht⟩ := exists_lift x (g' / g) fun z => by
          obtain ⟨V, a, hV, e⟩ :=
            hG.exists_local_geom g.left g'.left (congrArg CommaMorphism.left h) z
          have e' : openι Z V ≫ g ≫ (transl a.1).hom = openι Z V ≫ g' := Over.OverMorphism.ext e
          refine ⟨V, hV, a, ?_⟩
          rw [GrpObj.comp_div, ← e', ← Category.assoc, comp_translHom, mul_div_cancel_right]
        exact ⟨t, by rw [ht, div_mul_cancel]⟩
      · rintro ⟨t, rfl⟩
        refine hom_ext_local _ _ fun z => ?_
        obtain ⟨V, hV, c, hc⟩ := locally_const_desc x t z
        refine ⟨V, hV, ?_⟩
        rw [← Category.assoc _ (_ * _), MonObj.comp_mul, hc, ← comp_translHom, Category.assoc,
          Category.assoc, hinv])
  refine ⟨B, inferInstance, q, ?_, hhom, hfin, het, hsurj, fun K _ _ t y => ⟨fun hy => ?_, ?_⟩⟩
  · have hw' : q.left ≫ B.hom = A.hom := Over.w q
    have := hA.smooth
    have := hA.proper
    have := hA.geomConnected
    have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth
      hA.geomConnected
    have : IsSeparated B.hom := hsep
    have : LocallyOfFiniteType B.hom := hlft
    have : UniversallyClosed (q.left ≫ B.hom) := by rw [hw']; infer_instance
    have : GeometricallyReduced (q.left ≫ B.hom) := by rw [hw']; infer_instance
    have : GeometricallyConnected (q.left ≫ B.hom) := by rw [hw']; infer_instance
    have := UniversallyClosed.of_comp_surjective q.left B.hom
    have := AbelianQuotient.geometricallyReduced_of_comp q.left B.hom
    have : LocallyOfFinitePresentation B.hom := inferInstance
    exact ⟨hcomm, AbelianQuotient.smooth_of_grpObj_of_flat B, ⟨⟩, AbelianQuotient.geometricallyConnected_of_comp q.left B.hom⟩
  · have h1 : (1 : Over.mk t ⟶ A) ≫ q = y ≫ q := by rw [hy, MonObj.one_comp]
    obtain ⟨a, ha, -⟩ := hG.fibre K (1 : Over.mk t ⟶ A).left y.left
      (congrArg CommaMorphism.left h1)
    have ha' : (1 : Over.mk t ⟶ A) ≫ (transl a.1).hom = y := Over.OverMorphism.ext ha
    exact ⟨a.1, a.2, by rw [← ha', comp_translHom, _root_.mul_one]⟩
  · rintro ⟨c, hc, rfl⟩
    rw [← _root_.mul_one (toUnit _ ≫ c), ← comp_translHom, Category.assoc, hinv ⟨c, hc⟩,
      MonObj.one_comp]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionPowerCalculusGeometricFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionPowerCalculusGeometricFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.Calc
open GlobalTheory.FrameGen GlobalTheory.ConstFam

variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L' : LB G'.left}
  {L : LB G.left} {w : LB.Iso L' (L.pull φ)} {k : ℕ} {T' : Over S'} {T T₁ : Over S}

theorem prod_ext' {Z : Scheme.{0}} {a b : Z ⟶ (T ⊗ G).left} (h₁ : a ≫ (fst T G).left = b ≫ (fst T G).left)
    (h₂ : a ≫ (snd T G).left = b ≫ (snd T G).left) : a = b := pullback.hom_ext h₁ h₂

theorem exists_lift {Z : Scheme.{0}} (a : Z ⟶ T.left) (b : Z ⟶ G.left) (e : a ≫ T.hom = b ≫ G.hom) :
    ∃ H : Z ⟶ (T ⊗ G).left, H ≫ (fst T G).left = a ∧ H ≫ (snd T G).left = b :=
  ⟨pullback.lift a b e, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem prod_w : (fst T G).left ≫ T.hom = (snd T G).left ≫ G.hom := (Over.w _).trans (Over.w _).symm

theorem exists_prod (hφ : φ ≫ G.hom = G'.hom ≫ f) {h : T'.left ⟶ T.left} (hh : h ≫ T.hom = T'.hom ≫ f) :
    ∃ H : (T' ⊗ G').left ⟶ (T ⊗ G).left, H ≫ (fst T G).left = (fst T' G').left ≫ h ∧
      H ≫ (snd T G).left = (snd T' G').left ≫ φ :=
  exists_lift _ _ (by rw [Category.assoc, Category.assoc, hh, hφ, ← Category.assoc, ← Category.assoc, prod_w])

theorem thru_sv {h : T'.left ⟶ T.left} {s : LB.Sec (LPow G L (k : ℤ) T)} {s' : LB.Sec (LPow G' L' (k : ℤ) T')}
    (H : Thru w k h s s') {Z : Scheme.{0}} (r' : Z ⟶ (T' ⊗ G').left) (r : Z ⟶ (T ⊗ G).left)
    (h₁ : r ≫ (fst T G).left = r' ≫ (fst T' G').left ≫ h) (h₂ : r ≫ (snd T G).left = r' ≫ (snd T' G').left ≫ φ)
    (z : Z) {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    sv G L k s r z J = (wVal w z J J' (r' ≫ (snd T' G').left) ^ k).val * sv G' L' k s' r' z J' := by
  rw [Units.val_pow_eq_pow_val]
  exact H Z r' r h₁ h₂ z J J' hJ hJ'

theorem existsUnique_thru (hφ : φ ≫ G.hom = G'.hom ≫ f) (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB)
    {h : T'.left ⟶ T.left} (hh : h ≫ T.hom = T'.hom ≫ f) (s : LB.Sec (LPow G L (k : ℤ) T)) :
    ∃! t : LB.Sec (LPow G' L' (k : ℤ) T'), Thru w k h s t := by
  obtain ⟨H, h₁, h₂⟩ := exists_prod hφ hh
  obtain ⟨t, ht⟩ := exists_secThrough (φ' := fun _ : Fin 1 => (snd T' G').left)
    (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (k : ℤ)) (h := H) hw hL hL' (fun _ => h₂.symm) s
  have key : Thru w k h s t := fun Z r' r e₁ e₂ z J J' hJ hJ' => by
    obtain rfl : r = r' ≫ H := prod_ext' (by rw [Category.assoc, h₁, e₁]) (by rw [Category.assoc, h₂, e₂])
    have a := ht.sval (fun _ => h₂.symm) r' hJ hJ'
    rwa [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val] at a
  refine ⟨t, key, fun t' ht' => SecOps.sec_ext (sec_ext_val hL' fun y J' hJ' => ?_)⟩
  obtain ⟨J, hJ⟩ := exists_good' hL y
  have e₁ : H ≫ (fst T G).left = 𝟙 _ ≫ (fst T' G').left ≫ h := by rw [Category.id_comp, h₁]
  have e₂ : H ≫ (snd T G).left = 𝟙 _ ≫ (snd T' G').left ≫ φ := by rw [Category.id_comp, h₂]
  exact (Units.mul_right_inj _).1 ((thru_sv ht' _ H e₁ e₂ y hJ hJ').symm.trans (thru_sv key _ H e₁ e₂ y hJ hJ'))

theorem cmb_iff (hL : L.IsLB) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (k : ℤ) T)) (a : Fin n → Γ(T.left, ⊤))
    (t : LB.Sec (LPow G L (k : ℤ) T)) :
    ((∀ j, t.f j = ∑ i, liftFun G _ (a i) * (b i).f j) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ G).left) (z : Z) (J), Good L z J →
      sv G L k t r z J = ∑ i, gT (r ≫ (fst T G).left) z (a i) * sv G L k (b i) r z J) ∧
    ((∀ (z : (T ⊗ G).left) (J), Good L z J →
      sv G L k t (𝟙 _) z J = ∑ i, gT (𝟙 _ ≫ (fst T G).left) z (a i) * sv G L k (b i) (𝟙 _) z J) →
      ∀ j, t.f j = ∑ i, liftFun G _ (a i) * (b i).f j) := by
  have key : ∀ t : LB.Sec (LPow G L (k : ℤ) T), (∀ j, t.f j = ∑ i, liftFun G _ (a i) * (b i).f j) →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ G).left) (z : Z) (J), Good L z J →
      sv G L k t r z J = ∑ i, gT (r ≫ (fst T G).left) z (a i) * sv G L k (b i) r z J := fun t H Z r z J hJ =>
    (SectionScalarValuation.sval_lin (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (k : ℤ)) (s := t)
      (fun i => (fst T G).left.appTop.hom (a i)) b H r z hJ).trans
      (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ((gs_top _ _ _).trans (gT_comp _ _ _ _)) rfl)
  refine ⟨key t, fun H j => ?_⟩
  let σ := SectionLimit.linSec (fun i => (fst T G).left.appTop.hom (a i)) b
  exact sec_ext_val (s := t) (s' := σ) hL (fun y J hJ => (H y J hJ).trans (key σ (fun _ => rfl) _ _ y J hJ).symm) j

theorem cmb_of_lin (hφ : φ ≫ G.hom = G'.hom ≫ f) (hL : L.IsLB) (hL' : L'.IsLB) {g : T'.left ⟶ T₁.left}
    (hg : g ≫ T₁.hom = T'.hom ≫ f) {h : T₁ ⟶ T} {p : T'.left ⟶ T.left} (hp : p = g ≫ h.left) {n : ℕ}
    {b : Fin n → LB.Sec (LPow G L (k : ℤ) T)} {c : Fin n → Γ(T₁.left, ⊤)} {s : LB.Sec (LPow G L (k : ℤ) T₁)}
    {b' : Fin n → LB.Sec (LPow G' L' (k : ℤ) T')} {t : LB.Sec (LPow G' L' (k : ℤ) T')} (hl : Lin G L k h b c s)
    (hb : ∀ i, Thru w k p (b i) (b' i)) (ht : Thru w k g s t) :
    ∀ j, t.f j = ∑ i, liftFun G' _ (g.appTop.hom (c i)) * (b' i).f j := by
  subst hp
  refine (cmb_iff hL' b' _ t).2 fun z J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' hL z
  obtain ⟨H, h₁, h₂⟩ := exists_prod hφ hg
  have e := lin_all hL hl H z hJ
  rw [thru_sv ht (𝟙 _) H (by rw [Category.id_comp, h₁]) (by rw [Category.id_comp, h₂]) z hJ hJ'] at e
  refine (Units.mul_right_inj _).1 (e.trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [thru_sv (hb i) (𝟙 _) (H ≫ (h ▷ G).left)
    (by rw [Category.id_comp, Category.assoc, wh_fst, ← Category.assoc, h₁, Category.assoc])
    (by rw [Category.id_comp, Category.assoc, wh_snd, h₂]) z hJ hJ', gT_comp, h₁, Category.id_comp,
    Category.id_comp, mul_left_comm]

theorem exists_thru_up (hφ : IsPullback φ G'.hom G.hom f) (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB)
    {g : T'.left ⟶ T₁.left} {p : T₁.left ⟶ T'.left} (hg : g ≫ T₁.hom = T'.hom ≫ f) (gp : g ≫ p = 𝟙 _) (pg : p ≫ g = 𝟙 _) :
    ∃ H : (T₁ ⊗ G).left ⟶ (T' ⊗ G').left, H ≫ (fst T' G').left ≫ g = (fst T₁ G).left ∧
      H ≫ (snd T' G').left ≫ φ = (snd T₁ G).left ∧
      ∀ t : LB.Sec (LPow G' L' (k : ℤ) T'), ∃ s : LB.Sec (LPow G L (k : ℤ) T₁), Thru w k g s t := by
  have hp : (snd T₁ G).left ≫ G.hom = (((fst T₁ G).left ≫ p) ≫ T'.hom) ≫ f := by
    rw [Category.assoc, ← hg, Category.assoc, ← Category.assoc p, pg, Category.id_comp, prod_w]
  obtain ⟨H, h₁, h₂⟩ := exists_lift (T := T') (G := G') ((fst T₁ G).left ≫ p) (hφ.lift _ _ hp) (hφ.lift_snd _ _ hp).symm
  have h₃ : H ≫ (snd T' G').left ≫ φ = (snd T₁ G).left := by rw [← Category.assoc, h₂, hφ.lift_fst]
  refine ⟨H, by rw [← Category.assoc, h₁, Category.assoc, pg, Category.comp_id], h₃, fun t => ?_⟩
  obtain ⟨t₁, ht₁⟩ := exists_sec_up (φ' := fun _ : Fin 1 => (snd T' G').left) (ε := fun _ => (k : ℤ))
    ((isGen_iff w).1 hw) hL hL' t
  obtain ⟨s, -, hs⟩ := SectionLimit.exists_pull t₁ H (fun _ : Fin 1 => (snd T₁ G).left) (fun _ => h₃)
  refine ⟨s, fun Z r' r e₁ e₂ z J J' hJ hJ' => ?_⟩
  have e₁' : r ≫ H ≫ (fst T' G').left = r' ≫ (fst T' G').left := by
    rw [h₁, ← Category.assoc, e₁, Category.assoc, Category.assoc, gp, Category.comp_id]
  have e : r ≫ H = r' := prod_ext' (by rw [Category.assoc, e₁']) (hφ.hom_ext
    (by rw [Category.assoc, Category.assoc, h₃, e₂, Category.assoc])
    (by rw [Category.assoc, Category.assoc, Category.assoc, ← prod_w, ← Category.assoc H, ← Category.assoc, e₁',
      Category.assoc]))
  have ST : SecThrough w (fun _ : Fin 1 => (snd T' G').left) (fun _ => (snd T' G').left ≫ φ) (fun _ => (k : ℤ)) t t₁
      (𝟙 _) := fun Z r z p q hp hq => by
    rw [Category.comp_id]
    exact ht₁ Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)
  have a := ST.sval (fun _ => (Category.id_comp _).symm) r' hJ hJ'
  rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val, Category.comp_id] at a
  exact (hs Z r z J hJ).trans ((congrArg (fun q => sval t₁ q z J) e).trans a)

theorem basis_thru (hφ : IsPullback φ G'.hom G.hom f) (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB)
    {g : T'.left ⟶ T₁.left} {p : T₁.left ⟶ T'.left} (hg : g ≫ T₁.hom = T'.hom ≫ f) (gp : g ≫ p = 𝟙 _) (pg : p ≫ g = 𝟙 _)
    {h : T₁ ⟶ T} {q : T'.left ⟶ T.left} (hq : q = g ≫ h.left) {n : ℕ}
    {b : Fin n → LB.Sec (LPow G L (k : ℤ) T)} {b' : Fin n → LB.Sec (LPow G' L' (k : ℤ) T')}
    (hB : BasisAlong G L k h b) (hb : ∀ i, Thru w k q (b i) (b' i)) (t : LB.Sec (LPow G' L' (k : ℤ) T')) :
    ∃! c : Fin n → Γ(T₁.left, ⊤), ∀ j, t.f j = ∑ i, liftFun G' _ (g.appTop.hom (c i)) * (b' i).f j := by
  obtain ⟨H, h₁, h₃, hs⟩ := exists_thru_up (k := k) hφ hw hL hL' hg gp pg
  obtain ⟨s, hst⟩ := hs t
  obtain ⟨c, hc, hu⟩ := hB s
  refine ⟨c, cmb_of_lin hφ.w hL hL' hg hq hc hb hst, fun c' hc' => hu c' fun z J hJ => ?_⟩
  subst hq
  obtain ⟨J', hJ'⟩ := exists_good' hL' z
  have a := thru_sv hst H (𝟙 _) ((Category.id_comp _).trans h₁.symm) ((Category.id_comp _).trans h₃.symm) z hJ hJ'
  refine a.trans ?_
  rw [(cmb_iff hL' b' _ t).1 hc' _ H z J' hJ', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have d := thru_sv (hb i) H (h ▷ G).left (by rw [wh_fst, ← h₁]; simp only [Category.assoc]) (by rw [wh_snd, h₃]) z hJ hJ'
  rw [mul_left_comm, ← d, gT_comp, Category.assoc, h₁]
  exact congrArg₂ (· * ·) (gs_top _ _ _).symm rfl

theorem appTop_fnR {R F : Type} [CommRing R] [CommRing F] (y : R →+* F) (c : R) :
    (spMap y).appTop.hom (fnR c) = fnR (y c) :=
  (congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y))).symm

theorem main : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ Z) (A : PolAV (Sp (FractionRing R))) (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)), IsGrpPullback A.A G₀ x φ → w.IsGen → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), (∀ (T : Over Z) (p : Sp F ⟶ T.left), p ≫ T.hom = jFK (R := R) F ≫ x → ∀ s : LB.Sec (LPow G₀ L₀ (k : ℤ) T), ∃! t : SecA A F k, Thru w k (T' := TFK (R := R) F) p s t) ∧ (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Z) (T : Over Z) (h : Over.mk y ⟶ T) (ga : R' →+* F), spMap ga ≫ y = jFK (R := R) F ≫ x → ∀ (n : ℕ) (b : Fin n → LB.Sec (LPow G₀ L₀ (k : ℤ) T)) (c : Fin n → R') (s : LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk y))) (bF : Fin n → SecA A F k) (t : SecA A F k), Lin G₀ L₀ k h b (fun i => fnR (c i)) s → (∀ i, Thru w k (T' := TFK (R := R) F) (spMap ga ≫ h.left) (b i) (bF i)) → Thru w k (T' := TFK (R := R) F) (T := Over.mk y) (spMap ga) s t → Cmb bF (fun i => ga (c i)) t) ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ Z) (ga : K →+* F), spMap ga ≫ y = jFK (R := R) F ≫ x → ∀ (n : ℕ) (τ : Fin n → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk y))) (τF : Fin n → SecA A F k), AllBasis G₀ L₀ k y τ → (∀ i, Thru w k (T' := TFK (R := R) F) (T := Over.mk y) (spMap ga) (τ i) (τF i)) → ∀ t : SecA A F k, ∃! a : Fin n → F, Cmb τF a t := by
  intro Z G₀ _ L₀ hL R _ _ x A φ w gp hw F _ _ k
  refine ⟨fun T p hp s => existsUnique_thru (T' := TFK (R := R) F) gp.1.w hw hL A.isLB hp s,
    fun R' _ y T h ga e n b c s bF t hl hb ht j => ?_, fun K _ y ga e n τ τF hB hτ t => ?_⟩
  · have := cmb_of_lin (T' := TFK (R := R) F) (T₁ := Over.mk y) (g := spMap ga) gp.1.w hL A.isLB e rfl hl hb ht j
    exact this.trans (Finset.sum_congr rfl fun i _ =>
      congrArg (fun q => liftFun A.A _ q * (bF i).f j) (appTop_fnR ga (c i)))
  · obtain ⟨c, hc, hu⟩ := basis_thru (T' := TFK (R := R) F) (T₁ := Over.mk (jFK (R := R) F ≫ x)) (g := 𝟙 (Sp F))
      (p := 𝟙 (Sp F)) gp.1 hw hL A.isLB (Category.id_comp _) (Category.id_comp _) (Category.id_comp _)
      (Category.id_comp _).symm (hB F ga _ e) hτ t
    let ε := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.symm
    refine ⟨fun i => ε.symm (c i), fun j => (hc j).trans (Finset.sum_congr rfl fun i _ => ?_), fun a ha => funext fun i => ?_⟩
    · exact congrArg (fun q => liftFun A.A _ q * (τF i).f j) (ε.apply_symm_apply (c i)).symm
    · exact ε.eq_symm_apply.2 (congrFun (hu (fun i => ε (a i)) ha) i)

end GlobalTheory.OneBasis.Calc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionPowerCalculusGeometricFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionPower_calculus_geometric_fibre : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ Z) (A : PolAV (Sp (FractionRing R))) (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)), IsGrpPullback A.A G₀ x φ → w.IsGen → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), (∀ (T : Over Z) (p : Sp F ⟶ T.left), p ≫ T.hom = jFK (R := R) F ≫ x → ∀ s : LB.Sec (LPow G₀ L₀ (k : ℤ) T), ∃! t : SecA A F k, Thru w k (T' := TFK (R := R) F) p s t) ∧ (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Z) (T : Over Z) (h : Over.mk y ⟶ T) (ga : R' →+* F), spMap ga ≫ y = jFK (R := R) F ≫ x → ∀ (n : ℕ) (b : Fin n → LB.Sec (LPow G₀ L₀ (k : ℤ) T)) (c : Fin n → R') (s : LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk y))) (bF : Fin n → SecA A F k) (t : SecA A F k), Lin G₀ L₀ k h b (fun i => fnR (c i)) s → (∀ i, Thru w k (T' := TFK (R := R) F) (spMap ga ≫ h.left) (b i) (bF i)) → Thru w k (T' := TFK (R := R) F) (T := Over.mk y) (spMap ga) s t → Cmb bF (fun i => ga (c i)) t) ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ Z) (ga : K →+* F), spMap ga ≫ y = jFK (R := R) F ≫ x → ∀ (n : ℕ) (τ : Fin n → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk y))) (τF : Fin n → SecA A F k), AllBasis G₀ L₀ k y τ → (∀ i, Thru w k (T' := TFK (R := R) F) (T := Over.mk y) (spMap ga) (τ i) (τF i)) → ∀ t : SecA A F k, ∃! a : Fin n → F, Cmb τF a t := by
  first | exact @GlobalTheory.OneBasis.Calc.main | exact GlobalTheory.OneBasis.Calc.main | (intros; apply GlobalTheory.OneBasis.Calc.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniversalSectionBasisPolarisedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniversalSectionBasisPolarisedFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

noncomputable section
namespace GlobalTheory.Ex.OneGen

theorem existsUnique_smul_of_basis {R M κ : Type} [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton κ]
    (c : Module.Basis κ R M) (k : κ) (s : M) : ∃! r : R, s = r • c k := by
  have := uniqueOfSubsingleton k
  obtain rfl : k = default := Subsingleton.elim _ _
  refine ⟨c.repr s default, ?_, fun r hr => ?_⟩
  · have e := c.sum_repr s
    rw [Fintype.sum_unique] at e
    exact e.symm
  · rw [hr]; simp

theorem exists_univBasis_field (hS : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K]
    (y : Sp K ⟶ S) : ∃ b : SecM P.A P.L ((1 : ℕ) : ℤ) (Over.mk y), ∀ (T : Over S) [IsAffine T.left] (h : T ⟶ Over.mk y)
      (s : SecM P.A P.L ((1 : ℕ) : ℤ) T), ∃! c : Γ(T.left, ⊤), s = c • VVRank.pullM P.A P.L _ h b := by
  obtain ⟨V, hV, b, hb⟩ := ThetaReal.exists_univBasis hS P 1 le_rfl (y (closedPoint K))
  have hr : Set.range y ⊆ Set.range V.ι := by
    rintro _ ⟨q, rfl⟩
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    rw [Subsingleton.elim q (closedPoint K)]
    exact ⟨⟨_, hV⟩, rfl⟩
  let u : Over.mk y ⟶ overRes (T := baseOver S) V := Over.homMk (IsOpenImmersion.lift V.ι y hr)
    ((congrArg (_ ≫ ·) (Category.comp_id V.ι)).trans (IsOpenImmersion.lift_fac V.ι y hr))
  have h1 : 1 ^ P.g = 1 := one_pow _
  let k₀ : Fin (1 ^ P.g) := Fin.cast h1.symm 0
  have : Subsingleton (Fin (1 ^ P.g)) := ⟨fun a a' => Fin.ext (by have := a.2; have := a'.2; omega)⟩
  refine ⟨VVRank.pullM P.A P.L _ u (b k₀), fun T _ h s => ?_⟩
  obtain ⟨c, hc⟩ := hb T (h ≫ u)
  rw [VVRank.pullM_comp _ P.isLB, ← hc]
  exact existsUnique_smul_of_basis c k₀ s

theorem exists_univBasis_of_fibre : Laws2 → ∀ (S S' : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB →
    ∀ (P : PolAV S') (f : S' ⟶ S) (φ : P.A.left ⟶ G.left), IsGrpPullback P.A G f φ → LBIso P.L (L.pull φ) →
    ∀ (K : Type) [Field K] (y : Sp K ⟶ S') (x : Sp K ⟶ S), y ≫ f = x → ∃ e, UnivBasis G L x e := by
  intro hL S S' G _ L hL₀ P f φ hp hw K _ y x hx
  obtain ⟨w, hw⟩ := hw
  obtain ⟨b, hb⟩ := exists_univBasis_field hL.secBaseChangeAny P y
  have hτ : (𝟙 (Sp K) : (Over.mk y).left ⟶ (Over.mk x).left) ≫ (Over.mk x).hom = (Over.mk y).hom ≫ f :=
    (Category.id_comp _).trans hx.symm
  have : IsIso (C := Scheme.{0}) (X := (Over.mk y).left) (Y := (Over.mk x).left) (𝟙 (Sp K)) := IsIso.id _
  obtain ⟨e, he⟩ := UnivBasisMove.exists_rel_up hp (T := Over.mk y) (T₀ := Over.mk x) (𝟙 (Sp K)) hτ hw hL₀ P.isLB b
  refine ⟨SecM.toSec G e, fun K' _ i x' h s => ?_⟩
  obtain rfl : (spMap i ≫ y) ≫ f = x' := by rw [Category.assoc, hx, h]
  let T : Over S' := Over.mk (spMap i ≫ y)
  have : IsAffine T.left := inferInstanceAs (IsAffine (Spec _))
  obtain ⟨E, hE⟩ := UnivBasisMove.exists_linearEquiv hp hw hL₀ P.isLB ((1 : ℕ) : ℤ) T
  let u : T ⟶ Over.mk y := Over.homMk (spMap i) rfl
  let u₀ : Over.mk (T.hom ≫ f) ⟶ Over.mk x := Over.homMk (spMap i) h
  have key : E (VVRank.pullM G L _ u₀ e) = VVRank.pullM P.A P.L _ u b :=
    (hE _).unique_down hL₀ P.isLB (he.pull _ _ u u₀ ((Category.id_comp _).trans (Category.comp_id _).symm))
  obtain ⟨c, hc, hu⟩ := hb T u (E s)
  refine ⟨c, E.injective (hc.trans ?_), fun r hr => hu r ?_⟩
  · rw [← key]
    exact (E.map_smul c _).symm
  · rw [← key]
    exact (congrArg E hr).trans (E.map_smul r _)

end GlobalTheory.Ex.OneGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniversalSectionBasisPolarisedFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_section_basis_polarised_fibre : Laws2 → ∀ (S S' : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → ∀ (P : PolAV S') (f : S' ⟶ S) (φ : P.A.left ⟶ G.left), IsGrpPullback P.A G f φ → LBIso P.L (L.pull φ) → ∀ (K : Type) [Field K] (y : Sp K ⟶ S') (x : Sp K ⟶ S), y ≫ f = x → ∃ e, UnivBasis G L x e := by
  first | exact @GlobalTheory.Ex.OneGen.exists_univBasis_of_fibre | exact GlobalTheory.Ex.OneGen.exists_univBasis_of_fibre | (intros; apply GlobalTheory.Ex.OneGen.exists_univBasis_of_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcLiftExtensionLargerClosedField
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcLiftExtensionLargerClosedField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.LiftExt
open GlobalTheory.TorusExt GlobalTheory.ArcExt

theorem qkExt_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F F' F'' : Type} [Field F] [Field F']
    [Field F''] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] [Algebra (FractionRing R) F'']
    {f : F →+* F'} {f' : F' →+* F''} {k : ℕ} {p : QkPt D F k} {p' : QkPt D F' k} {p'' : QkPt D F'' k}
    (h : QkExt f p p') (h' : QkExt f' p' p'') : QkExt (f'.comp f) p p'' := by
  have e : spMap (f'.comp f) = spMap f' ≫ spMap f := spMap_comp' f f'
  refine ⟨h'.1.trans h.1, by rw [h'.2.1, h.2.1, e, Category.assoc], fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine (val_corr hJ (h'.2.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (h.2.2 χ) _).trans
    ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))))
  rw [e, Category.assoc]

theorem equiv_of_base {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F F' : Type} [Field F]
    [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') {k : ℕ}
    {p₀ : QkPt D (FractionRing R) k} {r : QkPt D F k}
    (h : ∀ p, QkExt (algebraMap (FractionRing R) F) p₀ p → QkPt.Equiv D F p r) (p' : QkPt D F' k)
    (hp' : QkExt (algebraMap (FractionRing R) F') p₀ p') : QkPt.Equiv D F' p' (qkExt hB f hf r) := by
  obtain ⟨p, hp, -⟩ := existsUnique_qkExt hB (algebraMap (FractionRing R) F) (RingHom.ext fun _ => rfl) p₀
  have h₁ := qkExt_trans hp ((qkExt_iff hB f hf p _).2 rfl)
  rw [hf] at h₁
  rw [(existsUnique_qkExt hB (algebraMap (FractionRing R) F') (RingHom.ext fun _ => rfl) p₀).unique hp' h₁]
  exact qkExt_congr hB f hf (h p hp)

theorem exists_lift_ext : Laws → BrGtSt → BrWpSt → AllA fun {_} _ _ _ {_} {_} {_} {_} {_} {_} _ {O'} _ _ {_} a => ∀ (F F' : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing O') F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing O') F'] (f : F →+* F'), f.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') F' → ∀ S : ValuationSubring F', (∀ r : O', algebraMap (FractionRing O') F' (algebraMap O' _ r) ∈ S) → ∀ A : Lift a F, ∃ A' : Lift a F', A'.ν.Integral S ∧ ∃ I : NumD.Hom f A.N A'.N, I.lam = 1 ∧ f A.ρ = A'.ρ ∧ (∀ n, 0 < n → f (A.I.ζ n) = A'.I.ζ n) ∧ (∀ y, A'.ν.eX (I.e y) = A.ν.eX y) ∧ ∀ n v, (A'.q n v).1.1.toAdd = I.e (A.q n v).1.1.toAdd ∧ I.Rel (A.q n v).1.2 (A'.q n v).1.2 := by
  intro hL hGt hWp E _ _ _ H D l Xo c W₀ Y R _ _ _ b ϖ a _ F F' _ _ _ _ _ _ f hf S hS A
  have hf₀ : ∀ x, f (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x := fun x =>
    DFunLike.congr_fun hf x
  have : CharZero F := charZero_of_isPrimitiveRoot A.I.ζ_prim
  obtain ⟨J', hg, hJ⟩ := GlobalTheory.ValuesExist.exists_gauge F' S a.D₀.P.isLB
  obtain ⟨N', ν', rfl, hth⟩ := GlobalTheory.GaugeValues.exists_numOf hL R a.D₀ a.even a.bimult F' J' hg A.ν.th A.ν.th_gen
  have G := (hGt R a.D₀ a.even a.bimult F A.N A.ν).2.2.2.2
  have G' := (hGt R a.D₀ a.even a.bimult F' N' ν').2.2.2.2
  obtain ⟨I, hlam, heX, hI⟩ := GlobalTheory.T.exists_numDHom_degenerationValues_fieldExtension R a.D₀ F F' f hf A.N N' A.ν ν' hth
  have hw : ∀ k, 1 ≤ k → ∀ (p p' : QkPt a.D₀ F k) (z : F), WeilQkIs a.D₀ F k p p' z →
      WeilQkIs a.D₀ F' k (qkExt a.bimult f hf p) (qkExt a.bimult f hf p') (f z) := fun k hk p p' z h => by
    obtain ⟨q, hq, -⟩ := (G k).1 p
    obtain ⟨q', hq', -⟩ := (G k).1 p'
    obtain ⟨r, hr, -⟩ := (G' k).1 (qkExt a.bimult f hf p)
    obtain ⟨r', hr', -⟩ := (G' k).1 (qkExt a.bimult f hf p')
    have e := hI k _ _ _ _ ((qkExt_iff a.bimult f hf _ _).2 rfl) hq hr
    have e' := hI k _ _ _ _ ((qkExt_iff a.bimult f hf _ _).2 rfl) hq' hr'
    rw [hWp R a.D₀ a.even a.bimult F' N' ν' k hk _ _ _ _ _ hr hr',
      (GlobalTheory.T.hom_transport_alt F F' f A.N N' I).2.2.2.1 k q q' r r' e.1 e.2 e'.1 e'.2,
      (hWp R a.D₀ a.even a.bimult F A.N A.ν k hk _ _ _ _ _ hq hq').1 h]
    rfl
  choose q' hq' using fun (n : ℕ) (v : D.La) => ((G' n).1 (qkExt a.bimult f hf (A.I.ev n v))).exists
  refine ⟨{ ρ := f A.ρ
            ρ_sq := by rw [← map_pow, A.ρ_sq, map_neg]; simp
            det := fun σ => ?_
            I := tateExt f hf a.bimult hL A.I hw, N := N', ν := ν', q := q', hq := hq'
            be := { be := a.be.compl₁₂ ν'.eX.toAddMonoidHom.toIntLinearMap ν'.eX.toAddMonoidHom.toIntLinearMap
                    symm := fun y z => a.be_symm _ _
                    pos := fun y hy => a.be_pos _ fun h => hy (ν'.eX.map_eq_zero_iff.1 h)
                    dvd := fun y z => a.be_dvd _ _ }
            be_eq := fun _ _ => rfl
            ρ_eq := fun r hr => (congrArg f (A.ρ_eq r hr)).trans (hf₀ _)
            ζ_eq := fun z hz => (congrArg f (A.ζ_eq z hz)).trans (hf₀ _)
            levA := fun v => equiv_of_base a.bimult f hf (A.levA v)
            levM := fun v hv => equiv_of_base a.bimult f hf (A.levM v hv)
            closed := inferInstance },
    fun x => hJ _ (GlobalTheory.ValuesExist.exists_ext a.D₀ F' S hS x), I, hlam, rfl, fun _ _ => rfl, heX,
    fun n v => hI n _ _ _ _ ((qkExt_iff a.bimult f hf _ _).2 rfl) (A.hq n v) (hq' n v)⟩
  obtain ⟨τ, rfl⟩ := DetExtend.exists_factor f σ
  obtain ⟨n, h₁, h₂⟩ := A.det τ
  have := a.D₀.P.isAb.smooth
  refine ⟨n, ?_, h₂.trans (by
    by_cases h : τ H.rt = A.ρ
    · rw [if_pos h, if_pos (show f.comp τ H.rt = f A.ρ from congrArg f h)]
    · rw [if_neg h, if_neg (show ¬ f.comp τ H.rt = f A.ρ from fun e => h (f.injective e))])⟩
  have e : spMap ((algebraMap (FractionRing R) F').comp (algebraMap R _)) =
      spMap f ≫ spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _)) := by
    rw [← spMap_comp', ← RingHom.comp_assoc, hf]
  rw [e]
  exact (DetExtend.lieMult_extend f _ _ τ n).2 h₁

end GlobalTheory.LiftExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcLiftExtensionLargerClosedFieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arcLift_extension_larger_closed_field : Laws → BrGtSt → BrWpSt → AllA fun {_} _ _ _ {_} {_} {_} {_} {_} {_} _ {O'} _ _ {_} a => ∀ (F F' : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing O') F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing O') F'] (f : F →+* F'), f.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') F' → ∀ S : ValuationSubring F', (∀ r : O', algebraMap (FractionRing O') F' (algebraMap O' _ r) ∈ S) → ∀ A : Lift a F, ∃ A' : Lift a F', A'.ν.Integral S ∧ ∃ I : NumD.Hom f A.N A'.N, I.lam = 1 ∧ f A.ρ = A'.ρ ∧ (∀ n, 0 < n → f (A.I.ζ n) = A'.I.ζ n) ∧ (∀ y, A'.ν.eX (I.e y) = A.ν.eX y) ∧ ∀ n v, (A'.q n v).1.1.toAdd = I.e (A.q n v).1.1.toAdd ∧ I.Rel (A.q n v).1.2 (A'.q n v).1.2 := by
  first | exact @GlobalTheory.LiftExt.exists_lift_ext | exact GlobalTheory.LiftExt.exists_lift_ext | (intros; apply GlobalTheory.LiftExt.exists_lift_ext <;> assumption)
end
end

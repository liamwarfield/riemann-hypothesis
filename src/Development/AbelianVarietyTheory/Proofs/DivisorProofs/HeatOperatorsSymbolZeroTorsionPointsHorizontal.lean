module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreLiftCommTranslationSectionRatios

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationHorizontalOfCommutingHeatOperators
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftCommutesTranslation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocDerKMono
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Heat.DerComm
open GlobalTheory.KS GlobalTheory.LocDerExt

theorem appLE_congr {X Y : Scheme.{0}} {g g' : Y ⟶ X} (e : g = g') (U : X.Opens) (V : Y.Opens)
    (h : V ≤ g ⁻¹ᵁ U) (h' : V ≤ g' ⁻¹ᵁ U) : g.appLE U V h = g'.appLE U V h' := by
  subst e; rfl

theorem locDerK_mono {R K : Type} [CommRing R] [Field K] {X Y : Scheme.{0}} {q : Y ⟶ Sp K}
    {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {W₀ W₁ : X.Opens}
    {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDerK q p m D W₀ d) (hW : W₁ ≤ W₀) :
    LocDerK q p m D W₁ d :=
  ⟨fun W hW' => h.add W (hW'.trans hW), fun W hW' => h.mul W (hW'.trans hW),
   fun W W' h' hW' => h.res W W' h' (hW'.trans hW), fun W hW' => h.base W (hW'.trans hW)⟩

theorem eq_of_gen {R K : Type} [CommRing R] [Field K] {X Y : Scheme.{0}} {q : Y ⟶ Sp K}
    {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {V : X.Opens}
    {d d' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDerK q p m D V d)
    (h' : LocDerK q p m D V d') {M : Type} (r : M → Γ(X, V))
    (hs : Function.Surjective (MvPolynomial.eval₂Hom (p.appLE ⊤ V (fun _ _ => trivial)).hom r))
    (he : ∀ j, d V (r j) = d' V (r j)) : d V = d' V := by
  funext f
  obtain ⟨P, rfl⟩ := hs f
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂Hom_C]
    have e : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) = a := by
      simp
    have : (p.appLE ⊤ V (fun _ _ => trivial)).hom a =
        constFn p V ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) := by
      unfold constFn; rw [e]
    rw [this, h.base V le_rfl, h'.base V le_rfl]
  | add P Q hP hQ => rw [map_add (f := _), h.add V le_rfl, h'.add V le_rfl, hP, hQ]
  | mul_X P n hP => rw [map_mul, MvPolynomial.eval₂Hom_X', h.mul V le_rfl, h'.mul V le_rfl, hP, he]

theorem comm_of_gen : ∀ {R K : Type} [CommRing R] [Field K] {X Y : Scheme.{0}} (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (dl : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)), GlobalTheory.KS.LocDerK q p m D ⊤ dl → ∀ (T : X ⟶ X) (T₀ : Y ⟶ Y), T₀ ≫ m = m ≫ T → T₀ ≫ q = q → T ≫ p = p → ∀ (Ix : Type) (U : Ix → X.Opens) (M : Ix → Type) (r : ∀ i, M i → Γ(X, U i)), (⨆ i, U i = ⊤) → (∀ i, IsAffineOpen (U i)) → (∀ i, Function.Surjective (MvPolynomial.eval₂Hom (p.appLE ⊤ (U i) (fun _ _ => trivial)).hom (r i))) → (∀ i j, dl (T ⁻¹ᵁ U i) ((T.app (U i)).hom (r i j)) = pbT T₀ (dl (U i) (r i j)) (m ⁻¹ᵁ (T ⁻¹ᵁ U i))) → ∀ (W : X.Opens) (f : Γ(X, W)), dl (T ⁻¹ᵁ W) ((T.app W).hom f) = pbT T₀ (dl W f) (m ⁻¹ᵁ (T ⁻¹ᵁ W)) := by
  intro R K _ _ X Y q p m D dl hdl T T₀ hm hq hp Ix U M r hU hA hs hg
  have pe : ∀ V : X.Opens, (m ≫ T) ⁻¹ᵁ V ≤ T₀ ⁻¹ᵁ (m ⁻¹ᵁ V) := fun V => by
    rw [← hm]; exact le_rfl
  have app1 : ∀ (V : X.Opens) (g : Γ(X, V)),
      (m.app (T ⁻¹ᵁ V)).hom ((T.app V).hom g) = ((m ≫ T).app V).hom g := by
    intro V g; rw [Scheme.Hom.comp_app]; rfl
  have app2 : ∀ (V : X.Opens) (g : Γ(X, V)),
      pbT T₀ ((m.app V).hom g) ((m ≫ T) ⁻¹ᵁ V) = ((m ≫ T).app V).hom g := by
    intro V g
    rw [pbT_of_le T₀ (pe V), Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
    have := congrArg (fun φ => φ.hom g) (Scheme.Hom.appLE_comp_appLE T₀ m V (m ⁻¹ᵁ V) ((m ≫ T) ⁻¹ᵁ V) le_rfl (pe V))
    refine this.trans ?_
    exact congrArg (fun φ : Γ(X, V) ⟶ Γ(Y, (m ≫ T) ⁻¹ᵁ V) => φ.hom g) (appLE_congr hm V _ _ _)
  let d1 : ∀ V : X.Opens, Γ(X, V) → Γ(Y, (m ≫ T) ⁻¹ᵁ V) := fun V g => dl (T ⁻¹ᵁ V) ((T.app V).hom g)
  let d2 : ∀ V : X.Opens, Γ(X, V) → Γ(Y, (m ≫ T) ⁻¹ᵁ V) := fun V g => pbT T₀ (dl V g) ((m ≫ T) ⁻¹ᵁ V)
  have h1 : LocDerK q p (m ≫ T) D ⊤ d1 := by
    refine ⟨fun V _ g g' => ?_, fun V _ g g' => ?_, fun V V' h _ g => ?_, fun V _ a => ?_⟩
    · simp only [d1, map_add (f := _)]; exact hdl.add _ le_top _ _
    · simp only [d1, map_mul]; rw [hdl.mul _ le_top, app1, app1]; exact rfl
    · simp only [d1]; rw [app_res T h, hdl.res _ _ _ le_top]; rfl
    · simp only [d1]
      rw [Scheme.Hom.app_eq_appLE, ← pbT_of_le T le_rfl, pbT_constFn p T le_rfl, hp]
      exact hdl.base _ le_top a
  have h2 : LocDerK q p (m ≫ T) D ⊤ d2 := by
    refine ⟨fun V _ g g' => ?_, fun V _ g g' => ?_, fun V V' h _ g => ?_, fun V _ a => ?_⟩
    · simp only [d2]; rw [hdl.add _ le_top, pbT_add]
    · simp only [d2]; rw [hdl.mul _ le_top, pbT_add, pbT_mul, pbT_mul, app2, app2]
    · simp only [d2]
      rw [hdl.res _ _ h le_top, pbT_rsT T₀ (pre_le m h) (pe V'), rsT_pbT T₀ (pe V) (pre_le (m ≫ T) h)]
    · simp only [d2]; rw [hdl.base _ le_top, pbT_constFn q T₀ (pe V), hq]
  have key : ∀ i, ∀ V, V ≤ U i → d1 V = d2 V := fun i V hV =>
    GlobalTheory.LocDerExtK.locDerK_unique (hA i) d1 d2 (locDerK_mono h1 le_top) (locDerK_mono h2 le_top)
      (eq_of_gen (locDerK_mono h1 le_top) (locDerK_mono h2 le_top) (r i) (hs i) (fun j => hg i j)) V hV
  intro W f
  show d1 W f = d2 W f
  refine eq_of_rsT_eq (fun k => (m ≫ T) ⁻¹ᵁ (W ⊓ U k)) (fun k => pre_le _ inf_le_left) ?_ _ _ ?_
  · intro y hy
    have : (m ≫ T).base y ∈ ⨆ i, U i := by rw [hU]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩
  · intro k
    rw [← h1.res W _ inf_le_left le_top, ← h2.res W _ inf_le_left le_top, key k _ inf_le_right]

end GlobalTheory.Heat.DerComm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastTer
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Gens

theorem res_ι_app {X : Scheme.{0}} (U : X.Opens) (V : U.toScheme.Opens) (x : Γ(X, U.ι ''ᵁ V))
    (hle : V ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V)) :
    (U.toScheme.presheaf.map (homOfLE hle).op).hom ((U.ι.app (U.ι ''ᵁ V)).hom x) = x := by
  have h1 := Scheme.Hom.appIso_hom U.ι V
  rw [Scheme.Opens.ι_appIso] at h1
  have h3 := congrArg (fun f => f.hom x) h1
  simp only [Iso.refl_hom, CommRingCat.hom_comp, RingHom.comp_apply] at h3
  exact (congrArg (fun f => (U.toScheme.presheaf.map f).hom ((U.ι.app (U.ι ''ᵁ V)).hom x))
    (Subsingleton.elim (homOfLE hle).op _)).trans h3.symm

theorem gs_ι {X : Scheme.{0}} (U : X.Opens) (j : X ⟶ U.toScheme) (hj : j ≫ U.ι = 𝟙 X) (V : U.toScheme.Opens)
    (x : Γ(X, U.ι ''ᵁ V)) (y : X) (hy : j y ∈ V) : gs j y V x = gs (𝟙 X) y (U.ι ''ᵁ V) x := by
  have hle : V ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V) := (Scheme.Hom.preimage_image_eq U.ι V).ge
  have e := gs_res j y hle hy ((U.ι.app (U.ι ''ᵁ V)).hom x)
  rw [res_ι_app] at e
  rw [e, gs_pull j U.ι y _ (hle hy), hj]

theorem gens : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R), ∃ N : ℕ, 1 ≤ N ∧ ∃ (Ix : Type) (U : Ix → Q.P.A.left.Opens) (M : Ix → Type) (r : ∀ i, M i → Γ(Q.P.A.left, U i)), (⨆ i, U i = ⊤) ∧ (∀ i, IsAffineOpen (U i)) ∧ (∀ i, Function.Surjective (MvPolynomial.eval₂Hom (Q.P.A.hom.appLE ⊤ (U i) (fun _ _ => trivial)).hom (r i))) ∧ ∀ i j, ∃ σ σ' : Q.SecB N 0, ∀ z ∈ U i, ∀ J, Good Q.P.L z J → IsUnit (sval σ' (𝟙 _) z J) ∧ sval σ (𝟙 _) z J = gs (𝟙 _) z (U i) (r i j) * sval σ' (𝟙 _) z J := by
  intro R _ _ Q
  obtain ⟨N, hN, M, s, hcov, hs⟩ := Q.P.ample ⊤ (isAffineOpen_top _)
  choose haff r hr hsurj using hs
  let ιU := (Q.P.A.hom ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)).ι
  let j : Q.P.A.left ⟶ (Q.P.A.hom ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)).toScheme := Q.P.A.left.topIso.inv
  have hj : j ≫ ιU = 𝟙 _ := by
    show Q.P.A.left.topIso.inv ≫ (⊤ : Q.P.A.left.Opens).ι = _
    rw [← Scheme.topIso_hom, Iso.inv_hom_id]
  have hιj : ιU ≫ j = 𝟙 _ := by
    show (⊤ : Q.P.A.left.Opens).ι ≫ Q.P.A.left.topIso.inv = _
    rw [← Scheme.topIso_hom, Iso.hom_inv_id]; rfl
  have hjι : ∀ w, j (ιU w) = w := fun w => by show (ιU ≫ j).base w = w; rw [hιj]; rfl
  have hfe : FormEq (K := Fin N) (fun _ => 𝟙 Q.P.A.left) (fun _ => (1 : ℤ)) (Q.famφB 0) (DegPre.famε N) := by
    intro U _ h
    refine Eq.trans ?_ (GlobalTheory.Mum.OriginSec.formEq_zero Q N U h)
    simp [Finset.prod_const, Fin.prod_univ_one]
  have hσ : ∀ a, ∃ σ : Q.SecB N 0, ∀ (z : Q.P.A.left) J, Good Q.P.L z J → sval σ (𝟙 _) z J = sval (s a) j z J := by
    intro a
    obtain ⟨s', hs'⟩ := GlobalTheory.UU.exists_pullSec_sval
      (s a : LB.Sec (LB.LinComb Q.P.L (K := Fin N) (fun _ => ιU) (fun _ => (1 : ℤ)))) j
      (fun _ : Fin N => 𝟙 Q.P.A.left) (fun _ => hj)
    obtain ⟨σ, hσ⟩ := exists_sec Q.P.isLB hfe s'
    exact ⟨σ, fun z J hJ => (hσ _ _ z J hJ).trans ((hs' _ _ z J hJ).trans (by rw [Category.id_comp]))⟩
  choose σ hσv using hσ
  refine ⟨N, hN, Fin (M + 1), fun a => ιU ''ᵁ nonzeroLocus (s a), fun _ => Fin (M + 1), fun a b => r a b, ?_, ?_, ?_, ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (show j y ∈ ⨆ a, nonzeroLocus (s a) by rw [hcov]; trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, ⟨j y, ha, show (j ≫ ιU).base y = y by rw [hj]; rfl⟩⟩
  · exact fun a => (haff a).image_of_isOpenImmersion ιU
  · intro a
    have key : ∀ (U U' : (Spec (CommRingCat.of R)).Opens) (_ : U = U') (W : Q.P.A.left.Opens) e e'
        (rr : Fin (M + 1) → Γ(Q.P.A.left, W)),
        Function.Surjective (MvPolynomial.eval₂Hom (Q.P.A.hom.appLE U' W e').hom rr) →
        Function.Surjective (MvPolynomial.eval₂Hom (Q.P.A.hom.appLE U W e).hom rr) := by
      rintro _ _ rfl _ _ _ _ h; exact h
    have e2 := morphismRestrict_appLE Q.P.A.hom ⊤ ⊤ (nonzeroLocus (s a)) le_top
    have h' := (congrArg (fun g => Function.Surjective (MvPolynomial.eval₂Hom (CommRingCat.Hom.hom g) (r a))) e2).mp (hsurj a)
    exact key ⊤ ((⊤ : (Spec (CommRingCat.of R)).Opens).ι ''ᵁ ⊤) (Scheme.Opens.ι_image_top _).symm
      (ιU ''ᵁ nonzeroLocus (s a)) _ _ (r a) h'
  · intro a b
    refine ⟨σ b, σ a, fun z hz J hJ => ?_⟩
    obtain ⟨w, hw, rfl⟩ := hz
    rw [hσv _ _ _ hJ, hσv _ _ _ hJ]
    have hm := hJ.mem (fun _ : Fin N => ιU) j
    have hw' : j (ιU w) ∈ nonzeroLocus (s a) := by rw [hjι]; exact hw
    refine ⟨(GlobalTheory.Mum.OriginSec.isUnit_sval_iff' (s a) j (ιU w) hJ).2 hw', ?_⟩
    have hm' : j (ιU w) ∈ nonzeroLocus (s a) ⊓ (powOver Q.P.A Q.P.L ⊤ N).U (fun _ => J (j ≫ ιU)) := ⟨hw', hm⟩
    have e := congrArg (gs j (ιU w) _) (hr a b (fun _ => J (j ≫ ιU)))
    rw [gs_res _ _ _ hm', gs_mul _ _ _ hm', gs_res _ _ _ hm', gs_res _ _ _ hm'] at e
    rw [gs_ι _ j hj _ (r a b) _ hw'] at e
    exact e
end GlobalTheory.Heat.Gens
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatTranslW

theorem lift_commutes_translation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r)))  → ∀ (A₀ : Over (Sp k)) (_ : GrpObj A₀) (m₀ : A₀.left ⟶ P.D.toPre.P.A.left), IsGrpPullback A₀ P.D.toPre.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∃ dl : ∀ W : P.D.toPre.P.A.left.Opens, Γ(P.D.toPre.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.D.toPre.P.A.hom m₀ (fun r => (ρ r).snd) ⊤ dl ∧ ∀ (y : P.D.toPre.X) (T₀ : A₀.left ⟶ A₀.left), T₀ ≫ m₀ = m₀ ≫ (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left → T₀ ≫ A₀.hom = A₀.hom → ∀ (W : P.D.toPre.P.A.left.Opens) (f : Γ(P.D.toPre.P.A.left, W)), dl ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ W) (((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left.app W).hom f) = pbT T₀ (dl W f) (m₀ ⁻¹ᵁ ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ W)) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab
  letI := H.starRing
  intro Y n' v' dd hinv D q hq h hB hdef hΘ ρ hρ A₀ _ m₀ hm₀
  let φ : ChartRing k m d →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ
  have hφΘ : ∀ a b, φ (h.Θ a b) = 0 := fun a b => by
    have h0 : MvPowerSeries.constantCoeff (h.Θ a b) = 0 := by
      by_contra hne
      exact hΘ a b (MvPowerSeries.isUnit_iff_constantCoeff.2 (Ne.isUnit hne))
    simp [φ, hρ, h0]
  obtain ⟨dl, hdl, hdesc⟩ := GlobalTheory.Heat.AbConst.exists_locDerK_desc Y h (fun a => (hinv a).1) hB φ hφΘ A₀.hom m₀ hm₀.1.w
  have hD : (fun r => φ (D r)) = fun r => (ρ r).snd := funext fun r => by simp [φ, hρ]
  rw [hD] at hdl
  refine ⟨dl, hdl, fun y T₀ hT₀ hT₀' W f => ?_⟩
  obtain ⟨N, hN, Ix, U, M, r, hU, hUa, hgen, hrat⟩ := GlobalTheory.Heat.Gens.gens P.D.toPre
  refine GlobalTheory.Heat.DerComm.comm_of_gen A₀.hom P.D.toPre.P.A.hom m₀ _ dl hdl _ T₀ hT₀ hT₀' (Over.w _) Ix U M r hU hUa hgen (fun i j => ?_) W f
  obtain ⟨σ, σ', hσ⟩ := hrat i j
  exact GlobalTheory.T.closedFibreLift_comm_translation_section_ratios E H k m d t P gam hmon hli hab Y n' v' dd hinv D q hq h hB hdef hΘ ρ hρ A₀ _ m₀ hm₀ dl hdl hdesc y T₀ hT₀
    hT₀' N hN σ σ' (U i) (r i j) hσ

end GlobalTheory.HeatTranslW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHorizOfComm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderLiftDerivationCommTranslations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderLiftDerivationCommTranslations
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KS.LiftComm

theorem appLE_congr {Z X : Scheme.{0}} {k k' : Z ⟶ X} (h : k = k') (U : X.Opens) (V : Z.Opens)
    (e : V ≤ k ⁻¹ᵁ U) (e' : V ≤ k' ⁻¹ᵁ U) : k.appLE U V e = k'.appLE U V e' := by
  subst h; rfl

theorem pbT_of_le {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Z.Opens)
    (h : O ≤ f ⁻¹ᵁ O₀) : pbT f s O = (f.appLE O₀ O h).hom s := by
  unfold pbT; rw [dite_eq_left h]

theorem ext_of_opens {Z X : Scheme.{0}} {a b : Z ⟶ X} (hb : a.base = b.base) (O : X.Opens → Z.Opens)
    (hO : ∀ U, O U = b ⁻¹ᵁ U)
    (h : ∀ U (e1 : O U ≤ a ⁻¹ᵁ U) (e2 : O U ≤ b ⁻¹ᵁ U), a.appLE U (O U) e1 = b.appLE U (O U) e2) :
    a = b := by
  refine GlobalTheory.KS.DerMorK.hom_ext_appLE hb fun U e => ?_
  have key : ∀ V (_ : V = O U) (e1 : V ≤ a ⁻¹ᵁ U) (e2 : V ≤ b ⁻¹ᵁ U), a.appLE U V e1 = b.appLE U V e2 := by
    intro V hV e1 e2; subst hV; exact h U e1 e2
  rw [key _ (hO U).symm e le_rfl, Scheme.Hom.appLE_eq_app]

theorem translate_comm : ∀ (k : Type) [Field k] (Y Y' X : Scheme.{0}) (m : Y ⟶ X) (π : Y' ⟶ Sp (DualNumber k)) (ρ' : Y' ⟶ Y) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) (Φ : Y' ⟶ X), (∀ y, Φ y = m (ρ' y)) → (∀ (W : X.Opens) (f : Γ(X, W)), pbT Φ f (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) = pbT (ρ' ≫ m) f (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) + constFn π (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) DualNumber.eps * pbT ρ' (d W f) (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W))) → ∀ (T : X ⟶ X) (T₀ : Y ⟶ Y) (TY : Y' ⟶ Y'), T₀ ≫ m = m ≫ T → TY ≫ ρ' = ρ' ≫ T₀ → TY ≫ π = π → (∀ (W : X.Opens) (f : Γ(X, W)), d (T ⁻¹ᵁ W) ((T.app W).hom f) = pbT T₀ (d W f) (m ⁻¹ᵁ (T ⁻¹ᵁ W))) → TY ≫ Φ = Φ ≫ T := by
  intro k _ Y Y' X m π ρ' d Φ hb hΦ T T₀ TY h₀ h₁ h₂ hd
  have hcomp : TY ≫ ρ' ≫ m = ρ' ≫ m ≫ T := by
    rw [← Category.assoc, h₁, Category.assoc, h₀]
  have hbase : (TY ≫ Φ).base = (Φ ≫ T).base := by
    ext y
    have e := congrArg (fun g => g.base y) hcomp
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at e ⊢
    rw [hb, hb, e]
  have hle : ∀ (Z : Scheme.{0}) (V : X.Opens) (g : Z ⟶ Y'), g ⁻¹ᵁ ρ' ⁻¹ᵁ m ⁻¹ᵁ V ≤ g ⁻¹ᵁ Φ ⁻¹ᵁ V := by
    intro Z V g y hy
    show Φ.base (g.base y) ∈ V
    rw [hb]; exact hy
  refine ext_of_opens hbase (fun W => ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) (fun W => ?_) (fun W e1 e2 => ?_)
  · exact le_antisymm (hle Y' (T ⁻¹ᵁ W) (𝟙 _)) (by
      intro y hy
      show T.base (m.base (ρ'.base y)) ∈ W
      rw [← hb]; exact hy)
  · ext f
    have hO' : ρ' ⁻¹ᵁ m ⁻¹ᵁ W ≤ Φ ⁻¹ᵁ W := hle Y' W (𝟙 _)
    have e' : ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W ≤ TY ⁻¹ᵁ ρ' ⁻¹ᵁ m ⁻¹ᵁ W :=
      le_of_eq (congrArg (fun g => g ⁻¹ᵁ W) hcomp.symm)
    have e2' : ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W ≤ Φ ⁻¹ᵁ T ⁻¹ᵁ W := hle Y' (T ⁻¹ᵁ W) (𝟙 _)
    have hT0 : m ⁻¹ᵁ T ⁻¹ᵁ W ≤ T₀ ⁻¹ᵁ m ⁻¹ᵁ W := le_of_eq (congrArg (fun g => g ⁻¹ᵁ W) h₀.symm)
    have hL : ((TY ≫ Φ).appLE W _ e1).hom f = (TY.appLE _ _ e').hom ((Φ.appLE W _ hO').hom f) := by
      rw [← Scheme.Hom.appLE_comp_appLE TY Φ W _ _ hO' e']; rfl
    have hR : ((Φ ≫ T).appLE W _ e2).hom f = (Φ.appLE (T ⁻¹ᵁ W) _ e2').hom ((T.app W).hom f) := by
      rw [Scheme.Hom.app_eq_appLE, ← Scheme.Hom.appLE_comp_appLE Φ T W (T ⁻¹ᵁ W) _ le_rfl e2']; rfl
    rw [hL, hR, ← pbT_of_le Φ f _ hO', ← pbT_of_le Φ _ _ e2', hΦ, hΦ, map_add (f := _), map_mul,
      GlobalTheory.KS.DerMorK.appLE_constFn, h₂, hd]
    have a1 : pbT (ρ' ≫ m) f (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) = ((ρ' ≫ m).appLE W (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) le_rfl).hom f :=
      pbT_of_le _ _ _ _
    have a2 : pbT ρ' (d W f) (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) = (ρ'.appLE (m ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) le_rfl).hom (d W f) :=
      pbT_of_le _ _ _ _
    have a3 : pbT (ρ' ≫ m) ((T.app W).hom f) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) =
        ((ρ' ≫ m).appLE (T ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) le_rfl).hom ((T.app W).hom f) :=
      pbT_of_le _ _ _ _
    have a4 : pbT T₀ (d W f) (m ⁻¹ᵁ T ⁻¹ᵁ W) = (T₀.appLE (m ⁻¹ᵁ W) (m ⁻¹ᵁ T ⁻¹ᵁ W) hT0).hom (d W f) :=
      pbT_of_le _ _ _ _
    have a5 : ∀ x : Γ(Y, m ⁻¹ᵁ T ⁻¹ᵁ W), pbT ρ' x (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) =
        (ρ'.appLE (m ⁻¹ᵁ T ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) le_rfl).hom x :=
      fun x => pbT_of_le _ _ _ _
    rw [a1, a2, a3, a4, a5]
    congr 1
    · have c1 := Scheme.Hom.appLE_comp_appLE TY (ρ' ≫ m) W (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) le_rfl e'
      have c2 := Scheme.Hom.appLE_comp_appLE (ρ' ≫ m) T W (T ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) le_rfl le_rfl
      have c3 := appLE_congr (hcomp.trans (Category.assoc _ _ _).symm) W (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W)
        (le_of_eq (congrArg (fun g => g ⁻¹ᵁ W) hcomp.symm)) le_rfl
      rw [Scheme.Hom.app_eq_appLE]
      exact (congr(($c1).hom f)).trans ((congr(($c3).hom f)).trans (congr(($c2).hom f)).symm)
    · congr 1
      have c1 := Scheme.Hom.appLE_comp_appLE TY ρ' (m ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) le_rfl e'
      have c2 := Scheme.Hom.appLE_comp_appLE ρ' T₀ (m ⁻¹ᵁ W) (m ⁻¹ᵁ T ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) hT0 le_rfl
      have c3 := appLE_congr h₁ (m ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W)
        (le_trans e' le_rfl) (le_trans le_rfl (ρ'.preimage_mono hT0))
      exact (congr(($c1).hom (d W f))).trans ((congr(($c3).hom (d W f))).trans (congr(($c2).hom (d W f))).symm)

end GlobalTheory.KS.LiftComm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderLiftDerivationCommTranslationsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstOrderLift_derivation_comm_translations : ∀ (k : Type) [Field k] (Y Y' X : Scheme.{0}) (m : Y ⟶ X) (π : Y' ⟶ Sp (DualNumber k)) (ρ' : Y' ⟶ Y) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) (Φ : Y' ⟶ X), (∀ y, Φ y = m (ρ' y)) → (∀ (W : X.Opens) (f : Γ(X, W)), pbT Φ f (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) = pbT (ρ' ≫ m) f (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) + constFn π (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) DualNumber.eps * pbT ρ' (d W f) (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W))) → ∀ (T : X ⟶ X) (T₀ : Y ⟶ Y) (TY : Y' ⟶ Y'), T₀ ≫ m = m ≫ T → TY ≫ ρ' = ρ' ≫ T₀ → TY ≫ π = π → (∀ (W : X.Opens) (f : Γ(X, W)), d (T ⁻¹ᵁ W) ((T.app W).hom f) = pbT T₀ (d W f) (m ⁻¹ᵁ (T ⁻¹ᵁ W))) → TY ≫ Φ = Φ ≫ T := by
  first | exact @GlobalTheory.KS.LiftComm.translate_comm | exact GlobalTheory.KS.LiftComm.translate_comm | (intros; apply GlobalTheory.KS.LiftComm.translate_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackTranslationCompEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackTranslationCompEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TranslPull

theorem transl_comp_of_isGrpPullback : ∀ {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (x : 𝟙_ (Over S') ⟶ G') (s : 𝟙_ (Over S) ⟶ G), x.left ≫ φ = f ≫ s.left → (lift (toUnit G' ≫ x) (𝟙 G') ≫ μ[G']).left ≫ φ = φ ≫ (lift (toUnit G ≫ s) (𝟙 G) ≫ μ[G]).left := by
  intro S S' G' _ G _ f φ h x s hx
  have hu' : ∀ (Y : Over S'), (toUnit Y).left = Y.hom := fun Y => by
    simpa using Over.w (toUnit Y)
  have hu : ∀ (Y : Over S), (toUnit Y).left = Y.hom := fun Y => by
    simpa using Over.w (toUnit Y)
  have hs : s.left ≫ G.hom = 𝟙 S := by simpa using Over.w s
  let x₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk (G'.hom ≫ f ≫ s.left) (by
    simp [hs])
  let y₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ (by simpa using h.1.w)
  have key := h.2 G' (toUnit G' ≫ x) (𝟙 G') x₀ y₀ (by
      simp [x₀, hu', hx]) (by simp [y₀])
  have e1 : lift (toUnit G' ≫ x) (𝟙 G') ≫ μ[G'] = (toUnit G' ≫ x) * 𝟙 G' := rfl
  have e2 : x₀ * y₀ = (Over.homMk φ (by simpa using h.1.w) : Over.mk (G'.hom ≫ f) ⟶ G) ≫ (lift (toUnit G ≫ s) (𝟙 G) ≫ μ[G]) := by
    rw [← Category.assoc, comp_lift, Category.comp_id]
    have hx0 : x₀ = ((Over.homMk φ (by simpa using h.1.w) : Over.mk (G'.hom ≫ f) ⟶ G) ≫ toUnit G) ≫ s := by
      apply Over.OverMorphism.ext
      simp [x₀, hu]
    rw [hx0]
    rfl
  rw [e1, ← key, e2]
  rfl
end GlobalTheory.TranslPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackTranslationCompEqStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupPullback_translation_comp_eq : ∀ {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (x : 𝟙_ (Over S') ⟶ G') (s : 𝟙_ (Over S) ⟶ G), x.left ≫ φ = f ≫ s.left → (lift (toUnit G' ≫ x) (𝟙 G') ≫ μ[G']).left ≫ φ = φ ≫ (lift (toUnit G ≫ s) (𝟙 G) ≫ μ[G]).left := by
  first | exact @GlobalTheory.TranslPull.transl_comp_of_isGrpPullback | exact GlobalTheory.TranslPull.transl_comp_of_isGrpPullback | (intros; apply GlobalTheory.TranslPull.transl_comp_of_isGrpPullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDualNumberEndoEqTranslation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDualNumberEndoEqTranslation
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RigidEndo

theorem exists_factor_of_range_subset {X Y S : Scheme.{0}} [IsAffine S] (p : X ⟶ S) [IsIso p.appTop]
    (f : X ⟶ Y) (U : Y.Opens) (hU : IsAffineOpen U) (hf : Set.range f ⊆ U) :
    ∃ h : S ⟶ Y, f = p ≫ h := by
  have : IsAffine U := hU
  have hr : Set.range f ⊆ Set.range U.ι := by simpa using hf
  let g : X ⟶ U := IsOpenImmersion.lift U.ι f hr
  have hg : g ≫ U.ι = f := IsOpenImmersion.lift_fac _ _ _
  refine ⟨S.isoSpec.hom ≫ inv (Spec.map p.appTop) ≫ Spec.map g.appTop ≫ (U : Scheme).isoSpec.inv ≫ U.ι, ?_⟩
  have e1 : g = X.toSpecΓ ≫ Spec.map g.appTop ≫ (U : Scheme).isoSpec.inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]
  have e2 : X.toSpecΓ = p ≫ S.isoSpec.hom ≫ inv (Spec.map p.appTop) := by
    rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_naturality_assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← hg]
  nth_rw 1 [e1]
  rw [e2]
  simp only [Category.assoc]

theorem isIso_appTop (k : Type) [Field k] (B : Over (Sp (DualNumber k))) [GrpObj B]
    (hB : IsAbelianScheme B) : IsIso B.hom.appTop := by
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  haveI : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom ‹_› ‹_›
  exact GlobalTheory.GlobalFunctions.isIso_app GlobalTheory.FlatFibreInjective.injective_baseChange
    GlobalTheory.exists_noetherian_model_of_smooth B.hom ⊤

theorem eq_translate : ∀ (k : Type) [Field k] (B : Over (Sp (DualNumber k))) [GrpObj B], IsAbelianScheme B →
    ∀ (α : B ⟶ B), (∀ (Z : Scheme.{0}) (z : Z ⟶ B.left) (y : Z ⟶ Sp k),
      z ≫ B.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → z ≫ α.left = z) →
    α = lift (toUnit B ≫ η[B] ≫ α) (𝟙 B) ≫ μ[B] := by
  intro k _ B _ hB α hα
  set β : B ⟶ B := α * (𝟙 B)⁻¹ with hβ

  have h1 : ∀ (Z : Scheme.{0}) (z : Z ⟶ B.left) (y : Z ⟶ Sp k),
      z ≫ B.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom →
      z ≫ β.left = z ≫ B.hom ≫ η[B].left := by
    intro Z z y hz
    let zo : Over.mk (z ≫ B.hom) ⟶ B := Over.homMk z
    have ha : zo ≫ α = zo := by
      ext; exact hα Z z y hz
    have hb : zo ≫ β = toUnit _ ≫ η[B] := by
      rw [hβ, comp_mul, GrpObj.comp_inv, ha, Category.comp_id, mul_inv_cancel, Hom.one_def]
    have := congrArg CommaMorphism.left hb
    simpa [zo] using this

  let q : Sp k := Classical.arbitrary _
  let e0 : B.left := η[B].left (spMap (TrivSqZeroExt.fstHom k k k).toRingHom q)
  have hsurj : Surjective (pullback.fst B.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) := by
    have := GlobalTheory.ConstThickening.surjective_spMap_fst (K := k)
    infer_instance
  have h2 : ∀ x : B.left, β.left x = e0 := by
    intro x
    obtain ⟨w, rfl⟩ := hsurj.surj x
    have := h1 _ _ _ (pullback.condition (f := B.hom) (g := spMap (TrivSqZeroExt.fstHom k k k).toRingHom))
    rw [← Scheme.Hom.comp_apply, this, pullback.condition_assoc]
    simp only [Scheme.Hom.comp_apply, e0]
    congr 2
    exact Subsingleton.elim _ _

  obtain ⟨U, hU, heU, -⟩ := exists_isAffineOpen_mem_and_subset (X := B.left) (x := e0) (U := ⊤) trivial
  have := isIso_appTop k B hB
  obtain ⟨h, hh⟩ := exists_factor_of_range_subset B.hom β.left U hU (by
    rintro _ ⟨x, rfl⟩; rw [h2 x]; exact heU)
  have hη : η[B].left ≫ B.hom = 𝟙 _ := by simpa using Over.w η[B]
  have h3 : β.left = B.hom ≫ η[B].left ≫ β.left := by
    rw [hh, reassoc_of% hη]

  have h4 : β = toUnit B ≫ η[B] ≫ β := by
    ext; simpa using h3
  have h5 : η[B] ≫ β = η[B] ≫ α := by
    have e : η[B] = (1 : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B) := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have e' : η[B]⁻¹ = (1 : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B) := by rw [e, inv_one]
    rw [hβ, comp_mul, GrpObj.comp_inv, Category.comp_id, e', _root_.mul_one]
  calc α = β * 𝟙 B := by rw [hβ, inv_mul_cancel_right]
    _ = _ := by rw [Hom.mul_def, h4, h5]

end GlobalTheory.RigidEndo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDualNumberEndoEqTranslationStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_dualNumber_endo_eq_translation : ∀ (k : Type) [Field k] (B : Over (Sp (DualNumber k))) [GrpObj B], IsAbelianScheme B → ∀ (α : B ⟶ B), (∀ (Z : Scheme.{0}) (z : Z ⟶ B.left) (y : Z ⟶ Sp k), z ≫ B.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → z ≫ α.left = z) → α = lift (toUnit B ≫ η[B] ≫ α) (𝟙 B) ≫ μ[B] := by
  first | exact @GlobalTheory.RigidEndo.eq_translate | exact GlobalTheory.RigidEndo.eq_translate | (intros; apply GlobalTheory.RigidEndo.eq_translate <;> assumption)
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.TranslHoriz

theorem isHoriz_of_comm : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ A.left), IsGrpPullback B' A (spMap ρ) π₁ → IsGrpPullback B' A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) (_ : GrpObj A₀) (m₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ (dl : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)), GlobalTheory.KS.LocDerK A₀.hom A.hom m₀ (fun r => (ρ r).snd) ⊤ dl → ∀ (s : 𝟙_ (Over (Sp R)) ⟶ A) (T₀ : A₀.left ⟶ A₀.left), T₀ ≫ m₀ = m₀ ≫ (lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left → T₀ ≫ A₀.hom = A₀.hom → (∀ (W : A.left.Opens) (f : Γ(A.left, W)), dl ((lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left ⁻¹ᵁ W) (((lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left.app W).hom f) = pbT T₀ (dl W f) (m₀ ⁻¹ᵁ ((lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left ⁻¹ᵁ W))) → ∀ x : Sp (DualNumber k) ⟶ B'.left, x ≫ B'.hom = 𝟙 _ → x ≫ π₁ = spMap ρ ≫ s.left → x ≫ π₂ = spMap (constHom ρ) ≫ s.left := by
  intro k _ R _ A _ hA ρ B' _ π₁ π₂ h₁ h₂ hcl A₀ _ m₀ hm₀ dl hdl s T₀ hT₀ hT₀h hcomm x hx hx1
  set fst := (TrivSqZeroExt.fstHom k k k).toRingHom with hfst
  set alg := algebraMap k (DualNumber k) with halg
  have e_fa : spMap fst ≫ spMap alg = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]; congr 1
  have e_c : spMap (constHom ρ) = spMap alg ≫ spMap (fst.comp ρ) := by
    simp only [spMap, constHom, ← Spec.map_comp]; rfl
  have e_r : spMap (fst.comp ρ) = spMap fst ≫ spMap ρ := by
    simp only [spMap, ← Spec.map_comp]; rfl
  have P₁ := h₁.1
  have P₂ := h₂.1
  have P₀ := hm₀.1
  have wr : π₂ ≫ A.hom = (B'.hom ≫ spMap alg) ≫ spMap (fst.comp ρ) := by
    rw [P₂.w, e_c, Category.assoc]
  let r : B'.left ⟶ A₀.left := P₀.lift π₂ (B'.hom ≫ spMap alg) wr
  have hr1 : r ≫ m₀ = π₂ := P₀.lift_fst _ _ _
  have hr2 : r ≫ A₀.hom = B'.hom ≫ spMap alg := P₀.lift_snd _ _ _
  have Pr : IsPullback r B'.hom A₀.hom (spMap alg) := by
    refine IsPullback.of_right ?_ hr2 P₀
    rw [hr1, ← e_c]; exact P₂
  have wj : m₀ ≫ A.hom = (A₀.hom ≫ spMap fst) ≫ spMap (constHom ρ) := by
    rw [P₀.w, Category.assoc, e_c, ← Category.assoc (spMap fst), e_fa, Category.id_comp]
  let j : A₀.left ⟶ B'.left := P₂.lift m₀ (A₀.hom ≫ spMap fst) wj
  have hj1 : j ≫ π₂ = m₀ := P₂.lift_fst _ _ _
  have hj2 : j ≫ B'.hom = A₀.hom ≫ spMap fst := P₂.lift_snd _ _ _
  have hjr : j ≫ r = 𝟙 _ := P₀.hom_ext (by rw [Category.assoc, hr1, hj1, Category.id_comp])
    (by rw [Category.assoc, hr2, ← Category.assoc, hj2, Category.assoc, e_fa, Category.comp_id, Category.id_comp])
  have hjπ₁ : j ≫ π₁ = m₀ := by rw [hcl A₀.left j A₀.hom hj2, hj1]
  obtain ⟨-, Pj, -⟩ := GlobalTheory.ConstThickening.structure_dualNumber k A₀.left B'.left A₀.hom B'.hom r j Pr hjr hj2
  have hjs : Surjective j :=
    MorphismProperty.of_isPullback (P := @Surjective) Pj.flip GlobalTheory.ConstThickening.surjective_spMap_fst
  have hm : m₀ ≫ A.hom = A₀.hom ≫ spMap fst ≫ spMap ρ := by rw [P₀.w, e_r]
  obtain ⟨Φ, hΦj, hΦp, hΦ⟩ := GlobalTheory.KS.DerMorK.exists_hom_of_derivation k A₀.left B'.left A₀.hom B'.hom r j Pr hjr hj2
    R ρ A.left A.hom m₀ dl hm hdl
  have hb : ∀ y, Φ y = m₀ (r y) := by
    intro y
    obtain ⟨y₀, rfl⟩ := hjs.surj y
    show (j ≫ Φ) y₀ = (j ≫ r ≫ m₀) y₀
    rw [hΦj, ← Category.assoc, hjr, Category.id_comp]
  have wT : (r ≫ T₀) ≫ A₀.hom = B'.hom ≫ spMap alg := by rw [Category.assoc, hT₀h, hr2]
  let TB : B'.left ⟶ B'.left := Pr.lift (r ≫ T₀) B'.hom wT
  have hTB1 : TB ≫ r = r ≫ T₀ := Pr.lift_fst _ _ _
  have hTB2 : TB ≫ B'.hom = B'.hom := Pr.lift_snd _ _ _
  have hcΦ : TB ≫ Φ = Φ ≫ (lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left :=
    GlobalTheory.T.firstOrderLift_derivation_comm_translations k A₀.left B'.left A.left m₀ B'.hom r dl Φ hb hΦ _ T₀ TB hT₀ hTB1 hTB2 hcomm
  let α : B'.left ⟶ B'.left := P₁.lift Φ B'.hom hΦp
  have hα1 : α ≫ π₁ = Φ := P₁.lift_fst _ _ _
  have hα2 : α ≫ B'.hom = B'.hom := P₁.lift_snd _ _ _
  have hjα : j ≫ α = j := P₁.hom_ext (by rw [Category.assoc, hα1, hΦj, hjπ₁]) (by rw [Category.assoc, hα2])
  let αo : B' ⟶ B' := Over.homMk α hα2
  have hB' : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h₁
  set w : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B' := η[B'] ≫ αo with hw
  have hαo : αo = lift (toUnit B' ≫ w) (𝟙 B') ≫ μ[B'] := GlobalTheory.T.abelianScheme_dualNumber_endo_eq_translation k B' hB' αo (fun Z z y hz => by
    change z ≫ α = z
    rw [← Pj.lift_fst z y hz, Category.assoc, hjα])
  let xo : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B' := Over.homMk x hx
  have wσ : (spMap (constHom ρ) ≫ s.left) ≫ A.hom = 𝟙 _ ≫ spMap (constHom ρ) := by
    rw [Category.assoc, Over.w s, Category.id_comp]; rfl
  let σ : Sp (DualNumber k) ⟶ B'.left := P₂.lift (spMap (constHom ρ) ≫ s.left) (𝟙 _) wσ
  have hσ1 : σ ≫ π₂ = spMap (constHom ρ) ≫ s.left := P₂.lift_fst _ _ _
  have hσ2 : σ ≫ B'.hom = 𝟙 _ := P₂.lift_snd _ _ _
  let σo : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B' := Over.homMk σ hσ2
  have tx := GlobalTheory.T.groupPullback_translation_comp_eq B' A (spMap ρ) π₁ h₁ xo s hx1
  have tσ := GlobalTheory.T.groupPullback_translation_comp_eq B' A (spMap (constHom ρ)) π₂ h₂ σo s hσ1
  have hTBσ : TB = (lift (toUnit B' ≫ σo) (𝟙 B') ≫ μ[B']).left := by
    refine P₂.hom_ext ?_ ?_
    · rw [tσ, ← hr1, ← Category.assoc, hTB1, Category.assoc, hT₀, ← Category.assoc]
    · rw [hTB2, Over.w]
  have hcα : αo ≫ (lift (toUnit B' ≫ xo) (𝟙 B') ≫ μ[B']) = (lift (toUnit B' ≫ σo) (𝟙 B') ≫ μ[B']) ≫ αo := by
    apply Over.OverMorphism.ext
    refine P₁.hom_ext ?_ ?_
    · show α ≫ (lift (toUnit B' ≫ xo) (𝟙 B') ≫ μ[B']).left ≫ π₁ =
        (lift (toUnit B' ≫ σo) (𝟙 B') ≫ μ[B']).left ≫ α ≫ π₁
      rw [tx, ← Category.assoc, hα1, ← hcΦ, hTBσ]
    · simp only [Over.comp_left, Category.assoc, Over.w]
  haveI : IsCommMonObj B' := hB'.comm
  have hτ : ∀ (u y : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B'), y ≫ (lift (toUnit B' ≫ u) (𝟙 B') ≫ μ[B']) = u * y := by
    intro u y
    rw [← Category.assoc, comp_lift, ← Category.assoc, toUnit_unique (y ≫ toUnit B') (𝟙 _), Category.id_comp,
      Category.comp_id, ← Hom.mul_def]
  have h1 : (η[B'] : 𝟙_ _ ⟶ B') = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have e1 : η[B'] ≫ αo ≫ (lift (toUnit B' ≫ xo) (𝟙 B') ≫ μ[B']) = xo * w := by
    rw [← Category.assoc, ← hw, hτ]
  have e2 : η[B'] ≫ (lift (toUnit B' ≫ σo) (𝟙 B') ≫ μ[B']) ≫ αo = w * σo := by
    rw [← Category.assoc, hτ, h1, _root_.mul_one]
    nth_rewrite 1 [hαo]
    rw [hτ]
  have key : xo * w = w * σo := by
    rw [← e1, ← e2]
    exact congrArg (η[B'] ≫ ·) hcα
  have hxσ : xo = σo := by
    rw [_root_.mul_comm w σo] at key
    exact _root_.mul_right_cancel key
  have : x = σ := congrArg Over.Hom.left hxσ
  rw [this, hσ1]

end GlobalTheory.TranslHoriz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationHorizontalOfCommutingHeatOperators
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtsHoriz

theorem transl_horizontal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r)))  → ∀ (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (y : P.D.toPre.X) (x : Sp (DualNumber k) ⟶ B'.left), x ≫ B'.hom = 𝟙 _ → x ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left → x ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab
  letI := H.starRing
  intro Y n' v' dd hdd D q hq h hbas hdef hΘ ρ hρ B' _ π₁ π₂ h₁ h₂ hcl y x hx hx₁
  obtain ⟨_, hA₀, -, -⟩ := GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback _ _
    ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) P.D.toPre.P.A _ _ _
    (IsPullback.of_hasPullback P.D.toPre.P.A.hom (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)))
  obtain ⟨dl, hdl, hcomm⟩ := GlobalTheory.HeatTranslW.lift_commutes_translation E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hbas hdef hΘ ρ hρ _ _ _ hA₀
  have hw : (pullback.fst P.D.toPre.P.A.hom (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) ≫
      (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left) ≫ P.D.toPre.P.A.hom =
      pullback.snd _ _ ≫ spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) := by
    rw [Category.assoc, Over.w, pullback.condition]
  let T₀ := pullback.lift _ _ hw
  exact GlobalTheory.TranslHoriz.isHoriz_of_comm k _ P.D.toPre.P.A P.D.toPre.P.isAb ρ B' _ π₁ π₂ h₁ h₂ hcl _ _ _ hA₀ dl hdl (P.D.toPre.c y) T₀
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (hcomm y T₀ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)) x hx hx₁

end GlobalTheory.PtsHoriz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationHorizontalOfCommutingHeatOperatorsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translation_horizontal_of_commuting_heatOperators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r)))  → ∀ (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (y : P.D.toPre.X) (x : Sp (DualNumber k) ⟶ B'.left), x ≫ B'.hom = 𝟙 _ → x ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left → x ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left := by
  first | exact @GlobalTheory.PtsHoriz.transl_horizontal | exact GlobalTheory.PtsHoriz.transl_horizontal | (intros; apply GlobalTheory.PtsHoriz.transl_horizontal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorsSymbolZeroTorsionPointsHorizontal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatPts

theorem exists_horizontal_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ y : P.D.toPre.X, ∃ c' : Sp (DualNumber k) ⟶ B'.left, c' ≫ B'.hom = 𝟙 _ ∧ c' ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left := by
  intro E _ _ _ H k _ _ m d t P gam hM hli hab Y n' v' dd hdd D q hD h hB hH hΘ ρ hρ B' _ π₁ π₂ h₁ h₂ h12 y
  have hw : (spMap ρ ≫ (P.D.toPre.c y).left) ≫ P.D.toPre.P.A.hom = 𝟙 _ ≫ spMap ρ := by
    rw [Category.assoc, Over.w]; simp
  refine ⟨h₁.1.lift (spMap ρ ≫ (P.D.toPre.c y).left) (𝟙 _) hw, h₁.1.lift_snd _ _ _, h₁.1.lift_fst _ _ _, ?_⟩
  exact GlobalTheory.T.translation_horizontal_of_commuting_heatOperators E H k m d t P gam hM hli hab Y n' v' dd hdd D q hD h hB hH hΘ ρ hρ B' inferInstance π₁ π₂ h₁ h₂ h12 y _
    (h₁.1.lift_snd _ _ _) (h₁.1.lift_fst _ _ _)

end GlobalTheory.HeatPts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorsSymbolZeroTorsionPointsHorizontalStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperators_symbol_zero_torsion_points_horizontal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ y : P.D.toPre.X, ∃ c' : Sp (DualNumber k) ⟶ B'.left, c' ≫ B'.hom = 𝟙 _ ∧ c' ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left := by
  first | exact @GlobalTheory.HeatPts.exists_horizontal_section | exact GlobalTheory.HeatPts.exists_horizontal_section | (intros; apply GlobalTheory.HeatPts.exists_horizontal_section <;> assumption)
end

module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChange
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KTrivOfLamEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelWithCmAction

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.DualMapCompAlgebraMap
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsLieNormSqBaseChange
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj UpperHalfPlane nonZeroDivisors

namespace GlobalTheory.CMPeriodCompare

section Analytic

set_option autoImplicit false in
theorem _root_.GlobalTheory.CMPeriodCompare.isDerivAt0_comp_linear {g g' : ℕ} {X : Scheme.{0}} {e : (Fin g → ℂ) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X)}
    (he : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo Set.univ e) (L : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) {w : Fin g' → ℂ}
    {v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ X} (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 e (L w) v) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => e (L z)) w v := by
  rw [_root_.GlobalTheory.FibreDeriv.isDerivAt0_iff] at h ⊢
  obtain ⟨h0, h1⟩ := h
  refine ⟨by simpa using h0, fun U hU f => ?_⟩
  rw [h1 U hU f]
  have hU0 : ⊤ ≤ e 0 ⁻¹ᵁ U := by
    rw [← h0]
    intro x _
    exact hU (by trivial)
  have hd := _root_.GlobalTheory.LocalLift.hol_differentiableAt he (Set.mem_univ 0) hU0 f
  unfold _root_.GlobalTheory.FibreDeriv.jet
  simp only [map_zero]
  congr 2
  have hd' : DifferentiableAt ℂ (fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e z) U f)
      (LinearMap.toContinuousLinearMap L 0) := by
    simpa using hd
  have hc := hd'.hasFDerivAt.comp (0 : Fin g' → ℂ) (LinearMap.toContinuousLinearMap L).hasFDerivAt
  rw [show (fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e (L z)) U f) =
      (fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (e z) U f) ∘ (LinearMap.toContinuousLinearMap L) from rfl, hc.fderiv]
  simp

variable {R : Type} [CommRing R] {s : R →+* ℂ} {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp ℂ)}
  {φ : P'.A.left ⟶ P.A.left}

set_option autoImplicit false in
private theorem isDerivAt0_ex_of_isDiff_tangent (u : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif P'.A P'.L P'.g)
    {t : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR ℂ ⟶ P'.A} (ht : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent t) {w : Fin P'.g → ℂ} (hw : u.IsDiff w t) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => (u.ex z).left) w t.left := by
  have h0 : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t.left = (u.ex 0).left := by
    rw [_root_.GlobalTheory.TangentOrigin.ex_zero_left]
    exact ht
  rw [_root_.GlobalTheory.FibreDeriv.isDerivAt0_iff]
  refine ⟨h0, fun U h f => ?_⟩
  ext
  · rw [_root_.GlobalTheory.FibreDeriv.fst_evEps _ _ h0, _root_.GlobalTheory.FibreDeriv.fst_jet]
  · have := hw U h f
    unfold _root_.GlobalTheory.FibreDeriv.jet
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    rw [← this]
    rfl

set_option autoImplicit false in
theorem _root_.GlobalTheory.CMPeriodCompare.isDerivAt0_line (u : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif P'.A P'.L P'.g) {t : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR ℂ ⟶ P'.A}
    (ht : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent t) {w : Fin P'.g → ℂ} (hw : u.IsDiff w t) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (g := 1) (fun z => (u.ex (z 0 • w)).left ≫ φ) (fun _ => 1) (t.left ≫ φ) := by
  have hu := isDerivAt0_ex_of_isDiff_tangent u ht hw
  have he : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo Set.univ (fun z => (u.ex z).left) := by
    simpa using _root_.GlobalTheory.HomLinear.isHolTo_ex_comp u (𝟙 _)
  let L : (Fin 1 → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ) := (LinearMap.proj 0).smulRight w
  have hL : L (fun _ => 1) = w := by simp [L]
  rw [← hL] at hu
  exact _root_.GlobalTheory.FibreDeriv.isDerivAt0_comp (_root_.GlobalTheory.CMPeriodCompare.isDerivAt0_comp_linear he L hu) φ

variable {v : epsR R ⟶ P.A}

variable {ex : ℂ → (Over.mk (spMap s) ⟶ P.A)} {Λ : Submodule ℤ ℂ}

end Analytic

section Arithmetic

variable {K : Type} [Field K] [NumberField K]

end Arithmetic

section Data

variable (d : ℕ) (K : Type) [Field K] [NumberField K] {M : Type} [Field M] [NumberField M]

variable {d K}

end Data

section Main

variable {d : ℕ} {K : Type} [Field K] [NumberField K]

end Main

end GlobalTheory.CMPeriodCompare
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgf

section Rings

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem spMap_comp_spMap_sesquilinear_fractions (f : R →+* R') (f' : R' →+* R'') : spMap f' ≫ spMap f = spMap (f'.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem dualMap_comp_algebraMap_sesquilinear_fractions (f : R →+* R') :
    (dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f :=
  RingHom.ext fun x => TrivSqZeroExt.ext (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
    (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])

theorem fstHom_comp_dualMap' (f : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom :=
  RingHom.ext fun x => by simp [dualMap]

theorem fst_comp_algebraMap_dual : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R :=
  RingHom.ext fun x => by simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_dualMap_ring (f : R →+* R') (f' : R' →+* R'') : (dualMap f').comp (dualMap f) = dualMap (f'.comp f) := by
  ext x <;> simp [dualMap]

theorem dualMap_eq_dualMapR' (f : R →+* R') : dualMap f = ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f := RingHom.ext fun _ => rfl

end Rings

theorem mono_spec_fraction_field (K : Type) [Field K] [NumberField K] : Mono (spMap (algebraMap (𝓞 K) K)) := by
  haveI : Epi (CommRingCat.ofHom (algebraMap (𝓞 K) K)) := IsLocalization.epi (nonZeroDivisors (𝓞 K)) K
  show Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) K)).op)
  infer_instance

set_option maxHeartbeats 1000000 in
theorem cm_image_unique_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (a : PureType.lat hP (sgnRt H b)), (∃! u, X.IsImage b a u) ∧ ∀ u, X.IsImage b a u → IsTanAt Xo.univ.t.G _ u ∧ IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • P a) (spMap (dualMap (algebraMap X.K ℂ)) ≫ u.left) := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X b a
  have hmono := mono_spec_fraction_field X.K
  set φ : 𝓞 X.K →+* X.K := algebraMap (𝓞 X.K) X.K with hφ
  have hA : (X.C b).v.left ≫ (X.C b).P.A.hom = spMap (algebraMap (𝓞 X.K) (DualNumber (𝓞 X.K))) := Over.w (X.C b).v
  have hψ : (X.ψ b a).left ≫ X.B.t.G.hom = (X.C b).P.A.hom := Over.w (X.ψ b a)
  set F : Sp (DualNumber X.K) ⟶ X.B.t.G.left := spMap (dualMap φ) ≫ (X.C b).v.left ≫ (X.ψ b a).left with hFdef
  have hF : F ≫ X.B.t.G.hom = spMap (algebraMap X.K (DualNumber X.K)) ≫ spMap φ := by
    rw [hFdef, Category.assoc, Category.assoc, hψ, hA, spMap_comp_spMap_sesquilinear_fractions, spMap_comp_spMap_sesquilinear_fractions, dualMap_comp_algebraMap_sesquilinear_fractions]
  have m'c := X.m'.cart.1
  have mc := X.m.cart.1

  have hbase : ∀ r : Sp (DualNumber X.K) ⟶ X.t.G.left, r ≫ X.m'.φ = F →
      r ≫ X.t.G.hom = spMap (algebraMap X.K (DualNumber X.K)) := by
    intro r hr
    apply (cancel_mono (spMap φ)).1
    rw [Category.assoc, ← m'c.w, ← Category.assoc, hr, hF]
  refine ⟨?_, ?_⟩
  · let r₀ := m'c.lift F (spMap (algebraMap X.K (DualNumber X.K))) hF
    have hr₀ : r₀ ≫ X.m'.φ = F := m'c.lift_fst _ _ _
    have hr₀' : r₀ ≫ X.t.G.hom = spMap (algebraMap X.K (DualNumber X.K)) := m'c.lift_snd _ _ _
    let u₀ : epsAt (under X.y) ⟶ Xo.univ.t.G := Over.homMk (r₀ ≫ X.m.φ) (by
      show (r₀ ≫ X.m.φ) ≫ Xo.univ.t.G.hom = spMap (algebraMap X.K (DualNumber X.K)) ≫ under X.y
      rw [Category.assoc, mc.w, ← Category.assoc, hr₀'])
    refine ⟨u₀, ⟨r₀, rfl, hr₀⟩, ?_⟩
    rintro u ⟨r, hr1, hr2⟩
    have e : r = r₀ := m'c.hom_ext (hr2.trans hr₀.symm) ((hbase r hr2).trans hr₀'.symm)
    apply Over.OverMorphism.ext
    rw [← hr1, e]
    rfl
  · rintro u ⟨r, hr1, hr2⟩
    have hrb := hbase r hr2
    refine ⟨?_, ?_⟩
    ·
      have hs : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom X.K X.K X.K).toRingHom) ≫ r = η[X.t.G].left := by
        refine m'c.hom_ext ?_ ?_
        · rw [Category.assoc, hr2, GlobalTheory.UU.eSec_comp_of_isGrpPullback X.m'.cart]
          have ht : spMap (TrivSqZeroExt.fstHom (𝓞 X.K) (𝓞 X.K) (𝓞 X.K)).toRingHom ≫ (X.C b).v.left =
              η[(X.C b).P.A].left := (X.C b).basis.1 0
          have hmon : η[(X.C b).P.A].left ≫ (X.ψ b a).left = η[X.B.t.G].left := by
            have := ((X.fam b).1 a).isMonHom
            exact congrArg CommaMorphism.left (IsMonHom.one_hom (f := X.ψ b a))
          rw [← Category.assoc, spMap_comp_spMap_sesquilinear_fractions, fstHom_comp_dualMap', ← spMap_comp_spMap_sesquilinear_fractions, Category.assoc,
            reassoc_of% ht, hmon]
        · rw [Category.assoc, hrb]
          show spMap (TrivSqZeroExt.fstHom X.K X.K X.K).toRingHom ≫ spMap (algebraMap X.K (DualNumber X.K)) = _
          rw [spMap_comp_spMap_sesquilinear_fractions, fst_comp_algebraMap_dual, Over.w η[X.t.G]]
          exact Spec.map_id _
      show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom X.K X.K X.K).toRingHom) ≫ u.left = _
      rw [← hr1, ← Category.assoc, hs, GlobalTheory.UU.eSec_comp_of_isGrpPullback X.m.cart, Hom.one_def]
      rfl
    ·
      have hπ : X.π b ≫ (X.C b).P.A.hom = (Z b).C'.P.A.hom ≫ spMap ((algebraMap X.K ℂ).comp φ) :=
        (X.map' b).2.1.2.1.1.w
      have hvo : (Z b).C'.v.left ≫ X.π b =
          spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ((algebraMap X.K ℂ).comp φ)) ≫ (X.C b).v.left := (X.map' b).2.2.1
      have hw0 : (X.π b ≫ (X.ψ b a).left) ≫ X.B.t.G.hom =
          ((Z b).C'.P.A.hom ≫ spMap (algebraMap X.K ℂ)) ≫ spMap φ := by
        rw [Category.assoc, hψ, hπ, Category.assoc, spMap_comp_spMap_sesquilinear_fractions]
      let Φ₀ := m'c.lift (X.π b ≫ (X.ψ b a).left) ((Z b).C'.P.A.hom ≫ spMap (algebraMap X.K ℂ)) hw0
      have hΦ₁ : Φ₀ ≫ X.m'.φ = X.π b ≫ (X.ψ b a).left := m'c.lift_fst _ _ _
      have hΦ₂ : Φ₀ ≫ X.t.G.hom = (Z b).C'.P.A.hom ≫ spMap (algebraMap X.K ℂ) := m'c.lift_snd _ _ _
      have claim1 : ∀ s : ℂ, ((Z b).u.ex (fun _ => (Z b).c * s)).left ≫ Φ₀ ≫ X.m.φ = (FU.ex i P (s • P a)).left := by
        intro s
        have hx1 : (((Z b).u.ex (fun _ => (Z b).c * s)).left ≫ Φ₀) ≫ X.t.G.hom = spMap (algebraMap X.K ℂ) := by
          rw [Category.assoc, hΦ₂, ← Category.assoc, Over.w ((Z b).u.ex (fun _ => (Z b).c * s))]
          exact Category.id_comp _
        have hx2 : (((Z b).u.ex (fun _ => (Z b).c * s)).left ≫ Φ₀) ≫ X.m'.φ =
            ((Z b).u.ex (fun _ => (Z b).c * s)).left ≫ X.π b ≫ (X.ψ b a).left := by
          rw [Category.assoc, hΦ₁]
        rw [← Category.assoc]
        exact X.tie b a s _ hx1 hx2
      have claim2 : spMap (dualMap (algebraMap X.K ℂ)) ≫ u.left = (Z b).C'.v.left ≫ Φ₀ ≫ X.m.φ := by
        have key : spMap (dualMap (algebraMap X.K ℂ)) ≫ r = (Z b).C'.v.left ≫ Φ₀ := by
          refine m'c.hom_ext ?_ ?_
          · rw [Category.assoc, hr2, Category.assoc, hΦ₁, reassoc_of% hvo, ← dualMap_eq_dualMapR', ← Category.assoc,
              spMap_comp_spMap_sesquilinear_fractions, dualMap_comp_dualMap_ring]
          · rw [Category.assoc, hrb, Category.assoc, hΦ₂, ← Category.assoc, Over.w (Z b).C'.v, spMap_comp_spMap_sesquilinear_fractions,
              dualMap_comp_algebraMap_sesquilinear_fractions, ← spMap_comp_spMap_sesquilinear_fractions]
            rfl
        rw [← hr1, ← Category.assoc, key, Category.assoc]
      have hline := GlobalTheory.CMPeriodCompare.isDerivAt0_line (φ := 𝟙 (Z b).C'.P.A.left) (t := (Z b).C'.v) (Z b).u ((Z b).C'.basis.1 0) (Z b).diff
      have h2 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_comp_hom hline (Φ₀ ≫ X.m.φ)
      have hfun : (fun z : Fin 1 → ℂ => (((Z b).u.ex (z 0 • fun _ => (Z b).c * (Z b).z)).left ≫ 𝟙 _) ≫ Φ₀ ≫ X.m.φ) =
          fun z => (FU.ex i P ((z 0 * (Z b).z) • P a)).left := by
        funext z
        have e : (z 0 • fun _ => (Z b).c * (Z b).z) = (fun _ : Fin (Z b).C'.P.g => (Z b).c * (z 0 * (Z b).z)) := by
          funext k; simp only [Pi.smul_apply, smul_eq_mul]; ring
        rw [Category.comp_id, e, claim1]
      rw [hfun, Category.comp_id, ← claim2] at h2
      let Dl : (Fin 1 → ℂ) →ₗ[ℂ] (Fin g → ℂ) := (LinearMap.proj (0 : Fin 1) : (Fin 1 → ℂ) →ₗ[ℂ] ℂ).smulRight ((Z b).z • P a)
      have hhol : IsHolTo Set.univ (fun z => (FU.ex i P z).left) := by
        intro U f
        obtain ⟨h1, h2⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.anHol FU i P hP U f
        simp only [Set.mem_univ, true_and]
        exact ⟨h1, h2⟩
      have hDl : Dl (fun _ => 1) = (Z b).z • P a := by simp [Dl]
      have hDz : ∀ z, Dl z = (z 0 * (Z b).z) • P a := fun z => by simp [Dl, smul_smul]
      obtain ⟨v₀, hv₀, -⟩ := (FU.ex_diff i P hP).1 ((Z b).z • P a)
      have h3 := GlobalTheory.CMPeriodCompare.isDerivAt0_comp_linear hhol Dl (w := fun _ => 1) (v := v₀.left) (by rw [hDl]; exact hv₀)
      have h3' : IsDerivAt0 (fun z : Fin 1 → ℂ => (FU.ex i P ((z 0 * (Z b).z) • P a)).left) (fun _ => 1) v₀.left := by
        have e : (fun z => (FU.ex i P (Dl z)).left) =
            fun z : Fin 1 → ℂ => (FU.ex i P ((z 0 * (Z b).z) • P a)).left := funext fun z => by
          rw [hDz]
        rw [← e]; exact h3
      rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique h2 h3']
      exact hv₀

end PositivityTheory.Xgf
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmImageUniqueLattice
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmImageUniqueLattice
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cm_image_unique_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (a : PureType.lat hP (sgnRt H b)), (∃! u, X.IsImage b a u) ∧ ∀ u, X.IsImage b a u → IsTanAt Xo.univ.t.G _ u ∧ IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • P a) (spMap (dualMap (algebraMap X.K ℂ)) ≫ u.left) := by
  first | exact @PositivityTheory.Xgf.cm_image_unique_lattice | exact PositivityTheory.Xgf.cm_image_unique_lattice
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmImageUniqueLatticeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_image_unique_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (a : PureType.lat hP (sgnRt H b)), (∃! u, X.IsImage b a u) ∧ ∀ u, X.IsImage b a u → IsTanAt Xo.univ.t.G _ u ∧ IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • P a) (spMap (dualMap (algebraMap X.K ℂ)) ≫ u.left) := by
  exact @GlobalTheory.CompanionTheory.Relay.cm_image_unique_lattice
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackEigenPeriod
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.CoordPart

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

section Comb

variable {S : Scheme.{0}} {K C : Type} [CommRing K] [CommRing C]

theorem dualMap_comp_algebraMap' (φ : K →+* C) :
    (GlobalTheory.CompanionTheory.Ar.dualMap φ).comp (algebraMap K (DualNumber K)) = (algebraMap C (DualNumber C)).comp φ := by
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

def bcHom (φ : K →+* C) (x : Sp K ⟶ S) : epsAt (spMap φ ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ)) (by
    show spMap _ ≫ spMap _ ≫ x = spMap _ ≫ spMap _ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_algebraMap'])

theorem dual_epsMul (φ : K →+* C) (a : K) :
    spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ spMap (GlobalTheory.CompanionTheory.Ar.epsMul a) =
      spMap (GlobalTheory.CompanionTheory.Ar.epsMul (φ a)) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) := by
  rw [spMap_comp_spMap, spMap_comp_spMap]
  congr 1
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, mul_comm]

theorem comp_list_prod {G : Over S} [GrpObj G] {T T' : Over S} (f : T' ⟶ T) (l : List (T ⟶ G)) :
    f ≫ l.prod = (l.map (f ≫ ·)).prod := by
  induction l with
  | nil => simp [MonObj.comp_one]
  | cons a l ih => simp [MonObj.comp_mul, ih]

theorem comb_eq_pt {G : Over S} [GrpObj G] (φ : K →+* C) {x : Sp K ⟶ S} {x' : Sp C ⟶ S} (hx : spMap φ ≫ x = x')
    {U : Type} [AddCommGroup U] [Module C U] (M : LieModel G x' U) {n : ℕ} (c : Fin n → K)
    (u : Fin n → (epsAt x ⟶ G)) (w : epsAt x ⟶ G) (hc : IsComb c u w) (e : Fin n → U)
    (he : ∀ k, spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ (u k).left = (M.pt (e k)).left) :
    spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ w.left = (M.pt (∑ k, φ (c k) • e k)).left := by
  subst hx
  obtain ⟨u', hu', rfl⟩ := hc
  have key : IsComb (fun k => φ (c k)) (fun k => M.pt (e k)) (bcHom φ x ≫ (List.ofFn u').prod) := by
    refine ⟨fun k => bcHom φ x ≫ u' k, fun k => ?_, ?_⟩
    · show spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ (u' k).left = _
      rw [hu' k, ← Category.assoc, dual_epsMul, Category.assoc, he k]
    · rw [comp_list_prod, List.map_ofFn]
      rfl
  have := ((GlobalTheory.T.lie_model_eigenvectors_action S C G _ U M).1 n _ _ _).1 key
  exact congrArg (fun q => q.left) this

end Comb

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sum_eq_tyPart {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty P) (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ))
    (hρ : ∀ a w, ρ a w = fun k => ty k (a : E) * w k) (τ : E →+* ℂ)
    (hpr : ∀ w, HT.eigProj ρ τ w = tyPart ty τ w) (z : ℂ) {n : ℕ}
    (e : Fin n ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (a : D.La) :
    ∑ k, τ (HT.dualInt E (e k)) • (z • P (RingOfIntegers.basis E (e k) • a)) = z • tyPart ty τ (P a) := by
  have h1 : ∀ s : 𝓞 E, P (s • a) = ρ s (P a) := fun s => by
    rw [hρ]; funext j; exact hP.1 s a j
  rw [← hpr, HT.eigProj, LinearMap.sum_apply, Finset.smul_sum,
    ← Equiv.sum_comp e (fun q => z • (τ (HT.dualInt E q) • ρ (RingOfIntegers.basis E q)) (P a))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h1, smul_comm]
  rfl

theorem isDerivAt0_of_isCMVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (a : PureType.lat hP (sgnRt H b)) (v : epsAt (under X.y) ⟶ Xo.univ.t.G), X.IsCMVec b τ a v → IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • tyPart ty τ (P a)) (spMap (dualMap (algebraMap X.K ℂ)) ≫ v.left) := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X b τ a v hv
  obtain ⟨M, ρ, -, hρ, hder, hpr⟩ := GlobalTheory.T.lie_model_with_cm_action E H D l Xo c g ty FU i P hP
  obtain ⟨n, e, u, hu, hc⟩ := hv
  have hk : ∀ k, spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap X.K ℂ)) ≫ (u k).left =
      (M.pt ((Z b).z • P (RingOfIntegers.basis E (e k) • (a : (FU.Di i).La)))).left := fun k =>
    ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique
      ((GlobalTheory.T.cm_image_unique_lattice E H D l Xo c g ty FU i Z P hP X b _).2 (u k) (hu k)).2 (hder _)
  have h := comb_eq_pt (algebraMap X.K ℂ) X.pt M _ u v hc _ hk
  rw [h]
  have hs : ∑ k, (algebraMap X.K ℂ) (X.β (tauE c τ (HT.dualInt E (e k)))) •
      ((Z b).z • P (RingOfIntegers.basis E (e k) • (a : (FU.Di i).La))) = (Z b).z • tyPart ty τ (P a) :=
    sum_eq_tyPart hP ρ hρ τ (hpr τ) _ e a
  rw [hs]
  exact hder _

end Main

end GlobalTheory.CompanionTheory.Ar.Fl.CoordPart
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackEigenPeriodStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_pack_eigen_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (a : PureType.lat hP (sgnRt H b)) (v : epsAt (under X.y) ⟶ Xo.univ.t.G), X.IsCMVec b τ a v → IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • tyPart ty τ (P a)) (spMap (dualMap (algebraMap X.K ℂ)) ≫ v.left) := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X b τ a v hv
  exact GlobalTheory.CompanionTheory.Ar.Fl.CoordPart.isDerivAt0_of_isCMVec E H D l Xo c g ty FU i Z P hP X b τ a v hv
end

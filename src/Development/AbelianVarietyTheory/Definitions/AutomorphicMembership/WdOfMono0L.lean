module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host NumberField IsDedekindDomain Polynomial

instance factRes (D : D7) (lam : D.what₂.places.Pl) : Fact (D.what₂.places.resChar lam).Prime :=
  ⟨D.what₂.places.resChar_prime lam⟩

structure CharSide (D : D7) (C : CharFrame D) where
  e1 : D.naut.CG 1 ≃ {χ : HChar D.host.E // χ.IsUnitary}
  unr_iff : ∀ π w, D.naut.unr (D.naut.locG π w) ↔ (e1 π).1.UnrAt w
  frob : ∀ π w, (e1 π).1.UnrAt w → D.naut.frobEig (D.naut.locG π w) = {(((e1 π).1.val w)⁻¹ : ℂˣ).1}
  tw : ∀ π χ : D.naut.CG 1, (e1 (D.naut.tw π χ)).1 = (e1 π).1 * (e1 χ).1
  infG : ∀ π (a : D.R.Psi → ℚ), (e1 π).1.HasInfQ (embPsi D.host) a → ∀ g,
    D.naut.infG π (embPsi D.host g) = {(a g : ℂ)} ∧
      D.naut.infG π ((starRingEnd ℂ).comp (embPsi D.host g)) = {-(a g : ℂ)}
  csd : ∀ π : D.naut.CG 1, D.naut.csd π ↔ IsCSD D.host (e1 π).1
  etaT : (e1 D.naut.etaT).1 = C.eta
  etaTinv : (e1 D.naut.etaTinv).1 = C.eta⁻¹
  plGw : ∀ k v, C.P.Div k (D.naut.plGw k v)

structure RowSide (D : D7) where
  locR : D.what₂.FT → ∀ w, D.naut.LP w
  satR : D.what₂.FT → PlE D.host → Multiset ℂ
  lab_eq : ∀ k σ v, D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (locR σ (D.naut.plGw k v))

structure PlSide (D : D7) where
  ι : ∀ lam : D.what₂.places.Pl, Qbar (D.what₂.places.resChar lam) ≃+* ℂ
  ι_w : ∀ lam (x : D.what₂.LL), 0 ≤ D.what₂.places.val lam x ↔ ‖(ι lam).symm (D.what₂.embLL x)‖ ≤ 1
  plB : D.what₂.places.Pl → ValuationSubring ℂ
  plB_eq : ∀ lam (z : ℂ), z ∈ plB lam ↔ ‖(ι lam).symm z‖ ≤ 1
  plκ : ∀ lam, IsLocalRing.ResidueField (plB lam) ≃+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar lam)


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
structure WDSide (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) where
  wdOf : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a}, (G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) → ∀ w, D.naut.LP w
  wdOf_dim : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w, D.naut.lpDim (wdOf l ι r w) = a
  wdOf_unr : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w, w ∉ placesOver D.host.E l →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) →
    (D.naut.unr (wdOf l ι r w) ↔ ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), r σ = 1)
  wdOf_frob : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w, w ∉ placesOver D.host.E l →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) →
    D.naut.unr (wdOf l ι r w) → ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B w →
    IsFrob (F := D.host.E) B (normV w) σ →
    ((r σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map
        ι.toRingHom =
      ((D.naut.frobEig (wdOf l ι r w)).map fun α => X - C α).prod
  wdOf_ine : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w, w ∉ placesOver D.host.E l →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) →
    ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
    ((r σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map
        ι.toRingHom = D.naut.inePol (wdOf l ι r w) σ
  wdOf_mono0 : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w, w ∉ placesOver D.host.E l →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) →
    (D.naut.mono0 (wdOf l ι r w) ↔ (r '' (Ine (F := D.host.E) (D.nd.plOm.1 w) : Set (G D.host.E D.nd.Om))).Finite)
  IsCrysW : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a}, (G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) → PlE D.host → Prop
  IsPotCrysW : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a}, (G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) → PlE D.host → Prop
  IsdRW : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a}, (G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) → PlE D.host → Prop
  jumpsW : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a}, (G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) → (D.host.E →+* Qbar l) →
    Multiset ℤ
  wdOf_unrL : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w, w ∈ placesOver D.host.E l →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) →
    IsdRW l ι r w → (D.naut.unr (wdOf l ι r w) ↔ IsCrysW l ι r w)
  wdOf_mono0L : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w, w ∈ placesOver D.host.E l →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) →
    IsdRW l ι r w → (D.naut.mono0 (wdOf l ι r w) ↔ IsPotCrysW l ι r w)
  away : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w
    (hw : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
    T.e w (wdOf l ι r w) = GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι r
  above : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w,
    w ∈ placesOver D.host.E l → ∃ (LL : Loc.FinExt l)
      (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) ↥(Loc.OL LL))
      (hj : GlobalTheory.Pst.Induces Bw), T.e w (wdOf l ι r w) =
        GlobalTheory.Pst.wdAt (D.loc l) ι Bw (D.nd.plOm.2 w) hj (GlobalTheory.Pst.resDec D.nd.plOm.1 r w)
  loc : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : PlE D.host), w ∈ placesOver D.host.E l →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O),
      (∀ x : D.nd.Om, x ∈ D.nd.plOm.1 w ↔ ‖Bw.j x‖ ≤ 1) → ∀ φ : O →+* Qbar l,
      (∀ x : O, φ x = ((Bw.toLL x : ↥Bw.LL.1) : Loc.Om l)) →
    (∀ (m : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin m) (O)),
      Continuous (fun g => ((ρ g : GL (Fin m) (O)) : Matrix (Fin m) (Fin m) (O))) →
      (IsCrysW l ι (mapRep φ ρ) w ↔
        Bw.IsCrysW (D.loc l) (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)) ∧
      (IsdRW l ι (mapRep φ ρ) w ↔
        Bw.IsdRW (D.loc l) (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)) ∧
      (IsPotCrysW l ι (mapRep φ ρ) w ↔
        Bw.IsPotCrysW (D.loc l) (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)) ∧
      ∀ (τ : D.host.E →+* Qbar l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1),
        (∀ x : D.host.E, τ x = ((τ' ⟨Bw.j (algebraMap D.host.E D.nd.Om x), Bw.j_E x⟩ :
          ↥Bw.LL.1) : Loc.Om l)) →
        (Bw.IsdRW (D.loc l) (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) →
          ∀ a : ℤ, a ∈ jumpsW l ι (mapRep φ ρ) τ ↔
          Bw.IsJumpW (D.loc l) (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ' a) ∧
        (Bw.IsdRW (D.loc l) (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) →
          ∀ a : ℤ, ((jumpsW l ι (mapRep φ ρ) τ).count a : ℤ) =
            Bw.multW (D.loc l) (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ' a)) ∧
    ∀ (LL' : Loc.FinExt l), Bw.LL.1 ≤ LL'.1 →
      ∀ (m : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin m) ↥LL'.1),
      Continuous (fun g => ((ρ g : GL (Fin m) ↥LL'.1) : Matrix (Fin m) (Fin m) ↥LL'.1)) →
      (IsCrysW l ι (mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ) w ↔
        Bw.IsCrysE (D.loc l) LL' (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)) ∧
      (IsdRW l ι (mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ) w ↔
        Bw.IsdRE (D.loc l) LL' (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)) ∧
      (IsPotCrysW l ι (mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ) w ↔
        Bw.IsPotCrysE (D.loc l) LL' (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)) ∧
      ∀ (τ : D.host.E →+* Qbar l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1),
        (∀ x : D.host.E, τ x = ((τ' ⟨Bw.j (algebraMap D.host.E D.nd.Om x), Bw.j_E x⟩ :
          ↥LL'.1) : Loc.Om l)) →
        (Bw.IsdRE (D.loc l) LL' (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) →
          ∀ a : ℤ, a ∈ jumpsW l ι (mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ) τ ↔
          Bw.IsJumpE (D.loc l) LL' (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ' a) ∧
        (Bw.IsdRE (D.loc l) LL' (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) →
          ∀ a : ℤ, ((jumpsW l ι (mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ) τ).count a : ℤ) =
            Bw.multE (D.loc l) LL' (ρ.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ' a)

def qCast {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (ι : Qbar p ≃+* ℂ) : Qbar q ≃+* ℂ := by
  subst h; exact ι

def LabTrue (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) : Prop :=
  ∀ k v (a : D.naut.LP (D.naut.plGw k v)), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    D.naut.items₂ k (D.naut.plGw k v) a = GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (T.e _ a)

end GlobalTheory.HeightCounting

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TopForm Formalism.BasicNotions
open scoped ComplexOrder

namespace GlobalTheory.TrueGeo

namespace Res

section Val

variable {K K' : Type} [Field K] [Field K'] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) {f g : Z.functionField}

theorem valAt_algebraMap (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dite_eq_left h, IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec]

variable {y}

theorem valAt_pow (hf : RegAt (below y) f) (m : ℕ) : valAt y (f ^ m) = valAt y f ^ m := by
  obtain ⟨a, rfl⟩ := hf
  rw [← map_pow, valAt_algebraMap, valAt_algebraMap, map_pow]

theorem valAt_ne_zero (hf : UnitAt (below y) f) : valAt y f ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [valAt_algebraMap]
  exact (ha.map _).ne_zero

variable (y)


omit [IsIntegral Z] in
theorem below_comp (φ : K →+* K') : below (spMap φ ≫ y) = below y := by
  exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg y (Subsingleton.elim (α := PrimeSpectrum K) _ _))

theorem valAt_comp (φ : K →+* K') (f : Z.functionField) : valAt (spMap φ ≫ y) f = φ (valAt y f) := by
  by_cases h : RegAt (below y) f
  · obtain ⟨U, hU, a, rfl⟩ := h.exists_fnOf
    have hU' : below (spMap φ ≫ y) ∈ U := (below_comp y φ).symm ▸ hU
    have e : spMap φ ≫ y =
        Spec.map (Scheme.stalkClosedPointTo y ≫ CommRingCat.ofHom φ) ≫ Z.fromSpecStalk (below y) := by
      rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
    have : IsLocalHom (Scheme.stalkClosedPointTo y ≫ CommRingCat.ofHom φ).hom := by
      rw [CommRingCat.hom_comp]
      exact RingHom.isLocalHom_comp φ _
    conv_rhs => rw [← algebraMap_germ hU a, valAt_algebraMap]
    rw [← algebraMap_germ hU' a, valAt_algebraMap]
    revert hU'
    rw [e]
    intro hU'
    exact congrArg (fun q => q.hom a) (Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
      (Scheme.stalkClosedPointTo y ≫ CommRingCat.ofHom φ) U hU')
  · rw [valAt, valAt, dite_eq_right h, dite_eq_right ((below_comp y φ).symm ▸ h), map_zero]


variable {y} in
theorem valAt_fnOf {U : Z.Opens} (hy : below y ∈ U) (h : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    valAt y (fnOf U h a) = TangentOrigin.evalPt y U ((Points.le_preimage_iff _ _).2 hy) a := by
  rw [← algebraMap_germ hy a, valAt_algebraMap]
  exact congrArg (fun q => q.hom a) (Scheme.germ_stalkClosedPointTo y U hy)

theorem ratVal_eq_valAt {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ} (z : CxPts q σ)
    (hf : RegAt (under z) f) : ratVal f z = valAt z.1 f := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  rw [ratVal_fnOf (CxPts.mem_ptsIn.2 hU), valAt_fnOf hU, CxPts.ev_eq (CxPts.mem_ptsIn.2 hU)]
  rfl

end Val

end Res

open Res

variable {F : Type} [Field F] [NumberField F] (Y : Var F)

def jacRat (u : Fin Y.dim → Y.Fn) : Y.Fn :=
  (isFreeGen_baseForm Y.str Y.dim).repr (dForm (Cartier.constFn Y.str) u)

variable (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ} (w : Fin n → Y.Fn)
  (c : Fin Y.dim → Fin n → 𝓞 E)

instance galAction : MulAction (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) (GeomPt Y E) where
  smul σ y := ⟨spMap (σ : AlgebraicClosure E →+* AlgebraicClosure E) ≫ y.1, by
    rw [Category.assoc, y.2, ← spMap_comp]
    exact congrArg spMap (RingHom.ext fun a => σ.commutes _)⟩
  one_smul y := Subtype.ext ((congrArg (· ≫ y.1) (Spec.map_id _)).trans (Category.id_comp _))
  mul_smul σ τ y := Subtype.ext (by
    change spMap _ ≫ y.1 = spMap _ ≫ spMap _ ≫ y.1
    rw [← Category.assoc, ← spMap_comp]
    rfl)

section Gal

variable {Y E} (σ : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) (y : GeomPt Y E)


omit [NumberField F] [NumberField E] in
theorem below_smul : below (σ • y).1 = below y.1 := below_comp _ _


omit [NumberField F] [NumberField E] in
theorem valAt_smul (f : Y.Fn) : valAt (σ • y).1 f = σ (valAt y.1 f) := valAt_comp _ _ _


omit [NumberField F] [NumberField E] [Algebra F E] in
theorem map_coef (i : Fin Y.dim) (l : Fin n) : σ (coef Y E c i l) = coef Y E c i l := σ.commutes _


omit [NumberField F] [NumberField E] in
variable {w c y} in
theorem smul_mem_cutSet (hy : y ∈ cutSet Y E w c) : σ • y ∈ cutSet Y E w c := fun k hk i => by
  have := congrArg σ (hy k (below_smul σ y ▸ hk) i)
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_sum, map_mul, map_coef, map_zero, valAt_smul] using this

end Gal

instance galActionCut : MulAction (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) (cutSet Y E w c) where
  smul σ y := ⟨σ • y.1, smul_mem_cutSet σ y.2⟩
  one_smul y := Subtype.ext (one_smul _ y.1)
  mul_smul σ τ y := Subtype.ext (mul_smul σ τ y.1)

def cutSec : Submodule E (cutSet Y E w c → AlgebraicClosure E) where
  carrier := {g | ∀ (σ : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) y, g (σ • y) = σ (g y)}
  zero_mem' _ _ := (map_zero _).symm
  add_mem' hf hg σ y := by rw [Pi.add_apply, Pi.add_apply, hf, hg, map_add (f := _)]
  smul_mem' a g hg σ y := by rw [Pi.smul_apply, Pi.smul_apply, hg, Algebra.smul_def, Algebra.smul_def, map_mul, σ.commutes]

def dsVal (y : GeomPt Y E) (k : Fin n) (g : Y.Fn) : AlgebraicClosure E :=
  ∑ l : Fin Y.dim → Fin n, (∏ i, coef Y E c i (l i)) * valAt y.1 (jacRat Y (fun i => w (l i) / w k) * g)

def resAt (f : Y.Fn) (y : GeomPt Y E) (k : Fin n) (g e : Y.Fn) : AlgebraicClosure E :=
  valAt y.1 (f * e * g / w k ^ Y.dim) / dsVal Y E w c y k g


open Classical in
def genIdx (x : Y.X) : Option (Fin n) := if h : ∃ k, GenAt Y w x k then some h.choose else none

def resVal (Δ : Y.Dv) (f : Y.Fn) (y : GeomPt Y E) : AlgebraicClosure E :=
  (genIdx Y w (below y.1)).elim 0 fun k => resAt Y E w c f y k (eqn Y.KY (below y.1)) (eqn Δ (below y.1))

def ResReg (Δ : Y.Dv) (f : Y.Fn) (x : Y.X) : Prop :=
  ∃ k, GenAt Y w x k ∧ (Δ + Y.KY).RegularAt x (f / w k ^ Y.dim)

section Indep

variable {Y E w c} {x : Y.X} {y : GeomPt Y E} {k k' : Fin n} {g g' e : Y.Fnˣ} {Δ : Y.Dv} {f f' : Y.Fn}



omit [NumberField F] in
theorem isEqn_eqn (Δ : Y.Dv) (x : Y.X) : Δ.IsEqn x (eqn Δ x) := (Δ.exists_isEqn x).choose_spec



omit [NumberField F] [NumberField E] in
theorem dsVal_pick {l : Fin Y.dim → Fin n} (hc : ∀ i j, c i j = if j = l i then 1 else 0) (g : Y.Fn) :
    dsVal Y E w c y k g = valAt y.1 (jacRat Y (fun i => w (l i) / w k) * g) := by
  rw [dsVal, Finset.sum_eq_single l _ (by simp)]
  · simp [coef, hc]
  · intro l' _ hl
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hl
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [coef, hc, hi]), zero_mul]



omit [NumberField F] [NumberField E] in
theorem resVal_smul (σ : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) (Δ : Y.Dv) (f : Y.Fn) (y : GeomPt Y E) :
    resVal Y E w c Δ f (σ • y) = σ (resVal Y E w c Δ f y) := by
  rw [resVal, resVal, below_smul]
  cases genIdx Y w (below y.1) with
  | none => exact (map_zero σ).symm
  | some k => simp only [Option.elim, resAt, dsVal, valAt_smul, map_div₀, map_sum, map_mul, map_prod, map_coef]

end Indep

def resSec (Δ : Y.Dv) (f : Y.Fn) : cutSec Y E w c :=
  ⟨fun y => resVal Y E w c Δ f y.1, fun σ y => resVal_smul σ Δ f y.1⟩

section Herm

variable {Y E}

def cxPt {τ : E →+* ℂ} {τ' : AlgebraicClosure E →+* ℂ} (h : τ'.comp (algebraMap E _) = τ) (y : GeomPt Y E) :
    Pts Y (τ.comp (algebraMap F E)) :=
  ⟨spMap τ' ≫ y.1, by rw [Category.assoc, y.2, ← spMap_comp, ← RingHom.comp_assoc, h]⟩

variable {C : CxSt F} (A : Adl C Y)

def Adl.frameSq (σ : F →+* ℂ) (z : Pts Y σ) : ℝ :=
  Real.exp (-(2 * (A.n : ℕ) * A.ci (InfinitePlace.mk σ))) *
    C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D (under z))⁻¹ : Y.Fnˣ)) z

def cutFormAt {τ : E →+* ℂ} {τ' : AlgebraicClosure E →+* ℂ} (h : τ'.comp (algebraMap E _) = τ)
    (g g' : cutSec Y E w c) : ℂ :=
  ∑ᶠ y : cutSet Y E w c, τ' (g.1 y) * starRingEnd ℂ (τ' (g'.1 y)) * (A.frameSq _ (cxPt h y.1) : ℝ)

def cutForm (τ : E →+* ℂ) (g g' : cutSec Y E w c) : ℂ :=
  cutFormAt w c A (ComplexEmbedding.lift_comp_algebraMap (AlgebraicClosure E) τ) g g'

def IsCutHerm (H : ReciprocityTheory.GeometryOfNumbersTheory.HermFam E (cutSec Y E w c)) : Prop := ∀ τ g g', H.form τ g g' = cutForm w c A τ g' g



open Classical in
def cutDeg (Λ : Submodule (𝓞 E) (cutSec Y E w c)) : ℝ :=
  if h : ∃ H, IsCutHerm w c A H then ReciprocityTheory.GeometryOfNumbersTheory.deg h.choose Λ else 0

end Herm

variable [StarRing F] (M0 : HLat F) (ι₀ : M0.V →ₗ[F] Y.Fn)

def resLat (Δ : Y.Dv) : Submodule (𝓞 E) (cutSec Y E w c) :=
  Submodule.span (𝓞 E) ((fun m => resSec Y E w c Δ (ι₀ m)) '' (M0.L : Set M0.V))

variable {C : CxSt F} (A : Adl C Y)

def resFull : Prop :=
  (∀ m ∈ M0.L, ∀ y ∈ cutSet Y E w c, ResReg Y w A.D (ι₀ m) (below y.1)) ∧ (resLat Y E w c M0 ι₀ A.D).FG ∧
    Submodule.span E (resLat Y E w c M0 ι₀ A.D : Set (cutSec Y E w c)) = ⊤

def resDeg : ℝ := cutDeg w c A (resLat Y E w c M0 ι₀ A.D)

def resSt (C : CxSt F) : ResSt C where
  resFull := fun Y E _ _ _ _ w c M0 ι₀ A => resFull Y E w c M0 ι₀ A
  resDeg := fun Y E _ _ _ _ w c M0 ι₀ A => resDeg Y E w c M0 ι₀ A

section OnePoint

variable {Y E w c} [Unique (cutSet Y E w c)]

end OnePoint

end GlobalTheory.TrueGeo
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MapSeqIndAll
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def castV {A B : HLat K} (h : A = B) : A.V ≃ₗ[K] B.V := by
  subst h
  exact LinearEquiv.refl K A.V

def unitLat (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) : HLat K :=
  HLat.ofCoord (Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n)))) fun _ => 1

theorem ofCoord_good {d : ℕ} {L : Submodule (𝓞 K) (Fin d → K)} {X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ}
    (hL : Submodule.IsFullLattice K L) (hX : ∀ v, IsUnit (X v).det) : (HLat.ofCoord L X).Good :=
  ⟨hX, hL.toIsLattice.fg, hL.span_eq_top⟩

theorem unitLat_good (n : ℕ) : (unitLat K n).Good :=
  ⟨fun _ => by
      show IsUnit (1 : Matrix (Fin n) (Fin n) ℂ).det
      rw [Matrix.det_one]; exact isUnit_one,
    Submodule.fg_span (Set.finite_range _),
    (Submodule.span_span_of_tower (𝓞 K) K (Set.range (Pi.basisFun K (Fin n)))).trans (Pi.basisFun K (Fin n)).span_eq⟩

def unitMap (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] :
    (unitLat K (Module.finrank ℂ W)).V →ₛₗ[σ] W :=
  (lin (stdOrthonormalBasis ℂ W)).comp (cptL σ (Module.finrank ℂ W))

theorem unitMap_b (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (k : Fin (Module.finrank ℂ W)) :
    unitMap σ W ((unitLat K (Module.finrank ℂ W)).b k) = stdOrthonormalBasis ℂ W k := by
  have h : cptL σ (Module.finrank ℂ W) (Pi.basisFun K _ k) = Pi.single k 1 := by
    funext i
    by_cases hi : i = k <;> simp [cptL, cpt, hi]
  exact (congrArg (lin (stdOrthonormalBasis ℂ W)) h).trans (lin_single _ k)

theorem unitMap_basis (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] :
    LinearIndependent ℂ (fun k => unitMap σ W ((unitLat K (Module.finrank ℂ W)).b k)) ∧
      Submodule.span ℂ (Set.range fun k => unitMap σ W ((unitLat K (Module.finrank ℂ W)).b k)) = ⊤ := by
  have h : (fun k => unitMap σ W ((unitLat K (Module.finrank ℂ W)).b k)) = (stdOrthonormalBasis ℂ W).toBasis :=
    funext fun k => unitMap_b σ W k
  rw [h]
  exact ⟨(stdOrthonormalBasis ℂ W).toBasis.linearIndependent, (stdOrthonormalBasis ℂ W).toBasis.span_eq⟩

theorem hLatTie_castV {d : ℕ} {L : Submodule (𝓞 K) (Fin d → K)} {X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ} {A : HLat K}
    (h : HLat.ofCoord L X = A) : HLatTie A L X (castV h) := by
  subst h
  exact ⟨(Submodule.map_id L).symm, fun _ _ _ => rfl⟩

variable {m : ℕ} {d : Fin m → ℕ} (M : ∀ i, Submodule (𝓞 K) (Fin (d i) → K))
  (X : ∀ i, InfinitePlace K → Matrix (Fin (d i)) (Fin (d i)) ℂ)
  (W : ℕ → Type) [∀ j, NormedAddCommGroup (W j)] [∀ j, InnerProductSpace ℂ (W j)] [∀ j, FiniteDimensional ℂ (W j)]

def latSeq : ℕ → HLat K
  | 0 => unitLat K (Module.finrank ℂ (W 0))
  | j + 1 => if h : j < m then HLat.ofCoord (M ⟨j, h⟩) (X ⟨j, h⟩) else unitLat K (Module.finrank ℂ (W (j + 1)))

theorem latSeq_succ (i : Fin m) : latSeq M X W ((i : ℕ) + 1) = HLat.ofCoord (M i) (X i) := dif_pos i.2

theorem latSeq_off {j : ℕ} (h : j = 0 ∨ m < j) : latSeq M X W j = unitLat K (Module.finrank ℂ (W j)) := by
  cases j with
  | zero => rfl
  | succ j => exact dif_neg (by omega)

variable {σ : K →+* ℂ} (f : ∀ i : Fin m, (Fin (d i) → K) →ₛₗ[σ] W ((i : ℕ) + 1))

def mapSeq : ∀ j, (latSeq M X W j).V →ₛₗ[σ] W j
  | 0 => unitMap σ (W 0)
  | j + 1 =>
    if h : j < m then (f ⟨j, h⟩).comp (castV (latSeq_succ M X W ⟨j, h⟩)).toLinearMap
    else (unitMap σ (W (j + 1))).comp (castV (latSeq_off M X W (Or.inr (Nat.lt_succ_of_le (Nat.le_of_not_lt h))))).toLinearMap

theorem mapSeq_succ (i : Fin m) :
    mapSeq M X W f ((i : ℕ) + 1) = (f i).comp (castV (latSeq_succ M X W i)).toLinearMap := dif_pos i.2

theorem mapSeq_off {j : ℕ} (h : j = 0 ∨ m < j) :
    mapSeq M X W f j = (unitMap σ (W j)).comp (castV (latSeq_off M X W h)).toLinearMap := by
  cases j with
  | zero => rfl
  | succ j => exact dif_neg (by omega)

theorem castV_ind {H : Type} [AddCommGroup H] [Module ℂ H] (P : ∀ A : HLat K, (A.V →ₛₗ[σ] H) → Prop) {A B : HLat K} (h : A = B)
    {g : B.V →ₛₗ[σ] H} (hg : P B g) : P A (g.comp (castV h).toLinearMap) := by
  subst h
  exact hg

theorem mapSeq_ind (P : ∀ (j : ℕ) (A : HLat K), (A.V →ₛₗ[σ] W j) → Prop)
    (hP : ∀ i : Fin m, P ((i : ℕ) + 1) (HLat.ofCoord (M i) (X i)) (f i)) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ m) :
    P j (latSeq M X W j) (mapSeq M X W f j) := by
  obtain ⟨i, rfl⟩ : ∃ i : Fin m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  rw [mapSeq_succ]
  exact castV_ind (P _) _ (hP i)

theorem mapSeq_ind_all (P : ∀ (j : ℕ) (A : HLat K), (A.V →ₛₗ[σ] W j) → Prop)
    (hP : ∀ i : Fin m, P ((i : ℕ) + 1) (HLat.ofCoord (M i) (X i)) (f i))
    (h0 : ∀ j, P j (unitLat K (Module.finrank ℂ (W j))) (unitMap σ (W j))) (j : ℕ) :
    P j (latSeq M X W j) (mapSeq M X W f j) := by
  by_cases h : j = 0 ∨ m < j
  · rw [mapSeq_off M X W f h]
    exact castV_ind (P _) _ (h0 j)
  · exact mapSeq_ind M X W f P hP j (by omega) (by omega)

theorem map_castV {H : ℕ → HLat K} {g : ∀ j, (H j).V →ₛₗ[σ] W j} (hH : H = latSeq M X W) (hg : HEq g (mapSeq M X W f))
    (i : Fin m) (h : HLat.ofCoord (M i) (X i) = H ((i : ℕ) + 1)) (x : Fin (d i) → K) :
    g ((i : ℕ) + 1) (castV h x) = f i x := by
  subst hH
  obtain rfl := eq_of_heq hg
  rw [mapSeq_succ]
  have key : ∀ {A B : HLat K} (h : A = B) (h' : B = A) (y : A.V), castV h' (castV h y) = y := by
    intro A B h h' y
    subst h
    rfl
  exact congrArg (f i) (key h _ x)

end Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}

open MjCoord

def mjLat (R : RealDat3 D A3 Ks) (F : Face3 D A3) : ℕ → HLat D.what₂.LL :=
  latSeq (m := D.R.m) (d := fun i => (s0Of R F).dW i) (fun i => (s0Of R F).M i) (fun i => (s0Of R F).XW i) D.what₂.Mj

def mjH (_Z : ReadL R F X0 Y) (j : ℕ) : HLat D.what₂.LL := mjLat R F j

def jM (Z : ReadL R F X0 Y) (j : ℕ) : (mjH Z j).V →ₛₗ[D.what₂.embLL] D.what₂.Mj j :=
  mapSeq (m := D.R.m) (d := fun i => (s0Of R F).dW i) (fun i => (s0Of R F).M i) (fun i => (s0Of R F).XW i) D.what₂.Mj Z.jW j

variable (Z : ReadL R F X0 Y)

theorem mjH_succ (i : Fin D.R.m) : mjH Z ((i : ℕ) + 1) = HLat.ofCoord ((s0Of R F).M i) ((s0Of R F).XW i) :=
  latSeq_succ _ _ _ i

theorem mjH_good (hH : Holds R F) (j : ℕ) : (mjH Z j).Good :=
  mapSeq_ind_all _ _ D.what₂.Mj Z.jW (fun _ A _ => A.Good)
    (fun i => by
      exact ofCoord_good (hH.prim.mLat i) fun v =>
        frame_gram_unit _ (RealDat3.kForm_of (F := F) hH.prim.unif false i v).1)
    (fun _ => unitLat_good _) j

theorem jM_basis (hH : Holds R F) (j : ℕ) : LinearIndependent ℂ (fun k => jM Z j ((mjH Z j).b k)) ∧
    Submodule.span ℂ (Set.range fun k => jM Z j ((mjH Z j).b k)) = ⊤ :=
  mapSeq_ind_all _ _ D.what₂.Mj Z.jW
    (fun _ A g => LinearIndependent ℂ (fun k => g (A.b k)) ∧ Submodule.span ℂ (Set.range fun k => g (A.b k)) = ⊤)
    (fun i => by
      have h : (fun k => Z.jW i ((HLat.ofCoord ((s0Of R F).M i) ((s0Of R F).XW i)).b k)) = fun k => Z.jW i (Pi.single k 1) :=
        funext fun k => congrArg (Z.jW i) (Pi.basisFun_apply _ _ k)
      exact h ▸ jW_basis Z hH i)
    (fun _ => unitMap_basis _ _) j

theorem jM_lat (hP : Pins R F cG) (hH : Holds R F) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (mjH Z j).V) :
    x ∈ (mjH Z j).L ↔ ∃ c : D.what₂.Mj j → 𝓞 D.what₂.LL,
      jM Z j x = ∑ v ∈ (D.what₂.MjLat j).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v :=
  mapSeq_ind _ _ D.what₂.Mj Z.jW
    (fun j A g => ∀ x : A.V, x ∈ A.L ↔ ∃ c : D.what₂.Mj j → 𝓞 D.what₂.LL,
      g x = ∑ v ∈ (D.what₂.MjLat j).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v)
    (fun i => (jW_lat Z hP hH i).2) j h1 h2 x

theorem mjLat_sub (hP : Pins R F cG) (hH : Holds R F) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    ∀ x ∈ (D.what₂.MjLat j).gen, x ∈ Set.range (jM Z j) :=
  mapSeq_ind _ _ D.what₂.Mj Z.jW (fun j _ g => ∀ x ∈ (D.what₂.MjLat j).gen, x ∈ Set.range g)
    (fun i => (jW_lat Z hP hH i).1) j h1 h2

theorem jM_metric (hH : Holds R F) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (mjH Z j).V) :
    Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (mjH Z j).b (mjH Z j).X (InfinitePlace.mk D.what₂.embLL) x) = ‖jM Z j x‖ :=
  mapSeq_ind _ _ D.what₂.Mj Z.jW
    (fun _ A g => ∀ x : A.V, Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord A.b A.X (InfinitePlace.mk D.what₂.embLL) x) = ‖g x‖)
    (fun i => jW_norm Z hH i) j h1 h2 x

def mjIds (Xd : DivX D) (h : Xd.MjH = mjH Z) : MjHIds D A3.A Xd (A3.indefDown (s0Of R F)) where
  eW i := castV ((mjH_succ Z i).symm.trans (congrFun h _).symm)

theorem mjHTie_of_eq (Xd : DivX D) (h : Xd.MjH = mjH Z) (hj : HEq Xd.jM (jM Z)) :
    MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW (mjIds Z Xd h) := by
  constructor
  · intro i x
    exact map_castV _ _ D.what₂.Mj Z.jW h hj i _ x
  · intro i
    exact hLatTie_castV ((mjH_succ Z i).symm.trans (congrFun h _).symm)

theorem exists_mjHTie (Xd : DivX D) (h : Xd.MjH = mjH Z) (hj : HEq Xd.jM (jM Z)) :
    ∃ JM, MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW JM :=
  ⟨_, mjHTie_of_eq Z Xd h hj⟩

section Reface

variable {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)} {Sp : ∀ Zs, SPer (Dc Zs)}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} {kap : ℝ} {lam : type_of% R.lam3} {err : type_of% (R.updS kap lam).err0}
  {Y' : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0}
  (Z' : ReadL ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y')

end Reface

end GlobalTheory.Mem.R3

end
end

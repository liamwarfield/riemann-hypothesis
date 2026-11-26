module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsNoetherianRingOfIsAdicComplete

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomOfDerivation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.DerMorK

section Deform
variable {Z X : Scheme.{0}} (g : Z ⟶ X) (ψ : ∀ W : X.Opens, Γ(X, W) →+* Γ(Z, g ⁻¹ᵁ W))
  (hnat : ∀ (W W' : X.Opens) (h : W' ≤ W) (f : Γ(X, W)),
    ψ W' (resG X h f) = resG Z (g.preimage_mono h) (ψ W f))

def deformPsh : Z.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := g.base
  c :=
    { app := fun W => CommRingCat.ofHom (ψ W.unop)
      naturality := fun W W' i => by
        ext f
        exact hnat W.unop W'.unop i.unop.le f }

def deformHom (hnil : ∀ (W : X.Opens) (f : Γ(X, W)), IsNilpotent (ψ W f - (g.app W).hom f)) : Z ⟶ X :=
  ⟨⟨deformPsh g ψ hnat, fun x => ⟨fun a ha => by
    obtain ⟨W, hW, f, rfl⟩ := X.presheaf.germ_exist a
    have h1 := PresheafedSpace.stalkMap_germ_apply (deformPsh g ψ hnat) W x hW f
    have h2 := Scheme.Hom.germ_stalkMap_apply g W x hW f
    have h3 : IsNilpotent ((Z.presheaf.germ (g ⁻¹ᵁ W) x hW).hom (ψ W f - (g.app W).hom f)) :=
      (hnil W f).map _
    have h4 : IsUnit ((Z.presheaf.germ (g ⁻¹ᵁ W) x hW).hom (ψ W f)) := by
      erw [h1] at ha
      exact ha
    have h5 : IsUnit ((Z.presheaf.germ (g ⁻¹ᵁ W) x hW).hom ((g.app W).hom f)) := by
      have := h3.neg.isUnit_add_right_of_commute h4 (Commute.all _ _)
      rw [map_sub] at this
      convert this using 1
      ring
    rw [← h2] at h5
    exact isUnit_of_map_unit (g.stalkMap x).hom _ h5⟩⟩⟩

theorem deformHom_base (hnil) : (deformHom g ψ hnat hnil).base = g.base := rfl

end Deform

theorem hom_ext_appLE {Z X : Scheme.{0}} {f g : Z ⟶ X} (hb : f.base = g.base)
    (h : ∀ U e, f.appLE U (g ⁻¹ᵁ U) e = g.app U) : f = g := by
  refine Scheme.Hom.ext hb fun U => ?_
  rw [← h U (le_of_eq congr((TopologicalSpace.Opens.map $hb.symm).obj U))]
  rfl

theorem appLE_constFn {R : Type} [CommRing R] {Z X : Scheme.{0}} (f : Z ⟶ X) (p : X ⟶ Sp R)
    {U : X.Opens} {V : Z.Opens} (e : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V e).hom (constFn p U a) = constFn (f ≫ p) V a := by
  unfold constFn
  rw [← Scheme.Hom.appLE_comp_appLE f p ⊤ U V (fun _ _ => trivial) e]
  rfl

theorem app_constFn {R : Type} [CommRing R] {Z X : Scheme.{0}} (f : Z ⟶ X) (p : X ⟶ Sp R)
    (U : X.Opens) (a : R) :
    (f.app U).hom (constFn p U a) = constFn (f ≫ p) (f ⁻¹ᵁ U) a := by
  rw [Scheme.Hom.app_eq_appLE, appLE_constFn]

theorem constFn_spMap {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}} (p : X ⟶ Sp R')
    (φ : R →+* R') (U : X.Opens) (a : R) :
    constFn (p ≫ spMap φ) U a = constFn p U (φ a) := by
  unfold constFn
  rw [← Scheme.Hom.appLE_comp_appLE p (spMap φ) ⊤ ⊤ U (fun _ _ => trivial) (fun _ _ => trivial)]
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have h2 := congr(($h).hom a)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2 ⊢
  rw [h2]
  congr 1

def constHom {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem constFn_eq {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a : R) :
    constFn p U a = constHom p U a := rfl

theorem res_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U)
    (a : R) : resG X h (constFn p U a) = constFn p V a := by
  have := Scheme.Hom.appLE_map p (U := ⊤) (V := U) (V' := V) (fun _ _ => trivial) (homOfLE h).op
  exact congr(($this).hom _)

theorem res_app {Z X : Scheme.{0}} (f : Z ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    (f.app V).hom (resG X h a) = resG Z (f.preimage_mono h) ((f.app U).hom a) := by
  have := f.naturality (homOfLE h).op
  exact congr(($this).hom _)

theorem pbT_eq_app {Z X : Scheme.{0}} (f : Z ⟶ X) {U : X.Opens} (a : Γ(X, U)) :
    pbT f a (f ⁻¹ᵁ U) = (f.app U).hom a := by
  unfold pbT
  rw [dite_eq_left le_rfl, Scheme.Hom.appLE_eq_app]

section Main
variable {K : Type} [Field K] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp K} (π : Y' ⟶ Sp (DualNumber K)) (ρ : Y' ⟶ Y)
  {R : Type} [CommRing R] {D : R → K} {X : Scheme.{0}} {p : X ⟶ Sp R} {m : Y ⟶ X}
  {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}

theorem eps_sq (U : Y'.Opens) :
    constFn π U DualNumber.eps * constFn π U DualNumber.eps = 0 := by
  rw [constFn_eq, ← map_mul, DualNumber.eps_mul_eps, map_zero]

def psi (hd : LocDerK q p m D ⊤ d) (W : X.Opens) : Γ(X, W) →+* Γ(Y', (ρ ≫ m) ⁻¹ᵁ W) where
  toFun f := (ρ.app (m ⁻¹ᵁ W)).hom ((m.app W).hom f) +
    constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ W) DualNumber.eps * (ρ.app (m ⁻¹ᵁ W)).hom (d W f)
  map_one' := by
    have h := hd.mul W le_top 1 1
    simp only [_root_.mul_one, map_one, _root_.one_mul] at h
    have h0 : d W 1 = 0 := by linear_combination -h
    simp only [h0, map_one, map_zero, mul_zero, add_zero]
    rfl
  map_mul' f f' := by
    have h := eps_sq π (ρ ⁻¹ᵁ m ⁻¹ᵁ W)
    rw [hd.mul W le_top]
    simp only [map_mul, map_add (f := _)]
    change (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) = (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) * (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W))
    linear_combination -((ρ.app (m ⁻¹ᵁ W)).hom (d W f) * (ρ.app (m ⁻¹ᵁ W)).hom (d W f')) * h
  map_zero' := by
    have h := hd.add W le_top 0 0
    simp only [add_zero] at h
    have h0 : d W 0 = 0 := by linear_combination -h
    simp only [h0, map_zero, mul_zero, add_zero]
    rfl
  map_add' f f' := by
    rw [hd.add W le_top]
    simp only [map_add (f := _)]
    change (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) = (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) + (_ : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W))
    ring

theorem psi_apply (hd : LocDerK q p m D ⊤ d) (W : X.Opens) (f : Γ(X, W)) :
    (psi π ρ hd W f : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) = (ρ.app (m ⁻¹ᵁ W)).hom ((m.app W).hom f) +
    constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ W) DualNumber.eps * (ρ.app (m ⁻¹ᵁ W)).hom (d W f) := rfl

theorem psi_nat (hd : LocDerK q p m D ⊤ d) (W W' : X.Opens) (h : W' ≤ W) (f : Γ(X, W)) :
    psi π ρ hd W' (resG X h f) = resG Y' ((ρ ≫ m).preimage_mono h) (psi π ρ hd W f) := by
  have h1 : m ⁻¹ᵁ W' ≤ m ⁻¹ᵁ W := m.preimage_mono h
  have h2 : (ρ.app (m ⁻¹ᵁ W')).hom ((m.app W').hom (resG X h f)) +
      constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ W') DualNumber.eps * (ρ.app (m ⁻¹ᵁ W')).hom (d W' (resG X h f)) =
      resG Y' (ρ.preimage_mono h1) ((ρ.app (m ⁻¹ᵁ W)).hom ((m.app W).hom f) +
      constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ W) DualNumber.eps * (ρ.app (m ⁻¹ᵁ W)).hom (d W f)) := by
    rw [hd.res W W' h le_top, rsT, dite_eq_left h1, res_app, res_app, res_app, map_add (f := _), map_mul, res_constFn]
  exact h2

theorem psi_nil (hd : LocDerK q p m D ⊤ d) (W : X.Opens) (f : Γ(X, W)) :
    IsNilpotent (psi π ρ hd W f - ((ρ ≫ m).app W).hom f) := by
  have h : IsNilpotent ((ρ.app (m ⁻¹ᵁ W)).hom ((m.app W).hom f) +
      constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ W) DualNumber.eps * (ρ.app (m ⁻¹ᵁ W)).hom (d W f) -
      (ρ.app (m ⁻¹ᵁ W)).hom ((m.app W).hom f)) := by
    refine ⟨2, ?_⟩
    have h := eps_sq π (ρ ⁻¹ᵁ m ⁻¹ᵁ W)
    linear_combination ((ρ.app (m ⁻¹ᵁ W)).hom (d W f)) ^ 2 * h
  exact h

end Main

theorem exists_hom_of_derivation : ∀ (K : Type) [Field K] (Y Y' : Scheme.{0}) (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap K (DualNumber K))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y ⟶ X) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)), m ≫ p = q ≫ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ spMap xD → LocDerK q p m (fun r => (xD r).snd) ⊤ d → ∃ Φ : Y' ⟶ X, j ≫ Φ = m ∧ Φ ≫ p = π ≫ spMap xD ∧ ∀ (W : X.Opens) (f : Γ(X, W)), pbT Φ f (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) = pbT (ρ ≫ m) f _ + constFn π _ DualNumber.eps * pbT ρ (d W f) _ := by
  intro K _ Y Y' q π ρ j hpb hjρ hjπ R _ xD X p m d hm hd
  let Φ := deformHom (ρ ≫ m) (psi π ρ hd) (psi_nat π ρ hd) (psi_nil π ρ hd)
  have hjm : j ≫ ρ ≫ m = m := by rw [← Category.assoc, hjρ, Category.id_comp]
  refine ⟨Φ, ?_, ?_, ?_⟩
  · refine hom_ext_appLE (congr(($hjm).base)) fun U e => ?_
    ext f
    have e' : m ⁻¹ᵁ U ≤ j ⁻¹ᵁ (ρ ⁻¹ᵁ m ⁻¹ᵁ U) := e
    have h1 : ((j ≫ Φ).appLE U (m ⁻¹ᵁ U) e).hom f = (j.appLE (ρ ⁻¹ᵁ m ⁻¹ᵁ U) (m ⁻¹ᵁ U) e').hom
        ((ρ.app (m ⁻¹ᵁ U)).hom ((m.app U).hom f) +
          constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ U) DualNumber.eps * (ρ.app (m ⁻¹ᵁ U)).hom (d U f)) := rfl
    have h2 : (j.appLE (ρ ⁻¹ᵁ m ⁻¹ᵁ U) (m ⁻¹ᵁ U) e').hom ((ρ.app (m ⁻¹ᵁ U)).hom ((m.app U).hom f)) =
        ((j ≫ ρ ≫ m).appLE U (m ⁻¹ᵁ U) e').hom f := rfl
    have h3 : ∀ (k : Y ⟶ X) (_ : k = m) (e''), k.appLE U (m ⁻¹ᵁ U) e'' = m.app U := by
      rintro k rfl e''
      exact Scheme.Hom.appLE_eq_app _
    rw [h1, map_add (f := _), map_mul, h2, h3 (j ≫ ρ ≫ m) hjm e', appLE_constFn, hjπ, constFn_spMap, constFn_eq]
    simp
  · apply ext_of_isAffine
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv]
    ext r
    have h0 : ∀ {Z : Scheme.{0}} (k : Z ⟶ Sp R),
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ k.appTop).hom r = constFn k ⊤ r := by
      intro Z k
      have := Scheme.Hom.appLE_eq_app k (U := ⊤)
      exact congr(($this.symm).hom _)
    rw [h0, h0, constFn_spMap]
    have h1 : constFn (Φ ≫ p) ⊤ r = (ρ.app (m ⁻¹ᵁ ⊤)).hom ((m.app ⊤).hom (constFn p ⊤ r)) +
        constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ ⊤) DualNumber.eps * (ρ.app (m ⁻¹ᵁ ⊤)).hom (d ⊤ (constFn p ⊤ r)) :=
      (app_constFn Φ p ⊤ r).symm
    rw [h1, hd.base ⊤ le_rfl, app_constFn, hm, ← Category.assoc, constFn_spMap, constFn_spMap,
      app_constFn, app_constFn, hpb.w, constFn_spMap, constFn_spMap, constFn_eq, constFn_eq, constFn_eq,
      ← map_mul, ← map_add]
    change constHom π ⊤ _ = constHom π ⊤ _
    congr 1
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  · intro W f
    have h1 := pbT_eq_app Φ f
    have h2 := pbT_eq_app (ρ ≫ m) f
    have h3 := pbT_eq_app ρ (d W f)
    refine h1.trans ?_
    rw [h3]
    erw [h2]
    rfl

end GlobalTheory.KS.DerMorK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientIsFiniteLocallyOfFiniteTypeDescend
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientIsFiniteLocallyOfFiniteTypeDescend
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem quotient_isFinite_locallyOfFiniteType_descend :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s' : X' ⟶ S), LocallyOfFiniteType (π ≫ s') → IsFinite π ∧ LocallyOfFiniteType s' ∧ (QuasiCompact (π ≫ s') → QuasiCompact s') ∧ (IsSeparated (π ≫ s') → IsSeparated s') ∧ (IsProper (π ≫ s') → IsProper s') := by
  intro G _ _ X X' ρ π hπ S _ s' hft
  obtain ⟨hA, hc, hV⟩ := hπ
  have hq : IsAffineQuotient ρ π :=
    { comp_eq := hc
      isAffineHom := hA
      app_injective := fun W => (hV W).1
      mem_range_app := fun W s hs => (hV W).2 s (by
        intro g hg
        unfold IsInvariantSection at hs
        obtain ⟨_, e⟩ := hs g
        exact e) }
  exact ⟨hq.isFinite s', hq.locallyOfFiniteType s',
    fun _ => hq.quasiCompact s', fun _ => hq.isSeparated s', fun _ => hq.isProper s'⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientIsFiniteLocallyOfFiniteTypeDescendStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
theorem _root_.GlobalTheory.T.quotient_isFinite_and_descends_finiteness_properties : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s' : X' ⟶ S), LocallyOfFiniteType (π ≫ s') → IsFinite π ∧ LocallyOfFiniteType s' ∧ (QuasiCompact (π ≫ s') → QuasiCompact s') ∧ (IsSeparated (π ≫ s') → IsSeparated s') ∧ (IsProper (π ≫ s') → IsProper s') := by
  first | exact @GlobalTheory.quotient_isFinite_locallyOfFiniteType_descend | exact GlobalTheory.quotient_isFinite_locallyOfFiniteType_descend | (intros; apply GlobalTheory.quotient_isFinite_locallyOfFiniteType_descend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSumSmulSeparatingInertia
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem _root_.GlobalTheory.exists_sum_smul_separating_inertia :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (B : Type) [CommRing B] [MulSemiringAction Γ B]
      (q : Ideal B), q.IsPrime → ∃ (n : ℕ) (c d : Fin n → B) (s : B), s ∉ q ∧ ∀ g : Γ,
        (g ∈ q.inertia Γ → (∑ j, d j * g • c j) - s ∈ q) ∧
        (g ∉ q.inertia Γ → (∑ j, d j * g • c j) ∈ q) := by
  intro Γ _ _ B _ _ q hq
  classical
  haveI := Fintype.ofFinite Γ
  have hmem : ∀ g : Γ, g ∈ q.inertia Γ ↔ ∀ x, g • x - x ∈ q := fun g => Iff.rfl
  have factor : ∀ h : Γ, ∃ x y : B, x + y ∉ q ∧ (h ∉ q.inertia Γ → h • x + y ∈ q) := by
    intro h
    by_cases hh : h ∈ q.inertia Γ
    · exact ⟨1, 0, by simpa using hq.one_notMem, fun h' => (h' hh).elim⟩
    · obtain ⟨x, hx⟩ : ∃ x, h • x - x ∉ q := by simpa [hmem] using hh
      refine ⟨x, -(h • x), fun hm => hx ?_, fun _ => by simp⟩
      rw [← neg_sub]
      exact q.neg_mem (by rwa [sub_eq_add_neg])
  choose x y hxy hzero using factor
  let e := (Fintype.equivFin (Finset Γ)).symm
  have key : ∀ g : Γ, ∑ j, (∏ h ∈ Finset.univ \ e j, y h) * g • ∏ h ∈ e j, x h =
      ∏ h, (g • x h + y h) := by
    intro g
    rw [Finset.prod_add, Finset.powerset_univ,
      Equiv.sum_comp e (fun t => (∏ h ∈ Finset.univ \ t, y h) * g • ∏ h ∈ t, x h)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.smul_prod', mul_comm]
  refine ⟨Fintype.card (Finset Γ), fun j => ∏ h ∈ e j, x h, fun j => ∏ h ∈ Finset.univ \ e j, y h,
    ∏ h, (x h + y h), ?_, fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · intro hs
    obtain ⟨h, -, hh⟩ := Ideal.IsPrime.prod_mem_iff.mp hs
    exact hxy h hh
  · rw [key, ← Ideal.Quotient.eq, map_prod, map_prod]
    refine Finset.prod_congr rfl fun h _ => ?_
    rw [Ideal.Quotient.eq]
    simpa using (hmem g).mp hg (x h)
  · rw [key]
    exact Ideal.IsPrime.prod_mem_iff.mpr ⟨g, Finset.mem_univ g, hzero g hg⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EtSetOfLists
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem etSet_of_lists : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (N n : ℕ) (σ : Fin n → (𝟙_ (Over S') ⟶ G')) (K : Set G.left), IsAbelianScheme G → IsGrpPullback G' G f φ → IsUnit (N : Γ(S, ⊤)) → IsFinite f → Etale f → Surjective f → Lists N σ (φ ⁻¹' K) → EtSet G K := by
  intro S S' f G G' _ _ φ N n σ K hG h hN hfin het hsurj hL
  obtain ⟨hpow, hK, -⟩ := hL
  obtain ⟨-, hWf, hWe⟩ := GrpTangent.finiteEtale_mulN_torsion G hN
  have := hG.proper
  let T : Over S := Over.mk ((𝟙_ (Over S')).hom ≫ f)
  have hTf : IsFinite T.hom := by
    change IsFinite (𝟙 S' ≫ f); infer_instance
  have hTe : Etale T.hom := by
    change Etale (𝟙 S' ≫ f); infer_instance
  let ρ : (𝟙_ (Over S') ⟶ G') →* (T ⟶ G) :=
    MonoidHom.mk' (fun x => Over.homMk (x.left ≫ φ) (by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x]; rfl))
      fun x y => Over.OverMorphism.ext (h.2 _ x y _ _ rfl rfl).symm
  have hρ : ∀ j, ρ (σ j) ^ N = 1 := fun j => by rw [← map_pow, hpow, map_one]
  choose τ hτ using fun j => (LatticeTorsion.existsUnique_torsion G N (ρ (σ j)) (hρ j)).exists
  have hτl : ∀ j, (τ j).left ≫ (torsion.ι G N).left = (σ j).left ≫ φ := fun j =>
    congrArg (fun z => z.left) (hτ j)
  have hτf : ∀ j, IsFinite (τ j).left := fun j => by
    have : IsFinite ((τ j).left ≫ (torsion G N).hom) := by rw [Over.w]; exact hTf
    exact IsFinite.of_comp _ (torsion G N).hom
  have hτe : ∀ j, Etale (τ j).left := fun j => by
    have : Etale ((τ j).left ≫ (torsion G N).hom) := by rw [Over.w]; exact hTe
    exact Etale.of_comp _ (torsion G N).hom
  have hop : IsOpen (⋃ j, Set.range (τ j).left) :=
    isOpen_iUnion fun j => (τ j).left.isOpenMap.isOpen_range
  have hcl : IsClosed (⋃ j, Set.range (τ j).left) :=
    isClosed_iUnion_of_finite fun j => (τ j).left.isClosedMap.isClosed_range
  let U : (torsion G N).left.Opens := ⟨_, hop⟩
  have hU : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hcl)
  have hη : IsClosedImmersion η[G].left := by
    have : IsClosedImmersion (η[G].left ≫ G.hom) := by
      rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 S))
    exact IsClosedImmersion.of_comp _ G.hom
  have hι : IsClosedImmersion (torsion.ι G N).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (GrpTangent.isPullback_torsion G N).flip hη
  have hφ : Surjective φ := MorphismProperty.of_isPullback (P := @Surjective) h.1.flip hsurj
  refine ⟨Over.mk (U.ι ≫ (torsion G N).hom), Over.homMk (U.ι ≫ (torsion.ι G N).left) (by simp), ?_, ?_, ?_, ?_⟩
  · change IsFinite (U.ι ≫ _); infer_instance
  · change Etale (U.ι ≫ _); infer_instance
  · change IsClosedImmersion (U.ι ≫ _); infer_instance
  · change Set.range (U.ι ≫ (torsion.ι G N).left) = K
    rw [← Set.image_preimage_eq K φ.surjective, hK, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    change _ '' (⋃ j, Set.range (τ j).left) = _
    rw [Set.image_iUnion, Set.image_iUnion]
    refine Set.iUnion_congr fun j => ?_
    rw [← Set.range_comp, ← Set.range_comp, ← TopCat.coe_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      ← Scheme.Hom.comp_base, hτl]

end GlobalTheory.HkFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGoodUniformisationKodairaSpencer
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGoodUniformisationKodairaSpencer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KSInh

variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g)

theorem dom_id (W : A₀.left.Opens) : dom u (𝟙 _) W = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ W} := by
  ext z
  unfold dom
  simp only [Category.comp_id]

theorem fn_id (W : A₀.left.Opens) (f : Γ(A₀.left, W)) :
    fn u (𝟙 _) W f = fun z => valAt' (u.ex z).left W f := by
  funext z
  unfold fn
  rw [Category.comp_id]

theorem isOpen_dom (W : A₀.left.Opens) : IsOpen (dom u (𝟙 _) W) := by
  rw [dom_id]
  exact (u.hol W 0).1

theorem differentiableOn_fn (W : A₀.left.Opens) (f : Γ(A₀.left, W)) :
    DifferentiableOn ℂ (fn u (𝟙 _) W f) (dom u (𝟙 _) W) := by
  rw [dom_id, fn_id]
  exact (u.hol W f).2

theorem differentiableAt_fn (W : A₀.left.Opens) (f : Γ(A₀.left, W)) {z : Fin g → ℂ} (hz : z ∈ dom u (𝟙 _) W) :
    DifferentiableAt ℂ (fn u (𝟙 _) W f) z :=
  (differentiableOn_fn u W f).differentiableAt ((isOpen_dom u W).mem_nhds hz)

theorem ex_add_period (l : u.Λ) (z : Fin g → ℂ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]

theorem ksRel_const (w : Fin g → ℂ) :
    KSRel u A₀.hom (𝟙 _) (fun _ => 0) 0 (fun z W f => fderiv ℂ (fn u (𝟙 _) W f) z w) := by
  refine { der := ?der, base := ?base, hol := ?hol, per := ?per }
  case der =>
    intro z
    have hd : ∀ (W : A₀.left.Opens) (k : Γ(A₀.left, W)), ⊤ ≤ ((u.ex z).left ≫ 𝟙 _) ⁻¹ᵁ W →
        DifferentiableAt ℂ (fn u (𝟙 _) W k) z :=
      fun W k hW => differentiableAt_fn u W k hW
    refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW' f => ?_⟩
    · have e : fn u (𝟙 _) W (f + f') = fn u (𝟙 _) W f + fn u (𝟙 _) W f' := by
        funext y
        simp only [fn, valAt', Pi.add_apply]
        split_ifs with hy
        · simp only [valAt, map_add (f := _)]
        · exact (add_zero 0).symm
      show fderiv ℂ (fn u (𝟙 _) W (f + f')) z w =
        fderiv ℂ (fn u (𝟙 _) W f) z w + fderiv ℂ (fn u (𝟙 _) W f') z w
      rw [e, fderiv_add (hd W f hW) (hd W f' hW)]
      rfl
    · have e : fn u (𝟙 _) W (f * f') = fn u (𝟙 _) W f * fn u (𝟙 _) W f' := by
        funext y
        simp only [fn, valAt', Pi.mul_apply]
        split_ifs with hy
        · simp only [valAt, map_mul]
        · exact (mul_zero 0).symm
      show fderiv ℂ (fn u (𝟙 _) W (f * f')) z w =
        fn u (𝟙 _) W f z * fderiv ℂ (fn u (𝟙 _) W f') z w + fn u (𝟙 _) W f' z * fderiv ℂ (fn u (𝟙 _) W f) z w
      rw [e, fderiv_mul (hd W f hW) (hd W f' hW)]
      rfl
    · show fderiv ℂ (fn u (𝟙 _) W' (resG A₀.left h f)) z w = fderiv ℂ (fn u (𝟙 _) W f) z w
      have hev : fn u (𝟙 _) W' (resG A₀.left h f) =ᶠ[nhds z] fn u (𝟙 _) W f := by
        filter_upwards [(isOpen_dom u W').mem_nhds hW'] with y hy
        have hyW' : ⊤ ≤ ((u.ex y).left ≫ 𝟙 _) ⁻¹ᵁ W' := hy
        have hy' : ⊤ ≤ ((u.ex y).left ≫ 𝟙 _) ⁻¹ᵁ W := hyW'.trans (Scheme.Hom.preimage_mono _ h)
        simp only [fn, valAt', dite_eq_left hyW', dite_eq_left hy']
        unfold valAt resG
        have key : A₀.left.presheaf.map (homOfLE h).op ≫ Scheme.Hom.appLE ((u.ex y).left ≫ 𝟙 _) W' ⊤ hyW' =
            Scheme.Hom.appLE ((u.ex y).left ≫ 𝟙 _) W ⊤ hy' :=
          Scheme.Hom.map_appLE _ _ _
        rw [← key]
        rfl
      rw [hev.fderiv_eq]
  case base =>
    intro z r
    show fderiv ℂ (fn u (𝟙 _) ⊤ (constFn A₀.hom ⊤ r)) z w = 0
    obtain ⟨K, hK⟩ : ∃ K : ℂ, ∀ y, fn u (𝟙 _) ⊤ (constFn A₀.hom ⊤ r) y = K := by
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
        ((Scheme.Hom.appLE (𝟙_ (Over (Sp ℂ))).hom ⊤ ⊤ (Scheme.Hom.preimage_top _).ge).hom
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)), fun y => ?_⟩
      have ht : ⊤ ≤ ((u.ex y).left ≫ 𝟙 _) ⁻¹ᵁ (⊤ : A₀.left.Opens) := (Scheme.Hom.preimage_top _).ge
      have key : Scheme.Hom.appLE A₀.hom ⊤ ⊤ (Scheme.Hom.preimage_top _).ge ≫ Scheme.Hom.appLE ((u.ex y).left ≫ 𝟙 _) ⊤ ⊤ ht =
          Scheme.Hom.appLE (𝟙_ (Over (Sp ℂ))).hom ⊤ ⊤ (Scheme.Hom.preimage_top _).ge := by
        rw [Scheme.Hom.appLE_comp_appLE]
        congr 1
        simp
      simp only [fn, valAt', dite_eq_left ht]
      unfold valAt constFn
      rw [← key]
      rfl
    have e : fn u (𝟙 _) ⊤ (constFn A₀.hom ⊤ r) = fun _ => K := funext hK
    rw [e]
    simp
  case hol =>
    intro W f
    exact ((cauchyRiemann_iff_differentiableOn_complex g _ _ (isOpen_dom u W)).2 (differentiableOn_fn u W f)).2 w
  case per =>
    intro l W f z _
    show fderiv ℂ (fn u (𝟙 _) W f) (z + l) w =
      fderiv ℂ (fn u (𝟙 _) W f) z w + fderiv ℂ (fn u (𝟙 _) W f) z ((0 : Matrix (Fin g) (Fin g) ℂ).mulVec (star (l : Fin g → ℂ)))
    have hp : (fun y => fn u (𝟙 _) W f (y + l)) = fn u (𝟙 _) W f := by
      funext y
      unfold fn
      rw [ex_add_period]
    rw [Matrix.zero_mulVec, map_zero, add_zero, ← fderiv_comp_add_right, hp]

theorem exists_goodU_ksRel : ThetaUnifAV → ∀ P₀ : Out.PolAV (Sp ℂ), ∃ (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ ∧ ∀ w : Fin P₀.g → ℂ, KSRel u P₀.A.hom (𝟙 _) (fun _ => 0) 0 (fun z W f => fderiv ℂ (fn u (𝟙 _) W f) z w) := by
  intro hT P₀
  obtain ⟨rig, hrig⟩ : ∃ rig : LB.Gen (P₀.L.pull (eSec P₀.A)), rig.IsGen := P₀.rigid
  obtain ⟨u, Hm, χ, _, hAH, -, ht₁, ht₂, hend, hth, -⟩ := hT P₀ rig hrig
  exact ⟨u, Hm, χ, ⟨hAH, ht₁, ht₂, hend, fun n θ hθ => ((hth n).2 θ hθ).exists⟩, fun w => ksRel_const u w⟩

end GlobalTheory.KSInh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGoodUniformisationKodairaSpencerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.exists_goodUniformisation_kodairaSpencer : ThetaUnifAV → ∀ P₀ : Out.PolAV (Sp ℂ), ∃ (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ ∧ ∀ w : Fin P₀.g → ℂ, KSRel u P₀.A.hom (𝟙 _) (fun _ => 0) 0 (fun z W f => fderiv ℂ (fn u (𝟙 _) W f) z w) := by
  first | exact @GlobalTheory.KSInh.exists_goodU_ksRel | exact GlobalTheory.KSInh.exists_goodU_ksRel | (intros; apply GlobalTheory.KSInh.exists_goodU_ksRel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GermDerivationIffDualNumberPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GermDerivationIffDualNumberPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KS.PtDual

variable {X : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S]

def ev (v : Sp R ⟶ X) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) : Γ(X, W) →+* R :=
  (v.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom

theorem ev_fromSpec (v : Sp R ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ v ⁻¹ᵁ U) :
    Spec.map (CommRingCat.ofHom (ev v U h)) ≫ hU.fromSpec = v := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec v hU (isAffineOpen_top _) h
  rw [ev, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, this, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem ev_ext {v v' : Sp R ⟶ X} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U)
    (e : ev v U h = ev v' U h') : v = v' := by
  rw [← ev_fromSpec v hU h, ← ev_fromSpec v' hU h', e]

theorem exists_ev {U : X.Opens} (hU : IsAffineOpen U) (φ : Γ(X, U) →+* R) :
    ∃ (v : Sp R ⟶ X) (h : ⊤ ≤ v ⁻¹ᵁ U), ev v U h = φ := by
  have h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
    exact le_top
  refine ⟨_, h, ?_⟩
  have := ev_fromSpec _ hU h
  rw [cancel_mono] at this
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)

theorem ev_res (v : Sp R ⟶ X) {W W' : X.Opens} (e : W' ≤ W) (h : ⊤ ≤ v ⁻¹ᵁ W) (h' : ⊤ ≤ v ⁻¹ᵁ W') (f : Γ(X, W)) :
    ev v W' h' (resG X e f) = ev v W h f := by
  have : X.presheaf.map (homOfLE e).op ≫ v.appLE W' ⊤ h' = v.appLE W ⊤ h := Scheme.Hom.map_appLE ..
  unfold ev
  rw [← this]
  rfl

theorem ev_comp (φ : R →+* S) (v : Sp R ⟶ X) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (h' : ⊤ ≤ (spMap φ ≫ v) ⁻¹ᵁ W)
    (f : Γ(X, W)) : ev (spMap φ ≫ v) W h' f = φ (ev v W h f) := by
  have h1 : v.appLE W ⊤ h ≫ (spMap φ).appLE ⊤ ⊤ le_top = (spMap φ ≫ v).appLE W ⊤ h' :=
    Scheme.Hom.appLE_comp_appLE ..
  have h2 : (spMap φ).appLE ⊤ ⊤ le_top = (spMap φ).appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact (congrArg _ ((Sp S).presheaf.map_id _)).trans (Category.comp_id _)
  have h3 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  unfold ev
  rw [← h1, h2, Category.assoc]
  erw [h3]
  rfl

abbrev pt0 : Sp ℂ ⟶ Sp (DualNumber ℂ) := spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom

theorem le_preimage_iff (v : Sp (DualNumber ℂ) ⟶ X) (W : X.Opens) :
    ⊤ ≤ v ⁻¹ᵁ W ↔ ⊤ ≤ (pt0 ≫ v) ⁻¹ᵁ W := by
  rw [Scheme.Hom.comp_preimage]
  refine ⟨fun h p _ => h (Set.mem_univ _), fun h p _ => ?_⟩
  have hs : Function.Surjective (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hp : (p : PrimeSpectrum (DualNumber ℂ)) ∈
      Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    rw [range_comap_of_surjective _ _ hs]
    intro x hx
    have hx' : x.fst = 0 := hx
    refine (p : PrimeSpectrum (DualNumber ℂ)).isPrime.mem_of_pow_mem 2 ?_
    have : x ^ 2 = 0 := by
      ext <;> simp [pow_two, hx']
    rw [this]
    exact zero_mem _
  obtain ⟨q, rfl⟩ := hp
  exact h (Set.mem_univ q)

theorem fst_ev {y : Sp ℂ ⟶ X} {v : Sp (DualNumber ℂ) ⟶ X} (hv : pt0 ≫ v = y) (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W)
    (f : Γ(X, W)) : (ev v W h f).fst = valAt' y W f := by
  subst hv
  have h' := (le_preimage_iff v W).1 h
  rw [valAt'_eq_valAtHom _ h']
  exact (ev_comp _ v W h h' f).symm

def derHom {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) (W : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ W) :
    Γ(X, W) →+* DualNumber ℂ where
  toFun f := TrivSqZeroExt.inl (valAt' y W f) + TrivSqZeroExt.inr (δ W f)
  map_one' := by
    have := hδ.mul W h 1 1
    rw [_root_.mul_one, valAt'_one y h, _root_.one_mul, left_eq_add] at this
    ext <;> simp [valAt'_one y h, this]
  map_mul' a b := by
    ext
    · simp [valAt'_mul]
    · simp [hδ.mul W h, mul_comm]
  map_zero' := by
    have := hδ.add W h 0 0
    rw [add_zero, left_eq_add] at this
    ext <;> simp [valAt'_zero, this]
  map_add' a b := by
    ext
    · simp [valAt'_add]
    · simp [hδ.add W h]

theorem fst_derHom {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) (W : X.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (f : Γ(X, W)) : (derHom hδ W h f).fst = valAt' y W f := by
  simp [derHom]

theorem snd_derHom {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) (W : X.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (f : Γ(X, W)) : (derHom hδ W h f).snd = δ W f := by
  simp [derHom]

theorem derHom_res {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) {W W' : X.Opens} (e : W' ≤ W)
    (h : ⊤ ≤ y ⁻¹ᵁ W) (h' : ⊤ ≤ y ⁻¹ᵁ W') (f : Γ(X, W)) : derHom hδ W' h' (resG X e f) = derHom hδ W h f := by
  ext
  · rw [fst_derHom, fst_derHom, valAt'_res y e f h']
  · rw [snd_derHom, snd_derHom, hδ.res W W' e h']

theorem exists_affine (y : Sp ℂ ⟶ X) : ∃ U : X.Opens, IsAffineOpen U ∧ ⊤ ≤ y ⁻¹ᵁ U := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (x := y (default : PrimeSpectrum ℂ)) (U := ⊤) trivial
  exact ⟨U, hU, (top_le_preimage_iff_mem y U).2 hy⟩

theorem ev_eq_derHom {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) {v : Sp (DualNumber ℂ) ⟶ X}
    (hv : pt0 ≫ v = y) {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U)
    (e : ev v U h = derHom hδ U h') (W : X.Opens) (k : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)) : (ev v W k f).snd = δ W f := by
  have k' : ⊤ ≤ y ⁻¹ᵁ W := hv ▸ (le_preimage_iff v W).1 k
  obtain ⟨g, hg, hy⟩ := hU.exists_basicOpen_le (V := W) ⟨_, (top_le_preimage_iff_mem y W).1 k'⟩
    ((top_le_preimage_iff_mem y U).1 h')
  have l' : ⊤ ≤ y ⁻¹ᵁ X.basicOpen g := (top_le_preimage_iff_mem y _).2 hy
  have l : ⊤ ≤ v ⁻¹ᵁ X.basicOpen g := (le_preimage_iff v _).2 (hv ▸ l')
  have := hU.isLocalization_basicOpen g
  have e' : ev v _ l = derHom hδ _ l' := by
    refine IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun a => ?_)
    refine (ev_res v (X.basicOpen_le g) h l a).trans ?_
    rw [e]
    exact (derHom_res hδ (X.basicOpen_le g) h' l' a).symm
  rw [← ev_res v hg k l, e', derHom_res hδ hg k' l', snd_derHom]

open Classical in
theorem exists_ptDer {y : Sp ℂ ⟶ X} {v : Sp (DualNumber ℂ) ⟶ X} (hv : pt0 ≫ v = y) :
    ∃ δ, PtDer y δ ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), (ev v W h f).snd = δ W f := by
  have H : ∀ W, ⊤ ≤ y ⁻¹ᵁ W → ⊤ ≤ v ⁻¹ᵁ W := fun W h => (le_preimage_iff v _).2 (hv ▸ h)
  refine ⟨fun W f => if h : ⊤ ≤ v ⁻¹ᵁ W then (ev v W h f).snd else 0, ⟨?_, ?_, ?_⟩, fun W h f => ?_⟩
  · intro W h f f'
    simp only [dif_pos (H W h), map_add (f := _), TrivSqZeroExt.snd_add]
  · intro W h f f'
    simp only [dif_pos (H W h), map_mul, DualNumber.snd_mul, fst_ev hv]
    ring
  · intro W W' e h f
    have k := H W (top_le_preimage_mono y e h)
    simp only [dif_pos (H W' h), dif_pos k, ev_res v e k]
  · simp only [dif_pos h]

theorem existsUnique_point {y : Sp ℂ ⟶ X} {δ : ∀ W : X.Opens, Γ(X, W) → ℂ} (hδ : PtDer y δ) :
    ∃! v : Sp (DualNumber ℂ) ⟶ X, pt0 ≫ v = y ∧
      ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), (ev v W h f).snd = δ W f := by
  obtain ⟨U, hU, h'⟩ := exists_affine y
  obtain ⟨v, h, e⟩ := exists_ev hU (derHom hδ U h')
  have hv : pt0 ≫ v = y := by
    refine ev_ext hU ((le_preimage_iff v U).1 h) h' (RingHom.ext fun f => ?_)
    rw [ev_comp _ v U h, e]
    exact (fst_derHom hδ U h' f).trans (valAt'_eq_valAtHom y h' f)
  refine ⟨v, ⟨hv, ev_eq_derHom hδ hv hU h h' e⟩, ?_⟩
  rintro w ⟨hw, hw'⟩
  have k : ⊤ ≤ w ⁻¹ᵁ U := (le_preimage_iff w _).2 (hw ▸ h')
  refine ev_ext hU k h (RingHom.ext fun f => ?_)
  rw [e]
  ext
  · rw [fst_ev hw, fst_derHom]
  · rw [hw', snd_derHom]

end GlobalTheory.KS.PtDual

namespace GlobalTheory.KS

theorem ptDer_iff_dualPoint : ∀ (X : Scheme.{0}) (y : Sp ℂ ⟶ X), (∀ δ, PtDer y δ → ∃! v : Sp (DualNumber ℂ) ⟶ X, (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v = y ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE W ⊤ h).hom f)) = δ W f) ∧ ∀ v : Sp (DualNumber ℂ) ⟶ X, (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v = y → ∃ δ, PtDer y δ ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE W ⊤ h).hom f)) = δ W f :=
  fun _ _ => ⟨fun _ hδ => PtDual.existsUnique_point hδ, fun _ hv => PtDual.exists_ptDer hv⟩

end GlobalTheory.KS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GermDerivationIffDualNumberPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.germDerivation_iff_dualNumberPoint : ∀ (X : Scheme.{0}) (y : Sp ℂ ⟶ X), (∀ δ, PtDer y δ → ∃! v : Sp (DualNumber ℂ) ⟶ X, (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v = y ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE W ⊤ h).hom f)) = δ W f) ∧ ∀ v : Sp (DualNumber ℂ) ⟶ X, (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v = y → ∃ δ, PtDer y δ ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE W ⊤ h).hom f)) = δ W f := by
  first | exact @GlobalTheory.KS.ptDer_iff_dualPoint | exact GlobalTheory.KS.ptDer_iff_dualPoint | (intros; apply GlobalTheory.KS.ptDer_iff_dualPoint <;> assumption)
end
end

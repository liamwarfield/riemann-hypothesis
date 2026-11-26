module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreChartBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeConstantRank
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TopLeAlgOverHom

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelActionBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelActionBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ggeo.LieCoord

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x : Sp R ⟶ S}

def transport {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E'] (M : LieModel G x E)
    (e : E ≃ₗ[R] E') : LieModel G x E' where
  pt v := M.pt (e.symm v)
  tan v := M.tan _
  inj a b h := e.symm.injective (M.inj h)
  onto v hv := by
    obtain ⟨w, hw⟩ := M.onto v hv
    exact ⟨e w, by simpa using hw⟩
  add a b := by rw [map_add (f := _), M.add]
  smul c a := by rw [map_smul]; exact M.smul c _

theorem transport_pt {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E'] (M : LieModel G x E)
    (e : E ≃ₗ[R] E') (v : E') : (transport M e).pt v = M.pt (e.symm v) := rfl

theorem isTanAt_comp {v : epsAt x ⟶ G} (hv : IsTanAt G x v) (f : G ⟶ G) [IsMonHom f] : IsTanAt G x (v ≫ f) := by
  unfold IsTanAt at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, MonObj.one_comp]

theorem mul_comp' {T : Over S} (u v : T ⟶ G) (f : G ⟶ G) [IsMonHom f] : (u * v) ≫ f = (u ≫ f) * (v ≫ f) := by
  simp [MonObj.mul_comp]

variable {E : Type} [AddCommGroup E] [Module R E]

def endo (M : LieModel G x E) (f : G ⟶ G) [IsMonHom f] (e : E) : E :=
  Classical.choose (M.onto (M.pt e ≫ f) (isTanAt_comp (M.tan e) f))

theorem endo_spec (M : LieModel G x E) (f : G ⟶ G) [IsMonHom f] (e : E) : M.pt (endo M f e) = M.pt e ≫ f :=
  Classical.choose_spec (M.onto (M.pt e ≫ f) (isTanAt_comp (M.tan e) f))

def diff (M : LieModel G x E) (f : G ⟶ G) [IsMonHom f] : E →ₗ[R] E where
  toFun := endo M f
  map_add' a b := M.inj (by rw [endo_spec, M.add, M.add, endo_spec, endo_spec, mul_comp'])
  map_smul' c a := M.inj (by
    rw [endo_spec, RingHom.id_apply, LieModel.pt_smul, LieModel.pt_smul, endo_spec, Category.assoc])

theorem diff_spec (M : LieModel G x E) (f : G ⟶ G) [IsMonHom f] (e : E) : M.pt (diff M f e) = M.pt e ≫ f :=
  endo_spec M f e

def rho {O : Type} [CommRing O] (act : OAct O G) (M : LieModel G x E) : O →+* Module.End R E where
  toFun a := letI := act.hom a; diff M (act.act a)
  map_one' := by
    ext e
    apply M.inj
    letI := act.hom 1
    show M.pt (diff M (act.act 1) e) = M.pt e
    rw [diff_spec, act.one, Category.comp_id]
  map_mul' a b := by
    ext e
    apply M.inj
    letI := act.hom a; letI := act.hom b; letI := act.hom (a * b)
    show M.pt (diff M (act.act (a * b)) e) = M.pt (diff M (act.act a) (diff M (act.act b) e))
    rw [diff_spec, diff_spec, diff_spec, mul_comm, act.mul, Category.assoc]
  map_zero' := by
    ext e
    apply M.inj
    letI := act.hom 0
    show M.pt (diff M (act.act 0) e) = M.pt 0
    have h0 : act.act 0 = 1 := by
      have := act.add 0 0
      rw [add_zero] at this
      exact mul_eq_left.1 this.symm
    rw [diff_spec, LieModel.pt_zero, h0, Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (M.pt e ≫ toUnit G)]
  map_add' a b := by
    ext e
    apply M.inj
    letI := act.hom a; letI := act.hom b; letI := act.hom (a + b)
    show M.pt (diff M (act.act (a + b)) e) = M.pt (diff M (act.act a) e + diff M (act.act b) e)
    rw [diff_spec, M.add, diff_spec, diff_spec, act.add, comp_mul]

theorem rho_isActOf {O : Type} [CommRing O] (act : OAct O G) (M : LieModel G x E) : M.IsActOf act.act (rho act M) :=
  fun a e => by letI := act.hom a; exact diff_spec M (act.act a) e

end GlobalTheory.CompanionTheory.Ar.Ggeo.LieCoord

namespace GlobalTheory.CompanionTheory.Ar.Ggeo


open LieCoord in
theorem lieModel_coordinates_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ S), ∃ (n : ℕ) (M : LieModel t.G x (Fin n → R)) (ρ : 𝓞 E →+* Module.End R (Fin n → R)), M.IsActOf t.act.act ρ ∧ ∀ (R' : Type) [CommRing R'] (f : R →+* R') (x' : Sp R' ⟶ S), x' = spMap f ≫ x → ∃ (M' : LieModel t.G x' (Fin n → R')) (ρ' : 𝓞 E →+* Module.End R' (Fin n → R')), M'.IsActOf t.act.act ρ' ∧ (∀ u, (M'.pt (f ∘ u)).left = spMap (dualMap f) ≫ (M.pt u).left) ∧ ∀ a u, ρ' a (f ∘ u) = f ∘ ρ a u := by
  intro E _ _ _ H S t R _ _ x
  haveI := t.semi
  haveI : Smooth t.G.hom := ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian.smooth
  obtain ⟨V, _, _, ⟨M0⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists S t.G R x
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.lie_model_finite_projective S t.G R x V M0
  haveI : Module.Flat R V := inferInstance
  haveI : Module.Free R V := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis R V
  let eV : V ≃ₗ[R] (Fin (Module.finrank R V) → R) := b.equivFun
  refine ⟨Module.finrank R V, transport M0 eV, rho t.act (transport M0 eV), rho_isActOf t.act _, ?_⟩
  intro R' _ f x' hx'
  subst hx'
  letI : Algebra R R' := f.toAlgebra
  obtain ⟨T, _, _, _, _, M', j, hlift, hbc⟩ :=
    GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_liftBaseChange S t.G R R' x V M0
  let eT : T ≃ₗ[R'] (Fin (Module.finrank R V) → R') := (hbc.basis b).equivFun
  have key : ∀ u : Fin (Module.finrank R V) → R, eT.symm (f ∘ u) = j (eV.symm u) := by
    intro u
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [eT, eV, Module.Basis.equivFun_symm_apply, map_sum, map_smul, IsBaseChange.basis_apply,
      Function.comp_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact algebraMap_smul R' (u i) (j (b i))
  have hpt : ∀ u : Fin (Module.finrank R V) → R, ((transport M' eT).pt (f ∘ u)).left =
      spMap (dualMap f) ≫ ((transport M0 eV).pt u).left := by
    intro u
    rw [transport_pt, transport_pt, key]
    have h := hlift (eV.symm u)
    unfold LieModel.Lifts at h
    rw [Category.comp_id] at h
    exact h
  refine ⟨transport M' eT, rho t.act (transport M' eT), rho_isActOf t.act _, hpt, ?_⟩
  intro a u
  apply (transport M' eT).inj
  apply Over.OverMorphism.ext
  letI := t.act.hom a
  have h1 := rho_isActOf t.act (transport M' eT) a (f ∘ u)
  have h2 := rho_isActOf t.act (transport M0 eV) a u
  rw [h1, Over.comp_left, hpt, hpt, h2, Over.comp_left, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.Ggeo
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelActionBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_action_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ S), ∃ (n : ℕ) (M : LieModel t.G x (Fin n → R)) (ρ : 𝓞 E →+* Module.End R (Fin n → R)), M.IsActOf t.act.act ρ ∧ ∀ (R' : Type) [CommRing R'] (f : R →+* R') (x' : Sp R' ⟶ S), x' = spMap f ≫ x → ∃ (M' : LieModel t.G x' (Fin n → R')) (ρ' : 𝓞 E →+* Module.End R' (Fin n → R')), M'.IsActOf t.act.act ρ' ∧ (∀ u, (M'.pt (f ∘ u)).left = spMap (dualMap f) ≫ (M.pt u).left) ∧ ∀ a u, ρ' a (f ∘ u) = f ∘ ρ a u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ggeo.lieModel_coordinates_baseChange | exact GlobalTheory.CompanionTheory.Ar.Ggeo.lieModel_coordinates_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Ggeo.lieModel_coordinates_baseChange <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSegreChartFrames
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSegreChartFrames
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartFrames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem genMap_germ_eq {U : X.Opens} (g : Γ(X, U)) (p q : Cpt ξ) (hp : p.1 ∈ U) (hq : q.1 ∈ U) :
    genMap ξ p (X.presheaf.germ U p.1 hp g) = genMap ξ q (X.presheaf.germ U q.1 hq g) := by
  have key : ∀ (r : Cpt ξ) (hr : r.1 ∈ U), genMap ξ r (X.presheaf.germ U r.1 hr g) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) (r.2.mem_open U.2 hr) g) := by
    intro r hr
    show (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.stalkSpecializes r.2 (X.presheaf.germ U r.1 hr g)) = _
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_stalkSpecializes_apply hr r.2 g)
  rw [key p hp, key q hq]

theorem unitAt_of_isUnit {p : Cpt ξ} {s : X.presheaf.stalk p.1} (hs : IsUnit s) :
    unitAt ξ p (genMap ξ p s) := by
  have hu : IsUnit (genMap ξ p s) := hs.map (genMap ξ p)
  obtain ⟨u, rfl⟩ := hs
  refine ⟨hu.ne_zero, ⟨_, rfl⟩, ⟨((u⁻¹ : (X.presheaf.stalk p.1)ˣ) : X.presheaf.stalk p.1), ?_⟩⟩
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← map_mul, Units.inv_mul, map_one]

theorem isUnit_of_unitAt (hξ : IsCptGen ξ) {p : Cpt ξ} {s : X.presheaf.stalk p.1}
    (h : unitAt ξ p (genMap ξ p s)) : IsUnit s := by
  obtain ⟨h0, _, t, ht⟩ := h
  refine IsUnit.of_mul_eq_one t (hξ.inj p ?_)
  rw [map_mul, ht, map_one, mul_inv_cancel₀ h0]

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem inFrameDomain_of_unitAt (hT : CoordTie ℤ ξ (segreCoord y)) {z : Spec (CommRingCat.of ℂ) ⟶ X}
    {w : (Σ k, J k) → ℂ} (hz : CoordsAt ξ y z w) (h : genPt ξ ⤳ centre z) {c : (k : K) → J k} {f : Ω}
    (hc : InChart ξ (segreCoord y) c ⟨centre z, h⟩) (hf : unitAt ξ ⟨centre z, h⟩ f) :
    InFrameDomain y c f w := by
  let gv : X.presheaf.stalk (centre z) →+* Ω := genMap ξ ⟨centre z, h⟩
  let ev : X.presheaf.stalk (centre z) →+* ℂ := (Scheme.stalkClosedPointTo z).hom
  have hinj : Function.Injective gv := hT.gen.inj ⟨centre z, h⟩
  constructor
  · choose d hd using hz.1
    have key : ∀ k, ∃ (r : ℂ) (s : X.presheaf.stalk (centre z)),
        gv s = y ⟨k, c k⟩ / y ⟨k, d k⟩ ∧ ev s = r ∧ w ⟨k, c k⟩ = r * w ⟨k, d k⟩ := by
      intro k
      obtain ⟨r, ⟨_, s, hs, hv⟩, hw⟩ := (hz.2 k (d k) (hd k)).2 (c k)
      exact ⟨r, s, hs, hv, hw⟩
    choose r s hs hv hw using key
    obtain ⟨t, ht⟩ : ∃ t, gv t = segreCoord y d / segreCoord y c := hc.2 d
    have hxd : segreCoord y d ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => (hz.2 k (d k) (hd k)).1
    have hxc : segreCoord y c ≠ 0 := hc.1
    have hone : t * ∏ k, s k = 1 := by
      refine hinj ?_
      rw [map_mul, map_prod, ht, map_one]
      simp only [hs]
      rw [Finset.prod_div_distrib]
      change segreCoord y d / segreCoord y c * (segreCoord y c / segreCoord y d) = 1
      field_simp
    have hval := congrArg ev hone
    rw [map_mul, map_prod, map_one] at hval
    simp only [hv] at hval
    have hr : ∏ k, r k ≠ 0 := right_ne_zero_of_mul_eq_one hval
    intro k
    rw [hw k]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.1 hr k (Finset.mem_univ k)) (hd k).ne_zero
  · obtain ⟨s, hs⟩ : ∃ s, gv s = f := hf.2.1
    obtain ⟨t, ht⟩ : ∃ t, gv t = f⁻¹ := hf.2.2
    have hone : s * t = 1 := by
      refine hinj ?_
      rw [map_mul, hs, ht, map_one, mul_inv_cancel₀ hf.1]
    have hval := congrArg ev hone
    rw [map_mul, map_one] at hval
    exact ⟨ev s, (GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w h hz f _).1 ⟨h, s, hs, rfl⟩,
      left_ne_zero_of_mul_eq_one hval⟩

variable {F : Type} [AddCommGroup F] [Module Ω F] {r : ℕ} {W : ChartBundle ℤ (segreCoord y) r F} {L : Lat ξ F}

theorem exists_frames_on_chart (hT : CoordTie ℤ ξ (segreCoord y)) (hV : L.IsVB r ⊤)
    (hC : L.IsChartOf (segreCoord y) W.lat) (c : (k : K) → J k) (hc : segreCoord y c ≠ 0) :
    ∃ S : Set (Ω × (Fin r → F)), S.Finite ∧ (∀ a ∈ S, IsFrameOver y W c a.1 a.2) ∧
      ∀ p : Cpt ξ, InChart ξ (segreCoord y) c p → ∃ a ∈ S, unitAt ξ p a.1 := by
  obtain ⟨U, hU, hmem⟩ := hT.affine c hc
  have loc : ∀ q : U, ∃ (g : Γ(X, U)) (b : Fin r → F), q.1 ∈ X.basicOpen g ∧
      ∀ p : Cpt ξ, p.1 ∈ X.basicOpen g → L.IsFrameAt b p := by
    intro q
    obtain ⟨h, -⟩ := (hmem q.1).1 q.2
    obtain ⟨V, hqV, b, -, hb⟩ := hV ⟨q.1, h⟩ (Set.mem_univ _)
    obtain ⟨g, hgV, hqg⟩ := hU.exists_basicOpen_le (V := V) ⟨q.1, hqV⟩ q.2
    exact ⟨g, b, hqg, fun p hp => hb p (Set.mem_univ _) (hgV hp)⟩
  choose g b hq hfr using loc
  have hsp : ∀ q : U, genPt ξ ⤳ q.1 := fun q => ((hmem q.1).1 q.2).1
  have hpU : ∀ p : Cpt ξ, InChart ξ (segreCoord y) c p → p.1 ∈ U :=
    fun p hp => (hmem p.1).2 ⟨p.2, hp⟩
  let v : U → Ω := fun q => genMap ξ ⟨q.1, hsp q⟩ (X.presheaf.germ U q.1 q.2 (g q))
  have hv : ∀ (q : U) (p : Cpt ξ) (hp : p.1 ∈ U), v q = genMap ξ p (X.presheaf.germ U p.1 hp (g q)) :=
    fun q p hp => genMap_germ_eq (g q) ⟨q.1, hsp q⟩ p q.2 hp
  have hunit : ∀ (q : U) (p : Cpt ξ), p.1 ∈ U → p.1 ∈ X.basicOpen (g q) → unitAt ξ p (v q) := by
    intro q p hp hb
    rw [hv q p hp]
    exact unitAt_of_isUnit ((Scheme.mem_basicOpen _ _ _ hp).1 hb)
  have hbasic : ∀ (q : U) (p : Cpt ξ), p.1 ∈ U → unitAt ξ p (v q) → p.1 ∈ X.basicOpen (g q) := by
    intro q p hp hu
    rw [hv q p hp] at hu
    exact (Scheme.mem_basicOpen _ _ _ hp).2 (isUnit_of_unitAt hT.gen hu)
  have hcov : (U : Set X) ⊆ ⋃ q : U, (X.basicOpen (g q) : Set X) :=
    fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hq _⟩
  obtain ⟨t, ht⟩ := hU.isCompact.elim_finite_subcover _ (fun q => (X.basicOpen (g q)).isOpen) hcov
  refine ⟨(fun q => (v q, b q)) '' (↑t : Set _), t.finite_toSet.image _, ?_, ?_⟩
  · rintro _ ⟨q, -, rfl⟩
    have hne : v q ≠ 0 := (hunit q ⟨q.1, hsp q⟩ q.2 (hq q)).1
    have hring : v q ∈ chartRing ℤ (segreCoord y) c :=
      (hT.ring c hc (v q)).2 fun p hp => ⟨_, (hv q p (hpU p hp)).symm⟩
    exact (GlobalTheory.T.segre_chart_bundle X Ω ξ K J y F r W L hT hV hC c (v q) (b q) hc hring hne).2
      fun p hp hu => hfr q p (hbasic q p (hpU p hp) hu)
  · intro p hp
    obtain ⟨q, hqt, hqp⟩ := Set.mem_iUnion₂.1 (ht (hpU p hp))
    exact ⟨_, ⟨q, hqt, rfl⟩, hunit q p (hpU p hp) hqp⟩

end GlobalTheory.CompanionTheory.Ar.ChartFrames

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem exists_frames_cover_mcPts : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (F : Type) [AddCommGroup F] [Module Ω F] (r : ℕ) (W : ChartBundle ℤ (segreCoord y) r F) (L : Lat ξ F), CoordTie ℤ ξ (segreCoord y) → L.IsVB r ⊤ → L.IsChartOf (segreCoord y) W.lat → ∃ (m : ℕ) (ch : Fin m → (k : K) → J k) (fr : Fin m → Ω) (b : Fin m → Fin r → F), (∀ i, IsFrameOver y W (ch i) (fr i) (b i)) ∧ ∀ w ∈ mcPts (mCoordIdeal y), ∃ i, InFrameDomain y (ch i) (fr i) w := by
  classical
  intro X Ω _ ξ K _ J _ y F _ _ r W L hT hV hC
  have hloc := fun c : {c : (k : K) → J k // segreCoord y c ≠ 0} =>
    ChartFrames.exists_frames_on_chart (W := W) (L := L) hT hV hC c.1 c.2
  choose S hfin hframe hcov using hloc
  let T : Set (((k : K) → J k) × Ω × (Fin r → F)) :=
    ⋃ c, (fun a : Ω × (Fin r → F) => (c.1, a.1, a.2)) '' S c
  have hTfin : T.Finite := Set.finite_iUnion fun c => (hfin c).image _
  haveI := hTfin.to_subtype
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin T
  refine ⟨m, fun i => (e.symm i).1.1, fun i => (e.symm i).1.2.1, fun i => (e.symm i).1.2.2, ?_, ?_⟩
  · have hall : ∀ t ∈ T, IsFrameOver y W t.1 t.2.1 t.2.2 := by
      intro t ht
      obtain ⟨c, a, ha, rfl⟩ := Set.mem_iUnion.1 ht
      exact hframe c a ha
    exact fun i => hall _ (e.symm i).2
  · intro w hw
    obtain ⟨z, h, hz⟩ := (GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT w).1 hw
    obtain ⟨c, hc⟩ := hT.cover ⟨centre z, h⟩
    obtain ⟨a, ha, hu⟩ := hcov ⟨c, hc.1⟩ ⟨centre z, h⟩ hc
    have hmem : (c, a.1, a.2) ∈ T := Set.mem_iUnion.2 ⟨⟨c, hc.1⟩, a, ha, rfl⟩
    refine ⟨e ⟨_, hmem⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact ChartFrames.inFrameDomain_of_unitAt hT hz h hc hu

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSegreChartFramesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_segre_chart_frames : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (F : Type) [AddCommGroup F] [Module Ω F] (r : ℕ) (W : ChartBundle ℤ (segreCoord y) r F) (L : Lat ξ F), CoordTie ℤ ξ (segreCoord y) → L.IsVB r ⊤ → L.IsChartOf (segreCoord y) W.lat → ∃ (m : ℕ) (ch : Fin m → (k : K) → J k) (fr : Fin m → Ω) (b : Fin m → Fin r → F), (∀ i, IsFrameOver y W (ch i) (fr i) (b i)) ∧ ∀ w ∈ mcPts (mCoordIdeal y), ∃ i, InFrameDomain y (ch i) (fr i) w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_frames_cover_mcPts | exact GlobalTheory.CompanionTheory.Ar.exists_frames_cover_mcPts | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_frames_cover_mcPts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConjugateLogPeriods
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConjugateLogPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConjPeriods

open GroundTheory.Heights₂.Heights.Regular

theorem star_mem_logCover {n a : ℕ} (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ logCover h) :
    star w ∈ logCover h := by
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · simpa using hw.1 i
  · simpa using hw.2 k hk

theorem expCover_star {n : ℕ} (a : ℕ) (w : Fin n → ℂ) : expCover a (star w) = star (expCover a w) := by
  funext k
  simp only [expCover, Pi.star_apply]
  split_ifs
  · exact Complex.exp_conj _
  · rfl

theorem isOpen_logCover {n a : ℕ} (h : a ≤ n) : IsOpen (logCover h) := by
  have : logCover h = (⋂ i : Fin a, {w : Fin n → ℂ | (w (Fin.castLE h i)).re < 0}) ∩
      ⋂ k : Fin n, {w : Fin n → ℂ | a ≤ k.val → ‖w k‖ < 1} := by
    ext w; simp [logCover]
  rw [this]
  refine (isOpen_iInter_of_finite fun i => ?_).inter (isOpen_iInter_of_finite fun k => ?_)
  · exact isOpen_lt (Complex.continuous_re.comp (continuous_apply _)) continuous_const
  · by_cases hk : a ≤ k.val
    · simpa [hk] using isOpen_lt (continuous_norm.comp (continuous_apply k)) continuous_const
    · simp [hk]

theorem star_mem_ball {n : ℕ} {z : Fin n → ℂ} (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    star z ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos] at hz ⊢
  intro i
  simpa using hz i

theorem differentiableOn_conj {n g : ℕ} {S : Set (Fin n → ℂ)} (hS : IsOpen S) (hst : ∀ w ∈ S, star w ∈ S)
    {f : (Fin n → ℂ) → Fin g → ℂ} (hf : DifferentiableOn ℂ f S) :
    DifferentiableOn ℂ (fun w => star (f (star w))) S := by
  intro w hw
  have h1 : DifferentiableAt ℂ f (star w) := hf.differentiableAt (hS.mem_nhds (hst w hw))
  have h2 := h1.star_star
  rw [star_star] at h2
  exact h2.differentiableWithinAt

theorem dot_map_conj {g : ℕ} (x y : Fin g → ℂ) (M : Matrix (Fin g) (Fin g) ℂ) :
    x ⬝ᵥ M.map (starRingEnd ℂ) *ᵥ y = star (star x ⬝ᵥ M *ᵥ star y) := by
  simp [dotProduct, Matrix.mulVec, star_sum]

theorem isHermitian_map_conj {g : ℕ} {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian) :
    (M.map (starRingEnd ℂ)).IsHermitian := by
  ext i j
  have := hM.apply i j
  simp [Matrix.conjTranspose_apply, ← this]

theorem star_single {n : ℕ} (c : Fin n) :
    star (Pi.single c (2 * Real.pi * Complex.I) : Fin n → ℂ) = -Pi.single c (2 * Real.pi * Complex.I) := by
  funext k
  by_cases hk : k = c
  · subst hk
    simp
  · simp [hk]

theorem sub_single_mem_logCover {n a : ℕ} (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ logCover h) (i : Fin a) :
    w - Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I) ∈ logCover h := by
  refine ⟨fun j => ?_, fun k hk => ?_⟩
  · by_cases hj : Fin.castLE h j = Fin.castLE h i
    · simpa [hj, Pi.single_apply] using (by simpa [hj] using hw.1 j)
    · simpa [Pi.single_apply, hj] using hw.1 j
  · have hki : k ≠ Fin.castLE h i := by
      rintro rfl
      simp at hk
      omega
    simpa [Pi.single_apply, hki] using hw.2 k hk

def conj {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ)
    (hT : ∀ i, Function.Bijective (L.T i)) : Flat.LogPeriods n a g Λ where
  a_le := L.a_le
  free := L.free
  fin := L.fin
  rank := L.rank
  E := -L.E
  alt x := by simp [L.alt x]
  unimod := by
    constructor
    · intro x y hxy
      exact L.unimod.1 (neg_injective hxy)
    · intro f
      obtain ⟨x, hx⟩ := L.unimod.2 (-f)
      exact ⟨x, by simp [hx]⟩
  P w := AddMonoidHom.mk' (fun x => star (L.P (star w) x)) (fun x y => by simp)
  hol x := differentiableOn_conj (isOpen_logCover L.a_le) (fun w hw => star_mem_logCover L.a_le hw) (L.hol x)
  H z := (L.H (star z)).map (starRingEnd ℂ)
  herm w hw := by
    rw [← expCover_star]
    exact isHermitian_map_conj (L.herm _ (star_mem_logCover L.a_le hw))
  pos w hw z hz := by
    rw [← expCover_star, dot_map_conj]
    have h := L.pos _ (star_mem_logCover L.a_le hw) (star z) (by simpa using hz)
    simpa using h
  im w hw x y := by
    simp only [AddMonoidHom.mk'_apply]
    rw [← expCover_star, dot_map_conj]
    have h := L.im _ (star_mem_logCover L.a_le hw) x y
    simp [h]
  T i := ((LinearEquiv.ofBijective (L.T i) (hT i)).symm : Λ ≃ₗ[ℤ] Λ).toLinearMap
  mono i w hw x := by
    set e : Fin _ → ℂ := Pi.single (Fin.castLE L.a_le i) (2 * Real.pi * Complex.I) with he
    have hw₁ : star w - e ∈ logCover L.a_le :=
      sub_single_mem_logCover L.a_le (star_mem_logCover L.a_le hw) i
    have hm := L.mono i _ hw₁ ((LinearEquiv.ofBijective (L.T i) (hT i)).symm x)
    have hTT : L.T i ((LinearEquiv.ofBijective (L.T i) (hT i)).symm x) = x :=
      (LinearEquiv.ofBijective (L.T i) (hT i)).apply_symm_apply x
    rw [hTT, ← he, sub_add_cancel] at hm
    have hs : star (w + e) = star w - e := by
      rw [star_add, he, star_single, sub_eq_add_neg]
    simp only [AddMonoidHom.mk'_apply, LinearEquiv.coe_coe]
    rw [hs, hm]
  W := L.W
  coiso x hx := L.coiso x fun y hy => by simpa using hx y hy
  s x z := star (L.s x (star z))
  s_hol x := differentiableOn_conj Metric.isOpen_ball (fun _ hz => star_mem_ball hz) (L.s_hol x)
  s_eq x w hw := by
    simp only [AddMonoidHom.mk'_apply]
    rw [← expCover_star, L.s_eq x _ (star_mem_logCover L.a_le hw)]
  span := by
    rw [eq_top_iff]
    intro v _
    have key : ∀ y ∈ Submodule.span ℂ (Set.range fun x => L.s x 0),
        star y ∈ Submodule.span ℂ (Set.range fun x => star (L.s x (star (0 : Fin _ → ℂ)))) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, rfl⟩ := hy
        exact Submodule.subset_span ⟨x, by simp⟩
      | zero => simp
      | add y z _ _ hy hz => simpa using Submodule.add_mem _ hy hz
      | smul c y _ hy =>
        rw [star_smul]
        exact Submodule.smul_mem _ _ hy
    have := key (star v) (by rw [L.span]; trivial)
    simpa using this

theorem exists_conj_periodGram : ∀ (n a g r : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ)
    (U : Fin r → (Fin n → ℂ) → Fin g → ℂ), (∀ i, Function.Bijective (L.T i)) →
    ∃ L' : Flat.LogPeriods n a g Λ, ∀ u ∈ Flat.punct n a 1,
      HodgeMetric.periodGram L' (fun k u' => star (U k (star u'))) u =
        (HodgeMetric.periodGram L U (star u)).map (starRingEnd ℂ) := by
  intro n a g r Λ _ L U hT
  refine ⟨conj L hT, fun u _ => ?_⟩
  ext i j
  simp only [HodgeMetric.periodGram, Matrix.of_apply, Matrix.map_apply]
  change _ * (_ ⬝ᵥ ((L.H (star u)).map (starRingEnd ℂ)) *ᵥ _) = _
  rw [dot_map_conj, map_mul, Complex.conj_ofReal]
  simp

end GlobalTheory.CompanionTheory.Ar.Flat.ConjPeriods
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConjugateLogPeriodsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugate_log_periods : ∀ (n a g r : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (U : Fin r → (Fin n → ℂ) → Fin g → ℂ), (∀ i, Function.Bijective (L.T i)) → ∃ L' : Flat.LogPeriods n a g Λ, ∀ u ∈ Flat.punct n a 1, HodgeMetric.periodGram L' (fun k u' => star (U k (star u'))) u = (HodgeMetric.periodGram L U (star u)).map (starRingEnd ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ConjPeriods.exists_conj_periodGram | exact GlobalTheory.CompanionTheory.Ar.Flat.ConjPeriods.exists_conj_periodGram | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ConjPeriods.exists_conj_periodGram <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperNormalCompactification
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IntegralModelFacts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.Xgn.IntegralModelFacts

theorem mem_range_spMap {O F : Type} [CommRing O] [Field F] (β : O →+* F) (hβ : Function.Injective β)
    (x : Sp O) : x ∈ Set.range (spMap β) ↔ ∀ o : O, o ≠ 0 → o ∉ x.asIdeal := by
  constructor
  · rintro ⟨y, rfl⟩ o ho hmem
    have h1 : β o ∈ (y : PrimeSpectrum F).asIdeal := hmem
    have hp : (y : PrimeSpectrum F).asIdeal.IsPrime := PrimeSpectrum.isPrime (y : PrimeSpectrum F)
    have h2 : (y : PrimeSpectrum F).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    rw [h2, Ideal.mem_bot] at h1
    exact ho (hβ (by rw [h1, map_zero]))
  · intro hx
    refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F), ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap β ⊥ = x.asIdeal
    ext o
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    constructor
    · intro h
      rw [(injective_iff_map_eq_zero β).1 hβ o h]
      exact zero_mem _
    · intro hmem
      by_contra hne
      exact hx o (fun h0 => hne (by rw [h0, map_zero])) hmem

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem lieMult_pt (Y : Model Xo c β) (τ : E →+* ℂ) (hτ : τ (H.rt : E) = H.rt0) {Ω : Type} [Field Ω]
    (i : c.F →+* Ω) (y : Sp Ω ⟶ Xo.XF c) (hy : y ≫ pullback.snd _ _ = spMap i) :
    LieMult Y.t.act (y ≫ Y.j) (i.comp (tauIn c τ)) D.p ∧
      LieMult Y.t.act (y ≫ Y.j) (i.comp (tauIn c (ComplexEmbedding.conjugate τ))) D.q := by
  haveI := Y.oF.t.semi.smooth
  let K := AlgebraicClosure Ω
  let e : Ω →+* K := algebraMap Ω K
  have hx : (spMap e ≫ y) ≫ (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s) =
      spMap (e.comp (i.comp (IntermediateField.inclusion c.le).toRingHom)) := by
    rw [pullback.condition, ← Category.assoc, Category.assoc _ y, hy]
    simp only [spMap, ← Spec.map_comp]
    rfl
  have hdet := (Y.oF.geom K (spMap e ≫ y) _ hx).1
  have key : ∀ (σ : 𝓞 E →+* Ω) (n : ℕ), LieMult Y.oF.t.act (spMap e ≫ y) (e.comp σ) n →
      LieMult Y.t.act (y ≫ Y.j) σ n := by
    intro σ n h
    rw [GlobalTheory.DetExtend.lieMult_extend] at h
    exact (GlobalTheory.LiePull.lieMult_pull (𝓞 E) _ _ Y.t.G Y.oF.t.G Y.j Y.m.cm.F Y.t.act Y.oF.t.act
      Y.m.cart Y.m.act Ω y σ n).1 h
  have hρ : ∀ σ : E →+* ℂ, (e.comp (i.comp (tauIn c σ))) H.rt =
      (e.comp (i.comp (IntermediateField.inclusion c.le).toRingHom)) (baseKA l).ρ ↔ σ (H.rt : E) = H.rt0 := by
    intro σ
    simp only [RingHom.comp_apply]
    rw [e.injective.eq_iff, i.injective.eq_iff, Subtype.ext_iff]
    rfl
  refine ⟨key _ _ ((hdet (e.comp (i.comp (tauIn c τ)))).1 ((hρ τ).2 hτ)),
    key _ _ ((hdet (e.comp (i.comp (tauIn c (ComplexEmbedding.conjugate τ))))).2 ?_)⟩
  intro h
  have h1 := (hρ _).1 h
  rw [ComplexEmbedding.conjugate_coe_eq, hτ,
    GlobalTheory.CompanionTheory.Ar.EigRank.rt0_conj_neg_ne_zero H.d_prime.pos H.sqrt_neg_disc_sq] at h1
  have h2 : (2 : ℂ) * H.rt0 = 0 := by linear_combination -h1
  have h0 : H.rt0 = 0 := (mul_eq_zero.1 h2).resolve_left two_ne_zero
  have h3 := H.sqrt_neg_disc_sq
  rw [h0] at h3
  have h4 : (H.d : ℂ) = 0 := by linear_combination h3
  exact H.d_prime.ne_zero (by exact_mod_cast h4)

end PositivityTheory.Xgn.IntegralModelFacts

private theorem normalCpt_of_isNormalScheme_isCptGen {X : Scheme} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (hg : GlobalTheory.CompanionTheory.Ar.IsCptGen ξ) :
    GlobalTheory.CompanionTheory.Ar.Flat.NormalCpt ξ := by
  intro p a ha
  obtain ⟨hdom, hic⟩ := hX p.1
  have hinj : Function.Injective (GlobalTheory.CompanionTheory.Ar.genMap ξ p) := hg.inj p
  have hfrac : ∀ z : Ω, ∃ r t : X.presheaf.stalk p.1, GlobalTheory.CompanionTheory.Ar.genMap ξ p t ≠ 0 ∧
      z * GlobalTheory.CompanionTheory.Ar.genMap ξ p t = GlobalTheory.CompanionTheory.Ar.genMap ξ p r := by
    intro z
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := p.1) (U := ⊤) trivial
    have hgU : GlobalTheory.CompanionTheory.Ar.genPt ξ ∈ U := p.2.mem_open U.2 hpU
    letI : Algebra Γ(X, U) (X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ)) :=
      (X.presheaf.germ U _ hgU).hom.toAlgebra
    haveI := hU.isLocalization_stalk ⟨_, hgU⟩
    have hφ : ∀ u, GlobalTheory.CompanionTheory.Ar.genMap ξ p (X.presheaf.germ U p.1 hpU u) =
        (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U _ hgU u) := by
      intro u
      show (X.presheaf.germ U p.1 hpU ≫ X.presheaf.stalkSpecializes p.2 ≫
        Scheme.stalkClosedPointTo ξ).hom u = _
      rw [← TopCat.Presheaf.germ_stalkSpecializes X.presheaf hpU p.2]
      rfl
    obtain ⟨s, hs⟩ : ∃ s : X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ),
        (Scheme.stalkClosedPointTo ξ).hom s = z := hg.bij.2 z
    obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.surj (S := X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ))
      (hU.primeIdealOf ⟨_, hgU⟩).asIdeal.primeCompl s
    refine ⟨X.presheaf.germ U p.1 hpU r, X.presheaf.germ U p.1 hpU t, ?_, ?_⟩
    · rw [hφ]
      have hu : IsUnit (X.presheaf.germ U _ hgU (t : Γ(X, U))) :=
        IsLocalization.map_units (X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ)) t
      exact (hu.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
    · rw [hφ, hφ, ← hs]
      exact (map_mul (Scheme.stalkClosedPointTo ξ).hom _ _).symm.trans
        (congrArg (Scheme.stalkClosedPointTo ξ).hom hrt)
  letI : Algebra (X.presheaf.stalk p.1) Ω := (GlobalTheory.CompanionTheory.Ar.genMap ξ p).toAlgebra
  haveI : IsFractionRing (X.presheaf.stalk p.1) Ω := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact IsUnit.mk0 _ (fun h => nonZeroDivisors.ne_zero hy (hinj (by
        rw [map_zero]; exact h)))
    · intro z
      obtain ⟨r, t, ht, hz⟩ := hfrac z
      exact ⟨⟨r, ⟨t, mem_nonZeroDivisors_of_ne_zero (fun h => ht (by rw [h, map_zero]))⟩⟩, hz⟩
    · intro x y hxy
      exact ⟨1, by rw [hinj hxy]⟩
  obtain ⟨P, hPm, hP⟩ := ha
  let e : X.presheaf.stalk p.1 ≃+* GlobalTheory.CompanionTheory.Ar.regAt ξ p :=
    RingEquiv.ofBijective (GlobalTheory.CompanionTheory.Ar.genMap ξ p).rangeRestrict
      ⟨fun x y h => hinj (congrArg Subtype.val h), (GlobalTheory.CompanionTheory.Ar.genMap ξ p).rangeRestrict_surjective⟩
  have hcomp : (algebraMap (X.presheaf.stalk p.1) Ω).comp e.symm.toRingHom =
      algebraMap (GlobalTheory.CompanionTheory.Ar.regAt ξ p) Ω := by
    ext u
    change GlobalTheory.CompanionTheory.Ar.genMap ξ p (e.symm u) = (u : Ω)
    conv_rhs => rw [← e.apply_symm_apply u]
    rfl
  have hint : IsIntegral (X.presheaf.stalk p.1) a := by
    refine ⟨P.map e.symm.toRingHom, hPm.map _, ?_⟩
    rw [Polynomial.eval₂_map, hcomp]
    exact hP
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact ⟨y, hy⟩

private theorem mem_range_pullback_fst_iff_unitAt {X : Scheme} {Ω O F : Type} [Field Ω] [CommRing O] [Field F]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (s : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) (β : O →+* F)
    (hβ : Function.Injective β) (k : F →+* Ω) (hg : GlobalTheory.CompanionTheory.Ar.IsCptGen ξ)
    (hs : ξ ≫ s = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (k.comp β)) (x : GlobalTheory.CompanionTheory.Ar.Cpt ξ) :
    x.1 ∈ Set.range (pullback.fst s (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap β)) ↔
      ∀ o : O, o ≠ 0 → GlobalTheory.CompanionTheory.Ar.unitAt ξ x (k (β o)) := by
  rw [Scheme.Pullback.range_fst, Set.mem_preimage,
    PositivityTheory.Xgn.IntegralModelFacts.mem_range_spMap β hβ]
  obtain ⟨θ, hθs⟩ := Spec.map_surjective (X.fromSpecStalk x.1 ≫ s)
  have hgen : ∀ o, GlobalTheory.CompanionTheory.Ar.genMap ξ x (θ.hom o) = k (β o) := by
    have e1 := GlobalTheory.CompanionTheory.Ar.LieCarrier.genMap_fromSpecStalk x
    have h1 : Spec.map (θ ≫ CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.genMap ξ x)) =
        Spec.map (CommRingCat.ofHom (k.comp β)) :=
      (Spec.map_comp _ _).trans ((congrArg (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.genMap ξ x)) ≫ ·) hθs).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ s) e1).trans hs)))
    have h2 := Spec.map_injective h1
    intro o
    exact congrArg (fun f => f.hom o) h2
  have hcp := congrArg (fun f : Spec (X.presheaf.stalk x.1) ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O =>
    f (IsLocalRing.closedPoint (X.presheaf.stalk x.1))) hθs
  have hpt : s x.1 = Spec.map θ (IsLocalRing.closedPoint (X.presheaf.stalk x.1)) :=
    (congrArg s (Scheme.fromSpecStalk_closedPoint (X := X) (x := x.1))).symm.trans hcp.symm
  have hmem : (s x.1).asIdeal = Ideal.comap θ.hom (IsLocalRing.maximalIdeal (X.presheaf.stalk x.1)) :=
    congrArg PrimeSpectrum.asIdeal hpt
  refine forall_congr' fun o => imp_congr_right fun _ => ?_
  refine Iff.trans ?_ (GlobalTheory.CompanionTheory.Ar.unitAt_iff_of_isCptGen ξ hg x _).symm
  rw [hmem, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  constructor
  · intro hu
    exact ⟨θ.hom o, hu, hgen o⟩
  · rintro ⟨u, hu, hu'⟩
    rw [← hgen o] at hu'
    rwa [← hg.inj x hu']

open PositivityTheory.Xgn.IntegralModelFacts in
theorem PositivityTheory.Xgn.integral_model_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ), Function.Injective β → (∀ x : c.F, ∃ a b : O, b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → IsProper Y.s ∧ NormalCpt (Z.ξ₀ ≫ Y.j) ∧ (Z.ξ₀ ≫ Y.j) ≫ Y.s = spMap (Z.inc.comp β) ∧ (∀ x, x ∈ Z.genFib ↔ ∀ o : O, o ≠ 0 → unitAt (Z.ξ₀ ≫ Y.j) x (Z.inc (β o))) ∧ FiniteDimensional Z.Ω Z.V ∧ Module.finrank Z.Ω (eigSp Z.ρ (Z.inc.comp (tauIn c τ))) = D.p ∧ Module.finrank Z.Ω (eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) = D.q := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z τ hβ hfrac hτ
  haveI := Y.t.semi.smooth
  have hlie := PositivityTheory.Xgn.IntegralModelFacts.lieMult_pt Y τ hτ Z.inc Z.ξ₀ Z.over_inc
  have hs : (Z.ξ₀ ≫ Y.j) ≫ Y.s = spMap (Z.inc.comp β) := by
    rw [Category.assoc, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j_s, ← Category.assoc, Z.over_inc]
    simp only [spMap, ← Spec.map_comp]
    rfl
  refine ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.projProper O Y.X Y.s Y.proj, normalCpt_of_isNormalScheme_isCptGen _ Y.normal Z.gen, hs,
    fun x => mem_range_pullback_fst_iff_unitAt _ Y.s β hβ Z.inc Z.gen hs x,
    (PositivityTheory.HtPt.Htat.lie_fin _ _ _ _ _ Z.M).1, ?_, ?_⟩
  · exact GlobalTheory.CompanionTheory.Ar.EigRank.finrank_eigSp_of_lieMult _ _ _ _ _ _ _ _ _ Z.M Z.ρ Z.act hlie.1
  · exact GlobalTheory.CompanionTheory.Ar.EigRank.finrank_eigSp_of_lieMult _ _ _ _ _ _ _ _ _ Z.M Z.ρ Z.act hlie.2
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperNormalCompactification
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem model_cpt_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ), Function.Injective β → (∀ x : c.F, ∃ a b : O, b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → IsProper Y.s ∧ NormalCpt (Z.ξ₀ ≫ Y.j) ∧ (Z.ξ₀ ≫ Y.j) ≫ Y.s = spMap (Z.inc.comp β) ∧ (∀ x, x ∈ Z.genFib ↔ ∀ o : O, o ≠ 0 → unitAt (Z.ξ₀ ≫ Y.j) x (Z.inc (β o))) ∧ FiniteDimensional Z.Ω Z.V ∧ Module.finrank Z.Ω (eigSp Z.ρ (Z.inc.comp (tauIn c τ))) = D.p ∧ Module.finrank Z.Ω (eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) = D.q :=
  PositivityTheory.Xgn.integral_model_facts

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperNormalCompactificationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_normal_compactification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ), Function.Injective β → (∀ x : c.F, ∃ a b : O, b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → IsProper Y.s ∧ NormalCpt (Z.ξ₀ ≫ Y.j) ∧ (Z.ξ₀ ≫ Y.j) ≫ Y.s = spMap (Z.inc.comp β) ∧ (∀ x, x ∈ Z.genFib ↔ ∀ o : O, o ≠ 0 → unitAt (Z.ξ₀ ≫ Y.j) x (Z.inc (β o))) ∧ FiniteDimensional Z.Ω Z.V ∧ Module.finrank Z.Ω (eigSp Z.ρ (Z.inc.comp (tauIn c τ))) = D.p ∧ Module.finrank Z.Ω (eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) = D.q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.model_cpt_facts | exact GlobalTheory.CompanionTheory.Ar.Flat.model_cpt_facts | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.model_cpt_facts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArtinSchreierCocycleRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSectionOfPow
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechRoot

theorem gen_res {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} [Nonempty V] [Nonempty W]
    (h : W ≤ V) (s : Γ(X, V)) :
    (X.germToFunctionField W).hom ((X.presheaf.map (homOfLE h).op).hom s) = (X.germToFunctionField V).hom s :=
  X.presheaf.germ_res_apply (homOfLE h) _ _ s

theorem nonempty_inf {X : Scheme.{0}} [IsIntegral X] (V W : X.Opens) [hV : Nonempty V] [hW : Nonempty W] :
    Nonempty (V ⊓ W : X.Opens) := by
  obtain ⟨⟨v, hv⟩⟩ := hV
  obtain ⟨⟨w, hw⟩⟩ := hW
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter V.isOpen W.isOpen ⟨v, hv⟩ ⟨w, hw⟩
  exact ⟨⟨z, hz⟩⟩

theorem exists_section_of_pow {X : Scheme.{0}} [IsIntegral X] (hN : ∀ b : X, IsIntegrallyClosed (X.presheaf.stalk b))
    {l : ℕ} (hl : 0 < l) (V : X.Opens) [Nonempty V] (f : Γ(X, V)) (t : X.functionField)
    (ht : t ^ l = (X.germToFunctionField V).hom f) : ∃ s : Γ(X, V), (X.germToFunctionField V).hom s = t := by
  refine IsNormalScheme.exists_germToFunctionField_eq_of_locally V t fun x hx => ?_
  refine exists_germToFunctionField_eq_of_mem_range_stalk ?_ hx
  haveI := hN x
  refine IsIntegrallyClosed.algebraMap_eq_of_integral (IsIntegral.of_pow hl ?_)
  rw [ht, ← Scheme.algebraMap_germ_eq_germToFunctionField X hx f]
  exact isIntegral_algebraMap

theorem charP_functionField {X : Scheme.{0}} [IsIntegral X] (l : ℕ) [Fact l.Prime] (h : (l : Γ(X, ⊤)) = 0) :
    CharP X.functionField l := by
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  refine (CharP.charP_iff_prime_eq_zero Fact.out).2 ?_
  rw [← map_natCast (X.germToFunctionField ⊤).hom, h, map_zero]

theorem exists_root : ∀ (X : Scheme.{0}) [IsIntegral X], (∀ b : X, IsIntegrallyClosed (X.presheaf.stalk b)) → ∀ (l : ℕ) [Fact l.Prime], (l : Γ(X, ⊤)) = 0 → ∀ (J : Type) (U : J → X.Opens) (f : ∀ j, Γ(X, U j)) (n : ∀ j j', Γ(X, U j ⊓ U j')), (∀ j j', (X.presheaf.map (homOfLE (inf_le_left : U j ⊓ U j' ≤ U j)).op).hom (f j) - (X.presheaf.map (homOfLE (inf_le_right : U j ⊓ U j' ≤ U j')).op).hom (f j') = n j j' ^ l) → ∀ (i : J) (b : X) (hb : b ∈ U i) (h : FractionRing (X.presheaf.stalk b)), h ^ l = algebraMap (X.presheaf.stalk b) _ ((X.presheaf.germ (U i) b hb).hom (f i)) → ∃ H : ∀ j, Γ(X, U j), ∀ j j', (X.presheaf.map (homOfLE (inf_le_left : U j ⊓ U j' ≤ U j)).op).hom (H j) - (X.presheaf.map (homOfLE (inf_le_right : U j ⊓ U j' ≤ U j')).op).hom (H j') = n j j' := by
  intro X _ hN l _ hl J U f n hf i b hb h hh
  haveI := charP_functionField l hl
  have hl0 : 0 < l := (Fact.out : l.Prime).pos
  haveI : Nonempty (U i) := ⟨⟨b, hb⟩⟩
  let e := FractionRing.algEquiv (X.presheaf.stalk b) X.functionField
  have he : e h ^ l = (X.germToFunctionField (U i)).hom (f i) := by
    rw [← map_pow, hh, AlgEquiv.commutes]
    exact Scheme.algebraMap_germ_eq_germToFunctionField X hb (f i)
  have hg : ∀ j j' [Nonempty (U j)] [Nonempty (U j')] [Nonempty (U j ⊓ U j' : X.Opens)],
      (X.germToFunctionField (U j)).hom (f j) - (X.germToFunctionField (U j')).hom (f j') =
        (X.germToFunctionField (U j ⊓ U j')).hom (n j j') ^ l := by
    intro j j' _ _ _
    rw [← map_pow, ← hf, map_sub, gen_res, gen_res]
  have ex : ∀ j, ∃ H : Γ(X, U j), ∀ [Nonempty (U j)],
      (X.germToFunctionField (U j)).hom H ^ l = (X.germToFunctionField (U j)).hom (f j) := by
    intro j
    by_cases hj : Nonempty (U j)
    · haveI := nonempty_inf (U j) (U i)
      have ht : (e h + (X.germToFunctionField (U j ⊓ U i)).hom (n j i)) ^ l =
          (X.germToFunctionField (U j)).hom (f j) := by
        rw [add_pow_char, he, ← hg, add_sub_cancel]
      obtain ⟨s, hs⟩ := exists_section_of_pow hN hl0 (U j) (f j) _ ht
      exact ⟨s, by intro _; rw [hs, ht]⟩
    · exact ⟨0, by intro h; exact absurd h hj⟩
  choose H hH using ex
  refine ⟨H, fun j j' => ?_⟩
  by_cases hj : Nonempty (U j ⊓ U j' : X.Opens)
  · obtain ⟨⟨z, hz⟩⟩ := id hj
    haveI : Nonempty (U j) := ⟨⟨z, hz.1⟩⟩
    haveI : Nonempty (U j') := ⟨⟨z, hz.2⟩⟩
    apply X.germToFunctionField_injective (U j ⊓ U j')
    apply frobenius_inj X.functionField l
    change (X.germToFunctionField (U j ⊓ U j')).hom _ ^ l = (X.germToFunctionField (U j ⊓ U j')).hom _ ^ l
    rw [map_sub, gen_res, gen_res, sub_pow_char, hH, hH, hg]
  · exact fn_ext (V := U j ⊓ U j') fun x hx => absurd ⟨⟨x, hx⟩⟩ hj

end GlobalTheory.CechRoot
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArtinSchreierCocycleRoot
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CompanionTheory.Ar.CechP.coboundary_of_pow_coboundary : ∀ (Z : Scheme.{0}) [IsIntegral Z] (p : ℕ) [Fact p.Prime] [CharP Z.functionField p], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ (J : Type) (U : J → Z.Opens) (n : ∀ a b, Γ(Z, U a ⊓ U b)) (h : ∀ a, Γ(Z, U a)) (a₀ : J) [Nonempty (U a₀)], (∀ a b, n a b ^ p = (Z.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ≤ U a)).op).hom (h a) - (Z.presheaf.map (homOfLE (inf_le_right : U a ⊓ U b ≤ U b)).op).hom (h b)) → (∃ r : Z.functionField, r ^ p = (Z.germToFunctionField (U a₀)).hom (h a₀)) → ∃ s : ∀ a, Γ(Z, U a), ∀ a b, n a b = (Z.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ≤ U a)).op).hom (s a) - (Z.presheaf.map (homOfLE (inf_le_right : U a ⊓ U b ≤ U b)).op).hom (s b) := by
  intro Z _ p _ _ hN J U n h a₀ _ hn ⟨r, hr⟩
  have hg : genericPoint Z ∈ U a₀ := ((genericPoint_spec Z).mem_open_set_iff (U a₀).isOpen).mpr (by
    obtain ⟨⟨z, hz⟩⟩ := ‹Nonempty (U a₀)›
    exact ⟨z, trivial, hz⟩)
  haveI : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
  have hp : (p : Γ(Z, ⊤)) = 0 := by
    apply Z.germToFunctionField_injective ⊤
    rw [map_natCast, map_zero]
    exact CharP.cast_eq_zero _ p
  obtain ⟨s, hs⟩ := GlobalTheory.CechRoot.exists_root Z (fun b => (hN b).2) p hp J U h n
    (fun a b => (hn a b).symm) a₀ (genericPoint Z) hg (algebraMap Z.functionField _ r)
    (by rw [← map_pow, hr])
  exact ⟨s, fun a b => (hs a b).symm⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArtinSchreierCocycleRootStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artin_schreier_cocycle_root : ∀ (Z : Scheme.{0}) [IsIntegral Z] (p : ℕ) [Fact p.Prime] [CharP Z.functionField p], IsNormalScheme Z → ∀ (J : Type) (U : J → Z.Opens) (n : ∀ a b, Γ(Z, U a ⊓ U b)) (h : ∀ a, Γ(Z, U a)) (a₀ : J) [Nonempty (U a₀)], (∀ a b, n a b ^ p = (Z.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ≤ U a)).op).hom (h a) - (Z.presheaf.map (homOfLE (inf_le_right : U a ⊓ U b ≤ U b)).op).hom (h b)) → (∃ r : Z.functionField, r ^ p = (Z.germToFunctionField (U a₀)).hom (h a₀)) → ∃ s : ∀ a, Γ(Z, U a), ∀ a b, n a b = (Z.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ≤ U a)).op).hom (s a) - (Z.presheaf.map (homOfLE (inf_le_right : U a ⊓ U b ≤ U b)).op).hom (s b) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CechP.coboundary_of_pow_coboundary | exact GlobalTheory.CompanionTheory.Ar.CechP.coboundary_of_pow_coboundary | (intros; apply GlobalTheory.CompanionTheory.Ar.CechP.coboundary_of_pow_coboundary <;> assumption)
end
end

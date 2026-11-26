module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinear
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSpanProjectionBound

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PieceLocalizationAtElement
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PieceLocalizationAtElement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem exists_basicOpen_piece (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (U : X.Opens) (R : Subring Ω) (a : Ω) (hc : IsCptGen ξ) (hP : IsPiece ξ U R) (haR : a ∈ R)
    (ha0 : a ≠ 0) :
    ∃ U' : X.Opens, IsPiece ξ U' (locSub R a) ∧ ∀ q : Cpt ξ, q.1 ∈ U' ↔ q.1 ∈ U ∧ unitAt ξ q a := by
  by_cases hη : genPt ξ ∈ U
  swap
  · have hno : ∀ q : Cpt ξ, q.1 ∉ U := fun q hq => hη (q.2.mem_open U.isOpen hq)
    refine ⟨U, ⟨hP.affine, hP.spec, fun b => ?_⟩, fun q => ?_⟩
    · refine ⟨fun _ q hq => absurd hq (hno q), fun _ => le_locSub R a ?_⟩
      exact (hP.ring b).2 fun q hq => absurd hq (hno q)
    · exact ⟨fun h => absurd h (hno q), fun h => h.1⟩
  obtain ⟨-, hrng⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X Ω ξ hc U hη hP.spec
  obtain ⟨s, hs⟩ := (hrng a).2 ((hP.ring a).1 haR)
  have hga : ∀ (q : Cpt ξ) (hq : q.1 ∈ U), genMap ξ q (X.presheaf.germ U q.1 hq s) = a :=
    fun q hq => (genMap_germ_eq_stalk_closed ξ q U hq hη s).trans hs
  have hmem : ∀ q : Cpt ξ, q.1 ∈ X.basicOpen s ↔ q.1 ∈ U ∧ unitAt ξ q a := by
    intro q
    constructor
    · intro hq
      have hqU : q.1 ∈ U := X.basicOpen_le s hq
      have hu := (Scheme.mem_basicOpen X s q.1 hqU).1 hq
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      have h1 : a * genMap ξ q v = 1 := by
        rw [← hga q hqU, ← map_mul, hv, map_one]
      exact ⟨hqU, ha0, ⟨_, hga q hqU⟩, ⟨v, (inv_eq_of_mul_eq_one_right h1).symm⟩⟩
    · rintro ⟨hqU, -, -, ⟨t, ht⟩⟩
      refine (Scheme.mem_basicOpen X s q.1 hqU).2 (isUnit_iff_exists_inv.2 ⟨t, hc.inj q ?_⟩)
      rw [map_mul, map_one, hga q hqU, ht, mul_inv_cancel₀ ha0]
  have hreg : ∀ c : Ω, c ∈ regAt ξ (Subtype.mk (genPt ξ) specializes_rfl : Cpt ξ) := by
    intro c
    obtain ⟨y, hy⟩ := hc.bij.2 c
    refine ⟨y, ?_⟩
    have e : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
      TopCat.Presheaf.stalkSpecializes_refl _ _
    change (X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) ≫
      Scheme.stalkClosedPointTo ξ).hom y = c
    rw [e]
    exact hy
  have hη' : genPt ξ ∈ X.basicOpen s :=
    (hmem (Subtype.mk (genPt ξ) specializes_rfl : Cpt ξ)).2 ⟨hη, ha0, hreg a, hreg a⁻¹⟩
  refine ⟨X.basicOpen s, ⟨hP.affine.basicOpen s, fun q hq => hP.spec q (X.basicOpen_le s hq),
    fun b => ?_⟩, hmem⟩
  constructor
  · intro hb q hq
    obtain ⟨k, hk⟩ := (mem_locSub_iff haR ha0 b).1 hb
    obtain ⟨hqU, -, -, hinv⟩ := (hmem q).1 hq
    have h1 := (hP.ring _).1 hk q hqU
    have e : b = a⁻¹ ^ k * (a ^ k * b) := by
      rw [inv_pow, ← _root_.mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ha0), _root_.one_mul]
    rw [e]
    exact (regAt ξ q).mul_mem ((regAt ξ q).pow_mem hinv _) h1
  · intro hb
    obtain ⟨-, hrng'⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X Ω ξ hc (X.basicOpen s) hη'
      (fun q hq => hP.spec q (X.basicOpen_le s hq))
    obtain ⟨t, ht⟩ := (hrng' b).2 hb
    have hloc := hP.affine.isLocalization_basicOpen s
    obtain ⟨n, c, hcn⟩ := IsLocalization.Away.surj s t
    have hres : ∀ x : Γ(X, U),
        (X.presheaf.germ (X.basicOpen s) (genPt ξ) hη' ≫ Scheme.stalkClosedPointTo ξ).hom
          (algebraMap Γ(X, U) Γ(X, X.basicOpen s) x) =
        (X.presheaf.germ U (genPt ξ) hη ≫ Scheme.stalkClosedPointTo ξ).hom x := by
      intro x
      have := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (X.basicOpen_le s)) (genPt ξ) hη' x
      exact congrArg (Scheme.stalkClosedPointTo ξ).hom this
    have key : a ^ n * b = (X.presheaf.germ U (genPt ξ) hη ≫ Scheme.stalkClosedPointTo ξ).hom c := by
      have := congrArg (X.presheaf.germ (X.basicOpen s) (genPt ξ) hη' ≫
        Scheme.stalkClosedPointTo ξ).hom hcn
      rw [map_mul, map_pow, hres, hres, hs, ht] at this
      rw [← this, _root_.mul_comm]
    refine (mem_locSub_iff haR ha0 b).2 ⟨n, (hP.ring _).2 fun q hq => ?_⟩
    rw [key]
    exact (hrng _).1 ⟨c, rfl⟩ q hq

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PieceLocalizationAtElementStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piece_localization_at_element : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (R : Subring Ω) (a : Ω), IsCptGen ξ → IsPiece ξ U R → a ∈ R → a ≠ 0 → ∃ U' : X.Opens, IsPiece ξ U' (locSub R a) ∧ ∀ q : Cpt ξ, q.1 ∈ U' ↔ q.1 ∈ U ∧ unitAt ξ q a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_basicOpen_piece | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_basicOpen_piece | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_basicOpen_piece <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateLatticeLeOmega
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateLatticeLeOmega
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HtHoriz

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
  {E : Type} [AddCommGroup E] [Module Ω E] {R : Type} [CommRing R] {L : Type} [AddCommGroup L] [Module R L]

theorem map_add_of_compat (M : LieModel G ξ E) {x : Spec (CommRingCat.of R) ⟶ X} {k : R →+* Ω}
    (hx : Spec.map (CommRingCat.ofHom k) ≫ x = ξ) (M₀ : LieModel G x L) (j : L → E)
    (hj : ∀ e, (M.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ (M₀.pt e).left)
    (a b : L) : j (a + b) = j a + j b := by
  have key : ∀ e, M.pt (j e) = LieCarrier.epsHom k x ξ hx ≫ M₀.pt e :=
    fun e => Over.OverMorphism.ext (hj e)
  apply M.inj
  rw [M.add, key, key, key, M₀.add, MonObj.comp_mul]

theorem map_smul_of_compat (M : LieModel G ξ E) {x : Spec (CommRingCat.of R) ⟶ X} {k : R →+* Ω}
    (M₀ : LieModel G x L) (j : L → E)
    (hj : ∀ e, (M.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ (M₀.pt e).left)
    (c : R) (e : L) : j (c • e) = k c • j e := by
  apply M.inj
  apply Over.OverMorphism.ext
  rw [hj, M₀.smul, M.smul, hj, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, LieCarrier.dualMap_epsMul]

theorem isHT_add_natCast_smul {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : BT.QFGroup R T)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {i : Γ.G.left ⟶ G.left}
    {L : Type} [AddCommGroup L] [Module R L] {M : LieModel G x L} {N : ℕ} {χ : T →* Rˣ}
    {w : Module.Dual R L} (h : Γ.IsHT i M N χ w) (u : Module.Dual R L) :
    Γ.IsHT i M N χ (w + (N : R) • u) := by
  obtain ⟨s, hs, h⟩ := h
  refine ⟨s, hs, fun e => ?_⟩
  obtain ⟨v, h1, h2, h3⟩ := h e
  refine ⟨v, h1, h2, h3.trans ?_⟩
  congr 2
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  exact ⟨-u e, by simp⟩

theorem natCast_smul_isHTFormOver (M : LieModel G ξ E) (N : ℕ) {x : Spec (CommRingCat.of R) ⟶ X} {k : R →+* Ω}
    (hx : Spec.map (CommRingCat.ofHom k) ≫ x = ξ) (hk : Function.Injective k) (h : M.IsHTFormOver N x k 0)
    (w : Module.Dual Ω E)
    (hw : ∀ (e : E) (v : epsAt x ⟶ G), IsTanAt G x v →
      (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ v.left → w e ∈ k.range) :
    M.IsHTFormOver N x k ((N : Ω) • w) := by
  obtain ⟨hd, T, _, Γ, i, L, _, _, M₀, j, χ, w₀, ht, hj, hHT, h0⟩ := h
  have hreg : ∀ e, ∃ r, k r = w (j e) := fun e => hw (j e) (M₀.pt e) (M₀.tan e) (hj e)
  choose f hf using hreg
  let u : Module.Dual R L :=
    { toFun := f
      map_add' := fun a b => hk (by rw [map_add (f := _), hf, hf, hf, map_add_of_compat M hx M₀ j hj, map_add (f := _)])
      map_smul' := fun c e => hk (by
        simp only [RingHom.id_apply, smul_eq_mul, map_mul]
        rw [hf, hf, map_smul_of_compat M M₀ j hj, map_smul, smul_eq_mul]) }
  refine ⟨hd, T, _, Γ, i, L, _, _, M₀, j, χ, w₀ + (N : R) • u, ht, hj, isHT_add_natCast_smul Γ hHT u, fun e => ?_⟩
  have h1 : k (w₀ e) = 0 := (h0 e).symm
  have h2 : k (u e) = w (j e) := hf e
  simp [h1, h2]

end GlobalTheory.CompanionTheory.Ar.HtHoriz

namespace GlobalTheory.CompanionTheory.Ar

theorem htLat_le_omLat_and_smul_mem : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G]
    [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (N : ℕ) (p : Cpt ξ),
    IsCptGen ξ → Smooth G.hom → M.htLat N p ≤ M.omLat p ∧
      (M.IsHTFormAt N p 0 → ∀ w ∈ M.omLat p, (N : Ω) • w ∈ M.htLat N p) := by
  intro X Ω _ ξ G _ _ V _ _ M N p hξ _
  refine ⟨?_, ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro w ⟨_, T, _, Γ, i, L, _, _, M₀, j, χ, w₀, -, hj, -, hw⟩ e he
    obtain ⟨v, hv, hev⟩ := ((lieLat_carrier X G Ω ξ V M p).1 e).1 he
    obtain ⟨e₀, rfl⟩ := M₀.onto v hv
    have : j e₀ = e := M.inj (Over.OverMorphism.ext ((hj e₀).trans hev.symm))
    subst this
    exact ⟨w₀ e₀, (hw e₀).symm⟩
  · intro h w hw
    exact Submodule.subset_span (HtHoriz.natCast_smul_isHTFormOver M N (LieCarrier.genMap_fromSpecStalk p) (hξ.inj p) h w
      fun e v hv hev => hw e (Submodule.subset_span ⟨v, hv, hev⟩))

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateLatticeLeOmegaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_lattice_le_omega : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (N : ℕ) (p : Cpt ξ), IsCptGen ξ → Smooth G.hom → M.htLat N p ≤ M.omLat p ∧ (M.IsHTFormAt N p 0 → ∀ w ∈ M.omLat p, (N : Ω) • w ∈ M.htLat N p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.htLat_le_omLat_and_smul_mem | exact GlobalTheory.CompanionTheory.Ar.htLat_le_omLat_and_smul_mem | (intros; apply GlobalTheory.CompanionTheory.Ar.htLat_le_omLat_and_smul_mem <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPullbackCorrespondence
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TorsionAlongGroupPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem tors_push {S S' U : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (a : U ⟶ S') (b : U ⟶ S) (hb : a ≫ f = b) :
    ∃ π : (Over.mk a ⟶ G') →* (Over.mk b ⟶ G), Function.Bijective π ∧ ∀ x, (π x).left = x.left ≫ φ := by
  subst hb
  have hw : ∀ x : Over.mk a ⟶ G', (x.left ≫ φ) ≫ G.hom = a ≫ f := by
    intro x
    have hx : x.left ≫ G'.hom = a := Over.w x
    rw [Category.assoc, h.1.w, ← Category.assoc, hx]
  let F : (Over.mk a ⟶ G') → (Over.mk (a ≫ f) ⟶ G) := fun x => Over.homMk (x.left ≫ φ) (hw x)
  have hF : ∀ x, (F x).left = x.left ≫ φ := fun x => rfl
  have hmul : ∀ x y, F (x * y) = F x * F y := by
    intro x y
    apply Over.OverMorphism.ext
    rw [hF]
    exact (h.2 (Over.mk a) x y (F x) (F y) (hF x) (hF y)).symm
  refine ⟨MonoidHom.mk' F hmul, ⟨?_, ?_⟩, hF⟩
  · intro x y hxy
    apply Over.OverMorphism.ext
    have e1 : (F x).left = (F y).left := congrArg (fun g => Over.Hom.left g) hxy
    rw [hF, hF] at e1
    apply h.1.hom_ext e1
    rw [Over.w x, Over.w y]
  · intro g
    have hg : g.left ≫ G.hom = a ≫ f := Over.w g
    refine ⟨Over.homMk (h.1.lift g.left a hg) (h.1.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    show (h.1.lift g.left a hg) ≫ φ = g.left
    exact h.1.lift_fst _ _ _

theorem tors_iff {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : BT.QFGroup R T) {X : Scheme.{0}}
    {x : Sp R ⟶ X} {G : Over X} [GrpObj G] {G₀ : Over (Sp R)} [GrpObj G₀] {ψ : G₀.left ⟶ G.left} (N : ℕ)
    (h : IsGrpPullback G₀ G x ψ) (i₀ : Γ.G.left ⟶ G₀.left) (hi : i₀ ≫ G₀.hom = Γ.G.hom) :
    Γ.IsTorsionAlong G₀ (𝟙 _) N i₀ ↔ Γ.IsTorsionAlong G x N (i₀ ≫ ψ) := by
  have cancel : ∀ {W : Scheme.{0}} (u v : W ⟶ G₀.left), u ≫ ψ = v ≫ ψ → u ≫ G₀.hom = v ≫ G₀.hom → u = v :=
    fun u v e1 e2 => h.1.hom_ext e1 e2
  have base : ∀ (Y : Over (Sp R)) (y : Y ⟶ Γ.G), (y.left ≫ i₀) ≫ G₀.hom = Y.hom := by
    intro Y y
    rw [Category.assoc, hi]
    exact Over.w y
  have pushY : ∀ (Y : Over (Sp R)), ∃ π : (Over.mk (Y.hom ≫ 𝟙 _) ⟶ G₀) →* (Over.mk (Y.hom ≫ x) ⟶ G),
      Function.Bijective π ∧ ∀ g, (π g).left = g.left ≫ ψ := by
    intro Y
    exact tors_push h (Y.hom ≫ 𝟙 _) (Y.hom ≫ x) (by simp)
  have w1 : ∀ (Y : Over (Sp R)) (g : Over.mk (Y.hom ≫ 𝟙 _) ⟶ G₀), g.left ≫ G₀.hom = Y.hom := by
    intro Y g
    have := Over.w g
    simpa using this
  constructor
  · intro t
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Category.assoc, h.1.w, ← Category.assoc, hi]
    · intro Y y z y₀ z₀ hy hz
      obtain ⟨π, -, hπ⟩ := pushY Y
      let y₁ : Over.mk (Y.hom ≫ 𝟙 _) ⟶ G₀ := Over.homMk (y.left ≫ i₀) (by simpa using base Y y)
      let z₁ : Over.mk (Y.hom ≫ 𝟙 _) ⟶ G₀ := Over.homMk (z.left ≫ i₀) (by simpa using base Y z)
      have ey : π y₁ = y₀ := by
        apply Over.OverMorphism.ext
        rw [hπ, hy]
        show (y.left ≫ i₀) ≫ ψ = _
        rw [Category.assoc]
      have ez : π z₁ = z₀ := by
        apply Over.OverMorphism.ext
        rw [hπ, hz]
        show (z.left ≫ i₀) ≫ ψ = _
        rw [Category.assoc]
      rw [← ey, ← ez, ← map_mul, hπ, t.mul Y y z y₁ z₁ rfl rfl, Category.assoc]
    · intro Y y z e
      apply t.inj Y y z
      apply cancel
      · simpa only [Category.assoc] using e
      · rw [base Y y, base Y z]
    · intro Y g
      obtain ⟨π, ⟨hinj, hsurj⟩, hπ⟩ := pushY Y
      obtain ⟨g₁, rfl⟩ := hsurj g
      rw [← map_pow, ← map_one π, hinj.eq_iff, t.kernel Y g₁, hπ]
      constructor
      · rintro ⟨y, hy⟩
        exact ⟨y, by rw [← hy, Category.assoc]⟩
      · rintro ⟨y, hy⟩
        refine ⟨y, cancel _ _ (by rw [Category.assoc, hy]) ?_⟩
        rw [base Y y, w1 Y g₁]
  · intro t
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hi, Category.comp_id]
    · intro Y y z y₀ z₀ hy hz
      obtain ⟨π, -, hπ⟩ := pushY Y
      have m := t.mul Y y z (π y₀) (π z₀) (by rw [hπ, hy, Category.assoc]) (by rw [hπ, hz, Category.assoc])
      rw [← map_mul, hπ] at m
      apply cancel
      · rw [m, Category.assoc]
      · rw [w1 Y, base Y]
    · intro Y y z e
      apply t.inj Y y z
      simp only [← Category.assoc, e]
    · intro Y g₁
      obtain ⟨π, ⟨hinj, -⟩, hπ⟩ := pushY Y
      rw [← hinj.eq_iff, map_pow, map_one, t.kernel Y (π g₁), hπ]
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨y, cancel _ _ (by rw [Category.assoc, hy]) ?_⟩
        rw [base Y y, w1 Y g₁]
      · rintro ⟨y, hy⟩
        exact ⟨y, by rw [← hy, Category.assoc]⟩

theorem isTorsionAlong_iff_of_isGrpPullback : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (X : Scheme.{0}) (x : Sp R ⟶ X) (G : Over X) [GrpObj G] (G₀ : Over (Sp R)) [GrpObj G₀] (ψ : G₀.left ⟶ G.left) (N : ℕ), IsGrpPullback G₀ G x ψ → (∀ i : Γ.G.left ⟶ G.left, Γ.IsTorsionAlong G x N i → ∃ i₀ : Γ.G.left ⟶ G₀.left, i₀ ≫ ψ = i ∧ Γ.IsTorsionAlong G₀ (𝟙 _) N i₀) ∧ ∀ i₀ : Γ.G.left ⟶ G₀.left, Γ.IsTorsionAlong G₀ (𝟙 _) N i₀ → Γ.IsTorsionAlong G x N (i₀ ≫ ψ) := by
  intro R _ _ T _ Γ X x G _ G₀ _ ψ N h
  refine ⟨?_, ?_⟩
  · intro i t
    have w : i ≫ G.hom = Γ.G.hom ≫ x := t.isOver
    refine ⟨h.1.lift i Γ.G.hom w, h.1.lift_fst _ _ _, ?_⟩
    have e := (tors_iff Γ N h (h.1.lift i Γ.G.hom w) (h.1.lift_snd _ _ _)).2
    rw [h.1.lift_fst] at e
    exact e t
  · intro i₀ t
    have hi : i₀ ≫ G₀.hom = Γ.G.hom := by
      have := t.isOver
      simpa using this
    exact (tors_iff Γ N h i₀ hi).1 t

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPullbackCorrespondence
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem torsionAlong_iff_pullback_torsion : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (X : Scheme.{0}) (x : Sp R ⟶ X) (G : Over X) [GrpObj G] (G₀ : Over (Sp R)) [GrpObj G₀] (ψ : G₀.left ⟶ G.left) (N : ℕ), IsGrpPullback G₀ G x ψ → (∀ i : Γ.G.left ⟶ G.left, Γ.IsTorsionAlong G x N i → ∃ i₀ : Γ.G.left ⟶ G₀.left, i₀ ≫ ψ = i ∧ Γ.IsTorsionAlong G₀ (𝟙 _) N i₀) ∧ ∀ i₀ : Γ.G.left ⟶ G₀.left, Γ.IsTorsionAlong G₀ (𝟙 _) N i₀ → Γ.IsTorsionAlong G x N (i₀ ≫ ψ) :=
  @PositivityTheory.UnitarySelfGeneration.isTorsionAlong_iff_of_isGrpPullback

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPullbackCorrespondenceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_pullback_correspondence : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (X : Scheme.{0}) (x : Sp R ⟶ X) (G : Over X) [GrpObj G] (G₀ : Over (Sp R)) [GrpObj G₀] (ψ : G₀.left ⟶ G.left) (N : ℕ), IsGrpPullback G₀ G x ψ → (∀ i : Γ.G.left ⟶ G.left, Γ.IsTorsionAlong G x N i → ∃ i₀ : Γ.G.left ⟶ G₀.left, i₀ ≫ ψ = i ∧ Γ.IsTorsionAlong G₀ (𝟙 _) N i₀) ∧ ∀ i₀ : Γ.G.left ⟶ G₀.left, Γ.IsTorsionAlong G₀ (𝟙 _) N i₀ → Γ.IsTorsionAlong G x N (i₀ ≫ ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.torsionAlong_iff_pullback_torsion | exact GlobalTheory.CompanionTheory.Ar.torsionAlong_iff_pullback_torsion | (intros; apply GlobalTheory.CompanionTheory.Ar.torsionAlong_iff_pullback_torsion <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleNormalProperPullback
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LineLatticeProperPushdown
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LineLatticeGeneratorCodimOne
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem PositivityTheory.Xgn.line_lattice_generator_codim_one : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X], IsCptGen ξ → NormalCpt ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (p : Cpt ξ) (t : Ω), L.IsVBOn T 1 ⊤ → (∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T) → t ≠ 0 → (∀ q : Cpt ξ, q.1 ⤳ p.1 → ringKrullDim (X.presheaf.stalk q.1) = 1 → L.IsGenAt q t) → L.IsGenAt p t := by
  intro X Ω _ ξ _ hg hn L T p t hL hT ht hq
  obtain ⟨U, hU, b, -, h⟩ := hL p (hT p specializes_rfl)
  have hr : Set.range b = {b 0} := by
    ext x
    simp [Fin.exists_fin_one, eq_comm]
  have hgen : ∀ q : Cpt ξ, q.1 ⤳ p.1 → b 0 ≠ 0 ∧ L q = Submodule.span (regAt ξ q) {b 0} := by
    intro q hqp
    obtain ⟨h1, h2⟩ := h q (hT q hqp) (hqp.mem_open U.2 hU)
    exact ⟨h1.ne_zero 0, by rw [h2, hr]⟩
  obtain ⟨he, hp⟩ := hgen p specializes_rfl
  have hu : ∀ q : Cpt ξ, q.1 ⤳ p.1 → ringKrullDim (X.presheaf.stalk q.1) = 1 → unitAt ξ q (t / b 0) := by
    intro q hqp hd
    obtain ⟨u, hu, e⟩ := ZUnit.exists_of_span_eq ht ((hq q hqp hd).2.symm.trans (hgen q hqp).2)
    rwa [e, smul_eq_mul, mul_div_cancel_right₀ _ he]
  have h1 : t / b 0 ∈ regAt ξ p :=
    mem_regAt_of_codim_one X Ω ξ hg hn p _ fun q hqp hd => (hu q hqp hd).2.1
  have h2 : (t / b 0)⁻¹ ∈ regAt ξ p :=
    mem_regAt_of_codim_one X Ω ξ hg hn p _ fun q hqp hd => (hu q hqp hd).2.2
  refine ⟨ht, ?_⟩
  rw [hp]
  refine le_antisymm ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  · refine ⟨⟨_, h2⟩, ?_⟩
    change (t / b 0)⁻¹ * t = b 0
    field_simp
  · refine ⟨⟨_, h1⟩, ?_⟩
    change (t / b 0) * b 0 = t
    field_simp
end

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.LineLatticePushdown

theorem exists_lift {X X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X')
    (f : X' ⟶ X) [IsProper f] (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra V Ω']
    [IsFractionRing V Ω'] (z : Spec (CommRingCat.of V) ⟶ X)
    (w : ξ' ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V Ω')) ≫ z) :
    ∃ p' : Cpt ξ', f p'.1 = z (IsLocalRing.closedPoint V) ∧
      ∀ a ∈ regAt ξ' p', ∃ v : V, algebraMap V Ω' v = a := by
  have hex : ValuativeCriterion.Existence f := by
    have h : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l : Spec (CommRingCat.of V) ⟶ X',
      Spec.map (CommRingCat.ofHom (algebraMap V Ω')) ≫ l = ξ' ∧ l ≫ f = z := by
    obtain ⟨l, hl₁, hl₂⟩ := (hex { R := V, K := Ω', commSq := ⟨w⟩, .. }).exists_lift
    exact ⟨l, hl₁, hl₂⟩
  have hsp : genPt ξ' ⤳ l (IsLocalRing.closedPoint V) := by
    unfold genPt
    rw [← hl₁]
    exact (IsLocalRing.specializes_closedPoint _).map l.continuous
  have key : X'.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo ξ' =
      Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap V Ω') := by
    apply Spec.map_injective
    rw [← cancel_mono (X'.fromSpecStalk (l (IsLocalRing.closedPoint V)))]
    have h1 : Spec.map (X'.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo ξ') ≫
        X'.fromSpecStalk (l (IsLocalRing.closedPoint V)) = ξ' := by
      refine Eq.trans (congrArg (· ≫ X'.fromSpecStalk (l (IsLocalRing.closedPoint V)))
        (Spec.map_comp (X'.presheaf.stalkSpecializes hsp) (Scheme.stalkClosedPointTo ξ'))) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ') ≫ ·)
        (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp)) ?_
      exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ'
    have h2 : Spec.map (Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap V Ω')) ≫
        X'.fromSpecStalk (l (IsLocalRing.closedPoint V)) = ξ' := by
      rw [Spec.map_comp, Category.assoc]
      refine Eq.trans (congrArg (Spec.map (CommRingCat.ofHom (algebraMap V Ω')) ≫ ·)
        (Scheme.Spec_stalkClosedPointTo_fromSpecStalk l)) hl₁
    exact h1.trans h2.symm
  refine ⟨⟨_, hsp⟩, ?_, ?_⟩
  · rw [← hl₂]
    exact (Scheme.Hom.comp_apply l f _).symm
  · rintro _ ⟨g, rfl⟩
    exact ⟨(Scheme.stalkClosedPointTo l).hom g, (congrArg (fun t => t.hom g) key).symm⟩

theorem spec_genMap {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) :
    Spec.map (X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk q.1 = ξ := by
  refine Eq.trans (congrArg (· ≫ X.fromSpecStalk q.1)
    (Spec.map_comp (X.presheaf.stalkSpecializes q.2) (Scheme.stalkClosedPointTo ξ))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·)
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk q.2)) ?_
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ

theorem exists_over {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    [IsLocallyNoetherian X] {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
    {f : X' ⟶ X} {i : Ω →+* Ω'} [IsProper f] (hD : Dominates ξ' ξ f i) (hi : Function.Bijective i)
    (hg : IsCptGen ξ) (hn : NormalCpt ξ) (q : Cpt ξ) (hd : ringKrullDim (X.presheaf.stalk q.1) = 1) :
    ∃ p' : Cpt ξ', f p'.1 = q.1 ∧ ∀ a : Ω, i a ∈ regAt ξ' p' → a ∈ regAt ξ q := by
  obtain ⟨hfr, -, -⟩ := RegAtRing.regAt_ring X Ω ξ hg q
  have : IsFractionRing (regAt ξ q) Ω := hfr
  have : IsIntegrallyClosed (regAt ξ q) := by
    rw [isIntegrallyClosed_iff Ω]
    intro x hx
    exact ⟨⟨x, hn q x hx⟩, rfl⟩
  have hdom : IsDomain (X.presheaf.stalk q.1) := (hg.inj q).isDomain (genMap ξ q)
  have : IsIntegrallyClosed (X.presheaf.stalk q.1) :=
    IsIntegrallyClosed.of_equiv (RegAtRing.stalkEquiv hg q).symm
  have : IsDiscreteValuationRing (X.presheaf.stalk q.1) := normal_noeth_local_dim_one_isDVR _ hd
  let _ : Algebra (X.presheaf.stalk q.1) Ω' := (i.comp (genMap ξ q)).toAlgebra
  have : FaithfulSMul (X.presheaf.stalk q.1) Ω' :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (hi.1.comp (hg.inj q))
  have hfr' : IsFractionRing (X.presheaf.stalk q.1) Ω' := by
    refine IsFractionRing.of_field _ _ fun z => ?_
    obtain ⟨y, rfl⟩ := hi.2 z
    obtain ⟨⟨_, a, rfl⟩, ⟨_, b, rfl⟩, rfl⟩ := RegAtRing.exists_div hg q y
    exact ⟨a, b, map_div₀ i _ _⟩
  have w : ξ' ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk q.1) Ω')) ≫
      X.fromSpecStalk q.1 := by
    have e : CommRingCat.ofHom (algebraMap (X.presheaf.stalk q.1) Ω') =
        (X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ) ≫ CommRingCat.ofHom i := rfl
    refine hD.trans ?_
    refine Eq.trans (congrArg (Spec.map (CommRingCat.ofHom i) ≫ ·) (spec_genMap ξ q).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact congrArg (· ≫ X.fromSpecStalk q.1) (Spec.map_comp _ _).symm
  have hv : ValuationRing (X.presheaf.stalk q.1) := inferInstance
  obtain ⟨p', h1, h2⟩ := @exists_lift X X' Ω' _ ξ' f _ (X.presheaf.stalk q.1) _ hdom hv _ hfr'
    (X.fromSpecStalk q.1) w
  refine ⟨p', h1.trans Scheme.fromSpecStalk_closedPoint, fun a ha => ?_⟩
  obtain ⟨v, hv⟩ := h2 _ ha
  exact ⟨v, hi.1 hv⟩

end PositivityTheory.Xgn.LineLatticePushdown

theorem PositivityTheory.Xgn.line_lattice_proper_pushdown : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') [IsProper f], Dominates ξ' ξ f i → Function.Bijective i → IsCptGen ξ → NormalCpt ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (p : Cpt ξ) (t : Ω), L.IsVBOn T 1 ⊤ → (∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T) → (∀ p' : Cpt ξ', f p'.1 ⤳ p.1 → (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' (i t)) → L.IsGenAt p t := by
  intro X Ω _ ξ _ X' Ω' _ ξ' f i _ hD hi hg hn L T p t hL hT hp
  have ht : t ≠ 0 := by
    have h0 := (hp ⟨genPt ξ', specializes_rfl⟩ (by
      show f (genPt ξ') ⤳ p.1
      rw [hD.map_genPt]; exact p.2)).1
    rintro rfl
    exact h0 (map_zero i)
  refine PositivityTheory.Xgn.line_lattice_generator_codim_one X Ω ξ hg hn L T p t hL hT ht fun q hqp hd => ?_
  obtain ⟨p', hq, hreg⟩ := PositivityTheory.Xgn.LineLatticePushdown.exists_over hD hi hg hn q hd
  obtain ⟨q, hq0⟩ := q
  obtain rfl : f p'.1 = q := hq
  obtain ⟨U, hU, b, -, h⟩ := hL _ (hT _ hqp)
  obtain ⟨h1, h2⟩ := h _ (hT _ hqp) hU
  have hr : Set.range b = {b 0} := by
    ext x
    simp [Fin.exists_fin_one, eq_comm]
  rw [hr] at h2
  have he : b 0 ≠ 0 := h1.ne_zero 0
  obtain ⟨_, -, hpull⟩ := pull_reg_and_gen X Ω ξ X' Ω' ξ' f i hD p'
  have g1 := hpull L (b 0) ⟨he, h2⟩
  have g2 := hp p' hqp
  obtain ⟨u, hu, e⟩ := ZUnit.exists_of_span_eq g2.1 (g2.2.symm.trans g1.2)
  have hu' : u = i (t / b 0) := by
    rw [map_div₀, e, smul_eq_mul, mul_div_cancel_right₀ _ g1.1]
  subst hu'
  have hu2 : unitAt ξ ⟨f p'.1, hq0⟩ (t / b 0) :=
    ⟨div_ne_zero ht he, hreg _ hu.2.1, hreg _ (by rw [map_inv₀]; exact hu.2.2)⟩
  refine ⟨ht, h2.trans (span_singleton_eq_of_unitAt hu2 ?_).symm⟩
  rw [smul_eq_mul, div_mul_cancel₀ _ he]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleNormalProperPullback
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem lat_isGenAt_of_proper_birational : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') [IsProper f], Dominates ξ' ξ f i → Function.Bijective i → IsCptGen ξ → NormalCpt ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (p : Cpt ξ) (t : Ω), L.IsVBOn T 1 ⊤ → (∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T) → (∀ p' : Cpt ξ', f p'.1 ⤳ p.1 → (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' (i t)) → L.IsGenAt p t :=
  @PositivityTheory.Xgn.line_lattice_proper_pushdown

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleNormalProperPullbackStatement
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_normal_proper_pullback : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') [IsProper f], Dominates ξ' ξ f i → Function.Bijective i → IsCptGen ξ → NormalCpt ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (p : Cpt ξ) (t : Ω), L.IsVBOn T 1 ⊤ → (∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T) → (∀ p' : Cpt ξ', f p'.1 ⤳ p.1 → (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' (i t)) → L.IsGenAt p t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.lat_isGenAt_of_proper_birational | exact GlobalTheory.CompanionTheory.Ar.Flat.lat_isGenAt_of_proper_birational | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.lat_isGenAt_of_proper_birational <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistOkAll
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwOk
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwMb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

private theorem fix_rt_lemma {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (g : HostAut H) : g.s H.rt = H.rt := by
  apply RingOfIntegers.ext
  rw [HostAut.s, RingOfIntegers.mapRingEquiv_apply]
  exact g.fix

private theorem fix_gen_lemma_2 {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (g : HostAut H) : g.s H.w0 = H.w0 ∧ g.s (H.bar H.w0) = H.bar H.w0 := by
  have hr := fix_rt_lemma g
  have hbr : g.s (H.bar H.rt) = H.bar H.rt := by
    have hsq : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by
      rw [← map_pow, H.rt_sq, map_neg, map_natCast]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · rw [h, hr]
    · rw [h, map_neg, hr]
  have two_ne : (2 : 𝓞 E) ≠ 0 := two_ne_zero
  constructor
  · apply mul_left_cancel₀ two_ne
    have h := congrArg g.s H.two_weight_eq_one_add_root
    rw [map_mul, map_ofNat, map_add (f := _), map_one, hr] at h
    rw [h, H.two_weight_eq_one_add_root]
  · apply mul_left_cancel₀ two_ne
    have h := congrArg (fun x => g.s (H.bar x)) H.two_weight_eq_one_add_root
    simp only [map_mul, map_ofNat, map_add (f := _), map_one] at h
    rw [h, hbr]
    have h2 := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_ofNat, map_add (f := _), map_one] at h2
    exact h2.symm

private theorem fix_adj_lemma_3 {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (g : HostAut H) (a : 𝓞 E) (ha : a ∈ Algebra.adjoin ℤ ({H.w0} : Set (𝓞 E))) : g.s a = a ∧ g.s (H.bar a) = H.bar a := by
  obtain ⟨h1, h2⟩ := fix_gen_lemma_2 g
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx]
    exact ⟨h1, h2⟩
  | algebraMap r =>
    simp
  | add x y _ _ hx hy =>
    simp only [map_add (f := _), hx.1, hy.1, hx.2, hy.2]
    exact ⟨trivial, trivial⟩
  | mul x y _ _ hx hy =>
    simp only [map_mul, hx.1, hy.1, hx.2, hy.2]
    exact ⟨trivial, trivial⟩

theorem tw_mb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (g : HostAut H), l.Mb.map (g.s : 𝓞 E →+* 𝓞 E) = l.Mb ∧ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)).map (g.s : 𝓞 E →+* 𝓞 E) = l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  intro E _ _ _ H l g
  set S : Set (𝓞 E) := {a : 𝓞 E | a ∈ l.Mb ∧ a ∈ Algebra.adjoin ℤ ({H.w0} : Set (𝓞 E))} with hSdef
  have hS : l.Mb = Ideal.span S := l.fromK
  constructor
  · rw [hS, Ideal.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [RingEquiv.coe_toRingHom]
      rw [(fix_adj_lemma_3 g y hy.2).1]
      exact hy
    · intro hx
      exact ⟨x, hx, by simp only [RingEquiv.coe_toRingHom]; exact (fix_adj_lemma_3 g x hx.2).1⟩
  · rw [hS, Ideal.map_span, Ideal.map_span, Set.image_image]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      simp only [RingEquiv.coe_toRingHom]
      exact ((fix_adj_lemma_3 g y hy.2).2).symm
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      simp only [RingEquiv.coe_toRingHom]
      exact (fix_adj_lemma_3 g y hy.2).2

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwTate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem tw_tate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H) (a : TwIso D g) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (I : TateIso D k Q act e), ∃ J : TateIso D k Q (fun c y => act (g.s c) y) e, J.ζ = I.ζ ∧ ∀ n x, J.ev n x = I.ev n (a.a n x) := by
  intro E _ _ _ H D g a k _ Q _ act e I
  have ev_nsmul : ∀ (n : ℕ), 0 < n → ∀ y : D.La, I.ev n (n • y) = 1 := fun n hn y =>
    (I.ker n hn (n • y)).mpr ⟨y, rfl⟩
  have ev_split : ∀ (n : ℕ), 0 < n → ∀ (c : D.La) (f : TwMod g.s D.La),
      I.ev n (((a.a n c + n • f : TwMod g.s D.La)) : D.La) = I.ev n (a.a n c) := by
    intro n hn c f
    have h1 : I.ev n (((a.a n c + n • f : TwMod g.s D.La)) : D.La) = I.ev n (a.a n c) * I.ev n (n • (f : D.La)) :=
      I.add n _ _
    have h0 : I.ev n (n • (f : D.La)) = 1 := ev_nsmul n hn f
    exact h1.trans ((congrArg (fun q => I.ev n (a.a n c) * q) h0).trans (_root_.mul_one _))
  refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow,
            ev := fun n x => I.ev n (a.a n x),
            add := ?_, lin := ?_, ker := ?_, onto := ?_, tower := ?_, isom := ?_ }, rfl, fun _ _ => rfl⟩
  · intro n x y
    rw [map_add (f := _)]
    exact I.add n _ _
  · intro n c x
    rw [map_smul]
    exact I.lin n (g.s c) (a.a n x)
  · intro n hn x
    exact (I.ker n hn (a.a n x)).trans (a.inj n hn x)
  · intro n hn x
    refine (I.onto n hn x).trans ⟨?_, ?_⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨c, f, hb⟩ := a.surj n hn b
      refine ⟨c, ?_⟩
      have h3 : I.ev n b = I.ev n (((a.a n c + n • f : TwMod g.s D.La)) : D.La) := by
        rw [hb]
      exact (ev_split n hn c f).symm.trans h3.symm
    · rintro ⟨c, rfl⟩
      exact ⟨_, rfl⟩
  · intro n m hn hm x
    obtain ⟨f, hf⟩ := a.compat n m hn hm x
    have h4 : I.ev (n * m) (a.a (n * m) x) ^ m = I.ev n (a.a (n * m) x) := I.tower n m hn hm _
    have h5 : I.ev n (a.a (n * m) x) = I.ev n (((a.a n x + n • f : TwMod g.s D.La)) : D.La) := by
      rw [hf]
    exact h4.trans (h5.trans (ev_split n hn x f))
  · intro n hn x y
    have h := I.isom n hn (a.a n x) (a.a n y)
    obtain ⟨t, ht⟩ := a.isom n hn x y
    have hpow : I.ζ n ^ n = 1 := (I.ζ_prim n hn).pow_eq_one
    have heq : I.ζ n ^ (D.EF (a.a n x : D.La)) (a.a n y : D.La) = I.ζ n ^ (D.EF x) y := by
      have h2 : (D.EF (a.a n x : D.La)) (a.a n y : D.La) = (D.EF x) y + (n : ℤ) * t := by
        have : (twForm D g ((a.a n) x)) ((a.a n) y) = (D.EF (a.a n x : D.La)) (a.a n y : D.La) := rfl
        rw [← this]
        linarith
      rw [h2, zpow_add, zpow_mul, zpow_natCast, hpow, one_zpow, _root_.mul_one]
    show e n (I.ev n (a.a n x)) (I.ev n (a.a n y)) (I.ζ n ^ (D.EF x) y)
    rw [← heq]
    exact h

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwSub
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem tw_sub : ∀ (O : Type) [CommRing O] (s : O ≃+* O) (L : Type) [AddCommGroup L] [Module O L] (f : L →ₗ[O] TwMod s L) (I : Ideal O), I.map (s : O →+* O) ≤ I → ∀ x ∈ I • (⊤ : Submodule O L), (show L from f x) ∈ I • (⊤ : Submodule O L) := by
  intro O _ s L _ _ f I hI x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y _
    have hsa : s a ∈ I := hI (Ideal.mem_map_of_mem (s : O →+* O) ha)
    have key : (show L from f (a • y)) = s a • (show L from f y) := f.map_smul a y
    rw [key]
    exact Submodule.smul_mem_smul hsa Submodule.mem_top
  · intro y z hy hz
    have key : (show L from f (y + z)) = (show L from f y) + (show L from f z) := f.map_add y z
    rw [key]
    exact Submodule.add_mem _ hy hz

end PositivityTheory.UnitarySelfGeneration
end

section -- restored from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwLiemult
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

private theorem isLieEigen_twistAct_iff {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct O G) (s : O ≃+* O) {k : Type} [Field k] (t : Sp k ⟶ S) (τ : O →+* k) (v : epsPt t ⟶ G) :
    IsLieEigen (twistAct act s) t (τ.comp s.toRingHom) v ↔ IsLieEigen act t τ v := by
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun a => ?_⟩
    have := h1 (s.symm a)
    simpa [twistAct] using this
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun a => ?_⟩
    simpa [twistAct] using h1 (s a)

theorem tw_liemult : ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (G : Over S) [GrpObj G] (act : OAct O G) (s : O ≃+* O) (k : Type) [Field k] (t : Sp k ⟶ S) (τ : O →+* k) (n : ℕ), LieMult (twistAct act s) t (τ.comp s.toRingHom) n ↔ LieMult act t τ n := by
  intro O _ S G _ act s k _ t τ n
  simp only [LieMult, isLieEigen_twistAct_iff]

end PositivityTheory.UnitarySelfGeneration
end

section -- restored from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwDet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem tw_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H) (S : Scheme.{0}) (G : Over S) [GrpObj G] (act : OAct (𝓞 E) G) (k : Type) [Field k] (t : Sp k ⟶ S) (ρ : k), DetCond D act t ρ → DetCond D (twistAct act g.s) t ρ := by
  intro E _ _ _ H D g S G _ act k _ t ρ h τ
  have e : τ = (τ.comp g.s.symm.toRingHom).comp g.s.toRingHom := by
    ext a
    simp
  have e2 : (τ.comp g.s.symm.toRingHom) H.rt = τ H.rt := by
    show τ (g.s.symm H.rt) = τ H.rt
    rw [(RingEquiv.symm_apply_eq _).2 g.s_rt.symm]
  have := h (τ.comp g.s.symm.toRingHom)
  rw [e2] at this
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · rw [e, tw_liemult]
    exact this.1 h1
  · rw [e, tw_liemult]
    exact this.2 h1

end PositivityTheory.UnitarySelfGeneration
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem tw_ok : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (g : HostAut H) (a : TwIso D g), TwOK o g a := by
  intro E _ _ _ H D l B _ b S s o g a
  obtain ⟨hm1, hm2⟩ := tw_mb E H l g
  refine ⟨fun x hx => o.eta_ker _ (tw_sub _ g.s D.La (a.a l.M) l.Mb hm1.le x hx), fun k _ _ x β hx => ?_⟩
  obtain ⟨hd, I, h1, h2, h3⟩ := o.geom k x β hx
  obtain ⟨J, hJ1, hJ2⟩ := tw_tate E H D g a k _ _ _ I
  refine ⟨tw_det E H D g S _ _ k x _ hd, J, by rw [hJ1]; exact h1, fun y => ?_, fun y hy => ?_⟩
  · rw [hJ2]
    exact h2 _
  · rw [hJ2]
    exact h3 _ (tw_sub _ g.s D.La (a.a l.M) _ hm2.le y hy)

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistOkAll
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TwistOk

theorem twOK_obj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (g : HostAut H) (a : TwIso D g), TwOK o g a :=
  @PositivityTheory.UnitarySelfGeneration.tw_ok

end GlobalTheory.CompanionTheory.Ar.TwistOk
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistOkAllStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_ok_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (g : HostAut H) (a : TwIso D g), TwOK o g a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwistOk.twOK_obj | exact GlobalTheory.CompanionTheory.Ar.TwistOk.twOK_obj | (intros; apply GlobalTheory.CompanionTheory.Ar.TwistOk.twOK_obj <;> assumption)
end
end

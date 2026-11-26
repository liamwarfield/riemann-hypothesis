module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLieBc

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.LieValAtBase
set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ci

theorem exists_base {S : Scheme.{0}} {G : Over S} [GrpObj G] {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R)
    (x : Spec (CommRingCat.of A) ⟶ S) (z : Spec (CommRingCat.of R) ⟶ S)
    (hz : Spec.map (CommRingCat.ofHom φ) ≫ x = z) {E F : Type} [AddCommGroup E] [Module A E] [AddCommGroup F]
    [Module R F] (M : LieModel G x E) (N : LieModel G z F) :
    ∃ j : E →+ F, (∀ e, N.pt (j e) = LieTangent.epsBase φ hz ≫ M.pt e) ∧
      (∀ (a : A) e, j (a • e) = φ a • j e) ∧
      (Smooth G.hom → ∀ (n : ℕ) (b : Module.Basis (Fin n) A E),
        ∃ b' : Module.Basis (Fin n) R F, ∀ k, b' k = j (b k)) := by
  subst hz
  letI := φ.toAlgebra
  obtain ⟨j, h1, h2, h3⟩ := PositivityTheory.HtPt.Htat.lie_bc S G A R x E F M N
  refine ⟨j, fun e => Over.OverMorphism.ext (h1 e), h2, fun hs n b => ?_⟩
  exact ⟨Module.Basis.mk (h3 hs n b).1 (h3 hs n b).2.ge, fun k => Module.Basis.mk_apply _ _ _⟩

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
  {V : Type} [AddCommGroup V] [Module Ω V]

theorem lieValAt_base (hξ : IsCptGen ξ) {M : LieModel G ξ V} {R R' : Type} [CommRing R] [IsLocalRing R]
    [CommRing R'] [IsLocalRing R'] (φ : R →+* R') {x : Spec (CommRingCat.of R) ⟶ X}
    {z : Spec (CommRingCat.of R') ⟶ X} (hz : Spec.map (CommRingCat.ofHom φ) ≫ x = z) {e : V} {w : epsAt x ⟶ G}
    (h : M.ValAt x e w) : M.ValAt z e (LieTangent.epsBase φ hz ≫ w) := by
  subst hz
  rw [LieModel.valAt_iff] at h ⊢
  obtain ⟨hc, v, hv, rfl⟩ := h
  have hsp := LieTangent.centre_specializes φ x
  have hc' := LieTangent.specializes_of_injective (hξ.inj ⟨_, hc⟩) hsp
  have F1 : Spec.map (CommRingCat.ofHom (X.presheaf.stalkSpecializes hsp).hom) ≫ X.fromSpecStalk (centre x) =
      X.fromSpecStalk (centre (Spec.map (CommRingCat.ofHom φ) ≫ x)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hd : ∀ {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D),
      (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
    intro A B D _ _ _ f g
    refine RingHom.ext fun a => ?_
    ext <;> simp
  rw [LieModel.extends_iff] at hv
  refine ⟨hc', LieTangent.epsBase (X.presheaf.stalkSpecializes hsp).hom F1 ≫ v,
    (M.extends_iff _ _ _).2 ⟨LieTangent.isTanAt_base _ _ hv.1, ?_⟩, ?_⟩
  · rw [hv.2, ← Category.assoc]
    congr 1
    refine Over.OverMorphism.ext ?_
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [LieTangent.spec_comp, hd]
    congr 3
    exact RingHom.ext fun s => (LieTangent.genMap_specializes ⟨_, hc⟩ hc' hsp s).symm
  · rw [← Category.assoc, ← Category.assoc]
    congr 1
    refine Over.OverMorphism.ext ?_
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [LieTangent.spec_comp, hd, LieTangent.spec_comp, hd]
    congr 3
    exact (congrArg CommRingCat.Hom.hom (LieTangent.stalk_base φ x)).symm

theorem frame_basis [IsCommMonObj G] (hξ : IsCptGen ξ) (hs : Smooth G.hom) (M : LieModel G ξ V) {R : Type}
    [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) {ER : Type}
    [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER) {n : ℕ} {b : Fin n → V}
    (hb : M.lat.IsFrameAt b ⟨centre z, h⟩) :
    ∃ bz : Module.Basis (Fin n) R ER, ∀ q, M.ValAt z (b q) (MR.pt (bz q)) := by
  obtain ⟨EA, _, _, ⟨MA⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z))
  obtain ⟨j, hj, -, hjb⟩ := exists_base (A := X.presheaf.stalk (centre z)) (Scheme.stalkClosedPointTo z).hom _ z
    (LieTangent.spec_centre z) MA MR
  obtain ⟨i, hi, his, -⟩ := exists_base (genMap ξ ⟨centre z, h⟩) _ ξ
    (LieTangent.spec_genMap ξ ⟨centre z, h⟩) MA M
  have hext : ∀ a, M.Extends ⟨centre z, h⟩ (i a) (MA.pt a) := fun a =>
    (M.extends_iff _ _ _).2 ⟨MA.tan a, hi a⟩
  have hinj : ∀ a b, i a = i b → a = b := fun a b hab =>
    MA.inj ((hext a).unique (hξ.inj _) (hab ▸ hext b))
  have hsurj : ∀ e ∈ M.lat ⟨centre z, h⟩, ∃ a, i a = e := by
    intro e he
    obtain ⟨v, hv⟩ := (M.mem_lat_iff _ _).1 he
    obtain ⟨a, rfl⟩ := MA.onto v hv.1
    exact ⟨a, M.inj ((hi a).trans ((M.extends_iff _ _ _).1 hv).2.symm)⟩
  choose a ha using fun q => hsurj (b q) (by rw [hb.2]; exact Submodule.subset_span ⟨q, rfl⟩)
  have hsum : ∀ c : Fin n → X.presheaf.stalk (centre z),
      i (∑ q, c q • a q) = ∑ q, genMap ξ ⟨centre z, h⟩ (c q) • b q := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [his, ha]
  have li : LinearIndependent (X.presheaf.stalk (centre z)) a := by
    rw [Fintype.linearIndependent_iff]
    intro c hc q
    have h1 := hsum c
    rw [hc, map_zero] at h1
    exact hξ.inj ⟨_, h⟩ ((Fintype.linearIndependent_iff.1 hb.1 _ h1.symm q).trans (map_zero _).symm)
  have sp : ⊤ ≤ Submodule.span (X.presheaf.stalk (centre z)) (Set.range a) := by
    intro e _
    have h1 : i e ∈ M.lat ⟨centre z, h⟩ := (M.mem_lat_iff _ _).2 ⟨_, hext e⟩
    rw [hb.2, Submodule.mem_span_range_iff_exists_fun] at h1
    obtain ⟨c, hc⟩ := h1
    choose s hs using fun q => (c q).2
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨s, hinj _ _ ?_⟩
    rw [hsum, ← hc]
    exact Finset.sum_congr rfl fun q _ => by rw [hs]; rfl
  obtain ⟨bz, hbz⟩ := hjb hs n (Module.Basis.mk li sp)
  refine ⟨bz, fun q => (M.valAt_iff _ _ _).2 ⟨h, MA.pt (a q), ha q ▸ hext (a q), ?_⟩⟩
  rw [hbz, hj, Module.Basis.mk_apply]

theorem frame_lat [IsCommMonObj G] (hξ : IsCptGen ξ) (hs : Smooth G.hom) (M : LieModel G ξ V) {K : Type} [Field K]
    {C : ACurve K} {z : Spec (CommRingCat.of K) ⟶ X} (Y : CurveIn C z) {Vz : Type} [AddCommGroup Vz] [Module K Vz]
    (Mz : LieModel G z Vz) {n : ℕ} {b : Fin n → V} (i : C.I) (h : genPt ξ ⤳ centre (Y.x i))
    (hb : M.lat.IsFrameAt b ⟨centre (Y.x i), h⟩) :
    ∃ bz : Module.Basis (Fin n) K Vz, (∀ q, M.ValAt z (b q) (Mz.pt (bz q))) ∧ IsLatOf C i bz (Y.lieLat Mz i) := by
  obtain ⟨ER, _, _, ⟨MR⟩⟩ := lieModel_exists X G _ (Y.x i)
  obtain ⟨bR, hbR⟩ := frame_basis hξ hs M (Y.x i) h MR hb
  obtain ⟨j, hj, hjs, hjb⟩ := exists_base (C.v i).valuationSubring.subtype _ z (Y.gen i) MR Mz
  obtain ⟨bz, hbz⟩ := hjb hs n bR
  refine ⟨bz, fun q => ?_, fun x => ?_⟩
  · rw [hbz, hj]
    exact lieValAt_base hξ _ _ (hbR q)
  · have hr : Y.lieLat Mz i = j.range := by
      refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) ?_
      · rintro e ⟨v, hv, he⟩
        obtain ⟨u, rfl⟩ := MR.onto v hv
        exact ⟨u, Mz.inj ((hj u).trans (Over.OverMorphism.ext he.symm))⟩
      · rintro _ ⟨u, rfl⟩
        exact AddSubgroup.subset_closure ⟨MR.pt u, MR.tan u, congrArg (fun q => q.left) (hj u)⟩
    have hsum : ∀ c : Fin n → (C.v i).valuationSubring, j (∑ q, c q • bR q) = ∑ q, (c q : K) • bz q := by
      intro c
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun q _ => by rw [hjs, hbz]; rfl
    rw [hr]
    constructor
    · rintro ⟨u, rfl⟩ q
      rw [← bR.sum_repr u, hsum, bz.repr_sum_self]
      exact (bR.repr u q).2
    · intro hx
      exact ⟨∑ q, (⟨bz.repr x q, hx q⟩ : (C.v i).valuationSubring) • bR q, by rw [hsum]; exact bz.sum_repr x⟩

end PositivityTheory.HtPt.Ci
end
end

set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ci

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
  {V : Type} [AddCommGroup V] [Module Ω V]

theorem span_values [IsCommMonObj G] (hξ : IsCptGen ξ) (hs : Smooth G.hom) (M : LieModel G ξ V) {R : Type}
    [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) {ER : Type}
    [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER) :
    Submodule.span R {v | ∃ e, M.ValAt z e (MR.pt v)} = ⊤ := by
  have exists_base {S : Scheme.{0}} {G : Over S} [GrpObj G] {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R)
      (x : Spec (CommRingCat.of A) ⟶ S) (z : Spec (CommRingCat.of R) ⟶ S)
      (hz : Spec.map (CommRingCat.ofHom φ) ≫ x = z) {E F : Type} [AddCommGroup E] [Module A E] [AddCommGroup F]
      [Module R F] (M : LieModel G x E) (N : LieModel G z F) :
      ∃ j : E →+ F, (∀ e, (N.pt (j e)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap φ)) ≫ (M.pt e).left) ∧
        (∀ (a : A) e, j (a • e) = φ a • j e) ∧
        (Smooth G.hom → ∀ (n : ℕ) (b : Module.Basis (Fin n) A E),
          ∃ b' : Module.Basis (Fin n) R F, ∀ k, b' k = j (b k)) := by
    subst hz
    letI := φ.toAlgebra
    obtain ⟨j, h1, h2, h3⟩ := PositivityTheory.HtPt.Htat.lie_bc S G A R x E F M N
    refine ⟨j, h1, h2, fun hs n b => ?_⟩
    exact ⟨Module.Basis.mk (h3 hs n b).1 (h3 hs n b).2.ge, fun k => Module.Basis.mk_apply _ _ _⟩
  obtain ⟨EA, _, _, ⟨MA⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z))
  obtain ⟨j, hj, -, hjb⟩ := exists_base (A := X.presheaf.stalk (centre z)) (Scheme.stalkClosedPointTo z).hom _ z
    (LieTangent.spec_centre z) MA MR
  obtain ⟨i, hi, -, -⟩ := exists_base (genMap ξ ⟨centre z, h⟩) _ ξ
    (LieTangent.spec_genMap ξ ⟨centre z, h⟩) MA M
  obtain ⟨hf, hp⟩ := PositivityTheory.HtPt.Htat.lie_fin X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) EA MA
  have : Module.Free (X.presheaf.stalk (centre z)) EA := Module.free_of_flat_of_isLocalRing
  obtain ⟨bz, hbz⟩ := hjb hs _ (Module.finBasis _ EA)
  refine top_le_iff.1 (bz.span_eq.symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨k, rfl⟩
  refine ⟨i (Module.finBasis _ EA k), h, MA.pt (Module.finBasis _ EA k), ⟨MA.tan _, ?_⟩, ?_⟩
  · exact hi _
  · rw [hbz, hj]

theorem lieValAt_end {M : LieModel G ξ V} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} {f : G ⟶ G} [IsMonHom f] {A : V →ₗ[Ω] V} (hA : M.IsDiffOf f A) {e : V}
    {w : epsAt z ⟶ G} (h : M.ValAt z e w) : M.ValAt z (A e) (w ≫ f) := by
  obtain ⟨hc, v, hv, hw⟩ := h
  refine ⟨hc, v ≫ f, ⟨?_, ?_⟩, ?_⟩
  · rw [LieTangent.isTanAt_iff, ← Category.assoc, (LieTangent.isTanAt_iff _).1 hv.1, MonObj.one_comp]
  · change (M.pt (A e)).left = _
    rw [hA e]
    change (M.pt e).left ≫ f.left = _ ≫ (v.left ≫ f.left)
    rw [hv.2, Category.assoc]
  · change w.left ≫ f.left = _
    change w.left ≫ f.left = _ ≫ (v.left ≫ f.left)
    rw [hw, Category.assoc]

theorem lieValAt_smul {M : LieModel G ξ V} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} {ER : Type} [AddCommGroup ER] [Module R ER] {MR : LieModel G z ER} {e : V}
    {v : ER} (h : M.ValAt z e (MR.pt v)) {a : Ω} {r : R} (ha : ValAt ξ z a r) :
    M.ValAt z (a • e) (MR.pt (r • v)) := by
  obtain ⟨h1, s, rfl, rfl⟩ := ha
  rw [MR.pt_smul]
  exact h.smul h1 s

def emptyCurve (K : Type) [Field K] : ACurve K where
  I := Empty
  v := fun i => i.elim
  w := fun i => i.elim
  fin := fun _ _ => Set.toFinite _
  prod := fun _ _ => finsum_of_isEmpty _

theorem eig_val : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (k K : Type) [Field k] [Field K] [Algebra k K] (z : Spec (CommRingCat.of K) ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (O S : Type) [CommRing O] [Fintype S] (act : O → (G ⟶ G)) (r : O →+* Module.End Ω V) (rz : O →+* Module.End K Vz) (σ : S → (O →+* Ω)) (χ : S → (O →+* k)), IsCptGen ξ → Smooth G.hom → (∀ a, IsMonHom (act a)) → M.IsActOf act r → Mz.IsActOf act rz → IsSplit χ → (∀ s a, ValAt ξ z (σ s a) (algebraMap k K (χ s a))) → M.lat ⟨centre z, h₀⟩ = ⨆ s, M.eigLat r (σ s) ⟨centre z, h₀⟩ → ∀ s, Submodule.span K {v | ∃ e ∈ M.eigLat r (σ s) ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} = eigSp rz ((algebraMap k K).comp (χ s)) := by
  intro X Ω _ ξ k K _ _ _ z G _ _ V _ _ M Vz _ _ Mz h₀ O S _ _ act r rz σ χ hξ hs hm hr hrz hχ hσ hlat s
  classical
  have : Module.Finite K Vz := (PositivityTheory.HtPt.Htat.lie_fin X G K z Vz Mz).1
  obtain ⟨e, -, -, he3, -, he5⟩ := GlobalTheory.T.eigen_projectors_split_action K (emptyCurve K) Vz (fun i => i.elim) O k S χ hχ (fun i => i.elim) rz
    ⟨fun i => i.elim, Module.finBasis K Vz, Set.toFinite (α := Empty) _⟩ (fun a i => i.elim)
  obtain ⟨m, c, a, hc, hes⟩ := he5 s
  let U : S → Submodule K Vz := fun s =>
    Submodule.span K {v | ∃ e ∈ M.eigLat r (σ s) ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)}
  have hU : ∀ t, U t ≤ eig (fun a => rz a) (fun a => algebraMap k K (χ t a)) := by
    intro t
    refine Submodule.span_le.2 ?_
    rintro v ⟨x, hx, hv⟩
    refine mem_eig.2 fun b => Mz.inj ?_
    have := hm b
    have h1 := lieValAt_end (hr b) hv
    have h2 := lieValAt_smul hv (hσ t b)
    have h3 : r b x = σ t b • x := (mem_eig (ρ := fun a => r a) (χ := fun a => σ t a)).1 hx.2 b
    rw [h3] at h1
    exact (hrz b v).trans (h1.unique hξ h2)
  have htop : ⨆ t, U t = ⊤ := by
    refine top_le_iff.1 ((span_values hξ hs M z h₀ Mz).symm.le.trans (Submodule.span_le.2 ?_))
    rintro v ⟨x, hx⟩
    obtain ⟨_, hxl⟩ := (M.exists_valAt_iff z x).1 ⟨_, hx⟩
    have key : ∀ x ∈ ⨆ s, M.eigLat r (σ s) ⟨centre z, h₀⟩, ∃ v ∈ ⨆ t, U t, M.ValAt z x (Mz.pt v) := by
      intro x hx
      induction hx using Submodule.iSup_induction' with
      | mem t x hx =>
        obtain ⟨w, hw⟩ := (M.exists_valAt_iff z x).2 ⟨h₀, hx.1⟩
        obtain ⟨v, rfl⟩ := Mz.onto w hw.isTanAt
        exact ⟨v, Submodule.mem_iSup_of_mem t (Submodule.subset_span ⟨x, hx, hw⟩), hw⟩
      | zero => exact ⟨0, zero_mem _, by rw [Mz.pt_zero]; exact M.valAt_zero h₀⟩
      | add x y _ _ hx hy =>
        obtain ⟨v, hv, hv'⟩ := hx
        obtain ⟨w, hw, hw'⟩ := hy
        exact ⟨v + w, add_mem hv hw, by rw [Mz.add]; exact hv'.add hw'⟩
    obtain ⟨v', hv', hv''⟩ := key x (hlat ▸ hxl)
    rw [Mz.inj (hx.unique hξ hv'')]
    exact hv'
  refine le_antisymm (hU s) fun v hv => ?_
  have key : ∀ v ∈ ⨆ t, U t, e s v ∈ U s := by
    intro v hv
    induction hv using Submodule.iSup_induction' with
    | mem t x hx =>
      have h1 : e s x = algebraMap k K (if t = s then 1 else 0) • x := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← hc t, hes, LinearMap.sum_apply, map_sum, Finset.sum_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [LinearMap.smul_apply, mem_eig.1 (hU t hx) (a j), map_mul, mul_smul]
      rw [h1]
      split_ifs with h
      · subst h; exact Submodule.smul_mem _ _ hx
      · simp
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  have := key v (htop ▸ Submodule.mem_top)
  rwa [he3 s v hv] at this

end PositivityTheory.HtPt.Ci

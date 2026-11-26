module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationTestOfGeometricTest
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalPolarisationVolumeFormSymmetricAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeometricallyConnectedOpenConditionSmoothProject
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoSpecialFibreTestGeometricTest
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoSpecialFibreTestGeometricTest
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory

theorem ZJ.Core.Test.exists_fibre_immersion {C : ZJ.Core} (hF : C.Fib) {p : ℕ} [Fact p.Prime]
    {y : Sp (ZJ.OO p) ⟶ C.Z} (τ : C.Test y) :
    ∃ h : pullback τ.H.hom (ZJ.rPt p ≫ spMap τ.j) ⟶ pullback C.GG.hom (ZJ.rPt p ≫ y),
      h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f ∧ h ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      IsClosedImmersion h ∧ Set.range h = Set.univ := by
  have w : (pullback.fst τ.H.hom (ZJ.rPt p ≫ spMap τ.j) ≫ τ.f) ≫ C.GG.hom =
      pullback.snd τ.H.hom (ZJ.rPt p ≫ spMap τ.j) ≫ ZJ.rPt p ≫ y := by
    rw [Category.assoc, τ.f_over, pullback.condition_assoc, Category.assoc, τ.fac]
  let h := pullback.lift _ _ w
  have h₁ : h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f := pullback.lift_fst _ _ _
  have h₂ : h ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hc := τ.imm h h₁ h₂
  refine ⟨h, h₁, h₂, hc, ?_⟩
  have := (ZJ.kb_isAlgClosed_and_conj p).1
  have := (ZJ.core_basic C).2.1
  let s := pullback.snd C.GG.hom (ZJ.rPt p ≫ y)
  have : JacobsonSpace ↥(pullback C.GG.hom (ZJ.rPt p ≫ y)) := LocallyOfFiniteType.jacobsonSpace s
  rw [← Set.univ_subset_iff, ← closure_closedPoints, h.isClosedEmbedding.isClosed_range.closure_subset_iff]
  intro x hx
  obtain ⟨z, hz, hzx⟩ : ∃ z : Sp (ZJ.kb p) ⟶ pullback C.GG.hom (ZJ.rPt p ≫ y),
      z ≫ pullback.snd _ _ = 𝟙 _ ∧ ∀ q, z q = x :=
    ⟨pointOfClosedPoint s x hx, pointOfClosedPoint_comp s x hx, pointOfClosedPoint_apply s x hx⟩
  obtain ⟨c, hc₁, hc₂⟩ := hF p y τ (z ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, reassoc_of% hz])
  have e : pullback.lift c (𝟙 _) (hc₁.trans (Category.id_comp _).symm) ≫ h = z := by
    apply pullback.hom_ext
    · rw [Category.assoc, h₁, pullback.lift_fst_assoc, hc₂]
    · rw [Category.assoc, h₂, pullback.lift_snd, hz]
  exact ⟨pullback.lift c (𝟙 _) (hc₁.trans (Category.id_comp _).symm) (IsLocalRing.closedPoint (ZJ.kb p)),
    (congrArg (fun g => g (IsLocalRing.closedPoint (ZJ.kb p))) e).trans (hzx _)⟩

theorem ZJ.Core.Test.exists_isGt_special {C : ZJ.Core} {p : ℕ} [Fact p.Prime]
    {y : Sp (ZJ.OO p) ⟶ C.Z} (τ : C.Test y) :
    ∃ E : SplitExt (Sp (ZJ.kb p)), E.IsGt ((Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H) := by
  have := τ.j_loc
  have hr : Set.range (ZJ.rPt p ≫ spMap τ.j) = {IsLocalRing.closedPoint τ.V} := by
    have h : ∀ q, (ZJ.rPt p ≫ spMap τ.j) q = IsLocalRing.closedPoint τ.V := fun q => by
      rw [Subsingleton.elim q (IsLocalRing.closedPoint (ZJ.kb p))]
      exact (congrArg (PrimeSpectrum.comap τ.j)
        (IsLocalRing.comap_closedPoint (IsLocalRing.residue (ZJ.OO p)))).trans (IsLocalRing.comap_closedPoint τ.j)
    exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨IsLocalRing.closedPoint (ZJ.kb p), h _⟩, by
      rintro _ ⟨q, rfl⟩
      exact h q⟩
  obtain ⟨G₁, _, _, E, φ, hE, hφ⟩ := τ.exists_isGt_fibre _ _ hr
  obtain ⟨e, he, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback τ.H _)
  exact ⟨E, isGt_of_iso e hE⟩

theorem ZH.Clos.TMap.eSec_comp_f {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} {Q : Clos ρ M U₀ EE} (ex : Q.Ext) {p : ℕ} [Fact p.Prime]
    {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p} {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u} (tm : Q.TMap t c) :
    (eSec t.u.G ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι : Sp t.u.V ⟶ Q.P.left) = c.yV ≫ ex.e ≫ Q.G.ι := by
  have := Q.proper
  have : IsDominant (Out.jK t.u.V) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    rw [CommRingCat.hom_ofHom, (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective t.u.V _)]
    exact bot_le)⟩
  obtain ⟨e₁, he₁, s₁⟩ : ∃ e₁ : Sp t.u.V ⟶ t.u.G.left, e₁ = eSec t.u.G ∧ e₁ ≫ t.u.G.hom = 𝟙 _ :=
    ⟨_, rfl, Over.w η[t.u.G]⟩
  obtain ⟨e₂, he₂, s₂⟩ : ∃ e₂ : Sp (FractionRing t.u.V) ⟶ pullback t.u.G.hom (jK t.u.V),
      e₂ = eSec ((Over.pullback (jK t.u.V)).obj t.u.G) ∧ e₂ ≫ pullback.snd _ _ = 𝟙 _ :=
    ⟨_, rfl, Over.w η[(Over.pullback (jK t.u.V)).obj t.u.G]⟩
  obtain ⟨e₃, he₃, s₃⟩ : ∃ e₃ : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀,
      e₃ = eSec ((Over.pullback Q.u₀).obj ρ.P.A) ∧ e₃ ≫ pullback.snd _ _ = 𝟙 _ :=
    ⟨_, rfl, Over.w η[(Over.pullback Q.u₀).obj ρ.P.A]⟩
  obtain ⟨e₄, he₄⟩ : ∃ e₄ : Sp S.R ⟶ ρ.P.A.left, e₄ = eSec ρ.P.A := ⟨_, rfl⟩
  have h₂ : e₂ ≫ pullback.fst _ _ = jK t.u.V ≫ e₁ := by
    subst he₁ he₂
    exact ZJ.eSec_comp_of_isGrpPullback (isGrpPullback_pullback t.u.G (jK t.u.V))
  have h₃ : e₃ ≫ pullback.fst _ _ = Q.u₀ ≫ e₄ := by
    subst he₃ he₄
    exact ZJ.eSec_comp_of_isGrpPullback (isGrpPullback_pullback ρ.P.A Q.u₀)
  have h₄ : e₂ ≫ t.u.U.gen.hom.left ≫ t.u.φ = spMap t.u.yK ≫ e₄ := by
    subst he₂ he₄
    have := t.u.U.gen_hom
    exact ZJ.eSec_comp_of_isGrpPullback
      (((isGrpPullback_of_iso t.u.U.gen).comp t.u.cart).congr (Category.id_comp _) rfl)
  have h₅ : U₀.ι ≫ ex.e = e₃ ≫ ex.a := he₃ ▸ ex.e_zero
  have h₆ : e₂ ≫ tm.φ = c.yK ≫ e₃ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, tm.φ_fst, h₃, reassoc_of% c.yK_u]
      exact h₄
    · rw [Category.assoc, Category.assoc, tm.φ_snd, s₃, reassoc_of% s₂, Category.comp_id]
  rw [← he₁]
  refine ext_of_isDominant_of_isSeparated Q.P.hom ?_ (Out.jK t.u.V) ?_
  · simp only [Category.assoc]
    rw [tm.f_over, ex.e_sec, reassoc_of% s₁, Category.comp_id]
  · rw [← reassoc_of% c.yK_fac, reassoc_of% h₅, ex.a_eq, ← reassoc_of% h₆, tm.φ_f, reassoc_of% h₂]

theorem ZH.exists_iso_special_fibre_of_test : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (p : ℕ) [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c) (τ : ex.core.Test y), S.Big → ex.core.Fib → ∃ e : (Over.pullback (GlobalTheory.ZJ.rPt p ≫ spMap τ.j)).obj τ.H ≅ t.mod.Φ.G, IsMonHom e.hom ∧ e.hom.left ≫ t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = pullback.fst _ _ ≫ τ.f ≫ Q.G.ι := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex p _ y y₀ t c tm τ hS hF
  obtain ⟨τ₀, e₀, he₁, he₂⟩ := GlobalTheory.T.exists_uniformisationTest_of_geometricTest hL o Ω S ρ M U₀ EE hB Q ex p y y₀ t c tm hS
  obtain ⟨h, h₁, h₂, hc, hr⟩ := τ.exists_fibre_immersion hF
  obtain ⟨h₀, h₀₁, h₀₂, hc₀, hr₀⟩ := τ₀.exists_fibre_immersion hF
  obtain ⟨E, hE⟩ := τ.exists_isGt_special
  have := (ZJ.kb_isAlgClosed_and_conj p).1
  have : IsCommMonObj ((Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H) := Functor.isCommMonObj_obj
  let Y : Over (Sp (ZJ.kb p)) := Over.mk (pullback.snd ex.core.GG.hom (ZJ.rPt p ≫ y))
  let f : (Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H ⟶ Y := Over.homMk h h₂
  have w : (e₀.inv ≫ h₀) ≫ pullback.snd _ _ = t.mod.Φ.G.hom := by
    rw [Category.assoc, h₀₂, ← he₁, Iso.inv_hom_id_assoc]
  let f' : t.mod.Φ.G ⟶ Y := Over.homMk (e₀.inv ≫ h₀) w
  have k : (e₀.inv ≫ h₀) ≫ pullback.fst _ _ ≫ Q.G.ι = t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι := by
    rw [Category.assoc, Iso.inv_comp_eq, he₂]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Q.G.ι) h₀₁).trans (Category.assoc _ _ _))
  have k' : h ≫ pullback.fst _ _ ≫ Q.G.ι = pullback.fst _ _ ≫ τ.f ≫ Q.G.ι :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Q.G.ι) h₁).trans (Category.assoc _ _ _))
  have hr' : Set.range (e₀.inv ≫ h₀) = Set.univ := by
    rw [Set.range_eq_univ] at hr₀ ⊢
    exact hr₀.comp e₀.inv.surjective
  have hone : η[(Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H] ≫ f = η[t.mod.Φ.G] ≫ f' := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · refine (cancel_mono Q.G.ι).1 ?_
      have u₁ := ZJ.eSec_comp_of_isGrpPullback (isGrpPullback_pullback τ.H (ZJ.rPt p ≫ spMap τ.j))
      have u₂ := ZJ.eSec_comp_of_isGrpPullback t.mod.cart
      have v₁ : eSec ((Over.pullback (ZJ.rPt p ≫ spMap τ.j)).obj τ.H) ≫ pullback.fst _ _ ≫ τ.f ≫ Q.G.ι =
          (ZJ.rPt p ≫ y ≫ ex.e ≫ Q.G.ι : Sp (ZJ.kb p) ⟶ Q.P.left) := by
        refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ τ.f ≫ Q.G.ι) u₁)).trans ?_
        have a := congrArg (fun g => ZJ.rPt p ≫ spMap τ.j ≫ g ≫ Q.G.ι) τ.eSec_comp_f
        exact a.trans (congrArg (fun g => ZJ.rPt p ≫ g ≫ ex.e ≫ Q.G.ι) τ.fac)
      have v₂ : eSec t.mod.Φ.G ≫ t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι =
          (ZJ.rPt p ≫ y ≫ ex.e ≫ Q.G.ι : Sp (ZJ.kb p) ⟶ Q.P.left) := by
        refine ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) u₂)).trans ?_
        have a := congrArg (fun g => ZJ.rPt p ≫ spMap t.u.j ≫ g) (tm.eSec_comp_f ex)
        simp only [Category.assoc] at a ⊢
        rw [reassoc_of% c.fac] at a
        exact a
      rw [← k'] at v₁
      rw [← k] at v₂
      exact v₁.trans v₂.symm
    · exact (Over.w _).trans (Over.w _).symm
  obtain ⟨e, he, hef⟩ := exists_iso_isMonHom_of_isGt_of_range_eq (ZJ.kb p) Y E t.mod.Φ.E _ _ f f' hE ⟨t.mod.Φ.D⟩ hc
    (inferInstanceAs (IsClosedImmersion (e₀.inv ≫ h₀))) (hr.trans hr'.symm) hone
  refine ⟨e, he, ?_⟩
  have hl : e.hom.left ≫ e₀.inv ≫ h₀ = h := congrArg (fun g => g.left) hef
  rw [← k, ← k', ← hl]
  simp only [Category.assoc]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoSpecialFibreTestGeometricTestStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_special_fibre_test_geometric_test : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (p : ℕ) [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c) (τ : ex.core.Test y), S.Big → ex.core.Fib → ∃ e : (Over.pullback (GlobalTheory.ZJ.rPt p ≫ spMap τ.j)).obj τ.H ≅ t.mod.Φ.G, IsMonHom e.hom ∧ e.hom.left ≫ t.mod.r ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = pullback.fst _ _ ≫ τ.f ≫ Q.G.ι := by
  first | exact @GlobalTheory.ZH.exists_iso_special_fibre_of_test | exact GlobalTheory.ZH.exists_iso_special_fibre_of_test | (intros; apply GlobalTheory.ZH.exists_iso_special_fibre_of_test <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CubicalBundleRelAmpleOfAmpleFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CubicalBundleRelAmpleOfAmpleFibres
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.CubicalFibreAmple

section General
variable {X X' Y : Scheme.{0}}

theorem pw_pw (H : LB X) (a b : ℤ) : pw (pw H a) b = pw H (a * b) :=
  congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X)) (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem triv_linComb_pw {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : Triv (LB.LinComb L φ ε)) (d : ℤ) : Triv (LB.LinComb (pw L d) φ ε) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨⟨fun j => t.s j ^ d⟩, fun i j => ?_⟩
  have e := congrArg (· ^ d) (ht i j)
  simp only [mul_zpow, ← map_zpow] at e
  refine e.trans (congrArg₂ (· * ·) ?_ rfl)
  refine (Finset.prod_zpow _ _ _).symm.trans (Finset.prod_congr rfl fun k _ => ?_)
  exact (zpow_comm _ _ _).trans (congrArg (· ^ ε k)
    ((map_zpow _ _ d).symm.trans (congrArg _ (map_zpow (pullU (φ k) _) _ d).symm)))

theorem exists_pull_mem {M : LB X} (s : LB.Sec M) (π : X' ⟶ X) :
    ∃ t : LB.Sec (M.pull π), ∀ z, π z ∈ nonzeroLocus s → z ∈ nonzeroLocus t := by
  obtain ⟨t, ht⟩ := SpreadSec.exists_pull s π
  refine ⟨t, fun z hz => ?_⟩
  obtain ⟨k, hk⟩ := AmpleSpan.exists_chart_of_mem s hz
  refine (mem_nonzeroLocus t z).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩
  rw [ht (fun _ => k) z hk]
  exact (AmpleSpan.mem_nonzeroLocus_iff_gs s π z hk).1 hz

theorem exists_mem_of_flat {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (hg : g.Flat)
    [CompactSpace X] [QuasiSeparatedSpace X] {f : X ⟶ Spec (CommRingCat.of R)} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of R')} (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    {M : LB X} (hM : M.IsLB) (σ : LB.Sec (M.pull π)) {z : X'} (hz : z ∈ nonzeroLocus σ) :
    ∃ u : LB.Sec M, π z ∈ nonzeroLocus u := by
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' h M hM σ
  obtain ⟨k, hk⟩ := exists_chart hM (π z)
  have e := (AmpleSpan.mem_nonzeroLocus_iff_gs σ (𝟙 X') z (k := fun _ => k) (mem_pull.2 hk)).1 hz
  rw [hu z k hk] at e
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum e
  exact ⟨u i, (AmpleSpan.mem_nonzeroLocus_iff_gs _ π z hk).2 (isUnit_of_mul_isUnit_right hi)⟩

theorem exists_finite_cover [CompactSpace X] {M : LB X} (s₀ : LB.Sec M)
    (h : ∀ x, ∃ u : LB.Sec M, x ∈ nonzeroLocus u) :
    ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec M), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun u : LB.Sec M => (nonzeroLocus u : Set X)) (fun u => (nonzeroLocus u).isOpen)
    (fun y _ => Set.mem_iUnion.2 (h y))
  refine ⟨F.card, Fin.cons s₀ (fun i => (F.equivFin.symm i : LB.Sec M)), top_unique fun y _ => ?_⟩
  obtain ⟨u, hu, hy⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ y))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨(F.equivFin ⟨u, hu⟩).succ, ?_⟩
  rw [Fin.cons_succ, Equiv.symm_apply_apply]
  exact hy

end General

theorem exists_mem_closed_fibre (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] (hG : IsAbelianScheme G) (N : LB G.left) (hN : N.IsLB)
    (s : LB.Sec N) (x : G.left) (hx : x ∈ nonzeroLocus s) :
    ∃ t : LB.Sec N, ∃ y ∈ nonzeroLocus t, G.hom y = IsLocalRing.closedPoint V := by
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  by_contra hcon
  push Not at hcon
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have : GeometricallyIntegral G.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance
  have hmax : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V ^ (0 + 1))
  have : IsIntegral (pullback G.hom (thick V (IsLocalRing.maximalIdeal V) 0)) :=
    GeometricallyIntegral.geometrically_isIntegral (thick V (IsLocalRing.maximalIdeal V) 0) _ _
      (IsPullback.of_hasPullback G.hom (thick V (IsLocalRing.maximalIdeal V) 0))
  have h0 : ∀ σ : LB.Sec N, ∃ τ : LB.Sec N, DVR.SecIsMul G.hom (ϖ ^ (0 + 1)) σ τ := fun σ =>
    (ThickDiv.main V ϖ hϖ G N σ 0).1 fun j => by
      refine eq_zero_of_basicOpen_eq_bot (X := pullback G.hom (thick V (IsLocalRing.maximalIdeal V) 0)) _
        (le_bot_iff.1 fun z hz => ?_)
      let p := pullback.fst G.hom (thick V (IsLocalRing.maximalIdeal V) 0)
      have hz' : p z ∈ G.left.basicOpen (σ.f j) :=
        (SetLike.ext_iff.1 (Scheme.preimage_basicOpen p (σ.f j)) z).2 hz
      refine hcon σ (p z) (TopologicalSpace.Opens.mem_iSup.2 ⟨j, hz'⟩) ?_
      have e : G.hom (p z) = thick V (IsLocalRing.maximalIdeal V) 0
          (pullback.snd G.hom (thick V (IsLocalRing.maximalIdeal V) 0) z) :=
        congrArg (fun q => q z) (pullback.condition (f := G.hom) (g := thick V (IsLocalRing.maximalIdeal V) 0))
      rw [e]
      refine PrimeSpectrum.ext ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le
        (PrimeSpectrum.isPrime _).ne_top fun a ha => ?_).symm
      change Ideal.Quotient.mk _ a ∈ PrimeSpectrum.asIdeal _
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (by rwa [zero_add, pow_one])]
      exact zero_mem _
  have h1 : ∀ (n : ℕ) (σ : LB.Sec N), ∃ τ : LB.Sec N, DVR.SecIsMul G.hom (ϖ ^ (n + 1)) σ τ := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      intro σ
      obtain ⟨τ, hτ⟩ := ih σ
      obtain ⟨ρ, hρ⟩ := h0 τ
      refine ⟨ρ, fun k => ?_⟩
      have e₁ : σ.f k = AbLaw.cst G.hom _ (ϖ ^ (n + 1)) * τ.f k := hτ k
      have e₂ : τ.f k = AbLaw.cst G.hom _ (ϖ ^ (0 + 1)) * ρ.f k := hρ k
      change σ.f k = AbLaw.cst G.hom _ (ϖ ^ (n + 1 + 1)) * ρ.f k
      rw [e₁, e₂, ← _root_.mul_assoc, ← map_mul, ← pow_add]
  have h2 : ∀ k, s.f k = 0 :=
    (sec_eq_zero_and_hom_eq_of_thickenings V (IsLocalRing.maximalIdeal V)
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge G).1 N hN s fun n =>
        (ThickDiv.main V ϖ hϖ G N s n).2 (h1 n s)
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  rw [h2, Scheme.basicOpen_zero] at hk
  exact hk

theorem exists_valuationRing (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsPrincipalIdealRing A] :
    ∃ (O : ValuationSubring (AlgebraicClosure (FractionRing A))) (g : A →+* O), g.Flat ∧ IsLocalHom g := by
  obtain ⟨O, h, hl⟩ := IsLocalRing.exists_factor_valuationRing (algebraMap A (AlgebraicClosure (FractionRing A)))
  refine ⟨O, _, ?_, hl⟩
  have inj : Function.Injective (algebraMap A (AlgebraicClosure (FractionRing A))) := by
    rw [IsScalarTower.algebraMap_eq A (FractionRing A)]
    exact (algebraMap (FractionRing A) _).injective.comp (IsFractionRing.injective A _)
  letI := ((algebraMap A (AlgebraicClosure (FractionRing A))).codRestrict O.toSubring h).toAlgebra
  refine Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (eq_bot_iff.2 ?_)
  rintro x ⟨⟨a, ha⟩, e⟩
  have e' : algebraMap A (AlgebraicClosure (FractionRing A)) a * x.1 = 0 := congrArg Subtype.val e
  exact Subtype.ext ((mul_eq_zero.1 e').resolve_left
    ((map_ne_zero_iff _ inj).2 (nonZeroDivisors.ne_zero ha)))

theorem relAmple_of_fibres : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsPrincipalIdealRing A], IsAdicComplete (IsLocalRing.maximalIdeal A) A → ∀ (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ M : CP B, (∀ (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)), RelAmple ((Over.pullback x).obj B) (M.L.L.pull (pullback.fst B.hom x))) → RelAmple B M.L.L := by
  intro _ _ A _ _ _ _ _ B _ _ hB M h
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : QuasiSeparatedSpace B.left := quasiSeparatedSpace_of_quasiSeparated B.hom
  have hL := M.L.isLB
  obtain ⟨d, hd, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy _ _ _ (LB.isLB_pull hL _)).1 (h _ (jK A))
  have hH := isLB_pw hL d

  have h₁ : ∃ σ : LB.Sec (pw M.L.L d), ∃ x, x ∈ nonzeroLocus σ := by
    have hσ : ∃ (σ : LB.Sec ((pw M.L.L d).pull (pullback.fst B.hom (jK A)))) (z : _), z ∈ nonzeroLocus σ := by
      rw [GlobalTheory.TrivLocus.pull_pw]
      have hz : (η[(Over.pullback (jK A)).obj B]).left (default : PrimeSpectrum (FractionRing A)) ∈
          ⨆ i, nonzeroLocus (s i) := by rw [hs.1]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
      exact ⟨s i, _, hi⟩
    obtain ⟨σ, z, hz⟩ := hσ
    obtain ⟨u, hu⟩ := exists_mem_of_flat (algebraMap A (FractionRing A))
      (RingHom.flat_algebraMap_iff.2 inferInstance) (IsPullback.of_hasPullback B.hom (jK A)) hH σ hz
    exact ⟨u, _, hu⟩
  have h₂ : ∃ σ : LB.Sec (pw M.L.L d), ∃ x ∈ nonzeroLocus σ, B.hom x = IsLocalRing.closedPoint A := by
    obtain ⟨σ, x, hx⟩ := h₁
    by_cases hA : IsLocalRing.maximalIdeal A = ⊥
    · refine ⟨σ, x, hx, PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal (PrimeSpectrum.isPrime _).ne_top) ?_)⟩
      exact hA.le.trans bot_le
    · have : IsDiscreteValuationRing A := { not_a_field' := hA }
      exact exists_mem_closed_fibre A B hB _ hH σ x hx
  obtain ⟨σ, x, hx, hxc⟩ := h₂

  obtain ⟨O, g, hg, hl⟩ := exists_valuationRing A
  let t : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom g)
  let π := pullback.fst B.hom t
  have ht : Function.Surjective t := by
    letI := g.toAlgebra
    have : Module.Flat A O := hg
    have : IsLocalHom (algebraMap A O) := hl
    have : Module.FaithfullyFlat A O := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := O)
  have hB' := CubeGen.isAb_baseChange hB t
  obtain ⟨_, _, c, -⟩ := exists_isCPMap M (toBase_mul_pullback B t) _ (pull_isLB hL π) _ (pullIso_isGen hL π)
  have cube : Triv (Theta ((Over.pullback t).obj B) ((pw M.L.L d).pull π)) := by
    rw [GlobalTheory.TrivLocus.pull_pw]
    exact triv_linComb_pw ⟨c.t, c.isGen⟩ d
  obtain ⟨σ', hσ'⟩ := exists_pull_mem σ π
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := B.hom) (g := t) x
    (IsLocalRing.closedPoint O) (hxc.trans (IsLocalRing.comap_closedPoint g).symm)
  have hu := SquareGenerated.exists_secs_sq_generate O (AlgebraicClosure (FractionRing A)) _ hB' _
    (LB.isLB_pull hH π) cube σ' ⟨z, hσ' z (by rw [← hz₁] at hx; exact hx), hz₂⟩
  rw [← GlobalTheory.TrivLocus.pull_pw, pw_pw, show (d : ℤ) * 2 = ((d * 2 : ℕ) : ℤ) by push_cast; rfl] at hu
  obtain ⟨m, u, hu⟩ := hu

  have hH₂ := isLB_pw hL ((d * 2 : ℕ) : ℤ)
  have gen : ∀ y, ∃ v : LB.Sec (pw M.L.L ((d * 2 : ℕ) : ℤ)), y ∈ nonzeroLocus v := fun y => by
    obtain ⟨q, hq⟩ := ht (B.hom y)
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := B.hom) (g := t) y q hq.symm
    have hw' : w ∈ ⨆ i, nonzeroLocus (u i) := by rw [hu]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hw'
    rw [← hw]
    exact exists_mem_of_flat g hg (IsPullback.of_hasPullback B.hom t) hH₂ (u i) hi
  obtain ⟨m', v, hv⟩ := exists_finite_cover (gen x).choose gen
  have aff := GlobalTheory.T.isAffineOpen_nonzeroLocus_of_fibrewise_ample A _ B.hom M.L.L (d * 2) m' v (by omega) hB.proper hL hv (fun q hq =>
    ⟨q.ResidueField, inferInstance, algebraMap A _, Ideal.ker_algebraMap_residueField q, h _ _⟩)
  obtain ⟨e, he, hw⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw_of_affine_loci A _ B.hom _ m' v hH₂ hv aff
  rw [pw_pw, ← Nat.cast_mul] at hw
  exact (GlobalTheory.Unif.relAmple_iff_veryAmpleBy A B M.L.L hL).2 ⟨d * 2 * e, Nat.mul_pos (by omega) he, hw⟩

end GlobalTheory.CubicalFibreAmple
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CubicalBundleRelAmpleOfAmpleFibresStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubical_bundle_relAmple_of_ample_fibres : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsPrincipalIdealRing A], IsAdicComplete (IsLocalRing.maximalIdeal A) A → ∀ (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ M : CP B, (∀ (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)), RelAmple ((Over.pullback x).obj B) (M.L.L.pull (pullback.fst B.hom x))) → RelAmple B M.L.L := by
  first | exact @GlobalTheory.CubicalFibreAmple.relAmple_of_fibres | exact GlobalTheory.CubicalFibreAmple.relAmple_of_fibres | (intros; apply GlobalTheory.CubicalFibreAmple.relAmple_of_fibres <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecGenericEqMulTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecGenericEqMulTheta
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.ThetaLine
open GlobalTheory.Points

variable {B : Scheme.{0}} (A : Over B) (L : LB A.left) (a : ℤ)

theorem le_chart {T : Over B} {K : Type} [CommRing K] (q : Sp K ⟶ (T ⊗ A).left) (j : L.ι)
    (h : Set.range (q ≫ (snd T A).left) ⊆ L.U j) : ⊤ ≤ q ⁻¹ᵁ (LPow A L a T).U (fun _ => j) :=
  fun y _ => Set.mem_iInter.2 fun _ => h ⟨y, rfl⟩

theorem valR_pull [GrpObj A] {T T' : Over B} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A}
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')} (H : IsPullSec A L a h hh s s')
    {K : Type} [CommRing K] (q : Sp K ⟶ (T' ⊗ A).left) (j : Fin 1 → L.ι) (hq : ⊤ ≤ q ⁻¹ᵁ (LPow A L a T').U j) :
    valR q _ (s'.f j) = valR (q ≫ h.left) _ (s.f j) := by
  rw [H j, valR_res q _ hq, valR_comp]

theorem valR_of_basis {Ω : Type} [CommRing Ω] (t : Sp Ω ⟶ B) {m : ℕ} (hm : m = 1)
    {b : Fin m → LB.Sec (LPow A L a (Over.mk t))} (hb : IsSecBasis _ b) :
    ∃ b₀ : LB.Sec (LPow A L a (Over.mk t)), ∀ s : LB.Sec (LPow A L a (Over.mk t)), ∃ c : Ω,
      ∀ (K : Type) [CommRing K] (β : Ω →+* K) (q : Sp K ⟶ (Over.mk t ⊗ A).left) (j : Fin 1 → L.ι),
        q ≫ (fst (Over.mk t) A).left = spMap β → ⊤ ≤ q ⁻¹ᵁ (LPow A L a (Over.mk t)).U j →
        valR q _ (s.f j) = β c * valR q _ (b₀.f j) := by
  subst hm
  refine ⟨b 0, fun s => ?_⟩
  obtain ⟨r, hr, -⟩ := hb s
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (r 0), fun K _ β q j hq hj => ?_⟩
  rw [hr j, Fin.sum_univ_one, valR_mul q _ hj, valR_res q _ hj]
  congr 1
  have e := valR_comp q (fst (Over.mk t) A).left ⊤ (r 0)
  refine e.symm.trans ?_
  rw [hq]
  have e2 := valR_specMap (C := K) (A := CommRingCat.of Ω) (CommRingCat.ofHom β)
    ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (r 0))
  refine Eq.trans ?_ e2
  exact congrArg (valR (spMap β) ⊤) ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom_inv_id_apply (r 0)).symm

theorem valR_ne_zero [GrpObj A] {T : Over B} {s : LB.Sec (LPow A L a T)} {z : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s z τ v) {K : Type} [Field K] (x : Sp K ⟶ T.left) (j : L.ι)
    (hj : Set.range (x ≫ z.left) ⊆ L.U j) (hv : valR x ⊤ v ≠ 0) :
    valR (x ≫ (ptSecT A z).left) _ (s.f fun _ => j) ≠ 0 := by
  have hx : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => z.left) (fun _ => j) :=
    fun y _ => Set.mem_iInter.2 fun _ => hj ⟨y, rfl⟩
  have e := congrArg (valR x _) (H fun _ => j)
  rw [valR_res x _ hx, valR_mul x _ hx, valR_res x _ hx] at e
  rw [valR_comp]
  refine e.trans_ne (mul_ne_zero hv ?_)
  rw [valR_eq x _ hx]
  exact ((τ.s fun _ => j).isUnit.map _).ne_zero

end GlobalTheory.ZH.ThetaLine


open GlobalTheory.Points GlobalTheory.ZH.ThetaLine in
theorem GlobalTheory.ZH.sec_generic_eq_mul_theta : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (s : LB.Sec (LPow ρ.P.A ρ.P.L 1 (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)))), ∃ c : Ω, ∀ (K : Type) [Field K] (β : Ω →+* K) (q : Sp K ⟶ ((Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ⊗ ρ.P.A).left) (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι), q ≫ (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left = spMap β → r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left → Set.range (q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left) ⊆ ρ.P.L.U jP → valF q _ (s.f fun _ => jP) = β c * valF r _ (ρ.th₁.f fun _ => jP) := by
  intro _ hL2 o Ω _ _ _ _ S ρ s
  let t₀ : Sp Ω ⟶ Sp S.R := spMap S.R.val.toRingHom
  let h : (Over.mk t₀ : Over (Sp S.R)) ⟶ baseOver (Sp S.R) := Over.homMk t₀ (Category.comp_id t₀)
  obtain ⟨th, hth⟩ : ∃ th, IsPullSec ρ.P.A ρ.P.L 1 (h ▷ ρ.P.A) (whiskerRight_snd h ρ.P.A) ρ.th₁ th :=
    (GlobalTheory.LN.PolFrames.exists_pullSec ρ.P.A ρ.P.L 1 h ρ.th₁).imp fun _ H => H.1
  obtain ⟨b, hb⟩ := GlobalTheory.PowBasis.exists_basis_pow hL2.secTwist ρ.P 1 le_rfl Ω t₀
  obtain ⟨b₀, hb₀⟩ := valR_of_basis ρ.P.A ρ.P.L 1 t₀ (one_pow _) hb
  obtain ⟨c, hc⟩ := hb₀ s
  obtain ⟨d, hd⟩ := hb₀ th
  have hd0 : d ≠ 0 := by
    obtain ⟨a, ha⟩ := S.th_ne
    obtain ⟨j, hj⟩ := exists_chart ρ.P.isLB ((t₀ ≫ (ρ.pt a).left) (IsLocalRing.closedPoint Ω))
    have hj' : Set.range (t₀ ≫ (ρ.pt a).left) ⊆ ρ.P.L.U j := by
      rintro _ ⟨y, rfl⟩
      rw [Subsingleton.elim y (IsLocalRing.closedPoint Ω)]
      exact hj
    have hne := valR_ne_zero ρ.P.A ρ.P.L 1 (ρ.th_val a) t₀ j hj'
      ((valR_specMap (C := Ω) (A := CommRingCat.of S.R) (CommRingCat.ofHom S.R.val.toRingHom) _).trans_ne ha)
    let x : Sp Ω ⟶ ((Over.mk t₀ : Over (Sp S.R)) ⊗ ρ.P.A).left := (ptSecT ρ.P.A (h ≫ ρ.pt a)).left
    have hx1 : x ≫ (fst (Over.mk t₀ : Over (Sp S.R)) ρ.P.A).left = spMap (RingHom.id Ω) :=
      (congrArg CommaMorphism.left (lift_fst (𝟙 (Over.mk t₀ : Over (Sp S.R))) (h ≫ ρ.pt a))).trans (Spec.map_id _).symm
    have hx2 : x ≫ (snd (Over.mk t₀ : Over (Sp S.R)) ρ.P.A).left = t₀ ≫ (ρ.pt a).left :=
      congrArg CommaMorphism.left (lift_snd (𝟙 (Over.mk t₀ : Over (Sp S.R))) (h ≫ ρ.pt a))
    have hx3 : x ≫ (h ▷ ρ.P.A).left = t₀ ≫ (ptSecT ρ.P.A (ρ.pt a)).left := by
      have : ptSecT ρ.P.A (h ≫ ρ.pt a) ≫ h ▷ ρ.P.A = h ≫ ptSecT ρ.P.A (ρ.pt a) := by
        simp [ptSecT]
      exact congrArg CommaMorphism.left this
    have hxj := le_chart ρ.P.A ρ.P.L 1 x j (hx2 ▸ hj')
    rintro rfl
    apply hne
    rw [← hx3, ← valR_pull ρ.P.A ρ.P.L 1 hth x _ hxj, hd Ω _ x _ hx1 hxj, map_zero, zero_mul]
  refine ⟨c / d, fun K _ β q r j hq hr hj => ?_⟩
  have hqj := le_chart ρ.P.A ρ.P.L 1 q j hj
  have hrq : r = q ≫ (h ▷ ρ.P.A).left := by
    have h2 : r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left =
        (q ≫ (h ▷ ρ.P.A).left) ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left := by
      rw [hr, Category.assoc, ← Over.comp_left, whiskerRight_snd]
    have w : (fst (baseOver (Sp S.R)) ρ.P.A).left =
        (snd (baseOver (Sp S.R)) ρ.P.A).left ≫ ρ.P.A.hom :=
      (Category.comp_id _).symm.trans (pullback.condition (f := 𝟙 (Sp S.R)) (g := ρ.P.A.hom))
    refine pullback.hom_ext (f := 𝟙 (Sp S.R)) (g := ρ.P.A.hom) ?_ h2
    change r ≫ (fst (baseOver (Sp S.R)) ρ.P.A).left = _ ≫ (fst (baseOver (Sp S.R)) ρ.P.A).left
    rw [w, ← Category.assoc, h2]
    simp only [Category.assoc]
  change valR q _ _ = β (c / d) * valR r _ _
  rw [hrq, ← valR_pull ρ.P.A ρ.P.L 1 hth q _ hqj, hc K β q _ hq hqj, hd K β q _ hq hqj, map_div₀,
    ← _root_.mul_assoc, div_mul_cancel₀ _ ((map_ne_zero β).2 hd0)]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecGenericEqMulThetaStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sec_generic_eq_mul_theta_alt : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (s : LB.Sec (LPow ρ.P.A ρ.P.L 1 (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)))), ∃ c : Ω, ∀ (K : Type) [Field K] (β : Ω →+* K) (q : Sp K ⟶ ((Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ⊗ ρ.P.A).left) (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι), q ≫ (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left = spMap β → r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left → Set.range (q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left) ⊆ ρ.P.L.U jP → valF q _ (s.f fun _ => jP) = β c * valF r _ (ρ.th₁.f fun _ => jP) := by
  first | exact @GlobalTheory.ZH.sec_generic_eq_mul_theta | exact GlobalTheory.ZH.sec_generic_eq_mul_theta | (intros; apply GlobalTheory.ZH.sec_generic_eq_mul_theta <;> assumption)
end
end

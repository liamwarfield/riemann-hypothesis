module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphism

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusCoordinateIsUnit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusCoordinateIsUnit
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoUnit

theorem awayMap_ratio_mul {K : Type} [Field K] {N e : ℕ} {a b : MvPolynomial (Fin (N + 1)) K}
    (ha : a ∈ grK K N e) (hb : b ∈ grK K N e) (hb1 : b ∈ grK K N (1 • e)) (ha1 : a ∈ grK K N (1 • e)) :
    HomogeneousLocalization.awayMap (grK K N) hb (x := a * b) rfl
        (HomogeneousLocalization.Away.mk _ ha 1 b hb1) *
      HomogeneousLocalization.awayMap (grK K N) ha (x := a * b) (mul_comm a b)
        (HomogeneousLocalization.Away.mk _ hb 1 a ha1) = 1 := by
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one, Localization.mk_mul,
    ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

theorem tV_isUnit {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens}
    (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) (k : Fin d) : IsUnit (tV i y hy V hV k) := by
  have h0 : y 0 ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hy 0)
  have h1 : y k.succ ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hy k.succ)
  have h0' : y 0 ∈ grK K N (1 • e) := by rw [one_smul]; exact h0
  have h1' : y k.succ ∈ grK K N (1 • e) := by rw [one_smul]; exact h1
  have hle : Proj.basicOpen (grK K N) (y 0 * y k.succ) ≤ Proj.basicOpen (grK K N) (y 0) := by
    rw [Proj.basicOpen_mul]; exact inf_le_left
  have hU : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0 * y k.succ) := by
    rw [Proj.basicOpen_mul]
    exact le_inf (hV.trans (iInf_le _ 0)) (hV.trans (iInf_le _ k.succ))
  have hu : IsUnit (HomogeneousLocalization.awayMap (grK K N) h1 (x := y 0 * y k.succ) rfl
      (HomogeneousLocalization.Away.mk _ h0 1 (y k.succ) h1')) :=
    isUnit_iff_exists_inv.mpr ⟨_, awayMap_ratio_mul h0 h1 h1' h0'⟩
  have e1 := Scheme.Hom.map_appLE i hU (homOfLE hle).op
  have e2 := Proj.awayMap_awayToSection (grK K N) h1 (f := y 0) (x := y 0 * y k.succ) rfl
  have key : tV i y hy V hV k =
      (Scheme.Hom.appLE i _ V hU).hom ((Proj.awayToSection (grK K N) (y 0 * y k.succ)).hom
        (HomogeneousLocalization.awayMap (grK K N) h1 (x := y 0 * y k.succ) rfl
          (HomogeneousLocalization.Away.mk _ h0 1 (y k.succ) h1'))) := by
    unfold tV yRatio
    rw [← e1, CommRingCat.hom_comp, RingHom.comp_apply]
    congr 1
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← e2, CommRingCat.hom_comp, RingHom.comp_apply]
    rfl
  rw [key]
  exact (hu.map _).map _

end GlobalTheory.CompanionTheory.GeoUnit
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusCoordinateIsUnitStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_coordinate_isUnit : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), ∀ k : Fin d, IsUnit (tV i y hy V hV k) := by
  first | exact @GlobalTheory.CompanionTheory.GeoUnit.tV_isUnit | exact GlobalTheory.CompanionTheory.GeoUnit.tV_isUnit | (intros; apply GlobalTheory.CompanionTheory.GeoUnit.tV_isUnit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QIsoAtRight
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.QCalc

section Linear

variable {R A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ C₂ : Type} [CommRing R]
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
  [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
  [AddCommGroup C₀] [AddCommGroup C₁] [AddCommGroup C₂]
  [Module R A₀] [Module R A₁] [Module R A₂]
  [Module R B₀] [Module R B₁] [Module R B₂]
  [Module R C₀] [Module R C₁] [Module R C₂]
  {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂}
  {c₀ : C₀ →ₗ[R] C₁} {c₁ : C₁ →ₗ[R] C₂}
  {f₀ : A₀ →ₗ[R] B₀} {f₁ : A₁ →ₗ[R] B₁} {f₂ : A₂ →ₗ[R] B₂}
  {g₀ : B₀ →ₗ[R] C₀} {g₁ : B₁ →ₗ[R] C₁} {g₂ : B₂ →ₗ[R] C₂} {k : A₁ →ₗ[R] C₁}

theorem qIsoAt_comp (hf₂ : ∀ x, f₂ (a₁ x) = b₁ (f₁ x)) (hg₀ : ∀ x, g₁ (b₀ x) = c₀ (g₀ x))
    (hk : ∀ x, k x = g₁ (f₁ x)) (hf : QIsoAt a₀ a₁ b₀ b₁ f₁) (hg : QIsoAt b₀ b₁ c₀ c₁ g₁) :
    QIsoAt a₀ a₁ c₀ c₁ k := by
  refine ⟨fun x hx ⟨y, hy⟩ ↦ ?_, fun z hz ↦ ?_⟩
  · have hc : b₁ (f₁ x) = 0 := by rw [← hf₂, hx, map_zero]
    exact hf.1 x hx (hg.1 (f₁ x) hc ⟨y, by rw [hy, hk]⟩)
  · obtain ⟨w, y, hw, hy⟩ := hg.2 z hz
    obtain ⟨x, y', hx, hy'⟩ := hf.2 w hw
    refine ⟨x, y + g₀ y', hx, ?_⟩
    have e : f₁ x = w + b₀ y' := by rw [← hy']; abel
    rw [hk, e, map_add (f := _), hg₀, map_add (f := _), ← hy]
    abel

theorem qIsoAt_right (hf₀ : ∀ x, f₁ (a₀ x) = b₀ (f₀ x)) (hf₂ : ∀ x, f₂ (a₁ x) = b₁ (f₁ x))
    (hg₀ : ∀ x, g₁ (b₀ x) = c₀ (g₀ x)) (hk : ∀ x, k x = g₁ (f₁ x))
    (hf : QIsoAt a₀ a₁ b₀ b₁ f₁) (hK : QIsoAt a₀ a₁ c₀ c₁ k) :
    QIsoAt b₀ b₁ c₀ c₁ g₁ := by
  refine ⟨fun x hx ⟨y, hy⟩ ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨u, v, hu, hv⟩ := hf.2 x hx
    have e : f₁ u = x + b₀ v := by rw [← hv]; abel
    obtain ⟨w, hw⟩ := hK.1 u hu ⟨y + g₀ v, by rw [hk, e, map_add (f := _), map_add (f := _), hg₀, hy]⟩
    refine ⟨f₀ w - v, ?_⟩
    rw [map_sub, ← hf₀, hw, e]
    abel
  · obtain ⟨x, y, hx, hy⟩ := hK.2 z hz
    refine ⟨f₁ x, y, by rw [← hf₂, hx, map_zero], ?_⟩
    rw [← hk]
    exact hy

theorem qIsoAt_left (hf₂ : ∀ x, f₂ (a₁ x) = b₁ (f₁ x))
    (hg₀ : ∀ x, g₁ (b₀ x) = c₀ (g₀ x)) (hg₂ : ∀ x, g₂ (b₁ x) = c₁ (g₁ x))
    (hk : ∀ x, k x = g₁ (f₁ x))
    (hg : QIsoAt b₀ b₁ c₀ c₁ g₁) (hK : QIsoAt a₀ a₁ c₀ c₁ k) :
    QIsoAt a₀ a₁ b₀ b₁ f₁ := by
  refine ⟨fun x hx ⟨y, hy⟩ ↦ ?_, fun z hz ↦ ?_⟩
  · exact hK.1 x hx ⟨g₀ y, by rw [← hg₀, hy, hk]⟩
  · have hc : c₁ (g₁ z) = 0 := by rw [← hg₂, hz, map_zero]
    obtain ⟨x, y, hx, hy⟩ := hK.2 (g₁ z) hc
    have hd : b₁ (f₁ x - z) = 0 := by rw [map_sub, ← hf₂, hx, hz, map_zero, sub_zero]
    obtain ⟨y', hy'⟩ := hg.1 (f₁ x - z) hd ⟨y, by rw [map_sub, ← hk, hy]⟩
    exact ⟨x, y', hx, hy'.symm⟩

end Linear

theorem qCalcSt : CxSt → QCalcSt := by
  intro hCx R _ C _ F D E _ _ G H m n k hk
  have cm : ∀ i x, pulln m (i + 1) (dn F i x) = dn G i (pulln m i x) :=
    fun i x ↦ LinearMap.congr_fun ((hCx R C F).2 D G m i) x
  have cn : ∀ i x, pulln n (i + 1) (dn G i x) = dn H i (pulln n i x) :=
    fun i x ↦ LinearMap.congr_fun ((hCx R D G).2 E H n i) x
  have zf : ∀ x : R, pulln m 0 ((0 : R →ₗ[R] Cn F 0) x) =
      (0 : R →ₗ[R] Cn G 0) ((0 : R →ₗ[R] R) x) := fun x ↦ by simp
  have zg : ∀ x : R, pulln n 0 ((0 : R →ₗ[R] Cn G 0) x) =
      (0 : R →ₗ[R] Cn H 0) ((0 : R →ₗ[R] R) x) := fun x ↦ by simp
  refine ⟨fun h₁ h₂ ↦ ⟨?_, fun i ↦ ?_⟩, fun h₁ h₂ ↦ ⟨?_, fun i ↦ ?_⟩, fun h₁ h₂ ↦ ⟨?_, fun i ↦ ?_⟩⟩
  · exact qIsoAt_comp (cm 0) zg (hk 0) h₁.1 h₂.1
  · exact qIsoAt_comp (cm (i + 1)) (cn i) (hk (i + 1)) (h₁.2 i) (h₂.2 i)
  · exact qIsoAt_right zf (cm 0) zg (hk 0) h₁.1 h₂.1
  · exact qIsoAt_right (cm i) (cm (i + 1)) (cn i) (hk (i + 1)) (h₁.2 i) (h₂.2 i)
  · exact qIsoAt_left (cm 0) zg (cn 0) (hk 0) h₁.1 h₂.1
  · exact qIsoAt_left (cm (i + 1)) (cn i) (cn (i + 1)) (hk (i + 1)) (h₁.2 i) (h₂.2 i)

end GlobalTheory.CompanionTheory.QCalc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHomogeneousIdealOfEvalZero
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoVan

theorem evV_awayMap {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)
    {x y z : MvPolynomial (Fin (N + 1)) K} {b : ℕ} (hy : y ∈ grK K N b) (hz : z = x * y)
    (V : X.Opens) (h : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) z)
    (h' : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) x) (u : HomogeneousLocalization.Away (grK K N) x) :
    evV i z V h (HomogeneousLocalization.awayMap (grK K N) hy hz u) = evV i x V h' u := by
  have e := congrArg (fun φ => φ.hom u) (Proj.awayMap_awayToSection (grK K N) hy hz)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [evV, RingHom.coe_comp, Function.comp_apply]
  rw [e, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem evV_res {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)
    {g : MvPolynomial (Fin (N + 1)) K} {V W : X.Opens} (hVW : V ≤ W)
    (hW : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g) (hV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g)
    (u : HomogeneousLocalization.Away (grK K N) g) :
    evV i g V hV u = resO hVW (evV i g W hW u) := by
  have e := congrArg (fun φ => φ.hom ((Proj.awayToSection (grK K N) g).hom u))
    (Scheme.Hom.appLE_map i hW (homOfLE hVW).op)
  exact e.symm

theorem away_factor {K : Type} [Field K] {N : ℕ} {x g f : MvPolynomial (Fin (N + 1)) K} {e s : ℕ}
    (hx : x ∈ grK K N 1) (hg : g ∈ grK K N e) (hf : f ∈ grK K N (s • e))
    (hf' : f ∈ grK K N ((s • e) • 1)) (hc : g ^ s ∈ grK K N ((s • e) • 1)) :
    HomogeneousLocalization.awayMap (grK K N) hg (rfl : x * g = x * g)
        (HomogeneousLocalization.Away.mk (grK K N) hx (s • e) f hf') =
      HomogeneousLocalization.awayMap (grK K N) hx (mul_comm x g)
          (HomogeneousLocalization.Away.mk (grK K N) hg s f hf) *
        HomogeneousLocalization.awayMap (grK K N) hg (rfl : x * g = x * g)
          (HomogeneousLocalization.Away.mk (grK K N) hx (s • e) (g ^ s) hc) := by
  ext
  simp only [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
  refine Localization.mk_eq_mk_iff.mpr ?_
  rw [Localization.r_iff_exists]
  use 1
  simp
  ring

theorem mem_homIdeal_of_vanish {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)
    (hX : IsIntegral X) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (he : 0 < e)
    (hg : g ∈ grK K N e) {s : ℕ} {f : MvPolynomial (Fin (N + 1)) K} (hf : f ∈ grK K N (s • e))
    (V : X.Opens) (hVne : (V : Set X).Nonempty)
    (hV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g)
    (h0 : evV i g V hV (HomogeneousLocalization.Away.mk (grK K N) hg s f hf) = 0) :
    f ∈ homIdeal i := by
  have hf' : f ∈ grK K N ((s • e) • 1) := by simpa using hf
  have hc : g ^ s ∈ grK K N ((s • e) • 1) := by
    have := SetLike.pow_mem_graded s hg
    simpa using this
  refine Ideal.subset_span ⟨s • e, hf', fun j => ?_⟩
  by_cases hU : ((i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) : X.Opens) : Set X).Nonempty
  · have hW : ((V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) : X.Opens) : Set X).Nonempty :=
      nonempty_preirreducible_inter V.isOpen (TopologicalSpace.Opens.isOpen _) hVne hU
    haveI : Nonempty (V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) : X.Opens) := hW.to_subtype
    have hx := xv_mem K N j
    have hWU : V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) ≤
        i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) := inf_le_right
    have hWV : V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) ≤ V := inf_le_left
    have hWg := hWV.trans hV
    have hWx : V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) ≤
        i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j * g) := by
      rw [Proj.basicOpen_mul]
      exact fun y hy => ⟨hWU hy, hWg hy⟩
    apply map_injective_of_isIntegral X (homOfLE hWU)
    rw [map_zero]
    refine (evV_res i hWU le_rfl hWU _).symm.trans ?_
    rw [← evV_awayMap i hg rfl _ hWx hWU, away_factor hx hg hf hf' hc, map_mul,
      evV_awayMap i hx (mul_comm _ g) _ hWx hWg, evV_res i hWV hV hWg, h0, map_zero, zero_mul]
  · refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 ?_)
    refine (X.basicOpen_le _).trans ?_
    intro y hy
    exact (hU ⟨y, hy⟩).elim

end GlobalTheory.CompanionTheory.GeoVan
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DnCompDn
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.HodgeCx

variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]

section Act

variable (F : C ⥤ CommAlgCat.{0} R)

def act {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) : Cn F m →ₗ[R] Cn F n :=
  LinearMap.pi fun c ↦ (mp F (c.map (homOfLE (Fin.le_last (θ (Fin.last m)))))).toLinearMap ∘ₗ
    LinearMap.proj (R := R) (φ := fun c : Fin (m + 1) ⥤ C ↦ (F.obj (c.obj (Fin.last m)) : Type))
      (θ.monotone.functor ⋙ c)

theorem act_apply {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) (f : Cn F m) (c : Fin (n + 1) ⥤ C) :
    act F θ f c = mp F (c.map (homOfLE (Fin.le_last (θ (Fin.last m))))) (f (θ.monotone.functor ⋙ c)) :=
  rfl

private theorem mp_map_endo_apply {n : ℕ} (c : Fin (n + 1) ⥤ C) {x : Fin (n + 1)} (h : x ⟶ x)
    (b : F.obj (c.obj x)) : GlobalTheory.CatCoh.mp F (c.map h) b = b := by
  have hc : c.map h = 𝟙 (c.obj x) := by
    rw [Subsingleton.elim h (𝟙 x)]
    exact c.map_id x
  rw [hc, GlobalTheory.CatCoh.mp_id]

private theorem mp_map_comp_apply {n : ℕ} (c : Fin (n + 1) ⥤ C) {x y z : Fin (n + 1)}
    (h : x ⟶ z) (h₁ : x ⟶ y) (h₂ : y ⟶ z) (b : F.obj (c.obj x)) :
    GlobalTheory.CatCoh.mp F (c.map h) b =
      GlobalTheory.CatCoh.mp F (c.map h₂) (GlobalTheory.CatCoh.mp F (c.map h₁) b) := by
  rw [Subsingleton.elim h (h₁ ≫ h₂), Functor.map_comp, GlobalTheory.CatCoh.mp_comp]

theorem act_id {n : ℕ} (f : Cn F n) : act F (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) f = f := by
  funext c
  show GlobalTheory.CatCoh.mp F (c.map (𝟙 (Fin.last n))) (f c) = f c
  exact mp_map_endo_apply F c _ _

theorem act_comp {k m n : ℕ} (θ : Fin (k + 1) →o Fin (m + 1)) (ψ : Fin (m + 1) →o Fin (n + 1))
    (f : Cn F k) : act F (ψ.comp θ) f = act F ψ (act F θ f) := by
  funext c
  exact mp_map_comp_apply F c _
    (homOfLE (ψ.monotone (Fin.le_last (θ (Fin.last k))))) (homOfLE (Fin.le_last (ψ (Fin.last m))))
    (f ((ψ.comp θ).monotone.functor ⋙ c))

def cosimp : CosimplicialObject (ModuleCat.{0} R) where
  obj a := ModuleCat.of R (Cn F a.len)
  map θ := ModuleCat.ofHom (act F θ.toOrderHom)
  map_id a := ModuleCat.hom_ext (LinearMap.ext fun f ↦ act_id F f)
  map_comp θ ψ := ModuleCat.hom_ext (LinearMap.ext fun f ↦ act_comp F θ.toOrderHom ψ.toOrderHom f)

theorem cof_eq (n : ℕ) (i : Fin (n + 2)) :
    cof F n i = act F (Fin.succAboveOrderEmb i).toOrderHom := rfl

theorem objD_hom (n : ℕ) : (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cosimp F) n).hom = dn F n := by
  unfold AlgebraicTopology.AlternatingCofaceMapComplex.objD
  rw [ModuleCat.hom_sum, MainStatements.Hodge.dn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ModuleCat.hom_zsmul]
  first
  | rfl
  | (rw [← Int.cast_smul_eq_zsmul R, Int.cast_pow, Int.cast_neg, Int.cast_one]; rfl)

theorem dn_comp_dn (n : ℕ) : dn F (n + 1) ∘ₗ dn F n = 0 := by
  have h := congrArg ModuleCat.Hom.hom
    (AlgebraicTopology.AlternatingCofaceMapComplex.d_squared (GlobalTheory.CompanionTheory.HodgeCx.cosimp F) n)
  rw [ModuleCat.hom_comp, GlobalTheory.CompanionTheory.HodgeCx.objD_hom, GlobalTheory.CompanionTheory.HodgeCx.objD_hom,
    ModuleCat.hom_zero] at h
  exact h

end Act

theorem pulln_cof {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
    (m : CoefMap (RingHom.id R) F G) (n : ℕ) (i : Fin (n + 2)) (f : Cn F n) :
    pulln m (n + 1) (cof F n i f) = cof G n i (pulln m n f) := by
  funext c
  exact m.3 (c.map (homOfLE (Fin.le_last _))) (f (MainStatements.Hodge.face i c ⋙ m.1))

theorem pulln_dn {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
    (m : CoefMap (RingHom.id R) F G) (n : ℕ) :
    pulln m (n + 1) ∘ₗ dn F n = dn G n ∘ₗ pulln m n := by
  apply LinearMap.ext
  intro f
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.comp_apply, MainStatements.Hodge.dn, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul, map_zsmul, GlobalTheory.CompanionTheory.HodgeCx.pulln_cof]

theorem cxSt : CxSt := by
  intro R _ C _ F
  exact ⟨GlobalTheory.CompanionTheory.HodgeCx.dn_comp_dn F, fun D _ G m n => GlobalTheory.CompanionTheory.HodgeCx.pulln_dn m n⟩

end GlobalTheory.CompanionTheory.HodgeCx
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormRestrictionCocycle
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormRestrictionCocycle
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrPull
noncomputable section
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

theorem prod_mem_fil {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (T : C) :
    ∀ (n : ℕ) (g : Fin n → Φ.A.obj T), (∀ k, g k ∈ Φ.J.S T) → ∏ k, g k ∈ (Fil n).S T
  | 0, g, _ => by
    have h := hF.top 0 le_rfl T
    simp only [Nat.cast_zero, h]
    exact Submodule.mem_top
  | n + 1, g, h => by
    rw [Fin.prod_univ_castSucc]
    have h1 : g (Fin.last n) ∈ (Fil ((1 : ℕ) : ℤ)).S T := by
      rw [Nat.cast_one, hF.one]; exact h _
    exact hF.mul n 1 T (prod_mem_fil hF T n _ fun k => h _) h1

variable {d : ℕ} {E : Frame Φ (d + 1)} (Q : Poly Φ) (σ : ∀ T : C, E.D ⟶ T)

theorem tau_sec_Pmap (i : Fin d) {T T' : C} (φ : T ⟶ T') :
    E.τ i.succ (Cut.sec Q ⟨T, σ T⟩ ≫ Cut.Pmap Q (X := ⟨T, σ T⟩) (Y := ⟨T', σ T'⟩) φ) (Cut.sec Q ⟨T', σ T'⟩) =
      (Φ.A.map (Q.j T')).hom (E.τ i.succ (σ T ≫ φ) (σ T')) := by
  rw [Cut.τ_sec, if_neg (Fin.succ_ne_zero i), neg_zero, zero_add]
  have e : σ T ≫ Q.j T ≫ Cut.Pmap Q (X := ⟨T, σ T⟩) (Y := ⟨T', σ T'⟩) φ = (σ T ≫ φ) ≫ Q.j T' := by
    have := Cut.Pmap_j Q (X := ⟨T, σ T⟩) (Y := ⟨T', σ T'⟩) φ
    simp only at this
    rw [this, Category.assoc]
  simp only
  rw [e, E.add i.succ _ (σ T' ≫ Q.j T') _, E.nat]
  have h := Cut.sec_spec Q (E := E) ⟨T', σ T'⟩ i.succ
  simp only at h
  rw [h, if_neg (Fin.succ_ne_zero i), add_zero]

theorem factor {T₀ T₁ T₂ : C} (i : Fin d) (b : T₀ ⟶ T₁) (a : T₁ ⟶ T₂) :
    (Φ.A.map (Cut.Pmap Q (X := ⟨T₁, σ T₁⟩) (Y := ⟨T₂, σ T₂⟩) a)).hom
      (E.τ i.succ (Cut.sec Q ⟨T₀, σ T₀⟩ ≫ Cut.Pmap Q (X := ⟨T₀, σ T₀⟩) (Y := ⟨T₁, σ T₁⟩) b) (Cut.sec Q ⟨T₁, σ T₁⟩)) =
      (Φ.A.map (Q.j T₂)).hom ((Φ.A.map a).hom (E.τ i.succ (σ T₀ ≫ b) (σ T₁))) := by
  rw [tau_sec_Pmap, ← Cut.mapA_comp, ← Cut.mapA_comp]
  have := Cut.Pmap_j Q (X := ⟨T₁, σ T₁⟩) (Y := ⟨T₂, σ T₂⟩) a
  simp only at this
  rw [this]

variable {Fil : ℤ → IdF Φ.A}

theorem form_sub_mem (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ) (hr : r = j + q)
    (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D) (s : ComposableArrows C j) :
    (show Φ.A.obj (Q.P (s.obj (Fin.last j))) from (Cut.E1 E).form Cut.can I x (s ⋙ Cut.Pσ Q σ)) -
      (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom (E.form σ (Fin.succ ∘ I) x s) ∈
        (Fil (r + 1)).S (Q.P (s.obj (Fin.last j))) := by
  have e1 : ∀ k : Fin j, ((Cut.Φ1 E).A.map ((s ⋙ Cut.Pσ Q σ).map (homOfLE (Fin.le_last k.succ)))).hom
      ((Cut.E1 E).a Cut.can (I k) ((s ⋙ Cut.Pσ Q σ).map (homOfLE (Fin.castSucc_lt_succ (i := k)).le))) =
      (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom ((Φ.A.map (s.map (homOfLE (Fin.le_last k.succ)))).hom
        (E.a σ ((Fin.succ ∘ I) k) (s.map (homOfLE (Fin.castSucc_lt_succ (i := k)).le)))) :=
    fun k => factor Q σ (I k) _ _
  let P₀ : Φ.A.obj (s.obj (Fin.last j)) := ∏ k : Fin j, (Φ.A.map (s.map (homOfLE (Fin.le_last k.succ)))).hom
    (E.a σ ((Fin.succ ∘ I) k) (s.map (homOfLE (Fin.castSucc_lt_succ (i := k)).le)))
  have hP : P₀ ∈ (Fil j).S (s.obj (Fin.last j)) :=
    prod_mem_fil hF _ j _ fun k => Φ.J.map_mem _ (E.mem _ _ _)
  let u : E.D ⟶ Q.P (s.obj (Fin.last j)) := Cut.sec Q ⟨s.obj (Fin.last j), σ _⟩
  let v : E.D ⟶ Q.P (s.obj (Fin.last j)) := σ (s.obj (Fin.last j)) ≫ Q.j _
  have f1 : (show Φ.A.obj (Q.P (s.obj (Fin.last j))) from (Cut.E1 E).form Cut.can I x (s ⋙ Cut.Pσ Q σ)) =
      (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom P₀ * (Φ.A.map u).hom x := by
    have h : (∏ k : Fin j, (show Φ.A.obj (Q.P (s.obj (Fin.last j))) from
        ((Cut.Φ1 E).A.map ((s ⋙ Cut.Pσ Q σ).map (homOfLE (Fin.le_last k.succ)))).hom
          ((Cut.E1 E).a Cut.can (I k) ((s ⋙ Cut.Pσ Q σ).map (homOfLE (Fin.castSucc_lt_succ (i := k)).le))))) =
        (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom P₀ :=
      (Finset.prod_congr rfl fun k _ => e1 k).trans (map_prod (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom _ _).symm
    exact congrArg (· * (Φ.A.map u).hom x) h
  have f2 : (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom (E.form σ (Fin.succ ∘ I) x s) =
      (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom P₀ * (Φ.A.map v).hom x := by
    change (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom (P₀ * (Φ.A.map (σ _)).hom x) = _
    rw [map_mul, ← Cut.mapA_comp]
  rw [f1, f2, ← mul_sub]
  have hcast : r + 1 = ((j + (q + 1) : ℕ) : ℤ) := by rw [hr]; push_cast; ring
  rw [hcast]
  refine hF.mul j (q + 1) _ ((Fil j).map_mem _ hP) ?_
  have := hc q u v hx
  have e : ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 := by push_cast; rfl
  rw [e]
  exact this

theorem gr_pull {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ) (hr : r = j + q)
    (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D)
    (f : CH.Cn (Cut.U E ⋙ gr Fil r) j) (g : CH.Cn (gr Fil r) j)
    (hf : ∀ s, (show sqM _ _ _ from f s).1 = Ideal.Quotient.mk _ ((Cut.E1 E).form Cut.can I x s))
    (hg : ∀ s, (show sqM _ _ _ from g s).1 = Ideal.Quotient.mk _ (E.form σ (Fin.succ ∘ I) x s)) :
    (CH.Mor.restrict (Cut.U E ⋙ gr Fil r) (Cut.Pσ Q σ)).pullC j f =
      (CH.Mor.ofNatTrans (Functor.whiskerRight (Cut.jσ Q σ) (gr Fil r))).pullC j g := by
  funext s
  refine Subtype.ext ?_
  have h1 := hf (s ⋙ Cut.Pσ Q σ)
  have h2 := hg s
  change (show sqM _ _ _ from f (s ⋙ Cut.Pσ Q σ)).1 =
    Ideal.quotientMapₐ _ (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom (fun _ hx => (Fil (r + 1)).map_mem _ hx)
      (show sqM _ _ _ from g s).1
  rw [h1, h2]
  exact Ideal.Quotient.eq.2 (form_sub_mem Q σ hF hc j q r hr I x hx s)

end
end GlobalTheory.CompanionTheory.GrPull
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormRestrictionCocycleStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_form_restriction_cocycle : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ) (hr : r = j + q)
    (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D)
    (f : CH.Cn (Cut.U E ⋙ gr Fil r) j) (g : CH.Cn (gr Fil r) j),
    (∀ s, (show sqM _ _ _ from f s).1 = Ideal.Quotient.mk _ ((Cut.E1 E).form Cut.can I x s)) →
    (∀ s, (show sqM _ _ _ from g s).1 = Ideal.Quotient.mk _ (E.form σ (Fin.succ ∘ I) x s)) →
    (CH.Mor.restrict (Cut.U E ⋙ gr Fil r) (Cut.Pσ Q σ)).pullC j f =
      (CH.Mor.ofNatTrans (Functor.whiskerRight (Cut.jσ Q σ) (gr Fil r))).pullC j g := by
  first | exact @GlobalTheory.CompanionTheory.GrPull.gr_pull | exact GlobalTheory.CompanionTheory.GrPull.gr_pull | (intros; apply GlobalTheory.CompanionTheory.GrPull.gr_pull <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIntegralExpression
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIntegralExpression
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Geo


open MvPolynomial in
theorem exists_monic_relation {K σ : Type} [Field K] {m : ℕ} (I : Ideal (MvPolynomial σ K))
    (y : Fin m → MvPolynomial σ K)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial σ K ⧸ I))
    (a : MvPolynomial σ K) :
    ∃ (s : ℕ) (C : ℕ → MvPolynomial (Fin m) K), 0 < s ∧
      a ^ s + ∑ l ∈ Finset.range s, aeval y (C l) * a ^ l ∈ I := by
  by_cases htop : I = ⊤
  · exact ⟨1, 0, one_pos, by simp [htop]⟩
  haveI : Nontrivial (MvPolynomial σ K ⧸ I) := Ideal.Quotient.nontrivial_iff.2 htop
  set B := Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)) with hB
  haveI : Algebra.IsIntegral B (MvPolynomial σ K ⧸ I) := Algebra.IsIntegral.of_finite _ _
  obtain ⟨p, hp, hroot⟩ := Algebra.IsIntegral.isIntegral (R := B) (Ideal.Quotient.mk I a)
  have hq : (p * Polynomial.X).Monic := hp.mul Polynomial.monic_X
  have hroot' : Polynomial.eval₂ (algebraMap B (MvPolynomial σ K ⧸ I)) (Ideal.Quotient.mk I a)
      (p * Polynomial.X) = 0 := by
    rw [Polynomial.eval₂_mul, hroot, zero_mul]
  have hdeg : 0 < (p * Polynomial.X).natDegree := by
    rw [hp.natDegree_mul Polynomial.monic_X, Polynomial.natDegree_X]
    omega
  generalize p * Polynomial.X = q at hq hroot' hdeg
  have hlift : ∀ l, ∃ c : MvPolynomial (Fin m) K,
      Ideal.Quotient.mk I (aeval y c) = ((q.coeff l : B) : MvPolynomial σ K ⧸ I) := by
    intro l
    have hmem : ((q.coeff l : B) : MvPolynomial σ K ⧸ I) ∈
        (aeval (fun k => Ideal.Quotient.mk I (y k)) :
          MvPolynomial (Fin m) K →ₐ[K] MvPolynomial σ K ⧸ I).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact (q.coeff l).2
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c, ?_⟩
    rw [← hc]
    have := MvPolynomial.comp_aeval_apply (R := K) (B := MvPolynomial σ K ⧸ I) y
      (Ideal.Quotient.mkₐ K I) c
    simpa using this
  choose C hC using hlift
  refine ⟨q.natDegree, C, hdeg, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hroot', Polynomial.eval₂_eq_sum_range,
    Finset.sum_range_succ, map_add, map_sum, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, hC, map_pow]
    rfl
  · simp [hq.coeff_natDegree]


open MvPolynomial in
theorem homogeneousComponent_aeval_mul {K σ : Type} [Field K] {m e : ℕ} (he : 0 < e)
    (y : Fin m → MvPolynomial σ K) (hy : ∀ k, (y k).IsHomogeneous e)
    (C : MvPolynomial (Fin m) K) (r t : ℕ) (b : MvPolynomial σ K) (hb : b.IsHomogeneous t) :
    homogeneousComponent (e * r + t) (aeval y C * b) = aeval y (homogeneousComponent r C) * b := by
  have key : ∀ r', homogeneousComponent (e * r + t) (aeval y (homogeneousComponent r' C) * b) =
      if r' = r then aeval y (homogeneousComponent r C) * b else 0 := by
    intro r'
    have h : (aeval y (homogeneousComponent r' C) * b).IsHomogeneous (e * r' + t) :=
      ((homogeneousComponent_isHomogeneous r' C).aeval y hy).mul hb
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 h)]
    by_cases hr : r' = r
    · subst hr
      simp
    · have hne : e * r' + t ≠ e * r + t := fun h' =>
        hr (Nat.eq_of_mul_eq_mul_left he (Nat.add_right_cancel h'))
      rw [if_neg hne.symm, if_neg hr]
  conv_lhs => rw [← sum_homogeneousComponent C]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul, map_sum]
  simp_rw [key]
  rw [Finset.sum_ite_eq']
  split_ifs with hmem
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by simpa [Nat.lt_succ_iff] using hmem)]
    simp


open MvPolynomial in
theorem exists_hom_relation {K σ : Type} [Field K] {m : ℕ} (I : Ideal (MvPolynomial σ K))
    (hI : ∀ f ∈ I, ∀ n : ℕ, homogeneousComponent n f ∈ I) (e : ℕ) (he : 0 < e)
    (y : Fin m → MvPolynomial σ K) (hy : ∀ k, (y k).IsHomogeneous e)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial σ K ⧸ I))
    (w : ℕ) (a : MvPolynomial σ K) (ha : a.IsHomogeneous (e * w)) :
    ∃ (s : ℕ) (c : ℕ → MvPolynomial (Fin m) K), 0 < s ∧ (∀ l, (c l).IsHomogeneous ((s - l) * w)) ∧
      a ^ s + ∑ l ∈ Finset.range s, aeval y (c l) * a ^ l ∈ I := by
  obtain ⟨s, C, hs, hmem⟩ := exists_monic_relation I y hfin a
  refine ⟨s, fun l => homogeneousComponent ((s - l) * w) (C l), hs,
    fun l => homogeneousComponent_isHomogeneous _ _, ?_⟩
  have hcomp := hI _ hmem (e * w * s)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum] at hcomp
  convert hcomp using 2
  · have h := ha.pow s
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 h)]
    simp
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ s := (Finset.mem_range.1 hl).le
    have hdeg : e * w * s = e * ((s - l) * w) + e * w * l := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hl'
      simp only [Nat.add_sub_cancel_left]
      ring
    rw [hdeg, homogeneousComponent_aeval_mul he y hy (C l) _ _ _ (ha.pow l)]

end GlobalTheory.CompanionTheory.Geo
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIntegralExpressionStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_integral_expression : ∀ {K σ : Type} [Field K] {m : ℕ} (I : Ideal (MvPolynomial σ K)), (∀ f ∈ I, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ I) → ∀ (e : ℕ), 0 < e → ∀ (y : Fin m → MvPolynomial σ K), (∀ k, (y k).IsHomogeneous e) → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k))) (MvPolynomial σ K ⧸ I) → ∀ (w : ℕ) (a : MvPolynomial σ K), a.IsHomogeneous (e * w) → ∃ (s : ℕ) (c : ℕ → MvPolynomial (Fin m) K), 0 < s ∧ (∀ l, (c l).IsHomogeneous ((s - l) * w)) ∧ a ^ s + ∑ l ∈ Finset.range s, MvPolynomial.aeval y (c l) * a ^ l ∈ I := by
  first | exact @GlobalTheory.CompanionTheory.Geo.exists_hom_relation | exact GlobalTheory.CompanionTheory.Geo.exists_hom_relation | (intros; apply GlobalTheory.CompanionTheory.Geo.exists_hom_relation <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechNerveFaceOneZero
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open CategoryTheory.ComposableArrows

namespace GlobalTheory.CompanionTheory.Dict

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def L0 : Cn F 0 →ₗ[R] C0 F where
  toFun f T := f (mk₀ T)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def L1 : Cn F 1 →ₗ[R] C1 F where
  toFun f _ _ φ := f (mk₁ φ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def L2 : Cn F 2 →ₗ[R] C2 F where
  toFun f _ _ _ φ ψ := f (mk₂ φ ψ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def L3 : Cn F 3 →ₗ[R] C3 F where
  toFun f _ _ _ _ φ ψ χ := f (mk₃ φ ψ χ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem L0_bijective_cochain : Function.Bijective (L0 F) := by
  refine ⟨fun f g h => funext fun c => ?_, fun e => ⟨fun c => e (c.obj (Fin.last 0)), rfl⟩⟩
  obtain ⟨X, rfl⟩ := ComposableArrows.mk₀_surjective c
  exact congr_fun h X

theorem L1_bijective_cochain : Function.Bijective (L1 F) := by
  refine ⟨fun f g h => funext fun c => ?_, fun e => ⟨fun c => e (c.obj 0) (c.obj (Fin.last 1))
    (c.map (homOfLE (Fin.zero_le _))), rfl⟩⟩
  obtain ⟨X₀, X₁, φ, rfl⟩ := ComposableArrows.mk₁_surjective c
  exact congr_fun (congr_fun (congr_fun h X₀) X₁) φ

theorem L2_bijective_cochain : Function.Bijective (L2 F) := by
  refine ⟨fun f g h => funext fun c => ?_, fun e => ⟨fun c => e (c.obj 0) (c.obj 1) (c.obj (Fin.last 2))
    (c.map (homOfLE (show (0 : Fin 3) ≤ 1 by decide)))
    (c.map (homOfLE (show (1 : Fin 3) ≤ Fin.last 2 by decide))), rfl⟩⟩
  obtain ⟨X₀, X₁, X₂, φ, ψ, rfl⟩ := ComposableArrows.mk₂_surjective c
  exact congr_fun (congr_fun (congr_fun (congr_fun (congr_fun h X₀) X₁) X₂) φ) ψ

theorem L3_bijective_cochain : Function.Bijective (L3 F) := by
  refine ⟨fun f g h => funext fun c => ?_, fun e => ⟨fun c => e (c.obj 0) (c.obj 1) (c.obj 2)
    (c.obj (Fin.last 3)) (c.map (homOfLE (show (0 : Fin 4) ≤ 1 by decide)))
    (c.map (homOfLE (show (1 : Fin 4) ≤ 2 by decide)))
    (c.map (homOfLE (show (2 : Fin 4) ≤ Fin.last 3 by decide))), rfl⟩⟩
  obtain ⟨X₀, X₁, X₂, X₃, φ, ψ, χ, rfl⟩ := ComposableArrows.mk₃_surjective c
  exact congr_fun (congr_fun (congr_fun (congr_fun (congr_fun (congr_fun (congr_fun h X₀) X₁) X₂) X₃) φ) ψ) χ

theorem cof_eq {n : ℕ} (i : Fin (n + 2)) (c : Fin (n + 2) ⥤ C) (c' : Fin (n + 1) ⥤ C)
    (h : face i c = c') (u : c'.obj (Fin.last n) ⟶ c.obj (Fin.last (n + 1)))
    (hu : HEq (c.map (homOfLE (Fin.le_last (i.succAbove (Fin.last n))))) u) (f : Cn F n) :
    cof F n i f c = mp F u (f c') := by
  subst h
  obtain rfl := eq_of_heq hu
  rfl

theorem dn0 (f : Cn F 0) (c : Fin 2 ⥤ C) : dn F 0 f c = cof F 0 0 f c - cof F 0 1 f c := by
  simp [dn, Fin.sum_univ_two, sub_eq_add_neg]

theorem dn1 (f : Cn F 1) (c : Fin 3 ⥤ C) :
    dn F 1 f c = cof F 1 0 f c - cof F 1 1 f c + cof F 1 2 f c := by
  simp [dn, Fin.sum_univ_three, pow_succ, sub_eq_add_neg]

theorem dn2 (f : Cn F 2) (c : Fin 4 ⥤ C) :
    dn F 2 f c = cof F 2 0 f c - cof F 2 1 f c + cof F 2 2 f c - cof F 2 3 f c := by
  simp [dn, Fin.sum_univ_four, pow_succ, sub_eq_add_neg]

theorem eq_mk₁ (c : ComposableArrows C 1) (x : c.left ⟶ c.right) (h : c.hom = x) : c = mk₁ x := by
  obtain ⟨X₀, X₁, g, rfl⟩ := ComposableArrows.mk₁_surjective c
  subst h
  rfl

theorem eq_mk₂ (c : ComposableArrows C 2) (x : c.obj' 0 ⟶ c.obj' 1) (y : c.obj' 1 ⟶ c.obj' 2)
    (hx : map' c 0 1 = x) (hy : map' c 1 2 = y) : c = mk₂ x y := by
  obtain ⟨X₀, X₁, X₂, g₀, g₁, rfl⟩ := ComposableArrows.mk₂_surjective c
  subst hx hy
  rfl

section Faces

variable {T T' T'' T''' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''')

theorem cech_nerve_face_one_zero : face 0 (mk₁ φ) = mk₀ T' := by
  exact ComposableArrows.ext₀ rfl
theorem cech_nerve_face_one_one : face 1 (mk₁ φ) = mk₀ T := by
  exact ComposableArrows.ext₀ rfl
theorem cech_nerve_face_two_zero : face 0 (mk₂ φ ψ) = mk₁ ψ := by
  exact eq_mk₁ (face 0 (mk₂ φ ψ)) ψ rfl
theorem cech_nerve_face_two_one : face 1 (mk₂ φ ψ) = mk₁ (φ ≫ ψ) := by
  exact eq_mk₁ (face 1 (mk₂ φ ψ)) (φ ≫ ψ) rfl
theorem cech_nerve_face_two_two : face 2 (mk₂ φ ψ) = mk₁ φ := by
  exact eq_mk₁ (face 2 (mk₂ φ ψ)) φ rfl
theorem face_zero_mk3 : face 0 (mk₃ φ ψ χ) = mk₂ ψ χ := by
  exact eq_mk₂ (face 0 (mk₃ φ ψ χ)) ψ χ rfl rfl
theorem face_one_mk3 : face 1 (mk₃ φ ψ χ) = mk₂ (φ ≫ ψ) χ := by
  exact eq_mk₂ (face 1 (mk₃ φ ψ χ)) (φ ≫ ψ) χ rfl rfl
theorem face_two_mk3 : face 2 (mk₃ φ ψ χ) = mk₂ φ (ψ ≫ χ) := by
  exact eq_mk₂ (face 2 (mk₃ φ ψ χ)) φ (ψ ≫ χ) rfl rfl
theorem face_three_mk3 : face 3 (mk₃ φ ψ χ) = mk₂ φ ψ := by
  exact eq_mk₂ (face 3 (mk₃ φ ψ χ)) φ ψ rfl rfl

end Faces

private theorem mp_id_apply (X : C) (x : F.obj X) : mp F (𝟙 X) x = x := by
  rw [mp, CategoryTheory.Functor.map_id]
  rfl

theorem L1_dn_zero_eq_d0_L0 (f : Cn F 0) : L1 F (dn F 0 f) = d0 F (L0 F f) := by
  funext T T' φ
  show dn F 0 f (mk₁ φ) = L0 F f T' - mp F φ (L0 F f T)
  rw [dn0, cof_eq F (n := 0) 0 (mk₁ φ) (mk₀ T') (cech_nerve_face_one_zero φ) (𝟙 T') HEq.rfl f,
    cof_eq F (n := 0) 1 (mk₁ φ) (mk₀ T) (cech_nerve_face_one_one φ) φ HEq.rfl f]
  show mp F (𝟙 T') (f (mk₀ T')) - mp F φ (f (mk₀ T)) = _
  rw [mp_id_apply F T' (f (mk₀ T'))]
  rfl

theorem L2_dn_one_eq_d1_L1 (f : Cn F 1) : L2 F (dn F 1 f) = d1 F (L1 F f) := by
  funext T T' T'' φ ψ
  show dn F 1 f (mk₂ φ ψ) = mp F ψ (L1 F f T T' φ) - L1 F f T T'' (φ ≫ ψ) + L1 F f T' T'' ψ
  rw [dn1, cof_eq F (n := 1) 0 (mk₂ φ ψ) (mk₁ ψ) (cech_nerve_face_two_zero φ ψ) (𝟙 T'') HEq.rfl f,
    cof_eq F (n := 1) 1 (mk₂ φ ψ) (mk₁ (φ ≫ ψ)) (cech_nerve_face_two_one φ ψ) (𝟙 T'') HEq.rfl f,
    cof_eq F (n := 1) 2 (mk₂ φ ψ) (mk₁ φ) (cech_nerve_face_two_two φ ψ) ψ HEq.rfl f]
  conv_lhs => rw [sub_add_comm]
  show mp F ψ (f (mk₁ φ)) - mp F (𝟙 T'') (f (mk₁ (φ ≫ ψ))) + mp F (𝟙 T'') (f (mk₁ ψ)) = _
  rw [mp_id_apply F T'' (f (mk₁ (φ ≫ ψ))), mp_id_apply F T'' (f (mk₁ ψ))]
  rfl

theorem L3_dn_two_eq_d2_L2 (f : Cn F 2) : L3 F (dn F 2 f) = d2 F (L2 F f) := by
  funext T T' T'' T''' φ ψ χ
  show dn F 2 f (mk₃ φ ψ χ) = L2 F f T' T'' T''' ψ χ - L2 F f T T'' T''' (φ ≫ ψ) χ +
    L2 F f T T' T''' φ (ψ ≫ χ) - mp F χ (L2 F f T T' T'' φ ψ)
  rw [dn2, cof_eq F (n := 2) 0 (mk₃ φ ψ χ) (mk₂ ψ χ) (face_zero_mk3 φ ψ χ) (𝟙 T''') HEq.rfl f,
    cof_eq F (n := 2) 1 (mk₃ φ ψ χ) (mk₂ (φ ≫ ψ) χ) (face_one_mk3 φ ψ χ) (𝟙 T''') HEq.rfl f,
    cof_eq F (n := 2) 2 (mk₃ φ ψ χ) (mk₂ φ (ψ ≫ χ)) (face_two_mk3 φ ψ χ) (𝟙 T''') HEq.rfl f,
    cof_eq F (n := 2) 3 (mk₃ φ ψ χ) (mk₂ φ ψ) (face_three_mk3 φ ψ χ) χ HEq.rfl f]
  show mp F (𝟙 T''') (f (mk₂ ψ χ)) - mp F (𝟙 T''') (f (mk₂ (φ ≫ ψ) χ)) +
    mp F (𝟙 T''') (f (mk₂ φ (ψ ≫ χ))) - mp F χ (f (mk₂ φ ψ)) = _
  rw [mp_id_apply F T''' (f (mk₂ ψ χ)), mp_id_apply F T''' (f (mk₂ (φ ≫ ψ) χ)),
    mp_id_apply F T''' (f (mk₂ φ (ψ ≫ χ)))]
  rfl

theorem dictSt : DictSt := by
  intro R _ C _ F
  refine ⟨LinearEquiv.ofBijective (L0 F) (L0_bijective_cochain F), LinearEquiv.ofBijective (L1 F) (L1_bijective_cochain F),
    LinearEquiv.ofBijective (L2 F) (L2_bijective_cochain F), LinearEquiv.ofBijective (L3 F) (L3_bijective_cochain F),
    fun _ _ => ?_, fun _ _ _ _ => ?_, fun _ _ _ _ _ _ => ?_, fun _ _ _ _ _ _ _ _ => ?_,
    fun f => ?_, fun f => ?_, fun f => ?_⟩ <;> simp only [LinearEquiv.ofBijective_apply]
  · rfl
  · rfl
  · rfl
  · rfl
  · exact L1_dn_zero_eq_d0_L0 F f
  · exact L2_dn_one_eq_d1_L1 F f
  · exact L3_dn_two_eq_d2_L2 F f

end GlobalTheory.CompanionTheory.Dict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineOpenFiniteType
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineOpenFiniteType
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoFT

theorem finiteType_affine {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType q] {W : X.Opens} (hW : IsAffineOpen W) :
    letI := (strV q W).toAlgebra; Algebra.FiniteType K Γ(X, W) := by
  have h1 : (q.appLE ⊤ W le_top).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) q inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2
  have h3 : (strV q W).FiniteType := by
    have : strV q W = (q.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom := rfl
    rw [this]
    exact h1.comp h2
  letI := (strV q W).toAlgebra
  exact RingHom.finiteType_algebraMap.1 h3

end GlobalTheory.CompanionTheory.GeoFT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineOpenFiniteTypeStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_open_finiteType : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType q] {W : X.Opens}, IsAffineOpen W → letI := (strV q W).toAlgebra; Algebra.FiniteType K Γ(X, W) := by
  first | exact @GlobalTheory.CompanionTheory.GeoFT.finiteType_affine | exact GlobalTheory.CompanionTheory.GeoFT.finiteType_affine | (intros; apply GlobalTheory.CompanionTheory.GeoFT.finiteType_affine <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartEmptyBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartEmptyBaseChange
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem toR_empty_bijective {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A]
    (C : ChartRings K A n d) : Function.Bijective (toR C ∅) := by
  have h : (toR C ∅ : A → C.R ∅) = C.base.symm := funext fun a => C.res_id ∅ _ _
  rw [h]
  exact C.base.symm.bijective

theorem theta_empty : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d),
    ∃ (θ : R0 K n d ∅ →ₐ[K] C.R ∅) (hθ : ∀ b, θ (poly n K ∅ b) = toR C ∅ (phi C b)),
      IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  intro K _ n d A _ _ C
  let e : Bp K n d ≃ₐ[K] R0 K n d ∅ := AlgEquiv.ofBijective (poly n K ∅) PolyBij.poly_bijective
  let θ : R0 K n d ∅ →ₐ[K] C.R ∅ := (toR C ∅).comp ((phi C).comp e.symm.toAlgHom)
  have hθ : ∀ b, θ (poly n K ∅ b) = toR C ∅ (phi C b) := fun b => by
    have hb : e.symm (poly n K ∅ b) = b := e.symm_apply_apply b
    change toR C ∅ (phi C (e.symm (poly n K ∅ b))) = _
    rw [hb]
  refine ⟨θ, hθ, ?_⟩
  let eM : Bp K n d ≃ₗ[Bp K n d] R0 K n d ∅ :=
    LinearEquiv.ofBijective (Algebra.linearMap (Bp K n d) (R0 K n d ∅)) PolyBij.poly_bijective
  let eN : Aa C ≃ₗ[Aa C] Rb C ∅ :=
    LinearEquiv.ofBijective (Algebra.linearMap (Aa C) (Rb C ∅)) (toR_empty_bijective C)
  refine (IsBaseChange.iff_of_equiv_comm (f := Algebra.linearMap (Bp K n d) (Aa C)) eM eN ?_).mp
    (IsBaseChange.linearMap (Bp K n d) (Aa C))
  refine LinearMap.ext fun b => ?_
  exact hθ b

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartEmptyBaseChangeStatement
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_empty_base_change : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d), ∃ (θ : R0 K n d ∅ →ₐ[K] C.R ∅) (hθ : ∀ b, θ (poly n K ∅ b) = toR C ∅ (phi C b)), IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty.theta_empty | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty.theta_empty | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty.theta_empty <;> assumption)
end
end

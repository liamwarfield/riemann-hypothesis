module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatUnitCocycleLocallyCoboundary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalTau

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFrameInvariantUnderDescentDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFrameInvariantUnderDescentDatum
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LBDescent

theorem twist_frame_descent : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ)
    (V : Y.Opens) (t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ), (∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j)) →
    ∀ (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ),
      (∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (𝟙 _) z _ c = gm (pullback.fst f f) z _ (t i) * gm (𝟙 _) z _ (φ i j) * (gm (pullback.snd f f) z _ (t j))⁻¹) →
    ∀ (V' : Y.Opens), V' ≤ V → ∀ u : Γ(X, f ⁻¹ᵁ V')ˣ, (∀ z : ↥(pullback f f), f (pullback.fst f f z) ∈ V' →
        gm (pullback.fst f f) z _ u * gm (𝟙 _) z _ c = gm (pullback.snd f f) z _ u) →
    ∃ s : ∀ i, Γ(X, f ⁻¹ᵁ V' ⊓ L.U i)ˣ,
      (∀ (i j : L.ι) (x : X), f x ∈ V' → x ∈ L.U i → x ∈ L.U j →
        gm (𝟙 X) x _ (s i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (s j)) ∧
      ∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V' → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (pullback.fst f f) z _ (s i) * gm (𝟙 _) z _ (φ i j) = gm (pullback.snd f f) z _ (s j) := by
  intro X Y f L φ V t ht c hc V' hV' u hu
  have h1 : ∀ i, f ⁻¹ᵁ V' ⊓ L.U i ≤ f ⁻¹ᵁ V' := fun i => inf_le_left
  have h2 : ∀ i, f ⁻¹ᵁ V' ⊓ L.U i ≤ f ⁻¹ᵁ V ⊓ L.U i := fun i =>
    inf_le_inf_right _ (fun x hx => hV' hx)
  refine ⟨fun i => res (h1 i) u * res (h2 i) (t i), ?_, ?_⟩
  · intro i j x hx hi hj
    have mi : (𝟙 X) x ∈ f ⁻¹ᵁ V' ⊓ L.U i := ⟨hx, hi⟩
    have mj : (𝟙 X) x ∈ f ⁻¹ᵁ V' ⊓ L.U j := ⟨hx, hj⟩
    rw [map_mul, map_mul, gm_res _ x _ mi, gm_res _ x _ mi, gm_res _ x _ mj, gm_res _ x _ mj,
      ht i j x (hV' hx) hi hj]
    exact mul_left_comm _ _ _
  · intro z i j hz hi hj
    have hfz : f (pullback.snd f f z) = f (pullback.fst f f z) := by
      have := congrArg (fun g => g z) (congrArg (fun g => g.base) (pullback.condition (f := f) (g := f)))
      simpa using this.symm
    have mi : pullback.fst f f z ∈ f ⁻¹ᵁ V' ⊓ L.U i := ⟨hz, hi⟩
    have mj : pullback.snd f f z ∈ f ⁻¹ᵁ V' ⊓ L.U j := ⟨show f (pullback.snd f f z) ∈ V' by rw [hfz]; exact hz, hj⟩
    rw [map_mul, map_mul, gm_res _ z _ mi, gm_res _ z _ mi, gm_res _ z _ mj, gm_res _ z _ mj, ← hu z hz,
      hc z i j (hV' hz) hi hj]
    group

end GlobalTheory.LBDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFrameInvariantUnderDescentDatumStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_frame_invariant_under_descentDatum : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ)
    (V : Y.Opens) (t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ), (∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j)) →
    ∀ (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ),
      (∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (𝟙 _) z _ c = gm (pullback.fst f f) z _ (t i) * gm (𝟙 _) z _ (φ i j) * (gm (pullback.snd f f) z _ (t j))⁻¹) →
    ∀ (V' : Y.Opens), V' ≤ V → ∀ u : Γ(X, f ⁻¹ᵁ V')ˣ, (∀ z : ↥(pullback f f), f (pullback.fst f f z) ∈ V' →
        gm (pullback.fst f f) z _ u * gm (𝟙 _) z _ c = gm (pullback.snd f f) z _ u) →
    ∃ s : ∀ i, Γ(X, f ⁻¹ᵁ V' ⊓ L.U i)ˣ,
      (∀ (i j : L.ι) (x : X), f x ∈ V' → x ∈ L.U i → x ∈ L.U j →
        gm (𝟙 X) x _ (s i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (s j)) ∧
      ∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V' → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (pullback.fst f f) z _ (s i) * gm (𝟙 _) z _ (φ i j) = gm (pullback.snd f f) z _ (s j) := by
  first | exact @GlobalTheory.LBDescent.twist_frame_descent | exact GlobalTheory.LBDescent.twist_frame_descent | (intros; apply GlobalTheory.LBDescent.twist_frame_descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleTrivialNearFibreFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleTrivialNearFibreFinite
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LBDescent

theorem exists_smul_mem_span_away {R S M : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [AddCommGroup M] [Module S M] [Module.Invertible S M]
    (p : Ideal R) [p.IsPrime] :
    ∃ r : R, r ∉ p ∧ ∃ m : M, ∀ x : M, ∃ a : S, algebraMap R S r • x = a • m := by
  classical
  let Q : Submonoid S := Algebra.algebraMapSubmonoid S p.primeCompl
  let T := Localization Q
  letI : Algebra (Localization.AtPrime p) T := localizationAlgebra p.primeCompl S
  haveI : Module.Finite (Localization.AtPrime p) T :=
    Module.Finite.of_isLocalization R S p.primeCompl
  haveI : Finite (MaximalSpectrum T) :=
    GlobalTheory.finite_maximalSpectrum_of_finite (Localization.AtPrime p) T
  obtain ⟨z, hz⟩ :=
    GlobalTheory.exists_bijective_toSpanSingleton_of_finite_maximalSpectrum T (LocalizedModule Q M)
  induction z using LocalizedModule.induction_on with
  | h m s =>
  have hloc : ∀ x : M, ∃ q ∈ Q, q • x ∈ Submodule.span S {m} := by
    intro x
    obtain ⟨c, hc⟩ := hz.2 (LocalizedModule.mk x 1)
    induction c using Localization.induction_on with
    | H c =>
    obtain ⟨a, t⟩ := c
    rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq] at hc
    obtain ⟨u, hu⟩ := hc
    refine ⟨(u : S) * ((t : S) * (s : S)), Q.mul_mem u.2 (Q.mul_mem t.2 s.2), ?_⟩
    rw [mul_smul, mul_smul]
    have hu' : (u : S) • (((t * s : Q) : S)) • x = (u : S) • ((1 : Q) : S) • a • m := hu.symm
    rw [Submonoid.coe_mul] at hu'
    rw [mul_smul] at hu'
    rw [hu', Submodule.mem_span_singleton]
    exact ⟨(u : S) * a, by simp [mul_smul]⟩
  choose q hqQ hq using hloc
  obtain ⟨F, hF⟩ := Module.Finite.fg_top (R := S) (M := M)
  let q₀ : S := ∏ x ∈ F, q x
  have hq₀ : q₀ ∈ Q := Q.prod_mem fun x _ => hqQ x
  have key : ∀ y ∈ Submodule.span S (F : Set M), q₀ • y ∈ Submodule.span S {m} := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      have : q₀ = (∏ x' ∈ F.erase x, q x') * q x := (Finset.prod_erase_mul F q hx).symm
      rw [this, mul_smul]
      exact Submodule.smul_mem _ _ (hq x)
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add y₁ y₂ _ _ h₁ h₂ => rw [smul_add]; exact Submodule.add_mem _ h₁ h₂
    | smul a y _ h => rw [smul_comm]; exact Submodule.smul_mem _ _ h
  obtain ⟨r, hr, hrq⟩ := hq₀
  refine ⟨r, hr, m, fun x => ?_⟩
  have := key x (hF ▸ Submodule.mem_top)
  rw [Submodule.mem_span_singleton] at this
  obtain ⟨a, ha⟩ := this
  exact ⟨a, by rw [hrq]; exact ha.symm⟩

theorem isFrame_res_of_smul_mem {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {U : X.Opens}
    (hU : IsAffineOpen U) (h : Γ(X, U)) (m : Γ(GlobalTheory.LB.toMod L, U))
    (hm : ∀ x : Γ(GlobalTheory.LB.toMod L, U), ∃ a : Γ(X, U), h • x = a • m) :
    GlobalTheory.LB.IsFrame ((GlobalTheory.LB.toMod L).presheaf.map (homOfLE (X.basicOpen_le h)).op m) := by
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hL
  have hD : IsAffineOpen (X.basicOpen h) := hU.basicOpen h
  haveI := GlobalTheory.LB.invertible_sections hL hD
  rw [GlobalTheory.LB.isFrame_iff_bijective hD]
  have h₁ := ((GlobalTheory.QCoh.isLocalizedModule_resBasicOpen_iff (GlobalTheory.LB.toMod L) h).1
    (GlobalTheory.QCoh.isLocalizedModule_resBasicOpen (GlobalTheory.LB.toMod L) hU h)).1
  refine Module.Invertible.bijective_of_surjective
    (f := LinearMap.toSpanSingleton Γ(X, X.basicOpen h) _
      ((GlobalTheory.LB.toMod L).presheaf.map (homOfLE (X.basicOpen_le h)).op m)) ?_
  intro s
  obtain ⟨n, t, ht⟩ := h₁ s
  obtain ⟨a, ha⟩ := hm t
  obtain ⟨u, hu⟩ := GlobalTheory.QCoh.isUnit_res_of_le_basicOpen h (X.basicOpen_le h) le_rfl
  have e1 := GlobalTheory.LB.map_smul_resG (F := GlobalTheory.LB.toMod L) (X.basicOpen_le h) h t
  rw [ha, GlobalTheory.LB.map_smul_resG] at e1
  refine ⟨((u⁻¹ : Γ(X, X.basicOpen h)ˣ) : Γ(X, X.basicOpen h)) ^ (n + 1) *
    resG X (X.basicOpen_le h) a, ?_⟩
  rw [← hu] at ht
  have hu' : resG X (X.basicOpen_le h) h = (u : Γ(X, X.basicOpen h)) := hu.symm
  rw [hu', ← ht, ← mul_smul] at e1
  rw [LinearMap.toSpanSingleton_apply, mul_smul, e1, ← mul_smul, ← pow_succ', ← mul_pow,
    Units.inv_mul, one_pow, one_smul]

theorem exists_trivial_near_fibre : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (L : LB X), L.IsLB →
    ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
    ∃ t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ, ∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j) := by
  intro X Y f _ L hL y
  obtain ⟨W, hW, hyW, -⟩ : ∃ W ∈ Y.affineOpens, y ∈ W ∧ W ≤ ⊤ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
    (show y ∈ (⊤ : Y.Opens) from trivial)
  let p : Ideal Γ(Y, W) :=
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).comap (Y.presheaf.germ W y hyW).hom
  letI : Algebra Γ(Y, W) Γ(X, f ⁻¹ᵁ W) := (f.app W).hom.toAlgebra
  haveI : Module.Finite Γ(Y, W) Γ(X, f ⁻¹ᵁ W) := f.finite_app W hW
  have hW : IsAffineOpen W := hW
  have hU : IsAffineOpen (f ⁻¹ᵁ W) := hW.preimage f
  haveI := GlobalTheory.LB.invertible_sections hL hU
  obtain ⟨r, hr, m, hm⟩ := exists_smul_mem_span_away (R := Γ(Y, W)) (S := Γ(X, f ⁻¹ᵁ W))
    (M := Γ(GlobalTheory.LB.toMod L, f ⁻¹ᵁ W)) p
  have he := isFrame_res_of_smul_mem hL hU (f.app W r) m hm
  have hpre : f ⁻¹ᵁ Y.basicOpen r = X.basicOpen (f.app W r) := Scheme.preimage_basicOpen f r
  refine ⟨Y.basicOpen r, ?_, ?_⟩
  · rw [Scheme.mem_basicOpen (x := y) (hx := hyW)]
    by_contra hn
    exact hr ((IsLocalRing.mem_maximalIdeal _).2 hn)
  let F := GlobalTheory.LB.toMod L
  let e : Γ(F, f ⁻¹ᵁ Y.basicOpen r) :=
    F.presheaf.map (homOfLE hpre.le).op (F.presheaf.map (homOfLE (X.basicOpen_le _)).op m)
  have he' : GlobalTheory.LB.IsFrame e := he.map hpre.le
  let u : ∀ i, Γ(X, f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i)ˣ := fun i =>
    (GlobalTheory.LB.isFrame_chartSec hL i).unit he' inf_le_right inf_le_left
  have hu : ∀ i, ((u i : Γ(X, f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i)ˣ) : Γ(X, f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i)) =
      GlobalTheory.LB.coord e i := fun i => by
    rw [GlobalTheory.LB.IsFrame.val_unit]
    apply GlobalTheory.LB.IsFrame.repr_eq
    apply Subtype.ext
    funext j
    change GlobalTheory.LB.coord (GlobalTheory.LB.coord e i •
      (GlobalTheory.LB.toMod L).presheaf.map (homOfLE inf_le_right).op
        (GlobalTheory.LB.chartSec hL i)) j =
      GlobalTheory.LB.coord ((GlobalTheory.LB.toMod L).presheaf.map
        (homOfLE inf_le_left).op e) j
    simp only [GlobalTheory.LB.coord_smul, GlobalTheory.LB.coord_map,
      GlobalTheory.LB.coord_chartSec, GlobalTheory.LB.resG_resG]
    rw [mul_comm]
    exact (GlobalTheory.LB.coord_rel e j i _ _ _).symm
  refine ⟨u, fun i j x hxV hi hj => ?_⟩
  have hxO : x ∈ f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j := ⟨⟨hxV, hi⟩, hj⟩
  rw [← gm_res (𝟙 X) x (inf_le_left : f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j ≤ _) hxO,
    ← gm_res (𝟙 X) x (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j ≤ L.U i ⊓ L.U j) hxO,
    ← gm_res (𝟙 X) x (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      f ⁻¹ᵁ Y.basicOpen r ⊓ L.U i ⊓ L.U j ≤ f ⁻¹ᵁ Y.basicOpen r ⊓ L.U j) hxO, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, hu, hu]
  exact GlobalTheory.LB.coord_rel e i j _ _ _

end GlobalTheory.LBDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleTrivialNearFibreFiniteStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_trivial_near_fibre_finite : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (L : LB X), L.IsLB → ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
    ∃ t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ, ∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j) := by
  first | exact @GlobalTheory.LBDescent.exists_trivial_near_fibre | exact GlobalTheory.LBDescent.exists_trivial_near_fibre | (intros; apply GlobalTheory.LBDescent.exists_trivial_near_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentDatumFrameCocycleUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentDatumFrameCocycleUnit
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

set_option autoImplicit false

namespace GlobalTheory.LBDescent

private theorem alg {G : Type*} [CommGroup G] (a P b G₁ G₃ : G) :
    a * P * b⁻¹ = G₁ * a * (G₁⁻¹ * P * G₃) * (G₃⁻¹ * b⁻¹) := by
  rw [mul_comm G₁ a]; group

theorem frame_cocycle {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (hL : L.IsLB)
    (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) (hC : DescCompat f L φ) (hK : DescCocycle f L φ)
    (V : Y.Opens) (t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ) (ht : ∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j)) :
    ∃ c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ,
      (∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (𝟙 _) z _ c = gm (pullback.fst f f) z _ (t i) * gm (𝟙 _) z _ (φ i j) * (gm (pullback.snd f f) z _ (t j))⁻¹) ∧
      ∀ w : ↥(Triple f), f (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w)) ∈ V →
        gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ c *
          gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ c = gm (pr13 f) w _ c := by

  have hf : ∀ z : ↥(pullback f f), f (pullback.snd f f z) = f (pullback.fst f f z) := fun z => by
    change (pullback.snd f f ≫ f) z = (pullback.fst f f ≫ f) z
    rw [pullback.condition]
  set V' : (pullback f f).Opens := pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V with hV'
  let W : L.ι × L.ι → (pullback f f).Opens := fun p => chart f L p.1 p.2 ⊓ V'
  have le1 : ∀ p : L.ι × L.ι, W p ≤ pullback.fst f f ⁻¹ᵁ (f ⁻¹ᵁ V ⊓ L.U p.1) :=
    fun p z hz => ⟨hz.2, hz.1.1⟩
  have le2 : ∀ p : L.ι × L.ι, W p ≤ chart f L p.1 p.2 := fun p => inf_le_left
  have le3 : ∀ p : L.ι × L.ι, W p ≤ pullback.snd f f ⁻¹ᵁ (f ⁻¹ᵁ V ⊓ L.U p.2) :=
    fun p z hz => ⟨show f (pullback.snd f f z) ∈ V by rw [hf]; exact hz.2, hz.1.2⟩
  let u : ∀ p, Γ(pullback f f, W p)ˣ := fun p =>
    res (le1 p) (pullU (pullback.fst f f) _ (t p.1)) * res (le2 p) (φ p.1 p.2) *
      (res (le3 p) (pullU (pullback.snd f f) _ (t p.2)))⁻¹
  have key : ∀ {T : Scheme.{0}} (h : T ⟶ pullback f f) (y : T) (p : L.ι × L.ι) (hy : h y ∈ W p),
      gm h y (W p) (u p) = gm (h ≫ pullback.fst f f) y _ (t p.1) * gm h y _ (φ p.1 p.2) *
        (gm (h ≫ pullback.snd f f) y _ (t p.2))⁻¹ := by
    intro T h y p hy
    simp only [u, map_mul, map_inv]
    rw [gm_res h y (le1 p) hy, gm_res h y (le2 p) hy, gm_res h y (le3 p) hy,
      gm_pull h (pullback.fst f f) y _ (le1 p hy), gm_pull h (pullback.snd f f) y _ (le3 p hy)]

  have tpull : ∀ {T : Scheme.{0}} (h : T ⟶ X) (y : T) (i j : L.ι), f (h y) ∈ V → h y ∈ L.U i → h y ∈ L.U j →
      gm h y _ (t i) = gm h y _ (L.g i j) * gm h y _ (t j) := by
    intro T h y i j hV hi hj
    have hle1 : f ⁻¹ᵁ V ⊓ (L.U i ⊓ L.U j) ≤ f ⁻¹ᵁ V ⊓ L.U i := inf_le_inf_left _ inf_le_left
    have hle2 : f ⁻¹ᵁ V ⊓ (L.U i ⊓ L.U j) ≤ L.U i ⊓ L.U j := inf_le_right
    have hle3 : f ⁻¹ᵁ V ⊓ (L.U i ⊓ L.U j) ≤ f ⁻¹ᵁ V ⊓ L.U j := inf_le_inf_left _ inf_le_right
    have e : res hle1 (t i) = res hle2 (L.g i j) * res hle3 (t j) := by
      apply unit_ext
      intro x hx
      rw [map_mul, gm_res _ x hle1 hx, gm_res _ x hle2 hx, gm_res _ x hle3 hx]
      exact ht i j x hx.1 hx.2.1 hx.2.2
    have hm : h y ∈ f ⁻¹ᵁ V ⊓ (L.U i ⊓ L.U j) := ⟨hV, hi, hj⟩
    have := congrArg (gm h y _) e
    rwa [map_mul, gm_res h y hle1 hm, gm_res h y hle2 hm, gm_res h y hle3 hm] at this
  have hW : ∀ p, W p ≤ V' := fun p => inf_le_right
  have hcov : V' ≤ iSup W := by
    intro z hz
    obtain ⟨i, hi⟩ := exists_chart hL (pullback.fst f f z)
    obtain ⟨j, hj⟩ := exists_chart hL (pullback.snd f f z)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), ⟨hi, hj⟩, hz⟩
  have hagree : ∀ p q, ∀ x ∈ W p ⊓ W q, gm (𝟙 _) x (W p) (u p) = gm (𝟙 _) x (W q) (u q) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ x ⟨hp, hq⟩
    rw [key (𝟙 _) x _ hp, key (𝟙 _) x _ hq]
    simp only [Category.id_comp]
    have hx1 : f (pullback.fst f f x) ∈ V := hp.2
    have hx2 : f (pullback.snd f f x) ∈ V := by rw [hf]; exact hx1
    rw [tpull (pullback.fst f f) x i' i hx1 hq.1.1 hp.1.1, tpull (pullback.snd f f) x j' j hx2 hq.1.2 hp.1.2,
      hC x i i' j j' hp.1.1 hq.1.1 hp.1.2 hq.1.2]
    have hg : gm (pullback.fst f f) x _ (L.g i' i) * gm (pullback.fst f f) x _ (L.g i i') = 1 := by
      rw [gm_cocycle hL _ x hq.1.1 hp.1.1 hq.1.1, gm_self hL _ x hq.1.1]
    rw [eq_inv_of_mul_eq_one_right hg, mul_inv]
    exact alg _ _ _ _ _
  obtain ⟨c, hc⟩ := glue_unit V' W hW hcov u hagree
  have cgerm : ∀ {T : Scheme.{0}} (h : T ⟶ pullback f f) (y : T) (p : L.ι × L.ι) (hy : h y ∈ W p),
      gm h y V' c = gm (h ≫ pullback.fst f f) y _ (t p.1) * gm h y _ (φ p.1 p.2) *
        (gm (h ≫ pullback.snd f f) y _ (t p.2))⁻¹ := by
    intro T h y p hy
    rw [← key h y p hy, ← hc p, gm_res h y (hW p) hy]
  refine ⟨c, ?_, ?_⟩
  · intro z i j hV hi hj
    have := cgerm (𝟙 _) z (i, j) ⟨⟨hi, hj⟩, hV⟩
    simpa only [Category.id_comp] using this
  · intro w hV
    set q₁ := pullback.fst (pullback.snd f f) (pullback.fst f f)
    set q₂ := pullback.snd (pullback.snd f f) (pullback.fst f f)
    have hmid : q₁ ≫ pullback.snd f f = q₂ ≫ pullback.fst f f := pullback.condition
    have h13a : pr13 f ≫ pullback.fst f f = q₁ ≫ pullback.fst f f := by unfold pr13; exact pullback.lift_fst _ _ _
    have h13b : pr13 f ≫ pullback.snd f f = q₂ ≫ pullback.snd f f := by unfold pr13; exact pullback.lift_snd _ _ _
    have pmid : pullback.snd f f (q₁ w) = pullback.fst f f (q₂ w) := by
      change (q₁ ≫ pullback.snd f f) w = (q₂ ≫ pullback.fst f f) w
      rw [hmid]
    have p13a : pullback.fst f f (pr13 f w) = pullback.fst f f (q₁ w) := by
      change (pr13 f ≫ pullback.fst f f) w = (q₁ ≫ pullback.fst f f) w
      rw [h13a]
    have p13b : pullback.snd f f (pr13 f w) = pullback.snd f f (q₂ w) := by
      change (pr13 f ≫ pullback.snd f f) w = (q₂ ≫ pullback.snd f f) w
      rw [h13b]
    obtain ⟨i, hi⟩ := exists_chart hL (pullback.fst f f (q₁ w))
    obtain ⟨j, hj⟩ := exists_chart hL (pullback.snd f f (q₁ w))
    obtain ⟨k, hk⟩ := exists_chart hL (pullback.snd f f (q₂ w))
    have hV2 : f (pullback.fst f f (q₂ w)) ∈ V := by rw [← pmid, hf]; exact hV
    have hV3 : f (pullback.fst f f (pr13 f w)) ∈ V := by rw [p13a]; exact hV
    have m1 : q₁ w ∈ W (i, j) := ⟨⟨hi, hj⟩, hV⟩
    have m2 : q₂ w ∈ W (j, k) := ⟨⟨show pullback.fst f f (q₂ w) ∈ L.U j by rw [← pmid]; exact hj, hk⟩, hV2⟩
    have m3 : pr13 f w ∈ W (i, k) := ⟨⟨show pullback.fst f f (pr13 f w) ∈ L.U i by rw [p13a]; exact hi,
      show pullback.snd f f (pr13 f w) ∈ L.U k by rw [p13b]; exact hk⟩, hV3⟩
    rw [cgerm q₁ w (i, j) m1, cgerm q₂ w (j, k) m2, cgerm (pr13 f) w (i, k) m3, hmid, h13a, h13b,
      ← hK w i j k hi hj hk]
    dsimp only
    simp only [q₁, q₂]
    group

end GlobalTheory.LBDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentDatumFrameCocycleUnitStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descentDatum_frame_cocycle_unit : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X), L.IsLB →
    ∀ (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ), DescCompat f L φ → DescCocycle f L φ →
    ∀ (V : Y.Opens) (t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ), (∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j)) →
    ∃ c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ,
      (∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (𝟙 _) z _ c = gm (pullback.fst f f) z _ (t i) * gm (𝟙 _) z _ (φ i j) * (gm (pullback.snd f f) z _ (t j))⁻¹) ∧
      ∀ w : ↥(Triple f), f (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w)) ∈ V →
        gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ c *
          gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ c = gm (pr13 f) w _ c := by
  first | exact @GlobalTheory.LBDescent.frame_cocycle | exact GlobalTheory.LBDescent.frame_cocycle | (intros; apply GlobalTheory.LBDescent.frame_cocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleOfDescentInvariantFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleOfDescentInvariantFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

set_option autoImplicit false

namespace GlobalTheory.LBDescent

private theorem ratio_eq {G : Type} [CommGroup G] (A B C D g : G) (h1 : A = g * B) (h2 : C = g * D) :
    C * A⁻¹ = D * B⁻¹ := by
  subst h1 h2; rw [mul_inv_rev, mul_comm g D, _root_.mul_assoc, mul_inv_cancel_comm_assoc]

private theorem ratio_mul {G : Type} [CommGroup G] (A B C : G) : (B * A⁻¹) * (C * B⁻¹) = C * A⁻¹ := by
  rw [mul_comm (B * A⁻¹), _root_.mul_assoc, inv_mul_cancel_left]

private theorem ratio_inv {G : Type} [CommGroup G] (A S g T : G) (h : S = g * T) :
    A⁻¹ = S * A⁻¹ * g⁻¹ * T⁻¹ := by
  rw [_root_.mul_assoc _ g⁻¹, ← mul_inv, ← h, mul_inv_cancel_comm]

theorem exists_lb_of_invariant_frames : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [Flat f] [Surjective f] (L : LB X), L.IsLB →
    ∀ (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ),
    (∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ s : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ,
      (∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
        gm (𝟙 X) x _ (s i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (s j)) ∧
      ∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (pullback.fst f f) z _ (s i) * gm (𝟙 _) z _ (φ i j) = gm (pullback.snd f f) z _ (s j)) →
    ∃ L' : LB Y, L'.IsLB ∧ LBIso L (L'.pull f) := by
  intro X Y f _ _ _ L hL φ H
  choose V hV s hs1 hs2 using H
  have hW : ∀ a b i, f ⁻¹ᵁ (V a ⊓ V b) ⊓ L.U i ≤ f ⁻¹ᵁ (V a ⊓ V b) := fun a b i => inf_le_left
  have lb : ∀ a b i, f ⁻¹ᵁ (V a ⊓ V b) ⊓ L.U i ≤ f ⁻¹ᵁ V b ⊓ L.U i := fun a b i x hx => ⟨hx.1.2, hx.2⟩
  have la : ∀ a b i, f ⁻¹ᵁ (V a ⊓ V b) ⊓ L.U i ≤ f ⁻¹ᵁ V a ⊓ L.U i := fun a b i x hx => ⟨hx.1.1, hx.2⟩
  have hex : ∀ a b, ∃ t : Γ(X, f ⁻¹ᵁ (V a ⊓ V b))ˣ, ∀ i,
      res (hW a b i) t = res (lb a b i) (s b i) * (res (la a b i) (s a i))⁻¹ := by
    intro a b
    refine glue_unit _ _ (hW a b) ?_ _ ?_
    · intro x hx
      obtain ⟨i, hi⟩ := exists_chart hL x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hx, hi⟩
    · intro i j x hx
      simp only [map_mul, map_inv]
      rw [gm_res _ x (lb a b i) hx.1, gm_res _ x (la a b i) hx.1, gm_res _ x (lb a b j) hx.2,
        gm_res _ x (la a b j) hx.2]
      exact ratio_eq _ _ _ _ _ (hs1 a i j x hx.1.1.1 hx.1.2 hx.2.2) (hs1 b i j x hx.1.1.2 hx.1.2 hx.2.2)
  choose t ht using hex
  have tform : ∀ a b {Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) (i : L.ι), f (g z) ∈ V a → f (g z) ∈ V b →
      g z ∈ L.U i → gm g z _ (t a b) = gm g z _ (s b i) * (gm g z _ (s a i))⁻¹ := by
    intro a b Z g z i ha hb hi
    have hm : g z ∈ f ⁻¹ᵁ (V a ⊓ V b) ⊓ L.U i := ⟨⟨ha, hb⟩, hi⟩
    rw [← gm_res g z (hW a b i) hm, ht a b i, map_mul, map_inv, gm_res g z (lb a b i) hm,
      gm_res g z (la a b i) hm]
  have hk : ∀ a b, ∃ k : Γ(Y, V a ⊓ V b)ˣ, pullU f _ k = t a b := by
    intro a b
    refine GlobalTheory.FlatDescent.exists_unit_of_gm_eq f (IsPullback.of_hasPullback f f) _ _ fun z hz => ?_
    obtain ⟨i, hi⟩ := exists_chart hL (pullback.fst f f z)
    obtain ⟨j, hj⟩ := exists_chart hL (pullback.snd f f z)
    have e : f (pullback.snd f f z) = f (pullback.fst f f z) :=
      congrArg (fun q : pullback f f ⟶ Y => q z) pullback.condition.symm
    rw [tform a b _ z i hz.1 hz.2 hi, tform a b _ z j (e ▸ hz.1) (e ▸ hz.2) hj,
      ← hs2 a z i j hz.1 hi hj, ← hs2 b z i j hz.2 hi hj]
    group
  choose k hk using hk
  have kform : ∀ a b (x : X) (i : L.ι), f x ∈ V a → f x ∈ V b → x ∈ L.U i →
      gm f x (V a ⊓ V b) (k a b) = gm (𝟙 X) x _ (s b i) * (gm (𝟙 X) x _ (s a i))⁻¹ := by
    intro a b x i ha hb hi
    have := gm_pull (𝟙 X) f x (V a ⊓ V b) ⟨ha, hb⟩ (k a b)
    rw [Category.id_comp, hk] at this
    rw [← this]
    exact tform a b (𝟙 X) x i ha hb hi
  have hL' : LB.IsLB (⟨Y, V, k⟩ : LB Y) := by
    refine ⟨?_, fun a => ?_, fun a b c => ?_⟩
    · exact eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hV y⟩
    · refine GlobalTheory.FlatDescent.unit_ext_of_flat f fun x hx => ?_
      obtain ⟨i, hi⟩ := exists_chart hL x
      rw [gm_res f x _ hx, map_one]
      exact (kform a a x i hx hx hi).trans (mul_inv_cancel _)
    · refine GlobalTheory.FlatDescent.unit_ext_of_flat f fun x hx => ?_
      obtain ⟨i, hi⟩ := exists_chart hL x
      rw [map_mul, gm_res f x _ hx, gm_res f x _ hx, gm_res f x _ hx]
      exact ((congrArg₂ (· * ·) (kform a b x i hx.1.1 hx.1.2 hi) (kform b c x i hx.1.2 hx.2 hi)).trans
        (ratio_mul _ _ _)).trans (kform a c x i hx.1.1 hx.2 hi).symm
  have le1 : ∀ (J : PUnit → Y) (i : L.ι), ((⟨Y, V, k⟩ : LB Y).pull f).U J ⊓ L.U i ≤ f ⁻¹ᵁ V (J PUnit.unit) ⊓ L.U i :=
    fun J i x hx => ⟨mem_pull.1 hx.1, hx.2⟩
  refine ⟨⟨Y, V, k⟩, hL', ⟨fun p => (res (le1 p.1 p.2) (s (p.1 PUnit.unit) p.2))⁻¹⟩, ?_⟩
  rintro ⟨J, i⟩ ⟨J', i'⟩
  apply unit_ext
  intro x hx
  have hj := mem_pull.1 hx.1.1
  have hj' := mem_pull.1 hx.2.1
  have d := gm_div_g (L := (⟨Y, V, k⟩ : LB Y)) (L' := L) (F := f) (𝟙 X) x (J PUnit.unit) (J' PUnit.unit) i i'
    hj hj' hx.1.2 hx.2.2
  rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx]
  erw [d]
  erw [map_inv, map_inv, gm_res (𝟙 X) x (le1 J i) (show x ∈ ((⟨Y, V, k⟩ : LB Y).pull f).U J ⊓ L.U i from hx.1),
    gm_res (𝟙 X) x (le1 J' i') (show x ∈ ((⟨Y, V, k⟩ : LB Y).pull f).U J' ⊓ L.U i' from hx.2)]
  rw [Category.id_comp]
  erw [kform (J PUnit.unit) (J' PUnit.unit) x i hj hj' hx.1.2]
  exact ratio_inv _ _ _ _ (hs1 (J' PUnit.unit) i i' x hj' hx.1.2 hx.2.2)
end GlobalTheory.LBDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleOfDescentInvariantFramesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_of_descentInvariant_frames : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [Flat f] [Surjective f] (L : LB X), L.IsLB →
    ∀ (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ),
    (∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ s : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ,
      (∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
        gm (𝟙 X) x _ (s i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (s j)) ∧
      ∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (pullback.fst f f) z _ (s i) * gm (𝟙 _) z _ (φ i j) = gm (pullback.snd f f) z _ (s j)) →
    ∃ L' : LB Y, L'.IsLB ∧ LBIso L (L'.pull f) := by
  first | exact @GlobalTheory.LBDescent.exists_lb_of_invariant_frames | exact GlobalTheory.LBDescent.exists_lb_of_invariant_frames | (intros; apply GlobalTheory.LBDescent.exists_lb_of_invariant_frames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleDescentFiniteFlat
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBDescent

theorem exists_descent : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian Y] (L : LB X), L.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, GlobalTheory.LBDescent.chart f L i j)ˣ), GlobalTheory.LBDescent.DescCompat f L φ → GlobalTheory.LBDescent.DescCocycle f L φ → ∃ L' : LB Y, L'.IsLB ∧ LBIso L (L'.pull f) := by
  intro X Y f _ _ _ _ L hL φ hc hcoc
  refine GlobalTheory.T.exists_lineBundle_of_descentInvariant_frames f L hL φ fun y => ?_
  obtain ⟨V, hy, t, ht⟩ := GlobalTheory.T.exists_lineBundle_trivial_near_fibre_finite f L hL y
  obtain ⟨c, hct, hcc⟩ := GlobalTheory.T.descentDatum_frame_cocycle_unit f L hL φ hc hcoc V t ht
  obtain ⟨V', hle, hy', u, hu⟩ := GlobalTheory.T.finiteFlat_unitCocycle_locally_coboundary f V c hcc y hy
  exact ⟨V', hy', GlobalTheory.T.twisted_frame_invariant_under_descentDatum f L φ V t ht c hct V' hle u hu⟩

end GlobalTheory.LBDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleDescentFiniteFlatStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_descent_finiteFlat : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian Y] (L : LB X), L.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, GlobalTheory.LBDescent.chart f L i j)ˣ), GlobalTheory.LBDescent.DescCompat f L φ → GlobalTheory.LBDescent.DescCocycle f L φ → ∃ L' : LB Y, L'.IsLB ∧ LBIso L (L'.pull f) := by
  first | exact @GlobalTheory.LBDescent.exists_descent | exact GlobalTheory.LBDescent.exists_descent | (intros; apply GlobalTheory.LBDescent.exists_descent <;> assumption)
end

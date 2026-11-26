module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfDiv
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameFreeFiniteOrderRuleConstPeriodSpace

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifCompareIsogeny
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifCompareIsogeny
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HodgeUniq

open GlobalTheory.CompanionTheory.Ar.Flat.PerGram

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A']

theorem isDiff_comp {M : LB A.left} {M' : LB A'.left} {g g' : ℕ} (u : HolUnif A M g) (u' : HolUnif A' M' g')
    (d₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) (f : A' ⟶ A) (F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u.ex (F z) = u'.ex z ≫ f) {a' : Fin g' → ℂ} {x' : epsR ℂ ⟶ A'} (ht : IsTangent x')
    (hd : u'.IsDiff a' x') : u.IsDiff (F a') (x' ≫ f) := by
  obtain ⟨t, ⟨h₁, h₂⟩, -⟩ := d₂ (F a')
  have a1 := isDerivAt0_comp_linMap (isHolTo_ex u) F (isDerivAt0_of_isDiff u h₁ h₂)
  have a2 := GlobalTheory.FibreDeriv.isDerivAt0_comp (isDerivAt0_of_isDiff u' ht hd) f.left
  rw [show (fun z => (u.ex (F z)).left) = fun z => (u'.ex z).left ≫ f.left from
    funext fun z => by rw [hF, Over.comp_left]] at a1
  have e : t = x' ≫ f := Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique a1 a2)
  exact e ▸ h₂

theorem tangent_of_iso (e : A' ≅ A) [IsMonHom e.hom] {x : epsR ℂ ⟶ A} {x' : epsR ℂ ⟶ A'} (hx : IsTangent x)
    (h : x' ≫ e.hom = x) : IsTangent x' := by
  have h' : x' = x ≫ e.inv := by rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]
  have h₁ : η[A'] ≫ e.hom = η[A] := IsMonHom.one_hom e.hom
  have h₂ : η[A] ≫ e.inv = η[A'] := by rw [← h₁, Category.assoc, e.hom_inv_id, Category.comp_id]
  unfold IsTangent at hx ⊢
  rw [h', Over.comp_left, ← Category.assoc, hx, ← Over.comp_left, h₂]

theorem hermForm_eq_of_pullbacks : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (L : LB G.left) (z : Spec (CommRingCat.of ℂ) ⟶ X) (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (φ : A.left ⟶ G.left) (φ' : A'.left ⟶ G.left) (g g' : ℕ) (u : HolUnif A (L.pull φ) g) (u' : HolUnif A' (L.pull φ') g') (Hm : Matrix (Fin g) (Fin g) ℂ) (Hm' : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (χ' : u'.Λ → ℂ), L.IsLB → IsAbelianScheme A → IsGrpPullback A G z φ → IsGrpPullback A' G z φ' → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → u.IsAH Hm χ → u'.IsAH Hm' χ' → ∀ (x y : epsR ℂ ⟶ A) (x' y' : epsR ℂ ⟶ A') (a b : Fin g → ℂ) (a' b' : Fin g' → ℂ), IsTangent x → IsTangent y → x'.left ≫ φ' = x.left ≫ φ → y'.left ≫ φ' = y.left ≫ φ → u.IsDiff a x → u.IsDiff b y → u'.IsDiff a' x' → u'.IsDiff b' y' → hermForm Hm' a' b' = hermForm Hm a b := by
  intro X G _ L z A A' _ _ φ φ' g g' u u' Hm Hm' χ χ' hL hAb hp hp' d₁ d₂ hAH hAH' x y x' y' a b a' b' hx hy hxx hyy
    da db da' db'
  obtain ⟨e, hmon, he⟩ := grpPullback_iso hp' hp
  haveI := hmon
  have hol : IsHolTo (Set.univ : Set (Fin g' → ℂ)) (fun w => (u'.ex w ≫ e.hom).left) := by
    simpa only [Over.comp_left] using GlobalTheory.HolTorsion.isHolTo_comp (isHolTo_ex u') e.hom.left
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hAb (L.pull φ) g g' u d₁ d₂
    (fun w => u'.ex w ≫ e.hom) (fun p q => by rw [u'.ex_add, MonObj.mul_comp]) hol
  have hΛ : ∀ l ∈ u'.Λ, F l ∈ u.Λ := fun l hl => (u.ker _).1 (by
    rw [hF, (u'.ker l).2 hl, MonObj.one_comp])
  have iso : LBIso (lbPow (L.pull φ') 1) (lbPow ((L.pull φ).pull e.hom.left) 1) :=
    GlobalTheory.lbIso_lbPow (GlobalTheory.GenSpread.lbIso_pull_pull hL e.hom.left he.symm) 1
  have hH := (GlobalTheory.appellHumbert_data_eq_of_lbIso_pow_pull A' A (L.pull φ') (L.pull φ) g' g u' u Hm' Hm χ' χ e.hom F hΛ 1
    one_pos (pull_isLB hL φ') (pull_isLB hL φ) hAH' hAH hF iso).1
  have coord : ∀ (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A') (c : Fin g → ℂ) (c' : Fin g' → ℂ), IsTangent v →
      v'.left ≫ φ' = v.left ≫ φ → u.IsDiff c v → u'.IsDiff c' v' → F c' = c := fun v v' c c' hv hvv dc dc' => by
    have h : v' ≫ e.hom = v := Over.OverMorphism.ext (hp.1.hom_ext
      (by rw [Over.comp_left, Category.assoc, he, hvv]) (by rw [Over.w, Over.w]))
    have ht := tangent_of_iso e hv h
    exact (d₁ v hv).unique (h ▸ isDiff_comp u u' d₂ e.hom F hF ht dc') dc
  rw [hH, coord x x' a a' hx hxx da da', coord y y' b b' hy hyy db db']

end GlobalTheory.CompanionTheory.Ar.HodgeUniq
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifCompareIsogenyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hol_unif_compare_isogeny : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (L : LB G.left) (z : Spec (CommRingCat.of ℂ) ⟶ X) (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (φ : A.left ⟶ G.left) (φ' : A'.left ⟶ G.left) (g g' : ℕ) (u : HolUnif A (L.pull φ) g) (u' : HolUnif A' (L.pull φ') g') (Hm : Matrix (Fin g) (Fin g) ℂ) (Hm' : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (χ' : u'.Λ → ℂ), L.IsLB → IsAbelianScheme A → IsGrpPullback A G z φ → IsGrpPullback A' G z φ' → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → u.IsAH Hm χ → u'.IsAH Hm' χ' → ∀ (x y : epsR ℂ ⟶ A) (x' y' : epsR ℂ ⟶ A') (a b : Fin g → ℂ) (a' b' : Fin g' → ℂ), IsTangent x → IsTangent y → x'.left ≫ φ' = x.left ≫ φ → y'.left ≫ φ' = y.left ≫ φ → u.IsDiff a x → u.IsDiff b y → u'.IsDiff a' x' → u'.IsDiff b' y' → hermForm Hm' a' b' = hermForm Hm a b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeUniq.hermForm_eq_of_pullbacks | exact GlobalTheory.CompanionTheory.Ar.HodgeUniq.hermForm_eq_of_pullbacks | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeUniq.hermForm_eq_of_pullbacks <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPeriodRiemannLattice
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPeriodRiemannLattice
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FibreAtPeriod

section Reparam

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left}

theorem exists_reparam_isAH {g g' : ℕ} (u : HolUnif A L g') (X : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ))
    (Hm : Matrix (Fin g') (Fin g') ℂ) (Hf : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (hAH : u.IsAH Hm χ)
    (hHf : Hf.IsHermitian) (hf : ∀ x y, hermForm Hf x y = hermForm Hm (X x) (X y)) :
    ∃ (u₂ : HolUnif A L g) (χ₂ : u₂.Λ → ℂ), (∀ z, u₂.ex z = u.ex (X z)) ∧ (∀ z, z ∈ u₂.Λ ↔ X z ∈ u.Λ) ∧
      u₂.IsAH Hf χ₂ ∧ ∀ w v, u.IsDiff (X w) v → u₂.IsDiff w v := by
  have hg : g = g' := by simpa using X.finrank_eq
  subst hg
  refine ⟨GlobalTheory.holUnifReparam u X (fun _ => 1) (differentiable_const _) (fun _ => one_ne_zero),
    fun l => χ ⟨X l, l.2⟩, fun _ => rfl, fun _ => Iff.rfl, ⟨hHf, ?_, fun l => hAH.2.2.1 _, ?_⟩, ?_⟩
  · intro z hz
    have h := hAH.2.1 (X z) ((LinearEquiv.map_ne_zero_iff X).2 hz)
    have e := hf z z
    unfold hermForm at e
    rw [e]
    exact h
  · intro l i z hz
    have h := hAH.2.2.2 ⟨X l, l.2⟩ i (X z) hz
    have e1 := hf z l
    have e2 := hf l l
    unfold hermForm at e1 e2
    show u.fr i (X z) / 1 = χ ⟨X l, l.2⟩ * Complex.exp (Real.pi * (z ⬝ᵥ Hf.mulVec (star (l : Fin g → ℂ))) +
      Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hf.mulVec (star (l : Fin g → ℂ)))) * (u.fr i (X (z + l)) / 1)
    rw [div_one, div_one, map_add (f := _), h, e1, e2]
  · intro w v hv U h f
    rw [hv U h f]
    have key := X.toContinuousLinearEquiv.comp_right_fderiv
      (f := fun z => valAt' (u.ex z).left U f) (x := 0)
    have h2 := congrArg (fun T => T w) key
    simp only [map_zero] at h2
    exact h2.symm

end Reparam

theorem fibreLatVec_of_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (R : RiemLat E g (FU.Di i).La) (P : (FU.Di i).La →+ (Fin g → ℂ)) (h : Matrix (Fin g) (Fin g) ℂ), IsPeriod (FU.Di i) ty P → R.form = (FU.Di i).EF → IsUnit h.det → (∀ x, P x = h *ᵥ R.P x) → ∀ (A₀ : Type) (x : A₀ → Fin g → ℂ) (v : A₀ → (epsAt (FU.u i P) ⟶ Xo.univ.t.G)), (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (h *ᵥ x a) (v a).left) → FibreLatVec Xo.univ.t (FU.u i P) R x v := by
  intro E _ _ _ H D l Xo σ g ty FU i R P h hP hRf hdet hPh A₀ x v hd
  let hl : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := h.toLinearEquiv' (h.invertibleOfIsUnitDet hdet)
  have hla : ∀ z, hl z = h *ᵥ z := fun z => by
    show Matrix.toLin' h z = h *ᵥ z
    exact Matrix.toLin'_apply h z
  have hlP : ∀ a, hl (R.P a) = P a := fun a => by rw [hla, hPh]
  have hlP' : ∀ a, hl.symm (P a) = R.P a := fun a => by rw [← hlP, hl.symm_apply_apply]
  obtain ⟨Q, ψ, -, hQ, hQL, -⟩ := GlobalTheory.exists_polAV_pullback_of_isLocalRing E H _ Xo.univ.t Xo.univ.proper
    Xo.univ.ample Xo.univ.ktriv ℂ (FU.u i P)
  obtain ⟨u, H₂, χ, F, hAH, -, d₂, -, hF, hΛ, hE⟩ :=
    GlobalTheory.familyUnif_fibre_theta GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1.weil E H D l Xo σ g ty FU i P hP
      Q ψ hQ hQL
  obtain ⟨w, hw⟩ := hQL

  have hLB : (Xo.univ.t.PP.L.pull ψ).IsLB := LB.isLB_pull Xo.univ.t.PP.isLB ψ
  let ub : HolUnif Q.A (Xo.univ.t.PP.L.pull ψ) Q.g := GlobalTheory.ArchMetricCompare.carry u Q.isLB hLB hw
  have hAHb : ub.IsAH H₂ χ := GlobalTheory.ArchMetricCompare.carry_isAH Q.isLB hLB hw hAH
  let T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin Q.g → ℂ) := hl.trans F
  have hf : ∀ x y, hermForm R.Hm x y = hermForm H₂ (T x) (T y) := fun x y => by
    have key := GlobalTheory.KeyFam.SamePeriod.hermForm_eq_of_im H₂ F.toLinearMap R.Hm hl.symm.toLinearMap hP.2.2.2.1 (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      have h1 := hE a b
      have h2 := R.im a b
      rw [hRf] at h2
      show (hermForm H₂ (F (P a)) (F (P b))).im = (hermForm R.Hm (hl.symm (P a)) (hl.symm (P b))).im
      rw [hlP', hlP', h1]
      exact h2.symm) (hl x) (hl y)
    show _ = hermForm H₂ (F (hl x)) (F (hl y))
    simpa using key.symm
  obtain ⟨u', χ', hue, huΛ, huAH, hud⟩ := exists_reparam_isAH ub T H₂ R.Hm χ hAHb R.herm hf
  have hex : ∀ q, (u'.ex q).left ≫ ψ = (FU.ex i P (hl q)).left := fun q => by
    rw [hue]
    exact hF (hl q)

  have hB : ∀ (a : 𝓞 E) (p : Fin g → ℂ), hl (R.B a p) = fun k => ty k (a : E) * hl p k := fun a p => by
    let Da : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      { toFun := fun z k => ty k (a : E) * z k
        map_add' := fun z z' => by
          ext k
          simp [mul_add]
        map_smul' := fun c z => by
          ext k
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          ring }
    let N : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      hl.toLinearMap.comp ((R.B a).comp hl.symm.toLinearMap) - Da
    have hN : N.restrictScalars ℝ = 0 := LinearMap.ext_on hP.2.2.2.1 (by
      rintro _ ⟨y, rfl⟩
      show hl (R.B a (hl.symm (P y))) - (fun k => ty k (a : E) * P y k) = 0
      rw [hlP', ← R.act, hlP, sub_eq_zero]
      exact funext (hP.1 a y))
    have h0 : N (hl p) = 0 := congrArg (fun f => f (hl p)) hN
    have h1 : hl (R.B a (hl.symm (hl p))) - (fun k => ty k (a : E) * hl p k) = 0 := h0
    rw [hl.symm_apply_apply] at h1
    exact sub_eq_zero.1 h1
  refine ⟨Q.A, inferInstance, ψ, u', χ', hQ, huAH, fun a p => ?_, fun y y' hy => ?_, fun p => ?_, fun a => ?_⟩
  · rw [hex, hB, FU.ex_lin i P hP a (hl p), Over.comp_left, ← Category.assoc, hex]
  · exact hP.2.1 (by rw [hPh, hPh, hy])
  · rw [huΛ]
    show F (hl p) ∈ u.Λ ↔ _
    rw [hΛ]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, hl.injective (by rw [hlP, hy])⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, (hlP y).symm⟩
  · have hd' : IsDerivAt0 (fun z => (FU.ex i P z).left) (hl (x a)) (v a).left := by
      rw [hla]
      exact hd a
    obtain ⟨t, ⟨h₁, h₂⟩, -⟩ := d₂ (F (hl (x a)))
    refine ⟨t, GlobalTheory.VerticalDeriv.isDerivAt0_unique
      (Flat.PerGram.isDerivAt0_of_fibre ψ u F.toLinearMap hF h₁ h₂) hd', hud (x a) t h₂⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.FibreAtPeriod
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPeriodRiemannLatticeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_period_riemann_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (R : RiemLat E g (FU.Di i).La) (P : (FU.Di i).La →+ (Fin g → ℂ)) (h : Matrix (Fin g) (Fin g) ℂ), IsPeriod (FU.Di i) ty P → R.form = (FU.Di i).EF → IsUnit h.det → (∀ x, P x = h *ᵥ R.P x) → ∀ (A₀ : Type) (x : A₀ → Fin g → ℂ) (v : A₀ → (epsAt (FU.u i P) ⟶ Xo.univ.t.G)), (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (h *ᵥ x a) (v a).left) → FibreLatVec Xo.univ.t (FU.u i P) R x v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FibreAtPeriod.fibreLatVec_of_period | exact GlobalTheory.CompanionTheory.Ar.Cusp.FibreAtPeriod.fibreLatVec_of_period | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FibreAtPeriod.fibreLatVec_of_period <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameSectionBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameSectionBound
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd

section IntWeight

variable {K : Type} [Field K] {ι : Type}
  {pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type}
  {mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T], (S →ₐ[K] T) → pts S → pts T → Prop}
  {borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop}

theorem evalAt_bor_zpow [Fintype ι] (h : BorChart pts mapR borR) (e : ι → ℤ) {f : Rules pts}
    (hf : IsNatural pts mapR f)
    (hw : ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' →
      f p y' = ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) * f p y)
    (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ)
    (y y' : pts S) (hy : FromTest pts mapR y) (hy' : FromTest pts mapR y') (hb : borR t y y') :
    evalAt pts mapR f y' = ((∏ i, t i ^ e i : Sˣ) : S) * evalAt pts mapR f y := by
  unfold evalAt
  rw [dite_eq_left hy, dite_eq_left hy']
  apply eq_of_locM (K := K)
  intro m hm
  obtain ⟨A, u, c, c', B, uB, uB', tB, π, π', cB, hc, hc', hπ, hπ', hbB, e1, e2, e3⟩ := h S t y y' hb m
  rw [map_mul, chartAt_val hf hc' hy'.choose_spec.choose_spec.choose_spec,
    chartAt_val hf hc hy.choose_spec.choose_spec.choose_spec, ← e1, ← e2, AlgHom.comp_apply, AlgHom.comp_apply,
    ← hf A B π u uB hπ, ← hf A B π' u uB' hπ', hw B tB uB uB' hbB, map_mul]
  congr 1
  have key : ∀ i, Units.map cB.toRingHom.toMonoidHom (tB i) = Units.map (locM K m).toRingHom.toMonoidHom (t i) :=
    fun i => Units.ext (by simpa using e3 i)
  have h1 : cB ((∏ i, tB i ^ e i : (B.R)ˣ) : B.R) =
      ((Units.map cB.toRingHom.toMonoidHom (∏ i, tB i ^ e i) : (Localization.AtPrime m)ˣ) : Localization.AtPrime m) := rfl
  have h2 : locM K m ((∏ i, t i ^ e i : Sˣ) : S) =
      ((Units.map (locM K m).toRingHom.toMonoidHom (∏ i, t i ^ e i) : (Localization.AtPrime m)ˣ) :
        Localization.AtPrime m) := rfl
  rw [h1, h2, map_prod, map_prod]
  simp_rw [map_zpow, key]

end IntWeight

section Abs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {c : Coeff l}

def absHom (p : ℕ) [hp : Fact p.Prime] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (e : ℕ) : T.Fr →*₀ ℝ where
  toFun := absT p la T e
  map_zero' := by simp [absT]
  map_one' := by
    have h1 : vV T.V (1 : T.Fr) = 0 := by simp [vV]
    simp [absT, h1]
  map_mul' x y := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    by_cases hx : x = 0
    · simp [absT, hx]
    by_cases hy : y = 0
    · simp [absT, hy]
    simp only [absT, if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy)]
    rw [← Real.rpow_add hp0, vV_mul hx hy]
    congr 1
    push_cast
    ring

theorem absHom_apply (p : ℕ) [Fact p.Prime] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (e : ℕ) (x : T.Fr) :
    absHom p la T e x = absT p la T e x := rfl

theorem absT_of_nval {p : ℕ} [hp : Fact p.Prime] {la : HeightOneSpectrum (𝓞 c.F)} {T : CDVR} {e : ℕ} (he : 0 < e)
    (hr : 0 < ramOverZ la) (t : Ix Dw → T.Frˣ) (n : Ix Dw → ℤ) {g w : T.Fr}
    (hg : g = ((∏ i, t i ^ n i : T.Frˣ) : T.Fr) * w) {s : ℝ}
    (hs : nval T.V e g = ((ramOverZ la * s : ℝ) : EReal)) :
    absT p la T e w = (p : ℝ) ^ (-s) * ∏ j, tOf p la T e t j ^ n j := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [nval_zero] at hs
    exact EReal.coe_ne_top _ hs.symm
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hr' : (ramOverZ la : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hv : (vV T.V g : ℝ) / e = ramOverZ la * s := by
    rw [nval_of_ne hg0] at hs
    exact_mod_cast hs
  have hag : absT p la T e g = (p : ℝ) ^ (-s) := by
    unfold absT
    rw [if_neg hg0]
    congr 1
    rw [← div_div, hv]
    field_simp
  have hu : absT p la T e ((∏ i, t i ^ n i : T.Frˣ) : T.Fr) = ∏ j, (tOf p la T e t j ^ n j)⁻¹ := by
    rw [Units.coe_prod, ← absHom_apply, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, absHom_apply, tOf, inv_zpow, inv_inv]
  have hm : absT p la T e g = absT p la T e ((∏ i, t i ^ n i : T.Frˣ) : T.Fr) * absT p la T e w := by
    rw [hg, ← absHom_apply, map_mul]
    rfl
  have hne : ∀ j, tOf p la T e t j ^ n j ≠ 0 := fun j => zpow_ne_zero _ (tOf_pos la T e t j).ne'
  have hP : (∏ j, tOf p la T e t j ^ n j) * ∏ j, (tOf p la T e t j ^ n j)⁻¹ = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun j _ => mul_inv_cancel₀ (hne j)
  rw [← hag, hm, hu]
  linear_combination (-absT p la T e w) * hP

end Abs

theorem readsZ_of_isIntPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), ∀ (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ x : (Ref.pjSys Xo c).Pt la, (∀ f, (Ref.pjSys Xo c).val x f = nval T.V e (evI y f)) → FinRd.ReadsZ Fr z x (FinRd.tOf p la T e t) := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hev la T io e y evT zT t hI x hx a f hf
  letI := io.toAlgebra
  letI := Small.cstAlg Or
  obtain ⟨hp, hO, -, -, -, hn, ⟨q, φ, ψ, yq, hφ, hψ, hA⟩, hb⟩ := hI
  have hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hWD := (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.2.1
  have hrd : Fr.rd f = φ (f q yq) := Fr.rd_eq_of_frMap hWD hf.1 q φ yq hφ
  obtain ⟨hmem, hψe⟩ := hA (f q yq)
  have hm : Fr.rd f ∈ A := hrd ▸ hmem
  have hft : Formalism.L2.Pj.FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) zT := ⟨q, ψ, yq, hψ⟩
  have hzT : evR Xo c f zT = ψ (f q yq) := by
    unfold evR evalAt
    rw [dite_eq_left hft]
    exact hWD f hf.1 T.Fr _ q _ ψ _ yq zT hft.choose_spec.choose_spec.choose_spec hψ
  have hbor : evI y f = ((∏ i, t i ^ exZ Dw a i : T.Frˣ) : T.Fr) * evR Xo c f zT :=
    evalAt_bor_zpow (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.1 (exZ Dw a) hf.1
      (fun p t y y' hb => by rw [hf.2 p t y y' hb, Units.coe_prod]) T.Fr t zT y.1 hft y.2.1 hb
  have hnorm : ‖ev ⟨Fr.rd f, hm⟩‖ = absT p la T e (evR Xo c f zT) := by
    rw [hn, hzT, hψe]
    exact congrArg (absT p la T e) (congrArg evT (Subtype.ext hrd))
  refine ⟨ev ⟨Fr.rd f, hm⟩, hev ⟨Fr.rd f, hm⟩, fun htop => ?_, fun s hs => ?_⟩
  · have h0 : evI y f = 0 := by
      by_contra hne
      rw [hx, nval_of_ne hne] at htop
      exact EReal.coe_ne_top _ htop
    have hw : evR Xo c f zT = 0 := by
      rw [h0] at hbor
      exact (mul_eq_zero.1 hbor.symm).resolve_left (Units.ne_zero _)
    rw [← norm_eq_zero, hnorm, hw]
    simp [absT]
  · rw [hnorm]
    exact absT_of_nval hO.1 (ram_pos hp) t (exZ Dw a) hbor (by rw [← hx]; exact hs)

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameSectionBoundStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_section_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), ∀ (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ x : (Ref.pjSys Xo c).Pt la, (∀ f, (Ref.pjSys Xo c).val x f = nval T.V e (evI y f)) → FinRd.ReadsZ Fr z x (FinRd.tOf p la T e t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.readsZ_of_isIntPt | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.readsZ_of_isIntPt | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.readsZ_of_isIntPt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaMultiplierQuadraticCharacter
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaMultiplierQuadraticCharacter
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Unimod

theorem mem_of_unimodular {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (Ef : LinearMap.BilinForm ℤ Λ) (hE : ∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im)
    (hB : Function.Bijective Ef) (w : Fin g → ℂ)
    (hw : ∀ l : Λ, ∃ k : ℤ, (hermForm Hm w l).im = k) : w ∈ Λ := by
  have addR : ∀ (v x y : Fin g → ℂ), hermForm Hm v (x + y) = hermForm Hm v x + hermForm Hm v y := fun v x y => by
    simp [hermForm, Matrix.mulVec_add, dotProduct_add]
  have addL : ∀ (v v' x : Fin g → ℂ), hermForm Hm (v - v') x = hermForm Hm v x - hermForm Hm v' x := fun v v' x => by
    simp [hermForm, sub_dotProduct]
  have smulR : ∀ (v x : Fin g → ℂ) (r : ℝ), hermForm Hm v (r • x) = r * hermForm Hm v x := fun v x r => by
    have e : star (r • x) = (r : ℂ) • star x := by
      ext i
      simp
    simp only [hermForm, e, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  choose k hk using hw
  have kadd : ∀ a b : Λ, k (a + b) = k a + k b := fun a b => by
    have h := hk (a + b)
    rw [Submodule.coe_add, addR, Complex.add_im, hk a, hk b] at h
    exact_mod_cast h.symm
  let ℓ : Λ →ₗ[ℤ] ℤ := (AddMonoidHom.mk' k kadd).toIntLinearMap
  obtain ⟨c, hc⟩ := hB.2 ℓ
  have hv : ∀ x ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)), (hermForm Hm (w - c) x).im = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      have h := hE c ⟨x, hx⟩
      have h' : Ef c ⟨x, hx⟩ = k ⟨x, hx⟩ := LinearMap.congr_fun hc _
      rw [addL, Complex.sub_im, ← h, h']
      have := hk ⟨x, hx⟩
      simp only at this
      rw [this, sub_self]
    | zero => simp [hermForm]
    | add x y _ _ hx hy => rw [addR, Complex.add_im, hx, hy, add_zero]
    | smul r x _ hx => rw [smulR, Complex.im_ofReal_mul, hx, mul_zero]
  have hI : (hermForm Hm (w - c) (Complex.I • (w - c))).im = 0 := hv _ (by rw [hfull]; trivial)
  have hv0 : w - (c : Fin g → ℂ) = 0 := by
    by_contra hne
    have hp := hpos _ hne
    have e : star (Complex.I • (w - (c : Fin g → ℂ))) = (-Complex.I) • star (w - (c : Fin g → ℂ)) := by
      ext i
      simp
    have e' : hermForm Hm (w - c) (Complex.I • (w - c)) = -Complex.I * hermForm Hm (w - c) (w - c) := by
      simp only [hermForm, e, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    rw [e'] at hI
    have : (hermForm Hm (w - c) (w - c)).re = 0 := by simpa using hI
    exact hp.ne' this
  rw [sub_eq_zero.1 hv0]
  exact c.2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {L : Type} [Field L] [NumberField L]

theorem exists_compare (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) :
    ∃ (g' : ℕ) (Λ₀ : Submodule ℤ (Fin g' → ℂ)) (H₀ : Matrix (Fin g') (Fin g') ℂ) (χ₀ : Λ₀ → ℂ)
      (Ef : LinearMap.BilinForm ℤ Λ₀) (F : (Fin D.g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hΛ : ∀ l ∈ a.u.Λ, F l ∈ Λ₀),
      Submodule.span ℝ (Λ₀ : Set (Fin g' → ℂ)) = ⊤ ∧
      (∀ z : Fin g' → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₀.mulVec (star z)).re) ∧
      (∀ x y : Λ₀, (Ef x y : ℝ) = (hermForm H₀ x y).im) ∧ Function.Bijective Ef ∧
      (∀ l : Λ₀, χ₀ l = 1 ∨ χ₀ l = -1) ∧
      (∀ z w, hermForm a.Hm z w = hermForm H₀ (F z) (F w)) ∧
      (∀ l : a.u.Λ, a.χ l = χ₀ ⟨F l, hΛ l l.2⟩) ∧
      (∀ z, F z ∈ Λ₀ → z ∈ a.u.Λ) ∧ Function.Surjective F := by
  have hLφ : (D.t.PP.L.pull a.φ).IsLB := pull_isLB D.t.PP.isLB _
  obtain ⟨hpr, hamp, hkt⟩ := D.princ
  have := D.tK.semi.smooth
  have := D.tK.semi.geomConnected
  have : ConnectedSpace D.tK.G.left := GeometricallyConnected.connectedSpace D.tK.G.hom D.tK.G.hom.isOpenMap
  obtain ⟨gd, hgd⟩ := exists_dim_of_preconnected D.tK.G.hom (Classical.arbitrary _)
  let P₀ : Out.PolAV (Sp L) :=
    { A := D.tK.G, g := gd, smoothDim := hgd, L := D.tK.PP.L, isLB := D.tK.PP.isLB, ample := hamp, ktriv := hkt
      isAb := ⟨D.tK.semi.comm, D.tK.semi.smooth, hpr, D.tK.semi.geomConnected⟩
      rigid := GlobalTheory.ObjDim.rigidified
      sym := GlobalTheory.ObjDim.sym }
  obtain ⟨P', ψ, hψ, -, hm, t, ht⟩ := GlobalTheory.polBaseChange_holds (Sp L) (Sp ℂ) (spMap σ) P₀
  have hpb : IsGrpPullback P'.A D.tK.G (spMap σ) ψ := by
    refine ⟨hψ, fun T x y x₀ y₀ hx hy => ?_⟩
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hψ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hψ.w y), ← hm]
    rfl
  have hpc : IsGrpPullback P'.A D.t.G (emb σ) (ψ ≫ D.m.φ) :=
    (hpb.comp D.m.cart).congr (by rw [spMap_comp_spMap]) rfl
  obtain ⟨e, hmon, he⟩ := grpPullback_iso a.cart hpc
  haveI := hmon
  obtain ⟨rig, hrig⟩ := P'.rigid
  obtain ⟨u₀, H₀, χ₀, Ef, hu₀, -, hv, hw, -, -, hE, hB, -⟩ := GlobalTheory.thetaUnifAV_closed P' rig hrig
  have hol : IsHolTo (Set.univ : Set (Fin D.g → ℂ)) (fun w => (a.u.ex w ≫ e.hom).left) := by
    simpa only [Over.comp_left] using GlobalTheory.HolTorsion.isHolTo_comp (Flat.PerGram.isHolTo_ex a.u) e.hom.left
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo P'.A P'.isAb P'.L P'.g D.g u₀ hv hw
    (fun w => a.u.ex w ≫ e.hom) (fun p q => by rw [a.u.ex_add, MonObj.mul_comp]) hol
  have hΛ : ∀ l ∈ a.u.Λ, F l ∈ u₀.Λ := fun l hl => (u₀.ker _).1 (by
    rw [hF, (a.u.ker l).2 hl, MonObj.one_comp])
  have back : ∀ z, F z ∈ u₀.Λ → z ∈ a.u.Λ := fun z hz => (a.u.ker z).1 (by
    have h := (u₀.ker _).2 hz
    rw [hF] at h
    have h' := congrArg (· ≫ e.inv) h
    simpa [MonObj.one_comp] using h')
  have hsurj : Function.Surjective F := by
    haveI := u₀.discrete
    refine LinearMap.range_eq_top.1 (GlobalTheory.AHWeil.eq_top_of_add_discrete u₀.Λ _ fun w => ?_)
    obtain ⟨z, hz⟩ := a.u.ex_onto (u₀.ex w ≫ e.inv)
    have hz' : u₀.ex (F z) = u₀.ex w := by
      rw [hF, hz, Category.assoc, e.inv_hom_id, Category.comp_id]
    have h := u₀.ex_add (w - F z) (F z)
    rw [sub_add_cancel, hz'] at h
    exact ⟨⟨w - F z, (u₀.ker _).1 (mul_eq_right.1 h.symm)⟩, z, by simp⟩
  have i₁ : LBIso P'.L (D.tK.PP.L.pull ψ) := LBIso.symm ⟨t, ht⟩
  have i₂ : LBIso D.tK.PP.L (D.t.PP.L.pull D.m.φ) := by
    obtain ⟨w, hw, -⟩ := D.m.lin
    exact ⟨w, hw⟩
  have i₃ : LBIso (D.tK.PP.L.pull ψ) (D.t.PP.L.pull (ψ ≫ D.m.φ)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso i₂ ψ rfl
  have i₄ : LBIso P'.L (D.t.PP.L.pull (ψ ≫ D.m.φ)) :=
    LBIso.trans P'.isLB (pull_isLB D.tK.PP.isLB _) (pull_isLB D.t.PP.isLB _) i₁ i₃
  have i₅ : LBIso (P'.L.pull e.hom.left) (D.t.PP.L.pull a.φ) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso i₄ e.hom.left he.symm
  have iso : LBIso (lbPow (D.t.PP.L.pull a.φ) 1) (lbPow (P'.L.pull e.hom.left) 1) :=
    GlobalTheory.lbIso_lbPow (LBIso.symm i₅) 1
  obtain ⟨hH, hχ⟩ := GlobalTheory.appellHumbert_data_eq_of_lbIso_pow_pull a.A P'.A _ P'.L D.g P'.g a.u u₀ a.Hm H₀ a.χ χ₀
    e.hom F hΛ 1 one_pos hLφ P'.isLB a.ah hu₀ hF iso
  exact ⟨P'.g, u₀.Λ, H₀, χ₀, Ef, F, hΛ, u₀.full, hu₀.2.1, hE, hB,
    GlobalTheory.ThetaUnifCompare.chi_eq_one_or_of_sym P'.isLB P'.sym hu₀, hH, fun l => by simpa using hχ l, back, hsurj⟩

theorem frame_unimodular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ), (∀ l l' : a.u.Λ, ∃ k : ℤ, (a.herm l l').im = k) ∧ (∀ w : Fin D.g → ℂ, (∀ l : a.u.Λ, ∃ k : ℤ, (a.herm w l).im = k) → w ∈ a.u.Λ) ∧ (∀ l l' : a.u.Λ, a.χ (l + l') = a.χ l * a.χ l' * Complex.exp (Real.pi * Complex.I * (a.herm l l').im)) ∧ ∀ l : a.u.Λ, a.χ l ^ 2 = 1 := by
  intro E _ _ _ H L _ _ D σ a
  have hLφ : (D.t.PP.L.pull a.φ).IsLB := pull_isLB D.t.PP.isLB _
  obtain ⟨g', Λ₀, H₀, χ₀, Ef, F, hΛ, hfull, hpos, hE, hB, hχ₀, hH, hχ, back, hsurj⟩ := exists_compare D σ a
  refine ⟨fun l l' => ?_, fun w hw => ?_, fun l l' => GlobalTheory.FrameValue.chi_add hLφ a.ah l l', fun l => ?_⟩
  · obtain ⟨n, hn⟩ := GlobalTheory.FrameValue.exists_int_im hLφ a.ah l l'
    exact ⟨n, hn.symm⟩
  · refine back w (mem_of_unimodular Λ₀ hfull H₀ hpos Ef hE hB (F w) fun l₀ => ?_)
    obtain ⟨z, hz⟩ := hsurj l₀
    have hzΛ : z ∈ a.u.Λ := back z (hz ▸ l₀.2)
    obtain ⟨k, hk⟩ := hw ⟨z, hzΛ⟩
    refine ⟨k, ?_⟩
    rw [← hz, ← hH]
    exact hk
  · rw [hχ l]
    rcases hχ₀ ⟨F l, hΛ l l.2⟩ with h | h <;> simp [h]

end GlobalTheory.CompanionTheory.Ar.Sl.Unimod
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaMultiplierQuadraticCharacterStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_multiplier_quadratic_character : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ), (∀ l l' : a.u.Λ, ∃ k : ℤ, (a.herm l l').im = k) ∧ (∀ w : Fin D.g → ℂ, (∀ l : a.u.Λ, ∃ k : ℤ, (a.herm w l).im = k) → w ∈ a.u.Λ) ∧ (∀ l l' : a.u.Λ, a.χ (l + l') = a.χ l * a.χ l' * Complex.exp (Real.pi * Complex.I * (a.herm l l').im)) ∧ ∀ l : a.u.Λ, a.χ l ^ 2 = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Unimod.frame_unimodular | exact GlobalTheory.CompanionTheory.Ar.Sl.Unimod.frame_unimodular | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Unimod.frame_unimodular <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerMapFlatSemiabelian
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerMapFlatSemiabelian
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem flat_mul_semiAbelian : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G],
    IsSemiAbelian G → ∀ N : ℕ, 1 ≤ N → Flat ((𝟙 G) ^ N).left :=
  PositivityTheory.HtPt.Twhopf.mul_flat

end GlobalTheory.CompanionTheory.Ar.BT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerMapFlatSemiabelianStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_map_flat_semiabelian : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ N : ℕ, 1 ≤ N → Flat ((𝟙 G) ^ N).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.flat_mul_semiAbelian | exact GlobalTheory.CompanionTheory.Ar.BT.flat_mul_semiAbelian | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.flat_mul_semiAbelian <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHolomorphic
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHolomorphic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isOpen_punct (n a : ℕ) (ρ : ℝ) : IsOpen (punct n a ρ) := by
  have h : punct n a ρ = Metric.ball 0 ρ ∩ ⋂ i : Fin n, {z : Fin n → ℂ | (i : ℕ) < a → z i ≠ 0} := by
    ext z
    simp only [punct, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [h]
  refine Metric.isOpen_ball.inter (isOpen_iInter_of_finite fun i => ?_)
  by_cases hi : (i : ℕ) < a
  · simp only [hi, true_implies]
    exact isOpen_ne_fun (continuous_apply i) continuous_const
  · simp [hi]

theorem isHolTo_of_comp_openImmersion {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {X Y : Scheme.{0}}
    (j : X ⟶ Y) [IsOpenImmersion j] {B : Set W} {y : W → (Sp ℂ ⟶ X)}
    (h : IsHolTo B fun b => y b ≫ j) : IsHolTo B y := by
  intro U f
  have hpre : ∀ x : Sp ℂ ⟶ X, (x ≫ j) ⁻¹ᵁ (j ''ᵁ U) = x ⁻¹ᵁ U := by
    intro x
    ext p
    simp
  have key : ∀ (x : Sp ℂ ⟶ X) (h1 : ⊤ ≤ (x ≫ j) ⁻¹ᵁ (j ''ᵁ U)) (h2 : ⊤ ≤ x ⁻¹ᵁ U),
      valAt (x ≫ j) (j ''ᵁ U) h1 ((j.appIso U).inv f) = valAt x U h2 f := by
    intro x h1 h2
    have e : (j.appIso U).inv ≫ (x ≫ j).appLE (j ''ᵁ U) ⊤ h1 = x.appLE U ⊤ h2 := by
      rw [← Scheme.Hom.appLE_comp_appLE x j (j ''ᵁ U) U ⊤ (j.preimage_image_eq U).ge h2]
      rw [← Category.assoc, Scheme.Hom.appIso_inv_appLE]
      simp
    unfold valAt
    rw [← e]
    rfl
  have hval : ∀ b, valAt' (y b ≫ j) (j ''ᵁ U) ((j.appIso U).inv f) = valAt' (y b) U f := by
    intro b
    unfold valAt'
    by_cases hb : ⊤ ≤ y b ⁻¹ᵁ U
    · have hb' : ⊤ ≤ (y b ≫ j) ⁻¹ᵁ (j ''ᵁ U) := by rw [hpre]; exact hb
      rw [dite_eq_left hb, dite_eq_left hb']
      exact key _ hb' hb
    · have hb' : ¬ ⊤ ≤ (y b ≫ j) ⁻¹ᵁ (j ''ᵁ U) := by rw [hpre]; exact hb
      rw [dite_eq_right hb, dite_eq_right hb']
  obtain ⟨ho, hd⟩ := h (j ''ᵁ U) ((j.appIso U).inv f)
  simp only [hpre] at ho hd
  exact ⟨ho, by simpa only [hval] using hd⟩

theorem isHolTo_pt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : BdryChart Xo σ n a), IsHolTo (punct n a 1) C.pt := by
  intro E _ _ _ H D l Xo σ n a C
  haveI := C.j_open
  apply isHolTo_of_comp_openImmersion C.j
  have hB : IsOpen (punct n a 1) := isOpen_punct n a 1
  have hsub : punct n a 1 ⊆ Metric.ball 0 1 := fun z hz => hz.1
  have h0 : IsHolTo (punct n a 1) fun z => ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (C.ψ z) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_spMap hB fun r => (C.hol.2 r).mono hsub
  exact GlobalTheory.FiniteOrderConst.isHolTo_of_eqOn h0 fun z hz => (C.pt_eq z hz).1

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHolomorphicStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_chart_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : BdryChart Xo σ n a), IsHolTo (punct n a 1) C.pt := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isHolTo_pt | exact GlobalTheory.CompanionTheory.Ar.Flat.isHolTo_pt | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isHolTo_pt <;> assumption)
end
end

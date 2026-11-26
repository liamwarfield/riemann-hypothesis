module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HtExists
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GhModel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIsOpenImmersion

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def PolarisedAt {X : Scheme.{0}} (t : SAB H X) (z : Spec (CommRingCat.of ℂ) ⟶ X) : Prop :=
  ∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' t z), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}


open Classical in
def gramFn (𝔐 : HodgeCpt Y S y) {r : ℕ} (b : Fin r → 𝔐.Li) (w : (Σ k, J k) → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  if h : ∃ (Γ : Matrix (Fin r) (Fin r) ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X),
      CoordsAt 𝔐.ξ y z w ∧ 𝔐.Interior z ∧ 𝔐.M.GramAt 𝔐.t.PP.L z b Γ then h.choose else 0

def recentre {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) : Fin n → ℂ :=
  t₀ + (ρ : ℂ) • (u ∘ π)

def uncentre {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) : Fin n → ℂ :=
  fun i => (ρ : ℂ)⁻¹ * (t (π.symm i) - t₀ (π.symm i))

def periodGram {n a₀ g r : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ g Λ)
    (U : Fin r → (Fin n → ℂ) → Fin g → ℂ) (u : Fin n → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => Real.pi * (U j u ⬝ᵥ L.H u *ᵥ star (U i u))

def IsFramePeriods (𝔐 : HodgeCpt Y S y) {r : ℕ} (b : Fin r → 𝔐.Li) {P : Ideal (MRing J)} {n : ℕ}
    {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω) {a₀ g : ℕ}
    {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ)
    (U : Fin r → (Fin n → ℂ) → Fin g → ℂ) : Prop :=
  0 < ρ ∧ ρ ≤ 1 ∧ (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) ∧ LinearIndependent ℂ (fun k => U k 0) ∧
  (∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < χ.a ∧ t₀ (π.symm i) = 0) ∧
  ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, recentre t₀ ρ π u ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧
    InFrameDomain y cc f (χ.γ (recentre t₀ ρ π u)) ∧ (χ.γ (recentre t₀ ρ π u) ∉ Bd ↔ u ∈ Flat.punct n a₀ 1) ∧
    (u ∈ Flat.punct n a₀ 1 → ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (χ.γ (recentre t₀ ρ π u)) →
      𝔐.M.GramAt 𝔐.t.PP.L z b (periodGram L U u))

theorem recentre_uncentre {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) :
    recentre t₀ ρ π (uncentre t₀ ρ π t) = t := by
  have h : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  funext i
  simp [recentre, uncentre, h]

theorem isOpen_punct (n a : ℕ) (ρ : ℝ) : IsOpen (Flat.punct n a ρ) := by
  have : Flat.punct n a ρ = Metric.ball 0 ρ ∩ ⋂ i : Fin n, {z : Fin n → ℂ | i.val < a → z i ≠ 0} := by
    ext z; simp [Flat.punct]
  rw [this]
  refine Metric.isOpen_ball.inter (isOpen_iInter_of_finite fun i => ?_)
  by_cases h : i.val < a
  · simpa [h] using isOpen_ne_fun (continuous_apply i) continuous_const
  · simp [h]

theorem contDiff_uncentre {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (uncentre t₀ ρ π) := by
  unfold uncentre
  exact contDiff_pi.2 fun i => contDiff_const.mul ((contDiff_apply ℝ (fun _ => ℂ) (π.symm i)).sub contDiff_const)

theorem uncentre_mem_ball {n : ℕ} {t₀ t : Fin n → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n))
    (h : ‖t - t₀‖ < ρ) : uncentre t₀ ρ π t ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
  intro i
  have h1 : ‖t (π.symm i) - t₀ (π.symm i)‖ ≤ ‖t - t₀‖ := norm_le_pi_norm (t - t₀) (π.symm i)
  simp only [uncentre, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  rw [inv_mul_lt_iff₀ hρ]
  linarith

theorem uncentre_self {n : ℕ} (t : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) : uncentre t ρ π t = 0 := by
  funext i
  simp [uncentre]

theorem recentre_zero {n : ℕ} (t : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) : recentre t ρ π 0 = t := by
  funext i
  simp [recentre]

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModelBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModelBaseChange
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem lieModel_liftBaseChange : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ X) (V : Type) [AddCommGroup V] [Module R V] (M : LieModel G x V), ∃ (T : Type) (_ : AddCommGroup T) (_ : Module R' T) (_ : Module R T) (_ : IsScalarTower R R' T) (M' : LieModel G (spMap (algebraMap R R') ≫ x) T) (j : V →ₗ[R] T), (∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left)) ∧ IsBaseChange R' j := by
  intro X G _ _ _ R R' _ _ _ x V _ _ M
  obtain ⟨T, iT, mT, ⟨M'⟩⟩ := lieModel_exists X G R' (spMap (algebraMap R R') ≫ x)
  letI mR : Module R T := Module.compHom T (algebraMap R R')
  have hsm : ∀ (a : R) (t : T), a • t = algebraMap R R' a • t := fun _ _ => rfl
  haveI tower : IsScalarTower R R' T :=
    ⟨fun a b t => by rw [Algebra.smul_def, hsm, mul_smul]⟩
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x = spMap (algebraMap R R') ≫ x := rfl
  have spec_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
      (f : A →+* B) (g : B →+* C) :
      Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
        Spec.map (CommRingCat.ofHom (g.comp f)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have spec_dual_alg :
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R' (DualNumber R'))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [spec_comp, spec_comp]
    congr 2
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have spec_fst_dual :
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R' R' R').toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) =
      Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [spec_comp, spec_comp]
    congr 2
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl']
  have spec_dual_eps (c : R) :
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫
        Spec.map (CommRingCat.ofHom (epsMul c)) =
      Spec.map (CommRingCat.ofHom (epsMul ((algebraMap R R') c))) ≫
        Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) := by
    rw [spec_comp, spec_comp]
    congr 2
    ext a <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl']
  let b : epsAt (spMap (algebraMap R R') ≫ x) ⟶ epsAt x :=
    Over.homMk (Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R')))) (by
      change _ ≫ _ ≫ x = _ ≫ (spMap (algebraMap R R') ≫ x)
      rw [← Category.assoc, spec_dual_alg, Category.assoc])
  have hb : ∀ {v : epsAt x ⟶ G}, IsTanAt G x v →
      IsTanAt G (spMap (algebraMap R R') ≫ x) (b ≫ v) := by
    intro v hv
    change _ ≫ Spec.map _ ≫ v.left = _
    rw [← Category.assoc, spec_fst_dual, Category.assoc, hv]
    exact congrArg (·.left)
      (comp_one (M := G) (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R R'))) hφ :
        Over.mk (spMap (algebraMap R R') ≫ x) ⟶ Over.mk x))
  have hs (c : R) : b ≫ LieTangent.epsScale x c =
      LieTangent.epsScale (spMap (algebraMap R R') ≫ x) (algebraMap R R' c) ≫ b :=
    Over.OverMorphism.ext (spec_dual_eps c)
  have ex : ∀ e, ∃ t, M'.pt t = b ≫ M.pt e :=
    fun e => M'.onto _ (hb (M.tan e))
  choose f hf using ex
  let j : V →ₗ[R] T :=
    { toFun := f
      map_add' := fun a b => M'.inj (by rw [M'.add, hf, hf, hf, M.add, comp_mul])
      map_smul' := fun c e => M'.inj (by
        rw [RingHom.id_apply, hsm, LieModel.pt_smul, hf, hf, LieModel.pt_smul, ← Category.assoc,
          hs, Category.assoc]) }
  have hl : ∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left) := fun e => by
    change (M'.pt (f e)).left ≫ 𝟙 G.left = _
    rw [hf, Category.comp_id]
    rfl
  exact ⟨T, iT, mT, mR, tower, M', j, hl, GlobalTheory.T.lie_model_isBaseChange X G R R' x V T M M' j hl⟩

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModelBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lie_model_base_change : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ X) (V : Type) [AddCommGroup V] [Module R V] (M : LieModel G x V), ∃ (T : Type) (_ : AddCommGroup T) (_ : Module R' T) (_ : Module R T) (_ : IsScalarTower R R' T) (M' : LieModel G (spMap (algebraMap R R') ≫ x) T) (j : V →ₗ[R] T), (∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left)) ∧ IsBaseChange R' j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_liftBaseChange | exact GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_liftBaseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_liftBaseChange <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieSigma

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem dualMap_comp_algebraMap (φ : R →+* R') :
    (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp φ := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap (φ : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap φ)
      = φ.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [GlobalTheory.CompanionTheory.Ar.dualMap]

theorem dualMap_comp_epsMul (φ : R →+* R') (a : R) :
    (dualMap φ).comp (epsMul a) = (epsMul (φ a)).comp (dualMap φ) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, mul_comm]

theorem comp_one_over {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  exact comp_one u

theorem comp_mul_over {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) (p q : X ⟶ M) :
    u ≫ (p * q) = (u ≫ p) * (u ≫ q) := by
  exact comp_mul u p q

def pullEps (φ : R →+* R') (x : Sp R ⟶ S) : epsAt (spMap φ ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (dualMap φ)) (by
    simp only [Over.mk_hom, epsAt]
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      dualMap_comp_algebraMap])

def pullPt (φ : R →+* R') (x : Sp R ⟶ S) : Over.mk (spMap φ ≫ x) ⟶ Over.mk x :=
  Over.homMk (spMap φ) rfl

theorem isTanAt_pull (G : Over S) [GrpObj G] (φ : R →+* R') (x : Sp R ⟶ S) (v : epsAt x ⟶ G)
    (hv : IsTanAt G x v) : IsTanAt G (spMap φ ≫ x) (pullEps φ x ≫ v) := by
  unfold IsTanAt at hv ⊢
  rw [← comp_one_over (pullPt φ x), Over.comp_left, Over.comp_left, ← hv]
  have key : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R' R' R').toRingHom) ≫ spMap (dualMap φ)
      = spMap φ ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, fst_comp_dualMap]
  simp only [pullEps, pullPt, Over.homMk_left]
  rw [reassoc_of% key]

theorem exists_linear (G : Over S) [GrpObj G] (φ : R →+* R') (x : Sp R ⟶ S)
    {E E₀ : Type} [AddCommGroup E] [Module R E] [AddCommGroup E₀] [Module R' E₀] [Module R E₀]
    (hs : ∀ (a : R) (e : E₀), a • e = φ a • e) (M : LieModel G x E)
    (M₀ : LieModel G (spMap φ ≫ x) E₀) :
    ∃ j : E →ₗ[R] E₀, ∀ e, M₀.pt (j e) = pullEps φ x ≫ M.pt e := by
  choose j hj using fun e => M₀.onto _ (isTanAt_pull G φ x (M.pt e) (M.tan e))
  refine ⟨{ toFun := j, map_add' := ?_, map_smul' := ?_ }, hj⟩
  · intro e e'
    apply M₀.inj
    rw [M₀.add, hj, hj, hj, M.add, comp_mul_over]
  · intro c e
    apply M₀.inj
    rw [RingHom.id_apply, hs, hj]
    apply Over.OverMorphism.ext
    rw [M₀.smul, hj, Over.comp_left, Over.comp_left, M.smul]
    simp only [pullEps, Over.homMk_left, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, dualMap_comp_epsMul]

def transport {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {E E' : Type} [AddCommGroup E] [Module R E]
    [AddCommGroup E'] [Module R E'] (M : LieModel G x E) (f : E' ≃ₗ[R] E) : LieModel G x E' where
  pt e := M.pt (f e)
  tan e := M.tan _
  inj := M.inj.comp f.injective
  onto v hv := by
    obtain ⟨e, he⟩ := M.onto v hv
    exact ⟨f.symm e, by simpa using he⟩
  add e e' := by simp only [map_add (f := _)]; exact M.add _ _
  smul c e := by simp only [map_smul]; exact M.smul _ _


open GroundTheory.Heights₂.Heights in
theorem lieModel_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ S) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] (M : LieModel G z V) (σ : L →+* ℂ), ∃ Mσ : LieModel G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (GroundTheory.Heights₂.Heights.Fibre σ V), ∀ e : V, M.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 G.left) e (Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)) := by
  intro S G _ _ _ L _ _ z V _ _ M σ
  classical
  let _ : Algebra (𝓞 L) ℂ := (σ.comp (algebraMap (𝓞 L) L)).toAlgebra
  obtain ⟨E₀, i1, i2, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists S G ℂ (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z)
  let _ : Module (𝓞 L) E₀ := Module.compHom E₀ (σ.comp (algebraMap (𝓞 L) L))
  have _ : IsScalarTower (𝓞 L) ℂ E₀ := ⟨fun a b e => by
    show ((σ.comp (algebraMap (𝓞 L) L)) a * b) • e = (σ.comp (algebraMap (𝓞 L) L)) a • b • e
    rw [mul_smul]⟩
  obtain ⟨j, hj⟩ := exists_linear G (σ.comp (algebraMap (𝓞 L) L)) z (fun a e => rfl) M M₀
  have hl : ∀ e, M.Lifts (algebraMap (𝓞 L) ℂ) (𝟙 G.left) e (M₀.pt (j e)) := by
    intro e
    unfold GlobalTheory.CompanionTheory.Ar.LieModel.Lifts
    rw [hj e, Over.comp_left, Category.comp_id]
    rfl
  have hb := GlobalTheory.T.lie_model_isBaseChange S G (𝓞 L) ℂ z V E₀ M M₀ j hl
  let f : GroundTheory.Heights₂.Heights.Fibre σ V ≃ₗ[ℂ] E₀ := hb.equiv
  refine ⟨transport M₀ f, fun e => ?_⟩
  have hf : f ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e) = j e := by
    show hb.equiv ((1 : ℂ) ⊗ₜ[𝓞 L] e) = j e
    rw [IsBaseChange.equiv_tmul, one_smul]
  unfold GlobalTheory.CompanionTheory.Ar.LieModel.Lifts
  show (M₀.pt (f ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e))).left ≫ 𝟙 _ = _
  rw [hf, hj e, Over.comp_left, Category.comp_id]
  rfl

end GlobalTheory.CompanionTheory.Ar.LieSigma
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_complex_base_change : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ S) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] (M : LieModel G z V) (σ : L →+* ℂ), ∃ Mσ : LieModel G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (GroundTheory.Heights₂.Heights.Fibre σ V), ∀ e : V, ((Mσ.pt ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (M.pt e).left) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieSigma.lieModel_fibre | exact GlobalTheory.CompanionTheory.Ar.LieSigma.lieModel_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.LieSigma.lieModel_fibre <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOverLocalRing
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOverLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieFreeSmooth

theorem lieModel_free_of_smooth : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom →
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E]
      [Module R E] (M : LieModel G x E), ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R E) := by
  intro S G _ hG R _ _ x E _ _ M
  haveI := hG
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.lie_model_finite_projective S G R x E M
  haveI := hfin
  haveI := hproj
  haveI : Module.Free R E := Module.free_of_flat_of_isLocalRing
  exact ⟨_, ⟨Module.finBasis R E⟩⟩

end GlobalTheory.CompanionTheory.Ar.LieFreeSmooth
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOverLocalRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_free_over_local_ring : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R E) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieFreeSmooth.lieModel_free_of_smooth | exact GlobalTheory.CompanionTheory.Ar.LieFreeSmooth.lieModel_free_of_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.LieFreeSmooth.lieModel_free_of_smooth <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RingOfIntegersHomInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem ringOfIntegers_hom_injective {F : Type} [Field F] [NumberField F] {R : Type} [Field R] [CharZero R]
    (a : 𝓞 F →+* R) : Function.Injective a := by
  have hI : (RingHom.ker a).comap (algebraMap ℤ (𝓞 F)) = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    have h0 : ((n : ℤ) : R) = 0 := by
      have h1 : a (algebraMap ℤ (𝓞 F) n) = 0 := hn
      simpa using h1
    have h2 : n = 0 := by exact_mod_cast h0
    simp [h2]
  exact (RingHom.injective_iff_ker_eq_bot a).2 (Ideal.eq_bot_of_comap_eq_bot hI)

theorem exists_ringHom_extend {F : Type} [Field F] [NumberField F] {R : Type} [Field R] [CharZero R]
    (a : 𝓞 F →+* R) : ∃ κ : F →+* R, κ.comp (algebraMap (𝓞 F) F) = a :=
  ⟨IsFractionRing.lift (ringOfIntegers_hom_injective a),
    RingHom.ext fun x => IsFractionRing.lift_algebraMap (ringOfIntegers_hom_injective a) x⟩

theorem exists_isOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X), 𝔐.Interior z → ∃ (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X), IsOver 𝔐 z κ p := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 z hz
  have := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  let a : 𝓞 c.F →+* ℂ := (Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom
  have ha : z ≫ 𝔐.f ≫ Y.s = spMap a := by
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨κ, hκ⟩ := exists_ringHom_extend a
  have hc : (z ≫ 𝔐.f) ≫ Y.s = spMap κ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Category.assoc, ha, ← hκ, Chg.spMap_comp']
  let w : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift (z ≫ 𝔐.f) (spMap κ) hc
  have hw₁ : w ≫ pullback.fst _ _ = z ≫ 𝔐.f := pullback.lift_fst _ _ _
  have hw₂ : w ≫ pullback.snd _ _ = spMap κ := pullback.lift_snd _ _ _
  have := Y.jQ_open
  have hr : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨u, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, hw₁, Scheme.Hom.comp_apply]
    have hu : u = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hu
    exact (abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 _).2 hz
  let x : Sp ℂ ⟶ Xo.XF c := IsOpenImmersion.lift Y.jQ w hr
  have hx : x ≫ Y.jQ = w := IsOpenImmersion.lift_fac _ _ _
  refine ⟨κ, x ≫ pullback.fst _ _, x, ?_, rfl, ?_⟩
  · rw [Model.j, ← Category.assoc, hx, hw₁]
  · rw [← Y.jQ_over, ← Category.assoc, hx, hw₂]

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCoordField
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCoordField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.CoverEff

section Gen

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem unitAt_div_of_isGenAt {Λ : Lat ξ Ω} {p : Cpt ξ} {s s' : Ω} (h : Λ.IsGenAt p s) (h' : Λ.IsGenAt p s') :
    unitAt ξ p (s' / s) := by
  obtain ⟨h0, e⟩ := h
  obtain ⟨h0', e'⟩ := h'
  have m1 : s' ∈ Submodule.span (regAt ξ p) {s} := by
    rw [← e, e']; exact Submodule.mem_span_singleton_self s'
  have m2 : s ∈ Submodule.span (regAt ξ p) {s'} := by
    rw [← e', e]; exact Submodule.mem_span_singleton_self s
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 m1
  obtain ⟨r', hr'⟩ := Submodule.mem_span_singleton.1 m2
  have hr1 : (r : Ω) * s = s' := hr
  have hr2 : (r' : Ω) * s' = s := hr'
  refine ⟨div_ne_zero h0' h0, ?_, ?_⟩
  · rw [(div_eq_iff h0).2 hr1.symm]; exact r.2
  · rw [inv_div, (div_eq_iff h0').2 hr2.symm]; exact r'.2

theorem tens_isGenAt {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} (a : I → ℤ) {p : Cpt ξ} {s : I → Ω}
    (h : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (h i).1, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨s', hs', rfl⟩
    have hu : unitAt ξ p (∏ i, (s' i / s i) ^ a i) :=
      unitAt.prod _ fun i _ => (unitAt_div_of_isGenAt (h i) (hs' i)).zpow _
    have e : ∏ i, s' i ^ a i = (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← mul_zpow, div_mul_cancel₀ _ (h i).1]
    rw [e]
    exact Submodule.mem_span_singleton.2 ⟨⟨_, hu.2.1⟩, rfl⟩
  · refine Submodule.span_mono ?_
    rintro _ rfl
    exact ⟨s, h, rfl⟩

theorem exists_gen_of_tens {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} {a : I → ℤ} {p : Cpt ξ} {t : Ω}
    (h : (Lat.tens Λ a).IsGenAt p t) : ∃ s : I → Ω, ∀ i, (Λ i).IsGenAt p (s i) := by
  by_contra hn
  have hE : {t | ∃ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) ∧ t = ∏ i, s i ^ a i} = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ ⟨s, hs, _⟩ => hn ⟨s, hs⟩
  have m : t ∈ (Lat.tens Λ a) p := by
    rw [h.2]; exact Submodule.mem_span_singleton_self t
  have m' : t ∈ Submodule.span (regAt ξ p) (∅ : Set Ω) := by
    rw [← hE]; exact m
  rw [Submodule.span_empty, Submodule.mem_bot] at m'
  exact h.1 m'

theorem unitAt_of_mul {p : Cpt ξ} {a b : Ω} (hab : unitAt ξ p (a * b)) (hb : unitAt ξ p b) : unitAt ξ p a := by
  have ha : a ≠ 0 := left_ne_zero_of_mul hab.1
  refine ⟨ha, ?_, ?_⟩
  · have e : a = a * b * b⁻¹ := by field_simp [hb.1]
    rw [e]; exact mul_mem hab.2.1 hb.2.2
  · have e : a⁻¹ = (a * b)⁻¹ * b := by field_simp [hb.1]
    rw [e]; exact mul_mem hab.2.2 hb.2.1

end Gen

section Below

variable {X X₀ : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀}

theorem inChart_below {p : Cpt ξ} {p₀ : Cpt ξ₀} (i : Ω₀ →+* Ω)
    (hU : ∀ a : Ω₀, a ∈ regAt ξ₀ p₀ → unitAt ξ p (i a) → unitAt ξ₀ p₀ a)
    (hR : ∀ a : Ω₀, a ∈ regAt ξ₀ p₀ → i a ∈ regAt ξ p) {κ : Type} {x : κ → Ω₀} {a a₀ : κ}
    (h₀ : InChart ξ₀ x a₀ p₀) (h : InChart ξ (fun k => i (x k)) a p) : InChart ξ₀ x a p₀ := by
  have hx : x a ≠ 0 := fun e => h.1 (by simp [e])
  have hu : unitAt ξ₀ p₀ (x a / x a₀) := by
    refine hU _ (h₀.2 a) ⟨(map_ne_zero i).2 (div_ne_zero hx h₀.1), hR _ (h₀.2 a), ?_⟩
    rw [← map_inv₀, inv_div, map_div₀]
    exact h.2 a₀
  refine ⟨hx, fun c => ?_⟩
  have e : x c / x a = x c / x a₀ * (x a / x a₀)⁻¹ := by
    have := h₀.1
    field_simp
  rw [e]
  exact mul_mem (h₀.2 c) hu.2.2

end Below

theorem rootLat_isGenAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y}
    (Fl : 𝔐.Flag) (r : RootIx D) {p : Cpt 𝔐.ξ} {g : Ω}
    (hg : ((𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2).IsGenAt p g) :
    (Fl.rootLat r).IsGenAt p (g ^ HodgeCpt.rootSgn D r) := by
  have := tens_isGenAt (I := Unit)
    (Λ := fun _ => (𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2)
    (fun _ => HodgeCpt.rootSgn D r) (p := p) (s := fun _ => g) fun _ => hg
  simpa [HodgeCpt.Flag.rootLat] using this

theorem section_on_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (S₀ S : Finset ℕ) (o : RootOrigin Y S₀ R Fx) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (bk : R.K → K) (bx : ∀ k, R.ι k ≃ J (bk k)) (𝔐 : HodgeCpt Y S y) (i : R.Ω →+* Ω) (h : 𝔐.X ⟶ o.𝔐.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o.𝔐.ξ h i) (Fl : 𝔐.Flag) (xdeg : RootIx D → K → ℤ) (e : RootIx D → Ω), (∀ k a, y ⟨bk k, bx k a⟩ = i (R.y ⟨k, a⟩)) → GenPull o.Fl Fl i hd → Fl.RootLines xdeg e → (∀ (p : Cpt 𝔐.ξ) (a : R.Ω), a ∈ regAt o.𝔐.ξ (pushCpt hd p) → unitAt 𝔐.ξ p (i a) → unitAt o.𝔐.ξ (pushCpt hd p) a) → (∀ (p : Cpt 𝔐.ξ) (a : R.Ω), a ∈ regAt o.𝔐.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ x : 𝔐.X, x ∈ abLocus 𝔐.t.G ↔ h x ∈ abLocus o.𝔐.t.G) → ∀ p : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r p) → ∀ (a : Fin (Fx.m + 1)) (t : Ω), InChart 𝔐.ξ (fun i' => (i.comp o.g) (Fx.yf i')) a p → (Lat.tens Fl.rootLat fun r => -Fx.n r).IsGenAt p t → (i.comp o.g) Fx.sE * (i.comp o.g) (Fx.yf a) ^ Fx.q' / t ∈ regAt 𝔐.ξ p ∧ (p.1 ∉ abLocus 𝔐.t.G → ¬ unitAt 𝔐.ξ p ((i.comp o.g) Fx.sE * (i.comp o.g) (Fx.yf a) ^ Fx.q' / t)) := by
  intro E _ _ _ H D l Xo c O _ β Y Sys Fx R S₀ S o Ω _ K _ J _ y bk bx 𝔐 i h hd Fl xdeg e hy hG hL hU hR hab p hp a t
    hch ht
  have hp0 : ∀ r : ℕ, r.Prime → ¬ InFibre o.𝔐.ξ r (pushCpt hd p) := by
    intro r hr hf
    apply hf
    have u : unitAt 𝔐.ξ p (r : Ω) := not_not.1 (hp r hr)
    exact hU p (r : R.Ω) (natCast_mem _ r) (by rw [map_natCast]; exact u)
  obtain ⟨c₀, hc₀⟩ := o.𝔐.tie.cover (pushCpt hd p)
  have hprod : ∀ k, R.y ⟨k, c₀ k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hc₀.1) k (Finset.mem_univ k)
  have ya₀ : o.g (Fx.yf (o.ix.symm (c₀ o.k₀))) = R.y ⟨o.k₀, c₀ o.k₀⟩ := by
    rw [← o.y_eq, Equiv.apply_symm_apply]
  have hch₀ : InChart o.𝔐.ξ (fun i' => o.g (Fx.yf i')) (o.ix.symm (c₀ o.k₀)) (pushCpt hd p) := by
    refine ⟨?_, fun j => ?_⟩
    · show o.g (Fx.yf (o.ix.symm (c₀ o.k₀))) ≠ 0
      rw [ya₀]; exact hprod _
    · show o.g (Fx.yf j) / o.g (Fx.yf (o.ix.symm (c₀ o.k₀))) ∈ _
      rw [ya₀, ← o.y_eq]
      exact Lat.block_ratio_mem hc₀ o.k₀ (o.ix j)
  have hcha : InChart o.𝔐.ξ (fun i' => o.g (Fx.yf i')) a (pushCpt hd p) :=
    inChart_below i (hU p) (hR p) hch₀ hch
  have gens : ∀ r : RootIx D, ∃ g : R.Ω, ((o.𝔐.V (HodgeCpt.rootIdx D r).1).gr (o.Fl.b (HodgeCpt.rootIdx D r).1)
      (HodgeCpt.rootIdx D r).2).IsGenAt (pushCpt hd p) g := by
    intro r
    have hgen : (o.Fl.rootLat r).IsGenAt (pushCpt hd p) ((∏ k, R.y ⟨k, c₀ k⟩ ^ R.xdeg r k) • o.e r) :=
      ⟨smul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hprod k)) (o.lines r).1,
        (o.lines r).2 _ trivial c₀ hc₀⟩
    obtain ⟨s, hs⟩ := exists_gen_of_tens hgen
    exact ⟨s (), hs ()⟩
  choose g hg using gens
  have ht₀ := tens_isGenAt (fun r => -Fx.n r) fun r => rootLat_isGenAt o.Fl r (hg r)
  have ht₁ : (Lat.tens Fl.rootLat fun r => -Fx.n r).IsGenAt p
      (i (∏ r, (g r ^ HodgeCpt.rootSgn D r) ^ (-Fx.n r))) := by
    have := tens_isGenAt (Λ := Fl.rootLat) (fun r => -Fx.n r) fun r =>
      rootLat_isGenAt Fl r (hG p hp _ _ _ (hg r))
    simpa only [map_prod, map_zpow₀] using this
  have hv := unitAt_div_of_isGenAt ht ht₁
  obtain ⟨hreg, hnu⟩ := o.eff (pushCpt hd p) hp0 a _ hcha ht₀
  have key : (i.comp o.g) Fx.sE * (i.comp o.g) (Fx.yf a) ^ Fx.q' / t =
      i (o.g Fx.sE * o.g (Fx.yf a) ^ Fx.q' / ∏ r, (g r ^ HodgeCpt.rootSgn D r) ^ (-Fx.n r)) *
        (i (∏ r, (g r ^ HodgeCpt.rootSgn D r) ^ (-Fx.n r)) / t) := by
    have h1 := ht₁.1
    have h2 := ht.1
    rw [map_div₀ i (o.g Fx.sE * o.g (Fx.yf a) ^ Fx.q'), div_mul_div_cancel₀ h1, map_mul, map_pow]
    rfl
  rw [key]
  refine ⟨mul_mem (hR p _ hreg) hv.2.1, fun hnab hu => ?_⟩
  exact hnu (fun hm => hnab ((hab p.1).2 hm)) (hU p _ hreg (unitAt_of_mul hu hv))

end GlobalTheory.CompanionTheory.Ar.Chg.CoverEff
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCoordFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_coord_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (S₀ S : Finset ℕ) (o : RootOrigin Y S₀ R Fx) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (bk : R.K → K) (bx : ∀ k, R.ι k ≃ J (bk k)) (𝔐 : HodgeCpt Y S y) (i : R.Ω →+* Ω) (h : 𝔐.X ⟶ o.𝔐.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o.𝔐.ξ h i) (Fl : 𝔐.Flag) (xdeg : RootIx D → K → ℤ) (e : RootIx D → Ω), (∀ k a, y ⟨bk k, bx k a⟩ = i (R.y ⟨k, a⟩)) → GenPull o.Fl Fl i hd → Fl.RootLines xdeg e → (∀ (p : Cpt 𝔐.ξ) (a : R.Ω), a ∈ regAt o.𝔐.ξ (pushCpt hd p) → unitAt 𝔐.ξ p (i a) → unitAt o.𝔐.ξ (pushCpt hd p) a) → (∀ (p : Cpt 𝔐.ξ) (a : R.Ω), a ∈ regAt o.𝔐.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ x : 𝔐.X, x ∈ abLocus 𝔐.t.G ↔ h x ∈ abLocus o.𝔐.t.G) → ∀ p : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r p) → ∀ (a : Fin (Fx.m + 1)) (t : Ω), InChart 𝔐.ξ (fun i' => (i.comp o.g) (Fx.yf i')) a p → (Lat.tens Fl.rootLat fun r => -Fx.n r).IsGenAt p t → (i.comp o.g) Fx.sE * (i.comp o.g) (Fx.yf a) ^ Fx.q' / t ∈ regAt 𝔐.ξ p ∧ (p.1 ∉ abLocus 𝔐.t.G → ¬ unitAt 𝔐.ξ p ((i.comp o.g) Fx.sE * (i.comp o.g) (Fx.yf a) ^ Fx.q' / t)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.section_on_cover | exact GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.section_on_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.section_on_cover <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderIsHopfOrderNoetherian
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderIsHopfOrderNoetherian
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.btOrder_isHopfOrder_noetherian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), IsHopfOrder (Γ.btOrder ⊤) := by
  first | exact @PositivityTheory.UnitarySelfGeneration.bt_hopf | exact PositivityTheory.UnitarySelfGeneration.bt_hopf
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderIsHopfOrderNoetherianStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.btOrder_isHopfOrder_noetherian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), IsHopfOrder (Γ.btOrder ⊤) := by
  exact @GlobalTheory.CompanionTheory.Relay.btOrder_isHopfOrder_noetherian
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsHodgeTateFunctional
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsHodgeTateFunctional
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_hodge_tate_functional : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ), ∃ w : Module.Dual R L, Γ.IsHT i M N χ w := by
  first | exact @PositivityTheory.UnitarySelfGeneration.ht_exists | exact PositivityTheory.UnitarySelfGeneration.ht_exists
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsHodgeTateFunctionalStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hodge_tate_functional : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ), ∃ w : Module.Dual R L, Γ.IsHT i M N χ w := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_hodge_tate_functional | exact GlobalTheory.CompanionTheory.Relay.exists_hodge_tate_functional | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_hodge_tate_functional <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLieModelExists
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.QuotientUniformizationModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace PositivityTheory.Xgn.QuotientUniformizationModel

def modelOfEquiv {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {F F' : Type} [AddCommGroup F] [Module R F] [AddCommGroup F'] [Module R F']
    (M : LieModel G x F) (e : F' ≃ₗ[R] F) : LieModel G x F' where
  pt v := M.pt (e v)
  tan v := M.tan _
  inj := M.inj.comp e.injective
  onto v hv := by
    obtain ⟨w, h⟩ := M.onto v hv
    exact ⟨e.symm w, by simpa using h⟩
  add v w := by rw [map_add (f := _), M.add]
  smul c v := by rw [map_smul, M.smul]

theorem exists_model (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (R R' : Type)
    [CommRing R] [CommRing R'] (c : R →+* R') (x : Sp R ⟶ S) (g : ℕ) (M : LieModel G x (Fin g → R))
    (y : Sp R' ⟶ S) (hy : y = spMap c ≫ x) :
    ∃ Mz : LieModel G y (Fin g → R'), ∀ e : Fin g → R, ((Mz.pt fun i => c (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt e).left) := by
  subst hy
  obtain ⟨F, _, _, ⟨M'⟩⟩ := lieModel_exists _ G R' (spMap c ≫ x)
  obtain ⟨j, hj, -⟩ := LieBaseChange.existsUnique_semilinear_lifts S G R R' c x _ F M M'
  letI : Algebra R R' := c.toAlgebra
  letI : Module R F := Module.compHom F c
  haveI : IsScalarTower R R' F := ⟨fun r s f => by
    change (c r * s) • f = c r • s • f
    rw [mul_smul]⟩
  let j' : (Fin g → R) →ₗ[R] F :=
    { toFun := j, map_add' := j.map_add, map_smul' := fun r e => j.map_smulₛₗ r e }
  have hb : IsBaseChange R' j' := lieModel_isBaseChange S G R R' x _ F M M' j' hj
  refine ⟨modelOfEquiv M' ((TensorProduct.piScalarRight R R' R' (Fin g)).symm.trans hb.equiv), fun e => ?_⟩
  have h1 : (TensorProduct.piScalarRight R R' R' (Fin g)).symm (fun i => c (e i)) = (1 : R') ⊗ₜ[R] e := by
    rw [LinearEquiv.symm_apply_eq, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    funext i
    change c (e i) = c (e i) * 1
    rw [_root_.mul_one]
  have h2 : ((TensorProduct.piScalarRight R R' R' (Fin g)).symm.trans hb.equiv) (fun i => c (e i)) = j e := by
    rw [LinearEquiv.trans_apply, h1, IsBaseChange.equiv_tmul, one_smul]
    rfl
  change ((M'.pt (((TensorProduct.piScalarRight R R' R' (Fin g)).symm.trans hb.equiv)
    (fun i => c (e i)))).left ≫ 𝟙 _) = _
  rw [h2]
  exact hj e

end PositivityTheory.Xgn.QuotientUniformizationModel

theorem PositivityTheory.Xgn.quotient_uniformization_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (u : Fin n → ℂ), ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left) := by
  intro E _ _ _ H D l Xo σ n a C u
  have := C.t.semi.smooth
  exact PositivityTheory.Xgn.QuotientUniformizationModel.exists_model _ C.t.G C.R ℂ (C.ψ u) (𝟙 _) C.g C.M _
    (Category.comp_id _).symm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLieModelExists
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif

theorem frame_lieModel_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (u : Fin n → ℂ), ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left) :=
  @PositivityTheory.Xgn.quotient_uniformization_model

end GlobalTheory.CompanionTheory.Ar.QuotUnif
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLieModelExistsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_chart_lie_model_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (u : Fin n → ℂ), ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.frame_lieModel_fibre | exact GlobalTheory.CompanionTheory.Ar.QuotUnif.frame_lieModel_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUnif.frame_lieModel_fibre <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsInCoordRatioField
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsInCoordRatioField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CstChart

theorem germ_top_stalk {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {q : X}
    (hq : ξ (IsLocalRing.closedPoint Ω) ⤳ q) :
    X.presheaf.germ ⊤ q (show q ∈ (⊤ : X.Opens) from trivial) ≫ X.presheaf.stalkSpecializes hq ≫
        Scheme.stalkClosedPointTo ξ = ξ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.germ_stalkClosedPointTo]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
  have e : ∀ (f : (⊤ : (Spec (CommRingCat.of Ω)).Opens) ⟶ ξ ⁻¹ᵁ ⊤),
      (Spec (CommRingCat.of Ω)).presheaf.map f.op = 𝟙 _ := fun f => (Spec (CommRingCat.of Ω)).presheaf.map_id _
  erw [e]
  simp

theorem ringHom_mem_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    {O : Type} [CommRing O] (φ : O →+* Ω) (s : X ⟶ Spec (CommRingCat.of O))
    (h : ξ ≫ s = Spec.map (CommRingCat.ofHom φ)) (p : Cpt ξ) (o : O) : φ o ∈ regAt ξ p := by
  obtain ⟨q, hq⟩ := p
  refine ⟨X.presheaf.germ ⊤ q (show q ∈ (⊤ : X.Opens) from trivial)
    (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)), ?_⟩
  have h1 := germ_top_stalk ξ hq
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ s.appTop ≫ ξ.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom φ := by
    have : s.appTop ≫ ξ.appTop = (ξ ≫ s).appTop := by simp
    rw [reassoc_of% this, h]
    simp
  have h3 := congrArg (fun f => f.hom o) h2
  have h4 := congrArg (fun f => f.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3 h4
  rw [CommRingCat.hom_ofHom] at h3
  refine Eq.trans ?_ (h4.trans h3)
  rfl

theorem segre_adjoin_le {Ω : Type} [Field Ω] [CharZero Ω] {K : Type} [Fintype K] {J : K → Type}
    (y : (Σ k, J k) → Ω) (cc : (k : K) → J k) :
    Algebra.adjoin ℤ (Set.range fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, cc k⟩) ≤
      (Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, cc p.1⟩)).restrictScalars ℤ := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨c', rfl⟩
  show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, cc k⟩ ∈
    Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, cc p.1⟩)
  rw [← Finset.prod_div_distrib]
  exact Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, c' k⟩, rfl⟩

theorem cst_mem_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (cc : (k : K) → J k), (∀ k, y ⟨k, cc k⟩ ≠ 0) → ∀ r : c.F, 𝔐.cst r ∈ Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, cc p.1⟩) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 cc hcc r
  have hx : (∏ k, y ⟨k, cc k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hcc k
  have hint : ∀ a : 𝓞 c.F, 𝔐.cst (algebraMap (𝓞 c.F) c.F a) ∈
      Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, cc p.1⟩) := fun a =>
    segre_adjoin_le y cc ((𝔐.tie.ring cc hx _).2 fun p _ =>
      ringHom_mem_regAt 𝔐.ξ (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) (𝔐.f ≫ Y.s) 𝔐.cst_over p a)
  haveI : FiniteDimensional ℚ c.F := c.fin
  have halg : IsAlgebraic ℤ r := (IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).2 (Algebra.IsAlgebraic.isAlgebraic r)
  obtain ⟨n, hn, hr⟩ := halg.exists_integral_multiple
  have hn' : (n : Ω) ≠ 0 := Int.cast_ne_zero.2 hn
  have e : 𝔐.cst r = algebraMap ℚ Ω (n : ℚ)⁻¹ *
      𝔐.cst (algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) (n • r) hr)) := by
    rw [IsIntegralClosure.algebraMap_mk', zsmul_eq_mul, map_mul, map_intCast]
    simp [hn']
  rw [e]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hint _)

end GlobalTheory.CompanionTheory.Ar.CstChart
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsInCoordRatioFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constants_in_coord_ratio_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (cc : (k : K) → J k), (∀ k, y ⟨k, cc k⟩ ≠ 0) → ∀ r : c.F, 𝔐.cst r ∈ Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, cc p.1⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CstChart.cst_mem_chart | exact GlobalTheory.CompanionTheory.Ar.CstChart.cst_mem_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.CstChart.cst_mem_chart <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqBtOrderTop
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqBtOrderTop
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.btOrder_eq_btOrder_top : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.btOrder U = Γ.btOrder ⊤ := by
  first | exact @PositivityTheory.UnitarySelfGeneration.bt_sub_eq_top | exact PositivityTheory.UnitarySelfGeneration.bt_sub_eq_top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqBtOrderTopStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.btOrder_eq_btOrder_top : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.btOrder U = Γ.btOrder ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.btOrder_eq_btOrder_top | exact GlobalTheory.CompanionTheory.Relay.btOrder_eq_btOrder_top | (intros; apply GlobalTheory.CompanionTheory.Relay.btOrder_eq_btOrder_top <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SandwichPointOverFieldExt
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SandwichPointOverFieldExt
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem hodge_tate_model_point_sandwich : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (κ : Ω), HTFree 𝔐 p → Sandwich 𝔐 p κ → ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O' : Type) [CommRing O'] [IsLocalRing O'] [Algebra O' C], v.Integers O' → v (p : C) < 1 → ∀ (z : Sp O' ⟶ 𝔐.X) (EC : Type) [AddCommGroup EC] [Module C EC] [Module O' EC] [IsScalarTower O' C EC] (MC : LieModel 𝔐.t.G (Spec.map (CommRingCat.ofHom (algebraMap O' C)) ≫ z) EC) (ρC : 𝓞 E →+* Module.End C EC) (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* O') (κz : O'), MC.IsActOf 𝔐.t.act.act ρC → (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt 𝔐.ξ z (𝔐.emb s a) (σ a)) → GlobalTheory.CompanionTheory.Ar.ValAt 𝔐.ξ z κ κz → 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap O' C).comp σ)).restrictScalars O' ≤ 𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC ∧ (∀ w ∈ 𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC, κz • w ∈ 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap O' C).comp σ)).restrictScalars O') ∧ (𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC).FG :=
  PositivityTheory.HtPt.Gh.hodge_tate_free_sandwich

end GlobalTheory.CompanionTheory.Ar.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SandwichPointOverFieldExtStatement
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sandwich_point_over_field_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (κ : Ω), HTFree 𝔐 p → Sandwich 𝔐 p κ → ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O' : Type) [CommRing O'] [IsLocalRing O'] [Algebra O' C], v.Integers O' → v (p : C) < 1 → ∀ (z : Sp O' ⟶ 𝔐.X) (EC : Type) [AddCommGroup EC] [Module C EC] [Module O' EC] [IsScalarTower O' C EC] (MC : LieModel 𝔐.t.G (Spec.map (CommRingCat.ofHom (algebraMap O' C)) ≫ z) EC) (ρC : 𝓞 E →+* Module.End C EC) (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* O') (κz : O'), MC.IsActOf 𝔐.t.act.act ρC → (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt 𝔐.ξ z (𝔐.emb s a) (σ a)) → GlobalTheory.CompanionTheory.Ar.ValAt 𝔐.ξ z κ κz → 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap O' C).comp σ)).restrictScalars O' ≤ 𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC ∧ (∀ w ∈ 𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC, κz • w ∈ 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap O' C).comp σ)).restrictScalars O') ∧ (𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC).FG := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.hodge_tate_model_point_sandwich | exact GlobalTheory.CompanionTheory.Ar.HT.hodge_tate_model_point_sandwich | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.hodge_tate_model_point_sandwich <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorusExtensionFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorusExtensionFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar

theorem exists_finite_torusExtension_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S), ∃ (L' : Type) (_ : Field L') (_ : Algebra L L'), FiniteDimensional L L' ∧ Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap L L') ≫ z)).obj G)) := by
  intro S G _ hG L _ _ z
  have h₀ : IsSemiAbelian ((Over.pullback z).obj G) := IsSemiAbelian.pullback _ G hG
  haveI := h₀.smooth
  obtain ⟨T⟩ := h₀.fibres (AlgebraicClosure L) (spMap (algebraMap L (AlgebraicClosure L)))
  obtain ⟨k', hk, ⟨T'⟩⟩ := GlobalTheory.exists_finite_torusExtension L (AlgebraicClosure L) ((Over.pullback z).obj G)
    inferInstance h₀.quasiCompact h₀.separated ⟨T⟩
  refine ⟨k', inferInstance, inferInstance, hk, ?_⟩
  haveI : IsMonHom (pullCompIso (spMap (algebraMap L k')) z G).symm.hom :=
    inferInstanceAs (IsMonHom (pullCompIso (spMap (algebraMap L k')) z G).inv)
  exact ⟨torusExtOfIso (pullCompIso (spMap (algebraMap L k')) z G).symm T'⟩

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorusExtensionFiniteStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_extension_finite : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S), ∃ (L' : Type) (_ : Field L') (_ : Algebra L L'), FiniteDimensional L L' ∧ Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap L L') ≫ z)).obj G)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_finite_torusExtension_fibre | exact GlobalTheory.CompanionTheory.Ar.exists_finite_torusExtension_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_finite_torusExtension_fibre <;> assumption)
end
end

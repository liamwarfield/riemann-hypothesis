module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerOperatorInjectiveEigenvector
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedVectorCoefficientLeftInvariantLevelGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumInnerProductFinsuppLocalCosetFamilies
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLIwasawaDecompositionStandardParabolic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightTranslateOperatorMulLocalOperatorHasSum
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightTranslateOperatorMulLocalOperatorHasSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.Eu

section Local
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem unitaryAdeleMatrix_injective (V : HSp D) : Function.Injective (Formalism.L2.Theta.mt V) := by
  intro g h hgh
  have h1 : matHom V g = matHom V h := Units.ext hgh
  exact (HR (AF D.host.F) D.sp.cm.sig V.gram).subtype_injective h1

theorem unitaryAdeleMatrix_mul (V : HSp D) (g h : GA D V) : Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul]; rfl

theorem unitaryAdeleMatrix_one (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := rfl

theorem supportedAtIdempotent_iff_smul_matrix_sub_one (V : HSp D) (f : AE D) (g : GA D V) :
    SuppF V f g ↔ f • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1 := by
  constructor
  · intro h; ext a b; rw [Matrix.smul_apply, smul_eq_mul]; exact h a b
  · intro h a b; have := congrFun (congrFun h a) b; rw [Matrix.smul_apply, smul_eq_mul] at this; exact this

theorem supportedAtAdeleIdempotent_mul_closed (V : HSp D) (f : AE D) {g h : GA D V} (hg : SuppF V f g) (hh : SuppF V f h) :
    SuppF V f (g * h) := by
  rw [supportedAtIdempotent_iff_smul_matrix_sub_one] at *
  have e : Formalism.L2.Theta.mt V (g * h) - 1 = (Formalism.L2.Theta.mt V g - 1) * (Formalism.L2.Theta.mt V h - 1) +
      (Formalism.L2.Theta.mt V g - 1) + (Formalism.L2.Theta.mt V h - 1) := by
    rw [unitaryAdeleMatrix_mul]; noncomm_ring
  rw [e, smul_add, smul_add, ← Matrix.smul_mul, hg, hh]

theorem supportedAtAdeleIdempotent_inv_closed (V : HSp D) (f : AE D) {g : GA D V} (hg : SuppF V f g) : SuppF V f g⁻¹ := by
  rw [supportedAtIdempotent_iff_smul_matrix_sub_one] at *
  have hm : Formalism.L2.Theta.mt V g⁻¹ * Formalism.L2.Theta.mt V g = 1 := by rw [← unitaryAdeleMatrix_mul, inv_mul_cancel]; rfl
  have e : Formalism.L2.Theta.mt V g⁻¹ - 1 = -(Formalism.L2.Theta.mt V g⁻¹ * (Formalism.L2.Theta.mt V g - 1)) := by
    rw [Matrix.mul_sub, hm]; noncomm_ring
  rw [e, smul_neg, ← Matrix.mul_smul, hg]

theorem supportedAtIdempotent_zero_eq_one (V : HSp D) {g : GA D V} (hg : SuppF V 0 g) : g = 1 := by
  rw [supportedAtIdempotent_iff_smul_matrix_sub_one, zero_smul] at hg
  apply unitaryAdeleMatrix_injective V
  rw [unitaryAdeleMatrix_one]
  exact (sub_eq_zero.mp hg.symm)

theorem rightTranslatePairingOperator_spec {R : RealDat D A Ks} {i : Fin D.R.m} (hTL : TransLaws R i) {γ : GA D (Wc D i)}
    (hγ : γ ∈ GfC (Wc D i)) : ∀ x y, trPair R i γ x y = ⟪x, Bop R i γ y⟫_ℂ := by
  have hex := hTL.2.2.1 γ hγ
  unfold Bop
  rw [dite_eq_left hex]
  exact hex.choose_spec.2

theorem rightTranslatePairingOperator_eq_of_forms {R : RealDat D A Ks} {i : Fin D.R.m} (hTL : TransLaws R i) {γ : GA D (Wc D i)}
    (hγ : γ ∈ GfC (Wc D i)) (B : (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H)
    (hB : ∀ x y, trPair R i γ x y = ⟪x, B y⟫_ℂ) : Bop R i γ = B := by
  apply ContinuousLinearMap.ext; intro y
  apply ext_inner_left ℂ; intro x
  rw [← rightTranslatePairingOperator_spec hTL hγ x y, hB]

theorem finite_mul_liftLevel_mem_finite {R : RealDat D A Ks} {i : Fin D.R.m} (hTL : TransLaws R i) {γ k : GA D (Wc D i)}
    (hγ : γ ∈ GfC (Wc D i)) (hk : k ∈ levW R i) (hγk : γ * k ∈ GfC (Wc D i)) : Bop R i (γ * k) = Bop R i γ := by
  apply rightTranslatePairingOperator_eq_of_forms hTL hγk
  intro x y
  have := hTL.2.2.2.1 γ hγ 1 (levW R i).one_mem k hk x y
  rw [one_mul] at this
  rw [this, rightTranslatePairingOperator_spec hTL hγ]

theorem rightTranslatePairingOperator_hecke_relation {R : RealDat D A Ks} {i : Fin D.R.m} (hTL : TransLaws R i) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {f : AE D} (hf : IsFinIdem D v f) {α : GA D (Wc D i)} (hα : SuppF (Wc D i) f α) (C : Finset (GA D (Wc D i)))
    (hCs : ∀ δ ∈ C, SuppF (Wc D i) f δ)
    (hC : IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C) {γ : GA D (Wc D i)}
    (hγ : γ ∈ GfC (Wc D i)) :
    Bop R i γ * ∑ δ ∈ C, Bop R i δ = ∑ δ ∈ C, Bop R i (γ * δ) := by
  have hCG : ∀ δ ∈ C, δ ∈ GfC (Wc D i) := fun δ hδ => (hC.1 δ hδ).1
  apply ContinuousLinearMap.ext; intro y
  obtain ⟨y', -, hy'⟩ := hTL.2.1 v f hf α hα C hCs hC y
  have e1 : y' = ∑ δ ∈ C, Bop R i δ y := by
    apply ext_inner_left ℂ; intro x
    rw [inner_sum, ← hTL.2.2.2.2.2 x y', hy' 1 (GfC (Wc D i)).one_mem x]
    refine Finset.sum_congr rfl fun δ hδ => ?_
    rw [one_mul, rightTranslatePairingOperator_spec hTL (hCG δ hδ)]
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply, ← e1]
  apply ext_inner_left ℂ; intro x
  rw [inner_sum, ← rightTranslatePairingOperator_spec hTL hγ, hy' γ hγ x]
  refine Finset.sum_congr rfl fun δ hδ => ?_
  rw [rightTranslatePairingOperator_spec hTL (mul_mem hγ (hCG δ hδ))]

def mkLX (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D (Wc D i))
    (hg : g ∈ locSet R i v) : LX R i v :=
  Quotient.mk _ ⟨g, hg⟩

theorem levelCosetRepresentative_mem_supportedSet {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x : LX R i v) :
    rep x ∈ locSet R i v := (Quotient.out x).2

theorem placeSupportedLevelCoset_representative_eq {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x : LX R i v) :
    mkLX R i v (rep x) (levelCosetRepresentative_mem_supportedSet x) = x := Quotient.out_eq x

theorem placeSupportedLevelCoset_eq_iff {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {g g' : GA D (Wc D i)} (hg : g ∈ locSet R i v) (hg' : g' ∈ locSet R i v) :
    mkLX R i v g hg = mkLX R i v g' hg' ↔ g⁻¹ * g' ∈ levW R i := by
  constructor
  · intro h
    have h2 := Quotient.exact h
    exact QuotientGroup.leftRel_apply.mp h2
  · intro h
    apply Quotient.sound
    exact QuotientGroup.leftRel_apply.mpr h

theorem representative_placeSupportedLevelCoset_rel {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {g : GA D (Wc D i)} (hg : g ∈ locSet R i v) : ∃ k ∈ levW R i, rep (mkLX R i v g hg) = g * k := by
  have h := placeSupportedLevelCoset_representative_eq (mkLX R i v g hg)
  rw [placeSupportedLevelCoset_eq_iff] at h
  refine ⟨g⁻¹ * rep (mkLX R i v g hg), ?_, by group⟩
  have := (levW R i).inv_mem h
  simpa using this

theorem levelCoset_eq_iff_representative_rel {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x y : LX R i v) :
    x = y ↔ (rep x)⁻¹ * rep y ∈ levW R i := by
  constructor
  · rintro rfl; rw [inv_mul_cancel]; exact (levW R i).one_mem
  · intro h
    have := (placeSupportedLevelCoset_eq_iff (levelCosetRepresentative_mem_supportedSet x) (levelCosetRepresentative_mem_supportedSet y)).mpr h
    rwa [placeSupportedLevelCoset_representative_eq, placeSupportedLevelCoset_representative_eq] at this

theorem eq_trivialLevelCoset_iff_representative_mem {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x : LX R i v) :
    x = lx0 R i v ↔ rep x ∈ levW R i := by
  have e : lx0 R i v = mkLX R i v 1 (one_mem_locSet R i v) := rfl
  conv_lhs => rw [e, ← placeSupportedLevelCoset_representative_eq x]
  rw [placeSupportedLevelCoset_eq_iff, mul_one, inv_mem_iff]

theorem chosenFinitePlaceIdempotent_spec {v : HeightOneSpectrum (𝓞 D.host.F)} (h : ∃ f, IsFinIdem D v f) : IsFinIdem D v (fid D v) := by
  unfold fid; rw [dite_eq_left h]; exact h.choose_spec

theorem chosenFinitePlaceIdempotent_eq_zero_of_not_exists {v : HeightOneSpectrum (𝓞 D.host.F)} (h : ¬ ∃ f, IsFinIdem D v f) : fid D v = 0 := by
  unfold fid; rw [dite_eq_right h]

def dcSetoid (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) : Setoid (LX R i v) where
  r x y := ∃ k₁ ∈ {k | k ∈ levW R i ∧ SuppF (Wc D i) (fid D v) k}, ∃ k₂ ∈ {k | k ∈ levW R i ∧ SuppF (Wc D i) (fid D v) k},
    rep y = k₁ * rep x * k₂
  iseqv := by
    refine ⟨fun x => ⟨1, ⟨(levW R i).one_mem, (Model.trivAt_one _ _).2⟩, 1, ⟨(levW R i).one_mem, (Model.trivAt_one _ _).2⟩,
      by group⟩, ?_, ?_⟩
    · rintro x y ⟨k₁, ⟨h1l, h1s⟩, k₂, ⟨h2l, h2s⟩, h⟩
      refine ⟨k₁⁻¹, ⟨(levW R i).inv_mem h1l, supportedAtAdeleIdempotent_inv_closed _ _ h1s⟩, k₂⁻¹,
        ⟨(levW R i).inv_mem h2l, supportedAtAdeleIdempotent_inv_closed _ _ h2s⟩, ?_⟩
      rw [h]; group
    · rintro x y z ⟨k₁, ⟨h1l, h1s⟩, k₂, ⟨h2l, h2s⟩, h⟩ ⟨l₁, ⟨g1l, g1s⟩, l₂, ⟨g2l, g2s⟩, h'⟩
      refine ⟨l₁ * k₁, ⟨mul_mem g1l h1l, supportedAtAdeleIdempotent_mul_closed _ _ g1s h1s⟩, k₂ * l₂,
        ⟨mul_mem h2l g2l, supportedAtAdeleIdempotent_mul_closed _ _ h2s g2s⟩, ?_⟩
      rw [h', h]; group

def dcMap {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (C : Quotient (dcSetoid R i v) → Finset (GA D (Wc D i)))
    (hCs : ∀ b, ∀ δ ∈ C b, SuppF (Wc D i) (fid D v) δ)
    (hC : ∀ b, IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) (fid D v) k} (rep (Quotient.out b)) (C b))
    (p : Σ b, ↥(C b)) : LX R i v :=
  mkLX R i v p.2.1 ⟨((hC p.1).1 p.2.1 p.2.2).1, hCs p.1 p.2.1 p.2.2⟩

theorem placeSupportedDoubleCosetMap_bijective {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (C : Quotient (dcSetoid R i v) → Finset (GA D (Wc D i)))
    (hCs : ∀ b, ∀ δ ∈ C b, SuppF (Wc D i) (fid D v) δ)
    (hC : ∀ b, IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) (fid D v) k} (rep (Quotient.out b)) (C b)) :
    Function.Bijective (dcMap C hCs hC) := by
  constructor
  · rintro ⟨b, δ, hδ⟩ ⟨b', δ', hδ'⟩ h
    replace h : δ⁻¹ * δ' ∈ levW R i := (placeSupportedLevelCoset_eq_iff _ _).mp h
    have hs : SuppF (Wc D i) (fid D v) (δ⁻¹ * δ') := supportedAtAdeleIdempotent_mul_closed _ _ (supportedAtAdeleIdempotent_inv_closed _ _ (hCs b δ hδ)) (hCs b' δ' hδ')
    obtain ⟨-, k₁, ⟨h1l, h1s⟩, k₂, ⟨h2l, h2s⟩, e⟩ := (hC b).1 δ hδ
    obtain ⟨-, l₁, ⟨g1l, g1s⟩, l₂, ⟨g2l, g2s⟩, e'⟩ := (hC b').1 δ' hδ'
    have hbb : b = b' := by
      apply Quotient.out_equiv_out.mp
      refine ⟨l₁⁻¹ * k₁, ⟨mul_mem ((levW R i).inv_mem g1l) h1l, supportedAtAdeleIdempotent_mul_closed _ _ (supportedAtAdeleIdempotent_inv_closed _ _ g1s) h1s⟩,
        k₂ * (δ⁻¹ * δ') * l₂⁻¹, ⟨mul_mem (mul_mem h2l h) ((levW R i).inv_mem g2l),
          supportedAtAdeleIdempotent_mul_closed _ _ (supportedAtAdeleIdempotent_mul_closed _ _ h2s hs) (supportedAtAdeleIdempotent_inv_closed _ _ g2s)⟩, ?_⟩
      rw [e, e']; group
    subst hbb
    have hu := (hC b).2 δ' ⟨l₁, ⟨g1l, g1s⟩, l₂, ⟨g2l, g2s⟩, e'⟩
    have hdd : δ = δ' := hu.unique ⟨hδ, h, hs⟩ ⟨hδ', by rw [inv_mul_cancel]; exact (levW R i).one_mem,
      by rw [inv_mul_cancel]; exact (Model.trivAt_one _ _).2⟩
    subst hdd
    rfl
  · intro x
    obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := Quotient.mk_out (s := dcSetoid R i v) x
    obtain ⟨γ, ⟨hγC, hγK⟩, -⟩ := (hC (Quotient.mk _ x)).2 (rep x) ⟨k₁, hk₁, k₂, hk₂, e⟩
    refine ⟨⟨Quotient.mk _ x, γ, hγC⟩, ?_⟩
    unfold dcMap
    conv_rhs => rw [← placeSupportedLevelCoset_representative_eq x]
    exact (placeSupportedLevelCoset_eq_iff _ _).mpr hγK.1

theorem localCoefficient_summable_nontrivialCosets {R : RealDat D A Ks} {i : Fin D.R.m} {t : T} (hLS : LocSmall R i t)
    {μ : Measure (WO (Vc D i) (Wc D i))} {𝓕 : Set (WO (Vc D i) (Wc D i))}
    (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hf : IsFinIdem D v (fid D v)) : Summable (fun x : LX R i v => ‖acoef R i t μ 𝓕 v x‖) := by
  obtain ⟨s, -, -, hs⟩ := hLS μ 𝓕 hμ
  refine summable_of_sum_le (c := ‖acoef R i t μ 𝓕 v (lx0 R i v)‖ + s v) (fun _ => norm_nonneg _) ?_
  intro u
  rw [← Finset.sum_filter_add_sum_filter_not u (fun x => x = lx0 R i v)]
  gcongr
  · calc ∑ x ∈ u.filter (fun x => x = lx0 R i v), ‖acoef R i t μ 𝓕 v x‖
          ≤ ∑ x ∈ ({lx0 R i v} : Finset (LX R i v)), ‖acoef R i t μ 𝓕 v x‖ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx; rw [Finset.mem_filter] at hx; rw [Finset.mem_singleton]; exact hx.2
            · intros; exact norm_nonneg _
      _ = _ := Finset.sum_singleton _ _
  · have hinj : Set.InjOn (fun x : LX R i v => rep x) ↑(u.filter (fun x => ¬ x = lx0 R i v)) := by
      intro x _ y _ hxy
      rw [levelCoset_eq_iff_representative_rel]
      simp only at hxy
      rw [hxy, inv_mul_cancel]; exact (levW R i).one_mem
    have e := Finset.sum_image (f := fun g => ‖coef R i t μ 𝓕 g‖) hinj
    unfold acoef
    rw [← e]
    apply hs v (fid D v) hf
    · intro g hg
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
      rw [Finset.mem_filter] at hx
      exact ⟨(levelCosetRepresentative_mem_supportedSet x).2, fun h => hx.2 ((eq_trivialLevelCoset_iff_representative_mem x).mpr h)⟩
    · intro g hg g' hg' h
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hg
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hg'
      rw [(levelCoset_eq_iff_representative_rel x y).mpr h]

set_option maxHeartbeats 1000000 in
theorem localCoefficient_fiber_sum_eq {R : RealDat D A Ks} {i : Fin D.R.m} {t : T} (hTL : TransLaws R i) (hLF : LevFix R i t)
    {μ : Measure (WO (Vc D i) (Wc D i))} {𝓕 : Set (WO (Vc D i) (Wc D i))}
    (hleft : ∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hf : IsFinIdem D v (fid D v))
    (C : Quotient (dcSetoid R i v) → Finset (GA D (Wc D i)))
    (hCs : ∀ b, ∀ δ ∈ C b, SuppF (Wc D i) (fid D v) δ)
    (hC : ∀ b, IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) (fid D v) k} (rep (Quotient.out b)) (C b))
    {γ : GA D (Wc D i)} (hγ : γ ∈ GfC (Wc D i)) (b : Quotient (dcSetoid R i v)) :
    ∑ δ : ↥(C b), acoef R i t μ 𝓕 v (dcMap C hCs hC ⟨b, δ⟩) • Bop R i (γ * rep (dcMap C hCs hC ⟨b, δ⟩)) =
      ∑ δ : ↥(C b), Bop R i γ * (acoef R i t μ 𝓕 v (dcMap C hCs hC ⟨b, δ⟩) • Bop R i (rep (dcMap C hCs hC ⟨b, δ⟩))) := by
  have key : ∀ δ : ↥(C b), acoef R i t μ 𝓕 v (dcMap C hCs hC ⟨b, δ⟩) = coef R i t μ 𝓕 (rep (Quotient.out b)) ∧
      Bop R i (γ * rep (dcMap C hCs hC ⟨b, δ⟩)) = Bop R i (γ * δ.1) ∧
      Bop R i (rep (dcMap C hCs hC ⟨b, δ⟩)) = Bop R i δ.1 := by
    intro δ
    obtain ⟨k, hk, hrep⟩ : ∃ k ∈ levW R i, rep (dcMap C hCs hC ⟨b, δ⟩) = δ.1 * k := representative_placeSupportedLevelCoset_rel _
    have hδG : δ.1 ∈ GfC (Wc D i) := ((hC b).1 δ.1 δ.2).1
    obtain ⟨k₁, ⟨h1l, -⟩, k₂, ⟨h2l, -⟩, e⟩ := ((hC b).1 δ.1 δ.2).2
    have hrG : rep (dcMap C hCs hC ⟨b, δ⟩) ∈ GfC (Wc D i) := (levelCosetRepresentative_mem_supportedSet _).1
    refine ⟨?_, ?_, ?_⟩
    · unfold acoef
      rw [hrep, Model.coef_mul_lev R i t hLF μ 𝓕 _ _ hk, e, Model.coef_mul_lev R i t hLF μ 𝓕 _ _ h2l]
      exact hleft k₁ h1l _
    · rw [hrep, ← mul_assoc]
      refine finite_mul_liftLevel_mem_finite hTL (mul_mem hγ hδG) hk ?_
      rw [mul_assoc, ← hrep]; exact mul_mem hγ hrG
    · rw [hrep]
      exact finite_mul_liftLevel_mem_finite hTL hδG hk (hrep ▸ hrG)
  have hlast : ∀ δ : ↥(C b), Bop R i γ * (coef R i t μ 𝓕 (rep (Quotient.out b)) • Bop R i δ.1) =
      Bop R i γ * (acoef R i t μ 𝓕 v (dcMap C hCs hC ⟨b, δ⟩) • Bop R i (rep (dcMap C hCs hC ⟨b, δ⟩))) := by
    intro δ
    obtain ⟨h1, -, h2⟩ := key δ
    exact congrArg (Bop R i γ * ·) (congrArg₂ (· • ·) h1.symm h2.symm)
  calc ∑ δ : ↥(C b), acoef R i t μ 𝓕 v (dcMap C hCs hC ⟨b, δ⟩) • Bop R i (γ * rep (dcMap C hCs hC ⟨b, δ⟩))
        = ∑ δ : ↥(C b), coef R i t μ 𝓕 (rep (Quotient.out b)) • Bop R i (γ * δ.1) :=
          Finset.sum_congr rfl (fun δ _ => by rw [(key δ).1, (key δ).2.1])
    _ = coef R i t μ 𝓕 (rep (Quotient.out b)) • ∑ δ ∈ C b, Bop R i (γ * δ) := by
          rw [← Finset.smul_sum, Finset.sum_coe_sort (C b) (fun δ => Bop R i (γ * δ))]
    _ = coef R i t μ 𝓕 (rep (Quotient.out b)) • (Bop R i γ * ∑ δ ∈ C b, Bop R i δ) := by
          rw [rightTranslatePairingOperator_hecke_relation (R := R) hTL hf (α := rep (Quotient.out b)) (levelCosetRepresentative_mem_supportedSet (Quotient.out b)).2 (C b) (hCs b) (hC b) hγ]
    _ = ∑ δ ∈ C b, Bop R i γ * (coef R i t μ 𝓕 (rep (Quotient.out b)) • Bop R i δ) := by
          rw [Finset.mul_sum, Finset.smul_sum]
          refine Finset.sum_congr rfl (fun δ _ => ?_)
          apply ContinuousLinearMap.ext; intro y
          show coef R i t μ 𝓕 (rep (Quotient.out b)) • Bop R i γ (Bop R i δ y) =
            Bop R i γ ((coef R i t μ 𝓕 (rep (Quotient.out b)) • Bop R i δ) y)
          rw [ContinuousLinearMap.smul_apply, map_smul]
    _ = ∑ δ : ↥(C b), Bop R i γ * (coef R i t μ 𝓕 (rep (Quotient.out b)) • Bop R i δ.1) :=
          (Finset.sum_coe_sort (C b) (fun δ => Bop R i γ * (coef R i t μ 𝓕 (rep (Quotient.out b)) • Bop R i δ))).symm
    _ = ∑ δ : ↥(C b), Bop R i γ * (acoef R i t μ 𝓕 v (dcMap C hCs hC ⟨b, δ⟩) • Bop R i (rep (dcMap C hCs hC ⟨b, δ⟩))) := by
          exact Finset.sum_congr rfl (fun δ _ => hlast δ)

end Local


set_option maxHeartbeats 1000000 in
theorem bop_mul_zop_hasSum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i t, LocSmall R i t → TransLaws R i → LevFix R i t → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g) → ∀ v, ∀ γ ∈ GfC (Wc D i), HasSum (fun x : Eu.LX R i v => Eu.acoef R i t μ 𝓕 v x • Eu.Bop R i (γ * Eu.rep x)) (Eu.Bop R i γ * Eu.Zop R i t μ 𝓕 v) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t hLS hTL hLF μ 𝓕 hμ hleft v γ hγ
  by_cases hex : ∃ f, IsFinIdem D v f
  · have hf : IsFinIdem D v (fid D v) := chosenFinitePlaceIdempotent_spec hex
    have hsa := localCoefficient_summable_nontrivialCosets hLS hμ hf (R := R)
    have hs1 : Summable (fun x : LX R i v => acoef R i t μ 𝓕 v x • Bop R i (rep x)) := by
      refine Summable.of_norm_bounded hsa (fun x => ?_)
      rw [norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _) (bop_norm R i _)
    have hs2 : Summable (fun x : LX R i v => acoef R i t μ 𝓕 v x • Bop R i (γ * rep x)) := by
      refine Summable.of_norm_bounded hsa (fun x => ?_)
      rw [norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _) (bop_norm R i _)
    have h1 : HasSum (fun x : LX R i v => Bop R i γ * (acoef R i t μ 𝓕 v x • Bop R i (rep x)))
        (Bop R i γ * Zop R i t μ 𝓕 v) := hs1.hasSum.mul_left (Bop R i γ)
    choose C hCs hC using fun b : Quotient (dcSetoid R i v) =>
      hTL.1 v (fid D v) hf (rep (Quotient.out b)) (levelCosetRepresentative_mem_supportedSet (Quotient.out b)).2
    let e := Equiv.ofBijective (dcMap C hCs hC) (placeSupportedDoubleCosetMap_bijective C hCs hC)
    have g1 := (e.hasSum_iff).mpr h1
    have g2 := ((e.summable_iff).mpr hs2).hasSum
    have k1 := g1.sigma (fun b => hasSum_fintype _)
    have k2 := g2.sigma (fun b => hasSum_fintype _)
    have hfib := localCoefficient_fiber_sum_eq (R := R) hTL hLF hleft hf C hCs hC hγ
    have hfun : (fun b => ∑ c : ↥(C b),
          ((fun x : LX R i v => acoef R i t μ 𝓕 v x • Bop R i (γ * rep x)) ∘ e) ⟨b, c⟩) =
        (fun b => ∑ c : ↥(C b),
          ((fun x : LX R i v => Bop R i γ * (acoef R i t μ 𝓕 v x • Bop R i (rep x))) ∘ e) ⟨b, c⟩) :=
      funext fun b => hfib b
    rw [hfun] at k2
    have hk := k2.unique k1
    rw [← hk]
    exact (e.hasSum_iff).mp g2
  · have h0 := chosenFinitePlaceIdempotent_eq_zero_of_not_exists hex
    have hall : ∀ x : LX R i v, rep x = 1 := fun x => supportedAtIdempotent_zero_eq_one _ (h0 ▸ (levelCosetRepresentative_mem_supportedSet x).2)
    haveI : Subsingleton (LX R i v) := ⟨fun x y => (levelCoset_eq_iff_representative_rel x y).mpr (by
      rw [hall x, hall y, inv_one, one_mul]; exact (levW R i).one_mem)⟩
    have hs1 : Summable (fun x : LX R i v => acoef R i t μ 𝓕 v x • Bop R i (rep x)) := Summable.of_finite
    have hF : (fun x : LX R i v => acoef R i t μ 𝓕 v x • Bop R i (γ * rep x)) =
        fun x => Bop R i γ * (acoef R i t μ 𝓕 v x • Bop R i (rep x)) := by
      funext x
      rw [hall x, mul_one, bop_one hTL]
      apply ContinuousLinearMap.ext; intro y
      show (acoef R i t μ 𝓕 v x • Bop R i γ) y = Bop R i γ ((acoef R i t μ 𝓕 v x • (1 : (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H)) y)
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul]
      rfl
    rw [hF]
    exact hs1.hasSum.mul_left (Bop R i γ)

end GlobalTheory.RawLift.Eu

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightTranslateOperatorMulLocalOperatorHasSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightTranslateOperator_mul_localOperator_hasSum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i t, LocSmall R i t → TransLaws R i → LevFix R i t → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g) → ∀ v, ∀ γ ∈ GfC (Wc D i), HasSum (fun x : Eu.LX R i v => Eu.acoef R i t μ 𝓕 v x • Eu.Bop R i (γ * Eu.rep x)) (Eu.Bop R i γ * Eu.Zop R i t μ 𝓕 v) := by
  first | exact @GlobalTheory.RawLift.Eu.bop_mul_zop_hasSum | exact GlobalTheory.RawLift.Eu.bop_mul_zop_hasSum | (intros; apply GlobalTheory.RawLift.Eu.bop_mul_zop_hasSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCovolumeOneMeasureHomSpaceOfLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCovolumeOneMeasureHomSpaceOfLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

namespace GlobalTheory.RawLift.Covol

theorem exists_isCovolOne_of_laws : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i, ∃ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ i
  exact GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)

end GlobalTheory.RawLift.Covol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCovolumeOneMeasureHomSpaceOfLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_covolumeOne_measure_homSpace_of_laws : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i, ∃ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 := by
  first | exact @GlobalTheory.RawLift.Covol.exists_isCovolOne_of_laws | exact GlobalTheory.RawLift.Covol.exists_isCovolOne_of_laws | (intros; apply GlobalTheory.RawLift.Covol.exists_isCovolOne_of_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalOperatorScalarOnSphericalEigenspace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalOperatorScalarOnSphericalEigenspace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.Eig

theorem mem_of_fibres {X Q H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] {g : X → H} {a : H}
    (hg : HasSum g a) (π : X → Q) (L : Submodule ℂ H) (hL : IsClosed (L : Set H))
    (h : ∀ x₀, ∃ s : Finset X, (∀ x, π x = π x₀ ↔ x ∈ s) ∧ ∑ x ∈ s, g x ∈ L) : a ∈ L := by
  have h1 := hg.tsum_fiberwise π
  refine hL.mem_of_tendsto h1 (Filter.Eventually.of_forall fun s => L.sum_mem fun c _ => ?_)
  by_cases hc : ∃ x₀, π x₀ = c
  · obtain ⟨x₀, rfl⟩ := hc
    obtain ⟨s, hs, hm⟩ := h x₀
    have e : π ⁻¹' {π x₀} = (s : Set X) := Set.ext fun x => hs x
    rw [e, Finset.tsum_subtype' s g]
    exact hm
  · have e : π ⁻¹' {c} = ((∅ : Finset X) : Set X) := Set.ext fun x => by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_empty, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hc ⟨x, hx⟩
    rw [e, Finset.tsum_subtype' ∅ g, Finset.sum_empty]
    exact L.zero_mem

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem isFinIdem_fid (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : IsFinIdem D v (Eu.fid D v) := by
  have h : ∃ f, IsFinIdem D v f := by
    obtain ⟨ε, hε⟩ := GlobalTheory.IdemSupport.exists_placeIdem (D := D) v
    exact ⟨_, ε, hε, rfl⟩
  unfold Eu.fid
  rw [dite_eq_left h]
  exact h.choose_spec

theorem exists_primeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f) :
    ∃ P e, P.under (𝓞 D.host.F) = v ∧ IsPrimeIdem P e f := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
  have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQ.isPrime, hne⟩
  have hP : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hQv.over.symm
  obtain ⟨e, f', h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  obtain ⟨-, ε, hε, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h
  obtain ⟨ε', hε', rfl⟩ := hf
  rw [hP] at hε
  rw [GlobalTheory.IdemSupport.placeIdem_unique hε' hε]
  exact ⟨P, e, hP, h⟩

theorem primeIdem_of_under {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P.under (𝓞 D.host.F) = v) : ∃ e, IsPrimeIdem P e f := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨e, f', h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  obtain ⟨-, ε, hε, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h
  obtain ⟨ε', hε', rfl⟩ := hf
  rw [hP] at hε
  rw [GlobalTheory.IdemSupport.placeIdem_unique hε' hε]
  exact ⟨e, h⟩

variable {R : RealDat D A Ks} {i : Fin D.R.m}

theorem bop_spec (hTL : TransLaws R i) {γ : GA D (Wc D i)} (hγ : γ ∈ GfC (Wc D i)) (x y) :
    trPair R i γ x y = ⟪x, Eu.Bop R i γ y⟫_ℂ := by
  have hex := hTL.2.2.1 γ hγ
  unfold Eu.Bop
  rw [dite_eq_left hex]
  exact hex.choose_spec.2 x y

theorem bop_mul_lev (hLP : LevProd R i) (hTL : TransLaws R i) {γ k : GA D (Wc D i)} (hγ : γ ∈ GfC (Wc D i))
    (hk : k ∈ levW R i) : Eu.Bop R i (γ * k) = Eu.Bop R i γ := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [← bop_spec hTL hγ, ← bop_spec hTL (mul_mem hγ (hLP.1 hk))]
  have := hTL.2.2.2.1 γ hγ 1 (one_mem _) k hk x y
  rwa [one_mul] at this

theorem hecke_sum_good {F : Face D A} (hL : Laws R F) (hTL : TransLaws R i) {c} {y} (hy : y ∈ part R i ∅ c)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f)
    (hv : ∀ P ∈ R.Pg, P.under (𝓞 D.host.F) ≠ v) {α : GA D (Wc D i)} (hα : SuppF (Wc D i) f α)
    {C : Finset (GA D (Wc D i))} (hC : ∀ γ ∈ C, SuppF (Wc D i) f γ)
    (hCR : IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C) :
    ∃ z : ℂ, ∑ δ ∈ C, Eu.Bop R i δ y = z • y := by
  obtain ⟨y', hy', hs⟩ := hTL.2.1 v f hf α hα C hC hCR y
  have e1 : ∑ δ ∈ C, Eu.Bop R i δ y = y' := by
    apply ext_inner_left ℂ
    intro x
    rw [← hTL.2.2.2.2.2 x y', hs 1 (one_mem _) x, inner_sum]
    refine Finset.sum_congr rfl fun δ hδ => ?_
    rw [one_mul, bop_spec hTL (hCR.1 δ hδ).1]
  obtain ⟨P, e, hPv, hP⟩ := exists_primeIdem hf
  obtain ⟨n, hβ⟩ := hL.lev.βW i
  obtain ⟨hJ, hχ, -⟩ := (GlobalTheory.LevSplit.lev_split (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ).2 P e f hP
    (by rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top)
    (by
      intro PP hPP
      have h1 : PP ∈ R.Pg := hPP.resolve_right (Finset.notMem_empty _)
      refine ⟨fun h => hv PP h1 (h ▸ hPv), fun h => hv PP h1 ?_⟩
      rw [(GlobalTheory.IdemSupport.isConjPl_iff _ _).1 h, GlobalTheory.IdemSupport.under_cP] at hPv
      exact hPv)
  obtain ⟨-, ϖ, -, h1, h2⟩ := GlobalTheory.SphLabelOps.exists_real_unif D P
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have he : e * e = e := GlobalTheory.IdemSupport.delta_idem hΦ (GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hP).1
  obtain ⟨d, hd, hD⟩ := GlobalTheory.SphLabelOps.exists_divAt (Wc D i) he (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem hP) h1 h2 α
  have hop : Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) ∅ P d C :=
    ⟨e, f, ϖ, α, fun w hw => absurd hw (Finset.notMem_empty w), hP, h1, h2, hd, hJ, hχ, hα, hD, hC, hCR⟩
  have hm := (Submodule.mem_comap.1 hy).2
  simp only [SetLike.mem_coe, Submodule.mem_iInf] at hm
  have hk := hm P d C hop
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hk
  refine ⟨c P d, e1.trans ((hL.models.HW i (sg0 D A)).1 ?_)⟩
  rw [hy', hk, map_smul]
  rfl

theorem hecke_sum_mem {F : Face D A} (hL : Laws R F) {t : T} (hB : BadSupp R i t) (hLP : LevProd R i)
    (hTL : TransLaws R i) {μ 𝓕} (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕) {c} {y} (hy : y ∈ part R i ∅ c)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f)
    {α : GA D (Wc D i)} (hα : SuppF (Wc D i) f α)
    {C : Finset (GA D (Wc D i))} (hC : ∀ γ ∈ C, SuppF (Wc D i) f γ)
    (hCR : IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C) :
    coef R i t μ 𝓕 α • ∑ δ ∈ C, Eu.Bop R i δ y ∈ Submodule.span ℂ {y} := by
  by_cases hv : ∀ P ∈ R.Pg, P.under (𝓞 D.host.F) ≠ v
  · obtain ⟨z, hz⟩ := hecke_sum_good hL hTL hy hf hv hα hC hCR
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y))
  · push_neg at hv
    obtain ⟨P, hP, hPv⟩ := hv
    obtain ⟨e, he⟩ := primeIdem_of_under hf hPv
    by_cases hk : α ∈ levW R i
    · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun δ hδ => ?_)
      obtain ⟨-, k₁, hk₁, k₂, hk₂, rfl⟩ := hCR.1 δ hδ
      have := bop_mul_lev hLP hTL (one_mem _) (mul_mem (mul_mem hk₁.1 hk) hk₂.1)
      rw [one_mul] at this
      rw [this, Eu.bop_one hTL]
      exact Submodule.mem_span_singleton_self y
    · rw [hB μ 𝓕 hμ P (Or.inl hP) e f he α hα hk, zero_smul]
      exact Submodule.zero_mem _

theorem mk_eq_iff {v : HeightOneSpectrum (𝓞 D.host.F)} (g : Eu.locSet R i v) (x : Eu.LX R i v) :
    (Quotient.mk _ g : Eu.LX R i v) = x ↔ g.1⁻¹ * Eu.rep x ∈ levW R i := by
  rw [← QuotientGroup.leftRel_apply]
  exact Quotient.mk_eq_iff_out


set_option maxHeartbeats 800000 in
theorem zop_eigen : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i t, BadSupp R i t → LevFix R i t → LocSmall R i t → LevProd R i → TransLaws R i → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g) → ∀ c, ∀ y ∈ part R i ∅ c, ∀ v, ∃ z : ℂ, Eu.Zop R i t μ 𝓕 v y = z • y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t hB hLF _ hLP hTL μ 𝓕 hμ hleft c y hy v
  suffices h : Eu.Zop R i t μ 𝓕 v y ∈ Submodule.span ℂ {y} by
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.1 h
    exact ⟨z, hz.symm⟩
  unfold Eu.Zop
  by_cases hs : Summable fun x : Eu.LX R i v => Eu.acoef R i t μ 𝓕 v x • Eu.Bop R i (Eu.rep x)
  swap
  · rw [tsum_eq_zero_of_not_summable hs]
    exact Submodule.zero_mem _
  have hf := isFinIdem_fid D v
  obtain ⟨P, e, -, hP⟩ := exists_primeIdem hf
  have h0 := (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents (Wc D i)).2.2.1 P e _ hP
  obtain ⟨S, hS⟩ := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents (Wc D i)).1 _ h0.1 h0.2.1).1
  have hloc : ∀ g, g ∈ S → g ∈ Eu.locSet R i v := fun g hg => ⟨h0.2.2.1 g ((hS g).1 hg), (hS g).1 hg⟩
  have hrep : ∀ x : Eu.LX R i v, Eu.rep x ∈ S := fun x => (hS _).2 (Quotient.out x).2.2
  have hsum := (ContinuousLinearMap.apply ℂ _ y).hasSum hs.hasSum
  refine mem_of_fibres hsum (fun x => DoubleCoset.mk (levW R i ⊓ S) (levW R i ⊓ S) (Eu.rep x)) _
    (Submodule.closed_of_finiteDimensional _) fun x₀ => ?_
  have hα : SuppF (Wc D i) (Eu.fid D v) (Eu.rep x₀) := (hS _).1 (hrep x₀)
  obtain ⟨C, hC, hCR⟩ := hTL.1 v _ hf _ hα
  have hK : ∀ k, k ∈ {k | k ∈ levW R i ∧ SuppF (Wc D i) (Eu.fid D v) k} ↔ k ∈ levW R i ⊓ S := fun k =>
    and_congr_right fun _ => (hS k).symm
  obtain ⟨φ, hφ⟩ : ∃ φ : GA D (Wc D i) → Eu.LX R i v, ∀ δ ∈ C, ∀ x, φ δ = x ↔ δ⁻¹ * Eu.rep x ∈ levW R i ⊓ S := by
    have key : ∀ δ : GA D (Wc D i), ∃ x' : Eu.LX R i v, δ ∈ C → ∀ x, x' = x ↔ δ⁻¹ * Eu.rep x ∈ levW R i ⊓ S := by
      intro δ
      by_cases hδ : δ ∈ C
      · have h1 := (hS δ).2 (hC δ hδ)
        exact ⟨Quotient.mk _ ⟨δ, hloc δ h1⟩, fun _ x =>
          (mk_eq_iff ⟨δ, hloc δ h1⟩ x).trans ⟨fun h => ⟨h, S.mul_mem (S.inv_mem h1) (hrep x)⟩, fun h => h.1⟩⟩
      · exact ⟨Eu.lx0 R i v, fun h => absurd h hδ⟩
    choose φ hφ using key
    exact ⟨φ, hφ⟩
  have hdc : ∀ δ ∈ C, ∃ k₁ ∈ levW R i ⊓ S, ∃ k₂ ∈ levW R i ⊓ S, Eu.rep (φ δ) = k₁ * Eu.rep x₀ * k₂ := fun δ hδ => by
    obtain ⟨-, k₁, hk₁, k₂, hk₂, e1⟩ := hCR.1 δ hδ
    refine ⟨k₁, (hK _).1 hk₁, k₂ * (δ⁻¹ * Eu.rep (φ δ)), mul_mem ((hK _).1 hk₂) ((hφ δ hδ _).1 rfl), ?_⟩
    rw [← mul_assoc, ← e1, mul_inv_cancel_left]
  refine ⟨C.image φ, fun x => ?_, ?_⟩
  · rw [eq_comm, DoubleCoset.eq, Finset.mem_image]
    constructor
    · rintro ⟨k₁, hk₁, k₂, hk₂, e1⟩
      obtain ⟨δ, ⟨hδ, h1⟩, -⟩ := hCR.2 _ ⟨k₁, (hK _).2 hk₁, k₂, (hK _).2 hk₂, e1⟩
      exact ⟨δ, hδ, (hφ δ hδ x).2 ((hK _).1 h1)⟩
    · rintro ⟨δ, hδ, rfl⟩
      exact hdc δ hδ
  · rw [Finset.sum_image]
    · have := hecke_sum_mem hL hB hLP hTL hμ hy hf hα hC hCR
      rw [Finset.smul_sum] at this
      refine (congrArg (· ∈ Submodule.span ℂ {y}) (Finset.sum_congr rfl fun δ hδ => ?_)).mpr this
      obtain ⟨k₁, hk₁, k₂, hk₂, e1⟩ := hdc δ hδ
      have e2 : Eu.acoef R i t μ 𝓕 v (φ δ) = coef R i t μ 𝓕 (Eu.rep x₀) := by
        unfold Eu.acoef
        rw [e1, Model.coef_mul_lev R i t hLF μ 𝓕 _ _ hk₂.1, hleft _ hk₁.1]
      have e3 : Eu.Bop R i (Eu.rep (φ δ)) = Eu.Bop R i δ := by
        rw [← bop_mul_lev hLP hTL (hCR.1 δ hδ).1 ((hφ δ hδ _).1 rfl).1, mul_inv_cancel_left]
      rw [ContinuousLinearMap.apply_apply, e2, e3, ContinuousLinearMap.smul_apply]
    · intro δ hδ δ' hδ' h
      obtain ⟨k₁, hk₁, k₂, hk₂, e1⟩ := hdc δ hδ
      obtain ⟨δ₀, -, hu⟩ := hCR.2 _ ⟨k₁, (hK _).2 hk₁, k₂, (hK _).2 hk₂, e1⟩
      exact (hu δ ⟨hδ, (hK _).2 ((hφ δ hδ _).1 rfl)⟩).trans (hu δ' ⟨hδ', (hK _).2 ((hφ δ' hδ' _).1 h.symm)⟩).symm

end GlobalTheory.RawLift.Eig

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalOperatorScalarOnSphericalEigenspaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localOperator_scalar_on_sphericalEigenspace : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i t, BadSupp R i t → LevFix R i t → LocSmall R i t → LevProd R i → TransLaws R i → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g) → ∀ c, ∀ y ∈ part R i ∅ c, ∀ v, ∃ z : ℂ, Eu.Zop R i t μ 𝓕 v y = z • y := by
  first | exact @GlobalTheory.RawLift.Eig.zop_eigen | exact GlobalTheory.RawLift.Eig.zop_eigen | (intros; apply GlobalTheory.RawLift.Eig.zop_eigen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightTranslateOperatorFamilyProdUpdate
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightTranslateOperatorFamilyProdUpdate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.Eu

theorem prod_toList_insert_comm {ι M : Type} [Monoid M] [DecidableEq ι] (s : Finset ι) (v : ι) (hv : v ∉ s) (f : ι → M)
    (hc : ∀ a b, a ≠ b → Commute (f a) (f b)) :
    ((insert v s).toList.map f).prod = (s.toList.map f).prod * f v := by
  have hp : ((insert v s).toList.map f).Perm ((v :: s.toList).map f) := (Finset.toList_insert hv).map f
  have hpw : ((insert v s).toList.map f).Pairwise Commute := by
    rw [List.pairwise_map]
    exact (Finset.nodup_toList _).imp fun h => hc _ _ h
  rw [hp.prod_eq' hpw, List.map_cons, List.prod_cons]
  refine (Commute.list_prod_right _ _ fun y hy => ?_).eq
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
  refine hc _ _ ?_
  rintro rfl
  exact hv (Finset.mem_toList.1 hw)

theorem fid_orth (D : D7) {v w : HeightOneSpectrum (𝓞 D.host.F)} (h : v ≠ w) : fid D v * fid D w = 0 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  unfold fid
  split_ifs with h1 h2
  · obtain ⟨ε, hε, e⟩ := h1.choose_spec
    obtain ⟨ε', hε', e'⟩ := h2.choose_spec
    rw [e, e']
    exact GlobalTheory.IdemSupport.place_orth hΦ hε hε' h
  · exact mul_zero _
  · exact zero_mul _
  · exact zero_mul _

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem rep_mem_locSet {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x : LX R i v) :
    rep x ∈ locSet R i v := (Quotient.out x).2

theorem rep_commute {R : RealDat D A Ks} {i : Fin D.R.m} {v w : HeightOneSpectrum (𝓞 D.host.F)} (h : v ≠ w)
    (x : LX R i v) (y : LX R i w) : Commute (rep x) (rep y) :=
  GlobalTheory.IdemSupport.commute_of_suppF _ (fid_orth D h) (rep_mem_locSet x).2 (rep_mem_locSet y).2

theorem famProd_mem_GfC (R : RealDat D A Ks) (i : Fin D.R.m) (F : ∀ v, LX R i v) :
    famProd R i F ∈ GfC (Wc D i) := by
  unfold famProd
  split_ifs with h
  · refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy
    exact (rep_mem_locSet _).1
  · exact Subgroup.one_mem _

theorem bop_congr (R : RealDat D A Ks) (i : Fin D.R.m) {γ γ' : GA D (Wc D i)}
    (h : trPair R i γ = trPair R i γ') : Bop R i γ = Bop R i γ' := by
  unfold Bop
  rw [h]

theorem famProd_update_of_ne (R : RealDat D A Ks) (i : Fin D.R.m) (F : ∀ v, LX R i v)
    (hF : {w | F w ≠ lx0 R i w}.Finite) (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : F v = lx0 R i v) (x : LX R i v)
    (hx : x ≠ lx0 R i v) : famProd R i (Function.update F v x) = famProd R i F * rep x := by
  have hs : {w | Function.update F v x w ≠ lx0 R i w} = insert v {w | F w ≠ lx0 R i w} := by
    ext w
    by_cases hw : w = v
    · subst hw
      simp [hx]
    · simp [hw]
  have hF' : {w | Function.update F v x w ≠ lx0 R i w}.Finite := by
    rw [hs]; exact hF.insert v
  have ht : hF'.toFinset = insert v hF.toFinset := by
    ext w
    rw [Set.Finite.mem_toFinset, hs, Finset.mem_insert, Set.Finite.mem_toFinset, Set.mem_insert_iff]
  have hnv : v ∉ hF.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact fun h => h hv
  unfold famProd
  rw [dite_eq_left hF, dite_eq_left hF', ht,
    prod_toList_insert_comm hF.toFinset v hnv (fun w => rep (Function.update F v x w))
      (fun a b h => rep_commute h _ _)]
  congr 1
  · congr 1
    refine List.map_congr_left fun w hw => ?_
    have : w ≠ v := by
      rintro rfl
      exact hnv (Finset.mem_toList.1 hw)
    rw [Function.update_of_ne this]
  · simp only [Function.update_self]

theorem bop_famProd_update : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i, TransLaws R i → ∀ (F : ∀ v, Eu.LX R i v), {w | F w ≠ Eu.lx0 R i w}.Finite → ∀ v, F v = Eu.lx0 R i v → Eu.famProd R i F ∈ GfC (Wc D i) ∧ ∀ x : Eu.LX R i v, Eu.Bop R i (Eu.famProd R i (Function.update F v x)) = Eu.Bop R i (Eu.famProd R i F * Eu.rep x) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hTL F hF v hv
  refine ⟨famProd_mem_GfC R i F, fun x => ?_⟩
  by_cases hx : x = lx0 R i v
  · have hu : Function.update F v x = F := by
      rw [hx, ← hv]; exact Function.update_eq_self v F
    rw [hu]
    refine bop_congr R i (funext fun a => funext fun b => ?_)
    have := hTL.2.2.2.1 _ (famProd_mem_GfC R i F) 1 (Subgroup.one_mem _) (rep x) (hx ▸ trivial_level_coset_representative_mem_level R i v) a b
    rw [one_mul] at this
    exact this.symm
  · rw [famProd_update_of_ne R i F hF v hv x hx]

end GlobalTheory.RawLift.Eu

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightTranslateOperatorFamilyProdUpdateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightTranslateOperator_familyProd_update : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i, TransLaws R i → ∀ (F : ∀ v, Eu.LX R i v), {w | F w ≠ Eu.lx0 R i w}.Finite → ∀ v, F v = Eu.lx0 R i v → Eu.famProd R i F ∈ GfC (Wc D i) ∧ ∀ x : Eu.LX R i v, Eu.Bop R i (Eu.famProd R i (Function.update F v x)) = Eu.Bop R i (Eu.famProd R i F * Eu.rep x) := by
  first | exact @GlobalTheory.RawLift.Eu.bop_famProd_update | exact GlobalTheory.RawLift.Eu.bop_famProd_update | (intros; apply GlobalTheory.RawLift.Eu.bop_famProd_update <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.Eu

theorem scalar_of_eigen {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (P : Submodule ℂ H)
    (Wop : H →L[ℂ] H) (hinj : Function.Injective Wop) (heig : ∀ y ∈ P, ∃ z : ℂ, Wop y = z • y) :
    ∃ l : ℂ, l ≠ 0 ∧ ∀ x ∈ P, Wop x = l • x := by
  by_cases h : ∃ x0 ∈ P, x0 ≠ 0
  · obtain ⟨x0, hx0, hne⟩ := h
    obtain ⟨l, hl⟩ := heig x0 hx0
    refine ⟨l, ?_, ?_⟩
    · rintro rfl
      apply hne
      apply hinj
      rw [hl, zero_smul, map_zero]
    · intro x hx
      obtain ⟨lx, hlx⟩ := heig x hx
      obtain ⟨m, hm⟩ := heig (x + x0) (P.add_mem hx hx0)
      rw [map_add (f := _), hlx, hl, smul_add] at hm
      by_cases hmx : m = lx
      · subst hmx
        have : (l - m) • x0 = 0 := by
          rw [sub_smul]; exact sub_eq_zero.2 (add_left_cancel hm)
        rcases smul_eq_zero.1 this with h1 | h1
        · rw [hlx, sub_eq_zero.1 h1]
        · exact absurd h1 hne
      · have hx' : x = ((l - m) / (m - lx)) • x0 := by
          have e1 : (m - lx) • x = (l - m) • x0 := by
            rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add]
            rw [← hm]; abel
          have hne' : m - lx ≠ 0 := sub_ne_zero.2 hmx
          rw [div_eq_mul_inv, mul_comm, mul_smul, ← e1, smul_smul, inv_mul_cancel₀ hne', one_smul]
        rw [hx', map_smul, hl, smul_comm]
  · push_neg at h
    refine ⟨1, one_ne_zero, fun x hx => ?_⟩
    rw [h x hx, map_zero, smul_zero]

set_option maxHeartbeats 4000000 in
theorem innerNe_main {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hL : Laws R F) (i : Fin D.R.m) (t : T) (hFS : FinSum R i t) (hFM : FinMult R i t) (hLF : LevFix R i t)
    (hVN : VecNe R i t) (hLS : LocSmall R i t) (hBS : BadSupp R i t) (hLP : LevProd R i) (hTL : TransLaws R i) :
    InnerNe R i t ∅ := by
  intro th hth c
  have hcov := @GlobalTheory.T.exists_covolumeOne_measure_homSpace_of_laws D G _ _ Pl0 T A Ks _ _ _ R F hL i
  obtain ⟨μ, 𝓕, hμ⟩ := hcov
  have hleft := @GlobalTheory.T.fixedVectorCoefficient_left_invariant_levelGroup D G _ _ Pl0 T A Ks _ _ _ R F hL i t hLF μ 𝓕 hμ
  have hfa := @GlobalTheory.T.hasSum_innerProduct_finsupp_localCosetFamilies D G _ _ Pl0 T A Ks _ _ _ R i t hLP hTL hFM hLF hVN hFS th hth μ 𝓕 hμ
  have hsm := @GlobalTheory.T.localCoefficient_nontrivialCosets_summable_bound D G _ _ Pl0 T A Ks _ _ _ R i t hLS μ 𝓕 hμ
  obtain ⟨a, ha, hfam⟩ := hfa
  obtain ⟨s, hs, hs1, hsC⟩ := hsm
  have hconv := @GlobalTheory.T.rightTranslateOperator_mul_localOperator_hasSum D G _ _ Pl0 T A Ks _ _ _ R i t hLS hTL hLF μ 𝓕 hμ hleft
  have hupd := @GlobalTheory.T.rightTranslateOperator_familyProd_update D G _ _ Pl0 T A Ks _ _ _ R i hTL
  have heig := @GlobalTheory.T.localOperator_scalar_on_sphericalEigenspace D G _ _ Pl0 T A Ks _ _ _ R F hL i t hBS hLF hLS hLP hTL μ 𝓕 hμ hleft c
  have hUpd : ∀ v (f : ∀ v, Eu.LX R i v), {w | f w ≠ Eu.lx0 R i w}.Finite → f v = Eu.lx0 R i v →
      HasSum (fun x => Eu.acoef R i t μ 𝓕 v x • Eu.Bfam R i (Function.update f v x))
        (Eu.Bfam R i f * Eu.Zop R i t μ 𝓕 v) := by
    intro v f hf hv
    obtain ⟨hG, hB⟩ := hupd f hf v hv
    have := hconv v _ hG
    unfold Eu.Bfam
    simp only [hB]
    exact this
  have hEu := GlobalTheory.T.eulerOperator_injective_eigenvector (HeightOneSpectrum (𝓞 D.host.F)) (Eu.LX R i) (Eu.lx0 R i)
    (R.HW i (sg0 D A)).H (Eu.acoef R i t μ 𝓕) s (Eu.Bfam R i) (Eu.Zop R i t μ 𝓕)
    (local_coefficient_trivial_level_coset hLF hVN hμ) hs hs1 hsC (fun f => bop_norm R i _)
    (by unfold Eu.Bfam; rw [localCosetFamilyRepresentativeProd_trivial_eq_one]; exact bop_one hTL) hUpd
  obtain ⟨Wop, hW, hinj, hWe⟩ := hEu
  have hip : ∀ x y, ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ = (a : ℂ) * ⟪x, Wop y⟫_ℂ := by
    intro x y
    let φ : ((R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H) →L[ℂ] ℂ :=
      (innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ _ y)
    have h1 := (hW.mapL φ).mul_left (a : ℂ)
    have h2 := hfam x y
    refine h2.unique ?_
    simpa [φ, inner_smul_right] using h1
  have hE : ∀ y ∈ part R i ∅ c, ∃ z : ℂ, Wop y = z • y := by
    intro y hy
    have hz := fun v => heig y hy v
    choose z hz using hz
    exact ⟨_, hWe y z hz⟩
  have hsc := scalar_of_eigen (part R i ∅ c) Wop hinj hE
  obtain ⟨l, hl, hlx⟩ := hsc
  refine ⟨(a : ℂ) * (starRingEnd ℂ) l, mul_ne_zero (by exact_mod_cast ha.ne') (by simpa using hl), ?_⟩
  intro x hx y
  rw [← inner_conj_symm, hip y x, hlx x hx, inner_smul_right, map_mul, map_mul, Complex.conj_ofReal,
    inner_conj_symm]
  ring

end GlobalTheory.RawLift.Eu

namespace GlobalTheory.RawLift

theorem innerNe_spherical : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, FinSum R i t → FinMult R i t → LevFix R i t → VecNe R i t → LocSmall R i t → BadSupp R i t → LevProd R i → TransLaws R i → InnerNe R i t ∅ :=
  fun _ _ _ _ _ _ _ _ _ _ _ R F hL _ i t hFS hFM hLF hVN hLS hBS hLP hTL =>
    Eu.innerNe_main R F hL i t hFS hFM hLF hVN hLS hBS hLP hTL

end GlobalTheory.RawLift

end

module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMemGLs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt
public import GroundTheory.AutomorphicForms.AnisotropicHeight

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CTFin

abbrev lev (R : Type) [CommRing R] (r s : ℕ) : GL (Fin r) R × GL (Fin s) R →* GL (Fin (r + s)) R :=
  GlobalTheory.SmGL.emb₂ R (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

def goodCT (L : Subgroup (GL (Fin (r + s)) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E (r + s)) W) (J : Set (Module.End ℂ (Sm E (r + s)))) :
    Submodule ℂ (Sm E (r + s)) where
  carrier := {F | (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) ∧
    (∀ (γ : GL (Fin r) E × GL (Fin s) E) (g : GA E (r + s)),
      F.1 (lev (Ad E) r s (ratGL E r γ.1, ratGL E s γ.2) * g) = F.1 g) ∧
    (∀ k ∈ L, finRep E (r + s) k F = F) ∧
    (∀ g : GA E (r + s), (fun k : Kinf E (r + s) => (cptRep E (r + s) k F).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧
    (∀ g : GA E (r + s), ∃ (C : ℝ) (N : ℕ), ∀ y, ‖F.1 (g * infGL E (r + s) y)‖ ≤ C * height y ^ N) ∧
    ∀ z ∈ J, z F = 0}
  add_mem' := by
    rintro F G ⟨a1, a2, a3, a4, a5, a6⟩ ⟨b1, b2, b3, b4, b5, b6⟩
    refine ⟨fun x g => ?_, fun γ g => ?_, fun k hk => ?_, fun g => ?_, fun g => ?_, fun z hz => ?_⟩
    · change F.1 _ + G.1 _ = F.1 _ + G.1 _
      rw [a1, b1]
    · change F.1 _ + G.1 _ = F.1 _ + G.1 _
      rw [a2, b2]
    · rw [map_add (f := _), a3 k hk, b3 k hk]
    · convert (GlobalTheory.Published.AutFin.coeffSpan ρ).add_mem (a4 g) (b4 g) using 1
      funext k
      simp
    · obtain ⟨C, N, h⟩ := a5 g
      obtain ⟨C', N', h'⟩ := b5 g
      refine ⟨|C| + |C'|, N + N', fun y => ?_⟩
      have hy := one_le_height y
      have e1 : height y ^ N ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
      have e2 : height y ^ N' ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
      have p1 : 0 ≤ height y ^ N := by positivity
      have p2 : 0 ≤ height y ^ N' := by positivity
      change ‖F.1 _ + G.1 _‖ ≤ _
      refine (norm_add_le _ _).trans ?_
      rw [add_mul]
      refine add_le_add ((h y).trans ?_) ((h' y).trans ?_)
      · exact (mul_le_mul_of_nonneg_right (le_abs_self C) p1).trans
          (mul_le_mul_of_nonneg_left e1 (abs_nonneg _))
      · exact (mul_le_mul_of_nonneg_right (le_abs_self C') p2).trans
          (mul_le_mul_of_nonneg_left e2 (abs_nonneg _))
    · rw [map_add (f := _), a6 z hz, b6 z hz, add_zero]
  zero_mem' := by
    refine ⟨fun x g => rfl, fun γ g => rfl, fun k _ => map_zero _, fun g => ?_, fun g => ⟨0, 0, fun y => ?_⟩,
      fun z _ => map_zero z⟩
    · convert (GlobalTheory.Published.AutFin.coeffSpan ρ).zero_mem using 1
      funext k
      simp
    · simp
  smul_mem' := by
    rintro c F ⟨a1, a2, a3, a4, a5, a6⟩
    refine ⟨fun x g => ?_, fun γ g => ?_, fun k hk => ?_, fun g => ?_, fun g => ?_, fun z hz => ?_⟩
    · change c • F.1 _ = c • F.1 _
      rw [a1]
    · change c • F.1 _ = c • F.1 _
      rw [a2]
    · rw [map_smul, a3 k hk]
    · convert (GlobalTheory.Published.AutFin.coeffSpan ρ).smul_mem c (a4 g) using 1
      funext k
      simp
    · obtain ⟨C, N, h⟩ := a5 g
      refine ⟨‖c‖ * C, N, fun y => ?_⟩
      change ‖c • F.1 _‖ ≤ _
      rw [norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (h y) (norm_nonneg _)
    · rw [map_smul, a6 z hz, smul_zero]

end GlobalTheory.CompanionTheory.CTFin

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInduction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInduction
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl Topology Matrix GroundTheory.Automorphic
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.AffglAssembly

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem isAutForm_add {φ ψ : Sm E a} (h : IsAutForm φ) (h' : IsAutForm ψ) : IsAutForm (φ + ψ) := by
  refine { left := ?_, level := ?_, kfin := ?_, zfin := ?_, growth := ?_ }
  · intro γ g
    change φ.1 _ + ψ.1 _ = φ.1 _ + ψ.1 _
    rw [h.left, h'.left]
  · refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
      ((h.level.inter h'.level).mem_nhds ⟨by simp, by simp⟩) ?_)
    intro k hk
    have h1 : finRep E a k φ = φ := hk.1
    have h2 : finRep E a k ψ = ψ := hk.2
    change finRep E a k (φ + ψ) = φ + ψ
    rw [map_add (f := _), h1, h2]
  · have := h.kfin
    have := h'.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) ⊔
      Submodule.span ℂ (Set.range fun k => cptRep E a k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [map_add (f := _)]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
  · have := h.zfin
    have := h'.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) ⊔
        Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z ψ) '' Zalg E a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [map_add (f := _)]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩) (Submodule.subset_span ⟨z, hz, rfl⟩)
  · intro g
    obtain ⟨C, N, h1⟩ := h.growth g
    obtain ⟨C', N', h2⟩ := h'.growth g
    refine ⟨|C| + |C'|, N + N', fun y => ?_⟩
    have hy := one_le_height y
    have e1 : height y ^ N ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
    have e2 : height y ^ N' ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
    have hp : 0 ≤ height y ^ N := by positivity
    have hp' : 0 ≤ height y ^ N' := by positivity
    calc ‖(φ + ψ).1 (g * infGL E a y)‖ ≤ ‖φ.1 (g * infGL E a y)‖ + ‖ψ.1 (g * infGL E a y)‖ := norm_add_le _ _
      _ ≤ C * height y ^ N + C' * height y ^ N' := add_le_add (h1 y) (h2 y)
      _ ≤ |C| * height y ^ (N + N') + |C'| * height y ^ (N + N') := by
        refine add_le_add ?_ ?_
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C) hp).trans
            (mul_le_mul_of_nonneg_left e1 (abs_nonneg C))
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C') hp').trans
            (mul_le_mul_of_nonneg_left e2 (abs_nonneg C'))
      _ = (|C| + |C'|) * height y ^ (N + N') := by ring

theorem isAutForm_smul (c : ℂ) {φ : Sm E a} (h : IsAutForm φ) : IsAutForm (c • φ) := by
  refine { left := ?_, level := ?_, kfin := ?_, zfin := ?_, growth := ?_ }
  · intro γ g
    change c • φ.1 _ = c • φ.1 _
    rw [h.left]
  · refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.level.mem_nhds (by simp)) ?_)
    intro k hk
    have h1 : finRep E a k φ = φ := hk
    change finRep E a k (c • φ) = c • φ
    rw [map_smul, h1]
  · have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E a k φ))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · have := h.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩)
  · intro g
    obtain ⟨C, N, h1⟩ := h.growth g
    refine ⟨‖c‖ * C, N, fun y => ?_⟩
    change ‖c * φ.1 (g * infGL E a y)‖ ≤ _
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 y) (norm_nonneg c)

def genSub (L : Subgroup (GL (Fin a) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))) : Submodule ℂ (Sm E a) where
  carrier := genSpace L ρ J
  zero_mem' := ⟨isAutForm_const (Submodule.zero_mem _), fun k _ => map_zero _, fun g => by
    have e : (fun k : Kinf E a => (cptRep E a k (0 : Sm E a)).1 g) = 0 := by
      funext k; rw [map_zero]; rfl
    rw [e]; exact Submodule.zero_mem _, fun z _ => map_zero z⟩
  add_mem' := by
    rintro φ ψ ⟨h1, h2, h3, h4⟩ ⟨h1', h2', h3', h4'⟩
    refine ⟨isAutForm_add h1 h1', fun k hk => by rw [map_add (f := _), h2 k hk, h2' k hk], fun g => ?_,
      fun z hz => by rw [map_add (f := _), h4 z hz, h4' z hz, add_zero]⟩
    have e : (fun k : Kinf E a => (cptRep E a k (φ + ψ)).1 g) =
        (fun k : Kinf E a => (cptRep E a k φ).1 g) + fun k : Kinf E a => (cptRep E a k ψ).1 g := by
      funext k; rw [map_add (f := _)]; rfl
    rw [e]; exact Submodule.add_mem _ (h3 g) (h3' g)
  smul_mem' := by
    rintro c φ ⟨h1, h2, h3, h4⟩
    refine ⟨isAutForm_smul c h1, fun k hk => by rw [map_smul, h2 k hk], fun g => ?_,
      fun z hz => by rw [map_smul, h4 z hz, smul_zero]⟩
    have e : (fun k : Kinf E a => (cptRep E a k (c • φ)).1 g) =
        c • fun k : Kinf E a => (cptRep E a k φ).1 g := by
      funext k; rw [map_smul]; rfl
    rw [e]; exact Submodule.smul_mem _ c (h3 g)

theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem continuous_mapInf :
    Continuous (GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf)

theorem continuous_mapFin :
    Continuous (GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pFin)

theorem continuous_of_level {φ : Sm E a} (h : IsOpen {k | finRep E a k φ = φ}) : Continuous φ.1 := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have hc : Continuous fun g : GA E a => g₀⁻¹ * g := continuous_const.mul continuous_id
  let f : GA E a → ℂ := fun g =>
    chart φ.1 g₀ (toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val)
  have e1 : ∀ᶠ g in 𝓝 g₀, f g = φ.1 g := by
    have hS : {g : GA E a | GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) ∈ {k | finRep E a k φ = φ}} ∈ 𝓝 g₀ :=
      ((continuous_mapFin.comp hc).continuousAt).preimage_mem_nhds
        (h.mem_nhds (by simp))
    filter_upwards [hS] with g hg
    have hg' : finRep E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g)) φ = φ := hg
    have e2 := congrFun (congrArg Subtype.val hg') (g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)))
    have e3 : g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) *
        finGL E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g)) = g := by
      rw [mul_assoc, infGL_mul_finGL, mul_inv_cancel_left]
    change φ.1 (_ * finGL E a _) = _ at e2
    rw [e3] at e2
    simp only [f]
    rw [chart_val, e2]
  refine ContinuousAt.congr ?_ e1
  have hx : toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g₀)).val ∈ invSet E a := val_mem_invSet _
  have h1 : ContinuousAt (chart φ.1 g₀) (toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g₀)).val) :=
    (contDiffAt_chart φ.2 g₀ hx).continuousAt
  have h3 : Continuous fun g : GA E a => ((GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) : GL (Fin a) (Cinf E)) :
      Matrix (Fin a) (Fin a) (Cinf E)) := Units.continuous_val.comp (continuous_mapInf.comp hc)
  have h2 : Continuous fun g : GA E a => toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val := h3
  exact ContinuousAt.comp (f := fun g : GA E a => toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) h1 h2.continuousAt

theorem unip_eq_unipGL {R : Type} [CommRing R] {r : ℕ} (x : BlockIx a r → R) :
    unip x = AutomorphicForm.unipGL x := Units.ext rfl

theorem pi_eq_borel (r : ℕ) :
    (MeasurableSpace.pi : MeasurableSpace (BlockIx a r → Ad E)) = borel (BlockIx a r → Ad E) :=
  BorelSpace.measurable_eq

theorem isCuspidal_of_constantTerm {φ : GA E a → ℂ} (hl : ∀ γ g, φ (ratGL E a γ * g) = φ g)
    (h0 : ∀ r : ℕ, 0 < r → r < a → ∀ g, ∫ x in AutomorphicForm.unipFundamentalDomain E a r, φ (unip x * g)
      ∂AutomorphicForm.unipMeasure E a r = 0) : IsCuspidal φ := by
  intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
  obtain rfl : inst1 = MeasurableSpace.pi := inst2.measurable_eq.trans (pi_eq_borel r).symm
  have : (AutomorphicForm.unipMeasure E a r).IsAddHaarMeasure := inferInstance
  have hc := Measure.isAddLeftInvariant_eq_smul μ (AutomorphicForm.unipMeasure E a r)
  have : Countable (ratN E a r) := AutomorphicForm.countable_unipLattice (K := E) (n := a) (r := r)
  have hF0 : IsAddFundamentalDomain (ratN E a r) (AutomorphicForm.unipFundamentalDomain E a r) μ :=
    IsAddFundamentalDomain.mono AutomorphicForm.isAddFundamentalDomain_unipFundamentalDomain
      (hc ▸ Measure.smul_absolutelyContinuous)
  have hinv : ∀ (ξ : ratN E a r) (x : BlockIx a r → Ad E), φ (unip (ξ +ᵥ x) * g) = φ (unip x * g) := by
    rintro ⟨_, ξ, rfl⟩ x
    change φ (unip ((fun p => algebraMap E (Ad E) (ξ p)) + x) * g) = _
    rw [unip_add, unip_algebraMap, mul_assoc, hl]
  rw [hF.setIntegral_eq hF0 hinv, hc, Measure.restrict_smul, integral_smul_nnreal_measure, h0 r hr hr' g, smul_zero]

theorem integrableOn_unip {φ : GA E a → ℂ} (hφ : Continuous φ) (r : ℕ) (g : GA E a) :
    IntegrableOn (fun x => φ (unip x * g)) (AutomorphicForm.unipFundamentalDomain E a r)
      (AutomorphicForm.unipMeasure E a r) := by
  have e : (fun x : BlockIx a r → Ad E => φ (unip x * g)) = fun X => φ (AutomorphicForm.unipGL X * g) :=
    funext fun x => by rw [unip_eq_unipGL]
  rw [e]
  exact AutomorphicForm.integrableOn_constantTerm hφ g

def ctMap (L : Subgroup (GL (Fin a) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))) (r : ℕ) :
    genSub L ρ J →ₗ[ℂ] (GA E a → ℂ) where
  toFun ψ g := ∫ x in AutomorphicForm.unipFundamentalDomain E a r, ψ.1.1 (unip x * g)
    ∂AutomorphicForm.unipMeasure E a r
  map_add' ψ ψ' := funext fun g =>
    integral_add (integrableOn_unip (continuous_of_level ψ.2.1.level) r g)
      (integrableOn_unip (continuous_of_level ψ'.2.1.level) r g)
  map_smul' c ψ := funext fun g => integral_smul c _

theorem genFin_step (hC : CuspFin E a) (hT : ∀ r, 0 < r → r < a → CTFin E a r) : GenFin E a := by
  intro L hL W _ _ _ ρ hρ J hJ
  let R := {r : ℕ // 0 < r ∧ r < a}
  have : Finite R := Finite.of_injective (fun r : R => (⟨r.1, r.2.2⟩ : Fin a))
    fun x y h => Subtype.ext (congrArg (fun z : Fin a => z.1) h)
  have ct := fun r : R => hT r.1 r.2.1 r.2.2 L hL W ρ hρ J hJ
  choose V hVf hV using ct
  have : ∀ r, FiniteDimensional ℂ (V r) := hVf
  have hm : ∀ (r : R) (ψ : genSub L ρ J), ctMap L ρ J r.1 ψ ∈ V r := fun r ψ =>
    hV r ψ.1 ψ.2 (AutomorphicForm.unipMeasure E a r.1) (AutomorphicForm.unipFundamentalDomain E a r.1)
      inferInstance AutomorphicForm.isAddFundamentalDomain_unipFundamentalDomain
  let Φ : genSub L ρ J →ₗ[ℂ] (∀ r : R, V r) :=
    LinearMap.pi fun r => (ctMap L ρ J r.1).codRestrict (V r) (hm r)
  have hker : FiniteDimensional ℂ (LinearMap.ker Φ) := by
    have hC' := hC L hL W ρ hρ J hJ
    have hle : (LinearMap.ker Φ).map (genSub L ρ J).subtype ≤
        Submodule.span ℂ {φ | φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1} := by
      rintro _ ⟨ψ, hψ, rfl⟩
      refine Submodule.subset_span ⟨ψ.2, isCuspidal_of_constantTerm ψ.2.1.left fun r h0 h1 g => ?_⟩
      exact congrFun (congrArg Subtype.val (congrFun (LinearMap.mem_ker.1 hψ) ⟨r, h0, h1⟩)) g
    have : FiniteDimensional ℂ ((LinearMap.ker Φ).map (genSub L ρ J).subtype) :=
      Submodule.finiteDimensional_of_le hle
    exact Module.Finite.equiv
      (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) (LinearMap.ker Φ)).symm
  have hfin : FiniteDimensional ℂ (genSub L ρ J) := by
    have : Module.Finite ℂ (genSub L ρ J ⧸ LinearMap.ker Φ) := Module.Finite.equiv Φ.quotKerEquivRange.symm
    exact Module.Finite.of_submodule_quotient (LinearMap.ker Φ)
  rw [show Submodule.span ℂ (genSpace L ρ J) = genSub L ρ J from Submodule.span_eq (genSub L ρ J)]
  exact hfin

theorem genFin_of_chapters :
    (∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), CuspFin E a) →
    (∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ b < a, GenFin E b) →
      ∀ r, 0 < r → r < a → CTFin E a r) →
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), GenFin E a := by
  intro hC hT E _ _ _ a
  induction a using Nat.strong_induction_on with
  | _ a ih => exact genFin_step (hC E a) (hT E a ih)

end GlobalTheory.CompanionTheory.AffglAssembly

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInductionStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_finite_by_induction : (∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), CuspFin E a) → (∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ b < a, GenFin E b) → ∀ r, 0 < r → r < a → CTFin E a r) → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), GenFin E a := by
  first | exact @GlobalTheory.CompanionTheory.AffglAssembly.genFin_of_chapters | exact GlobalTheory.CompanionTheory.AffglAssembly.genFin_of_chapters | (intros; apply GlobalTheory.CompanionTheory.AffglAssembly.genFin_of_chapters <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeCalculusHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeCalculusHolds
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace GlobalTheory.CompanionTheory.RCalc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem rcalc : RCalc := by
  intro n
  refine ⟨?_, ?_, ?_⟩
  · intro V _ _ f hf
    exact ⟨fun X => Rd_contDiffOn X hf, fun X Y g hg => Rd_bracket X Y hf hg, fun s m X g hg => Rd_gel X s m hf hg,
      fun s m x hx g hg => ⟨gel_left s m hx hf hg, gel_right s m hx hf hg⟩⟩
  · intro E f hf s m
    exact gel_mem_CE E hf s m
  · intro _ _ μ _ V _ _ _ f hf hc X
    exact ibp n μ V f hf hc X

end GlobalTheory.CompanionTheory.RCalc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeCalculusHoldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_calculus_holds : PositivityTheory.RgBcC.RCalc := by
  first | exact @GlobalTheory.CompanionTheory.RCalc.rcalc | exact GlobalTheory.CompanionTheory.RCalc.rcalc | (intros; apply GlobalTheory.CompanionTheory.RCalc.rcalc <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollifierApproximationHilbert
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollifierApproximationHilbert
noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS

namespace GlobalTheory.CompanionTheory.HilbMoll

variable {n : ℕ}

theorem opConv_mem_of_isClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (W : Submodule ℂ H) (hWc : IsClosed (W : Set H)) (hWs : ∀ g ∈ UJset ε, ∀ x ∈ W, σ g x ∈ W)
    {x : H} (hx : x ∈ W) : opConv ε σ α x ∈ W := by
  have : CompleteSpace W := hWc.completeSpace_coe
  unfold opConv
  by_cases hint : Integrable (fun g : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat g) x)
      (Formalism.REAL.muG ε)
  · have hfix : ∀ g : Formalism.REAL.UJ ε, W.starProjection (α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat g) x) =
        α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat g) x := fun g =>
      Submodule.starProjection_eq_self_iff.2 (W.smul_mem _ (hWs _ (arb_umat_mem g) x hx))
    have h := W.starProjection.integral_comp_comm hint
    simp only [hfix] at h
    rw [h]
    exact W.starProjection_apply_mem _
  · rw [integral_undef hint]
    exact W.zero_mem

theorem stepMoll : PositivityTheory.RgDs.Hilb.StepMoll := by
  intro n ε W S hWc hWs hSf hSW _
  have := hSf
  obtain ⟨α, hadd, hsmul, hαK, hαsm, hαS⟩ := exists_moll_data (rreg_isURepOn ε) S
  let A : L2 ε →ₗ[ℂ] L2 ε := { toFun := opConv ε (rreg ε) α, map_add' := hadd, map_smul' := hsmul }
  have hAv : ∀ v, A v = opConv ε (rreg ε) α v := fun v => rfl
  refine ⟨A, fun k hk x => (hαK k hk x).symm, ?_, ?_, ?_⟩
  · intro w hw h0
    have h1 := hαS w hw
    rw [← hAv, h0, zero_sub, norm_neg] at h1
    have h2 : ‖w‖ ≤ 0 := by linarith
    exact norm_le_zero_iff.1 h2
  · rintro _ ⟨w, _, rfl⟩
    exact (mem_smD_iff ε (rreg ε) _).2 (hαsm w)
  · rintro _ ⟨w, hw, rfl⟩
    exact opConv_mem_of_isClosed ε (rreg ε) α W hWc hWs (hSW hw)

end GlobalTheory.CompanionTheory.HilbMoll
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollifierApproximationHilbertStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mollifier_approximation_hilbert : PositivityTheory.RgDs.Hilb.StepMoll := by
  first | exact @GlobalTheory.CompanionTheory.HilbMoll.stepMoll | exact GlobalTheory.CompanionTheory.HilbMoll.stepMoll | (intros; apply GlobalTheory.CompanionTheory.HilbMoll.stepMoll <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorsSpanDense
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorsSpanDense
noncomputable section

namespace GlobalTheory.CompanionTheory.RgDsHilb

open ReciprocityTheory.ChartRestriction.DS

theorem stepWtSpan : PositivityTheory.RgDs.Hilb.StepWtSpan := by
  intro n ε S hSf hSD hSK N _ _ e he
  classical
  have hσ := rreg_isURepOn ε
  have hD : IsDerivedOn ε (rreg ε) (smD ε (rreg ε)) (smE ε (rreg ε)) := isDerivedOn_smE hσ
  have hE : IsGlRep (smE ε (rreg ε)) := hD.glRep
  have hKU : IsKUnitary ε (smE ε (rreg ε)) :=
    isKUnitary_of_isInfUnitary (isInfUnitary_of_isDerivedOn hσ hD)
  have hSK' : ∀ k ∈ Kset ε, ∀ x ∈ S, rreg ε k x ∈ S := hSK
  haveI := hSf
  haveI hS'f : FiniteDimensional ℂ (S.comap (smD ε (rreg ε)).subtype) :=
    LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe hSD).symm
  have hS'k : IsKStableSub ε (smE ε (rreg ε)) (S.comap (smD ε (rreg ε)).subtype) :=
    isKStableSub_of_kStable hσ hD _ hS'f fun k hk v hv =>
      ⟨⟨rreg ε k v, hD.kStable k hk _ v.2⟩, hSK' k hk _ hv, rfl⟩
  let T : Fin n → Module.End ℂ (S.comap (smD ε (rreg ε)).subtype) :=
    fun c => (smE ε (rreg ε) c c).restrict (hS'k c c rfl)
  have hTs : ∀ c, (T c).IsSymmetric := fun c x z => hKU c c rfl (x : smD ε (rreg ε)) (z : smD ε (rreg ε))
  have hcomm : Pairwise (Function.onFun Commute T) := fun a c _ =>
    LinearMap.ext fun x => Subtype.ext (kUnit_diag_comm hE a c (x : smD ε (rreg ε)))
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hTs hcomm
  let e' : (S.comap (smD ε (rreg ε)).subtype) →ₗ[ℂ] N :=
    e.comp (Submodule.comapSubtypeEquivOfLe hSD).toLinearMap
  by_contra hno
  push_neg at hno
  have hle : ∀ χ : Fin n → ℂ, (⨅ c, Module.End.eigenspace (T c) (χ c)) ≤ LinearMap.ker e' := by
    intro χ x hx
    by_cases hx0 : x = 0
    · rw [hx0]
      exact Submodule.zero_mem _
    have hxc : ∀ c, smE ε (rreg ε) c c (x : smD ε (rreg ε)) = χ c • (x : smD ε (rreg ε)) := fun c =>
      congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hx c))
    have hx0' : (x : smD ε (rreg ε)) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hxν : ∀ c, smE ε (rreg ε) c c (x : smD ε (rreg ε)) =
        (((χ c).re : ℝ) : ℂ) • (x : smD ε (rreg ε)) := fun c =>
      (hxc c).trans (congrArg (· • (x : smD ε (rreg ε))) (kUnit_eig_real hKU hx0' (hxc c)))
    exact hno (fun c => (χ c).re) (Submodule.comapSubtypeEquivOfLe hSD x)
      ((isWtOn_iff hσ hD (x : smD ε (rreg ε)) _).2 hxν)
  have hker : LinearMap.ker e' = ⊤ := top_le_iff.mp (htop ▸ iSup_le hle)
  refine he (LinearMap.ext fun y => ?_)
  have hy : (Submodule.comapSubtypeEquivOfLe hSD).symm y ∈ LinearMap.ker e' := hker ▸ Submodule.mem_top
  have h2 : e' ((Submodule.comapSubtypeEquivOfLe hSD).symm y) = 0 := hy
  calc e y = e (Submodule.comapSubtypeEquivOfLe hSD ((Submodule.comapSubtypeEquivOfLe hSD).symm y)) := by
        rw [LinearEquiv.apply_symm_apply]
    _ = 0 := h2

end GlobalTheory.CompanionTheory.RgDsHilb
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorsSpanDenseStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_vectors_span_dense : PositivityTheory.RgDs.Hilb.StepWtSpan := by
  first | exact @GlobalTheory.CompanionTheory.RgDsHilb.stepWtSpan | exact GlobalTheory.CompanionTheory.RgDsHilb.stepWtSpan | (intros; apply GlobalTheory.CompanionTheory.RgDsHilb.stepWtSpan <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VoganMinimalTypeStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VoganMinimalTypeStatement
namespace GlobalTheory.CompanionTheory.DiscreteSeries

private lemma two_mul_rhoN_add_rhoC_eq_card_sub_card {n : ℕ} (ε : Fin n → Bool) (x : Fin n) :
    2 * (Formalism.REAL.rhoN ε x + Formalism.REAL.rhoC ε x) =
      (({y | x < y} : Finset (Fin n)).card : ℝ) - (({y | y < x} : Finset (Fin n)).card : ℝ) := by
  have hA : ({y | x < y ∧ ε y ≠ ε x} : Finset (Fin n)).card
      + ({y | x < y ∧ ε y = ε x} : Finset (Fin n)).card = ({y | x < y} : Finset (Fin n)).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases h : x < y <;> by_cases h' : ε y = ε x <;> simp [h, h']
  have hB : ({y | y < x ∧ ε y ≠ ε x} : Finset (Fin n)).card
      + ({y | y < x ∧ ε y = ε x} : Finset (Fin n)).card = ({y | y < x} : Finset (Fin n)).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases h : y < x <;> by_cases h' : ε y = ε x <;> simp [h, h']
  have hA' : (({y | x < y ∧ ε y ≠ ε x} : Finset (Fin n)).card : ℝ)
      + (({y | x < y ∧ ε y = ε x} : Finset (Fin n)).card : ℝ)
      = (({y | x < y} : Finset (Fin n)).card : ℝ) := by
    exact_mod_cast hA
  have hB' : (({y | y < x ∧ ε y ≠ ε x} : Finset (Fin n)).card : ℝ)
      + (({y | y < x ∧ ε y = ε x} : Finset (Fin n)).card : ℝ)
      = (({y | y < x} : Finset (Fin n)).card : ℝ) := by
    exact_mod_cast hB
  simp only [Formalism.REAL.rhoN, Formalism.REAL.rhoC]
  linarith

private lemma rhoN_add_rhoC_le_of_lt {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) :
    Formalism.REAL.rhoN ε b + Formalism.REAL.rhoC ε b ≤ Formalism.REAL.rhoN ε a + Formalism.REAL.rhoC ε a := by
  have h1 := two_mul_rhoN_add_rhoC_eq_card_sub_card ε a
  have h2 := two_mul_rhoN_add_rhoC_eq_card_sub_card ε b
  have c1 : ({y | b < y} : Finset (Fin n)).card ≤ ({y | a < y} : Finset (Fin n)).card := by
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact lt_trans hab hy
  have c2 : ({y | y < a} : Finset (Fin n)).card ≤ ({y | y < b} : Finset (Fin n)).card := by
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact lt_trans hy hab
  have c1' : (({y | b < y} : Finset (Fin n)).card : ℝ) ≤ (({y | a < y} : Finset (Fin n)).card : ℝ) := by
    exact_mod_cast c1
  have c2' : (({y | y < a} : Finset (Fin n)).card : ℝ) ≤ (({y | y < b} : Finset (Fin n)).card : ℝ) := by
    exact_mod_cast c2
  linarith

private lemma nsq_le_nsq_add_of_dot_nonneg {n : ℕ} (v w : Fin n → ℝ) (h : 0 ≤ Formalism.REAL.dot v w) :
    Formalism.REAL.nsq v ≤ Formalism.REAL.nsq (v + w) := by
  unfold Formalism.REAL.nsq Formalism.REAL.dot at *
  have h2 : 0 ≤ ∑ a, w a * w a := Finset.sum_nonneg (fun a _ => mul_self_nonneg (w a))
  have e : ∑ a, (v + w) a * (v + w) a = ∑ a, v a * v a + 2 * ∑ a, v a * w a + ∑ a, w a * w a := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => by simp only [Pi.add_apply]; ring)
  rw [e]
  linarith

private lemma dot_nonneg_sum_root_of_antitone {n : ℕ} (v : Fin n → ℝ) (c : Fin n → Fin n → ℕ)
    (hc : ∀ a b : Fin n, c a b ≠ 0 → a < b) (hmono : ∀ a b : Fin n, a < b → v b ≤ v a) :
    0 ≤ Formalism.REAL.dot v (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b) := by
  have hdot : Formalism.REAL.dot v (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b)
      = ∑ a, ∑ b, (c a b : ℝ) * (v a - v b) := by
    unfold Formalism.REAL.dot
    simp only [Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, Formalism.REAL.root, Pi.sub_apply, Pi.single_apply, mul_sub,
      Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  rw [hdot]
  refine Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => ?_))
  by_cases h0 : c a b = 0
  · simp [h0]
  · exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hmono a b (hc a b h0)))


open GlobalTheory.LowestKTypeDetermines in
theorem stepVogan : PositivityTheory.RgDs.Hilb.StepVogan := by
  intro n ε lam η hlam hη
  obtain ⟨c, hc, rfl⟩ := hη
  have hk : ReciprocityTheory.ChartRestriction.DS.lowK ε lam = Formalism.QuantumDeterminants.lowK ε lam := by rfl
  unfold Formalism.MainNotions.S.vNormSq
  rw [hk, add_right_comm]
  apply nsq_le_nsq_add_of_dot_nonneg
  apply dot_nonneg_sum_root_of_antitone _ c hc
  intro a b hab
  simp only [Formalism.QuantumDeterminants.lowK, two_nsmul, two_smul, Pi.add_apply, Pi.sub_apply]
  have h1 := rhoN_add_rhoC_le_of_lt ε hab
  have h2 := hlam.1 hab
  linarith

end GlobalTheory.CompanionTheory.DiscreteSeries
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VoganMinimalTypeStatementStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vogan_minimal_type_statement : PositivityTheory.RgDs.Hilb.StepVogan := by
  first | exact @GlobalTheory.CompanionTheory.DiscreteSeries.stepVogan | exact GlobalTheory.CompanionTheory.DiscreteSeries.stepVogan | (intros; apply GlobalTheory.CompanionTheory.DiscreteSeries.stepVogan <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleOfDiscreteSeriesDatum
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleOfDiscreteSeriesDatum
noncomputable section

open Finset Matrix

namespace GlobalTheory.CompanionTheory.RgDsHilb

open ReciprocityTheory.ChartRestriction.DS PositivityTheory.RgDs PositivityTheory.RgDs.Hilb

variable {n : ℕ}

theorem isKTypeOf_map_of_injOn {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Λ : Fin n → ℝ} {S : Submodule ℂ H}
    (hS : Formalism.MainNotions.S.IsKTypeOf ε σ Λ S) (A : H →ₗ[ℂ] H)
    (hcomm : ∀ k ∈ Kset ε, ∀ v, σ k (A v) = A (σ k v))
    (hinj : ∀ w ∈ S, A w = 0 → w = 0) :
    Formalism.MainNotions.S.IsKTypeOf ε σ Λ (S.map A) := by
  haveI : FiniteDimensional ℂ S := hS.1
  have hirr : ∀ S' : Submodule ℂ H, S' ≤ S.map A → Formalism.MainNotions.S.IsKStableOn ε σ S' →
      S' = ⊥ ∨ S' = S.map A := by
    intro S' hS' hK'
    have hTK : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ S'.comap A) := by
      intro g hg v hv
      rw [Submodule.mem_inf] at hv ⊢
      refine ⟨hS.2.1 g hg v hv.1, ?_⟩
      show A (σ g v) ∈ S'
      rw [← hcomm g hg v]
      exact hK' g hg _ hv.2
    rcases hS.2.2.1 (S ⊓ S'.comap A) inf_le_left hTK with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hS' hx
      have hwT : w ∈ S ⊓ S'.comap A := Submodule.mem_inf.2 ⟨hw, hx⟩
      rw [h] at hwT
      rw [(Submodule.mem_bot ℂ).1 hwT, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hS' ?_
      rintro _ ⟨w, hw, rfl⟩
      have hwT : w ∈ S ⊓ S'.comap A := by rw [h]; exact hw
      exact (Submodule.mem_inf.1 hwT).2
  refine ⟨inferInstance, ?_, hirr, ?_, ?_⟩
  · rintro g hg _ ⟨w, hw, rfl⟩
    exact ⟨σ g w, hS.2.1 g hg w hw, (hcomm g hg w).symm⟩
  · obtain ⟨v, hv, hv0, hwt⟩ := hS.2.2.2.1
    refine ⟨A v, ⟨v, hv, rfl⟩, fun h => hv0 (hinj v hv h), ?_⟩
    intro θ hθ
    rw [hcomm _ hθ, hwt θ hθ, map_smul]
  · rintro μ _ ⟨w, hw, rfl⟩ hne hwt
    refine hS.2.2.2.2 μ w hw (fun h => hne (by rw [h, map_zero])) ?_
    intro θ hθ
    have h1 : A (σ (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) w -
        Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • w) = 0 := by
      rw [map_sub, map_smul, ← hcomm _ hθ, hwt θ hθ, sub_self]
    have h2 := hinj _ (Submodule.sub_mem _ (hS.2.1 _ hθ w hw) (Submodule.smul_mem _ _ hw)) h1
    exact sub_eq_zero.1 h2

theorem stepIrred_of_stepDatum : StepDatum → StepIrred := by
  intro hDatum n ε lam T Ψ hP _hst huniq W hWle hWc hWG
  classical
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hV1 : Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) (lowK ε lam) (V1 ε Ψ) := hDatum n ε lam T Ψ hP
  have : CompleteSpace W := hWc.completeSpace_coe
  have hWo : ∀ g ∈ UJset ε, ∀ x ∈ Wᗮ, rreg ε g x ∈ Wᗮ := by
    intro g hg
    obtain ⟨g', hg', hgg⟩ := UnitaryGroupOfForm.inv_mem_UJ hg
    exact UnitaryGroupOfForm.orth_stable hσ hg hg' hgg W (hWG g' hg')
  have hK : Formalism.MainNotions.S.IsKStableOn ε (rreg ε) (V1 ε Ψ ⊓ Wᗮ) := by
    intro k hk x hx
    exact ⟨hV1.2.1 k hk x hx.1, hWo k (UnitaryGroupOfForm.K_mem_UJ hk) x hx.2⟩
  have hmem : ∀ v ∈ datumV ε Ψ T.w, ((v : smD ε (rreg ε)) : L2 ε) ∈ V1 ε Ψ :=
    fun v hv => Submodule.mem_map_of_mem hv
  rcases hV1.2.2.1 (V1 ε Ψ ⊓ Wᗮ) inf_le_left hK with h0 | hV'
  · right
    refine le_antisymm hWle (UnitaryGroupOfForm.closGen_le hD W hWc hWG _ ?_)
    have hcomm : ∀ k ∈ Kset ε, ∀ v, rreg ε k (W.starProjection.toLinearMap v) =
        W.starProjection.toLinearMap (rreg ε k v) := by
      intro k hk v
      have hkU := UnitaryGroupOfForm.K_mem_UJ hk
      exact (UnitaryGroupOfForm.proj_comm W (rreg ε k) (hWG k hkU) (hWo k hkU) v).symm
    have hinj : ∀ w ∈ V1 ε Ψ, W.starProjection.toLinearMap w = 0 → w = 0 := by
      intro w hw h
      have hwo : w ∈ Wᗮ := by
        have := W.sub_starProjection_mem_orthogonal w
        have h' : W.starProjection w = 0 := h
        rwa [h', sub_zero] at this
      have : w ∈ V1 ε Ψ ⊓ Wᗮ := ⟨hw, hwo⟩
      rw [h0] at this
      exact (Submodule.mem_bot ℂ).1 this
    have hle : (V1 ε Ψ).map W.starProjection.toLinearMap ≤ W := by
      rintro _ ⟨w, -, rfl⟩
      exact W.starProjection_apply_mem w
    have heq := huniq _ (hle.trans hWle) (isKTypeOf_map_of_injOn hV1 _ hcomm hinj)
    intro v hv
    have hv' : ((v : smD ε (rreg ε)) : L2 ε) ∈ (V1 ε Ψ).map W.starProjection.toLinearMap := by
      rw [heq]; exact hmem v hv
    exact hle hv'
  · left
    have hle : Hlam ε Ψ T.w ≤ Wᗮ :=
      UnitaryGroupOfForm.closGen_le hD Wᗮ (Submodule.isClosed_orthogonal W) hWo _
        (fun v hv => (show ((v : smD ε (rreg ε)) : L2 ε) ∈ V1 ε Ψ ⊓ Wᗮ by
          rw [hV']; exact hmem v hv).2)
    rw [eq_bot_iff, ← Submodule.inf_orthogonal_eq_bot W]
    exact le_inf le_rfl (hWle.trans hle)

end GlobalTheory.CompanionTheory.RgDsHilb
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleOfDiscreteSeriesDatumStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_of_discrete_series_datum : PositivityTheory.RgDs.Hilb.StepDatum → PositivityTheory.RgDs.Hilb.StepIrred := by
  first | exact @GlobalTheory.CompanionTheory.RgDsHilb.stepIrred_of_stepDatum | exact GlobalTheory.CompanionTheory.RgDsHilb.stepIrred_of_stepDatum | (intros; apply GlobalTheory.CompanionTheory.RgDsHilb.stepIrred_of_stepDatum <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsEqLogIdeleModule
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsEqLogIdeleModule
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh

theorem logAbs_eq_log_ideleModule (E : Type) [Field E] [NumberField E] [IsCMField E] (s : (Ad E)ˣ) :
    logAbs (s : Ad E) = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E s : ℝ) := by
  have hm : ∀ v : InfinitePlace E, v.mult = 2 := fun v =>
    InfinitePlace.mult_isComplex ⟨v, IsTotallyComplex.isComplex v⟩
  have hinf : ∀ w : InfinitePlace E, ‖(s : Ad E).1 w‖ ≠ 0 := fun w =>
    norm_ne_zero_iff.2 (GroundTheory.Global.IdeleGroup.infinite_ne_zero s w)
  have hfin : ∀ v : HeightOneSpectrum (𝓞 E), 0 < ‖(s : Ad E).2 v‖ := fun v =>
    norm_pos_iff.2 (GroundTheory.Global.IdeleGroup.finite_ne_zero s v)
  have hA : (∏ w : InfinitePlace E, ‖(s : Ad E).1 w‖ ^ w.mult) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (hinf w)
  have hB : (∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖(s : Ad E).2 v‖) ≠ 0 :=
    (GroundTheory.Global.IdeleGroup.finiteModule_pos s).ne'
  have e : (GroundTheory.Global.IdeleGroup.ideleModule E s : ℝ) =
      (∏ w : InfinitePlace E, ‖(s : Ad E).1 w‖ ^ w.mult) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖(s : Ad E).2 v‖ :=
    GroundTheory.Global.IdeleGroup.ideleModule_eq s
  rw [e, Real.log_mul hA hB, Real.log_prod (fun w _ => pow_ne_zero _ (hinf w)), Real.log_finprod hfin]
  unfold logAbs
  simp only [GlobalTheory.CompanionTheory.TorNorm.norm_cV, hm]
  rfl

end GlobalTheory.CompanionTheory.TorusCh

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsEqLogIdeleModuleStatement
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_abs_eq_log_idele_module : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (s : (Ad E)ˣ), logAbs (s : Ad E) = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E s : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.logAbs_eq_log_ideleModule | exact GlobalTheory.CompanionTheory.TorusCh.logAbs_eq_log_ideleModule | (intros; apply GlobalTheory.CompanionTheory.TorusCh.logAbs_eq_log_ideleModule <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocVanishOf
noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.LocVan

variable {n : ℕ}

theorem locVanish_of (hN : NilChange) (hQ : QuotVanish) : LocVanish := by
  intro n _ _ μ _ f u d μd _ W₁ W₂ hf hfc hV hsep hW1 hle h12 h21 hu hub huK huT huN
  have hTw : Continuous fun x : GL (Fin n) ℂ => twConj (thC n) x d :=
    (continuous_inv.mul continuous_const).mul continuous_thC
  refine hQ n μ d μd W₁ W₂ hsep hW1 hle h12 h21 _
    (((hf.comp hTw).measurable).mul hu) (fun t ht x => ?_) (fun x k hk => ?_) ?_
  · show f (twConj (thC n) (t * x) d) * u (t * x) = f (twConj (thC n) x d) * u x
    rw [twConj_mul_left _ _ ht, huT t ht]
  · show f (twConj (thC n) (x * k) d) * u (x * k) = f (twConj (thC n) x d) * u x
    have : twConj (thC n) (x * k) d = twConj (thC n) k (twConj (thC n) x d) := by
      simp only [twConj, map_mul, _root_.mul_inv_rev, mul_assoc]
    rw [this, hV.1 k _ hk, huK x k hk]
  · intro _ _ ν _ q
    obtain ⟨Φ, hΦc, hΦ, hΦν⟩ := hN n d W₁ W₂ hsep hW1 hle h12 h21
    obtain ⟨c, hc⟩ := hΦν ν

    set g : nilrad W₁ W₂ → ℂ := fun Y => f (q⁻¹ * uOf Y * d * thC n q) with hg
    have hgc : Continuous g :=
      hf.comp (((continuous_const.mul continuous_uOf).mul continuous_const).mul continuous_const)
    have e1 : ∀ X : nilrad W₁ W₂,
        f (twConj (thC n) (uOf X * q) d) * u (uOf X * q) = u q * g (Φ X) := fun X => by
      have hm : (uOf X).val - 1 ∈ nilrad W₁ W₂ := by simpa using X.2
      rw [huN _ hm, mul_comm]
      congr 2
      simp only [hg, hΦ, twConj, map_mul, _root_.mul_inv_rev]
      group
    have e2 : ∫ X, g (Φ X) ∂ν = (c : ℝ) • ∫ Y, g Y ∂ν := by
      rw [← integral_map hΦc.measurable.aemeasurable hgc.aestronglyMeasurable, hc,
        integral_smul_measure]
      simp
    simp only [e1]
    rw [integral_const_mul, e2]
    suffices h : ∫ Y, g Y ∂ν = 0 by simp [h]

    letI : MeasurableSpace (nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) := borel _
    haveI : BorelSpace (nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) := ⟨rfl⟩
    have hcn := continuous_conjNil q W₁ W₂
    haveI : (ν.map (conjNil q W₁ W₂)).IsAddHaarMeasure :=
      (conjNil q W₁ W₂).isAddHaarMeasure_map ν hcn (continuous_conjNil_symm q W₁ W₂)
    have key := hV.2 (twConj (thC n) q d) (img q⁻¹ W₁) (img q⁻¹ W₂) (img_ne_bot _ hW1)
      (img_le_img _ hle) (by rw [perpD_twConj, h12]) (by rw [perpD_twConj, h21]) uOf
      (fun X => uOf_val X) (ν.map (conjNil q W₁ W₂))
    have hcont : Continuous fun Z : nilrad (img q⁻¹ W₁) (img q⁻¹ W₂) =>
        f (uOf Z * twConj (thC n) q d) := hf.comp (continuous_uOf.mul continuous_const)
    rw [integral_map hcn.measurable.aemeasurable hcont.aestronglyMeasurable] at key
    rw [← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
    show f _ = f _
    rw [uOf_conjNil]
    congr 1
    simp only [twConj]
    group

end GlobalTheory.CompanionTheory.LocVan
end
end

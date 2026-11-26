module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOpenSubgroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedThetaGeneratorEqClassSumIntegralForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameGenAtTransport
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LabTies

section Galois

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

def conjHom (c : Ω ≃+* Ω) (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y) :
    G E Ω →* G E Ω where
  toFun := GlobalTheory.AntiRamConj.conjAut c hc
  map_one' := by
    ext x
    exact c.apply_symm_apply x
  map_mul' g h := by
    ext x
    change c (g (h (c.symm x))) = c (g (c.symm (c (h (c.symm x)))))
    rw [RingEquiv.symm_apply_apply]

theorem conjHom_apply (c : Ω ≃+* Ω) (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    (g : G E Ω) (x : Ω) : conjHom c hc g x = c (g (c.symm x)) := rfl

theorem continuous_conjHom (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y) : Continuous (conjHom c hc) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).1 hU
  obtain ⟨S, hS⟩ := IntermediateField.fg_of_fg_toSubalgebra L (Subalgebra.fg_of_fg_toSubmodule
    ((Submodule.fg_iff_finiteDimensional L.toSubalgebra.toSubmodule).2 hL))
  classical
  let L' := IntermediateField.adjoin E ((S.image c.symm : Finset Ω) : Set Ω)
  have hL' : FiniteDimensional E L' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine Filter.mem_map.2 (Filter.mem_of_superset
    ((IntermediateField.fixingSubgroup_isOpen L').mem_nhds (Subgroup.one_mem _)) fun g hg => hLU ?_)
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hg
  have key : L ≤ IntermediateField.fixedField (Subgroup.zpowers (conjHom c hc g)) := by
    rw [← hS, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    have h1 : conjHom c hc g x = x := by
      rw [conjHom_apply, hg _ (IntermediateField.subset_adjoin _ _ (by simpa using hx)), RingEquiv.apply_symm_apply]
    exact (Subgroup.zpowers_le (H := MulAction.stabilizer (G E Ω) x)).2 h1 hf
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixedField_iff _ _).1 (key hx) _ (Subgroup.mem_zpowers _)

theorem tameGenAt_transport (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    (hc' : ∀ x : E, ∃ y : E, c (algebraMap E Ω x) = algebraMap E Ω y)
    {B B' : ValuationSubring Ω} (hB : ∀ y, y ∈ B ↔ c y ∈ B') {γ γ' : G E Ω} (hγ : ∀ y, γ' (c y) = c (γ y))
    (h : TameGenAt B γ) : TameGenAt B' γ' := by
  have hc'' : ∀ x : E, ∃ y : E, c.symm.symm (algebraMap E Ω x) = algebraMap E Ω y := hc'
  have eB : B' = GlobalTheory.AntiRamConj.moveVal c B := by
    ext y
    rw [GlobalTheory.AntiRamConj.mem_moveVal, hB, RingEquiv.apply_symm_apply]
  have eγ : γ' = conjHom c hc γ := by
    ext y
    rw [conjHom_apply, ← hγ, RingEquiv.apply_symm_apply]
  subst eB eγ
  set f := conjHom c hc
  refine ⟨GlobalTheory.AntiRamConj.conjAut_mem_ine c hc h.1, fun σ hσ => ?_⟩
  have h1 := GlobalTheory.AntiRamConj.conjAut_mem_ine c.symm hc'' hσ
  have e2 : GlobalTheory.AntiRamConj.moveVal c.symm (GlobalTheory.AntiRamConj.moveVal c B) = B := by
    ext x
    simp [GlobalTheory.AntiRamConj.mem_moveVal]
  rw [e2] at h1
  have e3 : σ = f (GlobalTheory.AntiRamConj.conjAut c.symm hc'' σ) := by
    ext x
    rw [conjHom_apply, GlobalTheory.AntiRamConj.conjAut_apply]
    simp
  rw [e3]
  refine map_mem_closure (continuous_conjHom c hc) (h.2 h1) fun τ hτ => ?_
  have h2 := Subgroup.mem_map_of_mem f hτ
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨a, ha | ha, rfl⟩
  · exact Or.inl (congrArg f ha)
  · refine Or.inr fun y hy => ?_
    rw [GlobalTheory.AntiRamConj.moveVal_lt_one, map_sub, map_div₀, map_one, conjHom_apply, RingEquiv.symm_apply_apply]
    exact ha _ ((map_ne_zero_iff _ c.symm.injective).2 hy)

end Galois

theorem main : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut),
    GlobalTheory.PendOf.LabAll D T → IneRep D ∧ LabDepth D ∧ LabGen D := by
  intro D T ⟨γ, h1, h2, h3⟩
  have hG : GenFam D γ := by
    refine ⟨h1, fun k w hw => ?_⟩
    obtain ⟨v, rfl | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
    · rw [h1]
      exact D.ntypes.tg_gen k v
    · obtain ⟨c, hc1, hc2, hc3⟩ := h2 k v w hv
      refine tameGenAt_transport c (fun x => ⟨D.host.conj x, ?_⟩) (fun x => ⟨_, hc1 x⟩) hc2 hc3
        (D.ntypes.tg_gen k v)
      rw [RingEquiv.symm_apply_eq, hc1, GlobalTheory.AntiRamConj.host_conj_conj]
  have h3' : GlobalTheory.PendOf.Model.LabAll T γ := h3
  exact ⟨GlobalTheory.PendOf.Model.ineRep_of_tie T, GlobalTheory.PendOf.Model.labDepth_of_tie T hG h3',
    GlobalTheory.PendOf.Model.labGen_of_tie T hG h3'⟩

end GlobalTheory.LabTies

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.MSpanDecay

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def Growth (F : GA E a → ℂ) : Prop :=
  ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y : GL (Fin a) (Cinf E), ‖F (g * infGL E a y)‖ ≤ C * height y ^ N

def Good (F : GA E a → ℂ) : Prop :=
  ∃ h : F ∈ Sm E a, ∀ l : List (Lie E a),
    GlobalTheory.ShortVecDecay.Decays (GlobalTheory.GLFin.word l ⟨F, h⟩).1 ∧ Growth (GlobalTheory.GLFin.word l ⟨F, h⟩).1


theorem Growth.zero : Growth (0 : GA E a → ℂ) := fun _ => ⟨0, 0, fun _ => by simp⟩

theorem Growth.add {F G : GA E a → ℂ} (hF : Growth F) (hG : Growth G) : Growth (F + G) := fun g => by
  obtain ⟨C, N, h⟩ := hF g
  obtain ⟨C', N', h'⟩ := hG g
  refine ⟨|C| + |C'|, max N N', fun y => ?_⟩
  have h1 := one_le_height y
  have p1 : height y ^ N ≤ height y ^ max N N' := pow_le_pow_right₀ h1 (le_max_left _ _)
  have p2 : height y ^ N' ≤ height y ^ max N N' := pow_le_pow_right₀ h1 (le_max_right _ _)
  have q : 0 ≤ height y ^ N := by positivity
  have q' : 0 ≤ height y ^ N' := by positivity
  calc ‖(F + G) (g * infGL E a y)‖ ≤ ‖F (g * infGL E a y)‖ + ‖G (g * infGL E a y)‖ := norm_add_le _ _
    _ ≤ C * height y ^ N + C' * height y ^ N' := add_le_add (h y) (h' y)
    _ ≤ |C| * height y ^ max N N' + |C'| * height y ^ max N N' := by
        exact add_le_add ((mul_le_mul_of_nonneg_right (le_abs_self C) q).trans
            (mul_le_mul_of_nonneg_left p1 (abs_nonneg C))) ((mul_le_mul_of_nonneg_right (le_abs_self C') q').trans
            (mul_le_mul_of_nonneg_left p2 (abs_nonneg C')))
    _ = (|C| + |C'|) * height y ^ max N N' := by ring

theorem Growth.smul {F : GA E a → ℂ} (hF : Growth F) (z : ℂ) : Growth (z • F) := fun g => by
  obtain ⟨C, N, h⟩ := hF g
  refine ⟨‖z‖ * C, N, fun y => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h y) (norm_nonneg _)

theorem Good.mem_Sm {F : GA E a → ℂ} (h : Good F) : F ∈ Sm E a := h.1

theorem Good.decays {F : GA E a → ℂ} (h : Good F) : GlobalTheory.ShortVecDecay.Decays F := (h.2 []).1

theorem Good.growth {F : GA E a → ℂ} (h : Good F) : Growth F := (h.2 []).2

theorem word_cons (X : Lie E a) (l : List (Lie E a)) (φ : Sm E a) :
    GlobalTheory.GLFin.word (X :: l) φ = lie E a X (GlobalTheory.GLFin.word l φ) := by
  simp [GlobalTheory.GLFin.word, Module.End.mul_apply]

theorem word_append_single (l : List (Lie E a)) (X : Lie E a) (φ : Sm E a) :
    GlobalTheory.GLFin.word (l ++ [X]) φ = GlobalTheory.GLFin.word l (lie E a X φ) := by
  simp [GlobalTheory.GLFin.word, List.prod_append, Module.End.mul_apply]

theorem Good.derivative {F : GA E a → ℂ} (h : Good F) (X : Lie E a) : Good (lieD X F) := by
  obtain ⟨hF, hl⟩ := h
  refine ⟨lieD_mem_Sm X hF, fun l => ?_⟩
  have e : (⟨lieD X F, lieD_mem_Sm X hF⟩ : Sm E a) = lie E a X ⟨F, hF⟩ := rfl
  rw [e, ← word_append_single]
  exact hl _

theorem good_zero : Good (0 : GA E a → ℂ) := by
  refine ⟨zero_mem _, fun l => ?_⟩
  have e : (⟨0, zero_mem _⟩ : Sm E a) = 0 := rfl
  rw [e, map_zero]
  exact ⟨GlobalTheory.ShortVecDecay.Decays.zero, Growth.zero⟩

theorem Good.add {F G : GA E a → ℂ} (hF : Good F) (hG : Good G) : Good (F + G) := by
  obtain ⟨hF1, hF2⟩ := hF
  obtain ⟨hG1, hG2⟩ := hG
  refine ⟨add_mem hF1 hG1, fun l => ?_⟩
  have e : (⟨F + G, add_mem hF1 hG1⟩ : Sm E a) = ⟨F, hF1⟩ + ⟨G, hG1⟩ := rfl
  rw [e, map_add (f := _), Submodule.coe_add]
  exact ⟨(hF2 l).1.add (hG2 l).1, (hF2 l).2.add (hG2 l).2⟩

theorem Good.smul {F : GA E a → ℂ} (hF : Good F) (z : ℂ) : Good (z • F) := by
  obtain ⟨hF1, hF2⟩ := hF
  refine ⟨Submodule.smul_mem _ z hF1, fun l => ?_⟩
  have e : (⟨z • F, Submodule.smul_mem _ z hF1⟩ : Sm E a) = z • ⟨F, hF1⟩ := rfl
  rw [e, map_smul, Submodule.coe_smul]
  exact ⟨(hF2 l).1.smul z, (hF2 l).2.smul z⟩

theorem good_of_mem {π : CuspSub E a} (hπ : π.IsUnitary) {φ : Sm E a} (hφ : φ ∈ π.V) : Good φ.1 :=
  ⟨φ.2, fun l => ⟨GlobalTheory.ShortVecDecay.decays_of_mem hπ (GlobalTheory.ShortVecDecay.word_mem l hφ),
    (π.cusp _ (GlobalTheory.ShortVecDecay.word_mem l hφ)).1.growth⟩⟩

end GlobalTheory.MSpanDecay
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjGenTransportExists
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Pointwise

namespace GlobalTheory.ConjTransport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem symm_alg (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) (x : E) :
    c.symm (algebraMap E Ω x) = algebraMap E Ω (τ.symm x) := by
  rw [RingEquiv.symm_apply_eq, hτ, RingEquiv.apply_symm_apply]

def conjG (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) :
    G E Ω →* G E Ω where
  toFun g := AlgEquiv.ofRingEquiv (f := c.symm.trans (g.toRingEquiv.trans c)) (fun x => by
    simp only [RingEquiv.trans_apply, symm_alg c τ hτ, AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes, hτ, RingEquiv.apply_symm_apply])
  map_one' := by ext y; simp
  map_mul' g h := by ext y; simp

theorem conjG_apply (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x))
    (g : G E Ω) (y : Ω) : conjG c τ hτ g y = c (g (c.symm y)) := rfl

theorem conjG_apply_c (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x))
    (g : G E Ω) (y : Ω) : conjG c τ hτ g (c y) = c (g y) := by
  rw [conjG_apply, RingEquiv.symm_apply_apply]

theorem conjG_conjG_symm (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x))
    (g : G E Ω) : conjG c τ hτ (conjG c.symm τ.symm (symm_alg c τ hτ) g) = g := by
  ext y; simp [conjG_apply]

theorem conjG_continuous [Algebra.IsAlgebraic E Ω] (c : Ω ≃+* Ω) (τ : E ≃+* E)
    (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) : Continuous (conjG c τ hτ) := by
  classical
  apply continuous_of_continuousAt_one (conjG c τ hτ)
  rw [ContinuousAt, map_one]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨S, hS, hSU⟩ := hU
  let b := Module.finBasis E S
  let s : Finset Ω := Finset.univ.image (fun i => c.symm (b i : Ω))
  have hfin : FiniteDimensional E (IntermediateField.adjoin E (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := E) x).isIntegral)
  show _ ∈ nhds (1 : G E Ω)
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨_, hfin, fun g hg => hSU ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hg ⊢
  intro x hx
  have hb : ∀ i, conjG c τ hτ g (b i : Ω) = b i := by
    intro i
    rw [conjG_apply, hg _ (IntermediateField.subset_adjoin _ _ (by simp [s])), RingEquiv.apply_symm_apply]
  have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : Ω) := by
    have := congrArg (fun z : S => (z : Ω)) (b.sum_repr ⟨x, hx⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_smul] at this
    exact this.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx', map_sum]
  simp [map_smul, hb]

theorem mem_Dec_iff' {A : ValuationSubring Ω} {σ : G E Ω} :
    σ ∈ Dec (F := E) A ↔ ∀ y, σ y ∈ A ↔ y ∈ A := by
  constructor
  · exact fun h y => apply_mem_iff_of_mem_Dec h y
  · intro h
    show σ • A = A
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← h, mul_inv_apply]

theorem lt_one_transport {A A' : ValuationSubring Ω} (c : Ω ≃+* Ω) (hc : ∀ y, y ∈ A ↔ c y ∈ A') (y : Ω) :
    A.valuation y < 1 ↔ A'.valuation (c y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, ← hc, ← hc, map_eq_zero_iff _ c.injective]

theorem conjG_mem_Ine {A A' : ValuationSubring Ω} (c : Ω ≃+* Ω) (τ : E ≃+* E)
    (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) (hc : ∀ y, y ∈ A ↔ c y ∈ A') {g : G E Ω}
    (hg : g ∈ Ine (F := E) A) : conjG c τ hτ g ∈ Ine (F := E) A' := by
  have hsurj : ∀ y', ∃ y, y' = c y := fun y' => ⟨c.symm y', (c.apply_symm_apply y').symm⟩
  refine ⟨?_, ?_⟩
  · have hD : g ∈ Dec (F := E) A := hg.1
    show conjG c τ hτ g ∈ Dec (F := E) A'
    rw [mem_Dec_iff'] at hD ⊢
    intro y'
    obtain ⟨y, rfl⟩ := hsurj y'
    rw [conjG_apply_c, ← hc, ← hc, hD]
  · intro y' hy'
    obtain ⟨y, rfl⟩ := hsurj y'
    rw [conjG_apply_c, ← map_sub, ← lt_one_transport c hc]
    rw [ValuationSubring.valuation_le_one_iff, ← hc, ← ValuationSubring.valuation_le_one_iff] at hy'
    exact hg.2 y hy'

theorem conjG_mem_wild {A A' : ValuationSubring Ω} (c : Ω ≃+* Ω) (τ : E ≃+* E)
    (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) (hc : ∀ y, y ∈ A ↔ c y ∈ A') {g : G E Ω}
    (hg : ∀ y : Ω, y ≠ 0 → A.valuation (g y / y - 1) < 1) :
    ∀ y : Ω, y ≠ 0 → A'.valuation (conjG c τ hτ g y / y - 1) < 1 := by
  intro y' hy'
  obtain ⟨y, rfl⟩ : ∃ y, y' = c y := ⟨c.symm y', (c.apply_symm_apply y').symm⟩
  have hy : y ≠ 0 := fun h => hy' (by rw [h, map_zero])
  rw [conjG_apply_c, ← map_div₀, ← map_one c, ← map_sub, ← lt_one_transport c hc]
  exact hg y hy

end GlobalTheory.ConjTransport

namespace GlobalTheory

open GlobalTheory.ConjTransport

theorem conjGen_transport_exists : ∀ (D : D7) (w w' : PlE D.host) (γ : GE D.nd), IsConjPl D.host w w' →
    TameGenAt (D.nd.plOm.1 w) γ → ∃ γ' : GE D.nd, IsConjGen D w w' γ γ' ∧ TameGenAt (D.nd.plOm.1 w') γ' := by
  intro D w w' γ hww hγ
  let τ : D.host.E ≃+* D.host.E := (D.host.conj : D.host.E ≃+* D.host.E)
  let c₀ : D.nd.Om ≃+* D.nd.Om := IsAlgClosure.equivOfEquiv D.nd.Om D.nd.Om τ
  have hc₀ : ∀ x, c₀ (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (τ x) :=
    IsAlgClosure.equivOfEquiv_algebraMap D.nd.Om D.nd.Om τ
  set A := D.nd.plOm.1 w with hAdef
  set A' := D.nd.plOm.1 w' with hA'def
  have hA : IsPlaceOver A w := D.nd.plOm.2 w
  have hA' : IsPlaceOver A' w' := D.nd.plOm.2 w'
  let B : ValuationSubring D.nd.Om := A.comap (c₀.symm : D.nd.Om →+* D.nd.Om)
  have hAB : ∀ y, y ∈ A ↔ c₀ y ∈ B := fun y => by
    show y ∈ A ↔ c₀.symm (c₀ y) ∈ A
    rw [RingEquiv.symm_apply_apply]
  have hB : IsPlaceOver B w' := by
    intro x
    let x'' : 𝓞 D.host.E := ⟨τ.symm x, (x.isIntegral_coe).map (τ.symm : D.host.E →+* D.host.E).toIntAlgHom⟩
    have h1 : algebraMap D.host.E D.nd.Om (x : D.host.E) = c₀ (algebraMap D.host.E D.nd.Om (x'' : D.host.E)) := by
      rw [hc₀]; congr 1
      show (x : D.host.E) = τ (τ.symm (x : D.host.E)); exact (τ.apply_symm_apply _).symm
    rw [h1, ← lt_one_transport c₀ hAB, hA x'']
    exact hww x'' x (by show (x : D.host.E) = τ (τ.symm (x : D.host.E)); exact (τ.apply_symm_apply _).symm)
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hB hA'
  let c : D.nd.Om ≃+* D.nd.Om := c₀.trans σ.toRingEquiv
  have hcE : ∀ x, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (τ x) := by
    intro x
    show σ (c₀ _) = _
    rw [hc₀, AlgEquiv.commutes]
  have hcA : ∀ y, y ∈ A ↔ c y ∈ A' := by
    intro y
    rw [hAB, ← hσ, ← ValuationSubring.smul_mem_pointwise_smul_iff (g := σ), AlgEquiv.smul_def]
    rfl
  have hcA' : ∀ y, y ∈ A' ↔ c.symm y ∈ A := by
    intro y
    rw [hcA, RingEquiv.apply_symm_apply]
  refine ⟨conjG c τ hcE γ, ⟨c, fun x => hcE x, hcA, fun y => conjG_apply_c c τ hcE γ y⟩, ?_⟩
  refine ⟨conjG_mem_Ine c τ hcE hcA hγ.1, ?_⟩
  intro h hh
  have h1 := hγ.2 (conjG_mem_Ine c.symm τ.symm (symm_alg c τ hcE) hcA' hh)
  rw [← conjG_conjG_symm c τ hcE h]
  refine closure_mono ?_ (image_closure_subset_closure_image (conjG_continuous c τ hcE) ⟨_, h1, rfl⟩)
  rw [← Subgroup.coe_map, MonoidHom.map_closure]
  refine SetLike.coe_subset_coe.mpr (Subgroup.closure_mono ?_)
  rintro _ ⟨g, hg, rfl⟩
  rcases hg with rfl | hg
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (conjG_mem_wild c τ hcE hcA hg)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelTameCharacter
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType ValuativeRel Polynomial

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TameCharLabel

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {p : ℕ} [Fact p.Prime]

theorem red_natCast_val (hp : resCard F = p) (a : ZMod p) : red hp ((a.val : ℕ) : 𝒪[F]) = a := by
  rw [map_natCast, ZMod.natCast_zmod_val]

theorem valuation_natCast_val (hp : resCard F = p) (a : (ZMod p)ˣ) :
    valuation F ((((a : ZMod p).val : ℕ) : F)) = 1 := by
  have hu : IsUnit (((a : ZMod p).val : ℕ) : 𝒪[F]) :=
    isUnit_of_red_ne_zero hp (by rw [red_natCast_val]; exact a.ne_zero)
  have := (Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one.1 hu
  rwa [map_natCast] at this

theorem tame_eq {χ : Fˣ →* ℂˣ} (hχ : IsTame χ) {x y : Fˣ} (hy : valuation F (y : F) = 1)
    (hxy : valuation F ((x : F) - y) < 1) : χ x = χ y := by
  have h1 : valuation F (((x / y : Fˣ) : F) - 1) < 1 := by
    have : ((x / y : Fˣ) : F) - 1 = ((x : F) - y) / y := by
      rw [Units.val_div_eq_div_val, sub_div, div_self y.ne_zero]
    rw [this, map_div₀, hy, div_one]
    exact hxy
  have := hχ _ h1
  rwa [_root_.map_div, div_eq_one] at this

def unitOf (hp : resCard F = p) (a : (ZMod p)ˣ) : Fˣ :=
  Units.mk0 (((a : ZMod p).val : ℕ) : F) fun h => by
    have := valuation_natCast_val hp a
    rw [h, map_zero] at this
    exact zero_ne_one this

theorem eq_unitOf {χ : Fˣ →* ℂˣ} (hχ : IsTame χ) (hp : resCard F = p) (a : (ZMod p)ˣ) (x : Fˣ)
    (hx : valuation F ((x : F) - ((a : ZMod p).val : F)) < 1) : χ x = χ (unitOf hp a) :=
  tame_eq hχ (valuation_natCast_val hp a) hx

theorem exists_charLift (hp : resCard F = p) {χ : Fˣ →* ℂˣ} (hχ : IsTame χ) : ∃ θ : (ZMod p)ˣ →* ℂˣ, CharLift θ χ := by
  refine ⟨{ toFun := fun a => χ (unitOf hp a), map_one' := ?_, map_mul' := fun a b => ?_ }, fun a x hx => ?_⟩
  · have h := eq_unitOf hχ hp 1 1 (by
      have := (red_eq_iff_val hp 1 ((1 : (ZMod p)ˣ) : ZMod p)).1 (by simp)
      simpa using this)
    rw [map_one] at h
    exact h.symm
  · have h := eq_unitOf hχ hp (a * b) (unitOf hp a * unitOf hp b) (by
      have := (red_eq_iff_val hp (((a : ZMod p).val : ℕ) * ((b : ZMod p).val : ℕ) : 𝒪[F]) ((a * b : (ZMod p)ˣ) : ZMod p)).1
        (by rw [map_mul, red_natCast_val, red_natCast_val, Units.val_mul])
      rw [MulMemClass.coe_mul, SubringClass.coe_natCast, SubringClass.coe_natCast] at this
      rw [Units.val_mul]
      exact this)
    rw [map_mul] at h
    exact h.symm
  · exact eq_unitOf hχ hp a x hx

end Local

end GlobalTheory.TameCharLabel

namespace GlobalTheory.TameCharLabel

open NumberField IsDedekindDomain GlobalTheory.SerSys.TameGen GlobalTheory.Published.DepthZeroModel

theorem inflates_det {E : Type} [Field E] [NumberField E] {g : ℕ} [Fact g.Prime] {w : HeightOneSpectrum (𝓞 E)}
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) {θ : (ZMod g)ˣ →* ℂˣ} {χ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hχ : IsSmoothChar χ) (hθ : CharLift θ χ) :
    Inflates ((IrrRep.det (Fin 1) χ hχ).ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) (tauOne θ) := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  refine ⟨LinearMap.id, fun e => (one_ne_zero : (1 : ℂ) ≠ 0) (LinearMap.congr_fun e (1 : ℂ)), fun k (v : ℂ) => ?_⟩
  set c := Matrix.GeneralLinearGroup.det k
  have e2 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k)) =
      Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom c) := by
    ext; simp [c, GlobalTheory.GLp.inc, RingHom.map_det]
  have e3 : Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.red g 1 k) =
      Units.map (PadicInt.toZMod (p := g)).toMonoidHom c := by
    ext; simp [c, GlobalTheory.GLp.red, RingHom.map_det]
  set r : ℕ := (PadicInt.toZMod (c : ℤ_[g])).val
  have hk : ‖(((c : ℤ_[g]) - r : ℤ_[g]) : ℚ_[g])‖ < 1 := by
    have : (c : ℤ_[g]) - r ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at this
    exact this
  have h6 := he.lt_one_iff_lt_one.2 (GlobalTheory.Published.DepthZeroTypeModel.v_lt_one i hi hk)
  have h7 : χ (Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom c)) =
      θ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom c) := by
    refine hθ _ _ ?_
    convert h6 using 2
    simp [r]
  change ((θ (Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.red g 1 k)) : ℂˣ) : ℂ) • v =
    ((χ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k))) : ℂˣ) : ℂ) • v
  rw [e2, e3, h7]

end GlobalTheory.TameCharLabel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRootsInField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRootsInField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.TwInputs

variable {D : D7} {ρ : Setup D.ntw}

theorem de_mem_eO (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (z : (AE D)ˣ) :
    (((ρ.B i j b).de.chi z : Circle) : ℂ) ∈ (ρ.eO i b).range := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have : Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i), ?_⟩
  rw [hρ.delta i j b]
  exact (charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm

theorem e_mem_eO (ρ : Setup D.ntw) (i : D.ntw.Tw) (b : Bool) {a : FractionRing (D.ntw.O i)} {n : ℕ}
    (hn : n ≠ 0) (h : ρ.e i b a ^ n = 1) : ρ.e i b a ∈ (ρ.eO i b).range := by
  have h1 : a ^ n = 1 := (ρ.e i b).injective (by rw [map_pow, h, map_one])
  have hi : IsIntegral (D.ntw.O i) a := ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [h1]⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact ⟨y, rfl⟩

theorem typeCharacterExtension_value_mem_coefficientRing {hρ : ρ.Good} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} {rd : Rd ρ D.nexp i j b}
    (T : CellTie hρ D.nexp rd) (g : G0 (ρ.B i j b).G.Pg (Wc D j).rank) :
    ((ext1 (ρ.B i j b).G.P.H (⇑(ρ.B i j b).G.P.chi) g : ℂˣ) : ℂ) ∈ (ρ.eO i b).range := by
  unfold ext1
  split_ifs with h
  · obtain ⟨g', rfl⟩ := (ρ.eG i j b).surjective g
    have e1 := T.psiU_eq ⟨g', (T.U_eq g').1 h⟩ h
    have hfin : ((ρ.B i j b).G.P.chi ⟨ρ.eG i j b g', h⟩) ^ Nat.card (ρ.B i j b).G.P.H = 1 := by
      rw [← map_pow, pow_card_eq_one', map_one]
    rw [e1]
    refine e_mem_eO ρ i b (n := Nat.card (ρ.B i j b).G.P.H) Nat.card_pos.ne' ?_
    rw [← e1, ← Units.val_pow_eq_pow_val, hfin, Units.val_one]
  · exact one_mem _

theorem card_residueField_of_type {k : Fin 2} {PP : Pl D.host.E} (h : PP ∈ placesOver D.host.E (D.host.g k)) :
    Nat.card (kP PP) = D.host.g k :=
  GlobalTheory.SplitResidueCard.card_quotient_of_ncard (F := D.host.E) (D.host.g_prime k) (D.nd.g_split k) PP h

theorem muC_mem_eO (hρ : ρ.Good)
    (hr : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange)
    (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) {PP : Pl D.host.E} (hPP : PP ∈ (ρ.B i j b).G.Pg) (w : (kP PP)ˣ) :
    (((ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ∈ (ρ.eO i b).range := by
  obtain ⟨k, hk⟩ := hρ.Pg i j b PP hPP
  have hw : w ^ (D.host.g k - 1) = 1 := by
    rw [← card_residueField_of_type hk, ← Nat.card_units]
    exact pow_card_eq_one'
  have hz : (((ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ^ (D.host.g k * (D.host.g k - 1)) = 1 := by
    rw [mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, hw, map_one, Units.val_one, one_pow]
  obtain ⟨x, hx⟩ := hr k _ hz
  have h2 := (D.host.g_prime k).two_le
  have e : ρ.e i b (sideEmb D.ntw i b x) = (((ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) := (hρ.e_LL0 i b x).trans hx
  rw [← e] at hz ⊢
  exact e_mem_eO ρ i b (Nat.mul_ne_zero (by omega) (by omega)) hz

theorem locC_mem {t : Twist D Circle} (ht : t.Good) {O : Subring ℂ} (h : ∀ x, ((t.chi x : Circle) : ℂ) ∈ O)
    (PP : Pl D.host.E) (w : (kP PP)ˣ) : ((t.locC PP w : ℂˣ) : ℂ) ∈ O := by
  unfold Twist.locC
  split_ifs with hq
  · obtain ⟨x, hx⟩ := GlobalTheory.ConjTwist.exists_isLocUnit (ht.split.isIdemAt hq) w
    show ((t.res PP w : Circle) : ℂ) ∈ _
    rw [← hx.eq (ht.res PP hq)]
    exact h x
  · simp

theorem levLam_mem_eOk {hρ : ρ.Good}
    (hr : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange)
    {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} {rd : Rd ρ D.nexp i j b} (T : CellTie hρ D.nexp rd) {k Q ψ} (hψ : TwOK i k Q ψ)
    (x : (ρ.B i j b).levJ (ρ.tw i b k Q ψ)) :
    (((ρ.B i j b).levLam (ρ.tw i b k Q ψ) x : ℂˣ) : ℂ) ∈ (ρ.eOk i b k).range := by
  obtain ⟨hg, -, hv⟩ := GlobalTheory.TwistGood.tw_good D _ _ ρ hρ i j b k Q ψ hψ
  have hle := hρ.range_le i b k
  have e : (ρ.B i j b).levLam (ρ.tw i b k Q ψ) x =
      levFn (ρ.B i j b).F.βS ((ρ.B i j b).levS (ρ.tw i b k Q ψ)) (Formalism.UG.bc (Lev.swapAE D) x.1.1) := by
    unfold Base.levLam Lev.levCharAfE
    rfl
  rw [e]
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod]
  refine mul_mem (mul_mem (hle (typeCharacterExtension_value_mem_coefficientRing T _)) (prod_mem fun PP hPP => prod_mem fun _ _ => hle (muC_mem_eO hρ hr i j b hPP _)))
    (prod_mem fun PP _ => ?_)
  rw [MonoidHom.mul_apply, Units.val_mul]
  exact mul_mem (hle (locC_mem (hρ.base i j b).de (de_mem_eO hρ i j b) PP _))
    (locC_mem (O := (ρ.eOk i b k).range) hg (fun z => (hv z).elim fun u hu => ⟨u, hu.symm⟩) PP _)

theorem admT4_of_full_compatibility : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), FullTie hρ rd →
    (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) →
    ∀ E : IntegralHeckeForms.XD D, IntegralHeckeForms.admT4 D.nexp E := by
  intro D ρ hρ rd hT hr E i _ j hj b k Q ψ hψ Sg _
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨j', rfl⟩ : ∃ j' : Fin D.R.m, j = (j' : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  have T := hT.tie i j' b
  rw [IntegralHeckeForms.ThPsi, Submodule.span_le]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨d, -, hx⟩ := hx
  have hg := (T.thPsi_iff k Q ψ hψ d x).1 hx
  obtain ⟨F, hF, e⟩ := GlobalTheory.T.twistedThetaGenerator_eq_classSum_integralForm D ρ hρ i j' b k Q ψ hψ (levLam_mem_eOk hr T hψ) _ _ _ (T.dat d) _ hg
  obtain ⟨f, hf, rfl⟩ := (T.mtLat_iff k Q ψ hψ F).1 hF
  refine ⟨f, hf, T.injective_rdK k ?_⟩
  rw [T.thP_eq k Q ψ hψ f ⟨x, e⟩]
  exact e.symm

end GlobalTheory.TwInputs

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRootsInFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admT4_of_roots_in_field : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), FullTie hρ rd → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) → ∀ E : IntegralHeckeForms.XD D, IntegralHeckeForms.admT4 D.nexp E := by
  first | exact @GlobalTheory.TwInputs.admT4_of_full_compatibility | exact GlobalTheory.TwInputs.admT4_of_full_compatibility | (intros; apply GlobalTheory.TwInputs.admT4_of_full_compatibility <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchwartzBruhatIntegrableMoments
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddPowLe
namespace GlobalTheory.OneAddPowBound

theorem one_add_pow_le : ∀ {t : ℝ}, (0 : ℝ) ≤ t → ∀ (k : ℕ),
    ((1 : ℝ) + t) ^ k ≤ (2 : ℝ) ^ k * ((1 : ℝ) + t ^ k) := by
  intro t ht k
  have htk : 0 ≤ t ^ k := pow_nonneg ht k
  have h2 : (0 : ℝ) ≤ 2 ^ k := pow_nonneg (by norm_num) k
  have h1 : (0 : ℝ) ≤ 1 + t := by linarith
  rcases le_total t 1 with h | h
  · have ha : (1 + t) ^ k ≤ (2 : ℝ) ^ k := pow_le_pow_left₀ h1 (by linarith) k
    have hb : (2 : ℝ) ^ k * 1 ≤ 2 ^ k * (1 + t ^ k) :=
      mul_le_mul_of_nonneg_left (by linarith) h2
    linarith
  · have ha : (1 + t) ^ k ≤ (2 * t) ^ k := pow_le_pow_left₀ h1 (by linarith) k
    rw [mul_pow] at ha
    have hb : (2 : ℝ) ^ k * t ^ k ≤ 2 ^ k * (1 + t ^ k) :=
      mul_le_mul_of_nonneg_left (by linarith) h2
    linarith

end GlobalTheory.OneAddPowBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchwartzBruhatIntegrableMoments
set_option synthInstance.maxSize 1000

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic.GJMatrix GlobalTheory.ThetaPoisson

open scoped Classical

namespace GlobalTheory.SchwartzBruhatMoments

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

theorem pInfPi_eq (x : Fin m → Ad E) :
    (fun i => pInf E (x i)) = (toMixedPi E m).symm (infPartPi x) := by
  rw [← toMixedPi_pInf, ContinuousLinearEquiv.symm_apply_apply]

theorem one_add_pow_le {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : (1 + t) ^ k ≤ 2 ^ k * (1 + t ^ k) := by
  first
  | exact @_root_.GlobalTheory.OneAddPowBound.one_add_pow_le
  | exact _root_.GlobalTheory.OneAddPowBound.one_add_pow_le
  | (apply _root_.GlobalTheory.OneAddPowBound.one_add_pow_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.OneAddPowBound.one_add_pow_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OneAddPowBound.one_add_pow_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OneAddPowBound.one_add_pow_le ..)

theorem integrable_arch (φ : SchwartzMap (Fin m → mixedEmbedding.mixedSpace E) ℂ) (k : ℕ) :
    Integrable (fun u => ‖φ u‖ * (1 + ‖(toMixedPi E m).symm u‖) ^ k) (mixedMeasurePi E) := by
  set S := (toMixedPi E m).symm
  set C := ‖(S : (Fin m → mixedEmbedding.mixedSpace E) →L[ℝ] (Fin m → Cinf E))‖
  have hC : 0 ≤ C := norm_nonneg _
  have hint : Integrable (fun u => ((1 + C) ^ k * 2 ^ k) * (‖φ u‖ + ‖u‖ ^ k * ‖φ u‖))
      (mixedMeasurePi E) :=
    ((φ.integrable (μ := mixedMeasurePi E)).norm.add
      (φ.integrable_pow_mul (mixedMeasurePi E) k)).const_mul _
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
  · exact (φ.continuous.norm.mul ((continuous_const.add S.continuous.norm).pow k)).aestronglyMeasurable
  · have h1 : ‖S u‖ ≤ C * ‖u‖ := (S : (Fin m → mixedEmbedding.mixedSpace E) →L[ℝ] (Fin m → Cinf E)).le_opNorm u
    have h2 : 1 + ‖S u‖ ≤ (1 + C) * (1 + ‖u‖) := by nlinarith [norm_nonneg u, norm_nonneg (S u)]
    have h3 : (1 + ‖S u‖) ^ k ≤ (1 + C) ^ k * (2 ^ k * (1 + ‖u‖ ^ k)) := by
      calc (1 + ‖S u‖) ^ k ≤ ((1 + C) * (1 + ‖u‖)) ^ k := pow_le_pow_left₀ (by positivity) h2 k
        _ = (1 + C) ^ k * (1 + ‖u‖) ^ k := mul_pow _ _ _
        _ ≤ (1 + C) ^ k * (2 ^ k * (1 + ‖u‖ ^ k)) :=
          mul_le_mul_of_nonneg_left (one_add_pow_le (norm_nonneg u) k) (by positivity)
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖φ u‖ * (1 + ‖S u‖) ^ k ≤ ‖φ u‖ * ((1 + C) ^ k * (2 ^ k * (1 + ‖u‖ ^ k))) :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = ((1 + C) ^ k * 2 ^ k) * (‖φ u‖ + ‖u‖ ^ k * ‖φ u‖) := by ring

theorem aestronglyMeasurable_weight (k : ℕ) :
    AEStronglyMeasurable (fun x : Fin m → Ad E => (1 + ‖fun i => pInf E (x i)‖) ^ k)
      (adeleMeasurePi E) := by
  have h : (fun x : Fin m → Ad E => (1 + ‖fun i => pInf E (x i)‖) ^ k) =
      (fun p : (Fin m → mixedEmbedding.mixedSpace E) × (Fin m → Af E) =>
        (1 + ‖(toMixedPi E m).symm p.1‖) ^ k) ∘ splitEquivPi E (Fin m) := by
    funext x
    simp only [Function.comp_apply, splitEquivPi_apply]
    rw [pInfPi_eq]
  rw [h]
  exact ((((continuous_const.add (toMixedPi E m).symm.continuous.norm).pow k).measurable.comp
    measurable_fst).comp (splitEquivPi E (Fin m)).measurable).aestronglyMeasurable

theorem integrable_tensor (φ : SchwartzMap (Fin m → mixedEmbedding.mixedSpace E) ℂ)
    {g : (Fin m → Af E) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi E) (k : ℕ) :
    Integrable (fun x => ‖schwartzBruhatTensorPi φ g x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k)
      (adeleMeasurePi E) := by
  have h : (fun x : Fin m → Ad E => ‖schwartzBruhatTensorPi φ g x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k) =
      (fun p : (Fin m → mixedEmbedding.mixedSpace E) × (Fin m → Af E) =>
        (‖φ p.1‖ * (1 + ‖(toMixedPi E m).symm p.1‖) ^ k) * ‖g p.2‖) ∘ splitEquivPi E (Fin m) := by
    funext x
    simp only [Function.comp_apply, splitEquivPi_apply, schwartzBruhatTensorPi, norm_mul]
    rw [pInfPi_eq]
    ring
  rw [h, measurePreserving_splitEquivPi.integrable_comp_emb (splitEquivPi E (Fin m)).measurableEmbedding]
  exact (integrable_arch φ k).mul_prod (integrable_of_mem_finiteSchwartzBruhatPi hg).norm

theorem compactSupport_and_integrable_moments :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (F : (Fin m → Ad E) → ℂ),
    F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin m) →
    (∃ L : Set (Fin m → Af E), IsCompact L ∧ ∀ x, F x ≠ 0 → (fun i => pFin E (x i)) ∈ L) ∧
    ∀ k : ℕ, Integrable (fun x => ‖F x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k)
      (GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E) := by
  intro E _ _ _ m F hF
  refine ⟨?_, fun k => ?_⟩
  · induction hF using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨φ, g, hg, rfl⟩ := hG
      refine ⟨tsupport g, hg.2, fun x hx => ?_⟩
      have e : (fun i => pFin E (x i)) = finPartPi x := rfl
      rw [e]
      apply subset_tsupport
      intro h0
      apply hx
      simp only [schwartzBruhatTensorPi, h0, mul_zero]
    | zero => exact ⟨∅, isCompact_empty, fun x hx => absurd rfl hx⟩
    | add G H _ _ hG hH =>
      obtain ⟨L1, h1, hL1⟩ := hG
      obtain ⟨L2, h2, hL2⟩ := hH
      refine ⟨L1 ∪ L2, h1.union h2, fun x hx => ?_⟩
      by_cases hGx : G x = 0
      · right
        apply hL2
        intro hH0
        apply hx
        simp [hGx, hH0]
      · left
        exact hL1 x hGx
    | smul c G _ hG =>
      obtain ⟨L, hL, hLx⟩ := hG
      exact ⟨L, hL, fun x hx => hLx x fun h0 => hx (by simp [h0])⟩
  · induction hF using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨φ, g, hg, rfl⟩ := hG
      exact integrable_tensor φ hg k
    | zero => simp
    | add G H hGm hHm hG hH =>
      refine (hG.add hH).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
      · exact (integrable_of_mem_schwartzBruhatPi (K := E) (ι := Fin m)
          (Submodule.add_mem _ hGm hHm)).aestronglyMeasurable.norm.mul (aestronglyMeasurable_weight k)
      · have hw : 0 ≤ (1 + ‖fun i => pInf E (x i)‖) ^ k := by positivity
        simp only [Pi.add_apply]
        rw [Real.norm_of_nonneg (by positivity), ← add_mul]
        exact mul_le_mul_of_nonneg_right (norm_add_le _ _) hw
    | smul c G _ hG =>
      refine (hG.const_mul ‖c‖).congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
      ring

end GlobalTheory.SchwartzBruhatMoments
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchwartzBruhatIntegrableMomentsStatement
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_integrable_moments : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (F : (Fin m → Ad E) → ℂ),
    F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin m) →
    (∃ L : Set (Fin m → Af E), IsCompact L ∧ ∀ x, F x ≠ 0 → (fun i => pFin E (x i)) ∈ L) ∧
    ∀ k : ℕ, Integrable (fun x => ‖F x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k)
      (GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E) := by
  first | exact @GlobalTheory.SchwartzBruhatMoments.compactSupport_and_integrable_moments | exact GlobalTheory.SchwartzBruhatMoments.compactSupport_and_integrable_moments | (intros; apply GlobalTheory.SchwartzBruhatMoments.compactSupport_and_integrable_moments <;> assumption)
end
end

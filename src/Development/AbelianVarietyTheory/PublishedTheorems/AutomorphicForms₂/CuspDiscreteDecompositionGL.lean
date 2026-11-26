module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
noncomputable section

open NumberField MeasureTheory Matrix
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CuspRep.CuspidalL2GL

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
  {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]


variable (μ) in
def IsKFinL2 (F : L2 (latticeGL E a) μ) : Prop :=
  IsOpen {k : GL (Fin a) (Af E) | R (latticeGL E a) μ (finGL E a k) F = F} ∧
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Kinf E a => R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) F))


variable (μ) in
structure IsFinitePartOf (π : CuspSub E a) (H : Submodule ℂ (L2 (latticeGL E a) μ)) : Prop where
  normalised : IsNormalised π
  finitePartMemL2 : ∀ φ ∈ π.V, MemL2Quotient (latticeGL E a) μ φ.1
  closure_eq : (classes π.V μ).topologicalClosure = H
  kfin : ∀ F ∈ H, IsKFinL2 μ F → F ∈ classes π.V μ

theorem isKFinL2_of_mem_classes {π : CuspSub E a} (h : ∀ φ ∈ π.V, MemL2Quotient (latticeGL E a) μ φ.1)
    {F : L2 (latticeGL E a) μ} (hF : F ∈ classes π.V μ) : IsKFinL2 μ F := by
  obtain ⟨φ, rfl⟩ := (range_toL2ₗ h).ge hF
  have hc := (π.cusp _ φ.2).1
  have hi := toL2ₗ_injective h fun ψ hψ => ContAut.continuous_of_isOpen_stab E a ψ (π.cusp ψ hψ).1.level
  refine ⟨?_, ?_⟩
  · convert hc.level using 1
    ext k
    exact (R_toL2ₗ h φ (π.stable (.fin k) _ φ.2)).congr_left.trans (hi.eq_iff.trans Subtype.ext_iff)
  · have := hc.kfin
    have : FiniteDimensional ℂ ((Submodule.span ℂ (Set.range fun k => cptRep E a k φ.1)).comap π.V.subtype) :=
      (Submodule.comapSubtypeEquivOfLe (Submodule.span_le.2 (by
        rintro _ ⟨k, rfl⟩
        exact π.stable (.cpt k) _ φ.2))).symm.finiteDimensional
    refine Submodule.finiteDimensional_of_le (S₂ := ((Submodule.span ℂ (Set.range fun k => cptRep E a k φ.1)).comap
      π.V.subtype).map (toL2ₗ μ π.V h)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨_, π.stable (.cpt k) _ φ.2⟩, Submodule.subset_span ⟨k, rfl⟩,
      (R_toL2ₗ h φ (π.stable (.cpt k) _ φ.2)).symm⟩

namespace IsFinitePartOf

variable {π : CuspSub E a} {H : Submodule ℂ (L2 (latticeGL E a) μ)}

theorem classes_le (h : IsFinitePartOf μ π H) : classes π.V μ ≤ H :=
  h.closure_eq ▸ Submodule.le_topologicalClosure _

theorem mem_classes_iff (h : IsFinitePartOf μ π H) {F : L2 (latticeGL E a) μ} :
    F ∈ classes π.V μ ↔ F ∈ H ∧ IsKFinL2 μ F :=
  ⟨fun hF => ⟨h.classes_le hF, isKFinL2_of_mem_classes h.finitePartMemL2 hF⟩, fun hF => h.kfin F hF.1 hF.2⟩

theorem unique {π' : CuspSub E a} (h : IsFinitePartOf μ π H) (h' : IsFinitePartOf μ π' H) : π = π' := by
  have key : ∀ {π π' : CuspSub E a}, IsFinitePartOf μ π H → IsFinitePartOf μ π' H → π.V ≤ π'.V := by
    intro π π' h h' φ hφ
    obtain ⟨ψ, hψ, e⟩ := h'.mem_classes_iff.2 (h.mem_classes_iff.1 (toL2_mem_classes hφ (h.finitePartMemL2 φ hφ)))
    rwa [show φ = ψ from Subtype.ext ((Continuous.ae_eq_iff_eq μ
      (ContAut.continuous_of_isOpen_stab E a φ (π.cusp φ hφ).1.level)
      (ContAut.continuous_of_isOpen_stab E a ψ (π'.cusp ψ hψ).1.level)).1 ((h.finitePartMemL2 φ hφ).lift_toL2_ae_eq.symm.trans e))]
  exact CuspSub.ext (le_antisymm (key h h') (key h' h))

end IsFinitePartOf

theorem isIrredSubrep_map {W : Submodule ℂ (L2cusp μ)} (h : IsIrredSubrep (Rcusp μ) W) :
    IsIrredSubrep (R (latticeGL E a) μ) (W.map (L2cusp μ).subtype) := by
  have hW := isSubrep_L2cusp μ
  have hinj := Submodule.map_injective_of_injective (Submodule.injective_subtype (L2cusp μ))
  refine ⟨hW.isSubrep_rep_iff.1 h.1, fun e => h.2.1 (hinj (e.trans (Submodule.map_bot _).symm)), fun U hU hs => ?_⟩
  have e : (U.comap (L2cusp μ).subtype).map (L2cusp μ).subtype = U := by
    rw [Submodule.map_comap_subtype, inf_eq_right.2 (hU.trans (Submodule.map_subtype_le _ _))]
  exact (h.2.2 (U.comap (L2cusp μ).subtype) ((Submodule.comap_mono hU).trans
    (Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _) W).le)
    (hW.isSubrep_rep_iff.2 (e.symm ▸ hs))).imp (fun h0 => by rw [← e, h0, Submodule.map_bot]) fun h0 => by rw [← e, h0]

end GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.Published

def CuspDiscreteDecompositionGL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant], IsDiscreteSum (Rcusp μ)

def CuspFiniteVectorsGL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ →
      IsIrredSubrep (R (latticeGL E a) μ) H → ∃ π : CuspSub E a, IsFinitePartOf μ π H

def CuspFormsBoundedGL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsCuspForm φ →
    (∀ t g, ‖φ.1 (splitCentre E a t * g)‖ = ‖φ.1 g‖) → ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C

def CuspidalSpectrumGL : Prop := CuspDiscreteDecompositionGL ∧ CuspFiniteVectorsGL ∧ CuspFormsBoundedGL

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem CuspFormsBoundedGL.of_isUnitary (h : CuspFormsBoundedGL) {π : CuspSub E a} (hπ : π.IsUnitary) {φ : Sm E a}
    (hφ : φ ∈ π.V) : ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C :=
  h E a φ (π.cusp φ hφ) fun t g => by rw [splitCentre_eq_scalar, hπ.norm_eq hφ]

theorem CuspFormsBoundedGL.of_invariant (h : CuspFormsBoundedGL) {φ : Sm E a} (hφ : IsCuspForm φ)
    (h' : ∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) : ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C :=
  h E a φ hφ fun t g => by rw [h']

theorem CuspFormsBoundedGL.isUnitary (h : CuspFormsBoundedGL) {π : CuspSub E a} (hπ : IsNormalised π) :
    π.IsUnitary := by
  obtain ⟨ω, hω⟩ := Central.exists_hasCentral E a π
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨C, hC⟩ := h.of_invariant (π.cusp φ hφ) (hπ φ hφ)
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := Function.ne_iff.1 fun e => h0 (Subtype.ext e)
  have hle : ∀ x, ‖((ω.1 x : ℂˣ) : ℂ)‖ ≤ 1 := fun x => by
    by_contra hc
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / ‖φ.1 g‖) (not_le.1 hc)
    have := hC (GeneralLinearGroup.scalar (Fin a) (x ^ n) * g)
    rw [hω.apply hφ, norm_mul, map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
    exact hn.not_ge ((le_div_iff₀ (norm_pos_iff.2 hg)).2 this)
  refine ⟨ω, fun x => le_antisymm (hle x) ?_, hω⟩
  have := hle x⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at this
  exact (inv_le_one₀ (norm_pos_iff.2 (Units.ne_zero _))).1 this

end GlobalTheory.Published

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GenericOfIsIsoRestrict
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.Published


open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.Published.generic_of_isIso_restrict {X X' : Scheme.{0}} [IsIntegral X]
    [IsIntegral X'] (π : X' ⟶ X) (U : X.Opens)
    (hU : (U : Set X).Nonempty) [IsIso (π ∣_ U)] :
    π (genericPoint X') = genericPoint X ∧ π.residueDegree (genericPoint X') = 1 := by
  have hrange : (U : Set X) ⊆ Set.range π := by
    intro y hy
    obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso ((π ∣_ U).base)).2 ⟨y, hy⟩
    refine ⟨x.1, ?_⟩
    have := congrArg Subtype.val hx
    simpa [morphismRestrict_base_coe] using this
  have hgen : π (genericPoint X') = genericPoint X := by
    have h1 := (genericPoint_spec X').image π.continuous
    have hdense : closure (Set.range π) = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← (U.isOpen.dense hU).closure_eq]
      exact closure_mono hrange
    rw [Set.image_univ, hdense] at h1
    exact h1.eq (genericPoint_spec X)
  refine ⟨hgen, ?_⟩
  have hmem : genericPoint X' ∈ π ⁻¹ᵁ U := by
    show π (genericPoint X') ∈ U
    rw [hgen]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  obtain ⟨x, hx⟩ : genericPoint X' ∈ Set.range (π ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]; exact hmem
  have h1 := _root_.GlobalTheory.CurveDegreesCompare.residueDegree_comp (π ∣_ U) U.ι x
  have h2 := _root_.GlobalTheory.CurveDegreesCompare.residueDegree_comp (π ⁻¹ᵁ U).ι π x
  rw [morphismRestrict_ι, h2, _root_.GlobalTheory.CurveDegreesCompare.residueDegree_of_isOpenImmersion (π ⁻¹ᵁ U).ι,
    _root_.GlobalTheory.CurveDegreesCompare.residueDegree_of_isOpenImmersion U.ι,
    _root_.GlobalTheory.CurveDegreesCompare.residueDegree_of_isOpenImmersion (π ∣_ U), hx] at h1
  simpa using h1


open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.Published.arBirational_of_arProj (H : _root_.GlobalTheory.Published.ArProj) :
    _root_.GlobalTheory.Published.ArBirational := by
  intro k _ X X' _ _ p p' D hp hp' _ _ π hπ U hU hiso L a hL
  obtain ⟨hgen, hdeg⟩ := _root_.GlobalTheory.Published.generic_of_isIso_restrict π U hU
  have := (H k X X' p p' D hp hp' π hπ hgen (by rw [hdeg]; exact one_ne_zero)).1 L a hL
  simpa [hdeg] using this

end GlobalTheory.Published
end
end

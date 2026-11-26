module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRestrictionBlockEmbeddingIntertwinesLie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FixedCongruenceNeBotOfJacquetTorusFixed
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CongruenceSubgroupEqDiagonalUnipotentLowerIwahor
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

private theorem inv_int {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] [LinearOrder n] {c : GL n k}
    (hc : c ∈ GlobalTheory.SmGL.IwahoriOnto.lowerInt k n) (i j : n) : valuation k ((c⁻¹).val i j) ≤ 1 := by
  let M : Matrix n n 𝒪[k] := Matrix.of fun i j => ⟨c.val i j, hc.1 i j⟩
  have hdet : c.val.det = 1 := by
    rw [Matrix.det_of_lowerTriangular c.val fun i j hij => hc.2.1 i j hij]
    simp [hc.2.2]
  have hM : (algebraMap 𝒪[k] k).mapMatrix M = c.val := by ext i j; rfl
  have e : (c⁻¹).val = (algebraMap 𝒪[k] k).mapMatrix M.adjugate := by
    rw [RingHom.map_adjugate, hM, Matrix.coe_units_inv, Matrix.inv_def, hdet]
    simp
  rw [e]
  exact (M.adjugate i j).2

theorem UpperTheory.congruence_subgroup_eq_diagonal_unipotent_lower_iwahori :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1),
    ∀ g ∈ GlobalTheory.CentralExponent.cong (Fin N) γ hγ, ∃ d : Fin N → kˣ, (∀ i, valuation k ((d i : k) - 1) < γ) ∧
      ∃ x ∈ unipB k (Fin N), ∃ c ∈ GlobalTheory.SmGL.IwahoriOnto.lowerInt k (Fin N), g = diagT k (Fin N) d * x * c := by
  intro k _ _ _ _ N γ hγ g hg
  have hg' : ∀ i j, valuation k ((g.val - 1) i j) < γ := hg
  have h1 : g ∈ KOne k (Fin N) := GlobalTheory.StepData.mem_KOne.2 fun i j => (hg' i j).trans_le hγ
  have hI : g ∈ iwahori k (Fin N) := by
    refine mem_iwahori.2 ⟨GlobalTheory.StepData.KOne_le_KO h1, fun i j hij => ?_⟩
    have := (hg' i j).trans_le (show ((γ : ValueGroupWithZero k)) ≤ 1 from hγ)
    rwa [Matrix.sub_apply, Matrix.one_apply_ne hij.ne', sub_zero] at this
  obtain ⟨d, -, x, hx, c, hc, e⟩ := GlobalTheory.SmGL.IwahoriOnto.iwahori_factor k (Fin N) g hI
  refine ⟨d, fun i => ?_, x, hx, c, hc, e⟩
  have hcl : c ∈ unipBLower k (Fin N) :=
    (mem_unipB (n := (Fin N)ᵒᵈ) k).2 ⟨fun i j hij => hc.2.1 i j hij, hc.2.2⟩
  have hci : (c⁻¹).val i i = 1 := ((mem_unipB (n := (Fin N)ᵒᵈ) k).1 (inv_mem hcl)).2 i
  have h2 : (g * c⁻¹).val i i = d i := by
    rw [e, mul_inv_cancel_right, Units.val_mul, val_diagT, Matrix.diagonal_mul, ((mem_unipB k).1 hx).2 i, mul_one]
  have h3 : ((g.val - 1) * (c⁻¹).val) i i = (d i : k) - 1 := by
    rw [sub_mul, one_mul, Matrix.sub_apply, hci, ← Units.val_mul, h2]
  rw [← h3, Matrix.mul_apply]
  refine Valuation.map_sum_lt _ γ.ne_zero fun s _ => ?_
  rw [map_mul]
  exact (mul_le_of_le_one_right' (inv_int hc s i)).trans_lt (hg' i s)
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.fixed_congruence_ne_bot_of_jacquet_torus_fixed :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1),
    IsAdmissible π → ∀ y : Jacquet π (unipB k (Fin N)), y ≠ 0 →
    (∀ t : Fin N → kˣ, (∀ i, valuation k ((t i : k) - 1) < γ) → jacBU π t y = y) →
    fixed π (GlobalTheory.CentralExponent.cong (Fin N) γ hγ) ≠ ⊥ := by
  intro k _ _ _ _ N V _ _ π γ hγ hπ y hy0 hy hbot
  have hmem : ∀ d : Fin N → kˣ, diagT k (Fin N) d ∈ GlobalTheory.CentralExponent.cong (Fin N) γ hγ ↔
      ∀ i, valuation k ((d i : k) - 1) < γ := by
    intro d
    constructor
    · intro h i
      have := h i i
      simpa [val_diagT] using this
    · intro h i j
      by_cases hij : i = j
      · subst hij
        simpa [val_diagT] using h i
      · simp [val_diagT, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  obtain ⟨v, hv, e⟩ := GlobalTheory.SmGL.IwahoriOnto.exists_fixed_mk_eq hπ
    (GlobalTheory.CentralExponent.isOpen_cong γ hγ) (GlobalTheory.CentralExponent.isCompact_cong γ hγ) (diagT k (Fin N))
    (N := unipB k (Fin N)) (fun _ => leviEmb_mem_normalizer k (points (Fin N)) _)
    ((GlobalTheory.CentralExponent.cong (Fin N) γ hγ).comap (diagT k (Fin N)))
    (fun _ h => h) (GlobalTheory.SmGL.IwahoriOnto.lowerInt k (Fin N))
    (fun g hg => by
      obtain ⟨d, hd, x, hx, c, hc, e⟩ := UpperTheory.congruence_subgroup_eq_diagonal_unipotent_lower_iwahori k N γ hγ g hg
      exact ⟨d, (hmem d).2 hd, x, hx, c, hc, e⟩)
    (GlobalTheory.SmGL.IwahoriOnto.lowerInt_contract k (Fin N)) y
    (fun d => by
      have := hy d ((hmem d).1 d.2)
      rw [MonoidHom.one_apply, Units.val_one, one_smul]
      exact this)
  rw [hbot, Submodule.mem_bot] at hv
  exact hy0 (by rw [← e, hv, map_zero])
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FixedNeBotOfIsSubquotientOfIsCompact
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.fixed_ne_bot_of_isSubquotient_of_isCompact :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G V) (π : Representation ℂ G W) (H : Subgroup G), IsSmooth π → IsSubquotient σ π → IsCompact (H : Set G) →
    fixed σ H ≠ ⊥ → fixed π H ≠ ⊥ := by
  intro G _ _ _ V W _ _ _ _ σ π H hπ hsq hH hne
  obtain ⟨S, f, hf⟩ := hsq
  have hS : IsSmooth S.toRepresentation := fun v => by
    have : {g : G | S.toRepresentation g v = v} = {g : G | π g v = v} := by
      ext g; exact Subtype.ext_iff
    rw [this]; exact hπ v
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨u, rfl⟩ := hf x
  obtain ⟨v, hv, e⟩ := IwahoriOnto.exists_fixed_map_eq hS hH f.toLinearMap u fun h hh => by
    show f (S.toRepresentation h u) = f u
    rw [f.isIntertwining]
    simpa using hx ⟨h, hh⟩
  refine (Submodule.ne_bot_iff _).2 ⟨v.1, fun h => ?_, fun h0 => hx0 ?_⟩
  · exact congrArg Subtype.val (hv h)
  · have hv0 : v = 0 := Subtype.ext h0
    have e' : f.toLinearMap v = f u := e
    rw [← e', hv0, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsConstantTermLinearMapEquivariantUniversalE
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.exists_constantTerm_linearMap_equivariant_universalEnveloping :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ), ∃ f : automorphicForms K n →ₗ[ℂ] archSmooth K n, (∀ φ, (f φ).1 = constantTerm r φ.1) ∧ ∀ u φ, f (uActionAF K n u φ) = uAction u (f φ) := by
  intro K _ _ n r
  have h := fun φ : automorphicForms K n =>
    UpperTheory.constantTerm_archSmooth K n r ⟨φ.1, automorphicForms_le_archSmooth φ.2⟩ φ.2
  choose hs hX using h
  let f : automorphicForms K n →ₗ[ℂ] archSmooth K n :=
    { toFun := fun φ => ⟨constantTerm r φ.1, hs φ⟩
      map_add' := fun φ ψ => Subtype.ext (funext fun g =>
        constantTerm_add (IsAutomorphicForm.continuous φ.2) (IsAutomorphicForm.continuous ψ.2) g)
      map_smul' := fun c φ => Subtype.ext (funext fun g => constantTerm_smul c φ.1 g) }
  refine ⟨f, fun _ => rfl, fun u => ?_⟩
  induction u using UEnv.induction with
  | halg c =>
    intro φ
    have e : uActionAF K n (algebraMap ℝ (UEnv K n) c) φ = (c : ℂ) • φ :=
      Subtype.ext (coe_uAction_algebraMap c ⟨φ.1, automorphicForms_le_archSmooth φ.2⟩)
    rw [e, map_smul]
    exact Subtype.ext (coe_uAction_algebraMap c (f φ)).symm
  | hι X => exact fun φ => Subtype.ext (hX φ X).symm
  | hmul a b ha hb =>
    intro φ
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  | hadd a b ha hb =>
    intro φ
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), ha, hb]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ArchimedeanUnitaryLeISupEmbUAndCommute
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

section
open GlobalTheory.DefU Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem infinite_unitary_generated_by_embeddings (s : Finset (InfinitePlace E)) :
    ∀ g ∈ infU E n, (∀ w, w ∉ s → evGL w (cInf g) = 1) → g ∈ ⨆ τ : E →+* ℂ, embU n τ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g hg h
    have h2 : GeneralLinearGroup.map (pFin E) g.1 = 1 := hg
    have h1 : cInf g = 1 := gl_ext_evGL fun w => by
      rw [h w (Finset.notMem_empty w), map_one]
    have : g = 1 := by
      refine Subtype.ext (ga_ext ?_ ?_)
      · change cInf g = cInf 1
        rw [h1, map_one]
      · rw [h2]
        exact (map_one _).symm
    rw [this]
    exact one_mem _
  | insert v s hv ih =>
    intro g hg h
    have hr : (embRet v.embedding g : UA E n) ∈ embU n v.embedding := (embRet v.embedding g).2
    have hr' : (embRet v.embedding g : UA E n) ∈ ⨆ τ : E →+* ℂ, embU n τ :=
      (le_iSup (fun τ : E →+* ℂ => embU n τ) v.embedding) hr
    have hk : (embRet v.embedding g : UA E n)⁻¹ * g ∈ ⨆ τ : E →+* ℂ, embU n τ := by
      refine ih _ (mul_mem (inv_mem (embU_le_infU _ hr)) hg) fun w hw => ?_
      rw [map_mul, map_inv, cInf_embRet, map_mul, map_inv, InfinitePlace.mk_embedding]
      by_cases e : w = v
      · subst e
        rw [evGL_cutGL_self, inv_mul_cancel]
      · rw [evGL_cutGL_of_ne e, h w (by simp [e, hw]), inv_one, one_mul]
    simpa using mul_mem hr' hk

end

open GlobalTheory.DefU Matrix in
theorem UpperTheory.archimedeanUnitary_le_iSup_embU_and_commute :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), infU E n ≤ (⨆ τ : E →+* ℂ, embU n τ) ∧ ∀ τ τ' : E →+* ℂ, InfinitePlace.mk τ ≠ InfinitePlace.mk τ' → ∀ a ∈ embU (E := E) n τ, ∀ b ∈ embU n τ', a * b = b * a := by
  intro E _ _ _ n
  refine ⟨fun g hg => infinite_unitary_generated_by_embeddings Finset.univ g hg fun w hw => (hw (Finset.mem_univ w)).elim, ?_⟩
  intro τ τ' hne a ha b hb
  have h2 : GeneralLinearGroup.map (pFin E) b.1 = 1 := hb.1
  refine Subtype.ext (ga_ext ?_ ?_)
  · change cInf (a * b) = cInf (b * a)
    rw [map_mul, map_mul]
    refine gl_ext_evGL fun w => ?_
    rw [map_mul, map_mul]
    by_cases h : w = InfinitePlace.mk τ'
    · rw [evGL_cInf_of_mem ha (h ▸ hne.symm), one_mul, mul_one]
    · rw [evGL_cInf_of_mem hb h, one_mul, mul_one]
  · simp only [Subgroup.coe_mul, map_mul, h2, one_mul, mul_one]
end

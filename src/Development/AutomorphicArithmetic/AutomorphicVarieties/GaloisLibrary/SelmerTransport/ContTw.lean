module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelLeIne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResSmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelBaseEig
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantFunctions
theorem UpperTheory.Reformulated.B.LocallyConstantFunctions.locConst :
    ∀ {Γ A : Type} [inst : Group Γ] [inst_1 : TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [inst_3 : Group A] (ψ : Γ →* A), IsOpen (↑ψ.ker : Set Γ) → IsLocallyConstant (⇑ψ : Γ → A) := by
  intro Γ A _ _ _ _ ψ h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (↑ψ.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp [MonoidHom.mem_ker]
  · intro y hy
    have hk : ψ (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
    rw [map_mul, map_inv, inv_mul_eq_one] at hk
    exact hk.symm
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem cont_smul (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (Γ : Type) [Group Γ]
    [TopologicalSpace Γ] (χ : Γ →* ℤ_[l]ˣ) (hχ : Continuous fun g => ((χ g : ℤ_[l]ˣ) : ℤ_[l])) (m : QO l O) :
    Continuous fun g => ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • m := by
  refine (QO.isBaseChange l O).inductionOn m
    (motive := fun m => Continuous fun g => ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • m) ?_ ?_ ?_
  · intro x
    have h1 : Continuous fun g => ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • x :=
      Continuous.comp (LDataCardLeFinrank.contScal l Γ χ hχ) (Continuous.prodMk_left x)
    have h2 : Continuous (QO.incl l O) := continuous_of_discreteTopology
    refine (h2.comp h1).congr fun g => ?_
    exact map_smul (QO.incl l O) _ x
  · intro s x hx
    have h2 : Continuous fun y : QO l O => s • y := continuous_of_discreteTopology
    exact (h2.comp hx).congr fun g => smul_comm _ _ _
  · intro x y hx hy
    exact (hx.add hy).congr fun g => (smul_add _ _ _).symm

private theorem locConst {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantFunctions.locConst ψ h

theorem UpperTheory.V.Base.contTw :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime],
      Continuous (cycZ k Ω l) ∧ (∀ e : ℤ, ContAction (UpperTheory.V.LDataCardLeFinrank.qzG k Ω l e)) ∧
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] (ψ : G k Ω →* Oˣ) (n : ℤ), IsOpen (ψ.ker : Set (G k Ω)) →
        ContAction (twist₂ l (ψ * chiO (k := k) (Ω := Ω) l O ^ n)) := by
  intro k Ω _ _ _ _ _ l _
  have hc := ReciprocityTheory.Gal.continuous_cycZ k Ω l
  have hcPow (n : ℤ) : Continuous fun g : G k Ω => (((cycZ k Ω l ^ n) g : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp
      (show Continuous fun g : G k Ω => cycZ k Ω l g ^ n from hc.zpow n)
  refine ⟨hc, fun e => LDataCardLeFinrank.contScal l _ (cycZ k Ω l ^ (-e)) (hcPow (-e)),
    fun O _ _ ψ n hψ => ?_⟩
  refine continuous_prod_of_discrete_right.2 fun m => ?_
  have h1 := cont_smul l O _ (cycZ k Ω l ^ n) (hcPow n) m
  have h2 := ((locConst ψ hψ).prodMk ((IsLocallyConstant.iff_continuous _).2 h1)).comp
    fun p : Oˣ × QO l O => (p.1 : O) • p.2
  refine h2.continuous.congr fun g => ?_
  show (ψ g : O) • (((cycZ k Ω l g ^ n : ℤ_[l]ˣ) : ℤ_[l]) • m) =
    ((ψ g * chiO (k := k) (Ω := Ω) l O g ^ n : Oˣ) : O) • m
  have e : chiO (k := k) (Ω := Ω) l O g ^ n = Units.map (algebraMap ℤ_[l] O).toMonoidHom (cycZ k Ω l g ^ n) :=
    (map_zpow (Units.map (algebraMap ℤ_[l] O).toMonoidHom) (cycZ k Ω l g) n).symm
  rw [Units.val_mul, mul_smul, e]
  exact congrArg _ (algebraMap_smul O _ m).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoBase
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.qoBase :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (χ : G →* ℤ_[l]ˣ) (U : Subgroup G) (𝒟 : Set (Subgroup G)),
      Module.length O (LocSel (twist₂ l ((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp χ)) U 𝒟) = Module.length ℤ_[l] (LocSel (scalRep (QZ l) χ) U 𝒟) * eO l O ∧
      ∀ [U.Normal] (h𝒟 : ConjStable 𝒟) (g : G) (s : ℤ_[l]),
        Module.length O (Module.End.eigenspace (selRep (twist₂ l ((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp χ)) U h𝒟 g) (algebraMap ℤ_[l] O s)) =
          Module.length ℤ_[l] (Module.End.eigenspace (selRep (scalRep (QZ l) χ) U h𝒟 g) s) * eO l O := by
  intro l _ G _ _ _ O _ _ _ _ _ χ U 𝒟
  obtain ⟨-, hfree, hloc, -, he, -⟩ := dvrFacts l O
  have hj : ∀ g m, QO.incl l O (scalRep (QZ l) χ g m) =
      twist₂ l ((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp χ) g (QO.incl l O m) := fun g m => by
    show QO.incl l O (((χ g : ℤ_[l]ˣ) : ℤ_[l]) • m) = algebraMap ℤ_[l] O (χ g : ℤ_[l]ˣ) • QO.incl l O m
    rw [map_smul, algebraMap_smul]
  rw [he]
  exact ⟨selBase ℤ_[l] G (QZ l) (scalRep (QZ l) χ) O (QO l O) _ (QO.incl l O) (QO.isBaseChange l O) hj U 𝒟,
    fun h𝒟 g s => (selBaseEig ℤ_[l] G (QZ l) (scalRep (QZ l) χ) O (QO l O) _ (QO.incl l O)
      (QO.isBaseChange l O) hj U 𝒟 h𝒟).2 g s⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DecInf
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem exists_unit (l : ℕ) [hl : Fact l.Prime] : ∃ u : ℤ_[l]ˣ, ¬ IsOfFinOrder u := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl2 := hl.out.two_le
  have hnorm : ‖((1 + l : ℕ) : ℤ_[l])‖ = 1 := by
    push_cast
    rw [PadicInt.norm_add_eq_max_of_ne, norm_one, PadicInt.norm_p]
    · exact max_eq_left (inv_le_one_of_one_le₀ hl1.le)
    · rw [norm_one, PadicInt.norm_p]
      exact (inv_lt_one_of_one_lt₀ hl1).ne'
  obtain ⟨u, hu⟩ := PadicInt.isUnit_iff.2 hnorm
  refine ⟨u, fun h => ?_⟩
  rw [← Units.isOfFinOrder_val, hu, isOfFinOrder_iff_pow_eq_one] at h
  obtain ⟨n, hn, h⟩ := h
  rw [← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one] at h
  omega

theorem UpperTheory.V.Base.decInf :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G k Ω)), IsOpen (U : Set (G k Ω)) → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
      ∃ g ∈ U ⊓ Dec (F := k) A, ¬ IsOfFinOrder (cycZ k Ω l g) := by
  intro k Ω _ _ _ _ _ l _ U hU A hlt
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ k Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  obtain ⟨u, hu⟩ := exists_unit l
  obtain ⟨σ, hσ, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hlt u
  let K : IntermediateField ℚ Ω := (IsScalarTower.toAlgHom ℚ k Ω).fieldRange
  have : FiniteDimensional ℚ K :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ k Ω)).toLinearEquiv.finiteDimensional
  have : Finite ((Ω ≃ₐ[ℚ] Ω) ⧸ K.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ K.fixingSubgroup_isOpen
  have : K.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨n, hn, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := K.fixingSubgroup)) σ
  let g : G k Ω := { (σ ^ n).toRingEquiv with
    commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _ ⟨x, rfl⟩ }
  have hg : g ∈ Dec (F := k) A := (Dec (F := ℚ) A).pow_mem (Ine_le_Dec A hσ) n
  have hgu : cycZ k Ω l g = u ^ n := by
    change cycZ ℚ Ω l (σ ^ n) = u ^ n
    rw [map_pow, hσu]
  haveI : Finite (G k Ω ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI := Subgroup.finiteIndex_normalCore U
  haveI := Subgroup.normalCore_normal U
  have hN : U.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hgU : g ^ U.normalCore.index ∈ U := U.normalCore_le (Subgroup.pow_index_mem _ g)
  refine ⟨g ^ U.normalCore.index, ⟨hgU, Subgroup.pow_mem (Dec (F := k) A) hg _⟩, ?_⟩
  rw [map_pow, hgu, ← pow_mul, isOfFinOrder_pow]
  rintro (h | h)
  · exact hu h
  · exact mul_ne_zero hn.ne' hN h
end

module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedGaloisHomsBoundedClassNumberOfArtinRec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerLawUpperTriangularUnipotentAdelic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedHomsBoundedByClassNumberOfArtin
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedHomsBoundedByClassNumberOfArtin
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.UnramifiedHomBound

noncomputable def homToH1 {O G M : Type} [CommRing O] [Group G] [AddCommGroup M] [Module O M]
    (U : Submodule O (G → M)) (hU : ∀ c ∈ U, ∀ g h, c (g * h) = c g + c h) :
    U →ₗ[O] NG.H1z (Representation.trivial O G M) :=
  (Submodule.mkQ _).comp (Submodule.inclusion
    (show U ≤ NG.coZ1s (Representation.trivial O G M) from fun c hc g h => by simpa using hU c hc g h))

theorem homToH1_injective {O G M : Type} [CommRing O] [Group G] [AddCommGroup M] [Module O M]
    (U : Submodule O (G → M)) (hU : ∀ c ∈ U, ∀ g h, c (g * h) = c g + c h) :
    Function.Injective (homToH1 U hU) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨v, hv⟩ := (Submodule.Quotient.mk_eq_zero _).1 hc
  apply Subtype.ext
  funext g
  have h := congrFun hv g
  have h2 : NG.coD0 (Representation.trivial O G M) v g = 0 := by simp [NG.coD0]
  exact h.symm.trans h2

theorem homToH1_mem_unrH1 {O G M : Type} [CommRing O] [Group G] [AddCommGroup M] [Module O M]
    (U : Submodule O (G → M)) (hU : ∀ c ∈ U, ∀ g h, c (g * h) = c g + c h) (I : Subgroup G)
    (c : U) (hc : ∀ g ∈ I, (c : G → M) g = 0) :
    homToH1 U hU c ∈ RepresentationBoundsCohomology.BR.unrH1 (Representation.trivial O G M) I := by
  change NG.resH1 (Representation.trivial O G M) I (Submodule.Quotient.mk _) = 0
  rw [NG.resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
  have h : NG.restrictCocycles1 (Representation.trivial O G M) I (Submodule.inclusion
      (show U ≤ NG.coZ1s (Representation.trivial O G M) from fun c hc g h => by simpa using hU c hc g h) c)
      = 0 := Subtype.ext (funext fun g => hc g g.2)
  rw [h]
  exact Submodule.zero_mem _

theorem l_ne_zero (D : D7) (i : D.nd.Loc) : ((D.nd.l i : ℕ) : D.nd.O i) ≠ 0 := by
  have : CharZero (FractionRing (D.nd.O i)) :=
    charZero_of_injective_ringHom (D.nd.embK i).injective
  intro h
  have h2 := congrArg (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) h
  rw [map_natCast, map_zero] at h2
  exact (Fact.out : (D.nd.l i).Prime).ne_zero (Nat.cast_eq_zero.1 h2)

theorem length_unrHom_le (h : ReciprocityTheory.ChartRestriction.T2.VhE) (D : D7) (i : D.nd.Loc) :
    Module.length (D.nd.O i) ↥(TruncatedSeriesCountingIdentities.unrHom i) ≤
      Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {((D.nd.l i : ℕ) : D.nd.O i)}) *
        (padicValNat (D.nd.l i) (classNumber D.host.E) : ℕ∞) := by
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  have hU : ∀ c ∈ TruncatedSeriesCountingIdentities.unrHom i, ∀ g h, c (g * h) = c g + c h := fun c hc => hc.2.1
  rw [(LinearEquiv.ofInjective _ (homToH1_injective _ hU)).length_eq]
  refine h D.host.E D.nd.Om D.nd.plOm.1 D.nd.plOm.2 (D.nd.l i) (D.nd.O i)
    (Or.inr (IsTotallyComplex.nrRealPlaces_eq_zero _)) (KmodO (D.nd.O i))
    ⟨Submodule.quotEquivOfEq _ _ (Submodule.one_eq_range).symm⟩ _ (fun _ _ => rfl) _ ?_ ?_
  · rintro _ ⟨c, rfl⟩
    exact ⟨_, rfl, c.2.1⟩
  · rintro v _ ⟨c, rfl⟩
    exact homToH1_mem_unrH1 _ hU _ c (c.2.2.2 v)

theorem unramified_homs_bounded_by_class_number_of_artin :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.UnramifiedClassFieldBound i := by
  intro hA D i
  have h := length_unrHom_le (GlobalTheory.T.unramifiedGaloisHoms_bounded_classNumber_of_artinReciprocity hA) D i
  have hfin : Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {((D.nd.l i : ℕ) : D.nd.O i)}) ≠ ⊤ :=
    Module.length_ne_top_iff.2
      (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero (l_ne_zero D i)))
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.1 hfin
  have hlt : Module.length (D.nd.O i) ↥(TruncatedSeriesCountingIdentities.unrHom i) < ⊤ := by
    refine lt_of_le_of_lt h ?_
    rw [← he, ← Nat.cast_mul]
    exact ENat.natCast_lt_top _
  refine ⟨hlt, ?_⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hlt.ne
  rw [← he, ← hn, ← Nat.cast_mul, Nat.cast_le] at h
  unfold lenUnit
  rw [← he, ← hn, ENat.toNat_natCast, ENat.toNat_natCast]
  refine div_le_of_le_mul₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _) ?_
  rw [mul_comm]
  exact_mod_cast h

end GlobalTheory.UnramifiedHomBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedHomsBoundedByClassNumberOfArtinStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedClassFieldBound_of_artin : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.UnramifiedClassFieldBound i := by
  first | exact @GlobalTheory.UnramifiedHomBound.unramified_homs_bounded_by_class_number_of_artin | exact GlobalTheory.UnramifiedHomBound.unramified_homs_bounded_by_class_number_of_artin | (intros; apply GlobalTheory.UnramifiedHomBound.unramified_homs_bounded_by_class_number_of_artin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageProdFubini
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageProdFubini
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

section Prod

variable {G₁ : Type} [AddCommGroup G₁] [TopologicalSpace G₁] [IsTopologicalAddGroup G₁]
  {G₂ : Type} [AddCommGroup G₂] [TopologicalSpace G₂] [IsTopologicalAddGroup G₂]

theorem isCoLat_prod {Γ₁ : AddSubgroup G₁} {Γ₂ : AddSubgroup G₂} (h₁ : IsCoLat Γ₁) (h₂ : IsCoLat Γ₂) :
    IsCoLat (Γ₁.prod Γ₂) := by
  obtain ⟨d₁, K₁, hK₁, c₁⟩ := h₁
  obtain ⟨d₂, K₂, hK₂, c₂⟩ := h₂
  refine ⟨?_, K₁ ×ˢ K₂, hK₁.prod hK₂, fun z => ?_⟩
  · refine DiscreteTopology.of_continuous_injective
      (f := fun z : Γ₁.prod Γ₂ => ((⟨z.1.1, (AddSubgroup.mem_prod.1 z.2).1⟩ : Γ₁),
        (⟨z.1.2, (AddSubgroup.mem_prod.1 z.2).2⟩ : Γ₂))) ?_ ?_
    · exact ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    · intro a b h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact Subtype.ext (Prod.ext h.1 h.2)
  · obtain ⟨γ₁, hγ₁, e₁⟩ := c₁ z.1
    obtain ⟨γ₂, hγ₂, e₂⟩ := c₂ z.2
    exact ⟨(γ₁, γ₂), AddSubgroup.mem_prod.2 ⟨hγ₁, hγ₂⟩, ⟨e₁, e₂⟩⟩

end Prod

section FD

open Pointwise

variable {G₁ : Type} [AddCommGroup G₁] [MeasurableSpace G₁]
  {G₂ : Type} [AddCommGroup G₂] [MeasurableSpace G₂]

theorem vadd_prod_set {Γ₁ : AddSubgroup G₁} {Γ₂ : AddSubgroup G₂} (g : Γ₁.prod Γ₂) (A : Set G₁) (B : Set G₂) :
    g +ᵥ (A ×ˢ B) = ((g : G₁ × G₂).1 +ᵥ A) ×ˢ ((g : G₁ × G₂).2 +ᵥ B) := by
  ext ⟨x, y⟩
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_prod]
  rfl

theorem isAddFundamentalDomain_prod {Γ₁ : AddSubgroup G₁} {Γ₂ : AddSubgroup G₂} {μ₁ : Measure G₁} {μ₂ : Measure G₂}
    [SFinite μ₁] [SFinite μ₂] {𝓕₁ : Set G₁} {𝓕₂ : Set G₂}
    (h₁ : IsAddFundamentalDomain Γ₁ 𝓕₁ μ₁) (h₂ : IsAddFundamentalDomain Γ₂ 𝓕₂ μ₂) :
    IsAddFundamentalDomain (Γ₁.prod Γ₂) (𝓕₁ ×ˢ 𝓕₂) (μ₁.prod μ₂) := by
  refine ⟨h₁.nullMeasurableSet.prod h₂.nullMeasurableSet, ?_, ?_⟩
  · have a₁ : ∀ᵐ z ∂μ₁.prod μ₂, ∃ γ : Γ₁, γ +ᵥ z.1 ∈ 𝓕₁ := Measure.quasiMeasurePreserving_fst.ae h₁.ae_covers
    have a₂ : ∀ᵐ z ∂μ₁.prod μ₂, ∃ γ : Γ₂, γ +ᵥ z.2 ∈ 𝓕₂ := Measure.quasiMeasurePreserving_snd.ae h₂.ae_covers
    filter_upwards [a₁, a₂] with z ⟨γ₁, e₁⟩ ⟨γ₂, e₂⟩
    exact ⟨⟨((γ₁ : G₁), (γ₂ : G₂)), AddSubgroup.mem_prod.2 ⟨γ₁.2, γ₂.2⟩⟩, ⟨e₁, e₂⟩⟩
  · intro g g' hne
    change μ₁.prod μ₂ ((g +ᵥ (𝓕₁ ×ˢ 𝓕₂)) ∩ (g' +ᵥ (𝓕₁ ×ˢ 𝓕₂))) = 0
    rw [vadd_prod_set, vadd_prod_set, Set.prod_inter_prod, Measure.prod_prod]
    by_cases e : (g : G₁ × G₂).1 = (g' : G₁ × G₂).1
    · have e2 : (g : G₁ × G₂).2 ≠ (g' : G₁ × G₂).2 := fun e2 => hne (Subtype.ext (Prod.ext e e2))
      have := h₂.aedisjoint (i := ⟨(g : G₁ × G₂).2, (AddSubgroup.mem_prod.1 g.2).2⟩)
        (j := ⟨(g' : G₁ × G₂).2, (AddSubgroup.mem_prod.1 g'.2).2⟩) (fun h => e2 (congrArg Subtype.val h))
      rw [show μ₂ (((g : G₁ × G₂).2 +ᵥ 𝓕₂) ∩ ((g' : G₁ × G₂).2 +ᵥ 𝓕₂)) = 0 from this, mul_zero]
    · have := h₁.aedisjoint (i := ⟨(g : G₁ × G₂).1, (AddSubgroup.mem_prod.1 g.2).1⟩)
        (j := ⟨(g' : G₁ × G₂).1, (AddSubgroup.mem_prod.1 g'.2).1⟩) (fun h => e (congrArg Subtype.val h))
      rw [show μ₁ (((g : G₁ × G₂).1 +ᵥ 𝓕₁) ∩ ((g' : G₁ × G₂).1 +ᵥ 𝓕₁)) = 0 from this, zero_mul]

end FD

section Main

theorem avg_prod (G₁ : Type) [AddCommGroup G₁] [TopologicalSpace G₁] [IsTopologicalAddGroup G₁]
    [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁]
    (G₂ : Type) [AddCommGroup G₂] [TopologicalSpace G₂] [IsTopologicalAddGroup G₂]
    [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂]
    (Γ₁ : AddSubgroup G₁) (Γ₂ : AddSubgroup G₂) (h₁ : IsCoLat Γ₁) (h₂ : IsCoLat Γ₂)
    (Φ : G₁ × G₂ → ℂ) (hΦ : Per (Γ₁.prod Γ₂) Φ) :
    avg (Γ₁.prod Γ₂) Φ = avg Γ₁ (fun x => avg Γ₂ (fun y => Φ (x, y))) := by
  letI m₁ : MeasurableSpace G₁ := borel G₁
  haveI : BorelSpace G₁ := ⟨rfl⟩
  letI m₂ : MeasurableSpace G₂ := borel G₂
  haveI : BorelSpace G₂ := ⟨rfl⟩
  have e₁ : ∃ p : Measure G₁ × Set G₁, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ₁ p.2 p.1 ∧ p.1 p.2 = 1 := by
    obtain ⟨μ, F, a, b, c⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G₁ Γ₁ h₁
    exact ⟨(μ, F), a, b, c⟩
  have e₂ : ∃ p : Measure G₂ × Set G₂, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ₂ p.2 p.1 ∧ p.1 p.2 = 1 := by
    obtain ⟨μ, F, a, b, c⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G₂ Γ₂ h₂
    exact ⟨(μ, F), a, b, c⟩
  have A₁ : ∀ Ψ : G₁ → ℂ, avg Γ₁ Ψ = ∫ x in e₁.choose.2, Ψ x ∂e₁.choose.1 := fun Ψ => dif_pos e₁
  have A₂ : ∀ Ψ : G₂ → ℂ, avg Γ₂ Ψ = ∫ y in e₂.choose.2, Ψ y ∂e₂.choose.1 := fun Ψ => dif_pos e₂
  obtain ⟨H₁, F₁, M₁⟩ := e₁.choose_spec
  obtain ⟨H₂, F₂, M₂⟩ := e₂.choose_spec
  set μ₁ := e₁.choose.1
  set 𝓕₁ := e₁.choose.2
  set μ₂ := e₂.choose.1
  set 𝓕₂ := e₂.choose.2
  have hFD : IsAddFundamentalDomain (Γ₁.prod Γ₂) (𝓕₁ ×ˢ 𝓕₂) (μ₁.prod μ₂) := isAddFundamentalDomain_prod F₁ F₂
  have hM : μ₁.prod μ₂ (𝓕₁ ×ˢ 𝓕₂) = 1 := by rw [Measure.prod_prod, M₁, M₂, one_mul]
  obtain ⟨-, -, hI, hE⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average (G₁ × G₂) (Γ₁.prod Γ₂) (isCoLat_prod h₁ h₂) (μ₁.prod μ₂) (𝓕₁ ×ˢ 𝓕₂)
    inferInstance hFD Φ hΦ
  rw [hM, ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hE
  rw [← hE, setIntegral_prod _ hI, A₁]
  simp only [A₂]

end Main

end GlobalTheory.CuspGeneric
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageProdFubiniStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientAverage_prod_fubini : ∀ (G₁ : Type) [AddCommGroup G₁] [TopologicalSpace G₁] [IsTopologicalAddGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] (G₂ : Type) [AddCommGroup G₂] [TopologicalSpace G₂] [IsTopologicalAddGroup G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂] (Γ₁ : AddSubgroup G₁) (Γ₂ : AddSubgroup G₂), IsCoLat Γ₁ → IsCoLat Γ₂ → ∀ Φ : G₁ × G₂ → ℂ, Per (Γ₁.prod Γ₂) Φ → avg (Γ₁.prod Γ₂) Φ = avg Γ₁ (fun x => avg Γ₂ (fun y => Φ (x, y))) := by
  first | exact @GlobalTheory.CuspGeneric.avg_prod | exact GlobalTheory.CuspGeneric.avg_prod | (intros; apply GlobalTheory.CuspGeneric.avg_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimensionSaturationUnramified
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N TensorProduct Module

noncomputable section
namespace GlobalTheory.FiltrationJumpMultiplicity

section Gen
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem fil_anti {a b : ℤ} (h : a ≤ b) : PD.Fil b ≤ PD.Fil a :=
  antitone_int_of_succ_le PD.Fil_anti h

theorem filV_anti {a b : ℤ} (h : a ≤ b) :
    FilV PD (LL := LL) (V := V) b ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v c =>
    refine ⟨v ⊗ₜ ⟨(c : BdR), fil_anti PD h c.2⟩, ?_⟩
    simp
  | add y z hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz

theorem exists_mem_filV (x : V ⊗[Qp] BdR) : ∃ a, x ∈ FilV PD (LL := LL) (V := V) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v c =>
    obtain ⟨a, ha⟩ := PD.Fil_exh c
    exact ⟨a, v ⊗ₜ ⟨c, ha⟩, by simp⟩
  | add y z hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨min a b, Submodule.add_mem _ (filV_anti PD (min_le_left a b) ha)
      (filV_anti PD (min_le_right a b) hb)⟩

theorem exists_DdRE_le_filV (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL)
    [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    ∃ a, DdRE PD ρ τ ≤ FilV PD (LL := LL) (V := V) a := by
  have key : ∀ s : Finset (V ⊗[Qp] BdR), ∃ a, ∀ x ∈ s, x ∈ FilV PD (LL := LL) (V := V) a := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert y s _ ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨b, hb⟩ := exists_mem_filV PD (LL := LL) y
      refine ⟨min a b, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact filV_anti PD (min_le_right a b) hb
      · exact filV_anti PD (min_le_left a b) (ha x hx)
  obtain ⟨s, hs⟩ : (DdRE PD ρ τ).FG := Module.Finite.iff_fg.mp inferInstance
  obtain ⟨a, ha⟩ := key s
  exact ⟨a, hs ▸ Submodule.span_le.mpr ha⟩

theorem finsum_multV_neg (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL)
    [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    ∑ᶠ (a : ℤ) (_ : a < 0), multV PD ρ τ a =
      (finrank LL ↥(DdRE PD ρ τ) : ℤ) - finrank LL ↥(FildR PD ρ τ 0) := by
  obtain ⟨a₀, ha₀⟩ := exists_DdRE_le_filV PD ρ τ
  have hF : ∀ b ≤ a₀, FildR PD ρ τ b = DdRE PD ρ τ := fun b hb =>
    inf_eq_left.mpr (ha₀.trans (filV_anti PD hb))
  set N : ℕ := (-a₀).toNat with hN
  have hNa : -(N : ℤ) ≤ a₀ := by have := Int.self_le_toNat (-a₀); omega
  set f : ℤ → ℤ := fun a => (finrank LL ↥(FildR PD ρ τ a) : ℤ) with hf
  have hg : ∀ a, multV PD ρ τ a = f a - f (a + 1) := fun a => rfl
  have hzero : ∀ a, a < -(N : ℤ) → multV PD ρ τ a = 0 := by
    intro a ha
    have h1 := hF a (by omega)
    have h2 := hF (a + 1) (by omega)
    rw [multV, h1, h2, sub_self]
  let e : ℕ ↪ ℤ := ⟨fun i => -((i : ℤ) + 1), fun i j h => by
    have : -((i : ℤ) + 1) = -((j : ℤ) + 1) := h
    omega⟩
  have he : ∀ i, e i = -((i : ℤ) + 1) := fun _ => rfl
  have hsum : ∑ᶠ (a : ℤ) (_ : a < 0), multV PD ρ τ a =
      ∑ a ∈ (Finset.range N).map e, multV PD ρ τ a := by
    apply finsum_mem_eq_sum_of_inter_support_eq (s := Set.Iio (0 : ℤ))
    ext a
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.coe_map, Finset.coe_range,
      Set.mem_image, Set.mem_Iio, Function.mem_support, he]
    constructor
    · rintro ⟨ha, hs⟩
      refine ⟨⟨(-a - 1).toNat, ?_, ?_⟩, hs⟩
      · by_contra h; exact hs (hzero a (by omega))
      · omega
    · rintro ⟨⟨i, hi, rfl⟩, hs⟩
      exact ⟨by omega, hs⟩
  rw [hsum, Finset.sum_map]
  have hT := Finset.sum_range_sub (fun i : ℕ => f (-(i : ℤ))) N
  have h2 : ∀ i ∈ Finset.range N, multV PD ρ τ (e i) = f (-((i + 1 : ℕ) : ℤ)) - f (-(i : ℤ)) := by
    intro i _
    rw [hg, he]
    congr 2 <;> push_cast <;> ring
  rw [Finset.sum_congr rfl h2, hT]
  simp only [Nat.cast_zero, neg_zero, hf]
  rw [hF (-(N : ℤ)) hNa]

end Gen
end GlobalTheory.FiltrationJumpMultiplicity

noncomputable section
namespace GlobalTheory.FiltrationJumpMultiplicity

section Sat
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem coboundary_mem_blochKatoCocycles (ρ : Representation LL G V) (hc : ∀ x, Continuous fun g => ρ g x) (x : V) :
    cob ρ x ∈ finiteCocycles PD ρ := by
  have hcob : ∀ g, cob ρ x g = ρ g x - x := fun g => rfl
  refine ⟨⟨?_, fun g h => ?_⟩, x ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  · have : (cob ρ x : G → V) = fun g => ρ g x + (-x) := funext fun g => by rw [hcob, sub_eq_add_neg]
    rw [this]
    exact (hc x).add continuous_const
  · simp only [hcob, map_mul, Module.End.mul_apply, map_sub]
    abel
  · rw [hcob, sub_tmul]
    simp [actVB]

theorem mem_H1fT_of_smul (ρ : Representation LL G V) (L : Lattice (O := O) ρ)
    (hc : ∀ x, Continuous fun g => ρ g x) (κ : LatticeCohomology L) (a : O) (ha : algebraMap O LL a ≠ 0)
    (h : a • κ ∈ latticeFiniteCohomology PD L) : κ ∈ latticeFiniteCohomology PD L := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
  obtain ⟨c', hc', hq⟩ := h
  rw [← Submodule.Quotient.mk_smul] at hq
  have hq' := (Submodule.Quotient.eq _).mp hq
  obtain ⟨x, -, hx⟩ := hq'
  have hx' : (c' : G → V) - a • (c : G → V) = cob ρ x := by
    have h3 : ((latticeCocycles L).subtype (c' - a • c) : G → V) = (c' : G → V) - a • (c : G → V) := by simp
    rw [← h3, ← hx]; rfl
  have h1 : a • (c : G → V) ∈ finiteCocycles PD ρ := by
    have : a • (c : G → V) = (c' : G → V) - cob ρ x := by rw [← hx']; abel
    rw [this]
    exact (finiteCocycles PD ρ).sub_mem hc'.2 (coboundary_mem_blochKatoCocycles PD ρ hc x)
  have h2 : (c : G → V) ∈ finiteCocycles PD ρ := by
    have e : a • (c : G → V) = algebraMap O LL a • (c : G → V) := (algebraMap_smul LL a _).symm
    rw [e] at h1
    have := (finiteCocycles PD ρ).smul_mem (algebraMap O LL a)⁻¹ h1
    rwa [inv_smul_smul₀ ha] at this
  exact ⟨c, ⟨c.2, h2⟩, rfl⟩

end Sat

theorem blochKato_dimension_saturation_unramified : ∀ D : D7, Formalism.MainNotions.tableLineDegreeTwo.adm19 D := by
  intro D l _ K LL hA
  haveI := K.2
  haveI := LL.2
  refine ⟨?_, ?_, ?_⟩
  · intro V _ _ _ _ _ _ _ _ _ ρ hc hcrys
    letI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
    have hBK := GlobalTheory.BlochKatoTied.blochKatoDim_of_tied l (D.loc l) (D.locA l) (D.locT l) K LL
      (GlobalTheory.H1fGeneratorBoundAlt.splits_of_good hA.2.2) V ρ hc hcrys
    rw [hBK, finsum_eq_sum_of_fintype]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    haveI := ((GlobalTheory.Per.Components.components_finrank l (D.loc l) (D.locA l) (D.locT l) K LL V ρ).1 τ).1
    exact (finsum_multV_neg _ ρ τ).symm
  · intro V _ _ _ _ _ _ _ _ _ _ _ ρ L hc _ κ a ha h
    refine mem_H1fT_of_smul _ ρ L hc κ a ?_ h
    intro h0
    exact ha (Subtype.ext h0)
  · exact GlobalTheory.T.unramified_trivial_local l (D.loc l) (D.locA l) (D.locT l) K LL

end GlobalTheory.FiltrationJumpMultiplicity
end
end
end

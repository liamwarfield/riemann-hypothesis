module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilPairingEqCmIntegerOfPureTypeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesOverSplitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PstAndWdAtOfIsRegAlg
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGramMatricesCmUnitaryShimuraObject
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexFibreLinearHomsPrincipalCMTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexFibreLinearHomsPrincipalCMTriple
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

noncomputable section

namespace GlobalTheory.GramBaseChange

theorem exists_complex_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (p q : ℕ), ρ ^ 2 = -(H.d : 𝓞 K) → HasType H A.t.act ρ p q → ∀ (f₁ f₂ : A.t.G ⟶ B.t.G), Serre.IsLinearHom A.t.act B.t.act f₁ → Serre.IsLinearHom A.t.act B.t.act f₂ → ∃ (A' B' : PAT H (Sp ℂ)) (f₁' f₂' : A'.t.G ⟶ B'.t.G) (p' q' : ℕ), p' + q' = p + q ∧ (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult A'.t.act (𝟙 (Sp ℂ)) τ p') ∧ (τ H.rt ≠ H.rt0 → LieMult A'.t.act (𝟙 (Sp ℂ)) τ q')) ∧ Serre.IsLinearHom A'.t.act B'.t.act f₁' ∧ Serre.IsLinearHom A'.t.act B'.t.act f₂' ∧ ∀ g : 𝓞 E, WeilEq B'.t.PP.L f₁' f₂' A'.t.PP.L (A'.t.act.act g) (𝟙 _) (𝟙 (Sp ℂ)) → WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ ρ σ₁ A B p q hρ hA f₁ f₂ hf₁ hf₂
  have hβi : Function.Injective (σ₁.comp (algebraMap (𝓞 K) K)) :=
    σ₁.injective.comp (IsFractionRing.injective (𝓞 K) K)
  obtain ⟨⟨A', mA, -⟩, hA2⟩ := GlobalTheory.LamT.pat_pullback E H (𝓞 K) ℂ (σ₁.comp (algebraMap (𝓞 K) K)) A
  obtain ⟨⟨B', mB, -⟩, hB2⟩ := GlobalTheory.LamT.pat_pullback E H (𝓞 K) ℂ (σ₁.comp (algebraMap (𝓞 K) K)) B
  obtain ⟨-, -, wA, hwA⟩ := hA2 A' mA inferInstance
  obtain ⟨-, -, wB, hwB⟩ := hB2 B' mB inferInstance
  haveI := hf₁.isMonHom
  haveI := hf₂.isMonHom
  obtain ⟨f₁', hm₁, e₁⟩ := GlobalTheory.PairingFibre.exists_hom mA.cart mB.cart f₁
  obtain ⟨f₂', hm₂, e₂⟩ := GlobalTheory.PairingFibre.exists_hom mA.cart mB.cart f₂
  have lin : ∀ (f : A.t.G ⟶ B.t.G) (f' : A'.t.G ⟶ B'.t.G), Serre.IsLinearHom A.t.act B.t.act f → IsMonHom f' →
      f'.left ≫ mB.φ = mA.φ ≫ f.left → Serre.IsLinearHom A'.t.act B'.t.act f' := by
    intro f f' hf hm e
    refine ⟨hm, fun c => ?_⟩
    apply Over.OverMorphism.ext
    apply mB.cart.1.hom_ext
    · have hc := congrArg CommaMorphism.left (hf.comm c)
      simp only [Over.comp_left] at hc ⊢
      rw [Category.assoc, e, ← Category.assoc, mA.act c, Category.assoc, hc, Category.assoc, mB.act c,
        ← Category.assoc, ← Category.assoc, e]
    · simp only [Over.comp_left, Category.assoc, Over.w]
  have hlie : ∀ (τ : 𝓞 E →+* ℂ) (n : ℕ), LieMult A'.t.act (𝟙 (Sp ℂ)) τ n ↔
      LieMult A.t.act (spMap (σ₁.comp (algebraMap (𝓞 K) K))) τ n := fun τ n => by
    have := GlobalTheory.lieMult_iff_of_isGrpPullback mA.cart A'.t.act A.t.act mA.act (𝟙 (Sp ℂ)) τ n
    rwa [Category.id_comp] at this
  have hweil : ∀ g : 𝓞 E, WeilEq B'.t.PP.L f₁' f₂' A'.t.PP.L (A'.t.act.act g) (𝟙 _) (𝟙 (Sp ℂ)) →
      WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
    intro g h
    have := (GlobalTheory.PairingFibre.weilEq_iff (g₂ := 𝟙 _) mA.cart mA.cart mB.cart mA.cart B.t.PP.isLB A.t.PP.isLB B'.t.PP.isLB
      A'.t.PP.isLB ⟨wB, hwB.1⟩ ⟨wA, hwA.1⟩ e₁ e₂ (mA.act g) (by simp) (𝟙 (Sp ℂ))).1 h
    rwa [Category.id_comp] at this
  have hT := hA ℂ (σ₁.comp (algebraMap (𝓞 K) K)) hβi
  have hd0 : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have hr0 : H.rt0 ≠ 0 := fun h0 => hd0 (by have := H.sqrt_neg_disc_sq; rw [h0] at this; linear_combination this)
  have hsq : ∀ x : ℂ, x ^ 2 = -(H.d : ℂ) → x = H.rt0 ∨ x = -H.rt0 := fun x hx =>
    sq_eq_sq_iff_eq_or_eq_neg.1 (hx.trans H.sqrt_neg_disc_sq.symm)
  have hβρ : (σ₁.comp (algebraMap (𝓞 K) K)) ρ ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, hρ]; simp
  have hτ : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ^ 2 = -(H.d : ℂ) := fun τ => by
    rw [← map_pow, H.rt_sq]; simp
  have hne : H.rt0 ≠ -H.rt0 := fun h => hr0 (by linear_combination h / 2)
  rcases hsq _ hβρ with hc | hc
  · refine ⟨A', B', f₁', f₂', p, q, rfl, fun τ => ⟨fun ht => ?_, fun ht => ?_⟩,
      lin f₁ f₁' hf₁ hm₁ e₁, lin f₂ f₂' hf₂ hm₂ e₂, hweil⟩
    · exact (hlie τ p).2 ((hT τ).1 (ht.trans hc.symm))
    · exact (hlie τ q).2 ((hT τ).2 (fun h => ht (h.trans hc)))
  · refine ⟨A', B', f₁', f₂', q, p, add_comm _ _, fun τ => ⟨fun ht => ?_, fun ht => ?_⟩,
      lin f₁ f₁' hf₁ hm₁ e₁, lin f₂ f₂' hf₂ hm₂ e₂, hweil⟩
    · exact (hlie τ q).2 ((hT τ).2 (fun h => hne (ht.symm.trans (h.trans hc))))
    · rcases hsq _ (hτ τ) with h | h
      · exact absurd h ht
      · exact (hlie τ p).2 ((hT τ).1 (h.trans hc.symm))

end GlobalTheory.GramBaseChange

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexFibreLinearHomsPrincipalCMTripleStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complex_fibre_linear_homs_principalCMTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (p q : ℕ), ρ ^ 2 = -(H.d : 𝓞 K) → HasType H A.t.act ρ p q → ∀ (f₁ f₂ : A.t.G ⟶ B.t.G), Serre.IsLinearHom A.t.act B.t.act f₁ → Serre.IsLinearHom A.t.act B.t.act f₂ → ∃ (A' B' : PAT H (Sp ℂ)) (f₁' f₂' : A'.t.G ⟶ B'.t.G) (p' q' : ℕ), p' + q' = p + q ∧ (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult A'.t.act (𝟙 (Sp ℂ)) τ p') ∧ (τ H.rt ≠ H.rt0 → LieMult A'.t.act (𝟙 (Sp ℂ)) τ q')) ∧ Serre.IsLinearHom A'.t.act B'.t.act f₁' ∧ Serre.IsLinearHom A'.t.act B'.t.act f₂' ∧ ∀ g : 𝓞 E, WeilEq B'.t.PP.L f₁' f₂' A'.t.PP.L (A'.t.act.act g) (𝟙 _) (𝟙 (Sp ℂ)) → WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  first | exact @GlobalTheory.GramBaseChange.exists_complex_fibre | exact GlobalTheory.GramBaseChange.exists_complex_fibre | (intros; apply GlobalTheory.GramBaseChange.exists_complex_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGramMatricesCmUnitaryShimuraObject
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

namespace GlobalTheory.FlatCM.GramExists

theorem exists_weilEq_entry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (p q : ℕ), ρ ^ 2 = -(H.d : 𝓞 K) → p + q = 1 →
    HasType H A.t.act ρ p q → ∀ (f₁ f₂ : A.t.G ⟶ B.t.G), Serre.IsLinearHom A.t.act B.t.act f₁ →
    Serre.IsLinearHom A.t.act B.t.act f₂ → ∃ g : 𝓞 E, WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ ρ σ₁ A B p q hρ hpq hA f₁ f₂ h₁ h₂
  obtain ⟨A', B', f₁', f₂', p', q', hpq', hdet, h₁', h₂', hW⟩ := GlobalTheory.T.exists_complex_fibre_linear_homs_principalCMTriple E H K ρ σ₁ A B p q hρ hA f₁ f₂ h₁ h₂
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_weil_pairing_eq_cm_integer_of_pure_type E H A' B' p' q' (hpq'.trans hpq) hdet f₁' f₂' h₁' h₂'
  exact ⟨g, hW g hg⟩

theorem exists_isGram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q), ∃ gP gQ, IsGram X gP gQ := by
  intro E _ _ _ H K _ _ ρ σ₁ p q X
  have hP : ∀ a b : Fin p, ∃ g : 𝓞 E, WeilEq X.B.t.PP.L (phiP X a) (phiP X b) (X.A true).t.PP.L
      ((X.A true).t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := fun a b =>
    exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP _ _ (X.lin (Sum.inl a)) (X.lin (Sum.inl b))
  have hQ : ∀ a b : Fin q, ∃ g : 𝓞 E, WeilEq X.B.t.PP.L (phiQ X a) (phiQ X b) (X.A false).t.PP.L
      ((X.A false).t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := fun a b =>
    exists_weilEq_entry E H K ρ σ₁ (X.A false) X.B 0 1 X.ρ_sq rfl X.typeM _ _ (X.lin (Sum.inr a)) (X.lin (Sum.inr b))
  choose gP hgP using hP
  choose gQ hgQ using hQ
  exact ⟨Matrix.of gP, Matrix.of gQ, fun a b => hgP a b, fun a b => hgQ a b⟩

end GlobalTheory.FlatCM.GramExists

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGramMatricesCmUnitaryShimuraObjectStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gramMatrices_cmUnitaryShimuraObject : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q), ∃ gP gQ, IsGram X gP gQ := by
  first | exact @GlobalTheory.FlatCM.GramExists.exists_isGram | exact GlobalTheory.FlatCM.GramExists.exists_isGram | (intros; apply GlobalTheory.FlatCM.GramExists.exists_isGram <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosure
noncomputable section

namespace GlobalTheory.LatHatClosed

open scoped TensorProduct RestrictedProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU Topology

variable (F : Type) [Field F] [NumberField F]

theorem isCompact_integralFinite :
    IsCompact {b : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), b.1 v ∈ v.adicCompletionIntegers F} := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

def intAd : AddSubgroup (AF F) where
  carrier := {a | evI F a = 0 ∧ ∀ v, evFin F v a ∈ v.adicCompletionIntegers F}
  zero_mem' := ⟨show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0 from map_zero _,
    fun v => by rw [map_zero]; exact zero_mem _⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, fun v => ?_⟩
    · simp only [evI] at ha hb ⊢
      rw [show (a + b).1 = a.1 + b.1 from rfl, map_add (f := _), ha, hb, add_zero]
    · rw [map_add (evFin F v)]
      exact add_mem (ha' v) (hb' v)
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨?_, fun v => ?_⟩
    · simp only [evI] at ha ⊢
      rw [show (-a).1 = -a.1 from rfl, map_neg, ha, neg_zero]
    · rw [map_neg]; exact neg_mem (ha' v)

theorem isCompact_intAd : IsCompact (intAd F : Set (AF F)) := by
  have e : (intAd F : Set (AF F)) = (({0} : Set (InfiniteAdeleRing F)) ×ˢ
      {b : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), b.1 v ∈ v.adicCompletionIntegers F} : Set _) := by
    ext a
    simp only [SetLike.mem_coe, Set.mem_prod, Set.mem_singleton_iff, Set.mem_setOf_eq]
    show (evI F a = 0 ∧ ∀ v, evFin F v a ∈ v.adicCompletionIntegers F) ↔ _
    have h1 : evI F a = 0 ↔ a.1 = 0 := by
      simp only [evI]; exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff
    rw [h1]
    rfl
  rw [e]
  exact isCompact_singleton.prod (isCompact_integralFinite F)

theorem incV_add {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ} (x y : Fin n → E) :
    incV F (x + y) = incV F x + incV F y := by
  funext i; simp [incV, map_add (f := _)]

theorem incV_zero {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ} :
    incV F (0 : Fin n → E) = 0 := by
  funext i; simp [incV]

theorem incV_zsmul {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ} (m : ℤ) (x : Fin n → E) :
    incV F (m • x) = m • incV F x := by
  funext i; simp [incV, map_zsmul]

theorem isClosed_latHat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (X : Spc F E n), X.L.IsLattice E → IsClosed ((latHat X : AddSubgroup (Fin n → AE F E)) : Set (Fin n → AE F E)) := by
  intro F E _ _ _ _ _ n X hL
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  obtain ⟨s, hs⟩ := Submodule.FG.restrictScalars (R := ℤ) hL.fg
  let ψ : (s → AF F) →+ (Fin n → AE F E) :=
    { toFun := fun c => ∑ i, c i • incV F (i : Fin n → E)
      map_zero' := by simp
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib] }
  let P : AddSubgroup (s → AF F) := AddSubgroup.pi Set.univ (fun _ => intAd F)
  have hψc : Continuous ψ :=
    continuous_finsetSum _ fun i _ => by
      show Continuous fun c : s → AF F => c i • incV F (i : Fin n → E)
      exact (continuous_apply i : Continuous fun c : s → AF F => c i).smul
        (continuous_const : Continuous fun _ : s → AF F => incV F (i : Fin n → E))
  have hPc : IsCompact (P : Set (s → AF F)) := by
    have : (P : Set (s → AF F)) = Set.pi Set.univ (fun _ => (intAd F : Set (AF F))) := by
      ext c; simp [P, AddSubgroup.mem_pi]
    rw [this]; exact isCompact_univ_pi fun _ => isCompact_intAd F
  have hsL : ∀ i ∈ s, i ∈ X.L := fun i hi => by
    have : i ∈ Submodule.span ℤ (s : Set (Fin n → E)) := Submodule.subset_span hi
    rw [hs] at this; exact this
  have key : ∀ x ∈ Submodule.span ℤ (s : Set (Fin n → E)), ∀ a ∈ intAd F, a • incV F x ∈ P.map ψ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      intro a ha
      refine ⟨Pi.single ⟨y, hy⟩ a, ?_, ?_⟩
      · intro i _
        by_cases h : i = ⟨y, hy⟩
        · subst h; simpa using ha
        · simp [Pi.single_apply, h, zero_mem]
      · simp [ψ, Pi.single_apply, ite_smul]
    | zero =>
      intro a _
      rw [incV_zero, smul_zero]; exact zero_mem _
    | add y y' _ _ ih ih' =>
      intro a ha
      rw [incV_add, smul_add]; exact add_mem (ih a ha) (ih' a ha)
    | smul m y _ ih =>
      intro a ha
      rw [incV_zsmul, smul_comm, ← smul_assoc]
      exact ih (m • a) (zsmul_mem ha m)
  have heq : latHat X = P.map ψ := by
    apply le_antisymm
    · refine (AddSubgroup.closure_le _).2 ?_
      rintro z ⟨a, ha0, hav, x, hx, rfl⟩
      have hx' : x ∈ Submodule.span ℤ (s : Set (Fin n → E)) := by rw [hs]; exact hx
      exact key x hx' a ⟨ha0, hav⟩
    · rintro z ⟨c, hc, rfl⟩
      exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure
        ⟨c i, (hc i trivial).1, (hc i trivial).2, i, hsL i i.2, rfl⟩
  rw [heq, AddSubgroup.coe_map]
  exact (hPc.image hψc).isClosed

end GlobalTheory.LatHatClosed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulConjSmul
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.SkewLatSelfDual

open GlobalTheory.FunObj.SqNum

variable {D : D7}

abbrev FI (D : D7) : Type := FractionalIdeal (𝓞 D.host.E)⁰ D.host.E

theorem star_eq_conj (x : D.host.E) : (letI := D.host.cmStar; star x) = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem conj_smul_conj_smul (𝔞 : Ideal (𝓞 D.host.E)) : D.host.conj • (D.host.conj • 𝔞) = 𝔞 := by
  rw [smul_smul]
  have : D.host.conj * D.host.conj = 1 := AlgEquiv.ext (VacMove.conj_conj D)
  rw [this, one_smul]

theorem conj_smul_ne_bot {𝔞 : Ideal (𝓞 D.host.E)} (h : 𝔞 ≠ ⊥) : D.host.conj • 𝔞 ≠ ⊥ := by
  intro h'
  apply h
  rw [← conj_smul_conj_smul 𝔞, h']
  ext x
  simp [Ideal.mem_pointwise_smul_iff_inv_smul_mem]

theorem coe_ne_zero {𝔞 : Ideal (𝓞 D.host.E)} (h : 𝔞 ≠ ⊥) : ((𝔞 : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 := by
  rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]

theorem conj_mem_div {A B : Ideal (𝓞 D.host.E)} (hB : B ≠ ⊥) {x : D.host.E}
    (hx : x ∈ ((A : FI D) / (B : FI D))) :
    D.host.conj x ∈ (((D.host.conj • A : Ideal (𝓞 D.host.E)) : FI D) / ((D.host.conj • B : Ideal (𝓞 D.host.E)) : FI D)) := by
  rw [FractionalIdeal.mem_div_iff_of_ne_zero (coe_ne_zero hB)] at hx
  rw [FractionalIdeal.mem_div_iff_of_ne_zero (coe_ne_zero (conj_smul_ne_bot hB))]
  intro y hy
  obtain ⟨β, hβ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
  have hβ' : D.host.conj • β ∈ B := by
    have := Ideal.smul_mem_pointwise_smul D.host.conj β _ hβ
    rwa [conj_smul_conj_smul] at this
  obtain ⟨α, hα, hαe⟩ := (FractionalIdeal.mem_coeIdeal _).1 (hx _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hβ', rfl⟩))
  refine (FractionalIdeal.mem_coeIdeal _).2 ⟨D.host.conj • α, Ideal.smul_mem_pointwise_smul _ _ _ hα, ?_⟩
  have e1 : algebraMap (𝓞 D.host.E) D.host.E (D.host.conj • α) = D.host.conj (algebraMap (𝓞 D.host.E) D.host.E α) := rfl
  have e2 : algebraMap (𝓞 D.host.E) D.host.E (D.host.conj • β) = D.host.conj (algebraMap (𝓞 D.host.E) D.host.E β) := rfl
  rw [e1, hαe, e2, map_mul, VacMove.conj_conj]

theorem mem_skewLat {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} (v : Fin N → D.host.E) :
    v ∈ skewLat D 𝔪 N ↔ ∀ i, v i ∈ ((𝔪 : FI D) / ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FI D)) := by
  simp [skewLat, Submodule.mem_pi]

theorem skewLat_SD {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) (N : ℕ) : SD D (skewLat D 𝔪 N) := by
  set 𝔫 : Ideal (𝓞 D.host.E) := D.host.conj • 𝔪 with h𝔫
  have h𝔫0 : 𝔫 ≠ ⊥ := conj_smul_ne_bot h𝔪
  have h𝔪𝔫 : D.host.conj • 𝔫 = 𝔪 := conj_smul_conj_smul 𝔪
  set I : FI D := (𝔪 : FI D) / (𝔫 : FI D) with hIdef
  set J : FI D := (𝔫 : FI D) / (𝔪 : FI D) with hJdef
  have hI0 : I ≠ 0 := div_ne_zero (coe_ne_zero h𝔪) (coe_ne_zero h𝔫0)
  have hJ0 : J ≠ 0 := div_ne_zero (coe_ne_zero h𝔫0) (coe_ne_zero h𝔪)
  have hJI : J * I = 1 := by
    rw [hIdef, hJdef, div_mul_div_comm, mul_comm (𝔫 : FI D), div_self]
    exact mul_ne_zero (coe_ne_zero h𝔪) (coe_ne_zero h𝔫0)
  have hIJ' : 1 / J = I := by rw [hJdef, hIdef, one_div_div]
  have cI : ∀ x ∈ I, D.host.conj x ∈ J := fun x hx => by
    have := conj_mem_div h𝔫0 hx
    rwa [h𝔪𝔫] at this
  have cJ : ∀ z ∈ J, D.host.conj z ∈ I := fun z hz => by
    have := conj_mem_div h𝔪 hz
    rwa [h𝔪𝔫] at this
  have memL : ∀ v : Fin N → D.host.E, v ∈ skewLat D 𝔪 N ↔ ∀ i, v i ∈ I := mem_skewLat
  letI := D.host.cmStar
  show IsSDLat D.host.E N (skewLat D 𝔪 N)
  refine ⟨Submodule.fg_pi fun _ => FractionalIdeal.fg_of_isNoetherianRing le_rfl _, ?_, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := (I : Submodule (𝓞 D.host.E) D.host.E))
      (fun h => hI0 (FractionalIdeal.coeToSubmodule_injective (h.trans FractionalIdeal.coe_zero.symm)))
    have hs : ∀ i : Fin N, (Pi.single i a : Fin N → D.host.E) ∈ skewLat D 𝔪 N := fun i => by
      rw [memL]
      intro j
      by_cases hj : j = i
      · subst hj; simpa using ha
      · rw [Pi.single_eq_of_ne hj]; exact Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E)
    rw [Submodule.eq_top_iff']
    intro x
    have : x = ∑ i, (x i * a⁻¹) • (Pi.single i a : Fin N → D.host.E) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, ha0]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs i))
  · rw [memL] at hx hy
    unfold Formalism.BasicNotions.stdH
    refine Subring.sum_mem _ fun i _ => ?_
    have hm : star (x i) * y i ∈ J * I := by
      rw [star_eq_conj]
      exact FractionalIdeal.mul_mem_mul (cI _ (hx i)) (hy i)
    rw [hJI] at hm
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 hm
    exact ⟨a, ha⟩
  · rw [memL]
    intro i
    rw [← hIJ', FractionalIdeal.mem_div_iff_of_ne_zero hJ0]
    intro z hz
    have hx : (Pi.single i (D.host.conj z) : Fin N → D.host.E) ∈ skewLat D 𝔪 N := by
      rw [memL]
      intro j
      by_cases hj : j = i
      · subst hj; simpa using cJ z hz
      · rw [Pi.single_eq_of_ne hj]; exact Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E)
    have h1 := h _ hx
    unfold Formalism.BasicNotions.stdH at h1
    have e : (∑ j, star ((Pi.single i (D.host.conj z) : Fin N → D.host.E) j) * y j) = y i * z := by
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, star_eq_conj, VacMove.conj_conj, mul_comm]
      · intro j _ hj; simp [Pi.single_eq_of_ne hj]
      · simp
    rw [e] at h1
    obtain ⟨a, ha⟩ := h1
    exact (FractionalIdeal.mem_one_iff _).2 ⟨a, ha⟩

end GlobalTheory.SkewLatSelfDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorConjIsThetaSomeLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorConjIsThetaSomeLevel
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall.CosetTheta

variable {D : D7}

theorem homL_nsmul_mem {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (M : ℕ) (hM : ∀ y ∈ L₁, M • y ∈ L₂)
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ homL D L L₁) : M • A ∈ homL D L L₂ := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    refine Submodule.subset_span fun x hx => ?_
    rw [Matrix.smul_mulVec]
    exact hM _ (hA x hx)
  | zero => simp
  | add A B _ _ hA hB => rw [smul_add]; exact add_mem hA hB
  | smul c A _ hA => rw [smul_comm]; exact Submodule.smul_mem _ c hA

theorem YYl_nsmul_mem {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (M : ℕ) (hM : ∀ y ∈ L₁, M • y ∈ L₂)
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ YYl D L L₁) : M • A ∈ YYl D L L₂ := by
  induction hA using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    exact Submodule.subset_span ⟨a, ha, M • A, homL_nsmul_mem M hM hA, smul_comm _ _ _⟩
  | zero => simp
  | add A B _ _ hA hB => rw [smul_add]; exact add_mem hA hB
  | smul c A _ hA => rw [smul_comm]; exact Submodule.smul_mem _ c hA

theorem La_nsmul_mem (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (M : ℕ) (hM : ∀ y ∈ L₁, M • y ∈ L₂)
    {x : VC D N N'} (hx : x ∈ La D (tor0 D cc δ) L L₁) : M • x ∈ La D (tor0 D cc δ) L L₂ := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨w, hw, M • A, YYl_nsmul_mem M hM hA, ?_⟩
    funext τ i j
    simp only [embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
    ring
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem skewLat_nsmul_le (𝔫 : Ideal (𝓞 D.host.E)) (h : D.host.conj • 𝔫 ≠ ⊥) (N : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ y ∈ skewLat D 𝔫 N, M • y ∈ stdL D N := by
  refine ⟨Ideal.absNorm (D.host.conj • 𝔫), Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using h),
    fun y hy => ?_⟩
  simp only [skewLat, stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at hy ⊢
  intro i
  rw [Pi.smul_apply]
  have hyi := hy i
  rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero
    (by simpa using h)] at hyi
  have hmem := hyi (algebraMap (𝓞 D.host.E) D.host.E (Ideal.absNorm (D.host.conj • 𝔫) : 𝓞 D.host.E))
    ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.absNorm_mem _, rfl⟩)
  obtain ⟨x', -, hx'⟩ := (FractionalIdeal.mem_coeIdeal _).1 hmem
  rw [Submodule.mem_one]
  refine ⟨x', ?_⟩
  rw [hx', nsmul_eq_mul, mul_comm, map_natCast]

end GlobalTheory.BotPairSmall.CosetTheta

namespace GlobalTheory.BotPairSmall.CosetTheta

theorem iop_mem_TT {D : D7} {δ : ℂ} (hc : Crv D ⊤ δ) {a d : ℕ} {B : AddSubgroup (VC D a d)} {M : ℕ} (hM : 0 < M)
    (hB : ∀ x ∈ B, M • x ∈ La0 D (tor0 D ⊤ δ) a d) {e0 : VC D a d → ℂ} (heT : e0 ∈ TT D (tor0 D ⊤ δ) a d) :
    Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) B e0 ∈ TT D (tor0 D ⊤ δ) a d := by
  have hlc := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  set T := tor0 D ⊤ δ
  set A := La0 D T a d
  have h0 : (0 : VC D a d → ℂ) ∈ TT D T a d := by
    have := hlc.2.2.2 0 e0 heT
    rwa [zero_smul] at this
  by_cases hfin : Finite (B ⧸ A.addSubgroupOf B)
  · haveI := Fintype.ofFinite (B ⧸ A.addSubgroupOf B)
    have e : Iop D T A B e0 = ∑ q : B ⧸ A.addSubgroupOf B,
        ((((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) * al D T ((Quotient.out q : B) : VC D a d) *
          (wdPh D T ((Quotient.out q : B) : VC D a d))⁻¹) • Wd D T ((Quotient.out q : B) : VC D a d) e0) := by
      funext z
      simp only [Iop, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Wd]
      rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      have : wdPh D T ((Quotient.out q : B) : VC D a d) ≠ 0 := by simp [wdPh, ee, Complex.exp_ne_zero]
      field_simp
    rw [e]
    refine Finset.sum_induction _ (· ∈ TT D T a d) (fun F G hF hG => hlc.2.2.1 F hF G hG) h0 fun q _ => ?_
    exact hlc.2.2.2 _ _ (GlobalTheory.FunObj.NormUniq.wd_rat_mem_TT hc hM (hB _ (Quotient.out q : B).2) heT)
  · have hi : (A.addSubgroupOf B).index = 0 :=
      AddSubgroup.index_eq_zero_iff_infinite.2 (not_finite_iff_infinite.1 hfin)
    have e : Iop D T A B e0 = 0 := by
      funext z
      simp [Iop, hi]
    rw [e]; exact h0

end GlobalTheory.BotPairSmall.CosetTheta

theorem GlobalTheory.BotPairSmall.cvec_conj_mem_TT : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0 ∈ TT D (tor0 D ⊤ δ) a d := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho
  have hlc := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  have s0 := VacMove.sd_of_moves (VacMove.moves_one D a)
  have s0' := VacMove.sd_of_moves (VacMove.moves_one D d)
  have heT : e0 ∈ TT D (tor0 D ⊤ δ) a d := hlc.1 _ _ s0 s0' e0 hv.1
  have hne : D.host.conj • (D.host.conj • 𝔪) ≠ ⊥ :=
    GlobalTheory.BotPairSmall.conj_smul_ne_bot D (GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm)
  obtain ⟨M, hM, hMs⟩ := GlobalTheory.BotPairSmall.CosetTheta.skewLat_nsmul_le (D := D) (D.host.conj • 𝔪) hne d
  have hI := GlobalTheory.BotPairSmall.CosetTheta.iop_mem_TT hc hM
    (fun x hx => GlobalTheory.BotPairSmall.CosetTheta.La_nsmul_mem (L := stdL D a) ⊤ δ M hMs hx) heT
  unfold GlobalTheory.BotPairSmall.cvec
  exact hlc.2.2.2 _ _ (hlc.2.1 _ _ hI)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorConjIsThetaSomeLevelStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetVector_conj_isTheta_some_level : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0 ∈ TT D (tor0 D ⊤ δ) a d := by
  first | exact @GlobalTheory.BotPairSmall.cvec_conj_mem_TT | exact GlobalTheory.BotPairSmall.cvec_conj_mem_TT | (intros; apply GlobalTheory.BotPairSmall.cvec_conj_mem_TT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorCosetScaledIntegralEqRestrictedProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorCosetScaledIntegralEqRestrictedProduct
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.EvAdm

noncomputable section

namespace GlobalTheory.EvAdm

variable {F : Type} [Field F] [NumberField F] {κ : Type}

def cosetBoxV (a : F) (r : κ → FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) : Set (κ → Fv F v) :=
  {x | ∀ i, (algebraMap F (v.adicCompletion F) a)⁻¹ * (x i - (r i) v) ∈ v.adicCompletionIntegers F}

theorem indicator_cosetBoxV_mem_SB [Finite κ] {a : F} (ha : a ≠ 0) (r : κ → FiniteAdeleRing (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) :
    Set.indicator (cosetBoxV a r v) (1 : (κ → Fv F v) → ℂ) ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  classical
  have ha0 : algebraMap F (v.adicCompletion F) a ≠ 0 := (map_ne_zero _).2 ha
  let P : Set (κ → Fv F v) := Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v))
  let f : (κ → Fv F v) → (κ → Fv F v) := fun x i => (algebraMap F (v.adicCompletion F) a)⁻¹ * (x i - (r i) v)
  let g : (κ → Fv F v) → (κ → Fv F v) := fun z i => algebraMap F (v.adicCompletion F) a * z i + (r i) v
  have hf : Continuous f :=
    continuous_pi fun i => continuous_const.mul ((continuous_apply i).sub continuous_const)
  have hg : Continuous g :=
    continuous_pi fun i => (continuous_const.mul (continuous_apply i)).add continuous_const
  have hS : cosetBoxV a r v = f ⁻¹' P := by
    ext x
    simp only [cosetBoxV, P, f, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq,
      SetLike.mem_coe]
  have hPo : IsOpen P := isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _
  have hPc : IsCompact P := isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v
  have hcl : IsClopen (cosetBoxV a r v) := by
    rw [hS]
    exact ⟨hPc.isClosed.preimage hf, hPo.preimage hf⟩
  have hco : IsCompact (cosetBoxV a r v) := by
    refine (hPc.image hg).of_isClosed_subset hcl.isClosed ?_
    intro x hx
    refine ⟨f x, ?_, ?_⟩
    · rw [hS] at hx
      exact hx
    · funext i
      simp only [f, g]
      rw [mul_inv_cancel_left₀ ha0, sub_add_cancel]
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ cosetBoxV a r v
    · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
      rfl
    · filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy
      simp only [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro' hco hcl.isClosed (fun y hy => Set.indicator_of_notMem hy _)

theorem eventually_cosetBoxV_eq {a : F} (ha : a ≠ 0) (r : κ → FiniteAdeleRing (𝓞 F) F) [Finite κ] :
    ∀ᶠ v in cofinite, cosetBoxV a r v = {x | ∀ i, x i ∈ v.adicCompletionIntegers F} := by
  have h1 : ∀ᶠ v in cofinite, (algebraMap F (FiniteAdeleRing (𝓞 F) F) a) v ∈ v.adicCompletionIntegers F :=
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) a).2
  have h2 : ∀ᶠ v in cofinite, (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹) v ∈ v.adicCompletionIntegers F :=
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹).2
  have h3 : ∀ᶠ v in cofinite, ∀ i, (r i) v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => (r i).2
  filter_upwards [h1, h2, h3] with v hv1 hv2 hv3
  have ha0 : algebraMap F (v.adicCompletion F) a ≠ 0 := (map_ne_zero _).2 ha
  have e1 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) a) v = algebraMap F (v.adicCompletion F) a := rfl
  have e2 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹) v = (algebraMap F (v.adicCompletion F) a)⁻¹ := by
    show algebraMap F (v.adicCompletion F) a⁻¹ = _
    exact map_inv₀ _ a
  rw [e1] at hv1
  rw [e2] at hv2
  ext x
  simp only [cosetBoxV, Set.mem_setOf_eq]
  refine forall_congr' fun i => ⟨fun h => ?_, fun h => ?_⟩
  · have hd : x i - (r i) v ∈ v.adicCompletionIntegers F := by
      rw [← mul_inv_cancel_left₀ ha0 (x i - (r i) v)]
      exact mul_mem hv1 h
    have e : x i = (x i - (r i) v) + (r i) v := (sub_add_cancel _ _).symm
    rw [e]
    exact add_mem hd (hv3 i)
  · exact mul_mem hv2 (sub_mem h (hv3 i))

theorem indicator_coset_scaledInt_eq_finprod : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F)
    (r : κ → FiniteAdeleRing (𝓞 F) F), a ≠ 0 →
    ∃ φ : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) ∧
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      ∀ y : κ → FiniteAdeleRing (𝓞 F) F, Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) y =
        ∏ᶠ v, φ v fun i => evalV F v (y i) := by
  intro F _ _ κ _ a r ha
  classical
  refine ⟨fun v => Set.indicator (cosetBoxV a r v) 1, fun v => indicator_cosetBoxV_mem_SB ha r v, ?_, ?_⟩
  · filter_upwards [eventually_cosetBoxV_eq ha r] with v hv
    rw [hv]
  · intro y
    have hmem : ∀ v, (fun i => evalV F v (y i)) ∈ cosetBoxV a r v ↔
        ∀ i, (algebraMap F (v.adicCompletion F) a)⁻¹ * ((y - r) i) v ∈ v.adicCompletionIntegers F :=
      fun v => Iff.rfl
    by_cases hy : y - r ∈ scaledInt F κ a
    · rw [Set.indicator_of_mem (show y ∈ {y | y - r ∈ scaledInt F κ a} from hy)]
      have h1 : ∀ v, Set.indicator (cosetBoxV a r v) (1 : (κ → Fv F v) → ℂ) (fun i => evalV F v (y i)) = 1 :=
        fun v => by rw [Set.indicator_of_mem ((hmem v).2 fun i => hy i v)]; rfl
      rw [finprod_congr h1, finprod_one]
    · rw [Set.indicator_of_notMem (show y ∉ {y | y - r ∈ scaledInt F κ a} from hy)]
      rw [mem_scaledInt] at hy
      push_neg at hy
      obtain ⟨i, v, hv⟩ := hy
      symm
      refine finprod_eq_zero _ v ?_ ?_
      · exact Set.indicator_of_notMem (fun h => hv ((hmem v).1 h i)) _
      · have hint : ∀ᶠ w in cofinite, ∀ i, evalV F w (y i) ∈ w.adicCompletionIntegers F :=
          Filter.eventually_all.2 fun i => (y i).2
        refine (Filter.eventually_cofinite.1 ((eventually_cosetBoxV_eq ha r).and hint)).subset ?_
        intro w hw h'
        apply hw
        simp only [Function.mem_mulSupport, not_not]
        rw [h'.1, Set.indicator_of_mem (show (fun i => evalV F w (y i)) ∈ {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} from h'.2)]
        rfl

end GlobalTheory.EvAdm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorCosetScaledIntegralEqRestrictedProductStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.EvAdm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indicator_coset_scaledIntegral_eq_restrictedProduct : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F) (r : κ → FiniteAdeleRing (𝓞 F) F), a ≠ 0 →
    ∃ φ : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) ∧
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      ∀ y : κ → FiniteAdeleRing (𝓞 F) F, Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) y =
        ∏ᶠ v, φ v fun i => evalV F v (y i) := by
  first | exact @GlobalTheory.EvAdm.indicator_coset_scaledInt_eq_finprod | exact GlobalTheory.EvAdm.indicator_coset_scaledInt_eq_finprod | (intros; apply GlobalTheory.EvAdm.indicator_coset_scaledInt_eq_finprod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockRepEquivFirst
open GlobalTheory.PRep GlobalTheory.SmGL Matrix GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.DiagCell

theorem mem_parab_of_single {R : Type} [CommRing R] {β : Type} [LinearOrder β] {n : β → ℕ} {t : Type}
    [Fintype t] [DecidableEq t]
    (e : (Σ j, Fin (n j)) ≃ t) (a₀ : β) (h0 : ∀ j, j ≠ a₀ → n j = 0) (x : GL t R) :
    x ∈ parab R e := by
  refine mem_parab_iff.2 fun a b i j hab => ?_
  by_cases ha : a = a₀
  · have hb : b ≠ a₀ := fun e => by rw [e, ha] at hab; exact lt_irrefl _ hab
    have hj := j.isLt
    have hz := h0 b hb
    omega
  · have hi := i.isLt
    have hz := h0 a ha
    omega

theorem eq_one_of_mem_unipRad_single {R : Type} [CommRing R] {β : Type} [Fintype β] [LinearOrder β]
    {n : β → ℕ} {t : Type} [Fintype t] [DecidableEq t] (e : (Σ j, Fin (n j)) ≃ t) (a₀ : β)
    (h0 : ∀ j, j ≠ a₀ → n j = 0) {g : GL t R} (hg : g ∈ unipRad R e) : g = 1 := by
  obtain ⟨-, h2⟩ := mem_unipRad.1 hg
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
  by_cases ha : a = a₀
  · by_cases hb : b = a₀
    · obtain rfl : b = a := hb.trans ha.symm
      rw [h2 b i j]
      simp [Matrix.one_apply]
    · exact absurd j.2 (by have := j.2; have := h0 b hb; omega)
  · exact absurd i.2 (by have := i.2; have := h0 a ha; omega)

end GlobalTheory.DiagCell

namespace GlobalTheory.DiagCell

theorem cellFunctor_diag_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {m : Type} [Fintype m] [DecidableEq m] (b : SizeMatrix (Two (Fin 1) m) (Two (Fin 1) m)),
    b.1 false true = 0 → b.1 true false = 0 →
    ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k (Two (Fin 1) m)) W), IsSmooth ρ →
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin 1) m i) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin 1) m j),
      Nonempty ((cellFunctor f g ρ).Equiv ρ) := by
  intro k _ _ _ _ m _ _ b h01 h10 W _ _ ρ hsm
  have hrz : ∀ i j, j ≠ i → b.1 i j = 0 := by
    intro i j hj
    cases i <;> cases j <;> simp_all
  have hcz : ∀ j i, i ≠ j → b.1 i j = 0 := fun j i hi => hrz i j (Ne.symm hi)
  have hcard : ∀ i, Fintype.card (Fin (b.1 i i)) = Fintype.card (Two (Fin 1) m i) := by
    intro i
    have r := b.2.1 i
    rw [Fintype.sum_bool] at r
    cases i <;> simp_all
  let E : ∀ i, Fin (b.1 i i) ≃ Two (Fin 1) m i := fun i => Fintype.equivOfCardEq (hcard i)
  let f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin 1) m i := fun i =>
    (OneBlockCell.valEquiv (n := fun j => b.1 i j) i rfl (fun j hj => hrz i j hj)).trans (E i)
  let g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin 1) m j := fun j =>
    (OneBlockCell.valEquiv (n := fun i => b.1 i j) j rfl (fun i hi => hcz j i hi)).trans (E j)
  refine ⟨f, g, ?_⟩
  have hbot : twKer ρ (relUnip k f) 1 = ⊥ := by
    refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨n, v, rfl⟩
    have : (n : Levi k (Two (Fin 1) m)) = 1 := funext fun i =>
      eq_one_of_mem_unipRad_single (f i) i (fun j hj => hrz i j hj) (n.2 i trivial)
    simp [this]
  have hδ : ∀ z, relDeltaHalf k (fun i j => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun i _ =>
      OneBlockCell.deltaHalf_eq_one_of_single i (fun j hj => hrz i j hj) (z i)
  have hδ' : ∀ z, relDeltaHalf k (fun j i => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun j _ =>
      OneBlockCell.deltaHalf_eq_one_of_single j (fun i hi => hcz j i hi) (z j)
  have hP : ∀ x, x ∈ relParab k g := fun x j _ =>
    mem_parab_of_single (g j) j (fun i hi => hcz j i hi) (x j)
  have hfg : ∀ i (t : Fin (b.1 i i)), f i ⟨i, t⟩ = g i ⟨i, t⟩ := fun i t => rfl
  have hγ : ∀ (p : relParab k g),
      relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g p)) =
        (p : Levi k (Two (Fin 1) m)) := by
    intro p
    funext i
    rw [relEmb_apply]
    refine Units.ext (Matrix.ext fun x y => ?_)
    obtain ⟨⟨a, t⟩, rfl⟩ := (f i).surjective x
    obtain ⟨⟨a', s⟩, rfl⟩ := (f i).surjective y
    have ha : a = i := by
      by_contra hne
      have h1 := hrz i a hne
      have h2 := t.2
      omega
    have ha' : a' = i := by
      by_contra hne
      have h1 := hrz i a' hne
      have h2 := s.2
      omega
    subst ha
    subst ha'
    have hsame (z : Levi k (fun j => Fin (b.1 a' j))) (u v : Fin (b.1 a' a')) :
        (leviEmb k (f a') z : Matrix _ _ k) (f a' ⟨a', u⟩) (f a' ⟨a', v⟩) =
          (z a' : Matrix _ _ k) u v := by
      simp [leviEmb, Matrix.blockDiagonal'_apply_eq]
    rw [hsame, hfg, hfg]
    rfl
  let Ψ : W ≃ₗ[ℂ] Jacquet ρ (relUnip k f) := (Submodule.quotEquivOfEqBot _ hbot).symm
  have hΨ : ∀ u, Ψ u = Submodule.Quotient.mk u := fun u => rfl
  let τ := (GlobalTheory.SmGL.twist ((relJac f ρ).comp (swapBlocks k (fun i j => Fin (b.1 i j))))
        (relDeltaHalf k (fun j i => Fin (b.1 i j)))).comp (relProj k g)
  have law : ∀ (p : relParab k g) u, τ p (Ψ u) = Ψ (ρ p u) := by
    intro p u
    rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, hΨ, relJac_mk, hδ, hδ', hΨ, hγ p]
    simp only [inv_one, Units.val_one, one_smul]
  let F : ρ.IntertwiningMap (cellFunctor f g ρ) :=
    { toFun := fun u => ⟨⟨fun x => Ψ (ρ x u), fun p x => by
          show Ψ (ρ (↑p * x) u) = _
          rw [map_mul, Module.End.mul_apply]
          exact (law p _).symm⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hsm u).mem_nhds (by simp)) fun x hx => by
          have hx' : ρ x u = u := hx
          refine Subtype.ext (funext fun y => ?_)
          show Ψ (ρ (y * x) u) = Ψ (ρ y u)
          rw [map_mul, Module.End.mul_apply, hx'])⟩
      map_add' := fun u w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c u => Subtype.ext (Subtype.ext (funext fun x => by simp))
      isIntertwining' := fun h => LinearMap.ext fun u => Subtype.ext (Subtype.ext (funext fun x => by
        show Ψ (ρ x (ρ h u)) = Ψ (ρ (x * h) u)
        rw [map_mul, Module.End.mul_apply])) }
  refine ⟨(LocGL.equivOfBijective F ⟨fun u w hw => ?_, fun φ => ⟨Ψ.symm (φ.1.1 1),
    Subtype.ext (Subtype.ext (funext fun x => ?_))⟩⟩).symm⟩
  · have h1 : Ψ (ρ 1 u) = Ψ (ρ 1 w) := congrArg (fun φ => φ.1.1 1) hw
    simpa using h1
  · show Ψ (ρ x (Ψ.symm (φ.1.1 1))) = φ.1.1 x
    refine (law ⟨x, hP x⟩ (Ψ.symm (φ.1.1 1))).symm.trans ?_
    refine (congrArg (τ ⟨x, hP x⟩) (Ψ.apply_symm_apply (φ.1.1 1))).trans ?_
    refine (φ.1.2 ⟨x, hP x⟩ 1).symm.trans ?_
    exact congrArg φ.1.1 (mul_one x)

end GlobalTheory.DiagCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCosocleComp
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CosocleComp

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def subrepOfComp (ρ : Representation ℂ G V) (s : H →* G) (hs : Function.Surjective s) :
    Subrepresentation (ρ.comp s : Representation ℂ H V) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule, fun g v hv => by
    obtain ⟨h, rfl⟩ := hs g
    exact S.apply_mem_toSubmodule h hv⟩
  invFun S := ⟨S.toSubmodule, fun h _ hv => S.apply_mem_toSubmodule (s h) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp {ρ : Representation ℂ G V} {s : H →* G} (hs : Function.Surjective s)
    (h : ρ.IsIrreducible) : Representation.IsIrreducible (ρ.comp s : Representation ℂ H V) :=
  (subrepOfComp ρ s hs).isSimpleOrder_iff.2 h

theorem isCosocle_comp : ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (σ : Representation ℂ G W) (π : Representation ℂ G V) (s : H →* G), Function.Surjective s →
    IsCosocle σ π → IsCosocle (σ.comp s) (π.comp s) := by
  intro G H V W _ _ _ _ _ _ σ π s hs h
  obtain ⟨hi, f, hf, hS⟩ := h
  let f' : Representation.IntertwiningMap (π.comp s : Representation ℂ H V) (σ.comp s : Representation ℂ H W) := ⟨f.toLinearMap, fun g => f.isIntertwining' (s g)⟩
  refine ⟨isIrreducible_comp hs hi, f', hf, fun S hS' => ?_⟩
  have h1 := hS (subrepOfComp π s hs S) ((OrderIso.isCoatom_iff (subrepOfComp π s hs) S).2 hS')
  have h2 := congrArg Subrepresentation.toSubmodule h1
  have inj : Function.Injective (Subrepresentation.toSubmodule (ρ := (π.comp s : Representation ℂ H V))) := by
    rintro ⟨a, _⟩ ⟨b, _⟩ rfl; rfl
  exact inj h2

end GlobalTheory.CosocleComp
end
end

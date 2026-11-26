module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSubquotientParIndProductsFlattened
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockVectorJacquetNonzero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetModuleInStagesRefinedBlocks
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryOfTraceEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulPowTwoLeTripleProdOfGe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicEquiv
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.SplitTypeCompl

theorem exists_padic_equiv : ∀ (D : D7) (s : SplitPlace D.host.E), s.v ∈ gPl D →
    ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* s.w.adicCompletion D.host.E), Continuous i := by
  intro D s hs
  obtain ⟨w, hw, k, hk⟩ := hs
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hwk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by simpa [placesOver] using hk
  have hv : ((D.host.g k : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
    rw [← hw, Ideal.mem_comap, map_natCast]; exact hwk
  have hsw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ s.w.asIdeal := by
    have := hv
    rw [← s.w_under, Ideal.mem_comap, map_natCast] at this
    exact this
  obtain ⟨h1, h2, -⟩ := GlobalTheory.Mem.Chr.splitsC_place (D.host.g_prime k) (D.nd.g_split k) _ hsw
  haveI : CharZero (s.w.adicCompletion D.host.E) :=
    charZero_of_injective_ringHom (algebraMap D.host.E _).injective
  obtain ⟨φ, h, -⟩ := GlobalTheory.QpChar.exists_ringEquiv_padic (s.w.adicCompletion D.host.E) (D.host.g k)
    ((GlobalTheory.LocLanglands.resCard_eq_normV _).trans (by
      simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h1))
    (GlobalTheory.TypeIdent.irreducible_natCast_compl _ hsw h2)
  exact ⟨D.host.g k, inferInstance, φ, h⟩

end GlobalTheory.SplitTypeCompl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProductsStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

private theorem flat_strictMono (d h : ℕ) : StrictMono (fun p : Fin (d * h) =>
    (toLex ⟨(finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2⟩ : Σₗ _ : Fin d, Fin h)) := by
  intro p q hpq
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨a', b'⟩, rfl⟩ := finProdFinEquiv.surjective q
  simp only [Equiv.symm_apply_apply]
  have h1 : (b : ℕ) + h * a < b' + h * a' := hpq
  rcases lt_trichotomy a a' with hlt | rfl | hgt
  · exact Sigma.Lex.left _ _ hlt
  · exact Sigma.Lex.right _ _ (show b < b' from by
      rw [Fin.lt_def]; omega)
  · exfalso
    have h2 : (a' : ℕ) + 1 ≤ a := hgt
    have h3 := Nat.mul_le_mul_left h h2
    have h4 := b'.2
    rw [Nat.mul_add, Nat.mul_one] at h3
    omega

theorem _root_.GlobalTheory.T.parabolicInduction_in_stages_product_of_products : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d h : ℕ) (y : Fin d → Fin h → IrrGL (k := k)) (N : Fin d → ℕ) (M : ℕ) (hN : ∀ i, ∑ j, (y i j).1 = N i)
    (hM : ∑ i, N i = M)
    (hM' : ∑ p : Fin (d * h), (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1 = M),
    Nonempty ((multiProd (stdBlocks N hM) fun i => prodIrr (y i) (hN i)).Equiv
      (prodIrr (fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) hM')) := by
  intro k _ _ _ _ d h y N M hN hM hM'
  have hφ := GlobalTheory.SmGL.Stages.stages_equiv (k := k) d N (fun _ => h) (fun a b => (y a b).1)
    (fun a => stdBlocks (fun b => (y a b).1) (hN a)) _ (fun a b => (y a b).rep) (Fin M) (stdBlocks N hM)
  obtain ⟨E0, ⟨φ⟩⟩ := hφ
  let F : Fin (d * h) ≃ Σₗ _ : Fin d, Fin h :=
    finProdFinEquiv.symm.trans ((Equiv.sigmaEquivProd (Fin d) (Fin h)).symm.trans toLex)
  let E : (Σ p : Fin (d * h), Fin (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1) ≃ Fin M :=
    (Equiv.sigmaCongrLeft (β := fun c : Σₗ _ : Fin d, Fin h => Fin (y (ofLex c).1 (ofLex c).2).1) F).trans E0
  have hψ := GlobalTheory.SmGL.BlockRename.multiProd_rename (k := k) F (flat_strictMono d h) F.surjective E0 E
    (fun _ _ => rfl) fun c => (y (ofLex c).1 (ofLex c).2).rep
  obtain ⟨ψ⟩ := hψ
  have hχ := GlobalTheory.ProdReorder.multiProd_placing (k := k) E
    (stdBlocks (fun p => (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1) hM')
    fun p => (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).rep
  obtain ⟨χ⟩ := hχ
  exact ⟨φ.trans (ψ.trans χ)⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientJacquetModuleRefineTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientJacquetModuleRefineTensor
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open GlobalTheory.JacStages

namespace GlobalTheory.JacStages

theorem isSubquotient_jac_refine : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    ∀ (X : Fin s → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), (∀ a, IsSmooth (ρ a)) →
    IsSubquotient (piTensor ρ) (GlobalTheory.SmGL.jac e π) →
    ∀ (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)] [∀ a b, Module ℂ (Y a b)]
    (ρ' : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (Y a b)),
    (∀ a, IsSubquotient (piTensor (ρ' a)) (GlobalTheory.SmGL.jac (e' a) (ρ a))) →
    ∃ E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n,
      IsSubquotient (piTensor fun c => ρ' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) (GlobalTheory.SmGL.jac E π) := by
  intro k _ _ _ _ n s d e V _ _ π hπ X _ _ ρ _ hsub t d' e' Y _ _ ρ' hρ'
  refine ⟨refinePlace e e', ?_⟩
  refine isSubquotient_of_comp (flatHom fun a b => GL (Fin (d' a b)) k) (flatHom_surjective _) ?_
  obtain ⟨φR⟩ := GlobalTheory.T.piExteriorTensor_flattenedIndex_equiv_nested s t (fun a b => GL (Fin (d' a b)) k) Y ρ'
  obtain ⟨φT⟩ := GlobalTheory.T.relativeJacquet_piExteriorTensor_equiv_normalized k s d t d' e' X ρ
  obtain ⟨φS⟩ := GlobalTheory.T.jacquetModule_in_stages_refined_blocks k s n d e t d' e' V π
  have h1 : IsSubquotient (piTensor fun a => piTensor (ρ' a)) (piTensor fun a => GlobalTheory.SmGL.jac (e' a) (ρ a)) :=
    GlobalTheory.piTensor_isSubquotient_of_forall _ _ _ _ _ _ hρ'
  have h3 := GlobalTheory.T.isSubquotient_relativeJacquet_blockLevi k s d t d' e' _ _ (piTensor ρ) (GlobalTheory.SmGL.jac e π) (isSmooth_jac e hπ) hsub
  exact (isSubquotient_of_equiv φR).trans (h1.trans ((isSubquotient_of_equiv φT.symm).trans
    (h3.trans (isSubquotient_of_equiv φS.symm))))

end GlobalTheory.JacStages
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientJacquetModuleRefineTensorStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSubquotient_jacquetModule_refine_tensor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    ∀ (X : Fin s → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), (∀ a, IsSmooth (ρ a)) →
    IsSubquotient (piTensor ρ) (GlobalTheory.SmGL.jac e π) →
    ∀ (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)] [∀ a b, Module ℂ (Y a b)]
    (ρ' : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (Y a b)),
    (∀ a, IsSubquotient (piTensor (ρ' a)) (GlobalTheory.SmGL.jac (e' a) (ρ a))) →
    ∃ E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n,
      IsSubquotient (piTensor fun c => ρ' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) (GlobalTheory.SmGL.jac E π) := by
  first | exact @GlobalTheory.JacStages.isSubquotient_jac_refine | exact GlobalTheory.JacStages.isSubquotient_jac_refine | (intros; apply GlobalTheory.JacStages.isSubquotient_jac_refine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotInDetectByEqvMap
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem isotIn_detect_by_eqv_map : ∀ (D : D7) {n : ℕ} (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (π : NG.FinTyp D.host.E n) (y : A), y ∈ principalLevelFrame.isotIn ρ C π → y ≠ 0 → ∃ q : A →ₗ[ℂ] (GAf D.host.E n → ℂ), q y ≠ 0 ∧ ∀ z ∈ principalLevelFrame.isotIn ρ C π, q z ∈ π.S ∧ ∀ h, q (ρ h z) = NG.rt D.host.E n h (q z) := by
  intro D n A _ _ ρ C π y hy hy0
  let St : Submodule ℂ A → Prop := fun K => ∀ h, ∀ x ∈ K, ρ h x ∈ K
  have rangeSt : ∀ Φ : π.S →ₗ[ℂ] A, principalLevelFrame.IsEqvA ρ π Φ → St (LinearMap.range Φ) := by
    rintro Φ hΦ h _ ⟨f, rfl⟩
    exact ⟨_, hΦ h f⟩
  have rangeLe : ∀ Φ : π.S →ₗ[ℂ] A, principalLevelFrame.IsEqvA ρ π Φ → LinearMap.range Φ ≤ C →
      LinearMap.range Φ ≤ principalLevelFrame.isotIn (D := D) ρ C π := fun Φ hΦ hC =>
    le_iSup₂ (f := fun (Ψ : π.S →ₗ[ℂ] A) (_ : principalLevelFrame.IsEqvA ρ π Ψ ∧ LinearMap.range Ψ ≤ C) => LinearMap.range Ψ) Φ ⟨hΦ, hC⟩
  have supSt : ∀ K1 K2 : Submodule ℂ A, St K1 → St K2 → St (K1 ⊔ K2) := by
    intro K1 K2 h1 h2 h x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _)]; exact Submodule.add_mem_sup (h1 h a ha) (h2 h b hb)
  have atom : ∀ K : Submodule ℂ A, St K → ∀ Φ : π.S →ₗ[ℂ] A, principalLevelFrame.IsEqvA ρ π Φ →
      LinearMap.range Φ ≤ K ∨ ∀ f, Φ f ∈ K → f = 0 := by
    intro K hK Φ hΦ
    rcases π.irr ((K.comap Φ).map π.S.subtype) (by
        rintro _ ⟨f, -, rfl⟩; exact f.2)
      (by
        rintro h _ ⟨f, hf, rfl⟩
        refine ⟨⟨NG.rt D.host.E n h f, π.stable h f f.2⟩, ?_, rfl⟩
        show Φ _ ∈ K
        rw [hΦ h f]; exact hK h _ hf) with h0 | h1
    · right; intro f hf
      have : (f : GAf D.host.E n → ℂ) ∈ (K.comap Φ).map π.S.subtype := ⟨f, hf, rfl⟩
      rw [h0] at this
      exact Subtype.ext ((Submodule.mem_bot ℂ).1 this)
    · left; rintro _ ⟨f, rfl⟩
      have : (f : GAf D.host.E n → ℂ) ∈ (K.comap Φ).map π.S.subtype := by rw [h1]; exact f.2
      obtain ⟨f', hf', he⟩ := this
      have : f' = f := Subtype.ext he
      subst this; exact hf'
  obtain ⟨K, hKmax⟩ := zorn_le₀ {K : Submodule ℂ A | K ≤ principalLevelFrame.isotIn (D := D) ρ C π ∧ St K ∧ y ∉ K} (by
    intro c hc hch
    rcases c.eq_empty_or_nonempty with rfl | hne
    · refine ⟨⊥, ⟨bot_le, fun h x hx => ?_, fun h => hy0 ((Submodule.mem_bot ℂ).1 h)⟩, by simp⟩
      rw [(Submodule.mem_bot ℂ).1 hx, map_zero]; exact zero_mem _
    · refine ⟨sSup c, ⟨sSup_le fun K hK => (hc hK).1, ?_, ?_⟩, fun K hK => le_sSup hK⟩
      · intro h x hx
        have : sSup c ≤ (sSup c).comap (ρ h) := sSup_le fun K hK z hz => le_sSup hK ((hc hK).2.1 h z hz)
        exact this hx
      · intro hyc
        obtain ⟨K, hK, hyK⟩ := (Submodule.mem_sSup_of_directed hne hch.directedOn).1 hyc
        exact (hc hK).2.2 hyK)
  obtain ⟨⟨hKN, hKSt, hyK⟩, hKm⟩ := hKmax
  have grow : ∀ K' : Submodule ℂ A, K' ≤ principalLevelFrame.isotIn (D := D) ρ C π → St K' → K ≤ K' → ¬ K' ≤ K → y ∈ K' :=
    fun K' h1 h2 h3 h4 => by
      by_contra hyK'; exact h4 (hKm ⟨h1, h2, hyK'⟩ h3)
  obtain ⟨Φ, ⟨hΦ, hΦC⟩, hΦK⟩ : ∃ Φ : π.S →ₗ[ℂ] A, (principalLevelFrame.IsEqvA ρ π Φ ∧ LinearMap.range Φ ≤ C) ∧
      ¬ LinearMap.range Φ ≤ K := by
    by_contra hcon
    push_neg at hcon
    exact hyK ((iSup₂_le fun Φ hΦ => hcon Φ hΦ : principalLevelFrame.isotIn (D := D) ρ C π ≤ K) hy)
  have hΦK' : ∀ f, Φ f ∈ K → f = 0 := (atom K hKSt Φ hΦ).resolve_left hΦK
  have hyK2 : y ∈ K ⊔ LinearMap.range Φ := grow _ (sup_le hKN (rangeLe Φ hΦ hΦC))
    (supSt _ _ hKSt (rangeSt Φ hΦ)) le_sup_left (fun h => hΦK (le_sup_right.trans h))
  have hN2 : principalLevelFrame.isotIn (D := D) ρ C π ≤ K ⊔ LinearMap.range Φ := by
    refine iSup₂_le fun Φ' hΦ' => ?_
    by_contra hnot
    have h3 := (atom _ (supSt _ _ hKSt (rangeSt Φ hΦ)) Φ' hΦ'.1).resolve_left hnot
    have hyK3 : y ∈ K ⊔ LinearMap.range Φ' := grow _ (sup_le hKN (rangeLe Φ' hΦ'.1 hΦ'.2))
      (supSt _ _ hKSt (rangeSt Φ' hΦ'.1)) le_sup_left
      (fun h => hnot ((le_sup_right.trans h).trans le_sup_left))
    obtain ⟨k, hk, _, ⟨f', rfl⟩, hsum⟩ := Submodule.mem_sup.1 hyK3
    have hf' : f' = 0 := h3 f' (by
      have : Φ' f' = y - k := by rw [← hsum]; abel
      rw [this]; exact Submodule.sub_mem _ hyK2 (Submodule.mem_sup_left hk))
    apply hyK; rw [← hsum, hf', map_zero, add_zero]; exact hk
  let Ψ : (K × π.S) →ₗ[ℂ] A := K.subtype.coprod Φ
  have hΨ : Function.Injective Ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨k, f⟩ h0
    simp only [Ψ, LinearMap.coprod_apply, Submodule.subtype_apply] at h0
    have hneg : Φ f = -(k : A) := eq_neg_iff_add_eq_zero.2 (by rw [add_comm]; exact h0)
    have hf : f = 0 := hΦK' f (by rw [hneg]; exact K.neg_mem k.2)
    subst hf
    rw [map_zero, add_zero] at h0
    have hk : k = 0 := Subtype.ext h0
    subst hk; rfl
  let E := LinearEquiv.ofInjective Ψ hΨ
  let q0 : LinearMap.range Ψ →ₗ[ℂ] π.S := (LinearMap.snd ℂ K π.S).comp E.symm.toLinearMap
  obtain ⟨g, hg⟩ := LinearMap.exists_extend q0
  have hq0 : ∀ (k : K) (f : π.S), g (k + Φ f) = f := by
    intro k f
    have hmem : (k : A) + Φ f ∈ LinearMap.range Ψ := ⟨(k, f), rfl⟩
    have h1 := LinearMap.congr_fun hg ⟨_, hmem⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1]
    have h2 : (⟨_, hmem⟩ : LinearMap.range Ψ) = E (k, f) := Subtype.ext (by simp only [E, LinearEquiv.ofInjective_apply]; rfl)
    show (E.symm _).2 = f
    rw [h2, LinearEquiv.symm_apply_apply]
  have dec : ∀ z ∈ principalLevelFrame.isotIn (D := D) ρ C π, ∃ (k : K) (f : π.S), z = k + Φ f := by
    intro z hz
    obtain ⟨a, ha, _, ⟨f, rfl⟩, rfl⟩ := Submodule.mem_sup.1 (hN2 hz)
    exact ⟨⟨a, ha⟩, f, rfl⟩
  refine ⟨π.S.subtype ∘ₗ g, ?_, ?_⟩
  · obtain ⟨k, f, rfl⟩ := dec y hy
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, hq0]
    intro hf
    have : f = 0 := Subtype.ext hf
    subst this
    apply hyK; rw [map_zero, add_zero]; exact k.2
  · intro z hz
    obtain ⟨k, f, rfl⟩ := dec z hz
    refine ⟨by simp [hq0], fun h => ?_⟩
    have : ρ h ((k : A) + Φ f) = ((⟨ρ h k, hKSt h k k.2⟩ : K) : A) + Φ ⟨NG.rt D.host.E n h f, π.stable h f f.2⟩ := by
      rw [map_add (f := _), hΦ h f]
    have e1 := hq0 ⟨ρ h k, hKSt h k k.2⟩ ⟨NG.rt D.host.E n h f, π.stable h f f.2⟩
    have e2 := hq0 k f
    rw [this, LinearMap.comp_apply, LinearMap.comp_apply, e1, e2]
    rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedFieldFibres
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.DetFibre

section Periods

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

end Periods

section Marks

open GlobalTheory.CharRead

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

theorem det_cong_of_finCong (V : HSp D) (N : ℕ) (hN : N ≠ 0) (u : GA D V) (hu : FinCong V N u) :
    ∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
        ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
          (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (N : ℕ) • w := by
  obtain ⟨k1, -, k3, k4, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V
  exact det_cong_one D.host.F (latC V) k3 k4 N hN (finHom V u).1 (by rw [← k1]; exact hu)





end Marks


end GlobalTheory.DetFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCompletionSymmContinuous
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ringEquiv_symm_continuous_of_continuous {K₁ K₂ : Type*} [NormedField K₁] [NormedField K₂]
    (i : K₁ ≃+* K₂) (hi : Continuous i) (hπ : ∃ π : K₁, 0 < ‖π‖ ∧ ‖π‖ < 1) :
    Continuous i.symm := by

  have small : ∀ δ : ℝ, 0 < δ → ∃ a : K₁, a ≠ 0 ∧ ‖a‖ < δ := by
    intro δ hδ
    obtain ⟨π, hπ0, hπ1⟩ := hπ
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hπ1
    exact ⟨π ^ n, pow_ne_zero _ (norm_pos_iff.mp hπ0), by rwa [norm_pow]⟩

  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ x : K₁, ‖x‖ < δ → ‖i x‖ < 1 := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.mp hi 0 1 one_pos
    refine ⟨δ, hδ, fun x hx => ?_⟩
    have := h x (by simpa [dist_eq_norm] using hx)
    simpa [dist_eq_norm] using this

  have key : ∀ y : K₁, ‖i y‖ < 1 → ‖y‖ < 1 := by
    intro y hy
    by_contra hge
    push_neg at hge
    have hy0 : y ≠ 0 := by
      rintro rfl
      norm_num at hge
    have hiy : 0 < ‖i y‖ := norm_pos_iff.mpr ((map_ne_zero i).mpr hy0)
    obtain ⟨a, ha0, ha⟩ := small δ hδ
    have hia : 0 < ‖i a‖ := norm_pos_iff.mpr ((map_ne_zero i).mpr ha0)
    have hgt : 1 < ‖i y‖⁻¹ := (one_lt_inv₀ hiy).mpr hy
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖i a‖⁻¹) hgt
    have hsmall : ‖a * y⁻¹ ^ n‖ < δ := by
      rw [norm_mul, norm_pow, norm_inv]
      have h1 : ‖y‖⁻¹ ^ n ≤ 1 := pow_le_one₀ (inv_nonneg.mpr (norm_nonneg _)) (inv_le_one_of_one_le₀ hge)
      calc ‖a‖ * ‖y‖⁻¹ ^ n ≤ ‖a‖ * 1 := by gcongr
        _ < δ := by simpa using ha
    have h2 := hball _ hsmall
    rw [map_mul, map_pow, map_inv₀, norm_mul, norm_pow, norm_inv] at h2
    have h3 : ‖i a‖ * ‖i a‖⁻¹ < ‖i a‖ * ‖i y‖⁻¹ ^ n := mul_lt_mul_of_pos_left hn hia
    rw [mul_inv_cancel₀ hia.ne'] at h3
    linarith

  have zero : ∀ ε > 0, ∃ η > 0, ∀ w : K₂, ‖w‖ < η → ‖i.symm w‖ < ε := by
    intro ε hε
    obtain ⟨a, ha0, ha⟩ := small ε hε
    have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    have hia : 0 < ‖i a‖ := norm_pos_iff.mpr ((map_ne_zero i).mpr ha0)
    refine ⟨‖i a‖, hia, fun w hw => ?_⟩
    have h1 : ‖i (i.symm w * a⁻¹)‖ < 1 := by
      rw [map_mul, map_inv₀, RingEquiv.apply_symm_apply, norm_mul, norm_inv, mul_inv_lt_iff₀ hia]
      simpa using hw
    have h2 := key _ h1
    rw [norm_mul, norm_inv, mul_inv_lt_iff₀ ha'] at h2
    linarith
  rw [Metric.continuous_iff]
  intro b ε hε
  obtain ⟨η, hη, h⟩ := zero ε hε
  refine ⟨η, hη, fun z hz => ?_⟩
  rw [dist_eq_norm] at hz ⊢
  rw [← map_sub]
  exact h _ hz

theorem GlobalTheory.splitCompletion_symm_continuous : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i → (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) → Continuous i.symm := by
  intro L _ _ _ s i hi _
  obtain ⟨π, hπ⟩ := s.v.valuation_exists_uniformizer (maximalRealSubfield L)
  have hv : Valued.v (π : s.v.adicCompletion (maximalRealSubfield L)) = WithZero.exp (-1 : ℤ) := by
    simpa using hπ
  refine ringEquiv_symm_continuous_of_continuous i hi ⟨(π : s.v.adicCompletion (maximalRealSubfield L)), ?_, ?_⟩
  · refine norm_pos_iff.mpr fun h => ?_
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · rw [Valued.toNormedField.norm_lt_one_iff, hv, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalMemIntegralPointsOfLatticeStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalMemIntegralPointsOfLatticeStabilizer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.InertKU

theorem compAt_mem_tensInt (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {z : AL L} (hz : z ∈ ALint L) :
    compAt L v z ∈ Formalism.UG.tensInt (F := maximalRealSubfield L)
      (v.adicCompletion (maximalRealSubfield L)) (Formalism.UG.intOE L)
      (Formalism.UG.Ov (maximalRealSubfield L) v) := by
  have key : ALint L ≤ (Formalism.UG.tensInt (F := maximalRealSubfield L)
      (v.adicCompletion (maximalRealSubfield L)) (Formalism.UG.intOE L)
      (Formalism.UG.Ov (maximalRealSubfield L) v)).comap (compAt L v) := by
    rw [ALint, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · apply Subring.subset_closure
      left
      refine ⟨⟨(y : L), y, rfl⟩, ?_⟩
      rw [GlobalTheory.InertUmax.compAt_tmul]
      rfl
    · apply Subring.subset_closure
      right
      refine ⟨⟨a v, ha v⟩, ?_⟩
      rw [GlobalTheory.InertUmax.compAt_tmul]
  exact key hz

theorem mem_range_bc_of_entries {K : Type} [Field K] (S : Subring K) {n : ℕ} (g : GL (Fin n) K)
    (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ S)
    (hg' : ∀ i j, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ S) :
    g ∈ (Formalism.UG.bc (n := Fin n) S.subtype).range := by
  let M : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, hg i j⟩
  let M' : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, hg' i j⟩
  have hM : (RingHom.mapMatrix S.subtype) M = (g : Matrix (Fin n) (Fin n) K) := rfl
  have hM' : (RingHom.mapMatrix S.subtype) M' = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
  have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) S.subtype) := by
    intro A B h
    ext i j
    exact congrFun (congrFun h i) j
  have h1 : M * M' = 1 := inj (by rw [map_mul, map_one, hM, hM']; exact Units.mul_inv g)
  have h2 : M' * M = 1 := inj (by rw [map_mul, map_one, hM, hM']; exact Units.inv_mul g)
  refine ⟨⟨M, M', h1, h2⟩, ?_⟩
  ext i j
  rfl

theorem loc_inv (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x : GAf L n) : Dv.loc x⁻¹ = (Dv.loc x)⁻¹ := by
  unfold InertDatum.loc
  simp only [InvMemClass.coe_inv, map_inv]
  group

theorem loc_entries_mem (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (y : GAf L n) (hy : y ∈ Umax L n) (i j : Fin n) :
    ((Dv.loc y : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j
      ∈ Formalism.UG.intL (w.adicCompletion L) := by
  have hP := GlobalTheory.InertUmax.entries_mem_of_range _ _ Dv.Pint
  have hP' := GlobalTheory.InertUmax.entries_mem_of_range _ _ (inv_mem Dv.Pint)
  have hE : ∀ l k, ((Formalism.UG.bc (n := Fin n)
      (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
      (Matrix.GeneralLinearGroup.map (compAt L v) (y : GL (Fin n) (AL L))) : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) (w.adicCompletion L)) l k ∈ Formalism.UG.intL (w.adicCompletion L) :=
    fun l k => (Dv.integ _).1 (compAt_mem_tensInt L v (hy l k))
  unfold InertDatum.loc
  simp only [Units.val_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _
    (Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hP' i l) (hE l k)) (hP k j)

theorem loc_mem_KU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (x : GAf L n), x ∈ Umax L n → ∀ hg : Dv.loc x ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc x, hg⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n := by
  intro L _ _ _ n v w Dv x hx hg
  rw [Formalism.UG.KU, Subgroup.mem_subgroupOf]
  refine ⟨hg, ?_⟩
  apply mem_range_bc_of_entries
  · exact loc_entries_mem L n v w Dv x hx
  · intro i j
    rw [← loc_inv]
    exact loc_entries_mem L n v w Dv x⁻¹ (inv_mem hx) i j

end GlobalTheory.InertKU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalMemIntegralPointsOfLatticeStabilizerStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertLocal_mem_integralPoints_of_latticeStabilizer : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (x : GAf L n), x ∈ Umax L n → ∀ hg : Dv.loc x ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc x, hg⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n := by
  first | exact @GlobalTheory.InertKU.loc_mem_KU | exact GlobalTheory.InertKU.loc_mem_KU | (intros; apply GlobalTheory.InertKU.loc_mem_KU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeFunIAddSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeFunIAddSmul
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Formalism.UG

namespace GlobalTheory.InertHeckeAdd

open Classical in
theorem heckeFunI_add_smul : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h₁ h₂ : Formalism.UG.GU Dv.σw n → ℂ), h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → ∀ (c : ℂ) (f : GAf L n → W), heckeFunI L n U Dv (h₁ + h₂) f = heckeFunI L n U Dv h₁ f + heckeFunI L n U Dv h₂ f ∧ heckeFunI L n U Dv (c • h₁) f = c • heckeFunI L n U Dv h₁ f := by
  intro L _ _ _ n v w Dv U hU W _ _ h h' hh hh' c f
  have hfin : ∀ k ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n,
      (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval k (Dv.loc x) ≠ 0} := fun k hk =>
    GlobalTheory.SatInd.CosetFin.finite_inert_support L n v w Dv (GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram)
      (GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv) U hU k hk
  have hsupp : ∀ k ∈ Hecke ℂ (KU Dv.σw n), ∀ (φ : GAf L n → W) (g : GAf L n),
      (Function.support (fun c : GAf L n ⧸ U =>
        if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
          Dv.hval k (Dv.loc hc.choose) • φ (g * hc.choose) else 0)).Finite := by
    intro k hk φ g
    refine (hfin k hk).subset ?_
    intro c hc
    simp only [Function.mem_support] at hc
    split_ifs at hc with h1
    · refine ⟨h1.choose, h1.choose_spec.1, h1.choose_spec.2, ?_⟩
      intro h0
      rw [h0, zero_smul] at hc
      exact hc rfl
    · exact absurd rfl hc
  have hadd : ∀ y, Dv.hval (h + h') y = Dv.hval h y + Dv.hval h' y := by
    intro y; unfold InertDatum.hval; split_ifs <;> simp
  have hsmul : ∀ y, Dv.hval (c • h) y = c * Dv.hval h y := by
    intro y; unfold InertDatum.hval; split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · funext g
    simp only [heckeFunI, Pi.add_apply]
    rw [← finsum_add_distrib (hsupp h hh f g) (hsupp h' hh' f g)]
    refine finsum_congr fun c => ?_
    split_ifs <;> simp [hadd, add_smul]
  · funext g
    simp only [heckeFunI, Pi.smul_apply]
    rw [_root_.smul_finsum' c (hsupp h hh f g)]
    refine finsum_congr fun c => ?_
    split_ifs <;> simp [hsmul, mul_smul]

end GlobalTheory.InertHeckeAdd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeFunIAddSmulStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeFunI_add_and_smul : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h₁ h₂ : Formalism.UG.GU Dv.σw n → ℂ), h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → ∀ (c : ℂ) (f : GAf L n → W), heckeFunI L n U Dv (h₁ + h₂) f = heckeFunI L n U Dv h₁ f + heckeFunI L n U Dv h₂ f ∧ heckeFunI L n U Dv (c • h₁) f = c • heckeFunI L n U Dv h₁ f := by
  first | exact @GlobalTheory.InertHeckeAdd.heckeFunI_add_smul | exact GlobalTheory.InertHeckeAdd.heckeFunI_add_smul | (intros; apply GlobalTheory.InertHeckeAdd.heckeFunI_add_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalMemUnitaryGroupAntidiagonalForm
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalMemUnitaryGroupAntidiagonalForm
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalUnitary

theorem compAt_conjAL (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (a : AL L) :
    compAt L v (conjAL L a) = Formalism.UG.sigR (↑(IsCMField.complexConj L))
      (HeightOneSpectrum.adicCompletion (maximalRealSubfield L) v) (compAt L v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [compAt, conjAL, Formalism.UG.sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem cT_mul {A : Type} [CommRing A] (σ : A →+* A) {m : Type} [Fintype m]
    (M N : Matrix m m A) : Formalism.UG.cT σ (M * N) = Formalism.UG.cT σ N * Formalism.UG.cT σ M := by
  unfold Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one {A : Type} [CommRing A] (σ : A →+* A) {m : Type} [Fintype m] [DecidableEq m] :
    Formalism.UG.cT σ (1 : Matrix m m A) = 1 := by
  unfold Formalism.UG.cT
  simp

theorem cT_conj_form {A : Type} [CommRing A] (σ : A →+* A) {m : Type} [Fintype m] [DecidableEq m]
    (Pm Pi X : Matrix m m A) (h1 : Pm * Pi = 1) (hX : Formalism.UG.cT σ X * X = 1) :
    Formalism.UG.cT σ (Pi * X * Pm) * (Formalism.UG.cT σ Pm * Pm) * (Pi * X * Pm) = Formalism.UG.cT σ Pm * Pm := by
  have h2 : Formalism.UG.cT σ Pi * Formalism.UG.cT σ Pm = 1 := by
    rw [← cT_mul, h1, cT_one]
  rw [cT_mul, cT_mul]
  calc _ = Formalism.UG.cT σ Pm * (Formalism.UG.cT σ X * ((Formalism.UG.cT σ Pi * Formalism.UG.cT σ Pm) * ((Pm * Pi) * X))) * Pm := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ Pm * Pm := by
        rw [h1, h2, Matrix.one_mul, Matrix.one_mul, hX, Matrix.mul_one]

theorem mem_UJ_iff {A : Type} [CommRing A] {m : Type} [Fintype m] [DecidableEq m] (σ : A →+* A)
    (J : Matrix m m A) (g : GL m A) : g ∈ Formalism.UG.UJ σ J ↔ Formalism.UG.cT σ (g : Matrix m m A) * J * g = J := Iff.rfl

theorem loc_mem_GU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x : GAf L n), Dv.loc x ∈ Formalism.UG.GU Dv.σw n := by
  intro L _ _ _ n v w Dv x
  let φ : AL L →+* HeightOneSpectrum.adicCompletion L w :=
    (Dv.e : _ →+* HeightOneSpectrum.adicCompletion L w).comp (compAt L v)
  have hφ : ∀ a : AL L, φ (conjAL L a) = Dv.σw (φ a) := by
    intro a
    simp only [φ, RingHom.comp_apply, RingHom.coe_coe, compAt_conjAL, Dv.comm]
  have hx : ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ReciprocityTheory.Aut.conjT (conjAL L) (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := x.2
  have hconj : φ.mapMatrix (ReciprocityTheory.Aut.conjT (conjAL L)
      ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) =
      Formalism.UG.cT Dv.σw (φ.mapMatrix ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, ReciprocityTheory.Aut.conjT, Formalism.UG.cT,
      Matrix.transpose_apply, hφ]
  have hX : φ.mapMatrix ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      Formalism.UG.cT Dv.σw (φ.mapMatrix ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) = 1 := by
    rw [← hconj, ← map_mul, hx, map_one]
  have hX' := mul_eq_one_comm.mp hX
  have hloc : ((Dv.loc x : GL (Fin n) (HeightOneSpectrum.adicCompletion L w)) :
      Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletion L w)) =
      ((Dv.P⁻¹ : GL (Fin n) (HeightOneSpectrum.adicCompletion L w)) :
        Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletion L w)) *
      φ.mapMatrix ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ((Dv.P : GL (Fin n) (HeightOneSpectrum.adicCompletion L w)) :
        Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletion L w)) := by
    rw [Formalism.AUTREP.InertDatum.loc, Units.val_mul, Units.val_mul]
    congr 2
  rw [mem_UJ_iff, hloc, ← Dv.Panti]
  exact cT_conj_form Dv.σw _ _ _ (by simp) hX'

end GlobalTheory.LocalUnitary
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalMemUnitaryGroupAntidiagonalFormStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertLocal_mem_unitaryGroup_antidiagonalForm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (x : GAf L n), Dv.loc x ∈ Formalism.UG.GU Dv.σw n := by
  first | exact @GlobalTheory.LocalUnitary.loc_mem_GU | exact GlobalTheory.LocalUnitary.loc_mem_GU | (intros; apply GlobalTheory.LocalUnitary.loc_mem_GU <;> assumption)
end
end

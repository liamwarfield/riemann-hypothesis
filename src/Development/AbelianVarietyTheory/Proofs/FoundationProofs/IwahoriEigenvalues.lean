module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IwahoriEigenvaluesOfNewton
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EqZeroOrSingleOfDegreeLtTwo
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromISlashChangeOfVariables
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumMulCosetRepresentativeTraceEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IwahoriEigenvalues
namespace GlobalTheory.IwahoriEigenObj

theorem iwahoriEigenvalues : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.IwahoriEigenvalues :=
  GlobalTheory.IwahoriEigen.iwahoriEigenvalues

end GlobalTheory.IwahoriEigenObj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAlgebrasOverHenselianAndComplete
noncomputable section

namespace GlobalTheory

open IsLocalRing TensorProduct

universe u

open WithConv in
theorem _root_.GlobalTheory.bialgHom_map_antipode {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [HopfAlgebra R A] [HopfAlgebra R B] (g : A →ₐc[R] B) (a : A) :
    g (HopfAlgebra.antipode R a) = HopfAlgebra.antipode R (g a) := by
  have h1 := LinearMap.algHom_comp_convMul_distrib (g : A →ₐ[R] B)
    (toConv (HopfAlgebra.antipode R)) (toConv LinearMap.id)
  have h2 := LinearMap.convMul_comp_coalgHom_distrib (toConv LinearMap.id)
    (toConv (HopfAlgebra.antipode R)) (g : A →ₗc[R] B)
  have e1 : (g : A →ₐ[R] B).toLinearMap ∘ₗ ofConv (1 : WithConv (A →ₗ[R] A)) =
      ofConv (1 : WithConv (A →ₗ[R] B)) := by
    ext x
    simp only [LinearMap.convOne_def]
    exact (g : A →ₐ[R] B).commutes _
  have e2 : ofConv (1 : WithConv (B →ₗ[R] B)) ∘ₗ (g : A →ₗc[R] B).toLinearMap =
      ofConv (1 : WithConv (A →ₗ[R] B)) := by
    ext x
    simp [LinearMap.convOne_def]
  rw [LinearMap.antipode_mul_id, e1] at h1
  rw [LinearMap.id_mul_antipode, e2] at h2
  have h := left_inv_eq_right_inv (ofConv_injective h1).symm (ofConv_injective h2).symm
  simpa using congrArg (fun f : WithConv (A →ₗ[R] B) ↦ (ofConv f) a) h

theorem _root_.GlobalTheory.henselianLocalRing_of_isAdicComplete (R : Type*) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] : HenselianLocalRing R :=
  _root_.GlobalTheory.henselianLocalRing_of_henselianRing R

theorem _root_.GlobalTheory.exists_etale_henselian_lift_of_isSeparable (R : Type u) (L : Type*) [CommRing R]
    [HenselianLocalRing R] [Field L] [Algebra (ResidueField R) L]
    [Module.Finite (ResidueField R) L] [Algebra.IsSeparable (ResidueField R) L] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧ Algebra.Etale R A ∧
      HenselianLocalRing A ∧ Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] L) := by
  obtain ⟨A, _, _, hfin, het, hloc, he⟩ := _root_.GlobalTheory.exists_etale_lift_of_isSeparable R L
  exact ⟨A, inferInstance, inferInstance, hfin, het, _root_.GlobalTheory.henselianLocalRing_of_finite R A, he⟩

open CategoryTheory in
theorem _root_.GlobalTheory.finite_algebras_over_henselian (R : Type u) [CommRing R] [HenselianLocalRing R] :
    (∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S],
      (∃ (ι : Type u) (_ : Finite ι) (T : ι → Type u) (_ : ∀ i, CommRing (T i))
        (_ : ∀ i, Algebra R (T i)) (_ : S ≃ₐ[R] Π i, T i),
        ∀ i, HenselianLocalRing (T i) ∧ Module.Finite R (T i)) ∧
      ∀ c : S ⧸ (maximalIdeal R).map (algebraMap R S), IsIdempotentElem c →
        ∃! e : S, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = c) ∧
    (CommAlgCat.FiniteEtale.baseChange.{u} R (ResidueField R)).IsEquivalence ∧
    ∀ (L : Type u) [Field L] [Algebra (ResidueField R) L] [Module.Finite (ResidueField R) L]
      [Algebra.IsSeparable (ResidueField R) L],
      ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Module.Finite R A ∧ Algebra.Etale R A ∧
        HenselianLocalRing A ∧ Nonempty (ResidueField R ⊗[R] A ≃ₐ[ResidueField R] L) := by
  refine ⟨fun S _ _ _ ↦ ⟨_root_.GlobalTheory.exists_algEquiv_pi_henselianLocalRing R S,
    fun c hc ↦ _root_.GlobalTheory.existsUnique_idempotent_lift_quotient R hc⟩, ?_,
    fun L _ _ _ _ ↦ _root_.GlobalTheory.exists_etale_henselian_lift_of_isSeparable R L⟩
  refine
    { faithful := ⟨fun {X Y} f g h ↦ ?_⟩
      full := ⟨fun {X Y} φ ↦ ?_⟩
      essSurj := ⟨fun Y ↦ ?_⟩ }
  · have : Algebra.Etale R X.obj := X.property.2
    have : Module.Finite R Y.obj := Y.property.1
    exact ObjectProperty.hom_ext _ (CommAlgCat.hom_ext
      ((_root_.GlobalTheory.bijective_baseChange_residueField_of_etale R X.obj Y.obj).1
        (congrArg (fun φ ↦ φ.hom.hom) h)))
  · have : Algebra.Etale R X.obj := X.property.2
    have : Module.Finite R Y.obj := Y.property.1
    obtain ⟨f, hf⟩ := (_root_.GlobalTheory.bijective_baseChange_residueField_of_etale R X.obj Y.obj).2 φ.hom.hom
    exact ⟨ObjectProperty.homMk (CommAlgCat.ofHom f),
      ObjectProperty.hom_ext _ (CommAlgCat.hom_ext hf)⟩
  · have : Algebra.Etale (ResidueField R) Y.obj := Y.property.2
    obtain ⟨A, _, _, hfin, het, ⟨e⟩⟩ := _root_.GlobalTheory.exists_etale_lift_of_etale.{u, u} R Y.obj
    exact ⟨⟨CommAlgCat.of R A, ⟨hfin, het⟩⟩, ⟨ObjectProperty.isoMk _ (CommAlgCat.isoMk e)⟩⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsExpEqOfSubstLg
open MvPowerSeries ReciprocityTheory.PGsh

namespace GlobalTheory.FGDepth

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

private theorem jacobian_logFGL_lg_eq_one {d : ℕ} (G : LogFGL v d) :
    FormalSeries.jacobian G.lg = 1 := by
  ext i j
  rw [FormalSeries.jacobian_apply, G.lg_lin i j, Matrix.one_apply]

private theorem exists_subst_inverse_logFGL_lg {d : ℕ} (G : LogFGL v d) :
    ∃ w : Fin d → MvPowerSeries (Fin d) C, (∀ j, constantCoeff (w j) = 0) ∧
      (∀ i, subst w (G.lg i) = X i) ∧ ∀ j, subst G.lg (w j) = X j :=
  FormalSeries.exists_subst_inverse G.lg_const (B := 1)
    (by rw [jacobian_logFGL_lg_eq_one, Matrix.mul_one]) (by rw [jacobian_logFGL_lg_eq_one, Matrix.one_mul])

theorem isExp_expOf {d : ℕ} (G : LogFGL v d) : IsExp G (expOf G) := by
  obtain ⟨w, hw0, hw1, -⟩ := exists_subst_inverse_logFGL_lg G
  exact Classical.epsilon_spec (p := IsExp G) ⟨w, hw0, hw1⟩

theorem isExp_eq_of_subst_lg {d : ℕ} (G : LogFGL v d) {w : Fin d → MvPowerSeries (Fin d) C}
    (h2 : ∀ j, subst G.lg (w j) = X j) {e : Fin d → MvPowerSeries (Fin d) C} (he : IsExp G e) :
    e = w := by
  obtain ⟨he0, he1⟩ := he
  have hlg : HasSubst G.lg := hasSubst_of_constantCoeff_zero G.lg_const
  have hes : HasSubst e := hasSubst_of_constantCoeff_zero he0
  funext j
  calc e j = subst e (X j : MvPowerSeries (Fin d) C) := (subst_X hes j).symm
    _ = subst e (subst G.lg (w j)) := by rw [h2 j]
    _ = subst (fun s => subst e (G.lg s)) (w j) := subst_comp_subst_apply hlg hes (w j)
    _ = subst (X : Fin d → MvPowerSeries (Fin d) C) (w j) := by simp only [he1]
    _ = w j := by rw [subst_self]; rfl

theorem isExp_unique {d : ℕ} (G : LogFGL v d) {e : Fin d → MvPowerSeries (Fin d) C}
    (he : IsExp G e) : e = expOf G := by
  obtain ⟨w, -, -, hw2⟩ := exists_subst_inverse_logFGL_lg G
  rw [isExp_eq_of_subst_lg G hw2 he, isExp_eq_of_subst_lg G hw2 (isExp_expOf G)]

theorem subst_lg_expOf {d : ℕ} (G : LogFGL v d) (a : Fin d) :
    subst G.lg (expOf G a) = (X a : MvPowerSeries (Fin d) C) := by
  obtain ⟨w, -, -, hw2⟩ := exists_subst_inverse_logFGL_lg G
  rw [isExp_eq_of_subst_lg G hw2 (isExp_expOf G)]
  exact hw2 a

theorem expOf_spec {d : ℕ} (G : LogFGL v d) :
    IsExp G (expOf G) ∧ (∀ e, IsExp G e → e = expOf G) ∧
      ∀ a, subst G.lg (expOf G a) = (X a : MvPowerSeries (Fin d) C) :=
  ⟨isExp_expOf G, fun _ he => isExp_unique G he, subst_lg_expOf G⟩

end GlobalTheory.FGDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergIntertwiningSumsCompEqIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergIntertwiningSumsCompEqIndex
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem _root_.GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul : ∀ {R X M : Type} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
    {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W →
    ∀ (A B : Submodule R X), _root_.GlobalTheory.FinWeil.SelfDual γ A → _root_.GlobalTheory.FinWeil.SelfDual γ B →
    _root_.GlobalTheory.FinWeil.idx A B ≠ 0 →
    _root_.GlobalTheory.FinWeil.idx B A = _root_.GlobalTheory.FinWeil.idx A B ∧
      ∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v →
        _root_.GlobalTheory.FinWeil.sumOp W B A (_root_.GlobalTheory.FinWeil.sumOp W A B v) =
          (_root_.GlobalTheory.FinWeil.idx A B : ℂ) • v := by
  intro R X M _ _ _ _ _ σ w γ W hW A B hA hB hAB
  obtain ⟨hidx, -, hsum⟩ := _root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW B.toAddSubgroup A.toAddSubgroup
    A.toAddSubgroup B.toAddSubgroup (fun a _ => hB a)
    (fun t _ => (hA t).trans (forall₂_congr fun a _ =>
      ⟨hW.swap_eq_one, hW.swap_eq_one⟩)) hAB
  refine ⟨hidx, fun v hv => ?_⟩
  have hfinB : (A.toAddSubgroup.addSubgroupOf B.toAddSubgroup).FiniteIndex := ⟨hAB⟩
  have hfinA : (B.toAddSubgroup.addSubgroupOf A.toAddSubgroup).FiniteIndex := by
    refine ⟨?_⟩
    change B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0
    rw [hidx]; exact hAB
  letI := Fintype.ofFinite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)
  letI := Fintype.ofFinite (A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup)
  unfold _root_.GlobalTheory.FinWeil.sumOp
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [finsum_eq_sum_of_fintype, map_sum] at hsum ⊢
  have hcomm : ∀ a ∈ A, ∀ b : X, W a (W b v) = γ a b • W b v := by
    intro a ha b
    rw [hW.comm, hv a ha]
  calc ∑ q : A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup,
        ∑ p : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup,
          W (Quotient.out q).1 (W (Quotient.out p).1 v)
      = ∑ p : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup,
          (∑ q : A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup,
            γ (Quotient.out q).1 (Quotient.out p).1) • W (Quotient.out p).1 v := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun q _ => hcomm _ (Quotient.out q).2 _
    _ = ∑ p : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup,
          if p = 0 then (_root_.GlobalTheory.FinWeil.idx A B : ℂ) • v else 0 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hsum _ (Quotient.out p).2]
        have hmem : (Quotient.out p).1 ∈ A.toAddSubgroup ↔ p = 0 := by
          conv_rhs => rw [← QuotientAddGroup.out_eq' p]
          rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
        by_cases hp : p = 0
        · rw [if_pos (hmem.2 hp), if_pos hp, hv _ (hmem.2 hp)]
          exact congrArg (fun n : ℕ => (n : ℂ) • v) hidx
        · rw [if_neg (mt hmem.1 hp), if_neg hp, zero_smul]
    _ = (_root_.GlobalTheory.FinWeil.idx A B : ℂ) • v := by
        rw [Finset.sum_ite_eq']
        simp

end GlobalTheory.FinWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergIntertwiningSumsCompEqIndexStatement
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_intertwining_sums_comp_eq_index : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ A → SelfDual γ B → idx A B ≠ 0 → idx B A = idx A B ∧ ∀ v, Fixes W A v → sumOp W B A (sumOp W A B v) = (idx A B : ℂ) • v := by
  first | exact @GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul | exact GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul | (intros; apply GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanHeisenbergTranslatesVacuumEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanHeisenbergTranslatesVacuumEqTop
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem span_translates_vacuum : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ A : Submodule R X, SelfDual γ A → ∀ e : M, (∀ v, Fixes W A v → ∃ c : ℂ, v = c • e) → (∀ v : M, ∃ T : Submodule R X, idx A T ≠ 0 ∧ ∀ a ∈ A, (∀ t ∈ T, γ a t = 1) → W a v = v) → Submodule.span ℂ (Set.range fun x => W x e) = ⊤ := by
  intro R X M _ _ _ _ _ σ w γ W h A hA e he hsm
  rw [eq_top_iff]
  intro v _
  obtain ⟨T, hT, hv⟩ := hsm v
  let S : Submodule R X :=
    { carrier := {a | a ∈ A ∧ ∀ t ∈ T, γ a t = 1}
      add_mem' := fun {a b} ha hb => ⟨A.add_mem ha.1 hb.1, fun t ht => by
        rw [h.add_left, ha.2 t ht, hb.2 t ht, mul_one]⟩
      zero_mem' := ⟨A.zero_mem, fun t _ => h.zero_left t⟩
      smul_mem' := fun r a ha => ⟨A.smul_mem r ha.1, fun t ht => by
        rw [h.adj]; exact ha.2 _ (T.smul_mem _ ht)⟩ }
  have hSm : ∀ a, a ∈ S ↔ a ∈ A ∧ ∀ t ∈ T, γ a t = 1 := fun a => Iff.rfl
  have hSv : Fixes W S v := fun a ha => hv a ha.1 ha.2
  have hSt : ∀ t ∈ T, Fixes W S (W (-t) v) := by
    intro t ht a ha
    rw [h.comm, ha.2 _ (T.neg_mem ht), one_smul, hSv a ha]
  obtain ⟨h1, -, -⟩ := perfect_pairing_quotients h S.toAddSubgroup A.toAddSubgroup
    A.toAddSubgroup T.toAddSubgroup
    (fun a ha => ⟨fun hs => hs.2, fun hs => ⟨ha, hs⟩⟩)
    (fun t _ => ⟨fun ht a ha => h.iso hA ha ht,
      fun ht => (hA t).2 fun a ha => h.swap_eq_one (ht a ha)⟩) hT
  have hn : idx S A ≠ 0 := by
    unfold idx
    rw [h1]
    exact hT
  obtain ⟨-, -, h2⟩ := perfect_pairing_quotients h A.toAddSubgroup T.toAddSubgroup
    S.toAddSubgroup A.toAddSubgroup
    (fun t _ => hA t)
    (fun a ha => ⟨fun hs t ht => h.swap_eq_one (hs.2 t ht),
      fun hs => ⟨ha, fun t ht => h.swap_eq_one (hs t ht)⟩⟩) hn
  obtain ⟨t1, t2, -⟩ := sumOp_transversal h S A hA
  obtain ⟨⟨m, f, hf, hu⟩, hfix, -⟩ := t2 hn
  have hg : ∀ t ∈ T, ∑ i, γ t (f i) • W (f i) v ∈ Submodule.span ℂ (Set.range fun x => W x e) := by
    intro t ht
    obtain ⟨c, hc⟩ := he _ (hfix _ (hSt t ht))
    rw [(t1 _ (hSt t ht) _ f hf hu).1] at hc
    have h3 := congrArg (W t) hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_smul] at h3
    have h4 : ∀ i, W t (W (f i) (W (-t) v)) = γ (w • t) (-t) • (γ t (f i) • W (f i) v) := by
      intro i
      rw [h.comm, h.comp t (-t), add_neg_cancel, h.zero, map_smul, smul_comm]
    rw [Finset.sum_congr rfl fun i _ => h4 i, ← Finset.smul_sum] at h3
    rw [← Submodule.smul_mem_iff _ (h.ne_zero (w • t) (-t)), h3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  haveI : Finite (T.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf T.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero hT
  letI := Fintype.ofFinite (T.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf T.toAddSubgroup)
  have h5 := Submodule.sum_mem (Submodule.span ℂ (Set.range fun x => W x e))
    (t := (Finset.univ : Finset
      (T.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf T.toAddSubgroup)))
    (fun q _ => hg _ (Quotient.out q : T.toAddSubgroup).2)
  rw [Finset.sum_comm] at h5
  obtain ⟨i₀, hi₀, hi⟩ := hu 0 A.zero_mem
  simp only [zero_sub, neg_mem_iff] at hi₀ hi
  have h6 : ∀ i, ∑ q : T.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf T.toAddSubgroup,
      γ ((Quotient.out q : T.toAddSubgroup) : X) (f i) • W (f i) v
      = if i = i₀ then (idx A T : ℂ) • v else 0 := by
    intro i
    rw [← Finset.sum_smul, ← finsum_eq_sum_of_fintype, h2 _ (hf i)]
    by_cases hii : i = i₀
    · subst hii
      rw [if_pos rfl, if_pos (show f i ∈ S.toAddSubgroup from hi₀), hSv _ hi₀]
      rfl
    · rw [if_neg hii, if_neg (fun hh : f i ∈ S.toAddSubgroup => hii (hi i hh)), zero_smul]
  rw [Finset.sum_congr rfl fun i _ => h6 i, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)] at h5
  exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 hT)).1 h5

end GlobalTheory.FinWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanHeisenbergTranslatesVacuumEqTopStatement
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_heisenberg_translates_vacuum_eq_top : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ A : Submodule R X, SelfDual γ A → ∀ e : M, (∀ v, Fixes W A v → ∃ c : ℂ, v = c • e) → (∀ v : M, ∃ T : Submodule R X, idx A T ≠ 0 ∧ ∀ a ∈ A, (∀ t ∈ T, γ a t = 1) → W a v = v) → Submodule.span ℂ (Set.range fun x => W x e) = ⊤ := by
  first | exact @GlobalTheory.FinWeil.span_translates_vacuum | exact GlobalTheory.FinWeil.span_translates_vacuum | (intros; apply GlobalTheory.FinWeil.span_translates_vacuum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntPrimeDivRootOfUnitySubOnePow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntPrimeDivRootOfUnitySubOnePow
open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.K5.PDiv

open Polynomial

theorem prod_one_sub_pow_dvd {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    (ζ : Ω) (hζ : IsIntegral (O0 p) ζ) (S : Finset Ω) (hS : ∀ μ ∈ S, ∃ i : ℕ, ζ ^ i = μ) :
    ∃ c : Ω, IsIntegral (O0 p) c ∧ ∏ μ ∈ S, (1 - μ) = (ζ - 1) ^ S.card * c := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, isIntegral_one, by simp⟩
  | insert a S ha ih =>
    obtain ⟨c, hc, e⟩ := ih (fun μ hμ => hS μ (Finset.mem_insert_of_mem hμ))
    obtain ⟨i, rfl⟩ := hS _ (Finset.mem_insert_self _ _)
    refine ⟨-(∑ k ∈ Finset.range i, ζ ^ k) * c, ?_, ?_⟩
    · refine IsIntegral.mul (IsIntegral.neg ?_) hc
      have : (∑ k ∈ Finset.range i, ζ ^ k) ∈ integralClosure (O0 p) Ω :=
        Subalgebra.sum_mem _ fun k _ => Subalgebra.pow_mem _ hζ k
      exact this
    · rw [Finset.prod_insert ha, e, Finset.card_insert_of_notMem ha, pow_succ]
      have g := geom_sum_mul ζ i
      linear_combination ((ζ - 1) ^ S.card * c) * g

theorem pdiv : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    ∀ (T : Tower p Ω) (j s : ℕ), 1 ≤ j → s ≤ Nat.totient (p ^ j) →
      IsInt (p := p) ((p : Ω) / (T.ζ j - 1) ^ s) := by
  intro p _ Ω _ _ T j s hj hs
  classical
  have hprim := T.prim j
  have hpos : 0 < p ^ j := pow_pos (Fact.out : p.Prime).pos j
  have hζ : IsIntegral (O0 p) (T.ζ j) := ⟨X ^ (p ^ j) - C 1, monic_X_pow_sub_C 1 hpos.ne', by simp [hprim.pow_eq_one]⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hne : T.ζ (j' + 1) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact hprim.ne_one (Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt)
  have hp : (p : Ω) = ∏ μ ∈ primitiveRoots (p ^ (j' + 1)) Ω, (1 - μ) := by
    rw [← eval_one_cyclotomic_prime_pow (R := Ω) j', cyclotomic_eq_prod_X_sub_primitiveRoots hprim,
      eval_prod]
    simp
  obtain ⟨c, hc, e⟩ := prod_one_sub_pow_dvd (T.ζ (j' + 1)) hζ (primitiveRoots (p ^ (j' + 1)) Ω)
    (fun μ hμ => by
      have hμ' := (mem_primitiveRoots hpos).1 hμ
      obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hμ'.pow_eq_one
      exact ⟨i, hi⟩)
  rw [hprim.card_primitiveRoots] at e
  have key : (p : Ω) / (T.ζ (j' + 1) - 1) ^ s =
      (T.ζ (j' + 1) - 1) ^ (Nat.totient (p ^ (j' + 1)) - s) * c := by
    rw [div_eq_iff (pow_ne_zero _ hne), hp, e, mul_right_comm, ← pow_add, Nat.sub_add_cancel hs]
  rw [IsInt, key]
  exact IsIntegral.mul (IsIntegral.pow (IsIntegral.sub hζ isIntegral_one) _) hc

end GlobalTheory.K5.PDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntPrimeDivRootOfUnitySubOnePowStatement
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (j s : ℕ), 1 ≤ j → s ≤ Nat.totient (p ^ j) → IsInt (p := p) ((p : Ω) / (T.ζ j - 1) ^ s) := by
  first | exact @GlobalTheory.K5.PDiv.pdiv | exact GlobalTheory.K5.PDiv.pdiv | (intros; apply GlobalTheory.K5.PDiv.pdiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitIndexAddIntVector
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitIndexAddIntVector
noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.Sieg.Model

namespace GlobalTheory.Sieg.Per

def qp (q u : ℂ) : ℂ := ∏' m : ℕ, (1 - q ^ (m + 1) * u)

theorem multipliable_qp {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) : Multipliable fun m : ℕ => 1 - q ^ (m + 1) * u := by
  have hs : Summable fun m : ℕ => ‖-(q ^ (m + 1) * u)‖ := by
    simp only [norm_neg, norm_mul, norm_pow, pow_succ]
    exact ((summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right _).mul_right _
  simpa [sub_eq_add_neg] using multipliable_one_add_of_summable hs

theorem qp_shift {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) : qp q u = (1 - q * u) * qp q (q * u) := by
  have e : (fun m : ℕ => 1 - q ^ (m + 1 + 1) * u) = fun m : ℕ => 1 - q ^ (m + 1) * (q * u) := by
    funext m; ring
  have h : Multipliable fun m : ℕ => (fun m : ℕ => 1 - q ^ (m + 1) * u) (m + 1) := by
    show Multipliable fun m : ℕ => 1 - q ^ (m + 1 + 1) * u
    rw [e]; exact multipliable_qp hq _
  have := tprod_eq_zero_mul' (f := fun m : ℕ => 1 - q ^ (m + 1) * u) h
  simp only [e, zero_add, pow_one] at this
  exact this

def tp (q u : ℂ) : ℂ := (1 - u) * qp q u * qp q u⁻¹

theorem tp_shift {q u : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hu : u ≠ 0) : tp q (q * u) = -u⁻¹ * tp q u := by
  have e : q * (q * u)⁻¹ = u⁻¹ := by field_simp
  unfold tp
  rw [← qp_shift hq u, qp_shift hq (q * u)⁻¹, e]
  have : 1 - u⁻¹ = -u⁻¹ * (1 - u) := by field_simp; ring
  rw [this]; ring

theorem tp_shift_pow {q u : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hu : u ≠ 0) (k : ℕ) :
    tp q (q ^ k * u) = (-u⁻¹) ^ k * (q ^ (k.choose 2))⁻¹ * tp q u := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : q ^ (k + 1) * u = q * (q ^ k * u) := by ring
    have e2 : (k + 1).choose 2 = k + k.choose 2 := by
      rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right]
    rw [e, tp_shift hq hq0 (mul_ne_zero (pow_ne_zero _ hq0) hu), ih, e2, pow_add q, pow_succ (-u⁻¹)]
    generalize (-u⁻¹) ^ k = A
    field_simp

theorem cth_eq {q t : ℂ} (hq : ‖q‖ < 1) (c : ℕ) (h1 : ∀ m : ℕ, 1 - q ^ (m + 1) * t ^ c ≠ 0)
    (h2 : ∀ m : ℕ, 1 - q ^ (m + 1) * (t ^ c)⁻¹ ≠ 0) :
    cth c q t = q ^ ((c ^ 2 - 1) / 12) * (-t) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * (tp q t ^ (c ^ 2) / tp q (t ^ c)) := by
  have pA := (multipliable_qp hq t).hasProd
  have pB := (multipliable_qp hq t⁻¹).hasProd
  obtain ⟨C, hC, pC⟩ := hasProd_geom hq _ h1
  obtain ⟨D, hD, pD⟩ := hasProd_geom hq _ h2
  have hP : HasProd (fun m : ℕ => cthFac c q t (m + 1)) (qp q t ^ (c ^ 2) * qp q t⁻¹ ^ (c ^ 2) * (C * D)⁻¹) := by
    have := ((hasProd_pow pA (c ^ 2)).mul (hasProd_pow pB (c ^ 2))).mul (hasProd_inv (pC.mul pD) (mul_ne_zero hC hD))
    simpa only [cthFac, div_eq_mul_inv, qp] using this
  have eC : qp q (t ^ c) = C := pC.tprod_eq
  have eD : qp q (t ^ c)⁻¹ = D := pD.tprod_eq
  unfold cth tp
  rw [hP.tprod_eq, eC, eD]
  simp only [div_eq_mul_inv, mul_inv, mul_pow]
  ring

theorem expo (c : ℕ) : ((c : ℤ) - (c : ℤ) ^ 2) / 2 = -((c.choose 2 : ℕ) : ℤ) := by
  have h : (c : ℤ) - (c : ℤ) ^ 2 = 2 * -((c.choose 2 : ℕ) : ℤ) := by
    induction c with
    | zero => simp
    | succ k ih =>
      have e2 : (k + 1).choose 2 = k + k.choose 2 := by
        rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right]
      rw [e2]; push_cast; linarith
  rw [h]; exact Int.mul_ediv_cancel_left _ (by norm_num)

theorem mono_shift {q t : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ht : t ≠ 0) (c : ℕ) :
    (-(q * t)) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * (tp q (q * t) ^ (c ^ 2) / tp q ((q * t) ^ c)) =
      (-t) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * (tp q t ^ (c ^ 2) / tp q (t ^ c)) := by
  have hs : (-t⁻¹) ^ (c ^ 2) = (-(t ^ c)⁻¹) ^ c := by
    have hpar : (-1 : ℂ) ^ (c ^ 2) = (-1) ^ c := by
      rcases Nat.even_or_odd c with h | h
      · rw [h.neg_one_pow, (h.pow_of_ne_zero two_ne_zero).neg_one_pow]
      · rw [h.neg_one_pow, h.pow.neg_one_pow]
    rw [neg_pow, neg_pow (t ^ c)⁻¹, hpar, ← inv_pow, ← pow_mul, sq]
  have hn : (-(t ^ c)⁻¹) ^ c ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero (pow_ne_zero _ ht)))
  have hqk : q ^ (c.choose 2) ≠ 0 := pow_ne_zero _ hq0
  have e : -(q * t) = q * -t := by ring
  rw [tp_shift hq hq0 ht, mul_pow q t c, tp_shift_pow hq hq0 (pow_ne_zero c ht), mul_pow, hs, e, mul_zpow, expo,
    zpow_neg q, zpow_natCast]
  generalize (-(t ^ c)⁻¹) ^ c = A at hn
  generalize q ^ (c.choose 2) = B at hqk
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  field_simp

theorem sg_eq {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) (τ : ℍ) :
    sg c x τ = ee τ ^ ((c ^ 2 - 1) / 12) * ((-ee (pt x τ)) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) *
      (tp (ee τ) (ee (pt x τ)) ^ (c ^ 2) / tp (ee τ) (ee (pt x τ) ^ c))) := by
  have hc : ¬ ((c • x) 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ (c • x) 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
    simpa using h.2.2
  unfold sg
  rw [cth_eq (norm_ee_lt_one τ) c (fun m => by rw [ee_pt_pow]; exact (ne_one_of_not_int hc τ (m + 1)).1)
    (fun m => by rw [ee_pt_pow]; exact (ne_one_of_not_int hc τ (m + 1)).2), mul_assoc]

theorem isAdmissibleSmoothingFactor_add_intVector {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) (n : Fin 2 → ℤ) : admitted c fun i => x i + n i := by
  refine ⟨h.1, h.2.1, ?_⟩
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  exact h.2.2 ⟨⟨a - c * n 0, by push_cast; rw [ha]; ring⟩, ⟨b - c * n 1, by push_cast; rw [hb]; ring⟩⟩

theorem sg_step {c : ℕ} {x y : Fin 2 → ℚ} (hx : admitted c x) (hy : admitted c y) (τ : ℍ) (h0 : y 0 = x 0 + 1) (h1 : y 1 = x 1) :
    sg c y τ = sg c x τ := by
  have e : ee (pt y τ) = ee τ * ee (pt x τ) := by
    rw [← ee_add]; congr 1; simp only [pt, h0, h1]; push_cast; ring
  rw [sg_eq hx, sg_eq hy, e, mono_shift (norm_ee_lt_one τ) (ee_ne_zero _) (ee_ne_zero _)]

theorem sg_fst {c : ℕ} {x : Fin 2 → ℚ} (hx : admitted c x) (τ : ℍ) (k : ℤ) :
    sg c (fun i => x i + (![k, 0] : Fin 2 → ℤ) i) τ = sg c x τ := by
  induction k using Int.induction_on with
  | zero =>
    congr 1; funext i; fin_cases i <;> simp
  | succ k ih =>
    rw [← ih]
    exact sg_step (isAdmissibleSmoothingFactor_add_intVector hx _) (isAdmissibleSmoothingFactor_add_intVector hx _) τ (by simp; ring) (by simp)
  | pred k ih =>
    rw [← ih]
    exact (sg_step (isAdmissibleSmoothingFactor_add_intVector hx _) (isAdmissibleSmoothingFactor_add_intVector hx _) τ (by simp; ring) (by simp)).symm

theorem sg_add_int : ∀ (c : ℕ) (x : Fin 2 → ℚ) (n : Fin 2 → ℤ) (τ : ℍ), admitted c x →
    sg c (fun i => x i + n i) τ = sg c x τ := by
  intro c x n τ hx
  rw [← sg_fst hx τ (n 0)]
  have e1 : ee (n 1 : ℂ) = 1 := by
    unfold ee
    rw [mul_comm]; exact Complex.exp_int_mul_two_pi_mul_I _
  unfold sg
  congr 1
  rw [← mul_one (ee (pt (fun i => x i + (![n 0, 0] : Fin 2 → ℤ) i) τ)), ← e1, ← ee_add]
  congr 1
  simp [pt]; ring

end GlobalTheory.Sieg.Per
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitIndexAddIntVectorStatement
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedSiegelUnit_index_add_intVector : ∀ (c : ℕ) (x : Fin 2 → ℚ) (n : Fin 2 → ℤ) (τ : ℍ), admitted c x → sg c (fun i => x i + n i) τ = sg c x τ := by
  first | exact @GlobalTheory.Sieg.Per.sg_add_int | exact GlobalTheory.Sieg.Per.sg_add_int | (intros; apply GlobalTheory.Sieg.Per.sg_add_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerPeriodCocycleMemCocyclesAndEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerPeriodCocycleMemCocyclesAndEq
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.PerCoc

theorem polySlash_apply (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i •
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
  simp only [slP, LinearMap.sum_apply, LinearMap.comp_apply, lcoeff_apply,
    LinearMap.toSpanSingleton_apply]

theorem homogenize_eq_sum (w : ℕ) (p : ℂ[X]) :
    p.homogenize w = ∑ i ∈ Finset.range (w + 1),
      p.coeff i • ((MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ^ i * MvPolynomial.X 1 ^ (w - i)) := by
  rw [homogenize, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [← homogenize_monomial hi', ← homogenize_X_pow hi', ← homogenize_smul, smul_X_eq_monomial]

theorem polySlash_eq_aeval (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = MvPolynomial.aeval
      ![C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ), C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)]
      (p.homogenize w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [polySlash_apply, homogenize_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_mul, map_pow, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  rfl

theorem isHomogeneous_lin (a b : ℂ) :
    (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 :=
  ((MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).C_mul a).add
    ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).C_mul b)

theorem homogenize_slP (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    (slP w g p).homogenize w = ∑ i ∈ Finset.range (w + 1), MvPolynomial.C (p.coeff i) *
      ((MvPolynomial.C ((g 0 0 : ℤ) : ℂ) * MvPolynomial.X 0 + MvPolynomial.C ((g 0 1 : ℤ) : ℂ) * MvPolynomial.X 1) ^ i *
        (MvPolynomial.C ((g 1 0 : ℤ) : ℂ) * MvPolynomial.X 0 +
          MvPolynomial.C ((g 1 1 : ℤ) : ℂ) * MvPolynomial.X 1) ^ (w - i)) := by
  apply homogenize_eq_of_isHomogeneous
  · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i hi => ?_
    have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h := (((isHomogeneous_lin ((g 0 0 : ℤ) : ℂ) ((g 0 1 : ℤ) : ℂ)).pow i).mul
      ((isHomogeneous_lin ((g 1 0 : ℤ) : ℂ) ((g 1 1 : ℤ) : ℂ)).pow (w - i))).C_mul (p.coeff i)
    rwa [one_mul, one_mul, Nat.add_sub_of_le hi'] at h
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [polySlash_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, map_pow, map_add (f := _), MvPolynomial.aeval_C, MvPolynomial.aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_one, ← C_eq_algebraMap, smul_eq_C_mul]

theorem polySlash_polySlash (w : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w h (slP w g p) = slP w (g * h) p := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [polySlash_eq_aeval w h, homogenize_slP, polySlash_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, map_pow, map_add (f := _), MvPolynomial.aeval_C, MvPolynomial.aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, ← C_eq_algebraMap, smul_eq_C_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add,
      Int.cast_mul]
  congr 3 <;> ring

theorem polySlash_mem_degreeLT (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p ∈ degreeLT ℂ (w + 1) := by
  rw [polySlash_apply]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [mem_degreeLT]
  refine lt_of_le_of_lt degree_le_natDegree ?_
  have h1 : ∀ a b : ℂ, (C a * X + C b).natDegree ≤ 1 := fun a b => natDegree_linear_le
  have h2 := natDegree_mul_le_of_le (natDegree_pow_le_of_le i (h1 ((g 0 0 : ℤ) : ℂ) ((g 0 1 : ℤ) : ℂ)))
    (natDegree_pow_le_of_le (w - i) (h1 ((g 1 0 : ℤ) : ℂ) ((g 1 1 : ℤ) : ℂ)))
  rw [mul_one, mul_one, Nat.add_sub_of_le hi'] at h2
  exact_mod_cast Nat.lt_succ_of_le h2

theorem eichler_I (w : ℕ) (f : ℍ → ℂ) : eichler w f UpperHalfPlane.I = 0 := by
  simp [eichler]

theorem slash_eq_self {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f : ModularForm Γ k) (γ : Γ) :
    (⇑f) ∣[k] (γ : SL(2, ℤ)) = ⇑f := by
  rw [ModularForm.SL_slash]
  exact f.slash_action_eq' _ ⟨γ, γ.2, rfl⟩

theorem per_eq (Γ : Subgroup SL(2, ℤ)) (k : ℕ) (hk : 2 ≤ k) (f : ModularForm Γ (k : ℤ)) (γ : Γ) (τ : ℍ) :
    per Γ (k - 2) ⇑f γ =
      slP (k - 2) (mat γ) (eichler (k - 2) ⇑f ((γ : SL(2, ℤ)) • τ)) - eichler (k - 2) ⇑f τ := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.eichlerIntegralFromI_slash_change_of_variables k hk ⇑f f.holo' γ
  rw [slash_eq_self] at hc
  rw [per, hc, hc, eichler_I]
  ring

theorem per_mem_Z1_and_eq_slP_eichler_sub : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 2 ≤ k → ∀ f : ModularForm Γ (k : ℤ),
    per Γ (k - 2) ⇑f ∈ Z1 Γ (k - 2) ∧ ∀ (γ : Γ) (τ : ℍ), per Γ (k - 2) ⇑f γ =
      slP (k - 2) (mat γ) (eichler (k - 2) ⇑f ((γ : SL(2, ℤ)) • τ)) - eichler (k - 2) ⇑f τ := by
  intro Γ k hk f
  refine ⟨⟨fun γ => polySlash_mem_degreeLT _ _ _, fun γ δ => ?_⟩, per_eq Γ k hk f⟩
  rw [per_eq Γ k hk f γ ((δ : SL(2, ℤ)) • UpperHalfPlane.I), map_sub, polySlash_polySlash]
  simp only [per, mat, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, mul_smul]
  ring

end GlobalTheory.HeckeFamilyMatrices.PerCoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerPeriodCocycleMemCocyclesAndEqStatement
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eichlerPeriodCocycle_mem_cocycles_and_eq : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 2 ≤ k → ∀ f : ModularForm Γ (k : ℤ), per Γ (k - 2) ⇑f ∈ Z1 Γ (k - 2) ∧ ∀ (γ : Γ) (τ : ℍ), per Γ (k - 2) ⇑f γ = slP (k - 2) (mat γ) (eichler (k - 2) ⇑f ((γ : SL(2, ℤ)) • τ)) - eichler (k - 2) ⇑f τ := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.PerCoc.per_mem_Z1_and_eq_slP_eichler_sub | exact GlobalTheory.HeckeFamilyMatrices.PerCoc.per_mem_Z1_and_eq_slP_eichler_sub | (intros; apply GlobalTheory.HeckeFamilyMatrices.PerCoc.per_mem_Z1_and_eq_slP_eichler_sub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletedLaurentQuotPrimeEquivLaurentFp
open GlobalTheory.K5

namespace GlobalTheory.K5

noncomputable def lauRed (p : ℕ) [Fact p.Prime] : Lau p →+* LaurentSeries (ZMod p) where
  toFun x := HahnSeries.map x (PadicInt.toZMod (p := p))
  map_one' := HahnSeries.map_one (PadicInt.toZMod (p := p)).toMonoidWithZeroHom
  map_mul' x y := HahnSeries.map_mul (PadicInt.toZMod (p := p)).toNonUnitalRingHom
  map_zero' := by ext n; simp
  map_add' x y := by ext n; simp

theorem lauRed_coeff (p : ℕ) [Fact p.Prime] (x : Lau p) (n : ℤ) :
    (lauRed p x).coeff n = PadicInt.toZMod (x.coeff n) := rfl

theorem lauRed_surjective (p : ℕ) [Fact p.Prime] : Function.Surjective (lauRed p) := by
  intro y
  refine ⟨HahnSeries.map y (⟨fun a => ((ZMod.val a : ℕ) : ℤ_[p]), by simp⟩ : ZeroHom (ZMod p) ℤ_[p]), ?_⟩
  ext n
  rw [lauRed_coeff]
  show PadicInt.toZMod ((ZMod.val (y.coeff n) : ℕ) : ℤ_[p]) = _
  simp

theorem ker_lauRed (p : ℕ) [Fact p.Prime] : RingHom.ker (lauRed p) = pI p := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have h : ∀ n, ∃ c : ℤ_[p], x.coeff n = (p : ℤ_[p]) * c := by
      intro n
      have h1 : x.coeff n ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
        rw [RingHom.mem_ker, ← lauRed_coeff, hx]; rfl
      rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
      exact h1
    choose c hc using h
    have hp : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    refine Ideal.mem_span_singleton.2 ⟨⟨c, x.isPWO_support.mono ?_⟩, ?_⟩
    · intro n hn
      rw [HahnSeries.mem_support, hc n]
      exact mul_ne_zero hp hn
    · ext n
      rw [← nsmul_eq_mul, HahnSeries.coeff_nsmul, hc n]
      simp
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show lauRed p _ = 0
    rw [map_natCast]
    ext n
    rw [← Nat.smul_one_eq_cast, HahnSeries.coeff_nsmul]
    simp

theorem exists_completedLaurent_quot_prime_equiv_laurentFp (p : ℕ) [Fact p.Prime] : ∃ e : (O0 p ⧸ Ideal.span {(p : O0 p)}) ≃+* LaurentSeries (ZMod p),
    e (Ideal.Quotient.mk _ (qO p)) = HahnSeries.single (1 : ℤ) (1 : ZMod p) := by
  have fg : (pI p).FG := Submodule.fg_span_singleton _
  have hker := AdicCompletion.ker_evalOneₐ_eq_map (pI p) fg
  have hsurj : Function.Surjective (AdicCompletion.evalOneₐ (pI p)) := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨algebraMap _ _ a, (AdicCompletion.evalOneₐ (pI p)).commutes a⟩
  have hmap : (pI p).map (algebraMap (Lau p) (O0 p)) = Ideal.span {(p : O0 p)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have h1 : Ideal.span {(p : O0 p)} = RingHom.ker (AdicCompletion.evalOneₐ (pI p)).toRingHom := by
    rw [← hmap]; exact hker.symm
  refine ⟨(Ideal.quotEquivOfEq h1).trans
    ((RingHom.quotientKerEquivOfSurjective (f := (AdicCompletion.evalOneₐ (pI p)).toRingHom) hsurj).trans
      ((Ideal.quotEquivOfEq (ker_lauRed p).symm).trans
        (RingHom.quotientKerEquivOfSurjective (lauRed_surjective p)))), ?_⟩
  simp only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  have hq : (AdicCompletion.evalOneₐ (pI p)).toRingHom (qO p) =
      Ideal.Quotient.mk (pI p) (HahnSeries.single (1 : ℤ) (1 : ℤ_[p])) :=
    (AdicCompletion.evalOneₐ (pI p)).commutes _
  rw [hq, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  ext n
  rw [lauRed_coeff]
  by_cases hn : n = 1
  · subst hn; simp
  · simp [HahnSeries.coeff_single_of_ne hn]

end GlobalTheory.K5
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionNeZero
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem sg_ne_zero : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), admitted c x → sg c x τ ≠ 0 :=
  fun _ _ τ h => (GlobalTheory.Sieg.Model.multipliable_and_sg_ne_zero h τ).2.2

end GlobalTheory.Sieg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationOnAdjoinMemSpanImage
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationOnAdjoinMemSpanImage
open GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

theorem derOn_adjoin_mem_span : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module S M] (s : Set S) (D : S → M), IsDerOn (Algebra.adjoin A s) D →
    ∀ x ∈ Algebra.adjoin A s, D x ∈ Submodule.span S (D '' s) := by
  intro A S M _ _ _ _ _ s D hD x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | algebraMap r => rw [hD.alg]; exact zero_mem _
  | add x y hx hy ihx ihy => rw [hD.add x hx y hy]; exact add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
    rw [hD.mul x hx y hy]
    exact add_mem (Submodule.smul_mem _ _ ihy) (Submodule.smul_mem _ _ ihx)

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationOnAdjoinMemSpanImageStatement
open GlobalTheory.AlmostEt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationOn_adjoin_mem_span_image : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M] (s : Set S) (D : S → M), IsDerOn (Algebra.adjoin A s) D → ∀ x ∈ Algebra.adjoin A s, D x ∈ Submodule.span S (D '' s) := by
  first | exact @GlobalTheory.AlmostEt.derOn_adjoin_mem_span | exact GlobalTheory.AlmostEt.derOn_adjoin_mem_span | (intros; apply GlobalTheory.AlmostEt.derOn_adjoin_mem_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorPreservesModularFormGamma1InterGamma0
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem isBoundedAt_finsetSum {ι : Type*} (s : Finset ι) (c : OnePoint ℝ) (k : ℤ) {F : ι → ℍ → ℂ}
    (h : ∀ i ∈ s, c.IsBoundedAt (F i) k) : c.IsBoundedAt (∑ i ∈ s, F i) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g _
    rw [Finset.sum_empty, SlashAction.zero_slash]
    exact zero_form_isBoundedAtImInfty
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem uOp_modularForm : ∀ (N l q : ℕ) (k : ℤ), 0 < N → 0 < l → q.Prime → q ∣ N * l →
    ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, ∃ g : ModularForm (GlobalTheory.Hk.lev N l) k,
      ⇑g = GlobalTheory.Hk.uOp q ⇑f := by
  intro N l q k hN hl hq hqd f
  have hq0 : 0 < q := hq.pos
  have hinv : ∀ γ ∈ lev N l, (⇑f) ∣[k] γ = ⇑f := fun γ hγ => by
    rw [SL_slash]; exact f.slash_action_eq' _ ⟨γ, hγ, rfl⟩
  have hU := GlobalTheory.T.heckeUOperatorExplicit_slash_invariant_gamma1InterGamma0 N l q k (⇑f) hN hl hq hqd hinv
  refine ⟨{ toFun := uOp q ⇑f
            slash_action_eq' := ?_
            holo' := (GlobalTheory.T.mdifferentiable_heckeOperatorsExplicit q k 1 (⇑f) hq0 f.holo').1
            bdd_at_cusps' := ?_ }, rfl⟩
  · intro γ hγ
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hγ
    have := hU s hs
    rw [SL_slash] at this
    exact this
  · intro c hc
    rw [GlobalTheory.T.heckeUOperatorExplicit_eq_sum_slash q k (⇑f) hq0]
    exact isBoundedAt_finsetSum _ c k fun j _ => GlobalTheory.T.slash_rat_isBoundedAt_gamma1InterGamma0Level N l k _ hN hl (by
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two_of]; exact_mod_cast hq0) f c hc

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CountSpanSingletonRingEquiv
open IsDedekindDomain Polynomial
open scoped nonZeroDivisors

namespace GlobalTheory.OrdTransport

theorem count_spanSingleton_ringEquiv : ∀ (A F : Type) [CommRing A] [IsDedekindDomain A] [Field F]
    [Algebra A F] [IsFractionRing A F] (τ : A ≃+* A) (σ : F ≃+* F),
    (∀ a : A, σ (algebraMap A F a) = algebraMap A F (τ a)) → ∀ v w : HeightOneSpectrum A,
    (∀ a : A, a ∈ v.asIdeal ↔ τ a ∈ w.asIdeal) → ∀ x : F, x ≠ 0 →
    FractionalIdeal.count F w (FractionalIdeal.spanSingleton A⁰ (σ x)) =
      FractionalIdeal.count F v (FractionalIdeal.spanSingleton A⁰ x) := by
  intro A F _ _ _ _ _ τ σ hc v w hvw x hx
  have h : v.asIdeal = w.asIdeal.comap τ := Ideal.ext fun a => by
    rw [Ideal.mem_comap]; exact hvw a
  have hv : v.valuation F x = w.valuation F (σ x) := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    rw [map_div₀ σ, hc, hc, map_div₀, map_div₀]
    simp only [HeightOneSpectrum.valuation_of_algebraMap,
      GlobalTheory.QNorm.intValuation_of_eq_comap τ w v h]
  have hσx : σ x ≠ 0 := (map_ne_zero σ).2 hx
  rw [GlobalTheory.Idele.valuation_eq_exp_neg_count v hx, GlobalTheory.Idele.valuation_eq_exp_neg_count w hσx,
    WithZero.exp_inj, neg_inj] at hv
  exact hv.symm

end GlobalTheory.OrdTransport
end

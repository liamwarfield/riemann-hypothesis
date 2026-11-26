module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemPullback
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperPullbackSystemQuasicoherent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobsonIdealFaithfulModule

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperBirationalClosedSystem
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardSystemAffineSections
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardSystemAffineSections
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Chart

attribute [local instance] algebraOfOver

variable {X Z : Scheme.{0}}

theorem idealPowι_comp_pullback_map_cokernel_eq_zero {A : Type} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X)
    (hφ : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) (E : X.Modules) (D : Subobject E) (m : ℕ)
    (hD : powSub I E m ≤ D) :
    idealPowι I ((Scheme.Modules.pullback φ).obj E) m ≫
      (Scheme.Modules.pullback φ).map (cokernel.π D.arrow) = 0 := by
  apply (cancel_epi (Abelian.factorThruImage
    (idealSumMap ((Scheme.Modules.pullback φ).obj E) (I ^ m)))).1
  rw [comp_zero, ← Category.assoc, Abelian.image.fac]
  apply biproduct.hom_ext'
  intro k
  rw [comp_zero, idealSumMap, biproduct.ι_desc_assoc, GroundTheory.Arith.SchemeCoh.smulHom_comp, ← appTop_algebraMap φ hφ,
    ← pullback_map_smulHom_appTop, ← Functor.map_comp, ← GroundTheory.Arith.SchemeCoh.smulHom_comp]
  obtain ⟨L, hL⟩ := exists_smulHom_eq_comp_idealSumMap E (I ^ m) (idealGen_mem (I ^ m) k)
  have hι : idealPowι I E m ≫ cokernel.π D.arrow = 0 := by
    have h := Subobject.ofMkLE_arrow (f := idealPowι I E m) (X := D) hD
    rw [← h, Category.assoc, cokernel.condition, comp_zero]
  rw [hL, ← Abelian.image.fac (idealSumMap E (I ^ m)), Category.assoc, Category.assoc, hι,
    comp_zero, comp_zero, Functor.map_zero]

theorem chartIn_of_pullback_app_eq_zero (φ : Z ⟶ X) {E : X.Modules} [E.IsQuasicoherent]
    (D : Subobject E) [(D : X.Modules).IsQuasicoherent] (V : X.Opens) (hV : IsAffineOpen V)
    (x : Γ(E, V))
    (hx : ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ φ ⁻¹ᵁ V,
      ((Scheme.Modules.pullback φ).map (cokernel.π D.arrow)).app U
        (GlobalTheory.QCoh.pullbackSections φ E h x) = 0) :
    ChartIn φ V (secsSub D V) x := by
  intro U hU h
  letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
  have hx' := hx U hU h
  rw [GlobalTheory.QCoh.pullback_map_app_pullbackSections] at hx'
  letI := GlobalTheory.QCoh.appLEModule φ ((Scheme.Modules.pullback φ).obj (cokernel D.arrow)) h
  haveI := GlobalTheory.QCoh.appLE_isScalarTower φ ((Scheme.Modules.pullback φ).obj (cokernel D.arrow)) h
  have hbc := GlobalTheory.QCoh.isBaseChange_pullbackSections φ (cokernel D.arrow) hU hV h
  let πl : Γ(E, V) →ₗ[Γ(X, V)] Γ(cokernel D.arrow, V) :=
    { toFun := (cokernel.π D.arrow).app V
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  have hsurj : Function.Surjective πl := surjective_cokernel_π_app D.arrow hV
  have hex : Function.Exact (secsSub D V).subtype πl := by
    intro m
    have hm : m ∈ Set.range (secsSub D V).subtype ↔ m ∈ Set.range (D.arrow.app V) := by
      rw [Submodule.coe_subtype, Subtype.range_coe_subtype]
      rfl
    rw [hm, mem_range_app_iff D.arrow hV m]
    rfl
  have hex' := rTensor_exact Γ(Z, U) hex hsurj
  refine (hex' _).1 ?_
  rw [LinearMap.rTensor_tmul]
  have h1 : (1 : Γ(Z, U)) ⊗ₜ[Γ(X, V)] πl x = 0 := by
    apply hbc.equiv.injective
    rw [hbc.equiv_tmul, one_smul, map_zero]
    exact hx'
  rw [← TensorProduct.comm_tmul, h1, map_zero]

theorem chartIn_adjKer : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}}
    [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X),
    φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E →
    ∀ {S : ℕ → Subobject E}, ClosedSys I E S →
    ∀ (B : Subobject ((Scheme.Modules.pullback φ).obj E)),
    (∀ e, B ⊔ powSub I _ (e + 1) = pullSys I φ E S e) → ∀ (V : X.Opens), IsAffineOpen V →
    ∀ x ∈ secs (adjKer φ B) V, ∀ n, ChartIn φ V (secsSub (S n) V) x := by
  intro A _ _ I X Z _ _ _ φ hφ E hE S hS B hB V hV x hx n
  have : E.IsQuasicoherent := hE.1
  have : ((S n : Subobject E) : X.Modules).IsQuasicoherent := hS.qcoh n
  apply chartIn_of_pullback_app_eq_zero φ (S n) V hV x
  intro U hU h
  obtain ⟨y, rfl⟩ := hx
  set g := (Scheme.Modules.pullback φ).map (cokernel.π (S n).arrow) with hg
  have hK : pullSys I φ E S n ≤ kernelSubobject g := by
    change imageSubobject ((Scheme.Modules.pullback φ).map (S n).arrow) ⊔
      powSub I _ (n + 1) ≤ kernelSubobject g
    refine sup_le (image_le_kernel _ _ ?_) (le_kernelSubobject _ _ ?_)
    · rw [hg, ← Functor.map_comp, cokernel.condition, Functor.map_zero]
    · rw [powSub, ← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc,
        idealPowι_comp_pullback_map_cokernel_eq_zero I φ hφ E (S n) (n + 1) (hS.pow_le n),
        comp_zero]
  have hBle : B ≤ kernelSubobject g := by
    rw [← hB n] at hK
    exact le_sup_left.trans hK
  have hBg : B.arrow ≫ g = 0 := by
    rw [← Subobject.ofLE_arrow hBle, Category.assoc, kernelSubobject_arrow_comp, comp_zero]
  have h0 : (adjMap φ B).app V ((adjKer φ B).arrow.app V y) = 0 := by
    have hk : (adjKer φ B).arrow ≫ adjMap φ B = 0 := kernelSubobject_arrow_comp _
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, hk]
    rfl
  have h1 : (cokernel.π B.arrow).app (φ ⁻¹ᵁ V)
      (((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app E).app V
        ((adjKer φ B).arrow.app V y)) = 0 := by
    rw [adjMap, Adjunction.homEquiv_unit] at h0
    exact h0
  have hfac : g = cokernel.π B.arrow ≫ cokernel.desc B.arrow g hBg := (cokernel.π_desc _ _ _).symm
  have h2 : (cokernel.π B.arrow).app U
      (GlobalTheory.QCoh.pullbackSections φ E h ((adjKer φ B).arrow.app V y)) = 0 := by
    rw [GlobalTheory.QCoh.pullbackSections_apply]
    erw [GlobalTheory.QCoh.hom_app_res (cokernel.π B.arrow) h]
    rw [h1, map_zero]
  rw [hfac, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, h2, map_zero]

end GlobalTheory.CompanionTheory.GE.Chart
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardSystemAffineSectionsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushforward_system_affine_sections : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X), φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → ∀ (B : Subobject ((Scheme.Modules.pullback φ).obj E)), (∀ e, B ⊔ powSub I _ (e + 1) = pullSys I φ E S e) → ∀ (V : X.Opens), IsAffineOpen V → ∀ x ∈ secs (adjKer φ B) V, ∀ n, ChartIn φ V (secsSub (S n) V) x := by
  first | exact @GlobalTheory.CompanionTheory.GE.Chart.chartIn_adjKer | exact GlobalTheory.CompanionTheory.GE.Chart.chartIn_adjKer | (intros; apply GlobalTheory.CompanionTheory.GE.Chart.chartIn_adjKer <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompleteModuleNoetherianRealization
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompleteModuleNoetherianRealization
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.CompletionTower

open AdicCompletion

variable {B : Type} [CommRing B] (I : Ideal B) {N : Type} [AddCommGroup N] [Module B N]

theorem exists_eval_smul (r : AdicCompletion I B) (x : AdicCompletion I N) (n : ℕ) :
    ∃ b : B, eval I N n (r • x) = b • eval I N n x := by
  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (r.val n)
  exact ⟨b, by show (r • x).val n = b • x.val n; rw [smul_eval, ← hb]; rfl⟩

theorem finite_adicCompletion [Module.Finite B N] :
    Module.Finite (AdicCompletion I B) (AdicCompletion I N) :=
  Module.Finite.of_surjective (ofTensorProduct I N) (ofTensorProduct_surjective_of_finite I N)

theorem span_range_of [Module.Finite B N] :
    Submodule.span (AdicCompletion I B) (Set.range (of I N)) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x ↦ ?_
  obtain ⟨t, rfl⟩ := ofTensorProduct_surjective_of_finite I N x
  induction t with
  | tmul a e =>
    rw [ofTensorProduct_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy

variable {I} (T : ℕ → Submodule B N) (hT : ∀ n, I ^ (n + 1) • (⊤ : Submodule B N) ≤ T n)

noncomputable def toQuot (n : ℕ) : AdicCompletion I N →ₗ[B] N ⧸ T n :=
  Submodule.factor (hT n) ∘ₗ eval I N (n + 1)

theorem toQuot_of (n : ℕ) (e : N) : toQuot T hT n (of I N e) = (T n).mkQ e := by
  simp [toQuot, eval_of, Submodule.factor_mk]

theorem toQuot_mk (n : ℕ) (f : AdicCauchySequence I N) :
    toQuot T hT n (AdicCompletion.mk I N f) = (T n).mkQ (f (n + 1)) := by
  show Submodule.factor (hT n) ((AdicCompletion.mk I N f).val (n + 1)) = _
  rw [mk_apply_coe, Submodule.factor_mk]

noncomputable def Tb (n : ℕ) : Submodule (AdicCompletion I B) (AdicCompletion I N) where
  carrier := {x | toQuot T hT n x = 0}
  add_mem' {x y} hx hy := by simp_all
  zero_mem' := by simp
  smul_mem' r x hx := by
    obtain ⟨b, hb⟩ := exists_eval_smul I r x (n + 1)
    have : toQuot T hT n (r • x) = b • toQuot T hT n x := by
      simp only [toQuot, LinearMap.comp_apply, hb, map_smul]
    simp_all

theorem mem_Tb (n : ℕ) (x : AdicCompletion I N) : x ∈ Tb T hT n ↔ toQuot T hT n x = 0 := Iff.rfl

theorem antitone_of_eq_sup_pow_smul_whole_module (hT' : ∀ n, T n = T (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule B N)) : Antitone T :=
  antitone_nat_of_succ_le fun n ↦ (hT' n).symm ▸ le_sup_left

theorem exists_lift (hT' : ∀ n, T n = T (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule B N)) (n : ℕ) (e : N)
    (he : e ∈ T n) : ∃ l ∈ ⨅ m, Tb T hT m, eval I N (n + 1) l = eval I N (n + 1) (of I N e) := by
  have step : ∀ j (x : T (n + j)), ∃ y : T (n + j + 1),
      (x : N) - y ∈ I ^ (n + j + 1) • (⊤ : Submodule B N) := by
    intro j x
    have hx : (x : N) ∈ T (n + j + 1) ⊔ I ^ (n + j + 1) • (⊤ : Submodule B N) := by
      rw [← hT']; exact x.2
    obtain ⟨a, ha, c, hc, hxe⟩ := Submodule.mem_sup.1 hx
    exact ⟨⟨a, ha⟩, by rw [← hxe]; simpa using hc⟩
  choose f hf using step
  let u : (j : ℕ) → T (n + j) := fun j ↦ Nat.rec ⟨e, he⟩ (fun j x ↦ f j x) j
  have huj : ∀ j, (u (j + 1)).1 = (f j (u j)).1 := fun j ↦ rfl
  have hu : ∀ j, ((u j).1 - (u (j + 1)).1) ∈ I ^ (n + j + 1) • (⊤ : Submodule B N) := fun j ↦ by
    rw [huj]; exact hf j (u j)
  let s : ℕ → N := fun k ↦ (u (k - (n + 1))).1
  have huc : ∀ a b, a = b → (u a).1 = (u b).1 := by rintro a b rfl; rfl
  have hs0 : ∀ k, k ≤ n + 1 → s k = e := fun k hk ↦ huc _ 0 (Nat.sub_eq_zero_of_le hk)
  have hs1 : ∀ j, s (n + 1 + j) = (u j).1 := fun j ↦ huc _ _ (by omega)
  have hcau : ∀ k, s k ≡ s (k + 1) [SMOD (I ^ k • ⊤ : Submodule B N)] := by
    intro k
    rw [SModEq.sub_mem]
    rcases Nat.lt_or_ge k (n + 1) with hk | hk
    · rw [hs0 k hk.le, hs0 (k + 1) hk, sub_self]; exact zero_mem _
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [hs1, show n + 1 + j + 1 = n + 1 + (j + 1) by omega, hs1]
      simpa [show n + 1 + j = n + j + 1 by omega] using hu j
  let F : AdicCauchySequence I N := AdicCauchySequence.mk I N s hcau
  have hF : ∀ k, F k = s k := fun k ↦ rfl
  refine ⟨AdicCompletion.mk I N F, Submodule.mem_iInf _ |>.2 fun m ↦ ?_, ?_⟩
  · rw [mem_Tb, toQuot_mk, hF, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rcases Nat.lt_or_ge m n with hm | hm
    · rw [hs0 _ (by omega)]; exact antitone_of_eq_sup_pow_smul_whole_module T hT' hm.le he
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
      rw [show n + j + 1 = n + 1 + j by omega, hs1]; exact (u j).2
  · show (AdicCompletion.mk I N F).val (n + 1) = _
    rw [mk_apply_coe, eval_of, hF, hs0 _ le_rfl]

end GlobalTheory.CompanionTheory.GE.CompletionTower

namespace GlobalTheory.CompanionTheory.GE.CompletionTower

open AdicCompletion

theorem exists_completion_tower : ∀ {B : Type} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {N : Type} [AddCommGroup N] [Module B N] [Module.Finite B N] (T : ℕ → Submodule B N),
    (∀ n, I ^ (n + 1) • (⊤ : Submodule B N) ≤ T n) →
    (∀ n, T n = T (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule B N)) →
    ∃ (R : Type) (_ : CommRing R) (_ : IsNoetherianRing R) (_ : Algebra B R) (M : Type)
      (_ : AddCommGroup M) (_ : Module R M) (_ : Module B M) (_ : IsScalarTower B R M)
      (_ : Module.Finite R M) (μ : N →ₗ[B] M), I.map (algebraMap B R) ≤ Ideal.jacobson ⊥ ∧
      Submodule.span R (Set.range μ) = ⊤ ∧
      ∀ n e, e ∈ T n ↔ μ e ∈ (I ^ (n + 1) • ⊤ : Submodule B M) := by
  intro B _ _ I N _ _ _ T hT hT'
  haveI := finite_adicCompletion I (N := N)
  haveI := AdicCompletion.isAdicComplete_self I I.fg_of_isNoetherianRing
  let L : Submodule (AdicCompletion I B) (AdicCompletion I N) := ⨅ m, Tb T hT m
  let μ : N →ₗ[B] AdicCompletion I N ⧸ L := (L.mkQ.restrictScalars B) ∘ₗ of I N
  refine ⟨AdicCompletion I B, inferInstance, GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion B I,
    inferInstance, AdicCompletion I N ⧸ L, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, μ, IsAdicComplete.le_jacobson_bot _, ?_, ?_⟩
  · have : Set.range μ = L.mkQ '' Set.range (of I N) := by
      ext y; simp [μ]
    rw [this, ← Submodule.map_span, span_range_of, Submodule.map_top, Submodule.range_mkQ]
  · intro n e
    constructor
    · intro he
      obtain ⟨l, hl, hle⟩ := exists_lift T hT hT' n e he
      have hmem : of I N e - l ∈ (I ^ (n + 1) • ⊤ : Submodule B (AdicCompletion I N)) := by
        rw [AdicCompletion.pow_smul_top_eq_ker_eval I.fg_of_isNoetherianRing, LinearMap.mem_ker,
          map_sub, hle, sub_self]
      have hl0 : L.mkQ l = 0 := (Submodule.Quotient.mk_eq_zero L).2 hl
      have hμ : μ e = (L.mkQ.restrictScalars B) (of I N e - l) := by
        simp only [μ, LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_sub, hl0, sub_zero]
      have h2 := Submodule.mem_map_of_mem (f := L.mkQ.restrictScalars B) hmem
      rw [Submodule.map_smul''] at h2
      rw [hμ]
      exact Submodule.smul_mono le_rfl le_top h2
    · intro hμ
      have key : (I ^ (n + 1) • ⊤ : Submodule B (AdicCompletion I N ⧸ L)) ≤
          (LinearMap.ker (toQuot T hT n)).map (L.mkQ.restrictScalars B) := by
        rw [Submodule.smul_le]
        intro i hi m _
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective L m
        refine ⟨i • x, ?_, by simp⟩
        show toQuot T hT n (i • x) = 0
        rw [map_smul]
        obtain ⟨y, hy⟩ := Submodule.mkQ_surjective (T n) (toQuot T hT n x)
        rw [← hy, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hT n (Submodule.smul_mem_smul hi Submodule.mem_top)
      obtain ⟨x, hx, hxe⟩ := key hμ
      have hd : x - of I N e ∈ L := (Submodule.Quotient.eq L).1 hxe
      have hd' := (Submodule.mem_iInf _).1 hd n
      rw [mem_Tb, map_sub, LinearMap.mem_ker.1 hx, zero_sub, neg_eq_zero, toQuot_of,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hd'
      exact hd'

end GlobalTheory.CompanionTheory.GE.CompletionTower
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompleteModuleNoetherianRealizationStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_module_noetherian_realization : ∀ {B : Type} [CommRing B] [IsNoetherianRing B] (I : Ideal B) {N : Type} [AddCommGroup N] [Module B N] [Module.Finite B N] (T : ℕ → Submodule B N), (∀ n, I ^ (n + 1) • (⊤ : Submodule B N) ≤ T n) → (∀ n, T n = T (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule B N)) → ∃ (R : Type) (_ : CommRing R) (_ : IsNoetherianRing R) (_ : Algebra B R) (M : Type) (_ : AddCommGroup M) (_ : Module R M) (_ : Module B M) (_ : IsScalarTower B R M) (_ : Module.Finite R M) (μ : N →ₗ[B] M), I.map (algebraMap B R) ≤ Ideal.jacobson ⊥ ∧ Submodule.span R (Set.range μ) = ⊤ ∧ ∀ n e, e ∈ T n ↔ μ e ∈ (I ^ (n + 1) • ⊤ : Submodule B M) := by
  first | exact @GlobalTheory.CompanionTheory.GE.CompletionTower.exists_completion_tower | exact GlobalTheory.CompanionTheory.GE.CompletionTower.exists_completion_tower | (intros; apply GlobalTheory.CompanionTheory.GE.CompletionTower.exists_completion_tower <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperBirationalClosedSystem
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.LocTors

theorem chartIn_map {X Z : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) {N M : Type} [AddCommGroup N]
    [Module Γ(X, V) N] [AddCommGroup M] [Module Γ(X, V) M] (g : N →ₗ[Γ(X, V)] M)
    {T : Submodule Γ(X, V) N} {T' : Submodule Γ(X, V) M} (hT : T.map g ≤ T') {x : N}
    (hx : ChartIn φ V T x) : ChartIn φ V T' (g x) := by
  intro U hU h
  letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
  obtain ⟨y, hy⟩ := hx U hU h
  let g' : T →ₗ[Γ(X, V)] T' := (g.comp T.subtype).codRestrict T' (fun t => hT ⟨t, t.2, rfl⟩)
  refine ⟨g'.rTensor Γ(Z, U) y, ?_⟩
  have hc : T'.subtype.comp g' = g.comp T.subtype := rfl
  change (T'.subtype.rTensor Γ(Z, U)) (g'.rTensor Γ(Z, U) y) = g x ⊗ₜ[Γ(X, V)] (1 : Γ(Z, U))
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hc, LinearMap.rTensor_comp,
    LinearMap.comp_apply, hy, LinearMap.rTensor_tmul]

theorem eq_zero_of_mem_pow {B R M : Type} [CommRing B] [CommRing R] [IsNoetherianRing R]
    [Algebra B R] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M]
    [Module.Finite R M] (I : Ideal B) (hjac : I.map (algebraMap B R) ≤ Ideal.jacobson ⊥) (m : M)
    (hm : ∀ n, m ∈ (I ^ (n + 1) • ⊤ : Submodule B M)) : m = 0 := by
  set IR : Ideal R := I.map (algebraMap B R)
  have key : ∀ n, m ∈ (IR ^ n • ⊤ : Submodule R M) := by
    intro n
    have h1 : (I ^ (n + 1) • ⊤ : Submodule B M) ≤ (IR ^ (n + 1) • ⊤ : Submodule R M).restrictScalars B := by
      rw [Submodule.smul_le]
      intro a ha u _
      rw [Submodule.restrictScalars_mem, algebraMap_smul R a u |>.symm]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      have h2 : algebraMap B R a ∈ (I ^ (n + 1)).map (algebraMap B R) := Ideal.mem_map_of_mem _ ha
      rwa [Ideal.map_pow] at h2
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n)) (h1 (hm n))
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) IR (by simpa only [Ideal.jacobson_bot] using hjac)
  have : m ∈ (⨅ n : ℕ, IR ^ n • (⊤ : Submodule R M)) := Submodule.mem_iInf _ |>.2 key
  rw [hK] at this
  exact (Submodule.mem_bot R).1 this

theorem adjKer_pow_smul_mem_secs {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsLocallyNoetherian X] (J : X.IdealSheafData)
    {Z : Scheme.{0}} [Z.Over (Spec (.of A))] (ψ : Z ⟶ J.subscheme) (hψ : IsProper ψ)
    (hover : (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)))
    (W : J.subscheme.Opens) (hW : IsIso (ψ ∣_ W)) {E : X.Modules} (hE : IsCoherent E)
    {S : ℕ → Subobject E} (hS : ClosedSys I E S) (hK : ∀ e, Killed J (S e))
    (B : Subobject ((Scheme.Modules.pullback (ψ ≫ J.subschemeι)).obj E))
    (hB : ∀ e, B ⊔ powSub I _ (e + 1) = pullSys I (ψ ≫ J.subschemeι) E S e)
    (V : X.affineOpens) (f : Γ(X, V)) (hf : J.subschemeι ⁻¹ᵁ X.basicOpen f ≤ W)
    (x : Γ(E, V)) (hx : x ∈ secs (adjKer (ψ ≫ J.subschemeι) B) V) :
    ∃ k : ℕ, ∀ n, f ^ k • x ∈ secs (S n) V := by
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  haveI : Module.Finite Γ(X, V) Γ(E, V) := hE.2 V V.2
  haveI : E.IsQuasicoherent := hE.1
  set IB : Ideal Γ(X, V) := Ideal.map (toFunctions (A := A) (V : X.Opens)) I with hIB
  have hpow : ∀ n, Ideal.map (toFunctions (A := A) (V : X.Opens)) (I ^ n) = IB ^ n :=
    fun n => Ideal.map_pow _ _ _
  let T : ℕ → Submodule Γ(X, V) Γ(E, V) := fun n => secsSub (S n) V
  have hpowsecs : ∀ n, secs (powSub I E n) (V : X.Opens) =
      ((IB ^ n • ⊤ : Submodule Γ(X, (V : X.Opens)) Γ(E, (V : X.Opens))) : Set Γ(E, (V : X.Opens))) := by
    intro n
    rw [GlobalTheory.T.ideal_power_subobject_sections I E hE.1 n V V.2, hpow]
  have h1 : ∀ n, IB ^ (n + 1) • (⊤ : Submodule Γ(X, V) Γ(E, V)) ≤ T n := by
    intro n y hy
    have hy' : y ∈ secs (powSub I E (n + 1)) V := by rw [hpowsecs]; exact hy
    exact (GlobalTheory.T.subobject_le_iff_affine_sections _ _).1 (hS.pow_le n) V hy'
  have h2 : ∀ n, T n = T (n + 1) ⊔ IB ^ (n + 1) • (⊤ : Submodule Γ(X, V) Γ(E, V)) := by
    intro n
    have hq : (powSub I E (n + 1) : X.Modules).IsQuasicoherent := (closedSys_pow I E).qcoh n
    obtain ⟨_, hsum⟩ := GlobalTheory.T.quasicoherent_sup_sections hE.1 (S (n + 1)) (powSub I E (n + 1)) (hS.qcoh (n + 1)) hq
    ext y
    change y ∈ secs (S n) V ↔ _
    rw [hS.succ n, hsum V V.2, Submodule.mem_sup]
    constructor
    · rintro ⟨s, hs, t, ht, rfl⟩
      refine ⟨s, hs, t, ?_, rfl⟩
      have ht' : t ∈ ((IB ^ (n + 1) • ⊤ : Submodule Γ(X, V) Γ(E, V)) : Set Γ(E, V)) := by
        rw [← hpowsecs]; exact ht
      exact ht'
    · rintro ⟨s, hs, t, ht, rfl⟩
      refine ⟨s, hs, t, ?_, rfl⟩
      rw [hpowsecs]
      exact ht
  obtain ⟨R, firstRealIndex, secondRealIndex, iR3, M, familyMassRatio, familyMassSecondLine, iM3, iM4, iM5, μ, hjac, hspan, hiff⟩ :=
    GlobalTheory.T.complete_module_noetherian_realization IB T h1 h2
  have hJ : ∀ a ∈ J.ideal ⟨(V : X.Opens), V.2⟩, ∀ m : M, a • m = 0 := by
    intro a ha m
    have hm : m ∈ Submodule.span R (Set.range μ) := hspan ▸ Submodule.mem_top
    refine Submodule.span_induction (p := fun m _ => a • m = 0) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨e, rfl⟩
      apply eq_zero_of_mem_pow IB hjac
      intro n
      rw [← map_smul]
      exact (hiff n (a • e)).1 (hK n V a ha e)
    · exact smul_zero a
    · intro u v _ _ hu hv
      rw [smul_add, hu, hv, add_zero]
    · intro r u _ hu
      rw [smul_comm a r u, hu, smul_zero]
  have hIso : IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) :=
    GroundTheory.Arith.SchemeCoh.isIso_morphismRestrict_of_le ψ hf
  have hch := GlobalTheory.T.pushforward_system_affine_sections I (ψ ≫ J.subschemeι) hover hE hS B hB (V : X.Opens) V.2 x hx
  have hch' : ∀ n, ChartIn (ψ ≫ J.subschemeι) (V : X.Opens)
      (IB ^ (n + 1) • ⊤ : Submodule Γ(X, V) M) (μ x) := by
    intro n
    refine chartIn_map _ _ μ ?_ (hch n)
    rintro _ ⟨e, he, rfl⟩
    exact (hiff n e).1 he
  obtain ⟨k, hk⟩ := GlobalTheory.T.jacobson_ideal_faithful_module J ψ hψ (V : X.Opens) V.2 IB hjac hJ f hIso (μ x) hch'
  refine ⟨k, fun n => ?_⟩
  have hμ : μ (f ^ k • x) ∈ (IB ^ (n + 1) • ⊤ : Submodule Γ(X, V) M) := by
    rw [map_smul, hk]
    exact Submodule.zero_mem _
  exact (hiff n _).2 hμ

end GlobalTheory.CompanionTheory.GE.LocTors
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperBirationalClosedSystemStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_birational_closed_system : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsLocallyNoetherian X] (J : X.IdealSheafData) {Z : Scheme.{0}} [Z.Over (Spec (.of A))] (ψ : Z ⟶ J.subscheme), IsProper ψ → (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ (W : J.subscheme.Opens), IsIso (ψ ∣_ W) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → (∀ e, Killed J (S e)) → ∀ (B : Subobject ((Scheme.Modules.pullback (ψ ≫ J.subschemeι)).obj E)), (∀ e, B ⊔ powSub I _ (e + 1) = pullSys I (ψ ≫ J.subschemeι) E S e) → ∀ (V : X.affineOpens) (f : Γ(X, V)), J.subschemeι ⁻¹ᵁ X.basicOpen f ≤ W → ∀ x ∈ secs (adjKer (ψ ≫ J.subschemeι) B) V, ∃ k : ℕ, ∀ n, f ^ k • x ∈ secs (S n) V := by
  first | exact @GlobalTheory.CompanionTheory.GE.LocTors.adjKer_pow_smul_mem_secs | exact GlobalTheory.CompanionTheory.GE.LocTors.adjKer_pow_smul_mem_secs | (intros; apply GlobalTheory.CompanionTheory.GE.LocTors.adjKer_pow_smul_mem_secs <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardClosedSystemUnseenStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardClosedSystemAuxiliary
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.KerSupp

theorem supportedIn_cokernel_kernelSubobject {X : Scheme.{0}} {F G : X.Modules} (g : F ⟶ G) {T : Set X}
    (h : Scheme.Modules.SupportedIn G T) :
    Scheme.Modules.SupportedIn (cokernel (kernelSubobject g).arrow) T := by
  let S : ShortComplex X.Modules := ShortComplex.mk (kernel.ι g) g (kernel.condition _)
  have hex : S.Exact := ShortComplex.exact_kernel _
  have hm : Mono (cokernel.desc S.f S.g S.zero) := S.exact_iff_mono_cokernel_desc.1 hex
  have h1 : Scheme.Modules.SupportedIn (cokernel (kernel.ι g)) T :=
    Scheme.Modules.SupportedIn.of_mono (cokernel.desc S.f S.g S.zero) h
  have e : (kernelSubobjectIso g).hom ≫ kernel.ι g = (kernelSubobject g).arrow :=
    kernelSubobject_arrow g
  let i : cokernel (kernelSubobject g).arrow ≅ cokernel (kernel.ι g) :=
    cokernelIsoOfEq e.symm ≪≫ (cokernelEpiComp (kernelSubobjectIso g).hom _)
  exact h1.of_iso i.symm

theorem toImage_surjective {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f] : Surjective f.toImage := by
  refine ⟨fun y => ?_⟩
  have h1 : f.imageι y ∈ (f.ker.support : Set X) := f.ker.range_subschemeι.le ⟨y, rfl⟩
  rw [Scheme.Hom.support_ker, f.isClosedMap.isClosed_range.closure_eq] at h1
  obtain ⟨x, hx⟩ := h1
  refine ⟨x, f.imageι.isEmbedding.injective ?_⟩
  rw [← hx, ← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]

theorem isProper_image {S Y X : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [IsSeparated p]
    [LocallyOfFiniteType p] [QuasiCompact p] [IsProper f] (hY : IsProper (f ≫ p)) :
    IsProper (f.ker.subschemeι ≫ p) := by
  have := toImage_surjective f
  have hu : UniversallyClosed (f.toImage ≫ f.ker.subschemeι ≫ p) := by
    rw [← Category.assoc]
    change UniversallyClosed ((f.toImage ≫ f.imageι) ≫ p)
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  have : UniversallyClosed (f.ker.subschemeι ≫ p) := .of_comp_surjective f.toImage _
  exact ⟨⟩

theorem propSupp_adjKer {A : Type} [CommRing A] [IsNoetherianRing A] {X Z : Scheme.{0}}
    [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] (φ : Z ⟶ X)
    (hφ : IsProper φ) (hc : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) {E : X.Modules}
    (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (hB : PropSupp A B) :
    PropSupp A (adjKer φ B) := by
  obtain ⟨TZ, hTZ, hsupp⟩ := hB
  let f : TZ.subscheme ⟶ X := TZ.subschemeι ≫ φ
  have hf : IsProper f := inferInstance
  have hfp : IsProper (f ≫ (X ↘ Spec (.of A))) := by
    change IsProper ((TZ.subschemeι ≫ φ) ≫ (X ↘ Spec (.of A)))
    rw [Category.assoc, hc]
    exact hTZ
  refine ⟨f.ker, isProper_image f _ hfp, ?_⟩
  have hpush := hsupp.pushforward φ
  have hsub : φ.base '' (TZ.support : Set Z) ⊆ (f.ker.support : Set X) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw⟩ := TZ.range_subschemeι.ge hz
    rw [Scheme.Hom.support_ker]
    refine subset_closure ⟨w, ?_⟩
    rw [← hw]
    rfl
  exact supportedIn_cokernel_kernelSubobject (adjMap φ B) (hpush.mono hsub)

end GlobalTheory.CompanionTheory.GE.KerSupp
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushforward_closed_system_auxiliary : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] (φ : Z ⟶ X), IsProper φ → φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules} (B : Subobject ((Scheme.Modules.pullback φ).obj E)), PropSupp A B → PropSupp A (adjKer φ B) := by
  first | exact @GlobalTheory.CompanionTheory.GE.KerSupp.propSupp_adjKer | exact GlobalTheory.CompanionTheory.GE.KerSupp.propSupp_adjKer | (intros; apply GlobalTheory.CompanionTheory.GE.KerSupp.propSupp_adjKer <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerKillsSystem
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerKillsSystem
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Globalize

lemma exists_pow_smul_uniform {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (P : Submodule R M) (hP : P.FG) (N : ℕ → Submodule R M) (f : R)
    (h : ∀ x ∈ P, ∃ k : ℕ, ∀ n, f ^ k • x ∈ N n) :
    ∃ k : ℕ, ∀ n, ∀ x ∈ P, f ^ k • x ∈ N n := by
  classical
  obtain ⟨s, rfl⟩ := hP
  have h' : ∀ x ∈ s, ∃ k : ℕ, ∀ n, f ^ k • x ∈ N n :=
    fun x hx => h x (Submodule.subset_span (Finset.mem_coe.2 hx))
  choose! k hk using h'
  refine ⟨s.sup k, fun n x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem y hy =>
    have hy' : y ∈ s := Finset.mem_coe.1 hy
    have e : f ^ s.sup k • y = f ^ (s.sup k - k y) • f ^ k y • y := by
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel (Finset.le_sup hy')]
    rw [e]
    exact (N n).smul_mem _ (hk y hy' n)
  | zero => rw [smul_zero]; exact (N n).zero_mem
  | add y z _ _ hy hz => rw [smul_add]; exact (N n).add_mem hy hz
  | smul r y _ hy => rw [smul_comm]; exact (N n).smul_mem _ hy

variable {X : Scheme.{0}}

def killIdeal {E : X.Modules} (D : Subobject E) (S : ℕ → Subobject E) (V : X.Opens) :
    Ideal Γ(X, V) :=
  ⨅ n, (secsSub (S n) V).colon (secs D V)

lemma mem_killIdeal {E : X.Modules} {D : Subobject E} {S : ℕ → Subobject E} {V : X.Opens}
    {a : Γ(X, V)} : a ∈ killIdeal D S V ↔ ∀ n, ∀ x ∈ secs D V, a • x ∈ secs (S n) V := by
  simp only [killIdeal, Submodule.mem_iInf, Submodule.mem_colon]
  rfl

theorem exists_pow_le_killIdeal [IsLocallyNoetherian X] {E : X.Modules} (hE : IsCoherent E)
    (D : Subobject E) (hD : (D : X.Modules).IsQuasicoherent) (S : ℕ → Subobject E)
    (J₀ : X.IdealSheafData) (V : X.affineOpens)
    (h : ∀ f ∈ J₀.ideal V, ∀ x ∈ secs D V, ∃ k : ℕ, ∀ n, f ^ k • x ∈ secs (S n) V) :
    ∃ m : ℕ, J₀.ideal V ^ m ≤ killIdeal D S V := by
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  have hfin : Module.Finite Γ(X, V) Γ((D : X.Modules), V) :=
    (isCoherent_subobject hE D hD).2 V V.2
  let φ : Γ((D : X.Modules), V) →ₗ[Γ(X, V)] Γ(E, V) :=
    { toFun := D.arrow.app V
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  have hr : secsSub D V = LinearMap.range φ := Submodule.ext fun _ => Iff.rfl
  have hP : (secsSub D V).FG := by
    rw [hr, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map φ
  have hrad : J₀.ideal V ≤ (killIdeal D S V).radical := by
    intro f hf
    obtain ⟨k, hk⟩ := exists_pow_smul_uniform (secsSub D V) hP (fun n => secsSub (S n) V) f
      (fun x hx => h f hf x hx)
    exact ⟨k, mem_killIdeal.2 fun n x hx => hk n x hx⟩
  exact Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)

end GlobalTheory.CompanionTheory.GE.Globalize

namespace GlobalTheory.CompanionTheory.GE.Globalize

variable {X : Scheme.{0}}

theorem pow_le_killIdeal_basicOpen {E : X.Modules} (D : Subobject E)
    [(D : X.Modules).IsQuasicoherent] (S : ℕ → Subobject E) (J₀ : X.IdealSheafData)
    (V : X.affineOpens) (m : ℕ) (hV : J₀.ideal V ^ m ≤ killIdeal D S V) (g : Γ(X, V)) :
    J₀.ideal (X.affineBasicOpen g) ^ m ≤ killIdeal D S (X.basicOpen g) := by
  have hmap : Ideal.map (resO (X.basicOpen_le g)) (J₀.ideal V ^ m) =
      J₀.ideal (X.affineBasicOpen g) ^ m := by
    rw [Ideal.map_pow, J₀.map_ideal_basicOpen]
    rfl
  intro a ha
  rw [← hmap] at ha
  refine (Ideal.map_le_iff_le_comap.2 ?_ : Ideal.map (resO (X.basicOpen_le g)) (J₀.ideal V ^ m) ≤
    killIdeal D S (X.basicOpen g)) ha
  intro r hr
  rw [Ideal.mem_comap]
  refine mem_killIdeal.2 fun n x hx => ?_
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨e, y', hy'⟩ := qcoh_exists_res_eq (D : X.Modules) V.2 g y
  obtain ⟨z, hz⟩ := mem_killIdeal.1 (hV hr) n _ ⟨y', rfl⟩
  have key : resO (X.basicOpen_le g) g ^ e • (resO (X.basicOpen_le g) r • D.arrow.app _ y) ∈
      secs (S n) (X.basicOpen g) := by
    refine ⟨resF _ (X.basicOpen_le g) z, ?_⟩
    rw [← resF_app, hz, resF_smul, resF_app, hy', Scheme.Modules.Hom.app_smul, smul_comm]
  obtain ⟨u, hu⟩ : IsUnit (resO (X.basicOpen_le g) g) := X.toRingedSpace.isUnit_res_basicOpen g
  have e2 : resO (X.basicOpen_le g) r • D.arrow.app _ y =
      ((u⁻¹ : (Γ(X, X.basicOpen g))ˣ) : Γ(X, X.basicOpen g)) ^ e •
        (resO (X.basicOpen_le g) g ^ e • (resO (X.basicOpen_le g) r • D.arrow.app _ y)) := by
    rw [smul_smul, ← mul_pow, ← hu, Units.inv_mul, one_pow, one_smul]
  rw [e2]
  exact (secsSub (S n) (X.basicOpen g)).smul_mem _ key

theorem mem_secs_of_local {E : X.Modules} [E.IsQuasicoherent] (T : Subobject E)
    [(T : X.Modules).IsQuasicoherent] (U : X.affineOpens) (x : Γ(E, U))
    (h : ∀ p ∈ (U : X.Opens), ∃ W : X.affineOpens, p ∈ (W : X.Opens) ∧
      ∃ hW : (W : X.Opens) ≤ U, resF E hW x ∈ secs T W) :
    x ∈ secs T U := by
  choose W hpW hWU hW using h
  have h0 : (cokernel.π T.arrow).app U x = 0 := by
    refine eq_of_forall_resF (cokernel T.arrow) (fun p : (U : X.Opens) => (W p.1 p.2 : X.Opens))
      (fun p => hWU p.1 p.2) ?_ _ 0 ?_
    · intro p hp
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, hp⟩, hpW p hp⟩
    · intro p
      obtain ⟨z, hz⟩ := hW p.1 p.2
      rw [resF_app, ← hz, map_zero, (GlobalTheory.QCoh.exact_cokernel_π_app T.arrow (W p.1 p.2).2).apply_apply_eq_zero z]
  exact (GlobalTheory.QCoh.exact_cokernel_π_app T.arrow U.2 x).1 h0

end GlobalTheory.CompanionTheory.GE.Globalize

namespace GlobalTheory.CompanionTheory.GE.Globalize

theorem exists_uniform_pow_kills : ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] [CompactSpace X]
    {E : X.Modules}, IsCoherent E → ∀ (D : Subobject E), (D : X.Modules).IsQuasicoherent →
    ∀ (S : ℕ → Subobject E), (∀ n, (S n : X.Modules).IsQuasicoherent) →
    ∀ J₀ : X.IdealSheafData, (∀ (V : X.affineOpens) (f : Γ(X, V)), f ∈ J₀.ideal V →
      ∀ x ∈ secs D V, ∃ k : ℕ, ∀ n, f ^ k • x ∈ secs (S n) V) →
    ∃ m : ℕ, ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ (powIdeal J₀ m).ideal U →
      ∀ x ∈ secs D U, a • x ∈ secs (S n) U := by
  intro X _ _ E hE D hD S hS J₀ hJ
  choose mV hmV using fun V : X.affineOpens => exists_pow_le_killIdeal hE D hD S J₀ V (hJ V)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens => ((V : X.Opens) : Set X))
    (fun V => (V : X.Opens).isOpen) (by
      intro p _
      obtain ⟨V, hV⟩ : ∃ V : X.affineOpens, p ∈ (V : X.Opens) := by
        obtain ⟨V, hV, hpV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
          (show p ∈ (⊤ : X.Opens) from trivial)
        exact ⟨⟨V, hV⟩, hpV⟩
      exact Set.mem_iUnion.2 ⟨V, hV⟩)
  refine ⟨t.sup mV, fun n U a ha x hx => ?_⟩
  haveI : E.IsQuasicoherent := hE.1
  haveI : (D : X.Modules).IsQuasicoherent := hD
  haveI := hS n
  refine mem_secs_of_local (S n) U (a • x) fun p hpU => ?_
  obtain ⟨V, hVt, hpV⟩ : ∃ V ∈ t, p ∈ ((V : X.Opens) : Set X) := by
    simpa using ht (Set.mem_univ p)
  obtain ⟨f, g, hfg, hpf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 p ⟨hpU, hpV⟩
  have hWU : X.basicOpen g ≤ (U : X.Opens) := hfg ▸ X.basicOpen_le f
  refine ⟨X.affineBasicOpen g, (show p ∈ X.basicOpen g from hfg ▸ hpf), hWU, ?_⟩
  have hVm : J₀.ideal V ^ t.sup mV ≤ killIdeal D S V :=
    (Ideal.pow_le_pow_right (Finset.le_sup hVt)).trans (hmV V)
  have hk := pow_le_killIdeal_basicOpen D S J₀ V _ hVm g
  have hWU' : X.affineBasicOpen g ≤ U := hWU
  have ha' : resO hWU a ∈ J₀.ideal (X.affineBasicOpen g) ^ t.sup mV := by
    have := Ideal.mem_map_of_mem (resO hWU) (show a ∈ J₀.ideal U ^ t.sup mV from ha)
    rw [Ideal.map_pow] at this
    exact (J₀.map_ideal hWU') ▸ this
  obtain ⟨y, rfl⟩ := hx
  have e3 := resF_smul E hWU a (D.arrow.app U y)
  erw [e3, resF_app]
  exact mem_killIdeal.1 (hk ha') n _ ⟨_, rfl⟩

end GlobalTheory.CompanionTheory.GE.Globalize
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerKillsSystemStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_power_kills_system : ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] [CompactSpace X] {E : X.Modules}, IsCoherent E → ∀ (D : Subobject E), (D : X.Modules).IsQuasicoherent → ∀ (S : ℕ → Subobject E), (∀ n, (S n : X.Modules).IsQuasicoherent) → ∀ J₀ : X.IdealSheafData, (∀ (V : X.affineOpens) (f : Γ(X, V)), f ∈ J₀.ideal V → ∀ x ∈ secs D V, ∃ k : ℕ, ∀ n, f ^ k • x ∈ secs (S n) V) → ∃ m : ℕ, ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ (powIdeal J₀ m).ideal U → ∀ x ∈ secs D U, a • x ∈ secs (S n) U := by
  first | exact @GlobalTheory.CompanionTheory.GE.Globalize.exists_uniform_pow_kills | exact GlobalTheory.CompanionTheory.GE.Globalize.exists_uniform_pow_kills | (intros; apply GlobalTheory.CompanionTheory.GE.Globalize.exists_uniform_pow_kills <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperSupportPullbackSystem
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperSupportPullbackSystem
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.PullSupp

theorem supportedIn_pullback {X Z : Scheme.{0}} (φ : Z ⟶ X) {C : X.Modules} {T₀ : Set X}
    (hT : IsClosed T₀) (h : Scheme.Modules.SupportedIn C T₀) :
    Scheme.Modules.SupportedIn ((Scheme.Modules.pullback φ).obj C) (φ.base ⁻¹' T₀) := by
  refine Scheme.Modules.SupportedIn.of_isZero_restrict fun U hU => ?_
  let V : X.Opens := ⟨T₀ᶜ, hT.isOpen_compl⟩
  have hr : Set.range (U.ι ≫ φ) ⊆ Set.range V.ι := by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    intro hx
    exact Set.disjoint_left.1 hU u.2 hx
  let g := IsOpenImmersion.lift V.ι (U.ι ≫ φ) hr
  have hg : g ≫ V.ι = U.ι ≫ φ := IsOpenImmersion.lift_fac _ _ _
  have h0 : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj C) :=
    h.isZero_restrict V disjoint_compl_left
  have h1 : IsZero ((Scheme.Modules.pullback g).obj ((Scheme.Modules.restrictFunctor V.ι).obj C)) :=
    Functor.map_isZero _ h0
  refine h1.of_iso ?_
  exact (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫
    (Scheme.Modules.pullbackComp U.ι φ).app C ≪≫ (Scheme.Modules.pullbackCongr hg.symm).app C ≪≫
    ((Scheme.Modules.pullbackComp g V.ι).app C).symm ≪≫
    (Scheme.Modules.pullback g).mapIso ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app C).symm

end GlobalTheory.CompanionTheory.GE.PullSupp

namespace GlobalTheory.CompanionTheory.GE.PullSupp

theorem supportedIn_cokernel_pullSys {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X Z : Scheme.{0}} [Z.Over (Spec (.of A))] (φ : Z ⟶ X) (E : X.Modules) (S : ℕ → Subobject E)
    {T₀ : Set X} (hT : IsClosed T₀) (h : Scheme.Modules.SupportedIn (cokernel (S 0).arrow) T₀) :
    Scheme.Modules.SupportedIn (cokernel (pullSys I φ E S 0).arrow) (φ.base ⁻¹' T₀) := by
  let f := (Scheme.Modules.pullback φ).map (S 0).arrow
  have hle : imageSubobject f ≤ pullSys I φ E S 0 := le_sup_left
  have w : f ≫ cokernel.π (pullSys I φ E S 0).arrow = 0 := by
    rw [← imageSubobject_arrow_comp f, ← Subobject.ofLE_arrow hle, Category.assoc, Category.assoc,
      cokernel.condition, comp_zero, comp_zero]
  have hd : Epi (cokernel.desc f _ w) := epi_of_epi_fac (cokernel.π_desc f _ w)
  have h1 : Scheme.Modules.SupportedIn (cokernel f) (φ.base ⁻¹' T₀) :=
    (supportedIn_pullback φ hT h).of_iso (PreservesCokernel.iso (Scheme.Modules.pullback φ) (S 0).arrow)
  exact Scheme.Modules.SupportedIn.of_epi (cokernel.desc f _ w) h1

theorem exists_proper_preimage {A : Type} [CommRing A] {X Z : Scheme.{0}} [X.Over (Spec (.of A))]
    [Z.Over (Spec (.of A))] (φ : Z ⟶ X) (hφ : IsProper φ)
    (hc : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) (T : X.IdealSheafData)
    (hT : IsProper (T.subschemeι ≫ (X ↘ Spec (.of A)))) :
    ∃ T' : Z.IdealSheafData, IsProper (T'.subschemeι ≫ (Z ↘ Spec (.of A))) ∧
      φ.base ⁻¹' (T.support : Set X) ⊆ (T'.support : Set Z) := by
  let p := pullback.fst φ T.subschemeι
  let q := pullback.snd φ T.subschemeι
  have hpc : IsClosedImmersion p := inferInstance
  let T' : Z.IdealSheafData := p.ker
  have hk1 : p.ker ≤ T'.subschemeι.ker := by rw [Scheme.IdealSheafData.ker_subschemeι]
  have hk2 : T'.subschemeι.ker ≤ p.ker := by rw [Scheme.IdealSheafData.ker_subschemeι]
  let u := IsClosedImmersion.lift p T'.subschemeι hk1
  let v := IsClosedImmersion.lift T'.subschemeι p hk2
  have hu : u ≫ p = T'.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have hv : v ≫ T'.subschemeι = p := IsClosedImmersion.lift_fac _ _ _
  refine ⟨T', ?_, ?_⟩
  · have hq : IsProper q := by haveI := hφ; infer_instance
    have huc : IsClosedImmersion u := by
      have : IsClosedImmersion (u ≫ p) := by rw [hu]; infer_instance
      exact IsClosedImmersion.of_comp u p
    have e : T'.subschemeι ≫ (Z ↘ Spec (.of A)) = u ≫ q ≫ (T.subschemeι ≫ (X ↘ Spec (.of A))) := by
      rw [← hu, ← hc, Category.assoc, ← Category.assoc p, pullback.condition]
      simp only [Category.assoc]
      rfl
    rw [e]
    infer_instance
  · intro z hz
    obtain ⟨w, hw⟩ := T.range_subschemeι.ge hz
    obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ) (g := T.subschemeι) z w hw.symm
    rw [← T'.range_subschemeι]
    refine ⟨v t, ?_⟩
    have hv' : v ≫ T'.subschemeι = pullback.fst φ T.subschemeι := hv
    rw [← ht, ← hv']
    rfl

theorem propSupp_pullSys : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}}
    [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X), IsProper φ →
    φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E →
    ∀ {S : ℕ → Subobject E}, ClosedSys I E S → PropSupp A (S 0) → PropSupp A (pullSys I φ E S 0) := by
  intro A _ _ I X Z _ _ _ φ hφ hc E _ S _ hS
  obtain ⟨T, hTp, hTs⟩ := hS
  obtain ⟨T', hT'p, hT's⟩ := exists_proper_preimage φ hφ hc T hTp
  exact ⟨T', hT'p, (supportedIn_cokernel_pullSys I φ E S T.support.isClosed hTs).mono hT's⟩

end GlobalTheory.CompanionTheory.GE.PullSupp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperSupportPullbackSystemStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_support_pullback_system : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X), IsProper φ → φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → PropSupp A (S 0) → PropSupp A (pullSys I φ E S 0) := by
  exact @GlobalTheory.CompanionTheory.GE.PullSupp.propSupp_pullSys
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonemptyOpenIdealNotNilpotent
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonemptyOpenIdealNotNilpotent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE.NonIso

theorem exists_ideal_not_pow_le {X : Scheme.{0}} (J : X.IdealSheafData) (W : J.subscheme.Opens)
    (hW : (W : Set J.subscheme).Nonempty) :
    ∃ J₀ : X.IdealSheafData, (∀ (V : X.affineOpens) (f : Γ(X, V)), f ∈ J₀.ideal V →
      J.subschemeι ⁻¹ᵁ X.basicOpen f ≤ W) ∧ ∀ m, ¬ powIdeal J₀ m ≤ J := by
  have hC : IsClosed (J.subschemeι '' (W : Set J.subscheme)ᶜ) :=
    J.subschemeι.isClosedEmbedding.isClosedMap _ W.isOpen.isClosed_compl
  let C : TopologicalSpace.Closeds X := ⟨_, hC⟩
  have hsupp : ∀ x : X, x ∈ (Scheme.IdealSheafData.vanishingIdeal C).support ↔
      x ∈ J.subschemeι '' (W : Set J.subscheme)ᶜ := by
    intro x
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  refine ⟨Scheme.IdealSheafData.vanishingIdeal C, ?_, ?_⟩
  · intro V f hf y hy
    have hyV : J.subschemeι y ∈ (V : X.Opens) := X.basicOpen_le f hy
    by_contra hyW
    have h1 : J.subschemeι y ∈ (Scheme.IdealSheafData.vanishingIdeal C).support :=
      (hsupp _).2 ⟨y, hyW, rfl⟩
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hyV, Scheme.mem_zeroLocus_iff] at h1
    exact h1 f hf hy
  · intro m hm
    obtain ⟨w, hw⟩ := hW
    obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
      (show J.subschemeι w ∈ (⊤ : X.Opens) from trivial)
    let V' : X.affineOpens := ⟨V, hV⟩
    have hxV' : J.subschemeι w ∈ (V' : X.Opens) := hxV
    have hnC : J.subschemeι w ∉ (Scheme.IdealSheafData.vanishingIdeal C).support := by
      rw [hsupp]
      rintro ⟨w', hw', he⟩
      exact hw' (J.subschemeι.isClosedEmbedding.injective he ▸ hw)
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxV', Scheme.mem_zeroLocus_iff] at hnC
    push_neg at hnC
    obtain ⟨f, hf, hxf⟩ := hnC
    have hfm : f ^ m ∈ J.ideal V' := Scheme.IdealSheafData.le_def.1 hm V' (Ideal.pow_mem_pow hf m)
    have hxJ : J.subschemeι w ∈ J.support := by
      rw [← SetLike.mem_coe, ← J.range_subschemeι]; exact ⟨w, rfl⟩
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxV', Scheme.mem_zeroLocus_iff] at hxJ
    refine hxJ (f ^ m) hfm ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · rw [pow_zero, Scheme.basicOpen_of_isUnit _ isUnit_one]; trivial
    · rwa [Scheme.basicOpen_pow _ _ hm0]

end GlobalTheory.CompanionTheory.GE.NonIso
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonemptyOpenIdealNotNilpotentStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_open_ideal_not_nilpotent : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) (W : J.subscheme.Opens), (W : Set J.subscheme).Nonempty → ∃ J₀ : X.IdealSheafData, (∀ (V : X.affineOpens) (f : Γ(X, V)), f ∈ J₀.ideal V → J.subschemeι ⁻¹ᵁ X.basicOpen f ≤ W) ∧ ∀ m, ¬ powIdeal J₀ m ≤ J := by
  first | exact @GlobalTheory.CompanionTheory.GE.NonIso.exists_ideal_not_pow_le | exact GlobalTheory.CompanionTheory.GE.NonIso.exists_ideal_not_pow_le | (intros; apply GlobalTheory.CompanionTheory.GE.NonIso.exists_ideal_not_pow_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProperPushforward
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem core_integral_step : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] (J : X.IdealSheafData) [IsIntegral J.subscheme] {Z : Scheme.{0}} [Z.Over (Spec (.of A))], Statement I (⊥ : Z.IdealSheafData) → ∀ (ψ : Z ⟶ J.subscheme), IsProper ψ → (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ (W : J.subscheme.Opens), (W : Set J.subscheme).Nonempty → IsIso (ψ ∣_ W) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → (∀ e, Killed J (S e)) → PropSupp A (S 0) → ∃ (D : Subobject E) (c : ℕ) (J' : X.IdealSheafData), (D : X.Modules).IsQuasicoherent ∧ PropSupp A D ∧ (∀ e, S (e + c) ≤ D ⊔ powSub I E (e + 1)) ∧ J < J' ∧ ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ J'.ideal U → ∀ x ∈ secs D U, a • x ∈ secs (S n) U := by
  intro A _ _ I _ X _ _ _ _ J _ Z _ hZ ψ hψ hover W hW hiso E hE S hS hK hP
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hcs : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have hφ : IsProper (ψ ≫ J.subschemeι) := by
    haveI := hψ
    infer_instance
  have hcl := GlobalTheory.T.closed_system_pullback I (ψ ≫ J.subschemeι) hover hE hS
  have hps := GlobalTheory.T.proper_support_pullback_system I (ψ ≫ J.subschemeι) hφ hover hE hS hP
  have hEZ := isCoherent_pullback (ψ ≫ J.subschemeι) hE
  obtain ⟨B, hBq, hBP, hB⟩ := hZ _ hEZ _ hcl (fun e U a ha x => by
    have ha0 : a = 0 := by simpa using ha
    subst ha0
    exact ⟨0, by rw [map_zero, zero_smul]⟩) hps
  have := hEZ.1
  have hG : IsCoherent (cokernel B.arrow) := isCoherent_cokernel B.arrow hEZ
  have hP' := GlobalTheory.T.proper_pushforward_coherent (ψ ≫ J.subschemeι) hφ hG
  have := hP'.1
  have hE1 := hE.1
  have hDq : ((adjKer (ψ ≫ J.subschemeι) B : Subobject E) : X.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (kernelSubobjectIso (adjMap (ψ ≫ J.subschemeι) B)).symm
      (isCoherent_kernel (adjMap (ψ ≫ J.subschemeι) B) hE).1
  obtain ⟨c, hc⟩ := GlobalTheory.T.proper_pullback_system_quasicoherent I (ψ ≫ J.subschemeι) hφ hover hE hS B hBq hB
  obtain ⟨J₀, hJ₀, hJ₀J⟩ := GlobalTheory.T.nonempty_open_ideal_not_nilpotent J W hW
  obtain ⟨m, hm⟩ := GlobalTheory.T.ideal_power_kills_system hE (adjKer (ψ ≫ J.subschemeι) B) hDq S hS.qcoh J₀
    (fun V f hf x hx => GlobalTheory.T.proper_birational_closed_system I J ψ hψ hover W hiso hE hS hK B hB V f (hJ₀ V f hf) x hx)
  refine ⟨adjKer (ψ ≫ J.subschemeι) B, c, J ⊔ powIdeal J₀ m, hDq,
    GlobalTheory.T.pushforward_closed_system_auxiliary (ψ ≫ J.subschemeι) hφ hover B hBP, hc, ?_, ?_⟩
  · exact lt_of_le_of_ne le_sup_left (fun h => hJ₀J m (h ▸ le_sup_right))
  · intro n U a ha x hx
    obtain ⟨a₁, h₁, a₂, h₂, rfl⟩ := Submodule.mem_sup.1 ha
    rw [add_smul]
    obtain ⟨y, rfl⟩ := hx
    exact (secsSub (S n) U).add_mem (hK n U a₁ h₁ _) (hm n U a₂ h₂ _ ⟨y, rfl⟩)

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProperPushforwardStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_existence_proper_pushforward : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] (J : X.IdealSheafData) [IsIntegral J.subscheme] {Z : Scheme.{0}} [Z.Over (Spec (.of A))], Statement I (⊥ : Z.IdealSheafData) → ∀ (ψ : Z ⟶ J.subscheme), IsProper ψ → (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ (W : J.subscheme.Opens), (W : Set J.subscheme).Nonempty → IsIso (ψ ∣_ W) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → (∀ e, Killed J (S e)) → PropSupp A (S 0) → ∃ (D : Subobject E) (c : ℕ) (J' : X.IdealSheafData), (D : X.Modules).IsQuasicoherent ∧ PropSupp A D ∧ (∀ e, S (e + c) ≤ D ⊔ powSub I E (e + 1)) ∧ J < J' ∧ ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ J'.ideal U → ∀ x ∈ secs D U, a • x ∈ secs (S n) U := by
  first | exact @GlobalTheory.CompanionTheory.GE.core_integral_step | exact GlobalTheory.CompanionTheory.GE.core_integral_step | (intros; apply GlobalTheory.CompanionTheory.GE.core_integral_step <;> assumption)
end

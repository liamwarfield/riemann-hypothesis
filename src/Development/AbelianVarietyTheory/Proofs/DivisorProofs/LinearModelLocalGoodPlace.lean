module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalProjection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepTrivialRealPoints
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorIsotropicTranslationCharSplit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceTransformSchwartzBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceTransformSchwartzBijective
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SwapSliceBij

open GlobalTheory.SwapSlice

theorem totDisc_localField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : TotallyDisconnectedSpace k := by
  haveI : T2Space k := inferInstance
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  infer_instance

theorem conj_mem_SB {X : Type} [TopologicalSpace X] {f : X → ℂ} (hf : f ∈ SB X) :
    (fun x => starRingEnd ℂ (f x)) ∈ SB X :=
  ⟨hf.1.comp (starRingEnd ℂ), hf.2.comp_left (map_zero _)⟩

theorem barL_bijOn {k Y : Type} [TopologicalSpace k] [TopologicalSpace Y] {κ : Type}
    (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (h : Set.BijOn ι (SB (κ → k) : Set ((κ → k) → ℂ)) (SB Y : Set (Y → ℂ))) :
    Set.BijOn (barL ι) (SB (κ → k) : Set ((κ → k) → ℂ)) (SB Y : Set (Y → ℂ)) := by
  refine ⟨fun φ hφ => conj_mem_SB (h.mapsTo (conj_mem_SB hφ)), fun φ hφ ψ hψ e => ?_, fun g hg => ?_⟩
  · have e' : ι (fun x => starRingEnd ℂ (φ x)) = ι (fun x => starRingEnd ℂ (ψ x)) := by
      funext y
      have := congrFun e y
      simp only [barL_apply] at this
      simpa using congrArg (starRingEnd ℂ) this
    have e'' := h.injOn (conj_mem_SB hφ) (conj_mem_SB hψ) e'
    funext x
    simpa using congrArg (starRingEnd ℂ) (congrFun e'' x)
  · obtain ⟨φ', hφ', e⟩ := h.surjOn (conj_mem_SB hg)
    refine ⟨fun x => starRingEnd ℂ (φ' x), conj_mem_SB hφ', ?_⟩
    funext y
    simp [barL_apply, e]

theorem boxFun_mem {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

variable {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] [LocallyCompactSpace k] [TotallyDisconnectedSpace k]
  {κ : Type} [Fintype κ]

theorem SB_le_span_boxFun :
    SB (κ ⊕ κ → k) ≤ Submodule.span ℂ {f | ∃ φ₁ ∈ SB (κ → k), ∃ φ₂ ∈ SB (κ → k), f = boxFun φ₁ φ₂} := by
  intro Φ hΦ
  let e := Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ)
  have hspan := GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top (κ → k) (κ → k)
  let T : GlobalTheory.SplitWeil.SB ((κ → k) × (κ → k)) →ₗ[ℂ] ((κ ⊕ κ → k) → ℂ) :=
    (LinearMap.funLeft ℂ ℂ e) ∘ₗ (GlobalTheory.SplitWeil.SB _).subtype
  have hΦ' : Φ ∘ e.symm ∈ GlobalTheory.SplitWeil.SB ((κ → k) × (κ → k)) :=
    ⟨hΦ.1.comp_continuous e.symm.continuous, hΦ.2.comp_homeomorph e.symm⟩
  have key : Φ ∈ Submodule.map T ⊤ := ⟨⟨Φ ∘ e.symm, hΦ'⟩, trivial, by
    funext x; simp [T, LinearMap.funLeft]⟩
  rw [← hspan, Submodule.map_span, ← Set.range_comp] at key
  refine Submodule.span_mono ?_ key
  rintro _ ⟨q, rfl⟩
  exact ⟨q.1.1, q.1.2, q.2.1, q.2.2, by funext x; rfl⟩

theorem mem_of_boxFun {M : Type} [AddCommGroup M] [Module ℂ M] (L : ((κ ⊕ κ → k) → ℂ) →ₗ[ℂ] M) (P : Submodule ℂ M)
    (h : ∀ φ₁ ∈ SB (κ → k), ∀ φ₂ ∈ SB (κ → k), L (boxFun φ₁ φ₂) ∈ P) : ∀ Φ ∈ SB (κ ⊕ κ → k), L Φ ∈ P := by
  intro Φ hΦ
  have hle : Submodule.span ℂ {f | ∃ φ₁ ∈ SB (κ → k), ∃ φ₂ ∈ SB (κ → k), f = boxFun φ₁ φ₂} ≤ P.comap L :=
    Submodule.span_le.2 (by rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩; exact h φ₁ h₁ φ₂ h₂)
  exact hle (SB_le_span_boxFun hΦ)

end GlobalTheory.SwapSliceBij


open GlobalTheory.SwapSlice GlobalTheory.SwapSliceBij in
theorem GlobalTheory.SwapSliceBij.sliceT_bijOn : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {κ : Type} [Fintype κ] {n d : ℕ}
    (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.BijOn ι (SB (κ → k) : Set ((κ → k) → ℂ)) (SB (Matrix (Fin n) (Fin d) k) : Set _) →
    Set.BijOn (GlobalTheory.SwapSlice.sliceT ι) (SB (κ ⊕ κ → k) : Set ((κ ⊕ κ → k) → ℂ))
      (SB (Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k) : Set _) := by
  intro k _ _ _ _ κ _ n d ι hι
  haveI : T2Space k := inferInstance
  haveI := totDisc_localField k
  haveI : LocallyCompactSpace k := inferInstance
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin d) k) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin d → k))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin d) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin d → k))
  haveI : T2Space (Matrix (Fin n) (Fin d) k) := inferInstanceAs (T2Space (Fin n → Fin d → k))
  have hbar := barL_bijOn ι hι

  have hslice : ∀ x₂ : κ → k, ∀ Φ ∈ SB (κ ⊕ κ → k), (fun x₁ => Φ (Sum.elim x₁ x₂)) ∈ SB (κ → k) := by
    intro x₂
    refine mem_of_boxFun (LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂)) (SB (κ → k)) ?_
    intro φ₁ h₁ φ₂ h₂
    have e : LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂) (boxFun φ₁ φ₂) = φ₂ x₂ • φ₁ := by
      funext x₁; simp [LinearMap.funLeft, boxFun, Function.comp_def, mul_comm]
    rw [e]; exact Submodule.smul_mem _ _ h₁

  have hcol : ∀ Z₁ : Matrix (Fin n) (Fin d) k, ∀ Φ ∈ SB (κ ⊕ κ → k),
      (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z₁) ∈ SB (κ → k) := by
    intro Z₁
    refine mem_of_boxFun (LinearMap.pi fun x₂ : κ → k => (LinearMap.proj Z₁) ∘ₗ ι ∘ₗ
      LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂)) (SB (κ → k)) ?_
    intro φ₁ h₁ φ₂ h₂
    have e : (LinearMap.pi fun x₂ : κ → k => (LinearMap.proj Z₁) ∘ₗ ι ∘ₗ
        LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂)) (boxFun φ₁ φ₂) = ι φ₁ Z₁ • φ₂ := by
      funext x₂
      have e' : LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂) (boxFun φ₁ φ₂) = φ₂ x₂ • φ₁ := by
        funext x₁; simp [LinearMap.funLeft, boxFun, Function.comp_def, mul_comm]
      simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, e', map_smul, LinearMap.coe_proj,
        Function.eval, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]; exact Submodule.smul_mem _ _ h₂
  have hz : ∀ Φ ∈ SB (κ ⊕ κ → k), sliceT ι Φ = 0 → Φ = 0 := by
    intro Φ hΦ h0
    have h1 : ∀ Z₁, (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z₁) = 0 := by
      intro Z₁
      refine hbar.injOn (hcol Z₁ Φ hΦ) (zero_mem _) ?_
      rw [map_zero]; funext Z₂; exact congrFun h0 (Z₁, Z₂)
    have h2 : ∀ x₂, (fun x₁ => Φ (Sum.elim x₁ x₂)) = 0 := by
      intro x₂
      refine hι.injOn (hslice x₂ Φ hΦ) (zero_mem _) ?_
      rw [map_zero]; funext Z₁; exact congrFun (h1 Z₁) x₂
    funext x
    have := congrFun (h2 (x ∘ Sum.inr)) (x ∘ Sum.inl)
    simpa [Sum.elim_comp_inl_inr] using this
  refine ⟨?_, fun Φ hΦ Ψ hΨ e => sub_eq_zero.1 (hz (Φ - Ψ) (sub_mem hΦ hΨ) (by rw [map_sub, e, sub_self])), ?_⟩
  · intro Φ hΦ
    refine mem_of_boxFun (sliceT ι) _ ?_ Φ hΦ
    intro φ₁ h₁ φ₂ h₂
    have e : sliceT ι (boxFun φ₁ φ₂) = GlobalTheory.LocFlat.CFac.prodFn (ι φ₁) (barL ι φ₂) := by
      funext Z; rw [sliceT_boxFun]; rfl
    rw [e]; exact GlobalTheory.LocFlat.CFac.prodFn_mem_SB (hι.mapsTo h₁) (hbar.mapsTo h₂)
  · intro g hg
    have hspan := GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top (Matrix (Fin n) (Fin d) k) (Matrix (Fin n) (Fin d) k)
    have key : g ∈ Submodule.map (GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k)).subtype ⊤ :=
      ⟨⟨g, hg⟩, trivial, rfl⟩
    rw [← hspan, Submodule.map_span, ← Set.range_comp] at key
    have hle : Submodule.span ℂ (Set.range ((GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k)).subtype ∘
        fun q : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k) × GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k) =>
          GlobalTheory.LocFlat.CFac.prodSB q.1 q.2)) ≤ Submodule.map (sliceT ι) (SB (κ ⊕ κ → k)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨q, rfl⟩
      obtain ⟨φ₁, h₁, e₁⟩ := hι.surjOn q.1.2
      obtain ⟨φ₂, h₂, e₂⟩ := hbar.surjOn q.2.2
      refine ⟨boxFun φ₁ φ₂, boxFun_mem h₁ h₂, ?_⟩
      funext Z
      rw [sliceT_boxFun, e₁, e₂]
      rfl
    obtain ⟨Φ, hΦ, e⟩ := Submodule.mem_map.1 (hle key)
    exact ⟨Φ, hΦ, e⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceTransformSchwartzBijectiveStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slice_transform_schwartz_bijective : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {κ : Type} [Fintype κ] {n d : ℕ}
    (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.BijOn ι (SB (κ → k) : Set ((κ → k) → ℂ)) (SB (Matrix (Fin n) (Fin d) k) : Set _) →
    Set.BijOn (GlobalTheory.SwapSlice.sliceT ι) (SB (κ ⊕ κ → k) : Set ((κ ⊕ κ → k) → ℂ))
      (SB (Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k) : Set _) := by
  first | exact @GlobalTheory.SwapSliceBij.sliceT_bijOn | exact GlobalTheory.SwapSliceBij.sliceT_bijOn | (intros; apply GlobalTheory.SwapSliceBij.sliceT_bijOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarModelLocalTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisSliceT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

open GlobalTheory.FlipMatch

namespace GlobalTheory.SwapHeis

theorem heis_sliceT : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    G.V'.J.det ≠ 0 → G.W.J.det ≠ 0 →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) d' dd →
    ∀ (u₁ u₂ : Matrix (Fin (a + a')) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) u₁ → At (evFin F v) u₂ →
    GlobalTheory.FlipMatch.pairM (GlobalTheory.FlipMatch.coX t 1 1 u₁ᵀ) (GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 u₁ᵀ) = 0 →
    GlobalTheory.FlipMatch.pairM (GlobalTheory.FlipMatch.coX t 1 1 u₂ᵀ) (GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 u₂ᵀ) = 0 →
    ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
    ∀ Z : Matrix (Fin a') (Fin (a + a')) (Fv F v) × Matrix (Fin a') (Fin (a + a')) (Fv F v),
      GlobalTheory.SwapSlice.sliceT ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂)) Φ) Z =
        GlobalTheory.LatVac.psiAt B.ψ v (-GlobalTheory.FlipMatch.pairM Z.1 (GlobalTheory.FlipMatch.coX t 1 1 u₁ᵀ) +
                     GlobalTheory.FlipMatch.pairM Z.2 (GlobalTheory.FlipMatch.coX t 1 1 u₂ᵀ)) *
          GlobalTheory.SwapSlice.sliceT ι Φ (Z.1 + GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 u₁ᵀ,
            Z.2 + GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 u₂ᵀ) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT hdV hdW v t ι hι d' hd' dd hdd u₁ u₂ hu₁ hu₂ hp₁ hp₂ Φ hΦ Z
  set ψv := GlobalTheory.LatVac.psiAt B.ψ v with hψv
  have hc : Continuous ψv := GlobalTheory.SchrSB.continuous_psiAt B.ψ hT.base.std.1 v
  have hstar : ∀ y, starRingEnd ℂ (ψv y) = ψv (-y) := fun y => GlobalTheory.DblVacLine.star_psiAt B.ψ hT.base.std.1 v y
  have hatT : ∀ u : Matrix (Fin (a + a')) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u → At (evFin F v) uᵀ :=
    fun u hu r hr => by rw [← Matrix.transpose_smul, hu r hr, Matrix.transpose_zero]
  have Heisenberg₂ : ∀ u : Matrix (Fin (a + a')) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u →
      pairM (coX t 1 1 uᵀ) (coY σ G.V' G.W t 1 1 uᵀ) = 0 →
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ Y,
        ι (schr ψv (GlobalTheory.LatVac.locCo G.M'.co v uᵀ) φ) Y =
          ψv (-pairM Y (coX t 1 1 uᵀ)) * ι φ (Y + coY σ G.V' G.W t 1 1 uᵀ) := by
    intro u hu hp φ hφ Y
    exact (GlobalTheory.HeisFlip.heis_trans_char hT.base.cm G.V' G.W hT.geo.hV'.herm hT.geo.hW.skew hdV hdW G.M' B.ψ
      hT.base.std t 1 1 uᵀ (hatT u hu) hp φ hφ _ (GlobalTheory.SchrSB.schr_mem_SB B.ψ hT.base.std.1 v _ φ hφ)
      (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v uᵀ (hatT u hu) φ)).2 ι hι Y
  have hloc : GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂) =
      (Sum.elim (GlobalTheory.LatVac.locCo G.M'.co v u₁ᵀ).1 (GlobalTheory.LatVac.locCo G.M'.co v u₂ᵀ).1,
        Sum.elim (GlobalTheory.LatVac.locCo G.M'.co v u₁ᵀ).2 (-(GlobalTheory.LatVac.locCo G.M'.co v u₂ᵀ).2)) := by
    have e1 := hd' u₁ᵀ
    have e2 := hd' u₂ᵀ
    rw [Matrix.transpose_transpose] at e1 e2
    have h := hdd u₁ u₂
    ext k <;> cases k <;> simp [GlobalTheory.LatVac.locCo, h, e1, e2]
  have hconjSB : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), (fun x => starRingEnd ℂ (φ x)) ∈ SB _ :=
    fun φ hφ => ⟨hφ.1.comp _, hφ.2.comp_left (map_zero _)⟩
  have hconj : ∀ (w : (Fin a' × Fin (a + a') → Fv F v) × (Fin a' × Fin (a + a') → Fv F v))
      (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (fun x => starRingEnd ℂ (schr ψv (w.1, -w.2) φ x)) = schr ψv w (fun x => starRingEnd ℂ (φ x)) := by
    intro w φ
    funext x
    simp only [GlobalTheory.WeilM.schr, map_mul, hstar]
    congr 2
    rw [dotProduct_neg, dotProduct_neg]
    ring
  have hbox : ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₂ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      GlobalTheory.SwapSlice.sliceT ι (schr ψv (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂)) (boxFun φ₁ φ₂)) Z =
        ψv (-pairM Z.1 (coX t 1 1 u₁ᵀ) + pairM Z.2 (coX t 1 1 u₂ᵀ)) *
          GlobalTheory.SwapSlice.sliceT ι (boxFun φ₁ φ₂) (Z.1 + coY σ G.V' G.W t 1 1 u₁ᵀ, Z.2 + coY σ G.V' G.W t 1 1 u₂ᵀ) := by
    intro φ₁ h₁ φ₂ h₂
    rw [hloc, GlobalTheory.BoxSpan.schr_boxFun, GlobalTheory.SwapSlice.sliceT_boxFun, GlobalTheory.SwapSlice.sliceT_boxFun]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Prod.mk.eta]
    rw [GlobalTheory.SwapSlice.barL_apply, GlobalTheory.SwapSlice.barL_apply, hconj (GlobalTheory.LatVac.locCo G.M'.co v u₂ᵀ),
      Heisenberg₂ u₁ hu₁ hp₁ φ₁ h₁, Heisenberg₂ u₂ hu₂ hp₂ _ (hconjSB φ₂ h₂), map_mul, hstar, neg_neg, AddChar.map_add_eq_mul]
    ring
  let Lw : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ]
      ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
    { toFun := schr ψv (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂))
      map_add' := fun f g => by funext x; simp [schr, mul_add]
      map_smul' := fun c f => by funext x; simp [schr]; ring }
  let Z' : Matrix (Fin a') (Fin (a + a')) (Fv F v) × Matrix (Fin a') (Fin (a + a')) (Fv F v) :=
    (Z.1 + coY σ G.V' G.W t 1 1 u₁ᵀ, Z.2 + coY σ G.V' G.W t 1 1 u₂ᵀ)
  let c : ℂ := ψv (-pairM Z.1 (coX t 1 1 u₁ᵀ) + pairM Z.2 (coX t 1 1 u₂ᵀ))
  let Λ : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ :=
    (LinearMap.proj Z).comp ((GlobalTheory.SwapSlice.sliceT ι).comp Lw) - c • (LinearMap.proj Z').comp (GlobalTheory.SwapSlice.sliceT ι)
  have hΛ : ∀ Ψ, Λ Ψ = GlobalTheory.SwapSlice.sliceT ι (schr ψv (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂)) Ψ) Z -
      c * GlobalTheory.SwapSlice.sliceT ι Ψ Z' := fun Ψ => rfl
  have h0 := GlobalTheory.BoxSpan.boxSpan_ker F v (Fin a' × Fin (a + a')) (Fin a' × Fin (a + a')) ψv hc
    (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hT.base.std v) Λ
    (fun φ₁ h₁ φ₂ h₂ => by rw [hΛ, hbox φ₁ h₁ φ₂ h₂, sub_self]) Φ hΦ
  rw [hΛ, sub_eq_zero] at h0
  exact h0

end GlobalTheory.SwapHeis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAtCoord
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace GlobalTheory.SplitCoord

theorem exists_at_coord : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d), X.J.det ≠ 0 → Y.J.det ≠ 0 → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (Z : Matrix (Fin n) (Fin d) (Fv F v)),
    (∃ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) x ∧ x.map (piW t) = 0 ∧
      GlobalTheory.FlipMatch.coY σ X Y t 1 1 x = Z) ∧
    (∃ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) x ∧ x.map (piW (t.comp σ)) = 0 ∧
      GlobalTheory.FlipMatch.coX t 1 1 x = Z) := by
  intro F E _ _ _ _ _ σ hcm n d X Y hdX hdY v t Z
  have hA : IsUnit (X.J.map t).det := by
    rw [show (X.J.map t).det = (t : E →+* Fv F v) X.J.det from (RingHom.map_det _ _).symm]
    exact isUnit_iff_ne_zero.2 fun h => hdX ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  have hB : IsUnit (Y.J.map t)ᵀ.det := by
    rw [Matrix.det_transpose, show (Y.J.map t).det = (t : E →+* Fv F v) Y.J.det from (RingHom.map_det _ _).symm]
    exact isUnit_iff_ne_zero.2 fun h => hdY ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  constructor
  · obtain ⟨x, hat, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hcm v t (0 : Matrix (Fin n) (Fin d) (Fv F v))
      (-((X.J.map t)⁻¹ * Z * ((Y.J.map t)ᵀ)⁻¹))
    refine ⟨x, hat, h0, ?_⟩
    simp only [GlobalTheory.FlipMatch.coY, h1, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, Units.val_one,
      Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hA, Matrix.nonsing_inv_mul _ hB, Matrix.mul_one]
  · obtain ⟨x, hat, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hcm v t Z (0 : Matrix (Fin n) (Fin d) (Fv F v))
    refine ⟨x, hat, h1, ?_⟩
    simp only [GlobalTheory.FlipMatch.coX, h0, inv_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.SplitCoord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarModelLocalTriple
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
noncomputable section

namespace GlobalTheory.SwapSchur

open GlobalTheory.SwapSlice

def splitC {R : Type} {m n : ℕ} (Y : Matrix (Fin m) (Fin (n + n)) R) :
    Matrix (Fin m) (Fin n) R × Matrix (Fin m) (Fin n) R :=
  (fun i j => Y i (Fin.castAdd n j), fun i j => Y i (Fin.natAdd n j))

def joinC {R : Type} {m n : ℕ} (Z : Matrix (Fin m) (Fin n) R × Matrix (Fin m) (Fin n) R) :
    Matrix (Fin m) (Fin (n + n)) R :=
  fun i => Fin.append (Z.1 i) (Z.2 i)

theorem splitC_joinC {R : Type} {m n : ℕ} (Z : Matrix (Fin m) (Fin n) R × Matrix (Fin m) (Fin n) R) :
    splitC (joinC Z) = Z := by
  rcases Z with ⟨Z₁, Z₂⟩
  simp only [splitC, joinC, Fin.append_left, Fin.append_right]

theorem joinC_splitC {R : Type} {m n : ℕ} (Y : Matrix (Fin m) (Fin (n + n)) R) : joinC (splitC Y) = Y := by
  funext i
  exact Fin.append_castAdd_natAdd

theorem splitC_add {R : Type} [Add R] {m n : ℕ} (Y C : Matrix (Fin m) (Fin (n + n)) R) :
    splitC (Y + C) = splitC Y + splitC C := rfl

theorem swapNeg_swapNeg {Y : Type} [InvolutiveNeg Y] (Z : Y × Y) : swapNeg (swapNeg Z) = Z := by
  simp [swapNeg]

def swapH {k : Type} [TopologicalSpace k] [AddGroup k] [IsTopologicalAddGroup k] {m n : ℕ} :
    Matrix (Fin m) (Fin (n + n)) k ≃ₜ (Matrix (Fin m) (Fin n) k × Matrix (Fin m) (Fin n) k) where
  toFun Y := swapNeg (splitC Y)
  invFun Z := joinC (swapNeg Z)
  left_inv Y := by
    show joinC (swapNeg (swapNeg (splitC Y))) = Y
    rw [swapNeg_swapNeg, joinC_splitC]
  right_inv Z := by
    show swapNeg (splitC (joinC (swapNeg Z))) = Z
    rw [splitC_joinC, swapNeg_swapNeg]
  continuous_toFun := by
    have h1 : Continuous fun Y : Matrix (Fin m) (Fin (n + n)) k => (splitC Y).1 :=
      continuous_matrix fun i j => continuous_id.matrix_elem i (Fin.castAdd n j)
    have h2 : Continuous fun Y : Matrix (Fin m) (Fin (n + n)) k => (splitC Y).2 :=
      continuous_matrix fun i j => continuous_id.matrix_elem i (Fin.natAdd n j)
    exact h2.neg.prodMk h1.neg
  continuous_invFun := by
    refine continuous_matrix fun i j => ?_
    cases j using Fin.addCases with
    | left j =>
      simp only [joinC, swapNeg, Fin.append_left, Matrix.neg_apply]
      exact (continuous_snd.matrix_elem i j).neg
    | right j =>
      simp only [joinC, swapNeg, Fin.append_right, Matrix.neg_apply]
      exact (continuous_fst.matrix_elem i j).neg

theorem comp_mem_SB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {g : Y → ℂ}
    (hg : g ∈ SB Y) : g ∘ e ∈ SB X :=
  ⟨hg.1.comp_continuous e.continuous, hg.2.comp_homeomorph e⟩

theorem bijOn_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Set.BijOn (fun g : Y → ℂ => g ∘ e) (SB Y : Set (Y → ℂ)) (SB X : Set (X → ℂ)) := by
  refine ⟨fun g hg => comp_mem_SB e hg, fun g _ g' _ h => funext fun y => ?_, fun f hf => ?_⟩
  · have := congrFun h (e.symm y)
    simpa using this
  · refine ⟨f ∘ e.symm, comp_mem_SB e.symm hf, ?_⟩
    funext x
    simp

theorem pairM_neg_left {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (X Y : Matrix A C k) :
    GlobalTheory.FlipMatch.pairM (-X) Y = -GlobalTheory.FlipMatch.pairM X Y := by
  simp [GlobalTheory.FlipMatch.pairM, Finset.sum_neg_distrib]

theorem pairM_zero_right {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (X : Matrix A C k) :
    GlobalTheory.FlipMatch.pairM X 0 = 0 := by
  simp [GlobalTheory.FlipMatch.pairM]

theorem pairM_zero_left {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (Y : Matrix A C k) :
    GlobalTheory.FlipMatch.pairM 0 Y = 0 := by
  simp [GlobalTheory.FlipMatch.pairM]

def formR {k : Type} [CommRing k] {m n : ℕ} (l : Matrix (Fin m) (Fin (n + n)) k →ₗ[k] k) : Matrix (Fin m) (Fin n) k :=
  fun i j => l (Matrix.single i (Fin.natAdd n j) 1)

def formL {k : Type} [CommRing k] {m n : ℕ} (l : Matrix (Fin m) (Fin (n + n)) k →ₗ[k] k) : Matrix (Fin m) (Fin n) k :=
  fun i j => -l (Matrix.single i (Fin.castAdd n j) 1)

theorem linForm_eq {k : Type} [CommRing k] {m n : ℕ} (l : Matrix (Fin m) (Fin (n + n)) k →ₗ[k] k)
    (Y : Matrix (Fin m) (Fin (n + n)) k) :
    l Y = GlobalTheory.FlipMatch.pairM (splitC Y).2 (formR l) -
      GlobalTheory.FlipMatch.pairM (splitC Y).1 (formL l) := by
  have e : ∀ i j, l (Matrix.single i j (Y i j)) = Y i j * l (Matrix.single i j 1) := fun i j => by
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, e]
  simp only [GlobalTheory.FlipMatch.pairM, splitC, formR, formL, Fin.sum_univ_add, mul_neg, Finset.sum_neg_distrib,
    sub_neg_eq_add, Finset.sum_add_distrib]
  ring

end GlobalTheory.SwapSchur


open GlobalTheory.SwapSchur in
theorem GlobalTheory.SwapSchur.sliceT_swap_eq_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (f : AE F E), GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl (incM F G.V'.J)),
      ((w : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (AE F E))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    ∀ S : (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) → ℂ) →
        ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) → ℂ,
    (∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      S Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v)) →
    (∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      ∀ Φ' ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), ∀ c : ℂ, S (c • Φ + Φ') = c • S Φ + S Φ') →
    (∀ u, At (evFin F v) u → ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) =
        schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (actB (cA σ) w u)) (S Φ)) →
    ∃ c : ℂ, ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      GlobalTheory.SwapSlice.sliceT ι (S Φ) = c • (GlobalTheory.SwapSlice.sliceT ι Φ ∘ GlobalTheory.SwapSlice.swapNeg) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v t ι hι d' hd' dd hdd f hf1 hf2 hf3 hf4 hf5 w hw S hSB hSlin hS
  classical
  obtain ⟨hdV', hdW⟩ := GlobalTheory.GramDet.gram_det_ne_zero F E σ B a a' G X om om' hT
  have hcm : IsCMExt F E σ := hT.base.cm
  have hstd : IsStd B.ψ := hT.base.std
  have hψc : Continuous B.ψ := hstd.1
  have hcont : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hψc v
  have hne : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hstd v
  have hι' : G.M'.IsLin B.ψ (piW (t.comp σ)) (piW t)
      (fun u => -((1 : GL (Fin a') (Fv F v)).1ᵀ * G.V'.J.map t * u.map (piW (t.comp σ)) * (G.W.J.map t)ᵀ *
        (1 : GL (Fin (a + a')) (Fv F v)).1)) ι := hι
  have hbij := GlobalTheory.SwapSliceBij.sliceT_bijOn ι hι'.bij
  obtain ⟨-, hw2⟩ := GlobalTheory.SwapAtPlace.swap_at_acts σ hcm (d := a + a') (incM F G.V'.J) v t f hf1 hf2 hf3 hf4 hf5 w hw
  have hheis := GlobalTheory.SwapHeis.heis_sliceT F E σ B a a' G X om om' hT hdV' hdW v t ι hι d' hd' dd hdd
  choose xY hxYat hxY0 hxY using fun Z => (GlobalTheory.SplitCoord.exists_at_coord σ hcm G.V' G.W hdV' hdW v t Z).1
  choose xX hxXat hxX0 hxX using fun Z => (GlobalTheory.SplitCoord.exists_at_coord σ hcm G.V' G.W hdV' hdW v t Z).2

  have atT : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x → At (evFin F v) xᵀ :=
    fun x hx r hr => by rw [← Matrix.transpose_smul, hx r hr, Matrix.transpose_zero]
  have atNeg : ∀ x : Matrix (Fin (a + a')) (Fin a') (AE F E), At (evFin F v) x → At (evFin F v) (-x) :=
    fun x hx r hr => by rw [smul_neg, hx r hr, neg_zero]
  have atCols : ∀ u₁ u₂ : Matrix (Fin (a + a')) (Fin a') (AE F E), At (evFin F v) u₁ → At (evFin F v) u₂ →
      At (evFin F v) (Matrix.fromCols u₁ u₂) := by
    intro u₁ u₂ h1 h2 r hr
    ext i j
    cases j with
    | inl j => simpa using congrFun (congrFun (h1 r hr) i) j
    | inr j => simpa using congrFun (congrFun (h2 r hr) i) j

  have coX0 : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), x.map (piW t) = 0 → GlobalTheory.FlipMatch.coX t 1 1 x = 0 := by
    intro x hx; simp [GlobalTheory.FlipMatch.coX, hx]
  have coY0 : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), x.map (piW (t.comp σ)) = 0 →
      GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x = 0 := by
    intro x hx; simp [GlobalTheory.FlipMatch.coY, hx]
  have mapNeg : ∀ (π : AE F E →+* Fv F v) (x : Matrix (Fin a') (Fin (a + a')) (AE F E)), (-x).map π = -x.map π := by
    intro π x; ext i j; simp
  have coXneg : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E),
      GlobalTheory.FlipMatch.coX t 1 1 (-x) = -GlobalTheory.FlipMatch.coX t 1 1 x := by
    intro x; simp only [GlobalTheory.FlipMatch.coX, mapNeg]; simp [Matrix.mul_neg, Matrix.neg_mul]
  have coYneg : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E),
      GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 (-x) = -GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x := by
    intro x; simp only [GlobalTheory.FlipMatch.coY, mapNeg]; simp [Matrix.mul_neg, Matrix.neg_mul]

  let hH : Matrix (Fin a') (Fin ((a + a') + (a + a'))) (Fv F v) ≃ₜ
      (Matrix (Fin a') (Fin (a + a')) (Fv F v) × Matrix (Fin a') (Fin (a + a')) (Fv F v)) := swapH
  let ι₁ := (LinearMap.funLeft ℂ ℂ hH) ∘ₗ GlobalTheory.SwapSlice.sliceT ι
  have hι₁ : ∀ Φ Y, ι₁ Φ Y = GlobalTheory.SwapSlice.sliceT ι Φ (GlobalTheory.SwapSlice.swapNeg (splitC Y)) := fun _ _ => rfl
  let ι₂ : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) →
      Matrix (Fin a') (Fin ((a + a') + (a + a'))) (Fv F v) → ℂ :=
    fun Φ Y => GlobalTheory.SwapSlice.sliceT ι (S Φ) (splitC Y)
  have hbij₁ : Set.BijOn ι₁ (SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) : Set _)
      (SB (Matrix (Fin a') (Fin ((a + a') + (a + a'))) (Fv F v)) : Set _) :=
    (bijOn_comp hH).comp hbij
  have hlin₂ : ∀ x ∈ SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v),
      ∀ y ∈ SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v), ∀ c : ℂ, ι₂ (c • x + y) = c • ι₂ x + ι₂ y := by
    intro x hx y hy c
    funext Y
    simp only [ι₂, hSlin x hx y hy c, map_add (f := _), map_smul, Pi.add_apply, Pi.smul_apply]

  have tMap : ∀ (π : AE F E →+* Fv F v) (x : Matrix (Fin a') (Fin (a + a')) (AE F E)), x.map π = 0 → xᵀ.map π = 0 := by
    intro π x hx; rw [Matrix.transpose_map, hx, Matrix.transpose_zero]
  have tNeg : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), (-xᵀ)ᵀ = -x := by
    intro x; rw [Matrix.transpose_neg, Matrix.transpose_transpose]
  have tr1 : ∀ x₁ x₂ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x₁ → At (evFin F v) x₂ →
      x₁.map (piW t) = 0 → x₂.map (piW t) = 0 →
      ∀ x ∈ SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v), ∀ Z,
      GlobalTheory.SwapSlice.sliceT ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols x₁ᵀ x₂ᵀ)) x) Z =
        GlobalTheory.SwapSlice.sliceT ι x (Z.1 + GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x₁, Z.2 + GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x₂) := by
    intro x₁ x₂ a1 a2 m1 m2 x hx Z
    have c1 : GlobalTheory.FlipMatch.coX t 1 1 x₁ᵀᵀ = 0 := by rw [Matrix.transpose_transpose]; exact coX0 _ m1
    have c2 : GlobalTheory.FlipMatch.coX t 1 1 x₂ᵀᵀ = 0 := by rw [Matrix.transpose_transpose]; exact coX0 _ m2
    have h := hheis x₁ᵀ x₂ᵀ (atT _ a1) (atT _ a2) (by rw [c1, pairM_zero_left]) (by rw [c2, pairM_zero_left]) x hx Z
    rw [c1, c2] at h
    set_option backward.isDefEq.respectTransparency false in
    simpa only [Matrix.transpose_transpose, pairM_zero_right, neg_zero, add_zero, AddChar.map_zero_eq_one, one_mul] using h
  have tr2 : ∀ x₁ x₂ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x₁ → At (evFin F v) x₂ →
      x₁.map (piW t) = 0 → x₂.map (piW t) = 0 →
      ∀ x ∈ SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v), ∀ Z,
      GlobalTheory.SwapSlice.sliceT ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols x₁ᵀ x₂ᵀ)) x)) Z =
        GlobalTheory.SwapSlice.sliceT ι (S x) (Z.1 - GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x₂, Z.2 - GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x₁) := by
    intro x₁ x₂ a1 a2 m1 m2 x hx Z
    have c1 : GlobalTheory.FlipMatch.coX t 1 1 (-x₁ᵀ)ᵀ = 0 := by rw [tNeg, coXneg, coX0 _ m1, neg_zero]
    have c2 : GlobalTheory.FlipMatch.coX t 1 1 (-x₂ᵀ)ᵀ = 0 := by rw [tNeg, coXneg, coX0 _ m2, neg_zero]
    rw [hS _ (atCols _ _ (atT _ a1) (atT _ a2)) x hx, (hw2 _ _ (atT _ a1) (atT _ a2)).1 (tMap _ _ m1) (tMap _ _ m2)]
    have h := hheis (-x₂ᵀ) (-x₁ᵀ) (atNeg _ (atT _ a2)) (atNeg _ (atT _ a1)) (by rw [c2, pairM_zero_left])
        (by rw [c1, pairM_zero_left]) (S x) (hSB x hx) Z
    rw [c2, c1] at h
    set_option backward.isDefEq.respectTransparency false in
    simpa only [tNeg, coYneg, pairM_zero_right, neg_zero, add_zero, AddChar.map_zero_eq_one, one_mul, sub_eq_add_neg] using h
  have mu1 : ∀ x₁ x₂ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x₁ → At (evFin F v) x₂ →
      x₁.map (piW (t.comp σ)) = 0 → x₂.map (piW (t.comp σ)) = 0 →
      ∀ x ∈ SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v), ∀ Z,
      GlobalTheory.SwapSlice.sliceT ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols x₁ᵀ x₂ᵀ)) x) Z =
        GlobalTheory.LatVac.psiAt B.ψ v (-GlobalTheory.FlipMatch.pairM Z.1 (GlobalTheory.FlipMatch.coX t 1 1 x₁) +
          GlobalTheory.FlipMatch.pairM Z.2 (GlobalTheory.FlipMatch.coX t 1 1 x₂)) * GlobalTheory.SwapSlice.sliceT ι x Z := by
    intro x₁ x₂ a1 a2 m1 m2 x hx Z
    have c1 : GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x₁ᵀᵀ = 0 := by rw [Matrix.transpose_transpose]; exact coY0 _ m1
    have c2 : GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x₂ᵀᵀ = 0 := by rw [Matrix.transpose_transpose]; exact coY0 _ m2
    have h := hheis x₁ᵀ x₂ᵀ (atT _ a1) (atT _ a2) (by rw [c1, pairM_zero_right]) (by rw [c2, pairM_zero_right]) x hx Z
    rw [c1, c2] at h
    set_option backward.isDefEq.respectTransparency false in
    simpa only [Matrix.transpose_transpose, add_zero, Prod.mk.eta] using h
  have mu2 : ∀ x₁ x₂ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x₁ → At (evFin F v) x₂ →
      x₁.map (piW (t.comp σ)) = 0 → x₂.map (piW (t.comp σ)) = 0 →
      ∀ x ∈ SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v), ∀ Z,
      GlobalTheory.SwapSlice.sliceT ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols x₁ᵀ x₂ᵀ)) x)) Z =
        GlobalTheory.LatVac.psiAt B.ψ v (-GlobalTheory.FlipMatch.pairM Z.1 (GlobalTheory.FlipMatch.coX t 1 1 x₂) +
          GlobalTheory.FlipMatch.pairM Z.2 (GlobalTheory.FlipMatch.coX t 1 1 x₁)) * GlobalTheory.SwapSlice.sliceT ι (S x) Z := by
    intro x₁ x₂ a1 a2 m1 m2 x hx Z
    rw [hS _ (atCols _ _ (atT _ a1) (atT _ a2)) x hx, (hw2 _ _ (atT _ a1) (atT _ a2)).2 (tMap _ _ m1) (tMap _ _ m2)]
    exact mu1 x₂ x₁ a2 a1 m2 m1 (S x) (hSB x hx) Z
  obtain ⟨c, hc⟩ := GlobalTheory.LinSchur.eq_smul_of_commute (SB _) (GlobalTheory.LatVac.psiAt B.ψ v) hcont hne ι₁ ι₂ hbij₁ hlin₂
    (fun C x => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v
      (Matrix.fromCols (xY (-(splitC C).2))ᵀ (xY (-(splitC C).1))ᵀ)) x)
    (fun l x => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v
      (Matrix.fromCols (xX (formR l))ᵀ (xX (formL l))ᵀ)) x)
    (fun C x hx => ⟨GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ x hx, funext fun Y => by
        beta_reduce
        rw [hι₁, tr1 _ _ (hxYat _) (hxYat _) (hxY0 _) (hxY0 _) x hx, hxY, hxY, hι₁]
        simp only [GlobalTheory.SwapSlice.swapNeg, splitC_add, Prod.fst_add, Prod.snd_add, neg_add],
      funext fun Y => by
        beta_reduce
        show GlobalTheory.SwapSlice.sliceT ι (S _) (splitC Y) = GlobalTheory.SwapSlice.sliceT ι (S x) (splitC (Y + C))
        rw [tr2 _ _ (hxYat _) (hxYat _) (hxY0 _) (hxY0 _) x hx, hxY, hxY]
        simp only [splitC_add, sub_neg_eq_add]
        rfl⟩)
    (fun l x hx => ⟨GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ x hx, funext fun Y => by
        beta_reduce
        rw [hι₁, mu1 _ _ (hxXat _) (hxXat _) (hxX0 _) (hxX0 _) x hx, hxX, hxX, hι₁, linForm_eq l Y]
        congr 2
        simp only [GlobalTheory.SwapSlice.swapNeg, pairM_neg_left]
        ring,
      funext fun Y => by
        beta_reduce
        show GlobalTheory.SwapSlice.sliceT ι (S _) (splitC Y) = _ * GlobalTheory.SwapSlice.sliceT ι (S x) (splitC Y)
        rw [mu2 _ _ (hxXat _) (hxXat _) (hxX0 _) (hxX0 _) x hx, hxX, hxX, linForm_eq l Y]
        congr 2
        ring⟩)
  refine ⟨c, fun Φ hΦ => funext fun Z => ?_⟩
  have e : GlobalTheory.SwapSlice.sliceT ι (S Φ) (splitC (joinC Z)) =
      c * GlobalTheory.SwapSlice.sliceT ι Φ (GlobalTheory.SwapSlice.swapNeg (splitC (joinC Z))) := congrFun (hc Φ hΦ) (joinC Z)
  rw [splitC_joinC] at e
  exact e
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarModelLocalTripleStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_bar_model_local_triple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl (incM F G.V'.J)),
      ((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    ∀ S : (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) → ℂ) →
        ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) → ℂ,
    (∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      S Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v)) →
    (∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      ∀ Φ' ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), ∀ c : ℂ, S (c • Φ + Φ') = c • S Φ + S Φ') →
    (∀ u, At (evFin F v) u → ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) =
        schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (actB (cA σ) w u)) (S Φ)) →
    ∃ c : ℂ, ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      GlobalTheory.SwapSlice.sliceT ι (S Φ) = c • (GlobalTheory.SwapSlice.sliceT ι Φ ∘ GlobalTheory.SwapSlice.swapNeg) := by
  first | exact @GlobalTheory.SwapSchur.sliceT_swap_eq_smul | exact GlobalTheory.SwapSchur.sliceT_swap_eq_smul | (intros; apply GlobalTheory.SwapSchur.sliceT_swap_eq_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplittingPreservesLocalSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplittingPreservesLocalSchwartz
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace GlobalTheory.LocSplitOp

theorem exists_locOp : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {Bf : W → W → AF F} {κ : Type} [Fintype κ]
    (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ {G : Type} [Group G] (act : G → W → W) (om : G →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsSplitting (adeleClass F) ψ dd act om →
    ∀ (v : Pl (F := F)) (p : G), (∀ u, At (evFin F v) u → At (evFin F v) (act p u)) →
    (∀ Φ ∈ SB (κ → Fv F v), ∃ Φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (om p) Φ Φ₁) →
    ∃ S : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ,
      (∀ Φ ∈ SB (κ → Fv F v), S Φ ∈ SB (κ → Fv F v) ∧ Acts (evFin F v) (om p) Φ (S Φ)) ∧
      ∀ u, At (evFin F v) u → ∀ Φ ∈ SB (κ → Fv F v),
        S (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) =
          schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v (act p u)) (S Φ) := by
  intro F _ _ W _ _ Bf κ _ dd ψ hψ G _ act om hsp v p hat hex
  choose! S hS using hex
  refine ⟨S, hS, ?_⟩
  intro u hu Φ hΦ
  have hc : Continuous ψ := hψ.1
  have hw := GlobalTheory.SchrSB.schr_mem_SB ψ hc v (GlobalTheory.LatVac.locCo dd v u) Φ hΦ
  have restS : ∀ r, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) Φ r → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) (S Φ) r :=
    fun r hr => ⟨hr.1, by rw [← (hS Φ hΦ).2 r hr]; exact hsp.pres p _ hr.2⟩
  refine GlobalTheory.TensUniq.eq_of_tens_eq v Φ _ _ hΦ fun r hr => ?_
  have hb1 := GlobalTheory.VacBridge.rho_acts_locCo dd ψ v u hu Φ r hr
  have hRw : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v)
      (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) r :=
    ⟨hr.1, by rw [← hb1]; exact GlobalTheory.SchrKeepsSchA.schr_mem_schA F ψ hψ κ _ _ hr.2⟩
  rw [← (hS _ hw).2 r hRw, ← hb1, hsp.impl _ _ _ hr.2, (hS Φ hΦ).2 r hr,
    GlobalTheory.VacBridge.rho_acts_locCo dd ψ v _ (hat u hu) (S Φ) r (restS r hr)]

end GlobalTheory.LocSplitOp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplittingPreservesLocalSchwartzStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitting_preserves_local_schwartz : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {Bf : W → W → AF F} {κ : Type} [Fintype κ]
    (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ {G : Type} [Group G] (act : G → W → W) (om : G →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsSplitting (adeleClass F) ψ dd act om →
    ∀ (v : Pl (F := F)) (p : G), (∀ u, At (evFin F v) u → At (evFin F v) (act p u)) →
    (∀ Φ ∈ SB (κ → Fv F v), ∃ Φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (om p) Φ Φ₁) →
    ∃ S : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ,
      (∀ Φ ∈ SB (κ → Fv F v), S Φ ∈ SB (κ → Fv F v) ∧ Acts (evFin F v) (om p) Φ (S Φ)) ∧
      ∀ u, At (evFin F v) u → ∀ Φ ∈ SB (κ → Fv F v),
        S (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) =
          schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v (act p u)) (S Φ) := by
  first | exact @GlobalTheory.LocSplitOp.exists_locOp | exact GlobalTheory.LocSplitOp.exists_locOp | (intros; apply GlobalTheory.LocSplitOp.exists_locOp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelLocalGoodPlace
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SwapActs

theorem swap_acts_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
    ∀ (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl (incM F G.V'.J)),
      ((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    ∃ c : ℂ, ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      ∀ ψ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ ψ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      ι ψ₁ = (fun Y => starRingEnd ℂ (ι (fun y => starRingEnd ℂ (φ₂ y)) (-Y))) →
      ι (fun y => starRingEnd ℂ (ψ₂ y)) = (fun Y => starRingEnd ℂ (ι φ₁ (-Y))) →
      Acts (evFin F v) (omd w) (boxFun φ₁ φ₂) (c • boxFun ψ₁ ψ₂) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv t ι hι d' hd' dd hdd omd hspl f hf1 hf2 hf3 hf4 hf5 w hw
  have hcm : IsCMExt F E σ := hT.base.cm
  obtain ⟨hAt, -⟩ := GlobalTheory.T.local_idempotent_character_value σ hcm (incM F G.V'.J) (d := a + a') v t f hf1 hf2 hf3 hf4 hf5 w hw
  have atAct : ∀ u : Matrix (Fin (a + a')) (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u →
      At (evFin F v) (actB (cA σ) w u) := by
    intro u hu r hr
    simp only [actB]
    rw [← Matrix.smul_mul, hu r hr, Matrix.zero_mul]
  have hex := GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace F E σ B a a' G hT.base dd omd hspl v w hAt
  obtain ⟨S, hS, hSh⟩ := GlobalTheory.T.splitting_preserves_local_schwartz dd B.ψ hT.base.std (actB (cA σ)) omd hspl.toIsSplitting v w atAct hex
  have hSlin := GlobalTheory.LocWeilAct.linear_of_acts v (omd w) S hS
  obtain ⟨c, hc⟩ := GlobalTheory.T.linear_bar_model_local_triple F E σ B a a' G X om om' hT v t ι hι d' hd' dd hdd f hf1 hf2 hf3 hf4 hf5 w hw S
    (fun Φ hΦ => (hS Φ hΦ).1) hSlin hSh
  refine ⟨c, fun φ₁ h₁ φ₂ h₂ ψ₁ k₁ ψ₂ k₂ e₁ e₂ => ?_⟩
  have hbij := GlobalTheory.T.slice_transform_schwartz_bijective ι hι.bij
  have hΦ := GlobalTheory.BoxSpan.boxFun_mem_SB' h₁ h₂
  have hΨ : c • boxFun ψ₁ ψ₂ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) :=
    (SB _).smul_mem c (GlobalTheory.BoxSpan.boxFun_mem_SB' k₁ k₂)
  have key : S (boxFun φ₁ φ₂) = c • boxFun ψ₁ ψ₂ := by
    refine hbij.injOn (hS _ hΦ).1 hΨ ?_
    rw [hc _ hΦ, map_smul]
    congr 1
    funext Z
    rw [Function.comp_apply, GlobalTheory.SwapSlice.sliceT_boxFun, GlobalTheory.SwapSlice.sliceT_boxFun, GlobalTheory.SwapSlice.swapNeg_apply,
      GlobalTheory.SwapSlice.barL_apply, GlobalTheory.SwapSlice.barL_apply, e₁, e₂]
    simp only [Complex.conj_conj]
    ring
  have h := (hS _ hΦ).2
  rwa [key] at h

end GlobalTheory.SwapActs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelLocalGoodPlaceStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_local_good_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
    ∀ (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl (incM F G.V'.J)),
      ((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    ∃ c : ℂ, ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      ∀ ψ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ ψ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      ι ψ₁ = (fun Y => starRingEnd ℂ (ι (fun y => starRingEnd ℂ (φ₂ y)) (-Y))) →
      ι (fun y => starRingEnd ℂ (ψ₂ y)) = (fun Y => starRingEnd ℂ (ι φ₁ (-Y))) →
      Acts (evFin F v) (omd w) (boxFun φ₁ φ₂) (c • boxFun ψ₁ ψ₂) := by
  first | exact @GlobalTheory.SwapActs.swap_acts_box | exact GlobalTheory.SwapActs.swap_acts_box | (intros; apply GlobalTheory.SwapActs.swap_acts_box <;> assumption)
end

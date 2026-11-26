module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIrreducibleSmoothAdmissible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatGlueLatIffDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandPairSphericalVectorUnique

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsFixedOfFinset
noncomputable section

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AutMult
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RestT

section Local

variable {G X H : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {δ : G →* (X →L[ℂ] X)} {ρ : G →* (H →L[ℂ] H)} {A : X → X → (H →L[ℂ] H)}

def IsOpFam (δ : G →* (X →L[ℂ] X)) (ρ : G →* (H →L[ℂ] H)) (A : X → X → (H →L[ℂ] H)) : Prop :=
  ∀ y ξ, ∀ T ∈ homIn δ ρ ⊤, ∀ x, A y ξ (T x) = ⟪ξ, x⟫_ℂ • T y

theorem ext_of_hom (hi : IsIsotypic δ ρ) {C D : H →L[ℂ] H}
    (h : ∀ T ∈ homIn δ ρ ⊤, ∀ x, C (T x) = D (T x)) : C = D := by
  have hle : isoPart δ ρ ⊤ ≤ LinearMap.ker ((C - D : H →L[ℂ] H) : H →ₗ[ℂ] H) :=
    isoPart_le (ContinuousLinearMap.isClosed_ker (C - D)) fun T hT x => by
      simp [h T hT x]
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v ∈ LinearMap.ker ((C - D : H →L[ℂ] H) : H →ₗ[ℂ] H) :=
    hle (by rw [show isoPart δ ρ ⊤ = ⊤ from hi]; exact Submodule.mem_top)
  simpa [sub_eq_zero] using hv

theorem eq_zero_of_hom [CompleteSpace H] (hi : IsIsotypic δ ρ) {v : H}
    (h : ∀ T ∈ homIn δ ρ ⊤, ∀ x, ⟪T x, v⟫_ℂ = 0) : v = 0 := by
  have hle : isoPart δ ρ ⊤ ≤ (ℂ ∙ v)ᗮ :=
    isoPart_le (Submodule.isClosed_orthogonal _) fun T hT x =>
      Submodule.mem_orthogonal_singleton_iff_inner_left.2 (h T hT x)
  have hv : v ∈ (ℂ ∙ v)ᗮ := hle (by rw [show isoPart δ ρ ⊤ = ⊤ from hi]; exact Submodule.mem_top)
  exact inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_left.1 hv)

theorem IsOpFam.commute (hA : IsOpFam δ ρ A) (hi : IsIsotypic δ ρ) {C : H →L[ℂ] H}
    (hC : ∀ g, Commute C (ρ g)) (y ξ : X) : Commute (A y ξ) C := by
  refine ext_of_hom hi fun T hT x => ?_
  have hCT : C ∘L T ∈ homIn δ ρ ⊤ := mem_homIn_top.2 fun g x => by
    have := DFunLike.congr_fun (hC g) (T x)
    simp only [ContinuousLinearMap.mul_apply] at this
    simp [(mem_homIn_top.1 hT) g x, this]
  have h1 := hA y ξ _ hCT x
  simp only [ContinuousLinearMap.comp_apply] at h1
  simp [h1, hA y ξ T hT x]

theorem IsOpFam.rep_mul (hA : IsOpFam δ ρ A) (hi : IsIsotypic δ ρ) (g : G) (y ξ : X) :
    ρ g * A y ξ = A (δ g y) ξ := by
  refine ext_of_hom hi fun T hT x => ?_
  simp [hA y ξ T hT x, hA (δ g y) ξ T hT x, (mem_homIn_top.1 hT) g y]

theorem IsOpFam.mul (hA : IsOpFam δ ρ A) (hi : IsIsotypic δ ρ) (y ξ y' ξ' : X) :
    A y ξ * A y' ξ' = ⟪ξ, y'⟫_ℂ • A y ξ' := by
  refine ext_of_hom hi fun T hT x => ?_
  simp [hA y' ξ' T hT x, hA y ξ T hT y', hA y ξ' T hT x, smul_smul, mul_comm]

theorem IsOpFam.adjoint_eq [CompleteSpace H] (hA : IsOpFam δ ρ A) (hi : IsIsotypic δ ρ) (hδ : IsIrrUnitary δ)
    (hρ : IsUnitaryRep ρ) (y ξ : X) : ContinuousLinearMap.adjoint (A y ξ) = A ξ y := by
  refine ext_of_hom hi fun T hT x => ?_
  refine sub_eq_zero.1 (eq_zero_of_hom hi fun T' hT' x' => ?_)
  rw [inner_sub_right, ContinuousLinearMap.adjoint_inner_right, hA y ξ T' hT' x', hA ξ y T hT x,
    inner_smul_left, inner_smul_right, inner_eq_be hδ hρ hT hT' x y, inner_eq_be hδ hρ hT hT' ξ x',
    inner_conj_symm]
  ring

theorem adjoint_intertwine [CompleteSpace H] (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ) {T : X →L[ℂ] H}
    (hT : T ∈ homIn δ ρ ⊤) (g : G) (v : H) :
    have := hδ.complete
    ContinuousLinearMap.adjoint T (ρ g v) = δ g (ContinuousLinearMap.adjoint T v) := by
  have := hδ.complete
  refine ext_inner_left ℂ fun u => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, ← inv_inv g, ← hδ.unitary.inner_apply_left,
    ContinuousLinearMap.adjoint_inner_right, ← hρ.inner_apply_left, (mem_homIn_top.1 hT) g⁻¹ u]

theorem IsOpFam.exists_ne_zero [CompleteSpace H] (hA : IsOpFam δ ρ A) (hi : IsIsotypic δ ρ) (hδ : IsIrrUnitary δ)
    (hρ : IsUnitaryRep ρ) {w : H} (hw : w ≠ 0) : ∃ ξ : X, ‖ξ‖ = 1 ∧ A ξ ξ w ≠ 0 := by
  have := hδ.complete
  obtain ⟨T, hT, x, hx⟩ : ∃ T ∈ homIn δ ρ ⊤, ∃ x, ⟪T x, w⟫_ℂ ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hw (eq_zero_of_hom hi hn)
  set z := ContinuousLinearMap.adjoint T w with hz
  have hz0 : z ≠ 0 := fun e => hx (by rw [← ContinuousLinearMap.adjoint_inner_right, ← hz, e, inner_zero_right])
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz0
  refine ⟨(‖z‖ : ℂ)⁻¹ • z, ?_, fun e => ?_⟩
  · simp [norm_smul, hz0]
  set ξ := (‖z‖ : ℂ)⁻¹ • z with hξ
  have h1 : ‖ξ‖ = 1 := by simp [hξ, norm_smul, hz0]
  have h2 : ⟪A ξ ξ (T ξ), w⟫_ℂ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hA.adjoint_eq hi hδ hρ, e, inner_zero_right]
  rw [hA ξ ξ T hT ξ, inner_self_eq_norm_sq_to_K, h1] at h2
  have h3 : ⟪ξ, z⟫_ℂ = 0 := by
    rw [hz, ContinuousLinearMap.adjoint_inner_right]
    simpa using h2
  rw [hξ, inner_smul_left, inner_self_eq_norm_sq_to_K] at h3
  simp [hz0] at h3

theorem exists_fixed_ne_zero [CompleteSpace H] (hi : IsIsotypic δ ρ) (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ)
    (K : Subgroup G) {h : H} (h0 : h ≠ 0) (hK : ∀ k ∈ K, ρ k h = h) : ∃ x : X, x ≠ 0 ∧ ∀ k ∈ K, δ k x = x := by
  have := hδ.complete
  obtain ⟨T, hT, x, hx⟩ : ∃ T ∈ homIn δ ρ ⊤, ∃ x, ⟪T x, h⟫_ℂ ≠ 0 := by
    by_contra hn
    push Not at hn
    exact h0 (eq_zero_of_hom hi hn)
  refine ⟨ContinuousLinearMap.adjoint T h, fun e => hx ?_, fun k hk => ?_⟩
  · rw [← ContinuousLinearMap.adjoint_inner_right, e, inner_zero_right]
  · rw [← adjoint_intertwine hδ hρ hT k h, hK k hk]

theorem IsOpFam.apply_fixed [CompleteSpace H] (hA : IsOpFam δ ρ A) (hi : IsIsotypic δ ρ) (hδ : IsIrrUnitary δ)
    (hρ : IsUnitaryRep ρ) (K : Subgroup G) {ξ : X} (hξ : ‖ξ‖ = 1)
    (hl : ∀ x : X, (∀ k ∈ K, δ k x = x) → ∃ c : ℂ, x = c • ξ) {h : H} (hK : ∀ k ∈ K, ρ k h = h) : A ξ ξ h = h := by
  have := hδ.complete
  refine sub_eq_zero.1 (eq_zero_of_hom hi fun T hT x => ?_)
  obtain ⟨c, hc⟩ := hl (ContinuousLinearMap.adjoint T h) fun k hk => by
    rw [← adjoint_intertwine hδ hρ hT k h, hK k hk]
  have h1 : ∀ u, ⟪T u, h⟫_ℂ = c * ⟪u, ξ⟫_ℂ := fun u => by
    rw [← ContinuousLinearMap.adjoint_inner_right, hc, inner_smul_right]
  rw [inner_sub_right, ← ContinuousLinearMap.adjoint_inner_left (A ξ ξ), hA.adjoint_eq hi hδ hρ, hA ξ ξ T hT x,
    inner_smul_left, h1, h1, inner_conj_symm, inner_self_eq_norm_sq_to_K, hξ]
  simp
  ring

end Local

section Tensor

variable {ι G H : Type} {Γ Hs : ι → Type} [Group G] [∀ i, Group (Γ i)] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)]
  {a : ∀ i, Hs i → (H →L[ℂ] H)} {ξ : ∀ i, Hs i} {w : H}

def pr (hc : ∀ i j, i ≠ j → ∀ y y', Commute (a i y) (a j y')) (s : Finset ι) (y : ∀ i, Hs i) : H →L[ℂ] H :=
  s.noncommProd (fun i => a i (y i)) fun i _ j _ h => hc i j h _ _

variable (hc : ∀ i j, i ≠ j → ∀ y y', Commute (a i y) (a j y'))

@[simp] theorem pr_empty (y : ∀ i, Hs i) : pr hc ∅ y = 1 := Finset.noncommProd_empty _ _

theorem pr_insert [DecidableEq ι] {s : Finset ι} {i : ι} (hi : i ∉ s) (y : ∀ i, Hs i) :
    pr hc (insert i s) y = a i (y i) * pr hc s y :=
  Finset.noncommProd_insert_of_notMem _ _ _ _ hi

theorem commute_pr {C : H →L[ℂ] H} {s : Finset ι} {y : ∀ i, Hs i} (h : ∀ i ∈ s, Commute C (a i (y i))) :
    Commute C (pr hc s y) :=
  Finset.noncommProd_commute _ _ _ _ h

theorem pr_congr {s : Finset ι} {y y' : ∀ i, Hs i} (h : ∀ i ∈ s, y i = y' i) : pr hc s y = pr hc s y' :=
  Finset.noncommProd_congr rfl (fun i hi => by rw [h i hi]) _

theorem pr_insert_apply [DecidableEq ι] {s : Finset ι} {i : ι} (hi : i ∉ s) {y : ∀ i, Hs i} (hy : y i = ξ i)
    (hw : a i (ξ i) w = w) : pr hc (insert i s) y w = pr hc s y w := by
  have h := commute_pr hc (C := a i (y i)) (s := s) (y := y) fun j hj =>
    hc i j (fun e => hi (e ▸ hj)) _ _
  rw [pr_insert hc hi, h.eq, ContinuousLinearMap.mul_apply, hy, hw]

theorem pr_union_apply [DecidableEq ι] (hw : ∀ i, a i (ξ i) w = w) (t u : Finset ι) {y : ∀ i, Hs i}
    (hy : ∀ i ∈ u, i ∉ t → y i = ξ i) : pr hc (t ∪ u) y w = pr hc t y w := by
  induction u using Finset.induction_on with
  | empty => simp
  | insert j u hj ih =>
    have ih' := ih fun i hi => hy i (Finset.mem_insert_of_mem hi)
    rw [Finset.union_insert]
    by_cases h : j ∈ t ∪ u
    · rwa [Finset.insert_eq_of_mem h]
    · rw [pr_insert_apply hc h (hy j (Finset.mem_insert_self _ _) fun e => h (Finset.mem_union_left _ e)) (hw j), ih']

theorem inner_pr [CompleteSpace H] [DecidableEq ι] (hw : ∀ i, a i (ξ i) w = w)
    (hadj : ∀ i y y', ContinuousLinearMap.adjoint (a i y') * a i y = ⟪y', y⟫_ℂ • a i (ξ i))
    (s : Finset ι) (y y' : ∀ i, Hs i) :
    ⟪pr hc s y' w, pr hc s y w⟫_ℂ = (∏ i ∈ s, ⟪y' i, y i⟫_ℂ) * ⟪w, w⟫_ℂ := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have h := commute_pr hc (C := a j (ξ j)) (s := s) (y := y) fun i hi =>
      hc j i (fun e => hj (e ▸ hi)) _ _
    have h2 : a j (ξ j) (pr hc s y w) = pr hc s y w := by
      have := DFunLike.congr_fun h.eq w
      simp only [ContinuousLinearMap.mul_apply, hw j] at this
      exact this
    rw [pr_insert hc hj, pr_insert hc hj, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.mul_apply (ContinuousLinearMap.adjoint _), hadj,
      ContinuousLinearMap.smul_apply, h2, inner_smul_right, ih, Finset.prod_insert hj, mul_assoc]


open Classical in
def pureVec (ξ : ∀ i, Hs i) (w : H) (y : ∀ i, Hs i) : H :=
  if h : {i | y i ≠ ξ i}.Finite then pr hc h.toFinset y w else 0

theorem pureVec_eq [DecidableEq ι] (hw : ∀ i, a i (ξ i) w = w) {y : ∀ i, Hs i} (hy : Formalism.MainNotions.KudlaSiegelWeil.Restr ξ y) {s : Finset ι}
    (hs : ∀ i ∉ s, y i = ξ i) : pureVec hc ξ w y = pr hc s y w := by
  have hy' : {i | y i ≠ ξ i}.Finite := hy
  rw [pureVec, dite_eq_left hy']
  have hsub : hy'.toFinset ⊆ s := fun i hi => by
    by_contra hn
    exact (hy'.mem_toFinset.1 hi) (hs i hn)
  rw [← Finset.union_eq_right.2 hsub]
  convert (pr_union_apply hc hw hy'.toFinset s (y := y) fun i _ hi => ?_).symm using 3
  by_contra hn
  exact hi (hy'.mem_toFinset.2 hn)

variable {p : ∀ i, G →* Γ i} {e : ∀ i, Γ i →* G} {δ : ∀ i, Γ i →* (Hs i →L[ℂ] Hs i)} {π : G →* (H →L[ℂ] H)}

theorem exists_off [DecidableEq ι] (hpe : ∀ i x, p i (e i x) = x) (hpe' : ∀ i j, i ≠ j → ∀ x, p j (e i x) = 1)
    (hcomm : ∀ v g, p v g = 1 → ∀ y, Commute (π g) (a v y))
    (hrep : ∀ i x y, π (e i x) * a i y = a i (δ i x y)) (s : Finset ι) (g : G) :
    ∃ k, (∀ i ∈ s, p i k = 1) ∧ (∀ i ∉ s, p i k = p i g) ∧
      ∀ y, π g * pr hc s y = pr hc s (fun i => δ i (p i g) (y i)) * π k := by
  induction s using Finset.induction_on generalizing g with
  | empty => exact ⟨g, by simp, by simp, by simp⟩
  | insert v s hv ih =>
    set g' := (e v (p v g))⁻¹ * g with hg'
    have h1 : p v g' = 1 := by simp [hg', hpe]
    have h2 : ∀ u, u ≠ v → p u g' = p u g := fun u hu => by simp [hg', hpe' v u hu.symm]
    obtain ⟨k, hk1, hk2, hk3⟩ := ih g'
    refine ⟨k, fun i hi => ?_, fun i hi => ?_, fun y => ?_⟩
    · rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [hk2 i hv, h1]
      · exact hk1 i hi
    · rw [hk2 i fun h => hi (Finset.mem_insert_of_mem h), h2 i fun h => hi (h ▸ Finset.mem_insert_self _ _)]
    · have e1 : π g = π (e v (p v g)) * π g' := by rw [← map_mul, hg', mul_inv_cancel_left]
      have e2 : pr hc s (fun i => δ i (p i g') (y i)) = pr hc s (fun i => δ i (p i g) (y i)) :=
        pr_congr hc fun i hi => by rw [h2 i fun h => hv (h ▸ hi)]
      rw [pr_insert hc hv, pr_insert hc hv, e1, mul_assoc, ← mul_assoc (π g'), (hcomm v g' h1 (y v)).eq, mul_assoc,
        hk3 y, e2, ← mul_assoc, hrep, mul_assoc]


include hc in
theorem exists_isRestrTensor [CompleteSpace H] (hπ : IsTopIrreducible π) (hξ : ∀ i, ‖ξ i‖ = 1) (hw1 : ‖w‖ = 1)
    (hw : ∀ i, a i (ξ i) w = w)
    (hadj : ∀ i y y', ContinuousLinearMap.adjoint (a i y') * a i y = ⟪y', y⟫_ℂ • a i (ξ i))
    (hpe : ∀ i x, p i (e i x) = x) (hpe' : ∀ i j, i ≠ j → ∀ x, p j (e i x) = 1)
    (hcomm : ∀ v g, p v g = 1 → ∀ y, Commute (π g) (a v y))
    (hrep : ∀ i x y, π (e i x) * a i y = a i (δ i x y))
    (hk : ∀ g, ∃ s₀ : Finset ι, (∀ i ∉ s₀, δ i (p i g) (ξ i) = ξ i) ∧ ∀ s, s₀ ⊆ s → ∀ k, (∀ i ∈ s, p i k = 1) →
      (∀ i ∉ s, p i k = p i g) → π k w = w) :
    ∃ B, IsRestrTensor p δ ξ π B := by
  classical
  have hfix : ∀ g, ∀ᶠ i in Filter.cofinite, δ i (p i g) (ξ i) = ξ i := fun g => by
    obtain ⟨s₀, h, -⟩ := hk g
    exact Filter.eventually_cofinite.2 (s₀.finite_toSet.subset fun i hi => by
      by_contra hn
      exact hi (h i hn))
  have happly : ∀ g y, Formalism.MainNotions.KudlaSiegelWeil.Restr ξ y →
      π g (pureVec hc ξ w y) = pureVec hc ξ w fun i => δ i (p i g) (y i) := fun g y hy => by
    obtain ⟨s₀, h0, h1⟩ := hk g
    have hy' : {i | y i ≠ ξ i}.Finite := hy
    set s := s₀ ∪ hy'.toFinset with hs
    have hoff : ∀ i ∉ s, y i = ξ i := fun i hi => by
      by_contra hn
      exact hi (Finset.mem_union_right _ (hy'.mem_toFinset.2 hn))
    obtain ⟨k, hk1, hk2, hk3⟩ := exists_off hc hpe hpe' hcomm hrep s g
    have hr := restr_map (f := fun i => δ i (p i g)) (hfix g) hy
    rw [pureVec_eq hc hw hy hoff, pureVec_eq hc hw hr (s := s) fun i hi => by
      rw [hoff i hi]; exact h0 i fun h => hi (Finset.mem_union_left _ h)]
    have := DFunLike.congr_fun (hk3 y) w
    simp only [ContinuousLinearMap.mul_apply] at this
    rw [this, h1 s Finset.subset_union_left k hk1 hk2]
  have hself : pureVec hc ξ w ξ = w := by
    rw [pureVec_eq hc hw (restr_self ξ) (s := ∅) fun _ _ => rfl]
    simp
  refine ⟨pureVec hc ξ w, .of_forall hξ, hfix, fun y y' hy hy' => ?_, ?_, happly⟩
  · have hy1 : {i | y i ≠ ξ i}.Finite := hy
    have hy2 : {i | y' i ≠ ξ i}.Finite := hy'
    set s := hy1.toFinset ∪ hy2.toFinset with hs
    have h1 : ∀ i ∉ s, y i = ξ i := fun i hi => by
      by_contra hn
      exact hi (Finset.mem_union_left _ (hy1.mem_toFinset.2 hn))
    have h2 : ∀ i ∉ s, y' i = ξ i := fun i hi => by
      by_contra hn
      exact hi (Finset.mem_union_right _ (hy2.mem_toFinset.2 hn))
    rw [pureVec_eq hc hw hy h1, pureVec_eq hc hw hy' h2, inner_pr hc hw hadj,
      inner_self_eq_norm_sq_to_K, hw1, finprod_eq_prod_of_mulSupport_subset (s := s)]
    · simp
    · intro i hi
      by_contra hn
      apply hi
      have hn' : i ∉ s := hn
      simp only [h1 i hn', h2 i hn', inner_self_eq_norm_sq_to_K, hξ i]
      simp
  · set D := Submodule.span ℂ {v | ∃ y, Formalism.MainNotions.KudlaSiegelWeil.Restr ξ y ∧ v = pureVec hc ξ w y} with hD
    have hinv : ∀ g, ∀ v ∈ D, π g v ∈ D := fun g v hv => by
      have hle : D ≤ D.comap (π g : H →ₗ[ℂ] H) := Submodule.span_le.2 (by
        rintro _ ⟨y, hy, rfl⟩
        exact Submodule.subset_span ⟨_, restr_map (f := fun i => δ i (p i g)) (hfix g) hy, happly g y hy⟩)
      exact hle hv
    rcases hπ.2 _ (isSubrep_topologicalClosure hinv) with h | h
    · exfalso
      have hm : w ∈ D.topologicalClosure :=
        Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨ξ, restr_self ξ, hself.symm⟩)
      rw [h, Submodule.mem_bot] at hm
      simp [hm] at hw1
    · exact h

end Tensor

section Select

variable {ι H : Type} {X : ι → Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [∀ i, NormedAddCommGroup (X i)] [∀ i, InnerProductSpace ℂ (X i)]

theorem exists_fixed_of_finset [DecidableEq ι] {A : ∀ i, X i → X i → (H →L[ℂ] H)}
    (hc : ∀ i j, i ≠ j → ∀ y ξ y' ξ', Commute (A i y ξ) (A j y' ξ'))
    (hsel : ∀ i (w : H), w ≠ 0 → ∃ ξ, ‖ξ‖ = 1 ∧ A i ξ ξ w ≠ 0)
    (hproj : ∀ i ξ, ‖ξ‖ = 1 → A i ξ ξ * A i ξ ξ = A i ξ ξ)
    (Inv : H → Prop) (s : Finset ι) (hstep : ∀ i ∈ s, ∀ ξ w, Inv w → Inv (A i ξ ξ w)) {w₀ : H} (h₀ : Inv w₀)
    (hw₀ : w₀ ≠ 0) :
    ∃ (ξ : ∀ i, X i) (w : H), w ≠ 0 ∧ Inv w ∧ ∀ i ∈ s, ‖ξ i‖ = 1 ∧ A i (ξ i) (ξ i) w = w := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, w₀, hw₀, h₀, by simp⟩
  | insert j s hj ih =>
    obtain ⟨ξ, w, hw, hI, hξ⟩ := ih fun i hi => hstep i (Finset.mem_insert_of_mem hi)
    obtain ⟨x, hx1, hx⟩ := hsel j w hw
    refine ⟨Function.update ξ j x, A j x x w, hx, hstep j (Finset.mem_insert_self _ _) x w hI, fun i hi => ?_⟩
    by_cases e : i = j
    · subst e
      refine ⟨by simpa using hx1, ?_⟩
      simp only [Function.update_self]
      rw [← ContinuousLinearMap.mul_apply, hproj i x hx1]
    · have hi' : i ∈ s := (Finset.mem_insert.1 hi).resolve_left e
      simp only [Function.update_of_ne e]
      refine ⟨(hξ i hi').1, ?_⟩
      have := DFunLike.congr_fun (hc i j e (ξ i) (ξ i) x x).eq w
      simp only [ContinuousLinearMap.mul_apply, (hξ i hi').2] at this
      exact this

end Select

end GlobalTheory.CompanionTheory.RestT

end
end

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult CompanionTheory.Rg.Fl
open GlobalTheory.PRep (IsAdmissible fixed)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RestT

theorem exists_good {G X H : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {δ : G →* (X →L[ℂ] X)} {ρ : G →* (H →L[ℂ] H)}
    {A : X → X → (H →L[ℂ] H)} (hA : IsOpFam δ ρ A) (hi : IsIsotypic δ ρ) (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ)
    (K : Subgroup G) (hl : ∀ x : X, x ≠ 0 → (∀ k ∈ K, δ k x = x) → ∀ y, (∀ k ∈ K, δ k y = y) → ∃ c : ℂ, y = c • x)
    {w : H} (hw : w ≠ 0) (hK : ∀ k ∈ K, ρ k w = w) :
    ∃ ξ : X, ‖ξ‖ = 1 ∧ (∀ k ∈ K, δ k ξ = ξ) ∧ ∀ h : H, (∀ k ∈ K, ρ k h = h) → A ξ ξ h = h := by
  obtain ⟨x, hx, hxK⟩ := exists_fixed_ne_zero hi hδ hρ K hw hK
  have hn : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hx
  have h1 : ‖(‖x‖ : ℂ)⁻¹ • x‖ = 1 := by simp [norm_smul, hx]
  have h2 : ∀ k ∈ K, δ k ((‖x‖ : ℂ)⁻¹ • x) = (‖x‖ : ℂ)⁻¹ • x := fun k hk => by rw [map_smul, hxK k hk]
  refine ⟨_, h1, h2, fun h hh => hA.apply_fixed hi hδ hρ K h1 (fun y hy => ?_) hh⟩
  have h3 : (‖x‖ : ℂ)⁻¹ • x ≠ 0 := fun e => by simp [e] at h1
  exact hl _ h3 h2 y hy

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem ext_projPl {a b : GAd σ J} (h : ∀ u, projPl σ J u a = projPl σ J u b) : a = b :=
  GAd_ext σ J (fun w => h (.inl w)) fun v => h (.inr v)

theorem commute_embPl {v : Formalism.MainNotions.SchurIrreducible.Pl F} {g : GAd σ J} (h : projPl σ J v g = 1) (x : GPl σ J v) :
    Commute g (embPl σ J v x) := by
  refine ext_projPl fun u => ?_
  by_cases e : u = v
  · subst e
    simp [h]
  · simp [projPl_embPl_ne σ J e]

theorem exists_levelOff_fixed (hFix : StFixVec) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : GAd σ J →* (H →L[ℂ] H)} (hπ : IsIrrUnitary π) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (w : H), w ≠ 0 ∧ ∀ k ∈ levelOff σ J L S, π k w = w := by
  haveI := hπ.complete
  haveI := hπ.irred.1
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GFin σ J
  obtain ⟨U, w, hU, hw, hfix⟩ := hFix (GFin σ J) H (π.comp (ofFin σ J)) (fun g v => hπ.unitary.norm_apply _ _)
    (fun v => (hπ.unitary.continuous_apply v).comp (continuous_ofFin σ J))
  obtain ⟨S, hS⟩ := GlobalTheory.PlaceGen.exists_levelOff_le σ J L (U.comap (projFin σ J)) (hU.preimage (continuous_projFin σ J))
  refine ⟨S, w, hw, fun k hk => ?_⟩
  have hr : k ∈ (ofFin σ J).range := by
    rw [range_ofFin]
    exact (mem_levelOff.1 hk).1
  obtain ⟨g, rfl⟩ := hr
  have := hS hk
  simp only [Subgroup.mem_comap, projFin_ofFin] at this
  exact hfix g this

theorem eventually_line (hAdm : GlobalTheory.Published.UnitaryIrreducibleAdmissible) (hc : IsCMExt F E σ) (hJ : IsHermND σ J)
    (L : Submodule (𝓞 E) (Fin n → E)) [hL : Submodule.IsFullLattice E L] :
    ∀ᶠ v in cofinite, ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
      (δ : GLoc σ J v →* (X →L[ℂ] X)), IsIrrUnitary δ → ∀ x : X, x ≠ 0 → (∀ k ∈ stabLoc σ J L v, δ k x = x) →
        ∀ y, (∀ k ∈ stabLoc σ J L v, δ k y = y) → ∃ c : ℂ, y = c • x := by
  filter_upwards [GlobalTheory.T.eventually_exists_doubleCoset_antiInvolution_unitary F E σ hc n J hJ L hL] with v hθ X _ _ δ hδ x hx0 hx y hy
  obtain ⟨θ, hθ1, hθ2, hθ3⟩ := hθ
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GLoc σ J v
  have hKo : IsOpen (stabLoc σ J L v : Set (GLoc σ J v)) := isOpen_stabLoc σ J L v
  have hKc : IsCompact (stabLoc σ J L v : Set (GLoc σ J v)) := isCompact_stabLoc σ J L v
  have hirr := GlobalTheory.T.unitary_irreducible_smooth_admissible (GLoc σ J v) X δ hδ
    (fun K hK hK' => hAdm F E σ hc n J hJ v X δ hδ K hK hK')
  have sm : ∀ z, (∀ k ∈ stabLoc σ J L v, δ k z = z) → z ∈ GlobalTheory.PRep.smoothPart (toRep δ) := by
    intro z hz
    let S : Subgroup (GLoc σ J v) :=
      { carrier := {g | toRep δ g z = z}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    have hle : stabLoc σ J L v ≤ S := fun k hk => hz k hk
    exact Subgroup.isOpen_mono hle hKo
  let x' : GlobalTheory.PRep.smoothPart (toRep δ) := ⟨x, sm x hx⟩
  have hx' : x' ∈ fixed (smRep δ) (stabLoc σ J L v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (hx k hk)
  have hx0' : x' ≠ 0 := fun e => hx0 (congrArg Subtype.val e)
  have hline := GlobalTheory.T.gelfand_pair_spherical_vector_unique (GLoc σ J v) (stabLoc σ J L v) hKo hKc θ hθ1 hθ2 hθ3 _
    (smRep δ) hirr.1 hirr.2 x' hx' hx0'
  have hy' : (⟨y, sm y hy⟩ : GlobalTheory.PRep.smoothPart (toRep δ)) ∈ fixed (smRep δ) (stabLoc σ J L v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (hy k hk)
  rw [hline] at hy'
  obtain ⟨c, hc'⟩ := Submodule.mem_span_singleton.1 hy'
  exact ⟨c, (congrArg Subtype.val hc').symm⟩

def plK (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) :
    ∀ u : Formalism.MainNotions.SchurIrreducible.Pl F, Subgroup (GPl σ J u)
  | .inl _ => ⊥
  | .inr v => stabLoc σ J L v

theorem exists_finset_projPl_mem (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (g : GAd σ J) :
    ∃ t : Finset (Formalism.MainNotions.SchurIrreducible.Pl F), ∀ u ∉ t, projPl σ J u g ∈ plK σ J L u := by
  classical
  have hf := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc σ J L g)
  refine ⟨Finset.univ.image Sum.inl ∪ hf.toFinset.image Sum.inr, fun u hu => ?_⟩
  rcases u with w | v
  · exact absurd (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ w))) hu
  · by_contra hn
    exact hu (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hf.mem_toFinset.2 hn)))

theorem projPl_eq_one_of_mem_levelOff {L : Submodule (𝓞 E) (Fin n → E)} {S : Finset (HeightOneSpectrum (𝓞 F))}
    {k : GAd σ J} (hk : k ∈ levelOff σ J L S) {u : Formalism.MainNotions.SchurIrreducible.Pl F}
    (hu : ∀ v, u = .inr v → v ∈ S) : projPl σ J u k = 1 := by
  rcases u with w | v
  · exact mem_finPts_iff_forall.1 (mem_levelOff.1 hk).1 w
  · exact (mem_levelOff.1 hk).2.1 v (hu v rfl)

theorem embPl_mem_levelOff {L : Submodule (𝓞 E) (Fin n → E)} {S : Finset (HeightOneSpectrum (𝓞 F))}
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {k : GLoc σ J v} (hk : k ∈ stabLoc σ J L v) :
    emb σ J v k ∈ levelOff σ J L S := by
  refine mem_levelOff.2 ⟨mem_finPts_iff_forall.2 fun w => projArch_emb σ J w v k, fun u hu => ?_, fun u _ => ?_⟩
  · exact proj_emb_ne σ J (by rintro rfl; exact hv hu) k
  · by_cases e : u = v
    · subst e
      simpa using hk
    · rw [proj_emb_ne σ J e]
      exact one_mem _

end Adelic

theorem stTensor : StTensor := by
  intro hOp hFix hAdm F E _ _ _ _ _ σ hc n J hJ H _ _ π hπ R hR
  classical
  haveI := hπ.complete
  haveI hL : Submodule.IsFullLattice E (stdLattice E n) := isLattice_stdLattice
  set L := stdLattice E n with hLdef
  let ρ : ∀ v, GPl σ J v →* (H →L[ℂ] H) := fun v => π.comp (embPl σ J v)
  have hρ : ∀ v, IsUnitaryRep (ρ v) := fun v => isUnitaryRep_comp hπ.unitary (continuous_embPl σ J v)
  have hA' := fun v => hOp (GPl σ J v) (R v).H H (R v).π (ρ v) (R v).isIrr (hρ v) (hR v)
  choose A hA0 using hA'
  have hA : ∀ v, IsOpFam (R v).π (ρ v) (A v) := hA0
  have hi : ∀ v, IsIsotypic (R v).π (ρ v) := hR
  have hcommπ : ∀ v g, projPl σ J v g = 1 → ∀ y ξ, Commute (π g) (A v y ξ) := fun v g h y ξ =>
    ((hA v).commute (hi v) (C := π g) (fun x => (commute_embPl h x).map π) y ξ).symm
  have hAA : ∀ u v, u ≠ v → ∀ y ξ y' ξ', Commute (A u y ξ) (A v y' ξ') := fun u v huv y ξ y' ξ' =>
    (hA u).commute (hi u) (C := A v y' ξ')
      (fun x => (hcommπ v (embPl σ J u x) (projPl_embPl_ne σ J huv.symm x) y' ξ').symm) y ξ
  obtain ⟨S, w₀, hw₀, hfix₀⟩ := exists_levelOff_fixed (σ := σ) (J := J) hFix L hπ
  have hbad := Filter.eventually_cofinite.1 (eventually_line hAdm hc hJ L)
  set S₁ := S ∪ hbad.toFinset with hS₁
  set s : Finset (Formalism.MainNotions.SchurIrreducible.Pl F) := Finset.univ.image Sum.inl ∪ S₁.image Sum.inr with hs
  have hinl : ∀ w, (Sum.inl w : Formalism.MainNotions.SchurIrreducible.Pl F) ∈ s := fun w =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ w))
  have hinr : ∀ v, v ∈ S₁ → (Sum.inr v : Formalism.MainNotions.SchurIrreducible.Pl F) ∈ s := fun v hv =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hv)
  have hmems : ∀ u ∈ s, ∀ v, u = .inr v → v ∈ S₁ := fun u hu v e => by
    subst e
    rcases Finset.mem_union.1 hu with h | h
    · obtain ⟨w, -, hw⟩ := Finset.mem_image.1 h
      exact absurd hw (by simp)
    · obtain ⟨v', hv', e⟩ := Finset.mem_image.1 h
      exact Sum.inr_injective e ▸ hv'
  have hoff : levelOff σ J L S₁ ≤ levelOff σ J L S := GlobalTheory.PlaceGen.levelOff_anti σ J L Finset.subset_union_left
  have hKlev : ∀ u, u ∉ s → ∀ k ∈ plK σ J L u, embPl σ J u k ∈ levelOff σ J L S₁ := fun u hu k hk => by
    rcases u with w | v
    · exact absurd (hinl w) hu
    · exact embPl_mem_levelOff (fun h => hu (hinr v h)) hk
  have hgood : ∀ u, ∃ ξ : (R u).H, u ∉ s → ‖ξ‖ = 1 ∧ (∀ k ∈ plK σ J L u, (R u).π k ξ = ξ) ∧
      ∀ h : H, (∀ k ∈ plK σ J L u, ρ u k h = h) → A u ξ ξ h = h := fun u => by
    by_cases hu : u ∈ s
    · exact ⟨0, fun h => absurd hu h⟩
    · rcases u with w | v
      · exact absurd (hinl w) hu
      · have hv : v ∉ hbad.toFinset := fun h => hu (hinr v (Finset.mem_union_right _ h))
        have hl : ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
            (δ : GLoc σ J v →* (X →L[ℂ] X)), IsIrrUnitary δ → ∀ x : X, x ≠ 0 → (∀ k ∈ stabLoc σ J L v, δ k x = x) →
              ∀ y, (∀ k ∈ stabLoc σ J L v, δ k y = y) → ∃ c : ℂ, y = c • x := by
          by_contra hn
          exact hv (hbad.mem_toFinset.2 hn)
        obtain ⟨ξ, h1, h2, h3⟩ := exists_good (hA (.inr v)) (hi (.inr v)) (R (.inr v)).isIrr (hρ (.inr v))
          (plK σ J L (.inr v)) (hl _ _ (R (.inr v)).isIrr) hw₀
          (fun k hk => hfix₀ _ (hoff (hKlev _ hu k hk)))
        exact ⟨ξ, fun _ => ⟨h1, h2, h3⟩⟩
  choose ξg hξg using hgood
  let Inv : H → Prop := fun w => (∀ k ∈ levelOff σ J L S₁, π k w = w) ∧ ∀ u, u ∉ s → A u (ξg u) (ξg u) w = w
  have hproj : ∀ i (ξ : (R i).H), ‖ξ‖ = 1 → A i ξ ξ * A i ξ ξ = A i ξ ξ := fun i ξ h => by
    rw [(hA i).mul (hi i), inner_self_eq_norm_sq_to_K, h]
    simp
  obtain ⟨ξs, w₁, hw₁, hI, hξs⟩ := exists_fixed_of_finset (A := A) hAA
    (fun i w hw => (hA i).exists_ne_zero (hi i) (R i).isIrr (hρ i) hw) hproj Inv s
    (fun i his ξ w hw => ⟨fun k hk => by
        have hc1 := (hcommπ i k (projPl_eq_one_of_mem_levelOff hk (hmems i his)) ξ ξ).eq
        have := DFunLike.congr_fun hc1 w
        simp only [ContinuousLinearMap.mul_apply] at this
        rw [this, hw.1 k hk],
      fun u hu => by
        have hne : u ≠ i := fun e => hu (e ▸ his)
        have := DFunLike.congr_fun (hAA u i hne (ξg u) (ξg u) ξ ξ).eq w
        simp only [ContinuousLinearMap.mul_apply] at this
        rw [this, hw.2 u hu]⟩)
    (w₀ := w₀) ⟨fun k hk => hfix₀ k (hoff hk), fun u hu =>
      (hξg u hu).2.2 w₀ fun k hk => hfix₀ _ (hoff (hKlev u hu k hk))⟩ hw₀
  let ξ : ∀ u, (R u).H := fun u => if u ∈ s then ξs u else ξg u
  have hξ : ∀ u, ‖ξ u‖ = 1 := fun u => by
    by_cases hu : u ∈ s
    · simp only [ξ, if_pos hu]
      exact (hξs u hu).1
    · simp only [ξ, if_neg hu]
      exact (hξg u hu).1
  have hfixall : ∀ u, A u (ξ u) (ξ u) w₁ = w₁ := fun u => by
    by_cases hu : u ∈ s
    · simp only [ξ, if_pos hu]
      exact (hξs u hu).2
    · simp only [ξ, if_neg hu]
      exact hI.2 u hu
  have hn : (‖w₁‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hw₁
  set w := (‖w₁‖ : ℂ)⁻¹ • w₁ with hwdef
  have hw1 : ‖w‖ = 1 := by simp [hwdef, norm_smul, hw₁]
  have hlev : ∀ k ∈ levelOff σ J L S₁, π k w = w := fun k hk => by
    rw [hwdef, map_smul, hI.1 k hk]
  let a : ∀ u, (R u).H → (H →L[ℂ] H) := fun u y => A u y (ξ u)
  have hac : ∀ i j, i ≠ j → ∀ y y', Commute (a i y) (a j y') := fun i j h y y' => hAA i j h _ _ _ _
  obtain ⟨B, hB⟩ := exists_isRestrTensor (a := a) (ξ := ξ) (w := w) (p := projPl σ J) (e := embPl σ J)
    (δ := fun v => (R v).π) (π := π) hac hπ.irred hξ hw1
    (fun i => by simp only [a, hwdef, map_smul, hfixall i])
    (fun i y y' => by
      simp only [a]
      rw [(hA i).adjoint_eq (hi i) (R i).isIrr (hρ i), (hA i).mul (hi i)])
    (fun i x => projPl_embPl_self σ J i x) (fun i j h x => projPl_embPl_ne σ J h.symm x)
    (fun v g h y => hcommπ v g h y _)
    (fun i x y => (hA i).rep_mul (hi i) x y (ξ i))
    (fun g => by
      obtain ⟨t, ht⟩ := exists_finset_projPl_mem (σ := σ) (J := J) L g
      refine ⟨s ∪ t, fun i hi' => ?_, fun s' hs' k hk1 hk2 => hlev k ?_⟩
      · have h1 : i ∉ s := fun h => hi' (Finset.mem_union_left _ h)
        have h2 : i ∉ t := fun h => hi' (Finset.mem_union_right _ h)
        simp only [ξ, if_neg h1]
        exact (hξg i h1).2.1 _ (ht i h2)
      · refine mem_levelOff.2 ⟨mem_finPts_iff_forall.2 fun w => hk1 _ (hs' (Finset.mem_union_left _ (hinl w))),
          fun v hv => hk1 _ (hs' (Finset.mem_union_left _ (hinr v hv))), fun v hv => ?_⟩
        by_cases h : (Sum.inr v : Formalism.MainNotions.SchurIrreducible.Pl F) ∈ s'
        · have : projPl σ J (.inr v) k = 1 := hk1 _ h
          change projPl σ J (.inr v) k ∈ stabLoc σ J L v
          rw [this]
          exact one_mem _
        · have h3 : (Sum.inr v : Formalism.MainNotions.SchurIrreducible.Pl F) ∉ t := fun h' => h (hs' (Finset.mem_union_right _ h'))
          change projPl σ J (.inr v) k ∈ stabLoc σ J L v
          rw [hk2 _ h]
          exact ht _ h3)
  exact ⟨ξ, B, hB⟩

end GlobalTheory.CompanionTheory.RestT

end

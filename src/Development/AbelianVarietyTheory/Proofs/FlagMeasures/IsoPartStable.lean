module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Formalism.HarderNarasimhan.ShiftInvariance

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsoPartStable
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.VminusComp

def ht {n : ℕ} (μ : Fin n → ℝ) : ℝ := ∑ i : Fin n, ((i : ℕ) : ℝ) * μ i

theorem ht_add {n : ℕ} (μ ν : Fin n → ℝ) : ht (μ + ν) = ht μ + ht ν := by
  simp [ht, mul_add, Finset.sum_add_distrib]

theorem ht_sub {n : ℕ} (μ ν : Fin n → ℝ) : ht (μ - ν) = ht μ - ht ν := by
  simp [ht, mul_sub, Finset.sum_sub_distrib]

theorem ht_root {n : ℕ} (a b : Fin n) : ht (Formalism.REAL.root a b) = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [ht, Formalism.REAL.root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem weight_shift {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} (hF : Formalism.REAL.KRel ε F) {ν : Fin n → ℝ} {x : W}
    (hx : Formalism.REAL.IsWeight F ν x) {a b : Fin n} (hab : ε a = ε b) :
    Formalism.REAL.IsWeight F (ν + Formalism.REAL.root a b) (F a b x) := by
  intro c
  have h := congrArg (fun T : Module.End ℂ W => T x) (hF c c a b rfl hab)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hx c, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases h1 : c = a <;> by_cases h2 : b = c
  · subst h1; subst h2; simp [Formalism.REAL.root]
  · subst h1
    simp [Formalism.REAL.root, h2, Pi.single_apply, Ne.symm h2, add_smul, add_comm]
  · subst h2
    simp [Formalism.REAL.root, h1, Pi.single_apply, add_smul, sub_smul, add_comm]
  · simp [Formalism.REAL.root, h1, h2, Pi.single_apply, Ne.symm h2]

theorem word_weight {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} (hF : Formalism.REAL.KRel ε F) {μ : Fin n → ℝ} {x : W}
    (hx : Formalism.REAL.IsWeight F μ x) (w : List (Fin n × Fin n))
    (hw : ∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) :
    ∃ ν, ht μ ≤ ht ν ∧ Formalism.REAL.IsWeight F ν (ew F w x) := by
  induction w with
  | nil => exact ⟨μ, le_rfl, by simpa [ew] using hx⟩
  | cons p w ih =>
    obtain ⟨ν, h1, h2⟩ := ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))
    have hp := hw p (List.mem_cons_self ..)
    refine ⟨ν + Formalism.REAL.root p.1 p.2, ?_, ?_⟩
    · rw [ht_add, ht_root]
      have : ((p.2 : ℕ) : ℝ) < ((p.1 : ℕ) : ℝ) := by exact_mod_cast hp.2
      linarith
    · simpa only [ew, Module.End.mul_apply] using weight_shift hF h2 hp.1

theorem comp_weight {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {E : Fin n → Fin n → Module.End ℂ V} {ν : Fin n → ℝ} {G : Arr V n 1}
    (hG : Formalism.REAL.IsWeight (arrE E 1) ν G) (a b : Fin n) :
    Formalism.REAL.IsWeight E (ν - Formalism.REAL.root a b) (G (fun _ => (a, b))) := by
  intro c
  have h1 := congrArg (fun G : Arr V n 1 => G (fun _ => (a, b))) (hG c)
  simp only at h1
  rw [arr_operator_one_apply, PiLp.smul_apply, add_comm, ← eq_sub_iff_add_eq] at h1
  rw [h1]
  by_cases h1 : a = c <;> by_cases h2 : b = c
  · subst h1; subst h2; simp [Formalism.REAL.root]
  · subst h1
    simp [Formalism.REAL.root, h2, Pi.single_apply, Ne.symm h2, sub_smul]
  · subst h2
    simp [Formalism.REAL.root, h1, Pi.single_apply, Ne.symm h1, add_smul, sub_smul]
  · simp [Formalism.REAL.root, h1, h2, Pi.single_apply, Ne.symm h2, Ne.symm h1]

theorem isoPart_stable {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} (T : Set (Fin n → ℝ)) (S : Submodule ℂ W) :
    Formalism.REAL.KStable ε F (isoPart ε F T S) := by
  intro a b hab x hx
  have : isoPart ε F T S ≤ (isoPart ε F T S).comap (F a b) := by
    apply isotypic_part_le_of_forall
    intro y hy μ hμ hyh z hz
    exact compact_span_le_isotypic_part hy hμ hyh (compact_span_stable_general y a b hab z hz)
  exact this hx

theorem vminus_comp : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (abelian₂ : Fin n → ℝ) (u : V), GlRel E → IsUnitary ε E → KHighest ε E abelian₂ u → FiniteDimensional ℂ (kSpan ε E u) → KStable ε (arrE E 1) (Vminus ε E abelian₂ u) ∧ Vminus ε E abelian₂ u ≤ arrV0 ε E u 1 ∧ FiniteDimensional ℂ (Vminus ε E abelian₂ u) ∧ ∀ G ∈ Vminus ε E abelian₂ u, ∀ a b, ¬ b < a → ⟪u, at1 G a b⟫_ℂ = 0 := by
  intro V _ _ n ε E abelian₂ u hg hu hΛ hfd
  have hle : Vminus ε E abelian₂ u ≤ arrV0 ε E u 1 := by
    apply isotypic_part_le_of_forall
    intro y hy μ _ _
    exact compact_span_le_of_stable noncompact_arr_one_compact_stable hy
  have hfd0 := noncompact_arr_finite_dimensional (j := 1) hfd
  refine ⟨isoPart_stable _ _, hle, Submodule.finiteDimensional_of_le hle, ?_⟩
  intro G hG a b hab
  have hKR := glRel_kRel ε _ ((arrModule V n ε E 1).1 hg).1
  let ℓ : Arr V n 1 →ₗ[ℂ] ℂ := (innerₛₗ ℂ u) ∘ₗ
    (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 → Fin n × Fin n => V) (fun _ => (a, b)) ∘ₗ arrOf V n 1)
  have hℓ : ∀ G : Arr V n 1, ℓ G = ⟪u, G (fun _ => (a, b))⟫_ℂ := fun G => rfl
  have hker : Vminus ε E abelian₂ u ≤ LinearMap.ker ℓ := by
    apply isotypic_part_le_of_forall
    rintro y - μ ⟨a', b', hba, -, rfl⟩ hyh
    rw [(kLow _ n ε _ _ y hKR hyh).1, lowSpan, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨ν, h1, h2⟩ := word_weight hKR hyh.1 w hw
    rw [SetLike.mem_coe, LinearMap.mem_ker, hℓ]
    refine kWtOrth V n ε E _ _ _ _ (isUnitary_kUnit ε E hu) hΛ.1 (comp_weight h2 a b) ?_
    intro h
    have h3 := congrArg ht h
    rw [ht_sub, ht_root] at h3
    rw [ht_add, ht_root] at h1
    have e1 : ((b' : ℕ) : ℝ) < ((a' : ℕ) : ℝ) := by exact_mod_cast hba
    have e2 : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast not_lt.mp hab
    linarith
  exact hker hG

end GlobalTheory.Jet.VminusComp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KMapLowestKTypeSubspaceEqScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KMapLowestKTypeSubspaceEqScalar
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.KMapInto

section
variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Λ : Fin n → ℝ} {S : Submodule ℂ H}

theorem comap_bot_or_top (hS : IsKTypeOf ε σ Λ S) (T : S →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' = σ k (T s))
    (W : Submodule ℂ H) (hW : IsKStableOn ε σ W) :
    (∀ s : S, T s ∈ W → s = 0) ∨ (∀ s : S, T s ∈ W) := by
  obtain ⟨_, hSst, hSirr, _, _⟩ := hS
  have hle : (W.comap T).map S.subtype ≤ S := by
    rintro _ ⟨s, _, rfl⟩
    exact s.2
  have hst : IsKStableOn ε σ ((W.comap T).map S.subtype) := by
    rintro g hg _ ⟨s, hs, rfl⟩
    refine ⟨⟨σ g s, hSst g hg s s.2⟩, ?_, rfl⟩
    show T _ ∈ W
    rw [hT g hg s _ rfl]
    exact hW g hg _ hs
  rcases hSirr _ hle hst with h | h
  · left
    intro s hs
    have hmem : (s : H) ∈ (W.comap T).map S.subtype := ⟨s, hs, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem
  · right
    intro s
    have hmem : (s : H) ∈ (W.comap T).map S.subtype := by
      rw [h]
      exact s.2
    obtain ⟨t, ht, hts⟩ := hmem
    obtain rfl : t = s := Subtype.ext hts
    exact ht

theorem inj_or_zero (hS : IsKTypeOf ε σ Λ S) (T : S →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' = σ k (T s)) :
    (∀ s : S, T s = 0 → s = 0) ∨ (∀ s : S, T s = 0) := by
  have hbot : IsKStableOn ε σ (⊥ : Submodule ℂ H) := by
    intro g _ v hv
    rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]
  simpa only [Submodule.mem_bot] using comap_bot_or_top hS T hT ⊥ hbot

theorem range_isKType (hS : IsKTypeOf ε σ Λ S) (T : S →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' = σ k (T s))
    (hinj : ∀ s : S, T s = 0 → s = 0) : IsKTypeOf ε σ Λ (LinearMap.range T) := by
  have hS' := hS
  obtain ⟨hfin, hSst, _, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := hS'
  have key : ∀ s : S, ∀ t ∈ Kset ε, ∀ c : ℂ, σ t (T s) = c • T s → σ t s = c • (s : H) := by
    intro s t ht c h
    have h2 : T (⟨σ t s, hSst t ht s s.2⟩ - c • s) = 0 := by
      rw [map_sub, map_smul, hT t ht s _ rfl, h, sub_self]
    exact congrArg Subtype.val (sub_eq_zero.mp (hinj _ h2))
  refine ⟨inferInstance, ?_, ?_, ⟨T ⟨v, hvS⟩, ⟨⟨v, hvS⟩, rfl⟩, ?_, ?_⟩, ?_⟩
  · rintro g hg _ ⟨s, rfl⟩
    exact ⟨⟨σ g s, hSst g hg s s.2⟩, hT g hg s _ rfl⟩
  · intro S' hle hst
    rcases comap_bot_or_top hS T hT S' hst with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨s, rfl⟩ := hle hx
      rw [h s hx, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨s, rfl⟩
      exact h s
  · intro h
    exact hv0 (congrArg Subtype.val (hinj _ h))
  · intro θ hθ
    rw [← hT _ hθ ⟨v, hvS⟩ ⟨_, hSst _ hθ v hvS⟩ rfl, ← map_smul]
    exact congrArg T (Subtype.ext (hvw θ hθ))
  · intro μ w hw hw0 hww
    obtain ⟨s, rfl⟩ := hw
    refine hdom μ s s.2 ?_ ?_
    · intro h
      apply hw0
      obtain rfl : s = 0 := Subtype.ext h
      exact map_zero T
    · intro θ hθ
      exact key s _ hθ _ (hww θ hθ)

theorem scalar_of_range_le (hS : IsKTypeOf ε σ Λ S) (T : S →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' = σ k (T s))
    (hle : ∀ s, T s ∈ S) : ∃ c : ℂ, ∀ s, T s = c • (s : H) := by
  have hS' := hS
  obtain ⟨hfin, _, _, ⟨v, hvS, hv0, _⟩, _⟩ := hS'
  haveI : Nontrivial S := ⟨⟨⟨v, hvS⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (LinearMap.codRestrict S T hle)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  have hK : ∀ k ∈ Kset ε, ∀ s s' : S, (s' : H) = σ k s →
      (T - c • S.subtype) s' = σ k ((T - c • S.subtype) s) := by
    intro k hk s s' hs'
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply, map_sub, map_smul,
      hT k hk s s' hs', hs']
  rcases inj_or_zero hS (T - c • S.subtype) hK with h | h
  · exfalso
    have e : T w = c • (w : H) := congrArg Subtype.val hw.apply_eq_smul
    refine hw.2 (h w ?_)
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply, e, sub_self]
  · intro s
    have hs := h s
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply, sub_eq_zero] at hs
    exact hs

end

theorem kMap_lowKSub_scalar : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → ∀ T : lowKSub ε lam σ →ₗ[ℂ] H, (∀ k ∈ Kset ε, ∀ s s' : lowKSub ε lam σ, (s' : H) = σ k s → T s' = σ k (T s)) → ∃ c : ℂ, ∀ s, T s = c • (s : H) := by
  intro n ε lam H _ _ _ σ _ hK T hT
  rcases inj_or_zero hK T hT with h | h
  · refine scalar_of_range_le hK T hT ?_
    intro s
    have hle : LinearMap.range T ≤ lowKSub ε lam σ := le_sSup (range_isKType hK T hT h)
    exact hle ⟨s, rfl⟩
  · exact ⟨0, fun s => by rw [h s, zero_smul]⟩

end GlobalTheory.KMapInto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KMapLowestKTypeSubspaceEqScalarStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kMap_lowestKTypeSubspace_eq_scalar : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → ∀ T : lowKSub ε lam σ →ₗ[ℂ] H, (∀ k ∈ Kset ε, ∀ s s' : lowKSub ε lam σ, (s' : H) = σ k s → T s' = σ k (T s)) → ∃ c : ℂ, ∀ s, T s = c • (s : H) := by
  first | exact @GlobalTheory.KMapInto.kMap_lowKSub_scalar | exact GlobalTheory.KMapInto.kMap_lowKSub_scalar | (intros; apply GlobalTheory.KMapInto.kMap_lowKSub_scalar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightLeOfMemWtSpan
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.FilGrowth

def wtSpan {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (R : ℝ) : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ ν : Fin n → ℝ, IsWeight E ν z ∧ ∀ a, |ν a| ≤ R}

section Alg
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V}

theorem isWeight_step (hE : GlRel E) {ν : Fin n → ℝ} {z : V} (hz : IsWeight E ν z) (a b : Fin n) :
    IsWeight E (fun c => ν c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) (E a b z) := by
  intro c
  have h := congrArg (fun T : Module.End ℂ V => T z) (hE c c a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hz c, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases h1 : c = a
  · subst h1
    by_cases h2 : b = c
    · subst h2; simp
    · have h3 : ¬ c = b := fun h => h2 h.symm
      simp [h2, h3, add_smul, add_comm]
  · by_cases h2 : b = c
    · subst h2
      simp [h1, sub_smul]
      abel
    · have h3 : ¬ c = b := fun h => h2 h.symm
      simp [h1, h2, h3]

theorem exists_isWeight_word (hE : GlRel E) {ν : Fin n → ℝ} {z : V} (hz : IsWeight E ν z)
    (w : List (Fin n × Fin n)) : ∃ ν' : Fin n → ℝ, IsWeight E ν' (ew E w z) := by
  induction w with
  | nil => exact ⟨ν, by simpa [ew] using hz⟩
  | cons p w ih =>
    obtain ⟨ν', h⟩ := ih
    exact ⟨_, by simpa [ew] using isWeight_step hE h p.1 p.2⟩

theorem wtSpan_mono {R R' : ℝ} (h : R ≤ R') : wtSpan E R ≤ wtSpan E R' :=
  Submodule.span_mono fun _ ⟨ν, h1, h2⟩ => ⟨ν, h1, fun a => (h2 a).trans h⟩

theorem step_mem_wtSpan (hE : GlRel E) {R : ℝ} (a b : Fin n) {z : V} (hz : z ∈ wtSpan E R) :
    E a b z ∈ wtSpan E (R + 1) := by
  have : wtSpan E R ≤ (wtSpan E (R + 1)).comap (E a b) := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨ν, h1, h2⟩
    refine Submodule.subset_span ⟨_, isWeight_step hE h1 a b, fun c => ?_⟩
    have := abs_le.1 (h2 c)
    rw [abs_le]
    split_ifs <;> constructor <;> linarith [this.1, this.2]
  exact this hz

theorem word_mem_wtSpan (hE : GlRel E) {R : ℝ} (w : List (Fin n × Fin n)) {z : V}
    (hz : z ∈ wtSpan E R) : ew E w z ∈ wtSpan E (R + w.length) := by
  induction w with
  | nil => simpa [ew] using hz
  | cons p w ih =>
    have := step_mem_wtSpan hE p.1 p.2 ih
    simpa [ew, add_assoc] using this

end Alg

section Inner
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ V}

theorem weight_le_of_mem_wtSpan (hU : KUnit ε E) {R : ℝ} {μ : Fin n → ℝ} {y : V}
    (hy : y ∈ wtSpan E R) (hy0 : y ≠ 0) (hμ : IsWeight E μ y) (a : Fin n) : |μ a| ≤ R := by
  by_contra hlt
  have : wtSpan E R ≤ LinearMap.ker (innerₛₗ ℂ y) := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨ν, h1, h2⟩
    have hne : μ ≠ ν := by
      rintro rfl
      exact hlt (h2 a)
    exact kWtOrth V n ε E μ ν y z hU hμ h1 hne
  have h0 : ⟪y, y⟫_ℂ = 0 := this hy
  exact hy0 (inner_self_eq_zero.1 h0)

theorem kSpan_le_wtSpan (hE : GlRel E) (hU : KUnit ε E) {μ : Fin n → ℝ} {u : V}
    (hu : KHighest ε E μ u) : kSpan ε E u ≤ wtSpan E (Real.sqrt (ckv ε μ)) := by
  have hl := (kLow V n ε E μ u (glRel_kRel ε E hE) hu).1
  rw [hl]
  refine Submodule.span_le.2 ?_
  rintro y ⟨w, hw, rfl⟩
  have hmem : ew E w u ∈ kSpan ε E u := by
    rw [hl]; exact Submodule.subset_span ⟨w, hw, rfl⟩
  by_cases h0 : ew E w u = 0
  · rw [h0]; exact Submodule.zero_mem _
  obtain ⟨ν, hν⟩ := exists_isWeight_word hE hu.1 w
  have hb := kWtBound V n ε E μ ν u _ (glRel_kRel ε E hE) hU hu hmem h0 hν
  refine Submodule.subset_span ⟨ν, hν, fun a => ?_⟩
  apply Real.abs_le_sqrt
  refine le_trans ?_ hb
  unfold Formalism.REAL.nsq Formalism.REAL.dot
  rw [sq]
  exact Finset.single_le_sum (f := fun a => ν a * ν a) (fun i _ => mul_self_nonneg _)
    (Finset.mem_univ a)

theorem pfil_le_wtSpan (hE : GlRel E) (hU : KUnit ε E) {μ : Fin n → ℝ} {u : V}
    (hu : KHighest ε E μ u) (j : ℕ) : pfil ε E u j ≤ wtSpan E (Real.sqrt (ckv ε μ) + j) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨w, hw, -, y, hy, rfl⟩
  refine wtSpan_mono ?_ (word_mem_wtSpan hE w (kSpan_le_wtSpan hE hU hu hy))
  have : (w.length : ℝ) ≤ j := by exact_mod_cast hw
  linarith

end Inner

theorem uGrowth : UGrowth := by
  intro V _ _ n ε E μ c u hE hU hu hc hfd j x hx
  have hK := isUnitary_kUnit ε E hU
  obtain ⟨-, -, hst, -, hcyc, -, hfin⟩ := pfilFacts V n ε E u hE
  have hb := kCasBound V n ε E (pfil ε E u j) (Real.sqrt (ckv ε μ) + j) (hfin hfd j)
    (glRel_kRel ε E hE) hK (hst j) (by positivity)
    (fun ν y hy hy0 hν a => weight_le_of_mem_wtSpan hK (pfil_le_wtSpan hE hK hu j hy) hy0 hν a) x hx
  have hcas := casOnCyc V n E c u hE hc x (hcyc j hx)
  have hs := congrArg Complex.re (sumOfSquaresIdentity_holds V n ε E x hU)
  rw [Complex.ofReal_re, LinearMap.sub_apply, hcas, two_smul, LinearMap.add_apply, inner_sub_right,
    inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K] at hs
  have h2 : ((c : ℂ) * ((‖x‖ : ℂ)) ^ 2).re = c * ‖x‖ ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [Complex.sub_re, Complex.add_re] at hs
  have h3 : ((c : ℂ) * (RCLike.ofReal ‖x‖ : ℂ) ^ 2).re = c * ‖x‖ ^ 2 := h2
  rw [h3] at hs
  rw [hs]
  have h4 : -c * ‖x‖ ^ 2 ≤ |c| * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (neg_le_abs c) (by positivity)
  linarith

end GlobalTheory.FilGrowth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsDer
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.DerOf

variable {n : ℕ} {ε : Fin n → Bool}

theorem rd_congr {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : ∀ g, inUJ ε g → f g = f' g)
    {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) : Rd X f g = Rd X f' g := by
  unfold Rd
  congr 1
  funext t
  exact h _ (indefinite_unitary_mul_mem ε hg (exp_indefinite_unitary_holds n ε X hX t))

theorem eab_congr {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : ∀ g, inUJ ε g → f g = f' g)
    (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : Eab ε a b f g = Eab ε a b f' g := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold Eab Ec
  rw [rd_congr h h1 hg, rd_congr h h2 hg]

theorem J_single_J (a b : Fin n) :
    Jm ε * Matrix.single a b (1 : ℂ) * Jm ε = (sgn ε a b : ℂ) • Matrix.single a b (1 : ℂ) := by
  ext i j
  simp only [Jm, sgn, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    cases ε a <;> cases ε b <;> simp
  · simp [h]

theorem sgn_comm (a b : Fin n) : sgn ε a b = sgn ε b a := by
  simp only [sgn, eq_comm]

theorem sgn_sq (a b : Fin n) : (sgn ε a b : ℂ) * sgn ε a b = 1 := by
  unfold sgn
  split_ifs <;> simp

theorem cpart1_swap (a b : Fin n) : cpart1 ε (Matrix.single a b (1 : ℂ)) =
    ((-sgn ε a b : ℝ) : ℂ) • cpart1 ε (Matrix.single b a (1 : ℂ)) := by
  simp only [cpart1, conjTranspose_single, star_one, J_single_J, sgn_comm (ε := ε) b a]
  have := sgn_sq (ε := ε) a b
  push_cast
  match_scalars
  · linear_combination (-1 / 2 : ℂ) * this
  · ring

theorem cpart2_swap (a b : Fin n) : cpart2 ε (Matrix.single a b (1 : ℂ)) =
    ((sgn ε a b : ℝ) : ℂ) • cpart2 ε (Matrix.single b a (1 : ℂ)) := by
  simp only [cpart2, conjTranspose_single, star_one, J_single_J, sgn_comm (ε := ε) b a]
  have := sgn_sq (ε := ε) a b
  match_scalars
  · linear_combination (-1 / (2 * Complex.I) : ℂ) * this
  · ring

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {V : Submodule ℂ H}

theorem exists_D (hV : ∀ v ∈ V, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∃ v' ∈ V,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∃ D : Module.End ℂ V, inG ε X → ∀ v : V,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) (D v : H) 0 := by
  by_cases hX : inG ε X
  · choose d hd hd' using fun v : V => hV v v.2 X hX
    refine ⟨⟨⟨fun v => ⟨d v, hd v⟩, fun v w => Subtype.ext ?_⟩, fun c v => Subtype.ext ?_⟩, fun _ v => hd' v⟩
    · refine (hd' (v + w)).unique ?_
      simpa using (hd' v).fun_add (hd' w)
    · refine (hd' (c • v)).unique ?_
      simpa using (hd' v).fun_const_smul c
  · exact ⟨0, fun h => absurd h hX⟩

theorem rd_coef (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {v v' : H}
    (h : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0) (y : H)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Rd X (fun g => ⟪y, σ g v⟫_ℂ) g = ⟪y, σ g v'⟫_ℂ := by
  have h1 := (((innerSL ℂ y).comp (σ g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h
  refine Eq.trans ?_ h1.deriv
  unfold Rd
  congr 1
  funext t
  have := hσ.1.2 g hg _ (exp_indefinite_unitary_holds n ε X hX t)
  simp only [this]
  rfl

theorem skew (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {x x' y y' : H}
    (hx : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) x) x' 0)
    (hy : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) y) y' 0) :
    ⟪x', y⟫_ℂ = -⟪x, y'⟫_ℂ := by
  have h := hx.inner ℂ hy
  have hc : (fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • X)) x, σ (NormedSpace.exp ((t : ℂ) • X)) y⟫_ℂ)
      = fun _ => ⟪x, y⟫_ℂ := by
    funext t
    exact LinearIsometry.inner_map_map
      ⟨(σ (NormedSpace.exp ((t : ℂ) • X))).toLinearMap, hσ.2.1 _ (exp_indefinite_unitary_holds n ε X hX t)⟩ x y
  rw [hc] at h
  have h0 := h.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1, ContinuousLinearMap.one_apply] at h0
  linear_combination h0

theorem exists_isDer : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H),
    IsURepOn (UJset ε) σ →
    (∀ v ∈ V, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∃ v' ∈ V,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0) →
    (∀ v ∈ V, ∀ y : H, SmoothOnG ε (fun g => ⟪y, σ g v⟫_ℂ)) →
    ∃ E : Fin n → Fin n → Module.End ℂ V, IsDer ε σ V E := by
  intro n ε H _ _ _ σ V hσ hV hs
  choose D hD using exists_D hV
  have hone : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  have h1 : ∀ v : H, σ 1 v = v := fun v => by rw [hσ.1.1]; rfl
  have hc := fun a b : Fin n => complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  have hR : ∀ X, inG ε X → ∀ (v : V) (y : H) g, inUJ ε g →
      Rd X (fun g => ⟪y, σ g v⟫_ℂ) g = ⟪y, σ g (D X v)⟫_ℂ :=
    fun X hX v y g hg => rd_coef hσ hX (hD X hX v) y hg
  set E : Fin n → Fin n → Module.End ℂ V := fun a b =>
    D (cpart1 ε (Matrix.single a b 1)) + Complex.I • D (cpart2 ε (Matrix.single a b 1)) with hE
  have hEab : ∀ a b (v : V) (y : H) g, inUJ ε g →
      Eab ε a b (fun g => ⟪y, σ g v⟫_ℂ) g = ⟪y, σ g (E a b v)⟫_ℂ := by
    intro a b v y g hg
    unfold Eab Ec
    rw [hR _ (hc a b).1 v y g hg, hR _ (hc a b).2.1 v y g hg]
    simp [hE, inner_add_right, inner_smul_right]
  have hsm : ∀ X (r : ℝ), inG ε X → inG ε ((r : ℂ) • X) → ∀ v : V,
      (D ((r : ℂ) • X) v : H) = (r : ℂ) • (D X v : H) := by
    intro X r hX hrX v
    refine ext_inner_left ℂ fun y => ?_
    have := (rdLin n ε _ _ X X r 0 1 (hs v v.2 y) (hs v v.2 y) hX hX hone).2.1
    rwa [hR _ hX v y 1 hone, hR _ hrX v y 1 hone, h1, h1, ← inner_smul_right] at this
  refine ⟨E, ?_, ?_, ?_, fun v y => hs v v.2 y⟩
  · intro a b c d
    refine LinearMap.ext fun v => Subtype.ext (ext_inner_left ℂ fun y => ?_)
    have := eabGl n ε _ a b c d 1 (hs v v.2 y) hone
    rw [eab_congr (hEab c d v y) a b hone, eab_congr (hEab a b v y) c d hone] at this
    simp only [hEab _ _ _ y 1 hone, h1] at this
    split_ifs at this ⊢ <;> simpa [inner_sub_right] using this
  · intro a b x y
    have e1 := hsm _ (-sgn ε a b) (hc b a).1 (cpart1_swap a b ▸ (hc a b).1) y
    have e2 := hsm _ (sgn ε a b) (hc b a).2.1 (cpart2_swap a b ▸ (hc a b).2.1) y
    rw [← cpart1_swap] at e1
    rw [← cpart2_swap] at e2
    have s1 := skew hσ (hc a b).1 (hD _ (hc a b).1 x) (hD _ (hc a b).1 y)
    have s2 := skew hσ (hc a b).2.1 (hD _ (hc a b).2.1 x) (hD _ (hc a b).2.1 y)
    rw [e1, inner_smul_right] at s1
    rw [e2, inner_smul_right] at s2
    simp only [hE, Submodule.coe_inner, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add,
      Submodule.coe_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, s1, s2,
      Complex.conj_I]
    push_cast
    ring
  · intro X hX v
    convert hD X hX v using 1
    refine ext_inner_left ℂ fun y => ?_
    have := ecSumV n ε ℂ _ X 1 (hs v v.2 y) hone
    obtain ⟨e1, e2⟩ := (complex_parts_mem_lie_algebra_holds n ε X).2.2.2 hX
    simp only [eabV_eq, hEab _ _ _ y 1 hone, h1] at this
    rw [EcV, e1, e2, rdV_eq, rdV_eq, hR _ hX v y 1 hone, h1] at this
    simpa [Rd, inner_sum, inner_smul_right] using this.symm

end GlobalTheory.DerOf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTotallyIsotropicFlagComplexifiedSaturatedFlag
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTotallyIsotropicFlagComplexifiedSaturatedFlag
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

private theorem finrank_span_map_ringHom_eq_finrank {K : Type*} [Field K] {n : ℕ} (φ : K →+* ℂ)
    (U : Submodule K (Fin n → K)) :
    Module.finrank ℂ (Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (U : Set (Fin n → K)))) =
      Module.finrank K U := by

  have hle : ∀ V : Submodule K (Fin n → K),
      Module.finrank ℂ (Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (V : Set (Fin n → K)))) ≤
        Module.finrank K V := by
    intro V
    let b := Module.finBasis K V
    have hsub : (fun y : Fin n → K => fun l => φ (y l)) '' (V : Set (Fin n → K)) ⊆
        Submodule.span ℂ (Set.range fun k => fun l => φ ((b k : Fin n → K) l)) := by
      rintro _ ⟨u, hu, rfl⟩
      simp only [SetLike.mem_coe]
      have hu' : u = ∑ k, b.repr ⟨u, hu⟩ k • (b k : Fin n → K) := by
        have h := congrArg Subtype.val (b.sum_repr ⟨u, hu⟩)
        simp only [Submodule.coe_sum, SetLike.val_smul] at h
        exact h.symm
      have hφ : (fun l => φ (u l)) = ∑ k, φ (b.repr ⟨u, hu⟩ k) • fun l => φ ((b k : Fin n → K) l) := by
        conv_lhs => rw [hu']
        ext l
        set_option synthInstance.maxHeartbeats 100000 in
          simp [Finset.sum_apply, map_sum, map_mul]
      rw [hφ]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    calc Module.finrank ℂ (Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (V : Set (Fin n → K))))
        ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range fun k => fun l => φ ((b k : Fin n → K) l))) :=
          Submodule.finrank_mono (Submodule.span_le.2 hsub)
      _ ≤ Fintype.card (Fin (Module.finrank K V)) := finrank_range_le_card _
      _ = Module.finrank K V := Fintype.card_fin _
  have hsup : ∀ V V' : Submodule K (Fin n → K), V ⊔ V' = ⊤ →
      Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (V : Set (Fin n → K))) ⊔
        Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (V' : Set (Fin n → K))) = ⊤ := by
    intro V V' h
    rw [eq_top_iff]
    intro z _
    have hz : z = ∑ i, z i • (Pi.single i (1 : ℂ) : Fin n → ℂ) := by
      ext l
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hz]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have hsingle : (fun l => φ ((Pi.single i (1 : K) : Fin n → K) l)) = (Pi.single i (1 : ℂ) : Fin n → ℂ) := by
      ext l
      by_cases hl : l = i
      · subst hl; simp
      · simp [Pi.single_eq_of_ne hl]
    rw [← hsingle]
    have hmem : (Pi.single i (1 : K) : Fin n → K) ∈ V ⊔ V' := by rw [h]; exact Submodule.mem_top
    obtain ⟨u, hu, u', hu', hsum⟩ := Submodule.mem_sup.1 hmem
    rw [← hsum]
    have hadd : (fun l => φ ((u + u') l)) = (fun l => φ (u l)) + fun l => φ (u' l) := by
      ext l; simp
    rw [hadd]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨u, hu, rfl⟩) (Submodule.subset_span ⟨u', hu', rfl⟩)
  obtain ⟨U', hU'⟩ := Submodule.exists_isCompl U
  have h1 := hle U
  have h2 := hle U'
  have h3 : Module.finrank K U + Module.finrank K U' = n := by
    have := Submodule.finrank_add_eq_of_isCompl hU'
    simpa using this
  have h4 := Submodule.finrank_add_le_finrank_add_finrank
    (Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (U : Set (Fin n → K))))
    (Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (U' : Set (Fin n → K))))
  rw [hsup U U' hU'.sup_eq_top, finrank_top, Module.finrank_fin_fun] at h4
  omega

private theorem span_map_ringHom_span_eq_span_map {K : Type*} [Field K] {n : ℕ} (φ : K →+* ℂ) (X : Set (Fin n → K)) :
    Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (Submodule.span K X : Set (Fin n → K))) =
      Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have h0 : (fun l => φ ((0 : Fin n → K) l)) = 0 := by ext; simp
      change (fun l => φ ((0 : Fin n → K) l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X)
      rw [h0]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have h : (fun l => φ ((x + y) l)) = (fun l => φ (x l)) + fun l => φ (y l) := by ext; simp
      change (fun l => φ (x l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X) at hx
      change (fun l => φ (y l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X) at hy
      change (fun l => φ ((x + y) l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X)
      rw [h]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      have h : (fun l => φ ((c • x) l)) = φ c • fun l => φ (x l) := by ext; simp
      change (fun l => φ (x l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X) at hx
      change (fun l => φ ((c • x) l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X)
      rw [h]; exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem isIsoFlag_flagAt_of_isSatFlag :
    ∀ (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) (a : ℕ) (j : Fin a → ℕ)
      (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)),
      IsSatFlag I Λ j S → ∀ v, IsIsoFlag (I.ε v) j (flagAt I S v) := by
  intro I Λ a j S hS v
  obtain ⟨h0, hmono, hrk, -, hiso⟩ := hS
  have hdet : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hPQ : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hinj : Function.Injective (Matrix.mulVecLin (I.P v)⁻¹) := by
    intro x y hxy
    have h := congrArg (fun z => I.P v *ᵥ z) hxy
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hPQ] using h

  have hspan : ∀ i, flagAt I S v i =
      (Submodule.span ℂ ((fun y : Fin I.n → I.E => fun l => I.φ v (y l)) '' (S i : Set _))).map
        (Matrix.mulVecLin (I.P v)⁻¹) := by
    intro i
    rw [Submodule.map_span, Set.image_image]
    rfl
  have hfr : ∀ i, Module.finrank ℂ (flagAt I S v i) = Formalism.HN.rkK (S i) := by
    intro i
    rw [hspan i, ← (Submodule.equivMapOfInjective _ hinj _).finrank_eq]
    show _ = Module.finrank I.E (Submodule.span I.E (S i : Set (Fin I.n → I.E)))
    rw [← span_map_ringHom_span_eq_span_map, finrank_span_map_ringHom_eq_finrank]

  have hstar : ∀ x : I.E, I.φ v (starRingEnd I.E x) = starRingEnd ℂ (I.φ v x) := fun x =>
    I.cm.cmUnram.2.1 (I.φ v) x
  have hJ : ((I.P v)⁻¹)ᴴ * (Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹) = I.J.map (I.φ v) := by
    rw [← I.P_spec v]
    calc ((I.P v)⁻¹)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v * (I.P v)⁻¹)
        = (I.P v * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = I.J.map (I.φ v) := by rw [hPQ]; simp
  have hgen : ∀ x y : Fin I.n → ℂ, star ((I.P v)⁻¹ *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm (I.ε v) *ᵥ ((I.P v)⁻¹ *ᵥ y)) =
      star x ⬝ᵥ (I.J.map (I.φ v) *ᵥ y) := by
    intro x y
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
    simp only [Matrix.mulVec_mulVec, hJ]
  have hpair : ∀ s ∈ S (Fin.last a), ∀ t ∈ S (Fin.last a),
      star (fun l => I.φ v (s l)) ⬝ᵥ (I.J.map (I.φ v) *ᵥ fun l => I.φ v (t l)) = 0 := by
    intro s hs t ht
    have h := hiso s hs t ht
    have h' := congrArg (I.φ v) h
    rw [map_zero] at h'
    rw [← h']
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, map_sum, map_mul, hstar, Finset.mul_sum, mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Submodule.span ℂ _ = ⊥
    rw [Submodule.span_eq_bot]
    rintro _ ⟨y, hy, rfl⟩
    rw [h0] at hy
    have hy0 : y = 0 := by simpa using hy
    subst hy0
    ext l
    simp [Matrix.mulVec, dotProduct]
  · intro i k hik
    exact Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.2 (hmono hik)))
  · intro i
    rw [hfr, hfr]
    exact hrk i
  · intro x hx y hy
    rw [hspan] at hx hy
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.1 hy
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hgen]
    clear hx hy

    have hgen1 : ∀ g ∈ (fun y : Fin I.n → I.E => fun l => I.φ v (y l)) '' (S (Fin.last a) : Set (Fin I.n → I.E)),
        ∀ z ∈ Submodule.span ℂ
          ((fun y : Fin I.n → I.E => fun l => I.φ v (y l)) '' (S (Fin.last a) : Set (Fin I.n → I.E))),
          star g ⬝ᵥ (I.J.map (I.φ v) *ᵥ z) = 0 := by
      rintro _ ⟨s, hs, rfl⟩ z hz
      induction hz using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨t, ht, rfl⟩ := hu
        exact hpair s hs t ht
      | zero => simp
      | add u u' _ _ hu hu' => rw [Matrix.mulVec_add, dotProduct_add, hu, hu', add_zero]
      | smul c u _ hu => rw [Matrix.mulVec_smul, dotProduct_smul, hu, smul_zero]
    induction hw using Submodule.span_induction with
    | mem u hu => exact hgen1 u hu w' hw'
    | zero => simp
    | add u u' _ _ hu hu' => rw [star_add, add_dotProduct, hu, hu', add_zero]
    | smul c u _ hu => rw [star_smul, smul_dotProduct, hu, smul_zero]

end GlobalTheory.FlagMeas
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTotallyIsotropicFlagComplexifiedSaturatedFlagStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTotallyIsotropicFlag_complexified_saturatedFlag : ∀ (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I Λ j S → ∀ v, IsIsoFlag (I.ε v) j (flagAt I S v) := by
  first | exact @GlobalTheory.FlagMeas.isIsoFlag_flagAt_of_isSatFlag | exact GlobalTheory.FlagMeas.isIsoFlag_flagAt_of_isSatFlag | (intros; apply GlobalTheory.FlagMeas.isIsoFlag_flagAt_of_isSatFlag <;> assumption)
end
end

module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairFirstStep
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesInducedNode
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JCh

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorInduction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorInduction
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

theorem allLeaves_mono {E : Type} [Field E] [NumberField E] [IsCMField E]
    {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} (hPQ : ∀ M V, P M V → Q M V) :
    ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves P → t.AllLeaves Q := by
  intro N t
  induction t with
  | leaf V z => exact fun h => hPQ _ _ h
  | node t₁ t₂ i₁ i₂ => exact fun h => ⟨i₁ h.1, i₂ h.2⟩

theorem factorStep_holds : FactorStep := by
  set_option synthInstance.maxHeartbeats 400000 in
    intro h4 E _ _ _ N W hW
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · refine ⟨fun _ => ∅, fun M => ⟨Set.finite_empty, by simp⟩, fun K _ =>
        ⟨fun _ => ∅, fun M => ⟨Set.finite_empty, by simp⟩, ?_⟩⟩
      intro U _ _ _ _ _ _ hU
      obtain ⟨ψ, hψ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
      refine ⟨.leaf ⊤ 0, LinearMap.id, trivial, Or.inl ⟨rfl, rfl, rfl⟩, Or.inl rfl,
        fun _ _ _ => rfl, fun χ _ => ?_, ψ, hψ, hne⟩
      exact ⟨(mulChi 0 (Model.absC E 0)).symm χ, trivial, by simp⟩
    · obtain ⟨Ω, hΩ, h⟩ := h4 E N W hW
      refine ⟨Ω, hΩ, fun K hK => ?_⟩
      obtain ⟨Θ, hΘ, h'⟩ := h K hK
      refine ⟨Θ, hΘ, ?_⟩
      intro U hs ha hg hn hc hi hU
      obtain ⟨t, T, hG, hL, he, hm, hne⟩ := h' U hN hs ha hg hn hc hi hU
      exact ⟨t, T, red_of_leaves hL, hG, allLeaves_mono (fun M V h => Or.inr h.2) hL, he, hm, hne⟩

end GlobalTheory.CompanionTheory.EGlue

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorInductionStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factor_induction : GlobalTheory.CompanionTheory.EGlue.FactorStep := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.factorStep_holds | exact GlobalTheory.CompanionTheory.EGlue.factorStep_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.factorStep_holds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscreteInfimum
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscreteInfimum
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.EGlue

theorem discInf : DiscInf := by
  intro E _ _ _ M V hV τ
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  obtain ⟨m, hm, h⟩ := exists_multiset_qdet (Eop (a := M) τ) (((M : ℂ) - 1) / 2) φ f hf
  refine ⟨m, hm, fun u ψ hψ => ?_⟩
  obtain ⟨c, h1⟩ := GlobalTheory.DiscLocEx.exists_scalarD hV (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩)
    (GlobalTheory.SpehInfChar.cap_commute_act τ u)
  have h2 : f (cap τ u φ) = _ := h u
  rw [h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one] at h2
  rw [h1 ψ hψ, h2]

end GlobalTheory.CompanionTheory.EGlue

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscreteInfimumStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_infimum : GlobalTheory.CompanionTheory.EGlue.DiscInf := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.discInf | exact GlobalTheory.CompanionTheory.EGlue.discInf | (intros; apply GlobalTheory.CompanionTheory.EGlue.discInf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HullGeneration
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HullGeneration
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

theorem typeB_of_mem_span {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {K : Subgroup (GL (Fin N) (Af E))} {W : Submodule ℂ (Kinf E N → ℂ)} {S : Set (Sm E N)}
    (hS : ∀ φ ∈ S, TypeB K W φ) {φ : Sm E N} (hφ : φ ∈ Submodule.span ℂ S) : TypeB K W φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨fun _ _ _ => rfl, fun _ => W.zero_mem⟩
  | add x y _ _ hx hy =>
    refine ⟨fun u hu g => ?_, fun g => W.add_mem (hx.2 g) (hy.2 g)⟩
    show x.1 (g * finGL E N u) + y.1 (g * finGL E N u) = x.1 g + y.1 g
    rw [hx.1 u hu g, hy.1 u hu g]
  | smul c x _ hx =>
    refine ⟨fun u hu g => ?_, fun g => W.smul_mem c (hx.2 g)⟩
    show c • x.1 (g * finGL E N u) = c • x.1 g
    rw [hx.1 u hu g]

theorem hullGen : HullGen := by
  intro E _ _ _ N K W S hS hfd
  have hst : _root_.GlobalTheory.CuspRep.IsStable (hull S) := fun o φ hφ =>
    Submodule.mem_sInf.2 fun U hU => hU.2 o φ (Submodule.mem_sInf.1 hφ U hU)
  refine ⟨hst, ?_⟩
  have hsub : S ⊆ hull S := fun φ hφ => Submodule.mem_sInf.2 fun U hU => hU.1 hφ
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional _).2 hfd
  have htS : ∀ φ ∈ t, φ ∈ Submodule.span ℂ S := fun φ hφ => ht ▸ Submodule.subset_span hφ
  refine ⟨t, fun φ hφ => typeB_of_mem_span hS (htS φ hφ), fun φ hφ => ?_, fun U' hU' htU => ?_⟩
  · exact (Submodule.span_le.2 hsub) (htS φ hφ)
  · refine sInf_le ⟨?_, hU'⟩
    have h : Submodule.span ℂ S ≤ U' := ht ▸ Submodule.span_le.2 htU
    exact Submodule.subset_span.trans h

end GlobalTheory.CompanionTheory.EGlue

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HullGenerationStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hull_generation : GlobalTheory.CompanionTheory.EGlue.HullGen := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.hullGen | exact GlobalTheory.CompanionTheory.EGlue.hullGen | (intros; apply GlobalTheory.CompanionTheory.EGlue.hullGen <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceType
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceType
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.SliceTypePf

theorem restrict_left {A B : Type} [One B] (W₁ : Submodule ℂ (A → ℂ)) (W₂ : Submodule ℂ (B → ℂ)) (f : A × B → ℂ)
    (hf : f ∈ Submodule.span ℂ {f : A × B → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :
    (fun k : A => f (k, 1)) ∈ W₁ := by
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨w₁, h₁, w₂, -, rfl⟩ := h
    have : (fun k : A => w₁ k * w₂ 1) = w₂ 1 • w₁ := by
      funext k
      simp [mul_comm]
    simpa [this] using W₁.smul_mem _ h₁
  | zero => exact W₁.zero_mem
  | add f g _ _ hf hg => exact W₁.add_mem hf hg
  | smul c f _ hf => exact W₁.smul_mem c hf

theorem restrict_right {A B : Type} [One A] (W₁ : Submodule ℂ (A → ℂ)) (W₂ : Submodule ℂ (B → ℂ)) (f : A × B → ℂ)
    (hf : f ∈ Submodule.span ℂ {f : A × B → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :
    (fun k : B => f (1, k)) ∈ W₂ := by
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨w₁, -, w₂, h₂, rfl⟩ := h
    have : (fun k : B => w₁ 1 * w₂ k) = w₁ 1 • w₂ := by
      funext k
      simp
    simpa [this] using W₂.smul_mem _ h₂
  | zero => exact W₂.zero_mem
  | add f g _ _ hf hg => exact W₂.add_mem hf hg
  | smul c f _ hf => exact W₂.smul_mem c hf

theorem main : GlobalTheory.CompanionTheory.EGlue.SliceType := by
  intro E _ _ _ a b K₁ K₂ W₁ W₂ F hF
  obtain ⟨hl, hk⟩ := hF
  refine ⟨?_, ?_⟩
  · rintro φ m₂ hφ
    refine ⟨?_, ?_⟩
    · intro u hu g
      have := hl u hu 1 K₂.one_mem (g, m₂)
      simpa [hφ, Prod.mk_mul_mk] using this
    · intro g
      have := restrict_left W₁ W₂ _ (hk (g, m₂))
      simpa [hφ, Prod.mk_mul_mk] using this
  · rintro φ m₁ hφ
    refine ⟨?_, ?_⟩
    · intro u hu g
      have := hl 1 K₁.one_mem u hu (m₁, g)
      simpa [hφ, Prod.mk_mul_mk] using this
    · intro g
      have := restrict_right W₁ W₂ _ (hk (m₁, g))
      simpa [hφ, Prod.mk_mul_mk] using this

end GlobalTheory.CompanionTheory.EGlue.SliceTypePf

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceTypeStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slice_type : GlobalTheory.CompanionTheory.EGlue.SliceType := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.SliceTypePf.main | exact GlobalTheory.CompanionTheory.EGlue.SliceTypePf.main | (intros; apply GlobalTheory.CompanionTheory.EGlue.SliceTypePf.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceShift
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceShift
open Filter Topology

namespace GlobalTheory.CompanionTheory.EGlue

theorem convShift_holds : ConvShift := by
  intro E _ _ _ N t s z z₀ h hz
  induction h with
  | leaf V w w₀ hw => exact Conv.leaf V (fun k => w k + z k) (w₀ + z₀) (hw.add hz)
  | node _ _ i₁ i₂ => exact Conv.node i₁ i₂

end GlobalTheory.CompanionTheory.EGlue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceShiftStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_shift : GlobalTheory.CompanionTheory.EGlue.ConvShift := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.convShift_holds | exact GlobalTheory.CompanionTheory.EGlue.convShift_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.convShift_holds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSlices
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSlices
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.PairSl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem exists_slices (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (F : H E a b → ℂ)
    (hF : F ∈ pairSpace U₁ U₂) :
    (∀ m₂, ∃ φ ∈ U₁, φ.1 = fun x => F (x, m₂)) ∧ (∀ m₁, ∃ φ ∈ U₂, φ.1 = fun x => F (m₁, x)) := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := h
    refine ⟨fun m₂ => ⟨φ₂.1 m₂ • φ₁, U₁.smul_mem _ h₁, ?_⟩, fun m₁ => ⟨φ₁.1 m₁ • φ₂, U₂.smul_mem _ h₂, ?_⟩⟩
    · funext x
      simp [mul_comm]
    · funext x
      simp
  | zero =>
    refine ⟨fun m₂ => ⟨0, U₁.zero_mem, ?_⟩, fun m₁ => ⟨0, U₂.zero_mem, ?_⟩⟩
    · funext x
      simp
    · funext x
      simp
  | add F G _ _ h₁ h₂ =>
    refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨φ, hφ, e⟩ := h₁.1 m₂
      obtain ⟨ψ, hψ, e'⟩ := h₂.1 m₂
      refine ⟨φ + ψ, U₁.add_mem hφ hψ, ?_⟩
      funext x
      have i := congrFun e x
      have i' := congrFun e' x
      simp_all
    · obtain ⟨φ, hφ, e⟩ := h₁.2 m₁
      obtain ⟨ψ, hψ, e'⟩ := h₂.2 m₁
      refine ⟨φ + ψ, U₂.add_mem hφ hψ, ?_⟩
      funext x
      have i := congrFun e x
      have i' := congrFun e' x
      simp_all
  | smul r F _ h =>
    refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨φ, hφ, e⟩ := h.1 m₂
      refine ⟨r • φ, U₁.smul_mem r hφ, ?_⟩
      funext x
      have i := congrFun e x
      simp_all
    · obtain ⟨φ, hφ, e⟩ := h.2 m₁
      refine ⟨r • φ, U₂.smul_mem r hφ, ?_⟩
      funext x
      have i := congrFun e x
      simp_all

end GlobalTheory.CompanionTheory.EGlue.PairSl

namespace GlobalTheory.CompanionTheory.EGlue

theorem pairSlices : PairSlices := by
  intro E _ _ _ a b U₁ U₂ F hF
  obtain ⟨h₁, h₂⟩ := PairSl.exists_slices U₁ U₂ F hF
  refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
  · obtain ⟨φ, hφ, e⟩ := h₁ m₂
    have hex : ∃ φ : Sm E a, φ.1 = fun x => F (x, m₂) := ⟨φ, e⟩
    have hs : sl₁ F m₂ = hex.choose := by simp only [sl₁, dif_pos hex]
    have hc : hex.choose = φ := Subtype.ext (hex.choose_spec.trans e.symm)
    rw [hs, hc]
    exact ⟨hφ, e⟩
  · obtain ⟨φ, hφ, e⟩ := h₂ m₁
    have hex : ∃ φ : Sm E b, φ.1 = fun x => F (m₁, x) := ⟨φ, e⟩
    have hs : sl₂ F m₁ = hex.choose := by simp only [sl₂, dif_pos hex]
    have hc : hex.choose = φ := Subtype.ext (hex.choose_spec.trans e.symm)
    rw [hs, hc]
    exact ⟨hφ, e⟩

end GlobalTheory.CompanionTheory.EGlue

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSlicesStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_slices : GlobalTheory.CompanionTheory.EGlue.PairSlices := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.pairSlices | exact GlobalTheory.CompanionTheory.EGlue.pairSlices | (intros; apply GlobalTheory.CompanionTheory.EGlue.pairSlices <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitTrees
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitTrees
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.LimT

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def lr : {N : ℕ} → Tr E N → ℕ
  | _, .leaf _ _ => 0
  | _, @Tr.node _ _ _ _ r _ _ _ => r

theorem lr_le {N : ℕ} (u : Tr E N) : lr u ≤ N := by
  cases u with
  | leaf V z => exact Nat.zero_le _
  | node t₁ t₂ => exact Nat.le_add_right _ _

theorem leaf_of {N : ℕ} (u : Tr E N) (h : lr u = 0) (hr : Red u) : ∃ V z, u = .leaf V z := by
  cases u with
  | leaf V z => exact ⟨V, z, rfl⟩
  | node t₁ t₂ => exact absurd (show _ = 0 from h) hr.1.ne'

theorem node_of {n : ℕ} (u : Tr E n) {r s : ℕ} (h : n = r + s) (hl : lr u = r) (hr : 0 < r) (hred : Red u) :
    ∃ (t₁ : Tr E r) (t₂ : Tr E s), h ▸ u = Tr.node t₁ t₂ ∧ Red t₁ ∧ Red t₂ := by
  cases u with
  | leaf V z => exact absurd (show 0 = r from hl) hr.ne
  | @node r' s' t₁ t₂ =>
    have hl' : r' = r := hl
    subst hl'
    have hs : s' = s := by omega
    subst hs
    exact ⟨t₁, t₂, rfl, hred.2.2.1, hred.2.2.2⟩

theorem pigeon {n : ℕ} (c : ℕ → ℕ) (h : ∀ k, c k ≤ n) : ∃ (r : ℕ) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ k, c (φ k) = r := by
  let f : ℕ → Fin (n + 1) := fun k => ⟨c k, Nat.lt_succ_of_le (h k)⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber f
  have hinf : (f ⁻¹' {y}).Infinite := Set.infinite_coe_iff.mp hy
  obtain ⟨φ, hφ, h2⟩ := extraction_of_frequently_atTop (P := fun k => f k = y)
    (Nat.frequently_atTop_iff_infinite.mpr hinf)
  exact ⟨y, φ, hφ, fun k => congrArg Fin.val (h2 k)⟩

theorem emb_refl {N : ℕ} (V : Submodule ℂ (Sm E N)) : Emb V (· ∈ V) :=
  ⟨LinearMap.id, fun _ h => h, fun _ _ h => h, fun _ _ _ => rfl⟩

theorem main (hc : ConvComp) (hs : TrStable) (hg : Graft)
    (Θs Θf : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ωs Ωf : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) (N : ℕ)
    (hL : LimLeafP N Θs Ωs Θf Ωf) (hR : ReproAll E) (n : ℕ) : n ≤ N → ∀ (t : ℕ → Tr E n) (R : ℝ), (∀ k, Red (t k)) →
    (∀ k, (t k).Good) → (∀ k, (t k).AllLeaves (ListLeaf Θs Ωs)) →
    (∀ k, LeafZ (fun M V z => 0 < M → InfBdd R V ∧ ‖z‖ ≤ R) (t k)) →
    ∃ (φ : ℕ → ℕ) (t' : ℕ → Tr E n) (s : Tr E n), StrictMono φ ∧ Conv t' s ∧ Red s ∧ s.Good ∧
      s.AllLeaves (ListLeaf Θf Ωf) ∧ (∀ k, (t' k).Disc) ∧ ∀ k, Emb (t (φ k)).space (· ∈ (t' k).space) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn t R hred hgood hlist hz
  obtain ⟨r, φ₀, hφ₀, hr⟩ := pigeon (n := n) (fun k => lr (t k)) (fun k => lr_le _)
  by_cases h0 : r = 0
  · subst h0
    choose V z hVz using fun k => leaf_of (t (φ₀ k)) (hr k) (hred _)
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have hk : ∀ k, t (φ₀ k) = .leaf ⊤ 0 := by
        intro k
        have h := hgood (φ₀ k)
        rw [hVz k] at h
        rcases h with ⟨-, hV, hz'⟩ | ⟨h, -, -⟩
        · rw [hVz k, hV, hz']
        · exact absurd h (lt_irrefl _)
      refine ⟨φ₀, fun _ => .leaf ⊤ 0, .leaf ⊤ 0, hφ₀, Conv.leaf ⊤ (fun _ => 0) 0 tendsto_const_nhds, trivial,
        Or.inl ⟨rfl, rfl, rfl⟩, Or.inl rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩, fun k => ?_⟩
      rw [hk k]
      exact emb_refl _
    · have hG : ∀ k, IsDiscrete (V k) ∧ (z k).re = 0 := by
        intro k
        have h := hgood (φ₀ k)
        rw [hVz k] at h
        rcases h with ⟨h, -, -⟩ | ⟨-, h⟩
        · exact absurd h hn0.ne'
        · exact h
      have hT : ∀ k, ∃ K' ∈ Θs n, ∃ W' ∈ Ωs n, HasType K' W' (V k) := by
        intro k
        have h := hlist (φ₀ k)
        rw [hVz k] at h
        rcases h with h | h
        · exact absurd h hn0.ne'
        · exact h
      have hB : ∀ k, InfBdd R (V k) ∧ ‖z k‖ ≤ R := by
        intro k
        have h := hz (φ₀ k)
        rw [hVz k] at h
        exact h hn0
      obtain ⟨φ, t', s, hφ, hc', hrs, hgs, hls, hd, he⟩ := hL n hn0 hn V z R hR (fun k => (hG k).1)
        (fun k => (hG k).2) hT (fun k => (hB k).1) (fun k => (hB k).2)
      refine ⟨φ₀ ∘ φ, t', s, hφ₀.comp hφ, hc', hrs, hgs, hls, hd, fun k => ?_⟩
      have e : t ((φ₀ ∘ φ) k) = .leaf (V (φ k)) (z (φ k)) := hVz _
      rw [e]
      exact he k
  · have hr0 : 0 < r := Nat.pos_of_ne_zero h0
    have hrn : r ≤ n := by
      have := lr_le (t (φ₀ 0))
      rwa [hr 0] at this
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hrn
    choose a b hab ha hb using fun k => node_of (t (φ₀ k)) rfl (hr k) hr0 (hred _)
    have hab' : ∀ k, t (φ₀ k) = .node (a k) (b k) := hab
    have hs0 : 0 < s := by
      have h := hred (φ₀ 0)
      rw [hab' 0] at h
      exact h.2.1
    have hG : ∀ k, (a k).Good ∧ (b k).Good := fun k => by
      have h := hgood (φ₀ k)
      rw [hab' k] at h
      exact h
    have hT : ∀ k, (a k).AllLeaves (ListLeaf Θs Ωs) ∧ (b k).AllLeaves (ListLeaf Θs Ωs) := fun k => by
      have h := hlist (φ₀ k)
      rw [hab' k] at h
      exact h
    have hB : ∀ k, LeafZ (fun M V z => 0 < M → InfBdd R V ∧ ‖z‖ ≤ R) (a k) ∧
        LeafZ (fun M V z => 0 < M → InfBdd R V ∧ ‖z‖ ≤ R) (b k) := fun k => by
      have h := hz (φ₀ k)
      rw [hab' k] at h
      exact h
    obtain ⟨φ₁, a', sa, hφ₁, hca, hra, hga, hla, hda, hea⟩ := ih r (by omega) (by omega) a R ha
      (fun k => (hG k).1) (fun k => (hT k).1) (fun k => (hB k).1)
    obtain ⟨φ₂, b', sb, hφ₂, hcb, hrb, hgb, hlb, hdb, heb⟩ := ih s (by omega) (by omega) (fun k => b (φ₁ k)) R
      (fun k => hb _) (fun k => (hG _).2) (fun k => (hT _).2) (fun k => (hB _).2)
    refine ⟨φ₀ ∘ φ₁ ∘ φ₂, fun k => .node (a' (φ₂ k)) (b' k), .node sa sb, hφ₀.comp (hφ₁.comp hφ₂),
      Conv.node (hc E r a' sa φ₂ hca hφ₂) hcb, ⟨hr0, hs0, hra, hrb⟩, ⟨hga, hgb⟩, ⟨hla, hlb⟩,
      fun k => ⟨hda _, hdb k⟩, fun k => ?_⟩
    have e : t ((φ₀ ∘ φ₁ ∘ φ₂) k) = .node (a (φ₁ (φ₂ k))) (b (φ₁ (φ₂ k))) := hab' _
    rw [e]
    exact hg E r s _ _ _ _ (hs E _ _ (disc_stable (good_disc (hG _).1))) (hs E _ _ (disc_stable (hda _)))
      (hs E _ _ (disc_stable (good_disc (hG _).2))) (hs E _ _ (disc_stable (hdb _))) (hea (φ₂ k)) (heb k)

theorem limTrees : ConvComp → LimTrees := by
  intro hc hs hg E _ _ _ Θs Θf Ωs Ωf N hL hR n hn t R h₁ h₂ h₃ h₄
  exact main hc hs hg Θs Θf Ωs Ωf N hL hR n hn t R h₁ h₂ h₃ h₄

end GlobalTheory.CompanionTheory.EGlue.LimT

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitTreesStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_trees : GlobalTheory.CompanionTheory.EGlue.ConvComp → GlobalTheory.CompanionTheory.EGlue.LimTrees := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.LimT.limTrees | exact GlobalTheory.CompanionTheory.EGlue.LimT.limTrees | (intros; apply GlobalTheory.CompanionTheory.EGlue.LimT.limTrees <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceComposition
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceComposition
open Filter Topology
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem convComp_proved : ConvComp := by
  intro E _ _ _ N t s φ h hφ
  induction h with
  | leaf V z z₀ h => exact Conv.leaf V (fun k => z (φ k)) z₀ (h.comp hφ.tendsto_atTop)
  | node _ _ i₁ i₂ => exact Conv.node i₁ i₂

end GlobalTheory.CompanionTheory.EGlue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceCompositionStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_composition : GlobalTheory.CompanionTheory.EGlue.ConvComp := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.convComp_proved | exact GlobalTheory.CompanionTheory.EGlue.convComp_proved | (intros; apply GlobalTheory.CompanionTheory.EGlue.convComp_proved <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorLimit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorLimit
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.FactorLimProof

theorem multiset_eq_of_prod_shift {m m' : Multiset ℂ}
    (h : ∀ u : ℂ, (m.map (u + ·)).prod = (m'.map (u + ·)).prod) : m = m' :=
  by apply _root_.UpperTheory.Reformulated.B.MultisetSeparation.msetSep <;> assumption

theorem factorLim_of_parts : GlobalTheory.CompanionTheory.EGlue.ConvComp → GlobalTheory.CompanionTheory.EGlue.LimTrees → GlobalTheory.CompanionTheory.EGlue.LeafBound →
    GlobalTheory.CompanionTheory.EGlue.ConvInf → GlobalTheory.CompanionTheory.EGlue.InfOfEq → GlobalTheory.CompanionTheory.EGlue.CapEquiv → GlobalTheory.CompanionTheory.EGlue.MCloseFacts →
    GlobalTheory.CompanionTheory.EGlue.FactorLim := by
  intro _ hLT hLB hCI hIE hCE hMF hTS hGr hIT E _ _ _ Θs Θf Ωs Ωf N t ψ m n B hLim hRA hRed hGood hAll hψ hψ0 hCap hB hCl
  have leaf := fun k => hLB E N (t k) (ψ k) (m k) B hIT (hGood k) (hψ k) (hψ0 k) (hCap k) (hB k)
  obtain ⟨φ, t', s, hφ, hConv, hRs, hGs, hAs, hDisc, hEmb⟩ :=
    hLT hTS hGr E Θs Θf Ωs Ωf N hLim hRA N le_rfl t (2 * B) hRed hGood hAll leaf
  refine ⟨φ, t', s, hφ, hConv, hRs, hGs, hAs, hDisc, fun τ => ?_, hEmb⟩
  obtain ⟨m₀, mk, hs, hk, hprod⟩ := hCI E N t' s τ hConv hGs
  have hst : ∀ k, IsStable (t (φ k)).space := fun k =>
    hTS E N _ (disc_stable (good_disc (hGood _)))
  have hmk : ∀ k, mk k = m (φ k) τ := by
    intro k
    obtain ⟨e, he1, he2, he3⟩ := hEmb k
    have hne : e (ψ (φ k)) ≠ 0 := fun h => hψ0 _ (he2 _ (hψ _) h)
    have hc : CapEig (e (ψ (φ k))) (m (φ k)) := hCE E N _ e _ _ (hst k) he3 (hψ _) (hCap _)
    exact hIE E N (t' k) _ _ τ _ hIT (hk k) (he1 _ (hψ _)) hne hc
  have hlim : ∀ u : ℂ, Tendsto (fun k => ((m (φ k) τ).map (u + ·)).prod) atTop
      (𝓝 (((n τ).map (u + ·)).prod)) := fun u =>
    hMF.2.2 (fun k => m (φ k) τ) (n τ)
      (fun ε hε => hφ.tendsto_atTop.eventually (hCl τ ε hε)) u
  have hm₀ : m₀ = n τ := multiset_eq_of_prod_shift fun u =>
    tendsto_nhds_unique (by simpa only [hmk] using hprod u) (hlim u)
  exact hm₀ ▸ hIT E N s τ m₀ hs

end GlobalTheory.CompanionTheory.EGlue.FactorLimProof
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorLimitStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factor_limit : GlobalTheory.CompanionTheory.EGlue.ConvComp → GlobalTheory.CompanionTheory.EGlue.LimTrees → GlobalTheory.CompanionTheory.EGlue.LeafBound → GlobalTheory.CompanionTheory.EGlue.ConvInf → GlobalTheory.CompanionTheory.EGlue.InfOfEq → GlobalTheory.CompanionTheory.EGlue.CapEquiv → GlobalTheory.CompanionTheory.EGlue.MCloseFacts → GlobalTheory.CompanionTheory.EGlue.FactorLim := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.FactorLimProof.factorLim_of_parts | exact GlobalTheory.CompanionTheory.EGlue.FactorLimProof.factorLim_of_parts | (intros; apply GlobalTheory.CompanionTheory.EGlue.FactorLimProof.factorLim_of_parts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairEmbedding
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairEmbedding
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem pairEmb_of_steps : PairSlices → PairStep₁ → PairStep₂ → PairEmb := by
  intro hS h₁ h₂ E _ _ _ a b ι _ K₁ K₂ W₁ W₂ X₁ Y₁ X₂ Y₂ G hW₁ hW₂ hX₁ hX₂ hE₁ hE₂ hG hGp hGt
  obtain ⟨e₁, he₁Y, he₁i, he₁q⟩ := hE₁
  obtain ⟨e₂, he₂Y, he₂i, he₂q⟩ := hE₂
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hG
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hi
  obtain ⟨hmem, hval⟩ := (hS E a b X₁ X₂ (G i) (hGp i)).1 x.2
  have hφ : sl₁ (G i) x.2 ≠ 0 := by
    intro h0
    apply hx
    have h := congrFun hval x.1
    rw [h0] at h
    simpa using h.symm
  obtain ⟨n₁, p₁, t₁, c₁⟩ := h₁ E a b ι K₁ K₂ W₁ W₂ X₁ Y₁ X₂ e₁ G hW₁ hW₂ hX₁ he₁q he₁Y hGp hGt
    ⟨i, x.2, sl₁ (G i) x.2, hval, fun h0 => hφ (he₁i _ hmem h0)⟩
  obtain ⟨j, hj⟩ := Function.ne_iff.mp n₁
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hj
  obtain ⟨hmem₂, hval₂⟩ := (hS E a b Y₁ X₂ (ap₁ e₁ (G j)) (p₁ j)).2 y.1
  have hψ : sl₂ (ap₁ e₁ (G j)) y.1 ≠ 0 := by
    intro h0
    apply hy
    have h := congrFun hval₂ y.2
    rw [h0] at h
    simpa using h.symm
  obtain ⟨n₂, p₂, t₂, c₂⟩ := h₂ E a b ι K₁ K₂ W₁ W₂ Y₁ X₂ Y₂ e₂ (fun i => ap₁ e₁ (G i)) hW₁ hW₂ hX₂ he₂q he₂Y p₁ t₁
    ⟨j, y.1, sl₂ (ap₁ e₁ (G j)) y.1, hval₂, fun h0 => hψ (he₂i _ hmem₂ h0)⟩
  exact ⟨fun i => ap₂ e₂ (ap₁ e₁ (G i)), n₂, p₂, t₂, fun h c hc => c₂ h c (c₁ h c hc)⟩

end GlobalTheory.CompanionTheory.EGlue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairEmbeddingStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_embedding : GlobalTheory.CompanionTheory.EGlue.PairSlices → GlobalTheory.CompanionTheory.EGlue.PairStep₁ → GlobalTheory.CompanionTheory.EGlue.PairStep₂ → GlobalTheory.CompanionTheory.EGlue.PairEmb := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.pairEmb_of_steps | exact GlobalTheory.CompanionTheory.EGlue.pairEmb_of_steps | (intros; apply GlobalTheory.CompanionTheory.EGlue.pairEmb_of_steps <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopologicalInfimum
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopologicalInfimum
open GlobalTheory.CompanionTheory.EGlue

noncomputable section

open GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.EGlue.Gl0

theorem topInf : GlobalTheory.CompanionTheory.EGlue.TopInf := by
  intro E _ _ _ τ
  refine ⟨rfl, fun u φ _ => ?_⟩
  simp [cap, Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm]

end GlobalTheory.CompanionTheory.EGlue.Gl0

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopologicalInfimumStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topological_infimum : GlobalTheory.CompanionTheory.EGlue.TopInf := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.Gl0.topInf | exact GlobalTheory.CompanionTheory.EGlue.Gl0.topInf | (intros; apply GlobalTheory.CompanionTheory.EGlue.Gl0.topInf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceStrip
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceStrip
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.ConvStripProof

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def nodeRank : {N : ℕ} → Tr E N → Option ℕ
  | _, .leaf _ _ => none
  | _, @Tr.node _ _ _ _ r _ _ _ => some r

theorem nodeRank_heq {N M : ℕ} (u : Tr E N) (v : Tr E M) (h : N = M) (hh : HEq u v) :
    nodeRank u = nodeRank v := by
  subst h
  rw [eq_of_heq hh]

theorem twists_length_strip : ∀ {N : ℕ} (u : Tr E N), u.strip.twists.length = u.twists.length := by
  intro N u
  induction u with
  | leaf V z => rfl
  | node t₁ t₂ i₁ i₂ => simp [Tr.strip, Tr.twists, i₁, i₂]

theorem twists_length_eq {N : ℕ} {u v : Tr E N} (h : u.strip = v.strip) :
    u.twists.length = v.twists.length := by
  rw [← twists_length_strip u, h, twists_length_strip]

theorem leaf_of_strip {N : ℕ} (u : Tr E N) (V : Submodule ℂ (Sm E N)) (w : ℂ)
    (h : u.strip = .leaf V w) : ∃ z, u = .leaf V z := by
  revert V w h
  cases u with
  | leaf V' z =>
    intro V w h
    simp only [Tr.strip] at h
    injection h with _ h₁
    exact ⟨z, by rw [h₁]⟩
  | node a b =>
    intro V w h
    have := congrArg nodeRank h
    simp [Tr.strip, nodeRank] at this

theorem node_of_strip_eq : ∀ {N : ℕ} (u : Tr E N) {r s : ℕ} (_ : N = r + s) (x : Tr E r) (y : Tr E s),
    HEq u.strip (Tr.node x y) →
    ∃ (a : Tr E r) (b : Tr E s), HEq u (Tr.node a b) ∧ a.strip = x ∧ b.strip = y := by
  intro N u
  cases u with
  | leaf V z =>
    intro r s hN x y h
    subst hN
    have := congrArg nodeRank (eq_of_heq h)
    simp [Tr.strip, nodeRank] at this
  | @node r' s' a b =>
    intro r s hN x y h
    have h₁ : r' = r := by
      have := nodeRank_heq _ _ hN h
      simpa [Tr.strip, nodeRank] using this
    subst h₁
    have h₂ : s' = s := by omega
    subst h₂
    have h₃ := eq_of_heq h
    simp only [Tr.strip] at h₃
    injection h₃ with _ _ e₁ e₂
    exact ⟨a, b, HEq.rfl, e₁, e₂⟩

theorem node_of_strip {r s : ℕ} (u : Tr E (r + s)) (x : Tr E r) (y : Tr E s)
    (h : u.strip = Tr.node x y) :
    ∃ (a : Tr E r) (b : Tr E s), u = Tr.node a b ∧ a.strip = x ∧ b.strip = y := by
  obtain ⟨a, b, e, h₁, h₂⟩ := node_of_strip_eq u rfl x y (heq_of_eq h)
  exact ⟨a, b, eq_of_heq e, h₁, h₂⟩

theorem getD_append_left (A B : List ℂ) {i : ℕ} (h : i < A.length) :
    (A ++ B).getD i 0 = A.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right (A B : List ℂ) (i : ℕ) :
    (A ++ B).getD (A.length + i) 0 = B.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem getD_of_le (A : List ℂ) {i : ℕ} (h : A.length ≤ i) : A.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem conv_forward {N : ℕ} {t : ℕ → Tr E N} {s : Tr E N} (h : Conv t s) :
    (∀ k, (t k).strip = s.strip) ∧
      ∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (s.twists.getD i 0)) := by
  induction h with
  | leaf V z z₀ h =>
    refine ⟨fun k => rfl, fun i => ?_⟩
    cases i with
    | zero => simpa [Tr.twists] using h
    | succ i => simp [Tr.twists]
  | @node r s t₁ t₂ s₁ s₂ _ _ i₁ i₂ =>
    refine ⟨fun k => ?_, fun i => ?_⟩
    · simp only [Tr.strip, i₁.1 k, i₂.1 k]
    · have hl : ∀ k, (t₁ k).twists.length = s₁.twists.length := fun k => twists_length_eq (i₁.1 k)
      simp only [Tr.twists]
      by_cases hi : i < s₁.twists.length
      · rw [getD_append_left _ _ hi]
        have : (fun k => ((t₁ k).twists ++ (t₂ k).twists).getD i 0) = fun k => (t₁ k).twists.getD i 0 :=
          funext fun k => getD_append_left _ _ (by rw [hl k]; exact hi)
        rw [this]
        exact i₁.2 i
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hi)
        rw [getD_append_right]
        have : (fun k => ((t₁ k).twists ++ (t₂ k).twists).getD (s₁.twists.length + j) 0) =
            fun k => (t₂ k).twists.getD j 0 :=
          funext fun k => by rw [← hl k, getD_append_right]
        rw [this]
        exact i₂.2 j

theorem conv_backward : ∀ {N : ℕ} (s : Tr E N) (t : ℕ → Tr E N), (∀ k, (t k).strip = s.strip) →
    (∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (s.twists.getD i 0))) → Conv t s := by
  intro N s
  induction s with
  | leaf V z₀ =>
    intro t hs ht
    choose z hz using fun k => leaf_of_strip (t k) V 0 (hs k)
    obtain rfl : t = fun k => .leaf V (z k) := funext hz
    exact Conv.leaf V z z₀ (by simpa [Tr.twists] using ht 0)
  | @node r s s₁ s₂ i₁ i₂ =>
    intro t hs ht
    choose a b hab ha hb using fun k => node_of_strip (t k) s₁.strip s₂.strip (hs k)
    obtain rfl : t = fun k => .node (a k) (b k) := funext hab
    have hl : ∀ k, (a k).twists.length = s₁.twists.length := fun k => twists_length_eq (ha k)
    simp only [Tr.twists] at ht
    refine Conv.node (i₁ a ha fun i => ?_) (i₂ b hb fun i => ?_)
    · by_cases hi : i < s₁.twists.length
      · have h := ht i
        rw [getD_append_left _ _ hi] at h
        have e : (fun k => ((a k).twists ++ (b k).twists).getD i 0) = fun k => (a k).twists.getD i 0 :=
          funext fun k => getD_append_left _ _ (by rw [hl k]; exact hi)
        rwa [e] at h
      · have e : (fun k => (a k).twists.getD i 0) = fun _ => (0 : ℂ) :=
          funext fun k => getD_of_le _ (by rw [hl k]; exact not_lt.mp hi)
        rw [e, getD_of_le _ (not_lt.mp hi)]
        exact tendsto_const_nhds
    · have h := ht (s₁.twists.length + i)
      rw [getD_append_right] at h
      have e : (fun k => ((a k).twists ++ (b k).twists).getD (s₁.twists.length + i) 0) =
          fun k => (b k).twists.getD i 0 :=
        funext fun k => by rw [← hl k, getD_append_right]
      rwa [e] at h

theorem convStrip : ConvStrip := fun _ _ _ _ _ t s =>
  ⟨conv_forward, fun h => conv_backward s t h.1 h.2⟩

end GlobalTheory.CompanionTheory.EGlue.ConvStripProof

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceStripStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_strip : GlobalTheory.CompanionTheory.EGlue.ConvStrip := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.ConvStripProof.convStrip | exact GlobalTheory.CompanionTheory.EGlue.ConvStripProof.convStrip | (intros; apply GlobalTheory.CompanionTheory.EGlue.ConvStripProof.convStrip <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.E45FinalGluing
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

theorem eFinalGlue_of (hCS : ConvStrip) (hCC : ConvComp) (hFS : FactorStep) (hLL : LimLists) (hOS : OneStep)
    (hFL : FactorLim) (hMC : MCloseFacts) (hPE : PairEmb) (hPS : PairSlices) (hST : SliceType) : InfinitesimalCharacterGlue := by
  intro hE3 hSep hLim hGraft hTw hTr hLV hAD hUn hInf E _ _ _ a b W₁ W₂ hW₁ hW₂
  obtain ⟨Ωs₁, hΩs₁, S₁⟩ := hFS hSep E a W₁ hW₁
  obtain ⟨Ωs₂, hΩs₂, S₂⟩ := hFS hSep E b W₂ hW₂
  obtain ⟨Ωf₁, hΩf₁, X₁⟩ := hLL hLim hTw E a Ωs₁ hΩs₁
  obtain ⟨Ωf₂, hΩf₂, X₂⟩ := hLL hLim hTw E b Ωs₂ hΩs₂
  refine ⟨Ωf₁, Ωf₂, hΩf₁, hΩf₂, fun K₁ K₂ hK₁ hK₂ => ?_⟩
  obtain ⟨Θs₁, hΘs₁, F₁⟩ := S₁ K₁ hK₁
  obtain ⟨Θs₂, hΘs₂, F₂⟩ := S₂ K₂ hK₂
  obtain ⟨Θf₁, hΘf₁, P₁⟩ := X₁ Θs₁ hΘs₁
  obtain ⟨Θf₂, hΘf₂, P₂⟩ := X₂ Θs₂ hΘs₂
  refine ⟨Θf₁, Θf₂, hΘf₁, hΘf₂, ?_⟩
  intro D ι _ M m₁ m₂ n₁ n₂ C lam lam₀ f hC hRep hcont hne hL hWL hTy hs1 hs2 ha1 ha2 hi1 hi2 heig hconv hR1 hR2 hgap hlam
  have hfar : ∀ᶠ k in atTop, ∀ τ, MClose (1 / 8) (m₁ k τ) (n₁ τ) ∧ MClose (1 / 8) (m₂ k τ) (n₂ τ) :=
    Filter.eventually_all.2 fun τ => hconv τ (1 / 8) (by norm_num)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hfar
  have h3 := fun k => hE3 E a b D ι M (f k) K₁ K₂ W₁ W₂ (m₁ k) (m₂ k) hK₁ hK₂ hW₁ hW₂ (hcont k) (hL k) (hWL k)
    (hTy k) (hs1 k) (hs2 k) (ha1 k) (ha2 k) (hi1 k) (hi2 k)
  have hone := fun k => hOS E a b ι K₁ K₂ W₁ W₂ Θs₁ Θs₂ Ωs₁ Ωs₂ (f (k + k₀)) (m₁ (k + k₀)) (m₂ (k + k₀)) hW₁ hW₂ F₁ F₂
    (hne _) (hTy _) (hs1 _) (hs2 _) (h3 _).2.2.1 (h3 _).2.2.2.1 (h3 _).2.2.2.2.1 (h3 _).2.2.2.2.2.1
    (h3 _).2.2.2.2.2.2.1 (h3 _).2.2.2.2.2.2.2.1 (h3 _).2.2.2.2.2.2.2.2.1 (h3 _).2.2.2.2.2.2.2.2.2.1
    (fun τ => hMC.2.1 (1 / 8) _ _ (by norm_num) (hk₀ (k + k₀) (by omega) τ).1 (hgap τ).1)
    (fun τ => hMC.2.1 (1 / 8) _ _ (by norm_num) (hk₀ (k + k₀) (by omega) τ).2 (hgap τ).2)
    (h3 _).2.2.2.2.2.2.2.2.2.2
  choose t₁ t₂ G ψ₁ ψ₂ hr₁ hr₂ hg₁ hg₂ hl₁ hl₂ hG0 hGm hGt hGe hp₁ hp₁0 hc₁ hp₂ hp₂0 hc₂ using hone
  have hB : ∀ n : (E →+* ℂ) → Multiset ℂ, ∃ B : ℝ, ∀ τ, ∀ y ∈ n τ, ‖y‖ ≤ B := fun n => by
    classical
    obtain ⟨B, hB⟩ := ((Finset.univ.biUnion fun τ => (n τ).toFinset).image norm).finite_toSet.bddAbove
    refine ⟨B, fun τ y hy => hB ?_⟩
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Multiset.mem_toFinset]
    exact ⟨y, ⟨τ, hy⟩, rfl⟩
  obtain ⟨B₁, hB₁⟩ := hB n₁
  obtain ⟨B₂, hB₂⟩ := hB n₂
  obtain ⟨φ₁, t₁', s₁, hφ₁, hC₁, hs₁R, hs₁G, hs₁L, hD₁, hI₁, hE₁⟩ := hFL hTr hGraft hInf E Θs₁ Θf₁ Ωs₁ Ωf₁ a t₁ ψ₁
    (fun k => m₁ (k + k₀)) n₁ (B₁ + 1 / 8) P₁ hRep hr₁ hg₁ hl₁ hp₁ hp₁0 hc₁
    (fun k τ => hMC.1 _ _ _ _ (hk₀ (k + k₀) (by omega) τ).1 (hB₁ τ))
    (fun τ ε hε => ((tendsto_add_atTop_nat k₀).eventually (hconv τ ε hε)).mono fun _ h => h.1)
  obtain ⟨φ₂, t₂', s₂, hφ₂, hC₂, hs₂R, hs₂G, hs₂L, hD₂, hI₂, hE₂⟩ := hFL hTr hGraft hInf E Θs₂ Θf₂ Ωs₂ Ωf₂ b
    (fun k => t₂ (φ₁ k)) (fun k => ψ₂ (φ₁ k))
    (fun k => m₂ (φ₁ k + k₀)) n₂ (B₂ + 1 / 8) P₂ hRep (fun k => hr₂ _) (fun k => hg₂ _) (fun k => hl₂ _)
    (fun k => hp₂ _) (fun k => hp₂0 _) (fun k => hc₂ _)
    (fun k τ => hMC.1 _ _ _ _ (hk₀ (φ₁ k + k₀) (by omega) τ).2 (hB₂ τ))
    (fun τ ε hε => (((tendsto_add_atTop_nat k₀).comp hφ₁.tendsto_atTop).eventually (hconv τ ε hε)).mono fun _ h => h.2)
  have hstab : ∀ {N : ℕ} {t : Tr E N}, t.Good → IsStable t.space := fun h => hTr E _ _ (disc_stable (good_disc h))
  have hG' := fun k => hPE E a b ι K₁ K₂ W₁ W₂ (t₁ (φ₁ (φ₂ k))).space (t₁' (φ₂ k)).space (t₂ (φ₁ (φ₂ k))).space (t₂' k).space
    (G (φ₁ (φ₂ k))) hW₁ hW₂ (hstab (hg₁ _)) (hstab (hg₂ _)) (hE₁ _) (hE₂ _) (hG0 _) (hGm _) (hGt _)
  choose G' hG'0 hG'm hG't hG'e using hG'
  have hCC₁ := (hCS E a _ _).1 (hCC E a _ _ φ₂ hC₁ hφ₂)
  have hCC₂ := (hCS E b _ _).1 hC₂
  obtain ⟨F, hF0, hFm, hFt, hFe⟩ := hLV hAD E a b ι (fun k => t₁' (φ₂ k)) t₂' s₁ s₂ K₁ K₂ W₁ W₂ C
    (fun k => lam (φ₁ (φ₂ k) + k₀)) lam₀ G' hK₁ hK₂ hW₁ hW₂ hC hs₁G hs₂G (fun k => hD₁ _) hD₂ hCC₁.1 hCC₂.1 hCC₁.2 hCC₂.2
    hG'0 hG'm hG't (fun k h hh => hG'e k h _ (hGe _ h _ (heig _ h hh)))
    (fun h hh => (hlam h hh).comp ((tendsto_add_atTop_nat k₀).comp (hφ₁.comp hφ₂).tendsto_atTop))
  obtain ⟨i, hi⟩ : ∃ i, F i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hF0 (funext hcon)
  obtain ⟨x, hx⟩ : ∃ x, F i x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hi (funext hcon)
  have hsl := hPS E a b _ _ (F i) (hFm i)
  have hn₁ : sl₁ (F i) x.2 ≠ 0 := fun h => hx (by
    have := congrFun (hsl.1 x.2).2 x.1
    rw [h] at this
    exact this.symm)
  have hn₂ : sl₂ (F i) x.1 ≠ 0 := fun h => hx (by
    have := congrFun (hsl.2 x.1).2 x.2
    rw [h] at this
    exact this.symm)
  have hb₁ : s₁.space ≠ ⊥ := fun h => hn₁ (by simpa [h] using (hsl.1 x.2).1)
  have hb₂ : s₂.space ≠ ⊥ := fun h => hn₂ (by simpa [h] using (hsl.2 x.1).1)
  exact ⟨s₁, s₂, F, hs₁G, hs₂G, hUn E a s₁ n₁ hs₁G hb₁ hI₁ hR1, hUn E b s₂ n₂ hs₂G hb₂ hI₂ hR2, hs₁L, hs₂L,
    hI₁, hI₂, hF0, hFm, hFt, hFe⟩

theorem eFinalGlue : PositivityTheory.Rg.BcB.SpectralAccumulation.InfinitesimalCharacterGlue :=
  have hPS := GlobalTheory.T.pair_slices
  have hP1 := GlobalTheory.T.pair_first_step hPS
  have hP2 := GlobalTheory.T.pair_second_step hPS
  have hCE := GlobalTheory.T.capacity_equivalence
  have hDI := GlobalTheory.T.discrete_infimum
  have hTI := GlobalTheory.T.topological_infimum
  have hIE := GlobalTheory.T.infimum_of_equality
  have hCS := GlobalTheory.T.convergence_strip
  have hCC := GlobalTheory.T.convergence_composition
  have hMC := GlobalTheory.T.closure_facts_alt
  eFinalGlue_of hCS hCC GlobalTheory.T.factor_induction (GlobalTheory.T.limit_lists hCS GlobalTheory.T.convergence_shift hCC)
    (GlobalTheory.T.single_gluing hPS GlobalTheory.T.pair_restriction GlobalTheory.T.pair_finite_dimensional GlobalTheory.T.slice_type hP1 hP2 GlobalTheory.T.hull_generation hCE)
    (GlobalTheory.T.factor_limit hCC (GlobalTheory.T.limit_trees hCC) (GlobalTheory.T.leaf_bound_alt hDI hTI hIE) (GlobalTheory.T.convergence_infimum hDI hTI) hIE hCE hMC)
    hMC (GlobalTheory.T.pair_embedding hPS hP1 hP2) hPS GlobalTheory.T.slice_type

end GlobalTheory.CompanionTheory.EGlue

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.E45FinalGluingStatement
open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.e45_final_gluing : PositivityTheory.Rg.BcB.SpectralAccumulation.InfinitesimalCharacterGlue := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.eFinalGlue | exact GlobalTheory.CompanionTheory.EGlue.eFinalGlue | (intros; apply GlobalTheory.CompanionTheory.EGlue.eFinalGlue <;> assumption)
end PositivityTheory.Rg.BcB.SpectralAccumulation
end

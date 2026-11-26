module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousWittExtendByZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumHeckeSeriesBorelSphericalIntegralCosets

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPatternIterated
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPatternIterated
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain.IterPattern

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem intM_submatrix_iff {a b : Type*} (e : a ≃ b) (M : Matrix b b k) :
    IntM (M.submatrix e e) ↔ IntM M := by
  constructor
  · intro h i j
    simpa using h (e.symm i) (e.symm j)
  · intro h i j
    exact h (e i) (e j)

theorem symm_mem_KO_iff {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b)
    (g : GL b k) : (reGL e).symm g ∈ KO k a ↔ g ∈ KO k b := by
  rw [mem_KO, mem_KO, ← map_inv (reGL e).symm g, reGL_symm_val, reGL_symm_val,
    intM_submatrix_iff, intM_submatrix_iff]

theorem mem_reindex_J {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (P : GlobalTheory.StepData.TypeDatum k a)
    (e : a ≃ b) (g : GL b k) : g ∈ (P.reindex e).J ↔ (reGL e).symm g ∈ P.J := Iff.rfl

variable {ρ κ l j : ℕ} {t : Type}

theorem free_ll (x y : Ix (Fin κ ⊕ Fin l) t j) :
    FreeIx ρ (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inl y)) ↔ FreeIx ρ x y := by
  rcases x with a | ⟨i, s⟩ <;> rcases y with b | ⟨i', s'⟩ <;> simp [ixSucc, FreeIx]

theorem free_lr (x : Ix (Fin κ ⊕ Fin l) t j) (s : t) :
    FreeIx ρ (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inr s)) := by
  rcases x with a | ⟨i, s'⟩ <;> simp [ixSucc, FreeIx, (Fin.castSucc_lt_last _).le]

theorem not_free_rl (s : t) (y : Ix (Fin κ ⊕ Fin l) t j) :
    ¬ FreeIx ρ (ixSucc _ t j (.inr s)) (ixSucc _ t j (.inl y)) := by
  rcases y with b | ⟨i, s'⟩
  · simp [ixSucc, FreeIx]
  · simp [ixSucc, FreeIx]

theorem free_rr (s s' : t) : FreeIx ρ (ixSucc (Fin κ ⊕ Fin l) t j (.inr s)) (ixSucc _ t j (.inr s')) := by
  simp [ixSucc, FreeIx]

variable [Fintype t] [DecidableEq t]

theorem base_iff (P : GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin l))
    (hP : ∀ g : GL (Fin κ ⊕ Fin l) k, g ∈ P.J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1)
    (g : GL (Ix (Fin κ ⊕ Fin l) t 0) k) :
    g ∈ (P.reindex (ixZero _ t)).J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  have hz : ∀ a b : Fin κ ⊕ Fin l, FreeIx ρ (ixZero _ t a) (ixZero _ t b) ↔ FreeTop ρ a b := fun _ _ => Iff.rfl
  rw [mem_reindex_J, hP, symm_mem_KO_iff]
  simp only [reGL_symm_val]
  refine and_congr_right fun _ => ⟨fun h a b hab => ?_, fun h a b hab => ?_⟩
  · obtain ⟨a, rfl⟩ := (ixZero _ t).surjective a
    obtain ⟨b, rfl⟩ := (ixZero _ t).surjective b
    have := h a b (fun hf => hab ((hz a b).2 hf))
    simpa [Matrix.one_apply] using this
  · have := h _ _ (fun hf => hab ((hz a b).1 hf))
    simpa [Matrix.one_apply] using this

theorem step_iff (Q : GlobalTheory.StepData.TypeDatum k (Ix (Fin κ ⊕ Fin l) t j))
    (μ : kˣ →* ℂˣ) (hμ : IsTame μ)
    (hQ : ∀ g : GL (Ix (Fin κ ⊕ Fin l) t j) k, g ∈ Q.J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1)
    (g : GL (Ix (Fin κ ⊕ Fin l) t (j + 1)) k) :
    g ∈ ((Q.step t μ hμ).reindex (ixSucc _ t j)).J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  rw [mem_reindex_J, TypeDatum.step_J, TypeDatum.mem_stepJ_iff, symm_mem_KO_iff]
  constructor
  · rintro ⟨hK, ⟨g', hg', hval⟩, hC⟩
    refine ⟨hK, fun a b hab => ?_⟩
    obtain ⟨a, rfl⟩ := (ixSucc _ t j).surjective a
    obtain ⟨b, rfl⟩ := (ixSucc _ t j).surjective b
    rcases a with x | s <;> rcases b with y | s'
    ·
      have hxy : ¬ FreeIx ρ x y := fun h => hab ((free_ll x y).2 h)
      have hold := ((hQ g').1 hg').2 x y hxy
      have hentry : g'.val x y = g.val (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inl y)) := by
        rw [hval, reGL_symm_val]; rfl
      rw [hentry] at hold
      simpa [Matrix.one_apply] using hold
    · exact absurd (free_lr x s') hab
    ·
      have hlow := hC s y
      simpa [Matrix.one_apply, reGL_symm_val, Matrix.toBlocks₂₁] using hlow
    · exact absurd (free_rr s s') hab
  · rintro ⟨hK, hfree⟩
    have hK' : (reGL (ixSucc _ t j)).symm g ∈ KO k _ := (symm_mem_KO_iff _ g).2 hK
    have hC : MaxM ((reGL (ixSucc _ t j)).symm g).val.toBlocks₂₁ := by
      intro s y
      have hnf := hfree _ _ (not_free_rl s y)
      simpa [Matrix.one_apply, reGL_symm_val, Matrix.toBlocks₂₁] using hnf
    refine ⟨hK, ?_, hC⟩
    obtain ⟨⟨g', hg'K, hg'val⟩, -⟩ := exists_diag_blocks hK' hC
    refine ⟨g', (hQ g').2 ⟨hg'K, fun x y hxy => ?_⟩, hg'val⟩
    have hnf := hfree _ _ (fun h => hxy ((free_ll x y).1 h))
    have hentry : g'.val x y = g.val (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inl y)) := by
      rw [hg'val, reGL_symm_val]; rfl
    rw [hentry]
    simpa [Matrix.one_apply] using hnf

theorem iter_iff (P : GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin l))
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (hP : ∀ g : GL (Fin κ ⊕ Fin l) k, g ∈ P.J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1)
    (j : ℕ) (g : GL (Ix (Fin κ ⊕ Fin l) t j) k) :
    g ∈ (P.iter t μ hμ j).J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  induction j with
  | zero =>
    rw [TypeDatum.iter_zero]
    exact base_iff P hP g
  | succ j ih =>
    rw [TypeDatum.iter_succ]
    exact step_iff _ (μ (j + 1)) (hμ _) ih g

end GlobalTheory.SymChain.IterPattern

theorem GlobalTheory.SymChain.pattern_iter (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ)
    (t : Type) [Fintype t] [DecidableEq t] :
    S.Pattern t := by
  intro j g
  have hP : ∀ x : GL (Fin κ ⊕ Fin (s + 1)) k, x ∈ S.P.J ↔
      x ∈ KO k _ ∧ ∀ a b, ¬ FreeTop S.ρ a b →
        valuation k (x.val a b - (1 : Matrix _ _ k) a b) < 1 := by
    intro x
    rw [S.sym.1 x]
    constructor
    · rintro ⟨u, hu, γ, hγ, x₀, hx₀, hxb⟩
      refine ⟨⟨x₀, hx₀⟩, fun a b hab => ?_⟩
      rw [← hx₀, GlobalTheory.SymPattern.entry_lt_iff, hxb]
      exact GlobalTheory.SymPattern.pat_of_mul S.ρ u ((Radical.mem_N_iff u).mp hu) γ hγ a b hab
    · rintro ⟨⟨x₀, hx₀⟩, hpat⟩
      obtain ⟨u, hu, γ, hγ, he⟩ := GlobalTheory.SymPattern.exists_of_pat S.ρ
        (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) x₀) (fun a b hab => by
          rw [← GlobalTheory.SymPattern.entry_lt_iff, hx₀]
          exact hpat a b hab)
      exact ⟨u, (Radical.mem_N_iff u).mpr hu, γ, hγ, x₀, hx₀, he⟩
  exact IterPattern.iter_iff S.P S.μ S.tame hP j g
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPatternIteratedStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLevelChain_pattern_iterated : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t := by
  first | exact @GlobalTheory.SymChain.pattern_iter | exact GlobalTheory.SymChain.pattern_iter | (intros; apply GlobalTheory.SymChain.pattern_iter <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChLApply
open MeasureTheory Matrix

noncomputable section
namespace GlobalTheory.PartRed
open GlobalTheory.SplitWeil GlobalTheory.RootEx

section Gen
variable {k : Type} [Field k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]

def fillAt (β : Matrix R Q k) (E I : Finset (R × Q)) (x : Matrix R Q k) (y : I → k) : Matrix R Q k :=
  Matrix.of fun r q => if h : (r, q) ∈ I then y ⟨(r, q), h⟩ else if (r, q) ∈ E then β r q else x r q

variable [TopologicalSpace k] [MeasurableSpace k]

def red (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k)
    (E I : Finset (R × Q)) (Φ : Matrix R Q k → ℂ) (x : Matrix R Q k) : ℂ :=
  ∫ y : I → k, Φ (fillAt β E I x y) * (ψ (-w (fillAt β E I x y)) : ℂ) ∂(Measure.pi fun _ => ν)

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def Kills (L : SB (Matrix R Q k) →ₗ[ℂ] M) (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k)
    (β : Matrix R Q k) (E I : Finset (R × Q)) : Prop :=
  ∀ Φ : SB (Matrix R Q k), red ψ ν w β E I Φ.1 = 0 → L Φ = 0

def EvalLaw (L : SB (Matrix R Q k) →ₗ[ℂ] M) (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k)
    (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q) : Prop :=
  ∀ (b : k) (Φ : SB (Matrix R Q k)), ∃ Φ' : SB (Matrix R Q k), L Φ' = L Φ ∧
    ∀ x, red ψ ν w β E I Φ'.1 x = (ψ (b * (x e.1 e.2 - β e.1 e.2)) : ℂ) * red ψ ν w β E I Φ.1 x

def IntLaw (L : SB (Matrix R Q k) →ₗ[ℂ] M) (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k)
    (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q) : Prop :=
  ∀ (a : k) (Φ : SB (Matrix R Q k)), ∃ Φ' : SB (Matrix R Q k), L Φ' = L Φ ∧
    ∀ x, red ψ ν w β E I Φ'.1 x = red ψ ν w β E I Φ.1 (x + Matrix.single e.1 e.2 a)

end Gen

section Flat
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def chL : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k →ₗ[k] k where
  toFun := ch
  map_add' x y := by simp [ch, Finset.sum_add_distrib]
  map_smul' a x := by simp [ch, Finset.mul_sum]

theorem chL_apply (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : chL x = ch x := rfl

open Classical in
def fixSet (ρ : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => (∃ i, e.2 = Sum.inr i ∧ i.val ≤ ρ ∧ ¬ Free (ρ + 1) e) ∨
    (∃ l s, e.1 = Sum.inr l ∧ ρ < l.val ∧ e.2 = Sum.inl s)

open Classical in
def transSet (ρ : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => Free (ρ + 1) e ∧ ∀ i, e.2 = Sum.inr i → ρ < i.val

open Classical in
def lowSet (ρ : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => ∃ (l : Fin c) (i : Fin (c + 1)), e = (Sum.inr l, Sum.inr i) ∧ ρ < i.val ∧ i.val ≤ l.val

open Classical in
def upSet (ρ : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => ∃ (l : Fin c) (i : Fin (c + 1)), e = (Sum.inr l, Sum.inr i) ∧ l.val < i.val ∧ i.val ≤ ρ

def colIx (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) : ℕ := Sum.elim (fun _ => 0) (fun i => i.val) e.2

end Flat

end GlobalTheory.PartRed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialFourierInversion
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open scoped Topology

noncomputable section
namespace GlobalTheory.LocFlat.PartialFourier

theorem eventually_add_invariant {X : Type*} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]
    {f : X → ℂ} (hf : f ∈ SB X) : ∀ᶠ t in 𝓝 (0 : X), ∀ x, f (x + t) = f x := by
  have h1 : ∀ᶠ t in 𝓝 (0 : X), ∀ x ∈ tsupport f, f (x + t) = f x := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : X × X => (f (q.2 + q.1), f q.2) :=
      (hf.1.comp_continuous (by fun_prop)).prodMk (hf.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  have h1' : ∀ᶠ t in 𝓝 (0 : X), ∀ x ∈ tsupport f, f (x + -t) = f x :=
    (continuous_neg.tendsto' (0 : X) 0 neg_zero).eventually h1
  filter_upwards [h1, h1'] with t ht ht' x
  by_cases hx : x ∈ tsupport f
  · exact ht x hx
  by_cases hx' : x + t ∈ tsupport f
  · have := ht' _ hx'
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

omit [BorelSpace k] in
theorem partial_mem_SB {I J : Type} [Fintype I] [Fintype J] (ν : Measure k) {f : (I → k) × (J → k) → ℂ}
    (hf : f ∈ SB ((I → k) × (J → k))) :
    (fun x₁ : I → k => ∫ y : J → k, f (x₁, y) ∂(Measure.pi fun _ => ν)) ∈ SB (I → k) := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_, ?_⟩
  · have h2 : Filter.Tendsto (fun z : I → k => ((z - x, 0) : (I → k) × (J → k))) (𝓝 x) (𝓝 0) := by
      have : Continuous (fun z : I → k => ((z - x, 0) : (I → k) × (J → k))) := by fun_prop
      convert this.tendsto x using 2
      simp only [sub_self]
      rfl
    filter_upwards [h2.eventually (eventually_add_invariant hf)] with z hz
    congr 1
    funext y
    have := hz (x, y)
    simpa using this
  · refine HasCompactSupport.intro (hf.2.image continuous_fst) fun x hx => ?_
    have : ∀ y, f (x, y) = 0 := fun y => image_eq_zero_of_notMem_tsupport fun h => hx ⟨_, h, rfl⟩
    simp [this]

theorem partial_fourier_inversion : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (I : Type) [Fintype I], ∃ C : ℝ, 0 < C ∧ ∀ (J : Type) [Fintype J] (a : I → k), ∀ f ∈ SB ((I → k) × (J → k)), Integrable (fun l : I → k => ∫ x : (I → k) × (J → k), f x * (ψ (l ⬝ᵥ x.1) : ℂ) ∂((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν))) (Measure.pi fun _ => ν) ∧ ∫ l : I → k, (ψ (-(l ⬝ᵥ a)) : ℂ) * (∫ x : (I → k) × (J → k), f x * (ψ (l ⬝ᵥ x.1) : ℂ) ∂((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν))) ∂(Measure.pi fun _ => ν) = (C : ℂ) * ∫ y : J → k, f (a, y) ∂(Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ ψ ν hψ hne hν I _
  classical
  have := secondCountable k
  have := t2Space k
  obtain ⟨c, hc⟩ := (conductor_exists k).1 ψ hψ hne
  have hO : 0 < ν.real (𝒪[k] : Set k) :=
    ENNReal.toReal_pos ((isOpen_int k).measure_pos ν ⟨0, zero_mem _⟩).ne' (isCompact_int k).measure_lt_top.ne
  have hpsi : ∀ u : k, (ψ (-u) : ℂ) * ψ u = 1 := by
    intro u
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
  refine ⟨(nabs k c * ν.real (𝒪[k] : Set k) ^ 2) ^ Fintype.card I, by have := nabs_pos k c; positivity,
    fun J _ a f hf => ?_⟩
  set μI : Measure (I → k) := Measure.pi fun _ => ν with hμI
  set μJ : Measure (J → k) := Measure.pi fun _ => ν with hμJ
  set g : (I → k) → ℂ := fun x₁ => ∫ y, f (x₁, y) ∂μJ with hgdef
  have hg : g ∈ SB (I → k) := partial_mem_SB ν hf
  have hF : ∀ l : I → k, ∫ x, f x * (ψ (l ⬝ᵥ x.1) : ℂ) ∂(μI.prod μJ) = ∫ x₁, g x₁ * (ψ (x₁ ⬝ᵥ l) : ℂ) ∂μI := by
    intro l
    have hfi : Integrable f (μI.prod μJ) := hf.1.continuous.integrable_of_hasCompactSupport hf.2
    have hi : Integrable (fun x => f x * (ψ (l ⬝ᵥ x.1) : ℂ)) (μI.prod μJ) :=
      hfi.mul_bdd (c := 1)
        ((continuous_subtype_val.comp (hψ.comp (continuous_const.dotProduct continuous_fst))).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun q => (Circle.norm_coe _).le)
    rw [integral_prod _ hi]
    congr 1
    funext x
    simp only
    rw [integral_mul_const, dotProduct_comm l x]
  simp only [hF]
  refine ⟨?_, ?_⟩
  · have := FourierPi.fourier_mem_SB μI hc hg
    exact this.1.continuous.integrable_of_hasCompactSupport this.2
  · set h : (I → k) → ℂ := fun x => g (x + a) with hhdef
    have hh : h ∈ SB (I → k) :=
      ⟨hg.1.comp_continuous (continuous_add_const a), hg.2.comp_homeomorph (Homeomorph.addRight a)⟩
    have htr : ∀ l : I → k, (ψ (-(l ⬝ᵥ a)) : ℂ) * ∫ x₁, g x₁ * (ψ (x₁ ⬝ᵥ l) : ℂ) ∂μI =
        ∫ x, h x * (ψ (x ⬝ᵥ l) : ℂ) ∂μI := by
      intro l
      rw [← integral_const_mul, ← integral_add_right_eq_self _ a]
      congr 1
      funext x
      have e1 : (x + a) ⬝ᵥ l = x ⬝ᵥ l + l ⬝ᵥ a := by rw [add_dotProduct, dotProduct_comm a l]
      rw [hhdef, e1, AddChar.map_add_eq_mul, Circle.coe_mul]
      linear_combination (g (x + a) * (ψ (x ⬝ᵥ l) : ℂ)) * hpsi (l ⬝ᵥ a)
    simp only [htr]
    obtain ⟨s, hs⟩ := FourierPi.fourier_inversion_pi μI hc hh
    have hb : ∀ r : kˣ, μI.real (FourierPi.box I r) = ν.real (cball r) ^ Fintype.card I := by
      intro r
      simp [hμI, Measure.real, FourierPi.box, Measure.pi_pi]
    rw [hs, hb, hb, ← mul_pow, measureReal_cball, measureReal_cball]
    have h4 : nabs k c = nabs k s * nabs k (c * s⁻¹) := by
      rw [← nabs_mul, mul_comm, inv_mul_cancel_right]
    simp only [hhdef, zero_add, hgdef, h4]
    push_cast
    ring

end GlobalTheory.LocFlat.PartialFourier
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRead
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.FlatFactor

section Gen
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']

def fill (ev it : Finset (m × m')) (β t : Matrix m m' k) (a : {e : m × m' // e ∈ it} → k) : Matrix m m' k :=
  Matrix.of fun r q => if h : (r, q) ∈ it then a ⟨(r, q), h⟩ else if (r, q) ∈ ev then β r q else t r q

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

def red (ν : Measure k) (ev it : Finset (m × m')) (β : Matrix m m' k) (Θ : Matrix m m' k → ℂ) (t : Matrix m m' k) : ℂ :=
  ∫ a, Θ (fill ev it β t a) ∂(Measure.pi fun _ => ν)

def KerRed {M : Type} [AddCommGroup M] [Module ℂ M] (ν : Measure k) (ev it : Finset (m × m')) (β : Matrix m m' k)
    (l : SB (Matrix m m' k) →ₗ[ℂ] M) : Prop :=
  ∀ Θ : SB (Matrix m m' k), (∀ t, red ν ev it β Θ.1 t = 0) → l Θ = 0

end Gen

section Pos
variable (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ)

open Classical in
def evC : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e =>
    (∃ i, e.2 = Sum.inr i ∧ i.val < ρ ∧ ¬ Free (ρ + 1) e) ∨
    (∃ l, e.1 = Sum.inr l ∧ ρ ≤ l.val ∧ ∀ i, e.2 = Sum.inr i → i.val = ρ)

open Classical in
def itB : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => Free (ρ + 1) e ∧ ∀ i, e.2 = Sum.inr i → ρ ≤ i.val

def IsRead : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → Prop
  | (.inl _, .inl _) => True
  | (.inl _, .inr i) => i.val = ρ
  | (.inr _, _) => False

open Classical in
def evAll : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => ¬ Free (ρ + 1) e ∧ ¬ IsRead n n' c ρ e

open Classical in
def itFree : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => Free (ρ + 1) e

variable {n n' c}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def TwLaw {M : Type} [AddCommGroup M] [Module ℂ M] (ψ : AddChar k Circle)
    (l : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M) : Prop :=
  ∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → (∀ i j : Fin c, i.val < ρ → ρ ≤ j.val → u.val i j = 0) →
    ∀ Θ Θ' Θ'' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      (∀ t, Θ'.1 t = Θ.1 (((embA n u)⁻¹).val * t)) →
      (∀ t, Θ''.1 t = (ψ (ch ((embA n u).val * t) - ch t) : ℂ) * Θ.1 t) →
      l Θ' = (ψ (-simpleSum (embA n u)) : ℂ) • l Θ''

end Pos

end GlobalTheory.FlatFactor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelZeroUniformizerFrameUnipotentAndEmbedGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelZeroUniformizerFrameUnipotentAndEmbedGL
open ValuativeRel Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.LevZeroUp
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LevZeroGen GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

def scal (ϖ : kˣ) : XIx (Fin κ) t 0 ⊕ Fin (s + 1) → k := Sum.elim 1 fun i => (ϖ : k) ^ (i.val + 1)

def back : XIx (Fin κ) t 0 ⊕ Fin (s + 1) → Fin κ ⊕ Fin (s + 1) :=
  fun r => (ixZero (Fin κ ⊕ Fin (s + 1)) t).symm ((stdOrd (Fin κ) t 0 (s + 1) (Nat.zero_add _)).symm r)

theorem back_eps (i : Fin κ) : back (s := s) t (.inl (.inl (.inl i))) = .inl i := by
  unfold back
  rw [show (stdOrd (Fin κ) t 0 (s + 1) (Nat.zero_add _)).symm (.inl (.inl (.inl i))) = .inl (.inl i) from
    (Equiv.symm_apply_eq _).2 rfl]
  exact (Equiv.symm_apply_eq _).2 rfl

theorem levelZeroOldIndexOfNew_inr (i : Fin (s + 1)) : back (κ := κ) t (.inr i) = .inr i := by
  unfold back
  rw [show (stdOrd (Fin κ) t 0 (s + 1) (Nat.zero_add _)).symm (.inr i) = .inl (.inr i) from
    (Equiv.symm_apply_eq _).2 (standardOrderExtendedBasis_apply_low_block (Fin κ) t (l := s + 1) 0 (s + 1) (Nat.zero_add _) i).symm]
  exact (Equiv.symm_apply_eq _).2 rfl

theorem scal_ne_zero (ϖ : kˣ) (r : XIx (Fin κ) t 0 ⊕ Fin (s + 1)) : scal t ϖ r ≠ 0 := by
  rcases r with r | r <;> simp [scal]

theorem bas_val : ((S.T t).bas 0 (s + 1) (Nat.zero_add _)).val = diagonal (scal t S.ϖ) := by
  show (embA _ (SplitFlip.diagGL fun i : Fin (s + 1) => S.ϖ ^ (i.val + 1))).val = _
  simp only [embA, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk, SplitFlip.diagGL_val]
  rw [← diagonal_one, fromBlocks_diagonal]
  congr 1

theorem bas_inv_val : (((S.T t).bas 0 (s + 1) (Nat.zero_add _))⁻¹).val = diagonal fun r => (scal t S.ϖ r)⁻¹ := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [bas_val, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext r; exact mul_inv_cancel₀ (scal_ne_zero t S.ϖ r)

theorem upZero_entry (x : GL (Fin κ ⊕ Fin (s + 1)) k) (r c : XIx (Fin κ) t 0 ⊕ Fin (s + 1)) :
    (upZero S t x).val r c = scal t S.ϖ r * x.val (back t r) (back t c) * (scal t S.ϖ c)⁻¹ := by
  rw [upZero_apply, Units.val_mul, Units.val_mul, bas_val, bas_inv_val, mul_diagonal, diagonal_mul, reGL_val, reGL_val]
  rfl

theorem xZero_symm (i : Fin κ) : (xZero (Fin κ) t).symm (.inl (.inl i)) = i := (Equiv.symm_apply_eq _).2 rfl

theorem upZero_mem_N {n : GL (Fin κ ⊕ Fin (s + 1)) k} (hn : n ∈ N k (Fin κ) (s + 1) (S.ρ + 1)) :
    upZero S t n ∈ N k (XIx (Fin κ) t 0) (s + 1) (S.ρ + 1) := by
  rw [Model.mem_N_iff] at hn ⊢
  intro r c h
  rw [upZero_entry]
  rcases r with ((r | r) | ⟨r, _⟩) | r
  · rcases c with ((c | c) | ⟨c, _⟩) | c
    · rw [back_eps, back_eps, hn _ _ (by simp [lev])]
      by_cases e : r = c
      · subst e; simp [scal]
      · simp [scal, Matrix.one_apply, e]
    · exact c.elim0
    · exact c.elim0
    · rw [back_eps, levelZeroOldIndexOfNew_inr, hn _ _ (by simpa [lev] using h)]
      simp [Matrix.one_apply]
  · exact r.elim0
  · exact r.elim0
  · rcases c with ((c | c) | ⟨c, _⟩) | c
    · rw [back_eps, levelZeroOldIndexOfNew_inr, hn _ _ (by simpa [lev] using h)]
      simp [Matrix.one_apply]
    · exact c.elim0
    · exact c.elim0
    · rw [levelZeroOldIndexOfNew_inr, levelZeroOldIndexOfNew_inr, hn _ _ (by simpa [lev] using h)]
      by_cases e : r = c
      · subst e; simp [scal, Matrix.one_apply]
      · simp [Matrix.one_apply, e]

theorem simpleSum_upZero (n : GL (Fin κ ⊕ Fin (s + 1)) k) :
    simpleSum (upZero S t n) = ((S.ϖ⁻¹ : kˣ) : k) * simpleSum n := by
  have hϖ : (S.ϖ : k) ≠ 0 := S.ϖ.ne_zero
  unfold simpleSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [upZero_entry, levelZeroOldIndexOfNew_inr, levelZeroOldIndexOfNew_inr]
    simp only [scal, Sum.elim_inr, h, Units.val_inv_eq_inv_val]
    field_simp
    ring
  · simp

theorem superSum_one : superSum Fin.val (1 : Matrix (Fin κ) (Fin κ) k) = 0 := by
  unfold superSum
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · have : i ≠ j := by rintro rfl; omega
    simp [Matrix.one_apply, this]
  · rfl

theorem lam_eq (n : S.P.J) (hn : n.1 ∈ N k (Fin κ) (s + 1) (S.ρ + 1)) :
    ((S.P.lam n : ℂˣ) : ℂ) = (S.ψ (simpleSum (upZero S t n.1)) : ℂ) := by
  rw [S.sym.2 n, simpleSum_upZero]
  have h11 : (n : GL (Fin κ ⊕ Fin (s + 1)) k).val.toBlocks₁₁ = 1 := by
    rw [Model.mem_N_iff] at hn
    ext i j
    simpa [toBlocks₁₁, Matrix.one_apply] using hn (.inl i) (.inl j) (by simp [lev])
  rw [h11, superSum_one]
  simp

theorem upZero_embX (γ : GL (Fin κ) k) :
    upZero S t (embX (s + 1) γ) = embX (s + 1) (reGL (xZero (Fin κ) t) γ) := by
  ext r c
  rw [upZero_entry]
  rcases r with ((r | r) | ⟨r, _⟩) | r
  · rcases c with ((c | c) | ⟨c, _⟩) | c
    · rw [back_eps, back_eps]
      simp [embX, scal, reGL_val, xZero_symm]
    · exact c.elim0
    · exact c.elim0
    · rw [back_eps, levelZeroOldIndexOfNew_inr]
      simp [embX]
  · exact r.elim0
  · exact r.elim0
  · rcases c with ((c | c) | ⟨c, _⟩) | c
    · rw [levelZeroOldIndexOfNew_inr, back_eps]
      simp [embX]
    · exact c.elim0
    · exact c.elim0
    · rw [levelZeroOldIndexOfNew_inr, levelZeroOldIndexOfNew_inr]
      by_cases e : r = c
      · subst e; simp [embX, scal, Matrix.one_apply]
      · simp [embX, Matrix.one_apply, e]

theorem upZero_N_embX : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], (∀ n : S.P.J, n.1 ∈ GlobalTheory.RootEx.N k (Fin κ) (s + 1) (S.ρ + 1) → GlobalTheory.LevZeroGen.upZero S t n.1 ∈ GlobalTheory.RootEx.N k (GlobalTheory.StepData.XIx (Fin κ) t 0) (s + 1) (S.ρ + 1) ∧ ((S.P.lam n : ℂˣ) : ℂ) = (S.ψ (GlobalTheory.RootEx.simpleSum (GlobalTheory.LevZeroGen.upZero S t n.1)) : ℂ)) ∧ ∀ γ : GL (Fin κ) k, GlobalTheory.LevZeroGen.upZero S t (GlobalTheory.RootEx.embX (s + 1) γ) = GlobalTheory.RootEx.embX (s + 1) (GlobalTheory.StepData.reGL (GlobalTheory.LevZeroGen.xZero (Fin κ) t) γ) := by
  intro k _ _ _ _ s κ S t _ _
  exact ⟨fun n hn => ⟨upZero_mem_N S t hn, lam_eq S t n hn⟩, upZero_embX S t⟩

end GlobalTheory.LevZeroUp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelZeroUniformizerFrameUnipotentAndEmbedGLStatement
open ValuativeRel Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelZeroUniformizerFrame_unipotent_and_embedGL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], (∀ n : S.P.J, n.1 ∈ GlobalTheory.RootEx.N k (Fin κ) (s + 1) (S.ρ + 1) → GlobalTheory.LevZeroGen.upZero S t n.1 ∈ GlobalTheory.RootEx.N k (GlobalTheory.StepData.XIx (Fin κ) t 0) (s + 1) (S.ρ + 1) ∧ ((S.P.lam n : ℂˣ) : ℂ) = (S.ψ (GlobalTheory.RootEx.simpleSum (GlobalTheory.LevZeroGen.upZero S t n.1)) : ℂ)) ∧ ∀ γ : GL (Fin κ) k, GlobalTheory.LevZeroGen.upZero S t (GlobalTheory.RootEx.embX (s + 1) γ) = GlobalTheory.RootEx.embX (s + 1) (GlobalTheory.StepData.reGL (GlobalTheory.LevZeroGen.xZero (Fin κ) t) γ) := by
  first | exact @GlobalTheory.LevZeroUp.upZero_N_embX | exact GlobalTheory.LevZeroUp.upZero_N_embX | (intros; apply GlobalTheory.LevZeroUp.upZero_N_embX <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatRowMapEqRootExchangeOperatorTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatRowMapEqRootExchangeOperatorTranslate
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.LocFlat

open GlobalTheory.RootEx.Exchange in
theorem flRow_eq_opE_rowE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ x : Matrix (n ⊕ Unit) n' k, GlobalTheory.LocFlat.flRow ψ ν p Φ x = opE ψ ν p (fun z => Φ (z * (rowE (c + 1) p (x (Sum.inr ()))).val)) x.toRows₁ := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c p hp hpc Φ hΦ x
  have := hν
  obtain ⟨q, rfl⟩ : ∃ q : Fin c, p = q.val + 1 := ⟨⟨p - 1, by omega⟩, by simp only; omega⟩
  have h := opE_rowE hψ ν 1 q (χ := fun _ => (1 : ℂ)) continuous_const hΦ.1.continuous x.toRows₁
    (x (Sum.inr ()))
  refine Eq.trans ?_ (h.symm.trans ?_)
  swap
  · rw [one_mul]
    congr 1
    funext z
    exact om_rowE _ _ _ _ _
  unfold flRow opE
  congr 1
  funext e
  have key : affPt (q.val + 1) x.toRows₁ e + rowAt n c (q.val + 1) (x (Sum.inr ())) =
      mat x.toRows₁ (ext0 (Free (q.val + 1)) e + gRow q (x (Sum.inr ()))) := by
    rw [affPt_eq]
    ext r s
    rcases r with r | r <;> rcases s with s | s <;>
      simp [mat, rowAt, gRow, Fin.val_inj, add_assoc]
  have hch : ch (mat x.toRows₁ (ext0 (Free (q.val + 1)) e + gRow q (x (Sum.inr ())))) =
      ch (affPt (q.val + 1) x.toRows₁ e) := by
    rw [affPt_eq]
    unfold ch
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mat, gRow]
  simp only [big]
  rw [key, hch, one_mul]

end GlobalTheory.LocFlat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatRowMapEqRootExchangeOperatorTranslateStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatRowMap_eq_rootExchangeOperator_translate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ x : Matrix (n ⊕ Unit) n' k, GlobalTheory.LocFlat.flRow ψ ν p Φ x = opE ψ ν p (fun z => Φ (z * (rowE (c + 1) p (x (Sum.inr ()))).val)) x.toRows₁ := by
  first | exact @GlobalTheory.LocFlat.flRow_eq_opE_rowE | exact GlobalTheory.LocFlat.flRow_eq_opE_rowE | (intros; apply GlobalTheory.LocFlat.flRow_eq_opE_rowE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatColumnMapEqRootExchangeOperatorTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatColumnMapEqRootExchangeOperatorTranslate
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.LocFlat.ColTranslate
open GlobalTheory.RootEx.Exchange GlobalTheory.LocFlat

theorem colE_neg_inv {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (y : n → k) :
    ((colE c p (-y))⁻¹ : GL (n ⊕ Fin c) k).val = (colE c p y).val := by
  ext r s
  rcases r with r | r <;> rcases s with s | s <;>
    simp [colE, upU, -Matrix.coe_units_inv, Units.inv_mk, neg_ite]

theorem affPt_add_colAt {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {c : ℕ} (q : Fin c) (y : n → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    affPt (q.val + 1) x₀ e + colAt n' c (q.val + 1) y = mat x₀ (ext0 (Free (q.val + 1)) e + gCol q y) := by
  classical
  ext r s
  rcases r with r | r <;> rcases s with s | s
  · simp [affPt_eq, mat, ext0, colAt, gCol, Free]
  · by_cases h : s = q.castSucc
    · subst h; simp [affPt_eq, mat, ext0, colAt, gCol, Free]
    · have h' : ¬ s.val = q.val := fun hh => h (Fin.ext (by simpa using hh))
      simp [affPt_eq, mat, ext0, colAt, gCol, h, h']
  · simp [affPt_eq, mat, ext0, colAt, gCol]
  · simp [affPt_eq, mat, ext0, colAt, gCol]

theorem ch_add_colAt {k : Type} [Field k] {n n' : Type} {c : ℕ} (p : ℕ) (y : n → k)
    (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : ch (z + colAt n' c p y) = ch z := by
  simp [ch, colAt]

end GlobalTheory.LocFlat.ColTranslate

namespace GlobalTheory.LocFlat
open GlobalTheory.RootEx.Exchange GlobalTheory.LocFlat.ColTranslate

theorem flCol_eq_opE_colE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ x : Matrix n (n' ⊕ Unit) k, GlobalTheory.LocFlat.flCol ψ ν p Φ x = opE ψ ν p (fun z => Φ ((colE c p fun r => x r (Sum.inr ())).val * z)) x.toCols₁ := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c p hp1 hpc Φ hΦ x
  obtain ⟨q, rfl⟩ : ∃ q : Fin c, p = q.val + 1 := ⟨⟨p - 1, by omega⟩, by simp; omega⟩
  have hcont : Continuous Φ := hΦ.1.continuous
  have h1 := opE_colE hψ ν 1 q q (χ := fun _ => (1 : ℂ)) continuous_const hcont x.toCols₁
    (-fun r => x r (Sum.inr ()))
  simp only [om_colE, colE_neg_inv, one_mul, neg_neg] at h1
  refine Eq.trans ?_ h1.symm
  rw [flCol]
  unfold opE
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  simp only
  rw [← affPt_add_colAt, big, ch_add_colAt, one_mul]

end GlobalTheory.LocFlat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatColumnMapEqRootExchangeOperatorTranslateStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatColumnMap_eq_rootExchangeOperator_translate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ x : Matrix n (n' ⊕ Unit) k, GlobalTheory.LocFlat.flCol ψ ν p Φ x = opE ψ ν p (fun z => Φ ((colE c p fun r => x r (Sum.inr ())).val * z)) x.toCols₁ := by
  first | exact @GlobalTheory.LocFlat.flCol_eq_opE_colE | exact GlobalTheory.LocFlat.flCol_eq_opE_colE | (intros; apply GlobalTheory.LocFlat.flCol_eq_opE_colE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumHeckeSeriesSphericalIntegralInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumHeckeSeriesSphericalIntegralInverse
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

noncomputable section

namespace GlobalTheory.HeckeDual

open GlobalTheory.SatakeFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private lemma isBorelSph_comp_invRevT {γ : Fin n → ℂ}
    {φ : GL (Fin n) k → ℂ} (hφ : _root_.GlobalTheory.SatakeBound.IsBorelSph k γ φ) :
    _root_.GlobalTheory.SatakeBound.IsBorelSph k (fun i => (γ i.rev)⁻¹)
      (fun g => φ (_root_.GlobalTheory.SatakeFlip.invRevT g)) := by
  obtain ⟨hK, hB⟩ := hφ
  refine ⟨fun g x hx => ?_, fun b hb t ht => ?_⟩
  · show φ (_root_.GlobalTheory.SatakeFlip.invRevT (g * x)) = φ (_root_.GlobalTheory.SatakeFlip.invRevT g)
    rw [map_mul]
    exact hK _ _ (_root_.GlobalTheory.SatakeFlip.invRevT_mem_KO hx)
  · have hb' := _root_.GlobalTheory.SatakeFlip.invRevT_mem_borel hb
    show φ (_root_.GlobalTheory.SatakeFlip.invRevT b) = _
    rw [hB _ hb' (fun i => (t i.rev)⁻¹) ?_]
    · refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
      simp [_root_.GlobalTheory.SatakeFlip.ord_inv_eq_neg, zpow_neg, inv_zpow]
    · intro i
      rw [_root_.GlobalTheory.SatakeFlip.invRevT_apply]
      have hi := _root_.GlobalTheory.SatakeFlip.inv_diag_mul hb i.rev
      rw [ht] at hi
      rw [Units.val_inv_eq_inv_val]
      exact eq_inv_of_mul_eq_one_left hi

private lemma exists_cosetMap_out_eq_invRevT_mul
    (c : GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n)) :
    ∃ x ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin n),
      (_root_.GlobalTheory.SatakeFlip.cosetMap c).out = _root_.GlobalTheory.SatakeFlip.invRevT c.out * x := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_out_eq_mul (_root_.GlobalTheory.SplitWeil.KO k (Fin n))
    (_root_.GlobalTheory.SatakeFlip.invRevT c.out)
  refine ⟨x, x.2, ?_⟩
  rw [← hx, ← _root_.GlobalTheory.SatakeFlip.cosetMap_mk, QuotientGroup.out_eq']

private lemma mul_entries_integral {g h : GL (Fin n) k}
    (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k])
    (hh : ∀ i j, (h : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k]) :
    ∀ i j, ((g * h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
  intro i j
  rw [Units.val_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hg i l) (hh l j)

private lemma invRevT_entries_integral_iff_inv (g : GL (Fin n) k) :
    (∀ i j, ((_root_.GlobalTheory.SatakeFlip.invRevT g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈
      𝒪[k]) ↔ ∀ i j, ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
  simp only [_root_.GlobalTheory.SatakeFlip.invRevT_apply]
  constructor
  · intro h i j
    simpa using h j.rev i.rev
  · intro h i j
    exact h _ _

private lemma det_invRevT' (g : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.SatakeFlip.invRevT g) =
      (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  rw [← map_inv]
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det ((↑g⁻¹ : Matrix (Fin n) (Fin n) k).transpose.submatrix Fin.rev Fin.rev) = _
  exact (Matrix.det_submatrix_equiv_self Fin.revPerm _).trans (Matrix.det_transpose _)

private lemma ord_det_eq_zero_of_mem_KO {x : GL (Fin n) k}
    (hx : x ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin n)) :
    _root_.GlobalTheory.SmGL.ord k (Matrix.GeneralLinearGroup.det x) = 0 := by
  have h := _root_.GlobalTheory.GLDoubling.nabs_det_of_mem_KO hx
  rw [_root_.GlobalTheory.LGrp.nabs_eq_zpow] at h
  have hq : (1 : ℝ) < _root_.GlobalTheory.SplitWeil.resCard k := by
    exact_mod_cast _root_.GlobalTheory.SplitWeil.one_lt_resCard k
  have := zpow_right_injective₀ (by positivity) hq.ne' (h.trans (zpow_zero _).symm)
  simpa using this

theorem _root_.GlobalTheory.HeckeDual.hasSum_dual : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ)
    (φ : GL (Fin n) k → ℂ), _root_.GlobalTheory.SatakeBound.IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ X : ℂ,
    (∀ i : Fin n, ‖(_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X‖ < 1) →
    HasSum (fun c : {c : GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n) //
        (∀ i j, (c.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k])} =>
      X ^ (-_root_.GlobalTheory.SmGL.ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat *
        φ c.1.out)
      (∏ i : Fin n, (1 - (_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹) := by
  intro k _ _ _ _ n γ φ hφ _ X hX
  have hrev : ∀ i : Fin n, (i.rev : ℕ) = n - 1 - i := fun i => by rw [Fin.val_rev]; omega
  have hX' : ∀ i : Fin n,
      ‖(_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * (γ i.rev)⁻¹ * X‖ < 1 := by
    intro i
    have hi := hX i.rev
    rwa [hrev] at hi
  have H := _root_.GlobalTheory.HeckeSeries.hasSum_integral_cosets k n _ _
    (isBorelSph_comp_invRevT hφ) X hX'
  have hprod : ∏ i : Fin n, (1 - (_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (n - 1 - (i : ℕ)) *
      (γ i.rev)⁻¹ * X)⁻¹ =
      ∏ i : Fin n, (1 - (_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹ :=
    Fintype.prod_equiv Fin.revPerm _ _ fun i => by rw [Fin.revPerm_apply, hrev]
  rw [hprod] at H
  let e : {c : GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n) //
        (∀ i j, (c.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k])} ≃
      {c : GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n) //
        (∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k])} :=
    { toFun := fun c => ⟨_root_.GlobalTheory.SatakeFlip.cosetMap c.1, by
        obtain ⟨x, hx, hc⟩ := exists_cosetMap_out_eq_invRevT_mul c.1
        rw [hc]
        exact mul_entries_integral
          ((invRevT_entries_integral_iff_inv _).mpr c.2)
          ((_root_.GlobalTheory.SplitFlip.mem_KO_iff x).mp hx).1⟩
      invFun := fun c => ⟨_root_.GlobalTheory.SatakeFlip.cosetMap c.1, by
        obtain ⟨x, hx, hc⟩ := exists_cosetMap_out_eq_invRevT_mul c.1
        rw [hc, mul_inv_rev, ← map_inv]
        refine mul_entries_integral ((_root_.GlobalTheory.SplitFlip.mem_KO_iff x).mp hx).2 ?_
        refine (invRevT_entries_integral_iff_inv _).mpr ?_
        simpa using c.2⟩
      left_inv := fun c => Subtype.ext (_root_.GlobalTheory.SatakeFlip.cosetMap_cosetMap c.1)
      right_inv := fun c => Subtype.ext (_root_.GlobalTheory.SatakeFlip.cosetMap_cosetMap c.1) }
  convert e.hasSum_iff.mpr H using 1
  funext c
  obtain ⟨x, hx, hc⟩ := exists_cosetMap_out_eq_invRevT_mul c.1
  show _ = X ^ (_root_.GlobalTheory.SmGL.ord k (Matrix.GeneralLinearGroup.det
      (_root_.GlobalTheory.SatakeFlip.cosetMap c.1).out)).toNat *
    φ (_root_.GlobalTheory.SatakeFlip.invRevT (_root_.GlobalTheory.SatakeFlip.cosetMap c.1).out)
  rw [hc, map_mul _root_.GlobalTheory.SatakeFlip.invRevT, _root_.GlobalTheory.SatakeFlip.invRevT_invRevT,
    hφ.1 _ _ (_root_.GlobalTheory.SatakeFlip.invRevT_mem_KO hx), map_mul,
    _root_.GlobalTheory.SmGL.ord_mul, det_invRevT', _root_.GlobalTheory.SatakeFlip.ord_inv_eq_neg,
    ord_det_eq_zero_of_mem_KO hx, add_zero]

end GlobalTheory.HeckeDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumHeckeSeriesSphericalIntegralInverseStatement
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_hecke_series_spherical_integral_inverse : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ X : ℂ, (∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X‖ < 1) → HasSum (fun c : {c : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (c.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k])} => X ^ (-ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ c.1.out) (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹) := by
  first | exact @GlobalTheory.HeckeDual.hasSum_dual | exact GlobalTheory.HeckeDual.hasSum_dual | (intros; apply GlobalTheory.HeckeDual.hasSum_dual <;> assumption)
end
end

module

public import Development.AutomorphicArithmetic.IntegralCasts.RegAlgFam
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.AwayLiftCompFromZeroRingHom

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
noncomputable section

open Topology

namespace GlobalTheory.CuspRep

variable {G : Type} [Group G]

theorem isIrreducible_iff {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) :
    ρ.IsIrreducible ↔ Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  constructor
  · intro h
    refine ⟨?_, fun W hW => ?_⟩
    · have : (⊥ : Submodule ℂ V) ≠ ⊤ := fun e =>
        bot_ne_top (α := Subrepresentation ρ) (Subrepresentation.toSubmodule_injective e)
      exact (Submodule.nontrivial_iff ℂ).1 ⟨⟨_, _, this⟩⟩
    · exact (eq_bot_or_eq_top (⟨W, hW⟩ : Subrepresentation ρ)).imp (congrArg Subrepresentation.toSubmodule)
        (congrArg Subrepresentation.toSubmodule)
  · rintro ⟨h0, h⟩
    have : Nontrivial (Subrepresentation ρ) :=
      ⟨⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e : (⊥ : Submodule ℂ V) = ⊤)⟩⟩
    exact ⟨fun W => (h W.toSubmodule W.apply_mem_toSubmodule).imp
      (fun e => Subrepresentation.toSubmodule_injective e) (fun e => Subrepresentation.toSubmodule_injective e)⟩

@[simp] theorem twRep_apply {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (χ : G →* ℂˣ)
    (g : G) (v : V) : twRep ρ χ g v = ((χ g : ℂˣ) : ℂ) • ρ g v := rfl

variable [TopologicalSpace G]


variable (G) in
structure SmIrr (G : Type) [Group G] [TopologicalSpace G] where

  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]

  ρ : Representation ℂ G V
  smooth : GlobalTheory.PRep.IsSmooth ρ
  irred : ρ.IsIrreducible

attribute [instance] SmIrr.acg SmIrr.mod


variable (G) in
instance SmIrr.setoid : Setoid (SmIrr G) where
  r σ σ' := Nonempty (σ.ρ.Equiv σ'.ρ)
  iseqv := ⟨fun σ => ⟨.refl σ.ρ⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩


variable (G) in
def Irr (G : Type) [Group G] [TopologicalSpace G] : Type 1 := Quotient (@SmIrr.setoid G _ _)


variable (G) in
def SmIrr.triv : SmIrr G where
  V := ℂ
  ρ := Representation.trivial ℂ G ℂ
  smooth v := by simp
  irred := (isIrreducible_iff _).2 ⟨inferInstance, fun W _ => eq_bot_or_eq_top W⟩

instance : Inhabited (Irr G) := ⟨Quotient.mk (@SmIrr.setoid G _ _) (SmIrr.triv G)⟩

variable [IsTopologicalGroup G]

def SmIrr.twist (σ : SmIrr G) (χ : G →* ℂˣ) (hχ : IsOpen {g | χ g = 1}) : SmIrr G where
  V := σ.V
  ρ := twRep σ.ρ χ
  smooth v := isOpen_stab_of_mem_nhds _ v <| Filter.mem_of_superset
    (((σ.smooth v).inter hχ).mem_nhds ⟨by simp, by simp⟩) fun g hg => by
      have h1 : σ.ρ g v = v := hg.1
      have h2 : χ g = 1 := hg.2
      simp [h1, h2]
  irred := by
    obtain ⟨h0, h⟩ := (isIrreducible_iff _).1 σ.irred
    refine (isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g v hv => ?_⟩
    exact (W.smul_mem_iff (Units.ne_zero (χ g))).1 (hW g v hv)

def Irr.twist (σ : Irr G) (χ : G →* ℂˣ) (hχ : IsOpen {g | χ g = 1}) : Irr G :=
  Quotient.map (sa := @SmIrr.setoid G _ _) (sb := @SmIrr.setoid G _ _) (fun σ : SmIrr G => σ.twist χ hχ) (fun σ σ' ⟨e⟩ => ⟨.mk e.toLinearEquiv fun g => by
    ext v
    change e (((χ g : ℂˣ) : ℂ) • σ.ρ g v) = ((χ g : ℂˣ) : ℂ) • σ'.ρ g (e v)
    rw [map_smul]
    exact congrArg _ (LinearMap.congr_fun (e.isIntertwining' g) v)⟩) σ

def Irr.ofChar (χ : G →* ℂˣ) (hχ : IsOpen {g | χ g = 1}) : Irr G :=
  Quotient.mk (@SmIrr.setoid G _ _) ((SmIrr.triv G).twist χ hχ)

end GlobalTheory.CuspRep
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff
set_option autoImplicit false

noncomputable section

open Module TopologicalSpace

namespace GlobalTheory.FlagPts

variable (k : Type) [Field k] {ι : Type} (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

def Frames : Type := ∀ i, Basis (Fin (finrank k (V i))) k (V i)

def regFns : Subalgebra k (Frames k V → k) :=
  Algebra.adjoin k ({f | ∃ (i : ι) (φ : Dual k (V i)) (a : Fin (finrank k (V i))), f = fun b => φ (b i a)} ∪
    {f | ∃ (i : ι) (v : V i) (a : Fin (finrank k (V i))), f = fun b => (b i).repr v a})

instance instTopFrames : TopologicalSpace (Frames k V) := .generateFrom {s | ∃ f ∈ regFns k V, s = {b | f b ≠ 0}}

def Flags : Type := ∀ i, FullFlag (R := k) (M := V i) (finrank k (V i))

variable {k V}

def Frames.flags (b : Frames k V) : Flags k V := fun i => FullFlag.ofBasis (b i)

theorem flags_surjective : Function.Surjective (Frames.flags (k := k) (V := V)) := fun F => by
  choose b hb using fun i => (F i).exists_isAdapted_of_isLocalRing
  exact ⟨b, funext fun i => FullFlag.isAdapted_iff.1 (hb i)⟩

instance : TopologicalSpace (Flags k V) := .coinduced Frames.flags inferInstance

instance [∀ i, FiniteDimensional k (V i)] : Nonempty (Flags k V) := ⟨Frames.flags fun i => finBasis k (V i)⟩

theorem isClosed_zero {f : Frames k V → k} (hf : f ∈ regFns k V) : IsClosed {b | f b = 0} :=
  isOpen_compl_iff.1 (isOpen_generateFrom_of_mem ⟨f, hf, rfl⟩)

theorem isClosed_flags_iff {s : Set (Flags k V)} : IsClosed s ↔ IsClosed (Frames.flags ⁻¹' s) := isClosed_coinduced

def Flags.step (F : Flags k V) (i : ι) (n : ℕ) : Submodule k (V i) :=
  (F i).sub ⟨min n (finrank k (V i)), Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem mem_step_flags {b : Frames k V} {i : ι} {n : ℕ} {v : V i} :
    v ∈ b.flags.step i n ↔ ∀ a : Fin (finrank k (V i)), n ≤ (a : ℕ) → (b i).repr v a = 0 := by
  refine (mem_basis_flag_iff _ _ _).trans (forall_congr' fun a => imp_congr_left ?_)
  have := a.2
  rw [Fin.le_def, Fin.val_castSucc]
  simp only
  omega

theorem step_flags_le {b : Frames k V} {i : ι} {n : ℕ} {P : Submodule k (V i)} :
    b.flags.step i n ≤ P ↔ ∀ a : Fin (finrank k (V i)), (a : ℕ) < n → b i a ∈ P := by
  refine ((b i).flag_le_iff).trans (forall_congr' fun a => imp_congr_left ?_)
  have := a.2
  rw [Fin.lt_def, Fin.val_castSucc]
  simp only
  omega

theorem finrank_step (F : Flags k V) (i : ι) (n : ℕ) : finrank k (F.step i n) = min n (finrank k (V i)) := by
  obtain ⟨b, rfl⟩ := flags_surjective F
  change finrank k (Submodule.span k (b i '' _)) = _
  rw [Set.image_eq_range]
  refine (finrank_span_eq_card ((b i).linearIndependent.comp _ Subtype.val_injective)).trans ?_
  rw [Fintype.card_subtype]
  simp only [Set.mem_setOf_eq, Fin.lt_def, Fin.val_castSucc, Fin.card_filter_val_lt]
  omega

def between (n : ℕ) (A B : ∀ i, Submodule k (V i)) : Closeds (Flags k V) where
  carrier := {F | ∀ i, A i ≤ F.step i n ∧ F.step i n ≤ B i}
  isClosed' := by
    refine isClosed_flags_iff.2 ?_
    change IsClosed {b : Frames k V | ∀ i, A i ≤ b.flags.step i n ∧ b.flags.step i n ≤ B i}
    simp only [Set.setOf_forall, Set.setOf_and]
    refine isClosed_iInter fun i => IsClosed.inter (X := Frames k V) ?_ ?_
    · simp only [SetLike.le_def, mem_step_flags, Set.setOf_forall]
      exact isClosed_iInter fun v => isClosed_iInter fun _ => isClosed_iInter fun a => isClosed_iInter fun _ =>
        isClosed_zero (Algebra.subset_adjoin (.inr ⟨i, v, a, rfl⟩))
    · have e (v : V i) : v ∈ B i ↔ ∀ φ ∈ (B i).dualAnnihilator, φ v = 0 := by
        rw [← Submodule.mem_dualCoannihilator, Subspace.dualAnnihilator_dualCoannihilator_eq]
      simp only [step_flags_le, e, Set.setOf_forall]
      exact isClosed_iInter fun a => isClosed_iInter fun _ => isClosed_iInter fun φ => isClosed_iInter fun _ =>
        isClosed_zero (Algebra.subset_adjoin (.inl ⟨i, φ, a, rfl⟩))

def dim (s : Closeds (Flags k V)) : ℕ := ((topologicalKrullDim (s : Set (Flags k V))).unbotD 0).toNat

end GlobalTheory.FlagPts
end
end

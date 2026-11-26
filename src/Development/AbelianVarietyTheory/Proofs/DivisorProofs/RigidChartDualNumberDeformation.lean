module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiHomogeneousRenameCastLE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDatumLiftDatumSameHalfTranslateConjugatePlac

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidChartDualNumberDeformation
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KSUniq

variable {K : Type} [Field K]

theorem theta_eq_fibre (P₀ : Out.PolAV (Sp K)) {n : ℕ} (u : Fin n → (epsR K ⟶ P₀.A)) (hu : IsLieBasis u)
    (dd : Fin n → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)) (hdd : ∀ a, IsInvDer (u a) (dd a))
    {X Z : Scheme.{0}} (π : Z ⟶ X) (x0 : Sp K ⟶ X) (m : P₀.A.left ⟶ Z) (hm : IsPullback m P₀.A.hom π x0)
    {U : X.Opens} (hU : IsAffineOpen U) (L : LB Z) (hL : L.IsLB) (hiso : LBIso P₀.L (L.pull m))
    (D : Γ(X, U) → Γ(X, U)) (θ θ' : Matrix (Fin n) (Fin n) K)
    {J J' : Type} (W : J → Z.Opens) (W' : J' → Z.Opens) (j : J → L.ι) (j' : J' → L.ι)
    (d : J → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)) (d' : J' → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O))
    (hWU : ∀ i, W i ≤ π ⁻¹ᵁ U) (hWU' : ∀ k, W' k ≤ π ⁻¹ᵁ U)
    (hWj : ∀ i, W i ≤ L.U (j i)) (hWj' : ∀ k, W' k ≤ L.U (j' k))
    (hcov : ∀ z : P₀.A.left, ∃ i, m z ∈ W i) (hcov' : ∀ z : P₀.A.left, ∃ k, m z ∈ W' k)
    (hf : ∀ i, GlobalTheory.LogKS.IsField (W i) (d i)) (hf' : ∀ k, GlobalTheory.LogKS.IsField (W' k) (d' k))
    (hl : ∀ i (h : W i ≤ π ⁻¹ᵁ U) (r : Γ(X, U)),
      d i (W i) ((π.appLE U (W i) h).hom r) = (π.appLE U (W i) h).hom (D r))
    (hl' : ∀ k (h : W' k ≤ π ⁻¹ᵁ U) (r : Γ(X, U)),
      d' k (W' k) ((π.appLE U (W' k) h).hom r) = (π.appLE U (W' k) h).hom (D r))
    (φ : Fin n → C1 (fun i => m ⁻¹ᵁ L.U i)) (hφ : IsDlog m L dd φ)
    (hP : ∀ i i' (O : Z.Opens), O ≤ W i ⊓ W i' → ∀ f, (m.app O).hom (d i O f - d i' O f) =
      ∑ a, (∑ b, constFn P₀.A.hom _ (θ a b) * rsT (φ b (j i) (j i')) (m ⁻¹ᵁ O)) * dd a _ ((m.app O).hom f))
    (hP' : ∀ k k' (O : Z.Opens), O ≤ W' k ⊓ W' k' → ∀ f, (m.app O).hom (d' k O f - d' k' O f) =
      ∑ a, (∑ b, constFn P₀.A.hom _ (θ' a b) * rsT (φ b (j' k) (j' k')) (m ⁻¹ᵁ O)) * dd a _ ((m.app O).hom f)) :
    θ = θ' := by
  have hs : Smooth P₀.A.hom := P₀.isAb.smooth
  obtain ⟨-, hind⟩ := GlobalTheory.KS.DlogPol.dlog_independent K P₀ n u dd hu hdd Z m L hL hiso
  obtain ⟨hcoc, hcob⟩ := hind φ hφ
  let Wp : J × J' → Z.Opens := fun p => W p.1 ⊓ W' p.2
  have hWpU : ∀ p, Wp p ≤ π ⁻¹ᵁ U := fun p => inf_le_left.trans (hWU p.1)
  have bse := fun i => field_base π (W i) (hWU i) (d i) (hf i) D (hl i)
  have bse' := fun k => field_base π (W' k) (hWU' k) (d' k) (hf' k) D (hl' k)
  have ex : ∀ p : J × J', ∃ h : Fin n → Γ(P₀.A.left, m ⁻¹ᵁ Wp p), ∀ W₁, W₁ ≤ Wp p → ∀ f,
      (m.app W₁).hom (d p.1 W₁ f - d' p.2 W₁ f) = ∑ a, rsT (h a) _ * dd a (m ⁻¹ᵁ W₁) ((m.app W₁).hom f) := by
    intro p
    refine (coeff_id hs hu hdd x0 π m hm hU (Wp p) (hWpU p)
      (fun W₁ f => (m.app W₁).hom (d p.1 W₁ f - d' p.2 W₁ f))
      (fun W₁ h f f' => ?_) (fun W₁ h f f' => ?_) (fun W₁ W₂ h h₀ f => ?_) (fun W₁ h r => ?_)).exists
    · rw [(hf p.1).1 W₁ (h.trans inf_le_left), (hf' p.2).1 W₁ (h.trans inf_le_right)]
      simp only [map_sub, map_add (f := _)]; ring
    · rw [(hf p.1).2.1 W₁ (h.trans inf_le_left), (hf' p.2).2.1 W₁ (h.trans inf_le_right)]
      simp only [map_sub, map_add (f := _), map_mul]; ring
    · rw [(hf p.1).2.2 W₁ W₂ h (h₀.trans inf_le_left), (hf' p.2).2.2 W₁ W₂ h (h₀.trans inf_le_right), ← map_sub,
        app_resG]
    · rw [bse p.1 W₁ (h.trans inf_le_left), bse' p.2 W₁ (h.trans inf_le_right), sub_self, map_zero]
  choose h hh using ex
  have cmp : ∀ (p p' : J × J') (a : Fin n),
      rsT (h p a) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') - rsT (h p' a) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') =
      ∑ b, (constFn P₀.A.hom (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') (θ a b) *
          rsT (φ b (j p.1) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') -
        constFn P₀.A.hom (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') (θ' a b) *
          rsT (φ b (j' p.2) (j' p'.2)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p')) := by
    intro p p'
    let W₁ := Wp p ⊓ Wp p'
    have l1 : W₁ ≤ Wp p := inf_le_left
    have l2 : W₁ ≤ Wp p' := inf_le_right
    have k2 : m ⁻¹ᵁ W₁ ≤ m ⁻¹ᵁ Wp p := m.preimage_mono l1
    have k3 : m ⁻¹ᵁ W₁ ≤ m ⁻¹ᵁ Wp p' := m.preimage_mono l2
    have k4 : m ⁻¹ᵁ W₁ ≤ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) :=
      fun z hz => ⟨hWj p.1 (hz.1.1), hWj p'.1 (hz.2.1)⟩
    have k5 : m ⁻¹ᵁ W₁ ≤ m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) :=
      fun z hz => ⟨hWj' p.2 (hz.1.2), hWj' p'.2 (hz.2.2)⟩
    let y₁ : Fin n → Γ(P₀.A.left, m ⁻¹ᵁ W₁) := fun a =>
      rsT (h p a) _ - rsT (h p' a) _ - ∑ b, (constFn P₀.A.hom _ (θ a b) * rsT (φ b (j p.1) (j p'.1)) _ -
        constFn P₀.A.hom _ (θ' a b) * rsT (φ b (j' p.2) (j' p'.2)) _)
    have z := (coeff_id hs hu hdd x0 π m hm hU W₁ (l1.trans (hWpU p)) (fun _ _ => 0) (fun _ _ _ _ => by simp)
      (fun _ _ _ _ => by simp) (fun _ _ _ _ _ => by simp [rsT_zero]) (fun _ _ _ => rfl)).unique
      (y₁ := y₁) (y₂ := fun _ => 0) (fun W₂ hW₂ f => ?_) (fun W₂ hW₂ f => by simp [rsT_zero])
    · intro a
      have := congrFun z a
      simp only [y₁] at this
      rw [sub_eq_zero] at this
      exact this
    · have k1 : m ⁻¹ᵁ W₂ ≤ m ⁻¹ᵁ W₁ := m.preimage_mono hW₂
      have E1 := hh p W₂ (hW₂.trans l1) f
      have E2 := hh p' W₂ (hW₂.trans l2) f
      have E3 := hP p.1 p'.1 W₂ (fun z hz => ⟨(l1 (hW₂ hz)).1, (l2 (hW₂ hz)).1⟩) f
      have E4 := hP' p.2 p'.2 W₂ (fun z hz => ⟨(l1 (hW₂ hz)).2, (l2 (hW₂ hz)).2⟩) f
      have k1' : m ⁻¹ᵁ W₂ ≤ m ⁻¹ᵁ Wp p := k1.trans k2
      have k1'' : m ⁻¹ᵁ W₂ ≤ m ⁻¹ᵁ Wp p' := k1.trans k3
      have k4' : m ⁻¹ᵁ W₂ ≤ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) := k1.trans k4
      have k5' : m ⁻¹ᵁ W₂ ≤ m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) := k1.trans k5
      simp (disch := assumption) only [y₁, rsT_sub, rsT_sum, rsT_mul, rsT_rsT, rsT_constFn, sub_mul,
        Finset.sum_sub_distrib, Finset.sum_mul] at E1 E2 E3 E4 ⊢
      simp only [map_sub] at E1 E2 E3 E4
      linear_combination E1 - E2 - E3 + E4
  funext a
  refine sub_eq_zero.1 (hcob (θ a - θ' a) ?_)
  refine GlobalTheory.T.isCechOneCoboundary_of_refinement (fun i => m ⁻¹ᵁ L.U i) (lc P₀.A.hom (θ a - θ' a) φ) (isCoc_lc _ _ _ hcoc)
    (fun p => m ⁻¹ᵁ Wp p) (fun p => j p.1) (fun p => m.preimage_mono (inf_le_left.trans (hWj p.1))) ?_
    (fun p => -(h p a) - ∑ b, constFn P₀.A.hom _ (θ' a b) * rsT (φ b (j' p.2) (j p.1)) (m ⁻¹ᵁ Wp p)) ?_
  · refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨i, hi⟩ := hcov z
    obtain ⟨k, hk⟩ := hcov' z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, k), hi, hk⟩
  · intro p p'
    have k2 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ Wp p := inf_le_left
    have k3 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ Wp p' := inf_le_right
    have k4 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) :=
      fun z hz => ⟨hWj p.1 hz.1.1, hWj p'.1 hz.2.1⟩
    have k6 : m ⁻¹ᵁ Wp p ≤ m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) :=
      fun z hz => ⟨hWj' p.2 hz.2, hWj p.1 hz.1⟩
    have k7 : m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) :=
      fun z hz => ⟨hWj' p'.2 hz.2, hWj p'.1 hz.1⟩
    have T1 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤
        m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) :=
      fun z hz => ⟨⟨hWj' p.2 hz.1.2, hWj' p'.2 hz.2.2⟩, hWj p'.1 hz.2.1⟩
    have T2 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤
        m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) :=
      fun z hz => ⟨⟨hWj' p.2 hz.1.2, hWj p.1 hz.1.1⟩, hWj p'.1 hz.2.1⟩
    have C1 : ∀ b, rsT (φ b (j' p.2) (j' p'.2)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') +
        rsT (φ b (j' p'.2) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') =
        rsT (φ b (j' p.2) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') := fun b => by
      have := congrArg (fun s => rsT s (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p')) (hcoc b (j' p.2) (j' p'.2) (j p'.1))
      have a1 : m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) ≤
          m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) := inf_le_left
      have a2 : m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) ≤
          m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) := fun _ h => ⟨h.1.2, h.2⟩
      have a3 : m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) ≤
          m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) := fun _ h => ⟨h.1.1, h.2⟩
      simpa (disch := assumption) only [rsT_add, rsT_rsT] using this
    have C2 : ∀ b, rsT (φ b (j' p.2) (j p.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') +
        rsT (φ b (j p.1) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') =
        rsT (φ b (j' p.2) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') := fun b => by
      have := congrArg (fun s => rsT s (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p')) (hcoc b (j' p.2) (j p.1) (j p'.1))
      have a1 : m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) ≤
          m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) := inf_le_left
      have a2 : m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) ≤
          m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) := fun _ h => ⟨h.1.2, h.2⟩
      have a3 : m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) ≤
          m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) := fun _ h => ⟨h.1.1, h.2⟩
      simpa (disch := assumption) only [rsT_add, rsT_rsT] using this
    have E := cmp p p' a
    have k8 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) := k2.trans k6
    have k9 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) := k3.trans k7
    have k10 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) := k4
    simp (disch := assumption) only [lc, rsT_sub, rsT_neg, rsT_sum, rsT_mul, rsT_rsT, rsT_constFn, constFn_sub,
      sub_mul, Finset.sum_sub_distrib]
    have E' : ∑ b, (constFn P₀.A.hom (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') (θ a b) *
          rsT (φ b (j p.1) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') -
        constFn P₀.A.hom (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') (θ' a b) *
          rsT (φ b (j p.1) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p')) =
        rsT (h p a) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') - rsT (h p' a) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') +
        ∑ b, constFn P₀.A.hom (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') (θ' a b) *
          (rsT (φ b (j' p.2) (j p.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') -
            rsT (φ b (j' p'.2) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p')) := by
      rw [E, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      linear_combination (constFn P₀.A.hom (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') (θ' a b)) * (C1 b - C2 b)
    simp only [Pi.sub_apply, constFn_sub, sub_mul, mul_sub, Finset.sum_sub_distrib] at E' ⊢
    linear_combination E'

theorem eq_of_resG_eq_of_dense {Y : Scheme.{0}} [IsReduced Y] {U V : Y.Opens} (hV : Dense (V : Set Y))
    (f g : Γ(Y, U)) (h : resG Y (inf_le_left : U ⊓ V ≤ U) f = resG Y inf_le_left g) : f = g := by
  rw [← sub_eq_zero, ← AlgebraicGeometry.basicOpen_eq_bot_iff]
  have h0 : Y.basicOpen (resG Y (inf_le_left : U ⊓ V ≤ U) (f - g)) = ⊥ := by
    rw [map_sub, h, sub_self, Scheme.basicOpen_zero]
  rw [resG, Scheme.basicOpen_res] at h0
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨y, hy1, hy2⟩ := hV.inter_open_nonempty _ (Y.basicOpen (f - g)).isOpen ⟨x, hx⟩
  have : y ∈ (U ⊓ V) ⊓ Y.basicOpen (f - g) := ⟨⟨Y.basicOpen_le _ hy1, hy2⟩, hy1⟩
  rw [h0] at this
  exact this.elim

theorem isKS_unique_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ Θ' : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), IsKS Y.t (interior Y) U v D.1 Θ → IsKS Y.t (interior Y) U v D.1 Θ' → Θ = Θ' := by
  intro E _ _ _ H Dw l Xo c Y _ _ _ _ U n v A hv hb hA D Θ Θ' hK hK'
  haveI : IsReduced Y.X := GlobalTheory.Coisotropic.isReduced_of_isNormalScheme Y.normal
  have key : ∀ {K : Type} [Field K] (x0 : Sp K ⟶ Y.X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1), ⊤ ≤ x0 ⁻¹ᵁ interior Y →
      ∀ a b, GlobalTheory.FlagMod.ev x0 U.1 hU (Θ a b) = GlobalTheory.FlagMod.ev x0 U.1 hU (Θ' a b) := by
    intro K _ x0 hU hV a b
    obtain ⟨P₀, θm, hpb, hiso⟩ := exists_polAV_interior Y x0 hV
    haveI : IsCommMonObj P₀.A := P₀.isAb.comm
    have hx : spMap (GlobalTheory.FlagMod.ev x0 U.1 hU) ≫ chart U = x0 := GlobalTheory.FlagMod.spMap_ev x0 U.2 hU
    have hv' := fun i => GlobalTheory.LieMet.isTan_map (GlobalTheory.FlagMod.ev x0 U.1 hU) hx (hv i)
    have hb' := GlobalTheory.GradedPieces.basis_map (GlobalTheory.FlagMod.ev x0 U.1 hU) hx hv hb
    obtain ⟨u, hu, hu'⟩ := GlobalTheory.LiePull.lieBasis_of_tanBasis Y.t x0 P₀.A θm hpb _ hv' hb'
    choose dd hdd using fun a => (GlobalTheory.KS.InvField.main K P₀.A (u a) (hu.1 a)).1
    obtain ⟨⟨φ, hφ⟩, -⟩ := GlobalTheory.KS.DlogPol.dlog_independent K P₀ n u dd hu hdd _ θm Y.t.PP.L Y.t.PP.isLB hiso
    obtain ⟨J, W, j, d, hcov, hWj, hf, hl, hdiff⟩ := hK
    obtain ⟨J', W', j', d', hcov', hWj', hf', hl', hdiff'⟩ := hK'
    have hP := pull_diff Y.t (interior Y) U v hv Θ W j d hWj hdiff x0 hU P₀.A θm hpb u hu' dd hdd φ hφ
    have hP' := pull_diff Y.t (interior Y) U v hv Θ' W' j' d' hWj' hdiff' x0 hU P₀.A θm hpb u hu' dd hdd φ hφ
    have hWU : ∀ i, W i ≤ Y.t.G.hom ⁻¹ᵁ U.1 := fun i p hp => by
      have : p ∈ Y.t.G.hom ⁻¹ᵁ (U.1 ⊓ interior Y) := hcov ▸ (le_iSup W i) hp
      exact this.1
    have hWU' : ∀ i, W' i ≤ Y.t.G.hom ⁻¹ᵁ U.1 := fun i p hp => by
      have : p ∈ Y.t.G.hom ⁻¹ᵁ (U.1 ⊓ interior Y) := hcov' ▸ (le_iSup W' i) hp
      exact this.1
    have hfib : ∀ z, Y.t.G.hom (θm z) ∈ U.1 ⊓ interior Y := fun z => by
      rw [← Scheme.Hom.comp_apply, hpb.1.w, Scheme.Hom.comp_apply]
      exact ⟨hU (Set.mem_univ _), hV (Set.mem_univ _)⟩
    have hcv : ∀ z, ∃ i, θm z ∈ W i := fun z => by
      have h2 : θm z ∈ ⨆ i, W i := by rw [hcov]; exact hfib z
      exact TopologicalSpace.Opens.mem_iSup.1 h2
    have hcv' : ∀ z, ∃ i, θm z ∈ W' i := fun z => by
      have h2 : θm z ∈ ⨆ i, W' i := by rw [hcov']; exact hfib z
      exact TopologicalSpace.Opens.mem_iSup.1 h2
    have := theta_eq_fibre P₀ u hu dd hdd Y.t.G.hom x0 θm hpb.1 U.2 Y.t.PP.L Y.t.PP.isLB hiso _
      (Matrix.of fun a b => GlobalTheory.FlagMod.ev x0 U.1 hU (Θ a b)) (Matrix.of fun a b => GlobalTheory.FlagMod.ev x0 U.1 hU (Θ' a b))
      W W' j j' d d' hWU hWU' hWj hWj' hcv hcv' hf hf' hl hl' φ hφ hP hP'
    exact congrFun (congrFun this a) b
  refine Matrix.ext fun a b => eq_of_resG_eq_of_dense (V := interior Y) (dense_interior Y) _ _ ?_
  refine GlobalTheory.GenericExtend.eq_of_valR_eq fun x hx => ⟨Y.X.residueField x, inferInstance,
    Y.X.fromSpecResidueField x, fun o => Scheme.fromSpecResidueField_apply x o, ?_⟩
  have ho : ∀ o, (Y.X.fromSpecResidueField x : Sp (Y.X.residueField x) ⟶ Y.X) o = x :=
    fun o => Scheme.fromSpecResidueField_apply x o
  generalize (Y.X.fromSpecResidueField x : Sp (Y.X.residueField x) ⟶ Y.X) = h at ho
  have hU : ⊤ ≤ h ⁻¹ᵁ U.1 := fun o _ => show h o ∈ U.1 by rw [ho]; exact hx.1
  have hV : ⊤ ≤ h ⁻¹ᵁ interior Y := fun o _ => show h o ∈ interior Y by rw [ho]; exact hx.2
  have hUV : ⊤ ≤ h ⁻¹ᵁ (U.1 ⊓ interior Y) := fun o _ => show h o ∈ U.1 ⊓ interior Y by rw [ho]; exact hx
  exact (GlobalTheory.CechKS.valR_resG h _ hUV _).trans ((GlobalTheory.CechKS.valR_eq_ev _ _ hU _).trans ((key h hU hV a b).trans
    ((GlobalTheory.CechKS.valR_eq_ev _ _ hU _).symm.trans (GlobalTheory.CechKS.valR_resG h _ hUV _).symm)))

end GlobalTheory.KSUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMetricUnitaryGauge
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.ChowHt GlobalTheory.CompHt
open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.HermLB

theorem isometric_pull_fs_toProj : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (L : GlobalTheory.HermLB p) (m : ℕ) (t : Fin (m + 1) → L.B.Sec) (ht : ⨆ j, nonzeroLocus (t j) = ⊤)
    (A : (k →+* ℂ) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hA : ∀ σ, (A σ).det ≠ 0)
    (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin (m + 1)) ℂ, A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U),
    (∀ (σ : k →+* ℂ) (i : L.B.ι) (y : GlobalTheory.CxPts p σ), y ∈ ptsIn p σ (L.B.U i) →
      (L.φ σ).φ i y = Real.log (∑ a, ‖∑ j, A σ j a * valR y.1 (L.B.U i) ((t j).f i)‖ ^ 2)) →
    ((GlobalTheory.HermLB.fs (PSpace.str k m) (GlobalTheory.ProjSpace.O1_isLB k m) (GlobalTheory.ProjSpace.coord k m) (GlobalTheory.ProjSpace.iSup_nonzeroLocus_coord k m) A hA hc).pull
      (GlobalTheory.ProjSpace.toProj p t ht) (GlobalTheory.ProjSpace.toProj_str p t ht)).Isometric L := by
  intro k _ X p L m t ht A hA hc h
  refine ⟨ProjSpace.toProjIso p t ht, ProjSpace.toProjIso_isGen p t ht, fun σ a b y ha hb => ?_⟩
  let π := ProjSpace.toProj p t ht
  have hπ : π ≫ PSpace.str k m = p := ProjSpace.toProj_str p t ht
  let z := Points.PtsOver.map π hπ (spMap σ) y
  let B := (ProjSpace.O1 k m).pull π
  have hb' : y ∈ ptsIn p σ (B.U b) := hb
  have hab : y ∈ ptsIn p σ (L.B.U a ⊓ B.U b) := mem_ptsIn_inf.2 ⟨ha, hb'⟩
  have hz : z ∈ ptsIn (PSpace.str k m) σ ((ProjSpace.O1 k m).U (b PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => z) (fun _ => rfl) hb' PUnit.unit
  let u : Γ(X, L.B.U a ⊓ B.U b)ˣ := (ProjSpace.toProjIso p t ht).s (a, b)
  let r : Fin (m + 1) → ℂ := fun j =>
    valR z.1 ((ProjSpace.O1 k m).U (b PUnit.unit)) ((ProjSpace.coord k m j).f (b PUnit.unit))
  have hu : ev p σ _ u.val y ≠ 0 := ev_ne_zero hab u.isUnit
  have e (j) : valR y.1 (L.B.U a) ((t j).f a) = ev p σ _ u.val y * r j := by
    have e₁ : resG X (inf_le_left : L.B.U a ⊓ B.U b ≤ L.B.U a) ((t j).f a) =
        u.val * resG X inf_le_right ((Cartier.secPull (ProjSpace.coord k m j) π).f b) :=
      ProjSpace.secMaps_toProjIso p t ht j (a, b)
    have e₂ := congrArg (ev p σ _ · y) e₁
    simp only [ev_mul, ev_res _ hab] at e₂
    exact e₂.trans (congrArg (_ * ·) (Points.valR_appLE y.1 π _ hb' _))
  have h0 := (Weight.noCommonZero_combVal (p := PSpace.str k m) (σ := σ)
    (ProjSpace.iSup_nonzeroLocus_coord k m) (hA σ)).sum_pos hz
  have h0' : 0 < ∑ c, ‖∑ j, A σ j c * r j‖ ^ 2 := h0.trans_eq (Finset.sum_congr rfl fun c _ =>
    congrArg (‖·‖ ^ 2) ((congrFun (Finset.sum_apply _ _ _) z).trans (Finset.sum_apply _ _ _)))
  have e₃ := (Weight.pull_φ (Weight.fsBasis (PSpace.str k m) σ (ProjSpace.O1_isLB k m) (ProjSpace.coord k m)
    (ProjSpace.iSup_nonzeroLocus_coord k m) (A σ) (hA σ)) π hπ b y).trans (Weight.fsBasis_φ _ _ _ _ _ _ _)
  refine (h σ a y ha).trans (Eq.trans ?_ (congrArg (· + Real.log (‖ev p σ _ u.val y‖ ^ 2)) e₃.symm))
  refine Eq.trans ?_ (Real.log_mul h0'.ne' (pow_ne_zero 2 (norm_ne_zero_iff.2 hu)))
  rw [Finset.sum_mul]
  refine congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
  rw [← mul_pow, ← norm_mul, Finset.sum_mul]
  refine congrArg (‖·‖ ^ 2) (Finset.sum_congr rfl fun j _ => ?_)
  rw [e j]
  ring

end GlobalTheory.HermLB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialDegenerationUnitPartExists
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnitPart

theorem exists_gen_of_top {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (j₀ : K → M.ι) (all : ∀ w : Y, w ∈ LB.wchart M φ j₀) (v : Γ(Y, ⊤)ˣ) :
    ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → M.ι),
      r z ∈ LB.wchart M φ j → gm r z (LB.wchart M φ j) (t.s j) = trF φ ε r z j j₀ * gm r z ⊤ v := by
  have le : ∀ j, LB.wchart M φ j ≤ LB.wchart M φ j ⊓ LB.wchart M φ j₀ := fun j w hw => ⟨hw, all w⟩
  let t : LB.Gen (LB.LinComb M φ ε) :=
    ⟨fun j => res (le j) ((LB.LinComb M φ ε).g j j₀) * res (le_top : LB.wchart M φ j ≤ ⊤) v⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → M.ι),
      r z ∈ LB.wchart M φ j → gm r z (LB.wchart M φ j) (t.s j) = trF φ ε r z j j₀ * gm r z ⊤ v :=
    fun Z r z j h => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z (le j) h _).trans (gm_linComb M φ ε r z j j₀ h (all _))) (gm_res r z le_top h _))
  refine ⟨t, fun j j' => Geo.Tor.unit_ext fun w hw => ?_, key⟩
  have hm : (𝟙 Y : Y ⟶ Y) w ∈ LB.wchart M φ j ⊓ LB.wchart M φ j' := hw
  refine ((gm_res _ w _ hm _).trans (key _ _ w j hm.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb M φ ε (𝟙 Y) w j j' hm.1 hm.2)
      ((gm_res _ w _ hm _).trans (key _ _ w j' hm.2)))).symm)
  rw [← trF_trans hM φ ε (𝟙 Y) w hm.1 hm.2 (all _), _root_.mul_assoc]
  rfl

theorem jK_app_toOpen {R : Type} [CommRing R] [IsDomain R] (r : R) :
    ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r) := by
  have e : DegPre.toOpen (R := R) ⊤ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
    ext r
    simp [DegPre.toOpen]
  rw [e]
  exact (congrArg (fun q => q.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))).symm

theorem exists_isUnitPart : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → ∀ y, ∃ n ψ₀, IsUnitPart Q t gam y n ψ₀ := by
  intro R _ _ Q m t gam h y
  obtain ⟨u, n, hn, hc⟩ := h y
  have h0 : ∏ i, t i ^ n i ≠ 0 := right_ne_zero_of_mul (PsiCoordLocal.ne_zero_of_coord hc)
  have h1 : algebraMap R (FractionRing R) (∏ i, t i ^ n i) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 h0
  obtain ⟨j₀, hj, hle, e⟩ := hc
  have all : ∀ w, w ∈ LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c y).left) j₀ := fun w =>
    Set.mem_iInter.2 fun _ => hj trivial
  obtain ⟨ψ₀, hg, hv⟩ := exists_gen_of_top Q.P.isLB (K := PUnit) (fun _ => (Q.c y).left) (fun _ => -1) j₀ all (unitOn u)
  refine ⟨n, ψ₀, hg, hn, Units.mk0 _ h1, rfl, fun z J hJ => ?_⟩
  have m₀ : (𝟙 (TK R).left : _ ⟶ _) z ∈ LB.wchart Q.P.L (K := PUnit) (fun _ => Q.xK y) j₀ := hle trivial
  have a := gen_trans (Q.psi_gen y) (𝟙 (TK R).left) z (hJ.mem (fun _ : PUnit => Q.xK y) (𝟙 _)) m₀
  have b := hv _ (toUnit (TK R)).left z _ (hJ.mem (fun _ : PUnit => (Q.c y).left) (toUnit (TK R)).left)
  have c : gm (𝟙 (TK R).left) z (LB.wchart Q.P.L (K := PUnit) (fun _ => Q.xK y) j₀) ((Q.psi y).s j₀) =
      gm (𝟙 (TK R).left) z ⊤ (unitOn (Units.mk0 _ h1)) * gm (toUnit (TK R)).left z ⊤ (unitOn u) := by
    have d : res hle ((Q.psi y).s j₀) =
        unitOn (Units.mk0 _ h1) * (show Γ(Sp (FractionRing R), ⊤)ˣ from pullU (jK R) ⊤ (unitOn u)) := by
      refine Units.ext (e.symm.trans ?_)
      rw [jK_app_toOpen, map_mul, _root_.mul_comm, map_mul]
      refine congrArg₂ (· * ·) rfl ?_
      rw [← jK_app_toOpen]
      exact congrArg _ (by simp [DegPre.toOpen, unitOn])
    refine (gm_res _ z hle trivial _).symm.trans ((congrArg _ d).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ?_)))
    exact gm_pull (𝟙 _) (jK R) z ⊤ trivial _
  refine a.trans (Eq.trans ?_ (congrArg _ b).symm)
  rw [c, mul_left_comm]
  rfl

end GlobalTheory.UnitPart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionContinuousLimit
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.HermLB GlobalTheory.CxPts GlobalTheory.Published

namespace GlobalTheory.SelfCont

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem icls_fnB_add {u v w : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hu hc hv hd hw he) (e : ∀ σ y, w σ y = u σ y + v σ y) :
    (fnB w hw he).icls = (fnB u hu hc).icls + (fnB v hv hd).icls := by
  rw [← icls_tens, icls_eq_iff.2 (isometric_tens_fnB _ v hv hd)]
  exact icls_eq_iff.2 (isometric_of_eqOn fun σ _ y _ => (e σ y).symm)

theorem isConj_mul {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ}
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (c : ℝ) (σ σ' : k →+* ℂ) :
    (Weight.ofFun fun y => c * u σ y).IsConj (Weight.ofFun fun y => c * u σ' y) :=
  fun i y y' h hy => congrArg (c * ·) (hc σ σ' i y y' h hy)

theorem icls_fnB_mul {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hu : ∀ σ y, CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (n : ℤ) :
    (fnB (fun σ y => (n : ℝ) * u σ y) (fun σ y => (hu σ y).const_mul _) (isConj_mul hc _)).icls =
      n • (fnB u hu hc).icls := by
  have key (m : ℤ) := icls_fnB_add (p := p) (w := fun σ y => ((m + 1 : ℤ) : ℝ) * u σ y) (u := fun σ y => (m : ℝ) * u σ y)
    (fun σ y => (hu σ y).const_mul _) (isConj_mul hc _) hu hc (fun σ y => (hu σ y).const_mul _) (isConj_mul hc _)
    fun σ y => by push_cast; ring
  induction n using Int.induction_on with
  | zero =>
    have := icls_fnB_add (p := p) (w := u) (u := fun σ y => ((0 : ℤ) : ℝ) * u σ y)
      (fun σ y => (hu σ y).const_mul _) (isConj_mul hc _) hu hc hu hc fun σ y => by push_cast; ring
    rw [zero_smul]
    exact right_eq_add.1 this
  | succ n ih => rw [key, ih, add_smul, one_smul]
  | pred n ih =>
    have := key (-(n : ℤ) - 1)
    simp only [sub_add_cancel] at this
    rw [sub_smul, one_smul, ← ih, this, add_sub_cancel_right]

variable [IsIntegral X] {D : ℕ} {t : ℝ → ℝ} {u : ℝ → ∀ σ : k →+* ℂ, CxPts p σ → ℝ}


omit [IsIntegral X] in
theorem isometric_comb_raise {v : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hv : ∀ σ y, CInfAt (v σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (v σ)).IsConj (Weight.ofFun (v σ'))) (N : HermLB p) (n : Fin 2 → ℤ) :
    (comb ![fnB v hv hc, N] n).Isometric ((zp N (n 1)).raise (fun σ y => (n 0 : ℝ) * v σ y)
      (fun σ y => (hv σ y).const_mul _) (isConj_mul hc _)) :=
  icls_eq_iff.1 (by
    rw [← icls_eq_iff.2 (isometric_tens_fnB _ _ _ _), icls_tens, icls_fnB_mul hv hc, icls_zp, icls_comb,
      Fin.sum_univ_two, add_comm]
    rfl)

theorem mixed_eq (H : ArCalc) (hX : IsArithVar p D) {v : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hv : ∀ σ y, CInfAt (v σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (v σ)).IsConj (Weight.ofFun (v σ'))) (N : HermLB p)
    {Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ} (hΘ : IsArFun ![fnB v hv hc, N] D Θ) (n : Fin 2 → ℤ) :
    Θ (MvPolynomial.X 0 * lin (fun i => (n i : ℝ)) ^ D) = 1 / 2 * chInt (comb ![fnB v hv hc, N] n) D v := by
  let A : Option (Fin 2) → Fin 2 → ℤ := fun j => Pi.single (j.elim 0 id) 1
  have h := ((H.arIso k X p D hX).2 _ _ Θ hΘ).2.2 (Option (Fin 2))
    (fun o => o.elim (fnB v hv hc) ![fnB v hv hc, N]) A (by
      rintro (_ | i)
      · exact isometric_comb_single _ 0
      · exact isometric_comb_single _ i)
  have e (j : Option (Fin 2)) : (lin fun i => (A j i : ℝ)) = MvPolynomial.X (j.elim 0 id) := lin_single _
  rw [← H.arChange k X p D hX _ _ v hv hc _ h n, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  congr 1
  rw [map_mul, map_pow, aeval_X, aeval_rename]
  simp only [Function.comp_def, e, Option.elim_none, Option.elim_some, id, aeval_X_left_apply]

end GlobalTheory.SelfCont

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTangentBasisOfRaynaudBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTangentBasisOfRaynaudBasis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TanRay

open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv_mem mkT tv_mkT tanM_ext tv_add tv_smul)

theorem tanBasis_of_isPointOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∃ b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G), ∀ a, b a = v' a := by
  intro E _ _ _ H R _ _ _ _ _ _ t P
  letI := H.starRing
  intro Y n vH v' hv
  have hc : IsAdicComplete ((maximalIdeal R).map (algebraMap R (DualNumber R))) (DualNumber R) := by
    have : Module.Finite R (DualNumber R) := inferInstanceAs (Module.Finite R (R × R))
    exact GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal R) (DualNumber R)
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  have hT : GlobalTheory.AdicColimit.IsAdicColimit (maximalIdeal R) (overAt (𝟙 (Sp R)) (DualNumber R)) := by
    refine GlobalTheory.AdicColimit.IsAdicColimit.of_iso (Over.isoMk (Iso.refl _) ?_)
      (GlobalTheory.AdicColimit.isAdicColimit_spec_of_isLocalRing R (maximalIdeal R) (DualNumber R)
        (algebraMap R (DualNumber R)) hc)
    simp
  have hΦ := Y.rep
  obtain ⟨J, hJ⟩ := GlobalTheory.TorusModel.exists_mulEquiv P.U.toUnifPre GlobalTheory.allSixLaws.1.globalFns hΦ
  have nat : ∀ (k : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ overAt (𝟙 (Sp R)) (DualNumber R))
      (w : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ Y.H), J _ hT (k ≫ w) = k ≫ J _ hT w := fun k w =>
    (hJ _ hT _ _).2 (((hJ _ hT w _).1 rfl).pull k (hΦ.1 _ _ k _))
  have hs : ∀ (a : R) (w : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ Y.H),
      J _ hT (smT (𝟙 (Sp R)) a w) = smT (𝟙 (Sp R)) a (J _ hT w) := fun a w => nat _ w
  have mem : ∀ v : TanM (𝟙 (Sp R)) Y.H, smT (𝟙 (Sp R)) 0 (J _ hT (tv v)) = 1 := fun v => by
    rw [← hs, tv_mem, map_one]
  let L : TanM (𝟙 (Sp R)) Y.H →ₗ[R] TanM (𝟙 (Sp R)) t.G :=
    { toFun := fun v => mkT (J _ hT (tv v)) (mem v)
      map_add' := fun u v => tanM_ext (by
        simp only [tv_mkT, tv_add, map_mul])
      map_smul' := fun a v => tanM_ext (by
        simp only [tv_mkT, tv_smul, RingHom.id_apply, hs]) }
  have hL : Function.Bijective L := by
    refine ⟨fun u v h => tanM_ext ((J _ hT).injective ?_), fun w => ?_⟩
    · have := congrArg tv h
      simpa [L, tv_mkT] using this
    · have h0 : smT (𝟙 (Sp R)) 0 ((J _ hT).symm (tv w)) = 1 := by
        apply (J _ hT).injective
        rw [hs, MulEquiv.apply_symm_apply, tv_mem, map_one]
      refine ⟨mkT _ h0, tanM_ext ?_⟩
      show J _ hT ((J _ hT).symm (tv w)) = tv w
      exact MulEquiv.apply_symm_apply _ _
  refine ⟨vH.map (LinearEquiv.ofBijective L hL), fun a => ?_⟩
  rw [Module.Basis.map_apply, LinearEquiv.ofBijective_apply]
  refine tanM_ext ?_
  exact (hJ _ hT _ _).2 (hv a)

end GlobalTheory.TanRay
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTangentBasisOfRaynaudBasisStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedTangentBasis_of_raynaudBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∃ b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G), ∀ a, b a = v' a := by
  first | exact @GlobalTheory.TanRay.tanBasis_of_isPointOf | exact GlobalTheory.TanRay.tanBasis_of_isPointOf | (intros; apply GlobalTheory.TanRay.tanBasis_of_isPointOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldConstFnEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldConstFnEqZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat

theorem IsInv.apply_constFn {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left) (hinv : IsInv G v dd) (O : G.left.Opens) (r : R) :
    dd O (constFn G.hom O r) = 0 := by

  have key : ∀ (U : G.left.Opens) (hU : IsAffineOpen U) (hle : U ≤ O),
      (G.left.presheaf.map (homOfLE hle).op).hom (dd O (constFn G.hom O r)) = 0 := by
    intro U hU hle
    let g : Sp Γ(G.left, U) ⟶ G.left := hU.fromSpec
    let φ : R →+* Γ(G.left, U) := (Spec.preimage (g ≫ G.hom)).hom
    have hφ : g ≫ G.hom = spMap φ := by simp [φ, spMap]
    have hgU : ⊤ ≤ g ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
    have hgO : ⊤ ≤ g ⁻¹ᵁ O := hgU.trans (g.preimage_mono hle)

    have e : (dualMap φ).comp (algebraMap R (DualNumber R)) =
        (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))).comp φ := by
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    have hv : (tv v).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) :=
      (Over.w (tv v)).trans (Category.comp_id _)
    have h2 : (spMap (dualMap φ) ≫ (tv v).left) ≫ G.hom = (tEpsG (g ≫ G.hom)).hom := by
      show _ = spMap (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))) ≫ g ≫ G.hom
      refine (Category.assoc _ _ _).trans ((congrArg (spMap (dualMap φ) ≫ ·) hv).trans ?_)
      rw [hφ, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
    let g' : tEpsG (g ≫ G.hom) ⟶ G :=
      Over.homMk (spMap (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))) ≫ g) (Category.assoc _ _ _)
    let v' : tEpsG (g ≫ G.hom) ⟶ G := Over.homMk (spMap (dualMap φ) ≫ (tv v).left) h2
    have htr : IsTr G φ g v (g' * v').left := ⟨g', v', rfl, rfl, rfl⟩
    have hval := hinv.2 _ φ g _ O (constFn G.hom O r) hφ hgO htr

    have hw : (g' * v').left ≫ G.hom =
        spMap ((algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))).comp φ) := by
      refine (Over.w (g' * v')).trans ?_
      show spMap (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))) ≫ g ≫ G.hom = _
      rw [hφ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h0 : (valR (g' * v').left O (constFn G.hom O r)).snd = 0 := by
      by_cases hO : ⊤ ≤ (g' * v').left ⁻¹ᵁ O
      · rw [GlobalTheory.ArcPts.SecValue.valR_constFn G.hom _ _ hw O hO r]
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      · rw [valR, dite_eq_right hO]
        rfl
    rw [h0, ← GlobalTheory.HolHom.valR_res g hle _ hgU] at hval
    rw [← GlobalTheory.DetRatio.valR_fromSpec hU ((G.left.presheaf.map (homOfLE hle).op).hom (dd O (constFn G.hom O r)))]
    exact hval.symm
  refine G.left.sheaf.eq_of_locally_eq' (fun k : {U : G.left.Opens // IsAffineOpen U ∧ U ≤ O} => k.1) O
    (fun k => homOfLE k.2.2) ?_ _ 0 fun k => ?_
  · intro x hx
    obtain ⟨U, hU, hxU, hUO⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp G.left.isBasis_affineOpens hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUO⟩, hxU⟩
  · exact (key k.1 k.2.1 k.2.2).trans (map_zero _).symm

end GlobalTheory.Heat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldConstFnEqZeroStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantVectorField_constFn_eq_zero : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left), IsInv G v dd → ∀ (O : G.left.Opens) (r : R), dd O (constFn G.hom O r) = 0 := by
  first | exact @GlobalTheory.Heat.IsInv.apply_constFn | exact GlobalTheory.Heat.IsInv.apply_constFn | (intros; apply GlobalTheory.Heat.IsInv.apply_constFn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceBoundTuple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVectorThreeStepDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVectorThreeStepDecomposition
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.LiftThreeStep

theorem omegaQ_union {D : D7} {a b : ℕ} {Sa St : Finset (Pl D.host.E)} (hd : Disjoint Sa St) (r : ℕ)
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    omegaQ (Sa ∪ St) r ξ k y = omegaQ Sa r ξ k y * omegaQ St r ξ k y := by
  let g : Pl D.host.E → ℂ := fun PP =>
    if h : LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ k else 0
  have key : ∀ Q : Finset (Pl D.host.E), omegaQ Q r ξ k y = ∏ PP ∈ Q, g PP := by
    intro Q
    unfold omegaQ
    by_cases h : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
    · rw [dite_eq_left h, ← Finset.prod_attach Q g]
      refine Finset.prod_congr rfl fun PP _ => ?_
      simp only [g]
      rw [dite_eq_left (h PP.1 PP.2)]
    · rw [dite_eq_right h]
      obtain ⟨PP, hPP⟩ := not_forall.1 h
      obtain ⟨hQ, hn⟩ := Classical.not_imp.1 hPP
      refine (Finset.prod_eq_zero hQ ?_).symm
      simp only [g]
      rw [dite_eq_right hn]
  rw [key, key, key, Finset.prod_union hd]

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

theorem adjDat_union {Sa St : Finset (Pl D.host.E)} {ea et : AE D} (hg : IsIdemSum ea Sa) (hq : IsIdemSum et St)
    (hd : Disjoint Sa St) (he : IsIdemSum (ea + et) (Sa ∪ St)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    adjDat R i (Sa ∪ St) ξ (cA D (ea + et)) =
      GlobalTheory.TwoStepModel.tensorHalf (cA D et) (cA D ea) (adjDat R i Sa ξ (cA D ea)) (adjDat R i St ξ (cA D et)) := by
  have hA := GlobalTheory.ConjHalfSplitInt.frMapAdj_int_iff D _ _ (R.βV i) (R.βW i) Sa St ea et hg hq hd he
  have hB := GlobalTheory.TwoStepRed.redM_twoStep D _ _ (R.βV i) (R.βW i) Sa St ea et hg hq hd he
  have heg := GlobalTheory.PlaceVec.idemSum_mul_self hg
  have heQ := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hcg : ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D ea) (cA D ea • x) :=
    fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heg]) x
  have hcQ : ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D et) (cA D et • x) :=
    fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heQ]) x
  funext x
  rw [GlobalTheory.TwoStepModel.tensorHalf_apply]
  unfold adjDat
  have hc : cA D (ea + et) = cA D et + cA D ea := by rw [map_add (f := _), add_comm]
  by_cases hx : IsHalf (cA D (ea + et)) x
  · have hx' : IsHalf (cA D et + cA D ea) x := hc ▸ hx
    rw [if_pos hx', mul_one]
    by_cases hi : IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) x)
    · obtain ⟨i1, i2⟩ := (hA x hx).1 hi
      obtain ⟨r1, r2⟩ := hB x hx hi
      rw [if_pos (And.intro hx hi), if_pos (And.intro (hcQ x) i2), if_pos (And.intro (hcg x) i1), omegaQ_union hd, mul_comm]
      congr 1
      · exact GlobalTheory.PlaceVec.omegaQ_congr St _ ξ _ fun PP hPP => (r2 PP hPP).symm
      · exact GlobalTheory.PlaceVec.omegaQ_congr Sa _ ξ _ fun PP hPP => (r1 PP hPP).symm
    · have c1 : ¬ (IsHalf (cA D (ea + et)) x ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) x)) := fun h => hi h.2
      rw [if_neg c1]
      have := mt (hA x hx).2 hi
      rcases not_and_or.1 this with h | h
      · have c3 : ¬ (IsHalf (cA D ea) (cA D ea • x) ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) (cA D ea • x))) :=
          fun h' => h h'.2
        rw [if_neg c3, mul_zero]
      · have c2 : ¬ (IsHalf (cA D et) (cA D et • x) ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) (cA D et • x))) :=
          fun h' => h h'.2
        rw [if_neg c2, zero_mul]
  · have c1 : ¬ (IsHalf (cA D (ea + et)) x ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) x)) := fun h => hx h.1
    have hx' : ¬ IsHalf (cA D et + cA D ea) x := hc ▸ hx
    rw [if_neg c1, if_neg hx', mul_zero]

end

theorem thetaVector_three_step_decomposition : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa St : Finset (Pl D.host.E)), Disjoint Sa St → Sa ∪ St = R.Q t → ∀ (eg ea et : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → IsIdemSum et St → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ∃ gA : WO (Vc D i) (Wc D i) → ℂ, ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) gA ∧ ThAt R i (cA D et) gA (adjDat R i St (R.xiR t) (cA D et)) (R.vP i t) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i t _ Sa St hd hU eg ea et fg hg ha ht hfg
  obtain ⟨⟨hψ, -⟩, e, he, -⟩ := hC.thP.vP i t
  have hSV := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have hSW := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  obtain ⟨eQ, hq⟩ := (GlobalTheory.IdemFlip.idemSum_sub_and_flip D e _ (R.Q t) he Finset.subset_union_right).1
  have h2 : ThAt R i (cA D eQ) fg (adjDat R i (R.Q t) (R.xiR t) (cA D eQ)) (R.vP i t) :=
    GlobalTheory.ConjTwist.isThetaAt_vP_twoStep D G Pl0 T0 A Ks R F hC hG i t eg eQ fg hg hq hfg
  rw [← hU] at hq h2
  have hsum : eQ = ea + et := by
    rw [← GlobalTheory.ExportSeries.idem_eq hq, ← GlobalTheory.ExportSeries.idem_eq ha, ← GlobalTheory.ExportSeries.idem_eq ht]
    exact Finset.sum_union hd
  subst hsum
  have hea := GlobalTheory.PlaceVec.idemSum_mul_self ha
  have het := GlobalTheory.PlaceVec.idemSum_mul_self ht
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hat : ea * et = 0 := by
    refine GlobalTheory.PlaceVec.natCast_mul_eq_zero 2 _ two_pos ?_
    push_cast
    linear_combination hee - hea - het
  have hca : cA D ea * cA D ea = cA D ea := by rw [← map_mul, hea]
  have hct : cA D et * cA D et = cA D et := by rw [← map_mul, het]
  have hta : cA D et * cA D ea = 0 := by rw [← map_mul, mul_comm, hat, map_zero]
  have hat' : cA D ea * cA D et = 0 := by rw [mul_comm, hta]
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True),
      a • u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) :=
    fun a ha u hu => GlobalTheory.PlaceModelSum.idem_smul_latO ha hu
  have hinfa : infPart D (cA D ea) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart ha)
  have hinft : infPart D (cA D et) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart ht)
  have hSB : ∀ (Q : Finset (Pl D.host.E)) (a : AE D), infPart D a = 0 →
      IsSBHalf a (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (adjDat R i Q (R.xiR t) a) :=
    fun Q a hinf => GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSV) (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSW) hinf (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
      (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
      Q (fun y => omegaQ Q (Wc D i).rank (R.xiR t) (-1) y) fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  obtain ⟨⟨Te, hTe1⟩, hTe2⟩ := h2
  have hc : cA D (ea + et) = cA D et + cA D ea := by rw [map_add (f := _), add_comm]
  have hc' : cA D (ea + et) = cA D ea + cA D et := map_add _ _ _
  have hm1 := GlobalTheory.TwoStepModel.isPlaceModel_comp_tensorHalf hct hca hta hΛ (hSB Sa _ hinfa) (hc ▸ hTe1)
  have hm2 := GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf hca hct hat' hΛ (hc' ▸ hTe1)
  refine ⟨_, ⟨⟨_, hm2⟩, fun T' hT' => ?_⟩, ⟨_, hm1⟩, fun T' hT' => ?_⟩
  · exact GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hca hinfa hm2 hT' (hSB Sa _ hinfa)
  · rw [hTe2 Te hTe1, adjDat_union R i ha ht hd hq (R.xiR t)]
    exact GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hct hinft hm1 hT' (hSB St _ hinft)

end GlobalTheory.LiftThreeStep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVectorThreeStepDecompositionStatement
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_vector_three_step_decomposition : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa St : Finset (Pl D.host.E)), Disjoint Sa St → Sa ∪ St = R.Q t → ∀ (eg ea et : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → IsIdemSum et St → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ∃ gA : WO (Vc D i) (Wc D i) → ℂ, ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) gA ∧ ThAt R i (cA D et) gA (adjDat R i St (R.xiR t) (cA D et)) (R.vP i t) := by
  first | exact @GlobalTheory.LiftThreeStep.thetaVector_three_step_decomposition | exact GlobalTheory.LiftThreeStep.thetaVector_three_step_decomposition | (intros; apply GlobalTheory.LiftThreeStep.thetaVector_three_step_decomposition <;> assumption)
end
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.BigOn.Exp.TupLe.Swap

theorem flat_gen : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (B : Base (Vc D i) (Wc D i)) (ψ : Twist D Circle), B.Good → BaseOf R i B → ψ.Good → B.admitted ψ.Q → R.xi t = B.de.chi * ψ.chi → idem (R.Q t) + cA D (idem (R.Q t)) = idem (B.de.Q ∪ ψ.Q) + cA D (idem (B.de.Q ∪ ψ.Q)) → ∃ (z : GA D (Vc D i)) (c : ℂ), SuppAt (idem (R.Q t)) (Vc D i) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime R t) c ∧
    (princ B).vecFlat ψ = c • R.ωP i t (z⁻¹, 1) (R.vP i t) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i t hV B ψ hB hB0 hψ hQ hxi hid
  classical
  obtain ⟨eg, ea, et, fg, hA, heg, hea, het, hfg, hhA, hflat⟩ := GlobalTheory.T.flatVector_three_steps_conjugate_places D G Pl0 T0 A Ks R F hC hQG i t hV B ψ hB hB0 hψ hQ hxi hid
  have hdisj : Disjoint (keepPart (R := R) t (B.de.Q ∪ ψ.Q)) (flipPart (R := R) t (B.de.Q ∪ ψ.Q)) :=
    Finset.disjoint_filter_filter_not _ _ _
  have hun : keepPart (R := R) t (B.de.Q ∪ ψ.Q) ∪ flipPart (R := R) t (B.de.Q ∪ ψ.Q) = R.Q t :=
    Finset.filter_union_filter_not_eq _ _
  obtain ⟨gA, hgA, hvP⟩ := GlobalTheory.T.lift_vector_three_step_decomposition D G Pl0 T0 A Ks R F hC hQG i t hV _ _ hdisj hun eg ea et fg heg hea het hfg
  obtain ⟨zA, cA', hzA, hzA', hcA, hAeq⟩ := GlobalTheory.T.flatVector_eq_unit_smul_centralTranslate_placePart D G Pl0 T0 A Ks R F hC hQG i t hV _ (Finset.filter_subset _ _) eg ea fg heg hea hfg
  obtain ⟨zT, cT, -, hzT', hcT, hT⟩ := GlobalTheory.T.flatDatum_liftDatum_same_half_translate_conjugatePlaces D G Pl0 T0 A Ks R F hC hQG i t hV B ψ hB hB0 hψ hQ hxi hid eg ea et fg hA heg hea het hfg hhA
  have e1 : hA = cA' • R.ωP i t (zA⁻¹, 1) gA := hAeq hA gA hhA hgA
  have hm := GlobalTheory.T.theta_half_moves_under_translate_other_places D G Pl0 T0 A Ks R F hC hQG i t hV _ _ (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj eg ea et fg gA _ _ zA cA'
    heg hea het hfg hgA hzA hcA.1 hvP
  rw [← e1] at hm
  have e2 := hT _ _ hflat hm
  refine ⟨zA * zT, cT * cA', suppAt_mul' hzA' hzT', GlobalTheory.BigOn.Exp.TupLe.unitOff_mul hcT hcA, ?_⟩
  rw [e2, map_smul, smul_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_rev]

end GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.BigOn.Exp.TupLe


end GlobalTheory.BigOn.Exp.TupLe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigRank
noncomputable section

open AlgebraicGeometry NumberField
open scoped Matrix

namespace GlobalTheory.BalProj

def eigSp {O k : Type} [Field k] {n : ℕ} (B : O → Matrix (Fin n) (Fin n) k) (χ : O → k) :
    Submodule k (Fin n → k) where
  carrier := {c | ∀ a, c ᵥ* B a = χ a • c}
  zero_mem' := fun a => by simp
  add_mem' := fun {c d} hc hd a => by rw [Matrix.add_vecMul, hc a, hd a, smul_add]
  smul_mem' := fun r c hc a => by rw [Matrix.smul_vecMul, hc a, smul_comm]

def eigRank {O R k : Type} [CommRing R] [Field k] (φ : R →+* k) {n : ℕ} (A : O → Matrix (Fin n) (Fin n) R)
    (χ : O → R) : ℕ :=
  Module.finrank k (eigSp (fun a => (A a).map φ) (fun a => φ (χ a)))

def embR {E : Type} [Field E] (F : IntermediateField ℚ ℂ) (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) {R : Type}
    [CommRing R] (ι : F →+* R) (τ : E →+* ℂ) (a : 𝓞 E) : R :=
  ι ⟨τ (a : E), hF τ a⟩

def fnHom {K : Type} [CommRing K] {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) : K →+* Γ(X, U) :=
  (s.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

end GlobalTheory.BalProj
end
end

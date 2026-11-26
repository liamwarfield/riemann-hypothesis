module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ExtendByIdentitySymmFixOrth

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FamilyStatementOfAbsAndVandermonde
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma MeasureTheory

theorem deg_epsI_empty {N : ℕ} : epsI (∅ : Finset (Fin N)) = 0 := by
  funext x; simp [epsI]

theorem deg_epsI_insert {N : ℕ} (I : Finset (Fin N)) (a : Fin N) (ha : a ∉ I) :
    epsI (insert a I) = epsI I + Pi.single a 1 := by
  funext x
  by_cases hx : x = a
  · subst hx; simp [epsI, ha]
  · simp [epsI, hx]

theorem deg_hc_int {N : ℕ} {μ : Fin N → ℝ} (h : IsHCParam μ) (I : Finset (Fin N)) (x : Fin N) :
    ∃ m : ℤ, (μ + epsI I) x - ((N : ℝ) - 1) / 2 = (m : ℝ) := by
  obtain ⟨m, hm⟩ := h.2 x
  by_cases hx : x ∈ I
  · refine ⟨m + 1, ?_⟩
    simp only [Pi.add_apply, epsI, if_pos hx]
    push_cast
    linarith
  · refine ⟨m, ?_⟩
    simp only [Pi.add_apply, epsI, if_neg hx]
    linarith

theorem deg_hc_diff {N : ℕ} {μ : Fin N → ℝ} (h : IsHCParam μ) (a b : Fin N) : ∃ m : ℤ, μ a - μ b = (m : ℝ) := by
  obtain ⟨m, hm⟩ := h.2 a
  obtain ⟨m', hm'⟩ := h.2 b
  refine ⟨m - m', ?_⟩
  push_cast
  linarith

theorem deg_hc_drop {N : ℕ} {μ : Fin N → ℝ} (h : IsHCParam μ) (I : Finset (Fin N)) (a : Fin N)
    (hmax : ∀ x ∈ I, x < a) (h' : IsHCParam (μ + epsI (insert a I))) : IsHCParam (μ + epsI I) := by
  refine ⟨fun i j hij => ?_, deg_hc_int h I⟩
  have h1 := h.1 hij
  have h2 := h'.1 hij
  have ha : a ∉ I := fun hh => lt_irrefl _ (hmax a hh)
  simp only [Pi.add_apply, epsI, Finset.mem_insert] at h2 ⊢
  by_cases hja : j = a
  · subst hja
    rw [if_neg ha]
    split_ifs <;> linarith
  · by_cases hia : i = a
    · subst hia
      have hj : j ∉ I := fun hh => lt_asymm hij (hmax j hh)
      rw [if_neg ha, if_neg hj]
      linarith
    · simpa [hja, hia] using h2

theorem deg_ind_up {N : ℕ} {μ : Fin N → ℝ} (hμ : IsHCParam μ) (Pr : Finset (Fin N) → Prop) (h0 : Pr ∅)
    (hs : ∀ I a, a ∉ I → IsHCParam (μ + epsI I) → IsHCParam (μ + epsI I + Pi.single a 1) → Pr I → Pr (insert a I)) :
    ∀ I, IsHCParam (μ + epsI I) → Pr I := by
  intro I
  induction I using Finset.induction_on_max with
  | empty => intro _; exact h0
  | insert a I hmax ih =>
    intro h'
    have ha : a ∉ I := fun hh => lt_irrefl _ (hmax a hh)
    have h1 := deg_hc_drop hμ I a hmax h'
    refine hs I a ha h1 ?_ (ih h1)
    rw [add_assoc, ← deg_epsI_insert I a ha]
    exact h'

theorem deg_fdeg_pos {N : ℕ} {μ : Fin N → ℝ} (h : IsHCParam μ) : 0 < fdegHC μ := by
  unfold fdegHC
  apply div_pos
  · exact Finset.prod_pos fun a _ => Finset.prod_pos fun b hb =>
      abs_pos.2 (sub_ne_zero.2 (h.1 (Finset.mem_filter.1 hb).2).ne')
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    have h1 : a.1 < b.1 := (Finset.mem_filter.1 hb).2
    have h2 : (a.1 : ℝ) < b.1 := by exact_mod_cast h1
    linarith

theorem deg_set_bound {N : ℕ} {μ : Fin N → ℝ} (hμ : IsHCParam μ) : ∀ I : Finset (Fin N), IsHCParam (μ + epsI I) →
    ((N : ℝ) ^ I.card)⁻¹ ≤ fdegHC (μ + epsI I) / fdegHC μ ∧ fdegHC (μ + epsI I) / fdegHC μ ≤ (N : ℝ) ^ I.card := by
  have h0 := deg_fdeg_pos hμ
  refine deg_ind_up hμ _ ?_ ?_
  · rw [deg_epsI_empty, add_zero, div_self h0.ne']
    simp
  · intro I a ha h1 h2 ih
    obtain ⟨ihl, ihu⟩ := ih
    have hr := Formalism.QuantumDeterminants.fdegRatio N (μ + epsI I) a h1.1.injective (deg_hc_diff h1) h2.1.injective
    have hb := (Formalism.HermitianLatticeCounting.Final.ExpansionTerms.degStepBound N (μ + epsI I) a h1.1.injective (deg_hc_diff h1)).1 h2.1.injective
    rw [← hr] at hb
    have hN : (0 : ℝ) < N := by
      have : 0 < N := lt_of_le_of_lt (Nat.zero_le _) a.2
      exact_mod_cast this
    have hp1 := deg_fdeg_pos h1
    have e : fdegHC (μ + epsI I + Pi.single a 1) / fdegHC μ =
        (fdegHC (μ + epsI I) / fdegHC μ) * (fdegHC (μ + epsI I + Pi.single a 1) / fdegHC (μ + epsI I)) := by
      field_simp
    rw [deg_epsI_insert I a ha, ← add_assoc, Finset.card_insert_of_notMem ha, pow_succ, e, mul_inv]
    have hq : 0 ≤ fdegHC (μ + epsI I) / fdegHC μ := (div_pos hp1 h0).le
    constructor
    · refine mul_le_mul ihl ?_ (by positivity) hq
      rw [← one_div]; exact hb.1
    · exact mul_le_mul ihu hb.2 (le_trans (by positivity) hb.1) (by positivity)

theorem deg_set_bound' {N : ℕ} {μ : Fin N → ℝ} (hμ : IsHCParam μ) (I : Finset (Fin N)) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (h' : IsHCParam (μ + s • epsI I)) :
    ((N : ℝ) ^ I.card)⁻¹ ≤ fdegHC (μ + s • epsI I) / fdegHC μ ∧ fdegHC (μ + s • epsI I) / fdegHC μ ≤ (N : ℝ) ^ I.card := by
  rcases hs with rfl | rfl
  · rw [one_smul] at h' ⊢
    exact deg_set_bound hμ I h'
  · have e : μ + (-1 : ℝ) • epsI I + epsI I = μ := by
      rw [neg_one_smul, neg_add_cancel_right]
    have h := deg_set_bound h' I (by rw [e]; exact hμ)
    rw [e] at h
    have h0 := deg_fdeg_pos hμ
    have h1 := deg_fdeg_pos h'
    have hx : 0 < fdegHC μ / fdegHC (μ + (-1 : ℝ) • epsI I) := div_pos h0 h1
    rw [← inv_div (fdegHC μ) (fdegHC (μ + (-1 : ℝ) • epsI I))]
    refine ⟨inv_anti₀ hx h.2, ?_⟩
    have h5 := inv_anti₀ (lt_of_lt_of_le (by
      have := hx
      exact inv_pos.2 (lt_of_lt_of_le hx h.2)) le_rfl) h.1
    rwa [inv_inv] at h5

def deg_VandLine (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A : LocS W, GoodS D lam' A →
      ∀ (I : Finset (Fin (2 * D.R.rS + D.R.k + 1))) (s : ℝ), (s = 1 ∨ s = -1) →
        ∀ A' : LocS W, GoodS D (lam' + s • epsI I) A' →
          A'.deg / A.deg = fdegHC (lam' + s • epsI I) / fdegHC lam'

theorem deg_cast_r (D : D7) : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ) := by rw [dimS_eq]

theorem degree_ratio_one_of_vandermonde (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 : ℝ)
    (h : deg_VandLine D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1) : DegreeRatioUnitShiftBound D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 1 := by
  intro hH τ w w' hTT θ hθ W hW lam' hl A hA I s hs A' hA'
  rw [h hH τ w w' hTT θ hθ W hW lam' hl A hA I s hs A' hA', one_mul, Real.rpow_natCast, ← deg_cast_r]
  exact (deg_set_bound' hA.1 I s hs hA'.1).2

section Fam

variable {eps : ℝ} (Fm : FamP eps)

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.LiftsConjugateUnderStabilizer
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfIsoAutCountGenus
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Tr

variable (D : D7)

theorem gmap_inf_cayley_degree_nondegeneracy {V : Type} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    [IsScalarTower (𝓞 D.host.E) D.host.E V] (g : V ≃ₗ[D.host.E] V) (A B : Submodule (𝓞 D.host.E) V) :
    gmap g (A ⊓ B) = gmap g A ⊓ gmap g B := by
  ext x
  simp only [isomAct_mem_gmap, Submodule.mem_inf]

theorem gmap_sup_cayley_degree_nondegeneracy {V : Type} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    [IsScalarTower (𝓞 D.host.E) D.host.E V] (g : V ≃ₗ[D.host.E] V) (A B : Submodule (𝓞 D.host.E) V) :
    gmap g (A ⊔ B) = gmap g A ⊔ gmap g B := Submodule.map_sup _ _ _

variable {D}

theorem isLattice_gmap_of_flag_isometry {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hσ : σ ∈ isom (VS D).hT) (hX : ∀ x ∈ F0.X, σ.symm x = x) (hz : σ.symm F0.z = F0.z) (Λ : LatV D)
    (hΛ : IsRowLat D F0 Λ) :
    IsRowLat D F0 (gmap σ Λ) ∧ Lsub (gmap σ Λ) (lf D F0) = gmap σ (Lsub Λ (lf D F0)) := by
  have hσ' : ∀ x y, (VS D).hT (σ x) (σ y) = (VS D).hT x y := hσ
  have hgX : gmap σ (toO (hS D) F0.X) = toO (hS D) F0.X := by
    ext x
    rw [isomAct_mem_gmap]
    constructor
    · intro h
      have h' : σ.symm x ∈ F0.X := h
      have := hX _ h'
      have e : σ.symm x = x := by
        apply σ.symm.injective
        exact this
      rw [e] at h
      exact h
    · intro h
      have h' : x ∈ F0.X := h
      rw [hX x h']
      exact h
  have hgO : gmap σ (toO (hS D) (orth (hS D) F0.X)) = toO (hS D) (orth (hS D) F0.X) := by
    ext y
    rw [isomAct_mem_gmap]
    change σ.symm y ∈ orth (hS D) F0.X ↔ y ∈ orth (hS D) F0.X
    rw [Formalism.MainNotions.mem_orth_iff, Formalism.MainNotions.mem_orth_iff]
    refine forall₂_congr fun x hx => ?_
    rw [← hσ' x (σ.symm y), LinearEquiv.apply_symm_apply]
    have : σ x = x := by
      rw [← LinearEquiv.eq_symm_apply, hX x hx]
    rw [this]
  have hXLam : XLam (gmap σ Λ) (lf D F0) = XLam Λ (lf D F0) := by
    have h1 : XLam (gmap σ Λ) (lf D F0) = gmap σ (XLam Λ (lf D F0)) := by
      unfold XLam
      rw [gmap_inf_cayley_degree_nondegeneracy]
      change gmap σ Λ ⊓ toO (hS D) F0.X = gmap σ Λ ⊓ gmap σ (toO (hS D) F0.X)
      rw [hgX]
    rw [h1]
    ext x
    rw [isomAct_mem_gmap]
    constructor
    · intro h
      have h' : σ.symm x ∈ F0.X := h.2
      have e : σ.symm x = x := σ.symm.injective (hX _ h')
      rw [e] at h
      exact h
    · intro h
      have h' : x ∈ F0.X := h.2
      rw [hX x h']
      exact h
  have hLsub : Lsub (gmap σ Λ) (lf D F0) = gmap σ (Lsub Λ (lf D F0)) := by
    unfold Lsub Lrep
    rw [gmap_inf_cayley_degree_nondegeneracy, gmap_sup_cayley_degree_nondegeneracy, gmap_inf_cayley_degree_nondegeneracy]
    change (gmap σ Λ ⊓ toO (hS D) (orth (hS D) F0.X) ⊔ toO (hS D) F0.X) ⊓ toO (hS D) (orth (hS D) F0.X) =
      (gmap σ Λ ⊓ gmap σ (toO (hS D) (orth (hS D) F0.X)) ⊔ gmap σ (toO (hS D) F0.X)) ⊓
        gmap σ (toO (hS D) (orth (hS D) F0.X))
    rw [hgX, hgO]
  refine ⟨?_, hLsub⟩
  obtain ⟨⟨hlat1, hgen1⟩, ⟨hL, hU, hLift, hConv⟩, hXS⟩ := hΛ
  obtain ⟨_, hloc, _, huni, _⟩ := isomAct (𝓞 D.host.E) D.host.E (VS D).V (VS D).hT σ hσ Λ
  have hfull : Submodule.IsFullLattice D.host.E (gmap σ Λ) := by
    refine { toIsLattice := isomAct_lattice σ Λ hlat1.toIsLattice, span_eq_top := ?_ }
    change Submodule.span D.host.E ((σ : (VS D).V →ₗ[D.host.E] (VS D).V) '' (Λ : Set (VS D).V)) = ⊤
    rw [Submodule.span_image, hlat1.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact σ.surjective
  refine ⟨⟨hfull, fun p hp => ?_⟩,
    ⟨isomAct_lattice σ Λ hL, huni.2 hU, ⟨?_, hLift.2⟩, ?_, fun c hc => hConv.2 c ?_⟩, hXLam.trans hXS⟩
  · obtain ⟨g, hg, e⟩ := hgen1 p hp
    exact ⟨σ * g, (isom (VS D).hT).mul_mem hσ hg, by rw [gmap_mul, e, hloc p]⟩
  · rw [isomAct_mem_gmap]
    change σ.symm F0.z ∈ Λ
    rw [hz]
    exact hLift.1
  · rw [hXLam]
    exact hConv.1
  · rw [hLsub, isomAct_mem_gmap, map_smul] at hc
    change c • σ.symm F0.z ∈ _ at hc
    rw [hz] at hc
    exact hc

variable (D)

theorem isometries_transport_lattices (u : D.what₂.Word) : IsometriesTransportLattices D u := by
  intro _ _ _ F0 he hz γ hγ Λ₁ hΛ₁
  have hzO : F0.z ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0)) := by
    rw [Formalism.MainNotions.mem_orth_iff]
    rintro _ ⟨w, rfl⟩
    rw [hz]
    exact Formalism.MainNotions.hT_swap_zero (z_orth_embedding D u w)
  have hXO : F0.X ≤ orth (hS D) (LinearMap.range (D.sp.iXY 0)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    rw [he]
    change D.sp.hypE a ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))
    rw [Formalism.MainNotions.mem_orth_iff]
    rintro _ ⟨w, rfl⟩
    exact (D.sp.hyp_orthX a w).1
  obtain ⟨hrow, hLsub⟩ := isLattice_gmap_of_flag_isometry F0 (extendByIdentity D γ) (extendByIdentity_mem_isom D γ hγ)
    (fun x hx => extendByIdentity_symm_fix_orth D γ x (hXO hx)) (extendByIdentity_symm_fix_orth D γ _ hzO) Λ₁ hΛ₁
  refine ⟨gmap (extendByIdentity D γ) Λ₁, hrow, ?_⟩
  ext ⟨w, c⟩
  unfold latticeWithZ
  rw [Submodule.mem_comap, hLsub, isomAct_mem_gmap, isomAct_mem_gmap, Submodule.mem_comap]
  have e1 : ((embedWithZ D F0).restrictScalars (𝓞 D.host.E)) (w, c) = D.sp.iXY 0 w + c • F0.z := by
    simp [embedWithZ]
  have e2 : ((embedWithZ D F0).restrictScalars (𝓞 D.host.E)) ((extendByOne D γ).symm (w, c)) =
      D.sp.iXY 0 (γ.symm w) + c • F0.z := by
    have : (extendByOne D γ).symm (w, c) = (γ.symm w, c) := rfl
    rw [this]
    simp [embedWithZ]
  rw [e1, e2, extendByIdentity_symm_apply D γ w _ (Submodule.smul_mem _ c hzO)]

theorem gluing_mass_of_iso_aut_count_genus (u : D.what₂.Word) (hpos : IsPosDef (D.sp.X 0).hT)
    (hlat : ForPrimeFlagLattice D u fun F0 Λ => Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)))
    (h1 : LatticeClassesIff D u) (h2 : CardAutEqCardIsometryStabilizer D u) (h4 : GluingCount D u)
    (h5 : OrthLatticesOneGenus D u) : WordRowsGluing D u :=
  gluing_mass_of_gluing_facts D u hpos hlat h1 h2 (isometries_transport_lattices D u) h4 h5

end Tr

end Formalism.MainNotions.BridgeLemma₂

end
end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LiftsConjugateUnderStabilizer (D : D7) (u : D.what₂.Word) : Prop :=
  ForPrimeFlag D u fun F0 => ∀ Λ₁ Λ₂ : LatV D, IsRowLat D F0 Λ₁ → IsRowLat D F0 Λ₂ →
    Lsub Λ₁ (lf D F0) = Lsub Λ₂ (lf D F0) →
    ∃ n ∈ stabF D F0, (∀ x ∈ orth (hS D) F0.X, n x - x ∈ F0.X) ∧ gmap n Λ₁ = Λ₂

section Cl

variable {D : D7}

theorem partial_isotropic_top {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : F0.Xa D.R.rS = F0.X := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext x
  simp

theorem partial_isotropic_le {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (j : ℕ) : F0.Xa j ≤ F0.X :=
  Submodule.span_mono (Set.image_subset_range _ _)

theorem isotropic_le_orth_isotropic {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : F0.X ≤ orth (hS D) F0.X := by
  intro y hy
  rw [Formalism.MainNotions.mem_orth_iff]
  intro x hx
  exact Formalism.MainNotions.hT_swap_zero (Formalism.MainNotions.hT_zero_of_mem_X F0
    (fun a => Formalism.MainNotions.hT_swap_zero (Formalism.MainNotions.hT_zero_of_mem_X F0 (fun b => F0.e_iso b a) x hx)) y hy)

theorem isotropic_le_Lsub {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LatV D) :
    toO (hS D) F0.X ≤ Lsub Λ (lf D F0) :=
  le_inf le_sup_right (fun _ hx => isotropic_le_orth_isotropic F0 hx)

theorem Lsub_gmap_of_isometry {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hσ : σ ∈ isom (VS D).hT) (hX : F0.X.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X) (Λ : LatV D) :
    Lsub (gmap σ Λ) (lf D F0) = gmap σ (Lsub Λ (lf D F0)) := by
  have hσ' : ∀ x y, (VS D).hT (σ x) (σ y) = (VS D).hT x y := hσ
  have hmem : ∀ x, σ.symm x ∈ F0.X ↔ x ∈ F0.X := by
    intro x
    conv_rhs => rw [← hX]
    rw [Submodule.mem_map_equiv]
  have hgX : gmap σ (toO (hS D) F0.X) = toO (hS D) F0.X := by
    ext x
    rw [isomAct_mem_gmap]
    exact hmem x
  have hgO : gmap σ (toO (hS D) (orth (hS D) F0.X)) = toO (hS D) (orth (hS D) F0.X) := by
    ext y
    rw [isomAct_mem_gmap]
    change σ.symm y ∈ orth (hS D) F0.X ↔ y ∈ orth (hS D) F0.X
    rw [Formalism.MainNotions.mem_orth_iff, Formalism.MainNotions.mem_orth_iff]
    constructor
    · intro h x hx
      have := h (σ.symm x) ((hmem x).2 hx)
      rwa [← hσ' (σ.symm x) (σ.symm y), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
    · intro h x hx
      have hx' : σ x ∈ F0.X := by
        rw [← hmem, LinearEquiv.symm_apply_apply]
        exact hx
      have := h (σ x) hx'
      rwa [← hσ' x (σ.symm y), LinearEquiv.apply_symm_apply]
  unfold Lsub Lrep
  rw [gmap_inf_cayley_degree_nondegeneracy, gmap_sup_cayley_degree_nondegeneracy, gmap_inf_cayley_degree_nondegeneracy]
  change (gmap σ Λ ⊓ toO (hS D) (orth (hS D) F0.X) ⊔ toO (hS D) F0.X) ⊓ toO (hS D) (orth (hS D) F0.X) =
    (gmap σ Λ ⊓ gmap σ (toO (hS D) (orth (hS D) F0.X)) ⊔ gmap σ (toO (hS D) F0.X)) ⊓
      gmap σ (toO (hS D) (orth (hS D) F0.X))
  rw [hgX, hgO]

theorem mul_mem_flag_stabilizer {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {a b : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (ha : a ∈ stabF D F0) (hb : b ∈ stabF D F0) : a * b ∈ stabF D F0 := by
  refine ⟨(isom (VS D).hT).mul_mem ha.1 hb.1, fun j => ?_, ?_⟩
  · have e : ((a * b : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) =
        (a : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ (b : (VS D).V →ₗ[D.host.E] (VS D).V) := rfl
    rw [e, Submodule.map_comp, hb.2.1 j, ha.2.1 j]
  · change a (b F0.z) = F0.z
    rw [hb.2.2, ha.2.2]

end Cl

end Formalism.MainNotions.BridgeLemma₂

end
end

module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.AvNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingMultiplicative
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfEigencharacter
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSemidefiniteNullRadical
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaussianDualMeasure.SecondCountableTopologyAndT2Space

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSubgroupRelIndexMul
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSubgroupRelIndexMul
open Matrix
open scoped Topology

namespace GlobalTheory.CompanionTheory.HaarIndex

theorem measure_eq_relIndex_mul : ∀ (G : Type) [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : MeasureTheory.Measure G) [μ.IsAddLeftInvariant] (H K : AddSubgroup G), H ≤ K →
    MeasurableSet (H : Set G) → H.relIndex K ≠ 0 →
    μ (K : Set G) = (H.relIndex K : ENNReal) * μ (H : Set G) := by
  intro G _ _ _ μ _ H K hHK hH hn
  classical
  set H' := H.addSubgroupOf K
  have hidx : H.relIndex K = H'.index := rfl
  have : H'.FiniteIndex := ⟨by rw [← hidx]; exact hn⟩
  have : Finite (K ⧸ H') := inferInstance
  letI := Fintype.ofFinite (K ⧸ H')
  let o : K ⧸ H' → G := fun q => ((Quotient.out q : K) : G)
  let S : K ⧸ H' → Set G := fun q => (fun x => -o q + x) ⁻¹' (H : Set G)
  have hS : ∀ q, MeasurableSet (S q) := fun q => (measurable_const_add (-o q)) hH
  have hcover : (K : Set G) = ⋃ q, S q := by
    ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hx
      refine ⟨((⟨x, hx⟩ : K) : K ⧸ H'), ?_⟩
      have h1 := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' ((⟨x, hx⟩ : K) : K ⧸ H'))
      rw [AddSubgroup.mem_addSubgroupOf] at h1
      simpa [S, o] using h1
    · rintro ⟨q, hq⟩
      have hq' : -o q + x ∈ H := hq
      have hoK : o q ∈ K := (Quotient.out q).2
      have hx : x = o q + (-o q + x) := (add_neg_cancel_left (o q) x).symm
      rw [hx]
      exact K.add_mem hoK (hHK hq')
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro q r hqr
    rw [Function.onFun, Set.disjoint_left]
    intro x hxq hxr
    apply hqr
    have hq' : -o q + x ∈ H := hxq
    have hr' : -o r + x ∈ H := hxr
    have h2 : -o q + o r ∈ H := by
      have := H.add_mem hq' (H.neg_mem hr')
      simpa [neg_add_rev, add_assoc] using this
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' r]
    apply QuotientAddGroup.eq.mpr
    rw [AddSubgroup.mem_addSubgroupOf]
    simpa [o] using h2
  have hμ : ∀ q, μ (S q) = μ (H : Set G) := fun q => MeasureTheory.measure_preimage_add μ (-o q) _
  rw [hcover, MeasureTheory.measure_iUnion hdisj hS, tsum_fintype]
  simp only [hμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hidx, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]

end GlobalTheory.CompanionTheory.HaarIndex
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSubgroupRelIndexMulStatement
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_subgroup_relIndex_mul : ∀ (G : Type) [AddGroup G] [MeasurableSpace G] [MeasurableAdd G] (μ : MeasureTheory.Measure G) [μ.IsAddLeftInvariant] (H K : AddSubgroup G), H ≤ K → MeasurableSet (H : Set G) → H.relIndex K ≠ 0 → μ (K : Set G) = (H.relIndex K : ENNReal) * μ (H : Set G) := by
  first | exact @GlobalTheory.CompanionTheory.HaarIndex.measure_eq_relIndex_mul | exact GlobalTheory.CompanionTheory.HaarIndex.measure_eq_relIndex_mul | (intros; apply GlobalTheory.CompanionTheory.HaarIndex.measure_eq_relIndex_mul <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeAnnihilatorWithinNhds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeAnnihilatorWithinNhds
open Matrix ValuativeRel
open scoped Topology

noncomputable section
namespace GlobalTheory.CompanionTheory.AnnihShrink

theorem exists_ne_zero_valuation_lt (k : Type) [Field k] [ValuativeRel k] [ValuativeRel.IsNontrivial k]
    (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) : ∃ t : k, t ≠ 0 ∧ valuation k t < γ := by
  obtain ⟨γ₀, h0, h1⟩ := ValuativeRel.IsNontrivial.condition (R := k)
  obtain ⟨ε, hε0, hε1⟩ : ∃ ε : ValueGroupWithZero k, ε ≠ 0 ∧ ε < 1 := by
    rcases lt_or_gt_of_ne h1 with h | h
    · exact ⟨γ₀, h0, h⟩
    · exact ⟨γ₀⁻¹, inv_ne_zero h0, inv_lt_one_of_one_lt₀ h⟩
  obtain ⟨t, ht⟩ := valuation_surjective (K := k) (ε * γ)
  have hpos : 0 < γ := zero_lt_iff.mpr hγ
  refine ⟨t, ?_, ?_⟩
  · rw [← (valuation k).ne_zero_iff, ht]
    exact mul_ne_zero hε0 hγ
  · rw [ht]
    exact mul_lt_of_lt_one_left hpos hε1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (n : ℕ) (b : k) : AddSubgroup (Fin n → k) where
  carrier := {a | ∀ j, valuation k (a j) ≤ valuation k b}
  zero_mem' := fun j => by simp
  add_mem' := fun {x y} hx hy j =>
    ((valuation k).map_add _ _).trans (max_le (hx j) (hy j))
  neg_mem' := fun {x} hx j => by simpa using hx j

theorem isCompact_box (n : ℕ) (b : k) : IsCompact (box n b : Set (Fin n → k)) := by
  have : (box n b : Set (Fin n → k)) =
      Set.univ.pi (fun _ => {y : k | valuation k y ≤ valuation k b}) := by
    ext a
    exact ⟨fun h j _ => h j, fun h j => h j (Set.mem_univ j)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _

theorem isOpen_box (n : ℕ) (b : k) (hb : b ≠ 0) : IsOpen (box n b : Set (Fin n → k)) := by
  have hvb : valuation k b ≠ 0 := (Valuation.ne_zero_iff _).2 hb
  have hU : Set.univ.pi (fun _ : Fin n => {y : k | valuation k y < valuation k b}) ∈
      nhds (0 : Fin n → k) :=
    set_pi_mem_nhds Set.finite_univ fun j _ =>
      (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem hvb
  refine (box n b).isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset hU ?_)
  intro x hx j
  exact (hx j (Set.mem_univ j)).le

theorem exists_compact_open_annihilator_subset :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (U : Set (Fin n → k)),
      U ∈ nhds (0 : Fin n → k) → ∃ A : AddSubgroup (Fin n → k),
        IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧
        {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} ⊆ U := by
  intro k _ _ _ _ ψ _ hne n U hU
  obtain ⟨y₀, hy⟩ : ∃ y : k, ψ y ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hne (AddChar.ext _ _ fun t => by simpa using hall t)
  have hy0 : y₀ ≠ 0 := by
    rintro rfl
    exact hy (by simp)

  obtain ⟨I, V, hV, hIV⟩ : ∃ (I : Set (Fin n)) (V : Fin n → Set k),
      (∀ i, V i ∈ nhds (0 : k)) ∧ I.pi V ⊆ U := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, _, V, hV, hIV⟩ := hU
    exact ⟨I, V, hV, hIV⟩
  have hball : ∀ i, ∃ γ : (ValueGroupWithZero k)ˣ, {y : k | valuation k y < γ} ⊆ V i := fun i =>
    (IsValuativeTopology.mem_nhds_zero_iff (V i)).1 (hV i)
  choose g hg using hball
  obtain ⟨γ, hγ0, hγ⟩ : ∃ γ : ValueGroupWithZero k, γ ≠ 0 ∧ ∀ i, γ ≤ (g i : ValueGroupWithZero k) := by
    obtain ⟨m, hm⟩ := Finite.exists_ge g
    exact ⟨m, m.ne_zero, fun i => Units.val_le_val.2 (hm i)⟩
  obtain ⟨t, ht0, ht⟩ := exists_ne_zero_valuation_lt k γ hγ0
  refine ⟨box n (y₀ / t), isCompact_box n _, isOpen_box n _ (div_ne_zero hy0 ht0), ?_⟩
  intro ξ hξ
  apply hIV
  intro i _
  apply hg i
  show valuation k (ξ i) < g i
  refine lt_of_lt_of_le ?_ (hγ i)
  by_contra hlt
  have hle : γ ≤ valuation k (ξ i) := not_lt.mp hlt
  have hvξ : valuation k (ξ i) ≠ 0 := (lt_of_lt_of_le (zero_lt_iff.mpr hγ0) hle).ne'
  have hξi : ξ i ≠ 0 := (Valuation.ne_zero_iff _).1 hvξ
  have hmem : (Pi.single i (y₀ / ξ i) : Fin n → k) ∈ box n (y₀ / t) := by
    intro j
    by_cases h : j = i
    · subst h
      have he : y₀ / ξ j = (y₀ / t) * (t / ξ j) := by field_simp
      rw [Pi.single_eq_same, he, map_mul]
      refine mul_le_of_le_one_right' ?_
      rw [map_div₀]
      exact (div_le_one₀ (zero_lt_iff.mpr hvξ)).2 (ht.le.trans hle)
    · simp [Pi.single_eq_of_ne h]
  have h1 := hξ _ hmem
  rw [dotProduct_single, mul_div_cancel₀ _ hξi] at h1
  exact hy h1

end GlobalTheory.CompanionTheory.AnnihShrink
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeAnnihilatorWithinNhdsStatement
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_annihilator_within_nhds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (U : Set (Fin n → k)), U ∈ nhds (0 : Fin n → k) → ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧ {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} ⊆ U := by
  first | exact @GlobalTheory.CompanionTheory.AnnihShrink.exists_compact_open_annihilator_subset | exact GlobalTheory.CompanionTheory.AnnihShrink.exists_compact_open_annihilator_subset | (intros; apply GlobalTheory.CompanionTheory.AnnihShrink.exists_compact_open_annihilator_subset <;> assumption)
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.MeasurableSpaceSecondLift
noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitWeil GlobalTheory.BZMir Filter
open scoped Topology ENNReal NNReal

namespace PositivityTheory.RgUd.Form.U.Lift2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Lattices

variable (ψ : AddChar k Circle) {n : ℕ}

theorem perp_open (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {A : AddSubgroup (Fin n → k)} (hA : Lat A) :
    IsOpen (perp ψ A : Set (Fin n → k)) := (GlobalTheory.T.annihilator_open_compact k ψ hψ hψ1 n A hA.1 hA.2).1

theorem perp_compact (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {A : AddSubgroup (Fin n → k)} (hA : Lat A) :
    IsCompact (perp ψ A : Set (Fin n → k)) := (GlobalTheory.T.annihilator_open_compact k ψ hψ hψ1 n A hA.1 hA.2).2

theorem perp_anti {A A' : AddSubgroup (Fin n → k)} (h : A ≤ A') : perp ψ A' ≤ perp ψ A :=
  fun _ hξ a ha => hξ a (h ha)

theorem perp_relIndex (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {A₀ A : AddSubgroup (Fin n → k)} (h₀ : Lat A₀) (h : Lat A)
    (hle : A₀ ≤ A) : (perp ψ A).relIndex (perp ψ A₀) = A₀.relIndex A :=
  GlobalTheory.T.relIndex_annihilators_duality k ψ hψ hψ1 n A₀ A (perp ψ A₀) (perp ψ A) h₀.1 h₀.2 h.1 h.2 hle (fun _ => Iff.rfl) (fun _ => Iff.rfl)

theorem relIndex_ne_zero_of_lat {A₀ A : AddSubgroup (Fin n → k)} (h₀ : Lat A₀) (h : Lat A) : A₀.relIndex A ≠ 0 := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp h.1
  have ho : IsOpen ((A₀.addSubgroupOf A : AddSubgroup A) : Set A) := h₀.2.preimage continuous_subtype_val
  haveI := AddSubgroup.quotient_finite_of_isOpen (A₀.addSubgroupOf A) ho
  exact AddSubgroup.index_ne_zero_of_finite

theorem lat_over {K : Set (Fin n → k)} (hK : IsCompact K) : ∃ A : AddSubgroup (Fin n → k), Lat A ∧ K ⊆ A := by
  obtain ⟨A, h1, h2, h3⟩ := GlobalTheory.T.exists_open_compact_lattice_containing k n K hK
  exact ⟨A, ⟨h1, h2⟩, h3⟩

theorem lat_shrink (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {U : Set (Fin n → k)} (hU : U ∈ 𝓝 (0 : Fin n → k)) :
    ∃ A : AddSubgroup (Fin n → k), Lat A ∧ (perp ψ A : Set _) ⊆ U := by
  obtain ⟨A, h1, h2, h3⟩ := GlobalTheory.T.lattice_annihilator_within_nhds k ψ hψ hψ1 n U hU
  exact ⟨A, ⟨h1, h2⟩, h3⟩

theorem lat_sup {A A' : AddSubgroup (Fin n → k)} (h : Lat A) (h' : Lat A') : ∃ A'', Lat A'' ∧ A ≤ A'' ∧ A' ≤ A'' := by
  obtain ⟨B, hB, hB'⟩ := lat_over (h.1.union h'.1)
  exact ⟨B, hB, fun x hx => hB' (Or.inl hx), fun x hx => hB' (Or.inr hx)⟩

end Lattices

section Forms

variable {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

abbrev md (g : GL (Fin (m + 1)) k) : ℝ := nabs k (Matrix.GeneralLinearGroup.det g)

theorem md_pos (g : GL (Fin (m + 1)) k) : 0 < md g := NNReal.coe_pos.mpr distribHaarChar_pos

theorem md_mul (g h : GL (Fin (m + 1)) k) : md (g * h) = md g * md h := by
  simp [md, nabs, map_mul]

theorem md_inv (g : GL (Fin (m + 1)) k) : md g⁻¹ = (md g)⁻¹ := by
  simp [md, nabs, map_inv]

theorem md_one : md (1 : GL (Fin (m + 1)) k) = 1 := by
  simp [md, nabs]

theorem xz_eq (m : ℕ) : (xz m : Fin (m + 1) → k) = eLast k m := rfl

variable (gl : GL (Fin (m + 1)) k →* (V →ₗ[ℂ] V)) (s : ℝ) (C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)

def Ct (g : GL (Fin (m + 1)) k) : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ :=
  (((md g ^ (s + 1) : ℝ) : ℂ)) • (C.compl₂ (gl g⁻¹)).comp (gl g⁻¹)

theorem Ct_apply (g : GL (Fin (m + 1)) k) (v w : V) :
    Ct gl s C g v w = ((md g ^ (s + 1) : ℝ) : ℂ) * C (gl g⁻¹ v) (gl g⁻¹ w) := by
  simp [Ct]


open Classical in
def sect (ξ : Fin (m + 1) → k) : GL (Fin (m + 1)) k :=
  if h : ξ = 0 then 1 else (Classical.choose (GlobalTheory.T.exists_GL_last_basis_vecMul_eq k m ξ h))⁻¹

theorem sect_spec {ξ : Fin (m + 1) → k} (h : ξ ≠ 0) :
    xz m ᵥ* (((sect ξ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := by
  rw [sect, dite_eq_right h, inv_inv]
  exact Classical.choose_spec (GlobalTheory.T.exists_GL_last_basis_vecMul_eq k m ξ h)


open Classical in
def Df (ξ : Fin (m + 1) → k) : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := if ξ = 0 then 0 else Ct gl s C (sect ξ)

theorem Df_zero : Df gl s C (0 : Fin (m + 1) → k) = 0 := by
  simp [Df]

variable {gl s C}

theorem Ct_congr (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w)
    {g h : GL (Fin (m + 1)) k}
    (hgh : xz m ᵥ* ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      xz m ᵥ* ((h⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) :
    Ct gl s C g = Ct gl s C h := by
  set p := h⁻¹ * g with hp_def
  have hp : p⁻¹ ∈ Mir k m := by
    show vecMul (eLast k m) ((p⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = eLast k m
    rw [hp_def, _root_.mul_inv_rev, inv_inv, Units.val_mul, ← vecMul_vecMul, ← xz_eq, hgh, vecMul_vecMul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, vecMul_one]
  have hg : g = h * p := by rw [hp_def, mul_inv_cancel_left]
  have hgi : g⁻¹ = p⁻¹ * h⁻¹ := by rw [hg, _root_.mul_inv_rev]
  refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
  rw [Ct_apply, Ct_apply, hgi, map_mul, Module.End.mul_apply, Module.End.mul_apply, hC _ hp, ← mul_assoc]
  congr 1
  rw [hg, md_mul, md_inv, ← Complex.ofReal_mul, Real.mul_rpow (md_pos h).le (md_pos p).le,
    Real.inv_rpow (md_pos p).le, mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos (md_pos p) _).ne', mul_one]

theorem Df_eq (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w)
    {ξ : Fin (m + 1) → k} (hξ : ξ ≠ 0) {g : GL (Fin (m + 1)) k}
    (hg : xz m ᵥ* ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ) :
    Df gl s C ξ = Ct gl s C g := by
  rw [Df, if_neg hξ]
  exact Ct_congr hC ((sect_spec hξ).trans hg.symm)

theorem Df_xz (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w) (v w : V) :
    Df gl s C (xz m) v w = C v w := by
  have h0 : (xz m : Fin (m + 1) → k) ≠ 0 := by
    intro h
    have := congrFun h (Fin.last m)
    simp [xz] at this
  rw [Df_eq hC h0 (g := 1) (by simp), Ct_apply]
  simp [md_one]

end Forms

section Forms2

variable {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {ψ : AddChar k Circle}
  {col : (Fin (m + 1) → k) → V →ₗ[ℂ] V} {gl : GL (Fin (m + 1)) k →* (V →ₗ[ℂ] V)} {s : ℝ} {C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

theorem circ_mul_conj (z : Circle) : (z : ℂ) * starRingEnd ℂ (z : ℂ) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
  norm_num

theorem Ct_herm (hCp : Psd C) (g : GL (Fin (m + 1)) k) (v w : V) :
    Ct gl s C g w v = starRingEnd ℂ (Ct gl s C g v w) := by
  rw [Ct_apply, Ct_apply, hCp.1, map_mul, Complex.conj_ofReal]

theorem Ct_re_nonneg (hCp : Psd C) (g : GL (Fin (m + 1)) k) (v : V) : 0 ≤ (Ct gl s C g v v).re := by
  rw [Ct_apply, Complex.re_ofReal_mul]
  exact mul_nonneg (Real.rpow_nonneg (md_pos g).le _) (hCp.2 _)

theorem Df_herm (hCp : Psd C) (ξ : Fin (m + 1) → k) (v w : V) :
    Df gl s C ξ w v = starRingEnd ℂ (Df gl s C ξ v w) := by
  by_cases h : ξ = 0
  · subst h
    simp [Df_zero]
  · simp only [Df, if_neg h]
    exact Ct_herm hCp _ _ _

theorem Df_re_nonneg (hCp : Psd C) (ξ : Fin (m + 1) → k) (v : V) : 0 ≤ (Df gl s C ξ v v).re := by
  by_cases h : ξ = 0
  · subst h
    simp [Df_zero]
  · simp only [Df, if_neg h]
    exact Ct_re_nonneg hCp _ _

theorem Ct_col (hS : Setup col gl) (hCc : ∀ x v w, C (col x v) w = ((ψ (xz m ⬝ᵥ x) : Circle) : ℂ) * C v w)
    (g : GL (Fin (m + 1)) k) (x : Fin (m + 1) → k) (v w : V) :
    Ct gl s C g (col x v) w =
      ((ψ ((xz m ᵥ* ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) ⬝ᵥ x) : Circle) : ℂ) *
        Ct gl s C g v w := by
  rw [Ct_apply, Ct_apply, hS.conj, hCc, dotProduct_mulVec]
  ring

variable (hS : Setup col gl) (hCp : Psd C)
  (hCc : ∀ x v w, C (col x v) w = ((ψ (xz m ⬝ᵥ x) : Circle) : ℂ) * C v w)
  (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w)
include hS hCc hC

theorem Df_col (ξ x : Fin (m + 1) → k) (v w : V) :
    Df gl s C ξ (col x v) w = ((ψ (ξ ⬝ᵥ x) : Circle) : ℂ) * Df gl s C ξ v w := by
  by_cases h : ξ = 0
  · subst h
    simp [Df_zero]
  · rw [Df_eq hC h (sect_spec h), Ct_col hS hCc, sect_spec h]

include hCp

theorem Df_col_right (ξ x : Fin (m + 1) → k) (v w : V) :
    Df gl s C ξ v (col x w) = starRingEnd ℂ ((ψ (ξ ⬝ᵥ x) : Circle) : ℂ) * Df gl s C ξ v w := by
  rw [Df_herm hCp, Df_col hS hCc hC, map_mul, ← Df_herm hCp]

theorem form_column_invariant (ξ x : Fin (m + 1) → k) (v w : V) : Df gl s C ξ (col x v) (col x w) = Df gl s C ξ v w := by
  rw [Df_col_right hS hCp hCc hC, Df_col hS hCc hC, ← mul_assoc, mul_comm (starRingEnd ℂ _), circ_mul_conj, one_mul]

omit hCp hCc in
theorem Df_gl {ξ : Fin (m + 1) → k} (hξ : ξ ≠ 0) (g : GL (Fin (m + 1)) k) (v w : V) :
    Df gl s C ξ (gl g v) (gl g w) =
      ((md g ^ (s + 1) : ℝ) : ℂ) * Df gl s C (ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) v w := by
  have hξg : ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ≠ 0 := by
    intro h0
    apply hξ
    have := congrArg (fun x => x ᵥ* ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) h0
    simpa [vecMul_vecMul, ← Units.val_mul] using this
  have hτ : xz m ᵥ* (((g⁻¹ * sect ξ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) := by
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← vecMul_vecMul, sect_spec hξ]
  rw [Df_eq hC hξ (sect_spec hξ), Df_eq hC hξg hτ, Ct_apply, Ct_apply, ← Module.End.mul_apply, ← Module.End.mul_apply,
    ← map_mul, _root_.mul_inv_rev (g⁻¹) (sect ξ), inv_inv, ← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  rw [md_mul, md_inv, Real.mul_rpow (inv_nonneg.mpr (md_pos g).le) (md_pos (sect ξ)).le, Real.inv_rpow (md_pos g).le,
    ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos (md_pos g) _).ne', one_mul]

omit hS hCc in
theorem Df_ker (Y : Submodule ℂ V) (hY : ∀ g, ∀ y ∈ Y, gl g y ∈ Y) (hCY : ∀ y ∈ Y, ∀ w, C y w = 0)
    (ξ : Fin (m + 1) → k) {y : V} (hy : y ∈ Y) (w : V) : Df gl s C ξ y w = 0 := by
  by_cases h : ξ = 0
  · subst h
    simp [Df_zero]
  · simp only [Df, if_neg h]
    rw [Ct_apply, hCY _ (hY _ _ hy), mul_zero]


omit hCp hCc in
theorem Df_loc {ζ : Fin (m + 1) → k} (hζ : ζ ≠ 0) (v w : V) : ∀ᶠ ξ in 𝓝 ζ, Df gl s C ξ v w = Df gl s C ζ v w := by
  obtain ⟨N, hNo, hζN, f, hf, hf1, hfN⟩ := GlobalTheory.T.local_continuous_section_vecMul_orbit k (m + 1) ζ hζ
  have hH : {h : GL (Fin (m + 1)) k | gl h v = v} ∩ {h | gl h w = w} ∩ {h | md h = 1} ∈ 𝓝 (1 : GL (Fin (m + 1)) k) := by
    refine Filter.inter_mem (Filter.inter_mem ?_ ?_) ?_
    · exact (hS.smooth_gl v).mem_nhds (by simp)
    · exact (hS.smooth_gl w).mem_nhds (by simp)
    · filter_upwards [GlobalTheory.T.eventually_haar_det_eq_one_near_one k (m + 1)] with h hh
      simp [md, nabs, hh]
  have hfc : ContinuousAt f ζ := hf.continuousAt (hNo.mem_nhds hζN)
  have hpre : f ⁻¹' ({h : GL (Fin (m + 1)) k | gl h v = v} ∩ {h | gl h w = w} ∩ {h | md h = 1}) ∈ 𝓝 ζ :=
    hfc (by rw [hf1]; exact hH)
  filter_upwards [hNo.mem_nhds hζN, hpre] with ξ hξN hξH
  obtain ⟨⟨hv, hw⟩, hd⟩ := hξH
  have hξ : ζ ᵥ* (f ξ : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := hfN ξ hξN
  have hξ0 : ξ ≠ 0 := by
    intro h0
    apply hζ
    have := congrArg (fun x => x ᵥ* (((f ξ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) (hξ.trans h0)
    simpa [vecMul_vecMul, ← Units.val_mul] using this
  have hτ : xz m ᵥ* ((((f ξ)⁻¹ * sect ζ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := by
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← vecMul_vecMul, sect_spec hζ, hξ]
  rw [Df_eq hC hξ0 hτ, Df_eq hC hζ (sect_spec hζ), Ct_apply, Ct_apply, _root_.mul_inv_rev, inv_inv, map_mul,
    Module.End.mul_apply, Module.End.mul_apply, hv, hw, md_mul, md_inv, hd, inv_one, one_mul]

end Forms2

section Meas

local instance instMeasK : MeasurableSpace k := borel k
local instance instBorelK : BorelSpace k := ⟨rfl⟩
local instance instSCK : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k

variable {m : ℕ} (ψ : AddChar k Circle) (ν : Measure (Fin (m + 1) → k)) [ν.IsAddHaarMeasure]

theorem meas_perp_index (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {A₀ A : AddSubgroup (Fin (m + 1) → k)} (h₀ : Lat A₀) (h : Lat A)
    (hle : A₀ ≤ A) : ν (perp ψ A₀) = (A₀.relIndex A : ℝ≥0∞) * ν (perp ψ A) := by
  have := GlobalTheory.T.haar_measure_subgroup_relIndex_mul (Fin (m + 1) → k) ν (perp ψ A) (perp ψ A₀) (perp_anti ψ hle)
    (perp_open ψ hψ hψ1 h).measurableSet (by rw [perp_relIndex ψ hψ hψ1 h₀ h hle]; exact relIndex_ne_zero_of_lat h₀ h)
  rw [this, perp_relIndex ψ hψ hψ1 h₀ h hle]

theorem meas_perp_lt_top (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {A : AddSubgroup (Fin (m + 1) → k)} (h : Lat A) :
    ν (perp ψ A) < ∞ := (perp_compact ψ hψ hψ1 h).measure_lt_top

theorem meas_perp_ne_zero (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {A : AddSubgroup (Fin (m + 1) → k)} (h : Lat A) :
    ν (perp ψ A) ≠ 0 := (perp_open ψ hψ hψ1 h).measure_ne_zero ν ⟨0, (perp ψ A).zero_mem⟩

def gT (g : GL (Fin (m + 1)) k) : GL (Fin (m + 1)) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵀ)
    (by rw [det_transpose]; exact (Matrix.isUnits_det_units g).ne_zero)

theorem md_gT (g : GL (Fin (m + 1)) k) : md (gT g) = md g := by
  have : Matrix.GeneralLinearGroup.det (gT g) = Matrix.GeneralLinearGroup.det g := by
    ext
    simp [gT, Matrix.GeneralLinearGroup.mkOfDetNeZero, det_transpose]
  simp only [md, this]

theorem integral_vecMul (f : (Fin (m + 1) → k) → ℂ) (g : GL (Fin (m + 1)) k) :
    ∫ ξ, f (ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) ∂ν = ((md g)⁻¹ : ℝ) * ∫ ξ, f ξ ∂ν := by
  have h := GlobalTheory.InertLagChar.haarChar_det_mul_integral_comp_mulVec_localField k (m + 1) _ BorelSpace.measurable_eq ν inferInstance (gT g) f
  have h2 : ∀ y : Fin (m + 1) → k, ((gT g : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ y =
      y ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) := by
    intro y
    simp [gT, Matrix.GeneralLinearGroup.mkOfDetNeZero, mulVec_transpose]
  simp_rw [h2] at h
  have hmd : ((distribHaarChar k (Matrix.GeneralLinearGroup.det (gT g)) : ℝ≥0) : ℝ) = md g := by
    rw [← md_gT]; rfl
  rw [← h, ← mul_assoc, ← Complex.ofReal_mul, hmd, inv_mul_cancel₀ (md_pos g).ne', Complex.ofReal_one, one_mul]

theorem perp_gmap (g : GL (Fin (m + 1)) k) (A : AddSubgroup (Fin (m + 1) → k)) (ξ : Fin (m + 1) → k) :
    ξ ∈ perp ψ (gmap g A) ↔ ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ∈ perp ψ A := by
  simp only [mem_perp, gmap, AddSubgroup.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h a ha
    rw [← dotProduct_mulVec]
    exact h _ a ha (by simp)
  · rintro h _ a ha rfl
    simp only [LinearMap.toAddMonoidHom_coe, mulVecLin_apply]
    rw [dotProduct_mulVec]
    exact h a ha

theorem meas_perp_gmap (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (g : GL (Fin (m + 1)) k) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : Lat A) : (ν (perp ψ (gmap g A))).toReal = (md g)⁻¹ * (ν (perp ψ A)).toReal := by
  have hmeas : MeasurableSet (perp ψ A : Set (Fin (m + 1) → k)) := (perp_open ψ hψ hψ1 hA).measurableSet
  have hmeas' : MeasurableSet (perp ψ (gmap g A) : Set (Fin (m + 1) → k)) :=
    (perp_open ψ hψ hψ1 (lat_gmap g A hA)).measurableSet
  have h := integral_vecMul ν ((perp ψ A : Set (Fin (m + 1) → k)).indicator fun _ => (1 : ℂ)) g
  have hset : (fun ξ => (perp ψ A : Set (Fin (m + 1) → k)).indicator (fun _ => (1 : ℂ))
      (ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k))) =
      (perp ψ (gmap g A) : Set (Fin (m + 1) → k)).indicator fun _ => (1 : ℂ) := by
    funext ξ
    by_cases hξ : ξ ∈ perp ψ (gmap g A)
    · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem ((perp_gmap ψ g A ξ).1 hξ)]
    · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem (fun h => hξ ((perp_gmap ψ g A ξ).2 h))]
  rw [hset, integral_indicator_const _ hmeas', integral_indicator_const _ hmeas] at h
  simp only [Complex.real_smul, mul_one] at h
  exact_mod_cast h

end Meas

section Psd

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem psd_norm_le (E : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hE : Psd E) (v w : V) : ‖E v w‖ ≤ ((E v v).re + (E w w).re) / 2 := by
  set c := E v w with hc
  by_cases h0 : c = 0
  · rw [h0, norm_zero]
    exact div_nonneg (add_nonneg (hE.2 v) (hE.2 w)) zero_le_two
  have hn : (‖c‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr h0
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = c / (‖c‖ : ℂ) := ⟨_, rfl⟩
  have h := hE.2 (v - z • w)
  have hwv : E w v = starRingEnd ℂ c := hE.1 v w
  have e1 : starRingEnd ℂ z * c = (‖c‖ : ℂ) := by
    rw [hz, map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    field_simp
  have e2 : z * starRingEnd ℂ c = (‖c‖ : ℂ) := by
    have := congrArg (starRingEnd ℂ) e1
    rwa [map_mul, Complex.conj_conj, Complex.conj_ofReal] at this
  have e3 : z * starRingEnd ℂ z = 1 := by
    rw [hz, map_div₀, Complex.conj_ofReal, div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rw [← pow_two]
    exact div_self (pow_ne_zero 2 (by exact_mod_cast hn))
  have hexp : E (v - z • w) (v - z • w) = E v v - (‖c‖ : ℂ) - (‖c‖ : ℂ) + E w w := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul]
    rw [← hc, hwv]
    linear_combination -e1 - e2 + (E w w) * e3
  rw [hexp] at h
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at h
  linarith

end Psd

section Main

local instance measurableSpaceSecondLift : MeasurableSpace k := borel k

theorem gmap_gmap_inv {n : ℕ} (g : GL (Fin n) k) (M : AddSubgroup (Fin n → k)) : gmap g (gmap g⁻¹ M) = M := by
  ext x
  simp only [gmap, AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe, mulVecLin_apply]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    rwa [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  · intro hx
    refine ⟨((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x, ⟨x, hx, rfl⟩, ?_⟩
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

variable {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {col : (Fin (m + 1) → k) → V →ₗ[ℂ] V} {gl : GL (Fin (m + 1)) k →* (V →ₗ[ℂ] V)} (hS : Setup col gl) {s : ℝ}
  {B B' C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : Lat A₀)
  (hBp : Psd B) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
  (hBg : ∀ g v w, B (gl g v) (gl g w) = ((md g ^ s : ℝ) : ℂ) * B v w)
  (hD : IsD ψ col A₀ B B') (hCp : Psd C) (hCc : ∀ x v w, C (col x v) w = ((ψ (xz m ⬝ᵥ x) : Circle) : ℂ) * C v w)
  (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w)
  (hCB : ∀ v, (C v v).re ≤ (B' v v).re)
  {ν : Measure (Fin (m + 1) → k)} [ν.IsAddHaarMeasure] (hν : ν (perp ψ A₀) = 1)


include hψ hψ1 hS hA₀ hBg hD hCp hC hCB hν in
theorem locB {ζ : Fin (m + 1) → k} (hζ : ζ ≠ 0) (v : V) :
    ∃ M₀ : AddSubgroup (Fin (m + 1) → k), Lat M₀ ∧ ∀ ξ, ξ - ζ ∈ perp ψ M₀ →
      Df gl s C ξ v v = Df gl s C ζ v v ∧ ∀ M, Lat M → M₀ ≤ M →
        (Df gl s C ζ v v).re * (ν (perp ψ M)).toReal ≤ (B (av ψ col ξ M v) v).re := by
  obtain ⟨A₁, hA₁, hA₀₁, hA₁s⟩ := hD (gl (sect ζ)⁻¹ v) (gl (sect ζ)⁻¹ v)
  obtain ⟨N, hNo, hζN, f, hf, hf1, hfN⟩ := GlobalTheory.T.local_continuous_section_vecMul_orbit k (m + 1) ζ hζ
  have hH : {h : GL (Fin (m + 1)) k | gl h v = v} ∩ {h | md h = 1} ∈ 𝓝 (1 : GL (Fin (m + 1)) k) := by
    refine Filter.inter_mem ((hS.smooth_gl v).mem_nhds (by simp)) ?_
    filter_upwards [GlobalTheory.T.eventually_haar_det_eq_one_near_one k (m + 1)] with h hh
    simp [md, nabs, hh]
  have hfc : ContinuousAt f ζ := hf.continuousAt (hNo.mem_nhds hζN)
  have hW : N ∩ f ⁻¹' ({h : GL (Fin (m + 1)) k | gl h v = v} ∩ {h | md h = 1}) ∈ 𝓝 ζ :=
    Filter.inter_mem (hNo.mem_nhds hζN) (hfc (by rw [hf1]; exact hH))
  have hU : (fun η => ζ + η) ⁻¹' (N ∩ f ⁻¹' ({h : GL (Fin (m + 1)) k | gl h v = v} ∩ {h | md h = 1})) ∈
      𝓝 (0 : Fin (m + 1) → k) := by
    have : Filter.Tendsto (fun η : Fin (m + 1) → k => ζ + η) (𝓝 0) (𝓝 ζ) := by
      have hc : Continuous (fun η : Fin (m + 1) → k => ζ + η) :=
        continuous_const.add continuous_id
      simpa using hc.tendsto (0 : Fin (m + 1) → k)
    exact this hW
  obtain ⟨M₁, hM₁, hM₁U⟩ := lat_shrink ψ hψ hψ1 hU
  have hSc : IsCompact ((fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k))) :=
    (perp_compact ψ hψ hψ1 hM₁).image (continuous_const.add continuous_id)
  have hSN : (fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k)) ⊆ N := by
    rintro _ ⟨η, hη, rfl⟩
    exact (hM₁U hη).1
  have hSH : ∀ ξ ∈ (fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k)), gl (f ξ) v = v ∧ md (f ξ) = 1 := by
    rintro _ ⟨η, hη, rfl⟩
    exact (hM₁U hη).2
  have hKc : IsCompact ((fun p : (Fin (m + 1) → k) × (Fin (m + 1) → k) =>
      ((((f p.1)⁻¹ * sect ζ : GL (Fin (m + 1)) k)) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ p.2) ''
        (((fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k))) ×ˢ (A₁ : Set (Fin (m + 1) → k)))) := by
    refine (hSc.prod hA₁.1).image_of_continuousOn ?_
    have h1 : ContinuousOn (fun p : (Fin (m + 1) → k) × (Fin (m + 1) → k) => f p.1)
        (((fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k))) ×ˢ (A₁ : Set (Fin (m + 1) → k))) :=
      (hf.mono hSN).comp continuous_fst.continuousOn (fun p hp => hp.1)
    have h2 := Units.continuous_val.comp_continuousOn (h1.inv.mul continuousOn_const
      (g := fun _ => (sect ζ : GL (Fin (m + 1)) k)))
    exact (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn (h2.prodMk continuous_snd.continuousOn)
  obtain ⟨M₂, hM₂, hKM₂⟩ := lat_over hKc
  obtain ⟨M₀, hM₀, hM₁M₀, hM₂M₀⟩ := lat_sup hM₁ hM₂
  refine ⟨M₀, hM₀, fun ξ hξ => ?_⟩
  have hξS : ξ ∈ (fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k)) :=
    ⟨ξ - ζ, perp_anti ψ hM₁M₀ hξ, by abel⟩
  obtain ⟨hhv, hhd⟩ := hSH ξ hξS
  have hζh : ζ ᵥ* (f ξ : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := hfN ξ (hSN hξS)
  have hg'ξ : xz m ᵥ* ((((f ξ)⁻¹ * sect ζ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := by
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← vecMul_vecMul, sect_spec hζ, hζh]
  have hξ0 : ξ ≠ 0 := by
    intro h0
    apply hζ
    have := congrArg (fun x => x ᵥ* (((f ξ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) (hζh.trans h0)
    simpa [vecMul_vecMul, ← Units.val_mul] using this
  have hu : gl ((f ξ)⁻¹ * sect ζ)⁻¹ v = gl (sect ζ)⁻¹ v := by
    rw [_root_.mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply, hhv]
  have hDg : Df gl s C ξ v v = Ct gl s C ((f ξ)⁻¹ * sect ζ) v v := by rw [Df_eq hC hξ0 hg'ξ]
  have hconst : Df gl s C ξ v v = Df gl s C ζ v v := by
    rw [hDg, Df_eq hC hζ (sect_spec hζ), Ct_apply, Ct_apply, hu, md_mul, md_inv, hhd, inv_one, one_mul]
  refine ⟨hconst, fun M hM hM₀M => ?_⟩
  set g' : GL (Fin (m + 1)) k := (f ξ)⁻¹ * sect ζ with hg'
  have hA : Lat (gmap g'⁻¹ M) := lat_gmap _ M hM
  have hA₁A : A₁ ≤ gmap g'⁻¹ M := by
    intro a ha
    have hK : ((g' : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ a) ∈ M :=
      hM₀M (hM₂M₀ (hKM₂ ⟨(ξ, a), ⟨hξS, ha⟩, rfl⟩))
    refine AddSubgroup.mem_map.mpr ⟨_, hK, ?_⟩
    simp only [LinearMap.toAddMonoidHom_coe, mulVecLin_apply]
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hdens := hA₁s _ hA hA₁A
  have hav := av_conj ψ hψ col hS.col_zero hS.col_add hS.smooth_col gl hS.conj g'⁻¹ M hM ξ v
  have hξg' : ξ ᵥ* (((g'⁻¹)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = xz m := by
    rw [inv_inv, ← hg'ξ, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]
  rw [hξg', hu] at hav
  rw [← hav, ← hu, hBg] at hdens

  have hmM : (ν (perp ψ M)).toReal = (md g')⁻¹ * (ν (perp ψ (gmap g'⁻¹ M))).toReal := by
    rw [← meas_perp_gmap ψ ν hψ hψ1 g' hA, gmap_gmap_inv]
  have hidx := meas_perp_index ψ ν hψ hψ1 hA₀ hA (hA₀₁.trans hA₁A)
  rw [hν] at hidx
  have hr : ((A₀.relIndex (gmap g'⁻¹ M) : ℕ) : ℝ) * (ν (perp ψ (gmap g'⁻¹ M))).toReal = 1 := by
    have := congrArg ENNReal.toReal hidx
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at this
    exact this.symm
  have hrpos : (0 : ℝ) < (A₀.relIndex (gmap g'⁻¹ M) : ℕ) := by
    exact_mod_cast Nat.pos_of_ne_zero (relIndex_ne_zero_of_lat hA₀ hA)

  have hre1 : (Df gl s C ζ v v).re = md g' ^ (s + 1) * (C (gl g'⁻¹ v) (gl g'⁻¹ v)).re := by
    rw [← hconst, hDg, Ct_apply, Complex.re_ofReal_mul]
  have hre2 : (B' (gl g'⁻¹ v) (gl g'⁻¹ v)).re =
      ((A₀.relIndex (gmap g'⁻¹ M) : ℕ) : ℝ) * (md g'⁻¹ ^ s * (B (av ψ col ξ M v) v).re) := by
    rw [hdens, ← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have hle := hCB (gl g'⁻¹ v)
  set t := md g' with ht
  have htpos : 0 < t := md_pos g'
  set r : ℝ := ((A₀.relIndex (gmap g'⁻¹ M) : ℕ) : ℝ) with hrdef
  set b := (B (av ψ col ξ M v) v).re with hb
  set c := (C (gl g'⁻¹ v) (gl g'⁻¹ v)).re with hc
  set μA := (ν (perp ψ (gmap g'⁻¹ M))).toReal with hμA
  rw [md_inv, ← ht] at hre2
  rw [hre1, hmM]
  have hμA' : μA = r⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hr)
  rw [hμA']
  have hts : t ^ (s + 1) = t ^ s * t := Real.rpow_add_one htpos.ne' s
  have hti : t⁻¹ ^ s = (t ^ s)⁻¹ := Real.inv_rpow htpos.le s
  rw [hti] at hre2
  have htspos : 0 < t ^ s := Real.rpow_pos_of_pos htpos s
  calc t ^ (s + 1) * c * (t⁻¹ * r⁻¹) ≤ t ^ (s + 1) * (r * ((t ^ s)⁻¹ * b)) * (t⁻¹ * r⁻¹) := by
        rw [← hre2]
        gcongr
    _ = b := by
        rw [hts]
        field_simp

end Main

end PositivityTheory.RgUd.Form.U.Lift2
end
end

noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitWeil GlobalTheory.BZMir Filter
open scoped Topology ENNReal NNReal

namespace PositivityTheory.RgUd.Form.U.Lift2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Main

local instance measurableSpaceThirdLift : MeasurableSpace k := borel k
local instance borelSpaceThirdLift : BorelSpace k := ⟨rfl⟩
local instance instSCK3 : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k

variable {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {col : (Fin (m + 1) → k) → V →ₗ[ℂ] V} {gl : GL (Fin (m + 1)) k →* (V →ₗ[ℂ] V)} (hS : Setup col gl) {s : ℝ}
  {B B' C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : Lat A₀)
  (hBp : Psd B) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
  (hBg : ∀ g v w, B (gl g v) (gl g w) = ((md g ^ s : ℝ) : ℂ) * B v w)
  (hD : IsD ψ col A₀ B B') (hCp : Psd C) (hCc : ∀ x v w, C (col x v) w = ((ψ (xz m ⬝ᵥ x) : Circle) : ℂ) * C v w)
  (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w)
  (hCB : ∀ v, (C v v).re ≤ (B' v v).re)
  {ν : Measure (Fin (m + 1) → k)} [ν.IsAddHaarMeasure] (hν : ν (perp ψ A₀) = 1)


include hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν in
theorem cov {K : Set (Fin (m + 1) → k)} (hK : IsCompact K) (h0 : (0 : Fin (m + 1) → k) ∉ K) (v : V) :
    ∫⁻ ξ in K, ENNReal.ofReal (Df gl s C ξ v v).re ∂ν ≤ ENNReal.ofReal (B v v).re := by
  classical
  have hloc : ∀ ζ ∈ K, ∃ M₀ : AddSubgroup (Fin (m + 1) → k), Lat M₀ ∧
      ∀ ξ, ξ - ζ ∈ perp ψ M₀ → Df gl s C ξ v v = Df gl s C ζ v v ∧
        ∀ M : AddSubgroup (Fin (m + 1) → k), Lat M → M₀ ≤ M →
          (Df gl s C ζ v v).re * (ν (perp ψ M)).toReal ≤ (B (av ψ col ξ M v) v).re :=
    fun ζ hζ => locB hψ hψ1 hS hA₀ hBg hD hCp hC hCB hν (fun h => h0 (h ▸ hζ)) v
  choose! M₀ hM₀L hM₀ using hloc
  obtain ⟨F, hFK, hFfin, hFcov⟩ := hK.elim_finite_subcover_image (b := K)
    (c := fun ζ => (fun ξ => ξ - ζ) ⁻¹' (perp ψ (M₀ ζ) : Set (Fin (m + 1) → k)))
    (fun ζ hζ => (perp_open ψ hψ hψ1 (hM₀L ζ hζ)).preimage (continuous_sub_right ζ))
    (fun ζ hζ => Set.mem_biUnion hζ (by simp))
  have hcomp : IsCompact (⋃ ζ ∈ F, (M₀ ζ : Set (Fin (m + 1) → k))) :=
    hFfin.isCompact_biUnion fun ζ hζ => (hM₀L ζ (hFK hζ)).1
  obtain ⟨M, hML, hMsub⟩ := lat_over hcomp
  have hMle : ∀ ζ ∈ F, M₀ ζ ≤ M := fun ζ hζ x hx => hMsub (Set.mem_biUnion hζ hx)
  have hPle : ∀ ζ ∈ F, perp ψ M ≤ perp ψ (M₀ ζ) := fun ζ hζ => perp_anti ψ (hMle ζ hζ)
  have hPo : IsOpen (perp ψ M : Set (Fin (m + 1) → k)) := perp_open ψ hψ hψ1 hML
  obtain ⟨T, hTK, hTfin, hTcov⟩ := hK.elim_finite_subcover_image (b := K)
    (c := fun t => (fun ξ => ξ - t) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k)))
    (fun t _ => hPo.preimage (continuous_sub_right t))
    (fun ξ hξ => Set.mem_biUnion hξ (by simp))
  let q : (Fin (m + 1) → k) → (Fin (m + 1) → k) ⧸ perp ψ M := QuotientAddGroup.mk
  have hq : ∀ a b, q a = q b → a - b ∈ perp ψ M := fun a b h => by
    have h1 := (perp ψ M).neg_mem (QuotientAddGroup.eq.mp h)
    rwa [show -(-a + b) = a - b by abel] at h1
  have hq' : ∀ a b, a - b ∈ perp ψ M → q a = q b := fun a b h => by
    apply QuotientAddGroup.eq.mpr
    rw [show -a + b = -(a - b) by abel]
    exact (perp ψ M).neg_mem h
  have hout : ∀ t, q (q t).out = q t := fun t => QuotientAddGroup.out_eq' (q t)
  let S : Finset (Fin (m + 1) → k) := hTfin.toFinset.image (fun t => (q t).out)
  have hSF : ∀ η ∈ S, ∃ ζ ∈ F, ∀ ξ, ξ - η ∈ perp ψ M → ξ - ζ ∈ perp ψ (M₀ ζ) := by
    intro η hη
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hη
    have htK : t ∈ K := hTK (hTfin.mem_toFinset.mp ht)
    obtain ⟨ζ, hζ, hζt⟩ := Set.mem_iUnion₂.mp (hFcov htK)
    refine ⟨ζ, hζ, fun ξ hξ => ?_⟩
    have h1 : (q t).out - t ∈ perp ψ M := hq _ _ (hout t)
    have h2 : ξ - ζ = (ξ - (q t).out) + ((q t).out - t) + (t - ζ) := by abel
    rw [h2]
    exact add_mem (add_mem (hPle ζ hζ hξ) (hPle ζ hζ h1)) (show t - ζ ∈ perp ψ (M₀ ζ) from hζt)
  have hSd : ∀ η ∈ S, ∀ η' ∈ S, η - η' ∈ perp ψ M → η = η' := by
    intro η hη η' hη' h
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hη
    obtain ⟨t', -, rfl⟩ := Finset.mem_image.mp hη'
    have h1 := hq' _ _ h
    rw [hout, hout] at h1
    rw [h1]
  have hKS : K ⊆ ⋃ η ∈ S, (fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k)) := by
    intro ξ hξ
    obtain ⟨t, ht, hξt⟩ := Set.mem_iUnion₂.mp (hTcov hξ)
    refine Set.mem_iUnion₂.mpr ⟨(q t).out, Finset.mem_image.mpr ⟨t, hTfin.mem_toFinset.mpr ht, rfl⟩, ?_⟩
    have h1 : t - (q t).out ∈ perp ψ M := hq _ _ (hout t).symm
    show ξ - (q t).out ∈ perp ψ M
    rw [show ξ - (q t).out = (ξ - t) + (t - (q t).out) by abel]
    exact add_mem (show ξ - t ∈ perp ψ M from hξt) h1
  have hdisj : Set.PairwiseDisjoint (↑S)
      (fun η => (fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k))) := by
    intro η hη η' hη' hne
    refine Set.disjoint_left.mpr fun ξ h1 h2 => hne (hSd η hη η' hη' ?_)
    rw [show η - η' = (ξ - η') - (ξ - η) by abel]
    exact sub_mem (show ξ - η' ∈ perp ψ M from h2) (show ξ - η ∈ perp ψ M from h1)
  have hPfin : ν (perp ψ M) < ∞ := meas_perp_lt_top ψ ν hψ hψ1 hML
  have hbd : ∀ η ∈ S, (Df gl s C η v v).re * (ν (perp ψ M)).toReal ≤ (B (av ψ col η M v) v).re ∧
      ∃ ζ ∈ F, Df gl s C η v v = Df gl s C ζ v v ∧
        ∀ ξ, ξ - η ∈ perp ψ M → Df gl s C ξ v v = Df gl s C η v v := by
    intro η hη
    obtain ⟨ζ, hζ, hζη⟩ := hSF η hη
    have hζK := hFK hζ
    have e0 : Df gl s C η v v = Df gl s C ζ v v := ((hM₀ ζ hζK) η (hζη η (by simp))).1
    have hb := ((hM₀ ζ hζK) η (hζη η (by simp))).2 M hML (hMle ζ hζ)
    refine ⟨by rw [e0]; exact hb, ζ, hζ, e0, fun ξ hξ => ?_⟩
    rw [e0]
    exact ((hM₀ ζ hζK) ξ (hζη ξ hξ)).1
  have step : ∀ η ∈ S, ∫⁻ ξ in (fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k)),
      ENNReal.ofReal (Df gl s C ξ v v).re ∂ν ≤ ENNReal.ofReal (B (av ψ col η M v) v).re := by
    intro η hη
    obtain ⟨hb, -, -, -, hc⟩ := hbd η hη
    rw [setLIntegral_congr_fun (g := fun _ => ENNReal.ofReal (Df gl s C η v v).re)
      (hPo.preimage (continuous_sub_right η)).measurableSet
      (fun ξ hξ => by simp only; rw [hc ξ hξ]), setLIntegral_const]
    have hmeas : ν ((fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k))) = ν (perp ψ M) := by
      simp only [sub_eq_add_neg]
      exact measure_preimage_add_right ν (-η) _
    rw [hmeas, ← ENNReal.ofReal_toReal hPfin.ne, ← ENNReal.ofReal_mul (Df_re_nonneg hCp η v)]
    exact ENNReal.ofReal_le_ofReal hb
  have hnn : ∀ η ∈ S, 0 ≤ (B (av ψ col η M v) v).re := fun η hη =>
    le_trans (mul_nonneg (Df_re_nonneg hCp η v) ENNReal.toReal_nonneg) (hbd η hη).1
  have hbes := av_bessel ψ hψ col hS.col_zero hS.col_add hS.smooth_col B hBp hBc M hML S hSd v
  calc ∫⁻ ξ in K, ENNReal.ofReal (Df gl s C ξ v v).re ∂ν
      ≤ ∫⁻ ξ in ⋃ η ∈ S, (fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k)),
          ENNReal.ofReal (Df gl s C ξ v v).re ∂ν := lintegral_mono_set hKS
    _ = ∑ η ∈ S, ∫⁻ ξ in (fun ξ => ξ - η) ⁻¹' (perp ψ M : Set (Fin (m + 1) → k)),
          ENNReal.ofReal (Df gl s C ξ v v).re ∂ν :=
        lintegral_biUnion_finset hdisj (fun η _ => (hPo.preimage (continuous_sub_right η)).measurableSet) _
    _ ≤ ∑ η ∈ S, ENNReal.ofReal (B (av ψ col η M v) v).re := Finset.sum_le_sum step
    _ = ENNReal.ofReal (∑ η ∈ S, (B (av ψ col η M v) v).re) := (ENNReal.ofReal_sum_of_nonneg hnn).symm
    _ ≤ ENNReal.ofReal (B v v).re := ENNReal.ofReal_le_ofReal hbes


include hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν in
theorem bessel (v : V) : ∫⁻ ξ, ENNReal.ofReal (Df gl s C ξ v v).re ∂ν ≤ ENNReal.ofReal (B v v).re := by
  classical
  let f : (Fin (m + 1) → k) → ℝ≥0∞ := fun ξ => ENNReal.ofReal (Df gl s C ξ v v).re
  have hDm : Measurable fun ξ => Df gl s C ξ v v := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro ζ hζ
    exact (continuousAt_const.congr
      ((Df_loc hS hC hζ v v).mono fun ξ hξ => hξ.symm)).continuousWithinAt
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp (Complex.measurable_re.comp hDm)
  obtain ⟨W, hWp, hW⟩ := (nhds_basis_opens (0 : Fin (m + 1) → k)).exists_antitone_subbasis
  let E := CompactExhaustion.choice (Fin (m + 1) → k)
  let K : ℕ → Set (Fin (m + 1) → k) := fun n => E n \ W n
  have hKc : ∀ n, IsCompact (K n) := fun n => (E.isCompact n).diff (hWp n).2
  have h0K : ∀ n, (0 : Fin (m + 1) → k) ∉ K n := fun n h => h.2 (hWp n).1
  have hKmono : Monotone K := fun a b hab => Set.diff_subset_diff (E.subset hab) (hW.antitone hab)
  let g : ℕ → (Fin (m + 1) → k) → ℝ≥0∞ := fun n => (K n).indicator f
  have hgm : ∀ n, Measurable (g n) := fun n => hfm.indicator (hKc n).measurableSet
  have hgmono : Monotone g := fun a b hab ξ =>
    Set.indicator_le_indicator_of_subset (hKmono hab) (fun _ => bot_le) ξ
  have hsup : ∀ ξ, f ξ = ⨆ n, g n ξ := by
    intro ξ
    by_cases hξ : ξ = 0
    · subst hξ
      have hf0 : f 0 = 0 := by simp [f, Df_zero]
      rw [hf0]
      symm
      exact ENNReal.iSup_eq_zero.mpr fun n => by simp [g, Set.indicator_apply, h0K n]
    · obtain ⟨n₁, hn₁⟩ := E.exists_mem ξ
      obtain ⟨i, -, hi⟩ := hW.toHasBasis.mem_iff.mp (isOpen_compl_singleton.mem_nhds (Ne.symm hξ))
      have hmem : ξ ∈ K (max n₁ i) := by
        refine ⟨E.subset (le_max_left _ _) hn₁, fun h => ?_⟩
        exact hi (hW.antitone (le_max_right _ _) h) rfl
      refine le_antisymm (le_iSup_of_le (max n₁ i) ?_) (iSup_le fun n => Set.indicator_le_self _ _ ξ)
      simp [g, Set.indicator_apply, hmem]
  show ∫⁻ ξ, f ξ ∂ν ≤ _
  calc ∫⁻ ξ, f ξ ∂ν = ∫⁻ ξ, ⨆ n, g n ξ ∂ν := lintegral_congr hsup
    _ = ⨆ n, ∫⁻ ξ, g n ξ ∂ν := lintegral_iSup hgm hgmono
    _ ≤ ENNReal.ofReal (B v v).re := iSup_le fun n => by
        simp only [g]
        rw [lintegral_indicator (hKc n).measurableSet]
        exact cov hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν (hKc n) (h0K n) v

omit hψ hψ1 hA₀ hBp hBc hBg hD hCp hCB hν [ν.IsAddHaarMeasure] in
include hS hC in
theorem Df_meas (v w : V) : Measurable fun ξ => Df gl s C ξ v w := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro ζ hζ
  exact (continuousAt_const.congr
    ((Df_loc hS hC hζ v w).mono fun ξ hξ => hξ.symm)).continuousWithinAt

include hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν in
theorem integrable_re (v : V) : Integrable (fun ξ => (Df gl s C ξ v v).re) ν := by
  refine ⟨(Complex.measurable_re.comp (Df_meas hS hC v v)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ξ => Df_re_nonneg hCp ξ v)]
  exact lt_of_le_of_lt (bessel hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν v) ENNReal.ofReal_lt_top

include hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν in
theorem integrable_Df (v w : V) : Integrable (fun ξ => Df gl s C ξ v w) ν := by
  refine Integrable.mono'
    (((integrable_re hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν v).add
      (integrable_re hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC hCB hν w)).div_const 2)
    (Df_meas hS hC v w).aestronglyMeasurable
    (Eventually.of_forall fun ξ => psd_norm_le _ ⟨Df_herm hCp ξ, Df_re_nonneg hCp ξ⟩ v w)

end Main

end PositivityTheory.RgUd.Form.U.Lift2

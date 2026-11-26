module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardKerSubspacesAndHeckePolyOfConvolution

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardSubspacesContainingRangeQVandermonde
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardSubspacesContainingRangeQVandermonde
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.RangeKerCount

open GlobalTheory.KerRangeCount Formalism.L2.Col

theorem card_above_range_eq_sum : ∀ (κ : Type) [Field κ] [Finite κ] (U U' : Type) [AddCommGroup U] [Module κ U] [FiniteDimensional κ U] [AddCommGroup U'] [Module κ U'] [FiniteDimensional κ U'] (f : U →ₗ[κ] U') (t e : ℕ), Module.finrank κ U' = Module.finrank κ U + t → e ≤ Module.finrank κ U' → Nat.card {X : Submodule κ U' // LinearMap.range f ≤ X ∧ Module.finrank κ X + e = Module.finrank κ U'} = ∑ n ∈ Finset.range (Module.finrank κ U + 1), (if n ≤ e then Nat.card κ ^ (n * (t - (e - n))) * Formalism.L2.Col.gaussBin (Nat.card κ) t (e - n) else 0) * Nat.card {X : Submodule κ U // X ≤ LinearMap.ker f ∧ Module.finrank κ X = n} := by
  intro κ _ _ U U' _ _ _ _ _ _ f t e hU' he
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  rw [Nat.card_eq_fintype_card (α := κ)]
  have hq0 : Fintype.card κ ≠ 0 := Fintype.card_ne_zero
  have hrk := f.finrank_range_add_finrank_ker
  have hin : ∀ n, Nat.card {X : Submodule κ U // X ≤ LinearMap.ker f ∧ Module.finrank κ X = n} =
      Formalism.L2.Col.gaussBin (Fintype.card κ) (Module.finrank κ (LinearMap.ker f)) n := by
    intro n
    rw [← card_below (LinearMap.ker f) n]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun X => and_comm)
  have hL : Nat.card {X : Submodule κ U' // LinearMap.range f ≤ X ∧ Module.finrank κ X + e = Module.finrank κ U'} =
      Formalism.L2.Col.gaussBin (Fintype.card κ) (Module.finrank κ (LinearMap.ker f) + t) e := by
    by_cases hem : e ≤ Module.finrank κ (LinearMap.ker f) + t
    · rw [gaussBin_symm hq0 (Module.finrank κ (LinearMap.ker f) + t) e
        (Module.finrank κ (LinearMap.ker f) + t - e) (by omega)]
      have h := card_above (k := κ) (LinearMap.range f) (Module.finrank κ (LinearMap.ker f) + t - e)
      rw [show Module.finrank κ U' - Module.finrank κ (LinearMap.range f) =
        Module.finrank κ (LinearMap.ker f) + t by omega] at h
      rw [← h]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun X =>
        ⟨fun h => ⟨by omega, h.1⟩, fun h => ⟨h.2, by omega⟩⟩)
    · have : IsEmpty {X : Submodule κ U' // LinearMap.range f ≤ X ∧ Module.finrank κ X + e = Module.finrank κ U'} :=
        ⟨fun X => by have := Submodule.finrank_mono X.2.1; have := X.2.2; omega⟩
      rw [Nat.card_of_isEmpty, gaussBin_eq_zero _ (by omega)]
  set q := Fintype.card κ
  set m := Module.finrank κ (LinearMap.ker f)
  set g : ℕ → ℕ := fun n => (if n ≤ e then q ^ (n * (t - (e - n))) * Formalism.L2.Col.gaussBin q t (e - n) else 0) *
    Formalism.L2.Col.gaussBin q m n with hg
  have hR : ∑ n ∈ Finset.range (Module.finrank κ U + 1), (if n ≤ e then q ^ (n * (t - (e - n))) *
      Formalism.L2.Col.gaussBin q t (e - n) else 0) *
      Nat.card {X : Submodule κ U // X ≤ LinearMap.ker f ∧ Module.finrank κ X = n} =
      ∑ n ∈ Finset.range (Module.finrank κ U + 1), g n :=
    Finset.sum_congr rfl fun n _ => by rw [hin]
  have h2 : ∑ n ∈ Finset.range (e + 1), g n = ∑ n ∈ Finset.range (e + Module.finrank κ U + 1), g n :=
    Finset.sum_subset (Finset.range_mono (by omega)) fun n _ hn => by
      rw [Finset.mem_range] at hn
      simp only [hg]
      rw [if_neg (by omega), zero_mul]
  have h3 : ∑ n ∈ Finset.range (Module.finrank κ U + 1), g n =
      ∑ n ∈ Finset.range (e + Module.finrank κ U + 1), g n :=
    Finset.sum_subset (Finset.range_mono (by omega)) fun n _ hn => by
      rw [Finset.mem_range] at hn
      simp only [hg]
      rw [gaussBin_eq_zero q (show m < n by omega), mul_zero]
  rw [hL, hR, h3, ← h2, gaussBin_add hq0 m t e, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_range] at hn
  simp only [hg]
  rw [if_pos (by omega), show e + 1 - 1 - n = e - n by omega, show e - (e - n) = n by omega]
  ring

end GlobalTheory.RangeKerCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardSubspacesContainingRangeQVandermondeStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_subspaces_containing_range_qVandermonde : ∀ (κ : Type) [Field κ] [Finite κ] (U U' : Type) [AddCommGroup U] [Module κ U] [FiniteDimensional κ U] [AddCommGroup U'] [Module κ U'] [FiniteDimensional κ U'] (f : U →ₗ[κ] U') (t e : ℕ), Module.finrank κ U' = Module.finrank κ U + t → e ≤ Module.finrank κ U' → Nat.card {X : Submodule κ U' // LinearMap.range f ≤ X ∧ Module.finrank κ X + e = Module.finrank κ U'} = ∑ n ∈ Finset.range (Module.finrank κ U + 1), (if n ≤ e then Nat.card κ ^ (n * (t - (e - n))) * Formalism.L2.Col.gaussBin (Nat.card κ) t (e - n) else 0) * Nat.card {X : Submodule κ U // X ≤ LinearMap.ker f ∧ Module.finrank κ X = n} := by
  first | exact @GlobalTheory.RangeKerCount.card_above_range_eq_sum | exact GlobalTheory.RangeKerCount.card_above_range_eq_sum | (intros; apply GlobalTheory.RangeKerCount.card_above_range_eq_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralIndicatorCosetsKernelSubspaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralIndicatorCosetsKernelSubspaces
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ParHecke.CosetSub

theorem exists_equiv_map_eq {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (W W' : Submodule F V)
    (h : Module.finrank F W = Module.finrank F W') :
    ∃ e : V ≃ₗ[F] V, W.map e.toLinearMap = W' := by
  obtain ⟨U, hU⟩ := W.exists_isCompl
  obtain ⟨U', hU'⟩ := W'.exists_isCompl
  have h1 := Submodule.finrank_add_eq_of_isCompl hU
  have h2 := Submodule.finrank_add_eq_of_isCompl hU'
  have h3 : Module.finrank F U = Module.finrank F U' := by omega
  let a : W ≃ₗ[F] W' := LinearEquiv.ofFinrankEq _ _ h
  let b : U ≃ₗ[F] U' := LinearEquiv.ofFinrankEq _ _ h3
  let e : V ≃ₗ[F] V := (Submodule.prodEquivOfIsCompl W U hU).symm ≪≫ₗ (a.prodCongr b) ≪≫ₗ
    Submodule.prodEquivOfIsCompl W' U' hU'
  have he : ∀ w : W, e w = a w := by
    intro w
    simp [e]
  refine ⟨e, ?_⟩
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    have := he ⟨w, hw⟩
    change e w ∈ W'
    simp only at this
    rw [this]
    exact (a ⟨w, hw⟩).2
  · intro w hw
    refine ⟨a.symm ⟨w, hw⟩, (a.symm ⟨w, hw⟩).2, ?_⟩
    change e _ = w
    rw [he]
    simp

theorem exists_gl_map_eq (O : Type) [CommRing O] [IsLocalRing O] (D : Type) [Fintype D] [DecidableEq D]
    (W W' : Submodule (IsLocalRing.ResidueField O) (D → IsLocalRing.ResidueField O))
    (h : Module.finrank (IsLocalRing.ResidueField O) W =
      Module.finrank (IsLocalRing.ResidueField O) W') :
    ∃ g : GL D O, W.map (g.1.map (IsLocalRing.residue O)).mulVecLin = W' := by
  obtain ⟨e, he⟩ := exists_equiv_map_eq W W' h
  let M : Matrix D D (IsLocalRing.ResidueField O) := LinearMap.toMatrix' e.toLinearMap
  choose A hA using fun i j => IsLocalRing.residue_surjective (R := O) (M i j)
  have hAM : (Matrix.of A).map (IsLocalRing.residue O) = M := by
    ext i j
    exact hA i j
  have hM : M.det ≠ 0 := by
    have : M.det = LinearMap.det e.toLinearMap := LinearMap.det_toMatrix' _
    rw [this]
    exact (LinearEquiv.isUnit_det' e).ne_zero
  have hu : IsUnit (Matrix.of A).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    change ((Matrix.of A).map (IsLocalRing.residue O)).det ≠ 0
    rw [hAM]
    exact hM
  obtain ⟨g, hg⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hu
  refine ⟨g, ?_⟩
  rw [hg, hAM, ← he]
  congr 1
  exact Matrix.toLin'_toMatrix' e.toLinearMap

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {D D' : Type} [Fintype D] [DecidableEq D]

def projE (F : Type) [Field F] (s : Finset D) : Matrix D D F := diagonal fun i => if i ∈ s then 1 else 0

theorem rank_projE (F : Type) [Field F] (s : Finset D) : (projE F s).rank = s.card := by
  classical
  rw [projE, rank_diagonal]
  rw [Fintype.card_subtype]
  congr 1
  ext i
  by_cases h : i ∈ s <;> simp [h]

abbrev red {m n : Type} (M : Matrix m n 𝒪[k]) : Matrix m n 𝓀[k] := M.map (IsLocalRing.residue 𝒪[k])

abbrev inc {m n : Type} (M : Matrix m n 𝒪[k]) : Matrix m n k := M.map (algebraMap 𝒪[k] k)

abbrev incG (κ : GL D 𝒪[k]) : GL D k := GeneralLinearGroup.map (algebraMap 𝒪[k] k) κ

def colSp (s : Finset D) (κ : GL D 𝒪[k]) : Submodule 𝓀[k] (D → 𝓀[k]) :=
  LinearMap.range (red κ.1 * projE 𝓀[k] s).mulVecLin

theorem finrank_colSp (s : Finset D) (κ : GL D 𝒪[k]) : Module.finrank 𝓀[k] (colSp s κ) = s.card := by
  rw [← rank_projE 𝓀[k] s]
  refine rank_mul_eq_right_of_isUnit_det _ _ ?_
  have : (red κ.1).det = IsLocalRing.residue 𝒪[k] κ.1.det := (RingHom.map_det _ _).symm
  rw [this]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 κ.isUnit).map _

theorem exists_colSp (s : Finset D) (U : Submodule 𝓀[k] (D → 𝓀[k])) (hU : Module.finrank 𝓀[k] U = s.card) :
    ∃ κ : GL D 𝒪[k], colSp s κ = U := by
  obtain ⟨g, hg⟩ := exists_gl_map_eq 𝒪[k] D (LinearMap.range (projE 𝓀[k] s).mulVecLin) U
    (by rw [hU, ← rank_projE 𝓀[k] s]; rfl)
  exact ⟨g, by rw [colSp, mulVecLin_mul, LinearMap.range_comp]; exact hg⟩

theorem colSp_le_ker_iff (s : Finset D) (κ : GL D 𝒪[k]) (Y : Matrix D' D 𝓀[k]) [Fintype D'] [DecidableEq D'] :
    colSp s κ ≤ LinearMap.ker Y.mulVecLin ↔ Y * red κ.1 * projE 𝓀[k] s = 0 := by
  rw [colSp, LinearMap.range_le_ker_iff, ← mulVecLin_mul, Matrix.mul_assoc, ← toLin'_apply', map_eq_zero_iff _ toLin'.injective]

theorem div_mem_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (x : 𝒪[k]) :
    (x : k) * (ϖ : k)⁻¹ ∈ 𝒪[k] ↔ IsLocalRing.residue 𝒪[k] x = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one, Valuation.mem_integer_iff, ← le_uniformizer_iff, ← hϖ,
    map_mul, map_inv₀, mul_inv_le_iff₀ (by rw [hϖ]; exact uniformizer_pos), one_mul]

theorem int_mul_torus_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D) (M : Matrix D' D 𝒪[k]) :
    (∀ i j, (inc M * (torusElt k D ϖ (-indic s)).1) i j ∈ 𝒪[k]) ↔ red M * projE 𝓀[k] s = 0 := by
  rw [val_torusElt, projE, ← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [mul_diagonal, mul_diagonal]
  by_cases h : j ∈ s
  · have := div_mem_iff hϖ (M i j)
    simp only [indic, h, Pi.neg_apply, if_true, _root_.zpow_neg, zpow_one, mul_one, map_apply, Matrix.zero_apply]
    exact this
  · simp only [indic, h, Pi.neg_apply, if_false, neg_zero, zpow_zero, mul_one, mul_zero, map_apply, Matrix.zero_apply, iff_true]
    exact (M i j).2

omit [DecidableEq D] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem int_mul {m n : Type} {A : Matrix m D k} {B : Matrix D n k} (hA : ∀ i j, A i j ∈ 𝒪[k]) (hB : ∀ i j, B i j ∈ 𝒪[k]) :
    ∀ i j, (A * B) i j ∈ 𝒪[k] := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hA i l) (hB l j)

theorem int_of_KO {g : GL D k} (hg : g ∈ KO k D) : ∀ i j, g.1 i j ∈ 𝒪[k] := by
  obtain ⟨κ, rfl⟩ := hg
  intro i j
  exact (κ.1 i j).2

theorem KO_of_int {g : GL D k} (hg : ∀ i j, g.1 i j ∈ 𝒪[k]) (hg' : ∀ i j, (g⁻¹).1 i j ∈ 𝒪[k]) : g ∈ KO k D := by
  let A : Matrix D D 𝒪[k] := fun i j => ⟨_, hg i j⟩
  let B : Matrix D D 𝒪[k] := fun i j => ⟨_, hg' i j⟩
  have hA : inc A = g.1 := rfl
  have hB : inc B = (g⁻¹).1 := rfl
  have inj : Function.Injective (inc : Matrix D D 𝒪[k] → Matrix D D k) := map_injective Subtype.val_injective
  have h1 : inc (1 : Matrix D D 𝒪[k]) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext hA⟩
  · rw [h1, inc, Matrix.map_mul]
    change g.1 * (g⁻¹).1 = 1
    simp
  · rw [h1, inc, Matrix.map_mul]
    change (g⁻¹).1 * g.1 = 1
    simp

theorem int_mul_KO_iff {A : Matrix D' D k} {g : GL D k} (hg : g ∈ KO k D) :
    (∀ i j, (A * g.1) i j ∈ 𝒪[k]) ↔ ∀ i j, A i j ∈ 𝒪[k] := by
  refine ⟨fun h => ?_, fun h => int_mul h (int_of_KO hg)⟩
  have := int_mul h (int_of_KO (inv_mem hg))
  rwa [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this

theorem int_iff_colSp {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D) [Fintype D'] [DecidableEq D']
    (y : Matrix D' D 𝒪[k]) (κ : GL D 𝒪[k]) :
    (∀ i j, (inc y * (incG κ * torusElt k D ϖ (-indic s)).1) i j ∈ 𝒪[k]) ↔ colSp s κ ≤ LinearMap.ker (red y).mulVecLin := by
  have e1 : red y * red κ.1 = red (y * κ.1) := Matrix.map_mul.symm
  have e2 : inc y * (incG κ).1 = inc (y * κ.1) := Matrix.map_mul.symm
  rw [colSp_le_ker_iff, e1, ← int_mul_torus_iff hϖ, Units.val_mul, ← Matrix.mul_assoc, e2]

theorem int_torus_inv {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D) :
    ∀ i j, ((torusElt k D ϖ (-indic s))⁻¹).1 i j ∈ 𝒪[k] := by
  have e : (torusElt k D ϖ (-indic s))⁻¹ = torusElt k D ϖ (indic s) := by
    rw [inv_eq_iff_mul_eq_one]
    apply Units.ext
    rw [Units.val_mul, val_torusElt, val_torusElt, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
    congr 1
    ext i
    rw [← zpow_add₀ ϖ.ne_zero]
    simp
  intro i j
  rw [e, val_torusElt, diagonal_apply]
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  split_ifs with h
  · by_cases h' : i ∈ s
    · simpa [indic, h', Valuation.mem_integer_iff] using hlt.le
    · simp [indic, h']
  · exact zero_mem _

theorem int_coset_inv {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D) {κ : GL D k} (hκ : κ ∈ KO k D) :
    ∀ i j, ((κ * torusElt k D ϖ (-indic s))⁻¹).1 i j ∈ 𝒪[k] := by
  rw [_root_.mul_inv_rev, Units.val_mul]
  exact int_mul (int_torus_inv hϖ s) (int_of_KO (inv_mem hκ))

theorem int_quot_of_le {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D) (κ₁ κ₂ : GL D 𝒪[k])
    (h : colSp s κ₂ ≤ colSp s κ₁) :
    ∀ i j, ((incG κ₁ * torusElt k D ϖ (-indic s))⁻¹ * (incG κ₂ * torusElt k D ϖ (-indic s))).1 i j ∈ 𝒪[k] := by
  let y : Matrix D D 𝒪[k] := fun i j => ⟨_, int_coset_inv hϖ s (κ := incG κ₁) ⟨κ₁, rfl⟩ i j⟩
  have hy : inc y = ((incG κ₁ * torusElt k D ϖ (-indic s))⁻¹).1 := rfl
  rw [Units.val_mul, ← hy, int_iff_colSp hϖ]
  refine h.trans ?_
  rw [← int_iff_colSp hϖ, hy, ← Units.val_mul, inv_mul_cancel]
  exact int_of_KO (one_mem _)

theorem colSp_eq_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D) (κ₁ κ₂ : GL D 𝒪[k]) :
    colSp s κ₁ = colSp s κ₂ ↔
      (incG κ₁ * torusElt k D ϖ (-indic s))⁻¹ * (incG κ₂ * torusElt k D ϖ (-indic s)) ∈ KO k D := by
  constructor
  · intro h
    refine KO_of_int (int_quot_of_le hϖ s κ₁ κ₂ h.ge) ?_
    rw [_root_.mul_inv_rev, inv_inv]
    exact int_quot_of_le hϖ s κ₂ κ₁ h.le
  · intro h
    have key : ∀ y : Matrix D D 𝒪[k], colSp s κ₁ ≤ LinearMap.ker (red y).mulVecLin ↔
        colSp s κ₂ ≤ LinearMap.ker (red y).mulVecLin := by
      intro y
      rw [← int_iff_colSp hϖ, ← int_iff_colSp hϖ, ← int_mul_KO_iff h, Matrix.mul_assoc, ← Units.val_mul,
        mul_inv_cancel_left]
    have key2 : ∀ U : Submodule 𝓀[k] (D → 𝓀[k]), ∃ y : Matrix D D 𝒪[k], LinearMap.ker (red y).mulVecLin = U := by
      intro U
      obtain ⟨U', hU⟩ := U.exists_isCompl
      let p : (D → 𝓀[k]) →ₗ[𝓀[k]] (D → 𝓀[k]) := U'.subtype ∘ₗ Submodule.projectionOnto U' U hU.symm
      choose A hA using fun i j => IsLocalRing.residue_surjective (R := 𝒪[k]) (LinearMap.toMatrix' p i j)
      have hAM : red (Matrix.of A) = LinearMap.toMatrix' p := by
        ext i j
        exact hA i j
      refine ⟨Matrix.of A, ?_⟩
      rw [hAM, ← toLin'_apply', toLin'_toMatrix', LinearMap.ker_comp, Submodule.ker_subtype, Submodule.comap_bot,
        Submodule.ker_projectionOnto]
    apply le_antisymm
    · obtain ⟨y, hy⟩ := key2 (colSp s κ₂)
      rw [← hy, key, hy]
    · obtain ⟨y, hy⟩ := key2 (colSp s κ₁)
      rw [← hy, ← key, hy]

theorem sum_intInd_cosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D D' : Type) [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) RK, IsRepsK (torusElt k D ϖ (-indic s)) RK → ∀ y : Matrix D' D k, ((¬ ∀ i j, y i j ∈ 𝒪[k]) → ∑ g ∈ RK, ParHecke.intInd (y * g.1) = 0) ∧ ∀ y₀ : Matrix D' D 𝒪[k], y = y₀.map (algebraMap 𝒪[k] k) → ∑ g ∈ RK, ParHecke.intInd (y * g.1) = (Nat.card {U : Submodule 𝓀[k] (D → 𝓀[k]) // U ≤ LinearMap.ker (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin ∧ Module.finrank 𝓀[k] U = s.card} : ℂ) := by
  intro k _ _ _ _ D D' _ _ _ _ ϖ hϖ s RK hR y
  classical
  set g₀ := torusElt k D ϖ (-indic s) with hg₀
  have hex : ∀ g : RK, ∃ κ : GL D 𝒪[k], ∃ κ' ∈ KO k D, g.1 = incG κ * g₀ * κ' := by
    intro g
    obtain ⟨_, ⟨κ, rfl⟩, κ', hκ', e⟩ := hR.1 g.1 g.2
    exact ⟨κ, κ', hκ', e⟩
  choose κ κ' hκ' hg using hex
  constructor
  · intro hy
    refine Finset.sum_eq_zero fun g hgR => ?_
    rw [ParHecke.intInd, if_neg]
    intro h
    apply hy
    have e : g = incG (κ ⟨g, hgR⟩) * g₀ * κ' ⟨g, hgR⟩ := hg ⟨g, hgR⟩
    rw [e, Units.val_mul, ← Matrix.mul_assoc, int_mul_KO_iff (hκ' _)] at h
    have := int_mul h (int_coset_inv hϖ s (κ := incG (κ ⟨g, hgR⟩)) ⟨_, rfl⟩)
    rwa [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this
  · rintro y₀ rfl
    have hint : ∀ g : RK, (∀ i j, (inc y₀ * g.1.1) i j ∈ 𝒪[k]) ↔ colSp s (κ g) ≤ LinearMap.ker (red y₀).mulVecLin := by
      intro g
      rw [← int_iff_colSp hϖ, hg g, Units.val_mul, ← Matrix.mul_assoc, int_mul_KO_iff (hκ' g)]
    have hco : ∀ (g : RK) (c : GL D 𝒪[k]), g.1⁻¹ * (incG c * g₀) ∈ KO k D ↔ colSp s (κ g) = colSp s c := by
      intro g c
      rw [colSp_eq_iff hϖ, hg g, _root_.mul_inv_rev, mul_assoc, (KO k D).mul_mem_cancel_left (inv_mem (hκ' g))]
    let f : {g : RK // ∀ i j, (inc y₀ * g.1.1) i j ∈ 𝒪[k]} → {U : Submodule 𝓀[k] (D → 𝓀[k]) // U ≤ LinearMap.ker (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin ∧ Module.finrank 𝓀[k] U = s.card} :=
      fun g => ⟨colSp s (κ g.1), (hint g.1).1 g.2, finrank_colSp s _⟩
    have hf : Function.Bijective f := by
      constructor
      · intro g₁ g₂ h
        have h' : colSp s (κ g₁.1) = colSp s (κ g₂.1) := congrArg Subtype.val h
        have := (hR.2 (incG (κ g₂.1)) ⟨_, rfl⟩).unique ⟨g₁.1.2, (hco _ _).2 h'⟩ ⟨g₂.1.2, (hco _ _).2 rfl⟩
        exact Subtype.ext (Subtype.ext this)
      · rintro ⟨U, hU, hd⟩
        obtain ⟨c, rfl⟩ := exists_colSp s U hd
        obtain ⟨g, ⟨hgR, hgc⟩, -⟩ := hR.2 (incG c) ⟨_, rfl⟩
        have e := (hco ⟨g, hgR⟩ c).1 hgc
        exact ⟨⟨⟨g, hgR⟩, (hint _).2 (e ▸ hU)⟩, Subtype.ext e⟩
    rw [← Nat.card_eq_of_bijective f hf, ← Finset.sum_coe_sort, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [ParHecke.intInd]
    rw [Finset.sum_boole]

end GlobalTheory.ParHecke.CosetSub

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralIndicatorCosetsKernelSubspacesStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_integralIndicator_cosets_kernel_subspaces : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D D' : Type) [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) RK, IsRepsK (torusElt k D ϖ (-indic s)) RK → ∀ y : Matrix D' D k, ((¬ ∀ i j, y i j ∈ 𝒪[k]) → ∑ g ∈ RK, intInd (y * g.1) = 0) ∧ ∀ y₀ : Matrix D' D 𝒪[k], y = y₀.map (algebraMap 𝒪[k] k) → ∑ g ∈ RK, intInd (y * g.1) = (Nat.card {U : Submodule 𝓀[k] (D → 𝓀[k]) // U ≤ LinearMap.ker (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin ∧ Module.finrank 𝓀[k] U = s.card} : ℂ) := by
  first | exact @GlobalTheory.ParHecke.CosetSub.sum_intInd_cosets | exact GlobalTheory.ParHecke.CosetSub.sum_intInd_cosets | (intros; apply GlobalTheory.ParHecke.CosetSub.sum_intInd_cosets <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralIndicatorCosetsSubspacesContaining
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralIndicatorCosetsSubspacesContaining
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ParHecke.CosetSubL

theorem exists_equiv_map_eq {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (W W' : Submodule F V)
    (h : Module.finrank F W = Module.finrank F W') :
    ∃ e : V ≃ₗ[F] V, W.map e.toLinearMap = W' := by
  obtain ⟨U, hU⟩ := W.exists_isCompl
  obtain ⟨U', hU'⟩ := W'.exists_isCompl
  have h1 := Submodule.finrank_add_eq_of_isCompl hU
  have h2 := Submodule.finrank_add_eq_of_isCompl hU'
  have h3 : Module.finrank F U = Module.finrank F U' := by omega
  let a : W ≃ₗ[F] W' := LinearEquiv.ofFinrankEq _ _ h
  let b : U ≃ₗ[F] U' := LinearEquiv.ofFinrankEq _ _ h3
  let e : V ≃ₗ[F] V := (Submodule.prodEquivOfIsCompl W U hU).symm ≪≫ₗ (a.prodCongr b) ≪≫ₗ
    Submodule.prodEquivOfIsCompl W' U' hU'
  have he : ∀ w : W, e w = a w := by
    intro w
    simp [e]
  refine ⟨e, ?_⟩
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    have := he ⟨w, hw⟩
    change e w ∈ W'
    simp only at this
    rw [this]
    exact (a ⟨w, hw⟩).2
  · intro w hw
    refine ⟨a.symm ⟨w, hw⟩, (a.symm ⟨w, hw⟩).2, ?_⟩
    change e _ = w
    rw [he]
    simp

theorem exists_gl_map_eq (O : Type) [CommRing O] [IsLocalRing O] (n : Type) [Fintype n] [DecidableEq n]
    (W W' : Submodule (IsLocalRing.ResidueField O) (n → IsLocalRing.ResidueField O))
    (h : Module.finrank (IsLocalRing.ResidueField O) W =
      Module.finrank (IsLocalRing.ResidueField O) W') :
    ∃ g : GL n O, W.map (g.1.map (IsLocalRing.residue O)).mulVecLin = W' := by
  obtain ⟨e, he⟩ := exists_equiv_map_eq W W' h
  let M : Matrix n n (IsLocalRing.ResidueField O) := LinearMap.toMatrix' e.toLinearMap
  choose A hA using fun i j => IsLocalRing.residue_surjective (R := O) (M i j)
  have hAM : (Matrix.of A).map (IsLocalRing.residue O) = M := by
    ext i j
    exact hA i j
  have hM : M.det ≠ 0 := by
    have : M.det = LinearMap.det e.toLinearMap := LinearMap.det_toMatrix' _
    rw [this]
    exact (LinearEquiv.isUnit_det' e).ne_zero
  have hu : IsUnit (Matrix.of A).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    change ((Matrix.of A).map (IsLocalRing.residue O)).det ≠ 0
    rw [hAM]
    exact hM
  obtain ⟨g, hg⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hu
  refine ⟨g, ?_⟩
  rw [hg, hAM, ← he]
  congr 1
  exact Matrix.toLin'_toMatrix' e.toLinearMap

theorem exists_range_eq (F : Type) [Field F] (n : Type) [Fintype n] [DecidableEq n] (U : Submodule F (n → F)) :
    ∃ M : Matrix n n F, LinearMap.range M.mulVecLin = U := by
  obtain ⟨U', hU⟩ := U.exists_isCompl
  refine ⟨LinearMap.toMatrix' (U.subtype ∘ₗ Submodule.projectionOnto U U' hU), ?_⟩
  rw [← toLin'_apply', toLin'_toMatrix', LinearMap.range_comp, Submodule.range_projectionOnto, Submodule.map_subtype_top]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n m : Type} [Fintype n] [DecidableEq n]

def projE (F : Type) [Field F] (s : Finset n) : Matrix n n F := diagonal fun i => if i ∈ s then 1 else 0

theorem rank_projE (F : Type) [Field F] (s : Finset n) : (projE F s).rank = s.card := by
  classical
  rw [projE, rank_diagonal]
  rw [Fintype.card_subtype]
  congr 1
  ext i
  by_cases h : i ∈ s <;> simp [h]

abbrev red {a b : Type} (M : Matrix a b 𝒪[k]) : Matrix a b 𝓀[k] := M.map (IsLocalRing.residue 𝒪[k])

abbrev inc {a b : Type} (M : Matrix a b 𝒪[k]) : Matrix a b k := M.map (algebraMap 𝒪[k] k)

abbrev incG (κ : GL n 𝒪[k]) : GL n k := GeneralLinearGroup.map (algebraMap 𝒪[k] k) κ

theorem isUnit_red (κ : GL n 𝒪[k]) : IsUnit (red (k := k) κ.1).det := by
  have : (red (k := k) κ.1).det = IsLocalRing.residue 𝒪[k] κ.1.det := (RingHom.map_det _ _).symm
  rw [this]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 κ.isUnit).map _

def rowKer (s : Finset n) (κ : GL n 𝒪[k]) : Submodule 𝓀[k] (n → 𝓀[k]) :=
  LinearMap.ker (projE 𝓀[k] s * red (κ⁻¹).1).mulVecLin

theorem finrank_rowKer (s : Finset n) (κ : GL n 𝒪[k]) :
    Module.finrank 𝓀[k] (rowKer s κ) + s.card = Fintype.card n := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (projE 𝓀[k] s * red (k := k) (κ⁻¹).1).mulVecLin
  have h2 : (projE 𝓀[k] s * red (k := k) (κ⁻¹).1).rank = s.card := by
    rw [← rank_projE 𝓀[k] s]
    exact rank_mul_eq_left_of_isUnit_det _ _ (isUnit_red κ⁻¹)
  rw [Matrix.rank] at h2
  rw [Module.finrank_fintype_fun_eq_card] at h1
  unfold rowKer
  omega

end GlobalTheory.ParHecke.CosetSubL

namespace GlobalTheory.ParHecke.CosetSubL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n m : Type} [Fintype n] [DecidableEq n]

theorem inv_mul_mem_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (x : 𝒪[k]) :
    (ϖ : k)⁻¹ * (x : k) ∈ 𝒪[k] ↔ IsLocalRing.residue 𝒪[k] x = 0 := by
  rw [mul_comm, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one, Valuation.mem_integer_iff, ← le_uniformizer_iff, ← hϖ,
    map_mul, map_inv₀, mul_inv_le_iff₀ (by rw [hϖ]; exact uniformizer_pos), one_mul]

theorem torus_inv (ϖ : kˣ) (s : Finset n) : (torusElt k n ϖ (indic s))⁻¹ = torusElt k n ϖ (-indic s) := by
  rw [inv_eq_iff_mul_eq_one]
  apply Units.ext
  rw [Units.val_mul, val_torusElt, val_torusElt, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
  congr 1
  ext i
  rw [← zpow_add₀ ϖ.ne_zero]
  simp

theorem torus_inv_mul_int_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset n) (M : Matrix n m 𝒪[k]) :
    (∀ i j, (((torusElt k n ϖ (indic s))⁻¹).1 * inc M) i j ∈ 𝒪[k]) ↔ projE 𝓀[k] s * red M = 0 := by
  rw [torus_inv, val_torusElt, projE, ← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [diagonal_mul, diagonal_mul]
  by_cases h : i ∈ s
  · have := inv_mul_mem_iff hϖ (M i j)
    simp only [indic, h, Pi.neg_apply, if_true, _root_.zpow_neg, zpow_one, one_mul, map_apply, Matrix.zero_apply]
    exact this
  · simp only [indic, h, Pi.neg_apply, if_false, neg_zero, zpow_zero, one_mul, zero_mul, map_apply, Matrix.zero_apply, iff_true]
    exact (M i j).2

omit [DecidableEq n] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem int_mul {a b : Type} {A : Matrix a n k} {B : Matrix n b k} (hA : ∀ i j, A i j ∈ 𝒪[k]) (hB : ∀ i j, B i j ∈ 𝒪[k]) :
    ∀ i j, (A * B) i j ∈ 𝒪[k] := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hA i l) (hB l j)

theorem int_of_KO {g : GL n k} (hg : g ∈ KO k n) : ∀ i j, g.1 i j ∈ 𝒪[k] := by
  obtain ⟨κ, rfl⟩ := hg
  intro i j
  exact (κ.1 i j).2

theorem KO_of_int {g : GL n k} (hg : ∀ i j, g.1 i j ∈ 𝒪[k]) (hg' : ∀ i j, (g⁻¹).1 i j ∈ 𝒪[k]) : g ∈ KO k n := by
  let A : Matrix n n 𝒪[k] := fun i j => ⟨_, hg i j⟩
  let B : Matrix n n 𝒪[k] := fun i j => ⟨_, hg' i j⟩
  have hA : inc A = g.1 := rfl
  have hB : inc B = (g⁻¹).1 := rfl
  have inj : Function.Injective (inc : Matrix n n 𝒪[k] → Matrix n n k) := map_injective Subtype.val_injective
  have h1 : inc (1 : Matrix n n 𝒪[k]) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext hA⟩
  · rw [h1, inc, Matrix.map_mul]
    change g.1 * (g⁻¹).1 = 1
    simp
  · rw [h1, inc, Matrix.map_mul]
    change (g⁻¹).1 * g.1 = 1
    simp

theorem KO_mul_int_iff {A : Matrix n m k} {g : GL n k} (hg : g ∈ KO k n) :
    (∀ i j, (g.1 * A) i j ∈ 𝒪[k]) ↔ ∀ i j, A i j ∈ 𝒪[k] := by
  refine ⟨fun h => ?_, fun h => int_mul (int_of_KO hg) h⟩
  have := int_mul (int_of_KO (inv_mem hg)) h
  rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this

theorem int_torus {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset n) :
    ∀ i j, (torusElt k n ϖ (indic s)).1 i j ∈ 𝒪[k] := by
  intro i j
  rw [val_torusElt, diagonal_apply]
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  split_ifs with h
  · by_cases h' : i ∈ s
    · simpa [indic, h', Valuation.mem_integer_iff] using hlt.le
    · simp [indic, h']
  · exact zero_mem _

theorem int_coset {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset n) (κ : GL n 𝒪[k]) :
    ∀ i j, (incG κ * torusElt k n ϖ (indic s)).1 i j ∈ 𝒪[k] := by
  rw [Units.val_mul]
  exact int_mul (int_of_KO ⟨κ, rfl⟩) (int_torus hϖ s)

theorem int_iff_rowKer [Fintype m] [DecidableEq m] {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset n) (y₀ : Matrix n m 𝒪[k])
    (κ : GL n 𝒪[k]) :
    (∀ i j, (((incG κ * torusElt k n ϖ (indic s))⁻¹).1 * inc y₀) i j ∈ 𝒪[k]) ↔
      LinearMap.range (red y₀).mulVecLin ≤ rowKer s κ := by
  have e1 : (incG κ * torusElt k n ϖ (indic s))⁻¹ = (torusElt k n ϖ (indic s))⁻¹ * incG κ⁻¹ := by
    rw [_root_.mul_inv_rev]
    congr 1
  have e2 : (incG κ⁻¹).1 * inc y₀ = inc ((κ⁻¹).1 * y₀) := Matrix.map_mul.symm
  have e3 : red ((κ⁻¹).1 * y₀) = red (k := k) (κ⁻¹).1 * red y₀ := Matrix.map_mul
  rw [e1, Units.val_mul, Matrix.mul_assoc, e2, torus_inv_mul_int_iff hϖ, rowKer, LinearMap.range_le_ker_iff,
    ← mulVecLin_mul, e3, ← Matrix.mul_assoc, ← toLin'_apply', map_eq_zero_iff _ toLin'.injective]

theorem int_quot_of_le {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset n) (κ₁ κ₂ : GL n 𝒪[k])
    (h : rowKer s κ₂ ≤ rowKer s κ₁) :
    ∀ i j, ((incG κ₁ * torusElt k n ϖ (indic s))⁻¹ * (incG κ₂ * torusElt k n ϖ (indic s))).1 i j ∈ 𝒪[k] := by
  let y : Matrix n n 𝒪[k] := fun i j => ⟨_, int_coset hϖ s κ₂ i j⟩
  have hy : inc y = (incG κ₂ * torusElt k n ϖ (indic s)).1 := rfl
  rw [Units.val_mul, ← hy, int_iff_rowKer hϖ]
  refine le_trans ?_ h
  rw [← int_iff_rowKer hϖ, hy, ← Units.val_mul, inv_mul_cancel]
  exact int_of_KO (one_mem _)

theorem rowKer_eq_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset n) (κ₁ κ₂ : GL n 𝒪[k]) :
    rowKer s κ₁ = rowKer s κ₂ ↔
      (incG κ₁ * torusElt k n ϖ (indic s))⁻¹ * (incG κ₂ * torusElt k n ϖ (indic s)) ∈ KO k n := by
  constructor
  · intro h
    refine KO_of_int (int_quot_of_le hϖ s κ₁ κ₂ h.ge) ?_
    rw [_root_.mul_inv_rev, inv_inv]
    exact int_quot_of_le hϖ s κ₂ κ₁ h.le
  · intro h
    set t := torusElt k n ϖ (indic s)
    have key : ∀ y : Matrix n n 𝒪[k], LinearMap.range (red y).mulVecLin ≤ rowKer s κ₁ ↔
        LinearMap.range (red y).mulVecLin ≤ rowKer s κ₂ := by
      intro y
      have e : (incG κ₂ * t)⁻¹ = ((incG κ₁ * t)⁻¹ * (incG κ₂ * t))⁻¹ * (incG κ₁ * t)⁻¹ := by group
      rw [← int_iff_rowKer hϖ, ← int_iff_rowKer hϖ, e, Units.val_mul, Matrix.mul_assoc, KO_mul_int_iff (inv_mem h)]
    have key2 : ∀ U : Submodule 𝓀[k] (n → 𝓀[k]), ∃ y : Matrix n n 𝒪[k], LinearMap.range (red y).mulVecLin = U := by
      intro U
      obtain ⟨M, hM⟩ := exists_range_eq 𝓀[k] n U
      choose A hA using fun i j => IsLocalRing.residue_surjective (R := 𝒪[k]) (M i j)
      have hAM : red (k := k) (Matrix.of A) = M := by
        ext i j
        exact hA i j
      exact ⟨Matrix.of A, by rw [hAM, hM]⟩
    apply le_antisymm
    · obtain ⟨y, hy⟩ := key2 (rowKer s κ₁)
      rw [← hy, ← key, hy]
    · obtain ⟨y, hy⟩ := key2 (rowKer s κ₂)
      rw [← hy, key, hy]

theorem exists_rowKer (s : Finset n) (U : Submodule 𝓀[k] (n → 𝓀[k]))
    (hU : Module.finrank 𝓀[k] U + s.card = Fintype.card n) : ∃ κ : GL n 𝒪[k], rowKer s κ = U := by
  have h0 : Module.finrank 𝓀[k] (LinearMap.ker (projE 𝓀[k] s).mulVecLin) + s.card = Fintype.card n := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (projE 𝓀[k] s).mulVecLin
    have h2 := rank_projE 𝓀[k] s
    rw [Matrix.rank] at h2
    rw [Module.finrank_fintype_fun_eq_card] at h1
    omega
  obtain ⟨g, hg⟩ := exists_gl_map_eq 𝒪[k] n U (LinearMap.ker (projE 𝓀[k] s).mulVecLin) (by omega)
  refine ⟨g⁻¹, ?_⟩
  have hinj : Function.Injective (red (k := k) g.1).mulVecLin :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_red g))
  rw [rowKer, inv_inv, mulVecLin_mul, LinearMap.ker_comp, ← hg, Submodule.comap_map_eq_of_injective hinj]

end GlobalTheory.ParHecke.CosetSubL


open GlobalTheory.ParHecke.CosetSubL in
theorem GlobalTheory.ParHecke.CosetSubL.sum_intInd_cosets_up : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D D' : Type) [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D') RK, IsRepsK (torusElt k D' ϖ (indic s)) RK → ∀ y : Matrix D' D k, ((¬ ∀ i j, y i j ∈ 𝒪[k]) → ∑ g ∈ RK, intInd ((g⁻¹).1 * y) = 0) ∧ ∀ y₀ : Matrix D' D 𝒪[k], y = y₀.map (algebraMap 𝒪[k] k) → ∑ g ∈ RK, intInd ((g⁻¹).1 * y) = (Nat.card {U : Submodule 𝓀[k] (D' → 𝓀[k]) // LinearMap.range (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin ≤ U ∧ Module.finrank 𝓀[k] U + s.card = Fintype.card D'} : ℂ) := by
  intro k _ _ _ _ D D' _ _ _ _ ϖ hϖ s RK hR y
  classical
  set g₀ := torusElt k D' ϖ (indic s) with hg₀
  have hex : ∀ g : RK, ∃ κ : GL D' 𝒪[k], ∃ κ' ∈ KO k D', g.1 = incG κ * g₀ * κ' := by
    intro g
    obtain ⟨_, ⟨κ, rfl⟩, κ', hκ', e⟩ := hR.1 g.1 g.2
    exact ⟨κ, κ', hκ', e⟩
  choose κ κ' hκ' hg using hex
  constructor
  · intro hy
    refine Finset.sum_eq_zero fun g hgR => ?_
    rw [ParHecke.intInd, if_neg]
    intro h
    apply hy
    have hgi : ∀ i j, g.1 i j ∈ 𝒪[k] := by
      have e : g = incG (κ ⟨g, hgR⟩) * g₀ * κ' ⟨g, hgR⟩ := hg ⟨g, hgR⟩
      rw [e, Units.val_mul]
      exact int_mul (int_coset hϖ s _) (int_of_KO (hκ' _))
    have := int_mul hgi h
    rwa [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul] at this
  · rintro y₀ rfl
    have hint : ∀ g : RK, (∀ i j, ((g.1⁻¹).1 * inc y₀) i j ∈ 𝒪[k]) ↔
        LinearMap.range (red y₀).mulVecLin ≤ rowKer s (κ g) := by
      intro g
      rw [← int_iff_rowKer hϖ, hg g, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc,
        KO_mul_int_iff (inv_mem (hκ' g))]
    have hco : ∀ (g : RK) (c : GL D' 𝒪[k]), g.1⁻¹ * (incG c * g₀) ∈ KO k D' ↔ rowKer s (κ g) = rowKer s c := by
      intro g c
      rw [rowKer_eq_iff hϖ, hg g, _root_.mul_inv_rev, mul_assoc, (KO k D').mul_mem_cancel_left (inv_mem (hκ' g))]
    let f : {g : RK // ∀ i j, ((g.1⁻¹).1 * inc y₀) i j ∈ 𝒪[k]} → {U : Submodule 𝓀[k] (D' → 𝓀[k]) // LinearMap.range (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin ≤ U ∧ Module.finrank 𝓀[k] U + s.card = Fintype.card D'} :=
      fun g => ⟨rowKer s (κ g.1), (hint g.1).1 g.2, finrank_rowKer s _⟩
    have hf : Function.Bijective f := by
      constructor
      · intro g₁ g₂ h
        have h' : rowKer s (κ g₁.1) = rowKer s (κ g₂.1) := congrArg Subtype.val h
        have := (hR.2 (incG (κ g₂.1)) ⟨_, rfl⟩).unique ⟨g₁.1.2, (hco _ _).2 h'⟩ ⟨g₂.1.2, (hco _ _).2 rfl⟩
        exact Subtype.ext (Subtype.ext this)
      · rintro ⟨U, hU, hd⟩
        obtain ⟨c, rfl⟩ := exists_rowKer s U hd
        obtain ⟨g, ⟨hgR, hgc⟩, -⟩ := hR.2 (incG c) ⟨_, rfl⟩
        have e := (hco ⟨g, hgR⟩ c).1 hgc
        exact ⟨⟨⟨g, hgR⟩, (hint _).2 (e ▸ hU)⟩, Subtype.ext e⟩
    rw [← Nat.card_eq_of_bijective f hf, ← Finset.sum_coe_sort, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [ParHecke.intInd]
    rw [Finset.sum_boole]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralIndicatorCosetsSubspacesContainingStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_integralIndicator_cosets_subspaces_containing : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D D' : Type) [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D') RK, IsRepsK (GlobalTheory.GLDoubling.torusElt k D' ϖ (indic s)) RK → ∀ y : Matrix D' D k, ((¬ ∀ i j, y i j ∈ 𝒪[k]) → ∑ g ∈ RK, GlobalTheory.ParHecke.intInd ((g⁻¹).1 * y) = 0) ∧ ∀ y₀ : Matrix D' D 𝒪[k], y = y₀.map (algebraMap 𝒪[k] k) → ∑ g ∈ RK, GlobalTheory.ParHecke.intInd ((g⁻¹).1 * y) = (Nat.card {U : Submodule 𝓀[k] (D' → 𝓀[k]) // LinearMap.range (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin ≤ U ∧ Module.finrank 𝓀[k] U + s.card = Fintype.card D'} : ℂ) := by
  first | exact @GlobalTheory.ParHecke.CosetSubL.sum_intInd_cosets_up | exact GlobalTheory.ParHecke.CosetSubL.sum_intInd_cosets_up | (intros; apply GlobalTheory.ParHecke.CosetSubL.sum_intInd_cosets_up <;> assumption)
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem GlobalTheory.ParHecke.heckeIdentity_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D D' : Type) [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ t : ℕ, Fintype.card D' = Fintype.card D + t → ∀ (s : Finset D') RK, IsRepsK (torusElt k D' ϖ (indic s)) RK → ∀ (sn : ℕ → Finset D) (Rn : ℕ → Finset (GL D k)), (∀ n ≤ Fintype.card D, (sn n).card = n ∧ IsRepsK (torusElt k D ϖ (-indic (sn n))) (Rn n)) → ∀ y : Matrix D' D k, ∑ g ∈ RK, intInd ((g⁻¹).1 * y) = ∑ n ∈ Finset.range (Fintype.card D + 1), (if n ≤ s.card then ((resCard k ^ (n * (t - (s.card - n))) * Formalism.L2.Col.gaussBin (resCard k) t (s.card - n) : ℕ) : ℂ) else 0) * ∑ g ∈ Rn n, intInd (y * g.1) := by
  intro k _ _ _ _ D D' _ _ _ _ ϖ hϖ t ht s RK hRK sn Rn hRn y
  have hL := GlobalTheory.T.sum_integralIndicator_cosets_subspaces_containing k D D' ϖ hϖ s RK hRK y
  by_cases hy : ∀ i j, y i j ∈ 𝒪[k]
  · let y₀ : Matrix D' D 𝒪[k] := fun i j => ⟨y i j, hy i j⟩
    have hy₀ : y = y₀.map (algebraMap 𝒪[k] k) := by
      ext i j; rfl
    rw [hL.2 y₀ hy₀]
    have hR : ∀ n ∈ Finset.range (Fintype.card D + 1), ∑ g ∈ Rn n, intInd (y * g.1) =
        (Nat.card {U : Submodule 𝓀[k] (D → 𝓀[k]) // U ≤ LinearMap.ker (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin ∧ Module.finrank 𝓀[k] U = n} : ℂ) := by
      intro n hn
      have hn' : n ≤ Fintype.card D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      obtain ⟨hc, hr⟩ := hRn n hn'
      rw [(GlobalTheory.T.sum_integralIndicator_cosets_kernel_subspaces k D D' ϖ hϖ (sn n) (Rn n) hr y).2 y₀ hy₀, hc]
    rw [Finset.sum_congr rfl (fun n hn => by rw [hR n hn])]
    have hC := GlobalTheory.T.card_subspaces_containing_range_qVandermonde 𝓀[k] (D → 𝓀[k]) (D' → 𝓀[k]) (y₀.map (IsLocalRing.residue 𝒪[k])).mulVecLin t s.card
      (by simp only [Module.finrank_fintype_fun_eq_card]; exact ht)
      (by simp only [Module.finrank_fintype_fun_eq_card]; exact Finset.card_le_univ s)
    simp only [Module.finrank_fintype_fun_eq_card] at hC
    rw [hC]
    push_cast
    refine Finset.sum_congr rfl (fun n _ => ?_)
    split_ifs <;> simp [resCard]
  · rw [hL.1 hy]
    symm
    apply Finset.sum_eq_zero
    intro n hn
    have hn' : n ≤ Fintype.card D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    rw [(GlobalTheory.T.sum_integralIndicator_cosets_kernel_subspaces k D D' ϖ hϖ (sn n) (Rn n) (hRn n hn').2 y).1 hy, mul_zero]

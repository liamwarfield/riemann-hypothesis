module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsNum
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsCnt
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsTrm

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsSiz
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

open Classical

def sumOfSquaredModuli {κ : Type} [Fintype κ] (y : κ → ℂ) : ℝ := ∏ v, ((max 1 (‖y v‖ / 1)) ^ 3)⁻¹

theorem rows_psi_nonneg {κ : Type} [Fintype κ] (y : κ → ℂ) : 0 ≤ sumOfSquaredModuli y :=
  Finset.prod_nonneg fun _ _ => inv_nonneg.2 (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) 3)

theorem rows_finsum_le {κ : Type} [Fintype κ] (Λ : AddSubgroup (κ → ℂ))
    (hΛ : ∀ x ∈ Λ, x ≠ 0 → 1 ≤ ∏ v, ‖x v‖) (T : Finset (κ → ℂ)) (hT : ∀ y ∈ T, y ∈ Λ) :
    ∑ y ∈ T, sumOfSquaredModuli y ≤ (41 : ℝ) ^ Fintype.card κ := by
  obtain ⟨hs, hle⟩ := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.latticeSum κ Λ 1 le_rfl hΛ
  have e : ∑ y ∈ T.subtype (fun y => y ∈ Λ), sumOfSquaredModuli (y : κ → ℂ) = ∑ y ∈ T, sumOfSquaredModuli y :=
    Finset.sum_subtype_of_mem (fun y => sumOfSquaredModuli y) hT
  rw [← e]
  have h1 : ∑ y ∈ T.subtype (fun y => y ∈ Λ), sumOfSquaredModuli (y : κ → ℂ) ≤
      ∑' y : Λ, ∏ v, ((max 1 (‖(y : κ → ℂ) v‖ / 1)) ^ 3)⁻¹ :=
    Summable.sum_le_tsum (f := fun y : Λ => ∏ v, ((max 1 (‖(y : κ → ℂ) v‖ / 1)) ^ 3)⁻¹) _
      (fun y _ => rows_psi_nonneg (y : κ → ℂ)) hs
  refine h1.trans (hle.trans ?_)
  norm_num

theorem rows_sum_prod_le {α ι κ : Type} [Fintype ι] [Fintype κ] (Λ : ι → AddSubgroup (κ → ℂ))
    (hΛ : ∀ i, ∀ x ∈ Λ i, x ≠ 0 → 1 ≤ ∏ v, ‖x v‖) (S : Finset α) (x : α → ι → κ → ℂ)
    (hx : ∀ Z ∈ S, ∀ i, x Z i ∈ Λ i) (hinj : ∀ Z ∈ S, ∀ Z' ∈ S, x Z = x Z' → Z = Z') :
    ∑ Z ∈ S, ∏ i, sumOfSquaredModuli (x Z i) ≤ ((41 : ℝ) ^ Fintype.card κ) ^ Fintype.card ι := by
  set T : ι → Finset (κ → ℂ) := fun i => S.image (fun Z => x Z i) with hT
  have e1 : ∑ Z ∈ S, ∏ i, sumOfSquaredModuli (x Z i) = ∑ y ∈ S.image x, ∏ i, sumOfSquaredModuli (y i) :=
    (Finset.sum_image (f := fun y : ι → κ → ℂ => ∏ i, sumOfSquaredModuli (y i)) (fun Z hZ Z' hZ' h => hinj Z hZ Z' hZ' h)).symm
  have sub : S.image x ⊆ Fintype.piFinset T := by
    intro y hy
    obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.1 hy
    exact Fintype.mem_piFinset.2 fun i => Finset.mem_image.2 ⟨Z, hZ, rfl⟩
  have e2 : ∑ y ∈ S.image x, ∏ i, sumOfSquaredModuli (y i) ≤ ∑ y ∈ Fintype.piFinset T, ∏ i, sumOfSquaredModuli (y i) :=
    Finset.sum_le_sum_of_subset_of_nonneg sub fun y _ _ => Finset.prod_nonneg fun i _ => rows_psi_nonneg _
  have e3 : ∑ y ∈ Fintype.piFinset T, ∏ i, sumOfSquaredModuli (y i) = ∏ i, ∑ y ∈ T i, sumOfSquaredModuli y :=
    (Finset.prod_univ_sum T (fun _ y => sumOfSquaredModuli y)).symm
  rw [e1]
  refine e2.trans ?_
  rw [e3]
  calc ∏ i, ∑ y ∈ T i, sumOfSquaredModuli y ≤ ∏ _i : ι, (41 : ℝ) ^ Fintype.card κ :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun y _ => rows_psi_nonneg y) fun i _ =>
          rows_finsum_le (Λ i) (hΛ i) (T i) fun y hy => by
            obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.1 hy
            exact hx Z hZ i
    _ = ((41 : ℝ) ^ Fintype.card κ) ^ Fintype.card ι := by
        rw [Finset.prod_const, Finset.card_univ]

end Abstract

section Gram

variable {D : D7}

def gramEntryFunction (D : D7) (Z : GramM D) (i : Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) : D.what₂.Tau → ℂ :=
  fun τ => ((rhoF D i.1 * rhoF D i.2 : ℝ) : ℂ) * embS D τ (Z i.1 i.2)

theorem rows_rhoF_pos (hrd : 0 < D.host.rdE) (a : Fin (D.R.rS + 1)) : 0 < rhoF D a := by
  unfold rhoF
  exact Real.rpow_pos_of_pos hrd _

theorem rows_norm_entry (hrd : 0 < D.host.rdE) (Z : GramM D) (i : Fin (D.R.rS + 1) × Fin (D.R.rS + 1))
    (τ : D.what₂.Tau) : ‖gramEntryFunction D Z i τ‖ = ‖embS D τ (Z i.1 i.2)‖ * (rhoF D i.1 * rhoF D i.2) := by
  unfold gramEntryFunction
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (rows_rhoF_pos hrd _) (rows_rhoF_pos hrd _)), mul_comm]

def rows_one (N : ℕ) (a : Fin N) : Fin 1 ↪o Fin N :=
  OrderEmbedding.ofStrictMono (fun _ => a) (fun x y h => absurd h (by rw [Subsingleton.elim x y]; exact lt_irrefl _))

theorem rows_one_apply (N : ℕ) (a : Fin N) (x : Fin 1) : rows_one N a x = a := rfl

theorem rows_absMinor_one (Z : GramM D) (a b : Fin (D.R.rS + 1)) (τ : D.what₂.Tau) :
    UnitaryVolumeMass.absMinor D Z (rows_one _ a) (rows_one _ b) τ = ‖embS D τ (Z a b)‖ * (rhoF D a * rhoF D b) := by
  unfold UnitaryVolumeMass.absMinor
  rw [Matrix.det_fin_one]
  simp [rows_one_apply]

theorem rows_det_one (Z : GramM D) (a b : Fin (D.R.rS + 1)) :
    (Z.submatrix (rows_one _ a) (rows_one _ b)).det = Z a b := by
  rw [Matrix.det_fin_one]
  simp [rows_one_apply]

theorem rows_entry_inj (hrd : 0 < D.host.rdE) (hf : 0 < D.R.f) (Z Z' : GramM D)
    (h : gramEntryFunction D Z = gramEntryFunction D Z') : Z = Z' := by
  have hc : 0 < Fintype.card D.what₂.Tau := by rw [D.what₂.card_Tau]; exact hf
  obtain ⟨τ⟩ := Fintype.card_pos_iff.1 hc
  refine Matrix.ext fun a b => ?_
  have h1 := congrFun (congrFun h (a, b)) τ
  unfold gramEntryFunction at h1
  have hne : (((rhoF D a * rhoF D b : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos (rows_rhoF_pos hrd a) (rows_rhoF_pos hrd b)).ne'
  exact (embS D τ).injective (mul_left_cancel₀ hne h1)

theorem rows_psi_ge (hrd : 0 < D.host.rdE) (Z : GramM D) (M : ℝ) (hM : 1 ≤ M)
    (hred : ∀ (j : ℕ) (I J : Fin j ↪o Fin (D.R.rS + 1)), (Z.submatrix I J).det ≠ 0 →
      ∏ τ, max 1 (UnitaryVolumeMass.absMinor D Z I J τ) ≤ M) (i : Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) :
    (M ^ 3)⁻¹ ≤ sumOfSquaredModuli (gramEntryFunction D Z i) := by
  have hP : ∏ τ, max 1 ‖gramEntryFunction D Z i τ‖ ≤ M := by
    by_cases h0 : Z i.1 i.2 = 0
    · have : ∀ τ, max 1 ‖gramEntryFunction D Z i τ‖ = 1 := fun τ => by
        rw [rows_norm_entry hrd, h0, map_zero, norm_zero, zero_mul]; exact max_eq_left zero_le_one
      rw [Finset.prod_congr rfl fun τ _ => this τ, Finset.prod_const_one]
      exact hM
    · have h := hred 1 (rows_one _ i.1) (rows_one _ i.2) (by rw [rows_det_one]; exact h0)
      refine le_trans (le_of_eq ?_) h
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [rows_absMinor_one, rows_norm_entry hrd]
  have hP0 : 0 < ∏ τ, max 1 ‖gramEntryFunction D Z i τ‖ :=
    Finset.prod_pos fun τ _ => lt_of_lt_of_le one_pos (le_max_left _ _)
  have e : sumOfSquaredModuli (gramEntryFunction D Z i) = ((∏ τ, max 1 ‖gramEntryFunction D Z i τ‖) ^ 3)⁻¹ := by
    unfold sumOfSquaredModuli
    rw [Finset.prod_inv_distrib, Finset.prod_pow]
    simp only [div_one]
  rw [e]
  exact inv_anti₀ (pow_pos hP0 3) (pow_le_pow_left₀ hP0.le hP 3)

theorem rows_sizeSum (X : TermTie D) {u u' : D.what₂.Word} (hE : wordPairEntriesInLattice X u u') (hrd : 0 < D.host.rdE)
    (hf : 0 < D.R.f) (S : Finset (GramM D)) (sg : GramM D → ℝ) (hsg : ∀ Z ∈ S, 1 ≤ sg Z) (B : ℝ) (hB : 1 ≤ B)
    (hterm : ∀ Z ∈ S, ∃ t : D.s.Term u u', D.s.Gterm t ≠ 0 ∧ D.s.relevant t ∧ ZEquiv (termGramMatrix X t) Z)
    (hred : ∀ Z ∈ S, ∀ (j : ℕ) (I J : Fin j ↪o Fin (D.R.rS + 1)), (Z.submatrix I J).det ≠ 0 →
      ∏ τ, max 1 (UnitaryVolumeMass.absMinor D Z I J τ) ≤ B * sg Z ^ 4)
    (e : ℝ) (he : 12 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ e) :
    ∑ Z ∈ S, sg Z ^ (-e) ≤ ((41 : ℝ) ^ D.R.f * B ^ 3) ^ ((D.R.rS + 1) ^ 2) := by
  classical
  choose Λ hΛ hmem using hE
  have hcard : Fintype.card (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) = (D.R.rS + 1) ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin, sq]
  have key := rows_sum_prod_le (fun i : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => Λ i.1 i.2)
    (fun i => hΛ i.1 i.2) S (fun Z => gramEntryFunction D Z)
    (fun Z hZ i => by
      obtain ⟨t, hG, hr, hz⟩ := hterm Z hZ
      exact hmem i.1 i.2 t Z hG hr hz)
    (fun Z _ Z' _ h => rows_entry_inj hrd hf Z Z' h)
  rw [hcard, D.what₂.card_Tau] at key
  have each : ∀ Z ∈ S, sg Z ^ (-e) ≤
      (B ^ 3) ^ ((D.R.rS + 1) ^ 2) * ∏ i : Fin (D.R.rS + 1) × Fin (D.R.rS + 1), sumOfSquaredModuli (gramEntryFunction D Z i) := by
    intro Z hZ
    have h1 := hsg Z hZ
    have s0 : 0 < sg Z := lt_of_lt_of_le one_pos h1
    have hM : 1 ≤ B * sg Z ^ 4 := by
      have : 1 ≤ sg Z ^ 4 := one_le_pow₀ h1
      nlinarith
    have hp : ((((B * sg Z ^ 4) ^ 3)⁻¹) ^ ((D.R.rS + 1) ^ 2)) ≤
        ∏ i : Fin (D.R.rS + 1) × Fin (D.R.rS + 1), sumOfSquaredModuli (gramEntryFunction D Z i) := by
      rw [← hcard, ← Finset.card_univ, ← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => rows_psi_ge hrd Z _ hM (hred Z hZ) i
    have hB3 : 0 < (B ^ 3) ^ ((D.R.rS + 1) ^ 2) := by positivity
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hp hB3.le)
    have e1 : (B ^ 3) ^ ((D.R.rS + 1) ^ 2) * (((B * sg Z ^ 4) ^ 3)⁻¹) ^ ((D.R.rS + 1) ^ 2) =
        (sg Z ^ (12 * (D.R.rS + 1) ^ 2))⁻¹ := by
      rw [← mul_pow, mul_pow B, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul, inv_pow, ← pow_mul,
        ← pow_mul]
      congr 2
      ring
    rw [e1, ← Real.rpow_natCast, ← Real.rpow_neg s0.le]
    refine Real.rpow_le_rpow_of_exponent_le h1 ?_
    push_cast
    linarith
  calc ∑ Z ∈ S, sg Z ^ (-e)
      ≤ ∑ Z ∈ S, (B ^ 3) ^ ((D.R.rS + 1) ^ 2) *
          ∏ i : Fin (D.R.rS + 1) × Fin (D.R.rS + 1), sumOfSquaredModuli (gramEntryFunction D Z i) := Finset.sum_le_sum each
    _ = (B ^ 3) ^ ((D.R.rS + 1) ^ 2) *
          ∑ Z ∈ S, ∏ i : Fin (D.R.rS + 1) × Fin (D.R.rS + 1), sumOfSquaredModuli (gramEntryFunction D Z i) := by
        rw [Finset.mul_sum]
    _ ≤ (B ^ 3) ^ ((D.R.rS + 1) ^ 2) * ((41 : ℝ) ^ D.R.f) ^ ((D.R.rS + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = ((41 : ℝ) ^ D.R.f * B ^ 3) ^ ((D.R.rS + 1) ^ 2) := by rw [mul_pow, mul_comm]

end Gram

section Reduced

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem rows_isTermF' (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) :
    IsTermF D (X.abelian₂ t) (lf D Y.F0) (X.fl' t) := by
  refine ⟨⟨X.lift' t, ?_, ?_⟩, Y.frame_ok t⟩
  · have := X.adm t
    rwa [Y.fl_eq t] at this
  · have h := X.G_eq t
    rw [Y.fl_eq t] at h
    rw [← h]
    exact (map_ne_zero_iff _ (algebraMap D.host.F D.host.E).injective).2 hG


include Y in
theorem rows_reduced_exists {C' Cl Cg cb Cu cT CT C0 A C : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hHH : UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0)
    (hrel : D.s.relevant t) :
    ∃ Z : GramM D, ZEquiv (termGramMatrix X t) Z ∧
      ∀ (j : ℕ) (I J : Fin j ↪o Fin (D.R.rS + 1)), (Z.submatrix I J).det ≠ 0 →
        ∏ τ, max 1 (UnitaryVolumeMass.absMinor D Z I J τ) ≤ HHZ D large₂.sc.b C (termGramMatrix X t) := by
  have hR : RelZ D (ZhatL (lf D Y.F0) (X.fl' t)) := by
    have h := X.pt_cell t hG hrel
    rw [Y.fl_eq t] at h
    exact ⟨_, h⟩
  obtain ⟨_, _, _, Z, hZ, hm⟩ := hHH hH Y.F0 Y.flag_e_eq_hyperbolic Y.formsAtZero (X.abelian₂ t) (Y.isRows.1 _ (Y.Lam_mem t)) (X.fl' t)
    (rows_isTermF' Y t hG) hR
  refine ⟨Z, ?_, fun j I J h => ?_⟩
  · unfold termGramMatrix; rw [Y.fl_eq t]; exact hZ
  · unfold termGramMatrix; rw [Y.fl_eq t]; exact (hm j I J h).1

end Reduced

end Formalism.MainNotions.BridgeLemma₂

end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsFibres
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsRpowPow
namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.HermitianLatticeCounting

theorem rows_rpow_pow {b : ℝ} (hb : 0 < b) (x : ℝ) (n : ℕ) : (b ^ x) ^ n = b ^ (x * n) := by
  first
    | exact (Real.rpow_mul_natCast hb.le x n).symm
    | (rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le])

theorem rows_num_Q {f r : ℕ} {b pe E1 cr δ : ℝ} (hb : 2 ≤ b) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1) :
    (1 + δ) * (((b ^ pe) ^ E1) ^ 2 * ((b ^ pe) ^ cr) ^ 2) * ((41 ^ f * (b ^ pe) ^ 3) ^ ((r + 1) ^ 2)) ^ 2 ≤
      b ^ (1 + 12 * (f : ℝ) * ((r : ℝ) + 1) ^ 2 + pe * (2 * E1 + 2 * cr + 6 * ((r : ℝ) + 1) ^ 2)) := by
  have hb0 : 0 < b := by linarith
  have hrp : ∀ y z : ℝ, (b ^ y) ^ z = b ^ (y * z) := fun y z => (Real.rpow_mul hb0.le y z).symm
  have h6 : (41 : ℝ) ≤ b ^ 6 := by
    have h2 : (2 : ℝ) ^ 6 ≤ b ^ 6 := by gcongr
    norm_num at h2
    linarith
  have h41 : (41 : ℝ) ^ f ≤ b ^ (6 * (f : ℝ)) := by
    calc (41 : ℝ) ^ f ≤ (b ^ 6) ^ f := by gcongr
      _ = b ^ (6 * (f : ℝ)) := by
        rw [← pow_mul, ← Real.rpow_natCast]
        congr 1 <;> push_cast <;> ring
  have e0 : (b ^ pe) ^ 3 = b ^ (3 * pe) := by
    rw [rows_rpow_pow hb0]
    congr 1 <;> push_cast <;> ring
  have hA : (41 : ℝ) ^ f * (b ^ pe) ^ 3 ≤ b ^ (6 * (f : ℝ) + 3 * pe) := by
    rw [Real.rpow_add hb0, e0]
    gcongr
    all_goals first | exact h41 | positivity
  have e1 : ((b ^ pe) ^ E1) ^ 2 = b ^ (2 * pe * E1) := by
    rw [hrp, rows_rpow_pow hb0]
    congr 1 <;> push_cast <;> ring
  have e2 : ((b ^ pe) ^ cr) ^ 2 = b ^ (2 * pe * cr) := by
    rw [hrp, rows_rpow_pow hb0]
    congr 1 <;> push_cast <;> ring
  have e3 : ((b ^ (6 * (f : ℝ) + 3 * pe)) ^ ((r + 1) ^ 2)) ^ 2 =
      b ^ (12 * (f : ℝ) * ((r : ℝ) + 1) ^ 2 + 6 * pe * ((r : ℝ) + 1) ^ 2) := by
    rw [rows_rpow_pow hb0, rows_rpow_pow hb0]
    congr 1 <;> push_cast <;> ring
  have h1δ : 1 + δ ≤ b ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    linarith
  calc (1 + δ) * (((b ^ pe) ^ E1) ^ 2 * ((b ^ pe) ^ cr) ^ 2) * ((41 ^ f * (b ^ pe) ^ 3) ^ ((r + 1) ^ 2)) ^ 2
      ≤ b ^ (1 : ℝ) * (((b ^ pe) ^ E1) ^ 2 * ((b ^ pe) ^ cr) ^ 2) *
          ((b ^ (6 * (f : ℝ) + 3 * pe)) ^ ((r + 1) ^ 2)) ^ 2 := by
        gcongr
        all_goals first | exact h1δ | exact hA | positivity
    _ = b ^ (1 : ℝ) * (b ^ (2 * pe * E1) * b ^ (2 * pe * cr)) *
          b ^ (12 * (f : ℝ) * ((r : ℝ) + 1) ^ 2 + 6 * pe * ((r : ℝ) + 1) ^ 2) := by
        rw [e1, e2, e3]
    _ = _ := by
        rw [← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_add hb0]
        congr 1
        ring

theorem rows_num_nd {k m f s r : ℕ} {b g v Γ c C pe E1 cr δ rD XiP : ℝ} {Xi : ℕ → ℝ}
    (hb : 2 ≤ b) (hg : 0 < g) (hv : 0 < v) (hΓ : 0 ≤ Γ) (hc : 0 ≤ c) (hcC : c ≤ C) (hC : 1 ≤ C)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1) (hrD : 0 ≤ rD) (hXiP : 0 ≤ XiP) (hXi : XiP ≤ Xi s)
    (hexp : 1 + 12 * (f : ℝ) * ((r : ℝ) + 1) ^ 2 + pe * (2 * E1 + 2 * cr + 6 * ((r : ℝ) + 1) ^ 2) ≤
      C * (m : ℝ) ^ 2 * f * (C * ((s : ℝ) + m) * (m : ℝ) ^ 2)) :
    (2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v / (Real.exp 1 * Real.pi)) ^ (k * f) *
        (XiP * (((b ^ pe) ^ E1) ^ 2 * ((b ^ pe) ^ cr) ^ 2 * (c * s * f) ^ (6 * s * f) * Γ)) * ((1 + δ) * rD) *
        ((41 ^ f * (b ^ pe) ^ 3) ^ ((r + 1) ^ 2)) ^ 2 ≤
      LatticeSumBounds.ndRow C k m f s b g v Γ Xi * rD := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hC0 : 0 < C := by linarith
  have hXis : 0 ≤ Xi s := hXiP.trans hXi
  have hH : b ^ (1 + 12 * (f : ℝ) * ((r : ℝ) + 1) ^ 2 + pe * (2 * E1 + 2 * cr + 6 * ((r : ℝ) + 1) ^ 2)) ≤
      Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) := by
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH
    rw [← Real.rpow_mul hb0.le]
    first
      | exact Real.rpow_le_rpow_of_exponent_le hb1 hexp
      | exact (Real.rpow_le_rpow_left_iff (by linarith)).2 hexp
  have hB := (rows_num_Q (f := f) (r := r) (pe := pe) (E1 := E1) (cr := cr) hb hδ0 hδ).trans hH
  have hep : 1 ≤ Real.exp 1 * Real.pi := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    nlinarith
  have hkv : 0 ≤ (k : ℝ) * v := by positivity
  have hq : (k : ℝ) * v / (Real.exp 1 * Real.pi) ≤ (k : ℝ) * v * C := by
    have hd : (k : ℝ) * v / (Real.exp 1 * Real.pi) ≤ (k : ℝ) * v := by
      first
        | exact div_le_self hkv hep
        | (rw [div_le_iff₀ (by positivity)]; nlinarith)
    nlinarith
  have hK : ((k : ℝ) * v / (Real.exp 1 * Real.pi)) ^ (k * f) ≤ ((k : ℝ) * v) ^ (k * f) * C ^ (k * f) := by
    rw [← mul_pow]
    gcongr
  calc _ = ((2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v / (Real.exp 1 * Real.pi)) ^ (k * f) * XiP *
          (c * s * f) ^ (6 * s * f) * Γ * rD) *
        ((1 + δ) * (((b ^ pe) ^ E1) ^ 2 * ((b ^ pe) ^ cr) ^ 2) * ((41 ^ f * (b ^ pe) ^ 3) ^ ((r + 1) ^ 2)) ^ 2) := by
        ring
    _ ≤ ((2 / g) ^ ((s - 1) * k * f) * (((k : ℝ) * v) ^ (k * f) * C ^ (k * f)) * Xi s *
          (C * s * f) ^ (6 * s * f) * Γ * rD) *
        Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) := by
        gcongr
        all_goals first | assumption | positivity
    _ = Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k m f s b g v Γ Xi * rD := by
        unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow
        ring

end Formalism.MainNotions.BridgeLemma₂
end

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.HermitianLatticeCounting


open Classical in
theorem rows_fibres {Pr κ : Type} (S : Finset Pr) (c₁ c₂ : Pr → κ) (F : Pr → ℝ) :
    ∑ p ∈ S, F p = ∑ x ∈ S.image c₁, ∑ y ∈ S.image c₂, ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), F p := by
  rw [← Finset.sum_product', ← Finset.sum_fiberwise_of_maps_to (g := fun p => (c₁ p, c₂ p))
    (t := S.image c₁ ×ˢ S.image c₂) (fun p hp => Finset.mem_product.2
      ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩)]
  refine Finset.sum_congr rfl fun z _ => ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  refine Finset.filter_congr fun p _ => ?_
  rw [Prod.ext_iff]


open Classical in
theorem weighted_sum_le {Pr κ : Type} (S : Finset Pr) (w a₁ a₂ : Pr → ℝ) (c₁ c₂ : Pr → κ) (M R Φ : ℝ) (N : κ → κ → ℝ)
    (α φ : κ → ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R) (hw : ∀ p ∈ S, 0 ≤ w p) (ha₁ : ∀ p ∈ S, 0 ≤ a₁ p) (ha₂ : ∀ p ∈ S, 0 ≤ a₂ p)
    (hα₁ : ∀ p ∈ S, a₁ p ≤ α (c₁ p)) (hα₂ : ∀ p ∈ S, a₂ p ≤ α (c₂ p))
    (hcount : ∀ x ∈ S.image c₁, ∀ y ∈ S.image c₂, ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p ≤ M * N x y)
    (hN : ∀ x ∈ S.image c₁, ∀ y ∈ S.image c₂, N x y * (α x * α y) ≤ R * (φ x * φ y))
    (hα0 : ∀ x, 0 ≤ α x) (hφ0 : ∀ x, 0 ≤ φ x)
    (hΦ₁ : ∑ x ∈ S.image c₁, φ x ≤ Φ) (hΦ₂ : ∑ y ∈ S.image c₂, φ y ≤ Φ) :
    ∑ p ∈ S, w p * (a₁ p * a₂ p) ≤ M * (R * Φ ^ 2) := by
  rw [rows_fibres S c₁ c₂]
  have hΦ0 : 0 ≤ Φ := le_trans (Finset.sum_nonneg fun x _ => hφ0 x) hΦ₁
  calc ∑ x ∈ S.image c₁, ∑ y ∈ S.image c₂, ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p * (a₁ p * a₂ p)
      ≤ ∑ x ∈ S.image c₁, ∑ y ∈ S.image c₂, M * (R * (φ x * φ y)) := by
        refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => ?_
        calc ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p * (a₁ p * a₂ p)
            ≤ ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p * (α x * α y) := by
              refine Finset.sum_le_sum fun p hp => ?_
              obtain ⟨hpS, h1, h2⟩ := Finset.mem_filter.1 hp
              refine mul_le_mul_of_nonneg_left ?_ (hw p hpS)
              exact mul_le_mul (h1 ▸ hα₁ p hpS) (h2 ▸ hα₂ p hpS) (ha₂ p hpS) (hα0 x)
          _ = (∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p) * (α x * α y) := by rw [Finset.sum_mul]
          _ ≤ (M * N x y) * (α x * α y) :=
              mul_le_mul_of_nonneg_right (hcount x hx y hy) (mul_nonneg (hα0 x) (hα0 y))
          _ = M * (N x y * (α x * α y)) := by ring
          _ ≤ M * (R * (φ x * φ y)) := mul_le_mul_of_nonneg_left (hN x hx y hy) hM
    _ = M * (R * ((∑ x ∈ S.image c₁, φ x) * ∑ y ∈ S.image c₂, φ y)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ M * (R * Φ ^ 2) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hR) hM
        rw [sq]
        exact mul_le_mul hΦ₁ hΦ₂ (Finset.sum_nonneg fun x _ => hφ0 x) hΦ0

theorem weighted_sum_le' {Pr κ : Type} (S : Finset Pr) (w a₁ a₂ : Pr → ℝ) (c₁ c₂ : Pr → κ) (M R Φ : ℝ) (N : κ → κ → ℝ)
    (α φ : κ → ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R) (hw : ∀ p ∈ S, 0 ≤ w p) (ha₁ : ∀ p ∈ S, 0 ≤ a₁ p) (ha₂ : ∀ p ∈ S, 0 ≤ a₂ p)
    (hα₁ : ∀ p ∈ S, a₁ p ≤ α (c₁ p)) (hα₂ : ∀ p ∈ S, a₂ p ≤ α (c₂ p))
    (hcount : ∀ x y, (∃ p ∈ S, c₁ p = x) → (∃ p ∈ S, c₂ p = y) → ∀ S' : Finset Pr, S' ⊆ S →
      (∀ p ∈ S', c₁ p = x ∧ c₂ p = y) → ∑ p ∈ S', w p ≤ M * N x y)
    (hN : ∀ x y, (∃ p ∈ S, c₁ p = x) → (∃ p ∈ S, c₂ p = y) → N x y * (α x * α y) ≤ R * (φ x * φ y))
    (hα0 : ∀ x, 0 ≤ α x) (hφ0 : ∀ x, 0 ≤ φ x)
    (hΦ₁ : ∀ 𝒵 : Finset κ, (∀ x ∈ 𝒵, ∃ p ∈ S, c₁ p = x) → ∑ x ∈ 𝒵, φ x ≤ Φ)
    (hΦ₂ : ∀ 𝒵 : Finset κ, (∀ x ∈ 𝒵, ∃ p ∈ S, c₂ p = x) → ∑ x ∈ 𝒵, φ x ≤ Φ) :
    ∑ p ∈ S, w p * (a₁ p * a₂ p) ≤ M * (R * Φ ^ 2) := by
  classical
  refine weighted_sum_le S w a₁ a₂ c₁ c₂ M R Φ N α φ hM hR hw ha₁ ha₂ hα₁ hα₂ ?_ ?_ hα0 hφ0 ?_ ?_
  · intro x hx y hy
    exact hcount x y (Finset.mem_image.1 hx) (Finset.mem_image.1 hy) _ (Finset.filter_subset _ _)
      fun p hp => (Finset.mem_filter.1 hp).2
  · intro x hx y hy
    exact hN x y (Finset.mem_image.1 hx) (Finset.mem_image.1 hy)
  · exact hΦ₁ _ fun x hx => Finset.mem_image.1 hx
  · exact hΦ₂ _ fun x hx => Finset.mem_image.1 hx

end Formalism.MainNotions.BridgeLemma₂
end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lab

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

def pairCountExponentShift (D : D7) (c Ch : ℝ) : ℝ :=
  c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f + 4 * (max (Ch - c) 0 * (D.R.m : ℝ) ^ 2 * D.R.f * ((D.R.rS : ℝ) + 1))

def pairCountExponent (D : D7) (c : ℝ) (s : ℕ) : ℝ := c * ((s : ℝ) + D.R.m) * D.R.m + c * cF D.R.f

theorem rows_gg_eq (D : D7) : gg D = (gS D : ℝ) := by unfold gg gS; push_cast; ring

theorem rows_Tr_pos (D : D7) (w : D.what₂.Word) : 0 < Tr D w := by
  unfold Tr; exact_mod_cast (D.mem w).A.T_prime.pos

theorem rows_NT_pos (D : D7) (w : D.what₂.Word) : 0 < NT D w := by
  unfold NT; exact pow_pos (rows_Tr_pos D w) _

def wordPairGramGood (X : TermTie D) (u u' : D.what₂.Word) (large₂ : SizeData₂ D) (c : ℝ) (Z : GramM D) : Prop :=
  ∃ t : D.s.Term u u', D.s.Gterm t ≠ 0 ∧ D.s.relevant t ∧ ZEquiv (termGramMatrix X t) Z ∧
    ∀ (j : ℕ) (I J : Fin j ↪o Fin (D.R.rS + 1)), (Z.submatrix I J).det ≠ 0 →
      ∏ τ, max 1 (UnitaryVolumeMass.absMinor D Z I J τ) ≤ HHZ D large₂.sc.b c (termGramMatrix X t)


open Classical in
def termReducedGramMatrix {C' Cl Cg cb Cu cT CT C0 A c : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hHH : UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) (t : D.s.Term u u') : GramM D :=
  if h : D.s.Gterm t ≠ 0 ∧ D.s.relevant t then Classical.choose (rows_reduced_exists Y hH hHH t h.1 h.2) else 0

theorem rows_Zr_spec {C' Cl Cg cb Cu cT CT C0 A c : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hHH : UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0)
    (hrel : D.s.relevant t) :
    ZEquiv (termGramMatrix X t) (termReducedGramMatrix Y hH hHH t) ∧ wordPairGramGood X u u' large₂ c (termReducedGramMatrix Y hH hHH t) := by
  have h := Classical.choose_spec (rows_reduced_exists Y hH hHH t hG hrel)
  have e : termReducedGramMatrix Y hH hHH t = Classical.choose (rows_reduced_exists Y hH hHH t hG hrel) := by
    unfold termReducedGramMatrix; rw [dite_eq_left ⟨hG, hrel⟩]
  rw [e]
  exact ⟨h.1, t, hG, hrel, h.1, h.2⟩

theorem rows_Gz_pos (hT : TermPtsTie X Y) (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0)
    (hrel : D.s.relevant t) (τ : D.what₂.Tau) : 0 < Formalism.MainNotions.S.Cnt.Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ := by
  obtain ⟨h1, _, _, _⟩ := hT t hG hrel
  obtain ⟨hz, hz', hTz, hTz', hR⟩ := h1 τ
  rw [← d_Gf_eq Y hrd t τ]
  exact lt_of_le_of_ne (Formalism.QuantumDeterminants.gNonneg D.R.k D.R.rS _ _ hz hz' (hTz ▸ rows_Tr_pos D u) (hTz' ▸ rows_Tr_pos D u') _ hR.1)
    (Ne.symm hR.2.2)

theorem two_le_gg_of_count_hypotheses {C' Cl Cg cb Cu cT CT C0 : ℝ} (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) : 2 ≤ gg D := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h12, _, h14, _⟩ := hH.1
  have hb := d_two_le_b D large₂
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have h0 : (2 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by
    have : (2 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := by nlinarith
    calc (2 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := this
      _ ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
  have g1 : (2 : ℝ) ≤ D.host.g 0 := h0.trans h12
  have g2 : (2 : ℝ) ≤ D.host.g 1 := h0.trans h14
  unfold gg
  nlinarith

theorem gramProductG0_pos {C' Cl Cg cb Cu cT CT C0 c : ℝ} (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (hT : TermPtsTie X Y)
    {Z : GramM D} (hZ : wordPairGramGood X u u' large₂ c Z) : 0 < wordPairGramProduct D u u' Z := by
  obtain ⟨t, hG, hrel, hE, _⟩ := hZ
  rw [gramProductG0_equiv_invariant hE]
  unfold wordPairGramProduct
  have hg : 0 < (gS D : ℝ) := by rw [← rows_gg_eq]; linarith [two_le_gg_of_count_hypotheses hH]
  exact mul_pos (Finset.prod_pos fun τ _ => rows_Gz_pos Y hT (d_rdE_pos hH) t hG hrel τ) (by positivity)

theorem rows_one_le_HHZ (D : D7) (large₂ : SizeData₂ D) {c : ℝ} (hc : 0 ≤ c) (Z : GramM D) : 1 ≤ HHZ D large₂.sc.b c Z := by
  unfold HHZ
  have hb := d_two_le_b D large₂
  have h1 : 1 ≤ (large₂.sc.b ^ (c * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (c * (D.R.m : ℝ)) :=
    Real.one_le_rpow (Real.one_le_rpow (by linarith) (by positivity)) (by positivity)
  have h2 : 1 ≤ sizeZ D large₂.sc.b c Z ^ 4 := one_le_pow₀ (rows_one_le_sizeZ _ _ _)
  nlinarith

theorem gramProductG0_le_height {C' Cl Cg cb Cu cT CT C0 A c : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hHH : UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) (hT : TermPtsTie X Y)
    {Z : GramM D} (hZ : wordPairGramGood X u u' large₂ c Z) : wordPairGramProduct D u u' Z ≤ HHZ D large₂.sc.b c Z := by
  obtain ⟨t, hG, hrel, hE, _⟩ := hZ
  rw [gramProductG0_equiv_invariant hE, rows_HHZ_inv hE]
  have hR : RelZ D (ZhatL (lf D Y.F0) (X.fl' t)) := by
    have h := X.pt_cell t hG hrel
    rw [Y.fl_eq t] at h
    exact ⟨_, h⟩
  obtain ⟨_, h2, _⟩ := hHH hH Y.F0 Y.flag_e_eq_hyperbolic Y.formsAtZero (X.abelian₂ t) (Y.isRows.1 _ (Y.Lam_mem t)) (X.fl' t)
    (rows_isTermF Y t hG) hR
  rw [← Y.fl_eq t] at h2
  have hg := two_le_gg_of_count_hypotheses hH.1
  rw [rows_gg_eq] at hg
  have hp : ∀ τ, 0 < Formalism.MainNotions.S.Cnt.Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ := fun τ => rows_Gz_pos Y hT (d_rdE_pos hH.1) t hG hrel τ
  have h3 : ∏ τ, Formalism.MainNotions.S.Cnt.Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ ≤ HHZ D large₂.sc.b c (termGramMatrix X t) :=
    le_trans (Finset.prod_le_prod₀ (fun τ _ => (hp τ).le) fun τ _ => le_max_right _ _) h2
  unfold wordPairGramProduct
  have h4 : ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f) ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith))
  calc (∏ τ, Formalism.MainNotions.S.Cnt.Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ) * ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f)
      ≤ (∏ τ, Formalism.MainNotions.S.Cnt.Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ) * 1 :=
        mul_le_mul_of_nonneg_left h4 (Finset.prod_nonneg fun τ _ => (hp τ).le)
    _ ≤ _ := by rw [mul_one]; exact h3

theorem rows_massS_nonneg (D : D7) (j : ℕ) : 0 ≤ massS D j := by
  unfold massS massU; exact d_mass_nonneg _ _

theorem rows_XiS_nonneg (D : D7) (w : D.what₂.Word) {HH c : ℝ} (hHH : 0 ≤ HH) (hc : 0 ≤ c) (s : ℕ) : 0 ≤ XiS D w HH c s := by
  unfold XiS Xi
  have hN := (rows_NT_pos D w).le
  split_ifs
  · exact div_nonneg (mul_nonneg (rows_massS_nonneg D _) (rows_massS_nonneg D _)) (rows_massS_nonneg D _)
  · positivity
  · exact le_rfl

theorem rows_Xi_le (D : D7) (w : D.what₂.Word) {HH P2 σ c : ℝ} (hHH : 0 ≤ HH) (hP2 : 0 ≤ P2) (hσ : 1 ≤ σ) (hc : 0 ≤ c)
    (h : HH ≤ P2 * σ ^ 4) (s : ℕ) : XiS D w HH c s ≤ XiS D w P2 c s * σ ^ (4 * (c * D.R.k)) := by
  have hσ0 : 0 < σ := by linarith
  have h1 : 1 ≤ σ ^ (4 * (c * D.R.k)) := Real.one_le_rpow hσ (by positivity)
  have hN := (rows_NT_pos D w).le
  unfold XiS Xi
  split_ifs
  · exact le_mul_of_one_le_right
      (div_nonneg (mul_nonneg (rows_massS_nonneg D _) (rows_massS_nonneg D _)) (rows_massS_nonneg D _)) h1
  · have e : (HH * NT D w) ^ (c * D.R.k) ≤ (P2 * NT D w) ^ (c * D.R.k) * σ ^ (4 * (c * D.R.k)) := by
      calc (HH * NT D w) ^ (c * D.R.k) ≤ ((P2 * NT D w) * σ ^ 4) ^ (c * (D.R.k : ℝ)) := by
            apply Real.rpow_le_rpow (by positivity) _ (by positivity)
            calc HH * NT D w ≤ (P2 * σ ^ 4) * NT D w := mul_le_mul_of_nonneg_right h hN
              _ = (P2 * NT D w) * σ ^ 4 := by ring
        _ = (P2 * NT D w) ^ (c * D.R.k) * σ ^ (4 * (c * D.R.k)) := by
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast σ 4, ← Real.rpow_mul hσ0.le]
            norm_num
    calc (c * D.R.k) ^ (D.R.k * D.R.f) * (HH * NT D w) ^ (c * D.R.k)
        ≤ (c * D.R.k) ^ (D.R.k * D.R.f) * ((P2 * NT D w) ^ (c * D.R.k) * σ ^ (4 * (c * D.R.k))) :=
          mul_le_mul_of_nonneg_left e (by positivity)
      _ = _ := by ring
  · simp

theorem rows_c3B_nonneg (D : D7) (large₂ : SizeData₂ D) (w : D.what₂.Word) {c : ℝ} (hc : 0 ≤ c) (Z' Z'' : GramM D) (s : ℕ) {De : ℝ}
    (hDe : 0 ≤ De) : 0 ≤ wordSublatticeTripleBound D large₂ w c Z' Z'' s De := by
  unfold wordSublatticeTripleBound
  have h1 := rows_one_le_HHZ D large₂ hc Z'
  have h2 := rows_one_le_HHZ D large₂ hc Z''
  have hN := rows_NT_pos D w
  have hX := rows_XiS_nonneg D w (HH := HHZ D large₂.sc.b c Z' * HHZ D large₂.sc.b c Z'') (by nlinarith) hc s
  have h3 : 0 ≤ HHZ D large₂.sc.b c Z' * HHZ D large₂.sc.b c Z'' := by nlinarith
  positivity

end Lab

end Formalism.MainNotions.BridgeLemma₂

end

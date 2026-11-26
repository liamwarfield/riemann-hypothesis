module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsKB
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsOneE

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsTie
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rows_scanl_head (xs : List ℕ) (a : ℕ) : xs.scanl (· + ·) a = a :: (xs.scanl (· + ·) a).tail := by
  cases xs <;> simp [List.scanl_cons]

theorem rows_scanl_pw : ∀ (xs : List ℕ) (a : ℕ), (∀ x ∈ xs, 1 ≤ x) →
    ((xs.scanl (· + ·) a).tail).Pairwise (· < ·) ∧ ∀ y ∈ (xs.scanl (· + ·) a).tail, a < y := by
  intro xs
  induction xs with
  | nil => intro a _; simp
  | cons x xs ih =>
    intro a h
    have hx : 1 ≤ x := h x (List.mem_cons_self ..)
    obtain ⟨ih1, ih2⟩ := ih (a + x) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.scanl_cons, List.tail_cons]
    rw [rows_scanl_head xs (a + x)]
    refine ⟨List.pairwise_cons.2 ⟨fun y hy => ih2 y hy, ih1⟩, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · omega
    · have := ih2 y hy
      omega

theorem rows_pw_ext : ∀ (l₁ l₂ : List ℕ), l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂ := by
  intro l₁ l₂ h1 h2 hm
  have hp : l₁.Perm l₂ := (List.perm_ext_iff_of_nodup (h1.imp ne_of_lt) (h2.imp ne_of_lt)).2 hm
  exact hp.eq_of_sortedLE (List.sortedLE_iff_pairwise.2 (h1.imp le_of_lt))
    (List.sortedLE_iff_pairwise.2 (h2.imp le_of_lt))

theorem rows_blockEnds_pw {i : ℕ} (p : Point ℂ i) :
    (ptBlockEnds p).Pairwise (· < ·) ∧ ∀ y ∈ ptBlockEnds p, 0 < y := by
  have h := rows_scanl_pw (p.1.map Prod.snd) 0 (by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
    exact (p.2.1 b hb).2)
  exact h

section Comparison₂

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

def wordPairNormRelation (X : TermTie D) (u u' : D.what₂.Word) : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t →
    1 ≤ ∏ τ, Formalism.MainNotions.S.Cnt.Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ ∧
    ∀ l, l ≤ D.R.rS + 1 → leadMinorE (termGramMatrix X t) l ≠ 0 → 1 ≤ ∏ τ, absDl D (termGramMatrix X t) l τ ^ 2

theorem rows_Dmin_ne_iff (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (τ : D.what₂.Tau) (l : ℕ) (hl : l ≤ D.R.rS + 1) :
    DminN (Y.W τ).z (Y.W τ).z' (Y.γ t τ) l ≠ 0 ↔ leadMinorE (termGramMatrix X t) l ≠ 0 := by
  rw [← norm_ne_zero_iff, d_norm_Dmin Y hrd t τ l hl]
  unfold absDl absReal
  have h0 : D.host.rdE ^ (-(2 * (frameExp D.R.rS l : ℝ))) ≠ 0 := (Real.rpow_pos_of_pos hrd _).ne'
  rw [mul_ne_zero_iff, norm_ne_zero_iff, map_ne_zero]
  exact ⟨fun h => h.1, fun h => ⟨h, h0⟩⟩

theorem rows_TermPtsTie_of (hrd : 0 < D.host.rdE) (hN : wordPairNormRelation X u u') : TermPtsTie X Y := by
  intro t hG hrel
  have hR : ∀ τ, RelPt D (Y.W τ).z (Y.W τ).z' (Y.γ t τ) (Y.pt t τ) := fun τ => (Y.rel t hG hrel τ).1
  have mem_iff : ∀ τ l, l ∈ ptBlockEnds (Y.pt t τ) ↔ (1 ≤ l ∧ l ≤ D.R.rS + 1 ∧ leadMinorE (termGramMatrix X t) l ≠ 0) := by
    intro τ l
    constructor
    · intro h
      have hl := blockEnd_le (Y.pt t τ) l h
      exact ⟨(rows_blockEnds_pw (Y.pt t τ)).2 l h, hl, (rows_Dmin_ne_iff Y hrd t τ l hl).1 (cell_ne_of_mem D (hR τ) l h)⟩
    · rintro ⟨h1, hl, hne⟩
      exact cell_mem_blockEnds D (hR τ) l h1 hl ((rows_Dmin_ne_iff Y hrd t τ l hl).2 hne)
  refine ⟨fun τ => ?_, fun τ τ' => ?_, ?_, fun τ₀ l hl => ?_⟩
  · obtain ⟨_, _, hz, hz', hT, hT', _⟩ := Y.goodW τ
    exact ⟨hz, hz', hT, hT', hR τ⟩
  · exact rows_pw_ext _ _ (rows_blockEnds_pw _).1 (rows_blockEnds_pw _).1 fun x => by rw [mem_iff τ x, mem_iff τ' x]
  · rw [Finset.prod_congr rfl fun τ _ => d_Gf_eq Y hrd t τ]
    exact (hN t hG hrel).1
  · obtain ⟨_, h2, h3⟩ := (mem_iff τ₀ l).1 hl
    rw [Finset.prod_congr rfl fun τ _ => by rw [d_norm_Dmin Y hrd t τ l h2]]
    exact (hN t hG hrel).2 l h2 h3

end Comparison₂

end Formalism.MainNotions.BridgeLemma₂

end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsOneF
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem decay_length_sufficient {m k r c B : ℝ} (hm : m = 2 * r + 2) (hr : 0 ≤ r) (hk : m + 3 ≤ k) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (ha : B * m ^ 5 ≤ k) :
    (r + 1) * (12 * (c * r ^ 2) + B * m ^ 2 / 2 + B * m ^ 4 + 12 * (r + 1) ^ 2) + 1 ≤ (9 * c + 3) * k * m ^ 2 := by
  have hm2 : 2 ≤ m := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hr1 : r + 1 = m / 2 := by linarith
  have e : (r + 1) * (12 * (c * r ^ 2) + B * m ^ 2 / 2 + B * m ^ 4 + 12 * (r + 1) ^ 2) + 1 =
      6 * m * (c * r ^ 2) + (B * m ^ 3) / 4 + (B * m ^ 5) / 2 + (m / 2) * (12 * (m / 2) ^ 2) + 1 := by rw [hr1]; ring
  have p1 : 6 * m * (c * r ^ 2) ≤ 2 * (c * k * m ^ 2) := by
    have a : r ^ 2 ≤ m ^ 2 / 4 := by nlinarith
    have b : c * r ^ 2 ≤ c * (m ^ 2 / 4) := mul_le_mul_of_nonneg_left a hc
    have d : 6 * m * (c * r ^ 2) ≤ 6 * m * (c * (m ^ 2 / 4)) := mul_le_mul_of_nonneg_left b (by linarith)
    nlinarith [mul_nonneg (mul_nonneg hc (sq_nonneg m)) (by linarith : 0 ≤ k - m)]
  have m35 : m ^ 3 ≤ m ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have p2 : B * m ^ 3 ≤ k := le_trans (mul_le_mul_of_nonneg_left m35 hB) ha
  have p4 : (m / 2) * (12 * (m / 2) ^ 2) ≤ (3 / 2) * (k * m ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg m) (by linarith : 0 ≤ k - m)]
  have p5 : (1 : ℝ) ≤ (1 / 2) * (k * m ^ 2) := by nlinarith
  have hm4 : 4 ≤ m ^ 2 := by nlinarith
  have p6 : k ≤ (1 / 4) * (k * m ^ 2) := by nlinarith [mul_nonneg hk0 (sub_nonneg.2 hm4)]
  have hU : 0 ≤ c * k * m ^ 2 := by positivity
  rw [e]
  have t : (9 * c + 3) * k * m ^ 2 = 9 * (c * k * m ^ 2) + 3 * (k * m ^ 2) := by ring
  rw [t]
  linarith

theorem le_max_four (a b c d : ℝ) : a ≤ max (max a b) (max c d) ∧ b ≤ max (max a b) (max c d) ∧
    c ≤ max (max a b) (max c d) ∧ d ≤ max (max a b) (max c d) :=
  ⟨le_trans (le_max_left _ _) (le_max_left _ _), le_trans (le_max_right _ _) (le_max_left _ _),
    le_trans (le_max_left _ _) (le_max_right _ _), le_trans (le_max_right _ _) (le_max_right _ _)⟩

section Mono

variable {D : D7} {large₂ : SizeData₂ D} {u u' : D.what₂.Word}

theorem height_pow_mono_constant (large₂ : SizeData₂ D) (hrd : 0 < D.host.rdE) {c' c : ℝ} (h : |c'| + 2 ≤ c) (Z : GramM D) :
    HHZ D large₂.sc.b c' Z ^ (c' * (D.R.rS : ℝ) ^ 2) ≤ HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2) := by
  have h1 : c' ≤ c := by linarith [le_abs_self c']
  have h2 : 2 ≤ c + c' := by linarith [neg_abs_le c']
  have mono := rows_HHZ_mono large₂ hrd h1 h2 Z
  have o := rows_one_le_HHZ' D large₂ c' Z
  have hc : 0 ≤ c := by linarith [abs_nonneg c']
  calc HHZ D large₂.sc.b c' Z ^ (c' * (D.R.rS : ℝ) ^ 2) ≤ HHZ D large₂.sc.b c' Z ^ (c * (D.R.rS : ℝ) ^ 2) :=
        Real.rpow_le_rpow_of_exponent_le o (by gcongr)
    _ ≤ HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2) := Real.rpow_le_rpow (by linarith) mono (by positivity)

theorem switch_bound_mono_constant {C' Cl Cg cb Cu cT CT C0 A c' c : ℝ} (h1 : |c'| + 2 ≤ c)
    (h : UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c') : UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c := by
  intro hH F0 he hz what₂ hrows Z hZ
  have h0 := h hH F0 he hz what₂ hrows Z hZ
  unfold MeanLe at h0 ⊢
  have hB : HHZ D large₂.sc.b c' Z ^ (c' * (D.R.rS : ℝ) ^ 2) * ∏ τ, nV D (Tu D u) (Tu D u') Z τ ≤
      HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2) * ∏ τ, nV D (Tu D u) (Tu D u') Z τ := by
    refine mul_le_mul_of_nonneg_right (height_pow_mono_constant large₂ (d_rdE_pos hH.1) h1 Z) ?_
    refine Finset.prod_nonneg fun τ _ => ?_
    unfold nV
    exact D.R.k_even.pow_nonneg _
  exact h0.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hB))

theorem partner_count_bound_mono_constant {C' Cl Cg cb Cu cT CT C0 A c' c : ℝ} (h1 : |c'| + 2 ≤ c)
    (h : UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c') : UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c := by
  intro hH F0 he hz Λ hΛ F' hF' hgen hR Z hZ
  refine (h hH F0 he hz Λ hΛ F' hF' hgen hR Z hZ).trans (ENNReal.ofReal_le_ofReal ?_)
  have hrd := d_rdE_pos hH.1
  have k1 : c' ≤ c := by linarith [le_abs_self c']
  have k2 : 2 ≤ c + c' := by linarith [neg_abs_le c']
  have hc : 0 ≤ c := by linarith [abs_nonneg c']
  have ma := rows_HHZ_mono large₂ hrd k1 k2 (ZhatL (lf D F0) F')
  have mb := rows_HHZ_mono large₂ hrd k1 k2 Z
  have oa := rows_one_le_HHZ' D large₂ c' (ZhatL (lf D F0) F')
  have ob := rows_one_le_HHZ' D large₂ c' Z
  have o : 1 ≤ HHZ D large₂.sc.b c' (ZhatL (lf D F0) F') * HHZ D large₂.sc.b c' Z := one_le_mul_of_one_le_of_one_le oa ob
  have hp : c' ^ D.R.f ≤ c ^ D.R.f :=
    (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) _)
  refine mul_le_mul hp ?_ (Real.rpow_nonneg (by linarith) _) (pow_nonneg hc _)
  calc (HHZ D large₂.sc.b c' (ZhatL (lf D F0) F') * HHZ D large₂.sc.b c' Z) ^ (c' * (D.R.rS : ℝ) ^ 2)
      ≤ (HHZ D large₂.sc.b c' (ZhatL (lf D F0) F') * HHZ D large₂.sc.b c' Z) ^ (c * (D.R.rS : ℝ) ^ 2) :=
        Real.rpow_le_rpow_of_exponent_le o (by gcongr)
    _ ≤ _ := Real.rpow_le_rpow (by linarith) (mul_le_mul ma mb (by linarith) (by linarith)) (by positivity)

end Mono

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

theorem rows_rdE_pos (D : D7) : 0 < D.host.rdE := by
  unfold Host.rdE
  exact Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)) _

def FamilyGramHypotheses : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    wordPairNormRelation (X x hx i) u u' ∧ @LatticeDeterminantFactorization (Fm.D x i) (X x hx i) u u' ∧
      wordPairEntriesInLattice (X x hx i) u u' ∧ wordPairTermInjective (X x hx i) (Y x hx i u u')

theorem family_gram_facts_of_hypotheses (h : FamilyGramHypotheses Fm C1 X Y) : rows_TiesF Fm C1 X Y := fun x hx i u u' =>
  ⟨rows_TermPtsTie_of _ (rows_rdE_pos _) (h x hx i u u').1, (h x hx i u u').2.1, (h x hx i u u').2.2.1⟩

end Fam

end Formalism.MainNotions.BridgeLemma₂

end

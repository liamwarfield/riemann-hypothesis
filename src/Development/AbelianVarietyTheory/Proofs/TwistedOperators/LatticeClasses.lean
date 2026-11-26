module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsValuationEqZpow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexParahoricLevelChainTwist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdaptedExponentSchwartzBruhatLastColumn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZpowMulMemPow
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.LatClass

section Pow
variable {k : Type} [Field k] [ValuativeRel k] {ϖ : kˣ}

theorem val_pos (x : kˣ) : 0 < valuation k (x : k) := by simp [zero_lt_iff]

theorem mem_pow {e : ℤ} {s : k} : s ∈ powInt ϖ e ↔ valuation k s ≤ valuation k (ϖ : k) ^ e := by
  simp [powInt]

theorem mem_pow_zero {s : k} : s ∈ powInt ϖ 0 ↔ s ∈ 𝒪[k] := by
  rw [mem_pow, zpow_zero]; rfl

theorem zpow_mul_mem_pow {a b : ℤ} {s : k} : (ϖ : k) ^ a * s ∈ powInt ϖ b ↔ s ∈ powInt ϖ (b - a) := by
  have h := val_pos ϖ
  rw [mem_pow, mem_pow, map_mul, map_zpow₀, zpow_sub₀ h.ne', le_div_iff₀ (zpow_pos h a), mul_comm]

theorem zero_mem_pow {e : ℤ} : (0 : k) ∈ powInt ϖ e := by simp [mem_pow]

theorem pow_mul_pow {a b : ℤ} {t s : k} (ht : t ∈ powInt ϖ a) (hs : s ∈ powInt ϖ b) : t * s ∈ powInt ϖ (a + b) := by
  rw [mem_pow] at ht hs ⊢
  rw [map_mul, zpow_add₀ (val_pos ϖ).ne']
  exact mul_le_mul' ht hs

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hϖ : valuation k (ϖ : k) = uniformizer k)
include hϖ

theorem zpow_mem_pow {a b : ℤ} : (ϖ : k) ^ a ∈ powInt ϖ b ↔ b ≤ a := by
  rw [mem_pow, map_zpow₀, zpow_le_zpow_iff_right_of_lt_one₀ (val_pos ϖ) (hϖ ▸ uniformizer_lt_one)]

theorem pow_mono {a b : ℤ} (h : a ≤ b) {s : k} (hs : s ∈ powInt ϖ b) : s ∈ powInt ϖ a := by
  have := (zpow_mem_pow hϖ).2 h
  rw [mem_pow] at hs this ⊢
  rw [map_zpow₀] at this
  exact hs.trans this

end Pow

section Lat
variable {k : Type} [Field k] [ValuativeRel k] {ϖ : kˣ}
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem mem_latOf_mul {g a : GL Y k} {y : Y → k} : y ∈ latOf (g * a) ↔ (g⁻¹).val *ᵥ y ∈ latOf a := by
  simp [mem_latOf, mulVec_mulVec]

theorem latOf_mul_congr (g : GL Y k) {a b : GL Y k} (h : latOf a = latOf b) : latOf (g * a) = latOf (g * b) := by
  ext y; rw [mem_latOf_mul, mem_latOf_mul, h]

omit [Fintype Y] [DecidableEq Y] in
theorem smul_mem_lat {L : Submodule 𝒪[k] (Y → k)} {t : k} (ht : t ∈ 𝒪[k]) {y : Y → k} (hy : y ∈ L) : t • y ∈ L :=
  L.smul_mem ⟨t, ht⟩ hy

theorem mapsLat_iff {x : Matrix Y Y' k} {g : GL Y' k} {h : GL Y k} :
    MapsLat x (latOf g) (latOf h) ↔ IntM ((h⁻¹).val * x * g.val) := by
  constructor
  · intro H i j
    have : g.val *ᵥ Pi.single j 1 ∈ latOf g := by
      have := (mulVec_mem_latOf g (g := 1) (y := Pi.single j 1)).2 (mem_latOf_one.2 fun l => by
        rw [Pi.single_apply]; split_ifs
        exacts [one_mem _, zero_mem _])
      rwa [mul_one] at this
    have := H _ this i
    rwa [mulVec_mulVec, mulVec_mulVec, mulVec_single_one] at this
  · intro H y hy i
    have : (h⁻¹).val *ᵥ (x *ᵥ y) = ((h⁻¹).val * x * g.val) *ᵥ ((g⁻¹).val *ᵥ y) := by
      simp [mulVec_mulVec, Matrix.mul_assoc]
    rw [this]
    exact sum_mem fun l _ => mul_mem (H i l) (hy l)

theorem mem_nf {g : GL n k} {e : Fin (c + 1) → ℤ} {z : n → k} {y : n ⊕ Fin (c + 1) → k} :
    y ∈ latOf (nfBasis ϖ g e z) ↔
      (fun r => y (.inl r) - y (.inr 0) * z r) ∈ latOf g ∧ ∀ i, y (.inr i) ∈ powInt ϖ (e i) := by
  have key : (nfBasis ϖ g e z).val *ᵥ Sum.elim ((g⁻¹).val *ᵥ fun r => y (.inl r) - y (.inr 0) * z r)
      (fun i => (ϖ : k) ^ (-e i) * y (.inr i)) = y := by
    have h0 : ∀ a : ℤ, (ϖ : k) ^ a ≠ 0 := fun a => zpow_ne_zero _ ϖ.ne_zero
    rw [nfBasis_val, fromBlocks_mulVec]
    ext (r | i)
    · simp only [Sum.elim_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_mulVec, Units.mul_inv, one_mulVec,
        Pi.add_apply]
      simp [mulVec, dotProduct]
      field_simp
      ring
    · simp [mulVec_diagonal, h0]
  conv_lhs => rw [← key, ← mul_one (nfBasis ϖ g e z)]
  rw [mul_one, ← mul_one (nfBasis ϖ g e z)]
  conv_lhs => enter [2]; rw [mul_one]
  rw [mulVec_mem_latOf, mem_latOf_one, Sum.forall]
  refine and_congr Iff.rfl (forall_congr' fun i => ?_)
  rw [Sum.elim_inr, ← mem_pow_zero (ϖ := ϖ), zpow_mul_mem_pow]; simp

theorem mem_normal {e : Fin (c + 1) → ℤ} {z : n → k} {y : n ⊕ Fin (c + 1) → k} :
    y ∈ latOf (normalBasis ϖ e z) ↔
      (∀ r, y (.inl r) - y (.inr 0) * z r ∈ 𝒪[k]) ∧ ∀ i, y (.inr i) ∈ powInt ϖ (e i) := by
  rw [← nfBasis_one, mem_nf, mem_latOf_one]

omit [ValuativeRel k] in
theorem N_mulVec {p : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) (y : n ⊕ Fin c → k) (r : n ⊕ Fin c)
    (h : ∀ s, lev p r < lev p s → y s = 0) : (u.val *ᵥ y) r = y r := by
  have hu' := (Radical.mem_N_iff u).1 hu
  conv_rhs => rw [← one_mulVec y]
  refine Finset.sum_congr rfl fun s _ => ?_
  rcases le_or_gt (lev p s) (lev p r) with hs | hs
  · exact congrArg (· * y s) (hu' r s hs)
  · simp [h s hs]


omit [ValuativeRel k] in
theorem N_fix {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c 1) (y : n ⊕ Fin c → k)
    (h : ∀ l : Fin c, 0 < l.val → y (.inr l) = 0) : u.val *ᵥ y = y := by
  ext r
  refine N_mulVec hu y r ?_
  rintro (s | s) hs
  · rcases r with r | r <;> simp [lev] at hs
  · apply h
    rcases r with r | r <;> simp [lev] at hs <;> omega

omit [ValuativeRel k] in
theorem embX_mulVec (x : GL n k) (y : n ⊕ Fin c → k) :
    (embX c x).val *ᵥ y = Sum.elim (x.val *ᵥ fun r => y (.inl r)) fun l => y (.inr l) := by
  rw [Radical.embX_val, fromBlocks_mulVec]; simp; rfl

theorem topCoord_le {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c 1) (h : GL (n ⊕ Fin c) k) (i : Fin c) :
    topCoord (latOf h) i ⊆ topCoord (latOf (r * h)) i := by
  obtain ⟨x, u, hu, rfl⟩ := Radical.exists_of_mem_R hr
  rintro _ ⟨y, hy, h0, rfl⟩
  have key : ∀ l, i ≤ l → ((embX c x * u).val *ᵥ y) (.inr l) = y (.inr l) := fun l hl => by
    rw [Units.val_mul, ← mulVec_mulVec, embX_mulVec, Sum.elim_inr]
    refine N_mulVec hu y _ ?_
    rintro (s | s) hs
    · simp [lev] at hs
    · apply h0
      simp [lev] at hs
      exact lt_of_le_of_lt hl hs
  exact ⟨_, (mulVec_mem_latOf _).2 hy, fun l hl => (key l hl.le).trans (h0 l hl), key i le_rfl⟩

theorem topCoord_R {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c 1) (h : GL (n ⊕ Fin c) k) (i : Fin c) :
    topCoord (latOf (r * h)) i = topCoord (latOf h) i := by
  refine Set.Subset.antisymm ?_ (topCoord_le hr h i)
  have := topCoord_le (inv_mem hr) (r * h) i
  rwa [inv_mul_cancel_left] at this

theorem col_mem_nf {g : GL n k} {e : Fin (c + 1) → ℤ} {z : n → k} (i : Fin (c + 1)) {s : k}
    (hs : s ∈ powInt ϖ (e i)) :
    (Sum.elim (fun r => if i = 0 then s * z r else 0) (Pi.single i s) : n ⊕ Fin (c + 1) → k) ∈
      latOf (nfBasis ϖ g e z) := by
  refine mem_nf.2 ⟨?_, fun l => ?_⟩
  · convert zero_mem (latOf g) using 1
    ext r
    by_cases h : i = 0
    · subst h; simp
    · simp [h]
  · rw [Sum.elim_inr, Pi.single_apply]
    split_ifs with h
    · rwa [h]
    · exact zero_mem_pow

theorem topCoord_nf (g : GL n k) (e : Fin (c + 1) → ℤ) (z : n → k) (i : Fin (c + 1)) :
    topCoord (latOf (nfBasis ϖ g e z)) i = powInt ϖ (e i) := by
  ext s
  constructor
  · rintro ⟨y, hy, -, rfl⟩
    exact (mem_nf.1 hy).2 i
  · intro hs
    exact ⟨_, col_mem_nf i hs, fun l hl => by simp [hl.ne'], by simp⟩

omit [ValuativeRel k] in
theorem embX_mul_nf (x g : GL n k) (e : Fin c → ℤ) (z : n → k) :
    embX c x * nfBasis ϖ g e z = nfBasis ϖ (x * g) e (x.val *ᵥ z) := by
  ext1
  rw [Units.val_mul, nfBasis_val, nfBasis_val, Radical.embX_val, fromBlocks_multiply]
  ext (r | r) (s | s)
  · simp
  · by_cases h : s.val = 0 <;> simp [h, Matrix.mul_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  · simp
  · simp

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem latOf_eq_of_KO {g : GL Y k} (hg : g ∈ KO k Y) : latOf g = latOf 1 := by
  have := (mem_stabLat_iff (g := 1) (h := g)).1 (by simpa [mem_stabLat] using hg)
  rwa [mul_one] at this

theorem om_supp {μ : kˣ →* ℂˣ} {Φ : Matrix Y Y' k → ℂ} (hs : ∀ x, Φ x ≠ 0 → IntM x) (g : GL Y' k) (h : GL Y k)
    (x : Matrix Y Y' k) (hx : om μ g h Φ x ≠ 0) : MapsLat x (latOf g) (latOf h) :=
  mapsLat_iff.2 (hs _ (right_ne_zero_of_mul hx))

theorem om_per (hϖ : valuation k (ϖ : k) = uniformizer k) {μ : kˣ →* ℂˣ} {Φ : Matrix Y Y' k → ℂ}
    (hp : ∀ x y, MaxM y → Φ (x + y) = Φ x) (g : GL Y' k) (h : GL Y k)
    (x y : Matrix Y Y' k) (hy : MapsLat y (latOf g) (latOf h)) :
    om μ g h Φ (x + (ϖ : k) • y) = om μ g h Φ x := by
  unfold om
  rw [Matrix.mul_add, Matrix.add_mul, hp]
  intro i j
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul, hϖ]
  exact mul_lt_one_of_nonneg_of_lt_one_left zero_le uniformizer_lt_one (mapsLat_iff.1 hy i j)

end Lat

end GlobalTheory.LatClass
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.LatClass

variable {k : Type} [Field k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

omit [Fintype n] [DecidableEq n] [DecidableEq n'] in
theorem aff_low (x₀ : Matrix n n' k) (y) (w : n' → k) (s : k) :
    affPt (c := c + 1) 1 x₀ y *ᵥ Sum.elim w (Pi.single 0 s) = Sum.elim (x₀ *ᵥ w) (Pi.single 0 s) := by
  ext (r | l)
  · simp [mulVec, dotProduct, Fintype.sum_sum_type, affPt, basePt, Free, Pi.single_apply]
  · simp [mulVec, dotProduct, Fintype.sum_sum_type, affPt, basePt, Free, Pi.single_apply]

omit [Fintype n] [DecidableEq n] [DecidableEq n'] in
theorem aff_row (x₀ : Matrix n n' k) (y) (w : n' → k) (i : Fin (c + 1)) (s : k) (l : Fin c) :
    (affPt (c := c) 1 x₀ y *ᵥ Sum.elim w (Pi.single i s)) (.inr l) = affPt 1 x₀ y (.inr l) (.inr i) * s := by
  have : ∀ r, affPt (c := c) 1 x₀ y (.inr l) (.inl r) = 0 := fun r => by simp [affPt, basePt, Free]
  simp [mulVec, dotProduct, Fintype.sum_sum_type, this, Pi.single_apply]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem aff_diag (x₀ : Matrix n n' k) (y) (i l : Fin c) (h : i ≤ l) :
    affPt (c := c) 1 x₀ y (.inr l) (.inr i.castSucc) = if l = i then 1 else 0 := by
  have : ¬ l < i := not_lt.2 h
  simp [affPt, basePt, Free, this, Fin.ext_iff]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  {ϖ : kˣ} {ψ : AddChar k Circle} {ν : Measure k}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [BorelSpace k] [DecidableEq n]
  [DecidableEq n'] in
theorem exists_supp {p : ℕ} {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {x₀ : Matrix n n' k}
    (h : opE ψ ν p Ψ x₀ ≠ 0) : ∃ y, Ψ (affPt p x₀ y) ≠ 0 := by
  by_contra H
  push Not at H
  exact h (by simp [opE, H])

theorem bounds (hϖ : valuation k (ϖ : k) = uniformizer k) (hψ : HasConductor ψ 1) [ν.IsAddHaarMeasure]
    {g' : GL n' k} {e' : Fin (c + 1 + 1) → ℤ} {z' : n' → k} {h : GL (n ⊕ Fin (c + 1)) k}
    {Ψ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ}
    (hs : ∀ x, Ψ x ≠ 0 → MapsLat x (latOf (nfBasis ϖ g' e' z')) (latOf h))
    (hp : ∀ x y, MapsLat y (latOf (nfBasis ϖ g' e' z')) (latOf h) → Ψ (x + (ϖ : k) • y) = Ψ x)
    {x₀ : Matrix n n' k} (h0 : opE ψ ν 1 Ψ x₀ ≠ 0) (i : Fin (c + 1)) {a : ℤ}
    (ha : topCoord (latOf h) i = powInt ϖ a) : e' i.succ - 1 ≤ a ∧ a ≤ e' i.castSucc := by
  constructor
  · obtain ⟨v, hv, hv0, hvi⟩ : (ϖ : k) ^ a ∈ topCoord (latOf h) i := ha ▸ (zpow_mem_pow hϖ).2 le_rfl
    have key : -((ϖ : k) * ((ϖ : k) ^ (-e' i.succ) * (ϖ : k) ^ a)) ∈ 𝒪[k] := by
      refine Unram.mem_of_psi hψ fun t ht => ?_
      let y : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k :=
        Matrix.of fun r s => if s = .inr i.succ then t * (ϖ : k) ^ (-e' i.succ) * v r else 0
      have hy : MapsLat y (latOf (nfBasis ϖ g' e' z')) (latOf h) := fun w hw => by
        have : y *ᵥ w = (t * ((ϖ : k) ^ (-e' i.succ) * w (.inr i.succ))) • v := by
          ext r; simp [y, mulVec, dotProduct]; ring
        rw [this]
        refine smul_mem_lat (mul_mem ht ?_) hv
        rw [← mem_pow_zero (ϖ := ϖ), zpow_mul_mem_pow]
        simpa using (mem_nf.1 hw).2 i.succ
      have := Unram.psi_ch_eq_one ψ ν Ψ x₀ h0 ((ϖ : k) • y) (fun r s hf => ?_) fun x => hp x y hy
      · convert this using 2
        simp [ch, y, hvi]; ring
      · simp only [y, Matrix.smul_apply, Matrix.of_apply]
        split_ifs with e
        · subst e
          rcases r with r | r
          · simp [Free] at hf
          · rw [hv0 r (by simp only [Free, Fin.val_succ] at hf; rw [Fin.lt_def]; omega)]; simp
        · simp
    rw [neg_mem_iff, ← mem_pow_zero (ϖ := ϖ), ← zpow_add₀ ϖ.ne_zero, ← zpow_one_add₀ ϖ.ne_zero,
      zpow_mem_pow hϖ] at key
    omega
  · obtain ⟨y, hy⟩ := exists_supp h0
    have := hs _ hy _ (col_mem_nf i.castSucc ((zpow_mem_pow hϖ).2 le_rfl))
    rw [← zpow_mem_pow hϖ, ← ha]
    refine ⟨_, this, fun l hl => ?_, ?_⟩
    · rw [aff_row, aff_diag _ _ _ _ hl.le, if_neg hl.ne', zero_mul]
    · rw [aff_row, aff_diag _ _ _ _ le_rfl, if_pos rfl, one_mul]

omit [BorelSpace k] in
theorem first_mem (hϖ : valuation k (ϖ : k) = uniformizer k)
    {g' : GL n' k} {e' : Fin (c + 1 + 1) → ℤ} {z' : n' → k} {h : GL (n ⊕ Fin (c + 1)) k}
    {Ψ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ}
    (hs : ∀ x, Ψ x ≠ 0 → MapsLat x (latOf (nfBasis ϖ g' e' z')) (latOf h))
    {x₀ : Matrix n n' k} (h0 : opE ψ ν 1 Ψ x₀ ≠ 0) :
    ((ϖ ^ e' 0 : kˣ) : k) • (Sum.elim (x₀ *ᵥ z') (Pi.single 0 1) : n ⊕ Fin (c + 1) → k) ∈ latOf h ∧
      ∀ w ∈ latOf g', (Sum.elim (x₀ *ᵥ w) 0 : n ⊕ Fin (c + 1) → k) ∈ latOf h := by
  obtain ⟨y, hy⟩ := exists_supp h0
  constructor
  · have := hs _ hy _ (col_mem_nf 0 ((zpow_mem_pow hϖ).2 le_rfl))
    rw [aff_low] at this
    convert this using 1
    ext (r | l)
    · simp [mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
    · simp [Pi.single_apply]
  · intro w hw
    have := hs _ hy (Sum.elim w (Pi.single 0 0)) (mem_nf.2 ⟨by simpa using hw, fun i => by simpa using zero_mem_pow⟩)
    rw [aff_low] at this
    simpa using this

theorem step_normal (H : NormalFormModN k) (hϖ : valuation k (ϖ : k) = uniformizer k) (hψ : HasConductor ψ 1)
    [ν.IsAddHaarMeasure] {j : ℕ} {e' : Fin (c + 1 + 1) → ℤ} {z' : n' → k}
    (he' : ∀ i, -(j : ℤ) ≤ e' i ∧ e' i ≤ 0) (hz' : ∀ i, z' i ∈ 𝒪[k]) {h : GL (n ⊕ Fin (c + 1)) k}
    {Ψ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ}
    (hs : ∀ x, Ψ x ≠ 0 → MapsLat x (latOf (nfBasis ϖ 1 e' z')) (latOf h))
    (hp : ∀ x y, MapsLat y (latOf (nfBasis ϖ 1 e' z')) (latOf h) → Ψ (x + (ϖ : k) • y) = Ψ x)
    {x₀ : Matrix n n' k} (h0 : opE ψ ν 1 Ψ x₀ ≠ 0) :
    ∃ r ∈ R k n (c + 1) 1, ∃ (e : Fin (c + 1) → ℤ) (z : n → k),
      (∀ i, -((j + 1 : ℕ) : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (∀ i, z i ∈ 𝒪[k]) ∧
        latOf (r * h) = latOf (normalBasis ϖ e z) := by
  obtain ⟨u, hu, g, e, z, hl, hm⟩ := H ϖ hϖ n (c + 1) h
  have ht : ∀ i, topCoord (latOf h) i = powInt ϖ (e i) := fun i => by
    rw [← topCoord_R (Subgroup.mem_sup_right hu) h i, hl, topCoord_nf]
  refine ⟨embX _ g⁻¹ * u, mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right hu), e,
    (g⁻¹).val *ᵥ z, fun i => ?_, ?_, ?_⟩
  · have := bounds hϖ hψ hs hp h0 i (ht i)
    have := he' i.succ
    have := he' i.castSucc
    push_cast
    omega
  · obtain ⟨h1, h2⟩ := first_mem hϖ hs h0
    have h3 := (hm _).1 (h2 z' (mem_latOf_one.2 hz'))
    rw [← mulVec_mem_latOf u, N_fix hu _ (fun l hl => by simp [Fin.ext_iff, hl.ne']), hl] at h1
    have h4 := smul_mem_lat (t := (ϖ : k) ^ (-e' 0))
      (mem_pow_zero.1 ((zpow_mem_pow hϖ).2 (by have := he' 0; omega))) (mem_nf.1 h1).1
    have h5 := sub_mem h3 h4
    change z ∈ latOf g
    convert h5 using 1
    have : (ϖ : k) ^ e' 0 ≠ 0 := zpow_ne_zero _ ϖ.ne_zero
    ext r
    simp
    field_simp
    ring
  · rw [mul_assoc, latOf_mul_congr _ hl, embX_mul_nf, inv_mul_cancel, nfBasis_one]

end GlobalTheory.LatClass
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.LatClass

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem lat_of_coset {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {J : Subgroup (GL (n ⊕ Fin c) k)}
    (hJ : J ≤ KO k _) {a b : GL (n ⊕ Fin c) k}
    (h : DoubleCoset.mk (R k n c 1) J a = DoubleCoset.mk (R k n c 1) J b) :
    ∃ r ∈ R k n c 1, latOf b = latOf (r * a) := by
  obtain ⟨r, hr, w, hw, rfl⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 h
  exact ⟨r, hr, by rw [latOf_mul_congr _ (latOf_eq_of_KO (hJ hw)), mul_one]⟩

variable [MeasurableSpace k] [BorelSpace k]
variable {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]
  {T : Chain k s X Z} {ϖ : kˣ} {ψ : AddChar k Circle} {ν : Measure k} [ν.IsAddHaarMeasure]
  (hϖ : valuation k (ϖ : k) = uniformizer k) (hψ : HasConductor ψ 1)
  (hb : ∀ j c h, latOf (T.bas j c h) = latOf 1)
  (hs : ∀ j c h x, T.Phi j c h x ≠ 0 → IntM x)
  (hp : ∀ j c h x y, MaxM y → T.Phi j c h (x + y) = T.Phi j c h x)
  (hJ : ∀ j c h, (T.lev j c h).J ≤ KO k (X j ⊕ Fin c))

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in
include hb in
theorem lat_bas {j c h} (g : GL (X j ⊕ Fin c) k) : latOf (g * T.bas j c h) = latOf g := by
  rw [latOf_mul_congr _ (hb j c h), mul_one]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in
include hb in
theorem normal_one (c : ℕ) (h : 0 + c = s) : IsNormalRep T ϖ 0 c h 1 := by
  refine ⟨0, 0, fun i => by simp, fun i => zero_mem _, ?_⟩
  rw [lat_bas hb]
  ext y
  simp [mem_normal, mem_latOf_one, mem_pow_zero]

include hϖ hψ hb hs hp hJ

theorem exists_normal {A : RepFam k s X} (hA : T.IsRepSystem A ψ ν) (j : ℕ) :
    ∀ c h, ∀ g ∈ A j c h, ∃ r ∈ R k (X j) (c + 1) 1, IsNormalRep T ϖ j c h (r * g) := by
  induction j with
  | zero =>
    intro c h g hg
    rw [hA.zero] at hg
    obtain rfl : g = 1 := hg
    exact ⟨1, one_mem _, by rw [one_mul]; exact normal_one hb c h⟩
  | succ j ih =>
    intro c h g' hg'
    obtain ⟨g, hg, a, ha, hf⟩ := Set.mem_iUnion₂.1 ((hA.bij j c h).mapsTo hg')
    obtain ⟨r, hr, e', z', he', hz', hl⟩ := ih _ _ g hg
    rw [lat_bas hb, ← nfBasis_one] at hl
    obtain ⟨x₀, h0⟩ := Function.ne_iff.1 (GlobalTheory.FlatSourceStable.flat_ne_zero_of_mem_R k _ _ c ψ ν _ _ g a hf r hr)
    obtain ⟨r₂, hr₂, e, z, he, hz, hl₂⟩ := step_normal (NormalForm.normalFormModN k) hϖ hψ he' hz'
      (hl ▸ om_supp (hs _ _ _) (r * g) a) (hl ▸ om_per hϖ (hp _ _ _) (r * g) a) h0
    obtain ⟨r₃, hr₃, hl₃⟩ := lat_of_coset (hJ _ _ _) ha
    refine ⟨r₂ * r₃⁻¹, mul_mem hr₂ (inv_mem hr₃), e, z, he, hz, ?_⟩
    rw [lat_bas hb, latOf_mul_congr _ hl₃, ← hl₂]
    congr 1
    group

end GlobalTheory.LatClass

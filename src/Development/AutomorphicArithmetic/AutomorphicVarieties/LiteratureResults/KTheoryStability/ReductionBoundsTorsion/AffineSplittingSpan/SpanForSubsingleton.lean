module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanPrism

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanStep
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanInj
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanLevel
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanCup
noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismSpan

open PositivityTheory.KB.SplitAffineSpectral

section General

variable {Y : Type}

theorem dc_dc : ∀ (m : ℕ) (F : (Fin (m + 1) → Y) → ℝ), dc (dc F) = 0 := by
  intro m
  induction m with
  | zero =>
    intro F
    funext y
    simp [dc, Fin.sum_univ_succ]
    have hCD : (fun j : Fin 1 => y (Fin.succAbove 1 (Fin.succAbove 1 j))) =
        fun j => y (Fin.succAbove 2 (Fin.succAbove 1 j)) := by
      funext j
      rw [Subsingleton.elim j (0 : Fin 1)]
      rfl
    linear_combination congrArg F hCD
  | succ m ih =>
    intro F
    funext y
    rw [← Fin.cons_self_tail y, dc_cons]
    have e : (fun w' => dc F (Fin.cons (y 0) w')) = F - dc (fun w' => F (Fin.cons (y 0) w')) := by
      funext w'; rw [dc_cons]; rfl
    rw [e, dc_sub, ih]
    simp

theorem dc_neg {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) : dc (-F) = -dc F := by
  funext y; simp [dc, Finset.sum_neg_distrib]

theorem prism_zero (φ : Y → Y) : ∀ {n : ℕ}, prism φ (0 : (Fin (n + 1) → Y) → ℝ) = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext y
    rw [prism_succ]
    change 0 - prism φ (0 : (Fin (n + 1) → Y) → ℝ) (Fin.tail y) = 0
    simp only [ih, Pi.zero_apply, sub_zero]

end General

section Grp

variable {P : Type} [Group P]

theorem dc_inv (S : Set P) {m : ℕ} (F : (Fin (m + 1) → P) → ℝ) (hF : InvS S F) : InvS S (dc F) := by
  intro g hg y
  simp only [dc]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg _ (hF g hg _)

def tcup (l : Additive P →+ ℝ) {n : ℕ} (e : (Fin (n + 1) → P) → ℝ) : (Fin (n + 2) → P) → ℝ :=
  fun y => l (Additive.ofMul ((y 0)⁻¹ * y 1)) * e (Fin.tail y)

theorem tail_eq' {α : Type} {k : ℕ} (q : Fin (k + 1) → α) : Fin.tail q = fun i => q i.succ := rfl

theorem dc_tcup (l : Additive P →+ ℝ) {n : ℕ} (e : (Fin (n + 1) → P) → ℝ) :
    dc (tcup l e) = -tcup l (dc e) := by
  funext y
  simp [dc, tcup, Fin.sum_univ_succ, tail_eq']
  simp only [pow_succ, mul_add, Finset.mul_sum, neg_add, ← Finset.sum_neg_distrib]
  ring_nf

theorem tcup_inv (l : Additive P →+ ℝ) (S : Set P) {n : ℕ} (e : (Fin (n + 1) → P) → ℝ) (he : InvS S e) :
    InvS S (tcup l e) := by
  intro g hg y
  simp only [tcup]
  rw [show (g * y 0)⁻¹ * (g * y 1) = (y 0)⁻¹ * y 1 by group]
  congr 1
  exact he g hg (Fin.tail y)

theorem tcup_add (l : Additive P →+ ℝ) {n : ℕ} (e f : (Fin (n + 1) → P) → ℝ) :
    tcup l (e + f) = tcup l e + tcup l f := by
  funext y; simp [tcup, mul_add]

theorem tcup_sum (l : Additive P →+ ℝ) {n k : ℕ} (a : Fin k → ℝ) (F : Fin k → (Fin (n + 1) → P) → ℝ) :
    tcup l (∑ i, a i • F i) = ∑ i, a i • tcup l (F i) := by
  funext y
  simp only [tcup, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem tcup_cupH (l : Additive P →+ ℝ) {q : ℕ} (β : Fin q → (Additive P →+ ℝ)) :
    tcup l (cupH β) = cupH (Fin.cons l β) := by
  funext y
  simp [tcup, cupH, Fin.prod_univ_succ, Fin.tail]

end Grp

end PositivityTheory.KB.SplitAffineSpectral.PrismSpan

end
end

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismSpan

open PositivityTheory.KB.SplitAffineSpectral

variable {P : Type} [Group P]

def levSum (t : P) (lev : P → ℤ) {n : ℕ} (w : (Fin (n + 1) → P) → ℝ) (y : Fin (n + 1) → P) : ℝ :=
  if 0 ≤ lev (y 0) then ∑ j ∈ Finset.range (lev (y 0)).toNat, w (fun i => t ^ (-((j : ℤ) + 1)) * y i)
  else -∑ j ∈ Finset.range (-lev (y 0)).toNat, w (fun i => t ^ (j : ℤ) * y i)

theorem levSum_spec (t : P) (lev : P → ℤ) (hlev : ∀ z, lev (t * z) = lev z + 1) {n : ℕ}
    (w : (Fin (n + 1) → P) → ℝ) (y : Fin (n + 1) → P) :
    levSum t lev w (fun i => t * y i) - levSum t lev w y = w y := by
  unfold levSum
  have e : ∀ k : ℤ, (fun i => t ^ k * (t * y i)) = fun i => t ^ (k + 1) * y i := by
    intro k
    funext i
    rw [← mul_assoc, ← zpow_add_one]
  simp only [hlev, e]
  generalize lev (y 0) = a
  rcases le_or_gt 0 a with h | h
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [if_pos (by omega), if_pos h]
    rw [show ((m : ℤ) + 1).toNat = m + 1 by omega, Int.toNat_natCast, Finset.sum_range_succ']
    have ex : ∀ j : ℕ, -(((j + 1 : ℕ) : ℤ) + 1) + 1 = -((j : ℤ) + 1) := by
      intro j
      push_cast
      ring
    simp only [ex]
    simp
  · obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero h
    rcases m with _ | k
    · rw [if_pos (by omega), if_neg (by omega)]
      simp
    · rw [if_neg (by omega), if_neg (by omega)]
      rw [show (-(Int.negSucc (k + 1) + 1)).toNat = k + 1 by omega,
        show (-Int.negSucc (k + 1)).toNat = k + 1 + 1 by omega, Finset.sum_range_succ' _ (k + 1)]
      have ex : ∀ j : ℕ, ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) := by
        intro j
        push_cast
        rfl
      simp only [ex]
      simp

theorem levSum_inv (t : P) (lev : P → ℤ) (S : Set P) (hS : ∀ g ∈ S, ∀ z, lev (g * z) = lev z)
    (hc : ∀ g ∈ S, g * t = t * g) {n : ℕ} (w : (Fin (n + 1) → P) → ℝ) (hw : InvS S w) :
    InvS S (levSum t lev w) := by
  intro g hg y
  unfold levSum
  simp only [hS g hg]
  have hk : ∀ k : ℤ, (fun i => t ^ k * (g * y i)) = fun i => g * (t ^ k * y i) := by
    intro k; funext i
    rw [← mul_assoc, ← mul_assoc, ((Commute.zpow_right (hc g hg) k)).eq]
  simp only [hk, hw g hg]

end PositivityTheory.KB.SplitAffineSpectral.PrismSpan

end
end

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismSpan

open PositivityTheory.KB.SplitAffineSpectral

structure WData (G P : Type) [Group G] [Group P] where
  ι : G →* P
  ρ : P →* G
  ℓ : Additive P →+ ℤ
  t : P
  ρι : ∀ g, ρ (ι g) = g
  ρt : ρ t = 1
  ℓι : ∀ g, ℓ (Additive.ofMul (ι g)) = 0
  ℓt : ℓ (Additive.ofMul t) = 1
  tc : ∀ z, t * z = z * t
  dec : ∀ p, p = ι (ρ p) * t ^ (ℓ (Additive.ofMul p))

variable {G P : Type} [Group G] [Group P] (W : WData G P)

def WData.pr (z : P) : P := W.ι (W.ρ z)

def WData.ps (z : P) : P := W.t⁻¹ * W.ι (W.ρ z)

theorem WData.comm_range (g : P) (_hg : g ∈ Set.range W.ι) : g * W.t = W.t * g := (W.tc g).symm

theorem WData.pr_mul (g : P) (hg : g ∈ Set.range W.ι) (z : P) : W.pr (g * z) = g * W.pr z := by
  obtain ⟨g', rfl⟩ := hg
  simp [WData.pr, W.ρι]

theorem WData.inv_univ {n : ℕ} (F : (Fin n → P) → ℝ) (hS : InvS (Set.range W.ι) F)
    (ht : ∀ y, F (fun i => W.t * y i) = F y) : InvS Set.univ F := by
  have hk : ∀ k : ℤ, ∀ y, F (fun i => W.t ^ k * y i) = F y := by
    intro k
    induction k using Int.induction_on with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [← ih y, ← ht (fun i => W.t ^ (k : ℤ) * y i)]
      congr 1; funext i
      rw [← mul_assoc, ← zpow_one_add, add_comm]
    | pred k ih =>
      intro y
      rw [← ih y, ← ht (fun i => W.t ^ (-(k : ℤ) - 1) * y i)]
      congr 1; funext i
      rw [← mul_assoc, ← zpow_one_add]; congr 2; ring
  intro p _ y
  have : (fun i => p * y i) = fun i => W.ι (W.ρ p) * (W.t ^ (W.ℓ (Additive.ofMul p)) * y i) := by
    funext i; rw [← mul_assoc, ← W.dec p]
  rw [this, hS _ ⟨_, rfl⟩, hk]

theorem WData.vanish_range {n : ℕ} (F : (Fin n → P) → ℝ) (hF : ∀ g : Fin n → G, F (fun i => W.ι (g i)) = 0)
    (z : Fin n → P) (hz : ∀ i, z i ∈ Set.range W.ι) : F z = 0 := by
  choose g hg using hz
  have : z = fun i => W.ι (g i) := by funext i; exact (hg i).symm
  rw [this, hF]

theorem dc_one {Y : Type} (F : (Fin 1 → Y) → ℝ) (a : Y) (y : Fin 1 → Y) :
    dc F (Fin.cons a y) = F y - F (fun _ => a) := by
  simp [dc, Fin.sum_univ_succ]
  have h1 : (fun j : Fin 1 => (Fin.cons a y : Fin 2 → Y) (Fin.succAbove 1 j)) = fun _ => a := by
    funext j; fin_cases j; rfl
  rw [h1]
  ring

theorem WData.inj (m : ℕ) (c : (Fin (m + 2) → P) → ℝ) (hc : InvS Set.univ c) (hdc : dc c = 0)
    (hres : ∀ g : Fin (m + 2) → G, c (fun i => W.ι (g i)) = 0)
    (hsl : ∀ g : Fin (m + 1) → G, prism W.ps c (fun i => W.ι (g i)) = 0) :
    ∃ e : (Fin (m + 1) → P) → ℝ, InvS Set.univ e ∧ c = dc e := by
  set S := Set.range W.ι with hSdef
  have hcS : InvS S c := fun g _ y => hc g trivial y
  have hprS : ∀ z ∈ S, W.pr z ∈ S := fun z _ => ⟨_, rfl⟩
  set x := prism W.pr c with hxdef
  have hxS : InvS S x := prism_inv W.pr S W.pr_mul c hcS
  have hdx : dc x = -c := by
    funext y
    have h := prism_dc W.pr m c y
    rw [hdc, prism_zero] at h
    have h0 : c (fun i => W.pr (y i)) = 0 := hres (fun i => W.ρ (y i))
    simp only [Pi.zero_apply, add_zero, h0, zero_sub] at h
    simpa using h
  have hx0 : ∀ g : Fin (m + 1) → G, x (fun i => W.ι (g i)) = 0 := fun g =>
    prism_eq_zero_of_set W.pr S hprS c _ (W.vanish_range c hres) (fun i => ⟨_, rfl⟩)
  have hxt : ∀ g : Fin (m + 1) → G, x (fun i => W.t * W.ι (g i)) = 0 := by
    intro g
    rw [hxdef, prism_mul]
    have e1 : (fun z => W.t⁻¹ * W.pr (W.t * z)) = W.ps := by
      funext z; simp [WData.pr, WData.ps, W.ρt]
    have e2 : (fun z : Fin (m + 2) → P => c (fun i => W.t * z i)) = c := by
      funext z; exact hc _ trivial z
    rw [e1, e2]
    exact hsl g
  have hv0 : ∀ g : Fin (m + 1) → G, x (fun i => W.t * W.ι (g i)) - x (fun i => W.ι (g i)) = 0 := by
    intro g; rw [hxt, hx0, sub_zero]
  have hdv : dc ((fun y => x (fun i => W.t * y i)) - x) = 0 := by
    rw [dc_sub]; funext z
    simp only [Pi.sub_apply, Pi.zero_apply]
    rw [dc_comp x (fun p => W.t * p) z, hdx]
    simp only [Pi.neg_apply]
    rw [hc _ trivial z]; ring
  have hvS : InvS S ((fun y => x (fun i => W.t * y i)) - x) := by
    intro g hg y
    simp only [Pi.sub_apply]
    have : (fun i => W.t * (g * y i)) = fun i => g * (W.t * y i) := by
      funext i; rw [← mul_assoc, ← mul_assoc, W.comm_range g hg]
    rw [this, hxS g hg, hxS g hg]
  cases m with
  | zero =>
    have hvz : ∀ y : Fin 1 → P, x (fun i => W.t * y i) = x y := by
      intro y
      have h := congrFun hdv (Fin.cons (W.ι 1) y)
      rw [dc_one] at h
      have h1 := hv0 (fun _ => 1)
      simp only [Pi.sub_apply, Pi.zero_apply] at h h1
      linarith
    refine ⟨-x, ?_, ?_⟩
    · have hx := W.inv_univ x hxS hvz
      intro g hg y; simp only [Pi.neg_apply]; rw [hx g hg y]
    · rw [dc_neg, hdx, neg_neg]
  | succ m' =>
    set v := (fun y => x (fun i => W.t * y i)) - x with hvdef
    set w := -prism W.pr v with hwdef
    have hdw : dc w = v := by
      funext y
      have h := prism_dc W.pr m' v y
      rw [hdv, prism_zero] at h
      have h0 : v (fun i => W.pr (y i)) = 0 := hv0 (fun i => W.ρ (y i))
      simp only [Pi.zero_apply, add_zero, h0, zero_sub] at h
      rw [hwdef, dc_neg, Pi.neg_apply, h, neg_neg]
    have hwS : InvS S w := by
      intro g hg y
      simp only [hwdef, Pi.neg_apply]
      rw [prism_inv W.pr S W.pr_mul v hvS g hg y]
    set lev : P → ℤ := fun z => W.ℓ (Additive.ofMul z) with hlevdef
    have hlev : ∀ z, lev (W.t * z) = lev z + 1 := by
      intro z; simp only [hlevdef, ofMul_mul, map_add (f := _), W.ℓt]; ring
    have hlevS : ∀ g ∈ S, ∀ z, lev (g * z) = lev z := by
      rintro g ⟨g', rfl⟩ z; simp only [hlevdef, ofMul_mul, map_add (f := _), W.ℓι, zero_add]
    set w' := levSum W.t lev w with hw'def
    have hw'S : InvS S w' := levSum_inv W.t lev S hlevS W.comm_range w hwS
    have hw'w : (fun y => w' (fun i => W.t * y i)) - w' = w := by
      funext y; exact levSum_spec W.t lev hlev w y
    set e0 := x - dc w' with he0def
    have he0S : InvS S e0 := by
      intro g hg y
      simp only [he0def, Pi.sub_apply]
      rw [hxS g hg y, dc_inv S w' hw'S g hg y]
    have he0t : ∀ y, e0 (fun i => W.t * y i) = e0 y := by
      intro y
      have h1 : dc ((fun y => w' (fun i => W.t * y i)) - w') y = v y := by rw [hw'w, hdw]
      rw [dc_sub] at h1
      simp only [Pi.sub_apply] at h1
      rw [dc_comp w' (fun p => W.t * p) y] at h1
      simp only [he0def, Pi.sub_apply, hvdef] at h1 ⊢
      linarith
    have he0 := W.inv_univ e0 he0S he0t
    refine ⟨-e0, ?_, ?_⟩
    · intro g hg y; simp only [Pi.neg_apply]; rw [he0 g hg y]
    · rw [dc_neg, he0def, dc_sub, dc_dc, sub_zero, hdx, neg_neg]

end PositivityTheory.KB.SplitAffineSpectral.PrismSpan

end
end

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismSpan

private theorem prism_sub' {Y : Type} (φ : Y → Y) : ∀ {n : ℕ} (F G : (Fin (n + 1) → Y) → ℝ),
    prism φ (F - G) = prism φ F - prism φ G := by
  intro n
  induction n with
  | zero =>
    intro F G
    funext y
    simp [prism]
  | succ n ih =>
    intro F G
    funext y
    rw [Pi.sub_apply, prism_succ, prism_succ, prism_succ]
    have hsub : prism φ (fun w => F (Fin.cons (y 0) w) - G (Fin.cons (y 0) w)) (Fin.tail y) =
        prism φ (fun w => F (Fin.cons (y 0) w)) (Fin.tail y) -
          prism φ (fun w => G (Fin.cons (y 0) w)) (Fin.tail y) :=
      congrFun (ih (fun w => F (Fin.cons (y 0) w)) (fun w => G (Fin.cons (y 0) w))) (Fin.tail y)
    change _ - _ - prism φ (fun w => F (Fin.cons (y 0) w) - G (Fin.cons (y 0) w))
      (Fin.tail y) = _
    rw [hsub]
    ring


open PositivityTheory.KB.SplitAffineSpectral

def SpanFor (A : Type) [Group A] : Prop :=
  ∀ (q : ℕ) (c : (Fin (q + 2) → A) → ℝ), InvS Set.univ c → dc c = 0 →
    ∃ (k : ℕ) (a : Fin k → ℝ) (α : Fin k → Fin (q + 1) → (Additive A →+ ℝ))
      (e : (Fin (q + 1) → A) → ℝ), InvS Set.univ e ∧ c = (∑ i, a i • cupH (α i)) + dc e

variable {G P : Type} [Group G] [Group P]

theorem pull_inv (ρ : P →* G) {n : ℕ} (F : (Fin n → G) → ℝ) (hF : InvS Set.univ F) :
    InvS Set.univ (fun z : Fin n → P => F (fun i => ρ (z i))) := by
  intro g _ y
  simp only [map_mul]
  exact hF _ trivial _

theorem pull_sum (ρ : P →* G) {n k : ℕ} (a : Fin k → ℝ) (α : Fin k → Fin n → (Additive G →+ ℝ)) :
    (fun z : Fin (n + 1) → P => (∑ i, a i • cupH (α i)) (fun j => ρ (z j))) =
      ∑ i, a i • cupH (fun j => (α i j).comp (MonoidHom.toAdditive ρ)) := by
  funext z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cupH, AddMonoidHom.comp_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  refine Finset.prod_congr rfl (fun j _ => ?_)
  simp [map_mul, map_inv]

theorem sum_append {Y : Type} {k1 k2 : ℕ} (a1 : Fin k1 → ℝ) (a2 : Fin k2 → ℝ) (F1 : Fin k1 → Y → ℝ)
    (F2 : Fin k2 → Y → ℝ) :
    ∑ i, Fin.append a1 a2 i • Fin.append F1 F2 i = (∑ i, a1 i • F1 i) + ∑ i, a2 i • F2 i := by
  rw [Fin.sum_univ_add]
  simp

variable (W : WData G P)

def WData.lR : Additive P →+ ℝ := (Int.castAddHom ℝ).comp W.ℓ

theorem WData.tdecomp (hG : SpanFor G) (q : ℕ) (a : (Fin (q + 1) → G) → ℝ) (ha : InvS Set.univ a)
    (hda : dc a = 0) : ∃ (k : ℕ) (b : Fin k → ℝ) (β : Fin k → Fin (q + 1) → (Additive P →+ ℝ))
      (e : (Fin (q + 1) → P) → ℝ), InvS Set.univ e ∧
        tcup W.lR (fun z : Fin (q + 1) → P => a (fun i => W.ρ (z i))) = (∑ i, b i • cupH (β i)) + dc e := by
  cases q with
  | zero =>
    have hconst : ∀ y : Fin 1 → G, a y = a (fun _ => 1) := by
      intro y
      have := ha (y 0)⁻¹ (Set.mem_univ _) y
      rw [← this]
      congr 1
      funext j
      rw [Fin.fin_one_eq_zero j, inv_mul_cancel]
    refine ⟨1, fun _ => a (fun _ => 1), fun _ => fun _ => W.lR, 0, fun _ _ _ => rfl, ?_⟩
    funext y
    simp [tcup, cupH, hconst, mul_comm, dc]
  | succ q =>
    obtain ⟨k, a', α, eG, heG, hdecomp⟩ := hG q a ha hda
    refine ⟨k, a', fun i => Fin.cons W.lR (fun j => (α i j).comp (MonoidHom.toAdditive W.ρ)),
      (-1 : ℝ) • tcup W.lR (fun z => eG (fun i => W.ρ (z i))), ?_, ?_⟩
    · intro g _ y
      simp only [Pi.smul_apply]
      rw [tcup_inv W.lR Set.univ _ (pull_inv W.ρ eG heG) g (Set.mem_univ _) y]
    · have hpull : (fun z : Fin (q + 2) → P => a (fun i => W.ρ (z i))) =
          (fun z : Fin (q + 2) → P => (∑ i, a' i • cupH (α i)) (fun j => W.ρ (z j))) +
            dc (fun z => eG (fun i => W.ρ (z i))) := by
        funext z
        rw [hdecomp]
        rfl
      rw [hpull, pull_sum, tcup_add, tcup_sum, dc_smul, dc_tcup]
      simp only [tcup_cupH]
      simp

private theorem wData_ps_iota_eq_t_inv_mul (W : WData G P) (g : G) : W.ps (W.ι g) = W.t⁻¹ * W.ι g := by
  simp [WData.ps, W.ρι]

private theorem wData_rho_ps_eq_rho (W : WData G P) (z : P) : W.ρ (W.ps z) = W.ρ z := by
  simp [WData.ps, W.ρι, W.ρt]

private theorem wData_lR_ofMul_iota_eq_zero (W : WData G P) (g : G) : W.lR (Additive.ofMul (W.ι g)) = 0 := by
  simp [WData.lR, W.ℓι]

private theorem wData_lR_ofMul_t_inv_eq_neg_one (W : WData G P) : W.lR (Additive.ofMul W.t⁻¹) = -1 := by
  simp [WData.lR, ofMul_inv, W.ℓt]

private theorem wData_ps_iota_mul_eq_iota_mul_ps (W : WData G P) (h : G) (z : P) : W.ps (W.ι h * z) = W.ι h * W.ps z := by
  have htc : ∀ x : P, W.t⁻¹ * x = x * W.t⁻¹ := by
    intro x
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, W.tc x, mul_assoc, mul_inv_cancel, mul_one]
  simp only [WData.ps, map_mul, W.ρι]
  rw [← mul_assoc, htc, mul_assoc]

private theorem wData_prism_ps_tcup_lR_iota_eq_neg (W : WData G P) {q : ℕ} (Y : (Fin (q + 1) → G) → ℝ)
    (g : Fin (q + 1) → G) :
    prism W.ps (tcup W.lR (fun z : Fin (q + 1) → P => Y (fun i => W.ρ (z i))))
      (fun i => W.ι (g i)) = - Y g := by
  have prism_zero {Y : Type} (φ : Y → Y) : ∀ {n : ℕ}, prism φ (0 : (Fin (n + 1) → Y) → ℝ) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      funext y
      rw [prism_succ]
      change 0 - prism φ (0 : (Fin (n + 1) → Y) → ℝ) (Fin.tail y) = 0
      simp only [ih, Pi.zero_apply, sub_zero]
  rw [prism_succ]
  have htc : ∀ x : P, W.t⁻¹ * x = x * W.t⁻¹ := by
    intro x
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, W.tc x, mul_assoc, mul_inv_cancel, mul_one]
  have h1 : tcup W.lR (fun z : Fin (q + 1) → P => Y (fun i => W.ρ (z i)))
      (Fin.cons (W.ι (g 0)) fun i => W.ps (W.ι (g i))) = - Y g := by
    simp only [tcup, Fin.cons_zero, Fin.cons_one, Fin.tail_cons, wData_rho_ps_eq_rho, W.ρι, wData_ps_iota_eq_t_inv_mul]
    rw [htc, ← mul_assoc, inv_mul_cancel, one_mul, wData_lR_ofMul_t_inv_eq_neg_one]
    simp [W.ρt, W.ρι]
  have h2 : prism W.ps (fun w : Fin (q + 1) → P =>
      tcup W.lR (fun z : Fin (q + 1) → P => Y (fun i => W.ρ (z i))) (Fin.cons (W.ι (g 0)) w))
      (Fin.tail fun i => W.ι (g i)) = 0 := by
    cases q with
    | zero => rw [prism.eq_1]
    | succ q =>
      rw [prism_succ]
      have h0 : (fun w : Fin (q + 1) → P =>
          tcup W.lR (fun z : Fin (q + 2) → P => Y (fun i => W.ρ (z i)))
            (Fin.cons (W.ι (g 0)) (Fin.cons ((Fin.tail fun i => W.ι (g i)) 0) w))) = 0 := by
        funext w
        simp only [tcup, Fin.cons_zero, Fin.cons_one, Fin.cons_zero, Fin.tail, Pi.zero_apply]
        rw [← map_inv, ← map_mul, wData_lR_ofMul_iota_eq_zero, zero_mul]
      rw [h0, prism_zero]
      simp only [tcup, Fin.cons_zero, Fin.cons_one, Fin.tail, Pi.zero_apply]
      rw [← map_inv, ← map_mul, wData_lR_ofMul_iota_eq_zero, zero_mul, sub_zero]
  rw [h1, h2, sub_zero]

private theorem wData_dc_prism_ps_iota_eq_zero_of_dc_eq_zero (W : WData G P) {m : ℕ} (F : (Fin (m + 2) → P) → ℝ) (hF : dc F = 0)
    (hps : ∀ g : Fin (m + 2) → G, F (fun i => W.ps (W.ι (g i))) = F (fun i => W.ι (g i))) :
    dc (fun g : Fin (m + 1) → G => prism W.ps F (fun i => W.ι (g i))) = 0 := by
  have prism_zero {Y : Type} (φ : Y → Y) : ∀ {n : ℕ}, prism φ (0 : (Fin (n + 1) → Y) → ℝ) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      funext y
      rw [prism_succ]
      change 0 - prism φ (0 : (Fin (n + 1) → Y) → ℝ) (Fin.tail y) = 0
      simp only [ih, Pi.zero_apply, sub_zero]
  have prism_dc {Y : Type} (φ : Y → Y) : ∀ (m : ℕ) (F : (Fin (m + 2) → Y) → ℝ) (y : Fin (m + 2) → Y),
      dc (prism φ F) y + prism φ (dc F) y = F (fun i => φ (y i)) - F y := by
    intro m
    induction m with
    | zero =>
      intro F y
      simp [dc, prism, Fin.sum_univ_succ, Fin.tail]
      have h1 : (Fin.cons (y 0) (fun i : Fin 1 => φ (y (Fin.succAbove 1 i))) : Fin 2 → Y) =
          fun j => (Fin.cons (y 0) (fun i => φ (y i)) : Fin 3 → Y) (Fin.succAbove 2 j) := by
        funext j; fin_cases j <;> rfl
      have h2 : (fun j => (Fin.cons (y 0) (Fin.cons (y 1) (fun i : Fin 1 => φ (y i.succ)) : Fin 2 → Y) :
          Fin 3 → Y) (Fin.succAbove 1 j)) =
          fun j => (Fin.cons (y 0) (fun i => φ (y i)) : Fin 3 → Y) (Fin.succAbove 1 j) := by
        funext j; fin_cases j <;> rfl
      have h3 : (fun j => (Fin.cons (y 0) (Fin.cons (y 1) (fun i : Fin 1 => φ (y i.succ)) : Fin 2 → Y) :
          Fin 3 → Y) (Fin.succAbove 2 j)) = y := by
        funext j; fin_cases j <;> rfl
      rw [h1, h2, h3]
      ring
    | succ m ih =>
      intro F y
      rw [← Fin.cons_self_tail y]
      set a := y 0
      set w := Fin.tail y
      have h := ih (fun w' => F (Fin.cons a w')) w
      rw [dc_cons, prism_cons]
      have e1 : (fun w' => prism φ F (Fin.cons a w')) =
          (fun w' => F (Fin.cons a (Fin.cons (φ a) (fun i => φ (w' i))))) -
            prism φ (fun w' => F (Fin.cons a w')) := by
        funext w'; rw [prism_cons]; rfl
      have e2 : (fun w' => dc F (Fin.cons a w')) =
          F - dc (fun w' => F (Fin.cons a w')) := by
        funext w'; rw [dc_cons]; rfl
      rw [e1, e2, dc_sub, prism_sub, dc_cons, dc_cons]
      simp only [Pi.sub_apply]
      rw [comp_cons']
      have e4 : dc (fun w' => F (Fin.cons a (Fin.cons (φ a) (fun i => φ (w' i))))) w =
          dc (fun w' => F (Fin.cons a (Fin.cons (φ a) w'))) (fun i => φ (w i)) := rfl
      rw [e4]
      linarith only [h]
  funext y
  have h := prism_dc W.ps m F (fun i => W.ι (y i))
  rw [hF, prism_zero, Pi.zero_apply, add_zero, hps, sub_self] at h
  exact h

private theorem wData_invS_prism_ps_iota_of_invS (W : WData G P) {n : ℕ} (F : (Fin (n + 1) → P) → ℝ) (hF : InvS Set.univ F) :
    InvS Set.univ (fun g : Fin n → G => prism W.ps F (fun i => W.ι (g i))) := by
  have hF' : InvS (Set.range W.ι) F := fun g _ y => hF g (Set.mem_univ _) y
  have hP := prism_inv W.ps (Set.range W.ι)
    (by rintro _ ⟨h, rfl⟩ z; exact wData_ps_iota_mul_eq_iota_mul_ps W h z) F hF'
  intro h _ y
  simp only [map_mul]
  exact hP (W.ι h) ⟨h, rfl⟩ _

theorem WData.step' (W' : WData G P) (hG : SpanFor G) : SpanFor P := by
  intro q c hc hdc
  let a : (Fin (q + 2) → G) → ℝ := fun g => c (fun i => W'.ι (g i))
  have ha : InvS Set.univ a := by
    intro h _ y
    simp only [a, map_mul]
    exact hc _ (Set.mem_univ _) _
  have hda : dc a = 0 := by
    funext y
    show dc c (fun i => W'.ι (y i)) = 0
    rw [hdc]; rfl
  let A : (Fin (q + 2) → P) → ℝ := fun z => a (fun i => W'.ρ (z i))
  have hAinv : InvS Set.univ A := pull_inv W'.ρ a ha
  have hdA : dc A = 0 := by
    funext y
    show dc a (fun i => W'.ρ (y i)) = 0
    rw [hda]; rfl
  let b : (Fin (q + 1) → G) → ℝ := fun g =>
    prism W'.ps A (fun i => W'.ι (g i)) - prism W'.ps c (fun i => W'.ι (g i))
  have hbinv : InvS Set.univ b := by
    intro h _ y
    simp only [b]
    exact congrArg₂ (fun u v => u - v) (wData_invS_prism_ps_iota_of_invS W' A hAinv h (Set.mem_univ _) y)
      (wData_invS_prism_ps_iota_of_invS W' c hc h (Set.mem_univ _) y)
  have hdb : dc b = 0 := by
    have h1 := wData_dc_prism_ps_iota_eq_zero_of_dc_eq_zero W' A hdA (fun g => by simp only [A, wData_rho_ps_eq_rho])
    have h2 := wData_dc_prism_ps_iota_eq_zero_of_dc_eq_zero W' c hdc (fun g => by
      simp only [wData_ps_iota_eq_t_inv_mul]
      exact hc _ (Set.mem_univ _) _)
    have : b = (fun g : Fin (q + 1) → G => prism W'.ps A (fun i => W'.ι (g i))) -
        (fun g : Fin (q + 1) → G => prism W'.ps c (fun i => W'.ι (g i))) := rfl
    rw [this, dc_sub, h1, h2, sub_zero]
  let T : (Fin (q + 2) → P) → ℝ := tcup W'.lR (fun z => b (fun i => W'.ρ (z i)))
  have hTinv : InvS Set.univ T := tcup_inv W'.lR Set.univ _ (pull_inv W'.ρ b hbinv)
  have hdT : dc T = 0 := by
    have : dc (fun z : Fin (q + 1) → P => b (fun i => W'.ρ (z i))) = 0 := by
      funext y
      show dc b (fun i => W'.ρ (y i)) = 0
      rw [hdb]; rfl
    simp only [T]
    rw [dc_tcup, this]
    funext y
    simp [tcup]
  have hinv' : InvS Set.univ (c - A - T) := by
    intro h _ y
    simp only [Pi.sub_apply]
    rw [hc h (Set.mem_univ _) y, hAinv h (Set.mem_univ _) y, hTinv h (Set.mem_univ _) y]
  have hdc' : dc (c - A - T) = 0 := by
    rw [dc_sub, dc_sub, hdc, hdA, hdT, sub_zero, sub_zero]
  have hι : ∀ g : Fin (q + 2) → G, (c - A - T) (fun i => W'.ι (g i)) = 0 := by
    intro g
    simp only [Pi.sub_apply, A, a, T, tcup, W'.ρι]
    rw [← map_inv, ← map_mul, wData_lR_ofMul_iota_eq_zero, zero_mul, sub_self, sub_zero]
  have hpr : ∀ g : Fin (q + 1) → G, prism W'.ps (c - A - T) (fun i => W'.ι (g i)) = 0 := by
    intro g
    rw [prism_sub, prism_sub]
    simp only [Pi.sub_apply, T]
    rw [wData_prism_ps_tcup_lR_iota_eq_neg W' b g]
    simp only [b]
    ring
  obtain ⟨e', he', hce'⟩ := W'.inj q (c - A - T) hinv' hdc' hι hpr
  obtain ⟨k1, a1, α1, eG, heG, hdecA⟩ := hG q a ha hda
  obtain ⟨k2, b2, β2, e2, he2, hdecB⟩ := W'.tdecomp hG q b hbinv hdb
  refine ⟨k1 + k2, Fin.append a1 b2,
    Fin.append (fun i j => (α1 i j).comp (MonoidHom.toAdditive W'.ρ)) β2,
    (fun z => eG (fun i => W'.ρ (z i))) + e2 + e', ?_, ?_⟩
  · intro h _ y
    simp only [Pi.add_apply]
    have h1 : (eG fun i => W'.ρ (h * y i)) = eG fun i => W'.ρ (y i) :=
      pull_inv W'.ρ eG heG h (Set.mem_univ _) y
    rw [h1, he2 h (Set.mem_univ _) y, he' h (Set.mem_univ _) y]
  · have hA' : A = (∑ i, a1 i • cupH (fun j => (α1 i j).comp (MonoidHom.toAdditive W'.ρ))) +
        dc (fun z => eG (fun i => W'.ρ (z i))) := by
      have : A = (fun z : Fin (q + 2) → P => (∑ i, a1 i • cupH (α1 i)) (fun j => W'.ρ (z j))) +
          dc (fun z => eG (fun i => W'.ρ (z i))) := by
        funext z
        show a (fun i => W'.ρ (z i)) = _
        rw [hdecA]
        rfl
      rw [this, pull_sum]
    have hT' : T = (∑ i, b2 i • cupH (β2 i)) + dc e2 := hdecB
    have hsplit : c = A + T + (c - A - T) := by abel
    have hfa : ∀ i, cupH (Fin.append (fun (i : Fin k1) (j : Fin (q + 1)) => (α1 i j).comp (MonoidHom.toAdditive W'.ρ)) β2 i) =
        Fin.append (fun i => cupH (fun j => (α1 i j).comp (MonoidHom.toAdditive W'.ρ))) (fun i => cupH (β2 i)) i := by
      intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [Fin.append_left, Fin.append_right]
    simp only [hfa]
    rw [hsplit, hce', hA', hT', sum_append, dc_add, dc_add]
    abel

end PositivityTheory.KB.SplitAffineSpectral.PrismSpan

end
end

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismSpan

open PositivityTheory.KB.SplitAffineSpectral

theorem altsum (n : ℕ) : ∑ i : Fin n, (-1 : ℝ) ^ (i : ℕ) = if Even n then 0 else 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last, ih]
    rcases Nat.even_or_odd n with h | h
    · have h' : ¬ Even (n + 1) := Nat.not_even_iff_odd.mpr (h.add_odd (by decide))
      simp [h, h', h.neg_one_pow]
    · have h' : ¬ Even n := Nat.not_even_iff_odd.mpr h
      have h'' : Even (n + 1) := h.add_odd (by decide)
      simp [h', h'', h.neg_one_pow]

theorem spanFor_subsingleton (G : Type) [Group G] [Subsingleton G] : SpanFor G := by
  intro q c hc hd
  obtain ⟨v, hv⟩ : ∃ v, ∀ y, c y = v := ⟨c (fun _ => 1), fun y => congrArg c (Subsingleton.elim _ _)⟩
  rcases Nat.even_or_odd q with hq | hq
  · have h3 : ¬ Even (q + 1 + 2) := by
      rw [Nat.not_even_iff_odd]
      rcases hq with ⟨r, rfl⟩
      exact ⟨r + 1, by ring⟩
    have hd1 := congrFun hd (fun _ => 1)
    simp only [dc, hv, Pi.zero_apply] at hd1
    rw [← Finset.sum_mul, altsum, if_neg h3, one_mul] at hd1
    refine ⟨0, Fin.elim0, Fin.elim0, fun _ => 0, fun _ _ _ => rfl, ?_⟩
    funext y
    simp [dc, hv, hd1]
  · have h2 : ¬ Even (q + 2) := by
      rw [Nat.not_even_iff_odd]
      rcases hq with ⟨r, rfl⟩
      exact ⟨r + 1, by ring⟩
    refine ⟨0, Fin.elim0, Fin.elim0, fun _ => v, fun _ _ _ => rfl, ?_⟩
    funext y
    simp only [dc, hv, Finset.univ_eq_empty, Finset.sum_empty, Pi.add_apply, Pi.zero_apply, zero_add]
    rw [← Finset.sum_mul, altsum, if_neg h2, one_mul]

theorem spanFor_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (hB : SpanFor B) : SpanFor A := by
  intro q c hc hd
  obtain ⟨k, a, α, f, hf, hcf⟩ := hB q (fun z => c (fun j => e.symm (z j)))
    (fun g _ y => by
      simp only [map_mul]
      exact hc _ trivial _)
    (by
      funext z
      have := congrFun hd (fun j => e.symm (z j))
      simpa [dc] using this)
  refine ⟨k, a, fun i j => (α i j).comp (MulEquiv.toAdditive e).toAddMonoidHom, fun y => f (fun j => e (y j)),
    fun g _ y => ?_, ?_⟩
  · simp only [map_mul]
    exact hf _ trivial _
  · funext y
    have := congrFun hcf (fun j => e (y j))
    simp only [MulEquiv.symm_apply_apply] at this
    rw [this]
    simp [Finset.sum_apply, cupH, dc]

def zdata (N : ℕ) : WData (Multiplicative (Fin N → ℤ)) (Multiplicative (Fin (N + 1) → ℤ)) where
  ι := { toFun := fun g => Multiplicative.ofAdd (Fin.cons 0 (Multiplicative.toAdd g))
         map_one' := by
           apply Multiplicative.toAdd.injective; funext i
           refine Fin.cases ?_ (fun j => ?_) i <;> simp
         map_mul' := fun g h => by
           apply Multiplicative.toAdd.injective; funext i
           refine Fin.cases ?_ (fun j => ?_) i <;> simp }
  ρ := { toFun := fun p => Multiplicative.ofAdd (Fin.tail (Multiplicative.toAdd p))
         map_one' := rfl
         map_mul' := fun _ _ => rfl }
  ℓ := { toFun := fun x => (Multiplicative.toAdd (Additive.toMul x)) 0
         map_zero' := rfl
         map_add' := fun _ _ => rfl }
  t := Multiplicative.ofAdd (Fin.cons 1 0)
  ρι := fun _ => rfl
  ρt := rfl
  ℓι := fun g => by simp
  ℓt := by simp
  tc := fun z => mul_comm _ _
  dec := fun p => by
    apply Multiplicative.toAdd.injective; funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
      try rfl

theorem spanFor_pi : ∀ N : ℕ, SpanFor (Multiplicative (Fin N → ℤ))
  | 0 => spanFor_subsingleton _
  | N + 1 => (zdata N).step' (spanFor_pi N)

end PositivityTheory.KB.SplitAffineSpectral.PrismSpan

namespace PositivityTheory.KB.SplitAffineSpectral

open PrismSpan

theorem span : Span := by
  intro A _ _ _ q c hc hd
  let e : Multiplicative (Additive A) ≃* Multiplicative (Fin (Module.finrank ℤ (Additive A)) → ℤ) :=
    AddEquiv.toMultiplicative (Module.finBasis ℤ (Additive A)).equivFun.toAddEquiv
  exact spanFor_equiv e (spanFor_pi _) q c hc hd

end PositivityTheory.KB.SplitAffineSpectral

end

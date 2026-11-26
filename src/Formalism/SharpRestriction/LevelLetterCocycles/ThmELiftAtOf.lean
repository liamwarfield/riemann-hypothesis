module

public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
public import Formalism.SharpRestriction.LevelLetterCocycles.ExponentWindowSubsetShort
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.ThmEPrim
public import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Bridge

@[expose] public section

section -- merged from Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.ThmEFinal
section -- merged from Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.PolynomialEvaluationValuation
namespace Formalism.ExponentWindows.E

open PowerSeries

namespace PolynomialValuationLemmas

theorem factV {O : Type} [CommRing O] [IsLocalRing O] {ℓ : ℕ} {u x : Oˣ} (hp : ℓ.Prime)
    (h3 : 3 ≤ ℓ) (hl : ¬ IsUnit (ℓ : O)) (hu : (u : O) = 1 + (ℓ : O) * (x : O)) :
    FactVval u ℓ := by
  have key : ∀ r : ℕ, 1 ≤ r →
      ∃ ε : Oˣ, (u : O) ^ r - 1 = (ε : O) * (ℓ : O) ^ (1 + padicValNat ℓ r) := by
    intro r hr
    rw [hu]
    exact GoodPlacesAlt.one_add_pow_sub_one_valuation hp h3 hl x.isUnit r hr
  intro m hm
  obtain ⟨r, rfl | rfl⟩ := m.eq_nat_or_neg
  · have hr : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with rfl | h
      · exact absurd rfl hm
      · exact h
    obtain ⟨ε, hε⟩ := key r hr
    refine ⟨-ε, ?_⟩
    rw [zpow_natCast, Units.val_pow_eq_pow_val, padicValInt.of_nat, Units.val_neg]
    rw [← Nat.padicValNat_def]
    linear_combination -hε
  · have hr : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with rfl | h
      · exact absurd (by simp) hm
      · exact h
    obtain ⟨ε, hε⟩ := key r hr
    refine ⟨(u ^ r)⁻¹ * ε, ?_⟩
    have hv : padicValInt ℓ (-(r : ℤ)) = padicValNat ℓ r := by
      simp [padicValInt, Nat.padicValNat_def]
    have hinv : (((u ^ r)⁻¹ : Oˣ) : O) * (u : O) ^ r = 1 := by
      rw [← Units.val_pow_eq_pow_val, Units.inv_mul]
    rw [zpow_neg, zpow_natCast, hv, Units.val_mul]
    linear_combination (((u ^ r)⁻¹ : Oˣ) : O) * hε - hinv

theorem val_mul_pow (ℓ E : ℕ) [Fact ℓ.Prime] {i : ℤ} (hi : i ≠ 0) :
    padicValInt ℓ (i * ((ℓ ^ E : ℕ) : ℤ)) = E + padicValInt ℓ i := by
  have h2 : ((ℓ ^ E : ℕ) : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero
  rw [padicValInt.mul hi h2, padicValInt.of_nat, padicValNat.prime_pow, add_comm]

theorem ppevalVal {O : Type} [CommRing O] (u : Oˣ) (ℓ E : ℕ) (JS : Finset ℤ) (hp : ℓ.Prime)
    (hV : FactVval u ℓ) :
    ∃ ε : Oˣ, (G.PPoly u ℓ E JS).eval 1 = (ε : O) * (ℓ : O) ^ kapExp ℓ E JS := by
  haveI := Fact.mk hp
  have hf : ∀ i ∈ JS.erase 0, ∃ ε : Oˣ, (1 : O) - ((u ^ (i * ((ℓ ^ E : ℕ) : ℤ)) : Oˣ) : O) =
      (ε : O) * (ℓ : O) ^ (1 + E + padicValInt ℓ i) := by
    intro i hi
    have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
    have hm : i * ((ℓ ^ E : ℕ) : ℤ) ≠ 0 := mul_ne_zero hi0 (by exact_mod_cast pow_ne_zero _ hp.ne_zero)
    obtain ⟨ε, hε⟩ := hV _ hm
    refine ⟨ε, ?_⟩
    rw [hε, val_mul_pow ℓ E hi0, add_assoc]
  choose! ε hε using hf
  refine ⟨∏ i ∈ JS.erase 0, ε i, ?_⟩
  unfold kapExp
  rw [G.PPoly, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, one_pow,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [Finset.prod_congr rfl hε, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Units.coe_prod]
  push_cast
  rw [pow_add]
  ring

theorem ppval_of_le {O : Type} [CommRing O] (u : Oˣ) (ℓ E kap : ℕ) (JS JS' : Finset ℤ)
    (hp : ℓ.Prime) (hV : FactVval u ℓ) (hk : kapExp ℓ E JS + kapExp ℓ E JS' ≤ 2 * kap) :
    PPval ℓ kap (G.PPoly u ℓ E JS) (G.PPoly u ℓ E JS') := by
  obtain ⟨ε, h1⟩ := ppevalVal u ℓ E JS hp hV
  obtain ⟨ε', h2⟩ := ppevalVal u ℓ E JS' hp hV
  exact ⟨kapExp ℓ E JS + kapExp ℓ E JS', ε * ε', hk, by rw [h1, h2, Units.val_mul, pow_add]; ring⟩

section free
variable {O : Type} [CommRing O]

variable {B : Base O} {n : ℕ} {V₀ : Type} [AddCommGroup V₀] [Module (PowerSeries O) V₀]

end free

end PolynomialValuationLemmas

open PolynomialValuationLemmas

theorem factorial_valuation_holds : FactVvalOf := by
  intro O _ _ ℓ u x hp h3 hl hu
  exact factV hp h3 hl hu

theorem factorial_bound_holds : FactVOf := by
  intro O LL Ks Δ _ _ _ _ _ Lev u ℓ hu hl hV m hm h1
  obtain ⟨ε, hε⟩ := hV m hm
  have hU : Lev.u = Units.map (algebraMap O LL : O →* LL) u := Units.ext hu
  have h2 : algebraMap O LL ((u ^ m : Oˣ) : O) = 1 := by
    have : ((Lev.u ^ m : LLˣ) : LL) = algebraMap O LL ((u ^ m : Oˣ) : O) := by
      rw [hU, ← map_zpow]
      rfl
    rw [← this, h1, Units.val_one]
  have h3 := congrArg (algebraMap O LL) hε
  rw [RingHom.map_sub, map_one, h2, sub_self, map_mul, map_pow, map_natCast] at h3
  exact mul_ne_zero ((ε.isUnit.map (algebraMap O LL)).ne_zero) (pow_ne_zero _ hl) h3.symm

theorem polynomial_valuation_holds : PPvalOf := by
  intro O _ u ℓ E kap JS JS' hp hV h
  exact ppval_of_le u ℓ E kap JS JS' hp hV (by unfold kapExp; omega)

end Formalism.ExponentWindows.E
end

noncomputable section

namespace Formalism.ExponentWindows.E.JumpSetWindowBounds

open PowerSeries

theorem HK_eq (g G₀ Sz η : ℕ) (k : Kind) (b : ℕ) :
    Formalism.ExponentWindows.G.HK g G₀ Sz η k b = g + hJ G₀ Sz η k b := by
  cases k <;> rfl

theorem primWord {ℓ ell a₀ : ℕ} {b : ℕ → ℕ} {kind : ℕ → Kind} (h : TextWord ℓ ell a₀ b kind) :
    PrimWord ℓ ell a₀ b kind := by
  obtain ⟨⟨t₀, t₁, ht⟩, hw⟩ := h
  by_cases hd : ∀ s < ell, kind s ≠ Kind.down
  · exact Or.inl hd
  simp only [not_forall, not_not] at hd
  obtain ⟨sd, hsd, hkd⟩ := hd
  have hso : ∃ so, ∀ s < ell, s ≠ sd → s ≠ so → kind s = Kind.thin := by
    by_cases h0 : sd = t₀
    · exact ⟨t₁, fun s hs h1 h2 => ht s hs (h0 ▸ h1) h2⟩
    · by_cases h1 : sd = t₁
      · exact ⟨t₀, fun s hs h2 h3 => ht s hs h3 (h1 ▸ h2)⟩
      · exact absurd (ht sd hsd h0 h1) (by rw [hkd]; decide)
  obtain ⟨so, hso⟩ := hso
  by_cases hthin : so < ell ∧ so ≠ sd ∧ kind so ≠ Kind.thin
  · obtain ⟨h1, h2, h3⟩ := hthin
    rcases lt_or_gt_of_ne h2 with hlt | hgt
    · cases hk : kind so with
      | thin => exact absurd hk h3
      | up =>
        exact Or.inr (Or.inr (Or.inl ⟨so, sd, hlt, hsd, hkd, hk, fun s hs a b => hso s hs b a,
          (hw so sd hlt hsd).1 hkd hk⟩))
      | down =>
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨so, sd, hlt, hsd, hkd, hk,
          fun s hs a b => hso s hs b a⟩)))
    · cases hk : kind so with
      | thin => exact absurd hk h3
      | up =>
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨sd, so, hgt, h1, hk, hkd, hso,
          ((hw sd so hgt h1).2 hk hkd).1, ((hw sd so hgt h1).2 hk hkd).2⟩)))
      | down =>
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨sd, so, hgt, h1, hk, hkd, hso⟩)))
  · refine Or.inr (Or.inl ⟨sd, hsd, hkd, fun s hs hne => ?_⟩)
    by_cases hs' : s = so
    · subst hs'
      by_contra hk
      exact hthin ⟨hs, hne, hk⟩
    · exact hso s hs hne hs'

theorem thick_lt {n : ℕ} {Cu : Cuts n} {kd : ZMod n → Kind} {j : ℕ}
    (hthin : ∀ c ∈ Cu.cuts, ∀ k : ℕ, 1 ≤ k → k ≤ j → kd (c + (k : ZMod n)) = Kind.thin)
    {c : ZMod n} (hc : c ∈ Cu.cuts) {s : ℕ} (hs : s < Cu.ell c) (hk : kindAt kd c s ≠ Kind.thin) :
    s < Cu.ell c - j := by
  by_contra hlt
  apply hk
  have h1 := hthin _ (Cu.prev_mem c hc) (Cu.ell c - s) (by omega) (by omega)
  have h2 : c - (Cu.ell c : ZMod n) + ((Cu.ell c - s : ℕ) : ZMod n) = c - (s : ZMod n) := by
    rw [Nat.cast_sub hs.le]
    ring
  rw [h2] at h1
  exact h1

theorem mem_second_jump_set {ell g : ℕ} {kind : ℕ → Kind} {b : ℕ → ℕ} {s : ℕ} (hs : s < ell) {i : ℤ}
    (hi : G.Win2 (kind s) g (b s) i) : i ∈ jumpWindows ell g kind b := by
  refine Finset.mem_biUnion.2 ⟨s, Finset.mem_range.2 hs, ?_⟩
  revert hi
  cases kind s <;> simp only [G.Win2, win2, Finset.mem_union, Finset.mem_Icc] <;> exact id

theorem mem_fourth_jump_set {LL D : Type} [Field LL] [AddCommGroup D] [Module LL D] {ell g G₀ Sz η : ℕ}
    {kind : ℕ → Kind} {b : ℕ → ℕ} {s : ℕ} (hs : s < ell) {Fil : ℤ → Submodule LL D}
    (hJ : G.Jumps (kind s) G₀ Sz η (b s) Fil) {v z : ℤ} (hv : Fil v ≠ Fil (v + 1)) (h1 : 1 ≤ z)
    (hz : z ≤ g) : -v - z ∈ wideWindows ell g G₀ Sz η kind b := by
  refine Finset.mem_biUnion.2 ⟨s, Finset.mem_range.2 hs, ?_⟩
  revert hJ
  cases kind s <;> simp only [G.Jumps, win4, Finset.mem_union, Finset.mem_Icc] <;> intro hJ <;>
    have := hJ v hv <;> omega

theorem ppval {O : Type} [CommRing O] (u : Oˣ) {ℓ E kap : ℕ} {JS JS' : Finset ℤ} (hp : ℓ.Prime)
    (hV : FactVval u ℓ) (h : kapExp ℓ E JS ≤ kap ∧ kapExp ℓ E JS' ≤ kap) :
    PPval ℓ kap (G.PPoly u ℓ E JS) (G.PPoly u ℓ E JS') := by
  refine polynomial_valuation_holds O u ℓ E kap JS JS' hp hV ?_
  obtain ⟨h1, h2⟩ := h
  unfold kapExp at h1 h2
  omega

section lev
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Base O} {n : ℕ}
  [NeZero n] {V : Type} [AddCommGroup V] [Module (PowerSeries O) V] {L : Lat B n V} {c : ZMod n}
  {ell : ℕ} {H : ℕ → ℕ} {r : ℕ} {S : LevelData L c ell (Formalism.ExponentWindows.abelian₂ B.p H ell) r}
  {LL : Type} [Field LL] [Algebra O LL] {Ks : ℕ → Type} [∀ s, CommRing (Ks s)]
  [∀ s, Algebra LL (Ks s)] {Δ D : Type} [AddCommGroup D] [Module LL D]
  {R : G.LevelModel S LL Ks Δ D} {ϖ : O} {u : Oˣ} {j M g G₀ Sz η : ℕ} {kind : ℕ → Kind}
  {b : ℕ → ℕ} {e : Fin r → V} {lam : Fin r → D} {U : ℕ → Submodule O (Fin r → O)}

theorem partModel (hF : FinalLevels L c ell H S R ϖ u j M g G₀ Sz η kind b e lam U) {hh : ℕ}
    (hX : L.Inv X) (hP : ∀ s, L.Inv (B.p s)) (h9 : L.P9)
    (h5 : ∀ s < ell, L.FrobeniusCobounded (c - (s : ZMod n)) (hJ G₀ Sz η (kind s) (b s)))
    (hH : ∀ s < ell, H s = Formalism.ExponentWindows.G.HK g G₀ Sz η (kind s) (b s))
    (hne : algebraMap O LL (B.ℓ : O) ≠ 0)
    (hnum : G.HeightNumerics ell j B.ℓ M g G₀ Sz η hh kind b) :
    G.PrimPartModel L c ell (fun s => hJ G₀ Sz η (kind s) (b s)) H S R ϖ j M g G₀ Sz hh e lam :=
  { invX := hX
    invP := fun s _ => hP s
    p9 := h9
    p5h := h5
    hh_le := fun s hs => by rw [hH s hs, HK_eq]; omega
    span := hF.span
    mem := hF.mem
    pa1b := hF.pa1b
    locReg := hF.locReg
    k1b := hF.k1b
    unitsAt := hF.unitsAt
    compl := hF.compl
    flDef := hF.flDef
    locLIs := hF.locLIs
    lamInd := hF.lamInd
    ell_ne := hne
    num := by
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hnum
      refine ⟨a1, a2, a3, by rw [hF.η_eq]; exact a4, a5, fun s hs hk => ?_⟩
      rw [hF.kind_eq s hs] at hk
      rw [hF.b_eq s hs]
      exact a6 s hs hk
    H_eq := fun s hs => by rw [hF.kind_eq s hs, hF.b_eq s hs, hF.η_eq]; exact hH s hs
    filt := fun s hs => by
      rw [hF.kind_eq s hs, hF.b_eq s hs, hF.η_eq]
      exact ⟨hF.filt s hs, hF.jumps s hs⟩ }

theorem rd (hF : FinalLevels L c ell H S R ϖ u j M g G₀ Sz η kind b e lam U) (hG : G₀ ≤ g)
    (hS : Sz ≤ g) (hη : η ≤ g) (hb : ∀ s < ell, kind s ≠ Kind.thin → g < b s) : S.RD g :=
  G.reduction_degree_holds filtration_rounding O B n V L c ell _ r S LL Ks Δ D R G₀ Sz g hF.k1b hG hS
    (by rw [hF.η_eq]; exact hη) (fun s hs => by
      rw [hF.kind_eq s hs, hF.b_eq s hs, hF.η_eq]
      exact ⟨hF.filt s hs, hb s hs, hF.jumps s hs⟩)

theorem factV (hF : FinalLevels L c ell H S R ϖ u j M g G₀ Sz η kind b e lam U)
    (hne : algebraMap O LL (B.ℓ : O) ≠ 0) (hV : FactVval u B.ℓ) : ∀ s < ell, (R.lev s).FactV :=
  fun s hs => factorial_bound_holds O LL (Ks s) Δ (R.lev s) u B.ℓ (hF.hasU s hs)
    (by rwa [map_natCast] at hne) hV

theorem sat (hF : FinalLevels L c ell H S R ϖ u j M g G₀ Sz η kind b e lam U)
    (hϖ : algebraMap O LL ϖ ≠ 0) : ∀ s < ell, Saturated ϖ (U s) := by
  intro s hs v hv
  rw [hF.uIs s hs] at hv ⊢
  have h1 : ∑ k, algebraMap O LL ((ϖ • v) k) • lam k =
      algebraMap O LL ϖ • ∑ k, algebraMap O LL (v k) • lam k := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul]
  rw [h1] at hv
  exact (Submodule.smul_mem_iff _ hϖ).1 hv

theorem bridgeItems (hF : FinalLevels L c ell H S R ϖ u j M g G₀ Sz η kind b e lam U)
    (hfr : IsFractionRing O LL) : G.BridgeItems R ϖ η kind b lam U :=
  { frac := hfr
    kind_eq := hF.kind_eq
    b_eq := hF.b_eq
    η_eq := hF.η_eq
    k1b := hF.k1b
    unitsAt := hF.unitsAt
    compl := hF.compl
    locLIs := hF.locLIs
    lamInd := hF.lamInd
    lamSpan := hF.lamSpan
    uIs := hF.uIs }

theorem bridge (hϖ : Irreducible ϖ)
    (hF : FinalLevels L c ell H S R ϖ u j M g G₀ Sz η kind b e lam U)
    (hfr : IsFractionRing O LL) : S.Bridge ϖ H b kind U :=
  G.lattice_transfer_holds O ϖ hϖ B n V L c ell H r S LL Ks Δ D R η kind b lam U (bridgeItems hF hfr)

end lev

section llift
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V₁ V₂ : Type} [AddCommGroup V₁]
  [Module (PowerSeries O) V₁] [AddCommGroup V₂] [Module (PowerSeries O) V₂]
  {L₁ : Lat B n V₁} {L₂ : Lat B n V₂}

theorem lLift_of {h : LatHom L₁ L₂} {c' : ZMod n} {r₁ r₂ : ℕ} {e₁ : Fin r₁ → V₁} {e₂ : Fin r₂ → V₂}
    {prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)} {rr : ℕ}
    (hs₁ : Submodule.span (PowerSeries O) (Set.range e₁) = L₁.N c')
    (hs₂ : Submodule.span (PowerSeries O) (Set.range e₂) = L₂.N c')
    (hi : LinearIndependent (PowerSeries O) e₂)
    (hp : ∀ k, h.f (e₁ k) - ∑ l, C (LinearMap.toMatrix' prL l k) • e₂ l ∈ sm (X : PowerSeries O) (L₂.N c'))
    (hW : h.WPrime c' rr) : LLift B.ℓ rr prL := by
  intro v
  have he₂ : ∀ l, e₂ l ∈ L₂.N c' := fun l => hs₂ ▸ Submodule.subset_span ⟨l, rfl⟩
  have hsum : ∀ d : Fin r₂ → PowerSeries O, ∑ l, d l • e₂ l ∈ L₂.N c' := fun d =>
    Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (he₂ l)
  obtain ⟨y, hy, hyx⟩ := hW (∑ l, C (v l) • e₂ l) (hsum _)
  rw [← hs₁] at hy
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (PowerSeries O)).1 hy
  refine ⟨fun k => constantCoeff (a k), ?_⟩
  set v₁ : Fin r₁ → O := fun k => constantCoeff (a k) with hv₁

  have h1 : ∀ k, a k • h.f (e₁ k) - C (v₁ k) • ∑ l, C (LinearMap.toMatrix' prL l k) • e₂ l ∈
      sm (X : PowerSeries O) (L₂.N c') := by
    intro k
    obtain ⟨a', ha'⟩ : ∃ a' : PowerSeries O, a k - C (v₁ k) = X * a' := by
      have : (X : PowerSeries O) ∣ a k - C (v₁ k) := by
        rw [X_dvd_iff]
        simp [hv₁]
      exact this
    have e : a k • h.f (e₁ k) - C (v₁ k) • ∑ l, C (LinearMap.toMatrix' prL l k) • e₂ l =
        a k • (h.f (e₁ k) - ∑ l, C (LinearMap.toMatrix' prL l k) • e₂ l) +
          (X : PowerSeries O) • (a' • ∑ l, C (LinearMap.toMatrix' prL l k) • e₂ l) := by
      rw [← mul_smul, ← ha', smul_sub, sub_smul]
      abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hp k))
      (IdempotentNormalFormsRhoFacts.smul_mem_sm _ (Submodule.smul_mem _ _ (hsum _)))
  have h2 : ∑ k, C (v₁ k) • ∑ l, C (LinearMap.toMatrix' prL l k) • e₂ l =
      ∑ l, C (prL v₁ l) • e₂ l := by
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← LinearMap.toMatrix'_mulVec prL v₁, Matrix.mulVec, dotProduct, map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_smul, ← map_mul, mul_comm]
  have h3 : h.f (∑ k, a k • e₁ k) - ∑ l, C (prL v₁ l) • e₂ l ∈ sm (X : PowerSeries O) (L₂.N c') := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h2, map_sum, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smul]
    exact h1 k
  rw [hyx] at h3
  obtain ⟨w, hw, hw'⟩ := IdempotentNormalFormsRhoFacts.mem_sm.1 h3
  rw [← hs₂] at hw
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (PowerSeries O)).1 hw
  have h4 : ∑ l, (X * b l - (C ((B.ℓ : O) ^ rr * v l) - C (prL v₁ l))) • e₂ l = 0 := by
    have : ∑ l, (X * b l - (C ((B.ℓ : O) ^ rr * v l) - C (prL v₁ l))) • e₂ l =
        (X : PowerSeries O) • ∑ l, b l • e₂ l - (B.lc ^ rr • ∑ l, C (v l) • e₂ l - ∑ l, C (prL v₁ l) • e₂ l) := by
      simp only [Finset.smul_sum, ← Finset.sum_sub_distrib, sub_smul, mul_smul, map_mul, map_pow,
        Base.lc]
    rw [this, hw', sub_self]
  have h5 := Fintype.linearIndependent_iff.1 hi _ h4
  funext l
  have h6 := congrArg constantCoeff (h5 l)
  simp only [map_sub, map_mul, constantCoeff_X, zero_mul, constantCoeff_C, map_zero, zero_sub,
    neg_sub] at h6
  rw [Pi.smul_apply, smul_eq_mul]
  exact sub_eq_zero.1 h6

end llift

section arc
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Base O} {n : ℕ}
  [NeZero n] {V₁ V₂ : Type} [AddCommGroup V₁] [Module (PowerSeries O) V₁] [AddCommGroup V₂]
  [Module (PowerSeries O) V₂] {L₁ : Lat B n V₁} {L₂ : Lat B n V₂}
  {LL : Type} [Field LL] [Algebra O LL] {Ks : ℕ → Type} [∀ s, CommRing (Ks s)]
  [∀ s, Algebra LL (Ks s)] {Δ : Type}

theorem inv_Th {V : Type} [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V)
    (hP : ∀ s, L.Inv (B.p s)) (ell g : ℕ) : L.Inv (B.Th ell g) :=
  XDivisibilityOfActions.bij_Lam L (fun _ => g) ell fun s _ => hP s

theorem primArc {ϖ : O} (hϖ : Irreducible ϖ) {eO : ℕ} {u x : Oˣ} (hB : FinalBase B ϖ eO u x LL)
    {Cu : Cuts n} {kd : ZMod n → Kind} {bb : ZMod n → ℕ} {j g G₀ Sz η hh sig rr kap ellmax : ℕ}
    (hN : FinalNum B.ℓ Cu kd bb j g G₀ Sz η hh sig rr kap ellmax)
    (hL₁ : FinalLat L₁ Cu kd bb j G₀ Sz η hh) (hL₂ : FinalLat L₂ Cu kd bb j G₀ Sz η hh)
    {h : LatHom L₁ L₂} (hW : WPrimeCuts h Cu rr) {c : ZMod n} (hc : c ∈ Cu.cuts)
    (hA : FinalArc h c (Cu.ell c) (HArc g G₀ Sz η kd bb c) LL Ks Δ ϖ u j (parM B.ℓ hh g) g G₀ Sz η
      (kindAt kd c) (sizeAt bb c)) :
    PrimArc h c (Cu.ell c) (HArc g G₀ Sz η kd bb c) g sig rr (parA sig rr g ellmax) kap ϖ := by
  obtain ⟨A, hP⟩ := hA
  have hpB := hB.prim
  have hℓ2 : 2 ≤ B.ℓ := by have := hpB.three_le; omega
  have hdvd : ϖ ∣ (B.ℓ : O) := Prim.dvd_ell hpB.one_le_e hpB.assoc
  have hnu : ¬ IsUnit (B.ℓ : O) := Prim.ell_nonunit hϖ hpB.one_le_e hpB.assoc
  have hV : FactVval u B.ℓ := factorial_valuation_holds O B.ℓ u x hpB.prime hpB.three_le hnu hB.u_eq
  have hinj : Function.Injective (algebraMap O LL) :=
    haveI := hB.frac
    IsFractionRing.injective O LL
  have hne : algebraMap O LL (B.ℓ : O) ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 (hpB.assoc.ne_zero_iff.2 (pow_ne_zero _ hϖ.ne_zero))
  have hϖ0 : algebraMap O LL ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have hgb : ∀ s < Cu.ell c, kindAt kd c s ≠ Kind.thin → g < sizeAt bb c s :=
    fun s _ hk => hN.g_lt_b _ hk
  have hbh : ∀ s < Cu.ell c, kindAt kd c s ≠ Kind.thin → sizeAt bb c s + Sz ≤ hh :=
    fun s _ hk => hN.b_le_h _ hk
  have hnum : G.HeightNumerics (Cu.ell c) j B.ℓ (parM B.ℓ hh g) g G₀ Sz η hh (kindAt kd c) (sizeAt bb c) :=
    ⟨Prim.lt_parM B.ℓ hh g hℓ2, hN.G_le_g, hN.S_le_g, hN.η_le_g, hN.g_le_h,
      fun s hs hk => ⟨hbh s hs hk, thick_lt hN.thin_after hc hs hk⟩⟩
  have hE : Cu.ell c ≤ Cu.ell c - 1 + 1 := by omega
  obtain ⟨p4c₁, p4a₁, p4b₁, pt₁, p3₁, -⟩ := G.partners_model_holds O ϖ B n V₁ L₁ c (Cu.ell c) _ _
    A.r₁ A.S₁ LL Ks Δ A.D₁ A.R₁ j (parM B.ℓ hh g) g G₀ Sz hh sig A.e₁ A.lam₁ hϖ hdvd hpB.prime
    hpB.three_le hpB.e3 hpB.e4 hN.one_le_j (hN.j_le_ell c hc) hN.sigOK
    (partModel hP.lev₁ hL₁.invX hL₁.invP hL₁.prim.p9 (fun s _ => hL₁.p5h _) (fun _ _ => rfl)
      hne hnum)
  obtain ⟨p4c₂, p4a₂, p4b₂, pt₂, p3₂, flr₂⟩ := G.partners_model_holds O ϖ B n V₂ L₂ c (Cu.ell c) _ _
    A.r₂ A.S₂ LL Ks Δ A.D₂ A.R₂ j (parM B.ℓ hh g) g G₀ Sz hh sig A.e₂ A.lam₂ hϖ hdvd hpB.prime
    hpB.three_le hpB.e3 hpB.e4 hN.one_le_j (hN.j_le_ell c hc) hN.sigOK
    (partModel hP.lev₂ hL₂.invX hL₂.invP hL₂.prim.p9 (fun s _ => hL₂.p5h _) (fun _ _ => rfl)
      hne hnum)
  refine ⟨A.r₁, A.r₂, A.S₁, A.S₂, A.m, sizeAt bb c, kindAt kd c, A.U₁, A.U₂,
    G.PPoly u B.ℓ (Cu.ell c - 1) (jumpWindows (Cu.ell c) g (kindAt kd c) (sizeAt bb c)),
    G.PPoly u B.ℓ (Cu.ell c - 1) (wideWindows (Cu.ell c) g G₀ Sz η (kindAt kd c) (sizeAt bb c)), ?_⟩
  exact
    { p4c₁ := p4c₁
      p4c₂ := p4c₂
      equiv₁ := hP.lev₁.equiv
      equiv₂ := hP.lev₂.equiv
      k2iii := G.graded_third_clause_holds O B n V₂ L₂ c (Cu.ell c) _ A.r₂ A.S₂ LL Ks Δ A.D₂ A.R₂ B.ℓ
        (by omega) (fun s hs => ⟨hP.lev₂.k1c s hs, factV hP.lev₂ hne hV s hs⟩)
      rd₁ := rd hP.lev₁ hN.G_le_g hN.S_le_g hN.η_le_g hgb
      rd₂ := rd hP.lev₂ hN.G_le_g hN.S_le_g hN.η_le_g hgb
      k3a2 := G.constant_term_second_form O B n V₂ L₂ c (Cu.ell c) _ A.r₂ A.S₂ LL Ks Δ A.D₂ A.R₂ u B.ℓ
        (Cu.ell c - 1) g _ hP.lev₂.k1b hP.lev₂.hasU hE hP.lev₂.k1c (fun s hs => by
          rw [hP.lev₂.kind_eq s hs, hP.lev₂.b_eq s hs]
          exact ⟨hgb s hs, fun i hi => mem_second_jump_set hs hi⟩)
      k3a4 := G.constant_term_fourth_form O B n V₁ L₁ c (Cu.ell c) _ A.r₁ A.S₁ LL Ks Δ A.D₁ A.R₁ u B.ℓ
        (Cu.ell c - 1) g _ hP.lev₁.k1b hP.lev₁.hasU hE
        (fun s hs => ⟨hP.lev₁.k1c s hs, hP.lev₁.k1d s hs⟩) (fun s hs => (hP.lev₁.filt s hs).1)
        (fun s hs v z hv h1 hz => mem_fourth_jump_set hs (hP.lev₁.jumps s hs) hv h1 hz)
      dcFix := G.descent_fixed_points_holds O B n V₁ L₁ c (Cu.ell c) _ A.r₁ A.S₁ LL Ks Δ A.D₁ A.R₁
      partner₁ := pt₁
      partner₂ := pt₂
      p3₁ := p3₁
      p3₂ := p3₂
      flReg := flr₂
      p4a₁ := p4a₁
      p4a₂ := p4a₂
      p4b₁ := p4b₁
      p4b₂ := p4b₂
      bridge₁ := bridge hϖ hP.lev₁ hB.frac
      bridge₂ := bridge hϖ hP.lev₂ hB.frac
      mapFl := hP.mapFl
      p4d := partner_fourth_fourth_form O B n V₁ V₂ L₁ L₂ h c (Cu.ell c) g rr (inv_Th L₁ hL₁.invP _ _)
        (inv_Th L₂ hL₂.invP _ _) (hW c hc)
      lLift := lLift_of hP.lev₁.span hP.lev₂.span hP.lev₂.ind hP.prLIs (hW _ (Cu.prev_mem c hc))
      cMap := hP.cMap
      ppval := ppval u hpB.prime hV (hN.kapOK c hc)
      sat₁ := sat hP.lev₁ hϖ0
      sat₂ := sat hP.lev₂ hϖ0
      b_le_H := fun s _ hk => by
        change sizeAt bb c s ≤ Formalism.ExponentWindows.G.HK g G₀ Sz η (kindAt kd c s) (sizeAt bb c s)
        rw [HK_eq, hk]
        simp only [hJ]
        omega
      g_lt_b := hgb
      word := primWord (hN.word c hc) }

end arc

end Formalism.ExponentWindows.E.JumpSetWindowBounds

namespace Formalism.ExponentWindows.E

theorem theorem_E_final_form : ThmEFinal := by
  intro O _ _ _ ϖ hϖ B eO n _ Cu kd bb j g G₀ Sz η hh sig rr kap ellmax u x LL _ _ Ks _ _ Δ
    V₁ V₂ V₀ _ _ _ _ _ _ L₁ L₂ L₀ e₀ h Zf₁ Zf₂ hB hN hL₁ hL₂ hU hK hW hA
  exact theorem_E_primitive_form O ϖ hϖ B eO n Cu (HArc g G₀ Sz η kd bb) j g G₀ hh sig rr kap ellmax
    V₁ V₂ V₀ L₁ L₂ L₀ e₀ h Zf₁ Zf₂ hB.prim
    ⟨hN.G_le_g, hN.g_le_h, hN.one_le_j, hN.j_le_ell, hN.ell_le, hN.sigOK⟩ hL₁.prim hL₂.prim hU hK
    (fun c hc => JumpSetWindowBounds.primArc hϖ hB hN hL₁ hL₂ hW hc (hA c hc))

end Formalism.ExponentWindows.E
end
end

noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] (W : LocWach PD LL O v n)

structure BrData (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) where
  I : BaseId W
  C₁ : Coord W I T₁
  C₂ : Coord W I T₂
  C₀ : Coord W I W.one
  h : CoordHom C₁ C₂ F
  e₀ : C₀.V
  ϖ : O
  eO : ℕ
  u : Oˣ
  x : Oˣ
  Ks : ℕ → Type
  [ksRing : ∀ s, CommRing (Ks s)]
  [ksAlg : ∀ s, Algebra LL (Ks s)]
  Δ : Type

attribute [instance] BrData.ksRing BrData.ksAlg

variable {W}

structure BrProps {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} (D : BrData W T₁ T₂ F)
    (Cu : Formalism.ExponentWindows.E.Cuts n) (kd : ZMod n → Formalism.ExponentWindows.Kind) (bb : ZMod n → ℕ)
    (j g G₀ Sz η hh sig rr : ℕ) : Prop where

  irr : Irreducible D.ϖ

  prim : Formalism.ExponentWindows.E.PrimBase D.I.Bs D.ϖ D.eO

  u_eq : (D.u : O) = 1 + (D.I.Bs.ℓ : O) * (D.x : O)

  lat₁ : Formalism.ExponentWindows.E.FinalLat (latOf D.C₁) Cu kd bb j G₀ Sz η hh

  lat₂ : Formalism.ExponentWindows.E.FinalLat (latOf D.C₂) Cu kd bb j G₀ Sz η hh

  unit : Formalism.ExponentWindows.E.PrimUnit (latOf D.C₀) D.e₀

  rho : ∀ c ∈ Cu.cuts, ∀ w,
    (latOf D.C₁).Wc Cu (Formalism.ExponentWindows.E.LamOf D.I.Bs Cu (Formalism.ExponentWindows.E.HArc g G₀ Sz η kd bb)) c w →
    ∀ y z, (latOf D.C₁).IsRho c j (Formalism.ExponentWindows.E.parM D.I.Bs.ℓ hh g) g sig w y z → (y, z) ∈ Zf D.C₁

  ext : ∀ κ ∈ Zf D.C₂, ∃ Y : Formalism.ExponentWindows.E.Ext (latOf D.C₂) (latOf D.C₀), Y.Rep D.e₀ κ.1 κ.2 ∧
    Formalism.ExponentWindows.E.PrimExt Y D.e₀ Cu j G₀ rr (Formalism.ExponentWindows.E.HArc g G₀ Sz η kd bb)

  wprime : Formalism.ExponentWindows.E.WPrimeCuts (latHomOf D.h) Cu rr

  arcs : ∀ c ∈ Cu.cuts, Formalism.ExponentWindows.E.FinalArc (latHomOf D.h) c (Cu.ell c)
    (Formalism.ExponentWindows.E.HArc g G₀ Sz η kd bb c) LL D.Ks D.Δ D.ϖ D.u j (Formalism.ExponentWindows.E.parM D.I.Bs.ℓ hh g) g G₀ Sz η
    (Formalism.ExponentWindows.E.kindAt kd c) (Formalism.ExponentWindows.E.sizeAt bb c)

variable (W) [Fintype (K →ₐ[Qp] LL)]

def Realised : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L),
    GoodCoeffs (K := K) (Qp := Qp) (LL := LL) (O := O) (V := T₁.V) →
    CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∀ (j Gp S η h : ℕ) (ty : ZMod n → LT) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ)
      (Mb₁ hb₁ Mb₂ hb₂ : ZMod n → ℕ) (hC : CutsOK n j ty cuts arcLen),
      KindJumps PD T₁ W.emb Gp S η ty →
      (∀ τ : K →ₐ[Qp] LL, JumpsInV PD T₁.ρ τ (Set.Icc (-(h : ℤ)) h)) →
      gPar Gp S η ≤ h → SizesOK (gPar Gp S η) S h ty → ThickLe2 ty cuts arcLen →
      (∀ i, JumpsAtE PD T₁ W.emb i (Set.Icc (-(Mb₁ i : ℤ)) (hb₁ i))) →
      (∀ i, JumpsAtE PD T₂ W.emb i (Set.Icc (-(Mb₂ i : ℤ)) (hb₂ i))) →
      WordOK PD.p (initialExponentBound PD.p n j (gPar Gp S η) h (Mb₁ + hb₁) (Mb₂ + hb₂) cuts arcLen) ty cuts
        arcLen →
      ∃ D : BrData W T₁ T₂ F, BrProps D (cutsOf hC) (kdOf ty) (bbOf ty) j (gPar Gp S η) Gp S η h
        (sigPar PD.p (gPar Gp S η) h j) (rrPar PD.p n (Mb₁ + hb₁) (Mb₂ + hb₂) cuts)

variable {W}

end Formalism.MainNotions.WachCoordinates.Br

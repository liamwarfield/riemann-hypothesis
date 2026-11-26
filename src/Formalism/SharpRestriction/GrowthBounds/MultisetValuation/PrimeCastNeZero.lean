module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TheoremOfAlternateForm
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PositivityConditionHolds
public import Formalism.SharpRestriction.GrowthBounds.LatticeSystems

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PrimeCastNeZero
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem prime_cast_ne_zero : ((p : ℕ) : K0 p) ≠ 0 := by
  have h1 : ((p : ℕ) : WW p) ≠ 0 := WittVector.p_nonzero p (kb p)
  have h2 : algebraMap (WW p) (K0 p) ((p : ℕ) : WW p) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (WW p) (K0 p))).2 h1
  simpa using h2

theorem pKf_ne (Y : Pend X) : ((p : ℕ) : X.G.Kf) ≠ 0 := by
  intro h
  have h1 : algebraMap X.G.Kf Y.Kc ((p : ℕ) : X.G.Kf) = 0 := by rw [h, map_zero]
  have h2 : algebraMap (K0 p) Y.Kc ((p : ℕ) : K0 p) = 0 := by
    rw [map_natCast] at h1 ⊢
    exact h1
  exact prime_cast_ne_zero ((map_eq_zero _).1 h2)

theorem algebraMap_inj (Y : Pend X) (he : 0 < X.eO) : Function.Injective (algebraMap X.G.O X.G.Kf) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha0 X.unif
  obtain ⟨u, hu⟩ := hn

  have h1 : algebraMap X.G.O X.G.Kf (X.vp ^ n) = 0 := by rw [← hu, map_mul, ha, zero_mul]
  have h2 : algebraMap X.G.O X.G.Kf X.vp = 0 := by
    rw [map_pow] at h1
    by_contra h
    exact pow_ne_zero n h h1
  obtain ⟨u', hu'⟩ := X.eO_spec
  have h3 : algebraMap X.G.O X.G.Kf ((p : X.G.O) * u') = 0 := by
    rw [hu', map_pow, h2, zero_pow (by omega)]
  rw [map_mul, map_natCast] at h3
  rcases mul_eq_zero.1 h3 with h | h
  · exact pKf_ne Y h
  · have : algebraMap X.G.O X.G.Kf ((u' : X.G.O) * ((u'⁻¹ : X.G.Oˣ) : X.G.O)) = 0 := by rw [map_mul, h, zero_mul]
    simp at this

theorem isFractionRing_of_pos_eO (Y : Pend X) (he : 0 < X.eO) : IsFractionRing X.G.O X.G.Kf := by
  have : FaithfulSMul X.G.O X.G.Kf := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap_inj Y he)
  apply IsFractionRing.of_field
  intro z
  rcases Y.Oc_val (algebraMap X.G.Kf Y.Kc z) with h | h
  · obtain ⟨a, ha⟩ := (mem_intK X).1 ((Y.Oc_K z).1 h)
    exact ⟨a, 1, by simp [ha]⟩
  · rw [← map_inv₀] at h
    obtain ⟨a, ha⟩ := (mem_intK X).1 ((Y.Oc_K z⁻¹).1 h)
    exact ⟨1, a, by simp [ha]⟩

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RelativePresentationOfD7
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

variable {p n' k1 t m c r : ℕ} {TT : Finset (Fin n')} {a b : Fin n' → ℤ} {lam0 : Fin n' → Fin (k1 + 1) → ℤ}
  {w : ℕ → Fin n' → ℤ}

theorem w_one_le (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') :
    ∀ j, 1 ≤ j → j ≤ m → w 1 s ≤ w j s := by
  intro j hj hm
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with hj0 | hj'
    · subst hj0
      exact le_rfl
    · exact (ih hj' (by omega)).trans (h.w_mono s j hj' (by omega))

theorem lamI_ge_last (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ k1 + 1) :
    lam0 s (Fin.last k1) ≤ lamI lam0 s i := by
  unfold lamI
  rw [dite_eq_left ⟨h1, h2⟩]
  exact h.dom s (Fin.le_last _)

theorem lamI_add_w_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') (i j : ℕ) (h1 : 1 ≤ i)
    (h2 : i ≤ k1 + 1) (hj : 1 ≤ j) (hm : j ≤ m) : 0 ≤ lamI lam0 s i + w j s := by
  have h3 := lamI_ge_last h s i h1 h2
  have h4 := w_one_le h s j hj hm
  have h5 := (h.w_low s).2
  linarith

theorem al_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') : 0 ≤ al TT lam0 s := by
  have hk : 2 ≤ k1 + 1 := by have := h.two_r; have := h.r_pos; omega
  unfold al
  split_ifs
  · unfold lamI
    rw [dite_eq_left (show 1 ≤ 1 ∧ 1 ≤ k1 + 1 by omega), dite_eq_left (show 1 ≤ 2 ∧ 2 ≤ k1 + 1 by omega)]
    exact sub_nonneg.mpr (h.dom s (Fin.mk_le_mk.mpr (by omega)))
  · exact le_rfl

theorem cap_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') (j : ℕ) (hj : 1 ≤ j) (hm : j ≤ m) :
    0 ≤ cap t TT lam0 w j s := by
  have hk : 2 ≤ k1 + 1 := by have := h.two_r; have := h.r_pos; omega
  unfold cap nu
  split_ifs <;> first
    | omega
    | exact lamI_add_w_nonneg h s _ j (by omega) (by omega) hj hm

theorem gam_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) : 0 ≤ gam p := by
  unfold gam
  have h5 : (5 : ℝ) ≤ p := by exact_mod_cast h.five_le
  apply div_nonneg
  · positivity
  · nlinarith

theorem Pr_nonneg (h : Std p n' k1 t m c r TT a b lam0 w) (j : ℕ) (hj : 1 ≤ j) (hm : j ≤ m) :
    0 ≤ Pr t r lam0 w j := by
  unfold Pr
  have hk := h.two_r
  have hr := h.r_pos
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro s _
    have hcard : (Icc (k1 + 2 - r) (k1 + 1)).card = r := by
      rw [Nat.card_Icc]
      omega
    have key : ∀ a ∈ Icc (k1 + 2 - r) (k1 + 1), (0 : ℝ) ≤ (w j s : ℝ) + (lamI lam0 s a : ℝ) := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      have h0 := lamI_add_w_nonneg h s a j (by omega) ha.2 hj hm
      have h0' : (0 : ℤ) ≤ w j s + lamI lam0 s a := by linarith
      exact_mod_cast h0'
    have hsum := Finset.sum_nonneg key
    rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul] at hsum
    linarith
  · positivity

theorem gA_ge (p t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ) :
    -de p t TT lam0 w j ≤ gA p t TT lam0 w j := by
  unfold gA
  have key : ∀ X Y : ℝ, 0 ≤ X → -Y ≤ X - Y := fun X Y hX => by linarith
  apply key
  apply Finset.sum_nonneg
  intro s _
  apply tsum_nonneg
  intro e
  split_ifs
  · exact le_rfl
  · exact le_max_right _ _

theorem gB_le (h : Std p n' k1 t m c r TT a b lam0 w) (j : ℕ) (hj : 1 ≤ j) (hm : j ≤ m) :
    gB p t TT lam0 w j ≤ gam p * ∑ s ∈ TT, (al TT lam0 s : ℝ) - de p t TT lam0 w j := by
  unfold gB
  have key : ∀ A X Y : ℝ, 0 ≤ X → A - X - Y ≤ A - Y := fun A X Y hX => by linarith
  apply key
  apply Finset.sum_nonneg
  intro s _
  apply tsum_nonneg
  intro e
  apply le_min
  · apply div_nonneg
    · exact_mod_cast al_nonneg h s
    · positivity
  · exact_mod_cast cap_nonneg h _ j hj hm

theorem relative_presentation_of_d7 (D : Formalism.BasicNotions.D7) : RelativePresentationLiterature D := by
  intro p n' k1 t m c r TT a b lam0 w h
  unfold Sv
  have hA : 0 ≤ gam p * ∑ s ∈ TT, (al TT lam0 s : ℝ) :=
    mul_nonneg (gam_nonneg h) (Finset.sum_nonneg fun s _ => by exact_mod_cast al_nonneg h s)
  calc ∑ j ∈ Icc 1 m, max (gB p t TT lam0 w j - Pr t r lam0 w j - gA p t TT lam0 w j) 0
      ≤ ∑ j ∈ Icc 1 m, gam p * ∑ s ∈ TT, (al TT lam0 s : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_Icc] at hj
        have e1 := gB_le h j hj.1 hj.2
        have e2 := Pr_nonneg h j hj.1 hj.2
        have e3 := gA_ge p t TT lam0 w j
        exact max_le (by linarith) hA
    _ = (m : ℝ) * gam p * ∑ s ∈ TT, (al TT lam0 s : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TminusLinApply
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

section PlacesLevel

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem edges_fin (v : Fin P.nV) (i : ℕ) (L : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    {L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v) | IsEdge p (P.n' v) i ⟨L'', L⟩}.Finite := by
  apply Formalism.MainNotions.G.LatticeSystems.ef_edges_finite_gen
  apply Nat.finite_of_card_ne_zero
  rw [(P.setting v).res_card]
  exact pow_ne_zero _ (P.setting v).prime.ne_zero

def EE (v : Fin P.nV) (i : ℕ) (L : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :
    Finset (Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) :=
  (edges_fin P v i L).toFinset

theorem mem_EE {v : Fin P.nV} {i : ℕ} {L L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)} :
    L'' ∈ EE P v i L ↔ IsEdge p (P.n' v) i ⟨L'', L⟩ :=
  Set.Finite.mem_toFinset _

theorem Tminus_eq (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp) (L : P.Tup) :
    P.Tminus v i F L = ∑ L'' ∈ EE P v i (L v), F (Function.update L v L'') :=
  finsum_mem_eq_finite_toFinset_sum _ (edges_fin P v i (L v))

def TminusLin (v : Fin P.nV) (i : ℕ) : (P.Tup → P.Xsp) →ₗ[Kf] (P.Tup → P.Xsp) where
  toFun := P.Tminus v i
  map_add' F F' := by
    funext L
    rw [Pi.add_apply, Tminus_eq, Tminus_eq, Tminus_eq, ← Finset.sum_add_distrib]
    rfl
  map_smul' c F := by
    funext L
    rw [RingHom.id_apply, Pi.smul_apply, Tminus_eq, Tminus_eq, Finset.smul_sum]
    rfl

theorem edge_zero_iff {v : Fin P.nV} {L L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)} :
    IsEdge p (P.n' v) 0 ⟨L'', L⟩ ↔ IsLattice (P.W v) L ∧ L'' = L := by
  constructor
  · rintro ⟨_, h2, h3, _, h5⟩
    refine ⟨h2, le_antisymm h3 ?_⟩
    rw [Nat.mul_zero, pow_zero, Nat.card_eq_one_iff_unique] at h5
    have h6 := (Submodule.Quotient.subsingleton_iff).1 h5.1
    intro x hx
    have : (⟨x, hx⟩ : L) ∈ Submodule.comap L.subtype L'' := by
      have h7 : Submodule.comap L.subtype L'' = ⊤ := h6
      rw [h7]
      exact Submodule.mem_top
    exact this
  · rintro ⟨h, rfl⟩
    refine ⟨h, h, le_rfl, fun x hx => Submodule.smul_mem _ _ hx, ?_⟩
    rw [Nat.mul_zero, pow_zero, Nat.card_eq_one_iff_unique]
    have h7 : Submodule.comap (L''.subtype) L'' = ⊤ := Submodule.comap_subtype_self L''
    refine ⟨(Submodule.Quotient.subsingleton_iff).2 h7, ⟨0⟩⟩

theorem Tminus_zero_lat (v : Fin P.nV) (F : P.Tup → P.Xsp) (L : P.Tup) (hL : IsLattice (P.W v) (L v)) :
    P.Tminus v 0 F L = F L := by
  rw [Tminus_eq]
  have : EE P v 0 (L v) = {L v} := by
    ext A
    rw [mem_EE, edge_zero_iff, Finset.mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨hL, h⟩⟩
  rw [this, Finset.sum_singleton]
  exact congrArg F (Function.update_eq_self v L)

theorem Tminus_not_lat (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp) (L : P.Tup) (hL : ¬ IsLattice (P.W v) (L v)) :
    P.Tminus v i F L = 0 := by
  rw [Tminus_eq]
  have : EE P v i (L v) = ∅ := by
    ext A
    rw [mem_EE]
    simp only [Finset.notMem_empty, iff_false]
    exact fun h => hL h.2.1
  rw [this, Finset.sum_empty]

end PlacesLevel

section SysLevel

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def TmLin (v : X.Pl) (i j : ℕ) : X.Fm j →ₗ[X.G.Kf] X.Fm j where
  toFun := X.Tm v i j
  map_add' F F' := by
    funext c
    exact (TminusLin (X.Pj j) (X.vJ j v) i).map_add (F c) (F' c)
  map_smul' a F := by
    funext c
    exact (TminusLin (X.Pj j) (X.vJ j v) i).map_smul a (F c)

def TtLin (v : X.Pl) (i j : ℕ) : X.Fm j →ₗ[X.G.Kf] X.Fm j :=
  if i = 0 then LinearMap.id else ((p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) j i)) • TmLin X v i j

@[simp] theorem TtLin_apply (v : X.Pl) (i j : ℕ) (F : X.Fm j) : TtLin X v i j F = X.Tt v i j F := by
  unfold TtLin Sys.Tt
  split_ifs <;> rfl

theorem yv_eq (v : X.Pl) (F : X.Fm 0) : X.yv v F = ((p : X.G.Kf) ^ X.G.P.ArV v) • X.Tm v X.G.P.r 0 F := rfl

def yvLin (v : X.Pl) : X.Fm 0 →ₗ[X.G.Kf] X.Fm 0 := ((p : X.G.Kf) ^ X.G.P.ArV v) • TmLin X v X.G.P.r 0

theorem Int_zero_off {j : ℕ} {F : X.Fm j} (hF : F ∈ X.Int j) (c : X.Lv.comp j) (L : (X.Pj j).Tup)
    (hL : ¬ (X.Pj j).IsLatTup L) : F c L = 0 := by
  have h1 : F c ∈ (X.Lv.lev j c).M := hF c (Set.mem_univ c)
  unfold Level.M Level.funMod at h1
  have h2 : F c ∈ (⨅ (L : (X.Pj j).Tup) (_ : ¬ (X.Pj j).IsLatTup L),
      LinearMap.ker (LinearMap.proj (R := X.G.O) (φ := fun _ : (X.Pj j).Tup => (X.Pj j).Xsp) L)) := h1.1.2
  rw [Submodule.mem_iInf] at h2
  have h3 := h2 L
  rw [Submodule.mem_iInf] at h3
  exact h3 hL

theorem FQ_zero_off {j : ℕ} {F : X.Fm j} (hF : F ∈ X.FQ j) (c : X.Lv.comp j) (L : (X.Pj j).Tup)
    (hL : ¬ (X.Pj j).IsLatTup L) : F c L = 0 := by
  unfold Sys.FQ at hF
  induction hF using Submodule.span_induction with
  | mem x hx => exact Int_zero_off X hx c L hL
  | zero => rfl
  | add x y _ _ hx hy => rw [Pi.add_apply, Pi.add_apply, hx, hy, add_zero]
  | smul a x _ hx => rw [Pi.smul_apply, Pi.smul_apply, hx, smul_zero]

theorem Tm_zero {j : ℕ} (v : X.Pl) {F : X.Fm j} (hF : F ∈ X.FQ j) : X.Tm v 0 j F = F := by
  funext c L
  show (X.Pj j).Tminus (X.vJ j v) 0 (F c) L = F c L
  by_cases hL : IsLattice ((X.Pj j).W (X.vJ j v)) (L (X.vJ j v))
  · exact Tminus_zero_lat _ _ _ _ hL
  · rw [Tminus_not_lat _ _ _ _ _ hL, FQ_zero_off X hF c L fun h => hL (h _)]

end SysLevel

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

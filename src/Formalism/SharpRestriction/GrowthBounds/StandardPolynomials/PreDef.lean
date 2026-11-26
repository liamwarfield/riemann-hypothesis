module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColsDef
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.SgKSPowP

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.PreDef
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def PreAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c →
    ∀ β : GlobalTheory X, (∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) →
    ∀ (L : LvDat C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β)
      (G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)),
      (∀ j, ColSys C0 CE1 CE2 X O S.w (mm + (n : ℝ) * ka1 X) β L j (G j)) → (∀ j, G j ≠ 0) →
    ∀ Std : MonH X, (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j →
      Nonempty (PreSys C0 CE1 CE2 X O S.w (mm + (n : ℝ) * ka1 X) β L G Std)

def RestPre : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => PreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColNumDef
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def ColumnNumericsAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc), D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j b →
      (∑ l : Fin (segS X.TT j), (if (l : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (b.sg l : ℤ) else 0)) ≤
          ⌊(((X.seg C0 CE1 CE2 j).A0 X.p : ℤ) : ℝ) - (mm + (n : ℝ) * ka1 X)⌋ ∧
      ∀ i : Fin (segS X.TT j), (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma →
        (∑ l : Fin (segS X.TT j), (if (l : ℕ) ≤ (i : ℕ) then (b.w l : ℤ) else 0)) +
          (∑ l : Fin (segS X.TT j), (if (l : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (b.sg l : ℤ) else 0)) ≤
          ⌊(((X.seg C0 CE1 CE2 j).A0 X.p : ℤ) : ℝ) - (mm + (n : ℝ) * ka1 X)⌋

def ColumnNumericsBeyond : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => ColumnNumericsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestRoom
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def usedX (X : Loc) (β : GlobalTheory X) (a0 : Fin (numSeg X.TT) → ℕ) (j0 j : Fin (numSeg X.TT)) : ℕ :=
  X.p ^ segG X.TT j * a0 j + X.p ^ segG X.TT j * (∑ i : Fin (segS X.TT j), (β j).sg i) +
    (∑ i : Fin (segS X.TT j), X.p ^ (segDists X.TT j).get i * ((∑ c : Fin X.m, (β j).rz i c.succ) + (β j).ry i 0)) +
    X.c * (X.m * (X.p ^ segG X.TT j - 1)) + (if j = j0 then X.c else 0)

def RoomAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc), D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c →
    ∀ β : GlobalTheory X, (∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) →
    ∀ a0 : Fin (numSeg X.TT) → ℕ,
      (∀ j, (a0 j : ℤ) + ∑ i : Fin (segS X.TT j),
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then ((β j).sg i : ℤ) else 0) ≤ (X.seg C0 CE1 CE2 j).A0 X.p) →
    ∀ j0 j : Fin (numSeg X.TT),
      usedX X β a0 j0 (rot _ j) ≤ segAPlus X.TT X.aT j - (β j).oPlus

def RestRoom : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => RoomAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXCnt
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf.GenusGluing

open Formalism.MainNotions.G Formalism.MainNotions.LemmaBAlt

theorem strip_count {n : ℕ} (nu mu : Fin n → ℤ) (b : ℕ) (h : HStrip nu mu b) (S : Finset ℤ)
    (hS : ∀ a c, nu a < c → c ≤ mu a → c ∈ S) :
    (S.filter fun c => colH nu c ≠ colH mu c).card = b := by
  classical
  have h1 : ∀ c, ((if colH nu c ≠ colH mu c then 1 else 0 : ℕ) : ℤ) =
      ∑ a : Fin n, (if nu a < c ∧ c ≤ mu a then (1 : ℤ) else 0) := by
    intro c
    obtain ⟨l1, l2⟩ := colH_strip nu mu b h c
    have e : (colH mu c : ℤ) - colH nu c = ∑ a : Fin n, (if nu a < c ∧ c ≤ mu a then (1 : ℤ) else 0) := by
      unfold colH
      rw [Finset.card_filter, Finset.card_filter]
      push_cast
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      have := h.1 a
      by_cases c1 : c ≤ mu a <;> by_cases c2 : c ≤ nu a
      · rw [if_pos c1, if_pos c2, if_neg (by omega)]; ring
      · rw [if_pos c1, if_neg c2, if_pos (by omega)]; ring
      · omega
      · rw [if_neg c1, if_neg c2, if_neg (by omega)]; ring
    rw [← e]
    split_ifs with hne
    · push_cast; omega
    · push_cast; omega
  have h2 : ((S.filter fun c => colH nu c ≠ colH mu c).card : ℤ) = b := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_congr rfl (fun c _ => h1 c), Finset.sum_comm, ← h.2.2]
    refine Finset.sum_congr rfl fun a _ => ?_
    have e : S.filter (fun c => nu a < c ∧ c ≤ mu a) = Finset.Ioc (nu a) (mu a) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨fun x => x.2, fun x => ⟨hS a c x.1 x.2, x⟩⟩
    have e2 : (∑ c ∈ S, (if nu a < c ∧ c ≤ mu a then (1 : ℤ) else 0)) =
        ((S.filter (fun c => nu a < c ∧ c ≤ mu a)).card : ℤ) := by
      rw [Finset.card_filter]; push_cast; rfl
    rw [e2, e, Int.card_Ioc]
    have := h.1 a
    omega
  exact_mod_cast h2

theorem sum_range_odd {M : Type*} [AddCommMonoid M] (G : ℕ → M) (s : ℕ) :
    ∑ a ∈ Finset.range (2 * s + 1), G a = (∑ l ∈ Finset.range s, (G (2 * l) + G (2 * l + 1))) + G (2 * s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have e : 2 * (s + 1) + 1 = (2 * s + 1) + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have e2 : 2 * (s + 1) = 2 * s + 1 + 1 := by ring
    rw [e2]
    abel

theorem sum_fin_odd {M : Type*} [AddCommMonoid M] (s : ℕ) (F : Fin (2 * s + 1) → M) :
    ∑ a, F a = (∑ l : Fin s, (F ⟨2 * l.val, by have := l.2; omega⟩ + F ⟨2 * l.val + 1, by have := l.2; omega⟩)) +
      F ⟨2 * s, by omega⟩ := by
  classical
  set G : ℕ → M := fun a => if h : a < 2 * s + 1 then F ⟨a, h⟩ else 0 with hG
  have e1 : ∑ a, F a = ∑ a ∈ Finset.range (2 * s + 1), G a := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hG]; simp only [a.2, dif_pos]
  rw [e1, sum_range_odd, Finset.sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    have := l.2
    rw [hG]
    simp only
    rw [dif_pos (by omega), dif_pos (by omega)]
  · rw [hG]; simp only; rw [dif_pos (by omega)]

end Formalism.MainNotions.ColumnSystems.Pf.GenusGluing
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXRen
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf.GenusGluing

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

variable {p f : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p f) O]

def renV {ι ι' : Type} {k k' : ℕ} (e : ι → ι') (hk : k = k') : ι × Fin k → ι' × Fin k' :=
  fun v => (e v.1, Fin.cast hk v.2)

theorem renV_injective {ι ι' : Type} {k k' : ℕ} (e : ι → ι') (he : Function.Injective e) (hk : k = k') :
    Function.Injective (renV e hk) := by
  intro a b h
  simp only [renV, Prod.mk.injEq] at h
  exact Prod.ext (he h.1) (Fin.cast_injective hk h.2)

theorem sigMat_congr_pos {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p f)) (s s' : ℤ)
    (h : s % (f : ℤ) = s' % (f : ℤ)) : sigMat p f O g s = sigMat p f O g s' := by
  simp only [sigMat, sigPow, h]

theorem liftSubst_rename (w : O) (r : ℕ) {ι ι' : Type} (LL : LiftLetters ι) (LL' : LiftLetters ι') (e : ι → ι')
    (hvec : ∀ i, LL'.vec (e i) = LL.vec i) (hpos : ∀ i, LL'.pos (e i) % (f : ℤ) = LL.pos i % (f : ℤ))
    {k k' : ℕ} (hk : k = k') (g : Matrix (Fin k') (Fin k') (WF p f)) (F : MvPolynomial (ι × Fin k) (KK O)) :
    liftSubst p f O w r LL' g (rename (renV e hk) F) =
      rename (renV e hk) (liftSubst p f O w r LL (g.submatrix (Fin.cast hk) (Fin.cast hk)) F) := by
  subst hk
  have hsub : g.submatrix (Fin.cast (rfl : k = k)) (Fin.cast rfl) = g := by
    ext a b
    simp
  rw [hsub]
  have key : (liftSubst p f O w r LL' g).comp (rename (renV e (rfl : k = k))) =
      (rename (renV e (rfl : k = k))).comp (liftSubst p f O w r LL g) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, a⟩
    simp only [AlgHom.comp_apply, rename_X, liftSubst, aeval_X, renV, Fin.cast_eq_self, hvec]
    rw [sigMat_congr_pos g _ _ (hpos i)]
    split_ifs <;> simp [map_sum, map_mul, rename_X, rename_C, apply_ite, renV, Fin.cast_eq_self]
  exact AlgHom.congr_fun key F

theorem isGLW_submatrix_cast {k k' : ℕ} (hk : k = k') (g : Matrix (Fin k') (Fin k') (WF p f)) (hg : IsGLW g) :
    IsGLW (g.submatrix (Fin.cast hk) (Fin.cast hk)) := by
  unfold IsGLW at hg ⊢
  rw [show (Fin.cast hk : Fin k → Fin k') = finCongr hk from rfl, Matrix.det_submatrix_equiv_self]
  exact hg

theorem one_submatrix_cast {k k' : ℕ} (hk : k = k') :
    (1 : Matrix (Fin k') (Fin k') (WF p f)).submatrix (Fin.cast hk) (Fin.cast hk) = 1 := by
  ext a b
  simp [Matrix.one_apply]

private theorem coeff_rename_mem_multiple_of_coeff {σ τ : Type} (φ : σ → τ) (a : O) (P : MvPolynomial σ (KK O))
    (h : ∀ m, ∃ c : O, P.coeff m = algebraMap O (KK O) (a * c)) :
    ∀ m, ∃ c : O, (rename φ P).coeff m = algebraMap O (KK O) (a * c) := by
  classical
  have hP : rename φ P = ∑ u ∈ P.support, monomial (u.mapDomain φ) (P.coeff u) := by
    conv_lhs => rw [P.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, rename_monomial]
  rw [hP]
  refine Finset.sum_induction _
    (fun Q : MvPolynomial τ (KK O) => ∀ m, ∃ c : O, Q.coeff m = algebraMap O (KK O) (a * c)) ?_ ?_ ?_
  · intro Q R hQ hR m
    obtain ⟨c1, h1⟩ := hQ m
    obtain ⟨c2, h2⟩ := hR m
    exact ⟨c1 + c2, by rw [MvPolynomial.coeff_add, h1, h2, mul_add, map_add (f := _)]⟩
  · intro m
    exact ⟨0, by simp⟩
  · intro u _ m
    rw [coeff_monomial]
    split_ifs
    · exact h u
    · exact ⟨0, by simp⟩

private theorem coeff_mem_multiple_of_rename_injective {σ τ : Type} (φ : σ → τ) (hφ : Function.Injective φ) (a : O)
    (P : MvPolynomial σ (KK O))
    (h : ∀ m, ∃ c : O, (rename φ P).coeff m = algebraMap O (KK O) (a * c)) :
    ∀ m, ∃ c : O, P.coeff m = algebraMap O (KK O) (a * c) := by
  intro m
  obtain ⟨c, hc⟩ := h (m.mapDomain φ)
  rw [coeff_rename_mapDomain φ hφ] at hc
  exact ⟨c, hc⟩

theorem inWj_rename_iff {σ τ : Type} (φ : σ → τ) (hφ : Function.Injective φ) (w : O)
    (P : MvPolynomial σ (KK O)) (j : ℕ) : InWj w (rename φ P) j ↔ InWj w P j :=
  ⟨coeff_mem_multiple_of_rename_injective φ hφ _ P, coeff_rename_mem_multiple_of_coeff φ _ P⟩

theorem inWj_rename {σ τ : Type} (φ : σ → τ) (w : O) (P : MvPolynomial σ (KK O)) (j : ℕ)
    (h : InWj w P j) : InWj w (rename φ P) j :=
  coeff_rename_mem_multiple_of_coeff φ _ P h

theorem inA_rename {σ τ : Type} (φ : σ → τ) (P : MvPolynomial σ (KK O)) (h : InA P) : InA (rename φ P) := by
  have e : ∀ {ρ : Type} (Q : MvPolynomial ρ (KK O)),
      InA Q ↔ ∀ m, ∃ c : O, Q.coeff m = algebraMap O (KK O) (1 * c) := by
    intro ρ Q
    simp only [one_mul]
    rfl
  rw [e] at h ⊢
  exact coeff_rename_mem_multiple_of_coeff φ _ P h

theorem inWjRg_rename (w : O) (r : ℕ) {ι ι' : Type} (LL : LiftLetters ι) (LL' : LiftLetters ι') (e : ι → ι')
    (he : Function.Injective e) (hvec : ∀ i, LL'.vec (e i) = LL.vec i)
    (hpos : ∀ i, LL'.pos (e i) % (f : ℤ) = LL.pos i % (f : ℤ)) {k k' : ℕ} (hk : k = k')
    (g : Matrix (Fin k') (Fin k') (WF p f)) (F : MvPolynomial (ι × Fin k) (KK O)) (j : ℕ) :
    InWjRg p f O w r LL' g (rename (renV e hk) F) j ↔
      InWjRg p f O w r LL (g.submatrix (Fin.cast hk) (Fin.cast hk)) F j := by
  unfold InWjRg
  rw [liftSubst_rename w r LL LL' e hvec hpos hk g F]
  exact inWj_rename_iff _ (renV_injective e he hk) _ _ _

open Classical in
theorem mem_Pol_rename {R : Type} [CommRing R] {ι ι' : Type} [Fintype ι] {k k' : ℕ} (e : ι → ι')
    (he : Function.Injective e) (hk : k = k') (d : ι → ℕ) (F : MvPolynomial (ι × Fin k) R) (hF : F ∈ Pol R k d) :
    rename (renV e hk) F ∈ Pol R k' (fun l => ∑ i : ι, if e i = l then d i else 0) := by
  subst hk
  unfold Pol at hF ⊢
  rw [MvPolynomial.mem_restrictSupport_iff] at hF ⊢
  rw [MvPolynomial.support_rename_of_injective (renV_injective e he rfl)]
  intro m hm
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hm
  obtain ⟨u, hu, rfl⟩ := hm
  have hud := hF hu
  intro l
  unfold multideg
  by_cases hl : ∃ i, e i = l
  · obtain ⟨i, rfl⟩ := hl
    have h1 : ∀ c, (Finsupp.mapDomain (renV e rfl) u) (e i, c) = u (i, c) := by
      intro c
      have h2 := Finsupp.mapDomain_apply_of_injective (renV_injective e he rfl) u (i, c)
      simpa [renV] using h2
    simp only [h1]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (fun h => hj (he h))]) (by simp), if_pos rfl]
    exact hud i
  · push_neg at hl
    have h0 : ∀ c, (Finsupp.mapDomain (renV e rfl) u) (l, c) = 0 := by
      intro c
      apply Finsupp.mapDomain_notin_range
      rintro ⟨v, hv⟩
      exact hl v.1 (congrArg Prod.fst hv)
    simp [h0, hl]

end Formalism.MainNotions.ColumnSystems.Pf.GenusGluing
end
end

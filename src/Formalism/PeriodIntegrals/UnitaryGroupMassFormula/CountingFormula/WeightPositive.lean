module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountPositivity.CardLeOfNegFamily

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DefFinWOf
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.FiniteLeOfPosDef
namespace PI.UnitaryGroupMassFormula.CntFormula

theorem finite_le_of_posDef {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (B : LinearMap.BilinForm ℚ V) (hS : ∀ x y, B x y = B y x) (hpos : ∀ v, v ≠ 0 → 0 < B v v)
    (A : Submodule ℤ V) (hA : A.FG) (c : ℚ) : {v | v ∈ A ∧ B v v ≤ c}.Finite := by
  classical
  obtain ⟨S, hS'⟩ := hA
  have hnn : ∀ v, 0 ≤ B v v := fun v => by
    by_cases hv : v = 0
    · simp [hv]
    · exact (hpos v hv).le

  have cs : ∀ v w, B v w ^ 2 ≤ B v v * B w w := by
    intro v w
    by_cases hw : w = 0
    · simp [hw]
    · have hww := hpos w hw
      have key := hnn (B w w • v - B v w • w)
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        hS w v] at key
      have h2 : B w w * B v w ^ 2 ≤ B w w * (B v v * B w w) := by nlinarith [key]
      exact le_of_mul_le_mul_left h2 hww
  let b := Module.finBasis ℚ V
  have hinj : ∀ v w, (∀ i, B v (b i) = B w (b i)) → v = w := by
    intro v w h
    have h0 : B (v - w) = 0 := b.ext fun i => by simp [map_sub, h i]
    by_contra hne
    have h1 := hpos (v - w) (sub_ne_zero.2 hne)
    rw [h0] at h1
    simp at h1
  let N : ℕ := ∏ s ∈ S, ∏ i, (B s (b i)).den
  have hNpos : 0 < N :=
    Finset.prod_pos fun s _ => Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (Rat.den_nz _)

  have hint : ∀ v ∈ A, ∀ i, ∃ z : ℤ, (z : ℚ) = N * B v (b i) := by
    intro v hv
    rw [← hS'] at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      intro i
      have hd : (B x (b i)).den ∣ N :=
        (Finset.dvd_prod_of_mem (fun i => (B x (b i)).den) (Finset.mem_univ i)).trans
          (Finset.dvd_prod_of_mem (fun s => ∏ i, (B s (b i)).den) hx)
      obtain ⟨k, hk⟩ := hd
      refine ⟨k * (B x (b i)).num, ?_⟩
      have e := Rat.mul_den_eq_num (B x (b i))
      rw [hk]
      push_cast
      linear_combination (-(k : ℚ)) * e
    | zero => intro i; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro i
      obtain ⟨z1, h1⟩ := hx i
      obtain ⟨z2, h2⟩ := hy i
      refine ⟨z1 + z2, ?_⟩
      rw [map_add (f := _), LinearMap.add_apply]
      push_cast
      rw [h1, h2]
      ring
    | smul a x _ hx =>
      intro i
      obtain ⟨z, hz⟩ := hx i
      refine ⟨a * z, ?_⟩
      rw [← Int.cast_smul_eq_zsmul ℚ a x, map_smul, LinearMap.smul_apply, smul_eq_mul]
      push_cast
      rw [hz]
      ring
  have hbd : ∀ v, B v v ≤ c → ∀ i, |B v (b i)| ≤ 1 + |c| * B (b i) (b i) := by
    intro v hv i
    have h1 := cs v (b i)
    have h2 : B v v * B (b i) (b i) ≤ |c| * B (b i) (b i) :=
      mul_le_mul_of_nonneg_right (hv.trans (le_abs_self c)) (hnn _)
    have h3 : |B v (b i)| ≤ 1 + B v (b i) ^ 2 := by
      nlinarith [sq_nonneg (|B v (b i)| - 1), sq_abs (B v (b i))]
    linarith
  let g : V → Fin (Module.finrank ℚ V) → ℤ := fun v i => round ((N : ℚ) * B v (b i))
  have hg : ∀ v ∈ A, ∀ i, ((g v i : ℤ) : ℚ) = N * B v (b i) := by
    intro v hv i
    obtain ⟨z, hz⟩ := hint v hv i
    simp only [g]
    rw [← hz, round_intCast]
  apply Set.Finite.of_finite_image (f := g)
  · refine Set.Finite.subset (Set.Finite.pi (t := fun i =>
      Set.Icc (-⌈(N : ℚ) * (1 + |c| * B (b i) (b i))⌉) ⌈(N : ℚ) * (1 + |c| * B (b i) (b i))⌉)
      fun i => Set.finite_Icc _ _) ?_
    rintro _ ⟨v, ⟨hvA, hvc⟩, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro i
    have e := hg v hvA i
    have hb : |((g v i : ℤ) : ℚ)| ≤ N * (1 + |c| * B (b i) (b i)) := by
      rw [e, abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (hbd v hvc i) (Nat.cast_nonneg _)
    have hK := Int.le_ceil ((N : ℚ) * (1 + |c| * B (b i) (b i)))
    have l1 := neg_abs_le ((g v i : ℤ) : ℚ)
    have l2 := le_abs_self ((g v i : ℤ) : ℚ)
    constructor
    · have : ((-⌈(N : ℚ) * (1 + |c| * B (b i) (b i))⌉ : ℤ) : ℚ) ≤ ((g v i : ℤ) : ℚ) := by
        push_cast
        linarith
      exact_mod_cast this
    · have : ((g v i : ℤ) : ℚ) ≤ ((⌈(N : ℚ) * (1 + |c| * B (b i) (b i))⌉ : ℤ) : ℚ) := by
        linarith
      exact_mod_cast this
  · rintro v ⟨hvA, -⟩ w ⟨hwA, -⟩ hvw
    apply hinj
    intro i
    have e : (N : ℚ) * B v (b i) = N * B w (b i) := by
      rw [← hg v hvA i, ← hg w hwA i, congrFun hvw i]
    exact mul_left_cancel₀ (by exact_mod_cast hNpos.ne') e

end PI.UnitaryGroupMassFormula.CntFormula
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DefFinW : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (P : Submodule ℤ (VS D).V), P.FG → ∀ c : D.host.E,
    {w : (VS D).V | w ∈ P ∧ (∀ a, (VS D).hT (D.sp.hypE a) w = 0) ∧ (∀ a, (VS D).hT (D.sp.hypF a) w = 0) ∧
      (VS D).hT D.sp.zm w = 0 ∧ (VS D).hT w w = c}.Finite

def WPos : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (w : (VS D).V), (∀ a, (VS D).hT (D.sp.hypE a) w = 0) →
    (∀ a, (VS D).hT (D.sp.hypF a) w = 0) → (VS D).hT D.sp.zm w = 0 → w ≠ 0 →
      0 < Algebra.trace ℚ D.host.E ((VS D).hT w w)

theorem defFinW_of (hW : WPos) : DefFinW := by
  intro D P hP c
  classical
  letI : Module ℚ (VS D).V := Module.compHom (VS D).V (algebraMap ℚ D.host.E)
  have hsm : ∀ (q : ℚ) (v : (VS D).V), q • v = (algebraMap ℚ D.host.E q) • v := fun _ _ => rfl
  have hsmL : ∀ (q : ℚ) (v w : (VS D).V), (VS D).hT (q • v) w = (q : D.host.E) * (VS D).hT v w := by
    intro q v w
    rw [hsm, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, eq_ratCast, map_ratCast]
  have hsmR : ∀ (q : ℚ) (v w : (VS D).V), (VS D).hT v (q • w) = (q : D.host.E) * (VS D).hT v w := by
    intro q v w
    rw [hsm, map_smul, smul_eq_mul, eq_ratCast]
  have htr : ∀ (q : ℚ) (y : D.host.E), Algebra.trace ℚ D.host.E ((q : D.host.E) * y) = q * Algebra.trace ℚ D.host.E y := by
    intro q y
    rw [show (q : D.host.E) * y = q • y by rw [Algebra.smul_def, eq_ratCast], map_smul, smul_eq_mul]
  let Wq : Submodule ℚ (VS D).V :=
    { carrier := {w | (∀ a, (VS D).hT (D.sp.hypE a) w = 0) ∧ (∀ a, (VS D).hT (D.sp.hypF a) w = 0) ∧
        (VS D).hT D.sp.zm w = 0}
      add_mem' := by
        rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
        exact ⟨fun a => by rw [map_add (f := _), hx1, hy1, add_zero],
          fun a => by rw [map_add (f := _), hx2, hy2, add_zero], by rw [map_add (f := _), hx3, hy3, add_zero]⟩
      zero_mem' := ⟨fun a => map_zero _, fun a => map_zero _, map_zero _⟩
      smul_mem' := by
        rintro q x ⟨hx1, hx2, hx3⟩
        exact ⟨fun a => by rw [hsmR, hx1, mul_zero], fun a => by rw [hsmR, hx2, mul_zero],
          by rw [hsmR, hx3, mul_zero]⟩ }
  let A0 : Submodule ℤ (VS D).V := P ⊓ Wq.restrictScalars ℤ
  have hA0 : A0.FG := by
    haveI := isNoetherian_of_fg_of_noetherian P hP
    have hfg : (A0.comap P.subtype).FG := IsNoetherian.noetherian _
    have := hfg.map P.subtype
    rwa [Submodule.map_comap_subtype, inf_of_le_right (inf_le_left : A0 ≤ P)] at this
  obtain ⟨s, hs⟩ := hA0
  let U : Submodule ℚ (VS D).V := Submodule.span ℚ (s : Set (VS D).V)
  haveI : FiniteDimensional ℚ U := FiniteDimensional.span_finset ℚ s
  have hA0U : ∀ w ∈ A0, w ∈ U := fun w hw => by
    rw [← hs] at hw
    exact Submodule.span_le_restrictScalars ℤ ℚ _ hw
  have hUle : U ≤ Wq := by
    refine Submodule.span_le.mpr fun x hx => ?_
    have hx' : x ∈ A0 := by
      rw [← hs]
      exact Submodule.subset_span hx
    exact (Submodule.mem_inf.mp hx').2
  let B : LinearMap.BilinForm ℚ U := LinearMap.mk₂ ℚ
    (fun u v : U => (Algebra.trace ℚ D.host.E ((VS D).hT u v) + Algebra.trace ℚ D.host.E ((VS D).hT v u)) / 2)
    (fun m1 m2 n => by simp only [Submodule.coe_add, map_add (f := _), LinearMap.add_apply]; ring)
    (fun q m n => by simp only [Submodule.coe_smul, hsmL, hsmR, htr, smul_eq_mul]; ring)
    (fun m n1 n2 => by simp only [Submodule.coe_add, map_add (f := _), LinearMap.add_apply]; ring)
    (fun q m n => by simp only [Submodule.coe_smul, hsmL, hsmR, htr, smul_eq_mul]; ring)
  have hS : ∀ x y, B x y = B y x := fun x y => by
    simp only [B, LinearMap.mk₂_apply]
    ring
  have hpos : ∀ v, v ≠ 0 → 0 < B v v := by
    intro v hv
    obtain ⟨h1, h2, h3⟩ := hUle v.2
    have := hW D v h1 h2 h3 (fun h => hv (Subtype.ext h))
    simp only [B, LinearMap.mk₂_apply]
    linarith
  let A : Submodule ℤ U := A0.comap (U.subtype.restrictScalars ℤ)
  have hA : A.FG := by
    refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars ℤ)
      Subtype.val_injective ?_
    rw [Submodule.map_comap_eq_self (fun w hw => ⟨⟨w, hA0U w hw⟩, rfl⟩)]
    exact ⟨s, hs⟩
  have hfin := finite_le_of_posDef B hS hpos A hA (Algebra.trace ℚ D.host.E c)
  refine (hfin.image U.subtype).subset ?_
  rintro w ⟨hwP, h1, h2, h3, hc⟩
  have hwA0 : w ∈ A0 := Submodule.mem_inf.mpr ⟨hwP, ⟨h1, h2, h3⟩⟩
  refine ⟨⟨w, hA0U w hwA0⟩, ⟨hwA0, ?_⟩, rfl⟩
  simp only [B, LinearMap.mk₂_apply, Subtype.coe_mk, hc]
  linarith

end PI.UnitaryGroupMassFormula.CntFormula
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hswap (D : Formalism.BasicNotions.D7) (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := ((VS D).herm.eq x y).symm

theorem hzero_swap (D : Formalism.BasicNotions.D7) {x y : (VS D).V} (h : (VS D).hT x y = 0) : (VS D).hT y x = 0 := by
  rw [hswap, h, star_zero]

theorem hFE (D : Formalism.BasicNotions.D7) (i i' : Fin D.R.rS) :
    (VS D).hT (D.sp.hypF i) (D.sp.hypE i') = if i' = i then 1 else 0 := by
  rw [hswap, D.sp.hyp_ef i' i]
  split_ifs <;> simp

theorem hEz (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT (D.sp.hypE i) D.sp.zm = 0 := by
  rw [hswap, (D.sp.hyp_orthz i).1, star_zero]

theorem hFz (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT (D.sp.hypF i) D.sp.zm = 0 := by
  rw [hswap, (D.sp.hyp_orthz i).2, star_zero]

theorem real_of_emb (D : Formalism.BasicNotions.D7) (τ : D.host.E →+* ℂ) (w : (VS D).V) :
    τ ((VS D).hT w w) = ((τ ((VS D).hT w w)).re : ℂ) := by
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  have h1 : starRingEnd ℂ (τ ((VS D).hT w w)) = τ ((VS D).hT w w) := by
    rw [← hτ, ← hswap]
  have him : (τ ((VS D).hT w w)).im = 0 := Complex.conj_eq_iff_im.1 h1
  exact Complex.ext (by simp) (by simp [him])

theorem semidef (D : Formalism.BasicNotions.D7) (w : (VS D).V) (hE : ∀ a, (VS D).hT (D.sp.hypE a) w = 0)
    (hF : ∀ a, (VS D).hT (D.sp.hypF a) w = 0) (hz : (VS D).hT D.sp.zm w = 0) (τ : D.host.E →+* ℂ) :
    0 ≤ (τ ((VS D).hT w w)).re := by
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  by_contra hlt
  rw [not_le] at hlt
  have hT0 : (0 : ℝ) < D.sp.T := by exact_mod_cast D.sp.T_prime.pos
  let wv : Fin D.R.rS ⊕ Bool → (VS D).V :=
    Sum.elim (fun a => D.sp.hypE a - D.sp.hypF a) (fun b => if b then w else D.sp.zm)
  let d : Fin D.R.rS ⊕ Bool → ℝ :=
    Sum.elim (fun _ => -2) (fun b => if b then (τ ((VS D).hT w w)).re else -(D.sp.T : ℝ))
  have hoff : ∀ i j, i ≠ j → (VS D).hT (wv i) (wv j) = 0 := by
    intro i j hij
    rcases i with a | b <;> rcases j with a' | b'
    · have ha : a ≠ a' := fun h => hij (by rw [h])
      have ha' : a' ≠ a := fun h => ha h.symm
      simp only [wv, Sum.elim_inl, map_sub, LinearMap.sub_apply, D.sp.hyp_ee, D.sp.hyp_ff, D.sp.hyp_ef,
        hFE, if_neg ha, if_neg ha']
      simp
    · cases b'
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, if_false, map_sub,
          LinearMap.sub_apply, hEz, hFz, sub_zero]
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, if_true, map_sub, LinearMap.sub_apply, hE, hF,
          sub_zero]
    · cases b
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true, if_false, map_sub,
          (D.sp.hyp_orthz a').1, (D.sp.hyp_orthz a').2, sub_zero]
      · simp only [wv, Sum.elim_inl, Sum.elim_inr, if_true, map_sub, hzero_swap D (hE a'),
          hzero_swap D (hF a'), sub_zero]
    · cases b <;> cases b'
      · exact absurd rfl hij
      · simpa [wv] using hz
      · simpa [wv] using hzero_swap D hz
      · exact absurd rfl hij
  have hdiag : ∀ i, τ ((VS D).hT (wv i) (wv i)) = (d i : ℂ) := by
    intro i
    rcases i with a | b
    · simp only [wv, d, Sum.elim_inl, map_sub, LinearMap.sub_apply, D.sp.hyp_ee, D.sp.hyp_ff,
        D.sp.hyp_ef, hFE, if_true]
      rw [map_zero, map_one]
      push_cast; ring
    · cases b
      · simp only [wv, d, Sum.elim_inr, Bool.false_eq_true, if_false, D.sp.zm_norm, map_neg,
          map_natCast]
        push_cast; ring
      · simp only [wv, d, Sum.elim_inr, if_true]
        exact real_of_emb D τ w
  have hneg : ∀ i, d i < 0 := by
    intro i
    rcases i with a | b
    · simp [d]
    · cases b
      · simp only [d, Sum.elim_inr, Bool.false_eq_true, if_false]; linarith
      · simpa [d] using hlt
  have hc := PI.CntNotPosW.card_le_of_negFamily (VS D) τ hτ (D.sp.Y_sig 0 τ) wv d hoff hdiag hneg
  have hq : ((D.sp.Y 0).sig τ).2 = D.R.rS + 1 := by rw [D.sp.baseSpace_signature_eq τ]; rfl
  rw [hq] at hc
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool] at hc
  omega

theorem isotropic_zero (D : Formalism.BasicNotions.D7) (w : (VS D).V) (hE : ∀ a, (VS D).hT (D.sp.hypE a) w = 0)
    (hF : ∀ a, (VS D).hT (D.sp.hypF a) w = 0) (hz : (VS D).hT D.sp.zm w = 0)
    (h0 : (VS D).hT w w = 0) : w = 0 := by
  let τ : D.host.E →+* ℂ := (IsAlgClosed.lift : D.host.E →ₐ[ℚ] ℂ).toRingHom
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ

  have orthW : ∀ y : (VS D).V, (∀ a, (VS D).hT (D.sp.hypE a) y = 0) →
      (∀ a, (VS D).hT (D.sp.hypF a) y = 0) → (VS D).hT D.sp.zm y = 0 → (VS D).hT w y = 0 := by
    intro y hyE hyF hyz
    by_contra hx
    set x := (VS D).hT w y with hxdef
    have hτx : τ x ≠ 0 := (map_ne_zero τ).2 hx
    have hN : 0 < Complex.normSq (τ x) := Complex.normSq_pos.2 hτx
    set y' : (VS D).V := star x • y with hy'
    have hxx : τ (x * star x) = ((Complex.normSq (τ x) : ℝ) : ℂ) := by
      rw [map_mul, hτ, Complex.mul_conj]
    have key : ∀ n : ℕ, 2 * n * Complex.normSq (τ x) ≤ (τ ((VS D).hT y' y')).re := by
      intro n
      set v : (VS D).V := (n : D.host.E) • w - y' with hv
      have hvE : ∀ a, (VS D).hT (D.sp.hypE a) v = 0 := by
        intro a; simp [hv, hy', map_sub, map_smul, hE a, hyE a]
      have hvF : ∀ a, (VS D).hT (D.sp.hypF a) v = 0 := by
        intro a; simp [hv, hy', map_sub, map_smul, hF a, hyF a]
      have hvz : (VS D).hT D.sp.zm v = 0 := by
        simp [hv, hy', map_sub, map_smul, hz, hyz]
      have hs := semidef D v hvE hvF hvz τ
      have hyw : (VS D).hT y w = star x := by rw [hswap]
      have e1 : (VS D).hT v v = -(2 * (n : D.host.E)) * (x * star x) + (VS D).hT y' y' := by
        simp only [hv, map_sub, LinearMap.sub_apply, map_smulₛₗ, map_smul, LinearMap.smul_apply,
          smul_eq_mul, starRingEnd_apply, star_natCast, h0, hy', star_star, hyw, ← hxdef, RingHom.id_apply]
        ring
      have e2 : (τ ((VS D).hT v v)).re =
          -(2 * n * Complex.normSq (τ x)) + (τ ((VS D).hT y' y')).re := by
        rw [e1, map_add (f := _), map_mul, hxx, map_neg, map_mul, map_ofNat, map_natCast, Complex.add_re]
        congr 1
        have : -(2 * (n : ℂ)) * ((Complex.normSq (τ x) : ℝ) : ℂ) =
            ((-(2 * n * Complex.normSq (τ x)) : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.ofReal_re]
      linarith
    obtain ⟨n, hn⟩ := exists_nat_gt ((τ ((VS D).hT y' y')).re / (2 * Complex.normSq (τ x)))
    have h2 := key n
    rw [div_lt_iff₀ (by positivity)] at hn
    nlinarith

  have hzz : (VS D).hT D.sp.zm D.sp.zm ≠ 0 := by
    rw [D.sp.zm_norm, neg_ne_zero]
    exact_mod_cast D.sp.T_prime.ne_zero
  apply (VS D).nondeg.1 w
  intro x
  set xW : (VS D).V := x - ∑ a, ((VS D).hT (D.sp.hypF a) x • D.sp.hypE a + (VS D).hT (D.sp.hypE a) x • D.sp.hypF a) -
    ((VS D).hT D.sp.zm x / (VS D).hT D.sp.zm D.sp.zm) • D.sp.zm with hxW
  have hWE : ∀ b, (VS D).hT (D.sp.hypE b) xW = 0 := by
    intro b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hxW, map_sub, map_sum, map_add (f := _), map_smul, D.sp.hyp_ee, D.sp.hyp_ef, hEz]
  have hWF : ∀ b, (VS D).hT (D.sp.hypF b) xW = 0 := by
    intro b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hxW, map_sub, map_sum, map_add (f := _), map_smul, D.sp.hyp_ff, hFE, hFz]
  have hWz : (VS D).hT D.sp.zm xW = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hxW, map_sub, map_sum, map_add (f := _), map_smul, (D.sp.hyp_orthz _).1, (D.sp.hyp_orthz _).2, hzz]
  have h1 := orthW xW hWE hWF hWz
  have hwE : ∀ a, (VS D).hT w (D.sp.hypE a) = 0 := fun a => hzero_swap D (hE a)
  have hwF : ∀ a, (VS D).hT w (D.sp.hypF a) = 0 := fun a => hzero_swap D (hF a)
  have hwz : (VS D).hT w D.sp.zm = 0 := hzero_swap D hz
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [hxW, map_sub, map_sum, map_add (f := _), map_smul, hwE, hwF, hwz] using h1

theorem weights_are_positive : WPos := by
  intro D w hE hF hz hw
  have pos : ∀ τ : D.host.E →+* ℂ, 0 < (τ ((VS D).hT w w)).re := by
    intro τ
    refine lt_of_le_of_ne (semidef D w hE hF hz τ) fun h => hw ?_
    apply isotropic_zero D w hE hF hz
    apply τ.injective
    rw [real_of_emb D τ w, ← h, Complex.ofReal_zero, map_zero]
  haveI : Nonempty (D.host.E →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have ht := trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) (E := ℂ) (x := (VS D).hT w w)
  have hre := congrArg Complex.re ht
  rw [Complex.re_sum] at hre
  have hsum : 0 < ∑ σ : D.host.E →ₐ[ℚ] ℂ, (σ ((VS D).hT w w)).re :=
    Finset.sum_pos (fun σ _ => pos σ.toRingHom) Finset.univ_nonempty
  rw [← hre] at hsum
  have : ((Algebra.trace ℚ D.host.E ((VS D).hT w w) : ℚ) : ℝ) =
      (algebraMap ℚ ℂ (Algebra.trace ℚ D.host.E ((VS D).hT w w))).re := by simp
  rw [← this] at hsum
  exact_mod_cast hsum

theorem definite_finite : DefFinW := defFinW_of weights_are_positive

end PI.UnitaryGroupMassFormula.CntFormula

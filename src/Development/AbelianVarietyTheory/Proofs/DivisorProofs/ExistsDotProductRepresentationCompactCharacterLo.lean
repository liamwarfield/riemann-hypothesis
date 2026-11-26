module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReGt
namespace GlobalTheory.UnitNormRealPartBound

lemma norm_eq_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) : ‖z‖ = 1 := by
  have hup : ∀ n : ℕ, ‖z‖ ^ n < 3 / 2 := fun n => by
    have := h n
    calc ‖z‖ ^ n = ‖(z ^ n - 1) + 1‖ := by rw [sub_add_cancel, norm_pow]
      _ ≤ ‖z ^ n - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ < 3 / 2 := by rw [norm_one]; linarith
  have hlo : ∀ n : ℕ, 1 / 2 < ‖z‖ ^ n := fun n => by
    have := h n
    have h2 : ‖(1 : ℂ)‖ ≤ ‖z ^ n - 1‖ + ‖z ^ n‖ := by
      calc ‖(1 : ℂ)‖ = ‖-(z ^ n - 1) + z ^ n‖ := by ring_nf
        _ ≤ ‖-(z ^ n - 1)‖ + ‖z ^ n‖ := norm_add_le _ _
        _ = ‖z ^ n - 1‖ + ‖z ^ n‖ := by rw [norm_neg]
    rw [norm_one, norm_pow] at h2
    linarith
  rcases lt_trichotomy ‖z‖ 1 with h1 | h1 | h1
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) h1
    linarith [hlo n]
  · exact h1
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (3 / 2 : ℝ) h1
    linarith [hup n]

lemma re_gt {w : ℂ} (hw : ‖w‖ = 1) (h : ‖w - 1‖ < 1 / 2) : 7 / 8 < w.re := by
  have h1 : ‖w - 1‖ ^ 2 < 1 / 4 := by nlinarith [norm_nonneg (w - 1)]
  have h2 : ‖w‖ ^ 2 = 1 := by rw [hw]; norm_num
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h1 h2
  simp at h1
  nlinarith

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  have hz := norm_eq_one h
  have hnp : ∀ n : ℕ, ‖z ^ n‖ = 1 := fun n => by rw [norm_pow, hz, one_pow]
  have hre : ∀ n : ℕ, 7 / 8 < (z ^ n).re := fun n => re_gt (hnp n) (h n)
  have key : ∀ k : ℕ, (7 / 4 : ℝ) ^ k * |z.im| ≤ |(z ^ (2 ^ k)).im| := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : z ^ (2 ^ (k + 1)) = z ^ (2 ^ k) * z ^ (2 ^ k) := by
        rw [pow_succ, pow_mul, sq]
      have hr := hre (2 ^ k)
      have e2 : (z ^ (2 ^ (k + 1))).im = 2 * (z ^ (2 ^ k)).re * (z ^ (2 ^ k)).im := by
        rw [e, Complex.mul_im]; ring
      rw [e2, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * (z ^ 2 ^ k).re), pow_succ]
      have : (7 / 4 : ℝ) ≤ 2 * (z ^ 2 ^ k).re := by linarith
      have hn : 0 ≤ (7 / 4 : ℝ) ^ k * |z.im| := by positivity
      nlinarith [abs_nonneg (z ^ 2 ^ k).im]
  have him : z.im = 0 := by
    by_contra hne
    have hpos : 0 < |z.im| := abs_pos.mpr hne
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / |z.im|) (by norm_num : (1 : ℝ) < 7 / 4)
    have hb : |(z ^ (2 ^ k)).im| ≤ 1 := (Complex.abs_im_le_norm _).trans (hnp _).le
    have : 1 < (7 / 4 : ℝ) ^ k * |z.im| := by rwa [div_lt_iff₀ hpos] at hk
    linarith [key k]
  have h1 := hre 1
  rw [pow_one] at h1
  have h2 : ‖z‖ ^ 2 = 1 := by rw [hz]; norm_num
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, him] at h2
  apply Complex.ext
  · simp; nlinarith
  · simp [him]

end GlobalTheory.UnitNormRealPartBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDotProductRepresentationCompactCharacterLo
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.CompactCharDual

theorem eq_one_of_pow_close {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.UnitNormRealPartBound.main
  | exact _root_.GlobalTheory.UnitNormRealPartBound.main
  | (apply _root_.GlobalTheory.UnitNormRealPartBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitNormRealPartBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitNormRealPartBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitNormRealPartBound.main ..)

theorem exists_ball_ker {K : Type} [NormedAddCommGroup K] [IsUltrametricDist K] (ψ : AddChar K ℂ)
    (hc : Continuous ψ) : ∃ δ > 0, ∀ x : K, ‖x‖ < δ → ψ x = 1 := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 (hc.continuousAt (x := 0)) (1 / 2) (by norm_num)
  refine ⟨δ, hδ, fun x hx => eq_one_of_pow_close fun n => ?_⟩
  have := h (x := n • x) (by
    rw [dist_zero_right]; exact (IsUltrametricDist.norm_nsmul_le x n).trans_lt hx)
  rwa [AddChar.map_zero_eq_one, dist_eq_norm, AddChar.map_nsmul_eq_pow] at this

theorem mem_of_separates {Q : Type} [AddCommGroup Q] [Finite Q] (H : AddSubgroup (AddChar Q ℂ))
    (h : ∀ x : Q, x ≠ 0 → ∃ χ ∈ H, χ x ≠ 1) (χ : AddChar Q ℂ) : χ ∈ H := by
  by_contra hχ
  have h0 : (QuotientAddGroup.mk χ : AddChar Q ℂ ⧸ H) ≠ 0 := fun e => hχ ((QuotientAddGroup.eq_zero_iff _).1 e)
  obtain ⟨Λ, hΛ⟩ := AddChar.exists_apply_ne_zero.2 h0
  obtain ⟨x, hx⟩ := (AddChar.doubleDualEquiv (α := Q)).surjective (Λ.compAddMonoidHom (QuotientAddGroup.mk' H))
  have hev : ∀ φ : AddChar Q ℂ, φ x = Λ (QuotientAddGroup.mk φ) := fun φ => DFunLike.congr_fun hx φ
  by_cases hx0 : x = 0
  · exact hΛ (by rw [← hev, hx0, AddChar.map_zero_eq_one])
  · obtain ⟨φ, hφ, hφx⟩ := h x hx0
    exact hφx (by rw [hev, (QuotientAddGroup.eq_zero_iff _).2 hφ, AddChar.map_zero_eq_one])

theorem exists_lift {G : Type} [AddCommGroup G] (N : AddSubgroup G) (φ : AddChar G ℂ)
    (hφ : ∀ x ∈ N, φ x = 1) : ∃ Λ : AddChar (G ⧸ N) ℂ, ∀ x : G, Λ x = φ x := by
  refine ⟨⟨Quotient.lift φ fun a b hab => ?_, φ.map_zero_eq_one, ?_⟩, fun x => rfl⟩
  · have := hφ _ (QuotientAddGroup.leftRel_apply.1 hab)
    rw [← add_neg_cancel_left a b, AddChar.map_add_eq_mul, this, mul_one]
  · rintro ⟨a⟩ ⟨b⟩
    exact φ.map_add_eq_mul a b

end GlobalTheory.CompactCharDual

namespace GlobalTheory.CompactCharDual

theorem exists_dotProduct_eq {K : Type} [NormedField K] [IsUltrametricDist K] {κ : Type} [Fintype κ]
    (ψ₀ : AddChar K ℂ) (hc : Continuous ψ₀) (hne : ψ₀ ≠ 1)
    (L : AddSubgroup (κ → K)) (hL : IsCompact (L : Set (κ → K)))
    (L' : AddSubgroup (κ → K)) (hL' : IsOpen (L' : Set (κ → K)))
    (χ : (κ → K) → ℂ) (hmul : ∀ y ∈ L, ∀ y' ∈ L, χ (y + y') = χ y * χ y') (htriv : ∀ y ∈ L, y ∈ L' → χ y = 1) :
    ∃ x₀ : κ → K, ∀ y ∈ L, χ y = ψ₀ (x₀ ⬝ᵥ y) := by
  classical
  obtain ⟨δ, hδ, hψδ⟩ := exists_ball_ker ψ₀ hc
  obtain ⟨r, hr, hrL'⟩ := Metric.isOpen_iff.1 hL' 0 L'.zero_mem
  obtain ⟨t₁, ht₁⟩ : ∃ t, ψ₀ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (DFunLike.ext _ _ fun t => by rw [h t, AddChar.one_apply])
  have ht0 : 0 < ‖t₁‖ := norm_pos_iff.2 fun h => ht₁ (by rw [h, AddChar.map_zero_eq_one])
  set ρ := ‖t₁‖ / r with hρ
  have hρ0 : 0 < ρ := div_pos ht0 hr
  set η := min r (δ / ρ) with hη
  have hη0 : 0 < η := lt_min hr (div_pos hδ hρ0)

  have small : ∀ a y : κ → K, ‖a‖ ≤ ρ → ‖y‖ < η → ψ₀ (a ⬝ᵥ y) = 1 := by
    intro a y ha hy
    have key : ∀ s : Finset κ, (∀ i ∈ s, ψ₀ (a i * y i) = 1) → ψ₀ (∑ i ∈ s, a i * y i) = 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro _; simp
      | insert i s hi ih =>
        intro hf
        rw [Finset.sum_insert hi, AddChar.map_add_eq_mul, hf i (Finset.mem_insert_self _ _),
          ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)), one_mul]
    show ψ₀ (∑ i, a i * y i) = 1
    refine key Finset.univ fun i _ => hψδ _ ?_
    rw [norm_mul]
    have h1 : ‖a i‖ ≤ ρ := (norm_le_pi_norm a i).trans ha
    have h2 : ‖y i‖ < δ / ρ := ((norm_le_pi_norm y i).trans_lt hy).trans_le (min_le_right _ _)
    calc ‖a i‖ * ‖y i‖ ≤ ρ * ‖y i‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ < ρ * (δ / ρ) := mul_lt_mul_of_pos_left h2 hρ0
      _ = δ := mul_div_cancel₀ _ hρ0.ne'
  let M : AddSubgroup (κ → K) :=
    { carrier := {y | ∀ a : κ → K, ‖a‖ ≤ ρ → ψ₀ (a ⬝ᵥ y) = 1}
      add_mem' := fun {y y'} hy hy' a ha => by
        rw [dotProduct_add, AddChar.map_add_eq_mul, hy a ha, hy' a ha, mul_one]
      zero_mem' := fun a _ => by rw [dotProduct_zero, AddChar.map_zero_eq_one]
      neg_mem' := fun {y} hy a ha => by
        rw [dotProduct_neg, ← neg_dotProduct]
        exact hy (-a) (by rwa [norm_neg]) }
  have hMmem : ∀ y, y ∈ M ↔ ∀ a : κ → K, ‖a‖ ≤ ρ → ψ₀ (a ⬝ᵥ y) = 1 := fun y => Iff.rfl

  have hML' : ∀ y ∈ M, y ∈ L' := by
    intro y hy
    refine hrL' (mem_ball_zero_iff.2 ?_)
    rw [pi_norm_lt_iff hr]
    intro k
    by_contra hk
    push_neg at hk
    have hyk : 0 < ‖y k‖ := hr.trans_le hk
    refine ht₁ ?_
    have hnorm : ‖(Pi.single k (t₁ / y k) : κ → K)‖ ≤ ρ := by
      refine (pi_norm_le_iff_of_nonneg hρ0.le).2 fun i => ?_
      by_cases hi : i = k
      · subst hi
        rw [Pi.single_eq_same, norm_div]
        exact div_le_div_of_nonneg_left ht0.le hr hk
      · rw [Pi.single_eq_of_ne hi, norm_zero]; exact hρ0.le
    have := (hMmem y).1 hy _ hnorm
    rwa [single_dotProduct, div_mul_cancel₀ _ (norm_pos_iff.1 hyk)] at this

  let U : AddSubgroup (κ → K) :=
    { carrier := Metric.ball 0 η
      add_mem' := fun {a b} ha hb => mem_ball_zero_iff.2
        ((IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt (mem_ball_zero_iff.1 ha) (mem_ball_zero_iff.1 hb)))
      zero_mem' := Metric.mem_ball_self hη0
      neg_mem' := fun {a} ha => by simpa using ha }
  have hUM : U ≤ M := fun y hy a ha => small a y ha (mem_ball_zero_iff.1 hy)
  let N : AddSubgroup L := M.addSubgroupOf L
  have hNo : IsOpen (N : Set L) := by
    refine AddSubgroup.isOpen_mono (H₁ := U.addSubgroupOf L)
      (fun y hy => AddSubgroup.mem_addSubgroupOf.2 (hUM (AddSubgroup.mem_addSubgroupOf.1 hy))) ?_
    exact (Metric.isOpen_ball (x := (0 : κ → K)) (ε := η)).preimage continuous_subtype_val
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hL
  haveI : Finite (L ⧸ N) := AddSubgroup.quotient_finite_of_isOpen N hNo

  let e : (κ → K) → AddChar L ℂ := fun a =>
    { toFun := fun y => ψ₀ (a ⬝ᵥ (y : κ → K))
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun y y' => by
        rw [AddSubgroup.coe_add, dotProduct_add, AddChar.map_add_eq_mul] }
  have he : ∀ a (y : L), e a y = ψ₀ (a ⬝ᵥ (y : κ → K)) := fun _ _ => rfl
  have hχ0 : χ 0 = 1 := htriv 0 L.zero_mem L'.zero_mem
  let χL : AddChar L ℂ :=
    { toFun := fun y => χ y
      map_zero_eq_one' := hχ0
      map_add_eq_mul' := fun y y' => hmul _ y.2 _ y'.2 }
  obtain ⟨X, hX⟩ := exists_lift N χL fun y hy => htriv _ y.2 (hML' _ hy)
  let H : AddSubgroup (AddChar (L ⧸ N) ℂ) :=
    { carrier := {Λ | ∃ a : κ → K, ‖a‖ ≤ ρ ∧ ∀ y : L, Λ y = ψ₀ (a ⬝ᵥ (y : κ → K))}
      add_mem' := by
        rintro Λ Λ' ⟨a, ha, h⟩ ⟨b, hb, h'⟩
        refine ⟨a + b, (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb), fun y => ?_⟩
        rw [AddChar.add_apply, h, h', add_dotProduct, AddChar.map_add_eq_mul]
      zero_mem' := ⟨0, by rw [norm_zero]; exact hρ0.le, fun y => by simp⟩
      neg_mem' := by
        rintro Λ ⟨a, ha, h⟩
        refine ⟨-a, by rwa [norm_neg], fun y => ?_⟩
        rw [AddChar.neg_apply, ← QuotientAddGroup.mk_neg, h, AddSubgroup.coe_neg, dotProduct_neg, neg_dotProduct] }
  have hsep : ∀ q : L ⧸ N, q ≠ 0 → ∃ Λ ∈ H, Λ q ≠ 1 := by
    intro q hq
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    have hyN : (y : κ → K) ∉ M := fun h => hq ((QuotientAddGroup.eq_zero_iff _).2 h)
    rw [hMmem] at hyN
    push_neg at hyN
    obtain ⟨a, ha, hay⟩ := hyN
    obtain ⟨Λ, hΛ⟩ := exists_lift N (e a) fun z hz => hz a ha
    exact ⟨Λ, ⟨a, ha, fun z => hΛ z⟩, by rw [hΛ]; exact hay⟩
  obtain ⟨a, -, ha⟩ := mem_of_separates H hsep X
  exact ⟨a, fun y hy => (hX ⟨y, hy⟩).symm.trans (ha ⟨y, hy⟩)⟩

end GlobalTheory.CompactCharDual

namespace GlobalTheory.CompactCharDual

theorem exists_dotProduct_eq_local : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ψ₀ ≠ 1 →
    ∀ L : AddSubgroup (κ → Fv F v), IsCompact (L : Set (κ → Fv F v)) →
    ∀ L' : AddSubgroup (κ → Fv F v), IsOpen (L' : Set (κ → Fv F v)) →
    ∀ χ : (κ → Fv F v) → ℂ, (∀ y ∈ L, ∀ y' ∈ L, χ (y + y') = χ y * χ y') → (∀ y ∈ L, y ∈ L' → χ y = 1) →
    ∃ x₀ : κ → Fv F v, ∀ y ∈ L, χ y = ψ₀ (x₀ ⬝ᵥ y) := by
  intro F _ _ v κ _ ψ₀ hc hne L hL L' hL' χ hmul htriv
  haveI : IsUltrametricDist (Fv F v) := inferInstance
  exact exists_dotProduct_eq ψ₀ hc hne L hL L' hL' χ hmul htriv

end GlobalTheory.CompactCharDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDotProductRepresentationCompactCharacterLoStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dotProduct_representation_compact_character_local : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ψ₀ ≠ 1 →
    ∀ L : AddSubgroup (κ → Fv F v), IsCompact (L : Set (κ → Fv F v)) →
    ∀ L' : AddSubgroup (κ → Fv F v), IsOpen (L' : Set (κ → Fv F v)) →
    ∀ χ : (κ → Fv F v) → ℂ, (∀ y ∈ L, ∀ y' ∈ L, χ (y + y') = χ y * χ y') → (∀ y ∈ L, y ∈ L' → χ y = 1) →
    ∃ x₀ : κ → Fv F v, ∀ y ∈ L, χ y = ψ₀ (x₀ ⬝ᵥ y) := by
  first | exact @GlobalTheory.CompactCharDual.exists_dotProduct_eq_local | exact GlobalTheory.CompactCharDual.exists_dotProduct_eq_local | (intros; apply GlobalTheory.CompactCharDual.exists_dotProduct_eq_local <;> assumption)
end

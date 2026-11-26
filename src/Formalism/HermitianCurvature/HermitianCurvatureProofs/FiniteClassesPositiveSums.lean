module

public import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces
public import Formalism.HermitianCurvature.StatementTB

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteClassesPositiveSums
noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology Finset
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums

section gen

variable {α : Type}

theorem psd_congr {F : Finset α} {k k' : α → α → ℂ} (h : IsPSD F k)
    (e : ∀ x ∈ F, ∀ y ∈ F, k x y = k' x y) : IsPSD F k' := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y = ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y :=
    sum_congr rfl fun x hx => sum_congr rfl fun y hy => by rw [e x hx y hy]
  rw [this]; exact h a

theorem psd_zero (F : Finset α) : IsPSD F (fun _ _ => (0 : ℂ)) := by
  intro a; simp

theorem psd_add {F : Finset α} {k k' : α → α → ℂ} (h : IsPSD F k) (h' : IsPSD F k') :
    IsPSD F (fun x y => k x y + k' x y) := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * (k x y + k' x y) =
      ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y + ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y := by
    simp only [mul_add, sum_add_distrib]
  rw [this, Complex.add_im, Complex.add_re, (h a).1, (h' a).1]
  exact ⟨by simp, add_nonneg (h a).2 (h' a).2⟩

theorem psd_sum {ι : Type} {F : Finset α} (s : Finset ι) (k : ι → α → α → ℂ)
    (h : ∀ i ∈ s, IsPSD F (k i)) : IsPSD F (fun x y => ∑ i ∈ s, k i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using psd_zero F
  | insert i s hi ih =>
    have := psd_add (h i (mem_insert_self i s)) (ih fun j hj => h j (mem_insert_of_mem hj))
    exact psd_congr this fun x _ y _ => by rw [sum_insert hi]

end gen

section classes

variable {K : Type} [CommRing K] (R : Subring K)

theorem out_mk (x : K) :
    ∃ r ∈ R, (Quotient.out ((x : K) : K ⧸ R.toAddSubgroup) : K) = x + r := by
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add R.toAddSubgroup x
  exact ⟨r.1, r.2, hr⟩

theorem periodic_out {β : Type} (f : K → β) (h1 : ∀ x, ∀ r ∈ R, f (x + r) = f x) (x : K) :
    f (Quotient.out ((x : K) : K ⧸ R.toAddSubgroup)) = f x := by
  obtain ⟨r, hr, e⟩ := out_mk R x
  rw [e, h1 x r hr]

theorem finite_classes [TopologicalSpace K] [IsTopologicalRing K] (hR : IsOpen (R : Set K))
    (Lc : Set K) (hLc : IsCompact Lc) :
    {y : K ⧸ R.toAddSubgroup | (Quotient.out y : K) ∈ Lc}.Finite := by
  have : DiscreteTopology (K ⧸ R.toAddSubgroup) := QuotientAddGroup.discreteTopology hR
  have h := (hLc.image (QuotientAddGroup.continuous_mk (N := R.toAddSubgroup))).finite_of_discrete
  refine h.subset ?_
  intro y hy
  exact ⟨Quotient.out y, hy, Quotient.out_eq' y⟩

variable {R} {F : Finset (Point K)} {Lc : Set K} {S : Finset (K ⧸ R.toAddSubgroup)}

theorem finsum_classes (hS : ∀ y : K ⧸ R.toAddSubgroup, (Quotient.out y : K) ∈ Lc → y ∈ S)
    {Θ : K → Point K → Point K → ℂ}
    (h3 : ∀ x, x ∉ Lc → ∀ h ∈ F, ∀ h' ∈ F, Θ x h h' = 0) {h h' : Point K} (hh : h ∈ F)
    (hh' : h' ∈ F) :
    ∑ᶠ y : K ⧸ R.toAddSubgroup, Θ (Quotient.out y) h h' = ∑ y ∈ S, Θ (Quotient.out y) h h' := by
  apply finsum_eq_sum_of_support_subset
  intro y hy
  by_contra hyS
  exact hy (h3 _ (fun hc => hyS (hS y hc)) h hh h' hh')

theorem psd_single (hS : ∀ y : K ⧸ R.toAddSubgroup, (Quotient.out y : K) ∈ Lc → y ∈ S)
    {M : Point K → Point K → ℂ} {Θ : K → Point K → Point K → ℂ}
    (h1 : ∀ x, ∀ r ∈ R, Θ (x + r) = Θ x) (h2 : ∀ x, IsPSD F (Θ x))
    (h3 : ∀ x, x ∉ Lc → ∀ h ∈ F, ∀ h' ∈ F, Θ x h h' = 0)
    (h5 : IsPSD F (fun h h' => M h h' - ∑ᶠ y : K ⧸ R.toAddSubgroup, Θ (Quotient.out y) h h'))
    (x : K) : IsPSD F (fun h h' => M h h' - Θ x h h') := by
  classical
  have key := psd_add h5 (psd_sum (S.erase ((x : K) : K ⧸ R.toAddSubgroup))
    (fun y => Θ (Quotient.out y)) (fun y _ => h2 _))
  refine psd_congr key ?_
  intro h hh h' hh'
  have e1 := finsum_classes hS h3 hh hh'
  have e2 : Θ (Quotient.out ((x : K) : K ⧸ R.toAddSubgroup)) = Θ x := periodic_out R Θ h1 x
  simp only [e1]
  by_cases hx : ((x : K) : K ⧸ R.toAddSubgroup) ∈ S
  · rw [← add_sum_erase S (fun y => Θ (Quotient.out y) h h') hx, e2]
    ring
  · rw [erase_eq_of_notMem hx]
    have : Θ x h h' = 0 := by
      rw [← e2]
      exact h3 _ (fun hc => hx (hS _ hc)) h hh h' hh'
    rw [this]; ring

theorem limit_core (hEntry : PSDEntryBound) (hSubseq : BoundedSubseq)
    (hS : ∀ y : K ⧸ R.toAddSubgroup, (Quotient.out y : K) ∈ Lc → y ∈ S)
    (M : Point K → Point K → ℂ) (Th : ℕ → K → Point K → Point K → ℂ)
    (h1 : ∀ j x, ∀ r ∈ R, Th j (x + r) = Th j x) (h2 : ∀ j x, IsPSD F (Th j x))
    (h3 : ∀ j x, x ∉ Lc → ∀ h ∈ F, ∀ h' ∈ F, Th j x h h' = 0)
    (h5 : ∀ j, IsPSD F (fun h h' => M h h' -
      ∑ᶠ y : K ⧸ R.toAddSubgroup, Th j (Quotient.out y) h h')) :
    ∃ (φ : ℕ → ℕ) (Θ : K → Point K → Point K → ℂ), StrictMono φ ∧
      (∀ x, ∀ r ∈ R, Θ (x + r) = Θ x) ∧
      ∀ x, ∀ h ∈ F, ∀ h' ∈ F, Tendsto (fun j => Th (φ j) x h h') atTop (𝓝 (Θ x h h')) := by
  classical
  let T : Finset ((K ⧸ R.toAddSubgroup) × Point K × Point K) := S ×ˢ F ×ˢ F
  let θ : ℕ → T → ℂ := fun j i => Th j (Quotient.out i.1.1) i.1.2.1 i.1.2.2
  let B : ℝ := ∑ h ∈ F, |(M h h).re|
  have hB0 : 0 ≤ B := sum_nonneg fun _ _ => abs_nonneg _
  have hBh : ∀ h ∈ F, |(M h h).re| ≤ B := fun h hh =>
    single_le_sum (f := fun h => |(M h h).re|) (fun _ _ => abs_nonneg _) hh
  have hb : ∀ j i, ‖θ j i‖ ≤ B := by
    rintro j ⟨⟨y, h, h'⟩, hi⟩
    simp only [T, mem_product] at hi
    have hE := hEntry _ F (Th j (Quotient.out y)) M (h2 j _)
      (psd_single hS (h1 j) (h2 j) (h3 j) (h5 j) _) h hi.2.1 h' hi.2.2
    have hle : (M h h).re * (M h' h').re ≤ B ^ 2 := by
      calc (M h h).re * (M h' h').re ≤ |(M h h).re * (M h' h').re| := le_abs_self _
        _ = |(M h h).re| * |(M h' h').re| := abs_mul _ _
        _ ≤ B * B := mul_le_mul (hBh h hi.2.1) (hBh h' hi.2.2) (abs_nonneg _) hB0
        _ = B ^ 2 := (sq B).symm
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB0 two_ne_zero).1 (hE.trans hle)
  obtain ⟨φ, l, hφ, hl⟩ := hSubseq T θ B hb
  refine ⟨φ, fun x h h' => if hx : (((x : K) : K ⧸ R.toAddSubgroup), h, h') ∈ T then l ⟨_, hx⟩
    else 0, hφ, ?_, ?_⟩
  · intro x r hr
    have e : (((x + r : K)) : K ⧸ R.toAddSubgroup) = ((x : K) : K ⧸ R.toAddSubgroup) := by
      rw [QuotientAddGroup.eq]
      have : -(x + r) + x = -r := by ring
      rw [this]
      exact neg_mem hr
    funext h h'
    simp only [e]
  · intro x h hh h' hh'
    have e2 : ∀ j, Th j (Quotient.out ((x : K) : K ⧸ R.toAddSubgroup)) = Th j x :=
      fun j => periodic_out R (Th j) (h1 j) x
    by_cases hx : (((x : K) : K ⧸ R.toAddSubgroup), h, h') ∈ T
    · simp only [dif_pos hx]
      have := hl ⟨_, hx⟩
      simp only [θ, e2] at this
      exact this
    · simp only [dif_neg hx]
      have hxS : ((x : K) : K ⧸ R.toAddSubgroup) ∉ S := by
        intro hc
        exact hx (by simp only [T, mem_product]; exact ⟨hc, hh, hh'⟩)
      have : ∀ j, Th (φ j) x h h' = 0 := by
        intro j
        rw [← e2]
        exact h3 _ _ (fun hc => hxS (hS _ hc)) h hh h' hh'
      simp only [this]
      exact tendsto_const_nhds

end classes

end Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.FiniteClassesPositiveSums

theorem thetaExistsStepOfSteps : Formalism.FourierDecayAlt.A6.ThetaExistenceInductive := by
  intro hThOm hSupp hNsS hCOne hExh _hLF hEntry hClosed hSubseq hA2 hN1 K _ _ _ R ψ hD hch s hs hAt
    n₀ F hF
  classical
  obtain ⟨Lc, hcut, hGL⟩ := hSupp hNsS K R ψ hD (s + 1) F (by omega)
  obtain ⟨Om, hOm, hmono, hex⟩ := hExh K R ψ hD hch (s + 1) (by omega)
  choose Th hTh using fun j => hThOm hA2 hN1 K R ψ hD hch s hs hAt n₀ F Lc (Om j) hF hcut (hOm j)
  obtain ⟨hLo, hLk, -, -⟩ := hcut
  have hfin := finite_classes R hD.isOpen (Lc : Set K) hLk
  have hS : ∀ y : K ⧸ R.toAddSubgroup, (Quotient.out y : K) ∈ (Lc : Set K) → y ∈ hfin.toFinset :=
    fun y hy => hfin.mem_toFinset.2 hy
  let M : Point K → Point K → ℂ := fun h h' =>
    ((cSize R h ^ (s + 1) * cSize R h' ^ (s + 1) : ℝ) : ℂ) * N0 R ψ h h'
  obtain ⟨φ, Θ, hφ, h1, hlim⟩ := limit_core hEntry hSubseq hS M Th (fun j => (hTh j).1)
    (fun j => (hTh j).2.1) (fun j => (hTh j).2.2.1) (fun j => (hTh j).2.2.2.2.1)
  have h2 : ∀ x, IsPSD F (Θ x) := fun x =>
    hClosed _ F (fun j => Th (φ j) x) (Θ x) (fun j => (hTh _).2.1 x) (hlim x)
  have h3 : ∀ x, x ∉ (Lc : Set K) → ∀ h ∈ F, ∀ h' ∈ F, Θ x h h' = 0 := by
    intro x hx h hh h' hh'
    have := hlim x h hh h' hh'
    simp only [(hTh _).2.2.1 x hx h hh h' hh'] at this
    exact tendsto_nhds_unique tendsto_const_nhds this |>.symm
  have h4 : ∀ t : Kˣ, IsPSD F (fun h h' => Θ (t : K) h h' - Ns R ψ (s + 1) h h' t t) := by
    intro t
    obtain ⟨j0, hj0⟩ := hex t
    have hmono' : ∀ j, j0 ≤ j → (t : K) ∈ Om j := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => exact hj0
      | succ j _ ih => exact hmono j ih
    refine hClosed _ F (fun j h h' => Th (φ (j + j0)) (t : K) h h' - Ns R ψ (s + 1) h h' t t) _
      (fun j => (hTh _).2.2.2.1 t (hmono' _ ((Nat.le_add_left _ _).trans hφ.le_apply))) ?_
    intro h hh h' hh'
    exact ((hlim (t : K) h hh h' hh').comp (tendsto_add_atTop_nat j0)).sub tendsto_const_nhds
  have h5 : IsPSD F (fun h h' => M h h' -
      ∑ᶠ y : K ⧸ R.toAddSubgroup, Θ (Quotient.out y) h h') := by
    refine hClosed _ F (fun j h h' => M h h' -
      ∑ᶠ y : K ⧸ R.toAddSubgroup, Th (φ j) (Quotient.out y) h h') _
      (fun j => (hTh _).2.2.2.2.1) ?_
    intro h hh h' hh'
    simp only [finsum_classes hS h3 hh hh', finsum_classes hS ((hTh _).2.2.1) hh hh']
    exact tendsto_const_nhds.sub (tendsto_finsetSum _ fun y _ => hlim _ h hh h' hh')
  have h6 : ∀ x, ∀ h ∈ F, ∀ h' ∈ F, modK R (pt h.1 h.2).det ≠ modK R (pt h'.1 h'.2).det →
      Θ x h h' = 0 := by
    intro x h hh h' hh' hne
    have := hlim x h hh h' hh'
    simp only [(hTh _).2.2.2.2.2 x h hh h' hh' hne] at this
    exact tendsto_nhds_unique tendsto_const_nhds this |>.symm
  refine ⟨Θ, h1, h2, ⟨Lc, hLo, hLk, h3⟩, h4, h5, h6, ?_⟩
  intro hG x
  by_cases hx : x ∈ R
  · simp only [if_pos hx]
    refine psd_congr (psd_single hS h1 h2 h3 h5 x) ?_
    intro h hh h' hh'
    simp only [M, hCOne K R ψ hD h (hG h hh), hCOne K R ψ hD h' (hG h' hh')]
    simp
  · simp only [if_neg hx]
    refine psd_congr (psd_zero F) ?_
    intro h hh h' hh'
    rw [h3 x (fun hc => hx ((hGL hG x).1 hc)) h hh h' hh']
    simp

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeanNormSquaredBound
noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace MeanNormSquaredBound

section Abstract

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma inner_sum_sum {ι κ : Type} (S : Finset ι) (S' : Finset κ) (c : ι → ℂ) (d : κ → ℂ)
    (v : ι → E) (v' : κ → E) :
    inner ℂ (∑ j ∈ S', d j • v' j) (∑ i ∈ S, c i • v i) =
      ∑ i ∈ S, ∑ j ∈ S', c i * conj (d j) * inner ℂ (v' j) (v i) := by
  rw [inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

lemma normSq_sum {ι : Type} (S : Finset ι) (c : ι → ℂ) (v : ι → E) :
    ((‖∑ i ∈ S, c i • v i‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, c i * conj (c j) * inner ℂ (v j) (v i) := by
  rw [← inner_sum_sum, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

lemma sum_sum_sum_sum_comm {α β M : Type} [AddCommMonoid M] (P : Finset α) (H : Finset β)
    (f : α → α → β → β → M) :
    ∑ p ∈ P, ∑ p' ∈ P, ∑ h ∈ H, ∑ h' ∈ H, f p p' h h' =
      ∑ h ∈ H, ∑ h' ∈ H, ∑ p ∈ P, ∑ p' ∈ P, f p p' h h' := by
  calc ∑ p ∈ P, ∑ p' ∈ P, ∑ h ∈ H, ∑ h' ∈ H, f p p' h h'
      = ∑ p ∈ P, ∑ h ∈ H, ∑ p' ∈ P, ∑ h' ∈ H, f p p' h h' :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ h ∈ H, ∑ p ∈ P, ∑ p' ∈ P, ∑ h' ∈ H, f p p' h h' := Finset.sum_comm
    _ = ∑ h ∈ H, ∑ p ∈ P, ∑ h' ∈ H, ∑ p' ∈ P, f p p' h h' :=
        Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ h ∈ H, ∑ h' ∈ H, ∑ p ∈ P, ∑ p' ∈ P, f p p' h h' :=
        Finset.sum_congr rfl fun h _ => Finset.sum_comm

lemma normSq_mean {X α : Type} (L : E →ₗ[ℂ] E) (k : ℂ) (hk : conj k = k) (P : Finset α)
    (c : α → ℂ) (F : Finset X) (a : X → ℂ) (u : X → α → E) :
    ((‖L (k • ∑ p ∈ P, c p • ∑ h ∈ F, a h • u h p)‖ ^ 2 : ℝ) : ℂ) =
      ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
        (k ^ 2 * ∑ p ∈ P, ∑ p' ∈ P, c p * conj (c p') * inner ℂ (L (u h' p')) (L (u h p))) := by
  have h1 : L (k • ∑ p ∈ P, c p • ∑ h ∈ F, a h • u h p) =
      ∑ p ∈ P, (k * c p) • ∑ h ∈ F, a h • L (u h p) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, Finset.smul_sum, smul_smul, mul_assoc]
  rw [h1, normSq_sum]
  simp only [inner_sum_sum, Finset.mul_sum]
  rw [sum_sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ =>
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
  rw [map_mul, hk]
  ring

lemma sum_sub_prod {α β M : Type} [AddCommMonoid M] (A : Finset α) (B : Finset β)
    (f : α × β → M) : ∑ p : ↥A × ↥B, f (p.1.1, p.2.1) = ∑ p ∈ A ×ˢ B, f p := by
  rw [Fintype.sum_prod_type, Finset.sum_product, ← Finset.sum_coe_sort A]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [← Finset.sum_coe_sort B]

lemma abstract_bound (AB : AvgBound) {X Y : Type} (F : Finset X) (a : X → ℂ) (A B : Finset Y)
    (u : X → Y × Y → E) (T : E →ₗ[ℂ] E) (hT : ∀ v, ‖T v‖ ≤ ‖v‖) (e₁ e₂ : Y → ℂ)
    (he₁ : ∀ ρ ∈ A, ‖e₁ ρ‖ = 1)
    (horth : ∀ h ∈ F, ∀ h' ∈ F, ∀ ρ ∈ A, ∀ ρ' ∈ A, ∀ b ∈ B, ∀ b' ∈ B, ρ ≠ ρ' →
      inner ℂ (u h (ρ, b)) (u h' (ρ', b')) = 0) :
    ∃ r₁ r₂ : ℝ, r₁ ≤ r₂ ∧
      (r₁ : ℂ) = ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
        ((((A.card : ℂ) * (B.card : ℂ))⁻¹) ^ 2 * ∑ p ∈ A ×ˢ B, ∑ p' ∈ A ×ˢ B,
          (e₁ p.1 * e₂ p.2) * conj (e₁ p'.1 * e₂ p'.2) * inner ℂ (T (u h' p')) (T (u h p))) ∧
      (r₂ : ℂ) = ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
        ((A.card : ℂ)⁻¹ * ((A.card : ℂ)⁻¹ * ∑ ρ ∈ A, ((B.card : ℂ)⁻¹) ^ 2 * ∑ b ∈ B, ∑ b' ∈ B,
          e₂ b * conj (e₂ b') * inner ℂ (u h' (ρ, b')) (u h (ρ, b)))) := by
  set w : Y × Y → E := fun p => ∑ h ∈ F, a h • u h p with hw
  have key := AB E ↥A ↥B (fun p => w (p.1.1, p.2.1)) T (fun ρ => e₁ ρ.1) (fun b => e₂ b.1) hT
    (fun ρ => he₁ ρ.1 ρ.2) (by
      intro ρ ρ' b b' hne
      have hne' : ρ.1 ≠ ρ'.1 := fun h => hne (Subtype.ext h)
      simp only [hw]
      rw [inner_sum_sum]
      refine Finset.sum_eq_zero fun h hh => Finset.sum_eq_zero fun h' hh' => ?_
      rw [horth h' hh' h hh ρ.1 ρ.2 ρ'.1 ρ'.2 b.1 b.2 b'.1 b'.2 hne', mul_zero])
  simp only [Fintype.card_coe] at key
  have e1 : (∑ p : ↥A × ↥B, (e₁ p.1.1 * e₂ p.2.1) • w (p.1.1, p.2.1)) =
      ∑ p ∈ A ×ˢ B, (e₁ p.1 * e₂ p.2) • w p :=
    sum_sub_prod A B (fun p => (e₁ p.1 * e₂ p.2) • w p)
  have e2 : (∑ ρ : ↥A, ‖(B.card : ℂ)⁻¹ • ∑ b : ↥B, e₂ b.1 • w (ρ.1, b.1)‖ ^ 2) =
      ∑ ρ ∈ A, ‖(B.card : ℂ)⁻¹ • ∑ b ∈ B, e₂ b • w (ρ, b)‖ ^ 2 := by
    rw [← Finset.sum_coe_sort A]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [← Finset.sum_coe_sort B]
  rw [e1, e2] at key
  refine ⟨_, _, key, ?_, ?_⟩
  · exact normSq_mean T _ (by simp) (A ×ˢ B) (fun p => e₁ p.1 * e₂ p.2) F a u
  · have h3 : ∀ ρ, ((‖(B.card : ℂ)⁻¹ • ∑ b ∈ B, e₂ b • w (ρ, b)‖ ^ 2 : ℝ) : ℂ) =
        ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') * (((B.card : ℂ)⁻¹) ^ 2 * ∑ b ∈ B, ∑ b' ∈ B,
          e₂ b * conj (e₂ b') * inner ℂ (u h' (ρ, b')) (u h (ρ, b))) := fun ρ =>
      normSq_mean LinearMap.id _ (by simp) B e₂ F a (fun h b => u h (ρ, b))
    rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_sum]
    simp only [h3, Complex.ofReal_inv, Complex.ofReal_natCast]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h' _ => Finset.sum_congr rfl fun ρ _ =>
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    ring

end Abstract

lemma norm_psi {K : Type} [CommRing K] (ψ : AddChar K ℂ) (hu : ∀ x : K, conj (ψ x) = ψ (-x))
    (x : K) : ‖ψ x‖ = 1 := by
  have h1 : ψ x * conj (ψ x) = 1 := by
    rw [hu, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h1
  have h2 : ‖ψ x‖ ^ 2 = 1 := by exact_mod_cast h1
  have h3 : (‖ψ x‖ - 1) * (‖ψ x‖ + 1) = 0 := by ring_nf; rw [h2]; ring
  rcases mul_eq_zero.mp h3 with h | h
  · linarith
  · have := norm_nonneg (ψ x); linarith

end MeanNormSquaredBound

open MeanNormSquaredBound in
theorem thetaAverageLower : Formalism.FourierDecayAlt.A6.ThxLower := by
  intro GI A2V UGE ExponentialIntegralMeasures CSA MM CPSD KG GRC AB CNE CM PL K _ _ _ R ψ hD hchar m hm n₀ F Om Lc hF hOm D
  classical
  set Sg : Finset K := (D.A ×ˢ D.B).image (fun p => p.1 + p.2) with hSg
  have hLat : IsLat (perp ψ D.L₂) := (PL K R ψ hD hchar D.L₂ D.lat₂).1
  have hAL : ∀ ρ ∈ D.A, ρ ∈ D.L₂ := D.repsA.1
  have hBR : ∀ b ∈ D.B, b ∈ R.toAddSubgroup := D.repsB.1
  have hmemSg : ∀ ρ ∈ D.A, ∀ b ∈ D.B, ρ + b ∈ Sg := by
    intro ρ hρ b hb
    exact Finset.mem_image.mpr ⟨(ρ, b), Finset.mem_product.mpr ⟨hρ, hb⟩, rfl⟩
  have hSgL : ∀ σ ∈ Sg, σ ∈ D.L₂ := by
    intro σ hσ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hσ
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    exact D.L₂.add_mem (hAL _ hp1) (D.le₂ (hBR _ hp2))
  obtain ⟨V, hV, hGI⟩ := GI K R ψ hD hchar m hm n₀ F hF Om Sg (perp ψ D.L₂) hOm hLat D.omStable
    D.nsInv (by
      intro σ hσ σ' hσ' l hl
      exact hl _ (D.L₂.sub_mem (hSgL σ hσ) (hSgL σ' hσ')))
  refine ⟨V, hV, ?_⟩
  intro t τ cr ht hcr hsh z₁ hz₁ a

  set F' : Finset (Point K × Kˣ) := F ×ˢ Sg.image τ with hF'
  have hmemF' : ∀ h ∈ F, ∀ ρ ∈ D.A, ∀ b ∈ D.B, (h, τ (ρ + b)) ∈ F' := by
    intro h hh ρ hρ b hb
    exact Finset.mem_product.mpr ⟨hh, Finset.mem_image_of_mem τ (hmemSg ρ hρ b hb)⟩
  obtain ⟨hc1, hc2⟩ := CPSD KG ExponentialIntegralMeasures MM K R ψ hD m cr (cutSet m Om t) F' hcr (by
    intro p hp p' hp'
    rw [hF _ (Finset.mem_product.mp hp).1, hF _ (Finset.mem_product.mp hp').1])
  obtain ⟨n, u₀, T, hT, hG, hGc⟩ := GRC (Point K × Kˣ) F'
    (fun p p' => uGram R ψ m cr Set.univ p.1 p'.1 p.2 p'.2)
    (fun p p' => uGram R ψ m cr (cutSet m Om t) p.1 p'.1 p.2 p'.2) hc1 hc2

  obtain ⟨r₁, r₂, hr, hr₁, hr₂⟩ := abstract_bound AB F a D.A D.B
    (fun h p => u₀ (h, τ (p.1 + p.2))) T hT (fun ρ => ψ (-(z₁ * ρ))) (fun b => ψ (-(z₁ * b)))
    (fun ρ _ => norm_psi ψ hD.unitary _) (by
      intro h hh h' hh' ρ hρ ρ' hρ' b hb b' hb' hne
      simp only
      rw [hG _ (hmemF' h' hh' ρ' hρ' b' hb') _ (hmemF' h hh ρ hρ b hb)]
      simp only
      rw [UGE ExponentialIntegralMeasures CSA MM K R ψ hD m h' h _ _ cr (by rw [hF h hh, hF h' hh']) hcr]
      by_contra hcon
      have hNs : Ns R ψ m h' h (τ (ρ' + b')) (τ (ρ + b)) ≠ 0 := fun h0 => hcon (by rw [h0, mul_zero])
      have hmem := A2V K R ψ hD m hm h' h _ _ (by rw [hF h hh, hF h' hh']) hNs
      rw [hsh ρ' hρ' b' hb', hsh ρ hρ b hb] at hmem
      have h5 : ρ' - ρ ∈ R.toAddSubgroup := by
        have h6 : ρ' - ρ = (((t⁻¹ : Kˣ) : K) + (ρ' + b') - (((t⁻¹ : Kˣ) : K) + (ρ + b))) + (b - b') := by
          ring
        rw [h6]
        exact R.toAddSubgroup.add_mem hmem (R.toAddSubgroup.sub_mem (hBR b hb) (hBR b' hb'))
      obtain ⟨x, _, hx⟩ := D.repsA.2 ρ' (hAL ρ' hρ')
      have e1 := hx ρ ⟨hρ, h5⟩
      have e2 := hx ρ' ⟨hρ', by rw [sub_self]; exact R.toAddSubgroup.zero_mem⟩
      exact hne (e1.trans e2.symm))
  have hr₁' : (r₁ : ℂ) = ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
      ((D.A.card : ℂ)⁻¹ * NsK R ψ (m + 1) h h' z₁) := by
    rw [hr₁]
    refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun h' hh' => ?_
    congr 1
    rw [← CNE CM PL K R ψ hD hchar (m + 1) F Om Lc D hOm.2.1 z₁ hz₁ h hh h' hh']
    congr 1
    refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun p' hp' => ?_
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hp1', hp2'⟩ := Finset.mem_product.mp hp'
    rw [hGc _ (hmemF' h hh p.1 hp1 p.2 hp2) _ (hmemF' h' hh' p'.1 hp1' p'.2 hp2')]
    simp only
    rw [hGI t _ _ cr ht hcr _ (hmemSg p.1 hp1 p.2 hp2) _ (hmemSg p'.1 hp1' p'.2 hp2')
      (hsh p.1 hp1 p.2 hp2) (hsh p'.1 hp1' p'.2 hp2') h hh h' hh']
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    have q1 : -(z₁ * p.1) + -(z₁ * p.2) = -(z₁ * (p.1 + p.2)) := by ring
    have q2 : -(z₁ * p'.1) + -(z₁ * p'.2) = -(z₁ * (p'.1 + p'.2)) := by ring
    rw [q1, q2]
  have hr₂' : (r₂ : ℂ) = ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
      ((D.A.card : ℂ)⁻¹ * thx R ψ m cr D.A D.B τ z₁ h h') := by
    rw [hr₂]
    refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun h' hh' => ?_
    congr 2
    unfold thx
    congr 1
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    congr 1
    refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun b' hb' => ?_
    simp only
    rw [hG _ (hmemF' h hh ρ hρ b hb) _ (hmemF' h' hh' ρ hρ b' hb')]
  have hApos : 0 < (D.A.card : ℝ) := by
    obtain ⟨x, hx, _⟩ := D.repsA.2 0 D.L₂.zero_mem
    exact_mod_cast Finset.card_pos.mpr ⟨x, hx.1⟩
  have hAne : (D.A.card : ℂ) ≠ 0 := by
    exact_mod_cast hApos.ne'
  have hfin : ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
      (thx R ψ m cr D.A D.B τ z₁ h h' - NsK R ψ (m + 1) h h' z₁) =
      (((D.A.card : ℝ) * (r₂ - r₁) : ℝ) : ℂ) := by
    push_cast
    rw [hr₁', hr₂', ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h' _ => ?_
    field_simp
  rw [hfin]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  exact mul_nonneg hApos.le (sub_nonneg.mpr hr)

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.OneLevelCoefficients
namespace Formalism.FourierDecayAlt.P.OneLevelCoefficients

open Formalism.FourierDecayAlt.TB Finset
open scoped ComplexOrder

variable {E W : Type} [Field E]

lemma exists_reps (L : AddSubgroup E) (S : Finset E) :
    ∃ R : Finset E, (∀ t ∈ S, ∃ t₀ ∈ R, t - t₀ ∈ L) ∧
      (∀ t₀ ∈ R, ∀ t₀' ∈ R, t₀ - t₀' ∈ L → t₀ = t₀') := by
  classical
  have hout : ∀ t : E, (((t : E ⧸ L).out : E) : E ⧸ L) = (t : E ⧸ L) :=
    fun t => QuotientAddGroup.out_eq' _
  refine ⟨S.image (fun t : E => (QuotientAddGroup.mk t : E ⧸ L).out), ?_, ?_⟩
  · intro t ht
    refine ⟨_, Finset.mem_image_of_mem _ ht, ?_⟩
    rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_sub, hout, sub_self]
  · intro a ha b hb hab
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨t', _, rfl⟩ := Finset.mem_image.1 hb
    rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_sub, hout, hout, sub_eq_zero] at hab
    simp only [hab]

lemma budget_step (K r i s c m : ℕ) (hsi : s ≤ i) (hi : i ≤ r + 1)
    (hc : c ≤ 4 * K * (r + 1 - i)) (hm : m ≤ 4 * s) : c + m * K ≤ 4 * K * (r + 1 - (i - s)) := by
  have h1 : r + 1 - (i - s) = (r + 1 - i) + s := by omega
  have h2 : m * K ≤ 4 * K * s := by
    calc m * K ≤ 4 * s * K := Nat.mul_le_mul_right _ hm
      _ = 4 * K * s := by ring
  rw [h1, Nat.mul_add]
  exact Nat.add_le_add hc h2

lemma budget_top (K r i s c m : ℕ) (hsi : s ≤ i) (hi : i ≤ r + 1)
    (hc : c ≤ 4 * K * (r + 1 - i)) (hm : m ≤ 4 * s) : c + m * K ≤ 4 * K * (r + 1) :=
  (budget_step K r i s c m hsi hi hc hm).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

theorem oneLevel_of_steps : OneLevelOfSteps := by
  intro hSplit hSchur hDiag hOne hMulti E W _ D ep C₄ hG hKer hW hA2 hA13 hEW hP hEL hEB hLat hep
    h4 hv0 hv1 T ε hε σ i hi1 hi hσ w hw
  have hwW : w ∈ D.Wall := (Finset.mem_filter.1 hw).1
  have hwc : D.cnt w ≤ 4 * D.K * (D.r + 1 - i) := (Finset.mem_filter.1 hw).2
  have hwt : 0 < D.wt w := hW w
  have he : 0 ≤ D.e i := (hA13 i 1 le_rfl hi1 hi).1.1
  have ha0 : 0 ≤ 3 ^ D.f * ep := by positivity
  have hb0 : 0 ≤ 2 ^ D.f * ep := by positivity

  have hS : ∀ s, 1 ≤ s → s ≤ i → ∀ M : ℝ,
      (∀ w' ∈ D.Wb (D.cnt w + D.K), D.Dg T ε i s w' ≤ M) →
      D.Sf ε i w (Xs T i s) / D.wt w ≤ (1 + 3 ^ D.f * ep) * M := by
    intro s hs hsi M hM
    have hN : D.cnt w + D.K ≤ D.Ntop := by
      have := budget_top D.K D.r i s (D.cnt w) 1 hsi hi hwc (by omega)
      simpa [Data.Ntop] using this
    have h := hSchur E W D ep hG hKer hW hA2 hEL hLat T ε hε i s hs hsi hi w hwW hN M hM
    have h2 := hM w (Finset.mem_filter.2 ⟨hwW, Nat.le_add_right _ _⟩)
    calc D.Sf ε i w (Xs T i s) / D.wt w ≤ D.Dg T ε i s w + 3 ^ D.f * ep * M := h
      _ ≤ M + 3 ^ D.f * ep * M := by linarith
      _ = (1 + 3 ^ D.f * ep) * M := by ring

  have h1 : D.Sf ε i w (Xs T i 1) / D.wt w ≤
      (1 + 3 ^ D.f * ep) * ((1 + D.e i) * ((1 + 2 ^ D.f * ep) * σ (i - 1) ^ 2)) := by
    apply hS 1 le_rfl hi1
    intro w' hw'
    have hw'W : w' ∈ D.Wall := (Finset.mem_filter.1 hw').1
    have hw'c : D.cnt w' ≤ D.cnt w + D.K := (Finset.mem_filter.1 hw').2
    obtain ⟨R, hR1, hR2⟩ := exists_reps (D.La (i - 1 + 1) 1) (T.Sg (i - 1 + 1) 1)
    have hd := hDiag E W D hG hKer hW hA13 T ε hε i 1 le_rfl hi1 hi w' R hR1
    have hii : i - 1 + 1 = i := by omega
    rw [hii] at hd hR2
    have hT : D.cnt w + 2 * D.K ≤ 4 * D.K * (D.r + 1) :=
      budget_top D.K D.r i 1 (D.cnt w) 2 hi1 hi hwc (by omega)
    have hB : D.cnt w + 2 * D.K ≤ 4 * D.K * (D.r + 1 - (i - 1)) :=
      budget_step D.K D.r i 1 (D.cnt w) 2 hi1 hi hwc (by omega)
    have hN : D.cnt w' + D.K ≤ D.Ntop := by
      simp only [Data.Ntop]; omega
    have hlow : ∀ w'' ∈ D.Wb (D.cnt w' + D.K),
        D.N0 ε (i - 1) w'' (T.X (i - 1)) (D.Kr (i - 1)) ≤ σ (i - 1) ^ 2 := by
      intro w'' hw''
      refine (hσ (i - 1) (by omega)).2 w'' (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hw'').1, ?_⟩)
      have := (Finset.mem_filter.1 hw'').2
      simp only [Data.budget]; omega
    have ho := hOne E W D ep hG hKer hW hA13 hEW hP hLat T ε hε i hi1 hi w' hw'W hN R hR2
      (σ (i - 1) ^ 2) hlow
    have hw0 := hlow w' (Finset.mem_filter.2 ⟨hw'W, Nat.le_add_right _ _⟩)
    calc D.Dg T ε i 1 w' ≤ _ := hd
      _ ≤ _ := ho
      _ ≤ (1 + D.e i) * (σ (i - 1) ^ 2 + 2 ^ D.f * ep * σ (i - 1) ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = (1 + D.e i) * ((1 + 2 ^ D.f * ep) * σ (i - 1) ^ 2) := by ring

  have h2 : ∀ s, 2 ≤ s → s ≤ i → D.Sf ε i w (Xs T i s) / D.wt w ≤
      (1 + 3 ^ D.f * ep) * (C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') *
        ((1 + D.e i) * σ (i - s) ^ 2)) := by
    intro s hs hsi
    apply hS s (by omega) hsi
    intro w' hw'
    have hw'W : w' ∈ D.Wall := (Finset.mem_filter.1 hw').1
    have hw'c : D.cnt w' ≤ D.cnt w + D.K := (Finset.mem_filter.1 hw').2
    obtain ⟨R, hR1, hR2⟩ := exists_reps (D.La (i - s + 1) s) (T.Sg (i - s + 1) s)
    have hd := hDiag E W D hG hKer hW hA13 T ε hε i s (by omega) hsi hi w' R hR1
    have hT : D.cnt w + (s + 2) * D.K ≤ 4 * D.K * (D.r + 1) :=
      budget_top D.K D.r i s (D.cnt w) (s + 2) hsi hi hwc (by omega)
    have hB : D.cnt w + (s + 2) * D.K ≤ 4 * D.K * (D.r + 1 - (i - s)) :=
      budget_step D.K D.r i s (D.cnt w) (s + 2) hsi hi hwc (by omega)
    have hsK : (s + 2) * D.K = D.K + (s + 1) * D.K := by ring
    have hN : D.cnt w' + (s + 1) * D.K ≤ D.Ntop := by
      simp only [Data.Ntop]; omega
    have hlow : ∀ w'' ∈ D.Wb (D.cnt w' + (s + 1) * D.K),
        D.N0 ε (i - s) w'' (T.X (i - s)) (D.Kr (i - s)) ≤ σ (i - s) ^ 2 := by
      intro w'' hw''
      refine (hσ (i - s) (by omega)).2 w'' (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hw'').1, ?_⟩)
      have := (Finset.mem_filter.1 hw'').2
      simp only [Data.budget]; omega
    have hm := hMulti E W D C₄ hG hKer hW hA13 hEB h4 hv0 T ε hε i s hs hsi hi w' hw'W hN
      (hv1 _ _ (by omega) (by omega) (by omega)) R hR2 (σ (i - s) ^ 2) hlow
    exact hd.trans hm

  have hsplit := hSplit E W D hG hKer T ε hε i hi1 w
  have hIcc : Icc 1 i = insert 1 (Icc 2 i) := by
    ext s; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : (1 : ℕ) ∉ Icc 2 i := by simp
  have hfirst : √(D.Q T ε i w) ≤ ∑ s ∈ Icc 1 i, √(D.Sf ε i w (Xs T i s) / D.wt w) := by
    have : ∀ x : ℝ, √(x / D.wt w) = √x / √(D.wt w) := fun x => Real.sqrt_div' x hwt.le
    simp only [Data.Q, this, ← Finset.sum_div]
    exact div_le_div_of_nonneg_right hsplit (Real.sqrt_nonneg _)
  refine hfirst.trans ?_
  rw [hIcc, Finset.sum_insert hnot]
  apply add_le_add
  · have hσ0 : 0 ≤ σ (i - 1) := (hσ (i - 1) (by omega)).1
    refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
    have : (1 + 3 ^ D.f * ep) * ((1 + D.e i) * ((1 + 2 ^ D.f * ep) * σ (i - 1) ^ 2)) =
        (1 + 3 ^ D.f * ep) * (1 + 2 ^ D.f * ep) * (1 + D.e i) * σ (i - 1) ^ 2 := by ring
    rw [this, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hσ0,
      Real.sqrt_mul' _ (by linarith : 0 ≤ 1 + D.e i)]
  · apply Finset.sum_le_sum
    intro s hs
    rw [Finset.mem_Icc] at hs
    have hσ0 : 0 ≤ σ (i - s) := (hσ (i - s) (by omega)).1
    refine (Real.sqrt_le_sqrt (h2 s hs.1 hs.2)).trans (le_of_eq ?_)
    have : (1 + 3 ^ D.f * ep) * (C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') *
        ((1 + D.e i) * σ (i - s) ^ 2)) =
        (1 + 3 ^ D.f * ep) * (1 + D.e i) * C₄ ^ (D.f * s) *
          (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') * σ (i - s) ^ 2 := by ring
    rw [this, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hσ0]

lemma coef (D : Data E W) (Θ C₄ C₀ a e : ℝ) (hΘ : 1 ≤ Θ) (h4 : 1 ≤ C₄) (h0 : 2 * C₄ ≤ C₀)
    (hf : 1 ≤ D.f) (hS : D.SizesBelow Θ) (ha0 : 0 ≤ a) (ha : a ≤ 1) (_he0 : 0 ≤ e) (he : e ≤ 1)
    (i s : ℕ) (hs : 2 ≤ s) (hsi : s ≤ i) (hi : i ≤ D.r + 1) :
    √((1 + a) * (1 + e) * C₄ ^ (D.f * s) * ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') ≤
      ((C₀ / Θ) ^ D.f) ^ (s - 1) := by
  have hΘ0 : 0 < Θ := by linarith
  set q : ℝ := (Θ ^ D.f)⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  have hC0 : 0 ≤ C₀ := by linarith
  have hP : ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s' ≤ (q ^ 2) ^ (s - 1) := by
    calc ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s' ≤ ∏ _s' ∈ Ico 1 s, q ^ 2 := by
          apply Finset.prod_le_prod₀ (fun s' _ => hS.1 _ _)
          intro s' hs'
          rw [Finset.mem_Ico] at hs'
          exact hS.2 _ _ (by omega) hs'.1 (by omega)
      _ = (q ^ 2) ^ (s - 1) := by simp
  have hP0 : 0 ≤ ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s' := Finset.prod_nonneg fun s' _ => hS.1 _ _
  have hR : ((C₀ / Θ) ^ D.f) ^ (s - 1) = (C₀ ^ D.f) ^ (s - 1) * q ^ (s - 1) := by
    rw [div_pow, div_eq_mul_inv, mul_pow]
  have hpow : 4 * C₄ ^ (D.f * s) ≤ ((C₀ ^ D.f) ^ (s - 1)) ^ 2 := by
    have e1 : ((C₀ ^ D.f) ^ (s - 1)) ^ 2 = C₀ ^ (D.f * (s - 1) * 2) := by
      rw [← pow_mul, ← pow_mul, mul_assoc]
    have e2 : (2 * C₄) ^ (D.f * (s - 1) * 2) ≤ C₀ ^ (D.f * (s - 1) * 2) :=
      pow_le_pow_left₀ (by linarith) h0 _
    have hn : 1 ≤ D.f * (s - 1) := Nat.mul_pos hf (by omega)
    have e3 : (4 : ℝ) ≤ 2 ^ (D.f * (s - 1) * 2) := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (D.f * (s - 1) * 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    have e4 : C₄ ^ (D.f * s) ≤ C₄ ^ (D.f * (s - 1) * 2) := by
      apply pow_le_pow_right₀ h4
      have : s ≤ (s - 1) * 2 := by omega
      calc D.f * s ≤ D.f * ((s - 1) * 2) := Nat.mul_le_mul_left _ this
        _ = D.f * (s - 1) * 2 := by ring
    rw [e1]
    refine le_trans ?_ e2
    rw [mul_pow]
    exact mul_le_mul e3 e4 (by positivity) (by positivity)
  rw [hR]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have h1 : (1 + a) * (1 + e) ≤ 4 := by nlinarith
  have hc : 0 ≤ C₄ ^ (D.f * s) := by positivity
  calc (1 + a) * (1 + e) * C₄ ^ (D.f * s) * ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s'
      ≤ 4 * C₄ ^ (D.f * s) * (q ^ 2) ^ (s - 1) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right h1 hc) hP hP0 (by positivity)
    _ ≤ ((C₀ ^ D.f) ^ (s - 1)) ^ 2 * (q ^ 2) ^ (s - 1) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = ((C₀ ^ D.f) ^ (s - 1) * q ^ (s - 1)) ^ 2 := by
        rw [mul_pow, ← pow_mul q, ← pow_mul q, mul_comm 2 (s - 1)]

lemma size_le_one (D : Data E W) (Θ : ℝ) (hΘ : 1 ≤ Θ) (hS : D.SizesBelow Θ) :
    ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ D.r + 2 → D.vol b s ≤ 1 := by
  intro b s hb hs hbs
  refine (hS.2 b s hb hs hbs).trans ?_
  have h1 : (Θ ^ D.f)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hΘ)
  have h0 : 0 ≤ (Θ ^ D.f)⁻¹ := by positivity
  exact pow_le_one₀ h0 h1

lemma small (r f : ℕ) (C C₀ Θ : ℝ) (hΘ : 0 < Θ) (h0 : 0 ≤ C₀) (h : C₀ ≤ C)
    (hs : (r : ℝ) * (C / Θ) ^ f ≤ 1) : (r : ℝ) * (C₀ / Θ) ^ f ≤ 1 := by
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg r)) hs
  exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right h hΘ.le) f

theorem X0 (T : Tower E) : T.X 0 = {[]} := by
  ext p
  rw [T.isTower 0 p, Finset.mem_singleton]
  constructor
  · rintro ⟨hl, hb⟩
    cases p with
    | nil => rfl
    | cons a q =>
      have := (hb 0 (by simp)).1
      simp [level] at hl
      simp at this
      omega
  · rintro rfl
    simp [level]

theorem Q0 (D : Data E W) (T : Tower E) (ε : ℝ) (w : W) :
    D.Q T ε 0 w = (D.gram ε 0 w [] []).re / D.wt w := by
  simp [Data.Q, Data.Sf, X0, D.K0]

lemma gram_diag (D : Data E W) (hG : D.GramPSD) (ε : ℝ) (hε : 0 < ε) (i : ℕ) (w : W) (p : Pt E) :
    0 ≤ (D.gram ε i w p p).re := by
  have h := hG ε hε i w {p}
  have := Matrix.PosSemidef.diag_nonneg h (i := ⟨p, by simp⟩)
  have h2 : 0 ≤ D.gram ε i w p p := by simpa using this
  exact (Complex.le_def.1 h2).1

end Formalism.FourierDecayAlt.P.OneLevelCoefficients

namespace Formalism.FourierDecayAlt.P

theorem levelInequalityOfSteps : Formalism.FourierDecayAlt.TB.OneLevelOfSteps := OneLevelCoefficients.oneLevel_of_steps

end Formalism.FourierDecayAlt.P
end

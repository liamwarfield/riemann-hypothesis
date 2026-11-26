module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorExponentAtPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAinfMatrixFrobeniusGaloisEqs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEModPrimeLaurentField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentCoefficientsAinfModPow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfLinearRetractionBreuilKisin
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfLinearRetractionBreuilKisin
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.AinfRetraction

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ c : Ainf l →+ bk.S, (∀ (s : bk.S) (a : Ainf l), c (bk.ev s * a) = s * c a) ∧ c 1 = 1 := by
  intro l _ K bk
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  refine ⟨TB.c TB.i₀, TB.c_mul TB.i₀, ?_⟩
  rw [← TB.b_i₀]
  exact TB.c_self TB.i₀

end GlobalTheory.BKLim.AinfRetraction
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfLinearRetractionBreuilKisinStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ainf_linear_retraction_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ c : Ainf l →+ bk.S, (∀ (s : bk.S) (a : Ainf l), c (bk.ev s * a) = s * c a) ∧ c 1 = 1 := by
  first | exact @GlobalTheory.BKLim.AinfRetraction.main | exact GlobalTheory.BKLim.AinfRetraction.main | (intros; apply GlobalTheory.BKLim.AinfRetraction.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentCoefficientsAinfModPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.CoefDescent

variable {l : ℕ} [hl : Fact l.Prime]

theorem pow_dvd_of_pow_dvd_inclW (k : ℕ) (a : Ainf l) (h : ((l : ℕ) : WCb l) ^ k ∣ inclW l a) :
    ((l : ℕ) : Ainf l) ^ k ∣ a := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    obtain ⟨c, hc⟩ := h
    have h0 : a.coeff 0 = 0 := by
      have h1 : (inclW l a).coeff 0 = 0 := by
        rw [hc, pow_succ', mul_assoc]; exact coeff_zero_l_mul _
      change algebraMap (OCb l) (Cb l) (a.coeff 0) = 0 at h1
      exact (map_eq_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).1 h1
    obtain ⟨b, rfl⟩ := ainf_exists_l_mul_of_coeff_zero a h0
    have hl0 : ((l : ℕ) : WCb l) ≠ 0 := fun h => by
      have h1 := congrArg (fun x : WCb l => x.coeff 1) h
      simp [WittVector.coeff_p] at h1
    have hb : ((l : ℕ) : WCb l) ^ k ∣ inclW l b := by
      refine ⟨c, mul_left_cancel₀ hl0 ?_⟩
      rw [← mul_assoc, ← pow_succ', ← hc, map_mul, map_natCast]
    exact pow_succ' ((l : ℕ) : Ainf l) k ▸ mul_dvd_mul_left _ (ih b hb)

variable {K : FinExt l} (bk : BK K)

theorem isUnit_evW_X : IsUnit (bk.evW X) := by
  have e : bk.evW X = WittVector.teichmuller l (algebraMap (OCb l) (Cb l) bk.flat) := by
    simp [BK.evW, bk.ev_X, inclW, WittVector.map_teichmuller]
  rw [e]
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [WittVector.teichmuller_coeff_zero]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 bk.flat_ne_zero

def Approx (n M : ℕ) (w : WCb l) : Prop :=
  ∃ (s : bk.S) (y : WCb l), bk.evW X ^ M * w = bk.evW s + (l : WCb l) ^ n * y

theorem Approx.mono {n M M' : ℕ} {w : WCb l} (h : Approx bk n M w) (hM : M ≤ M') : Approx bk n M' w := by
  obtain ⟨s, y, e⟩ := h
  refine ⟨X ^ (M' - M) * s, bk.evW X ^ (M' - M) * y, ?_⟩
  have : bk.evW X ^ M' = bk.evW X ^ (M' - M) * bk.evW X ^ M := by
    rw [← pow_add, Nat.sub_add_cancel hM]
  rw [this, map_mul, map_pow]
  linear_combination bk.evW X ^ (M' - M) * e

theorem exists_approx {ι : Type} [Fintype ι] (n : ℕ) (w : ι → WCb l) (hw : ∀ i, w i ∈ bk.OE) :
    ∃ M, ∀ i, Approx bk n M (w i) := by
  classical
  choose m hm using fun i => hw i n
  refine ⟨Finset.univ.sup m, fun i => ?_⟩
  obtain ⟨s, y, e⟩ := hm i
  exact Approx.mono bk ⟨s, y, e⟩ (Finset.le_sup (Finset.mem_univ i))

theorem descent : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' n : ℕ) (R : Matrix (Fin d) (Fin d') (WCb l)) (x : Fin d → WCb l) (a : Fin d' → Ainf l), (∀ i j, R i j ∈ bk.OE) → (∀ i, x i ∈ bk.OE) → (∀ i, (l : WCb l) ^ n ∣ (x - R *ᵥ fun j => inclW l (a j)) i) → ∃ s : Fin d' → bk.S, ∀ i, (l : WCb l) ^ n ∣ (x - R *ᵥ fun j => bk.evW (s j)) i := by
  intro l _ K bk d d' n R x a hR hx hdiv
  obtain ⟨M₁, h₁⟩ := exists_approx bk n (fun p : Fin d × Fin d' => R p.1 p.2) (fun p => hR p.1 p.2)
  obtain ⟨M₂, h₂⟩ := exists_approx bk n x hx
  obtain ⟨M, hM1, hM2⟩ : ∃ M, M₁ ≤ M ∧ M₂ ≤ M := ⟨max M₁ M₂, le_max_left _ _, le_max_right _ _⟩
  choose r yR hRe using fun i j => (h₁ (i, j)).mono bk hM1
  choose ξ z hxe using fun i => (h₂ i).mono bk hM2
  simp only at hRe
  obtain ⟨c, hc, hc1⟩ := GlobalTheory.T.exists_ainf_linear_retraction_breuilKisin l K bk
  have hcev : ∀ s : bk.S, c (bk.ev s) = s := fun s => by
    have := hc s 1; rwa [mul_one, hc1, mul_one] at this

  have hb : ∀ i, ((l : ℕ) : Ainf l) ^ n ∣ bk.ev (ξ i) - ∑ j, bk.ev (r i j) * a j := by
    intro i
    apply pow_dvd_of_pow_dvd_inclW
    obtain ⟨q, hq⟩ := hdiv i
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct] at hq
    have hs : ∑ j, bk.evW (r i j) * inclW l (a j) =
        bk.evW X ^ M * ∑ j, R i j * inclW l (a j) - (l : WCb l) ^ n * ∑ j, yR i j * inclW l (a j) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      linear_combination (-(inclW l (a j))) * hRe i j
    refine ⟨bk.evW X ^ M * q - z i + ∑ j, yR i j * inclW l (a j), ?_⟩
    have e1 : inclW l (bk.ev (ξ i) - ∑ j, bk.ev (r i j) * a j) =
        bk.evW (ξ i) - ∑ j, bk.evW (r i j) * inclW l (a j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [BK.evW, map_sub, map_sum, map_mul]
    rw [e1, hs]
    linear_combination (-1 : WCb l) * hxe i + bk.evW X ^ M * hq
  choose b' hb' using hb
  refine ⟨fun j => c (a j), fun i => ?_⟩

  have hci : ξ i - ∑ j, r i j * c (a j) = (l : bk.S) ^ n * c (b' i) := by
    have := congrArg c (hb' i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, hcev] at this
    have e2 : ((l : ℕ) : Ainf l) ^ n * b' i = bk.ev ((l : bk.S) ^ n) * b' i := by
      rw [map_pow, map_natCast]
    rw [e2] at this
    simp only [hc] at this
    exact this
  have hci' := congrArg bk.evW hci
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum, map_mul, map_pow, map_natCast] at hci'
  simp only [map_mul] at hci'
  have hU := (isUnit_evW_X bk).pow M
  rw [← hU.dvd_mul_left]
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
  have hs : bk.evW X ^ M * ∑ j, R i j * bk.evW (c (a j)) =
      ∑ j, bk.evW (r i j) * bk.evW (c (a j)) + (l : WCb l) ^ n * ∑ j, yR i j * bk.evW (c (a j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    linear_combination (bk.evW (c (a j))) * hRe i j
  refine ⟨bk.evW (c (b' i)) + z i - ∑ j, yR i j * bk.evW (c (a j)), ?_⟩
  linear_combination hxe i - hs + hci'

end GlobalTheory.CoefDescent

theorem GlobalTheory.descentCoefficients : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' n : ℕ) (R : Matrix (Fin d) (Fin d') (WCb l)) (x : Fin d → WCb l) (a : Fin d' → Ainf l), (∀ i j, R i j ∈ bk.OE) → (∀ i, x i ∈ bk.OE) → (∀ i, (l : WCb l) ^ n ∣ (x - R *ᵥ fun j => inclW l (a j)) i) → ∃ s : Fin d' → bk.S, ∀ i, (l : WCb l) ^ n ∣ (x - R *ᵥ fun j => bk.evW (s j)) i :=
  GlobalTheory.CoefDescent.descent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentCoefficientsAinfModPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_descent_coefficients_ainf_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' n : ℕ) (R : Matrix (Fin d) (Fin d') (WCb l)) (x : Fin d → WCb l) (a : Fin d' → Ainf l), (∀ i j, R i j ∈ bk.OE) → (∀ i, x i ∈ bk.OE) → (∀ i, (l : WCb l) ^ n ∣ (x - R *ᵥ fun j => inclW l (a j)) i) → ∃ s : Fin d' → bk.S, ∀ i, (l : WCb l) ^ n ∣ (x - R *ᵥ fun j => bk.evW (s j)) i := by
  first | exact @GlobalTheory.descentCoefficients | exact GlobalTheory.descentCoefficients | (intros; apply GlobalTheory.descentCoefficients <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MittagLefflerImageBreuilKisinModPow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MittagLefflerImageBreuilKisinModPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.ImageTower

variable {S A : Type} [CommRing S] [CommRing A] (e : S →+* A) (p : ℕ) {d : ℕ} {d' : ℕ → ℕ}
  (R : ∀ n, Matrix (Fin d) (Fin (d' n)) A)

def Img (n m : ℕ) : Set (Fin d → A) :=
  {w | ∃ s : Fin (d' m) → S, ∀ i, (p : A) ^ n ∣ (w - R m *ᵥ fun j => e (s j)) i}

variable {e p R}

theorem mem_of_dvd {n m : ℕ} {w x : Fin d → A} (hw : w ∈ Img e p R n m)
    (h : ∀ i, (p : A) ^ n ∣ (x - w) i) : x ∈ Img e p R n m := by
  obtain ⟨s, hs⟩ := hw
  refine ⟨s, fun i => ?_⟩
  have : (x - R m *ᵥ fun j => e (s j)) i = (x - w) i + (w - R m *ᵥ fun j => e (s j)) i := by
    simp only [Pi.sub_apply]; ring
  rw [this]; exact dvd_add (h i) (hs i)

theorem add_mem {n m : ℕ} {w x : Fin d → A} (hw : w ∈ Img e p R n m) (hx : x ∈ Img e p R n m) :
    w + x ∈ Img e p R n m := by
  obtain ⟨s, hs⟩ := hw
  obtain ⟨t, ht⟩ := hx
  refine ⟨s + t, fun i => ?_⟩
  have he : (fun j => e ((s + t) j)) = (fun j => e (s j)) + fun j => e (t j) := by
    funext j; simp
  rw [he, mulVec_add]
  have : (w + x - ((R m *ᵥ fun j => e (s j)) + R m *ᵥ fun j => e (t j))) i =
      (w - R m *ᵥ fun j => e (s j)) i + (x - R m *ᵥ fun j => e (t j)) i := by
    simp only [Pi.sub_apply, Pi.add_apply]; ring
  rw [this]; exact dvd_add (hs i) (ht i)

theorem image_mem (n m : ℕ) (s : Fin (d' m) → S) : (R m *ᵥ fun j => e (s j)) ∈ Img e p R n m :=
  ⟨s, fun i => by simp⟩

theorem dvd_mulVec' {κ ι : Type} [Fintype ι] {q : A} (D : Matrix κ ι A) (h : ∀ i j, q ∣ D i j)
    (v : ι → A) (i : κ) : q ∣ (D *ᵥ v) i := by
  simp only [mulVec, dotProduct]
  exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (h i j) _

theorem img_succ_sub (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) S)
    (h1 : ∀ n i j, (p : A) ^ n ∣ (R n * (Y n).map e - R (n + 1)) i j) {n m : ℕ} (hnm : n ≤ m) :
    Img e p R n (m + 1) ⊆ Img e p R n m := by
  rintro w ⟨s, hs⟩
  refine ⟨Y m *ᵥ s, fun i => ?_⟩
  have he : (fun j => e ((Y m *ᵥ s) j)) = (Y m).map e *ᵥ fun j => e (s j) := by
    funext j; exact RingHom.map_mulVec e (Y m) s j
  rw [he, mulVec_mulVec]
  have : (w - (R m * (Y m).map e) *ᵥ fun j => e (s j)) i =
      (w - R (m + 1) *ᵥ fun j => e (s j)) i -
        ((R m * (Y m).map e - R (m + 1)) *ᵥ fun j => e (s j)) i := by
    simp only [sub_mulVec, Pi.sub_apply]; ring
  rw [this]
  exact dvd_sub (hs i) ((pow_dvd_pow _ hnm).trans (dvd_mulVec' _ (h1 m) _ i))

theorem img_anti (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) S)
    (h1 : ∀ n i j, (p : A) ^ n ∣ (R n * (Y n).map e - R (n + 1)) i j) {n m m' : ℕ} (hnm : n ≤ m)
    (hm : m ≤ m') : Img e p R n m' ⊆ Img e p R n m := by
  induction m', hm using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact (img_succ_sub Y h1 (hnm.trans hk)).trans ih

theorem img_mod {k n m : ℕ} (hkn : k ≤ n) : Img e p R n m ⊆ Img e p R k m := by
  rintro w ⟨s, hs⟩; exact ⟨s, fun i => (pow_dvd_pow _ hkn).trans (hs i)⟩

theorem img_stable (u : S) (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) S)
    (h1 : ∀ n i j, (p : A) ^ n ∣ (R n * (Y n).map e - R (n + 1)) i j)
    (n c : ℕ) [Finite (S ⧸ (Ideal.span {(p : S) ^ n} ⊔ Ideal.span {u ^ c}))]
    (hc : ∀ m, n ≤ m → ∀ s : Fin (d' n) → S, ∃ s' : Fin (d' m) → S, ∀ i,
      (p : A) ^ n ∣ ((R n *ᵥ fun j => e (u ^ c * s j)) - R m *ᵥ fun j => e (s' j)) i) :
    ∃ m₀, n ≤ m₀ ∧ ∀ m, m₀ ≤ m → Img e p R n m = Img e p R n m₀ := by
  let J : Ideal S := Ideal.span {(p : S) ^ n} ⊔ Ideal.span {u ^ c}
  let T : ℕ → Set (Fin (d' n) → S ⧸ J) := fun m =>
    {q | ∃ s : Fin (d' n) → S, (fun j => Ideal.Quotient.mk J (s j)) = q ∧
      (R n *ᵥ fun j => e (s j)) ∈ Img e p R n m}
  have key : ∀ m m', n ≤ m → n ≤ m' → T m ⊆ T m' → Img e p R n m ⊆ Img e p R n m' := by
    intro m m' hm hm' hT w hw
    obtain ⟨s, hs⟩ := img_anti Y h1 le_rfl hm hw
    have hRs : (R n *ᵥ fun j => e (s j)) ∈ Img e p R n m :=
      mem_of_dvd hw fun i => dvd_sub_comm.1 (hs i)
    obtain ⟨s', hq, hs'⟩ := hT ⟨s, rfl, hRs⟩
    have hj : ∀ j, ∃ a b : S, s j = s' j + (p : S) ^ n * a + u ^ c * b := by
      intro j
      have hqj : Ideal.Quotient.mk J (s' j) = Ideal.Quotient.mk J (s j) := congrFun hq j
      have hmem : s' j - s j ∈ J := Ideal.Quotient.eq.1 hqj
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.1 hy
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 hz
      exact ⟨-a, -b, by linear_combination hyz⟩
    choose a b hab using hj
    obtain ⟨t, ht⟩ := hc m' hm' b
    have hsum : ((R n *ᵥ fun j => e (s' j)) + R n *ᵥ fun j => e (u ^ c * b j)) ∈ Img e p R n m' :=
      add_mem hs' (mem_of_dvd (image_mem n m' t) ht)
    have hRs' : (R n *ᵥ fun j => e (s j)) ∈ Img e p R n m' := by
      refine mem_of_dvd hsum fun i => ?_
      have hv : (fun j => e (s j)) = (fun j => e (s' j)) + (p : A) ^ n • (fun j => e (a j)) +
          fun j => e (u ^ c * b j) := by
        funext j; rw [hab j]; simp
      rw [hv, mulVec_add, mulVec_add, mulVec_smul]
      have : ((R n *ᵥ fun j => e (s' j)) + (p : A) ^ n • (R n *ᵥ fun j => e (a j)) +
          (R n *ᵥ fun j => e (u ^ c * b j)) - ((R n *ᵥ fun j => e (s' j)) +
            R n *ᵥ fun j => e (u ^ c * b j))) i = (p : A) ^ n * (R n *ᵥ fun j => e (a j)) i := by
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [this]; exact dvd_mul_right _ _
    exact mem_of_dvd hRs' hs
  have hanti : Antitone fun k => T (n + k) := by
    rintro k k' hkk q ⟨s, rfl, hs⟩
    exact ⟨s, rfl, img_anti Y h1 (Nat.le_add_right n k) (by omega) hs⟩
  obtain ⟨k₀, hk₀⟩ := WellFoundedLT.antitone_chain_condition hanti
  refine ⟨n + k₀, by omega, fun m hm => le_antisymm (img_anti Y h1 (by omega) hm) ?_⟩
  have hTe : T (n + k₀) = T m := by
    have := hk₀ (m - n) (by omega)
    rwa [Nat.add_sub_cancel' (by omega : n ≤ m)] at this
  exact key _ _ (by omega) (by omega) hTe.le

theorem ml (u : S) (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) S)
    (h1 : ∀ n i j, (p : A) ^ n ∣ (R n * (Y n).map e - R (n + 1)) i j)
    (hfin : ∀ n c, Finite (S ⧸ (Ideal.span {(p : S) ^ n} ⊔ Ideal.span {u ^ c})))
    [IsAdicComplete (Ideal.span {(p : A)}) A]
    (h2 : ∀ n, ∃ c : ℕ, ∀ m, n ≤ m → ∀ s : Fin (d' n) → S, ∃ s' : Fin (d' m) → S, ∀ i,
      (p : A) ^ n ∣ ((R n *ᵥ fun j => e (u ^ c * s j)) - R m *ᵥ fun j => e (s' j)) i) :
    ∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → S, ∃ v : Fin d → A,
      (∀ i, (p : A) ^ n ∣ (v - R m *ᵥ fun j => e (s j)) i) ∧
      ∀ k, ∃ s' : Fin (d' k) → S, ∀ i, (p : A) ^ k ∣ (v - R k *ᵥ fun j => e (s' j)) i := by
  have hst : ∀ n, ∃ m₀, n ≤ m₀ ∧ ∀ m, m₀ ≤ m → Img e p R n m = Img e p R n m₀ := fun n => by
    obtain ⟨c, hc⟩ := h2 n
    haveI := hfin n c
    exact img_stable u Y h1 n c hc
  choose m₀ hnm₀ hm₀ using hst
  have lift : ∀ n x, x ∈ Img e p R n (m₀ n) →
      ∃ y, y ∈ Img e p R (n + 1) (m₀ (n + 1)) ∧ ∀ i, (p : A) ^ n ∣ (y - x) i := by
    intro n x hx
    rw [← hm₀ n (max (m₀ n) (m₀ (n + 1))) (le_max_left _ _)] at hx
    obtain ⟨s, hs⟩ := hx
    refine ⟨_, ?_, fun i => dvd_sub_comm.1 (hs i)⟩
    rw [← hm₀ (n + 1) (max (m₀ n) (m₀ (n + 1))) (le_max_right _ _)]
    exact image_mem _ _ s
  choose! L hL hLd using lift
  intro n
  refine ⟨m₀ n, hnm₀ n, fun s => ?_⟩
  set x₀ := R (m₀ n) *ᵥ fun j => e (s j) with hx₀def
  have hx₀ : x₀ ∈ Img e p R n (m₀ n) := image_mem _ _ s
  let w : ℕ → Fin d → A := fun k => Nat.rec x₀ (fun k y => L (n + k) y) k
  have hw0 : w 0 = x₀ := rfl
  have hws : ∀ k, w (k + 1) = L (n + k) (w k) := fun _ => rfl
  have hmem : ∀ k, w k ∈ Img e p R (n + k) (m₀ (n + k)) := by
    intro k; induction k with
    | zero => exact hx₀
    | succ k ih => rw [hws]; exact hL _ _ ih
  have htel : ∀ k j i, (p : A) ^ (n + k) ∣ (w (k + j) - w k) i := by
    intro k j; induction j with
    | zero => intro i; simp
    | succ j ih =>
      intro i
      have : (w (k + (j + 1)) - w k) i = (w (k + j + 1) - w (k + j)) i + (w (k + j) - w k) i := by
        rw [← add_assoc]; simp only [Pi.sub_apply]; ring
      rw [this, hws]
      exact dvd_add ((pow_dvd_pow _ (by omega)).trans (hLd _ _ (hmem _) i)) (ih i)
  have hcau : ∀ i, ∃ v : A, ∀ k, (p : A) ^ k ∣ w k i - v := by
    intro i
    obtain ⟨v, hv⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {(p : A)}) A) (f := fun k => w k i) (by
      intro a b hab
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hab
      have h' : (p : A) ^ a ∣ w (a + j) i - w a i := (pow_dvd_pow _ (by omega)).trans (htel a j i)
      exact dvd_sub_comm.1 h')
    refine ⟨v, fun k => ?_⟩
    have := hv k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at this
  choose V hV using hcau
  refine ⟨V, fun i => ?_, fun k => ?_⟩
  · have h1' := htel 0 n i
    rw [Nat.add_zero, Nat.zero_add, hw0] at h1'
    have : (V - x₀) i = (V i - w n i) + (w n - x₀) i := by simp only [Pi.sub_apply]; ring
    rw [this]; exact dvd_add (dvd_sub_comm.1 (hV i n)) h1'
  · have hk : w k ∈ Img e p R k k :=
      img_anti Y h1 le_rfl (le_trans (by omega) (hnm₀ (n + k))) (img_mod (by omega) (hmem k))
    exact mem_of_dvd hk fun i => dvd_sub_comm.1 (hV i k)

end GlobalTheory.ImageTower

theorem GlobalTheory.ImageTower.perfectRing_Cb' (l : ℕ) [Fact l.Prime] : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  obtain ⟨a, rfl⟩ := (bijective_frobenius (OCb l) l).2 a
  obtain ⟨b, rfl⟩ := (bijective_frobenius (OCb l) l).2 b
  exact ⟨algebraMap _ _ a / algebraMap _ _ b, by simp [frobenius_def]⟩

theorem GlobalTheory.BKLim.mittagLeffler_image : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (d' : ℕ → ℕ) (R : ∀ n, Matrix (Fin d) (Fin (d' n)) (WCb l)) (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) (bk.S)), (∀ n i j, (l : WCb l) ^ n ∣ (R n * (Y n).map bk.evW - R (n + 1)) i j) → (∀ n, ∃ c : ℕ, ∀ m, n ≤ m → ∀ s : Fin (d' n) → bk.S, ∃ s' : Fin (d' m) → bk.S, ∀ i, (l : WCb l) ^ n ∣ ((R n *ᵥ fun j => bk.evW (X ^ c * s j)) - R m *ᵥ fun j => bk.evW (s' j)) i) → ∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i := by
  intro l _ K bk d d' R Y h1 h2
  haveI : PerfectRing (Cb l) l := GlobalTheory.ImageTower.perfectRing_Cb' l
  haveI : IsAdicComplete (Ideal.span {(l : WCb l)}) (WCb l) := WittVector.isAdicCompleteIdealSpanP
  exact GlobalTheory.ImageTower.ml (e := bk.evW) (p := l) (R := R) X Y h1 (fun n c => GlobalTheory.T.finite_breuilKisin_quotient_prime_pow_X_pow l K bk n c) h2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MittagLefflerImageBreuilKisinModPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mittagLeffler_image_breuilKisin_modPow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (d' : ℕ → ℕ) (R : ∀ n, Matrix (Fin d) (Fin (d' n)) (WCb l)) (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) (bk.S)), (∀ n i j, (l : WCb l) ^ n ∣ (R n * (Y n).map bk.evW - R (n + 1)) i j) → (∀ n, ∃ c : ℕ, ∀ m, n ≤ m → ∀ s : Fin (d' n) → bk.S, ∃ s' : Fin (d' m) → bk.S, ∀ i, (l : WCb l) ^ n ∣ ((R n *ᵥ fun j => bk.evW (X ^ c * s j)) - R m *ᵥ fun j => bk.evW (s' j)) i) → ∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i := by
  first | exact @GlobalTheory.BKLim.mittagLeffler_image | exact GlobalTheory.BKLim.mittagLeffler_image | (intros; apply GlobalTheory.BKLim.mittagLeffler_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralActsOnHeckeEigenspaceOfTypeSections
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralActsOnHeckeEigenspaceOfTypeSections
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.PendOf.EigSpanProof

section GroupAlg

variable {R : Type} [CommRing R] {G : Type} [Group G] [Fintype G]

def conjSum (w : MonoidAlgebra R G) : MonoidAlgebra R G :=
  ∑ h : G, MonoidAlgebra.of R G h * w * MonoidAlgebra.of R G h⁻¹

theorem conjSum_comm_of (w : MonoidAlgebra R G) (m : G) :
    conjSum w * MonoidAlgebra.of R G m = MonoidAlgebra.of R G m * conjSum w := by
  unfold conjSum
  rw [Finset.sum_mul, Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft m)]
  refine Finset.sum_congr rfl fun h _ => ?_
  have hm : MonoidAlgebra.of R G m⁻¹ * MonoidAlgebra.of R G m = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  simp only [Equiv.coe_mulLeft, mul_inv_rev, map_mul, mul_assoc, hm, mul_one]

theorem conjSum_mem_center (w : MonoidAlgebra R G) :
    conjSum w ∈ Subalgebra.center R (MonoidAlgebra R G) := by
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using MonoidAlgebra.induction_on with
  | of m => exact (conjSum_comm_of w m).symm
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem conjSum_add (x y : MonoidAlgebra R G) : conjSum (x + y) = conjSum x + conjSum y := by
  simp only [conjSum, mul_add, add_mul, Finset.sum_add_distrib]

theorem conjSum_smul (r : R) (x : MonoidAlgebra R G) : conjSum (r • x) = r • conjSum x := by
  simp only [conjSum, Finset.smul_sum, mul_smul_comm, smul_mul_assoc]

theorem conjSum_of_central (z : MonoidAlgebra R G) (hz : ∀ a, z * a = a * z) :
    conjSum z = Fintype.card G • z := by
  unfold conjSum
  have e : ∀ h : G, MonoidAlgebra.of R G h * z * MonoidAlgebra.of R G h⁻¹ = z := fun h => by
    rw [mul_assoc, hz, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  simp only [e, Finset.sum_const, Finset.card_univ]

theorem mapCoef_conjSum {S : Type} [CommRing S] (f : R →+* S) (w : MonoidAlgebra R G) :
    PairedCharacterCondition.mapCoef f (conjSum w) = conjSum (PairedCharacterCondition.mapCoef f w) := by
  show MonoidAlgebra.mapRingHom G f (conjSum w) = conjSum (MonoidAlgebra.mapRingHom G f w)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [conjSum, map_sum, map_mul, MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom_single, map_one]

theorem mapCoef_of {S : Type} [CommRing S] (f : R →+* S) (m : G) :
    PairedCharacterCondition.mapCoef f (MonoidAlgebra.of R G m) = MonoidAlgebra.of S G m := by
  show MonoidAlgebra.mapRingHom G f _ = _
  simp only [MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom_single, map_one]

theorem mapCoef_central {S : Type} [CommRing S] (f : R →+* S) (z : MonoidAlgebra R G)
    (hz : z ∈ Subalgebra.center R (MonoidAlgebra R G)) :
    PairedCharacterCondition.mapCoef f z ∈ Subalgebra.center S (MonoidAlgebra S G) := by
  rw [Subalgebra.mem_center_iff] at hz ⊢
  intro a
  induction a using MonoidAlgebra.induction_on with
  | of m =>
    rw [← mapCoef_of f m]
    show MonoidAlgebra.mapRingHom G f _ * MonoidAlgebra.mapRingHom G f _ =
      MonoidAlgebra.mapRingHom G f _ * MonoidAlgebra.mapRingHom G f _
    rw [← map_mul, ← map_mul, hz]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem mapCoef_smul {S : Type} [CommRing S] (f : R →+* S) (r : R) (x : MonoidAlgebra R G) :
    PairedCharacterCondition.mapCoef f (r • x) = f r • PairedCharacterCondition.mapCoef f x := by
  ext g
  simp [PairedCharacterCondition.mapCoef]

theorem mapCoef_add {S : Type} [CommRing S] (f : R →+* S) (x y : MonoidAlgebra R G) :
    PairedCharacterCondition.mapCoef f (x + y) = PairedCharacterCondition.mapCoef f x + PairedCharacterCondition.mapCoef f y :=
  map_add (MonoidAlgebra.mapRingHom G f) x y

end GroupAlg

section Forms

variable {D : D7}

theorem onMt_add (i : D.nd.Loc) {a b : MonoidAlgebra ℂ (G0g D.nd)}
    (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))
    (hb : b ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) :
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (a + b) =
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i) a + D.ntypes.onMt (D.nd.mu i) (D.nd.j i) b := by
  unfold NTypes.onMt
  rw [dite_eq_left ha, dite_eq_left hb, dite_eq_left (add_mem ha hb), ← map_add (f := _)]
  rfl

theorem onMt_smul (i : D.nd.Loc) (c : ℂ) {a : MonoidAlgebra ℂ (G0g D.nd)}
    (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) :
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (c • a) = c • D.ntypes.onMt (D.nd.mu i) (D.nd.j i) a := by
  unfold NTypes.onMt
  rw [dite_eq_left ha, dite_eq_left (Subalgebra.smul_mem _ ha c), ← map_smul]
  rfl

theorem onMt_typeSum (hC : OnMtPreservesTypeV D) (i : D.nd.Loc) (z : MonoidAlgebra ℂ (G0g D.nd))
    (o : Option (D.nd.X i)) :
    typeSum D i o ≤ (typeSum D i o).comap (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) z) := by
  refine iSup₂_le fun P hP F hF => ?_
  exact Submodule.mem_comap.2 (le_biSup (D.naut.typeV i) hP (hC i P z F hF))

def ptPart (D : D7) (i : D.nd.Loc) : Submodule ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i)) :=
  ⨆ (o : Option (D.nd.X i)) (_ : o ≠ none), typeSum D i o

theorem onMt_ptPart (hC : OnMtPreservesTypeV D) (i : D.nd.Loc) (z : MonoidAlgebra ℂ (G0g D.nd)) :
    ptPart D i ≤ (ptPart D i).comap (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) z) :=
  iSup₂_le fun o ho F hF => Submodule.mem_comap.2
    (Submodule.mem_iSup_of_mem o (Submodule.mem_iSup_of_mem ho (onMt_typeSum hC i z o hF)))

theorem Phi_mem {i : D.nd.Loc} (s : Sec D i) (w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    s.Φ w ∈ ptPart D i := by
  have hw : w ∈ ⨆ x, heckeEig (D.nd.T i) (D.nd.act i) x := by
    rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i]; exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun w => s.Φ w ∈ ptPart D i) hw
    (fun x v hv => ?_) (by rw [map_zero]; exact Submodule.zero_mem _)
    (fun v v' h h' => by rw [map_add (f := _)]; exact Submodule.add_mem _ h h')
  exact Submodule.mem_iSup_of_mem (some x)
    (Submodule.mem_iSup_of_mem (Option.some_ne_none x) (s.eig x v hv))

theorem class_step (P : PairedCharacterCondition.Pend D) (hC : OnMtPreservesTypeV D) (i : D.nd.Loc) (s : Sec D i)
    (C : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))))
    (CL : MonoidAlgebra D.what₂.LL (G0g D.nd)) (hCL : ∀ a, CL * a = a * CL)
    (heq : PairedCharacterCondition.mapCoef D.what₂.embLL CL =
      PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (C : MonoidAlgebra (D.nd.O i) (G0g D.nd)))
    (w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    s.Φ ((P.zO i C).baseChange (KK D.nd i) w) =
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (C : MonoidAlgebra (D.nd.O i) (G0g D.nd))) (s.Φ w) := by
  set T := D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
    (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (C : MonoidAlgebra (D.nd.O i) (G0g D.nd))) with hT
  have hw : w ∈ Submodule.span (KK D.nd i) (Set.range (D.nd.prMt i)) := by
    rw [D.nd.prMt_span i]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨y, rfl⟩ := hv
    obtain ⟨y', hy'⟩ := P.zL_stable i CL hCL y
    have hy2 : D.what₂.jMt _ _ y' = T (D.what₂.jMt _ _ y) := by rw [hy', heq]
    rw [← P.zO_act i C y y' hy2]
    have hind := (GlobalTheory.PendOf.PrTypeProof.typeSum_indep D i) none
    have h1 := s.split y
    have h2 := s.split y'
    have hA : s.Φ (D.nd.prMt i y') - T (s.Φ (D.nd.prMt i y)) =
        -((D.what₂.jMt _ _ y' - s.Φ (D.nd.prMt i y')) - T (D.what₂.jMt _ _ y - s.Φ (D.nd.prMt i y))) := by
      rw [map_sub T, ← hy2]; abel
    have m1 : s.Φ (D.nd.prMt i y') - T (s.Φ (D.nd.prMt i y)) ∈ typeSum D i none := by
      rw [hA]; exact Submodule.neg_mem _ (Submodule.sub_mem _ h2 (onMt_typeSum hC i _ none h1))
    have m2 : s.Φ (D.nd.prMt i y') - T (s.Φ (D.nd.prMt i y)) ∈ ptPart D i :=
      Submodule.sub_mem _ (Phi_mem s _) (onMt_ptPart hC i _ (Phi_mem s _))
    exact sub_eq_zero.1 ((Submodule.disjoint_def.1 hind) _ m1 m2)
  | zero => simp only [map_zero]
  | add v v' _ _ h h' => simp only [map_add (f := _), h, h']
  | smul a v _ h => rw [LinearMap.map_smul, s.semi, h, s.semi, LinearMap.map_smul]

end Forms

section Main

variable {D : D7}

theorem lhs_smul {i : D.nd.Loc} (s : Sec D i) (r : D.nd.O i) (f : Module.End (D.nd.O i) (D.nd.Mt i))
    (w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    s.Φ ((r • f).baseChange (KK D.nd i) w) = iotaO D.nd D.naut i r • s.Φ (f.baseChange (KK D.nd i) w) := by
  rw [LinearMap.baseChange_smul, LinearMap.smul_apply, ← algebraMap_smul (KK D.nd i) r, s.semi]
  rfl

theorem all_central (P : PairedCharacterCondition.Pend D) (hC : OnMtPreservesTypeV D) (i : D.nd.Loc) (s : Sec D i)
    (z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))))
    (w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    s.Φ ((P.zO i z).baseChange (KK D.nd i) w) =
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) (s.Φ w) := by
  classical
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  have hQ : ∀ v : MonoidAlgebra (D.nd.O i) (G0g D.nd), ∀ w,
      s.Φ ((P.zO i ⟨conjSum v, conjSum_mem_center v⟩).baseChange (KK D.nd i) w) =
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (conjSum v)) (s.Φ w) := by
    intro v
    induction v using MonoidAlgebra.induction_on with
    | of m =>
      intro w
      refine class_step P hC i s _ (conjSum (MonoidAlgebra.of D.what₂.LL _ m))
        (fun a => ((Subalgebra.mem_center_iff.1 (conjSum_mem_center _)) a).symm) ?_ w
      show _ = PairedCharacterCondition.mapCoef _ (conjSum _)
      rw [mapCoef_conjSum, mapCoef_conjSum, mapCoef_of, mapCoef_of]
    | add x y hx hy =>
      intro w
      have e : (⟨conjSum (x + y), conjSum_mem_center _⟩ :
          ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd)))) =
          ⟨conjSum x, conjSum_mem_center _⟩ + ⟨conjSum y, conjSum_mem_center _⟩ :=
        Subtype.ext (conjSum_add x y)
      rw [e, map_add (f := _), LinearMap.baseChange_add, LinearMap.add_apply, map_add (f := _), hx, hy, conjSum_add,
        mapCoef_add, onMt_add i (mapCoef_central _ _ (conjSum_mem_center _))
          (mapCoef_central _ _ (conjSum_mem_center _)), LinearMap.add_apply]
    | smul r x hx =>
      intro w
      have e : (⟨conjSum (r • x), conjSum_mem_center _⟩ :
          ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd)))) =
          r • ⟨conjSum x, conjSum_mem_center _⟩ :=
        Subtype.ext (conjSum_smul r x)
      rw [e, map_smul, lhs_smul, hx, conjSum_smul, mapCoef_smul,
        onMt_smul i _ (mapCoef_central _ _ (conjSum_mem_center _)), LinearMap.smul_apply]
  have hz : ∀ a, (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) * a = a * z :=
    fun a => ((Subalgebra.mem_center_iff.1 z.2) a).symm
  set n : D.nd.O i := (Fintype.card (G0g D.nd) : D.nd.O i) with hn
  have e : (⟨conjSum (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)), conjSum_mem_center _⟩ :
      ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd)))) = n • z := by
    apply Subtype.ext
    show conjSum (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) = _
    rw [conjSum_of_central _ hz, ← Nat.cast_smul_eq_nsmul (D.nd.O i)]
    rfl
  have h := hQ z w
  rw [e, map_smul, lhs_smul, hn, conjSum_of_central _ hz, ← Nat.cast_smul_eq_nsmul (D.nd.O i), mapCoef_smul,
    onMt_smul i _ (mapCoef_central _ _ z.2), LinearMap.smul_apply, map_natCast] at h
  have hne : ((Fintype.card (G0g D.nd) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  exact smul_right_injective _ hne h

theorem main : ∀ (D : D7) (P : PairedCharacterCondition.Pend D), (∀ i, Nonempty (Sec D i)) → OnMtPreservesTypeV D → EigSpan P := by
  intro D P hS hC i z x c hzc u hu
  let s := (hS i).some
  refine s.inj ?_
  have h1 := all_central P hC i s z u
  have h2 : D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) (s.Φ u) =
      iotaO D.nd D.naut i c • s.Φ u := by
    have hle : typeSum D i (some x) ≤ Module.End.eigenspace (D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)))) (iotaO D.nd D.naut i c) :=
      iSup₂_le fun PI hPI F hF => Module.End.mem_eigenspace_iff.2 (hzc PI hPI F hF)
    exact Module.End.mem_eigenspace_iff.1 (hle (s.eig x u hu))
  rw [h1, h2, ← algebraMap_smul (KK D.nd i) c u, s.semi]
  rfl

end Main

end GlobalTheory.PendOf.EigSpanProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralActsOnHeckeEigenspaceOfTypeSectionsStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralActsOnHeckeEigenspace_of_typeSections : ∀ (D : D7) (P : PairedCharacterCondition.Pend D), (∀ i, Nonempty (Sec D i)) → OnMtPreservesTypeV D → EigSpan P := by
  first | exact @GlobalTheory.PendOf.EigSpanProof.main | exact GlobalTheory.PendOf.EigSpanProof.main | (intros; apply GlobalTheory.PendOf.EigSpanProof.main <;> assumption)
end
end

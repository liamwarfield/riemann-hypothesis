module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelCompIdempotentSplitTensor
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiAtTransport

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BeforeLastStepDatumTransportBadPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BeforeLastStepDatumTransportBadPrime
noncomputable section

namespace GlobalTheory.Transport.TwistCpl

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep

variable {E : Type} [Field E] [NumberField E]

theorem intAt_iff_val (P : HeightOneSpectrum (𝓞 E)) (a : E) : IntAt P a ↔ P.valuation E a ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, h⟩
    have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hs
    have h2 := congrArg (P.valuation E) h
    rw [map_mul, h1, one_mul] at h2
    rw [h2]
    exact P.valuation_le_one r
  · intro h
    obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer a h
    exact ⟨n, d, d.2, by rw [mul_comm]; exact hnd⟩

theorem intAt_inv_pow_mul {P : HeightOneSpectrum (𝓞 E)} {q B c : ℕ} (hq : (q : E) ≠ 0) {z : E}
    (hz : P.valuation E z ≤ P.valuation E (((q ^ B * c : ℕ) : ℕ) : E)) : IntAt P (((q : E) ^ B)⁻¹ * z) := by
  rw [intAt_iff_val, map_mul, map_inv₀]
  have hc : P.valuation E ((c : ℕ) : E) ≤ 1 :=
    (intAt_iff_val P _).1 ⟨(c : 𝓞 E), 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have h1 : P.valuation E z ≤ P.valuation E ((q : E) ^ B) := by
    refine hz.trans ?_
    rw [Nat.cast_mul, Nat.cast_pow, map_mul]
    exact mul_le_of_le_one_right' hc
  have h0 : P.valuation E ((q : E) ^ B) ≠ 0 := (Valuation.ne_zero_iff _).2 (pow_ne_zero _ hq)
  exact (inv_mul_le_one₀ (zero_lt_iff.2 h0)).2 h1

end GlobalTheory.Transport.TwistCpl

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker

theorem GlobalTheory.Transport.TwistCpl.psiAt_transport_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (hm : i + 2 = B.R.m) (al : (I.idx a).β i) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a))
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u (i)) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N (i))) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i)) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 → cosetIn q' = cosetIn p' →
    ∃ M : ℕ, 0 < M ∧ ∀ M₀ : ℕ, M ∣ M₀ → ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P)
                (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀)
                ((Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P).symm (Formalism.L2.Col.repY p'.1.2)) =
        Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P)
          (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x)
          ((Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P).symm (Formalism.L2.Col.repY q'.1.2)) := by
  intro B X I hI l u a i hm al P p q p' q' k y k' y' hp hN hp' hN' hq hq' hc
  have hL := hI.idx_ok a
  rw [show B.R.m - 2 = i by omega] at hL
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · refine ⟨Formalism.L2.Col.qOf P.1, Nat.pos_of_ne_zero fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), ?_⟩
    rintro _ ⟨c, rfl⟩ x x₀ hx
    exact GlobalTheory.Transport.Pen.psiAt_frames (base_fields_primes_ok B X).1 l.pr hL al P hP p q p' q' hp hN hp' hN' hq hq' hc
      (GlobalTheory.Transport.Pen.lt_of_congAt hx)
  · have hPQ : P.1 ∈ I.Q a := (Finset.mem_union.1 P.2).resolve_left hP
    have hq0n : Formalism.L2.Col.qOf P.1 ≠ 0 := fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    have hq0 : ((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ≠ 0 := Nat.cast_ne_zero.2 hq0n
    refine ⟨Formalism.L2.Col.qOf P.1 ^ (I.cst a).B, pow_pos (Nat.pos_of_ne_zero hq0n) _, ?_⟩
    rintro _ ⟨c, rfl⟩ x x₀ hx
    have hr := GlobalTheory.T.twist_prime_congruent_maps_frame_readings_bound I u a i P hPQ (GlobalTheory.Mem.Df.disjoint_vGs_Q I hI l a) p q p' q' k y k' y' hp hN hp' hN' hq hq' _ x x₀ hx
    have hm' : i + 1 + 1 = B.R.m := by omega
    set x₁ := Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀ with hx₁
    set x₂ := Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x with hx₂
    set y₁ := (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P).symm (Formalism.L2.Col.repY p'.1.2) with hy₁
    set y₂ := (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P).symm (Formalism.L2.Col.repY q'.1.2) with hy₂
    have s1 := hL.psiInvX al P x₁ (x₂ - x₁) y₁ fun s l => by
      have := hr l s
      rw [Matrix.sub_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply] at this
      exact GlobalTheory.Transport.TwistCpl.intAt_inv_pow_mul hq0 (by rw [LinearMap.sub_apply, Pi.sub_apply]; exact this)
    rw [add_sub_cancel] at s1
    rw [← s1]
    have h1 : y₁ ∈ cosetIn p' P := ⟨_, p'.repY_mem hm', by simp [hy₁]⟩
    rw [← hc] at h1
    obtain ⟨z, hz, h2⟩ := h1
    rw [if_neg hP] at h2
    have h3 := add_mem h2 ((GlobalTheory.TopLaw.coset_sub q'.1.1 (q'.mem_ybSet hm') hz (q'.repY_mem hm') P).2 hP)
    rw [← smul_add, sub_add_sub_cancel] at h3
    have h4 := hL.psiInv al P x₂ y₂ (y₁ - y₂) fun j => by
      rw [if_neg hP]
      open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.TopStep in exact mem_stdAt.1 h3 j
    rwa [add_sub_cancel] at h4
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BeforeLastStepDatumTransportBadPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.beforeLastStep_datum_transport_badPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (hm : i + 2 = B.R.m) (al : (I.idx a).β i) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a))
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u (i)) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N (i))) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i)) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 → cosetIn q' = cosetIn p' →
    ∃ M : ℕ, 0 < M ∧ ∀ M₀ : ℕ, M ∣ M₀ → ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P)
                (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀)
                ((Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P).symm (Formalism.L2.Col.repY p'.1.2)) =
        Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P)
          (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x)
          ((Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P).symm (Formalism.L2.Col.repY q'.1.2)) := by
  first | exact @GlobalTheory.Transport.TwistCpl.psiAt_transport_tw | exact GlobalTheory.Transport.TwistCpl.psiAt_transport_tw | (intros; apply GlobalTheory.Transport.TwistCpl.psiAt_transport_tw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepDatumTransportBadPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntMOfMulRight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Transport.Last

section Val

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

def IntM {a b : Type} (M : Matrix a b K) : Prop := ∀ i j, v (M i j) ≤ 1

def SmallM {a b : Type} (M : Matrix a b K) : Prop := ∀ i j, v (M i j) < 1

variable {v} {a b c : Type}

theorem SmallM.int {M : Matrix a b K} (h : SmallM v M) : IntM v M := fun i j => (h i j).le

theorem IntM.add {M N : Matrix a b K} (h : IntM v M) (h' : IntM v N) : IntM v (M + N) :=
  fun i j => v.map_add_le (h i j) (h' i j)

theorem IntM.sub {M N : Matrix a b K} (h : IntM v M) (h' : IntM v N) : IntM v (M - N) :=
  fun i j => v.map_sub_le (h i j) (h' i j)

theorem SmallM.sub {M N : Matrix a b K} (h : SmallM v M) (h' : SmallM v N) : SmallM v (M - N) :=
  fun i j => v.map_sub_lt (h i j) (h' i j)

theorem IntM.mul [Fintype b] {M : Matrix a b K} {N : Matrix b c K} (h : IntM v M) (h' : IntM v N) : IntM v (M * N) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact v.map_sum_le fun l _ => by rw [map_mul]; exact mul_le_one' (h i l) (h' l j)

theorem SmallM.mul_int [Fintype b] {M : Matrix a b K} {N : Matrix b c K} (h : SmallM v M) (h' : IntM v N) :
    SmallM v (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact v.map_sum_lt one_ne_zero fun l _ => by
    rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right' (h' l j)) (h i l)

theorem IntM.mul_small [Fintype b] {M : Matrix a b K} {N : Matrix b c K} (h : IntM v M) (h' : SmallM v N) :
    SmallM v (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact v.map_sum_lt one_ne_zero fun l _ => by
    rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (h i l)) (h' l j)

theorem intM_one [DecidableEq a] : IntM v (1 : Matrix a a K) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem intM_of_near [DecidableEq a] {A : Matrix a a K} (h : SmallM v (A - 1)) : IntM v A := by
  simpa using h.int.add intM_one

theorem intM_of_mul_left [Fintype a] [DecidableEq a] {A : Matrix a a K} (h : SmallM v (A - 1)) {Y : Matrix a b K}
    (hY : IntM v (A * Y)) : IntM v Y := by
  intro i j
  obtain ⟨l, -, hl⟩ := Finset.exists_max_image Finset.univ (fun l => v (Y l j)) ⟨i, Finset.mem_univ _⟩
  refine (hl i (Finset.mem_univ _)).trans ?_
  by_contra hn
  push_neg at hn
  have h0 : v (Y l j) ≠ 0 := (zero_lt_one.trans hn).ne'
  have e : Y l j = (A * Y : Matrix a b K) l j - ((A - 1) * Y : Matrix a b K) l j := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, sub_sub_cancel]
  have h1 : v (((A - 1) * Y : Matrix a b K) l j) < v (Y l j) := by
    rw [Matrix.mul_apply]
    refine v.map_sum_lt h0 fun t _ => ?_
    rw [map_mul]
    refine lt_of_le_of_lt (mul_le_mul_right (hl t (Finset.mem_univ _)) _) ?_
    exact mul_lt_of_lt_one_left (zero_lt_one.trans hn) (h l t)
  have h2 := v.map_sub_lt ((hY l j).trans_lt hn) h1
  rw [← e] at h2
  exact lt_irrefl _ h2

theorem intM_of_mul_right [Fintype a] [DecidableEq a] {A : Matrix a a K} (h : SmallM v (A - 1)) {Y : Matrix b a K}
    (hY : IntM v (Y * A)) : IntM v Y := by
  have h1 : SmallM v (Aᵀ - 1) := fun i j => by
    have := h j i
    simpa [Matrix.one_apply, eq_comm] using this
  have h2 : IntM v (Aᵀ * Yᵀ) := fun i j => by
    rw [← Matrix.transpose_mul]
    exact hY j i
  exact fun i j => intM_of_mul_left h1 h2 j i

theorem two_sided [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {A : Matrix a a K} {C : Matrix b b K}
    (hA : SmallM v (A - 1)) (hC : SmallM v (C - 1)) {Y Z : Matrix a b K} (e : A * Y = Z * C) :
    (IntM v Y ↔ IntM v Z) ∧ (IntM v Y → SmallM v (Y - Z)) := by
  have h1 : IntM v Y ↔ IntM v Z :=
    ⟨fun h => intM_of_mul_right hC (e ▸ (intM_of_near hA).mul h),
      fun h => intM_of_mul_left hA (e ▸ h.mul (intM_of_near hC))⟩
  refine ⟨h1, fun h => ?_⟩
  have e2 : Y - Z = Z * (C - 1) - (A - 1) * Y := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, e]
    abel
  rw [e2]
  exact ((h1.1 h).mul_small hC).sub (hA.mul_int h)

end Val

section Frames

open _root_.Formalism.L2.Col _root_.Formalism.L2.DIV GlobalTheory.TopStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

def ratM (P : HeightOneSpectrum (𝓞 E)) {a b : ℕ} (x : HomE E a b) : Matrix (Fin b) (Fin a) (P.adicCompletion E) :=
  (LinearMap.toMatrix' x).map (algebraMap E (P.adicCompletion E))


variable (F) in
def locM (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (g : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (P.adicCompletion E) :=
  (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P)

omit [StarRing E] in
theorem ratM_comp (P : HeightOneSpectrum (𝓞 E)) {a b c : ℕ} (x : HomE E b c) (y : HomE E a b) :
    ratM P (x ∘ₗ y) = ratM P x * ratM P y := by
  unfold ratM
  rw [LinearMap.toMatrix'_comp, Matrix.map_mul]

omit [StarRing E] in
theorem locM_mul (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (g h : GL (Fin n) (AfE F E)) :
    locM F P (g * h) = locM F P g * locM F P h := by
  unfold locM
  rw [Units.val_mul, Matrix.map_mul]

omit [StarRing E] in
theorem locM_one (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} : locM F P (1 : GL (Fin n) (AfE F E)) = 1 := by
  unfold locM
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

omit [StarRing E] in
theorem ratM_apply (P : HeightOneSpectrum (𝓞 E)) {a b : ℕ} (x : HomE E a b) (i : Fin b) (j : Fin a) :
    ratM P x i j = algebraMap E _ (x (Pi.single j 1) i) := by
  simp [ratM, LinearMap.toMatrix'_apply]

omit [StarRing E] in
theorem intM_ratM (P : HeightOneSpectrum (𝓞 E)) {a b : ℕ} (x : HomE E a b) :
    IntM Valued.v (ratM P x) ↔ ∀ j i, IntAt P (x (Pi.single j 1) i) := by
  unfold IntM
  simp only [ratM_apply, valued_algebraMap, GlobalTheory.Proof.IntegralPowerExpansion.intAt_iff_val]
  exact forall_comm

omit [StarRing E] in
theorem intAt_div_of_val {P : HeightOneSpectrum (𝓞 E)} (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {a : E}
    (h : P.valuation E a < 1) : IntAt P (a / (qOf P : E)) := by
  have ha : IntAt P a := (GlobalTheory.Proof.IntegralPowerExpansion.intAt_iff_val P a).2 h.le
  refine intAt_div_of_redP hq ha ?_
  obtain ⟨r, s, hs, e⟩ := ha
  have h1 := reduction_spec P hs e
  have hr : r ∈ P.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
    change P.valuation E (algebraMap (𝓞 E) E r) < 1
    rw [← e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (P.valuation_le_one s)) h
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hr] at h1
  have := P.isPrime
  exact (mul_eq_zero.1 h1).resolve_left fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.1 h0)

theorem single_std {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (j : Fin n) : (Pi.single j 1 : Sp E n) ∈ stdAt E n P :=
  mem_stdAt.2 fun i => by
    rw [Pi.single_apply]
    split_ifs
    · exact intAt_one
    · exact intAt_zero

variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem frame_near {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (w : SG) :
    SmallM Valued.v (locM F w.1 g⁻¹ * ratM w.1 (p.deco.1.liftFr w).toLinearMap - 1) := by
  intro i j
  obtain ⟨h1, h2⟩ := liftFr_spec p.deco.2 w
  have hz := (h1 _).2 (single_std w.1 j)
  have hb := h2 _ (single_std w.1 j)
  set z := p.deco.1.liftFr w (Pi.single j 1) with hzdef
  have hs := p.deco.2.be_smul w
  obtain ⟨s, hs0, hsz⟩ : ∃ s ∈ w.1.asIdeal.primeCompl, s • z ∈ p.deco.1.N := id hz
  obtain ⟨r, hr, hv⟩ := h.be w _ hsz i
  rw [hs s z hz, hb] at hr
  have hδ : ∃ d : 𝓞 E, redV w.1 (Pi.single j 1 : Sp E n) i = Ideal.Quotient.mk _ d ∧
      (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j = algebraMap E _ (algebraMap (𝓞 E) E d) := by
    unfold redV
    rw [Pi.single_apply, Matrix.one_apply]
    split_ifs
    · exact ⟨1, by rw [reduction_one₂, map_one], by simp⟩
    · exact ⟨0, by rw [reduction_zero, map_zero], by simp⟩
  obtain ⟨d, hd, hd'⟩ := hδ
  rw [Pi.smul_apply, hd, smul_eq_mul, ← map_mul] at hr
  have hr' : Valued.v (algebraMap E (w.1.adicCompletion E) (algebraMap (𝓞 E) E (r - s * d))) < 1 := by
    rw [valued_algebraMap, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact Ideal.Quotient.eq.1 hr
  have hs1 : Valued.v (algebraMap E (w.1.adicCompletion E) (algebraMap (𝓞 E) E s)) = 1 := by
    rw [valued_algebraMap]
    refine le_antisymm (w.1.valuation_le_one s) (not_lt.1 fun hlt => hs0 ?_)
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w.1 s).1 hlt
  have e : adAt F w.1 (Col2.pullV g (s • z) i) = algebraMap E (w.1.adicCompletion E) (algebraMap (𝓞 E) E s) *
      (locM F w.1 g⁻¹ * ratM w.1 (p.deco.1.liftFr w).toLinearMap : Matrix (Fin n) (Fin n) _) i j := by
    rw [Matrix.mul_apply, Finset.mul_sum]
    unfold Col2.pullV
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mulVec, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, adAt_inclE, ratM_apply, Pi.smul_apply, Algebra.smul_def, map_mul]
    change locM F w.1 g⁻¹ i l * _ = _ * (_ * algebraMap E _ (z l))
    ring
  have h3 := Valuation.map_add_lt _ hv hr'
  rw [e, map_sub, map_sub, map_mul, map_mul, sub_add_sub_cancel, ← mul_sub, map_mul, hs1, one_mul, ← hd'] at h3
  exact h3

theorem locM_int {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (hN : p.deco.1.N = Formalism.L2.Col.stdLat E n) (w : SG) :
    IntM Valued.v (locM F w.1 g) ∧ IntM Valued.v (locM F w.1 g⁻¹) := by
  have h0 := frame_near h w
  have h1 : ∀ x, p.deco.1.liftFr w x ∈ stdAt E n w.1 ↔ x ∈ stdAt E n w.1 := fun x => by
    have := (liftFr_spec p.deco.2 w).1 x
    rwa [Deco.at, hN] at this
  set f := p.deco.1.liftFr w
  have hf : IntM Valued.v (ratM w.1 f.toLinearMap) :=
    (intM_ratM _ _).2 fun j => mem_stdAt.1 ((h1 _).2 (single_std w.1 j))
  have hf' : IntM Valued.v (ratM w.1 f.symm.toLinearMap) :=
    (intM_ratM _ _).2 fun j => mem_stdAt.1 ((h1 _).1 (by
      rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]; exact single_std w.1 j))
  constructor
  · refine intM_of_mul_right h0 ?_
    rwa [← Matrix.mul_assoc, ← locM_mul, mul_inv_cancel, locM_one, Matrix.one_mul]
  · have := (intM_of_near h0).mul hf'
    rwa [Matrix.mul_assoc, ← ratM_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
      ratM, LinearMap.toMatrix'_id, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this

theorem read_cong {a b : ℕ} {ST' : Finset (HeightOneSpectrum (𝓞 E))} {k y : GL (Fin a) (AfE F E)} {k' y' : GL (Fin b) (AfE F E)}
    {p q : DecoF E a ST SG Q} {p' q' : DecoF E b ST' SG Q} (hp : IsPtOf hc k p) (hN : p.deco.1.N = Formalism.L2.Col.stdLat E a)
    (hp' : IsPtOf hc k' p') (hN' : p'.deco.1.N = Formalism.L2.Col.stdLat E b) (hq : IsPtOf hc (y * k) q) (hq' : IsPtOf hc (y' * k') q') (w : SG)
    (x x₀ : HomE E a b) (hx : SmallM Valued.v (locM F w.1 y'⁻¹ * ratM w.1 x * locM F w.1 y - ratM w.1 x₀)) :
    (IntM Valued.v (ratM w.1 (inFr (p.deco.1.liftFr w) (p'.deco.1.liftFr w) x₀)) ↔
      IntM Valued.v (ratM w.1 (inFr (q.deco.1.liftFr w) (q'.deco.1.liftFr w) x))) ∧
    (IntM Valued.v (ratM w.1 (inFr (p.deco.1.liftFr w) (p'.deco.1.liftFr w) x₀)) →
      SmallM Valued.v (ratM w.1 (inFr (p.deco.1.liftFr w) (p'.deco.1.liftFr w) x₀) -
        ratM w.1 (inFr (q.deco.1.liftFr w) (q'.deco.1.liftFr w) x))) := by
  have key : ∀ (g : GL (Fin a) (AfE F E)) (g' : GL (Fin b) (AfE F E)) (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b)
      (z : HomE E a b), (locM F w.1 g'⁻¹ * ratM w.1 f'.toLinearMap) * ratM w.1 (inFr f f' z) =
        (locM F w.1 g'⁻¹ * ratM w.1 z * locM F w.1 g) * (locM F w.1 g⁻¹ * ratM w.1 f.toLinearMap) := by
    intro g g' f f' z
    have e : f'.toLinearMap ∘ₗ inFr f f' z = z ∘ₗ f.toLinearMap := by
      ext v l
      simp [inFr]
    rw [Matrix.mul_assoc, ← ratM_comp, e, ratM_comp, Matrix.mul_assoc _ (locM F w.1 g), ← Matrix.mul_assoc (locM F w.1 g),
      ← locM_mul, mul_inv_cancel, locM_one, Matrix.one_mul, Matrix.mul_assoc]
  obtain ⟨a1, a2⟩ := two_sided (frame_near hp' w) (frame_near hp w) (key _ _ _ _ x₀)
  obtain ⟨b1, b2⟩ := two_sided (frame_near hq' w) (frame_near hq w) (key _ _ _ _ x)
  have hD := ((locM_int hp' hN' w).2.mul_small hx).mul_int (locM_int hp hN w).1
  have e : locM F w.1 k'⁻¹ * (locM F w.1 y'⁻¹ * ratM w.1 x * locM F w.1 y - ratM w.1 x₀) * locM F w.1 k =
      locM F w.1 (y' * k')⁻¹ * ratM w.1 x * locM F w.1 (y * k) - locM F w.1 k'⁻¹ * ratM w.1 x₀ * locM F w.1 k := by
    rw [_root_.mul_inv_rev, locM_mul, locM_mul, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
  rw [e] at hD
  have c1 : IntM Valued.v (locM F w.1 k'⁻¹ * ratM w.1 x₀ * locM F w.1 k) ↔
      IntM Valued.v (locM F w.1 (y' * k')⁻¹ * ratM w.1 x * locM F w.1 (y * k)) :=
    ⟨fun h => by simpa using hD.int.add h, fun h => by simpa using h.sub hD.int⟩
  have c2 := a1.trans (c1.trans b1.symm)
  refine ⟨c2, fun h => ?_⟩
  have := ((a2 h).sub hD).sub (b2 (c2.1 h))
  convert this using 1
  abel

end Frames

section Top

open _root_.Formalism.L2.Col _root_.Formalism.L2.DIV GlobalTheory.TopStep

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {m2 : ℕ}

theorem locTop_shift (hc : cst.Ok) {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs)
    (y : HomE X.E (R.N (m2 + 1)) (R.N R.m)) {a b : Sp X.E (R.N (m2 + 1))} (ha : ∀ i, IntAt P.1 ((qOf P.1 : X.E) * a i))
    (hb : ∀ i, IntAt P.1 (b i - a i)) : locTop Ch sel mu cst m2 P y b = locTop Ch sel mu cst m2 P y a := by
  unfold locTop
  congr 1
  generalize atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y = η
  unfold ftY
  rw [if_pos hP, if_pos hP]
  split_ifs with h
  · have ev : ∀ z : Sp X.E (R.N (m2 + 1)), η z = ∑ j, z j * η (Pi.single j 1) := fun z => by
      conv_lhs => rw [pi_eq_sum_univ' z]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum]
    have he : IntAt P.1 ((epsSg : ℤ) : X.E) := intCast_mem (intRing P.1) _
    have hd : IntAt P.1 ((epsSg : X.E) * η (b - a)) := by
      rw [ev]
      exact he.mul (intAt_sum _ fun j _ => (hb j).mul (h j))
    have hz' : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * η a)) := by
      obtain ⟨D, hD⟩ : ∃ D, cst.D P = D + 1 := ⟨cst.D P - 1, by have := hc.D_pos P; omega⟩
      have := (intAt_pow (intAt_nat (P := P.1) (qOf P.1)) D).mul
        (he.mul (intAt_sum Finset.univ fun j _ => (ha j).mul (h j)))
      convert this using 1
      rw [hD, ev, pow_succ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have := hc.psi_add P _ _ hz' ((intAt_pow (intAt_nat (P := P.1) (qOf P.1)) _).mul hd)
    rw [hc.psi_int P _ hd, mul_one, ← mul_add, ← map_add (f := _), add_sub_cancel] at this
    exact this
  · rfl

theorem rep_sub_int {u : Pr.Word} {j : ℕ} (h : j + 1 = R.m) (p q : PtAt R sel mu cst u j) (e : cosetIn q = cosetIn p)
    {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs) (i : Fin (R.N j)) :
    IntAt P.1 ((frsF sel mu p.1.1 P).symm (repY p.1.2) i - (frsF sel mu q.1.1 P).symm (repY q.1.2) i) := by
  have h1 : (frsF sel mu p.1.1 P).symm (repY p.1.2) ∈ cosetIn p P :=
    ⟨_, p.repY_mem h, by rw [sub_self, smul_zero]; exact zero_mem _⟩
  rw [← e] at h1
  obtain ⟨z, hz1, h2⟩ := h1
  rw [if_pos hP, pow_zero, inv_one, one_smul] at h2
  have h3 := q.repY_mem h
  obtain ⟨y, -, hY⟩ := q.mem_ybSet h
  have h4 := (mem_locLat _ _ _ _).1 ((Set.ext_iff.1 hY _).1 hz1) P
  have h5 := (mem_locLat _ _ _ _).1 ((Set.ext_iff.1 hY _).1 h3) P
  simp only [if_pos hP, zpow_zero, inv_one, one_smul] at h4 h5
  have h6 : z - repY q.1.2 ∈ q.1.1.deco.1.at P.1 := by
    have := sub_mem h4 h5
    rwa [sub_sub_sub_cancel_right] at this
  rw [← (frsF sel mu q.1.1 P).apply_symm_apply (z - _), frsF_mem, map_sub] at h6
  have h7 := add_mem h2 h6
  rw [sub_add_sub_cancel] at h7
  exact mem_stdAt.1 h7 i

theorem locTop_of_cong (hm : R.m = m2 + 2) (hc : cst.Ok) {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs)
    (hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2) {j : ℕ} (h : R.N j = R.N R.m) (y z : HomE X.E (R.N (m2 + 1)) (R.N j))
    {a : Sp X.E (R.N (m2 + 1))} (ha : ∀ i, IntAt P.1 ((qOf P.1 : X.E) * a i))
    (H : (IntM Valued.v (ratM P.1 y) ↔ IntM Valued.v (ratM P.1 z)) ∧
      (IntM Valued.v (ratM P.1 y) → SmallM Valued.v (ratM P.1 y - ratM P.1 z))) :
    locTop Ch sel mu cst m2 P (castSp X.E h ∘ₗ y) a = locTop Ch sel mu cst m2 P (castSp X.E h ∘ₗ z) a := by
  have supp : ∀ w : HomE X.E (R.N (m2 + 1)) (R.N j), locTop Ch sel mu cst m2 P (castSp X.E h ∘ₗ w) a ≠ 0 →
      IntM Valued.v (ratM P.1 w) := fun w hw =>
    (intM_ratM _ _).2 fun s i => mem_stdAt.1 (locTop_supp hm hP hw s) (Fin.cast h i)
  by_cases hy : IntM Valued.v (ratM P.1 y)
  · refine locTop_congr hm hc hP ha fun s l => ⟨(intM_ratM _ _).1 hy s _, (intM_ratM _ _).1 (H.1.1 hy) s _, ?_⟩
    refine intAt_div_of_val hq ?_
    have := H.2 hy (Fin.cast h.symm l) s
    rwa [Matrix.sub_apply, ratM_apply, ratM_apply, ← map_sub, valued_algebraMap] at this
  · have h1 : locTop Ch sel mu cst m2 P (castSp X.E h ∘ₗ y) a = 0 := by
      by_contra h0
      exact hy (supp _ h0)
    have h2 : locTop Ch sel mu cst m2 P (castSp X.E h ∘ₗ z) a = 0 := by
      by_contra h0
      exact hy (H.1.2 (supp _ h0))
    rw [h1, h2]

end Top

end GlobalTheory.Transport.Last
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepDatumTransportBadPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.Transport.LastTw

section TopQ

open _root_.Formalism.L2.Col _root_.Formalism.L2.DIV GlobalTheory.TopStep GlobalTheory.TopStep.Model

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {m2 : ℕ}

theorem locTop_shiftQ (hc : cst.Ok) {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D P)
    (y : HomE X.E (R.N (m2 + 1)) (R.N R.m)) {a b : Sp X.E (R.N (m2 + 1))} (ha : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * a i))
    (hb : ∀ i, IntAt P.1 (((qOf P.1 : X.E) ^ cst.M)⁻¹ * (b i - a i))) :
    locTop Ch sel mu cst m2 P y b = locTop Ch sel mu cst m2 P y a := by
  have hq := qOf_ne_zero (P := P.1)
  unfold locTop
  congr 1
  generalize atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y = η
  unfold ftY
  rw [if_neg hP, if_neg hP]
  split_ifs with h
  · congr 1
    have ev : ∀ z : Sp X.E (R.N (m2 + 1)), η z = ∑ j, z j * η (Pi.single j 1) := fun z => by
      conv_lhs => rw [pi_eq_sum_univ' z]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum]
    have he : IntAt P.1 ((epsSg : ℤ) : X.E) := intCast_mem (intRing P.1) _
    have hd : IntAt P.1 ((epsSg : X.E) * η (b - a)) := by
      rw [ev]
      refine he.mul (intAt_sum _ fun j _ => ?_)
      have := (hb j).mul (h j)
      convert this using 1
      rw [Pi.sub_apply, mul_mul_mul_comm, inv_mul_cancel₀ (pow_ne_zero _ hq), one_mul]
    have hz' : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * η a)) := by
      obtain ⟨D, hD'⟩ := Nat.exists_eq_add_of_le hD
      have := (intAt_pow (intAt_nat (P := P.1) (qOf P.1)) D).mul
        (he.mul (intAt_sum Finset.univ fun j _ => (ha j).mul (h j)))
      convert this using 1
      rw [hD', ev, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have := hc.psi_add P _ _ hz' ((intAt_pow (intAt_nat (P := P.1) (qOf P.1)) _).mul hd)
    rw [hc.psi_int P _ hd, mul_one, ← mul_add, ← map_add (f := _), add_sub_cancel] at this
    exact this
  · rfl

theorem locTop_congQ (hm : R.m = m2 + 2) (hc : cst.Ok) {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D P)
    (y z : HomE X.E (R.N (m2 + 1)) (R.N R.m))
    (hyz : ∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ (cst.M + 1))⁻¹ * (y (Pi.single s 1) l - z (Pi.single s 1) l)))
    {a : Sp X.E (R.N (m2 + 1))} (ha : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * a i)) :
    locTop Ch sel mu cst m2 P y a = locTop Ch sel mu cst m2 P z a := by
  have hq := qOf_ne_zero (P := P.1)
  choose t ht ez using fun s l => (⟨_, hyz s l, by field_simp; ring⟩ : ∃ t, IntAt P.1 t ∧
    y (Pi.single s 1) l = z (Pi.single s 1) l + (qOf P.1 : X.E) ^ (cst.M + 1) * t)
  have ez' : ∀ s l, z (Pi.single s 1) l = y (Pi.single s 1) l + (qOf P.1 : X.E) ^ (cst.M + 1) * (0 - t s l) :=
    fun s l => by rw [ez]; ring
  have ht' : ∀ s l, IntAt P.1 (0 - t s l) := fun s l => intAt_sub intAt_zero (ht s l)
  have tr : ∀ (y z : HomE X.E (R.N (m2 + 1)) (R.N R.m)) (t : Fin (R.N (m2 + 1)) → Fin (R.N R.m) → X.E),
      (∀ s l, IntAt P.1 (t s l)) → (∀ s l, y (Pi.single s 1) l = z (Pi.single s 1) l + (qOf P.1 : X.E) ^ (cst.M + 1) * t s l) →
      SuppQ (m2 := m2) P.1 cst.M z → SuppQ (m2 := m2) P.1 cst.M y := fun y z t ht ez hz s => by
    refine ⟨fun i => ?_, ?_⟩
    · rw [ez]
      exact ((hz s).1 i).add ((intAt_pow (intAt_nat _) _).mul (ht _ _))
    · rw [ez, mul_add]
      refine (hz s).2.add ?_
      rw [← mul_assoc, ← pow_add]
      exact (intAt_pow (intAt_nat _) _).mul (ht _ _)
  by_cases hz : SuppQ (m2 := m2) P.1 cst.M z
  swap
  · have h1 : locTop Ch sel mu cst m2 P z a = 0 := by
      by_contra h
      exact hz (suppQ_of_ne hm hP h)
    have h2 : locTop Ch sel mu cst m2 P y a = 0 := by
      by_contra h
      exact hz (tr z y _ ht' ez' (suppQ_of_ne hm hP h))
    rw [h1, h2]
  have hy := tr y z t ht ez hz
  unfold locTop
  refine congrArg₂ (· * ·) ?_ ?_
  · have he : ∀ p p', CongQ P.1
        (LocE.entB (qOf P.1) R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) 0 0
          (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) p p')
        (LocE.entB (qOf P.1) R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) 0 0
          (prXp X.E R ∘ₗ z ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) p p') := fun p p' => by
      rw [entB_topQ hm, entB_topQ hm]
      split_ifs with h
      · refine ⟨(hy _).1 _, (hz _).1 _, ?_⟩
        show IntAt _ ((y _ _ - z _ _) / _)
        rw [ez]
        convert (intAt_pow (intAt_nat (P := P.1) (qOf P.1)) cst.M).mul (ht ⟨p', h.2⟩ (Br.iC (N_m_succ R) ⟨p, h.1⟩)) using 1
        rw [pow_succ]
        field_simp
        ring
      · exact congQ_zero
    unfold PhiTop
    rw [if_neg hP]
    unfold LocE.PhiQ
    refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ ?_ rfl
    · simp only [(he _ _).1, (he _ _).2.1, (he _ _).div_iff]
    · exact unitV_det_congr _ fun s s' => he s.1 s'.1
  · unfold ftY
    have ev : ∀ w : HomE X.E (R.N (m2 + 1)) (R.N R.m), (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ w) a =
        ∑ j, a j * w (Pi.single j 1) (Br.iL (N_m_succ R)) := fun w => by
      rw [LinearMap.comp_apply, atNL_last, apply_eq_sum]
    have he : IntAt P.1 ((epsSg : ℤ) : X.E) := intCast_mem (intRing P.1) _
    rw [if_neg hP, if_neg hP, if_pos (fun i => by rw [LinearMap.comp_apply, atNL_last]; exact (hy _).2),
      if_pos (fun i => by rw [LinearMap.comp_apply, atNL_last]; exact (hz _).2), ev, ev]
    congr 1
    have hd : IntAt P.1 ((epsSg : X.E) * ∑ j, ((qOf P.1 : X.E) ^ cst.M * a j) * ((qOf P.1 : X.E) * t j (Br.iL (N_m_succ R)))) :=
      he.mul (intAt_sum _ fun j _ => (ha j).mul ((intAt_nat _).mul (ht _ _)))
    have hz' : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * ∑ j, a j * z (Pi.single j 1) (Br.iL (N_m_succ R)))) := by
      obtain ⟨D, hD'⟩ := Nat.exists_eq_add_of_le hD
      have := (intAt_pow (intAt_nat (P := P.1) (qOf P.1)) D).mul
        (he.mul (intAt_sum Finset.univ fun j _ => (ha j).mul (hz j).2))
      convert this using 1
      rw [hD', Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have := hc.psi_add P _ _ hz' ((intAt_pow (intAt_nat (P := P.1) (qOf P.1)) _).mul hd)
    rw [hc.psi_int P _ hd, mul_one] at this
    rw [← this]
    congr 1
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ez]
    ring

theorem rep_sub_intQ {u : Pr.Word} {j : ℕ} (h : j + 1 = R.m) (p q : PtAt R sel mu cst u j) (e : cosetIn q = cosetIn p)
    {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) (i : Fin (R.N j)) :
    IntAt P.1 (((qOf P.1 : X.E) ^ cst.M)⁻¹ *
      ((frsF sel mu p.1.1 P).symm (repY p.1.2) i - (frsF sel mu q.1.1 P).symm (repY q.1.2) i)) := by
  have h1 : (frsF sel mu p.1.1 P).symm (repY p.1.2) ∈ cosetIn p P :=
    ⟨_, p.repY_mem h, by rw [sub_self, smul_zero]; exact zero_mem _⟩
  rw [← e] at h1
  obtain ⟨z, hz1, h2⟩ := h1
  rw [if_neg hP] at h2
  have h3 := q.repY_mem h
  obtain ⟨y, -, hY⟩ := q.mem_ybSet h
  have h4 := (mem_locLat _ _ _ _).1 ((Set.ext_iff.1 hY _).1 hz1) P
  have h5 := (mem_locLat _ _ _ _).1 ((Set.ext_iff.1 hY _).1 h3) P
  simp only [if_neg hP, zpow_natCast] at h4 h5
  have h6 : ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (z - repY q.1.2) ∈ q.1.1.deco.1.at P.1 := by
    have := sub_mem h4 h5
    rwa [← smul_sub, sub_sub_sub_cancel_right] at this
  rw [← (frsF sel mu q.1.1 P).apply_symm_apply (_ • (z - _)), frsF_mem, map_smul, map_sub] at h6
  have h7 := add_mem h2 h6
  rw [← smul_add, sub_add_sub_cancel] at h7
  simpa using mem_stdAt.1 h7 i

end TopQ

theorem locTop_transport_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (ok : I.Ok) (u : B.Word) (a : I.ι) (n : ℕ) (h : n + 1 + 1 = B.R.m) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a))
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u (n + 1)) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (n + 1 + 1))
    (k y : TC.GA B (B.R.N (n + 1))) (k' y' : TC.GA B (B.R.N (n + 1 + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (n + 1)) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (n + 1 + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 → cosetIn q = cosetIn p →
    ∃ M : ℕ, 0 < M ∧ ∀ M₀ : ℕ, M ∣ M₀ → ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N (n + 1)) (B.R.N (n + 1 + 1)),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      GlobalTheory.TopStep.locTop I.Ch I.sel (I.tup a) (I.cst a) n P
                   (castSp B.fields.E (congrArg B.R.N h) ∘ₗ Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀)
                   ((Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P).symm (Formalism.L2.Col.repY p.1.2)) =
        GlobalTheory.TopStep.locTop I.Ch I.sel (I.tup a) (I.cst a) n P
          (castSp B.fields.E (congrArg B.R.N h) ∘ₗ Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x)
          ((Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P).symm (Formalism.L2.Col.repY q.1.2)) := by
  intro B X I l ok u a n h P p q p' q' k y k' y' hp hN hp' hN' hq hq' e
  have hc := (ok.idx_ok a).cst_ok
  have hqpos : 0 < Formalism.L2.Col.qOf P.1 := Nat.pos_of_ne_zero fun h0 => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · have hsq := Formalism.L2.Col.ciQ_notMem_sq (GlobalTheory.Mem.FieldsLaws.fields_ok B) l.pr hP
    refine ⟨Formalism.L2.Col.qOf P.1, hqpos, ?_⟩
    rintro _ ⟨c, rfl⟩ x x₀ hx
    have hv : Valued.v ((Formalism.L2.Col.qOf P.1 * c : ℕ) : P.1.adicCompletion B.fields.E) < 1 := by
      rw [← map_natCast (algebraMap B.fields.E (P.1.adicCompletion B.fields.E)), valued_algebraMap,
        ← map_natCast (algebraMap (𝓞 B.fields.E) B.fields.E), HeightOneSpectrum.valuation_lt_one_iff_mem, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ GlobalTheory.TopStep.qOf_mem
    have H := GlobalTheory.Transport.Last.read_cong hp hN hp' hN' hq hq' ⟨P.1, hP⟩ x x₀ (fun r s => by
      refine lt_of_eq_of_lt (congrArg Valued.v ?_) ((hx r s).trans_lt hv)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [GlobalTheory.Transport.Last.locM, GlobalTheory.Transport.Last.ratM, Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, map_sub,
        map_sum, map_mul, adAt_inclE])
    have f1 : ∀ {j : ℕ} (r : Formalism.L2.Col.ChPt (R := B.R) I.sel (I.tup a) u j),
        Formalism.L2.Col.frsF I.sel (I.tup a) r P = r.deco.1.liftFr ⟨P.1, hP⟩ := fun r => dif_pos hP
    rw [← f1, ← f1, ← f1, ← f1] at H
    have hq1 := GlobalTheory.TopStep.repY_int q.1.1 (q.mem_ybSet h) hP
    rw [GlobalTheory.Transport.Last.locTop_shift hc hP _ hq1 (GlobalTheory.Transport.Last.rep_sub_int h p q e hP)]
    exact GlobalTheory.Transport.Last.locTop_of_cong h.symm hc hP hsq _ _ _ hq1 H
  · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.1 P.2).resolve_left hP
    have hD := (ok.idx_ok a).depthQ P hP
    have hq0 := GlobalTheory.TopStep.qOf_ne_zero (P := P.1)
    refine ⟨Formalism.L2.Col.qOf P.1 ^ ((I.cst a).M + 1), pow_pos hqpos _, ?_⟩
    rintro _ ⟨c, rfl⟩ x x₀ hx
    have H := GlobalTheory.T.twist_prime_congruent_maps_frame_readings_bound I u a (n + 1) P hQ (GlobalTheory.Mem.Df.disjoint_vGs_Q I ok l a) p q p' q' k y k' y' hp hN hp' hN' hq hq' _ x x₀ hx
    have hqv := GlobalTheory.TopStep.Model.repY_intQ q.1.1 (q.mem_ybSet h) hP
    rw [locTop_shiftQ hc hP hD _ hqv (rep_sub_intQ h p q e hP)]
    have key : ∀ s r, Formalism.L2.Col.IntAt P.1 (((Formalism.L2.Col.qOf P.1 : B.fields.E) ^ ((I.cst a).M + 1))⁻¹ *
        (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀ (Pi.single s 1) r -
          Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x (Pi.single s 1) r)) := by
      intro s r
      rw [GlobalTheory.Proof.IntegralPowerExpansion.intAt_iff_val]
      have H1 := H r s
      rw [Matrix.sub_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, Nat.cast_mul, Nat.cast_pow, map_mul] at H1
      have hc1 : P.1.valuation B.fields.E (c : B.fields.E) ≤ 1 := by
        rw [← map_natCast (algebraMap (𝓞 B.fields.E) B.fields.E)]
        exact P.1.valuation_le_one _
      have hpos : P.1.valuation B.fields.E ((Formalism.L2.Col.qOf P.1 : B.fields.E) ^ ((I.cst a).M + 1)) ≠ 0 :=
        (Valuation.ne_zero_iff _).2 (pow_ne_zero _ hq0)
      rw [map_mul, map_inv₀, ← neg_sub, Valuation.map_neg]
      calc _ ≤ (P.1.valuation B.fields.E ((Formalism.L2.Col.qOf P.1 : B.fields.E) ^ ((I.cst a).M + 1)))⁻¹ *
            (P.1.valuation B.fields.E ((Formalism.L2.Col.qOf P.1 : B.fields.E) ^ ((I.cst a).M + 1)) * P.1.valuation B.fields.E (c : B.fields.E)) :=
            by gcongr
        _ ≤ (P.1.valuation B.fields.E ((Formalism.L2.Col.qOf P.1 : B.fields.E) ^ ((I.cst a).M + 1)))⁻¹ *
            (P.1.valuation B.fields.E ((Formalism.L2.Col.qOf P.1 : B.fields.E) ^ ((I.cst a).M + 1)) * 1) :=
            by gcongr
        _ = 1 := by rw [mul_one, inv_mul_cancel₀ hpos]
    refine locTop_congQ h.symm hc hP hD _ _ ?_ hqv
    intro s l
    rw [LinearMap.comp_apply, LinearMap.comp_apply, castSp_apply, castSp_apply]
    exact key s _

end GlobalTheory.Transport.LastTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepDatumTransportBadPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStep_datum_transport_badPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (ok : I.Ok) (u : B.Word) (a : I.ι) (n : ℕ) (h : n + 1 + 1 = B.R.m) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a))
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u (n + 1)) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (n + 1 + 1))
    (k y : TC.GA B (B.R.N (n + 1))) (k' y' : TC.GA B (B.R.N (n + 1 + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (n + 1)) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (n + 1 + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 → cosetIn q = cosetIn p →
    ∃ M : ℕ, 0 < M ∧ ∀ M₀ : ℕ, M ∣ M₀ → ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N (n + 1)) (B.R.N (n + 1 + 1)),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      GlobalTheory.TopStep.locTop I.Ch I.sel (I.tup a) (I.cst a) n P
                   (castSp B.fields.E (congrArg B.R.N h) ∘ₗ Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀)
                   ((Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P).symm (Formalism.L2.Col.repY p.1.2)) =
        GlobalTheory.TopStep.locTop I.Ch I.sel (I.tup a) (I.cst a) n P
          (castSp B.fields.E (congrArg B.R.N h) ∘ₗ Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x)
          ((Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P).symm (Formalism.L2.Col.repY q.1.2)) := by
  exact @GlobalTheory.Transport.LastTw.locTop_transport_tw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartBasePairDatumRationalApproxEqTwisted
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.AdForm.TwResid

theorem phiT_tw {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ)
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N i)) (k' y' : TC.GA B (B.R.N (i + 1)))
    (hp : TC.PtOf k p.1.1) (hpN : p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i))
    (hp' : TC.PtOf k' p'.1.1) (hpN' : p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)))
    (hq : TC.PtOf (y * k) q.1.1) (hq' : TC.PtOf (y' * k') q'.1.1) :
    ∃ M : ℕ, 0 < M ∧ ∀ M₀ : ℕ, M ∣ M₀ → ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)),
      (∀ P ∈ (B.primes X).vT u, GlobalTheory.Transport.CongAt B P M₀ y y' x x₀) →
      Formalism.L2.Col.phiT B.fields.K p.1.1.deco.1 p'.1.1.deco.1 x₀ = Formalism.L2.Col.phiT B.fields.K q.1.1.deco.1 q'.1.1.deco.1 x := by
  refine ⟨∏ P ∈ (B.primes X).vT u, Ideal.absNorm P.asIdeal,
    Finset.prod_pos fun P _ => Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 P.ne_bot), fun M₀ hM x x₀ h => ?_⟩
  exact GlobalTheory.Transport.LevelDatum.phiT_eq B.fields.K (B.R.N_pos i) (B.R.N_pos (i + 1)) hp hpN hp' hpN' hq hq' x x₀
    fun P hP r s => lt_of_le_of_lt (h P hP r s) (GlobalTheory.Transport.LevelDatum.val_natCast_lt hM hP)

theorem xiAt_transport_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (hok : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ)
    (hi : i + 1 ≤ B.R.m)
    (b : Idx I.sel (I.tup a) (I.idx a) i) (b' : Idx I.sel (I.tup a) (I.idx a) (i + 1))
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N i)) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 → cosetIn q = cosetIn p → cosetIn q' = cosetIn p' →
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)),
      (∀ P ∈ Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u, ∀ r s,
        Valued.v (adAt B.host.F P
          ((HMul.hMul (HMul.hMul ((y'⁻¹ : TC.GA B (B.R.N (i + 1))).1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E))
          ((LinearMap.toMatrix' x).map (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)))
          (y.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) -
          ((LinearMap.toMatrix' x₀).map (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E))) r s)) ≤
        Valued.v ((M₀ : ℕ) : P.adicCompletion B.host.E)) →
      xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i b b' p p' x₀ =
        xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i b b' q q' x := by
  intro B X I l hok u a i hi b b' p q p' q' k y k' y' hk hN hk' hN' hq hq' hc hc'
  obtain ⟨M1, hM1, H1⟩ := phiT_tw I u a i p q p' q' k y k' y' hk hN hk' hN' hq hq'
  have Hent := GlobalTheory.T.entryDatum_transport_badPrime_anyTuple I hok l u a
  have Hcp := GlobalTheory.T.beforeLastStep_datum_transport_badPrime I hok l u a
  have Hlast := GlobalTheory.T.lastStep_datum_transport_badPrime I l hok u a
  have hrowT : ∀ (M₀ : ℕ) (x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))),
      (∀ P ∈ Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u, GlobalTheory.Transport.CongAt B P M₀ y y' x x₀) →
      (∀ P ∈ (B.primes X).vT u, GlobalTheory.Transport.CongAt B P M₀ y y' x x₀) ∧
        ∀ P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a), GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ :=
    fun M₀ x x₀ hx => ⟨fun P hP => hx P (Finset.mem_union_left _ hP), fun P => hx P.1 (Finset.mem_union_right _ P.2)⟩
  by_cases h2 : i + 2 < B.R.m
  · have hlt : i < B.R.m := by omega
    have hlt' : i + 1 < B.R.m := by omega
    choose Mf hMf Hf using fun P => Hent i h2 (b.get hlt) (b'.get hlt') P p q p' q' k y k' y' hk hN hk' hN' hq hq'
    refine ⟨M1 * ∏ P, Mf P, Nat.mul_pos hM1 (Finset.prod_pos fun P _ => hMf P), ?_⟩
    intro x x₀ hx
    obtain ⟨hvT, hrow⟩ := hrowT _ x x₀ hx
    unfold xiAt
    rw [dite_eq_left h2, dite_eq_left h2]
    unfold Formalism.L2.Col.XiEntry
    rw [H1 _ (dvd_mul_right _ _) x x₀ hvT]
    refine congrArg (HMul.hMul _) (Finset.prod_congr rfl fun P _ => ?_)
    exact Hf P _ (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ P)) _) x x₀ (hrow P)
  by_cases h3 : i + 2 = B.R.m
  · have hlt : i < B.R.m := by omega
    choose Mf hMf Hf using fun P => Hcp i h3 (b.get hlt) P p q p' q' k y k' y' hk hN hk' hN' hq hq' hc'
    refine ⟨M1 * ∏ P, Mf P, Nat.mul_pos hM1 (Finset.prod_pos fun P _ => hMf P), ?_⟩
    intro x x₀ hx
    obtain ⟨hvT, hrow⟩ := hrowT _ x x₀ hx
    unfold xiAt
    rw [dite_eq_right h2, dite_eq_right h2, dite_eq_left h3, dite_eq_left h3]
    unfold Formalism.L2.Col.XiCpl1
    rw [H1 _ (dvd_mul_right _ _) x x₀ hvT]
    refine congrArg (HMul.hMul _) (Finset.prod_congr rfl fun P _ => ?_)
    exact Hf P _ (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ P)) _) x x₀ (hrow P)
  · have h4 : i + 1 = B.R.m := by omega
    have h2m := B.R.two_le_m
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    choose Mf hMf Hf using fun P => Hlast n h4 P p q p' q' k y k' y' hk hN hk' hN' hq hq' hc
    refine ⟨M1 * ∏ P, Mf P, Nat.mul_pos hM1 (Finset.prod_pos fun P _ => hMf P), ?_⟩
    intro x x₀ hx
    obtain ⟨hvT, hrow⟩ := hrowT _ x x₀ hx
    rw [xiAt_last _ _ _ _ _ h4, xiAt_last _ _ _ _ _ h4]
    unfold xiOver
    rw [H1 _ (dvd_mul_right _ _) x x₀ hvT]
    refine congrArg (HMul.hMul _) (Finset.prod_congr rfl fun P _ => ?_)
    exact Hf P _ (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ P)) _) x x₀ (hrow P)

theorem tw_resid_datum : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) g g', g ∈ GfC _ → g' ∈ GfC _ → finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) g = ((A.K i (Nat.le_of_succ_le hi) (A.chOf i c)).y ⟨c, rfl⟩).1.1 → finM _ (rankN (I.rec7 l Z) (i + 1) hi) g' = ((A.K (i + 1) hi (A.chOf (i + 1) c')).y ⟨c', rfl⟩).1.1 → ∃ M : ℕ, 0 < M ∧ ∀ (γ γ₀ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → γ₀.map (fun r => A.e * incA (I.rec7 l Z) r) = actO _ _ g⁻¹ g'⁻¹ (γ.map fun r => A.e * incA (I.rec7 l Z) r) + M • v → A.xi i hi (A.chOf i c) (A.chOf (i + 1) c') γ₀ = B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) γ)) := by
  intro B X I hok hpins l Z u a Ch A hA i hi c c' g g' hg hg' hy hy'
  have hi0 := Nat.le_of_succ_le hi
  obtain ⟨d, hd, h1⟩ := GlobalTheory.AdForm.CongAtIdem.cong_at_idem ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))
    (rankN (I.rec7 l Z) i hi0) (rankN (I.rec7 l Z) (i + 1) hi) A.e _ hA.idem
  have hd0 := GlobalTheory.Mem.Df.disjoint_vGs_Q I hok l a
  have hQ := GlobalTheory.Mem.Col2.ColIn.Q_subset_SQ I a
  have hb := hA.base i hi0 (A.chOf i c)
  have hb' := hA.base (i + 1) hi (A.chOf (i + 1) c')
  have hr := hA.rep i hi0 c
  have hr' := hA.rep (i + 1) hi c'
  have hq := (hA.reads i hi0).pt c
  have hq' := (hA.reads (i + 1) hi).pt c'
  obtain ⟨M₀, hM₀, h2⟩ := xiAt_transport_tw I l hok u a i hi (A.b0 i (A.chOf i c)) (A.b0 (i + 1) (A.chOf (i + 1) c'))
    (A.p0 i (A.chOf i c)) ((I.stp u a i).rep c) (A.p0 (i + 1) (A.chOf (i + 1) c')) ((I.stp u a (i + 1)).rep c')
    (A.kb i (A.chOf i c)) (((A.K i hi0 (A.chOf i c)).y ⟨c, rfl⟩).1)
    (A.kb (i + 1) (A.chOf (i + 1) c')) (((A.K (i + 1) hi (A.chOf (i + 1) c')).y ⟨c', rfl⟩).1)
    (hb.1.of_extTo hQ hd0) hb.2 (hb'.1.of_extTo hQ hd0) hb'.2 (hq.of_extTo hQ hd0) (hq'.of_extTo hQ hd0) hr.2 hr'.2
  refine ⟨d * M₀, Nat.mul_pos hd hM₀, fun γ γ₀ v hv _ hγ => ?_⟩
  have hc := h1 g g' _ _ hy hy' M₀ γ γ₀ v hv hγ
  refine congrArg B.embLL ((h2 _ _ hc).trans ?_)
  rw [← hr.1, ← hr'.1]
  rfl

end GlobalTheory.AdForm.TwResid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartBasePairDatumRationalApproxEqTwistedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartBasePair_datum_rational_approx_eq_twisted : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) g g', g ∈ GfC _ → g' ∈ GfC _ → finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) g = ((A.K i (Nat.le_of_succ_le hi) (A.chOf i c)).y ⟨c, rfl⟩).1.1 → finM _ (rankN (I.rec7 l Z) (i + 1) hi) g' = ((A.K (i + 1) hi (A.chOf (i + 1) c')).y ⟨c', rfl⟩).1.1 → ∃ M : ℕ, 0 < M ∧ ∀ (γ γ₀ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → γ₀.map (fun r => A.e * incA (I.rec7 l Z) r) = actO _ _ g⁻¹ g'⁻¹ (γ.map fun r => A.e * incA (I.rec7 l Z) r) + M • v → A.xi i hi (A.chOf i c) (A.chOf (i + 1) c') γ₀ = B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) γ)) := by
  first | exact @GlobalTheory.AdForm.TwResid.tw_resid_datum | exact GlobalTheory.AdForm.TwResid.tw_resid_datum | (intros; apply GlobalTheory.AdForm.TwResid.tw_resid_datum <;> assumption)
end

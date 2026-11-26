module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IteratedDerivLine
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.Jet.Line

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

theorem smooth_comb {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f') : SmoothOnG ε (fun h => f h + c * f' h) := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, e⟩ := hf g hg
  obtain ⟨U', F', hU', hgU', hF', e'⟩ := hf' g hg
  refine ⟨U ∩ U', fun h => F h + c * F' h, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (contDiffOn_const.mul (hF'.mono Set.inter_subset_right)), ?_⟩
  intro x hx hxJ
  simp only [e x hx.1 hxJ, e' x hx.2 hxJ]

theorem smooth_word {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f)
    (w : List (Fin n × Fin n)) : SmoothOnG ε (Eword ε w f) := by
  induction w with
  | nil => exact hf
  | cons p w ih =>
    have hc := cpartMem n ε (Matrix.single p.1 p.2 1)
    exact smooth_comb Complex.I (rdSmooth n ε _ _ ih hc.1) (rdSmooth n ε _ _ ih hc.2.1)

theorem word_comb {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f') (w : List (Fin n × Fin n)) :
    ∀ g, inUJ ε g → Eword ε w (fun h => f h + c * f' h) g = Eword ε w f g + c * Eword ε w f' g := by
  induction w with
  | nil => intro g _; rfl
  | cons p w ih =>
    intro g hg
    have hc := cpartMem n ε (Matrix.single p.1 p.2 1)
    have h1 := Eword_congr ε ih [p] g hg
    have h2 := fun X hX => (rdLin n ε _ _ X X 0 c g (smooth_word hf w) (smooth_word hf' w) hX hX hg).2.2
    refine Eq.trans h1 ?_
    simp only [Eword, Eab, Ec, id, h2 _ hc.1, h2 _ hc.2.1]
    ring

theorem word_append (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (w v : List (Fin n × Fin n)) :
    Eword ε (w ++ v) f = Eword ε w (Eword ε v f) := by
  induction w with
  | nil => rfl
  | cons p w ih => simp only [List.cons_append, Eword, ih]

def ZeroJet (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  SmoothOnG ε f ∧ ∀ w : List (Fin n × Fin n), Eword ε w f 1 = 0

theorem one_mem : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]

theorem zeroJet_zero : ZeroJet ε (fun _ => 0) := by
  refine ⟨fun g _ => ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩, fun w => ?_⟩
  cases w with
  | nil => rfl
  | cons p w => rw [Eword_const]

theorem zeroJet_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i, ZeroJet ε (F i)) : ZeroJet ε (fun g => ∑ i ∈ s, c i * F i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zeroJet_zero
  | insert i s hi ih =>
    have e : (fun g => ∑ j ∈ insert i s, c j * F j g) = fun g => (∑ j ∈ s, c j * F j g) + c i * F i g := by
      funext g; rw [Finset.sum_insert hi, add_comm]
    rw [e]
    refine ⟨smooth_comb _ ih.1 (hF i).1, fun w => ?_⟩
    rw [word_comb _ ih.1 (hF i).1 w 1 one_mem, ih.2, (hF i).2]
    simp

theorem cpart1_smul (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε (c • Z) = c.re • cpart1 ε Z + (-c.im) • cpart2 ε Z := by
  have hI : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by
    field_simp; simp
  simp only [cpart1, cpart2, hI, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
  generalize Jm ε * Zᴴ * Jm ε = W
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Complex.real_smul]
  apply Complex.ext <;> simp <;> ring

theorem cpart2_smul (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε (c • Z) = c.re • cpart2 ε Z + c.im • cpart1 ε Z := by
  have hI : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by
    field_simp; simp
  simp only [cpart1, cpart2, hI, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
  generalize Jm ε * Zᴴ * Jm ε = W
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Complex.real_smul]
  apply Complex.ext <;> simp <;> ring

theorem rd_eq_sum {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    Rd X f g = ∑ p : Fin n × Fin n, X p.1 p.2 * Eab ε p.1 p.2 f g := by
  obtain ⟨U, F, hU, hgU, hF, e⟩ := hf g hg
  have hE : ∀ Z, Ec ε Z f g =
      fderiv ℝ F g (g * cpart1 ε Z) + Complex.I * fderiv ℝ F g (g * cpart2 ε Z) := fun Z => by
    have hc := cpartMem n ε Z
    simp only [Ec, rdExt n ε f F U g _ hU hgU hg hF e hc.1, rdExt n ε f F U g _ hU hgU hg hF e hc.2.1]
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun Z => Ec ε Z f g
      map_add' := fun Y Z => by
        have h1 : cpart1 ε (Y + Z) = cpart1 ε Y + cpart1 ε Z := by
          simp only [cpart1, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]
          congr 1; abel
        have h2 : cpart2 ε (Y + Z) = cpart2 ε Y + cpart2 ε Z := by
          simp only [cpart2, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]
          congr 1; abel
        simp only [hE, h1, h2, Matrix.mul_add, map_add (f := _)]
        ring
      map_smul' := fun c Z => by
        simp only [hE, cpart1_smul, cpart2_smul, Matrix.mul_add, Matrix.mul_smul, map_add (f := _), map_smul,
          RingHom.id_apply, smul_eq_mul, Complex.real_smul]
        apply Complex.ext <;> simp <;> ring }
  have hc := (cpartMem n ε X).2.2.2 hX
  have h0 : Rd X f g = L X := by
    change _ = Ec ε X f g
    rw [hE, hc.1, hc.2, rdExt n ε f F U g _ hU hgU hg hF e hX]
    simp
  have h1 : X = ∑ p : Fin n × Fin n, X p.1 p.2 • Matrix.single p.1 p.2 (1 : ℂ) := by
    rw [Fintype.sum_prod_type]
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp
  rw [h0]
  conv_lhs => rw [h1]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul]
  rfl

theorem zeroJet_rd {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : ZeroJet ε f) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) : ZeroJet ε (Rd X f) := by
  refine ⟨rdSmooth n ε _ _ hf.1 hX, fun w => ?_⟩
  rw [Eword_congr ε (rd_eq_sum hf.1 hX) w 1 one_mem]
  refine (zeroJet_sum Finset.univ (fun p : Fin n × Fin n => X p.1 p.2) (fun p => Eab ε p.1 p.2 f)
    (fun p => ⟨smooth_word hf.1 [p], fun v => ?_⟩)).2 w
  have := hf.2 (v ++ [p])
  rwa [word_append] at this

theorem deriv_line (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    deriv (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => Rd X f (NormedSpace.exp ((t : ℂ) • X)) := by
  funext s
  simp only [Rd, ← oneParam n X s]
  rw [deriv_comp_const_add (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) s 0, add_zero]

theorem iteratedDeriv_line {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (j : ℕ) :
    ∀ f : Matrix (Fin n) (Fin n) ℂ → ℂ, ZeroJet ε f →
      iteratedDeriv j (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) 0 = 0 := by
  induction j with
  | zero =>
    intro f hf
    simpa [Eword] using hf.2 []
  | succ j ih =>
    intro f hf
    rw [iteratedDeriv_succ', deriv_line]
    exact ih _ (zeroJet_rd hf hX)

theorem vanish_of_zero_jet : ∀ (n : ℕ) (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (X : Matrix (Fin n) (Fin n) ℂ), SmoothOnG ε f → inG ε X → (∀ w : List (Fin n × Fin n), Eword ε w f 1 = 0) → AnalyticOnNhd ℝ (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) Set.univ → f (NormedSpace.exp X) = 0 := by
  intro n ε f X hf hX hw hA
  have htop : analyticOrderAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) 0 = ⊤ := by
    refine ENat.eq_top_iff_forall_ge.2 fun m => ?_
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hA 0 trivial)).2
      fun i _ => iteratedDeriv_line hX i f ⟨hf, hw⟩
  have h := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
    (analyticOrderAt_eq_top.1 htop) (Set.mem_univ 1)
  simpa using h

end GlobalTheory.Jet.Line
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IpLEqZeroOfMemSpan
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas Formalism.REAL

noncomputable section

namespace GlobalTheory.NilCov

variable {n : ℕ} {ε : Fin n → Bool}

def ipL (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℝ where
  toFun X := ((X * Yᴴ).trace).re
  map_add' X X' := by simp [add_mul]
  map_smul' a X := by simp

theorem ipL_apply (X Y : Matrix (Fin n) (Fin n) ℂ) : ipL Y X = ((X * Yᴴ).trace).re := rfl

theorem ipL_comm (X Y : Matrix (Fin n) (Fin n) ℂ) : ipL Y X = ipL X Y := by
  rw [ipL_apply, ipL_apply]

  have hswap : Y * Xᴴ = (X * Yᴴ)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  rw [hswap, trace_conjTranspose, Complex.star_def, Complex.conj_re]

private theorem Jm_sq_lemma : Jm ε * Jm ε = 1 := by
  rw [Jm, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  by_cases ha : ε a <;> simp [ha]

private theorem Jm_conjTransposeFlagMeasures' : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, diagonal_conjTranspose]
  congr 1
  funext a
  by_cases ha : ε a <;> simp [ha]

private theorem Jm_mul_Jm_mulFlagMeasures (M : Matrix (Fin n) (Fin n) ℂ) : Jm ε * (Jm ε * M) = M := by
  rw [← Matrix.mul_assoc, Jm_sq_lemma, Matrix.one_mul]

theorem inv_eq_neg_of_inG {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) : Jm ε * Yᴴ * Jm ε = -Y := by
  have h0 : Yᴴ * Jm ε + Jm ε * Y = 0 := h
  have h1 : Yᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left h0
  rw [Matrix.mul_assoc, h1, Matrix.mul_neg, Jm_mul_Jm_mulFlagMeasures]

theorem inG_sub_inv (X : Matrix (Fin n) (Fin n) ℂ) : inG ε (X - Jm ε * Xᴴ * Jm ε) := by
  show (X - Jm ε * Xᴴ * Jm ε)ᴴ * Jm ε + Jm ε * (X - Jm ε * Xᴴ * Jm ε) = 0
  simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, Jm_conjTransposeFlagMeasures',
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Jm_sq_lemma, Jm_mul_Jm_mulFlagMeasures, Matrix.mul_one]
  abel

theorem ipL_inv {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) (X : Matrix (Fin n) (Fin n) ℂ) :
    ipL Y (Jm ε * Xᴴ * Jm ε) = -ipL Y X := by
  have h0 : Yᴴ * Jm ε + Jm ε * Y = 0 := h
  have h1 : Jm ε * Y = -(Yᴴ * Jm ε) := eq_neg_of_add_eq_zero_right h0

  have hY : Jm ε * Y * Jm ε = -Yᴴ := by
    rw [h1, Matrix.neg_mul, Matrix.mul_assoc, Jm_sq_lemma, Matrix.mul_one]
  have hstar : (Jm ε * Xᴴ * Jm ε)ᴴ = Jm ε * X * Jm ε := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Jm_conjTransposeFlagMeasures', Matrix.mul_assoc]
  have htr : (Y * (Jm ε * X * Jm ε)).trace = -(X * Yᴴ).trace :=
    calc (Y * (Jm ε * X * Jm ε)).trace = ((Y * (Jm ε * X)) * Jm ε).trace := by
          simp only [Matrix.mul_assoc]
      _ = (Jm ε * (Y * (Jm ε * X))).trace := Matrix.trace_mul_comm _ _
      _ = (Jm ε * Y * Jm ε * X).trace := by simp only [Matrix.mul_assoc]
      _ = (-Yᴴ * X).trace := by rw [hY]
      _ = -(X * Yᴴ).trace := by rw [Matrix.neg_mul, Matrix.trace_neg, Matrix.trace_mul_comm]
  rw [ipL_comm, ipL_apply, ipL_apply, hstar, htr, Complex.neg_re]

theorem ipL_sub_inv {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) (X : Matrix (Fin n) (Fin n) ℂ) :
    ipL Y (X - Jm ε * Xᴴ * Jm ε) = 2 * ipL Y X := by
  rw [map_sub, ipL_inv h]
  ring

theorem add_inv_eq (g : UJ ε) :
    (uMat g - 1) + Jm ε * (uMat g - 1)ᴴ * Jm ε = -(Jm ε * (uMat g - 1)ᴴ * Jm ε * (uMat g - 1)) := by
  have hg : (uMat g)ᴴ * Jm ε * uMat g = Jm ε := g.2

  have key : Jm ε * (uMat g)ᴴ * Jm ε * uMat g = 1 := by
    calc Jm ε * (uMat g)ᴴ * Jm ε * uMat g = Jm ε * ((uMat g)ᴴ * Jm ε * uMat g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, Jm_sq_lemma]
  have e : Jm ε * (uMat g - 1)ᴴ * Jm ε = Jm ε * (uMat g)ᴴ * Jm ε - 1 := by
    rw [conjTranspose_sub, conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Jm_sq_lemma]
  rw [e, Matrix.sub_mul, Matrix.mul_sub, key, Matrix.mul_one, Matrix.one_mul]
  abel

variable {d : ℕ} {E : Fin d → Matrix (Fin n) (Fin n) ℂ}

theorem ipL_eq_zero_of_mem_span
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) {s : Set (Fin d)} {i : Fin d}
    (hi : i ∉ s) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ Submodule.span ℝ (E '' s)) : ipL (E i) X = 0 := by
  have hle : Submodule.span ℝ (E '' s) ≤ LinearMap.ker (ipL (E i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    have hji : j ≠ i := fun e => hi (e ▸ hj)
    simp [LinearMap.mem_ker, ipL_apply, hE, hji]
  exact hle hX

theorem eq_sum_of_mem_span
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ Submodule.span ℝ (Set.range E)) : X = ∑ i, ipL (E i) X • E i := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hX
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1

  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, ipL_apply, hE]

theorem ipL_eq_zero_of_mem
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) (hG : ∀ i, inG ε (E i))
    {B : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)} (hB : ∀ X ∈ B, Jm ε * Xᴴ * Jm ε ∈ B) {s : Set (Fin d)}
    (hs : ∀ X, X ∈ B ∧ inG ε X → X ∈ Submodule.span ℝ (E '' s)) {i : Fin d} (hi : i ∉ s)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ B) : ipL (E i) X = 0 := by
  have hZ : X - Jm ε * Xᴴ * Jm ε ∈ Submodule.span ℝ (E '' s) :=
    hs _ ⟨B.sub_mem hX (hB X hX), inG_sub_inv X⟩
  have h0 := ipL_eq_zero_of_mem_span hE hi hZ
  rw [ipL_sub_inv (hG i)] at h0
  linarith

theorem sub_mem_of_coord_eq {A : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)} {deg : Fin d → ℕ}
    (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (hinv : ∀ c, ∀ X ∈ A c, Jm ε * Xᴴ * Jm ε ∈ A c)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hsp : ∀ c X, (X ∈ A c ∧ inG ε X) ↔ X ∈ Submodule.span ℝ (E '' {i | c ≤ deg i}))
    {g h : UJ ε} (hg : uMat g - 1 ∈ A 0) (hh : uMat h - 1 ∈ A 0) (c : ℕ)
    (hc : ∀ i, deg i < c → ipL (E i) (uMat g - 1) = ipL (E i) (uMat h - 1)) :
    uMat g - uMat h ∈ A c := by

  have hGi : ∀ i, inG ε (E i) := fun i =>
    ((hsp 0 (E i)).2 (Submodule.subset_span ⟨i, Nat.zero_le _, rfl⟩)).2
  have eX := add_inv_eq g
  have eY := add_inv_eq h
  have hgX : uMat g - 1 ∈ A 0 := hg
  have hhY : uMat h - 1 ∈ A 0 := hh
  revert hc
  generalize uMat g = G at eX eY hgX ⊢
  generalize uMat h = H at eX eY hhY ⊢
  induction c with
  | zero =>
    intro _
    have h0 := (A 0).sub_mem hgX hhY
    rwa [sub_sub_sub_cancel_right] at h0
  | succ c ih =>
    intro hc
    have hD : G - H ∈ A c := ih fun i hi => hc i (Nat.lt_succ_of_lt hi)
    have hθD : Jm ε * (G - H)ᴴ * Jm ε ∈ A c := hinv c _ hD
    have hDXY : G - H = (G - 1) - (H - 1) := (sub_sub_sub_cancel_right G H 1).symm

    have hsym : (G - H) + Jm ε * (G - H)ᴴ * Jm ε ∈ A (c + 1) := by
      have hθ : Jm ε * (G - H)ᴴ * Jm ε = Jm ε * (G - 1)ᴴ * Jm ε - Jm ε * (H - 1)ᴴ * Jm ε := by
        rw [hDXY, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
      have hprod : (G - H) + Jm ε * (G - H)ᴴ * Jm ε =
          -(Jm ε * (G - 1)ᴴ * Jm ε * (G - H) + Jm ε * (G - H)ᴴ * Jm ε * (H - 1)) := by
        rw [hθ, hDXY, Matrix.mul_sub, Matrix.sub_mul]
        calc (G - 1) - (H - 1) + (Jm ε * (G - 1)ᴴ * Jm ε - Jm ε * (H - 1)ᴴ * Jm ε)
            = ((G - 1) + Jm ε * (G - 1)ᴴ * Jm ε) - ((H - 1) + Jm ε * (H - 1)ᴴ * Jm ε) := by abel
          _ = -(Jm ε * (G - 1)ᴴ * Jm ε * (G - 1)) - -(Jm ε * (H - 1)ᴴ * Jm ε * (H - 1)) := by
            rw [eX, eY]
          _ = _ := by abel
      rw [hprod]
      refine (A (c + 1)).neg_mem ((A (c + 1)).add_mem ?_ ?_)
      · exact (hmul c _ hD _ (hinv 0 _ hgX)).2
      · exact (hmul c _ hθD _ hhY).1

    have hW : (G - H) - Jm ε * (G - H)ᴴ * Jm ε ∈ A (c + 1) := by
      have hWc : (G - H) - Jm ε * (G - H)ᴴ * Jm ε ∈ A c := (A c).sub_mem hD hθD
      have hWsp := (hsp c _).1 ⟨hWc, inG_sub_inv (G - H)⟩
      have hWr : (G - H) - Jm ε * (G - H)ᴴ * Jm ε ∈ Submodule.span ℝ (Set.range E) :=
        Submodule.span_mono (Set.image_subset_range _ _) hWsp
      have hcoord : ∀ i, deg i < c + 1 → ipL (E i) ((G - H) - Jm ε * (G - H)ᴴ * Jm ε) = 0 := by
        intro i hi
        rw [ipL_sub_inv (hGi i), hDXY, map_sub, hc i hi, sub_self, mul_zero]
      have hsum := eq_sum_of_mem_span hE hWr
      have hspan : (G - H) - Jm ε * (G - H)ᴴ * Jm ε ∈ Submodule.span ℝ (E '' {i | c + 1 ≤ deg i}) := by
        rw [hsum]
        refine Submodule.sum_mem _ fun i _ => ?_
        by_cases hi : c + 1 ≤ deg i
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
        · rw [hcoord i (by omega), zero_smul]
          exact Submodule.zero_mem _
      exact ((hsp (c + 1) _).2 hspan).1
    have h2 : (2 : ℝ) • (G - H) ∈ A (c + 1) := by
      have hs2 := (A (c + 1)).add_mem hsym hW
      convert hs2 using 1
      rw [two_smul]
      abel
    have h1 := (A (c + 1)).smul_mem (1 / 2 : ℝ) h2
    rwa [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h1

end GlobalTheory.NilCov
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsShuffle
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.ParCoset

open GlobalTheory.FinGL Formalism.L2.DIV Finset

variable {g : ℕ} [Fact g.Prime] {n : ℕ}

theorem inPar_iff (a : ℕ) (M : Mt g n) :
    InPar a M ↔ M.BlockTriangular (fun i : Fin n => if (i : ℕ) < a then 0 else 1) := by
  constructor
  · intro h i j hij
    apply h <;> (dsimp only at hij; split_ifs at hij <;> omega)
  · intro h i j hj hi
    apply h
    dsimp only
    rw [if_pos hj, if_neg (by omega)]
    exact Nat.zero_lt_one

theorem inPar_mul {a : ℕ} {x y : Gn g n} (hx : InPar a (x : Mt g n)) (hy : InPar a (y : Mt g n)) :
    InPar a ((x * y : Gn g n) : Mt g n) := by
  rw [inPar_iff] at *
  exact hx.mul hy

theorem inPar_inv {a : ℕ} {x : Gn g n} (hx : InPar a (x : Mt g n)) : InPar a ((x⁻¹ : Gn g n) : Mt g n) := by
  rw [inPar_iff] at *
  rw [Matrix.coe_units_inv]
  haveI := x.invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular hx

def pMat (g : ℕ) [Fact g.Prime] (σ : Equiv.Perm (Fin n)) : Mt g n := fun r j => if r = σ j then 1 else 0

theorem pMat_mul (σ τ : Equiv.Perm (Fin n)) : pMat g σ * pMat g τ = pMat g (σ * τ) := by
  ext r j
  simp [pMat, Matrix.mul_apply]
  congr

theorem pMat_one : pMat g (1 : Equiv.Perm (Fin n)) = 1 := by
  ext r j
  simp [pMat, Matrix.one_apply]
  congr

def pU (g : ℕ) [Fact g.Prime] (σ : Equiv.Perm (Fin n)) : Gn g n :=
  ⟨pMat g σ, pMat g σ⁻¹, by rw [pMat_mul, mul_inv_cancel, pMat_one], by rw [pMat_mul, inv_mul_cancel, pMat_one]⟩

theorem pU_mul (σ τ : Equiv.Perm (Fin n)) : pU g (σ * τ) = pU g σ * pU g τ :=
  Units.ext (pMat_mul σ τ).symm

theorem inPar_pU {a : ℕ} {τ : Equiv.Perm (Fin n)} (h : ∀ j, (τ j : ℕ) < a ↔ (j : ℕ) < a) :
    InPar a ((pU g τ : Gn g n) : Mt g n) := by
  intro i j hj hi
  have : i ≠ τ j := by
    rintro rfl
    have := (h j).2 hj
    omega
  exact if_neg this

noncomputable def rk (a c : ℕ) (M : Mt g n) : ℕ :=
  (Matrix.diagonal (fun i : Fin n => if c ≤ (i : ℕ) then (1 : ZMod g) else 0) * M *
    Matrix.diagonal (fun j : Fin n => if (j : ℕ) < a then (1 : ZMod g) else 0)).rank

theorem rk_le {a c : ℕ} {p q : Mt g n} (hp : InPar c p) (hq : InPar a q) (M : Mt g n) :
    rk a c (p * M * q) ≤ rk a c M := by
  unfold rk
  set F : Mt g n := Matrix.diagonal (fun i : Fin n => if c ≤ (i : ℕ) then (1 : ZMod g) else 0) with hF
  set E : Mt g n := Matrix.diagonal (fun j : Fin n => if (j : ℕ) < a then (1 : ZMod g) else 0) with hE
  have h1 : F * p = F * p * F := by
    ext i j
    simp only [hF, Matrix.mul_diagonal, Matrix.diagonal_mul]
    split_ifs with h h'
    · simp
    · rw [hp i j (by omega) h]; simp
    · simp
    · simp
  have h2 : q * E = E * (q * E) := by
    ext i j
    simp only [hE, Matrix.mul_diagonal, Matrix.diagonal_mul]
    split_ifs with h h'
    · simp
    · rw [hq i j h (by omega)]; simp
    · simp
    · simp
  have h3 : F * (p * M * q) * E = (F * p) * ((F * M * E) * (q * E)) := by
    calc F * (p * M * q) * E = (F * p) * M * (q * E) := by simp only [Matrix.mul_assoc]
      _ = (F * p * F) * M * (E * (q * E)) := by rw [← h1, ← h2]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h3]
  exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_mul_le_left _ _)

theorem rk_eq {a c : ℕ} {p q : Gn g n} (hp : InPar c (p : Mt g n)) (hq : InPar a (q : Mt g n)) (x : Gn g n) :
    rk a c ((p * x * q : Gn g n) : Mt g n) = rk a c (x : Mt g n) := by
  refine le_antisymm (rk_le hp hq _) ?_
  have h := rk_le (inPar_inv hp) (inPar_inv hq) ((p * x * q : Gn g n) : Mt g n)
  rw [← Units.val_mul, ← Units.val_mul] at h
  have e : p⁻¹ * (p * x * q) * q⁻¹ = x := by group
  rwa [e] at h

theorem rk_pU (a c : ℕ) (σ : Equiv.Perm (Fin n)) :
    rk a c ((pU g σ : Gn g n) : Mt g n) = #{j : Fin n | (j : ℕ) < a ∧ ¬ (σ j : ℕ) < c} := by
  unfold rk
  have h : Matrix.diagonal (fun i : Fin n => if c ≤ (i : ℕ) then (1 : ZMod g) else 0) *
      ((pU g σ : Gn g n) : Mt g n) *
      Matrix.diagonal (fun j : Fin n => if (j : ℕ) < a then (1 : ZMod g) else 0) =
      ((pU g σ : Gn g n) : Mt g n) *
      Matrix.diagonal (fun j : Fin n => if (j : ℕ) < a ∧ ¬ (σ j : ℕ) < c then (1 : ZMod g) else 0) := by
    ext r j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, pU, pMat]
    by_cases hr : r = σ j
    · subst hr
      by_cases h1 : (j : ℕ) < a <;> by_cases h2 : c ≤ (σ j : ℕ) <;> simp [h1, h2]
    · simp [hr]
  rw [h, Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnits_det_units _), Matrix.rank_diagonal,
    Fintype.card_subtype]
  congr 1
  ext j
  simp

theorem card_lt {a : ℕ} (ha : a ≤ n) (σ : Equiv.Perm (Fin n)) : #{j : Fin n | (σ j : ℕ) < a} = a := by
  have h : #{j : Fin n | (σ j : ℕ) < a} = #{j : Fin n | (j : ℕ) < a} :=
    Finset.card_equiv σ (by simp)
  rw [h, Fin.card_filter_val_lt]
  omega

theorem card_lt' {a : ℕ} (ha : a ≤ n) : #{j : Fin n | (j : ℕ) < a} = a := by
  rw [Fin.card_filter_val_lt]
  omega

theorem card_split (P Q : Fin n → Prop) [DecidablePred P] [DecidablePred Q] :
    #{j : Fin n | P j ∧ Q j} + #{j : Fin n | P j ∧ ¬ Q j} = #{j : Fin n | P j} := by
  rw [← Finset.filter_filter, ← Finset.filter_filter, Finset.card_filter_add_card_filter_not]

theorem card_split' (P Q : Fin n → Prop) [DecidablePred P] [DecidablePred Q] :
    #{j : Fin n | P j ∧ Q j} + #{j : Fin n | ¬ P j ∧ Q j} = #{j : Fin n | Q j} := by
  rw [← card_split Q P]
  simp only [and_comm]

theorem card_not (P : Fin n → Prop) [DecidablePred P] :
    #{j : Fin n | P j} + #{j : Fin n | ¬ P j} = n := by
  rw [Finset.card_filter_add_card_filter_not]
  simp

theorem exists_young {a c : ℕ} (ha : a ≤ n) (hc : c ≤ n) (σ s : Equiv.Perm (Fin n))
    (h : #{j : Fin n | (j : ℕ) < a ∧ ¬ (σ j : ℕ) < c} = #{j : Fin n | (j : ℕ) < a ∧ ¬ (s j : ℕ) < c}) :
    ∃ t₁ t₂ : Equiv.Perm (Fin n), (∀ j, (t₁ j : ℕ) < c ↔ (j : ℕ) < c) ∧ (∀ j, (t₂ j : ℕ) < a ↔ (j : ℕ) < a) ∧
      σ = t₁ * s * t₂ := by
  let f : Equiv.Perm (Fin n) → Fin n → Bool × Bool := fun τ j => (decide ((j : ℕ) < a), decide ((τ j : ℕ) < c))
  have hcard : ∀ y, Fintype.card {j // f σ j = y} = Fintype.card {j // f s j = y} := by
    have e1 := card_split (fun j : Fin n => (j : ℕ) < a) (fun j => (σ j : ℕ) < c)
    have e2 := card_split (fun j : Fin n => (j : ℕ) < a) (fun j => (s j : ℕ) < c)
    have e3 := card_split' (fun j : Fin n => (j : ℕ) < a) (fun j => (σ j : ℕ) < c)
    have e4 := card_split' (fun j : Fin n => (j : ℕ) < a) (fun j => (s j : ℕ) < c)
    have e5 := card_split (fun j : Fin n => ¬ (j : ℕ) < a) (fun j => (σ j : ℕ) < c)
    have e6 := card_split (fun j : Fin n => ¬ (j : ℕ) < a) (fun j => (s j : ℕ) < c)
    rw [card_lt hc] at e3 e4
    rintro ⟨y₁, y₂⟩
    rw [Fintype.card_subtype, Fintype.card_subtype]
    cases y₁ <;> cases y₂ <;>
      simp only [f, Prod.mk.injEq, decide_eq_true_eq, decide_eq_false_iff_not] <;> omega
  let t₂ : Equiv.Perm (Fin n) := Equiv.ofFiberEquiv fun y => Fintype.equivOfCardEq (hcard y)
  have ht : ∀ j, f s (t₂ j) = f σ j := fun j => Equiv.ofFiberEquiv_map _ j
  refine ⟨σ * t₂⁻¹ * s⁻¹, t₂, fun j => ?_, fun j => ?_, by group⟩
  · have := congrArg Prod.snd (ht (t₂⁻¹ (s⁻¹ j)))
    simpa [f] using this.symm
  · have := congrArg Prod.fst (ht j)
    simpa [f] using this

theorem exists_shuffle {a b c i : ℕ} (hn : n = a + b) (hia : i ≤ a) (hic : i ≤ c) (hb : c - i ≤ b) :
    ∃ s : Equiv.Perm (Fin n), wI g a c i n = pU g s ∧
      #{j : Fin n | (j : ℕ) < a ∧ ¬ (s j : ℕ) < c} = a - i := by
  let f : Fin n → Fin n := fun j => ⟨sigI a c i j, by
    have := j.2
    unfold sigI
    split_ifs <;> omega⟩
  have hf : Function.Injective f := by
    intro j k h
    have h' : sigI a c i j = sigI a c i k := congrArg Fin.val h
    apply Fin.ext
    unfold sigI at h'
    split_ifs at h' <;> omega
  let s : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
  have hs : ∀ j, (s j : ℕ) = sigI a c i j := fun _ => rfl
  refine ⟨s, ?_, ?_⟩
  · have e : (fun r j : Fin n => if (r : ℕ) = sigI a c i j then (1 : ZMod g) else 0) =
        ((pU g s : Gn g n) : Mt g n) := by
      funext r j
      simp only [pU, pMat, ← hs, Fin.val_inj]
    unfold wI toG
    rw [e, dite_eq_left (Units.isUnit _), IsUnit.unit_of_val_units]
  · have e1 := card_split (fun j : Fin n => (j : ℕ) < a) (fun j => (s j : ℕ) < c)
    have e2 : #{j : Fin n | (j : ℕ) < a ∧ (s j : ℕ) < c} = #{j : Fin n | (j : ℕ) < i} := by
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs, sigI]
      split_ifs <;> omega
    have e3 := card_lt' (a := a) (n := n) (by omega)
    have e4 := card_lt' (a := i) (n := n) (by omega)
    omega

theorem exists_perm (a c : ℕ) (x : Gn g n) : ∃ σ : Equiv.Perm (Fin n), ∃ p q : Gn g n,
    InPar c (p : Mt g n) ∧ InPar a (q : Mt g n) ∧ x = p * pU g σ * q := by
  obtain ⟨m, u, hu, u', hu', h⟩ := Bruhat.exists_decomp x
  have hup : ∀ (e : ℕ) (v : Gn g n), v ∈ unip (ZMod g) n → InPar e (v : Mt g n) := fun e v hv i j hj hi =>
    unip_lower hv (show j < i from Fin.lt_def.2 (by omega))
  let D : Gn g n := ⟨Matrix.diagonal fun j => (m.2 j : ZMod g), Matrix.diagonal fun j => ((m.2 j)⁻¹ : (ZMod g)ˣ),
    by simp only [Matrix.diagonal_mul_diagonal, Units.mul_inv, Matrix.diagonal_one],
    by simp only [Matrix.diagonal_mul_diagonal, Units.inv_mul, Matrix.diagonal_one]⟩
  have hD : InPar a (D : Mt g n) := fun i j hj hi =>
    Matrix.diagonal_apply_ne _ (by rintro rfl; omega)
  refine ⟨m.1, u, D * u', hup c u hu, inPar_mul hD (hup a u' hu'), Units.ext ?_⟩
  have e : Bruhat.mono m = ((pU g m.1 : Gn g n) : Mt g n) * (D : Mt g n) := by
    ext r j
    simp [Bruhat.mono, pU, pMat, D, Matrix.mul_diagonal]
  rw [h, e]
  simp only [Units.val_mul, Matrix.mul_assoc]

theorem doubleCoset : ∀ (g : ℕ) [Fact g.Prime] (a b c d n : ℕ), n = a + b → n = c + d → ∀ x : Gn g n, ∃! i : ℕ, i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b) ∧ ∃ p q : Gn g n, InPar c (p : Mt g n) ∧ InPar a (q : Mt g n) ∧ x = p * wI g a c i n * q := by
  intro g _ a b c d n hab hcd x
  have key : ∀ i : ℕ, (i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b) ∧ ∃ p q : Gn g n,
      InPar c (p : Mt g n) ∧ InPar a (q : Mt g n) ∧ x = p * wI g a c i n * q) →
      i = a - rk a c (x : Mt g n) := by
    rintro i ⟨hi, p, q, hp, hq, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨s, hs, hc⟩ := exists_shuffle (g := g) hab (by omega : i ≤ a) hi.2.1 hi.2.2
    rw [rk_eq hp hq, hs, rk_pU, hc]
    omega
  refine existsUnique_of_exists_of_unique ?_ fun i j hi hj => (key i hi).trans (key j hj).symm
  obtain ⟨σ, p, q, hp, hq, rfl⟩ := exists_perm a c x
  have e1 := card_split (fun j : Fin n => (j : ℕ) < a) (fun j => (σ j : ℕ) < c)
  have e3 := card_split' (fun j : Fin n => (j : ℕ) < a) (fun j => (σ j : ℕ) < c)
  have e5 := card_split (fun j : Fin n => ¬ (j : ℕ) < a) (fun j => (σ j : ℕ) < c)
  have e6 := card_not (fun j : Fin n => (j : ℕ) < a)
  have e7 := card_lt' (a := a) (n := n) (by omega)
  rw [card_lt (by omega)] at e3
  obtain ⟨i, hi⟩ : ∃ i, i = #{j : Fin n | (j : ℕ) < a ∧ (σ j : ℕ) < c} := ⟨_, rfl⟩
  obtain ⟨s, hs, hc⟩ := exists_shuffle (g := g) (i := i) (c := c) hab (by omega) (by omega) (by omega)
  obtain ⟨t₁, t₂, h₁, h₂, ht⟩ := exists_young (a := a) (c := c) (by omega) (by omega) σ s (by omega)
  refine ⟨i, ?_, p * pU g t₁, pU g t₂ * q, inPar_mul hp (inPar_pU h₁), inPar_mul (inPar_pU h₂) hq, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · rw [hs, ht, pU_mul, pU_mul]
    group

end GlobalTheory.GLm.ParCoset
end

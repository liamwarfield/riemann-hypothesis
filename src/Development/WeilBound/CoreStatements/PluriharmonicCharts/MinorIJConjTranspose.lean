module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageCoord

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorIJConjTranspose
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc GlobalTheory.CompanionTheory.Ar.PB.CPts
open scoped ComplexOrder Classical

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_hom

variable {N j : ℕ}

theorem exists_selector (R : Type) [CommRing R] (hj : j ≤ N) (i : Fin N) {I' : Finset (Fin N)}
    (hI : IsStepRows N j i I') : ∃ h : Matrix (Fin N) (Fin N) R, IsBlockDiag j h ∧
      ∀ I, minorIJ h I (stepCols N j i) = if I = I' then 1 else 0 := by
  refine ⟨Matrix.of fun a b => if ∃ s, a = I'.orderEmbOfFin hI.1 s ∧ b = (stepCols N j i).orderEmbOfFin rfl s
    then 1 else 0, fun a b hab => ?_, fun I => ?_⟩
  · rw [Matrix.of_apply, if_neg]
    rintro ⟨s, rfl, rfl⟩
    have h1 := hI.2 (I'.orderEmbOfFin_mem hI.1 s)
    have h2 := mem_stepCols_block hj ((stepCols N j i).orderEmbOfFin_mem rfl s)
    apply hab
    split_ifs at h1 h2 with h
    · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at h1
      omega
    · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at h1
      exact ⟨fun _ => h2, fun _ => h1⟩
  · by_cases e : I = I'
    · subst e
      rw [if_pos rfl, minorIJ, dite_eq_left hI.1]
      refine Eq.trans (congrArg Matrix.det ?_) Matrix.det_one
      ext s t
      simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]
      refine if_congr ⟨?_, ?_⟩ rfl rfl
      · rintro ⟨u, rfl, rfl⟩; rfl
      · rintro rfl; exact ⟨s, rfl, rfl⟩
    · rw [if_neg e]
      by_cases c : I.card = (stepCols N j i).card
      · have hs : ¬ I ⊆ I' := fun hs => e (Finset.eq_of_subset_of_card_le hs (by rw [c, hI.1]))
        obtain ⟨a, ha, has⟩ := Finset.not_subset.mp hs
        refine minorIJ_eq_zero_of_row _ ha fun b _ => ?_
        rw [Matrix.of_apply, if_neg]
        rintro ⟨s, rfl, -⟩
        exact has (I'.orderEmbOfFin_mem hI.1 s)
      · exact minorIJ_of_card_ne _ c

theorem minorIJ_conjTranspose (h : Matrix (Fin N) (Fin N) ℂ) (I J : Finset (Fin N)) :
    minorIJ hᴴ J I = star (minorIJ h I J) := by
  by_cases e : I.card = J.card
  · rw [minorIJ_eq_det h I J _ e rfl, minorIJ_eq_det hᴴ J I _ rfl e, ← Matrix.det_conjTranspose]
    rfl
  · rw [minorIJ_of_card_ne h e, minorIJ_of_card_ne hᴴ (Ne.symm e), star_zero]

theorem gram_minor {G h g : Matrix (Fin N) (Fin N) ℂ} {C : Finset (Fin N)} {a l : ℂ}
    (e : ∀ I, a * minorIJ h I C = l * minorIJ g I C) :
    ‖a‖ ^ 2 * (minorIJ (hᴴ * G * h) C C).re = ‖l‖ ^ 2 * (minorIJ (gᴴ * G * g) C C).re := by
  have key : ∀ (b : ℂ) (f : Matrix (Fin N) (Fin N) ℂ), star b * b * minorIJ (fᴴ * G * f) C C =
      ∑ I', ∑ I, star (b * minorIJ f I C) * minorIJ G I I' * (b * minorIJ f I' C) := by
    intro b f
    rw [minorIJ_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I' _ => ?_
    rw [minorIJ_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [minorIJ_conjTranspose, star_mul]
    ring
  have h1 := key a h
  simp only [e] at h1
  rw [← key l g] at h1
  have n : ∀ b : ℂ, star b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := fun b => by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  rw [n, n] at h1
  simpa only [Complex.re_ofReal_mul] using congrArg Complex.re h1

theorem minor_pos {G : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (C : Finset (Fin N)) : 0 < minorIJ G C C := by
  rw [minorIJ, dite_eq_left rfl]
  exact (hG.submatrix (C.orderEmbOfFin rfl).injective).det_pos

theorem detFac_pos {G : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (i : Fin N) : 0 < (detFac j i G).re := by
  have : 0 < detFac j i G := by
    unfold detFac
    refine mul_pos ?_ ?_ <;> split_ifs
    exacts [minor_pos hG _, one_pos, minor_pos hG _, one_pos]
  exact (Complex.pos_iff.1 this).1

theorem gram_pos {G h : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (hh : h.det ≠ 0) (C : Finset (Fin N)) :
    0 < (minorIJ (hᴴ * G * h) C C).re := by
  have : (hᴴ * G * h).PosDef := hG.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det h).2 hh.isUnit))
  exact (Complex.pos_iff.1 (minor_pos this C)).1

theorem detFac_conjTranspose (i : Fin N) (h : Matrix (Fin N) (Fin N) ℂ) :
    detFac j i hᴴ = star (detFac j i h) := by
  unfold detFac
  rw [minorIJ_conjTranspose, minorIJ_conjTranspose, star_mul']
  split_ifs <;> simp

theorem log_detFac (hj : j ≤ N) (i : Fin N) {G R : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (bG : IsBlockDiag j G)
    (bR : IsBlockDiag j R) (hR : R.det ≠ 0) :
    (1 / 2) * Real.log (detFac j i (Rᴴ * G * R)).re =
      (1 / 2) * Real.log (detFac j i G).re + Real.log ‖detFac j i R‖ := by
  have h0 := norm_ne_zero_iff.2 (detFac_ne_zero hj i bR hR)
  have e : detFac j i (Rᴴ * G * R) = ((‖detFac j i R‖ ^ 2 : ℝ) : ℂ) * detFac j i G := by
    rw [detFac_mul i bR, detFac_mul i bG, detFac_conjTranspose, mul_right_comm, Complex.star_def, Complex.conj_mul']
    push_cast; rfl
  rw [e, Complex.re_ofReal_mul, Real.log_mul (pow_ne_zero _ h0) (detFac_pos hG i).ne', Real.log_pow]
  push_cast; ring

theorem pot_step (hj : j ≤ N) (i : Fin N) (hi : IsProperStep N j i) {G R h h' : Matrix (Fin N) (Fin N) ℂ}
    (hG : G.PosDef) (bG : IsBlockDiag j G) (bR : IsBlockDiag j R) (hR : R.det ≠ 0) (hh : h.det ≠ 0)
    (hh' : h'.det ≠ 0) {a a' μ : ℂ} (ha : a ≠ 0) (ha' : a' ≠ 0) (hμ : μ ≠ 0)
    (e : ∀ I, a * minorIJ h I (stepCols N j i) = a' * detFac j i R * μ * minorIJ (R * h') I (stepCols N j i)) :
    Real.log ‖a‖ + blockPot j i G h = Real.log ‖a'‖ + Real.log ‖μ‖ + blockPot j i (Rᴴ * G * R) h' := by
  have h0 := detFac_ne_zero hj i bR hR
  have h1 := gram_minor (G := G) e
  have p1 := gram_pos hG hh (stepCols N j i)
  have p2 := gram_pos hG (h := R * h') (by rw [Matrix.det_mul]; exact mul_ne_zero hR hh') (stepCols N j i)
  have h2 := congrArg Real.log h1
  rw [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 ha)) p1.ne',
    Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 (mul_ne_zero (mul_ne_zero ha' h0) hμ))) p2.ne',
    Real.log_pow, Real.log_pow, norm_mul, norm_mul,
    Real.log_mul (mul_ne_zero (norm_ne_zero_iff.2 ha') (norm_ne_zero_iff.2 h0)) (norm_ne_zero_iff.2 hμ),
    Real.log_mul (norm_ne_zero_iff.2 ha') (norm_ne_zero_iff.2 h0)] at h2
  have e2 : h'ᴴ * (Rᴴ * G * R) * h' = (R * h')ᴴ * G * (R * h') := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  unfold blockPot
  rw [if_pos hi, if_pos hi, log_detFac hj i hG bG bR hR, e2]
  push_cast at h2
  linarith

theorem pot_base (hj : j ≤ N) (i : Fin N) (hi : ¬ IsProperStep N j i) {G R : Matrix (Fin N) (Fin N) ℂ}
    (h h' : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosDef) (bG : IsBlockDiag j G) (bR : IsBlockDiag j R) (hR : R.det ≠ 0) :
    blockPot j i (Rᴴ * G * R) h' = blockPot j i G h + Real.log ‖detFac j i R‖ := by
  unfold blockPot
  rw [if_neg hi, if_neg hi, log_detFac hj i hG bG bR hR]
  ring

theorem detFac_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (i : Fin N) (A : Matrix (Fin N) (Fin N) R) :
    detFac j i (A.map f) = f (detFac j i A) := by
  unfold detFac
  rw [minorIJ_map, minorIJ_map, map_mul]
  split_ifs <;> simp

theorem pot_conj (i : Fin N) (G h : Matrix (Fin N) (Fin N) ℂ) :
    blockPot j i (G.map (starRingEnd ℂ)) (h.map (starRingEnd ℂ)) = blockPot j i G h := by
  have e : (h.map (starRingEnd ℂ))ᴴ * G.map (starRingEnd ℂ) * h.map (starRingEnd ℂ) =
      (hᴴ * G * h).map (starRingEnd ℂ) := by
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  unfold blockPot
  rw [e, detFac_map, minorIJ_map, Complex.conj_re, Complex.conj_re]

end PositivityTheory.Xgp.c_bm_exists_hom
end
end

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.XFlArith
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace PositivityTheory.Xgp.fl_arith

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter GroundTheory.Heights₂.Heights.CoordinateConeArithVar FlagArithVar

theorem arith_of_trdeg {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
    (hK : Nonempty K) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (d : ℕ)
    (hd : Algebra.trdeg ℤ (Subfield.closure (coneRatios y c)) = (d : Cardinal)) :
    IsArithVar (mCoordIdeal y) (d + 1) := by
  have hhor : IsHorizontal (mCoordIdeal y) := horizontal y
  refine ⟨hK, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal y, relevant y _ hc⟩, hhor, ?_⟩
  have htr := ConeTrdeg.full _ ι (CoordinateConeArithVar.ratioField y c) (ratioPtL y c) (birational y _ hc)
    (fun k ↦ ⟨c k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [ratioPtL, ratioPt, hc] at h1⟩)
    (by rw [mCoordIdeal_ratioPtL y _ hc]; exact hhor)
  have hL : Algebra.trdeg ℤ (CoordinateConeArithVar.ratioField y c) = ((d : ℕ) : Cardinal) := by
    rw [CoordinateConeArithVar.ratioField, trdeg_int_adjoin]
    exact hd
  rw [mCoordIdeal_ratioPtL y _ hc, hL] at htr
  have : (mCoordIdeal y).IsPrime := RingHom.ker_isPrime _
  have hA := IntDomainDim.full (MRing ι ⧸ mCoordIdeal y) (algebraMap_injective _ hhor)
  rw [hA, htr, ← Nat.cast_add, Cardinal.toENat_nat]
  push_cast
  ring

theorem trdeg_lt {Ω : Type} [Field Ω] [CharZero Ω] (L' L : Subfield Ω) (h : L' ≤ L) (t : Ω) (ht : t ∈ L)
    (σ : ℕ → Ω →+* Ω) (hσ : ∀ n, ∀ x ∈ L', σ n x = x) (hinj : Function.Injective fun n => σ n t) (D : ℕ)
    (hD : Algebra.trdeg ℤ L = (D : Cardinal)) : ∃ d < D, Algebra.trdeg ℤ L' = (d : Cardinal) := by
  letI : Algebra L' L := (Subfield.inclusion h).toAlgebra
  haveI : IsScalarTower ℤ L' L := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : FaithfulSMul ℤ L' := (faithfulSMul_iff_algebraMap_injective ℤ L').mpr Int.cast_injective
  haveI : FaithfulSMul L' L := (faithfulSMul_iff_algebraMap_injective L' L).mpr (algebraMap L' L).injective
  haveI : Algebra.Transcendental L' L := by
    refine ⟨⟨t, ht⟩, ?_⟩
    rintro ⟨p, hp0, hp⟩
    have h1 : Polynomial.eval₂ L'.subtype t p = 0 := by
      have := congrArg L.subtype hp
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂, map_zero] at this
      exact this
    have h2 : ∀ n, (p.map L'.subtype).IsRoot (σ n t) := fun n => by
      have := congrArg (σ n) h1
      rw [Polynomial.hom_eval₂, map_zero] at this
      have e : (σ n).comp L'.subtype = L'.subtype := RingHom.ext fun x => hσ n x x.2
      rw [e] at this
      rw [Polynomial.IsRoot, Polynomial.eval_map]
      exact this
    refine Polynomial.map_ne_zero (f := L'.subtype) hp0 (Polynomial.eq_zero_of_infinite_isRoot _ ?_)
    exact Set.infinite_of_injective_forall_mem hinj h2
  have hadd := trdeg_add_eq ℤ L' (A := L)
  have hpos := trdeg_pos L' L
  rw [hD] at hadd
  have hfin : Algebra.trdeg ℤ L' < Cardinal.aleph0 :=
    (le_self_add.trans hadd.le).trans_lt (Cardinal.natCast_lt_aleph0)
  have hfin2 : Algebra.trdeg L' L < Cardinal.aleph0 :=
    (le_add_self.trans hadd.le).trans_lt (Cardinal.natCast_lt_aleph0)
  obtain ⟨d, hd⟩ := Cardinal.lt_aleph0.1 hfin
  obtain ⟨e, he⟩ := Cardinal.lt_aleph0.1 hfin2
  rw [he] at hpos
  rw [hd, he] at hadd
  refine ⟨d, ?_, hd⟩
  have a1 : d + e = D := by exact_mod_cast hadd
  have a2 : 0 < e := by exact_mod_cast hpos
  omega

variable {Ψ : Type} [DecidableEq Ψ] {N : ℕ}

def r0 (q₀ : FlBlock Ψ N) : Fin N := ⟨q₀.2, by have := q₀.2.2; omega⟩

def r1 (q₀ : FlBlock Ψ N) : Fin N := ⟨q₀.2 + 1, by have := q₀.2.2; omega⟩

def sub (q₀ : FlBlock Ψ N) (c : ℚ) : MvPolynomial (Ψ × Fin N × Fin N) ℚ →ₐ[ℚ] MvPolynomial (Ψ × Fin N × Fin N) ℚ :=
  aeval fun x => X x + if x.1 = q₀.1 ∧ x.2.1 = r0 q₀ then C c * X (x.1, r1 q₀, x.2.2) else 0

theorem flag_row_one_ne_zero (q₀ : FlBlock Ψ N) : r1 q₀ ≠ r0 q₀ := fun h => by
  have := congrArg Fin.val h
  simp [r0, r1] at this

theorem sub_sub (q₀ : FlBlock Ψ N) (c : ℚ) (p) : sub q₀ (-c) (sub q₀ c p) = p := by
  have : (sub q₀ (-c)).comp (sub q₀ c) = AlgHom.id ℚ _ := by
    refine MvPolynomial.algHom_ext fun x => ?_
    by_cases h : x.1 = q₀.1 ∧ x.2.1 = r0 q₀
    · simp [sub, h, flag_row_one_ne_zero]
    · simp [sub, h]
  exact congrArg (fun φ => φ p) this

theorem sub_inj (q₀ : FlBlock Ψ N) (c : ℚ) : Function.Injective (sub q₀ c) :=
  Function.LeftInverse.injective (sub_sub q₀ c)

def subF (q₀ : FlBlock Ψ N) (c : ℚ) : ΩFl Ψ N →+* ΩFl Ψ N :=
  IsFractionRing.lift (g := (algebraMap _ (ΩFl Ψ N)).comp (sub q₀ c).toRingHom)
    ((IsFractionRing.injective _ _).comp (sub_inj q₀ c))

theorem subF_alg (q₀ : FlBlock Ψ N) (c : ℚ) (p) :
    subF q₀ c (algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) _ p) = algebraMap _ _ (sub q₀ c p) :=
  IsFractionRing.lift_algebraMap _ _

def yP (p : Σ q : FlBlock Ψ N, FlIdx Ψ N q) : MvPolynomial (Ψ × Fin N × Fin N) ℚ :=
  Matrix.det (Matrix.of fun a b : Fin ((p.1.2 : ℕ) + 1) => X (p.1.1, Fin.castLE (step_le p.1.2) a, p.2.1 b))

theorem sub_yP (q₀ : FlBlock Ψ N) (c : ℚ) (p : Σ q : FlBlock Ψ N, FlIdx Ψ N q) (hp : p.1 ≠ q₀) :
    sub q₀ c (yP p) = yP p := by
  obtain ⟨⟨τ, i⟩, A⟩ := p
  rw [yP, AlgHom.map_det]
  by_cases h : τ = q₀.1 ∧ (q₀.2 : ℕ) < i
  · obtain ⟨h1, h2⟩ := h
    let a0 : Fin ((i : ℕ) + 1) := ⟨q₀.2, by omega⟩
    let a1 : Fin ((i : ℕ) + 1) := ⟨q₀.2 + 1, by omega⟩
    have hne : a0 ≠ a1 := fun e => by have := congrArg Fin.val e; simp [a0, a1] at this
    refine Eq.trans ?_ (Matrix.det_updateRow_add_smul_self _ hne (C c))
    congr 1
    ext1 a b
    by_cases ha : a = a0
    · subst ha
      have e0 : Fin.castLE (step_le i) a0 = r0 q₀ := rfl
      have e1 : Fin.castLE (step_le i) a1 = r1 q₀ := rfl
      simp [sub, e0, e1, h1]
    · have e0 : Fin.castLE (step_le i) a ≠ r0 q₀ := fun e => ha (Fin.ext (congrArg (fun x : Fin N => (x : ℕ)) e))
      simp [sub, e0, Matrix.updateRow_ne ha]
  · congr 1
    ext1 a b
    have e0 : ¬ (τ = q₀.1 ∧ Fin.castLE (step_le i) a = r0 q₀) := by
      rintro ⟨h1, e⟩
      have e' : (a : ℕ) = q₀.2 := congrArg (fun x : Fin N => (x : ℕ)) e
      have h5 : (a : ℕ) < i + 1 := a.2
      refine hp (Prod.ext h1 (Fin.ext ?_))
      have : ¬ (q₀.2 : ℕ) < i := fun h2 => h ⟨h1, h2⟩
      show (i : ℕ) = q₀.2
      omega
    simp [sub, e0]

def nextIdx (q₀ : FlBlock Ψ N) : FlIdx Ψ N q₀ :=
  ⟨fun b => if (b : ℕ) = q₀.2 then r1 q₀ else Fin.castLE (step_le q₀.2) b, fun a b hab => by
    have h1 := a.2
    have h2 := b.2
    rw [Fin.lt_def] at hab ⊢
    dsimp only
    split_ifs <;> simp [r1] <;> omega⟩

def ev1 : MvPolynomial (Ψ × Fin N × Fin N) ℚ →+* ℚ := eval fun x => if x.2.1 = x.2.2 then 1 else 0

theorem ev_lead (q₀ : FlBlock Ψ N) (c : ℚ) : ev1 (sub q₀ c (yP ⟨q₀, leadIdx Ψ N q₀⟩)) = 1 := by
  rw [yP, AlgHom.map_det, RingHom.map_det, ← Matrix.det_one (n := Fin ((q₀.2 : ℕ) + 1))]
  congr 1
  ext a b
  have h2 : (b : ℕ) < q₀.2 + 1 := b.2
  have : r1 q₀ ≠ Fin.castLE (step_le q₀.2) b := fun e => by
    have : (q₀.2 : ℕ) + 1 = b := congrArg (fun x : Fin N => (x : ℕ)) e
    omega
  simp [sub, ev1, leadIdx, Matrix.one_apply, apply_ite (eval _), this]

theorem ev_next (q₀ : FlBlock Ψ N) (c : ℚ) : ev1 (sub q₀ c (yP ⟨q₀, nextIdx q₀⟩)) = c := by
  rw [yP, AlgHom.map_det, RingHom.map_det]
  have : (ev1.mapMatrix ((sub q₀ c).mapMatrix (Matrix.of fun a b : Fin ((q₀.2 : ℕ) + 1) =>
      (X (q₀.1, Fin.castLE (step_le q₀.2) a, (nextIdx q₀).1 b) : MvPolynomial (Ψ × Fin N × Fin N) ℚ)))) =
      Matrix.diagonal fun a => if a = Fin.last _ then c else 1 := by
    ext a b
    have h1 := a.2
    have h2 := b.2
    simp only [sub, ev1, nextIdx, RingHom.mapMatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      aeval_X, map_add, eval_X, apply_ite (eval _), map_mul, eval_C, map_zero, true_and, Matrix.diagonal_apply,
      Fin.ext_iff, r0, r1, Fin.val_castLE, Fin.val_last, apply_ite Fin.val]
    split_ifs <;> first | omega | simp
  rw [this, Matrix.det_diagonal]
  simp

end PositivityTheory.Xgp.fl_arith

end

open PositivityTheory.Xgp.fl_arith FlagArithVar in
theorem PositivityTheory.Xgp.t_fl_arith : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) ∧ ∀ q₀ : FlBlock Ψ N, Nonempty {q : FlBlock Ψ N // q ≠ q₀} → ∃ d₀ < antisymDegree Ψ N + 1, IsArithVar (imageZ (fun p : Σ q : {q : FlBlock Ψ N // q ≠ q₀}, FlIdx Ψ N q.1 => (⟨p.1.1, p.2⟩ : Σ q, FlIdx Ψ N q)) (PFl Ψ N)) d₀ := by
  intro Ψ _ _ _ N hN
  have hD : antisymDegree Ψ N = dimFl Ψ N := by rw [dimFl, ← Nat.choose_two_right]; rfl
  rw [hD]
  refine ⟨FlagArithVar.proof Ψ N hN, fun q₀ hK => ?_⟩
  have hc : ∀ q, yFl Ψ N ⟨q, leadIdx Ψ N q⟩ ≠ 0 := fun q => by
    rw [yFl_lead]; exact GenLeadMinorNeZero.full ℚ Ψ N q.1 q.2
  set v := (fun p : Σ q : {q : FlBlock Ψ N // q ≠ q₀}, FlIdx Ψ N q.1 => (⟨p.1.1, p.2⟩ : Σ q, FlIdx Ψ N q)) with hv
  have himg : imageZ v (PFl Ψ N) = mCoordIdeal (yFl Ψ N ∘ v) := by
    ext F
    simp only [PFl, imageZ, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, GroundTheory.Heights₂.Heights.Targets.ImageCoord.mConeMap_rename
        (Subtype.val : {q : FlBlock Ψ N // q ≠ q₀} → FlBlock Ψ N) v (fun _ => rfl) (yFl Ψ N) F]
    exact ⟨fun h => rename_injective _ Subtype.val_injective (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
  have hL : Algebra.trdeg ℤ (Subfield.closure (coneRatios (yFl Ψ N) (leadIdx Ψ N))) =
      ((dimFl Ψ N : ℕ) : Cardinal) := by
    have h := trdeg_closure_of_rat _ (FlagRatioTrdeg.full ℚ Ψ N)
    rw [coneRatios_eq]
    exact h
  have hy : ∀ p, yFl Ψ N p = algebraMap _ _ (yP p) := fun _ => rfl
  obtain ⟨d, hd, hd'⟩ := trdeg_lt (Subfield.closure (coneRatios (yFl Ψ N ∘ v) fun q => leadIdx Ψ N q.1)) _
    (Subfield.closure_mono (t := coneRatios (yFl Ψ N) (leadIdx Ψ N)) (by rintro _ ⟨p, rfl⟩; exact ⟨v p, rfl⟩))
    (yFl Ψ N ⟨q₀, nextIdx q₀⟩ / yFl Ψ N ⟨q₀, leadIdx Ψ N q₀⟩)
    (Subfield.subset_closure ⟨⟨q₀, nextIdx q₀⟩, rfl⟩) (fun n => subF q₀ n) (fun n x hx => by
      refine (Subfield.closure_le (t := (subF q₀ n).eqLocusField (RingHom.id _))).2 ?_ hx
      rintro _ ⟨p, rfl⟩
      show subF q₀ n (yFl Ψ N (v p) / yFl Ψ N (v ⟨p.1, _⟩)) = yFl Ψ N (v p) / yFl Ψ N (v ⟨p.1, _⟩)
      rw [map_div₀, hy, hy, subF_alg, subF_alg, sub_yP q₀ _ _ p.1.2, sub_yP q₀ _ _ p.1.2])
    (fun n m hnm => by
      have hne : ∀ n : ℕ, subF q₀ n (yFl Ψ N ⟨q₀, leadIdx Ψ N q₀⟩) ≠ 0 := fun n =>
        (map_ne_zero _).2 (hc q₀)
      simp only [map_div₀] at hnm
      rw [div_eq_div_iff (hne n) (hne m)] at hnm
      simp only [hy, subF_alg, ← map_mul] at hnm
      have := congrArg ev1 (IsFractionRing.injective _ _ hnm)
      simp only [map_mul, ev_lead, ev_next, mul_one] at this
      exact_mod_cast this) _ hL
  refine ⟨d + 1, by omega, ?_⟩
  rw [himg]
  exact arith_of_trdeg hK _ (fun q => leadIdx Ψ N q.1) (fun q => hc q.1) d hd'
end

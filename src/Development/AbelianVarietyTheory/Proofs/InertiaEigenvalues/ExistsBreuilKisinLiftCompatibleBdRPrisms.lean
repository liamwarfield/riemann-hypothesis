module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDecompositionBaseChange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinLiftCompatibleBdRPrisms
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproxRootSubUniformizerMemFilP
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproxRootSubUniformizerMemFilP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.ApproxRoot

theorem mul_eval_derivative_scaleRoots {R : Type} [CommRing R] (p : Polynomial R) (s r : R) :
    s * (Polynomial.derivative (p.scaleRoots s)).eval (s * r) =
      s ^ p.natDegree * (Polynomial.derivative p).eval r := by
  have h : (p.scaleRoots s).comp (Polynomial.C s * Polynomial.X) = Polynomial.C s ^ p.natDegree * p := by
    have := Polynomial.scaleRoots_eval₂_mul (p := p) Polynomial.C Polynomial.X s
    rwa [Polynomial.eval₂_C_X] at this
  rw [← map_pow] at h
  have h2 := congrArg (fun t => (Polynomial.derivative t).eval r) h
  simp only [Polynomial.derivative_C_mul] at h2
  simpa [Polynomial.derivative_comp, Polynomial.eval_comp] using h2

theorem sub_mem_pow {R : Type} [CommRing R] (I : Ideal R) (P : Polynomial R) (s r x : R) (n : ℕ) (hs : IsUnit s)
    (hr : P.eval r = 0) (hd : IsUnit ((Polynomial.derivative P).eval r))
    (hx : (P.scaleRoots s).eval x ∈ I ^ n) (hxy : x - s * r ∈ I) : x - s * r ∈ I ^ n := by
  have hy : (P.scaleRoots s).eval (s * r) ∈ I ^ n := by
    rw [Polynomial.scaleRoots_eval_mul, hr, mul_zero]
    exact zero_mem _
  have h := GlobalTheory.T.pow_mul_sub_mem_pow_of_eval_mem_pow R I (P.scaleRoots s) (s * r) x s (s ^ P.natDegree * (Polynomial.derivative P).eval r) n
    hy hx (by rw [← neg_sub]; exact neg_mem hxy)
    (by rw [mul_eval_derivative_scaleRoots, sub_self]; exact zero_mem _)
  rw [Ideal.unit_mul_mem_iff_mem _ (((hs.pow _).mul hd).pow n)] at h
  rw [← neg_sub]
  exact neg_mem h

end GlobalTheory.BSP.ApproxRoot


open GlobalTheory.BSP.ApproxRoot in
theorem GlobalTheory.BSP.approxRoot_sub_mem_fil : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (n m : ℕ) (q : bk.S), bk.E ∣ q - (l : bk.S) ^ m * X → bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)) → aDp l (bk.ev q) - (l : Per.BdRp l) ^ m * C.o (((bk.str.symm (Ideal.Quotient.mk _ X) : ↥(OL K)) : ↥K.1) : Om l) ∈ Per.FilP l n := by
  intro l _ K bk C n m q hq hroot
  obtain ⟨hfil, -⟩ := GlobalTheory.T.bdR_filtration_ker_theta_generator_facts l C (bk.ev bk.E) bk.span_ev
  obtain ⟨-, hker, -, hth, -⟩ := thetaD_props l
  let e : bk.S →+* Per.BdRp l := (aDp l).comp bk.ev
  let f : Wq l bk.a →+* Per.BdRp l := (aDp l).comp (wA l bk.a)
  let g : bk.S →+* Per.BdRp l := C.o.comp ((K.1.val : ↥K.1 →+* Om l).comp (((OL K).val : ↥(OL K) →+* ↥K.1).comp
    (bk.str.symm.toRingHom.comp (Ideal.Quotient.mk _))))
  have hg : ∀ s, g s = C.o (((bk.str.symm (Ideal.Quotient.mk _ s) : ↥(OL K)) : ↥K.1) : Om l) := fun _ => rfl
  have hθ : ∀ s : bk.S, ((Per.θ l (bk.ev s) : OC l) : ℂ_[l]) =
      ((((bk.str.symm (Ideal.Quotient.mk _ s) : ↥(OL K)) : ↥K.1) : Om l) : ℂ_[l]) := fun s => by
    rw [bk.θ_ev (bk.str.symm (Ideal.Quotient.mk _ s)) s (bk.str.apply_symm_apply _).symm, coe_intToOC]
  have hef : e.comp PowerSeries.C = f := RingHom.ext fun w => congrArg (aDp l) (bk.ev_C w)
  have hgf : g.comp PowerSeries.C = f := RingHom.ext fun w =>
    GlobalTheory.T.localPeriodRings_section_eq_ainfToBdRPlus l bk.a C w _ (by rw [← bk.ev_C]; exact hθ _)
  have hgE : g bk.E = 0 := by
    rw [hg, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)]
    simp
  have hθeg : ∀ s, Per.θD l (e s) = Per.θD l (g s) := fun s => by
    rw [hg, C.o_sec.th]
    exact (hth _).trans (hθ s)
  have hl : IsUnit ((l : Per.BdRp l) ^ m) := (isUnit_l_BdRp l).pow m
  have hr : (bk.Ep.map f).eval (g X) = 0 := by
    rw [Polynomial.eval_map, ← hgf, ← Polynomial.hom_eval₂, Polynomial.eval₂_C_X_eq_coe]
    exact hgE
  have hd : IsUnit ((Polynomial.derivative (bk.Ep.map f)).eval (g X)) := by
    obtain ⟨c, a, b, hab⟩ := GlobalTheory.T.bezout_eisenstein_derivative_prime_pow l K bk
    have h := congrArg (fun t => (Polynomial.map f t).eval (g X)) hab
    simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.eval_add, Polynomial.eval_mul, hr, mul_zero,
      zero_add, Polynomial.map_C, Polynomial.eval_C, map_pow f, map_natCast f] at h
    rw [Polynomial.derivative_map]
    exact isUnit_of_mul_isUnit_right (h ▸ (isUnit_l_BdRp l).pow c)
  haveI : Nontrivial (Per.BdRp l) := (Per.θD l).domain_nontrivial
  have hx : ((bk.Ep.map f).scaleRoots ((l : Per.BdRp l) ^ m)).eval (e q) ∈ Ideal.span {e bk.E} ^ n := by
    have h1 : (bk.Ep.map f).scaleRoots ((l : Per.BdRp l) ^ m) =
        (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)).map f := by
      rw [Polynomial.map_scaleRoots _ _ _ (by rw [bk.monic.leadingCoeff, map_one]; exact one_ne_zero), map_pow,
        map_natCast]
    rw [h1, Polynomial.eval_map, ← hef, ← Polynomial.hom_eval₂, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      ← map_pow]
    exact map_dvd e hroot
  have hxy : e q - (l : Per.BdRp l) ^ m * g X ∈ Ideal.span {e bk.E} := by
    have h1 : e q - (l : Per.BdRp l) ^ m * g X ∈ Per.FilP l 1 := by
      rw [← hker, map_sub, hθeg, ← map_sub]
      obtain ⟨t, ht⟩ := hq
      have h2 := congrArg g ht
      rw [map_sub, map_mul, map_pow, map_natCast, map_mul, hgE, zero_mul] at h2
      rw [h2, map_zero]
    rwa [hfil, pow_one] at h1
  have h := sub_mem_pow _ _ _ _ _ n hl hr hd hx hxy
  rw [Ideal.span_singleton_pow] at h
  rw [hfil]
  exact h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproxRootSubUniformizerMemFilPStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approxRoot_sub_uniformizer_mem_filP : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (n m : ℕ) (q : bk.S), bk.E ∣ q - (l : bk.S) ^ m * X → bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)) → aDp l (bk.ev q) - (l : Per.BdRp l) ^ m * C.o (((bk.str.symm (Ideal.Quotient.mk _ X) : ↥(OL K)) : ↥K.1) : Om l) ∈ Per.FilP l n := by
  first | exact @GlobalTheory.BSP.approxRoot_sub_mem_fil | exact GlobalTheory.BSP.approxRoot_sub_mem_fil | (intros; apply GlobalTheory.BSP.approxRoot_sub_mem_fil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinLiftCompatibleBdRPrisms
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.RingHomLiftCongruence

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem exists_poly (bk : BK K) (y : bk.S ⧸ Ideal.span {bk.E}) :
    ∃ P : Polynomial (Wq l bk.a), Ideal.Quotient.mk _ (P : bk.S) = y := by
  have : IsAdicComplete (Ideal.span {(l : Wq l bk.a)}) (Wq l bk.a) := WittVector.isAdicCompleteIdealSpanP
  have H : bk.Ep.IsDistinguishedAt (Ideal.span {(l : Wq l bk.a)}) :=
    { mem := fun {i} hi => Ideal.mem_span_singleton.2 (bk.dvd_coeff i hi)
      monic := bk.monic }
  exact ⟨_, H.isWeierstrassDivisorAt'.mk_mod'_eq_self⟩

theorem exists_dvd_pow_mul_ringHom_sub_mul {S A : Type} [CommRing S] [CommRing A] (f g : S →+* A) (e p : A) (s t : S)
    (hs : ∃ k : ℕ, e ∣ p ^ k * (f s - g s)) (ht : ∃ k : ℕ, e ∣ p ^ k * (f t - g t)) :
    ∃ k : ℕ, e ∣ p ^ k * (f (s * t) - g (s * t)) := by
  obtain ⟨a, x, hx⟩ := hs
  obtain ⟨b, y, hy⟩ := ht
  refine ⟨a + b, p ^ b * f t * x + p ^ a * g s * y, ?_⟩
  rw [map_mul, map_mul]
  linear_combination (p ^ b * f t) * hx + (p ^ a * g s) * hy

theorem exists_dvd_pow_mul_ringHom_sub_natPowComb {S A : Type} [CommRing S] [CommRing A] (f g : S →+* A) (e p : A) (m i j : ℕ) (s t : S)
    (hs : ∃ k : ℕ, e ∣ p ^ k * (f s - g s)) (ht : ∃ k : ℕ, e ∣ p ^ k * (f t - g t)) :
    ∃ k : ℕ, e ∣ p ^ k * (f ((m : S) ^ i * s + (m : S) ^ j * t) - g ((m : S) ^ i * s + (m : S) ^ j * t)) := by
  obtain ⟨a, x, hx⟩ := hs
  obtain ⟨b, y, hy⟩ := ht
  refine ⟨a + b, p ^ b * (m : A) ^ i * x + p ^ a * (m : A) ^ j * y, ?_⟩
  simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  linear_combination (p ^ b * (m : A) ^ i) * hx + (p ^ a * (m : A) ^ j) * hy

theorem ringHom_lift_sub_mem_mul {S R A : Type} [CommRing S] [CommRing R] [CommRing A] (ψ : S →+* A) (φ : R →+* A) (I : Ideal A)
    (p : A) (i j : ℕ) (s t : S) (x y : R) (hs : ψ s - p ^ i * φ x ∈ I) (ht : ψ t - p ^ j * φ y ∈ I) :
    ψ (s * t) - p ^ (i + j) * φ (x * y) ∈ I := by
  have h := I.add_mem (I.mul_mem_left (ψ t) hs) (I.mul_mem_left (p ^ i * φ x) ht)
  convert h using 1
  rw [map_mul, map_mul]
  ring

theorem ringHom_lift_sub_mem_natPowComb {S R A : Type} [CommRing S] [CommRing R] [CommRing A] (ψ : S →+* A) (φ : R →+* A) (I : Ideal A)
    (m i j : ℕ) (s t : S) (x y : R) (hs : ψ s - (m : A) ^ i * φ x ∈ I) (ht : ψ t - (m : A) ^ j * φ y ∈ I) :
    ψ ((m : S) ^ j * s + (m : S) ^ i * t) - (m : A) ^ (i + j) * φ (x + y) ∈ I := by
  have h := I.add_mem (I.mul_mem_left ((m : A) ^ j) hs) (I.mul_mem_left ((m : A) ^ i) ht)
  convert h using 1
  simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  ring

noncomputable def oK (K : FinExt l) (C : Core l) : ↥(OL K) →+* Per.BdRp l :=
  C.o.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)

def Good (bk : BK K) (C : Core l) (n : ℕ) (x : ↥(OL K)) : Prop :=
  ∃ (k : ℕ) (s : bk.S), ((aDp l).comp bk.ev) s - (l : Per.BdRp l) ^ k * oK K C x ∈ Per.FilP l n ∧
    ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ,
      BK.hf (bk := bk) f bk.E ^ n ∣ (l : B.A) ^ k * (BK.hf (bk := bk) f s - BK.hf (bk := bk) g s)

variable {bk : BK K} {C : Core l} {n : ℕ}

theorem Good.mul {x y : ↥(OL K)} (hx : Good bk C n x) (hy : Good bk C n y) : Good bk C n (x * y) := by
  obtain ⟨i, s, hs, hs'⟩ := hx
  obtain ⟨j, t, ht, ht'⟩ := hy
  exact ⟨i + j, s * t, ringHom_lift_sub_mem_mul _ _ _ _ i j s t x y hs ht,
    fun B f g => exists_dvd_pow_mul_ringHom_sub_mul _ _ _ _ s t (hs' B f g) (ht' B f g)⟩

theorem Good.add {x y : ↥(OL K)} (hx : Good bk C n x) (hy : Good bk C n y) : Good bk C n (x + y) := by
  obtain ⟨i, s, hs, hs'⟩ := hx
  obtain ⟨j, t, ht, ht'⟩ := hy
  exact ⟨i + j, (l : bk.S) ^ j * s + (l : bk.S) ^ i * t, ringHom_lift_sub_mem_natPowComb _ _ _ l i j s t x y hs ht,
    fun B f g => exists_dvd_pow_mul_ringHom_sub_natPowComb _ _ _ _ l j i s t (hs' B f g) (ht' B f g)⟩

theorem good_C (w : Wq l bk.a) :
    Good bk C n (bk.str.symm (Ideal.Quotient.mk _ (PowerSeries.C w))) := by
  refine ⟨0, PowerSeries.C w, ?_, fun B f g => ⟨0, ?_⟩⟩
  · have h := bk.θ_ev (bk.str.symm (Ideal.Quotient.mk _ (PowerSeries.C w))) (PowerSeries.C w)
      (bk.str.apply_symm_apply _).symm
    rw [bk.ev_C] at h
    have h2 := GlobalTheory.T.localPeriodRings_section_eq_ainfToBdRPlus l bk.a C w
      (((bk.str.symm (Ideal.Quotient.mk _ (PowerSeries.C w)) : ↥(OL K)) : ↥K.1) : Om l)
      (by rw [h]; exact coe_intToOC K _)
    have h3 : oK K C (bk.str.symm (Ideal.Quotient.mk _ (PowerSeries.C w))) = aDp l (wA l bk.a w) := h2
    rw [h3, RingHom.comp_apply, bk.ev_C, pow_zero, one_mul, sub_self]
    exact Ideal.zero_mem _
  · rw [(GlobalTheory.T.breuilKisinPrism_homs_agree_witt_and_mod_ideal l K bk B f g).1 w, sub_self, mul_zero]
    exact dvd_zero _

theorem good_X : Good bk C n (bk.str.symm (Ideal.Quotient.mk _ X)) := by
  obtain ⟨m, q, h1, h2⟩ := GlobalTheory.T.exists_approx_root_eisenstein_away_prime l K bk n
  have hIndep (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) :
      ∃ k : ℕ, BK.hf (bk := bk) f bk.E ^ n ∣
        (l : B.A) ^ k * (BK.hf (bk := bk) f q - BK.hf (bk := bk) g q) := by
    obtain ⟨hC, hX, hI⟩ := GlobalTheory.T.breuilKisinPrism_homs_agree_witt_and_mod_ideal l K bk B f g
    obtain ⟨-, -, hI'⟩ := GlobalTheory.T.breuilKisinPrism_homs_agree_witt_and_mod_ideal l K bk B g f
    obtain ⟨c, a, b, hab⟩ := GlobalTheory.T.bezout_eisenstein_derivative_prime_pow l K bk
    exact approxRoot_image_indep_general_rings l n m c bk.Ep a b hab q h1 h2 B.I
      (BK.hf (bk := bk) f) (BK.hf (bk := bk) g) hC hX hI hI'
  exact ⟨m, q, GlobalTheory.T.approxRoot_sub_uniformizer_mem_filP l K bk C n m q h1 h2, hIndep⟩

theorem good_poly (P : Polynomial (Wq l bk.a)) :
    Good bk C n (bk.str.symm (Ideal.Quotient.mk _ (P : bk.S))) := by
  induction P using Polynomial.induction_on with
  | C a => rw [Polynomial.coe_C]; exact good_C a
  | add p q hp hq => rw [Polynomial.coe_add, map_add (f := _), map_add (f := _)]; exact hp.add hq
  | monomial k a h =>
    rw [pow_succ, ← mul_assoc, Polynomial.coe_mul, Polynomial.coe_X, map_mul, map_mul]
    exact h.mul good_X

theorem exists_lift : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l)
    (n : ℕ) (x : ↥(OL K)), ∃ (k : ℕ) (s : bk.S),
    aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * C.o ((x : ↥K.1) : Om l) ∈ Per.FilP l n ∧
    (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ,
      BK.hf (bk := bk) f bk.E ^ n ∣ (l : B.A) ^ k * (BK.hf (bk := bk) f s - BK.hf (bk := bk) g s)) := by
  intro l _ K bk C n x
  obtain ⟨P, hP⟩ := exists_poly bk (bk.str x)
  have h := good_poly (bk := bk) (C := C) (n := n) P
  rw [hP, bk.str.symm_apply_apply] at h
  exact h

end GlobalTheory.BSP.RingHomLiftCongruence
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinLiftCompatibleBdRPrismsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_breuilKisin_lift_compatible_bdR_prisms : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (n : ℕ) (x : ↥(OL K)), ∃ (k : ℕ) (s : bk.S), aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * C.o ((x : ↥K.1) : Om l) ∈ Per.FilP l n ∧ (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, BK.hf f bk.E ^ n ∣ (l : B.A) ^ k * (BK.hf f s - BK.hf g s)) := by
  first | exact @GlobalTheory.BSP.RingHomLiftCongruence.exists_lift | exact GlobalTheory.BSP.RingHomLiftCongruence.exists_lift | (intros; apply GlobalTheory.BSP.RingHomLiftCongruence.exists_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaConjBoundedCompatibleBreuilKisinFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaConjBoundedCompatibleBreuilKisinFrames
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.HTBound

section mat
variable {𝕜 : Type*} [NormedField 𝕜] [IsUltrametricDist 𝕜] {m n k : Type*} [Fintype n]

theorem nsub_max (x y : 𝕜) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)

theorem bnd_mul {A : Matrix m n 𝕜} {B : Matrix n k 𝕜} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hA : ∀ i j, ‖A i j‖ ≤ r) (hB : ∀ i j, ‖B i j‖ ≤ s) : ∀ i j, ‖(A * B) i j‖ ≤ r * s := by
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr hs) fun x _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hA _ _) (hB _ _) (norm_nonneg _) hr

theorem bnd_add {A B : Matrix m k 𝕜} {r : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ r) (hB : ∀ i j, ‖B i j‖ ≤ r) :
    ∀ i j, ‖(A + B) i j‖ ≤ r := fun i j =>
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA i j) (hB i j))

theorem bnd_sub {A B : Matrix m k 𝕜} {r : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ r) (hB : ∀ i j, ‖B i j‖ ≤ r) :
    ∀ i j, ‖(A - B) i j‖ ≤ r := fun i j =>
  (nsub_max _ _).trans (max_le (hA i j) (hB i j))

theorem bnd_smul {A : Matrix m k 𝕜} {r : ℝ} (a : 𝕜) (hA : ∀ i j, ‖A i j‖ ≤ r) :
    ∀ i j, ‖(a • A) i j‖ ≤ ‖a‖ * r := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hA i j) (norm_nonneg a)

end mat

variable {l : ℕ} [hl : Fact l.Prime]

theorem th_le (x : Ainf l) : ‖((Per.θD l).comp (aDp l)) x‖ ≤ 1 := by
  rw [RingHom.comp_apply, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
  exact (GlobalTheory.RingBasics.mem_OC _).1 (Per.θ l x).2

theorem norm_l : ‖((l : ℕ) : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [GlobalTheory.RingBasics.norm_eq_val, PadicComplex.valuation_p]
  simp

theorem th_pow_dvd (n : ℕ) (x : Ainf l) (h : ((l : ℕ) : Ainf l) ^ n ∣ x) :
    ‖((Per.θD l).comp (aDp l)) x‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
  obtain ⟨w, rfl⟩ := h
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, norm_l, inv_pow]
  exact mul_le_of_le_one_right (by positivity) (th_le w)

theorem th_gal {K : FinExt l} (bk : BK K) (g : ↥(GK K)) (s : bk.S) :
    ((Per.θD l).comp (aDp l)) (Per.σA (g : GQ l) (bk.ev s)) = ((Per.θD l).comp (aDp l)) (bk.ev s) := by
  simp only [RingHom.comp_apply, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1, GlobalTheory.RingBasics.θ_σA]
  obtain ⟨r, hr⟩ := bk.str.surjective (Ideal.Quotient.mk _ s)
  rw [bk.θ_ev r s hr.symm]
  refine (GlobalTheory.RingIface.sigO_coe l (g : GQ l) (intToOC K r)).trans ?_
  rw [coe_intToOC, GlobalTheory.RingBasics.σC_coe]
  congr 1
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (r : ↥K.1).2

theorem zl_unique (f g : ℤ_[l] →+* ℂ_[l]) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1) (x : ℤ_[l]) :
    f x = g x := by
  have key : ∀ n : ℕ, ‖f x - g x‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ ^ n := by
    intro n
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n x)
    have e : x = ((x.appr n : ℕ) : ℤ_[l]) + u * ((l : ℕ) : ℤ_[l]) ^ n := by rw [hu]; ring
    rw [e, map_add (f := _), map_add (f := _), map_natCast, map_natCast, add_sub_add_left_eq_sub, map_mul, map_mul, map_pow,
      map_pow, map_natCast, map_natCast, ← sub_mul, norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity)
      ((nsub_max _ _).trans (max_le (hf u) (hg u)))
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (GlobalTheory.RingBasics.norm_p_lt (p := l))
  have h0 := ge_of_tendsto' ht key
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

theorem th_zl (z : ℤ_[l]) :
    ((Per.θD l).comp (aDp l)) (algebraMap ℤ_[l] (Ainf l) z) = algebraMap (Om l) ℂ_[l] (zOm l z) :=
  zl_unique (((Per.θD l).comp (aDp l)).comp (algebraMap ℤ_[l] (Ainf l)))
    ((algebraMap (Om l) ℂ_[l]).comp (zOm l)) (fun _ => th_le _) (fun x => by
      simp [zOm]
      exact PadicInt.norm_le_one x) z

theorem pow_dvd_of_inclW (k : ℕ) (a : Ainf l) (h : ((l : ℕ) : WCb l) ^ k ∣ inclW l a) :
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

theorem bounded_compat : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N : ℕ), ∃ Bd : ℝ, ∀ (N' d d' n : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') (ℤ_[l])) (F : Frame bk N' d ρ) (F' : Frame bk N d' ρ') (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Y' : Matrix (Fin d') (Fin d') (Ainf l)), N' = N → Y.map (inclW l) = inclW l τ ^ N • F.T → Y'.map (inclW l) = inclW l τ ^ N • F'.T → ∀ (g : ↥(GK K)) (U : Matrix (Fin d) (Fin d) (ℂ_[l])) (U' : Matrix (Fin d') (Fin d') (ℂ_[l])), U * Y.map ((Per.θD l).comp (aDp l)) = Y.map ((Per.θD l).comp (aDp l)) * (F.ε g).map ((Per.θD l).comp (aDp l)) → U' * Y'.map ((Per.θD l).comp (aDp l)) = Y'.map ((Per.θD l).comp (aDp l)) * (F'.ε g).map ((Per.θD l).comp (aDp l)) → (∀ i j, ‖U i j‖ ≤ Bd) ∧ (∀ i j, ‖U' i j‖ ≤ Bd) ∧ ∀ (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])) (R : Matrix (Fin d) (Fin d') (bk.S)), (∀ g i j, (l : ℤ_[l]) ^ n ∣ (Pi * ρ' g - ρ g * Pi) i j) → (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - F.T * R.map bk.evW) i j) → ∀ i j, ‖(U * Pi.map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) - Pi.map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) * U') i j‖ ≤ Bd * ((l : ℝ) ^ n)⁻¹ := by
  intro l _ K bk τ hτ N
  have hs0 := GlobalTheory.T.theta_ainf_period_pow_ne_zero l K bk τ hτ (2 * N)
  set s := ((Per.θD l).comp (aDp l)) (τ ^ (2 * N)) with hs
  have hc0 : 0 < ‖s‖ := norm_pos_iff.2 hs0
  have hc1 : ‖s‖ ≤ 1 := th_le _
  have hci : 1 ≤ ‖s‖⁻¹ := (one_le_inv₀ hc0).2 hc1
  refine ⟨‖s‖⁻¹ * ‖s‖⁻¹, ?_⟩
  intro N' d d' n ρ ρ' F F' Y Y' hN hY hY' g U U' hU hU'
  subst N'
  have hb1 : ∀ {m k : Type} (M : Matrix m k (Ainf l)), ∀ i j, ‖(M.map ((Per.θD l).comp (aDp l))) i j‖ ≤ 1 :=
    fun M i j => th_le _

  have inv : ∀ {e : ℕ} {σ : ↥(GK K) → Matrix (Fin e) (Fin e) ℤ_[l]} (G : Frame bk N e σ)
      (Z : Matrix (Fin e) (Fin e) (Ainf l)), Z.map (inclW l) = inclW l τ ^ N • G.T →
      ∃ Z₁ : Matrix (Fin e) (Fin e) (Ainf l),
        Z.map ((Per.θD l).comp (aDp l)) * Z₁.map ((Per.θD l).comp (aDp l)) = s • 1 := by
    intro e σ G Z hZ
    obtain ⟨Z₀, Z₁, h0, h1⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N e σ G.toPre
    have e0 : Z₀ = Z := by
      refine Matrix.ext fun i j => ?_
      apply inclW_injective
      have := congrFun (congrFun (h0.trans hZ.symm) i) j
      simpa using this
    subst e0
    refine ⟨Z₁, ?_⟩
    rw [← Matrix.map_mul, h1]
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j <;> simp [Matrix.smul_apply, Matrix.one_apply, hij, s]
  obtain ⟨Y₁, hY₁⟩ := inv F Y hY
  obtain ⟨Y₁', hY₁'⟩ := inv F' Y' hY'

  have solve : ∀ {e : ℕ} (y y₁ x V : Matrix (Fin e) (Fin e) ℂ_[l]), y * y₁ = s • 1 → V * y = y * x →
      V = s⁻¹ • (y * x * y₁) := by
    intro e y y₁ x V h1 h2
    rw [← h2, Matrix.mul_assoc, h1, Matrix.mul_smul, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have bnd : ∀ {e : ℕ} {σ : ↥(GK K) → Matrix (Fin e) (Fin e) ℤ_[l]} (G : Frame bk N e σ)
      (Z Z₁ : Matrix (Fin e) (Fin e) (Ainf l)) (V : Matrix (Fin e) (Fin e) ℂ_[l]),
      Z.map ((Per.θD l).comp (aDp l)) * Z₁.map ((Per.θD l).comp (aDp l)) = s • 1 →
      V * Z.map ((Per.θD l).comp (aDp l)) = Z.map ((Per.θD l).comp (aDp l)) * (G.ε g).map ((Per.θD l).comp (aDp l)) →
      ∀ i j, ‖V i j‖ ≤ ‖s‖⁻¹ := by
    intro e σ G Z Z₁ V h1 h2
    rw [solve _ _ _ V h1 h2]
    have := bnd_smul s⁻¹ (bnd_mul (mul_nonneg zero_le_one zero_le_one) zero_le_one
      (bnd_mul zero_le_one zero_le_one (hb1 Z) (hb1 (G.ε g))) (hb1 Z₁))
    simpa [norm_inv] using this
  have hUb := bnd F Y Y₁ U hY₁ hU
  have hU'b := bnd F' Y' Y₁' U' hY₁' hU'
  have hle : ‖s‖⁻¹ ≤ ‖s‖⁻¹ * ‖s‖⁻¹ := le_mul_of_one_le_left (by positivity) hci
  refine ⟨fun i j => (hUb i j).trans hle, fun i j => (hU'b i j).trans hle, ?_⟩
  intro Pi R hequi hlink
  set θ' : Ainf l →+* ℂ_[l] := (Per.θD l).comp (aDp l) with hθ'
  have hD1 : ∀ i j, ((l : ℕ) : Ainf l) ^ n ∣ (Pi.map (algebraMap ℤ_[l] (Ainf l)) * Y' - Y * R.map bk.ev) i j := by
    intro i j
    apply pow_dvd_of_inclW
    have e1 : (Pi.map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW Pi := by
      refine Matrix.ext fun a b => ?_
      exact (inclWA l).commutes _
    have e2 : (R.map bk.ev).map (inclW l) = R.map bk.evW := by
      rw [Matrix.map_map]; rfl
    have e : (Pi.map (algebraMap ℤ_[l] (Ainf l)) * Y' - Y * R.map bk.ev).map (inclW l) =
        inclW l τ ^ N • (zW Pi * F'.T - F.T * R.map bk.evW) := by
      rw [Matrix.map_sub _ (map_sub (inclW l)), Matrix.map_mul, Matrix.map_mul, hY, hY', e1, e2,
        Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    have := congrFun (congrFun e i) j
    rw [Matrix.map_apply] at this
    rw [this, Matrix.smul_apply, smul_eq_mul]
    exact Dvd.dvd.mul_left (hlink i j) _
  have hD2 := GlobalTheory.T.breuilKisinLatticeFrame_cocycles_linked l K bk N N d d' n ρ ρ' F F' Pi R hequi hlink g
  have hP : Pi.map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) = (Pi.map (algebraMap ℤ_[l] (Ainf l))).map θ' := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    exact (th_zl _).symm
  have hR : ((R.map bk.ev).map (Per.σA (g : GQ l))).map θ' = (R.map bk.ev).map θ' := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    exact th_gal bk g _
  rw [hP]
  set P := (Pi.map (algebraMap ℤ_[l] (Ainf l))).map θ' with hPdef
  set y := Y.map θ' with hy
  set y' := Y'.map θ' with hy'
  set Ry := (R.map bk.ev).map θ' with hRy
  set e := (F.ε g).map θ' with he
  set e' := (F'.ε g).map θ' with he'
  have eD1 : P * y' - y * Ry = (Pi.map (algebraMap ℤ_[l] (Ainf l)) * Y' - Y * R.map bk.ev).map θ' := by
    rw [Matrix.map_sub _ (map_sub θ'), Matrix.map_mul, Matrix.map_mul]
  have eD2 : e * Ry - Ry * e' = (F.ε g * (R.map bk.ev).map (Per.σA (g : GQ l)) - R.map bk.ev * F'.ε g).map θ' := by
    rw [Matrix.map_sub _ (map_sub θ'), Matrix.map_mul, Matrix.map_mul, hR]
  set q : ℝ := ((l : ℝ) ^ n)⁻¹ with hqdef
  have hq : 0 ≤ q := by positivity
  have bD1 : ∀ i j, ‖(P * y' - y * Ry) i j‖ ≤ q := by
    rw [eD1]; intro i j; exact th_pow_dvd n _ (hD1 i j)
  have bD2 : ∀ i j, ‖(e * Ry - Ry * e') i j‖ ≤ q := by
    rw [eD2]; intro i j; exact th_pow_dvd n _ (hD2 i j)
  have key : (U * P - P * U') * y' = U * (P * y' - y * Ry) + y * (e * Ry - Ry * e') - (P * y' - y * Ry) * e' := by
    rw [Matrix.sub_mul, Matrix.mul_assoc P U' y', hU', Matrix.mul_assoc U P y']
    simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, hU]
    abel
  have hX : U * P - P * U' = s⁻¹ • ((U * P - P * U') * y' * Y₁'.map θ') := by
    rw [Matrix.mul_assoc (U * P - P * U') y', hY₁', Matrix.mul_smul, Matrix.mul_one, smul_smul,
      inv_mul_cancel₀ hs0, one_smul]
  intro i j
  rw [hX, key]
  have hsq : q ≤ ‖s‖⁻¹ * q := le_mul_of_one_le_left hq hci
  have b1 : ∀ i j, ‖(U * (P * y' - y * Ry)) i j‖ ≤ ‖s‖⁻¹ * q := bnd_mul (by positivity) hq hUb bD1
  have b2 : ∀ i j, ‖(y * (e * Ry - Ry * e')) i j‖ ≤ ‖s‖⁻¹ * q := fun i j =>
    (bnd_mul zero_le_one hq (hb1 Y) bD2 i j).trans (by rw [one_mul]; exact hsq)
  have b3 : ∀ i j, ‖((P * y' - y * Ry) * e') i j‖ ≤ ‖s‖⁻¹ * q := fun i j =>
    (bnd_mul hq zero_le_one bD1 (hb1 _) i j).trans (by rw [mul_one]; exact hsq)
  have b4 := bnd_smul s⁻¹ (bnd_mul (by positivity) zero_le_one (bnd_sub (bnd_add b1 b2) b3) (hb1 Y₁'))
  calc _ ≤ _ := b4 i j
    _ = _ := by rw [norm_inv]; ring

end GlobalTheory.HTBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaConjBoundedCompatibleBreuilKisinFramesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_conj_bounded_compatible_breuilKisin_frames : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N : ℕ), ∃ Bd : ℝ, ∀ (N' d d' n : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') (ℤ_[l])) (F : Frame bk N' d ρ) (F' : Frame bk N d' ρ') (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Y' : Matrix (Fin d') (Fin d') (Ainf l)), N' = N → Y.map (inclW l) = inclW l τ ^ N • F.T → Y'.map (inclW l) = inclW l τ ^ N • F'.T → ∀ (g : ↥(GK K)) (U : Matrix (Fin d) (Fin d) (ℂ_[l])) (U' : Matrix (Fin d') (Fin d') (ℂ_[l])), U * Y.map ((Per.θD l).comp (aDp l)) = Y.map ((Per.θD l).comp (aDp l)) * (F.ε g).map ((Per.θD l).comp (aDp l)) → U' * Y'.map ((Per.θD l).comp (aDp l)) = Y'.map ((Per.θD l).comp (aDp l)) * (F'.ε g).map ((Per.θD l).comp (aDp l)) → (∀ i j, ‖U i j‖ ≤ Bd) ∧ (∀ i j, ‖U' i j‖ ≤ Bd) ∧ ∀ (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])) (R : Matrix (Fin d) (Fin d') (bk.S)), (∀ g i j, (l : ℤ_[l]) ^ n ∣ (Pi * ρ' g - ρ g * Pi) i j) → (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - F.T * R.map bk.evW) i j) → ∀ i j, ‖(U * Pi.map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) - Pi.map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) * U') i j‖ ≤ Bd * ((l : ℝ) ^ n)⁻¹ := by
  first | exact @GlobalTheory.HTBound.bounded_compat | exact GlobalTheory.HTBound.bounded_compat | (intros; apply GlobalTheory.HTBound.bounded_compat; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopeDvdPrimeOfAinf
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopeDvdPrimeOfAinf
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.EnvPush

theorem c_mem_of_mem_map {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (TB : TopBasis s I ι) (L : Ideal S) (i : ι) {x : A} (hx : x ∈ L.map s) : TB.c i x ∈ L := by
  have key : ∀ a : A, TB.c i (a * x) ∈ L := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      intro a
      rw [mul_comm, TB.c_mul]
      exact L.mul_mem_right _ hj
    | zero => intro a; rw [mul_zero, map_zero]; exact L.zero_mem
    | add y z _ _ hy hz => intro a; rw [mul_add, map_add (f := _)]; exact L.add_mem (hy a) (hz a)
    | smul b y _ hy => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hy (a * b)
  simpa using key 1

theorem coeff_map {S A S' A' ι : Type} [CommRing S] [CommRing A] [CommRing S'] [CommRing A'] {s : S →+* A}
    {s' : S' →+* A'} {I : Ideal S} {I' : Ideal S'} (TB : TopBasis s I ι) (TB' : TopBasis s' I' ι) (g : S →+* S')
    (qf : A →+* A') (hq : ∀ y, qf (s y) = s' (g y)) (hb : ∀ i, qf (TB.b i) = TB'.b i) (hI : I.map g ≤ I')
    (hH : IsHausdorff I' S') (x : A) (α : ι) : TB'.c α (qf x) = g (TB.c α x) := by
  classical
  refine sub_eq_zero.1 (hH.haus _ fun n => SModEq.zero.2 ((Ideal.mul_top _).ge ?_))
  have hF : ∀ i, i ∉ (TB.fin x n).toFinset ∪ {α} → TB.c i x ∈ I ^ n := fun i hi => by
    by_contra h
    exact hi (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).2 h))
  have hm : qf (x - ∑ i ∈ (TB.fin x n).toFinset ∪ {α}, s (TB.c i x) * TB.b i) ∈ (I' ^ n).map s' := by
    have h1 := Ideal.mem_map_of_mem qf (TB.approx x n _ hF)
    rw [Ideal.map_map, show qf.comp s = s'.comp g from RingHom.ext hq, ← Ideal.map_map, Ideal.map_pow] at h1
    exact Ideal.map_mono (Ideal.pow_right_mono hI n) h1
  have hc := c_mem_of_mem_map TB' _ α hm
  have e : TB'.c α (qf (x - ∑ i ∈ (TB.fin x n).toFinset ∪ {α}, s (TB.c i x) * TB.b i)) =
      TB'.c α (qf x) - g (TB.c α x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sub, map_sum, map_sum, Finset.sum_eq_single α]
    · rw [map_mul, hq, hb, TB'.c_mul, TB'.c_self, mul_one]
    · intro i _ hi
      rw [map_mul, hq, hb, TB'.c_mul, TB'.c_ne α i (Ne.symm hi), mul_zero]
    · intro h
      exact absurd (Finset.mem_union_right _ (Finset.mem_singleton_self α)) h
  rwa [e] at hc

end GlobalTheory.BSP.EnvPush


open GlobalTheory.BSP.EnvPush in
theorem GlobalTheory.BSP.envPush_dvd_l : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (An : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (q : Hom En.Q An.Q), q.comp En.inl = An.inl.comp bk.ι → q.comp En.inr = An.inr → ∀ x : En.Q.A, ((l : ℕ) : An.Q.A) ∣ q.f x → ((l : ℕ) : En.Q.A) ∣ x := by
  intro l _ K bk En An q hl hr x hx
  have hql : ∀ y : bk.prism.A, q.f (En.inl.f y) = An.inl.f (bk.ι.f y) := fun y =>
    congrArg (fun h : Hom bk.prism An.Q => h.f y) hl
  have hqr : ∀ y : bk.prism.A, q.f (En.inr.f y) = An.inr.f y := fun y =>
    congrArg (fun h : Hom bk.prism An.Q => h.f y) hr

  have hw : q.f En.w = An.w := by
    have e1 : q.f (En.inr.f (bk.toP X)) = An.inr.f (bk.toP X) := hqr _
    have e2 : En.inr.f (bk.toP X) = En.inl.f (bk.toP X) + En.inl.f (bk.toP bk.E) * En.w := En.w_eq
    have e3 : An.inr.f (bk.toP X) = An.inl.f (bk.ι.f (bk.toP X)) + An.inl.f (bk.ι.f (bk.toP bk.E)) * An.w :=
      An.w_eq
    have e4 : q.f (En.inl.f (bk.toP X) + En.inl.f (bk.toP bk.E) * En.w) =
        An.inl.f (bk.ι.f (bk.toP X)) + An.inl.f (bk.ι.f (bk.toP bk.E)) * q.f En.w :=
      (q.f.map_add _ _).trans (congrArg₂ (· + ·) (hql _) ((q.f.map_mul _ _).trans (congrArg (· * q.f En.w) (hql _))))
    have e5 := add_left_cancel (e4.symm.trans ((congrArg q.f e2).symm.trans (e1.trans e3)))
    have key : ∀ (b u v : An.Q.A), b ∈ nonZeroDivisors An.Q.A → b * u = b * v → u = v := fun b u v hb h =>
      sub_eq_zero.1 ((mul_left_mem_nonZeroDivisors_eq_zero_iff hb).1 (by rw [mul_sub, h, sub_self]))
    have hnz : An.inl.f (bk.ι.f (bk.toP bk.E)) ∈ nonZeroDivisors An.Q.A :=
      (GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk An.Q (An.inl.comp bk.ι) (An.inl.comp bk.ι)).1
    exact key _ _ _ hnz e5

  have hδ : ∀ (n : ℕ) (y : En.Q.A), q.f (En.Q.D.δ^[n] y) = An.Q.D.δ^[n] (q.f y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      exact (congrArg q.f (Function.iterate_succ_apply' _ n y)).trans ((q.f_δ _).trans
        ((congrArg An.Q.D.δ (ih y)).trans (Function.iterate_succ_apply' _ n _).symm))
  have hb : ∀ α, q.f (En.tb.b α) = An.tb.b α := by
    intro α
    refine (congrArg q.f (En.tb_b α)).trans ((map_finsuppProd q.f _ _).trans (Eq.trans ?_ (An.tb_b α).symm))
    exact Finsupp.prod_congr fun i _ =>
      (map_pow q.f _ _).trans (congrArg (· ^ α.1 i) ((hδ i En.w).trans (congrArg _ hw)))

  have hJ : (Ideal.span {((l : ℕ) : bk.prism.A)} ⊔ bk.prism.I).map bk.ι.f ≤
      Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ (ainfObj K).I := by
    refine Ideal.map_le_iff_le_comap.2 (sup_le (Ideal.span_le.2 (Set.singleton_subset_iff.2 ?_))
      fun y hy => Ideal.mem_sup_right (bk.ι.f_I y hy))
    show bk.ι.f ((l : ℕ) : bk.prism.A) ∈ Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ (ainfObj K).I
    rw [map_natCast]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have hH : IsHausdorff (Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ (ainfObj K).I) (ainfObj K).A :=
    (ainfObj K).complete.toIsHausdorff

  have key : ∀ α, An.tb.c α (q.f x) = bk.ι.f (En.tb.c α x) := fun α =>
    coeff_map En.tb An.tb bk.ι.f q.f hql hb hJ hH x α

  obtain ⟨y, hy⟩ := hx
  have hl' : ∀ α, ((l : ℕ) : bk.S) ∣ En.tb.c α x := fun α => by
    apply (GlobalTheory.T.breuilKisin_evW_isUnit_injective_dvd l K bk).2.2
    refine ⟨An.tb.c α y, ?_⟩
    calc bk.ι.f (En.tb.c α x) = An.tb.c α (q.f x) := (key α).symm
      _ = An.tb.c α (An.inl.f ((l : ℕ) : (ainfObj K).A) * y) := by rw [hy, map_natCast]
      _ = ((l : ℕ) : (ainfObj K).A) * An.tb.c α y := An.tb.c_mul α _ y
  have h := (GlobalTheory.T.dvd_iff_dvd_coeff_breuilKisin l K bk En.Q.A (En.inl.f : bk.S →+* En.Q.A) (Digits l) En.tb ((l : ℕ) : bk.S) x).2 hl'
  have hg : ∀ {R A : Type} [CommRing R] [CommRing A] (s : R →+* A) (y : A) (n : ℕ), s n ∣ y → (n : A) ∣ y :=
    fun s y n h => (map_natCast s n) ▸ h
  exact hg _ _ _ h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopeDvdPrimeOfAinfStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_envelope_dvd_prime_of_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (An : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (q : Hom En.Q An.Q), q.comp En.inl = An.inl.comp bk.ι → q.comp En.inr = An.inr → ∀ x : En.Q.A, ((l : ℕ) : An.Q.A) ∣ q.f x → ((l : ℕ) : En.Q.A) ∣ x := by
  first | exact @GlobalTheory.BSP.envPush_dvd_l | exact GlobalTheory.BSP.envPush_dvd_l | (intros; apply GlobalTheory.BSP.envPush_dvd_l <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EPowXiExtMemMan
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
variable {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem YD_xiExt (P : PhiMod O K l e a ι) (α : ℕ)
    (hb : ∀ d : P.D, E K l e ^ α • P.xi d ∈ P.Man) {w : Vec K a ι} (hw : w ∈ P.Mext (invL l (S O K e))) :
    YD t ϖ (E K l e ^ α • P.xiExt w) = ∑ k, ϖ.iD t K (fun τ => hatR O (w τ k)) •
      YD t ϖ (E K l e ^ α • P.xi (fun _ => Pi.single k 1)) := by
  funext i
  simp only [YD, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [← map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  congr 1
  funext τ
  have hw' : ∀ k, w τ k ∈ Rpi O K l e := fun k => invL_S_le_Rpi l e (mem_tot.1 hw τ k)
  have hb' : ∀ k, E K l e ^ α * P.xi (fun _ => Pi.single k 1) τ i ∈ Rpi O K l e := fun k =>
    mem_Rpi_of_mem_Man (hb (fun _ => Pi.single k 1)) τ i
  have hx : ∀ k, P.xi (fun _ => Pi.single k 1) τ i = P.xiMat τ i k := fun k => by
    rw [P.xi_apply, P.xiExt_apply]
    have : (cst (fun _ => Pi.single k 1 : P.D) : Vec K a ι) τ = Pi.single k 1 := by
      funext j
      change C ((Pi.single k 1 : ι → K) j) = _
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp
    rw [this]
    simp
  have hs : E K l e ^ α * P.xiExt w τ i = ∑ k, w τ k * (E K l e ^ α * P.xi (fun _ => Pi.single k 1) τ i) := by
    simp only [hx, P.xiExt_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hm : (∑ k, w τ k * (E K l e ^ α * P.xi (fun _ => Pi.single k 1) τ i)) ∈ Rpi O K l e :=
    Subalgebra.sum_mem _ fun k _ => mul_mem (hw' k) (hb' k)
  rw [hs, hatR_of_mem (O := O) hm, Finset.sum_apply]
  simp only [Pi.mul_apply, hatR_of_mem (O := O) (hw' _), hatR_of_mem (O := O) (hb' _), ← map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  congr 1
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  rfl


omit [NeZero a] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem cst_mem_Mext (P : PhiMod O K l e a ι) (d : P.D) : (cst d : Vec K a ι) ∈ P.Mext (invL l (S O K e)) := by
  refine mem_tot.2 fun τ i => ?_
  exact HasK.C_mem (d τ i)


omit [NeZero a] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem descN_mem_Mext (P : PhiMod O K l e a ι) (i : ℕ) (w : Vec K a ι) (hw : w ∈ P.Mext (invL l (S O K e))) :
    (fun τ j => descN K i (w τ j)) ∈ P.Mext (invL l (S O K e)) := by
  refine mem_tot.2 fun τ j => ?_
  obtain ⟨n, hn⟩ := mem_tot.1 hw τ j
  refine ⟨n, ?_⟩
  have h3 : (((l : S O K e) : K⟦X⟧)) ^ n = C ((l : K) ^ n) := by simp
  have h := descN_mem_S e i hn
  rwa [h3, ← smul_eq_C_mul, map_smul, smul_eq_C_mul, ← h3] at h

theorem E_pow_xiExt_mem_Man (P : PhiMod O K l e a ι) (α : ℕ) (hα : ∀ v ∈ P.L, E K l e ^ α • v ∈ P.M)
    (w : Vec K a ι) (hw : w ∈ P.Mext (invL l (S O K e))) : E K l e ^ α • P.xiExt w ∈ P.Man := by
  have h1 : P.xiExt w ∈ P.MMl := ((GlobalTheory.BK.xi_trivialises_invL_S O K l e a ι P).2 w).2 hw
  refine P.mem_Man.2 (mem_tot.2 fun τ i => ?_)
  obtain ⟨m, hm, h⟩ := P.mem_extc.1 (mem_tot.1 h1 τ)
  have hc : ∀ k, E K l e ^ α * P.mx τ i k ∈ A O K := fun k => by
    have hv : (Pi.single τ ((P.mx τ).col k) : Vec K a ι) ∈ P.L := mem_tot.2 fun σ => by
      by_cases hσ : σ = τ
      · subst hσ
        rw [Pi.single_eq_same]
        exact Submodule.subset_span ⟨k, rfl⟩
      · rw [Pi.single_eq_of_ne hσ]
        exact zero_mem _
    have h2 := mem_tot.1 (hα _ hv) τ i
    rwa [Pi.smul_apply, Pi.single_eq_same] at h2
  rw [Pi.smul_apply, h, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Subalgebra.sum_mem _ fun k _ => ?_
  rw [← mul_assoc]
  exact mul_mem (invL_S_le_Rpi l e (le_away _ _ (A_le_S l e (hc k)))) (invL_S_le_Rpi l e (hm k))

theorem taylor_vec (P : PhiMod O K l e a ι) (α : ℕ)
    (hdesc : ∀ (i : ℕ) (w : Vec K a ι), w ∈ P.Mext (invL l (S O K e)) →
      (fun τ j => descN K i (w τ j)) ∈ P.Mext (invL l (S O K e)))
    (hman : ∀ w ∈ P.Mext (invL l (S O K e)), E K l e ^ α • P.xiExt w ∈ P.Man)
    (σ : OD l O → OD l O) (ρ : (ι → OD l O) →+ (ι → OD l O)) (hρ : ∀ c y, ρ (c • y) = σ c • ρ y) (c : OD l O)
    (hor : ∀ d : P.D, ρ (YD t ϖ (E K l e ^ α • P.xi d)) = c • YD t ϖ (E K l e ^ α • P.xi d))
    (μ : ℕ → OD l O) (R : ℕ) (J : Ideal (OD l O))
    (hscal : ∀ f : ZMod a → K⟦X⟧, (∀ τ, f τ ∈ invL l (S O K e)) → σ (ϖ.iD t K (fun τ => hatR O (f τ))) -
      ∑ i ∈ Finset.range R, μ i * ϖ.iD t K (fun τ => hatR O (descN K i (f τ))) ∈ J)
    {w : Vec K a ι} (hw : w ∈ P.Mext (invL l (S O K e))) (j : ι) :
    ρ (YD t ϖ (E K l e ^ α • P.xiExt w)) j - c * ∑ i ∈ Finset.range R, μ i *
      YD t ϖ (E K l e ^ α • P.xiExt (fun τ k => descN K i (w τ k))) j ∈ J := by
  have hb : ∀ d : P.D, E K l e ^ α • P.xi d ∈ P.Man := fun d => hman _ (cst_mem_Mext P d)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [YD_xiExt t ϖ P α hb hw, map_sum]
  simp only [YD_xiExt t ϖ P α hb (hdesc _ w hw), hρ, hor, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine J.sum_mem fun k _ => ?_
  have h := J.mul_mem_left (c * YD t ϖ (E K l e ^ α • P.xi (fun _ => Pi.single k 1)) j)
    (hscal (fun τ => w τ k) fun τ => mem_tot.1 hw τ k)
  convert h using 1
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.GalStep

namespace GlobalTheory.GalStep
variable {l : ℕ} [Fact l.Prime]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
def rhoDHom {LL : FinExt l} {ι : Type} (T : QLat LL)
    (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T) (g : Gl l) :
    (ι → OD l ↥(OL LL)) →+ (ι → OD l ↥(OL LL)) :=
  AddMonoidHom.mk' (rhoD T jD g) fun x y => by
    have h1 : jD (x + y) = jD x + jD y := jD.map_add x y
    have h2 := (TWact (galOD ↥(OL LL) (sQ l g)) T g).map_add (jD x) (jD y)
    have h3 := jD.symm.map_add (TWact (galOD ↥(OL LL) (sQ l g)) T g (jD x)) (TWact (galOD ↥(OL LL) (sQ l g)) T g (jD y))
    exact (congrArg (fun z => jD.symm (TWact (galOD ↥(OL LL) (sQ l g)) T g z)) h1).trans
      ((congrArg jD.symm h2).trans h3)
end GlobalTheory.GalStep
end
end

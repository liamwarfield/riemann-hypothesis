module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JetsTorsionTranslatesCmThetaProduct
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfNormConst
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmAMemSpanShort
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.NormSum.Term

def Bd {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (B : ℝ) (x : ℂ) : Prop :=
  x ∈ Qbar ∧ ‖lamC lam x‖ ≤ B

section
variable {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]}

theorem lamC_coe (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  simp [lamC, x.2]

theorem Bd.coe {B : ℝ} {x : Qbar} (h : ‖lam x‖ ≤ B) : Bd lam B (x : ℂ) :=
  ⟨x.2, by rwa [lamC_coe]⟩

theorem Bd.mono {B B' : ℝ} {x : ℂ} (h : Bd lam B x) (hB : B ≤ B') : Bd lam B' x :=
  ⟨h.1, h.2.trans hB⟩

theorem Bd.zero {B : ℝ} (hB : 0 ≤ B) : Bd lam B 0 := by
  have := Bd.coe (lam := lam) (B := B) (x := 0) (by simpa using hB)
  simpa using this

theorem Bd.add {B : ℝ} {x y : ℂ} (hx : Bd lam B x) (hy : Bd lam B y) : Bd lam B (x + y) := by
  obtain ⟨hx, h1⟩ := hx
  obtain ⟨hy, h2⟩ := hy
  lift x to Qbar using hx
  lift y to Qbar using hy
  rw [lamC_coe] at h1 h2
  have := Bd.coe (lam := lam) (B := B) (x := x + y) (by
    rw [map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2))
  simpa using this

theorem Bd.mul {A B : ℝ} {x y : ℂ} (hx : Bd lam A x) (hy : Bd lam B y) : Bd lam (A * B) (x * y) := by
  obtain ⟨hx, h1⟩ := hx
  obtain ⟨hy, h2⟩ := hy
  lift x to Qbar using hx
  lift y to Qbar using hy
  rw [lamC_coe] at h1 h2
  have := Bd.coe (lam := lam) (B := A * B) (x := x * y) (by
    rw [map_mul, norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1))
  simpa using this

theorem Bd.sum {ι : Type*} {B : ℝ} (hB : 0 ≤ B) (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, Bd lam B (f i)) :
    Bd lam B (∑ i ∈ s, f i) :=
  Finset.sum_induction f (Bd lam B) (fun _ _ => Bd.add) (Bd.zero hB) h

theorem Bd.intCast (z : ℤ) : Bd lam 1 (z : ℂ) := by
  have := Bd.coe (lam := lam) (B := 1) (x := (z : Qbar)) (by
    rw [map_intCast]
    exact IsUltrametricDist.norm_intCast_le_one _ z)
  simpa using this

theorem Bd.prod_coe {n : ℕ} {A : ℝ} (c : Fin n → Qbar) (h : ∀ i, ‖lam (c i)‖ ≤ A) :
    Bd lam (A ^ n) (∏ i, (c i : ℂ)) := by
  have := Bd.coe (lam := lam) (B := A ^ n) (x := ∏ i, c i) (by
    rw [map_prod, norm_prod]
    calc ∏ i, ‖lam (c i)‖ ≤ ∏ _i : Fin n, A :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => h i)
      _ = A ^ n := by simp)
  simpa using this

theorem bd_applyAt0 (D : D7) {a d n : ℕ} {B : ℝ} (hB : 0 ≤ B) (G : VC D a d → ℂ)
    (P : MvPolynomial (GL3Theta.Idx D a d) ℤ) (hP : P.IsHomogeneous n)
    (h : ∀ f : Fin n → GL3Theta.Idx D a d, Bd lam B (iteratedFDeriv ℂ n G 0 (fun i => coordV D (f i)))) :
    Bd lam B (GL3Theta.applyAt0 D (MvPolynomial.map (Int.castRingHom ℂ) P) G) := by
  have h' : ∀ m, m = n → ∀ f : Fin m → GL3Theta.Idx D a d,
      Bd lam B (iteratedFDeriv ℂ m G 0 (fun i => coordV D (f i))) := by
    rintro m rfl; exact h
  refine Bd.sum hB _ _ fun α hα => ?_
  have hα' : AddMonoidAlgebra.coeff P α ≠ 0 :=
    MvPolynomial.mem_support_iff.1 (MvPolynomial.support_map_subset _ _ hα)
  have hdeg : Multiset.card α.toMultiset = n := by
    have h1 := hP hα'
    rw [Finsupp.card_toMultiset]
    rw [← h1, Finsupp.weight_apply]
    simp only [Pi.one_apply, smul_eq_mul, mul_one]
    rfl
  have hne : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  unfold Formalism.MainNotions.TaylorLogMetric.taylor
  rw [mul_assoc, mul_div_cancel₀ _ hne, MvPolynomial.coeff_map]
  have := (Bd.intCast (lam := lam) (AddMonoidAlgebra.coeff P α)).mul (h' _ hdeg
    (fun i => α.toMultiset.toList.get ⟨i, by simpa using i.2⟩))
  rw [one_mul] at this
  exact this

theorem bd_coord (D : D7) {a d n : ℕ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (T : Tor D) (hT : ∀ τ x, T.emb τ x = embT D τ x)
    (Y : Set (Matrix (Fin d) (Fin a) D.host.E))
    (hL : ∀ k : GL3Theta.Idx D a d, ∃ (m : ℕ) (c : Fin m → Qbar) (y : Fin m → Matrix (Fin d) (Fin a) D.host.E),
        (∀ i, y i ∈ Y) ∧ (∀ i, ‖lam (c i)‖ ≤ A) ∧
        coordV D k = ∑ i, (c i : ℂ) • (fun τ s t => embT D τ (y i s t) : VC D a d))
    (φ : ContinuousMultilinearMap ℂ (fun _ : Fin n => VC D a d) ℂ)
    (h : ∀ y : Fin n → Matrix (Fin d) (Fin a) D.host.E, (∀ i, y i ∈ Y) → Bd lam B (φ fun i => embV D T (y i)))
    (f : Fin n → GL3Theta.Idx D a d) : Bd lam (A ^ n * B) (φ fun i => coordV D (f i)) := by
  choose m c y hy hc he using hL
  have h1 : (fun i => coordV D (f i)) = fun i => ∑ j, (c (f i) j : ℂ) • embV D T (y (f i) j) := by
    funext i
    rw [he]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    funext τ s t
    simp [embV, hT]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, φ.map_sum]
  refine Bd.sum (by positivity) _ _ fun r _ => ?_
  rw [φ.map_smul_univ, smul_eq_mul]
  exact (Bd.prod_coe (fun i => c (f i) (r i)) fun i => hc _ _).mul (h _ fun i => hy _ _)

end

def minorZ (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) : MvPolynomial (GL3Theta.Idx D a d) ℤ :=
  ∏ τ, ∏ j, (Matrix.of fun i i' : Fin a =>
    (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (GL3Theta.Idx D a d) ℤ)).det

theorem map_minorZ (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) :
    MvPolynomial.map (Int.castRingHom ℂ) (minorZ D T) = minorPol D T := by
  simp only [minorZ, minorPol, map_prod, RingHom.map_det]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_
  congr 1
  ext i i' : 2
  simp

theorem minorZ_homogeneous (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) :
    (minorZ D T).IsHomogeneous (a * ∑ τ, n τ) := by
  have h : a * ∑ τ, n τ = ∑ τ, ∑ _j : Fin (n τ), a := by
    simp [Finset.mul_sum, mul_comm]
  rw [h]
  refine MvPolynomial.IsHomogeneous.prod _ _ _ fun τ _ => MvPolynomial.IsHomogeneous.prod _ _ _ fun j _ => ?_
  rw [Matrix.det_apply']
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have h2 := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin a))
    (fun i => (MvPolynomial.X (τ, (T τ j).1 (σ i), i) : MvPolynomial (GL3Theta.Idx D a d) ℤ)) (fun _ => 1)
    (fun i _ => MvPolynomial.isHomogeneous_X _ _)
  have h3 := (MvPolynomial.isHomogeneous_C (GL3Theta.Idx D a d) ((Equiv.Perm.sign σ : ℤˣ) : ℤ)).mul h2
  simpa using h3

theorem differentiable_evenTheta (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (h : Crv D cc δ) :
    Differentiable ℂ (GL3Theta.th0 (lamOf D cc δ) t0) := by
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ h
  have hs : Differentiable ℂ (sgStar (lamOf D cc δ)) := by
    refine (GlobalTheory.OddTheta.sgStar_laws _ ⟨L.ω₁, L.ω₂, L.indep, ?_⟩).1.1
    ext z
    rw [hL, PeriodPair.lattice, ← Submodule.span_int_eq_addSubgroupClosure]
    rfl
  unfold GL3Theta.th0 U1
  fun_prop

theorem contDiff_U_pullB (D : D7) (T : Tor D) {a d r : ℕ} (b : Fin r → Matrix (Fin d) (Fin a) D.host.E)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) (s : VC D a d) (n : ℕ) : ContDiff ℂ n (U D T s (pullB D T b g)) := by
  have hg' : ContDiff ℂ n g := hg.contDiff
  have h1 : ContDiff ℂ n (pullB D T b g) := by
    unfold pullB coordB
    refine contDiff_prod fun j _ => ?_
    fun_prop
  unfold U Hf
  fun_prop

theorem norm_natCast_inv (p : ℕ) [Fact p.Prime] {Q : ℕ} (hQ : Q ≠ 0) :
    ‖(Q : ℂ_[p])‖⁻¹ = (p : ℝ) ^ (padicValNat p Q : ℝ) := by
  have h1 : (Q : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (Q : ℚ_[p]) := by simp
  rw [h1, norm_algebraMap', Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hQ), Padic.valuation_natCast]
  simp [Nat.padicValNat_def]

theorem iteratedFDeriv_comb {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : ℕ} (n : ℕ)
    (r : Fin k → ℂ) (G : Fin k → V → ℂ) (hG : ∀ i, ContDiff ℂ n (G i)) (y : Fin n → V) :
    iteratedFDeriv ℂ n (fun z => ∑ i, r i * G i z) 0 y = ∑ i, r i * iteratedFDeriv ℂ n (G i) 0 y := by
  have h1 : (fun z => ∑ i, r i * G i z) = ∑ i, r i • G i := by
    funext z; simp
  rw [h1, iteratedFDeriv_sum_apply (f := fun i => r i • G i) (fun i _ => ((hG i).const_smul (r i)).contDiffAt),
    sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_const_smul_apply (hG i).contDiffAt, smul_apply, smul_eq_mul]

theorem rpow_collect {x : ℝ} (hx : 0 < x) (c : Prop) [Decidable c] (n m : ℕ) (u v : ℝ) :
    (x ^ u) ^ n * ((x ^ v) ^ m * ((x ^ v) ^ n * (if c then x ^ ((n : ℝ) / 4) else 1))) =
      x ^ ((n : ℝ) * (u + (if c then 1 / 4 else 0) + v) + (m : ℝ) * v) := by
  have he' : (if c then x ^ ((n : ℝ) / 4) else 1) = x ^ ((n : ℝ) * (if c then 1 / 4 else 0)) := by
    split_ifs
    · congr 1; ring
    · simp
  rw [he', ← Real.rpow_mul_natCast hx.le, ← Real.rpow_mul_natCast hx.le, ← Real.rpow_mul_natCast hx.le,
    ← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_add hx]
  congr 1
  ring

theorem term_bound : ∀ (D : D7), Inp D → ∀ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl → ∀ (δ t0 : ℂ) (Q : ℕ), Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → GoodLevel D Q → ∀ (P : Pair D ⊤ δ t0 Q) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (g : GA D P.a) (g' k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p (g : GL (Fin P.a) (AE D)) → TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ∀ T, P.term g g' T ∈ Qbar ∧ ‖lamC lam (P.term g g' T)‖ ≤ (p : ℝ) ^ (((P.a * ∑ τ, P.n τ : ℕ) : ℝ) * (dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) + ((P.a * P.d : ℕ) : ℝ) * (padicValNat p Q : ℝ)) := by
  intro D hI S dl hL δ t0 Q hC ht hQ P p _ lam g g' k' hk hg hg' T
  obtain ⟨b, k, M, r, s, hb, hloc, hM, hMp, hs, hr, hF⟩ :=
    GlobalTheory.T.kernelAtPrime_eq_sum_torsionTranslates D hI δ t0 Q hC ht hQ.1 P p lam g g' k' hk hg hg'
  have hp : p.Prime := Fact.out
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hQn := norm_natCast_inv p hQ.1.ne'
  have hN : ‖((M * Q : ℕ) : ℂ_[p])‖⁻¹ = (p : ℝ) ^ (padicValNat p Q : ℝ) := by
    have hval : padicValNat p M = 0 := by
      simpa only [Nat.padicValNat_def] using
        (multiplicity_eq_zero_of_not_dvd (hp.coprime_iff_not_dvd.1 hMp.symm))
    rw [norm_natCast_inv p (Nat.mul_pos hM hQ.1).ne', (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hM.ne' hQ.1.ne',
      hval, zero_add]
  have hsp : p ∣ M * Q → SplitIn D p := fun h =>
    hQ.2 p hp (hMp.symm.dvd_of_dvd_mul_left h)
  have he0 : 0 ≤ (if p = D.host.d then (p : ℝ) ^ (((P.a * ∑ τ, P.n τ : ℕ) : ℝ) / 4) else 1) := by
    split_ifs <;> positivity
  rw [← rpow_collect hp0, Pair.term, ← map_minorZ, hF]
  refine bd_applyAt0 (lam := lam) D (by positivity) _ _ (minorZ_homogeneous D T) fun f => ?_
  refine bd_coord D (by positivity) (by positivity) (tor0 D ⊤ δ) (fun _ _ => rfl)
    (YYl D (stdL D P.a) (stdL D P.d)) (hL.2.2.2.2 p lam P.a P.d) _ (fun y hy => ?_) f
  rw [iteratedFDeriv_comb _ (fun i => (r i : ℂ))
    (fun i => U D (tor0 D ⊤ δ) (s i) (pullB D (tor0 D ⊤ δ) b (GL3Theta.th0 (lamOf D ⊤ δ) t0))) fun i =>
    contDiff_U_pullB D _ b _ (differentiable_evenTheta D ⊤ δ t0 hC) (s i) _]
  refine Bd.sum (by positivity) _ _ fun i _ => ?_
  have h1 := hr i
  rw [hQn] at h1
  refine (Bd.coe h1).mul ?_
  have := GlobalTheory.T.jets_torsion_translates_cm_theta_product D hI p lam ⊤ δ hC (by simp) t0 ht P.a P.d _ b hb hloc (s i) (M * Q)
    (Nat.mul_pos hM hQ.1) (hs i) hsp _ y hy
  rw [hN] at this
  exact this

end GlobalTheory.NormSum.Term
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBoundStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicValuation_thetaKernelJet_bound : ∀ (D : D7), Inp D → ∀ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl → ∀ (δ t0 : ℂ) (Q : ℕ), Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → GoodLevel D Q → ∀ (P : Pair D ⊤ δ t0 Q) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (g : GA D P.a) (g' k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p (g : GL (Fin P.a) (AE D)) → TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ∀ T, P.term g g' T ∈ Qbar ∧ ‖lamC lam (P.term g g' T)‖ ≤ (p : ℝ) ^ (((P.a * ∑ τ, P.n τ : ℕ) : ℝ) * (dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) + ((P.a * P.d : ℕ) : ℝ) * (padicValNat p Q : ℝ)) := by
  first | exact @GlobalTheory.NormSum.Term.term_bound | exact GlobalTheory.NormSum.Term.term_bound | (intros; apply GlobalTheory.NormSum.Term.term_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdemAtEqOneIff
noncomputable section

namespace GlobalTheory.FlatLine.Definite

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_bc {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) : ∃ z, FrMap φ y z :=
  GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c S T φ y

theorem frMap_of_comp {R S T : Type} [CommRing R] [Algebra c.F R] [CommRing S] [Algebra c.F S] [CommRing T]
    [Algebra c.F T] {φ : R →ₐ[c.F] S} {ψ : S →ₐ[c.F] T} {χ : R →ₐ[c.F] T} (h : ψ.comp φ = χ) {y : FrPt Xo c R}
    {z : FrPt Xo c S} {w : FrPt Xo c T} (hz : FrMap φ y z) (hw : FrMap χ y w) : FrMap ψ z w := by
  obtain ⟨w', hw'⟩ := exists_bc ψ z
  rwa [(frMap_unique_refl_iff E H Dw l Xo c R T χ y).1 w w' hw (h ▸ ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ hz hw')]

abbrev idemAt (Z : Comp Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : S :=
  CompSplitPfB.cspB_idem _ (CompSplitPfB.cspB_isClopen (CompSplitPfD.cspD_comp_disj Xo c) Z) y.x y.x_over

theorem idemAt_eq_one_iff (Z : Comp Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    idemAt Z y = 1 ↔ LiesOn Z y := by
  refine ⟨fun h q => (CompSplitPfB.cspB_idem_spec _
    (CompSplitPfB.cspB_isClopen (CompSplitPfD.cspD_comp_disj Xo c) Z) y.x y.x_over q).1 ?_, fun h => ?_⟩
  · show idemAt Z y ∉ _
    rw [h]
    exact (Ideal.ne_top_iff_one _).1 q.isPrime.ne_top
  · refine CompSplitPfB.cspB_idem_eq_of (CompSplitPfB.cspB_idem_idem _ _ _ _) IsIdempotentElem.one fun q => ?_
    rw [CompSplitPfB.cspB_idem_spec]
    exact iff_of_true (h q) ((Ideal.ne_top_iff_one _).1 q.isPrime.ne_top)

def IsCoef (Z : Comp Xo c) (y₀ : FrPt Xo c c.F) (τ : E →+* ℂ) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (s : S) : Prop :=
  idemAt Z y * s = s ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (w z : FrPt Xo c T)
    (g : (∀ ρ : E →+* ℂ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) T)) (a : T),
    FrMap φ y w → FrMap (Algebra.ofId c.F T) y₀ z → FrChg g a w z → φ s = (g τ).det

theorem eq_of_mk_eq {S : Type} [CommRing S] {e s t : S} (he : IsIdempotentElem e) (hs : e * s = s) (ht : e * t = t)
    (h : Ideal.Quotient.mk (Ideal.span {1 - e}) s = Ideal.Quotient.mk (Ideal.span {1 - e}) t) : s = t := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)
  have := he.eq
  linear_combination ht - hs - e * hb - b * this

theorem exists_isCoef {Z : Comp Xo c} {y₀ : FrPt Xo c c.F} (h₀ : LiesOn Z y₀)
    (hy₀ : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y →
      y.x = spMap (algebraMap c.F S) ≫ y₀.x) (τ : E →+* ℂ) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) : ∃ s s' : S, IsCoef Z y₀ τ y s ∧ (∀ t, IsCoef Z y₀ τ y t → t = s) ∧
      idemAt Z y * s' = s' ∧ s * s' = idemAt Z y := by
  have he : IsIdempotentElem (idemAt Z y) := CompSplitPfB.cspB_idem_idem _ _ _ _
  let π := Ideal.Quotient.mkₐ c.F (Ideal.span {1 - idemAt Z y})
  have hπ : π (idemAt Z y) = 1 := by
    rw [← map_one π]
    exact (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self _)).symm
  obtain ⟨w, hw⟩ := exists_bc π y
  obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F (S ⧸ Ideal.span {1 - idemAt Z y})) y₀
  have hwZ : LiesOn Z w := (idemAt_eq_one_iff Z w).1
    ((CompSplitPfB.cspB_idem_map _ _ π y.x_over w.x_over hw.1).symm.trans hπ)
  obtain ⟨g, a, hg, hc⟩ := (frChg_exists_unique E H Dw l Xo c _ w z).1 (hz.1.trans (hy₀ _ w hwZ).symm)
  obtain ⟨d', hd'⟩ := (hg τ).exists_right_inv
  obtain ⟨s, hs⟩ := Ideal.Quotient.mkₐ_surjective c.F _ (g τ).det
  obtain ⟨s', hs'⟩ := Ideal.Quotient.mkₐ_surjective c.F _ d'
  have k : ∀ t, idemAt Z y * (idemAt Z y * t) = idemAt Z y * t := fun t => by rw [← mul_assoc, he.eq]
  have hs₁ : π (idemAt Z y * s) = (g τ).det := by rw [map_mul, hπ, one_mul]; exact hs
  have hs₂ : π (idemAt Z y * s') = d' := by rw [map_mul, hπ, one_mul]; exact hs'
  refine ⟨idemAt Z y * s, idemAt Z y * s', ⟨k s, fun T _ _ φ w' z' g' a' hw' hz' hc' => ?_⟩,
    fun t ht => eq_of_mk_eq he ht.1 (k s) ((ht.2 _ π w z g a hw hz hc).trans hs₁.symm), k s',
    eq_of_mk_eq he (by rw [← mul_assoc, k]) he.eq ?_⟩
  · have h1 : φ (idemAt Z y) = 1 := (CompSplitPfB.cspB_idem_map _ _ φ y.x_over w'.x_over hw'.1).trans
      ((CompSplitPfB.cspB_idem_congr _ _ z'.x_over w'.x_over hc'.1.symm).trans
        ((idemAt_eq_one_iff Z z').2 (liesOn_frMap hz' h₀)))
    let ψ := Ideal.Quotient.liftₐ (Ideal.span {1 - idemAt Z y}) φ fun b hb => by
      obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.1 hb
      rw [map_mul, map_sub, h1, map_one, sub_self, mul_zero]
    have hψ : ψ.comp π = φ := Ideal.Quotient.liftₐ_comp _ _ _
    have c₁ := (ChgBC.frChg_baseChange E H Dw l Xo c _ T ψ w z w' z' g a hc (frMap_of_comp hψ hw hw')).1
      (frMap_of_comp (Subsingleton.elim _ _) hz hz')
    rw [((frChg_exists_unique E H Dw l Xo c T w' z').2 _ _ _ _ hc' c₁).1, ← hψ, AlgHom.comp_apply, hs₁]
    exact ψ.toRingHom.map_det (g τ)
  · show π _ = π _
    rw [map_mul, hs₁, hs₂, hd', hπ]

theorem prod_exOf_flatWt (hq : Dw.q = 0) (τ : Psi H) {G : Type} [CommGroup G] (t : Ix Dw → G) :
    ∏ i, t i ^ exOf Dw (flatWt Dw τ) 0 i = (∏ i, t (some ⟨τ.1, i⟩))⁻¹ := by
  have h : ∀ (ρ : E →+* ℂ) (i : Fin (Dw.mult ρ)),
      exOf Dw (flatWt Dw τ) 0 (some ⟨ρ, i⟩) = open Classical in if ρ = τ.1 then -1 else 0 := fun ρ i => by
    have hi := i.2
    have hρ : ρ (H.rt : E) = H.rt0 := by
      by_contra hn
      simp [Datum.mult, hn, hq] at hi
    refine (wtOf_big (flatWt Dw τ) 0 ⟨ρ, hρ⟩ i (by simpa [Datum.mult, hρ] using hi)).trans ?_
    simp only [flatWt, parWt, sub_zero]
    by_cases h1 : ρ = τ.1
    · rw [if_pos h1, if_pos (Subtype.ext h1)]
    · rw [if_neg h1, if_neg fun h2 => h1 (congrArg Subtype.val h2)]
  have h0 : exOf Dw (flatWt Dw τ) 0 none = 0 := rfl
  rw [Fintype.prod_option, h0, zpow_zero, one_mul, Fintype.prod_sigma, Finset.prod_eq_single τ.1
    (fun ρ _ hρ => by simp [h, hρ]) (by simp)]
  simp [h]

theorem inv_mem_secZ_on {Z : Comp Xo c} {e : Ix Dw → ℤ} {f f' : Rul Xo c} (hf : f ∈ secZ Xo c e)
    (h1 : idem Z * f' = f') (h2 : f * f' = idem Z) : f' ∈ secZ Xo c (-e) := by
  have k1 : ∀ p y, idem Z p y * f' p y = f' p y := fun p y => congrFun (congrFun h1 p) y
  have k2 : ∀ p y, f p y * f' p y = idem Z p y := fun p y => congrFun (congrFun h2 p) y
  have hi := idem_mem_secZ Z
  refine ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩
  · have a1 := congrArg φ (k1 p y)
    have a2 := congrArg φ (k2 p y)
    rw [map_mul, ← hi.1 p q φ y z h] at a1
    rw [map_mul, ← hi.1 p q φ y z h, ← hf.1 p q φ y z h] at a2
    linear_combination a1 - k1 q z - f' q z * a2 + φ (f' p y) * k2 q z
  · have a1 := k2 p y'
    have a0 : idem Z p y' = idem Z p y := by simpa using hi.2 p t y y' h
    have a4 := k1 p y'
    rw [hf.2 p t y y' h, a0] at a1
    rw [a0] at a4
    have a3 : ((∏ i, t i ^ (-e) i : (p.R)ˣ) : p.R) * ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) = 1 := by
      rw [← Units.val_mul, ← Finset.prod_mul_distrib]; simp
    generalize ((∏ i, t i ^ (-e) i : (p.R)ˣ) : p.R) = A at *
    generalize ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) = B at *
    linear_combination A * f' p y * a1 - a4 - f' p y' * k2 p y + A * k1 p y - f p y * f' p y * f' p y' * a3

theorem exists_flatRule : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.q = 0 → ∀ (Z : Comp Xo c) (τ : Psi H) (y₀ : FrPt Xo c c.F), LiesOn Z y₀ → (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → y.x = spMap (algebraMap c.F S) ≫ y₀.x) → ∃ f f' : Rul Xo c, f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) ∧ f' ∈ secZ Xo c (-exOf Dw (flatWt Dw τ) 0) ∧ idem Z * f = f ∧ idem Z * f' = f' ∧ f * f' = idem Z ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y z : FrPt Xo c S) (g : (∀ ρ : E →+* ℂ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) S)) (a : S), Tested y → FrMap (Algebra.ofId c.F S) y₀ z → FrChg g a y z → evR Xo c f y = (g τ.1).det := by
  intro E _ _ _ H Dw l Xo c hq Z τ y₀ h₀ hy₀
  choose f f' hf hu h1 h2 using fun (p : TRing c.F) (y : FrPt Xo c p.R) => exists_isCoef h₀ hy₀ τ.1 y
  have i1 : idem Z * f' = f' := funext fun p => funext fun y => h1 p y
  have i2 : (f : Rul Xo c) * f' = idem Z := funext fun p => funext fun y => h2 p y
  have hm : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) := by
    refine ⟨fun p q φ y z h => (hu q z _ ⟨?_, fun T _ _ ψ w z' g a hw hz hc => ?_⟩).symm,
      fun p t y y' h => (hu p y' _ ⟨?_, fun T _ _ ψ w' z' g a hw hz hc => ?_⟩).symm⟩
    · rw [idemAt, ← CompSplitPfB.cspB_idem_map _ _ φ y.x_over z.x_over h.1, ← map_mul]
      exact congrArg φ (hf p y).1
    · exact (hf p y).2 T (ψ.comp φ) w z' g a (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ h hw) hz hc
    · rw [mul_left_comm, idemAt, CompSplitPfB.cspB_idem_congr _ _ y.x_over y'.x_over h.1]
      exact congrArg _ (hf p y).1
    · obtain ⟨k, k0, k1, hk⟩ := ((frBor_calculus E H Dw l Xo c _ y y' y').1 t).1 h
      obtain ⟨w, hw₀⟩ := exists_bc ψ y
      have c₁ := (ChgBC.frChg_baseChange E H Dw l Xo c _ T ψ y y' w w' k _ hk hw₀).1 hw
      have c₂ := (frChg_refl_and_comp E H Dw l Xo c T w w' z').2 _ _ _ _ c₁ hc
      have hd : (k τ.1).det = ((∏ i, t (some ⟨τ.1, i⟩) : (p.R)ˣ) : p.R) := by
        rw [Matrix.det_of_isLowerTriangular _ (fun i j hij => k0 τ.1 i j hij), Units.coe_prod]
        exact Finset.prod_congr rfl fun i _ => k1 τ.1 i
      have hd' : ((k τ.1).map ψ).det = ψ (k τ.1).det := (ψ.toRingHom.map_det (k τ.1)).symm
      rw [map_mul, (hf p y).2 T ψ w z' _ _ hw₀ hz c₂, Matrix.det_mul, hd', hd, prod_exOf_flatWt hq, mul_left_comm,
        ← map_mul, Units.inv_mul, map_one, mul_one]
  refine ⟨f, f', hm, inv_mem_secZ_on hm i1 i2, funext fun p => funext fun y => (hf p y).1, i1, i2,
    fun S _ _ y z g a ht hz hc => ?_⟩
  unfold evR evalAt
  rw [dite_eq_left ht]
  exact (hf _ _).2 S _ y z g a ht.choose_spec.choose_spec.choose_spec hz hc

end GlobalTheory.FlatLine.Definite
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCovPinNotIsXiDet
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ShortSpanUnitOfExactValues
section -- merged from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ShortRuleRepresentationChange
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab)

def CoverVal {S : Type} [CommRing S] [Algebra Δ.cov.c₂.F S] (y₂ : FrPt Δ.cov.Xo₂ Δ.cov.c₂ S) {n : ℕ} (Λ : Lat E n)
    (N : ℕ) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (v : S) : Prop :=
  ThVal Δ.cov.Xo₂ Δ.cov.c₂ Δ.nab₂ y₂ Λ N (Δ.cov.incl β) (Δ.combinedCoeff x₀) a (MvPolynomial.map Δ.cov.incl P) v

def IsShortRule {n : ℕ} (Λ : Lat E n) (N : ℕ) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R),
    (∃ (S' : Type) (_ : CommRing S') (_ : Algebra Δ.cov.c₂.F S') (φ : p.R →+* S')
      (y₂ : FrPt Δ.cov.Xo₂ Δ.cov.c₂ S'), φ.FaithfullyFlat ∧ Δ.cov.LiesOver φ y₂ y) ∧
    ∀ (S' : Type) [CommRing S'] [Algebra Δ.cov.c₂.F S'] (φ : p.R →+* S') (y₂ : FrPt Δ.cov.Xo₂ Δ.cov.c₂ S'),
      Δ.cov.LiesOver φ y₂ y → ∃ v, CoverVal Δ y₂ Λ N β x₀ a P v ∧ φ (f p y) = v * Δ.fnVal y₂

def ramPart (E : Type) [Field E] [NumberField E] : ℕ := 2 * (discr E).natAbs

def reps (n : ℕ) (s : ℕ+) : Set (Lat E n) :=
  {Λ | Λ.InGenus ∧ Λ.StdAt (ramPart E * Δ.a.l₂.M * s)}

def IsPairIso {n : ℕ} (γ : (Fin n → E) ≃ₗ[E] (Fin n → E)) (Λ Λ' : Lat E n) : Prop :=
  IsUnitary γ ∧ (Λ.map γ).L = Λ'.L ∧
    ∀ x ∈ Λ.L, ∃ k : ℕ, k.Coprime Δ.a.l₂.M ∧ k • (γ x - x) ∈ mulStd E n Δ.a.l₂.M

def MeetsAllClasses {n : ℕ} (T : Set (Lat E n)) : Prop :=
  T ⊆ reps Δ n 1 ∧ ∀ Λ ∈ reps Δ n 1, ∃ Λ' ∈ T, ∃ γ, IsPairIso Δ γ Λ Λ'

def IsSeriesData {n : ℕ} (Λ : Lat E n) (N : ℕ) (β : c.F) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  Λ ∈ reps Δ n 1 ∧ Λ.Admissible Δ.a.l₂.M N ∧ IsBeLat Dw c Λ β ∧ P ∈ harmLat Dw c a Λ

def shortGen (hK : ReflexLe Dw c) (nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Rul Xo c) :=
  {f | ∃ (Λ : Lat E n) (N : ℕ) (x₀ : Fin n → ConjCl Dw l) (P : MvPolynomial (LtN Dw n) c.F),
    IsSeriesData Δ Λ N (be hK Λ) a P ∧ LevelSpanSeparation.Admissible nV x₀ ∧ IsShortRule Δ Λ N (be hK Λ) x₀ a P f}

def Descends : Prop :=
  ∀ (n N : ℕ) (Λ : Lat E n) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F), IsSeriesData Δ Λ N β a P →
    ∃ f ∈ sec Xo c a n, IsShortRule Δ Λ N β x₀ a P f

def OnePos (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : Prop :=
  ∃ τ : E →+* ℂ, InPsi H τ ∧ (0 < Dw.p → 1 ≤ a (τ, Dw.p - 1))

def ShortInCusp (hK : ReflexLe Dw c) (nV : ℕ)
    (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → OnePos Dw a → ∀ f ∈ shortGen Δ hK nV a n, f ∈ cusp a n



end GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism
end
end

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortSpanCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient
open GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation hiding zetaM
open GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism hiding IsShortRule shortGen ShortInCusp
open GlobalTheory.GenusLatCompare GlobalTheory.LevelCoverCompare GlobalTheory.ShortDatumEq GlobalTheory.TransferCompare

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

section Generators

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab)

theorem evR_of_frMap {f : Rul Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hf : f ∈ sec Xo c a n) {p : TRing c.F}
    {S : Type} [CommRing S] [Algebra c.F S] (φ : p.R →ₐ[c.F] S) {y : FrPt Xo c p.R} {z : FrPt Xo c S}
    (h : FrMap φ y z) : evR Xo c f z = φ (f p y) := by
  have hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, φ, y, h⟩
  unfold evR evalAt
  rw [dite_eq_left hT]
  exact evalWD_framed Xo c f hf.1 S _ _ _ _ _ _ z hT.choose_spec.choose_spec.choose_spec h

variable {Δ}

end Generators

section Spans

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ)

variable {Δ}

end Spans

section Claims

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ)
  (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c))

variable {Δ hK nV}

end Claims

section Std

variable (Xo c) (nab : NabV Xo c)

variable {Xo c nab}

variable (Xo c nab)

variable {Xo c nab}

end Std

end GlobalTheory.ShortSpanCompare
end
end

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverPinCompare

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ClsVal.Cmp (OverBase overBase_of_ne eq_incl coe_incl spMap_comp')

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem nonempty_lift {K L : Type} [Field K] [Field L] [Algebra K L] [Algebra K ℂ] [Module.Finite K L] :
    Nonempty (L →ₐ[K] ℂ) := ⟨IsAlgClosed.lift⟩

theorem exists_algHom_ker {K : Type} [Field K] (σ : K →+* ℂ) (p : TRing K) (m : Ideal p.R) [hm : m.IsMaximal] :
    ∃ ψ : p.R →ₐ[K] CAt σ, ∀ x, ψ x = 0 ↔ x ∈ m := by
  letI : Algebra K ℂ := σ.toAlgebra
  letI := Ideal.Quotient.field m
  haveI : Module.Finite K (p.R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K _
  obtain ⟨j⟩ := nonempty_lift (K := K) (L := p.R ⧸ m)
  refine ⟨(j.comp (Ideal.Quotient.mkₐ K m) : p.R →ₐ[K] ℂ), fun x => ?_⟩
  exact (map_eq_zero_iff j j.toRingHom.injective).trans Ideal.Quotient.eq_zero_iff_mem

theorem eq_of_complex (σ : c.F →+* ℂ) {f f' : Rul Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {w : ℕ} (hf : f ∈ sec Xo c a w)
    (hf' : f' ∈ sec Xo c a w) (h : ∀ y : FrPt Xo c (CAt σ), evR Xo c f y = evR Xo c f' y) : f = f' := by
  funext p y
  haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  haveI : IsJacobsonRing p.R := isJacobsonRing_of_finiteType (A := c.F)
  have hj : (⊥ : Ideal p.R).jacobson = ⊥ := IsJacobsonRing.out inferInstance (Ideal.isRadical_bot)
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← hj, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨-, hm⟩
  obtain ⟨ψ, hψ⟩ := exists_algHom_ker σ p m
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c _ _ ψ y
  rw [← hψ, map_sub, ← GlobalTheory.ShortSpanCompare.evR_of_frMap hf ψ hz, ← GlobalTheory.ShortSpanCompare.evR_of_frMap hf' ψ hz, h, sub_self]

section Pins

variable [StarRing (𝓞 E)]


variable {Tup : Type} (σ : c.F →+* ℂ) (Q : Tup → Finset (Ideal (𝓞 E))) (xi : Tup → (Ideal (𝓞 E) →*₀ c.F))
  (I : Tup → Ideal (𝓞 E))

end Pins


end GlobalTheory.CoverPinCompare
end
end

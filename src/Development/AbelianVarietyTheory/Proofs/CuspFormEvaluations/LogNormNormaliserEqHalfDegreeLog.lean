module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueExistsUniqueOfChartIndependence
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogNormNormaliserEqHalfDegreeLog
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogNormMapPowMulPowOfMulConj
open scoped BigOperators

namespace GlobalTheory

theorem norm_map_eq_sqrt_of_mul_conj {K : Type*} [Semiring K] (σ : K →+* ℂ) (x y : K) (g : ℕ)
    (hxy : x * y = g) (hy : σ y = starRingEnd ℂ (σ x)) : ‖σ x‖ = (g : ℝ) ^ (1 / 2 : ℝ) := by
  have h : σ x * starRingEnd ℂ (σ x) = (g : ℂ) := by
    rw [← hy, ← map_mul, hxy, map_natCast]
  have h2 : ((‖σ x‖ : ℝ) : ℂ) ^ 2 = (g : ℂ) := by
    rw [← Complex.mul_conj', h]
  have h3 : ‖σ x‖ ^ 2 = (g : ℝ) := by exact_mod_cast h2
  rw [← Real.sqrt_eq_rpow, ← h3, Real.sqrt_sq (norm_nonneg _)]

theorem norm_map_pow_mul_pow_of_mul_conj {K : Type*} [Semiring K] (σ : K →+* ℂ) (x y : K) (g : ℕ)
    (hxy : x * y = g) (hy : σ y = starRingEnd ℂ (σ x)) (a b : ℕ) :
    ‖σ (x ^ a * y ^ b)‖ = (g : ℝ) ^ (((a : ℝ) + b) / 2) := by
  have h1 := norm_map_eq_sqrt_of_mul_conj σ x y g hxy hy
  have hyn : ‖σ y‖ = ‖σ x‖ := by rw [hy]; simp
  rw [map_mul, map_pow, map_pow, norm_mul, norm_pow, norm_pow, hyn, ← pow_add, h1,
    ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg g)]
  congr 1
  push_cast
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogNormNormaliserEqHalfDegreeLog
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem normaliser_factor_mul_bar {D : D7} (EX : ErrX D) (i : Fin 2) :
    EX.piG i * piBarO EX i = ((D.host.g i : ℕ) : 𝓞 D.host.E) := by
  apply NumberField.RingOfIntegers.ext
  simpa [piBarO, NumberField.RingOfIntegers.mapRingHom_apply] using EX.piG_norm i

theorem map_piBar_eq_conj {D : D7} (EX : ErrX D) (i : Fin 2) (ρ : 𝓞 D.host.E →+* ℂ)
    (hρ : Function.Injective ρ) : ρ (piBarO EX i) = starRingEnd ℂ (ρ (EX.piG i)) := by
  let ψ : D.host.E →+* ℂ := IsFractionRing.lift hρ
  have hψ : ∀ x : 𝓞 D.host.E, ψ (x : D.host.E) = ρ x := fun x => IsFractionRing.lift_algebraMap hρ x
  rw [← hψ (piBarO EX i), ← hψ (EX.piG i), piBarO, NumberField.RingOfIntegers.mapRingHom_apply]
  exact D.host.toHostAx.conjE_apply ψ _

theorem log_norm_normaliser : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (w : WeightFamilies.Wt D j) (σ : B.KO →+* ℂ), nnW B hinj EX w ≠ 0 ∧ Real.log ‖σ (nnW B hinj EX w : B.KO)‖ = (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by
  intro D B hinj EX j w σ
  set ρ : 𝓞 D.host.E →+* ℂ := σ.comp ((algebraMap (𝓞 B.KO) B.KO).comp (iE D hinj B)) with hρdef
  have hρ : Function.Injective ρ :=
    σ.injective.comp ((IsFractionRing.injective (𝓞 B.KO) B.KO).comp (iE_injective D hinj B))
  have hg : ∀ i : Fin 2, (0 : ℝ) < (D.host.g i : ℝ) := fun i => by
    exact_mod_cast (D.host.g_prime i).pos
  have hval : σ ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) =
      ∏ i : Fin 2, ρ (EX.piG i ^ Dplus w * piBarO EX i ^ Dminus w) := by
    simp [nnW, hρdef, map_prod, map_mul, map_pow]
  have hnorm : ‖σ ((nnW B hinj EX w : 𝓞 B.KO) : B.KO)‖ =
      ∏ i : Fin 2, (D.host.g i : ℝ) ^ (((Dplus w : ℝ) + Dminus w) / 2) := by
    rw [hval, norm_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact norm_map_pow_mul_pow_of_mul_conj ρ _ _ _ (normaliser_factor_mul_bar EX i)
      (map_piBar_eq_conj EX i ρ hρ) _ _
  have hDF : WeightAlgebra.DF w = Dplus w + Dminus w := by
    simp only [WeightAlgebra.DF, WeightAlgebra.degP, Dplus, Dminus, Finset.sum_add_distrib]
  have h0 := Real.rpow_pos_of_pos (hg 0) (((Dplus w : ℝ) + Dminus w) / 2)
  have h1 := Real.rpow_pos_of_pos (hg 1) (((Dplus w : ℝ) + Dminus w) / 2)
  refine ⟨fun hz => ?_, ?_⟩
  · have hz' : ‖σ ((nnW B hinj EX w : 𝓞 B.KO) : B.KO)‖ = 0 := by rw [hz]; simp
    rw [hnorm, Fin.prod_univ_two] at hz'
    nlinarith [mul_pos h0 h1]
  · rw [hnorm, Fin.prod_univ_two, Real.log_mul h0.ne' h1.ne', Real.log_rpow (hg 0), Real.log_rpow (hg 1),
      Real.log_mul (hg 0).ne' (hg 1).ne', hDF]
    push_cast
    ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogNormNormaliserEqHalfDegreeLogStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norm_normaliser_eq_half_degree_log : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (w : WeightFamilies.Wt D j) (σ : B.KO →+* ℂ), nnW B hinj EX w ≠ 0 ∧ Real.log ‖σ (nnW B hinj EX w : B.KO)‖ = (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by
  first | exact @GlobalTheory.log_norm_normaliser | exact GlobalTheory.log_norm_normaliser | (intros; apply GlobalTheory.log_norm_normaliser <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointsInterpolationGenericSections
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointsInterpolationGenericSections
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem addL_zero_pts {D : D7} {j : ℕ} (u wL : WeightFamilies.Wt D j) : addL u wL 0 = u := by
  show wadd u (wsmul 0 wL) = u
  cases u
  simp [wadd, wsmul]

theorem rdg_s_apply {D : D7} {T : Top D} {h : LawsP T} {j : ℕ} {hj : InR D j} {n : SecNorm (recB h.toLawsCore)}
    {R : Rdg (recPlusN h j hj n)} {e : R.Y ≃ DomPt T j} (hR : IsRdgU h j hj n R e) {N : ℕ} {wL : WeightFamilies.Wt D j}
    (w : Fin N → (recB h.toLawsCore).Cusp j wL) (t : Idx D j N → ℂ) (i : Fin (WeightFamilies.dimY D j + 1)) (y : R.Y) :
    R.s w t i y = ∑ k, t (i, k) * rdR h j (w k) (e y).1 (e y).2.1 := by
  simp only [Rdg.s, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2]

theorem mem_sp_of_rdOnto {D : D7} {T : Top D} {h : LawsP T} {j : ℕ} {hj : InR D j} {n : SecNorm (recB h.toLawsCore)}
    {R : Rdg (recPlusN h j hj n)} {e : R.Y ≃ DomPt T j} (hR : IsRdgU h j hj n R e) {u : WeightFamilies.Wt D j}
    (hO : RdOnto h j u) (f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ)
    (hf : ∀ k, f k ∈ ((T.U j T.σ₀).X k).SS (laR T j u k)) :
    (fun y => f (e y).1 (e y).2.1) ∈ R.sp u Set.univ := by
  obtain ⟨m, a, F, -, hF⟩ := hO f hf
  have hfun : (fun y => f (e y).1 (e y).2.1) = ∑ i, a i • R.ev ((recPlusN h j hj n).inc u (F i)) := by
    funext y
    rw [hF _ _ (e y).2.2]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2]
  rw [hfun]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨F i, Set.mem_univ _, rfl⟩)

theorem points_and_interp : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → (∀ q, R.s w t 0 (xs q) ≠ 0 ∧ ∀ i : Fin (WeightFamilies.dimY D j), R.s w t i.succ (xs q) = 0) ∧ ∀ v : Fin δ → ℂ, ∃ f ∈ R.sp wF Set.univ, ∀ q, f (xs q) = v q := by
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en hxs hO

  have hvan : ∀ (k : (T.U j T.σ₀).Comp) (a : Fin (nd ((T.U j T.σ₀).X k))) (p : Fin (Fl.Fl k).δ),
      (Fl.Fl k).s a ((Fl.Fl k).xs p) = 0 := by
    intro k a p
    have hb : (fun _ => (1 : Matrix (Fin D.R.r) (Fin D.R.r) ℂ) : Frame ((T.U j T.σ₀).X k).Ψ D.R.r) ∈
        Bor ((T.U j T.σ₀).X k).Ψ D.R.r := by
      intro τ
      refine ⟨?_, fun a c hca => Matrix.one_apply_ne hca.ne'⟩
      show (1 : Matrix (Fin D.R.r) (Fin D.R.r) ℂ).det ≠ 0
      simp
    have hself : (Fl.Fl k).xs p = lact 1 (rmul ((Fl.Fl k).xs p)
        (fun _ => (1 : Matrix (Fin D.R.r) (Fin D.R.r) ℂ))) := by
      funext τ a c
      simp only [lact, rmul, mat, Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), one_mul]
      have hm : (Matrix.of ((Fl.Fl k).xs p τ) : Matrix (Fin D.R.r) (Fin D.R.r) ℂ) * 1 =
          Matrix.of ((Fl.Fl k).xs p τ) := Matrix.mul_one _
      exact (congrFun (congrFun hm a) c).symm
    exact (((Fl.Fl k).S_eq _ ((Fl.Fl k).xs_mem p)).2
      ⟨p, 1, ((T.U j T.σ₀).X k).Γ.one_mem, _, hb, hself⟩) a
  refine ⟨fun q => ⟨?_, fun i => ?_⟩, fun v => ?_⟩
  · rw [rdg_s_apply hR, hxs q]
    dsimp only
    rw [← Fl.h0]
    exact (Fl.Fl _).w0_ne _
  · rw [rdg_s_apply hR, hxs q]
    dsimp only
    have hs := Fl.hs (en q).1 (Fin.cast (A.dim (en q).1).symm i) ((Fl.Fl (en q).1).xs (en q).2)
    have hi : Fin.cast (A.dim (en q).1) (Fin.cast (A.dim (en q).1).symm i) = i := Fin.ext rfl
    rw [hi] at hs
    rw [← hs]
    exact hvan _ _ _
  ·
    have hF : ∀ k : (T.U j T.σ₀).Comp, ∃ F ∈ ((T.U j T.σ₀).X k).SSgt (A.Xa k).Fp 0,
        ∀ p, F ((Fl.Fl k).xs p) = v (en.symm ⟨k, p⟩) := by
      intro k
      obtain ⟨bb, m, h1, h2, h3⟩ := (A.mar k).1
      exact interpStatement_holds _ _ (A.Xa k) (Fl.Fl k)
        (GlobalTheory.ClosedDiscontinuity.propDisc_closed _ _)
        ⟨bb, m, h1, h2, fun x0 hx0 z hz ξ => by simpa using h3 0 (Set.mem_insert _ _) x0 hx0 z hz ξ⟩
        (A.mar k).2.2.1 (fun P hP => by simpa using (A.mar k).2.2.2.2 0 P (by simpa using hP)) _
    choose F hFmem hFval using hF
    have hO0 : RdOnto h j wF := by
      have h0 := hO 0
      rwa [addL_zero_pts] at h0
    have hf : ∀ k, F k ∈ ((T.U j T.σ₀).X k).SS (laR T j wF k) := by
      intro k
      rw [← A.hF k]
      exact (hFmem k).1
    refine ⟨_, mem_sp_of_rdOnto hR hO0 F hf, fun q => ?_⟩
    show F (e (xs q)).1 (e (xs q)).2.1 = v q
    rw [hxs q]
    exact (hFval _ _).trans (by simp)

end GlobalTheory.Shares
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointsInterpolationGenericSectionsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_interpolation_genericSections : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → (∀ q, R.s w t 0 (xs q) ≠ 0 ∧ ∀ i : Fin (WeightFamilies.dimY D j), R.s w t i.succ (xs q) = 0) ∧ ∀ v : Fin δ → ℂ, ∃ f ∈ R.sp wF Set.univ, ∀ q, f (xs q) = v q := by
  first | exact @GlobalTheory.Shares.points_and_interp | exact GlobalTheory.Shares.points_and_interp | (intros; apply GlobalTheory.Shares.points_and_interp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRulesLinearAndLevelCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRulesLinearAndLevelCongruence
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaRule

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn

attribute [local instance] Over.cartesianMonoidalCategory

section Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem monomial_degree_of_mem_harm {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {P : MvPolynomial (LtN Dw n) c.F}
    (hP : P ∈ harmA (Dw := Dw) c a n) {m : LtN Dw n →₀ ℕ} (hm : m ∈ P.support) :
    (m.sum fun _ e => e) = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i) := by
  have hrow := hP.1.2.2 m hm
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => hrow τ i

theorem totalDegree_of_mem_harm {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {P : MvPolynomial (LtN Dw n) c.F}
    (hP : P ∈ harmA (Dw := Dw) c a n) (h0 : P ≠ 0) :
    P.totalDegree = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i) := by
  obtain ⟨m0, hm0⟩ := Finset.nonempty_iff_ne_empty.2 (mt MvPolynomial.support_eq_empty.1 h0)
  unfold MvPolynomial.totalDegree
  refine le_antisymm (Finset.sup_le fun m hm => (monomial_degree_of_mem_harm hP hm).le) ?_
  rw [← monomial_degree_of_mem_harm hP hm0]
  exact Finset.le_sup (f := fun s : LtN Dw n →₀ ℕ => s.sum fun _ e => e) hm0

theorem thExpr_eq_sum_superset (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)))
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA (Dw := Dw) c a n) (U : Finset (LtN Dw n →₀ ℕ))
    (hU : P.support ⊆ U) :
    thExpr Xo c nab y P F = algebraMap c.F S (((l.M : c.F) ^ (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)))⁻¹) *
      ∑ m ∈ U, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((l.M : ℤ) ^ 2) (F b) (colOf m b) := by
  unfold thExpr
  rw [Finset.sum_subset hU (fun m _ hm => by rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, zero_mul])]
  by_cases h0 : P = 0
  · subst h0; simp
  · rw [totalDegree_of_mem_harm hP h0]

theorem thExpr_linear (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)))
    {N : ℕ} (cf : Fin N → c.F) (Q : Fin N → MvPolynomial (LtN Dw n) c.F) (hQ : ∀ i, Q i ∈ harmA (Dw := Dw) c a n)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA (Dw := Dw) c a n) (hsum : ∑ i, cf i • Q i = P) :
    thExpr Xo c nab y P F = ∑ i, algebraMap c.F S (cf i) * thExpr Xo c nab y (Q i) F := by
  classical
  set U := P.support ∪ Finset.univ.biUnion fun i => (Q i).support
  have hQU : ∀ i, (Q i).support ⊆ U := fun i =>
    (Finset.subset_biUnion_of_mem (fun i => (Q i).support) (Finset.mem_univ i)).trans Finset.subset_union_right
  rw [thExpr_eq_sum_superset nab y F hP U Finset.subset_union_left]
  simp only [fun i => thExpr_eq_sum_superset nab y F (hQ i) U (hQU i)]
  subst hsum
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

theorem thValAt_linear (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (x : Fin n → Dw.La)
    {N : ℕ} (cf : Fin N → c.F) (Q : Fin N → MvPolynomial (LtN Dw n) c.F) (hQ : ∀ i, Q i ∈ harmA (Dw := Dw) c a n)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA (Dw := Dw) c a n) (hsum : ∑ i, cf i • Q i = P)
    {S : Type} [CommRing S] [Algebra c.F S] (y0 : FrPt Xo c S) {v : S} (hv : ThValAt Xo c nab y0 x P v)
    (vi : Fin N → S) (hvi : ∀ i, ThValAt Xo c nab y0 x (Q i) (vi i)) :
    v = ∑ i, algebraMap c.F S (cf i) * vi i := by
  obtain ⟨S', _, _, φ, y', F, hff, hmap, hV, he⟩ := hv
  have hrefl : FrMap (AlgHom.id c.F S') y' y' :=
    (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S' S' (AlgHom.id c.F S') y').2.1
  have e1 : ∀ i, φ (vi i) = thExpr Xo c nab y' (Q i) F := fun i =>
    GlobalTheory.thetaValue_natural GlobalTheory.abelianSchemeLaws_all.1 hC E H Dw l Xo c nab hnab S S' φ y0 y' hmap a n x (Q i) (hQ i)
      _ _ (hvi i) ⟨S', inferInstance, inferInstance, AlgHom.id c.F S', y', F,
        RingHom.FaithfullyFlat.of_bijective Function.bijective_id, hrefl, hV, rfl⟩
  apply hff.injective
  show φ v = φ (∑ i, algebraMap c.F S (cf i) * vi i)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [he, thExpr_linear nab y' F cf Q hQ hP hsum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, AlgHom.commutes, e1 i]

theorem levPt_eq_of_sub_mem {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) {u u' : Dw.La}
    (h : u - u' ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) : levPt Xo x0 u = levPt Xo x0 u' := by
  have e : Xo.univ.eta u = Xo.univ.eta u' := by
    have h1 := Xo.univ.eta_add (u - u') u'
    rw [sub_add_cancel, Xo.univ.eta_ker _ h, _root_.one_mul] at h1
    exact h1
  unfold levPt
  rw [e]

end Lin

theorem isThRule_linear_and_congr : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ (x : Fin n → Dw.La) (m : ℕ) (cf : Fin m → c.F) (Q : Fin m → MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c) (g : Fin m → Rul Xo c), (∀ i, Q i ∈ harmA c a n) → (∑ i, cf i • Q i) ∈ harmA c a n → IsThRule Xo c nab x (∑ i, cf i • Q i) f → (∀ i, IsThRule Xo c nab x (Q i) (g i)) → f = ∑ i, cf i • g i) ∧ ∀ (x x' : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c), (∀ b, x b - x' b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → IsThRule Xo c nab x P f → IsThRule Xo c nab x' P f := by
  intro hC E _ _ _ H Dw l Xo c _ nab hnab a n
  refine ⟨fun x m cf Q f g hQ hP hf hg => ?_, fun x x' P f hx hf p y => ?_⟩
  · funext p y
    rw [thValAt_linear hC nab hnab x cf Q hQ hP rfl y (hf p y) (fun i => g i p y) (fun i => hg i p y)]
    rw [Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => (Algebra.smul_def (cf i) (g i p y)).symm
  · obtain ⟨S', _, _, φ, y', F, hff, hmap, hV, he⟩ := hf p y
    exact ⟨S', inferInstance, inferInstance, φ, y', F, hff, hmap,
      fun b => levPt_eq_of_sub_mem (Xo := Xo) y'.x (hx b) ▸ hV b, he⟩

end GlobalTheory.ThetaRule
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRulesLinearAndLevelCongruenceStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_rules_linear_and_level_congruence : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ (x : Fin n → Dw.La) (m : ℕ) (cf : Fin m → c.F) (Q : Fin m → MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c) (g : Fin m → Rul Xo c), (∀ i, Q i ∈ harmA c a n) → (∑ i, cf i • Q i) ∈ harmA c a n → IsThRule Xo c nab x (∑ i, cf i • Q i) f → (∀ i, IsThRule Xo c nab x (Q i) (g i)) → f = ∑ i, cf i • g i) ∧ ∀ (x x' : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c), (∀ b, x b - x' b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → IsThRule Xo c nab x P f → IsThRule Xo c nab x' P f := by
  first | exact @GlobalTheory.ThetaRule.isThRule_linear_and_congr | exact GlobalTheory.ThetaRule.isThRule_linear_and_congr | (intros; apply GlobalTheory.ThetaRule.isThRule_linear_and_congr <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueExistsUniqueOfChartIndependence
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem thExpr_tmul_lemma (hL : Laws) (hC : ChartIndepSt2) {E : Type} [Field E] [NumberField E]
    [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    [StarRing (𝓞 E)] {nab : NabV Xo c} (hnab : IsNab Xo c nab) {S : Type} [CommRing S]
    [Algebra c.F S] (y : FrPt Xo c S) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (x : Fin n → Dw.La)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n)
    {S1 : Type} [CommRing S1] [Algebra c.F S1] [Algebra S S1] (φ1 : S →ₐ[c.F] S1)
    (hφ1 : ∀ s, φ1 s = algebraMap S S1 s) (y1 : FrPt Xo c S1)
    (F1 : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y1.x)))
    (h1 : FrMap φ1 y y1)
    (hF1 : ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y1.s
      (levPt Xo y1.x (x b)) (F1 b))
    {S2 : Type} [CommRing S2] [Algebra c.F S2] [Algebra S S2] (φ2 : S →ₐ[c.F] S2)
    (hφ2 : ∀ s, φ2 s = algebraMap S S2 s) (y2 : FrPt Xo c S2)
    (F2 : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y2.x)))
    (h2 : FrMap φ2 y y2)
    (hF2 : ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y2.s
      (levPt Xo y2.x (x b)) (F2 b)) :
    TensorProduct.tmul S (thExpr Xo c nab y1 P F1) (1 : S2) =
      TensorProduct.tmul S (1 : S1) (thExpr Xo c nab y2 P F2) := by
  letI : Algebra c.F (TensorProduct S S1 S2) :=
    ((algebraMap S (TensorProduct S S1 S2)).comp (algebraMap c.F S)).toAlgebra
  let χ1 : S1 →ₐ[S] TensorProduct S S1 S2 := Algebra.TensorProduct.includeLeft
  let χ2 : S2 →ₐ[S] TensorProduct S S1 S2 := Algebra.TensorProduct.includeRight

  let ψ1 : S1 →ₐ[c.F] TensorProduct S S1 S2 :=
    { χ1.toRingHom with
      commutes' := fun r => by
        show χ1 (algebraMap c.F S1 r) = algebraMap S (TensorProduct S S1 S2) (algebraMap c.F S r)
        rw [← φ1.commutes r, hφ1]
        exact χ1.commutes _ }
  let ψ2 : S2 →ₐ[c.F] TensorProduct S S1 S2 :=
    { χ2.toRingHom with
      commutes' := fun r => by
        show χ2 (algebraMap c.F S2 r) = algebraMap S (TensorProduct S S1 S2) (algebraMap c.F S r)
        rw [← φ2.commutes r, hφ2]
        exact χ2.commutes _ }
  have hcomp : ψ1.comp φ1 = ψ2.comp φ2 := by
    ext s
    show χ1 (φ1 s) = χ2 (φ2 s)
    rw [hφ1, hφ2, χ1.commutes, χ2.commutes]
  exact GlobalTheory.T.thetaExpression_eq_of_witnesses hL hC E H Dw l Xo c nab hnab S y a n x P hP S1 φ1 y1 F1 S2 φ2 y2 F2 h1 hF1 h2 hF2
    (TensorProduct S S1 S2) ψ1 ψ2 hcomp

theorem thValTot_of_chartIndep : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ThValTot Xo c nab := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab S _ _ y a n x P hP

  obtain ⟨S', _, _, φ, y', F, hff, hy', hF⟩ := GlobalTheory.T.exists_faithfullyFlat_cover_level_sections hL E H Dw l Xo c S y n x
  letI : Algebra S S' := φ.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat S S' := hff
  have hφ : ∀ s, φ s = algebraMap S S' s := fun _ => rfl

  have htmul := thExpr_tmul_lemma hL hC hnab y x hP φ hφ y' F hy' hF φ hφ y' F hy' hF
  obtain ⟨v, hv⟩ := (Algebra.IsEffective.of_faithfullyFlat S S' (thExpr Xo c nab y' P F)).mp
    (by rw [Algebra.TensorProduct.includeLeftSubRight_apply, htmul, sub_self])
  refine ⟨v, ⟨S', inferInstance, inferInstance, φ, y', F, hff, hy', hF, hv⟩, ?_⟩

  rintro w ⟨S2, _, _, φ2, y2, F2, hff2, hy2, hF2, hw⟩
  letI : Algebra S S2 := φ2.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat S S2 := hff2
  have h12 := thExpr_tmul_lemma hL hC hnab y x hP φ hφ y' F hy' hF φ2 (fun _ => rfl) y2 F2 hy2 hF2
  have hv' : φ v = thExpr Xo c nab y' P F := hv
  rw [← hv', ← hw, hφ, Algebra.TensorProduct.tmul_one_eq_one_tmul] at h12
  have h3 : algebraMap S S2 v = algebraMap S S2 w :=
    Module.FaithfullyFlat.tensorProduct_mk_injective (A := S) (B := S') S2 h12
  exact (FaithfulSMul.algebraMap_injective S S2 h3).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLatticeQuotientHalfLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLatticeQuotientHalfLevel
set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn

namespace GlobalTheory


open scoped TensorProduct in
theorem natCard_quot_smul_top_of_projective {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card (R ⧸ I) ^ Module.finrank R N := by
  classical
  open scoped TensorProduct in
  have hA : Finite (Ideal (R ⧸ I)) :=
    Finite.of_injective (fun J : Ideal (R ⧸ I) => (J : Set (R ⧸ I))) SetLike.coe_injective
  have hMS : Finite (MaximalSpectrum (R ⧸ I)) :=
    Finite.of_injective (fun m : MaximalSpectrum (R ⧸ I) => m.asIdeal) (fun a b h => MaximalSpectrum.ext h)
  have rk : ∀ P : MaximalSpectrum (R ⧸ I), Module.finrank ((R ⧸ I) ⧸ P.1)
      (((R ⧸ I) ⧸ P.1) ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] N)) = Module.finrank R N := by
    intro P
    have hP := P.2
    let _ : Field ((R ⧸ I) ⧸ P.1) := Ideal.Quotient.field P.1
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.1) ((R ⧸ I) ⧸ P.1) N).finrank_eq]
    have h1 := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := (R ⧸ I) ⧸ P.1)
      (M := ((R ⧸ I) ⧸ P.1) ⊗[R] N)) ⟨⊥, Ideal.isPrime_bot⟩
    rw [Module.rankAtStalk_baseChange, Pi.natCast_apply, Nat.cast_id] at h1
    rw [← h1]
    generalize PrimeSpectrum.comap (algebraMap R ((R ⧸ I) ⧸ P.1)) ⟨⊥, Ideal.isPrime_bot⟩ = q
    obtain ⟨p, hp⟩ := q
    rw [← Ideal.finrank_fiber_eq_rankAtStalk, Ideal.finrank_fiber_eq_finrank]
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N)
    (Module.finrank R N) rk
  calc Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card ((R ⧸ I) ⊗[R] N) :=
        Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv.symm
    _ = Nat.card (Fin (Module.finrank R N) → R ⧸ I) := Nat.card_congr b.equivFun.toEquiv
    _ = Nat.card (R ⧸ I) ^ Module.finrank R N := by simp [Nat.card_fun]

theorem absNorm_level_half {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    Ideal.absNorm l.Mb = l.M ^ FD.fdeg E := by
  have h1 : Ideal.absNorm (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) = Ideal.absNorm l.Mb := by
    simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv l.Mb _ H.bar rfl).toEquiv.symm
  have h2 := congrArg Ideal.absNorm l.prod
  rw [map_mul, h1, Ideal.absNorm_span_singleton] at h2
  have h3 : (Algebra.norm ℤ ((l.M : ℕ) : 𝓞 E)).natAbs = l.M ^ Module.finrank ℚ E := by
    have : ((l.M : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (l.M : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  have hev : Module.finrank ℚ E = 2 * FD.fdeg E := by
    have h := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h
    unfold FD.fdeg
    omega
  rw [h3, hev, pow_mul', ← sq] at h2
  exact Nat.pow_left_injective two_ne_zero h2

theorem card_levQ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H),
    Finite (LevQ Dw l) ∧ Nat.card (LevQ Dw l) = l.M ^ (FD.fdeg E * (Dw.p + Dw.q)) := by
  intro E _ _ _ H Dw l
  unfold LevQ
  have := Dw.fin
  have := Dw.proj
  have hN := absNorm_level_half l
  have : Finite (𝓞 E ⧸ l.Mb) := by
    rw [← Ideal.absNorm_ne_zero_iff, hN]
    exact pow_ne_zero _ (by have := l.three_le; omega)
  have hc := natCard_quot_smul_top_of_projective (N := Dw.La) l.Mb
  have hq : Nat.card (𝓞 E ⧸ l.Mb) = l.M ^ FD.fdeg E := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Dw.rank, hq, ← pow_mul] at hc
  refine ⟨?_, hc⟩
  apply Nat.finite_of_card_ne_zero
  rw [hc]
  exact pow_ne_zero _ (by have := l.three_le; omega)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLatticeQuotientHalfLevelStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_lattice_quotient_half_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H), Finite (LevQ Dw l) ∧ Nat.card (LevQ Dw l) = l.M ^ (FD.fdeg E * (Dw.p + Dw.q)) := by
  first | exact @GlobalTheory.card_levQ | exact GlobalTheory.card_levQ | (intros; apply GlobalTheory.card_levQ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueNaturalAlgebraMap
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueNaturalAlgebraMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem thetaValue_natural : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ v0 w, ThValAt Xo c nab y0 x P v0 → ThValAt Xo c nab y x P w → φ v0 = w := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab S T _ _ _ _ φ y0 y hφ a n x P hP v0 w h0 h1
  obtain ⟨S', _, _, φ0, y0', F0, hff0, hm0, hv0, he0⟩ := h0
  obtain ⟨T', _, _, φ1, y1, F1, hff1, hm1, hv1, he1⟩ := h1

  have hm01 : FrMap (φ1.comp φ) y0 y1 := GlobalTheory.FramedBaseChange.trans φ φ1 hφ hm1

  let iS : Algebra S S' := φ0.toRingHom.toAlgebra
  let iT : Algebra S T' := (φ1.comp φ).toRingHom.toAlgebra
  have : Module.FaithfullyFlat S S' := hff0
  let iU : Algebra c.F (TensorProduct S T' S') :=
    ((algebraMap T' (TensorProduct S T' S')).comp (algebraMap c.F T')).toAlgebra
  have hsq : ∀ s : S, (1 : T') ⊗ₜ[S] φ0 s = (φ1 (φ s)) ⊗ₜ[S] (1 : S') := by
    intro s
    calc (1 : T') ⊗ₜ[S] φ0 s = (1 : T') ⊗ₜ[S] (s • (1 : S')) := by
          rw [← Algebra.algebraMap_eq_smul_one]; rfl
      _ = (s • (1 : T')) ⊗ₜ[S] (1 : S') := (TensorProduct.smul_tmul _ _ _).symm
      _ = (φ1 (φ s)) ⊗ₜ[S] (1 : S') := by
          rw [← Algebra.algebraMap_eq_smul_one]; rfl
  let ψ2 : T' →ₐ[c.F] TensorProduct S T' S' :=
    { algebraMap T' (TensorProduct S T' S') with commutes' := fun _ => rfl }
  let ψ1 : S' →ₐ[c.F] TensorProduct S T' S' :=
    { (Algebra.TensorProduct.includeRight : S' →ₐ[S] TensorProduct S T' S').toRingHom with
      commutes' := fun r => by
        show (1 : T') ⊗ₜ[S] algebraMap c.F S' r = algebraMap T' (TensorProduct S T' S') (algebraMap c.F T' r)
        rw [← φ0.commutes r, hsq, φ.commutes, φ1.commutes]
        rfl }
  have hcomp : ψ1.comp φ0 = ψ2.comp (φ1.comp φ) := by
    ext s
    exact hsq s
  have key := GlobalTheory.T.thetaExpression_eq_of_witnesses hL hC E H Dw l Xo c nab hnab S y0 a n x P hP S' φ0 y0' F0 T' (φ1.comp φ)
    y1 F1 hm0 hv0 hm01 hv1 (TensorProduct S T' S') ψ1 ψ2 hcomp
  rw [← he0, ← he1] at key
  have hv : ψ1 (φ0 v0) = ψ2 (φ1 (φ v0)) := congrArg (fun f => f v0) hcomp
  have hinj : Function.Injective (algebraMap T' (TensorProduct S T' S')) :=
    FaithfulSMul.algebraMap_injective T' (TensorProduct S T' S')
  exact hff1.injective (hinj (hv.symm.trans key))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueNaturalAlgebraMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaValue_natural_algebraMap : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ v0 w, ThValAt Xo c nab y0 x P v0 → ThValAt Xo c nab y x P w → φ v0 = w := by
  first | exact @GlobalTheory.thetaValue_natural | exact GlobalTheory.thetaValue_natural | (intros; apply GlobalTheory.thetaValue_natural <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNormalisedIsoReadingOneAnalyticFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNormalisedIsoReadingOneAnalyticFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal.PrimRd

theorem finset_fin_two_eq_cases (I : Finset (Fin 2)) : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by
  revert I
  decide

theorem e_psum {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) (w : A ⟶ A) (z z' : Fin g → ℂ) (h : Φ.e z' = Φ.e z ≫ w) (I : ULift.{0} (Finset (Fin 2))) :
    Φ.e z ≫ psum A ![𝟙 A, w] I.down = Φ.e (psumL 2 g I ![z, z']) := by
  obtain ⟨I⟩ := I
  have h0 : Φ.e 0 = 1 := (Φ.e_ker 0).2 (zero_mem _)
  rcases finset_fin_two_eq_cases I with rfl | rfl | rfl | rfl
  · show Φ.e z ≫ (toUnit A ≫ η) = _
    simp [psumL, h0]
    rfl
  · show Φ.e z ≫ (lift (𝟙 A) (toUnit A ≫ η) ≫ μ) = _
    simp [psumL]
  · show Φ.e z ≫ (lift w (toUnit A ≫ η) ≫ μ) = _
    simp [psumL]
    exact h.symm
  · show Φ.e z ≫ (lift (𝟙 A) (lift w (toUnit A ≫ η) ≫ μ) ≫ μ) = _
    simp [psumL, Φ.e_add, h]
    rw [← Category.assoc, comp_lift, Category.comp_id]
    rfl

theorem sum_ulift_finset_fin_two_expand {M : Type} [AddCommMonoid M] (f : ULift.{0} (Finset (Fin 2)) → M) :
    ∑ I, f I = f ⟨∅⟩ + f ⟨{0}⟩ + f ⟨{1}⟩ + f ⟨{0, 1}⟩ := by
  rw [Fintype.sum_equiv Equiv.ulift f (fun x => f ⟨x⟩) (fun _ => rfl)]
  have hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [add_assoc]

theorem sameSum_of_const {X Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (f : Y ⟶ X) (h : ∀ k, φ k = f) (h' : ∀ k, φ' k = f)
    (hs : ∑ k, ε k = ∑ k, ε' k) : LB.SameSum φ ε φ' ε' := by
  intro ψ
  by_cases hψ : f = ψ
  · subst hψ
    simpa [h, h'] using hs
  · simp [h, h', hψ]

private theorem w0_add_bar_w0_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := by
  have hrt : H.bar H.rt = -H.rt := by
    apply RingOfIntegers.ext
    rw [H.bar_eq]
    push_cast
    set r : E := (H.rt : E) with hr
    have hr2 : r ^ 2 = -(H.d : E) := by
      have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
      simpa [hr] using this
    have hc2 : (IsCMField.complexConj E r) ^ 2 = r ^ 2 := by
      rw [← map_pow, hr2]
      simp
    have hprod : (IsCMField.complexConj E r - r) * (IsCMField.complexConj E r + r) = 0 := by
      linear_combination hc2
    rcases mul_eq_zero.1 hprod with h1 | h1
    · exfalso
      have heq : IsCMField.complexConj E r = r := sub_eq_zero.1 h1
      let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
      have h3 := IsCMField.complexEmbedding_complexConj E τ r
      rw [heq] at h3
      have him : (τ r).im = 0 := by
        have := congrArg Complex.im h3
        simp at this
        linarith
      have h4 : (τ r) ^ 2 = -(H.d : ℂ) := by
        rw [← map_pow, hr2]
        simp
      have h5 : τ r = ((τ r).re : ℂ) := Complex.ext (by simp) (by simp [him])
      rw [h5] at h4
      have h6 : (τ r).re ^ 2 = -(H.d : ℝ) := by exact_mod_cast h4
      have h7 : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
      nlinarith [sq_nonneg (τ r).re]
    · exact eq_neg_of_add_eq_zero_left h1
  have hb : H.bar (2 * H.w0) = H.bar (1 + H.rt) := by rw [H.two_weight_eq_one_add_root]
  rw [map_mul, map_add (f := _), map_one, hrt, map_ofNat] at hb
  have h2 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    linear_combination H.two_weight_eq_one_add_root + hb
  exact mul_left_cancel₀ two_ne_zero h2

private theorem hf_eq_cj_hf_swap_of_isHerm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (T Tb : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hadj : ∀ z w, hermForm Hm (T z) w = hermForm Hm z (Tb w)) (hTT : ∀ w, T w + Tb w = w) (z w : Fin g → ℂ) :
    ∑ k : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)), (((Sum.elim (fun _ => (1 : ℤ)) fun I => -cε 2 I) k : ℤ) : ℂ) *
      hermForm Hm ((Sum.elim (fun _ => LinearMap.id) (fun I => (psumL 2 g I).comp (LinearMap.pi ![LinearMap.id, T])) :
        (Fin 1 ⊕ ULift.{0} (Finset (Fin 2))) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) k z)
        ((Sum.elim (fun _ => LinearMap.id) (fun I => (psumL 2 g I).comp (LinearMap.pi ![LinearMap.id, T])) :
        (Fin 1 ⊕ ULift.{0} (Finset (Fin 2))) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) k w) = 0 := by
  have hB1 : ∀ a b c, hermForm Hm (a + b) c = hermForm Hm a c + hermForm Hm b c := by
    intro a b c
    simp [hermForm, add_dotProduct]
  have hB2 : ∀ a b c, hermForm Hm a (b + c) = hermForm Hm a b + hermForm Hm a c := by
    intro a b c
    simp [hermForm, Matrix.mulVec_add, dotProduct_add]
  have hB0 : ∀ a, hermForm Hm 0 a = 0 := by intro a; simp [hermForm]
  rw [Fintype.sum_sum_type, sum_ulift_finset_fin_two_expand, Fin.sum_univ_one]
  simp [psumL, cε, hB1, hB2, hB0]
  have k3 : hermForm Hm z w = hermForm Hm z (T w) + hermForm Hm z (Tb w) := by rw [← hB2, hTT]
  rw [hadj z w]
  linear_combination k3

theorem prim_reading : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), (∃ wP : PrimTy H Xo, IsPrim wP) ∧ ∀ wP : PrimTy H Xo, IsPrim wP → ∀ z : Fin g → ℂ, Φ.toAnFr.GenRd _ _ wP (Φ.e z).left (Sum.elim (fun _ => z) (fun I => psumL 2 g I ![z, tyAct ty H.w0 z])) 1 := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ
  have hw0 : IsMonHom (Xo.univ.t.act.act H.w0) := Xo.univ.t.act.hom H.w0
  have hη : η ≫ Xo.univ.t.act.act H.w0 = η := IsMonHom.one_hom _
  refine ⟨Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.exists_wP Xo.univ.t, ?_⟩
  intro wP hP z
  obtain ⟨hPg, hPc⟩ := hP
  let Λ : (Fin 1 ⊕ ULift.{0} (Finset (Fin 2))) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    Sum.elim (fun _ => LinearMap.id)
      (fun I => (psumL 2 g I).comp (LinearMap.pi ![LinearMap.id, tyAct ty H.w0]))
  have hΛl : ∀ k z, Λ (Sum.inl k) z = z := fun _ _ => rfl
  have hΛr : ∀ I z, Λ (Sum.inr I) z = psumL 2 g I ![z, tyAct ty H.w0 z] := by
    intro I z
    simp only [Λ, Sum.elim_inr, LinearMap.comp_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hlin : ∀ z, Φ.e (tyAct ty H.w0 z) = Φ.e z ≫ Xo.univ.t.act.act H.w0 := Φ.lin H.w0
  have h0 : Φ.e 0 = 1 := (Φ.e_ker 0).2 (zero_mem _)
  have hφ : ∀ z k, (Φ.e z).left ≫
      (Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0])) k =
      (Φ.e (Λ k z)).left := by
    intro z k
    rcases k with k | I
    · simp [hΛl]
    · have := e_psum Φ.toAnFr (Xo.univ.t.act.act H.w0) z (tyAct ty H.w0 z) (hlin z) I
      rw [hΛr, ← this]
      rfl
  have hT : ∀ gm ∈ Φ.lat, tyAct ty H.w0 gm ∈ Φ.lat := by
    intro gm hgm
    apply (Φ.e_ker _).1
    rw [hlin, (Φ.e_ker gm).2 hgm]
    show (toUnit _ ≫ η) ≫ _ = toUnit _ ≫ η
    rw [Category.assoc, hη]
  have p0 : ∀ a b : Fin g → ℂ, psumL 2 g ⟨∅⟩ ![a, b] = 0 := by intro a b; simp [psumL]
  have p1 : ∀ a b : Fin g → ℂ, psumL 2 g ⟨{0}⟩ ![a, b] = a := by intro a b; simp [psumL]
  have p2 : ∀ a b : Fin g → ℂ, psumL 2 g ⟨{1}⟩ ![a, b] = b := by intro a b; simp [psumL]
  have p3 : ∀ a b : Fin g → ℂ, psumL 2 g ⟨{0, 1}⟩ ![a, b] = a + b := by intro a b; simp [psumL]
  have hper : ∀ gm ∈ Φ.lat, (∀ z, (Φ.e (z + gm)).left = (Φ.e z).left) ∧ ∀ k, Λ k gm ∈ Φ.lat := by
    intro gm hgm
    refine ⟨fun z => by rw [Φ.e_add, (Φ.e_ker gm).2 hgm, _root_.mul_one], fun k => ?_⟩
    rcases k with k | I
    · exact hgm
    · rw [hΛr]
      obtain ⟨I⟩ := I
      rcases finset_fin_two_eq_cases I with rfl | rfl | rfl | rfl
      · rw [p0]
        exact zero_mem _
      · rw [p1]
        exact hgm
      · rw [p2]
        exact hT gm hgm
      · rw [p3]
        exact add_mem hgm (hT gm hgm)
  have hbar := w0_add_bar_w0_eq_one H
  have hTT : ∀ w, tyAct ty H.w0 w + tyAct ty (H.bar H.w0) w = w := by
    intro w
    funext k
    have h1 : ((H.w0 : E) + (H.bar H.w0 : E)) = 1 := by
      exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) hbar
    simp only [tyAct, Pi.add_apply, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
    rw [← add_mul, ← map_add (f := _), h1, map_one, _root_.one_mul]
  have hherm : ∀ z w, ∑ k, (((Sum.elim (fun _ => (1 : ℤ)) fun I => -cε 2 I) k : ℤ) : ℂ) *
      hermForm Φ.Hm (Λ k z) (Λ k w) = 0 :=
    fun z w => hf_eq_cj_hf_swap_of_isHerm Φ.Hm (tyAct ty H.w0) (tyAct ty (H.bar H.w0)) (Φ.adj H.w0) hTT z w
  obtain ⟨⟨v, hv0, hv⟩, -⟩ := GlobalTheory.T.abelianHolomorphicFrame_reading_const_of_forms_cancel _ _ _ _ g Φ.toAnFr _ _
    (Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0]))
    (Sum.elim (fun _ => 1) fun I => -cε 2 I) wP hPg g (fun z => (Φ.e z).left) Λ Φ.lat Φ.hol hφ Φ.span hper hherm
  have heS : ∀ k : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)), eSec Xo.univ.t.G ≫
      (Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0])) k =
      eSec Xo.univ.t.G := by
    intro k
    rcases k with k | I
    · simp
    · obtain ⟨I⟩ := I
      show (η ≫ psum Xo.univ.t.G ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0] I).left = (η : _ ⟶ Xo.univ.t.G).left
      congr 1
      rcases finset_fin_two_eq_cases I with rfl | rfl | rfl | rfl
      · show η ≫ (toUnit _ ≫ η) = η
        simp
      · show η ≫ (lift (𝟙 _) (toUnit _ ≫ η) ≫ μ) = η
        simp
      · show η ≫ (lift (Xo.univ.t.act.act H.w0) (toUnit _ ≫ η) ≫ μ) = η
        simp [hη]
      · show η ≫ (lift (𝟙 _) (lift (Xo.univ.t.act.act H.w0) (toUnit _ ≫ η) ≫ μ) ≫ μ) = η
        simp
  have hv1 : v = 1 := by
    have A0 := hv 0
    have hz : ∀ k, Λ k 0 = 0 := fun k => map_zero _
    have hq0 : (Φ.e 0).left = y.x ≫ eSec Xo.univ.t.G := by
      rw [h0]
      rfl
    simp only [hz, hq0] at A0
    have A2 := ((GlobalTheory.T.generatorReading_pullback_period_rigid _ _ _ _ g Φ.toAnFr _ _ _ _ wP).1 _ (eSec Xo.univ.t.G) y.x _ v).2 A0
    have A3 : Φ.toAnFr.GenRd (fun _ : PUnit => eSec Xo.univ.t.G) (fun _ => 1) Xo.univ.t.PP.rig y.x (fun _ => 0) 1 := by
      obtain ⟨b1, b2⟩ := (GlobalTheory.T.generatorReading_pullback_period_rigid _ _ _ _ g Φ.toAnFr _ _
        (Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0]))
        (Sum.elim (fun _ => 1) fun I => -cε 2 I) wP).2.2 1
      refine ⟨b1, fun j hj => ?_⟩
      have b3 := b2 j hj
      simpa [rigPow] using b3
    have hsame : LB.SameSum (fun k : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)) => eSec Xo.univ.t.G ≫
        (Sum.elim (fun _ => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0])) k)
        (Sum.elim (fun _ => 1) fun I => -cε 2 I) (fun _ : PUnit => eSec Xo.univ.t.G) (fun _ => 1) := by
      refine sameSum_of_const (eSec Xo.univ.t.G) heS (fun _ => rfl) ?_
      rw [Fintype.sum_sum_type, sum_ulift_finset_fin_two_expand, Fin.sum_univ_one]
      simp [cε]
    exact (GlobalTheory.T.generatorReading_corr_mul_inv _ _ _ _ g Φ.toAnFr _ _ _ _ _ _ _ _ _ y.x _ _ v 1 A2 A3).2.1 hPc hsame
      ⟨fun _ => 0, fun _ => rfl, fun _ => rfl⟩
  have hfin := hv z
  rw [hv1] at hfin
  have hpt : (fun k => Λ k z) = Sum.elim (fun _ => z) (fun I => psumL 2 g I ![z, tyAct ty H.w0 z]) := by
    funext k
    rcases k with k | I
    · rfl
    · exact hΛr I z
  rw [hpt] at hfin
  exact hfin

end GlobalTheory.AnVal.PrimRd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNormalisedIsoReadingOneAnalyticFrameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisedIso_reading_one_analyticFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), (∃ wP : PrimTy H Xo, IsPrim wP) ∧ ∀ wP : PrimTy H Xo, IsPrim wP → ∀ z : Fin g → ℂ, Φ.toAnFr.GenRd _ _ wP (Φ.e z).left (Sum.elim (fun _ => z) (fun I => psumL 2 g I ![z, tyAct ty H.w0 z])) 1 := by
  first | exact @GlobalTheory.AnVal.PrimRd.prim_reading | exact GlobalTheory.AnVal.PrimRd.prim_reading | (intros; apply GlobalTheory.AnVal.PrimRd.prim_reading <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LevelFourierTransformAutAndHomogeneous
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LevelFourierTransformAutAndHomogeneous
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

namespace GlobalTheory.GalTw

section

open GlobalTheory.LevelPairing

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem exists_zetaM_pow (c : Coeff l) (ta : c.F ≃+* c.F) :
    ∃ a a' : ℕ, ta (zetaM c) = zetaM c ^ a ∧ a * a' ≡ 1 [MOD l.M] := by
  have h3 := l.three_le
  haveI : NeZero l.M := ⟨by omega⟩
  have hp := zetaM_prim c
  have hp' : IsPrimitiveRoot (ta (zetaM c)) l.M := hp.map_of_injective ta.injective
  obtain ⟨a, -, ha⟩ := hp.eq_pow_of_pow_eq_one hp'.pow_eq_one
  have hco : a.Coprime l.M := (hp.pow_iff_coprime (by omega) a).1 (ha ▸ hp')
  obtain ⟨a', -, h⟩ := Nat.exists_mul_mod_eq_one_of_coprime hco (by omega)
  refine ⟨a, a', ha.symm, ?_⟩
  unfold Nat.ModEq
  rw [h, Nat.mod_eq_of_lt (by omega)]

theorem mk_qRep {K : Submodule (𝓞 E) Dw.La} (x : Dw.La ⧸ K) : (Submodule.Quotient.mk (qRep x) : Dw.La ⧸ K) = x :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective _ x)

theorem level_nsmul (x : LevQc Dw l) : l.M • x = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h : (l.M : 𝓞 E) ∈ l.Mb * Mfr l := by
    rw [Mfr, l.prod]; exact Ideal.mem_span_singleton_self _
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul (Submodule.mem_inf.1 (Ideal.mul_le_inf h)).2 Submodule.mem_top

theorem nsmul_nsmul_of_modEq {n a a' : ℕ} (h : a * a' ≡ 1 [MOD l.M]) (x : Fin n → LevQc Dw l) :
    a • a' • x = x := by
  have h3 := l.three_le
  have hM : l.M • x = 0 := funext fun b => level_nsmul (x b)
  have e : a * a' = l.M * (a * a' / l.M) + 1 := by
    have := Nat.div_add_mod (a * a') l.M
    rw [h, Nat.mod_eq_of_lt (show 1 < l.M by omega)] at this
    exact this.symm
  rw [← mul_smul, e, add_smul, one_smul, mul_comm, mul_smul, hM, smul_zero, zero_add]

theorem pairL_nsmul {n : ℕ} (a : ℕ) (x : Fin n → LevQc Dw l) (y : Fin n → Dw.La) :
    (l.M : ℤ) ∣ (a : ℤ) * pairL (l := l) (fun b => qRep (x b)) y -
      pairL (l := l) (fun b => qRep ((a • x) b)) y := by
  have e : (a : ℤ) * pairL (l := l) (fun b => qRep (x b)) y = pairL (l := l) (fun b => a • qRep (x b)) y := by
    unfold pairL
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  rw [e]
  refine pairL_congr _ _ _ _ (fun b => ?_) (fun b => by simp)
  rw [← Submodule.Quotient.eq, mk_qRep, ← Nat.cast_smul_eq_nsmul (𝓞 E), Submodule.Quotient.mk_smul, mk_qRep,
    Nat.cast_smul_eq_nsmul]
  rfl

theorem map_phiHat (c : Coeff l) {n : ℕ} (ta : c.F ≃+* c.F) {a a' : ℕ} (ha : ta (zetaM c) = zetaM c ^ a)
    (h : a * a' ≡ 1 [MOD l.M]) (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l) :
    ta (phiHat c φ q) = phiHat c (fun x => ta (φ (a' • x))) q := by
  have h' : a' * a ≡ 1 [MOD l.M] := mul_comm a a' ▸ h
  let e : (Fin n → LevQc Dw l) ≃ (Fin n → LevQc Dw l) :=
    ⟨fun x => a • x, fun x => a' • x, nsmul_nsmul_of_modEq h', nsmul_nsmul_of_modEq h⟩
  unfold phiHat
  refine (ta.toAddEquiv.map_finsum _).trans (Eq.trans (finsum_congr fun x => ?_) (finsum_comp_equiv e))
  change ta _ = ta (φ (a' • a • x)) * zetaM c ^ pairL (l := l) (fun b => qRep ((a • x) b)) _
  rw [nsmul_nsmul_of_modEq h', map_mul, map_zpow₀, ha, ← zpow_natCast, ← zpow_mul,
    zpow_congr c (pairL_nsmul a x _)]

theorem phiHat_mul (c : Coeff l) {n : ℕ} (u : c.F) (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l) :
    phiHat c (fun x => u * φ x) q = u * phiHat c φ q := by
  unfold phiHat
  rw [← smul_eq_mul u, smul_finsum]
  refine finsum_congr fun x => ?_
  rw [smul_eq_mul, mul_assoc]

theorem shortValAt_mul {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (nab : NabV Xo c)
    (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (b u : c.F) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) (h : ShortValAt Xo c nab w Λ b N P y v) :
    ShortValAt Xo c nab (fun q => u * w q) Λ b N P y (algebraMap c.F S u * v) := by
  obtain ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, ?_⟩
  rw [map_mul, h7, AlgHom.commutes, mul_left_comm]
  congr 1
  rw [← Algebra.smul_def, smul_finsum]
  refine finsum_congr fun q => ?_
  rw [Algebra.smul_def, map_mul, mul_assoc]

end

theorem phiHat_aut_and_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ), (∀ ta : c.F ≃+* c.F, (∃ a a' : ℕ, ta (zetaM c) = zetaM c ^ a ∧ a * a' ≡ 1 [MOD l.M]) ∧ ∀ a a' : ℕ, ta (zetaM c) = zetaM c ^ a → a * a' ≡ 1 [MOD l.M] → ∀ (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l), ta (phiHat c φ q) = phiHat c (fun x => ta (φ (a' • x))) q) ∧ (∀ (u : c.F) (φ : (Fin n → LevQc Dw l) → c.F) q, phiHat c (fun x => u * φ x) q = u * phiHat c φ q) ∧ ∀ (nab : NabV Xo c) (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (b u : c.F) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S), ShortValAt Xo c nab w Λ b N P y v → ShortValAt Xo c nab (fun q => u * w q) Λ b N P y (algebraMap c.F S u * v) := by
  intro E _ _ _ H Dw l Xo c n
  exact ⟨fun ta => ⟨exists_zetaM_pow c ta, fun _ _ ha h φ q => map_phiHat c ta ha h φ q⟩,
    fun u φ q => phiHat_mul c u φ q,
    fun nab w Λ b u N P S _ _ y v h => shortValAt_mul nab w Λ b u N P S y v h⟩

end GlobalTheory.GalTw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LevelFourierTransformAutAndHomogeneousStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_fourier_transform_aut_and_homogeneous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ), (∀ ta : c.F ≃+* c.F, (∃ a a' : ℕ, ta (zetaM c) = zetaM c ^ a ∧ a * a' ≡ 1 [MOD l.M]) ∧ ∀ a a' : ℕ, ta (zetaM c) = zetaM c ^ a → a * a' ≡ 1 [MOD l.M] → ∀ (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l), ta (phiHat c φ q) = phiHat c (fun x => ta (φ (a' • x))) q) ∧ (∀ (u : c.F) (φ : (Fin n → LevQc Dw l) → c.F) q, phiHat c (fun x => u * φ x) q = u * phiHat c φ q) ∧ ∀ (nab : NabV Xo c) (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (b u : c.F) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S), ShortValAt Xo c nab w Λ b N P y v → ShortValAt Xo c nab (fun q => u * w q) Λ b N P y (algebraMap c.F S u * v) := by
  first | exact @GlobalTheory.GalTw.phiHat_aut_and_mul | exact GlobalTheory.GalTw.phiHat_aut_and_mul | (intros; apply GlobalTheory.GalTw.phiHat_aut_and_mul <;> assumption)
end
end

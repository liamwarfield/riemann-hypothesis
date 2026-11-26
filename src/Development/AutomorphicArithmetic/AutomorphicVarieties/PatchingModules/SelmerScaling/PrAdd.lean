module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkInd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GGram

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PrAdd
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.prAdd :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), (∀ a, algebraMap S.Bh S.U.AA (S.pr0 a) + (S.pr1 a : S.U.AA) = a) ∧ (∀ (b : S.Bh) (y : S.U.N), S.pr0 (algebraMap S.Bh S.U.AA b + y) = b ∧ S.pr1 (algebraMap S.Bh S.U.AA b + y) = y) ∧ (∀ a a', S.pr0 (a + a') = S.pr0 a + S.pr0 a' ∧ S.pr1 (a + a') = S.pr1 a + S.pr1 a') ∧ (∀ (b : S.Bh) a, S.pr0 (b • a) = b * S.pr0 a ∧ S.pr1 (b • a) = b • S.pr1 a) ∧ (∀ a a', S.pr0 (a * a') - S.pr0 a * S.pr0 a' ∈ ired S.U.N ∧ S.pr1 (a * a') = S.pr0 a • S.pr1 a' + S.pr0 a' • S.pr1 a) ∧ ired S.U.N ≤ maximalIdeal S.Bh ∧ S.J2 ≤ maximalIdeal S.Bh := by
  intro l _ S
  have h1 : ∀ a, algebraMap S.Bh S.U.AA (S.pr0 a) + (S.pr1 a : S.U.AA) = a := by
    intro a
    simp [Ctx.pr1]
  have h2 : ∀ (b : S.Bh) (y : S.U.N), S.pr0 (algebraMap S.Bh S.U.AA b + y) = b ∧
      S.pr1 (algebraMap S.Bh S.U.AA b + y) = y := by
    intro b y
    have e := h1 (algebraMap S.Bh S.U.AA b + y)
    have hm : algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b + y) - b) ∈ S.U.N := by
      have : algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b + y) - b) =
          (y : S.U.AA) - (S.pr1 (algebraMap S.Bh S.U.AA b + y) : S.U.AA) := by
        rw [map_sub]; linear_combination e
      rw [this]
      exact S.U.N.sub_mem y.2 (S.pr1 _).2
    have hz : algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b + y) - b) = 0 :=
      Submodule.disjoint_def.1 S.U.compl.disjoint _ (Submodule.mem_one.2 ⟨_, rfl⟩) hm
    have hb : S.pr0 (algebraMap S.Bh S.U.AA b + y) = b :=
      sub_eq_zero.1 (S.U.inj (by rw [hz, map_zero]))
    refine ⟨hb, Subtype.ext ?_⟩
    rw [hb] at e
    exact add_left_cancel e
  have key : ∀ (a : S.U.AA) (b : S.Bh) (y : S.U.N), a = algebraMap S.Bh S.U.AA b + y →
      S.pr0 a = b ∧ S.pr1 a = y := by
    rintro a b y rfl
    exact h2 b y
  have hi : ired S.U.N ≤ maximalIdeal S.Bh := by
    refine Ideal.span_le.2 ?_
    rintro b ⟨x, hx, y, hy, e⟩
    obtain ⟨c, hc, e'⟩ := S.U.mul_mem x hx y hy
    have : b = c := S.U.inj (e.symm.trans e')
    rw [this]; exact hc
  refine ⟨h1, h2, fun a a' => key _ _ _ ?_, fun b a => key _ _ _ ?_, fun a a' => ?_, hi, ?_⟩
  · rw [map_add (f := _), Submodule.coe_add]
    linear_combination - h1 a - h1 a'
  · rw [map_mul, Submodule.coe_smul, Algebra.smul_def, Algebra.smul_def, ← mul_add, h1]
  · obtain ⟨c, -, e⟩ := S.U.mul_mem _ (S.pr1 a).2 _ (S.pr1 a').2
    have := key (a * a') (S.pr0 a * S.pr0 a' + c) (S.pr0 a • S.pr1 a' + S.pr0 a' • S.pr1 a) (by
      rw [map_add (f := _), map_mul, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, Algebra.smul_def,
        Algebra.smul_def, ← e]
      have e1 := h1 a
      have e2 := h1 a'
      linear_combination (- a') * e1 - (algebraMap S.Bh S.U.AA (S.pr0 a) + (S.pr1 a : S.U.AA)) * e2)
    refine ⟨?_, this.2⟩
    rw [this.1, add_sub_cancel_left]
    exact Ideal.subset_span ⟨_, (S.pr1 a).2, _, (S.pr1 a').2, e⟩
  · refine sup_le (sup_le ?_ (Ideal.pow_le_self two_ne_zero)) hi
    exact ((IsLocalRing.local_hom_tfae (algebraMap S.OO S.Bh)).out 1 3).1 (IsCO.isLocalHom (O := S.OO) (R := S.Bh))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.BndOps
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section SlopeTestRemainingChoices
variable {A Fr G : Type} [CommRing A] [CommRing Fr] [Algebra A Fr] [TopologicalSpace G] {I : Ideal A} {t : A}

private theorem ac_const (c : A) : AdicCont I fun _ : G => c := fun _ => IsLocallyConstant.const _

end SlopeTestRemainingChoices

private theorem adicCont_add_and_adicCont_mul {R G : Type} [CommRing R] [TopologicalSpace G] {I : Ideal R} {φ ψ : G → R}
    (hφ : AdicCont I φ) (hψ : AdicCont I ψ) :
    AdicCont I (fun g => φ g + ψ g) ∧ AdicCont I (fun g => φ g * ψ g) := by
  unfold AdicCont at *
  constructor
  · intro N
    simpa [map_add (f := _)] using (hφ N).comp₂ (hψ N) (· + ·)
  · intro N
    simpa [map_mul] using (hφ N).comp₂ (hψ N) (· * ·)

private theorem adicCont_neg_of_adicCont {R G : Type} [CommRing R] [TopologicalSpace G] {I : Ideal R} {φ : G → R}
    (hφ : AdicCont I φ) : AdicCont I (fun g => -φ g) := by
  unfold AdicCont at *
  intro N
  simpa [map_neg, Function.comp_def] using (hφ N).comp (fun y => -y)

private theorem adicCont_comp_inv_of_isTopologicalGroup {R G : Type} [CommRing R] [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {I : Ideal R} {φ : G → R} (hφ : AdicCont I φ) : AdicCont I (fun g => φ g⁻¹) := by
  unfold AdicCont at *
  intro N
  exact (hφ N).comp_continuous continuous_inv

theorem UpperTheory.V.Pa.bndOps :
    ∀ (K G : Type) [Field K] [TopologicalSpace G] [Group G] [IsTopologicalGroup G], (∀ c : FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) fun _ : G => c) ∧ (∀ φ ψ : G → FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) φ → BndF (PowerSeries.X : PowerSeries K) ψ → (BndF (PowerSeries.X : PowerSeries K) fun g => φ g + ψ g) ∧ (BndF (PowerSeries.X : PowerSeries K) fun g => φ g * ψ g) ∧ (BndF (PowerSeries.X : PowerSeries K) fun g => -φ g) ∧ BndF (PowerSeries.X : PowerSeries K) fun g => φ g⁻¹) ∧ (∀ (ι : Type) (s : Finset ι) (φ : ι → G → FractionRing (PowerSeries K)), (∀ i ∈ s, BndF (PowerSeries.X : PowerSeries K) (φ i)) → BndF (PowerSeries.X : PowerSeries K) fun g => ∑ i ∈ s, φ i g) ∧ (∀ φ : G → PowerSeries K, AdicCont (Ideal.span {(PowerSeries.X : PowerSeries K)}) φ → BndF (PowerSeries.X : PowerSeries K) fun g => algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (φ g)) ∧ ∀ (φ : G → FractionRing (PowerSeries K)), BndF (PowerSeries.X : PowerSeries K) φ → ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∃ φ' : G → PowerSeries K, AdicCont (Ideal.span {(PowerSeries.X : PowerSeries K)}) φ' ∧ ∀ g, algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (φ' g) = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X ^ s * φ g := by
  intro K G _ _ _ _
  have hconst : ∀ c : FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) fun _ : G => c := by
    intro c
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (PowerSeries K)) c
    have hb : (b : PowerSeries K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    obtain ⟨v, hv⟩ := PowerSeries.isUnit_divided_by_X_pow_order hb
    obtain ⟨n, hbv⟩ : ∃ n : ℕ, (b : PowerSeries K) = PowerSeries.X ^ n * (v : PowerSeries K) :=
      ⟨(b : PowerSeries K).order.toNat, by rw [hv, PowerSeries.X_pow_order_mul_divXPowOrder]⟩
    have hb0 : algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))).mpr hb
    unfold BndF
    refine ⟨n, fun _ => a * ↑v⁻¹, ac_const _, fun _ => ?_⟩
    dsimp only
    rw [IsFractionRing.mk'_eq_div, mul_div_assoc', eq_div_iff hb0,
      ← map_mul (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))),
      ← map_pow (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))),
      ← map_mul (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))]
    congr 1
    rw [hbv, show a * ↑v⁻¹ * (PowerSeries.X ^ n * ↑v) = PowerSeries.X ^ n * a * (↑v⁻¹ * ↑v) by ring,
      Units.inv_mul, mul_one]
  have hops : ∀ φ ψ : G → FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) φ →
      BndF (PowerSeries.X : PowerSeries K) ψ →
      (BndF (PowerSeries.X : PowerSeries K) fun g => φ g + ψ g) ∧
      (BndF (PowerSeries.X : PowerSeries K) fun g => φ g * ψ g) ∧
      (BndF (PowerSeries.X : PowerSeries K) fun g => -φ g) ∧
      BndF (PowerSeries.X : PowerSeries K) fun g => φ g⁻¹ := by
    intro φ ψ hφ hψ
    unfold BndF at hφ hψ ⊢
    obtain ⟨s1, φ1, hc1, he1⟩ := hφ
    obtain ⟨s2, ψ2, hc2, he2⟩ := hψ
    refine ⟨⟨s1 + s2, fun g => PowerSeries.X ^ s2 * φ1 g + PowerSeries.X ^ s1 * ψ2 g, ?_, fun g => ?_⟩,
      ⟨s1 + s2, fun g => φ1 g * ψ2 g, (adicCont_add_and_adicCont_mul hc1 hc2).2, fun g => ?_⟩,
      ⟨s1, fun g => -φ1 g, adicCont_neg_of_adicCont hc1, fun g => ?_⟩,
      ⟨s1, fun g => φ1 g⁻¹, adicCont_comp_inv_of_isTopologicalGroup hc1, fun g => he1 g⁻¹⟩⟩
    · exact (adicCont_add_and_adicCont_mul (adicCont_add_and_adicCont_mul (ac_const _) hc1).2 (adicCont_add_and_adicCont_mul (ac_const _) hc2).2).1
    · simp only [map_add (f := _), map_mul, map_pow, he1, he2]
      ring
    · simp only [map_mul, he1, he2]
      ring
    · simp only [map_neg, he1]
      ring
  refine ⟨hconst, hops, ?_, ?_, ?_⟩
  · intro ι s φ hφ
    classical
    revert hφ
    refine Finset.induction_on s ?_ ?_
    · intro _
      simpa using hconst 0
    · intro a t hat ih hall
      have h1 := hall a (Finset.mem_insert_self a t)
      have h2 := ih (fun i hi => hall i (Finset.mem_insert_of_mem hi))
      simp only [Finset.sum_insert hat]
      exact (hops _ _ h1 h2).1
  · intro φ hφ
    unfold BndF
    exact ⟨0, φ, hφ, fun g => by simp⟩
  · intro φ hφ
    unfold BndF at hφ
    obtain ⟨s0, φ0, hc0, he0⟩ := hφ
    refine ⟨s0, fun s hs => ⟨fun g => PowerSeries.X ^ (s - s0) * φ0 g, (adicCont_add_and_adicCont_mul (ac_const _) hc0).2, fun g => ?_⟩⟩
    rw [map_mul, map_pow, he0, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hs]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.OddDiag
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem conjugate_diagonal_zero_of_parity {R : Type} [CommRing R] {n : ℕ} (p q : Fin n → Bool)
    (w wi Z : Matrix (Fin n) (Fin n) R) (h1 : w * wi = 1) (h2 : wi * w = 1)
    (hw : ∀ i j, p i ≠ q j → w i j = 0) (hZ : ∀ i j, p i = p j → Z i j = 0) (i : Fin n) :
    (wi * Z * w) i i = 0 := by
  classical
  set P : Matrix (Fin n) (Fin n) R := Matrix.diagonal (fun k => if p k then (1 : R) else 0) with hP
  set Q : Matrix (Fin n) (Fin n) R := Matrix.diagonal (fun k => if q k then (1 : R) else 0) with hQ
  have hPw : P * w = w * Q := by
    ext a b
    rw [hP, hQ, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hab : p a = q b
    · rw [hab, mul_comm]
    · rw [hw a b hab]; simp
  have hQwi : Q * wi = wi * P := by
    calc Q * wi = (wi * w) * Q * wi := by rw [h2, Matrix.one_mul]
      _ = wi * (w * Q) * wi := by rw [Matrix.mul_assoc wi w Q]
      _ = wi * (P * w) * wi := by rw [hPw]
      _ = wi * P * (w * wi) := by simp only [Matrix.mul_assoc]
      _ = wi * P := by rw [h1, Matrix.mul_one]
  have hwi : ∀ a b, p b ≠ q a → wi a b = 0 := by
    intro a b hab
    have e := congrFun (congrFun hQwi a) b
    rw [hP, hQ, Matrix.diagonal_mul, Matrix.mul_diagonal] at e
    cases hpa : p b <;> cases hqa : q a <;> simp_all
  simp only [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : p j = q i
  · by_cases hk : p k = q i
    · rw [hZ j k (hj.trans hk.symm)]; ring
    · rw [hw k i hk]; ring
  · rw [hwi i j hj]; ring

theorem UpperTheory.V.Pa.oddDiag :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (R : Type) [CommRing R] [Algebra x.A R] (v : L.Vl), x.wX R v * x.wiX R v = 1 ∧ x.wiX R v * x.wX R v = 1 ∧ (∀ Z ∈ Od x.A R n x.a, ∀ i, (x.wiX R v * Z * x.wX R v) i i = 0) ∧ (∀ g, (∀ i j, j < i → (x.wiX R v * x.ρX R (G0.φ v g) * x.wX R v) i j = 0) ∧ ∀ i, (x.wiX R v * x.ρX R (G0.φ v g) * x.wX R v) i i = algebraMap x.A R (x.ψ v i g)) ∧ (∀ g g', x.ρX R (g * g') = x.ρX R g * x.ρX R g') ∧ x.ρX R 1 = 1 ∧ (∀ g, x.ρX R g ∈ Ev x.A R n x.a) ∧ ∀ g, (x.ρX R g)ᵀ * x.ρX R (G0.frame.conj g) = algebraMap x.A R ((G0.frame.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) • (1 : Matrix (Fin n) (Fin n) R) := by
  intro l _ L G G0 h n x R _ _ v
  have hmat : ∀ g, mat x.ρ g = ((x.ρ g : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A) := fun g => rfl
  have hconj : ∀ g, x.wiX R v * x.ρX R g * x.wX R v =
      ((((x.w v)⁻¹ * x.ρ g * x.w v : GL (Fin n) x.A)) : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A R) := by
    intro g
    simp only [NP.wX, NP.wiX, NP.ρX, hmat, Units.val_mul, Matrix.map_mul]
  have hw1 : x.wX R v * x.wiX R v = 1 := by
    simp only [NP.wX, NP.wiX]
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hw2 : x.wiX R v * x.wX R v = 1 := by
    simp only [NP.wX, NP.wiX]
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨hw1, hw2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Z hZ i
    refine conjugate_diagonal_zero_of_parity (fun k => decide ((k : ℕ) < x.a)) (x.ty v) _ _ Z hw1 hw2 ?_ ?_ i
    · intro a b hab
      simp only [NP.wX, Matrix.map_apply]
      rw [x.w_blk v a b hab, map_zero]
    · intro a b hab
      have := (hZ a b).1 (by simpa using hab)
      simpa using this
  · intro g
    have t := x.tri v g
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hconj, Matrix.map_apply]
      exact (congrArg (algebraMap x.A R) (t.1 i j hij)).trans (map_zero _)
    · rw [hconj, Matrix.map_apply]
      exact congrArg (algebraMap x.A R) (t.2 i)
  · intro g g'
    simp only [NP.ρX, map_mul, Matrix.map_mul]
  · simp only [NP.ρX, map_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · intro g i j
    have hb := x.blk g i j
    refine ⟨fun _ => Submodule.mem_top, fun hn => ?_⟩
    have h0 := hb.2 hn
    rw [Submodule.mem_bot] at h0 ⊢
    simp only [NP.ρX, Matrix.map_apply, h0, map_zero]
  · intro g
    have e := x.form g
    have e2 := congrArg (fun M => M.map (algebraMap x.A R)) e
    simp only [Units.val_one, Matrix.mul_one] at e2
    simp only [NP.ρX, ← Matrix.transpose_map, ← Matrix.map_mul]
    rw [e2]
    ext i j
    by_cases hij : i = j
    · simp [Matrix.one_apply, GFrame.eps, hij]
    · simp [Matrix.one_apply, GFrame.eps, hij]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.HomBasic
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.homBasic :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0), Function.Surjective h.p₀ ∧ Continuous h.p₀ ∧ (∀ g, h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g)) ∧ (∀ v g, h.p₀ (G.φ v g) = G0.φ v g) ∧ (∀ w, ∀ g ∈ G.frame.Iu w, h.p₀ g ∈ G0.frame.Iu w) ∧ ∀ (O R : Type) [CommRing O] [Algebra ℤ_[l] O] [CommRing R] [Algebra O R] (g : G.G₀), G0.frame.eps O R (h.p₀ g) = G.frame.eps O R g := by
  intro l _ L G G0 h
  refine ⟨fun g => ?_, (h.cont.comp continuous_subtype_val).subtype_mk _, fun g => Subtype.ext ?_,
    fun v g => Subtype.ext (h.φ v g), ?_, fun O R _ _ _ _ g => ?_⟩
  · obtain ⟨a, ha⟩ := h.surj g
    exact ⟨⟨a, by rw [MonoidHom.mem_ker, ← h.η, ha]; exact g.2⟩, Subtype.ext ha⟩
  · change h.p (G.c * g * G.c⁻¹) = G0.c * h.p g * G0.c⁻¹
    rw [map_mul, map_mul, map_inv, h.c]
  · rintro w _ ⟨j, hj, rfl⟩
    exact ⟨j, hj, Subtype.ext (h.φu w j).symm⟩
  · change Units.map _ (G0.ε (h.p g)) = Units.map _ (G.ε g)
    rw [h.ε]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PrVr
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.prVr :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ g (i j : Fin S.n), S.rF (S.pr0 (S.U.vr g i j)) = S.ρ S.F g i j ∧ ((((i : ℕ) < S.x.a) ↔ ((j : ℕ) < S.x.a)) → S.pr1 (S.U.vr g i j) = 0) ∧ (¬ (((i : ℕ) < S.x.a) ↔ ((j : ℕ) < S.x.a)) → S.pr0 (S.U.vr g i j) = 0) := by
  intro l _ S g i j
  have hm : S.U.vr g ∈ blkMat S.n S.x.a (1 : Submodule S.Bh S.U.AA) S.U.N := by
    rw [← S.U.span]; exact Submodule.subset_span ⟨g, rfl⟩
  have hN : S.U.vr g i j - algebraMap S.Bh S.U.AA (S.pr0 (S.U.vr g i j)) ∈ S.U.N := (S.pr1 (S.U.vr g i j)).2
  have hd := Submodule.disjoint_def.1 S.U.compl.disjoint
  have h1 : algebraMap S.Bh S.U.AA (S.pr0 (S.U.vr g i j)) ∈ (1 : Submodule S.Bh S.U.AA) :=
    Submodule.mem_one.2 ⟨_, rfl⟩
  refine ⟨S.U.red g i j _ hN, fun e => ?_, fun e => ?_⟩
  · exact Subtype.ext (hd _ (Submodule.sub_mem _ ((hm i j).1 e) h1) hN)
  · apply S.U.inj
    rw [map_zero]
    refine hd _ h1 ?_
    have := S.U.N.sub_mem ((hm i j).2 e) hN
    rwa [sub_sub_cancel] at this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.BndRho
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem bnd_of {A Fr Γ Γ' : Type} [CommRing A] [CommRing Fr] [Algebra A Fr] [TopologicalSpace Γ]
    [TopologicalSpace Γ'] (t : A) (φ : Γ' → A) (hφ : AdicCont (Ideal.span {t}) φ) (p : Γ → Γ') (hp : Continuous p) :
    BndF t fun g => algebraMap A Fr (φ (p g)) :=
  ⟨0, fun g => φ (p g), fun N => (hφ N).comp_continuous hp, fun g => by simp⟩

theorem UpperTheory.V.Pa.bndRho :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), BndM x.t (fun g : G.G₀ => x.ρX x.Fr (h.p₀ g)) ∧ BndM x.t (fun g : G.G₀ => x.ρX x.Fr (h.p₀ g⁻¹)) ∧ ∀ j, BndM x.t (kapF h k j) := by
  intro l _ L G G0 h n x k
  have hp : Continuous (h.p₀ : G.G₀ → G0.G₀) := by
    apply Continuous.subtype_mk
    exact h.cont.comp continuous_subtype_val
  have hpi : Continuous (fun g : G.G₀ => h.p₀ g⁻¹) := hp.comp continuous_inv
  have hρ : ∀ i j, AdicCont (Ideal.span {x.t}) (fun g : G0.G₀ => (mat x.ρ) g i j) := by
    intro i j
    have := x.cont i j
    rwa [PowerSeries.maximalIdeal_eq_span_X] at this
  refine ⟨fun i j => bnd_of x.t _ (hρ i j) _ hp, fun i j => bnd_of x.t _ (hρ i j) _ hpi, ?_⟩
  intro j i i'
  have hk := ((k.mem j).2.1 i i')
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hk
  exact bnd_of x.t _ hk _ hp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.ClosureIdeal
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem chi_rep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [Matrix.charpoly, Matrix.charmatrix]
  congr 1
  rw [map_sub, MonoidAlgebra.mapRingHom_single, map_one]
  ext i j : 2
  simp [GDet.repAlg, Matrix.one_apply, Matrix.diagonal_apply]

private theorem rep_single {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Algebra B A] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) (b : B) :
    GDet.repAlg ρ A (MonoidAlgebra.mapRingHom G (algebraMap B A) (MonoidAlgebra.single g b)) =
      algebraMap B A b • ρ g := by
  rw [MonoidAlgebra.mapRingHom_single]
  ext i j
  simp [GDet.repAlg]

theorem UpperTheory.V.Pa.vrRel :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), (∀ v (g : Fin S.n → S.L.Gv v), (List.ofFn fun i => S.U.vr (S.G.φ v (g i)) - algebraMap S.U.AA (Matrix (Fin S.n) (Fin S.n) S.U.AA) (algebraMap S.B S.U.AA (S.u.ψ v i (g i)))).prod = 0) ∧ (∀ w, ∀ g ∈ S.G.frame.Iu w, S.U.vr g = 1) ∧ (∀ j, (List.ofFn fun i => S.U.vr (S.P.ph j) - algebraMap S.U.AA (Matrix (Fin S.n) (Fin S.n) S.U.AA) (algebraMap S.B S.U.AA (S.P.U j i))).prod = 0) ∧ (∀ j i, (List.ofFn fun k => if k = i then 1 else S.U.vr (S.P.ph j) - algebraMap S.U.AA (Matrix (Fin S.n) (Fin S.n) S.U.AA) (algebraMap S.B S.U.AA (S.P.U j k))).prod * (S.U.vr (S.P.ta j) - 1 - algebraMap S.U.AA (Matrix (Fin S.n) (Fin S.n) S.U.AA) (algebraMap S.B S.U.AA (S.P.y j i))) = 0) ∧ ∀ i g, algebraMap S.B S.U.AA (S.u.D.lam i (MonoidAlgebra.single g 1)) = (-1) ^ i * (S.U.vr g).charpoly.coeff (S.n - i) := by
  intro l _ S
  let Φ : MonoidAlgebra S.B S.G.G₀ →+* Matrix (Fin S.n) (Fin S.n) S.U.AA :=
    (GDet.repAlg S.U.vr S.U.AA).toRingHom.comp (MonoidAlgebra.mapRingHom S.G.G₀ (algebraMap S.B S.U.AA))
  have h1 : ∀ g : S.G.G₀, Φ (MonoidAlgebra.single g 1) = S.U.vr g := fun g =>
    (rep_single S.U.vr g (1 : S.B)).trans (by rw [map_one, one_smul])
  have h2 : ∀ b : S.B, Φ (MonoidAlgebra.single 1 b) =
      algebraMap S.U.AA (Matrix (Fin S.n) (Fin S.n) S.U.AA) (algebraMap S.B S.U.AA b) := fun b =>
    (rep_single S.U.vr 1 b).trans (by rw [map_one, Algebra.algebraMap_eq_smul_one (A := Matrix _ _ _)])
  have hk : ∀ z ∈ pairGens S.u ∪ qGens (O := S.O) (F := S.G.frame) S.P.ph S.P.ta S.P.U S.P.y, Φ z = 0 := by
    intro z hz
    refine S.U.kills z ?_
    change z ∈ S.u.D.chBar _
    simp only [GDet.chBar, closureIdeal, TwoSidedIdeal.mem_iInf]
    exact fun N H => TwoSidedIdeal.subset_span (Or.inl (Or.inl (Or.inr hz)))
  refine ⟨fun v g => ?_, fun w g hg => ?_, fun j => ?_, fun j i => ?_, fun i g => ?_⟩
  · rw [← hk (S.G.frame.oEl v (S.u.ψ v) g) (Or.inl (Or.inl ⟨v, g, Or.inl rfl⟩)), GFrame.oEl, map_list_prod,
      List.map_ofFn]
    congr 2
    funext i
    dsimp only [Function.comp_apply]
    rw [map_sub, h1, h2]
  · have := hk _ (Or.inl (Or.inr ⟨w, g, (S.P.Ip w).symm ▸ hg, Or.inl rfl⟩))
    rwa [map_sub, h1, map_one, sub_eq_zero] at this
  · rw [← hk _ (Or.inr (Or.inl ⟨j, Or.inl rfl⟩)), q1El, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    dsimp only [Function.comp_apply]
    rw [map_sub, h1, h2]
  · rw [← hk _ (Or.inr (Or.inr ⟨j, i, Or.inl rfl⟩)), q2El, map_mul, map_list_prod, List.map_ofFn, map_sub, map_sub,
      h1, h2, map_one]
    congr 3
    funext k
    dsimp only [Function.comp_apply]
    split_ifs
    · rw [map_one]
    · rw [map_sub, h1, h2]
  · rw [← ((UpperTheory.V.CA.d_gmap S.u.D).2.2.1 (algebraMap S.B S.U.AA) _).2 i, S.U.det, MonoidAlgebra.mapRingHom_single,
      map_one, GDet.lam, chi_rep]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.KapF
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.indF :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ c : Fin k.g → x.Fr, ∑ j, c j • kapF h k j ∈ BdM h x x.Fr → c = 0 := by
  intro l _ L G G0 h n x k c hc
  classical
  obtain ⟨Y, hY, hYt, hcY⟩ := hc
  have hinj : Function.Injective (algebraMap x.A x.Fr) := IsFractionRing.injective x.A x.Fr
  have hsurj : Function.Surjective h.p₀ := by
    rintro ⟨g', hg'⟩
    obtain ⟨γ, hγ⟩ := h.surj g'
    refine ⟨⟨γ, ?_⟩, Subtype.ext hγ⟩
    show G.η γ = 1
    rw [← h.η, hγ]
    exact hg'
  have hb : ∃ b : nonZeroDivisors x.A, ∀ i : Fin k.g ⊕ (Fin n × Fin n),
      ∃ r : x.A, algebraMap x.A x.Fr r = (b : x.A) • Sum.elim c (fun p => Y p.1 p.2) i :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors x.A) _
  obtain ⟨b, hb⟩ := hb
  choose a ha using hb
  let cA : Fin k.g → x.A := fun j => a (Sum.inl j)
  let YA : Matrix (Fin n) (Fin n) x.A := fun i j => a (Sum.inr (i, j))
  let ψ := (Algebra.ofId x.A x.Fr).mapMatrix (m := Fin n)
  have hψ : ∀ M : Matrix (Fin n) (Fin n) x.A, ψ M = M.map (algebraMap x.A x.Fr) := fun M => rfl
  have hψinj : Function.Injective ψ := by
    intro M N hMN
    refine Matrix.ext fun i j => ?_
    apply hinj
    have := congrFun (congrFun hMN i) j
    rwa [hψ, hψ] at this
  have hψY : ψ YA = (b : x.A) • Y := by
    refine Matrix.ext fun i j => ?_
    rw [hψ]
    exact ha (Sum.inr (i, j))
  have hρ : ∀ g, ψ (x.ρX x.A g) = x.ρX x.Fr g := by
    intro g
    refine Matrix.ext fun i j => ?_
    simp [hψ, NP.ρX]
  have hκ : ∀ j γ, ψ (k.κ j (h.p₀ γ)) = kapF h k j γ := fun j γ => rfl
  have hcj : ∀ j (M : Matrix (Fin n) (Fin n) x.Fr), cA j • M = (b : x.A) • (c j • M) := by
    intro j M
    rw [← algebraMap_smul x.Fr (cA j) M, ha (Sum.inl j), Sum.elim_inl, smul_assoc]
  have hmem : ∑ j, cA j • k.κ j ∈ Bd G0.frame (x.ρX x.A) (Od x.A x.A n x.a) := by
    refine ⟨YA, ?_, ?_, ?_⟩
    · intro i j
      refine ⟨fun hij => ?_, fun _ => Submodule.mem_top⟩
      have h0 : Y i j = 0 := (Submodule.mem_bot _).1 ((hY i j).1 hij)
      rw [Submodule.mem_bot]
      apply hinj
      rw [map_zero]
      have := ha (Sum.inr (i, j))
      rw [Sum.elim_inr, h0, smul_zero] at this
      exact this
    · refine Matrix.ext fun i j => ?_
      apply hinj
      have h1 := ha (Sum.inr (j, i))
      have h2 := ha (Sum.inr (i, j))
      rw [Sum.elim_inr] at h1 h2
      have hYij : Y j i = - Y i j := congrFun (congrFun hYt i) j
      rw [Matrix.transpose_apply, Matrix.neg_apply, map_neg]
      show algebraMap x.A x.Fr (a (Sum.inr (j, i))) = -algebraMap x.A x.Fr (a (Sum.inr (i, j)))
      rw [h1, h2, hYij, smul_neg]
    · funext g'
      obtain ⟨γ, rfl⟩ := hsurj g'
      apply hψinj
      have hL : ψ ((∑ j, cA j • k.κ j) (h.p₀ γ)) = (b : x.A) • (∑ j, c j • kapF h k j) γ := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, hκ, hcj, Finset.smul_sum]
      rw [hL, hcY]
      simp only [dY, map_sub, map_mul, hρ, hψY, Matrix.mul_smul, Matrix.smul_mul, smul_sub, map_inv]
  have hzero := k.indep cA hmem
  funext j
  have hj := ha (Sum.inl j)
  have h0 : cA j = 0 := congrFun hzero j
  rw [Sum.elim_inl, Algebra.smul_def] at hj
  change algebraMap x.A x.Fr (cA j) = _ at hj
  rw [h0, map_zero] at hj
  have hb0 : algebraMap x.A x.Fr (b : x.A) ≠ 0 := fun h0' =>
    nonZeroDivisors.ne_zero b.2 (hinj (h0'.trans (map_zero _).symm))
  exact (mul_eq_zero.1 hj.symm).resolve_left hb0
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.RfEx
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.rfEx :
    ∀ (K O B Bh : Type) [Field K] [CommRing O] [IsLocalRing O] [Algebra O K] [CommRing B] [Algebra O B] [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] (f : B →ₐ[O] PowerSeries K), IsCplAt B (RingHom.ker f) Bh → ∃ rF : Bh →+* FractionRing (PowerSeries K), (∀ b, rF (algebraMap B Bh b) = algebraMap (PowerSeries K) _ (f b)) ∧ RingHom.ker rF = maximalIdeal Bh := by
  intro K O B Bh _ _ _ _ _ _ _ _ _ f h
  haveI : IsAdicComplete (maximalIdeal (FractionRing (PowerSeries K))) (FractionRing (PowerSeries K)) := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  let φ : B →+* FractionRing (PowerSeries K) :=
    (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (f : B →+* PowerSeries K)
  have hcomap : Ideal.comap φ (maximalIdeal (FractionRing (PowerSeries K))) = RingHom.ker f := by
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
    ext b
    simp only [RingHom.mem_ker, φ, RingHom.comp_apply, RingHom.coe_coe]
    exact map_eq_zero_iff _ (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))
  obtain ⟨ψ, hψ, -⟩ := IsCplAt.existsUnique_lift B (RingHom.ker f) Bh h (FractionRing (PowerSeries K)) φ hcomap
  refine ⟨ψ, fun b => RingHom.congr_fun hψ b, le_antisymm ?_ ?_⟩
  · intro x hx
    by_contra hm
    have hu : IsUnit x := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hm
      exact hm
    exact (hu.map ψ).ne_zero (RingHom.mem_ker.mp hx)
  · have hm := IsCplAt.map_pow_eq B (RingHom.ker f) Bh h 1
    rw [pow_one, pow_one] at hm
    rw [← hm]
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hψ]
    simp only [φ, RingHom.comp_apply, RingHom.coe_coe]
    rw [RingHom.mem_ker.mp ha, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PresOut0
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.presOut0 :
    ∀ (O B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CommRing B] [Algebra O B] [IsCO O B] (D0 : ℕ) (X : Fin D0 → B), (∀ a, X a ∈ maximalIdeal B) → maximalIdeal B ≤ Ideal.span (Set.range X) ⊔ ((maximalIdeal O).map (algebraMap O B) ⊔ maximalIdeal B ^ 2) → ∀ Z Q : Ideal B, Z.IsPrime → Q.IsPrime → ((1 + D0 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ Z) → Z ≤ Q := by
  intro O B _ _ _ _ _ _ _ D0 X hX hspan Z Q hZ hQ hdim
  haveI hOO : IsCO O O :=
    { complete := inferInstance
      isLocalHom := ⟨fun a h => by simpa using h⟩
      res_surj := fun x => ⟨x, by simp⟩ }
  haveI hA : IsCO O (MvPowerSeries (Fin D0) O) := co_mvps O O (Fin D0)
  obtain ⟨F, ⟨hFC, hFX⟩, -⟩ := co_ev O O B (Fin D0) (Algebra.ofId O B) X hX
  have hsurj : Function.Surjective F := by
    apply co_surj
    refine le_trans hspan (sup_le ?_ (sup_le ?_ le_sup_right))
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      refine Ideal.mem_sup_left ?_
      rw [← hFX i]
      refine Ideal.mem_map_of_mem _ ?_
      rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff]
      simp
    · refine le_sup_of_le_left ?_
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap]
      have h1 : algebraMap O B a = F (MvPowerSeries.C a) := by
        rw [hFC]; rfl
      rw [h1]
      refine Ideal.mem_map_of_mem _ ?_
      rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff]
      simpa using ha
  have hdimA : ringKrullDim (MvPowerSeries (Fin D0) O) = 1 + (D0 : WithBot ℕ∞) := by
    rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one]
    simp
  have hinj : ∀ r, F r ∈ Z → r = 0 := by
    intro r hr
    by_contra hne
    have hnz : r ∈ nonZeroDivisors (MvPowerSeries (Fin D0) O) := mem_nonZeroDivisors_of_ne_zero hne
    have hle := ringKrullDim_succ_le_of_surjective ((Ideal.Quotient.mk Z).comp F.toRingHom)
      ((Ideal.Quotient.mk_surjective).comp hsurj) hnz (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hr)
    rw [hdimA] at hle
    generalize ringKrullDim (B ⧸ Z) = d at hle hdim
    have hb : d ≠ ⊥ := ne_bot_of_le_ne_bot (WithBot.coe_ne_bot) hdim
    obtain ⟨e, rfl⟩ := WithBot.ne_bot_iff_exists.mp hb
    have h2 : (((1 + D0 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (e : WithBot ℕ∞) := hdim
    rw [WithBot.coe_le_coe] at h2
    have h1 : ((e + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((1 + D0 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      push_cast at hle ⊢; exact hle
    rw [WithBot.coe_le_coe] at h1
    have het : e ≠ ⊤ := by
      intro h; rw [h] at h1; simp at h1
    lift e to ℕ using het
    norm_cast at h1 h2
    omega
  have hZbot : Z = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨r, rfl⟩ := hsurj z
    rw [hinj r hz, map_zero]
    exact Ideal.zero_mem _
  rw [hZbot]
  exact bot_le
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DiscImp
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.UrepStable
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem tr_of_map {n : ℕ} {A G K : Type} [CommRing A] [Group G] [CommRing K] (hn : 1 ≤ n)
    (D : GDet n A G) (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (h : D.map f = GDet.ofRep ρ) (g : G) :
    f (D.tr (MonoidAlgebra.single g 1)) = (ρ g).trace := by
  have h1 := ((d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 1
  rw [MonoidAlgebra.mapRingHom_single, map_one, h] at h1
  have h2 := (d_toDet (GDet.ofRep ρ) (MonoidAlgebra.single g 1)).2.2.1
  rw [d_toDet_ofRep.1, (d_ofRep _ _ _).2.2.1 hn] at h2
  have h3 : GDet.repAlg ρ K (MonoidAlgebra.single g 1) = ρ g := by
    ext i j; simp [GDet.repAlg]
  rw [h3] at h2
  exact h1.symm.trans h2.symm

private theorem span_of_gram {n : ℕ} {K : Type} [Field K] (s : Set (Matrix (Fin n) (Fin n) K))
    (x y : Fin (n * n) → Matrix (Fin n) (Fin n) K) (hx : ∀ a, x a ∈ s)
    (hdet : Matrix.det (Matrix.of fun a b => (x a * y b).trace) ≠ 0) : Submodule.span K s = ⊤ := by
  have hrank : Module.finrank K (Matrix (Fin n) (Fin n) K) = Fintype.card (Fin (n * n)) := by
    simp [Module.finrank_matrix]
  have hli : LinearIndependent K x := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have : g = 0 := by
      apply Matrix.eq_zero_of_vecMul_eq_zero hdet
      funext c
      have hvec : Matrix.vecMul g (Matrix.of fun a b => (x a * y b).trace) c
          = ((∑ a, g a • x a) * y c).trace := by
        simp [Matrix.vecMul, dotProduct, Finset.sum_mul, Matrix.trace_sum]
      rw [hvec, hg]
      simp
    intro i
    simp [this]
  have := hli.span_eq_top_of_card_eq_finrank' hrank.symm
  rw [eq_top_iff, ← this]
  apply Submodule.span_mono
  rintro _ ⟨a, rfl⟩
  exact hx a

private theorem discSt_iff {n : ℕ} {A G K : Type} [CommRing A] [Group G] [Field K] (hn : 1 ≤ n)
    (D : GDet n A G) (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (h : D.map f = GDet.ofRep ρ)
    (Q : Ideal A) (hQ : ∀ b, f b = 0 ↔ b ∈ Q) :
    DiscSt D Q ↔ Submodule.span K (Set.range ρ) = ⊤ := by
  have key : ∀ g g' : Fin (n * n) → G,
      f (Matrix.det (Matrix.of fun a b => D.tr (MonoidAlgebra.single (g a * g' b) 1))) =
        Matrix.det (Matrix.of fun a b => (ρ (g a) * ρ (g' b)).trace) := by
    intro g g'
    rw [RingHom.map_det]
    congr 1
    ext a b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply,
      tr_of_map hn D f ρ h, map_mul]
  constructor
  · rintro ⟨g, g', hg⟩
    refine span_of_gram _ (fun a => ρ (g a)) (fun a => ρ (g' a)) (fun a => ⟨_, rfl⟩) fun h0 => hg ?_
    rw [← hQ, key]
    exact h0
  · intro hs
    obtain ⟨x, hx, hdet⟩ := (g_gram _ _ _).1 hs
    choose g hg using hx
    refine ⟨fun a => g (finProdFinEquiv.symm a), fun a => g (finProdFinEquiv.symm a), fun hm => hdet ?_⟩
    rw [← hQ, key] at hm
    rw [← Matrix.det_submatrix_equiv_self finProdFinEquiv.symm, ← hm]
    congr 1
    ext a b
    simp only [hg, Matrix.submatrix_apply, Matrix.of_apply]

private theorem top_of_single {n : ℕ} {K : Type} [Field K] (S : Submodule K (Matrix (Fin n) (Fin n) K))
    (h : ∀ i j, ∃ c : K, c ≠ 0 ∧ Matrix.single i j c ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine S.sum_mem fun i _ => S.sum_mem fun j _ => ?_
  obtain ⟨c, hc, hm⟩ := h i j
  have := S.smul_mem (M i j * c⁻¹) hm
  rwa [Matrix.smul_single, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hc, mul_one] at this

private theorem single_mem_blk {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n a : ℕ}
    (V₁ V₂ : Submodule A R) (i j : Fin n) (c : R)
    (h1 : (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → c ∈ V₁) (h2 : ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → c ∈ V₂) :
    Matrix.single i j c ∈ blkMat n a V₁ V₂ := by
  intro i' j'
  by_cases hij : i = i' ∧ j = j'
  · obtain ⟨rfl, rfl⟩ := hij
    rw [Matrix.single_apply_same]
    exact ⟨h1, h2⟩
  · rw [Matrix.single_apply_of_ne _ _ _ _ _ hij]
    exact ⟨fun _ => V₁.zero_mem, fun _ => V₂.zero_mem⟩

theorem UpperTheory.V.Pa.urep_stable :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {B : Type} [CommRing B] [IsLocalRing B] {D : GDet n B G.G₀} {I : Set (MonoidAlgebra B G.G₀)} {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] {rF : Bh →+* FractionRing x.A} {e : G.G₀ →* Bˣ} (V : URep h x D I Bh rF e), ∀ Q : Ideal Bh, Q.IsPrime → (DiscSt (D.map (algebraMap B Bh)) Q ↔ x.a = n ∨ ∃ y ∈ V.N, ∃ z ∈ V.N, ∃ b : Bh, b ∉ Q ∧ y * z = algebraMap Bh V.AA b) := by
  intro l _ L G G0 h n x B _ _ D I Bh _ _ _ rF e V Q hQp
  haveI := V.fin
  have hn : 1 ≤ n := x.a_pos.trans x.a_le
  obtain ⟨Q', -, hQ', hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := V.AA) Q ⊥ (by
    intro b hb
    have : b = 0 := V.inj (by simpa using hb)
    rw [this]; exact Q.zero_mem)
  let f : V.AA →+* Q'.ResidueField := algebraMap _ _
  have hf : ∀ b, (f.comp (algebraMap Bh V.AA)) b = 0 ↔ b ∈ Q := fun b => by
    rw [RingHom.comp_apply, Ideal.algebraMap_residueField_eq_zero, ← hc, Ideal.mem_comap]
  let ρ : G.G₀ →* Matrix (Fin n) (Fin n) Q'.ResidueField := f.mapMatrix.toMonoidHom.comp V.vr
  have hρ : (D.map (algebraMap B Bh)).map (f.comp (algebraMap Bh V.AA)) = GDet.ofRep ρ := by
    rw [(d_gmap D).2.1, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, ← (d_gmap D).2.1, V.det]
    exact (d_gmap (GDet.ofRep V.vr)).2.2.2 f V.vr
  rw [discSt_iff hn _ _ ρ hρ Q hf]
  have hmem : ∀ Y ∈ blkMat n x.a (1 : Submodule Bh V.AA) V.N,
      Y.map f ∈ Submodule.span Q'.ResidueField (Set.range ρ) := by
    intro Y hY
    rw [← V.span] at hY
    induction hY using Submodule.span_induction with
    | mem _ hy =>
      obtain ⟨g, rfl⟩ := hy
      exact Submodule.subset_span ⟨g, rfl⟩
    | zero => rw [Matrix.map_zero _ (map_zero f)]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [Matrix.map_add _ (map_add f)]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have : (c • a).map f = f (algebraMap Bh V.AA c) • a.map f := by
        ext i j
        rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, Algebra.smul_def, map_mul, smul_eq_mul]
      rw [this]
      exact Submodule.smul_mem _ _ ha
  have hone : (1 : V.AA) ∈ (1 : Submodule Bh V.AA) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have hsing : ∀ (i j : Fin n) (c : V.AA), (Matrix.single i j c).map f = Matrix.single i j (f c) :=
    fun i j c => Matrix.map_single i j c f
  constructor
  · intro hs
    by_cases ha : x.a = n
    · exact Or.inl ha
    right
    have hlt : x.a < n := lt_of_le_of_ne x.a_le ha
    have hex : ∃ y ∈ V.N, f y ≠ 0 := by
      by_contra hne
      push Not at hne
      let i : Fin n := ⟨0, hn⟩
      let j : Fin n := ⟨x.a, hlt⟩
      have hall : ∀ M ∈ Submodule.span Q'.ResidueField (Set.range ρ), M i j = 0 := by
        intro M hM
        induction hM using Submodule.span_induction with
        | mem _ hy =>
          obtain ⟨g, rfl⟩ := hy
          have hg : V.vr g ∈ blkMat n x.a (1 : Submodule Bh V.AA) V.N := by
            rw [← V.span]; exact Submodule.subset_span ⟨g, rfl⟩
          refine hne _ ((hg i j).2 fun hh => ?_)
          exact lt_irrefl _ (hh.1 x.a_pos)
        | zero => rfl
        | add a b _ _ ha hb => rw [Matrix.add_apply, ha, hb, add_zero]
        | smul c a _ ha => rw [Matrix.smul_apply, ha, smul_zero]
      have := hall (Matrix.single i j 1) (hs ▸ Submodule.mem_top)
      rw [Matrix.single_apply_same] at this
      exact one_ne_zero this
    obtain ⟨y, hy, hfy⟩ := hex
    obtain ⟨c, -, hc'⟩ := V.mul_mem y hy y hy
    refine ⟨y, hy, y, hy, c, fun hcQ => ?_, hc'⟩
    have := (hf c).2 hcQ
    rw [RingHom.comp_apply, ← hc', map_mul] at this
    exact hfy (mul_self_eq_zero.1 this)
  · intro hR
    refine top_of_single _ fun i j => ?_
    by_cases hij : ((i : ℕ) < x.a) ↔ ((j : ℕ) < x.a)
    · refine ⟨f 1, by simp, ?_⟩
      rw [← hsing]
      exact hmem _ (single_mem_blk _ _ i j 1 (fun _ => hone) fun h' => (h' hij).elim)
    · rcases hR with ha | ⟨y, hy, z, -, b, hb, hyz⟩
      · exact (hij (by rw [ha]; exact ⟨fun _ => j.2, fun _ => i.2⟩)).elim
      · refine ⟨f y, fun h0 => hb ((hf b).1 ?_), ?_⟩
        · rw [RingHom.comp_apply, ← hyz, map_mul, h0, zero_mul]
        · rw [← hsing]
          exact hmem _ (single_mem_blk _ _ i j y (fun h' => (hij h').elim) fun _ => hy)
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.discImp :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ Q : Ideal S.Bh, Q.IsPrime → DiscSt (S.u.D.map (algebraMap S.B S.Bh)) Q → S.x.a = S.n ∨ ¬ ired S.U.N ≤ Q := by
  intro l _ S Q hQ hs
  rcases (UpperTheory.V.Pa.urep_stable S.U Q hQ).1 hs with ha | ⟨y, hy, z, hz, b, hb, e⟩
  · exact Or.inl ha
  · exact Or.inr fun hle => hb (hle (Ideal.subset_span ⟨y, hy, z, hz, e⟩))
end

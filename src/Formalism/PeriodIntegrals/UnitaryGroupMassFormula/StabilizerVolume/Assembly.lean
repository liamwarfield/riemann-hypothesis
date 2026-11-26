module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.LocallyCompactAdelicUnitary
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnfoldMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FinTheta
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabU
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.OrbTupFin
public import Lemmata.FunctionAtZero.FZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RpAbsHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVolDone
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensIdxF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensCnt

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.EventuallyStruct
noncomputable section

namespace PI.VolStabS

namespace CompGAux

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.VolStabS.FiniteThetaCoordinates
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem tmap_sigR (φ : R →ₐ[F] S) (x : R ⊗[F] E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (sigR R σ x) =
      sigR S σ (Algebra.TensorProduct.map φ (AlgHom.id F E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tmap_inclR (φ : R →ₐ[F] S) (e : E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (inclR R e) = inclR S e := by
  simp [inclR, Algebra.TensorProduct.map_tmul]

theorem map_mem_HR (φ : R →ₐ[F] S) {g : GL (Fin M) (R ⊗[F] E)} (hg : g ∈ HR R σ J) :
    Formalism.UG.bc (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom g ∈ HR S σ J := by
  set ψ : R ⊗[F] E →+* S ⊗[F] E := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom
  have hg' : Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := hg
  have hcT : (Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E))).map ψ =
      Formalism.UG.cT (sigR S σ) ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map ψ) := by
    ext i j
    simp [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, ψ, tmap_sigR]
  have hJ : (JR R J).map ψ = JR S J := by
    ext i j
    simp [JR, Matrix.map_apply, ψ, tmap_inclR]
  show Formalism.UG.cT (sigR S σ) ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map ψ) * JR S J *
      (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map ψ = JR S J
  rw [← hcT, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg']

def haMap (φ : R →ₐ[F] S) : HA R σ J →* HA S σ J :=
  MonoidHom.codRestrict
    ((Formalism.UG.bc (n := Fin M) (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom).comp
      (HR R σ J).subtype) (HR S σ J) (fun h => map_mem_HR σ J φ h.2)

theorem mat_haMap_apply (φ : R →ₐ[F] S) (h : HA R σ J) (i j : Fin M) :
    ((HA.mat S σ J (haMap σ J φ h) : GL (Fin M) (S ⊗[F] E)) : Matrix (Fin M) (Fin M) _) i j =
      Algebra.TensorProduct.map φ (AlgHom.id F E)
        (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) i j) := rfl

theorem map_smul_tup (φ : R →ₐ[F] S) {n : ℕ} (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E) :
    (fun x i => Algebra.TensorProduct.map φ (AlgHom.id F E) ((h • X) x i)) =
      haMap σ J φ h • (fun x i => Algebra.TensorProduct.map φ (AlgHom.id F E) (X x i)) := by
  funext x i
  show Algebra.TensorProduct.map φ (AlgHom.id F E)
      ((((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec (X x)) i) =
    (((HA.mat S σ J (haMap σ J φ h) : GL (Fin M) (S ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec
      (fun j => Algebra.TensorProduct.map φ (AlgHom.id F E) (X x j))) i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, mat_haMap_apply]

theorem tmap_comp {T : Type} [CommRing T] [Algebra F T] (f : R →ₐ[F] S) (g : S →ₐ[F] T)
    (y : R ⊗[F] E) :
    Algebra.TensorProduct.map g (AlgHom.id F E) (Algebra.TensorProduct.map f (AlgHom.id F E) y) =
      Algebra.TensorProduct.map (g.comp f) (AlgHom.id F E) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end Gen

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem crd_mulVec_mem (v : HeightOneSpectrum (𝓞 F)) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (m : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) (y : Fin M → Fv F v ⊗[F] E)
    (hm : ∀ i j p, crd b (Fv F v) (m i j) p ∈ v.adicCompletionIntegers F)
    (hy : ∀ j q, crd b (Fv F v) (y j) q ∈ v.adicCompletionIntegers F)
    (hc : ∀ p q k, algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F)
    (i : Fin M) (k : Fin d) : crd b (Fv F v) ((m.mulVec y) i) k ∈ v.adicCompletionIntegers F := by
  rw [crd_mulVec]
  exact sum_mem fun j _ => sum_mem fun p _ => sum_mem fun q _ =>
    mul_mem (mul_mem (hm i j p) (hy j q)) (hc p q k)

theorem smul_mem_latV (v : HeightOneSpectrum (𝓞 F)) {d a : ℕ} (b : Module.Basis (Fin d) F E)
    (h : HA (Fv F v) σ J)
    (hm : ∀ i j p, crd b (Fv F v)
      (((HA.mat (Fv F v) σ J h : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) i j) p ∈
        v.adicCompletionIntegers F)
    (hc : ∀ p q k, algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F)
    (Y : Fin a → Fin M → Fv F v ⊗[F] E) (hY : Y ∈ latV b v) : h • Y ∈ latV b v := by
  simp only [latV, Set.mem_ofPred_eq] at hY ⊢
  intro x i k
  exact crd_mulVec_mem v b _ (Y x) hm (fun j q => hY x j q) hc i k

theorem eventually_int (g : HA (AF F) σ J) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v in Filter.cofinite, ∀ i j p, piV F v (crd b (AF F)
      (((HA.mat (AF F) σ J g : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) i j) p) ∈
        v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  intro i j p
  exact (eventually_piV_le_one F _).mono fun v hv => (norm_le_one_iff_mem F v _).1 hv

theorem eventually_struct {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v in Filter.cofinite, ∀ p q k,
      algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  intro p q k
  refine (eventually_piV_le_one F (algebraMap F (AF F) (b.repr (b p * b q) k))).mono fun v hv => ?_
  rw [AlgHom.commutes] at hv
  exact (norm_le_one_iff_mem F v _).1 hv

theorem compG_gen (a : ℕ) (g : HA (AF F) σ J) :
    ∃ (hInf : HA (Ainf F) σ J) (hv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J),
    (∀ X : Fin a → Fin M → AF F ⊗[F] E, projInf (g • X) = hInf • projInf X) ∧
    (∀ (v : HeightOneSpectrum (𝓞 F)) (X : Fin a → Fin M → AF F ⊗[F] E),
      projV v (projFin (g • X)) = hv v • projV v (projFin X)) ∧
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in Filter.cofinite,
      ∀ Y : Fin a → Fin M → Fv F v ⊗[F] E, hv v • Y ∈ latV b v ↔ Y ∈ latV b v := by
  refine ⟨haMap σ J (fstA F) g, fun v => haMap σ J (piV F v) g, ?_, ?_, ?_⟩
  · intro X
    exact map_smul_tup σ J (fstA F) g X
  · intro v X
    have e : ∀ Z : Fin a → Fin M → AF F ⊗[F] E, projV v (projFin Z) =
        fun x i => Algebra.TensorProduct.map (piV F v) (AlgHom.id F E) (Z x i) := by
      intro Z
      funext x i
      exact tmap_comp (sndA F) (evalV F v) (Z x i)
    rw [e, e, map_smul_tup]
  · intro d b
    filter_upwards [eventually_int σ J g b, eventually_int σ J g⁻¹ b, eventually_struct b]
      with v h1 h2 h3
    have hm : ∀ g' : HA (AF F) σ J, (∀ i j p, piV F v (crd b (AF F)
        (((HA.mat (AF F) σ J g' : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) i j) p) ∈
          v.adicCompletionIntegers F) → ∀ i j p, crd b (Fv F v)
        (((HA.mat (Fv F v) σ J (haMap σ J (piV F v) g') : GL (Fin M) _) :
          Matrix (Fin M) (Fin M) _) i j) p ∈ v.adicCompletionIntegers F := by
      intro g' hg' i j p
      rw [mat_haMap_apply, crd_map]
      exact hg' i j p
    intro Y
    constructor
    · intro hY
      have := smul_mem_latV σ J v b (haMap σ J (piV F v) g⁻¹) (hm g⁻¹ h2) h3 _ hY
      rwa [map_inv, inv_smul_smul] at this
    · intro hY
      exact smul_mem_latV σ J v b (haMap σ J (piV F v) g) (hm g h1) h3 Y hY

end Loc

end CompGAux

theorem compG_holds : CompG := by
  intro F E _ _ _ _ _ σ _hCM M J _hJ _ha _hc a _ha1 _ha2 _X0 _hT _hdet g
  exact CompGAux.compG_gen σ J a g

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdAlt
namespace PI.VolStabS

theorem restrProd_holds : RestrProd :=
  restrProd_of rpAbs_holds rpFib_holds rpGlue_holds RestrProdG.rpGram_holds
    RestrProdA.rpTail_holds RestrProdA.latCofin_holds

end PI.VolStabS
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensQ
noncomputable section

namespace PI.VolStabS

open NumberField IsDedekindDomain Filter Asymptotics
open scoped nonZeroDivisors

namespace LocalCountingSum

variable (K : Type) [Field K] [NumberField K]

def cnt (n : ℕ) : ℝ := (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ)

theorem sum_cnt (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, cnt K k =
    (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ) := by
  induction n with
  | zero =>
    have hE : IsEmpty {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ 0} := by
      constructor
      rintro ⟨I, hI⟩
      have h0 : Ideal.absNorm (I : Ideal (𝓞 K)) = 0 := Nat.le_zero.1 hI
      rw [Ideal.absNorm_eq_zero_iff] at h0
      exact (mem_nonZeroDivisors_iff_ne_zero.1 I.2) (by rw [h0]; rfl)
    rw [Nat.card_of_isEmpty]
    simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    haveI : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} := (Ideal.finite_setOf_absNorm_le₀ (S := 𝓞 K) n).to_subtype
    haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n + 1} :=
      (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) (n + 1)).to_subtype
    have hnz : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = n + 1 → I ∈ (Ideal (𝓞 K))⁰ := by
      intro I hI
      refine mem_nonZeroDivisors_iff_ne_zero.2 (fun h => ?_)
      rw [h] at hI
      simp at hI
    let e : {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n + 1} ≃ {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} ⊕ {I : Ideal (𝓞 K) // Ideal.absNorm I = n + 1} :=
      { toFun := fun x => if h : Ideal.absNorm (x.1 : Ideal (𝓞 K)) ≤ n then Sum.inl ⟨x.1, h⟩
          else Sum.inr ⟨x.1.1, by have := x.2; omega⟩
        invFun := fun y => match y with
          | Sum.inl z => ⟨z.1, Nat.le_succ_of_le z.2⟩
          | Sum.inr z => ⟨⟨z.1, hnz z.1 z.2⟩, z.2.le⟩
        left_inv := by
          intro x
          by_cases h : Ideal.absNorm (x.1 : Ideal (𝓞 K)) ≤ n
          · simp only [dif_pos h]
          · simp only [dif_neg h]
        right_inv := by
          intro y
          rcases y with z | z
          · simp only [dif_pos z.2]
          · have hz : ¬ Ideal.absNorm z.1 ≤ n := by have := z.2; omega
            simp only [dif_neg hz] }
    rw [Nat.card_congr e, Nat.card_sum]
    unfold cnt
    push_cast
    ring

theorem sum_cnt_bigO :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, cnt K k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
  have h2 := (NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop
  have hc : ∀ n : ℕ, (Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ (n : ℝ)} : ℝ) =
      (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ) := by
    intro n
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun I => Nat.cast_le))
  simp only [Real.rpow_one]
  obtain ⟨L, hL⟩ : ∃ L, Tendsto ((fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, cnt K k) / fun n : ℕ => (n : ℝ))
      atTop (nhds L) :=
    ⟨_, h2.congr (fun n => by simp only [Function.comp_apply, Pi.div_apply, hc n, sum_cnt K n])⟩
  exact Asymptotics.isBigO_of_div_tendsto_nhds
    (Filter.eventually_atTop.2 ⟨1, fun n hn h0 => absurd h0 (by positivity)⟩) L hL

theorem cnt_summable : Summable fun n : ℕ ↦ cnt K n / (n : ℝ) ^ 2 := by
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := cnt K) (r := 1) (s := 2) (sum_cnt_bigO K)
    (fun n => by unfold cnt; positivity) zero_le_one (by norm_num)
  unfold LSeriesSummable at h
  have e : LSeries.term (fun n => ((cnt K n : ℝ) : ℂ)) 2 = fun n => ((cnt K n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn.ne']
      push_cast
      congr 1
      exact_mod_cast Complex.cpow_natCast (n : ℂ) 2
  rw [e] at h
  exact Complex.summable_ofReal.1 h

end LocalCountingSum

theorem qV_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    qV v = (Ideal.absNorm v.asIdeal : ℝ) := by
  unfold qV
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem qvSum_holds : QvSum := by
  intro F _ _
  haveI hfin : ∀ n : ℕ, Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
    fun n => (Ideal.finite_setOf_absNorm_eq (S := 𝓞 F) n).to_subtype
  let f : Ideal (𝓞 F) → ℝ := fun I => ((Ideal.absNorm I : ℝ))⁻¹ ^ 2
  have hf0 : ∀ I, 0 ≤ f I := fun I => by positivity
  have hsig : Summable (fun x : Σ n : ℕ, {I : Ideal (𝓞 F) // Ideal.absNorm I = n} => f x.2.1) := by
    rw [summable_sigma_of_nonneg (fun x => hf0 _)]
    refine ⟨fun n => Summable.of_finite, ?_⟩
    have e2 : (fun n : ℕ => ∑' I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}, f I.1) =
        fun n => LocalCountingSum.cnt F n / (n : ℝ) ^ 2 := by
      funext n
      have hc : ∀ I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}, f I.1 = ((n : ℝ))⁻¹ ^ 2 := by
        intro I
        simp only [f, I.2]
      rw [tsum_congr hc, tsum_const, nsmul_eq_mul]
      unfold LocalCountingSum.cnt
      rw [inv_pow, div_eq_mul_inv]
    rw [e2]
    exact LocalCountingSum.cnt_summable F
  have hI : Summable f := (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)).summable_iff.1 hsig
  have hinj : Function.Injective (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) :=
    fun v w h => HeightOneSpectrum.ext h
  refine (hI.comp_injective hinj).congr (fun v => ?_)
  simp only [Function.comp_apply, f, qV_eq]

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnfoldFin
namespace PI.VolStabS

theorem unfold_holds : Unfold :=
  unfold_of witt_holds finTheta_holds invInv_holds measOrb_holds measGrp_holds

end PI.VolStabS
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosTest
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem integrable_of_isOmT {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {ψ : AddChar (AF F) ℂ}
    {a : ℕ} {T : Matrix (Fin a) (Fin a) E} {hT : ∀ i j, σ (T j i) = T i j}
    {νX : Measure (Fin a → Fin M → AF F ⊗[F] E)} (hν : IsOmT F E σ M J ψ T hT νX)
    {Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ} (hΦ : IsAdm F E Φ) : Integrable Φ νX := by
  obtain ⟨d, b, Φinf, Φf, Φv, hc, hcs, hpf, hprod⟩ := hΦ
  obtain ⟨μinf, h1⟩ := hν.2.1
  have k1 := hν.2.2 μinf h1
  obtain ⟨νinf, h2⟩ := k1.1
  have k2 := k1.2 νinf h2
  obtain ⟨μv, h3⟩ := k2.1
  have k3 := k2.2 μv h3
  obtain ⟨νv, h4⟩ := k3.1
  have k4 := k3.2 νv h4
  obtain ⟨fibInf, h5⟩ := k4.1
  have k5 := k4.2 fibInf h5
  obtain ⟨fibV, h6⟩ := k5.1
  exact (k5.2 fibV h6 d b Φ Φinf Φf Φv hc hcs hpf hprod).1

theorem posTest_of (hN : TestNear) : PosTest := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ _hψ μ hμ νX hν μ' _hμ' hC
  obtain ⟨φ, hφ0, hadm, U, hUo, hUne, hUpos⟩ := hN F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet
  refine ⟨φ, hφ0, hadm, fun hI0 => ?_⟩
  have hint : Integrable (fun X => (φ X : ℂ)) νX := integrable_of_isOmT hν hadm.adm
  have hintR : Integrable φ νX := by simpa using hint.re
  have hI : ∫ X, φ X ∂νX = 0 := by
    rw [integral_complex_ofReal] at hI0
    exact_mod_cast hI0
  have hae : φ =ᵐ[νX] 0 := (integral_eq_zero_iff_of_nonneg (fun X => hφ0 X) hintR).1 hI
  obtain ⟨hnull, hform⟩ := hC
  classical
  let s : (Fin a → Fin M → AF F ⊗[F] E) → HA (AF F) σ J := fun y =>
    if h : ∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y then h.choose else 1
  have hs : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y) →
      s y • ratTup (AF F) X0 = y := by
    intro y h
    simp only [s, dif_pos h]
    exact h.choose_spec
  have hf : Measurable (U.indicator (1 : HA (AF F) σ J → ENNReal)) :=
    measurable_one.indicator hUo.measurableSet
  have e := hform _ hf s hs
  have hL : ∫⁻ g, U.indicator (1 : HA (AF F) σ J → ENNReal) g ∂μ = μ U :=
    lintegral_indicator_one hUo.measurableSet
  have : μ.IsHaarMeasure := hμ
  have hpos : 0 < μ U := hUo.measure_pos μ hUne
  have hR : ∫⁻ y, ∫⁻ h', U.indicator (1 : HA (AF F) σ J → ENNReal)
      (s y * (h' : HA (AF F) σ J)) ∂μ' ∂νX = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hae, ae_iff.2 hnull] with y hy0 hyo
    simp only [Pi.zero_apply] at hy0
    have hz : ∀ h' : stabT (AF F) σ J X0,
        U.indicator (1 : HA (AF F) σ J → ENNReal) (s y * (h' : HA (AF F) σ J)) = 0 := by
      intro h'
      refine Set.indicator_apply_eq_zero.2 fun hm => ?_
      exfalso
      have hh : (h' : HA (AF F) σ J) • ratTup (AF F) X0 = ratTup (AF F) X0 := h'.2
      have h0 := hUpos _ hm
      rw [mul_smul, hh, hs y hyo, hy0] at h0
      exact lt_irrefl _ h0
    simp only [hz, lintegral_zero]
  rw [hL, hR] at e
  exact hpos.ne' e

theorem posTest_holds : PosTest := posTest_of testNear_holds

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SdTestInf
noncomputable section

namespace PI.VolStabS

namespace SdTestInfW

open MeasureTheory Complex Filter Topology

theorem char_real (f : ℝ → ℂ) (hc : Continuous f) (hadd : ∀ s t, f (s + t) = f s * f t)
    (hn : ∀ s, ‖f s‖ = 1) : ∃ b : ℝ, ∀ s : ℝ, f s = exp (↑(b * s) * I) := by
  first | exact Bl.FunctionAtZero.goal1 .. | (apply Bl.FunctionAtZero.goal1 <;> assumption) | (intros; apply Bl.FunctionAtZero.goal1 <;> assumption)

theorem freq_unique {u v : ℝ} (h : ∀ s : ℝ, exp (↑(u * s) * I) = exp (↑(v * s) * I)) : u = v := by
  by_contra huv
  have hne : u - v ≠ 0 := sub_ne_zero.2 huv
  have h1 := h (Real.pi / (u - v))
  have h2 : exp (↑((u - v) * (Real.pi / (u - v))) * I) = 1 := by
    have : (↑((u - v) * (Real.pi / (u - v))) : ℂ) * I =
        ↑(u * (Real.pi / (u - v))) * I - ↑(v * (Real.pi / (u - v))) * I := by
      push_cast; ring
    rw [this, Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  rw [mul_div_cancel₀ _ hne, Complex.exp_pi_mul_I] at h2
  norm_num at h2

section Bichar

open scoped RealInnerProductSpace

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

structure IsBichar (χ : W → W → ℂ) : Prop where
  addL : ∀ x x' y, χ (x + x') y = χ x y * χ x' y
  addR : ∀ x y y', χ x (y + y') = χ x y * χ x y'
  norm1 : ∀ x y, ‖χ x y‖ = 1
  contL : ∀ y, Continuous fun x => χ x y
  contR : ∀ x, Continuous (χ x)

theorem IsBichar.zero_left {χ : W → W → ℂ} (h : IsBichar χ) (y : W) : χ 0 y = 1 := by
  have hne : χ 0 y ≠ 0 := fun h0 => by have := h.norm1 0 y; rw [h0, norm_zero] at this; exact zero_ne_one this
  have e := h.addL 0 0 y
  rw [add_zero] at e
  exact mul_left_cancel₀ hne (by rw [mul_one]; exact e.symm)

theorem IsBichar.freq {χ : W → W → ℂ} (h : IsBichar χ) (v y : W) :
    ∃ β : ℝ, ∀ s : ℝ, χ (s • v) y = exp (↑(β * s) * I) :=
  char_real (fun s => χ (s • v) y) ((h.contL y).comp (continuous_id.smul continuous_const))
    (fun s t => by simp only [add_smul]; exact h.addL _ _ y) (fun s => h.norm1 _ y)

theorem arg_exp_small {θ : ℝ} (h : θ ∈ Set.Ioo (-Real.pi) Real.pi) : arg (exp (↑θ * I)) = θ := by
  rw [arg_exp_mul_I, toIocMod_eq_self]
  exact ⟨h.1, by linarith [h.2, Real.pi_pos]⟩

theorem measurable_freq {χ : W → W → ℂ} (h : IsBichar χ) (v : W) (β : W → ℝ)
    (hβ : ∀ y, ∀ s : ℝ, χ (s • v) y = exp (↑(β y * s) * I)) : Measurable β := by
  let g : ℕ → W → ℝ := fun m y => ((m : ℝ) + 1) * arg (χ ((1 / ((m : ℝ) + 1)) • v) y)
  have hg : ∀ m, Measurable (g m) := fun m =>
    measurable_const.mul (measurable_arg.comp (h.contR _).measurable)
  refine measurable_of_tendsto_metrizable hg (tendsto_pi_nhds.2 fun y => ?_)
  have ht : Tendsto (fun m : ℕ => β y * (1 / ((m : ℝ) + 1))) atTop (𝓝 (β y * 0)) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (β y)
  rw [mul_zero] at ht
  have hev := ht (Ioo_mem_nhds (neg_lt_zero.2 Real.pi_pos) Real.pi_pos)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev] with m hm
  simp only [g]
  rw [hβ y, arg_exp_small hm]
  field_simp

theorem freq_add {χ : W → W → ℂ} (h : IsBichar χ) (v : W) (β : W → ℝ)
    (hβ : ∀ y, ∀ s : ℝ, χ (s • v) y = exp (↑(β y * s) * I)) (y y' : W) :
    β (y + y') = β y + β y' := by
  refine freq_unique fun s => ?_
  rw [← hβ, h.addR, hβ, hβ, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem bichar_eq {χ : W → W → ℂ} (h : IsBichar χ) :
    ∃ L : W →L[ℝ] W, ∀ x y, χ x y = (Real.fourierChar ⟪x, L y⟫ : ℂ) := by
  classical
  choose β hβ using fun v y => h.freq v y
  let b := stdOrthonormalBasis ℝ W
  have hm : ∀ j, Measurable (fun y => β (b j) y) := fun j =>
    measurable_freq h (b j) _ (fun y => hβ (b j) y)
  have ha : ∀ j y y', β (b j) (y + y') = β (b j) y + β (b j) y' := fun j =>
    freq_add h (b j) (fun y => β (b j) y) (fun y => hβ (b j) y)
  let Lf : W → W := fun y => ∑ j, (β (b j) y / (2 * Real.pi)) • b j
  let Lm : W →+ W := AddMonoidHom.mk' Lf fun y y' => by
    simp only [Lf, ha, add_div, add_smul, Finset.sum_add_distrib]
  have hLm : Measurable Lm := by
    show Measurable fun y => ∑ j, (β (b j) y / (2 * Real.pi)) • b j
    exact Finset.measurable_sum Finset.univ fun j _ => ((hm j).div_const _).smul_const (b j)
  have hLc : Continuous Lm := Measure.AddMonoidHom.continuous_of_measurable Lm hLm
  refine ⟨Lm.toRealLinearMap hLc, fun x y => ?_⟩
  have hprod : ∀ s : Finset (Fin (Module.finrank ℝ W)),
      χ (∑ j ∈ s, ⟪b j, x⟫ • b j) y = ∏ j ∈ s, χ (⟪b j, x⟫ • b j) y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [h.zero_left]
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, h.addL, ih]
  have e1 : χ x y = χ (∑ j, ⟪b j, x⟫ • b j) y := by rw [b.sum_repr' x]
  rw [e1, hprod]
  have e2 : ∀ j, χ (⟪b j, x⟫ • b j) y = exp (↑(β (b j) y * ⟪b j, x⟫) * I) := fun j => hβ _ _ _
  simp only [e2]
  rw [← Complex.exp_sum, Real.fourierChar_apply]
  congr 1
  have hLy : ⟪x, (Lm.toRealLinearMap hLc) y⟫ = ∑ j, β (b j) y / (2 * Real.pi) * ⟪b j, x⟫ := by
    show ⟪x, Lf y⟫ = _
    simp only [Lf, inner_sum, inner_smul_right]
    exact Finset.sum_congr rfl fun j _ => by rw [real_inner_comm]
  rw [hLy]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp

end Bichar

section Tests

open scoped RealInnerProductSpace FourierTransform SchwartzMap ContDiff

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

theorem testEx_kernel (μ : Measure W) [μ.IsAddHaarMeasure] (χ : W → W → ℂ)
    (hadd : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (hc : ∀ y, Continuous fun x => χ x y)
    (t : W) (ht0 : t ≠ 0) (ht : ∀ y, χ t y = 1) : SdUniqW.TestEx μ χ := by
  have hpos : 0 < ‖t‖ := norm_pos_iff.2 ht0
  let f : ContDiffBump (0 : W) := ⟨‖t‖ / 4, ‖t‖ / 2, by positivity, by linarith⟩
  let φ : W → ℂ := fun x => ((f x : ℝ) : ℂ)
  have hφc : Continuous φ := Complex.continuous_ofReal.comp f.continuous
  have hφs : HasCompactSupport φ := f.hasCompactSupport.comp_left Complex.ofReal_zero
  let Φ : W → ℂ := fun x => φ (x + t) - φ x
  have hΦc : Continuous Φ := (hφc.comp (continuous_id.add continuous_const)).sub hφc
  have hΦs : HasCompactSupport Φ := by
    have h1 : HasCompactSupport fun x => φ (x + t) := hφs.comp_homeomorph (Homeomorph.addRight t)
    exact h1.sub hφs
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂μ = 0 := by
    intro y
    let g : W → ℂ := fun x => φ x * χ x y
    have hg : Integrable g μ := (hφc.mul (hc y)).integrable_of_hasCompactSupport hφs.mul_right
    have e : (fun x => Φ x * χ x y) = fun x => g (x + t) - g x := by
      funext x; simp only [Φ, g, hadd, ht, mul_one, sub_mul]
    rw [e, integral_sub (hg.comp_add_right t) hg, integral_add_right_eq_self, sub_self]
  refine ⟨Φ, hΦc, hΦs, ?_, 0, ?_⟩
  · have e : (fun y => ∫ x, Φ x * χ x y ∂μ) = fun _ => 0 := funext hT
    rw [e]; exact integrable_zero _ _ _
  · simp only [Φ, φ, neg_zero, zero_add]
    rw [f.zero_of_le_dist (by rw [dist_zero_right]; show ‖t‖ / 2 ≤ ‖t‖; linarith),
      f.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))]
    norm_num

theorem testEx_fourier (μ : Measure W) [μ.IsAddHaarMeasure] (A : W ≃L[ℝ] W) :
    SdUniqW.TestEx μ (fun x y => (Real.fourierChar ⟪x, A y⟫ : ℂ)) := by
  let f : ContDiffBump (0 : W) := ⟨1, 2, one_pos, one_lt_two⟩
  let φ : W → ℂ := fun x => ((f x : ℝ) : ℂ)
  have hφd : ContDiff ℝ ∞ φ := Complex.ofRealCLM.contDiff.comp f.contDiff
  have hφs : HasCompactSupport φ := f.hasCompactSupport.comp_left Complex.ofReal_zero
  let S : 𝓢(W, ℂ) := hφs.toSchwartzMap hφd
  let B : W ≃L[ℝ] W := A.trans (ContinuousLinearEquiv.neg ℝ)
  set c : NNReal := μ.addHaarScalarFactor volume
  have hμ : μ = c • volume := Measure.isAddLeftInvariant_eq_smul μ volume
  have hT : ∀ y, ∫ x, φ x * (Real.fourierChar ⟪x, A y⟫ : ℂ) ∂μ =
      ((c : ℝ) : ℂ) * (𝓕 S : 𝓢(W, ℂ)) (B y) := by
    intro y
    rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    congr 1
    rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [B, S, φ, inner_neg_right, Circle.smul_def, mul_comm]
  have hB : (Measure.map B μ).IsAddHaarMeasure := B.isAddHaarMeasure_map μ
  have hI : Integrable (fun y => (𝓕 S : 𝓢(W, ℂ)) (B y)) μ := by
    have h1 : Integrable (𝓕 S : 𝓢(W, ℂ)) (Measure.map B μ) := (𝓕 S).integrable
    exact (integrable_map_measure h1.aestronglyMeasurable B.continuous.measurable.aemeasurable).1 h1
  refine ⟨φ, hφd.continuous, hφs, ?_, 0, ?_⟩
  · have e : (fun y => ∫ x, φ x * (Real.fourierChar ⟪x, A y⟫ : ℂ) ∂μ) =
        fun y => ((c : ℝ) : ℂ) * (𝓕 S : 𝓢(W, ℂ)) (B y) := funext hT
    rw [e]; exact hI.const_mul _
  · simp only [φ, neg_zero]
    rw [f.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
    norm_num

theorem testEx_bichar (μ : Measure W) [μ.IsAddHaarMeasure] {χ : W → W → ℂ} (h : IsBichar χ) :
    SdUniqW.TestEx μ χ := by
  obtain ⟨L, hL⟩ := bichar_eq h
  by_cases hs : Function.Surjective L
  · have hi : Function.Injective L :=
      (LinearMap.injective_iff_surjective (f := (L : W →ₗ[ℝ] W))).2 hs
    let A : W ≃L[ℝ] W :=
      (LinearEquiv.ofBijective (L : W →ₗ[ℝ] W) ⟨hi, hs⟩).toContinuousLinearEquiv
    have e : χ = fun x y => (Real.fourierChar ⟪x, A y⟫ : ℂ) :=
      funext₂ fun x y => by rw [hL x y]; rfl
    rw [e]; exact testEx_fourier μ A
  · have hK : (LinearMap.range (L : W →ₗ[ℝ] W))ᗮ ≠ ⊥ := by
      rw [Ne, Submodule.orthogonal_eq_bot_iff, LinearMap.range_eq_top]; exact hs
    obtain ⟨t, htK, ht0⟩ := (Submodule.ne_bot_iff _).1 hK
    refine testEx_kernel μ χ h.addL h.contL t ht0 fun y => ?_
    have h0 : ⟪t, L y⟫ = 0 :=
      (Submodule.mem_orthogonal' _ t).1 htK _ (LinearMap.mem_range_self (L : W →ₗ[ℝ] W) y)
    rw [hL, h0, AddChar.map_zero_eq_one, Circle.coe_one]

theorem testEx_of_homeo {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
    (e : V ≃ₜ W) (he : ∀ x y, e (x + y) = e x + e y)
    (hL : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (hR : ∀ x y y', χ x (y + y') = χ x y * χ x y')
    (hn : ∀ x y, ‖χ x y‖ = 1) (hcL : ∀ y, Continuous fun x => χ x y)
    (hcR : ∀ x, Continuous (χ x)) : SdUniqW.TestEx μ χ := by
  let ea : V ≃+ W := AddEquiv.mk' e.toEquiv he
  have hs : ∀ u v : W, e.symm (u + v) = e.symm u + e.symm v := fun u v => ea.symm.map_add u v
  let ce : V ≃ₜ+ W :=
    { ea with continuous_toFun := e.continuous, continuous_invFun := e.symm.continuous }
  let em : V ≃ᵐ W := e.toMeasurableEquiv
  let μ' : Measure W := Measure.map em μ
  have : μ'.IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ ce
  let χ' : W → W → ℂ := fun x y => χ (e.symm x) (e.symm y)
  have hb : IsBichar χ' :=
    { addL := fun x x' y => by simp only [χ', hs, hL]
      addR := fun x y y' => by simp only [χ', hs, hR]
      norm1 := fun x y => hn _ _
      contL := fun y => (hcL _).comp e.symm.continuous
      contR := fun x => (hcR _).comp e.symm.continuous }
  obtain ⟨φ, hφc, hφs, hI, z, hz⟩ := testEx_bichar μ' hb
  have hT : ∀ y, ∫ x, φ (e x) * χ x y ∂μ = ∫ x, φ x * χ' x (e y) ∂μ' := by
    intro y
    rw [integral_map_equiv em]
    simp [χ', em]
  refine ⟨fun x => φ (e x), hφc.comp e.continuous, hφs.comp_homeomorph e, ?_, e.symm z, ?_⟩
  · show Integrable (fun y => ∫ x, φ (e x) * χ x y ∂μ) μ
    have e1 : (fun y => ∫ x, φ (e x) * χ x y ∂μ) = (fun y => ∫ x, φ x * χ' x y ∂μ') ∘ em :=
      funext hT
    rw [e1]
    exact (integrable_map_equiv em _).1 hI
  · show φ (e (-e.symm z)) ≠ 0
    have h1 : e (-e.symm z) = -z := by
      have := ea.map_neg (e.symm z)
      change e (-e.symm z) = -e (e.symm z) at this
      rw [this, e.apply_symm_apply]
    rw [h1]; exact hz

end Tests

section Adelic

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation PI.VolFromSW SdUniqW

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem BR_add_right' (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y Y' : Fin n → Fin M → R ⊗[F] E) : BR R σ J X (Y + Y') = BR R σ J X Y + BR R σ J X Y' := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem pairHerm_add_right' (σ : E →ₐ[F] E) (n : ℕ) (S T U : HermR R σ n) :
    pairHerm R σ n S (T + U) = pairHerm R σ n S T + pairHerm R σ n S U := by
  simp only [pairHerm, AddSubgroup.coe_add, Matrix.add_apply, mul_add, Finset.sum_add_distrib,
    map_add]

end Alg

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]

theorem continuous_BR_left (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin n → Fin M → R ⊗[F] E) : Continuous fun X => BR R σ J X Y := by
  have h : ∀ a : Fin n, Continuous fun X : Fin n → Fin M → R ⊗[F] E =>
      Algebra.trace R (R ⊗[F] E) (hR R σ J (X a) (Y a)) := by
    intro a
    have h0 : Continuous fun X : Fin n → Fin M → R ⊗[F] E => (X a, Y a) :=
      (continuous_apply a).prodMk (continuous_const (y := Y a))
    have hc := continuous_hR R σ J
    have h1 := Continuous.comp (g := fun q : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E) =>
      hR R σ J q.1 q.2) hc h0
    have h2 : Continuous fun z : R ⊗[F] E => Algebra.trace R (R ⊗[F] E) z := continuous_trace_tens R
    exact h2.comp h1
  exact continuous_finsetSum Finset.univ fun a _ => h a

theorem continuous_pairHerm_left (σ : E →ₐ[F] E) (n : ℕ) (T : HermR R σ n) :
    Continuous fun S : HermR R σ n => pairHerm R σ n S T := by
  show Continuous fun S : HermR R σ n => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
    (∑ a, ∑ b, (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a b * (T : Matrix (Fin n) (Fin n) _) b a)
  refine continuous_const.mul ((continuous_trace_tens R).comp ?_)
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact (Continuous.matrix_elem continuous_subtype_val a b).mul continuous_const

end Top

theorem continuous_psiInf' {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : Continuous ψ) : Continuous (psiInf F ψ) := by
  have : Continuous fun x : Ainf F => ((x, (0 : Af F)) : Ainf F × Af F) :=
    continuous_id.prodMk continuous_const
  exact hψ.comp this

theorem testEx_coord {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
    {n : ℕ} (e : V ≃ₜ (Fin n → ℝ)) (he : ∀ x y, e (x + y) = e x + e y)
    (hL : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (hR : ∀ x y y', χ x (y + y') = χ x y * χ x y')
    (hn : ∀ x y, ‖χ x y‖ = 1) (hcL : ∀ y, Continuous fun x => χ x y)
    (hcR : ∀ x, Continuous (χ x)) : TestEx μ χ := by
  let L := (EuclideanSpace.equiv (Fin n) ℝ).symm
  refine testEx_of_homeo μ χ (e.trans L.toHomeomorph) (fun x y => ?_) hL hR hn hcL hcR
  show L (e (x + y)) = L (e x) + L (e y)
  rw [he, map_add (f := _)]

end Adelic

end SdTestInfW

open scoped TensorProduct
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation PI.VolFromSW SdUniqW SdTestInfW

theorem sdTestInf_holds : SdTestInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨n, m, eV, eH, hV, hH⟩ := tensR_holds F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet
  have : SecondCountableTopology (HermR (Ainf F) σ a) :=
    have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) :=
      inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Ainf F ⊗[F] E))
    Topology.IsInducing.subtypeVal.secondCountableTopology
  have hpc := continuous_psiInf' ψ hψ.1
  have hpn : ∀ r, ‖psiInf F ψ r‖ = 1 := fun r => hψ.2.1 _
  refine ⟨fun μ hμ => ?_, fun ν hν => ?_⟩
  · have := hμ.1
    exact testEx_coord μ _ eV hV (fun X X' Y => by rw [BR_add, psiInf_add])
      (fun X Y Y' => by rw [BR_add_right', psiInf_add]) (fun X Y => hpn _)
      (fun Y => hpc.comp (continuous_BR_left (Ainf F) σ J Y))
      (fun X => hpc.comp (continuous_BR_right (Ainf F) σ J X))
  · have := hν.1
    exact testEx_coord ν _ eH hH (fun S S' T => by rw [pairHerm_add, psiInf_add])
      (fun S T T' => by rw [pairHerm_add_right', psiInf_add]) (fun S T => hpn _)
      (fun T => hpc.comp (continuous_pairHerm_left (Ainf F) σ a T))
      (fun S => hpc.comp (continuous_pairHerm_right (Ainf F) σ a S))

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabOrb
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabFin
noncomputable section

namespace PI.VolStabS

theorem exStab_of_orb (hO : OrbTup) (hI : NuInv) (hF : NuFin) (hN : NuNeZero) : ExStab :=
  exStab_of_U secCtblW_holds lcscPolish_holds hO hI hF hN

end PI.VolStabS
end
end

namespace PI.VolStabS

theorem exStab_of_nu (hI : NuInv) (hF : NuFin) (hN : NuNeZero) : ExStab :=
  exStab_of_orb orbTup_holds hI hF hN

end PI.VolStabS
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExFDStabFin
namespace PI.VolStabS

theorem discHF_holds : DiscHF :=
  discHF_of_discHA (PI.VolSemiDirect.W.discHA_of PI.VolSemiDirect.W.Lc.tensor_adele_topology_holds)

theorem exFDStab_holds : ExFDStab := exFDStab_of scha_holds discHF_holds

end PI.VolStabS
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.VolStabFromSWOf
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem volStabFromSW_of (h1 : ExChar) (h2 : ExOmT) (h3 : ExStab) (h4 : ExFDStab)
    (h5 : SWeqOm) (h6 : Unfold) (h7 : PosTest) : PI.VolStabS.VolStabFromSWS := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc hJ' a ha1 ha2 X0 hT hdet
  refine ⟨h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet, fun ψ hψ => ?_⟩
  refine ⟨ha.1, fun μ hμ => ?_⟩
  refine ⟨h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ, fun νX hν => ?_⟩
  refine ⟨h3 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν, fun μ' hμ' => ?_⟩
  obtain ⟨hμ'H, hμ'C⟩ := hμ'
  refine ⟨(ha.2 μ hμ).1, fun 𝓕 h𝓕 => ?_⟩
  refine ⟨h4 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ' hμ'H, fun 𝓕' h𝓕' => ?_⟩
  obtain ⟨φ, hφ0, hadm, hI⟩ := h7 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν μ' hμ'H hμ'C
  have e1 := h5 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν _ hadm
  unfold meanC at e1
  have hθ : ∫ h in 𝓕, thetaS F E σ M J (fun X => (φ X : ℂ))
      {X | gramE σ J X = gramE σ J X0} h ∂μ ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at e1
    exact hI e1.symm
  obtain ⟨hfin, e2⟩ :=
    h6 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν μ' hμ'H hμ'C 𝓕' h𝓕'
      φ hφ0 hadm.adm hθ
  rw [e2, smul_smul] at e1
  have hc1 : (μ 𝓕).toReal⁻¹ * (μ' 𝓕').toReal = 1 := by
    have e3 : ((((μ 𝓕).toReal⁻¹ * (μ' 𝓕').toReal : ℝ)) : ℂ) * ∫ X, (φ X : ℂ) ∂νX =
        1 * ∫ X, (φ X : ℂ) ∂νX := by
      rw [one_mul, ← Complex.real_smul]
      exact e1
    exact_mod_cast mul_right_cancel₀ hI e3
  have h0 : (μ 𝓕).toReal ≠ 0 := by
    intro h0
    rw [h0, inv_zero, zero_mul] at hc1
    exact zero_ne_one hc1
  have e4 : (μ 𝓕).toReal = (μ' 𝓕').toReal := (inv_mul_eq_one₀ h0).1 hc1
  exact (ENNReal.toReal_eq_toReal_iff' hfin ((ha.2 μ hμ).2 𝓕 h𝓕).ne).1 e4.symm

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExChar
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem exChar_holds : ExChar := by
  intro F E _ _ _ _ _ σ hE M J _hJ _ha hc a _ha1 ha2 _X0 _hT _hdet
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)
  let b := Module.finBasis F E
  have h0 : 2 * 0 < M := by omega
  have hrd : RapidDecay b (fun _ : Fin 0 → Fin M → Ainf F ⊗[F] E => (1 : ℂ)) :=
    fun N => ⟨1, fun X => by simp [sizeTup]⟩
  have hpf : IsPureFin b (fun _ : Fin 0 → Fin M → Af F ⊗[F] E => (1 : ℂ))
      (fun v (_ : Fin 0 → Fin M → Fv F v ⊗[F] E) => (1 : ℂ)) := by
    refine ⟨fun v => ⟨IsLocallyConstant.const 1, ?_⟩, Filter.Eventually.of_forall fun v => ?_,
      fun X => by simp⟩
    · exact (Set.subsingleton_of_subsingleton).isCompact
    · funext X
      simp [latV, Set.indicator]
  have hS := hc 0 h0 (0 : Matrix (Fin 0) (Fin 0) E) (fun i => Fin.elim0 i) (by simp)
    (Module.finrank F E) b (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ _ => 1)
    continuous_const hrd (Formalism.L2.SG.Pf.NcWeil.isSmoothCc_empty _) hpf (fun _ => by simp)
  obtain ⟨μ, hμ⟩ := hS.1
  obtain ⟨𝓕, h𝓕⟩ := (hS.2 μ hμ).1
  exact ((hS.2 μ hμ).2 𝓕 h𝓕).1

end PI.VolStabS
end
end

namespace PI.VolStabS.Assembly

open PI.VolStabS

theorem fibPin_closed : FibPin := fibPin_holds

theorem sWeqOm_closed : SWeqOm := sWeqOm_of densFibInf_holds densFibV_holds

theorem sdUniq_closed : SdUniq :=
  sdUniq_of_inf sdTestInf_holds

theorem exOmT_holds : ExOmT :=
  exOmT_of_open (fibInfEx_of DiscreteGroups.fibOfDens_holds tensAll_holds densInf_holds)
    (fibVEx_of DiscreteGroups.fibOfDens_holds tensAll_holds densV_holds) sdUniq_closed restrProd_holds

theorem nuInv_holds : NuInv := nuInv_of_pin detAdm_holds compG_holds fibPin_closed sdUniq_closed

theorem volStabFromSW_of_nuNe (hN : NuNeZero) : PI.VolStabS.VolStabFromSWS := volStabFromSW_of exChar_holds exOmT_holds (exStab_of_nu nuInv_holds nuFin_holds hN)
    exFDStab_holds sWeqOm_closed unfold_holds posTest_holds

theorem volStabFromSW_of_open_dens (hDA : DensAA) : PI.VolStabS.VolStabFromSWS := volStabFromSW_of_nuNe (nuNeZero_of_dens archPos_holds locPos_holds hDA qvSum_holds)

theorem volStabFromSW_of_open_aa (hV : VolAA) (hH : HensAA) (hI : IdxH) (hC : CntAA) :
    PI.VolStabS.VolStabFromSWS := volStabFromSW_of_open_dens (densAA_of_open hV hH hI hC)

theorem volStabFromSW_of_open_vic (hV : VolAA) (hI : IdxH) (hC : CntAA) :
    PI.VolStabS.VolStabFromSWS := volStabFromSW_of_open_aa hV hensAA_holds hI hC

theorem volStabFromSW_of_open_ic (hI : IdxH) (hC : CntAA) : PI.VolStabS.VolStabFromSWS := volStabFromSW_of_open_vic volAA_holds hI hC

theorem volStabFromSW_of_cntAA (hC : CntAA) : PI.VolStabS.VolStabFromSWS := volStabFromSW_of_open_ic idxH_holds hC

theorem volStabFromSW_holds : PI.VolStabS.VolStabFromSWS := volStabFromSW_of_cntAA cntAA_holds

end PI.VolStabS.Assembly

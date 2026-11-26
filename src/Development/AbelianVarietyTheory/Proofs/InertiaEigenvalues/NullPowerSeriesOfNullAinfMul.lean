module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratPeriodMatrixExistsFixedFrobeniusSolution
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFacts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionLawsOfRootsOfUnity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NullPowerSeriesOfNullAinfMul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinMemIdealPowOfXPowMulMem
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinMemIdealPowOfXPowMulMem
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP.BK

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem X_pow_natDegree_mem_lE (bk : BK K) : (X : bk.S) ^ bk.Ep.natDegree ∈ bk.J := by
  have hdvd : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i bk.Ep.natDegree with h | h | h
    · rw [if_neg h.ne, sub_zero]; exact bk.dvd_coeff i h
    · subst h; rw [if_pos rfl, bk.monic.coeff_natDegree, sub_self]; exact dvd_zero _
    · rw [if_neg h.ne', Polynomial.coeff_eq_zero_of_natDegree_lt h, sub_zero]; exact dvd_zero _
  obtain ⟨q, hq⟩ := hdvd
  have h1 := congrArg (fun p : Polynomial (Wq l bk.a) => (p : bk.S)) hq
  simp only [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul,
    Polynomial.coe_C] at h1
  rw [map_natCast] at h1
  have h2 : (X : bk.S) ^ bk.Ep.natDegree = bk.E - (l : bk.S) * (q : bk.S) := by
    linear_combination -h1
  rw [h2]
  exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

theorem E_mem_span_l_X (bk : BK K) : bk.E ∈ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)} := by
  obtain ⟨w, hw⟩ := bk.coeff_zero
  have hc : constantCoeff bk.E = (l : Wq l bk.a) * w := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hw]
  rw [eq_shift_mul_X_add_const bk.E, hc, map_mul, map_natCast]
  exact Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
    (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

end GlobalTheory.BSP.BK

theorem GlobalTheory.BSP.BK.mem_J_pow_of_X_pow_mul_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N : ℕ),
    ∃ n : ℕ, ∀ m : ℕ, ∃ n' : ℕ, ∀ s : bk.S,
      (X : bk.S) ^ m * s ∈ bk.J ^ n' ⊔ Ideal.span {(l : bk.S) ^ n} → s ∈ bk.J ^ N := by
  intro l _ K bk N
  refine ⟨N, fun m => ⟨N + (m + bk.Ep.natDegree * N), fun s hs => ?_⟩⟩
  have hJ : bk.J ≤ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)} :=
    sup_le le_sup_left (Ideal.span_singleton_le_iff_mem _ |>.2 (BK.E_mem_span_l_X bk))
  have h1 : bk.J ^ (N + (m + bk.Ep.natDegree * N)) ≤
      Ideal.span {(l : bk.S) ^ N} ⊔ Ideal.span {(X : bk.S) ^ (m + bk.Ep.natDegree * N)} := by
    refine (Ideal.pow_right_mono hJ _).trans ?_
    have := Ideal.sup_pow_add_le_pow_sup_pow (I := Ideal.span {(l : bk.S)}) (J := Ideal.span {(X : bk.S)})
      (n := N) (m := m + bk.Ep.natDegree * N)
    rwa [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at this
  have hs' := (sup_le h1 le_sup_left : _ ≤ Ideal.span {(l : bk.S) ^ N} ⊔
      Ideal.span {(X : bk.S) ^ (m + bk.Ep.natDegree * N)}) hs
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hs'
  obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  set t := s - (X : bk.S) ^ (bk.Ep.natDegree * N) * g with ht
  have htm : (X : bk.S) ^ m * t = C ((l : Wq l bk.a) ^ N) * h := by
    rw [ht, map_pow, map_natCast, mul_sub, ← hyz]; ring
  have ht' : t = C ((l : Wq l bk.a) ^ N) * PowerSeries.mk (fun k => coeff (k + m) h) := by
    ext k
    have := congrArg (coeff (k + m)) htm
    rw [coeff_X_pow_mul', if_pos (Nat.le_add_left m k), Nat.add_sub_cancel, coeff_C_mul] at this
    rw [this, coeff_C_mul, coeff_mk]
  have hs2 : s = ((X : bk.S) ^ bk.Ep.natDegree) ^ N * g + (l : bk.S) ^ N * PowerSeries.mk (fun k => coeff (k + m) h) := by
    have : s = t + (X : bk.S) ^ (bk.Ep.natDegree * N) * g := by rw [ht]; ring
    rw [this, ht', map_pow, map_natCast, ← pow_mul]; ring
  rw [hs2]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (BK.X_pow_natDegree_mem_lE bk) N))
    (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) N))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinMemIdealPowOfXPowMulMemStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_mem_ideal_pow_of_X_pow_mul_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N : ℕ), ∃ n : ℕ, ∀ m : ℕ, ∃ n' : ℕ, ∀ s : bk.S, (X : bk.S) ^ m * s ∈ bk.J ^ n' ⊔ Ideal.span {(l : bk.S) ^ n} → s ∈ bk.J ^ N := by
  first | exact @GlobalTheory.BSP.BK.mem_J_pow_of_X_pow_mul_mem | exact GlobalTheory.BSP.BK.mem_J_pow_of_X_pow_mul_mem | (intros; apply GlobalTheory.BSP.BK.mem_J_pow_of_X_pow_mul_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NullPowerSeriesOfNullAinfMul
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.NullOverS

theorem topBasis_c_mem_map {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (TB : TopBasis s I ι) (i : ι) (n : ℕ) {x : A} (hx : x ∈ (I ^ n).map s) : TB.c i x ∈ I ^ n := by
  have key : ∀ r : A, TB.c i (r * x) ∈ I ^ n := by
    refine Submodule.span_induction (p := fun x _ => ∀ r : A, TB.c i (r * x) ∈ I ^ n) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, hj, rfl⟩ r
      rw [mul_comm, TB.c_mul]
      exact Ideal.mul_mem_right _ _ hj
    · intro r; simp
    · intro y z _ _ hy hz r
      rw [mul_add, map_add (f := _)]; exact Ideal.add_mem _ (hy r) (hz r)
    · intro a y _ hy r
      rw [smul_eq_mul, ← mul_assoc]; exact hy _
  simpa using key 1

theorem topBasis_c_i₀ {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (TB : TopBasis s I ι) (a : S) : TB.c TB.i₀ (s a) = a := by
  have h := TB.c_mul TB.i₀ a 1
  rw [mul_one, ← TB.b_i₀, TB.c_self, mul_one] at h
  exact h

end GlobalTheory.NullOverS

theorem GlobalTheory.NullOverS.null_of_mul_null : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type)
    (TB : TopBasis bk.ev bk.J ι) (d : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) →
    ∀ (σ : ι → Matrix (Fin d) (Fin d) bk.S),
    (∀ (n : ℕ) (a b : Fin d), {i | (Y * (σ i).map bk.ev) a b ∉ (bk.J ^ n).map bk.ev}.Finite) →
    ∀ (n : ℕ) (a b : Fin d), {i | σ i a b ∉ bk.J ^ n}.Finite := by
  intro l _ K bk ι TB d Y hY σ hσ N a b
  obtain ⟨n, hn⟩ := GlobalTheory.T.breuilKisin_mem_ideal_pow_of_X_pow_mul_mem l K bk N
  have hdet : IsUnit (inclW l Y.det) := by
    rw [RingHom.map_det]; exact (Matrix.isUnit_iff_isUnit_det _).1 hY
  obtain ⟨m, t, q, hq⟩ := GlobalTheory.T.ainf_unit_bounded_teichmullerFlat_denominators l K bk Y.det hdet n
  obtain ⟨n', hn'⟩ := hn m
  refine (Set.finite_iUnion fun c : Fin d => hσ n' c b).subset ?_
  intro i hi
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hi ⊢
  by_contra hc
  push_neg at hc
  apply hi
  apply hn'
  have h1 : (t • adjugate Y * (Y * (σ i).map bk.ev)) a b = t * Y.det * bk.ev (σ i a b) := by
    rw [← Matrix.mul_assoc, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
  have h2 : bk.ev (X ^ m * σ i a b) = (t • adjugate Y * (Y * (σ i).map bk.ev)) a b -
      bk.ev ((l : bk.S) ^ n) * (q * bk.ev (σ i a b)) := by
    rw [h1, map_mul, map_pow, map_pow, map_natCast]
    linear_combination (-(bk.ev (σ i a b))) * hq
  rw [← GlobalTheory.NullOverS.topBasis_c_i₀ TB (X ^ m * σ i a b), h2, map_sub]
  refine Ideal.sub_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
  · refine GlobalTheory.NullOverS.topBasis_c_mem_map TB _ _ ?_
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_left _ _ (hc c)
  · rw [TB.c_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NullPowerSeriesOfNullAinfMulStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.null_powerSeries_of_null_ainf_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type) (TB : TopBasis bk.ev bk.J ι) (d : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) → ∀ (σ : ι → Matrix (Fin d) (Fin d) bk.S), (∀ (n : ℕ) (a b : Fin d), {i | (Y * (σ i).map bk.ev) a b ∉ (bk.J ^ n).map bk.ev}.Finite) → ∀ (n : ℕ) (a b : Fin d), {i | σ i a b ∉ bk.J ^ n}.Finite := by
  first | exact @GlobalTheory.NullOverS.null_of_mul_null | exact GlobalTheory.NullOverS.null_of_mul_null | (intros; apply GlobalTheory.NullOverS.null_of_mul_null <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisPeriodMatrixOverAcris
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisPeriodMatrixOverAcris
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
noncomputable section

namespace GlobalTheory.CrisPeriods

variable {l : ℕ} [Fact l.Prime]

private theorem padicInt_hom_ext (f g : ℤ_[l] →+* Per.Ainf l) (z : ℤ_[l]) : f z = g z := by
  have hH : IsHausdorff (Ideal.span {((l : ℕ) : Per.Ainf l)}) (Per.Ainf l) := inferInstance
  rw [← sub_eq_zero]
  refine hH.haus _ fun n => ?_
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  have hz : z = w * (l : ℤ_[l]) ^ n + (z.appr n : ℤ_[l]) := by rw [hw]; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨f w - g w, ?_⟩
  have hf := congrArg f hz
  have hg := congrArg g hz
  simp only [map_add (f := _), map_mul, map_pow, map_natCast] at hf hg
  rw [hf, hg]
  ring

theorem map_smul_ring {R S : Type} [CommRing R] [CommRing S] {n : Type} (f : R →+* S) (c : R)
    (M : Matrix n n R) : (c • M).map f = f c • M.map f := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply]

theorem exists_lift (C : Core l) (hA : C.AwayT) {d : ℕ} (U : Matrix (Fin d) (Fin d) (Per.Bcris l)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Z : Matrix (Fin d) (Fin d) (Per.Acris l),
      Z.map (algebraMap (Per.Acris l) (Per.Bcris l)) = algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ N • U := by
  haveI : IsLocalization.Away C.t (Per.Bcris l) := hA
  have h : ∀ i j, ∃ k : ℕ, ∃ a : Per.Acris l,
      U i j * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ k = algebraMap (Per.Acris l) (Per.Bcris l) a := by
    intro i j
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers C.t) (U i j)
    obtain ⟨k, hk⟩ := s.2
    refine ⟨k, a, ?_⟩
    have hk' : C.t ^ k = (s : Per.Acris l) := hk
    rw [← map_pow, hk']
    exact hs
  choose k a ha using h
  refine ⟨Finset.univ.sup fun p : Fin d × Fin d => k p.1 p.2, fun N hN =>
    ⟨Matrix.of fun i j => a i j * C.t ^ (N - k i j), ?_⟩⟩
  ext i j
  have hk : k i j ≤ N :=
    le_trans (Finset.le_sup (f := fun p : Fin d × Fin d => k p.1 p.2) (Finset.mem_univ (i, j))) hN
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, ← ha]
  rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hk, mul_comm]

end GlobalTheory.CrisPeriods

namespace GlobalTheory.CrisPeriods

theorem periods_over_Acris : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)), U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) → ∀ (c₁ : ℕ) (F : Matrix (Fin d) (Fin d) (Wq l bk.a)), (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (X X' : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, (U.map C.ι * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j ∈ Per.FilD l N) → (∀ i j, (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U'.map C.ι) i j ∈ Per.FilD l N) → ∃ Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l), Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), C.t ^ N • ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • Z) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) := by
  intro l _ K P AI T C _hFits bk d ρ U U' hUU' hgal c₁ F hφ
  have hA := (GlobalTheory.MemLoc.AwayT.away_and_inj l C).1
  obtain ⟨_, _, -, -, -, hFilt, -⟩ := GlobalTheory.MemLoc.BdRDVR.core_dvr l C
  obtain ⟨-, hmul, -, hiff, -, -, hinj⟩ := GlobalTheory.T.bdR_filtration_ker_theta_generator_facts l C (xi C.ε) C.ker_theta.symm
  have AL := GlobalTheory.MemLoc.ActLaws.act_laws l
  obtain ⟨N₁, h₁⟩ := exists_lift C hA U
  obtain ⟨N₂, h₂⟩ := exists_lift C hA U'
  refine ⟨max N₁ N₂, fun N hN X X' hX hX' => ?_⟩
  obtain ⟨Z, hZ⟩ := h₁ N (le_of_max_le_left hN)
  obtain ⟨Z', hZ'⟩ := h₂ N (le_of_max_le_right hN)
  have hmi : Function.Injective
      (fun M : Matrix (Fin d) (Fin d) (Per.Acris l) => M.map (algebraMap (Per.Acris l) (Per.Bcris l))) :=
    Matrix.map_injective hinj
  have hXm : ∀ Y : Matrix (Fin d) (Fin d) bk.S,
      ((Y.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (algebraMap (Per.Acris l) (Per.Bcris l))).map C.ι =
        Y.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) := by
    intro Y
    ext i j
    simp only [Matrix.map_apply, RingHom.comp_apply]
    rw [C.ι_j]
    congr 1
    exact (congrArg C.j (GlobalTheory.RingIface.tower l (bk.ev (Y i j)))).trans
      ((C.j_cris.on0 _).trans (congrArg _ (Subalgebra.coe_algebraMap _ _)))
  have htN : C.ι (algebraMap (Per.Acris l) (Per.Bcris l) C.t) ^ N ∈ Per.FilD l N := by
    rw [C.ι_j, ← map_pow, hiff, hFilt]
    exact Ideal.mem_span_singleton_self _
  refine ⟨Z, Z', ?_, ?_, ?_, ?_, ?_⟩
  · apply hmi
    simp only
    rw [Matrix.map_mul, hZ, hZ', map_smul_ring, Matrix.map_one _ (map_zero _) (map_one _), smul_mul_smul_comm,
      hUU', map_pow, ← pow_add, two_mul]
  · apply hmi
    simp only
    have hZφ : (Z.map (phiA l)).map (algebraMap (Per.Acris l) (Per.Bcris l)) =
        (Z.map (algebraMap (Per.Acris l) (Per.Bcris l))).map (Per.φB l) := by
      ext i j
      exact (AL.2.2.2.2.2.2.2.2.2.2.2.2 (Z i j)).symm
    have hFm : (F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)).map
        (algebraMap (Per.Acris l) (Per.Bcris l)) = F.map ((Per.aB l).comp (wA l bk.a).toRingHom) := by
      ext i j
      simp only [Matrix.map_apply, RingHom.comp_apply, bk.ev_C]
      exact (GlobalTheory.RingIface.aB_eq_alg l _).symm
    have ht : algebraMap (Per.Acris l) (Per.Bcris l) (phiA l C.t) =
        Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) C.t) :=
      (AL.2.2.2.2.2.2.2.2.2.2.2.2 C.t).symm
    rw [map_smul_ring, hZφ, hZ, map_smul_ring, map_smul_ring, Matrix.map_mul, hFm, hZ, map_pow, map_pow, ht,
      Matrix.smul_mul, ← hφ]
    simp only [map_mul, map_pow, map_natCast, smul_smul]
    congr 1
    ring
  · intro g
    apply hmi
    simp only
    have hZσ : (Z.map (sigA (g : GQ l))).map (algebraMap (Per.Acris l) (Per.Bcris l)) =
        (Z.map (algebraMap (Per.Acris l) (Per.Bcris l))).map (Per.σB (g : GQ l)) := by
      ext i j
      exact (AL.2.2.2.2.2.2.2.2.2.2.2.1 _ (Z i j)).symm
    have hρ : ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l)))).map
        (algebraMap (Per.Acris l) (Per.Bcris l)) = (ρ g).map (Per.zB l) := by
      ext i j
      simp only [Matrix.map_apply, RingHom.comp_apply]
      rw [GlobalTheory.RingIface.zB_eq_aB_zA, GlobalTheory.RingIface.aB_eq_alg, padicInt_hom_ext (Per.zA l) (algebraMap ℤ_[l] (Ainf l))]
    have ht : algebraMap (Per.Acris l) (Per.Bcris l) (sigA (g : GQ l) C.t) =
        Per.σB (g : GQ l) (algebraMap (Per.Acris l) (Per.Bcris l) C.t) :=
      (AL.2.2.2.2.2.2.2.2.2.2.2.1 _ C.t).symm
    rw [map_smul_ring, Matrix.map_mul, hρ, hZσ, hZ, map_smul_ring, map_smul_ring, hZ]
    simp only [map_pow, ht]
    rw [Matrix.mul_smul, hgal, smul_smul, smul_smul, mul_comm]
  · intro i j
    rw [← hiff, ← C.ι_j]
    have e : algebraMap (Per.Acris l) (Per.Bcris l) ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) =
        ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (algebraMap (Per.Acris l) (Per.Bcris l))) i j :=
      rfl
    rw [e, Matrix.map_mul, hZ, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
    have e2 : C.ι ((U * (X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map
        (algebraMap (Per.Acris l) (Per.Bcris l))) i j) =
        (U.map C.ι * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j := by
      rw [← hXm]
      exact congrFun (congrFun (Matrix.map_mul (f := C.ι)) i) j
    rw [e2, show ((2 * N : ℕ) : ℤ) = (N : ℤ) + (N : ℤ) by push_cast; ring]
    exact hmul _ _ _ _ htN (hX i j)
  · intro i j
    rw [← hiff, ← C.ι_j]
    have e : algebraMap (Per.Acris l) (Per.Bcris l) ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) =
        ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z').map (algebraMap (Per.Acris l) (Per.Bcris l))) i j :=
      rfl
    rw [e, Matrix.map_mul, hZ', Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
    have e2 : C.ι (((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map
        (algebraMap (Per.Acris l) (Per.Bcris l)) * U') i j) =
        (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U'.map C.ι) i j := by
      rw [← hXm]
      exact congrFun (congrFun (Matrix.map_mul (f := C.ι)) i) j
    rw [e2, show ((2 * N : ℕ) : ℤ) = (N : ℤ) + (N : ℤ) by push_cast; ring]
    exact hmul _ _ _ _ htN (hX' i j)

end GlobalTheory.CrisPeriods
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisPeriodMatrixOverAcrisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcris_periodMatrix_over_acris : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)), U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) → ∀ (c₁ : ℕ) (F : Matrix (Fin d) (Fin d) (Wq l bk.a)), (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (X X' : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, (U.map C.ι * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j ∈ Per.FilD l N) → (∀ i j, (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U'.map C.ι) i j ∈ Per.FilD l N) → ∃ Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l), Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), C.t ^ N • ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • Z) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) := by
  first | exact @GlobalTheory.CrisPeriods.periods_over_Acris | exact GlobalTheory.CrisPeriods.periods_over_Acris | (intros; apply GlobalTheory.CrisPeriods.periods_over_Acris <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapConstantCoeffEqOne
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.WachMat

section Series

open PowerSeries

variable {L : Type} [Field L] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem constantCoeff_rescale' (u : L) (f : L⟦X⟧) : constantCoeff (rescale u f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul, coeff_zero_eq_constantCoeff_apply]

theorem X_pow_dvd_rescale (u : L) (f : L⟦X⟧) (a : ℕ) (h : X ^ a ∣ f) : X ^ a ∣ rescale u f := by
  rw [X_pow_dvd_iff] at h ⊢
  intro m hm
  rw [coeff_rescale, h m hm, mul_zero]

theorem map_constantCoeff_eq_one (G : Matrix ι ι L⟦X⟧) (hG : ∀ i j, X ∣ (G - 1) i j) :
    G.map (constantCoeff (R := L)) = 1 := by
  ext i j
  have := X_dvd_iff.1 (hG i j)
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem X_pow_dvd_of_rescale (u : L) (hu0 : u ≠ 0) (hu : ∀ n : ℕ, n ≠ 0 → u ^ n ≠ 1) (w : L⟦X⟧) (hw : IsUnit w)
    (a : ℕ) (B G G₁ : Matrix ι ι L⟦X⟧) (hG : ∀ i j, X ∣ (G - 1) i j) (hG₁ : ∀ i j, X ∣ (G₁ - 1) i j)
    (h : (X * w) ^ a • (G * B.map (rescale u)) = (rescale u (X * w)) ^ a • (B * G₁)) :
    ∀ i j, X ^ a ∣ B i j := by
  have key : ∀ k, k ≤ a → ∀ i j, X ^ k ∣ B i j := by
    intro k
    induction k with
    | zero => intro _ i j; simp
    | succ k ih =>
      intro hk i j
      choose B' hB' using ih (by omega)
      have hB : B = (X : L⟦X⟧) ^ k • Matrix.of B' := by
        ext1 i j; rw [hB']; rfl
      have hBu : B.map (rescale u) = ((C u) ^ k * (X : L⟦X⟧) ^ k) • (Matrix.of B').map (rescale u) := by
        ext1 i j
        rw [Matrix.map_apply, hB', map_mul, map_pow, rescale_X, mul_pow]; rfl
      rw [hBu] at h
      rw [hB] at h
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, map_mul, rescale_X] at h
      have h1 := congrFun (congrFun h i) j
      simp only [Matrix.smul_apply, smul_eq_mul] at h1
      have h2 : w ^ a * C u ^ k * (G * (Matrix.of B').map (rescale u)) i j
          = C u ^ a * rescale u w ^ a * (Matrix.of B' * G₁) i j := by
        apply mul_left_cancel₀ (pow_ne_zero (a + k) (X_ne_zero (R := L)))
        linear_combination h1
      have h3 := congrArg (constantCoeff (R := L)) h2
      have e1 : constantCoeff ((G * (Matrix.of B').map (rescale u)) i j) = constantCoeff (B' i j) := by
        rw [← Matrix.map_apply (f := constantCoeff (R := L)), Matrix.map_mul, map_constantCoeff_eq_one G hG,
          Matrix.one_mul, Matrix.map_apply, Matrix.map_apply, constantCoeff_rescale']
        rfl
      have e2 : constantCoeff ((Matrix.of B' * G₁) i j) = constantCoeff (B' i j) := by
        rw [← Matrix.map_apply (f := constantCoeff (R := L)), Matrix.map_mul, map_constantCoeff_eq_one G₁ hG₁,
          Matrix.mul_one, Matrix.map_apply]
        rfl
      simp only [map_mul, map_pow, constantCoeff_C, constantCoeff_rescale', e1, e2] at h3
      have hw0 : constantCoeff w ≠ 0 := (isUnit_iff_constantCoeff.1 hw).ne_zero
      obtain ⟨d, rfl⟩ : ∃ d, a = k + (d + 1) := ⟨a - (k + 1), by omega⟩
      have h4 : (constantCoeff w ^ (k + (d + 1)) * u ^ k * (u ^ (d + 1) - 1)) * constantCoeff (B' i j) = 0 := by
        linear_combination -h3
      have h5 : constantCoeff (B' i j) = 0 :=
        (mul_eq_zero.1 h4).resolve_left (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hw0) (pow_ne_zero _ hu0))
          (sub_ne_zero.2 (hu _ (by omega))))
      rw [hB', pow_succ]
      exact mul_dvd_mul_left _ (X_dvd_iff.2 h5)
  exact key a le_rfl

end Series

theorem pow_smul_eq {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (Q : R) (m m' : ℕ)
    (B B' Pm P₁ P₁' : Matrix ι ι R) (h1 : P₁ * P₁' = (Q ^ m') • (1 : Matrix ι ι R))
    (h2 : Pm * B' = (Q ^ m) • (B * P₁)) : Q ^ (m + m') • B = Pm * B' * P₁' := by
  rw [h2, Matrix.smul_mul, Matrix.mul_assoc, h1, Matrix.mul_smul, Matrix.mul_one, smul_smul, pow_add]

theorem dvd_map_of_pow_smul_eq {R S ι : Type} [CommRing R] [CommRing S] [Fintype ι] (f : R →+* S) (Q : R)
    (hQ : IsUnit (f Q)) (m : ℕ) (B B' Pm P₁' : Matrix ι ι R) (h : Q ^ m • B = Pm * B' * P₁') (x : S)
    (hx : ∀ i j, x ∣ f (B' i j)) (i j : ι) : x ∣ f (B i j) := by
  have h1 := congrArg f (congrFun (congrFun h i) j)
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow] at h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (hQ.pow m).dvd_mul_left, h1, Matrix.mul_apply, map_sum]
  refine Finset.dvd_sum fun k _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, Matrix.mul_apply, map_sum]
  refine Dvd.dvd.mul_right (Finset.dvd_sum fun k' _ => ?_) _
  rw [map_mul]
  exact (hx _ _).mul_left _


set_option maxHeartbeats 1600000 in
theorem X_pow_dvd_entry : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (r a m m' : ℕ) (B G G₁ Pm P₁ P₁' : Matrix (Fin r) (Fin r) (AA K LL)), (∀ i j, (G - 1) i j ∈ Ideal.span {(letπ : AA K LL)}) → (∀ i j, (G₁ - 1) i j ∈ Ideal.span {(letπ : AA K LL)}) → (W.X ^ a) • (G * B.map (W.γA W.gam)) = (W.γA W.gam W.X ^ a) • (B * G₁) → P₁ * P₁' = (W.Q ^ m') • (1 : Matrix (Fin r) (Fin r) (AA K LL)) → Pm * B.map W.φA = (W.Q ^ m) • (B * P₁) → ∀ i j, W.X ^ a ∣ B i j := by
  intro D HW l hl K s LL h W r a m m' B G G₁ Pm P₁ P₁' hG hG₁ hγ hP hφ
  obtain ⟨Lγ, Lφ⟩ : LevLaws W := GlobalTheory.NL.Expansion.levLaws D HW l K s LL h
  have Lp := GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h
  obtain ⟨χ, hχ, -, -, -, -, hgam, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  obtain ⟨-, Wd, -⟩ := GlobalTheory.NL.WDiv.weierstrass_dense D HW l K s LL h
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  rw [hp] at Lγ Lφ
  have hroot : ∀ (j : ℕ) (ζ : ↥LL.1), ζ ^ (l ^ j) = 1 → ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := by
    intro j ζ h1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl.out).1 (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨k, hk ▸ IsPrimitiveRoot.orderOf ζ⟩
  set u : ↥LL.1 := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)) with hudef
  have hu0 : u ≠ 0 := ((W.χΓ W.gam).isUnit.map (algebraMap ↥(OL LL) ↥LL.1)).ne_zero
  have hu : ∀ n : ℕ, n ≠ 0 → u ^ n ≠ 1 := by
    intro n hn h1
    have h2 := GlobalTheory.Cyc.norm_unit_zpow_sub_one l s (χ W.gam) h.1 h.2.1 hgam n (by exact_mod_cast hn)
    have h3 : ((χ W.gam : ℤ_[l]ˣ) : ℤ_[l]) ^ n = 1 := by
      have inj : Function.Injective (algebraMap ℤ_[l] ↥LL.1) := by
        rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]
        exact (algebraMap ℚ_[l] ↥LL.1).injective.comp Subtype.val_injective
      apply inj
      rw [map_pow, map_one, IsScalarTower.algebraMap_apply ℤ_[l] ↥(OL LL) ↥LL.1, hχ]
      exact h1
    rw [zpow_natCast, Units.val_pow_eq_pow_val, h3, sub_self, norm_zero] at h2
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
    refine mul_ne_zero (zpow_pos hl0 _).ne' (norm_ne_zero_iff.2 ?_) h2.symm
    exact_mod_cast hn
  have base : ∀ (i : Let K) p q, PowerSeries.X ^ a ∣ W.lev i 1 (B p q) := by
    intro i
    have r1 : IsPrimitiveRoot (1 : ↥LL.1) (l ^ 0) := by
      rw [pow_zero]; exact IsPrimitiveRoot.one
    obtain ⟨⟨x, -, hx, w₀, -, hπ⟩, -, hX, -⟩ := Lp i 1 ⟨0, r1⟩
    obtain ⟨⟨w, hw, hX⟩, -⟩ := hX (one_pow _)
    rw [hx, sub_self, map_zero, zero_add] at hπ
    have hγ1 : ∀ f, W.lev i 1 (W.γA W.gam f) = PowerSeries.rescale u (W.lev i 1 f) := by
      refine Lγ W.gam i 1 1 0 1 r1 ?_ (one_pow _).symm
      rw [Nat.cast_one, W.gam_gen]
      exact_mod_cast Nat.zero_le _
    have hone : ∀ G : Matrix (Fin r) (Fin r) (AA K LL), (∀ p q, (G - 1) p q ∈ Ideal.span {(letπ : AA K LL)}) →
        ∀ p q, PowerSeries.X ∣ (G.map (W.lev i 1) - 1) p q := by
      intro G hG p q
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (hG p q)
      have e : (G.map (W.lev i 1) - 1) p q = W.lev i 1 ((G - 1) p q) := by
        rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [e, hc, map_mul, hπ, mul_assoc]
      exact dvd_mul_right _ _
    refine X_pow_dvd_of_rescale u hu0 hu w hw a (B.map (W.lev i 1)) (G.map (W.lev i 1)) (G₁.map (W.lev i 1))
      (hone G hG) (hone G₁ hG₁) ?_
    ext1 p q
    have h1 := congrArg (W.lev i 1) (congrFun (congrFun hγ p) q)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply, map_mul, map_pow, map_sum,
      hγ1] at h1
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply, ← hX]
    exact h1
  have hB := pow_smul_eq W.Q m m' B (B.map W.φA) Pm P₁ P₁' hP hφ
  have step : ∀ j : ℕ, j ≤ s - 1 → ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ j) = 1 → ∀ p q,
      PowerSeries.X ^ a ∣ W.lev i ζ (B p q) := by
    intro j
    induction j with
    | zero =>
      intro _ i ζ hζ
      rw [pow_zero, pow_one] at hζ
      subst hζ
      exact base i
    | succ j ih =>
      intro hj i ζ hζ
      have hr := hroot _ ζ hζ
      have hζ' : ζ ^ (l ^ (s - 1)) = 1 := by
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
        rw [hd, pow_add, pow_mul, hζ, one_pow]
      obtain ⟨-, -, hX, -⟩ := Lp i ζ hr
      obtain ⟨-, hQ⟩ := hX hζ'
      refine dvd_map_of_pow_smul_eq (W.lev i ζ : AA K LL →+* PowerSeries ↥LL.1) W.Q hQ _ B _ Pm P₁' hB _ fun p q => ?_
      change _ ∣ W.lev i ζ (W.φA (B p q))
      rw [Lφ i ζ hr]
      refine X_pow_dvd_rescale _ _ _ (ih (by omega) _ _ ?_ p q)
      rw [← pow_mul, ← pow_succ', hζ]
  intro p q
  refine Wd a (B p q) fun i ζ hζ => ?_
  exact Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 (step _ le_rfl i ζ hζ p q))

end GlobalTheory.NL.WachMat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobStableInertiaThrough
open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

noncomputable section

namespace GlobalTheory

section InertialCharacters

variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem inertialEig_mem_iff (ρ : Representation LL G V) (I : Subgroup G) (a : I →* LLˣ)
    (w : V ⊗[Qp] B) :
    w ∈ PC.Eig ρ I a ↔ w ∈ PC.Dpcris ρ ∧ ∀ g : I, actVB PC.PD ρ (g : G) w = ((a g : LLˣ) : LL) • w := by
  simp [PotCrysData.Eig, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem actVB_one_apply (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    actVB PC.PD ρ 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem inertialEig_inf_iSup_eq_bot (ρ : Representation LL G V) (I : Subgroup G) (b : I →* LLˣ)
    (T : Finset (I →* LLˣ)) (hb : b ∉ T) :
    PC.Eig ρ I b ⊓ (⨆ a ∈ T, PC.Eig ρ I a) = ⊥ := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a0 T' ha0 ih =>
    have hba0 : b ≠ a0 := fun h => hb (h ▸ Finset.mem_insert_self _ _)
    have hbT : b ∉ T' := fun h => hb (Finset.mem_insert_of_mem h)
    have ih' := ih hbT
    obtain ⟨g, hg⟩ : ∃ g : I, b g ≠ a0 g := by
      by_contra h
      push_neg at h
      exact hba0 (MonoidHom.ext h)
    have hne : ((b g : LLˣ) : LL) - ((a0 g : LLˣ) : LL) ≠ 0 := by
      intro h
      exact hg (Units.ext (sub_eq_zero.mp h))
    set f : V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B :=
      actVB PC.PD ρ (g : G) - ((a0 g : LLˣ) : LL) • LinearMap.id with hf
    have hfE : ∀ (a : I →* LLˣ) w, w ∈ PC.Eig ρ I a →
        f w = (((a g : LLˣ) : LL) - ((a0 g : LLˣ) : LL)) • w := by
      intro a w hw
      rw [inertialEig_mem_iff] at hw
      simp [hf, hw.2 g, sub_smul]
    have hmapT : ∀ z ∈ (⨆ a ∈ T', PC.Eig ρ I a), f z ∈ (⨆ a ∈ T', PC.Eig ρ I a) := by
      intro z hz
      have : (⨆ a ∈ T', PC.Eig ρ I a) ≤ (⨆ a ∈ T', PC.Eig ρ I a).comap f := by
        refine iSup₂_le fun a ha w hw => ?_
        rw [Submodule.mem_comap, hfE a w hw]
        exact Submodule.smul_mem _ _ ((le_iSup₂ (f := fun a (_ : a ∈ T') => PC.Eig ρ I a) a ha) hw)
      exact this hz
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxb, hxs⟩ := hx
    rw [Finset.iSup_insert, Submodule.mem_sup] at hxs
    obtain ⟨y, hy, z, hz, rfl⟩ := hxs
    have hfx : f (y + z) = (((b g : LLˣ) : LL) - ((a0 g : LLˣ) : LL)) • (y + z) := hfE b _ hxb
    have hfy : f y = 0 := by rw [hfE a0 y hy, sub_self, zero_smul]
    have hmem : (((b g : LLˣ) : LL) - ((a0 g : LLˣ) : LL)) • (y + z) ∈
        PC.Eig ρ I b ⊓ (⨆ a ∈ T', PC.Eig ρ I a) := by
      refine ⟨Submodule.smul_mem _ _ hxb, ?_⟩
      rw [← hfx, map_add (f := _), hfy, zero_add]
      exact hmapT z hz
    rw [ih'] at hmem
    rw [Submodule.mem_bot] at hmem ⊢
    exact (smul_eq_zero.mp hmem).resolve_left hne

theorem conj_mem_Iner (F : G) (g : G) (hg : g ∈ PC.Iner) : F⁻¹ * g * F ∈ PC.Iner := by
  intro c
  obtain ⟨c', hc'⟩ := PC.stableK₀' F c
  have hg' := hg c'
  have hFinv : PC.PD.actB F⁻¹ (algebraMap K₀' B c') = algebraMap K₀' B c := by
    rw [← hc', ← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply]
  rw [map_mul, map_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hc', hg', hFinv]

def inerConj (F : G) : PC.Iner →* PC.Iner where
  toFun g := ⟨F⁻¹ * (g : G) * F, conj_mem_Iner PC F g g.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_assoc]

theorem exists_frobStable_inertiaThrough {ι : Type} (ρ : ι → Representation LL G V) (F : G)
    (S : Finset (PC.Iner →* LLˣ)) (h1 : 1 ∈ S) (hS : ∀ x, PC.InertiaThrough (ρ x) S) :
    ∃ Sig : Finset (PC.Iner →* LLˣ), Sig ⊆ S ∧ 1 ∈ Sig ∧ FrobStable PC.Iner F Sig ∧
      ∀ x, PC.InertiaThrough (ρ x) Sig := by
  classical
  let Sig : Finset (PC.Iner →* LLˣ) :=
    insert 1 (S.filter (fun a => ∃ x, PC.Eig (ρ x) PC.Iner a ≠ ⊥))
  have hSigS : Sig ⊆ S := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact h1
    · exact (Finset.mem_filter.mp ha).1
  refine ⟨Sig, hSigS, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨1, Finset.mem_insert_self _ _, fun g h _ => by simp⟩
    obtain ⟨haS, x, hx⟩ := Finset.mem_filter.mp ha
    let b : PC.Iner →* LLˣ := a.comp (inerConj PC F)
    refine ⟨b, ?_, ?_⟩
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hx
      rw [inertialEig_mem_iff] at hv
      set u := actVB PC.PD (ρ x) F v with hu
      have huD : u ∈ PC.Dpcris (ρ x) := pc_Dpcris_stable PC (ρ x) F hv.1
      have hu0 : u ≠ 0 := by
        intro h
        apply hv0
        have : actVB PC.PD (ρ x) F⁻¹ u = v := by
          rw [hu, ← pc_actVB_mul, inv_mul_cancel, actVB_one_apply]
        rw [← this, h, map_zero]
      have huE : u ∈ PC.Eig (ρ x) PC.Iner b := by
        rw [inertialEig_mem_iff]
        refine ⟨huD, fun g => ?_⟩
        have e : (g : G) * F = F * (F⁻¹ * (g : G) * F) := by group
        have hc := hv.2 (inerConj PC F g)
        rw [hu, ← pc_actVB_mul, e, pc_actVB_mul]
        change actVB PC.PD (ρ x) F (actVB PC.PD (ρ x) ((inerConj PC F g : PC.Iner) : G) v) = _
        rw [hc, map_smul]
        rfl
      have hbS : b ∈ S := by
        by_contra hbS
        have hbot := inertialEig_inf_iSup_eq_bot PC (ρ x) PC.Iner b S hbS
        apply hu0
        have : u ∈ PC.Eig (ρ x) PC.Iner b ⊓ (⨆ a ∈ S, PC.Eig (ρ x) PC.Iner a) := by
          refine ⟨huE, ?_⟩
          rw [← (hS x).2.2]
          exact huD
        rw [hbot] at this
        exact (Submodule.mem_bot LL).mp this
      apply Finset.mem_insert_of_mem
      refine Finset.mem_filter.mpr ⟨hbS, x, ?_⟩
      intro h
      apply hu0
      have := huE
      rw [h] at this
      exact (Submodule.mem_bot LL).mp this
    · intro g h hh
      change a (inerConj PC F g) = a h
      congr 1
      ext
      exact hh.symm
  · intro x
    refine ⟨?_, ?_, ?_⟩
    · intro a ha g hg
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rfl
      · exact (hS x).1 a (Finset.mem_filter.mp ha).1 g hg
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · simp
      · exact (hS x).2.1 a (Finset.mem_filter.mp ha).1
    · apply le_antisymm
      · rw [(hS x).2.2]
        refine iSup₂_le fun a ha => ?_
        by_cases h0 : PC.Eig (ρ x) PC.Iner a = ⊥
        · rw [h0]; exact bot_le
        · have haSig : a ∈ Sig := Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨ha, x, h0⟩)
          exact le_iSup₂ (f := fun a (_ : a ∈ Sig) => PC.Eig (ρ x) PC.Iner a) a haSig
      · exact iSup₂_le fun a _ => inf_le_left

end InertialCharacters

theorem frobStable_inertial_subset : ∀ {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K] [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {ι : Type} (ρ : ι → Representation LL G V) (F : G) (S : Finset (PC.Iner →* LLˣ)),
    1 ∈ S → (∀ x, PC.InertiaThrough (ρ x) S) →
    ∃ Sig : Finset (PC.Iner →* LLˣ), Sig ⊆ S ∧ 1 ∈ Sig ∧ FrobStable PC.Iner F Sig ∧
      ∀ x, PC.InertiaThrough (ρ x) Sig := by
  intros
  apply exists_frobStable_inertiaThrough <;> assumption

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EcoefQNormLe
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SstPer

variable {l : ℕ} [Fact l.Prime]


variable (l) in
def ecoefQ (k₀ k i : ℕ) : ℚ_[l] := (l : ℚ_[l]) ^ k₀ * ((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹


variable (l) in
def ecoef (k₀ k i : ℕ) : ℤ_[l] :=
  ⟨if ‖ecoefQ l k₀ k i‖ ≤ 1 then ecoefQ l k₀ k i else 0, by
    split_ifs with h
    · exact h
    · simp⟩

def kap (C : Core l) {K : FinExt l} (bk : BK K) {d : ℕ} (k₀ k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a))
    (z : ℤ_[l]) : Matrix (Fin d) (Fin d) (Per.Acris l) :=
  ∑ i ∈ Finset.range d, (algebraMap (Ainf l) (Per.Acris l) (Per.zA l (ecoef l k₀ k i)) *
    (algebraMap (Ainf l) (Per.Acris l) (Per.zA l z) * C.t) ^ i) •
      (Mn.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ^ i

theorem ecoefQ_norm_le {d e m : ℕ} (k : ℕ) (hm : ¬ l ∣ m) (hd : d.factorial = l ^ e * m) {i : ℕ} (hi : i < d) :
    ‖ecoefQ l (e + k * d) k i‖ ≤ 1 := by
  obtain ⟨q, hq⟩ := Nat.factorial_dvd_factorial hi.le
  obtain ⟨r, rfl⟩ : ∃ r, d = i + r := ⟨d - i, by omega⟩
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hm0 : (m : ℚ_[l]) ≠ 0 := by
    rintro h
    exact hm (by rw [Nat.cast_eq_zero.1 h]; exact dvd_zero _)
  have hf0 : (i.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero i)
  have h : (l : ℚ_[l]) ^ e * m = i.factorial * q := by
    exact_mod_cast (hd.symm.trans hq)
  have e1 : ecoefQ l (e + k * (i + r)) k i = (l : ℚ_[l]) ^ (k * r) * q * (m : ℚ_[l])⁻¹ := by
    unfold ecoefQ
    rw [show e + k * (i + r) = e + k * i + k * r by ring]
    field_simp
    rw [pow_add, pow_add]
    linear_combination ((l : ℚ_[l]) ^ (k * i) * (l : ℚ_[l]) ^ (k * r)) * h
  rw [e1, norm_mul, norm_mul, norm_inv, (Padic.norm_natCast_eq_one_iff (p := l)).2 ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hm), inv_one, mul_one]
  have h1 : ‖(l : ℚ_[l]) ^ (k * r)‖ ≤ 1 := by
    rw [norm_pow, Padic.norm_p]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le))
  have h2 : ‖(q : ℚ_[l])‖ ≤ 1 := by exact_mod_cast Padic.norm_int_le_one (q : ℤ)
  calc ‖(l : ℚ_[l]) ^ (k * r)‖ * ‖(q : ℚ_[l])‖ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem ecoef_val {k₀ k i : ℕ} (h : ‖ecoefQ l k₀ k i‖ ≤ 1) :
    ((ecoef l k₀ k i : ℤ_[l]) : ℚ_[l]) = ecoefQ l k₀ k i := by
  show (if ‖ecoefQ l k₀ k i‖ ≤ 1 then ecoefQ l k₀ k i else 0) = _
  rw [if_pos h]

theorem kap_zero (C : Core l) {K : FinExt l} (bk : BK K) {d : ℕ} (k₀ k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) :
    kap C bk k₀ k Mn 0 = (l : Per.Acris l) ^ k₀ • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Subsingleton.elim _ _
  unfold kap
  rw [Finset.sum_eq_single 0]
  · have h0 : ecoef l k₀ k 0 = (l : ℤ_[l]) ^ k₀ := by
      have hn : ‖ecoefQ l k₀ k 0‖ ≤ 1 := by
        simp only [ecoefQ, Nat.factorial_zero, Nat.cast_one, mul_zero, pow_zero, mul_one, inv_one]
        rw [norm_pow, Padic.norm_p]
        exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le))
      apply Subtype.ext
      rw [ecoef_val hn]
      simp [ecoefQ]
    simp [h0]
  · intro i _ hi
    simp [zero_pow hi]
  · intro h
    exact absurd (Finset.mem_range.2 hd) h

end GlobalTheory.SstPer

end
end

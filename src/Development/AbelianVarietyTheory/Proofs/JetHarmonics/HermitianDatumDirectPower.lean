module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorMomentWeighted
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupCayleyRecursion
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowMulEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HermitianDatumDirectPower
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HermitianDatumDirectPower
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
open scoped TensorProduct

namespace GlobalTheory

noncomputable section

def diagEnd {U V : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (e : U ≃ₗ[ℝ] (Fin n → V)) (f : V →ₗ[ℝ] V) : U →ₗ[ℝ] U :=
  e.symm.toLinearMap ∘ₗ (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) ∘ₗ e.toLinearMap

theorem diagEnd_apply {U V : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (e : U ≃ₗ[ℝ] (Fin n → V)) (f : V →ₗ[ℝ] V) (x : U) (i : Fin n) : e (diagEnd e f x) i = f (e x i) := by
  simp [diagEnd]

theorem diagEnd_comp {U V : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (e : U ≃ₗ[ℝ] (Fin n → V)) (f g : V →ₗ[ℝ] V) : diagEnd e f ∘ₗ diagEnd e g = diagEnd e (f ∘ₗ g) := by
  ext x
  apply e.injective
  funext i
  simp [diagEnd_apply]

theorem trace_diagEnd {U V : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
    [Module.Finite ℝ V] {n : ℕ} (e : U ≃ₗ[ℝ] (Fin n → V)) (f : V →ₗ[ℝ] V) :
    LinearMap.trace ℝ U (diagEnd e f) = n * LinearMap.trace ℝ V f := by
  have h1 : diagEnd e f = e.symm.conj (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) := by
    ext x; simp [diagEnd, LinearEquiv.conj_apply]
  have h2 : (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i : (Fin n → V) →ₗ[ℝ] (Fin n → V)) =
      ∑ i, LinearMap.single ℝ (fun _ : Fin n => V) i ∘ₗ (f ∘ₗ LinearMap.proj i) := by
    apply LinearMap.ext; intro x
    funext j
    simp [LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, LinearMap.trace_conj', h2, map_sum]
  have h3 : ∀ i : Fin n, LinearMap.trace ℝ _ (LinearMap.single ℝ (fun _ : Fin n => V) i ∘ₗ (f ∘ₗ LinearMap.proj i)) =
      LinearMap.trace ℝ V f := by
    intro i
    rw [LinearMap.trace_comp_comm']
    congr 1
    ext x; simp
  simp [h3]

def powForm {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (n : ℕ) :
    LinearMap.BilinForm ℤ (Fin n → L) :=
  ∑ i, B.compl₁₂ (LinearMap.proj i) (LinearMap.proj i)

theorem powForm_apply {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (n : ℕ) (x y : Fin n → L) :
    powForm B n x y = ∑ i, B (x i) (y i) := by
  simp [powForm, LinearMap.sum_apply]

theorem powForm_single {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (n : ℕ) (x : Fin n → L)
    (i : Fin n) (y : L) : powForm B n x (Pi.single i y) = B (x i) y := by
  rw [powForm_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · simp

theorem powForm_bijective {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (hB : Function.Bijective B)
    (n : ℕ) : Function.Bijective (powForm B n) := by
  constructor
  · intro x y h
    funext i
    apply hB.1
    ext z
    rw [← powForm_single, ← powForm_single, h]
  · intro φ
    choose x hx using fun i : Fin n => hB.2 (φ ∘ₗ LinearMap.single ℤ (fun _ : Fin n => L) i)
    refine ⟨x, ?_⟩
    apply LinearMap.pi_ext
    intro i z
    rw [powForm_single, hx]
    rfl

theorem powForm_baseChange {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (n : ℕ)
    (x y : ℝ ⊗[ℤ] (Fin n → L)) :
    (powForm B n).baseChange ℝ x y =
      ∑ i, B.baseChange ℝ (TensorProduct.piRight ℤ ℝ ℝ (fun _ : Fin n => L) x i)
        (TensorProduct.piRight ℤ ℝ ℝ (fun _ : Fin n => L) y i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply, ha, hb, Finset.sum_add_distrib]
  | tmul r u =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb, Finset.sum_add_distrib]
    | tmul s v => simp [powForm_apply, Finset.sum_smul, Finset.sum_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def powDatum (D : Datum H) (n : ℕ) : Datum H where
  La := Fin n → D.La
  fin := by haveI := D.fin; infer_instance
  proj := by
    haveI := D.proj
    exact Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := 𝓞 E) (M := fun _ : Fin n => D.La))
  EF := powForm D.EF n
  alt := fun x => by simp [powForm_apply, D.alt]
  unimod := powForm_bijective D.EF D.unimod n
  adj := fun a x y => by simp [powForm_apply, D.adj]
  p := n * D.p
  q := n * D.q
  rank := by
    haveI := D.fin
    haveI := D.proj
    have h1 := (TensorProduct.isBaseChange (𝓞 E) (Fin n → D.La) E).finrank_eq
    have h2 := (TensorProduct.isBaseChange (𝓞 E) D.La E).finrank_eq
    have h3 := (TensorProduct.piRight (𝓞 E) E E (fun _ : Fin n => D.La)).finrank_eq
    rw [← h1, h3, Module.finrank_pi_fintype]
    simp [h2, D.rank, mul_add]
  dom := by
    haveI := D.fin
    haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
    obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
    set e := TensorProduct.piRight ℤ ℝ ℝ (fun _ : Fin n => D.La) with he
    refine ⟨diagEnd e J, ?_, ?_, ?_, ?_⟩
    · intro x
      apply e.injective
      funext i
      simp [diagEnd_apply, h1]
    · intro x y
      simp only [powForm_baseChange, ← he, diagEnd_apply, h2]
    · intro x hx
      simp only [powForm_baseChange, ← he, diagEnd_apply]
      have : ∃ i, e x i ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hx (e.injective (by rw [map_zero]; exact funext hc))
      obtain ⟨i, hi⟩ := this
      refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, h3 _ hi⟩
      by_cases hj : e x j = 0
      · simp [hj]
      · exact (h3 _ hj).le
    · intro a A t hA ht
      let A0 : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La :=
        ((DistribSMul.toAddMonoidHom D.La a).toIntLinearMap).baseChange ℝ
      obtain ⟨k1, k2, k3⟩ := h4 a A0 _ (fun x => by simp [A0]) rfl
      have hAA : A = diagEnd e A0 := by
        apply LinearMap.ext
        intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add a b ha hb => simp only [map_add (f := _), ha, hb]
        | tmul r u =>
          have : r ⊗ₜ[ℤ] u = r • ((1 : ℝ) ⊗ₜ[ℤ] u) := by simp [TensorProduct.smul_tmul']
          rw [this, map_smul, map_smul, hA]
          congr 1
          apply e.injective
          funext i
          simp [diagEnd_apply, he, A0]
      have ht' : t = n * ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
        ((D.p : ℂ) * τ (a : E) + (D.q : ℂ) * starRingEnd ℂ (τ (a : E))) := by
        rw [ht, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        push_cast; ring
      rw [hAA, diagEnd_comp, diagEnd_comp, trace_diagEnd, trace_diagEnd, k1, ← k1, k2, k3, ht']
      refine ⟨rfl, ?_, ?_⟩
      · rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]; ring
      · rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im]; ring

theorem exists_datum_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ),
    ∃ (Dw' : Datum H) (e : Dw'.La ≃ₗ[𝓞 E] (Fin n → Dw.La)),
      (∀ x y, Dw'.EF x y = ∑ i, Dw.EF (e x i) (e y i)) ∧ Dw'.p = n * Dw.p ∧ Dw'.q = n * Dw.q :=
  fun E _ _ _ _ Dw n => ⟨powDatum Dw n, LinearEquiv.refl (𝓞 E) (Fin n → Dw.La),
    fun x y => powForm_apply Dw.EF n x y, rfl, rfl⟩

end
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HermitianDatumDirectPowerStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_datum_direct_power : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ), ∃ (Dw' : Datum H) (e : Dw'.La ≃ₗ[𝓞 E] (Fin n → Dw.La)), (∀ x y, Dw'.EF x y = ∑ i, Dw.EF (e x i) (e y i)) ∧ Dw'.p = n * Dw.p ∧ Dw'.q = n * Dw.q := by
  first | exact @GlobalTheory.exists_datum_pow | exact GlobalTheory.exists_datum_pow | (intros; apply GlobalTheory.exists_datum_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupMomentClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupMomentRecursion
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupMomentRecursion
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomProd

theorem product_moment : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + (r + 1) ^ 2 ≤ q0 → NzOn (R ν) (l ν) → ∃ w ∈ (R ν).sm, ‖w‖ = 1 ∧ ∫⁻ x, ENNReal.ofReal ((∏ a, lenA k r z (Matrix.of x) a ^ 2) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ (r + 1)) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν hnz
  classical
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hNum := hS.1
  have hFam := hS.2.1
  have hSide := hS.2.2.1
  have hSF := hS.2.2.2
  have hk : 1 ≤ k := hNum.1
  have hν0 : n1 ν ≤ q0 := le_trans (Nat.le_add_right _ _) hν
  obtain ⟨Q, hQ⟩ := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).1 hk
  have hQu : IsUnit Q := hQ.1.1
  have hE : ∀ ν', ∃ E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub,
      n1 ν' ≤ q0 → (R ν').IsE Q E ∧ Formalism.REAL.GlRel E := by
    intro ν'
    by_cases h' : n1 ν' ≤ q0
    · obtain ⟨E, hE⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r _ _ (R ν') (hFam ν' h') Q hQu
      exact ⟨E, fun _ => hE⟩
    · exact ⟨fun _ _ => 0, fun h'' => absurd h'' h'⟩
  choose E hE using hE
  have hDS := hFam ν hν0
  obtain ⟨w, hw1, -, hwK, hwF⟩ := GlobalTheory.T.exists_lowest_kFinite_vector_discreteSeries hK k r _ _ (R ν) hDS Q (E ν) hQ (hE ν hν0).1
  have hMod := GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ (R ν) hk hDS Q (E ν) hQ (hE ν hν0).1
  have hLev := GlobalTheory.lev_zero_of_kHighest _ _ _ (E ν) _ w hMod.1 hMod.2.1 hwK hwF
  have hw1' : ‖(w : (R ν).H)‖ = 1 := hw1
  have hwsm : (w : (R ν).H) ∈ (R ν).sm := w.2
  refine ⟨(w : (R ν).H), hwsm, hw1', ?_⟩
  obtain ⟨hG, -, hlen, hmeas⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hSide
  obtain ⟨hBeL, hdg, -⟩ := hSF ν hν0
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := hSide.2.1
  obtain ⟨⟨hb1, hb2, -, -, -⟩, -⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  have hq2 : ∀ q ≤ (r + 1) ^ 2, 0 + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 := by
    intro q hq
    have : (r + 1) ^ 2 ≤ (2 * r + k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hb : (1 : ℝ) ≤ b := by linarith
  have hA : 0 ≤ (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) := by
    have : 0 ≤ bv := by linarith
    positivity
  have hmain := GlobalTheory.T.product_moment_bound_density_mass_one (Formalism.QuantumDeterminants.Mt k r) νq r (fun a x => lenA k r z (Matrix.of x) a)
    (fun x => dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)
    (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) (b ^ 2)
    hlen
    (fun a => hG.mono fun x hx => (GlobalTheory.TensLen.lengths k r z hSide.1 hT _ hx).2.2.1 a)
    (((hmeas (l ν) hBeL.1 w hwsm).norm.aemeasurable.pow_const 2).const_mul _)
    (fun x => mul_nonneg hdg.le (by positivity))
    (by
      have := ((GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν0).2 hnz).2 w hwsm
      simpa only [one_mul, hw1', one_pow, ENNReal.ofReal_one] using this)
    hA (one_le_pow₀ hb)
    (fun q hq => by
      have := GlobalTheory.T.family_setup_cayley_recursion hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE q ν
        (by omega) 0 (hq2 q hq) w hLev
      simpa only [hw1, one_pow, mul_one] using this)
    (fun a q hq => by
      have := GlobalTheory.T.family_setup_cayley_bound hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hν0
        0 q (hq2 q hq) a w hLev
      simpa only [hw1, one_pow, mul_one] using this)
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  exact pow_le_pow_left₀ (mul_nonneg hA (by positivity))
    (GlobalTheory.T.numericalFamily_productBound_constant_le k r lam u b bv ga h q0 _ hNum hT) _

end GlobalTheory.MomProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupMomentRecursionStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_exists_unit_product_moment_le_Hsq_pow : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + (r + 1) ^ 2 ≤ q0 → NzOn (R ν) (l ν) → ∃ w ∈ (R ν).sm, ‖w‖ = 1 ∧ ∫⁻ x, ENNReal.ofReal ((∏ a, lenA k r z (Matrix.of x) a ^ 2) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ (r + 1)) := by
  first | exact @GlobalTheory.MomProd.product_moment | exact GlobalTheory.MomProd.product_moment | (intros; apply GlobalTheory.MomProd.product_moment <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupMomentClosure
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.WedgeKappa

theorem n1_add_eZ_le_add_card {n : ℕ} (ν : Fin n → ℤ) (I : Finset (Fin n)) : n1 (ν + eZ I) ≤ n1 ν + I.card := by
  unfold n1
  have h1 : ∑ i, (eZ I i).natAbs = I.card := by
    have : ∀ i, (eZ I i).natAbs = if i ∈ I then 1 else 0 := by
      intro i; unfold eZ; split_ifs <;> rfl
    simp [this]
  rw [← h1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _

theorem eZ_injective {n : ℕ} : Function.Injective (eZ : Finset (Fin n) → Fin n → ℤ) := by
  intro I J h
  ext i
  have := congrFun h i
  unfold eZ at this
  by_cases hI : i ∈ I <;> by_cases hJ : i ∈ J <;> simp_all

theorem kappa_bound : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + (r + 1) * (r + 2) ≤ q0 → ∀ io pr ep, TensH (cmp (r + 1)) (cmp (r + 1) (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) (r + 1) => R (ν + eZ I.1)) io pr ep → NzOn (R ν) (l ν) → ∀ (I : Sub (2 * r + k + 1) (r + 1)) (κ₀ : ℂ), NzOn (R (ν + eZ I.1)) (l (ν + eZ I.1)) → (∀ v ∈ (R ν).sm, l (ν + eZ I.1) (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec k r z)) v c)) = κ₀ • l ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν + eZ I.1) ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ (r + 1) := by
  intro hyp k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν io pr ep hT hnz I κ₀ hnzI hκ
  classical
  have hS' := hS
  obtain ⟨hNum, hFam, hG, hSF⟩ := hS'
  have hν0 : n1 ν ≤ q0 := by omega
  have hνJ : ∀ J : Sub (2 * r + k + 1) (r + 1), n1 (ν + eZ J.1) + (r + 1) ^ 2 ≤ q0 := by
    intro J
    have := n1_add_eZ_le_add_card ν J.1
    rw [J.2] at this
    nlinarith
  have hνJ0 : ∀ J : Sub (2 * r + k + 1) (r + 1), n1 (ν + eZ J.1) ≤ q0 := fun J =>
    le_trans (Nat.le_add_right _ _) (hνJ J)
  have hDS := hFam ν hν0
  have hDSJ := fun J : Sub (2 * r + k + 1) (r + 1) => hFam (ν + eZ J.1) (hνJ0 J)
  have hF := GlobalTheory.WedgeFRep.isFRep_cmp k r (r + 1)
  have hdual := fun J : Sub (2 * r + k + 1) (r + 1) =>
    GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hyp k r _ _ _ _ _ (R ν) _ io pr ep _ _ _ Wp z π u μW μN μG νq
      (wedge (Formalism.QuantumDeterminants.fvec k r z)) (l ν) hDS hDSJ hF hT hG
      (fun s hs => (GlobalTheory.FlagFix.fixes_wedge_and_form k r z hG.1 s hs).1) (hSF ν hν0).1 hnz J
      (l (ν + eZ J.1)) (hSF _ (hνJ0 J)).1
  have hex : ∀ J : Sub (2 * r + k + 1) (r + 1), ∃ c : ℂ, (J = I → c = κ₀) ∧
      ∀ y ∈ (R (ν + eZ J.1)).sm, l ν (ev (cmp (r + 1) (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (wedge (Formalism.QuantumDeterminants.fvec k r z))
        (fun c => io J c y)) = ((ep J : ℂ) * star c) • l (ν + eZ J.1) y := by
    intro J
    by_cases hJ : J = I
    · subst hJ
      exact ⟨κ₀, fun _ => rfl, (hdual J).2 κ₀ hκ⟩
    · obtain ⟨c, hc⟩ := (hdual J).1
      exact ⟨c, fun h => absurd h hJ, (hdual J).2 c hc⟩
  choose κ hκI hκd using hex
  have hd0 : 0 < dg ν := (hSF ν hν0).2.1
  have hdJ : ∀ J : Sub (2 * r + k + 1) (r + 1), 0 < dg (ν + eZ J.1) := fun J => (hSF _ (hνJ0 J)).2.1
  have hmass := GlobalTheory.T.bessel_functional_l2_bound_and_isometry hyp k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS
  obtain ⟨w, hw, hw1, hint⟩ := GlobalTheory.T.family_exists_unit_product_moment_le_Hsq_pow hyp k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS _ (hνJ I) hnzI
  have hinj : Function.Injective (fun (J : Sub (2 * r + k + 1) (r + 1)) (a : Fin (2 * r + k + 1)) =>
      lam a + (((ν + eZ J.1) a : ℤ) : ℝ)) := by
    intro J J' hJ
    apply Subtype.ext
    apply eZ_injective
    funext a
    have := congrFun hJ a
    simp only [Pi.add_apply, add_right_inj, Int.cast_inj] at this
    exact this
  have h8 := GlobalTheory.T.tensor_moment_weighted hyp k r _ _ _ _ _ (R ν) _ io pr ep _ _ _ Wp z π u μW μN μG νq
    (wedge (Formalism.QuantumDeterminants.fvec k r z)) (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν w)
    (fun J w => ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) • l (ν + eZ J.1) w)
    (fun J => if NzOn (R (ν + eZ J.1)) (l (ν + eZ J.1)) then
      (ep J : ℂ) * star (κ J) * ((Real.sqrt (dg ν) : ℝ) : ℂ) / ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) else 0)
    hDS hDSJ hinj hF hT hG ((hmass ν hν0).2 hnz).1
    (fun J => by
      by_cases hJ : NzOn (R (ν + eZ J.1)) (l (ν + eZ J.1))
      · exact Or.inl ((hmass _ (hνJ0 J)).2 hJ).1
      · exact Or.inr (if_neg hJ))
    (fun J y hy => by
      rw [hκd J y hy]
      by_cases hJ : NzOn (R (ν + eZ J.1)) (l (ν + eZ J.1))
      · rw [if_pos hJ, smul_smul, smul_smul]
        congr 1
        have : ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hdJ J)).ne'
        field_simp
      · have : l (ν + eZ J.1) y = 0 := by
          by_contra hne
          exact hJ ⟨y, hy, hne⟩
        rw [if_neg hJ, this]
        simp)
    I ((hmass _ (hνJ0 I)).2 hnzI).1 w hw
  have hae := (GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hyp.1.2.2.1 k r _ _ (R ν) Wp z π u μW μN μG νq hDS hG).1
  rw [if_pos hnzI, hκI I rfl, hw1] at h8
  have h9 := h8.trans (le_trans (le_of_eq (lintegral_congr_ae ?_)) hint)
  · have hH : 0 ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ (r + 1) := by
      apply pow_nonneg
      unfold Hsq
      apply mul_nonneg (le_trans zero_le_one (le_max_left _ _))
      rw [show 20 * (r + 1) = 2 * (10 * (r + 1)) by ring, pow_mul]
      positivity
    rw [ENNReal.ofReal_le_ofReal_iff hH] at h9
    refine le_trans (le_of_eq ?_) h9
    have hep : ‖(ep I : ℂ)‖ = 1 := by
      rcases hT.ep_sq I with h | h <;> simp [h]
    rw [norm_div, norm_mul, norm_mul, hep, norm_star, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, div_pow, mul_pow, sq_abs, sq_abs, Real.sq_sqrt hd0.le, Real.sq_sqrt (hdJ I).le]
    ring
  · filter_upwards [hae] with x hx
    rw [(GlobalTheory.TensLen.lengths k r z hG.1 hG.2.1 _ hx).1, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, Real.sq_sqrt (hdJ I).le]

end GlobalTheory.WedgeKappa
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupMomentClosureStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wedge_raising_scalar_sq_mul_degree_ratio_le : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + (r + 1) * (r + 2) ≤ q0 → ∀ io pr ep, TensH (cmp (r + 1)) (cmp (r + 1) (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) (r + 1) => R (ν + eZ I.1)) io pr ep → NzOn (R ν) (l ν) → ∀ (I : Sub (2 * r + k + 1) (r + 1)) (κ₀ : ℂ), NzOn (R (ν + eZ I.1)) (l (ν + eZ I.1)) → (∀ v ∈ (R ν).sm, l (ν + eZ I.1) (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec k r z)) v c)) = κ₀ • l ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν + eZ I.1) ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ (r + 1) := by
  first | exact @GlobalTheory.WedgeKappa.kappa_bound | exact GlobalTheory.WedgeKappa.kappa_bound | (intros; apply GlobalTheory.WedgeKappa.kappa_bound <;> assumption)
end
end

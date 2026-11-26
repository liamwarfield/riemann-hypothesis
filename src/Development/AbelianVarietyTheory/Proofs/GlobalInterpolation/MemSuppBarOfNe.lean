module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteQuotDivLatMulLatHomAt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousToZModComp
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegOneZpowRound
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPrimeUnder
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexNeZeroOfSmul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentsCosetSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelDetCompanion
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.ChiMove

open GlobalTheory.CharValCompare GlobalTheory.RelDetIdeal GlobalTheory.IdealTransport

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

omit [StarRing E] in
theorem functional_sum {P : HeightOneSpectrum (𝓞 E)} (M : Submodule (𝓞 E) (Sp E n)) (φ : Sp E n → 𝓞 E ⧸ P.asIdeal)
    (hadd : ∀ x ∈ M, ∀ y ∈ M, φ (x + y) = φ x + φ y)
    (hsm : ∀ (a : 𝓞 E), ∀ x ∈ M, φ (a • x) = Ideal.Quotient.mk P.asIdeal a * φ x)
    {ι : Type} (S : Finset ι) (r : ι → 𝓞 E) (v : ι → Sp E n) (hv : ∀ i, v i ∈ M) :
    φ (∑ i ∈ S, r i • v i) = ∑ i ∈ S, Ideal.Quotient.mk P.asIdeal (r i) * φ (v i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hsm 0 0 M.zero_mem
  | insert k S hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk,
      hadd _ (M.smul_mem _ (hv k)) _ (M.sum_mem fun i _ => M.smul_mem _ (hv i)), hsm _ _ (hv k), ih]

theorem functional_frame {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} {f : Sp E n ≃ₗ[E] Sp E n}
    (hf : IsFr P N f) (φ : Sp E n → 𝓞 E ⧸ P.asIdeal)
    (hadd : ∀ x ∈ localization₂ P.asIdeal N, ∀ y ∈ localization₂ P.asIdeal N, φ (x + y) = φ x + φ y)
    (hsm : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.asIdeal N, φ (a • x) = Ideal.Quotient.mk P.asIdeal a * φ x) :
    ∃ c : Fin n → 𝓞 E, ∀ z ∈ stdAt E n P,
      φ (f z) = 0 ↔ P.valuation E (∑ i, algebraMap (𝓞 E) E (c i) * z i) ≤ WithZero.exp (-1 : ℤ) := by
  classical
  choose c hc using fun i : Fin n => Ideal.Quotient.mk_surjective (φ (f (Pi.single i 1)))
  refine ⟨c, fun z hz => ?_⟩
  obtain ⟨s, hs, hsz⟩ := (mem_locP P _ _).1 hz
  choose r hr using (Formalism.L2.Col.mem_stdLat _).1 hsz
  have h1 : s • f z = ∑ i, r i • f (Pi.single i 1) := by
    rw [← algebraMap_smul E s, ← map_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← algebraMap_smul E (r _), ← map_smul, ← map_sum]
    congr 1
    funext j
    simp [Finset.sum_apply, Pi.single_apply, hr, Algebra.smul_def]
  have h2 : Ideal.Quotient.mk P.asIdeal s * φ (f z) = Ideal.Quotient.mk P.asIdeal (∑ i, r i * c i) := by
    rw [← hsm s _ ((hf z).2 hz), h1, functional_sum _ φ hadd hsm _ _ _ fun i => (hf _).2 (single_mem_stdAt P i)]
    simp [hc]
  have h3 : algebraMap (𝓞 E) E (∑ i, r i * c i) = algebraMap (𝓞 E) E s * ∑ i, algebraMap (𝓞 E) E (c i) * z i := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hr, Pi.smul_apply, Algebra.smul_def]
    ring
  have h4 : P.valuation E (∑ i, algebraMap (𝓞 E) E (c i) * z i) = P.intValuation (∑ i, r i * c i) := by
    have := congrArg (P.valuation E) h3
    rw [Valuation.map_mul, val_of_notMem hs, one_mul, HeightOneSpectrum.valuation_of_algebraMap] at this
    exact this.symm
  have h5 := P.intValuation_le_pow_iff_mem (∑ i, r i * c i) 1
  have h6 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)
  haveI := P.isPrime
  rw [h4, ← mul_eq_zero_iff_left h6, h2, Ideal.Quotient.eq_zero_iff_mem]
  simpa using h5.symm

theorem val_det_ker {P : HeightOneSpectrum (𝓞 E)} {N N'' : Submodule (𝓞 E) (Sp E n)} {f f'' : Sp E n ≃ₗ[E] Sp E n}
    (hf : IsFr P N f) (hf'' : IsFr P N'' f'') (φ : Sp E n → 𝓞 E ⧸ P.asIdeal)
    (hadd : ∀ x ∈ localization₂ P.asIdeal N, ∀ y ∈ localization₂ P.asIdeal N, φ (x + y) = φ x + φ y)
    (hsm : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.asIdeal N, φ (a • x) = Ideal.Quotient.mk P.asIdeal a * φ x)
    (hne : ∃ x ∈ N, φ x ≠ 0) (hker : ∀ y, y ∈ localization₂ P.asIdeal N'' ↔ y ∈ localization₂ P.asIdeal N ∧ φ y = 0) :
    P.valuation E (dt f'' / dt f) = WithZero.exp (-1 : ℤ) := by
  classical
  obtain ⟨c, hc⟩ := functional_frame hf φ hadd hsm
  have hstd : ∀ z : Sp E n, z ∈ stdAt E n P ↔ ∀ i, P.valuation E (z i) ≤ 1 := fun z => by
    rw [stdAt, mem_localization_standardLattice]
    simp only [intAt_iff]
  obtain ⟨j, hj⟩ : ∃ j, c j ∉ P.asIdeal := by
    by_contra H
    push Not at H
    obtain ⟨x, hx, hx0⟩ := hne
    obtain ⟨z, rfl⟩ := f.surjective x
    have hz := (hf z).1 (le_locP P _ hx)
    refine hx0 ((hc z hz).2 (Valuation.map_sum_le _ fun i _ => ?_))
    rw [map_mul, HeightOneSpectrum.valuation_of_algebraMap]
    have := (P.intValuation_le_pow_iff_mem (c i) 1).2 (by simpa using H i)
    exact (mul_le_of_le_one_right' ((hstd z).1 hz i)).trans (by simpa using this)
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hπ0 : π ≠ 0 := by rintro rfl; rw [map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm
  let M : Matrix (Fin n) (Fin n) E := (1 : Matrix (Fin n) (Fin n) E).updateRow j fun i => algebraMap (𝓞 E) E (c i) / π
  have hM : M.det = algebraMap (𝓞 E) E (c j) / π := by
    have := Matrix.det_updateRow_sum (1 : Matrix (Fin n) (Fin n) E) j fun i => algebraMap (𝓞 E) E (c i) / π
    rw [Matrix.det_one, smul_eq_mul, mul_one] at this
    rw [← this]
    refine congrArg (fun v => Matrix.det (Matrix.updateRow 1 j v)) (funext fun k => ?_)
    simp [Finset.sum_apply, Matrix.one_apply]
  have hMj : ∀ z, M.mulVec z j = (∑ i, algebraMap (𝓞 E) E (c i) * z i) / π := fun z => by
    simp only [M, Matrix.mulVec, dotProduct, Matrix.updateRow_self, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hMi : ∀ z i, i ≠ j → M.mulVec z i = z i := fun z i hi => by
    simp [M, Matrix.mulVec, dotProduct, Matrix.updateRow_ne hi, Matrix.one_apply]
  have hle : ∀ a : E, P.valuation E (a / π) ≤ 1 ↔ P.valuation E a ≤ WithZero.exp (-1 : ℤ) := fun a => by
    rw [map_div₀, div_le_one₀ (val_pos hπ0), hπ]
  have key : ∀ z, M.mulVec z ∈ stdAt E n P ↔ f z ∈ localization₂ P.asIdeal N'' := by
    intro z
    rw [hker, hf]
    constructor
    · intro h
      rw [hstd] at h
      have h1 := h j
      rw [hMj, hle] at h1
      have hz : z ∈ stdAt E n P := by
        rw [hstd]
        intro i
        by_cases hi : i = j
        · subst hi
          have h2 : algebraMap (𝓞 E) E (c i) * z i =
              ∑ k, algebraMap (𝓞 E) E (c k) * z k - ∑ k ∈ Finset.univ.erase i, algebraMap (𝓞 E) E (c k) * z k := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; ring
          have h3 : P.valuation E (algebraMap (𝓞 E) E (c i) * z i) ≤ 1 := by
            rw [h2]
            refine Valuation.map_sub_le _ (h1.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega))
              (Valuation.map_sum_le _ fun k hk => ?_)
            rw [map_mul]
            exact mul_le_one' (P.valuation_le_one _) (hMi z k (Finset.ne_of_mem_erase hk) ▸ h k)
          rwa [map_mul, val_of_notMem hj, one_mul] at h3
        · exact hMi z i hi ▸ h i
      exact ⟨hz, (hc z hz).2 h1⟩
    · rintro ⟨hz, h0⟩
      rw [hstd]
      intro i
      by_cases hi : i = j
      · rw [hi, hMj, hle]
        exact (hc z hz).1 h0
      · rw [hMi z i hi]
        exact (hstd z).1 hz i
  have hd : LinearMap.det (Matrix.toLin' M ∘ₗ (f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ (f'' : Sp E n →ₗ[E] Sp E n)) =
      algebraMap (𝓞 E) E (c j) / π * (dt f'' / dt f) := by
    have h3 := LinearEquiv.det_mul_det_symm f
    have h4 := dt_ne f
    rw [LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_toLin', hM, ← dt_eq f'']
    rw [← dt_eq f] at h3
    congr 1
    rw [eq_div_iff h4]
    linear_combination dt f'' * h3
  have hv := val_of_notMem (E := E) hj
  have h0 : LinearMap.det (Matrix.toLin' M ∘ₗ (f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ (f'' : Sp E n →ₗ[E] Sp E n)) ≠ 0 := by
    rw [hd]
    refine mul_ne_zero (div_ne_zero ?_ hπ0) (div_ne_zero (dt_ne _) (dt_ne _))
    intro h
    simp [h] at hv
  have h1 : P.valuation E (algebraMap (𝓞 E) E (c j) / π * (dt f'' / dt f)) = 1 := by
    rw [← hd]
    exact val_det_eq_one (P := P) (LinearMap.equivOfDetNeZero _ h0) fun x => by
      rw [← hf'' x]
      have := key (f.symm (f'' x))
      rw [LinearEquiv.apply_symm_apply] at this
      exact this
  rw [map_mul, map_div₀ _ _ π, hv, hπ, one_div, inv_mul_eq_one₀ WithZero.exp_ne_zero] at h1
  exact h1.symm

omit [StarRing E] in
theorem val_of_simple {P : HeightOneSpectrum (𝓞 E)} {a : 𝓞 E} (h1 : a ∈ P.asIdeal) (h2 : a ∉ P.asIdeal ^ 2) :
    P.valuation E (algebraMap (𝓞 E) E a) = WithZero.exp (-1 : ℤ) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  have h0 : a ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have e1 := (P.intValuation_le_pow_iff_mem a 1).2 (by simpa using h1)
  have e2 := (P.intValuation_le_pow_iff_mem a 2).not.2 h2
  rw [← WithZero.exp_log (P.intValuation_ne_zero a h0), WithZero.exp_le_exp] at e1 e2
  rw [← WithZero.exp_log (P.intValuation_ne_zero a h0)]
  congr 1
  push_cast at e1 e2
  omega

theorem relDet_companion {SG : Finset (HeightOneSpectrum (𝓞 E))} {ϖ : 𝓞 E} (d : DecoSet (E := E) (n := n) (ST := divs ϖ) (SG := SG))
    {N'' : Submodule (𝓞 E) (Sp E n)} (h0 : ϖ ≠ 0) (hcop : IsCoprime ϖ (cO E ϖ)) (hsq : ∀ P ∈ divs ϖ, ϖ ∉ P.asIdeal ^ 2)
    (hN'' : IsSdLat N'') (h1 : ∀ y ∈ d.1.N, (ϖ : E) • y ∈ N'') (h2 : ∀ y ∈ N'', star (ϖ : E) • y ∈ d.1.N)
    (h3 : ∀ (P : ↥(divs ϖ)) (y : Sp E n), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d.1.at P.1 ∧ d.1.f P y = 0) :
    relDet d.1.N N'' = Submodule.span (𝓞 E) {(ϖ : E) / star (ϖ : E)} := by
  have hN : IsSdLat d.1.N := ⟨d.2.lat, d.2.uni⟩
  choose f hf using fun P => exists_isFr P hN
  choose f'' hf'' using fun P => exists_isFr P hN''
  have hϖ : (ϖ : E) ≠ 0 := by simpa using h0
  have hϖ' : star (ϖ : E) ≠ 0 := star_ne_zero.2 hϖ
  have hnot : ∀ P : HeightOneSpectrum (𝓞 E), ϖ ∈ P.asIdeal → cO E ϖ ∉ P.asIdeal := fun P a b => by
    obtain ⟨u, v, e⟩ := hcop
    exact one_notMem P (e ▸ add_mem (P.asIdeal.mul_mem_left _ a) (P.asIdeal.mul_mem_left _ b))
  have hA : ∀ P : HeightOneSpectrum (𝓞 E), ϖ ∈ P.asIdeal →
      P.valuation E (dt (f'' P) / dt (f P)) = P.valuation E (ϖ : E) := fun P hP => by
    have hP' := (mem_divs h0 P).2 hP
    rw [val_det_ker (hf P) (hf'' P) (d.1.f ⟨P, hP'⟩) (d.2.f_add ⟨P, hP'⟩) (d.2.f_smul ⟨P, hP'⟩) (d.2.f_ne ⟨P, hP'⟩)
      (h3 ⟨P, hP'⟩)]
    exact (val_of_simple hP (hsq P hP')).symm
  refine eq_of_gen _ (fun _ => (ϖ : E) / star (ϖ : E)) (fun P => gen_relDet hN.1.fg (hf P) (hf'' P))
    (fun P => gen_of (div_ne_zero hϖ hϖ') (le_locP P _ (Submodule.mem_span_singleton_self _))
      (GlobalTheory.CharVal.maxV_span_singleton _).1) fun P => ?_
  by_cases hP : ϖ ∈ P.asIdeal
  · have : P.valuation E (star (ϖ : E)) = 1 := val_of_notMem (hnot P hP)
    rw [hA P hP, map_div₀, this, div_one]
  have hv : P.valuation E (ϖ : E) = 1 := val_of_notMem hP
  by_cases hP' : cO E ϖ ∈ P.asIdeal
  · have e1 := hA (conjPrime₂ P) ((mem_conjP P ϖ).2 hP')
    have e2 : (conjPrime₂ P).valuation E (dt (f'' (conjPrime₂ P)) / dt (f (conjPrime₂ P)) / (ϖ : E)) = 1 := by
      rw [map_div₀, e1, div_self (val_pos hϖ).ne']
    have e3 := val_star_eq_one e2
    have e4 := val_dual hN (hf (conjPrime₂ P)) (f' := f P) (by rw [conjP_conjP]; exact hf P)
    have e5 := val_dual hN'' (hf'' (conjPrime₂ P)) (f' := f'' P) (by rw [conjP_conjP]; exact hf'' P)
    rw [conjP_conjP] at e3 e4 e5
    have e6 : dt (f'' P) / dt (f P) = (star (dt (f'' (conjPrime₂ P))) * dt (f'' P)) / (star (dt (f (conjPrime₂ P))) * dt (f P)) /
        star (dt (f'' (conjPrime₂ P)) / dt (f (conjPrime₂ P)) / (ϖ : E)) / star (ϖ : E) := by
      have := star_ne_zero.2 (dt_ne (f'' (conjPrime₂ P)))
      have := star_ne_zero.2 (dt_ne (f (conjPrime₂ P)))
      have := dt_ne (f P)
      rw [star_div₀, star_div₀]
      field_simp
    rw [e6, map_div₀, map_div₀, map_div₀, e3, e4, e5, map_div₀, hv]
    simp
  · have hv' : P.valuation E (star (ϖ : E)) = 1 := val_of_notMem hP'
    have e : IsFr P N'' (f P) := fun x => by
      rw [← hf P x, mem_locP, mem_locP]
      constructor
      · rintro ⟨s, hs, h⟩
        refine ⟨cO E ϖ * s, fun hm => (P.isPrime.mem_or_mem hm).elim hP' hs, ?_⟩
        rw [mul_smul, ← algebraMap_smul E (cO E ϖ)]
        exact h2 _ h
      · rintro ⟨s, hs, h⟩
        refine ⟨ϖ * s, fun hm => (P.isPrime.mem_or_mem hm).elim hP hs, ?_⟩
        rw [mul_smul, ← algebraMap_smul E ϖ]
        exact h1 _ h
    rw [map_div₀, map_div₀, hv, hv', (gen_detI e).val_eq (gen_detI (hf'' P)), div_self (val_pos (dt_ne _)).ne', div_one]

omit [StarRing E] in
theorem det_set_rel {E' : Type} [Field E'] [NumberField E'] (e : E ≃+* E') (L N : Submodule (𝓞 E) (Fin n → E)) :
    {x | ∃ A : Matrix (Fin n) (Fin n) E', (∀ v ∈ trL e L, A.mulVec v ∈ trL e N) ∧ x = A.det} =
      e '' {x | ∃ A : Matrix (Fin n) (Fin n) E, (∀ v ∈ L, A.mulVec v ∈ N) ∧ x = A.det} := by
  have key : ∀ A : Matrix (Fin n) (Fin n) E, (∀ v ∈ trL e L, (A.map e).mulVec v ∈ trL e N) ↔ ∀ v ∈ L, A.mulVec v ∈ N := by
    intro A
    constructor
    · intro H v hv
      have := H (fun i => e (v i)) ((mem_trL e _ _).2 (by simpa using hv))
      rw [map_mulVec', mem_trL] at this
      simpa using this
    · intro H v hv
      have := H (fun i => e.symm (v i)) ((mem_trL e _ _).1 hv)
      have hv' : v = fun i => e (e.symm (v i)) := by simp
      rw [hv', map_mulVec', mem_trL]
      simpa using this
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    have hAe : A = (A.map e.symm).map e := by ext i j; simp
    refine ⟨_, ⟨A.map e.symm, (key _).1 (hAe ▸ hA), rfl⟩, ?_⟩
    rw [← det_map', ← hAe]
  · rintro ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨A.map e, (key A).2 hA, (det_map' e A).symm⟩

end General

theorem chi_move : ∀ (D : D7) (X : Fields) (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ) (b : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (d : DecoSet (E := X.E) (n := b) (ST := divs ϖ) (SG := SG)) (N'' : Submodule (𝓞 X.E) (Sp X.E b)), X.Ok → s.Ok → TaylorLogMetric.IsChi D χ → ϖ ≠ 0 → IsCoprime ϖ (X.conjO ϖ) → (∀ P ∈ divs ϖ, ϖ ∉ P.asIdeal ^ 2) → IsSdLat N'' → ((∀ y ∈ d.1.N, (ϖ : X.E) • y ∈ N'') ∧ (∀ y ∈ N'', star (ϖ : X.E) • y ∈ d.1.N) ∧ ∀ (P : ↥(divs ϖ)) (y : Sp X.E b), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d.1.at P.1 ∧ d.1.f P y = 0) → χ (TaylorLogMetric.detId D (s.lat d.1.N) (s.lat N'')) = ∏ τ, (s.σ₀ (X.emb τ ((ϖ : X.E) / star (ϖ : X.E))))⁻¹ := by
  intro D X s χ b SG ϖ d N'' _ hs hχ h0 hcop hsq hN'' ⟨h1, h2, h3⟩
  have hϖ : (ϖ : X.E) ≠ 0 := by simpa using h0
  have hϖ' : star (ϖ : X.E) ≠ 0 := star_ne_zero.2 hϖ
  have e : TaylorLogMetric.detId D (s.lat d.1.N) (s.lat N'') = GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.idTo s (relDet d.1.N N'') :=
    (congrArg (Submodule.span (𝓞 D.host.E)) (det_set_rel s.iE d.1.N N'')).trans (trI_span s.iE _).symm
  rw [e, relDet_companion d h0 hcop hsq hN'' h1 h2 h3]
  refine ChiUnit.chi_span hs hχ ?_
  rw [star_div₀, star_star]
  field_simp

end GlobalTheory.MomT.ChiMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormSplitPlace
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.Proof.AbsNormSplitPlace

open GlobalTheory.Proof.NarrowJetMoments

theorem absNorm_of_split {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v) (hl : (Ideal.absNorm v.asIdeal).Prime)
    {P : HeightOneSpectrum (𝓞 E)} (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal := by
  obtain ⟨Q, Q', -, hm⟩ := hs
  have hN : Ideal.absNorm Q.asIdeal * Ideal.absNorm Q'.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [← map_mul, ← hm, Ideal.absNorm_algebraMap]
    congr 1
    rw [← h2]
    exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E).symm
  have h1 : ∀ R : HeightOneSpectrum (𝓞 E), Ideal.absNorm R.asIdeal ≠ 1 := fun R h =>
    R.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have hb := (hl.mul_eq_prime_sq_iff (h1 Q) (h1 Q')).1 hN
  have hle : Q.asIdeal * Q'.asIdeal ≤ P.asIdeal := by
    rw [← hm, ← hP, Ideal.under_def]
    exact Ideal.map_comap_le
  rcases P.isPrime.mul_le.1 hle with h | h
  · rw [← Q.isMaximal.eq_of_le P.isPrime.ne_top h, hb.1]
  · rw [← Q'.isMaximal.eq_of_le P.isPrime.ne_top h, hb.2]

theorem plc_eq_absNorm {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    (hl : (Ideal.absNorm v.asIdeal).Prime) : ringChar (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
  have h6 : ringChar (𝓞 F ⧸ v.asIdeal) ∣ Ideal.absNorm v.asIdeal := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.absNorm_mem _
  haveI := v.isPrime
  exact ((Nat.dvd_prime hl).1 h6).resolve_left CharP.ringChar_ne_one

theorem main : ∀ (Z : Dat) (u : Z.Pr.Word) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S), Z.Ok → IsSel Z.X sel → Z.Pr.T u ∈ S → (∀ i, Z.Pr.g i ∈ S) → (∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u) ∧ ∀ P ∈ rowSG Z.Pr sel mu, (Formalism.L2.Col.qOf P).Prime ∧ Formalism.L2.Col.qOf P ≠ Z.Pr.T u ∧ ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∉ P.asIdeal ∧ ((∃ i, Formalism.L2.Col.qOf P = Z.Pr.g i) ∨ Formalism.L2.Col.qOf P ∉ S) := by
  intro Z u sel S mu hZ hsel hT hg
  have hPr := hZ.primes
  have hTn : ∀ P ∈ rowSG Z.Pr sel mu, ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∉ P.asIdeal := fun P hP =>
    notMem_rowSG hPr hsel (hPr.T_prime u) hT (hPr.T_ne_g u) hP
  refine ⟨fun P hP hP' => ?_, fun P hP => ?_⟩
  · rcases (mem_Sall sel mu u P).1 hP with h | h <;> rcases (mem_Sall sel mu u _).1 hP' with h' | h'
    · refine conj_piT_notMem hPr u ⟨conjPrime₂ P, h'⟩ ?_
      change cO Z.X.E (Z.Pr.piT u) ∈ (conjPrime₂ P).asIdeal
      rw [mem_conjP, cO_cO]
      exact decoFin_mem_of_mem_divs h
    · exact hTn _ h' (natCast_mem_conjP.2 (T_mem hPr u ⟨P, h⟩))
    · exact hTn _ h (natCast_mem_conjP.1 (T_mem hPr u ⟨conjPrime₂ P, h'⟩))
    · exact conjP_notMem_rowSG hZ.fields hPr hsel hg h h'
  · have key : (Formalism.L2.Col.qOf P).Prime ∧ ((∃ i, Formalism.L2.Col.qOf P = Z.Pr.g i) ∨ Formalism.L2.Col.qOf P ∉ S) := by
      classical
      rcases Finset.mem_union.1 hP with h | h
      · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h
        have e : Formalism.L2.Col.qOf P = Z.Pr.g i := hPr.vG_norm i P hi
        exact ⟨e ▸ hPr.g_prime i, Or.inl ⟨i, e⟩⟩
      · obtain ⟨v, hv, e⟩ := good_of_mem_QE h
        have e1 : Formalism.L2.Col.qOf P = Ideal.absNorm v.asIdeal :=
          absNorm_of_split hZ.fields.rankE hv.1 hv.2.1.1 (e ▸ hsel v)
        refine ⟨e1 ▸ hv.2.1.1, Or.inr ?_⟩
        rw [e1, ← plc_eq_absNorm hv.2.1.1]
        exact hv.2.2
    refine ⟨key.1, fun e => hTn P hP ?_, hTn P hP, key.2⟩
    rw [← e]
    exact Ideal.absNorm_mem _

end GlobalTheory.Proof.AbsNormSplitPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentCompanion
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.MomentCompanion

theorem companion_gen {E : Type} [Field E] [NumberField E] [StarRing E] {b : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (ϖ : 𝓞 E) (d : DecoSet (E := E) (n := b) (ST := ST) (SG := SG))
    (hST : ∀ P : ST, ϖ ∈ P.1.asIdeal) (hcop : IsCoprime ϖ (cO E ϖ)) :
    ∃ N'' : Submodule (𝓞 E) (Sp E b), IsSdLat N'' ∧ (∀ y ∈ d.1.N, (ϖ : E) • y ∈ N'') ∧
      (∀ y ∈ N'', star (ϖ : E) • y ∈ d.1.N) ∧
      ∀ (P : ST) (y : Sp E b), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d.1.at P.1 ∧ d.1.f P y = 0 := by
  have hd := d.2
  have hIN : Ideal.span {ϖ} • d.1.N ≤ d.1.L := by
    rw [Submodule.smul_le]
    intro r hr y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    exact hd.smul_N_mem_L (fun P => Ideal.mul_mem_left _ _ (hST P)) hy
  obtain ⟨h1, h2⟩ := glue_unimodular (I := Ideal.span {ϖ}) (J := Ideal.span {cO E ϖ})
    (fun p hp => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hp
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    (fun p hp => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hp
      rw [map_mul, cO_cO]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    (by
      obtain ⟨u, v, huv⟩ := hcop
      exact ⟨u * ϖ, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), v * cO E ϖ,
        Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), huv⟩)
    hd.uni hd.L_lattice hd.L_le_N hIN
  have hbar : ∀ x ∈ d.1.L ⊔ Ideal.span {ϖ} • dual (hStd E b) d.1.L, cO E ϖ • x ∈ d.1.L := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ hy) ?_
    refine Submodule.smul_induction_on hz (fun r hr u hu => ?_) (fun u v hu hv => ?_)
    · rw [smul_comm]
      exact hIN (Submodule.smul_mem_smul hr (conj_smul_dual_mem hd.uni hIN
        (by rw [cO_cO]; exact Ideal.mem_span_singleton_self _) hu))
    · rw [smul_add]
      exact Submodule.add_mem _ hu hv
  refine ⟨_, ⟨h1, h2⟩, fun y hy => ?_, fun y hy => ?_, fun P y => ?_⟩
  · have : ϖ • y ∈ d.1.L := hd.smul_N_mem_L hST hy
    rw [← algebraMap_smul E ϖ y] at this
    exact Submodule.mem_sup_left this
  · have := hd.L_le_N (hbar y hy)
    rw [← algebraMap_smul E (cO E ϖ) y, algebraMap_cO] at this
    exact this
  · have hn : cO E ϖ ∉ P.1.asIdeal := by
      intro h
      obtain ⟨u, v, huv⟩ := hcop
      exact one_notMem P.1 (huv ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hST P)) (Ideal.mul_mem_left _ _ h))
    rw [← hd.mem_locP_L P y]
    exact ⟨fun h => localization_le_of_smul_mem hn hbar h, fun h => localization_le_of_smul_mem (one_notMem P.1) (fun x hx => by
      rw [one_smul]; exact Submodule.mem_sup_left hx) h⟩

theorem companion : ∀ (X : Fields) (b : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (d : DecoSet (E := X.E) (n := b) (ST := divs ϖ) (SG := SG)), X.Ok → ϖ ≠ 0 → IsCoprime ϖ (X.conjO ϖ) → (∀ P ∈ divs ϖ, ϖ ∉ P.asIdeal ^ 2) → ∃ N'' : Submodule (𝓞 X.E) (Sp X.E b), IsSdLat N'' ∧ (∀ y ∈ d.1.N, (ϖ : X.E) • y ∈ N'') ∧ (∀ y ∈ N'', star (ϖ : X.E) • y ∈ d.1.N) ∧ ∀ (P : ↥(divs ϖ)) (y : Sp X.E b), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d.1.at P.1 ∧ d.1.f P y = 0 :=
  fun _ _ _ ϖ d _ h0 hcop _ => companion_gen ϖ d (fun P => (mem_divs h0 P.1).1 P.2) hcop

end GlobalTheory.MomT.MomentCompanion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ApplyMemLocP
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable
  GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.AdjMem

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

omit [NumberField E] in
theorem hStd_adj (x : HomE E a b) (v : Sp E a) (y : Sp E b) : hStd E a v (adj x y) = hStd E b (x v) y := by
  have : x v = LinearMap.toMatrix' x *ᵥ v := (LinearMap.toMatrix'_mulVec x v).symm
  rw [this]
  change star v ⬝ᵥ ((LinearMap.toMatrix' x)ᴴ *ᵥ y) = star (LinearMap.toMatrix' x *ᵥ v) ⬝ᵥ y
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec]

theorem apply_mem_locP {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {Q : HeightOneSpectrum (𝓞 E)} (hA : localization₂ Q.asIdeal AA = localization₂ Q.asIdeal (1 : Submodule (𝓞 E) E))
    {x : HomE E a b} (hx : x ∈ perO AA N N') {v : Sp E a} (hv : v ∈ localization₂ Q.asIdeal N) : x v ∈ localization₂ Q.asIdeal N' := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, x', hx', rfl⟩ := hz
    obtain ⟨s, hs, hsv⟩ := (mem_locP _ _ _).1 hv
    obtain ⟨t, ht, htr⟩ := (mem_locP _ _ _).1 (hA ▸ le_locP Q AA hr)
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 htr
    refine (mem_locP _ _ _).2 ⟨t * s, fun hm => (Q.isPrime.mem_or_mem hm).elim ht hs, ?_⟩
    have h1 := N'.smul_mem c (hx' _ hsv)
    have e : (t * s) • (r • x') v = c • x' (s • v) := by
      rw [← algebraMap_smul E c, hc, ← algebraMap_smul E s v, map_smul, LinearMap.smul_apply, ← algebraMap_smul E (t * s),
        smul_smul, smul_smul, map_mul, Algebra.smul_def t r]
      congr 1
      ring
    rw [e]
    exact h1
  | zero => exact zero_mem _
  | add x x' _ _ h h' => exact add_mem h h'
  | smul c x _ h => exact Submodule.smul_mem _ c h

theorem adj_mem_locP {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {P : HeightOneSpectrum (𝓞 E)} (hN : IsSdLat N) (hN' : IsSdLat N')
    (hA : localization₂ (conjPrime₂ P).asIdeal AA = localization₂ (conjPrime₂ P).asIdeal (1 : Submodule (𝓞 E) E))
    {x : HomE E a b} (hx : x ∈ perO AA N N') {y : Sp E b} (hy : y ∈ localization₂ P.asIdeal N') : adj x y ∈ localization₂ P.asIdeal N := by
  obtain ⟨Q, rfl⟩ : ∃ Q, P = conjPrime₂ Q := ⟨conjPrime₂ P, (GlobalTheory.CharValCompare.conjP_conjP P).symm⟩
  rw [GlobalTheory.CharValCompare.conjP_conjP] at hA
  rw [GlobalTheory.Survey.StandardDeterminantUnits.mem_at_conj hN'.1.fg hN'.2] at hy
  rw [GlobalTheory.Survey.StandardDeterminantUnits.mem_at_conj hN.1.fg hN.2]
  intro v hv
  rw [hStd_adj]
  exact hy _ (apply_mem_locP hA hx hv)

theorem adj_per_mem : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a))
    (N'' : Submodule (𝓞 X.E) (Sp X.E b)) (P : HeightOneSpectrum (𝓞 X.E)), IsSdLat N → IsSdLat N'' →
    localization₂ (conjPrime₂ P).asIdeal A.AA = localization₂ (conjPrime₂ P).asIdeal (1 : Submodule (𝓞 X.E) X.E) →
    ∀ x ∈ per A N N'', ∀ y ∈ localization₂ P.asIdeal N'', adj x y ∈ localization₂ P.asIdeal N :=
  fun _ _ _ _ _ _ _ hN hN' hA _ hx _ hy => adj_mem_locP hN hN' hA hx hy

end GlobalTheory.AdjMem
end
end

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MomT

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable

section abelian₂

variable {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p])

theorem lamC_of_mem {x : ℂ} (h : x ∈ TaylorLogMetric.Qbar) : TaylorLogMetric.lamC lam x = lam ⟨x, h⟩ := dif_pos h

theorem lamC_mul {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x * y) = TaylorLogMetric.lamC lam x * TaylorLogMetric.lamC lam y := by
  rw [lamC_of_mem lam hx, lamC_of_mem lam hy, lamC_of_mem lam (mul_mem hx hy), ← map_mul]; rfl

theorem lamC_zpow {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (n : ℤ) : TaylorLogMetric.lamC lam (x ^ n) = TaylorLogMetric.lamC lam x ^ n := by
  rw [lamC_of_mem lam hx, lamC_of_mem lam (zpow_mem hx n), ← map_zpow₀]; rfl

theorem lamC_sum {κ : Type} (T : Finset κ) (f : κ → ℂ) (h : ∀ i ∈ T, f i ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (∑ i ∈ T, f i) = ∑ i ∈ T, TaylorLogMetric.lamC lam (f i) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, lamC_of_mem lam (zero_mem _)]; exact map_zero lam
  | insert i T hi ih =>
    have h1 := h i (Finset.mem_insert_self _ _)
    have h2 : ∀ j ∈ T, f j ∈ TaylorLogMetric.Qbar := fun j hj => h j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih h2, lamC_of_mem lam h1, lamC_of_mem lam (sum_mem h2),
      lamC_of_mem lam (add_mem h1 (sum_mem h2)), ← map_add]
    rfl

end abelian₂

section Asm

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E)))
  (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))

theorem thInd_add (c : ℕ) (x y : HomE X.E a b) (hy : y ∈ mulLat c (homAt S N N')) :
    A.thInd S N N' c (x + y) = A.thInd S N N' c x := by
  have : A.IsLift S N N' c (x + y) = A.IsLift S N N' c x := by
    funext t
    unfold Amb.IsLift
    have e : t - x = (t - (x + y)) + y := by abel
    rw [e, add_mem_cancel_right hy]
  unfold Amb.thInd Amb.liftW
  rw [this]

theorem mulLat_le_divLat {H : Type} [AddCommGroup H] [Module (𝓞 X.E) H] (c c' : ℕ) (M : Submodule (𝓞 X.E) H) :
    mulLat c M ≤ divLat c' M := by
  rintro _ ⟨y, hy, rfl⟩
  exact M.smul_mem _ (M.smul_mem _ hy)

theorem assemble {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : X.K →+* ℂ_[p])
    (hlam : ∀ k, A.σ₀ k ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.lamC lam (A.σ₀ k) = ι k) (cA c : ℕ) (hcA : 0 < cA) (hc : 0 < c)
    (hN : IsSdLat N) (hN' : IsSdLat N') (Ξ : HomE X.E a b → X.K)
    (hχ : A.chiF a b N N' ∈ TaylorLogMetric.Qbar) (hχ1 : ‖TaylorLogMetric.lamC lam (A.chiF a b N N')‖ = 1)
    (C : AddSubgroup (HomE X.E a b)) (hC : C ≤ (divLat cA (homAt S N N')).toAddSubgroup) (J : Finset (HomE X.E a b))
    (hJ : IsReps (mulLat c (homAt S N N')).toAddSubgroup C J)
    (h0 : ∀ x ∈ divLat cA (homAt S N N'), ∀ y ∈ mulLat c (homAt S N N'), Ξ (x + y) = Ξ x)
    (h1 : ∀ x ∈ divLat cA (homAt S N N'), ∀ y ∈ C, Ξ (x + y) = Ξ x)
    (h2 : ∀ x ∈ divLat cA (homAt S N N'), ‖ι (Ξ x)‖ ≤ 1)
    (Sup : Set (HomE X.E a b)) (tab : HomE X.E a b → (DVar X.Tau a b →₀ ℕ) → ℂ_[p])
    (h3 : ∀ x ∈ divLat cA (homAt S N N'), Ξ x ≠ 0 → InIntClosure Sup tab Set.univ
      fun m => TaylorLogMetric.lamC lam (∑ j ∈ J, jetC A.cD (A.thInd S N N' c (x + j)) m)) :
    InIntClosure Sup tab (RatIdx A S cA c N N' Ξ) fun m => ι (jetSum A S cA c N N' Ξ m) := by
  classical
  obtain ⟨R, hR, hsum⟩ := _root_.GlobalTheory.latSum_eq_sum_sum_reps X.E _ (divLat cA (homAt S N N')) (mulLat c (homAt S N N')) C J
    (mulLat_le_divLat _ _ _) hC (_root_.GlobalTheory.MomT.finite_quot_divLat_mulLat_homAt X.E a b S N N' cA c hN.1 hN'.1 hcA hc) hJ
  have hχ0 : A.chiF a b N N' ≠ 0 := by
    intro h
    rw [h, lamC_of_mem lam (zero_mem _)] at hχ1
    have : lam ⟨0, zero_mem _⟩ = 0 := map_zero lam
    rw [this, norm_zero] at hχ1
    exact zero_ne_one hχ1
  have hinv : TaylorLogMetric.lamC lam (A.chiF a b N N')⁻¹ = (TaylorLogMetric.lamC lam (A.chiF a b N N'))⁻¹ := by
    simpa using lamC_zpow lam hχ (-1)
  refine clo_congr (clo_sum R (fun x m => if Ξ x = 0 then 0 else ι (Ξ x) * TaylorLogMetric.lamC lam (A.chiF a b N N')⁻¹ *
      TaylorLogMetric.lamC lam (∑ j ∈ J, jetC A.cD (A.thInd S N N' c (x + j)) m)) (M := Set.univ) fun x hx => ?_)
    subset_rfl (Set.subset_univ _) fun m hm => ?_
  · by_cases h : Ξ x = 0
    · simpa [h] using clo_zero Sup tab Set.univ
    · simp only [if_neg h]
      refine clo_mul (h3 x (hR x hx) h) _ ?_
      rw [norm_mul, hinv, norm_inv, hχ1, inv_one, mul_one]
      exact h2 x (hR x hx)
  · unfold jetSum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum X.K _ (fun x hx y hy => by rw [h0 x hx y hy]; unfold Amb.jetK; rw [thInd_add A S N N' c x y hy]), map_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hj : ∀ j ∈ J, Ξ (x + j) = Ξ x := fun j hj => h1 x (hR x hx) j (hJ.1 j hj)
    rw [Finset.sum_congr rfl fun j hj' => by rw [hj j hj'], ← Finset.mul_sum]
    split_ifs with h
    · simp [h]
    have hk : ∀ j ∈ J, A.σ₀ (A.jetK S N N' c (x + j) m) =
        (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' c (x + j)) m := by
      intro j hj'
      have := hm (x + j) (add_mem (hR x hx) (hC (hJ.1 j hj'))) (by rw [hj j hj']; exact h)
      unfold Amb.jetK desc
      rw [dif_pos this]
      exact this.choose_spec
    have e : A.σ₀ (∑ j ∈ J, A.jetK S N N' c (x + j) m) =
        (A.chiF a b N N')⁻¹ * ∑ j ∈ J, jetC A.cD (A.thInd S N N' c (x + j)) m := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.mul_sum]; exact Finset.sum_congr rfl hk
    have hq : ∑ j ∈ J, jetC A.cD (A.thInd S N N' c (x + j)) m ∈ TaylorLogMetric.Qbar := by
      have := mul_mem hχ (hlam (∑ j ∈ J, A.jetK S N N' c (x + j) m)).1
      rwa [e, mul_inv_cancel_left₀ hχ0] at this
    rw [map_mul, ← (hlam (∑ j ∈ J, A.jetK S N N' c (x + j) m)).2, e, lamC_mul lam (inv_mem hχ) hq, mul_assoc]

end Asm

section Phi

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

theorem suppBar_add {d : Deco E a ST SG} {d' : Deco E b ST SG'} (hd' : d'.Ok) {x y : HomE E a b} (hx : x ∈ suppBar d d')
    (hy : ∀ P : ST, ∀ v ∈ d.at P.1, y v ∈ d'.at P.1 ∧ d'.f P (y v) = 0) : x + y ∈ suppBar d d' := by
  intro P v hv
  refine ⟨add_mem (hx P v hv).1 (hy P v hv).1, ?_⟩
  rw [LinearMap.add_apply, hd'.f_add P _ (hx P v hv).1 _ (hy P v hv).1, (hy P v hv).2, add_zero, (hx P v hv).2]

theorem phiT_add (K : Type) [Field K] {d : Deco E a ST SG} {d' : Deco E b ST SG'} (hd' : d'.Ok) (x : HomE E a b)
    {y : HomE E a b} (hy : ∀ P : ST, ∀ v ∈ d.at P.1, y v ∈ d'.at P.1 ∧ d'.f P (y v) = 0) :
    phiT K d d' (x + y) = phiT K d d' x := by
  have h : x + y ∈ suppBar d d' ↔ x ∈ suppBar d d' := by
    refine ⟨fun h => ?_, fun h => suppBar_add hd' h hy⟩
    have := suppBar_add hd' (y := -y) h fun P v hv => ⟨neg_mem (hy P v hv).1, by
      have := hd'.f_smul P (-1) _ (hy P v hv).1
      rw [(hy P v hv).2, mul_zero, neg_one_smul] at this
      exact this⟩
    simpa using this
  unfold phiT
  by_cases hx : x ∈ suppBar d d'
  · exact (if_pos (h.2 hx)).trans (if_pos hx).symm
  · exact (if_neg fun h' => hx (h.1 h')).trans (if_neg hx).symm

theorem ker_of_mulLat {d : Deco E a ST SG} {d' : Deco E b ST SG'} (hd' : d'.Ok) {S : Finset (HeightOneSpectrum (𝓞 E))}
    (hS : ST ⊆ S) {c : ℕ} (hc : ∀ P ∈ ST, (c : 𝓞 E) ∈ P.asIdeal) {y : HomE E a b} (hy : y ∈ mulLat c (homAt S d.N d'.N)) :
    ∀ P : ST, ∀ v ∈ d.at P.1, y v ∈ d'.at P.1 ∧ d'.f P (y v) = 0 := by
  obtain ⟨y, hy, rfl⟩ := hy
  intro P v hv
  have h1 : y v ∈ d'.at P.1 := hy P.1 (hS P.2) v hv
  refine ⟨Submodule.smul_mem _ (c : 𝓞 E) h1, ?_⟩
  have := hd'.f_smul P (c : 𝓞 E) _ h1
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (hc P.1 P.2), zero_mul] at this
  exact this

theorem homAt_mono {S S' : Finset (HeightOneSpectrum (𝓞 E))} (h : S ⊆ S') (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) : homAt S' N N' ≤ homAt S N N' := fun _ hx P hP => hx P (h hP)

theorem norm_phiT_le {K : Type} [Field K] {p : ℕ} [Fact p.Prime] (ι : K →+* ℂ_[p]) (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (x : HomE E a b) : ‖ι (phiT K d d' x)‖ ≤ 1 := by
  unfold phiT
  split_ifs <;> simp

theorem mem_suppBar_of_ne {K : Type} [Field K] {d : Deco E a ST SG} {d' : Deco E b ST SG'} {x : HomE E a b}
    (h : phiT K d d' x ≠ 0) : x ∈ suppBar d d' := by
  unfold phiT at h
  split_ifs at h with h'
  exacts [h', absurd rfl h]

end Phi

section Types

variable {X : Fields} {A : Amb X} {a b : ℕ} {S SG SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} {ϖ : 𝓞 X.E} {p g cA : ℕ}
  [Fact p.Prime] {lam : TaylorLogMetric.Qbar →+* ℂ_[p]} {ι : X.K →+* ℂ_[p]} {un : X.Tau → ℂ_[p]} {w : HeightOneSpectrum (𝓞 X.K)}

theorem conjO_conjO (x : 𝓞 X.E) : X.conjO (X.conjO x) = x := by
  ext
  exact star_star (x : X.E)

omit [Fact p.Prime] in
theorem Ctx.ne_zero (h : Ctx A a b S SG ϖ p g cA) : ϖ ≠ 0 := by
  rintro rfl
  have := h.2.2.2.2.2.1
  rw [zero_mul] at this
  exact h.2.2.2.2.1.ne_zero (by exact_mod_cast this.symm)

omit [Fact p.Prime] in
theorem Ctx.sub (h : Ctx A a b S SG ϖ p g cA) : divs ϖ ⊆ S ∧ SG ⊆ S ∧ (∀ P ∈ divs ϖ, (p : 𝓞 X.E) ∈ P.asIdeal) ∧
    0 < cA ∧ 0 < p * g := by
  obtain ⟨-, -, -, -, hp, hn, -, hS, -, hg, hA⟩ := id h
  refine ⟨fun P hP => (hS P).2 (Or.inl ((mem_divs h.ne_zero P).1 hP)), fun P hP => (hS P).2 (Or.inr hP),
    fun P hP => hn ▸ Ideal.mul_mem_right _ _ ((mem_divs h.ne_zero P).1 hP), Nat.pos_of_ne_zero ?_,
    Nat.mul_pos hp.pos (Nat.pos_of_ne_zero ?_)⟩
  · rintro rfl
    exact hp.ne_one (by simpa using hA)
  · rintro rfl
    exact hp.ne_one (by simpa using hg)

theorem assemble_phi (h : Ctx A a b S SG ϖ p g cA) (hlam : ∀ k, A.σ₀ k ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.lamC lam (A.σ₀ k) = ι k)
    (hw : Induces ι w) (d : DecoSet (E := X.E) (n := a) (ST := divs ϖ) (SG := SG₁)) (d' : DecoSet (E := X.E) (n := b) (ST := divs ϖ) (SG := SG₂))
    (hχ : A.chiF a b d.1.N d'.1.N ∈ TaylorLogMetric.Qbar) (hχ1 : ‖TaylorLogMetric.lamC lam (A.chiF a b d.1.N d'.1.N)‖ = 1)
    (Ξ₀ : HomE X.E a b → X.K) (hΞ : OffDatum cA (p * g) d.1.N d'.1.N SG w Ξ₀)
    (C : AddSubgroup (HomE X.E a b)) (hC : ∀ y ∈ C, y ∈ homAt S d.1.N d'.1.N ∧ y ∈ mulLat (p * g) (homAt SG d.1.N d'.1.N) ∧
      ∀ P : ↥(divs ϖ), ∀ v ∈ d.1.at P.1, y v ∈ d'.1.at P.1 ∧ d'.1.f P (y v) = 0)
    (J : Finset (HomE X.E a b)) (hJ : IsReps (mulLat (p * g) (homAt S d.1.N d'.1.N)).toAddSubgroup C J)
    (Sup : Set (HomE X.E a b)) (tab : HomE X.E a b → (DVar X.Tau a b →₀ ℕ) → ℂ_[p])
    (h3 : ∀ x ∈ divLat cA (homAt S d.1.N d'.1.N), x ∈ suppBar d.1 d'.1 → InIntClosure Sup tab Set.univ
      fun m => TaylorLogMetric.lamC lam (∑ j ∈ J, jetC A.cD (A.thInd S d.1.N d'.1.N (p * g) (x + j)) m)) :
    InIntClosure Sup tab (RatIdx A S cA (p * g) d.1.N d'.1.N fun x => phiT X.K d.1 d'.1 x * Ξ₀ x)
      fun m => ι (jetSum A S cA (p * g) d.1.N d'.1.N (fun x => phiT X.K d.1 d'.1 x * Ξ₀ x) m) := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := h.sub
  have hd : ∀ x ∈ divLat cA (homAt S d.1.N d'.1.N), x ∈ divLat cA (homAt SG d.1.N d'.1.N) :=
    fun x hx => homAt_mono s2 _ _ hx
  refine assemble A S d.1.N d'.1.N lam ι hlam cA (p * g) s4 s5 ⟨d.2.lat, d.2.uni⟩ ⟨d'.2.lat, d'.2.uni⟩ _ hχ hχ1 C
    (fun y hy => Submodule.smul_mem (homAt S d.1.N d'.1.N) (cA : 𝓞 X.E) (hC y hy).1) J hJ (fun x hx y hy => ?_)
    (fun x hx y hy => ?_) (fun x hx => ?_) Sup tab fun x hx h0 => h3 x hx (mem_suppBar_of_ne (left_ne_zero_of_mul h0))
  · rw [phiT_add X.K d'.2 x (ker_of_mulLat d'.2 s1 (fun P hP => ?_) hy),
      (hΞ x (hd x hx)).2 y (Submodule.map_mono (homAt_mono s2 _ _) hy)]
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (s3 P hP)
  · rw [phiT_add X.K d'.2 x (hC y hy).2.2, (hΞ x (hd x hx)).2 y (hC y hy).2.1]
  · rw [map_mul, norm_mul]
    exact mul_le_one₀ (norm_phiT_le ι _ _ x) (norm_nonneg _)
      ((_root_.GlobalTheory.MomPlace.places X.K p A.σ₀ ι).2.1 w hw _ (hΞ x (hd x hx)).1)

theorem type_bar (h : Ctx A a b S SG ϖ p g cA) (hlam : ∀ k, A.σ₀ k ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.lamC lam (A.σ₀ k) = ι k)
    (hw : Induces ι w) (d : DecoSet (E := X.E) (n := a) (ST := divs ϖ) (SG := SG₁)) (d' : DecoSet (E := X.E) (n := b) (ST := divs ϖ) (SG := SG₂))
    (hχ : A.chiF a b d.1.N d'.1.N ∈ TaylorLogMetric.Qbar) (hχ1 : ‖TaylorLogMetric.lamC lam (A.chiF a b d.1.N d'.1.N)‖ = 1)
    (Ξ₀ : HomE X.E a b → X.K) (hΞ : OffDatum cA (p * g) d.1.N d'.1.N SG w Ξ₀)
    (hm : PtMom A a b lam ι un ((ϖ : X.E) / star (ϖ : X.E))) :
    InIntClosure (suppBar d.1 d'.1) (ptTab ι un)
      (RatIdx A S cA (p * g) d.1.N d'.1.N fun x => phiT X.K d.1 d'.1 x * Ξ₀ x)
      fun m => ι (jetSum A S cA (p * g) d.1.N d'.1.N (fun x => phiT X.K d.1 d'.1 x * Ξ₀ x) m) := by
  refine assemble_phi h hlam hw d d' hχ hχ1 Ξ₀ hΞ ⊥ (fun y hy => ?_) {0} ⟨by simp, by simp, by simp⟩ _ _ fun x hx hs => ?_
  · rw [AddSubgroup.mem_bot.1 hy]
    refine ⟨zero_mem _, zero_mem _, fun P v _ => ⟨zero_mem _, ?_⟩⟩
    have := d'.2.f_smul P 0 0 (zero_mem _)
    simpa using this
  · have := (_root_.GlobalTheory.MomT.CosetBar.moments_thInd X A a b S SG ϖ p g cA d.1.N d'.1.N lam ι un h ⟨d.2.lat, d.2.uni⟩ ⟨d'.2.lat, d'.2.uni⟩ hm x hx
      fun P hP v hv => (hs ⟨P, hP⟩ v hv).1).2
    refine clo_congr this (fun t ht => ?_) subset_rfl fun m _ => by simp
    have := suppBar_add d'.2 hs (ker_of_mulLat d'.2 subset_rfl h.sub.2.2.1 ht)
    simpa using this

theorem type_p (h : Ctx A a b S SG ϖ p g cA) (hlam : ∀ k, A.σ₀ k ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.lamC lam (A.σ₀ k) = ι k)
    (hw : Induces ι w) (d : DecoSet (E := X.E) (n := a) (ST := divs ϖ) (SG := SG₁)) (d' : DecoSet (E := X.E) (n := b) (ST := divs ϖ) (SG := SG₂)) (hstd : StdAtT d.1)
    (hχ : A.chiF a b d.1.N d'.1.N ∈ TaylorLogMetric.Qbar) (hχ1 : ‖TaylorLogMetric.lamC lam (A.chiF a b d.1.N d'.1.N)‖ = 1)
    (Ξ₀ : HomE X.E a b → X.K) (hΞ : OffDatum cA (p * g) d.1.N d'.1.N SG w Ξ₀)
    (hm : PtMom A a b lam ι un (star (ϖ : X.E) / (ϖ : X.E))) (hnorm : ∀ P ∈ divs ϖ, Ideal.absNorm P.asIdeal = p)
    (N'' : Submodule (𝓞 X.E) (Sp X.E b)) (hN'' : IsSdLat N'')
    (hc : (∀ y ∈ d'.1.N, (ϖ : X.E) • y ∈ N'') ∧ (∀ y ∈ N'', star (ϖ : X.E) • y ∈ d'.1.N) ∧
      ∀ (P : ↥(divs ϖ)) (y : Sp X.E b), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d'.1.at P.1 ∧ d'.1.f P y = 0)
    (κ : ℂ) (hκ : κ ∈ TaylorLogMetric.Qbar) (hκ1 : ‖TaylorLogMetric.lamC lam κ‖ ^ 2 ≤ (p : ℝ) ^ ((divs ϖ).card * a))
    (hmove : ∀ R : Finset (HomE X.E a b), IsReps (per A d.1.N d'.1.N).toAddSubgroup (per A d.1.N N'').toAddSubgroup R →
      ∀ z, ∑ y ∈ R, Wx A y (A.e a b d.1.N d'.1.N) z = ((Real.sqrt (R.card : ℝ) : ℝ) : ℂ) * κ * A.e a b d.1.N N'' z) :
    InIntClosure (suppP d.1 d'.1) (fun x m => ((p : ℂ_[p]) ^ ((divs ϖ).card * a))⁻¹ * ptTab ι un x m)
      (RatIdx A S cA (p * g) d.1.N d'.1.N fun x => phiT X.K d.1 d'.1 x * Ξ₀ x)
      fun m => ι (jetSum A S cA (p * g) d.1.N d'.1.N (fun x => phiT X.K d.1 d'.1 x * Ξ₀ x) m) := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := h.sub
  have hN : IsSdLat d.1.N := ⟨d.2.lat, d.2.uni⟩
  have hN' : IsSdLat d'.1.N := ⟨d'.2.lat, d'.2.uni⟩
  obtain ⟨hAA, -, -, -, l4, -⟩ := _root_.GlobalTheory.MomT.HalfIncl.half_inclusions X A a b S SG ϖ p g cA d.1.N d'.1.N h hN hN'
  have hFG : A.AA.FG := h.2.1.2.2.2.2.1
  have hU : A.AAUnit S := h.2.1.2.2.2.1
  set r : X.E := ((cA * g : ℕ) : X.E) * star (ϖ : X.E) with hr
  have hrO : ∀ (W : Type) [AddCommGroup W] [Module X.E W] [Module (𝓞 X.E) W] [IsScalarTower (𝓞 X.E) X.E W] (y : W),
      r • y = (((cA * g : ℕ) : 𝓞 X.E) * X.conjO ϖ) • y := by
    intro W _ _ _ _ y
    rw [← algebraMap_smul X.E (((cA * g : ℕ) : 𝓞 X.E) * X.conjO ϖ) y, map_mul, map_natCast]
    rfl
  have hC : ∀ y ∈ (smulLat r (per A d.1.N d'.1.N ⊓ per A d.1.N N'')).toAddSubgroup,
      y ∈ homAt S d.1.N d'.1.N ∧ y ∈ mulLat (p * g) (homAt SG d.1.N d'.1.N) ∧
      ∀ P : ↥(divs ϖ), ∀ v ∈ d.1.at P.1, y v ∈ d'.1.at P.1 ∧ d'.1.f P (y v) = 0 := by
    intro y hy
    obtain ⟨m, hm', rfl⟩ := (mem_smulLat _ _ _).1 hy
    refine ⟨?_, (l4 m hm'.1).2.2.1, fun P v hv => (hc.2.2 P _).1 ?_⟩
    · rw [hrO]; exact Submodule.smul_mem _ _ (l4 m hm'.1).1
    · rw [LinearMap.smul_apply, hrO]
      exact Submodule.smul_mem _ _
        (((_root_.GlobalTheory.MomT.LatFin.per_lattice_facts X A a b d.1.N N'' hFG hAA hN hN'').2.2.2 P.1 (hU P.1 (s1 P.2)) m).1 (le_locP _ _ hm'.2) v hv)
  obtain ⟨J, hJ⟩ := (_root_.GlobalTheory.RepsMod.reps_facts (HomE X.E a b)).1 (mulLat (p * g) (homAt S d.1.N d'.1.N)).toAddSubgroup
    (smulLat r (per A d.1.N d'.1.N ⊓ per A d.1.N N'')).toAddSubgroup (by
      have hf := _root_.GlobalTheory.MomT.finite_quot_divLat_mulLat_homAt X.E a b S d.1.N d'.1.N cA (p * g) hN.1 hN'.1 s4 s5
      have h1 : (mulLat (p * g) (homAt S d.1.N d'.1.N)).toAddSubgroup.relIndex
          (divLat cA (homAt S d.1.N d'.1.N)).toAddSubgroup ≠ 0 := @AddSubgroup.index_ne_zero_of_finite _ _ _ hf
      intro h0
      exact h1 (AddSubgroup.relIndex_eq_zero_of_le_right
        (fun y hy => Submodule.smul_mem (homAt S d.1.N d'.1.N) (cA : 𝓞 X.E) (hC y hy).1) h0))
  refine assemble_phi h hlam hw d d' hχ hχ1 Ξ₀ hΞ _ hC J hJ _ _ fun x hx hs => ?_
  refine clo_congr (_root_.GlobalTheory.MomT.CosetSum.moments_coset_sum X A a b S SG ϖ p g cA d.1.N d'.1.N N'' lam ι un κ _ h hN hN' hN'' hc.1 hc.2.1 hm hκ hκ1
    (_root_.GlobalTheory.MomT.IdxBound.relIndex_per_dvd X A a b SG₂ ϖ p d.1.N d' N'' hFG hAA (fun P hP => hU P (s1 hP)) h.ne_zero hnorm hN hN''
      (fun P hP => hstd ⟨P, hP⟩) hc) hmove J hJ x hx fun P hP v hv => (hs ⟨P, hP⟩ v hv).1)
    (fun t ht P y hy hf => ?_) subset_rfl fun _ _ => rfl
  refine _root_.GlobalTheory.AdjMem.adj_per_mem X A a b d.1.N N'' P.1 hN hN'' (h.2.2.1 _ ?_) t ht y ((hc.2.2 P y).2 ⟨hy, hf⟩)
  have h0 : X.conjO ϖ ≠ 0 := by
    intro h0
    have := h.2.2.2.2.2.1
    rw [h0, mul_zero] at this
    exact h.2.2.2.2.1.ne_zero (by exact_mod_cast this.symm)
  rw [mem_divs h0, mem_conjP]
  have : cO X.E (X.conjO ϖ) = ϖ := conjO_conjO ϖ
  rw [this]
  exact (mem_divs h.ne_zero _).1 P.2

end Types

section Main

theorem norm_ratio_le {X : Fields} {p : ℕ} [Fact p.Prime] (ρ : X.E →+* ℂ_[p]) {ϖ : 𝓞 X.E}
    (h : ϖ * X.conjO ϖ = (p : 𝓞 X.E)) : ‖(ρ ((ϖ : X.E) / star (ϖ : X.E)))⁻¹‖ ≤ p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 : ‖ρ (ϖ : X.E)‖ * ‖ρ (star (ϖ : X.E))‖ = (p : ℝ)⁻¹ := by
    have e : (ϖ : X.E) * star (ϖ : X.E) = (p : X.E) := by
      have := congrArg (algebraMap (𝓞 X.E) X.E) h
      rwa [map_mul, map_natCast] at this
    rw [← norm_mul, ← map_mul, e, map_natCast, ← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]
  have h2 : ‖ρ (star (ϖ : X.E))‖ ≤ 1 :=
    GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int ρ (X.conjO ϖ).isIntegral_coe)
  have h0 : ‖ρ (ϖ : X.E)‖ ≠ 0 := left_ne_zero_of_mul (h1 ▸ (inv_pos.2 hp).ne')
  have h3 : ‖ρ (star (ϖ : X.E))‖ / ‖ρ (ϖ : X.E)‖ = ‖ρ (star (ϖ : X.E))‖ ^ 2 * p := by
    have : (p : ℝ) * (‖ρ (ϖ : X.E)‖ * ‖ρ (star (ϖ : X.E))‖) = 1 := by rw [h1, mul_inv_cancel₀ hp.ne']
    rw [div_eq_iff h0]
    linear_combination (-‖ρ (star (ϖ : X.E))‖) * this
  rw [map_div₀, inv_div, norm_div, h3]
  exact mul_le_of_le_one_left hp.le (pow_le_one₀ (norm_nonneg _) h2)

end Main

end GlobalTheory.MomT

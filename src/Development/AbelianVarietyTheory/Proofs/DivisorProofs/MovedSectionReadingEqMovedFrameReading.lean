module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticHeckeCharCMEqIdeleInfiniteSignFiniteTri
public import Development.AutomorphicArithmetic.WeightCongruences.NormRootOfUnityQuadraticSubfield
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRestrictionExtendByZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointsAllNormalisationsFamilyUnif

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.WeightCongruences.DvdNormSubOneOfIdempotentInterpolationRelNormOne
open NumberField IsDedekindDomain

private theorem prod_interp_mod {Ω ι : Type*} [CommRing Ω] (n : ℕ) (e t : Ω) (he : e * e - e = n * t)
    (hei : IsIntegral ℤ e) (hti : IsIntegral ℤ t) (f g : ι → Ω) (hf : ∀ i, IsIntegral ℤ (f i))
    (hg : ∀ i, IsIntegral ℤ (g i)) (s : Finset ι) :
    ∃ z, IsIntegral ℤ z ∧ ∏ i ∈ s, (e * f i + (1 - e) + n * g i) = e * ∏ i ∈ s, f i + (1 - e) + n * z := by
  classical
  have hn : IsIntegral ℤ (n : Ω) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := Ω) (x := (n : ℤ)))
  induction s using Finset.induction_on with
  | empty => exact ⟨0, isIntegral_zero, by simp⟩
  | insert a s ha ih =>
    obtain ⟨z, hz, hprod⟩ := ih
    set P := ∏ i ∈ s, f i with hP
    have hPi : IsIntegral ℤ P := IsIntegral.prod _ fun i _ => hf i
    refine ⟨t * f a * P - t * f a - t * P + t + g a * (e * P + (1 - e)) +
      z * (e * f a + (1 - e)) + n * g a * z, ?_, ?_⟩
    · have h1e : IsIntegral ℤ (1 - e) := isIntegral_one.sub hei
      exact ((((((hti.mul (hf a)).mul hPi).sub (hti.mul (hf a))).sub (hti.mul hPi)).add hti).add
        ((hg a).mul ((hei.mul hPi).add h1e))).add (hz.mul ((hei.mul (hf a)).add h1e)) |>.add
        ((hn.mul (hg a)).mul hz)
    · rw [Finset.prod_insert ha, Finset.prod_insert ha, hprod]
      linear_combination (f a * P - f a - P + 1) * he

private theorem descend_mod {F Ω : Type*} [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (n : ℕ) (a : F) (z : Ω)
    (hz : IsIntegral ℤ z) (h : algebraMap F Ω a = 1 + n * z) :
    ∃ w : F, IsIntegral ℤ w ∧ a = 1 + n * w := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, isIntegral_zero, ?_⟩
    apply (algebraMap F Ω).injective
    simpa using h
  · have hnF : (n : F) ≠ 0 := by exact_mod_cast hn.ne'
    refine ⟨(a - 1) / n, ?_, by field_simp; ring⟩
    have hmap : algebraMap F Ω ((a - 1) / n) = z := by
      have hnΩ : (n : Ω) ≠ 0 := by
        rw [← map_natCast (algebraMap F Ω)]
        exact (map_ne_zero _).mpr hnF
      rw [map_div₀, map_sub, map_one, map_natCast, h]
      field_simp
      ring
    rw [← isIntegral_algebraMap_iff (B := Ω), hmap]
    exact hz

theorem UpperTheory.dvd_norm_sub_one_of_idempotent_interpolation_relNorm_one :
    ∀ (E : Type) [Field E] [NumberField E] (K : IntermediateField ℚ E) (n : ℕ) (e t δ y : 𝓞 E), (e : E) ∈ K → e * e - e = n * t →
      Algebra.norm K (δ : E) = 1 → (n : ℤ) ∣ Algebra.norm ℤ (e * δ + (1 - e) + n * y : 𝓞 E) - 1 := by
  intro E _ _ K n e t δ y heK he hδ
  classical
  let Ω := AlgebraicClosure E
  have hint : ∀ u : 𝓞 E, IsIntegral ℤ (u : E) := fun u => u.2
  have hintΩ : ∀ (u : 𝓞 E) (σ : E →ₐ[K] Ω), IsIntegral ℤ (σ u) := fun u σ =>
    (hint u).map (σ.restrictScalars ℚ).toRingHom.toIntAlgHom
  have hσe : ∀ σ : E →ₐ[K] Ω, σ (e : E) = algebraMap E Ω e := by
    intro σ
    have h := σ.commutes (⟨e, heK⟩ : K)
    rw [IsScalarTower.algebraMap_apply K E Ω] at h
    exact h
  have heE : ((e : E) * e - e) = n * (t : E) := by
    have h := congrArg (fun u : 𝓞 E => (u : E)) he
    simpa using h
  have heΩ : algebraMap E Ω e * algebraMap E Ω e - algebraMap E Ω e = n * algebraMap E Ω t := by
    have h := congrArg (algebraMap E Ω) heE
    simpa using h
  obtain ⟨z, hz, hprod⟩ := prod_interp_mod n (algebraMap E Ω e) (algebraMap E Ω t) heΩ
    ((hint e).map (IsScalarTower.toAlgHom ℤ E Ω)) ((hint t).map (IsScalarTower.toAlgHom ℤ E Ω))
    (fun σ : E →ₐ[K] Ω => σ δ) (fun σ => σ y) (fun σ => hintΩ δ σ) (fun σ => hintΩ y σ) Finset.univ
  have hδΩ : ∏ σ : E →ₐ[K] Ω, σ δ = 1 := by
    rw [← Algebra.norm_eq_prod_embeddings, hδ, map_one]
  have hK : algebraMap K Ω (Algebra.norm K ((e * δ + (1 - e) + n * y : 𝓞 E) : E)) = 1 + n * z := by
    rw [Algebra.norm_eq_prod_embeddings]
    have hσ : ∀ σ : E →ₐ[K] Ω, σ ((e * δ + (1 - e) + n * y : 𝓞 E) : E) =
        algebraMap E Ω e * σ δ + (1 - algebraMap E Ω e) + n * σ y := by
      intro σ
      push_cast
      rw [map_add (f := _), map_add (f := _), map_mul, map_sub, map_one, map_mul, map_natCast, hσe]
    simp_rw [hσ]
    rw [hprod, hδΩ]
    ring
  obtain ⟨w, hw, hwK⟩ := descend_mod n _ z hz hK
  let Ω₂ := AlgebraicClosure K
  obtain ⟨z₂, hz₂, hprod₂⟩ := prod_interp_mod (Ω := Ω₂) n 1 0 (by simp) isIntegral_one isIntegral_zero
    (fun _ : K →ₐ[ℚ] Ω₂ => 1) (fun τ => τ w) (fun _ => isIntegral_one)
    (fun τ => hw.map τ.toRingHom.toIntAlgHom) Finset.univ
  simp only [one_mul, sub_self, add_zero, Finset.prod_const_one] at hprod₂
  have hQ : algebraMap ℚ Ω₂ (Algebra.norm ℚ (1 + n * w)) = 1 + n * z₂ := by
    rw [Algebra.norm_eq_prod_embeddings]
    simp_rw [map_add (f := _), map_one, map_mul, map_natCast]
    exact hprod₂
  obtain ⟨w₂, hw₂, hw₂Q⟩ := descend_mod n _ z₂ hz₂ hQ
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hw₂
  have hnorm : ((Algebra.norm ℤ (e * δ + (1 - e) + n * y : 𝓞 E) : ℤ) : ℚ) = 1 + n * m := by
    rw [Algebra.coe_norm_int, ← Algebra.norm_norm (S := K), hwK, hw₂Q, ← hm]
    simp
  have hZ : Algebra.norm ℤ (e * δ + (1 - e) + n * y : 𝓞 E) = 1 + n * m := by
    exact_mod_cast hnorm
  exact ⟨m, by rw [hZ]; ring⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionSqMultiplierAlongIsometryMove
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceW0PowFourEven
open NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AdaptedDet

namespace GlobalTheory.AdaptedDetSign

theorem det_interp_gen {E : Type} [Field E] [NumberField E] {r : ℕ} (n : ℕ) (hn : n ≠ 0)
    (e t δ : 𝓞 E) (he0 : e ≠ 0) (he : e * e - e = n * t)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (g : Matrix (Fin r) (Fin r) E) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hg : ∀ v ∈ Λ, g *ᵥ v ∈ Λ) (hdet : g.det = (δ : E)) :
    ∃ y : 𝓞 E, ((e : E) • g + (1 - (e : E)) • (1 : Matrix (Fin r) (Fin r) E)).det =
      ((e * δ + (1 - e) + n * y : 𝓞 E) : E) := by
  classical
  let K := AlgebraicClosure E
  have hinj := (algebraMap E K).injective
  have hn' : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hint : ∀ x : 𝓞 E, IsIntegral ℤ (algebraMap E K (x : E)) := fun x =>
    x.isIntegral_coe.algebraMap
  have hroots : ∀ μ ∈ (g.map (algebraMap E K)).charpoly.roots, IsIntegral ℤ μ := by
    intro μ hμ
    have := CongruenceDet.isIntegral_root (R := 𝓞 E) (M := 1) one_ne_zero Λ g hfg hspan
      (fun v hv => ⟨g *ᵥ v - v, sub_mem (hg v hv) hv, by simp⟩) μ
      (Polynomial.isRoot_of_mem_roots hμ)
    have h2 : IsIntegral ℤ ((μ - 1) / ((1 : ℕ) : K)) := isIntegral_trans (A := 𝓞 E) _ this
    simpa using h2.add isIntegral_one
  obtain ⟨y, hy, h⟩ := prod_interp (n : K) (algebraMap E K e) (algebraMap E K t)
    (by
      have := congrArg (fun x : 𝓞 E => algebraMap E K (x : E)) he
      simpa using this) (hint e) (hint t) _ hroots
  rw [← det_smul_add _ _ _ (by simpa using he0), ← Matrix.det_eq_prod_roots_charpoly,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet] at h
  set d := ((e : E) • g + (1 - (e : E)) • (1 : Matrix (Fin r) (Fin r) E)).det with hd
  have hd' : algebraMap E K d = algebraMap E K ((e : E) * (δ : E) + (1 - (e : E))) + n * y := by
    rw [hd, RingHom.map_det]
    have : (algebraMap E K).mapMatrix ((e : E) • g + (1 - (e : E)) • (1 : Matrix (Fin r) (Fin r) E))
        = algebraMap E K e • (algebraMap E K).mapMatrix g + (1 - algebraMap E K e) • 1 := by
      generalize (e : E) = x
      ext i j
      by_cases h : i = j <;> simp [h, -algebraMap_smul]
    rw [this, h, map_add (f := _), map_mul, map_sub, map_one]
  have hy' : IsIntegral ℤ ((d - ((e : E) * (δ : E) + (1 - (e : E)))) / n) := by
    rw [← isIntegral_algebraMap_iff (B := K), map_div₀, map_sub, map_natCast, hd',
      add_sub_cancel_left, mul_div_cancel_left₀ _ hn']
    exact hy
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, (z : E) = (d - ((e : E) * (δ : E) + (1 - (e : E)))) / n := ⟨⟨_, hy'⟩, rfl⟩
  refine ⟨z, ?_⟩
  have hn'' : (n : E) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h1 : ((e * δ + (1 - e) + n * z : 𝓞 E) : E) =
      (e : E) * (δ : E) + (1 - (e : E)) + n * (z : E) := by simp
  rw [h1, hz]
  field_simp
  ring

theorem norm_one_add_two {E : Type} [Field E] [NumberField E] (u : 𝓞 E) :
    (4 : ℤ) ∣ Algebra.norm ℤ (1 + 2 * u : 𝓞 E) - (1 + 2 * Algebra.trace ℤ (𝓞 E) u) := by
  classical
  have h2 : (2 * u : 𝓞 E) = (2 : ℤ) • u := by simp
  rw [Algebra.norm_eq_matrix_det (RingOfIntegers.basis E), map_add (f := _), map_one, h2, map_smul,
    Matrix.det_one_add_smul, Algebra.trace_eq_matrix_trace (RingOfIntegers.basis E)]
  generalize Polynomial.eval (2 : ℤ) _ = c
  exact ⟨c, by ring⟩

theorem det_interp_pm {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (D : Datum H) {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ D.La)
    (gam : D.La ≃ₗ[𝓞 E] D.La) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (A : Matrix (Fin r) (Fin r) E)
    (hinj : Function.Injective φ) (hspan : Submodule.span E (Set.range φ) = ⊤)
    (hA : ∀ x, φ (gam x) = A *ᵥ φ x)
    (hdet : A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E))
    (T : D.La →ₗ[ℤ] D.La) (hT : ∀ x, T x = H.w0 ^ 4 • gam x + (x - H.w0 ^ 4 • x)) :
    (4 : ℤ) ∣ (LinearMap.toMatrix b b T).det - 1 := by
  have hsm : ∀ (a : 𝓞 E) (x : D.La), φ (a • x) = (a : E) • φ x := fun a x => by
    rw [map_smul]; rfl
  haveI := D.fin
  have hfg : (LinearMap.range φ).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map φ
  obtain ⟨he0, t, ht⟩ := cmUnit_pow_four_idempotent_mod_eight H
  have h := det_eq_norm b φ hinj hspan T
    (((H.w0 ^ 4 : 𝓞 E) : E) • A + (1 - ((H.w0 ^ 4 : 𝓞 E) : E)) • 1) (by
      intro x
      rw [hT, map_add (f := _), map_sub, hsm, hsm, Matrix.add_mulVec, Matrix.smul_mulVec,
        Matrix.smul_mulVec, hA, Matrix.one_mulVec, sub_smul, one_smul])
  have hst : ∀ v ∈ LinearMap.range φ, A *ᵥ v ∈ LinearMap.range φ := by
    rintro _ ⟨x, rfl⟩
    exact ⟨gam x, hA x⟩
  rcases hdet with hdet | ⟨hdet, h4⟩
  · obtain ⟨y, hy⟩ := det_interp_gen 8 (by norm_num) _ t 1 he0 ht (LinearMap.range φ) A hfg hspan
      hst (by simpa using hdet)
    rw [hy, ← Algebra.coe_norm_int] at h
    have h1 : (H.w0 ^ 4 * 1 + (1 - H.w0 ^ 4) + (8 : ℕ) * y : 𝓞 E) = 1 + 2 * ((4 : ℤ) • y) := by
      rw [zsmul_eq_mul]
      push_cast
      ring
    have h2 := norm_one_add_two ((4 : ℤ) • y)
    rw [Int.cast_injective h, h1]
    rw [map_zsmul, smul_eq_mul] at h2
    omega
  · obtain ⟨m, hm, hpow⟩ := hdet
    have hi : IsIntegral ℤ A.det := IsIntegral.of_pow hm (hpow ▸ isIntegral_one)
    obtain ⟨δ, hδ⟩ : ∃ δ : 𝓞 E, (δ : E) = A.det := ⟨⟨_, hi⟩, rfl⟩
    obtain ⟨y, hy⟩ := det_interp_gen 8 (by norm_num) _ t δ he0 ht (LinearMap.range φ) A hfg hspan hst hδ.symm
    rw [hy, ← Algebra.coe_norm_int] at h
    have hrt : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
      simpa using this
    have hN := UpperTheory.norm_root_of_unity_quadratic_subfield E (H.rt : E) H.d H.d_prime (by have := H.d_mod; omega) hrt h4 (δ : E)
      ⟨m, hm, by rw [hδ, hpow]⟩
    have hw : ((H.w0 ^ 4 : 𝓞 E) : E) ∈ IntermediateField.adjoin ℚ {(H.rt : E)} := by
      have h2 : (H.w0 : E) = (1 + (H.rt : E)) / ((2 : ℕ) : E) := by
        have h3 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
          have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
          rwa [map_mul, map_add, map_one, map_ofNat] at this
        rw [← h3]
        push_cast
        ring
      have h4' : ((H.w0 ^ 4 : 𝓞 E) : E) = (H.w0 : E) ^ 4 := by push_cast; rfl
      rw [h4', h2]
      exact pow_mem (div_mem (add_mem (one_mem _) (IntermediateField.mem_adjoin_simple_self _ _)) (natCast_mem _ 2)) 4
    have h8 := UpperTheory.dvd_norm_sub_one_of_idempotent_interpolation_relNorm_one E _ 8 _ t δ y hw ht hN
    rw [Int.cast_injective h]
    exact (show (4 : ℤ) ∣ ((8 : ℕ) : ℤ) by norm_num).trans h8

theorem blocks_det_mod_four : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (g r : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (gam : D.La ≃ₗ[𝓞 E] D.La) (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (A : Matrix (Fin r) (Fin r) E), (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inl k) 1) = bas (Pi.single (Sum.inl k) 1) + (8 : ℕ) • e) ∧ (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inr k) 1) = (8 : ℕ) • e) → Function.Injective φ → Submodule.span E (Set.range φ) = ⊤ → (∀ a, φ (gam a) = A *ᵥ φ a) → (A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → (∀ u v, N u v = bas.symm (gam (bas (Pi.single v 1))) u) → (∀ i j, (8 : ℤ) ∣ N (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ N (Sum.inr i) (Sum.inl j)) ∧ (4 : ℤ) ∣ N.toBlocks₁₁.det - 1 := by
  intro E _ _ _ H D g r bas gam N φ A ⟨hl, hr⟩ hinj hspan hA hdet hN
  classical
  let π : D.La →+ (Fin g ⊕ Fin g → ZMod 8) :=
    { toFun := fun x u => ((bas.symm x u : ℤ) : ZMod 8)
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  have hπ : ∀ x u, π x u = ((bas.symm x u : ℤ) : ZMod 8) := fun _ _ => rfl
  have h8 : ∀ x, π ((8 : ℕ) • x) = 0 := fun x => by
    rw [map_nsmul]
    ext u
    rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  have hπb : ∀ v u, π (bas (Pi.single v 1)) u = if u = v then 1 else 0 := fun v u => by
    simp [hπ, Pi.single_apply]

  have he : ∀ x u, π (H.w0 ^ 4 • x) u = Sum.elim (fun _ => π x u) (fun _ => 0) u := by
    intro x u
    obtain ⟨c, rfl⟩ := bas.surjective x
    induction c using Pi.single_induction with
    | zero => cases u <;> simp
    | add a b ha hb => rw [map_add (f := _), smul_add, map_add (f := _), map_add (f := _), Pi.add_apply, ha, hb]; cases u <;> simp
    | single v n =>
      have : (Pi.single v n : Fin g ⊕ Fin g → ℤ) = n • Pi.single v 1 := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [this, map_zsmul, smul_comm, map_zsmul, map_zsmul, Pi.smul_apply, Pi.smul_apply]
      cases v with
      | inl k =>
        obtain ⟨e, h⟩ := hl k
        rw [h, map_add (f := _), h8, add_zero]
        cases u <;> simp [hπb]
      | inr k =>
        obtain ⟨e, h⟩ := hr k
        rw [h, h8]
        cases u <;> simp [hπb]
  have hN' : ∀ u v, ((N u v : ℤ) : ZMod 8) = π (gam (bas (Pi.single v 1))) u := fun u v => by
    rw [hN, hπ]
  constructor
  · intro i j
    constructor
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
      obtain ⟨e, h⟩ := hr j
      have h1 := he (gam (bas (Pi.single (Sum.inr j) 1))) (Sum.inl i)
      rw [← map_smul, h, map_nsmul, h8] at h1
      rw [hN']
      exact h1.symm
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
      obtain ⟨e, h⟩ := hl j
      have h1 := he (gam (bas (Pi.single (Sum.inl j) 1))) (Sum.inr i)
      rw [← map_smul, h, map_add (f := _), map_nsmul, map_add (f := _), h8, add_zero] at h1
      rw [hN']
      exact h1
  · let b : Module.Basis (Fin g ⊕ Fin g) ℤ D.La := (Pi.basisFun ℤ _).map bas
    let T : D.La →ₗ[𝓞 E] D.La :=
      H.w0 ^ 4 • gam.toLinearMap + (LinearMap.id - H.w0 ^ 4 • LinearMap.id)
    have hT : ∀ x, T.restrictScalars ℤ x = H.w0 ^ 4 • gam x + (x - H.w0 ^ 4 • x) := fun x => rfl
    have h := det_interp_pm D b gam φ A hinj hspan hA hdet (T.restrictScalars ℤ) hT
    suffices h8 : (8 : ℤ) ∣ N.toBlocks₁₁.det - (LinearMap.toMatrix b b (T.restrictScalars ℤ)).det by
      omega
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
    rw [Int.cast_sub, sub_eq_zero, ← eq_intCast (Int.castRingHom (ZMod 8)),
      ← eq_intCast (Int.castRingHom (ZMod 8)), RingHom.map_det, RingHom.map_det]
    have hent : ∀ u v, (Int.castRingHom (ZMod 8)).mapMatrix
        (LinearMap.toMatrix b b (T.restrictScalars ℤ)) u v =
        π (T.restrictScalars ℤ (bas (Pi.single v 1))) u := fun u v => by
      simp [LinearMap.toMatrix_apply, b, hπ]
    have hblk : (Int.castRingHom (ZMod 8)).mapMatrix
        (LinearMap.toMatrix b b (T.restrictScalars ℤ)) =
        Matrix.fromBlocks ((Int.castRingHom (ZMod 8)).mapMatrix N.toBlocks₁₁)
          (Matrix.of fun i j => (Int.castRingHom (ZMod 8)).mapMatrix
            (LinearMap.toMatrix b b (T.restrictScalars ℤ)) (Sum.inl i) (Sum.inr j)) 0 1 := by
      ext u v
      rcases u with i | i <;> rcases v with j | j
      · rw [hent, hT, map_add (f := _), map_sub, Pi.add_apply, Pi.sub_apply, he, he]
        simp [Matrix.toBlocks₁₁, hN']
      · rfl
      · rw [hent, hT, map_add (f := _), map_sub, Pi.add_apply, Pi.sub_apply, he, he]
        simp [hπb]
      · rw [hent, hT, map_add (f := _), map_sub, Pi.add_apply, Pi.sub_apply, he, he]
        simp [hπb, Matrix.one_apply]
    rw [hblk, Matrix.det_fromBlocks_zero₂₁, det_one, mul_one]

end GlobalTheory.AdaptedDetSign
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionSqMultiplierAlongIsometryMove
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

noncomputable section

namespace GlobalTheory.GeoLevel

theorem exists_entire_ratio {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (W : ι → Set V)
    (hW : ∀ i, IsOpen (W i)) (hcov : ∀ w, ∃ i, w ∈ W i) (f f' : ι → V → ℂ) (c : ι → ι → V → ℂ)
    (hd : ∀ i, DifferentiableOn ℂ (f i) (W i)) (hd' : ∀ i, DifferentiableOn ℂ (f' i) (W i))
    (hn : ∀ i, ∀ w ∈ W i, f i w ≠ 0) (hn' : ∀ i, ∀ w ∈ W i, f' i w ≠ 0)
    (hc : ∀ i j w, w ∈ W i → w ∈ W j → f i w = c i j w * f j w)
    (hc' : ∀ i j w, w ∈ W i → w ∈ W j → f' i w = c i j w * f' j w) :
    ∃ ρ : V → ℂ, Differentiable ℂ ρ ∧ (∀ w, ρ w ≠ 0) ∧ ∀ i, ∀ w ∈ W i, f' i w = ρ w * f i w := by
  choose J hJ using hcov
  have key : ∀ i, ∀ w ∈ W i, f' i w = f' (J w) w / f (J w) w * f i w := fun i w h => by
    have := hn _ _ (hJ w)
    rw [hc i (J w) w h (hJ w), hc' i (J w) w h (hJ w)]
    field_simp
  refine ⟨_, fun w => ?_, fun w => div_ne_zero (hn' _ _ (hJ w)) (hn _ _ (hJ w)), key⟩
  refine (((hd' (J w)).mul ((hd (J w)).inv (hn _))).congr fun w' h => ?_).differentiableAt ((hW _).mem_nhds (hJ w))
  exact (eq_div_of_mul_eq (hn _ _ h) (key _ _ h).symm).trans (div_eq_mul_inv _ _)


open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi in
theorem det_eq_sq_mul_of_theta_ratio (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La)
    (gam : D.La ≃ₗ[𝓞 E] D.La) (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (P P' : D.La →+ (Fin g → ℂ))
    (h h' τ τ' : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (ρ : (Fin g → ℂ) → ℂ) (κ : ℂ)
    (hbas : ∀ a b, D.EF (bas a) (bas b) = -omegaStd a b) (hiso : ∀ a b, D.EF (gam a) (gam b) = D.EF a b)
    (hN : ∀ u v, N u v = bas.symm (gam (bas (Pi.single v 1))) u) (hP : ∀ a, P' a = P (gam a))
    (hn : ∀ k, h *ᵥ P (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧
      h *ᵥ P (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1)
    (hn' : ∀ k, h' *ᵥ P' (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧
      h' *ᵥ P' (bas (Pi.single (Sum.inr k) 1)) = τ' *ᵥ Pi.single k 1)
    (hτ : τ ∈ SiegelH (Fin g)) (hτ' : τ' ∈ SiegelH (Fin g)) (hu : IsUnit h.det)
    (h8 : ∀ i j, (8 : ℤ) ∣ N (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ N (Sum.inr i) (Sum.inl j))
    (hdet : (4 : ℤ) ∣ N.toBlocks₁₁.det - 1)
    (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2)
    (hρd : Differentiable ℂ ρ) (hρ0 : ∀ z, ρ z ≠ 0) (hρ1 : ρ 0 = 1) (hκ : κ ≠ 0)
    (hrel : ∀ z, thetaChar τ' c₁ c₂ (h' *ᵥ z) * ρ z = κ * thetaChar τ c₁ c₂ (h *ᵥ z)) :
    h.det = κ ^ 2 * h'.det := by
  obtain ⟨ga, hga, hgae, hτe, hhe, hde⟩ := PeriodChange.period_change E H D g bas gam N
    P P' h h' τ τ' hbas hiso hN hP hn hn' hτ hτ' hu
  have h8ga : ∀ i j, (8 : ℤ) ∣ ga (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ ga (Sum.inr i) (Sum.inl j) :=
    fun i j => by
      rw [hgae]
      exact h8 j i
  have hχ : ((ZMod.χ₄ ((ga.toBlocks₂₂.det : ℤ) : ZMod 4) : ℤ) : ℂ) = 1 := by
    have e : ga.toBlocks₂₂.det = N.toBlocks₁₁.det := by
      rw [hgae, Matrix.toBlocks_fromBlocks₂₂, Matrix.det_transpose]
    have e' : ((ga.toBlocks₂₂.det : ℤ) : ZMod 4) = 1 := by
      have h4 : ((4 : ℕ) : ℤ) ∣ N.toBlocks₁₁.det - 1 := hdet
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).2 h4
      rw [Int.cast_sub, Int.cast_one, sub_eq_zero] at this
      rw [e, this]
    rw [e', map_one, Int.cast_one]
  have hl := GlobalTheory.theta_sq_transform_level_eight g ga hga h8ga
  rw [hχ] at hl
  have dl : Differentiable ℂ (fun w : Fin g → ℂ => h⁻¹ *ᵥ w) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin h⁻¹)).differentiable
  have hκ2 := ThetaRatio.ratio_sq_eq_det_jAut g ga hga h8ga hl c₁ c₂ h₁ h₂ τ hτ
    (fun w => ρ (h⁻¹ *ᵥ w)) κ (hρd.comp dl) (fun w => hρ0 _)
    (by simp only [Matrix.mulVec_zero, hρ1]) hκ (fun w => by
      have := hrel (h⁻¹ *ᵥ w)
      simp only [Matrix.mulVec_mulVec] at this
      rw [hhe, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, hτe] at this
      exact this)
  rw [hde, hκ2]


set_option maxHeartbeats 1600000 in
theorem theta_move_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : GlobalTheory.FrameUnif.ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ b' ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ κ' : ℂ) (y z y' : FrPt Xo c (CAt σ)) (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La) (A : Matrix (Fin r) (Fin r) E) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (t : Ix Dw → (CAt σ)ˣ), κ ≠ 0 → κ' ≠ 0 → IsThetaPt T b κ y → IsThetaPt T b' κ' z → (∀ a a', (F.Di k).EF (gam a) (gam a') = (F.Di k).EF a a') → (∀ a, (M.φ k (gam a) : Fin r → E) = A *ᵥ (M.φ k a : Fin r → E)) → (A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → (∀ a, T.Pf (T.co b') (gam a) = T.Pf (T.co b) a) → (∀ w, (F.ex k (T.Pf (T.co b')) w).left = (F.ex k (T.Pf (T.co b)) w).left ≫ ν.φ) → FrMove ρ ν y y' → FrBor t z y' → Formalism.L2.PjFree.toC (t none : CAt σ) ^ 2 * (κ' ^ 2 * (T.h b).det) = κ ^ 2 * (T.h b').det := by
  intro E _ _ _ H Dw l Xo c σ g e F r M k T b hb b' hb' κ κ' y z y' gam A ρ ν t hκ hκ' hy hz hiso hA hdA hPP hex hmv hbor
  obtain ⟨O, ω, o1, o2, o3, o4, o5⟩ := GlobalTheory.MoveValues.frMove_values E H Dw l Xo c σ ρ ν _ _ hmv
  have hxρ : z.x = y.x ≫ ρ := hbor.1.symm.trans hmv.1
  obtain ⟨hxx, -, hbc⟩ := hbor
  clear hmv
  have hp := T.isPer _ hb
  have hp' := T.isPer _ hb'
  obtain ⟨hu, -, hv⟩ := hy
  obtain ⟨hu', -, hv'⟩ := hz
  obtain ⟨hdu, hsy, hpos, hn⟩ := T.norm b hb
  obtain ⟨hdu', hsy', hpos', hn'⟩ := T.norm b' hb'
  have hd : ∀ j, DifferentiableOn ℂ (fun w => T.fr j (b, w))
      {w | ⊤ ≤ (F.ex k (T.Pf (T.co b)) w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := fun j =>
    (T.fr_hol j).comp (f := fun w => (b, w)) (by fun_prop) (fun w h => ⟨hb, h⟩)
  have hd' : ∀ j, DifferentiableOn ℂ (fun w => T.fr j (b', w))
      {w | ⊤ ≤ (F.ex k (T.Pf (T.co b')) w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := fun j =>
    (T.fr_hol j).comp (f := fun w => (b', w)) (by fun_prop) (fun w h => ⟨hb', h⟩)
  have hne := fun j w => T.fr_ne j b w hb
  have hne' := fun j w => T.fr_ne j b' w hb'
  have hc := fun j j' w => T.fr_coc j j' b w hb
  have hc' := fun j j' w => T.fr_coc j j' b' w hb'
  have h0 := fun j => T.fr_rig j b hb
  have h0' := fun j => T.fr_rig j b' hb'
  generalize T.Pf (T.co b) = P at *
  generalize T.Pf (T.co b') = P' at *
  have hcov2 : ∀ w, ∃ q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι, ⊤ ≤ (F.ex k P w).left ⁻¹ᵁ O q.1 q.2 := fun w => by
    obtain ⟨j, hj⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (F.ex k P w).left
    obtain ⟨j', hj'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB ((F.ex k P w).left ≫ ν.φ)
    exact ⟨(j', j), (o1 _ _ _).2 ⟨hj', hj⟩⟩
  have tr : ∀ j j' w, ⊤ ≤ (F.ex k P w).left ⁻¹ᵁ O j j' →
      ⊤ ≤ (F.ex k P' w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j j' w hw => by
    rw [hex]; exact ((o1 _ _ _).1 hw).1
  have tr2 : ∀ j j' w, ⊤ ≤ (F.ex k P w).left ⁻¹ᵁ O j j' →
      ⊤ ≤ (F.ex k P w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j' := fun j j' w hw => ((o1 _ _ _).1 hw).2
  have hw0 : ∀ w, (F.ex k P w).left ≫ Xo.univ.t.G.hom = (y.x : Sp ℂ ⟶ Xo.X) := fun w =>
    (Over.w (F.ex k P w)).trans hu.symm
  have hw0' : ∀ w, (F.ex k P' w).left ≫ Xo.univ.t.G.hom = (z.x : Sp ℂ ⟶ Xo.X) := fun w =>
    (Over.w (F.ex k P' w)).trans hu'.symm
  have hz0 : (F.ex k P 0).left = (y.x : Sp ℂ ⟶ Xo.X) ≫ eSec Xo.univ.t.G := by
    rw [(F.ex_ker k P hp 0).2 (zero_mem _), hu]
    rfl
  obtain ⟨ρf, hρd, hρ0, hfr⟩ := exists_entire_ratio
    (fun q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι => {w | ⊤ ≤ (F.ex k P w).left ⁻¹ᵁ O q.1 q.2})
    (fun j => GlobalTheory.FamilyUnif_isOpen_ex F k P hp _) hcov2
    (fun q w => valAt' (F.ex k P w).left (O q.1 q.2) (ω q.1 q.2) * T.fr q.2 (b, w)) (fun q w => T.fr q.1 (b', w))
    (fun q q' w => valAt' ((F.ex k P w).left ≫ ν.φ) (Xo.univ.t.PP.L.U q.1 ⊓ Xo.univ.t.PP.L.U q'.1)
      (Xo.univ.t.PP.L.g q.1 q'.1).val)
    (fun q => (((GlobalTheory.ClassUniq.isHolTo_ex F k P hp) (O q.1 q.2) (ω q.1 q.2)).2.mono
      fun w hw => ⟨Set.mem_univ _, hw⟩).mul ((hd q.2).mono fun w hw => tr2 _ _ w hw))
    (fun q => (hd' q.1).mono fun w hw => tr _ _ w hw)
    (fun q w hw => mul_ne_zero (o2 _ _ _ hw) (hne _ w (tr2 _ _ w hw)))
    (fun q w hw => hne' _ w (tr _ _ w hw))
    (fun q q' w h1 h2 => by
      rw [hc q.2 q'.2 w ((top_le_preimage_inf _ _ _).2 ⟨tr2 _ _ w h1, tr2 _ _ w h2⟩), ← mul_assoc,
        o3 _ _ _ _ _ h1 h2, mul_assoc])
    (fun q q' w h1 h2 => by
      have e2 := hc' q.1 q'.1 w ((top_le_preimage_inf _ _ _).2 ⟨tr _ _ _ h1, tr _ _ _ h2⟩)
      rw [hex] at e2
      exact e2)
  have hρ1 : ρf 0 = 1 := by
    obtain ⟨q, hq⟩ := hcov2 0
    have e1 := hfr q 0 hq
    have e2 : T.fr q.1 (b', 0) = valAt' (F.ex k P 0).left (O q.1 q.2) (ω q.1 q.2) * T.fr q.2 (b, 0) := by
      rw [h0 _ (tr2 _ _ 0 hq), h0' _ (tr _ _ 0 hq), ← hu', hxρ]
      exact (o4 _ _ _ _ hz0 hq).trans (congrArg (fun x : Sp ℂ ⟶ Xo.X => _ * valAt' x _ _) hu)
    exact (mul_eq_right₀ (mul_ne_zero (o2 _ _ _ hq) (hne _ 0 (tr2 _ _ 0 hq)))).1 (e1.symm.trans e2)
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by simp [spMap]
  have hbc' : GlobalTheory.Frames.SecBC (RingHom.id ℂ) (Formalism.L2.PjFree.toC (t none : CAt σ)) z.x y'.x z.s y'.s := by
    obtain ⟨pm, p1, p2, p3⟩ := hbc
    exact ⟨pm, p1, by rw [hid]; exact p2.trans (Category.comp_id _).symm, p3⟩
  have ht0 : Formalism.L2.PjFree.toC (t none : CAt σ) ≠ 0 := Units.ne_zero (M₀ := ℂ) (t none)
  generalize Formalism.L2.PjFree.toC (t none : CAt σ) = t₀ at *
  have hrel : ∀ w, thetaChar (T.ta b') T.c₁ T.c₂ (T.h b' *ᵥ w) * ρf w =
      κ / (t₀ * κ') * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ w) := fun w => by
    obtain ⟨q, hq⟩ := hcov2 w
    let p : Over.mk (y.x : Sp ℂ ⟶ Xo.X) ⟶ Xo.univ.t.G := Over.homMk (F.ex k P w).left (hw0 w)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv q.2 w _ e1 e2 (tr2 _ _ w hq)
    have hval := GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hxx _ _ _ hbc'
      (Over.homMk (F.ex k P' w).left (hw0' _)) q.1 _ _
      (fun pt h1 h2 => hv' q.1 w pt h1 h2 (tr _ _ w hq))
      (fun pt h1 h2 => o5 q.1 q.2 _ pt _ e1 e2 (h1.trans (hex w)) h2 hq)
    have hval2 : valAt' (F.ex k P w).left (O q.1 q.2) (ω q.1 q.2) *
        (κ * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ w) * T.fr q.2 (b, w)) =
        t₀ * (κ' * thetaChar (T.ta b') T.c₁ T.c₂ (T.h b' *ᵥ w) * T.fr q.1 (b', w)) :=
      (congrArg (valAt' (F.ex k P w).left (O q.1 q.2) (ω q.1 q.2) * ·) v1).symm.trans hval
    have e3 : T.fr q.1 (b', w) = ρf w * (valAt' (F.ex k P w).left (O q.1 q.2) (ω q.1 q.2) * T.fr q.2 (b, w)) :=
      hfr q w hq
    rw [e3] at hval2
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero ht0 hκ')]
    apply mul_right_cancel₀ (mul_ne_zero (o2 _ _ _ hq) (hne _ w (tr2 _ _ w hq)))
    linear_combination -hval2
  have hAu : IsUnit A.det := by
    rcases hdA with h | ⟨⟨m, hm, h⟩, -⟩
    · rw [h]; exact isUnit_one
    · exact IsUnit.of_pow_eq_one h hm.ne'
  have hdA' : A⁻¹.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A⁻¹.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E) := by
    rw [Matrix.det_nonsing_inv]
    rcases hdA with h | ⟨⟨m, hm, h⟩, h4⟩
    · left; rw [h]; simp
    · right; exact ⟨⟨m, hm, by rw [Ring.inverse_eq_inv', inv_pow, h, inv_one]⟩, h4⟩
  have hiso' : ∀ a a', (F.Di k).EF (gam.symm a) (gam.symm a') = (F.Di k).EF a a' := fun a a' => by
    rw [← hiso, gam.apply_symm_apply, gam.apply_symm_apply]
  let N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
    Matrix.of fun u v => T.bas.symm (gam.symm (T.bas (Pi.single v 1))) u
  obtain ⟨h8, hdet⟩ := GlobalTheory.AdaptedDetSign.blocks_det_mod_four E H (F.Di k) g r T.bas gam.symm N
    ((M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap) A⁻¹ T.adapt
    (Subtype.val_injective.comp (M.φ k).injective)
    (by
      rw [← (M.X k).Λ_span]
      congr 1
      ext v
      exact ⟨fun ⟨a, ha⟩ => ha ▸ (M.φ k a).2, fun hv => ⟨(M.φ k).symm ⟨v, hv⟩,
        congrArg Subtype.val ((M.φ k).apply_symm_apply ⟨v, hv⟩)⟩⟩)
    (fun a => by
      have := hA (gam.symm a)
      rw [gam.apply_symm_apply] at this
      show (M.φ k (gam.symm a) : Fin r → E) = A⁻¹ *ᵥ (M.φ k a : Fin r → E)
      rw [this, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAu, Matrix.one_mulVec])
    hdA' (fun _ _ => rfl)
  have hκ2 := det_eq_sq_mul_of_theta_ratio E H (F.Di k) g T.bas gam.symm N P P' (T.h b) (T.h b') (T.ta b) (T.ta b')
    T.c₁ T.c₂ ρf _ T.sympl hiso' (fun _ _ => rfl) (fun a => by rw [← hPP, gam.apply_symm_apply]) hn hn'
    ⟨hsy, hpos⟩ ⟨hsy', hpos'⟩ hdu h8 hdet T.half₁ T.half₂ hρd hρ0 hρ1
    (div_ne_zero hκ (mul_ne_zero ht0 hκ')) hrel
  rw [hκ2]
  field_simp

end GlobalTheory.GeoLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionSqMultiplierAlongIsometryMoveStatement
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSection_sq_multiplier_along_isometry_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : GlobalTheory.FrameUnif.ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ b' ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ κ' : ℂ) (y z y' : FrPt Xo c (CAt σ)) (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La) (A : Matrix (Fin r) (Fin r) E) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (t : Ix Dw → (CAt σ)ˣ), κ ≠ 0 → κ' ≠ 0 → IsThetaPt T b κ y → IsThetaPt T b' κ' z → (∀ a a', (F.Di k).EF (gam a) (gam a') = (F.Di k).EF a a') → (∀ a, (M.φ k (gam a) : Fin r → E) = A *ᵥ (M.φ k a : Fin r → E)) → (A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → (∀ a, T.Pf (T.co b') (gam a) = T.Pf (T.co b) a) → (∀ w, (F.ex k (T.Pf (T.co b')) w).left = (F.ex k (T.Pf (T.co b)) w).left ≫ ν.φ) → FrMove ρ ν y y' → FrBor t z y' → Formalism.L2.PjFree.toC (t none : CAt σ) ^ 2 * (κ' ^ 2 * (T.h b).det) = κ ^ 2 * (T.h b').det := by
  first | exact @GlobalTheory.GeoLevel.theta_move_sq | exact GlobalTheory.GeoLevel.theta_move_sq | (intros; apply GlobalTheory.GeoLevel.theta_move_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSectionReadingEqMovedFrameReading
set_option autoImplicit false

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

noncomputable section

namespace GlobalTheory.GeoLevel

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}


set_option maxHeartbeats 800000 in
theorem exists_isometry_of_move_deriv {g : ℕ} {σ' : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty)
    {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ) {i : Fin F.n} {P P' : (F.Di i).La →+ (Fin g → ℂ)}
    (p : IsPeriod (F.Di i) ty P) (p' : IsPeriod (F.Di i) ty P') (hu : F.u i P ≫ ρ = F.u i P')
    (hd : ∀ j, ∃ v, IsDerivAt0 (fun z => (F.ex i P z).left) (Pi.single j 1) v ∧
      IsDerivAt0 (fun z => (F.ex i P' z).left) (Pi.single j 1) (v ≫ ν.φ)) :
    ∃ gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i).La, (∀ a b, (F.Di i).EF (gam a) (gam b) = (F.Di i).EF a b) ∧
      (∀ a, P' (gam a) = P a) ∧ ∀ z, (F.ex i P' z).left = (F.ex i P z).left ≫ ν.φ := by
  obtain ⟨gam, h, hiso, hh, hex⟩ := exists_isometry_of_sabMap F ν p p' hu
  have hcol : ∀ j, h.toLinearMap (Pi.single j 1) = Pi.single j 1 := by
    intro j
    obtain ⟨v, hv, d1⟩ := hd j
    have d0 := FibreDeriv.isDerivAt0_comp hv ν.φ
    simp only [← hex] at d0
    have d2 := (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F _ P' p') h.toLinearMap _ _).1 d0
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P' p'
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  have hid : h.toLinearMap = LinearMap.id := by
    refine (Pi.basisFun ℂ (Fin g)).ext fun j => ?_
    rw [Pi.basisFun_apply, hcol, LinearMap.id_apply]
  have hz : ∀ z, h z = z := fun z => LinearMap.congr_fun hid z
  exact ⟨gam, hiso, fun a => by rw [hh, hz], fun z => by rw [← hex, hz]⟩


set_option maxHeartbeats 1600000 in
theorem evR_normUn_move {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)}
    {M : GlobalTheory.FrameUnif.ModelsOf F r} {k : Fin F.n} (T : ThetaData e F M k) {un : (M.X k).dom → FrPt Xo c (CAt σ)}
    (hun : IsNormUn T un) (x x' : (M.X k).dom) (A : Matrix (Fin r) (Fin r) E)
    (hA : A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E))
    (hper : ∀ a, ∃ a', (M.φ k a' : Fin r → E) = A *ᵥ (M.φ k a : Fin r → E) ∧ T.Pf x'.1 a' = T.Pf x.1 a)
    {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ) (hρ : ρ ≫ Xo.s = Xo.s)
    (hx : (un x').x = (un x).x ≫ ρ) (hu : ∀ τ i, (un x').u τ i = (un x).u τ i ≫ ν.φ)
    {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hw : Dom w n) {f f' : Rul Xo c} (hf : f ∈ sec Xo c w n)
    (hff : ∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') :
    evR Xo c f' (un x) = evR Xo c f (un x') := by
  obtain ⟨κ, hκ, hy⟩ := hun x
  obtain ⟨κ', hκ', hy'⟩ := hun x'
  have hb : T.co.symm x.1 ∈ T.co ⁻¹' (M.X k).dom := by
    show T.co (T.co.symm x.1) ∈ (M.X k).dom
    rw [T.co.apply_symm_apply]; exact x.2
  have hb' : T.co.symm x'.1 ∈ T.co ⁻¹' (M.X k).dom := by
    show T.co (T.co.symm x'.1) ∈ (M.X k).dom
    rw [T.co.apply_symm_apply]; exact x'.2
  have p := T.isPer _ hb
  have p' := T.isPer _ hb'
  obtain ⟨gam, hiso, hP, hex⟩ := exists_isometry_of_move_deriv F ν p p'
    ((congrArg (· ≫ ρ) hy.1).symm.trans (hx.symm.trans hy'.1)) (fun j => by
      obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective j
      exact ⟨_, hy.2.1 τ i, hu τ i ▸ hy'.2.1 τ i⟩)
  have hgam : ∀ a, (M.φ k (gam a) : Fin r → E) = A *ᵥ (M.φ k a : Fin r → E) := fun a => by
    obtain ⟨a', h1, h2⟩ := hper a
    have h3 : gam a = a' := p'.2.1 (by rw [hP, T.co.apply_symm_apply, T.co.apply_symm_apply, h2])
    rw [h3, h1]
  obtain ⟨y', hmv⟩ := (GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν hρ (CAt σ) (un x)).1
  obtain ⟨t₀, ht⟩ := exists_frBor_gen (un x') y' (hmv.1.trans hx.symm)
    (funext fun τ => funext fun i => (hmv.2.1 τ i).trans (hu τ i).symm)
  have hC : (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : Formalism.L2.PjFree.relab c σ (e j).1 (M.X k).ξ0 ≠ 0 := (map_ne_zero _).2 (M.X k).ξ0_ne
    positivity
  have d1 := (T.norm _ hb).1.ne_zero
  have d2 := (T.norm _ hb').1.ne_zero
  have k1 : κ ≠ 0 := fun h0 => mul_ne_zero hC d1 (by rw [← hκ, h0]; simp)
  have k2 : κ' ≠ 0 := fun h0 => mul_ne_zero hC d2 (by rw [← hκ', h0]; simp)
  have hth := GlobalTheory.T.thetaSection_sq_multiplier_along_isometry_move E H Dw l Xo c σ g e F r M k T _ hb _ hb' κ κ' (un x) (un x') y' gam A ρ ν _ k1 k2 hy hy'
    hiso hgam hA hP hex hmv ht
  have ht2 : Formalism.L2.PjFree.toC (t₀ : CAt σ) ^ 2 = 1 := by
    rw [hκ, hκ'] at hth
    refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hC d2) d1) ?_
    refine hth.trans ?_
    ring
  have hred : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
  rw [hff _ _ hmv, (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 (CAt σ) hred w n f hf _ _ _ ht,
    wchar_ex_sign Dw _ ht2 (fun _ => rfl) w n hw.2, one_mul]

theorem exists_isMatch_of_models (D : Datum H) {X X' : Data E r} (φ : D.La ≃ₗ[𝓞 E] X.Λ) (φ' : D.La ≃ₗ[𝓞 E] X'.Λ)
    (hΨ : X.Ψ = X'.Ψ) (hp : X.p0 = X'.p0) (hG : X'.Gm = X.Gm) (hξ : X'.ξ0 = X.ξ0)
    (ef : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
    (ef' : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X'.ξ0 * herm X'.Gm (φ' a : Fin r → E) (φ' b))) :
    ∃ δ : GL (Fin r) E, IsMatch X X' δ ∧
      ∀ a, (φ' a : Fin r → E) = (δ : Matrix (Fin r) (Fin r) E) *ᵥ (φ a : Fin r → E) := by
  have hs : ∀ (Y : Data E r) (ψ : D.La ≃ₗ[𝓞 E] Y.Λ), Function.Injective (Y.Λ.subtype ∘ₗ ψ.toLinearMap) ∧
      Submodule.span E (Set.range (Y.Λ.subtype ∘ₗ ψ.toLinearMap)) = ⊤ := fun Y ψ => by
    refine ⟨Subtype.val_injective.comp ψ.injective, ?_⟩
    rw [← Y.Λ_span]
    congr 1
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (ψ a).2
    · intro hv
      exact ⟨ψ.symm ⟨v, hv⟩, congrArg Subtype.val (ψ.apply_symm_apply _)⟩
  have hc : cc (-X.ξ0) = -(-X.ξ0) := by
    have := X.ξ0_im
    unfold cc at this ⊢
    rw [map_neg, this]
  rw [hG, hξ] at ef'
  obtain ⟨δ, h1, h2⟩ := GlobalTheory.IsoExt.exists_unitary_of_isometry E H D D r (-X.ξ0) X.Gm
    (X.Λ.subtype ∘ₗ φ.toLinearMap) (X'.Λ.subtype ∘ₗ φ'.toLinearMap) (LinearEquiv.refl _ _) hc
    ⟨(hs X φ).1, (hs X φ).2, X.Gm_herm, X.Gm_det, ef⟩ ⟨(hs X' φ').1, (hs X' φ').2, X.Gm_herm, X.Gm_det, ef'⟩
    (fun _ _ => rfl)
  have h3 : ∀ a, (φ' a : Fin r → E) = (δ : Matrix (Fin r) (Fin r) E) *ᵥ (φ a : Fin r → E) := h2
  refine ⟨δ, ⟨hΨ, hp, hξ.symm, fun u v => by rw [hG, h1], fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩, h3⟩
  · have := h3 (φ.symm ⟨v, hv⟩)
    rw [φ.apply_symm_apply] at this
    exact this ▸ (φ' _).2
  · have := h3 (φ'.symm ⟨_, hv⟩)
    rw [φ'.apply_symm_apply] at this
    have e := congrArg (fun u => ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u) this
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at e
    rw [e]
    exact (φ _).2

end


set_option maxHeartbeats 3200000 in
theorem rdU_move_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (φD : Dw.La →ₗ[𝓞 E] (Fin r → E)), Function.Injective φD → Submodule.span E (Set.range φD) = ⊤ → (∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φD x) (φD y))) → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ (U.X k).ξ0).im < 0) → ∀ (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k) δ), ((δ : Matrix (Fin r) (Fin r) E).det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ (δ : Matrix (Fin r) (Fin r) E).det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → MoveMatch U U k k h ρ ν → ∀ w n, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n, (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom, Formalism.L2.PjFree.rdU U f' k x = Formalism.L2.PjFree.rdU U f k (lact δ (castFr h.psi x)) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU k φD hinj hsp hEF hneg δ h hdet ρ ν hρ hmm w n hw f hf f' hf' hff x hx
  obtain ⟨g, e, F, ik, φ, ⟨hef, hpin⟩, hnorm⟩ := exists_pinned_of_isUnf hU
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨M, hM, hξ, hMG⟩ := GlobalTheory.ModelsExist.exists_modelsOf GlobalTheory.QNorm.hasseNormSt E H Dw l Xo _ _ _ F r
    (U.X k).ξ0 (U.X k).Gm φD (U.X k).ξ0_im hneg ⟨hinj, hsp, (U.X k).Gm_herm, (U.X k).Gm_det, hEF⟩
  have T : ∀ k, ThetaData e F M k := fun k => (GlobalTheory.T.nonempty_thetaData_flagDomainModels E H Dw l Xo c σ g e F r M hσ hM hξ k).some
  choose un hun using fun k => GlobalTheory.T.exists_normalisedFramedPoint_on_each_component hT E H Dw l Xo c σ g e F r M k (T k)
  have hok : FramesOK e F M un :=
    ⟨fun k => GlobalTheory.T.normalised_points_satisfy_single_frame hT E H Dw l Xo c σ g e F r M k (T k) (un k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_triangularFrame_weightRule hT E H Dw l Xo c σ g e F r M un k (T k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_arithmeticGroup_invariant_sign hT E H Dw l Xo c σ g e F r M un k (T k) hσ hM hξ (hun k),
      fun a n han f hf k => GlobalTheory.T.differentiableOn_readings_normalised_theta_points hB hT E H Dw l Xo c σ g e F r M un k (T k) (hun k) a n han f hf⟩
  have hU₀ := isUnf_built hB E H Dw l Xo c σ g e F r M un hσ hM hξ hok
  obtain ⟨δ₀, h₀, hφ⟩ := exists_isMatch_of_models (F.Di (ik k)) (φ k) (M.φ (ik k))
    (Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hM.type (ik k)).2 τ).symm)
    ((hU.2.1 k).1.trans (hM.type (ik k)).1.symm) (hMG _).1 (hMG _).2 (hef k) (hM.ef _)
  have hPf : ∀ (y : Frame (U.X k).Ψ r) a j, (T (ik k)).Pf (lact δ₀ (castFr h₀.psi y)) a j =
      Formalism.L2.PjFree.perFr (U.X k) y (φ k a : Fin r → E) (Formalism.L2.PjFree.relab c σ (e j).1) (e j).2 := fun y a j => by
    rw [(T (ik k)).per, hφ]
    exact GlobalTheory.T.period_coordinates_frame_rational_isometry E r _ _ δ₀ h₀ y _ _ _
  have key : ∀ y : (U.X k).dom, (un (ik k) ⟨_, h₀.mem_dom y.2⟩).x = (U.un k y).x ∧
      (un (ik k) ⟨_, h₀.mem_dom y.2⟩).u = (U.un k y).u ∧
      (IsUnitFr (U.X k) y.1 → ∃ P : (F.Di (ik k)).La →+ (Fin g → ℂ),
        IsPeriod (F.Di (ik k)) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P ∧ (U.un k y).x = F.u (ik k) P ∧
        NormPin F (ik k) P (U.un k y) ∧ NormPin F (ik k) P (un (ik k) ⟨_, h₀.mem_dom y.2⟩)) := fun y => by
    obtain ⟨P, a1, a2, a3, a4⟩ := hpin k y
    obtain ⟨P', b1, -, b3, b4, b5⟩ := hok.1 (ik k) ⟨_, h₀.mem_dom y.2⟩
    obtain rfl : P' = P := AddMonoidHom.ext fun v => funext fun j =>
      (b1 v j).trans (((T (ik k)).per _ v j).symm.trans ((hPf y.1 v j).trans (a1 v j).symm))
    refine ⟨b3.trans a3.symm, funext fun τ => funext fun i =>
      ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ _ a2).2.1 _).unique (b4 τ i) (a4 τ i), fun hy =>
      ⟨P', a2, a3, hnorm k y P' a1 hy, b5 fun τ i => (congrArg norm (h₀.dmin_eq y.1 τ i)).trans (hy _ i)⟩⟩
  obtain ⟨ν₁, hν₁, hid⟩ := (GlobalTheory.MoveCalc.frMove_calculus E H Dw l Xo c).1
  have hmm₀ : MoveMatch U (unfOf e F M un) k (ik k) h₀ (𝟙 _) ν₁ := fun y y' hy =>
    ⟨hy.1.trans ((Category.comp_id _).trans (key y).1.symm), (funext fun τ => funext fun i =>
      (hy.2.1 τ i).trans ((congrArg _ hν₁).trans (Category.comp_id _))).trans (key y).2.1.symm⟩
  obtain ⟨ε, -, hε⟩ := GlobalTheory.T.exists_const_mul_reading_of_moved_section_at_frame E H Dw l Xo c σ r U (unfOf e F M un) hσ hU hU₀ k (ik k) δ₀ h₀ (𝟙 _) ν₁
    (Category.id_comp _) hmm₀ (fun y y' t hy hmv hb => by
      obtain ⟨P, p, a1, a2, a3⟩ := (key y).2.2 hy
      exact cabs_gen_eq_one_of_normPin E H Dw l Xo c σ _ g _ F _ _ P P _ ν₁ _ _ y' t p p a1
        ((key y).1.trans a1) a2 a3 hmv hb) n
  have hself : ∀ (f₀ : Rul Xo c) (y y' : FrPt Xo c (CAt σ)), FrMove (𝟙 _) ν₁ y y' →
      evR Xo c f₀ y = evR Xo c f₀ y' := fun f₀ y y' hy => by
    rw [(GlobalTheory.exists_unique_frMove E H Dw l Xo c _ ν₁ (Category.id_comp _) (CAt σ) y).2 y y' ν₁ rfl (hid _ y) hy]
  have hx' := h.mem_dom hx
  rw [hε w hw f' hf' f' hf' (hself f') x hx, hε w hw f hf f hf (hself f) _ hx']
  refine congrArg (ε * ·) ?_
  refine (rdU_of_mem (unfOf e F M un) f' (ik k) (h₀.mem_dom hx)).trans
    (Eq.trans (congrArg Formalism.L2.PjFree.toC ?_) (rdU_of_mem (unfOf e F M un) f (ik k) (h₀.mem_dom hx')).symm)
  obtain ⟨y', hmv⟩ := (GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν hρ (CAt σ) (U.un k ⟨x, hx⟩)).1
  obtain ⟨m1, m2⟩ := hmm ⟨x, hx⟩ y' hmv
  obtain ⟨k1, k2, -⟩ := key ⟨x, hx⟩
  obtain ⟨k3, k4, -⟩ := key ⟨_, hx'⟩
  refine evR_normUn_move (T (ik k)) (hun (ik k)) ⟨_, h₀.mem_dom hx⟩ ⟨_, h₀.mem_dom hx'⟩
    ((δ₀ * δ * δ₀⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) ?_ (fun a => ?_) ν hρ ?_ (fun τ i => ?_) hw hf hff
  · have : ((δ₀ * δ * δ₀⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).det = (δ : Matrix (Fin r) (Fin r) E).det := by
      rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj]
    rw [this]
    exact hdet
  · obtain ⟨a', ha'⟩ := (φ k).surjective ⟨_, (h.lat _).1 (φ k a).2⟩
    have ha : (φ k a' : Fin r → E) = (δ : Matrix (Fin r) (Fin r) E) *ᵥ (φ k a : Fin r → E) := congrArg Subtype.val ha'
    refine ⟨a', ?_, funext fun j => ?_⟩
    · rw [hφ, hφ, ha, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Matrix.mul_assoc, Units.inv_mul,
        Matrix.mul_one, Units.val_mul]
    · refine (hPf _ a' j).trans (Eq.trans ?_ (hPf _ a j).symm)
      rw [ha]
      exact GlobalTheory.T.period_coordinates_frame_rational_isometry E r _ _ δ h x _ _ _
  · exact k3.trans (m1.symm.trans (hmv.1.trans (congrArg (· ≫ ρ) k1.symm)))
  · exact (congrFun (congrFun (k4.trans m2.symm) τ) i).trans
      ((hmv.2.1 τ i).trans (congrArg (· ≫ ν.φ) (congrFun (congrFun k2.symm τ) i)))

end GlobalTheory.GeoLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSectionReadingEqMovedFrameReadingStatement
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedSection_reading_eq_movedFrame_reading : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (φD : Dw.La →ₗ[𝓞 E] (Fin r → E)), Function.Injective φD → Submodule.span E (Set.range φD) = ⊤ → (∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φD x) (φD y))) → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ (U.X k).ξ0).im < 0) → ∀ (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k) δ), ((δ : Matrix (Fin r) (Fin r) E).det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ (δ : Matrix (Fin r) (Fin r) E).det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → MoveMatch U U k k h ρ ν → ∀ w n, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n, (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom, Formalism.L2.PjFree.rdU U f' k x = Formalism.L2.PjFree.rdU U f k (lact δ (castFr h.psi x)) := by
  first | exact @GlobalTheory.GeoLevel.rdU_move_eq | exact GlobalTheory.GeoLevel.rdU_move_eq | (intros; apply GlobalTheory.GeoLevel.rdU_move_eq <;> assumption)
end

module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinpolyDefinitePairsTermNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarConjugateSubgroupIndexRatio
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDefinitePairClassesFixedMinpolyDegreeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefinitePairsRatioLocallyRationalTimesNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefinitePairsRatioLocallyRationalTimesNorm
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LocTriv


set_option maxHeartbeats 1000000 in
theorem ratio_local_norm_dpair : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω →
    ∀ (P₁ : GlobalTheory.LKDef.DPair G) (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L),
    Function.Injective ι → (∀ z : G.C, z * P₁.γ = P₁.γ * z ↔ ∃ w, ι w = z) →
    (∀ x, ι (c x) = P₁.β * sh G (ι x) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ), ∀ (P : GlobalTheory.LKDef.DPair G), P.γ = P₁.γ → P.c = P₁.c →
      (∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.toAf x t hx P.self ∈ Ω) →
      ∀ a : L, ι a = ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) → ∀ v ∉ S,
        ∃ (r : (v.adicCompletion ℚ)ˣ) (y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ),
          (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] a = algebraMap (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L) (r : v.adicCompletion ℚ) *
            ((y : v.adicCompletion ℚ ⊗[ℚ] L) * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c y) := by
  intro p _ G Ω hΩ P₁ L _ _ ι c hinj hcent hc
  obtain ⟨x₁, t₁, hx₁⟩ := P₁.trivAf
  have hβ₁inv := sh_inv_unit G P₁.β P₁.sym
  have hcc : ∀ x, c (c x) = x := fun x => hinj (by
    rw [hc, hc, sh_mul', sh_mul', sh_sh, hβ₁inv, P₁.sym]
    simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one])
  have hcne : ∃ x, c x ≠ x := by
    obtain ⟨τ⟩ : Nonempty (G.F →+* ℂ) := inferInstance
    obtain ⟨f, -, hf⟩ := G.hKq.2 τ
    have hconj : IsCMField.complexConj G.F f ≠ f := by
      intro h
      apply hf
      have e := IsCMField.complexEmbedding_complexConj G.F τ f
      rw [h] at e
      exact Complex.conj_eq_iff_im.1 e.symm
    obtain ⟨w, hw⟩ := (hcent (algebraMap G.F G.C f)).1 (Algebra.commutes f _)
    refine ⟨w, fun h => hconj ?_⟩
    have e2 : ι (c w) = algebraMap G.F G.C (IsCMField.complexConj G.F f) := by
      rw [hc, hw, sh_algebraMap, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]
    rw [h, hw] at e2
    exact ((algebraMap G.F G.C).injective e2).symm
  obtain ⟨S1, hS1⟩ := exists_finset_of_eventually (GlobalTheory.OrbFinAf.cptInt p G Ω hΩ)
  obtain ⟨S2, hS2⟩ := exists_finset_of_eventually
    (GlobalTheory.OrbFinAf.cptInt p G {P₁.toAf x₁ t₁ hx₁ P₁.self} isCompact_singleton)
  obtain ⟨S3, hS3⟩ := GlobalTheory.T.eventually_adic_integral_span_closed_mul_star G.C G.star _ (Module.finBasis ℚ G.C)
  obtain ⟨S4, hS4⟩ := GlobalTheory.T.eventually_integral_conjugators_differ_by_centralizer p G P₁.γ P₁.reg.1 P₁.reg.2 L ι hinj hcent _ (Module.finBasis ℚ G.C)
  obtain ⟨S5, hS5⟩ := GlobalTheory.T.almost_all_places_twisted_unit_integral G.C L ι hinj _ (Module.finBasis ℚ G.C) _ (Module.finBasis ℚ L)
  obtain ⟨S6, hS6⟩ := GlobalTheory.T.fixed_unit_eq_norm_almost_all_places L c hcc hcne _ (Module.finBasis ℚ L)
  refine ⟨S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6 ∪ (finite_above p).toFinset, ?_⟩
  intro P hγ hcP hex a ha v hv
  obtain ⟨x, t, hx, hxΩ⟩ := hex
  simp only [Finset.mem_union, not_or] at hv
  obtain ⟨⟨⟨⟨⟨⟨hv1, hv2⟩, hv3⟩, hv4⟩, hv5⟩, hv6⟩, hvp⟩ := hv
  have hvp' : v.asIdeal ≠ Ideal.span {(p : ℤ)} := fun h => hvp ((Set.Finite.mem_toFinset _).2 h)
  let w : AwayP p := ⟨v, hvp'⟩
  let K := v.adicCompletion ℚ
  let φ : AfP p ⊗[ℚ] G.C →ₐ[ℚ] K ⊗[ℚ] G.C := Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C)
  let ιv : K ⊗[ℚ] L →ₐ[ℚ] K ⊗[ℚ] G.C := Algebra.TensorProduct.map (AlgHom.id ℚ K) ι
  let cv : K ⊗[ℚ] L →ₐ[ℚ] K ⊗[ℚ] L := Algebra.TensorProduct.map (AlgHom.id ℚ K) c
  let X : (K ⊗[ℚ] G.C)ˣ := Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) x
  let X₁ : (K ⊗[ℚ] G.C)ˣ := Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) x₁
  have key : ∀ (Q : GlobalTheory.LKDef.DPair G) (y : (AfP p ⊗[ℚ] G.C)ˣ) (s : (AfP p)ˣ) (hy : Triv G (AfP p) Q.β y s),
      ((((GlobalTheory.OrbFinAf.piV G w (Q.toAf y s hy Q.self) : GlobalTheory.OrbFinAf.Gv G w) :
        (K ⊗[ℚ] G.C)ˣ × Kˣ).1 : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) =
        ↑(Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) y) * ((1 : K) ⊗ₜ[ℚ] (Q.γ : G.C)) *
          ↑(Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) y)⁻¹ := by
    intro Q y s hy
    show φ (↑y * ((1 : AfP p) ⊗ₜ[ℚ] (Q.γ : G.C)) * ↑y⁻¹) = _
    rw [map_mul, map_mul, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    rfl
  have hXg : IsIntB v (Module.finBasis ℚ G.C) (↑X * ((1 : K) ⊗ₜ[ℚ] (P₁.γ : G.C)) * ↑X⁻¹) := by
    have h := (hS1 w hv1 ⟨_, hxΩ, rfl⟩).1
    rw [key P x t hx, hγ] at h
    exact h
  have hX₁g : IsIntB v (Module.finBasis ℚ G.C) (↑X₁ * ((1 : K) ⊗ₜ[ℚ] (P₁.γ : G.C)) * ↑X₁⁻¹) := by
    have h := (hS2 w hv2 ⟨_, rfl, rfl⟩).1
    rw [key P₁ x₁ t₁ hx₁] at h
    exact h

  obtain ⟨m, hm1, hm2⟩ := hS4 v hv4 X X₁ hXg hX₁g
  obtain ⟨hmul, hstar⟩ := hS3 v hv3
  let T : Kˣ := Units.map (AfP.eval w : AfP p →* K) t
  let T₁ : Kˣ := Units.map (AfP.eval w : AfP p →* K) t₁
  let β₁v : (K ⊗[ℚ] G.C)ˣ :=
    Units.map ((Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] K ⊗[ℚ] G.C) : G.C →* K ⊗[ℚ] G.C) P₁.β
  have hiota_a : ιv ((1 : K) ⊗ₜ[ℚ] a) * (β₁v : K ⊗[ℚ] G.C) = (1 : K) ⊗ₜ[ℚ] (P.β : G.C) := by
    show (1 : K) ⊗ₜ[ℚ] ι a * (1 : K) ⊗ₜ[ℚ] (P₁.β : G.C) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ha, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  have htriv : ∀ (Q : GlobalTheory.LKDef.DPair G) (y : (AfP p ⊗[ℚ] G.C)ˣ) (s : (AfP p)ˣ), Triv G (AfP p) Q.β y s →
      (↑(Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) y) : K ⊗[ℚ] G.C) * ((1 : K) ⊗ₜ[ℚ] (Q.β : G.C)) *
        (starT G.star K ↑(Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) y)).unop =
        algebraMap K (K ⊗[ℚ] G.C) (AfP.eval w (s : AfP p)) := by
    intro Q y s hy
    have hy' : (y : AfP p ⊗[ℚ] G.C) * inC G (AfP p) Q.β * (starT G.star (AfP p) y).unop =
        algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s := hy
    have h := congrArg (Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C)) hy'
    rw [map_mul, map_mul, map_starT] at h
    have e1 : Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (inC G (AfP p) Q.β) =
        (1 : K) ⊗ₜ[ℚ] (Q.β : G.C) := by
      simp [inC, Algebra.TensorProduct.map_tmul]
    have e2 : Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s) =
        algebraMap K (K ⊗[ℚ] G.C) (AfP.eval w (s : AfP p)) := by
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
    rw [e1, e2] at h
    exact h
  have h1 : (X : K ⊗[ℚ] G.C) * (ιv ((1 : K) ⊗ₜ[ℚ] a) * β₁v) * (starT G.star K X).unop =
      algebraMap K (K ⊗[ℚ] G.C) (T : K) := by
    rw [hiota_a]; exact htriv P x t hx
  have h2 : (X₁ : K ⊗[ℚ] G.C) * β₁v * (starT G.star K X₁).unop = algebraMap K (K ⊗[ℚ] G.C) (T₁ : K) :=
    htriv P₁ x₁ t₁ hx₁
  have hιR : ∀ r : K, ιv (algebraMap K (K ⊗[ℚ] L) r) = algebraMap K (K ⊗[ℚ] G.C) r := by
    intro r; simp [ιv, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  have hcm : ιv (cv ↑m) = ↑β₁v * (starT G.star K (ιv ↑m)).unop * ↑β₁v⁻¹ := map_conj_ext G K ι c P₁.β hc ↑m
  have hcore := selfDual_conj_eq_one (R := K) (ιv : K ⊗[ℚ] L →+* K ⊗[ℚ] G.C) hιR (starT G.star K) (cv : K ⊗[ℚ] L →+* K ⊗[ℚ] L)
    β₁v X X₁ T T₁ ((1 : K) ⊗ₜ[ℚ] a) m hcm h1 h2
  simp only [RingHom.coe_coe] at hcore

  have hu'u : ((X₁ : K ⊗[ℚ] G.C) * ιv ↑m⁻¹ * ↑X⁻¹) * ((X : K ⊗[ℚ] G.C) * ιv ↑m * ↑X₁⁻¹) = 1 := by
    calc ((X₁ : K ⊗[ℚ] G.C) * ιv ↑m⁻¹ * ↑X⁻¹) * ((X : K ⊗[ℚ] G.C) * ιv ↑m * ↑X₁⁻¹)
        = (X₁ : K ⊗[ℚ] G.C) * (ιv ↑m⁻¹ * ((↑X⁻¹ : K ⊗[ℚ] G.C) * ↑X) * ιv ↑m) * ↑X₁⁻¹ := by
          simp only [mul_assoc]
      _ = 1 := by rw [Units.inv_mul, mul_one, ← map_mul, Units.inv_mul, map_one, mul_one, Units.mul_inv]
  have hshu : (starT G.star K ((X : K ⊗[ℚ] G.C) * ιv ↑m * ↑X₁⁻¹)).unop *
      (starT G.star K ((X₁ : K ⊗[ℚ] G.C) * ιv ↑m⁻¹ * ↑X⁻¹)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, hu'u, map_one, MulOpposite.unop_one]
  set u := (X : K ⊗[ℚ] G.C) * ιv ↑m * ↑X₁⁻¹ with hu
  set u' := (X₁ : K ⊗[ℚ] G.C) * ιv ↑m⁻¹ * ↑X⁻¹ with hu'
  set E := algebraMap K (K ⊗[ℚ] L) (↑T⁻¹ * ↑T₁) * ((1 : K) ⊗ₜ[ℚ] a) * (↑m⁻¹ * cv ↑m⁻¹) with hE
  set wv := (X₁ : K ⊗[ℚ] G.C) * ιv E * ↑X₁⁻¹ with hwvdef
  have hwv : wv = u' * (starT G.star K u').unop := by
    calc wv = (u' * u) * wv * ((starT G.star K u).unop * (starT G.star K u').unop) := by
          rw [hu'u, hshu, one_mul, mul_one]
      _ = u' * (u * wv * (starT G.star K u).unop) * (starT G.star K u').unop := by simp only [mul_assoc]
      _ = _ := by rw [hcore, mul_one]
  have hwvI : IsIntB v (Module.finBasis ℚ G.C) wv := hwv ▸ hmul _ _ hm2 (hstar _ hm2)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (Units.ne_zero _) ha.symm
  obtain ⟨Eu, hEu⟩ : ∃ Eu : (K ⊗[ℚ] L)ˣ, (Eu : K ⊗[ℚ] L) = E :=
    ⟨Units.map (algebraMap K (K ⊗[ℚ] L) : K →* K ⊗[ℚ] L) (T⁻¹ * T₁) *
      Units.map ((Algebra.TensorProduct.includeRight : L →ₐ[ℚ] K ⊗[ℚ] L) : L →* K ⊗[ℚ] L) (Units.mk0 a ha0) *
        (m⁻¹ * Units.map (cv : K ⊗[ℚ] L →* K ⊗[ℚ] L) m⁻¹), by
      simp only [Units.val_mul, Units.coe_map, Units.val_mk0, hE, map_mul]
      rfl⟩
  have h_a : ((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹) * wv = 1 := by
    rw [hwvdef, ← hEu]
    calc ((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹) * ((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu * ↑X₁⁻¹)
        = (X₁ : K ⊗[ℚ] G.C) * (ιv ↑Eu⁻¹ * ((↑X₁⁻¹ : K ⊗[ℚ] G.C) * ↑X₁) * ιv ↑Eu) * ↑X₁⁻¹ := by
          simp only [mul_assoc]
      _ = 1 := by rw [Units.inv_mul X₁, mul_one, ← map_mul ιv, Units.inv_mul Eu, map_one, mul_one, Units.mul_inv X₁]
  have h_b : wv * ((starT G.star K u).unop * u) = 1 := by
    calc wv * ((starT G.star K u).unop * u) = (u' * u) * wv * (starT G.star K u).unop * u := by
          rw [hu'u, one_mul]; simp only [mul_assoc]
      _ = u' * (u * wv * (starT G.star K u).unop) * u := by simp only [mul_assoc]
      _ = 1 := by rw [hcore, mul_one, hu'u]
  have hwv' : (X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹ = (starT G.star K u).unop * u := by
    calc (X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹
        = ((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹) * (wv * ((starT G.star K u).unop * u)) := by rw [h_b, mul_one]
      _ = (((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹) * wv) * ((starT G.star K u).unop * u) := by
          rw [← mul_assoc]
      _ = _ := by rw [h_a, one_mul]
  have hE1 : IsIntB v (Module.finBasis ℚ L) (Eu : K ⊗[ℚ] L) := hS5 v hv5 X₁ _ (by rw [hEu]; exact hwvI)
  have hE2 : IsIntB v (Module.finBasis ℚ L) ((Eu⁻¹ : (K ⊗[ℚ] L)ˣ) : K ⊗[ℚ] L) :=
    hS5 v hv5 X₁ _ (by rw [hwv']; exact hmul _ _ (hstar _ hm1) hm1)
  have hca : c a = a := hinj (by
    rw [hc, ha, Units.val_mul, sh_mul', hβ₁inv, P.sym]
    simp only [mul_assoc, Units.mul_inv_cancel_left])
  have hcalg : ∀ r : K, cv (algebraMap K (K ⊗[ℚ] L) r) = algebraMap K (K ⊗[ℚ] L) r := by
    intro r; simp [cv, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  have hcinv : cv (cv ↑m⁻¹) = ↑m⁻¹ := map_invol c hcc _
  have hfix : cv ↑Eu = ↑Eu := by
    have : cv ((1 : K) ⊗ₜ[ℚ] a) = (1 : K) ⊗ₜ[ℚ] a := by
      show (1 : K) ⊗ₜ[ℚ] c a = _
      rw [hca]
    rw [hEu, hE]
    simp only [map_mul, hcalg, hcinv, this]
    ring
  obtain ⟨y₀, hy₀⟩ := hS6 v hv6 Eu hfix hE1 hE2
  refine ⟨T * T₁⁻¹, m * y₀, ?_⟩
  rw [hEu, hE, map_mul] at hy₀
  have hm' : (m : K ⊗[ℚ] L) * ↑m⁻¹ = 1 := Units.mul_inv m
  have hcm' : cv ↑m * cv ↑m⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hT : algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hT₁ : algebraMap K (K ⊗[ℚ] L) ↑T₁ * algebraMap K (K ⊗[ℚ] L) ↑T₁⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  show (1 : K) ⊗ₜ[ℚ] a = algebraMap K (K ⊗[ℚ] L) ↑(T * T₁⁻¹) * (↑(m * y₀) * cv ↑(m * y₀))
  rw [Units.val_mul, Units.val_mul, map_mul, map_mul]
  linear_combination (algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T₁⁻¹ * ↑m * cv ↑m) * hy₀ -
    ((1 : K) ⊗ₜ[ℚ] a) * hT - ((1 : K) ⊗ₜ[ℚ] a) * algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T⁻¹ * hT₁ -
    ((1 : K) ⊗ₜ[ℚ] a) * algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T⁻¹ *
      algebraMap K (K ⊗[ℚ] L) ↑T₁ * algebraMap K (K ⊗[ℚ] L) ↑T₁⁻¹ * hm' -
    ((1 : K) ⊗ₜ[ℚ] a) * algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T⁻¹ *
      algebraMap K (K ⊗[ℚ] L) ↑T₁ * algebraMap K (K ⊗[ℚ] L) ↑T₁⁻¹ * ↑m * ↑m⁻¹ * hcm'

end GlobalTheory.LocTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefinitePairsRatioLocallyRationalTimesNormStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definitePairs_ratio_locally_rational_times_norm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω →
    ∀ (P₁ : GlobalTheory.LKDef.DPair G) (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L),
    Function.Injective ι → (∀ z : G.C, z * P₁.γ = P₁.γ * z ↔ ∃ w, ι w = z) →
    (∀ x, ι (c x) = P₁.β * sh G (ι x) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ), ∀ (P : GlobalTheory.LKDef.DPair G), P.γ = P₁.γ → P.c = P₁.c →
      (∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.toAf x t hx P.self ∈ Ω) →
      ∀ a : L, ι a = ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) → ∀ v ∉ S,
        ∃ (r : (v.adicCompletion ℚ)ˣ) (y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ),
          (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] a = algebraMap (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L) (r : v.adicCompletion ℚ) *
            ((y : v.adicCompletion ℚ ⊗[ℚ] L) * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c y) := by
  first | (exact @GlobalTheory.LocTriv.ratio_local_norm_dpair) | (exact GlobalTheory.LocTriv.ratio_local_norm_dpair) | (intros; apply GlobalTheory.LocTriv.ratio_local_norm_dpair  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumberFieldInvolutionSimilitudeCentralizer
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentraliserInvolution
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentConj

variable {p : ℕ} [Fact p.Prime]

theorem sh_mul' (G : HTGroup p) (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_add' (G : HTGroup p) (x y : G.C) : sh G (x + y) = sh G x + sh G y := by
  simp only [sh, map_add (f := _), MulOpposite.unop_add]

theorem sh_one' (G : HTGroup p) : sh G 1 = 1 := by
  simp only [sh, map_one, MulOpposite.unop_one]

theorem sh_sh' (G : HTGroup p) (x : G.C) : sh G (sh G x) = x := G.star_star x

theorem sh_inv_of_sym (G : HTGroup p) (β : G.Cˣ) (hβ : sh G β = β) :
    sh G ((β⁻¹ : G.Cˣ) : G.C) = ((β⁻¹ : G.Cˣ) : G.C) := by
  have e : sh G ((β⁻¹ : G.Cˣ) : G.C) * β = 1 := by
    rw [← hβ, ← sh_mul', Units.mul_inv, sh_one']
  calc sh G ((β⁻¹ : G.Cˣ) : G.C) = sh G ((β⁻¹ : G.Cˣ) : G.C) * β * ((β⁻¹ : G.Cˣ) : G.C) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [e, one_mul]

end GlobalTheory.CentConj

namespace GlobalTheory.CentConj

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.CentConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumberFieldInvolutionSimilitudeCentralizer
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentSim

variable {p : ℕ} [Fact p.Prime]

theorem commute_conj_sh_sim (G : HTGroup p) (β γ : G.Cˣ) (c₀ : ℚ)
    (h : (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c₀ * β) (z : G.C) (hz : Commute z (γ : G.C)) :
    Commute ((β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C)) (γ : G.C) := by
  set y : G.Cˣ := γ with hydef
  set c : G.C := algebraMap ℚ G.C c₀
  set Y := sh G (y : G.C)
  set Yi := sh G ((y⁻¹ : G.Cˣ) : G.C)
  have hYYi : Y * Yi = 1 := by
    simp only [Y, Yi, ← GlobalTheory.CentConj.sh_mul', Units.inv_mul, GlobalTheory.CentConj.sh_one']
  have hzi : Commute z ((y⁻¹ : G.Cˣ) : G.C) := hz.units_inv_right
  have hcomm : Yi * sh G z = sh G z * Yi := by
    simp only [Yi, ← GlobalTheory.CentConj.sh_mul']; rw [hzi.eq]
  have hcc : ∀ w : G.C, c * w = w * c := fun w => Algebra.commutes _ w
  have h1 : (y : G.C) * β = c * β * Yi := by
    calc (y : G.C) * β = (y : G.C) * β * (Y * Yi) := by rw [hYYi, mul_one]
      _ = c * β * Yi := by rw [← mul_assoc, h]
  have h2 : ((β⁻¹ : G.Cˣ) : G.C) * y = c * Yi * ((β⁻¹ : G.Cˣ) : G.C) := by
    calc ((β⁻¹ : G.Cˣ) : G.C) * y = ((β⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * β) * ((β⁻¹ : G.Cˣ) : G.C) := by
          simp only [mul_assoc, Units.mul_inv, mul_one]
      _ = c * Yi * ((β⁻¹ : G.Cˣ) : G.C) := by
          rw [h1, ← mul_assoc, ← mul_assoc, ← hcc, mul_assoc c, Units.inv_mul, mul_one]
  change (β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C) * y = y * ((β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C))
  calc (β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C) * y
        = (β : G.C) * sh G z * (((β⁻¹ : G.Cˣ) : G.C) * y) := by rw [mul_assoc]
    _ = c * (β * (sh G z * Yi)) * ((β⁻¹ : G.Cˣ) : G.C) := by
        rw [h2]; simp only [mul_assoc]
        rw [← mul_assoc (sh G z) c, ← hcc (sh G z), mul_assoc c, ← mul_assoc (β : G.C) c, ← hcc (β : G.C)]
        simp only [mul_assoc]
    _ = c * (β * (Yi * sh G z)) * ((β⁻¹ : G.Cˣ) : G.C) := by rw [hcomm]
    _ = (y : G.C) * β * sh G z * ((β⁻¹ : G.Cˣ) : G.C) := by rw [h1]; simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

theorem centraliser_field_involution : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β γ : G.Cˣ) (c₀ : ℚˣ), sh G β = β →
    (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c₀ * β → Irreducible (minpoly G.F (γ : G.C)) →
    (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L),
      Function.Injective ι ∧ (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) ∧
      (∀ x, ι (c x) = β * sh G (ι x) * ((β⁻¹ : G.Cˣ) : G.C)) ∧ ∀ x, c (c x) = x := by
  intro p _ G β γ c₀ hβ hsim hirr hdeg
  obtain ⟨E, _, _, _, j, hj, hcent⟩ := GlobalTheory.CentIrr.centralizer_unit_eq_field p G γ hirr hdeg
  set w : E → G.C := fun e => (β : G.C) * sh G (j e) * ((β⁻¹ : G.Cˣ) : G.C) with hw
  have hex : ∀ e, ∃ e', j e' = w e := fun e =>
    (hcent _).1 (commute_conj_sh_sim G β γ (c₀ : ℚ) hsim (j e) ((hcent _).2 ⟨e, rfl⟩))
  choose t ht using hex
  have tt : ∀ e, t (t e) = e := by
    intro e
    apply hj
    rw [ht, hw]; dsimp only
    rw [ht, GlobalTheory.CentConj.sh_mul', GlobalTheory.CentConj.sh_mul', GlobalTheory.CentConj.sh_sh', hβ,
      GlobalTheory.CentConj.sh_inv_of_sym G β hβ]
    simp only [mul_assoc, Units.mul_inv, mul_one]
    rw [← mul_assoc, Units.mul_inv, one_mul]
  have hm : ∀ a b, t (a * b) = t a * t b := by
    intro a b
    apply hj
    rw [mul_comm a b, ht, map_mul, ht, ht, hw]; dsimp only
    rw [map_mul, GlobalTheory.CentConj.sh_mul']
    simp only [mul_assoc]
    rw [← mul_assoc ((β⁻¹ : G.Cˣ) : G.C) (β : G.C), Units.inv_mul, one_mul]
  have ha : ∀ a b, t (a + b) = t a + t b := by
    intro a b
    apply hj
    rw [ht, map_add (f := _), ht, ht, hw]; dsimp only
    rw [map_add (f := _), GlobalTheory.CentConj.sh_add']; noncomm_ring
  have h1 : t 1 = 1 := by
    apply hj
    rw [ht, hw]; dsimp only
    rw [map_one, GlobalTheory.CentConj.sh_one', mul_one, Units.mul_inv]
  have h0 : t 0 = 0 := by
    have h := ha 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  let τ : E →+* E := { toFun := t, map_one' := h1, map_mul' := hm, map_zero' := h0, map_add' := ha }
  refine ⟨E, inferInstance, inferInstance, j.toRingHom.toRatAlgHom, τ.toRatAlgHom, hj, ?_, ?_, ?_⟩
  · intro z
    exact hcent z
  · intro x; exact ht x
  · intro x; exact tt x

end GlobalTheory.CentSim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumberFieldInvolutionSimilitudeCentralizerStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numberField_involution_similitudeCentralizer : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β γ : G.Cˣ) (c₀ : ℚˣ), sh G β = β →
    (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c₀ * β → Irreducible (minpoly G.F (γ : G.C)) →
    (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L),
      Function.Injective ι ∧ (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) ∧
      (∀ x, ι (c x) = β * sh G (ι x) * ((β⁻¹ : G.Cˣ) : G.C)) ∧ ∀ x, c (c x) = x := by
  first | (exact @GlobalTheory.CentSim.centraliser_field_involution) | (exact GlobalTheory.CentSim.centraliser_field_involution) | (intros; apply GlobalTheory.CentSim.centraliser_field_involution  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkolemNoetherConjugacy
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem units_conj_of_minpoly_eq_of_irreducible : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (a b : G.Cˣ),
    minpoly G.F (a : G.C) = minpoly G.F (b : G.C) → Irreducible (minpoly G.F (b : G.C)) →
      ∃ g : G.Cˣ, (a : G.C) = g * b * ↑g⁻¹ := by
  intro p _ G a b h hirr
  have hb : IsIntegral G.F (b : G.C) := IsIntegral.of_finite G.F _
  haveI : Fact (Irreducible (minpoly G.F (b : G.C))) := ⟨hirr⟩
  haveI : FiniteDimensional G.F (AdjoinRoot (minpoly G.F (b : G.C))) :=
    (AdjoinRoot.powerBasis (minpoly.ne_zero hb)).finite
  have ha : Polynomial.aeval (a : G.C) (minpoly G.F (b : G.C)) = 0 := by rw [← h]; exact minpoly.aeval _ _
  obtain ⟨y, hy⟩ := GroundTheory.Brauer.exists_unit_conj (evalQuot _ (b : G.C) (minpoly.aeval _ _))
    (evalQuot _ (a : G.C) ha)
  refine ⟨y, ?_⟩
  have := hy (AdjoinRoot.root _)
  rwa [evalQuot_root, evalQuot_root] at this

end GlobalTheory.LKCx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDefinitePairClassesFixedMinpolyDegreeOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKDefFin

open GlobalTheory.LKDef GlobalTheory.LKMid.PairConj

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem form_conj (v : InfinitePlace G.F) (β y : G.Cˣ) (x : Fin G.n → ℂ) :
    star x ⬝ᵥ ((G.gram v * G.psi v (((y * β * shU G y)⁻¹ : G.Cˣ) : G.C)) *ᵥ x) =
      star (G.psi v ((y⁻¹ : G.Cˣ) : G.C) *ᵥ x) ⬝ᵥ
        ((G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *ᵥ (G.psi v ((y⁻¹ : G.Cˣ) : G.C) *ᵥ x)) := by
  have e1 : (((y * β * shU G y)⁻¹ : G.Cˣ) : G.C) =
      sh G ((y⁻¹ : G.Cˣ) : G.C) * (((β⁻¹ : G.Cˣ) : G.C) * ((y⁻¹ : G.Cˣ) : G.C)) := by
    simp only [_root_.mul_inv_rev, Units.val_mul]; rfl
  have e2 : G.psi v (sh G ((y⁻¹ : G.Cˣ) : G.C)) =
      (G.gram v)⁻¹ * (G.psi v ((y⁻¹ : G.Cˣ) : G.C))ᴴ * G.gram v := G.psi_star v _
  have hg : G.gram v * (G.gram v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (Ne.isUnit (G.gram_det v))
  have e3 : G.gram v * G.psi v (((y * β * shU G y)⁻¹ : G.Cˣ) : G.C) =
      (G.psi v ((y⁻¹ : G.Cˣ) : G.C))ᴴ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *
        G.psi v ((y⁻¹ : G.Cˣ) : G.C) := by
    rw [e1, map_mul, map_mul, e2]
    calc G.gram v * ((G.gram v)⁻¹ * (G.psi v ((y⁻¹ : G.Cˣ) : G.C))ᴴ * G.gram v *
          (G.psi v ((β⁻¹ : G.Cˣ) : G.C) * G.psi v ((y⁻¹ : G.Cˣ) : G.C)))
        = (G.gram v * (G.gram v)⁻¹) * (G.psi v ((y⁻¹ : G.Cˣ) : G.C))ᴴ * G.gram v *
          (G.psi v ((β⁻¹ : G.Cˣ) : G.C) * G.psi v ((y⁻¹ : G.Cˣ) : G.C)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg, Matrix.one_mul]; simp only [Matrix.mul_assoc]
  rw [e3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

def conjD (P : DPair G) (y : G.Cˣ) : DPair G where
  β := y * P.β * shU G y
  γ := y * P.γ * y⁻¹
  c := P.c
  sym := by
    simp only [Units.val_mul, shU_val, sh_mul, sh_sh, P.sym, mul_assoc]
  sim := by
    have hs := P.sim
    have h1 := unop_mul_inv G.star y
    simp only [Units.val_mul, shU_val, sh_mul]
    calc _ = (y : G.C) * (P.γ * (((y⁻¹ : G.Cˣ) : G.C) * y) * P.β * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C)) * sh G P.γ) *
            sh G y := by simp only [mul_assoc]
      _ = y * ((P.γ : G.C) * P.β * sh G P.γ) * sh G y := by
            rw [Units.inv_mul, show sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 from h1, mul_one, mul_one]
      _ = _ := by
            rw [hs, ← mul_assoc, ← mul_assoc, ← Algebra.commutes, mul_assoc _ (y : G.C), mul_assoc, mul_assoc]
  reg := by
    have e : ((y * P.γ * y⁻¹ : G.Cˣ) : G.C) = conjAlg G y P.γ := by simp [conjAlg]
    rw [e, minpoly.algHom_eq (conjAlg G y) (conjAlg_injective G y)]
    exact P.reg
  trivAf := by
    obtain ⟨x, t, hx⟩ := P.trivAf
    have h := triv_conj_unit (AfP p) (P.β : G.C) y x t hx
    rw [← conj_val] at h
    exact ⟨_, t, h⟩
  posR := by
    intro v x hx
    have hM : G.psi v ((y⁻¹ : G.Cˣ) : G.C) *ᵥ x ≠ 0 := by
      intro h0; apply hx
      have e : G.psi v (y : G.C) *ᵥ (G.psi v ((y⁻¹ : G.Cˣ) : G.C) *ᵥ x) = x := by
        rw [Matrix.mulVec_mulVec, ← map_mul, Units.mul_inv, map_one, Matrix.one_mulVec]
      rw [← e, h0, Matrix.mulVec_zero]
    rw [form_conj]
    exact P.posR v _ hM

theorem conjD_β (P : DPair G) (y : G.Cˣ) :
    (((conjD P y).β : G.Cˣ) : G.C) = (y : G.C) * P.β * sh G y := conj_val P.β y

theorem exists_conj (P : DPair G) (y : G.Cˣ) :
    ∃ P' : DPair G, P.Rel P' ∧ P'.γ = y * P.γ * y⁻¹ ∧ P'.c = P.c ∧
      ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t),
        ∃ (x' : (AfP p ⊗[ℚ] G.C)ˣ) (hx' : Triv G (AfP p) P'.β x' t),
          P'.toAf x' t hx' P'.self = P.toAf x t hx P.self := by
  refine ⟨conjD P y, ⟨y, 1, one_pos, ?_, rfl⟩, rfl, rfl, ?_⟩
  · rw [map_one, one_mul, conjD_β]
  · intro x t hx
    have h := triv_conj_unit (AfP p) (P.β : G.C) y x t hx
    rw [← conjD_β] at h
    refine ⟨_, h, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · show (x * (Units.map (inC G (AfP p)).toMonoidHom y)⁻¹) *
          Units.map (inC G (AfP p)).toMonoidHom (y * P.γ * y⁻¹) *
          (x * (Units.map (inC G (AfP p)).toMonoidHom y)⁻¹)⁻¹ =
        x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹
      simp only [map_mul, map_inv]
      group
    · rfl

theorem norm_sim (P : DPair G) :
    Algebra.norm ℚ (P.γ : G.C) * Algebra.norm ℚ (sh G P.γ) = (P.c : ℚ) ^ Module.finrank ℚ G.C := by
  have h := congrArg (Algebra.norm ℚ) P.sim
  rw [map_mul, map_mul, map_mul, Algebra.norm_algebraMap] at h
  have hb : Algebra.norm ℚ (P.β : G.C) ≠ 0 := (P.β.isUnit.map (Algebra.norm ℚ)).ne_zero
  apply mul_right_cancel₀ hb
  rw [← h]; ring

theorem c_eq_or_eq_neg (P P' : DPair G) (hγ : P'.γ = P.γ) : P'.c = P.c ∨ P'.c = -P.c := by
  have h1 := norm_sim P
  have h2 := norm_sim P'
  rw [hγ, h1] at h2
  have hN : Module.finrank ℚ G.C ≠ 0 := Module.finrank_pos.ne'
  rcases (pow_eq_pow_iff_of_ne_zero hN).1 h2.symm with h | ⟨h, _⟩
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (by rw [h, Units.val_neg]))

theorem exists_ne_zero_of_term_ne_zero (P : DPair G) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) (h : P.term Kf f r K φ ≠ 0) :
    ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf),
      f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0 := by
  unfold DPair.term at h
  split_ifs at h with hd
  · unfold DPair.termAt pointSum at h
    obtain ⟨q, hq⟩ := not_forall.1 (fun hc => h (finsum_eq_zero_of_forall_eq_zero hc))
    refine ⟨_, _, P.trivAf.choose_spec.choose_spec, (Quotient.out q).1, fun h0 => hq ?_⟩
    rw [h0, zero_mul, mul_zero]
  · exact absurd rfl h

end GlobalTheory.LKDefFin

noncomputable section

namespace GlobalTheory.LKDefFin

open GlobalTheory.LKDef

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem exists_triv_toAf_eq_conj (P : DPair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) P.β x t) (g : G.GAf) : ∃ (x' : (AfP p ⊗[ℚ] G.C)ˣ) (t' : (AfP p)ˣ)
    (hx' : Triv G (AfP p) P.β x' t'), P.toAf x' t' hx' P.self = g⁻¹ * P.toAf x t hx P.self * g := by
  refine ⟨g.1.1⁻¹ * x, t * g.1.2⁻¹, ?_, ?_⟩
  · exact mul_triv_star (starT G.star (AfP p)) (inC G (AfP p) P.β) ((g.1.1⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)
      (x : AfP p ⊗[ℚ] G.C) (t : AfP p) ((g.1.2⁻¹ : (AfP p)ˣ) : AfP p) hx (mem_uGroup.1 (g⁻¹).2)
  · apply Subtype.ext
    apply Prod.ext
    · change (g.1.1⁻¹ * x) * Units.map (inC G (AfP p)).toMonoidHom P.γ * (g.1.1⁻¹ * x)⁻¹ =
        g.1.1⁻¹ * (x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹) * g.1.1
      group
    · change Units.map (algebraMap ℚ (AfP p)).toMonoidHom P.c =
        g.1.2⁻¹ * Units.map (algebraMap ℚ (AfP p)).toMonoidHom P.c * g.1.2
      rw [mul_comm g.1.2⁻¹, inv_mul_cancel_right]

theorem quot_commute_and_fixed (P Q : DPair G) (hγ : P.γ = Q.γ) (hc : P.c = Q.c) :
    ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * Q.γ = Q.γ * ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) ∧
    (Q.β : G.C) * sh G ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * ((Q.β⁻¹ : G.Cˣ) : G.C) = ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) := by
  have hmul : ∀ x y : G.C, sh G (x * y) = sh G y * sh G x := fun x y => by
    simp only [sh, map_mul, MulOpposite.unop_mul]
  have hinv : ∀ y : G.Cˣ, sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := fun y => by
    rw [← hmul, Units.inv_mul, sh_one_eq]
  have hP := P.sim
  have hQ := Q.sim
  rw [hγ, hc] at hP
  refine ⟨?_, ?_⟩
  · have e1 : ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * Q.γ * (Q.β * sh G Q.γ) = algebraMap ℚ G.C Q.c * P.β := by
      calc ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * Q.γ * (Q.β * sh G Q.γ)
          = ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * (Q.γ * Q.β * sh G Q.γ) := by simp only [mul_assoc]
        _ = algebraMap ℚ G.C Q.c * (((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * Q.β) := by
          rw [hQ]; simp only [← Algebra.smul_def, mul_smul_comm]
        _ = _ := by rw [Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
    have e2 : (Q.γ : G.C) * ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * (Q.β * sh G Q.γ) = algebraMap ℚ G.C Q.c * P.β := by
      rw [← hP, Units.val_mul]
      simp only [mul_assoc, Units.inv_mul_cancel_left]
    have e3 : (Q.β : G.C) * sh G Q.γ * (sh G ((Q.γ⁻¹ : G.Cˣ) : G.C) * ((Q.β⁻¹ : G.Cˣ) : G.C)) = 1 := by
      rw [mul_assoc, ← mul_assoc (sh G Q.γ), hinv, one_mul, Units.mul_inv]
    have e4 := congrArg (· * (sh G ((Q.γ⁻¹ : G.Cˣ) : G.C) * ((Q.β⁻¹ : G.Cˣ) : G.C))) (e1.trans e2.symm)
    rwa [mul_assoc _ (_ * sh G _), mul_assoc _ (_ * sh G _), e3, mul_one, mul_one] at e4
  · have h := hinv Q.β
    rw [Q.sym] at h
    rw [Units.val_mul, hmul, P.sym, ← mul_assoc, h, one_mul]

theorem rel_of_ratio (P Q P₁ : DPair G) (y : G.Cˣ) (s : ℚ) (hs : 0 < s)
    (hP : P.γ = P₁.γ) (hQ : Q.γ = P₁.γ) (hy : (y : G.C) * P₁.γ = P₁.γ * y)
    (ha : ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) * y = y * ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C))
    (hr : ((Q.β * P₁.β⁻¹ : G.Cˣ) : G.C) = algebraMap ℚ G.C s * ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) *
      ((y : G.C) * ((P₁.β : G.C) * sh G y * ((P₁.β⁻¹ : G.Cˣ) : G.C)))) : DPair.Rel P Q := by
  refine ⟨y, s, hs, ?_, ?_⟩
  · have h1 : ((Q.β * P₁.β⁻¹ : G.Cˣ) : G.C) * (P₁.β : G.C) = Q.β := by
      rw [← Units.val_mul, inv_mul_cancel_right]
    have h2 : ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) * (P₁.β : G.C) = P.β := by
      rw [← Units.val_mul, inv_mul_cancel_right]
    rw [← h1, hr, ← h2]
    generalize ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) = a at ha ⊢
    calc algebraMap ℚ G.C s * a * ((y : G.C) * ((P₁.β : G.C) * sh G y * ((P₁.β⁻¹ : G.Cˣ) : G.C))) * P₁.β
        = algebraMap ℚ G.C s * ((a * y) * ((P₁.β : G.C) * sh G y) *
            (((P₁.β⁻¹ : G.Cˣ) : G.C) * P₁.β)) := by simp only [mul_assoc]
      _ = _ := by rw [Units.inv_mul, mul_one, ha]; simp only [mul_assoc]
  · have hy' : y * P₁.γ = P₁.γ * y := Units.ext (by simpa using hy)
    rw [hQ, hP, hy', mul_inv_cancel_right]

theorem supp_compact (L : G.Level) (f : G.GAf → ℂ)
    (hT : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) :
    ∃ Ω : Set G.GAf, IsCompact Ω ∧ ∀ g, f g ≠ 0 → g ∈ Ω := by
  obtain ⟨-, -, -, S, hS⟩ := hT
  refine ⟨⋃ s ∈ S, (fun k : G.GAf × G.GAf => k.1 * s * k.2) '' ((L.K : Set G.GAf) ×ˢ (L.K : Set G.GAf)),
    S.isCompact_biUnion fun s _ => (L.compact.prod L.compact).image (by fun_prop), fun g hg => ?_⟩
  obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
  exact Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩

theorem finite_of_compact (Ω : Set G.GAf) (hΩ : IsCompact Ω) (γ₀ : G.Cˣ)
    (hirr : Irreducible (minpoly G.F (γ₀ : G.C))) (c₀ : ℚˣ) :
    {q : DCls G | ∃ P : DPair G, (Quot.mk DPair.Rel P : DCls G) = q ∧ P.γ = γ₀ ∧ P.c = c₀ ∧
      ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.toAf x t hx P.self ∈ Ω}.Finite := by
  set Y : Set (DPair G) := {P | P.γ = γ₀ ∧ P.c = c₀ ∧
      ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.toAf x t hx P.self ∈ Ω} with hYdef
  have hset : {q : DCls G | ∃ P : DPair G, (Quot.mk DPair.Rel P : DCls G) = q ∧ P.γ = γ₀ ∧ P.c = c₀ ∧
      ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.toAf x t hx P.self ∈ Ω} =
      Quot.mk DPair.Rel '' Y := by
    ext q; constructor
    · rintro ⟨P, rfl, h⟩; exact ⟨P, h, rfl⟩
    · rintro ⟨P, h, rfl⟩; exact ⟨P, rfl, h⟩
  rw [hset]
  rcases Y.eq_empty_or_nonempty with hY | ⟨P₁, hP₁⟩
  · rw [hY, Set.image_empty]; exact Set.finite_empty
  have hirr₁ : Irreducible (minpoly G.F (P₁.γ : G.C)) := by rw [hP₁.1]; exact hirr
  obtain ⟨L, _, _, ι, c, hinj, hcent, hc, hcc⟩ :=
    GlobalTheory.T.exists_numberField_involution_similitudeCentralizer p G P₁.β P₁.γ P₁.c P₁.sym P₁.sim hirr₁ P₁.reg.1
  obtain ⟨S, hloc⟩ := GlobalTheory.T.definitePairs_ratio_locally_rational_times_norm p G Ω hΩ P₁ L ι c hinj hcent hc
  have hγ : ∀ P ∈ Y, P.γ = P₁.γ := fun P hP => hP.1.trans hP₁.1.symm
  have hcc' : ∀ P ∈ Y, P.c = P₁.c := fun P hP => hP.2.1.trans hP₁.2.1.symm
  have ha : ∀ P ∈ Y, ∃ a : L, ι a = ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) := fun P hP =>
    (hcent _).1 (quot_commute_and_fixed P P₁ (hγ P hP) (hcc' P hP)).1
  set X : Set L := {a | ∃ P ∈ Y, ι a = ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C)} with hXdef
  obtain ⟨R, hR⟩ := GlobalTheory.FixedNormCls.finite_classes_mod_rat_norms L c hcc S X (by
    rintro a ⟨P, hP, hPa⟩
    refine ⟨fun h0 => ?_, hinj ?_, fun v hv => hloc P (hγ P hP) (hcc' P hP) hP.2.2 a hPa v hv⟩
    · rw [h0, map_zero] at hPa
      exact (P.β * P₁.β⁻¹).ne_zero hPa.symm
    · rw [hc, hPa]; exact (quot_commute_and_fixed P P₁ (hγ P hP) (hcc' P hP)).2)
  let good : L → Prop → DPair G → Prop := fun b s P => P ∈ Y ∧ ∃ (a : L) (q : ℚ) (z : L),
    ι a = ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) ∧ (0 < q ↔ s) ∧ q ≠ 0 ∧ z ≠ 0 ∧ a = algebraMap ℚ L q * b * (z * c z)
  let rep : L × Bool → DPair G := fun bs => if h : ∃ P, good bs.1 (bs.2 = true) P then h.choose else P₁
  refine ((R ×ˢ (Finset.univ : Finset Bool) : Finset (L × Bool)).finite_toSet.image
    (fun bs => Quot.mk DPair.Rel (rep bs))).subset ?_
  rintro _ ⟨P, hP, rfl⟩
  obtain ⟨a, hPa⟩ := ha P hP
  obtain ⟨b, hb, q, z, hq, hz, hab⟩ := hR a ⟨P, hP, hPa⟩
  have hex : ∃ P', good b (decide (0 < q) = true) P' := ⟨P, hP, a, q, z, hPa, decide_eq_true_iff.symm, hq, hz, hab⟩
  refine ⟨(b, decide (0 < q)), Finset.mem_coe.2 (Finset.mem_product.2 ⟨hb, Finset.mem_univ _⟩), ?_⟩
  have hrep : rep (b, decide (0 < q)) = hex.choose := dif_pos hex
  obtain ⟨hP', a', q', z', hPa', hsgn, hq', hz', hab'⟩ := hex.choose_spec
  simp only [hrep]
  apply Quot.sound
  set P' := hex.choose
  have hpos : 0 < q / q' := by
    have hs : (0 < q' ↔ 0 < q) := by simpa using hsgn
    rcases lt_or_gt_of_ne hq with h | h
    · exact div_pos_of_neg_of_neg h (lt_of_le_of_ne (not_lt.1 (fun h' => absurd (hs.1 h') (not_lt.2 h.le))) hq')
    · exact div_pos h (hs.2 h)
  set w : L := z / z' with hw
  have hw0 : w ≠ 0 := div_ne_zero hz hz'
  let y : G.Cˣ := Units.map ι.toMonoidHom (Units.mk0 w hw0)
  have hy : (y : G.C) = ι w := rfl
  have hrat : a = algebraMap ℚ L (q / q') * a' * (w * c w) := by
    rw [hab, hab', hw, map_div₀, map_div₀]
    have hcz' : c z' ≠ 0 := by
      intro h; apply hz'; have := congrArg c h; rwa [hcc, map_zero] at this
    have hq'' : algebraMap ℚ L q' ≠ 0 := (map_ne_zero _).2 hq'
    field_simp
  apply rel_of_ratio P' P P₁ y (q / q') hpos (hγ P' hP') (hγ P hP)
  · rw [hy]; exact ((hcent _).2 ⟨w, rfl⟩)
  · rw [hy, ← hPa', ← map_mul, ← map_mul, mul_comm]
  · rw [← hPa, hrat, hy, ← hPa', ← hc, map_mul, map_mul, map_mul, AlgHom.commutes]

theorem finite_classes_fixed_gamma (L : G.Level) (f : G.GAf → ℂ)
    (hT : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) (γ₀ : G.Cˣ)
    (hirr : Irreducible (minpoly G.F (γ₀ : G.C))) (c₀ : ℚˣ) :
    {q : DCls G | ∃ P : DPair G, (Quot.mk DPair.Rel P : DCls G) = q ∧ P.γ = γ₀ ∧ P.c = c₀ ∧
      ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf),
        f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0}.Finite := by
  obtain ⟨Ω, hΩ, hf⟩ := supp_compact L f hT
  refine (finite_of_compact Ω hΩ γ₀ hirr c₀).subset ?_
  rintro q ⟨P, rfl, hγ, hc, x, t, hx, g, hne⟩
  obtain ⟨x', t', hx', he⟩ := exists_triv_toAf_eq_conj P x t hx g
  exact ⟨P, rfl, hγ, hc, x', t', hx', he ▸ hf _ hne⟩

end GlobalTheory.LKDefFin


open GlobalTheory.LKDef GlobalTheory.LKDefFin in
theorem GlobalTheory.LKDefFin.finite_classes_of_pol : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      ∀ P0 : Polynomial G.F, {q : GlobalTheory.LKDef.DCls G | (Quot.out q).pol = P0 ∧ Irreducible (Quot.out q).pol ∧
        (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  intro p _ G _ L f hf _ K' f' _ _ P0
  by_cases hne : {q : DCls G | (Quot.out q).pol = P0 ∧ Irreducible (Quot.out q).pol ∧
      (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Nonempty
  · obtain ⟨q₀, hq₀⟩ := hne
    have hirr₀ : Irreducible (minpoly G.F ((Quot.out q₀).γ : G.C)) := hq₀.2.1
    refine ((finite_classes_fixed_gamma L f hf (Quot.out q₀).γ hirr₀ (Quot.out q₀).c).union
      (finite_classes_fixed_gamma L f hf (Quot.out q₀).γ hirr₀ (-(Quot.out q₀).c))).subset ?_
    intro q hq
    obtain ⟨x, t, hx, g, hg⟩ := exists_ne_zero_of_term_ne_zero _ _ _ _ _ _ hq.2.2
    have hpol : minpoly G.F ((Quot.out q₀).γ : G.C) = minpoly G.F ((Quot.out q).γ : G.C) :=
      hq₀.1.trans hq.1.symm
    have hirrq : Irreducible (minpoly G.F ((Quot.out q).γ : G.C)) := hq.2.1
    obtain ⟨y, hy⟩ := GlobalTheory.LKCx.units_conj_of_minpoly_eq_of_irreducible p G (Quot.out q₀).γ (Quot.out q).γ hpol hirrq
    obtain ⟨P', hrel, hγ, hc', htr⟩ := exists_conj (Quot.out q) y
    obtain ⟨x', hx', he⟩ := htr x t hx
    have hq' : (Quot.mk DPair.Rel P' : DCls G) = q := by
      rw [← Quot.sound hrel]; exact Quot.out_eq q
    have hγ' : P'.γ = (Quot.out q₀).γ := by
      rw [hγ]; apply Units.ext; rw [hy]; simp
    have hg' : f (g⁻¹ * P'.toAf x' t hx' P'.self * g) ≠ 0 := by rw [he]; exact hg
    rcases c_eq_or_eq_neg (Quot.out q₀) P' hγ' with hc | hc
    · exact Or.inl ⟨P', hq', hγ', hc, x', t, hx', g, hg'⟩
    · exact Or.inr ⟨P', hq', hγ', hc, x', t, hx', g, hg'⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]; exact Set.finite_empty
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDefinitePairClassesFixedMinpolyDegreeOneStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_definitePair_classes_fixed_minpoly_degree_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      ∀ P0 : Polynomial G.F, {q : GlobalTheory.LKDef.DCls G | (Quot.out q).pol = P0 ∧ Irreducible (Quot.out q).pol ∧
        (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  first | (exact @GlobalTheory.LKDefFin.finite_classes_of_pol) | (exact GlobalTheory.LKDefFin.finite_classes_of_pol) | (intros; apply GlobalTheory.LKDefFin.finite_classes_of_pol <;> assumption)
end
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef.FinPairs

theorem finite_classes_irr_term_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      {q : GlobalTheory.LKDef.DCls G | Irreducible (Quot.out q).pol ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  intro p _ G ha L f hf hfb K' f' hf' hfb'
  refine ((GlobalTheory.T.finite_minpoly_definitePairs_term_ne_zero p G ha L f hf hfb K' f' hf' hfb').biUnion
    (fun P0 _ => GlobalTheory.T.finite_definitePair_classes_fixed_minpoly_degree_one p G ha L f hf hfb K' f' hf' hfb' P0)).subset ?_
  intro q hq
  exact Set.mem_biUnion (x := (Quot.out q).pol) ⟨Quot.out q, rfl, hq.1, hq.2⟩ ⟨rfl, hq.1, hq.2⟩

end GlobalTheory.LKDef.FinPairs
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.bi_invariant_conjugacy_classes_finite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      {q : GlobalTheory.LKDef.DCls G | Irreducible (Quot.out q).pol ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  first | exact @GlobalTheory.LKDef.FinPairs.finite_classes_irr_term_ne_zero | exact GlobalTheory.LKDef.FinPairs.finite_classes_irr_term_ne_zero

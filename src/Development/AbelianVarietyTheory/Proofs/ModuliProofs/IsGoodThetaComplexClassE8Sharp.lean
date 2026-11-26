module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GoodThetaClassOfLatticeFamilies
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BijectiveTensorOmegaStd
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerThetaObjectOfUniformisation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPeriodsEighthPowerEvenUnimodularBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivPiRangeOfMatrixUnits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_equiv_pi_range_of_matrixUnits {R M n : Type} [CommRing R] [AddCommGroup M]
    [Module R M] [Fintype n] [DecidableEq n] (p q : n → M →ₗ[R] M) (P : M →ₗ[R] M)
    (hpq : ∀ u v x, p u (q v x) = if u = v then P x else 0)
    (hs : ∀ x, ∑ u, q u (p u x) = x) (hP : ∀ x, P (P x) = P x) :
    ∃ φ : M ≃ₗ[R] (n → LinearMap.range P), (∀ x u, (φ x u : M) = p u x) ∧
      ∀ x, x = ∑ u, q u (φ x u) := by
  have hmem : ∀ u x, p u x ∈ LinearMap.range P := fun u x => by
    refine ⟨p u x, ?_⟩
    conv_rhs => rw [← hs x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, hpq]
  let f : M →ₗ[R] (n → LinearMap.range P) :=
    LinearMap.pi fun u => (p u).codRestrict _ (hmem u)
  have hf : ∀ x u, (f x u : M) = p u x := fun _ _ => rfl
  have hb : Function.Bijective f := by
    refine ⟨(injective_iff_map_eq_zero f).2 fun x hx => ?_, fun y => ⟨∑ v, q v (y v), ?_⟩⟩
    · rw [← hs x]
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [← hf, hx]; simp
    · funext u
      apply Subtype.ext
      rw [hf]
      obtain ⟨z, hz⟩ := (y u).2
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, hpq, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [← hz, hP]
  exact ⟨LinearEquiv.ofBijective f hb, hf, fun x => (hs x).symm⟩

theorem matrixUnits_apply {La : Type} [AddCommGroup La]
    (r : Matrix (Fin 8) (Fin 8) ℤ →+* Module.End ℤ La) :
    (∀ u v x, r (Matrix.single 0 u 1) (r (Matrix.single v 0 1) x) =
      if u = v then r (Matrix.single 0 0 1) x else 0) ∧
    (∀ x, ∑ u, r (Matrix.single u 0 1) (r (Matrix.single 0 u 1) x) = x) ∧
    (∀ x, r (Matrix.single 0 0 1) (r (Matrix.single 0 0 1) x) = r (Matrix.single 0 0 1) x) := by
  refine ⟨fun u v x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [← Module.End.mul_apply, ← map_mul]
    split_ifs with huv
    · subst huv; simp
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ huv]; simp
  · have : (∑ u : Fin 8, Matrix.single u 0 (1:ℤ) * Matrix.single (0 : Fin 8) u (1:ℤ)) = 1 := by
      ext i j
      simp only [Matrix.single_mul_single_same, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, mul_one]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij]
        refine Finset.sum_eq_zero fun u _ => if_neg ?_
        rintro ⟨rfl, rfl⟩; exact hij rfl
    simp only [← Module.End.mul_apply, ← map_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← LinearMap.sum_apply, ← map_sum, this]; simp
  · rw [← Module.End.mul_apply, ← map_mul]; simp

theorem form_matrixUnits_eq {La : Type} [AddCommGroup La] (G : Matrix (Fin 8) (Fin 8) ℤ)
    (EF : LinearMap.BilinForm ℤ La) (r : Matrix (Fin 8) (Fin 8) ℤ →+* Module.End ℤ La)
    (hdet : G.det = 1)
    (hadj : ∀ a a', a.transpose * G = G * a' → ∀ x y, EF (r a x) y = EF x (r a' y)) (u v : Fin 8)
    (x y : La) : EF (r (Matrix.single u 0 1) x) (r (Matrix.single v 0 1) y) =
      G u v * EF x (r (G⁻¹ * Matrix.single 0 0 1) y) := by
  have hu : IsUnit G.det := by simp [hdet]
  rw [hadj _ (G⁻¹ * ((Matrix.single u 0 1).transpose * G))
    (by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]),
    ← Module.End.mul_apply, ← map_mul]
  have : G⁻¹ * ((Matrix.single u (0 : Fin 8) (1:ℤ)).transpose * G) * Matrix.single v (0 : Fin 8) (1:ℤ) =
      G u v • (G⁻¹ * Matrix.single 0 0 1) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_smul, Matrix.transpose_single, Matrix.single_mul_mul_single]
    simp
  rw [this, map_zsmul]
  simp

theorem hermForm_pullback {g h : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (J : Matrix (Fin g) (Fin h) ℂ)
    (c : ℂ) (z w : Fin h → ℂ) :
    hermForm (c • (J.transpose * Hm * J.map star)) z w = c * hermForm Hm (J.mulVec z) (J.mulVec w) := by
  have : star (J.mulVec w) = (J.map star).mulVec (star w) := by
    funext i; simp [Matrix.mulVec, dotProduct]
  simp only [hermForm, this, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec z, Matrix.vecMul_transpose]

theorem exists_form_range_matrixUnit {La : Type} [AddCommGroup La] (G : Matrix (Fin 8) (Fin 8) ℤ)
    (EF : LinearMap.BilinForm ℤ La) (r : Matrix (Fin 8) (Fin 8) ℤ →+* Module.End ℤ La)
    (hG : G 0 0 ≠ 0) (hdet : G.det = 1) (hb : Function.Bijective EF) (halt : ∀ x, EF x x = 0)
    (hadj : ∀ a a', a.transpose * G = G * a' → ∀ x y, EF (r a x) y = EF x (r a' y)) :
    ∃ (φ : La ≃ₗ[ℤ] (Fin 8 → LinearMap.range (r (Matrix.single 0 0 1))))
      (E : LinearMap.BilinForm ℤ (LinearMap.range (r (Matrix.single 0 0 1)))),
      (∀ x u, (φ x u : La) = r (Matrix.single 0 u 1) x) ∧ Function.Bijective E ∧ (∀ x, E x x = 0) ∧
      (∀ x y, EF x y = ∑ u, ∑ v, G u v * E (φ x u) (φ y v)) ∧
      ∀ x y : LinearMap.range (r (Matrix.single 0 0 1)), EF x y = G 0 0 * E x y := by
  obtain ⟨h1, h2, h3⟩ := matrixUnits_apply r
  obtain ⟨φ, hφ, hφ'⟩ := exists_equiv_pi_range_of_matrixUnits (fun u => r (Matrix.single 0 u 1))
    (fun u => r (Matrix.single u 0 1)) (r (Matrix.single 0 0 1)) h1 h2 h3
  have hu : IsUnit G.det := by simp [hdet]
  let E : LinearMap.BilinForm ℤ (LinearMap.range (r (Matrix.single 0 0 1))) :=
    EF.compl₁₂ (Submodule.subtype _) (r (G⁻¹ * Matrix.single 0 0 1) ∘ₗ Submodule.subtype _)
  have hE : ∀ x y, E x y = EF x (r (G⁻¹ * Matrix.single 0 0 1) y) := fun _ _ => rfl
  have hsum : ∀ x y, EF x y = ∑ u, ∑ v, G u v * E (φ x u) (φ y v) := fun x y => by
    conv_lhs => rw [hφ' x, hφ' y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, form_matrixUnits_eq G EF r hdet hadj, hE]
    rw [Finset.sum_comm]
  have hfix : ∀ x : LinearMap.range (r (Matrix.single 0 0 1)), r (Matrix.single 0 0 1) x = x := by
    rintro ⟨_, z, rfl⟩; exact h3 z
  have h00 : ∀ x y : LinearMap.range (r (Matrix.single 0 0 1)), EF x y = G 0 0 * E x y :=
    fun x y => by
      rw [hE, ← form_matrixUnits_eq G EF r hdet hadj, hfix, hfix]
  refine ⟨φ, E, hφ, ⟨(injective_iff_map_eq_zero E).2 fun x hx => ?_, fun f => ?_⟩, fun x => ?_,
    hsum, h00⟩
  · have : EF (φ.symm (Pi.single 0 x)) = 0 := by
      ext y
      rw [hsum]
      refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => ?_
      rw [LinearEquiv.apply_symm_apply]
      by_cases h : u = 0
      · subst h; simp [hx]
      · simp [h]
    have h0 := (injective_iff_map_eq_zero EF).1 hb.1 _ this
    have := congrFun (φ.symm.map_eq_zero_iff.1 h0) 0
    simpa using this
  · obtain ⟨x, hx⟩ := hb.2 (∑ v, G 0 v • (f ∘ₗ LinearMap.proj v ∘ₗ φ.toLinearMap))
    refine ⟨φ x 0, LinearMap.ext fun y => ?_⟩
    have key : ∀ v, ∑ u, E (φ x u) y * G u v = f y * G 0 v := fun v => by
      have := LinearMap.congr_fun hx (φ.symm (Pi.single v y))
      rw [hsum] at this
      simpa [Pi.single_apply, apply_ite, mul_comm] using this
    have k2 : Matrix.vecMul (fun u => E (φ x u) y) G = Matrix.vecMul (Pi.single 0 (f y)) G := by
      funext v
      rw [Matrix.single_vecMul]
      exact key v
    have k3 := congrArg (fun w => Matrix.vecMul w G⁻¹ 0) k2
    simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one] at k3
    simpa using k3
  · have := h00 x x
    rw [halt] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hG

theorem polarised_lattice_eighth_power :
    ∀ (h g : ℕ) (G : Matrix (Fin 8) (Fin 8) ℤ) (σ : Fin 8 × Fin h ≃ Fin g) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (r : Matrix (Fin 8) (Fin 8) ℤ →+* Module.End ℤ La), G.IsSymm → (G.map (Int.cast : ℤ → ℝ)).PosDef → G.det = 1 → Function.Bijective EF → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (∀ a, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ x, F (Q x) = Q (r a x)) → (∀ a a', a.transpose * G = G * a' → ∀ x y, EF (r a x) y = EF x (r a' y)) → ∃ (τ : Matrix (Fin h) (Fin h) ℂ) (e : La ≃+ (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (hh : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (τ).IsSymm ∧ ((τ).map Complex.im).PosDef ∧ (∀ x u i, hh (Q x) (σ (u, i)) = τ.mulVec (fun i' => (e x u (.inl i') : ℂ)) i + (e x u (.inr i) : ℂ)) ∧ (∀ x y, EF x y = ∑ u, ∑ v, G u v * omegaStd (e x u) (e y v)) ∧ ∀ a x u, e (r a x) u = ∑ v, a u v • e x v := by
  intro h g G σ La _ EF Q Hm r _ hpos hdet hb hQ hF hadj
  obtain ⟨hfree, hfin, hrk, halt⟩ :=
    unimodular_symplectic_coordinates_and_lattice_rank.2 La EF g Q Hm hQ
  obtain ⟨hinj, hdisc, hspan, hherm, hHpos, hIm⟩ := hQ
  have hg : g = 8 * h := by simpa using (Fintype.card_congr σ).symm
  have hG : (0 : ℤ) < G 0 0 := by
    have := hpos.diag_pos (i := 0)
    simpa using this
  obtain ⟨φ, E, hφ, hEb, hEalt, hsum, h00⟩ :=
    exists_form_range_matrixUnit G EF r hG.ne' hdet hb halt hadj
  have hrk0 : Module.finrank ℤ (LinearMap.range (r (Matrix.single 0 0 1))) = 2 * h := by
    have := φ.finrank_eq
    rw [hrk, Module.finrank_pi_fintype] at this
    simp at this
    omega
  obtain ⟨bas, hbas⟩ := unimodular_symplectic_coordinates_and_lattice_rank.1 _ E h hEb hEalt hrk0
  choose F hF using hF
  have hspanC : Submodule.span ℂ (Set.range Q) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    exact Submodule.span_subset_span ℝ ℂ _ (hspan ▸ Submodule.mem_top)
  obtain ⟨h1, h2, h3⟩ := matrixUnits_apply r
  obtain ⟨ψ, hψ, -⟩ := exists_equiv_pi_range_of_matrixUnits (fun u => F (Matrix.single 0 u 1))
    (fun u => F (Matrix.single u 0 1)) (F (Matrix.single 0 0 1))
    (fun u v => by
      have : F (Matrix.single 0 u 1) ∘ₗ F (Matrix.single v 0 1) =
          if u = v then F (Matrix.single 0 0 1) else 0 := by
        refine LinearMap.ext_on_range hspanC fun x => ?_
        simp only [LinearMap.comp_apply, hF, h1]
        split_ifs <;> simp [hF]
      intro x
      have := LinearMap.congr_fun this x
      rw [LinearMap.comp_apply] at this
      rw [this]; split_ifs <;> simp)
    (fun z => by
      have : ∑ u, F (Matrix.single u 0 1) ∘ₗ F (Matrix.single 0 u 1) = LinearMap.id := by
        refine LinearMap.ext_on_range hspanC fun x => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [LinearMap.sum_apply, LinearMap.comp_apply, hF, ← map_sum, h2, LinearMap.id_apply]
      simpa using LinearMap.congr_fun this z)
    (fun z => by
      have : F (Matrix.single 0 0 1) ∘ₗ F (Matrix.single 0 0 1) = F (Matrix.single 0 0 1) := by
        refine LinearMap.ext_on_range hspanC fun x => ?_
        simp only [LinearMap.comp_apply, hF, h3]
      exact LinearMap.congr_fun this z)
  have hdim : Module.finrank ℂ (Fin h → ℂ) =
      Module.finrank ℂ (LinearMap.range (F (Matrix.single 0 0 1))) := by
    have := ψ.finrank_eq
    rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype] at this
    simp at this
    simp
    omega
  let j := LinearEquiv.ofFinrankEq _ _ hdim
  let T : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ) :=
    j.symm.toLinearMap ∘ₗ (F (Matrix.single 0 0 1)).rangeRestrict
  let Jl : (Fin h → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Submodule.subtype _ ∘ₗ j.toLinearMap
  have hJT : ∀ z, Jl (T z) = F (Matrix.single 0 0 1) z := fun z => by simp [Jl, T]
  have hJinj : Function.Injective Jl := Subtype.val_injective.comp j.injective
  have hTs : Function.Surjective T :=
    j.symm.surjective.comp (F (Matrix.single 0 0 1)).surjective_rangeRestrict
  let Q₀ : LinearMap.range (r (Matrix.single 0 0 1)) →+ (Fin h → ℂ) :=
    T.toAddMonoidHom.comp (Q.comp (Submodule.subtype _).toAddMonoidHom)
  have hQ₀ : ∀ x, Jl (Q₀ x) = Q x := by
    rintro ⟨_, z, rfl⟩
    change Jl (T (Q _)) = _
    rw [hJT, hF]
    exact congrArg Q (h3 z)
  let J := LinearMap.toMatrix' Jl
  have hJ : ∀ z, J.mulVec z = Jl z := fun z => LinearMap.toMatrix'_mulVec _ _
  have hGR : (0 : ℝ) < G 0 0 := by exact_mod_cast hG
  obtain ⟨m, τ, hm, -, -, hτs, hτp, -, hτ⟩ := GlobalTheory.SiegelPeriod.exists_siegel_form _ E h bas Q₀
    ((((G 0 0 : ℝ)⁻¹ : ℝ) : ℂ) • (J.transpose * Hm * J.map star)) hbas
    ⟨fun x y hxy => Subtype.ext (hinj (by rw [← hQ₀, ← hQ₀, hxy])),
      by
        let f : Q₀.range → Q.range := fun z => ⟨Jl z, by
          obtain ⟨x, hx⟩ := z.2
          exact ⟨x, by rw [← hx, hQ₀]⟩⟩
        exact DiscreteTopology.of_continuous_injective (f := f)
          ((Jl.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _)
          fun a b hab => Subtype.ext (hJinj (congrArg (fun z : Q.range => (z : Fin g → ℂ)) hab)),
      by
        rw [eq_top_iff]
        intro z _
        obtain ⟨w, rfl⟩ := hTs z
        have hw : w ∈ Submodule.span ℝ (Set.range Q) := hspan ▸ Submodule.mem_top
        refine Submodule.span_mono ?_
          (Submodule.apply_mem_span_image_of_mem_span (T.restrictScalars ℝ) hw)
        rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
        refine ⟨⟨_, x, rfl⟩, hJinj ?_⟩
        rw [hQ₀, LinearMap.restrictScalars_apply, hJT, hF],
      by
        have e1 : J.map star = J.transpose.conjTranspose := by ext; simp
        rw [e1]
        have := Matrix.isHermitian_mul_mul_conjTranspose J.transpose hherm
        unfold Matrix.IsHermitian at this ⊢
        rw [Matrix.conjTranspose_smul, this]; simp,
      fun z hz => by
        rw [hermForm_pullback, Complex.re_ofReal_mul, hJ]
        exact mul_pos (inv_pos.2 hGR) (hHpos _ fun h0 => hz (hJinj (by rw [h0, map_zero]))),
      fun x y => by
        rw [hermForm_pullback, Complex.im_ofReal_mul, hJ, hJ, hQ₀, hQ₀, hIm, h00]
        push_cast
        field_simp⟩
  let mE : (Fin h → ℂ) ≃ₗ[ℂ] (Fin h → ℂ) := Matrix.toLinearEquiv' m hm.invertible
  have hmE : ∀ z, mE z = m.mulVec z := fun _ => rfl
  let e : La ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) :=
    φ ≪≫ₗ LinearEquiv.piCongrRight fun _ => bas.symm
  have he : ∀ x u, e x u = bas.symm (φ x u) := fun _ _ => rfl
  let hh : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) :=
    ψ ≪≫ₗ (LinearEquiv.piCongrRight fun _ => j.symm ≪≫ₗ mE) ≪≫ₗ
      (LinearEquiv.curry ℂ ℂ (Fin 8) (Fin h)).symm ≪≫ₗ LinearEquiv.funCongrLeft ℂ ℂ σ.symm
  have hhh : ∀ z u i, hh z (σ (u, i)) = m.mulVec (j.symm (ψ z u)) i := fun z u i => by
    simp [hh, hmE]
  refine ⟨τ, e.toAddEquiv, hh, hτs, hτp, fun x u i => ?_, fun x y => ?_, fun a x u => ?_⟩
  · have e1 : j.symm (ψ (Q x) u) = Q₀ (bas (e x u)) := by
      apply hJinj
      rw [hQ₀, he, LinearEquiv.apply_symm_apply, hφ, ← hF, ← hψ]
      simp [Jl]
    rw [hhh, e1, hτ]
    rfl
  · rw [hsum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    change G u v * E (φ x u) (φ y v) = G u v * omegaStd (bas.symm (φ x u)) (bas.symm (φ y v))
    rw [← hbas, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  · change bas.symm (φ (r a x) u) = ∑ v, a u v • bas.symm (φ x v)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum]
    refine congrArg bas.symm (Subtype.ext ?_)
    have : Matrix.single (0 : Fin 8) u (1 : ℤ) * a = ∑ v, a u v • Matrix.single (0 : Fin 8) v (1 : ℤ) := by
      ext i k
      by_cases hi : i = 0
      · subst hi; simp [Matrix.sum_apply, Matrix.single_apply]
      · simp [Matrix.sum_apply, Matrix.single_apply, hi, Ne.symm hi]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hφ, ← Module.End.mul_apply, ← map_mul, this, map_sum, LinearMap.sum_apply,
      Submodule.coe_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_zsmul, LinearMap.smul_apply, Submodule.coe_smul, hφ]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPeriodsEighthPowerEvenUnimodularBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SharpPeriods

theorem zpow_finsum' {G I : Type*} [CommGroup G] (x : G) (s : Finset I) (f : I → ℤ) :
    x ^ (∑ i ∈ s, f i) = ∏ i ∈ s, x ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add, ih]

section Mat
variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj B]

theorem comp_finprod {T T' : Over S} (f : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ B)) :
    f ≫ (∏ v, x v) = ∏ v, f ≫ x v := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp [MonObj.comp_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]

theorem exists_matrix_action {n : ℕ} (pr : Fin n → (A ⟶ B)) (hpr : ∀ u, IsMonHom (pr u))
    (hu : ∀ (T : Over S) (y : Fin n → (T ⟶ B)), ∃! x : T ⟶ A, ∀ u, x ≫ pr u = y u) :
    ∃ α : Matrix (Fin n) (Fin n) ℤ → (A ⟶ A), (∀ m u, α m ≫ pr u = ∏ v, pr v ^ m u v) ∧
      (∀ m, IsMonHom (α m)) ∧ α 1 = 𝟙 A ∧ (∀ m m', α (m * m') = α m' ≫ α m) ∧
      ∀ m m', α (m + m') = α m * α m' := by
  classical
  have hext : ∀ (T : Over S) (x x' : T ⟶ A), (∀ u, x ≫ pr u = x' ≫ pr u) → x = x' :=
    fun T x x' h => (hu T (fun u => x' ≫ pr u)).unique h (fun _ => rfl)
  choose α hα _ using fun m : Matrix (Fin n) (Fin n) ℤ => hu A (fun u => ∏ v, pr v ^ m u v)
  have hα' : ∀ m u (T : Over S) (x : T ⟶ A), x ≫ α m ≫ pr u = ∏ v, (x ≫ pr v) ^ m u v := by
    intro m u T x
    rw [hα, comp_finprod]
    simp only [GrpObj.comp_zpow]
  refine ⟨α, hα, fun m => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · refine hext _ _ _ fun u => ?_
    haveI := hpr
    rw [Category.assoc, hα', MonObj.one_eq_one]
    simp [MonObj.one_comp]
  · refine hext _ _ _ fun u => ?_
    haveI := hpr
    rw [Category.assoc, hα', MonObj.mul_eq_mul]
    simp only [MonObj.comp_mul, MonObj.mul_comp, tensorHom_fst, tensorHom_snd, Category.assoc, hα', mul_zpow,
      Finset.prod_mul_distrib]
  · refine hext _ _ _ fun u => ?_
    rw [hα, Category.id_comp, Finset.prod_eq_single u]
    · simp
    · intro v _ hv
      simp [Matrix.one_apply_ne hv.symm]
    · simp
  · intro m m'
    refine hext _ _ _ fun u => ?_
    rw [Category.assoc, hα', hα]
    simp only [hα, ← Finset.prod_zpow, ← zpow_mul, Matrix.mul_apply]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [zpow_finsum']
    exact Finset.prod_congr rfl fun v _ => by rw [mul_comm]
  · intro m m'
    refine hext _ _ _ fun u => ?_
    haveI := hpr
    rw [MonObj.mul_comp, hα, hα, hα, ← Finset.prod_mul_distrib]
    simp only [Matrix.add_apply, zpow_add]
end Mat

theorem linear_eq_zero_of_mem {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, F z ∈ Λ) : F = 0 := by
  refine LinearMap.ext fun z => ?_
  have hc : Continuous (fun t : ℂ => (⟨F (t • z), h _⟩ : Λ)) := by
    refine Continuous.subtype_mk ?_ _
    simp only [map_smul]
    fun_prop
  have := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℂ) hc (x := 1) (y := 0)
  simpa using congrArg Subtype.val this

section Unif
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_eq_iff (z w : Fin g → ℂ) : u.ex z = u.ex w ↔ z - w ∈ u.Λ := by
  rw [← u.ker]
  have : u.ex z = u.ex (z - w) * u.ex w := by rw [← u.ex_add, sub_add_cancel]
  rw [this]
  exact mul_eq_right

theorem lift_unique {F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (h : ∀ z, u.ex (F z) = u.ex (F' z)) : F = F' := by
  haveI := u.discrete
  exact sub_eq_zero.1 (linear_eq_zero_of_mem u.Λ (F - F') fun z => (ex_eq_iff u _ _).1 (h z))

theorem exists_lattice_action {R La : Type} [Ring R] [AddCommGroup La] (Q : La →+ (Fin g → ℂ))
    (hQ : Function.Injective Q) (hΛ : ∀ z, z ∈ u.Λ ↔ z ∈ Q.range) (α : R → (A ⟶ A)) (hm : ∀ m, IsMonHom (α m))
    (h1 : α 1 = 𝟙 A) (hmul : ∀ m m', α (m * m') = α m' ≫ α m) (hadd : ∀ m m', α (m + m') = α m * α m')
    (F : R → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ m z, u.ex (F m z) = u.ex z ≫ α m) :
    ∃ r : R →+* Module.End ℤ La, ∀ m x, F m (Q x) = Q (r m x) := by
  have hmem : ∀ m x, F m (Q x) ∈ Q.range := by
    intro m x
    haveI := hm m
    rw [← hΛ, ← u.ker, hF, (u.ker _).2 ((hΛ _).2 ⟨x, rfl⟩), MonObj.one_comp]
  choose f hf using hmem
  have F1 : F 1 = LinearMap.id := lift_unique u fun z => by rw [hF, h1]; simp
  have Fmul : ∀ m m', F (m * m') = F m ∘ₗ F m' := fun m m' => lift_unique u fun z => by
    rw [hF, hmul, LinearMap.comp_apply, hF, hF, Category.assoc]
  have Fadd : ∀ m m', F (m + m') = F m + F m' := fun m m' => lift_unique u fun z => by
    rw [hF, hadd, LinearMap.add_apply, u.ex_add, hF, hF, MonObj.comp_mul]
  let r₀ : R → Module.End ℤ La := fun m => (AddMonoidHom.mk' (f m) fun x y => hQ (by
    rw [map_add (f := _), hf, hf, hf, map_add (f := _), map_add (f := _)])).toIntLinearMap
  have hr₀ : ∀ m x, Q (r₀ m x) = F m (Q x) := hf
  refine ⟨RingHom.mk' ⟨⟨r₀, ?_⟩, ?_⟩ ?_, fun m x => (hr₀ m x).symm⟩
  · ext x
    apply hQ
    rw [hr₀, F1]; rfl
  · intro m m'
    ext x
    apply hQ
    simp only [Module.End.mul_apply, hr₀, Fmul, LinearMap.comp_apply]
  · intro m m'
    ext x
    apply hQ
    change Q (r₀ (m + m') x) = Q (r₀ m x + r₀ m' x)
    simp only [map_add (f := _), hr₀, Fadd, LinearMap.add_apply]
end Unif

theorem exists_level_map {P P' I : Type} [Group P] [CommGroup P'] [Fintype I] {n k : ℕ} (u₀ : Fin n)
    (π : Fin n → (P →* P')) (hinj : ∀ x x', (∀ u, π u x = π u x') → x = x')
    (hsurj : ∀ y : Fin n → P', ∃ x, ∀ u, π u x = y u)
    (φ : (Fin n → (I → ℤ)) → P) (hφ : ∀ x y, φ (x + y) = φ x * φ y) (htor : ∀ p, p ^ k = 1 → ∃ x, φ x = p)
    (hψ : ∀ x u, π u (φ x) = π u₀ (φ (Pi.single u₀ (x u))))
    (lev : (I → ℤ) → P') (hadd : ∀ x y, lev (x + y) = lev x * lev y) (hlt : ∀ x, lev x ^ k = 1) :
    ∃ m : (I → ℤ) →+ (I → ℤ), ∀ (x : Fin n → (I → ℤ)) u, π u (φ fun v => m (x v)) = lev (x u) := by
  classical
  let ψ : (I → ℤ) →+ Additive P' := AddMonoidHom.mk' (fun y => Additive.ofMul (π u₀ (φ (Pi.single u₀ y))))
    fun x y => by rw [Pi.single_add, hφ, map_mul, ofMul_mul]
  let lv : (I → ℤ) →+ Additive P' := AddMonoidHom.mk' (fun y => Additive.ofMul (lev y))
    fun x y => by rw [hadd, ofMul_mul]
  have hex : ∀ y, ∃ z, ψ z = lv y := by
    intro y
    obtain ⟨p, hp⟩ := hsurj fun _ => lev y
    obtain ⟨z, rfl⟩ := htor p (hinj _ _ fun u => by rw [map_pow, hp, hlt, map_one])
    refine ⟨z u₀, ?_⟩
    change Additive.ofMul _ = Additive.ofMul _
    rw [← hψ, hp]
  choose z hz using hex
  let m : (I → ℤ) →ₗ[ℤ] (I → ℤ) := (Pi.basisFun ℤ I).constr ℤ fun s => z (Pi.basisFun ℤ I s)
  have hm : ψ.toIntLinearMap ∘ₗ m = lv.toIntLinearMap := (Pi.basisFun ℤ I).ext fun s => by
    rw [LinearMap.comp_apply, Module.Basis.constr_basis]
    exact hz _
  refine ⟨m.toAddMonoidHom, fun x u => ?_⟩
  rw [hψ]
  exact Additive.ofMul.injective (LinearMap.congr_fun hm (x u))

theorem zpow_bilin_ext {G X I : Type} [CommGroup G] [AddCommGroup X] (b : Module.Basis I ℤ X) (ξ ζ : G)
    (B B' : LinearMap.BilinForm ℤ X) (h : ∀ i j, ξ ^ B (b i) (b j) = ζ ^ B' (b i) (b j)) (x y : X) :
    ξ ^ B x y = ζ ^ B' x y := by
  have : B.compr₂ (LinearMap.toSpanSingleton ℤ (Additive G) (Additive.ofMul ξ)) =
      B'.compr₂ (LinearMap.toSpanSingleton ℤ (Additive G) (Additive.ofMul ζ)) :=
    LinearMap.ext_basis b b fun i j => congrArg Additive.ofMul (h i j)
  exact Additive.ofMul.injective (LinearMap.congr_fun₂ this x y)

theorem omegaStd_zero_left {h : ℕ} (y : Fin h ⊕ Fin h → ℤ) : omegaStd 0 y = 0 := by simp [omegaStd]

theorem omegaStd_smul_right {h : ℕ} (c : ℤ) (x y : Fin h ⊕ Fin h → ℤ) : omegaStd x (c • y) = c * omegaStd x y := by
  simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem multiplier_of_power {G₀ : Type} [CommGroup G₀] {h g k : ℕ} (G : Matrix (Fin 8) (Fin 8) ℤ) (hG : G.det = 1)
    (EF : LinearMap.BilinForm ℤ (Fin 8 → (Fin h ⊕ Fin h → ℤ)))
    (hEF : ∀ x y, EF x y = ∑ u, ∑ v, G u v * omegaStd (x u) (y v))
    (bas : (Fin g → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (m : (Fin h ⊕ Fin h → ℤ) →+ (Fin h ⊕ Fin h → ℤ))
    (ξ ζ : G₀) (hξ : ξ ^ k = 1) (lam : Fin g → (Fin 8 → (Fin h ⊕ Fin h → ℤ)))
    (hlam : ∀ i, ∃ y, lam i = (fun u => m (bas (Pi.single i 1) u)) + k • y)
    (hlev : ∀ i j, ξ ^ EF (lam i) (lam j) = ζ ^ EF (bas (Pi.single i 1)) (bas (Pi.single j 1))) (x y) :
    ξ ^ omegaStd (m x) (m y) = ζ ^ omegaStd x y := by
  classical
  let M : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) := m.toIntLinearMap.compLeft (Fin 8)
  have hk : ∀ c : ℤ, ξ ^ (k • c) = 1 := fun c => by rw [nsmul_eq_mul, zpow_mul, zpow_natCast, hξ, one_zpow]
  have key := zpow_bilin_ext ((Pi.basisFun ℤ (Fin g)).map bas) ξ ζ (EF.compl₁₂ M M) EF (fun i j => by
    obtain ⟨y, hy⟩ := hlam i
    obtain ⟨y', hy'⟩ := hlam j
    simp only [Module.Basis.map_apply, Pi.basisFun_apply, LinearMap.compl₁₂_apply]
    rw [← hlev, hy, hy']
    simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, zpow_add, hk, _root_.mul_one]
    rfl)
  have hc : ∑ v, G 0 v * G.adjugate v 0 = 1 := by
    have := congrFun (congrFun (Matrix.mul_adjugate G) 0) 0
    simpa [Matrix.mul_apply, hG] using this
  have hE : ∀ x y, EF (Pi.single 0 x) (fun v => G.adjugate v 0 • y) = omegaStd x y := by
    intro x y
    rw [hEF, Finset.sum_eq_single 0]
    · simp only [Pi.single_eq_same, omegaStd_smul_right, ← _root_.mul_assoc, ← Finset.sum_mul, hc, _root_.one_mul]
    · intro u _ hu
      simp [Pi.single_eq_of_ne hu, omegaStd_zero_left]
    · simp
  have := key (Pi.single 0 x) (fun v => G.adjugate v 0 • y)
  rw [hE, LinearMap.compl₁₂_apply] at this
  rw [← this, ← hE]
  congr 2
  · congr 1
    funext u
    by_cases hu : u = 0
    · subst hu; simp [M]
    · simp [M, Pi.single_eq_of_ne hu]
  · funext u
    exact (map_zsmul m _ _).symm

end GlobalTheory.SharpPeriods


open GlobalTheory.SharpPeriods in
theorem GlobalTheory.exists_periods_of_sharpClass : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (σ : Fin 8 × Fin h ≃ Fin g) (EF : LinearMap.BilinForm ℤ (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ x y, EF x y = ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (x u) (y v)) → ∀ t : TObj g k J b (spMap em), SharpClass W a bas em t → ∃ (τ : Matrix (Fin h) (Fin h) ℂ) (m : (Fin h ⊕ Fin h → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (Q : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), ((τ).IsSymm ∧ ((τ).map Complex.im).PosDef) ∧ (∀ x y, Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd (m x) (m y) : ℂ) / k) = em (b.ζ : o) ^ omegaStd x y) ∧ (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) ∧ (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i u => m (bas (Pi.single i 1) u)) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  intro hL hL2 hth hU o _ g k J b em w w' h W a bas σ EF hE8 hbas hw hw' hEF t ht
  classical
  have hprim := (GlobalTheory.sharpClass_prim_and_iso hth o g k J b em w w' h W a bas t ht).1 hE8 hw hw'
  obtain ⟨La, _, EF0, lam, ac, Q0, Hm0, hbij, hpol, hlev, u, χ, hAH, hΛ, hχ, hpt, hact⟩ :=
    GlobalTheory.PrimUnif.exists_unif_of_prim hL hL2 hth hU o g k J b em w w' t hprim
  obtain ⟨c, -, pr, hpr, huniv, hLB, hactpr, hptpr⟩ := ht
  have hext : ∀ (T : Over (Sp ℂ)) (x x' : T ⟶ t.A), (∀ u, x ≫ pr u = x' ≫ pr u) → x = x' :=
    fun T x x' h => (huniv T (fun u => x' ≫ pr u)).unique h (fun _ => rfl)
  obtain ⟨α, hα, hαm, hα1, hαmul, hαadd⟩ := exists_matrix_action pr hpr huniv
  have hα' : ∀ m u, α m ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod := fun m u => by
    rw [hα, List.prod_ofFn]
  have hF : ∀ m, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ α m := fun m =>
    GlobalTheory.exists_linear_lift_of_isMonHom_polAV t.pol t.pol t.L t.L u u (α m) (hαm m)
  choose F hF using hF
  obtain ⟨r, hr⟩ := exists_lattice_action u Q0 hpol.1 hΛ α hαm hα1 hαmul hαadd F hF
  have hadj : ∀ m m', m.transpose * (W + W.transpose) = (W + W.transpose) * m' →
      ∀ x y, EF0 (r m x) y = EF0 x (r m' y) := by
    intro m m' hmm' x y
    have h1 := (GlobalTheory.T.eighthPower_integerMatrix_primitive_adjoint hth W ℂ o (spMap em) h k _ c t.pol pr hpr huniv hLB m (α m) (hα' m)).2 m' (α m')
      (hα' m') hmm'
    have h2 : hermForm Hm0 (F m (Q0 x)) (Q0 y) = hermForm Hm0 (Q0 x) (F m' (Q0 y)) :=
      (GlobalTheory.T.cubeLineBundle_adjoint_iff_hermForm_adjoint hL hL2 hth hU t.pol u Hm0 χ (α m) (α m') (F m) (F m') hAH (hαm m) (hαm m') (hF m) (hF m')).1
        h1 (Q0 x) (Q0 y)
    rw [hr, hr] at h2
    have h3 := congrArg Complex.im h2
    rw [hpol.2.2.2.2.2, hpol.2.2.2.2.2] at h3
    exact_mod_cast h3
  have hsymm : (W + W.transpose).IsSymm := Matrix.isSymm_add_transpose_self W
  obtain ⟨τ, e, hh, hτ1, hτ2, hQe, hEe, hre⟩ := GlobalTheory.polarised_lattice_eighth_power h g (W + W.transpose) σ La EF0 Q0 Hm0 r hsymm hE8.1 hE8.2
    hbij hpol (fun m => ⟨F m, hr m⟩) hadj
  obtain ⟨Q, Hm, hQ, hpol'⟩ := (GlobalTheory.TensorSiegel.tensor_siegel_lattices h g (W + W.transpose) σ EF hsymm hE8.1 hE8.2 hEF).2.1 τ ⟨hτ1, hτ2⟩
  have hk0 : (k : ℂ) ≠ 0 := by simpa using (b.unit.map em).ne_zero
  have hmul : ∀ z : Fin g → ℂ, k • ((k : ℂ)⁻¹ • z) = z := fun z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hk0, one_smul]
  have hmul' : ∀ z : Fin g → ℂ, (k : ℂ)⁻¹ • (k • z) = z := fun z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk0, one_smul]
  let φ : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) → (𝟙_ (Over (Sp ℂ)) ⟶ t.A) := fun x => u.ex ((k : ℂ)⁻¹ • Q0 (e.symm x))
  let π : Fin 8 → ((𝟙_ (Over (Sp ℂ)) ⟶ t.A) →* (𝟙_ (Over (Sp ℂ)) ⟶ c.A)) := fun v =>
    MonoidHom.mk' (fun x => x ≫ pr v) fun x y => haveI := hpr v; MonObj.mul_comp _ _ _
  have hψ : ∀ x v, π v (φ x) = π 0 (φ (Pi.single 0 (x v))) := by
    intro x v
    have h1 : α (Matrix.single 0 v 1) ≫ pr 0 = pr v := by
      rw [hα, Finset.prod_eq_single v]
      · simp
      · intro v' _ hv'
        simp [Matrix.single_apply, hv'.symm]
      · simp
    have h2 : e.symm (Pi.single 0 (x v)) = r (Matrix.single 0 v 1) (e.symm x) := by
      rw [AddEquiv.symm_apply_eq]
      funext u'
      rw [hre, AddEquiv.apply_symm_apply, Finset.sum_eq_single v]
      · by_cases hu : u' = 0
        · subst hu; simp
        · simp [Pi.single_eq_of_ne hu, Matrix.single_apply, Ne.symm hu]
      · intro v' _ hv'
        simp [Matrix.single_apply, hv'.symm]
      · simp
    change u.ex _ ≫ pr v = u.ex _ ≫ pr 0
    rw [h2, ← hr, ← LinearMap.map_smul, hF, Category.assoc, h1]
  obtain ⟨m, hm⟩ := exists_level_map (k := k) 0 π (hext _) (fun y => (huniv _ y).exists) φ
    (fun x y => by simp only [φ, map_add (f := _), smul_add, u.ex_add])
    (fun p hp => by
      obtain ⟨z, rfl⟩ := u.ex_onto p
      obtain ⟨x, hx⟩ := (hΛ _).1 ((u.ker _).1 ((holUnif_ex_nsmul_eq_pow u z k).trans hp))
      exact ⟨e x, by simp only [φ, AddEquiv.symm_apply_apply, hx, hmul']⟩)
    hψ c.lev c.lev_add c.lev_tors
  have hlam : ∀ i, ∃ y, e (lam i) = (fun u => m (bas (Pi.single i 1) u)) + k • y := by
    intro i
    have h1 : u.ex ((k : ℂ)⁻¹ • Q0 (lam i)) = φ fun u => m (bas (Pi.single i 1) u) := by
      refine hext _ _ _ fun v => ?_
      refine Eq.trans ?_ (hm (bas (Pi.single i 1)) v).symm
      apply Over.OverMorphism.ext
      rw [← hptpr, Over.comp_left, Over.comp_left, hpt]
    obtain ⟨y, hy⟩ := (hΛ _).1 ((ex_eq_iff u _ _).1 h1)
    refine ⟨e y, ?_⟩
    rw [← e.apply_symm_apply (fun u => m (bas (Pi.single i 1) u)), ← map_nsmul, ← map_add (f := _)]
    congr 1
    apply hpol.1
    rw [map_add (f := _), map_nsmul, hy, ← smul_sub, hmul, add_sub_cancel]
  have hEe' : ∀ x y, EF (e x) (e y) = EF0 x y := fun x y => by rw [hEF, hEe]
  refine ⟨τ, m, Q, Hm, ⟨hτ1, hτ2⟩, ?_, hQ, hpol', ?_⟩
  · let ξ : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) / k)) (Complex.exp_ne_zero _)
    have hξ : ∀ n : ℤ, ((ξ ^ n : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k) := fun n => by
      rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← Complex.exp_int_mul]
      congr 1
      ring
    have hζ : ∀ n : ℤ, ((Units.map em.toMonoidHom b.ζ ^ n : ℂˣ) : ℂ) = em (b.ζ : o) ^ n := fun n => by
      rw [Units.val_zpow_eq_zpow_val]; rfl
    have hξk : ξ ^ k = 1 := by
      apply Units.ext
      rw [← zpow_natCast, hξ, Int.cast_natCast, mul_div_cancel_right₀ _ hk0, Complex.exp_neg,
        Complex.exp_two_pi_mul_I]
      simp
    intro x y
    rw [← hξ, ← hζ]
    congr 1
    refine multiplier_of_power (W + W.transpose) hE8.2 EF hEF bas m ξ _ hξk (fun i => e (lam i)) hlam ?_ x y
    intro i j
    apply Units.ext
    rw [hξ, hζ, hEe', hlev, hEF, hbas]
  · refine GlobalTheory.UnifTransport.transport_uniformisation o g k J b em w w' t La EF0 lam ac Q0 Hm0 _ EF (fun i u => m (bas (Pi.single i 1) u))
      (fun j x u => ∑ v, a j u v • x v) Q Hm e hh hpol hpol' ?_ hEe' ?_ hlam
      ⟨u, χ, hAH, hΛ, hχ, hpt, hact⟩
    · intro x
      funext s
      obtain ⟨⟨v, i⟩, rfl⟩ := σ.surjective s
      rw [hQ, hQe]
    · intro j x
      obtain ⟨F', hF'1, hF'2⟩ := hact j
      have h1 : t.act j = α (a j) := hext _ _ _ fun v => by rw [hactpr, hα']
      have h2 : F' = F (a j) := lift_unique u fun z => by rw [hF'2, hF, h1]
      have h3 : ac j x = r (a j) x := hpol.1 (by rw [← hF'1, h2, hr])
      funext v
      rw [h3, hre]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPeriodsEighthPowerEvenUnimodularBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periods_eighthPower_evenUnimodularBundle : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (σ : Fin 8 × Fin h ≃ Fin g) (EF : LinearMap.BilinForm ℤ (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ x y, EF x y = ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (x u) (y v)) → ∀ t : TObj g k J b (spMap em), SharpClass W a bas em t → ∃ (τ : Matrix (Fin h) (Fin h) ℂ) (m : (Fin h ⊕ Fin h → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (Q : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), ((τ).IsSymm ∧ ((τ).map Complex.im).PosDef) ∧ (∀ x y, Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd (m x) (m y) : ℂ) / k) = em (b.ζ : o) ^ omegaStd x y) ∧ (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) ∧ (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i u => m (bas (Pi.single i 1) u)) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  first | exact @GlobalTheory.exists_periods_of_sharpClass | exact GlobalTheory.exists_periods_of_sharpClass | (intros; apply GlobalTheory.exists_periods_of_sharpClass <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGoodThetaComplexClassE8Sharp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SharpGood

theorem exists_representatives {α β : Type} [Finite β] (f : α → β) (P : α → Prop) :
    ∃ (r : ℕ) (s : Fin r → α), (∀ i, P (s i)) ∧ ∀ x, P x → ∃ i, f x = f (s i) := by
  classical
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin {y : β // ∃ x, P x ∧ f x = y}
  refine ⟨r, fun i => (e.symm i).2.choose, fun i => (e.symm i).2.choose_spec.1, fun x hx => ?_⟩
  refine ⟨e ⟨f x, x, hx, rfl⟩, ?_⟩
  rw [(e.symm (e ⟨f x, x, hx, rfl⟩)).2.choose_spec.2, Equiv.symm_apply_apply]

theorem exists_hom_representatives {ν : Type} [Fintype ν] (k : ℕ) (hk : k ≠ 0)
    (P : ((ν → ℤ) →+ (ν → ℤ)) → Prop) :
    ∃ (r : ℕ) (s : Fin r → ((ν → ℤ) →+ (ν → ℤ))), (∀ i, P (s i)) ∧
      ∀ m, P m → ∃ i, ∀ x, ∃ y, m x = s i x + k • y := by
  classical
  haveI : NeZero k := ⟨hk⟩
  obtain ⟨r, s, hs, hm⟩ := exists_representatives
    (fun (m : (ν → ℤ) →+ (ν → ℤ)) (p q : ν) => ((m (Pi.single p 1) q : ℤ) : ZMod k)) P
  refine ⟨r, s, hs, fun m hP => ?_⟩
  obtain ⟨i, hi⟩ := hm m hP
  refine ⟨i, fun x => ?_⟩
  have hx : x = ∑ p, x p • (Pi.single p 1 : ν → ℤ) := by
    ext q; simp [Finset.sum_apply, Pi.single_apply]
  have key : ∀ q, ((m x q : ℤ) : ZMod k) = ((s i x q : ℤ) : ZMod k) := by
    intro q
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum, map_sum]
    simp only [map_zsmul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [congrFun (congrFun hi p) q]
  have key' : ∀ q, ∃ c : ℤ, m x q - s i x q = k * c := fun q =>
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (key q).symm
  choose y hy using key'
  refine ⟨y, funext fun q => ?_⟩
  have := hy q
  rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]
  linarith

theorem zpow_finset_sum {ν : Type} (q : ℂ) (hq : q ≠ 0) (s : Finset ν) (f : ν → ℤ) :
    q ^ (∑ i ∈ s, f i) = ∏ i ∈ s, q ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hq, ih]

theorem exp_sum_eq (k : ℕ) (ζ : ℂ) (hζ : ζ ≠ 0) (G p q : Fin 8 → Fin 8 → ℤ)
    (hpq : ∀ u v, Complex.exp (-(2 * Real.pi * Complex.I) * (p u v : ℂ) / k) = ζ ^ q u v) :
    Complex.exp (-(2 * Real.pi * Complex.I) * ((∑ u, ∑ v, G u v * p u v : ℤ) : ℂ) / k)
      = ζ ^ (∑ u, ∑ v, G u v * q u v) := by
  have h1 : ∀ n : ℤ, Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)
      = Complex.exp (-(2 * Real.pi * Complex.I) / k) ^ n := by
    intro n
    rw [← Complex.exp_int_mul]; congr 1; ring
  rw [h1, zpow_finset_sum _ (Complex.exp_ne_zero _), zpow_finset_sum _ hζ]
  refine Finset.prod_congr rfl fun u _ => ?_
  rw [zpow_finset_sum _ (Complex.exp_ne_zero _), zpow_finset_sum _ hζ]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [mul_comm (G u v), mul_comm (G u v), zpow_mul, zpow_mul, ← h1, hpq]

def omegaBil (h : ℕ) : LinearMap.BilinForm ℤ (Fin h ⊕ Fin h → ℤ) :=
  LinearMap.mk₂ ℤ (fun x y => omegaStd x y)
    (fun x x' y => by
      simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun c x y => by
      simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun x y y' => by
      simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun c x y => by
      simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)

theorem omegaBil_apply {h : ℕ} (x y : Fin h ⊕ Fin h → ℤ) : omegaBil h x y = omegaStd x y := rfl

theorem exists_tensor_form (h : ℕ) (G : Matrix (Fin 8) (Fin 8) ℤ) :
    ∃ EF : LinearMap.BilinForm ℤ (Fin 8 → (Fin h ⊕ Fin h → ℤ)),
      ∀ x y, EF x y = ∑ u, ∑ v, G u v * omegaStd (x u) (y v) := by
  refine ⟨∑ u, ∑ v, G u v • (omegaBil h).compl₁₂ (LinearMap.proj u) (LinearMap.proj v), fun x y => ?_⟩
  simp [LinearMap.sum_apply, omegaBil_apply]

theorem tensor_form_adjoint {h : ℕ} (G A A' : Matrix (Fin 8) (Fin 8) ℤ)
    (hA : A.transpose * G = G * A') (x y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) :
    ∑ u, ∑ v, G u v * omegaStd (∑ s, A u s • x s) (y v)
      = ∑ u, ∑ v, G u v * omegaStd (x u) (∑ s, A' v s • y s) := by
  have h1 : ∑ u, ∑ v, G u v * omegaStd (∑ s, A u s • x s) (y v)
      = ∑ s, ∑ v, (A.transpose * G) s v * omegaStd (x s) (y v) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← omegaBil_apply, map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply,
      smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun u _ => by ring
  have h2 : ∑ u, ∑ v, G u v * omegaStd (x u) (∑ s, A' v s • y s)
      = ∑ u, ∑ s, (G * A') u s * omegaStd (x u) (y s) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← omegaBil_apply, map_sum, map_zsmul,
      smul_eq_mul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun v _ => by ring
  rw [h1, h2, hA]

theorem nonempty_index_equiv {h g : ℕ}
    (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) :
    Nonempty (Fin 8 × Fin h ≃ Fin g) := by
  have := bas.finrank_eq
  rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype] at this
  simp at this
  refine ⟨Fintype.equivOfCardEq ?_⟩
  simp; omega

theorem action_on_basis {h g : ℕ}
    (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (A : Matrix (Fin 8) (Fin 8) ℤ)
    (m : (Fin h ⊕ Fin h → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (i : Fin (2 * g)) :
    (fun u => ∑ v, A u v • m (bas (Pi.single i 1) v))
      = ∑ i', bas.symm (fun u => ∑ v, A u v • bas (Pi.single i 1) v) i' •
          (fun u => m (bas (Pi.single i' 1) u)) := by
  set z := bas.symm (fun u => ∑ v, A u v • bas (Pi.single i 1) v) with hz
  have hx : z = ∑ p, z p • (Pi.single p 1 : Fin (2 * g) → ℤ) := by
    ext q; simp [Finset.sum_apply, Pi.single_apply]
  have h1 : (fun u => ∑ v, A u v • bas (Pi.single i 1) v) = ∑ p, z p • bas (Pi.single p 1) := by
    have : bas z = (fun u => ∑ v, A u v • bas (Pi.single i 1) v) := by
      rw [hz, LinearEquiv.apply_symm_apply]
    rw [← this]
    conv_lhs => rw [hx]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul]
  funext u
  have h2 := congrArg m (congrFun h1 u)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_zsmul] at h2 ⊢
  exact h2

theorem goodClass_sharpClass : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) [Finite J] (a : J → Matrix (Fin 8) (Fin 8) ℤ) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ u v, ∃ j, a j = Matrix.single u v 1) → ∃ (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ), ∀ n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ), GoodClass em (SharpClass (b := b) W a bas em) Mat κ w w' (h * (h + 1) / 2) := by
  intro L₁ L₂ hgen hunif h g W J _ a w w' bas hE hbas hw hw' _
  classical
  obtain ⟨σ⟩ := nonempty_index_equiv bas
  obtain ⟨EF, hEF⟩ := exists_tensor_form h (W + W.transpose)
  have hGs : (W + W.transpose).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  obtain ⟨hbij, hdom, hinj, hκ⟩ :=
    GlobalTheory.TensorSiegel.tensor_siegel_lattices h g (W + W.transpose) σ EF hGs hE.1 hE.2 hEF
  choose κ₀ hκ₀ using hκ
  obtain ⟨κ, hκ⟩ : ∃ κ : ℕ, ∀ j, κ₀ (a j) ≤ κ :=
    (Set.finite_range fun j => κ₀ (a j)).bddAbove.imp fun κ hκ j => hκ ⟨j, rfl⟩
  obtain ⟨B, τ, hBo, hBc, hτd, hτ, hτs⟩ := GlobalTheory.exists_siegel_coordinates h
  have hQ : ∀ bb, ∃ (Q : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ))
      (Hm : Matrix (Fin g) (Fin g) ℂ), bb ∈ B →
      (∀ x u i, Q x (σ (u, i)) = (τ bb).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) ∧
      (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧
        (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
        ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) := by
    intro bb
    by_cases hb : bb ∈ B
    · obtain ⟨Q, Hm, hh⟩ := hdom (τ bb) (hτ bb hb)
      exact ⟨Q, Hm, fun _ => hh⟩
    · exact ⟨0, 0, fun hb' => absurd hb' hb⟩
  choose Q Hm hQ using hQ
  have hsum : a w + a w' = 1 := by
    have hu : IsUnit (W + W.transpose) := by
      rw [Matrix.isUnit_iff_isUnit_det, hE.2]; exact isUnit_one
    apply hu.mul_left_cancel
    rw [_root_.mul_add, hw, hw', _root_.mul_one]
  have hadj : (a w).transpose * (W + W.transpose) = (W + W.transpose) * a w' := by
    rw [hw']
    conv_rhs => rw [← hw]
    rw [Matrix.transpose_mul, hGs.eq]
  refine ⟨fun j => Matrix.of fun i' i =>
    bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i', κ, fun n hn hodd => ?_⟩
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.goodThetaClass_of_lattice_families L₁ L₂ hgen hunif g J (fun j => Matrix.of fun i' i =>
    bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i') κ n w w' hn hodd
  refine ⟨j₀, fun j hj N' hN o _ b em => ?_⟩
  have hk : N' ^ 2 ≠ 0 := by
    rw [hN]; exact pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)
  have hζ : em (b.ζ : o) ≠ 0 := (b.ζ.isUnit.map em).ne_zero
  obtain ⟨r, ms, hms, hrep⟩ := exists_hom_representatives (ν := Fin h ⊕ Fin h) (N' ^ 2) hk
    (fun m => ∀ x y, Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd (m x) (m y) : ℂ)
      / ((N' ^ 2 : ℕ) : ℂ)) = em (b.ζ : o) ^ omegaStd x y)
  refine hj₀ j hj N' hN o b em _ _ r (fun _ => Fin 8 → (Fin h ⊕ Fin h → ℤ)) (fun _ => EF)
    (fun p i u => ms p (bas (Pi.single i 1) u)) (fun _ j x u => ∑ v, a j u v • x v)
    (fun _ => B) (fun _ => Q) (fun _ => Hm) ?_ ?_ ?_ ?_
  · exact fun t t' ht hm => (GlobalTheory.T.sharpClass_prim_and_closed_under_tMap hgen o g _ J b em w w' h W a bas t ht).2 t' hm
  · exact fun t ht => (GlobalTheory.T.sharpClass_prim_and_closed_under_tMap hgen o g _ J b em w w' h W a bas t ht).1 hE hw hw'
  · intro p
    refine ⟨hbij, hBo, hBc.isPreconnected, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      refine differentiableOn_pi.2 fun c => ?_
      obtain ⟨⟨u, i⟩, rfl⟩ := σ.surjective c
      refine DifferentiableOn.congr
        (f := fun bb => ∑ i', τ bb i i' * (x u (.inl i') : ℂ) + (x u (.inr i) : ℂ)) ?_ ?_
      · refine Differentiable.differentiableOn ?_
        exact (Differentiable.fun_sum fun i' _ => (hτd i i').mul_const _).add_const _
      · intro bb hb
        exact (hQ bb hb).1 x u i
    · intro x
      funext u
      have h1 : ∀ v, a w u v + a w' u v = (1 : Matrix (Fin 8) (Fin 8) ℤ) u v := fun v => by
        rw [← hsum]; rfl
      show ∑ v, a w u v • x v + ∑ v, a w' u v • x v = x u
      rw [← Finset.sum_add_distrib]
      simp only [← add_smul, h1, Matrix.one_apply, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    · intro x y
      rw [hEF, hEF]
      exact tensor_form_adjoint _ _ _ hadj x y
    · intro i₁ i₂
      rw [hEF, ← hbas i₁ i₂]
      exact exp_sum_eq _ _ hζ _ _ _ fun u v => hms p _ _
    · intro j₁ i₁
      refine ⟨0, ?_⟩
      rw [smul_zero, add_zero]
      exact action_on_basis bas (a j₁) (ms p) i₁
    · intro bb hb
      exact ⟨(hQ bb hb).2, fun j₁ =>
        hκ₀ (a j₁) κ (hκ j₁) (τ bb) (Q bb) (Hm bb) (hτ bb hb) (hQ bb hb).1 (hQ bb hb).2⟩
    · intro bb hb z' hz' he
      have h1 := hinj (τ bb) (τ z') (Q bb) (Q z') (hQ bb hb).1 (hQ z' hz').1 he
      exact (hτs (τ bb) (hτ bb hb).1 (hτ bb hb).2).unique ⟨hb, rfl⟩ ⟨hz', h1.symm⟩
    · intro bb hb t hu _
      exact GlobalTheory.T.eighthPower_theta_object_of_uniformisation L₁ L₂ hgen hunif o g _ J b em w w' h W a bas σ EF hE hbas hw hw' hEF t
        (τ bb) (ms p) (Q bb) (Hm bb) (hτ bb hb) (hms p) (hQ bb hb).1 (hQ bb hb).2 hu
  · intro t ht
    obtain ⟨τ₀, m, Q₀, H₀, hτ₀, hm, hQ₀, hpol, hu⟩ :=
      GlobalTheory.T.exists_periods_eighthPower_evenUnimodularBundle L₁ L₂ hgen hunif o g _ J b em w w' h W a bas σ EF hE hbas hw hw' hEF t ht
    obtain ⟨bb, ⟨hb, rfl⟩, -⟩ := hτs τ₀ hτ₀.1 hτ₀.2
    obtain ⟨p, hp⟩ := hrep m hm
    choose y hy using hp
    refine ⟨p, bb, hb, ?_⟩
    refine GlobalTheory.UnifTransport.transport_uniformisation o g _ J b em w w' t _ EF
      (fun i u => m (bas (Pi.single i 1) u)) (fun j x u => ∑ v, a j u v • x v) Q₀ H₀ _ EF
      (fun i u => ms p (bas (Pi.single i 1) u)) (fun j x u => ∑ v, a j u v • x v) (Q bb) (Hm bb)
      (AddEquiv.refl _) (LinearEquiv.refl _ _) hpol (hQ bb hb).2 ?_ (fun _ _ => rfl)
      (fun _ _ => rfl) ?_ hu
    · intro x
      funext c
      obtain ⟨⟨u, i⟩, rfl⟩ := σ.surjective c
      exact ((hQ bb hb).1 x u i).trans (hQ₀ x u i).symm
    · intro i
      exact ⟨fun u => y (bas (Pi.single i 1) u), funext fun u => hy _⟩

end GlobalTheory.SharpGood
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGoodThetaComplexClassE8SharpStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGoodThetaComplexClass_E8Sharp : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) [Finite J] (a : J → Matrix (Fin 8) (Fin 8) ℤ) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ u v, ∃ j, a j = Matrix.single u v 1) → ∃ (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ), ∀ n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ), GoodClass em (SharpClass (b := b) W a bas em) Mat κ w w' (h * (h + 1) / 2) := by
  first | exact @GlobalTheory.SharpGood.goodClass_sharpClass | exact GlobalTheory.SharpGood.goodClass_sharpClass | (intros; apply GlobalTheory.SharpGood.goodClass_sharpClass <;> assumption)
end

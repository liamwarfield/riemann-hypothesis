module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.GeoLeaves
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.ThetaTowerHermitianSecondHolds

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedPlaneFirstVariable
section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.DarbouxModelRationalLattice
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem PositivityTheory.Mix.darboux_model_rational_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∃ (e : Fn F n d →ₗ[ℂ] Fn F n d) (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
        (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ),
        Function.Surjective ei ∧ (∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n × Fin d)) ∧
        (∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ u Φ) = co.rho B.ψ u (e Φ)) ∧
        (∀ v, (SB _).map (ev v) = SB _) ∧
        (∀ v, (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W).IsVac B.ψ v (ev v (M.vac v))) ∧
        (∀ᶠ v in cofinite, ev v (M.vac v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v) :=
  PositivityTheory.Mix.darboux_model_rational_lattice_of PositivityTheory.Mix.adelic_estimates_holds
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPairOfPair
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixXUnip

theorem twist_heis_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (g : UA σ X.J) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), mat g *ᵥ incV F H.x = a • incV F H.x →
      (∀ z : Fin n₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ∃ b : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat g *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + b • incV F H.x) →
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ)) =
        M₁.co.rho B.ψ z (e (om (g, 1) Φ))) ∧
      ∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) (M.co.rho B.ψ u Φ)) = e (om (g, 1) Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he g a hx hι
  have hs := IsUWeilPair.isUSplitting hP.weil
  have hstd : IsStd B.ψ := hP.base.std
  have hc : ∀ t : E, cA σ (inclR (F := F) (AF F) t) = inclR (F := F) (AF F) (σ t) := fun t => rfl
  have h1 : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := by simp [incM]
  have hact : ∀ w, actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) w = mat g * w := by
    intro w; simp [actAB, mat]
  have hcomp : ∀ w w' Φ, symp (cA σ) (-1) (incM F X.J) (incM F W.J) w w' = 0 →
      M.co.rho B.ψ w (M.co.rho B.ψ w' Φ) = M.co.rho B.ψ (w + w') Φ := by
    intro w w' Φ h0
    simp only [Darboux.rho]
    have hlaw : ∀ (v v' : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) (φ : (Fin n × Fin d → AF F) → ℂ),
        schr B.ψ v (schr B.ψ v' φ) = B.ψ (⅟(2 : AF F) * (v.1 ⬝ᵥ v'.2 - v'.1 ⬝ᵥ v.2)) • schr B.ψ (v + v') φ := by
      intro v v' φ
      funext x
      simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add, Prod.snd_add,
        add_assoc, add_dotProduct, dotProduct_add]
      congr 2
      linear_combination (-(v.1 ⬝ᵥ v'.2)) * invOf_mul_self (2 : AF F)
    rw [hlaw, ← M.co.form, h0, mul_zero, AddChar.map_zero_eq_one, one_smul, ← map_add (f := _)]
  have hcol : ∀ m, ∑ i, ∑ k, H.ι i m * (X.J i k * σ (H.x k)) = 0 := by
    intro m
    have h := (hH.orth (Pi.single m 1)).1
    simp only [form, Matrix.mulVec_single_one, dotProduct, Matrix.mulVec] at h
    simpa [Finset.mul_sum, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_mul] using h
  have hperp : ∀ (z : Matrix (Fin n₁) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (q : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) q) = 0 := by
    intro z q
    have hinner : ∀ j, ∑ i, ∑ k, (incM F H.ι * z) i j * incM F X.J i k * cA σ (incV F H.x k) = 0 := by
      intro j
      have e1 : ∀ i k, (incM F H.ι * z) i j * incM F X.J i k * cA σ (incV F H.x k) =
          ∑ m, z m j * inclR (F := F) (AF F) (H.ι i m * (X.J i k * σ (H.x k))) := by
        intro i k
        rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [incM, incV, Matrix.map_apply, hc, map_mul]
        ring
      simp_rw [e1]
      calc _ = ∑ i, ∑ m, ∑ k, z m j * inclR (F := F) (AF F) (H.ι i m * (X.J i k * σ (H.x k))) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ m, ∑ i, ∑ k, z m j * inclR (F := F) (AF F) (H.ι i m * (X.J i k * σ (H.x k))) := Finset.sum_comm
        _ = ∑ m, z m j * inclR (F := F) (AF F) (∑ i, ∑ k, H.ι i m * (X.J i k * σ (H.x k))) := by
            set_option synthInstance.maxHeartbeats 100000 in
              simp [map_sum, Finset.mul_sum]
        _ = 0 := Finset.sum_eq_zero fun m _ => by rw [hcol m, map_zero, mul_zero]
    have hT : hTens (cA σ) (incM F X.J) (incM F W.J) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) q) = 0 := by
      unfold hTens
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      have e2 : ∀ i k, ∑ l, (incM F H.ι * z) i j * incM F X.J i k * incM F W.J j l *
          cA σ (Matrix.vecMulVec (incV F H.x) q k l) =
          ((incM F H.ι * z) i j * incM F X.J i k * cA σ (incV F H.x k)) * ∑ l, incM F W.J j l * cA σ (q l) := by
        intro i k
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Matrix.vecMulVec_apply, map_mul]
        ring
      simp_rw [e2, ← Finset.sum_mul, hinner j, zero_mul]
    simp [symp, hT]
  choose β hβ using fun j : Fin n₁ => hι (Pi.single j 1)
  have hgι : mat g * incM F H.ι = incM F H.ι + Matrix.vecMulVec (incV F H.x) β := by
    ext i j
    have h := congrFun (hβ j) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    simpa [Matrix.vecMulVec_apply, mul_comm] using h
  refine ⟨fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_⟩
  · have hΨ := hs.pres (g, 1) Φ hΦ
    rw [hs.impl (g, 1) _ Φ hΦ, hact]
    have hw : mat g * (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) =
        incM F H.ι * z + Matrix.vecMulVec (incV F H.x) (β ᵥ* z) := by
      rw [h1, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, hgι, Matrix.add_mul]
      congr 1
      ext i j
      simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
    have hh := he.Heisenberg₂ z _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd (Matrix.vecMulVec (incV F H.x) (β ᵥ* z)) _ hΨ)
    rw [h1, Matrix.transpose_one, Matrix.mul_one] at hh
    rw [hw, ← hcomp _ _ _ (hperp z _), hh, he.inv _ ⟨_, rfl⟩ _ hΨ]
  · obtain ⟨q, rfl⟩ := hu
    have hΨ := hs.pres (g, 1) Φ hΦ
    rw [hs.impl (g, 1) _ Φ hΦ, hact, Matrix.mul_vecMulVec, hx]
    refine he.inv _ ⟨a • q, ?_⟩ _ hΨ
    ext i j
    simp [Matrix.vecMulVec_apply]
    ring

end GlobalTheory.MixXUnip
end
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.UnitaryFixingIsotropicComplement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open PositivityTheory.Mix

theorem PositivityTheory.Mix.unitary_fixing_isotropic_complement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X : Spc F E n)
    (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ r s r₁ s₁ : ℕ), B.IsGood σ → H.IsAdapted σ B X X₁ j₀ j₁ → X.IsHerm σ B r s → X₁.IsHerm σ B r₁ s₁ →
      ∀ u : UA σ X.J, mat u *ᵥ incV F H.x = incV F H.x →
      (∀ z : Fin n₁ → AE F E, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) →
      ∀ (m m' : UA σ X.J) (t : ℕ),
      mat m *ᵥ incV F H.x = (2 : AE F E) • incV F H.x → (2 : AE F E) • (mat m *ᵥ incV F H.y) = incV F H.y →
      (∀ z : Fin n₁ → AE F E, mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z) →
      mat m' *ᵥ incV F H.x = (t : AE F E) • incV F H.x → (t : AE F E) • (mat m' *ᵥ incV F H.y) = incV F H.y →
      (∀ z : Fin n₁ → AE F E, mat m' *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z) →
      m' * (u⁻¹ * u⁻¹ * (m * u * m⁻¹)) * m'⁻¹ = (u⁻¹ * u⁻¹ * (m * u * m⁻¹)) ^ (t ^ 2) := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ H j₀ j₁ r s r₁ s₁ hB hH hX hX₁ u hux huι m m' t hmx hmy hmι hm'x hm'y hm'ι
  obtain ⟨ε, hP⟩ := planeOK_herm hB hH hX
  obtain ⟨cc, ee, ce, herm, xx, yy, xy, ix, iy, span, nd⟩ := hP
  set vx := incV F H.x with hvx
  set vy := incV F H.y with hvy
  set ιM := incM F H.ι with hιM
  set c := (cA σ).toRingHom with hc
  set J := incM F X.J with hJ
  have hact : ∀ (g h : UA σ X.J) (v : Fin n → AE F E), mat (g * h) *ᵥ v = mat g *ᵥ (mat h *ᵥ v) := by
    intro g h v
    rw [Matrix.mulVec_mulVec]
    rfl
  have hinv : ∀ (g : UA σ X.J) (v : Fin n → AE F E), mat g⁻¹ *ᵥ (mat g *ᵥ v) = v := by
    intro g v
    rw [← hact, inv_mul_cancel]
    exact Matrix.one_mulVec v
  have hinv' : ∀ (g : UA σ X.J) (v w : Fin n → AE F E), mat g *ᵥ w = v → mat g⁻¹ *ᵥ v = w := by
    intro g v w h
    rw [← h, hinv]
  have h2 : IsUnit (2 : AE F E) := by
    have := (IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F (AE F E))
    rwa [map_ofNat] at this
  choose a ha using huι
  obtain ⟨s₀, r₀, z₀, huy⟩ := span (mat u *ᵥ vy)
  have hpres : ∀ v w, bf c J (mat u *ᵥ v) (mat u *ᵥ w) = bf c J v w := by
    intro v w
    have hU : (mat u)ᵀ * J * (mat u).map c = J := u.2
    have e1 : (fun i => c ((mat u *ᵥ w) i)) = (mat u).map c *ᵥ (fun i => c (w i)) := by
      funext i
      exact RingHom.map_mulVec c (mat u) w i
    unfold PositivityTheory.Mix.bf
    rw [e1, ← Matrix.vecMul_transpose (mat u) v, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hU]
  have hsym : ∀ v w, c (bf c J v w) = ε * bf c J w v := by
    intro v w
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [PositivityTheory.Mix.bf, dotProduct, Matrix.mulVec, map_sum, map_mul, cc, herm, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hyx : bf c J vy vx = ε := by
    have h := hsym vx vy
    rw [xy, map_one] at h
    calc bf c J vy vx = ε * (ε * bf c J vy vx) := by rw [← mul_assoc, ee, one_mul]
      _ = ε := by rw [← h, mul_one]
  have hlin : ∀ (p q : AE F E) (v₁ v₂ v₃ w : Fin n → AE F E),
      bf c J (p • v₁ + v₂ + q • v₃) w = p * bf c J v₁ w + bf c J v₂ w + q * bf c J v₃ w := by
    intro p q v₁ v₂ v₃ w
    simp only [PositivityTheory.Mix.bf, add_dotProduct, smul_dotProduct, smul_eq_mul]
  have hr : r₀ = 1 := by
    have h1 := hpres vy vx
    rw [hux, huy, hlin, xx, ix, hyx] at h1
    have h1' : r₀ * ε = ε := by simpa using h1
    calc r₀ = r₀ * ε * ε := by rw [mul_assoc, ee, mul_one]
      _ = 1 := by rw [h1', ee]
  have hUix : mat u⁻¹ *ᵥ vx = vx := hinv' u vx vx hux
  have hUiι : ∀ z, mat u⁻¹ *ᵥ (ιM *ᵥ z) = ιM *ᵥ z - a z • vx := by
    intro z
    apply hinv'
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, ha, hux]
    abel
  have hUiy : mat u⁻¹ *ᵥ vy = vy - s₀ • vx - ιM *ᵥ z₀ + a z₀ • vx := by
    apply hinv'
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, huy, hr, ha, hux, one_smul]
    abel
  set Am := mat (u⁻¹ * u⁻¹ * (m * u * m⁻¹)) with hAm
  have hAact : ∀ v, Am *ᵥ v = mat u⁻¹ *ᵥ (mat u⁻¹ *ᵥ (mat m *ᵥ (mat u *ᵥ (mat m⁻¹ *ᵥ v)))) := by
    intro v
    rw [hAm]
    simp only [hact]
  have hAx : Am *ᵥ vx = vx := by
    have h : Am *ᵥ (mat m *ᵥ vx) = mat m *ᵥ vx := by
      rw [hAact, hinv m, hux, hmx, Matrix.mulVec_smul, Matrix.mulVec_smul, hUix, hUix]
    rw [hmx, Matrix.mulVec_smul] at h
    exact h2.smul_left_cancel.1 h
  have hAι : ∀ z, Am *ᵥ (ιM *ᵥ z) = ιM *ᵥ z := by
    intro z
    have h : Am *ᵥ (mat m *ᵥ (ιM *ᵥ z)) = ιM *ᵥ z := by
      rw [hAact, hinv m, ha, Matrix.mulVec_add, hmι, Matrix.mulVec_smul, hmx]
      simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hUiι, hUix]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rwa [hmι] at h
  set c₀ := 2 * s₀ - a z₀ with hc₀
  have hAy : Am *ᵥ vy = vy + c₀ • vx := by
    have e : Am *ᵥ vy = (2 : AE F E) • (mat u⁻¹ *ᵥ (mat u⁻¹ *ᵥ (mat m *ᵥ (mat u *ᵥ vy)))) := by
      conv_lhs => rw [← hmy, Matrix.mulVec_smul, hAact, hinv m]
    have e2 : (2 : AE F E) • (mat m *ᵥ (mat u *ᵥ vy)) = (2 * s₀ * 2) • vx + (2 : AE F E) • (ιM *ᵥ z₀) + vy := by
      simp only [huy, hr, Matrix.mulVec_add, Matrix.mulVec_smul, hmx, hmι, one_smul, smul_add, hmy]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, e2]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hUiι, hUix, hUiy]
    rw [hc₀]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  by_cases ht0 : t = 0
  · subst ht0
    have hy0 : vy = 0 := by simpa using hm'y.symm
    have h01 : (0 : AE F E) = 1 := by
      rw [← xy, hy0]
      unfold PositivityTheory.Mix.bf
      simp only [Pi.zero_apply, map_zero]
      rw [show (fun _ : Fin n => (0 : AE F E)) = 0 from rfl, Matrix.mulVec_zero, dotProduct_zero]
    haveI : Subsingleton (AE F E) := subsingleton_of_zero_eq_one h01
    apply matH_inj (σ := σ) X.J
    ext i j
    exact Subsingleton.elim _ _
  have ht : IsUnit (t : AE F E) := by
    have := (IsUnit.mk0 (t : F) (Nat.cast_ne_zero.2 ht0)).map (algebraMap F (AE F E))
    rwa [map_natCast] at this
  have hpow : ∀ k : ℕ, Am ^ k *ᵥ vx = vx ∧ (∀ w, Am ^ k *ᵥ (ιM *ᵥ w) = ιM *ᵥ w) ∧
      Am ^ k *ᵥ vy = vy + ((k : AE F E) * c₀) • vx := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨h1, h2', h3⟩ := ih
      refine ⟨?_, fun w => ?_, ?_⟩
      · rw [pow_succ, ← Matrix.mulVec_mulVec, hAx, h1]
      · rw [pow_succ, ← Matrix.mulVec_mulVec, hAι, h2']
      · rw [pow_succ, ← Matrix.mulVec_mulVec, hAy, Matrix.mulVec_add, Matrix.mulVec_smul, h3, h1]
        push_cast
        funext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
  have hext : ∀ P Q : Matrix (Fin n) (Fin n) (AE F E), (∀ v, P *ᵥ v = Q *ᵥ v) → P = Q := by
    intro P Q h
    ext i j
    simpa using congrFun (h (Pi.single j 1)) i
  have key : mat m' * Am = Am ^ (t ^ 2) * mat m' := by
    apply hext
    intro v
    obtain ⟨p, q, w, hv⟩ := span v
    have ex : (mat m' * Am) *ᵥ vx = (Am ^ (t ^ 2) * mat m') *ᵥ vx := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAx, hm'x, Matrix.mulVec_smul, (hpow _).1]
    have eι : (mat m' * Am) *ᵥ (ιM *ᵥ w) = (Am ^ (t ^ 2) * mat m') *ᵥ (ιM *ᵥ w) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAι, hm'ι, (hpow _).2.1]
    have ey : (mat m' * Am) *ᵥ vy = (Am ^ (t ^ 2) * mat m') *ᵥ vy := by
      have hL : (t : AE F E) • ((mat m' * Am) *ᵥ vy) = vy + ((t : AE F E) * t * c₀) • vx := by
        rw [← Matrix.mulVec_mulVec, hAy, Matrix.mulVec_add, Matrix.mulVec_smul, hm'x, smul_add, hm'y]
        funext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have hR : (t : AE F E) • ((Am ^ (t ^ 2) * mat m') *ᵥ vy) = vy + ((t : AE F E) * t * c₀) • vx := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, hm'y, (hpow _).2.2]
        congr 2
        push_cast
        ring
      exact ht.smul_left_cancel.1 (hL.trans hR.symm)
    rw [hv]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, ex, eι, ey]
  rw [mul_inv_eq_iff_eq_mul]
  apply matH_inj (σ := σ) X.J
  calc matH σ X.J (m' * (u⁻¹ * u⁻¹ * (m * u * m⁻¹))) = mat m' * Am := map_mul _ _ _
    _ = Am ^ (t ^ 2) * mat m' := key
    _ = matH σ X.J ((u⁻¹ * u⁻¹ * (m * u * m⁻¹)) ^ (t ^ 2) * m') := by
      rw [map_mul, map_pow]
      rfl
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.ExistsUnitaryScalingIsotropic
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open PositivityTheory.Mix

theorem PositivityTheory.Mix.exists_unitary_scaling_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X : Spc F E n)
    (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ r s r₁ s₁ : ℕ), B.IsGood σ → H.IsAdapted σ B X X₁ j₀ j₁ → X.IsHerm σ B r s → X₁.IsHerm σ B r₁ s₁ →
      ∀ t : ℕ, t ≠ 0 → ∃ m : UA σ X.J, mat m *ᵥ incV F H.x = (t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • incV F H.x ∧
        (t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • (mat m *ᵥ incV F H.y) = incV F H.y ∧ ∀ z : Fin n₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ H j₀ j₁ r s r₁ s₁ hB hH hX _ t ht
  obtain ⟨ε, h⟩ := planeOK_herm hB hH hX
  exact exists_scale h t ht
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedPlanePairRestriction
section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.DarbouxCoordinatesGoodModel
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem _root_.PositivityTheory.Mix.T.darboux_coordinates_good_model : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∃ (e : Fn F n d →ₗ[ℂ] Fn F n d) (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
        (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ),
        Function.Surjective ei ∧ (∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n × Fin d)) ∧
        (∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ u Φ) = co.rho B.ψ u (e Φ)) ∧
        (∀ v, (SB _).map (ev v) = SB _) ∧
        (∀ v, (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W).IsVac B.ψ v (ev v (M.vac v))) ∧
        (∀ᶠ v in cofinite, ev v (M.vac v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v) := by
  first | exact @PositivityTheory.Mix.darboux_model_rational_lattice | exact fun _ => @PositivityTheory.Mix.darboux_model_rational_lattice | exact PositivityTheory.Mix.darboux_model_rational_lattice | exact @PositivityTheory.Mix.darboux_model_rational_lattice trivial
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.ExistsAdaptedBasisHermitian
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem _root_.PositivityTheory.Mix.T.exists_adapted_basis_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (r₁ s₁ : ℕ), X₁.IsHerm σ B r₁ s₁ →
      H.IsAdapted σ B X X₁ j₀ j₁ → M₁.IsGood B.ψ →
      ∃ (j : Fin n₁ × Fin d → Fin n × Fin d) (co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin n × Fin d)),
        Function.Injective j ∧
        (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
          co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
        (∀ z, co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) H.ι * z) = (Function.extend j (M₁.co.e z).1 0, Function.extend j (M₁.co.e z).2 0)) ∧
        (∀ z, (co.e (Matrix.vecMulVec (incV F H.x) z)).1 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F H.x) z)).2 (j k) = 0) ∧
        (∀ z, (co.e (Matrix.vecMulVec (incV F H.y) z)).2 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F H.y) z)).1 (j k) = 0) := by
  first | exact @PositivityTheory.Mix.exists_adapted_index_hermitian | exact fun _ => @PositivityTheory.Mix.exists_adapted_index_hermitian | exact PositivityTheory.Mix.exists_adapted_index_hermitian | exact @PositivityTheory.Mix.exists_adapted_index_hermitian trivial
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedBasisHermitianUnique
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem _root_.PositivityTheory.Mix.T.adapted_basis_hermitian_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (r₁ s₁ : ℕ), X₁.IsHerm σ B r₁ s₁ →
      H.IsAdapted σ B X X₁ j₀ j₁ → M₁.IsGood B.ψ →
      ∀ (j : Fin n₁ × Fin d → Fin n × Fin d) (co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin n × Fin d)),
        Function.Injective j →
        (∀ z, co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) H.ι * z) = (Function.extend j (M₁.co.e z).1 0, Function.extend j (M₁.co.e z).2 0)) →
        (∀ z, (co.e (Matrix.vecMulVec (incV F H.x) z)).1 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F H.x) z)).2 (j k) = 0) →
        (∀ z, (co.e (Matrix.vecMulVec (incV F H.y) z)).2 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F H.y) z)).1 (j k) = 0) →
        ∀ (v : Pl (F := F)) (φ : (Fin n × Fin d → Fv F v) → ℂ), (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W).IsVac B.ψ v φ →
          ∃ c : ℂ, c ≠ 0 ∧ (fun y => φ (Function.extend j y 0)) = c • M₁.vac v := by
  first | exact @PositivityTheory.Mix.adapted_index_vector_compatibility | exact fun _ => @PositivityTheory.Mix.adapted_index_vector_compatibility | exact PositivityTheory.Mix.adapted_index_vector_compatibility | exact @PositivityTheory.Mix.adapted_index_vector_compatibility trivial
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.ExistsRestrictionExtendByZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem _root_.PositivityTheory.Mix.T.exists_restriction_extend_by_zero : ∀ (F : Type) [Field F] [NumberField F] {κ₁ κ : Type} [Fintype κ₁] [Fintype κ] (j : κ₁ → κ), Function.Injective j →
    ∃ R : SInf F κ →L[ℂ] SInf F κ₁, ∀ f y, R f y = f (Function.extend j y 0) := by
  first | exact @GlobalTheory.RestrS.exists_restr | exact fun _ => @GlobalTheory.RestrS.exists_restr | exact GlobalTheory.RestrS.exists_restr | exact @GlobalTheory.RestrS.exists_restr trivial
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.ExtendByZeroSchwartzBruhatMap
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem _root_.PositivityTheory.Mix.T.extend_by_zero_schwartzBruhat_map : ∀ (F : Type) [Field F] [NumberField F] {κ₁ κ : Type} [Fintype κ₁] [Fintype κ] (j : κ₁ → κ), Function.Injective j →
    ∀ v : Pl (F := F), (SB (κ → Fv F v)).map (LinearMap.funLeft ℂ ℂ (fun y : κ₁ → Fv F v => Function.extend j y 0)) = SB (κ₁ → Fv F v) := by
  first | exact @GlobalTheory.SchwartzBruhatRestrict.map_funLeft_extendZero | exact fun _ => @GlobalTheory.SchwartzBruhatRestrict.map_funLeft_extendZero | exact GlobalTheory.SchwartzBruhatRestrict.map_funLeft_extendZero | exact @GlobalTheory.SchwartzBruhatRestrict.map_funLeft_extendZero trivial
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.ExtendByZeroMemSchA
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem _root_.PositivityTheory.Mix.T.extend_by_zero_mem_schA : ∀ (F : Type) [Field F] [NumberField F] {κ₁ κ : Type} [Fintype κ₁] [Fintype κ] (j : κ₁ → κ), Function.Injective j →
    ∀ Φ ∈ schA F κ, (fun y => Φ (Function.extend j y 0)) ∈ schA F κ₁ := by
  first | exact @GlobalTheory.RestrSchA.mem_schA_comp_extend | exact fun _ => @GlobalTheory.RestrSchA.mem_schA_comp_extend | exact GlobalTheory.RestrSchA.mem_schA_comp_extend | exact @GlobalTheory.RestrSchA.mem_schA_comp_extend trivial
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedPlanePairRestriction
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKMixXEx

theorem extend_map_m {α β M N : Type} {j : α → β} (hj : Function.Injective j) [Zero M] [Zero N] (g : M → N) (hg : g 0 = 0)
    (y : α → M) : (fun k => g (Function.extend j y 0 k)) = Function.extend j (fun i => g (y i)) 0 := by
  funext k
  by_cases h : ∃ a, j a = k
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h, hg]

theorem extend_zero'_m {α β M : Type} {j : α → β} (hj : Function.Injective j) [Zero M] :
    Function.extend j (0 : α → M) 0 = 0 := by
  funext k
  by_cases h : ∃ a, j a = k
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

theorem extend_add_m {α β M : Type} {j : α → β} (hj : Function.Injective j) [AddZeroClass M] (a b : α → M) :
    Function.extend j (a + b) 0 = Function.extend j a 0 + Function.extend j b 0 := by
  funext k
  by_cases h : ∃ x, j x = k
  · obtain ⟨x, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

theorem sum_extend_m {α β R : Type} [Fintype α] [Fintype β] {j : α → β} (hj : Function.Injective j) [AddCommMonoid R]
    (f : α → R) : ∑ k, Function.extend j f 0 k = ∑ i, f i := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨j, hj⟩)) (fun k _ hk => by
      rw [Function.extend_apply' (f := j) f (0 : β → R) k (fun ⟨a, ha⟩ => hk (Finset.mem_map.2 ⟨a, Finset.mem_univ _, ha⟩))]; rfl),
    Finset.sum_map]
  exact Finset.sum_congr rfl fun i _ => hj.extend_apply _ _ _

theorem extend_dot_m {α β R : Type} [Fintype α] [Fintype β] {j : α → β} (hj : Function.Injective j) [CommRing R]
    (a b : α → R) : Function.extend j a 0 ⬝ᵥ Function.extend j b 0 = a ⬝ᵥ b := by
  have : (fun k => Function.extend j a 0 k * Function.extend j b 0 k) = Function.extend j (fun i => a i * b i) 0 := by
    funext k
    by_cases h : ∃ x, j x = k
    · obtain ⟨x, rfl⟩ := h
      simp [hj.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]
  simp only [dotProduct]
  rw [show (∑ k, Function.extend j a 0 k * Function.extend j b 0 k) = ∑ k, Function.extend j (fun i => a i * b i) 0 k from
    Finset.sum_congr rfl fun k _ => congrFun this k, sum_extend_m hj]

theorem extend_dot_zero_m {α β R : Type} [Fintype α] [Fintype β] {j : α → β} [CommRing R] (y : α → R) (q : β → R)
    (hq : ∀ k, q (j k) = 0) : Function.extend j y 0 ⬝ᵥ q = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h : ∃ x, j x = k
  · obtain ⟨x, rfl⟩ := h
    simp [hq]
  · simp [Function.extend_apply' _ _ _ h]

end GlobalTheory.ThKMixXEx

namespace GlobalTheory.ThKMixXEx

theorem std_extend_m {F : Type} [Field F] [NumberField F] {κ₁ κ : Type} {j : κ₁ → κ} (hj : Function.Injective j) (v : Pl (F := F)) :
    (fun y : κ₁ → Fv F v => Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} (1 : (κ → Fv F v) → ℂ)
      (Function.extend j y 0)) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} (1 : (κ₁ → Fv F v) → ℂ) := by
  funext y
  have key : (∀ i, Function.extend j y 0 i ∈ v.adicCompletionIntegers F) ↔ ∀ i, y i ∈ v.adicCompletionIntegers F := by
    constructor
    · intro h i
      simpa [hj.extend_apply] using h (j i)
    · intro h k
      by_cases hk : ∃ a, j a = k
      · obtain ⟨a, rfl⟩ := hk
        simpa [hj.extend_apply] using h a
      · simp [Function.extend_apply' _ _ _ hk]
  by_cases hy : ∀ i, y i ∈ v.adicCompletionIntegers F
  · rw [Set.indicator_of_mem (show y ∈ {x : κ₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hy),
      Set.indicator_of_mem (show Function.extend j y 0 ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from key.2 hy)]
    rfl
  · rw [Set.indicator_of_notMem (show y ∉ {x : κ₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hy),
      Set.indicator_of_notMem (show Function.extend j y 0 ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from
        fun h => hy (key.1 h))]

theorem exists_isEv_mixedX_m : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∃ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁
  classical
  obtain ⟨j, co, hj, hrat, hι, hx, hy⟩ :=
    PositivityTheory.Mix.T.exists_adapted_basis_hermitian F E σ B n d X W r s r' s' hP.base hP.herm hP.skew n₁ X₁ H j₀ j₁ M₁ r₁ s₁ hP₁.herm hH hP₁.good
  obtain ⟨e₁, ei₁, ev₁, hsurj, hmaps, hheis, hSB, hvac, hstd, hpure⟩ :=
    PositivityTheory.Mix.T.darboux_coordinates_good_model F E σ B n d X W M r s r' s' hP.base hP.herm hP.skew hP.good co hrat
  have hres := fun v => PositivityTheory.Mix.T.adapted_basis_hermitian_unique F E σ B n d X W r s r' s' hP.base hP.herm hP.skew n₁ X₁ H j₀ j₁ M₁ r₁ s₁ hP₁.herm hH
    hP₁.good j co hj hι hx hy v _ (hvac v)
  choose c hc0 hc using hres
  have hc1 : ∀ᶠ v in cofinite, c v = 1 := by
    filter_upwards [hstd, hP₁.good.std] with v h1 h2
    have h' := hc v
    rw [h1, h2, std_extend_m hj v] at h'
    have h := congrFun h' 0
    have hm : (0 : Fin n₁ × Fin d → Fv F v) ∈ {x : Fin n₁ × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} :=
      fun i => zero_mem _
    rw [Pi.smul_apply, Set.indicator_of_mem hm, smul_eq_mul] at h
    simpa using h.symm
  obtain ⟨R, hR⟩ := PositivityTheory.Mix.T.exists_restriction_extend_by_zero F j hj
  refine ⟨(∏ᶠ v, c v)⁻¹ • (LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → AF F => Function.extend j y 0) ∘ₗ e₁),
    ⟨?_, ?_, ?_, ?_⟩⟩
  · intro Φ hΦ
    exact Submodule.smul_mem _ _ (PositivityTheory.Mix.T.extend_by_zero_mem_schA F j hj _ (hmaps Φ hΦ))
  · intro z Φ hΦ
    have h1 : incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ = incM F H.ι * z := by
      rw [show incM F (1 : Matrix (Fin d) (Fin d) E) = 1 from Matrix.map_one _ (map_zero _) (map_one _)]
      simp
    rw [h1]
    funext y
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [hheis _ Φ hΦ]
    have hi : co.e (incM F H.ι * z) =
        (Function.extend j (M₁.co.e z).1 0, Function.extend j (M₁.co.e z).2 0) := hι z
    simp only [Darboux.rho, schr, hi, Prod.fst, Prod.snd, extend_dot_m hj, ← extend_add_m hj, Pi.smul_apply, smul_eq_mul,
      LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply]
    ring
  · intro u hu Φ hΦ
    obtain ⟨z, rfl⟩ := hu
    funext y
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [hheis _ Φ hΦ]
    obtain ⟨h1, h2⟩ := hx z
    simp only [Darboux.rho, schr, h1, extend_dot_zero_m _ _ h2, zero_dotProduct, mul_zero, add_zero,
      AddChar.map_zero_eq_one, one_mul]
  · obtain ⟨b, hb0⟩ : ∃ b : SInf F (Fin n × Fin d), b 0 ≠ 0 := by
      let bb : ContDiffBump (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
      have hs : HasCompactSupport (fun x => ((bb x : ℝ) : ℂ)) :=
        bb.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
      have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((bb x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp bb.contDiff
      refine ⟨hs.toSchwartzMap hcd, ?_⟩
      have h2 : bb 0 = 1 := bb.one_of_mem_closedBall (by simp [bb])
      simp [h2]
    obtain ⟨f₀, hf₀⟩ := hsurj b
    refine ⟨R.comp ei₁, fun v => (c v)⁻¹ •
      (LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → Fv F v => Function.extend j y 0) ∘ₗ ev₁ v), ?_, ?_, ?_⟩
    · intro h
      have := congrArg (fun T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d) => T f₀ 0) h
      simp only [ContinuousLinearMap.comp_apply, hR, hf₀, extend_zero'_m hj, ContinuousLinearMap.zero_apply,
        SchwartzMap.zero_apply] at this
      exact hb0 this
    · intro v
      refine ⟨?_, ?_⟩
      · rw [LinearMap.smul_apply, LinearMap.comp_apply]
        rw [show LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → Fv F v => Function.extend j y 0) (ev₁ v (M.vac v)) =
          c v • M₁.vac v from hc v, smul_smul, inv_mul_cancel₀ (hc0 v), one_smul]
      · rw [Submodule.map_smul _ _ _ (inv_ne_zero (hc0 v)), Submodule.map_comp, hSB v, PositivityTheory.Mix.T.extend_by_zero_schwartzBruhat_map F j hj v]
    · intro f φ hφ hφv
      funext y
      rw [LinearMap.smul_apply, LinearMap.comp_apply, hpure f φ hφ hφv]
      simp only [LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure,
        ContinuousLinearMap.comp_apply, hR, LinearMap.smul_apply, LinearMap.comp_apply]
      have hI : (fun i => evI F (Function.extend j y 0 i)) = Function.extend j (fun i => evI F (y i)) 0 :=
        extend_map_m hj (evI F) (by unfold evI; exact map_zero _) y
      have hF : ∀ v : Pl (F := F), (fun i => evFin F v (Function.extend j y 0 i)) =
          Function.extend j (fun i => evFin F v (y i)) 0 := fun v => extend_map_m hj _ (map_zero _) y
      simp only [hI, hF]
      have hfin1 : (Function.mulSupport fun v : Pl F => (c v)⁻¹).Finite := by
        refine (Filter.eventually_cofinite.1 hc1).subset fun v hv h => hv ?_
        simp [h]
      have hfin2 : (Function.mulSupport fun v : Pl F =>
          ev₁ v (φ v) (Function.extend j (fun i => evFin F v (y i)) 0)).Finite := by
        have := GlobalTheory.PureFactor.mulSupport_finite (κ := Fin n₁ × Fin d)
          (fun v x => ev₁ v (φ v) (Function.extend j x 0)) (by
            filter_upwards [hφv, hstd] with v h1 h2
            rw [h1, h2]
            exact std_extend_m hj v) y
        exact this
      rw [finprod_mul_distrib hfin1 hfin2, finprod_inv_distrib]
      ring

end GlobalTheory.ThKMixXEx
end
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedPlanePairRestrictionStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.PositivityTheory.Mix.T.adapted_plane_pair_restriction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∃ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e := by
  first | exact @GlobalTheory.ThKMixXEx.exists_isEv_mixedX_m | exact fun _ => @GlobalTheory.ThKMixXEx.exists_isEv_mixedX_m | exact GlobalTheory.ThKMixXEx.exists_isEv_mixedX_m | exact @GlobalTheory.ThKMixXEx.exists_isEv_mixedX_m trivial
end
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedPlanePairSeesawIdentity
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.PositivityTheory.Mix.T.adapted_plane_pair_seesaw_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (t : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) (g₁ : UA σ X₁.J) (m : UA σ X.J), IsLevi H t g₁ m → ∀ Φ ∈ schA F (Fin n × Fin d),
        e (om (m, 1) Φ) = ((χW t : ℂ) * (((absE F E t : ℝ) ^ ((d : ℝ) / 2) : ℝ) : ℂ)) • om₁ (g₁, 1) (e Φ) := by
  first | exact @PositivityTheory.Mix.theta_tower_hermitian_second_holds | exact @PositivityTheory.Mix.theta_tower_hermitian_second_holds | exact PositivityTheory.Mix.theta_tower_hermitian_second_holds | exact @PositivityTheory.Mix.theta_tower_hermitian_second_holds trivial
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedPlanePairLocalFactor
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.PositivityTheory.Mix.T.adapted_plane_pair_local_factor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (h : UA σ W.J), ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, h) Φ) = om₁ (1, h) (e Φ) := by
  first | exact @PositivityTheory.Mix.theta_tower_hermitian_first_holds | exact @PositivityTheory.Mix.theta_tower_hermitian_first_holds | exact PositivityTheory.Mix.theta_tower_hermitian_first_holds | exact @PositivityTheory.Mix.theta_tower_hermitian_first_holds trivial
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedPlanePairThetaIntegral
section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.HermitianAdaptedPlaneLocal
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.PositivityTheory.Mix.T.hermitian_adapted_plane_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ e' : Fn F n d →ₗ[ℂ] Fn F n₁ d,
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e' (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ) = M₁.co.rho B.ψ z (e' Φ)) →
      (∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Φ ∈ schA F (Fin n × Fin d), e' (M.co.rho B.ψ u Φ) = e' Φ) →
      (∀ y : Fin n₁ × Fin d → AF F, (LinearMap.proj y : Fn F n₁ d →ₗ[ℂ] ℂ) ∘ₗ e' ∈ (adeleClass F).adm (Fin n × Fin d)) →
      ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), e' Φ = c • e Φ := by
  first | exact @PositivityTheory.ThKF0.hermitian_plane_theta_restriction | exact @PositivityTheory.ThKF0.hermitian_plane_theta_restriction | exact PositivityTheory.ThKF0.hermitian_plane_theta_restriction | exact @PositivityTheory.ThKF0.hermitian_plane_theta_restriction trivial
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.HermitianAdaptedPairConverse
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.PositivityTheory.Mix.T.hermitian_adapted_pair_converse : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ y : Fin n₁ × Fin d → AF F, (LinearMap.proj y : Fn F n₁ d →ₗ[ℂ] ℂ) ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  first | exact @PositivityTheory.ThKF0.hermitian_plane_theta_cusp_integral | exact fun _ => @PositivityTheory.ThKF0.hermitian_plane_theta_cusp_integral | exact PositivityTheory.ThKF0.hermitian_plane_theta_cusp_integral | exact @PositivityTheory.ThKF0.hermitian_plane_theta_cusp_integral trivial
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.HermitianAdaptedPairOfPair
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.PositivityTheory.Mix.T.hermitian_adapted_pair_of_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (g : UA σ X.J) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), mat g *ᵥ incV F H.x = a • incV F H.x →
      (∀ z : Fin n₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ∃ b : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat g *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + b • incV F H.x) →
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ)) =
        M₁.co.rho B.ψ z (e (om (g, 1) Φ))) ∧
      ∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) (M.co.rho B.ψ u Φ)) = e (om (g, 1) Φ) := by
  first | exact @GlobalTheory.MixXUnip.twist_heis_inv | exact fun _ => @GlobalTheory.MixXUnip.twist_heis_inv | exact GlobalTheory.MixXUnip.twist_heis_inv | exact @GlobalTheory.MixXUnip.twist_heis_inv trivial
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.UnitaryFixingVectorPreserves
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.PositivityTheory.Mix.T.unitary_fixing_vector_preserves : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X : Spc F E n)
    (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ r s r₁ s₁ : ℕ), B.IsGood σ → H.IsAdapted σ B X X₁ j₀ j₁ → X.IsHerm σ B r s → X₁.IsHerm σ B r₁ s₁ →
      ∀ u : UA σ X.J, mat u *ᵥ incV F H.x = incV F H.x →
      (∀ z : Fin n₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) →
      ∀ (m m' : UA σ X.J) (t : ℕ),
      mat m *ᵥ incV F H.x = (2 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • incV F H.x → (2 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • (mat m *ᵥ incV F H.y) = incV F H.y →
      (∀ z : Fin n₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z) →
      mat m' *ᵥ incV F H.x = (t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • incV F H.x → (t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • (mat m' *ᵥ incV F H.y) = incV F H.y →
      (∀ z : Fin n₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat m' *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z) →
      m' * (u⁻¹ * u⁻¹ * (m * u * m⁻¹)) * m'⁻¹ = (u⁻¹ * u⁻¹ * (m * u * m⁻¹)) ^ (t ^ 2) := by
  first | exact @PositivityTheory.Mix.unitary_fixing_isotropic_complement | exact fun _ => @PositivityTheory.Mix.unitary_fixing_isotropic_complement | exact PositivityTheory.Mix.unitary_fixing_isotropic_complement | exact @PositivityTheory.Mix.unitary_fixing_isotropic_complement trivial
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.ExistsUnitaryScalingVector
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.PositivityTheory.Mix.T.exists_unitary_scaling_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X : Spc F E n)
    (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ r s r₁ s₁ : ℕ), B.IsGood σ → H.IsAdapted σ B X X₁ j₀ j₁ → X.IsHerm σ B r s → X₁.IsHerm σ B r₁ s₁ →
      ∀ t : ℕ, t ≠ 0 → ∃ m : UA σ X.J, mat m *ᵥ incV F H.x = (t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • incV F H.x ∧
        (t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • (mat m *ᵥ incV F H.y) = incV F H.y ∧ ∀ z : Fin n₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z := by
  first | exact @PositivityTheory.Mix.exists_unitary_scaling_isotropic | exact fun _ => @PositivityTheory.Mix.exists_unitary_scaling_isotropic | exact PositivityTheory.Mix.exists_unitary_scaling_isotropic | exact @PositivityTheory.Mix.exists_unitary_scaling_isotropic trivial
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedPlanePairThetaIntegral
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.MixXUnip

theorem unip_trivial_m : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ u ∈ unip σ X H, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (u, 1) Φ) = e Φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he u hu
  have hS := IsUWeilPair.isUSplitting hP.weil
  have pres : ∀ g Φ, Φ ∈ schA F (Fin n × Fin d) → om g Φ ∈ schA F (Fin n × Fin d) := fun g Φ h => hS.pres g Φ h
  have omul : ∀ g h : UA σ X.J, ∀ Φ, om (g * h, 1) Φ = om (g, 1) (om (h, 1) Φ) := fun g h Φ => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have om1 : ∀ Φ, om (1, 1) Φ = Φ := fun Φ => by
    rw [show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one, Module.End.one_apply]
  have twist : ∀ (g : UA σ X.J) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), mat g *ᵥ incV F H.x = a • incV F H.x →
      (∀ z : Fin n₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ∃ b : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat g *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + b • incV F H.x) →
      ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) Φ) = c • e Φ := by
    intro g a ha hb
    obtain ⟨h1, h2⟩ := PositivityTheory.Mix.T.hermitian_adapted_pair_of_pair F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he g a ha hb
    refine PositivityTheory.Mix.T.hermitian_adapted_plane_local F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he
      (e ∘ₗ om (g, 1)) h1 h2 fun y => ?_
    have := hS.adm (g, 1) _ (PositivityTheory.Mix.T.hermitian_adapted_pair_converse F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he y)
    rwa [LinearMap.comp_assoc] at this
  by_cases h0 : ∀ Φ ∈ schA F (Fin n × Fin d), e Φ = 0
  · intro Φ hΦ
    rw [h0 _ (pres _ _ hΦ), h0 _ hΦ]
  push_neg at h0
  obtain ⟨Φ₀, hΦ₀, hne⟩ := h0
  let Q : UA σ X.J → ℂ → Prop := fun g c => ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) Φ) = c • e Φ
  have Quniq : ∀ g c c', Q g c → Q g c' → c = c' := fun g c c' h h' =>
    smul_left_injective ℂ hne ((h Φ₀ hΦ₀).symm.trans (h' Φ₀ hΦ₀))
  have Qmul : ∀ g h c c', Q g c → Q h c' → Q (g * h) (c * c') := fun g h c c' hg hh Φ hΦ => by
    rw [omul, hg _ (pres _ _ hΦ), hh _ hΦ, smul_smul]
  have Qone : Q 1 1 := fun Φ _ => by rw [om1, one_smul]
  have Qinv : ∀ g c, Q g c → c ≠ 0 ∧ Q g⁻¹ c⁻¹ := by
    intro g c hg
    have key : ∀ Φ ∈ schA F (Fin n × Fin d), e Φ = c • e (om (g⁻¹, 1) Φ) := fun Φ hΦ => by
      rw [← hg _ (pres _ _ hΦ), ← omul, mul_inv_cancel, om1]
    have hc : c ≠ 0 := fun h => hne (by rw [key _ hΦ₀, h, zero_smul])
    exact ⟨hc, fun Φ hΦ => by rw [key Φ hΦ, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩
  have Qpow : ∀ g c, Q g c → ∀ k : ℕ, Q (g ^ k) (c ^ k) := by
    intro g c hg k
    induction k with
    | zero => simpa using Qone
    | succ k ih => rw [pow_succ, pow_succ]; exact Qmul _ _ _ _ ih hg

  have gen : ∀ g : UA σ X.J, mat g *ᵥ incV F H.x = incV F H.x →
      (∀ z : Fin n₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat g *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) → Q g 1 := by
    intro g hgx hgz
    obtain ⟨cu, hcu⟩ := twist g 1 (by rw [one_smul]; exact hgx) hgz
    have scl : ∀ t : ℕ, t ≠ 0 → ∃ m : UA σ X.J, (mat m *ᵥ incV F H.x = (t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • incV F H.x ∧
        (t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • (mat m *ᵥ incV F H.y) = incV F H.y ∧ ∀ z : Fin n₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z) ∧
        ∃ c, Q m c := by
      intro t ht
      obtain ⟨m, h1, h2, h3⟩ := PositivityTheory.Mix.T.exists_unitary_scaling_vector F E σ B n n₁ X X₁ H j₀ j₁ r s r₁ s₁ hP.base hH hP.herm hP₁.herm t ht
      exact ⟨m, ⟨h1, h2, h3⟩, twist m _ h1 fun z => ⟨0, by rw [zero_smul, add_zero, h3]⟩⟩
    obtain ⟨m, ⟨hm1, hm2, hm3⟩, cm, hcm⟩ := scl 2 two_ne_zero
    have hm1' : mat m *ᵥ incV F H.x = (2 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • incV F H.x := by exact_mod_cast hm1
    have hm2' : (2 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • (mat m *ᵥ incV F H.y) = incV F H.y := by exact_mod_cast hm2
    obtain ⟨hcm0, hcmi⟩ := Qinv _ _ hcm
    obtain ⟨hcu0, hcui⟩ := Qinv _ _ hcu
    set v := g⁻¹ * g⁻¹ * (m * g * m⁻¹) with hv
    have hQv : Q v (cu⁻¹ * cu⁻¹ * (cm * cu * cm⁻¹)) :=
      Qmul _ _ _ _ (Qmul _ _ _ _ hcui hcui) (Qmul _ _ _ _ (Qmul _ _ _ _ hcm hcu) hcmi)
    set cv := cu⁻¹ * cu⁻¹ * (cm * cu * cm⁻¹) with hcv
    have hcv' : cv = cu⁻¹ := by rw [hcv]; field_simp
    have step : ∀ t : ℕ, t ≠ 0 → cv ^ (t ^ 2) = cv := by
      intro t ht
      obtain ⟨m', ⟨h1, h2, h3⟩, cm', hcm'⟩ := scl t ht
      obtain ⟨hcm0', hcmi'⟩ := Qinv _ _ hcm'
      have e1 := Qmul _ _ _ _ (Qmul _ _ _ _ hcm' hQv) hcmi'
      rw [PositivityTheory.Mix.T.unitary_fixing_vector_preserves F E σ B n n₁ X X₁ H j₀ j₁ r s r₁ s₁ hP.base hH hP.herm hP₁.herm g hgx hgz m m' t hm1' hm2' hm3 h1 h2 h3] at e1
      have := Quniq _ _ _ (Qpow _ _ hQv (t ^ 2)) e1
      rw [this]; field_simp
    have hcv0 : cv ≠ 0 := by rw [hcv']; exact inv_ne_zero hcu0
    have s2 := step 2 two_ne_zero
    have s3 := step 3 three_ne_zero
    norm_num at s2 s3
    have c3 : cv ^ 3 = 1 := by
      have : cv * (cv ^ 3 - 1) = 0 := by linear_combination s2
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hcv0)
    have c1 : cv = 1 := by rw [← s3, show 9 = 3 * 3 from rfl, pow_mul, c3, one_pow]
    have : cu = 1 := by rw [hcv', inv_eq_one] at c1; exact c1
    rw [← this]; exact hcu

  have hcl : ∀ g ∈ unip σ X H, Q g 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg => exact gen g hg.1 hg.2
    | one => exact Qone
    | mul g h _ _ ihg ihh => simpa using Qmul _ _ _ _ ihg ihh
    | inv g _ ih => simpa using (Qinv _ _ ih).2
  intro Φ hΦ
  simpa using hcl u hu Φ hΦ

end GlobalTheory.MixXUnip
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedPlanePairThetaIntegralStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem _root_.PositivityTheory.Mix.T.adapted_plane_pair_theta_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ u ∈ unip σ X H, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (u, 1) Φ) = e Φ := by
  first | exact @GlobalTheory.MixXUnip.unip_trivial_m | exact fun _ => @GlobalTheory.MixXUnip.unip_trivial_m | exact GlobalTheory.MixXUnip.unip_trivial_m | exact @GlobalTheory.MixXUnip.unip_trivial_m trivial
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThKMixX

theorem mixed_model_plane_X_m : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      (∃ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e) ∧
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ h t g₁ m, IsLevi H t g₁ m → ∀ u ∈ unip σ X H, ∀ Φ ∈ schA F (Fin n × Fin d),
        e (om (u * m, h) Φ) = ((χW t : ℂ) * (((absE F E t : ℝ) ^ ((d : ℝ) / 2) : ℝ) : ℂ)) • om₁ (g₁, h) (e Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁
  refine ⟨PositivityTheory.Mix.T.adapted_plane_pair_restriction F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁, ?_⟩
  intro e he h t g₁ m hm u hu Φ hΦ
  have pres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) :=
    fun x Φ hΦ => hP.weil.isUSplitting.pres x Φ hΦ
  have hsplit : ((u * m, h) : UA σ X.J × UA σ W.J) = ((u, 1) * (m, 1)) * (1, h) := by simp
  rw [hsplit, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    PositivityTheory.Mix.T.adapted_plane_pair_theta_integral F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he u hu _ (pres _ _ (pres _ _ hΦ)),
    PositivityTheory.Mix.T.adapted_plane_pair_seesaw_identity F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he t g₁ m hm _ (pres _ _ hΦ),
    PositivityTheory.Mix.T.adapted_plane_pair_local_factor F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he h Φ hΦ,
    ← Module.End.mul_apply, ← map_mul]
  simp

end GlobalTheory.ThKMixX
end

theorem PositivityTheory.Mix.mixX_closed : PositivityTheory.ThKG.MixX := GlobalTheory.ThKMixX.mixed_model_plane_X_m

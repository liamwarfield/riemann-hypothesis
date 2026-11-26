module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralUnitGLEqHermitianLatticeCo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjugacyClassesEquivUnitsModNormsNonspli
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOfEqualGramTraceForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOfEqualGramTraceForms
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitLemma.IsometryUnit

theorem isometry_unit : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∀ (a : ℕ) (β β' : B.Aˣ), B.σ (β : B.A) = β * (ε * B.g) → B.σ (β' : B.A) = β' * (ε * B.g) → ∀ b b' : Module.Basis (Fin a) K.E B.A, (∀ i j, B.herm β (b i) (b j) = B.herm β' (b' i) (b' j)) → ∃ t : B.Aˣ, (β' : B.A) = β * (t * B.σ t) := by
  intro K B hs ε hε a β β' hβ hβ' b b' hgram
  have hs' : (LinearMap.mulLeft K.E B.g).charpoly.Separable := hs
  have σsm : ∀ (r : K.E) (y : B.A), B.σ (r • y) = K.c r • B.σ y := by
    intro r y; rw [Algebra.smul_def, map_mul, B.σ_alg, Algebra.smul_def]
  have trσ := GlobalTheory.UnitLemma.PairClass.trace_σ K B
  have addL : ∀ (x u u' v : B.A), B.herm x (u + u') v = B.herm x u v + B.herm x u' v := by
    intro x u u' v; unfold InvAlg.herm; rw [mul_add, add_mul, map_add (f := _)]
  have subL : ∀ (x u u' v : B.A), B.herm x (u - u') v = B.herm x u v - B.herm x u' v := by
    intro x u u' v; unfold InvAlg.herm; rw [mul_sub, sub_mul, map_sub]
  have smulL : ∀ (x : B.A) (r : K.E) (u v : B.A), B.herm x (r • u) v = r * B.herm x u v := by
    intro x r u v; unfold InvAlg.herm; rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]
  have addR : ∀ (x u v v' : B.A), B.herm x u (v + v') = B.herm x u v + B.herm x u v' := by
    intro x u v v'; unfold InvAlg.herm; rw [map_add (f := _), mul_add, map_add (f := _)]
  have smulR : ∀ (x : B.A) (r : K.E) (u v : B.A), B.herm x u (r • v) = K.c r * B.herm x u v := by
    intro x r u v; unfold InvAlg.herm; rw [σsm, mul_smul_comm, map_smul, smul_eq_mul]

  have asym : ∀ (x : B.A), B.σ x = x * (ε * B.g) → ∀ z y, K.c (B.herm x z y) = B.herm x (ε * B.g * y) z := by
    intro x hx z y; unfold InvAlg.herm
    rw [← trσ]; congr 1; simp only [map_mul, B.σ_σ, hx]; ring

  have nd : ∀ x : B.A, (∀ y, Algebra.trace K.E B.A (x * y) = 0) → x = 0 :=
    fun x hx => GlobalTheory.UnitLemma.PairClass.trace_nondeg K.E B.A B.g hs' x hx
  have ndh : ∀ w : B.A, (∀ z, B.herm β w z = 0) → w = 0 := by
    intro w hw
    have h0 : (β : B.A) * w = 0 := nd _ (fun y => by
      have := hw (B.σ y); unfold InvAlg.herm at this; rwa [B.σ_σ] at this)
    have := congrArg (fun z => ((β⁻¹ : B.Aˣ) : B.A) * z) h0
    simpa [← mul_assoc] using this

  let φ : B.A ≃ₗ[K.E] B.A := b'.equiv b (Equiv.refl _)
  have hφb : ∀ i, φ (b' i) = b i := fun i => by simp [φ, Module.Basis.equiv_apply]
  have hφ : ∀ u v, B.herm β (φ u) (φ v) = B.herm β' u v := by
    let F₁ : B.A →ₗ[K.E] B.A →ₛₗ[(K.c : K.E →+* K.E)] K.E :=
      LinearMap.mk₂'ₛₗ (RingHom.id K.E) (K.c : K.E →+* K.E) (fun u v => B.herm β (φ u) (φ v))
        (fun u u' v => by rw [map_add (f := _), addL]) (fun r u v => by rw [map_smul, smulL]; rfl)
        (fun u v v' => by rw [map_add (f := _), addR]) (fun r u v => by rw [map_smul, smulR]; rfl)
    let F₂ : B.A →ₗ[K.E] B.A →ₛₗ[(K.c : K.E →+* K.E)] K.E :=
      LinearMap.mk₂'ₛₗ (RingHom.id K.E) (K.c : K.E →+* K.E) (fun u v => B.herm β' u v)
        (fun u u' v => addL _ _ _ _) (fun r u v => smulL _ _ _ _)
        (fun u v v' => addR _ _ _ _) (fun r u v => smulR _ _ _ _)
    have hF : F₁ = F₂ := LinearMap.ext_basis b' b' (fun i j => by
      simp only [F₁, F₂, LinearMap.mk₂'ₛₗ_apply, hφb]; exact hgram i j)
    intro u v
    have := LinearMap.congr_fun₂ hF u v
    simp only [F₁, F₂, LinearMap.mk₂'ₛₗ_apply] at this
    exact this
  have hcomm : ∀ u, φ (ε * B.g * u) = ε * B.g * φ u := by
    intro u
    rw [← sub_eq_zero]
    apply ndh
    intro z
    obtain ⟨v, rfl⟩ : ∃ v, φ v = z := ⟨φ.symm z, by simp⟩
    rw [subL, hφ, ← asym _ hβ', ← hφ, asym _ hβ, sub_self]
  have hg : ∀ u, φ (B.g * u) = B.g * φ u := by
    intro u
    rcases hε with rfl | rfl
    · simpa using hcomm u
    · have := hcomm u
      simp only [neg_mul, one_mul, map_neg, neg_inj] at this
      exact this
  have hpoly : ∀ q : K.E[X], ∀ u, φ (aeval B.g q * u) = aeval B.g q * φ u := by
    intro q
    induction q using Polynomial.induction_on with
    | C r => intro u; rw [aeval_C, ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
    | add p q hp hq => intro u; rw [map_add (f := _), add_mul, add_mul, map_add (f := _), hp, hq]
    | monomial n r h =>
      intro u
      have e : aeval B.g (C r * X ^ (n + 1)) = aeval B.g (C r * X ^ n) * B.g := by
        simp [pow_succ, mul_assoc]
      rw [e, mul_assoc, h, hg, mul_assoc]
  have hmul : ∀ y, φ y = y * φ 1 := by
    intro y
    obtain ⟨q, rfl⟩ := GlobalTheory.UnitLemma.PairClass.exists_aeval_eq_of_separable B.g hs' y
    simpa using hpoly q 1
  have ht : IsUnit (φ 1) := by
    have := hmul (φ.symm 1)
    rw [LinearEquiv.apply_symm_apply] at this
    exact ⟨⟨φ 1, φ.symm 1, by rw [mul_comm]; exact this.symm, this.symm⟩, rfl⟩
  refine ⟨ht.unit, ?_⟩
  rw [IsUnit.unit_spec]
  rw [← sub_eq_zero]
  apply nd
  intro y
  have h1 := hφ y 1
  rw [hmul y] at h1
  unfold InvAlg.herm at h1
  rw [map_one B.σ, mul_one] at h1
  have h2 : ((β' : B.A) - β * (φ 1 * B.σ (φ 1))) * y = (β' : B.A) * y - β * (y * φ 1) * B.σ (φ 1) := by ring
  rw [h2, map_sub, h1, sub_self]

end GlobalTheory.UnitLemma.IsometryUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOfEqualGramTraceFormsStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_of_equal_gram_traceForms : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∀ (a : ℕ) (β β' : B.Aˣ), B.σ (β : B.A) = β * (ε * B.g) → B.σ (β' : B.A) = β' * (ε * B.g) → ∀ b b' : Module.Basis (Fin a) K.E B.A, (∀ i j, B.herm β (b i) (b j) = B.herm β' (b' i) (b' j)) → ∃ t : B.Aˣ, (β' : B.A) = β * (t * B.σ t) := by
  first | exact @GlobalTheory.UnitLemma.IsometryUnit.isometry_unit | exact GlobalTheory.UnitLemma.IsometryUnit.isometry_unit | (intros; apply GlobalTheory.UnitLemma.IsometryUnit.isometry_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjugacyClassesEquivUnitsModNormsNonspli
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TwClassForms

theorem twConj_gram (L : Type) [Field L] (c : L →+* L) (a : ℕ) (δ q : GL (Fin a) L) :
    (((q⁻¹ * δ * thetaGL a c q).val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ =
      q.valᵀ * ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ * q.val.map c := by
  have hΦ : GlobalTheory.Tw.Phi a L * (GlobalTheory.Tw.Phi a L)ᵀ = 1 := Phi_mul_transpose a L
  have hΦ' : (GlobalTheory.Tw.Phi a L)ᵀ * GlobalTheory.Tw.Phi a L = 1 := mul_eq_one_comm.1 hΦ
  have hinv : (GlobalTheory.Tw.Phi a L)⁻¹ = (GlobalTheory.Tw.Phi a L)ᵀ := Matrix.inv_eq_left_inv hΦ'
  have hθ : (thetaGL a c q).val =
      GlobalTheory.Tw.Phi a L * ((GeneralLinearGroup.map c q)⁻¹).valᵀ * (GlobalTheory.Tw.Phi a L)ᵀ := rfl
  have hC : ((GeneralLinearGroup.map c q)⁻¹).valᵀ * (q.val.map c)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, show q.val.map c = (GeneralLinearGroup.map c q).val from rfl,
      Units.mul_inv, Matrix.transpose_one]
  have k1 : ∀ X : Matrix (Fin a) (Fin a) L, (GlobalTheory.Tw.Phi a L)ᵀ * (GlobalTheory.Tw.Phi a L * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hΦ', Matrix.one_mul]
  have k2 : ∀ X : Matrix (Fin a) (Fin a) L, ((GeneralLinearGroup.map c q)⁻¹).valᵀ * ((q.val.map c)ᵀ * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hC, Matrix.one_mul]
  have k3 : ∀ X : Matrix (Fin a) (Fin a) L, GlobalTheory.Tw.Phi a L * ((GlobalTheory.Tw.Phi a L)ᵀ * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hΦ, Matrix.one_mul]
  have k4 : ∀ X : Matrix (Fin a) (Fin a) L, δ.val * ((δ⁻¹).val * X) = X := by
    intro X; rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hY : (q⁻¹ * δ * thetaGL a c q).val * GlobalTheory.Tw.Phi a L *
      ((q.val.map c)ᵀ * (GlobalTheory.Tw.Phi a L)ᵀ * (δ⁻¹).val * q.val) = 1 := by
    simp only [Units.val_mul, hθ, Matrix.mul_assoc, k1, k2, k3, k4]
    exact Units.inv_mul q
  rw [Matrix.inv_eq_right_inv hY, Matrix.mul_inv_rev, hinv, ← Matrix.coe_units_inv]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem gram_delta (L : Type) [Field L] (a : ℕ) :
    (∀ G : Matrix (Fin a) (Fin a) L, IsUnit G.det → ∃ δ : GL (Fin a) L, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = G) ∧
    (∀ δ δ' : GL (Fin a) L, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = ((δ'.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ → δ = δ') := by
  have hΦ : GlobalTheory.Tw.Phi a L * (GlobalTheory.Tw.Phi a L)ᵀ = 1 := Phi_mul_transpose a L
  have hΦ' : (GlobalTheory.Tw.Phi a L)ᵀ * GlobalTheory.Tw.Phi a L = 1 := mul_eq_one_comm.1 hΦ
  have hdΦ : IsUnit (GlobalTheory.Tw.Phi a L).det := Matrix.isUnit_det_of_right_inverse hΦ
  refine ⟨fun G hG => ?_, fun δ δ' h => ?_⟩
  · have hGT : IsUnit (Gᵀ)⁻¹.det := by
      rw [Matrix.det_nonsing_inv, Matrix.det_transpose]; exact hG.ringInverse
    have hd : IsUnit ((Gᵀ)⁻¹ * (GlobalTheory.Tw.Phi a L)ᵀ).det := by
      rw [Matrix.det_mul, Matrix.det_transpose]; exact hGT.mul hdΦ
    refine ⟨Matrix.nonsingInvUnit _ hd, ?_⟩
    change (((Gᵀ)⁻¹ * (GlobalTheory.Tw.Phi a L)ᵀ * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = G
    rw [Matrix.mul_assoc, hΦ', Matrix.mul_one, Matrix.nonsing_inv_nonsing_inv _ (by rw [Matrix.det_transpose]; exact hG),
      Matrix.transpose_transpose]
  · have hu : ∀ x : GL (Fin a) L, IsUnit (x.val * GlobalTheory.Tw.Phi a L).det := by
      intro x; rw [Matrix.det_mul]; exact (Matrix.isUnits_det_units x).mul hdΦ
    have h1 := congrArg Matrix.transpose h
    simp only [Matrix.transpose_transpose] at h1
    have h2 := congrArg Inv.inv h1
    rw [Matrix.nonsing_inv_nonsing_inv _ (hu δ), Matrix.nonsing_inv_nonsing_inv _ (hu δ')] at h2
    have h3 := congrArg (· * (GlobalTheory.Tw.Phi a L)ᵀ) h2
    simp only [Matrix.mul_assoc, hΦ, Matrix.mul_one] at h3
    exact Units.ext h3

theorem herm_norm_basis (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (a : ℕ) (β t : B.Aˣ)
    (b : Module.Basis (Fin a) K.E B.A) : ∃ b' : Module.Basis (Fin a) K.E B.A,
      ∀ i j, B.herm ((β : B.A) * (t * B.σ t)) (b i) (b j) = B.herm β (b' i) (b' j) := by
  let f : B.A ≃ₗ[K.E] B.A := LinearEquiv.ofLinear (LinearMap.mulLeft K.E (t : B.A))
    (LinearMap.mulLeft K.E ((t⁻¹ : B.Aˣ) : B.A))
    (by ext y; simp [← mul_assoc]) (by ext y; simp [← mul_assoc])
  refine ⟨b.map f, fun i j => ?_⟩
  simp only [Module.Basis.map_apply, f, LinearEquiv.ofLinear_apply, LinearMap.mulLeft_apply,
    GlobalTheory.UnitLemma.InvAlg.herm, map_mul]
  congr 1
  ring

theorem twCl_equiv_cl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (Q : (w.adicCompletion E)[X]), Q.Monic → Q.natDegree = a → Q.Separable → ∀ (B : GlobalTheory.UnitLemma.InvAlg K), B.g * B.σ B.g = 1 → B.P = Q.map e.symm.toRingHom → ∀ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * ((-1) ^ (a - 1) * B.g) → ∃ F : B.Cl ≃ {c : TwCl (thL a w) // (nrmL a w c.rep).val.charpoly = Q}, ∀ k : B.Cl, ∃ b : Module.Basis (Fin a) K.E B.A, ∀ i j, (((F k).1.rep.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm ((β₀ : B.A) * k.rep) (b i) (b j)) := by
  intro E _ _ _ hE w hw K e he hO a Q hQm hQd hQs B hg hP β₀ hβ₀
  have hthL : thL a w = thetaGL a (cj w) := by rw [thL, if_neg hw]
  have hnrm : ∀ y, nrmL a w y = y * thetaGL a (cj w) y := by intro y; rw [nrmL, if_neg hw]
  have hcc : ∀ x, cj w (cj w x) = x := by
    intro x; obtain ⟨y, rfl⟩ := e.surjective x; rw [← he, ← he, K.c_c]
  have hPsep : B.P.Separable := by rw [hP]; exact hQs.map
  have hfr : Module.finrank K.E B.A = a := by
    rw [← LinearMap.charpoly_natDegree (LinearMap.mulLeft K.E B.g)]
    change B.P.natDegree = a
    rw [hP, natDegree_map, hQd]
  let b0 : Module.Basis (Fin a) K.E B.A := Module.finBasisOfFinrankEq K.E B.A hfr
  have hε : ((-1 : B.A) ^ (a - 1) = 1 ∨ (-1 : B.A) ^ (a - 1) = -1) := neg_one_pow_eq_or B.A (a - 1)
  have hβx : ∀ x : B.Aˣ, B.σ (x : B.A) = x →
      B.σ ((β₀ * x : B.Aˣ) : B.A) = (β₀ * x : B.Aˣ) * ((-1) ^ (a - 1) * B.g) := by
    intro x hx; simp only [Units.val_mul, map_mul, hβ₀, hx]; ring

  have htwE : ∀ δ δ' : GLw a w, Relation.EqvGen (fun x y : GLw a w => ∃ g, y = g⁻¹ * x * thL a w g) δ δ' →
      ∃ q, δ' = q⁻¹ * δ * thL a w q := by
    intro δ δ' h
    induction h with
    | rel x y hxy => exact hxy
    | refl x => exact ⟨1, by simp⟩
    | symm x y _ ih =>
      obtain ⟨q, rfl⟩ := ih
      exact ⟨q⁻¹, by simp [mul_assoc]⟩
    | trans x y z _ _ ih1 ih2 =>
      obtain ⟨q, rfl⟩ := ih1
      obtain ⟨r, rfl⟩ := ih2
      exact ⟨q * r, by simp [mul_assoc]⟩
  have hσinv : ∀ u : B.Aˣ, B.σ ((u⁻¹ : B.Aˣ) : B.A) * B.σ (u : B.A) = 1 := by
    intro u; rw [← map_mul, Units.inv_mul, map_one]
  have hclE : ∀ x y : {x : B.Aˣ // B.σ (x : B.A) = x}, Relation.EqvGen (fun x y : {x : B.Aˣ // B.σ (x : B.A) = x} =>
      ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A))) x y → ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A)) := by
    intro x y h
    induction h with
    | rel x y hxy => exact hxy
    | refl x => exact ⟨1, by simp⟩
    | symm x y _ ih =>
      obtain ⟨u, hu⟩ := ih
      refine ⟨u⁻¹, ?_⟩
      have h1 := hσinv u
      have h2 : ((u⁻¹ : B.Aˣ) : B.A) * u = 1 := Units.inv_mul u
      rw [hu]
      linear_combination (-(x.1 : B.A) * (B.σ ((u⁻¹ : B.Aˣ) : B.A) * B.σ (u : B.A))) * h2 - (x.1 : B.A) * h1
    | trans x y z _ _ ih1 ih2 =>
      obtain ⟨u, hu⟩ := ih1
      obtain ⟨v, hv⟩ := ih2
      exact ⟨u * v, by rw [hv, hu, Units.val_mul, map_mul]; ring⟩

  obtain ⟨F0i, F0u⟩ := gram_delta (w.adicCompletion E) a
  have hF1 := GlobalTheory.T.hermitian_form_det_unit_and_twist K B (w.adicCompletion E) e (cj w) he hcc a Q hP hQs hQd
  have hF4 := GlobalTheory.T.gramMatrix_traceForm_basis_change K B (w.adicCompletion E) e (cj w) he a
  have hF6 := twConj_gram (w.adicCompletion E) (cj w) a
  have hcl : ∀ k : B.Cl, B.σ (((Quot.out k).1 : B.Aˣ) : B.A) = (Quot.out k).1 := fun k => (Quot.out k).2
  have hG : ∀ k : B.Cl, IsUnit (Matrix.of fun i j => e (B.herm (((β₀ * (Quot.out k).1 : B.Aˣ)) : B.A) (b0 i) (b0 j))).det :=
    fun k => (hF1 _ (hβx _ (hcl k)) b0).1
  choose δk hδk using fun k => F0i _ (hG k)

  have hrep : ∀ k : B.Cl, ∀ δ : GLw a w, Relation.EqvGen (fun x y : GLw a w => ∃ g, y = g⁻¹ * x * thL a w g) (δk k) δ →
      ∃ b : Module.Basis (Fin a) K.E B.A, ((δ.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ =
        Matrix.of fun i j => e (B.herm (((β₀ * (Quot.out k).1 : B.Aˣ)) : B.A) (b i) (b j)) := by
    intro k δ h
    obtain ⟨q, rfl⟩ := htwE _ _ h
    rw [hthL, hF6, hδk k]
    obtain ⟨b', hb'⟩ := (hF4 _ b0).1 q
    exact ⟨b', hb'.symm⟩
  let F : B.Cl → {c : TwCl (thL a w) // (nrmL a w c.rep).val.charpoly = Q} := fun k =>
    ⟨Quot.mk _ (δk k), by
      obtain ⟨b, hb⟩ := hrep k _ (Quot.eqvGen_exact (Quot.out_eq (Quot.mk _ (δk k)))).symm
      rw [hnrm]
      exact (hF1 _ (hβx _ (hcl k)) b).2 _ hb⟩
  have hinj : Function.Injective F := by
    intro k k' hkk
    have h1 : (Quot.mk _ (δk k) : TwCl (thL a w)) = Quot.mk _ (δk k') := congrArg Subtype.val hkk
    obtain ⟨b', hb'⟩ := hrep k _ (Quot.eqvGen_exact h1)
    rw [hδk k'] at hb'
    obtain ⟨t, ht⟩ := GlobalTheory.T.exists_norm_of_equal_gram_traceForms K B hPsep _ hε a _ _ (hβx _ (hcl k')) (hβx _ (hcl k)) b0 b' (fun i j => by
      have := congrFun (congrFun hb' i) j
      simpa using e.injective this)
    have hrel : (Quot.mk _ (Quot.out k') : B.Cl) = Quot.mk _ (Quot.out k) := by
      apply Quot.sound
      refine ⟨t, ?_⟩
      have h2 : ((β₀⁻¹ : B.Aˣ) : B.A) * β₀ = 1 := Units.inv_mul β₀
      simp only [Units.val_mul] at ht
      linear_combination ((β₀⁻¹ : B.Aˣ) : B.A) * ht - (((Quot.out k).1 : B.A) - ((Quot.out k').1 : B.A) * ((t : B.A) * B.σ (t : B.A))) * h2
    exact (Quot.out_eq k).symm.trans (hrel.symm.trans (Quot.out_eq k'))

  have hsurj : Function.Surjective F := by
    rintro ⟨cl, hclQ⟩
    have hQδ : ((Quot.out cl) * thetaGL a (cj w) (Quot.out cl)).val.charpoly = Q := by
      rw [← hnrm]; exact hclQ
    obtain ⟨β, hβ, b, hb⟩ := GlobalTheory.T.exists_traceForm_of_twistedNorm_charpoly K B (w.adicCompletion E) e (cj w) he hcc hg a Q hP hQs hQd _ hQδ
    have hx : B.σ (((β₀⁻¹ * β : B.Aˣ)) : B.A) = ((β₀⁻¹ * β : B.Aˣ) : B.A) := by
      have h1 : B.σ ((β₀⁻¹ : B.Aˣ) : B.A) * ((β₀ : B.A) * ((-1) ^ (a - 1) * B.g)) = 1 := by
        rw [← hβ₀, ← map_mul, Units.inv_mul, map_one]
      have h2 : ((β₀⁻¹ : B.Aˣ) : B.A) * β₀ = 1 := Units.inv_mul β₀
      simp only [Units.val_mul, map_mul, hβ]
      linear_combination (((β₀⁻¹ : B.Aˣ) : B.A) * β) * h1 - (B.σ ((β₀⁻¹ : B.Aˣ) : B.A) * β * ((-1) ^ (a - 1) * B.g)) * h2
    let k : B.Cl := Quot.mk _ ⟨β₀⁻¹ * β, hx⟩
    refine ⟨k, ?_⟩
    obtain ⟨u, hu⟩ := hclE _ _ (Quot.eqvGen_exact (Quot.out_eq k)).symm
    have hβu : ((β₀ * (Quot.out k).1 : B.Aˣ) : B.A) = (β : B.A) * ((u : B.A) * B.σ (u : B.A)) := by
      rw [Units.val_mul, hu, Units.val_mul]
      have h2 : (β₀ : B.A) * ((β₀⁻¹ : B.Aˣ) : B.A) = 1 := Units.mul_inv β₀
      linear_combination ((β : B.A) * ((u : B.A) * B.σ (u : B.A))) * h2
    obtain ⟨b'', hb''⟩ := herm_norm_basis K B a β u b0
    obtain ⟨P, hPb⟩ := (hF4 (β : B.A) b).2 b''
    have hmat : ((δk k).val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹ᵀ =
        (((P⁻¹ * Quot.out cl * thetaGL a (cj w) P)).val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹ᵀ := by
      rw [hF6, hb, ← hPb, hδk k]
      ext i j
      simp only [Matrix.of_apply, hβu, hb'']
    have hδeq := F0u _ _ hmat
    apply Subtype.ext
    change (Quot.mk _ (δk k) : TwCl (thL a w)) = cl
    rw [hδeq]
    have hθP : thL a w P = thetaGL a (cj w) P := by rw [hthL]
    exact (Quot.sound (⟨P, by rw [hθP]⟩ : ∃ g, P⁻¹ * Quot.out cl * thetaGL a (cj w) P = g⁻¹ * Quot.out cl * thL a w g)).symm.trans (Quot.out_eq cl)
  refine ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, fun k => ?_⟩
  obtain ⟨b, hb⟩ := hrep k _ (Quot.eqvGen_exact (Quot.out_eq (Quot.mk _ (δk k) : TwCl (thL a w)))).symm
  refine ⟨b, fun i j => ?_⟩
  have := congrFun (congrFun hb i) j
  rw [Matrix.of_apply, Units.val_mul] at this
  exact this

end GlobalTheory.TwClassForms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjugacyClassesEquivUnitsModNormsNonspliStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedConjugacyClasses_equiv_unitsModNorms_nonsplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (Q : (w.adicCompletion E)[X]), Q.Monic → Q.natDegree = a → Q.Separable → ∀ (B : GlobalTheory.UnitLemma.InvAlg K), B.g * B.σ B.g = 1 → B.P = Q.map e.symm.toRingHom → ∀ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * ((-1) ^ (a - 1) * B.g) → ∃ F : B.Cl ≃ {c : TwCl (thL a w) // (nrmL a w c.rep).val.charpoly = Q}, ∀ k : B.Cl, ∃ b : Module.Basis (Fin a) K.E B.A, ∀ i j, (((F k).1.rep.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm ((β₀ : B.A) * k.rep) (b i) (b j)) := by
  first | exact @GlobalTheory.TwClassForms.twCl_equiv_cl | exact GlobalTheory.TwClassForms.twCl_equiv_cl | (intros; apply GlobalTheory.TwClassForms.twCl_equiv_cl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStableTwistedOrbitalUnitEqLatticeSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasePointTwistedHermUnimodularEqSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasePointTwistedHermUnimodularEqSelfDual
namespace GlobalTheory.UnitLemma.TwistUnitAny

open GlobalTheory.UnitLemma Polynomial

variable {K : UQ}

theorem stable_of_unimodular (B : InvAlg K) (hg : B.g * B.σ B.g = 1) (ε : B.A) (hε : ε = 1 ∨ ε = -1)
    (β x : B.A) (hβ : B.σ β = β * (ε * B.g)) (hx : B.σ x = x) (L : Submodule K.O B.A)
    (hU : ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm (β * x) y z ∈ (algebraMap K.O K.E).range) :
    ∀ y ∈ L, B.g * y ∈ L := by
  set R := (algebraMap K.O K.E).range with hR
  set T := Algebra.trace K.E B.A with hT
  have hεT : ∀ a, T (ε * a) ∈ R ↔ T a ∈ R := by
    intro a
    rcases hε with rfl | rfl
    · rw [one_mul]
    · rw [neg_one_mul, map_neg, neg_mem_iff]
  have hsym : ∀ a b : B.A, T (β * x * a * B.σ b) ∈ R ↔ T (β * x * (B.g * b) * B.σ a) ∈ R := by
    intro a b
    rw [← TwistUnit.trace_σ_mem B (β * x * a * B.σ b),
      show B.σ (β * x * a * B.σ b) = ε * (β * x * (B.g * b) * B.σ a) by
        rw [map_mul, map_mul, map_mul, hβ, hx, B.σ_σ]; ring, hεT]
  simp only [InvAlg.herm, ← hT, ← hR] at hU
  have h1 : ∀ y ∈ L, B.σ B.g * y ∈ L := by
    intro y hy
    rw [hU]
    intro y' hy'
    rw [hsym, show β * x * (B.g * (B.σ B.g * y)) * B.σ y' = β * x * y * B.σ y' by
      linear_combination (β * x * y * B.σ y') * hg]
    exact (hU y').1 hy' y hy
  intro y hy
  rw [hU]
  intro y' hy'
  have hb : B.σ B.g * (B.σ B.g * y') ∈ L := h1 _ (h1 y' hy')
  have := (hU _).1 hb y hy
  rw [hsym] at this
  rw [show β * x * y' * B.σ (B.g * y) = β * x * (B.g * (B.σ B.g * (B.σ B.g * y'))) * B.σ y by
    rw [map_mul]; linear_combination (-(β * x * y' * B.σ B.g * B.σ y)) * hg]
  exact this

theorem twisted_unit_eq_unit_any : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable →
    ∀ ε : B.A, (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧
      ∀ x : B.Aˣ, B.σ (x : B.A) = x →
        {L : Submodule K.O B.A | GlobalTheory.UnitLemma.IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L,
          B.herm ((β₀ : B.A) * x) y z ∈ (algebraMap K.O K.E).range} = B.X x := by
  intro K B hg hs ε hε
  by_cases hi : IsIntegral K.O B.g
  · exact TwistUnit.twisted_unit_eq_unit K B hg hs hi ε hε
  have hσε : B.σ ε = ε := by rcases hε with rfl | rfl <;> simp
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hu : (ε * B.g) * B.σ (ε * B.g) = 1 := by
    rw [map_mul, hσε]; linear_combination B.g * B.σ B.g * hεε + hg
  obtain ⟨β₀, hβ⟩ := GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma K B (ε * B.g) hu
  refine ⟨β₀, hβ, fun x hx => ?_⟩
  ext L
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hLat, hU⟩
    exact absurd (isIntegral_of_isLat_stable L hLat B.g
      (stable_of_unimodular B hg ε hε β₀ x hβ hx L hU)) hi
  · rintro ⟨hLat, h2, -⟩
    exact absurd (isIntegral_of_isLat_stable L hLat B.g h2) hi

end GlobalTheory.UnitLemma.TwistUnitAny
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasePointTwistedHermUnimodularEqSelfDualStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basePoint_twistedHerm_unimodular_eq_selfDual : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → ∀ ε : B.A, (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧ ∀ x : B.Aˣ, B.σ (x : B.A) = x → {L : Submodule K.O B.A | GlobalTheory.UnitLemma.IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm ((β₀ : B.A) * x) y z ∈ (algebraMap K.O K.E).range} = B.X x := by
  first | exact @GlobalTheory.UnitLemma.TwistUnitAny.twisted_unit_eq_unit_any | exact GlobalTheory.UnitLemma.TwistUnitAny.twisted_unit_eq_unit_any | (intros; apply GlobalTheory.UnitLemma.TwistUnitAny.twisted_unit_eq_unit_any <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfReciprocalInvAlgWithPoly
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfReciprocalInvAlgWithPoly
open Polynomial

namespace GlobalTheory.UnitLemma

noncomputable section

namespace InertUnit

variable {K : UQ} {P : K.E[X]}

theorem coeff_mul (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    K.c (P.coeff 0) * P.coeff 0 = 1 := by
  have h := congrArg (fun Q => Q.coeff 0) hr
  simp only [coeff_C_mul, coeff_zero_reverse] at h
  rw [h, leadingCoeff_map_of_leadingCoeff_ne_zero _ (by simp [hP.leadingCoeff]), hP.leadingCoeff, map_one]

def rootInv (P : K.E[X]) : AdjoinRoot P :=
  -(algebraMap K.E (AdjoinRoot P) (K.c (P.coeff 0))) * aeval (AdjoinRoot.root P) P.divX

theorem root_mul_rootInv (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    AdjoinRoot.root P * rootInv P = 1 := by
  have h0 : aeval (AdjoinRoot.root P) P = 0 := AdjoinRoot.aeval_eq P ▸ AdjoinRoot.mk_self
  have h1 := congrArg (aeval (AdjoinRoot.root P)) (X_mul_divX_add P)
  rw [h0, map_add (f := _), map_mul, aeval_X, aeval_C] at h1
  have h2 : AdjoinRoot.root P * aeval (AdjoinRoot.root P) P.divX = -algebraMap K.E (AdjoinRoot P) (P.coeff 0) :=
    eq_neg_of_add_eq_zero_left h1
  unfold rootInv
  rw [mul_left_comm, h2, neg_mul_neg, ← map_mul, coeff_mul hP hr, map_one]

theorem eval_rootInv (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    P.eval₂ ((algebraMap K.E (AdjoinRoot P)).comp (K.c : K.E →+* K.E)) (rootInv P) = 0 := by
  have hu := root_mul_rootInv hP hr
  letI : Invertible (rootInv P) := ⟨AdjoinRoot.root P, hu, by rw [mul_comm]; exact hu⟩
  rw [← eval₂_map, ← eval₂_reverse_mul_pow]
  have : ⅟(rootInv P) = AdjoinRoot.root P := rfl
  rw [this, ← hr, eval₂_mul, eval₂_C]
  have h0 : P.eval₂ (algebraMap K.E (AdjoinRoot P)) (AdjoinRoot.root P) = 0 := AdjoinRoot.eval₂_root P
  rw [h0, mul_zero, zero_mul]

def sig (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    AdjoinRoot P →+* AdjoinRoot P :=
  AdjoinRoot.lift ((algebraMap K.E (AdjoinRoot P)).comp (K.c : K.E →+* K.E)) (rootInv P) (eval_rootInv hP hr)

theorem sig_alg (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) (e : K.E) :
    sig hP hr (algebraMap K.E (AdjoinRoot P) e) = algebraMap K.E (AdjoinRoot P) (K.c e) := by
  rw [AdjoinRoot.algebraMap_eq, sig, AdjoinRoot.lift_of]
  rfl

theorem sig_root (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    sig hP hr (AdjoinRoot.root P) = rootInv P := AdjoinRoot.lift_root _

theorem sig_sig (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    (sig hP hr).comp (sig hP hr) = RingHom.id _ := by
  refine AdjoinRoot.ringHom_ext (RingHom.ext fun e => ?_) ?_
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [← AdjoinRoot.algebraMap_eq, sig_alg, sig_alg, K.c_c]
  · simp only [RingHom.comp_apply, RingHom.id_apply, sig_root]
    have hu := root_mul_rootInv hP hr
    have h1 : sig hP hr (AdjoinRoot.root P) * sig hP hr (rootInv P) = 1 := by rw [← map_mul, hu, map_one]
    rw [sig_root] at h1
    calc sig hP hr (rootInv P) = (AdjoinRoot.root P * rootInv P) * sig hP hr (rootInv P) := by rw [hu, one_mul]
      _ = AdjoinRoot.root P * (rootInv P * sig hP hr (rootInv P)) := by ring
      _ = AdjoinRoot.root P := by rw [h1, mul_one]

def invAlg (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) : InvAlg K where
  A := AdjoinRoot P
  fd := (AdjoinRoot.powerBasis hP.ne_zero).finite
  σ := RingEquiv.ofRingHom (sig hP hr) (sig hP hr) (sig_sig hP hr) (sig_sig hP hr)
  σ_σ := fun y => congrArg (fun f : AdjoinRoot P →+* AdjoinRoot P => f y) (sig_sig hP hr)
  σ_alg := sig_alg hP hr
  g := AdjoinRoot.root P

theorem charpoly_root (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    (invAlg hP hr).P = P := by
  haveI : Module.Finite K.E (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  have h := charpoly_leftMulMatrix (AdjoinRoot.powerBasis hP.ne_zero)
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, AdjoinRoot.powerBasis_gen,
    AdjoinRoot.minpoly_root hP.ne_zero, hP.leadingCoeff, inv_one, C_1, mul_one] at h
  exact h

end InertUnit

open InertUnit in
theorem exists_invAlg_root : ∀ (K : GlobalTheory.UnitLemma.UQ) (P : K.E[X]), P.Monic →
    C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse →
    ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = P := by
  intro K P hP hr
  refine ⟨invAlg hP hr, ?_, charpoly_root hP hr⟩
  show AdjoinRoot.root P * sig hP hr (AdjoinRoot.root P) = 1
  rw [sig_root]
  exact root_mul_rootInv hP hr
end
end GlobalTheory.UnitLemma
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfReciprocalInvAlgWithPolyStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfReciprocalInvAlg_with_poly : ∀ (K : GlobalTheory.UnitLemma.UQ) (P : K.E[X]), P.Monic → C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse → ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = P := by
  first | exact @GlobalTheory.UnitLemma.exists_invAlg_root | exact GlobalTheory.UnitLemma.exists_invAlg_root | (intros; apply GlobalTheory.UnitLemma.exists_invAlg_root <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStableTwistedOrbitalUnitEqLatticeSum
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertTwUnit

theorem cast_finsum_rat {ι : Type} (f : ι → ℚ) : ((∑ᶠ i, f i : ℚ) : ℂ) = ∑ᶠ i, (f i : ℂ) := by
  by_cases h : (Function.support f).Finite
  · exact map_finsum (Rat.castHom ℂ) h
  · have h1 : (Function.support f).Infinite := h
    have h2 : (Function.support fun i => (f i : ℂ)).Infinite := by
      have e : (Function.support fun i => (f i : ℂ)) = Function.support f := by
        ext i; simp
      rw [e]; exact h1
    rw [finsum_of_infinite_support h1, finsum_of_infinite_support h2, Rat.cast_zero]

theorem twisted_unit_eq_stSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (a : ℕ) (Q : (w.adicCompletion E)[X]), Q.Monic → Q.natDegree = a → Q.Separable → IsCsr w Q → ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = Q.map e.symm.toRingHom ∧ stTw a w Q ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) = (B.stSum : ℂ) := by
  intro E _ _ _ hU w hw K e hc hr hv hq a Q hm hd hs hQ
  unfold stTw IsCsr at *
  unfold clSum
  have hQ' : C ((cj w) (Q.coeff 0)) * Q = (Q.map (cj w)).reverse := hQ.resolve_left hw
  have hcomm : e.symm.toRingHom.comp (cj w) = (K.c : K.E →+* K.E).comp e.symm.toRingHom := by
    ext y
    have h := congrArg e.symm (hc (e.symm y))
    simp only [RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply] at h
    simp [h]
  have hrev : ∀ p : (w.adicCompletion E)[X],
      (p.reverse).map e.symm.toRingHom = (p.map e.symm.toRingHom).reverse := by
    intro p
    unfold Polynomial.reverse
    rw [Polynomial.natDegree_map_eq_of_injective e.symm.injective, Polynomial.reflect_map]
  have hPr : C (K.c ((Q.map e.symm.toRingHom).coeff 0)) * Q.map e.symm.toRingHom =
      ((Q.map e.symm.toRingHom).map (K.c : K.E →+* K.E)).reverse := by
    have h1 := congrArg (Polynomial.map e.symm.toRingHom) hQ'
    have h0 : e.symm.toRingHom ((cj w) (Q.coeff 0)) = K.c ((Q.map e.symm.toRingHom).coeff 0) := by
      rw [Polynomial.coeff_map]
      exact RingHom.congr_fun hcomm (Q.coeff 0)
    rw [Polynomial.map_mul, Polynomial.map_C, h0] at h1
    rw [h1, hrev, Polynomial.map_map, hcomm, ← Polynomial.map_map]
  obtain ⟨B, hg, hP⟩ := GlobalTheory.T.exists_selfReciprocalInvAlg_with_poly K (Q.map e.symm.toRingHom) (hm.map _) hPr
  have hsep : B.P.Separable := by
    rw [hP]
    exact hs.map
  refine ⟨B, hg, hP, ?_⟩
  have hε : (-1 : B.A) ^ (a - 1) = 1 ∨ (-1 : B.A) ^ (a - 1) = -1 := neg_one_pow_eq_or B.A (a - 1)
  obtain ⟨β₀, hβ₀, hX⟩ := GlobalTheory.T.exists_basePoint_twistedHerm_unimodular_eq_selfDual K B hg hsep _ hε
  obtain ⟨F, hF⟩ := GlobalTheory.T.twistedConjugacyClasses_equiv_unitsModNorms_nonsplit E hU w hw K e hc hr a Q hm hd hs B hg hP β₀ hβ₀
  have hterm : ∀ k : B.Cl, twOrb (thL a w) (GlobalTheory.LFun.KGL w (n := a)) (F k).1.rep
      ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) = ((B.N k.rep : ℚ) : ℂ) := by
    intro k
    obtain ⟨b, hb⟩ := hF k
    have hu : B.σ (((Quot.out k).1 : B.Aˣ) : B.A) = ((Quot.out k).1 : B.Aˣ) := (Quot.out k).2
    have hβ : B.σ ((β₀ * (Quot.out k).1 : B.Aˣ) : B.A) =
        (β₀ * (Quot.out k).1 : B.Aˣ) * ((-1) ^ (a - 1) * B.g) := by
      rw [Units.val_mul, map_mul, hβ₀, hu]
      ring
    have h := GlobalTheory.T.twistedOrbitalIntegral_unitGL_eq_hermitianLatticeCount E hU w hw K e hc hr a B hsep (β₀ * (Quot.out k).1) _ hε hβ b (F k).1.rep
      (fun i j => by rw [Units.val_mul]; exact hb i j)
    rw [h, Units.val_mul, hX _ hu]
    rfl
  simp only [Set.mem_ofPred_eq, Pi.one_apply, one_mul]
  simp only [← finsum_eq_if]
  rw [← finsum_subtype_eq_finsum_cond, ← finsum_comp_equiv F]
  simp only [hterm]
  exact (cast_finsum_rat _).symm

end GlobalTheory.InertTwUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStableTwistedOrbitalUnitEqLatticeSumStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_stableTwistedOrbital_unit_eq_latticeSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (a : ℕ) (Q : (w.adicCompletion E)[X]), Q.Monic → Q.natDegree = a → Q.Separable → IsCsr w Q → ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = Q.map e.symm.toRingHom ∧ stTw a w Q ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) = (B.stSum : ℂ) := by
  first | exact @GlobalTheory.InertTwUnit.twisted_unit_eq_stSum | exact GlobalTheory.InertTwUnit.twisted_unit_eq_stSum | (intros; apply GlobalTheory.InertTwUnit.twisted_unit_eq_stSum <;> assumption)
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriTrivialCase.IwahoriTrivialLemmas.UnitProductIndicatorTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyNrmLConj
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.UnitProd

private theorem equivalence_twisted_conj {G : Type} [Group G] (θ : G →* G) :
    Equivalence (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) := by
  constructor
  · intro x
    exact ⟨1, by simp⟩
  · rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by rw [map_inv]; group⟩
  · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by rw [map_mul]; group⟩

theorem rep_mk {G : Type} [Group G] (θ : G →* G) (x : G) :
    ∃ g, TwCl.rep (θ := θ) (Quot.mk _ x) = g⁻¹ * x * θ g := by
  unfold TwCl.rep
  have h := Quot.eqvGen_exact (Quot.out_eq (Quot.mk (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) x))
  rw [Equivalence.eqvGen_iff (equivalence_twisted_conj θ)] at h
  exact (equivalence_twisted_conj θ).symm h

theorem mk_rep {G : Type} [Group G] {θ : G →* G} (c : TwCl θ) : (Quot.mk _ c.rep : TwCl θ) = c := by
  unfold TwCl.rep
  exact Quot.out_eq c

noncomputable def clsEquiv {G G' : Type} [Group G] [Group G'] (θ : G →* G) (θ' : G' →* G') :
    TwCl θ × TwCl θ' ≃ TwCl (θ.prodMap θ') where
  toFun p := Quot.mk _ (p.1.rep, p.2.rep)
  invFun c := (Quot.mk _ c.rep.1, Quot.mk _ c.rep.2)
  left_inv p := by
    obtain ⟨g, hg⟩ := rep_mk (θ.prodMap θ') (p.1.rep, p.2.rep)
    refine Prod.ext ?_ ?_
    · refine Eq.trans (Quot.sound ⟨g.1, ?_⟩).symm (mk_rep p.1)
      exact congrArg Prod.fst hg
    · refine Eq.trans (Quot.sound ⟨g.2, ?_⟩).symm (mk_rep p.2)
      exact congrArg Prod.snd hg
  right_inv c := by
    obtain ⟨g, hg⟩ := rep_mk θ c.rep.1
    obtain ⟨g', hg'⟩ := rep_mk θ' c.rep.2
    refine Eq.trans (Quot.sound ⟨(g, g'), ?_⟩).symm (mk_rep c)
    refine Prod.ext ?_ ?_
    · simp [hg]
    · simp [hg']

theorem ind_conj {G : Type} [Group G] (θ : G →* G) (K : Subgroup G) (hK : ∀ k ∈ K, θ k ∈ K) (δ x k : G) (hk : k ∈ K) :
    (x * k)⁻¹ * δ * θ (x * k) ∈ K ↔ x⁻¹ * δ * θ x ∈ K := by

  have e : (x * k)⁻¹ * δ * θ (x * k) = k⁻¹ * (x⁻¹ * δ * θ x) * θ k := by
    rw [map_mul]; group
  rw [e, K.mul_mem_cancel_right (hK k hk), K.mul_mem_cancel_left (K.inv_mem hk)]

theorem index_ne {G : Type} [Group G] (θ : G →* G) (K : Subgroup G) (hK : ∀ k ∈ K, θ k ∈ K) (δ x : G) :
    (rStab fun k : K => (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0 := by

  have htop : rStab (fun k : K => (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * δ * θ (x * k))) = ⊤ := by
    ext k
    simp only [Subgroup.mem_top, iff_true]
    rw [GlobalTheory.TwOrbConj.mem_rStab]
    intro y
    simp only [Subgroup.coe_mul, ← mul_assoc]
    rw [Set.indicator_apply, Set.indicator_apply]
    simp only [SetLike.mem_coe, ind_conj θ K hK δ (x * y) k k.2, Pi.one_apply]
  rw [htop, Subgroup.index_top]
  exact one_ne_zero

theorem clSum_prod {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] [T2Space G'] (θ : G →* G) (θ' : G' →* G') (K : Subgroup G)
    (K' : Subgroup G') (S : Set G) (S' : Set G') (hK : ∀ k ∈ K, θ k ∈ K) (hK' : ∀ k ∈ K', θ' k ∈ K')
    (hS : ∀ g y, g⁻¹ * y * θ g ∈ S ↔ y ∈ S) (hS' : ∀ g y, g⁻¹ * y * θ' g ∈ S' ↔ y ∈ S')
    (hf : {c : TwCl θ | c.rep ∈ S}.Finite) (hf' : {c : TwCl θ' | c.rep ∈ S'}.Finite)
    (hd : ∀ y ∈ S, {q : DoubleCoset.Quotient (twCent θ y : Set G) (K : Set G) |
      (Quotient.out q)⁻¹ * y * θ (Quotient.out q) ∈ K}.Finite)
    (hd' : ∀ y ∈ S', {q : DoubleCoset.Quotient (twCent θ' y : Set G') (K' : Set G') |
      (Quotient.out q)⁻¹ * y * θ' (Quotient.out q) ∈ K'}.Finite) :
    clSum (θ.prodMap θ') (K.prod K') {y | y.1 ∈ S ∧ y.2 ∈ S'} 1 (((K.prod K' : Subgroup _) : Set _).indicator 1) =
      clSum θ K S 1 ((K : Set G).indicator 1) * clSum θ' K' S' 1 ((K' : Set G').indicator 1) := by
  unfold clSum
  simp only [Pi.one_apply, one_mul]

  have hKK : ∀ k ∈ K.prod K', (θ.prodMap θ') k ∈ K.prod K' := fun k hk =>
    Subgroup.mem_prod.mpr ⟨hK _ (Subgroup.mem_prod.mp hk).1, hK' _ (Subgroup.mem_prod.mp hk).2⟩
  have hind : (((K.prod K' : Subgroup _) : Set (G × G')).indicator (1 : G × G' → ℂ)) =
      fun y => (K : Set G).indicator 1 y.1 * (K' : Set G').indicator 1 y.2 := by
    funext y
    by_cases h1 : y.1 ∈ K <;> by_cases h2 : y.2 ∈ K' <;>
      simp [Subgroup.mem_prod, h1, h2]
  have hfin : ∀ {H : Type} [Group H] (φ : H →* H) (L : Subgroup H) (hL : ∀ k ∈ L, φ k ∈ L) (T : Set H)
      (hT : ∀ y ∈ T, {q : DoubleCoset.Quotient (twCent φ y : Set H) (L : Set H) |
        (Quotient.out q)⁻¹ * y * φ (Quotient.out q) ∈ L}.Finite) (y : H), y ∈ T →
      {q : DoubleCoset.Quotient (twCent φ y : Set H) (L : Set H) |
        ∃ k ∈ L, (L : Set H).indicator (1 : H → ℂ) ((Quotient.out q * k)⁻¹ * y * φ (Quotient.out q * k)) ≠ 0}.Finite := by
    intro H _ φ L hL T hT y hy
    refine (hT y hy).subset ?_
    rintro q ⟨k, hk, hne⟩
    by_contra hq
    apply hne
    rw [Set.indicator_apply, if_neg]
    rw [SetLike.mem_coe, ind_conj φ L hL _ _ k hk]
    exact hq
  have hprod : ∀ p : TwCl θ × TwCl θ',
      (if (clsEquiv θ θ' p).rep ∈ {y : G × G' | y.1 ∈ S ∧ y.2 ∈ S'} then
        twOrb (θ.prodMap θ') (K.prod K') (clsEquiv θ θ' p).rep (((K.prod K' : Subgroup _) : Set _).indicator 1)
        else 0) =
      (if p.1.rep ∈ S then twOrb θ K p.1.rep ((K : Set G).indicator 1) else 0) *
      (if p.2.rep ∈ S' then twOrb θ' K' p.2.rep ((K' : Set G').indicator 1) else 0) := by
    intro p
    obtain ⟨g, hg⟩ := rep_mk (θ.prodMap θ') (p.1.rep, p.2.rep)
    have e : (clsEquiv θ θ' p).rep = g⁻¹ * (p.1.rep, p.2.rep) * (θ.prodMap θ') g := hg
    have hmem : g⁻¹ * (p.1.rep, p.2.rep) * (θ.prodMap θ') g ∈ {y : G × G' | y.1 ∈ S ∧ y.2 ∈ S'} ↔
        p.1.rep ∈ S ∧ p.2.rep ∈ S' := by
      show g.1⁻¹ * p.1.rep * θ g.1 ∈ S ∧ g.2⁻¹ * p.2.rep * θ' g.2 ∈ S' ↔ _
      rw [hS, hS']
    rw [e, GlobalTheory.TwOrbConj.twOrb_twConj (G × G') (θ.prodMap θ') (K.prod K') (p.1.rep, p.2.rep) g _
      (fun x => index_ne (θ.prodMap θ') (K.prod K') hKK _ x)]
    by_cases h1 : p.1.rep ∈ S <;> by_cases h2 : p.2.rep ∈ S'
    · simp only [hmem, h1, h2, and_self, if_true]
      rw [hind]
      exact GlobalTheory.T.twistedOrbitalIntegral_productGroup G G' θ θ' K K' _ _ _ _ (fun x => index_ne θ K hK _ x) (fun x => index_ne θ' K' hK' _ x)
        (hfin θ K hK S hd _ h1) (hfin θ' K' hK' S' hd' _ h2)
    · rw [if_neg fun h => h2 (hmem.mp h).2, if_neg h2, mul_zero]
    · rw [if_neg fun h => h1 (hmem.mp h).1, if_neg h1, zero_mul]
    · rw [if_neg fun h => h1 (hmem.mp h).1, if_neg h1, zero_mul]
  have hs1 : (Function.support fun c : TwCl θ =>
      if c.rep ∈ S then twOrb θ K c.rep ((K : Set G).indicator 1) else 0).Finite := by
    refine hf.subset fun c hc => ?_
    by_contra h
    apply hc
    change ¬ c.rep ∈ S at h
    simp [h]
  have hs2 : (Function.support fun c : TwCl θ' =>
      if c.rep ∈ S' then twOrb θ' K' c.rep ((K' : Set G').indicator 1) else 0).Finite := by
    refine hf'.subset fun c hc => ?_
    by_contra h
    apply hc
    change ¬ c.rep ∈ S' at h
    simp [h]
  rw [← finsum_comp_equiv (clsEquiv θ θ')]
  refine (finsum_congr hprod).trans ?_
  rw [finsum_curry _ ((hs1.prod hs2).subset fun p hp => ⟨left_ne_zero_of_mul hp, right_ne_zero_of_mul hp⟩),
    finsum_mul]
  refine finsum_congr fun c => ?_
  rw [mul_finsum]

theorem charpoly_nrmL_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (hE : Unr E) (n : ℕ) (w : Pl E)
    (g y : GLw n w) : (nrmL n w (g⁻¹ * y * thL n w g)).val.charpoly = (nrmL n w y).val.charpoly := by
  rw [GlobalTheory.BCT.ThBasic.nrmL_twist hE, Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' _ _

theorem stTw2_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (w : Pl E), ¬ IsSplitAt w → ∀ Q₁ Q₂ : (w.adicCompletion E)[X], Q₁.Separable → Q₂.Separable → stTw2 a b w Q₁ Q₂ ((((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) : Subgroup _) : Set _).indicator 1) = stTw a w Q₁ ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) * stTw b w Q₂ ((GlobalTheory.LFun.KGL w (n := b) : Set (GLw b w)).indicator 1) := by
  intro E _ _ _ hE a b w hw Q₁ Q₂ h₁ h₂
  unfold stTw2 stTw
  have hL : ∀ m : ℕ, IsLevel (thL m w) (GlobalTheory.LFun.KGL w (n := m)) (GlobalTheory.LFun.KGL w (n := m)) := by
    intro m
    unfold IsLevel
    exact ⟨(GlobalTheory.BCT.ThBasic.twist_basic E hE m w).2.2.2.2.1, le_rfl,
      fun k hk => GlobalTheory.BCT.ThBasic.thL_mem_KGL hE m w k hk⟩
  have hS : ∀ (m : ℕ) (Q : (w.adicCompletion E)[X]) (g y : GLw m w),
      g⁻¹ * y * thL m w g ∈ {y : GLw m w | (nrmL m w y).val.charpoly = Q} ↔
        y ∈ {y : GLw m w | (nrmL m w y).val.charpoly = Q} := by
    intro m Q g y
    show _ = Q ↔ _ = Q
    rw [charpoly_nrmL_conj hE]
  have hd : ∀ (m : ℕ) (Q : (w.adicCompletion E)[X]), Q.Separable →
      ∀ y ∈ {y : GLw m w | (nrmL m w y).val.charpoly = Q},
        {q : DoubleCoset.Quotient (twCent (thL m w) y : Set (GLw m w)) (GlobalTheory.LFun.KGL w (n := m) : Set (GLw m w)) |
          (Quotient.out q)⁻¹ * y * thL m w (Quotient.out q) ∈ GlobalTheory.LFun.KGL w (n := m)}.Finite := by
    intro m Q hQ y hy
    have hy' : (nrmL m w y).val.charpoly = Q := hy
    exact (GlobalTheory.T.regularTwistedOrbit_local_finiteness E hE m w y (hy' ▸ hQ) _ (hL m)).2 _ (GlobalTheory.BCT.ThBasic.twist_basic E hE m w).2.2.2.2.2.1
  exact clSum_prod (thL a w) (thL b w) _ _ _ _ (GlobalTheory.BCT.ThBasic.thL_mem_KGL hE a w)
    (GlobalTheory.BCT.ThBasic.thL_mem_KGL hE b w) (hS a Q₁) (hS b Q₂) (GlobalTheory.BCT.ClsFin.classes_finite E hE a w Q₁ h₁).1
    (GlobalTheory.BCT.ClsFin.classes_finite E hE b w Q₂ h₂).1 (hd a Q₁ h₁) (hd b Q₂ h₂)

end GlobalTheory.BCT.UnitProd
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem PositivityTheory.BcbA.Ties.unit_product_indicator_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (w : Pl E), ¬ IsSplitAt w → ∀ Q₁ Q₂ : (w.adicCompletion E)[X], Q₁.Separable → Q₂.Separable → stTw2 a b w Q₁ Q₂ ((((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) : Subgroup _) : Set _).indicator 1) = stTw a w Q₁ ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) * stTw b w Q₂ ((GlobalTheory.LFun.KGL w (n := b) : Set (GLw b w)).indicator 1) :=
  GlobalTheory.BCT.UnitProd.stTw2_unit
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

theorem PositivityTheory.Rg.Bc.ArchbcB.B.archimedean_base_change_first : PositivityTheory.Rg.Bc.ArchbcB.B.M1 := by
  intro E _ _ _ hE w hw n a b hab Q₁ Q₂ hm₁ hm₂ hd₁ hd₂ hsep hc₁ hc₂
  obtain ⟨K, e, he1, he2, he3, he4⟩ := GlobalTheory.T.exists_unramifiedQuadraticDatum_at_inertPlace E hE w hw
  have hs₁ : Q₁.Separable := hsep.of_mul_left
  have hs₂ : Q₂.Separable := hsep.of_mul_right
  obtain ⟨B₁, hg₁, hP₁, hst₁⟩ := GlobalTheory.T.inertPlace_stableTwistedOrbital_unit_eq_latticeSum E hE w hw K e he1 he2 he3 he4 a Q₁ hm₁ hd₁ hs₁ hc₁
  obtain ⟨B₂, hg₂, hP₂, hst₂⟩ := GlobalTheory.T.inertPlace_stableTwistedOrbital_unit_eq_latticeSum E hE w hw K e he1 he2 he3 he4 b Q₂ hm₂ hd₂ hs₂ hc₂
  have hk := GlobalTheory.T.inertPlace_kappaOrbital_unit_eq_signedLatticeSum E hE w hw K e he1 he2 he3 he4 n Q₁ Q₂ hm₁ hm₂ (by omega) hsep hc₁ hc₂ B₁ B₂ hg₁ hg₂ hP₁ hP₂
  have hsepP : (B₁.P * B₂.P).Separable := by
    rw [hP₁, hP₂, ← Polynomial.map_mul]
    exact hsep.map
  have hid := GlobalTheory.T.unitLemma_unramified_product_unitary_groups K B₁ B₂ hg₁ hg₂ hsepP
  unfold GlobalTheory.UnitLemma.InvAlg.Identity at hid
  have hv : GlobalTheory.UnitLemma.val K.O (resultant B₁.P B₂.P) = ordL (resultant Q₁ Q₂) := by
    rw [he3, hP₁, hP₂]
    have h1 : (Q₁.map e.symm.toRingHom).natDegree = Q₁.natDegree :=
      Polynomial.natDegree_map_eq_of_injective e.symm.injective _
    have h2 : (Q₂.map e.symm.toRingHom).natDegree = Q₂.natDegree :=
      Polynomial.natDegree_map_eq_of_injective e.symm.injective _
    rw [h1, h2, Polynomial.resultant_map_map]
    simp
  rw [PositivityTheory.BcbA.Ties.unit_product_indicator_twist E hE a b w hw Q₁ Q₂ hs₁ hs₂, hst₁, hst₂, hk, ← Rat.cast_mul, ← hid, Rat.cast_mul]
  congr 1
  rw [hv]
  unfold delta absHalf
  rw [if_neg hw, he4]
  set v := ordL (resultant Q₁ Q₂)
  have hq : Real.sqrt (((K.q ^ 2 : ℕ) : ℝ) ^ (-v)) = (K.q : ℝ) ^ (-v) := by
    rw [Nat.cast_pow, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast]
    exact Real.sqrt_sq (zpow_nonneg (Nat.cast_nonneg _) _)
  rw [hq]
  push_cast
  rw [neg_eq_neg_one_mul, mul_zpow, ← _root_.inv_zpow', inv_neg_one]

theorem PositivityTheory.Rg.Bc.ArchbcB.B.m1 : PositivityTheory.Rg.Bc.ArchbcB.B.M1 :=
  PositivityTheory.Rg.Bc.ArchbcB.B.archimedean_base_change_first

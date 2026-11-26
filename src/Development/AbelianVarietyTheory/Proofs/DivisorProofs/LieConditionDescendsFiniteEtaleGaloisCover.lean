module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineGaloisCoverDualNumberEpi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineGaloisCoverDualNumberEpi
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.DualCover

variable {A B : Type} [CommRing A] [CommRing B]

def dualMap (g : A →+* B) : DualNumber A →+* DualNumber B :=
  letI : Algebra A B := g.toAlgebra
  (DualNumber.lift ⟨(Algebra.ofId A (DualNumber B), DualNumber.eps), by simp, fun _ ↦ Commute.all _ _⟩).toRingHom

theorem dualMap_apply (g : A →+* B) (x : DualNumber A) :
    dualMap g x = TrivSqZeroExt.inl (g x.fst) + TrivSqZeroExt.inr (g x.snd) := by
  letI : Algebra A B := g.toAlgebra
  show (DualNumber.lift _ : DualNumber A →ₐ[A] DualNumber B) x = _
  rw [DualNumber.lift_apply_apply]
  ext <;> simp [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl', RingHom.algebraMap_toAlgebra]

@[simp] theorem dualMap_fst (g : A →+* B) (x : DualNumber A) : (dualMap g x).fst = g x.fst := by
  simp [dualMap_apply]

end GlobalTheory.DualCover

namespace GlobalTheory.DualCover
variable {A B : Type} [CommRing A] [CommRing B]

theorem isPushout_dualMap (g : A →+* B) :
    IsPushout (CommRingCat.ofHom (algebraMap A (DualNumber A))) (CommRingCat.ofHom g)
      (CommRingCat.ofHom (dualMap g)) (CommRingCat.ofHom (algebraMap B (DualNumber B))) := by
  letI : Algebra A B := g.toAlgebra
  have hc : ∀ a : A, dualMap g (algebraMap A (DualNumber A) a) = algebraMap A (DualNumber B) a := by
    intro a
    ext <;> simp [dualMap_apply, TrivSqZeroExt.algebraMap_eq_inl', RingHom.algebraMap_toAlgebra]
  let ψ₀ : DualNumber A →ₐ[A] DualNumber B := AlgHom.mk (dualMap g) hc
  have hψ₀ : ∀ x, ψ₀ x = dualMap g x := fun _ ↦ rfl
  let j : B →ₐ[A] DualNumber B := TrivSqZeroExt.inlAlgHom A B B
  let G : TensorProduct A (DualNumber A) B →ₐ[A] DualNumber B :=
    Algebra.TensorProduct.lift ψ₀ j (fun _ _ ↦ Commute.all _ _)
  let h : DualNumber B → TensorProduct A (DualNumber A) B := fun x ↦
    (1 : DualNumber A) ⊗ₜ[A] x.fst + (DualNumber.eps : DualNumber A) ⊗ₜ[A] x.snd
  have hadd : ∀ u v, h (u + v) = h u + h v := by
    intro u v
    simp only [h, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TensorProduct.tmul_add]
    abel
  have hgh : ∀ x, G (h x) = x := by
    intro x
    simp only [h, G, map_add (f := _), Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    ext <;> simp [j, hψ₀, dualMap_apply]
  have hhg : ∀ x, h (G x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [h]
    | tmul a b =>
      have e1 : a = TrivSqZeroExt.fst a • (1 : DualNumber A) + TrivSqZeroExt.snd a • DualNumber.eps := by
        ext <;> simp
      have f1 : TrivSqZeroExt.fst (ψ₀ a * j b) = TrivSqZeroExt.fst a • b := by
        simp [hψ₀, dualMap_apply, j, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      have f2 : TrivSqZeroExt.snd (ψ₀ a * j b) = TrivSqZeroExt.snd a • b := by
        simp [hψ₀, dualMap_apply, j, Algebra.smul_def, RingHom.algebraMap_toAlgebra, TrivSqZeroExt.algebraMap_eq_inl]
      show (1 : DualNumber A) ⊗ₜ[A] TrivSqZeroExt.fst (ψ₀ a * j b) +
        (DualNumber.eps : DualNumber A) ⊗ₜ[A] TrivSqZeroExt.snd (ψ₀ a * j b) = a ⊗ₜ[A] b
      rw [f1, f2, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul, ← e1]
    | add x y hx hy => rw [map_add (f := _), hadd, hx, hy]
  have hbij : Function.Bijective G := Function.bijective_iff_has_inverse.2 ⟨h, hhg, hgh⟩
  let eR : TensorProduct A (DualNumber A) B ≃+* DualNumber B := (AlgEquiv.ofBijective G hbij).toRingEquiv
  refine (CommRingCat.isPushout_tensorProduct A (DualNumber A) B).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    eR.toCommRingCatIso (by simp) (by ext; simp [RingHom.algebraMap_toAlgebra]) ?_ ?_
  · refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    show G (x ⊗ₜ[A] 1) = dualMap g x
    simp [G, hψ₀]
  · refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    show G (1 ⊗ₜ[A] x) = algebraMap B (DualNumber B) x
    simp [G, j, TrivSqZeroExt.algebraMap_eq_inl']

end GlobalTheory.DualCover

namespace GlobalTheory.DualCover

theorem epi_spMap_dualMap {X Y : Scheme.{0}} {π : X ⟶ Y} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)}
    (hG : GlobalTheory.ZM.IsGaloisCover Ga ρ π) {A B : Type} [CommRing A] [CommRing B] (g : A →+* B)
    (x : Sp A ⟶ Y) (x' : Sp B ⟶ X) (hsq : IsPullback (spMap g) x' x π) : Epi (spMap (dualMap g)) := by
  have h2 := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_dualMap g)
  have h3 : IsPullback (spMap (dualMap g)) (spMap (algebraMap B (DualNumber B)) ≫ x')
      (spMap (algebraMap A (DualNumber A)) ≫ x) π :=
    (IsPullback.paste_horiz h2.flip hsq.flip).flip
  have he := GlobalTheory.GaloisCartDesc.epi_pullback_fst hG (spMap (algebraMap A (DualNumber A)) ≫ x)
  rw [← h3.isoPullback_hom_fst]
  exact epi_comp _ _

theorem exists_dualCover : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ Y), ∃ (R'' : Type) (_ : CommRing R'') (g₁ : R' →+* R'') (x'' : Sp R'' ⟶ X) (d₁ : DualNumber R' →+* DualNumber R''), x'' ≫ π = spMap g₁ ≫ x ∧ d₁.comp (algebraMap R' (DualNumber R')) = (algebraMap R'' (DualNumber R'')).comp g₁ ∧ (TrivSqZeroExt.fstHom R'' R'' R'').toRingHom.comp d₁ = g₁.comp (TrivSqZeroExt.fstHom R' R' R').toRingHom ∧ (∀ r : R', d₁.comp (epsScaleR r) = (epsScaleR (g₁ r)).comp d₁) ∧ Epi (spMap d₁) := by
  intro X Y π Ga _ ρ hG R' _ x
  haveI : IsFinite π := hG.fin
  haveI : IsAffine (pullback x π) := isAffine_of_isAffineHom (pullback.fst x π)
  let X' := pullback x π
  let g₁ : R' →+* Γ(X', ⊤) := (Spec.preimage (X'.isoSpec.inv ≫ pullback.fst x π)).hom
  have hg₁ : spMap g₁ = X'.isoSpec.inv ≫ pullback.fst x π := Spec.map_preimage _
  let x'' : Sp Γ(X', ⊤) ⟶ X := X'.isoSpec.inv ≫ pullback.snd x π
  have hsq : IsPullback (spMap g₁) x'' x π := by
    rw [hg₁]
    exact IsPullback.of_iso_pullback ⟨by simp [x'', pullback.condition]⟩ X'.isoSpec.symm (by simp) (by simp [x''])
  refine ⟨Γ(X', ⊤), inferInstance, g₁, x'', dualMap g₁, hsq.w.symm, ?_, ?_, ?_, epi_spMap_dualMap hG g₁ x x'' hsq⟩
  · refine RingHom.ext fun a ↦ ?_
    ext <;> simp [dualMap_apply, TrivSqZeroExt.algebraMap_eq_inl']
  · refine RingHom.ext fun a ↦ ?_
    simp
  · intro r
    refine RingHom.ext fun a ↦ ?_
    ext <;> simp [epsScaleR, dualMap_apply] <;> ring

end GlobalTheory.DualCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineGaloisCoverDualNumberEpiStatement
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_galois_cover_dual_number_epi : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ Y), ∃ (R'' : Type) (_ : CommRing R'') (g₁ : R' →+* R'') (x'' : Sp R'' ⟶ X) (d₁ : DualNumber R' →+* DualNumber R''), x'' ≫ π = spMap g₁ ≫ x ∧ d₁.comp (algebraMap R' (DualNumber R')) = (algebraMap R'' (DualNumber R'')).comp g₁ ∧ (TrivSqZeroExt.fstHom R'' R'' R'').toRingHom.comp d₁ = g₁.comp (TrivSqZeroExt.fstHom R' R' R').toRingHom ∧ (∀ r : R', d₁.comp (epsScaleR r) = (epsScaleR (g₁ r)).comp d₁) ∧ Epi (spMap d₁) := by
  first | (exact @GlobalTheory.DualCover.exists_dualCover) | (exact GlobalTheory.DualCover.exists_dualCover) | (intros; apply GlobalTheory.DualCover.exists_dualCover  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTanScalIffOfLeftEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.HTPullTan

open GlobalTheory.UPel.HT

theorem isTanScal_iff_of_left_eq : ∀ {O : Type} [Ring O] {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] (f : S' ⟶ S) (φ : A'.left ⟶ A.left) (act : GlobalTheory.UPel.HT.OActN O A) (act' : GlobalTheory.UPel.HT.OActN O A'), IsGrpPullback A' A f φ → (∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) → ∀ {R' : Type} [CommRing R'] (x : Sp R' ⟶ S') (b : O) (c : R') (v : GlobalTheory.UPel.HT.epsPtR x ⟶ A') (v₀ : GlobalTheory.UPel.HT.epsPtR (x ≫ f) ⟶ A), v₀.left = v.left ≫ φ → (GlobalTheory.UPel.HT.IsTanScal act' x b c v ↔ GlobalTheory.UPel.HT.IsTanScal act (x ≫ f) b c v₀) := by
  intro O _ S S' A A' _ _ f φ a a' h hact R' _ x b c v v₀ hv₀
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ A).left = (1 : Over.mk x ⟶ A').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : spMap (epsScaleR c) ≫ spMap (algebraMap R' (DualNumber R')) = spMap (algebraMap R' (DualNumber R')) := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hR : ∀ (u w : epsPtR x ⟶ A') (u₀ w₀ : epsPtR (x ≫ f) ⟶ A), u₀.left = u.left ≫ φ → w₀.left = w.left ≫ φ →
      (u.left = spMap (epsScaleR c) ≫ w.left ↔
      u₀.left = spMap (epsScaleR c) ≫ w₀.left) := fun u w u₀ w₀ hu hw => by
    rw [hu, hw]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w w)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)
  refine and_congr ?_ ?_
  · rw [one, hv₀]
    refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
      fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
    refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ A')).symm
    refine (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
  · refine hR _ _ _ _ ?_ hv₀
    rw [Over.comp_left, Over.comp_left, hv₀, Category.assoc, Category.assoc, hact]

end GlobalTheory.HTPullTan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenProjectionsOfComaximal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenProjectionsOfComaximal
open scoped TensorProduct

namespace GlobalTheory

theorem eigenProjections_of_comaximal :
    ∀ (R F : Type) [CommRing R] [CommRing F] (a : ℕ) (t : Fin a → (F →+* R)),
      (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) →
      ∃ e : Fin a → R ⊗[ℤ] F, ∀ (M : Type) [AddCommGroup M] (Θ : R ⊗[ℤ] F →+* AddMonoid.End M)
        (i l : Fin a) (m : M), (∀ c : F, Θ (1 ⊗ₜ c) m = Θ (t l c ⊗ₜ 1) m) →
          Θ (e i) m = if i = l then m else 0 := by
  intro R F _ _ a t ht
  have hf : ∀ i j : Fin a, ∃ f : F →₀ R, i ≠ j → (f.sum fun c r => r * (t i c - t j c)) = 1 := by
    intro i j
    by_cases hij : i = j
    · exact ⟨0, fun h => (h hij).elim⟩
    · have h1 : (1 : R) ∈ Ideal.span (Set.range fun x => t i x - t j x) := by
        rw [ht i j hij]; trivial
      obtain ⟨f, hf⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h1
      exact ⟨f, fun _ => by simpa [smul_eq_mul] using hf⟩
  choose f hf using hf
  let χ : Fin a → (R ⊗[ℤ] F →ₐ[ℤ] R) := fun l =>
    Algebra.TensorProduct.productMap (AlgHom.id ℤ R) (t l).toIntAlgHom
  have hχ : ∀ l r c, χ l (r ⊗ₜ c) = r * t l c := by
    intro l r c; simp [χ, Algebra.TensorProduct.productMap_apply_tmul]
  refine ⟨fun i => ∏ j, if j = i then 1 else
    (f i j).sum fun c r => (r ⊗ₜ (1:F)) * ((1:R) ⊗ₜ c - t j c ⊗ₜ (1:F)), ?_⟩
  intro M _ Θ i l m hm
  have key : ∀ z, Θ z m = Θ (χ l z ⊗ₜ (1:F)) m := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r c =>
      have e1 : (r ⊗ₜ c : R ⊗[ℤ] F) = (r ⊗ₜ (1:F)) * ((1:R) ⊗ₜ c) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      have e2 : ((r * t l c) ⊗ₜ (1:F) : R ⊗[ℤ] F) = (r ⊗ₜ (1:F)) * (t l c ⊗ₜ (1:F)) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      rw [hχ, e1, e2, map_mul, map_mul]
      change Θ (r ⊗ₜ 1) (Θ (1 ⊗ₜ c) m) = Θ (r ⊗ₜ 1) (Θ (t l c ⊗ₜ 1) m)
      rw [hm c]
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), TensorProduct.add_tmul, map_add (f := _)]
      change Θ x m + Θ y m = Θ (χ l x ⊗ₜ 1) m + Θ (χ l y ⊗ₜ 1) m
      rw [hx, hy]
  rw [key, map_prod]
  split_ifs with hil
  · subst hil
    rw [Finset.prod_eq_one]
    · rw [← Algebra.TensorProduct.one_def, map_one]; rfl
    intro j _
    split_ifs with hji
    · exact map_one _
    · unfold Finsupp.sum
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      have := hf i j (Ne.symm hji)
      unfold Finsupp.sum at this
      refine Eq.trans ?_ this
      apply Finset.sum_congr rfl
      intro c _
      rw [map_mul, map_sub, hχ, hχ, hχ]
      simp
  · rw [Finset.prod_eq_zero (Finset.mem_univ l)]
    · rw [TensorProduct.zero_tmul, map_zero]; rfl
    rw [if_neg (Ne.symm hil)]
    unfold Finsupp.sum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    apply Finset.sum_eq_zero
    intro c _
    rw [map_mul, map_sub, hχ, hχ, hχ]
    simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenProjectionsOfComaximalStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigen_projections_tensor_of_comaximal : ∀ (R F : Type) [CommRing R] [CommRing F] (a : ℕ) (t : Fin a → (F →+* R)), (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → ∃ e : Fin a → R ⊗[ℤ] F, ∀ (M : Type) [AddCommGroup M] (Θ : R ⊗[ℤ] F →+* AddMonoid.End M) (i l : Fin a) (m : M), (∀ c : F, Θ (1 ⊗ₜ c) m = Θ (t l c ⊗ₜ 1) m) → Θ (e i) m = if i = l then m else 0 := by
  first | (exact @GlobalTheory.eigenProjections_of_comaximal) | (exact GlobalTheory.eigenProjections_of_comaximal) | (intros; apply GlobalTheory.eigenProjections_of_comaximal  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionDescendsFiniteEtaleGaloisCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LieGalDesc

section Help
variable {S : Scheme.{0}} {R₁ : Type} [CommRing R₁]

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]

theorem fst_comp_alg : (TrivSqZeroExt.fstHom R₁ R₁ R₁).toRingHom.comp (algebraMap R₁ (DualNumber R₁)) = RingHom.id R₁ :=
  RingHom.ext fun a => by simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem es_comp_alg (r : R₁) : (epsScaleR r).comp (algebraMap R₁ (DualNumber R₁)) = algebraMap R₁ (DualNumber R₁) :=
  RingHom.ext fun a => by ext <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_es (r : R₁) : (TrivSqZeroExt.fstHom R₁ R₁ R₁).toRingHom.comp (epsScaleR r) =
    (TrivSqZeroExt.fstHom R₁ R₁ R₁).toRingHom :=
  RingHom.ext fun a => by simp [epsScaleR]

theorem es_comp_es (r s : R₁) : (epsScaleR r).comp (epsScaleR s) = epsScaleR (r * s) :=
  RingHom.ext fun a => by ext <;> simp [epsScaleR] <;> ring

theorem es_one : epsScaleR (1 : R₁) = RingHom.id _ :=
  RingHom.ext fun a => by ext <;> simp [epsScaleR]

theorem es_zero : epsScaleR (0 : R₁) = (algebraMap R₁ (DualNumber R₁)).comp (TrivSqZeroExt.fstHom R₁ R₁ R₁).toRingHom :=
  RingHom.ext fun a => by ext <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

def zeroAt (y : Sp R₁ ⟶ S) : Over.mk y ⟶ epsPtR y :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R₁ R₁ R₁).toRingHom) (by
    show _ ≫ spMap _ ≫ y = y
    rw [← Category.assoc, spMap_comp', fst_comp_alg, spMap_id', Category.id_comp])

def baseAt (y : Sp R₁ ⟶ S) : epsPtR y ⟶ Over.mk y :=
  Over.homMk (spMap (algebraMap R₁ (DualNumber R₁))) rfl

def scaleAt (y : Sp R₁ ⟶ S) (r : R₁) : epsPtR y ⟶ epsPtR y :=
  Over.homMk (spMap (epsScaleR r)) (by
    show _ ≫ spMap _ ≫ y = spMap _ ≫ y
    rw [← Category.assoc, spMap_comp', es_comp_alg])

theorem zeroAt_scaleAt (y : Sp R₁ ⟶ S) (r : R₁) : zeroAt y ≫ scaleAt y r = zeroAt y :=
  Over.OverMorphism.ext (by
    show spMap _ ≫ spMap _ = spMap _
    rw [spMap_comp', fst_comp_es])

theorem scaleAt_mul (y : Sp R₁ ⟶ S) (r s : R₁) : scaleAt y r ≫ scaleAt y s = scaleAt y (r * s) :=
  Over.OverMorphism.ext (by
    show spMap _ ≫ spMap _ = spMap _
    rw [spMap_comp', es_comp_es])

theorem scaleAt_one (y : Sp R₁ ⟶ S) : scaleAt y 1 = 𝟙 _ :=
  Over.OverMorphism.ext (by
    show spMap _ = 𝟙 _
    rw [es_one, spMap_id'])

theorem scaleAt_zero (y : Sp R₁ ⟶ S) : scaleAt y 0 = baseAt y ≫ zeroAt y :=
  Over.OverMorphism.ext (by
    show spMap _ = spMap _ ≫ spMap _
    rw [spMap_comp', es_zero])

variable (G : Over S) [GrpObj G] [IsCommMonObj G]

def tan (y : Sp R₁ ⟶ S) : Subgroup (epsPtR y ⟶ G) where
  carrier := {u | zeroAt y ≫ u = 1}
  one_mem' := comp_one _
  mul_mem' {u u'} hu hu' := by
    simp only [Set.mem_setOf_eq] at *
    rw [comp_mul, hu, hu', _root_.one_mul]
  inv_mem' {u} hu := by
    simp only [Set.mem_setOf_eq] at *
    rw [GrpObj.comp_inv, hu, inv_one]

abbrev TM (y : Sp R₁ ⟶ S) := Additive (tan G y)

def scM (y : Sp R₁ ⟶ S) (r : R₁) : AddMonoid.End (TM G y) where
  toFun u := Additive.ofMul ⟨scaleAt y r ≫ (Additive.toMul u).1, by
    show zeroAt y ≫ scaleAt y r ≫ _ = 1
    rw [← Category.assoc, zeroAt_scaleAt]; exact (Additive.toMul u).2⟩
  map_zero' := Subtype.ext (comp_one _)
  map_add' u u' := Subtype.ext (comp_mul _ _ _)

def acM (y : Sp R₁ ⟶ S) (f : G ⟶ G) (hf : IsMonHom f) : AddMonoid.End (TM G y) where
  toFun u := Additive.ofMul ⟨(Additive.toMul u).1 ≫ f, by
    show zeroAt y ≫ _ ≫ f = 1
    rw [← Category.assoc, (Additive.toMul u).2, one_comp]⟩
  map_zero' := Subtype.ext (one_comp _)
  map_add' u u' := Subtype.ext (mul_comp _ _ _)

end Help

section Theta
variable {S : Scheme.{0}} {R₁ : Type} [CommRing R₁] (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem isTanScal_iff' {O : Type} [Ring O] (act : OActN O G) (y : Sp R₁ ⟶ S) (c : O) (r : R₁)
    (u : epsPtR y ⟶ G) : IsTanScal act y c r u ↔ zeroAt y ≫ u = 1 ∧ u ≫ act.act c = scaleAt y r ≫ u :=
  and_congr ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg Over.Hom.left h⟩
    ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg Over.Hom.left h⟩

theorem tan_left (y : Sp R₁ ⟶ S) (u : tan G y) :
    spMap (TrivSqZeroExt.fstHom R₁ R₁ R₁).toRingHom ≫ u.1.left = (1 : Over.mk y ⟶ G).left :=
  congrArg Over.Hom.left u.2

def phiR (y : Sp R₁ ⟶ S) : R₁ →+* AddMonoid.End (TM G y) where
  toFun := scM G y
  map_one' := AddMonoidHom.ext fun u => Subtype.ext (by
    show scaleAt y 1 ≫ _ = _
    rw [scaleAt_one, Category.id_comp]; rfl)
  map_mul' r s := AddMonoidHom.ext fun u => Subtype.ext (by
    show scaleAt y (r * s) ≫ _ = scaleAt y r ≫ scaleAt y s ≫ _
    rw [← Category.assoc, scaleAt_mul])
  map_zero' := AddMonoidHom.ext fun u => Subtype.ext (by
    show scaleAt y 0 ≫ _ = 1
    rw [scaleAt_zero, Category.assoc, (Additive.toMul u).2, comp_one])
  map_add' r s := AddMonoidHom.ext fun u => Subtype.ext (by
    show scaleAt y (r + s) ≫ _ = (scaleAt y r ≫ _) * (scaleAt y s ≫ _)
    exact Over.OverMorphism.ext ((GlobalTheory.T.grpObj_tangentVector_add_at_point G y _ (tan_left G y _) r s _ _ rfl rfl).symm))

def psiR {O : Type} [Ring O] (F : Type) [CommRing F] [Algebra F O] (act : OActN O G) (y : Sp R₁ ⟶ S) :
    F →+* AddMonoid.End (TM G y) where
  toFun c := acM G y (act.act (algebraMap F O c)) (act.hom _)
  map_one' := AddMonoidHom.ext fun u => Subtype.ext (by
    show _ ≫ act.act (algebraMap F O 1) = _
    rw [map_one, act.one, Category.comp_id]; rfl)
  map_mul' c d := AddMonoidHom.ext fun u => Subtype.ext (by
    show _ ≫ act.act (algebraMap F O (c * d)) = (_ ≫ act.act (algebraMap F O d)) ≫ act.act (algebraMap F O c)
    rw [map_mul, act.mul, Category.assoc])
  map_zero' := AddMonoidHom.ext fun u => Subtype.ext (by
    show _ ≫ act.act (algebraMap F O 0) = 1
    have h0 : act.act 0 = 1 := by
      have h := act.add 0 0
      rw [add_zero] at h
      exact (mul_left_cancel (a := act.act 0) (by rw [_root_.mul_one]; exact h)).symm
    rw [map_zero, h0, comp_one])
  map_add' c d := AddMonoidHom.ext fun u => Subtype.ext (by
    show _ ≫ act.act (algebraMap F O (c + d)) = (_ ≫ act.act (algebraMap F O c)) * (_ ≫ act.act (algebraMap F O d))
    rw [map_add (f := _), act.add, comp_mul])

def theta {O : Type} [Ring O] (F : Type) [CommRing F] [Algebra F O] (act : OActN O G) {R : Type} [CommRing R]
    (β₁ : R →+* R₁) (y : Sp R₁ ⟶ S) : R ⊗[ℤ] F →+* AddMonoid.End (TM G y) :=
  (Algebra.TensorProduct.lift ((phiR G y).comp β₁).toIntAlgHom (psiR G F act y).toIntAlgHom
    (fun r c => AddMonoidHom.ext fun u => Subtype.ext (by
      show scaleAt y (β₁ r) ≫ (_ ≫ _) = (scaleAt y (β₁ r) ≫ _) ≫ _
      exact (Category.assoc _ _ _).symm))).toRingHom

theorem theta_tmul {O : Type} [Ring O] (F : Type) [CommRing F] [Algebra F O] (act : OActN O G) {R : Type}
    [CommRing R] (β₁ : R →+* R₁) (y : Sp R₁ ⟶ S) (r : R) (c : F) :
    theta G F act β₁ y (r ⊗ₜ c) = phiR G y (β₁ r) * psiR G F act y c :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

def pullM {R₂ : Type} [CommRing R₂] (y : Sp R₁ ⟶ S) (y' : Sp R₂ ⟶ S) (j : epsPtR y' ⟶ epsPtR y)
    (g₀ : Over.mk y' ⟶ Over.mk y) (hj : zeroAt y' ≫ j = g₀ ≫ zeroAt y) : TM G y →+ TM G y' where
  toFun u := Additive.ofMul ⟨j ≫ (Additive.toMul u).1, by
    show zeroAt y' ≫ j ≫ _ = 1
    rw [← Category.assoc, hj, Category.assoc, (Additive.toMul u).2, comp_one]⟩
  map_zero' := Subtype.ext (comp_one _)
  map_add' u u' := Subtype.ext (comp_mul _ _ _)

theorem pullM_theta {O : Type} [Ring O] (F : Type) [CommRing F] [Algebra F O] (act : OActN O G) {R : Type}
    [CommRing R] (β₁ : R →+* R₁) {R₂ : Type} [CommRing R₂] (g₁ : R₁ →+* R₂) (y : Sp R₁ ⟶ S) (y' : Sp R₂ ⟶ S)
    (j : epsPtR y' ⟶ epsPtR y) (g₀ : Over.mk y' ⟶ Over.mk y) (hj : zeroAt y' ≫ j = g₀ ≫ zeroAt y)
    (hs : ∀ r, j ≫ scaleAt y r = scaleAt y' (g₁ r) ≫ j) (z : R ⊗[ℤ] F) (u : TM G y) :
    pullM G y y' j g₀ hj (theta G F act β₁ y z u) = theta G F act (g₁.comp β₁) y' z (pullM G y y' j g₀ hj u) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact map_zero _
  | tmul r c =>
    rw [theta_tmul, theta_tmul]
    apply Subtype.ext
    show j ≫ scaleAt y (β₁ r) ≫ (_ ≫ _) = scaleAt y' (g₁ (β₁ r)) ≫ (j ≫ _) ≫ _
    rw [← Category.assoc, hs, Category.assoc, Category.assoc]
  | add z z' hz hz' =>
    rw [map_add (f := _), map_add (f := _)]
    show pullM G y y' j g₀ hj (theta G F act β₁ y z u + theta G F act β₁ y z' u) =
      theta G F act (g₁.comp β₁) y' z (pullM G y y' j g₀ hj u) + theta G F act (g₁.comp β₁) y' z' (pullM G y y' j g₀ hj u)
    rw [map_add (f := _), hz, hz']

end Theta

theorem lie_descends : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ X), x ≫ (π ≫ sY) = spMap β → ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Y), x ≫ sY = spMap β → ∀ v : epsPtR x ⟶ A₀, IsTanScal act₀ x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A₀), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act₀ x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) := by
  intro p _ D R _ b X Y π sY Ga _ ρ A _ _ A₀ _ _ φ act act₀ hG _ _ hpb hact H R' _ β x hx v hv
  classical
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_eigen_projections_tensor_of_comaximal R (𝓞 D.F) D.a b.t b.comax
  obtain ⟨R'', _, g₁, x'', d₁, hsq, hdalg, hdfst, hdes, hepi⟩ := GlobalTheory.T.exists_affine_galois_cover_dual_number_epi X Y π Ga ρ hG R' x

  let j : epsPtR (x'' ≫ π) ⟶ epsPtR x := Over.homMk (spMap d₁) (by
    show spMap d₁ ≫ spMap _ ≫ x = spMap _ ≫ x'' ≫ π
    rw [hsq, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', hdalg])
  let g₀ : Over.mk (x'' ≫ π) ⟶ Over.mk x := Over.homMk (spMap g₁) hsq.symm
  have hj : zeroAt (x'' ≫ π) ≫ j = g₀ ≫ zeroAt x := Over.OverMorphism.ext (by
    show spMap _ ≫ spMap d₁ = spMap g₁ ≫ spMap _
    rw [spMap_comp', spMap_comp', hdfst])
  have hs : ∀ r, j ≫ scaleAt x r = scaleAt (x'' ≫ π) (g₁ r) ≫ j := fun r => Over.OverMorphism.ext (by
    show spMap d₁ ≫ spMap _ = spMap _ ≫ spMap d₁
    rw [spMap_comp', spMap_comp', hdes])
  have jinj : ∀ u u' : epsPtR x ⟶ A₀, j ≫ u = j ≫ u' → u = u' := fun u u' h =>
    Over.OverMorphism.ext ((cancel_epi (spMap d₁)).1 (congrArg Over.Hom.left h))
  let pj : (epsPtR x ⟶ A₀) →* (epsPtR (x'' ≫ π) ⟶ A₀) :=
    { toFun := fun u => j ≫ u, map_one' := comp_one _, map_mul' := fun u u' => comp_mul _ _ _ }

  have hv' := (isTanScal_iff' A₀ act₀ x _ _ v).1 hv
  let m : TM A₀ x := Additive.ofMul ⟨v, hv'.1⟩
  let Θ := theta A₀ (𝓞 D.F) act₀ β x
  let Θ' := theta A₀ (𝓞 D.F) act₀ (g₁.comp β) (x'' ≫ π)
  let P := pullM A₀ x (x'' ≫ π) j g₀ hj
  have hP : ∀ z u, P (Θ z u) = Θ' z (P u) := pullM_theta A₀ (𝓞 D.F) act₀ β g₁ x (x'' ≫ π) j g₀ hj hs
  let w : Fin D.a → (epsPtR x ⟶ A₀) := fun i => (Additive.toMul (Θ (e i) m)).1

  have hx'' : x'' ≫ (π ≫ sY) = spMap (g₁.comp β) := by
    rw [← Category.assoc, hsq, Category.assoc, hx, spMap_comp']
  obtain ⟨E, hE⟩ := GlobalTheory.LiePull.exists_pushEquiv hpb (epsPtR x'')
    (spMap (algebraMap R'' (DualNumber R'')) ≫ (x'' ≫ π)) (Category.assoc _ _ _).symm
  have key : ∀ (u : epsPtR x'' ⟶ A) (c : D.O) (r : R''), IsTanScal act x'' c r u ↔
      IsTanScal act₀ (x'' ≫ π) c r (E u) := fun u c r =>
    GlobalTheory.HTPullTan.isTanScal_iff_of_left_eq π φ act₀ act hpb hact x'' c r u (E u) (hE u)
  have hvj : IsTanScal act₀ (x'' ≫ π) (algebraMap (𝓞 D.F) D.O D.ω) ((g₁.comp β) b.ρ) (j ≫ v) := by
    refine (isTanScal_iff' A₀ act₀ _ _ _ _).2 ⟨(Additive.toMul (P m)).2, ?_⟩
    rw [Category.assoc, hv'.2, ← Category.assoc, hs, Category.assoc]
    rfl
  obtain ⟨w₃, hw₃, hprod⟩ := H R'' (g₁.comp β) x'' hx'' (E.symm (j ≫ v))
    ((key _ _ _).2 (by rw [MulEquiv.apply_symm_apply]; exact hvj))
  have eig : ∀ l c, E (w₃ l) ≫ act₀.act (algebraMap (𝓞 D.F) D.O c) =
      scaleAt (x'' ≫ π) (g₁ (β (b.t l c))) ≫ E (w₃ l) := fun l c =>
    ((isTanScal_iff' A₀ act₀ _ _ _ _).1 ((key _ _ _).1 (hw₃ l c))).2
  let m₃ : Fin D.a → TM A₀ (x'' ≫ π) := fun l =>
    Additive.ofMul ⟨E (w₃ l), ((isTanScal_iff' A₀ act₀ _ _ _ _).1 ((key _ _ _).1 (hw₃ l 1))).1⟩
  have hjv : j ≫ v = ∏ l, E (w₃ l) := by
    rw [← List.prod_ofFn]
    have h2 := congrArg E hprod
    rw [MulEquiv.apply_symm_apply, map_list_prod, List.map_ofFn] at h2
    exact h2
  have hPm : P m = ∑ l, m₃ l := by
    apply Additive.toMul.injective
    rw [toMul_sum]
    apply Subtype.ext
    change j ≫ v = (↑(∏ l, Additive.toMul (m₃ l)) : epsPtR (x'' ≫ π) ⟶ A₀)
    simpa [m₃] using hjv
  have eig₃ : ∀ l (c : 𝓞 D.F), Θ' (1 ⊗ₜ c) (m₃ l) = Θ' (b.t l c ⊗ₜ 1) (m₃ l) := fun l c => by
    rw [theta_tmul, theta_tmul]
    apply Subtype.ext
    show scaleAt (x'' ≫ π) ((g₁.comp β) 1) ≫ (E (w₃ l) ≫ act₀.act (algebraMap (𝓞 D.F) D.O c)) =
      scaleAt (x'' ≫ π) ((g₁.comp β) (b.t l c)) ≫ (E (w₃ l) ≫ act₀.act (algebraMap (𝓞 D.F) D.O 1))
    rw [map_one, scaleAt_one, Category.id_comp, map_one, act₀.one, Category.comp_id, eig]
    rfl
  have hw : ∀ i, j ≫ w i = E (w₃ i) := fun i => by
    have h1 : P (Θ (e i) m) = m₃ i := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hP, hPm, map_sum]
      simp only [he _ _ i _ _ (eig₃ _), Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact congrArg (fun z : TM A₀ (x'' ≫ π) => (Additive.toMul z).1) h1
  refine ⟨w, fun i c => ?_, ?_⟩
  · refine (isTanScal_iff' A₀ act₀ _ _ _ _).2 ⟨(Additive.toMul (Θ (e i) m)).2, jinj _ _ ?_⟩
    rw [← Category.assoc j (w i), hw, eig, ← Category.assoc j (scaleAt x _) (w i), hs, Category.assoc, hw]
  · refine jinj _ _ ?_
    show pj v = pj (List.ofFn w).prod
    rw [map_list_prod, List.map_ofFn, List.prod_ofFn]
    exact hjv.trans (Finset.prod_congr rfl fun i _ => (hw i).symm)

end GlobalTheory.LieGalDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionDescendsFiniteEtaleGaloisCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_condition_descends_finite_etale_galois_cover : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ X), x ≫ (π ≫ sY) = spMap β → ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Y), x ≫ sY = spMap β → ∀ v : epsPtR x ⟶ A₀, IsTanScal act₀ x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A₀), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act₀ x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) := by
  first | (exact @GlobalTheory.LieGalDesc.lie_descends) | (exact GlobalTheory.LieGalDesc.lie_descends) | (intros; apply GlobalTheory.LieGalDesc.lie_descends  <;> assumption)
end

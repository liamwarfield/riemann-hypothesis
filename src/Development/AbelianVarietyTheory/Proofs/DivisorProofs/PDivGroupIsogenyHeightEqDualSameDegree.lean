module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithAmbientVerticalOrArithmeticVariety
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureChartApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralLinearOfDensityEqSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingThetaConstantsGenerateIntegralTorsionLab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalExtendedBundleOfGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIsogenyHeightEqDualSameDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIsogenyHeightEqDualSameDegree
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

section Height

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

theorem finrank_level (G : PDivGroup p k) (n : ℕ) : Module.finrank k (G.A n) = p ^ (n * G.height) := by
  have h := G.rank_eq n ⟨⊥, Ideal.isPrime_bot⟩
  rwa [Module.rankAtStalk_eq_finrank_of_free] at h

theorem finrank_range_cartierDual_map {A B : Type} [CommRing A] [CommRing B] [HopfAlgebra k A]
    [HopfAlgebra k B] [Module.Finite k A] [Module.Finite k B] (f : B →ₐc[k] A) :
    Module.finrank k (LinearMap.range (CartierDual.map f : CartierDual k A →ₐ[k] CartierDual k B).toLinearMap) =
      Module.finrank k (LinearMap.range (f : B →ₐ[k] A).toLinearMap) := by
  have h : (CartierDual.map f : CartierDual k A →ₐ[k] CartierDual k B).toLinearMap =
      (CartierDual.toDual k B).symm.toLinearMap ∘ₗ
        ((f : B →ₐ[k] A).toLinearMap.dualMap ∘ₗ (CartierDual.toDual k A).toLinearMap) := rfl
  rw [h, LinearMap.range_comp, LinearEquiv.finrank_map_eq,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
    LinearMap.finrank_range_dualMap_eq_finrank_range]

theorem finrank_quot_mulBy (G : PDivGroup p k) {m n : ℕ} (h : m ≤ n) :
    Module.finrank k (G.A n ⧸ kerIdeal (mulBy k (G.A n) (p ^ m))) = p ^ (m * G.height) := by
  obtain ⟨f, hf, hk⟩ := G.exists_res_le h
  have hk' : kerIdeal (mulBy k (G.A n) (p ^ m)) = RingHom.ker (f : G.A n →ₐ[k] G.A m) := hk.symm
  rw [hk', (Ideal.quotientKerAlgEquivOfSurjective (f := (f : G.A n →ₐ[k] G.A m)) hf).toLinearEquiv.finrank_eq,
    finrank_level]

theorem height_le_of_comp_eq {G H : PDivGroup p k} (q : G ⟶ H) (g : H ⟶ G) (m : ℕ)
    (hqg : q ≫ g = (p : ℤ_[p]) ^ m • 𝟙 G) : G.height ≤ H.height := by
  have key : ∀ n, m ≤ n → p ^ (n * G.height) ≤ p ^ (m * G.height) * p ^ (n * H.height) := by
    intro n hn
    have hL := finrank_eq_ker_mul_range k (G.A n) (G.A n) (mulBy k (G.A n) (p ^ m))
    rw [finrank_quot_mulBy G hn, finrank_level] at hL
    have happ : (q ≫ g).app n = mulBy k (G.A n) (p ^ m) := by
      rw [hqg, ← Nat.cast_pow, natCast_smul_id_app]
    have hr : LinearMap.range ((mulBy k (G.A n) (p ^ m) : G.A n →ₐ[k] G.A n).toLinearMap) ≤
        LinearMap.range ((q.app n : H.A n →ₐ[k] G.A n).toLinearMap) := by
      rw [← happ]
      exact LinearMap.range_comp_le_range (g.app n : G.A n →ₐ[k] H.A n).toLinearMap
        (q.app n : H.A n →ₐ[k] G.A n).toLinearMap
    have h1 := Submodule.finrank_mono hr
    have h2 := LinearMap.finrank_range_le ((q.app n : H.A n →ₐ[k] G.A n).toLinearMap)
    rw [finrank_level] at h2
    rw [hL]
    exact Nat.mul_le_mul_left _ (h1.trans h2)
  by_contra hlt
  push_neg at hlt
  have h3 := key (m * G.height + m + 1) (by nlinarith)
  rw [← pow_add] at h3
  have h4 := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 h3
  nlinarith [Nat.mul_le_mul_left (m * G.height + m + 1) hlt]

theorem height_eq_and_dual_isog (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G H : PDivGroup p k) (q : G ⟶ H) (hq : IsIsog q) :
    G.height = H.height ∧ IsIsog (dualHom G H q) ∧ ∀ e, HasLogDeg q e → HasLogDeg (dualHom G H q) e := by
  obtain ⟨m, g, h1, h2⟩ := hq
  have hGH : G.height = H.height :=
    le_antisymm (height_le_of_comp_eq q g m h1) (height_le_of_comp_eq g q m h2)
  refine ⟨hGH, ⟨m, dualHom H G g, ?_, ?_⟩, ?_⟩
  · rw [← dualHom_comp, h2, map_smul, dualHom_id]
  · rw [← dualHom_comp, h1, map_smul, dualHom_id]
  · rintro e ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    have he := hN n hn
    have L1 := finrank_eq_ker_mul_range k (G.A n) (H.A n) (q.app n)
    have L2 := finrank_eq_ker_mul_range k (H.dual.A n) (G.dual.A n) ((dualHom G H q).app n)
    rw [he, finrank_level] at L1
    rw [finrank_level, dualHom_app, finrank_range_cartierDual_map] at L2
    have hr : 0 < Module.finrank k (LinearMap.range (q.app n : H.A n →ₐ[k] G.A n).toLinearMap) := by
      rcases Nat.eq_zero_or_pos (Module.finrank k (LinearMap.range (q.app n : H.A n →ₐ[k] G.A n).toLinearMap))
        with h0 | h0
      · rw [h0, mul_zero] at L1
        exact absurd L1 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
      · exact h0
    have L3 : p ^ (n * H.dual.height) = p ^ (n * G.height) := by rw [hGH]
    rw [L1, L2] at L3
    exact Nat.eq_of_mul_eq_mul_right hr L3

end Height

end GlobalTheory.Dieu
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIsogenyHeightEqDualSameDegreeStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q → G.height = H.height ∧ IsIsog (dualHom G H q) ∧ ∀ e, HasLogDeg q e → HasLogDeg (dualHom G H q) e := by
  first | exact @GlobalTheory.Dieu.height_eq_and_dual_isog | exact GlobalTheory.Dieu.height_eq_and_dual_isog | (intros; apply GlobalTheory.Dieu.height_eq_and_dual_isog <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelPartMulOfCoprimeAbelianVariety
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelPartMulOfCoprimeAbelianVariety
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.DeRham (spOver spOver_comp)
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerPart

theorem crt_split {G : Type} [CommGroup G] {a b : ℕ} {u v : ℤ} (huv : u * a + v * b = 1) (x : G)
    (hx : x ^ (a * b) = 1) : (x ^ (v * b)) ^ a = 1 ∧ (x ^ (u * a)) ^ b = 1 ∧ x ^ (v * b) * x ^ (u * a) = x := by
  have hx' : x ^ ((a : ℤ) * b) = 1 := by
    rw [← Nat.cast_mul, zpow_natCast, hx]
  refine ⟨?_, ?_, ?_⟩
  · rw [← zpow_natCast, ← zpow_mul, show v * (b : ℤ) * a = a * b * v by ring, zpow_mul, hx', one_zpow]
  · rw [← zpow_natCast, ← zpow_mul, show u * (a : ℤ) * b = a * b * u by ring, zpow_mul, hx', one_zpow]
  · rw [← zpow_add, show v * (b : ℤ) + u * a = 1 by linarith, zpow_one]

theorem crt_unique {G : Type} [CommGroup G] {a b : ℕ} {u v : ℤ} (huv : u * a + v * b = 1) {y₁ y₂ : G}
    (h₁ : y₁ ^ a = 1) (h₂ : y₂ ^ b = 1) : (y₁ * y₂) ^ (v * b) = y₁ ∧ (y₁ * y₂) ^ (u * a) = y₂ := by
  have h₁' : y₁ ^ (a : ℤ) = 1 := by rw [zpow_natCast, h₁]
  have h₂' : y₂ ^ (b : ℤ) = 1 := by rw [zpow_natCast, h₂]
  have e₁ : y₁ = y₁ ^ (u * a) * y₁ ^ (v * b) := by rw [← zpow_add, huv, zpow_one]
  have e₂ : y₂ = y₂ ^ (u * a) * y₂ ^ (v * b) := by rw [← zpow_add, huv, zpow_one]
  have a₁ : y₁ ^ (u * (a : ℤ)) = 1 := by rw [mul_comm, zpow_mul, h₁', one_zpow]
  have b₂ : y₂ ^ (v * (b : ℤ)) = 1 := by rw [mul_comm, zpow_mul, h₂', one_zpow]
  refine ⟨?_, ?_⟩
  · rw [mul_zpow, b₂, mul_one]
    conv_rhs => rw [e₁, a₁, one_mul]
  · rw [mul_zpow, a₁, one_mul]
    conv_rhs => rw [e₂, b₂, mul_one]

variable {k : Type} [Field k] {A B : AbVar k}

def postHom {T : Over (Sp k)} (f : A ⟶ B) : (T ⟶ A.X) →* (T ⟶ B.X) :=
  MonoidHom.mk' (fun x => x ≫ f.hom) fun x y => MonObj.mul_comp x y f.hom

theorem spMap_comp_left_iff {H R : Type} [CommRing H] [Algebra k H] [CommRing R] [Algebra k R] (φ : H →ₐ[k] R)
    (i : ptOver k H ⟶ A.X) (x : ptOver k R ⟶ A.X) : spMap φ.toRingHom ≫ i.left = x.left ↔ spOver φ ≫ i = x :=
  ⟨fun h => Over.OverMorphism.ext h, fun h => by subst h; rfl⟩

theorem kerPow_mul_of_coprime : ∀ (k : Type) [Field k] (A B : AbVar k) (f : A ⟶ B) (a b : ℕ), a.Coprime b →
    ∀ (H₁ : Type) [CommRing H₁] [Algebra k H₁] (i₁ : ptOver k H₁ ⟶ A.X) (H₂ : Type) [CommRing H₂] [Algebra k H₂]
    (i₂ : ptOver k H₂ ⟶ A.X), KerPow f a H₁ i₁ → KerPow f b H₂ i₂ → ∃ (H : Type) (_ : CommRing H)
    (_ : Algebra k H) (i : ptOver k H ⟶ A.X), KerPow f (a * b) H i ∧
      Module.finrank k H = Module.finrank k H₁ * Module.finrank k H₂ := by
  intro k _ A B f a b hab H₁ _ _ i₁ H₂ _ _ i₂ h₁ h₂
  obtain ⟨u, v, huv⟩ : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.2 hab
  let inl : H₁ →ₐ[k] H₁ ⊗[k] H₂ := Algebra.TensorProduct.includeLeft
  let inr : H₂ →ₐ[k] H₁ ⊗[k] H₂ := Algebra.TensorProduct.includeRight
  refine ⟨H₁ ⊗[k] H₂, inferInstance, inferInstance, (spOver inl ≫ i₁) * (spOver inr ≫ i₂),
    ⟨⟨?_, ?_⟩, ?_⟩, Module.finrank_tensorProduct⟩
  · rw [MonObj.mul_comp, Category.assoc, Category.assoc, h₁.1.1, h₂.1.1, MonObj.comp_one, MonObj.comp_one, mul_one]
  · rw [mul_pow, ← MonObj.comp_pow, ← MonObj.comp_pow, pow_mul, h₁.1.2, one_pow, mul_comm a b, pow_mul, h₂.1.2,
      one_pow, MonObj.comp_one, MonObj.comp_one, mul_one]
  · intro R _ _ x hx hxab
    obtain ⟨hx₁, hx₂, hx12⟩ := crt_split huv x hxab
    have hf : ∀ n : ℤ, (x ^ n) ≫ f.hom = 1 := fun n => by
      change postHom f (x ^ n) = 1
      rw [map_zpow]
      change (x ≫ f.hom) ^ n = 1
      rw [hx, one_zpow]
    obtain ⟨φ₁, hφ₁, hu₁⟩ := h₁.2 R _ (hf _) hx₁
    obtain ⟨φ₂, hφ₂, hu₂⟩ := h₂.2 R _ (hf _) hx₂
    rw [spMap_comp_left_iff] at hφ₁ hφ₂
    refine ⟨Algebra.TensorProduct.productMap φ₁ φ₂, ?_, fun ψ hψ => ?_⟩
    · refine (spMap_comp_left_iff _ _ _).2 ?_
      rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp]
      change spOver ((Algebra.TensorProduct.productMap φ₁ φ₂).comp Algebra.TensorProduct.includeLeft) ≫ i₁ *
        spOver ((Algebra.TensorProduct.productMap φ₁ φ₂).comp Algebra.TensorProduct.includeRight) ≫ i₂ = x
      rw [Algebra.TensorProduct.productMap_left, Algebra.TensorProduct.productMap_right, hφ₁, hφ₂, hx12]
    · replace hψ := (spMap_comp_left_iff _ _ _).1 hψ
      have hy : (spOver (ψ.comp inl) ≫ i₁) * (spOver (ψ.comp inr) ≫ i₂) = x := by
        rw [← spOver_comp, ← spOver_comp, Category.assoc, Category.assoc, ← MonObj.comp_mul]
        exact hψ
      have hy₁ : (spOver (ψ.comp inl) ≫ i₁) ^ a = 1 := by rw [← MonObj.comp_pow, h₁.1.2, MonObj.comp_one]
      have hy₂ : (spOver (ψ.comp inr) ≫ i₂) ^ b = 1 := by rw [← MonObj.comp_pow, h₂.1.2, MonObj.comp_one]
      obtain ⟨e₁, e₂⟩ := crt_unique huv hy₁ hy₂
      rw [hy] at e₁ e₂
      have k₁ : ψ.comp inl = φ₁ := hu₁ _ ((spMap_comp_left_iff _ _ _).2 e₁.symm)
      have k₂ : ψ.comp inr = φ₂ := hu₂ _ ((spMap_comp_left_iff _ _ _).2 e₂.symm)
      apply Algebra.TensorProduct.ext
      · rw [Algebra.TensorProduct.productMap_left]; exact k₁
      · exact k₂.trans (Algebra.TensorProduct.productMap_right φ₁ φ₂).symm

end GlobalTheory.AV.KerPart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelPartMulOfCoprimeAbelianVarietyStatement
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelPart_mul_of_coprime_abelianVariety : ∀ (k : Type) [Field k] (A B : AbVar k) (f : A ⟶ B) (a b : ℕ), a.Coprime b → ∀ (H₁ : Type) [CommRing H₁] [Algebra k H₁] (i₁ : ptOver k H₁ ⟶ A.X) (H₂ : Type) [CommRing H₂] [Algebra k H₂] (i₂ : ptOver k H₂ ⟶ A.X), KerPow f a H₁ i₁ → KerPow f b H₂ i₂ → ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X), KerPow f (a * b) H i ∧ Module.finrank k H = Module.finrank k H₁ * Module.finrank k H₂ := by
  first | exact @GlobalTheory.AV.KerPart.kerPow_mul_of_coprime | exact GlobalTheory.AV.KerPart.kerPow_mul_of_coprime | (intros; apply GlobalTheory.AV.KerPart.kerPow_mul_of_coprime; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegOneLeftCompSelf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassPullbackOfIsFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassPullbackOfIsFinite
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isAmpleCls_pull_of_isFinite : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (d : Pic B.X.left),
    IsFinite f.hom.left → IsAmpleCls d → IsAmpleCls (CechPic.pull f.hom.left d) := by
  intro K _ A B f d hf hd
  obtain ⟨L, hL, hrel, rfl⟩ := hd
  have hB : IsAmpleLB L := (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K B L hL).1 ⟨L, hL, hrel, rfl⟩
  have hA : IsAmpleLB (L.pull f.hom.left) := hB.pull_of_isAffineHom f.hom.left
  have h := (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K A (L.pull f.hom.left) hA.isLB).2 hA
  rwa [cls_pull hL f.hom.left hA.isLB] at h

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassPullbackOfIsFiniteStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianVarietyAmpleClass_pullback_of_isFinite : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (d : Pic B.X.left), IsFinite f.hom.left → IsAmpleCls d → IsAmpleCls (CechPic.pull f.hom.left d) := by
  first | exact @GlobalTheory.AV.AbVar.isAmpleCls_pull_of_isFinite | exact GlobalTheory.AV.AbVar.isAmpleCls_pull_of_isFinite | (intros; apply GlobalTheory.AV.AbVar.isAmpleCls_pull_of_isFinite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassAdd
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

theorem isAmpleCls_add : ∀ (K : Type) [Field K] (A : AbVar K) (c d : Pic A.X.left),
    IsAmpleCls c → IsAmpleCls d → IsAmpleCls (c + d) := by
  intro K _ A c d hc hd
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨M, hM, rfl⟩ := cls_surj d
  have hA : IsAmpleLB L := (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K A L hL).1 hc
  have hB : IsAmpleLB M := (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K A M hM).1 hd
  have hN : (tens L M).IsLB := isLB_tens hL hM
  have hT : IsAmpleLB (tens L M) := by
    refine hA.tensor hB hN ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hN hL) hM)).1 ?_)
    rw [cls_div (LB.isLB_div hN hL) hM, cls_div hN hL, cls_tens hL hM]
    abel
  rw [← cls_tens hL hM hN]
  exact (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K A (tens L M) hN).2 hT

end GlobalTheory.AV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassAddStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianVarietyAmpleClass_add : ∀ (K : Type) [Field K] (A : AbVar K) (c d : Pic A.X.left), IsAmpleCls c → IsAmpleCls d → IsAmpleCls (c + d) := by
  first | exact @GlobalTheory.AV.isAmpleCls_add | exact GlobalTheory.AV.isAmpleCls_add | (intros; apply GlobalTheory.AV.isAmpleCls_add <;> assumption)
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem neg_one_left_comp_self {K : Type} [Field K] (A : AbVar K) :
    (Hom.hom (-(𝟙 A))).left ≫ (Hom.hom (-(𝟙 A))).left = 𝟙 A.X.left := by
  have h : (-(𝟙 A)) ≫ (-(𝟙 A)) = 𝟙 A := by
    rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Category.id_comp]
  have h2 := congrArg (fun g : A ⟶ A => (Hom.hom g).left) h
  simpa only [comp_hom, Over.comp_left, id_hom, Over.id_left] using h2

theorem exists_symm_ample :
    ∀ (K : Type) [Field K] (A : AbVar K), ∃ c : Pic A.X.left, IsAmpleCls c ∧ CechPic.pull (Hom.hom (-(𝟙 A))).left c = c := by
  intro K _ A
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.T.abelianVariety_exists_ampleClass K A
  set f : A.X.left ⟶ A.X.left := (Hom.hom (-(𝟙 A))).left with hf
  have hff : f ≫ f = 𝟙 A.X.left := neg_one_left_comp_self A
  have hiso : IsIso f := ⟨⟨f, hff, hff⟩⟩
  have hfin : IsFinite (Hom.hom (-(𝟙 A))).left := by
    rw [← hf]; infer_instance
  refine ⟨c₀ + CechPic.pull f c₀, GlobalTheory.T.isAbelianVarietyAmpleClass_add K A _ _ hc₀ (GlobalTheory.T.isAbelianVarietyAmpleClass_pullback_of_isFinite K A A (-(𝟙 A)) c₀ hfin hc₀), ?_⟩
  rw [map_add (f := _), ← CechPic.pull_comp, hff, CechPic.pull_id, add_comm]

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableLogNormSectionMixedChernForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableLogNormSectionMixedChernForms
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory Metric
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixLogSec

theorem exists_integrableOn {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {D : ℕ} [SecondCountableTopology (CxPts p σ)] (hσ : Function.Injective σ) (L : Fin D → MLine p σ)
    (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (ε : ℤˣ) (c : AlgChart p σ D)
    {y : CxPts p σ} (hy : y ∈ c.e.source) :
    ∃ O ∈ 𝓝 y, IntegrableOn (M.logSec s) (ptsIn p σ (nonzeroLocus s) ∩ O) (part L ε) := by
  have : IsDomain k := hσ.isDomain σ
  set i := pick M.φ.isLB y
  have hi : y ∈ ptsIn p σ (M.B.U i) := mem_pick _ y
  have hT' := (isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (M.B.U i))).mem_nhds (mem_over c.e hy hi)
  have hd : ∀ᶠ v in 𝓝 (c.e y), DifferentiableAt ℂ (ev p σ _ (s.f i) ∘ c.e.symm) v :=
    (c.holo _ _).eventually_differentiableAt hT'
  have hfr : ∃ᶠ v in 𝓝 (c.e y), (ev p σ _ (s.f i) ∘ c.e.symm) v ≠ 0 := by
    have h := Measure.dense_of_ae (SemiPosBir.ae_mem hσ c (U := nonzeroLocus s) ⟨_, hs⟩)
    have h₁ := mem_closure_iff_frequently.1 (h (c.e y))
    refine (h₁.and_eventually hT').mono ?_
    rintro v ⟨h₂, h₃⟩
    exact (secVal_ne_zero_iff s h₃.2).2 (h₂ h₃.1)
  obtain ⟨δ, hδ, -, hint⟩ := exists_integrableOn_log_norm_of_frequently_ne_zero volume hd hfr
  obtain ⟨η, hη, hηs⟩ := nhds_basis_closedBall.mem_iff.1 (inter_mem hT' (ball_mem_nhds _ hδ))
  have hcont : ContinuousOn (fun v => dens L c (c.e.symm v)) c.e.target :=
    (GlobalTheory.T.continuousOn_mixedChernFormDensityInChart k X p σ D L c).comp c.e.continuousOn_symm c.e.mapsTo_symm
  obtain ⟨C, hC⟩ := (isCompact_closedBall (c.e y) η).exists_bound_of_continuousOn
    (hcont.mono fun v hv => (hηs hv).1.1)
  set O := c.e.source ∩ c.e ⁻¹' ball (c.e y) η
  have hO : IsOpen O := c.e.continuousOn.isOpen_inter_preimage c.e.open_source isOpen_ball
  set S := ptsIn p σ (nonzeroLocus s) ∩ O
  have hS : IsOpen S := (isOpen_ptsIn _).inter hO
  have hSs : S ⊆ c.e.source := fun z hz => hz.2.1
  have him : c.e '' S ⊆ closedBall (c.e y) η := by
    rintro _ ⟨z, hz, rfl⟩
    exact ball_subset_closedBall hz.2.2
  have hSi (z) (hz : z ∈ S) : z ∈ ptsIn p σ (M.B.U i) := by
    have := (hηs (him (mem_image_of_mem _ hz))).1.2
    rwa [mem_preimage, c.e.left_inv (hSs hz)] at this
  have hne (z) (hz : z ∈ S) : ev p σ _ (s.f i) z ≠ 0 := (secVal_ne_zero_iff s (hSi z hz)).2 hz.1
  have heq (z) (hz : z ∈ S) : M.logSec s z = Real.log ‖ev p σ _ (s.f i) z‖ - M.φ.φ i z / 2 := by
    rw [MLine.logSec, M.φ.nsq_eq (secVal_mem s) (hSi z hz), secVal_apply,
      Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 (hne z hz))) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp]
    push_cast
    ring
  have hm := measurableSet_image c.e hS.measurableSet hSs
  refine ⟨O, hO.mem_nhds ⟨hy, by exact Set.mem_preimage.mpr (mem_ball_self hη)⟩, LogNormInt.integrableOn_of_chart c.e
    (fun A hA hAs => GlobalTheory.T.mixedChernFormSignedPartMeasure_chart_apply k X p σ D L ε c A hA hAs) hS.measurableSet hSs
    (C := ENNReal.ofReal C) ENNReal.ofReal_ne_top (fun v hv => ENNReal.ofReal_le_ofReal ?_) ?_ ?_⟩
  · have h := hC v (him hv)
    rw [Real.norm_eq_abs, abs_le] at h
    rcases Int.units_eq_one_or ε with rfl | rfl
    · simpa using h.2
    · simpa [neg_le] using h.1
  · refine ContinuousOn.congr (fun z hz => ContinuousAt.continuousWithinAt ?_) heq
    exact ((((continuousOn_ev (s.f i)).continuousAt ((isOpen_ptsIn _).mem_nhds (hSi z hz))).norm.log
      (norm_ne_zero_iff.2 (hne z hz))).sub ((M.cInf i z (hSi z hz)).continuousAt.div_const 2))
  · have hsub : c.e '' S ⊆ ball (c.e y) δ := fun v hv => (hηs (him hv)).2
    have h₁ : IntegrableOn (fun v => (M.φ.φ i ∘ c.e.symm) v / 2) (c.e '' S) :=
      (((((contDiffOn_chart (M.cInf i) c).continuousOn.mono fun v hv => (hηs hv).1).div_const
        2).integrableOn_compact (isCompact_closedBall _ _)).mono_set him)
    refine ((hint.mono_set hsub).sub h₁).congr ?_
    filter_upwards [ae_restrict_mem hm] with v hv'
    obtain ⟨z, hz, rfl⟩ := hv'
    simp only [Function.comp_apply, Pi.sub_apply, c.e.left_inv (hSs hz)]
    exact (heq z hz).symm

theorem intg_logSec : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ (L : Fin D → MLine p σ) (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → Intg L (M.logSec s) := by
  intro F _ X _ _ p σ D hp hsm L M s hs
  have := CxPts.compactSpace σ hp
  have := CxPts.secondCountableTopology_of_isProjOver σ hp
  have key (ε : ℤˣ) : Integrable (M.logSec s) (part L ε) := by
    have h (y : CxPts p σ) : ∃ O ∈ 𝓝 y, IntegrableOn (M.logSec s) (ptsIn p σ (nonzeroLocus s) ∩ O) (part L ε) :=
      have ⟨c, hc⟩ := AlgChart.exists_mem_source (D := D) y
      exists_integrableOn σ.injective L M s hs ε c hc
    choose O hO hint using h
    obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover O fun y _ => hO y
    have h₁ : IntegrableOn (M.logSec s) (ptsIn p σ (nonzeroLocus s)) (part L ε) := by
      refine ((integrableOn_finset_iUnion (s := t)).2 fun y _ => hint y).mono_set fun z hz => ?_
      obtain ⟨y, hy, hz'⟩ := mem_iUnion₂.1 (ht (mem_univ z))
      exact mem_iUnion₂.2 ⟨y, hy, hz, hz'⟩
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (s := ptsIn p σ (nonzeroLocus s))
      (mem_ae_iff.2 (GlobalTheory.T.mixedChernFormSignedPartMeasure_compl_open_genericPoint_eq_zero F X p σ σ.injective hp D L ε _ hs))] at h₁
  exact ⟨key 1, key (-1)⟩

end GlobalTheory.MixLogSec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableLogNormSectionMixedChernFormsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_logNormSection_mixedChernForms : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ (L : Fin D → MLine p σ) (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → Intg L (M.logSec s) := by
  first | exact @GlobalTheory.MixLogSec.intg_logSec | exact GlobalTheory.MixLogSec.intg_logSec | (intros; apply GlobalTheory.MixLogSec.intg_logSec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneBaseChangeBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneBaseChangeBasis
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.Base


set_option maxHeartbeats 800000 in
theorem exists_mem_span_red_eq (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop)
    (B : Base p P) (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] [Algebra k k'] (G : PDivGroup p k) (hG : P k G) (hG' : P k' (G.baseChange k'))
    (ι : Type) (b : Module.Basis ι (WittVector p k) (B.M G hG)) (z : (G.baseChange k').RigExt) :
    ∃ n ∈ Submodule.span (WittVector p k') (Set.range fun i => B.smap hG' hG (G.toBase k') (b i)),
      B.red _ hG' n = z := by
  obtain ⟨x, rfl⟩ := G.liftSemi_rig_bijective k' (CharP.cast_eq_zero k p) (.inl inferInstance) |>.2 z
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    obtain ⟨n, hn, h1⟩ := hx
    obtain ⟨n', hn', h2⟩ := hy
    refine ⟨n + n', add_mem hn hn', ?_⟩
    rw [LinearMap.map_add (B.red _ hG') n n', h1, h2, LinearMap.map_add (f := _)]
  | tmul r y =>
    obtain ⟨m, rfl⟩ := B.red_surjective G hG y
    obtain ⟨R, rfl⟩ := (WittVector.constantCoeff_surjective p : Function.Surjective
      (WittVector.constantCoeff : WittVector p k' →+* k')) r
    refine ⟨R • B.smap hG' hG (G.toBase k') m, Submodule.smul_mem _ _ ?_, ?_⟩
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.linearCombination_repr m, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
      exact Submodule.sum_mem _ fun i _ => by
        rw [B.smap_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · set_option backward.isDefEq.respectTransparency false in
      rw [liftSemi_tmul, LinearMap.map_smulₛₗ (B.red _ hG') R, B.red_smap]

set_option synthInstance.maxHeartbeats 200000 in
theorem smap_toBase_basis (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop)
    (B : Base p P) (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] [Algebra k k'] (G : PDivGroup p k) (hG : P k G) (hG' : P k' (G.baseChange k'))
    (ι : Type) [Fintype ι] (b : Module.Basis ι (WittVector p k) (B.M G hG)) :
    ∃ b' : Module.Basis ι (WittVector p k') (B.M (G.baseChange k') hG'),
      ∀ i, b' i = B.smap hG' hG (G.toBase k') (b i) := by
  have := B.free G hG
  have := B.finite G hG
  have := B.free _ hG'
  have := B.finite _ hG'
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  have hp' : (p : k') = 0 := CharP.cast_eq_zero k' p
  obtain ⟨-, hr⟩ := finrank_eq_of_semilinear_surjective (WittVector.constantCoeff_surjective p) hp
    (B.red G hG) (B.red_surjective G hG) fun m h => (B.red_eq_zero G hG m).1 h
  obtain ⟨-, hr'⟩ := finrank_eq_of_semilinear_surjective (WittVector.constantCoeff_surjective p) hp'
    (B.red _ hG') (B.red_surjective _ hG') fun m h => (B.red_eq_zero _ hG' m).1 h
  change Module.finrank k G.RigExt = _ at hr
  change Module.finrank k' (G.baseChange k').RigExt = _ at hr'
  have hrank : Module.finrank k' (G.baseChange k').RigExt = Module.finrank k G.RigExt := by
    rw [← (LinearEquiv.ofBijective _ (G.liftSemi_rig_bijective k' hp (.inl inferInstance))).finrank_eq,
      Module.finrank_baseChange]
  have hmax : (p : WittVector p k') ∈ IsLocalRing.maximalIdeal (WittVector p k') := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map (WittVector.constantCoeff : WittVector p k' →+* k')
    rw [map_natCast, hp'] at this
    exact not_isUnit_zero this
  have hjac : Ideal.span {(p : WittVector p k')} ≤ Ring.jacobson (WittVector p k') := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact Ideal.span_le.2 (Set.singleton_subset_iff.2 hmax)
  have hspan : ⊤ ≤ Submodule.span (WittVector p k')
      (Set.range fun i => B.smap hG' hG (G.toBase k') (b i)) := by
    refine Submodule.le_of_le_smul_of_le_jacobson Module.Finite.fg_top hjac fun m _ => ?_
    obtain ⟨n, hn, h1⟩ := exists_mem_span_red_eq p P B k k' G hG hG' ι b (B.red _ hG' m)
    obtain ⟨q, hq⟩ := (B.red_eq_zero _ hG' (m - n)).1 (by
      rw [LinearMap.map_sub (B.red _ hG') m n, h1, sub_self])
    have hm : m = n + (p : WittVector p k') • q := by
      rw [← Nat.cast_smul_eq_nsmul (WittVector p k')] at hq
      rw [← hq, add_sub_cancel]
    rw [hm]
    exact Submodule.add_mem_sup hn (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _)
      Submodule.mem_top)
  have hcard : Fintype.card ι = Module.finrank (WittVector p k') (B.M (G.baseChange k') hG') := by
    rw [← hr', hrank, hr, Module.finrank_eq_card_basis b]
  exact ⟨Module.Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank hspan hcard) hspan,
    fun i => Module.Basis.mk_apply _ _ i⟩

end GlobalTheory.Dieu.Base
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneBaseChangeBasisStatement
open GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dieudonne_baseChange_basis :
    ∀ (p : ℕ) [Fact p.Prime]
      (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop)
      (B : Dieu.Base p P) (k k' : Type)
      [Field k] [CharP k p] [PerfectRing k p]
      [Field k'] [CharP k' p] [PerfectRing k' p] [Algebra k k']
      (G : PDivGroup p k) (hG : P k G) (hG' : P k' (G.baseChange k'))
      (ι : Type) [Fintype ι] (b : Module.Basis ι (WittVector p k) (B.M G hG)),
      ∃ b' : Module.Basis ι (WittVector p k') (B.M (G.baseChange k') hG'),
        ∀ i, b' i = B.smap hG' hG (G.toBase k') (b i) :=
  @GlobalTheory.Dieu.Base.smap_toBase_basis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralLinearRelationZero
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ChernLinRel

theorem restrict_finsetSum {α : Type} [MeasurableSpace α] {J : Type} (s : Finset J) (ν : J → Measure α) (S : Set α) :
    (∑ j ∈ s, ν j).restrict S = ∑ j ∈ s, (ν j).restrict S := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.restrict_add, ih]

end GlobalTheory.ChernLinRel


open GlobalTheory.ChernLinRel in
theorem GlobalTheory.ChernLinRel.sum_chernInt_eq_zero : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (σ : k →+* ℂ) (D : ℕ) (J : Type) [Fintype J] (a : J → ℝ) (N : J → HermLB p), (∀ (c : AlgChart p σ D), ∀ y ∈ c.e.source, ∑ j, a j * c.chernDens ((N j).φ σ) y = 0) → ∀ (S : Set (CxPts p σ)) (g : CxPts p σ → ℝ), (∀ j, ((N j).φ σ).ChernIntegrableOn D S g) → ∑ j, a j * ((N j).φ σ).chernInt D S g = 0 := by
  intro k _ X p hp σ D J _ a N hlin S g hint
  classical
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hp
  set P : J → ℤˣ → Measure (CxPts p σ) := fun j ε => ((N j).φ σ).chernPart D ε with hPdef
  let ap : J → ℝ := fun j => max (a j) 0
  let an : J → ℝ := fun j => max (-a j) 0
  let μ : (J → ℝ) → (J → ℝ) → Measure (CxPts p σ) := fun u w =>
    ∑ j, (ENNReal.ofReal (u j) • P j 1 + ENNReal.ofReal (w j) • P j (-1))

  have hcont : ∀ j (c : AlgChart p σ D), ContinuousOn (fun v => c.chernDens ((N j).φ σ) (c.e.symm v)) c.e.target :=
    fun j c => continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      ((Continuous.matrix_det continuous_id).comp_continuousOn
        ((GlobalTheory.MixDens.chernMat_isForm k X p σ D _ ((N j).φ σ) ((N j).cInf σ)).2.1 c)))

  have hchart : ∀ (u w : J → ℝ) (c : AlgChart p σ D) (A : Set (CxPts p σ)), MeasurableSet A → A ⊆ c.e.source →
      μ u w A = ∫⁻ v in c.e '' A, ∑ j, (ENNReal.ofReal (u j) * ENNReal.ofReal (1 * c.chernDens ((N j).φ σ) (c.e.symm v)) +
        ENNReal.ofReal (w j) * ENNReal.ofReal (-1 * c.chernDens ((N j).φ σ) (c.e.symm v))) := by
    intro u w c A hA hAc
    have hsub : c.e '' A ⊆ c.e.target := fun _ ⟨y, hy, e⟩ => e ▸ c.e.map_source (hAc hy)
    have hm : ∀ j (s : ℝ), AEMeasurable (fun v => ENNReal.ofReal (s * c.chernDens ((N j).φ σ) (c.e.symm v)))
        (volume.restrict (c.e '' A)) := fun j s =>
      ((((hcont j c).aemeasurable c.e.open_target.measurableSet).const_mul s).ennreal_ofReal).mono_measure
        (Measure.restrict_mono hsub le_rfl)
    have hP : ∀ j (ε : ℤˣ), P j ε A = ∫⁻ v in c.e '' A, ENNReal.ofReal ((ε : ℤ) * c.chernDens ((N j).φ σ) (c.e.symm v)) :=
      fun j ε => Weight.chernPart_apply ((N j).cInf σ) ε c hA hAc
    have hm2 : ∀ j ∈ (Finset.univ : Finset J), AEMeasurable (fun v => ENNReal.ofReal (u j) * ENNReal.ofReal (1 * c.chernDens ((N j).φ σ) (c.e.symm v)) +
        ENNReal.ofReal (w j) * ENNReal.ofReal (-1 * c.chernDens ((N j).φ σ) (c.e.symm v))) (volume.restrict (c.e '' A)) :=
      fun j _ => ((hm j 1).const_mul _).add ((hm j (-1)).const_mul _)
    rw [lintegral_finsetSum' _ hm2]
    simp only [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [lintegral_add_left' ((hm j 1).const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hP, hP]
    simp

  set U : Set (CxPts p σ) := ⋃ c : AlgChart p σ D, c.e.source with hUdef
  have hUo : IsOpen U := isOpen_iUnion fun c => c.e.open_source
  have hzero : ∀ u w : J → ℝ, μ u w Uᶜ = 0 := by
    intro u w
    have h0 : ∀ j (ε : ℤˣ), P j ε Uᶜ = 0 := fun j ε =>
      Weight.chernPart_eq_zero ε hUo.measurableSet.compl fun c =>
        Set.disjoint_compl_right_iff_subset.2 (Set.subset_iUnion (fun c : AlgChart p σ D => c.e.source) c)
    simp [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.add_apply, Measure.smul_apply, h0]

  have hbal : μ ap an = μ an ap := by
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable (fun c : AlgChart p σ D => c.e.source)
      fun c => c.e.open_source
    let s : Option (AlgChart p σ D) → Set (CxPts p σ) := fun o => o.elim Uᶜ fun c => c.e.source
    refine Measure.ext_of_biUnion_eq_univ (S := insert none (some '' T)) (s := s) ((hTc.image _).insert _) ?_ ?_
    · refine Set.eq_univ_of_forall fun y => ?_
      by_cases hy : y ∈ U
      · rw [hUdef, ← hT] at hy
        obtain ⟨c, hc, hyc⟩ := Set.mem_iUnion₂.1 hy
        exact Set.mem_iUnion₂.2 ⟨some c, Set.mem_insert_of_mem _ ⟨c, hc, rfl⟩, hyc⟩
      · exact Set.mem_iUnion₂.2 ⟨none, Set.mem_insert _ _, hy⟩
    · rintro (_ | c) -
      · show (μ ap an).restrict Uᶜ = (μ an ap).restrict Uᶜ
        rw [Measure.restrict_eq_zero.2 (hzero _ _), Measure.restrict_eq_zero.2 (hzero _ _)]
      · show (μ ap an).restrict c.e.source = (μ an ap).restrict c.e.source
        ext B hB
        have hBs := hB.inter c.e.open_source.measurableSet
        rw [Measure.restrict_apply hB, Measure.restrict_apply hB, hchart _ _ c _ hBs Set.inter_subset_right,
          hchart _ _ c _ hBs Set.inter_subset_right]
        refine setLIntegral_congr_fun (GlobalTheory.ChartGlue.measurableSet_image _ hBs Set.inter_subset_right) fun v hv => ?_
        obtain ⟨y, hy, rfl⟩ := hv
        have h0 := hlin c (c.e.symm (c.e y)) (c.e.map_target (c.e.map_source hy.2))
        have := GlobalTheory.GoodMetric.ChernLin.ofReal_balance a fun j => c.chernDens ((N j).φ σ) (c.e.symm (c.e y))
        rw [h0, mul_zero, mul_zero, ENNReal.ofReal_zero, zero_add, zero_add] at this
        exact this.symm

  have hI : ∀ u w : J → ℝ, (∀ j, 0 ≤ u j) → (∀ j, 0 ≤ w j) → ∫ y in S, g y ∂μ u w =
      ∑ j, (u j * ∫ y in S, g y ∂P j 1 + w j * ∫ y in S, g y ∂P j (-1)) := by
    intro u w hu hw
    simp only [μ, restrict_finsetSum, Measure.restrict_add, Measure.restrict_smul]
    rw [integral_finsetSum_measure fun j _ => ((hint j).1.smul_measure ENNReal.ofReal_ne_top).add_measure
      ((hint j).2.smul_measure ENNReal.ofReal_ne_top)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_add_measure ((hint j).1.smul_measure ENNReal.ofReal_ne_top)
      ((hint j).2.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
      ENNReal.toReal_ofReal (hu j), ENNReal.toReal_ofReal (hw j), smul_eq_mul, smul_eq_mul]
  have e := congrArg (fun m : Measure (CxPts p σ) => ∫ y in S, g y ∂m) hbal
  rw [hI _ _ (fun j => le_max_right _ _) (fun j => le_max_right _ _),
    hI _ _ (fun j => le_max_right _ _) (fun j => le_max_right _ _)] at e
  have key : ∑ j, a j * ((N j).φ σ).chernInt D S g =
      ∑ j, (ap j * ∫ y in S, g y ∂P j 1 + an j * ∫ y in S, g y ∂P j (-1)) -
      ∑ j, (an j * ∫ y in S, g y ∂P j 1 + ap j * ∫ y in S, g y ∂P j (-1)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have ha : ap j - an j = a j := GlobalTheory.GoodMetric.ChernLin.max_sub_max_neg (a j)
    rw [Weight.chernInt]
    simp only [P]
    linear_combination (-(∫ y in S, g y ∂((N j).φ σ).chernPart D 1) + ∫ y in S, g y ∂((N j).φ σ).chernPart D (-1)) * ha
  rw [key, e, sub_self]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistWeightWellDefinedOnLatticeClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistWeightWellDefinedOnLatticeClass
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep.WtWd

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem qkSub : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Y) (𝔪 : UMem X₁ z₁ act V ev Y t δ) (p p' : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N)) (x x' : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), p.y = p'.y → QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p x → QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p' x' → ∃ q : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N), q.y = 0 ∧ QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) q (x * x'⁻¹) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev Y _ m t δ 𝔪 p p' x x' hp hx hx'
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    obtain ⟨j, -, hj⟩ := X₁.ρ.r_eq
    have hn := X₁.ρ.n_prime.pos
    rw [hj, X₁.ρ.N_eq]
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  have hB := 𝔪.D.tau_bimult
  obtain ⟨f, hto, -, -, hadd, -⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk
  have e := (hto p x).1 hx
  have e' := (hto p' x').1 hx'
  have h0 : f (GlobalTheory.TorusExt.qkZero hB _ _) = 1 := by
    have := hadd _ _ _ (GlobalTheory.TorusExt.qkAdd_qkAdd hB (GlobalTheory.TorusExt.qkZero hB (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N))
      (GlobalTheory.TorusExt.qkZero hB _ _))
    rw [show GlobalTheory.TorusExt.qkAdd hB (GlobalTheory.TorusExt.qkZero hB (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N))
        (GlobalTheory.TorusExt.qkZero hB _ _) = GlobalTheory.TorusExt.qkZero hB _ _ from
      GlobalTheory.TorusExt.qk_ext (by simp [GlobalTheory.TorusExt.qkAdd, GlobalTheory.TorusExt.qkZero]) (by simp [GlobalTheory.TorusExt.qkAdd, GlobalTheory.TorusExt.qkZero])] at this
    exact left_eq_mul.1 this
  have hneg : f (GlobalTheory.TorusExt.qkNeg hB p') = (f p')⁻¹ := by
    have := hadd _ _ _ (GlobalTheory.TorusExt.qkAdd_qkAdd hB p' (GlobalTheory.TorusExt.qkNeg hB p'))
    rw [show GlobalTheory.TorusExt.qkAdd hB p' (GlobalTheory.TorusExt.qkNeg hB p') = GlobalTheory.TorusExt.qkZero hB _ _ from
      GlobalTheory.TorusExt.qk_ext (by simp [GlobalTheory.TorusExt.qkAdd, GlobalTheory.TorusExt.qkNeg, GlobalTheory.TorusExt.qkZero])
        (by simp [GlobalTheory.TorusExt.qkAdd, GlobalTheory.TorusExt.qkNeg, GlobalTheory.TorusExt.qkZero]), h0] at this
    exact (eq_inv_of_mul_eq_one_right this.symm)
  refine ⟨GlobalTheory.TorusExt.qkAdd hB p (GlobalTheory.TorusExt.qkNeg hB p'), ?_, ?_⟩
  · simp [GlobalTheory.TorusExt.qkAdd, GlobalTheory.TorusExt.qkNeg, hp]
  · rw [hto, hadd _ _ _ (GlobalTheory.TorusExt.qkAdd_qkAdd hB _ _), hneg, e, e']

section
variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {Y : Type} [AddCommGroup Y] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ Y} (𝔪 : UMem X₁ z₁ act V ev Y t δ)

theorem yy_sub {a a' : X₁.S.Gam} {mu : Fin 8 → Y} (h : 𝔪.YY a mu) (h' : 𝔪.YY a' mu) : 𝔪.YY (a - a') 0 := by
  obtain ⟨p, x, hp, hx, hxa⟩ := h
  obtain ⟨p', x', hp', hx', hxa'⟩ := h'
  obtain ⟨q, hq, hqx⟩ := qkSub g n F W Z i X₁ z₁ act V ev Y m t δ 𝔪 p p' x x' (hp.trans hp'.symm) hx hx'
  refine ⟨q, x * x'⁻¹, by rw [hq, map_zero], hqx, ?_⟩
  let T := TFK (R := V) (AlgebraicClosure (FractionRing V))
  have e2 : spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) =
      T.hom ≫ spMap 𝔪.yK := by
    simp [T, spMap, jFK, ← Spec.map_comp]
  let U : Over.mk (T.hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) := Over.homMk (T.hom ≫ spMap 𝔪.yK) (by simp)
  have hU : ∀ (b : X₁.S.Gam) (y : T ⟶ 𝔪.A.A),
      y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt b).left →
      pushHom 𝔪.cart T y = U ≫ X₁.ρ.pt b := fun b y hy => by
    apply Over.OverMorphism.ext
    show y.left ≫ 𝔪.φ = (U ≫ X₁.ρ.pt b).left
    rw [Over.comp_left, hy, e2]
    rfl
  have hpt : X₁.ρ.pt (a - a') = X₁.ρ.pt a * (X₁.ρ.pt a')⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ← X₁.ρ.pt_add, sub_add_cancel]
  have key : pushHom 𝔪.cart T (x * x'⁻¹) = U ≫ X₁.ρ.pt (a - a') := by
    rw [map_mul, map_inv, hU a x hxa, hU a' x' hxa', hpt]
    show _ = preHom U _
    rw [map_mul, map_inv]
    rfl
  have e3 := congrArg (fun z => z.left) key
  rw [e2]
  exact e3.trans (Over.comp_left _ _ _ U _)

end

theorem wt_wd : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (sg : ℤˣ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ wt : (Fin 8 → Y1) → ZMod (X₁.S.r * X₁.S.N), ∀ a mu, 𝔪1.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a := by
  intro g n F W Z i X₁ z₁ act x₀ hD V1 _ _ _ ev1 Y1 _ m1 t1 δ1 𝔪1 sg τ hτ
  classical
  refine ⟨fun mu => if h : ∃ a, 𝔪1.YY a mu then (sg : ℤ) • eStd X₁.S.g _ τ h.choose else 0, ?_⟩
  intro a mu hY
  have h : ∃ a, 𝔪1.YY a mu := ⟨a, hY⟩
  simp only [dif_pos h]
  congr 1
  have hd := yy_sub 𝔪1 h.choose_spec hY
  have hH : h.choose - a ∈ X₁.S.HH X₁.M z₁ :=
    (GlobalTheory.T.dividingThetaConstants_generate_integral_torsion_labels g n F W Z i X₁ z₁ act x₀ hD V1 ev1 Y1 m1 t1 δ1 𝔪1 _).2 hd
  have h0 : eStd X₁.S.g _ τ (h.choose - a) = 0 := hτ _ hH
  have hs : eStd X₁.S.g _ τ (h.choose - a) = eStd X₁.S.g _ τ h.choose - eStd X₁.S.g _ τ a := by
    simp only [eStd, Pi.sub_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hs, sub_eq_zero] at h0
  exact h0

end GlobalTheory.Poinc.Sep.WtWd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistWeightWellDefinedOnLatticeClassStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistWeight_wellDefined_on_lattice_class : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (sg : ℤˣ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ wt : (Fin 8 → Y1) → ZMod (X₁.S.r * X₁.S.N), ∀ a mu, 𝔪1.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a := by
  first | exact @GlobalTheory.Poinc.Sep.WtWd.wt_wd | exact GlobalTheory.Poinc.Sep.WtWd.wt_wd | (intros; apply GlobalTheory.Poinc.Sep.WtWd.wt_wd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalDescendsFiniteEtaleGalois
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalDescendsFiniteEtaleGalois
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.DescGal

theorem relAmple_diag_descends : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → Out.RelAmple A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) := by
  intro X Y _ π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ hπ _ hA₀ gp sq hP hP₀ hw hamp
  have hc : (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = φ ≫ (lift (𝟙 A₀) (𝟙 A₀)).left :=
    (GlobalTheory.DiagAmpleExt.diag_comm φ φ₂ sq).symm
  have H₁ : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) ((P₀.pull φ₂).pull (lift (𝟙 A) (𝟙 A)).left) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull P _ _ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (P₀.pull φ₂) _ _ rfl) hw
  have H₂ : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) (P₀.pull ((lift (𝟙 A) (𝟙 A)).left ≫ φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn P₀ (fun _ : PUnit => φ₂) (fun _ => 1) _) H₁
  have H₃ : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) :=
    LBIso.chartPull (chartPullId _)
      (chartPullOut P₀ (fun _ : PUnit => (lift (𝟙 A₀) (𝟙 A₀)).left) (fun _ => 1) φ
        (fun _ => (lift (𝟙 A) (𝟙 A)).left ≫ φ₂) fun _ => hc) H₂
  exact (GlobalTheory.relAmple_kTriv_of_finite_etale_cover Y X π A₀ A φ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left)
    (P.pull (lift (𝟙 A) (𝟙 A)).left) hπ.fin hπ.etale hπ.onto hA₀ (pull_isLB hP₀ _) (pull_isLB hP _) gp H₃).1 hamp

end GlobalTheory.DescGal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalDescendsFiniteEtaleGaloisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_diagonal_descends_finiteEtaleGalois : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → Out.RelAmple A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) := by
  first | exact @GlobalTheory.DescGal.relAmple_diag_descends | exact GlobalTheory.DescGal.relAmple_diag_descends | (intros; apply GlobalTheory.DescGal.relAmple_diag_descends; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatBox
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

noncomputable section

namespace GlobalTheory.ProdUnif

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig

theorem compat_box₂ : ∀ {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁} {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁} {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂} (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)), M.IsLB → M₁.IsLB → M₂.IsLB → L.IsLB → L₁.IsLB → L₂.IsLB → p ≫ b₁ = h₁ ≫ p₁ → p ≫ b₂ = h₂ ≫ p₂ → f ≫ g₁ = h₁ ≫ f₁ → f ≫ g₂ = h₂ ≫ f₂ → ∀ (we : LB.Iso (L.pull f) (M.pull p)), BoxSq wM wL we we₁ we₂ h₁ h₂ → ∀ {T' T₁' T₂' : Scheme.{0}} {p' : T' ⟶ B} {f' : T' ⟶ G} {p₁' : T₁' ⟶ B₁} {f₁' : T₁' ⟶ G₁} {p₂' : T₂' ⟶ B₂} {f₂' : T₂' ⟶ G₂} {h₁' : T' ⟶ T₁'} {h₂' : T' ⟶ T₂'} (we' : LB.Iso (L.pull f') (M.pull p')) (we₁' : LB.Iso (L₁.pull f₁') (M₁.pull p₁')) (we₂' : LB.Iso (L₂.pull f₂') (M₂.pull p₂')), BoxSq wM wL we' we₁' we₂' h₁' h₂' → ∀ (m : T ⟶ T') (m₁ : T₁ ⟶ T₁') (m₂ : T₂ ⟶ T₂'), m ≫ h₁' = h₁ ≫ m₁ → m ≫ h₂' = h₂ ≫ m₂ → m ≫ f' = f → m ≫ p' = p → m₁ ≫ f₁' = f₁ → m₁ ≫ p₁' = p₁ → m₂ ≫ f₂' = f₂ → m₂ ≫ p₂' = p₂ → GlobalTheory.UnifPullRig.CompatAlong we₁' we₁ m₁ → GlobalTheory.UnifPullRig.CompatAlong we₂' we₂ m₂ → GlobalTheory.UnifPullRig.CompatAlong we' we m := by
  intro B B₁ B₂ G G₁ G₂ T T₁ T₂ M M₁ M₂ L L₁ L₂ b₁ b₂ g₁ g₂ p f p₁ f₁ p₂ f₂ h₁ h₂ wM wL we₁ we₂ hM hM₁ hM₂ hL hL₁ hL₂
    ep₁ ep₂ ef₁ ef₂ we Q T' T₁' T₂' p' f' p₁' f₁' p₂' f₂' h₁' h₂' we' we₁' we₂' Q' m m₁ m₂ hm₁ hm₂ hmf hmp hm₁f hm₁p
    hm₂f hm₂p H₁ H₂
  rintro ⟨qM, qL⟩ V a₁ a₂
  refine unit_ext fun y hy => ?_
  have bM : p y ∈ M.U (qM ⟨⟩) := mem_pull.1 (a₂ hy).1
  have bL : f y ∈ L.U (qL ⟨⟩) := mem_pull.1 (a₂ hy).2
  obtain ⟨J, hJ, eJ⟩ := exists_good M hM y (K := PUnit) (fun _ => p) (fun _ => qM ⟨⟩) (fun _ _ _ => rfl)
    (fun _ => bM)
  obtain ⟨N, hN, eN⟩ := exists_good L hL y (K := PUnit) (fun _ => f) (fun _ => qL ⟨⟩) (fun _ _ _ => rfl)
    (fun _ => bL)
  obtain ⟨J₁, hJ₁⟩ := exists_good_at hM₁ y
  obtain ⟨J₂, hJ₂⟩ := exists_good_at hM₂ y
  obtain ⟨N₁, hN₁⟩ := exists_good_at hL₁ y
  obtain ⟨N₂, hN₂⟩ := exists_good_at hL₂ y
  have e₀ := Q T (𝟙 T) y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
  have e₁ := Q' T m y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
  have c₁ := H₁.stalk hm₁f hm₁p h₁ y (J₁ (p ≫ b₁)) (N₁ (f ≫ g₁))
    ((pt_of_eq ep₁ y) ▸ hJ₁ (p ≫ b₁)) ((pt_of_eq ef₁ y) ▸ hN₁ (f ≫ g₁))
  have c₂ := H₂.stalk hm₂f hm₂p h₂ y (J₂ (p ≫ b₂)) (N₂ (f ≫ g₂))
    ((pt_of_eq ep₂ y) ▸ hJ₂ (p ≫ b₂)) ((pt_of_eq ef₂ y) ▸ hN₂ (f ≫ g₂))
  simp only [Category.id_comp] at e₀
  rw [hmp, hmf, hm₁, hm₂, c₁, c₂, ← e₀] at e₁
  have e := mul_left_cancel e₁
  rw [eJ ⟨⟩, eN ⟨⟩] at e
  exact (gm_res_pull _ m y a₁ hy _).trans ((Category.id_comp m).symm ▸ e.trans (gm_res _ y a₂ hy _).symm)

end GlobalTheory.ProdUnif
end
end

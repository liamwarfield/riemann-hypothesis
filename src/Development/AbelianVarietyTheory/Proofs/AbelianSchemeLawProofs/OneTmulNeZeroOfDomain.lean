module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoequifiberedDiagramMap
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpecHomCompCoaction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.OneTmulNeZeroOfDomain
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatFibreInjective

open TensorProduct

theorem one_tmul_ne_zero_of_domain {A P k : Type} [CommRing A] [IsDomain A] [AddCommGroup P]
    [Module A P] [Field k] [Algebra A k] (hinj : Function.Injective (algebraMap A k)) (y : P)
    (hy : ∀ a : A, a • y = 0 → a = 0) : (1 : k) ⊗ₜ[A] y ≠ 0 := by
  intro h1
  letI : Algebra (FractionRing A) k := (IsFractionRing.lift hinj).toAlgebra
  haveI : IsScalarTower A (FractionRing A) k :=
    IsScalarTower.of_algebraMap_eq (fun a => (IsFractionRing.lift_algebraMap hinj a).symm)
  haveI : Module.Flat A (FractionRing A) := IsLocalization.flat _ (nonZeroDivisors A)
  haveI : Module.Free (FractionRing A) k := Module.Free.of_divisionRing _ _
  haveI : Module.Flat (FractionRing A) k := Module.Flat.of_free
  haveI : Module.Flat A k := Module.Flat.trans _ (FractionRing A) _
  have hi : Function.Injective (LinearMap.toSpanSingleton A P y) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    exact hy
  have h2 : (1 : k) ⊗ₜ[A] (1 : A) = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := k) _ hi
    rw [LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply, one_smul, map_zero, h1]
  have h3 := congrArg (TensorProduct.rid A k) h2
  rw [TensorProduct.rid_tmul, one_smul, map_zero] at h3
  exact one_ne_zero h3

theorem one_tmul_ne_zero {R₀ P k : Type} [CommRing R₀] [AddCommGroup P] [Module R₀ P]
    [Field k] [Algebra R₀ k] (p : Ideal R₀) (hk : ∀ a, algebraMap R₀ k a = 0 ↔ a ∈ p)
    (hP : Module.IsTorsionBySet R₀ P p) (y : P) (hy : ∀ a : R₀, a • y = 0 → a ∈ p) :
    (1 : k) ⊗ₜ[R₀] y ≠ 0 := by
  intro h
  have hker : p = RingHom.ker (algebraMap R₀ k) := by
    ext a; simp [RingHom.mem_ker, hk]
  haveI : p.IsPrime := hker ▸ RingHom.ker_isPrime _
  letI : Module (R₀ ⧸ p) P := hP.module
  haveI : IsScalarTower R₀ (R₀ ⧸ p) P := hP.isScalarTower
  letI : Algebra (R₀ ⧸ p) k :=
    (Ideal.Quotient.lift p (algebraMap R₀ k) (fun a ha => (hk a).2 ha)).toAlgebra
  haveI : IsScalarTower R₀ (R₀ ⧸ p) k := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (algebraMap (R₀ ⧸ p) k) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hk a).1 ha)
  refine one_tmul_ne_zero_of_domain (A := R₀ ⧸ p) hinj y ?_ ?_
  · intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hy a ha)
  · have := congrArg (TensorProduct.mapOfCompatibleSMul (R₀ ⧸ p) R₀ R₀ k P) h
    rwa [TensorProduct.mapOfCompatibleSMul_tmul, map_zero] at this

theorem one_tmul_eq_zero {R₀ M C₀ C₁ k : Type} [CommRing R₀] [AddCommGroup M] [Module R₀ M]
    [AddCommGroup C₀] [Module R₀ C₀] [AddCommGroup C₁] [Module R₀ C₁]
    [Field k] [Algebra R₀ k] (φ : C₀ →ₗ[R₀] C₁) (hφ : Function.Injective (φ.baseChange k))
    (y : M ⊗[R₀] C₀) (hy : φ.lTensor M y = 0) : (1 : k) ⊗ₜ[R₀] y = 0 := by
  obtain ⟨g, hg⟩ := (φ.baseChange k).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hφ)
  have key : ∀ z : M ⊗[R₀] C₀,
      TensorProduct.leftComm R₀ M k C₀ ((g.restrictScalars R₀).lTensor M
        ((TensorProduct.mk R₀ k C₁ 1).lTensor M (φ.lTensor M z))) = (1 : k) ⊗ₜ[R₀] z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m c =>
      have := LinearMap.congr_fun hg ((1 : k) ⊗ₜ[R₀] c)
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.id_apply] at this
      simp [this]
    | add a b ha hb => simp only [map_add (f := _), ha, hb, tmul_add]
  rw [← key, hy]
  simp

theorem exists_of_torsion {R₀ N C : Type} [CommRing R₀] [AddCommGroup N] [Module R₀ N]
    [AddCommGroup C] [Module R₀ C] [Module.Flat R₀ C] (p : Ideal R₀) (hp : p.FG)
    (x : N ⊗[R₀] C) (hx : ∀ a ∈ p, a • x = 0) :
    ∃ y, (Submodule.torsionBySet R₀ N p).subtype.rTensor C y = x := by
  classical
  obtain ⟨s, rfl⟩ := hp
  let g : N →ₗ[R₀] (s → N) := LinearMap.pi fun a => (a : R₀) • LinearMap.id
  have hex : Function.Exact (Submodule.torsionBySet R₀ N (Ideal.span (s : Set R₀))).subtype g := by
    rw [LinearMap.exact_iff, Submodule.range_subtype, ← Submodule.torsionBySet_eq_torsionBySet_span]
    ext n
    simp [g, funext_iff, LinearMap.mem_ker]
  have h := Module.Flat.rTensor_exact C hex x
  refine h.1 ?_
  apply (TensorProduct.piLeft R₀ C (fun _ : s => N)).injective
  have key : ∀ z : N ⊗[R₀] C, ∀ a : s,
      TensorProduct.piLeft R₀ C (fun _ : s => N) (g.rTensor C z) a = (a : R₀) • z := by
    intro z a
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul n c => simp [g, smul_tmul']
    | add u v hu hv => simp only [map_add (f := _), Pi.add_apply, hu, hv, smul_add]
  funext a
  rw [key, hx _ (Ideal.subset_span a.2)]
  simp

theorem injective_baseChange :
    ∀ (R₀ R C₀ C₁ : Type) [CommRing R₀] [IsNoetherianRing R₀] [CommRing R] [Algebra R₀ R]
      [AddCommGroup C₀] [Module R₀ C₀] [AddCommGroup C₁] [Module R₀ C₁] [Module.Flat R₀ C₀]
      [Module.Flat R₀ C₁] (φ : C₀ →ₗ[R₀] C₁),
      (∀ (k : Type) [Field k] [Algebra R k] [Algebra R₀ k] [IsScalarTower R₀ R k],
        Function.Injective (φ.baseChange k)) → Function.Injective (φ.baseChange R) := by
  intro R₀ R C₀ C₁ _ _ _ _ _ _ _ _ _ _ φ H
  change Function.Injective (φ.lTensor R)
  rw [← LinearMap.ker_eq_bot]
  by_contra hne
  haveI : Nontrivial (LinearMap.ker (φ.lTensor R)) := Submodule.nontrivial_iff_ne_bot.2 hne
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty R₀ (LinearMap.ker (φ.lTensor R))
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hp
  obtain ⟨hp, ⟨x, hx0⟩, hx⟩ := hp
  have hann : ∀ a : R₀, a • x = 0 ↔ a ∈ p := by
    intro a
    rw [hx]
    simp [Submodule.mem_colon_singleton]
  let M := Submodule.torsionBySet R₀ R p
  obtain ⟨y, rfl⟩ : ∃ y, M.subtype.rTensor C₀ y = x :=
    exists_of_torsion p (IsNoetherian.noetherian p) x (fun a ha => (hann a).2 ha)
  have hy0 : φ.lTensor M y = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := C₁) M.subtype M.injective_subtype
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor]
    exact hx0
  have hkill : ∀ a : R₀, (∀ m : M, a • m = 0) → ∀ z : M ⊗[R₀] C₀, a • z = 0 := by
    intro a ha z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m c => rw [smul_tmul', ha, zero_tmul]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  have hy : ∀ a : R₀, a • y = 0 → a ∈ p := by
    intro a ha
    rw [← hann, ← map_smul, ha, map_zero]
  have hcm : (p.map (algebraMap R₀ R)).comap (algebraMap R₀ R) = p := by
    refine le_antisymm ?_ Ideal.le_comap_map
    intro a ha
    refine hy a (hkill a (fun m => ?_) y)
    have hle : p.map (algebraMap R₀ R) ≤ LinearMap.ker (LinearMap.toSpanSingleton R R m) := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      have := (Submodule.mem_torsionBySet_iff _ _).1 m.2 ⟨b, hb⟩
      simpa [Algebra.smul_def] using this
    have := hle ha
    apply Subtype.ext
    simpa [Algebra.smul_def] using this
  obtain ⟨q, hq, hqp⟩ := (Ideal.comap_map_eq_self_iff_of_isPrime p).1 hcm
  refine one_tmul_ne_zero (k := q.ResidueField) p ?_ ?_ y hy
    (one_tmul_eq_zero φ (H q.ResidueField) y hy0)
  · intro a
    rw [IsScalarTower.algebraMap_apply R₀ R q.ResidueField, Ideal.algebraMap_residueField_eq_zero,
      ← hqp]
    rfl
  · intro z a
    refine hkill a (fun m => Subtype.ext ?_) z
    exact (Submodule.mem_torsionBySet_iff _ _).1 m.2 a

end GlobalTheory.FlatFibreInjective
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsMulEqSmulOneOfMulVecInjective
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_mul_eq_smul_one_of_mulVec_injective {R K : Type} [CommRing R] [Field K]
    (g : R →+* K) {m l : Type} [Fintype m] [Fintype l] [DecidableEq l] (M : Matrix m l R)
    (hM : ∀ x : l → K, (M.map g).mulVec x = 0 → x = 0) :
    ∃ (r : R) (T : Matrix l m R), g r ≠ 0 ∧ T * M = r • (1 : Matrix l l R) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K (fun i : m => (M.map g) i)
  have : Fintype κ := Fintype.ofInjective a ha
  have h1 : Fintype.card κ ≤ Fintype.card l := by
    have := hli.fintype_card_le_finrank
    simpa using this
  have h2 : Fintype.card l ≤ Fintype.card κ := by
    have hinj : Function.Injective (Matrix.mulVecLin ((M.map g).submatrix a id)) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro x hx
      apply hM
      funext i
      have hi : (M.map g) i ∈ Submodule.span K (Set.range ((fun i : m => (M.map g) i) ∘ a)) := by
        rw [hspan]; exact Submodule.subset_span ⟨i, rfl⟩
      have key : ∀ y ∈ Submodule.span K (Set.range ((fun i : m => (M.map g) i) ∘ a)),
          y ⬝ᵥ x = 0 := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨k, rfl⟩ := hy
          exact congrFun hx k
        | zero => simp
        | add y z _ _ hy hz => rw [add_dotProduct, hy, hz, add_zero]
        | smul c y _ hy => rw [smul_dotProduct, hy, smul_zero]
      exact key _ hi
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this
  let e : l ≃ κ := Fintype.equivOfCardEq (le_antisymm h2 h1)
  let N : Matrix l l R := M.submatrix (a ∘ e) id
  have hN : IsUnit (N.map g) := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact hli.comp e e.injective
  refine ⟨N.det, N.adjugate * (1 : Matrix m m R).submatrix (a ∘ e) id, ?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det] at hN
    have : g N.det = (N.map g).det := by rw [RingHom.map_det]; rfl
    rw [this]; exact hN.ne_zero
  · rw [Matrix.mul_assoc]
    have : (1 : Matrix m m R).submatrix (a ∘ e) id * M = N := by
      ext i j
      simp [N, Matrix.mul_apply, Matrix.one_apply]
    rw [this, Matrix.adjugate_mul]

theorem exists_kernel_certificate {R K : Type} [CommRing R] [Field K] (g : R →+* K)
    {a b c : Type} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a]
    (D₀ : Matrix b a R) (D₁ : Matrix c b R) (h0 : D₁ * D₀ = 0)
    (hex : ∀ w : b → K, (D₁.map g).mulVec w = 0 → ∃ v, (D₀.map g).mulVec v = w) :
    ∃ (r : R) (n : ℕ) (B : Matrix a (Fin n) R) (C : Matrix (Fin n) a R) (H : Matrix a b R),
      g r ≠ 0 ∧ D₀ * B = 0 ∧ C * B = r • (1 : Matrix (Fin n) (Fin n) R) ∧
        B * C + H * D₀ = r • (1 : Matrix a a R) := by
  classical
  obtain ⟨κ, s, hs, hspan, hli⟩ := exists_linearIndependent' K (fun j : a => (D₀.map g).col j)
  have : Fintype κ := Fintype.ofInjective s hs
  let S : Matrix a κ R := (1 : Matrix a a R).submatrix id s
  have hDS : D₀ * S = D₀.submatrix id s := by
    ext i j
    simp [S, Matrix.mul_apply, Matrix.one_apply]
  have hsum : ∀ x : κ → K, ((D₀ * S).map g).mulVec x =
      ∑ k, x k • ((fun j : a => (D₀.map g).col j) ∘ s) k := by
    intro x
    funext i
    simp [hDS, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  obtain ⟨r₀, T₀, hr₀, hT₀⟩ := exists_mul_eq_smul_one_of_mulVec_injective g (D₀ * S) (by
    intro x hx
    rw [hsum] at hx
    funext k
    exact Fintype.linearIndependent_iff.1 hli x hx k)
  obtain ⟨r₁, T₁, hr₁, hT₁⟩ := exists_mul_eq_smul_one_of_mulVec_injective g
    (Matrix.fromRows T₀ D₁) (by
    intro w hw
    have hw1 : (T₀.map g).mulVec w = 0 := by
      funext k; exact congrFun hw (Sum.inl k)
    have hw2 : (D₁.map g).mulVec w = 0 := by
      funext k; exact congrFun hw (Sum.inr k)
    obtain ⟨v, hv⟩ := hex w hw2
    have hmem : w ∈ Submodule.span K (Set.range ((fun j : a => (D₀.map g).col j) ∘ s)) := by
      rw [hspan, ← hv]
      have : (D₀.map g).mulVec v = ∑ j, v j • (D₀.map g).col j := by
        funext i
        simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
      rw [this]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
    rw [← hsum] at hu
    rw [← hu, Matrix.mulVec_mulVec, ← Matrix.map_mul, hT₀] at hw1
    have hu0 : u = 0 := by
      funext k
      have := congrFun hw1 k
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite g] at this
      rcases this with h | h
      · exact absurd h hr₀
      · exact h
    rw [← hu, hu0, Matrix.mulVec_zero])
  let Q : Matrix a a R := r₀ • (1 : Matrix a a R) - S * T₀ * D₀
  have hQS : Q * S = 0 := by
    simp only [Q, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hT₀,
      Matrix.mul_smul, Matrix.mul_one, sub_self]
  have hDQ : r₁ • (D₀ * Q) = 0 := by
    have h1 : T₀ * (D₀ * Q) = 0 := by
      have : T₀ * (D₀ * (S * T₀ * D₀)) = (T₀ * (D₀ * S)) * (T₀ * D₀) := by
        simp only [Matrix.mul_assoc]
      simp only [Q, Matrix.mul_sub, this, hT₀, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul, sub_self]
    have h2 : D₁ * (D₀ * Q) = 0 := by rw [← Matrix.mul_assoc, h0, Matrix.zero_mul]
    have h3 : Matrix.fromRows T₀ D₁ * (D₀ * Q) = 0 := by
      rw [Matrix.fromRows_mul, h1, h2, Matrix.fromRows_zero]
    calc r₁ • (D₀ * Q) = (T₁ * Matrix.fromRows T₀ D₁) * (D₀ * Q) := by
          rw [hT₁, Matrix.smul_mul, Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, h3, Matrix.mul_zero]
  let t := {j : a // j ∉ Set.range s}
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  let f : Fin (Fintype.card t) → a := fun i => (e i).1
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hfs : ∀ i k, f i ≠ s k := fun i k h => (e i).2 ⟨k, h.symm⟩
  let E : Matrix a (Fin (Fintype.card t)) R := (1 : Matrix a a R).submatrix id f
  have hEE : E.transpose * E = 1 := by
    ext i j
    simp [E, Matrix.mul_apply, Matrix.one_apply, hf.eq_iff]
  have hES : E.transpose * S = 0 := by
    ext i j
    simp [E, S, Matrix.mul_apply, Matrix.one_apply, hfs]
  have hQE : Q * E * E.transpose = Q := by
    ext i j
    have hQE' : Q * E = Q.submatrix id f := by
      ext i j
      simp [E, Matrix.mul_apply, Matrix.one_apply]
    rw [hQE']
    by_cases hj : j ∈ Set.range s
    · obtain ⟨k, rfl⟩ := hj
      have : Q i (s k) = (Q * S) i k := by
        simp [S, Matrix.mul_apply, Matrix.one_apply]
      rw [this, hQS]
      simp [E, Matrix.mul_apply, Matrix.one_apply, hfs]
    · obtain ⟨k, hk⟩ : ∃ k, f k = j := ⟨e.symm ⟨j, hj⟩, by simp [f]⟩
      subst hk
      simp [E, Matrix.mul_apply, Matrix.one_apply, hf.eq_iff]
  refine ⟨r₁ * r₀, _, r₁ • (Q * E), E.transpose, r₁ • (S * T₀), ?_, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hr₁ hr₀
  · rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.smul_mul, hDQ, Matrix.zero_mul]
  · have : E.transpose * (S * T₀ * D₀ * E) = (E.transpose * S) * (T₀ * D₀ * E) := by
      simp only [Matrix.mul_assoc]
    simp only [Q, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, this, hES, Matrix.zero_mul,
      sub_zero, Matrix.smul_mul, Matrix.one_mul, hEE, smul_smul]
  · rw [Matrix.smul_mul, Matrix.smul_mul, hQE, ← smul_add, mul_smul]
    simp only [Q, sub_add_cancel]

theorem exists_matrix_basis_ker_of_exact_at_point :
    ∀ (R K : Type) [CommRing R] [Field K] (g₀ : R →+* K) (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) R) (D₁ : Matrix (Fin c) (Fin b) R), D₁ * D₀ = 0 → (∀ w : Fin b → K, (D₁.map g₀).mulVec w = 0 → ∃ v, (D₀.map g₀).mulVec v = w) → ∃ (r : R) (n : ℕ) (B : Matrix (Fin a) (Fin n) R), g₀ r ≠ 0 ∧ D₀ * B = 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g r) → ∀ v : Fin a → R', (D₀.map g).mulVec v = 0 → ∃! z : Fin n → R', (B.map g).mulVec z = v := by
  intro R K _ _ g₀ a b c D₀ D₁ h0 hex
  obtain ⟨r, n, B, C, H, hr, hB, hCB, hBC⟩ := exists_kernel_certificate g₀ D₀ D₁ h0 hex
  refine ⟨r, n, B, hr, hB, ?_⟩
  intro R' _ g hu v hv
  obtain ⟨u, hu⟩ := hu
  have hone : ∀ (m : ℕ) (x : Fin m → R'),
      ((r • (1 : Matrix (Fin m) (Fin m) R)).map g).mulVec x = g r • x := by
    intro m x
    funext k
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite g]
  have h1 : ∀ z : Fin n → R', (C.map g).mulVec ((B.map g).mulVec z) = (u : R') • z := by
    intro z
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hCB, hone, hu]
  have h2 : (B.map g).mulVec ((C.map g).mulVec v) = (u : R') • v := by
    rw [hu, ← hone, ← hBC, Matrix.map_add _ (map_add g), Matrix.add_mulVec, Matrix.map_mul,
      Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero,
      add_zero]
  refine ⟨((u⁻¹ : R'ˣ) : R') • (C.map g).mulVec v, ?_, ?_⟩
  · show (B.map g).mulVec _ = v
    rw [Matrix.mulVec_smul, h2, smul_smul, Units.inv_mul, one_smul]
  · intro z hz
    rw [← hz, h1, smul_smul, Units.inv_mul, one_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LinearIndependentOfCommSmul
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.linearIndependent_of_comm_smul {K G V : Type} [Field K] [AddCommGroup V] [Module K V]
    [Nontrivial V] (A : G → V →ₗ[K] V) (c : G → G → K) (hA : ∀ x, Function.Injective (A x))
    (h : ∀ x y v, A x (A y v) = c x y • A y (A x v)) (hc : Function.Injective c) :
    LinearIndependent K A := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro g hg i hi
  by_contra hgi

  have htwist : ∀ y, ∑ x ∈ s, (g x * (c x y - c i y)) • A x = 0 := by
    intro y
    ext v
    have h0 := LinearMap.congr_fun hg v
    have h1 := LinearMap.congr_fun hg (A y v)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.zero_apply] at h0 h1 ⊢
    have h2 : A y (∑ x ∈ s, (g x * c x y) • A x v) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← h1]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_smul, h x y v, smul_smul]
    have h3 : ∑ x ∈ s, (g x * c x y) • A x v = 0 :=
      hA y (by rw [h2, map_zero])
    simp_rw [mul_sub, sub_smul, Finset.sum_sub_distrib, h3, zero_sub, neg_eq_zero]
    have h4 : ∑ x ∈ s, (g x * c i y) • A x v = c i y • ∑ x ∈ s, g x • A x v := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [smul_smul, mul_comm]
    rw [h4, h0, smul_zero]
  have hothers : ∀ x ∈ s, x ≠ i → g x = 0 := by
    intro x hx hxi
    by_contra hgx
    apply hxi
    apply hc
    funext y
    have hrel : ∑ z ∈ s.erase i, (g z * (c z y - c i y)) • A z = 0 := by
      rw [← htwist y, ← Finset.sum_erase_add s _ hi, sub_self, mul_zero, zero_smul, add_zero]
    have := ih (s.erase i) (Finset.erase_ssubset hi) _ hrel x (Finset.mem_erase.2 ⟨hxi, hx⟩)
    rcases mul_eq_zero.1 this with h5 | h5
    · exact absurd h5 hgx
    · exact sub_eq_zero.1 h5
  have hsingle : g i • A i = 0 := by
    rw [← hg, Finset.sum_eq_single_of_mem i hi]
    intro x hx hxi
    rw [hothers x hx hxi, zero_smul]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  apply hv
  apply hA i
  have := LinearMap.congr_fun hsingle v
  simp only [LinearMap.smul_apply, LinearMap.zero_apply] at this
  rw [map_zero]
  exact (smul_eq_zero.1 this).resolve_left hgi

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.heisenberg_family_irreducible : ∀ (K G V : Type) [Field K] [CommGroup G] [Finite G] [AddCommGroup V] [Module K V] [Module.Finite K V] (U : G → V ≃ₗ[K] V) (e : G → G →* Kˣ), (∀ x y v, U x (U y v) = (e x y : K) • U y (U x v)) → Function.Injective e → Module.finrank K V ^ 2 ≤ Nat.card G → ∀ W : Submodule K V, (∀ x v, v ∈ W → U x v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro K G V _ _ _ _ _ _ U e hU he hcard W hW
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact Or.inl (Submodule.eq_bot_of_subsingleton)
  haveI : Fintype G := Fintype.ofFinite G
  have hind : LinearIndependent K (fun x => (U x : V →ₗ[K] V)) := by
    refine _root_.GlobalTheory.linearIndependent_of_comm_smul (fun x => (U x : V →ₗ[K] V))
      (fun x y => (e x y : K)) (fun x => (U x).injective) (fun x y v => hU x y v) ?_
    intro x x' hxx'
    apply he
    ext y
    exact congr_fun hxx' y
  have hdim : Module.finrank K (V →ₗ[K] V) = Module.finrank K V ^ 2 := by
    rw [Module.finrank_linearMap, sq]
  have hle := hind.fintype_card_le_finrank
  rw [hdim] at hle
  rw [Nat.card_eq_fintype_card] at hcard
  have hspan := hind.span_eq_top_of_card_eq_finrank (le_antisymm hle hcard |>.trans hdim.symm)

  let S : Submodule K (V →ₗ[K] V) :=
    { carrier := {f | ∀ w ∈ W, f w ∈ W}
      add_mem' := fun hf hg w hw => W.add_mem (hf w hw) (hg w hw)
      zero_mem' := fun w _ => by simp
      smul_mem' := fun a f hf w hw => W.smul_mem a (hf w hw) }
  have hS : ∀ f : V →ₗ[K] V, ∀ w ∈ W, f w ∈ W := by
    intro f
    have : f ∈ Submodule.span K (Set.range fun x => (U x : V →ₗ[K] V)) := by
      rw [hspan]; exact Submodule.mem_top
    have hsub : Submodule.span K (Set.range fun x => (U x : V →ₗ[K] V)) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩ w hw
      exact hW x w hw
    exact hsub this
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K V, φ w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff K w).1 hcon)
  rw [eq_top_iff]
  intro v _
  have := hS ((φ w)⁻¹ • φ.smulRight v) w hwW
  simpa [LinearMap.smulRight_apply, smul_smul, inv_mul_cancel₀ hφ] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.EqOneOfPowEqOneOfCongrOne
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SerreTorsion

variable {E : Type} [Ring E]

theorem one_add_pow_expand (x : E) (n : ℕ) :
    ∃ y : E, (1 + x) ^ n = 1 + n • x + n.choose 2 • x ^ 2 + x ^ 3 * y := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih
    refine ⟨n.choose 2 • (1 : E) + y * (1 + x), ?_⟩
    have hc : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    rw [pow_succ, hy, hc]
    simp only [add_mul, mul_add, _root_.one_mul, _root_.mul_one, smul_mul_assoc, mul_smul_comm, add_smul,
      one_smul, pow_succ, pow_zero, _root_.mul_assoc]
    abel

theorem one_add_smul_pow_expand (c : ℕ) (ψ : E) (n : ℕ) :
    ∃ z : E, (1 + c • ψ) ^ n = 1 + c • (n • ψ + (n.choose 2 * c) • ψ ^ 2 + (c ^ 2) • z) := by
  obtain ⟨y, hy⟩ := one_add_pow_expand (c • ψ) n
  refine ⟨ψ ^ 3 * y, ?_⟩
  rw [hy, smul_pow, smul_pow, smul_mul_assoc]
  module

theorem step (htf : ∀ (n : ℕ) (x : E), n ≠ 0 → n • x = 0 → x = 0) {q c l : ℕ} (hq : q.Prime)
    (hl : l.Prime) (hc0 : c ≠ 0) (hqc : q ∣ c) (h2 : q = 2 → 4 ∣ c) (ψ : E)
    (h : (1 + c • ψ) ^ l = 1) : ∃ y : E, ψ = q • y := by
  obtain ⟨z, hz⟩ := one_add_smul_pow_expand c ψ l
  rw [h] at hz
  have h0 := htf c _ hc0 (left_eq_add.mp hz)
  obtain ⟨d, rfl⟩ := hqc
  by_cases hlq : l = q
  · subst hlq
    have hdiv : l ∣ l.choose 2 * d := by
      by_cases hl2 : l = 2
      · subst hl2
        have := h2 rfl
        apply Dvd.dvd.mul_left
        omega
      · have := hl.two_le
        exact Dvd.dvd.mul_right (hl.dvd_choose_self (by norm_num) (by omega)) _
    obtain ⟨e, he⟩ := hdiv
    have h1 : l • (ψ + l • (e • ψ ^ 2 + (d ^ 2) • z)) = 0 := by
      rw [← h0, mul_left_comm, he]
      module
    have h3 := htf l _ hl.ne_zero h1
    exact ⟨-(e • ψ ^ 2 + (d ^ 2) • z), by rw [smul_neg]; exact eq_neg_of_add_eq_zero_left h3⟩
  · have hcop : IsCoprime (l : ℤ) (q : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hl hq).mpr hlq)
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨v • ψ - u • ((l.choose 2 * d) • ψ ^ 2 + (q * d ^ 2) • z), ?_⟩
    have h1 : ψ = (u * l + v * q) • ψ := by rw [huv, one_smul]
    have h4 : ψ = (u * l + v * q) • ψ
        - u • (l • ψ + (l.choose 2 * (q * d)) • ψ ^ 2 + ((q * d) ^ 2) • z) := by
      rw [h0, smul_zero, sub_zero]; exact h1
    refine h4.trans ?_
    module

theorem eq_zero_of_prime (htf : ∀ (n : ℕ) (x : E), n ≠ 0 → n • x = 0 → x = 0) {q c l : ℕ}
    (hq : q.Prime) (hsep : ∀ x : E, (∀ k : ℕ, ∃ y : E, x = q ^ k • y) → x = 0)
    (hl : l.Prime) (hc0 : c ≠ 0) (hqc : q ∣ c) (h2 : q = 2 → 4 ∣ c) (ψ : E)
    (h : (1 + c • ψ) ^ l = 1) : ψ = 0 := by
  apply hsep
  intro k
  induction k with
  | zero => exact ⟨ψ, by simp⟩
  | succ k ih =>
    obtain ⟨y, hy⟩ := ih
    have h' : (1 + (c * q ^ k) • y) ^ l = 1 := by rw [mul_smul, ← hy, h]
    obtain ⟨w, hw⟩ := step htf hq hl (mul_ne_zero hc0 (pow_ne_zero k hq.ne_zero))
      (hqc.mul_right _) (fun hq2 => (h2 hq2).mul_right _) y h'
    exact ⟨w, by rw [hy, hw, pow_succ, mul_smul]⟩

theorem eq_one_of_pow (htf : ∀ (n : ℕ) (x : E), n ≠ 0 → n • x = 0 → x = 0) {q c : ℕ}
    (hq : q.Prime) (hsep : ∀ x : E, (∀ k : ℕ, ∃ y : E, x = q ^ k • y) → x = 0)
    (hc0 : c ≠ 0) (hqc : q ∣ c) (h2 : q = 2 → 4 ∣ c) (m : ℕ) :
    m ≠ 0 → ∀ ψ : E, (1 + c • ψ) ^ m = 1 → 1 + c • ψ = 1 := by
  induction m using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one => intro _ ψ h; simpa only [pow_one] using h
  | prime_mul l a hl ih =>
    intro hm ψ h
    have ha : a ≠ 0 := right_ne_zero_of_mul hm
    obtain ⟨z, hz⟩ := one_add_smul_pow_expand c ψ l
    rw [pow_mul, hz] at h
    have h1 := ih ha _ h
    rw [← hz] at h1
    rw [eq_zero_of_prime htf hq hsep hl hc0 hqc h2 ψ h1, smul_zero, add_zero]

end SerreTorsion

theorem eq_one_of_pow_eq_one_of_congr_one :
    ∀ (E : Type) [Ring E] (M : ℕ), 3 ≤ M → (∀ (n : ℕ) (x : E), n ≠ 0 → (n : E) * x = 0 → x = 0) → (∀ (q : ℕ) (x : E), 2 ≤ q → (∀ k : ℕ, ∃ y : E, x = (q : E) ^ k * y) → x = 0) → ∀ (σ φ : E) (m : ℕ), m ≠ 0 → σ = 1 + (M : E) * φ → σ ^ m = 1 → σ = 1 := by
  intro E _ M hM htf hsep σ φ m hm hσ h
  have hq : ∃ q : ℕ, q.Prime ∧ q ∣ M ∧ (q = 2 → 4 ∣ M) := by
    rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt (by omega : 2 < M) with
      h4 | ⟨p, hp, hpM, hodd⟩
    · exact ⟨2, Nat.prime_two, Dvd.dvd.trans (by norm_num) h4, fun _ => h4⟩
    · refine ⟨p, hp, hpM, fun h2 => ?_⟩
      subst h2
      exact absurd hodd (by decide)
  obtain ⟨q, hq, hqM, h2⟩ := hq
  rw [← nsmul_eq_mul] at hσ
  subst hσ
  refine SerreTorsion.eq_one_of_pow (fun n x hn hx => htf n x hn (by rwa [← nsmul_eq_mul])) hq
    (fun x hx => hsep q x hq.two_le fun k => ?_) (by omega) hqM h2 m hm φ h
  obtain ⟨y, hy⟩ := hx k
  exact ⟨y, by rw [hy, nsmul_eq_mul, Nat.cast_pow]⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsQuotientSchemeOfFiniteFlatSubgroup
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AffineQuotient

set_option backward.isDefEq.respectTransparency false

open TensorProduct Algebra.TensorProduct in
lemma exists_coaction {R Λ : Type} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ]
    {A : Over (Spec (CommRingCat.of R))} [GrpObj A] (i : specOver R Λ ⟶ A) {Y : Scheme.{0}}
    (f : A.left ⟶ Y) (g : (specOver R Λ ⊗ A).left ⟶ Y)
    (ha : ((fst (specOver R Λ) A ≫ i) * snd (specOver R Λ) A).left ≫ f = g)
    (hp : (snd (specOver R Λ) A).left ≫ f = g) (U : Y.Opens) (hf : IsAffineOpen (f ⁻¹ᵁ U))
    (hg : IsAffineOpen (g ⁻¹ᵁ U)) :
    ∃ (_ : Algebra R Γ(A.left, f ⁻¹ᵁ U)) (v : specOver R Γ(A.left, f ⁻¹ᵁ U) ⟶ A) (_ : Mono v)
      (ρ : Γ(A.left, f ⁻¹ᵁ U) →ₐ[R] Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)
      (e : Γ((specOver R Λ ⊗ A).left, g ⁻¹ᵁ U) ⟶ .of (Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)) (_ : IsIso e),
      specHom ρ ≫ v = (specHom includeRight ≫ i) * (specHom includeLeft ≫ v) ∧
      pullOver f g _ ha U ≫ e = CommRingCat.ofHom ρ.toRingHom ∧
      pullOver f g _ hp U ≫ e = CommRingCat.ofHom (includeLeft : Γ(A.left, f ⁻¹ᵁ U) →ₐ[R]
        Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ).toRingHom := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hf.fromSpec ≫ A.hom)
  let : Algebra R Γ(A.left, f ⁻¹ᵁ U) := φ.hom.toAlgebra
  let v : specOver R Γ(A.left, f ⁻¹ᵁ U) ⟶ A := Over.homMk hf.fromSpec hφ.symm
  have : Mono v.left := inferInstanceAs (Mono hf.fromSpec)
  have P₁ : IsPullback (Spec.map (pullOver f g _ hp U))
      (hg.fromSpec ≫ (fst (specOver R Λ) A).left) (Spec.map φ) (specOver R Λ).hom := by
    rw [hφ]
    exact (isPullback_pullOver f g _ hp hf hg).paste_vert
      (IsPullback.of_hasPullback (specOver R Λ).hom A.hom).flip
  have P₂ : IsPullback (specHom (includeLeft : Γ(A.left, f ⁻¹ᵁ U) →ₐ[R]
        Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)).left (specHom (includeRight : Λ →ₐ[R]
        Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)).left (Spec.map φ) (specOver R Λ).hom :=
    isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct R Γ(A.left, f ⁻¹ᵁ U) Λ)
  obtain ⟨e, he⟩ := Spec.map_surjective (P₂.isoIsPullback _ _ P₁).hom
  have : IsIso (Spec.map e) := by rw [he]; infer_instance
  have : IsIso e := by
    have : IsIso (Scheme.Spec.map e.op) := this
    have := Spec.fullyFaithful.isIso_of_isIso_map e.op
    exact isIso_of_op e
  have h₁ := P₂.isoIsPullback_hom_fst _ _ P₁
  have h₂ := P₂.isoIsPullback_hom_snd _ _ P₁
  rw [← he] at h₁ h₂
  have hw : (Spec.map e ≫ hg.fromSpec) ≫ (specOver R Λ ⊗ A).hom =
      (specOver R (Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)).hom := by
    rw [← Over.w (fst (specOver R Λ) A), Category.assoc, reassoc_of% h₂, Over.w]
  let k : specOver R (Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ) ⟶ specOver R Λ ⊗ A :=
    Over.homMk (Spec.map e ≫ hg.fromSpec) hw
  have k₁ : k ≫ fst _ _ = specHom includeRight := by
    ext1
    rw [← h₂]
    exact Category.assoc ..
  have k₂ : k ≫ snd _ _ = specHom includeLeft ≫ v := by
    ext1
    rw [Over.comp_left, Over.comp_left, ← h₁]
    change (Spec.map e ≫ hg.fromSpec) ≫ _ = (Spec.map e ≫ _) ≫ hf.fromSpec
    rw [Category.assoc, Category.assoc, SpecMap_pullOver f g _ hp hf hg]
  have k₃ : (k ≫ ((fst (specOver R Λ) A ≫ i) * snd (specOver R Λ) A)).left =
      Spec.map (pullOver f g _ ha U ≫ e) ≫ hf.fromSpec := by
    rw [Spec.map_comp, Category.assoc, SpecMap_pullOver f g _ ha hf hg]
    exact Category.assoc ..
  have h₃ : φ ≫ pullOver f g _ ha U ≫ e =
      CommRingCat.ofHom (algebraMap R (Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, ← Category.assoc, ← k₃, Over.w]
    rfl
  let ρ : Γ(A.left, f ⁻¹ᵁ U) →ₐ[R] Γ(A.left, f ⁻¹ᵁ U) ⊗[R] Λ :=
    ⟨(pullOver f g _ ha U ≫ e).hom, fun r ↦ congr($h₃ r)⟩
  refine ⟨inferInstance, v, Over.mono_of_mono_left v, ρ, e, this, ?_, rfl, ?_⟩
  · rw [← k₂, ← k₁, Category.assoc, ← comp_mul]
    ext1
    exact k₃.symm
  · apply Spec.map_injective
    rw [Spec.map_comp, h₁]
    rfl

lemma exists_quotient_hopf
    (hq : (∀ (R Λ B : Type) [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Module.Finite R Λ] [Module.Projective R Λ] [CommRing B] [Algebra R B] (ρ : B →ₐ[R] TensorProduct R B Λ), (∀ b, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) = (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b)) → (∀ b, TensorProduct.rid R B ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ b)) = b) → Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ) ρ) → Module.Finite (AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ)) B ∧ Module.FaithfullyFlat (AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ)) B ∧ RingHom.ker (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ) ρ) = Ideal.span {z | ∃ b ∈ AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ), z = b ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] b}))
    {R Λ : Type} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Module.Finite R Λ]
    [Module.Projective R Λ]
    {A : Over (Spec (CommRingCat.of R))} [GrpObj A] [IsCommMonObj A] (i : specOver R Λ ⟶ A)
    [IsMonHom i] [Mono i] {Y : Over (Spec (CommRingCat.of R))} [IsLocallyNoetherian Y.left]
    (f : A ⟶ Y) [IsFinite f.left]
    (h : ((fst (specOver R Λ) A ≫ i) * snd (specOver R Λ) A) ≫ f = snd (specOver R Λ) A ≫ f) :
    ∃ (Q : Over (Spec (CommRingCat.of R))) (q : A ⟶ Q) (π : Q ⟶ Y), IsFinite π.left ∧
      IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧
      IsPullback ((fst (specOver R Λ) A ≫ i) * snd (specOver R Λ) A) (snd (specOver R Λ) A) q q := by
  have : IsAffine (specOver R Λ).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffineHom (specOver R Λ).hom := inferInstance
  have : IsAffineHom (snd (specOver R Λ) A).left :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) (specOver R Λ).hom A.hom this
  have ha : ((fst (specOver R Λ) A ≫ i) * snd (specOver R Λ) A).left ≫ f.left =
    (snd (specOver R Λ) A).left ≫ f.left := congr(($h).left)
  obtain ⟨Q, q, π, h₀, h₁, h₂, h₃, h₄, h₅⟩ := exists_quotient f.left _ _ ha _ rfl (fun U ↦ by
    obtain ⟨_, v, _, ρ, e, _, hρ, e₁, e₂⟩ :=
      exists_coaction i f.left _ ha rfl U.1 (U.2.preimage _) (U.2.preimage _)
    have hs := coaction_free i v ρ hρ
    obtain ⟨-, hff, hk⟩ := hq R Λ _ ρ (coaction_assoc i v ρ hρ) (coaction_counit i v ρ hρ) hs
    have hC : invariants f.left _ _ ha _ rfl U.1 = ρ.toRingHom.eqLocus
        (Algebra.TensorProduct.includeLeft : Γ(A.left, f.left ⁻¹ᵁ U.1) →ₐ[R] _).toRingHom := by
      ext x
      rw [mem_invariants, ← (ConcreteCategory.bijective_of_isIso e).1.eq_iff,
        ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, e₁, e₂]
      rfl
    rw [hC]
    refine ⟨hff, ?_⟩
    refine (isPushout_equalizer ρ _ hs hk).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (asIso e).symm (by simp) (by simp) ?_ ?_
    · rw [← e₁]; simp
    · rw [← e₂]; simp)
  refine ⟨Over.mk (π ≫ Y.hom), Over.homMk q (by simp [reassoc_of% h₀]), Over.homMk π rfl,
    h₁, h₂, h₃, h₄, ?_⟩
  exact IsPullback.of_map_of_faithful (Over.forget _) h₅

lemma exists_hopfAlgebra (R : Type) [CommRing R] [IsNoetherianRing R]
    (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [IsFinite H.hom] [Flat H.hom] :
    ∃ (Λ : Type) (_ : CommRing Λ) (_ : HopfAlgebra R Λ) (_ : Module.Finite R Λ)
      (_ : Module.Projective R Λ) (e : specOver R Λ ≅ H), IsMonHom e.hom := by
  have : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨⟨Λ⟩, ⟨e⟩⟩ := (essImage_hopfSpec (R := .of R) (G := Grp.mk H)).2 this
  let e' : specOver R Λ ≅ H := (Grp.forget _).mapIso e
  have h₁ : IsFinite (specOver R Λ).hom := by
    rw [← Over.w e'.hom]; infer_instance
  have h₂ : Flat (specOver R Λ).hom := by
    rw [← Over.w e'.hom]; infer_instance
  have : Module.Finite R Λ := RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1 h₁)
  have : Module.Flat R Λ := RingHom.flat_algebraMap_iff.1 (Flat.SpecMap_iff.1 h₂)
  have : Module.FinitePresentation R Λ := Module.finitePresentation_of_finite R Λ
  exact ⟨Λ, inferInstance, inferInstance, inferInstance,
    Module.Flat.projective_of_finitePresentation, e', e.hom.hom.isMonHom_hom⟩

end GlobalTheory.AffineQuotient

namespace GlobalTheory

open AffineQuotient

set_option backward.isDefEq.respectTransparency false in
theorem exists_quotient_scheme_of_finite_flat_subgroup :
    (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [IsCommMonObj H], IsFinite H.hom → Flat H.hom → ∃ N : ℕ, 1 ≤ N ∧ 𝟙 H ^ N = 1) → (∀ (R Λ B : Type) [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Module.Finite R Λ] [Module.Projective R Λ] [CommRing B] [Algebra R B] (ρ : B →ₐ[R] TensorProduct R B Λ), (∀ b, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) = (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b)) → (∀ b, TensorProduct.rid R B ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ b)) = b) → Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ) ρ) → Module.Finite (AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ)) B ∧ Module.FaithfullyFlat (AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ)) B ∧ RingHom.ker (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ) ρ) = Ideal.span {z | ∃ b ∈ AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] TensorProduct R B Λ), z = b ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] b}) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Spec (CommRingCat.of R))) (H : Over (Spec (CommRingCat.of R))) [GrpObj H] (i : H ⟶ P.A), IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → ∃ (Q : Over (Spec (CommRingCat.of R))) (q : P.A ⟶ Q), IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ IsSeparated Q.hom ∧ LocallyOfFiniteType Q.hom ∧ IsPullback ((fst H P.A ≫ i) * snd H P.A) (snd H P.A) q q := by
  intro hk hq hm R _ _ P H _ i _ _ _ _
  have := P.isAb.comm
  have := P.isAb.proper
  have : IsCommMonObj H := ⟨by
    rw [← cancel_mono i, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]⟩
  obtain ⟨N, hN, hH⟩ := hk R H ‹_› ‹_›
  have : IsLocallyNoetherian P.A.left := LocallyOfFiniteType.isLocallyNoetherian P.A.hom
  have := (hm _ P N hN).1
  obtain ⟨Λ, _, _, _, _, e, _⟩ := exists_hopfAlgebra R H
  have hi : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hH, MonObj.one_comp]
  obtain ⟨Q, q, π, h₁, h₂, h₃, h₄, h₅⟩ := exists_quotient_hopf hq (e.hom ≫ i) (mulA P.A N) (by
    rw [mulA, comp_pow, comp_pow, Category.comp_id, Category.comp_id, mul_pow, ← comp_pow,
      ← comp_pow i, hi, comp_one, comp_one, _root_.one_mul])
  refine ⟨Q, q, h₂, h₃, h₄, ?_, ?_, ?_⟩
  · rw [← Over.w π]; infer_instance
  · rw [← Over.w π]; infer_instance
  · refine h₅.of_iso (whiskerRightIso e P.A) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      <;> simp [comp_mul]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NatCardEqOfEquivPiField
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace MulLaw

theorem natCard_eq_of_equiv_pi_field {R : Type} [Field R] {U V : Type} [AddCommGroup U]
    [Module R U] [AddCommGroup V] [Module R V] {X : Type} (e : U ≃ₗ[R] (X → V)) {m : ℕ}
    (hm : 0 < m) (hU : Module.finrank R U = m) (hV : Module.finrank R V = 1) :
    Nat.card X = m := by
  classical
  haveI : Module.Finite R U := Module.finite_of_finrank_pos (hU ▸ hm)
  haveI : Module.Finite R V := Module.finite_of_finrank_pos (hV ▸ Nat.one_pos)
  have e₁ : V ≃ₗ[R] R := LinearEquiv.ofFinrankEq V R (by rw [hV, Module.finrank_self])
  have e₂ : U ≃ₗ[R] (X → R) := e.trans (LinearEquiv.piCongrRight fun _ => e₁)
  haveI : Module.Finite R (X → R) := Module.Finite.equiv e₂
  haveI : Finite X := (Pi.linearIndependent_single_one X R).finite
  haveI := Fintype.ofFinite X
  rw [← hU, e₂.finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

theorem natCard_eq_of_equiv_pi {R : Type} [CommRing R] (hR : IsField R) {U V : Type}
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V] {X : Type}
    (e : U ≃ₗ[R] (X → V)) {m : ℕ}
    (hm : 0 < m) (hU : Module.finrank R U = m) (hV : Module.finrank R V = 1) :
    Nat.card X = m := by
  letI := hR.toField
  exact natCard_eq_of_equiv_pi_field e hm hU hV

noncomputable def basePointsEquiv {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'}
    [GrpObj A] [GrpObj A'] {g : A'.left ⟶ A.left} (hg : IsPullback g A'.hom A.hom f)
    (hmul : ∀ (T : Over S') (x y : T ⟶ A'),
      toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y) (T : Over S') :
    (T ⟶ A') ≃* (Over.mk (T.hom ≫ f) ⟶ A) where
  toFun x := toBase hg.w x
  invFun y := Over.homMk (hg.lift y.left T.hom (Over.w y)) (hg.lift_snd _ _ _)
  left_inv x := by
    apply Over.OverMorphism.ext
    apply hg.hom_ext
    · exact hg.lift_fst _ _ _
    · exact (hg.lift_snd _ _ _).trans (Over.w x).symm
  right_inv y := by
    apply Over.OverMorphism.ext
    exact hg.lift_fst _ _ _
  map_mul' x y := hmul T x y

end MulLaw

theorem mulN_of_decomposition :
    (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n j : ℕ), (n : K) ≠ 0 → 1 ≤ j → Nonempty (SecM P.A P.L ((n ^ 2 * j : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K))) ≃ₗ[Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)] ({x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A // x ^ n = 1} → SecM P.A P.L (j : ℤ) (baseOver (Spec (CommRingCat.of K)))))) → GlobalSectionsRankAlgClosed → PolBaseChangeSt → MulNSt := by
  intro hQ hRel hH hBC S _ P n hn
  obtain ⟨h1, h2, h3, h4⟩ := hQ S P n hn
  refine ⟨h1, h2, h3, h4, fun k _ _ t hk => ?_⟩
  obtain ⟨P', g, hg, hdim, hmul, -⟩ := hBC S _ t P
  obtain ⟨e⟩ := hRel k P' n 1 hk le_rfl
  have hn2 : 1 ≤ n ^ 2 * 1 := by
    rw [Nat.mul_one]; exact Nat.one_le_pow _ _ hn
  have hU := hH k P' (n ^ 2 * 1) hn2
  have hV := hH k P' 1 le_rfl
  rw [one_pow] at hV
  have hF : IsField Γ((baseOver (Spec (CommRingCat.of k))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)
  have hcard := MulLaw.natCard_eq_of_equiv_pi hF e (Nat.pow_pos hn2) hU hV
  have φ : (baseOver (Spec (CommRingCat.of k)) ⟶ P'.A) ≃* (Over.mk t ⟶ P.A) := by
    have ψ := MulLaw.basePointsEquiv hg hmul (baseOver (Spec (CommRingCat.of k)))
    have ht : (baseOver (Spec (CommRingCat.of k))).hom ≫ t = t := Category.id_comp t
    rw [ht] at ψ
    exact ψ
  rw [← Nat.card_congr (φ.toEquiv.subtypeEquiv
    (p := fun x => x ^ n = 1) (q := fun x => x ^ n = 1) (fun x => by
      show x ^ n = 1 ↔ φ x ^ n = 1
      rw [← map_pow, map_eq_one_iff φ φ.injective])), hcard, hdim, Nat.mul_one, ← pow_mul]

end GlobalTheory
end

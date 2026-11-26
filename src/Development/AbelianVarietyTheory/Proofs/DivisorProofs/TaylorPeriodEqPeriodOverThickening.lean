module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnInvSetOfSmoothAlongProdExp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockHarmonicRepresentative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersOfCompOnGenerators

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSliceZeroIsTay
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSliceZeroIsTay
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily

namespace GlobalTheory.AnPer.SliceZero

theorem prod_sumElim_zero {I : Type} {g : ℕ} {R : Type} [CommRing R] (N : ℕ) (t : I → R)
    (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) (s : Fin (N + 1) → I ⊕ Fin g) :
    ∏ a, (Sum.elim t (0 : Fin g → R)) (s a) = 0 := by
  by_cases h : ∀ a, ∃ i, s a = Sum.inl i
  · choose f hf using h
    rw [Finset.prod_congr rfl fun a _ ↦ by rw [hf a]]
    simpa using ht f
  · push_neg at h
    obtain ⟨a, ha⟩ := h
    obtain ⟨b, hb⟩ : ∃ b, s a = Sum.inr b := by
      rcases hs : s a with i | b
      · exact absurd hs (ha i)
      · exact ⟨b, rfl⟩
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by rw [hb]; rfl)

end GlobalTheory.AnPer.SliceZero


open GlobalTheory.AnPer.SliceZero in
theorem GlobalTheory.AnPer.exists_sliceZero_isTay : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∃ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ := by
  intro I _ _ g R _ _ N t ht W W₀ hW
  obtain ⟨ρ, hρ⟩ := GlobalTheory.AnPer.exists_sliceTaylor_algHom N (Sum.elim t (0 : Fin g → R))
    (prod_sumElim_zero N t ht) (E := Tot Empty g) W W₀ Prod.snd
    (fun p _ ↦ analyticAt_snd) hW
  refine ⟨ρ.toRingHom, fun h p hp ↦ ?_⟩
  refine (hρ h p hp).trans ?_
  have hh : AnalyticAt ℂ h.fn (0, p.2 + (fun _ : I → ℂ ↦ (0 : Fin g → ℂ)) 0) := by
    rw [add_zero]; exact h.analytic _ (hW p hp)
  have hs := taylor_shear N t ht h.fn (fun _ ↦ (0 : Fin g → ℂ)) p.2 analyticAt_const hh
  simp only [add_zero, Pi.zero_apply, taylor_const_fun, map_zero, sub_zero] at hs
  rw [hs]
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSliceZeroIsTayStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_isTay_of_slice_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∃ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ := by
  first | exact @GlobalTheory.AnPer.exists_sliceZero_isTay | exact GlobalTheory.AnPer.exists_sliceZero_isTay | (intros; apply GlobalTheory.AnPer.exists_sliceZero_isTay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassLinearRelationUniqueOfNilpotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationChartCoboundaryOnChartsFirstOrder
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartCobd

open GlobalTheory.CatCoh GlobalTheory.AnPer.Charts

theorem tsze_mul_of_fst {A : Type} [CommRing A] {n : ℕ} (x y : TrivSqZeroExt A (Fin n → A)) (hx : x.fst = 0)
    (hy : y.fst = 0) : x * y = 0 := by
  ext : 1 <;> simp [hx, hy]

theorem comap_fst_nil {A : Type} [CommRing A] {n : ℕ} (J : Ideal A) (hJ : IsNilpotent J) :
    IsNilpotent (J.comap (TrivSqZeroExt.fstHom ℤ A (Fin n → A)).toRingHom) := by
  obtain ⟨N, hN⟩ := hJ
  refine ⟨N * 2, ?_⟩
  have h1 : (J.comap (TrivSqZeroExt.fstHom ℤ A (Fin n → A)).toRingHom) ^ N ≤
      RingHom.ker (TrivSqZeroExt.fstHom ℤ A (Fin n → A)).toRingHom := by
    refine (Ideal.le_comap_pow _ N).trans ?_
    rw [hN, Ideal.zero_eq_bot]
    exact le_of_eq rfl
  rw [pow_mul, Ideal.zero_eq_bot, eq_bot_iff]
  refine (Ideal.pow_right_mono h1 2).trans ?_
  rw [pow_two, Ideal.mul_le]
  intro a ha b hb
  rw [Ideal.mem_bot]
  exact tsze_mul_of_fst a b ha hb

section Gen

variable {R : Type} [CommRing R] [Algebra ℂ R] {O O' : Type} [CommRing O] [Algebra ℂ O] [CommRing O'] [Algebra ℂ O']

theorem map_alg (φ : O →ₐ[ℂ] O') (r : R) :
    Algebra.TensorProduct.map (AlgHom.id ℂ R) φ (algebraMap R (R ⊗[ℂ] O) r) = algebraMap R (R ⊗[ℂ] O') r := by
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem map_mem (φ : O →ₐ[ℂ] O') (M : Ideal R) (c : R ⊗[ℂ] O) (hc : c ∈ M.map (algebraMap R (R ⊗[ℂ] O))) :
    Algebra.TensorProduct.map (AlgHom.id ℂ R) φ c ∈ M.map (algebraMap R (R ⊗[ℂ] O')) := by
  have e : (Algebra.TensorProduct.map (AlgHom.id ℂ R) φ).toRingHom.comp (algebraMap R (R ⊗[ℂ] O)) =
      algebraMap R (R ⊗[ℂ] O') := RingHom.ext (map_alg φ)
  have := Ideal.mem_map_of_mem (Algebra.TensorProduct.map (AlgHom.id ℂ R) φ).toRingHom hc
  rwa [Ideal.map_map, e] at this

theorem map_right (φ : O →ₐ[ℂ] O') (x : O) :
    Algebra.TensorProduct.map (AlgHom.id ℂ R) φ (Algebra.TensorProduct.includeRight x) =
      Algebra.TensorProduct.includeRight (R := ℂ) (A := R) (φ x) := by
  simp

theorem map_nil {A : Type} [CommRing A] (f : R →+* A) (M : Ideal R) (h : IsNilpotent M) : IsNilpotent (M.map f) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, by rw [← Ideal.map_pow, hN, Ideal.zero_eq_bot, Ideal.map_bot, Ideal.zero_eq_bot]⟩

theorem lTensor_alg (D : Derivation ℂ O O) (r : R) :
    LinearMap.lTensor R D.toLinearMap (algebraMap R (R ⊗[ℂ] O) r) = 0 := by
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem lTensor_right (D : Derivation ℂ O O) (x : O) :
    LinearMap.lTensor R D.toLinearMap (Algebra.TensorProduct.includeRight (R := ℂ) (A := R) x) =
      Algebra.TensorProduct.includeRight (R := ℂ) (A := R) (D x) := by
  simp

theorem right_alg (c : ℂ) : Algebra.TensorProduct.includeRight (R := ℂ) (A := R) (algebraMap ℂ O c) =
    algebraMap R (R ⊗[ℂ] O) (algebraMap ℂ R c) := by
  rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

theorem tensor_subsingleton [Subsingleton O] (x y : R ⊗[ℂ] O) : x = y := Subsingleton.elim _ _

theorem fst_inl_inr {A : Type} [CommRing A] {n : ℕ} (x : A) (v : Fin n → A) :
    (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v : TrivSqZeroExt A (Fin n → A)).fst = x := by simp

theorem eq_zero_of_inl_inr {A : Type} [CommRing A] {n : ℕ} (x : A) (v : Fin n → A)
    (h : (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v : TrivSqZeroExt A (Fin n → A)) = TrivSqZeroExt.inl x) : v = 0 := by
  simpa using congrArg TrivSqZeroExt.snd h

theorem inl_add_zero {A : Type} [CommRing A] {n : ℕ} (x : A) (v : Fin n → A) (h : ∀ a, v a = 0) :
    (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v : TrivSqZeroExt A (Fin n → A)) = TrivSqZeroExt.inl x := by
  rw [show v = 0 from funext h]; simp

end Gen

variable {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam Empty g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R]
  {et : Hol F₀.V →+* R} {M : Ideal R}

theorem right_cst (hev : ∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) (k : K₀.K) (f : Hol F₀.V) :
    Algebra.TensorProduct.includeRight (R := ℂ) (A := R) (K₀.cst k f) = algebraMap R (R ⊗[ℂ] Hol (K₀.W k)) (et f) := by
  rcases Classical.em (∃ p, p ∈ K₀.W k) with ⟨p, hp⟩ | hW
  · have e : K₀.cst k f = algebraMap ℂ (Hol (K₀.W k)) (f.fn p.1) := Hol.ext_fn fun p' hp' ↦ by
      rw [K₀.fn_cst k f hp', Hol.fn_algebraMap _ hp', show p'.1 = p.1 from funext fun x => x.elim]
    rw [e, hev f p.1 (K₀.base k p hp)]
    exact right_alg _
  · haveI : Subsingleton (Hol (K₀.W k)) := ⟨fun a b ↦ Hol.ext_fn fun p hp ↦ (hW ⟨p, hp⟩).elim⟩
    exact tensor_subsingleton _ _

@[reducible] def objS (hM : IsNilpotent M) (hev : ∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) (k : K₀.K) :
    K₀.DObj et M where
  T :=
    { k := k
      C := R ⊗[ℂ] Hol (K₀.W k)
      alg := ((algebraMap R (R ⊗[ℂ] Hol (K₀.W k))).comp et).toAlgebra
      J := M.map (algebraMap R (R ⊗[ℂ] Hol (K₀.W k)))
      nil := map_nil _ M hM
      ρ := (Algebra.TensorProduct.includeRight (R := ℂ) (A := R)).toRingHom
      ρ_cst := right_cst K₀ hev k }
  alg := Algebra.TensorProduct.leftAlgebra
  compat _ := rfl
  mem _ hd := Ideal.mem_map_of_mem _ hd

def homS (hM : IsNilpotent M) (hev : ∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) {l : Λ} {k k' : K₀.K}
    (h : K₀.le l k' k) : objS K₀ hM hev k ⟶ objS K₀ hM hev k' :=
  ⟨{ φ := letI := (objS K₀ hM hev k).T.alg; letI := (objS K₀ hM hev k').T.alg
      { (Algebra.TensorProduct.map (AlgHom.id ℂ R) (shA h)).toRingHom with commutes' := fun f ↦ map_alg (shA h) (et f) }
     deg := l
     le := h
     mem := map_mem (shA h) M
     close := by
       have e : (Algebra.TensorProduct.map (AlgHom.id ℂ R) (shA h)).toRingHom.comp (objS K₀ hM hev k).T.ρ =
           (objS K₀ hM hev k').T.ρ.comp (sh h) := RingHom.ext fun x ↦ map_right (R := R) (shA h) x
       exact Eq.mpr (congrArg (Close _ _) e) Relation.ReflTransGen.refl },
   map_alg (shA h)⟩

variable {K₀}

@[reducible] def jetD (S : K₀.DObj et M) : K₀.DObj et M where
  T :=
    { k := S.T.k
      C := TrivSqZeroExt S.T.C (Fin g → S.T.C)
      alg := ((TrivSqZeroExt.inlHom S.T.C (Fin g → S.T.C)).comp (algebraMap (Hol F₀.V) S.T.C)).toAlgebra
      J := S.T.J.comap (TrivSqZeroExt.fstHom ℤ S.T.C (Fin g → S.T.C)).toRingHom
      nil := comap_fst_nil _ S.T.nil
      ρ := (TrivSqZeroExt.inlHom S.T.C (Fin g → S.T.C)).comp S.T.ρ
      ρ_cst := fun f ↦ congrArg (TrivSqZeroExt.inlHom S.T.C (Fin g → S.T.C)) (S.T.ρ_cst f) }
  alg := ((TrivSqZeroExt.inlHom S.T.C (Fin g → S.T.C)).comp (algebraMap R S.T.C)).toAlgebra
  compat f := congrArg (TrivSqZeroExt.inlHom S.T.C (Fin g → S.T.C)) (S.compat f)
  mem d hd := S.mem d hd

def jetHom (S : K₀.DObj et M) (ψ : S.T.C →+* TrivSqZeroExt S.T.C (Fin g → S.T.C)) (D : S.T.C → Fin g → S.T.C)
    (hψ : ∀ x, ψ x = TrivSqZeroExt.inl x + TrivSqZeroExt.inr (D x)) (hR : ∀ r a, D (algebraMap R S.T.C r) a = 0)
    (hc : Close (jetD S).T.J (jetD S).T.ρ (ψ.comp S.T.ρ)) : S ⟶ jetD S :=
  ⟨{ φ := letI := (jetD S).T.alg
      { ψ with commutes' := fun f ↦ (hψ _).trans (inl_add_zero _ _ fun a ↦ by rw [S.compat]; exact hR _ a) }
     deg := 0
     le := K₀.le_refl _
     mem := fun c hc ↦ by
       change (ψ c).fst ∈ S.T.J
       rw [hψ, fst_inl_inr]; exact hc
     close := Eq.mpr (congrArg (fun ρ ↦ Close (jetD S).T.J ρ (ψ.comp S.T.ρ))
       (RingHom.ext fun x ↦ congrArg (jetD S).T.ρ (sh_refl (K₀.le_refl _) x))) hc },
   fun d ↦ (hψ _).trans (inl_add_zero _ _ (hR d))⟩

theorem killed {q : Λ →+ R} (s : ∀ S : K₀.DObj et M, S.T.C)
    (key : ∀ {S S' : K₀.DObj et M} (f : S ⟶ S'), s S' - f.1.φ (s S) = algebraMap R S'.T.C (q f.1.deg))
    (S : K₀.DObj et M) (ψ : S.T.C →+* TrivSqZeroExt S.T.C (Fin g → S.T.C)) (D : S.T.C → Fin g → S.T.C)
    (hψ : ∀ x, ψ x = TrivSqZeroExt.inl x + TrivSqZeroExt.inr (D x)) (hR : ∀ r a, D (algebraMap R S.T.C r) a = 0)
    (hD : ∀ h a, D (S.T.ρ h) a = S.T.ρ (dw a h)) : D (s S) = 0 := by
  have e0 := key (jetHom S (TrivSqZeroExt.inlHom _ _) (fun _ ↦ 0) (fun x ↦ (inl_add_zero x _ fun _ ↦ rfl).symm)
    (fun _ _ ↦ rfl) Relation.ReflTransGen.refl)
  have e1 := key (jetHom S ψ D hψ hR (Relation.ReflTransGen.single
    ⟨fun a ↦ TrivSqZeroExt.inr (Pi.single a 1), fun _ ↦ S.T.J.zero_mem, fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _,
      fun h ↦ (hψ _).trans (by
        rw [show D (S.T.ρ h) = fun a ↦ S.T.ρ (dw a h) from funext (hD h)]
        exact tsze_expand _ _)⟩))
  have e2 : ψ (s S) = TrivSqZeroExt.inl (s S) := sub_right_injective (e1.trans e0.symm)
  exact eq_zero_of_inl_inr _ _ ((hψ _).symm.trans e2)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 8000000 in
theorem coboundary_on_charts : ∀ {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam Empty g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : Hol F₀.V →+* R) (M : Ideal R), IsNilpotent M → (∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) → ∀ (q : Λ →+ R), K₀.perClD et M q = 0 → ∃ G : ∀ k, R ⊗[ℂ] Hol (K₀.W k), (∀ k a, LinearMap.lTensor R (dw a).toLinearMap (G k) = 0) ∧ ∀ l k k' (h : K₀.le l k' k), G k' - Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h) (G k) = q l ⊗ₜ[ℂ] 1 := by
  intro g Λ _ F₀ K₀ R _ _ et M hM hev q hq
  obtain ⟨s, hs⟩ := CatCoh.H1.mk_eq_zero.1 hq
  have key : ∀ {S S' : K₀.DObj et M} (f : S ⟶ S'),
      @HSub.hSub S'.T.C S'.T.C S'.T.C _ (s S') (f.1.φ (s S)) = algebraMap R S'.T.C (q f.1.deg) :=
    fun f ↦ congrFun (congrFun (congrFun hs _) _) f
  refine ⟨fun k ↦ s (objS K₀ hM hev k), fun k a ↦ ?_, fun l k k' h ↦ key (homS K₀ hM hev h)⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.SqZeroMove.sqZeroMove (TrivSqZeroExt.inlHom (R ⊗[ℂ] Hol (K₀.W k)) (Fin g → R ⊗[ℂ] Hol (K₀.W k)))
    (fun a ↦ TrivSqZeroExt.inr (Pi.single a 1)) (fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _)
  exact congrFun (killed s key (objS K₀ hM hev k) ψ (fun x a ↦ LinearMap.lTensor R (dw (W := K₀.W k) a).toLinearMap x)
    (fun x ↦ (hψ x).trans (tsze_expand _ _).symm) (fun r a ↦ lTensor_alg _ r) (fun h a ↦ lTensor_right _ h)) a

end GlobalTheory.ChartCobd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassLinearRelationUniqueOfNilpotent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)
  {R : Type} [CommRing R] (et : Hol F.V →+* R) (M : Ideal R)

def perZDLin : (Λ →+ R) →ₗ[R] GlobalTheory.CatCoh.Z1 (K.OD et M) where
  toFun := K.perZD et M
  map_add' q q' := Subtype.ext (funext fun _ ↦ funext fun S' ↦ funext fun f ↦ map_add (algebraMap R S'.T.C) (q f.1.deg) (q' f.1.deg))
  map_smul' r q := Subtype.ext (funext fun _ ↦ funext fun S' ↦ funext fun f ↦
    (map_mul (algebraMap R S'.T.C) r (q f.1.deg)).trans (Algebra.smul_def (A := S'.T.C) r _).symm)

end GlobalTheory.AnPer.Charts


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.AnPer.perClD_relation_unique : ∀ {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : _root_.GlobalTheory.AnPer.Fam Empty g Λ} (K₀ : _root_.GlobalTheory.AnPer.Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : _root_.GlobalTheory.AnPer.Hol F₀.V →+* R) (M : Ideal R), K₀.Rich → (∀ z, z ∈ F₀.V) → IsNilpotent M → (∀ (f : _root_.GlobalTheory.AnPer.Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) → ∀ {io : Type} (S : Finset io) (d : io → R) (q : io → (Λ →+ R)) (q' : Λ →+ R), K₀.perClD et M q' = ∑ i ∈ S, d i • K₀.perClD et M (q i) → ∀ l, q' l = ∑ i ∈ S, d i * q i l := by
  intro g Λ _ F₀ K₀ R _ _ et M hrich hV hnil het io S d q q' hrel l
  let q'' : Λ →+ R := q' - ∑ i ∈ S, d i • q i
  have hq'' : ∀ m, q'' m = q' m - ∑ i ∈ S, d i * q i m := by
    intro m
    simp [q'', smul_eq_mul]
  have hcl : K₀.perClD et M q'' = 0 := by
    have hc : ∀ p : Λ →+ R, K₀.perClD et M p =
        _root_.GlobalTheory.CatCoh.H1.mk _
          (K₀.perZDLin et M p) := fun p => rfl
    simp only [hc] at hrel ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [q'', map_sub, map_sum, map_smul, hrel, sub_self]
  have hG : ∃ G : ∀ k, R ⊗[ℂ] _root_.GlobalTheory.AnPer.Hol (K₀.W k),
      (∀ k a, LinearMap.lTensor R (_root_.GlobalTheory.AnPer.dw (W := K₀.W k) a).toLinearMap (G k) = 0) ∧
      ∀ l k k' (h : K₀.le l k' k), G k' - Algebra.TensorProduct.map (AlgHom.id ℂ R)
        (_root_.GlobalTheory.AnPer.Charts.shA h) (G k) = q'' l ⊗ₜ[ℂ] 1 :=
    _root_.GlobalTheory.ChartCobd.coboundary_on_charts K₀ et M hnil het q'' hcl
  obtain ⟨G, hG0, hGsh⟩ := hG
  have hzero : q'' l = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    let Φ : ∀ k, R ⊗[ℂ] _root_.GlobalTheory.AnPer.Hol (K₀.W k) →ₗ[ℂ]
        _root_.GlobalTheory.AnPer.Hol (K₀.W k) :=
      fun k => (TensorProduct.lid ℂ _).toLinearMap ∘ₗ LinearMap.rTensor _ φ
    have hΦ : ∀ k r h, Φ k (r ⊗ₜ h) = φ r • h := by
      intro k r h
      simp [Φ]
    have hΦd : ∀ k a y, _root_.GlobalTheory.AnPer.dw a (Φ k y) =
        Φ k (LinearMap.lTensor R (_root_.GlobalTheory.AnPer.dw (W := K₀.W k) a).toLinearMap y) := by
      intro k a y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r h =>
        set_option synthInstance.maxHeartbeats 400000 in
          simp [hΦ]
      | add y z hy hz =>
        set_option synthInstance.maxHeartbeats 400000 in
          simp only [map_add (f := _), hy, hz]
    have hΦs : ∀ {m k k'} (h : K₀.le m k' k) y,
        Φ k' (Algebra.TensorProduct.map (AlgHom.id ℂ R)
          (_root_.GlobalTheory.AnPer.Charts.shA h) y) =
        _root_.GlobalTheory.AnPer.Charts.sh h (Φ k y) := by
      intro m k k' h y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r b =>
        set_option synthInstance.maxHeartbeats 400000 in
          simp [hΦ, ← _root_.GlobalTheory.AnPer.Charts.shA_apply]
      | add y z hy hz =>
        set_option synthInstance.maxHeartbeats 400000 in
          simp only [map_add (f := _), hy, hz]
    have hfsh : ∀ m k k' (h : K₀.le m k' k),
        _root_.GlobalTheory.AnPer.Charts.sh h (Φ k (G k)) =
          Φ k' (G k') + K₀.cst k' (algebraMap ℂ _ (-(φ (q'' m)))) := by
      intro m k k' h
      have h1 := congrArg (Φ k') (hGsh m k k' h)
      rw [map_sub, hΦs, hΦ] at h1
      have h2 : K₀.cst k' (algebraMap ℂ _ (-(φ (q'' m)))) =
          -(φ (q'' m) • 1) := by
        unfold _root_.GlobalTheory.AnPer.Charts.cst
        simp [Algebra.algebraMap_eq_smul_one]
      rw [h2, ← h1]
      abel
    obtain ⟨Gf, -, -, hper, hconst⟩ := _root_.GlobalTheory.AnPer.Charts.glue K₀
      hrich (fun k => Φ k (G k)) (by
        intro k k' h
        simp [hfsh 0 k k' h])
    have hc := hconst (fun k a => by rw [hΦd, hG0, map_zero])
    let p : _root_.GlobalTheory.AnPer.Tot Empty g := ((0 : Empty → ℂ), (0 : Fin g → ℂ))
    have hp := hper l (algebraMap ℂ _ (-(φ (q'' l)))) (fun k k' h => hfsh l k k' h) p (hV _)
    have e : Gf (F₀.shift l p) = Gf p := by
      calc Gf (F₀.shift l p) =
          Gf ((F₀.shift l p).1, (F₀.shift l p).2) := rfl
        _ = Gf ((F₀.shift l p).1, 0) := hc _ (hV _) _
        _ = Gf (p.1, 0) := by rw [show (F₀.shift l p).1 = p.1 from funext fun x => x.elim]
        _ = Gf p := rfl
    have hfn : (algebraMap ℂ (_root_.GlobalTheory.AnPer.Hol F₀.V)
        (-(φ (q'' l)))).fn p.1 = -(φ (q'' l)) := by
      unfold _root_.GlobalTheory.AnPer.Hol.fn
      simp [hV]
    rw [e, hfn] at hp
    linear_combination hp
  rw [← sub_eq_zero, ← hq'' l]
  exact hzero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassLinearRelationUniqueOfNilpotentStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodClass_linear_relation_unique_of_nilpotent : ∀ {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam Empty g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : Hol F₀.V →+* R) (M : Ideal R), K₀.Rich → (∀ z, z ∈ F₀.V) → IsNilpotent M → (∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) → ∀ {io : Type} (S : Finset io) (d : io → R) (q : io → (Λ →+ R)) (q' : Λ →+ R), K₀.perClD et M q' = ∑ i ∈ S, d i • K₀.perClD et M (q i) → ∀ l, q' l = ∑ i ∈ S, d i * q i l := by
  first | exact @GlobalTheory.AnPer.perClD_relation_unique | exact GlobalTheory.AnPer.perClD_relation_unique | (intros; apply GlobalTheory.AnPer.perClD_relation_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTaylorAlgHomHolomorphicNilpotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTaylorAlgHomHolomorphicNilpotent
set_option autoImplicit false

open Filter Topology TopologicalSpace

namespace GlobalTheory.AnPer.TaylorHom

open GlobalTheory.AnPer GlobalTheory.PeriodFamily

variable {I : Type} [Fintype I] [DecidableEq I] {R : Type} [CommRing R] [Algebra ℂ R]

theorem fn_add_eventually {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) (f g : Hol V) :
    (f + g).fn =ᶠ[𝓝 0] fun z ↦ f.fn z + g.fn z := by
  filter_upwards [V.isOpen.mem_nhds h0] with q hq using Hol.fn_add f g hq

theorem fn_mul_eventually {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) (f g : Hol V) :
    (f * g).fn =ᶠ[𝓝 0] fun z ↦ f.fn z * g.fn z := by
  filter_upwards [V.isOpen.mem_nhds h0] with q hq using Hol.fn_mul f g hq

theorem fn_algebraMap_eventually {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) (c : ℂ) :
    (algebraMap ℂ (Hol V) c).fn =ᶠ[𝓝 0] fun _ ↦ c := by
  filter_upwards [V.isOpen.mem_nhds h0] with q hq using Hol.fn_algebraMap c hq

theorem taylor_algebraMap (N : ℕ) (t : I → R) {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) (c : ℂ) :
    GlobalTheory.PeriodFamily.taylor N t (algebraMap ℂ (Hol V) c).fn = algebraMap ℂ R c := by
  rw [taylor_congr_germ N t _ _ (fn_algebraMap_eventually h0 c), taylor_const_fun]

noncomputable def taylorHom (N : ℕ) (t : I → R) (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0)
    (V : Opens (I → ℂ)) (h0 : (0 : I → ℂ) ∈ V) : Hol V →ₐ[ℂ] R where
  toFun f := GlobalTheory.PeriodFamily.taylor N t f.fn
  map_one' := by
    have h : (1 : Hol V) = algebraMap ℂ (Hol V) 1 := (map_one _).symm
    change GlobalTheory.PeriodFamily.taylor N t (1 : Hol V).fn = 1
    rw [h, taylor_algebraMap N t h0, map_one]
  map_mul' f g := by
    change GlobalTheory.PeriodFamily.taylor N t (f * g).fn = GlobalTheory.PeriodFamily.taylor N t f.fn * GlobalTheory.PeriodFamily.taylor N t g.fn
    rw [taylor_congr_germ N t _ _ (fn_mul_eventually h0 f g)]
    exact taylor_mul_of_prod_eq_zero N t ht _ _ (f.analytic 0 h0) (g.analytic 0 h0)
  map_zero' := by
    have h : (0 : Hol V) = algebraMap ℂ (Hol V) 0 := (map_zero _).symm
    change GlobalTheory.PeriodFamily.taylor N t (0 : Hol V).fn = 0
    rw [h, taylor_algebraMap N t h0, map_zero]
  map_add' f g := by
    change GlobalTheory.PeriodFamily.taylor N t (f + g).fn = GlobalTheory.PeriodFamily.taylor N t f.fn + GlobalTheory.PeriodFamily.taylor N t g.fn
    rw [taylor_congr_germ N t _ _ (fn_add_eventually h0 f g)]
    exact taylor_add_of_analyticAt N t _ _ (f.analytic 0 h0) (g.analytic 0 h0)
  commutes' c := taylor_algebraMap N t h0 c

end GlobalTheory.AnPer.TaylorHom

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily

theorem GlobalTheory.AnPer.exists_taylor_algHom : ∀ {I : Type} [Fintype I] [DecidableEq I] {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (V : Opens (I → ℂ)), 0 ∈ V → ∃ θ : Hol V →ₐ[ℂ] R, ∀ f, θ f = GlobalTheory.PeriodFamily.taylor N t f.fn := by
  intro I _ _ R _ _ N t ht V h0
  exact ⟨GlobalTheory.AnPer.TaylorHom.taylorHom N t ht V h0, fun f ↦ rfl⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTaylorAlgHomHolomorphicNilpotentStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_taylor_algHom_holomorphic_nilpotent : ∀ {I : Type} [Fintype I] [DecidableEq I] {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (V : Opens (I → ℂ)), 0 ∈ V → ∃ θ : Hol V →ₐ[ℂ] R, ∀ f, θ f = taylor N t f.fn := by
  first | exact @GlobalTheory.AnPer.exists_taylor_algHom | exact GlobalTheory.AnPer.exists_taylor_algHom | (intros; apply GlobalTheory.AnPer.exists_taylor_algHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodConstExt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodConstExt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem period_const_ext : ∀ {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) {B₀ D : Type} [CommRing B₀] [CommRing D] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp B₀} {σ₀ : B₀ →+* Hol F₀.V} (r₀ : GlobalTheory.AnPer.Real K₀ s₀ σ₀) {J : Ideal D} (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io) (j : B₀ →+* D) (φ₀ : X₀ ⟶ X₀) (n : IsMor (dp0 B₀) s₀ dl s' j φ₀), φ₀ = 𝟙 X₀ → (∀ b, et (σ₀ b) = io (j b)) → ∀ (c : FirstDeRham s₀) (per : Λ →+ Hol F₀.V), r₀.coef.pull1 c = K₀.perCl per → (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (et.toAddMonoidHom.comp per) := by
  intro I₀ _ g Λ _ F₀ K₀ R _ et M B₀ D _ _ X₀ s₀ σ₀ r₀ J dl s' π io H j φ₀ n hφ hj c per hc
  refine GlobalTheory.T.period_over_ring_restrict_family_class K₀ K₀ et M et id (fun h ↦ h) (fun _ ↦ RingHom.id _) (fun S ↦ S.T.ρ)
    (fun S f ↦ (S.T.ρ_cst f).trans (S.compat f)) (fun S h ↦ ?_) (fun S S' f ↦ Charts.Hom.close f.1)
    r₀ r₀ dl H j φ₀ n hj (fun k ↦ ?_) c per hc
  · exact (sub_self (S.T.ρ h)).symm ▸ S.T.J.zero_mem
  · subst hφ
    have e : spMap (RingHom.id (Hol (K₀.W k))) = 𝟙 _ := Spec.map_id _
    exact (congrArg (· ≫ r₀.x k) e).trans ((Category.id_comp _).trans (Category.comp_id _).symm)

end GlobalTheory.AnPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodConstExtStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefD_pull1_eq_perClD_of_pull1_eq_perCl : ∀ {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) {B₀ D : Type} [CommRing B₀] [CommRing D] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp B₀} {σ₀ : B₀ →+* Hol F₀.V} (r₀ : GlobalTheory.AnPer.Real K₀ s₀ σ₀) {J : Ideal D} (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io) (j : B₀ →+* D) (φ₀ : X₀ ⟶ X₀) (n : IsMor (dp0 B₀) s₀ dl s' j φ₀), φ₀ = 𝟙 X₀ → (∀ b, et (σ₀ b) = io (j b)) → ∀ (c : FirstDeRham s₀) (per : Λ →+ Hol F₀.V), r₀.coef.pull1 c = K₀.perCl per → (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (et.toAddMonoidHom.comp per) := by
  first | exact @GlobalTheory.AnPer.period_const_ext | exact GlobalTheory.AnPer.period_const_ext | (intros; apply GlobalTheory.AnPer.period_const_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParameterTaylorExpansionHomFibreDerivation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParameterTaylorExpansionHomFibreDerivation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnPer

variable {I : Type} [Fintype I] [DecidableEq I] {g : ℕ}

def slTayCoef {W : Opens (Tot I g)} (h : Hol W) (k : ℕ) (s : Fin k → I) (p : Tot Empty g) : ℂ :=
  (k.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ k (fun z ↦ h.fn (z, p.2)) 0 fun b ↦ Pi.single (s b) 1

theorem slTayCoef_analytic {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (h : Hol W) (k : ℕ) (s : Fin k → I) :
    AnalyticOnNhd ℂ (slTayCoef h k s) W₀ := fun p hp ↦ by
  have hA : AnalyticAt ℂ h.fn ((0 : I → ℂ), p.2) := h.analytic _ (hW p hp)
  have hG := (analyticAt_iteratedFDeriv_slice_and_fderiv h.fn p.2 k (fun b ↦ Pi.single (s b) 1) hA).1
  exact analyticAt_const.mul (hG.comp analyticAt_snd)

def slTayHol {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (h : Hol W) (k : ℕ) (s : Fin k → I) : Hol W₀ :=
  Hol.mk (slTayCoef h k s) (slTayCoef_analytic hW h k s)

theorem isTay_expand {R : Type} [CommRing R] [Algebra ℂ R] {N : ℕ} {t : I → R} {W : Opens (Tot I g)}
    {W₀ : Opens (Tot Empty g)} (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W)
    {ρ : Hol W →+* R ⊗[ℂ] Hol W₀} (hρ : IsTay N t ρ) (h : Hol W) :
    ρ h = ∑ k ∈ Finset.range (N + 1), ∑ s : Fin k → I, (∏ b, t (s b)) ⊗ₜ[ℂ] slTayHol hW h k s := by
  refine tensor_hol_ext_of_values W₀ R _ _ fun p hp ↦ ?_
  have e := hρ h p hp
  change evT R p hp (ρ h) = evT R p hp _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  unfold GlobalTheory.PeriodFamily.taylor
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, Hol.ev_apply, slTayHol, Hol.fn_mk _ _ hp,
    Algebra.smul_def, mul_comm]
  rfl

theorem dw_slTayHol {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (a : Fin g) (h : Hol W) (k : ℕ) (s : Fin k → I) :
    dw a (slTayHol hW h k s) = slTayHol hW (dw a h) k s := by
  refine Hol.ext_fn fun p hp ↦ ?_
  have hA : AnalyticAt ℂ h.fn ((0 : I → ℂ), p.2) := h.analytic _ (hW p hp)
  obtain ⟨hG, hD⟩ := analyticAt_iteratedFDeriv_slice_and_fderiv h.fn p.2 k (fun b ↦ Pi.single (s b) 1) hA
  have e1 : slTayCoef h k s = (fun w : Fin g → ℂ ↦ (k.factorial : ℂ)⁻¹ *
      iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 fun b ↦ Pi.single (s b) 1) ∘ Prod.snd := rfl
  have hG' : DifferentiableAt ℂ (fun w : Fin g → ℂ ↦ (k.factorial : ℂ)⁻¹ *
      iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 fun b ↦ Pi.single (s b) 1) p.2 :=
    hG.differentiableAt.const_mul _
  have hev : (fun z : I → ℂ ↦ fderiv ℂ h.fn (z, p.2) ((0 : I → ℂ), Pi.single a 1)) =ᶠ[𝓝 0]
      fun z ↦ (dw a h).fn (z, p.2) := by
    have hc : Continuous fun z : I → ℂ ↦ ((z, p.2) : Tot I g) := continuous_id.prodMk continuous_const
    filter_upwards [hc.continuousAt.eventually_mem (W.isOpen.mem_nhds (hW p hp))] with z hz
    rw [dw, Hol.fn_der _ _ hz]
  rw [slTayHol, slTayHol, Hol.fn_mk _ _ hp, dw, Hol.fn_der _ _ hp,
    Hol.fderiv_fn_congr _ (F := slTayCoef h k s) (fun q hq ↦ Hol.fn_mk _ _ hq) hp, e1,
    fderiv_comp p hG' differentiableAt_snd, fderiv_snd,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', fderiv_const_mul hG.differentiableAt,
    ContinuousLinearMap.smul_apply, hD, smul_eq_mul]
  unfold slTayCoef
  congr 1
  exact (Filter.EventuallyEq.iteratedFDeriv ℂ hev k).eq_of_nhds ▸ rfl

theorem isTay_dw_lTensor : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type}
    [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)),
    (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) →
    ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (a : Fin g) (h : Hol W),
      ρ (dw a h) = LinearMap.lTensor R (dw (W := W₀) a).toLinearMap (ρ h) := by
  intro I _ _ g R _ _ N t W W₀ hW ρ hρ a h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [isTay_expand hW hρ (dw a h), isTay_expand hW hρ h, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [LinearMap.lTensor_tmul, ← dw_slTayHol hW a h k s]
  rfl

end GlobalTheory.AnPer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParameterTaylorExpansionHomFibreDerivationStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isParameterTaylorExpansionHom_fibreDerivation :
    ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R]
      (N : ℕ) (t : I → R) (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)),
      (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) →
      ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (a : Fin g) (h : Hol W),
        ρ (dw a h) = LinearMap.lTensor R (dw (W := W₀) a).toLinearMap (ρ h) := by
  intro I _ _ g R _ _ N t W W₀ hW ρ hρ a h
  have expand := isTay_expand hW hρ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [expand (dw a h), expand h, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [LinearMap.lTensor_tmul, ← dw_slTayHol hW a h k s]
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParameterTaylorExpansionHomApplyOfParamOnly
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParameterTaylorExpansionHomApplyOfParamOnly
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem isTay_apply_of_fn_eq_param : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (h : Hol W) (f : (I → ℂ) → ℂ), (∀ p ∈ W, h.fn p = f p.1) → ρ h = GlobalTheory.PeriodFamily.taylor N t f ⊗ₜ[ℂ] 1 := by
  intro I _ _ g R _ _ N t W W₀ h0 ρ hρ h f hf
  apply GlobalTheory.tensor_hol_ext_of_values W₀ R
  intro p hp
  have e1 := hρ h p hp
  have e2 : (fun z : I → ℂ ↦ h.fn (z, p.2)) =ᶠ[𝓝 0] f := by
    have hc : Continuous (fun z : I → ℂ ↦ ((z, p.2) : Tot I g)) := continuous_id.prodMk continuous_const
    have hm : ∀ᶠ z in 𝓝 (0 : I → ℂ), ((z, p.2) : Tot I g) ∈ W :=
      hc.continuousAt.preimage_mem_nhds (W.isOpen.mem_nhds (h0 p hp))
    filter_upwards [hm] with z hz using hf _ hz
  have e3 := (GlobalTheory.PeriodFamily.taylor_formal_properties (D := R) N t).2.2.2.1 _ _ e2
  change evT R p hp (ρ h) = evT R p hp (GlobalTheory.PeriodFamily.taylor N t f ⊗ₜ[ℂ] (1 : Hol W₀))
  rw [e1, e3]
  simp [evT, Algebra.TensorProduct.lift_tmul]

end GlobalTheory.AnPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParameterTaylorExpansionHomApplyOfParamOnlyStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isParameterTaylorExpansionHom_apply_of_param_only : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (h : Hol W) (f : (I → ℂ) → ℂ), (∀ p ∈ W, h.fn p = f p.1) → ρ h = taylor N t f ⊗ₜ[ℂ] 1 := by
  first | exact @GlobalTheory.AnPer.isTay_apply_of_fn_eq_param | exact GlobalTheory.AnPer.isTay_apply_of_fn_eq_param | (intros; apply GlobalTheory.AnPer.isTay_apply_of_fn_eq_param <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorRestrictionSubMemIdealMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorRestrictionSubMemIdealMap
open TopologicalSpace TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnPer

section General

variable {R H : Type} [CommRing R] [Algebra ℂ R] [CommRing H] [Algebra ℂ H]

def redCoef (π : R →ₐ[ℂ] ℂ) : R ⊗[ℂ] H →ₐ[ℂ] H :=
  Algebra.TensorProduct.lift ((Algebra.ofId ℂ H).comp π) (AlgHom.id ℂ H) (fun _ _ ↦ Commute.all _ _)

theorem redCoef_tmul (π : R →ₐ[ℂ] ℂ) (d : R) (y : H) :
    redCoef π (d ⊗ₜ[ℂ] y) = algebraMap ℂ H (π d) * y := by
  simp [redCoef, Algebra.TensorProduct.lift_tmul]

theorem sub_redCoef_mem (π : R →ₐ[ℂ] ℂ) (x : R ⊗[ℂ] H) :
    x - 1 ⊗ₜ[ℂ] redCoef π x ∈
      (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] H) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d y =>
    rw [redCoef_tmul]
    have e : d ⊗ₜ[ℂ] y - (1 : R) ⊗ₜ[ℂ] (algebraMap ℂ H (π d) * y) =
        (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] H) (d - algebraMap ℂ R (π d)) * ((1 : R) ⊗ₜ[ℂ] y) := by
      rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
        TensorProduct.sub_tmul, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul, TensorProduct.smul_tmul]
    rw [e]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes]
    simp
  | add x y hx hy =>
    have e : x + y - 1 ⊗ₜ[ℂ] redCoef π (x + y) = (x - 1 ⊗ₜ[ℂ] redCoef π x) + (y - 1 ⊗ₜ[ℂ] redCoef π y) := by
      rw [map_add (f := _), TensorProduct.tmul_add]; abel
    rw [e]; exact Ideal.add_mem _ hx hy

end General

theorem fn_redCoef {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} {R : Type} [CommRing R]
    [Algebra ℂ R] (π : R →ₐ[ℂ] ℂ) (x : R ⊗[ℂ] Hol W) {p : E} (hp : p ∈ W) :
    (redCoef π x).fn p = π (evT R p hp x) := by
  rw [← Hol.ev_apply p hp]
  change ((Hol.ev p hp).comp (redCoef π)) x = (π.comp (evT R p hp)) x
  congr 1
  refine Algebra.TensorProduct.ext' fun d y ↦ ?_
  simp only [AlgHom.comp_apply, redCoef_tmul, evT, Algebra.TensorProduct.lift_tmul, map_mul, AlgHom.commutes,
    AlgHom.id_apply, Algebra.ofId_apply]
  simp

theorem taylor_red {I : Type} [Fintype I] [DecidableEq I] {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ)
    (t : I → R) (π : R →ₐ[ℂ] ℂ) (ht : ∀ i, π (t i) = 0) (f : (I → ℂ) → ℂ) :
    π (GlobalTheory.PeriodFamily.taylor N t f) = f 0 := by
  have h := GlobalTheory.PeriodFamily.taylor_sub_value_mem_span N t f
  have hle : Ideal.span (Set.range t) ≤ RingHom.ker π := by
    rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact ht i
  have := hle h
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at this
  simpa using this

theorem taylor_reduces_to_slice : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (π : R →ₐ[ℂ] ℂ), (∀ i, π (t i) = 0) → ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (h : Hol W) (h₀ : Hol W₀), (∀ p ∈ W₀, h₀.fn p = h.fn (0, p.2)) → ρ h - 1 ⊗ₜ[ℂ] h₀ ∈ (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol W₀) := by
  intro I _ _ g R _ _ N t π ht W W₀ _ ρ hρ h h₀ hh₀
  have hq : redCoef π (ρ h) = h₀ := Hol.ext_fn fun p hp ↦ by
    rw [fn_redCoef π _ hp, hρ h p hp, taylor_red N t π ht, hh₀ p hp]
  have := sub_redCoef_mem (H := Hol W₀) π (ρ h)
  rwa [hq] at this

end GlobalTheory.AnPer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorRestrictionSubMemIdealMapStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_restriction_sub_mem_ideal_map : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (π : R →ₐ[ℂ] ℂ), (∀ i, π (t i) = 0) → ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (h : Hol W) (h₀ : Hol W₀), (∀ p ∈ W₀, h₀.fn p = h.fn (0, p.2)) → ρ h - 1 ⊗ₜ[ℂ] h₀ ∈ (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol W₀) := by
  first | exact @GlobalTheory.AnPer.taylor_reduces_to_slice | exact GlobalTheory.AnPer.taylor_reduces_to_slice | (intros; apply GlobalTheory.AnPer.taylor_reduces_to_slice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPeriodEqPeriodOverThickening
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GaussManinTaylor

theorem prod_zero_of_pow_eq_bot {R : Type} [CommRing R] (J : Ideal R) (n₀ : ℕ) (h : J ^ n₀ = ⊥) (N' : ℕ)
    (hN : n₀ ≤ N' + 1) (s : Fin (N' + 1) → R) (hs : ∀ a, s a ∈ J) : ∏ a, s a = 0 := by
  have h1 : ∏ a, s a ∈ ∏ _a ∈ (Finset.univ : Finset (Fin (N' + 1))), J := Ideal.prod_mem_prod (fun a _ ↦ hs a)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  have h2 := Ideal.pow_le_pow_right hN h1
  rw [h] at h2
  simpa using h2

end GlobalTheory.GaussManinTaylor

open GlobalTheory.GaussManinTaylor in
theorem GlobalTheory.GaussManinTaylor.taylor_period_eq_period_over_thickening : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} {B D : Type} [CommRing B] [CommRing D] [Algebra ℂ D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp ℂ} {σ : B →+* Hol F.V} (e : Unif F s σ) (u₀ : Unif F₀ s₀ (algebraMap ℂ (Hol F₀.V))), X.IsSeparated → X₀.IsSeparated → 0 ∈ F.V → (∀ z, z ∈ F₀.V) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (φ₀ : X₀ ⟶ X), (∀ p : Tot Empty g, u₀.E p ≫ φ₀ = e.E (0, p.2)) → ∀ (π : D →ₐ[ℂ] ℂ), IsNilpotent (RingHom.ker π) → ∀ {J : Ideal D} (dl : DividedPowers J), (∀ d ∈ J, π d = 0) → ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (j : B →+* D), (∀ b, j b = GlobalTheory.PeriodFamily.taylor N t (σ b).fn) → ∀ (s' : X₀ ⟶ Sp D), s' = s₀ ≫ spMap (π : D →+* ℂ) → ∀ (n : IsMor (dp0 B) s dl s' j φ₀) (ψ : X₀ ⟶ X₀) (k : IsMor (dp0 ℂ) s₀ dl s' (algebraMap ℂ D) ψ), ψ = 𝟙 X₀ → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod e c per → ∀ {io : Type} (S : Finset io) (d : io → D) (a : io → FirstDeRham s₀) (p : io → Λ → ℂ) (p' : io → (Λ →+ Hol F₀.V)), (∀ i l, p' i l = algebraMap ℂ _ (p i l)) → (∀ i, IsPeriod u₀ (a i) (p' i)) → n.pull1 c = ∑ i ∈ S, d i • k.pull1 (a i) → ∀ l, ∑ i ∈ S, d i * algebraMap ℂ D (p i l) = GlobalTheory.PeriodFamily.taylor N t (per l).fn := by
  intro I _ _ g Λ _ F F₀ B D _ _ _ X X₀ s s₀ σ e u₀ hX hX₀ h0V hV₀ hτ φ₀ hφ₀ π hπ J dl hJ N t ht hprod j hj s' hs' n ψ kk hψ c per hper ιo S d a p p' hp' hpa hsum l

  obtain ⟨R, _, _, io, π', m, hinj, hπ', hnil, hm0, hmm, hmsum⟩ :=
    GlobalTheory.SquareZeroSum.exists_sum_sq_zero N D π t hπ ht hprod
  set t' : I → R := fun i ↦ ∑ j, m j i with ht'def
  have ht' : (fun i ↦ io (t i)) = t' := funext hmsum
  have hprod' : ∀ s : Fin (N + 1) → I, ∏ a, t' (s a) = 0 := by
    intro s
    rw [← ht']
    simp only
    rw [← map_prod, hprod, map_zero]
  obtain ⟨n₀, hn₀⟩ := hnil
  set N' := N + n₀ with hN'
  have hker : ∀ s : Fin (N' + 1) → R, (∀ a, s a ∈ RingHom.ker (π' : R →+* ℂ)) → ∏ a, s a = 0 :=
    fun s hs ↦ prod_zero_of_pow_eq_bot _ n₀ hn₀ N' (by omega) s hs
  have ht'ker : ∀ i, t' i ∈ RingHom.ker (π' : R →+* ℂ) := fun i ↦ by
    have h1 : io (t i) = t' i := congrFun ht' i
    rw [RingHom.mem_ker, ← h1]
    change π' (io (t i)) = 0
    rw [hπ', ht]
  have hprodN' : ∀ s : Fin (N' + 1) → I, ∏ a, t' (s a) = 0 := fun s ↦ hker _ fun a ↦ ht'ker (s a)

  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_taylor_algHom_holomorphic_nilpotent N' t' hprodN' F.V h0V
  have hθio : ∀ f : Hol F.V, θ f = io (GlobalTheory.PeriodFamily.taylor N t f.fn) := by
    intro f
    rw [hθ, GlobalTheory.PeriodFamily.taylor_eq_of_le N t' hprod' N' (by omega),
      (GlobalTheory.PeriodFamily.taylor_formal_properties N t).2.2.2.2.1 R io f.fn, ht']

  have hdef : (default : Empty → ℂ) ∈ F₀.V := hV₀ _
  obtain ⟨K₀, K, ka, hRich, hU₀, hU, hmemk, hka⟩ := GlobalTheory.T.exists_small_chart_pair_along_linear_map u₀ e (fun _ ↦ (0 : I → ℂ))
    (fun _ _ ↦ analyticAt_const) (fun _ _ ↦ h0V) (LinearMap.id) (AddMonoidHom.id Λ)
    (fun l z _ ↦ (hτ l z).symm)
  have hmem0 : ∀ k, ∀ q ∈ K₀.W k, (((0 : I → ℂ), q.2) : Tot I g) ∈ K.W (ka k) := fun k q hq ↦ hmemk k q hq
  have hka' : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k) := fun h ↦ hka _ _ _ h
  obtain ⟨r₀, hr₀, -⟩ := GlobalTheory.T.exists_analyticChartsRealization_of_affine u₀ hX₀ K₀ hU₀
  obtain ⟨r, hr, -⟩ := GlobalTheory.T.exists_analyticChartsRealization_of_affine e hX K hU
  have han : AnalyticOnNhd ℂ (fun q : Tot Empty g ↦ (((0 : I → ℂ), q.2) : Tot I g)) ⊤ :=
    fun _ _ ↦ analyticAt_const.prod analyticAt_snd
  let res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k) := fun k ↦
    (Hol.comap (fun q : Tot Empty g ↦ (((0 : I → ℂ), q.2) : Tot I g)) (fun q _ ↦ han q trivial) (hmem0 k)).toRingHom
  have hres : ∀ k (h : Hol (K.W (ka k))) {q : Tot Empty g}, q ∈ K₀.W k → (res k h).fn q = h.fn ((0 : I → ℂ), q.2) :=
    fun k h q hq ↦ Hol.fn_comap _ _ _ h hq

  choose ρ hρ using fun k ↦ GlobalTheory.T.exists_ringHom_isTay_of_slice_zero N' t' hprodN' (K.W (ka k)) (K₀.W k) (hmem0 k)
  let M : Ideal R := RingHom.ker (π' : R →+* ℂ)
  let et : Hol F₀.V →ₐ[ℂ] R := (Algebra.ofId ℂ R).comp (Hol.ev default hdef)
  have hcst : ∀ k f, ρ k (K.cst (ka k) f) = θ.toRingHom f ⊗ₜ[ℂ] 1 := fun k f ↦ by
    rw [GlobalTheory.T.isParameterTaylorExpansionHom_apply_of_param_only N' t' _ _ (hmem0 k) (ρ k) (hρ k) _ f.fn (fun q hq ↦ Charts.fn_cst _ _ _ hq)]
    exact congrArg (· ⊗ₜ[ℂ] (1 : Hol (K₀.W k))) (hθ f).symm
  have hdw : ∀ k (a : Fin g) (h : Hol (K.W (ka k))), ρ k (dw a h) = LinearMap.lTensor R (dw (W := K₀.W k) a).toLinearMap (ρ k h) := fun k a h ↦
    GlobalTheory.T.isParameterTaylorExpansionHom_fibreDerivation N' t' _ _ (hmem0 k) (ρ k) (hρ k) a h
  have hclose : ∀ l k' k (h : K₀.le l k' k), Close (M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k'))) ((ρ k').comp (Charts.sh (hka' h))) ((Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h)).toRingHom.comp (ρ k)) := by
    intro l k' k h
    have hρk := hρ k
    have hρk' := hρ k'
    rw [ht'def] at hρk hρk'
    exact GlobalTheory.T.close_taylor_shift_alt K K₀ M N' hker N m (fun j i ↦ hm0 j i) hmm hτ l (ka k) (ka k') k k' (hka' h) h (hmem0 k') (ρ k) (ρ k') hρk hρk'
  have hred : ∀ k h, ρ k h - 1 ⊗ₜ[ℂ] res k h ∈ M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k)) :=
    fun k h ↦ GlobalTheory.T.taylor_restriction_sub_mem_ideal_map N' t' π' (fun i ↦ ht'ker i) _ _ (hmem0 k) (ρ k) (hρ k) h (res k h) (fun q hq ↦ hres k h hq)
  obtain ⟨ρ', hρ'1, hρ'2, hρ'3⟩ := GlobalTheory.T.exists_points_translationFamilyCharts_thickenings K K₀ et M θ.toRingHom ka hka' ρ hcst hdw hclose res hred
  have hetc : ∀ x : ℂ, et (algebraMap ℂ (Hol F₀.V) x) = algebraMap ℂ R x := fun x ↦ et.commutes x
  have H : IsOver (et : Hol F₀.V →+* R) M s₀ (algebraMap ℂ (Hol F₀.V)) J s' (π : D →+* ℂ) (io : D →+* R) :=
    { w := hs'
      mem := fun d hd ↦ by
        rw [RingHom.mem_ker]
        change π' (io d) = 0
        rw [hπ', hJ d hd]
      red := fun d ↦ by
        rw [RingHom.mem_ker, map_sub]
        change π' (io d) - π' (et (algebraMap ℂ (Hol F₀.V) (π d))) = 0
        rw [hetc, AlgHom.commutes, hπ']
        simp }
  have hpt : ∀ k, spMap (res k) ≫ r.x (ka k) = r₀.x k ≫ φ₀ := fun k ↦ by
    refine GlobalTheory.T.holomorphicPoint_ext_of_isSeparated (K₀.W k) hX _ _ (fun q hq ↦ ?_)
    have hq' := hmem0 k q hq
    have hev : (Hol.ev q hq).toRingHom.comp (res k) = (Hol.ev (((0 : I → ℂ), q.2) : Tot I g) hq').toRingHom :=
      RingHom.ext fun h ↦ by
        change Hol.ev q hq (res k h) = Hol.ev _ hq' h
        rw [Hol.ev_apply, Hol.ev_apply, hres k h hq]
    rw [← Category.assoc, ← GlobalTheory.Cris.spMap_comp, hev, hr (ka k) _ hq', ← Category.assoc, hr₀ k q hq, hφ₀ q]
  have hθj : ∀ b, θ.toRingHom (σ b) = io (j b) := fun b ↦ by
    rw [hj]
    exact hθio (σ b)
  have hfam := GlobalTheory.T.period_over_ring_restrict_family_class K K₀ (et : Hol F₀.V →+* R) M θ.toRingHom ka hka' res ρ' hρ'1 hρ'2 hρ'3 r r₀ dl H j φ₀ n hθj hpt c per (hper K r hr)
  have hfib : ∀ i, (r₀.coefD dl H).pull1 (kk.pull1 (a i)) = K₀.perClD (et : Hol F₀.V →+* R) M ((et : Hol F₀.V →+* R).toAddMonoidHom.comp (p' i)) :=
    fun i ↦ GlobalTheory.T.coefD_pull1_eq_perClD_of_pull1_eq_perCl K₀ (et : Hol F₀.V →+* R) M r₀ dl H (algebraMap ℂ D) ψ kk hψ
      (fun b ↦ by
        change et (algebraMap ℂ (Hol F₀.V) b) = io (algebraMap ℂ D b)
        rw [hetc, AlgHom.commutes]) (a i) (p' i) (hpa i K₀ r₀ hr₀)
  have hmain := congrArg (r₀.coefD dl H).pull1 hsum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hfam, map_sum] at hmain
  simp only [map_smulₛₗ, hfib] at hmain
  have het : ∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, (et : Hol F₀.V →+* R) f = algebraMap ℂ R (f.fn z) := fun f z hz ↦ by
    have : z = default := funext fun x => x.elim
    subst this
    change algebraMap ℂ R (Hol.ev default hdef f) = _
    rw [Hol.ev_apply]
  have hdu := GlobalTheory.T.periodClass_linear_relation_unique_of_nilpotent K₀ (et : Hol F₀.V →+* R) M hRich hV₀ ⟨n₀, hn₀⟩ het S _ _ _ hmain l
  apply hinj
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← hθio]
  refine Eq.trans ?_ hdu.symm
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change io (d i * algebraMap ℂ D (p i l)) = io (d i) * et (p' i l)
  rw [map_mul, AlgHom.commutes, hp', hetc]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPeriodEqPeriodOverThickeningStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_period_eq_period_over_thickening_alt : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} {B D : Type} [CommRing B] [CommRing D] [Algebra ℂ D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp ℂ} {σ : B →+* Hol F.V} (e : Unif F s σ) (u₀ : Unif F₀ s₀ (algebraMap ℂ (Hol F₀.V))), X.IsSeparated → X₀.IsSeparated → 0 ∈ F.V → (∀ z, z ∈ F₀.V) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (φ₀ : X₀ ⟶ X), (∀ p : Tot Empty g, u₀.E p ≫ φ₀ = e.E (0, p.2)) → ∀ (π : D →ₐ[ℂ] ℂ), IsNilpotent (RingHom.ker π) → ∀ {J : Ideal D} (dl : DividedPowers J), (∀ d ∈ J, π d = 0) → ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (j : B →+* D), (∀ b, j b = taylor N t (σ b).fn) → ∀ (s' : X₀ ⟶ Sp D), s' = s₀ ≫ spMap (π : D →+* ℂ) → ∀ (n : IsMor (dp0 B) s dl s' j φ₀) (ψ : X₀ ⟶ X₀) (k : IsMor (dp0 ℂ) s₀ dl s' (algebraMap ℂ D) ψ), ψ = 𝟙 X₀ → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod e c per → ∀ {io : Type} (S : Finset io) (d : io → D) (a : io → FirstDeRham s₀) (p : io → Λ → ℂ) (p' : io → (Λ →+ Hol F₀.V)), (∀ i l, p' i l = algebraMap ℂ _ (p i l)) → (∀ i, IsPeriod u₀ (a i) (p' i)) → n.pull1 c = ∑ i ∈ S, d i • k.pull1 (a i) → ∀ l, ∑ i ∈ S, d i * algebraMap ℂ D (p i l) = taylor N t (per l).fn := by
  first | exact @GlobalTheory.GaussManinTaylor.taylor_period_eq_period_over_thickening | exact GlobalTheory.GaussManinTaylor.taylor_period_eq_period_over_thickening | (intros; apply GlobalTheory.GaussManinTaylor.taylor_period_eq_period_over_thickening <;> assumption)
end

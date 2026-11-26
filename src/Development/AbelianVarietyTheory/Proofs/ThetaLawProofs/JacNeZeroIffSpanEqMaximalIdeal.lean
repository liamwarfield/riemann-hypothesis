module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KaFormHomogeneous
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.JacNeZeroIffSpanEqMaximalIdeal
noncomputable section

namespace GlobalTheory.JacGen

section Algebra

open IsLocalRing

theorem det_ne_zero_iff_span_eq {K S : Type} [Field K] [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [Algebra K S] {n : ℕ} (u : S →ₐ[K] K) (D : Fin n → S →ₗ[K] K)
    (hD : ∀ k a b, D k (a * b) = u a * D k b + u b * D k a)
    (hinj : ∀ c : Fin n → K, (∀ a, ∑ k, D k a * c k = 0) → c = 0)
    (hsurj : ∀ δ : S →ₗ[K] K, (∀ a b, δ (a * b) = u a * δ b + u b * δ a) →
      ∃ c : Fin n → K, ∀ a, δ a = ∑ k, D k a * c k)
    (f : Fin n → S) (hf : ∀ i, u (f i) = 0) :
    (Matrix.of fun i k => D k (f i)).det ≠ 0 ↔ Ideal.span (Set.range f) = maximalIdeal S := by
  have hker : RingHom.ker u = maximalIdeal S := eq_maximalIdeal
    (RingHom.ker_isMaximal_of_surjective u fun a => ⟨algebraMap K S a, u.commutes a⟩)
  have hmem : ∀ a, a ∈ maximalIdeal S ↔ u a = 0 := fun a => by rw [← hker, RingHom.mem_ker]
  have hsub : ∀ a, a - algebraMap K S (u a) ∈ maximalIdeal S := fun a => by
    simp [hmem]
  have hle : Ideal.span (Set.range f) ≤ maximalIdeal S :=
    Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact (hmem _).2 (hf i))
  constructor
  · intro h
    refine le_antisymm hle (Submodule.le_of_le_smul_of_le_jacobson_bot
      (IsNoetherian.noetherian _) (maximalIdeal_le_jacobson _) fun a ha => ?_)
    by_contra hn
    obtain ⟨l, hl, hl0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
      (p := (Ideal.span (Set.range f) ⊔ maximalIdeal S • maximalIdeal S).restrictScalars K) hn inferInstance
    have hz : ∀ b ∈ Ideal.span (Set.range f) ⊔ maximalIdeal S • maximalIdeal S, l b = 0 := fun b hb =>
      (Submodule.mem_bot K).1 (hl0 ▸ Submodule.mem_map_of_mem hb)
    let δ : S →ₗ[K] K := l ∘ₗ (LinearMap.id - (Algebra.linearMap K S ∘ₗ u.toLinearMap))
    have hδ : ∀ b, δ b = l (b - algebraMap K S (u b)) := fun b => rfl
    obtain ⟨c, hc⟩ := hsurj δ fun a b => by
      have h0 := hz _ (Submodule.mem_sup_right (Submodule.smul_mem_smul (hsub a) (hsub b)))
      rw [hδ, hδ, hδ, ← smul_eq_mul (u a), ← smul_eq_mul (u b), ← map_smul, ← map_smul, ← map_add (f := _),
        ← sub_eq_zero, ← map_sub, ← h0]
      congr 1
      rw [smul_eq_mul]
      simp only [Algebra.smul_def, map_mul]
      ring
    have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero h (funext fun i => by
      have := hc (f i)
      rw [hδ, hf, map_zero, sub_zero,
        hz _ (Submodule.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))] at this
      exact this.symm)
    have := hc a
    rw [hδ, (hmem a).1 ha, map_zero, sub_zero, hc0] at this
    exact hl (by simpa using this)
  · intro h h0
    obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    refine hc (hinj c fun a => ?_)
    have h1 : ∀ k, D k 1 = 0 := fun k => by simpa using hD k 1 1
    have key : ∀ b ∈ Ideal.span (Set.range f), ∑ k, D k b * c k = 0 := fun b hb => by
      obtain ⟨r, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hb
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, hD, hf, zero_mul, add_zero, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Finset.mul_sum]
      exact mul_eq_zero_of_right _ (congrFun hc0 i)
    have := key _ (h ▸ hsub a)
    simpa [Algebra.algebraMap_eq_smul_one, h1] using this

end Algebra

section Group

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory.SqZero GlobalTheory.LieComb IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

variable {K : Type} [Field K] {G : Over (Spec (CommRingCat.of K))}

theorem isLocalRing_trivSqZeroExt (n : ℕ) : IsLocalRing (TrivSqZeroExt K (Fin n → K)) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact isUnit_or_isUnit_one_sub_self _

theorem exists_factor {y : G.left} [Algebra K (G.left.presheaf.stalk y)]
    (j : sp (R₀ := K) (G.left.presheaf.stalk y) ⟶ G) (hj : j.left = G.left.fromSpecStalk y)
    {T : Type} [CommRing T] [IsLocalRing T] [Algebra K T] (w : sp (R₀ := K) T ⟶ G)
    (hw : w.left (closedPoint T) = y) : ∃ φ : G.left.presheaf.stalk y →ₐ[K] T, spMap φ ≫ j = w := by
  obtain ⟨φ, hφ⟩ : ∃ φ : G.left.presheaf.stalk y ⟶ .of T, Spec.map φ ≫ G.left.fromSpecStalk y = w.left := by
    subst hw
    exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of T) w.left⟩
  have h : CommRingCat.ofHom (algebraMap K (G.left.presheaf.stalk y)) ≫ φ =
      CommRingCat.ofHom (algebraMap K T) := by
    apply Spec.map_injective
    have h1 := Over.w j
    have h2 := Over.w w
    rw [hj] at h1
    rw [← hφ] at h2
    rw [Spec.map_comp]
    exact (congrArg (Spec.map φ ≫ ·) h1.symm).trans ((Category.assoc _ _ _).symm.trans h2)
  refine ⟨{ φ.hom with commutes' := fun a => congrArg (fun q => q.hom a) h }, ?_⟩
  apply Over.OverMorphism.ext
  rw [Over.comp_left, hj]
  exact hφ

variable [GrpObj G] [IsCommMonObj G] {n : ℕ} {v : Fin n → (epsR K ⟶ G)}

theorem exists_derivations (hv : IsLieBasis v) {S : Type} [CommRing S] [Algebra K S] (j : sp (R₀ := K) S ⟶ G)
    [Mono j] (z : 𝟙_ _ ⟶ G) (u : S →ₐ[K] K) (hu : spMap u ≫ j = toUnit _ ≫ z)
    (χ : S →ₐ[K] TrivSqZeroExt K (Fin n → K))
    (hχ : spMap χ ≫ j = (toUnit _ ≫ z) * lieExp v (fun i => inr (Pi.single i 1))
      (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) :
    ∃ D : Fin n → S →ₗ[K] K, (∀ k a b, D k (a * b) = u a * D k b + u b * D k a) ∧
      (∀ c : Fin n → K, (∀ a, ∑ k, D k a * c k = 0) → c = 0) ∧
      (∀ δ : S →ₗ[K] K, (∀ a b, δ (a * b) = u a * δ b + u b * δ a) →
        ∃ c : Fin n → K, ∀ a, δ a = ∑ k, D k a * c k) ∧
      ∀ k, ∃ φ : S →ₐ[K] DualNumber K, spMap φ ≫ j = (toUnit _ ≫ z) * v k ∧ ∀ a, (φ a).snd = D k a := by
  have inj : ∀ {T : Type} [CommRing T] [Algebra K T] (φ ψ : S →ₐ[K] T), spMap φ ≫ j = spMap ψ ≫ j → φ = ψ := by
    intro T _ _ φ ψ h
    have h1 := Spec.map_injective (congrArg (·.left) ((cancel_mono j).1 h))
    exact AlgHom.ext fun a => congrArg (fun q => q.hom a) h1
  have hz : ∀ {T T' : Type} [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T'] (φ : T →ₐ[K] T'),
      spMap φ ≫ toUnit _ ≫ z = toUnit _ ≫ z := fun φ => by
    rw [← Category.assoc, comp_toUnit]
  have hfst : ∀ a, (χ a).fst = u a := by
    refine AlgHom.congr_fun (inj ((TrivSqZeroExt.fstHom K K _).comp χ) u ?_)
    rw [← spMap_comp, Category.assoc, hχ, MonObj.comp_mul, hz, comp_lieExp,
      lieExp_eq_one hv.1 _ (fun i => by rfl), mul_one, hu]
  let φ : (Fin n → K) → (S →ₐ[K] DualNumber K) := fun c => (vecTo (inlS K K) (fun i => inr (c i))
      (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)).comp χ
  have hφ : ∀ c, spMap (φ c) ≫ j = (toUnit _ ≫ z) * tanExp v c := fun c => by
    rw [← spMap_comp, Category.assoc, hχ, MonObj.comp_mul, hz, comp_lieExp]
    exact congrArg _ (lieExp_congr _ (fun i => vecTo_single _ _ _ i) _ _)
  have hφ1 : ∀ c a, (φ c a).fst = u a := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.fst_sum, hfst]
  have hφ2 : ∀ c a, (φ c a).snd = ∑ k, (χ a).snd k * c k := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.snd_sum, mul_comm]
  obtain ⟨hinj, hsurj⟩ := isLieBasisOver_self hv
  refine ⟨fun k => LinearMap.proj k ∘ₗ TrivSqZeroExt.sndHom K _ ∘ₗ χ.toLinearMap, fun k a b => ?_,
    fun c hc => hinj _ _ ?_, fun δ hδ => ?_, fun k => ⟨φ (Pi.single k 1), ?_, fun a => ?_⟩⟩
  · simp [hfst]
  · have : φ c = φ 0 := AlgHom.ext fun a => TrivSqZeroExt.ext (by rw [hφ1, hφ1]) (by
      rw [hφ2, hφ2]
      simpa using hc a)
    exact mul_left_cancel ((hφ c).symm.trans (this ▸ hφ 0))
  · let ψ : S →ₐ[K] DualNumber K := addDer ((inlS K K).comp u) (TrivSqZeroExt.inrHom K K ∘ₗ δ)
      (fun a b => by ext <;> simp [hδ, mul_comm]) (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)
    have h1 : (fstS K K).comp ψ = u := AlgHom.ext fun a => add_zero (u a)
    obtain ⟨c, hc⟩ := hsurj ((toUnit _ ≫ z)⁻¹ * (spMap ψ ≫ j)) (by
      rw [IsTanOver, MonObj.comp_mul, GrpObj.comp_inv, hz, ← Category.assoc, spMap_comp, h1, hu,
        inv_mul_cancel])
    have h2 : ψ = φ c := inj _ _ (by rw [hφ, ← hc, mul_inv_cancel_left])
    refine ⟨c, fun a => ?_⟩
    have := hφ2 c a
    rw [← h2] at this
    exact (zero_add (δ a)).symm.trans this
  · rw [hφ, tanExp_single hv.1]
  · rw [hφ2]
    simp [Pi.single_apply]

theorem valT_specMap_fromSpecStalk {X : Scheme.{0}} {y : X} {U : X.Opens} (hy : y ∈ U) {T : Type} [CommRing T]
    (φ : X.presheaf.stalk y ⟶ .of T) (f : Γ(X, U)) :
    KeyKa.valT (T := T) (Spec.map φ ≫ X.fromSpecStalk y) U f = φ.hom ((X.presheaf.germ U y hy).hom f) := by
  have ht : ⊤ ≤ X.fromSpecStalk y ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem (X.fromSpecStalk y)
    (by rwa [Scheme.fromSpecStalk_closedPoint])).ge
  have ht' : ⊤ ≤ (Spec.map φ ≫ X.fromSpecStalk y) ⁻¹ᵁ U := fun q _ => ht (x := Spec.map φ q) trivial
  refine (dif_pos ht').trans ?_
  have h1 : (X.fromSpecStalk y).appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (X.presheaf.stalk y)).hom =
      X.presheaf.germ U y hy := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hy]
    simp only [Category.assoc]
    have e : (Spec (X.presheaf.stalk y)).presheaf.map (homOfLE (le_top : X.fromSpecStalk y ⁻¹ᵁ U ≤ ⊤)).op ≫
        (Spec (X.presheaf.stalk y)).presheaf.map (homOfLE ht).op = 𝟙 _ := by
      rw [← Functor.map_comp]; exact CategoryTheory.Functor.map_id _ _
    rw [reassoc_of% e, Iso.inv_hom_id, Category.comp_id]
  have h2 : (Spec.map φ ≫ X.fromSpecStalk y).appLE U ⊤ ht' ≫ (Scheme.ΓSpecIso (.of T)).hom =
      X.presheaf.germ U y hy ≫ φ := by
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) _ U ⊤ ⊤ ht le_top, ← h1, Category.assoc, Category.assoc,
      ← Scheme.ΓSpecIso_naturality]
    congr 2
  exact congrArg (fun q => q.hom f) h2

theorem det_ne_zero_iff_span_germ_eq [LocallyOfFiniteType G.hom] (hv : IsLieBasis v) (z : 𝟙_ _ ⟶ G) (p : Sp K)
    {U : G.left.Opens} (hU : z.left p ∈ U) (f : Fin n → Γ(G.left, U))
    (hf : ∀ i, KeyKa.valT (T := K) z.left U (f i) = 0) :
    (Matrix.of fun i k => (KeyKa.valT (T := DualNumber K) ((toUnit (epsR K) ≫ z) * v k).left U (f i)).snd).det ≠ 0 ↔
      Ideal.span (Set.range fun i => (G.left.presheaf.germ U _ hU).hom (f i)) =
        maximalIdeal (G.left.presheaf.stalk (z.left p)) := by
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  letI : Algebra K (G.left.presheaf.stalk (z.left p)) :=
    (Spec.preimage (G.left.fromSpecStalk (z.left p) ≫ G.hom)).hom.toAlgebra
  let j : sp (R₀ := K) (G.left.presheaf.stalk (z.left p)) ⟶ G :=
    Over.homMk (G.left.fromSpecStalk (z.left p)) (Spec.map_preimage _).symm
  have : Mono j.left := inferInstanceAs (Mono (G.left.fromSpecStalk (z.left p)))
  have : Mono j := Over.mono_of_mono_left j
  have hpt : ∀ {T : Over (Sp K)} (t : T.left), (toUnit T ≫ z).left t = z.left p := fun {T} t =>
    congrArg z.left (Subsingleton.elim (α := PrimeSpectrum K) _ _)
  obtain ⟨u, hu⟩ := exists_factor j rfl (T := K) (toUnit _ ≫ z) (hpt _)
  have := isLocalRing_trivSqZeroExt (K := K) n
  obtain ⟨χ, hχ⟩ := exists_factor j rfl (T := TrivSqZeroExt K (Fin n → K))
    ((toUnit _ ≫ z) * lieExp v (fun i => inr (Pi.single i 1)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) (by
      have h1 : IsLocalHom (TrivSqZeroExt.fstHom K K (Fin n → K)).toRingHom :=
        ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
      have h2 : spMap (TrivSqZeroExt.fstHom K K (Fin n → K)) ≫ ((toUnit _ ≫ z) * lieExp v
          (fun i => inr (Pi.single i 1)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) = toUnit _ ≫ z := by
        rw [MonObj.comp_mul, comp_lieExp, lieExp_eq_one hv.1 _ (fun i => by rfl), mul_one, ← Category.assoc,
          comp_toUnit]
      rw [← comap_closedPoint (TrivSqZeroExt.fstHom K K (Fin n → K)).toRingHom, ← hpt (T := sp (R₀ := K) K) (closedPoint K), ← h2]
      rfl)
  obtain ⟨D, h1, h2, h3, h4⟩ := exists_derivations hv j z u hu χ hχ
  have hz : z.left = Spec.map (CommRingCat.ofHom u.toRingHom) ≫ G.left.fromSpecStalk (z.left p) := by
    have h := congrArg (·.left) hu
    have e : (toUnit (sp (R₀ := K) K)).left = 𝟙 (Sp K) := by
      rw [Over.toUnit_left]
      exact Spec.map_id _
    refine Eq.trans ?_ h.symm
    rw [Over.comp_left, e]
    exact (Category.id_comp _).symm
  rw [← det_ne_zero_iff_span_eq u D h1 h2 h3 _ fun i =>
    (valT_specMap_fromSpecStalk hU _ (f i)).symm.trans ((congrArg (KeyKa.valT (T := K) · U (f i)) hz.symm).trans (hf i))]
  refine iff_of_eq (congrArg (fun M : Matrix (Fin n) (Fin n) K => M.det ≠ 0) (Matrix.ext fun i k => ?_))
  obtain ⟨φ, hφ, hD⟩ := h4 k
  rw [Matrix.of_apply, Matrix.of_apply, ← hD]
  refine congrArg TrivSqZeroExt.snd ?_
  exact (congrArg (fun w : epsR K ⟶ G => KeyKa.valT (T := DualNumber K) w.left U (f i)) hφ.symm).trans
    (valT_specMap_fromSpecStalk hU (CommRingCat.ofHom φ.toRingHom) (f i))

end Group

end GlobalTheory.JacGen

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem GlobalTheory.KeyKa.jac_ne_zero_iff_span_eq_maximalIdeal : ∀ (K : Type) [Field K] (x : KeyIn K) (n : ℕ) (s : Fin x.P.g → RR x n) (z : Pt x) (c : x.P.L.ι) (p : Sp K), ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c → (∀ i, valT (T := K) z.left (x.P.L.U c) ((s i).f c) = 0) → (jac x s z c ≠ 0 ↔ Ideal.span (Set.range fun i => gs (𝟙 _) (z.left p) (x.P.L.U c) ((s i).f c)) = IsLocalRing.maximalIdeal (x.P.A.left.presheaf.stalk (z.left p))) := by
  intro K _ x n s z c p hc hs
  have := x.P.smoothDim
  have : Smooth x.P.A.hom := SmoothOfRelativeDimension.smooth x.P.g _
  have hU : z.left p ∈ x.P.L.U c := hc (x := p) trivial
  refine (GlobalTheory.JacGen.det_ne_zero_iff_span_germ_eq x.basis z p hU (fun i => (s i).f c) hs).trans ?_
  refine iff_of_eq (congrArg (fun F => Ideal.span (Set.range F) = _) (funext fun i => ?_))
  exact (gs_eq (𝟙 _) _ _ hU _).symm

end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsSquareDetComparisonScaleSec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD scaleD prodPts isTan_iff isLieComb_iff comp_one' isTan_mul isTan_one
  isTan_scale)
open GlobalTheory.UnifDifferential GlobalTheory.SqZero

noncomputable section

namespace GlobalTheory.KaScale

section Lin

variable {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))}

theorem valT_comp {T : Type} [CommRing T] {X Y : Scheme.{0}} (w : Sp T ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (f : Γ(Y, U)) : valT (w ≫ φ) U f = valT w (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  unfold valT
  by_cases h : ⊤ ≤ w ⁻¹ᵁ (φ ⁻¹ᵁ U)
  · rw [dif_pos h, dif_pos (show ⊤ ≤ (w ≫ φ) ⁻¹ᵁ U from h)]
    rfl
  · rw [dif_neg h, dif_neg (show ¬ ⊤ ≤ (w ≫ φ) ⁻¹ᵁ U from h)]

def der (v : sp (R₀ := K) (DualNumber K) ⟶ A) (U : A.left.Opens) (f : Γ(A.left, U)) : K :=
  TrivSqZeroExt.snd (valT (T := DualNumber K) v.left U f)

theorem der_pos (v : sp (R₀ := K) (DualNumber K) ⟶ A) (U : A.left.Opens) (f : Γ(A.left, U))
    (h : ⊤ ≤ v.left ⁻¹ᵁ U) : der v U f = (pullFn v U h f).snd := congrArg _ (dif_pos h)

theorem der_neg (v : sp (R₀ := K) (DualNumber K) ⟶ A) (U : A.left.Opens) (f : Γ(A.left, U))
    (h : ¬ ⊤ ≤ v.left ⁻¹ᵁ U) : der v U f = 0 := congrArg _ (dif_neg h)

theorem der_scale (v : sp (R₀ := K) (DualNumber K) ⟶ A) (c : K) (U : A.left.Opens) (f : Γ(A.left, U)) :
    der (Chart.spMap (scaleD c) ≫ v) U f = c * der v U f := by
  have : Subsingleton (PrimeSpectrum (DualNumber K)) := subsingleton_primeSpectrum K K
  by_cases h : ⊤ ≤ v.left ⁻¹ᵁ U
  · have h' := le_preimage_comp (scaleD c) v _ rfl U h
    rw [der_pos _ _ _ h, der_pos _ _ _ h', pullFn_comp (scaleD c) v _ rfl U h h' f, scaleD_eq]
    simp [epsTo, dualTo_apply, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]
  · rw [der_neg _ _ _ h, der_neg _ _ _ (fun h' => h (le_preimage_of_comp (scaleD c) v _ rfl U h')), mul_zero]

variable [GrpObj A]

theorem le_of_isTan {v v' : sp (R₀ := K) (DualNumber K) ⟶ A} (hv : Chart.IsTan v) (hv' : Chart.IsTan v')
    (U : A.left.Opens) (h : ⊤ ≤ v.left ⁻¹ᵁ U) : ⊤ ≤ v'.left ⁻¹ᵁ U := by
  have : Subsingleton (PrimeSpectrum (DualNumber K)) := subsingleton_primeSpectrum K K
  exact le_preimage_of_comp (fstD K) v' 1 hv'.symm U (le_preimage_comp (fstD K) v 1 hv.symm U h)

theorem der_mul {v v' : sp (R₀ := K) (DualNumber K) ⟶ A} (hv : Chart.IsTan v) (hv' : Chart.IsTan v')
    (U : A.left.Opens) (f : Γ(A.left, U)) : der (v * v') U f = der v U f + der v' U f := by
  by_cases h : ⊤ ≤ (v * v').left ⁻¹ᵁ U
  · obtain ⟨h₁, h₂, e⟩ := snd_pullFn_mul hv hv' U h
    rw [der_pos _ _ _ h, der_pos _ _ _ h₁, der_pos _ _ _ h₂, e]
  · rw [der_neg _ _ _ h, der_neg _ _ _ (fun h' => h (le_of_isTan hv (isTan_mul hv hv') U h')),
      der_neg _ _ _ (fun h' => h (le_of_isTan hv' (isTan_mul hv hv') U h')), add_zero]

theorem der_one (U : A.left.Opens) (f : Γ(A.left, U)) :
    der (1 : sp (R₀ := K) (DualNumber K) ⟶ A) U f = 0 := by
  rw [← comp_one' (Chart.spMap (scaleD (0 : K))), der_scale, zero_mul]

theorem der_prod (U : A.left.Opens) (f : Γ(A.left, U)) :
    ∀ {n : ℕ} (v : Fin n → (sp (R₀ := K) (DualNumber K) ⟶ A)), (∀ i, Chart.IsTan (v i)) →
      Chart.IsTan (List.ofFn v).prod ∧ der (List.ofFn v).prod U f = ∑ i, der (v i) U f := by
  intro n
  induction n with
  | zero =>
    intro v _
    rw [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨isTan_one, der_one U f⟩
  | succ n ih =>
    intro v hv
    obtain ⟨h₁, h₂⟩ := ih (fun i => v i.succ) (fun i => hv i.succ)
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ, der_mul (hv 0) h₁, h₂]
    exact ⟨isTan_mul (hv 0) h₁, rfl⟩

theorem der_comb {n : ℕ} {c : Fin n → K} {v : Fin n → (epsR K ⟶ A)} {w : epsR K ⟶ A}
    (hv : ∀ i, IsTangent (v i)) (hw : IsLieComb c v w) (U : A.left.Opens) (f : Γ(A.left, U)) :
    der w U f = ∑ i, c i * der (v i) U f := by
  rw [(isLieComb_iff c v w).1 hw]
  refine (der_prod U f _ (fun i => isTan_scale (c i) ((isTan_iff _).2 (hv i)))).2.trans ?_
  exact Finset.sum_congr rfl fun i _ => der_scale _ _ _ _

theorem translate_left (z : 𝟙_ (Over (Sp K)) ⟶ A) (v : epsR K ⟶ A) :
    ((toUnit (epsR K) ≫ z) * v).left = v.left ≫ ((toUnit A ≫ z) * 𝟙 A).left := by
  rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem snd_valT_comb {n : ℕ} {c : Fin n → K} {v : Fin n → (epsR K ⟶ A)} {w : epsR K ⟶ A}
    (hv : ∀ i, IsTangent (v i)) (hw : IsLieComb c v w) (z : 𝟙_ (Over (Sp K)) ⟶ A)
    (U : A.left.Opens) (f : Γ(A.left, U)) :
    TrivSqZeroExt.snd (valT (T := DualNumber K) ((toUnit (epsR K) ≫ z) * w).left U f) =
      ∑ i, c i * TrivSqZeroExt.snd (valT (T := DualNumber K) ((toUnit (epsR K) ≫ z) * v i).left U f) := by
  simp only [translate_left]
  exact (congrArg _ (valT_comp _ _ _ _)).trans ((der_comb hv hw _ _).trans
    (Finset.sum_congr rfl fun i _ => congrArg (fun t => c i * TrivSqZeroExt.snd t) (valT_comp _ _ _ _).symm))

end Lin

def cS {K : Type} [CommRing K] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (y : Y) : K →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ (p ⁻¹ᵁ ⊤) y trivial).hom.comp
    ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

theorem gs_constFn' {K : Type} [CommRing K] {X Y : Scheme.{0}} (p : X ⟶ Sp K) (W : X.Opens) (r : Y ⟶ X)
    (y : Y) (hy : r y ∈ W) (a : K) : gs r y W (constFn p W a) = cS (r ≫ p) y a :=
  ((gs_res r y (fun _ _ => trivial : W ≤ p ⁻¹ᵁ ⊤) hy _).trans (gs_pull r p y ⊤ trivial _)).trans
    (gs_eq (r ≫ p) y ⊤ trivial _)

theorem gs_cst' {K : Type} [CommRing K] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (y : Y) (a : K) :
    gs (𝟙 Y) y ⊤ (AbLaw.cst p ⊤ a) = cS p y a :=
  (gs_constFn' p ⊤ (𝟙 Y) y trivial a).trans (by rw [Category.id_comp])

variable {K : Type} [Field K] {P : Out.PolAV (Sp K)} {hg rig hr th hth v hv th' hth' v' hv'}

theorem isSquareDetComparison_scale_sec (a : Kˣ) (hth₀ : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ (a : K) * LB.Sec.f th i)
    (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b) (lam : Kˣ)
    (h : IsSquareDeterminantComparison ⟨P, hg, rig, hr, th, hth, v, hv⟩ m al b lam) :
    IsSquareDeterminantComparison ⟨P, hg, rig, hr, th', hth', v', hv'⟩ m al b (lam * a ^ (8 * m ^ (4 * P.g + 2))) := by
  obtain ⟨ξ, mu, w, Q, rho, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  refine ⟨ξ, mu, w, (a : K) ^ 4 • Q, rho, h₁, h₂, h₃, h₄, h₅, fun I y J hJ => ?_, ?_⟩
  · have e := h₆ I y J hJ
    simp only [gs_cst'] at e ⊢
    have e₂ : ∀ r : Fin 4, gs (alMap ⟨P, hg, rig, hr, th', hth', v', hv'⟩ al r (ξ I r)).left y _
        (LB.Sec.f th' (J (alMap ⟨P, hg, rig, hr, th', hth', v', hv'⟩ al r (ξ I r)).left)) =
        cS (Out.powObj P.A 4).hom y a * gs (alMap ⟨P, hg, rig, hr, th, hth, v, hv⟩ al r (ξ I r)).left y _
        (LB.Sec.f th (J (alMap ⟨P, hg, rig, hr, th, hth, v, hv⟩ al r (ξ I r)).left)) := fun r => by
      rw [hth₀, gs_mul _ _ _ (hJ _), gs_constFn' _ _ _ _ (hJ _), Over.w]
      rfl
    refine (Finset.prod_congr rfl fun r _ => e₂ r).trans ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (congrArg _ e).trans ?_
    rw [mul_left_comm, Finset.mul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun I' _ => ?_)
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, _root_.mul_assoc]
  · rw [Units.val_mul, h₇, Matrix.det_smul, Units.val_pow_eq_pow_val]
    simp only [Fintype.card_fun, Fintype.card_fin]
    ring

theorem jac_scale (M : Matrix (Fin P.g) (Fin P.g) K) (hM : ∀ i, IsLieComb (M i) v (v' i)) {n : ℕ}
    (s : Fin P.g → LB.Sec (pw P.L (n : ℤ))) (z) (c) :
    GlobalTheory.KeyKa.jac ⟨P, hg, rig, hr, th', hth', v', hv'⟩ s z c = GlobalTheory.KeyKa.jac ⟨P, hg, rig, hr, th, hth, v, hv⟩ s z c * M.det := by
  unfold GlobalTheory.KeyKa.jac
  rw [← Matrix.det_transpose M, ← Matrix.det_mul]
  congr 1
  ext i k
  rw [Matrix.mul_apply, Matrix.of_apply]
  refine (snd_valT_comb hv.1 (hM k) z _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
  exact mul_comm _ _

theorem kaVal_scale : ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K) (M : Matrix (Fin P.g) (Fin P.g) K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (s : Fin P.g → LB.Sec (pw P.L (n : ℤ))) (κ : Kˣ), admitted P.g n l l' al → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → KaVal ⟨P, hg, rig, hr, th, hth, v, hv⟩ n l l' al s κ → ∃ κ' : Kˣ, KaVal ⟨P, hg, rig, hr, th', hth', v', hv'⟩ n l l' al s κ' ∧ a ^ (8 * kaExp P.g n l l') * (κ' : K) = M.det ^ (4 * kaExp P.g n l l') * κ := by
  intro K _ P hg rig hr th hth v hv th' hth' v' hv' a M n l l' al s κ hadm hth₀ hM hκ
  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨y, -, hy⟩ := hth' (IsLocalRing.closedPoint K)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    rw [hth₀, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  have : IsCommMonObj P.A := P.isAb.comm
  have hdet : IsUnit M.det := ((LieComb.lieComb_algebra K P.A P.g v hv.1).2.2.2.2 M v' hv hM).1 hv'
  lift a to Kˣ using ha.isUnit
  obtain ⟨D, hD⟩ := hdet
  obtain ⟨z, ch, b, b', t, t', J, lam, lam', ⟨e₁, e₂, e₃, e₄, e₅⟩, hJ, hb, hb', ht, ht', rfl⟩ := hκ
  refine ⟨_, ⟨z, ch, b, b', t, t', J * D ^ (P.g.factorial * n ^ P.g),
    fun j => lam j * a ^ (8 * (l - j * n) ^ (4 * P.g + 2)),
    fun j => lam' j * a ^ (8 * (l' - j * n) ^ (4 * P.g + 2)), ⟨e₁, e₂, fun k => ?_, e₄, e₅⟩, ?_,
    fun j hj => ⟨(hb j hj).1, isSquareDetComparison_scale_sec a hth₀ _ _ _ _ (hb j hj).2⟩,
    fun j hj => ⟨(hb' j hj).1, isSquareDetComparison_scale_sec a hth₀ _ _ _ _ (hb' j hj).2⟩, ht, ht', rfl⟩, ?_⟩
  · rw [jac_scale (th := th) (hth := hth) (hv := hv) M hM, ← hD]
    exact (e₃ k).mul D.isUnit
  · rw [Units.val_mul, hJ, Units.val_pow_eq_pow_val, hD]
    simp only [jac_scale (th := th) (hth := hth) (hv := hv) (th' := th') (hth' := hth') (hv' := hv') M hM]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · have key := kaForm_homogeneous K P.g n l l' t t' J 1 a 1 lam lam' (fun _ => 1) (fun _ => 1)
      hadm.2.1 hadm.2.2.1
    simp only [one_zpow, one_pow, _root_.mul_one, Finset.prod_const_one] at key
    rw [← hD]
    norm_cast
    rw [← key]
    unfold kaForm kaExp
    generalize tComb P.g n l _ t _ = X
    generalize tComb P.g n l' _ t' _ = X'
    generalize degProd P.g n l l' ^ (3 * P.g + 2) = N
    generalize P.g.factorial * n ^ P.g = F
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ← natCast_zsmul]
    push_cast [Nat.cast_sub hadm.2.2.1.le]
    module

end GlobalTheory.KaScale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.EqOfSimilitudeIsoQuotientKernelInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.EqOfInvariantGenTranslates
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory

theorem eq_of_invariantGen_translates :
    Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (m : ℕ) (ξ ξ' : 𝟙_ (Over (Sp K)) ⟶ P.A) (u : LB.Gen (LB.LinComb P.L (K := Fin 2) ![((𝟙 P.A) ^ m * (toUnit P.A ≫ ξ)).left, ((𝟙 P.A) ^ m * (toUnit P.A ≫ ξ')).left] ![1, -1])), (m : K) ≠ 0 → u.IsGen → (∀ δ : 𝟙_ (Over (Sp K)) ⟶ P.A, δ ^ m = 1 → ∀ (y : P.A.left) J, Good P.L y J → val u ((toUnit P.A ≫ δ) * 𝟙 P.A).left y J = val u (𝟙 _) y J) → ξ = ξ' := by
  intro laws K _ _ P m ξ ξ' u hm hu hinv
  haveI : IsCommMonObj P.A := P.isAb.comm
  have hmul : ∀ {Z : Over (Sp K)} (y : Z ⟶ P.A), y ≫ Out.mulA P.A m = y ^ m :=
    fun y => by rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
  obtain ⟨v, hv⟩ := exists_isGen_of_invariant P.isLB (K := Fin 2)
    ![(𝟙 P.A * (toUnit P.A ≫ ξ)).left, (𝟙 P.A * (toUnit P.A ≫ ξ')).left] ![1, -1]
    (Out.mulA P.A m).left
    (I := {y : 𝟙_ (Over (Sp K)) ⟶ P.A // y ^ m = 1})
    (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left)
    (fun y => by
      rw [← Over.comp_left, hmul, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one, _root_.one_mul,
        Out.mulA])
    (fun U f hf => torsion_invariant_descends (fun S _ Q n hn =>
      let ⟨a, b, c, d, _⟩ := laws.mulN S Q n hn; ⟨a, b, c, d⟩) K P m hm U f fun y hy => hf ⟨y, hy⟩) _
    (fun i => by
      fin_cases i
      · change ((𝟙 P.A) ^ m * (toUnit P.A ≫ ξ)).left =
          (Out.mulA P.A m ≫ (𝟙 P.A * (toUnit P.A ≫ ξ))).left
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, Out.mulA]
      · change ((𝟙 P.A) ^ m * (toUnit P.A ≫ ξ')).left =
          (Out.mulA P.A m ≫ (𝟙 P.A * (toUnit P.A ≫ ξ'))).left
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, Out.mulA])
    u hu (fun y z J hJ => hinv y.1 y.2 z J hJ)
  let B : Over (Sp K) := Over.mk (𝟙 (Sp K))
  let x : B ⟶ P.A := toUnit B ≫ (ξ * ξ'⁻¹)
  let r : B ⊗ P.A ⟶ P.A := snd B P.A * (toUnit _ ≫ ξ'⁻¹)
  have hx : x = toUnit _ ≫ η[P.A] := by
    refine P.ktriv K (𝟙 _) x fun p => ⟨⊤, trivial, ?_⟩
    have h3 : (fun i => r.left ≫
        ![(𝟙 P.A * (toUnit P.A ≫ ξ)).left, (𝟙 P.A * (toUnit P.A ≫ ξ')).left] i) =
        ![(lift (fst B P.A ≫ x) (snd B P.A) ≫ μ[P.A]).left, (snd B P.A).left] := by
      funext i
      fin_cases i
      · change (r ≫ (𝟙 P.A * (toUnit P.A ≫ ξ))).left = ((fst B P.A ≫ x) * snd B P.A).left
        congr 1
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
        simp only [r, x, comp_toUnit_assoc, MonObj.comp_mul]
        rw [_root_.mul_assoc, _root_.mul_comm (snd B P.A), _root_.mul_comm (toUnit _ ≫ ξ'⁻¹)]
      · change (r ≫ (𝟙 P.A * (toUnit P.A ≫ ξ'))).left = (snd B P.A).left
        congr 1
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
        simp only [r]
        rw [GrpObj.comp_inv, inv_mul_cancel_right]
    have h4 : ∃ w : LB.Gen (LB.LinComb P.L (fun i => r.left ≫
        ![(𝟙 P.A * (toUnit P.A ≫ ξ)).left, (𝟙 P.A * (toUnit P.A ≫ ξ')).left] i) ![1, -1]),
        w.IsGen := ⟨_, DVR.pullGen_isGen _ _ _ v hv _⟩
    rw [h3] at h4
    obtain ⟨w, hw⟩ := h4
    exact exists_isGen_pull (Out.translDiff P.A P.L x) w hw _
  let s : 𝟙_ (Over (Sp K)) ⟶ B := Over.homMk (𝟙_ (Over (Sp K))).hom (Category.comp_id _)
  have h5 := congrArg (fun q => s ≫ q) hx
  simp only [x, comp_toUnit_assoc] at h5
  rw [← Hom.one_def, toUnit_unit, Category.id_comp] at h5
  exact mul_inv_eq_one.1 h5

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.EqOfSimilitudeIsoQuotientKernelInvariant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.KeyKa

section
variable {R : Type} [CommRing R] (x : KeyIn R) (al : Matrix (Fin 4) (Fin 4) ℤ) (r₀ : Fin 4)

def rowEmb : x.P.A ⟶ Out.powObj x.P.A 4 :=
  (Out.powIsLimit x.P.A 4).lift (Fan.mk x.P.A fun c => (𝟙 x.P.A) ^ al r₀ c)

theorem rowEmb_pr (c : Fin 4) : rowEmb x al r₀ ≫ Out.powPr x.P.A c = (𝟙 x.P.A) ^ al r₀ c :=
  (Out.powIsLimit x.P.A 4).fac (Fan.mk x.P.A fun c => (𝟙 x.P.A) ^ al r₀ c) ⟨c⟩

theorem rowEmb_alMap {m : ℕ} (hal : al * al.transpose = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (r : Fin 4)
    (ζ : Pt x) : rowEmb x al r₀ ≫ alMap x al r ζ =
      (if r = r₀ then (𝟙 x.P.A) ^ m else 1) * (toUnit x.P.A ≫ ζ) := by
  have := x.P.isAb.comm
  have h : al r₀ 0 * al r 0 + (al r₀ 1 * al r 1 + (al r₀ 2 * al r 2 + al r₀ 3 * al r 3)) =
      if r = r₀ then (m : ℤ) else 0 := by
    have := congrFun (congrFun hal r₀) r
    simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, mul_ite, _root_.mul_one, mul_zero, eq_comm (a := r₀)] at this
    rw [← this]; ring
  rw [alMap, MonObj.comp_mul, ← Category.assoc, comp_toUnit]
  congr 1
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul, GrpObj.comp_zpow,
    rowEmb_pr, _root_.mul_one, ← zpow_mul, ← zpow_add]
  refine (congrArg (fun n : ℤ => (𝟙 x.P.A) ^ n) h).trans ?_
  split_ifs
  · exact zpow_natCast _ _
  · exact zpow_zero _

theorem transl_rowEmb (δ : Pt x) : ((toUnit x.P.A ≫ δ) * 𝟙 x.P.A) ≫ rowEmb x al r₀ =
    rowEmb x al r₀ ≫ ((toUnit (Out.powObj x.P.A 4) ≫ δ ≫ rowEmb x al r₀) * 𝟙 (Out.powObj x.P.A 4)) := by
  have := x.P.isAb.comm
  refine (Out.powIsLimit x.P.A 4).hom_ext fun ⟨c⟩ => ?_
  change (_ ≫ _) ≫ Out.powPr x.P.A c = (_ ≫ _) ≫ Out.powPr x.P.A c
  rw [Category.assoc, Category.assoc, rowEmb_pr, MonObj.mul_comp _ _ (Out.powPr x.P.A c), MonObj.comp_mul, Category.id_comp, Category.assoc,
    Category.assoc, rowEmb_pr, ← Category.assoc (rowEmb x al r₀), comp_toUnit]
  simp only [GrpObj.comp_zpow, Category.comp_id, mul_zpow]

end

theorem eq_of_similitude_invariant : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ ξ' : Fin 4 → Pt x) (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (w' : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ' r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → w.IsGen → w'.IsGen → (∀ v : 𝟙_ (Over (Sp K)) ⟶ Out.powObj x.P.A 4, (∀ r, v ≫ alMap x al r 1 = 1) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → val w (r ≫ ((toUnit (Out.powObj x.P.A 4) ≫ v) * 𝟙 (Out.powObj x.P.A 4)).left) z J * val w' r z J = val w' (r ≫ ((toUnit (Out.powObj x.P.A 4) ≫ v) * 𝟙 (Out.powObj x.P.A 4)).left) z J * val w r z J) → ξ = ξ' := by
  intro laws K _ _ x m al ξ ξ' w w' hm hal hw hw' hinv
  have hL := x.P.isLB
  have hm0 : (m : ℤ) ≠ 0 := fun h => hm (by rw [Int.natCast_eq_zero.1 h, Nat.cast_zero])
  have hal' : al * al.transpose = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    have hd : al.det ≠ 0 := fun h => by
      have := congrArg Matrix.det hal
      rw [Matrix.det_mul, h, mul_zero, Matrix.det_smul, Matrix.det_one, _root_.mul_one] at this
      exact pow_ne_zero _ hm0 this.symm
    have h1 : (al * al.transpose - (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) * al = 0 := by
      rw [sub_mul, _root_.mul_assoc, hal, Matrix.mul_smul, Matrix.smul_mul, _root_.mul_one,
        _root_.one_mul, sub_self]
    have h2 := congrArg (· * al.adjugate) h1
    simp only [_root_.mul_assoc, Matrix.mul_adjugate, zero_mul, Matrix.mul_smul, _root_.mul_one] at h2
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left hd)
  funext r₀
  obtain ⟨g, hg⟩ := DVR.exists_gen_of_local (V := K) x.P.L hL (K := Fin 4 ⊕ Fin 4)
    (Sum.elim (fun r => (ξ r).left) (fun r => (ξ' r).left))
    (Sum.elim (fun r => if r = r₀ then 0 else -1) (fun r => if r = r₀ then 0 else 1))
  let i := rowEmb x al r₀
  have hu₀ := DVR.mulGen_isGen x.P.L _ _ _ _ _ _
    (DVR.mulGen_isGen x.P.L _ _ _ _ _ _ (DVR.pullGen_isGen x.P.L _ _ w hw i.left)
      (DVR.invGen_isGen x.P.L _ _ _ (DVR.pullGen_isGen x.P.L _ _ w' hw' i.left)))
    (DVR.pullGen_isGen x.P.L _ _ g hg (toUnit x.P.A).left)
  obtain ⟨u, hu, hval⟩ := exists_gen hL (K' := Fin 2)
    (φ' := ![((𝟙 x.P.A) ^ m * (toUnit x.P.A ≫ ξ r₀)).left, ((𝟙 x.P.A) ^ m * (toUnit x.P.A ≫ ξ' r₀)).left])
    (ε' := ![1, -1]) (by
      intro U _ h
      have e : ∀ (r : Fin 4) (ζ : Pt x), i.left ≫ (alMap x al r ζ).left =
          ((if r = r₀ then (𝟙 x.P.A) ^ m else 1) * (toUnit x.P.A ≫ ζ)).left := fun r ζ =>
        congrArg (fun q => q.left) (rowEmb_alMap x al r₀ hal' r ζ)
      have e' : ∀ ζ : Pt x, (toUnit x.P.A).left ≫ ζ.left = (toUnit x.P.A ≫ ζ).left := fun _ => rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, e, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, neg_neg]
      simp only [← Finset.prod_mul_distrib]
      rw [Finset.prod_eq_single r₀ (fun r _ hr => ?_) (fun hr => absurd (Finset.mem_univ _) hr)]
      · simp only [if_true, zpow_zero, _root_.mul_one, zpow_neg]
        rw [_root_.mul_mul_mul_comm, inv_mul_cancel, _root_.mul_one]
      · simp only [if_neg hr, _root_.one_mul, zpow_one, zpow_neg, e']
        rw [_root_.mul_mul_mul_comm, mul_inv_cancel_comm, inv_mul_cancel_comm, inv_mul_cancel]) _ hu₀
  refine GlobalTheory.eq_of_invariantGen_translates laws K x.P m (ξ r₀) (ξ' r₀) u hm hu fun δ hδ y J hJ => ?_
  have hv := hinv (δ ≫ i) (fun r => by
    rw [Category.assoc, rowEmb_alMap x al r₀ hal', MonObj.comp_one, _root_.mul_one]
    split_ifs
    · rw [MonObj.comp_pow, Category.comp_id, hδ]
    · exact MonObj.comp_one _) _ i.left y J hJ
  have e₁ : ((toUnit x.P.A ≫ δ) * 𝟙 x.P.A).left ≫ i.left =
      i.left ≫ ((toUnit (Out.powObj x.P.A 4) ≫ δ ≫ i) * 𝟙 (Out.powObj x.P.A 4)).left :=
    congrArg (fun q => q.left) (transl_rowEmb x al r₀ δ)
  have e₂ : ((toUnit x.P.A ≫ δ) * 𝟙 x.P.A).left ≫ (toUnit x.P.A).left = (toUnit x.P.A).left :=
    congrArg (fun q => q.left) (comp_toUnit ((toUnit x.P.A ≫ δ) * 𝟙 x.P.A))
  rw [hval _ _ y J hJ, hval _ _ y J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv,
    val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ, e₁, Category.id_comp,
    Category.id_comp]
  erw [e₂]
  congr 1
  rw [mul_inv_eq_iff_eq_mul, mul_right_comm, eq_mul_inv_iff_mul_eq, hv, mul_comm]

end GlobalTheory.KeyKa

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.EqOfSimilitudeIsoQuotientKernelInvariantStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_similitudeIso_quotient_kernel_invariant : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ ξ' : Fin 4 → Pt x) (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (w' : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ' r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → w.IsGen → w'.IsGen → (∀ v : 𝟙_ (Over (Sp K)) ⟶ Out.powObj x.P.A 4, (∀ r, v ≫ alMap x al r 1 = 1) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → val w (r ≫ ((toUnit (Out.powObj x.P.A 4) ≫ v) * 𝟙 (Out.powObj x.P.A 4)).left) z J * val w' r z J = val w' (r ≫ ((toUnit (Out.powObj x.P.A 4) ≫ v) * 𝟙 (Out.powObj x.P.A 4)).left) z J * val w r z J) → ξ = ξ' := by
  first | exact @GlobalTheory.KeyKa.eq_of_similitude_invariant | exact GlobalTheory.KeyKa.eq_of_similitude_invariant | (intros; apply GlobalTheory.KeyKa.eq_of_similitude_invariant <;> assumption)
end
end

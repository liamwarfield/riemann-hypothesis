module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationConstantOfLogKodairaSpencerMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldBasisToroidalModelSnc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivationExtendsCompletedToricChartRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DirEqZeroOfConst

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerInjectiveModMaximalBoundary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogVectorFieldMemMaxIdealSmulOfVanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogVectorFieldMemMaxIdealSmulOfVanishing
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogBack

section Algebra

open IsLocalRing GlobalTheory.LogDerProj GlobalTheory.LogBasis

theorem prime_X {σ k : Type} [CommRing k] [IsDomain k] (s : σ) : Prime (MvPowerSeries.X s : MvPowerSeries σ k) := by
  classical
  let ρ := MvPowerSeries.rescale (σ := σ) (R := k) (fun i => if i = s then 0 else 1)
  have key : ∀ g, MvPowerSeries.X s ∣ g ↔ ρ g = 0 := by
    intro g
    rw [MvPowerSeries.X_dvd_iff, MvPowerSeries.ext_iff]
    refine forall_congr' fun n => ?_
    rw [MvPowerSeries.coeff_rescale, map_zero]
    by_cases hn : n s = 0
    · have : (n.prod fun i m => (if i = s then (0 : k) else 1) ^ m) = 1 := by
        refine Finset.prod_eq_one fun i hi => ?_
        have : i ≠ s := fun h => (Finsupp.mem_support_iff.1 hi) (h ▸ hn)
        simp [this]
      simp [hn, this]
    · have : (n.prod fun i m => (if i = s then (0 : k) else 1) ^ m) = 0 :=
        Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hn) (by simp [hn])
      simp [hn, this]
  refine ⟨?_, ?_, fun a b h => ?_⟩
  · intro h
    have := congrArg (MvPowerSeries.coeff (Finsupp.single s 1)) h
    simp [MvPowerSeries.coeff_X] at this
  · intro h
    have := h.map (MvPowerSeries.constantCoeff (σ := σ) (R := k))
    simp at this
  · rw [key, map_mul, mul_eq_zero, ← key, ← key] at h
    exact h

theorem exists_log_of_dvd {R ι : Type} [CommRing R] [IsDomain R] [Algebra ℤ R] [Fintype ι] (I : Ideal R) (δ : Derivation ℤ R R)
    (h0 : ∀ r, δ r ∈ I) (T a : ι → R) (hT : ∀ i, Prime (T i)) (ha : ∀ i, a i ∈ I) (hδ : ∀ i, δ (T i) = a i * T i)
    (N : ℕ) : ∀ g, g ∣ (∏ i, T i) ^ N → ∃ α ∈ I, δ g = α * g := by
  classical
  have step : ∀ i q, (∀ g, g ∣ q → ∃ α ∈ I, δ g = α * g) → ∀ g, g ∣ T i * q → ∃ α ∈ I, δ g = α * g := by
    rintro i q hq g ⟨h, hh⟩
    rcases (hT i).dvd_or_dvd (⟨q, hh.symm⟩ : T i ∣ g * h) with ⟨g', rfl⟩ | ⟨h', rfl⟩
    · obtain ⟨α, hα, e⟩ := hq g' ⟨h, mul_left_cancel₀ (hT i).ne_zero (by rw [hh]; ring)⟩
      refine ⟨α + a i, I.add_mem hα (ha i), ?_⟩
      rw [δ.leibniz, e, hδ, smul_eq_mul, smul_eq_mul]
      ring
    · exact hq g ⟨h', mul_left_cancel₀ (hT i).ne_zero (by rw [hh]; ring)⟩
  have steps : ∀ (s : Finset ι) q, (∀ g, g ∣ q → ∃ α ∈ I, δ g = α * g) →
      ∀ g, g ∣ (∏ i ∈ s, T i) * q → ∃ α ∈ I, δ g = α * g := by
    intro s q hq
    induction s using Finset.induction_on with
    | empty => simpa using hq
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, mul_assoc]
      exact step j _ ih
  induction N with
  | zero =>
    intro g hg
    rw [pow_zero] at hg
    obtain ⟨v, hv⟩ := hg
    exact ⟨δ g * v, I.mul_mem_right _ (h0 g), by linear_combination (δ g) * hv⟩
  | succ N ih =>
    rw [pow_succ']
    exact steps _ _ ih

theorem exists_dual {K R : Type} [CommRing K] [CommRing R] [Algebra K R]
    {n : ℕ} (z : Fin n → R) (bΩ : Module.Basis (Fin n) R Ω[R⁄K])
    (hb : ∀ i, bΩ i = KaehlerDifferential.D K R (z i)) :
    ∃ d : Fin n → Derivation ℤ R R, (∀ k l, d k (z l) = if k = l then 1 else 0) ∧
      (∀ k a, d k (algebraMap K R a) = 0) ∧
      ∀ D : Derivation ℤ R R, (∀ a, D (algebraMap K R a) = 0) → D = ∑ k, D (z k) • d k := by
  classical
  let d : Fin n → Derivation ℤ R R := fun k =>
    (KaehlerDifferential.linearMapEquivDerivation K R (bΩ.coord k)).restrictScalars ℤ
  have hd' : ∀ k r, d k r = bΩ.repr (KaehlerDifferential.D K R r) k := fun k r => rfl
  refine ⟨d, fun k l => by rw [hd', ← hb]; simp [Finsupp.single_apply, eq_comm], fun k a => by rw [hd']; simp,
    fun D hD => ?_⟩
  let D' : Derivation K R R := Derivation.mk'
    { toFun := D
      map_add' := map_add D
      map_smul' := fun a r => by
        simp only [Algebra.smul_def, D.leibniz, hD, RingHom.id_apply]
        simp }
    (fun x y => D.leibniz x y)
  have hD' : ∀ r, D' r = D r := fun _ => rfl
  ext r
  have := map_sum (Derivation.coeFnAddMonoidHom (R := ℤ) (A := R) (M := R)) (fun k => D (z k) • d k) Finset.univ
  have h3 := congrFun this r
  rw [Finset.sum_apply] at h3
  refine Eq.trans ?_ h3.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hD', ← D'.liftKaehlerDifferential_comp_D r, ← bΩ.sum_repr (KaehlerDifferential.D K R r), map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, hb, D'.liftKaehlerDifferential_comp_D, hD']
  simp [Derivation.coeFnAddMonoidHom_apply, hd', mul_comm]

theorem exists_sum_of_coords {K B R : Type} [Field K] [CharZero K] [CommRing B] [Algebra K B] [IsNoetherianRing B]
    [CommRing R] (I : Ideal R) {n m : ℕ} (z : Fin n → B) (bΩ : Module.Basis (Fin n) B Ω[B⁄K])
    (hb : ∀ i, bΩ i = KaehlerDifferential.D K B (z i)) (e : Fin m → Fin n) (he : Function.Injective e)
    (ψ : B →+* R) (D : Derivation ℤ B B) (hD : D ∈ logSub (algebraMap K B) (Ideal.span {∏ i, z (e i)}))
    (h0 : ∀ r, ψ (D r) ∈ I) (h1 : ∀ i c, D (z (e i)) = c * z (e i) → ψ c ∈ I) :
    ∃ (g : Fin n → B) (v : Fin n → Derivation ℤ B B), (∀ k, ψ (g k) ∈ I) ∧
      (∀ k, v k ∈ logSub (algebraMap K B) (Ideal.span {∏ i, z (e i)})) ∧ D = ∑ k, g k • v k := by
  classical
  have hQ : ∀ n : ℕ, IsUnit ((n : B) + 1) := fun n => by
    have := (IsUnit.mk0 ((n : K) + 1) (Nat.cast_add_one_ne_zero n)).map (algebraMap K B)
    simpa using this
  obtain ⟨d, hd, hd0, hspan⟩ := exists_dual z bΩ hb
  obtain ⟨b, hb'⟩ := exists_basis_of_dual hQ (algebraMap K B) z d hd hd0 hspan e he
    (logSub (algebraMap K B) (Ideal.span {∏ i, z (e i)})) (fun _ => Iff.rfl)
  have hv : ∀ k u, (∀ i, k = e i → z (e i) ∣ u) → u • d k ∈ logSub (algebraMap K B) (Ideal.span {∏ i, z (e i)}) := by
    intro k u hu
    refine ⟨fun a => by simp [hd0], mem_span_of_dvd _ (prod_mem_span _ _ _ fun i _ => ?_)⟩
    rw [Derivation.smul_apply, hd]
    split_ifs with h
    · simpa using hu i h
    · simp
  have key : ∀ k, ∃ (g : B) (v : Derivation ℤ B B), ψ g ∈ I ∧
      v ∈ logSub (algebraMap K B) (Ideal.span {∏ i, z (e i)}) ∧ D (z k) • d k = g • v := by
    intro k
    by_cases hk : ∃ i, e i = k
    · obtain ⟨i, rfl⟩ := hk
      have hc : D (z (e i)) = b.repr ⟨D, hD⟩ (e i) * z (e i) := by
        have h2 := congrArg Subtype.val (b.sum_repr ⟨D, hD⟩)
        rw [Submodule.coe_sum] at h2
        have := map_sum (Derivation.coeFnAddMonoidHom (R := ℤ) (A := B) (M := B))
          (fun k => ((b.repr ⟨D, hD⟩ k • b k : logSub (algebraMap K B) (Ideal.span {∏ i, z (e i)})) :
            Derivation ℤ B B)) Finset.univ
        have h3 := congrFun this (z (e i))
        rw [Finset.sum_apply, h2] at h3
        refine h3.trans ?_
        simp [Derivation.coeFnAddMonoidHom_apply, hb']
      refine ⟨_, z (e i) • d (e i), h1 i _ hc, hv _ _ fun j hj => by rw [hj], ?_⟩
      rw [smul_smul, ← hc]
    · exact ⟨D (z k), (1 : B) • d k, h0 _, hv _ _ fun j hj => absurd ⟨j, hj.symm⟩ hk, by rw [one_smul]⟩
  choose g v hg hv' hgv using key
  exact ⟨g, v, hg, hv', (hspan D hD.1).trans (Finset.sum_congr rfl fun k _ => hgv k)⟩

theorem mem_smul_top_of_sum {K A B ι : Type} [Field K] [CommRing A] [CommRing B] [Algebra A B] [Fintype ι] (f : A)
    [IsLocalization.Away f B] (φ : K →+* A) (hφ : φ.FiniteType) (J m : Ideal A) (hm : m.IsMaximal) (hf : f ∉ m)
    (D : logSub φ J) (g : ι → B) (v : ι → Derivation ℤ B B)
    (hg : ∀ k, ∃ (s : Submonoid.powers f) (a : A), a ∈ m ∧ g k * algebraMap A B s = algebraMap A B a)
    (hv : ∀ k, v k ∈ logSub ((algebraMap A B).comp φ) (J.map (algebraMap A B)))
    (h : extL (S := B) f D.1 = ∑ k, g k • v k) : D ∈ m • (⊤ : Submodule A (logSub φ J)) := by
  classical
  have key : ∃ (s : Submonoid.powers f) (D' : logSub φ J), D' ∈ m • (⊤ : Submodule A (logSub φ J)) ∧
      (s : A) • extL (S := B) f D.1 = extL (S := B) f D'.1 := by
    rw [h]
    refine Finset.sum_induction _ (fun δ : Derivation ℤ B B => ∃ (s : Submonoid.powers f) (D' : logSub φ J),
      D' ∈ m • (⊤ : Submodule A (logSub φ J)) ∧ (s : A) • δ = extL (S := B) f D'.1) ?_ ⟨1, 0, zero_mem _, by simp⟩ ?_
    · rintro x y ⟨s, D₁, h₁, e₁⟩ ⟨t, D₂, h₂, e₂⟩
      refine ⟨s * t, (t : A) • D₁ + (s : A) • D₂,
        add_mem (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂), ?_⟩
      rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, map_add (f := _), map_smul, map_smul, ← e₁, ← e₂,
        smul_smul, smul_smul, smul_add, Submonoid.coe_mul, mul_comm (t : A)]
    · intro k _
      obtain ⟨s, a, ha, e⟩ := hg k
      obtain ⟨⟨D', t⟩, e'⟩ := exists_pow_smul_eq_res (S := B) f φ hφ J ⟨v k, hv k⟩
      have e'' : (t : A) • v k = extL (S := B) f D'.1 := congrArg Subtype.val e'
      refine ⟨s * t, a • D', Submodule.smul_mem_smul ha trivial, ?_⟩
      rw [Submodule.coe_smul, map_smul, ← e'', ← algebraMap_smul B a, ← e, ← algebraMap_smul B (t : A),
        ← algebraMap_smul B ((s * t : Submonoid.powers f) : A), smul_smul, smul_smul, Submonoid.coe_mul, map_mul]
      congr 1
      ring
  obtain ⟨s, D', hD', e⟩ := key
  obtain ⟨c, hc⟩ := exists_pow_smul_eq_of_res_eq (S := B) f φ hφ J ((s : A) • D) D' (Subtype.ext (by
    change extL (S := B) f ((s : A) • D.1) = extL (S := B) f D'.1
    rw [map_smul, e]))
  have h1 : ((c * s : Submonoid.powers f) : A) • D ∈ m • (⊤ : Submodule A (logSub φ J)) := by
    rw [Submonoid.coe_mul, mul_smul]
    have : (c : A) • (s : A) • D = (c : A) • D' := hc
    rw [this]
    exact Submodule.smul_mem _ _ hD'
  have h2 : ((c * s : Submonoid.powers f) : A) ∉ m := by
    obtain ⟨N, hN⟩ := (c * s).2
    rw [← hN]
    exact fun h => hf (hm.isPrime.mem_of_pow_mem N h)
  obtain ⟨y, i, hi, e1⟩ := hm.exists_inv h2
  rw [← one_smul A D, ← e1, add_smul, mul_smul]
  exact add_mem (Submodule.smul_mem _ _ h1) (Submodule.smul_mem_smul hi trivial)

theorem mem_smul_top_of_coords {K A B R : Type} [Field K] [CharZero K] [CommRing A] [CommRing B] [Algebra A B]
    [Algebra K B] [IsNoetherianRing B] [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra ℤ R] (f : A) [IsLocalization.Away f B]
    (φ : K →+* A) (hφ : φ.FiniteType) (hK : (algebraMap A B).comp φ = algebraMap K B) (J m : Ideal A)
    (hm : m.IsMaximal) (hf : f ∉ m) {n r : ℕ} (z : Fin n → B) (bΩ : Module.Basis (Fin n) B Ω[B⁄K])
    (hb : ∀ i, bΩ i = KaehlerDifferential.D K B (z i)) (e : Fin r → Fin n) (he : Function.Injective e)
    (hJ : J.map (algebraMap A B) = Ideal.span {∏ i, z (e i)}) (ψ : B →+* R)
    (hψ : ∀ g ∈ m, ψ (algebraMap A B g) ∈ maximalIdeal R) (D : logSub φ J) (δ : Derivation ℤ R R)
    (hδ : ∀ a, δ (ψ (algebraMap A B a)) = ψ (algebraMap A B (D.1 a))) (h0 : ∀ x, δ x ∈ maximalIdeal R)
    (h1 : ∀ i, ψ (z (e i)) ≠ 0 ∧ ∃ α ∈ maximalIdeal R, δ (ψ (z (e i))) = α * ψ (z (e i))) :
    D ∈ m • (⊤ : Submodule A (logSub φ J)) := by
  have hcomm : ∀ y, ψ (extL (S := B) f D.1 y) = δ (ψ y) := by
    intro y
    obtain ⟨⟨a, t⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) y
    have hu : IsUnit (ψ (algebraMap A B t)) := (IsLocalization.map_units B t).map ψ
    have e' : y * algebraMap A B t = algebraMap A B a := e
    have h1 := congrArg (fun y => ψ (extL (S := B) f D.1 y)) e'
    have h2 := congrArg (fun y => δ (ψ y)) e'
    simp only [Derivation.leibniz, smul_eq_mul, map_mul, map_add (f := _), extL_algebraMap, hδ] at h1 h2
    exact hu.mul_left_cancel (by linear_combination h1 - h2)
  have hD : extL (S := B) f D.1 ∈ logSub (algebraMap K B) (Ideal.span {∏ i, z (e i)}) := by
    rw [← hK, ← hJ]
    exact (res (S := B) f φ J D).2
  obtain ⟨g, v, hg, hv, hs⟩ := exists_sum_of_coords (maximalIdeal R) z bΩ hb e he ψ _ hD
    (fun y => hcomm y ▸ h0 _) (fun i c hc => by
      obtain ⟨hne, α, hα, e1⟩ := h1 i
      rw [← hcomm, hc, map_mul] at e1
      exact mul_right_cancel₀ hne e1 ▸ hα)
  refine mem_smul_top_of_sum f φ hφ J m hm hf D g v (fun k => ?_) (fun k => by rw [hK, hJ]; exact hv k) hs
  obtain ⟨⟨a, t⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) (g k)
  have e' : g k * algebraMap A B t = algebraMap A B a := e
  refine ⟨t, a, ?_, e'⟩
  have hle : m = (maximalIdeal R).comap (ψ.comp (algebraMap A B)) :=
    hm.eq_of_le (Ideal.comap_ne_top _ (maximalIdeal.isMaximal R).ne_top) hψ
  rw [hle, Ideal.mem_comap, RingHom.comp_apply, ← e', map_mul]
  exact Ideal.mul_mem_right _ _ (hg k)

end Algebra

section Geometry

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.LogBasis GlobalTheory.LogDerProj GlobalTheory.ZH.CrdCalc
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem mem_basicOpen_iff {R : Type} [CommRing R] {X : Scheme.{0}} (χ : Sp R ⟶ X) (W : X.Opens) (h : ⊤ ≤ χ ⁻¹ᵁ W)
    (g : Γ(X, W)) (q : Sp R) : χ q ∈ X.basicOpen g ↔ valHom χ W h g ∉ q.asIdeal := by
  have b := Scheme.basicOpen_appLE χ ⊤ W h g
  rw [top_inf_eq, basicOpen_eq_of_affine'] at b
  change q ∈ χ ⁻¹ᵁ X.basicOpen g ↔ _
  rw [← b]
  rfl

theorem mem_smul_top_of_chart {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (p : X ⟶ Sp K) (n : ℕ)
    [SmoothOfRelativeDimension n p] (Z : Closeds X) (hI : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal Z))
    (U : X.affineOpens) (D : LogKS.logDer p (Scheme.IdealSheafData.vanishingIdeal Z) U) (m : Ideal Γ(X, U.1))
    (hm : m.IsMaximal) {R ι : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra ℤ R] [Fintype ι] (χ : Sp R ⟶ X)
    (hx : χ (closedPoint R) ∈ U.1) (hxm : ∀ f ∈ m, χ (closedPoint R) ∉ X.basicOpen f)
    (T a : ι → R) (hT : ∀ i, Prime (T i)) (hZ : ∀ q : Sp R, χ q ∈ Z → ∏ i, T i ∈ q.asIdeal)
    (δ : Derivation ℤ R R) (hδ : ∀ r, δ (valR χ U.1 r) = valR χ U.1 (D.1 r)) (hδT : ∀ i, δ (T i) = a i * T i)
    (h0 : ∀ r, δ r ∈ maximalIdeal R) (ha : ∀ i, a i ∈ maximalIdeal R) :
    D ∈ m • (⊤ : Submodule Γ(X, U.1) (LogKS.logDer p (Scheme.IdealSheafData.vanishingIdeal Z) U)) := by
  classical
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hIdef : I = Scheme.IdealSheafData.vanishingIdeal Z := rfl
  haveI : Smooth p := SmoothOfRelativeDimension.smooth n p
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨-, O, hxO, r, s, J, hrsp, hO⟩ := hI (χ (closedPoint R))
  obtain ⟨V, hV, e, hxV, he, H⟩ := exists_coords p n _ O.1 hxO s hrsp
  obtain ⟨f, hfV, hxf⟩ := U.2.exists_basicOpen_le ⟨_, hxV⟩ hx
  let W : X.affineOpens := ⟨X.basicOpen f, U.2.basicOpen f⟩
  obtain ⟨z, bΩ, hz, hb⟩ := H W.1 hfV W.2
  let ix : Fin J.card → Fin r := fun i => (J.equivFin.symm i).1
  have hix : Function.Injective ix := fun i j h => J.equivFin.symm.injective (Subtype.ext h)
  have hWO : W ≤ O := hfV.trans hV
  have hideal : I.ideal W = Ideal.span {∏ i, z (e (ix i))} := by
    rw [← I.map_ideal hWO, hIdef, hO, Ideal.map_span, Set.image_singleton, map_prod, ← Finset.prod_coe_sort J,
      ← J.equivFin.symm.prod_comp]
    simp only [hz]
    rfl
  have hW : W.1 ≤ U.1 := X.basicOpen_le f
  letI : Algebra K Γ(X, W.1) := (algX p W.1).toAlgebra
  haveI : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  letI : Algebra Γ(X, U.1) Γ(X, W.1) := (resG X hW).toAlgebra
  haveI : IsLocalization.Away f Γ(X, W.1) := U.2.isLocalization_basicOpen f
  have hφ : (algX p U.1).FiniteType := by
    have h1 : (p.appLE ⊤ U.1 (by simp)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ U _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective)
  have hχ : ⊤ ≤ χ ⁻¹ᵁ W.1 := (top_le_iff χ W.1).2 hxf
  have hχU : ⊤ ≤ χ ⁻¹ᵁ U.1 := (top_le_iff χ U.1).2 hx
  have hval : ∀ g, valHom χ W.1 hχ (algebraMap Γ(X, U.1) Γ(X, W.1) g) = valR χ U.1 g := fun g =>
    (valR_eq χ W.1 hχ _).symm.trans (valR_res χ hW hχ g)
  refine mem_smul_top_of_coords (K := K) (B := Γ(X, W.1)) f (algX p U.1) hφ (GlobalTheory.TopForm.resG_comp_algX (p := p) hW)
    (I.ideal U) m hm (fun h => hxm f h hxf) z bΩ hb (e ∘ ix) (he.comp hix)
    ((I.map_ideal (U := W) (V := U) hW).trans hideal) (valHom χ W.1 hχ) (fun g hg => ?_) D δ
    (fun g => by rw [hval, hval]; exact hδ g) h0 (fun i => ?_)
  · rw [hval]
    exact fun hu => hxm g hg ((top_le_iff χ _).1 ((isUnit_valR_iff χ U.1 hχU g).1 hu))
  · have hrad : ∏ i, T i ∈ (Ideal.span {valHom χ W.1 hχ (z (e (ix i)))}).radical := by
      rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
      rintro P ⟨hP, hP'⟩
      let q : Sp R := (⟨P, hP'⟩ : PrimeSpectrum R)
      refine hZ q ?_
      have hq : χ q ∈ I.support := by
        rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := W) (hχ (Set.mem_univ q)), hideal,
          Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]
        rintro _ rfl
        rw [mem_basicOpen_iff χ W.1 hχ, not_not, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        exact Ideal.mul_mem_right _ _ (hP (Ideal.mem_span_singleton_self _))
      have hs : (I.support : Set X) = Z := by
        rw [hIdef, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      change χ q ∈ (Z : Set X)
      rw [← hs]
      exact hq
    obtain ⟨N, hN⟩ := hrad
    have hdvd := Ideal.mem_span_singleton.1 hN
    refine ⟨ne_zero_of_dvd_ne_zero (pow_ne_zero N (Finset.prod_ne_zero_iff.2 fun j _ => (hT j).ne_zero)) hdvd,
      exists_log_of_dvd _ δ h0 T a hT ha hδT N _ hdvd⟩

end Geometry

end GlobalTheory.LogBack

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartDer

theorem GlobalTheory.LogBack.mem_smul_top_of_vanish : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim (genStr Y) → FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → ∀ x : Y.X, x ∉ interior Y → x ∈ U.1 → (∀ f ∈ m, x ∉ Y.X.basicOpen f) → ∀ (k : Type) [Field k] (m' d : ℕ) (ξ : Sp (ChartRing k m' d) ⟶ gen Y) (x' : gen Y), ξ (closedPoint _) = x' → genι Y x' = x → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (FinalTheorems.stalkId (genBdIdeal Y) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom = Ideal.span {∏ i, bdParam k m' d i} → (∀ p : Sp (ChartRing k m' d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m' d i ∈ p.asIdeal) → ∀ (hU : ⊤ ≤ (ξ ≫ genι Y) ⁻¹ᵁ U.1) (DR : Derivation ℤ (ChartRing k m' d) (ChartRing k m' d)) (a : Fin m' → (ChartRing k m' d)), (∀ r, DR (valR (ξ ≫ genι Y) U.1 r) = valR (ξ ≫ genι Y) U.1 (D.1 r)) → (∀ i, DR (bdParam k m' d i) = a i * bdParam k m' d i) → (∀ r, residue _ (DR r) = 0) → (∀ i, residue _ (a i) = 0) → D ∈ m • (⊤ : Submodule Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) := by
  intro E _ _ _ H Dw l Xo c Y hs hsnc U D m hm x _ hxU hxm k _ m' d ξ x' hξ hx' _ _ hbd _ DR a hD hT h0 ha
  haveI := smooth_gen_iff.1 hs
  subst hξ hx'
  refine GlobalTheory.LogBack.mem_smul_top_of_chart Y.s Dw.dim (interior Y).compl (snc_gen_iff.1 hsnc) U D m hm (ξ ≫ genι Y)
    hxU hxm (bdParam k m' d) a (fun i => GlobalTheory.LogBack.prime_X _) (fun q hq => (hbd q).1 ?_) DR hD hT
    (fun r => (residue_eq_zero_iff _).1 (h0 r)) (fun i => (residue_eq_zero_iff _).1 (ha i))
  rw [mem_genBd_iff, ← coe_interior]
  exact hq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogVectorFieldMemMaxIdealSmulOfVanishingStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logVectorField_mem_maxIdeal_smul_of_vanishing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim (genStr Y) → FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → ∀ x : Y.X, x ∉ interior Y → x ∈ U.1 → (∀ f ∈ m, x ∉ Y.X.basicOpen f) → ∀ (k : Type) [Field k] (m' d : ℕ) (ξ : Sp (ChartRing k m' d) ⟶ gen Y) (x' : gen Y), ξ (closedPoint _) = x' → genι Y x' = x → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (FinalTheorems.stalkId (genBdIdeal Y) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom = Ideal.span {∏ i, bdParam k m' d i} → (∀ p : Sp (ChartRing k m' d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m' d i ∈ p.asIdeal) → ∀ (hU : ⊤ ≤ (ξ ≫ genι Y) ⁻¹ᵁ U.1) (DR : Derivation ℤ (ChartRing k m' d) (ChartRing k m' d)) (a : Fin m' → (ChartRing k m' d)), (∀ r, DR (valR (ξ ≫ genι Y) U.1 r) = valR (ξ ≫ genι Y) U.1 (D.1 r)) → (∀ i, DR (bdParam k m' d i) = a i * bdParam k m' d i) → (∀ r, residue _ (DR r) = 0) → (∀ i, residue _ (a i) = 0) → D ∈ m • (⊤ : Submodule Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) := by
  first | exact @GlobalTheory.LogBack.mem_smul_top_of_vanish | exact GlobalTheory.LogBack.mem_smul_top_of_vanish | (intros; apply GlobalTheory.LogBack.mem_smul_top_of_vanish <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedBoundaryPointMaximalIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedBoundaryPointMaximalIdeal
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartDer

namespace GlobalTheory.BoundaryPoint

theorem isClosed_of_isMaximal {X : Scheme.{0}} [JacobsonSpace X] {U : X.Opens} (hU : IsAffineOpen U)
    {m : Ideal Γ(X, U)} (hm : m.IsMaximal) {x : X} (hx : x ∈ U) (h : ∀ f ∈ m, x ∉ X.basicOpen f) :
    IsClosed ({x} : Set X) := by
  have e := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have hle : m ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := fun f hf => by
    by_contra hc
    refine h f hf ?_
    have h₁ : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact hc
    have h₂ : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f := h₁
    rwa [e] at h₂
  have hmax : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.IsMaximal :=
    hm.eq_of_le (hU.primeIdealOf ⟨x, hx⟩).isPrime.ne_top hle ▸ hm
  have hc := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hmax
  have h₃ : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹' closedPoints X := by
    rw [hU.fromSpec.isOpenEmbedding.preimage_closedPoints]
    exact hc
  have h₄ : IsClosed ({hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩)} : Set X) := h₃
  rwa [e] at h₄

theorem exists_closed_boundary_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim (genStr Y) → ∀ (U : Y.X.affineOpens) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → ∀ x : Y.X, x ∉ interior Y → x ∈ U.1 → (∀ f ∈ m, x ∉ Y.X.basicOpen f) → ∃ x' : gen Y, genι Y x' = x ∧ x' ∈ genBd Y ∧ IsClosed ({x'} : Set (gen Y)) := by
  intro E _ _ _ H Dw l Xo c Y hs U m hm x hx hU h
  have hi : IsIso (genι Y) := GlobalTheory.LogKS.isIso_fst Y
  have : Smooth (genStr Y) := SmoothOfRelativeDimension.smooth Dw.dim _
  have : JacobsonSpace Y.X := LocallyOfFiniteType.jacobsonSpace (inv (genι Y) ≫ genStr Y)
  have hc := isClosed_of_isMaximal U.2 hm hU h
  obtain ⟨x', rfl⟩ := (genι Y).homeomorph.surjective x
  refine ⟨x', rfl, mem_genBd_iff.2 fun h' => hx ?_, ?_⟩
  · rw [← coe_interior] at h'
    exact h'
  · rw [← (genι Y).homeomorph.isClosed_image, Set.image_singleton]
    exact hc

end GlobalTheory.BoundaryPoint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedBoundaryPointMaximalIdealStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedBoundaryPoint_maximalIdeal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim (genStr Y) → ∀ (U : Y.X.affineOpens) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → ∀ x : Y.X, x ∉ interior Y → x ∈ U.1 → (∀ f ∈ m, x ∉ Y.X.basicOpen f) → ∃ x' : gen Y, genι Y x' = x ∧ x' ∈ genBd Y ∧ IsClosed ({x'} : Set (gen Y)) := by
  first | exact @GlobalTheory.BoundaryPoint.exists_closed_boundary_point | exact GlobalTheory.BoundaryPoint.exists_closed_boundary_point | (intros; apply GlobalTheory.BoundaryPoint.exists_closed_boundary_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerInjectiveModMaximalBoundary
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartDer

def constEps {σ k : Type} [Field k] (δ : Derivation ℤ (MvPowerSeries σ k) (MvPowerSeries σ k)) :
    MvPowerSeries σ k →+* DualNumber k where
  toFun r := TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (δ r))
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [Derivation.leibniz, mul_comm, add_comm]

theorem constEps_apply {σ k : Type} [Field k] (δ : Derivation ℤ (MvPowerSeries σ k) (MvPowerSeries σ k))
    (r : MvPowerSeries σ k) :
    constEps δ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) +
      TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (δ r)) := rfl

theorem residue_eq_zero_iff_constantCoeff {σ k : Type} [Field k] (r : MvPowerSeries σ k) :
    residue _ r = 0 ↔ MvPowerSeries.constantCoeff r = 0 := by
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero,
    not_not]

theorem logKS_inj_mod_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → (∃ x, x ∉ interior Y ∧ x ∈ U.1 ∧ ∀ f ∈ m, x ∉ Y.X.basicOpen f) → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) := by
  intro E _ _ _ H Dw l Xo c Y hpq hsm hsnc hrig U n v A hv hvb hA D Θ m hm hx hKS hΘ
  obtain ⟨x, hxi, hxU, hxm⟩ := hx
  have h2 := GlobalTheory.T.exists_closedBoundaryPoint_maximalIdeal E H Dw l Xo c Y hsm U m hm x hxi hxU hxm
  obtain ⟨x', hx'x, hx'bd, hx'cl⟩ := h2
  have h3 := hrig x' hx'bd hx'cl
  obtain ⟨k, _, m', d, ξ, t, P, gam, hξ, hEt, hId, hBd, hSAB, hMon, hPart, hRig⟩ := h3
  have hxU' : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1 := by
    show genι Y (ξ (closedPoint _)) ∈ U.1
    rw [hξ, hx'x]
    exact hxU
  have hU : ⊤ ≤ (ξ ≫ genι Y) ⁻¹ᵁ U.1 := top_le_preimage_of_closedPoint _ _ hxU'
  have h4 := GlobalTheory.ChartDer.logDer_extend_chartRing E H Dw l Xo c Y U D k m' d ξ hxU' hEt hId
  obtain ⟨DR, hDR0, hDRt⟩ := h4
  have hval : ∀ r, valR (ξ ≫ genι Y) U.1 r = ((Scheme.stalkClosedPointTo ξ).hom.comp
      (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hxU').hom.comp ((genι Y).app U.1).hom)) r := by
    intro r
    have e := ReciprocityTheory.ChartRestriction.G.PullbackSections.germ_stalkClosedPointTo_eq ξ (genι Y ⁻¹ᵁ U.1) hxU'
    have e2 := congrArg (fun φ => φ.hom (((genι Y).app U.1).hom r)) e
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
    rw [RingHom.comp_apply, RingHom.comp_apply, e2, valR, dite_eq_left hU, Scheme.Hom.comp_appLE]
    rfl
  have hDR : ∀ r, DR (valR (ξ ≫ genι Y) U.1 r) = valR (ξ ≫ genι Y) U.1 (D.1 r) := by
    intro r
    rw [hval, hval]
    exact hDR0 r
  have ha' : ∀ i, ∃ a, DR (bdParam k m' d i) = a * bdParam k m' d i := fun i => by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (hDRt i)
    exact ⟨a, ha.symm⟩
  choose a ha using ha'
  have hc := GlobalTheory.T.degeneration_constant_of_logKodairaSpencer_mem E H Dw l Xo c Y hpq hsm hsnc U n v A hv hvb hA D Θ m hm x hxi hxU hxm hKS hΘ k m' d ξ x' hξ
    hx'x t P gam hEt hId hBd hSAB hMon hPart hU DR a hDR ha (constEps DR) (constEps_apply DR)
  obtain ⟨c₀, hc₀, hcc⟩ := hc
  have ht0 : ∀ i, MvPowerSeries.constantCoeff (bdParam k m' d i) = 0 := fun i => by simp
  have hsnd : ∀ r, (constEps DR r).snd = 0 := by
    have h1 : ∀ r ∈ maximalIdeal (ChartRing k m' d), (constEps DR r).fst = 0 := fun r hr => by
      rw [constEps_apply]
      simpa using (residue_eq_zero_iff_constantCoeff r).1 ((residue_eq_zero_iff r).2 hr)
    have h2 : ∀ i, constEps DR (bdParam k m' d i) = 0 := fun i => by
      rw [constEps_apply, ha i, map_mul, ht0 i, mul_zero]
      simp
    exact hRig k (constEps DR) _ h1 h2 hcc
  have hres : ∀ r, residue _ (DR r) = 0 := fun r => by
    rw [residue_eq_zero_iff_constantCoeff]
    simpa [constEps_apply] using hsnd r
  haveI : CharZero k := by
    let f : c.F →+* k := MvPowerSeries.constantCoeff.comp (Spec.preimage (ξ ≫ genι Y ≫ Y.s)).hom
    exact charZero_of_injective_ringHom f.injective
  have hli : LinearIndependent ℤ (fun i => (gam i : LinearMap.BilinForm ℤ P.D.toPre.X)) :=
    hPart.linearIndependent.map' (levelForms H l.M' P.D.toPre.X).subtype (Submodule.ker_subtype _)
  have hdir := GlobalTheory.ConstPointCone.dir_eq_zero_of_const (ChartRing k m' d) P.D.toPre m' (bdParam k m' d)
    (fun i => gam i) hMon hli (fun i => by simp [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff])
    (fun i y z => (gam i).2.1 y z) k (constEps DR) _ hsnd hcc
  have ha0 : ∀ i, residue _ (a i) = 0 := fun i => by
    rw [residue_eq_zero_iff_constantCoeff]
    have := congrFun hdir i
    simp only [Pi.zero_apply, mul_eq_zero, Rat.cast_eq_zero, hc₀, false_or] at this
    exact this
  exact GlobalTheory.T.logVectorField_mem_maxIdeal_smul_of_vanishing E H Dw l Xo c Y hsm hsnc U D m hm x hxi hxU hxm k m' d ξ x' hξ hx'x hEt hId hBd hU DR a hDR ha
    hres ha0

end GlobalTheory.ChartDer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerInjectiveModMaximalBoundaryStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logKodairaSpencer_injective_mod_maximal_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → (∃ x, x ∉ interior Y ∧ x ∈ U.1 ∧ ∀ f ∈ m, x ∉ Y.X.basicOpen f) → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) := by
  first | exact @GlobalTheory.ChartDer.logKS_inj_mod_boundary | exact GlobalTheory.ChartDer.logKS_inj_mod_boundary | (intros; apply GlobalTheory.ChartDer.logKS_inj_mod_boundary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerInjectiveClosedInteriorPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerInjectiveClosedInteriorPoint
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InteriorKS

theorem exists_sum_smul {F R : Type} [CommRing F] [CommRing R] [Algebra F R] [Algebra.Smooth F R]
    (D : Derivation ℤ R R) (hD : ∀ a, D (algebraMap F R a) = 0) (m : Ideal R) (hm : ∀ r, D r ∈ m) :
    ∃ (n : ℕ) (c : Fin n → R) (δ : Fin n → Derivation ℤ R R), (∀ k, c k ∈ m) ∧
      (∀ k a, δ k (algebraMap F R a) = 0) ∧ D = ∑ k, c k • δ k := by
  let DF : Derivation F R R :=
    { toFun := D
      map_add' := map_add D
      map_smul' := fun a r => by simp [Algebra.smul_def, hD]
      map_one_eq_zero' := D.map_one_eq_zero
      leibniz' := D.leibniz }
  let L : Ω[R⁄F] →ₗ[R] R := DF.liftKaehlerDifferential
  have hL : ∀ r, L (KaehlerDifferential.D F R r) = D r := fun r => DF.liftKaehlerDifferential_comp_D r
  have hLm : ∀ w, L w ∈ m := by
    intro w
    have hw : w ∈ Submodule.span R (Set.range (KaehlerDifferential.D F R)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    refine (Submodule.span_le (p := Submodule.comap L m)).2 ?_ hw
    rintro _ ⟨r, rfl⟩
    show L _ ∈ m
    rw [hL]; exact hm r
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R Ω[R⁄F]
  refine ⟨n, fun k => L (p (Pi.single k 1)),
    fun k => (((LinearMap.proj k : (Fin n → R) →ₗ[R] R) ∘ₗ i).compDer (KaehlerDifferential.D F R)).restrictScalars ℤ,
    fun k => hLm _, fun k a => by simp, ?_⟩
  ext r
  have e : KaehlerDifferential.D F R r = ∑ k, i (KaehlerDifferential.D F R r) k • p (Pi.single k 1) := by
    have e0 := LinearMap.congr_fun hpi (KaehlerDifferential.D F R r)
    rw [LinearMap.comp_apply, LinearMap.id_apply, pi_eq_sum_univ' (i _)] at e0
    simpa using e0.symm
  have hs : ∀ δ : Fin n → Derivation ℤ R R, (∑ k, δ k) r = ∑ k, δ k r := fun δ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
    rfl
  rw [← hL, e, hs]
  simp [mul_comm]

theorem mem_smul_top {F : Type} [CommRing F] {X : Scheme.{0}} (s : X ⟶ Sp F) [Smooth s] (I : X.IdealSheafData)
    (U : X.affineOpens) (D : logDer s I U) (m : Ideal Γ(X, U.1)) (hm : m.IsMaximal) (h : Γ(X, U.1)) (hI : h ∈ I.ideal U)
    (hh : h ∉ m) (hD : ∀ r, D.1 r ∈ m) : D ∈ m • (⊤ : Submodule Γ(X, U.1) (logDer s I U)) := by
  let φ : F →+* Γ(X, U.1) := (s.appLE ⊤ U.1 (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  have hφ : φ.Smooth := by
    refine RingHom.Smooth.comp ?_ (Smooth.smooth_appLE s (isAffineOpen_top _) U.2 _)
    exact RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv)
  letI := φ.toAlgebra
  haveI : Algebra.Smooth F Γ(X, U.1) := hφ
  obtain ⟨n, c, δ, hc, hδ, e⟩ := exists_sum_smul (F := F) D.1 D.2.1 m hD
  obtain ⟨y, z, hz, hyz⟩ := hm.exists_inv hh
  let δ' : Fin n → logDer s I U := fun k => ⟨(y * h) • δ k, fun a => by
    have : δ k (constFn s U.1 a) = 0 := hδ k a
    simp [this], fun f _ => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hI)⟩
  have e' : D = z • D + ∑ k, c k • δ' k := by
    apply Subtype.ext
    have : (∑ k, c k • δ' k : logDer s I U).1 = (y * h) • D.1 := by
      rw [e, Finset.smul_sum, Submodule.coe_sum]
      exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    rw [Submodule.coe_add, this, Submodule.coe_smul, ← add_smul, add_comm, hyz, one_smul]
  rw [e']
  exact add_mem (Submodule.smul_mem_smul hz trivial) (sum_mem fun k _ => Submodule.smul_mem_smul (hc k) trivial)

def dualConst {k R : Type} [Field k] [CommRing R] (ρ : R →+* DualNumber k) : R →+* DualNumber k :=
  (algebraMap k (DualNumber k)).comp ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)

theorem constPt_spMap {K R : Type} [Field K] [CommRing R] (ψ : R →+* DualNumber K) :
    constPt (spMap ψ) = spMap (dualConst ψ) := by
  rw [constPt, spMap_comp', spMap_comp']
  rfl

theorem chart_comp {F : Type} [CommRing F] {X : Scheme.{0}} (s : X ⟶ Sp F) (U : X.affineOpens) :
    ∃ σ : F →+* Γ(X, U.1), (∀ a, σ a = constFn s U.1 a) ∧ chart U ≫ s = spMap σ := by
  refine ⟨(s.appLE ⊤ U.1 (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom, fun _ => rfl, ?_⟩
  have h := IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top (Spec (CommRingCat.of F))) U.2 (fun _ _ => trivial)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  exact h.symm

theorem snd_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens)
    {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (D : Γ(Y.X, U.1) → Γ(Y.X, U.1))
    (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (hv : ∀ i, IsTanAtG Y.t (chart U) (v i))
    (hKS : IsKS Y.t (interior Y) U v D Θ) {K : Type} [Field K] (φ : Γ(Y.X, U.1) →+* DualNumber K)
    (hφ : ∀ r, (φ r).snd = (φ (D r)).fst) (hΘ : ∀ a b, (φ (Θ a b)).fst = 0)
    (hV : ⊤ ≤ (spMap φ ≫ chart U) ⁻¹ᵁ interior Y) (hc : ∀ a, (φ (constFn Y.s U.1 a)).snd = 0) (r : Γ(Y.X, U.1)) :
    (φ r).snd = 0 := by
  obtain ⟨y', hy'⟩ : ∃ y' : Sp (DualNumber K) ⟶ Xo.XF c, y' ≫ Y.j = spMap φ ≫ chart U :=
    ⟨_, IsOpenImmersion.lift_fac Y.j _ (by rintro _ ⟨p, rfl⟩; exact hV (Set.mem_univ p))⟩
  obtain ⟨σ, hσ, hcs⟩ := chart_comp Y.s U
  letI : Algebra c.F K := ((TrivSqZeroExt.fstHom K K K).toRingHom.comp (φ.comp σ)).toAlgebra
  obtain ⟨A', _, lam, hlam⟩ := GlobalTheory.FlagTan.exists_isGrpPullback Y.oF.t.G y'
  obtain ⟨A₀, _, i, hi⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A' (GlobalTheory.DeRham.epsRed K)
  have hπ' := hlam.comp Y.m0.cart
  have hι' : IsGrpPullback A' Y.t.G (spMap φ ≫ chart U) _ := (hlam.comp Y.m.cart).congr hy' rfl
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ'
  obtain ⟨ρ, hρ, -, hiρ⟩ := exists_isConstK Y.t (interior Y) U v D Θ hv hKS φ hφ hΘ hV A₀ A' _ i hA' hι' hi
  have e₁ := eq_constPt c hi hπ' hiρ hρ
  have hjs : Y.j ≫ Y.s = pullback.snd _ _ := by
    have h0 : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over, h0, Category.comp_id]
  have e₂ : y' ≫ pullback.snd _ _ = spMap (φ.comp σ) := by
    rw [← hjs, reassoc_of% hy', hcs, spMap_comp']
  have e₃ : y' = constPt y' := by
    refine pullback.hom_ext e₁ ?_
    show _ = constPt (y' ≫ pullback.snd _ _)
    rw [e₂, constPt_spMap]
    congr 1
    ext a
    · simp [dualConst, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [dualConst, TrivSqZeroExt.algebraMap_eq_inl, hσ, hc]
  have e₄ : spMap φ ≫ chart U = spMap (dualConst φ) ≫ chart U := by
    rw [← constPt_spMap]
    show _ = constPt (spMap φ ≫ chart U)
    rw [← hy']
    exact congrArg (· ≫ Y.j) e₃
  have hU : IsAffineOpen U.1 := U.2
  haveI : Mono (chart U) := inferInstanceAs (Mono hU.fromSpec)
  have e₅ : φ = dualConst φ := congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 e₄))
  rw [e₅]
  simp [dualConst, TrivSqZeroExt.algebraMap_eq_inl]


set_option maxHeartbeats 1000000 in
theorem mem_smul_top_of_isKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → (∃ x ∈ interior Y, x ∈ U.1 ∧ ∀ f ∈ m, x ∉ Y.X.basicOpen f) → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) := by
  intro E _ _ _ H Dw l Xo c Y _ hs _ _ U n v A hv _ _ D Θ m hm ⟨x, hxi, hxU, hx⟩ hKS hΘ
  have hs' := smooth_gen_iff.1 hs
  haveI : Smooth Y.s := SmoothOfRelativeDimension.smooth Dw.dim Y.s
  have hU : IsAffineOpen U.1 := U.2
  obtain ⟨h, hle, hxh⟩ := hU.exists_basicOpen_le (V := interior Y) ⟨x, hxi⟩ hxU
  have hh : h ∉ m := fun hh => hx h hh hxh
  have hI : h ∈ (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal U := by
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
    intro p hp
    by_contra hn
    refine hp (hle ?_)
    have : p ∈ hU.fromSpec ⁻¹ᵁ Y.X.basicOpen h := by
      rw [hU.fromSpec_preimage_basicOpen]; exact hn
    exact this
  refine mem_smul_top Y.s _ U D m hm h hI hh fun r => ?_
  obtain ⟨K, _, π, hπ⟩ : ∃ (K : Type) (_ : Field K) (π : Γ(Y.X, U.1) →+* K), ∀ r, π r = 0 ↔ r ∈ m :=
    ⟨Γ(Y.X, U.1) ⧸ m, Ideal.Quotient.field m, Ideal.Quotient.mk m, fun _ => Ideal.Quotient.eq_zero_iff_mem⟩
  obtain ⟨φ, hf, hsn⟩ : ∃ φ : Γ(Y.X, U.1) →+* DualNumber K, (∀ r, (φ r).fst = π r) ∧ ∀ r, (φ r).snd = π (D.1 r) :=
    ⟨(dualMap π).comp (epsHom D.1), fun r => by simp [epsHom, dualMap], fun r => by simp [epsHom, dualMap]⟩
  have hV : ⊤ ≤ (spMap φ ≫ chart U) ⁻¹ᵁ interior Y := by
    intro p _
    refine hle ?_
    have : spMap φ p ∈ hU.fromSpec ⁻¹ᵁ Y.X.basicOpen h := by
      rw [hU.fromSpec_preimage_basicOpen]
      intro hp
      have hu : IsUnit (φ h) := by
        rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hf]
        exact Ne.isUnit fun h0 => hh ((hπ h).1 h0)
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)
    exact this
  rw [← hπ, ← hsn]
  exact snd_eq_zero Y U v D.1 Θ hv hKS φ (fun r => (hsn r).trans (hf _).symm)
    (fun a b => (hf _).trans ((hπ _).2 (hΘ a b))) hV (fun a => by rw [hsn, D.2.1 a, map_zero]) r

end GlobalTheory.InteriorKS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerInjectiveClosedInteriorPointStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_injective_closed_interior_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → (∃ x ∈ interior Y, x ∈ U.1 ∧ ∀ f ∈ m, x ∉ Y.X.basicOpen f) → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) := by
  first | exact @GlobalTheory.InteriorKS.mem_smul_top_of_isKS | exact GlobalTheory.InteriorKS.mem_smul_top_of_isKS | (intros; apply GlobalTheory.InteriorKS.mem_smul_top_of_isKS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerInjectiveModMaximalIdeal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_point_vanishing_of_isMaximal {X : Scheme} (U : X.affineOpens) (m : Ideal Γ(X, U.1))
    (hm : m.IsMaximal) : ∃ x, x ∈ U.1 ∧ ∀ f ∈ m, x ∉ X.basicOpen f := by
  let p : PrimeSpectrum Γ(X, U.1) := ⟨m, hm.isPrime⟩
  refine ⟨U.2.fromSpec p, ?_, ?_⟩
  · have h : U.2.fromSpec p ∈ Set.range U.2.fromSpec := ⟨p, rfl⟩
    rw [U.2.range_fromSpec] at h
    exact h
  · intro f hf hx
    have h : p ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen f := hx
    rw [U.2.fromSpec_preimage_basicOpen] at h
    exact h hf

theorem logKS_inj_mod_maximal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) := by
  intro E _ _ _ H Dw l Xo c Y hpq hsm hsnc hrig U n v A hv hbasis hact D Θ m hm hKS hΘ
  have hp := exists_point_vanishing_of_isMaximal U m hm
  obtain ⟨x, hxU, hxm⟩ := hp
  by_cases hx : x ∈ LogKS.interior Y
  · exact GlobalTheory.T.kodairaSpencer_injective_closed_interior_point E H Dw l Xo c Y hpq hsm hsnc hrig U n v A hv hbasis hact D Θ m hm
      ⟨x, hx, hxU, hxm⟩ hKS hΘ
  · have hb : ∃ x, x ∉ LogKS.interior Y ∧ x ∈ U.1 ∧ ∀ f ∈ m, x ∉ Y.X.basicOpen f := ⟨x, hx, hxU, hxm⟩
    have key := GlobalTheory.T.logKodairaSpencer_injective_mod_maximal_boundary E H Dw l Xo c Y hpq hsm hsnc hrig U n v A hv hbasis hact D Θ m hm
    first
      | exact key hb hKS hΘ
      | exact key hKS hΘ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerInjectiveModMaximalIdealStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logKodairaSpencer_injective_mod_maximalIdeal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) := by
  first | exact @GlobalTheory.logKS_inj_mod_maximal | exact GlobalTheory.logKS_inj_mod_maximal | (intros; apply GlobalTheory.logKS_inj_mod_maximal <;> assumption)
end

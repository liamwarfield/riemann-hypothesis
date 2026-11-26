module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusCoordinateIsUnit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalZeroOfMemHomogeneousIdeal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreRepresentationSmooth
public import GroundTheory.ArithmeticGeometry.ModularCurves.WeierstrassGenus

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusMonomialEvalCompat
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoTorus

variable {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ}

theorem evV_awayMap (i : X ⟶ PSpace K N) {f g x : MvPolynomial (Fin (N + 1)) K} {m : ℕ}
    (hg : g ∈ grK K N m) (hx : x = f * g) (V : X.Opens)
    (hVf : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) f) (hVx : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) x)
    (a : HomogeneousLocalization.Away (grK K N) f) :
    evV i x V hVx (HomogeneousLocalization.awayMap (grK K N) hg hx a) = evV i f V hVf a := by
  have h := congrArg (fun φ => φ.hom a) (Proj.awayMap_awayToSection (grK K N) hg hx)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h
  simp only [evV, RingHom.comp_apply]
  rw [h, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem evV_mul_cross (i : X ⟶ PSpace K N) {f g u : MvPolynomial (Fin (N + 1)) K} {a b n m : ℕ}
    (hf : f ∈ grK K N a) (hg : g ∈ grK K N b) (V : X.Opens)
    (hVf : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) f) (hVg : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g)
    (hu : u ∈ grK K N (n • a)) (hu' : u ∈ grK K N (m • b)) (hfn : f ^ n ∈ grK K N (m • b)) :
    evV i f V hVf (HomogeneousLocalization.Away.mk (grK K N) hf n u hu) *
        evV i g V hVg (HomogeneousLocalization.Away.mk (grK K N) hg m (f ^ n) hfn) =
      evV i g V hVg (HomogeneousLocalization.Away.mk (grK K N) hg m u hu') := by
  have hVx : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (f * g) := by
    rw [Proj.basicOpen_mul]
    exact le_inf hVf hVg
  rw [← evV_awayMap i hg rfl V hVf hVx, ← evV_awayMap i hf (mul_comm f g) V hVg hVx,
    ← evV_awayMap i hf (mul_comm f g) V hVg hVx, ← map_mul]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
  refine Localization.mk_eq_mk_iff.mpr ?_
  rw [Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul]
  ring

theorem mk_prod_pow {m e : ℕ} {g : MvPolynomial (Fin (N + 1)) K} (hg : g ∈ grK K N e)
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, y k ∈ grK K N (1 • e)) (β : Fin m → ℕ) {n : ℕ}
    (hn : ∑ k, β k = n) (h : ∏ k, y k ^ β k ∈ grK K N (n • e)) :
    HomogeneousLocalization.Away.mk (grK K N) hg n (∏ k, y k ^ β k) h =
      ∏ k, HomogeneousLocalization.Away.mk (grK K N) hg 1 (y k) (hy k) ^ β k := by
  subst hn
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, ← HomogeneousLocalization.algebraMap_apply, map_prod]
  simp only [map_pow, HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  have key : ∀ s : Finset (Fin m), Localization.mk (∏ k ∈ s, y k ^ β k)
      (⟨g ^ ∑ k ∈ s, β k, ⟨_, rfl⟩⟩ : Submonoid.powers g) =
      ∏ k ∈ s, Localization.mk (y k) (⟨g ^ 1, ⟨_, rfl⟩⟩ : Submonoid.powers g) ^ β k := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Localization.mk_one]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ← ih, Localization.mk_pow, Localization.mk_mul]
      congr 1
      apply Subtype.ext
      simp [Finset.sum_insert ha, pow_add, ← pow_mul]
  exact key Finset.univ

theorem mk_add' {f u v : MvPolynomial (Fin (N + 1)) K} {a n : ℕ} (hf : f ∈ grK K N a) (hu : u ∈ grK K N (n • a))
    (hv : v ∈ grK K N (n • a)) (h : u + v ∈ grK K N (n • a)) :
    HomogeneousLocalization.Away.mk (grK K N) hf n (u + v) h =
      HomogeneousLocalization.Away.mk (grK K N) hf n u hu + HomogeneousLocalization.Away.mk (grK K N) hf n v hv := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_add, HomogeneousLocalization.Away.val_mk, Localization.add_mk_self]

theorem mk_C_mul {f u : MvPolynomial (Fin (N + 1)) K} {a n : ℕ} (hf : f ∈ grK K N a) (r : K)
    (hr : MvPolynomial.C r ∈ grK K N (0 • a)) (hu : u ∈ grK K N (n • a)) (h : MvPolynomial.C r * u ∈ grK K N (n • a)) :
    HomogeneousLocalization.Away.mk (grK K N) hf n (MvPolynomial.C r * u) h =
      HomogeneousLocalization.Away.mk (grK K N) hf 0 (MvPolynomial.C r) hr *
        HomogeneousLocalization.Away.mk (grK K N) hf n u hu := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
  congr 1
  apply Subtype.ext
  simp

theorem mk_zero' {f : MvPolynomial (Fin (N + 1)) K} {a n : ℕ} (hf : f ∈ grK K N a) (h : 0 ∈ grK K N (n • a)) :
    HomogeneousLocalization.Away.mk (grK K N) hf n 0 h = 0 := by
  apply HomogeneousLocalization.val_injective
  simp [Localization.mk_zero]

theorem evV_const (i : X ⟶ PSpace K N) (q : X ⟶ Spec (CommRingCat.of K)) (hq : i ≫ PSpace.str K N = q)
    {f : MvPolynomial (Fin (N + 1)) K} {a : ℕ} (hf : f ∈ grK K N a) (V : X.Opens)
    (hVf : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) f) (r : K) (hr : MvPolynomial.C r ∈ grK K N (0 • a)) :
    evV i f V hVf (HomogeneousLocalization.Away.mk (grK K N) hf 0 (MvPolynomial.C r) hr) = strV q V r := by
  subst hq
  have h0 : HomogeneousLocalization.Away.mk (grK K N) hf 0 (MvPolynomial.C r) hr =
      HomogeneousLocalization.fromZeroRingHom (grK K N) _ (algebraMap K (grK K N 0) r) := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.fromZeroRingHom]
  have e : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (i ≫ PSpace.str K N).appLE ⊤ V le_top =
      CommRingCat.ofHom (algebraMap K (grK K N 0)) ≫ (Scheme.ΓSpecIso (CommRingCat.of (grK K N 0))).inv ≫
        (Proj.toSpecZero (grK K N)).appTop ≫ i.appLE ⊤ V le_top := by
    have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K (grK K N 0)))
    rw [reassoc_of% hn, Scheme.Hom.comp_appLE, PSpace.str, Scheme.Hom.comp_app, Category.assoc]
    rfl
  rw [h0]
  simp only [evV, RingHom.comp_apply, strV]
  rw [e, GroundTheory.Arith.Modular.awayToSection_fromZero (grK K N) hf]
  have h2 := Scheme.Hom.map_appLE i hVf (homOfLE (le_top : Proj.basicOpen (grK K N) f ≤ ⊤)).op
  exact congrArg (fun φ => φ.hom ((Scheme.Hom.appTop (Proj.toSpecZero (grK K N)))
    ((Scheme.ΓSpecIso (CommRingCat.of (grK K N 0))).inv (algebraMap K (grK K N 0) r)))) h2

def bS {m : ℕ} (S : Finset (Fin m)) (j : ℕ) (k : Fin m) : ℕ := if k ∈ S then j else 0

theorem sum_bS {m : ℕ} (S : Finset (Fin m)) (j : ℕ) : ∑ k, bS S j k = j * S.card := by
  simp [bS, mul_comm]

theorem yS_pow {m : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (S : Finset (Fin m)) (j : ℕ) :
    yS y S ^ j = ∏ k, y k ^ bS S j k := by
  simp [yS, bS, pow_ite, Finset.prod_ite_mem, Finset.prod_pow]

theorem mono_mem {m e n : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e)
    (α : Fin m → ℕ) (hα : ∑ k, α k = n) : ∏ k, y k ^ α k ∈ grK K N (n • e) := by
  have h := MvPolynomial.IsHomogeneous.prod Finset.univ (fun k => y k ^ α k) (fun k => e * α k)
    (fun k _ => (hy k).pow (α k))
  rw [← Finset.mul_sum, hα] at h
  rw [MvPolynomial.mem_homogeneousSubmodule, smul_eq_mul, mul_comm]
  exact h

theorem mem_expS {d : ℕ} (S : Finset (Fin (d + 1))) (j : ℕ) (α : Fin (d + 1) → ℕ) (hα : ∑ k, α k = j * S.card) :
    (fun k : Fin d => (α k.succ : ℤ) - (bS S j k.succ : ℤ)) ∈ expS S := by
  refine ⟨fun k hk => ?_, fun h0 => ?_⟩
  · simp [bS, hk]
  · have h1 := sum_bS S j
    rw [Fin.sum_univ_succ] at h1 hα
    have h2 : bS S j 0 = 0 := by simp [bS, h0]
    rw [h2, zero_add] at h1
    rw [Finset.sum_sub_distrib]
    have h3 : ((∑ k : Fin d, α k.succ : ℕ) : ℤ) + α 0 = ((∑ k : Fin d, bS S j k.succ : ℕ) : ℤ) := by
      rw [h1, ← hα]; push_cast; ring
    push_cast at h3
    have h4 : (0 : ℤ) ≤ α 0 := by positivity
    linarith

theorem evV_monomial {d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k))
    (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S))
    (ht : ∀ k, IsUnit (tV i y hy V hV k)) {j : ℕ} (α : Fin (d + 1) → ℕ) (hα : ∑ k, α k = j * S.card)
    (h : ∏ k, y k ^ α k ∈ grK K N (j • (S.card * e))) :
    evV i (yS y S) V hS (HomogeneousLocalization.Away.mk (grK K N) (yS_mem y hy S) j (∏ k, y k ^ α k) h) =
      tpow (fun k => (ht k).unit) (fun k : Fin d => (α k.succ : ℤ) - (bS S j k.succ : ℤ)) := by
  have h0 : y 0 ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule e (y 0)).2 (hy 0)
  have hV0 : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0) :=
    hV.trans (iInf_le (fun k => i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) 0)
  have hy1 : ∀ k, y k ∈ grK K N (1 • e) := fun k => by
    simpa using (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)
  have one : HomogeneousLocalization.Away.mk (grK K N) h0 1 (y 0) (hy1 0) = 1 := by
    apply HomogeneousLocalization.val_injective
    simp [Localization.mk_self]
  have A2 : ∀ (γ : Fin (d + 1) → ℕ) (hγ : ∑ k, γ k = j * S.card)
      (h' : ∏ k, y k ^ γ k ∈ grK K N ((j * S.card) • e)),
      evV i (y 0) V hV0 (HomogeneousLocalization.Away.mk (grK K N) h0 (j * S.card) (∏ k, y k ^ γ k) h') =
        ∏ k : Fin d, tV i y hy V hV k ^ γ k.succ := by
    intro γ hγ h'
    rw [mk_prod_pow h0 y hy1 γ hγ h', map_prod, Fin.prod_univ_succ]
    simp only [map_pow, one, map_one, one_pow, one_mul]
    rfl
  have hu' : ∏ k, y k ^ α k ∈ grK K N ((j * S.card) • e) := mono_mem y hy α hα
  have hβ' : ∏ k, y k ^ bS S j k ∈ grK K N ((j * S.card) • e) := mono_mem y hy _ (sum_bS S j)
  have hfn : yS y S ^ j ∈ grK K N ((j * S.card) • e) := by rw [yS_pow]; exact hβ'
  have A1 := evV_mul_cross i (yS_mem y hy S) h0 V hS hV0 h hu' hfn
  have A3 : evV i (y 0) V hV0 (HomogeneousLocalization.Away.mk (grK K N) h0 (j * S.card) (yS y S ^ j) hfn) =
      ∏ k : Fin d, tV i y hy V hV k ^ bS S j k.succ := by
    rw [← A2 _ (sum_bS S j) hβ']
    simp only [yS_pow]
  rw [A2 α hα hu', A3] at A1
  let U : Γ(X, V)ˣ := ∏ k : Fin d, (ht k).unit ^ bS S j k.succ
  have hU : (U : Γ(X, V)) = ∏ k : Fin d, tV i y hy V hV k ^ bS S j k.succ := by
    simp [U, Units.coe_prod]
  rw [← hU] at A1
  refine (Units.mul_left_inj U).1 ?_
  rw [A1, tpow, ← Units.val_mul]
  simp only [U]
  rw [← Finset.prod_mul_distrib, Units.coe_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [zpow_sub, zpow_natCast, zpow_natCast, inv_mul_cancel_right]
  simp

theorem aeval_mem_torusS {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens}
    (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) (_he : 0 < e)
    (q : X ⟶ Spec (CommRingCat.of K)) (hq : i ≫ PSpace.str K N = q) (S : Finset (Fin (d + 1)))
    (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S)) (ht : ∀ k, IsUnit (tV i y hy V hV k)) {j : ℕ}
    (c : MvPolynomial (Fin (d + 1)) K) (hc : c.IsHomogeneous (j * S.card)) :
    letI := (strV q V).toAlgebra
    evV i (yS y S) V hS (HomogeneousLocalization.Away.mk (grK K N) (yS_mem y hy S) j (MvPolynomial.aeval y c)
      (aeval_mem y hy S c hc)) ∈ torusS K (fun k => (ht k).unit) S := by
  letI := (strV q V).toAlgebra
  have hdeg : ∀ α ∈ c.support, ∑ k, α k = j * S.card := fun α hα => by
    have h := hc (MvPolynomial.mem_support_iff.1 hα)
    rw [← h]
    simp [Finsupp.weight_apply, Finsupp.sum_fintype]
  have hmono : ∀ α ∈ c.support, ∏ k, y k ^ α k ∈ grK K N (j • (S.card * e)) := fun α hα => by
    have := mono_mem y hy (fun k => α k) (hdeg α hα)
    rwa [smul_eq_mul, mul_assoc, ← smul_eq_mul] at this
  have hC : ∀ r : K, MvPolynomial.C r ∈ grK K N (0 • (S.card * e)) := fun r => by
    simpa using MvPolynomial.isHomogeneous_C (Fin (N + 1)) r
  have hCm : ∀ (r : K) (u : MvPolynomial (Fin (N + 1)) K), u ∈ grK K N (j • (S.card * e)) →
      MvPolynomial.C r * u ∈ grK K N (j • (S.card * e)) := fun r u hu => by
    rw [MvPolynomial.C_mul']
    exact Submodule.smul_mem _ r hu
  have key : ∀ s : Finset (Fin (d + 1) →₀ ℕ), s ⊆ c.support → ∀ h,
      evV i (yS y S) V hS (HomogeneousLocalization.Away.mk (grK K N) (yS_mem y hy S) j
        (∑ α ∈ s, MvPolynomial.C (AddMonoidAlgebra.coeff c α) * ∏ k, y k ^ α k) h) ∈
        torusS K (fun k => (ht k).unit) S := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _ h
      simp only [Finset.sum_empty]
      rw [mk_zero', map_zero]
      exact zero_mem _
    | insert a s ha ih =>
      intro hs h
      have hs' : s ⊆ c.support := (Finset.subset_insert a s).trans hs
      have hA : a ∈ c.support := hs (Finset.mem_insert_self a s)
      have hrest : ∑ α ∈ s, MvPolynomial.C (AddMonoidAlgebra.coeff c α) * ∏ k, y k ^ α k ∈ grK K N (j • (S.card * e)) :=
        Submodule.sum_mem _ fun α hα => hCm _ _ (hmono α (hs' hα))
      simp only [Finset.sum_insert ha]
      rw [mk_add' _ (hCm _ _ (hmono a hA)) hrest, map_add (f := _)]
      refine add_mem ?_ (ih hs' hrest)
      rw [mk_C_mul _ _ (hC _) (hmono a hA), map_mul, evV_const i q hq]
      refine mul_mem ?_ ?_
      · exact Subalgebra.algebraMap_mem _ _
      · rw [evV_monomial i y hy hV S hS ht (fun k => a k) (hdeg a hA)]
        exact Algebra.subset_adjoin ⟨_, mem_expS S j _ (hdeg a hA), rfl⟩
  have hsum : MvPolynomial.aeval y c = ∑ α ∈ c.support, MvPolynomial.C (AddMonoidAlgebra.coeff c α) * ∏ k, y k ^ α k := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    rfl
  have gen : ∀ (p : MvPolynomial (Fin (N + 1)) K) (hp : p ∈ grK K N (j • (S.card * e))), MvPolynomial.aeval y c = p →
      evV i (yS y S) V hS (HomogeneousLocalization.Away.mk (grK K N) (yS_mem y hy S) j p hp) ∈
        torusS K (fun k => (ht k).unit) S →
      evV i (yS y S) V hS (HomogeneousLocalization.Away.mk (grK K N) (yS_mem y hy S) j (MvPolynomial.aeval y c)
        (aeval_mem y hy S c hc)) ∈ torusS K (fun k => (ht k).unit) S := by
    rintro _ _ rfl h
    exact h
  have hp := hsum ▸ aeval_mem y hy S c hc
  exact gen _ hp hsum (key _ subset_rfl hp)

end GlobalTheory.CompanionTheory.GeoTorus
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherNormalizationFinite
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoInteg

theorem away_val_mk {K : Type} [Field K] {N : ℕ} {g : MvPolynomial (Fin (N + 1)) K} {D : ℕ}
    (hg : g ∈ grK K N D) (n : ℕ) (x : MvPolynomial (Fin (N + 1)) K) (hx : x ∈ grK K N (n • D)) :
    (HomogeneousLocalization.Away.mk (grK K N) hg n x hx).val =
      algebraMap _ (Localization.Away g) x * (IsLocalization.Away.invSelf g : Localization.Away g) ^ n := by
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  rw [IsLocalization.mk'_eq_iff_eq_mul]
  have h : algebraMap _ (Localization.Away g) g * IsLocalization.Away.invSelf g = 1 :=
    IsLocalization.Away.mul_invSelf g
  simp only [map_pow]
  rw [mul_assoc, ← mul_pow, mul_comm _ (algebraMap _ _ g), h, one_pow, mul_one]

theorem away_relation {K : Type} [Field K] {N : ℕ} {g : MvPolynomial (Fin (N + 1)) K} {D : ℕ}
    (hg : g ∈ grK K N D) (r s : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (r • D))
    (c : ℕ → MvPolynomial (Fin (N + 1)) K) (hc : ∀ l, c l ∈ grK K N (((s - l) * r) • D))
    (F : MvPolynomial (Fin (N + 1)) K) (hF : F ∈ grK K N ((s * r) • D))
    (hFe : F = f ^ s + ∑ l ∈ Finset.range s, c l * f ^ l) :
    HomogeneousLocalization.Away.mk (grK K N) hg r f hf ^ s +
      ∑ l ∈ Finset.range s, HomogeneousLocalization.Away.mk (grK K N) hg _ (c l) (hc l) *
        HomogeneousLocalization.Away.mk (grK K N) hg r f hf ^ l =
      HomogeneousLocalization.Away.mk (grK K N) hg _ F hF := by
  have val_sum : ∀ (t : Finset ℕ) (u : ℕ → HomogeneousLocalization.Away (grK K N) g),
      (∑ l ∈ t, u l).val = ∑ l ∈ t, (u l).val := fun t u =>
    map_sum (algebraMap (HomogeneousLocalization.Away (grK K N) g) (Localization.Away g)) u t
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_add, HomogeneousLocalization.val_pow,
    HomogeneousLocalization.val_mul, val_sum, away_val_mk]
  rw [hFe]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_mul, map_pow, add_mul, Finset.sum_mul]
  congr 1
  · rw [mul_pow, ← pow_mul, mul_comm s r]
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ s := (Finset.mem_range.1 hl).le
    have : s * r = (s - l) * r + r * l := by
      obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hl'
      simp only [Nat.add_sub_cancel_left]
      ring
    rw [this, pow_add, mul_pow, ← pow_mul]
    ring

theorem rel_mem {K : Type} [Field K] {N : ℕ} {D : ℕ} (r s : ℕ) (f : MvPolynomial (Fin (N + 1)) K)
    (hf : f ∈ grK K N (r • D)) (c : ℕ → MvPolynomial (Fin (N + 1)) K)
    (hc : ∀ l, c l ∈ grK K N (((s - l) * r) • D)) :
    f ^ s + ∑ l ∈ Finset.range s, c l * f ^ l ∈ grK K N ((s * r) • D) := by
  have hf' : f.IsHomogeneous (r • D) := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hf
  refine add_mem ?_ (sum_mem fun l hl => ?_)
  · rw [MvPolynomial.mem_homogeneousSubmodule]
    convert hf'.pow s using 1
    simp only [smul_eq_mul]
    ring
  · have hl' : l ≤ s := (Finset.mem_range.1 hl).le
    rw [MvPolynomial.mem_homogeneousSubmodule]
    convert ((MvPolynomial.mem_homogeneousSubmodule _ _).1 (hc l)).mul (hf'.pow l) using 1
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hl'
    simp only [Nat.add_sub_cancel_left, smul_eq_mul]
    ring

theorem isIntegral_torusS : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), 0 < e → ∀ (q : X ⟶ Spec (CommRingCat.of K)), i ≫ PSpace.str K N = q → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k))) (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) → ∀ (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S)) (ht : ∀ k, IsUnit (tV i y hy V hV k)), letI := (strV q V).toAlgebra; ∀ a, IsIntegral (torusS K (fun k => (ht k).unit) S) (evV i (yS y S) V hS a) := by
  intro K _ X N d e i y hy V hV he q hq hfin S hS ht
  letI := (strV q V).toAlgebra
  intro a
  have hg := yS_mem y hy S
  obtain ⟨r, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (grK K N) hg a
  by_cases hS0 : S.card = 0
  ·
    have hf0 : f.IsHomogeneous 0 := by
      have := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hf
      simpa [hS0] using this
    have hfC : f = MvPolynomial.C (AddMonoidAlgebra.coeff f 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hf0.totalDegree_le)
    have hc : (MvPolynomial.C (AddMonoidAlgebra.coeff f 0) : MvPolynomial (Fin (d + 1)) K).IsHomogeneous (r * S.card) := by
      rw [hS0, Nat.mul_zero]
      exact MvPolynomial.isHomogeneous_C _ _
    have hmem := GlobalTheory.CompanionTheory.GeoTorus.aeval_mem_torusS i y hy hV he q hq S hS ht _ hc
    have hfe : MvPolynomial.aeval y (MvPolynomial.C (AddMonoidAlgebra.coeff f 0) : MvPolynomial (Fin (d + 1)) K) = f := by
      rw [MvPolynomial.aeval_C]
      exact hfC.symm
    have heq : HomogeneousLocalization.Away.mk (grK K N) hg r (MvPolynomial.aeval y (MvPolynomial.C (AddMonoidAlgebra.coeff f 0) : MvPolynomial (Fin (d + 1)) K)) (aeval_mem y hy S _ hc) = HomogeneousLocalization.Away.mk (grK K N) hg r f hf := by
      simp only [hfe]
    rw [heq] at hmem
    exact isIntegral_algebraMap (R := torusS K (fun k => (ht k).unit) S) (x := ⟨_, hmem⟩)
  · have hD : 0 < S.card * e := Nat.mul_pos (Nat.pos_of_ne_zero hS0) he
    have hfh : f.IsHomogeneous (e * (r * S.card)) := by
      have := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hf
      convert this using 1
      simp only [smul_eq_mul]
      ring
    obtain ⟨s, c, -, hc, hrel⟩ := GlobalTheory.CompanionTheory.Geo.exists_hom_relation (homIdeal i) (GlobalTheory.CompanionTheory.Geo.homIdeal_homog i) e he y hy hfin (r * S.card) f hfh
    have hc' : ∀ l, (c l).IsHomogeneous (((s - l) * r) * S.card) := fun l => by
      rw [mul_assoc]
      exact hc l
    have hcm := fun l => aeval_mem y hy S (c l) (hc' l)
    have hF := rel_mem r s f hf (fun l => MvPolynomial.aeval y (c l)) hcm
    have hid := away_relation hg r s f hf (fun l => MvPolynomial.aeval y (c l)) hcm _ hF rfl
    have hzero := GlobalTheory.CompanionTheory.GeoVanish.homIdeal_vanish i hD hg hF hrel V hS
    rw [← hid] at hzero
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum] at hzero
    simp only [map_mul, map_pow] at hzero
    have hco := fun l => GlobalTheory.CompanionTheory.GeoTorus.aeval_mem_torusS i y hy hV he q hq S hS ht (c l) (hc' l)
    refine ⟨Polynomial.X ^ s + ∑ l ∈ Finset.range s,
      Polynomial.C (⟨_, hco l⟩ : torusS K (fun k => (ht k).unit) S) * Polynomial.X ^ l, ?_, ?_⟩
    · refine Polynomial.monic_X_pow_add ?_
      rw [← Polynomial.mem_degreeLT]
      refine Submodule.sum_mem _ fun l hl => ?_
      rw [Polynomial.mem_degreeLT]
      refine (Polynomial.degree_C_mul_X_pow_le l _).trans_lt ?_
      exact_mod_cast Finset.mem_range.1 hl
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C]
      exact hzero

end GlobalTheory.CompanionTheory.GeoInteg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherNormalizationFiniteStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noether_normalization_finite : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), 0 < e → ∀ (q : X ⟶ Spec (CommRingCat.of K)), i ≫ PSpace.str K N = q → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k))) (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) → ∀ (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S)) (ht : ∀ k, IsUnit (tV i y hy V hV k)), letI := (strV q V).toAlgebra; ∀ a, IsIntegral (torusS K (fun k => (ht k).unit) S) (evV i (yS y S) V hS a) := by
  first | exact @GlobalTheory.CompanionTheory.GeoInteg.isIntegral_torusS | exact GlobalTheory.CompanionTheory.GeoInteg.isIntegral_torusS | (intros; apply GlobalTheory.CompanionTheory.GeoInteg.isIntegral_torusS <;> assumption)
end

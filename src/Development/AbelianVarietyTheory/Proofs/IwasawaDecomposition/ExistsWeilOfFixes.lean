module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticPowOfRestrictsToQuadraticSig
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueBarCompatibility
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryInfinitePointEqListProdPlaceParts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilOfFixes
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilOfFixes
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilSurj

open GlobalTheory.WeilRestrict Polynomial

theorem card_le_of_forall_pow_eq {F : Type*} [Field F] [Finite F] {m : ℕ} (hm : 1 < m)
    (h : ∀ x : F, x ^ m = x) : Nat.card F ≤ m := by
  classical
  haveI := Fintype.ofFinite F
  have hdeg : (X : F[X]).natDegree < (X ^ m : F[X]).natDegree := by
    rw [natDegree_X, natDegree_X_pow]; exact hm
  have hp : (X ^ m - X : F[X]) ≠ 0 := by
    intro h0
    have := congrArg natDegree h0
    rw [natDegree_sub_eq_left_of_natDegree_lt hdeg, natDegree_X_pow, natDegree_zero] at this
    omega
  have hsub : (Finset.univ : Finset F) ⊆ (X ^ m - X : F[X]).roots.toFinset := by
    intro x _
    rw [Multiset.mem_toFinset, mem_roots hp, IsRoot.def]
    simp [h x]
  calc Nat.card F = (Finset.univ : Finset F).card := by rw [Nat.card_eq_fintype_card, Finset.card_univ]
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Multiset.toFinset_card_le _
    _ ≤ _ := card_roots' _
    _ = m := by rw [natDegree_sub_eq_left_of_natDegree_lt hdeg, natDegree_X_pow]

theorem exists_weil_of_fixes : ∀ (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra E K] [IsScalarTower E K Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A w) (h' : IsPlaceOver A W) (σ : Weil h), (∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x) → ∃ τ : Weil h', ∀ z : Ω, (σ : G E Ω) z = (τ : G K Ω) z := by
  intro E K Ω _ _ _ _ _ _ _ _ _ _ _ A w W h h' σ hσ
  obtain ⟨f, hf⟩ := normV_eq_pow_of_isPlaceOver h h'
  have hq1 : 1 < normV w := one_lt_normV w
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · have := one_lt_normV W
      rw [hf, h0, pow_zero] at this
      exact absurd this (lt_irrefl 1)
    · exact h0
  have hφdeg : deg (resWeil h h' (frob h')) = f := by
    have h1 : ActsAs A (normV w ^ f) (frob h' : G K Ω) 1 0 := by
      rw [← hf]; exact actsAs_one_iff.mpr isFrob_frob
    have h2 := actsAs_resG (K := E) h1
    have := deg_eq (σ := resWeil h h' (frob h')) h2
    simpa using this
  obtain ⟨k, r, hr0, hrf, hdr⟩ : ∃ k r : ℤ, 0 ≤ r ∧ r < f ∧ r + f * k = deg σ :=
    ⟨deg σ / f, deg σ % f, Int.emod_nonneg _ (by exact_mod_cast hf0.ne'),
      Int.emod_lt_of_pos _ (by exact_mod_cast hf0), Int.emod_add_mul_ediv _ _⟩
  set σ' : Weil h := σ * (resWeil h h' (frob h' ^ k))⁻¹ with hσ'
  have hdeg' : deg σ' = r := by
    rw [hσ', deg_mul, deg_inv, map_zpow, deg_zpow, hφdeg]
    linear_combination -hdr
  have hfix' : ∀ x : K, (σ' : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x := by
    intro x
    rw [hσ', Subgroup.coe_mul, AlgEquiv.mul_apply, ← map_inv, resWeil_apply, AlgEquiv.commutes, hσ]
  have hr : r = 0 := by
    by_contra hne
    have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hne)
    set n := r.toNat with hn'
    have hn : (n : ℤ) = r := Int.toNat_of_nonneg hr0
    have hact := actsAs_of_deg (σ := σ') (a := n) (b := 0) (by rw [hdeg', hn]; simp)
    have hmem : ∀ x : 𝓞 K, x ^ (normV w ^ n) - x ∈ W.asIdeal := by
      intro x
      rw [← h' _]
      have hx : A.valuation (algebraMap K Ω x) ≤ 1 :=
        (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (map_isIntegral_int (algebraMap K Ω) x.isIntegral_coe))
      have := hact.2 _ hx
      rw [hfix', pow_zero, pow_one, Valuation.map_sub_swap] at this
      have e : algebraMap K Ω ((x ^ (normV w ^ n) - x : 𝓞 K) : K) =
          (algebraMap K Ω x) ^ (normV w ^ n) - algebraMap K Ω x := by simp
      rw [e]; exact this
    haveI : W.asIdeal.IsMaximal := W.isMaximal
    letI : Field (𝓞 K ⧸ W.asIdeal) := Ideal.Quotient.field _
    haveI : Finite (𝓞 K ⧸ W.asIdeal) := W.asIdeal.finiteQuotientOfFreeOfNeBot W.ne_bot
    have hall : ∀ y : 𝓞 K ⧸ W.asIdeal, y ^ (normV w ^ n) = y := by
      intro y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hmem x
    have hn0 : n ≠ 0 := by omega
    have hcard := card_le_of_forall_pow_eq (one_lt_pow₀ hq1 hn0) hall
    have hQ : Nat.card (𝓞 K ⧸ W.asIdeal) = normV w ^ f := hf
    rw [hQ] at hcard
    have : normV w ^ n < normV w ^ f := Nat.pow_lt_pow_right hq1 (by omega)
    omega
  have hine : (σ' : G E Ω) ∈ Ine (F := E) A := deg_eq_zero_iff.mp (by rw [hdeg', hr])
  let τ0 : G K Ω := { (σ' : G E Ω).toRingEquiv with commutes' := fun x => hfix' x }
  have hτ0 : τ0 ∈ Ine (F := K) A := hine
  refine ⟨ineIncl h' ⟨τ0, hτ0⟩ * frob h' ^ k, fun z => ?_⟩
  have key : (((resWeil h h' (frob h' ^ k))⁻¹ : Weil h) : G E Ω)
      (((frob h' ^ k : Weil h') : G K Ω) z) = z := by
    rw [← map_inv, resWeil_apply, ← AlgEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, AlgEquiv.one_apply]
  show (σ : G E Ω) z = (σ' : G E Ω) (((frob h' ^ k : Weil h') : G K Ω) z)
  rw [hσ', Subgroup.coe_mul, AlgEquiv.mul_apply, key]

end GlobalTheory.WeilSurj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilOfFixesStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weil_of_fixes' : ∀ (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra E K] [IsScalarTower E K Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A w) (h' : IsPlaceOver A W) (σ : Weil h), (∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x) → ∃ τ : Weil h', ∀ z : Ω, (σ : G E Ω) z = (τ : G K Ω) z := by
  first | exact @GlobalTheory.WeilSurj.exists_weil_of_fixes | exact GlobalTheory.WeilSurj.exists_weil_of_fixes | (intros; apply GlobalTheory.WeilSurj.exists_weil_of_fixes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeMarkingAdmissible
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

theorem mulVec_congr {A : Type} [CommRing A] {n N : ℕ} (P Q : Matrix (Fin n) (Fin n) A) {x y w : Fin n → A}
    (e : x - Q *ᵥ y = N • w) : P *ᵥ x - (P * Q) *ᵥ y = N • P *ᵥ w := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, e, Matrix.mulVec_smul]

theorem latW_rfl {D : D7} {W : HSp D} (L : Lt D.host.E W.rank) : latW (T := W) rfl L = L := rfl

section

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {W : HSp D}
  {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)} {h : GA D W}

theorem markAd_rfl (l : Level H) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) :
    MarkAd (T := W) rfl l ι h mk ↔ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat W h,
      finVec W (mk a) - (finHom W h).1 *ᵥ (finVec W (ι a)) = l.M • w := Iff.rfl

theorem finVec_add' (a b : Fin W.rank → D.host.E) : finVec W (a + b) = finVec W a + finVec W b :=
  GlobalTheory.AdLat.cap_fv_add D.host.F a b

theorem finVec_nsmul' (n : ℕ) (a : Fin W.rank → D.host.E) : finVec W (n • a) = n • finVec W a :=
  GlobalTheory.AdLat.cap_fv_nsmul D.host.F n a

theorem finVec_sub' (a b : Fin W.rank → D.host.E) : finVec W (a - b) = finVec W a - finVec W b :=
  funext fun _ => TensorProduct.tmul_sub _ _ _

theorem markOver_of_markAd {l l₂ : Level H} (hM : l.M ∣ l₂.M) (hI : Mfr l₂ ≤ Mfr l)
    {mk mk₂ : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)} (h1 : MarkAd (T := W) rfl l ι h mk)
    (h2 : MarkAd (T := W) rfl l₂ ι h mk₂) : MarkOver l l₂ (latG W h) mk mk₂ := by
  intro a ha
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  obtain ⟨c, hc⟩ := hM
  obtain ⟨w, hw, e⟩ := (markAd_rfl l mk).1 h1 a (Submodule.smul_mono_left hI ha)
  obtain ⟨w', hw', e'⟩ := (markAd_rfl l₂ mk₂).1 h2 a ha
  obtain ⟨u, hu, eu⟩ := GlobalTheory.MarkCoset.finVec_div W l.M hM0 (mk₂ a - mk a) (c • w' - w)
    ((finVec_sub' _ _).trans (GlobalTheory.AdMark.sub_congr hc e e'))
  refine ⟨u, ((GlobalTheory.MarkCoset.latG_spec D W h).1 u).2 (hu ▸ sub_mem (nsmul_mem hw' c) hw), ?_⟩
  rw [← eu]
  abel

theorem finHom_mulVec_finVec {δ : GA D W} {ga : GL (Fin W.rank) D.host.E}
    (hδ : Formalism.L2.Theta.mt W δ = (ga : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D))
    (v : Fin W.rank → D.host.E) : (finHom W δ).1 *ᵥ finVec W v = finVec W (ga.1 *ᵥ v) := by
  funext i
  have hf : ∀ i j, (finHom W δ).1 i j = (1 : Af D.host.F) ⊗ₜ ga.1 i j := fun i j => by
    have he' : (matHom W δ).1 i j = (1 : AF D.host.F) ⊗ₜ ga.1 i j := congrFun (congrFun hδ i) j
    change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom W δ).1 i j) = _
    rw [he', Algebra.TensorProduct.map_tmul, map_one]
    rfl
  simp only [Matrix.mulVec, dotProduct, hf, finVec, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one,
    TensorProduct.tmul_sum]

theorem mem_latGHat_mul (δ : GA D W) (z : Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom W δ).1 *ᵥ z ∈ latGHat W (δ * h) ↔ z ∈ latGHat W h := by
  rw [(GlobalTheory.MarkCoset.latG_spec D W h).2, (GlobalTheory.MarkCoset.latG_spec D W (δ * h)).2]
  refine exists_congr fun y => and_congr_right fun _ => ?_
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  refine ⟨fun e => ?_, fun e => by rw [e]⟩
  have := congrArg (fun v => ((finHom W δ)⁻¹).1 *ᵥ v) e
  simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Units.inv_mul_cancel_left] at this
  exact this

end

theorem markAd_laws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (W : HSp D) (r : ℕ) (hr : W.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), LatEmb W ι → ∀ (h : GA D W) (L : Lt D.host.E r), latW hr L = latG W h → ∀ l : Level H, (∃ mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a, mk a ∈ L) ∧ MarkAd hr l ι h mk) ∧ ∀ mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a, mk a ∈ L) → MarkAd hr l ι h mk → IsMark l L mk ∧ (∀ mk' : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ u ∈ L, mk' a = mk a + l.M • u) → MarkAd hr l ι h mk') ∧ (∀ l₂ : Level H, l.M ∣ l₂.M → Mfr l₂ ≤ Mfr l → ∀ mk₂ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a, mk₂ a ∈ L) → MarkAd hr l₂ ι h mk₂ → MarkOver l l₂ L mk mk₂) ∧ ∀ (δ : GA D W) (ga : GL (Fin r) D.host.E), Formalism.L2.Theta.mt W δ = ((ga : Matrix (Fin r) (Fin r) D.host.E).submatrix (Fin.cast hr) (Fin.cast hr)).map (incA D) → latW hr (mapL ga L) = latG W (δ * h) ∧ MarkAd hr l ι (δ * h) (mvMap ga mk) := by
  intro D H Dw W r hr ι hι h L hL l
  subst hr
  rw [latW_rfl] at hL
  subst hL
  obtain ⟨mk₀, hm0, ha0, -⟩ := GlobalTheory.AdMark.exists_marking D H Dw l l W _ rfl ι hι dvd_rfl le_rfl h
  rw [GlobalTheory.AdMark.latR_rfl] at hm0
  replace ha0 : MarkAd (T := W) rfl l ι h mk₀ := ha0
  refine ⟨⟨mk₀, hm0.mem, ha0⟩, fun mk hmem hmk => ⟨?_, ?_, ?_, ?_⟩⟩
  · have ho := markOver_of_markAd dvd_rfl le_rfl hmk ha0
    refine ⟨hmem, ?_, fun v hv => ?_⟩
    · rintro a ha ⟨u, hu, e⟩
      obtain ⟨u', hu', e'⟩ := ho a ha
      exact hm0.inj a ha ⟨u + u', add_mem hu hu', by rw [e', e, smul_add]⟩
    · obtain ⟨a, ha, u, hu, e⟩ := hm0.surj v hv
      obtain ⟨u', hu', e'⟩ := ho a ha
      exact ⟨a, ha, u' + u, add_mem hu' hu, by rw [e, e', smul_add, add_assoc]⟩
  · intro mk' hc
    refine (markAd_rfl l mk').2 fun a ha => ?_
    obtain ⟨u, hu, e⟩ := hc a ha
    obtain ⟨w, hw, e'⟩ := (markAd_rfl l mk).1 hmk a ha
    refine ⟨w + finVec W u, add_mem hw (((GlobalTheory.MarkCoset.latG_spec D W h).1 u).1 hu), ?_⟩
    rw [e, finVec_add', finVec_nsmul', smul_add, ← e']
    abel
  · intro l₂ hM hI mk₂ _ h2
    exact markOver_of_markAd hM hI hmk h2
  · intro δ ga hδ
    have hf := finHom_mulVec_finVec (δ := δ) (ga := ga) hδ
    constructor
    · rw [latW_rfl]
      ext v
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ((GlobalTheory.MarkCoset.latG_spec D W (δ * h)).1 _).2 ?_
        change finVec W (ga.1 *ᵥ x) ∈ _
        rw [← hf, mem_latGHat_mul]
        exact ((GlobalTheory.MarkCoset.latG_spec D W h).1 _).1 hx
      · intro hv
        have hri : ga.1 *ᵥ ((ga⁻¹).1 *ᵥ v) = v := by
          rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
        refine ⟨(ga⁻¹).1 *ᵥ v, ((GlobalTheory.MarkCoset.latG_spec D W h).1 _).2 ?_, hri⟩
        rw [← mem_latGHat_mul δ, hf, hri]
        exact ((GlobalTheory.MarkCoset.latG_spec D W (δ * h)).1 _).1 hv
    · refine (markAd_rfl l _).2 fun a ha => ?_
      obtain ⟨w, hw, e⟩ := (markAd_rfl l mk).1 hmk a ha
      refine ⟨_, (mem_latGHat_mul δ w).2 hw, ?_⟩
      change finVec W (ga.1 *ᵥ mk a) - _ = _
      rw [← hf, map_mul, Units.val_mul]
      exact mulVec_congr _ _ e

end GlobalTheory.OneMapRef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointCarriesFrameFlagsTransferBetweenFlagBundles
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointCarriesFrameFlagsTransferBetweenFlagBundles
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle.Transfer

variable {ι : Type} {m : ι → ℕ}

theorem inv_mul_cancel_left {K : Type} [Field K] {g : Mat m K} (hg : ∀ τ, (g τ).det ≠ 0) (X : Mat m K) :
    g⁻¹ * (g * X) = X := by
  rw [← mul_assoc, Mat.inv_mul hg, one_mul]

theorem mul_inv_cancel_left {K : Type} [Field K] {g : Mat m K} (hg : ∀ τ, (g τ).det ≠ 0) (X : Mat m K) :
    g * (g⁻¹ * X) = X := by
  rw [← mul_assoc, Mat.mul_inv hg, one_mul]

theorem det_mul_ne {K : Type} [Field K] {g g' : Mat m K} (hg : ∀ τ, (g τ).det ≠ 0) (hg' : ∀ τ, (g' τ).det ≠ 0)
    (τ : ι) : ((g * g') τ).det ≠ 0 := by
  rw [Pi.mul_apply, Matrix.det_mul]; exact mul_ne_zero (hg τ) (hg' τ)

theorem par_of_three {K : Type} [Field K] {k : ι → ℕ} {h h' P Q E L : Mat m K} (hP : ∀ τ, (P τ).det ≠ 0)
    (hQ : ∀ τ, (Q τ).det ≠ 0) (hE : ∀ τ, (E τ).det ≠ 0) (hL : Par k ⊤ L) (G1 : Par k ⊤ (h * P⁻¹))
    (G2 : Par k ⊤ (h' * (L * (P * E))⁻¹)) (G3 : Par k ⊤ (h' * (Q * E)⁻¹)) : Par k ⊤ (h * Q⁻¹) := by
  have hh' : ∀ τ, (h' τ).det ≠ 0 := fun τ => by
    have := G3.det_ne τ
    rw [Pi.mul_apply, Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  have hLPE : ∀ τ, ((L * (P * E)) τ).det ≠ 0 := det_mul_ne hL.det_ne (det_mul_ne hP hE)
  have e : h * Q⁻¹ = h * P⁻¹ * L⁻¹ * (h' * (L * (P * E))⁻¹)⁻¹ * (h' * (Q * E)⁻¹) := by
    rw [Mat.mul_inv_rev h', Mat.inv_inv hLPE, Mat.mul_inv_rev Q E]
    simp only [mul_assoc]
    rw [inv_mul_cancel_left hh', mul_inv_cancel_left hE, inv_mul_cancel_left hL.det_ne,
      inv_mul_cancel_left hP]
  rw [e]
  exact ((G1.mul hL.inv).mul G2.inv).mul G3

variable {F : Type} [Field F]

theorem sp_specializes {Y : Var F} {K : Type} [Field K] (p : Sp K ⟶ Y.X) (w : Sp K) :
    p w ⤳ p (IsLocalRing.closedPoint K) := by
  rw [Subsingleton.elim w (IsLocalRing.closedPoint K)]

theorem val_map_mul {Y : Var F} {K : Type} [Field K] (p : Sp K ⟶ Y.X) {k k' : ι → ℕ} {g g' : Mat m Y.Fn}
    (hg : Par k ((ratOf Y).O (p (IsLocalRing.closedPoint K))).toSubring g)
    (hg' : Par k' ((ratOf Y).O (p (IsLocalRing.closedPoint K))).toSubring g') :
    (g * g').map ((ratOf Y).val p) = g.map ((ratOf Y).val p) * g'.map ((ratOf Y).val p) :=
  hg.map_mul_of hg' _ (RatModel.valHomOf p _ (sp_specializes p)) fun _ => rfl

theorem val_map_par {Y : Var F} {K : Type} [Field K] (p : Sp K ⟶ Y.X) {k : ι → ℕ} {g : Mat m Y.Fn}
    (hg : Par k ((ratOf Y).O (p (IsLocalRing.closedPoint K))).toSubring g) :
    Par k ⊤ (g.map ((ratOf Y).val p)) :=
  hg.map_of _ (RatModel.valHomOf p _ (sp_specializes p)) fun _ => rfl

theorem frame_change {X Y : Var F} (ψ : X.Fn →ₐ[F] Y.Fn) (A B : Mat m X.Fn) (hA : ∀ τ, (A τ).det ≠ 0)
    : ∀ C : Mat m Y.Fn, C * (B.map ψ)⁻¹ = (C * (A.map ψ)⁻¹) * (A * B⁻¹).map ψ := by
  intro C
  have hA' : ∀ τ, ((A.map ψ) τ).det ≠ 0 := fun τ => by
    have e : (A.map ψ τ).det = ψ (A τ).det := Mat.det_map A ψ.toRingHom τ
    rw [e]; exact (map_ne_zero _).2 (hA τ)
  have e1 : (A * B⁻¹).map ψ = A.map ψ * B⁻¹.map ψ := Mat.map_mul A B⁻¹ ψ.toRingHom
  have e2 : B⁻¹.map ψ = (B.map ψ)⁻¹ := Mat.map_inv B ψ.toRingHom
  rw [e1, e2]
  show C * (B.map ψ)⁻¹ = C * (A.map ψ)⁻¹ * (A.map ψ * (B.map ψ)⁻¹)
  rw [mul_assoc, inv_mul_cancel_left hA']

theorem val_map_hom {X Y : Var F} {ψ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hf : (ratOf X).IsHom (ratOf Y) ψ f)
    {K : Type} [Field K] (p : Sp K ⟶ Y.X) {k : ι → ℕ} {D : Mat m X.Fn}
    (hD : Par k ((ratOf X).O (f (p (IsLocalRing.closedPoint K)))).toSubring D) :
    (D.map ψ).map ((ratOf Y).val p) = D.map ((ratOf X).val (p ≫ f)) := by
  funext τ
  ext i j
  exact (hf.val_comp p (IsLocalRing.closedPoint K) ((hD τ).1 i j)).symm

theorem par_map_hom {X Y : Var F} {ψ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hf : (ratOf X).IsHom (ratOf Y) ψ f)
    {z : Y.X} {k : ι → ℕ} {D : Mat m X.Fn} (hD : Par k ((ratOf X).O (f z)).toSubring D) :
    Par k ((ratOf Y).O z).toSubring (D.map ψ) :=
  hD.map ψ.toRingHom fun _ hx => hf.map_mem_O hx

end GlobalTheory.FlagBundle.Transfer

namespace GlobalTheory.FlagBundle

open Transfer

theorem Bears.transfer : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F)
    (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X)
    (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ →
    ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (q : Sp K ⟶ Y₂.X), p ≫ f₁ = q ≫ f₂ →
    ∀ A ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)), ∀ B ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)),
    ∀ h h' : Mat m K, Bears S₁ φ₁ A h p → Bears S₁ φ₁ B h' p → Bears S₂ φ₂ B h' q → Bears S₂ φ₂ A h q := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ R₁ R₂ K _ p q hpq A hA B hB h h' b1 b2 b3
  obtain ⟨A₁, hA₁, G1⟩ := b1
  obtain ⟨A₁', hA₁', G2⟩ := b2
  obtain ⟨A₂, hA₂, G3⟩ := b3
  refine ⟨A₂, hA₂, ?_⟩
  have hx1 : f₁ (p (IsLocalRing.closedPoint K)) = (p ≫ f₁) (IsLocalRing.closedPoint K) := rfl
  have hx2 : f₂ (q (IsLocalRing.closedPoint K)) = (p ≫ f₁) (IsLocalRing.closedPoint K) := by rw [hpq]; rfl
  have hD : Par 0 ((ratOf X).O ((p ≫ f₁) (IsLocalRing.closedPoint K))).toSubring (A * B⁻¹) := (Fr.mem_iff hB).1 hA
  have hD1 : Par 0 ((ratOf X).O (f₁ (p (IsLocalRing.closedPoint K)))).toSubring (A * B⁻¹) := hx1 ▸ hD
  have hD2 : Par 0 ((ratOf X).O (f₂ (q (IsLocalRing.closedPoint K)))).toSubring (A * B⁻¹) := hx2 ▸ hD
  have C1 := R₁.2.1 _ A₁ hA₁ A (hx1 ▸ hA)
  have C1B := R₁.2.1 _ A₁ hA₁ B (hx1 ▸ hB)
  have C2 := R₂.2.1 _ A₂ hA₂ A (hx2 ▸ hA)
  have L1 := (Fr.mem_iff hA₁).1 hA₁'
  have e1 : A₁' * (B.map φ₁)⁻¹ = (A₁' * A₁⁻¹) * (A₁ * (B.map φ₁)⁻¹) := by
    rw [mul_assoc, inv_mul_cancel_left (Fr.det_ne hA₁)]
  have hAd : ∀ τ, (A τ).det ≠ 0 := Fr.det_ne hA
  rw [e1, val_map_mul p L1 C1B, frame_change φ₁ A B hAd, val_map_mul p C1 (par_map_hom R₁.1 hD1),
    val_map_hom R₁.1 p hD1] at G2
  rw [frame_change φ₂ A B hAd, val_map_mul q C2 (par_map_hom R₂.1 hD2), val_map_hom R₂.1 q hD2] at G3
  have ev : (A * B⁻¹).map ((ratOf X).val (q ≫ f₂)) = (A * B⁻¹).map ((ratOf X).val (p ≫ f₁)) :=
    congrArg (fun y => (A * B⁻¹).map ((ratOf X).val y)) hpq.symm
  rw [ev] at G3
  have hE : Par 0 ⊤ ((A * B⁻¹).map ((ratOf X).val (p ≫ f₁))) := by
    rw [← val_map_hom R₁.1 p hD1]; exact val_map_par p (par_map_hom R₁.1 hD1)
  exact par_of_three (val_map_par p C1).det_ne (val_map_par q C2).det_ne hE.det_ne (val_map_par p L1) G1 G2 G3

end GlobalTheory.FlagBundle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointCarriesFrameFlagsTransferBetweenFlagBundlesStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointCarriesFrameFlags_transfer_between_flag_bundles : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (q : Sp K ⟶ Y₂.X), p ≫ f₁ = q ≫ f₂ → ∀ A ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)), ∀ B ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)), ∀ h h' : Mat m K, Bears S₁ φ₁ A h p → Bears S₁ φ₁ B h' p → Bears S₂ φ₂ B h' q → Bears S₂ φ₂ A h q := by
  first | exact @GlobalTheory.FlagBundle.Bears.transfer | exact GlobalTheory.FlagBundle.Bears.transfer | (intros; apply GlobalTheory.FlagBundle.Bears.transfer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormGaloisEquivariance
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DictionaryRationalElementAnalyticPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DictionaryRationalElementAnalyticPoint
namespace GlobalTheory.OneMapRef.DictPt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem isDerivAt0_comp {X : Scheme.{0}} {g g' : ℕ} {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (hol : IsHolTo Set.univ e)
    (ρ : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) {w : Fin g' → ℂ} {u : Sp (DualNumber ℂ) ⟶ X} (h : IsDerivAt0 e (ρ w) u) :
    IsDerivAt0 (fun z => e (ρ z)) w u := by
  rw [HolHom.isDerivAt0_iff] at h ⊢
  refine ⟨h.1.trans (congrArg e (map_zero ρ).symm), fun U hU f => ?_⟩
  have hU' : ⊤ ≤ e 0 ⁻¹ᵁ U := by simpa only [map_zero] using hU
  have h1 : HasFDerivAt (fun t => valAt' (e t) U f) (fderiv ℂ (fun t => valAt' (e t) U f) 0) (ρ 0) := by
    rw [map_zero]; exact ((HolHom.holAt_of_isHolTo hol (Set.mem_univ 0) U hU').2 f).hasFDerivAt
  exact (h.2 U hU' f).trans (congrArg (· w) (h1.comp 0 ρ.hasFDerivAt).fderiv).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g g' : ℕ} {ty : Fin g' → (E →+* ℂ)}

theorem isHolTo_ex (F : FamilyUnif Xo σ ty) (i : Fin F.n) {P : (F.Di i).La →+ (Fin g' → ℂ)}
    (hP : IsPeriod (F.Di i) ty P) : IsHolTo Set.univ (fun z => (F.ex i P z).left) := by
  have h := (F.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  exact HolHom.isHolTo_of_holAt isOpen_univ fun z _ =>
    (HolHom.holAt_of_isHolTo h (z := (0, z)) ⟨trivial, trivial⟩).precomp (k := fun z => (0, z)) (by fun_prop)

theorem levPt_eq (F : FamilyUnif Xo σ ty) (i : Fin F.n) {Pm : (F.Di i).La →+ (Fin g' → ℂ)}
    (hper : IsPeriod (F.Di i) ty Pm) (π : Fin g ≃ Fin g') {y : Sp ℂ ⟶ Xo.X} (h : y = F.u i Pm)
    (ex : (Fin g → ℂ) → (ptO Xo y ⟶ Xo.univ.t.G)) (u : Fin g' → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left))
    (b1 : ∀ z w, ex (z + w) = ex z * ex w) (b2 : IsHolTo Set.univ (fun z => (ex z).left))
    (b3 : ∀ m, IsDerivAt0 (fun z => (ex z).left) (Pi.single (π.symm m) 1) (u m))
    (b4 : ∀ m, IsDerivAt0 (fun z => (F.ex i Pm z).left) (Pi.single m 1) (u m))
    (a : Dw.La) (ha : a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La)) :
    levPt Xo y a = ex (fun j => (l.M : ℂ)⁻¹ * Pm (F.t i a) (π j)) := by
  subst h
  let ρ : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ) := ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (π j)
  have hρ : ∀ m, ρ (Pi.single m 1) = Pi.single (π.symm m) 1 := fun m => by
    funext j
    change (Pi.single m 1 : Fin g' → ℂ) (π j) = _
    simp only [Pi.single_apply, Equiv.eq_symm_apply]
  have E : (fun z => ex (ρ z)) = F.ex i Pm :=
    GlobalTheory.AnUniq.exp_eq (fun z w => by rw [map_add (f := _), b1]) (F.ex_add _ _ hper)
      (HolHom.isHolTo_of_holAt isOpen_univ fun z _ =>
        (HolHom.holAt_of_isHolTo b2 (Set.mem_univ (ρ z))).precomp ρ.differentiableAt) (isHolTo_ex F _ hper)
      u (fun m => isDerivAt0_comp b2 ρ (by rw [hρ]; exact b3 m)) b4
  exact (F.ex_eta i Pm hper a ha).trans (congrFun E _).symm

theorem ex_add_ker {y : Sp ℂ ⟶ Xo.X} (ex : (Fin g → ℂ) → (ptO Xo y ⟶ Xo.univ.t.G))
    (b1 : ∀ z w, ex (z + w) = ex z * ex w) (z k z' : Fin g → ℂ) (hk : ex k = 1) (h : z' = z + k) : ex z = ex z' := by
  rw [h, b1, hk, _root_.mul_one]

theorem sub_eq_nsmul {A : Type} [AddCommGroup A] (M : ℕ) (p q z w w' : A) (e : p - z = M • w)
    (e' : q - z = M • w') : p - q = M • (w - w') := by
  rw [smul_sub, ← e, ← e', sub_sub_sub_cancel_right]

end GlobalTheory.OneMapRef.DictPt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

theorem GlobalTheory.OneMapRef.DictPt.exists_sub_eq {D : D7} (V : HSp D) (g : GA D V) (M : ℕ) (hM : M ≠ 0)
    (p q : Fin V.rank → D.host.E) (z w w' : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hw : w ∈ latGHat V g) (hw' : w' ∈ latGHat V g) (e : finVec V p - z = M • w) (e' : finVec V q - z = M • w') :
    (M : D.host.E)⁻¹ • (p - q) ∈ latG V g := by
  rw [(GlobalTheory.MarkCoset.latG_spec D V g).1]
  have hM' : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have h1 : M • finVec V ((M : D.host.E)⁻¹ • (p - q)) = M • (w - w') := by
    refine Eq.trans ?_ (GlobalTheory.OneMapRef.DictPt.sub_eq_nsmul M _ _ z w w' e e')
    funext i
    change M • ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((M : D.host.E)⁻¹ * (p i - q i))) = 1 ⊗ₜ p i - 1 ⊗ₜ q i
    rw [← TensorProduct.tmul_smul, nsmul_eq_mul, mul_inv_cancel_left₀ hM', TensorProduct.tmul_sub]
  have h2 : finVec V ((M : D.host.E)⁻¹ • (p - q)) = w - w' :=
    GlobalTheory.MarkCoset.nsmul_cancel D.host.F M (Nat.cast_ne_zero.2 hM) h1
  rw [h2]
  exact sub_mem hw hw'


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.OneMapRef.DictPt.dict_point : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (W : HSp D) (r : ℕ) (hr : W.rank = r) (U : Unf Xo c σ r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (g₀ : ℕ) (e₀ : Fin g₀ ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e₀ j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (θ : InfFam D) (Z₀ : Fam W), GoodEmb c σ → IsUnf U → 1 ≤ r → IsInfFam θ → (∀ k τ, IsInfEmb τ.1 (th k τ)) → DictLat U W hr dict ι e₀ F ik φ th x₀ → (∀ ρ, x₀ (tauE D ρ) = Matrix.reindex (finCongr hr) (finCongr hr) (Z₀ ρ)) → ∀ h : GA D W, ∃ γ ∈ GQ W, MarkBy U W hr dict ι F ik φ h γ ∧ latW hr (U.X (dict h).1).Λ = latG W (γ * h) ∧ (∀ eT : D.what₂.Tau ≃ (U.X (dict h).1).Ψ, (∀ ρ, (eT ρ).1 = tauE D ρ) → (dict h).2 = frOf hr eT (mvZ θ (γ * h) Z₀)) ∧ ∀ (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X (dict h).1).Λ) (idx : Fin g ≃ (U.X (dict h).1).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl (U.X (dict h).1) bas → Matched c σ (U.X (dict h).1) idx e → letI : Algebra c.F ℂ := σ.toAlgebra; ∀ (A : AnFib (U.X (dict h).1) bas idx e (dict h).2 (U.X (dict h).1).Λ (ptC U (dict h).1 ⟨(dict h).2, hx⟩)) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), (∀ a, mk a ∈ (U.X (dict h).1).Λ) → MarkAd hr l ι (γ * h) mk → A.Marked mk := by
  intro D H Dw l Xo c σ W r hr U dict ι g₀ e₀ F ik φ th x₀ θ Z₀ hσ hU h1 hθ hth hD hx₀ h
  subst hr
  obtain ⟨γ, hγ, hl, hm, hf⟩ := hD.2 h
  have hΛ : (U.X (dict h).1).Λ = latG W (γ * h) := SetLike.ext' (hl.trans (Set.image_id _))
  refine ⟨γ, hγ, ⟨hγ, hl, hm⟩, hΛ, fun eT heT => ?_, ?_⟩
  · funext τ
    obtain ⟨ρ, rfl⟩ := eT.surjective τ
    have e1 : th _ (eT ρ) = θ ρ :=
      GlobalTheory.SmoothForms.RealPts.infEmb_unique _ _ _ (hth _ (eT ρ)) (by rw [heT]; exact hθ ρ)
    have := hf (eT ρ)
    rw [e1, heT, hx₀] at this
    funext a b
    simp only [frOf, Equiv.symm_apply_apply]
    exact congrFun (congrFun this a) b
  · intro hx g bas idx e hs hM
    letI : Algebra c.F ℂ := σ.toAlgebra
    intro A mk hmk hA a ha
    obtain ⟨Pm, hPm, hP, hu, hder⟩ := hD.1.2 (dict h).1 ⟨(dict h).2, hx⟩
    have hM0 : l.M ≠ 0 := by have := l.three_le; omega
    have key := GlobalTheory.OneMapRef.DictPt.levPt_eq F _ hP (e.trans e₀.symm) hu A.ex (fun m => (U.un _ ⟨(dict h).2, hx⟩).u (e₀ m).1 (e₀ m).2)
      A.ex_add A.hol (fun m => A.der (e₀ m)) (fun m => by simpa only [Sigma.eta, Equiv.symm_apply_apply] using hder (e₀ m).1 (e₀ m).2) a ha
    obtain ⟨w, hw, ew⟩ := hA a ha
    obtain ⟨w', hw', ew'⟩ := hm a ha
    have hmem := GlobalTheory.OneMapRef.DictPt.exists_sub_eq W (γ * h) l.M hM0 _ _ _ w w' hw hw' ew ew'
    rw [← hΛ] at hmem
    have hk := (A.ex_ker _).2 ⟨_, hmem, rfl⟩
    refine key.trans (GlobalTheory.OneMapRef.DictPt.ex_add_ker A.ex A.ex_add _ _ _ hk ?_)
    funext j
    have e3 : ∀ v (ℓ ℓ' : Lt1 Dw), ℓ = ℓ' → perFr (U.X (dict h).1) (dict h).2 v (relab c σ ℓ.1) ℓ.2 =
        perFr (U.X (dict h).1) (dict h).2 v (relab c σ ℓ'.1) ℓ'.2 := fun v ℓ ℓ' hℓ => by rw [hℓ]
    rw [Pi.add_apply, hPm, Equiv.trans_apply, e3 _ _ _ (e₀.apply_symm_apply (e j)), ← hM.1]
    have e2 : ∀ p q : Fin W.rank → D.host.E, (l.M : D.host.E)⁻¹ • p =
        (l.M : D.host.E)⁻¹ • q + (l.M : D.host.E)⁻¹ • (p - q) := fun p q => by rw [← smul_add, add_sub_cancel]
    rw [e2 (mk a) (φ _ (F.t _ a))]
    simp only [pv, Function.comp_apply, per_add, Pi.add_apply]
    congr 1
    rw [per_smul, map_inv₀, map_natCast]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DictionaryRationalElementAnalyticPointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictionary_rational_element_analytic_point : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (W : HSp D) (r : ℕ) (hr : W.rank = r) (U : Unf Xo c σ r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (g₀ : ℕ) (e₀ : Fin g₀ ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e₀ j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (θ : InfFam D) (Z₀ : Fam W), GoodEmb c σ → IsUnf U → 1 ≤ r → IsInfFam θ → (∀ k τ, IsInfEmb τ.1 (th k τ)) → DictLat U W hr dict ι e₀ F ik φ th x₀ → (∀ ρ, x₀ (tauE D ρ) = Matrix.reindex (finCongr hr) (finCongr hr) (Z₀ ρ)) → ∀ h : GA D W, ∃ γ ∈ GQ W, MarkBy U W hr dict ι F ik φ h γ ∧ latW hr (U.X (dict h).1).Λ = latG W (γ * h) ∧ (∀ eT : D.what₂.Tau ≃ (U.X (dict h).1).Ψ, (∀ ρ, (eT ρ).1 = tauE D ρ) → (dict h).2 = frOf hr eT (mvZ θ (γ * h) Z₀)) ∧ ∀ (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X (dict h).1).Λ) (idx : Fin g ≃ (U.X (dict h).1).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl (U.X (dict h).1) bas → Matched c σ (U.X (dict h).1) idx e → letI : Algebra c.F ℂ := σ.toAlgebra; ∀ (A : AnFib (U.X (dict h).1) bas idx e (dict h).2 (U.X (dict h).1).Λ (ptC U (dict h).1 ⟨(dict h).2, hx⟩)) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), (∀ a, mk a ∈ (U.X (dict h).1).Λ) → MarkAd hr l ι (γ * h) mk → A.Marked mk := by
  first | exact @GlobalTheory.OneMapRef.DictPt.dict_point | exact GlobalTheory.OneMapRef.DictPt.dict_point | (intros; apply GlobalTheory.OneMapRef.DictPt.dict_point <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

theorem laws_cast {D : D7} {T : CoreJ D} (L : LawsJ T) {j : ℕ} (hj : InR D j) {σ : T.Q.c.F →+* ℂ}
    (hσ : GoodEmb T.Q.c σ) {W : HSp D} (hV : T.V j σ = W) (hr : W.rank = D.R.r) :
    (∀ k, ModelW W hr ((T.U j σ).X k)) ∧
    (∀ h, (castDict hV (T.dict j σ) h).2 ∈ ((T.U j σ).X (castDict hV (T.dict j σ) h).1).dom) ∧
    (∀ h, IsUnitFr ((T.U j σ).X (castDict hV (T.dict j σ) h).1) (castDict hV (T.dict j σ) h).2) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ))
      (F : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FamilyUnif (T.Q.Xo j) (σ.comp (IntermediateField.inclusion T.Q.c.le).toRingHom)
        (fun i => relab T.Q.c σ (e i).1))
      (ik : (T.U j σ).Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((T.U j σ).X k).Λ)
      (th : ∀ k, ((T.U j σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧
        DictLat (T.U j σ) W hr (castDict hV (T.dict j σ))
          (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) e F ik φ th (T.x₀ j σ) := by
  subst hV
  obtain ⟨_, hm⟩ := L.modelW j hj σ hσ
  obtain ⟨_, _, -, hd⟩ := L.dictU j hj σ hσ
  obtain ⟨_, g, e, F, ik, φ, th, -, -, h1, h2⟩ := L.adPin j hj σ hσ
  exact ⟨hm, hd.2.2.2.1, (L.muUnit j hj σ hσ).2.2.2, g, e, F, ik, φ, th, h1, h2⟩

theorem exists_type_equiv {D : D7} (Q : Par D) (hp : Q.PinHost) (Ψ : Finset (D.host.E →+* ℂ))
    (hΨ : ∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ τ (Q.H.rt : D.host.E) = Q.H.rt0) :
    ∃ eT : D.what₂.Tau ≃ Ψ, ∀ ρ, (eT ρ).1 = tauE D ρ := by
  refine ⟨Equiv.ofBijective (fun ρ => ⟨tauE D ρ, (hΨ _).2 (hp.2.2.2 ρ)⟩) ⟨fun a b h => ?_, fun τ => ?_⟩, fun _ => rfl⟩
  · exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 (congrArg Subtype.val h)))
  · obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi Q hp τ.1 ((hΨ _).1 τ.2)
    exact ⟨t, Subtype.ext ht.symm⟩

end GlobalTheory.OneMapRef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardDvdCardGL
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
open Formalism.MainNotions Formalism.L2.Col
open scoped TensorProduct

namespace GlobalTheory.Mem.DuInt

theorem idx_eq (g k : ℕ) (hg : g.Prime) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) = StandardLattice.idxColLoc g k ∧ Nat.card (GL (Fin k) (ZMod g)) = g ^ (k * (k - 1) / 2) * n := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  have h1 : Nat.card {A : GL (Fin k) (ZMod g) // StandardLattice.IsUnitri (A : Matrix (Fin k) (Fin k) (ZMod g))} =
      Nat.card (HU (ZMod g) k) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun A => ⟨fun h => ?_, fun h => isUpperUni_of_mem_uniUT le_rfl h⟩)
    have : A ∈ uSet (ZMod g) (fun i j : Fin k => i < j) :=
      ⟨h.2, fun i j hne hij => h.1 i j (lt_of_le_of_ne (not_lt.1 hij) hne.symm)⟩
    rw [← uniUT_full_eq] at this
    exact this
  have h2 := (HU (ZMod g) k).card_mul_index
  have h3 := card_HU (ZMod g) k
  rw [Nat.card_zmod] at h3
  refine ⟨(HU (ZMod g) k).index, Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite, ?_, by rw [← h2, h3]⟩
  unfold StandardLattice.idxColLoc StandardLattice.idxLoc
  rw [h1, ← h2]
  have h4 : (0 : ℝ) < Nat.card (HU (ZMod g) k) := by exact_mod_cast Nat.card_pos
  push_cast
  field_simp

theorem dimV_nat {R : Ranks} (P : HCParam R) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) = StandardLattice.dimV fun i => ((P.u i : ℚ) : ℝ) := by
  have hk : 0 < R.k := by have := R.m_add_three_le_k; omega
  have hanti : StrictAnti P.u := by
    have key : ∀ d : ℕ, ∀ (a : ℕ) (h : a + d + 1 < R.k), P.u ⟨a + d + 1, h⟩ < P.u ⟨a, by omega⟩ := by
      intro d
      induction d with
      | zero => intro a h; exact (P.v_gt_u ⟨a, by omega⟩).trans (P.u_gt_v ⟨a, by omega⟩)
      | succ d ih =>
        intro a h
        exact ((P.v_gt_u ⟨a + d + 1, by omega⟩).trans (P.u_gt_v ⟨a + d + 1, by omega⟩)).trans (ih a (by omega))
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt (show a < b from hab)
    exact key d a hb
  choose z hz using P.u_half
  have gen : ∀ (N : ℕ) (_ : 0 < N) (u : Fin N → ℚ) (z : Fin N → ℤ), StrictAnti u → (∀ i, u i = z i + 1 / 2) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) = StandardLattice.dimV fun i => ((u i : ℚ) : ℝ) := by
    intro N hN u z hu hz
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    obtain ⟨c, hc⟩ := Matrix.superFactorial_dvd_vandermonde_det (fun i => - z i)
    have e1 : StandardLattice.vand (fun i => ((u i : ℚ) : ℝ)) = ((Matrix.vandermonde fun i => - z i).det : ℤ) := by
      rw [Matrix.det_vandermonde]
      unfold StandardLattice.vand
      push_cast
      refine Finset.prod_congr rfl fun a _ => Finset.prod_congr (by ext; simp) fun b _ => ?_
      rw [hz a, hz b]
      push_cast
      ring
    have e2 : StandardLattice.facProd (M + 1) = (M.superFactorial : ℕ) := by
      unfold StandardLattice.facProd
      rw [← Nat.prod_range_succ_factorial]
      push_cast
      rfl
    have h3 : (0 : ℝ) < (M.superFactorial : ℕ) := by
      rw [← e2]
      exact Finset.prod_pos fun i _ => by positivity
    have h4 : 0 < StandardLattice.vand (fun i => ((u i : ℚ) : ℝ)) := by
      refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
      have := hu (Finset.mem_filter.1 hb).2
      have : ((u b : ℚ) : ℝ) < u a := by exact_mod_cast this
      linarith
    have e5 : StandardLattice.dimV (fun i => ((u i : ℚ) : ℝ)) = c := by
      unfold StandardLattice.dimV
      rw [e1, e2, hc]
      push_cast
      field_simp
    have h6 : (0 : ℝ) < c := by
      rw [← e5]
      exact div_pos h4 (e2 ▸ h3)
    have h7 : 0 < c := by exact_mod_cast h6
    refine ⟨c.toNat, by omega, ?_⟩
    rw [e5]
    exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) (Int.toNat_of_nonneg h7.le)
  exact gen R.k hk P.u z hanti hz

section Lat

variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

def resHom (N : Submodule (𝓞 E) V) : autLat (E := E) N →* Module.End (𝓞 E) N where
  toFun γ := ((γ.1 : V →ₗ[E] V).restrictScalars (𝓞 E)).restrict fun _ hx => autLat_apply γ.2 hx
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

theorem finrank_red (N : Submodule (𝓞 E) V) (hN : Submodule.IsFullLattice E N) (w : Ideal (𝓞 E)) [w.IsMaximal] :
    Module.finrank (𝓞 E ⧸ w) ((𝓞 E ⧸ w) ⊗[𝓞 E] N) = Module.finrank E V := by
  have : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (self := hN.toIsLattice))
  have : Module.IsTorsionFree (𝓞 E) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 E) E V
  have : Module.Flat (𝓞 E) N := inferInstance
  have hr : Module.finrank (𝓞 E) N = Module.finrank E V := by
    have : IsLocalizedModule (nonZeroDivisors (𝓞 E)) N.subtype := by
      refine ⟨fun s => ?_, fun y => ?_, fun {a b} hab => ⟨1, by simpa using hab⟩⟩
      · have := isLocalizedModule_id (nonZeroDivisors (𝓞 E)) V E
        exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E)) (LinearMap.id : V →ₗ[𝓞 E] V) s
      · have hy : y ∈ Submodule.span E (N : Set V) := (Submodule.IsFullLattice.span_eq_top (self := hN)) ▸ Submodule.mem_top
        obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ y hy
        rw [Submodule.span_eq] at ht
        exact ⟨(⟨_, ht⟩, t), rfl⟩
    rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 E)) N.subtype le_rfl,
      IsFractionRing.finrank_right_eq (𝓞 E) E V]
  letI : Field (𝓞 E ⧸ w) := Ideal.Quotient.field _
  have h1 := Module.rankAtStalk_baseChange (R := 𝓞 E) (M := N) (S := 𝓞 E ⧸ w) ⊥
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank, hr] at h1
  exact h1

theorem card_dvd_card_GL (N : Submodule (𝓞 E) V) (hN : Submodule.IsFullLattice E N) (w : Ideal (𝓞 E)) [hw : w.IsMaximal]
    {g : ℕ} (hg : g.Prime) (hgw : (g : 𝓞 E) ∈ w) (hn : Ideal.absNorm w = g)
    (hbig : Module.finrank ℚ E * Module.finrank E V + 1 < g) (Γ : Subgroup (V ≃ₗ[E] V)) [Finite Γ] (hΓ : Γ ≤ autLat N) :
    Nat.card Γ ∣ Nat.card (GL (Fin (Module.finrank E V)) (ZMod g)) := by
  have : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (self := hN.toIsLattice))
  have : Module.IsTorsionFree (𝓞 E) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 E) E V
  letI : Field (𝓞 E ⧸ w) := Ideal.Quotient.field _
  have hc : Nat.card (𝓞 E ⧸ w) = g := by rw [← hn, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ w) := Nat.finite_of_card_ne_zero (hc ▸ hg.ne_zero)
  letI : Fintype (𝓞 E ⧸ w) := Fintype.ofFinite _
  haveI : NeZero g := ⟨hg.ne_zero⟩
  let e : ZMod g ≃+* 𝓞 E ⧸ w := ZMod.ringEquivOfPrime _ hg (by rw [← hc, Nat.card_eq_fintype_card])
  let b := Module.finBasisOfFinrankEq (𝓞 E ⧸ w) ((𝓞 E ⧸ w) ⊗[𝓞 E] N) (finrank_red N hN w)
  let φ : Module.End (𝓞 E ⧸ w) ((𝓞 E ⧸ w) ⊗[𝓞 E] N) ≃*
      Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) (ZMod g) :=
    (LinearMap.toMatrixAlgEquiv b).toMulEquiv.trans e.symm.mapMatrix.toMulEquiv
  let ρ : Γ →* Module.End (𝓞 E ⧸ w) ((𝓞 E ⧸ w) ⊗[𝓞 E] N) :=
    ((Module.End.baseChangeHom (𝓞 E) (𝓞 E ⧸ w) N : _ →* _).comp (resHom N)).comp (Subgroup.inclusion hΓ)
  refine Subgroup.card_dvd_of_injective (φ.toMonoidHom.comp ρ).toHomUnits ?_
  rw [injective_iff_map_eq_one]
  intro γ hγ
  have h1 : ρ γ = 1 := φ.injective (by rw [map_one]; exact congrArg Units.val hγ)
  refine Subtype.ext (stab0 hw.ne_top hN.fg (Submodule.IsFullLattice.span_eq_top (self := hN)) hg hgw hbig ⟨hΓ γ.2, 1, fun x hx => ?_⟩
    (Submonoid.isOfFinOrder_coe.mpr (isOfFinOrder_of_finite γ)))
  have h2 : (1 : 𝓞 E ⧸ w) ⊗ₜ[𝓞 E] (resHom N ⟨γ.1, hΓ γ.2⟩ ⟨x, hx⟩) = (1 : 𝓞 E ⧸ w) ⊗ₜ[𝓞 E] (⟨x, hx⟩ : N) :=
    LinearMap.congr_fun h1 ((1 : 𝓞 E ⧸ w) ⊗ₜ[𝓞 E] (⟨x, hx⟩ : N))
  have h3 := congrArg (TensorProduct.quotTensorEquivQuotSMul N w) h2
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul,
    Submodule.Quotient.eq] at h3
  have h4 := Submodule.mem_map_of_mem (f := N.subtype) h3
  rw [Submodule.map_smul'', Submodule.map_subtype_top] at h4
  rw [pow_one]
  exact h4

open Formalism.HermitianLatticesTheory in
theorem mass_mul_idx [StarRing E] (h : V →ₗ⋆[E] V →ₗ[E] E) (hs : h.IsSymm)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ E (h x x))
    (L : Submodule (𝓞 E) V) (hL : Submodule.IsFullLattice E L) (w : Ideal (𝓞 E)) [hw : w.IsMaximal]
    {g : ℕ} (hg : g.Prime) (hgw : (g : 𝓞 E) ∈ w) (hn : Ideal.absNorm w = g)
    (hbig : Module.finrank ℚ E * Module.finrank E V + 1 < g) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) = Formalism.HermitianLatticesTheory.mass h L * StandardLattice.idxColLoc g (Module.finrank E V) := by
  obtain ⟨⟨s, hs₀⟩, hm, hp⟩ := final_massBasic E V h hs hpos L (by infer_instance)
  obtain ⟨m, hm0, hm1, hm2⟩ := idx_eq g (Module.finrank E V) hg
  have key : ∀ M ∈ s, ((m / Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) = ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ * m := by
    intro M hM
    have hMl : Submodule.IsFullLattice E M := (hs₀.1 M hM).1
    have hfin := autFinite E V h hs hpos M (by infer_instance)
    have : Finite (Formalism.HermitianLatticesTheory.isom h ⊓ autLat M : Subgroup (V ≃ₗ[E] V)) := hfin.to_subtype
    have e : Nat.card (Formalism.ThetaLiftIndependence.autL h M) = Nat.card (Formalism.HermitianLatticesTheory.isom h ⊓ autLat M : Subgroup (V ≃ₗ[E] V)) := rfl
    have h1 := card_dvd_card_GL M hMl w hg hgw hn hbig (Formalism.HermitianLatticesTheory.isom h ⊓ autLat M) inf_le_right
    have h2 : (Nat.card (Formalism.HermitianLatticesTheory.isom h ⊓ autLat M : Subgroup (V ≃ₗ[E] V))).Coprime g := by
      rw [Nat.coprime_comm, hg.coprime_iff_not_dvd]
      intro hd
      have := prime_le_of_dvd_card _ hg hd
      omega
    rw [hm2] at h1
    have h3 := (h2.pow_right _).dvd_of_dvd_mul_left h1
    rw [e, Nat.cast_div h3 (by exact_mod_cast Nat.card_pos.ne'), div_eq_inv_mul]
  have e : ((∑ M ∈ s, m / Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) =
      Formalism.HermitianLatticesTheory.mass h L * StandardLattice.idxColLoc g (Module.finrank E V) := by
    rw [hm s hs₀, ← hm1, Finset.sum_mul, Nat.cast_sum]
    exact Finset.sum_congr rfl key
  refine ⟨_, ?_, e⟩
  have : (0 : ℝ) < Formalism.HermitianLatticesTheory.mass h L * StandardLattice.idxColLoc g (Module.finrank E V) :=
    mul_pos hp (by rw [← hm1]; exact_mod_cast hm0)
  rw [← e] at this
  exact_mod_cast this

end Lat

theorem duStarOf_nat : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (hc : Tau R → HCParam R), (∀ i, H.g i % (H.QS * H.q * H.d) = 1) → (∀ i, 2 * R.f * R.k < H.g i - 1) → ∃ n : ℕ, 0 < n ∧ (n : ℝ) = duStarOf H hc := by
  intro R H hc hmod hbig
  letI := H.cmStar
  have hg := H.g_prime 0
  have hdeg : Module.finrank ℚ H.E = 4 * R.ord := H.finrank_cmField
  have hdeg' : Module.finrank ℚ H.E = 2 * R.f := by
    rw [hdeg, show R.f = 2 * R.ord from rfl]; ring
  have hs : SplitsC H.E (H.g 0) := by
    refine splitsC_of_modEq_one R H _ hg ?_
    have := Nat.mod_modEq (H.g 0) (H.QS * H.q * H.d)
    rw [hmod 0] at this
    exact this.symm
  obtain ⟨v, hv⟩ : {v : HeightOneSpectrum (𝓞 H.E) | ((H.g 0 : ℕ) : 𝓞 H.E) ∈ v.asIdeal}.Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [show Set.ncard _ = _ from hs]; exact Module.finrank_pos.ne')
  have hn := (splitsC_main R H _ hg hs v hv).1
  haveI := v.isMaximal
  haveI := H.isCMField_hostE
  have hconj : ∀ (φ : H.E →+* ℂ) (x : H.E), φ (star x) = starRingEnd ℂ (φ x) := fun φ x =>
    IsCMField.complexEmbedding_complexConj H.E φ x
  have hsym : (StandardLattice.stdForm H.E R.k).IsSymm := by
    refine LinearMap.isSymm_def.mpr fun x y => ?_
    show starRingEnd H.E (∑ i, star (x i) * y i) = ∑ i, star (y i) * x i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, starRingEnd_apply, star_mul, star_star]
  have hpos : ∀ x : Fin R.k → H.E, x ≠ 0 → 0 < Algebra.trace ℚ H.E (StandardLattice.stdForm H.E R.k x x) := fun x hx => by
    have := hStd_trace_pos hconj x hx
    rw [hStd_apply] at this
    exact this
  have hL : Submodule.IsFullLattice H.E (StandardLattice.stdLat H.E R.k) := by
    refine { toIsLattice := Submodule.IsLattice.of_fg _ (Submodule.fg_span (Set.finite_range _)),
             span_eq_top := ?_ }
    have hb : (fun i : Fin R.k => (Pi.single i 1 : Fin R.k → H.E)) = Pi.basisFun H.E (Fin R.k) :=
      funext fun i => (Pi.basisFun_apply H.E (Fin R.k) i).symm
    rw [StandardLattice.stdLat, Submodule.span_span_of_tower, hb, Module.Basis.span_eq]
  obtain ⟨n₁, p₁, e₁⟩ := mass_mul_idx _ hsym hpos _ hL v.asIdeal hg hv hn
    (by rw [Module.finrank_fin_fun, hdeg']; have := hbig 0; omega)
  rw [Module.finrank_fin_fun] at e₁
  obtain ⟨n₂, p₂, e₂, -⟩ := idx_eq (H.g 0) R.k hg
  obtain ⟨n₃, p₃, e₃, -⟩ := idx_eq (H.g 1) R.k (H.g_prime 1)
  choose d pd ed using fun τ => dimV_nat (hc τ)
  obtain ⟨f, hf⟩ : ∃ f, R.f = f + 1 := ⟨R.f - 1, by
    have : 0 < R.f := Nat.mul_pos two_pos R.ord_pos
    omega⟩
  refine ⟨n₁ * n₂ ^ f * n₃ ^ R.f * ∏ τ, d τ, ?_, ?_⟩
  · have := Finset.prod_pos (s := Finset.univ) fun τ _ => pd τ
    positivity
  · unfold duStarOf
    push_cast
    simp only [ed]
    rw [e₁, e₂, e₃, hf]
    ring

end GlobalTheory.Mem.DuInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightRepresentationIrreducible
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

theorem Wt.isIrreducible_rep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n),
    W.rep.IsIrreducible := by
  intro E _ _ _ n W
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨Formalism.L2.Col.VV_nontrivial ℂ W, fun U hU => ?_⟩
  refine GlobalTheory.CoefIrred.vv_irreducible_unitary (InfinitePlace E) n W U fun g hg x hx => ?_
  obtain ⟨y, hy, hyg⟩ := GlobalTheory.T.exists_definiteUnitaryInfinitePoint_of_unitary_family E n g hg
  have h := hU ⟨y, hy⟩ x hx
  rw [← hyg]
  exact h

end GlobalTheory.DefU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIwasawaDecompositionUpperUnitriangularInte
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIwasawaDecompositionUpperUnitriangularInte
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SmGL

theorem exists_unipB_mul_diagT_mul_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (g : GL (Fin m) k), ∃ u ∈ unipB k (Fin m), ∃ t : Fin m → kˣ, ∃ κ ∈ KO k (Fin m), g = u * diagT k (Fin m) t * κ := by
  intro k _ _ _ _ m g
  obtain ⟨u, l, w, hw, h⟩ := GlobalTheory.SmGL.UnitInd.exists_iwasawa (points (Fin m)) g
  refine ⟨u, u.2, (leviTorus k (Fin m)).symm l, w, hw, ?_⟩
  rw [h]
  simp [diagT]

end GlobalTheory.SmGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIwasawaDecompositionUpperUnitriangularInteStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iwasawa_decomposition_upperUnitriangular_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (g : GL (Fin m) k), ∃ u ∈ unipB k (Fin m), ∃ t : Fin m → kˣ, ∃ κ ∈ KO k (Fin m), g = u * diagT k (Fin m) t * κ := by
  first | exact @GlobalTheory.SmGL.exists_unipB_mul_diagT_mul_KO | exact GlobalTheory.SmGL.exists_unipB_mul_diagT_mul_KO | (intros; apply GlobalTheory.SmGL.exists_unipB_mul_diagT_mul_KO <;> assumption)
end
end

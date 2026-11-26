module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PullbackKahlerDegree
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

section Forms
variable {k K L : Type} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

private theorem mapDR_smul' (c : K) (w : DR k K) :
    mapDR k K L (c • w) = algebraMap K L c • mapDR k K L w := by
  rw [map_smul]
  exact (algebraMap_smul L c (mapDR k K L w)).symm

private theorem mapDR_deg {q : ℕ} {w : DR k K} (hw : w ∈ ⋀[K]^q Ω[K⁄k]) :
    mapDR k K L w ∈ ⋀[L]^q Ω[L⁄k] := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hw
  induction hw using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, rfl⟩ := hz
    rw [GlobalTheory.W1.Base.mapDR_ιMulti]
    exact ExteriorAlgebra.ιMulti_range L q ⟨_, rfl⟩
  | zero => simp
  | add a c _ _ ha hc => rw [map_add]; exact add_mem ha hc
  | smul r a _ ha => rw [mapDR_smul']; exact Submodule.smul_mem _ _ ha

private theorem omB_deg {B : Subalgebra k K} {q : ℕ} {w : DR k K} (hw : w ∈ omB k K B q) :
    w ∈ ⋀[K]^q Ω[K⁄k] := by
  have h : omB k K B q ≤ (⋀[K]^q Ω[K⁄k]).restrictScalars k := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨b, -, v, -, rfl⟩
    exact Submodule.smul_mem _ _ (ExteriorAlgebra.ιMulti_range K q ⟨_, rfl⟩)
  exact h hw

end Forms

section Pr2
variable {K K' : Type} [Field K] [Field K'] [Algebra ℂ K] [Algebra ℂ K']

private theorem pullback_kahler_smul (j2 : K →ₐ[ℂ] K') (c : K) (w : DR ℂ K) :
    pr2L j2 (c • w) = j2 c • pr2L j2 w := by
  letI : Algebra K K' := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K K' := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_smul' c w

private theorem pullback_kahler_degree (j2 : K →ₐ[ℂ] K') {q : ℕ} {w : DR ℂ K} (hw : w ∈ ⋀[K]^q Ω[K⁄ℂ]) :
    pr2L j2 w ∈ ⋀[K']^q Ω[K'⁄ℂ] := by
  letI : Algebra K K' := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K K' := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_deg hw

end Pr2

private theorem exists_sum {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (P : Submodule ℂ E) (Q : Submodule ℂ E') {m : E ⊗[ℂ] E'}
    (hm : m ∈ Submodule.map₂ (TensorProduct.mk ℂ E E') P Q) :
    ∃ (n : ℕ) (w' : Fin n → E) (w : Fin n → E'), (∀ k, w' k ∈ P ∧ w k ∈ Q) ∧ m = ∑ k, w' k ⊗ₜ[ℂ] w k := by
  rw [Submodule.map₂_eq_span_image2] at hm
  induction hm using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, hp, q, hq, rfl⟩ := hz
    exact ⟨1, fun _ => p, fun _ => q, fun _ => ⟨hp, hq⟩, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, by simp⟩
  | add a c _ _ ha hc =>
    obtain ⟨n, v', v, hv, rfl⟩ := ha
    obtain ⟨n', u', u, hu, rfl⟩ := hc
    refine ⟨n + n', Fin.append v' u', Fin.append v u, fun k => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · simpa using hv i
      · simpa using hu i
    · simp [Fin.sum_univ_add]
  | smul r a _ ha =>
    obtain ⟨n, v', v, hv, rfl⟩ := ha
    refine ⟨n, fun k => r • v' k, v, fun k => ⟨P.smul_mem r (hv k).1, (hv k).2⟩, ?_⟩
    simp [Finset.smul_sum, TensorProduct.smul_tmul']

private theorem val_ring (hV : ValBasic) {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) :
    Val B e 0 0 ∧ ∀ v c v' c', Val B e v c → Val B e v' c' →
      Val B e (v + v') (c + c') ∧ Val B e (v * v') (c * c') := by
  obtain ⟨-, ⟨ev, hev⟩, h3, -⟩ := hV L B e
  refine ⟨by simpa using h3 0, ?_⟩
  intro v c v' c' h h'
  obtain ⟨hv, rfl⟩ := (hev _ _).1 h
  obtain ⟨hv', rfl⟩ := (hev _ _).1 h'
  exact ⟨(hev _ _).2 ⟨add_mem hv hv', by rw [← map_add (f := _)]; rfl⟩,
    (hev _ _).2 ⟨mul_mem hv hv', by rw [← map_mul]; rfl⟩⟩

private theorem val_sum (hV : ValBasic) {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ)
    {ι : Type} (s : Finset ι) (f : ι → L) (c : ι → ℂ) (h : ∀ i ∈ s, Val B e (f i) (c i)) :
    Val B e (∑ i ∈ s, f i) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (val_ring hV B e).1
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact ((val_ring hV B e).2 _ _ _ _ (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).1

private theorem sum_delta {ι : Type} [DecidableEq ι] (P : Finset ι) (n : ℕ) (α β : Fin n → ι → ℂ) (μ : ι → ι → ℂ)
    (hδ : ∀ S ∈ P, ∀ T ∈ P, ∑ k, α k S * β k T = if S = T then 1 else 0) :
    ∑ k, ∑ T ∈ P, ∑ S ∈ P, β k T * μ T S * α k S = ∑ S ∈ P, μ S S := by
  calc ∑ k, ∑ T ∈ P, ∑ S ∈ P, β k T * μ T S * α k S
      = ∑ T ∈ P, ∑ S ∈ P, (∑ k, α k S * β k T) * μ T S := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ T ∈ P, μ T T := by
        refine Finset.sum_congr rfl fun T hT => ?_
        rw [Finset.sum_congr rfl fun S hS => by rw [hδ S hS T hT]]
        simp [ite_mul, hT]

section Term
variable {K K' : Type} [Field K] [Field K'] [Algebra ℂ K] [Algebra ℂ K'] [Algebra K K'] [IsScalarTower ℂ K K']

private theorem gY_term {ι : Type} (j2 : K →ₐ[ℂ] K') (dK : ι → DR ℂ K) (dL : ι → DR ℂ K') (U : ι) (P : Finset ι)
    (hmap : ∀ T, mapDR ℂ K K' (dK T) = dL T) (c : ι → ι → K')
    (hc : ∀ T ∈ P, pr2L j2 (dK T) = ∑ S ∈ P, c T S • dL S) (w' w : DR ℂ K) (g b : ι → K)
    (hg : ∀ S ∈ P, w' * dK S = g S • dK U) (hb : w = ∑ T ∈ P, b T • dK T) :
    gY j2 (w' ⊗ₜ[ℂ] w) = (∑ T ∈ P, ∑ S ∈ P, j2 (b T) * c T S * algebraMap K K' (g S)) • dL U := by
  have h1 : gY j2 (w' ⊗ₜ[ℂ] w) = mapDR ℂ K K' w' * pr2L j2 w := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, hb, map_sum, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [pullback_kahler_smul, hc T hT, Finset.smul_sum, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [smul_smul, mul_smul_comm, ← hmap S, ← map_mul, hg S hS, mapDR_smul', hmap U, smul_smul]

private theorem gY_deg (j2 : K →ₐ[ℂ] K') {p q : ℕ} {w' w : DR ℂ K} (h' : w' ∈ ⋀[K]^p Ω[K⁄ℂ]) (h : w ∈ ⋀[K]^q Ω[K⁄ℂ]) :
    gY j2 (w' ⊗ₜ[ℂ] w) ∈ ⋀[K']^(p + q) Ω[K'⁄ℂ] := by
  have h1 : gY j2 (w' ⊗ₜ[ℂ] w) = mapDR ℂ K K' w' * pr2L j2 w := rfl
  rw [h1]
  have h2 : mapDR ℂ K K' w' ∈ LinearMap.range (ExteriorAlgebra.ι K' (M := Ω[K'⁄ℂ])) ^ p := mapDR_deg h'
  have h3 : pr2L j2 w ∈ LinearMap.range (ExteriorAlgebra.ι K' (M := Ω[K'⁄ℂ])) ^ q := pullback_kahler_degree j2 h
  show _ ∈ LinearMap.range (ExteriorAlgebra.ι K' (M := Ω[K'⁄ℂ])) ^ (p + q)
  rw [pow_add]
  exact Submodule.mul_mem_mul h2 h3

end Term

theorem UpperTheory.Gal.productCup_of_system.valG_of :
    IdVal → RedK → FixZ → DtPull → MinorSum → DtBasic → ValBasic → ValG := by
  intro hId hRed hFix hDt hMin hDtB hVB F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY τ hτ a ha m hm hAct
  have hm' : m ∈ Submodule.map₂ (TensorProduct.mk ℂ (DR ℂ K) (DR ℂ K)) (omB ℂ K (rB ℂ K (xv x) {0}) (d - a))
      (omB ℂ K (rB ℂ K (xv x) {0}) a) := hm
  obtain ⟨n, w', w, hww, rfl⟩ := exists_sum _ _ hm'
  have hCov : IsFinCover ℂ K' (xv x) := hY.covY
  obtain ⟨⟨τ', hτ'⟩, htop⟩ := GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms ℂ F K' d (xv x) hCov
  obtain ⟨-, -, hdt, -, -⟩ := hDtB F K' d x hCov τ' hτ'
  have hg0 : algebraMap F K' (omG x 0) ≠ 0 := by
    refine (map_ne_zero _).2 (Finset.prod_ne_zero_iff.2 fun l _ => ?_)
    exact div_ne_zero (x l).ne_zero (x 0).ne_zero
  have hdt0 : dtS K' x Finset.univ ≠ 0 := by
    rw [hdt]
    exact smul_ne_zero hg0 hCov.dlogRatioVolumeForm_ne_zero
  have hdeg : gY j2 (∑ k, w' k ⊗ₜ[ℂ] w k) ∈ ⋀[K']^d Ω[K'⁄ℂ] := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    have := gY_deg j2 (omB_deg (hww k).1) (omB_deg (hww k).2)
    rwa [Nat.sub_add_cancel ha] at this
  have hs : gY j2 (∑ k, w' k ⊗ₜ[ℂ] w k) =
      (τ' (gY j2 (∑ k, w' k ⊗ₜ[ℂ] w k)) / algebraMap F K' (omG x 0)) • dtS K' x Finset.univ := by
    rw [hdt, smul_smul, div_mul_cancel₀ _ hg0]
    exact htop τ' hτ' _ hdeg
  refine ⟨_, hs, fun e he => ?_⟩
  obtain ⟨z, hz⟩ := hFix F K K' d x j2 Fx A hY e he
  have hRK := hRed F K K' d x j2 hY.toY0
  obtain ⟨g, b, α, β, hg1, hb1, hval, hδ⟩ :=
    hId F K d x hY.covZ τ hτ hRK a ha n w' w (fun k => hww k) hAct z
  choose hmap c hc hv using hDt F K K' d x j2 Fx A hY e he
  have hP : ∀ {T : Finset (Fin d)}, T ∈ Finset.univ.powersetCard a → T.card = a :=
    fun hT => (Finset.mem_powersetCard.1 hT).2
  have hc' : ∀ T ∈ Finset.univ.powersetCard a, pr2L j2 (dtS K x T) =
      ∑ S ∈ Finset.univ.powersetCard a, c T S • dtS K' x S := by
    intro T hT
    have := hc T
    rwa [hP hT] at this
  have hsum : gY j2 (∑ k, w' k ⊗ₜ[ℂ] w k) =
      (∑ k, ∑ T ∈ Finset.univ.powersetCard a, ∑ S ∈ Finset.univ.powersetCard a,
        j2 (b k T) * c T S * algebraMap K K' (g k S)) • dtS K' x Finset.univ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl fun k _ => gY_term j2 (dtS K x) (dtS K' x) Finset.univ _ hmap c hc' (w' k) (w k) (g k) (b k)
      (fun S hS => hg1 k S (hP hS)) (hb1 k)
  rw [smul_left_injective K' hdt0 (hs.symm.trans hsum)]
  let μ : Finset (Fin d) → Finset (Fin d) → ℂ := fun T S =>
    if h : S.card = T.card then ((A e).submatrix (T.orderEmbOfFin rfl) (S.orderEmbOfFin h)).det else 0
  have hV := val_sum hVB (rB ℂ K' (xv x) {0}) e.1 Finset.univ
    (fun k => ∑ T ∈ Finset.univ.powersetCard a, ∑ S ∈ Finset.univ.powersetCard a,
      j2 (b k T) * c T S * algebraMap K K' (g k S))
    (fun k => ∑ T ∈ Finset.univ.powersetCard a, ∑ S ∈ Finset.univ.powersetCard a, β k T * μ T S * α k S)
    (fun k _ => val_sum hVB _ _ _ _ _ fun T hT => val_sum hVB _ _ _ _ _ fun S hS => by
      have hr := (val_ring hVB (rB ℂ K' (xv x) {0}) e.1).2
      have h1 := (hz _ _ (hval k T (hP hT)).2).2
      have h2 := (hz _ _ (hval k S (hP hS)).1).1
      have hcard : S.card = T.card := (hP hS).trans (hP hT).symm
      have h3 : Val (rB ℂ K' (xv x) {0}) e.1 (c T S) (μ T S) := by
        simp only [μ, dif_pos hcard]
        exact hv T S hcard
      exact (hr _ _ _ _ (hr _ _ _ _ h1 h3).2 h2).2)
  rw [sum_delta _ n α β μ fun S hS T hT => hδ S T (hP hS) (hP hT)] at hV
  rw [hMin d a (A e)]
  simpa [μ] using hV
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PYMain
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 GlobalTheory.W1.Lef UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

namespace UpperTheory.Gal.productCup_of_system

section
variable {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L] [IsScalarTower ℂ F L] {d : ℕ}

private theorem locCoch_mem_Z (x : Fin (d + 1) → Fˣ) (h : L) (hh : h ∈ rB ℂ L (xv x) Finset.univ) :
    locCoch ℂ L (xv x) h ∈ (omCx (rB ℂ L (xv x)) d).Z d := by
  have ht : ∀ j : Fin d, algebraMap F L ((x j.succ : F) / x 0) ∈ rB ℂ L (xv x) Finset.univ := fun j =>
    (integralClosure (rA ℂ (xv x) Finset.univ) L).algebraMap_mem
      ⟨(x j.succ : F) / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_univ _, j.succ, rfl⟩⟩
  have hti : ∀ j : Fin d, (algebraMap F L ((x j.succ : F) / x 0))⁻¹ ∈ rB ℂ L (xv x) Finset.univ := fun j => by
    have := (integralClosure (rA ℂ (xv x) Finset.univ) L).algebraMap_mem
      ⟨(x 0 : F) / x j.succ, Algebra.subset_adjoin ⟨j.succ, Finset.mem_univ _, 0, rfl⟩⟩
    rw [← map_inv₀, inv_div]
    exact this
  refine ⟨?_, ?_⟩
  · show _ ∈ cechC _ _
    rw [cechC, Submodule.mem_pi]
    intro s _
    by_cases hs : s = Finset.univ
    · subst hs
      rw [if_pos ⟨Finset.univ_nonempty, by simp⟩]
      have hv : locCoch ℂ L (xv x) h Finset.univ = (h * ∏ j : Fin d, (algebraMap F L ((x j.succ : F) / x 0))⁻¹) •
          ExteriorAlgebra.ιMulti L d fun j => D ℂ L (algebraMap F L ((x j.succ : F) / x 0)) := by
        rw [locCoch, if_pos rfl, vol0, mul_smul]
        congr 1
        exact (ExteriorAlgebra.ιMulti L d).toMultilinearMap.map_smul_univ _ _
      rw [hv]
      exact Submodule.subset_span ⟨_, mul_mem hh (prod_mem fun j _ => hti j), _, ht, rfl⟩
    · have : locCoch ℂ L (xv x) h s = 0 := if_neg hs
      rw [this]
      exact zero_mem _
  · refine LinearMap.mem_ker.2 ?_
    funext t
    show GlobalTheory.DI.delta _ t = 0
    unfold GlobalTheory.DI.delta
    refine Finset.sum_eq_zero fun i hi => ?_
    have : locCoch ℂ L (xv x) h (t.erase i) = 0 := if_neg fun h' => by
      have := Finset.mem_univ i
      rw [← h'] at this
      exact Finset.notMem_erase i t this
    simp [this]

private theorem pk_single (i : Fin (d + 1)) : pk ({i} : Finset (Fin (d + 1))) = i := by
  simp [pk]

end

section
variable {β κ₁ κ₂ : Type} [LinearOrder β] [LinearOrder κ₁] [LinearOrder κ₂]

private theorem map_inlE (L : Finset κ₁) : L.map (inlE : κ₁ ↪o κ₁ ⊕ₗ κ₂).toEmbedding = uni L ∅ := by
  ext t
  simp only [uni, inlE, Finset.mem_map, Finset.mem_disjSum, Finset.notMem_empty]
  simp

private theorem prod_u {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
    (n : κ₂ → ℕ × ℕ) (L : Finset κ₁) (i j : Fin (d + 1)) :
    ∏ l ∈ uni L (∅ : Finset κ₂), T.u (app n11 n) i j l = (T.X i * T.Y j) ^ L.card := by
  rw [← map_inlE, Finset.prod_map]
  have : ∀ l : κ₁, T.u (app n11 n) i j ((inlE : κ₁ ↪o κ₁ ⊕ₗ κ₂).toEmbedding l) = T.X i * T.Y j := fun l => by
    simp [Sys.u, app, n11, inlE]
  rw [Finset.prod_congr rfl fun l _ => this l, Finset.prod_const]

end

section
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → Fˣ)

private theorem valuation_power_identity {K : Type} [Field K] (e P X : K) (d : ℕ) (hX : X ≠ 0) (he : e * (-1) ^ d = 1) :
    e * ((X * X) ^ d)⁻¹ * ((-1) ^ d * (P * X ^ d)) = P / X ^ d := by
  have h1 : X ^ d ≠ 0 := pow_ne_zero _ hX
  rw [mul_pow]
  calc _ = (e * (-1) ^ d) * (P * (X ^ d * (X ^ d * X ^ d)⁻¹)) := by ring
    _ = _ := by
      rw [he, one_mul]
      field_simp

private theorem lmul_X (a : ℕ) (i : Fin (d + 1)) :
    Algebra.TensorProduct.lmul' ℂ (((sysZ K x a).X i : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = algebraMap F K (x i) := by
  simp [sysZ]

private theorem lmul_Y (a : ℕ) (i : Fin (d + 1)) :
    Algebra.TensorProduct.lmul' ℂ (((sysZ K x a).Y i : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = algebraMap F K (x i) := by
  simp [sysZ]

private theorem kap_dj (hTh : ThMu) :
    kap K x (img (dj (0 : Fin (d + 1)))) = (∏ l : Fin d, algebraMap F K (x l.succ)) * algebraMap F K (x 0) ^ d := by
  unfold kap
  rw [(hTh d (K ⊗[ℂ] K) (DR ℂ K ⊗[ℂ] DR ℂ K) (sysZ K x 0)).2.2.2]
  simp only [map_mul, map_prod, map_pow, lmul_X, lmul_Y]

private theorem omG_zero : algebraMap F K (omG x 0) =
    (∏ l : Fin d, algebraMap F K (x l.succ)) / algebraMap F K (x 0) ^ d := by
  have h0 : algebraMap F K (x 0) ≠ 0 := by simp
  rw [omG, Fin.prod_univ_succ, div_self (x 0).ne_zero, one_mul, map_prod]
  simp only [map_div₀]
  rw [Finset.prod_div_distrib]
  simp

end

theorem yMain_of :
    ValG → YBig → YCmpT → YCmpG → GMap → CRT → ThMu → KapInd → ActsLin → DtBasic → SysBasic → RYBasic → OmLoc → WdUni → YMain := by
  intro hVal hBig hCT hCG hG hCRT hTh _ hAL _ hSB hRY _ hWU F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY τ hτ a ha κ _ _ n z hz c hc hD
  classical
  obtain ⟨-, hcrt⟩ := hCRT F K' d x hY.covY
  obtain ⟨h, hh⟩ := hcrt fun e => if e ∈ Fx then locTerm (A e) a else 0
  have hoff : ∀ e : fib ℂ K' (xv x), e ∉ Fx → e.1 h = 0 := fun e he => by rw [hh, if_neg he]
  have hon : ∀ e ∈ Fx, e.1 h = locTerm (A e) a := fun e he => by rw [hh, if_pos he]
  have hsum : ∑ᶠ e : fib ℂ K' (xv x), e.1 h = ∑ e ∈ Fx, locTerm (A e) a := by
    rw [finsum_eq_sum_of_support_subset (s := Fx) _ fun e he => ?_]
    · exact Finset.sum_congr rfl hon
    · by_contra hn
      exact he (hoff e hn)
  have hloc : locCoch ℂ K' (xv x) h ∈ (omCx (rB ℂ K' (xv x)) d).Z d := by
    obtain ⟨h1, -, h3, -⟩ := hRY F K K' d x j2 hY.toY0
    refine locCoch_mem_Z x _ ?_
    have := h3 {0} Finset.univ ∅ ∅ (Finset.subset_univ _) subset_rfl
    rw [h1, h1] at this
    exact this h.2
  refine ⟨h, ?_, hloc, hsum⟩
  have hlr : ∀ {β γ : Type} [LinearOrder β] [LinearOrder γ] (b : Finset β) (L : Finset γ),
      lft (uni b L) = b ∧ rgt (uni b L) = L ∧ (uni b L).card = b.card + L.card := fun b L =>
    ⟨(hWU _ _ ℂ 0 0 b L).2.1, (hWU _ _ ℂ 0 0 b L).2.2.1, (hWU _ _ ℂ 0 0 b L).2.2.2.1⟩
  have hcardI : (img (dj (0 : Fin (d + 1)))).card = d := by simp [img]
  have hcard0 : (uni (img (dj (0 : Fin (d + 1)))) (∅ : Finset κ)).card = d := by
    rw [(hlr _ _).2.2, hcardI]; simp
  set L0 : Finset (Mi d ⊕ₗ κ) := uni (img (dj (0 : Fin (d + 1)))) ∅ with hL0
  set c0 := c (uni (uni {0} {0}) L0) with hc0

  have hcol := ((hSB d _ _ (sysZ K x a) (Mi d ⊕ₗ κ) (app n11 n) (app (sysZ K x a).mu z) ((d : ℤ) + 2)).2.1 c).1 hc.1 {0} {0}
  rw [if_pos ⟨Finset.singleton_nonempty _, Finset.singleton_nonempty _⟩] at hcol
  have h3 : c0 ∈ ((sysZ K x a).M {0} {0}).map ((sysZ K x a).act
      ((∏ l ∈ L0, (sysZ K x a).u (app n11 n) (pk {0}) (pk {0}) l : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K)) := by
    have := hcol L0 (Set.mem_univ _)
    dsimp only at this
    rw [SetLike.mem_coe, if_pos (by rw [hcard0]; simp; ring)] at this
    exact this
  rw [pk_single, hL0, prod_u, hcardI] at h3
  obtain ⟨m', hm', hm'eq⟩ := h3

  set U : (K ⊗[ℂ] K)ˣ := ((sysZ K x a).X 0 * (sysZ K x a).Y 0) ^ d with hU
  have hm'eq' : actZ K (U : K ⊗[ℂ] K) m' = c0 := hm'eq
  set ε : ℂ := (-1) ^ d with hε
  have hεε : ε * ε = 1 := by rw [hε, ← mul_pow]; simp
  set s0 : K ⊗[ℂ] K := algebraMap ℂ _ ε * ((U⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) with hs0
  have hm_eq : actZ K s0 c0 = ε • m' := by
    rw [← hm'eq', ← Module.End.mul_apply, ← map_mul, hs0, mul_assoc, Units.inv_mul, mul_one, AlgHom.commutes,
      Module.algebraMap_end_apply]
  have hmM : actZ K s0 c0 ∈ (sysZ K x a).M {0} {0} := by
    rw [hm_eq]
    exact Submodule.smul_mem _ _ hm'
  have hdiag : Acts (F := F) K τ a c0 ((-1) ^ d * kap K x (img (dj (0 : Fin (d + 1))))) := by
    have := hD 0 0 (img (dj 0)) hcardI
    have he : resK inlE c (uni (uni {0} {0}) (img (dj (0 : Fin (d + 1))))) = c0 := by
      show c (uni (lft _) ((rgt _).map _)) = _
      rw [(hlr _ _).1, (hlr _ _).2.1, map_inlE]
    rwa [he] at this
  have hact := (hAL F K d x hY.covZ τ hτ a).2.1 _ _ s0 hdiag
  have hX0 : algebraMap F K (x 0) ≠ 0 := by simp
  have hlU : Algebra.TensorProduct.lmul' ℂ ((U⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) * (algebraMap F K (x 0) * algebraMap F K (x 0)) ^ d = 1 := by
    have h1 : Algebra.TensorProduct.lmul' ℂ (U : K ⊗[ℂ] K) = (algebraMap F K (x 0) * algebraMap F K (x 0)) ^ d := by
      rw [hU, Units.val_pow_eq_pow_val, map_pow, Units.val_mul, map_mul, lmul_X, lmul_Y]
    rw [← h1, ← map_mul, Units.inv_mul, map_one]
  have hval : Algebra.TensorProduct.lmul' ℂ s0 * ((-1) ^ d * kap K x (img (dj (0 : Fin (d + 1))))) = algebraMap F K (omG x 0) := by
    have hε' : algebraMap ℂ K ε * (-1) ^ d = 1 := by
      rw [hε, map_pow, map_neg, map_one, ← mul_pow]; simp
    rw [hs0, map_mul, AlgHom.commutes, kap_dj x hTh, omG_zero]
    have hi : Algebra.TensorProduct.lmul' ℂ ((U⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = ((algebraMap F K (x 0) * algebraMap F K (x 0)) ^ d)⁻¹ :=
      eq_inv_of_mul_eq_one_left hlU
    rw [hi]
    exact valuation_power_identity _ _ _ d hX0 hε'
  rw [hval] at hact
  obtain ⟨s, hs1, hs2⟩ := hVal F K K' d x j2 Fx A hY τ hτ a ha _ hmM hact
  obtain ⟨gmu, gact, -, -, gZ⟩ := hG F K K' d x j2 hY.toY0 a ha
  have hgG : (fun l => gS j2 (app (sysZ K x a).mu z l)) = gG x j2 z := by
    funext t
    show gS j2 (Sum.elim _ _ (ofLex t)) = Sum.elim _ _ (ofLex t)
    cases ofLex t with
    | inl l => exact gmu l
    | inr l => rfl
  have hc' : (fun t => gY j2 (c t)) ∈ ((sysY x j2 d).cx (app n11 n) (gG x j2 z)).Z ((d : ℤ) + 2) := by
    rw [← hgG]
    exact gZ (Mi d ⊕ₗ κ) (app n11 n) (app (sysZ K x a).mu z) ((d : ℤ) + 2) c hc
  have hgX : gS j2 (((sysZ K x a).X 0 : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = algebraMap F K' (x 0) := by
    simp [sysZ, gS, ← IsScalarTower.algebraMap_apply]
  have hgY : gS j2 (((sysZ K x a).Y 0 : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = j2 (algebraMap F K (x 0)) := by
    simp [sysZ, gS]
  have hc'v : gY j2 c0 = ((-1) ^ d * (algebraMap F K' (x 0) * j2 (algebraMap F K (x 0))) ^ d * s) • dtS K' x Finset.univ := by
    have ht : actZ K (algebraMap ℂ _ ε * (U : K ⊗[ℂ] K)) (actZ K s0 c0) = c0 := by
      rw [← Module.End.mul_apply, ← map_mul, hs0]
      have : algebraMap ℂ (K ⊗[ℂ] K) ε * (U : K ⊗[ℂ] K) * (algebraMap ℂ (K ⊗[ℂ] K) ε * ((U⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K)) = 1 := by
        rw [mul_mul_mul_comm, ← map_mul, hεε, map_one, one_mul, Units.mul_inv]
      rw [this, map_one, Module.End.one_apply]
    have hgU : gS j2 (algebraMap ℂ _ ε * (U : K ⊗[ℂ] K)) = (-1) ^ d * (algebraMap F K' (x 0) * j2 (algebraMap F K (x 0))) ^ d := by
      rw [map_mul, AlgHom.commutes, hU, Units.val_pow_eq_pow_val, Units.val_mul, map_pow (gS j2), map_mul (gS j2), hgX, hgY, hε]
      simp
    calc gY j2 c0 = gY j2 (actZ K (algebraMap ℂ _ ε * (U : K ⊗[ℂ] K)) (actZ K s0 c0)) := by rw [ht]
      _ = _ := by rw [gact, hs1, smul_smul, hgU]
  have hsv : ∀ e ∈ Fx, Val (rB ℂ K' (xv x) {0}) e.1 s (e.1 h * (1 - A e).det) := fun e he => by
    rw [hon e he, locTerm, div_mul_cancel₀ _ (hY.det e he)]
    exact hs2 e he
  obtain ⟨c1, hc1, hc1v, hc1z⟩ := hBig F K K' d x j2 Fx A hY κ n z hz h hoff
  have hCmp := hCG F K K' d x j2 Fx A hY κ n z hz h s hsv c1 hc1 hc1v _ hc' hc'v
  have hres := (hSB d _ _ (sysY x j2 d) ((Mi d ⊕ₗ κ) ⊕ₗ Fin d) (app (app n11 n) n10) (app (gG x j2 z) (gT x j2))
    ((d : ℤ) + 2)).2.2.2.2.2 (Fin d) inrE c1 hc1
  have e1 : (fun l : Fin d => app (app n11 n) n10 ((inrE : Fin d ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d) l)) = n10 := funext fun l => rfl
  have e2 : (fun l : Fin d => app (gG x j2 z) (gT x j2) ((inrE : Fin d ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d) l)) = gT x j2 := funext fun l => rfl
  rw [e1, e2] at hres
  have hres1 : resK (inrE : Fin d ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d) c1 (uni (uni {0} {0}) Finset.univ) =
      ((-1) ^ d * algebraMap F K' (x 0) ^ d * (h : K')) • dtS K' x Finset.univ := by
    show c1 (uni (lft _) ((rgt _).map _)) = _
    rw [(hlr _ _).1, (hlr _ _).2.1]
    exact hc1v
  have hres2 : ∀ i j, (i ≠ 0 ∨ j ≠ 0) → col (resK (inrE : Fin d ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d) c1) (uni {i} {j}) = 0 := fun i j hij => by
    funext L
    show c1 (uni (lft _) ((rgt _).map _)) = 0
    rw [(hlr _ _).1, (hlr _ _).2.1]
    exact congrFun (hc1z i j hij) _
  have hT := hCT F K K' d x j2 Fx A hY h hoff (resK (inrE : Fin d ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d) c1) hres hres1 hres2
  have htop : top (resK (inrE : Fin d ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d) c1) = top c1 := by
    funext b
    show c1 (uni (lft _) ((rgt _).map _)) = c1 _
    rw [(hlr _ _).1, (hlr _ _).2.1, Finset.map_empty]
  rw [htop] at hT
  have := add_mem hCmp hT
  rw [sub_add_sub_cancel] at this
  have hfin : top (fun t => gY j2 (c t)) = fun s => gY j2 (top c s) := rfl
  rw [hfin] at this
  exact this

end UpperTheory.Gal.productCup_of_system
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DeltaConst
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

namespace UpperTheory.Gal.productCup_of_system

private theorem delta_const' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (v : E) :
    deltaL ℂ ι E (fun J => if J.card = 1 then v else 0) = 0 := by
  funext t
  change ∑ i ∈ t, GlobalTheory.cubeSign t i • (if (t.erase i).card = 1 then v else 0) = 0
  by_cases h2 : t.card = 2
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 h2
    rcases lt_or_gt_of_ne hab with h | h
    · have s1 : GlobalTheory.cubeSign ({a, b} : Finset ι) a = 1 := GlobalTheory.cubeSign_eq_one_of_forall_le (by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact le_rfl
        · exact h.le)
      have s2 : GlobalTheory.cubeSign ({a, b} : Finset ι) b = -1 := by
        have : ({a, b} : Finset ι).filter (· < b) = {a} := by
          ext j; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl, h'⟩
            · rfl
            · exact absurd h' (lt_irrefl _)
          · rintro rfl; exact ⟨Or.inl rfl, h⟩
        simp [GlobalTheory.cubeSign, this]
      rw [Finset.sum_pair hab, s1, s2]
      have e1 : (({a, b} : Finset ι).erase a).card = 1 := by
        rw [Finset.card_erase_of_mem (by simp), h2]
      have e2 : (({a, b} : Finset ι).erase b).card = 1 := by
        rw [Finset.card_erase_of_mem (by simp), h2]
      rw [if_pos e1, if_pos e2]; simp
    · have s1 : GlobalTheory.cubeSign ({a, b} : Finset ι) b = 1 := GlobalTheory.cubeSign_eq_one_of_forall_le (by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact h.le
        · exact le_rfl)
      have s2 : GlobalTheory.cubeSign ({a, b} : Finset ι) a = -1 := by
        have : ({a, b} : Finset ι).filter (· < a) = {b} := by
          ext j; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl, h'⟩
            · exact absurd h' (lt_irrefl _)
            · rfl
          · rintro rfl; exact ⟨Or.inr rfl, h⟩
        simp [GlobalTheory.cubeSign, this]
      rw [Finset.sum_pair hab, s1, s2]
      have e1 : (({a, b} : Finset ι).erase a).card = 1 := by
        rw [Finset.card_erase_of_mem (by simp), h2]
      have e2 : (({a, b} : Finset ι).erase b).card = 1 := by
        rw [Finset.card_erase_of_mem (by simp), h2]
      rw [if_pos e1, if_pos e2]; simp
  · refine Finset.sum_eq_zero fun i hi => ?_
    have : (t.erase i).card ≠ 1 := by
      rw [Finset.card_erase_of_mem hi]
      have := Finset.card_pos.2 ⟨i, hi⟩
      omega
    simp [this]

private theorem lft_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    lft (uni I J) = I := by
  ext i; simp [lft, uni]

private theorem rgt_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    rgt (uni I J) = J := by
  ext i; simp [rgt, uni]

private theorem omB_mono' {L : Type} [Field L] [Algebra ℂ L] {B B' : Subalgebra ℂ L} (h : B ≤ B') (q : ℕ) :
    omB ℂ L B q ≤ omB ℂ L B' q :=
  Submodule.span_mono (by
    rintro y ⟨b, hb, v, hv, rfl⟩
    exact ⟨b, h hb, v, fun j => h (hv j), rfl⟩)

private theorem omB_smul' {L : Type} [Field L] [Algebra ℂ L] {B : Subalgebra ℂ L} {q : ℕ} {r : L} (hr : r ∈ B)
    {m : DR ℂ L} (hm : m ∈ omB ℂ L B q) : r • m ∈ omB ℂ L B q := by
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hy
    rw [smul_smul]
    exact Submodule.subset_span ⟨r * b, B.mul_mem hr hb, v, hv, rfl⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add a c _ _ ha hc => rw [smul_add]; exact Submodule.add_mem _ ha hc
  | smul z a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ z ha

private theorem mem_acxC' {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E) (n : ℤ) (c : Finset σ → E) :
    c ∈ (acx A w).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then A s else ⊥) := by
  show c ∈ Submodule.pi Set.univ _ ↔ _
  simp only [Submodule.mem_pi, Set.mem_univ, forall_true_left]

private theorem pk_zero {d : ℕ} {I : Finset (Fin (d + 1))} (h : 0 ∈ I) : pk I = 0 := by
  have hn : I.Nonempty := ⟨0, h⟩
  rw [pk, dite_eq_left hn]
  exact le_antisymm (I.min'_le 0 h) (Fin.zero_le _)

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] {d : ℕ}
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')

private theorem inv_mem_rB (I : Finset (Fin (d + 1))) {m : Fin (d + 1)} (hm : m ∈ I) :
    algebraMap F K' ((x 0 : F) / x m) ∈ rB ℂ K' (xv x) I :=
  (integralClosure (rA ℂ (xv x) I) K').algebraMap_mem ⟨(x 0 : F) / x m, Algebra.subset_adjoin ⟨m, hm, 0, rfl⟩⟩

private theorem prod_tt :
    ∏ l, tt K' x l = ∏ m : Fin (d + 1), algebraMap F K' ((x m : F) / x 0) := by
  rw [Fin.prod_univ_succ, div_self (x 0).ne_zero, map_one, one_mul]
  rfl

private theorem prod_compl (I : Finset (Fin (d + 1))) :
    (∏ m ∈ I, algebraMap F K' ((x 0 : F) / x m)) * ∏ l, tt K' x l =
      ∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0) := by
  rw [prod_tt, ← Finset.prod_mul_prod_compl I, ← mul_assoc, ← Finset.prod_mul_distrib]
  rw [Finset.prod_eq_one, one_mul]
  intro m _
  rw [← map_mul, div_mul_div_comm, mul_comm (x 0 : F), div_self (mul_ne_zero (x m).ne_zero (x 0).ne_zero), map_one]

private theorem prod_X (I : Finset (Fin (d + 1))) :
    ∏ m ∈ I, algebraMap F K' (x m : F) =
      algebraMap F K' (x 0 : F) ^ I.card * ∏ m ∈ I, algebraMap F K' ((x m : F) / x 0) := by
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [← map_mul, mul_div_cancel₀ _ (x 0).ne_zero]

private theorem prod_tt_X :
    ∏ l : Fin d, algebraMap F K' (x l.succ : F) = algebraMap F K' (x 0 : F) ^ d * ∏ l, tt K' x l := by
  have : algebraMap F K' (x 0 : F) ^ d = ∏ _l : Fin d, algebraMap F K' (x 0 : F) := by simp
  rw [this, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [tt, ← map_mul, mul_div_cancel₀ _ (x 0).ne_zero]

end

theorem yXi_of :
    MJ → ThT → DtBasic → SysBasic → RYBasic → OmLoc → YXi := by
  intro hMJ hTh hDt hSB hRY _ F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY h
  obtain ⟨hw, h1, h0, hL⟩ := hTh d K' (DR ℂ K') (sysY x j2 d)
  obtain ⟨τ, hτ⟩ := hY.covY.exists_isTop
  obtain ⟨-, hdt, hvol, hom, -⟩ := hDt F K' d x hY.covY τ hτ
  obtain ⟨hR0, -, hmono, -, -⟩ := hRY F K K' d x j2 hY
  obtain ⟨v, hv⟩ : ∃ v : DR ℂ K', v = (h : K') • vol0 ℂ K' (xv x) := ⟨_, rfl⟩
  let b : Finset (Fin (d + 1)) → DR ℂ K' := fun J => if J.card = 1 then v else 0
  let θ := detC (sysY x j2 d).rowT
  have hval : ∀ I J L, (sysY x j2 d).mj 0 θ b (uni (uni I J) L) =
      ((-1 : ℤ) ^ ((0 + 1) * L.card)) • (θ (uni I L) • b J) := by
    intro I J L
    simp only [Sys.mj, lft_uni', rgt_uni']
    rfl
  have hcore : ∀ (I : Finset (Fin (d + 1))) (j : Fin (d + 1)), 0 ∈ I →
      (∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0)) • v ∈ omB ℂ K' (RY (xv x) j2 I {j}) d := by
    intro I j h0I
    have hle : rB ℂ K' (xv x) {0} ≤ RY (xv x) j2 I {j} := by
      have := hmono {0} I ∅ {j} (Finset.singleton_subset_iff.2 h0I) (Finset.empty_subset _)
      rwa [hR0] at this
    have hwm : (∏ m ∈ I, algebraMap F K' ((x 0 : F) / x m)) ∈ RY (xv x) j2 I {j} :=
      (le_sup_left : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I {j})
        (Subalgebra.prod_mem _ fun m hm => inv_mem_rB x I hm)
    have hd : dtS K' x Finset.univ ∈ omB ℂ K' (RY (xv x) j2 I {j}) d := by
      have := omB_mono' hle _ (hdt Finset.univ)
      simpa using this
    have e : (∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0)) • v =
        (∏ m ∈ I, algebraMap F K' ((x 0 : F) / x m)) • (h : K') • dtS K' x Finset.univ := by
      rw [hvol, hom, hv, smul_smul, smul_smul, smul_smul, ← prod_compl]
      congr 1
      ring
    rw [e]
    exact omB_smul' hwm (omB_smul' (hle h.2) hd)
  refine ⟨(sysY x j2 d).mj 0 θ b, Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [(hSB d K' (DR ℂ K') (sysY x j2 d) (Fin d) n10 (gT x j2) (d + 2)).2.1]
    intro I J
    split_ifs with hIJ
    · refine (mem_acxC' _ _ _ _).2 fun L => ?_
      change (sysY x j2 d).mj 0 θ b (uni (uni I J) L) ∈ _
      rw [hval]
      by_cases hJ : J.card = 1
      · rcases hL I L with hz | ⟨h0I, hc, ε, hε⟩
        · have : θ (uni I L) = 0 := hz
          simp [this]
        · obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hJ
          have hcard : ((L.card : ℤ) = (d : ℤ) + 2 - I.card - ({j} : Finset (Fin (d + 1))).card) := by
            simp only [Finset.card_singleton]
            omega
          rw [if_pos hcard, pk_zero h0I]
          refine ⟨(((-1 : ℤ) ^ ((0 + 1) * L.card)) * (ε : ℤ)) • ((∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0)) • v),
            Submodule.smul_of_tower_mem _ _ (hcore I j h0I), ?_⟩
          have hU : (((∏ l ∈ L, (sysY x j2 d).u n10 0 (pk {j}) l : K'ˣ)) : K') = algebraMap F K' (x 0 : F) ^ L.card := by
            rw [Units.coe_prod, Finset.prod_congr rfl (g := fun _ => algebraMap F K' (x 0 : F))
              (fun l _ => by simp [Sys.u, n10, sysY]), Finset.prod_const]
          have hθ : θ (uni I L) = ε • (algebraMap F K' (x 0 : F) ^ L.card * ∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0)) := by
            have hcc : Iᶜ.card = L.card := by
              rw [Finset.card_compl, Fintype.card_fin]; omega
            rw [← hcc, ← prod_X]
            exact hε
          have hb : b {j} = v := if_pos (Finset.card_singleton j)
          change (((∏ l ∈ L, (sysY x j2 d).u n10 0 (pk {j}) l : K'ˣ)) : K') • ((((-1 : ℤ) ^ ((0 + 1) * L.card)) * (ε : ℤ)) • ((∏ m ∈ Iᶜ, algebraMap F K' ((x m : F) / x 0)) • v)) = _
          rw [hU, hθ, hb, Units.smul_def, smul_assoc]
          simp only [mul_smul]
          rw [smul_comm (algebraMap F K' (x 0 : F) ^ L.card) ((-1 : ℤ) ^ ((0 + 1) * L.card)),
            smul_comm (algebraMap F K' (x 0 : F) ^ L.card) (ε : ℤ)]
      · have : b J = 0 := if_neg hJ
        simp [this]
    · refine (Submodule.mem_bot _).2 (funext fun L => ?_)
      change (sysY x j2 d).mj 0 θ b (uni (uni I J) L) = 0
      rw [hval]
      by_cases hJ : J.card = 1
      · have hI : ¬ I.Nonempty := fun hI => hIJ ⟨hI, Finset.card_pos.1 (by omega)⟩
        rcases hL I L with hz | ⟨h0I, -⟩
        · have : θ (uni I L) = 0 := hz
          simp [this]
        · exact absurd ⟨0, h0I⟩ hI
      · have : b J = 0 := if_neg hJ
        simp [this]
  · exact hMJ d K' (DR ℂ K') (sysY x j2 d) (Fin d) (gT x j2) 0 θ b hw (delta_const' v) (fun J hJ => if_neg hJ)
  · funext s
    change (sysY x j2 d).mj 0 θ b (uni s ∅) = edge1 (locCoch ℂ K' (xv x) h) s
    simp only [Sys.mj, lft_uni', rgt_uni', edge1, Finset.card_empty, mul_zero, pow_zero, one_smul]
    by_cases hc : (rgt s).card = 1
    · rw [if_pos hc]
      have hb : b (rgt s) = v := if_pos hc
      rw [hb]
      by_cases hu : lft s = Finset.univ
      · have hθ : θ (uni Finset.univ ∅) = 1 := h1
        rw [hu, hθ, locCoch, if_pos rfl, hv]
        simp [sysY]
      · rw [locCoch, if_neg hu]
        rcases hL (lft s) ∅ with hz | ⟨-, hc', -⟩
        · have : θ (uni (lft s) ∅) = 0 := hz
          rw [this]
          simp [sysY]
        · exfalso
          apply hu
          apply Finset.eq_univ_of_card
          simpa using hc'
    · rw [if_neg hc]
      have hb : b (rgt s) = 0 := if_neg hc
      rw [hb, map_zero]
  · intro j
    rw [hval]
    have hb : b {j} = v := if_pos (Finset.card_singleton j)
    have hθ : θ (uni {0} Finset.univ) = ∏ l : Fin d, algebraMap F K' (x l.succ : F) := h0
    rw [hb, hθ, prod_tt_X, hv, hvol, hom, Finset.card_univ, Fintype.card_fin, zero_add, one_mul,
      ← Int.cast_smul_eq_zsmul K', smul_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring

end UpperTheory.Gal.productCup_of_system
end

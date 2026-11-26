module

public import Development.WeilBound.CoreStatements.NefModelVolumes.TwoLtHalfFinrank
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToroidalFlagNonempty

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeLineBundleLe
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsNefModelOfImage
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsModelOfImage
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo
namespace GlobalTheory.ImageModel
theorem exists_model_of_image : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ), (∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → W.FG → Submodule.span K (W : Set V) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D → ∃ (X : AlgebraicGeometry.Scheme.{0}) (_ : AlgebraicGeometry.IsIntegral X) (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s := by
  intro _ K V Ω _ _ _ _ _ _ _ _ Nm W ev D hK hG hcj hW hs hR hD
  classical
  obtain ⟨N, n, b, w, A, hF⟩ := GlobalTheory.CompHt.exists_isFrame hK hcj hG hW hs
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases n with _ | m
    · exfalso
      have hW0 : W = ⊥ := by rw [← hF.span]; simp
      have htop : (⊤ : Submodule K V) = ⊥ := by rw [← hs, hW0]; simp
      refine hR.1 (LinearMap.ext fun x => ?_)
      have hx : x ∈ (⊥ : Submodule K V) := htop ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at hx
      simp [hx]
    · exact ⟨m, rfl⟩
  set u : Fin (m + 1) → V := fun k => ∑ j, w j k • b j with hu_def
  have huW : ∀ k, u k ∈ W := fun k => hF.span ▸ Submodule.subset_span ⟨k, rfl⟩
  let gw : Fin (m + 1) → W := fun k => ⟨u k, huW k⟩
  have hspan : Submodule.span K (Set.range u) = ⊤ := by
    rw [← hs, ← hF.span, Submodule.span_span_of_tower]
  choose cc hcc using fun j => (Submodule.mem_span_range_iff_exists_fun K).1
    (hspan ▸ Submodule.mem_top : b j ∈ Submodule.span K (Set.range u))
  let c : Matrix (Fin (m + 1)) (Fin N) K := Matrix.of fun k j => cc j k
  set y : Fin (m + 1) → Ω := fun k => ev (u k) with hy_def
  have hy0 : y ≠ 0 := fun h0 => hR.1 (LinearMap.ext_on_range hspan fun k => by
    simpa using congrFun h0 k)
  obtain ⟨Y, _, q, B₀, hB₀, t, ψ₀, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_integral_projective_closure_of_linearSystem_point K V Ω ev D m u hspan hR hD
  obtain ⟨X₀, _, p₀, g₀, ψ₁, e⟩ := GlobalTheory.T.exists_flat_projective_model_over_ringOfIntegers K Ω D m y Y q B₀ hB₀ t ψ₀ h1 h2 h3 h4 h5 h6
  obtain ⟨X, _, p, g, ψ, hgp, har, hnorm, hbij, hbase, hrat⟩ := GlobalTheory.T.exists_normal_arithmeticVariety_model_projectiveSpace K Ω D m y X₀ p₀ g₀ ψ₁ e
  let B := (ProjSpace.O1 (𝓞 K) m).pull g
  have hB : B.IsLB := LB.isLB_pull (ProjSpace.O1_isLB _ m) g
  let sk : Fin (m + 1) → B.Sec := fun k => secPull (ProjSpace.coord (𝓞 K) m k) g
  obtain ⟨hlin, hrel⟩ := GlobalTheory.T.pulledBack_coordinate_combination_ratio_and_vanish K Ω m y X p g ψ hbase hrat
  have hev : ∀ lam : Fin (m + 1) → 𝓞 K, ev (∑ k, lam k • u k) = ∑ k, algebraMap K Ω (lam k : K) * y k := by
    intro lam
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← algebraMap_smul K (lam k) (u k), LinearMap.map_smul, Algebra.smul_def]
  have hrelV : ∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, algX p ⊤ (lam k) • sk k = 0 :=
    fun lam h0 => hrel hy0 lam (by rw [← hev, h0, map_zero])
  choose coef hcoef using fun x : W => (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1
    (hF.span.symm ▸ x.2 : (x : V) ∈ Submodule.span (𝓞 K) (Set.range u))
  let s : W → B.Sec := fun x => ∑ k, algX p ⊤ (coef x k) • sk k
  have sg : ∀ k, s (gw k) = sk k := by
    intro k
    have e1 : ∑ l, (Pi.single k (1 : 𝓞 K) : Fin (m + 1) → 𝓞 K) l • u l = u k := by
      rw [Finset.sum_eq_single k (fun l _ hl => by rw [Pi.single_eq_of_ne hl, zero_smul]) (by simp)]
      rw [Pi.single_eq_same, one_smul]
    have e3 : ∑ l, algX p ⊤ ((Pi.single k (1 : 𝓞 K) : Fin (m + 1) → 𝓞 K) l) • sk l = sk k := by
      rw [Finset.sum_eq_single k (fun l _ hl => by rw [Pi.single_eq_of_ne hl, map_zero, zero_smul]) (by simp)]
      rw [Pi.single_eq_same, map_one, one_smul]
    have h0 := hrelV (coef (gw k) - Pi.single k 1) (by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hcoef, e1]
      exact sub_eq_zero.2 (hcoef (gw k)))
    simp only [Pi.sub_apply, map_sub, sub_smul, Finset.sum_sub_distrib, e3, sub_eq_zero] at h0
    exact h0
  have hbpf : ⨆ k, nonzeroLocus (sk k) = ⊤ :=
    ProjSpace.iSup_nonzeroLocus_secPull (ProjSpace.iSup_nonzeroLocus_coord (𝓞 K) m) g
  let A' : (𝓞 K →+* ℂ) → Matrix (Fin (m + 1)) (Fin N) ℂ := fun τ =>
    c.map (OfLattice.extEmb τ) * A (OfLattice.extEmb τ)
  have hnz := GlobalTheory.T.fubiniStudy_coordinate_combinations_noCommonZero K V m N X p g u b c A hgp hrelV (fun j => (hcc j).symm) hF.herm
  have hcU : ∀ τ : 𝓞 K →+* ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ,
      A' ((starRingEnd ℂ).comp τ) = (A' τ).map (starRingEnd ℂ) * U := by
    intro τ
    obtain ⟨U, hU, eU⟩ := GlobalTheory.T.frame_conjugate_embedding_eq_conj_mul_unitary K N A hF.conj hF.herm (OfLattice.extEmb τ)
    have he : OfLattice.extEmb ((starRingEnd ℂ).comp τ) = (starRingEnd ℂ).comp (OfLattice.extEmb τ) :=
      OfLattice.extEmb_eq (by rw [RingHom.comp_assoc, OfLattice.extEmb_comp])
    refine ⟨U, hU, ?_⟩
    simp only [A', he, eU, Matrix.map_mul, Matrix.map_map, Matrix.mul_assoc]
    rfl
  let L : HermLB p := OfLattice.combHerm hB sk A' hnz hcU
  refine ⟨X, inferInstance, p, L, ψ, s, har, hnorm, hbij, hbase, ?_, ?_, ?_⟩
  · obtain ⟨k₀, hk₀⟩ : ∃ k, y k ≠ 0 := by
      by_contra! h; exact hy0 (funext h)
    intro x x' i h
    have hψ : ψ (y k₀) ≠ 0 := (map_ne_zero ψ).2 hk₀
    have ha : ψ (y k₀) * fnOf _ h ((s x).f i) = ψ (ev x) * fnOf _ h ((sk k₀).f i) := by
      have := hlin (coef x) k₀ i h
      rwa [← hev, hcoef] at this
    have hb : ψ (y k₀) * fnOf _ h ((s x').f i) = ψ (ev x') * fnOf _ h ((sk k₀).f i) := by
      have := hlin (coef x') k₀ i h
      rwa [← hev, hcoef] at this
    refine mul_left_cancel₀ hψ ?_
    linear_combination (ψ (ev x)) * hb - (ψ (ev x')) * ha
  · refine top_le_iff.1 ?_
    rw [← hbpf]
    exact iSup_le fun k => by
      rw [← sg k]
      exact le_iSup (fun x => nonzeroLocus (s x)) (gw k)
  · refine ⟨N, m + 1, b, w, A, c, gw, hF, fun k => rfl, fun j => (hcc j).symm, fun σ i z => ?_⟩
    have he : OfLattice.extEmb (σ.comp (algebraMap (𝓞 K) K)) = σ := OfLattice.extEmb_eq rfl
    refine (OfLattice.combWeight_φ hB sk _ (hnz _) i z).trans ?_
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sg k]
    simp only [A', he, Matrix.mul_apply, Matrix.map_apply, c, Matrix.of_apply]
    rfl
end GlobalTheory.ImageModel
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.image_admits_model : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ), (∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → W.FG → Submodule.span K (W : Set V) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D → ∃ (X : AlgebraicGeometry.Scheme.{0}) (_ : AlgebraicGeometry.IsIntegral X) (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s := by
  first | exact @_root_.GlobalTheory.ImageModel.exists_model_of_image | exact _root_.GlobalTheory.ImageModel.exists_model_of_image | (intros; apply _root_.GlobalTheory.ImageModel.exists_model_of_image <;> assumption)
end
end

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
namespace SelfIntersectionVolumeEstimates.ImageNefG
theorem exists_nef_model_of_image : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (n : ℕ) (w : Fin n → cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (abelian₂ t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) w abelian₂ → Real.log abelian₂ ≤ t → ∃ (k : Type) (_ : CommRing k) (X : AlgebraicGeometry.Scheme.{0}) (_ : AlgebraicGeometry.IsIntegral X) (p : X ⟶ Sp k) (L : GlobalTheory.HermLB p) (A : ℝ), GlobalTheory.IsArithVar p (dimFlag (T.Q.Dw j)) ∧ L.IsNef (dimFlag (T.Q.Dw j)) ∧ L.IsSelfInter A ∧ A ≤ (Module.finrank ℚ Y.d.c₂.F : ℝ) * ((dimFlag (T.Q.Dw j) : ℝ) + 1) * (Y.dg u Z * (Y.ht u Z + t)) ∧ ∀ i : ℕ, 1 ≤ i → (smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t).encard ≤ (L.pow (8 * i)).smallSec.encard := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro hPX hP D T j Y e o hY h2 Z u n w abelian₂ t hG hB hN hd hS hL
  obtain ⟨hgram, hfg, hspan⟩ := hG
  have hK : ∀ σ : Y.d.c₂.F →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ := fun σ => conj_comp_ne σ
  have hconj : ∀ σ (x : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)),
      normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) ((starRingEnd ℂ).comp σ) x =
        normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) σ x :=
    fun σ x => petOn_conj Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) σ (x : Rul Y.d.Xo₂ Y.d.c₂)
  have hdeg : 0 < imageDeg (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) := by
    have := hd
    simp only [Deep.dg, compDeg, Nat.cast_pos] at this
    exact this
  have hB' : GlobalTheory.DegVal.GenRatios (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) := hB
  obtain ⟨X, hX, p, L0, ψ, s, hM⟩ := _root_.GlobalTheory.T.image_admits_model hP Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (Om Z)
    (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0))
    (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) hK hgram hconj hfg hspan hB hdeg
  obtain ⟨h, hh, -⟩ := hP.q11.existsUnique hM.arith (L0.shift (fun _ => t) (fun _ => rfl))
  refine ⟨𝓞 Y.d.c₂.F, inferInstance, X, hX, p, L0.shift (fun _ => t) (fun _ => rfl),
    h (genericPoint X), hM.arith, ?_, ⟨h, hh, rfl⟩, ?_, ?_⟩
  · exact GlobalTheory.T.isNef_shifted_fubiniStudy_of_short_generators Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (Om Z)
      (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0))
      (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) X p L0 ψ s n w abelian₂ t hM hB'.1 hS hL
  · have key : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec) (t a : ℝ), (∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → W.FG → Submodule.span K (W : Set V) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D → GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → (L.shift (fun _ => t) (fun _ => rfl)).IsSelfInter a → a ≤ (Module.finrank ℚ K : ℝ) * ((D : ℝ) + 1) * ((imageDeg ev D : ℝ) * (imageHeight Nm W ev D + t)) := by
      exact hPX.1
    exact key hP Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (Om Z)
      (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0))
      (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) X p L0 ψ s t _ hK hgram hconj hfg hspan
      hB hdeg hM ⟨h, hh, rfl⟩
  · exact hPX.2 hP D T j Y e o hY h2 Z u X p L0 ψ s t ⟨hgram, hfg, hspan⟩ hB hN hd hM
end SelfIntersectionVolumeEstimates.ImageNefG
end
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
namespace SelfIntersectionVolumeEstimates.VolUpG
theorem volume_line_bundle_le : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (n : ℕ) (w : Fin n → cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (abelian₂ t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) w abelian₂ → Real.log abelian₂ ≤ t → volL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict 8 Z (wtOf (T.Q.Dw j) u 0) t ≤ ENNReal.ofReal (Y.dg u Z * (Y.ht u Z + t)) := by
  intro hX hP D T j Y e o hG hE Z u n w abelian₂ t hGood hBir hNo hdg hShort hLam
  obtain ⟨k, _, X, _, p, L, A, hV, hN, hS, hA, hinj⟩ :=
    _root_.SelfIntersectionVolumeEstimates.ImageNefG.exists_nef_model_of_image hX hP D T j Y e o hG hE Z u n w abelian₂ t hGood hBir hNo hdg hShort hLam
  have hd : 0 < Module.finrank ℚ Y.d.c₂.F := Module.finrank_pos
  have h2 := GlobalTheory.T.countingVolume_le_selfIntersection_nefHermitianBundle k X p (dimFlag (T.Q.Dw j)) (Module.finrank ℚ Y.d.c₂.F) 8 L A
    (fun τ => (smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) τ t).encard)
    hP.q9 hV hN hS hd (by norm_num) hinj
  refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
  have hpos : (0 : ℝ) < (Module.finrank ℚ Y.d.c₂.F : ℝ) * ((dimFlag (T.Q.Dw j) : ℝ) + 1) := by positivity
  rw [div_le_iff₀ hpos]
  linarith [hA]
end SelfIntersectionVolumeEstimates.VolUpG
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoverHeightComparison
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovHt
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.CovHt.FrameCmp
section Different
variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  {E : Type} [Field E] [NumberField E]
end Different
section Point
variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0}
  {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)
variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
end Point
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
section Frame
variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0}
  {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  [Algebra c.F C] [StarRing (𝓞 E)] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
end Frame
attribute [local instance] algPadicInt algPadicField towerPadic factPadic PadicComplexHost.isAdicComplete
end GlobalTheory.CovHt.FrameCmp
theorem GlobalTheory.CovHt.cover_height_comparison : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
    HTCmp Xo c := fun _ _ _ _ _ _ _ _ _ _ _ => GlobalTheory.CovHt.FrameCmp.htCmp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ImageHeightNonnegOfDivisor
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
namespace GlobalTheory.ImageHeightNonneg
theorem imageHeight_nonneg_of_divisor : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (K V Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (d n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → Submodule.span K (L : Set V) = ⊤ → IsShortGen Nm L w abelian₂ → 0 < imageDeg ev d → 0 ≤ imageHeight Nm L ev d + Real.log abelian₂ :=
  fun _ => imageHeight_add_log_nonneg
end GlobalTheory.ImageHeightNonneg
end
end
end

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.CovHt.HtTopG
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} {p : PtAt ex Csz} {i : Fin D.R.m} {Y : Cov p i}
theorem height_add_log_nonneg (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {u1 : AllWt.Weight (dat p i)} {Z : Comp Y.d.Xo₂ Y.d.c₂} {n : ℕ}
    {w : Fin n → cuspOn Y.U Z (wtOf (dat p i) u1 0)} {abelian₂ : ℝ}
    (hw : IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0))
        (latOn Y.U Z (wtOf (dat p i) u1 0)) w abelian₂)
    (hG : GoodOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0)) (hd : 0 < Y.dg u1 Z) :
    0 ≤ Y.ht u1 Z + Real.log abelian₂ := by
  haveI hTC : IsTotallyComplex Y.d.c₂.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := Y.d.c₂) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  have hd' : 0 < compDeg Y.U Z (wtOf (dat p i) u1 0) := by exact_mod_cast hd
  exact _root_.GlobalTheory.ImageHeightNonneg.imageHeight_nonneg_of_divisor hP _ _ _ _ _ _ _ _ w abelian₂ hG.1 (fun σ f => petOn_conj _ _ _ _ Z _ σ f) hG.2.2 hw hd'
theorem slope_le_height (hPX : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses) (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (hHT : HTCmp Y.d.Xo₂ Y.d.c₂)
    {u1 : AllWt.Weight (dat p i)} {Z : Comp Y.d.Xo₂ Y.d.c₂} {n : ℕ}
    {w : Fin n → cuspOn Y.U Z (wtOf (dat p i) u1 0)} {abelian₂ : ℝ}
    (hw : IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0))
        (latOn Y.U Z (wtOf (dat p i) u1 0)) w abelian₂)
    (hGo : GoodOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0))
    (hBir : GlobalTheory.DegVal.BirOn Y.U Z (wtOf (dat p i) u1 0))
    (hdel : (1 - rhoB (dat p i) u1) * Y.dg u1 Z ≤ delPrime Y.U Z u1) (hρ : rhoB (dat p i) u1 < 1) (hd : 0 < Y.dg u1 Z)
    {cc B s cs : ℝ} (hM : Mult Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z u1 (uPrime (dat p i) u1) cc)
    (hcc : 0 ≤ cc) (hh : 0 ≤ htCost Y.d.l₂ B * l1 (uPrime (dat p i) u1)) (hcs : Real.log abelian₂ ≤ cs)
    (hnn : 0 ≤ Y.ht u1 Z + cs)
    (hs : (s : EReal) ≤ compVolSlope Y.U (xiR D) 8 (mixVals Y.d.Xo₂ Y.d.c₂ B) Z (uPrime (dat p i) u1)) :
    (1 - rhoB (dat p i) u1) * max 0 (s + cs) ≤ Y.ht u1 Z + cs + (cc + htCost Y.d.l₂ B * l1 (uPrime (dat p i) u1)) := by
  have h1ρ : 0 < 1 - rhoB (dat p i) u1 := by linarith
  have hdelpos : 0 < topDeg Y.U Z (uPrime (dat p i) u1) :=
    lt_of_lt_of_le (mul_pos h1ρ hd) hdel
  have hf := two_lt_half_finrank D
  set hc := htCost Y.d.l₂ B * l1 (uPrime (dat p i) u1) with hhc
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hA := (le_compVolSlope_iff Y.U (xiR D) 8 (mixVals Y.d.Xo₂ Y.d.c₂ B) hdelpos s).1 hs cs
  have hB := GlobalTheory.CovHtCmp.compVol_le_volL_deep D p.T.toCore ((i : ℕ) + 1) Y e o hY hf hHT Z u1 (uPrime (dat p i) u1) cc B cs ε hM hε
  have hC := _root_.SelfIntersectionVolumeEstimates.VolUpG.volume_line_bundle_le hPX hP D p.T.toCore ((i : ℕ) + 1) Y e o hY hf Z u1 n w abelian₂ (cs + cc + hc + ε) hGo hBir hM.1 hd hw
    (by linarith)
  have hABC := hA.trans (hB.trans hC)
  have hpos : 0 ≤ Y.dg u1 Z * (Y.ht u1 Z + (cs + cc + hc + ε)) := mul_nonneg hd.le (by linarith)
  rw [ENNReal.ofReal_le_ofReal_iff hpos] at hABC
  change delPrime Y.U Z u1 * (s + cs) ≤ _ at hABC
  have key : (1 - rhoB (dat p i) u1) * max 0 (s + cs) * Y.dg u1 Z ≤ (Y.ht u1 Z + cs + (cc + hc) + ε) * Y.dg u1 Z := by
    rcases le_total (s + cs) 0 with h | h
    · rw [max_eq_left h, mul_zero, zero_mul]
      exact mul_nonneg (by linarith) hd.le
    · rw [max_eq_right h]
      calc (1 - rhoB (dat p i) u1) * (s + cs) * Y.dg u1 Z = ((1 - rhoB (dat p i) u1) * Y.dg u1 Z) * (s + cs) := by ring
        _ ≤ delPrime Y.U Z u1 * (s + cs) := mul_le_mul_of_nonneg_right hdel h
        _ ≤ _ := hABC
        _ = _ := by ring
  exact le_of_mul_le_mul_right key hd
theorem heightAt_eq_of_cover (hPX : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses) (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (hHT : HTCmp Y.d.Xo₂ Y.d.c₂)
    {C0 Cs Cm Cb PP : ℝ} (h0 : 0 ≤ C0) (hs0 : 0 ≤ Cs) (hm0 : 0 ≤ Cm) (hb0 : 0 ≤ Cb) (hU : 0 ≤ unitE p)
    (hmean : MeanAll Y.U (xiR D) (ell D) C0) (hne : Nonempty (Comp Y.d.Xo₂ Y.d.c₂)) {u1 : AllWt.Weight (dat p i)}
    (hρ : rhoB (dat p i) u1 < 1) (hDeg : DegAt p i Y u1) (hS : ShortAt p i Y PP Cs u1) (hGe : GeomAt p i Y u1)
    (hM : MultAt p i Y PP Cm u1) (hB : BudgetAt p i Y PP Cb u1) :
    HeightAt p i Y PP (Cs + Cm + Cb + C0 * Cb) u1 := by
  obtain ⟨abelian₂, hLam, hSb⟩ := hS
  obtain ⟨cc, hcc, hccb, hMZ⟩ := hM
  obtain ⟨-, g, hgap, herr0, herrb, hht0, hhtb⟩ := hB
  obtain ⟨sl, hsl, hX⟩ := hmean (uPrime (dat p i) u1) g hgap
  obtain ⟨δ, hδ, hδZ⟩ := hDeg
  have hdg : ∀ Z, 0 < Y.dg u1 Z := fun Z => lt_of_lt_of_le hδ (hδZ Z).1
  have hLam1 : 1 ≤ abelian₂ := by
    obtain ⟨Z⟩ := hne
    obtain ⟨n, w, hw⟩ := hLam Z
    exact hw.one_le
  have hcs : 0 ≤ Real.log abelian₂ := Real.log_nonneg hLam1
  have hl1 : 0 ≤ l1 (uPrime (dat p i) u1) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hhc : 0 ≤ htCost Y.d.l₂ (bndB (uPrime (dat p i) u1) g) * l1 (uPrime (dat p i) u1) := mul_nonneg hht0 hl1
  have hT : (0 : ℝ) ≤ lenT p i PP := Nat.cast_nonneg _
  have hnn : ∀ Z, 0 ≤ Y.ht u1 Z + Real.log abelian₂ := fun Z => by
    obtain ⟨n, w, hw⟩ := hLam Z
    exact _root_.GlobalTheory.CovHt.HtTopG.height_add_log_nonneg hP hw (hGe Z).1 (hdg Z)
  have e1 : 0 ≤ Cs * unitE p := mul_nonneg hs0 hU
  have e2 : 0 ≤ Cm * unitE p := mul_nonneg hm0 hU
  have e3 : 0 ≤ Cb * unitE p := mul_nonneg hb0 hU
  have e4 : 0 ≤ C0 * Cb * unitE p := mul_nonneg (mul_nonneg h0 hb0) hU
  refine ⟨Real.log abelian₂, cc + htCost Y.d.l₂ (bndB (uPrime (dat p i) u1) g) * l1 (uPrime (dat p i) u1),
    C0 * errX (ell D) (uPrime (dat p i) u1) g, sl, hcs, add_nonneg hcc hhc, mul_nonneg h0 herr0, hnn, fun Z => ?_, hX,
    ?_, ?_, ?_⟩
  · obtain ⟨n, w, hw⟩ := hLam Z
    exact _root_.GlobalTheory.CovHt.HtTopG.slope_le_height hPX hP hY hHT hw (hGe Z).1 (hGe Z).2.1 (hGe Z).2.2 hρ (hdg Z) (hMZ Z) hcc hhc le_rfl (hnn Z) (hsl Z)
  · have : (lenT p i PP : ℝ) * (C0 * errX (ell D) (uPrime (dat p i) u1) g) ≤ C0 * Cb * unitE p := by
      rw [mul_left_comm, mul_assoc]
      exact mul_le_mul_of_nonneg_left herrb h0
    linarith
  · rw [mul_add]
    linarith
  · linarith
end Point
end GlobalTheory.CovHt.HtTopG
end
end

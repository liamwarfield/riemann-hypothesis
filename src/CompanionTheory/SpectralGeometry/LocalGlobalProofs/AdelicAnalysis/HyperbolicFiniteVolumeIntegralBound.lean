module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicPrimitiveVectorCompactRescale
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramOrbitCompactRepresentative
public import CompanionTheory.AutomorphicTheory.ThetaDilations.ActWSmul
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionGlobal

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicFundamentalDomainCover
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicUnitaryStabilizerCocompact
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicUnitaryStabilizerCocompact
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Iwa

section Alg

variable {K : Type} [CommRing K] {N : ℕ}

theorem hform_eq (s : K →+* K) (L : Matrix (Fin N) (Fin N) K) (x y : Fin N → K) :
    hform s L x y = (fun i => s (x i)) ⬝ᵥ (L *ᵥ y) := by
  simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_sub_right (s : K →+* K) (L : Matrix (Fin N) (Fin N) K) (x y w : Fin N → K) :
    hform s L x (y - w) = hform s L x y - hform s L x w := by
  simp [hform_eq, Matrix.mulVec_sub, dotProduct_sub]

theorem hform_smul_right (s : K →+* K) (L : Matrix (Fin N) (Fin N) K) (c : K) (x y : Fin N → K) :
    hform s L x (c • y) = c * hform s L x y := by
  simp [hform_eq, Matrix.mulVec_smul, dotProduct_smul]

theorem hform_sub_left (s : K →+* K) (L : Matrix (Fin N) (Fin N) K) (x w y : Fin N → K) :
    hform s L (x - w) y = hform s L x y - hform s L w y := by
  simp only [hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_smul_left (s : K →+* K) (L : Matrix (Fin N) (Fin N) K) (c : K) (x y : Fin N → K) :
    hform s L (c • x) y = s c * hform s L x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem hform_conj (s : K →+* K) (L : Matrix (Fin N) (Fin N) K) (hs : ∀ x, s (s x) = x)
    (hL : ∀ i j, s (L j i) = L i j) (x y : Fin N → K) :
    s (hform s L x y) = hform s L y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hform, map_sum, map_mul, hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hL]; ring

def dualV (s : K →+* K) (Li : Matrix (Fin N) (Fin N) K) (z : Fin N → K) : Fin N → K :=
  fun i => s ((z ᵥ* Li) i)

theorem hform_dual (s : K →+* K) (L Li : Matrix (Fin N) (Fin N) K) (hs : ∀ x, s (s x) = x)
    (hLi : Li * L = 1) (z w : Fin N → K) : hform s L (dualV s Li z) w = z ⬝ᵥ w := by
  have h : hform s L (dualV s Li z) w = (z ᵥ* Li) ⬝ᵥ (L *ᵥ w) := by
    simp only [hform_eq, dualV, hs]
  rw [h, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hLi, Matrix.vecMul_one]

def partner (s : K →+* K) (L Li : Matrix (Fin N) (Fin N) K) (half : K) (z w : Fin N → K) : Fin N → K :=
  dualV s Li z - (half * hform s L (dualV s Li z) (dualV s Li z)) • w

theorem partner_spec (s : K →+* K) (L Li : Matrix (Fin N) (Fin N) K) (half : K)
    (hs : ∀ x, s (s x) = x) (hL : ∀ i j, s (L j i) = L i j) (hLi : Li * L = 1)
    (hh : s half = half) (h2 : 2 * half = 1) (z w : Fin N → K) (hw : hform s L w w = 0)
    (hz : z ⬝ᵥ w = 1) :
    hform s L w (partner s L Li half z w) = 1 ∧ hform s L (partner s L Li half z w) w = 1 ∧
      hform s L (partner s L Li half z w) (partner s L Li half z w) = 0 := by
  set u := dualV s Li z with hu
  set A := hform s L u u with hA
  have huw : hform s L u w = 1 := by rw [hu, hform_dual s L Li hs hLi, hz]
  have hwu : hform s L w u = 1 := by rw [← hform_conj s L hs hL u w, huw, map_one]
  have hsA : s A = A := hform_conj s L hs hL u u
  have hc : s (half * A) = half * A := by rw [map_mul, hh, hsA]
  have hp : partner s L Li half z w = u - (half * A) • w := rfl
  have e1 : hform s L w (u - (half * A) • w) = 1 := by
    rw [hform_sub_right, hform_smul_right, hwu, hw]; ring
  have e2 : hform s L (u - (half * A) • w) w = 1 := by
    rw [hform_sub_left, hform_smul_left, huw, hw]; ring
  have e3 : hform s L u (u - (half * A) • w) = A - half * A := by
    rw [hform_sub_right, hform_smul_right, huw, ← hA]; ring
  rw [hp]
  refine ⟨e1, e2, ?_⟩
  rw [hform_sub_left, hform_smul_left, e1, e3, hc]
  linear_combination (-A) * h2

theorem hform_single (s : K →+* K) (L : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    hform s L (Pi.single i 1) (Pi.single j 1) = L i j := by
  simp [hform_eq, Matrix.mulVec_single_one, dotProduct, Pi.single_apply, apply_ite s]

variable [TopologicalSpace K] [IsTopologicalRing K]

theorem continuous_hform (s : K →+* K) (hs : Continuous s) (L : Matrix (Fin N) (Fin N) K) :
    Continuous fun p : (Fin N → K) × (Fin N → K) => hform s L p.1 p.2 := by
  unfold hform
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  have h1 : Continuous fun p : (Fin N → K) × (Fin N → K) => p.1 i :=
    (continuous_apply i).comp continuous_fst
  have h2 : Continuous fun p : (Fin N → K) × (Fin N → K) => p.2 j :=
    (continuous_apply j).comp continuous_snd
  exact ((hs.comp h1).mul continuous_const).mul h2

theorem continuous_dualV (s : K →+* K) (hs : Continuous s) (Li : Matrix (Fin N) (Fin N) K) :
    Continuous (dualV s Li) := by
  refine continuous_pi fun i => hs.comp ?_
  exact (continuous_apply i).comp (continuous_id.matrix_vecMul continuous_const)

theorem continuous_partner (s : K →+* K) (hs : Continuous s) (L Li : Matrix (Fin N) (Fin N) K)
    (half : K) : Continuous fun p : (Fin N → K) × (Fin N → K) => partner s L Li half p.1 p.2 := by
  have hd : Continuous fun p : (Fin N → K) × (Fin N → K) => dualV s Li p.1 :=
    (continuous_dualV s hs Li).comp continuous_fst
  have hf : Continuous fun p : (Fin N → K) × (Fin N → K) =>
      hform s L (dualV s Li p.1) (dualV s Li p.1) :=
    (continuous_hform s hs L).comp (hd.prodMk hd)
  unfold partner
  exact hd.sub ((continuous_const.mul hf).smul continuous_snd)

end Alg

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_invol (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x)
    (a : R ⊗[F] E) : sigR R σ (sigR R σ a) = a := by
  induction a with
  | tmul r e => simp [sigR, hσ]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

theorem sigR_incl (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (e : E) :
    sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem gramR_ratTup (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {N n : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (X : Fin n → Fin N → E) :
    gramR R σ J (ratTup R X) = (gramE σ J X).map (inclR R) := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramR, hR, hform, ratTup, JR, sigR_incl, Matrix.map_apply, gramE, hE, map_sum, map_mul]
  rfl

end Tens

def frame (E : Type) [Field E] (M : ℕ) : Fin 2 → Fin (M + 2) → E :=
  ![Pi.single 0 1, Pi.single (Fin.succ 0) 1]

theorem gram_frame {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) :
    gramE σ (hypJ J) (frame E M) = !![0, 1; 1, 0] := by
  have h : ∀ i j : Fin (M + 2), hE σ (hypJ J) (Pi.single i 1) (Pi.single j 1) = hypJ J i j :=
    fun i j => hform_single (σ : E →+* E) (hypJ J) i j
  ext a b
  fin_cases a <;> fin_cases b
  · exact (h 0 0).trans (by simp [hypJ])
  · exact (h 0 (Fin.succ 0)).trans (by simp [hypJ])
  · exact (h (Fin.succ 0) 0).trans (by simp [hypJ])
  · exact (h (Fin.succ 0) (Fin.succ 0)).trans (by simp [hypJ])

theorem eOne_eq_frame {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (M : ℕ) (a : Fin 1) :
    eOne (R ⊗[F] E) (M + 1) a = ratTup R (frame E M) 0 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [eOne, ratTup, frame]
  · simp [eOne, ratTup, frame, Pi.single_apply, Fin.succ_ne_zero]

section Core

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {N : ℕ}

theorem continuous_pair (s : K →+* K) (hs : Continuous s) (L Li : Matrix (Fin N) (Fin N) K) (half : K) :
    Continuous fun p : (Fin 1 → Fin N → K) × (Fin 1 → Fin N → K) =>
      (![p.1 0, partner s L Li half (p.2 0) (p.1 0)] : Fin 2 → Fin N → K) := by
  have c1 : Continuous fun p : (Fin 1 → Fin N → K) × (Fin 1 → Fin N → K) => p.1 0 :=
    (continuous_apply 0).comp continuous_fst
  have c2 : Continuous fun p : (Fin 1 → Fin N → K) × (Fin 1 → Fin N → K) => p.2 0 :=
    (continuous_apply 0).comp continuous_snd
  have c3 := (continuous_partner s hs L Li half).comp (c2.prodMk c1)
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact c1
  · exact c3

theorem gram_pair (s : K →+* K) (L : Matrix (Fin N) (Fin N) K) (w p : Fin N → K)
    (h00 : hform s L w w = 0) (h01 : hform s L w p = 1) (h10 : hform s L p w = 1)
    (h11 : hform s L p p = 0) (a b : Fin 2) :
    hform s L ((![w, p] : Fin 2 → Fin N → K) a) ((![w, p] : Fin 2 → Fin N → K) b) =
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) a b := by
  fin_cases a <;> fin_cases b
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem iwa_core {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (s : K →+* K) (hsc : Continuous s) (hs : ∀ x, s (s x) = x) (L Li : Matrix (Fin N) (Fin N) K)
    (hL : ∀ i j, s (L j i) = L i j) (hLi : Li * L = 1) (half : K) (hh : s half = half)
    (h2 : 2 * half = 1) (act : H → (Fin N → K) → Fin N → K)
    (hmul : ∀ g k v, act (g * k) v = act g (act k v)) (hone : ∀ v, act 1 v = v)
    (hsmul : ∀ g (a : K) v, act g (a • v) = a • act g v)
    (hpres : ∀ g x y, hform s L (act g x) (act g y) = hform s L x y)
    (X : Fin 2 → Fin N → K) (hX : ∀ a b, hform s L (X a) (X b) = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) a b)
    (Ω : Set (Fin 1 → Fin N → K)) (hΩ : IsCompact Ω)
    (hprim : ∀ y : Fin 1 → Fin N → K, (∃ z : Fin N → K, z ⬝ᵥ y 0 = 1) →
      ∃ (a : Kˣ) (z : Fin 1 → Fin N → K), (a : K) • y ∈ Ω ∧ z ∈ Ω ∧ z 0 ⬝ᵥ ((a : K) • y) 0 = 1)
    (hproper : ∀ Ω₂ : Set (Fin 2 → Fin N → K), IsCompact Ω₂ → ∃ C : Set H, IsCompact C ∧ ∀ Y ∈ Ω₂,
      (∀ a b, hform s L (Y a) (Y b) = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) a b) →
        ∃ c ∈ C, ∀ i, act c (X i) = Y i) :
    ∃ C : Set H, IsCompact C ∧ ∀ h : H, ∃ c ∈ C, ∃ a : Kˣ, act (h * c⁻¹) (X 0) = (a : K) • X 0 := by
  obtain ⟨C₀, hC₀, hprop⟩ := hproper _ ((hΩ.prod hΩ).image (continuous_pair s hsc L Li half))
  refine ⟨Inv.inv '' C₀, hC₀.image continuous_inv, fun h => ?_⟩
  have hG00 : hform s L (act h⁻¹ (X 0)) (act h⁻¹ (X 0)) = 0 := by
    rw [hpres, hX]; rfl
  have hG10 : hform s L (act h⁻¹ (X 1)) (act h⁻¹ (X 0)) = 1 := by
    rw [hpres, hX]; rfl
  have hunim : ∃ z : Fin N → K, z ⬝ᵥ (fun _ : Fin 1 => act h⁻¹ (X 0)) 0 = 1 := by
    refine ⟨(fun i => s (act h⁻¹ (X 1) i)) ᵥ* L, ?_⟩
    rw [← Matrix.dotProduct_mulVec, ← hform_eq]
    exact hG10
  obtain ⟨a, z, hay, hz, hza⟩ := hprim (fun _ => act h⁻¹ (X 0)) hunim
  have hww : hform s L ((a : K) • act h⁻¹ (X 0)) ((a : K) • act h⁻¹ (X 0)) = 0 := by
    rw [hform_smul_left, hform_smul_right, hG00, mul_zero, mul_zero]
  have hza' : z 0 ⬝ᵥ ((a : K) • act h⁻¹ (X 0)) = 1 := hza
  obtain ⟨p1, p2, p3⟩ := partner_spec s L Li half hs hL hLi hh h2 (z 0) ((a : K) • act h⁻¹ (X 0)) hww hza'
  have hmem : (![((a : K) • act h⁻¹ (X 0)), partner s L Li half (z 0) ((a : K) • act h⁻¹ (X 0))] : Fin 2 → Fin N → K)
      ∈ (fun p : (Fin 1 → Fin N → K) × (Fin 1 → Fin N → K) =>
      (![p.1 0, partner s L Li half (p.2 0) (p.1 0)] : Fin 2 → Fin N → K)) '' (Ω ×ˢ Ω) :=
    ⟨((a : K) • (fun _ => act h⁻¹ (X 0)), z), ⟨hay, hz⟩, rfl⟩
  obtain ⟨c, hc, hcY⟩ := hprop _ hmem (gram_pair s L _ _ hww p1 p2 p3)
  refine ⟨c⁻¹, ⟨c, hc, rfl⟩, a, ?_⟩
  have h0 : act c (X 0) = (a : K) • act h⁻¹ (X 0) := hcY 0
  rw [inv_inv, hmul, h0, hsmul, ← hmul, mul_inv_cancel, hone]

end Core

def actV {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (g : HA R σ J) (v : Fin N → R ⊗[F] E) :
    Fin N → R ⊗[F] E :=
  (HA.mat R σ J g : Matrix (Fin N) (Fin N) (R ⊗[F] E)).mulVec v

theorem map_hyp {E K : Type} [Field E] [CommRing K] (φ : E →+* K) :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E).map φ = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem iwasawa : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ C : Set (HA (AF F) σ (hypJ J)), IsCompact C ∧ ∀ h : HA (AF F) σ (hypJ J), ∃ c ∈ C, ∃ a : (AF F ⊗[F] E)ˣ, actW (AF F) σ _ (h * c⁻¹) (eOne _ (M + 1)) = (a : AF F ⊗[F] E) • eOne _ (M + 1) := by
  intro F E _ _ _ _ _ σ hCM M J hJ
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  have hJ' : IsHermND σ (hypJ J) := (GlobalTheory.T.hyperbolic_and_block_one_nondegenerate F E σ hCM M J hJ).1
  obtain ⟨⟨lc, sc, t2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := lc
  haveI := sc
  haveI := t2
  obtain ⟨hTG, -, -, -, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 2) (hypJ J) hJ' (AF F)
  obtain ⟨hTR, -, -, -, hsc, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  haveI := hTG
  haveI := hTR
  obtain ⟨Ω, hΩ, hprim⟩ := GlobalTheory.T.adelic_primitive_vector_compact_rescale F E σ hCM (M + 2)
  have hLh : ∀ i j, sigR (AF F) σ (JR (F := F) (AF F) (hypJ J) j i) = JR (F := F) (AF F) (hypJ J) i j := by
    intro i j
    simp only [JR, Matrix.map_apply, sigR_incl, hJ'.1 i j]
  have hLi : ((hypJ J)⁻¹).map (inclR (F := F) (AF F)) * JR (F := F) (AF F) (hypJ J) = 1 := by
    have hu : IsUnit (hypJ J).det := isUnit_iff_ne_zero.mpr hJ'.2
    have h1 : ((hypJ J)⁻¹ * hypJ J).map (inclR (F := F) (AF F)) = 1 := by
      rw [Matrix.nonsing_inv_mul _ hu]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [← h1, Matrix.map_mul]
    rfl
  have hh : sigR (AF F) σ (inclR (F := F) (AF F) (1 / 2 : E)) = inclR (F := F) (AF F) (1 / 2 : E) := by
    have e : σ (1 / 2 : E) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
    rw [sigR_incl, e]
  have h2 : 2 * inclR (F := F) (AF F) (1 / 2 : E) = 1 := by
    have h3 : inclR (F := F) (AF F) (2 * (1 / 2 : E)) = 1 := by
      rw [mul_one_div_cancel two_ne_zero, map_one]
    rw [map_mul, map_ofNat] at h3
    exact h3
  have hdet : (gramE σ (hypJ J) (frame E M)).det ≠ 0 := by
    rw [gram_frame, Matrix.det_fin_two_of]
    simp
  have hmapG : (gramE σ (hypJ J) (frame E M)).map (inclR (F := F) (AF F)) = !![0, 1; 1, 0] := by
    rw [gram_frame, map_hyp]
  have hX : ∀ a b, hform (sigR (AF F) σ) (JR (F := F) (AF F) (hypJ J)) (ratTup (AF F) (frame E M) a)
      (ratTup (AF F) (frame E M) b) = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (AF F ⊗[F] E)) a b := by
    intro a b
    rw [← hmapG, ← gramR_ratTup]
    rfl
  obtain ⟨C, hC, hCh⟩ := iwa_core (H := HA (AF F) σ (hypJ J)) (sigR (AF F) σ) hsc
    (sigR_invol (AF F) σ hσ) (JR (F := F) (AF F) (hypJ J)) _ hLh hLi _ hh h2
    (actV (AF F) σ (hypJ J))
    (fun g k v => congrFun ((hact 1).2.2.1 g k (fun _ => v)) 0)
    (fun v => congrFun ((hact 1).2.1 (fun _ => v)) 0)
    (fun g a v => Matrix.mulVec_smul _ a v)
    (fun g x y => congrFun (congrFun ((hact 2).2.2.2 g ![x, y]) 0) 1)
    (ratTup (AF F) (frame E M)) hX Ω hΩ hprim
    (fun Ω₂ hΩ₂ => by
      obtain ⟨C, hC, hp⟩ := GlobalTheory.T.gram_orbit_compact_representative F E σ hCM (M + 2) (hypJ J) hJ' 2 (frame E M) hdet Ω₂ hΩ₂
      refine ⟨C, hC, fun Y hY hg => ?_⟩
      obtain ⟨c, hc, hcY⟩ := hp Y hY (by
        rw [hmapG]
        funext a b
        exact hg a b)
      exact ⟨c, hc, fun i => congrFun hcY i⟩)
  refine ⟨C, hC, fun h => ?_⟩
  obtain ⟨c, hc, a, hca⟩ := hCh h
  refine ⟨c, hc, a, funext fun i => ?_⟩
  have e1 := eOne_eq_frame (F := F) (E := E) (AF F) M i
  show actV (AF F) σ (hypJ J) (h * c⁻¹) (eOne _ (M + 1) i) = (a : AF F ⊗[F] E) • eOne _ (M + 1) i
  rw [e1]
  exact hca

end GlobalTheory.CompanionTheory.SW.Iwa
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicUnitaryStabilizerCocompactStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_unitary_stabilizer_cocompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ C : Set (HA (AF F) σ (hypJ J)), IsCompact C ∧ ∀ h : HA (AF F) σ (hypJ J), ∃ c ∈ C, ∃ a : (AF F ⊗[F] E)ˣ, actW (AF F) σ _ (h * c⁻¹) (eOne _ (M + 1)) = (a : AF F ⊗[F] E) • eOne _ (M + 1) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Iwa.iwasawa | exact GlobalTheory.CompanionTheory.SW.Iwa.iwasawa | (intros; apply GlobalTheory.CompanionTheory.SW.Iwa.iwasawa <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicParabolicSiegelSetBound
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicParabolicSiegelSetBound
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.FNu

theorem exists_nu_siegel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVol F E σ M J → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∃ (P : Subgroup (HA (AF F) σ (hypJ J))) (ν : Measure (HA (AF F) σ (hypJ J))) (S : ℤ → Set (HA (AF F) σ (hypJ J))) (ω : Set (AF F ⊗[F] E)ˣ) (Kc : ℝ≥0∞), (∀ h, h ∈ P ↔ ∃ a : (AF F ⊗[F] E)ˣ, actW (AF F) σ _ h (eOne _ (M + 1)) = (a : AF F ⊗[F] E) • eOne _ (M + 1)) ∧ SFinite ν ∧ (∀ p ∈ P, ν.map (fun g => p * g) = ν) ∧ (∀ U ∈ 𝓝 (1 : HA (AF F) σ (hypJ J)), ν U ≠ 0) ∧ IsCompact ω ∧ Kc < ⊤ ∧ (∀ j, MeasurableSet (S j)) ∧ (∀ j : ℤ, ν (S j) ≤ Kc * ENNReal.ofReal (Real.exp (-(2 * Module.finrank ℚ F * (M + 1) * (j : ℝ))))) ∧ (∀ j : ℤ, ∀ p ∈ S j, p ∈ P ∧ ∃ c ∈ ω, actW (AF F) σ _ p (eOne _ (M + 1)) = ((τ (Multiplicative.ofAdd (j : ℝ)) * c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • eOne _ (M + 1)) ∧ ∀ᵐ p ∂ν, ∃ γ ∈ P, HA.mat (AF F) σ (hypJ J) γ ∈ HFin (AF F) σ (hypJ J) ∧ ∃ j, γ * p ∈ S j :=
  CompanionTheory.PlacePermOperatorBicommutantSpan.nu

end GlobalTheory.CompanionTheory.SW.FNu
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicParabolicSiegelSetBoundStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_parabolic_siegel_set_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVol F E σ M J → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∃ (P : Subgroup (HA (AF F) σ (hypJ J))) (ν : Measure (HA (AF F) σ (hypJ J))) (S : ℤ → Set (HA (AF F) σ (hypJ J))) (ω : Set (AF F ⊗[F] E)ˣ) (Kc : ℝ≥0∞), (∀ h, h ∈ P ↔ ∃ a : (AF F ⊗[F] E)ˣ, actW (AF F) σ _ h (eOne _ (M + 1)) = (a : AF F ⊗[F] E) • eOne _ (M + 1)) ∧ SFinite ν ∧ (∀ p ∈ P, ν.map (fun g => p * g) = ν) ∧ (∀ U ∈ 𝓝 (1 : HA (AF F) σ (hypJ J)), ν U ≠ 0) ∧ IsCompact ω ∧ Kc < ⊤ ∧ (∀ j, MeasurableSet (S j)) ∧ (∀ j : ℤ, ν (S j) ≤ Kc * ENNReal.ofReal (Real.exp (-(2 * Module.finrank ℚ F * (M + 1) * (j : ℝ))))) ∧ (∀ j : ℤ, ∀ p ∈ S j, p ∈ P ∧ ∃ c ∈ ω, actW (AF F) σ _ p (eOne _ (M + 1)) = ((τ (Multiplicative.ofAdd (j : ℝ)) * c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • eOne _ (M + 1)) ∧ ∀ᵐ p ∂ν, ∃ γ ∈ P, HA.mat (AF F) σ (hypJ J) γ ∈ HFin (AF F) σ (hypJ J) ∧ ∃ j, γ * p ∈ S j := by
  first | exact @GlobalTheory.CompanionTheory.SW.FNu.exists_nu_siegel | exact GlobalTheory.CompanionTheory.SW.FNu.exists_nu_siegel | (intros; apply GlobalTheory.CompanionTheory.SW.FNu.exists_nu_siegel <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryTransitiveOnIsotropicVectors
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryTransitiveOnIsotropicVectors
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.WittIso

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem hE_eq_sum (x y : Fin M → E) :
    hE σ J x y = ∑ i, ∑ j, σ (x i) * J i j * y j := rfl

theorem hE_add_right (x y z : Fin M → E) : hE σ J x (y + z) = hE σ J x y + hE σ J x z := by
  simp only [hE_eq_sum, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hE_smul_right (c : E) (x y : Fin M → E) : hE σ J x (c • y) = c * hE σ J x y := by
  simp only [hE_eq_sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hE_add_left (x y z : Fin M → E) : hE σ J (x + y) z = hE σ J x z + hE σ J y z := by
  simp only [hE_eq_sum, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hE_smul_left (c : E) (x y : Fin M → E) : hE σ J (c • x) y = σ c * hE σ J x y := by
  simp only [hE_eq_sum, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {σ J}

theorem hE_conj (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → E) :
    σ (hE σ J x y) = hE σ J y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE_eq_sum, map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ i j]
  ring

theorem exists_hE_ne_zero (hdet : J.det ≠ 0) {x : Fin M → E} (hx : x ≠ 0) :
    ∃ w, hE σ J x w ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hu : (fun i => σ (x i)) ᵥ* J = 0 := by
    funext j
    have h := hcon (Pi.single j 1)
    simp only [hE_eq_sum, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    simpa [Matrix.vecMul, dotProduct] using h
  have h0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hu
  apply hx
  funext i
  have := congrFun h0 i
  simpa using this

theorem exists_hyperbolic_partner [CharZero E] (hσ : ∀ a, σ (σ a) = a)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) {x : Fin M → E} (hx : x ≠ 0)
    (hxx : hE σ J x x = 0) :
    ∃ x', hE σ J x x' = 1 ∧ hE σ J x' x = 1 ∧ hE σ J x' x' = 0 := by
  obtain ⟨w₀, hw₀⟩ := exists_hE_ne_zero (σ := σ) hdet hx
  obtain ⟨w, hxw⟩ : ∃ w, hE σ J x w = 1 :=
    ⟨(hE σ J x w₀)⁻¹ • w₀, by rw [hE_smul_right, inv_mul_cancel₀ hw₀]⟩
  have hwx : hE σ J w x = 1 := by
    rw [← hE_conj hσ hJ x w, hxw, map_one]
  obtain ⟨t, ht⟩ : ∃ t, t = hE σ J w w := ⟨_, rfl⟩
  have hσt : σ t = t := by
    rw [ht]; exact hE_conj hσ hJ w w
  obtain ⟨c, hc⟩ : ∃ c : E, c = -t / 2 := ⟨_, rfl⟩
  have hσc : σ c = c := by
    have h2 : σ (2 : E) = 2 := map_ofNat σ 2
    rw [hc, map_div₀, map_neg, hσt, h2]
  have h1 : hE σ J x (w + c • x) = 1 := by
    rw [hE_add_right, hE_smul_right, hxx, hxw]; ring
  have h2 : hE σ J (w + c • x) x = 1 := by
    rw [hE_add_left, hE_smul_left, hxx, hwx]; ring
  refine ⟨w + c • x, h1, h2, ?_⟩
  rw [hE_add_left, hE_smul_left, h1, hE_add_right, hE_smul_right, hwx, ← ht, hσc, hc]
  ring

end Alg

theorem transitive_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
    IsHermND σ J → ∀ x y : Fin M → E, x ≠ 0 → y ≠ 0 → hE σ J x x = 0 → hE σ J y y = 0 →
    ∃ g ∈ UJ (σ : E →+* E) J, (g : Matrix (Fin M) (Fin M) E) *ᵥ x = y := by
  intro F E _ _ _ _ _ σ hCM M J hJ x y hx hy hxx hyy
  have hσ : ∀ a, σ (σ a) = a := by
    intro a
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2 τ, hCM.2.2.2 τ, star_star]
  obtain ⟨x', h1, h2, h3⟩ := exists_hyperbolic_partner hσ hJ.1 hJ.2 hx hxx
  obtain ⟨y', k1, k2, k3⟩ := exists_hyperbolic_partner hσ hJ.1 hJ.2 hy hyy
  have hgram : gramE σ J ![x, x'] = gramE σ J ![y, y'] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [gramE, hxx, hyy, h1, h2, h3, k1, k2, k3]
  have hdet : (gramE σ J ![x, x']).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp [gramE, hxx, h1, h2, h3]
  obtain ⟨g, hg, hgX⟩ := GlobalTheory.T.witt_extension_global F E σ hCM M J hJ 2 ![x, x'] ![y, y'] hgram hdet
  exact ⟨g, hg, by simpa using hgX 0⟩

end GlobalTheory.CompanionTheory.SW.WittIso
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryTransitiveOnIsotropicVectorsStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_transitive_on_isotropic_vectors : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x y : Fin M → E, x ≠ 0 → y ≠ 0 → hE σ J x x = 0 → hE σ J y y = 0 → ∃ g ∈ UJ (σ : E →+* E) J, (g : Matrix (Fin M) (Fin M) E) *ᵥ x = y := by
  first | exact @GlobalTheory.CompanionTheory.SW.WittIso.transitive_isotropic | exact GlobalTheory.CompanionTheory.SW.WittIso.transitive_isotropic | (intros; apply GlobalTheory.CompanionTheory.SW.WittIso.transitive_isotropic <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicFundamentalDomainCover
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.IsoMain

theorem actW_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) (a : R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E) :
    actW R σ J h (a • X) = a • actW R σ J h X := funext fun i => Matrix.mulVec_smul _ a (X i)


set_option maxHeartbeats 1000000 in
theorem integral_isotropic_lines_le_flow_sum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVol F E σ M J → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (μ : Measure (HA (AF F) σ (hypJ J))) (𝓕 : Set (HA (AF F) σ (hypJ J))), IsHaarH F E σ (M + 2) (hypJ J) μ → IsFDH F E σ (M + 2) (hypJ J) μ 𝓕 → ∃ (Y : Set ((Fin 1 → Fin (M + 2) → AF F ⊗[F] E) × (Fin 1 → Fin (M + 2) → AF F ⊗[F] E))) (Kc : ℝ≥0∞), IsCompact Y ∧ Kc < ⊤ ∧ (∀ p ∈ Y, hR (AF F) σ (hypJ J) (p.2 0) (p.1 0) = 1) ∧ ∀ Φ : (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞, Measurable Φ → (∀ (l : E) y, l ≠ 0 → Φ ((inclR (F := F) (AF F) l : AF F ⊗[F] E) • y) = Φ y) → ∀ g : ℤ → ℝ≥0∞, (∀ (j : ℤ), ∀ p ∈ Y, Φ (((τ (Multiplicative.ofAdd (-(j : ℝ))) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • p.1) ≤ g j) → ∀ L : Set (Fin 1 → Fin (M + 2) → E), L ⊆ {X : Fin 1 → Fin (M + 2) → E | X ≠ 0 ∧ gramE σ (hypJ J) X = 0} → (∀ X ∈ L, ∀ X' ∈ L, ∀ l : E, X' = l • X → X' = X) → cntI σ _ μ 𝓕 L Φ ≤ Kc * ∑' j : ℤ, g j * ENNReal.ofReal (Real.exp (-(2 * Module.finrank ℚ F * (M + 1) * (j : ℝ)))) := by
  intro F E _ _ _ _ _ σ hcm M J hJ hfin τ hτ μ 𝓕 hμ h𝓕
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, hsc, -, -, hB, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)
  have := hB 1 (M + 2)
  have hH := (GlobalTheory.CompanionTheory.SW.BlockForm.blockForms_isHermND F E σ hcm M J hJ).1
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hcm _ _ hH (AF F)
  obtain ⟨ac, a1, a2, -⟩ := hact 1
  obtain ⟨-, -, -, ag⟩ := hact 2
  have : μ.IsHaarMeasure := hμ
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  obtain ⟨P, ν, S, ω, Kc, hP, _, hν, hνU, hω, hKc, hSm, hSν, hSP, hScov⟩ := GlobalTheory.T.hyperbolic_parabolic_siegel_set_bound F E σ hcm M J hJ hfin τ hτ
  obtain ⟨C, hC, hiwa⟩ := GlobalTheory.T.hyperbolic_unitary_stabilizer_cocompact F E σ hcm M J hJ
  obtain ⟨C', K, hC', hK, hcover⟩ := GlobalTheory.CompanionTheory.Adelic.integral_fundamentalDomain_le_siegel _ μ P ν hν hνU C hC
  set e₀ : Fin 1 → Fin (M + 2) → AF F ⊗[F] E := eOne _ (M + 1) with he₀
  set e₁ : Fin 1 → Fin (M + 2) → AF F ⊗[F] E := fun _ => Fin.cons 0 (Fin.cons 1 fun _ => 0) with he₁
  have aC : ∀ X, Continuous fun h : HA (AF F) σ (hypJ J) => actW (AF F) σ _ h⁻¹ X := fun X =>
    ac.comp (continuous_inv.prodMk continuous_const)
  let Γ : Subgroup (HA (AF F) σ (hypJ J)) := HFinIn (AF F) σ (hypJ J)
  have : Countable Γ := (GlobalTheory.CompanionTheory.SW.rational_countable_discrete F E σ hcm _ _ hH).1
  have : Countable (Γ ⊓ P : Subgroup _) := (Subgroup.inclusion_injective (inf_le_left : Γ ⊓ P ≤ Γ)).countable
  have hrat : ∀ γ ∈ Γ, ∀ X, ∃ X' : Fin 1 → Fin (M + 2) → E, actW (AF F) σ _ γ (ratTup (AF F) X) = ratTup (AF F) X' := by
    rintro γ ⟨g, -, e⟩ X
    refine ⟨fun a => g.val *ᵥ X a, funext fun a => funext fun i => ?_⟩
    have e' : (HA.mat (AF F) σ _ γ).val = g.val.map (inclR (AF F)) :=
      (congrArg Units.val e).symm
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [actW, actTup, e', ratTup, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  have he : e₀ = ratTup (AF F) (eOne E (M + 1)) := by
    funext a i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [he₀, eOne, ratTup]
  have hline : ∀ γ ∈ Γ ⊓ P, ∃ l : E, l ≠ 0 ∧ actW (AF F) σ _ γ e₀ = (inclR (AF F) l : AF F ⊗[F] E) • e₀ := by
    intro γ hγ
    obtain ⟨a, ha⟩ := (hP γ).1 hγ.2
    obtain ⟨X, hX⟩ := hrat γ hγ.1 (eOne E (M + 1))
    have h1 : (a : AF F ⊗[F] E) = inclR (AF F) (X 0 0) := by
      have := congrFun (congrFun (ha.symm.trans (he ▸ hX)) 0) 0
      simpa [he₀, eOne, ratTup] using this
    refine ⟨X 0 0, fun h0 => ?_, h1 ▸ ha⟩
    have : Nontrivial (AF F ⊗[F] E) := hinj.nontrivial
    exact a.ne_zero (by rw [h1, h0, map_zero])
  refine ⟨(fun p : (AF F ⊗[F] E)ˣ × HA (AF F) σ (hypJ J) =>
      (((p.1⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • actW (AF F) σ _ p.2⁻¹ e₀,
        sigR (AF F) σ (p.1 : AF F ⊗[F] E) • actW (AF F) σ _ p.2⁻¹ e₁)) '' (ω ×ˢ C'), K * Kc,
    (hω.prod hC').image (((Units.continuous_coe_inv.comp continuous_fst).smul ((aC _).comp continuous_snd)).prodMk
      ((hsc.comp (Units.continuous_val.comp continuous_fst)).smul ((aC _).comp continuous_snd))),
    ENNReal.mul_lt_top hK hKc, ?_, fun Φ hΦ hΦl g hg L hL hLu => ?_⟩
  · rintro _ ⟨⟨a, c⟩, -, rfl⟩
    have h1 : hR (AF F) σ (hypJ J) (actW (AF F) σ _ c⁻¹ e₁ 0) (actW (AF F) σ _ c⁻¹ e₀ 0) =
        hR (AF F) σ (hypJ J) (e₁ 0) (e₀ 0) := congrFun (congrFun (ag c⁻¹ ![e₁ 0, e₀ 0]) 0) 1
    have h2 : hR (AF F) σ (hypJ J) (e₁ 0) (e₀ 0) = 1 := by
      simp [hR, hform, he₀, he₁, eOne, JR, hypJ, Fin.sum_univ_succ]
    have hs : ∀ x, sigR (AF F) σ (sigR (AF F) σ x) = x := GlobalTheory.GaussMean.OneVec.sigR_sigR (AF F) hcm
    rw [h2] at h1
    simp only [hR, hform, Pi.smul_apply, smul_eq_mul, map_mul, hs] at h1 ⊢
    rw [← a.mul_inv, ← mul_one (_ * _), ← h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  · have hw : ∀ X : L, ∃ γ ∈ Γ, actW (AF F) σ _ γ⁻¹ e₀ = ratTup (AF F) X.1 := fun X => by
      obtain ⟨g, hg, e⟩ := GlobalTheory.T.unitary_transitive_on_isotropic_vectors F E σ hcm _ _ hH (eOne E (M + 1) 0) (X.1 0)
        (fun h => one_ne_zero (congrFun h 0)) (fun h => (hL X.2).1 (funext fun a => by rw [Subsingleton.elim a 0]; exact h))
        (by simp [hE, hform, eOne, hypJ, Fin.sum_univ_succ]) (congrFun (congrFun (hL X.2).2 0) 0)
      have hm : bc (inclR (AF F)) g ∈ HR (AF F) σ (hypJ J) := by
        have h1 := congrArg (fun A => A.map (inclR (F := F) (AF F))) hg
        simp only [Matrix.map_mul] at h1
        refine Eq.trans ?_ h1
        have e1 : cT (sigR (AF F) σ) (bc (inclR (F := F) (AF F)) g).val = (cT (σ : E →+* E) g.val).map (inclR (AF F)) := by
          ext1 i j; simp [cT, bc, sigR, inclR]
        rw [e1]
        rfl
      refine ⟨(⟨_, hm⟩ : HR (AF F) σ (hypJ J))⁻¹, Γ.inv_mem ⟨g, hg, rfl⟩, ?_⟩
      rw [he]
      funext a i
      rw [Subsingleton.elim a 0, ratTup, ← e]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
      rfl
    choose γ hγ hγe using hw
    let Q := Quotient (QuotientGroup.rightRel ((Γ ⊓ P).subgroupOf Γ))
    have hout : ∀ x : Γ, (x : HA (AF F) σ (hypJ J)) * (((Quotient.mk _ x : Q).out : Γ) : HA (AF F) σ (hypJ J))⁻¹ ∈ Γ ⊓ P :=
      fun x => (QuotientGroup.rightRel_apply (s := (Γ ⊓ P).subgroupOf Γ)).1 (Quotient.mk_out x)
    obtain ⟨𝓕', h𝓕', hunf⟩ := GlobalTheory.CompanionTheory.Adelic.unfold_coset_sum_fundamentalDomain _ μ Γ (Γ ⊓ P) inf_le_left 𝓕 h𝓕 Q (fun q => (q.out : Γ)) (fun q => q.out.2)
      fun x hx => ⟨Quotient.mk _ ⟨x, hx⟩, hout ⟨x, hx⟩, fun q hq =>
        (Quotient.out_eq q).symm.trans (Quotient.sound (QuotientGroup.rightRel_apply.2 hq))⟩
    set f : HA (AF F) σ (hypJ J) → ℝ≥0∞ := fun h => Φ (actW (AF F) σ _ h⁻¹ e₀) with hf
    have hfm : Measurable f := hΦ.comp (aC _).measurable
    have hfi : ∀ x ∈ Γ ⊓ P, ∀ h, f (x * h) = f h := fun x hx h => by
      obtain ⟨l, hl, e⟩ := hline _ ((Γ ⊓ P).inv_mem hx)
      simp only [hf, mul_inv_rev, a2, e, actW_smul, hΦl l _ hl]
    let q : L → Q := fun X => Quotient.mk _ ⟨γ X, hγ X⟩
    have hq : Function.Injective q := fun X X' h => by
      obtain ⟨l, -, e⟩ := hline (γ X * (γ X')⁻¹)
        ((QuotientGroup.rightRel_apply (s := (Γ ⊓ P).subgroupOf Γ)).1 (Quotient.exact h.symm))
      have h1 := congrArg (actW (AF F) σ _ (γ X)⁻¹) e
      rw [← a2, inv_mul_cancel_left, actW_smul, hγe, hγe] at h1
      refine Subtype.ext (hLu _ X.2 _ X'.2 l (funext fun a => funext fun i => ?_)).symm
      apply hinj
      simpa [ratTup] using congrFun (congrFun h1 a) i
    have h1 : cntI σ _ μ 𝓕 L Φ ≤ ∫⁻ h in 𝓕', f h ∂μ := by
      rw [← hunf f hfm]
      refine lintegral_mono fun h => le_trans (le_of_eq (tsum_congr fun X => ?_))
        (ENNReal.tsum_comp_le_tsum_of_injective hq fun y => f ((y.out : Γ) * h))
      have h2 : γ X * (((q X).out : Γ) : HA (AF F) σ (hypJ J))⁻¹ ∈ Γ ⊓ P := hout ⟨γ X, hγ X⟩
      rw [← hfi _ h2, ← mul_assoc, inv_mul_cancel_right, hf]
      simp only [mul_inv_rev, a2, hγe]
    have hgm : ∀ j, Measurable ((S j).indicator fun _ => g j) := fun j => measurable_const.indicator (hSm j)
    refine h1.trans ((hcover (Γ ⊓ P) inf_le_right 𝓕' h𝓕' (⋃ j, S j) (MeasurableSet.iUnion hSm)
      (hScov.mono fun p ⟨x, hx, hx', j, hj⟩ => ⟨x, ⟨hx', hx⟩, Set.mem_iUnion.2 ⟨j, hj⟩⟩) f
      (fun p => ∑' j, (S j).indicator (fun _ => g j) p) hfm (Measurable.tsum hgm) hfi
      (fun x _ => ?_) fun p hp c hc => ?_).trans ?_)
    · obtain ⟨c, hc, a, ha⟩ := hiwa x
      exact ⟨x * c⁻¹, (hP _).2 ⟨a, ha⟩, c, hc, by rw [inv_mul_cancel_right]⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hp
      obtain ⟨-, a, ha, e⟩ := hSP j p hj
      refine le_trans ?_ (ENNReal.le_tsum j)
      rw [Set.indicator_of_mem hj]
      refine le_trans (le_of_eq ?_) (hg j _ ⟨(a, c), ⟨ha, hc⟩, rfl⟩)
      have h2 := congrArg (fun X => (((τ (Multiplicative.ofAdd (j : ℝ)) * a)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) •
        actW (AF F) σ _ p⁻¹ X) e
      simp only [← a2, inv_mul_cancel, a1, actW_smul, smul_smul, Units.inv_mul, one_smul] at h2
      simp only [hf, mul_inv_rev, a2, ← h2, actW_smul, smul_smul, ofAdd_neg, map_inv, Units.val_mul, mul_comm]
    · rw [mul_assoc]
      gcongr
      refine (setLIntegral_le_lintegral _ _).trans ?_
      rw [lintegral_tsum (f := fun j p => (S j).indicator (fun _ => g j) p) fun j => (hgm j).aemeasurable, ← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun j => ?_
      rw [lintegral_indicator_const (hSm j), mul_left_comm]
      gcongr
      exact hSν j

end GlobalTheory.CompanionTheory.SW.IsoMain
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicFundamentalDomainCoverStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_fundamental_domain_cover : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVol F E σ M J → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (μ : Measure (HA (AF F) σ (hypJ J))) (𝓕 : Set (HA (AF F) σ (hypJ J))), IsHaarH F E σ (M + 2) (hypJ J) μ → IsFDH F E σ (M + 2) (hypJ J) μ 𝓕 → ∃ (Y : Set ((Fin 1 → Fin (M + 2) → AF F ⊗[F] E) × (Fin 1 → Fin (M + 2) → AF F ⊗[F] E))) (Kc : ℝ≥0∞), IsCompact Y ∧ Kc < ⊤ ∧ (∀ p ∈ Y, hR (AF F) σ (hypJ J) (p.2 0) (p.1 0) = 1) ∧ ∀ Φ : (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞, Measurable Φ → (∀ (l : E) y, l ≠ 0 → Φ ((inclR (F := F) (AF F) l : AF F ⊗[F] E) • y) = Φ y) → ∀ g : ℤ → ℝ≥0∞, (∀ (j : ℤ), ∀ p ∈ Y, Φ (((τ (Multiplicative.ofAdd (-(j : ℝ))) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • p.1) ≤ g j) → ∀ L : Set (Fin 1 → Fin (M + 2) → E), L ⊆ {X : Fin 1 → Fin (M + 2) → E | X ≠ 0 ∧ gramE σ (hypJ J) X = 0} → (∀ X ∈ L, ∀ X' ∈ L, ∀ l : E, X' = l • X → X' = X) → cntI σ _ μ 𝓕 L Φ ≤ Kc * ∑' j : ℤ, g j * ENNReal.ofReal (Real.exp (-(2 * Module.finrank ℚ F * (M + 1) * (j : ℝ)))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.IsoMain.integral_isotropic_lines_le_flow_sum | exact GlobalTheory.CompanionTheory.SW.IsoMain.integral_isotropic_lines_le_flow_sum | (intros; apply GlobalTheory.CompanionTheory.SW.IsoMain.integral_isotropic_lines_le_flow_sum <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GeomSumIntLe
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem geom_sum_int_le (D M : ℕ) (hD : 0 < D) (hM : 1 ≤ M) (x₀ C : ℝ) :
    ∃ C' : ℝ, ∀ r : ℝ, 0 < r →
      ∑' j : ℤ, (if (j : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((j : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (j : ℝ)))) ≤
        ENNReal.ofReal (C' * r ^ (2 * D * (M + 1))) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 * D * M := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Real.exp (-a) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; exact (Real.exp_pos _).le
  have hq1 : q < 1 := by rw [hq, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have h1q : 0 < 1 - q := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = max C 0 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; exact le_max_right _ _
  have hCK : C ≤ K := by rw [hK]; exact le_max_left _ _
  refine ⟨K * Real.exp (-a * x₀) / (1 - q), fun r hr => ?_⟩
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℤ, n₀ = ⌈x₀ - Real.log r⌉ := ⟨_, rfl⟩
  have hn₀le : x₀ - Real.log r ≤ n₀ := by rw [hn₀]; exact Int.le_ceil _
  have hr2 : (0 : ℝ) < r ^ (2 * D) := by positivity
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = K * r ^ (2 * D) * Real.exp (-a * n₀) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; have := Real.exp_pos (-a * n₀); positivity

  have hsupp : Function.support (fun j : ℤ =>
      (if (j : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((j : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (j : ℝ))))) ⊆
      Set.range (fun n : ℕ => n₀ + (n : ℤ)) := by
    intro j hj
    have hnot : ¬ ((j : ℝ) + Real.log r < x₀) := by
      intro h
      apply hj
      simp [h]
    have hge : n₀ ≤ j := by
      rw [hn₀]
      apply Int.ceil_le.mpr
      linarith [not_lt.mp hnot]
    refine ⟨(j - n₀).toNat, ?_⟩
    have : (((j - n₀).toNat : ℕ) : ℤ) = j - n₀ := Int.toNat_of_nonneg (by omega)
    simp only [this]
    omega
  have hinj : Function.Injective (fun n : ℕ => n₀ + (n : ℤ)) := by
    intro m n h
    simpa using h
  rw [← hinj.tsum_eq hsupp]

  have hterm : ∀ n : ℕ,
      (if (((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (((n₀ + (n : ℤ) : ℤ)) : ℝ)))) ≤
        ENNReal.ofReal (A * q ^ n) := by
    intro n
    split_ifs with h
    · simp
    · rw [← ENNReal.ofReal_mul' (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      have hr' : r ^ (2 * D) = Real.exp (((2 * D : ℕ) : ℝ) * Real.log r) := by
        rw [Real.exp_nat_mul, Real.exp_log hr]
      have hq' : q ^ n = Real.exp ((n : ℝ) * (-a)) := by
        rw [hq, Real.exp_nat_mul]
      have key : Real.exp (2 * D * ((((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r)) *
          Real.exp (-(2 * D * (M + 1) * (((n₀ + (n : ℤ) : ℤ)) : ℝ))) =
          r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n := by
        rw [hr', hq', ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ha]
        congr 1
        push_cast
        ring
      have hpos : 0 ≤ r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n := by
        have := Real.exp_pos (-a * n₀)
        positivity
      calc C * Real.exp (2 * D * ((((n₀ + (n : ℤ) : ℤ)) : ℝ) + Real.log r)) *
            Real.exp (-(2 * D * (M + 1) * (((n₀ + (n : ℤ) : ℤ)) : ℝ)))
          = C * (r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n) := by rw [mul_assoc, key]
        _ ≤ K * (r ^ (2 * D) * Real.exp (-a * n₀) * q ^ n) :=
            mul_le_mul_of_nonneg_right hCK hpos
        _ = A * q ^ n := by rw [hA]; ring
  refine (ENNReal.tsum_le_tsum hterm).trans ?_
  have hsum : Summable (fun n : ℕ => A * q ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left A
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
  apply ENNReal.ofReal_le_ofReal
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]

  have hexp : Real.exp (-a * n₀) ≤ Real.exp (-a * x₀) * r ^ (2 * D * M) := by
    have hr' : r ^ (2 * D * M) = Real.exp (((2 * D * M : ℕ) : ℝ) * Real.log r) := by
      rw [Real.exp_nat_mul, Real.exp_log hr]
    rw [hr', ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hc : (((2 * D * M : ℕ) : ℝ)) = a := by rw [ha]; push_cast; ring
    rw [hc]
    nlinarith [mul_le_mul_of_nonneg_left hn₀le ha0.le]
  have hpow : r ^ (2 * D * (M + 1)) = r ^ (2 * D) * r ^ (2 * D * M) := by
    rw [← pow_add]
    congr 1
    ring
  have hAle : A ≤ K * Real.exp (-a * x₀) * r ^ (2 * D * (M + 1)) := by
    rw [hA, hpow]
    calc K * r ^ (2 * D) * Real.exp (-a * n₀)
        ≤ K * r ^ (2 * D) * (Real.exp (-a * x₀) * r ^ (2 * D * M)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = K * Real.exp (-a * x₀) * (r ^ (2 * D) * r ^ (2 * D * M)) := by ring
  calc A * (1 - q)⁻¹
      ≤ (K * Real.exp (-a * x₀) * r ^ (2 * D * (M + 1))) * (1 - q)⁻¹ :=
        mul_le_mul_of_nonneg_right hAle (inv_nonneg.mpr h1q.le)
    _ = K * Real.exp (-a * x₀) / (1 - q) * r ^ (2 * D * (M + 1)) := by
        rw [div_eq_mul_inv]; ring

theorem geom_sum_int :
    ∀ (D M : ℕ), 0 < D → 1 ≤ M → ∀ (x₀ C : ℝ), ∃ C' : ℝ, ∀ r : ℝ, 0 < r →
      ∑' j : ℤ, (if (j : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((j : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (j : ℝ)))) ≤
        ENNReal.ofReal (C' * r ^ (2 * D * (M + 1))) :=
  fun D M hD hM x₀ C => geom_sum_int_le D M hD hM x₀ C

end GlobalTheory.CompanionTheory.Adelic
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicFiniteVolumeIntegralBound
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.IsoCount

theorem actW_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) (a : R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E) :
    actW R σ J h (a • X) = a • actW R σ J h X := funext fun i => Matrix.mulVec_smul _ a (X i)


set_option maxHeartbeats 600000 in
theorem mean_isotropic_count_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → FinVol F E σ M J → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (μ : Measure (HA (AF F) σ (hypJ J))) (𝓕 : Set (HA (AF F) σ (hypJ J))), IsHaarH F E σ (M + 2) (hypJ J) μ → IsFDH F E σ (M + 2) (hypJ J) μ 𝓕 → ∀ Ω : Set (Fin 1 → Fin (M + 2) → AF F ⊗[F] E), IsCompact Ω → ∃ C : ℝ, ∀ r : ℝ, 0 < r → cntI σ _ μ 𝓕 {X : Fin 1 → Fin (M + 2) → E | X ≠ 0 ∧ gramE σ (hypJ J) X = 0} (fun Y => (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) (((τ (Multiplicative.ofAdd (-Real.log r)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • Y)) ≤ ENNReal.ofReal (C * r ^ (2 * Module.finrank ℚ F * (M + 1))) := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM hfin τ hτ μ 𝓕 hμ h𝓕 Ω hΩ
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, hsc, -, -, hB, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)
  have := hB 1 (M + 2)
  obtain ⟨Y, Kc, hY, hKc, hY1, hmain⟩ := GlobalTheory.T.hyperbolic_fundamental_domain_cover F E σ hcm M J hJ hfin τ hτ μ 𝓕 hμ h𝓕
  have hc : Continuous fun p : ((Fin 1 → Fin (M + 2) → AF F ⊗[F] E) × (Fin 1 → Fin (M + 2) → AF F ⊗[F] E)) ×
      (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) => fun (_ _ : Fin 1) => hR (AF F) σ (hypJ J) (p.1.2 0) (p.2 0) := by
    refine continuous_pi fun _ => continuous_pi fun _ => ?_
    simp only [hR, hform]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((hsc.comp ((continuous_apply_apply 0 i).comp continuous_fst.snd)).mul continuous_const).mul
        ((continuous_apply_apply 0 j).comp continuous_snd)
  obtain ⟨x₀, C, hlat⟩ := GlobalTheory.T.flow_lattice_count_bounded F E σ hcm τ hτ 1 _ ((hY.prod hΩ).image hc)
  obtain ⟨C', hC'⟩ := GlobalTheory.CompanionTheory.Adelic.geom_sum_int (Module.finrank ℚ F) M Module.finrank_pos hM x₀ C
  refine ⟨Kc.toReal * C', fun r hr => ?_⟩
  set t : AF F ⊗[F] E := ((τ (Multiplicative.ofAdd (-Real.log r)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) with ht
  set Z : Set (Fin 1 → Fin (M + 2) → E) := {X | X ≠ 0 ∧ gramE σ (hypJ J) X = 0} with hZ
  let R : Setoid (Fin 1 → Fin (M + 2) → E) := MulAction.orbitRel Eˣ _
  set L : Set (Fin 1 → Fin (M + 2) → E) := {X | X ∈ Z ∧ (Quotient.mk R X).out = X} with hL
  set Φ : (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞ := fun y => ∑' l : Eˣ,
    Ω.indicator (fun _ => (1 : ℝ≥0∞)) (t • (inclR (F := F) (AF F) (l : E) : AF F ⊗[F] E) • y) with hΦ
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv
  have : Countable Eˣ := Units.val_injective.countable
  have hsm : ∀ (l : E) (X : Fin 1 → Fin (M + 2) → E), ratTup (F := F) (AF F) (l • X) =
      (inclR (F := F) (AF F) l : AF F ⊗[F] E) • ratTup (AF F) X := fun l X =>
    funext fun a => funext fun i => map_mul _ _ _
  have h1 : cntI σ _ μ 𝓕 Z (fun Y => Ω.indicator (fun _ => (1 : ℝ≥0∞)) (t • Y)) ≤ cntI σ _ μ 𝓕 L Φ := by
    refine lintegral_mono fun h => ?_
    have hex : ∀ X : Z, ∃ p : L × Eˣ, (p.2 : E) • p.1.1 = X.1 := fun X => by
      obtain ⟨Y₀, l, hl, hY⟩ : ∃ (Y₀ : Fin 1 → Fin (M + 2) → E) (l : Eˣ), (l : E) • Y₀ = X.1 ∧
          (Quotient.mk R Y₀).out = Y₀ := by
        obtain ⟨l, hl⟩ : ∃ l : Eˣ, l • (Quotient.mk R X.1).out = X.1 := (R.symm (Quotient.mk_out X.1) :)
        exact ⟨_, l, hl, congrArg Quotient.out (Quotient.out_eq _)⟩
      refine ⟨(⟨Y₀, ⟨fun h0 => X.2.1 (by rw [← hl, h0, smul_zero]), ?_⟩, hY⟩, l), hl⟩
      have h2 := X.2.2
      rw [← hl] at h2
      funext a b
      have h3 := congrFun (congrFun h2 a) b
      have e : gramE σ (hypJ J) ((l : E) • Y₀) a b = σ l * l * gramE σ (hypJ J) Y₀ a b := by
        simp only [gramE, hE, hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, RingHom.coe_coe]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      rw [e] at h3
      exact (mul_eq_zero.1 h3).resolve_left (mul_ne_zero ((map_ne_zero σ).2 l.ne_zero) l.ne_zero)
    choose p hp using hex
    have hpi : Function.Injective p := fun X X' e => Subtype.ext (by rw [← hp X, e, hp X'])
    simp only [hΦ, ← ENNReal.tsum_prod]
    refine le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hpi _)
    rw [← actW_smul _ _ _ _ (inclR _ _), ← hsm, hp]
  have hm : Measurable Φ := Measurable.tsum fun l =>
    (measurable_const.indicator hΩ.measurableSet).comp ((continuous_const_smul _).const_smul t).measurable
  refine h1.trans ((hmain Φ hm (fun l y hl => ?_) (fun j => if (j : ℝ) + Real.log r < x₀ then 0 else
    ENNReal.ofReal (C * Real.exp (2 * Module.finrank ℚ F * ((j : ℝ) + Real.log r)))) (fun j p hp => ?_) L
    (fun X hX => hX.1) fun X hX X' hX' l e => ?_).trans ?_)
  · simp only [hΦ, smul_smul (inclR _ _), ← map_mul]
    exact (Equiv.mulRight (Units.mk0 l hl)).tsum_eq fun l : Eˣ =>
      Ω.indicator (fun _ => (1 : ℝ≥0∞)) (t • (inclR (F := F) (AF F) (l : E) : AF F ⊗[F] E) • y)
  · have h2 := hlat ((j : ℝ) + Real.log r)
    rw [Nat.cast_one, mul_one] at h2
    refine le_trans ?_ h2
    let ι : Eˣ → {X : Fin 1 → Fin 1 → E // X ≠ 0} := fun l => ⟨fun _ _ => l, fun h => l.ne_zero (congrFun (congrFun h 0) 0)⟩
    have hι : Function.Injective ι := fun l l' e => Units.ext (congrFun (congrFun (congrArg Subtype.val e) 0) 0)
    refine le_trans (ENNReal.tsum_le_tsum fun l => ?_) (ENNReal.tsum_comp_le_tsum_of_injective hι _)
    by_cases hmem : t • (inclR (F := F) (AF F) (l : E) : AF F ⊗[F] E) •
        ((τ (Multiplicative.ofAdd (-(j : ℝ))) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • p.1 ∈ Ω
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem]
      refine ⟨(p, _), ⟨hp, hmem⟩, funext fun a => funext fun b => ?_⟩
      have h3 := hY1 p hp
      simp only [hR, hform, Pi.smul_apply, smul_eq_mul, ratTup, ι, neg_add, ofAdd_add, map_mul, Units.val_mul,
        ← ht] at h3 ⊢
      rw [← mul_one (_ * _ * _), ← h3, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    · rw [Set.indicator_of_notMem hmem]
      exact zero_le
  · have hl : l ≠ 0 := fun h0 => hX'.1.1 (by rw [e, h0, zero_smul])
    rw [← hX'.2, ← hX.2]
    exact congrArg Quotient.out (Quotient.sound (show R X' X from ⟨Units.mk0 l hl, e.symm⟩))
  · rw [mul_assoc Kc.toReal, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hKc.ne]
    exact mul_le_mul_right (hC' r hr) _

end GlobalTheory.CompanionTheory.SW.IsoCount
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicFiniteVolumeIntegralBoundStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_finite_volume_integral_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → FinVol F E σ M J → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (μ : Measure (HA (AF F) σ (hypJ J))) (𝓕 : Set (HA (AF F) σ (hypJ J))), IsHaarH F E σ (M + 2) (hypJ J) μ → IsFDH F E σ (M + 2) (hypJ J) μ 𝓕 → ∀ Ω : Set (Fin 1 → Fin (M + 2) → AF F ⊗[F] E), IsCompact Ω → ∃ C : ℝ, ∀ r : ℝ, 0 < r → cntI σ _ μ 𝓕 {X : Fin 1 → Fin (M + 2) → E | X ≠ 0 ∧ gramE σ (hypJ J) X = 0} (fun Y => (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) (((τ (Multiplicative.ofAdd (-Real.log r)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • Y)) ≤ ENNReal.ofReal (C * r ^ (2 * Module.finrank ℚ F * (M + 1))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.IsoCount.mean_isotropic_count_le | exact GlobalTheory.CompanionTheory.SW.IsoCount.mean_isotropic_count_le | (intros; apply GlobalTheory.CompanionTheory.SW.IsoCount.mean_isotropic_count_le <;> assumption)
end

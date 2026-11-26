module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PstAndWdAtOfIsRegAlg
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesOverSplitPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralizerRegularLeviCommutativeNoncompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedOrbitalIntegralTypeTestVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDeepestFiltrationStepEqRational
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridNuUnitTrivial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairDecomposition
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
noncomputable section

namespace GlobalTheory.UnipMass.StdMat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_inclR_eq (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (AF F) e) = inclR (AF F) (σ e) := by
  simp [cA, inclR]

theorem cA_cA_eq (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, hσ]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem incM_mulVec_incV_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) (v : Fin n → E) :
    incM F A *ᵥ incV F v = incV F (A *ᵥ v) := by
  ext i; simp [incM, incV, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem cA_incV_eq (σ : E →ₐ[F] E) {n : ℕ} (x : Fin n → E) :
    (fun i => cA σ (incV F x i)) = incV F (fun i => σ (x i)) := by
  funext i; simp [incV, cA_inclR_eq]

theorem hA_incV_eq (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) :
    hA σ J (incV F a) (incV F b) = inclR (AF F) (form σ J a b) := by
  rw [hA, cA_incV_eq, incM_mulVec_incV_eq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [form, incV, dotProduct, map_sum, map_mul]

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem hA_add_l (v v' w : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : hA σ J (v + v') w = hA σ J v w + hA σ J v' w := by
  simp [hA, add_dotProduct]

theorem hA_smul_l (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (v w : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : hA σ J (a • v) w = a * hA σ J v w := by
  simp [hA, smul_dotProduct]

theorem hA_add_r (v w w' : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : hA σ J v (w + w') = hA σ J v w + hA σ J v w' := by
  have : (fun i => cA σ ((w + w') i)) = (fun i => cA σ (w i)) + (fun i => cA σ (w' i)) := by
    funext i; simp
  rw [hA, this, Matrix.mulVec_add, dotProduct_add]; rfl

theorem hA_smul_r (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (v w : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : hA σ J v (a • w) = cA σ a * hA σ J v w := by
  have : (fun i => cA σ ((a • w) i)) = cA σ a • (fun i => cA σ (w i)) := by
    funext i; simp
  rw [hA, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]; rfl

theorem hA_skew_eq (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    hA σ J w v = -cA σ (hA σ J v w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hA, dotProduct, Matrix.mulVec, incM, Matrix.map_apply, map_sum, map_mul, cA_cA_eq σ hσ, cA_inclR_eq,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; simp only [map_neg]; ring

end GlobalTheory.UnipMass.StdMat

namespace GlobalTheory.UnipMass.StdMat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hA_mat_eq (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (v w : Fin n → AE F E) :
    hA σ J (mat g *ᵥ v) (mat g *ᵥ w) = hA σ J v w := by
  have hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  have hc : (fun i => cA σ ((mat g *ᵥ w) i)) = (mat g).map (cA σ) *ᵥ fun i => cA σ (w i) := by
    funext i; exact RingHom.map_mulVec (cA σ).toRingHom (mat g) w i
  rw [hA, hA, hc, ← Matrix.vecMul_transpose (mat g) v, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec]
  rw [← Matrix.mul_assoc, hg]

theorem hA_ι_incV_eq (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (ι : Matrix (Fin d) (Fin d₁) E)
    (w : Fin d → E) (h : ∀ u, form σ J (ι *ᵥ u) w = 0) (z : Fin d₁ → AE F E) :
    hA σ J (incM F ι *ᵥ z) (incV F w) = 0 := by
  have hq : ιᵀ *ᵥ (J *ᵥ fun i => σ (w i)) = 0 := by
    funext k
    have := h (Pi.single k 1)
    rw [form, Matrix.mulVec_single_one] at this
    exact this
  rw [hA, cA_incV_eq, incM_mulVec_incV_eq, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
    show (incM F ι)ᵀ = incM F ιᵀ from rfl, incM_mulVec_incV_eq, hq]
  have : incV F (0 : Fin d₁ → E) = 0 := by funext i; simp [incV]
  rw [this, dotProduct_zero]

theorem incV_add_eq {n : ℕ} (a b : Fin n → E) : incV F (a + b) = incV F a + incV F b := by
  funext i; simp [incV]

theorem incV_smul_eq {n : ℕ} (s : E) (a : Fin n → E) : incV F (s • a) = inclR (F := F) (AF F) s • incV F a := by
  funext i; simp [incV]

theorem decomp_eq {d d₁ : ℕ} (x y : Fin d → E) (ι : Matrix (Fin d) (Fin d₁) E)
    (hdec : ∀ v : Fin d → E, ∃ (s t : E) (u : Fin d₁ → E), v = s • x + ι *ᵥ u + t • y) (v : Fin d → AE F E) :
    ∃ (s t : AE F E) (z : Fin d₁ → AE F E), v = s • incV F x + incM F ι *ᵥ z + t • incV F y := by
  choose s t u hu using fun i => hdec (Pi.single i 1)
  have he : ∀ i, incV F (Pi.single i (1 : E)) =
      inclR (F := F) (AF F) (s i) • incV F x + incM F ι *ᵥ incV F (u i) + inclR (F := F) (AF F) (t i) • incV F y := by
    intro i
    rw [hu i, incV_add_eq, incV_add_eq, incV_smul_eq, incV_smul_eq, incM_mulVec_incV_eq]
  have hv : v = ∑ i, v i • incV F (Pi.single i (1 : E)) := by
    funext k; simp [incV, Finset.sum_apply, Pi.single_apply]
  refine ⟨∑ i, v i * inclR (F := F) (AF F) (s i), ∑ i, v i * inclR (F := F) (AF F) (t i), ∑ i, v i • incV F (u i), ?_⟩
  calc v = ∑ i, v i • incV F (Pi.single i (1 : E)) := hv
    _ = _ := by
      simp only [he, smul_add, smul_smul, Finset.sum_add_distrib, Finset.sum_smul, Matrix.mulVec_sum, Matrix.mulVec_smul]

theorem mem_unip_std (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) (g : UA σ W.J)
    (hg : g ∈ unip σ W H') :
    mat g *ᵥ incV F H'.x = incV F H'.x ∧
      ∀ z, ∃ a : AE F E, mat g *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x := by
  unfold unip at hg
  induction hg using Subgroup.closure_induction with
  | mem u hu => exact hu
  | one => exact ⟨by simp [mat], fun z => ⟨0, by simp [mat]⟩⟩
  | mul u v _ _ hu hv =>
    have hm : mat (u * v) = mat u * mat v := rfl
    refine ⟨?_, fun z => ?_⟩
    · rw [hm, ← Matrix.mulVec_mulVec, hv.1, hu.1]
    · obtain ⟨a, ha⟩ := hv.2 z
      obtain ⟨b, hb⟩ := hu.2 z
      refine ⟨b + a, ?_⟩
      rw [hm, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, hb, hu.1, add_smul]
      abel
  | inv u _ hu =>
    have h1 : mat u⁻¹ * mat u = 1 := by
      rw [show mat u⁻¹ * mat u = mat (u⁻¹ * u) from rfl, inv_mul_cancel]; rfl
    have hx : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x := by
      conv_lhs => rw [← hu.1]
      rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    refine ⟨hx, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu.2 z
    have key : mat u⁻¹ *ᵥ (incM F H'.ι *ᵥ z + a • incV F H'.x) = incM F H'.ι *ᵥ z := by
      rw [← ha, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hx] at key
    refine ⟨-a, ?_⟩
    rw [eq_sub_of_add_eq key, neg_smul, sub_eq_add_neg]

end GlobalTheory.UnipMass.StdMat

namespace GlobalTheory.UnipMass.StdMat

theorem unip_eq_nmat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁), (∀ i j, σ (W.J j i) = -W.J i j) → form σ W.J H'.x H'.x = 0 → form σ W.J H'.y H'.y = 0 → form σ W.J H'.x H'.y = 1 → (∀ u, form σ W.J (H'.ι *ᵥ u) H'.x = 0 ∧ form σ W.J (H'.ι *ᵥ u) H'.y = 0) → (∀ v : Fin d → E, ∃ (s t : E) (u : Fin d₁ → E), v = s • H'.x + H'.ι *ᵥ u + t • H'.y) → ∀ g ∈ unip σ W H', ∃ (b : Fin d₁ → AE F E) (c : AE F E), c - cA σ c = -hA σ W.J (incM F H'.ι *ᵥ b) (incM F H'.ι *ᵥ b) ∧ mat g = nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ b) c := by
  intro F E _ _ _ _ _ σ hσ d d₁ W H' hJ hxx hyy hxy horth hdec g hg
  have hXX : hA σ W.J (incV F H'.x) (incV F H'.x) = 0 := by rw [hA_incV_eq, hxx, map_zero]
  have hYY : hA σ W.J (incV F H'.y) (incV F H'.y) = 0 := by rw [hA_incV_eq, hyy, map_zero]
  have hXY : hA σ W.J (incV F H'.x) (incV F H'.y) = 1 := by rw [hA_incV_eq, hxy, map_one]
  have hYX : hA σ W.J (incV F H'.y) (incV F H'.x) = -1 := by
    rw [hA_skew_eq σ W.J hσ hJ, hXY, map_one]
  have hιX : ∀ z, hA σ W.J (incM F H'.ι *ᵥ z) (incV F H'.x) = 0 :=
    hA_ι_incV_eq σ W.J H'.ι H'.x (fun u => (horth u).1)
  have hιY : ∀ z, hA σ W.J (incM F H'.ι *ᵥ z) (incV F H'.y) = 0 :=
    hA_ι_incV_eq σ W.J H'.ι H'.y (fun u => (horth u).2)
  have hXι : ∀ z, hA σ W.J (incV F H'.x) (incM F H'.ι *ᵥ z) = 0 := fun z => by
    rw [hA_skew_eq σ W.J hσ hJ, hιX, map_zero, neg_zero]
  have hYι : ∀ z, hA σ W.J (incV F H'.y) (incM F H'.ι *ᵥ z) = 0 := fun z => by
    rw [hA_skew_eq σ W.J hσ hJ, hιY, map_zero, neg_zero]
  obtain ⟨hgX, hgι⟩ := mem_unip_std σ W H' g hg
  have inv : ∀ v w, hA σ W.J (mat g *ᵥ v) (mat g *ᵥ w) = hA σ W.J v w := hA_mat_eq σ g
  have dec := decomp_eq (F := F) H'.x H'.y H'.ι hdec
  obtain ⟨α, γ, β, hgY⟩ := dec (mat g *ᵥ incV F H'.y)
  have hγ : γ = 1 := by
    have h := inv (incV F H'.y) (incV F H'.x)
    rw [hgX, hgY] at h
    simp only [hA_add_l, hA_smul_l, hXX, hιX, hYX] at h
    linear_combination -h
  subst hγ
  have ha : ∀ z (a : AE F E), mat g *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x →
      a = -hA σ W.J (incM F H'.ι *ᵥ z) (incM F H'.ι *ᵥ β) := by
    intro z a h
    have h2 := inv (incM F H'.ι *ᵥ z) (incV F H'.y)
    rw [h, hgY] at h2
    simp only [hA_add_l, hA_add_r, hA_smul_l, hA_smul_r, hXX, hXY, hιX, hιY, hXι, mul_zero, mul_one, zero_add,
      add_zero, one_smul] at h2
    linear_combination h2
  have hα : α - cA σ α = -hA σ W.J (incM F H'.ι *ᵥ β) (incM F H'.ι *ᵥ β) := by
    have h3 := inv (incV F H'.y) (incV F H'.y)
    rw [hgY] at h3
    simp only [hA_add_l, hA_add_r, hA_smul_l, hA_smul_r, hXX, hXY, hYX, hYY, hιX, hιY, hXι, hYι, mul_zero, mul_one,
      zero_add, add_zero, one_smul, one_mul] at h3
    linear_combination h3
  refine ⟨β, α, hα, ?_⟩
  have key : ∀ v, mat g *ᵥ v = nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ β) α *ᵥ v := by
    intro v
    obtain ⟨s, t, z, rfl⟩ := dec v
    obtain ⟨a, hz⟩ := hgι z
    have ha' := ha z a hz
    rw [nmat_mulVec]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hgX, hz, hgY, hA_add_l, hA_smul_l, hXX, hιX, hYX, hXι, hYι,
      mul_zero, zero_add, add_zero, one_smul]
    rw [ha']
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  ext i j
  have h4 := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using h4

end GlobalTheory.UnipMass.StdMat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairDecompositionStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_pair_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁), (∀ i j, σ (W.J j i) = -W.J i j) → form σ W.J H'.x H'.x = 0 → form σ W.J H'.y H'.y = 0 → form σ W.J H'.x H'.y = 1 → (∀ u, form σ W.J (H'.ι *ᵥ u) H'.x = 0 ∧ form σ W.J (H'.ι *ᵥ u) H'.y = 0) → (∀ v : Fin d → E, ∃ (s t : E) (u : Fin d₁ → E), v = s • H'.x + H'.ι *ᵥ u + t • H'.y) → ∀ g ∈ unip σ W H', ∃ (b : Fin d₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), c - cA σ c = -hA σ W.J (incM F H'.ι *ᵥ b) (incM F H'.ι *ᵥ b) ∧ mat g = nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ b) c := by
  first | exact @GlobalTheory.UnipMass.StdMat.unip_eq_nmat | exact GlobalTheory.UnipMass.StdMat.unip_eq_nmat | (intros; apply GlobalTheory.UnipMass.StdMat.unip_eq_nmat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LargePlaceNotDvdDifferent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LargePlaceNotDvdDifferent
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop

namespace GlobalTheory.DiffSOne

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem not_dvd_diff_of_split (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {p : ℕ} (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 L)).ncard = Module.finrank ℚ L)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 K) := by
  have h' : ({w : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ w.asIdeal}).ncard = Module.finrank ℚ L := by
    rw [← h, Formalism.L2.SG.Pf.TypedLoc.primesOver_eq L hp]
    exact (Set.ncard_image_of_injective _ fun v w hvw => HeightOneSpectrum.ext hvw).symm
  obtain ⟨he, -⟩ := Formalism.L2.SG.Pf.TypedLoc.tower_ef K L hp h' v hv
  have hvq : v.asIdeal ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
    rw [Formalism.L2.SG.Pf.TypedLoc.primesOver_eq K hp]; exact ⟨v, hv, rfl⟩
  have : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := hvq.2
  have : v.asIdeal.IsPrime := v.isPrime
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp)] at he
  rw [not_dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain]
  exact he

theorem not_dvd_differentIdeal : ∀ {D : D7} (large₂ : SizeData₂ D), Rec large₂ → ∀ v : HeightOneSpectrum (𝓞 D.host.F), v ∈ S1 D →
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  intro D large₂ hR v hv
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hR.size
  rcases (S1_mem_OmF D).1 hv with h | h | h | h
  · exact Formalism.L2.SG.Pf.FibD.not_dvd_diff v 0 h
  · exact Formalism.L2.SG.Pf.FibD.not_dvd_diff v 1 h
  · exact not_dvd_diff_of_split D.host.F D.host.E D.host.pde_prime Pm.pde_split.1 v h
  · exact not_dvd_diff_of_split D.host.F D.host.E D.host.pde'_prime Pm.pde_split.2 v h

end GlobalTheory.DiffSOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LargePlaceNotDvdDifferentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.large_place_not_dvd_different : ∀ {D : D7} (large₂ : SizeData₂ D), Rec large₂ → ∀ v : HeightOneSpectrum (𝓞 D.host.F), v ∈ S1 D → ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  first | exact @GlobalTheory.DiffSOne.not_dvd_differentIdeal | exact GlobalTheory.DiffSOne.not_dvd_differentIdeal | (intros; apply GlobalTheory.DiffSOne.not_dvd_differentIdeal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContraMapInjective
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CosocleOfContra

open ProjLine

section General

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ G V}

theorem isIrreducible_quot {S : Subrepresentation π} (hS : IsCoatom S) : (quot S).IsIrreducible := by
  have h1 : S.toSubmodule ≠ ⊤ := fun e => hS.1 (Subrepresentation.toSubmodule_injective e)
  have := Submodule.Quotient.nontrivial_iff.2 h1
  have : Nontrivial (Subrepresentation (quot S)) := ⟨⊥, ⊤, fun e =>
    bot_ne_top (α := Submodule ℂ (V ⧸ S.toSubmodule)) (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun T => ?_⟩
  let T' : Subrepresentation π := ⟨T.toSubmodule.comap S.toSubmodule.mkQ, fun g v hv => T.apply_mem_toSubmodule g hv⟩
  have hle : S ≤ T' := fun v hv => by
    show S.toSubmodule.mkQ v ∈ T.toSubmodule
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hv]
    exact T.toSubmodule.zero_mem
  rcases hS.le_iff.1 hle with e | e
  · right
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨v, rfl⟩ := S.toSubmodule.mkQ_surjective y
    have : v ∈ T' := e ▸ trivial
    exact this
  · left
    refine eq_bot_iff.2 fun y hy => ?_
    obtain ⟨v, rfl⟩ := S.toSubmodule.mkQ_surjective y
    have : v ∈ T' := hy
    rw [e] at this
    exact (Submodule.Quotient.mk_eq_zero _).2 this

end General

section GeneralLinearIntegers

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}

theorem isSmooth_quot (hπ : IsSmooth π) (S : Subrepresentation π) : IsSmooth (quot S) :=
  (IsSubquotient.of_surjective (quotMk S) S.toSubmodule.mkQ_surjective).isSmooth hπ

end GeneralLinearIntegers

end GlobalTheory.CosocleOfContra
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardPrincipalCongruenceTransversalLeAbsNormPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardPrincipalCongruenceTransversalLeAbsNormPow
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

theorem GlobalTheory.card_congRep_le : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (a : ℕ) (R : Finset (GA D a)), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) → R.card ≤ Ideal.absNorm 𝔪 ^ (a ^ 2) := by
  intro D 𝔪 h𝔪 a R hR huniq
  classical
  obtain ⟨hne, hle⟩ := GlobalTheory.congLev_relIndex_le D 𝔪 h𝔪 a
  let Q := intG D a ⧸ (congLev D 𝔪 a).subgroupOf (intG D a)
  haveI : Finite Q := Nat.finite_of_card_ne_zero hne
  let f : R → Q := fun r => QuotientGroup.mk (⟨(r : GA D a), hR r r.2⟩ : intG D a)
  have hf : Function.Injective f := by
    rintro ⟨r, hr⟩ ⟨r', hr'⟩ h
    have h1 := QuotientGroup.eq.1 h
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : r⁻¹ * r' ∈ congLev D 𝔪 a := h1
    have h3 := ((mem_congLev_iff D 𝔪 a _).1 h2).2
    have h4 : CongOne D 𝔪 (r'⁻¹ * r') := by
      rw [inv_mul_cancel]; exact congOne_one 𝔪 a
    obtain ⟨s, -, hs⟩ := huniq r' (hR r' hr')
    have e1 := hs r ⟨hr, h3⟩
    have e2 := hs r' ⟨hr', h4⟩
    exact Subtype.ext (e1.trans e2.symm)
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hc
  calc R.card ≤ Nat.card Q := hc
    _ = (congLev D 𝔪 a).relIndex (intG D a) := rfl
    _ ≤ _ := hle

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardPrincipalCongruenceTransversalLeAbsNormPowStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_principalCongruence_transversal_le_absNorm_pow : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (a : ℕ) (R : Finset (GA D a)), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) → R.card ≤ Ideal.absNorm 𝔪 ^ (a ^ 2) := by
  first | exact @GlobalTheory.card_congRep_le | exact GlobalTheory.card_congRep_le | (intros; apply GlobalTheory.card_congRep_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalDefiniteSpaceH
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem signs_pos_of_frame_gram_posdef {r : ℕ} (ε : Fin r → Bool) (fr G : Matrix (Fin r) (Fin r) ℂ)
    (h : fr.conjTranspose * Formalism.REAL.Jm ε * fr = G) (hs : Formalism.UG.HasSignature G r 0) :
    ∀ i, ε i = true := by
  obtain ⟨e, P, hP⟩ := hs
  have hcT : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ) =
      (P : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ).conjTranspose := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  have hJ0 : Formalism.UG.Jpq r 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  rw [hcT, hJ0] at hP
  set P' : Matrix (Fin r) (Fin r) ℂ := (P : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ).submatrix e e with hP'
  have h1 : P'.conjTranspose * G * P' = 1 := by
    have := congrArg (fun A : Matrix (Fin r ⊕ Fin 0) (Fin r ⊕ Fin 0) ℂ => A.submatrix e e) hP
    simp only [Matrix.reindex_apply] at this
    rw [← Matrix.submatrix_mul_equiv _ _ _ e _, ← Matrix.submatrix_mul_equiv _ _ _ e _] at this
    simpa [Matrix.submatrix_submatrix, Matrix.conjTranspose_submatrix, hP'] using this
  set Q := fr * P' with hQ
  have h2 : (Q.conjTranspose * Formalism.REAL.Jm ε) * Q = 1 := by
    rw [← h1, ← h]; simp only [hQ, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have h3 : Q * (Q.conjTranspose * Formalism.REAL.Jm ε) = 1 := mul_eq_one_comm.mp h2
  have h4 : Q * Q.conjTranspose = Formalism.REAL.Jm ε := by
    have := congrArg (· * Formalism.REAL.Jm ε) h3
    simpa [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self] using this
  intro i
  by_contra hi
  have hi' : ε i = false := by simpa using hi
  have h5 := congrFun (congrFun h4 i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Formalism.REAL.Jm, Matrix.diagonal_apply_eq, hi'] at h5
  have h6 := congrArg Complex.re h5
  simp only [Complex.re_sum, Bool.false_eq_true, if_false, Complex.neg_re, Complex.one_re] at h6
  have h7 : ∀ k, 0 ≤ (Q i k * star (Q i k)).re := by
    intro k
    rw [Complex.star_def, Complex.mul_conj]
    simp [Complex.normSq_nonneg]
  have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => h7 k)
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKUConjOfComp
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.IntRead

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def thAt (u : Pl E) : GLw n (cPl E u) →* GLw n u :=
  (MulAut.conj (PhiU n (u.adicCompletion E))).toMonoidHom.comp
    ((invT n (u.adicCompletion E)).comp (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv u)))

theorem thAt_apply (u : Pl E) (h : GLw n (cPl E u)) (i j : Fin n) :
    (thAt u h).val i j =
      (-1) ^ ((i : ℕ) + j) * conjLoc (IsCMField.complexConj E).toRingEquiv u ((h⁻¹).val j.rev i.rev) :=
  GlobalTheory.ThetaPull.phi_mul_apply _ i j

theorem map_thF (u : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    GeneralLinearGroup.map (pLoc E u) (thF E n g) = thAt u (GeneralLinearGroup.map (pLoc E (cPl E u)) g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h := GlobalTheory.ThetaPull.thetaGL_apply (a := n) (conjFin (IsCMField.complexConj E).toRingEquiv) g i j
  change pLoc E u ((thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv) g).val i j) = _
  rw [h, thAt_apply, map_mul, map_pow, map_neg, map_one, pLoc_conjFin]
  rfl

theorem mem_KGL_of_thAt (u : Pl E) (k : GLw n (cPl E u)) (hk : thAt u k ∈ GlobalTheory.LFun.KGL u (n := n)) :
    k ∈ GlobalTheory.LFun.KGL (cPl E u) (n := n) := by
  have hv : ∀ (h : GLw n (cPl E u)) (i j : Fin n),
      Valued.v ((thAt u h).val i j) = Valued.v ((h⁻¹).val j.rev i.rev) := by
    intro h i j
    rw [thAt_apply, Valuation.map_mul, Valuation.map_pow, Valuation.map_neg, Valuation.map_one, one_pow, one_mul]
    exact (conjLoc_spec (IsCMField.complexConj E).toRingEquiv u).2.2 _
  rw [GlobLev.mem_KGL_iff_val] at hk ⊢
  obtain ⟨h1, h2⟩ := hk
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have := h2 j.rev i.rev
    rw [← map_inv, hv, inv_inv, Fin.rev_rev, Fin.rev_rev] at this
    exact this
  · have := h1 j.rev i.rev
    rwa [hv, Fin.rev_rev, Fin.rev_rev] at this

end GlobalTheory.EulerTw.IntRead

namespace GlobalTheory.EulerTw.IntRead

open GlobalTheory.EulerTw

end GlobalTheory.EulerTw.IntRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularSemisimpleUnitaryDataOfRegular
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularSemisimpleUnitaryDataOfRegular
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.ConjLevi.RegularData

theorem isRegular_of_isRegSS : ∀ {D : D7} {V : HSp D} (γ : GF V), IsRegSS γ.1.1 → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsRegular D.sp.cm.sig V.gram γ.1 := by
  intro D V γ h
  have hHN := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V
  refine ⟨⟨?_, D.sp.cm.deg2, ?_, ?_⟩, ?_, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V, γ.2, h⟩
  · haveI : Module.Finite (↥D.host.F) D.host.E :=
      Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
    exact ⟨Algebra.FormallyEtale.of_isSeparable _ _,
      Algebra.FinitePresentation.of_finiteType.1 inferInstance⟩
  · intro e
    simp [Formalism.BasicNotions.CMData.sig]
  · by_contra hne
    push_neg at hne
    have htop : (⊥ : Subalgebra (↥D.host.F) D.host.E) = ⊤ := by
      refine eq_top_iff.2 (fun e _ => ?_)
      rw [Algebra.mem_bot]
      have := (D.sp.cm.fixed e).1 (hne e)
      simpa using this
    have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 htop
    rw [D.sp.cm.deg2] at h1
    norm_num at h1
  · ext i j
    simpa [Formalism.UG.IsHerm, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] using hHN.1 i j

end GlobalTheory.ConjLevi.RegularData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularSemisimpleUnitaryDataOfRegularStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularSemisimpleUnitaryData_of_regular : ∀ {D : D7} {V : HSp D} (γ : GF V), IsRegSS γ.1.1 → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsRegular D.sp.cm.sig V.gram γ.1 := by
  first | exact @GlobalTheory.ConjLevi.RegularData.isRegular_of_isRegSS | exact GlobalTheory.ConjLevi.RegularData.isRegular_of_isRegSS | (intros; apply GlobalTheory.ConjLevi.RegularData.isRegular_of_isRegSS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormEqOwnRealLieSmoothing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormEqOwnRealLieSmoothing
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.AutGrowth.SelfSmoothing

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def smoothings (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a) : Submodule ℂ (GA E a → ℂ) where
  carrier := {f | ∃ β, IsTest (invSet E a) β ∧ smoothing ν β φ.1 = f}
  zero_mem' := ⟨0, isTest_zero, funext fun x => by simp [smoothing]⟩
  add_mem' := by
    rintro _ _ ⟨β, hβ, rfl⟩ ⟨γ, hγ, rfl⟩
    refine ⟨β + γ, hβ.add hγ, funext fun x => ?_⟩
    refine Eq.trans ?_ (integral_add (hβ.integrable_mul ν isOpen_invSet (φ.2 x).continuousOn)
      (hγ.integrable_mul ν isOpen_invSet (φ.2 x).continuousOn))
    simp only [smoothing, Pi.add_apply, add_mul]
  smul_mem' := by
    rintro c _ ⟨β, hβ, rfl⟩
    refine ⟨fun y => β y * c, hβ.mul contDiff_const, funext fun x => ?_⟩
    refine Eq.trans ?_ (integral_const_mul c _)
    simp only [smoothing]
    congr 1
    funext y
    ring

theorem exists_smoothing_eq_self : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a), IsAutForm φ →
    ∃ α : Lie E a → ℂ, IsTest (invSet E a) α ∧ smoothing ν α φ.1 = φ.1 := by
  intro hP E _ _ _ a ν _ φ hφ
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.T.exists_conjInvariant_approxIdentity_realLieSmoothing E a ν
  obtain ⟨V, hVf, -, hV⟩ := GlobalTheory.T.exists_finiteDimensional_space_automorphic_smoothings hP E a ν φ hφ
  let V₀ : Submodule ℂ (GA E a → ℂ) := V.map (Sm E a).subtype
  let V' : Submodule ℂ (GA E a → ℂ) := smoothings ν φ ⊓ V₀
  have hf : FiniteDimensional ℂ V' := Submodule.finiteDimensional_of_le (S₂ := V₀) inf_le_right
  have hc : IsClosed (V' : Set (GA E a → ℂ)) := Submodule.closed_of_finiteDimensional V'
  have hmem : ∀ n, smoothing ν (α n) φ.1 ∈ V' := fun n => by
    obtain ⟨h, hv⟩ := hV (α n) (hα n).1 (hα n).2
    exact ⟨⟨α n, (hα n).1, rfl⟩, ⟨_, hv, rfl⟩⟩
  have hφ' : φ.1 ∈ V' :=
    hc.mem_of_tendsto (tendsto_pi_nhds.2 fun g => hlim φ.1 φ.2 g) (Eventually.of_forall hmem)
  exact hφ'.1

end GlobalTheory.AutGrowth.SelfSmoothing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormEqOwnRealLieSmoothingStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicForm_eq_own_realLieSmoothing : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a), IsAutForm φ → ∃ α : Lie E a → ℂ, IsTest (invSet E a) α ∧ smoothing ν α φ.1 = φ.1 := by
  first | exact @GlobalTheory.AutGrowth.SelfSmoothing.exists_smoothing_eq_self | exact GlobalTheory.AutGrowth.SelfSmoothing.exists_smoothing_eq_self | (intros; apply GlobalTheory.AutGrowth.SelfSmoothing.exists_smoothing_eq_self <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameConjMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameConjMap
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

noncomputable section

open scoped Classical

namespace GlobalTheory.DoublingEv.ConjTame

def conjSch {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] :
    SchwartzMap D ℂ →SL[starRingEnd ℂ] SchwartzMap D ℂ :=
  SchwartzMap.mkCLM (𝕜 := ℂ) (𝕜' := ℂ) (σ := starRingEnd ℂ) (fun f x => star (f x))
    (fun f g x => by simp [star_add])
    (fun a f x => by simp [smul_eq_mul, mul_comm])
    (fun f => Complex.conjCLE.contDiff.comp (f.smooth ⊤))
    (fun n => ⟨{n}, 1, zero_le_one, fun f x => by
      have h : (fun x => star (f x)) = (Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ) ∘ f := rfl
      rw [h, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, Finset.sup_singleton, one_mul]
      exact SchwartzMap.le_seminorm ℂ n.1 n.2 f x⟩)

theorem conjSch_apply {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] (f : SchwartzMap D ℂ) (x : D) :
    conjSch f x = star (f x) := rfl

theorem star_mem_SB {X : Type} [TopologicalSpace X] {g : X → ℂ} (hg : g ∈ SB X) : star g ∈ SB X :=
  ⟨hg.1.comp star, hg.2.comp_left (g := star) (star_zero ℂ)⟩

variable {F : Type} [Field F] [NumberField F]

theorem star_pureA {κ : Type} [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    star (pureA F (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) g) = pureA F (conjSch f : _ → ℂ) (star g) := by
  funext x
  simp [pureA, conjSch_apply, star_mul', Pi.star_apply]

end GlobalTheory.DoublingEv.ConjTame


open GlobalTheory.DoublingEv.ConjTame in
theorem GlobalTheory.DoublingEv.isTame_conjMap : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)), IsTame F T → IsTame F (conjMap T) := by
  intro F _ _ κ κ' _ _ T hT g hg
  obtain ⟨ι, _, P, g', hg', hP⟩ := hT (star g) (star_mem_SB hg)
  let Q : ι → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ' → mixedEmbedding.mixedSpace F) ℂ :=
    fun j => (conjSch.comp (P j)).comp conjSch
  refine ⟨ι, inferInstance, Q, fun j => star (g' j), fun j => star_mem_SB (hg' j), fun f => ?_⟩
  have hs : star (pureA F (f : _ → ℂ) g) = pureA F (conjSch f : _ → ℂ) (star g) := by
    rw [star_pureA]
  rw [conjMap_apply, hs, hP, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_pureA]
  rfl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameConjMapStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_conj_map : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)), IsTame F T → IsTame F (conjMap T) := by
  first | exact @GlobalTheory.DoublingEv.isTame_conjMap | exact GlobalTheory.DoublingEv.isTame_conjMap | (intros; apply GlobalTheory.DoublingEv.isTame_conjMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledCosetIndicatorSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledCosetIndicatorSchwartz
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

namespace GlobalTheory.EvAdm

theorem isCompact_scaledInt_of_ne_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Finite κ] {a : F} (ha : a ≠ 0) :
    IsCompact (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  have hO : IsCompact {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ v.adicCompletionIntegers F} := by
    haveI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
      fun v => isCompact_iff_compactSpace.1 (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v)
    have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (𝓕 := Filter.cofinite)).continuous
    rw [RestrictedProduct.range_structureMap] at h
    exact h
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → (κ → FiniteAdeleRing (𝓞 F) F) :=
    fun z i => algebraMap F (FiniteAdeleRing (𝓞 F) F) a * z i
  have hg : Continuous g := continuous_pi fun i => continuous_const.mul (continuous_apply i)
  have hP : IsCompact (Set.pi Set.univ fun _ : κ =>
      {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ v.adicCompletionIntegers F}) := isCompact_univ_pi fun _ => hO
  refine (hP.image hg).of_isClosed_subset ((scaledInt F κ a).isClosed_of_isOpen (isOpen_scaledInt a)) ?_
  intro z hz
  refine ⟨fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i, fun i _ v => ?_, ?_⟩
  · have h : (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i) v =
        (algebraMap F (v.adicCompletion F) a)⁻¹ * (z i) v := by
      have h1 := map_mul (evalV F v) (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹) (z i)
      rw [AlgHom.commutes, map_inv₀ (algebraMap F (v.adicCompletion F))] at h1
      exact h1
    show (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i) v ∈ _
    rw [h]
    exact hz i v
  · funext i
    simp only [g]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]

theorem indicator_coset_scaledInt_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a}.indicator (fun _ => (1 : ℂ)) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _ κ _ a ha r
  have hf : Continuous fun y : κ → FiniteAdeleRing (𝓞 F) F => y - r := continuous_id.sub continuous_const
  have hcl : IsClopen {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} :=
    ⟨((scaledInt F κ a).isClosed_of_isOpen (isOpen_scaledInt a)).preimage hf, (isOpen_scaledInt a).preimage hf⟩
  have hco : IsCompact {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} :=
    (Homeomorph.subRight r).isCompact_preimage.2 (isCompact_scaledInt_of_ne_zero (κ := κ) ha)
  generalize {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} = S at hcl hco ⊢
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ S
    · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    · filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro' hco hcl.isClosed (fun y hy => Set.indicator_of_notMem hy _)

end GlobalTheory.EvAdm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledCosetIndicatorSchwartzStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_coset_indicator_schwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a}.indicator (fun _ => (1 : ℂ)) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  exact @GlobalTheory.EvAdm.indicator_coset_scaledInt_mem_SB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulLeOfIsConjPl
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

noncomputable section

namespace GlobalTheory.BotPairSmall.CondXi

open GlobalTheory.Mem.Col2.SplitChar

theorem modT_le {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T)
    {PP : HeightOneSpectrum (𝓞 D.host.E)} (hq : PP ∈ L.Q t) : modT G t ≤ PP.asIdeal := by
  classical
  by_cases hW : PP ∈ G.pl.W0
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hW
    unfold modT
    refine (Ideal.mul_le_inf.trans inf_le_left).trans ?_
    have h1 : condE G.pl ≤ (G.pl.w v).asIdeal ^ condExp G.pl v :=
      Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv)
    refine h1.trans (Ideal.pow_le_self ?_)
    unfold condExp; split_ifs <;> omega
  · have hT : PP ∈ twPl G t := by
      unfold twPl
      rw [Finset.mem_filter]
      exact ⟨by unfold GlobalTheory.FunObj.locPl; exact Finset.mem_union_right _ hq, hW⟩
    unfold modT
    exact (Ideal.mul_le_inf.trans inf_le_right).trans (Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hT))

theorem conj_smul_le_of_isConjPl {D : D7} {PP' PP : HeightOneSpectrum (𝓞 D.host.E)}
    (h : Formalism.IndefR.Lev.IsConjPl PP' PP) : D.host.conj • PP'.asIdeal ≤ PP.asIdeal := by
  show Ideal.map _ _ ≤ _
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  obtain ⟨c', hc', e⟩ := h x hx
  rw [Ideal.mem_comap]
  convert hc'
  apply RingOfIntegers.ext
  rw [e, Formalism.BasicNotions.bridge_star_holds]
  rfl


open Formalism.L2.Host in
theorem xiH_eq_one_of_cong : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (t : T) (u : (AE D)ˣ), IntU D u → (u : AE D) - 1 ∈ hatId D (modT G t * D.host.conj • modT G t) → (L.xiH t).1 (finIdl D u) = 1 := by
  intro D T L sc μ₀ hL G t u hu hc
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E _ (L.xiH t).2.1 (finIdl D u) (finIdl_unit hu)
    (fun w => by rw [finIdl_fst]; rfl) fun PP x hx => ?_
  have hunit : IsUnitAt PP x := by
    unfold IsUnitAt
    rw [hx]
    exact finIdl_unit hu PP
  show (L.xiH t).loc PP x = 1
  by_cases hr : (L.xiH t).UnrAt PP
  · exact hr x hunit
  have hle : modT G t * D.host.conj • modT G t ≤ PP.asIdeal ^ (1 : ℕ) := by
    rw [pow_one]
    rcases (hL.Q_ram t PP).1 hr with hq | ⟨PP', hq, hcj⟩
    · exact (Ideal.mul_le_inf.trans inf_le_left).trans (modT_le G t hq)
    · exact (Ideal.mul_le_inf.trans inf_le_right).trans
        ((Ideal.map_mono (modT_le G t hq)).trans (conj_smul_le_of_isConjPl hcj))
  refine hL.xi_tame t PP x hunit ?_
  rw [hx, vl_sub_one]
  exact GlobalTheory.BotPairSmall.CondNu.vl_le_of_mem_hatId hle hc

end GlobalTheory.BotPairSmall.CondXi

end
end

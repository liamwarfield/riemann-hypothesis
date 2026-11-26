module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLevelReductionCriterion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFinitePartMemHomLatticeCompletionIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFinitePartMemHomLatticeCompletionIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.RatLat

open GlobalTheory.LatVac

variable {D : D7}

theorem eq_of_parts {m n : ℕ} {u u' : Formalism.IndefR.Datum.Mx D m n} (h1 : u.map (infPart D) = u'.map (infPart D))
    (h2 : u.map (finPart D) = u'.map (finPart D)) : u = u' := by
  ext i j
  rw [← sub_eq_zero]
  apply eq_zero_of_parts
  · rw [RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun h1 i) j
  · rw [RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun h2 i) j

theorem finTens_mem_iff {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    finTens 1 M ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      M ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
  refine ⟨fun h => ?_, finTens_mem_latO (one_mem_intAf _)⟩
  refine (GlobalTheory.T.rationalHermitianRankOneLattice_selfDual D S T ΛS ΛT hS hT (GlobalTheory.T.exists_dual_family_selfDual_hermitianSpace D S ΛS hS) _).2 fun ℓ hℓ => ?_
  have h1 := char_sympl_eq_one hψ hS hT h (finTens_mem_latO (one_mem_intAf _) hℓ)
  rw [symplO_finTens, one_mul, one_mul] at h1
  exact (char_rat hψ _).1 h1

theorem genMap_mulVec (S T : HSp D) (a : D.host.E) (s y : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    genMap S T a s t *ᵥ y = a • (∑ i, ∑ j, star (s i) * S.gram i j * y j) • t := by
  funext i
  simp only [genMap, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem mem_latRat_iff_perO {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : IsSelfDualC S ΛS) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    M ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) ↔
      Matrix.toLin' M ∈ perO (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) ΛS ΛT := by
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      refine Submodule.subset_span ⟨a, ha, Matrix.toLin' (genMap S T 1 s t), fun y hy => ?_, ?_⟩
      · obtain ⟨b, hb⟩ := (hS.2 y).1 hy s hs
        rw [Matrix.toLin'_apply, genMap_mulVec, one_smul, ← hb]
        exact ΛT.smul_mem b ht
      · refine LinearMap.ext fun y => ?_
        rw [LinearMap.smul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, genMap_mulVec, genMap_mulVec, one_smul]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  · intro h
    obtain ⟨n, s, s', hs, hd⟩ := GlobalTheory.T.exists_dual_family_selfDual_hermitianSpace D S ΛS hS
    have key : ∀ z ∈ perO (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) ΛS ΛT,
        LinearMap.toMatrix' z ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨r, hr, x, hx, rfl⟩ := hw
        have e : LinearMap.toMatrix' (r • x) = ∑ k, genMap S T r (s' k) (x (s k)) := by
          refine Matrix.ext fun i j => ?_
          have e1 : (Pi.single j 1 : Fin S.rank → D.host.E) = ∑ k, (∑ l, star (s' k l) * S.gram l j) • s k := by
            funext c
            rw [Finset.sum_apply, Pi.single_apply, ← hd c j]
            exact Finset.sum_congr rfl fun k _ => mul_comm (s k c) _
          have e2 : LinearMap.toMatrix' (r • x) i j = r * x (Pi.single j 1) i := by
            rw [LinearMap.toMatrix'_apply]
            first
              | rfl
              | (congr 3; funext c; simp [Pi.single_apply])
          set_option synthInstance.maxHeartbeats 100000 in
            rw [e2, e1, map_sum, Matrix.sum_apply, Finset.sum_apply, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [LinearMap.map_smul]
          change r * ((∑ l, star (s' k l) * S.gram l j) * x (s k) i) = r * x (s k) i * ∑ l, star (s' k l) * S.gram l j
          ring
        refine e ▸ AddSubgroup.sum_mem _ fun k _ => ?_
        exact AddSubgroup.subset_closure ⟨r, hr, _, (hs k).2, _, hx _ (hs k).1, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul c x _ hx =>
        have e : LinearMap.toMatrix' (c • x) = (c : D.host.E) • LinearMap.toMatrix' x := by
          rw [← map_smul]; rfl
        rw [e]
        exact smul_mem_latRat c hx
    have := key _ h
    rwa [LinearMap.toMatrix'_toLin'] at this

theorem AA_eq (h : D.host.ccK = ⊤) : D.host.AA = D.host.AA0 := by
  rw [Host.AA, Host.ccE, h, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul]

theorem finOf_mem_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) N N', (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → (v ∈ (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) ↔ toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D ψ θ S T a b hS hT δ sc hP ΛS ΛT N N' h1 h2 hΛS hΛT γ v hv
  subst hS hT
  have e1 : N = ΛS := (SetLike.coe_injective h1).symm
  have e2 : N' = ΛT := (SetLike.coe_injective h2).symm
  have : v = finTens 1 γ :=
    eq_of_parts (hv.1.trans (Matrix.ext fun i j => (infPart_pair _ _).symm)) (hv.2.trans rfl)
  rw [← h1, ← h2, this, finTens_mem_iff hP.std hΛS hΛT, mem_latRat_iff_perO ΛT hΛS, AA_eq hP.cc, e1, e2]
  rfl

end GlobalTheory.AdForm.RatLat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFinitePartMemHomLatticeCompletionIffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalFinitePart_mem_homLatticeCompletion_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) N N', (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → (v ∈ (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) ↔ toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  first | exact @GlobalTheory.AdForm.RatLat.finOf_mem_iff | exact GlobalTheory.AdForm.RatLat.finOf_mem_iff | (intros; apply GlobalTheory.AdForm.RatLat.finOf_mem_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianTwistedRealReadingEntireAndInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianTwistedRealReadingEntireAndInjective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.VacRead

variable {D : D7}

theorem eq_of_comp {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (w w' : Mx D m n)
    (hw : w.map (finPart D) = 0) (hw' : w'.map (finPart D) = 0) (h : ∀ τ, compAt θ τ w = compAt θ τ w') : w = w' := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  funext i j
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · have e1 : finPart D (w i j) = 0 := congrFun (congrFun hw i) j
    have e2 : finPart D (w' i j) = 0 := congrFun (congrFun hw' i) j
    rw [RingHom.map_sub, e1, e2, sub_zero]
  · have e : θ τ (infPart D (w i j)) = θ τ (infPart D (w' i j)) := congrFun (congrFun (h τ) i) j
    rw [RingHom.map_sub, RingHom.map_sub, e, sub_self]

theorem realPt_eq {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (w : Mx D m n)
    (hw : w.map (finPart D) = 0) (hz : ∀ τ, compAt θ τ w = z τ) : realPt θ z = w := by
  have hs : (realPt θ z).map (finPart D) = 0 ∧ ∀ τ, compAt θ τ (realPt θ z) = z τ := by
    unfold realPt
    exact Classical.epsilon_spec (p := fun w : Mx D m n => w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = z τ) ⟨w, hw, hz⟩
  exact eq_of_comp hθ _ _ hs.1 hw fun τ => (hs.2 τ).trans (hz τ).symm

theorem hAt_one (S T : HSp D) (hS : S.gram = 1) (hT : T.gram = 1) (τ : D.what₂.Tau)
    (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    GlobalTheory.VacUnique.hAt S T τ x y = ∑ i, ∑ j, x i j * starRingEnd ℂ (y i j) := by
  have h1 : gramAt D S τ = 1 := by
    unfold gramAt; rw [hS]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : gramAt D T τ = 1 := by
    unfold gramAt; rw [hT]; exact Matrix.map_one _ (map_zero _) (map_one _)
  unfold GlobalTheory.VacUnique.hAt
  rw [h1, h2, inv_one, Matrix.one_mul, Matrix.mul_one]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

end GlobalTheory.AdForm.VacRead

namespace GlobalTheory.AdForm.VacRead
variable {D : D7}

theorem xiN_eq_zero (θ : InfFam D) (hθ : IsInfFam θ) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b)
    (δ : ℂ) (sc : ℝ) (hδ : δ ≠ 0) (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    (h0 : xiN θ S T hS hT δ sc f = 0) : f = 0 := by
  subst hS hT
  refine GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real hf fun w hw => ?_
  have h1 := congrFun h0 (fun τ i j => -(δ * compAt θ τ w i j))
  have hp : realPt θ (fun τ => Matrix.of fun i j => -(δ⁻¹ * (fun τ i j => -(δ * compAt θ τ w i j) :
      VCx D.what₂.Tau S.rank T.rank) τ (Fin.cast rfl i) (Fin.cast rfl j))) = w := by
    refine realPt_eq hθ _ w hw fun τ => ?_
    funext i j
    simp only [Matrix.of_apply, Fin.cast_eq_self]
    field_simp
  unfold xiN at h1
  rw [hp, Pi.zero_apply] at h1
  exact (mul_eq_zero.1 h1).resolve_left (Complex.exp_ne_zero _)

end GlobalTheory.AdForm.VacRead

namespace GlobalTheory.AdForm.VacRead

theorem key_sum {ι : Type} [Fintype ι] (r0 k : ℝ) (s : ι → ℂ) :
    ((∑ τ, 2 * (Complex.I * (r0 : ℂ) * (k : ℂ) * s τ).re : ℝ) : ℂ) +
      Complex.I * ((∑ τ, 2 * (Complex.I * (r0 : ℂ) * (k : ℂ) * (-Complex.I * s τ)).re : ℝ) : ℂ) =
      2 * Complex.I * ((r0 * k : ℝ) : ℂ) * ∑ τ, s τ := by
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  apply Complex.ext <;> simp <;> ring

theorem scale_eq (x y sc : ℝ) (hy : y ≠ 0) (h : sc * y = 2 * x) : x * y⁻¹ = sc / 2 := by
  field_simp
  linarith

end GlobalTheory.AdForm.VacRead

namespace GlobalTheory.AdForm.VacRead
variable {D : D7}
open GlobalTheory.FockCompare

theorem xiN_differentiable (θ : InfFam D) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b)
    (δ : ℂ) (sc : ℝ) (ψ : AddChar (AF D.host.F) ℂ) (hP : StdPair θ S T δ sc ψ) (f : WO S T → ℂ)
    (hf : IsHol θ S T ψ f) : Differentiable ℂ (xiN θ S T hS hT δ sc f) := by
  subst hS hT
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hP.inf
  obtain ⟨hF, hann⟩ := GlobalTheory.VacUnique.Ann.vacuum_annihilation D θ σ hσ ψ hP.std S T (fun _ => 1) (fun _ => 1) f
    hf.1 hf.2
  set F : RW T S → ℂ := fun z => f (iotaW σ T S z) with hFdef
  set r : ℝ := sc / 2 with hr
  let L : RW T S →L[ℂ] RW T S := (-δ⁻¹) • ContinuousLinearMap.id ℂ (RW T S)
  have hL : ∀ Z τ i j, L Z τ i j = -(δ⁻¹ * Z τ i j) := fun Z τ i j => by simp [L]
  set E : RW T S → ℂ := fun Z => Complex.exp ((Real.pi * r * ∑ τ, ∑ i, ∑ j, ‖Z τ i j‖ ^ 2 : ℝ) : ℂ) with hE
  have hxi : xiN θ S T rfl rfl δ sc f = fun Z => F (L Z) * E Z := by
    funext Z
    unfold xiN
    have hp : realPt θ (fun τ => Matrix.of fun i j => -(δ⁻¹ * Z τ (Fin.cast rfl i) (Fin.cast rfl j))) =
        iotaW σ T S (L Z) := by
      refine realPt_eq hP.inf _ _ (by funext i j; exact hσ.fin _) fun τ => ?_
      funext i j
      show θ τ (infPart D (σ fun τ' => L Z τ' i j)) = _
      rw [hσ.comp]
      simp [hL]
    rw [hp, mul_comm]
    congr 2
    show (Real.pi : ℂ) / 2 * ((sc : ℂ) * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Z τ i j)) = _
    simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hr]; push_cast; ring
  rw [hxi]
  have hdG : ∀ Z Y, fderiv ℝ (fun Z => F (L Z)) Z Y = fderiv ℝ F (L Z) (L Y) := fun Z Y => by
    have h : HasFDerivAt (fun Z => F (L Z)) ((fderiv ℝ F (L Z)).comp (L.restrictScalars ℝ)) Z :=
      (hF (L Z)).hasFDerivAt.comp Z (L.restrictScalars ℝ).hasFDerivAt
    rw [h.fderiv]; rfl
  refine GlobalTheory.FockPos.differentiable_mul_of_cr (fun Z => F (L Z)) E
    (fun Z Y => (2 * Real.pi * r * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j) : ℂ))
    (hF.comp (L.restrictScalars ℝ).differentiable) (GlobalTheory.FockPos.gauss_cr r).1 (fun Z Y => ?_)
    (GlobalTheory.FockPos.gauss_cr r).2
  rw [hdG, hdG]
  have hj : GlobalTheory.VacUnique.jO S T (fun _ => 1) (fun _ => 1) (L Y) = L (Complex.I • Y) := by
    rw [L.map_smul]; funext τ; rw [GlobalTheory.VacUnique.jO_apply]
    change Complex.I • ((1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) * Matrix.of (L Y τ) *
      (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) = _
    rw [Matrix.one_mul, Matrix.mul_one]; rfl
  have h := hann (L Z) (L Y)
  rw [hj] at h
  have hdd : δ⁻¹ * starRingEnd ℂ δ⁻¹ = (((‖δ‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_inv, Complex.normSq_eq_norm_sq]
  have hom : ∀ Y' : RW T S, GlobalTheory.VacUnique.omO S T (L Z) (L Y') =
      ∑ τ, 2 * (Complex.I * (((Real.sqrt D.host.d)⁻¹ : ℝ) : ℂ) * (((‖δ‖ ^ 2)⁻¹ : ℝ) : ℂ) *
        ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y' τ i j)).re := by
    intro Y'
    rw [GlobalTheory.VacUnique.omO_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    show 2 * (tauE D τ D.host.xi0 * GlobalTheory.VacUnique.hAt S T τ (L Z τ) (L Y' τ)).re = _
    rw [hP.xi τ]
    erw [hAt_one S T hP.gS hP.gT τ (L Z τ) (L Y' τ)]
    have hs : ∑ i, ∑ j, L Z τ i j * starRingEnd ℂ (L Y' τ i j) =
        (((‖δ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y' τ i j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hL, hL, ← hdd]
      simp only [map_neg, map_mul]
      ring
    rw [hs]
    congr 2
    ring
  rw [hom, hom] at h
  have hs2 : ∀ τ, (∑ i, ∑ j, Z τ i j * starRingEnd ℂ ((Complex.I • Y) τ i j)) =
      -Complex.I * ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j) := fun τ => by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [hs2] at h
  have key := key_sum ((Real.sqrt D.host.d)⁻¹) ((‖δ‖ ^ 2)⁻¹) fun τ => ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j)
  have hrk : (Real.sqrt D.host.d)⁻¹ * (‖δ‖ ^ 2)⁻¹ = r :=
    scale_eq _ _ _ (pow_ne_zero 2 (norm_ne_zero_iff.2 hP.ne)) hP.scale
  rw [hrk] at key
  show _ = -((2 * Real.pi * r * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j) : ℂ) * F (L Z))
  linear_combination h + Real.pi * Complex.I * F (L Z) * key +
    2 * Real.pi * r * (∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j)) * F (L Z) * Complex.I_sq

end GlobalTheory.AdForm.VacRead

namespace GlobalTheory.AdForm.VacRead

theorem xiN_entire_and_injective : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ)
    (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ →
    (∀ f, IsHol θ S T ψ f → Differentiable ℂ (xiN θ S T hS hT δ sc f)) ∧
      ∀ f, IsThetaFunO ψ S T f → xiN θ S T hS hT δ sc f = 0 → f = 0 := by
  intro D ψ θ S T a b hS hT δ sc hP
  exact ⟨fun f hf => xiN_differentiable θ S T hS hT δ sc ψ hP f hf,
    fun f hf h0 => xiN_eq_zero θ hP.inf S T hS hT δ sc hP.ne ψ f hf h0⟩

end GlobalTheory.AdForm.VacRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianTwistedRealReadingEntireAndInjectiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianTwistedRealReading_entire_and_injective : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → (∀ f, IsHol θ S T ψ f → Differentiable ℂ (xiN θ S T hS hT δ sc f)) ∧ ∀ f, IsThetaFunO ψ S T f → xiN θ S T hS hT δ sc f = 0 → f = 0 := by
  first | exact @GlobalTheory.AdForm.VacRead.xiN_entire_and_injective | exact GlobalTheory.AdForm.VacRead.xiN_entire_and_injective | (intros; apply GlobalTheory.AdForm.VacRead.xiN_entire_and_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FixLevCompactOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixProjEqOneOfSuppAtDistinctFinitePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixProjEqOneOfSuppAtDistinctFinitePlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OtherPlace

theorem pr_placeIdem_other {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (hv : q.v ≠ q'.v) :
    q.pr (q'.e + cA D q'.e) = 0 := by
  obtain ⟨ε, hε, hqe⟩ := q.above
  obtain ⟨ε', hε', hqe'⟩ := q'.above
  have hpr : ∀ x, q.pr x = q.pr (q.e * x) := fun x => by rw [← q.sec_pr, q.pr_sec]
  have he : q.e = q.e * algebraMap (AF D.host.F) (AE D) ε := by
    rw [← hqe, mul_add, q.split.1, q.split.2.1, add_zero]
  have hεε : ε * ε' = 0 := by
    rw [GlobalTheory.SplitCut.eFin_of_placeIdem hε, GlobalTheory.SplitCut.eFin_of_placeIdem hε']
    exact GlobalTheory.LocWeil.PlaceIdem.eFin_mul_eFin _ hv
  rw [hqe', hpr, he, mul_assoc, ← map_mul, hεε, map_zero, mul_zero, map_zero]

theorem mt_map_pr_eq_one : ∀ (D : D7) (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q : GlobalTheory.FinPl.SplitPt D k)
    (q' : GlobalTheory.FinPl.SplitPt D k') (V : HSp D) (g : GA D V), q.v ≠ q'.v → SuppAt q'.e V g → (mt V g).map q.pr = 1 := by
  intro D k k' _ _ _ _ _ _ _ _ q q' V g hv hs
  have h0 := pr_placeIdem_other q q' hv
  ext i j
  have h1 := congrArg q.pr (hs i j)
  rw [map_mul, h0, zero_mul, Matrix.sub_apply, map_sub] at h1
  rw [Matrix.map_apply, ← sub_eq_zero, ← h1.symm]
  have : q.pr ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) k) i j := by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [this]

end GlobalTheory.OtherPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixProjEqOneOfSuppAtDistinctFinitePlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_proj_eq_one_of_suppAt_distinct_finitePlace : ∀ (D : D7) (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (V : HSp D) (g : GA D V), q.v ≠ q'.v → SuppAt q'.e V g → (mt V g).map q.pr = 1 := by
  first | exact @GlobalTheory.OtherPlace.mt_map_pr_eq_one | exact GlobalTheory.OtherPlace.mt_map_pr_eq_one | (intros; apply GlobalTheory.OtherPlace.mt_map_pr_eq_one <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FixLev
variable {D : D7}

theorem continuous_mt (V : HSp D) : Continuous (mt V) :=
  Units.continuous_val.comp continuous_subtype_val

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y : Type} [Fintype Y] [DecidableEq Y]

theorem map_mt_mul (q : SplitPt D k) (V : HSp D) (g h : GA D V) :
    (mt V (g * h)).map q.pr = (mt V g).map q.pr * (mt V h).map q.pr := by
  rw [GlobalTheory.SplitCut.mt_mul, Matrix.map_mul]

theorem frame_mul {N : ℕ} (F : GlobalTheory.LocMod.Frame k N Y) (A B : Matrix (Fin N) (Fin N) k) :
    F.γ * A * F.β * (F.γ * B * F.β) = F.γ * (A * B) * F.β := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul]

theorem frame_cancel {N : ℕ} (F : GlobalTheory.LocMod.Frame k N Y) {A B : Matrix Y Y k}
    (h : F.β * A * F.γ = F.β * B * F.γ) : A = B := by
  have := congrArg (fun M => F.γ * M * F.β) h
  simp only [Matrix.mul_assoc] at this
  simpa [← Matrix.mul_assoc, F.γβ] using this

theorem frame_conj {N : ℕ} (F : GlobalTheory.LocMod.Frame k N Y) (A : Matrix (Fin N) (Fin N) k) :
    F.β * (F.γ * A * F.β) * F.γ = A := by
  simp only [← Matrix.mul_assoc, F.βγ, Matrix.one_mul]
  rw [Matrix.mul_assoc, F.βγ, Matrix.mul_one]

def locHom (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y) : GA D V →* GL Y k where
  toFun g := ⟨F.γ * (mt V g).map q.pr * F.β, F.γ * (mt V g⁻¹).map q.pr * F.β,
    by rw [frame_mul, ← map_mt_mul, mul_inv_cancel, GlobalTheory.SplitCut.mt_one,
      Matrix.map_one _ (map_zero q.pr) (map_one q.pr), Matrix.mul_one, F.γβ],
    by rw [frame_mul, ← map_mt_mul, inv_mul_cancel, GlobalTheory.SplitCut.mt_one,
      Matrix.map_one _ (map_zero q.pr) (map_one q.pr), Matrix.mul_one, F.γβ]⟩
  map_one' := Units.ext (by
    change F.γ * (mt V 1).map q.pr * F.β = 1
    rw [GlobalTheory.SplitCut.mt_one, Matrix.map_one _ (map_zero q.pr) (map_one q.pr), Matrix.mul_one, F.γβ])
  map_mul' g h := Units.ext (by
    change F.γ * (mt V (g * h)).map q.pr * F.β = F.γ * (mt V g).map q.pr * F.β * (F.γ * (mt V h).map q.pr * F.β)
    rw [frame_mul, map_mt_mul])

theorem locHom_val (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y) (g : GA D V) :
    (locHom q V F g).val = F.γ * (mt V g).map q.pr * F.β := rfl

theorem locHom_spec (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y) (g : GA D V) :
    (mt V g).map q.pr = F.β * (locHom q V F g).val * F.γ := by
  rw [locHom_val, frame_conj]

theorem continuous_locHom (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y) :
    Continuous (locHom q V F) := by
  have h1 : Continuous fun g : GA D V => F.γ * (mt V g).map q.pr * F.β :=
    (continuous_const.matrix_mul ((continuous_mt V).matrix_map q.cont_pr)).matrix_mul continuous_const
  refine Units.continuous_iff.2 ⟨h1, ?_⟩
  refine (h1.comp continuous_inv).congr fun g => ?_
  change F.γ * (mt V g⁻¹).map q.pr * F.β = ((locHom q V F g)⁻¹ : GL Y k).val
  rw [← map_inv, locHom_val]

end Local

theorem list_prod_single {M : Type} [Monoid M] {ι : Type} [DecidableEq ι] (f : ι → M) (i : ι)
    (hf : ∀ i', i' ≠ i → f i' = 1) : ∀ l : List ι, l.Nodup → i ∈ l → (l.map f).prod = f i := by
  intro l hl hi
  rw [List.prod_map_eq_pow_single i f (fun i' hne _ => hf i' hne),
    List.count_eq_one_of_mem hl hi, pow_one]

theorem map_mt_list_prod {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) (V : HSp D) (l : List (GA D V)) : (mt V l.prod).map q.pr = (l.map fun g => (mt V g).map q.pr).prod := by
  induction l with
  | nil => simp [GlobalTheory.SplitCut.mt_one]
  | cons a l ih => rw [List.prod_cons, map_mt_mul, ih, List.map_cons, List.prod_cons]

theorem exists_section (V : HSp D) {n : ℕ} (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
    [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, SplitPt D (k i))
    (hq : Function.Injective fun i => (q i).v) (Y : Fin n → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (F : ∀ i, GlobalTheory.LocMod.Frame (k i) V.rank (Y i)) :
    ∃ Ψ : (∀ i, GL (Y i) (k i)) → GA D V, Continuous Ψ ∧ (∀ x, Ψ x ∈ grpAt V (fun p => ∃ i, p = (q i).v)) ∧
      (∀ x i, (mt V (Ψ x)).map (q i).pr = (F i).β * (x i).val * (F i).γ) ∧
      ∀ g ∈ grpAt V (fun p => ∃ i, p = (q i).v), ∀ x,
        (∀ i, (mt V g).map (q i).pr = (F i).β * (x i).val * (F i).γ) → Ψ x = g := by
  choose gl hgc hgl hgu using fun i => GlobalTheory.T.exists_continuous_local_GL_embedding_splitPlace D (k i) (q i) V (Y i) (F i)
  have hmat : ∀ (h : Fin n → GA D V), (∀ i, SuppAt (q i).e V (h i)) → ∀ i,
      (mt V ((List.finRange n).map h).prod).map (q i).pr = (mt V (h i)).map (q i).pr := fun h hh i => by
    rw [map_mt_list_prod, List.map_map]
    exact list_prod_single (fun i' => (mt V (h i')).map (q i).pr) i
      (fun i' hi' => GlobalTheory.T.matrix_proj_eq_one_of_suppAt_distinct_finitePlace D (k i) (k i') (q i) (q i') V (h i') (fun e => hi' (hq e).symm) (hh i'))
      _ (List.nodup_finRange n) (List.mem_finRange i)
  refine ⟨fun x => ((List.finRange n).map fun i => gl i (x i)).prod, ?_, fun x => ?_, fun x i => ?_, fun g hg x hx => ?_⟩
  · exact continuous_list_prod _ fun i _ => (hgc i).comp (continuous_apply i)
  · refine Subgroup.list_prod_mem (K := grpAt V (fun p => ∃ i, p = (q i).v)) fun y hy => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact GlobalTheory.T.mem_supportedSubgroup_of_suppAt_splitPlace_mem D (k i) (q i) V _ (hgl i (x i)).1 _ ⟨i, rfl⟩
  · rw [hmat (fun i => gl i (x i)) (fun i => (hgl i (x i)).1) i]
    exact (hgl i (x i)).2
  · obtain ⟨h, hh, rfl⟩ := GlobalTheory.T.unitarySupported_splitPlaces_eq_prod_local_parts D V n k q hq g hg
    show ((List.finRange n).map fun i => gl i (x i)).prod = _
    congr 1
    refine List.map_congr_left fun i _ => (hgu i (h i) (x i) (hh i) ((hmat h hh i).symm.trans (hx i))).symm


open GlobalTheory.SeeSaw GlobalTheory.StepData in
theorem fixLev_compact_open : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), GPin G → ∀ j, j < D.R.m →
    v.JG j ≤ grpAt (c.V j) (· ∈ v.gP) ∧ IsCompact (v.JG j : Set (GA D (c.V j))) ∧
    IsOpen (((v.JG j).subgroupOf (grpAt (c.V j) (· ∈ v.gP)) : Subgroup _) : Set (grpAt (c.V j) (· ∈ v.gP))) := by
  intro D c v n G hG j hj
  have ha : ∀ i, j + ((G i).s + 1 - j) = (G i).s + 1 := fun i => by have := (G i).hs; omega
  set V := c.V j
  have hP : (· ∈ v.gP) = fun p => ∃ i, p = (G i).q.v := funext fun p => propext (hG.places p)
  have hMat : ∀ i a ha g x, (G i).Mat j a ha g x ↔ x = locHom (G i).q V ((G i).FY j a ha) g := fun i a ha g x => by
    constructor
    · intro h
      exact Units.ext (frame_cancel ((G i).FY j a ha) (h.symm.trans (locHom_spec _ _ _ g)))
    · rintro rfl
      exact locHom_spec _ _ _ g
  let Js : ∀ i, Subgroup (GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin ((G i).s + 1 - j)) (G i).k) := fun i =>
    (((G i).S.T (Fin D.R.t)).lev j _ (ha i)).J
  have hJ : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO (Js i) := fun i =>
    GlobalTheory.UnfoldedEntries.isCO_lev (T := (G i).S.T (Fin D.R.t)) (GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _) j _ (ha i)
  have hmem : ∀ g, g ∈ v.JG j ↔ g ∈ grpAt V (· ∈ v.gP) ∧ ∀ i, locHom (G i).q V ((G i).FY j _ (ha i)) g ∈ Js i := by
    intro g
    rw [hG.lev j hj g]
    refine and_congr_right fun _ => ⟨fun H i => H i _ (ha i) _ ((hMat _ _ _ _ _).2 rfl), fun H i a ha' x hx => ?_⟩
    have e : a = (G i).s + 1 - j := by omega
    subst e
    rw [(hMat _ _ _ _ _).1 hx]
    exact H i
  refine ⟨fun g hg => ((hmem g).1 hg).1, ?_, ?_⟩
  · obtain ⟨Ψ, hc, hin, hloc, huniq⟩ := exists_section V (fun i => (G i).k) (fun i => (G i).q) hG.inj
      (fun i => XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin ((G i).s + 1 - j)) (fun i => (G i).FY j _ (ha i))
    have himg : (v.JG j : Set (GA D V)) = Ψ '' Set.pi Set.univ fun i => (Js i : Set _) := by
      ext g
      constructor
      · intro hg
        obtain ⟨h1, h2⟩ := (hmem g).1 hg
        refine ⟨fun i => locHom (G i).q V ((G i).FY j _ (ha i)) g, fun i _ => h2 i, huniq g (hP ▸ h1) _ fun i => ?_⟩
        exact locHom_spec _ _ _ g
      · rintro ⟨x, hx, rfl⟩
        refine (hmem _).2 ⟨hP ▸ hin x, fun i => ?_⟩
        have e : locHom (G i).q V ((G i).FY j _ (ha i)) (Ψ x) = x i :=
          Units.ext (frame_cancel ((G i).FY j _ (ha i)) ((locHom_spec _ _ _ _).symm.trans (hloc x i)))
        rw [e]
        exact hx i (Set.mem_univ _)
    rw [himg]
    exact (isCompact_univ_pi fun i => (hJ i).2).image hc
  · have hset : (((v.JG j).subgroupOf (grpAt V (· ∈ v.gP)) : Subgroup _) : Set (grpAt V (· ∈ v.gP))) =
        ⋂ i, (fun g : grpAt V (· ∈ v.gP) => locHom (G i).q V ((G i).FY j _ (ha i)) g.1) ⁻¹' (Js i : Set _) := by
      ext g
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_iInter, Set.mem_preimage]
      exact ((hmem g.1).trans (and_iff_right g.2))
    rw [hset]
    exact isOpen_iInter_of_finite fun i =>
      (hJ i).1.preimage ((continuous_locHom _ _ _).comp continuous_subtype_val)

end GlobalTheory.FixLev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharConductorIntegersContinuousNeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharConductorIntegersContinuousNeOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem hasConductor_one_continuous_ne_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle),
    HasConductor ψ 1 → Continuous ψ ∧ ψ ≠ 1 := by
  intro k _ _ _ _ ψ h
  exact ⟨h.continuous, h.ne_one⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharConductorIntegersContinuousNeOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addChar_conductor_integers_continuous_ne_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle),
    HasConductor ψ 1 → Continuous ψ ∧ ψ ≠ 1 := by
  first | exact @GlobalTheory.hasConductor_one_continuous_ne_one | exact GlobalTheory.hasConductor_one_continuous_ne_one | (intros; apply GlobalTheory.hasConductor_one_continuous_ne_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDataDifferBySplittingFactorQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDataDifferBySplittingFactorQuotient
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

namespace GlobalTheory.WeilChange

theorem weilData_differ_by_splitFac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT χS' χT' : (AE D)ˣ →* Circle) (om om' : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS' χT' om' → ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y → ∀ f, IsThetaFunO ψ S T f → om' (g, h) f = ((splitFacO χS' χT' x y : ℂ) * (splitFacO χS χT x y : ℂ)⁻¹) • om (g, h) f := by
  intro D ψ S T χS χT χS' χT' om om' H H' g h x y hx hy f hf
  have rS : ResEta D (χS⁻¹ * χS') 0 :=
    resEta_parity (resEta_mul (resEta_inv H.resS) H'.resS) (by omega)
  have rT : ResEta D (χT⁻¹ * χT') 0 :=
    resEta_parity (resEta_mul (resEta_inv H.resT) H'.resT) (by omega)
  obtain ⟨om₂, H₂, h₂⟩ := exists_weilDatum_twist D ψ H.std S T χS χT (χS⁻¹ * χS') (χT⁻¹ * χT') om H
    (hecke_mul (hecke_inv H.hecS) H'.hecS) (hecke_mul (hecke_inv H.hecT) H'.hecT) rS rT
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at H₂
  rw [GlobalTheory.WeilUniq.weilDatum_unique D ψ H.std S T χS' χT' om' om₂ H' H₂ (g, h) f hf, h₂ g h x y hx hy, LinearMap.smul_apply]
  congr 1
  rw [← Circle.coe_inv, ← Circle.coe_mul]
  congr 1
  simp only [splitFacO, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_inv]
  generalize (χT' x)⁻¹ = a, (χS y)⁻¹ = b, χS' y = c, χT x = d
  apply Circle.ext
  simp only [Circle.coe_mul]
  ring

end GlobalTheory.WeilChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDataDifferBySplittingFactorQuotientStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilData_differ_by_splittingFactorQuotient : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT χS' χT' : (AE D)ˣ →* Circle) (om om' : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS' χT' om' → ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y → ∀ f, IsThetaFunO ψ S T f → om' (g, h) f = ((splitFacO χS' χT' x y : ℂ) * (splitFacO χS χT x y : ℂ)⁻¹) • om (g, h) f := by
  first | exact @GlobalTheory.WeilChange.weilData_differ_by_splitFac | exact GlobalTheory.WeilChange.weilData_differ_by_splitFac | (intros; apply GlobalTheory.WeilChange.weilData_differ_by_splitFac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmPureTensorOComb
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockComb

theorem om_pureTensorO_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ sS sT BS BT (e : WO S T →₀ ℂ) (f₀ f : WO S T → ℂ) (x : ℂ), IsFinComb e → IsThetaFunO ψ S T f₀ → IsThetaFunO ψ S T f → ∀ b ∈ GfC S, ∀ b' ∈ GfC T, om (b, b') f = x • comb ψ S T e f₀ → ∀ P, ∀ a ∈ GinfC S, ∀ a' ∈ GinfC T, om (a * b, a' * b') (pureTensorO ψ θ S T sS sT BS BT f P) = x • comb ψ S T e (om (a, a') (pureTensorO ψ θ S T sS sT BS BT f₀ P)) ∧ ∀ (N : Lat S) (N' : Lat T), Vac ψ S T N N' (fun _ => True) f₀ → Vac ψ S T N N' (fun _ => True) (om (a, a') (pureTensorO ψ θ S T sS sT BS BT f₀ P)) := by
  intro D ψ θ S T χS χT om hθ hW sS sT BS BT e f₀ f x he hf₀ hf b hb b' hb' hfx P a ha a' ha'
  have hψ : IsStdChar D ψ (-1) := hW.std

  have hfin := GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT b b'
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb', Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb', Matrix.one_mul]) f hf P
  have hth₀ : IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f₀ P) :=
    (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT 1 1
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.one_mul]) f₀ hf₀ P).1

  have hcomb : comb ψ S T e (pureTensorO ψ θ S T sS sT BS BT f₀ P) =
      pureTensorO ψ θ S T sS sT BS BT (comb ψ S T e f₀) P := by
    let q := e.support.equivFin
    have key := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D ψ θ S T hψ hθ sS sT BS BT f₀ hf₀ e.support.card
      (fun i => e (q.symm i).1) (fun i => (q.symm i).1) (fun i => he _ (q.symm i).2) P).1
    have h1 : ∀ g : WO S T → (WO S T → ℂ), ∑ u ∈ e.support, e u • g u = ∑ i, e (q.symm i).1 • g (q.symm i).1 := by
      intro g
      rw [← Finset.sum_coe_sort e.support]
      exact (Equiv.sum_comp q.symm (fun u : e.support => e u.1 • g u.1)).symm
    simp only [comb]
    rw [h1, h1]
    exact key
  refine ⟨?_, fun N N' hv => ?_⟩
  · have e1 : ((a * b, a' * b') : GA D S × GA D T) = (a, a') * (b, b') := rfl
    rw [e1, map_mul, Module.End.mul_apply, hfin.2, hfx, GlobalTheory.FiniteFock.pureTensorO_smul, ← hcomb, map_smul,
      GlobalTheory.FrComb.om_comb hW ha ha' he hth₀]
  · refine ⟨hW.om_pres _ _ hth₀, GlobalTheory.FrComb.latVac_om hW ha ha' hth₀ ?_⟩
    have fix : ∀ u ∈ latO S T (N : Set _) (N' : Set _) (fun _ => True), heisO ψ S T u f₀ = f₀ →
        heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT f₀ P) = pureTensorO ψ θ S T sS sT BS BT f₀ P := by
      intro u hu h0
      have := ((GlobalTheory.FinTranslate.finite_translate D ψ θ S T hψ hθ f₀ hf₀).2 u (GlobalTheory.SplitScalar.latO_fin hu)).2 sS BS sT BT P
      rw [← this, h0]
    exact ⟨fun u hu => fix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hv.2.1 u hu),
      fun e' he' u hu hh => fix u hu (hv.2.2 e' he' u hu hh)⟩

end GlobalTheory.FockComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedDataEqKernelDataAtLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedDataEqKernelDataAtLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSawRhs

variable {D : D7}

theorem latO_mono (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : latO S T LS LT P ≤ latO S T LS LT P' := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, hv, rest⟩
  exact ⟨α, hα, fun v hv' => hv v (fun hp => hv' (h v hp)), rest⟩

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P P' : Pl D → Prop}
    (h : ∀ p, P p → P' p) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P' f) : Vac ψ S T LS LT P f :=
  ⟨hf.1, fun u hu => hf.2.1 u (latO_mono S T _ _ h hu),
    fun e he u hu hh => hf.2.2 e he u (latO_mono S T _ _ h hu) hh⟩

theorem idAt_mono {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : idAt D P ≤ idAt D P' := by
  intro x hx
  simp only [idAt, Ideal.mem_inf, Submodule.mem_iInf] at hx ⊢
  exact ⟨hx.1, fun w => hx.2 ⟨w.1, fun hw => w.2 (h _ hw)⟩⟩

theorem combAt_mono {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) {S T : HSp D} {c : WO S T →₀ ℂ}
    (hc : CombAt P c) : CombAt P' c := fun u hu i j => idAt_mono h (hc u hu i j)

theorem comb_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) (w : WO S T) :
    comb ψ S T c f w = ∑ x ∈ c.support, c x * (ψ (symplOH S T w x) * f (w + x)) := by
  simp [comb, heisO, Finset.sum_apply]

theorem biComb_smul (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) (a : ℂ)
    (C : WO A S → WO S A' → ℂ) : biComb ψ A S A' c c' (a • C) = a • biComb ψ A S A' c c' C := by
  funext u v
  simp only [biComb, Pi.smul_apply, smul_eq_mul, comb_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem comb_comm2 (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (e : WO A S →₀ ℂ) (d' : WO S A' →₀ ℂ)
    (G : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    comb ψ S A' d' (fun v' => comb ψ A S e (fun u'' => G u'' v') u) v =
      comb ψ A S e (fun u'' => comb ψ S A' d' (G u'') v) u := by
  simp only [comb_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem biComb_biComb (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (d e : WO A S →₀ ℂ) (d' e' : WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    biComb ψ A S A' d d' (biComb ψ A S A' e e' C) u v =
      comb ψ A S d (comb ψ A S e (fun u'' => comb ψ S A' d' (comb ψ S A' e' (C u'')) v)) u := by
  simp only [biComb]
  congr 1
  funext u'
  exact comb_comm2 ψ A S A' e d' (fun u'' v' => comb ψ S A' e' (C u'') v') u' v

theorem biLift_smul {A S A' : HSp D} (oma : Om A S) (omb : Om S A') (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ) (a : ℂ)
    (C : WO A S → WO S A' → ℂ) : biLift oma omb vA vS φ (a • C) = a • biLift oma omb vA vS φ C := by
  funext h₂
  have h1 : ∀ h₀ h₁ v, oma (h₀, h₁) (fun u => a * C u v) 0 = a * oma (h₀, h₁) (fun u => C u v) 0 := by
    intro h₀ h₁ v
    rw [show (fun u => a * C u v) = a • (fun u => C u v) from rfl, map_smul]
    rfl
  have h2 : ∀ h₀ h₁, omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => a * C u v) 0) 0 =
      a * omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => C u v) 0) 0 := by
    intro h₀ h₁
    have e : (fun v => oma (h₀, h₁) (fun u => a * C u v) 0) = a • (fun v => oma (h₀, h₁) (fun u => C u v) 0) :=
      funext fun v => h1 h₀ h₁ v
    rw [e, map_smul]
    rfl
  simp only [biLift, Pi.smul_apply, smul_eq_mul, h2]
  simp_rw [show ∀ x y : ℂ, x * (a * y) = a * (x * y) from fun x y => mul_left_comm x a y, integral_const_mul]

theorem theta_comb_left {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} (Y : WO A S → WO S A' → ℂ)
    (hY : ∀ v, IsThetaFunO ψ A S (fun u => Y u v)) (c : WO S A' →₀ ℂ) (v : WO S A') :
    IsThetaFunO ψ A S (fun u => comb ψ S A' c (Y u) v) := by
  classical
  have key : ∀ s : Finset (WO S A'),
      IsThetaFunO ψ A S (fun u => ∑ x ∈ s, c x * (ψ (symplOH S A' v x) * Y u (v + x))) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp only [Finset.sum_empty]
      exact Formalism.IndefR.Fock.CCR.theta_zero ψ A S
    · intro x s hx ih
      have := Formalism.IndefR.Fock.CCR.theta_add_smul ih (hY (v + x)) (c x * ψ (symplOH S A' v x))
      convert this using 1
      funext u
      simp only [Finset.sum_insert hx, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  simpa only [comb_apply] using key c.support

end GlobalTheory.SeeSawRhs

namespace GlobalTheory.SeeSawRhs

theorem unfolded_eq_kernel_data : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → GValue (t := t) v → TLaw v w → FlatLaw D → BiAct D → ∀ j σ h Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ β, (∑ α, ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) (comb c.ψ _ _ (v.eG j) Ψ₁) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂)))) = (v.cG j * w.cT j) • t.two j (fun α => v.Sad j (φ α)) ((v.op j).app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) β := by
  intro D c v t w hc hv _ hF hG hT _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ hφ β
  have hj : j < D.R.m := by omega
  have hj1 : j + 1 < D.R.m := by omega
  have top : ∀ (P : Pl D → Prop) p, P p → True := fun _ _ _ => trivial
  simp only [Comm.bl]
  rw [hG.1 j σ h Ψ₁ Ψ₂ (vac_mono (top _) h₁) (vac_mono (top _) h₂)]
  obtain ⟨hBV, hTL⟩ := hT.1 j σ h Ψ₁ Ψ₂ (vac_mono (top _) h₁) (vac_mono (top _) h₂)
  simp only [Comm.bl] at hTL
  set X₀ := c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂ with hX₀
  set Y := (v.op j).app c.ψ X₀ with hY
  have hQG : ∀ p, p ∈ w.Q → ¬ p ∈ v.gP := fun p hp => Finset.disjoint_left.mp hF.disjG hp
  have hoff : ∀ p, (p ∈ w.Q ∨ p ∈ v.gP) → p ∉ v.tP := by
    rintro p (hp | hp)
    · exact Finset.disjoint_left.mp hF.disjT hp
    · exact Finset.disjoint_left.mp hv.disj hp
  have prod := fun (S T : HSp D) => (GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D c.ψ hc.std S T (· ∈ w.Q) (· ∈ v.gP) hQG).2.2.2.1
  unfold Tup.two
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  obtain ⟨d₁, hd₁, ed₁⟩ := prod _ _ (w.dQ j α γ) (v.dG j)
    (combAt_mono (fun p hp => Or.inl hp) ((hF.atQ j).2.2 α γ)) (combAt_mono (fun p hp => Or.inr hp) (hv.atG j).2.1)
  obtain ⟨d₂, hd₂, ed₂⟩ := prod _ _ (w.dQ (j + 1) γ β) (v.dG (j + 1))
    (combAt_mono (fun p hp => Or.inl hp) ((hF.atQ (j + 1)).2.2 γ β))
    (combAt_mono (fun p hp => Or.inr hp) (hv.atG (j + 1)).2.1)
  have e1 : biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) (biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) X₀) =
      biComb c.ψ _ _ _ d₁ d₂ X₀ := by
    funext u v'
    rw [biComb_biComb]
    simp only [biComb, ed₁, ed₂]
  have e2 : biComb c.ψ _ _ _ d₁ d₂ (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) Y) =
      biComb c.ψ _ _ _ (t.dd j α γ) (t.dd (j + 1) γ β) Y := by
    funext u v'
    rw [biComb_biComb, ed₁]
    have hF' : (fun u'' => comb c.ψ _ _ d₂ (comb c.ψ _ _ (v.dT (j + 1)) (Y u'')) v') =
        fun u'' => comb c.ψ _ _ (t.dd (j + 1) γ β) (Y u'') v' := by
      funext u''
      rw [ed₂, ← hF.dd (j + 1) hj1 γ β _ (hBV.2 u'').1]
    rw [hF', ← hF.dd j hj α γ _ (theta_comb_left Y (fun v'' => (hBV.1 v'').1) _ v')]
    rfl
  rw [biComb_smul, biLift_smul, e1, hTL d₁ d₂ (combAt_mono hoff hd₁) (combAt_mono hoff hd₂) (φ α) (hφ α), e2,
    smul_smul]

end GlobalTheory.SeeSawRhs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedDataEqKernelDataAtLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_unfoldedData_eq_kernelData_at_level : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → GValue (t := t) v → TLaw v w → FlatLaw D → BiAct D → ∀ j σ h Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ β, (∑ α, ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) (comb c.ψ _ _ (v.eG j) Ψ₁) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂)))) = (v.cG j * w.cT j) • t.two j (fun α => v.Sad j (φ α)) ((v.op j).app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) β := by
  first | exact @GlobalTheory.SeeSawRhs.unfolded_eq_kernel_data | exact GlobalTheory.SeeSawRhs.unfolded_eq_kernel_data | (intros; apply GlobalTheory.SeeSawRhs.unfolded_eq_kernel_data <;> assumption)
end
end

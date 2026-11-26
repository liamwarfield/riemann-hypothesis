module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Iwa
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ContinuousAdeleInfHom
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WtBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingEquivPlaceCorrespondencePlaceUnder
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Tube

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Iwa
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.iwa :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], Iwa F := by
  intro F _ _ _
  obtain ⟨hK, hKc⟩ := M.kkCpt F
  obtain ⟨hB, e, he⟩ := M.borHomeo F
  refine ⟨hKc, fun C hC => ?_⟩
  have hemb : IsClosedEmbedding (Subtype.val : M.Bor F → G1 F) := hB.isClosedEmbedding_subtypeVal
  have hS : IsCompact ((fun p : G1 F × G1 F => p.1 * p.2) '' (C ×ˢ KK F)) :=
    (hC.prod hKc).image continuous_mul
  refine ⟨Prod.fst '' (e.symm '' ((Subtype.val : M.Bor F → G1 F) ⁻¹'
    ((fun p : G1 F × G1 F => p.1 * p.2) '' (C ×ˢ KK F)))),
    ((hemb.isCompact_preimage hS).image e.symm.continuous).image continuous_fst, fun g hg => ?_⟩
  obtain ⟨b, a, k, hk, rfl⟩ := M.iwa F g
  refine ⟨b, a, ?_, k, hk, rfl⟩
  refine ⟨(a, b), ⟨e (a, b), ?_, e.symm_apply_apply _⟩, rfl⟩
  change ((e (a, b) : M.Bor F) : G1 F) ∈ (fun p : G1 F × G1 F => p.1 * p.2) '' (C ×ˢ KK F)
  rw [he]
  refine ⟨(nU b * mD a * k, k⁻¹), ⟨hg, ?_⟩, by simp⟩
  change k⁻¹ ∈ KK F
  rw [hK] at hk ⊢
  exact (M.Ks F).inv_mem hk
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DLFock
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.dLFock :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (Y : Lie E 2), ∀ φ ∈ Fock D.δ, O.dL D Y φ ∈ Fock D.δ := by
  intro F E _ _ _ _ _ _ _ D O Y φ hφ
  let S : Subalgebra ℂ (Module.End ℂ (S4 F)) :=
    { carrier := {z | ∀ φ ∈ Fock D.δ, z φ ∈ Fock D.δ}
      mul_mem' := fun hx hy φ h => hx _ (hy φ h)
      add_mem' := fun hx hy φ h => add_mem (hx φ h) (hy φ h)
      algebraMap_mem' := fun c φ h => Submodule.smul_mem _ c h }
  have hx : ∀ w i, O.x w i ∈ S := fun w i ψ hψ => (opsFock F E D O w i ψ hψ).1
  have hd : ∀ w i, O.d w i ∈ S := fun w i ψ hψ => (opsFock F E D O w i ψ hψ).2
  have hX : ∀ τ a b, O.X D τ a b ∈ S := fun τ a b => by
    fin_cases a <;> fin_cases b
    · exact hx _ _
    · exact add_mem (hx _ _) (S.smul_mem (hx _ _) _)
    · exact sub_mem (hx _ _) (S.smul_mem (hx _ _) _)
    · exact hx _ _
  have hD : ∀ τ a b, O.DX D τ a b ∈ S := fun τ a b => by
    fin_cases a <;> fin_cases b
    · exact hd _ _
    · exact S.smul_mem (add_mem (hd _ _) (S.smul_mem (hd _ _) _)) _
    · exact S.smul_mem (sub_mem (hd _ _) (S.smul_mem (hd _ _) _)) _
    · exact hd _ _
  refine (?_ : O.dL D Y ∈ S) φ hφ
  refine sum_mem fun τ _ => sum_mem fun i _ => sum_mem fun j _ => S.smul_mem (sub_mem (neg_mem ?_) ?_) _
  · split_ifs
    · exact one_mem _
    · exact zero_mem _
  · exact sum_mem fun b _ => mul_mem (hX _ _ _) (hD _ _ _)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ContinuousAb
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem wt_nonneg' {K : Type} [Field K] [NumberField K]
    (S : Set (Fin 4 → FiniteAdeleRing (𝓞 K) K)) (N : ℕ) (v : V4 K) : 0 ≤ wt S N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

private theorem continuous_ab {K : Type} [Field K] [NumberField K] :
    Continuous (ab : (A K)ˣ → ℝ) :=
  continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule (K := K))

private theorem ab_pos {K : Type} [Field K] [NumberField K] (a : (A K)ˣ) : 0 < ab a :=
  (IdeleGroup.ideleModule K a).2

theorem UpperTheory.ConvolutionTheory.R2.Ff.lDom :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), LDom W := by
  intro F E _ _ _ _ _ _ _ D W ι s Φ hΦ C hC
  obtain ⟨K, hK, hΦ⟩ := hΦ
  obtain ⟨ρ, hρ, hact, hnu, -, -⟩ := actCont F E D

  let r : GL (Fin 2) (A E) → GL (Fin 4) (A F) := fun h => ρ h⁻¹
  have hr : Continuous r := hρ.comp continuous_inv
  obtain ⟨K', hK', hlin⟩ := wtLin F (r '' C) (hC.image hr) K hK

  let β : GL (Fin 2) (A E) → ℝ := fun h => (ab (nu F h))⁻¹
  have hβ : Continuous β :=
    (continuous_ab.comp hnu).inv₀ fun h => (ab_pos _).ne'
  obtain ⟨A₀, hA₀⟩ := (hC.image hβ).bddAbove
  refine ⟨K', hK', fun N => ?_⟩
  obtain ⟨B, hB⟩ := hΦ N
  obtain ⟨B', hB'⟩ := hlin N
  refine ⟨|A₀| * (|B| * B'), ?_⟩
  rintro ⟨h, i⟩ ⟨hh, hi⟩ v
  have hβ0 : 0 ≤ β h := (inv_pos.2 (ab_pos _)).le
  have hβA : β h ≤ |A₀| := (hA₀ ⟨h, hh, rfl⟩).trans (le_abs_self _)
  have hnorm : ‖(W.L h (Φ i)).1 v‖ = β h * ‖(Φ i).1 (D.act h⁻¹ v)‖ := by
    rw [W.L_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ0]
  have h1 : ‖(Φ i).1 (D.act h⁻¹ v)‖ ≤ |B| * (B' * wt K' N v) := by
    have h2 : wt K N ((r h).val *ᵥ v) ≤ B' * wt K' N v := hB' (r h) ⟨h, hh, rfl⟩ v
    have h3 := hB i hi (D.act h⁻¹ v)
    rw [hact h⁻¹ v] at h3 ⊢
    calc _ ≤ B * wt K N ((r h).val *ᵥ v) := h3
      _ ≤ |B| * wt K N ((r h).val *ᵥ v) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (wt_nonneg' _ _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  calc ‖(W.L h (Φ i)).1 v‖ = β h * ‖(Φ i).1 (D.act h⁻¹ v)‖ := hnorm
    _ ≤ |A₀| * (|B| * (B' * wt K' N v)) :=
      mul_le_mul hβA h1 (norm_nonneg _) (abs_nonneg _)
    _ = |A₀| * (|B| * B') * wt K' N v := by ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Imports
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFinGLLeInvAbsDet
open NumberField IsDedekindDomain GlobalTheory.HenQ
open GlobalTheory.CuspRep (GA Af finGL)

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.HenQ

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem finGL_apply (k : GL (Fin n) (Af K)) (a b : Fin n) :
    ((finGL K n k : GA K n) : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) a b =
      (1 : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) a b
        - GlobalTheory.CuspRep.sFin K ((1 : Matrix (Fin n) (Fin n) (Af K)) a b)
        + GlobalTheory.CuspRep.sFin K ((k : Matrix (Fin n) (Fin n) (Af K)) a b) := rfl

theorem sFin_fst (x : Af K) : (GlobalTheory.CuspRep.sFin K x).1 = 0 := rfl

end GlobalTheory.HenQ

namespace GlobalTheory.HenQ

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

end GlobalTheory.HenQ
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LLevel
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.Ff.TubeLevelLattice

private theorem tube {G X : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G] [TopologicalSpace X]
    (T : G → X → X) (hT : Continuous fun p : G × X => T p.1 p.2) (h1 : ∀ w, T 1 w = w)
    (hinv : ∀ k w, T k⁻¹ (T k w) = w) {g : X → ℂ} (hg : IsLocallyConstant g) (hc : HasCompactSupport g) :
    ∀ᶠ k in 𝓝 (1 : G), ∀ w, g (T k w) = g w :=
  _root_.UpperTheory.Reformulated.B.Qi19.tube T hT h1 hinv hg hc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private def eI (K : Type) [Field K] [NumberField K] : A K := (1, 0)

private theorem am_eI : am E (eI F) = eI E :=
  Prod.ext (map_one (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)))
    (map_zero (AdeleBaseChange.finiteAdeleMap F E))

private theorem eI_fst (K : Type) [Field K] [NumberField K] (x : A K) : (eI K * x).1 = x.1 :=
  one_mul x.1

private theorem eI_snd (K : Type) [Field K] [NumberField K] (x : A K) : (eI K * x).2 = 0 :=
  zero_mul x.2

private theorem fin_fst (k : GL (Fin 2) (Af E)) (a b : Fin 2) :
    ((finGL E 2 k).val a b).1 = ((1 : Matrix (Fin 2) (Fin 2) (A E)) a b).1 := by
  have := GlobalTheory.HenQ.finGL_apply k a b
  rw [this]
  change ((1 : Matrix (Fin 2) (Fin 2) (A E)) a b).1 -
    (GlobalTheory.CuspRep.sFin E ((1 : Matrix (Fin 2) (Fin 2) (Af E)) a b)).1 +
    (GlobalTheory.CuspRep.sFin E (k.val a b)).1 = _
  rw [GlobalTheory.HenQ.sFin_fst, GlobalTheory.HenQ.sFin_fst, sub_zero, add_zero]

private theorem eI_mul (x y : A E) (h : x.1 = y.1) : eI E * x = eI E * y :=
  Prod.ext (by rw [eI_fst, eI_fst, h]) (by rw [eI_snd, eI_snd])

private theorem eI_fin (k : GL (Fin 2) (Af E)) :
    eI E • (finGL E 2 k).val = eI E • (1 : Matrix (Fin 2) (Fin 2) (A E)) := by
  ext a b
  exact eI_mul _ _ (fin_fst k a b)

private theorem eI_star (D : Dat F E) (k : GL (Fin 2) (Af E)) :
    eI E • D.star2 (finGL E 2 k).val = eI E • (1 : Matrix (Fin 2) (Fin 2) (A E)) := by
  have hb : D.bar (eI E) = eI E := by rw [← am_eI (F := F), D.bar_am]
  have h1 := eI_fin k
  ext a b
  have h2 := congrFun (congrFun h1 b) a
  simp only [Matrix.smul_apply, smul_eq_mul] at h2 ⊢
  rw [D.conjTransposeGal_apply]
  have h3 := congrArg D.bar h2
  rw [map_mul, map_mul, hb] at h3
  rw [h3]
  have : D.bar ((1 : Matrix (Fin 2) (Fin 2) (A E)) b a) = (1 : Matrix (Fin 2) (Fin 2) (A E)) a b := by
    by_cases hab : a = b
    · subst hab; simp
    · have hba : b ≠ a := fun h => hab h.symm
      simp [Matrix.one_apply, hab, hba]
  rw [this]

private theorem act_eI (D : Dat F E) (k : GL (Fin 2) (Af E)) (v : V4 F) :
    D.act (finGL E 2 k) (eI F • v) = eI F • v := by
  apply D.herm_injective
  rw [D.herm_act, D.herm_smul, am_eI]
  rw [Matrix.mul_smul, ← Matrix.smul_mul, eI_fin, Matrix.smul_mul, one_mul, Matrix.smul_mul,
    ← Matrix.mul_smul, eI_star, Matrix.mul_smul, mul_one]

private theorem act_fst (D : Dat F E) (k : GL (Fin 2) (Af E)) (v : V4 F) (i : Fin 4) :
    (D.act (finGL E 2 k) v i).1 = (v i).1 := by
  have h := congrFun (act_eI D k v) i
  rw [D.act_smul] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  have := congrArg Prod.fst h
  rwa [eI_fst, eI_fst] at this

private def io (w : Fin 4 → Af F) : V4 F := fun i => (0, w i)

private theorem continuous_io : Continuous (io (F := F)) :=
  continuous_pi fun i => continuous_const.prodMk (continuous_apply i)

private theorem finPart_io (w : Fin 4 → Af F) : finPartPi (io w) = w := rfl

private theorem split (v : V4 F) : v = eI F • v + io (finPartPi v) := by
  funext i
  refine Prod.ext ?_ ?_
  · show (v i).1 = (eI F * v i).1 + 0
    rw [eI_fst, add_zero]
  · show (v i).2 = (eI F * v i).2 + (v i).2
    rw [eI_snd, zero_add]

private def TT (D : Dat F E) (k : GL (Fin 2) (Af E)) (w : Fin 4 → Af F) : Fin 4 → Af F :=
  finPartPi (D.act (finGL E 2 k) (io w))

private theorem finPart_act (D : Dat F E) (k : GL (Fin 2) (Af E)) (v : V4 F) :
    finPartPi (D.act (finGL E 2 k) v) = TT D k (finPartPi v) := by
  conv_lhs => rw [split v]
  rw [D.act_add, act_eI]
  funext i
  show (eI F * v i).2 + _ = _
  rw [eI_snd, zero_add]
  rfl

end UpperTheory.ConvolutionTheory.R2.Ff.TubeLevelLattice

end

open UpperTheory.ConvolutionTheory.R2.Ff.TubeLevelLattice in
theorem UpperTheory.ConvolutionTheory.R2.Ff.lLevel :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), LLevel W := by
  intro F E _ _ _ _ _ _ _ D W φ
  obtain ⟨ρ, -, -, -, -, hfin⟩ := actCont F E D
  have hT : Continuous fun p : GL (Fin 2) (Af E) × (Fin 4 → Af F) => TT D p.1 p.2 :=
    continuous_finPartPi.comp (D.continuous_act' (hfin.comp continuous_fst) (continuous_io.comp continuous_snd))
  have h1 : ∀ w, TT D 1 w = w := fun w => by
    simp only [TT, map_one, D.act_one, finPart_io]
  have hinv : ∀ k w, TT D k⁻¹ (TT D k w) = w := fun k w => by
    have e := finPart_act D k⁻¹ (D.act (finGL E 2 k) (io w))
    rw [map_inv, D.act_inv_act, finPart_io] at e
    exact e.symm
  have key : ∀ f ∈ schwartzBruhatPi (K := F) (ι := Fin 4), ∀ᶠ k in 𝓝 (1 : GL (Fin 2) (Af E)),
      ∀ v, f (D.act (finGL E 2 k)⁻¹ v) = f v := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨φ₀, g, hg, rfl⟩ := hG
      obtain ⟨hlc, hcs⟩ := (mem_finiteSchwartzBruhatPi F).1 hg
      have ht : Tendsto (fun k : GL (Fin 2) (Af E) => k⁻¹) (𝓝 1) (𝓝 1) := by
        simpa only [inv_one] using (continuous_inv (G := GL (Fin 2) (Af E))).tendsto 1
      filter_upwards [ht.eventually (tube (TT D) hT h1 hinv hlc hcs)] with k hk v
      have e1 : infPartPi (D.act (finGL E 2 k)⁻¹ v) = infPartPi v := by
        funext i
        simp only [infPartPi, ← map_inv, act_fst]
      have e2 : finPartPi (D.act (finGL E 2 k)⁻¹ v) = TT D k⁻¹ (finPartPi v) := by
        rw [← map_inv, finPart_act]
      simp only [schwartzBruhatTensorPi, e1, e2, hk]
    | zero => exact Eventually.of_forall fun _ _ => rfl
    | add G H _ _ hG hH =>
      filter_upwards [hG, hH] with k h h' v
      simp only [Pi.add_apply, h, h']
    | smul c G _ hG =>
      filter_upwards [hG] with k h v
      simp only [Pi.smul_apply, h]
  have hab : ∀ᶠ k in 𝓝 (1 : GL (Fin 2) (Af E)), ab (nu F (finGL E 2 k)) = 1 := by
    have hU : (KLev E 2 1 : Set (GL (Fin 2) (Af E))) ∈ 𝓝 (1 : GL (Fin 2) (Af E)) :=
      (isOpen_KLev le_rfl).mem_nhds (one_mem _)
    filter_upwards [hU] with k hk
    let f : GL (Fin 2) (Af E) →* {r : ℝ // 0 < r} :=
      (IdeleGroup.ideleModule F).comp ((ideleNorm F E).comp
        ((Matrix.GeneralLinearGroup.det).comp (finGL E 2)))
    have := GroundTheory.Automorphic.Reduction.eq_one_of_isCompact (isCompact_KLev le_rfl) f
      (continuous_ab.comp (continuous_nu.comp hfin)) hk
    exact congrArg Subtype.val this
  filter_upwards [key φ.1 φ.2, hab] with k h₁ h₂
  refine Subtype.ext (funext fun v => ?_)
  rw [W.L_apply, h₁, h₂]
  simp
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.level :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), Level W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ Φ hΦ
  obtain ⟨κ, hκc, hκ⟩ := finTr F E D
  have hfo : IsOpen {k | TR.finRep F 2 k f = f} := (π.cusp f hf).1.level
  have h1 : ∀ᶠ k in 𝓝 (1 : GL (Fin 2) (Af E)), TR.finRep F 2 (κ k) f = f := by
    have hm : {k | TR.finRep F 2 k f = f} ∈ 𝓝 (κ 1) := hfo.mem_nhds (by simp)
    exact hκc.continuousAt.eventually hm
  let S : Subgroup (GL (Fin 2) (Af E)) :=
    { carrier := {k | GlobalTheory.CuspRep.finRep E 2 k Φ = Φ}
      one_mem' := by simp
      mul_mem' := fun {k l} hk hl => by
        change GlobalTheory.CuspRep.finRep E 2 (k * l) Φ = Φ
        rw [map_mul, Module.End.mul_apply, hl, hk]
      inv_mem' := fun {k} hk => by
        change GlobalTheory.CuspRep.finRep E 2 k⁻¹ Φ = Φ
        conv_lhs => rw [← show GlobalTheory.CuspRep.finRep E 2 k Φ = Φ from hk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl }
  refine Subgroup.isOpen_of_mem_nhds (H := S) (g := 1) ?_
  filter_upwards [lLevel F E D W φ, h1] with k hL hk
  refine Subtype.ext (funext fun g => ?_)
  change Φ.1 (g * finGL E 2 k) = Φ.1 g
  rw [hΦ, transl F E D W M, hL, hκ k]
  exact congrFun (congrArg (fun u => lift W M u φ) (congrArg Subtype.val hk)) g
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThDer
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.thDer :
    ∀ (F : Type) [Field F] [NumberField F], ThDer F := by
  intro F _ _ Ψ Ψ' hD t hDom
  obtain ⟨K, hK, hB⟩ := hDom
  obtain ⟨N, hN⟩ := wtSum F
  obtain ⟨C, hC⟩ := hN K hK 1 one_pos
  have hab : (1 : ℝ) ≤ ab (1 : (A F)ˣ) := by simp [ab]
  have hsum := (hC 1 hab).1
  obtain ⟨B, hB⟩ := hB N
  have hsc : ∀ ξ : Fin 4 → F, sc (1 : (A F)ˣ) ξ = fun i => rt (ξ i) := by
    intro ξ; funext i; simp [sc]
  obtain ⟨-, K', hK', hB'⟩ := wtBound F (Ψ t)
  have hs0 : Summable (fun ξ : Fin 4 → F => (Ψ t).1 fun i => rt (ξ i)) := by
    obtain ⟨B', hB'⟩ := hB' N
    obtain ⟨C', hC'⟩ := hN K' hK' 1 one_pos
    refine Summable.of_norm_bounded (g := fun ξ : Fin 4 → F => B' * wt K' N (sc (1 : (A F)ˣ) ξ)) ((hC' 1 hab).1.mul_left B') ?_
    intro ξ
    rw [hsc]
    exact hB' () (Set.mem_univ _) _
  have key := hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℂ)
    (u := fun ξ : Fin 4 → F => B * wt K N (sc (1 : (A F)ˣ) ξ))
    (g := fun (ξ : Fin 4 → F) (s : ℝ) => (Ψ s).1 fun i => rt (ξ i))
    (g' := fun (ξ : Fin 4 → F) (s : ℝ) => (Ψ' s).1 fun i => rt (ξ i))
    (t := Metric.ball t 1) (y₀ := t) (y := t)
    (hsum.mul_left B) Metric.isOpen_ball (convex_ball t 1).isPreconnected
    (fun ξ y _ => hD y _)
    (fun ξ y hy => by rw [hsc]; exact hB y hy _)
    (Metric.mem_ball_self one_pos) hs0 (Metric.mem_ball_self one_pos)
  exact key
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.SummableRationalSchwartz
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem summable_rational_schwartz (F : Type) [Field F] [NumberField F] (φ : S4 F) :
    Summable (fun ξ : Fin 4 → F => φ.1 fun i => rt (ξ i)) := by
  obtain ⟨-, K, hK, hB⟩ := wtBound F φ
  obtain ⟨N, hN⟩ := wtSum F
  obtain ⟨B, hB⟩ := hB N
  obtain ⟨C, hC⟩ := hN K hK 1 one_pos
  have hab : (1 : ℝ) ≤ ab (1 : (A F)ˣ) := by
    simp [ab]
  have hs := (hC 1 hab).1
  refine Summable.of_norm_bounded (g := fun ξ => B * wt K N (sc (1 : (A F)ˣ) ξ)) (hs.mul_left B) ?_
  intro ξ
  have := hB () (Set.mem_univ _) (fun i => rt (ξ i))
  have hsc : sc (1 : (A F)ˣ) ξ = fun i => rt (ξ i) := by
    funext i
    exact one_mul _
  rw [hsc]
  exact this

theorem UpperTheory.ConvolutionTheory.R2.Ff.thLin :
    ∀ (F : Type) [Field F] [NumberField F], ThLin F := by
  intro F _ _
  refine ⟨fun φ φ' => ?_, fun c φ => ?_⟩
  · have h : ∀ ξ : Fin 4 → F, (φ + φ').1 (fun i => rt (ξ i)) =
        φ.1 (fun i => rt (ξ i)) + φ'.1 (fun i => rt (ξ i)) := fun ξ => rfl
    simp only [Th, h]
    exact (summable_rational_schwartz F φ).tsum_add (summable_rational_schwartz F φ')
  · have h : ∀ ξ : Fin 4 → F, (c • φ).1 (fun i => rt (ξ i)) =
        c * φ.1 (fun i => rt (ξ i)) := fun ξ => rfl
    simp only [Th, h]
    exact tsum_mul_left
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.IntegrableMulChar
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WtEqComp
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

set_option synthInstance.maxSize 1000

private theorem wt_eq_comp {F : Type} [Field F] [NumberField F]
    (K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)) (N : ℕ) :
    wt (F := F) K N =
      (fun p : (Fin 4 → mixedEmbedding.mixedSpace F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) =>
        ((1 + ‖p.1‖) ^ N)⁻¹ * K.indicator (fun _ => (1 : ℝ)) p.2) ∘ splitEquivPi F (Fin 4) := by
  funext v
  by_cases h : finPartPi v ∈ K
  · simp [wt, splitEquivPi_apply, h]
  · simp [wt, splitEquivPi_apply, h]

theorem UpperTheory.ConvolutionTheory.R2.Ff.wtInt :
    ∀ (F : Type) [Field F] [NumberField F], WtInt F := by
  intro F _ _
  refine ⟨Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) + 1, fun K hK => ?_⟩
  rw [wt_eq_comp, measurePreserving_splitEquivPi.integrable_comp_emb
    (splitEquivPi F (Fin 4)).measurableEmbedding]
  refine Integrable.mul_prod (f := fun x : Fin 4 → mixedEmbedding.mixedSpace F => ((1 + ‖x‖) ^ (Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) + 1))⁻¹)
    (g := fun y => K.indicator (fun _ => (1 : ℝ)) y) ?_ ?_
  · have h := integrable_one_add_norm (E := Fin 4 → mixedEmbedding.mixedSpace F)
      (μ := mixedMeasurePi F) (r := ((Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) + 1 : ℕ) : ℝ))
      (by push_cast; linarith)
    refine h.congr (Eventually.of_forall fun x => ?_)
    have hx : (0 : ℝ) ≤ 1 + ‖x‖ := by positivity
    simp only [Real.rpow_neg hx, Real.rpow_natCast]
  · exact (integrable_indicator_iff hK.measurableSet).2
      (integrableOn_const hK.measure_lt_top.ne)
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem der_nU {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E} (W : Weil D) {Ψ Ψ' : ℝ → S4 F}
    (h : Der Ψ Ψ') (b : A F) :
    Der (fun s => W.Om (nU b) (Ψ s)) (fun s => W.Om (nU b) (Ψ' s)) := by
  intro t v
  simp only [W.Om_n]
  exact (h t v).const_mul _

private theorem integrable_mul_char {F : Type} [Field F] [NumberField F] (φ : S4 F)
    {c : V4 F → ℂ} (hc : Continuous c) (hn : ∀ y, ‖c y‖ = 1) :
    Integrable (fun y => φ.1 y * c y) (adeleMeasurePi F) := by
  obtain ⟨N, hN⟩ := wtInt F
  obtain ⟨hφ, K, hK, hB⟩ := wtBound F φ
  obtain ⟨B, hB⟩ := hB N
  refine Integrable.mono' ((hN K hK).const_mul B) (hφ.mul hc).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [norm_mul, hn, mul_one]
  exact hB () (Set.mem_univ _) y

private theorem der_wW {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E} (W : Weil D) {Ψ Ψ' : ℝ → S4 F}
    (h : Der Ψ Ψ') (hd : ∀ t, Dom (Metric.ball t 1) fun s => (Ψ' s).1) :
    Der (fun s => W.Om (wW F) (Ψ s)) (fun s => W.Om (wW F) (Ψ' s)) := by
  intro t v
  simp only [W.Om_w, ft4]
  obtain ⟨N, hN⟩ := wtInt F
  obtain ⟨K, hK, hB⟩ := hd t
  obtain ⟨B, hB⟩ := hB N
  have e : ∀ i, Continuous fun y : V4 F => y i := fun i => continuous_apply i
  have cB : Continuous fun y : V4 F => B4 D.δ y v :=
    ((continuous_const.mul (((e 2).mul continuous_const).sub
      (continuous_const.mul ((e 3).mul continuous_const)))).sub
      ((e 1).mul continuous_const)).sub ((e 0).mul continuous_const)
  have cψ : Continuous fun y : V4 F => ψ (B4 D.δ y v) := continuous_ψ.comp cB
  have cont : ∀ φ : S4 F, Continuous fun y => φ.1 y * ψ (B4 D.δ y v) :=
    fun φ => (wtBound F φ).1.mul cψ
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s y => (Ψ s).1 y * ψ (B4 D.δ y v)) (F' := fun s y => (Ψ' s).1 y * ψ (B4 D.δ y v))
    (bound := fun y => B * wt K N y) (μ := adeleMeasurePi F)
    (Metric.ball_mem_nhds t one_pos)
    (Eventually.of_forall fun s => (cont (Ψ s)).aestronglyMeasurable)
    (integrable_mul_char (Ψ t) cψ fun y => norm_ψ _)
    (cont (Ψ' t)).aestronglyMeasurable
    (Eventually.of_forall fun y s hs => by
      rw [norm_mul, norm_ψ, mul_one]
      exact hB s hs y)
    ((hN K hK).const_mul B)
    (Eventually.of_forall fun y s _ => (h s y).mul_const _)).2

theorem UpperTheory.ConvolutionTheory.R2.Ff.omDer :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), OmDer W := by
  intro F E _ _ _ _ _ _ _ D W Ψ Ψ' h hd g
  have hg : g ∈ Subgroup.closure (Set.range (nU (F := F)) ∪ {wW F}) := by
    rw [(gen F).1]
    trivial
  have wstep : ∀ y, Der (fun s => W.Om y (Ψ s)) (fun s => W.Om y (Ψ' s)) →
      Der (fun s => W.Om (wW F * y) (Ψ s)) (fun s => W.Om (wW F * y) (Ψ' s)) := by
    intro y hy
    simp only [map_mul, Module.End.mul_apply]
    exact der_wW W hy (hd y)
  induction hg using Subgroup.closure_induction_left with
  | one => simpa using h
  | mul_left x hx y _ ih =>
    rcases hx with ⟨b, rfl⟩ | hx
    · simp only [map_mul, Module.End.mul_apply]
      exact der_nU W ih b
    · rw [Set.mem_singleton_iff.1 hx]
      exact wstep y ih
  | inv_mul_cancel x hx y _ ih =>
    rcases hx with ⟨b, rfl⟩ | hx
    · rw [← nU_neg]
      simp only [map_mul, Module.End.mul_apply]
      exact der_nU W ih (-b)
    · rw [Set.mem_singleton_iff.1 hx, wW_inv, ← wW_mul_wW, mul_assoc, mul_assoc]
      exact wstep _ (wstep _ (wstep y ih))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WtLeOfNorm
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem wt_le_of_norm {K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)} {N : ℕ} {v w : V4 F} {m : ℝ}
    (hm1 : 1 ≤ m) (hf : finPartPi w = finPartPi v) (h : ‖infPartPi v‖ ≤ m * ‖infPartPi w‖) :
    wt K N w ≤ m ^ N * wt K N v := by
  have hm0 : 0 ≤ m ^ N := by positivity
  by_cases hv : finPartPi w ∈ K
  · have hv' : finPartPi v ∈ K := hf ▸ hv
    generalize hsd : ‖infPartPi v‖ = s at h
    generalize htd : ‖infPartPi w‖ = t at h
    have ht0 : 0 ≤ t := htd ▸ norm_nonneg _
    have hs0 : 0 ≤ s := hsd ▸ norm_nonneg _
    have h1 : 1 + s ≤ m * (1 + t) := by nlinarith
    have hp : (1 + s) ^ N ≤ m ^ N * (1 + t) ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h1 N
    have e1 : wt K N w = ((1 + t) ^ N)⁻¹ := by rw [← htd]; exact if_pos hv
    have e2 : wt K N v = ((1 + s) ^ N)⁻¹ := by rw [← hsd]; exact if_pos hv'
    rw [e1, e2, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  · have e : wt K N w = 0 := if_neg hv
    rw [e]
    refine mul_nonneg hm0 ?_
    unfold wt
    split_ifs
    · positivity
    · exact le_rfl

private theorem exists_pl (w : InfinitePlace F) : ∃ τ : E →+* ℂ, UpperTheory.ConvolutionTheory.R2.Fo.pl F τ = w := by
  obtain ⟨w', hw'⟩ := InfinitePlace.comap_surjective (k := F) (K := E) w
  refine ⟨w'.embedding, ?_⟩
  change InfinitePlace.mk (w'.embedding.comp (algebraMap F E)) = w
  rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  exact hw'

private theorem entry_le (Y H : Matrix (Fin 2) (Fin 2) ℂ) {t B : ℝ} (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hY : ∀ i j, ‖Y i j‖ ≤ t) (hH : ∀ i j, ‖H i j‖ ≤ B) (i j : Fin 2) :
    ‖(Y * H * Yᴴ) i j‖ ≤ 4 * t ^ 2 * B := by
  have T : ∀ a b, ‖Y i a * H a b * star (Y j b)‖ ≤ t ^ 2 * B := fun a b => by
    rw [norm_mul, norm_mul, norm_star]
    calc ‖Y i a‖ * ‖H a b‖ * ‖Y j b‖ ≤ t * B * t :=
          mul_le_mul (mul_le_mul (hY _ _) (hH _ _) (norm_nonneg _) ht) (hY _ _) (norm_nonneg _)
            (mul_nonneg ht hB)
      _ = t ^ 2 * B := by ring
  have e : (Y * H * Yᴴ) i j = Y i 0 * H 0 0 * star (Y j 0) + Y i 1 * H 1 0 * star (Y j 0) +
      (Y i 0 * H 0 1 * star (Y j 1) + Y i 1 * H 1 1 * star (Y j 1)) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  linarith [norm_add_le (Y i 0 * H 0 0 * star (Y j 0)) (Y i 1 * H 1 0 * star (Y j 0)),
    norm_add_le (Y i 0 * H 0 1 * star (Y j 1)) (Y i 1 * H 1 1 * star (Y j 1)), T 0 0, T 1 0, T 0 1, T 1 1]

end

section

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem abs_pInf_le (v : V4 F) (i : Fin 4) (w : InfinitePlace F) :
    |TR.pInf F (v i) w| ≤ ‖infPartPi v‖ := by
  have hw : w.IsReal := IsTotallyReal.isReal w
  have e : (infPartPi v i).1 ⟨w, hw⟩ = TR.pInf F (v i) w := rfl
  calc |TR.pInf F (v i) w| = ‖(infPartPi v i).1 ⟨w, hw⟩‖ := by rw [e, Real.norm_eq_abs]
    _ ≤ ‖(infPartPi v i).1‖ := norm_le_pi_norm _ _
    _ ≤ ‖infPartPi v i‖ := norm_fst_le _
    _ ≤ ‖infPartPi v‖ := norm_le_pi_norm _ _

private theorem norm_inf_le (v : V4 F) {U : ℝ} (hU : 0 ≤ U)
    (h : ∀ i w, |TR.pInf F (v i) w| ≤ U) : ‖infPartPi v‖ ≤ U := by
  refine (pi_norm_le_iff_of_nonneg hU).2 fun i => ?_
  rw [Prod.norm_def]
  refine max_le ((pi_norm_le_iff_of_nonneg hU).2 fun w => ?_) ((pi_norm_le_iff_of_nonneg hU).2 fun w => ?_)
  · have e : (infPartPi v i).1 w = TR.pInf F (v i) w.1 := rfl
    rw [e, Real.norm_eq_abs]
    exact h i w.1
  · exact absurd w.2 (InfinitePlace.not_isComplex_iff_isReal.2 (IsTotallyReal.isReal w.1))

private theorem co_le_Hm {s : ℂ} (hs : s ≠ 0) (w : InfinitePlace F) (x : Fin 4 → TR.Rinf F) {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ i j, ‖Hm s w x i j‖ ≤ B) (i : Fin 4) : |x i w| ≤ (1 + ‖s‖⁻¹) * B := by
  have hs' : 0 < ‖s‖ := norm_pos_iff.2 hs
  have e00 : Hm s w x 0 0 = (x 1 w : ℂ) := by simp [Hm]
  have e11 : Hm s w x 1 1 = (x 0 w : ℂ) := by simp [Hm]
  have e01 : Hm s w x 0 1 = (x 2 w : ℂ) + s * (x 3 w : ℂ) := by simp [Hm]
  have e10 : Hm s w x 1 0 = (x 2 w : ℂ) - s * (x 3 w : ℂ) := by simp [Hm]
  have h0 : |x 0 w| ≤ B := by simpa [e11] using h 1 1
  have h1 : |x 1 w| ≤ B := by simpa [e00] using h 0 0
  have h2 : |x 2 w| ≤ B := by
    have e : ((2 * x 2 w : ℝ) : ℂ) = Hm s w x 0 1 + Hm s w x 1 0 := by
      rw [e01, e10]; push_cast; ring
    have : ‖((2 * x 2 w : ℝ) : ℂ)‖ ≤ B + B := by
      rw [e]; exact (norm_add_le _ _).trans (add_le_add (h _ _) (h _ _))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul] at this
    norm_num at this
    linarith
  have h3 : |x 3 w| ≤ ‖s‖⁻¹ * B := by
    have e : s * ((2 * x 3 w : ℝ) : ℂ) = Hm s w x 0 1 - Hm s w x 1 0 := by
      rw [e01, e10]; push_cast; ring
    have : ‖s * ((2 * x 3 w : ℝ) : ℂ)‖ ≤ B + B := by
      rw [e]; exact (norm_sub_le _ _).trans (add_le_add (h _ _) (h _ _))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul] at this
    norm_num at this
    rw [inv_mul_eq_div, le_div_iff₀ hs']
    nlinarith
  have hp : 0 ≤ ‖s‖⁻¹ * B := by positivity
  fin_cases i
  · change |x 0 w| ≤ _
    nlinarith
  · change |x 1 w| ≤ _
    nlinarith
  · change |x 2 w| ≤ _
    nlinarith
  · change |x 3 w| ≤ _
    nlinarith

private theorem Hm_le (s : ℂ) (w : InfinitePlace F) (x : Fin 4 → TR.Rinf F) {U : ℝ}
    (hU : 0 ≤ U) (h : ∀ i, |x i w| ≤ U) (i j : Fin 2) : ‖Hm s w x i j‖ ≤ (1 + ‖s‖) * U := by
  have hn : 0 ≤ ‖s‖ * U := by positivity
  have hr : ∀ k, ‖(x k w : ℂ)‖ ≤ U := fun k => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact h k
  have hm : ‖s * (x 3 w : ℂ)‖ ≤ ‖s‖ * U := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hr 3) (norm_nonneg _)
  fin_cases i <;> fin_cases j
  · have e : Hm s w x 0 0 = (x 1 w : ℂ) := by simp [Hm]
    change ‖Hm s w x 0 0‖ ≤ _
    rw [e]
    nlinarith [hr 1]
  · have e : Hm s w x 0 1 = (x 2 w : ℂ) + s * (x 3 w : ℂ) := by simp [Hm]
    change ‖Hm s w x 0 1‖ ≤ _
    rw [e]
    exact (norm_add_le _ _).trans (by nlinarith [hr 2])
  · have e : Hm s w x 1 0 = (x 2 w : ℂ) - s * (x 3 w : ℂ) := by simp [Hm]
    change ‖Hm s w x 1 0‖ ≤ _
    rw [e]
    exact (norm_sub_le _ _).trans (by nlinarith [hr 2])
  · have e : Hm s w x 1 1 = (x 0 w : ℂ) := by simp [Hm]
    change ‖Hm s w x 1 1‖ ≤ _
    rw [e]
    nlinarith [hr 0]

end

section

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem pt_bound {s : ℂ} (hs : s ≠ 0) (w : InfinitePlace F) (x x' : Fin 4 → TR.Rinf F)
    (Y Z : Matrix (Fin 2) (Fin 2) ℂ) (hZ : Y * Z = 1) (hx : Hm s w x' = Z * Hm s w x * Zᴴ)
    {t U : ℝ} (ht : 0 ≤ t) (hU : 0 ≤ U) (hY : ∀ i j, ‖Y i j‖ ≤ t) (h' : ∀ i, |x' i w| ≤ U) (i : Fin 4) :
    |x i w| ≤ (1 + ‖s‖⁻¹) * (4 * (1 + ‖s‖)) * (t ^ 2 * U) := by
  have e : Hm s w x = Y * Hm s w x' * Yᴴ := by
    calc Hm s w x = (Y * Z) * Hm s w x * (Y * Z)ᴴ := by rw [hZ]; simp
      _ = Y * Hm s w x' * Yᴴ := by
        rw [hx, Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
  have hH : ∀ i j, ‖Hm s w x i j‖ ≤ 4 * t ^ 2 * ((1 + ‖s‖) * U) := fun i j => by
    rw [e]
    exact entry_le _ _ ht (by positivity) hY (Hm_le s w x' hU h') i j
  have := co_le_Hm hs w x (by positivity) hH i
  calc |x i w| ≤ _ := this
    _ = _ := by ring

end

theorem UpperTheory.ConvolutionTheory.R2.Ff.wtAct :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E), WtAct D := by
  intro F E _ _ _ _ _ _ _ D
  have hθ : ∀ τ : E →+* ℂ, τ D.θ ≠ 0 := fun τ => (map_ne_zero τ).2 D.θ_ne_zero
  obtain ⟨A, hA0, hterm⟩ : ∃ A : ℝ, 0 ≤ A ∧
      ∀ τ : E →+* ℂ, (1 + ‖τ D.θ‖⁻¹) * (4 * (1 + ‖τ D.θ‖)) ≤ A :=
    ⟨∑ τ : E →+* ℂ, (1 + ‖τ D.θ‖⁻¹) * (4 * (1 + ‖τ D.θ‖)),
      Finset.sum_nonneg fun _ _ => by positivity, fun τ =>
        Finset.single_le_sum (f := fun τ : E →+* ℂ => (1 + ‖τ D.θ‖⁻¹) * (4 * (1 + ‖τ D.θ‖)))
          (fun _ _ => by positivity) (Finset.mem_univ τ)⟩
  refine ⟨A + 1, fun K N y v => ?_⟩
  have hHt : 1 ≤ Ht y := ((htLe E).2 y).1
  have hH2 : 1 ≤ Ht y ^ 2 := one_le_pow₀ hHt
  have hm1 : 1 ≤ (A + 1) * Ht y ^ 2 := by nlinarith
  rw [← map_inv]
  have hact := actInf F E D y⁻¹ v
  refine wt_le_of_norm hm1 hact.1 ?_
  have hU : 0 ≤ ‖infPartPi (D.act (infGL E 2 y⁻¹) v)‖ := norm_nonneg _
  refine norm_inf_le v (by positivity) fun i w => ?_
  obtain ⟨τ, rfl⟩ := exists_pl (E := E) w
  have hZ : y.val.map (coord τ) * (y⁻¹).val.map (coord τ) = 1 := by
    change (coord τ).mapMatrix y.val * (coord τ).mapMatrix (y⁻¹).val = 1
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hY : ∀ i j, ‖y.val.map (coord τ) i j‖ ≤ Ht y := fun i j => by
    have h1 : ‖coord τ (y.val i j)‖ = ‖y.val i j (InfinitePlace.mk τ)‖ := GlobalTheory.IsoPull.norm_coord τ _
    have h2 : ‖y.val i j (InfinitePlace.mk τ)‖ ≤ ‖toL y.val‖ :=
      (norm_le_pi_norm (y.val i j) _).trans
        ((norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i))
    have h3 : 0 ≤ ‖toL (y⁻¹).val‖ := norm_nonneg _
    rw [Matrix.map_apply, h1]
    unfold Ht
    linarith
  have key := pt_bound (hθ τ) (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ) (fun i => TR.pInf F (v i))
    (fun i => TR.pInf F (D.act (infGL E 2 y⁻¹) v i)) _ _ hZ (hact.2 τ) (by linarith) hU hY
    (fun i => abs_pInf_le _ i _) i
  refine key.trans ?_
  have hp : 0 ≤ Ht y ^ 2 * ‖infPartPi (D.act (infGL E 2 y⁻¹) v)‖ := by positivity
  calc _ ≤ A * (Ht y ^ 2 * ‖infPartPi (D.act (infGL E 2 y⁻¹) v)‖) :=
        mul_le_mul_of_nonneg_right (hterm τ) hp
    _ ≤ (A + 1) * Ht y ^ 2 * ‖infPartPi (D.act (infGL E 2 y⁻¹) v)‖ := by nlinarith
end

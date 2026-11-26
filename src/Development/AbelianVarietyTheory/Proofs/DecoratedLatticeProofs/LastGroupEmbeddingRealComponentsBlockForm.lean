module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergIntegralFourierBesselBasePointEqPairin
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMixedCoordinatesContinuousBoundedSupNormStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeRationalCosetSameOrbitIffLevel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSmulOfStableGraph
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesUnderEq
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastGroupEmbeddingRealComponentsBlockForm
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOfEntries
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix
open Formalism.L2.Theta GlobalTheory.Mem.Th Filter Topology MeasureTheory
open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.TC.BlockMatrixCriteria

theorem sum_ite_val {m : ℕ} (f : Fin m → ℂ) (c : ℕ) (hc : c < m) :
    ∑ j : Fin m, (if (j : ℕ) = c then f j else 0) = f ⟨c, hc⟩ := by
  rw [Finset.sum_eq_single ⟨c, hc⟩]
  · simp
  · intro j _ hj
    rw [if_neg]
    exact fun h => hj (Fin.ext h)
  · simp

theorem sum_ite_val_zero {m : ℕ} (f : Fin m → ℂ) (c : ℕ) (hc : m ≤ c) :
    ∑ j : Fin m, (if (j : ℕ) = c then f j else 0) = 0 :=
  Finset.sum_eq_zero fun j _ => if_neg (by have := j.2; omega)

theorem isBlock_of_frame {p q N n : ℕ} (hp : p = N) (hq : q = n) (hN : N = n + 1) (M : Matrix (Fin p) (Fin p) ℂ)
    (M' : Matrix (Fin q) (Fin q) ℂ)
    (h1 : M * Matrix.of (fun (i : Fin p) (a : Fin q) => if (i : ℕ) = a then (1 : ℂ) else 0) =
      Matrix.of (fun (i : Fin p) (a : Fin q) => if (i : ℕ) = a then (1 : ℂ) else 0) * M')
    (h2 : M *ᵥ (fun i : Fin p => if (i : ℕ) = q then (1 : ℂ) else 0) = fun i : Fin p => if (i : ℕ) = q then (1 : ℂ) else 0) :
    GlobalTheory.BranchFormula.IsBlock hN (fun i j : Fin N => M (Fin.cast hp.symm i) (Fin.cast hp.symm j))
      (fun a b : Fin n => M' (Fin.cast hq.symm a) (Fin.cast hq.symm b)) 1 := by
  subst hp hq hN
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · have e := congrFun (congrFun h1 (Br.iC rfl a)) b
    simp only [Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul] at e
    simp only [eq_comm (a := ((Br.iC rfl a : Fin (q+1)) : ℕ))] at e
    rw [sum_ite_val _ _ (by have := b.2; omega), sum_ite_val _ _ (show ((Br.iC rfl a : Fin (q+1)) : ℕ) < q from a.2)] at e
    exact e
  · have e := congrFun h2 (Br.iC rfl a)
    simp only [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero] at e
    rw [sum_ite_val _ _ (by omega), if_neg (by have := a.2; simp [Br.iC]; omega)] at e
    exact e
  · have e := congrFun (congrFun h1 (Br.iL rfl)) a
    simp only [Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul] at e
    simp only [eq_comm (a := ((Br.iL rfl : Fin (q+1)) : ℕ))] at e
    rw [sum_ite_val _ _ (by have := a.2; omega), sum_ite_val_zero _ _ (by simp [Br.iL])] at e
    exact e
  · have e := congrFun h2 (Br.iL rfl)
    simp only [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero] at e
    rw [sum_ite_val _ _ (by omega), if_pos (by simp [Br.iL])] at e
    exact e

end GlobalTheory.Mem.Col2.TC.BlockMatrixCriteria

namespace GlobalTheory.Mem.Col2.TC.BlockMatrixCriteria

theorem isBlock_of_entries {p q N n : ℕ} (hp : p = N) (hq : q = n) (hN : N = n + 1) (M : Matrix (Fin p) (Fin p) ℂ)
    (M' : Matrix (Fin q) (Fin q) ℂ) (A : Matrix (Fin N) (Fin N) ℂ) (A' : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A i j = M (Fin.cast hp.symm i) (Fin.cast hp.symm j))
    (hA' : ∀ i j, A' i j = M' (Fin.cast hq.symm i) (Fin.cast hq.symm j))
    (h1 : M * Matrix.of (fun (i : Fin p) (a : Fin q) => if (i : ℕ) = a then (1 : ℂ) else 0) =
      Matrix.of (fun (i : Fin p) (a : Fin q) => if (i : ℕ) = a then (1 : ℂ) else 0) * M')
    (h2 : M *ᵥ (fun i : Fin p => if (i : ℕ) = q then (1 : ℂ) else 0) = fun i : Fin p => if (i : ℕ) = q then (1 : ℂ) else 0) :
    GlobalTheory.BranchFormula.IsBlock hN A A' 1 := by
  have e1 : A = fun i j => M (Fin.cast hp.symm i) (Fin.cast hp.symm j) := funext fun i => funext fun j => hA i j
  have e2 : A' = fun i j => M' (Fin.cast hq.symm i) (Fin.cast hq.symm j) := funext fun i => funext fun j => hA' i j
  subst e1 e2
  exact isBlock_of_frame hp hq hN M M' h1 h2

end GlobalTheory.Mem.Col2.TC.BlockMatrixCriteria

namespace GlobalTheory.Mem.Col2.TC

end GlobalTheory.Mem.Col2.TC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastGroupEmbeddingRealComponentsBlockForm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EmbTopBlock

theorem iXm_entry {D : D7}
    (hi : ∀ (a : Fin D.sp.X'.rank) (b : Fin (D.sp.X D.R.m).rank), (a : ℕ) = b →
      D.sp.iX' (D.sp.X'.frame a) = (D.sp.X D.R.m).frame b)
    (i : Fin (D.R.N D.R.m)) (b : Fin (D.R.N D.R.m - 1)) :
    iXm D i b = if (i : ℕ) = b then 1 else 0 := by
  have hP' : D.sp.X'.rank = D.R.N D.R.m - 1 := rankP D
  have hN' : (D.sp.X D.R.m).rank = D.R.N D.R.m := rankN D D.R.m le_rfl
  have hb : (b : ℕ) < D.sp.X'.rank := by have := b.2; omega
  have hb2 : (b : ℕ) < (D.sp.X D.R.m).rank := by have := b.2; omega
  have key : D.sp.iX' (D.sp.X'.frame ⟨b, hb⟩) = (D.sp.X D.R.m).frame ⟨b, hb2⟩ := hi _ _ rfl
  rw [iXm, LinearMap.toMatrix'_apply, iXc]
  have hs : (D.sp.X'.frame.equivFun.trans
      (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)).symm
      (Pi.single b 1) = D.sp.X'.frame ⟨b, hb⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    ext j
    simp only [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, Module.Basis.equivFun_apply, Module.Basis.repr_self,
      Pi.single_apply, Finsupp.single_apply, Fin.ext_iff, Fin.val_cast, finCongr_symm, finCongr_apply, Fin.coe_cast, LinearMap.funLeft_apply, Function.comp_apply]
    split_ifs <;> first | rfl | (exfalso; omega)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hs, key]
  simp only [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, Module.Basis.equivFun_apply, Module.Basis.repr_self,
      Pi.single_apply, Finsupp.single_apply, Fin.ext_iff, Fin.val_cast, finCongr_symm, finCongr_apply, Fin.coe_cast, LinearMap.funLeft_apply, Function.comp_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

end GlobalTheory.EmbTopBlock

namespace GlobalTheory.EmbTopBlock

theorem piT_coe_ne_zero {B : GlobalTheory.Mem.Base} (X : PreX B.toPre) (u : B.Word) : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := by
  intro h0
  have hn := X.piT_norm u
  rw [h0, zero_mul] at hn
  have hT : B.T u = 0 := by exact_mod_cast hn.symm
  have h1 := X.T_gt u
  have h2 := X.a_gt
  rw [hT] at h1
  have h3 := h2.trans h1
  exact (Nat.not_lt_zero _) (by exact_mod_cast h3)

theorem isBlock_infM_emb : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (θ : InfFam (I.rec7 l Z)), IsInfFam θ → ∀ (emb : GA (I.rec7 l Z) (I.rec7 l Z).sp.X' →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m)) (hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1), IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) emb → ∀ (k : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') (τ : (I.rec7 l Z).what₂.Tau), GlobalTheory.BranchFormula.IsBlock hN (infM θ _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb k) τ) (infM θ _ (rankP (I.rec7 l Z)) k τ) 1 := by
  intro B X I _hOk hP l Z u θ _hθ emb hN hemb k τ
  obtain ⟨h1, h2⟩ := hemb k
  let q : AE (I.rec7 l Z) →+* ℂ := (θ τ).comp (infPart (I.rec7 l Z))
  let p : (I.rec7 l Z).host.E →+* ℂ := q.comp (incA (I.rec7 l Z))
  let G : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) ℂ := infM θ _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb k) τ
  let G' : Matrix (Fin (B.R.N B.R.m - 1)) (Fin (B.R.N B.R.m - 1)) ℂ := infM θ _ (rankP (I.rec7 l Z)) k τ
  let J : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m - 1)) ℂ := (iXm (I.rec7 l Z)).map p
  have hF : J = Matrix.of (fun (i : Fin (B.R.N B.R.m)) (a : Fin (B.R.N B.R.m - 1)) => if (i : ℕ) = a then (1 : ℂ) else 0) := by
    ext i a
    show p (iXm (I.rec7 l Z) i a) = if (i : ℕ) = a then (1 : ℂ) else 0
    rw [iXm_entry (D := I.rec7 l Z) hP.iX i a]
    split_ifs <;> simp
  have e1 : G * J = J * G' := by
    have := congrArg (fun M => Matrix.map M q) h1
    simp only [Matrix.map_mul, Matrix.map_map] at this
    exact this
  rw [hF] at e1
  have e2 : G *ᵥ (fun a : Fin (B.R.N B.R.m) => p (TC.z0 X u a)) = fun a => p (TC.z0 X u a) := by
    funext i
    have := congrArg q (congrFun h2 i)
    exact (RingHom.map_mulVec q _ _ i).symm.trans this
  have hc0 : p ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := (map_ne_zero p).2 (piT_coe_ne_zero X u)
  have hz : (fun a : Fin (B.R.N B.R.m) => p (TC.z0 X u a)) =
      p ((X.piT u : 𝓞 B.host.E) : B.host.E) •
        (fun i : Fin (B.R.N B.R.m) => if (i : ℕ) = B.R.N B.R.m - 1 then (1 : ℂ) else 0) := by
    funext i
    simp only [TC.z0, Pi.smul_apply, smul_eq_mul]
    have := i.2
    by_cases h : (i : ℕ) + 1 = B.R.N B.R.m
    · rw [if_pos h, if_pos (by omega), mul_one]
    · rw [if_neg h, if_neg (by omega), mul_zero]
      exact map_zero p
  rw [hz, Matrix.mulVec_smul] at e2
  have e2' := smul_right_injective _ hc0 e2
  exact TC.BlockMatrixCriteria.isBlock_of_entries rfl rfl hN G G' _ _ (fun _ _ => rfl) (fun _ _ => rfl) e1 e2'

end GlobalTheory.EmbTopBlock
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastGroupEmbeddingRealComponentsBlockFormStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastGroup_embedding_real_components_block_form : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (θ : InfFam (I.rec7 l Z)), IsInfFam θ → ∀ (emb : GA (I.rec7 l Z) (I.rec7 l Z).sp.X' →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m)) (hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1), IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) emb → ∀ (k : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') (τ : (I.rec7 l Z).what₂.Tau), GlobalTheory.BranchFormula.IsBlock hN (infM θ _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb k) τ) (infM θ _ (rankP (I.rec7 l Z)) k τ) 1 := by
  first | exact @GlobalTheory.EmbTopBlock.isBlock_infM_emb | exact GlobalTheory.EmbTopBlock.isBlock_infM_emb | (intros; apply GlobalTheory.EmbTopBlock.isBlock_infM_emb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedTermBasePointEqFlatMapPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedTermBasePointEqFlatMapPairing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.FlatBase

variable {D : D7}

theorem continuous_psiUni {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) (ρ : ℕ) :
    Continuous fun u : UX D ρ => psiUni ψ u.1 := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun u : UX D ρ => (u.1.1 : Mx D ρ ρ) := Units.continuous_val.comp continuous_subtype_val
  have hu : Continuous fun u : UX D ρ => upSum (u.1.1 : Mx D ρ ρ) := by
    unfold upSum
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    split_ifs
    · exact (continuous_apply j).comp ((continuous_apply i).comp hc)
    · exact continuous_const
  exact hψ.comp (ht.comp hu)

theorem integral_swap_of_majorant {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) (μ : Measure β) [IsFiniteMeasure μ] (K : α → β → ℂ)
    (hK : StronglyMeasurable (Function.uncurry K)) (M : α → ℝ) (hM : Integrable M ν) (C : ℝ)
    (hb : ∀ u v, ‖K u v‖ ≤ M u * C) :
    ∫ u, ∫ v, K u v ∂μ ∂ν = ∫ v, ∫ u, K u v ∂ν ∂μ := by
  obtain ⟨t, htm, hMt, hσ⟩ := hM.aefinStronglyMeasurable.exists_set_sigmaFinite
  have h0 : ∀ᵐ u ∂ν, u ∈ tᶜ → M u = 0 := (ae_restrict_iff' htm.compl).1 hMt
  have hz : ∀ᵐ u ∂ν, u ∉ t → ∀ v, K u v = 0 := h0.mono fun u hu hut v => by
    have h := hb u v
    rw [hu hut, zero_mul] at h
    exact norm_le_zero_iff.1 h
  have e1 : ∫ u, ∫ v, K u v ∂μ ∂ν = ∫ u in t, ∫ v, K u v ∂μ ∂ν :=
    (setIntegral_eq_integral_of_ae_compl_eq_zero (hz.mono fun u hu hut => by simp [hu hut])).symm
  have e2 : (fun v => ∫ u, K u v ∂ν) = fun v => ∫ u in t, K u v ∂ν := funext fun v =>
    (setIntegral_eq_integral_of_ae_compl_eq_zero (hz.mono fun u hu hut => hu hut v)).symm
  rw [e1, e2]
  haveI := hσ
  refine integral_integral_swap ?_
  refine Integrable.mono' ((hM.restrict (s := t)).mul_prod (integrable_const C)) hK.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun p => hb p.1 p.2

end GlobalTheory.FlatBase

namespace GlobalTheory.Unf.FB

open GlobalTheory.FlatBase

theorem fl_base_eq_tFlat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vb : VolM D (σ + 1) J.W₀.rank) (vL : VolM D B.L.rank J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ), Quasi ψ J.W₀ B.L y → IsThetaFunO ψ J.W B.V Ψ → fl ψ J.d B.V s.vS vb s.vU (th J ψ B y) (x0 B) Ψ = tFlat s vL y Ψ ∧ ∀ M : ℝ, (∀ w, ‖y w‖ ≤ M) → ‖tFlat s vL y Ψ‖ₑ ≤ ENNReal.ofReal M * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (x0 B ⬝ u.1.1) (x0 B ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν := by
  intro D ψ σ J B s vb vL y Ψ hy hΨ
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  have hchar := hstd.1
  obtain ⟨-, ⟨My, hMy, -⟩, -, -, -, hlaw⟩ := GlobalTheory.T.fourierBesselThetaCharIntegrand_laws D ψ hstd σ J B y hy
  have hnorm : ∀ u : UX D (σ + 1), ‖psiUni ψ u.1‖ = 1 := fun u => hchar.2.1 _

  have hfl : ∀ u : UX D (σ + 1), (∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (th J ψ B y) (x0 B) Ψ u b ∂vb.μ) =
      star (psiUni ψ u.1) * ∫ v in vL.𝓕, evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (x0 B ⬝ u.1.1) 0
        ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ := by
    intro u
    have hf : Quasi ψ J.W₀ B.V (J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (x0 B ⬝ u.1.1)) := by
      have h := (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hstd).1 J.W J.W₀ B.V (σ + 1) J.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ (x0 B ⬝ u.1.1)
      exact ⟨h.quasi, h.cont⟩
    have hh := (GlobalTheory.T.heisenbergIntegral_fourierBesselBasePoint_eq_pairing D ψ hstd σ J.W₀ B vb s.vT vL _ y hf hy).1
    calc (∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (th J ψ B y) (x0 B) Ψ u b ∂vb.μ)
        = ∫ b in vb.𝓕, star (psiUni ψ u.1) * (J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (x0 B ⬝ u.1.1) (x0 B ⬝ b) *
            star (y (zl B ⬝ b))) ∂vb.μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
          simp only [flFun]
          rw [hlaw b u.1 u.2]
          simp only [I195MixedCoordinates_f1b992d3c44b213cc9f27f15.source, HypDec.mixS,
            HypDec.extX, HypDec.extY, HypDec.ext0, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
          ring
      _ = _ := by
          rw [integral_const_mul]
          exact congrArg (star (psiUni ψ u.1) * ·) hh
  have hLeft : fl ψ J.d B.V s.vS vb s.vU (th J ψ B y) (x0 B) Ψ = ∫ u, star (psiUni ψ u.1) *
      ∫ v in vL.𝓕, evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (x0 B ⬝ u.1.1) 0
        ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ ∂s.vU.ν := by
    unfold fl
    exact integral_congr_ae (Filter.Eventually.of_forall hfl)

  obtain ⟨x, hxo, hx⟩ := GlobalTheory.T.exists_mem_orb_rat_eq_x0 D σ B
  obtain ⟨M, hMi, hMb⟩ := GlobalTheory.T.flatThetaIntegrand_locallyUniform_majorant D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil s.vU x
    hxo.1 Ψ hΨ {1} isCompact_singleton
  have hom1 : s.om 1 Ψ = Ψ := by rw [map_one]; rfl
  have hbound : ∀ (u : UX D (σ + 1)) (v : WO J.W₀ B.L),
      ‖flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v)‖ ≤
        M u * My := by
    intro u v
    have h := hMb 1 (Set.mem_singleton 1) 0 ((B.o.resT J.W₀).symm (0, v)) u
    rw [hx, hom1] at h
    rw [norm_mul, norm_star]
    exact mul_le_mul h (hMy v) (norm_nonneg _) ((norm_nonneg _).trans h)
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : BorelSpace (UX D (σ + 1)) := ⟨rfl⟩
  have : BorelSpace (WO J.W₀ B.L) := ⟨rfl⟩
  have : SecondCountableTopology (WO J.W₀ B.L) := (lattice_Mx D B.L.rank J.W₀.rank).2.2.1
  have hE : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L =>
      evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (x0 B ⬝ p.1.1.1) 0 ((B.o.resT J.W₀).symm (0, p.2)) := by
    have hmc := (GlobalTheory.T.weilMixedCoordinates_continuous_bounded_supNorm D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil Ψ hΨ).2
    have hc : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L => (p.1.1.1 : Mx D (σ + 1) (σ + 1)) :=
      (Units.continuous_val.comp continuous_subtype_val).comp continuous_fst
    have hin : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L =>
        ((1 : GA D J.W × GA D B.V), x0 B ⬝ p.1.1.1, (0 : Mx D J.W₀.rank σ), (B.o.resT J.W₀).symm (0, p.2)) :=
      continuous_const.prodMk ((continuous_const.matrix_mul hc).prodMk (continuous_const.prodMk
        ((B.o.continuous_resT_symm J.W₀).comp (continuous_const.prodMk continuous_snd))))
    have h := hmc.comp hin
    simpa only [Function.comp_def, hom1] using h
  have hK : Continuous (Function.uncurry fun (u : UX D (σ + 1)) (v : WO J.W₀ B.L) =>
      flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v)) :=
    ((continuous_star.comp ((continuous_psiUni hchar.1 (σ + 1)).comp continuous_fst)).mul hE).mul
      (continuous_star.comp (hy.2.comp continuous_snd))
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) := isFiniteMeasure_restrict.2 (by rw [vL.covol.2.2]; simp)
  have hswap := integral_swap_of_majorant s.vU.ν (vL.μ.restrict vL.𝓕) (fun u v =>
      flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v))
    hK.stronglyMeasurable M hMi My hbound
  have h1 : fl ψ J.d B.V s.vS vb s.vU (th J ψ B y) (x0 B) Ψ = tFlat s vL y Ψ := by
    rw [hLeft]
    calc (∫ u, star (psiUni ψ u.1) * ∫ v in vL.𝓕, evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (x0 B ⬝ u.1.1) 0
            ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ ∂s.vU.ν)
        = ∫ u, ∫ v in vL.𝓕, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u *
            star (y v) ∂vL.μ ∂s.vU.ν := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          dsimp only
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
          simp only [flatFun]
          ring
      _ = ∫ v in vL.𝓕, ∫ u, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u *
            star (y v) ∂s.vU.ν ∂vL.μ := hswap
      _ = ∫ v in vL.𝓕, (∫ u, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (x0 B) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u
            ∂s.vU.ν) * star (y v) ∂vL.μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun v => integral_mul_const _ _)
      _ = tFlat s vL y Ψ := rfl
  refine ⟨h1, fun Mb hMb' => ?_⟩
  rw [← h1]
  unfold fl
  calc ‖∫ u, ∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (th J ψ B y) (x0 B) Ψ u b ∂vb.μ ∂s.vU.ν‖ₑ
      ≤ ∫⁻ u, ‖∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (th J ψ B y) (x0 B) Ψ u b ∂vb.μ‖ₑ ∂s.vU.ν :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ u, ∫⁻ b in vb.𝓕, ‖flFun ψ J.d B.V s.vS (th J ψ B y) (x0 B) Ψ u b‖ₑ ∂vb.μ ∂s.vU.ν :=
        lintegral_mono fun u => enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ u, ∫⁻ b in vb.𝓕, ENNReal.ofReal Mb *
          ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (x0 B ⬝ u.1.1) (x0 B ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν := by
        refine lintegral_mono fun u => lintegral_mono fun b => ?_
        simp only [flFun]
        rw [enorm_mul]
        gcongr
        · rw [hlaw b u.1 u.2, ← ofReal_norm_eq_enorm, norm_mul, norm_star, norm_star, hnorm u, one_mul]
          exact ENNReal.ofReal_le_ofReal (hMb' _)
        · simp only [I195MixedCoordinates_f1b992d3c44b213cc9f27f15.source, HypDec.mixS,
            HypDec.extX, HypDec.extY, HypDec.ext0, AddMonoidHom.coe_mk, ZeroHom.coe_mk, le_refl]
    _ = _ := (lintegral_congr fun u => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)

end GlobalTheory.Unf.FB

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedTermBasePointEqFlatMapPairingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedTerm_basePoint_eq_flatMap_pairing : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vb : VolM D (σ + 1) J.W₀.rank) (vL : VolM D B.L.rank J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ), Quasi ψ J.W₀ B.L y → IsThetaFunO ψ J.W B.V Ψ → fl ψ J.d B.V s.vS vb s.vU (th J ψ B y) (x0 B) Ψ = tFlat s vL y Ψ ∧ ∀ M : ℝ, (∀ w, ‖y w‖ ≤ M) → ‖tFlat s vL y Ψ‖ₑ ≤ ENNReal.ofReal M * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (x0 B ⬝ u.1.1) (x0 B ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν := by
  first | exact @GlobalTheory.Unf.FB.fl_base_eq_tFlat | exact GlobalTheory.Unf.FB.fl_base_eq_tFlat | (intros; apply GlobalTheory.Unf.FB.fl_base_eq_tFlat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalCongruenceFixesDefiniteStepVector
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalCongruenceFixesDefiniteStepVector
noncomputable section

namespace GlobalTheory.SmallFix

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isDetRoot_one (V : HSp D) : IsDetRoot V (1 : GA D V) (1 : (AE D)ˣ) := by
  show ((1 : (AE D)ˣ) : AE D) = _
  rw [map_one, Units.val_one]
  simp

theorem suppPl_one (ε : AF D.host.F) (V : HSp D) : SuppPl ε V (1 : GA D V) := fun i j => by
  rw [GlobalTheory.AdelicLatMove.mt_one, sub_self, Matrix.zero_apply, mul_zero]

theorem suppAt_one (e : AE D) (V : HSp D) : Formalism.L2.Theta.SuppAt e V (1 : GA D V) := fun i j => by
  rw [GlobalTheory.AdelicLatMove.mt_one, sub_self, Matrix.zero_apply, mul_zero]

theorem inert_one {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {χS : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS 1 om)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hη : ∃ η, IsEtaTilde D η)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : NonSplitAt D v ε) (g : GA D S) (hg : SuppPl ε S g)
    (hst : ∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔
      actO S T g 1 u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True))
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f) :
    om (g, 1) f = f := by
  obtain ⟨η, hη⟩ := hη
  have hψ := hW.std
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨om₀, h0, hv, -⟩ := GlobalTheory.T.exists_weilDatum_powers_unramifiedEtaTilde D ψ hψ S T θ hθ ΛS ΛT hS hT η hη
  obtain ⟨om₁, h1, htw⟩ := GlobalTheory.T.exists_weilDatum_twist_heckeCharacters D ψ hψ S T _ _ ((η ^ S.rank)⁻¹ * χS) ((η ^ T.rank)⁻¹ * 1) om₀ h0
    (GlobalTheory.VacInert.hecke_quot hW.hecS h0.hecS) (GlobalTheory.VacInert.hecke_quot hW.hecT h0.hecT)
    (GlobalTheory.VacInert.resEta_quot hW.resS h0.resS) (GlobalTheory.VacInert.resEta_quot hW.resT h0.resT)
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at h1
  obtain ⟨x, hx, xi, -, x1, x2⟩ := GlobalTheory.VacInert.exists_unit_root hε S g hg
  have hlat : ∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v) ↔
      actO S T g 1 u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v) := fun u => by
    rw [GlobalTheory.VecInvInert.mem_place_iff hε.1, GlobalTheory.VecInvInert.mem_place_iff hε.1, ← hst, ← GlobalTheory.FinWeilO.actO_smul,
      (GlobalTheory.VecInvInert.act_injective g 1).eq_iff]
  have hfix : ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v),
      heisO ψ S T u f = f := fun u hu => by
    obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hε
    have e1 : 2 • (a • u) = u := by
      rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.VecInvInert.idem_smul_eq hε.1 hu]
    have e2 := hvac.1 (a • u)
      (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u (GlobalTheory.PlaceModel.latO_le_top _ hu))
    rwa [e1] at e2
  rw [GlobalTheory.T.weilDatum_unique_on_thetaFunctions D ψ hψ S T χS 1 om om₁ hW h1 _ f hf, htw g 1 x 1 hx (isDetRoot_one T), LinearMap.smul_apply,
    hv v ε hε g 1 hg (suppPl_one ε T) hlat f hf hfix]
  simp [hη.2.1 x xi x1 x2]

theorem local_one {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {χS : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS 1 om)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hη : ∃ η, IsEtaTilde D η)
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} (frS : IsFrame βS ΛS) (frT : IsFrame βT ΛT)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) (g : GA D S) (hg : Stab S βS g)
    (sg : SuppPl ε S g) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f) :
    om (g, 1) f = f := by
  have hlat := mem_latO_iff frS frT (h := (1 : GA D T)) hg.2 (Stab.one T βT).2
  by_cases hsp : ∃ e', IsSplitIdem D e' ∧ e' + cA D e' = algebraMap (AF D.host.F) (AE D) ε
  · obtain ⟨e', he', hb⟩ := hsp
    have := GlobalTheory.T.splitPlace_weilRep_latticeVacuum_character D ψ S T ΛS ΛT χS 1 om hW hS hT e' he' g 1 (fun i j => by rw [hb]; exact sg i j)
      (suppAt_one e' T) hlat _ _ (isDetAt_detAt e' he'.1 S g) (isDetAt_detAt e' he'.1 T 1) f hf hvac
    rw [this, splitFacO, map_one, map_one, MonoidHom.one_apply, inv_one, one_mul, Circle.coe_one, one_smul]
  · exact inert_one hW hS hT hη ⟨hε, hsp⟩ g sg hlat f hf hvac

theorem vac_one {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {χS : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS 1 om)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hη : ∃ η, IsEtaTilde D η)
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} (frS : IsFrame βS ΛS) (frT : IsFrame βT ΛT)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f)
    (g : GA D S) (hg : Stab S βS g) : om (g, 1) f = f := by
  let H : Subgroup (GA D S × GA D T) :=
    { carrier := {p | om (p.1, 1) f = f}
      one_mem' := by
        change om ((1 : GA D S), (1 : GA D T)) f = f
        rw [Prod.mk_one_one, map_one, Module.End.one_apply]
      mul_mem' := fun {p q} hp hq => by
        change om ((p * q).1, (1 : GA D T)) f = f
        have e : ((p * q).1, (1 : GA D T)) = (p.1, (1 : GA D T)) * (q.1, 1) := Prod.ext rfl (mul_one 1).symm
        have hq' : om (q.1, 1) f = f := hq
        have hp' : om (p.1, 1) f = f := hp
        rw [e, map_mul, Module.End.mul_apply, hq', hp']
      inv_mem' := fun {p} hp => by
        change om (p⁻¹.1, (1 : GA D T)) f = f
        have hp' : om (p.1, 1) f = f := hp
        have e : (p⁻¹.1, (1 : GA D T)) = (p.1, (1 : GA D T))⁻¹ := Prod.ext rfl inv_one.symm
        rw [e]
        calc om (p.1, (1 : GA D T))⁻¹ f = om (p.1, (1 : GA D T))⁻¹ (om (p.1, 1) f) := by rw [hp']
          _ = f := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hcl : IsClosed (H : Set (GA D S × GA D T)) := by
    have : (H : Set (GA D S × GA D T)) = ⋂ w, {p | om (p.1, 1) f w = f w} := by
      ext p
      rw [Set.mem_iInter]
      exact funext_iff
    rw [this]
    exact isClosed_iInter fun w => isClosed_eq
      ((hW.om_cont f hf w).comp (continuous_fst.prodMk continuous_const)) continuous_const
  exact GlobalTheory.T.mem_closedSubgroup_of_localStabilizerPairs D S T βS βT H hcl (fun v ε hε g' h' hg' _ sg' _ =>
    local_one hW hS hT hη frS frT hε g' hg' sg' f hf hvac) g 1 hg (Stab.one T βT)

end GlobalTheory.SmallFix

end

noncomputable section

namespace GlobalTheory.SmallFix

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes _root_.Formalism.L2.Theta _root_.Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW


set_option maxHeartbeats 1000000 in
open Classical in
theorem prin_fixes_stepVec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∀ (βH : GL (Fin H.rank) (Formalism.IndefR.Lev.EAf D)) (f₀ f : WO A H → ℂ), Formalism.L2.DIV.IsFrame βH (frameLat H) → IsStepVecOf ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) ∅ (fun _ => 1) f₀ f → IsThetaFunO ψ A H f → ∀ κ ∈ prin A β Z, om (κ, 1) f = f := by
  intro D ψ θ A H χA om sA sH hθ hη hW cA' cH hrk β Z hPl βH f₀ f hfrH hv hthf κ hκ
  obtain ⟨hf, e, he, hΘ⟩ := hv
  have dA := frameLat_isSelfDualC A
  have dH := frameLat_isSelfDualC H
  have hlev : Formalism.IndefR.Lev.finE A κ ∈ Formalism.L2.DIV.lev D.sp.cm A.gram β (prinDat A Z) := hκ.2
  have sg : Formalism.IndefR.Lev.finE A κ ∈ Formalism.L2.DIV.St β := Formalism.L2.DIV.parLev_St hlev.1
  have sh : Formalism.IndefR.Lev.finE H 1 ∈ Formalism.L2.DIV.St βH := by rw [map_one]; exact Subgroup.one_mem _
  have h1 : om (κ, 1) f₀ = (1 : ℂ) • f₀ := by
    rw [one_smul]
    exact GlobalTheory.SmallFix.vac_one hW dA dH hη hPl.frame hfrH f₀ hf.2.theta hf.2.lat κ ⟨hκ.1, sg⟩
  have hoG := GlobalTheory.T.levelPlacesDatum_mul_right_source_level D A.rank H.rank (prinDat A Z) (fun _ => 1)
    (fun PP => Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE A κ)) (fun PP hP => Formalism.L2.DIV.parLev_g hlev.1 hP) hlev.2
  have h2 := GlobalTheory.T.weilRep_theta_datum_half_eq_smul D ψ A H χA 1 om hW e _ f₀ _ f
    (GlobalTheory.T.schrodingerIntertwiner_schwartzBruhat_isTheta D ψ hW.std A H (frameLat A) (frameLat H) dA dH e (GlobalTheory.PlaceDatum.idemSum_mul_self he)
      (GlobalTheory.PlaceDatum.infPart_idemSum he) f₀ hf.2.theta) hΘ κ 1
    (GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem D A H (frameLat A) (frameLat H) β βH dA dH hPl.frame hfrH κ 1 sg sh) 1 1 one_ne_zero h1 (fun x => by
      obtain ⟨i1, i2⟩ := GlobalTheory.T.frameMatrix_movedHom_integral_reductions D A H β βH κ 1 sg sh x
      have i0 : Formalism.IndefR.Datum.IsHalf e (actO A H κ⁻¹ 1⁻¹ x) ↔ Formalism.IndefR.Datum.IsHalf e x :=
        ⟨fun H' => GlobalTheory.AdelicLatMove.actO_actO_inv A H κ 1 x ▸ GlobalTheory.SplitHecke.isHalf_actO κ 1 H',
          fun H' => GlobalTheory.SplitHecke.isHalf_actO _ _ H'⟩
      by_cases hx : Formalism.IndefR.Datum.IsHalf e x ∧ Formalism.IndefR.Datum.IsIntM (frMapO A H β βH x)
      · beta_reduce
        rw [if_pos hx, if_pos ⟨i0.2 hx.1, i1.2 hx.2⟩, funext (i2 hx.2), GlobalTheory.ChainOnto.StepLevLaw.omegaQ_empty,
          GlobalTheory.ChainOnto.StepLevLaw.omegaQ_empty, mul_one, mul_one]
        simp only [map_one, Formalism.L2.DIV.redFn_one, inv_one, Units.val_one, Matrix.one_mul]
        rw [hoG]
        congr 1
        rw [show (prinDat A Z).s = 0 from rfl, Finset.range_zero]
        simp only [Finset.prod_empty, Finset.prod_const_one, MonoidHom.one_apply, inv_one, mul_one]
        exact (congrArg Units.val (show (prinDat A Z).P.chi _ = 1 from rfl)).trans Units.val_one
      · beta_reduce
        rw [if_neg hx, if_neg fun H' => hx ⟨i0.1 H'.1, i1.1 H'.2⟩, mul_zero])
  rw [h2, mul_one, one_smul]

end GlobalTheory.SmallFix

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalCongruenceFixesDefiniteStepVectorStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruence_fixes_definiteStepVector : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∀ (βH : GL (Fin H.rank) (Formalism.IndefR.Lev.EAf D)) (f₀ f : WO A H → ℂ), Formalism.L2.DIV.IsFrame βH (frameLat H) → IsStepVecOf ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) ∅ (fun _ => 1) f₀ f → IsThetaFunO ψ A H f → ∀ κ ∈ prin A β Z, om (κ, 1) f = f := by
  first | exact @GlobalTheory.SmallFix.prin_fixes_stepVec | exact GlobalTheory.SmallFix.prin_fixes_stepVec | (intros; apply GlobalTheory.SmallFix.prin_fixes_stepVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLevelIntegralTwist
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.CongFlag

open Formalism.MainNotions.S _root_.Formalism.L2.SG.HidaSetting _root_.Formalism.L2.SG.Pf.unitaryCongruence
open scoped Matrix

theorem core (I : AutInst) (g : ℕ) {r : ℕ} (e0 : Fin r → VA I) (z0 : VA I) (hz0 : z0 ∈ I.Lf)
    (hzz : ZMod' I g (hA I z0 z0 + 1)) (hze : ∀ a, ZMod' I g (hA I (e0 a) z0))
    (x : I.Gf) (hxK : x ∈ I.Kset) (hxz : InMod I g (Set.range e0) ((I.fmat x - 1) *ᵥ z0))
    (v v' : VA I) (hv : InAt I g g (v - z0)) (hv' : InAt I g g (v' - z0))
    (ε c c₂ : I.E ⊗[I.F] Af I.F) (hε : ε ∈ IntAf I.F I.E) (hc : c ∈ IntAf I.F I.E) (hc₂ : c₂ ∈ IntAf I.F I.E)
    (hyp : ε • (c • (I.fmat x *ᵥ v')) = ε • (c₂ • v)) :
    ∃ N : ℕ, N.Coprime g ∧ ZMod' I g (ε * (c - c₂) * (N : I.E ⊗[I.F] Af I.F)) := by
  obtain ⟨n, hn, hnv⟩ := hv
  obtain ⟨n', hn', hnv'⟩ := hv'
  refine ⟨n * n', Nat.Coprime.mul_left hn hn', ?_⟩

  have hQ : Mo I g (Set.range e0) ≤ Qs I g z0 := by
    refine sup_le (Submodule.span_le.2 ?_) (mL_Qs I g hz0)
    rintro _ ⟨a, rfl⟩
    show ZMod' I g (hA I z0 (e0 a))
    rw [hA_symm]; exact Z_sig I g (hze a)
  have hmL : mL I g ≤ Qs I g z0 := mL_Qs I g hz0
  have hxmL : ∀ w ∈ mL I g, I.fmat x *ᵥ w ∈ mL I g := fun w hw =>
    pres I hxK g ∅ (mL I g) (by simp) (by simp) le_rfl w (mL_Mo I hw)
  have hNint : ∀ m : ℕ, ((m : I.E ⊗[I.F] Af I.F)) ∈ IntAf I.F I.E := fun m => natCast_mem _ m

  have hA1 : ZMod' I g (((n * n' : ℕ) : I.E ⊗[I.F] Af I.F) * hA I z0 (I.fmat x *ᵥ v') + ((n * n' : ℕ) : I.E ⊗[I.F] Af I.F)) := by
    have e : I.fmat x *ᵥ v' = z0 + (I.fmat x - 1) *ᵥ z0 + I.fmat x *ᵥ (v' - z0) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
      abel
    have e2 : ((n * n' : ℕ) : I.E ⊗[I.F] Af I.F) * hA I z0 (I.fmat x *ᵥ (v' - z0)) =
        (n : I.E ⊗[I.F] Af I.F) * hA I z0 (I.fmat x *ᵥ ((n' : I.E ⊗[I.F] Af I.F) • (v' - z0))) := by
      rw [Matrix.mulVec_smul, hA_smul_right, Nat.cast_mul]; ring
    have h2 : ZMod' I g (hA I z0 ((I.fmat x - 1) *ᵥ z0)) := hQ hxz
    have h3 : ZMod' I g (hA I z0 (I.fmat x *ᵥ ((n' : I.E ⊗[I.F] Af I.F) • (v' - z0)))) := hmL (hxmL _ hnv')
    have h1 := Z_smul I g (hNint (n * n')) hzz
    have := Z_add I g (Z_add I g h1 (Z_smul I g (hNint (n * n')) h2)) (Z_smul I g (hNint n) h3)
    rw [e, hA_add_right, hA_add_right]
    convert this using 1
    rw [← e2]; ring
  have hA2 : ZMod' I g (((n * n' : ℕ) : I.E ⊗[I.F] Af I.F) * hA I z0 v + ((n * n' : ℕ) : I.E ⊗[I.F] Af I.F)) := by
    have e : v = z0 + (v - z0) := by abel
    have e2 : ((n * n' : ℕ) : I.E ⊗[I.F] Af I.F) * hA I z0 (v - z0) =
        (n' : I.E ⊗[I.F] Af I.F) * hA I z0 ((n : I.E ⊗[I.F] Af I.F) • (v - z0)) := by
      rw [hA_smul_right, Nat.cast_mul]; ring
    have h3 : ZMod' I g (hA I z0 ((n : I.E ⊗[I.F] Af I.F) • (v - z0))) := hmL hnv
    have h1 := Z_smul I g (hNint (n * n')) hzz
    have := Z_add I g h1 (Z_smul I g (hNint n') h3)
    rw [e, hA_add_right]
    convert this using 1
    rw [← e2]; ring

  have key : ε * (c * hA I z0 (I.fmat x *ᵥ v')) = ε * (c₂ * hA I z0 v) := by
    have := congrArg (fun w => hA I z0 w) hyp
    simp only [hA_smul_right] at this
    exact this
  have := Z_sub I g (Z_smul I g (mul_mem hε hc) hA1) (Z_smul I g (mul_mem hε hc₂) hA2)
  convert this using 1
  linear_combination (-((n * n' : ℕ) : I.E ⊗[I.F] Af I.F)) * key

end GlobalTheory.CongFlag

namespace GlobalTheory.CongFlag

open Formalism.MainNotions.S _root_.Formalism.L2.SG.HidaSetting

theorem res_eq {D : D7} (PP : Formalism.L2.DIV.Pl D.host.E) (g : ℕ) (hg : ((g : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (ε c c₂ : Formalism.IndefR.Lev.EAf D) (hε : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hε1 : Formalism.L2.DIV.resS D.host.F PP ⟨ε, hε⟩ = 1)
    (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (N : ℕ) (hN : N.Coprime g)
    (hZ : ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) g (ε * (c - c₂) * (N : Formalism.IndefR.Lev.EAf D))) :
    Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  obtain ⟨t, ht, he⟩ := hZ
  have hs : (⟨ε, hε⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * (⟨c, hc⟩ - ⟨c₂, hc₂⟩) * (N : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      (g : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨t, ht⟩ := Subtype.ext (by
    push_cast
    exact he)
  have hr := congrArg (Formalism.L2.DIV.resS D.host.F PP) hs
  simp only [map_mul, map_sub, map_natCast, hε1, one_mul] at hr
  have hg0 : ((g : ℕ) : Formalism.L2.DIV.kP PP) = 0 := by
    show ((g : 𝓞 D.host.E) : 𝓞 D.host.E ⧸ PP.asIdeal) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 hg
  have hN0 : ((N : ℕ) : Formalism.L2.DIV.kP PP) ≠ 0 := by
    intro h0
    have hNm : ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact h0
    have hco : IsCoprime ((N : ℤ) : 𝓞 D.host.E) ((g : ℤ) : 𝓞 D.host.E) :=
      (Nat.isCoprime_iff_coprime.2 hN).map (Int.castRingHom (𝓞 D.host.E))
    obtain ⟨a, b, hab⟩ := hco
    push_cast at hab
    apply PP.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hNm) (Ideal.mul_mem_left _ _ hg)
  rw [hg0, zero_mul] at hr
  exact sub_eq_zero.1 ((mul_eq_zero.1 hr).resolve_right hN0)

end GlobalTheory.CongFlag

namespace GlobalTheory.CongFlag
open Formalism.MainNotions.S _root_.Formalism.L2.SG.HidaSetting
open scoped Matrix

theorem finE_inv_val {D : D7} (y : GA D (D.sp.Y 0)) :
    ((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from y))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val =
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat (((Formalism.IndefR.RationalEmbedding.iota D) y).2)⁻¹ :=
  (congrArg Units.val (map_inv (Formalism.IndefR.Lev.finE (Yc D 0)) (show GA D (Yc D 0) from y)).symm).trans
    ((GlobalTheory.SeeConjGroup.fmat_iota_eq_finE (D := D) (y⁻¹ : GA D (D.sp.Y 0))).symm.trans
      (congrArg (fun p : (Formalism.IndefR.RationalEmbedding.inst D).GA => (Formalism.L2.SG.InstExistsPf.instOf D).fmat p.2) (map_inv (Formalism.IndefR.RationalEmbedding.iota D) y)))

theorem core_res {D : D7} {r : ℕ} (e0 : Fin r → VA (Formalism.L2.SG.InstExistsPf.instOf D)) (z0 : VA (Formalism.L2.SG.InstExistsPf.instOf D)) (g : ℕ) (hz0 : z0 ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf)
    (hzz : ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) g (hA (Formalism.L2.SG.InstExistsPf.instOf D) z0 z0 + 1)) (hze : ∀ a, ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) g (hA (Formalism.L2.SG.InstExistsPf.instOf D) (e0 a) z0))
    (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (hxK : x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset) (hxz : InMod (Formalism.L2.SG.InstExistsPf.instOf D) g (Set.range e0) (((Formalism.L2.SG.InstExistsPf.instOf D).fmat x - 1) *ᵥ z0))
    (v v' : VA (Formalism.L2.SG.InstExistsPf.instOf D)) (hv : InAt (Formalism.L2.SG.InstExistsPf.instOf D) g g (v - z0)) (hv' : InAt (Formalism.L2.SG.InstExistsPf.instOf D) g g (v' - z0))
    (PP : Formalism.L2.DIV.Pl D.host.E) (hg : ((g : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (ε c c₂ : Formalism.IndefR.Lev.EAf D) (hε : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hε1 : Formalism.L2.DIV.resS D.host.F PP ⟨ε, hε⟩ = 1)
    (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (M : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)) (w w' : Fin (Yc D 0).rank → Formalism.IndefR.Lev.EAf D)
    (hM : M = (Formalism.L2.SG.InstExistsPf.instOf D).fmat x) (hw : w = v) (hw' : w' = v')
    (hyp : ε • (c • (M *ᵥ w')) = ε • (c₂ • w)) :
    Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  subst hM hw hw'
  obtain ⟨N, hN, hZ⟩ := core (Formalism.L2.SG.InstExistsPf.instOf D) g e0 z0 hz0 hzz hze x hxK hxz w w' hv hv' ε c c₂ hε hc hc₂ hyp
  exact res_eq PP g hg ε c c₂ hε hε1 hc hc₂ N hN hZ


set_option maxHeartbeats 400000 in
theorem frame_facts {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = (Formalism.L2.SG.InstExistsPf.instOf D)) (hId : IdE X) :
    ∃ (e0 : Fin D.R.rS → VA (Formalism.L2.SG.InstExistsPf.instOf D)) (z0 : VA (Formalism.L2.SG.InstExistsPf.instOf D)), z0 ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ∧ ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) (hA (Formalism.L2.SG.InstExistsPf.instOf D) z0 z0 + 1) ∧
      (∀ a, ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) (hA (Formalism.L2.SG.InstExistsPf.instOf D) (e0 a) z0)) ∧
      (∀ κ ∈ rowJ X h, ∃ x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf, ((Formalism.IndefR.RationalEmbedding.iota D) κ).2 = x ∧ x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset ∧
        InMod (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) (Set.range e0) (((Formalism.L2.SG.InstExistsPf.instOf D).fmat x - 1) *ᵥ z0)) ∧
      ∀ u : D.what₂.Word, ∃ (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (z : VA (Formalism.L2.SG.InstExistsPf.instOf D)),
        ((Formalism.IndefR.RationalEmbedding.iota D) ((iotaX X h).symm (1, X.xu u))).2 = x ∧
        (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (X.ιE (X.zR u (Fin.cast (rank_eq X h) r)))) = z ∧
        InAt (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) (D.host.g 0 * D.host.g 1) ((Formalism.L2.SG.InstExistsPf.instOf D).fmat x⁻¹ *ᵥ z - z0) := by
  have hi : ∀ u, (iotaX X h) ((iotaX X h).symm (1, X.xu u)) = (1, X.xu u) := fun u => (iotaX X h).apply_symm_apply _
  obtain ⟨⟨I⟩, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq, lam_eq, ds, low, g_eq, g0_eq, Rph,
    Rph_spec, eX, fY, ee, ff, ef, Lb, Lb_perp, Lam_split, zu, zu_norm, zu_orth, zu_Lb, Fu, Fu_e, flagZVector, Fu_fixed,
    psiEf, psiEf_add, psiEf_int, psiEf_rat, e0, f0, z0, bw, bwd, ew, vectorsInLattice, basisApprox, gramIntegral, formsAtZero, weightVectorsIntegral, ew_idem,
    ew_orth, ew_int, ew_full, bw_w, bwd_w, bw_dual, latticeSpan, e_eq, xu, xu_fix, xu_z, xu_one, xu_K⟩ := X
  dsimp only at h
  subst h
  dsimp only at g_eq
  subst g_eq
  have hs : ∀ y : D.host.E, ιE.symm y = y := fun y => by
    have := eq_of_heq (hId (ιE.symm y))
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨e0, z0, vectorsInLattice.2.1, formsAtZero.1, fun a => (formsAtZero.2 a).1, fun κ hκ => ?_, fun u => ?_⟩
  · have hk : ((Formalism.IndefR.RationalEmbedding.iota D) κ).2 ∈ K2set (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) e0 z0 bw := hκ.2
    exact ⟨_, rfl, hk.1, hk.2.2.1⟩
  · refine ⟨xu u, incl (Formalism.L2.SG.InstExistsPf.instOf D) (crdOf (Formalism.L2.SG.InstExistsPf.instOf D) ιE bas (zu u)), congrArg Prod.snd (hi u), ?_, xu_z u⟩
    funext r
    show algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (ιE (ιE.symm (bas.repr (zu u) r))) =
      algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (ιE.symm (bas.repr (zu u) r))
    rw [RingEquiv.apply_symm_apply, hs]

theorem inv_mulVec_eq {D : D7} (y : GA D (D.sp.Y 0)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (hx : ((Formalism.IndefR.RationalEmbedding.iota D) y).2 = x)
    (w : Fin (Yc D 0).rank → Formalism.IndefR.Lev.EAf D) (z : VA (Formalism.L2.SG.InstExistsPf.instOf D)) (hz : w = z) :
    Matrix.mulVec ((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from y))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val w =
      ((Formalism.L2.SG.InstExistsPf.instOf D).fmat x⁻¹ *ᵥ z : VA (Formalism.L2.SG.InstExistsPf.instOf D)) := by
  subst hx hz
  exact congrArg (fun M : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D) => Matrix.mulVec M w) (finE_inv_val y)


set_option maxHeartbeats 400000 in
theorem finiteRing_sq_sub_mul_sq_eq_of_card {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hId : IdE X)
    (u u' : D.what₂.Word) (κ : GA D (D.sp.Y 0)) (hκ : κ ∈ rowJ X h)
    (c c₂ : Formalism.IndefR.Lev.EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (PP : Formalism.L2.DIV.Pl D.host.E) (hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (ε : Formalism.IndefR.Lev.EAf D) (hε : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hε1 : Formalism.L2.DIV.resS D.host.F PP ⟨ε, hε⟩ = 1)
    (hE : ε • (c • Matrix.mulVec (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from κ)).val (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX X h).symm (1, X.xu u'))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (X.ιE (X.zR u' (Fin.cast (rank_eq X h) r)))))) = ε • (c₂ • (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX X h).symm (1, X.xu u))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (X.ιE (X.zR u (Fin.cast (rank_eq X h) r))))))) :
    Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  obtain ⟨e0, z0, hz0, hzz, hze, hK, hu⟩ := frame_facts X h hId
  obtain ⟨x, hx, hxK, hxz⟩ := hK κ hκ
  obtain ⟨y, z, hy, hz, hv⟩ := hu u
  obtain ⟨y', z', hy', hz', hv'⟩ := hu u'
  have e1 : (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from κ)).val = (Formalism.L2.SG.InstExistsPf.instOf D).fmat x :=
    (GlobalTheory.SeeConjGroup.fmat_iota_eq_finE (D := D) κ).symm.trans (congrArg (Formalism.L2.SG.InstExistsPf.instOf D).fmat hx)
  have e2 := inv_mulVec_eq _ y hy _ z hz
  have e3 := inv_mulVec_eq _ y' hy' _ z' hz'
  exact core_res e0 z0 _ hz0 hzz hze x hxK hxz _ _ hv hv' PP hg ε c c₂ hε hε1 hc hc₂ _ _ _ e1 e2 e3 hE

end GlobalTheory.CongFlag

namespace GlobalTheory.CongFlag

end GlobalTheory.CongFlag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemPerOInfHalfAO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HalfAConj
open GlobalTheory.LatVac

theorem conjPl_eq_conjP {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.L2.DIV.conjPl P = Formalism.L2.Col.conjPrime₂ P := by
  apply HeightOneSpectrum.ext
  apply Ideal.ext
  intro r
  show Formalism.L2.DIV.starOHom r ∈ P.asIdeal ↔ Formalism.L2.Col.cO E r ∈ P.asIdeal
  have : Formalism.L2.DIV.starOHom r = Formalism.L2.Col.cO E r := by
    first
      | rfl
      | (apply RingOfIntegers.ext; simp [Formalism.L2.DIV.starOHom, Formalism.L2.DIV.starO_coe, Formalism.L2.Col.cO])
  rw [this]

set_option maxHeartbeats 1000000 in
theorem mem_perO_inf_halfAO : ∀ (D : D7) (S T : HSp D), D.host.ccK = ⊤ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ c : ℕ, 0 < c → ∀ M ∈ GlobalTheory.LatVac.latRat S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)), (∃ w ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True), cA D e • GlobalTheory.LatVac.finTens 1 M = c • w) → Matrix.toLin' M ∈ (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ⊓ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c := by
  intro D S T hcc e SS hE N N' hN hN' c hc M hM hw
  obtain ⟨w, hw, hcw⟩ := hw
  have h1 : Matrix.toLin' M ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' := by
    have := (GlobalTheory.AdForm.RatLat.mem_latRat_iff_perO N' hN M).1 hM
    rwa [GlobalTheory.AdForm.RatLat.AA_eq hcc] at this
  refine Submodule.mem_inf.2 ⟨h1, ?_⟩
  have hcE : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have h0 : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hE)
  have hconj : ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • Matrix.toLin' M)).map fun r => cA D e * incA D r : WO S T) = w := by
    ext i j
    have hij := congrFun (congrFun hcw i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hij
    have e1 : cA D e * finTens 1 M i j = cA D e * incA D (M i j) := by
      refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
      · rw [RingHom.map_mul, RingHom.map_mul, h0, zero_mul, zero_mul]
      · rw [RingHom.map_mul, RingHom.map_mul]
        rfl
    have e2 : LinearMap.toMatrix' ((c : D.host.E)⁻¹ • Matrix.toLin' M) i j = (c : D.host.E)⁻¹ * M i j := by
      have e2' : (c : D.host.E)⁻¹ • Matrix.toLin' M = Matrix.toLin' ((c : D.host.E)⁻¹ • M) :=
        (map_smul Matrix.toLin' _ _).symm
      rw [e2', LinearMap.toMatrix'_toLin']
      rfl
    rw [Matrix.map_apply, e2, RingHom.map_mul, mul_left_comm, ← e1, hij, nsmul_eq_mul, ← mul_assoc]
    have e3 : incA D (c : D.host.E)⁻¹ * (c : AE D) = 1 := by
      rw [← map_natCast (incA D) c, ← RingHom.map_mul, inv_mul_cancel₀ hcE, map_one]
    rw [e3, one_mul]
  have hloc := (GlobalTheory.T.idempotentHalf_mem_completedHomLattice_iff_local D S T hcc (cA D e) _ (Formalism.IndefR.Fin.LevelGroupLemmas.isIdemSum_conj hE) N N' hN hN' _).1
    (hconj ▸ hw)
  rw [halfAO, Formalism.L2.Ker.mem_twO]
  intro Q
  by_cases hQ : Q ∈ SS
  · have ex : expS SS Q = 1 := by simp [expS, hQ]
    rw [ex]
    have e4 : (((c : D.host.E) ^ (-(1 : ℤ)))⁻¹) = (c : D.host.E) := by simp
    rw [e4]
    exact Formalism.L2.Ker.le_locP' _ _ (Formalism.L2.Ker.nat_smul_mem _ c h1)
  · by_cases hQ' : Formalism.L2.Col.conjPrime₂ Q ∈ SS
    · have ex : expS SS Q = -1 := by simp [expS, hQ, hQ']
      rw [ex]
      have e4 : (((c : D.host.E) ^ (-(-1 : ℤ)))⁻¹) = (c : D.host.E)⁻¹ := by simp
      rw [e4]
      refine hloc Q (Finset.mem_image.2 ⟨Formalism.L2.Col.conjPrime₂ Q, hQ', ?_⟩)
      rw [conjPl_eq_conjP, Formalism.L2.Ker.conjP_conjP']
    · have ex : expS SS Q = 0 := by simp [expS, hQ, hQ']
      rw [ex]
      simpa using Formalism.L2.Ker.le_locP' _ _ h1

end GlobalTheory.HalfAConj
end
end

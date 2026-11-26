module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSliceFamGood
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHOpClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PtieLevTransportHerOf

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSRadLocCut
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

def FamCCUnif : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)),
    CutSH.GoodFam T j G → ∀ K : Set ℂ, IsCompact K → (∀ t ∈ K, t ≠ 0) → ∀ (A : ℝ) (m : ℕ),
      ∃ c : ℝ, ∀ t ∈ K, B.CCle A m (G t) c

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSRadLocFamCC
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE.FamCC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.JFxG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem phiP_contDiffAt (f : ℂ × Mat k r → E) {U : Set (ℂ × Mat k r)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ∀ (j : ℕ) (bs : Fin j → Bool) (p : ℂ × ((Fin j → Mat k r) × Mat k r)), (p.1, p.2.2) ∈ U →
      ContDiffAt ℝ ∞ (fun p : ℂ × ((Fin j → Mat k r) × Mat k r) => Phi (fun x => f (p.1, x)) j bs p.2) p := by
  intro j
  induction j with
  | zero =>
    intro bs p hp
    have hm : ContDiff ℝ ∞ (fun p : ℂ × ((Fin 0 → Mat k r) × Mat k r) => (p.1, p.2.2)) :=
      contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
    exact (hf.contDiffAt (hU.mem_nhds hp)).comp p hm.contDiffAt
  | succ j ih =>
    intro bs p hp
    have hsh : ContDiff ℝ ∞ (fun q : (ℂ × ((Fin (j + 1) → Mat k r) × Mat k r)) × Mat k r =>
        (q.1.1, ((fun i : Fin j => q.1.2.1 i.succ), q.2))) :=
      (contDiff_fst.comp contDiff_fst).prodMk
        ((contDiff_pi.2 fun (i : Fin j) =>
          (by simpa only [Function.comp_def] using
            (contDiff_apply ℝ (fun _ : Fin (j + 1) => Mat k r) i.succ).comp (contDiff_fst.comp (contDiff_snd.comp contDiff_fst)))).prodMk
          contDiff_snd)
    have h1 : ContDiffAt ℝ ∞ (Function.uncurry fun (q : ℂ × ((Fin (j + 1) → Mat k r) × Mat k r)) (g : Mat k r) =>
        Phi (fun x => f (q.1, x)) j (fun i => bs i.succ) ((fun i => q.2.1 i.succ), g)) (p, p.2.2) :=
      ContDiffAt.comp (g := fun q : ℂ × ((Fin j → Mat k r) × Mat k r) =>
        Phi (fun x => f (q.1, x)) j (fun i => bs i.succ) q.2) (p, p.2.2)
        (ih (fun i => bs i.succ) (p.1, ((fun i => p.2.1 i.succ), p.2.2)) hp) hsh.contDiffAt
    have h2 := ContDiffAt.fderiv h1 (contDiffAt_snd.comp p contDiffAt_snd) top_add_one_le
    have h3 : ContDiff ℝ ∞ (fun q : ℂ × ((Fin (j + 1) → Mat k r) × Mat k r) => vf (bs 0) (q.2.1 0) q.2.2) :=
      vf_contDiff (bs 0) (by simpa only [Function.comp_def] using
        (contDiff_apply ℝ (fun _ : Fin (j + 1) => Mat k r) 0).comp (contDiff_fst.comp contDiff_snd))
        (contDiff_snd.comp contDiff_snd)
    exact h2.clm_apply h3.contDiffAt

theorem local_boundP {G : ℂ → Mat k r → E} (f : ℂ × Mat k r → E) {U : Set (ℂ × Mat k r)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hGf : ∀ p ∈ U, p.2 ∈ GV k r → G p.1 p.2 = f p) (m : ℕ) {p₀ : ℂ × Mat k r}
    (hp₀ : p₀ ∈ U) :
    ∃ V ∈ 𝓝 p₀, ∃ c : ℝ, 0 ≤ c ∧ ∀ p ∈ V, p.2 ∈ GV k r → ∀ (j : ℕ), j ≤ m → ∀ (bs : Fin j → Bool)
      (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) (G p.1) p.2‖ ≤ c := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU p₀ hp₀
  have hsub : Metric.closedBall p₀ (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hb : ∀ (j : ℕ) (bs : Fin j → Bool), ∃ c : ℝ, ∀ q ∈ Metric.closedBall p₀.1 (ε / 2) ×ˢ
      ((Set.pi Set.univ fun _ : Fin j => Box k r) ×ˢ Metric.closedBall p₀.2 (ε / 2)),
      ‖Phi (fun x => f (q.1, x)) j bs q.2‖ ≤ c := by
    intro j bs
    have hK : IsCompact (Metric.closedBall p₀.1 (ε / 2) ×ˢ
        ((Set.pi Set.univ fun _ : Fin j => Box k r) ×ˢ Metric.closedBall p₀.2 (ε / 2))) :=
      (isCompact_closedBall _ _).prod ((isCompact_univ_pi fun _ => box_compact).prod (isCompact_closedBall _ _))
    refine hK.exists_bound_of_continuousOn fun q hq => ?_
    have hqU : (q.1, q.2.2) ∈ U := by
      apply hsub
      rw [Metric.mem_closedBall, Prod.dist_eq]
      exact max_le (Metric.mem_closedBall.1 hq.1) (Metric.mem_closedBall.1 hq.2.2)
    exact (phiP_contDiffAt f hU hf j bs q hqU).continuousAt.continuousWithinAt
  choose c hcb using hb
  refine ⟨Metric.closedBall p₀ (ε / 2), Metric.closedBall_mem_nhds p₀ (by linarith),
    ∑ j : Fin (m + 1), ∑ bs : Fin j → Bool, |c j bs|, by positivity, ?_⟩
  intro p hp hpG j hj bs Xs hL hB
  have hpU : p ∈ U := hsub hp
  have hUt : IsOpen {x : Mat k r | (p.1, x) ∈ U} :=
    hU.preimage (continuous_const.prodMk continuous_id)
  have hft : ContDiffOn ℝ ∞ (fun x => f (p.1, x)) {x : Mat k r | (p.1, x) ∈ U} :=
    hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x hx => hx)
  have hmem : p.2 ∈ {x : Mat k r | (p.1, x) ∈ U} := hpU
  rw [W_eq_phi hUt hft (fun x hx hxG => hGf (p.1, x) hx hxG) j bs Xs hL p.2 hmem hpG]
  have hpd : dist p p₀ ≤ ε / 2 := Metric.mem_closedBall.1 hp
  rw [Prod.dist_eq] at hpd
  have hq : (p.1, (Xs, p.2)) ∈ Metric.closedBall p₀.1 (ε / 2) ×ˢ
      ((Set.pi Set.univ fun _ : Fin j => Box k r) ×ˢ Metric.closedBall p₀.2 (ε / 2)) :=
    ⟨Metric.mem_closedBall.2 ((le_max_left _ _).trans hpd), fun i _ => hB i,
      Metric.mem_closedBall.2 ((le_max_right _ _).trans hpd)⟩
  calc ‖Phi (fun x => f (p.1, x)) j bs (Xs, p.2)‖ ≤ |c j bs| := (hcb j bs _ hq).trans (le_abs_self _)
    _ = |c (⟨j, by omega⟩ : Fin (m + 1)) bs| := rfl
    _ ≤ ∑ bs' : Fin (⟨j, by omega⟩ : Fin (m + 1)) → Bool, |c (⟨j, by omega⟩ : Fin (m + 1)) bs'| :=
        Finset.single_le_sum (f := fun bs' => |c (⟨j, by omega⟩ : Fin (m + 1)) bs'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ bs)
    _ ≤ ∑ j' : Fin (m + 1), ∑ bs' : Fin j' → Bool, |c j' bs'| :=
        Finset.single_le_sum (f := fun j' : Fin (m + 1) => ∑ bs' : Fin j' → Bool, |c j' bs'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ _)

theorem ccle_unif {G : ℂ → Mat k r → E} {K : Set ℂ} (hK : IsCompact K) {C : Set (Mat k r)} (hC : IsCompact C)
    (hloc : ∀ t ∈ K, ∀ γ ∈ GV k r, ∃ (U : Set (ℂ × Mat k r)) (f : ℂ × Mat k r → E), IsOpen U ∧ (t, γ) ∈ U ∧
      ContDiffOn ℝ ∞ f U ∧ ∀ p ∈ U, p.2 ∈ GV k r → G p.1 p.2 = f p)
    (hck : ∀ t ∈ K, CkOn ⊤ (GV k r) (G t))
    (hsupp : ∀ t ∈ K, ∀ γ, G t γ ≠ 0 → γ ∈ C) (A : ℝ) (m : ℕ) :
    ∃ c : ℝ, ∀ t ∈ K, CCle A m (G t) c := by
  classical
  have hS : IsCompact (K ×ˢ (C ∩ GV k r)) := hK.prod (hC.inter_right B5.GV_closed)
  have hl : ∀ p ∈ K ×ˢ (C ∩ GV k r), ∃ V, V ∈ 𝓝 p ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ q ∈ V, q.2 ∈ GV k r → ∀ (j : ℕ), j ≤ m →
      ∀ (bs : Fin j → Bool) (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) (G q.1) q.2‖ ≤ c := fun p hp => by
    obtain ⟨U, f, hU, hpU, hf, hGf⟩ := hloc p.1 hp.1 p.2 hp.2.2
    obtain ⟨V, hV, c, hc0, hc⟩ := local_boundP f hU hf hGf m (p₀ := (p.1, p.2)) hpU
    exact ⟨V, hV, c, hc0, hc⟩
  choose! V hV c hc0 hc using hl
  obtain ⟨s, hsS, hcov⟩ := hS.elim_nhds_subcover V hV
  have hsum0 : 0 ≤ ∑ x ∈ s, c x := Finset.sum_nonneg fun y hy => hc0 y (hsS y hy)
  have hcW : ∀ t ∈ K, ∀ g ∈ C ∩ GV k r, ∀ (j : ℕ), j ≤ m → ∀ (bs : Fin j → Bool) (Xs : Fin j → Mat k r),
      (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) (G t) g‖ ≤ ∑ x ∈ s, c x := by
    intro t ht g hg j hj bs Xs hL hB
    obtain ⟨x, hxs, hgx⟩ := Set.mem_iUnion₂.1 (hcov (show (t, g) ∈ K ×ˢ (C ∩ GV k r) from ⟨ht, hg⟩))
    exact (hc x (hsS x hxs) (t, g) hgx hg.2 j hj bs Xs hL hB).trans
      (Finset.single_le_sum (fun y hy => hc0 y (hsS y hy)) hxs)
  obtain ⟨cg, hcg⟩ := (hC.inter_right B5.GV_closed).exists_bound_of_continuousOn
    (f := fun g : Mat k r => gN g ^ A)
    fun g hg => ((B6.gN_continuous.continuousAt).rpow_const (Or.inl (B6.gN_pos hg.2).ne')).continuousWithinAt
  refine ⟨|cg| * ∑ x ∈ s, c x, fun t ht => ⟨B5.ckOn_mono le_top (hck t ht), ?_⟩⟩
  intro u v hu hv hlen g hg
  rw [dLR_eq]
  have hmemlr : ∀ y ∈ lr u v, unitLie k r y.2 := by
    intro y hy
    simp only [lr, List.mem_append, List.mem_map] at hy
    rcases hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact hu X hX
    · exact hv X hX
  by_cases hgC : g ∈ C
  · have hw : lr u v = List.ofFn fun i : Fin (lr u v).length => ((lr u v)[i].1, (lr u v)[i].2) := by
      simp
    have hlen' : (lr u v).length ≤ m := by simp [lr]; omega
    have hb := hcW t ht g ⟨hgC, hg⟩ _ hlen' (fun i => (lr u v)[i].1) (fun i => (lr u v)[i].2)
      (fun i => (hmemlr _ (List.getElem_mem _)).1) (fun i => mem_box (hmemlr _ (List.getElem_mem _)).2)
    rw [← hw] at hb
    have hg1 : gN g ^ A ≤ |cg| := by
      have := hcg g ⟨hgC, hg⟩
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_abs_self _))
    exact mul_le_mul hg1 hb (norm_nonneg _) (abs_nonneg _)
  · have h0 := W_local_zero hC.isClosed.isOpen_compl
      (fun x hx _ => by by_contra h; exact hx (hsupp t ht x h)) (lr u v)
      (fun y hy => (hmemlr y hy).1) g hgC hg
    rw [h0, norm_zero, mul_zero]
    positivity

end Formalism.FourierDecayAlt.P.CutSE.FamCC

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem family_uniform_compact_convergence : FamCCUnif := by
  intro Wp Wq _ _ _ _ _ _ P T j G hG K hK hK0 A m
  obtain ⟨hG1, hG2⟩ := hG
  obtain ⟨C, hC, ε, hε, hCε⟩ := hG2 K hK hK0
  have hck : ∀ t ∈ K, B.CkOn ⊤ (B.GV P.k (P.r - (j + 1))) (G t) := by
    intro t ht γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hfe⟩ := hG1 t (hK0 t ht) γ₀ hγ₀
    have hcm : Continuous (fun γ : B.Mat P.k (P.r - (j + 1)) => (t, γ)) :=
      continuous_const.prodMk continuous_id
    refine ⟨(fun γ => (t, γ)) ⁻¹' U, fun γ => f (t, γ), hU.preimage hcm, hmem, ?_, ?_⟩
    · exact hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun γ hγ => hγ)
    · intro γ hγ hγG
      exact hfe (t, γ) hγ hγG
  exact FamCC.ccle_unif hK hC (fun t ht γ hγ => hG1 t (hK0 t ht) γ hγ) hck
    (fun t ht γ h => (hCε t ht γ h).1) A m

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelOneSquareIntegrableOfTransport
open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section Tr

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem fs_tr (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ) (t : ℂ)
    {zi zi' : Fin (2 * (r - l.succ) + k + 1) → ℂ} {πi : Mx k (r - l.succ) → (Wp →L[ℂ] Wp)}
    {πi' : Mx k (r - l.succ) → (Wq →L[ℂ] Wq)} (μi : Measure (Mt k (r - l.succ)))
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - l.succ) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' =
      (κ : ℂ) * pairAt μ Φ Ψ (glue l.succ (Function.update c l t) (Formalism.FourierDecayAlt.P.PTie.shiftCf l.succ c'')))
    (Φ Ψ : RadSp k r z z' π π') :
    fs μ l Φ Ψ c t = (κ : ℂ)⁻¹ * ∫ c'' : Cf (r - l.succ) 0, wtI 0 c'' *
      pairAt μi (T Φ) (T Ψ) (glue 0 (shiftV l.succ (Function.update c l t)) c'') := by
  have hjl : (0 : Fin (r - l.succ + 1)).val + l.succ.val = l.succ.val := by simp
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  unfold fs
  rw [← (shEqJ_mp l.succ l.succ 0 hjl).integral_comp', ← integral_const_mul]
  congr 1; funext c''
  rw [wtI_shEqJ, glue_shEqJ l.succ l.succ 0 hjl (Function.update c l t) (Function.update c l t) (fun _ _ => rfl), hT]
  field_simp

theorem level_one_square_integrable_of_transport (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ) (t : ℂ)
    {zi zi' : Fin (2 * (r - l.succ) + k + 1) → ℂ} {πi : Mx k (r - l.succ) → (Wp →L[ℂ] Wp)}
    {πi' : Mx k (r - l.succ) → (Wq →L[ℂ] Wq)} (μi : Measure (Mt k (r - l.succ)))
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - l.succ) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' =
      (κ : ℂ) * pairAt μ Φ Ψ (glue l.succ (Function.update c l t) (Formalism.FourierDecayAlt.P.PTie.shiftCf l.succ c'')))
    (Φ : RadSp k r z z' π π') (c₀ : Fin (r - l.succ) → ℂ) (h : LevelSquareIntegrable μi 0 (T Φ) c₀) :
    LevelSquareIntegrable μ l.succ Φ (Function.update c l t) :=
  level_square_integrable_of_transport μ l.succ (Function.update c l t) μi T κ hκ hT Φ c₀ h

end Tr

end Formalism.FourierDecayAlt.P5.HerD
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PTieUL
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevTransportU
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTie

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

def LevTransportU : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (Bs : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → Bs.z = z → Bs.z' = z' → Bs.π = π → Bs.π' = π' →
    ∀ (i : Fin (P.r + 1)),
    ∃ Tw : D.LevTower P.k P.r Wp Wq, D.TowerNormalised Tw ∧
      Tw.base.z = z ∧ Tw.base.z' = z' ∧ Tw.base.π = π ∧ Tw.base.π' = π' ∧
    ∃ (Di : B.RealPlaceData P.k (P.r - i) Wp Wq)
      (Xi : ActualOps (JC.parLev P i).k (JC.parLev P i).r Di.z Di.z' Di.π Di.π') (μi : Measure (Mt P.k (P.r - i)))
      (Li : R.LevelData (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π')) (P.r - i))
      (sti : Fr.Start (Pr (RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π'))) (κ : ℝ),
      Di = Tw.bs i ∧ 0 < κ ∧ IsData (JC.parLev P i) Di.z Di.z' Di.π Di.π' Xi μi Li sti l0 ∧
      ∀ (c : Fin P.r → ℂ), (∀ l : Fin P.r, l.val < i.val → c l ≠ 0) →
      ∃ T : RadSp P.k P.r z z' π π' →ₗ[ℂ] RadSp P.k (P.r - i) Di.z Di.z' Di.π Di.π',
        LevTrClauses P μ L st l0 i c Di μi Li sti T ∧
        ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (shiftCf i c''))

end Formalism.FourierDecayAlt.P.PTie
end
end

open Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTieUL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.PTieB Formalism.FourierDecayAlt.P.PTieL

theorem lev_indU {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π')
    (X : ActualOps P.k P.r T.base.z T.base.z' T.base.π T.base.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π'))) (l0 : ℕ)
    (hD : P5.IsData P T.base.z T.base.z' T.base.π T.base.π' X μ L st l0) :
    ∀ (j : ℕ) (hj : j ≤ P.r),
    ∃ (Xj : ActualOps (JC.parLev P j).k (JC.parLev P j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
      (μj : Measure (Mt P.k (P.r - j)))
      (Lj : R.LevelData (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) (P.r - j))
      (stj : Fr.Start (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))) (κ : ℝ),
      0 < κ ∧ P5.IsData (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Xj μj Lj stj l0 ∧
      KB.ZetaNorm (T.bs j) μj ∧
      ∀ c : Fin P.r → ℂ, (∀ l : Fin P.r, l.val < j → c l ≠ 0) →
      ∃ Tj : RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π' →ₗ[ℂ]
        RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π',
      (∀ Φ c'' g, (Tj Φ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c'' g =
        (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) (P5.glue ⟨j, by omega⟩ c (PTie.shiftCf ⟨j, by omega⟩ c''))
          (D.castM (by omega) (ιLev P.k j (P.r - j) g))) ∧
      (∀ Φ Ψ c'', P5.pairAt μj (Tj Φ) (Tj Ψ) c'' =
        (κ : ℂ) * P5.pairAt μ Φ Ψ (P5.glue ⟨j, by omega⟩ c (PTie.shiftCf ⟨j, by omega⟩ c''))) ∧
      (∀ l : Fin (P.r - j), Rel Tj (L.p ⟨l.val + j, by omega⟩) (Lj.p l) ∧
        Rel Tj (L.c ⟨l.val + j, by omega⟩) (Lj.c l) ∧ Rel Tj (L.ci ⟨l.val + j, by omega⟩) (Lj.ci l)) ∧
      ∀ (n : ℕ) (hn : n + j ≤ P.r) (Y : ℂ),
        MRel Tj (P5.QQi L st ⟨n + j, by omega⟩ Y) (P5.QQi Lj stj ⟨n, by omega⟩ Y) := by
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar P.k (P.r - 0) Wp Wq (T.bs 0)
    have h1 : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hD.2.1
    obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, μ = a • μ0 := by
      have hU := Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed P.k P.r
      have h1' := h1
      have h0 : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ0 := hμ0.1
      rw [glev_last_eq] at h1' h0
      exact Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar P.k P.r _ μ0 μ hU h0 h1'.conc h1'.left h1'.finite_compact
    have ha0 : (a : ℝ) ≠ 0 := by
      intro h
      apply h1.ne_zero
      rw [ha, show a = 0 from by exact_mod_cast h, zero_smul]
    refine ⟨X, μ0, L, st, (a : ℝ)⁻¹, inv_pos.2 (lt_of_le_of_ne a.2 (Ne.symm ha0)),
      ⟨JCTx5.isPlace_lev P T ⟨0, by omega⟩ hP, hμ0.1, hD.2.2⟩, hμ0, fun c _ => ⟨LinearMap.id,
      fun Φ c'' g => ?_, fun Φ Ψ c'' => ?_, fun l => ⟨rel_id _, rel_id _, rel_id _⟩, fun n hn Y => mrel_id _⟩⟩
    · rw [glue_zero', castM_iota0]; rfl
    · rw [glue_zero', ha, pairAt_smul, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ ha0, Complex.ofReal_one,
        one_mul]
      rfl
  | succ j ih =>
    intro hj'
    obtain ⟨Xj, μj, Lj, stj, κ, hκ, hDj, hZj, hall⟩ := ih (by omega)
    have hPl := JCTx5.isPlace_lev P T ⟨j + 1, by omega⟩ hP
    obtain ⟨Xs⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
    obtain ⟨Ls, sts, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl Xs l0
    obtain ⟨μs, hμs⟩ := Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar P.k (P.r - (j + 1)) Wp Wq (T.bs (j + 1))
    have hDs : P5.IsData (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π
        (T.bs (j + 1)).π' Xs μs Ls sts l0 := ⟨hPl, hμs.1, h1, h2, h3, h4, h5, h6⟩
    refine ⟨Xs, μs, Ls, sts, κ, hκ, hDs, hμs, fun c hc => ?_⟩
    obtain ⟨Tj, hform, hpair, hsite, hqq⟩ := hall c (fun l hl => hc l (by omega))
    have hn : P.r - j = 1 + (P.r - (j + 1)) := by omega
    have hcj : c ⟨j, by omega⟩ ≠ 0 := hc ⟨j, by omega⟩ (by simp)
    obtain ⟨T', hf', hs', hq', hp'⟩ := step_cast (k := P.k) (n := P.r - j) (ρ := P.r - (j + 1)) hn
      (levTower_bs_z_eq_castV_liftVec T j hj') (levTower_bs_z'_eq_castV_liftVec T j hj') (T.bs (j + 1)).z_mem (T.bs (j + 1)).z'_mem (tower_π T j hj')
      (tower_π' T j hj') Xj Xs Lj stj Ls sts (M.sgn (JC.parLev P j) l0) μj μs hDj.2.2.1 hDs.2.2.1
      hDj.2.2.2.1 hDs.2.2.2.1 hZj.1 hμs.1 hZj.2 hμs.2 (c ⟨j, by omega⟩) hcj
    refine ⟨T' ∘ₗ Tj, fun Φ c'' g => ?_, fun Φ Ψ c'' => ?_, fun l => ?_, fun n hn' Y => ?_⟩
    · rw [LinearMap.comp_apply, hf', hform, glue_step j hj' c c'' hn,
        lift_lift_M j (P.r - (j + 1)) (P.r - j) P.r hn.symm (by omega) (by omega)]
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, hp', hpair, glue_step j hj' c c'' hn]
    · have e : (⟨l.val + 1 + j, by omega⟩ : Fin P.r) = ⟨l.val + (j + 1), by omega⟩ :=
        Fin.ext (show l.val + 1 + j = l.val + (j + 1) by omega)
      obtain ⟨a1, a2, a3⟩ := hsite ⟨l.val + 1, by omega⟩
      obtain ⟨b1, b2, b3⟩ := hs' l
      rw [← e]
      exact ⟨rel_comp a1 b1, rel_comp a2 b2, rel_comp a3 b3⟩
    · have e : (⟨n + 1 + j, by omega⟩ : Fin (P.r + 1)) = ⟨n + (j + 1), by omega⟩ :=
        Fin.ext (show n + 1 + j = n + (j + 1) by omega)
      have a := hqq (n + 1) (by omega) Y
      have b := hq' n (by omega) Y
      rw [← e]
      exact mrel_comp a b

theorem levTransportU : Formalism.FourierDecayAlt.P.PTie.LevTransportU := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 Bs hD hz hz' hπ hπ' i
  obtain ⟨T, h1, h2, h3, h4, hN⟩ := Formalism.FourierDecayAlt.P.exists_normalized_tower P.k P.r Wp Wq Bs
  have e1 : T.base.z = z := h1.trans hz
  have e2 : T.base.z' = z' := h2.trans hz'
  have e3 : T.base.π = π := h3.trans hπ
  have e4 : T.base.π' = π' := h4.trans hπ'
  subst e1 e2 e3 e4
  obtain ⟨Xi, μi, Li, sti, κ, hκ, hDi, -, hall⟩ := lev_indU P T hD.1 X μ L st l0 hD i.val (by omega)
  refine ⟨T, hN, rfl, rfl, rfl, rfl, T.bs i, Xi, μi, Li, sti, κ, rfl, hκ, hDi, fun c hc => ?_⟩
  obtain ⟨Ti, hform, hpair, hsite, hqq⟩ := hall c hc
  refine ⟨Ti, ⟨hform, ⟨κ, hκ, hpair⟩, fun n hn Y => hqq n hn Y,
    fun S _ _ w => ⟨fun l => ?_, fun n hn => ?_, fun hw => ?_⟩⟩, hpair⟩
  · obtain ⟨a1, a2, a3⟩ := hsite l
    exact arel_bT (σ := P5.site L ⟨l.val + i, by omega⟩) (σ' := P5.site Li l) a1 a2 a3 w
  · exact arel_RRw (fun Y => hqq n hn Y) w
  · obtain ⟨⟨hA1, hA2, hA3, hA4⟩, hw2, hw3⟩ := hw
    have hq : sti.q = st.q := hDi.2.2.2.2.1.trans hD.2.2.2.2.1.symm
    have hinv : sti.inv = st.inv := hDi.2.2.2.2.2.1.trans hD.2.2.2.2.2.1.symm
    refine ⟨⟨hA1, hA2, fun l hl => ?_, hA4⟩, hw2, hw3⟩
    rw [hq, hinv]
    exact hA3 l hl

end Formalism.FourierDecayAlt.P.PTieUL

namespace Formalism.FourierDecayAlt.P

theorem level_transport_unitary : Formalism.FourierDecayAlt.P.PTie.LevTransportU := PTieUL.levTransportU

end Formalism.FourierDecayAlt.P
end
end

open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerD Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jSRadLoc_of (hU : FamCCUnif) : JSRadLoc := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' l hl ε hε G hN hGc Φ hlc hΦ c hc js hjs t0 ht0
  have hr0 : 0 < P.r := by have := l.isLt; omega
  obtain rfl : l = ⟨0, hr0⟩ := Fin.ext hl
  obtain ⟨Tw, hNw, e1, e2, e3, e4, Di, Xi, μi, Li, sti, κ, hDiEq, hκ, hDi, hall⟩ :=
    Formalism.FourierDecayAlt.P.level_transport_unitary Wp Wq P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' ⟨1, by omega⟩
  subst e1 e2 e3 e4
  subst hDiEq
  have hj : 0 + 1 ≤ P.r := by omega
  have hP : IsPlace P Tw.base.z Tw.base.z' Tw.base.π Tw.base.π' := hD.1
  have hPj := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P Tw ⟨0, by omega⟩ hP
  have hPs := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P Tw ⟨0 + 1, by omega⟩ hP
  obtain ⟨κ0, hκ0⟩ := Formalism.FourierDecayAlt.P.jacquet_scaling P.k P.r Wp Wq D Tw.base hz hz' hπ hπ'

  set G0 : B.Mat P.k (P.r - 0) → (Wq →L[ℂ] Wp) := fun g => κ0 • G g with hG0
  have hG0ok : JFOKCpt (JC.parLev P 0) (Tw.bs 0).z (Tw.bs 0).z' G0 := by
    have hck : B.CkOn ⊤ (B.GV P.k (P.r - 0)) G0 := by
      intro g₀ hg₀
      obtain ⟨U, f', hU', hgU, hcf, hff⟩ := hN.1 g₀ hg₀
      exact ⟨U, fun g => κ0 • f' g, hU', hgU, hcf.const_smul κ0, fun g hg hgG => by
        simp only [hG0]; rw [hff g hg hgG]⟩
    have hz0 : ∀ g ∈ B.GV P.k (P.r - 0), g ∉ tsupport G → G0 g = 0 := fun g _ hg => by
      simp only [hG0]; rw [image_eq_zero_of_notMem_tsupport hg, smul_zero]
    refine ⟨⟨fun A m => Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hck hGc hz0 A m, ε, hε, fun g hg hne => ?_⟩, ?_⟩
    · have hne' : G g ≠ 0 := fun h => hne (by simp only [hG0]; rw [h, smul_zero])
      have := hN.2.2 g hg hne'
      rwa [hz, hz'] at this
    · exact HasCompactSupport.intro hGc (fun g hg => by simp only [hG0]; rw [image_eq_zero_of_notMem_tsupport hg, smul_zero])
  have hΦ0 : IsRadJF (JC.parLev P 0) (Tw.bs 0).z (Tw.bs 0).z' (Tw.bs 0).π (Tw.bs 0).π' (Tw.bs 0) G0 Φ := by
    intro (x : (Fin P.r → ℂ) × Mx P.k P.r) hx
    have e : B.JF Tw.base G0 = κ0 • B.JF Tw.base G := by
      funext h
      exact Formalism.FourierDecayAlt.P.JCx2.bc_JF_smul (Bs := Tw.base) κ0 G h
    have h2 : resG P.k P.r (Fin.last P.r) (B.JF D G) x.1 x.2 =
        resG P.k P.r (Fin.last P.r) (B.JF Tw.base G0) x.1 x.2 := by
      rw [hκ0 G, e]
    exact (hΦ x hx).trans h2
  have hC0 : CutSH.InC Tw 0 hj Φ :=
    CutSH.inC_seed Formalism.FourierDecayAlt.P.cell_compatibility_identity Formalism.FourierDecayAlt.P.slice_family_good
      CutSH.slice_family_orbital hP hNw hPj hPs G0 hG0ok Φ hΦ0
  have hW : ∀ js : List (Fin 6), CutSH.InC Tw 0 hj (wOp X ⟨0, hr0⟩ js Φ) := by
    intro js
    induction js with
    | nil => simpa [wOp] using hC0
    | cons j js ih =>
      have e : wOp X ⟨0, hr0⟩ (j :: js) Φ = X.op ⟨0, hr0⟩ j (wOp X ⟨0, hr0⟩ js Φ) := by
        simp [wOp, List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [e]
      exact Formalism.FourierDecayAlt.P.operator_class_closed Wp Wq P Tw hP hNw 0 hj hPj hPs X j _ ih
  obtain ⟨Gj, hGj, hRep⟩ := hW js
  set K : Set ℂ := Metric.closedBall t0 (‖t0‖ / 2) with hKdef
  have hK : IsCompact K := isCompact_closedBall _ _
  have hn0 : 0 < ‖t0‖ := norm_pos_iff.2 ht0
  have hK0 : ∀ t ∈ K, t ≠ 0 := fun t ht h0 => by
    rw [h0, hKdef, Metric.mem_closedBall, dist_zero_left] at ht
    linarith
  obtain ⟨c4, hc4⟩ := hU Wp Wq P Tw 0 Gj hGj K hK hK0 (B.AB P.k (P.r - (0 + 1))) 4
  obtain ⟨CR, hCR, hRB⟩ := Formalism.FourierDecayAlt.P.radial_beta_pos Wp Wq P Tw ⟨1, by omega⟩ μi hDi.2.1
  obtain ⟨-, -, -, ⟨CB, hB1⟩, -⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi P.k (P.r - (0 + 1)) Wp Wq (Tw.bs (0 + 1))
    (B.AB _ _) le_rfl
  refine ⟨‖t0‖ / 2, by positivity, κ⁻¹ * CR⁻¹ * (|CB| * |c4| * |c4|), fun t ht => ?_⟩
  have htK : t ∈ K := Metric.ball_subset_closedBall ht
  have ht0' : t ≠ 0 := hK0 t htK
  obtain ⟨Tt, ⟨hform, -⟩, hpair⟩ := hall (Function.update c ⟨0, hr0⟩ t) (fun l' hl' => by
    have e : l' = ⟨0, hr0⟩ := Fin.ext (by simp at hl'; omega)
    subst e
    simpa using ht0')

  set Ψ := wOp X ⟨0, hr0⟩ js Φ with hΨdef
  have hTΨ : ∀ x ∈ DomR P.k (P.r - (0 + 1)) (Tw.bs (0 + 1)).z (Tw.bs (0 + 1)).z',
      (Tt Ψ : Fn P.k (P.r - (0 + 1)) (Wq →L[ℂ] Wp)) x.1 x.2 =
        resG P.k (P.r - (0 + 1)) (Fin.last _) (B.JF (Tw.bs (0 + 1)) (Gj t)) x.1 x.2 := by
    intro x hx
    rw [hform]
    have hg : glue ⟨1, by omega⟩ (Function.update c ⟨0, hr0⟩ t) (PTie.shiftCf ⟨1, by omega⟩ x.1) =
        CutSH.cc 0 hj t x.1 := by
      funext l'
      rcases Nat.eq_zero_or_pos l'.val with h | h
      · have e : l' = ⟨0, hr0⟩ := Fin.ext h
        subst e
        simp [glue, CutSH.cc, consC]
      · have hne : l' ≠ ⟨0, hr0⟩ := fun e => by rw [e] at h; simp at h
        have h1 : (1 : ℕ) ≤ l'.val := h
        simp [glue, CutSH.cc, consC, PTie.shiftCf, h1, Nat.pos_iff_ne_zero.mp h]
    rw [hg]
    exact hRep t ht0' x hx
  obtain ⟨⟨hInCC, εt, hεt, hεG⟩, -⟩ := CutSH.family_orbital_valid Wp Wq P Tw 0 Gj hGj t ht0'
  have hck : B.CkOn ⊤ (B.GV P.k (P.r - (0 + 1))) (Gj t) := by
    intro γ₀ hγ₀
    obtain ⟨U, f, hU', hmem, hf, hfe⟩ := hGj.1 t ht0' γ₀ hγ₀
    have hcm : Continuous (fun γ : B.Mat P.k (P.r - (0 + 1)) => (t, γ)) :=
      continuous_const.prodMk continuous_id
    refine ⟨(fun γ => (t, γ)) ⁻¹' U, fun γ => f (t, γ), hU'.preimage hcm, hmem, ?_, ?_⟩
    · exact hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun γ hγ => hγ)
    · intro γ hγ hγG
      exact hfe (t, γ) hγ hγG
  have hNice : JC.NiceCoef (Tw.bs (0 + 1)) εt (Gj t) := ⟨hck, hInCC, hεG⟩
  have hL2 : LevelSquareIntegrable μi 0 (Tt Ψ) 0 := by
    have h := Formalism.FourierDecayAlt.P5.HerC.level_zero_form_integrable_compact (S := Empty) (Tw.bs (0 + 1)) μi hDi.2.1 (fun _ => Gj t) (fun _ => Gj t)
      (fun _ => Tt Ψ) (fun _ => Tt Ψ) (fun _ => hInCC) (fun _ => hInCC) (fun _ => hTΨ) (fun _ => hTΨ) 0
    unfold LevelSquareIntegrable
    letI : Unique (Wd.Ix Empty) := { default := Empty.elim, uniq := fun _ => funext fun x => x.elim }
    simpa [wtI] using h
  refine ⟨level_one_square_integrable_of_transport μ ⟨0, hr0⟩ c t μi Tt κ hκ hpair Ψ 0 hL2, ?_⟩
  rw [fs_tr μ ⟨0, hr0⟩ c t μi Tt κ hκ hpair Ψ Ψ]
  have hform0 : (∫ c'' : Cf (P.r - (0 + 1)) 0, wtI 0 c'' * pairAt μi (Tt Ψ) (Tt Ψ)
      (glue 0 (shiftV (Fin.succ ⟨0, hr0⟩) (Function.update c ⟨0, hr0⟩ t)) c'')) =
      form μi 0 (fun _ : Wd.Ix (Fin 0) => Tt Ψ) (fun _ => Tt Ψ) 0 := by
    unfold form
    congr 1
    funext c''
    have eg : glue 0 (shiftV (Fin.succ ⟨0, hr0⟩) (Function.update c ⟨0, hr0⟩ t)) c'' = glue 0 0 c'' := by
      funext l'; simp [glue]
    rw [eg]
    simp [wtI]
  have hβ := hRB 0 (fun _ => Gj t) (fun _ => Gj t) (fun _ => Tt Ψ) (fun _ => Tt Ψ) εt hεt (fun _ => hNice)
    (fun _ => hNice) (fun _ => hTΨ) (fun _ => hTΨ)
  have hβ' : B.beta (Tw.bs (0 + 1)) (Gj t) (Gj t) = (CR : ℂ) * form μi 0 (fun _ : Wd.Ix (Fin 0) => Tt Ψ) (fun _ => Tt Ψ) 0 := by
    convert hβ using 1
    · simp
    · rfl
  have hb := (hB1 (Gj t) (Gj t) c4 c4 (hInCC _ 5) (hInCC _ 5) (hc4 t htK) (hc4 t htK)).2.2
  erw [hform0]
  have hf : form μi 0 (fun _ : Wd.Ix (Fin 0) => Tt Ψ) (fun _ => Tt Ψ) 0 = (CR : ℂ)⁻¹ * B.beta (Tw.bs (0 + 1)) (Gj t) (Gj t) := by
    rw [hβ']
    have : (CR : ℂ) ≠ 0 := by exact_mod_cast hCR.ne'
    field_simp
  rw [hf, norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hκ.le,
    Real.norm_of_nonneg hCR.le, mul_assoc]
  gcongr
  calc ‖B.beta (Tw.bs (0 + 1)) (Gj t) (Gj t)‖ ≤ CB * c4 * c4 := hb
    _ ≤ |CB| * |c4| * |c4| := by
      have := abs_mul_abs_self c4
      calc CB * c4 * c4 = CB * (c4 * c4) := by ring
        _ ≤ |CB * (c4 * c4)| := le_abs_self _
        _ = |CB| * |c4| * |c4| := by rw [abs_mul, abs_mul, mul_assoc]

theorem spectral_radial_locality : JSRadLoc := jSRadLoc_of family_uniform_compact_convergence

end Formalism.FourierDecayAlt.P.CutSE

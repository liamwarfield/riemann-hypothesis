module

public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.GoodRankOfPrim
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ExistsPolFamilyOfMemGenOfVsDegLe
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.MultidegreeBoundLeA
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SourcePrimitiveIntegrality
public import Formalism.PeriodIntegrals.AdmissibleModel.WeylDim

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.ScaleEdges
section -- merged from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SymbolRealisableIffGeneralRank
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

theorem oHyp_of {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (h : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w)
    (φ : WF p n' ≃+* W) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    OHyp p n' O (dvrOfStd h) := by
  let _ : Algebra (WF p n') O := algOfIdent j φ
  refine ⟨dvrOfStd_sq h, ?_, ?_⟩
  · show (j.comp (φ : WF p n' →+* W)).Finite
    exact RingHom.Finite.comp h.1.finite (RingHom.Finite.of_surjective _ φ.surjective)
  · show Function.Injective (j.comp (φ : WF p n' →+* W))
    have hj : Function.Injective j := by
      intro a b hab
      have h1 : algebraMap O Kf (j a) = algebraMap O Kf (j b) := congrArg _ hab
      rw [← h.1.ι_comp, ← h.1.ι_comp] at h1
      have := h.1.frac_alt
      exact IsFractionRing.injective W Qq (ι.injective h1)
    exact hj.comp φ.injective

def castVK {n' k r K : ℕ} (hk : k = r + K) : Fin n' × Fin (r + K) → Fin n' × Fin k :=
  fun v => (v.1, Fin.cast hk.symm v.2)

section Lift

variable (p n' : ℕ) [Fact p.Prime] [NeZero n'] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF p n') O] (w : O)

def SymbolRealisableGeneralRank {k r K : ℕ} [NeZero r] [NeZero K] (hk : k = r + K) (hrk : r ≤ k) (F : Frames n' r)
    (XXs : ℤ → Submodule O (SegRing O r K)) (deg dTop : Fin n' → ℕ) (c' Q E₀ : ℕ) : Prop :=
  ∃ E' : Fin n' → ℕ, (∀ t ∈ F.TT, E' t ≤ E₀ ∧ E' t ≤ deg t) ∧
    ∀ g : Matrix (Fin k) (Fin k) (WF p n'), IsGLW g →
    ∀ P ∈ Gen O p K F XXs (G2d F deg E'), ∀ T : ℕ, (∀ mm ∈ P.support, vsDeg mm ≤ T) →
      ∃ Fs : ℕ → ↥((Pol (KK O) (ι := Fin n') k dTop).restrictScalars O),
        (∀ o, HasMultideg (subst p n' O w n' r g (Fs o : MvPolynomial (TV n' k) (KK O))) dTop ∧
          InWj w (subst p n' O w n' r g (Fs o : MvPolynomial (TV n' k) (KK O))) 0 ∧
          Realisable p n' w n' r g c' o (subst p n' O w n' r g (Fs o : MvPolynomial (TV n' k) (KK O)))) ∧
        ∑ o ∈ Finset.range (T + 1), subst p n' O w n' r g (Fs o : MvPolynomial (TV n' k) (KK O)) =
          MvPolynomial.map (algebraMap O (KK O)) (rename (castVK hk) P) *
            subst p n' O w n' r g (SPtrue p n' O F hrk g c' Q)

theorem symbol_realisable_iff_general_rank {m r K : ℕ} [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (F : Frames n' r)
    (XXs : ℤ → Submodule O (SegRing O r K)) (deg dTop : Fin n' → ℕ) (c' Q E₀ : ℕ) :
    SymbolRealisableAt p n' O w hk hrk F XXs deg dTop c' Q E₀ ↔ SymbolRealisableGeneralRank p n' O w hk hrk F XXs deg dTop c' Q E₀ := Iff.rfl

end Lift

theorem symbol_realisable_general_rank (D : Formalism.BasicNotions.D7) (hW1 : GeneratorSpanInclusion) (hW2 : GeneratorImageIsSymbol) (hMon : RestMon) {p n' : ℕ} [Fact p.Prime] [NeZero n']
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF p n') O] (S : UniformizedDVR p O)
    (hO : OHyp p n' O S) {k r K : ℕ} [NeZero r] [NeZero K] (hk : k = r + K) (hH : CommonHypotheses p n' r k) (F : Frames n' r)
    (L₁ N₁ G' : ℕ) (hV : F.Valid L₁ N₁) (hT : TwistBound p F (p ^ G')) (hG : ∀ j : ℤ, zF F j - F.fr (j - 1) 0 ≤ G')
    (hK : N₁ + 2 * r ≤ K) (mg : ℤ → ℤ → ℤ) (th o : ℤ → ℤ → ℝ) (hmg : ∀ j x, 0 ≤ mg j x) (deg dTop : Fin n' → ℕ)
    (c' E₀ : ℕ) (hdT : ∀ s, dTop s = if s ∈ F.TT then deg s else 0)
    (hE1 : ∀ t ∈ F.TT, eSP p n' F k c' (p ^ G') t ≤ E₀ ∧ eSP p n' F k c' (p ^ G') t ≤ deg t)
    (hE0 : ∀ t, t ∉ F.TT → eSP p n' F k c' (p ^ G') t = 0) :
    SymbolRealisableGeneralRank p n' O S.w hk hH.2.2.1 F (fun j => XX' O r K F j (mg j) (th j) (o j)) deg dTop c' (p ^ G') E₀ := by
  subst hk
  refine ⟨eSP p n' F (r + K) c' (p ^ G'), hE1, ?_⟩
  intro g hg P hP T hT'
  let X : Ctx p n' r K O :=
    { S := S, hO := hO, hH := hH, Fr := F, L₁ := L₁, N₁ := N₁, G' := G', hV := hV, hT := hT, hG := hG, hK := hK,
      g := g, hg := hg }
  have hd : ∀ s, G2d F deg (eSP p n' F (r + K) c' (p ^ G')) s + eSP p n' F (r + K) c' (p ^ G') s = dTop s := by
    intro s
    unfold G2d
    rw [hdT s]
    by_cases hs : s ∈ F.TT
    · rw [ite_eq_left hs, ite_eq_left hs]
      have := (hE1 s hs).2
      omega
    · rw [ite_eq_right hs, ite_eq_right hs, hE0 s hs]
  have hd0 : ∀ s, s ∉ F.TT → G2d F deg (eSP p n' F (r + K) c' (p ^ G')) s = 0 := by
    intro s hs
    unfold G2d
    rw [ite_eq_right hs]
  have hren : rename (castVK (n' := n') (rfl : r + K = r + K)) P = P := by
    have : (castVK (n' := n') (rfl : r + K = r + K)) = id := by
      funext v
      rfl
    rw [this, rename_id_apply]
  rw [hren]
  exact exists_pol_family_of_mem_gen_of_vsDeg_le X D hW1 hW2 hMon c' mg th o hmg _ _ dTop hd hd0 (SPtrue_hom p n' O F hH.2.2.1 g c' (p ^ G')) P hP T hT'

theorem sources_realisable_holds (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz : ℝ) : SourcesRealisable D CLa Ck Crk Cdeg CLa' CD Csz := by
  intro hA _
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, a15, a16, a17, a18, _, a20, _⟩ := hA
  have hW1 : GeneratorSpanInclusion := generator_pair_conditions_of_admitted D a15 a16
  have hW2 : GeneratorImageIsSymbol := generator_path_homogeneous_holds D a17 a18 a20
  have hMon : RestMon := restMon D
  refine ⟨30, by norm_num, ?_⟩
  intro C hC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ _ K
    _ _ hk hrk F hF
  let _ : Algebra (WF p n') O := algOfIdent j φ
  rw [symbol_realisable_iff_general_rank]
  have hB := hyps_basic (C := C) (by linarith) H
  have hTT := hF.1
  have hGn : goodG' r de h x ≤ n' := by have := H.2.2.1.2.2.2; omega
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hH : CommonHypotheses p n' r (m + 1) := ⟨H.1, H.2.1, hrk, hSet.1.two_le, hSet.1.even⟩
  have eE : E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) =
      E0 p r (m + 1) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) := by rw [hk]
  rw [eE]
  show SymbolRealisableGeneralRank p n' O (dvrOfStd hSet).w hk hH.2.2.1 F (fun j => XX' O r K F j _ _ _) _ _ _ _ _
  refine symbol_realisable_general_rank D hW1 hW2 hMon O (dvrOfStd hSet) (oHyp_of hSet φ) hk hH F L₁ (orbitWindowCount r de h x) (goodG' r de h x)
    hF.2.1 (twist_of hF (by have := H.2.1; omega) hGn p (by have := H.1; omega))
    (fun j => (hF.2.2.1 j).le) (by omega) _ _ _ ?_ (flatDeg lam0) (dT TT lam0) (cPrime n' r TT.card c0 cpp cStar) _
    ?_ ?_ ?_
  · intro j x'
    positivity
  · intro s
    unfold dT
    rw [hTT]
  · intro t ht
    exact spdeg hC H hF t ht
  · intro t ht
    exact eSP_off hF _ _ _ t ht

end Formalism.MainNotions.Pf14
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.InitialLevelMonoWeights
section -- merged from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ScaleZpowMono
noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

section Scale

variable {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X] [Module O X]
  [IsScalarTower O Kf X]

theorem scale_zpow_mono (w : O) (hw : algebraMap O Kf w ≠ 0) {a b : ℤ} (hab : b ≤ a) (M : Submodule O X) :
    scale (algebraMap O Kf w ^ a) M ≤ scale (algebraMap O Kf w ^ b) M := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_scale.1 hx
  refine mem_scale.2 ⟨w ^ (a - b).toNat • y, M.smul_mem _ hy, ?_⟩
  rw [← algebraMap_smul Kf (w ^ (a - b).toNat) y, smul_smul, map_pow, ← zpow_natCast, ← zpow_add₀ hw]
  congr 2
  rw [Int.toNat_of_nonneg (by omega)]
  ring

theorem scale_mono (c : Kf) {M N : Submodule O X} (h : M ≤ N) : scale c M ≤ scale c N :=
  Submodule.map_mono h

end Scale

section Be

variable {Kf : Type} [Field Kf] {n' m : ℕ}

theorem be_add_left (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (F F' : Vsp Kf lam0)
    (G : Module.Dual Kf (Vsp Kf lam0)) : be p r lam0 (F + F') G = be p r lam0 F G + be p r lam0 F' G := by
  unfold be
  rw [smul_add, map_add (f := _)]

theorem be_smulK_left (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (c : Kf) (F : Vsp Kf lam0)
    (G : Module.Dual Kf (Vsp Kf lam0)) : be p r lam0 (c • F) G = c * be p r lam0 F G := by
  unfold be
  rw [smul_comm, map_smul, smul_eq_mul]

end Be

theorem edgeFamOf : EdgeFamOf := by
  intro D hM hBP hInc p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS m r fl rest lam0 hnu h1 h2 e he nb n2 T oS tT D1
    cStar c' hc' hD Fvb Sy sh hF1 hF2 hF3 hSy hsh hT
  have hw := w_ne_zero hS
  have hdom : IsDominant lam0 := by
    rw [hnu]
    exact isDominant_add h1 h2
  let eqv : Fin nb × Fin n2 ≃ Fin (nb * n2) := finProdFinEquiv
  let Fs : Fin nb × Fin n2 → Vsp Kf lam0 := fun x => mulV hnu h1 h2 (Fvb x.1) (sh x.2)
  let Ss : Fin nb × Fin n2 → Vsp Kf lam0 := fun x => mulV hnu h1 h2 (Sy x.1) (sh x.2)
  have hdiff : ∀ x, Fs x - Ss x ∈ scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r lam0 e) := by
    intro x
    have hz : ((Fs x - Ss x : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
        ((Fvb x.1 - Sy x.1 : Vsp Kf fl) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
          ((sh x.2 : Vsp Kf rest) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := by
      simp only [Fs, Ss, AddSubgroupClass.coe_sub, mulV_coe, sub_mul]
    have h0 : sh x.2 ∈ scale (algebraMap O Kf w ^ (0 : ℤ)) (Re p ι σ w r rest e) := by
      rw [zpow_zero]
      exact mem_scale.2 ⟨_, (hsh x.2).1, one_smul _ _⟩
    have h3 := Re_mul D hM p ι σ w hw r hnu h1 h2 e (c' : ℤ) 0 hz (hF2 x.1) h0
    rwa [add_zero] at h3
  have hSs : ∀ x, Ss x ∈ Re p ι σ w r lam0 e := fun x =>
    edge_lattice_mul_of_weight_sum D hM p ι σ w hw r hnu h1 h2 e (z := Ss x) rfl (hSy x.1) (hsh x.2).1
  refine ⟨fun i => Fs (eqv.symm i), ?_, ?_, ?_⟩
  · intro i
    constructor
    · have h3 := HL_mul (O := O) D hM ι σ hnu h1 h2 e.src (algebraMap O Kf w) hw (-(T : ℤ)) (-(oS : ℤ))
        (z := Fs (eqv.symm i)) rfl (hF1 _) (hsh _).2
      have e1 : (-(T : ℤ)) + (-(oS : ℤ)) = -((T + oS : ℕ) : ℤ) := by
        push_cast
        ring
      rwa [e1] at h3
    · have e2 : Fs (eqv.symm i) = Ss (eqv.symm i) + (Fs (eqv.symm i) - Ss (eqv.symm i)) := by abel
      show Fs (eqv.symm i) ∈ Re p ι σ w r lam0 e
      rw [e2]
      exact Submodule.add_mem _ (hSs _) (scale_pos_le w c' _ (hdiff _))
  · intro i e' he' hsrc hne
    have hI := (hInc p n' W Qq O Kf ι σ j w hS m r rest h2 e' he').1
    have hs : sh (eqv.symm i).2 ∈ scale (algebraMap O Kf w ^ (-(oS : ℤ))) (Re p ι σ w r rest e') := by
      apply scale_mono _ hI
      rw [hsrc]
      exact (hsh _).2
    have h3 := Re_mul D hM p ι σ w hw r hnu h1 h2 e' (c' : ℤ) (-(oS : ℤ)) (z := Fs (eqv.symm i)) rfl
      (hF3 _ e' he' hsrc hne) hs
    exact scale_zpow_mono w hw (by omega) _ h3
  · rintro c ⟨i0, hi0⟩
    obtain ⟨G, hG1, hG2, hG3, ⟨a, b, ha, hab⟩⟩ := hT (fun x => c (eqv x))
      ⟨eqv.symm i0, by simpa using hi0⟩
    refine ⟨G, hG1, hG2, hG3, ?_⟩
    have e1 : (∑ i, c i • Fs (eqv.symm i)) =
        (∑ x, c (eqv x) • Ss x) + ∑ x, c (eqv x) • (Fs x - Ss x) := by
      rw [← Finset.sum_add_distrib, ← Equiv.sum_comp eqv]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Equiv.symm_apply_apply, ← smul_add]
      congr 1
      abel
    have hE : (∑ x, c (eqv x) • (Fs x - Ss x)) ∈
        scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r lam0 e) :=
      Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (hdiff x)
    obtain ⟨y, hy, hyE⟩ := mem_scale.1 hE
    obtain ⟨z, hz⟩ := ((hBP p n' W Qq O Kf ι σ j w hS m r lam0 hdom e he).1 G).1 hG2 y hy
    have hwc : w ^ c' = (p : O) ^ (D1 + 1) * w ^ (c' - 2 * (D1 + 1)) := by
      rw [← hS.w_sq, ← pow_mul, ← pow_add]
      congr 1
      omega
    obtain ⟨b', hb'⟩ := dvd_of_add (p : O) (p_nonunit hS) D1 a (w ^ (c' - 2 * (D1 + 1)) * z) ⟨b, hab.symm⟩
    refine ⟨a + (p : O) ^ (D1 + 1) * (w ^ (c' - 2 * (D1 + 1)) * z), b', ?_, hb'.symm⟩
    show be p r lam0 (∑ i, c i • Fs (eqv.symm i)) G = _
    rw [e1, be_add_left, ha, ← hyE, be_smulK_left, ← hz, zpow_natCast, ← map_pow, hwc]
    simp only [map_add (f := _), map_mul]
    ring

end Formalism.MainNotions.Pf14
end
end

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning MvPolynomial

theorem initial_level_nonneg {C Ct0 : ℝ} (hC : 0 ≤ C) (h0 : 0 ≤ Ct0) (p N N₁ L₁ G' k : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    0 ≤ t0 C Ct0 p N N₁ L₁ G' k a := by
  unfold t0 tableLineDegreeFive.La
  have hl : 0 ≤ Real.log a := Real.log_nonneg ha
  have ha0 : 0 ≤ a := by linarith
  positivity

theorem initial_level_mono_weights {C Ct0 Ct0' : ℝ} (hC : 0 ≤ C) (h : Ct0 ≤ Ct0') (p N N₁ L₁ G' k : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    t0 C Ct0 p N N₁ L₁ G' k a ≤ t0 C Ct0' p N N₁ L₁ G' k a := by
  unfold t0 tableLineDegreeFive.La
  have hl : 0 ≤ Real.log a := Real.log_nonneg ha
  have ha0 : 0 ≤ a := by linarith
  have hB : 0 ≤ C * (N₁ : ℝ) ^ 2 * Real.log a * a / (p * k) + a * (p : ℝ) ^ (-(L₁ : ℤ)) + k * (p : ℝ) ^ G' := by
    positivity
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hN) hB

theorem edgeStep_of (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg)
    (Ct0 CD1 C₂ C₃ : ℝ) (h0 : 0 < Ct0) (h1 : 0 < CD1)
    (hL3 : ∀ C : ℝ, C₂ ≤ C → SymbolRealisableBound C CLa) (hCl : ∀ C : ℝ, C₃ ≤ C → CloudStep C Ct0 CD1 CLa) :
    ∃ Ct0' CD1' Cr C₁ : ℝ, 0 < Ct0' ∧ 0 < CD1' ∧ 0 < Cr ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → EdgeStep C Ct0' CD1' Cr := by
  have hInc : DualHeightInclusion := hA.2.2.1
  have hBP : BePerfect := hA.2.2.2.1
  have h26 : Formalism.MainNotions.SelectionLemmas.Conclusion2 D CLa Ck Crk Cdeg := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hWI : WittIdent := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hM : tableLineDegreeFive.LevelPrimesProviso D := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨Cg, hCg1, hg2⟩ := symbol_space_at D CLa Ck Crk Cdeg h26
  refine ⟨max Ct0 |Cdeg|, CD1, max Crk 1, max Cg (max C₂ (max C₃ (max 2 (max |CLa| CD1)))),
    lt_of_lt_of_le h0 (le_max_left _ _), h1, lt_of_lt_of_le one_pos (le_max_right _ _),
    lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
  intro C hC
  have c1 : Cg ≤ C := le_trans (le_max_left _ _) hC
  have hC' := le_trans (le_max_right _ _) hC
  have c2 : C₂ ≤ C := le_trans (le_max_left _ _) hC'
  have hC'' := le_trans (le_max_right _ _) hC'
  have c3 : C₃ ≤ C := le_trans (le_max_left _ _) hC''
  have hC3 := le_trans (le_max_right _ _) hC''
  have c4 : 2 ≤ C := le_trans (le_max_left _ _) hC3
  have hC4 := le_trans (le_max_right _ _) hC3
  have c5 : |CLa| ≤ C := le_trans (le_max_left _ _) hC4
  have c6 : CD1 ≤ C := le_trans (le_max_right _ _) hC4
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H e he htgt
  have : Fact p.Prime := ⟨hSet.1.prime⟩
  have : NeZero n' := ⟨by have := hSet.1.two_le; omega⟩
  have hB := hyps_basic (C := C) (by linarith) H
  have hr2 : 2 ≤ r := H.2.1
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hcS : 8 * (Dp + 1) ≤ cStar := H.2.2.2.2.2.2.2.2.2.2.1
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  obtain ⟨K, hk⟩ : ∃ K, m + 1 = r + K := ⟨m + 1 - r, by omega⟩
  have : NeZero r := ⟨by omega⟩
  have : NeZero K := ⟨by omega⟩
  have hrk : r ≤ m + 1 := by omega
  have hw := w_ne_zero hSet.1
  have ha1 : (1 : ℝ) ≤ a := by linarith [hB.two_le_a]
  obtain ⟨φ, hφ⟩ := hWI p n' W Qq O Kf ι σ j w hSet.1
  obtain ⟨F, hF⟩ := frames_of TT r L₁ L₂ de h x hSet.1.even hr2 hB.one_le_depth_alt H.2.2.1
  have hTT := hF.1
  subst hTT
  let _ : Algebra (WF p n') O := algOfIdent j φ
  obtain ⟨E', hE', hL⟩ := hL3 C c2 p W Qq O Kf ι σ j w n' m r F.TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H
    φ hφ K hk hrk F hF
  have hG2 := hg2 C c1 p W Qq O Kf ι σ j w n' m r F.TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H K hk F hF E'
    (fun t ht => (hE' t ht).1)
  obtain ⟨⟨Sg, hle, hcompl, ⟨ιb, b, hb⟩, hrank, _⟩, hdeg⟩ := hG2
  obtain ⟨B, hBgen, hBli, hBc⟩ := basis_fin Sg b hcompl
    (fun P => P ∈ Gen O p K F
      (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * F.TT.card))
        (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r F.TT.card c0 cpp cStar)) a Y)
      (G2d F (flatDeg lam0) E')) hb
  obtain ⟨hm, hhm, hsrc⟩ := he.1
  obtain ⟨hE1, _, _⟩ := edgePlane p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r hm hhm
  obtain ⟨g, hg, hbasis⟩ := hE1 e he hsrc
  set X : ℝ := Cdeg * (F.TT.card : ℝ) *
    (CLa * ((min (orbitWindowCount r de h x) (2 * F.TT.card) : ℕ) : ℝ) ^ 2 * Real.log a * a / ((p : ℝ) * ((r + K : ℕ) : ℝ)) +
      a * (p : ℝ) ^ (-(L₁ : ℤ)) + ((r + K : ℕ) : ℝ) * (p : ℝ) ^ goodG' r de h x) with hX
  have hT : ∀ i, ∀ mm ∈ (B i).support, vsDeg mm ≤ ⌊X⌋₊ := fun i mm hmm =>
    Nat.le_floor (hdeg (B i) (Submodule.subset_span (hBgen i)) mm hmm)
  choose Fs hFs1 hFs2 using fun i => hL g hg (B i) (hBgen i) ⌊X⌋₊ (hT i)
  obtain ⟨Θ, hΘ, n2, oS, tT, D1, sh, hoS, htT, hD1, hsh, hcount, htests⟩ :=
    hCl C c3 p W Qq O Kf ι σ j w n' m r F.TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K hk hrk F hF E' hE'
      _ B hBgen hBli hBc e he htgt hm g hhm hg hbasis (fun i => ∑ o ∈ Finset.range (⌊X⌋₊ + 1), Fs i o)
      (by
        intro i
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← hFs2 i, Submodule.coe_sum, map_sum])
  choose Fv hv1 hv2 hv3 using fun (i : Fin (Module.finrank O Sg)) (o : ℕ) =>
    flatSrc edgePlane p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r (dT F.TT lam0) hm hhm Θ hΘ g hg e hbasis
      (cPrime n' r F.TT.card c0 cpp cStar) o _ (Fs i o) (hFs1 i o).1 rfl (hFs1 i o).2.2
  obtain ⟨_, _, hn3, _⟩ := num C 1 CD1 1 one_pos h1 one_pos c4 (by linarith) c6 (by linarith) p n' m r F.TT L₁ L₂ de h x
    lam0 aT bT a Y cpp c0 Dp cStar H
  have hD1' : D1 ≤ Dp := by
    have : (D1 : ℝ) ≤ Dp := le_trans hD1 hn3
    exact_mod_cast this
  have hoS' : oS ≤ r * F.TT.card * c0 + 2 * r * n' * cpp := by
    have : (oS : ℝ) ≤ ((r * F.TT.card * c0 + 2 * r * n' * cpp : ℕ) : ℝ) := by
      refine le_trans hoS ?_
      unfold om
      push_cast
      exact le_refl _
    exact_mod_cast this
  have hfam := edgeFamOf D hM hBP hInc p n' W Qq O Kf ι σ j w hSet.1 m r (flW (dT F.TT lam0)) (restW F.TT lam0) lam0
    (lambda_zero_eq_product F.TT lam0) (flW_dom _) (restW_dom (by have := hB.m_ge; omega) F.TT lam0 hdom) e he
    (Module.finrank O Sg) n2 ⌊X⌋₊ oS tT D1 cStar (cPrime n' r F.TT.card c0 cpp cStar)
    (by unfold cPrime; omega) (by unfold cPrime; omega)
    (fun i => ∑ o ∈ Finset.range (⌊X⌋₊ + 1), Fv i o)
    (fun i => Θ (∑ o ∈ Finset.range (⌊X⌋₊ + 1), Fs i o)) sh
    (by
      intro i
      refine Submodule.sum_mem _ fun o ho => ?_
      rw [hsrc]
      exact scale_neg_mono w hw (Nat.lt_succ_iff.1 (Finset.mem_range.1 ho)) _ (hv1 i o))
    (by
      intro i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← Finset.sum_sub_distrib]
      exact Submodule.sum_mem _ fun o _ => hv2 i o)
    (by
      intro i e' he' hs' hne
      exact Submodule.sum_mem _ fun o _ => hv3 i o e' he' (hs'.trans hsrc) hne)
    (by
      intro i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Submodule.sum_mem _ fun o _ => ?_
      exact scale_pos_le w 0 _ ((hΘ.2 g hg e hbasis (Fs i o) 0).1 (hFs1 i o).2.1))
    hsh
    (fun c hc => htests _ (fun _ _ => rfl) c hc)
  have hkR : ((r + K : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) := by rw [hk]
  have hXle : X ≤ t0 C (max Ct0 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a := by
    rw [hX, hkR]
    exact level_lower_bound_terms Cdeg CLa C (max Ct0 |Cdeg|) (le_max_right _ _) c5
      p F.TT.card (orbitWindowCount r de h x) (min (orbitWindowCount r de h x) (2 * F.TT.card)) L₁ (goodG' r de h x) (m + 1)
      (min_le_left _ _) (by have := H.1; omega) (by omega) a ha1
  have ht0 := initial_level_nonneg (C := C) (Ct0 := max Ct0 |Cdeg|) (by linarith) (le_trans h0.le (le_max_left _ _)) p F.TT.card
    (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) ha1
  have hTle : ((⌊X⌋₊ : ℕ) : ℝ) ≤ t0 C (max Ct0 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a := by
    rcases le_or_gt 0 X with hx0 | hx0
    · exact le_trans (Nat.floor_le hx0) hXle
    · rw [Nat.floor_of_nonpos hx0.le]
      simpa using ht0
  refine ⟨Module.finrank O Sg * n2, ⌊X⌋₊ + oS, tT, D1, ?_, ?_, hD1, ?_, hfam⟩
  · push_cast
    linarith
  · have := initial_level_mono_weights (C := C) (by linarith) (le_max_left Ct0 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x)
      (m + 1) ha1
    linarith
  · have hK : m + 1 - r = K := by omega
    have hp0 : (0 : ℝ) < p := by
      have : 0 < p := by have := H.1; omega
      exact_mod_cast this
    have hY : 0 < Y := by linarith [hB.two_le_Y]
    have hu : 0 ≤ (1 - ((m + 1 : ℕ) : ℝ) * c0 / a) ^ F.TT.card :=
      pow_nonneg (by linarith [rank_mul_conductor_div_le_one c4 H]) _
    have hPi : ∏ t ∈ F.TT, ((Nat.choose (flatDeg lam0 t + (r + K) - 1) (r + K - 1) : ℕ) : ℝ) =
        ∏ t ∈ F.TT, ((Nat.choose (flatDeg lam0 t + (m + 1) - 1) (m + 1 - 1) : ℕ) : ℝ) := by rw [hk]
    have hq : ((p : ℝ) ^ n') ^ (-((r * K : ℕ) : ℤ)) = ((p : ℝ) ^ (n' * (r * (m + 1 - r))))⁻¹ := by
      rw [zpow_neg, zpow_natCast, ← pow_mul, hK]
    rw [hq, hPi, hkR] at hrank
    have := norm_index_count_bound Crk (max Crk 1) ((F.TT.card : ℝ) * (r : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) / Y)
      ((1 - ((m + 1 : ℕ) : ℝ) * c0 / a) ^ F.TT.card) (dimV Kf lam0 : ℝ)
      (∏ t ∈ F.TT, ((Nat.choose (flatDeg lam0 t + (m + 1) - 1) (m + 1 - 1) : ℕ) : ℝ))
      ((p : ℝ) ^ (n' * (r * (m + 1 - r)))) (Module.finrank O Sg) n2 (le_max_left _ _)
      (div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)) (Nat.cast_nonneg _)) hY.le) hu
      (Nat.cast_nonneg _) (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _) (pow_pos hp0 _)
      (by
        refine le_trans (le_of_eq ?_) hrank
        ring)
      hcount
    refine le_trans (le_of_eq ?_) this
    ring

theorem restEdge_of (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hR3 : SourcesRealisable D CLa Ck Crk Cdeg CLa' CD Csz)
    (hRC : RestCloud D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) :
    RestEdge D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 := by
  intro hA h14a h14b
  obtain ⟨C₂, _, hL3⟩ := hR3 hA h14a
  obtain ⟨Ct0, CD1, C₃, h0, h1, _, hCl⟩ := hRC hA h14a h14b
  exact edgeStep_of D CLa Ck Crk Cdeg hA Ct0 CD1 C₂ C₃ h0 h1 hL3 hCl

end Formalism.MainNotions.Pf14
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ColSpanMap
noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G

section Incl

variable (W Qq : Type) [CommRing W] [IsDomain W] [Field Qq] [Algebra W Qq]

def incl (k : ℕ) : (Fin k → W) →ₗ[W] (Fin k → Qq) := (Algebra.linearMap W Qq).compLeft (Fin k)

variable {W Qq}

theorem incl_apply {k : ℕ} (y : Fin k → W) (i : Fin k) : incl W Qq k y i = algebraMap W Qq (y i) := rfl

theorem incl_inj [IsFractionRing W Qq] (k : ℕ) : Function.Injective (incl W Qq k) := by
  intro x y h
  funext i
  have h1 := congrFun h i
  rw [incl_apply, incl_apply] at h1
  exact IsFractionRing.injective W Qq h1

theorem colSpan_map {k : ℕ} (M : Matrix (Fin k) (Fin k) W) :
    colSpan W (M.map (algebraMap W Qq)) =
      (Submodule.span W (Set.range fun c : Fin k => fun i => M i c)).map (incl W Qq k) := by
  unfold colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem colSpan_one (k : ℕ) :
    colSpan W (1 : Matrix (Fin k) (Fin k) Qq) = LinearMap.range (incl W Qq k) := by
  have h1 : (1 : Matrix (Fin k) (Fin k) Qq) = (1 : Matrix (Fin k) (Fin k) W).map (algebraMap W Qq) :=
    (Matrix.map_one _ (map_zero _) (map_one _)).symm
  rw [h1, colSpan_map, LinearMap.range_eq_map]
  congr 1
  rw [← (Pi.basisFun W (Fin k)).span_eq]
  congr 1
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    funext i
    simp [Matrix.one_apply, Pi.single_apply]
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    funext i
    simp [Matrix.one_apply, Pi.single_apply]

theorem lattice_of [IsPrincipalIdealRing W] [IsFractionRing W Qq] (p k : ℕ) (hp0 : (p : W) ≠ 0)
    (N : Submodule W (Fin k → W)) (hpN : ∀ x, (p : W) • x ∈ N) : IsLattice W (N.map (incl W Qq k)) := by
  classical
  haveI : Module.Free W N := Module.Free.of_basis (Submodule.basisOfPid (Pi.basisFun W (Fin k)) N).2
  have hfin : Module.finrank W N = k := by
    apply le_antisymm
    · calc Module.finrank W N ≤ Module.finrank W (Fin k → W) := Submodule.finrank_le N
        _ = k := by simp
    · let f : (Fin k → W) →ₗ[W] N := LinearMap.codRestrict N ((p : W) • LinearMap.id) (fun c => by simpa using hpN c)
      have hinj : Function.Injective f := by
        intro x y hxy
        have h2 := congrArg Subtype.val hxy
        simp only [f, LinearMap.codRestrict_apply, LinearMap.smul_apply, LinearMap.id_apply] at h2
        exact smul_right_injective (Fin k → W) hp0 h2
      have h3 := LinearMap.finrank_le_finrank_of_injective hinj
      simpa using h3
  let b' : Module.Basis (Fin k) W N := Module.finBasisOfFinrankEq W N hfin
  let M : Matrix (Fin k) (Fin k) W := fun i c => (b' c : Fin k → W) i
  have hspan : Submodule.span W (Set.range fun c => (b' c : Fin k → W)) = N := by
    have h1 := congrArg (Submodule.map N.subtype) b'.span_eq
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h1
    exact h1
  let A : Matrix (Fin k) (Fin k) W := fun c i => b'.repr ⟨(p : W) • Pi.single i 1, hpN _⟩ c
  have hMA : M * A = (p : W) • (1 : Matrix (Fin k) (Fin k) W) := by
    ext a i
    have hx := congrArg (fun v : N => (v : Fin k → W) a) (b'.sum_repr ⟨(p : W) • Pi.single i 1, hpN _⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply] at hx
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ← hx]
    exact Finset.sum_congr rfl (fun c _ => by simp only [M, A]; ring)
  have hdetM : M.det ≠ 0 := by
    intro h0
    have h4 := congrArg Matrix.det hMA
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h4
    exact pow_ne_zero k hp0 h4.symm
  refine ⟨M.map (algebraMap W Qq), ?_, ?_⟩
  · rw [isUnit_iff_ne_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ (IsFractionRing.injective W Qq)).mpr hdetM
  · rw [colSpan_map]
    congr 1
    exact hspan.symm

theorem card_quot [IsFractionRing W Qq] (k : ℕ) (T : Submodule W (Fin k → Qq))
    (hT : T = LinearMap.range (incl W Qq k)) (N : Submodule W (Fin k → W)) :
    Nat.card (↥T ⧸ Submodule.comap T.subtype (N.map (incl W Qq k))) = Nat.card ((Fin k → W) ⧸ N) := by
  subst hT
  refine Nat.card_congr (Submodule.Quotient.equiv N _ (LinearEquiv.ofInjective (incl W Qq k) (incl_inj k)) ?_).toEquiv.symm
  ext ⟨y, hy⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    have h1 := congrArg Subtype.val hxy
    simpa [LinearEquiv.ofInjective_apply] using h1
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    apply Subtype.ext
    simpa [LinearEquiv.ofInjective_apply] using hxy

end Incl

section Psi

variable {W : Type} [CommRing W]

def psi {r K : ℕ} (I : Ideal W) (A : Fin r → Fin K → W) : (Fin (r + K) → W) →ₗ[W] (Fin r → W ⧸ I) :=
  LinearMap.pi fun i =>
    (Submodule.mkQ I) ∘ₗ (LinearMap.proj (Fin.castAdd K i) + ∑ c, A i c • LinearMap.proj (Fin.natAdd r c))

theorem psi_apply {r K : ℕ} (I : Ideal W) (A : Fin r → Fin K → W) (y : Fin (r + K) → W) (i : Fin r) :
    psi I A y i = Ideal.Quotient.mk I (y (Fin.castAdd K i) + ∑ c, A i c * y (Fin.natAdd r c)) := by
  simp [psi, LinearMap.sum_apply]

theorem psi_surj {r K : ℕ} (I : Ideal W) (A : Fin r → Fin K → W) : Function.Surjective (psi I A) := by
  intro z
  choose f hf using fun i => Ideal.Quotient.mk_surjective (I := I) (z i)
  refine ⟨Fin.append f 0, ?_⟩
  funext i
  rw [psi_apply, Fin.append_left]
  simp [Fin.append_right, hf]

theorem psi_smul {r K : ℕ} (I : Ideal W) (a : W) (ha : a ∈ I) (A : Fin r → Fin K → W) (x : Fin (r + K) → W) :
    a • x ∈ LinearMap.ker (psi I A) := by
  rw [LinearMap.mem_ker, map_smul]
  funext i
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (psi I A x i)
  rw [Pi.smul_apply, ← hy, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul, Pi.zero_apply]

theorem psi_ker_inj {r K : ℕ} (I : Ideal W) (A B : Fin r → Fin K → W)
    (h : LinearMap.ker (psi I A) = LinearMap.ker (psi I B)) (i : Fin r) (c : Fin K) :
    Ideal.Quotient.mk I (A i c) = Ideal.Quotient.mk I (B i c) := by
  have key : ∀ Z : Fin r → Fin K → W, ∀ i', psi I Z (Fin.append (fun i'' => -A i'' c) (Pi.single c 1)) i' =
      Ideal.Quotient.mk I (-A i' c + Z i' c) := by
    intro Z i'
    rw [psi_apply, Fin.append_left]
    congr 1
    simp [Fin.append_right, Pi.single_apply]
  have hA : Fin.append (fun i'' => -A i'' c) (Pi.single c 1) ∈ LinearMap.ker (psi I A) := by
    rw [LinearMap.mem_ker]
    funext i'
    rw [key, Pi.zero_apply]
    simp
  rw [h, LinearMap.mem_ker] at hA
  have h1 := congrFun hA i
  rw [key, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at h1
  rw [eq_comm, Ideal.Quotient.eq]
  convert h1 using 1
  ring

end Psi

theorem manyEdges : ManyEdges := by
  classical
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS k r hrk
  obtain ⟨K, rfl⟩ : ∃ K, k = r + K := ⟨k - r, by omega⟩
  haveI := hS.frac_alt
  set I : Ideal W := Ideal.span {(p : W)} with hI
  have hpI : (p : W) ∈ I := Ideal.mem_span_singleton_self _
  have hp0 : (p : W) ≠ 0 := hS.p_unif.ne_zero
  have hcard : Nat.card (W ⧸ I) = p ^ n' := hS.res_card
  haveI : Finite (W ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hS.prime.ne_zero)
  haveI : Fintype (W ⧸ I) := Fintype.ofFinite _
  choose lift hlift using (Ideal.Quotient.mk_surjective (I := I))
  let ed : (Fin r → Fin K → W ⧸ I) → Edge W Qq (r + K) := fun A =>
    ⟨(LinearMap.ker (psi I (fun i c => lift (A i c)))).map (incl W Qq (r + K)),
      colSpan W (1 : Matrix (Fin (r + K)) (Fin (r + K)) Qq)⟩
  have hinj : Function.Injective ed := by
    intro A B hAB
    have h1 := congrArg Edge.src hAB
    have h2 := Submodule.map_injective_of_injective (incl_inj (W := W) (Qq := Qq) (r + K)) h1
    funext i c
    have h3 := psi_ker_inj I _ _ h2 i c
    rwa [hlift, hlift] at h3
  refine ⟨Finset.univ.image ed, ?_, ?_⟩
  · intro e he
    obtain ⟨A, -, rfl⟩ := Finset.mem_image.mp he
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, rfl⟩
    · exact lattice_of (Qq := Qq) p (r + K) hp0 _ (fun x => psi_smul I (p : W) hpI _ x)
    · exact ⟨1, by simp, rfl⟩
    · show _ ≤ colSpan W (1 : Matrix (Fin (r + K)) (Fin (r + K)) Qq)
      rw [colSpan_one]
      exact LinearMap.map_le_range
    · intro x hx
      change x ∈ colSpan W (1 : Matrix (Fin (r + K)) (Fin (r + K)) Qq) at hx
      rw [colSpan_one] at hx
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
      exact Submodule.mem_map.mpr ⟨(p : W) • y, psi_smul I (p : W) hpI _ y, map_smul _ _ _⟩
    · refine (card_quot (r + K) _ (colSpan_one (r + K)) _).trans ?_
      rw [Nat.card_congr (LinearMap.quotKerEquivOfSurjective _ (psi_surj I _)).toEquiv]
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, hcard,
        ← pow_mul]
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin, ← Nat.card_eq_fintype_card, hcard, Nat.add_sub_cancel_left,
      ← pow_mul, ← pow_mul]
    apply le_of_eq
    congr 1
    ring

end Formalism.MainNotions.Pf14
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ScaleEdges.TheoremIIOfEdgeBoundConstants
noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

theorem prvE_of_gl_operators_form_representation (D : Formalism.BasicNotions.D7) (hME : ManyEdges) (hS7 : S7) (hAsm : Asm) (hNum : Num)
    (hBP : BePerfect) (hOE : LPOneEvery)
    (Ct0 CD1 Cr C₁ : ℝ) (h0 : 0 < Ct0) (h1 : 0 < CD1) (h2 : 0 < Cr) (h3 : 0 < C₁)
    (hE : ∀ C : ℝ, C₁ ≤ C → EdgeStep C Ct0 CD1 Cr) : tableLineDegreeFive.ConclusionE D := by
  refine ⟨max C₁ (max 2 (max Ct0 (max CD1 (Cr + 1)))), lt_of_lt_of_le h3 (le_max_left _ _), ?_⟩
  intro C hC
  have hC1 : C₁ ≤ C := le_trans (le_max_left _ _) hC
  have hC' := le_trans (le_max_right _ _) hC
  have hC2 : 2 ≤ C := le_trans (le_max_left _ _) hC'
  have hC'' := le_trans (le_max_right _ _) hC'
  have hC3 : Ct0 ≤ C := le_trans (le_max_left _ _) hC''
  have hC''' := le_trans (le_max_right _ _) hC''
  have hC4 : CD1 ≤ C := le_trans (le_max_left _ _) hC'''
  have hC5 : Cr + 1 ≤ C := le_trans (le_max_right _ _) hC'''
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet hp hr
    hOrb hN1 hWt hY hLa hk hL1 hD hc hsz t ht
  have hH : Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar :=
    ⟨hp, hr, hOrb, hN1, hWt, hY, hLa, hk, hL1, hD, hc, hsz⟩
  have hdom : IsDominant lam0 := hWt.2.1
  apply hOE p n' W Qq O Kf ι σ j w hSet.1 m r lam0 t Dp _ cStar hdom
  refine ⟨by omega, colSpan W 1, ⟨1, by simp, rfl⟩, ?_⟩
  apply hS7 p n' W Qq O Kf ι σ j w hSet.1 hBP m r lam0 t Dp _ cStar _ hdom (by omega)
  obtain ⟨E, hE1, hE2⟩ := hME p n' W Qq O Kf ι σ j w hSet.1 (m + 1) r (by omega)
  obtain ⟨hn1, hn2, hn3, hn4⟩ := hNum C Ct0 CD1 Cr h0 h1 h2 hC2 hC3 hC4 hC5 p n' m r TT L₁ L₂ de h x lam0 aT bT a Y
    cpp c0 Dp cStar hH
  have key : ∀ e ∈ E, _ := fun e he =>
    hE C hC1 p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet hH e
      (hE1 e he).1 (hE1 e he).2
  choose! nE tS tT D1 hkey using key
  apply hAsm p n' W Qq O Kf ι σ j w hSet.1 m r lam0 t Dp _ cStar _ E nE hE1
  · intro e he
    obtain ⟨a1, a2, a3, _, a5⟩ := hkey e he
    refine ⟨tS e, tT e, D1 e, ?_, ?_, ?_, a5⟩
    · have : (tS e : ℝ) ≤ t := by linarith
      exact_mod_cast this
    · have : (tT e : ℝ) ≤ t := by linarith
      exact_mod_cast this
    · have : (D1 e : ℝ) ≤ Dp := by linarith
      exact_mod_cast this
  · set ρ : ℝ := (1 - Cr * (TT.card : ℝ) * (r : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) / Y) *
      (1 - ((m + 1 : ℕ) : ℝ) * c0 / a) ^ TT.card with hρ
    set Qr : ℝ := (p : ℝ) ^ (n' * (r * (m + 1 - r))) with hQr
    have hp0 : (0 : ℝ) < p := by
      have : 0 < p := by omega
      exact_mod_cast this
    have hQpos : 0 < Qr := pow_pos hp0 _
    have hdim : (0 : ℝ) ≤ (dimV Kf lam0 : ℝ) := Nat.cast_nonneg _
    have hle : (1 - C * TT.card * (r : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) / Y) * (dimV Kf lam0 : ℝ) ≤
        ρ * (dimV Kf lam0 : ℝ) := mul_le_mul_of_nonneg_right hn4 hdim
    refine le_trans hle ?_
    rcases le_or_gt 0 (ρ * (dimV Kf lam0 : ℝ)) with hpos | hneg
    · have hsum : (E.card : ℝ) * (ρ * (dimV Kf lam0 : ℝ) / Qr) ≤ ((∑ e ∈ E, nE e : ℕ) : ℝ) := by
        push_cast
        rw [← nsmul_eq_mul]
        apply Finset.card_nsmul_le_sum
        intro e he
        exact (hkey e he).2.2.2.1
      have hcard : Qr ≤ (E.card : ℝ) := by
        rw [hQr]
        exact_mod_cast hE2
      have : Qr * (ρ * (dimV Kf lam0 : ℝ) / Qr) ≤ (E.card : ℝ) * (ρ * (dimV Kf lam0 : ℝ) / Qr) :=
        mul_le_mul_of_nonneg_right hcard (div_nonneg hpos hQpos.le)
      have h4 : Qr * (ρ * (dimV Kf lam0 : ℝ) / Qr) = ρ * (dimV Kf lam0 : ℝ) := by
        field_simp
      linarith
    · exact le_trans hneg.le (Nat.cast_nonneg _)

theorem theorem_II_of_edge_bound_constants (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hME : ManyEdges) (hS7 : S7) (hAsm : Asm) (hNum : Num)
    (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) (h14a : SourceCleaning.aux₃ D CLa' CD Csz) (h14b : PlaneGramData.aux₃ D CH CE C6 C18)
    (hR : RestEdge D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ConclusionE D := by
  obtain ⟨Ct0, CD1, Cr, C₁, h0, h1, h2, h3, hE⟩ := hR hA h14a h14b
  have hBP : BePerfect := hA.2.2.2.1
  have hOE : LPOneEvery := hA.2.2.2.2.1
  exact prvE_of_gl_operators_form_representation D hME hS7 hAsm hNum hBP hOE Ct0 CD1 Cr C₁ h0 h1 h2 h3 hE

end Formalism.MainNotions.Pf14
end
end

noncomputable section

namespace Formalism.MainNotions.Pf14

theorem theorem_II_of_edge_bound (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) (h14a : SourceCleaning.aux₃ D CLa' CD Csz) (h14b : PlaneGramData.aux₃ D CH CE C6 C18)
    (hR : RestEdge D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ConclusionE D :=
  theorem_II_of_edge_bound_constants D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 manyEdges s7 asm num hA h14a h14b hR

theorem prvE_degree_five_of_adm_sources_realisable (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) (h14a : SourceCleaning.aux₃ D CLa' CD Csz) (h14b : PlaneGramData.aux₃ D CH CE C6 C18)
    (hR3 : SourcesRealisable D CLa Ck Crk Cdeg CLa' CD Csz)
    (hRC : RestCloud D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ConclusionE D :=
  theorem_II_of_edge_bound D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hA h14a h14b
    (restEdge_of D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hR3 hRC)

theorem theorem_II_of_cloud_bound (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) (h14a : SourceCleaning.aux₃ D CLa' CD Csz) (h14b : PlaneGramData.aux₃ D CH CE C6 C18)
    (hRC : RestCloud D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ConclusionE D :=
  prvE_degree_five_of_adm_sources_realisable D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hA h14a h14b (sources_realisable_holds D CLa Ck Crk Cdeg CLa' CD Csz) hRC

theorem theorem_II_of_cloud_bound_X (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) (h14a : SourceCleaning.aux₃ D CLa' CD Csz) (h14b : PlaneGramData.aux₃ D CH CE C6 C18)
    (hRC : RestCloudX D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ConclusionE D :=
  theorem_II_of_cloud_bound D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hA h14a h14b
    (restCloud_of_X D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hRC)

theorem theorem_II_of_cloud_bound_Y (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) (h14a : SourceCleaning.aux₃ D CLa' CD Csz) (h14b : PlaneGramData.aux₃ D CH CE C6 C18)
    (hRC : RestCloudY D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ConclusionE D :=
  theorem_II_of_cloud_bound_X D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hA h14a h14b
    (restCloudX_of_Y D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hRC)

theorem theorem_II_of_split_cloud_bounds (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) (h14a : SourceCleaning.aux₃ D CLa' CD Csz) (h14b : PlaneGramData.aux₃ D CH CE C6 C18)
    (h6a : SourcePrimitiveIntegrality D CLa Ck Crk Cdeg) (h6b : RemainingInputsAfter D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ConclusionE D :=
  theorem_II_of_cloud_bound_Y D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 hA h14a h14b
    (restCloudY_of D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 h6a h6b)

end Formalism.MainNotions.Pf14
end
end

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.L2.G.Model (Nv)

def Xs (m : ℕ) (top vec : Bool) (ν : Fin (m + 1) → ℕ) : Set (Fin (m + 1) × Fin (m + 1) →₀ ℕ) :=
  {e | e ∈ ssIdx (m + 1) (m + 1) ν ∧ (top = true → (vec = true → e (0, 0) = ν 0) ∧ (vec = false → ∀ t, e (0, t) = 0))}

def thAll (R : Type) [CommRing R] (n' m : ℕ) (vec : Fin n' → Bool) :
    MvPolynomial (Fin n' × Fin (m + 1)) R →ₐ[R] MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R :=
  aeval fun v => blockEmb R v.1 (Nv R m (vec v.1) v.2)

def IsMultiHom {R : Type} [CommRing R] {n' k : ℕ} (d : Fin n' → ℕ) (Q : MvPolynomial (Fin n' × Fin k) R) : Prop :=
  ∀ e ∈ Q.support, ∀ s, ∑ c : Fin k, e (s, c) = d s

def PosInd : Prop :=
  ∀ (F : Type) [Field F] (m : ℕ), 2 ≤ m → ∀ (top vec : Bool) (d : ℕ) (ν : Fin (m + 1) → ℕ),
    (top = false → d = 0) → (top = true → vec = false → ∀ t : Fin (m + 1), m ≤ t.val + 1 → ν t = 0) →
    ∀ b : Xs m top vec ν → MvPolynomial (Fin (m + 1) × Fin (m + 1)) F,
      (∀ x, (colLex (m + 1) (m + 1)).degree (b x) = x.1 ∧ (colLex (m + 1) (m + 1)).leadingCoeff (b x) = 1) →
      LinearIndependent F (fun y : {α : Fin (m + 1) →₀ ℕ // ∑ c, α c = d} × Xs m top vec ν =>
        (∏ c, Nv F m vec c ^ (y.1.1 c)) * b y.2)

def BigInd : Prop :=
  ∀ (F : Type) [Field F] (n' m : ℕ), 2 ≤ m → ∀ (top vec : Fin n' → Bool) (d : Fin n' → ℕ) (ν : Fin n' → Fin (m + 1) → ℕ),
    (∀ s, top s = false → d s = 0) →
    (∀ s, top s = true → vec s = false → ∀ t : Fin (m + 1), m ≤ t.val + 1 → ν s t = 0) →
    ∀ b : ∀ s, Xs m (top s) (vec s) (ν s) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) F,
      (∀ s x, (colLex (m + 1) (m + 1)).degree (b s x) = x.1 ∧ (colLex (m + 1) (m + 1)).leadingCoeff (b s x) = 1) →
      ∀ (J : Finset (∀ s, Xs m (top s) (vec s) (ν s)))
        (Q : (∀ s, Xs m (top s) (vec s) (ν s)) → MvPolynomial (Fin n' × Fin (m + 1)) F),
        (∀ i, IsMultiHom d (Q i)) →
        ∑ i ∈ J, thAll F n' m vec (Q i) * ∏ s, blockEmb F s (b s (i s)) = 0 → ∀ i ∈ J, Q i = 0

def CntTop : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (lo : Fin (m + 1) → ℤ), Antitone lo → lo 0 = lo 1 → ∀ vec : Bool,
    ((Nat.card (Xs m true vec (nuOf (if vec = true then lo else fun i => -lo i.rev))) : ℕ) : ℚ) =
      Formalism.CountingSumsFrames.weylDim m (fun i : Fin m => lo i.succ)

def CntSpec : Prop :=
  ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam → ∀ vec : Bool,
    ((Nat.card (Xs m false vec (nuOf lam)) : ℕ) : ℚ) = Formalism.CountingSumsFrames.weylDim (m + 1) lam

end Formalism.MainNotions.TestSideCounting

module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.LowestKTypeModels.Models
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.IntertwinerAdjoints.Imports
public import Development.WeilBound.CoreStatements.BranchingTraces.CasimirDecomposition.UnitaryDecompositionExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.Imports
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.StepM
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.FarClosed

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.FlipDecomposition.DecompositionExistenceHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlipUSymmCont
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.CompanionTheory.NegDS

variable {n : ℕ} {ε ε' : Fin n → Bool}

theorem sign_eq_iff (he : ∀ a, ε' a = !ε a) (a b : Fin n) : ε' a = ε' b ↔ ε a = ε b := by
  rw [he a, he b]
  cases ε a <;> cases ε b <;> simp

theorem Jm_flip (he : ∀ a, ε' a = !ε a) : Formalism.REAL.Jm ε' = -Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_neg]
  congr 1
  funext a
  rw [he a]
  cases ε a <;> simp

theorem UJset_flip (he : ∀ a, ε' a = !ε a) : Formalism.MainNotions.S.UJset ε' = Formalism.MainNotions.S.UJset ε := by
  ext g
  show Formalism.REAL.inUJ ε' g ↔ Formalism.REAL.inUJ ε g
  unfold Formalism.REAL.inUJ
  rw [Jm_flip he, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem Kset_flip (he : ∀ a, ε' a = !ε a) : Formalism.REAL.Kset ε' = Formalism.REAL.Kset ε := by
  ext g
  show g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε' = Formalism.REAL.Jm ε' * g ↔
    g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g
  rw [Jm_flip he, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem rhoC_flip (he : ∀ a, ε' a = !ε a) : Formalism.REAL.rhoC ε' = Formalism.REAL.rhoC ε := by
  funext a
  simp only [Formalism.REAL.rhoC, sign_eq_iff he]

theorem rhoN_flip (he : ∀ a, ε' a = !ε a) : Formalism.REAL.rhoN ε' = Formalism.REAL.rhoN ε := by
  funext a
  simp only [Formalism.REAL.rhoN, ne_eq, sign_eq_iff he]

theorem lowK_flip (he : ∀ a, ε' a = !ε a) (lam : Fin n → ℝ) : Formalism.QuantumDeterminants.lowK ε' lam = Formalism.QuantumDeterminants.lowK ε lam := by
  unfold Formalism.QuantumDeterminants.lowK
  rw [rhoC_flip he, rhoN_flip he]

theorem vNormSq_flip (he : ∀ a, ε' a = !ε a) (μ : Fin n → ℝ) : Formalism.MainNotions.S.vNormSq ε' μ = Formalism.MainNotions.S.vNormSq ε μ := by
  unfold Formalism.MainNotions.S.vNormSq
  rw [rhoC_flip he]

theorem cdom_flip (he : ∀ a, ε' a = !ε a) (μ Λ : Fin n → ℝ) : Formalism.MainNotions.S.CDom ε' μ Λ ↔ Formalism.MainNotions.S.CDom ε μ Λ := by
  simp only [Formalism.MainNotions.S.CDom, sign_eq_iff he]

section Rep

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem kstable_flip (he : ∀ a, ε' a = !ε a) (S : Submodule ℂ H) :
    Formalism.MainNotions.S.IsKStableOn ε' σ S ↔ Formalism.MainNotions.S.IsKStableOn ε σ S := by
  simp only [Formalism.MainNotions.S.IsKStableOn, Kset_flip he]

theorem ktype_flip (he : ∀ a, ε' a = !ε a) (Λ : Fin n → ℝ) (S : Submodule ℂ H) :
    Formalism.MainNotions.S.IsKTypeOf ε' σ Λ S ↔ Formalism.MainNotions.S.IsKTypeOf ε σ Λ S := by
  simp only [Formalism.MainNotions.S.IsKTypeOf, kstable_flip he, Kset_flip he, cdom_flip he]

end Rep

def flipU (he : ∀ a, ε' a = !ε a) : Formalism.REAL.UJ ε' ≃* Formalism.REAL.UJ ε where
  toFun g := ⟨g.1, (Set.ext_iff.1 (UJset_flip he) _).1 g.2⟩
  invFun g := ⟨g.1, (Set.ext_iff.1 (UJset_flip he) _).2 g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem flipU_cont (he : ∀ a, ε' a = !ε a) : Continuous (flipU he) := by
  exact continuous_induced_rng.2 continuous_subtype_val

theorem flipU_symm_cont (he : ∀ a, ε' a = !ε a) : Continuous (flipU he).symm := by
  exact continuous_induced_rng.2 continuous_subtype_val

theorem memLp_flip (he : ∀ a, ε' a = !ε a) {F : Formalism.REAL.UJ ε → ℂ} (hF : MemLp F 2 (Formalism.REAL.muG ε)) :
    MemLp (F ∘ flipU he) 2 (Formalism.REAL.muG ε') := by
  have hc := flipU_cont he
  have hcs := flipU_symm_cont he
  let eH : Formalism.REAL.UJ ε' ≃ₜ Formalism.REAL.UJ ε := ⟨(flipU he).toEquiv, hc, hcs⟩
  have hme : MeasurableEmbedding (flipU he) := eH.measurableEmbedding
  haveI : (Measure.map (flipU he) (Formalism.REAL.muG ε')).IsHaarMeasure :=
    (flipU he).isHaarMeasure_map (Formalism.REAL.muG ε') hc hcs
  have hmap : Measure.map (flipU he) (Formalism.REAL.muG ε') =
      MeasureTheory.Measure.haarScalarFactor (Measure.map (flipU he) (Formalism.REAL.muG ε')) (Formalism.REAL.muG ε) •
        Formalism.REAL.muG ε :=
    MeasureTheory.Measure.isMulLeftInvariant_eq_smul _ _
  rw [← hme.memLp_map_measure_iff, hmap, ENNReal.smul_def]
  exact hF.smul_measure ENNReal.coe_ne_top

theorem sqInt_flip {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (he : ∀ a, ε' a = !ε a) (h : Formalism.MainNotions.S.IsSqIntOn ε σ) : Formalism.MainNotions.S.IsSqIntOn ε' σ := by
  intro v w
  have e : Formalism.MainNotions.S.coefOn (ε := ε') σ v w = Formalism.MainNotions.S.coefOn (ε := ε) σ v w ∘ flipU he := by
    funext g
    rfl
  rw [e]
  exact memLp_flip he (h v w)

theorem isDS_flip : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS (fun a => !ε a) lam σ := by
  intro n H _ _ ε lam σ h
  have he : ∀ a, (fun a => !ε a) a = !ε a := fun _ => rfl
  unfold Formalism.MainNotions.S.IsDS at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, ?_, ?_, sqInt_flip he h5, ?_, ?_⟩
  · rw [UJset_flip he]
    exact h3
  · rw [UJset_flip he]
    exact h4
  · obtain ⟨S, hS⟩ := h6
    exact ⟨S, by rw [lowK_flip he, ktype_flip he]; exact hS⟩
  · intro μ S hS
    rw [lowK_flip he, vNormSq_flip he, vNormSq_flip he]
    exact h7 μ S ((ktype_flip he μ S).1 hS)

end GlobalTheory.CompanionTheory.NegDS

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.FlipDecomposition.FlipDecAlt
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe.Dec

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition

def Facts {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (X : Dec ε lam π) : Prop :=
  (∀ s, s ∈ X.S ↔ Formalism.QuantumDeterminants.IsHCParam (lam - Pi.single s 1)) ∧ ∀ s, X.κ s = (lam s : ℂ) + ((m : ℂ) - 1) / 2

def DecLe : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (lam : Fin m → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)), (∃ a, ε a = false) →
    (univ.filter fun a => ε a = false).card ≤ (univ.filter fun a => ε a = true).card →
    Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam π → Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * (m : ℝ) ^ 3) →
    ∃ X : Dec ε lam π, Facts X

def FlipDS : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (lam : Fin m → ℝ) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (σ : Matrix (Fin m) (Fin m) ℂ → (K →L[ℂ] K)), IsDS (fun a => !ε a) lam σ ↔ IsDS ε lam σ

def FlipDec : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (lam : Fin m → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)) (X : Dec (fun a => !ε a) lam π), Facts X → ∃ Y : Dec ε lam π, Facts Y

end PositivityTheory.RgHe.Dec
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.FlipDecomposition.DecompositionUnitaryShift
open Matrix Finset
open scoped InnerProductSpace Classical

noncomputable section

namespace PositivityTheory.RgHe.Dec.DL

open CompanionTheory.Zuck PositivityTheory.UnitaryDecomposition.DecA PositivityTheory.UnitaryDecomposition.DecB PositivityTheory.UnitaryDecomposition BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
open PI.UpqRep (IsHCParam IsCayleyU)
open Formalism.REAL (Jm UJ)

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem decomposition_unitary_shift (hk : 1 ≤ k) (lam : Fin (2 * r + k + 1) → ℝ) (U : URep k r) (π : Mx k r → (U.R.H →L[ℂ] U.R.H)) {P : Mx k r}
    (hP : IsCayleyU k r ε P) (hπe : (fun g => U.R.σ (P⁻¹ * g * P)) = π) (hU : U.R.IsDS ε lam)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) :
    ∃ X : Dec ε lam π, X.S = univ.filter (fun s => IsHCParam (shift true lam s)) ∧
      ∀ s, X.κ s = (lam s : ℂ) + (((2 * r + k + 1 : ℕ) : ℂ) - 1) / 2 := by
  have S := zuckerman_ingredients
  have hl : IsHCParam lam := hU.1
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have hn1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hth : thr _ ε + (((2 * r + k + 1) ^ 2 + 2 : ℕ) : ℝ) + 1 < 200 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := by
    have h1 := thr_le (n := 2 * r + k + 1) (by omega) ε
    have h2 : ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
    have h3 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ hn1
    rw [Nat.cast_add, Nat.cast_pow]
    push_cast at h1 h2 h3 ⊢
    linarith
  obtain ⟨T0, hT0, -, -⟩ := injV S zuckerman_library_bounds true hU hg (by linarith)
  let T : Fin (2 * r + k + 1) → URep k r := fun s => if h : IsHCParam (shift true lam s) then T0 ⟨s, h⟩ else U
  have hT : ∀ s : {s // IsHCParam (shift true lam s)}, (T s.1).R.IsDS ε (shift true lam s.1) := fun s => by
    simp only [T, dif_pos s.2]; exact hT0 s
  obtain ⟨io, pr, hD⟩ := decReg S zuckerman_library_bounds hk true hU hg hth (fun s => T s.1) hT
  have hsimp := S.schur S.infChar k r ε _ _ (fun s : {s // IsHCParam (shift true lam s)} => T s.1)
    ((shift_inj true lam).comp Subtype.val_injective) hT
  have hQ : ∀ s, ∃ Q : Mx k r, IsCayleyU k r ε Q ∧ (IsHCParam (shift true lam s) →
      PI.UpqRep.IsDS ε (shift true lam s) fun g => (T s).R.σ (Q⁻¹ * g * Q)) := fun s => by
    by_cases h : IsHCParam (shift true lam s)
    · obtain ⟨Q, h1, h2⟩ := (hT ⟨s, h⟩).2
      exact ⟨Q, h1, fun _ => h2⟩
    · exact ⟨P, hP, fun h' => absurd h' h⟩
  choose Q hQ1 hQ2 using hQ
  have sm_iff : ∀ v : U.R.H, v ∈ PI.PhMeasCore.smoothVecs (Jm ε) π ↔ v ∈ U.R.sm := fun v => by
    refine ⟨fun hv => ?_, fun hv => ?_⟩
    · have h1 := GlobalTheory.CayleyTransport.smoothOn_comp (H := Jm ε) (J := PI.UpqRep.Hpk k r) (A := P) (B := P⁻¹)
        (f := fun g => π g v) (fun g hg' => cay_mem' hP hg') hv
      have h2 : (fun g => π (P * g * P⁻¹) v) = fun g => U.R.σ g v := funext fun g => by
        rw [← hπe]
        show U.R.σ (P⁻¹ * (P * g * P⁻¹) * P) v = _
        rw [Matrix.mul_assoc P, Matrix.nonsing_inv_mul_cancel_left _ _ hPu, Matrix.nonsing_inv_mul_cancel_right _ _ hPu]
      rw [h2] at h1
      exact h1
    · have := (GlobalTheory.CayleyTransport.smooth_and_dsigC_transport k r ε U.R P hP).1 v hv
      rwa [hπe] at this
  let up : (Fin (2 * r + k + 1) → U.R.H) → M (vr k r true, U) := fun x =>
    if h : x ∈ SmT ε π then fun c => ∑ d, P d c • (⟨x d, (sm_iff _).1 (h d)⟩ : U.R.smSub) else 0
  have up_coe : ∀ x ∈ SmT ε π, ∀ c, (up x c : U.R.H) = ∑ d, P d c • x d := fun x hx c => by
    simp only [up, dif_pos hx]; simp
  have dn_up : ∀ x ∈ SmT ε π, dn U P (up x) = x := fun x hx => funext fun c => by
    show ∑ d, P⁻¹ d c • (up x d : U.R.H) = x c
    simp only [up_coe x hx]
    rw [DecB.sum_comp, Matrix.mul_nonsing_inv _ hPu, DecB.sum_one]
  have dn_sm : ∀ z, dn U P z ∈ SmT ε π := fun z c =>
    (sm_iff _).2 (show ∑ d, P⁻¹ d c • (z d : U.R.H) ∈ U.R.smSub from
      U.R.smSub.sum_mem fun d _ => U.R.smSub.smul_mem _ (z d).2)
  have up_dn : ∀ z, up (dn U P z) = z := fun z => funext fun c => Subtype.ext (by
    rw [up_coe _ (dn_sm z)]
    show ∑ d, P d c • ∑ e, P⁻¹ e d • (z e : U.R.H) = _
    rw [DecB.sum_comp, Matrix.nonsing_inv_mul _ hPu, DecB.sum_one])
  have mem : ∀ g : UJ ε, P⁻¹ * um g * P ∈ GG k r := fun g => cay_mem hP g.2
  have dn_act : ∀ (g : UJ ε) z, dn U P (CompanionTheory.Zuck.act (vr k r true, U) (P⁻¹ * um g * P) z) = actT π (um g) (dn U P z) := fun g z => by
    funext c
    show ∑ d, P⁻¹ d c • (CompanionTheory.Zuck.act (vr k r true, U) (P⁻¹ * um g * P) z d : U.R.H) = ∑ d, (um g)⁻¹ d c • π (um g) (∑ e, P⁻¹ e d • (z e : U.R.H))
    have e0 : U.R.σ (P⁻¹ * um g * P) = π (um g) := congrFun hπe _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [act_coe U (mem g), map_sum, map_smul, e0]
    rw [DecB.sum_comp, DecB.sum_comp, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hPu, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_right _ _ hPu]
  have up_act : ∀ (g : UJ ε), ∀ x ∈ SmT ε π, up (actT π (um g) x) = CompanionTheory.Zuck.act (vr k r true, U) (P⁻¹ * um g * P) (up x) :=
    fun g x hx => by rw [← up_dn (CompanionTheory.Zuck.act _ _ _), dn_act, dn_up x hx]
  have hform := fun s s' => invForm (U := U) hP (io s) (io s') (hD.io_hom s) (hD.io_hom s')
  choose cI hc using fun s => (CompanionTheory.D.gk.Poul.poulsen_smooth_vectors_dense k r ε _ _ _ _ (hT s) (hT s)).1 _ (hform s s)
  have horth : ∀ s s', s ≠ s' → ∀ a b, formT ε (dn U P (io s' b)) (dn U P (io s a)) = 0 := fun s s' hs a b => by
    rcases (CompanionTheory.D.gk.Poul.poulsen_smooth_vectors_dense k r ε _ _ _ _ (hT s) (hT s')).2 _ (hform s s') with h | h
    · have := h _ (a ()).2 _ (b ()).2
      simpa only [extension_one_coe] using this
    · obtain ⟨f, g, hf, -, hgf, -⟩ := S.uIso k r (triv k r) _ _ h
      have h0 := hsimp.2.2 s s' hs f hf
      obtain ⟨y, y', hy⟩ := hsimp.1 s
      have h1 : ∀ z, z = (g ∘ₗ f) z := fun z => by rw [hgf]; rfl
      exact absurd ((h1 y).trans (by rw [h1 y', h0]; simp)) hy
  have bmem : ∀ s, (Q s)⁻¹ * P ∈ GG k r := fun s => cay_two hP (hQ1 s)
  have sumS : ∀ f : {s // IsHCParam (shift true lam s)} → Fin (2 * r + k + 1) → U.R.H,
      ∑ s ∈ univ.filter (fun s => IsHCParam (shift true lam s)), (if h : IsHCParam (shift true lam s) then f ⟨s, h⟩ else 0) =
        ∑ s, f s := fun f => by
    rw [Finset.sum_subtype (p := fun s => IsHCParam (shift true lam s)) _ (by simp)]
    exact Finset.sum_congr rfl fun s _ => dif_pos s.2
  have hsum : ∀ z, ∑ s, io s (pr s z) = z := fun z => by
    have := LinearMap.congr_fun hD.sum z
    simpa [LinearMap.sum_apply] using this
  refine ⟨{ S := univ.filter fun s => IsHCParam (shift true lam s)
            Hs := fun s => (T s).R.H
            πs := fun s g => (T s).R.σ ((Q s)⁻¹ * g * Q s)
            ds := fun s hs => ⟨(mem_filter.1 hs).2, hQ2 s (mem_filter.1 hs).2⟩
            p := fun s x => if h : IsHCParam (shift true lam s) then dn U P (io ⟨s, h⟩ (pr ⟨s, h⟩ (up x))) else 0
            pr := fun s x => if h : IsHCParam (shift true lam s) then (T s).R.σ ((Q s)⁻¹ * P) (pr ⟨s, h⟩ (up x) ()) else 0
            c := fun s => if h : IsHCParam (shift true lam s) then cI ⟨s, h⟩ else 0
            κ := fun s => (lam s : ℂ) + (((2 * r + k + 1 : ℕ) : ℂ) - 1) / 2
            p_sm := fun s hs x _ => by rw [dif_pos (mem_filter.1 hs).2]; exact dn_sm _
            sum := fun x hx => by rw [sumS fun s => dn U P (io s (pr s (up x))), ← map_sum, hsum, dn_up x hx]
            p_act := fun s hs g x hx => ?_
            pr_act := fun s hs g x hx => ?_
            form := fun s hs x hx y hy => ?_
            cas := fun s hs x hx => ?_
            κ_inj := fun s _ s' _ h => hl.1.injective (by exact_mod_cast add_right_cancel h) }, rfl, fun _ => rfl⟩
  · have h := (mem_filter.1 hs).2
    simp only [dif_pos h]
    rw [up_act g x hx, ← dn_act]
    congr 1
    exact LinearMap.congr_fun (((S.homCat k r).comp _ _ _ _ _ (hD.pr_hom ⟨s, h⟩) (hD.io_hom ⟨s, h⟩)).equiv _ (mem g)) (up x)
  · have h := (mem_filter.1 hs).2
    have hQu : IsUnit (Q s).det := (Matrix.isUnit_iff_isUnit_det _).1 (hQ1 s).1.1
    simp only [dif_pos h]
    have e := LinearMap.congr_fun ((hD.pr_hom ⟨s, h⟩).equiv _ (mem g)) (up x)
    simp only [LinearMap.comp_apply] at e
    rw [up_act g x hx, e, act_one_coe _ (mem g), ← (T s).repOn.apply_mul (bmem s) (mem g),
      ← (T s).repOn.apply_mul (cay_mem (hQ1 s) g.2) (bmem s)]
    congr 2
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hPu, Matrix.mul_nonsing_inv_cancel_left _ _ hQu]
  · have h := (mem_filter.1 hs).2
    simp only [dif_pos h]
    have e := (LinearMap.norm_map_iff_inner_map_map ((T s).R.σ ((Q s)⁻¹ * P) : (T s).R.H →ₗ[ℂ] (T s).R.H)).1
      ((T s).rep.2.1 _ (bmem s)) (pr ⟨s, h⟩ (up y) ()) (pr ⟨s, h⟩ (up x) ())
    simp only [ContinuousLinearMap.coe_coe] at e
    rw [e, ← hc ⟨s, h⟩ _ (pr ⟨s, h⟩ (up x) ()).2 _ (pr ⟨s, h⟩ (up y) ()).2]
    simp only [extension_one_coe]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← dn_up y hy, ← hsum (up y), map_sum]
    have e2 : ∀ (f : {s // IsHCParam (shift true lam s)} → Fin (2 * r + k + 1) → U.R.H) z,
        formT ε (∑ s', f s') z = ∑ s', formT ε (f s') z := fun f z => by
      simp only [formT, Finset.sum_apply, sum_inner, Finset.mul_sum]
      exact Finset.sum_comm
    rw [e2, Finset.sum_eq_single ⟨s, h⟩ (fun s' _ hs' => horth _ _ (Ne.symm hs') _ _) (by simp)]
  · have h := (mem_filter.1 hs).2
    simp only [dif_pos h]
    have e := cas_dn hU hP (io ⟨s, h⟩ (pr ⟨s, h⟩ (up x)))
    rw [show (fun g => U.R.σ (P⁻¹ * g * P)) = π from hπe] at e
    rw [e, kOp_io hk hU s (hT ⟨s, h⟩) _ (hD.io_hom ⟨s, h⟩), map_smul]

theorem decomposition_cayley_shift (hk : 1 ≤ k) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Mx k r → (H →L[ℂ] H)) {P : Mx k r} (hP : IsCayleyU k r ε P) (hl : IsHCParam lam) (hπ : Formalism.MainNotions.S.IsDS ε lam π)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) :
    ∃ X : Dec ε lam π, X.S = univ.filter (fun s => IsHCParam (shift true lam s)) ∧
      ∀ s, X.κ s = (lam s : ℂ) + (((2 * r + k + 1 : ℕ) : ℂ) - 1) / 2 := by
  haveI : CompleteSpace H := hπ.1
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  let R : Rep k r := { H := H, σ := fun g => π (P * g * P⁻¹) }
  have hπe : (fun g => R.σ (P⁻¹ * g * P)) = π := funext fun g => by
    show π (P * (P⁻¹ * g * P) * P⁻¹) = π g
    rw [Matrix.mul_assoc P⁻¹, Matrix.mul_nonsing_inv_cancel_left _ _ hPu, Matrix.mul_nonsing_inv_cancel_right _ _ hPu]
  have hR : R.IsDS ε lam := ⟨hl, P, hP, by rw [hπe]; exact hπ⟩
  exact decomposition_unitary_shift hk lam (mkU R hR) π hP hπe hR hg

end PositivityTheory.RgHe.Dec.DL

namespace PositivityTheory.RgHe.Dec

open Finset

theorem decomposition_le_holds : DecLe := by
  intro m ε lam H _ _ π ⟨a, ha⟩ hle hl hπ hg
  have h1 : 1 ≤ (univ.filter fun a => ε a = false).card := Finset.card_pos.2 ⟨a, by simp [ha]⟩
  have h2 : (univ.filter fun a => ε a = true).card + (univ.filter fun a => ε a = false).card = m := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) fun a => ε a = true
    simpa using this
  obtain ⟨r, hr⟩ : ∃ r, (univ.filter fun a => ε a = false).card = r + 1 := ⟨_, (Nat.sub_add_cancel h1).symm⟩
  obtain ⟨k, hk⟩ : ∃ k, (univ.filter fun a => ε a = true).card = k + r := ⟨_, (Nat.sub_add_cancel (by omega)).symm⟩
  obtain rfl : m = 2 * r + k + 1 := by omega
  obtain ⟨P, hP⟩ := Formalism.MainNotions.S.Inh.obj_cayleyU_of_card k r ε hk
  obtain ⟨X, hS, hκ⟩ := DL.decomposition_cayley_shift (by omega) lam H π (P := P) hP hl hπ hg
  refine ⟨X, fun s => ?_, fun s => ?_⟩
  · rw [hS, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, CompanionTheory.Zuck.shift, if_true]
    exact Iff.rfl
  · rw [hκ]

end PositivityTheory.RgHe.Dec
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.FlipDecomposition.FlipDec
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe.Dec

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition

section Flip

variable {m : ℕ}

theorem flip_he (ε : Fin m → Bool) : ∀ a, (fun a => !ε a) a = !ε a := fun _ => rfl

theorem smoothOnH_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (J : Matrix (Fin m) (Fin m) ℂ)
    (f : Matrix (Fin m) (Fin m) ℂ → E) : PI.PhMeasCore.SmoothOnH (-J) f ↔ PI.PhMeasCore.SmoothOnH J f := by
  have key : ∀ g : Matrix (Fin m) (Fin m) ℂ, gᴴ * -J * g = -J ↔ gᴴ * J * g = J := by
    intro g
    rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj]
  unfold PI.PhMeasCore.SmoothOnH PI.PhMeasCore.UH
  simp only [Set.mem_setOf_eq, key]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem mem_smoothVecs_flip (ε : Fin m → Bool) (π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)) (v : H) :
    v ∈ PI.PhMeasCore.smoothVecs (Jm (fun a => !ε a)) π ↔ v ∈ PI.PhMeasCore.smoothVecs (Jm ε) π := by
  simp only [PI.PhMeasCore.smoothVecs, Set.mem_setOf_eq]
  rw [GlobalTheory.CompanionTheory.NegDS.Jm_flip (ε := ε) (ε' := fun a => !ε a) (fun a => rfl)]
  exact smoothOnH_neg _ _

theorem mem_SmT_flip (ε : Fin m → Bool) (π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)) (x : Fin m → H) :
    x ∈ SmT (fun a => !ε a) π ↔ x ∈ SmT ε π := by
  simp only [SmT, Set.mem_setOf_eq, mem_smoothVecs_flip]

theorem thetaJ_flip (ε : Fin m → Bool) (Y : Matrix (Fin m) (Fin m) ℂ) :
    PI.DSInfCharCap.thetaJ (fun a => !ε a) Y = PI.DSInfCharCap.thetaJ ε Y := by
  unfold PI.DSInfCharCap.thetaJ
  rw [GlobalTheory.CompanionTheory.NegDS.Jm_flip (ε := ε) (ε' := fun a => !ε a) (fun a => rfl)]
  simp [Matrix.mul_neg, Matrix.neg_mul]

theorem dsigC_flip (ε : Fin m → Bool) (σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)) (Y : Matrix (Fin m) (Fin m) ℂ) (v : H) :
    PI.DSInfCharCap.dsigC (fun a => !ε a) σ Y v = PI.DSInfCharCap.dsigC ε σ Y v := by
  simp only [PI.DSInfCharCap.dsigC, thetaJ_flip]

theorem casT_flip (ε : Fin m → Bool) (π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)) (x : Fin m → H) :
    casT (fun a => !ε a) π x = casT ε π x := by
  funext c
  simp only [casT, dsigC_flip]

theorem formT_flip (ε : Fin m → Bool) (y x : Fin m → H) : formT (fun a => !ε a) y x = -formT ε y x := by
  unfold formT
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro l _
  by_cases h : ε l = true <;> simp [h]

theorem isDS_of_flip {ε : Fin m → Bool} {lam : Fin m → ℝ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {σ : Matrix (Fin m) (Fin m) ℂ → (K →L[ℂ] K)} (h : IsDS (fun a => !ε a) lam σ) : IsDS ε lam σ := by
  have h2 := GlobalTheory.CompanionTheory.NegDS.isDS_flip m K (fun a => !ε a) lam σ h
  simp only [Bool.not_not] at h2
  exact h2

end Flip

theorem flip_decomposition_holds : FlipDec := by
  intro m ε lam H _ _ π X hF
  let Y : Dec ε lam π :=
    { S := X.S
      Hs := X.Hs
      nH := X.nH
      iH := X.iH
      cH := X.cH
      πs := X.πs
      ds := fun s hs => ⟨(X.ds s hs).1, isDS_of_flip (X.ds s hs).2⟩
      p := X.p
      pr := X.pr
      c := fun s => -X.c s
      κ := X.κ
      p_sm := fun s hs x hx => (mem_SmT_flip ε π _).1 (X.p_sm s hs x ((mem_SmT_flip ε π x).2 hx))
      sum := fun x hx => X.sum x ((mem_SmT_flip ε π x).2 hx)
      p_act := fun s hs g x hx =>
        X.p_act s hs ((GlobalTheory.CompanionTheory.NegDS.flipU (flip_he ε)).symm g) x ((mem_SmT_flip ε π x).2 hx)
      pr_act := fun s hs g x hx =>
        X.pr_act s hs ((GlobalTheory.CompanionTheory.NegDS.flipU (flip_he ε)).symm g) x ((mem_SmT_flip ε π x).2 hx)
      form := fun s hs x hx y hy => by
        have h := X.form s hs x ((mem_SmT_flip ε π x).2 hx) y ((mem_SmT_flip ε π y).2 hy)
        rw [formT_flip] at h
        rw [neg_mul, ← h, neg_neg]
      cas := fun s hs x hx => by
        have h := X.cas s hs x ((mem_SmT_flip ε π x).2 hx)
        rwa [casT_flip] at h
      κ_inj := X.κ_inj }
  exact ⟨Y, hF⟩

end PositivityTheory.RgHe.Dec
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.FlipDecomposition.OccurrenceOfWalk
noncomputable section

open Finset

namespace PositivityTheory.RgHe.Dec

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition

variable {n : ℕ}

def shL (lam : Fin (n + 1) → ℝ) (b : Fin (n + 1) ⊕ Fin n → ℕ) : Fin (n + 1) → ℝ := lam + fun i => (b (Sum.inl i) : ℝ)

def shM (mu : Fin n → ℝ) (b : Fin (n + 1) ⊕ Fin n → ℕ) : Fin n → ℝ := mu + fun j => (b (Sum.inr j) : ℝ)

theorem abs_le_shift {x y : ℝ} {p q : ℕ} (h1 : x ≤ y → p ≤ q) (h2 : y ≤ x → q ≤ p) :
    |x - y| ≤ |(x + p) - (y + q)| := by
  rcases le_total x y with h | h
  · have := h1 h
    have h' : (p : ℝ) ≤ q := by exact_mod_cast this
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have := h2 h
    have h' : (q : ℝ) ≤ p := by exact_mod_cast this
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

theorem hc_shift {m : ℕ} {lam : Fin m → ℝ} (hl : Formalism.QuantumDeterminants.IsHCParam lam) (c : Fin m → ℕ)
    (hc : ∀ i j, lam i ≤ lam j → c i ≤ c j) : Formalism.QuantumDeterminants.IsHCParam (lam + fun i => (c i : ℝ)) := by
  refine ⟨fun i j hij => ?_, fun a => ?_⟩
  · have h1 := hl.1 hij
    have h2 : (c j : ℝ) ≤ c i := by exact_mod_cast hc j i h1.le
    simp only [Pi.add_apply]
    linarith
  · obtain ⟨z, hz⟩ := hl.2 a
    exact ⟨z + c a, by simp only [Pi.add_apply]; push_cast; linarith⟩

theorem gap_shift {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {h : ℝ} (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (c : Fin m → ℕ)
    (hc : ∀ i j, lam i ≤ lam j → c i ≤ c j) : Formalism.QuantumDeterminants.GapAtLeast ε (lam + fun i => (c i : ℝ)) h := by
  intro a b hab
  refine (hg a b hab).trans ?_
  simp only [Pi.add_apply]
  exact abs_le_shift (hc a b) (hc b a)

def Mono (lam : Fin (n + 1) → ℝ) (mu : Fin n → ℝ) (b : Fin (n + 1) ⊕ Fin n → ℕ) : Prop :=
  ∀ x y, Sum.elim lam mu x ≤ Sum.elim lam mu y → b x ≤ b y

theorem gp_shift {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ}
    {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (hG : Gp ε lam ε' mu e) {b : Fin (n + 1) ⊕ Fin n → ℕ} (hb : Mono lam mu b) :
    Gp ε (shL lam b) ε' (shM mu b) e :=
  ⟨hG.fits, hG.two, hG.neg, hG.le, hc_shift hG.hc _ fun i j h => hb (Sum.inl i) (Sum.inl j) h,
    hc_shift hG.hc' _ fun i j h => hb (Sum.inr i) (Sum.inr j) h,
    gap_shift hG.gap _ fun i j h => hb (Sum.inl i) (Sum.inl j) h,
    gap_shift hG.gap' _ fun i j h => hb (Sum.inr i) (Sum.inr j) h⟩

theorem half {lam : Fin (n + 1) → ℝ} {mu : Fin n → ℝ} (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hm : Formalism.QuantumDeterminants.IsHCParam mu)
    (i : Fin (n + 1)) (j : Fin n) : ∃ z : ℤ, lam i - mu j = z + 1 / 2 := by
  obtain ⟨a, ha⟩ := hl.2 i
  obtain ⟨b, hb⟩ := hm.2 j
  refine ⟨a - b, ?_⟩
  push_cast at ha hb ⊢
  linarith

theorem half_ne {x : ℝ} (h : ∃ z : ℤ, x = z + 1 / 2) : x ≠ 0 := by
  obtain ⟨z, rfl⟩ := h
  intro h0
  have h1 : ((2 * z + 1 : ℤ) : ℝ) = 0 := by
    push_cast
    linarith
  have h2 : (2 * z + 1 : ℤ) = 0 := by exact_mod_cast h1
  omega

theorem half_ge {x : ℝ} (h : ∃ z : ℤ, x = z + 1 / 2) (hx : 0 < x) : 1 / 2 ≤ x := by
  obtain ⟨z, rfl⟩ := h
  have h1 : ((-1 : ℤ) : ℝ) < z := by
    push_cast
    linarith
  have hz : (-1 : ℤ) < z := by exact_mod_cast h1
  have hz0 : (0 : ℤ) ≤ z := by omega
  have h2 : (0 : ℝ) ≤ z := by exact_mod_cast hz0
  linarith

theorem inj_merge {lam : Fin (n + 1) → ℝ} {mu : Fin n → ℝ} (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hm : Formalism.QuantumDeterminants.IsHCParam mu) :
    Function.Injective (Sum.elim lam mu) := by
  intro x y hxy
  rcases x with i | j <;> rcases y with i' | j'
  · simp only [Sum.elim_inl] at hxy
    rw [hl.1.injective hxy]
  · simp only [Sum.elim_inl, Sum.elim_inr] at hxy
    exact absurd (sub_eq_zero.2 hxy) (half_ne (half hl hm i j'))
  · simp only [Sum.elim_inl, Sum.elim_inr] at hxy
    exact absurd (sub_eq_zero.2 hxy.symm) (half_ne (half hl hm i' j))
  · simp only [Sum.elim_inr] at hxy
    rw [hm.1.injective hxy]

section Step

variable {lam : Fin (n + 1) → ℝ} {mu : Fin n → ℝ} (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hm : Formalism.QuantumDeterminants.IsHCParam mu)
  {b : Fin (n + 1) ⊕ Fin n → ℕ} (hb : Mono lam mu b) {x : Fin (n + 1) ⊕ Fin n} (hx : 0 < b x)
  (hmin : ∀ y, 0 < b y → Sum.elim lam mu x ≤ Sum.elim lam mu y)
include hl hm hb hx hmin

theorem mono_down : Mono lam mu (Function.update b x (b x - 1)) := by
  intro y z hyz
  by_cases hy : y = x <;> by_cases hz : z = x
  · rw [hy, hz]
  · rw [hy, Function.update_self, Function.update_of_ne hz]
    have h := hb y z hyz
    rw [hy] at h
    omega
  · rw [hz, Function.update_of_ne hy, Function.update_self]
    rcases Nat.eq_zero_or_pos (b y) with h0 | hpos
    · omega
    · exfalso
      apply hy
      apply inj_merge hl hm
      rw [hz] at hyz
      exact le_antisymm hyz (hmin y hpos)
  · rw [Function.update_of_ne hy, Function.update_of_ne hz]
    exact hb y z hyz

theorem cond_down_l (s : Fin (n + 1)) (hs : x = Sum.inl s) (j : Fin n) : shL lam b s - 1 / 2 ≠ shM mu b j := by
  subst hs
  intro heq
  simp only [shL, shM, Pi.add_apply] at heq
  have hh := half hl hm s j
  rcases lt_trichotomy (mu j) (lam s) with hlt | heq' | hgt
  · have h1 := hb (Sum.inr j) (Sum.inl s) hlt.le
    have hge := half_ge hh (by linarith)
    have hc1 : (b (Sum.inr j) : ℝ) ≤ b (Sum.inl s) := by exact_mod_cast h1
    have hbeq : b (Sum.inr j) = b (Sum.inl s) := by
      have h2 : (b (Sum.inr j) : ℝ) = b (Sum.inl s) := by linarith
      exact_mod_cast h2
    have hpos : 0 < b (Sum.inr j) := by
      rw [hbeq]
      exact hx
    have h3 := hmin (Sum.inr j) hpos
    simp only [Sum.elim_inl, Sum.elim_inr] at h3
    linarith
  · exact half_ne hh (by linarith)
  · have h1 := hb (Sum.inl s) (Sum.inr j) hgt.le
    have hc1 : (b (Sum.inl s) : ℝ) ≤ b (Sum.inr j) := by exact_mod_cast h1
    linarith

theorem cond_down_m (j : Fin n) (hs : x = Sum.inr j) (s : Fin (n + 1)) : shM mu b j - 1 / 2 ≠ shL lam b s := by
  subst hs
  intro heq
  simp only [shL, shM, Pi.add_apply] at heq
  have hh : ∃ z : ℤ, mu j - lam s = z + 1 / 2 := by
    obtain ⟨z, hz⟩ := half hl hm s j
    exact ⟨-z - 1, by push_cast; linarith⟩
  rcases lt_trichotomy (lam s) (mu j) with hlt | heq' | hgt
  · have h1 := hb (Sum.inl s) (Sum.inr j) hlt.le
    have hge := half_ge hh (by linarith)
    have hc1 : (b (Sum.inl s) : ℝ) ≤ b (Sum.inr j) := by exact_mod_cast h1
    have hbeq : b (Sum.inl s) = b (Sum.inr j) := by
      have h2 : (b (Sum.inl s) : ℝ) = b (Sum.inr j) := by linarith
      exact_mod_cast h2
    have hpos : 0 < b (Sum.inl s) := by
      rw [hbeq]
      exact hx
    have h3 := hmin (Sum.inl s) hpos
    simp only [Sum.elim_inl, Sum.elim_inr] at h3
    linarith
  · exact half_ne hh (by linarith)
  · have h1 := hb (Sum.inr j) (Sum.inl s) hgt.le
    have hc1 : (b (Sum.inr j) : ℝ) ≤ b (Sum.inl s) := by exact_mod_cast h1
    linarith

end Step

theorem shL_down (lam : Fin (n + 1) → ℝ) (b : Fin (n + 1) ⊕ Fin n → ℕ) (s : Fin (n + 1)) (hx : 0 < b (Sum.inl s)) :
    shL lam (Function.update b (Sum.inl s) (b (Sum.inl s) - 1)) = shL lam b - Pi.single s 1 := by
  funext i
  simp only [shL, Pi.add_apply, Pi.sub_apply]
  by_cases h : i = s
  · subst h
    rw [Function.update_self, Pi.single_eq_same, Nat.cast_sub (by omega : 1 ≤ b (Sum.inl i))]
    push_cast
    ring
  · rw [Function.update_of_ne (fun h' => h (Sum.inl_injective h')), Pi.single_eq_of_ne h]
    ring

theorem shM_down_l (mu : Fin n → ℝ) (b : Fin (n + 1) ⊕ Fin n → ℕ) (s : Fin (n + 1)) :
    shM mu (Function.update b (Sum.inl s) (b (Sum.inl s) - 1)) = shM mu b := by
  funext j
  simp only [shM, Pi.add_apply]
  rw [Function.update_of_ne Sum.inr_ne_inl]

theorem shM_down (mu : Fin n → ℝ) (b : Fin (n + 1) ⊕ Fin n → ℕ) (j : Fin n) (hx : 0 < b (Sum.inr j)) :
    shM mu (Function.update b (Sum.inr j) (b (Sum.inr j) - 1)) = shM mu b - Pi.single j 1 := by
  funext i
  simp only [shM, Pi.add_apply, Pi.sub_apply]
  by_cases h : i = j
  · subst h
    rw [Function.update_self, Pi.single_eq_same, Nat.cast_sub (by omega : 1 ≤ b (Sum.inr i))]
    push_cast
    ring
  · rw [Function.update_of_ne (fun h' => h (Sum.inr_injective h')), Pi.single_eq_of_ne h]
    ring

theorem shL_down_m (lam : Fin (n + 1) → ℝ) (b : Fin (n + 1) ⊕ Fin n → ℕ) (j : Fin n) :
    shL lam (Function.update b (Sum.inr j) (b (Sum.inr j) - 1)) = shL lam b := by
  funext i
  simp only [shL, Pi.add_apply]
  rw [Function.update_of_ne Sum.inl_ne_inr]

theorem sum_down (b : Fin (n + 1) ⊕ Fin n → ℕ) (x : Fin (n + 1) ⊕ Fin n) (hx : 0 < b x) :
    ∑ y, Function.update b x (b x - 1) y + 1 = ∑ y, b y := by
  rw [Finset.sum_update_of_mem (mem_univ x), ← Finset.add_sum_erase _ _ (mem_univ x)]
  rw [show (univ \ {x} : Finset _) = univ.erase x from (Finset.erase_eq _ _).symm]
  omega

theorem down (hL : StepL) (hM : StepM) {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool}
    {mu : Fin n → ℝ} {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (hG : Gp ε lam ε' mu e) :
    ∀ (k : ℕ) (b : Fin (n + 1) ⊕ Fin n → ℕ), ∑ y, b y = k → Mono lam mu b →
      OccAt ε (shL lam b) ε' (shM mu b) e → OccAt ε lam ε' mu e := by
  intro k
  induction k with
  | zero =>
    intro b hs _ ho
    have h0 : ∀ y, b y = 0 := fun y => (Finset.sum_eq_zero_iff.1 hs) y (mem_univ y)
    have e1 : shL lam b = lam := by funext i; simp [shL, h0]
    have e2 : shM mu b = mu := by funext i; simp [shM, h0]
    rwa [e1, e2] at ho
  | succ k ih =>
    intro b hs hb ho
    have hne : (univ.filter fun y => 0 < b y).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
      have : ∑ y, b y = 0 := Finset.sum_eq_zero fun y _ => by have := h (mem_univ y); omega
      omega
    obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image _ (Sum.elim lam mu) hne
    have hx' : 0 < b x := (mem_filter.1 hx).2
    have hmin' : ∀ y, 0 < b y → Sum.elim lam mu x ≤ Sum.elim lam mu y := fun y hy => hmin y (mem_filter.2 ⟨mem_univ y, hy⟩)
    have hb' := mono_down hG.hc hG.hc' hb hx' hmin'
    have hs' : ∑ y, Function.update b x (b x - 1) y = k := by have := sum_down b x hx'; omega
    refine ih _ hs' hb' ?_
    have hGb := gp_shift hG hb
    have hGb' := gp_shift hG hb'
    rcases x with s | j
    · rw [shL_down lam b s hx', shM_down_l] at hGb' ⊢
      exact hL n ε _ ε' _ e hGb s hGb' (cond_down_l hG.hc hG.hc' hb hx' hmin' s rfl) ho
    · rw [shM_down mu b j hx', shL_down_m] at hGb' ⊢
      exact hM n ε _ ε' _ e hGb j hGb' (cond_down_m hG.hc hG.hc' hb hx' hmin' j rfl) ho

theorem occurrence_of_walk (hL : StepL) (hM : StepM) (hB : Base) : Occ := by
  intro n ε lam ε' mu e hG hW
  obtain ⟨a, ha, ho⟩ := hB n ε lam ε' mu e hG hW
  exact down hL hM hG _ a rfl ha ho

end PositivityTheory.RgHe.Dec
end
end

noncomputable section

open Finset

namespace PositivityTheory.RgHe.Dec

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition

theorem flip_discrete_series_holds : FlipDS := fun m ε lam K _ _ σ =>
  ⟨isDS_of_flip, GlobalTheory.CompanionTheory.NegDS.isDS_flip m K ε lam σ⟩

theorem decEx2_of (h1 : DecLe) (h2 : FlipDS) (h3 : FlipDec) : DecEx2 := by
  intro m ε lam H _ _ π hf ht hp hds hgap
  by_cases hle : #{a : Fin m | ε a = false} ≤ #{a : Fin m | ε a = true}
  · obtain ⟨X, hX⟩ := h1 m ε lam H π hf hle hp hds hgap
    exact ⟨X, hX⟩
  · have hds' : IsDS (fun a : Fin m => !ε a) lam π := (h2 m ε lam H π).2 hds
    have hf' : ∃ a : Fin m, (!ε a) = false := by
      obtain ⟨a, ha⟩ := ht
      exact ⟨a, by simp [ha]⟩
    have hle' : #{a : Fin m | (!ε a) = false} ≤ #{a : Fin m | (!ε a) = true} := by
      simp only [Bool.not_eq_false', Bool.not_eq_true']
      omega
    have hgap' : Formalism.QuantumDeterminants.GapAtLeast (fun a : Fin m => !ε a) lam (200 * (m : ℝ) ^ 3) := by
      intro a b hab
      apply hgap a b
      intro h
      apply hab
      simp [h]
    obtain ⟨X, hX⟩ := h1 m (fun a => !ε a) lam H π hf' hle' hp hds' hgap'
    exact h3 m ε lam H π X hX

theorem decomposition_existence_holds : DecEx2 := decEx2_of decomposition_le_holds flip_discrete_series_holds flip_decomposition_holds

theorem walk : StepL → StepM → Base → Occ := occurrence_of_walk

end PositivityTheory.RgHe.Dec
end
end

namespace PositivityTheory.RgHe

theorem occ : Occ :=
  Dec.walk (Sl.stepL LowestKTypeModel.models LowestKTypeModel.ofInt LowestKTypeModel.seed Dec.decomposition_existence_holds)
    (SM.stepM LowestKTypeModel.models LowestKTypeModel.ofInt LowestKTypeModel.seed Dec.decomposition_existence_holds)
    (PositivityTheory.RgHe3.base LowestKTypeModel.models FrameF.frame)

end PositivityTheory.RgHe

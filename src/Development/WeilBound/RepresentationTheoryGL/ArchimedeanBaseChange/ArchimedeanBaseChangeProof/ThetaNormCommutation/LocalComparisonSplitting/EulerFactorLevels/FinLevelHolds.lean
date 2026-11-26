module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetRegroupCommutative
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalFinitePlaces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfTwist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedOrbitalSwapConvolution
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqOfRealUnitaryConj
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHypothesesHold

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonSplit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedOrbitalPairConvolution
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedOrbitalSwapConvolutionStatement
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_orbital_swap_convolution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (K L : Subgroup H) (N : H) (f₁ f₂ : H → ℂ),
  IsOpen (K : Set H) → IsCompact (K : Set H) → IsOpen (L : Set H) → L ≤ K → IsHecke L f₁ → IsHecke L f₂ → Good (MonoidHom.id H) K N →
  (∀ C : Set H, IsCompact C → ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C → ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d) →
  twOrb ((MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (K.prod K) (N, 1) (fun y => f₁ y.1 * f₂ y.2) =
    twOrb (MonoidHom.id H) K N (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) := by
  first | exact @GlobalTheory.CompanionTheory.SplitSwap.main | exact GlobalTheory.CompanionTheory.SplitSwap.main | (intros; apply GlobalTheory.CompanionTheory.SplitSwap.main <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedOrbitalPairConvolution
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitConvF

def twistEquiv {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (σ : H →* H)
    (hc : Continuous σ) (hσ : ∀ g, σ (σ g) = g) : H × H ≃ₜ* H × H where
  toFun y := (y.1, σ y.2)
  invFun y := (y.1, σ y.2)
  left_inv y := by simp [hσ]
  right_inv y := by simp [hσ]
  map_mul' a b := by simp
  continuous_toFun := continuous_fst.prodMk (hc.comp continuous_snd)
  continuous_invFun := continuous_fst.prodMk (hc.comp continuous_snd)

theorem twOrb_conj_of_biinv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G)
    (K K' : Subgroup G) (δ g : G) (F : G → ℂ) (hθ : Continuous θ) (hK : IsCompact (K : Set G))
    (hK' : IsOpen (K' : Set G)) (hF : ∀ k ∈ K', ∀ x, F (k * x) = F x ∧ F (x * k) = F x) :
    twOrb θ K (g⁻¹ * δ * θ g) F = twOrb θ K δ F :=
  GlobalTheory.TwOrbConj.twOrb_twConj G θ K δ g F
    (GlobalTheory.CompanionTheory.SplitIndex.rStab_index_ne_zero_of_compact θ K K' δ F hθ hK hK' hF)

theorem splitConv_of_finite : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H),
  Continuous σ → (∀ g, σ (σ g) = g) → (∀ k ∈ K, σ k ∈ K) → IsOpen (K : Set H) → IsCompact (K : Set H) → ∀ (d d' : H) (f₁ f₂ : H → ℂ) (K' : Subgroup H),
  IsOpen (K' : Set H) → K' ≤ K → (∀ k ∈ K', σ k ∈ K') → IsHecke K' f₁ → IsHecke K' f₂ →
  Good (MonoidHom.id H) K (d * σ d') →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  twOrb ((MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (K.prod K) (d, d') (fun y => f₁ y.1 * f₂ (σ y.2)) =
    twOrb (MonoidHom.id H) K (d * σ d') (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) := by
  intro H _ _ _ _ σ K hc hσ hσK hKo hKc d d' f₁ f₂ K' hK'o hK'K hσK' h₁ h₂ hG hfin
  set θ := (MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom with hθ
  have hθc : Continuous θ := (hc.comp continuous_snd).prodMk (hc.comp continuous_fst)
  have hKKc : IsCompact ((K.prod K : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hKc.prod hKc
  have hK'K'o : IsOpen ((K'.prod K' : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hK'o.prod hK'o
  have hinv : ∀ k ∈ K'.prod K', ∀ x : H × H,
      (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) (k * x) = (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) x ∧
      (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) (x * k) = (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) x := by
    rintro ⟨k₁, k₂⟩ hk ⟨x₁, x₂⟩
    obtain ⟨hk₁, hk₂⟩ := Subgroup.mem_prod.1 hk
    have hk₂' : σ k₂ ∈ K' := hσK' _ hk₂
    constructor
    · show f₁ (k₁ * x₁) * f₂ (σ (k₂ * x₂)) = f₁ x₁ * f₂ (σ x₂)
      rw [(h₁.2 k₁ hk₁ x₁).1, map_mul, (h₂.2 _ hk₂' _).1]
    · show f₁ (x₁ * k₁) * f₂ (σ (x₂ * k₂)) = f₁ x₁ * f₂ (σ x₂)
      rw [(h₁.2 k₁ hk₁ x₁).2, map_mul, (h₂.2 _ hk₂' _).2]
  have hconj : ((1, d') : H × H)⁻¹ * (d, d') * θ (1, d') = (d * σ d', 1) := by
    have e : θ (1, d') = (σ d', 1) := by simp [hθ]
    rw [e]
    ext <;> simp
  have step₁ := twOrb_conj_of_biinv θ (K.prod K) (K'.prod K') (d, d') (1, d')
    (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) hθc hKKc hK'K'o hinv
  rw [hconj] at step₁
  rw [← step₁]
  have step₂ := GlobalTheory.EulerTw.Transport.twOrb_transport (H × H) (H × H) (twistEquiv σ hc hσ) θ
    (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom (K.prod K) (K.prod K) (d * σ d', 1)
    (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) (fun y : H × H => f₁ y.1 * f₂ y.2)
    (by
      rintro ⟨x₁, x₂⟩
      show (σ x₂, σ (σ x₁)) = (σ x₂, x₁)
      rw [hσ])
    (by
      rintro ⟨x₁, x₂⟩
      show x₁ ∈ K ∧ x₂ ∈ K ↔ x₁ ∈ K ∧ σ x₂ ∈ K
      refine and_congr_right fun _ => ⟨hσK _, fun h => ?_⟩
      simpa [hσ] using hσK _ h)
    (fun _ => rfl)
  have he : (twistEquiv σ hc hσ) (d * σ d', 1) = (d * σ d', 1) := by
    show (d * σ d', σ 1) = (d * σ d', 1)
    rw [map_one]
  rw [he] at step₂
  rw [step₂]
  exact GlobalTheory.T.twisted_orbital_swap_convolution H K K' (d * σ d') f₁ f₂ hKo hKc hK'o hK'K h₁ h₂ hG
    (GlobalTheory.T.exists_compact_conjugacy_transversal H K (d * σ d') hKc hfin)

end GlobalTheory.CompanionTheory.SplitConvF
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedOrbitalPairConvolutionStatement
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_orbital_pair_convolution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H),
  Continuous σ → (∀ g, σ (σ g) = g) → (∀ k ∈ K, σ k ∈ K) → IsOpen (K : Set H) → IsCompact (K : Set H) → ∀ (d d' : H) (f₁ f₂ : H → ℂ) (K' : Subgroup H),
  IsOpen (K' : Set H) → K' ≤ K → (∀ k ∈ K', σ k ∈ K') → IsHecke K' f₁ → IsHecke K' f₂ →
  Good (MonoidHom.id H) K (d * σ d') →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  twOrb ((MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (K.prod K) (d, d') (fun y => f₁ y.1 * f₂ (σ y.2)) =
    twOrb (MonoidHom.id H) K (d * σ d') (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) := by
  first | exact @GlobalTheory.CompanionTheory.SplitConvF.splitConv_of_finite | exact GlobalTheory.CompanionTheory.SplitConvF.splitConv_of_finite | (intros; apply GlobalTheory.CompanionTheory.SplitConvF.splitConv_of_finite <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonSplit
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses

namespace GlobalTheory.CompanionTheory.LcSplit

theorem level_pick {H : Type} [Group H] [TopologicalSpace H] (σ : H →* H) (hc : Continuous σ) (hi : ∀ g, σ (σ g) = g)
    (K A₁ A₂ : Subgroup H) (f₁ f₂ : H → ℂ) (ho₁ : IsOpen (A₁ : Set H)) (ho₂ : IsOpen (A₂ : Set H)) (hK : A₁ ≤ K)
    (h₁ : IsHecke A₁ f₁) (h₂ : IsHecke A₂ f₂) :
    ∃ L : Subgroup H, IsOpen (L : Set H) ∧ L ≤ K ∧ (∀ k ∈ L, σ k ∈ L) ∧ IsHecke L f₁ ∧ IsHecke L f₂ := by
  have hAo : IsOpen ((A₁ ⊓ A₂ : Subgroup H) : Set H) := by
    rw [Subgroup.coe_inf]; exact ho₁.inter ho₂
  refine ⟨(A₁ ⊓ A₂) ⊓ (A₁ ⊓ A₂).comap σ, ?_, fun x hx => hK hx.1.1, fun k hk => ⟨hk.2, ?_⟩,
    ⟨h₁.1, fun k hk => h₁.2 k hk.1.1⟩, ⟨h₂.1, fun k hk => h₂.2 k hk.1.2⟩⟩
  · rw [Subgroup.coe_inf]
    exact hAo.inter (hAo.preimage hc)
  · show σ (σ k) ∈ A₁ ⊓ A₂
    rw [hi]; exact hk.1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem exists_level (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (hφ₁ : IsTestP φ₁) (hφ₂ : IsTestP φ₂) (w : Pl E) :
    ∃ L : Subgroup (GLw a w × GLw b w), IsOpen (L : Set (GLw a w × GLw b w)) ∧ L ≤ K2 a b w ∧ (∀ k ∈ L, sgP a b w k ∈ L) ∧
      IsHecke L (φ₁ w) ∧ IsHecke L (φ₂ w) := by
  obtain ⟨hc, hi, hk⟩ := sgP_facts E a b w
  obtain ⟨K₁, K₂, hl₁, hl₂, ht⟩ := hφ₁
  obtain ⟨K₁', K₂', hl₁', hl₂', ht'⟩ := hφ₂
  refine level_pick (sgP a b w) hc hi (K2 a b w) ((K₁ w).prod (K₂ w)) ((K₁' w).prod (K₂' w)) _ _ ?_ ?_ ?_ (ht.1 w) (ht'.1 w)
  · rw [Subgroup.coe_prod]; exact (hl₁.1 w).1.prod (hl₂.1 w).1
  · rw [Subgroup.coe_prod]; exact (hl₁'.1 w).1.prod (hl₂'.1 w).1
  · exact Subgroup.prod_mono (hl₁.1 w).2.1 (hl₂.1 w).2.1

theorem fv_split (S : Set (Pl E)) (hS : IsSection S) (w : Pl E) (hw : w ∈ S) (hs : IsSplitAt w)
    (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    fv S φ₁ φ₂ _ y = φ₁ w (evw ⟨w, rfl⟩ y) * φ₂ w (evw ⟨w, rfl⟩ (thv a b _ y)) := by
  unfold fv
  have key : ∀ u : Above (w.under (𝓞 (maximalRealSubfield E))), u.1 ∈ S → u = ⟨w, rfl⟩ := by
    intro u hu
    exact Subtype.ext ((hS w).unique ⟨hu, u.2⟩ ⟨hw, rfl⟩)
  rw [finprod_eq_single _ (⟨w, rfl⟩ : Above (w.under (𝓞 (maximalRealSubfield E))))]
  · rw [finprod_eq_if, if_pos hw, if_pos hs]
  · intro u hu
    rw [finprod_eq_if, if_neg (fun h => hu (key u h))]

theorem th_split (a b : ℕ) (w : Pl E) (hs : IsSplitAt w) :
    (thL a w).prodMap (thL b w) = MonoidHom.id (GLw a w × GLw b w) := by
  unfold thL
  rw [if_pos hs, if_pos hs]
  ext x <;> rfl

theorem seen_split (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (w : Pl E) (hs : IsSplitAt w) :
    seen φ₁ φ₂ w = fun y => hint (K2 a b w) fun z => φ₁ w z * φ₂ w (z⁻¹ * y) := by
  funext y
  unfold seen
  rw [if_pos hs]

theorem locEl_sep {n : ℕ} (w : Pl E) (hs : IsSplitAt w) (δ : GL (Fin n) E) (h : polE δ ∈ Ell E n) :
    (nrmL n w (locEl n w δ)).val.charpoly.Separable := by
  have : (nrmL n w (locEl n w δ)).val.charpoly = (polE δ).map (algebraMap E (w.adicCompletion E)) := by
    unfold nrmL locEl polE
    rw [if_pos hs, if_pos hs]
    exact Matrix.charpoly_map _ _
  rw [this]
  exact h.2.2.1.map

theorem target_side (hU : GlobalTheory.BCT.Unr E) (w : Pl E) (hs : IsSplitAt w)
    (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) (hδ₁ : polE δ₁ ∈ Ell E a) (hδ₂ : polE δ₂ ∈ Ell E b) :
    Good (MonoidHom.id _) (K2 a b w) (locEl a w δ₁, locEl b w δ₂) ∧
    ∀ C : Set (GLw a w × GLw b w), IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id (GLw a w × GLw b w)) (locEl a w δ₁, locEl b w δ₂) : Set _)
      (K2 (E := E) a b w : Set (GLw a w × GLw b w)) | ∃ k ∈ K2 (E := E) a b w,
        (Quotient.out q * k)⁻¹ * (locEl a w δ₁, locEl b w δ₂) * MonoidHom.id (GLw a w × GLw b w) (Quotient.out q * k) ∈ C}.Finite := by
  have h1 := GlobalTheory.CompanionTheory.LocGoodProof.locGood E hU a b w (locEl a w δ₁, locEl b w δ₂) (locEl_sep w hs δ₁ hδ₁) (locEl_sep w hs δ₂ hδ₂)
  have h2 := (GlobalTheory.CompanionTheory.TwistOrbit.locSupp E hU a b w (locEl a w δ₁, locEl b w δ₂) (locEl_sep w hs δ₁ hδ₁) (locEl_sep w hs δ₂ hδ₂)).1
  rw [th_split a b w hs] at h1 h2
  exact ⟨h1, h2⟩

theorem pair_integral_points_open_compact (a b : ℕ) (w : Pl E) :
    IsOpen ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) ∧ IsCompact ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) := by
  obtain ⟨hKo₁, hKc₁⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨hKo₂, hKc₂⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b
  rw [Subgroup.coe_prod]
  exact ⟨hKo₁.prod hKo₂, hKc₁.prod hKc₂⟩

theorem locCompareSplit : LocCompareSplit := by
  intro hCj E _ _ _ hU a b S hS φ₁ φ₂ hφ₁ hφ₂ δ₁ δ₂ hδ₁ hδ₂ w hw hs
  obtain ⟨e, he1, he3, he4, heδ⟩ := GlobalTheory.CompanionTheory.SplitIso.split_iso hCj E a b _ ⟨w, rfl⟩ hs
  obtain ⟨hc, hi, hk⟩ := sgP_facts E a b w
  obtain ⟨L, hLo, hLK, hLs, hH₁, hH₂⟩ := exists_level φ₁ φ₂ hφ₁ hφ₂ w
  obtain ⟨hKo, hKc⟩ := pair_integral_points_open_compact (E := E) a b w
  obtain ⟨hG, hF⟩ := target_side hU w hs δ₁ δ₂ hδ₁ hδ₂
  set y := pv a b (w.under (𝓞 (maximalRealSubfield E))) (ratF E a δ₁, ratF E b δ₂) with hy
  have hN : (e y).1 * sgP a b w (e y).2 = (locEl a w δ₁, locEl b w δ₂) := by
    rw [hy, heδ]
    exact Prod.ext (GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL E a w δ₁ hs) (GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL E b w δ₂ hs)
  have ht := GlobalTheory.EulerTw.Transport.twOrb_transport _ _ e (thv a b _) (swTw (sgP a b w))
    (Kv a b _) ((K2 a b w).prod (K2 a b w)) y (fv S φ₁ φ₂ _) (fun z => φ₁ w z.1 * φ₂ w (sgP a b w z.2))
    he3 he4 (fun g => by
      have h2 : evw ⟨w, rfl⟩ (thv a b _ g) = sgP a b w (e g).2 := by
        rw [← he1, he3]; rfl
      show φ₁ w (e g).1 * φ₂ w (sgP a b w (e g).2) = _
      rw [he1, ← h2, fv_split S hS w hw hs])
  rw [ht, seen_split φ₁ φ₂ w hs, th_split a b w hs]
  have hsc := GlobalTheory.T.twisted_orbital_pair_convolution _ (sgP a b w) (K2 a b w) hc hi hk hKo hKc (e y).1 (e y).2 (φ₁ w) (φ₂ w) L hLo hLK hLs hH₁ hH₂
    (by rw [hN]; exact hG) (by rw [hN]; exact hF)
  rw [hN] at hsc
  exact hsc

end GlobalTheory.CompanionTheory.LcSplit

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonSplitStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_comparison_split : PositivityTheory.Rg.BcB.G8.Fin.LocCompareSplit := by
  first | exact @GlobalTheory.CompanionTheory.LcSplit.locCompareSplit | exact GlobalTheory.CompanionTheory.LcSplit.locCompareSplit | (intros; apply GlobalTheory.CompanionTheory.LcSplit.locCompareSplit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteReindexing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteReindexing
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.SecReindex

open PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_under (v : PlF E) : ∃ w : Pl E, w.under (𝓞 (maximalRealSubfield E)) = v := by
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) := by
    first
    | exact FaithfulSMul.algebraMap_injective _ _
    | exact NoZeroSMulDivisors.algebraMap_injective _ _
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  refine ⟨⟨Q, hQmax.isPrime, ?_⟩, ?_⟩
  · rintro rfl
    apply v.ne_bot
    rw [← hQ]
    exact Ideal.comap_bot_of_injective _ hinj
  · ext1
    exact hQ

def secEquiv {S : Set (Pl E)} (hS : IsSection S) : S ≃ PlF E :=
  Equiv.ofBijective (fun w => w.1.under (𝓞 (maximalRealSubfield E))) (by
    constructor
    · rintro ⟨u, hu⟩ ⟨u', hu'⟩ h
      exact Subtype.ext ((hS u).unique ⟨hu, rfl⟩ ⟨hu', h.symm⟩)
    · intro v
      obtain ⟨w, rfl⟩ := exists_under v
      obtain ⟨u, ⟨hu, huw⟩, -⟩ := hS w
      exact ⟨⟨u, hu⟩, huw⟩)

theorem secPl_eq {S : Set (Pl E)} (hS : IsSection S) (u : S) :
    secPl S (secEquiv hS u) = some u.1 := by
  have hv : secEquiv hS u = u.1.under (𝓞 (maximalRealSubfield E)) := rfl
  have h : ∃ w ∈ S, w.under (𝓞 (maximalRealSubfield E)) = secEquiv hS u := ⟨u.1, u.2, hv.symm⟩
  rw [secPl, dite_eq_left h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  exact congrArg some ((hS u.1).unique ⟨h1, h2.trans hv⟩ ⟨u.2, rfl⟩)

theorem reindex : Reindex := by
  intro E _ _ _ S hS g
  rw [show (∏ᶠ (w : Pl E) (_ : w ∈ S), g w) = ∏ᶠ u : S, g u from
    (finprod_set_coe_eq_finprod_mem S).symm]
  exact finprod_eq_of_bijective (secEquiv hS) (secEquiv hS).bijective
    (fun u => by rw [secPl_eq hS u] <;> rfl)

end GlobalTheory.CompanionTheory.SecReindex

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteReindexingStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_reindexing : PositivityTheory.Rg.BcB.G8.Fin.Reindex := by
  first | exact @GlobalTheory.CompanionTheory.SecReindex.reindex | exact GlobalTheory.CompanionTheory.SecReindex.reindex | (intros; apply GlobalTheory.CompanionTheory.SecReindex.reindex <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonOf
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonOf
namespace GlobalTheory.CompanionTheory.LocCompareHalves

open PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.UnitaryBC GlobalTheory.BCT

theorem locCompareOf : PositivityTheory.Rg.BcB.G8.Fin.LocCompareOf := by
  intro hI hS hC E _ _ _ hU a b S hSec φ₁ φ₂ h₁ h₂ δ₁ δ₂ e₁ e₂ w hw
  by_cases hs : IsSplitAt w
  · exact hS hC E hU a b S hSec φ₁ φ₂ h₁ h₂ δ₁ δ₂ e₁ e₂ w hw hs
  · exact hI hC E hU a b S hSec φ₁ φ₂ h₁ h₂ δ₁ δ₂ e₁ e₂ w hw hs

end GlobalTheory.CompanionTheory.LocCompareHalves
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonOfStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_comparison_of : PositivityTheory.Rg.BcB.G8.Fin.LocCompareOf := by
  first | exact @GlobalTheory.CompanionTheory.LocCompareHalves.locCompareOf | exact GlobalTheory.CompanionTheory.LocCompareHalves.locCompareOf | (intros; apply GlobalTheory.CompanionTheory.LocCompareHalves.locCompareOf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteEulerProductOf
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteEulerProductOf
noncomputable section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

namespace GlobalTheory.CompanionTheory.EulerAsm

theorem exists_above {E : Type} [Field E] [NumberField E] [IsCMField E] (v : PlF E) :
    ∃ w : Pl E, w.under (𝓞 (maximalRealSubfield E)) = v := by
  obtain ⟨Q, hQm, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  refine ⟨⟨Q, hQm.isPrime, hQ0⟩, ?_⟩
  apply HeightOneSpectrum.ext
  exact (hQo.over).symm

theorem eulerFinOf' : EulerFinOf' := by
  intro hC hR hG hL hH hI E _ _ _ hU a b S hS φ₁ φ₂ h1 h2 δ₁ δ₂ e1 e2
  obtain ⟨hr, hth, hK, hKm⟩ := hR hC E a b
  have hKeq : (Kf E a).prod (Kf E b) = ⨅ v, (Kv (E := E) a b v).comap (pv a b v) := by
    ext x
    rw [Subgroup.mem_iInf]
    exact hKm x
  obtain ⟨H1, H2, H3, H4, H5⟩ := hH hC E hU a b S hS φ₁ φ₂ h1 h2 δ₁ δ₂ e1 e2
  set_option synthInstance.maxHeartbeats 200000 in
  have main := GlobalTheory.T.twistedOrbitalIntegral_restrictedProduct_finprod (pv (E := E) a b) (Kv a b) hr (thP E a b) (thv a b) hth hK
    (ratF E a δ₁, ratF E b δ₂) (finFn S φ₁ φ₂) (fv S φ₁ φ₂) (hG E a b S hS φ₁ φ₂ h1 h2) H1 H2 H3 H4 H5
  rw [hKeq, main, hI E S hS]
  refine finprod_congr fun v => ?_
  have key : ∀ w ∈ S, w.under (𝓞 (maximalRealSubfield E)) = v →
      twOrb (thv a b v) (Kv a b v) (pv a b v (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ v) =
        twOrb ((thL a w).prodMap (thL b w)) (K2 a b w) (locEl a w δ₁, locEl b w δ₂) (seen φ₁ φ₂ w) := by
    rintro w hw rfl
    exact hL hC E hU a b S hS φ₁ φ₂ h1 h2 δ₁ δ₂ e1 e2 w hw
  obtain ⟨w0, hw0⟩ := exists_above v
  have h : ∃ w ∈ S, w.under (𝓞 (maximalRealSubfield E)) = v := by
    obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w0
    exact ⟨u, huS, hu.trans hw0⟩
  simp only [secPl, dif_pos h, Option.elim]
  exact key _ h.choose_spec.1 h.choose_spec.2

end GlobalTheory.CompanionTheory.EulerAsm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteEulerProductOfStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_euler_product_of : PositivityTheory.Rg.BcB.G8.Fin.EulerFinOf' := by
  first | exact @GlobalTheory.CompanionTheory.EulerAsm.eulerFinOf' | exact GlobalTheory.CompanionTheory.EulerAsm.eulerFinOf' | (intros; apply GlobalTheory.CompanionTheory.EulerAsm.eulerFinOf' <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteMassProductFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteMassProductFormula
noncomputable section

open GlobalTheory.BCT

namespace GlobalTheory.CompanionTheory.MassProd

section Cards

variable {A B C : Type} [Group A] [Group B] [Group C]

theorem card_doubleCoset (e : C ≃* A × B) (H K : Subgroup A) (H' K' : Subgroup B) (H'' K'' : Subgroup C)
    (hH : ∀ c, c ∈ H'' ↔ (e c).1 ∈ H ∧ (e c).2 ∈ H') (hK : ∀ c, c ∈ K'' ↔ (e c).1 ∈ K ∧ (e c).2 ∈ K') :
    Nat.card (DoubleCoset.Quotient (H'' : Set C) (K'' : Set C)) =
      Nat.card (DoubleCoset.Quotient (H : Set A) (K : Set A)) *
        Nat.card (DoubleCoset.Quotient (H' : Set B) (K' : Set B)) := by
  rw [← Nat.card_prod]
  apply Nat.card_congr
  let F : C → DoubleCoset.Quotient (H : Set A) (K : Set A) × DoubleCoset.Quotient (H' : Set B) (K' : Set B) :=
    fun c => (DoubleCoset.mk H K (e c).1, DoubleCoset.mk H' K' (e c).2)
  have hF : ∀ x y : C, F x = F y ↔ DoubleCoset.mk H'' K'' x = DoubleCoset.mk H'' K'' y := by
    intro x y
    simp only [F, Prod.mk.injEq, DoubleCoset.eq]
    constructor
    · rintro ⟨⟨h, hh, k, hk, h1⟩, h', hh', k', hk', h2⟩
      refine ⟨e.symm (h, h'), ?_, e.symm (k, k'), ?_, ?_⟩
      · rw [hH]; simpa using ⟨hh, hh'⟩
      · rw [hK]; simpa using ⟨hk, hk'⟩
      · apply e.injective
        simp only [map_mul, MulEquiv.apply_symm_apply]
        exact Prod.ext (by simpa using h1) (by simpa using h2)
    · rintro ⟨h, hh, k, hk, rfl⟩
      rw [hH] at hh
      rw [hK] at hk
      exact ⟨⟨_, hh.1, _, hk.1, by simp⟩, _, hh.2, _, hk.2, by simp⟩
  refine Equiv.ofBijective (Quotient.lift F fun x y h => (hF x y).2 (Quotient.sound h)) ⟨?_, ?_⟩
  · intro p q
    induction p using Quotient.inductionOn with | _ x => ?_
    induction q using Quotient.inductionOn with | _ y => ?_
    intro h
    exact (hF x y).1 h
  · rintro ⟨p, q⟩
    induction p using Quotient.inductionOn with | _ x => ?_
    induction q using Quotient.inductionOn with | _ y => ?_
    refine ⟨DoubleCoset.mk H'' K'' (e.symm (x, y)), ?_⟩
    show F (e.symm (x, y)) = _
    simp [F]

end Cards

section Top

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
  [IsTopologicalGroup G']

theorem twCent_prodMap (θ : G →* G) (θ' : G' →* G') (δ : G) (δ' : G') :
    twCent (θ.prodMap θ') (δ, δ') = (twCent θ δ).prod (twCent θ' δ') := by
  ext ⟨a, b⟩
  show (a, b) * (δ, δ') = (δ, δ') * (θ a, θ' b) ↔ a * δ = δ * θ a ∧ b * δ' = δ' * θ' b
  simp [Prod.ext_iff]

theorem compactPowers_prod (a : G) (b : G') :
    IsCompact (closure (Subgroup.zpowers ((a, b) : G × G') : Set (G × G'))) ↔
      IsCompact (closure (Subgroup.zpowers a : Set G)) ∧ IsCompact (closure (Subgroup.zpowers b : Set G')) := by
  constructor
  · intro h
    constructor
    · refine (h.image continuous_fst).closure_of_subset ?_
      rintro _ ⟨n, rfl⟩
      exact ⟨(a, b) ^ n, subset_closure ⟨n, rfl⟩, by simp⟩
    · refine (h.image continuous_snd).closure_of_subset ?_
      rintro _ ⟨n, rfl⟩
      exact ⟨(a, b) ^ n, subset_closure ⟨n, rfl⟩, by simp⟩
  · rintro ⟨h, h'⟩
    refine (h.prod h').closure_of_subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨subset_closure ⟨n, by simp⟩, subset_closure ⟨n, by simp⟩⟩

theorem cptPart_prod (T : Subgroup G) (T' : Subgroup G') :
    cptPart (T.prod T') = (cptPart T).prod (cptPart T') := by
  have h1 : ∀ {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X],
      IsCompact (closure (Subgroup.zpowers (1 : X) : Set X)) := by
    intro X _ _ _
    simpa using (isCompact_singleton (x := (1 : X))).closure
  unfold cptPart
  have hs : (1 : G) ∈ {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))} := ⟨T.one_mem, h1⟩
  have hs' : (1 : G') ∈ {t | t ∈ T' ∧ IsCompact (closure (Subgroup.zpowers t : Set G'))} := ⟨T'.one_mem, h1⟩
  rw [← Subgroup.closure_prod hs hs']
  congr 1
  ext ⟨a, b⟩
  simp only [Set.mem_setOf_eq, Set.mem_prod, compactPowers_prod, Subgroup.mem_prod]
  tauto

theorem card_inf_prod (Γ C : Subgroup G) (Γ' C' : Subgroup G') :
    Nat.card (Γ.prod Γ' ⊓ C.prod C' : Subgroup (G × G')) =
      Nat.card (Γ ⊓ C : Subgroup G) * Nat.card (Γ' ⊓ C' : Subgroup G') := by
  have h : Γ.prod Γ' ⊓ C.prod C' = (Γ ⊓ C).prod (Γ' ⊓ C') := by
    ext ⟨a, b⟩
    simp only [Subgroup.mem_inf, Subgroup.mem_prod]
    tauto
  rw [h, ← Nat.card_prod]
  exact Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv

end Top

theorem massProd : PositivityTheory.Rg.BcB.G8.Fin.MassProd := by
  intro G G' _ _ _ _ _ _ θ θ' Γ Γ' δ δ'
  unfold mass
  rw [twCent_prodMap, cptPart_prod, card_inf_prod]
  rw [card_doubleCoset (Subgroup.prodEquiv (twCent θ δ) (twCent θ' δ'))
    (Γ.subgroupOf (twCent θ δ)) ((cptPart (twCent θ δ)).subgroupOf (twCent θ δ))
    (Γ'.subgroupOf (twCent θ' δ')) ((cptPart (twCent θ' δ')).subgroupOf (twCent θ' δ'))
    _ _ (fun c => by simp only [Subgroup.mem_subgroupOf, Subgroup.mem_prod]; exact Iff.rfl)
    (fun c => by simp only [Subgroup.mem_subgroupOf, Subgroup.mem_prod]; exact Iff.rfl)]
  push_cast
  rw [mul_div_mul_comm]

end GlobalTheory.CompanionTheory.MassProd

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteMassProductFormulaStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_mass_product_formula : PositivityTheory.Rg.BcB.G8.Fin.MassProd := by
  first | exact @GlobalTheory.CompanionTheory.MassProd.massProd | exact GlobalTheory.CompanionTheory.MassProd.massProd | (intros; apply GlobalTheory.CompanionTheory.MassProd.massProd <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteHalfOfTwist
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteHalfOfTwist
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.FinHalfAsm

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

theorem cptPart_le' {G : Type} [Group G] [TopologicalSpace G] (T : Subgroup G) : cptPart T ≤ T := by
  unfold GlobalTheory.BCT.cptPart
  exact (Subgroup.closure_le _).mpr fun t ht => ht.1

theorem mass_inf_twCent {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (Γ : Subgroup G) (δ : G) :
    mass θ (Γ ⊓ twCent θ δ) δ = mass θ Γ δ := by
  have h1 : (Γ ⊓ GlobalTheory.BCT.twCent θ δ).subgroupOf (GlobalTheory.BCT.twCent θ δ) = Γ.subgroupOf (GlobalTheory.BCT.twCent θ δ) :=
    Subgroup.inf_subgroupOf_right _ _
  have h2 : Γ ⊓ GlobalTheory.BCT.twCent θ δ ⊓ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)
      = Γ ⊓ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ) := by
    rw [inf_assoc, inf_eq_right.mpr (cptPart_le' _)]
  unfold GlobalTheory.BCT.mass
  rw [h1, h2]

theorem index_rStab_orbit {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K U : Subgroup G)
    (f : G → ℂ) (δ : G) (hK : IsCompact (K : Set G)) (hU : IsOpen (U : Set G))
    (hf : ∀ u ∈ U, ∀ y, f (u⁻¹ * y * θ u) = f y) (x : G) :
    (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hopen : IsOpen ((U.subgroupOf K : Subgroup K) : Set K) := by
    rw [Subgroup.coe_subgroupOf]
    exact hU.preimage continuous_subtype_val
  have hle : U.subgroupOf K ≤ GlobalTheory.BCT.rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k)) := by
    intro k' hk'
    rw [Subgroup.mem_subgroupOf] at hk'
    change ∀ y : K, f ((x * ↑(y * k'))⁻¹ * δ * θ (x * ↑(y * k'))) = f ((x * ↑y)⁻¹ * δ * θ (x * ↑y))
    intro y
    rw [← hf (k' : G) hk' ((x * ↑y)⁻¹ * δ * θ (x * ↑y))]
    congr 1
    simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev, mul_assoc]
  haveI : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hopen
  haveI : (U.subgroupOf K).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI := Subgroup.finiteIndex_of_le hle
  exact Subgroup.FiniteIndex.index_ne_zero

theorem range_pair (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) :
    ((ratF E a).prodMap (ratF E b)).range = (ratF E a).range.prod (ratF E b).range := by
  exact MonoidHom.range_prodMap _ _

theorem finHalfOf : FinHalfOf := by
  unfold PositivityTheory.Rg.BcB.G8.Fin.FinHalfOf PositivityTheory.Rg.BcB.G8.Fin.DcCount PositivityTheory.Rg.BcB.G8.Fin.MassProd
    PositivityTheory.Rg.BcB.G8.Fin.RatFin PositivityTheory.Rg.BcB.G8.Fin.SuppFin PositivityTheory.Rg.BcB.G8.Fin.EulerFin
    PositivityTheory.Rg.BcB.G8.KfOC PositivityTheory.Rg.BcB.G8.FinLevel PositivityTheory.Rg.BcB.G8.FinHalf
  intro hDc hMP hRat hSupp hEuler hKf hFL E _ _ _ hUnr a b S hS φ₁ φ₂ hT1 hT2 δ₁ δ₂ h1 h2
  obtain ⟨hGood, hfin1, hfin2, hfin3⟩ := hRat E hUnr a b δ₁ δ₂ h1 h2
  obtain ⟨hsupp, hsuppG⟩ := hSupp E hUnr a b S hS φ₁ φ₂ hT1 hT2 δ₁ δ₂ h1 h2
  obtain ⟨U, hUo, hUinv⟩ := hFL E hUnr a b S φ₁ φ₂ hT1 hT2
  have hKo : IsOpen (((PositivityTheory.Rg.BcB.G8.Kf E a).prod (PositivityTheory.Rg.BcB.G8.Kf E b) :
      Subgroup (PositivityTheory.Rg.BcB.G8.Gf E a b)) : Set (PositivityTheory.Rg.BcB.G8.Gf E a b)) := by
    rw [Subgroup.coe_prod]
    exact (hKf E a).1.prod (hKf E b).1
  have hKc : IsCompact (((PositivityTheory.Rg.BcB.G8.Kf E a).prod (PositivityTheory.Rg.BcB.G8.Kf E b) :
      Subgroup (PositivityTheory.Rg.BcB.G8.Gf E a b)) : Set (PositivityTheory.Rg.BcB.G8.Gf E a b)) := by
    rw [Subgroup.coe_prod]
    exact (hKf E a).2.prod (hKf E b).2
  have hdc := hDc (PositivityTheory.Rg.BcB.G8.Gf E a b) (PositivityTheory.Rg.BcB.G8.thP E a b)
    ((PositivityTheory.Rg.BcB.G8.Kf E a).prod (PositivityTheory.Rg.BcB.G8.Kf E b)) (PositivityTheory.Rg.BcB.G8.gam δ₁ δ₂)
    ((GlobalTheory.BCT.ratF E a) δ₁, (GlobalTheory.BCT.ratF E b) δ₂) (PositivityTheory.Rg.BcB.G8.finFn S φ₁ φ₂)
    hKo hKc hGood inf_le_right hfin1 hfin2 hfin3
    (fun x0 => index_rStab_orbit _ _ U _ _ hKc hUo hUinv (x0 : PositivityTheory.Rg.BcB.G8.Gf E a b)) hsupp
  have hdc' : PositivityTheory.Rg.BcB.G8.dcSum (PositivityTheory.Rg.BcB.G8.gam δ₁ δ₂)
      ((PositivityTheory.Rg.BcB.G8.Kf E a).prod (PositivityTheory.Rg.BcB.G8.Kf E b)) (PositivityTheory.Rg.BcB.G8.orbFn S φ₁ φ₂ δ₁ δ₂) = _ := hdc
  have hmass : GlobalTheory.BCT.mass (PositivityTheory.Rg.BcB.G8.thP E a b) (PositivityTheory.Rg.BcB.G8.gam δ₁ δ₂)
      ((GlobalTheory.BCT.ratF E a) δ₁, (GlobalTheory.BCT.ratF E b) δ₂) =
      GlobalTheory.BCT.mass (GlobalTheory.BCT.thF E a) (GlobalTheory.BCT.ratF E a).range ((GlobalTheory.BCT.ratF E a) δ₁) *
        GlobalTheory.BCT.mass (GlobalTheory.BCT.thF E b) (GlobalTheory.BCT.ratF E b).range ((GlobalTheory.BCT.ratF E b) δ₂) := by
    unfold PositivityTheory.Rg.BcB.G8.gam
    rw [mass_inf_twCent, range_pair]
    exact hMP _ _ (GlobalTheory.BCT.thF E a) (GlobalTheory.BCT.thF E b) _ _ _ _
  refine ⟨hsuppG, hfin1, ?_⟩
  rw [hdc', hmass, hEuler E hUnr a b S hS φ₁ φ₂ hT1 hT2 δ₁ δ₂ h1 h2]

end GlobalTheory.CompanionTheory.FinHalfAsm

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteHalfOfTwistStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_half_of_twist : PositivityTheory.Rg.BcB.G8.Fin.FinHalfOf := by
  first | exact @GlobalTheory.CompanionTheory.FinHalfAsm.finHalfOf | exact GlobalTheory.CompanionTheory.FinHalfAsm.finHalfOf | (intros; apply GlobalTheory.CompanionTheory.FinHalfAsm.finHalfOf <;> assumption)
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.PUnitAE
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8.Fin

open PositivityTheory.Rg.BcB.G8

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem unitae_nrm (hU : Unr E) (n : ℕ) (w : Pl E) (δ : GL (Fin n) E) :
    nrmL n w (locEl n w δ) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ) := by
  by_cases hs : IsSplitAt w
  · unfold nrmL locEl
    rw [if_pos hs, if_pos hs]
  · unfold nrmL locEl
    rw [if_neg hs, if_neg hs]
    obtain ⟨-, -, -, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    obtain ⟨hp, -⟩ := hns hs
    rw [map_mul, thE, GlobalTheory.ThetaPull.map_thetaGL (algebraMap E (w.adicCompletion E)) _ (cj w) (fun x => (hp x).symm)]

theorem unitae_single (hU : Unr E) (n : ℕ) (δ : GL (Fin n) E) (hsep : (polE δ).Separable) :
    ∀ᶠ w : Pl E in cofinite, locEl n w δ ∈ GlobalTheory.LFun.KGL w (n := n) ∧
      (∀ g : GLw n w, g⁻¹ * locEl n w δ * thL n w g ∈ GlobalTheory.LFun.KGL w (n := n) →
        ∃ t ∈ twCent (thL n w) (locEl n w δ), t⁻¹ * g ∈ GlobalTheory.LFun.KGL w (n := n)) ∧
      (∀ t ∈ twCent (thL n w) (locEl n w δ), IsCompact (closure (Subgroup.zpowers t : Set (GLw n w))) →
        t ∈ GlobalTheory.LFun.KGL w (n := n)) := by
  filter_upwards [GlobalTheory.EulerTwU.eventually_pc_ratF_mem δ, GlobalTheory.EulerTwU.eventually_pc_ratF_mem (δ * thE E n δ),
    GlobalTheory.BCT.SepBezout.bezout_eventually E _ hsep] with w h1 h2 h3
  rw [GlobalTheory.EulerTwU.pc_ratF] at h1 h2
  have hN := unitae_nrm hU n w δ
  have hbez : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w (locEl n w δ)).val.charpoly + v * derivative (nrmL n w (locEl n w δ)).val.charpoly = 1 := by
    have e : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ)).val.charpoly =
        (polE δ).map (algebraMap E (w.adicCompletion E)) := Matrix.charpoly_map _ _
    rw [hN, e]
    exact h3
  have hy : locEl n w δ ∈ GlobalTheory.LFun.KGL w (n := n) := by
    unfold locEl
    split_ifs
    · exact h2
    · exact h1
  have hNK : nrmL n w (locEl n w δ) ∈ GlobalTheory.LFun.KGL w (n := n) := by rw [hN]; exact h2
  refine ⟨hy, ?_, ?_⟩
  · intro g hg
    by_cases hs : IsSplitAt w
    · have hθ : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
      have hnr : nrmL n w (locEl n w δ) = locEl n w δ := by unfold nrmL; rw [if_pos hs]
      rw [hθ, MonoidHom.id_apply] at hg
      rw [hnr] at hbez
      obtain ⟨t, ht, k, hk, hgk⟩ := GlobalTheory.SplitUniq.splitUniq E n w _ g hy hbez hg
      refine ⟨t, ?_, ?_⟩
      · show t * locEl n w δ = locEl n w δ * thL n w t
        rw [hθ, MonoidHom.id_apply]
        exact ht
      · rw [hgk, inv_mul_cancel_left]
        exact hk
    · obtain ⟨t, ht, k, hk, hgk⟩ := GlobalTheory.InertUniq.eq_twCent_mul_KGL E hU n w hs _ g hy hbez hg
      refine ⟨t, ht, ?_⟩
      rw [hgk, inv_mul_cancel_left]
      exact hk
  · intro t ht hc
    have ht' : t * locEl n w δ = locEl n w δ * thL n w t := ht
    have hcomm : t * nrmL n w (locEl n w δ) = nrmL n w (locEl n w δ) * t := by
      by_cases hs : IsSplitAt w
      · have hθ : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
        rw [hθ, MonoidHom.id_apply] at ht'
        unfold nrmL
        rw [if_pos hs]
        exact ht'
      · have hθ : thL n w = thetaGL n (cj w) := by unfold thL; rw [if_neg hs]
        obtain ⟨-, hinv, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
        rw [hθ] at ht'
        have hth := GlobalTheory.ThetaPull.thetaGL_thetaGL (a := n) (cj w) hinv t
        unfold nrmL
        rw [if_neg hs]
        calc t * (locEl n w δ * thetaGL n (cj w) (locEl n w δ))
            = locEl n w δ * thetaGL n (cj w) t * thetaGL n (cj w) (locEl n w δ) := by rw [← mul_assoc, ht']
          _ = locEl n w δ * thetaGL n (cj w) (t * locEl n w δ) := by rw [map_mul, mul_assoc]
          _ = locEl n w δ * thetaGL n (cj w) (locEl n w δ * thetaGL n (cj w) t) := by rw [ht']
          _ = locEl n w δ * thetaGL n (cj w) (locEl n w δ) * t := by rw [map_mul, hth, mul_assoc]
    exact GlobalTheory.StabInt.mem_KGL_of_commute E n w _ t hNK hbez hcomm hc

theorem unitae_cpt_fst {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A] [Group B]
    [TopologicalSpace B] [IsTopologicalGroup B] (t : A × B) (h : IsCompact (closure (Subgroup.zpowers t : Set (A × B)))) :
    IsCompact (closure (Subgroup.zpowers t.1 : Set A)) := by
  have hK := h.image continuous_fst
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  rintro _ ⟨k, rfl⟩
  exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩

theorem unitae_cpt_snd {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [Group B]
    [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B] (t : A × B) (h : IsCompact (closure (Subgroup.zpowers t : Set (A × B)))) :
    IsCompact (closure (Subgroup.zpowers t.2 : Set B)) := by
  have hK := h.image continuous_snd
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  rintro _ ⟨k, rfl⟩
  exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩

theorem unitAE_holds : UnitAE := by
  intro E _ _ _ hU a b S _ δ₁ δ₂ h₁ h₂
  have hs₁ : (polE δ₁).Separable := by obtain ⟨-, -, h, -⟩ := h₁; exact h
  have hs₂ : (polE δ₂).Separable := by obtain ⟨-, -, h, -⟩ := h₂; exact h
  have hev := (unitae_single hU a δ₁ hs₁).and (unitae_single hU b δ₂ hs₂)
  filter_upwards [(Subtype.val_injective (p := (· ∈ S))).tendsto_cofinite.eventually hev] with w hw
  obtain ⟨⟨hy1, hc1, hk1⟩, ⟨hy2, hc2, hk2⟩⟩ := hw
  rintro y rfl
  refine ⟨Subgroup.mem_prod.2 ⟨hy1, hy2⟩, ?_, ?_⟩
  · rintro ⟨g1, g2⟩ hg
    have hg' := Subgroup.mem_prod.1 hg
    obtain ⟨t1, ht1, hk1'⟩ := hc1 g1 hg'.1
    obtain ⟨t2, ht2, hk2'⟩ := hc2 g2 hg'.2
    refine ⟨(t1, t2), ?_, Subgroup.mem_prod.2 ⟨hk1', hk2'⟩⟩
    have e1 : t1 * locEl a w.1 δ₁ = locEl a w.1 δ₁ * thL a w.1 t1 := ht1
    have e2 : t2 * locEl b w.1 δ₂ = locEl b w.1 δ₂ * thL b w.1 t2 := ht2
    show (t1, t2) * (locEl a w.1 δ₁, locEl b w.1 δ₂) =
      (locEl a w.1 δ₁, locEl b w.1 δ₂) * ((thL a w.1).prodMap (thL b w.1)) (t1, t2)
    exact Prod.ext e1 e2
  · refine (Subgroup.closure_le _).2 fun t ht => ?_
    obtain ⟨ht1, ht2⟩ := ht
    have e : t * (locEl a w.1 δ₁, locEl b w.1 δ₂) =
        (locEl a w.1 δ₁, locEl b w.1 δ₂) * ((thL a w.1).prodMap (thL b w.1)) t := ht1
    have e1 : t.1 ∈ twCent (thL a w.1) (locEl a w.1 δ₁) := congrArg Prod.fst e
    have e2 : t.2 ∈ twCent (thL b w.1) (locEl b w.1 δ₂) := congrArg Prod.snd e
    exact Subgroup.mem_prod.2 ⟨hk1 _ e1 (unitae_cpt_fst t ht2), hk2 _ e2 (unitae_cpt_snd t ht2)⟩

end PositivityTheory.Rg.BcB.G8.Fin

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.DcCount
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8.Fin.DoubleCosetCounting

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

theorem avg_comp_mul_left {H : Type} [Group H] (u : H → ℂ) (h : H) : avg (fun y => u (h * y)) = avg u := by
  have hR : rStab (fun y => u (h * y)) = rStab u := by
    ext k
    show (∀ x, u (h * (x * k)) = u (h * x)) ↔ ∀ x, u (x * k) = u x
    constructor
    · intro H x
      have := H (h⁻¹ * x)
      simpa [mul_assoc] using this
    · intro H x
      simpa [mul_assoc] using H (h * x)
  unfold avg
  rw [hR]
  congr 1
  calc ∑ᶠ q : H ⧸ rStab u, u (h * q.out) = ∑ᶠ q : H ⧸ rStab u, u ((h • q).out) := by
        refine finsum_congr fun q => ?_
        obtain ⟨r, hr⟩ := QuotientGroup.mk_out_eq_mul (rStab u) (h * q.out)
        have hq : h • q = ((h * q.out : H) : H ⧸ rStab u) := by
          conv_lhs => rw [← QuotientGroup.out_eq' q]
          rfl
        rw [hq, hr]
        exact (r.2 (h * q.out)).symm
    _ = ∑ᶠ q : H ⧸ rStab u, u q.out := finsum_comp_equiv (MulAction.toPerm h) (f := fun q : H ⧸ rStab u => u q.out)

end PositivityTheory.Rg.BcB.G8.Fin.DoubleCosetCounting

namespace PositivityTheory.Rg.BcB.G8.Fin

open PositivityTheory.Rg.BcB.G8

theorem DcCount_pf : DcCount := by
  intro G _ _ _ θ K Γ δ f _ _ hG hΓ _ _ _ _ _
  have hCT : cptPart (twCent θ δ) ≤ twCent θ δ := (Subgroup.closure_le _).2 fun t ht => ht.1
  have hinv : ∀ t ∈ twCent θ δ, ∀ k ∈ K, ∀ x : G,
      (avg fun k' : K => f ((t * x * k * k')⁻¹ * δ * θ (t * x * k * k'))) =
        avg fun k' : K => f ((x * k')⁻¹ * δ * θ (x * k')) := by
    intro t ht k hk x
    have ht' : t * δ = δ * θ t := ht
    have e1 : t⁻¹ * δ * θ t = δ := by
      rw [mul_assoc, ← ht', ← mul_assoc, inv_mul_cancel, one_mul]
    have e2 : ∀ y : G, (t * y)⁻¹ * δ * θ (t * y) = y⁻¹ * δ * θ y := by
      intro y
      rw [map_mul, _root_.mul_inv_rev]
      calc y⁻¹ * t⁻¹ * δ * (θ t * θ y) = y⁻¹ * (t⁻¹ * δ * θ t) * θ y := by simp only [mul_assoc]
        _ = y⁻¹ * δ * θ y := by rw [e1]
    have e3 : (fun k' : K => f ((t * x * k * k')⁻¹ * δ * θ (t * x * k * k'))) =
        fun k' : K => (fun y : K => f ((x * y)⁻¹ * δ * θ (x * y))) (⟨k, hk⟩ * k') := by
      funext k'
      have : t * x * k * (k' : G) = t * (x * ((⟨k, hk⟩ * k' : K) : G)) := by simp [mul_assoc]
      rw [this, e2]
    rw [e3]
    exact DoubleCosetCounting.avg_comp_mul_left (fun y : K => f ((x * y)⁻¹ * δ * θ (x * y))) ⟨k, hk⟩
  have hreg := GlobalTheory.T.finsum_doubleCoset_regroup_commutative G (twCent θ δ) Γ (cptPart (twCent θ δ)) K
    (fun x => avg fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))) hG.1 hCT hG.2 hinv
  rw [inf_eq_left.2 hΓ] at hreg
  have key : dcSum Γ K (fun x => f (x⁻¹ * δ * θ x)) =
      ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
        ((Nat.card (Γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℂ))⁻¹ *
          avg (fun k : K => f ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k))) := by
    unfold dcSum
    exact finsum_congr fun q => by rw [div_eq_inv_mul]
  rw [key, hreg]
  rfl

end PositivityTheory.Rg.BcB.G8.Fin

end
end

namespace PositivityTheory.Rg.BcB.G8.Fin

theorem kfOC_holds : PositivityTheory.Rg.BcB.G8.KfOC := GlobalTheory.T.finite_kernel_compact_open

theorem finLevel_holds : PositivityTheory.Rg.BcB.G8.FinLevel := GlobalTheory.T.finite_level_facts

theorem suppFin_holds : SuppFin := GlobalTheory.T.finite_support_of_twist GlobalTheory.T.local_support_facts unitAE_holds GlobalTheory.T.rational_finite_places GlobalTheory.T.local_good_reduction

theorem eulerFin_holds : EulerFin :=
  GlobalTheory.T.finite_euler_product_of GlobalTheory.T.finite_conjugacy_exists GlobalTheory.T.finite_restriction_vanishing GlobalTheory.T.aux_statement_21 (GlobalTheory.T.local_comparison_of GlobalTheory.T.local_comparison_inert GlobalTheory.T.local_comparison_split) GlobalTheory.T.local_hypotheses_hold GlobalTheory.T.finite_reindexing

theorem finHalf_holds : PositivityTheory.Rg.BcB.G8.FinHalf :=
  GlobalTheory.T.finite_half_of_twist DcCount_pf GlobalTheory.T.finite_mass_product_formula GlobalTheory.T.rational_finite_places suppFin_holds eulerFin_holds kfOC_holds finLevel_holds

end PositivityTheory.Rg.BcB.G8.Fin

module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceTransposePow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.RadCov

section Defs

variable {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {n : ℕ}

def lowers (F : ℕ → Submodule R (Fin n → K)) (c : ℕ) : Submodule R (Matrix (Fin n) (Fin n) K) where
  carrier := {T | ∀ b, ∀ y ∈ F (b + c + 1), T *ᵥ y ∈ F b}
  zero_mem' := fun b y _ => by simp
  add_mem' := fun {S T} hS hT b y hy => by
    rw [Matrix.add_mulVec]
    exact add_mem (hS b y hy) (hT b y hy)
  smul_mem' := fun r T hT b y hy => by
    rw [Matrix.smul_mulVec]
    exact Submodule.smul_mem _ _ (hT b y hy)

theorem mem_lowers {F : ℕ → Submodule R (Fin n → K)} {c : ℕ} {T : Matrix (Fin n) (Fin n) K} :
    T ∈ lowers F c ↔ ∀ b, ∀ y ∈ F (b + c + 1), T *ᵥ y ∈ F b := Iff.rfl

def IsDualFlag [StarRing K] (J : Matrix (Fin n) (Fin n) K) (F : ℕ → Submodule R (Fin n → K)) (m : ℕ) : Prop :=
  Monotone F ∧ F 0 = ⊥ ∧ (∀ b, m ≤ b → F b = F m) ∧
    ∀ b, b ≤ m → ∀ y, y ∈ F (m - b) ↔ y ∈ F m ∧ ∀ x ∈ F b, star x ⬝ᵥ (J *ᵥ y) = 0

def Biorth (r : ℕ → ℕ) (m : ℕ) (T : ∀ b, Matrix (Fin n) (Fin (r b)) K)
    (T' : ∀ b, Matrix (Fin (r b)) (Fin n) K) : Prop :=
  (∀ b, T' b * T b = 1) ∧ (∀ b b', b ≠ b' → T' b * T b' = 0) ∧ ∑ b ∈ Finset.range m, T b * T' b = 1

theorem lowers_succ_le {F : ℕ → Submodule R (Fin n → K)} (hF : Monotone F) (c : ℕ) :
    lowers F (c + 1) ≤ lowers F c := by
  intro T hT
  rw [mem_lowers] at hT ⊢
  intro b y hy
  exact hT b y (hF (by omega) hy)

theorem lowers_anti {F : ℕ → Submodule R (Fin n → K)} (hF : Monotone F) : Antitone (lowers F) :=
  antitone_nat_of_succ_le (lowers_succ_le hF)

theorem lowers_mul {F : ℕ → Submodule R (Fin n → K)} {c c' : ℕ} {X Y : Matrix (Fin n) (Fin n) K}
    (hX : X ∈ lowers F c) (hY : Y ∈ lowers F c') : X * Y ∈ lowers F (c + c' + 1) := by
  rw [mem_lowers] at hX hY ⊢
  intro b y hy
  rw [← Matrix.mulVec_mulVec]
  apply hX b
  apply hY (b + c + 1)
  have e : b + c + 1 + c' + 1 = b + (c + c' + 1) + 1 := by omega
  rw [e]
  exact hy

theorem lowers_mul_zero {F : ℕ → Submodule R (Fin n → K)} {c : ℕ} {X Y : Matrix (Fin n) (Fin n) K}
    (hX : X ∈ lowers F c) (hY : Y ∈ lowers F 0) :
    X * Y ∈ lowers F (c + 1) ∧ Y * X ∈ lowers F (c + 1) := by
  have h1 := lowers_mul hX hY
  have h2 := lowers_mul hY hX
  rw [Nat.add_zero] at h1
  rw [Nat.zero_add] at h2
  exact ⟨h1, h2⟩

theorem lowers_eq_bot {F : ℕ → Submodule R (Fin n → K)} {m : ℕ} (h0 : F 0 = ⊥)
    (hm : ∀ b, m ≤ b → F b = F m) (hsp : Submodule.span K (F m : Set (Fin n → K)) = ⊤) :
    lowers F m = ⊥ := by
  rw [eq_bot_iff]
  intro T hT
  rw [mem_lowers] at hT
  have hzero : ∀ y ∈ (F m : Set (Fin n → K)), T *ᵥ y = 0 := by
    intro y hy
    have hy' : y ∈ F (0 + m + 1) := by
      rw [hm (0 + m + 1) (by omega)]
      exact hy
    have h := hT 0 y hy'
    rw [h0] at h
    exact (Submodule.mem_bot R).1 h
  have hlin : Matrix.toLin' T = 0 := by
    apply LinearMap.ext_on hsp
    intro y hy
    simpa [Matrix.toLin'_apply] using hzero y hy
  have hT0 : T = 0 := by
    apply Matrix.toLin'.injective
    rw [hlin, map_zero]
  exact (Submodule.mem_bot R).2 hT0

theorem lowers_adj [StarRing K] {J : Matrix (Fin n) (Fin n) K} (hJ : Jᴴ = J)
    {F : ℕ → Submodule R (Fin n → K)} {m : ℕ} (hF : IsDualFlag J F m) {c : ℕ}
    {T T' : Matrix (Fin n) (Fin n) K} (hT : T ∈ lowers F c) (hadj : J * T' = Tᴴ * J)
    (htop : ∀ y ∈ F m, T' *ᵥ y ∈ F m) : T' ∈ lowers F c := by
  obtain ⟨hmono, h0, hstab, hdual⟩ := hF
  have hleM : ∀ k, F k ≤ F m := by
    intro k
    rcases le_total k m with h | h
    · exact hmono h
    · exact (hstab k h).le
  rw [mem_lowers] at hT ⊢
  intro b y hy
  have hyM : y ∈ F m := hleM _ hy
  rcases le_total m b with hb | hb
  · rw [hstab b hb]
    exact htop y hyM
  ·
    have key : ∀ x ∈ F (m - b), star x ⬝ᵥ (J *ᵥ (T' *ᵥ y)) = 0 := by
      intro x hx
      have e : star x ⬝ᵥ (J *ᵥ (T' *ᵥ y)) = star (T *ᵥ x) ⬝ᵥ (J *ᵥ y) := by
        rw [Matrix.mulVec_mulVec, hadj, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
          Matrix.star_mulVec]
      rw [e]
      rcases le_or_gt (b + c + 1) m with hc | hc
      · have hTx : T *ᵥ x ∈ F (m - (b + c + 1)) := by
          apply hT
          have e' : m - (b + c + 1) + c + 1 = m - b := by omega
          rw [e']
          exact hx
        have hy' : y ∈ F (m - (m - (b + c + 1))) := by
          rw [show m - (m - (b + c + 1)) = b + c + 1 by omega]
          exact hy
        exact ((hdual _ (Nat.sub_le _ _) y).1 hy').2 _ hTx
      ·
        have hTx : T *ᵥ x ∈ F 0 := hT 0 x (hmono (by omega) hx)
        rw [h0] at hTx
        rw [(Submodule.mem_bot R).1 hTx, star_zero, zero_dotProduct]
    have hd := hdual (m - b) (Nat.sub_le _ _) (T' *ᵥ y)
    rw [show m - (m - b) = b by omega] at hd
    exact hd.2 ⟨htop y hyM, key⟩

end Defs

section Loc

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def locFlag (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (b : ℕ) :
    Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ ((fun y : Fin n → E => P⁻¹ *ᵥ fun l => φ (y l)) '' (F b : Set _))

def PlaceMatch {ι : Type} (φ : ι → E →+* ℂ) (P : ι → Matrix (Fin n) (Fin n) ℂ)
    (X : InfinitePlace E → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Function.Bijective (fun v => InfinitePlace.mk (φ v)) ∧
    ∀ v, ((InfinitePlace.mk (φ v)).embedding = φ v ∧ X (InfinitePlace.mk (φ v)) = P v) ∨
      ((InfinitePlace.mk (φ v)).embedding = (starRingEnd ℂ).comp (φ v) ∧
        X (InfinitePlace.mk (φ v)) = (P v).map (starRingEnd ℂ))

def pieceHt [StarRing E] (X : InfinitePlace E → Matrix (Fin n) (Fin n) ℂ)
    (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (b : ℕ) : ℝ :=
  Formalism.HN.ht (Pi.basisFun E (Fin n)) X (F (b + 1)) / Formalism.HN.ht (Pi.basisFun E (Fin n)) X (F b)

def covStd (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)) : ℝ :=
  GlobalTheory.FlagBase.covAt E j (GlobalTheory.FlagBase.latAt E j Λ fun _ a b => if a = b then 1 else 0)

end Loc

end GlobalTheory.RadCov
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConsequencesOfDsClass
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.ClassificationConsequences

open GlobalTheory.LowestKTypeDetermines

variable {n : ℕ} {ε : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {τ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

theorem mul_mem_UJset {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) :
    a * b ∈ UJset ε := by
  have ha' : aᴴ * Jm ε * a = Jm ε := ha
  have hb' : bᴴ * Jm ε * b = Jm ε := hb
  show (a * b)ᴴ * Jm ε * (a * b) = Jm ε
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [ha', hb']

theorem isSqIntIrr_of_uEquiv (he : UEquiv ε σ τ) (h : IsSqIntIrr ε τ) : IsSqIntIrr ε σ := by
  obtain ⟨T, hT⟩ := he
  obtain ⟨hc, hn, ⟨⟨h1, hmul⟩, hiso, hcont⟩, hirr, hsq⟩ := h

  have hσ : ∀ g ∈ UJset ε, ∀ v, σ g v = T.symm (τ g (T v)) := by
    intro g hg v
    rw [← hT g hg v, LinearIsometryEquiv.symm_apply_apply]
  have one_mem : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  refine ⟨?_, ?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · haveI := hc
    exact T.toIsometryEquiv.completeSpace
  · haveI := hn
    exact T.toLinearEquiv.toEquiv.nontrivial
  · ext v
    rw [hσ 1 one_mem v, h1]
    simp
  · intro a ha b hb
    ext v
    rw [hσ _ (mul_mem_UJset ha hb), hmul a ha b hb, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, hσ a ha, hσ b hb, LinearIsometryEquiv.apply_symm_apply]
  · intro g hg v
    rw [hσ g hg v, LinearIsometryEquiv.norm_map, hiso g hg, LinearIsometryEquiv.norm_map]
  · intro v
    have hc' : ContinuousOn (fun g => T.symm (τ g (T v))) (UJset ε) :=
      T.symm.continuous.comp_continuousOn (hcont (T v))
    exact hc'.congr (fun g hg => hσ g hg v)
  ·
    intro S hS hst
    let S' : Submodule ℂ H' := S.comap (T.symm.toLinearEquiv : H' →ₗ[ℂ] H)
    have mem' : ∀ w, w ∈ S' ↔ T.symm w ∈ S := fun w => Iff.rfl
    have hcl : IsClosed (S' : Set H') := hS.preimage T.symm.continuous
    have hst' : ∀ g ∈ UJset ε, ∀ w ∈ S', τ g w ∈ S' := by
      intro g hg w hw
      rw [mem'] at hw ⊢
      rw [symm_inter T hT g hg w]
      exact hst g hg _ hw
    rcases hirr S' hcl hst' with h0 | h0
    · left
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hTv : T v ∈ S' := by
        rw [mem', LinearIsometryEquiv.symm_apply_apply]
        exact hv
      rw [h0, Submodule.mem_bot] at hTv
      exact (LinearIsometryEquiv.map_eq_zero_iff T).mp hTv
    · right
      rw [Submodule.eq_top_iff']
      intro v
      have hTv : T v ∈ S' := by
        rw [h0]
        exact Submodule.mem_top
      rw [mem', LinearIsometryEquiv.symm_apply_apply] at hTv
      exact hTv
  ·
    intro v w
    have heq : coefOn (ε := ε) σ v w = coefOn (ε := ε) τ (T v) (T w) := by
      funext g
      have hg : umat g ∈ UJset ε := g.2
      simp only [coefOn]
      rw [← hT _ hg v, LinearIsometryEquiv.inner_map_map]
    rw [heq]
    exact hsq (T v) (T w)

theorem isDS_of_uEquiv {lam : Fin n → ℝ} (he : UEquiv ε σ τ) (h : IsDS ε lam τ) : IsDS ε lam σ := by
  obtain ⟨c1, c2, c3, c4, c5⟩ :=
    isSqIntIrr_of_uEquiv he ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
  obtain ⟨T, hT⟩ := he
  refine ⟨c1, c2, c3, c4, c5, ?_, ?_⟩
  · exact exists_ktype_of_uEquiv (uEquiv_symm ⟨T, hT⟩) h.2.2.2.2.2.1
  · intro μ S hS
    exact h.2.2.2.2.2.2 μ _ (ktype_transfer T hT hS)

theorem isKFin_transfer (T : H ≃ₗᵢ[ℂ] H') (h : ∀ g ∈ UJset ε, ∀ v, T (σ g v) = τ g (T v)) {v : H}
    (hv : IsKFin ε σ v) : IsKFin ε τ (T v) := by
  obtain ⟨S, hfin, hvS, hst⟩ := hv
  refine ⟨S.map (T.toLinearEquiv : H →ₗ[ℂ] H'), ?_, Submodule.mem_map_of_mem hvS, ?_⟩
  · haveI := hfin
    infer_instance
  · intro g hg w hw
    obtain ⟨u, hu, hwu⟩ := Submodule.mem_map.mp hw
    have hw' : w = T u := hwu.symm
    subst hw'
    rw [← h g (Kset_sub hg) u]
    exact Submodule.mem_map_of_mem (hst g hg u hu)

theorem isZEigen_congr {χ : Fin n → ℂ} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g, inUJ ε g → f g = f' g) (hf : IsZEigen ε χ f') : IsZEigen ε χ f := by
  obtain ⟨hsm, heig⟩ := hf
  refine ⟨?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hsm g₀ hg₀
    exact ⟨U, F, hU, hgU, hF, fun g hgU' hg => (h g hg).trans (hfF g hgU' hg)⟩
  · intro m g hg

    have hgel : gelf ε m f g = gelf ε m f' g := by
      simp only [gelf]
      exact Finset.sum_congr rfl (fun a _ => Eword_congr ε h _ g hg)
    rw [hgel, heig m g hg, h g hg]

theorem hasInfChar_of_uEquiv {χ : Fin n → ℂ} (he : UEquiv ε σ τ) (h : HasInfChar ε χ τ) :
    HasInfChar ε χ σ := by
  obtain ⟨T, hT⟩ := he
  intro v w hv hw
  have hz := h (T v) (T w) (isKFin_transfer T hT hv) (isKFin_transfer T hT hw)
  refine isZEigen_congr (fun g hg => ?_) hz
  show ⟪w, σ g v⟫_ℂ = ⟪T w, τ g (T v)⟫_ℂ
  rw [← hT g hg v, LinearIsometryEquiv.inner_map_map]

theorem dsExhaust_of_dsClass (h : DSClass) : DSExhaust := by
  intro n ε H _ _ σ hσ
  obtain ⟨G, i1, i2, π, hπ, hcl⟩ := h n
  obtain ⟨s, mu, hmu, hs, he⟩ := hcl ε H σ hσ
  exact ⟨s, mu, hmu, hs, isDS_of_uEquiv he (isDS_of_isHCDS hmu (hπ (ε ∘ s) mu hmu))⟩

theorem dsInfChar_of_dsClass (h : DSClass) : DSInfChar := by
  intro n ε lam H _ _ σ hl hσ
  obtain ⟨G, i1, i2, π, hπ, huniq⟩ := exists_model h ε hl
  exact hasInfChar_of_uEquiv (huniq H σ hσ) hπ.2.1

theorem strictLow_of_dsClass (h : DSClass) : StrictLow := by
  intro n ε lam hl H _ _ _ σ hσ
  obtain ⟨S0, hS0⟩ := hσ.2.2.2.2.2.1
  refine ⟨?_, ?_⟩
  ·
    have hset : {S : Submodule ℂ H | IsKTypeOf ε σ (lowK ε lam) S} = {S0} := by
      ext S
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro hS
        exact lowKMultOne_of_dsClass h n ε lam H σ hl hσ S S0 hS hS0
      · rintro rfl
        exact hS0
    have hsub : lowKSub ε lam σ = S0 := by
      show sSup {S : Submodule ℂ H | IsKTypeOf ε σ (lowK ε lam) S} = S0
      rw [hset, sSup_singleton]
    rw [hsub]
    exact hS0
  ·
    intro μ S hS hne
    obtain ⟨c, hc, hμ⟩ := kTypesAbove_of_dsClass h n ε lam H σ hl hσ μ S hS
    have hQ0 : (∑ a, ∑ b, (c a b : ℝ) • root a b) ≠ 0 := by
      intro h0
      apply hne
      rw [hμ, h0, add_zero]
    have hx : Antitone (lam + Formalism.QuantumDeterminants.rhoStd n) := (strictAnti_add_rho hl.1).antitone
    have hcone := nsq_add_cone hx hc
    have hpos : 0 < nsq (∑ a, ∑ b, (c a b : ℝ) • root a b) := by
      rcases (nsq_nonneg (∑ a, ∑ b, (c a b : ℝ) • root a b)).lt_or_eq with hp | hp
      · exact hp
      · exact absurd (eq_zero_of_nsq hp.symm.le) hQ0
    have e1 : vNormSq ε (lowK ε lam) = nsq (lam + Formalism.QuantumDeterminants.rhoStd n) := by
      show nsq (lowK ε lam + (2 : ℝ) • rhoC ε) = _
      rw [lowK_add]
    have e2 : vNormSq ε μ = nsq (lam + Formalism.QuantumDeterminants.rhoStd n + ∑ a, ∑ b, (c a b : ℝ) • root a b) := by
      show nsq (μ + (2 : ℝ) • rhoC ε) = _
      rw [hμ, add_right_comm (lowK ε lam) _ ((2 : ℝ) • rhoC ε), lowK_add]
    rw [e1, e2]
    linarith

theorem consequences_of_dsClass :
    DSClass → DSExists ∧ DSExhaust ∧ DSUnique ∧ DSInfChar ∧ LowKMultOne ∧ KTypesAbove ∧ StrictLow := by
  intro h
  exact ⟨dsExists_of_dsClass h, dsExhaust_of_dsClass h, dsUnique_of_dsClass h, dsInfChar_of_dsClass h,
    lowKMultOne_of_dsClass h, kTypesAbove_of_dsClass h, strictLow_of_dsClass h⟩

end GlobalTheory.ClassificationConsequences
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section
namespace GlobalTheory.Dec.GelfAd

variable {n : ℕ}

private lemma conj_apply_lemma {A : Type} [Ring A] [Algebra ℂ A] (P Q : Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) A) (a b : Fin n) :
    (P.map (algebraMap ℂ A) * X * Q.map (algebraMap ℂ A)) a b = ∑ c, ∑ d, (P a c * Q d b) • X c d := by
  simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [Algebra.smul_def, map_mul, mul_assoc, ← Algebra.commutes (Q d b) (X c d), ← mul_assoc]

private lemma sum_diag_conj_eq_sum_diag {A : Type} [Ring A] [Algebra ℂ A] (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (X : Matrix (Fin n) (Fin n) A) :
    ∑ a, (P.map (algebraMap ℂ A) * X * Q.map (algebraMap ℂ A)) a a = ∑ a, X a a := by
  simp only [conj_apply_lemma]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have hd : ∀ d, ∑ a, P a c * Q d a = (1 : Matrix (Fin n) (Fin n) ℂ) d c := fun d => by
    rw [← hQP, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  simp [hd, Matrix.one_apply]

private lemma conj_pow_of_mul_eq_one' {A : Type} [Ring A] [Algebra ℂ A] (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (X : Matrix (Fin n) (Fin n) A) (m : ℕ) :
    (P.map (algebraMap ℂ A) * X * Q.map (algebraMap ℂ A)) ^ m =
      P.map (algebraMap ℂ A) * X ^ m * Q.map (algebraMap ℂ A) := by
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  have h1 : Q.map (algebraMap ℂ A) * P.map (algebraMap ℂ A) = 1 := by
    rw [← Matrix.map_mul, hQP]
    simp
  have h2 : P.map (algebraMap ℂ A) * Q.map (algebraMap ℂ A) = 1 := by
    rw [← Matrix.map_mul, hPQ]
    simp
  induction m with
  | zero => rw [pow_zero, pow_zero, mul_one, h2]
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc (Q.map (algebraMap ℂ A)) (P.map (algebraMap ℂ A)), h1, one_mul]

private lemma pow_apply_mul_eq_mul_pow_apply {A : Type} [Ring A] (M N : Matrix (Fin n) (Fin n) A) (R : A)
    (h : ∀ a b, M a b * R = R * N a b) (m : ℕ) :
    ∀ a b, (M ^ m) a b * R = R * (N ^ m) a b := by
  induction m with
  | zero =>
    intro a b
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  | succ m ih =>
    intro a b
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_assoc, h c b, ← mul_assoc ((M ^ m) a c), ih a c, mul_assoc]

lemma trace_pow_comm {A : Type} [Ring A] [Algebra ℂ A] (E : Fin n → Fin n → A) (R : A)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (h : ∀ a b, E a b * R = R * ∑ c, ∑ d, (P a c * Q d b) • E c d) (m : ℕ) :
    (∑ c, (Matrix.of E ^ m) c c) * R = R * ∑ c, (Matrix.of E ^ m) c c := by
  have hN : ∀ a b, Matrix.of E a b * R =
      R * (P.map (algebraMap ℂ A) * Matrix.of E * Q.map (algebraMap ℂ A)) a b := by
    intro a b
    rw [conj_apply_lemma]
    exact h a b
  calc (∑ c, (Matrix.of E ^ m) c c) * R
      = ∑ c, R * ((P.map (algebraMap ℂ A) * Matrix.of E * Q.map (algebraMap ℂ A)) ^ m) c c := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => pow_apply_mul_eq_mul_pow_apply _ _ R hN m c c
    _ = R * ∑ c, (Matrix.of E ^ m) c c := by
        rw [← Finset.mul_sum, conj_pow_of_mul_eq_one' P Q hQP, sum_diag_conj_eq_sum_diag P Q hQP]

lemma inv_mul_of_UJ {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k) :
    Jm ε * kᴴ * Jm ε * k = 1 := by
  unfold inUJ at hk
  rw [Matrix.mul_assoc (Jm ε * kᴴ), Matrix.mul_assoc (Jm ε), ← Matrix.mul_assoc kᴴ, hk,
    Formalism.REAL.Jm_mul_self]

lemma Rd_right (X k g : Matrix (Fin n) (Fin n) ℂ) (hk : IsUnit k) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Rd X (fun x => f (x * k)) g = Rd (k⁻¹ * X * k) f (g * k) := by
  have hd : IsUnit k.det := (Matrix.isUnit_iff_isUnit_det k).mp hk
  simp only [Rd]
  congr 1
  funext t
  congr 1
  rw [show ((t : ℂ) • (k⁻¹ * X * k)) = k⁻¹ * ((t : ℂ) • X) * k by
    rw [Matrix.mul_smul, Matrix.smul_mul], Matrix.exp_conj' k _ hk]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc g k k⁻¹, Matrix.mul_nonsing_inv k hd, Matrix.mul_one]

private lemma isUnit_of_inUJ_flag_measures {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k) :
    IsUnit k :=
  (Matrix.isUnit_iff_isUnit_det k).mpr (Matrix.isUnit_det_of_left_inverse (inv_mul_of_UJ hk))

private lemma Jm_conjTranspose_conj_of_inUJ {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    (Z : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (k⁻¹ * Z * k)ᴴ * Jm ε = k⁻¹ * (Jm ε * Zᴴ * Jm ε) * k := by
  have hinv : k⁻¹ = Jm ε * kᴴ * Jm ε := Matrix.inv_eq_left_inv (inv_mul_of_UJ hk)
  have hL : Jm ε * kᴴ = k⁻¹ * Jm ε := by
    rw [hinv]
    simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
  have hR : (k⁻¹)ᴴ * Jm ε = Jm ε * k := by
    rw [hinv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Formalism.REAL.Jm_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [hR, ← Matrix.mul_assoc (Jm ε) kᴴ, hL]
  simp only [Matrix.mul_assoc]

private lemma cpart1_conj_of_inUJ {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    (Z : Matrix (Fin n) (Fin n) ℂ) : cpart1 ε (k⁻¹ * Z * k) = k⁻¹ * cpart1 ε Z * k := by
  rw [cpart1, cpart1, Jm_conjTranspose_conj_of_inUJ hk, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_smul,
    Matrix.smul_mul]

private lemma cpart2_conj_of_inUJ {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    (Z : Matrix (Fin n) (Fin n) ℂ) : cpart2 ε (k⁻¹ * Z * k) = k⁻¹ * cpart2 ε Z * k := by
  rw [cpart2, cpart2, Jm_conjTranspose_conj_of_inUJ hk, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.mul_smul,
    Matrix.smul_mul]

lemma Ec_right {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    (Z g : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Ec ε Z (fun x => f (x * k)) g = Ec ε (k⁻¹ * Z * k) f (g * k) := by
  have hu := isUnit_of_inUJ_flag_measures hk
  simp only [Ec]
  rw [Rd_right _ _ _ hu f, Rd_right _ _ _ hu f, cpart1_conj_of_inUJ hk, cpart2_conj_of_inUJ hk]

private lemma inUJ_mul_flag_measures' {ε : Fin n → Bool} {g k : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (hk : inUJ ε k) : inUJ ε (g * k) := by
  unfold inUJ at *
  rw [Matrix.conjTranspose_mul]
  calc kᴴ * gᴴ * Jm ε * (g * k) = kᴴ * (gᴴ * Jm ε * g) * k := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg, hk]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
lemma smooth_right {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) : SmoothOnG ε (fun x => f (x * k)) := by
  have hc : ContDiff ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x * k) :=
    (LinearMap.mulRight ℝ k).toContinuousLinearMap.contDiff
  unfold SmoothOnG at hf ⊢
  intro g₀ hg₀
  obtain ⟨U, F, hU, hmem, hF, hfF⟩ := hf (g₀ * k) (inUJ_mul_flag_measures' hg₀ hk)
  exact ⟨(fun x => x * k) ⁻¹' U, fun x => F (x * k), hU.preimage hc.continuous, hmem,
    hF.comp hc.contDiffOn (fun _ hx => hx), fun g hg hgJ => hfF (g * k) hg (inUJ_mul_flag_measures' hgJ hk)⟩


open GlobalTheory.CapelliCentral in
def rightEnd {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k) :
    Module.End ℂ (smoothSpace ε ℂ) where
  toFun F := mk (fun x => F.1 (x * k)) (smooth_right hk F.2.1)
  map_add' F F' := by
    apply ext_on
    intro g hg
    exact (mk_apply _ (smooth_right hk (F + F').2.1) hg).trans
      (congrArg₂ (· + ·) (mk_apply _ (smooth_right hk F.2.1) hg).symm
        (mk_apply _ (smooth_right hk F'.2.1) hg).symm)
  map_smul' c F := by
    apply ext_on
    intro g hg
    exact (mk_apply _ (smooth_right hk (c • F).2.1) hg).trans
      (congrArg (c • ·) (mk_apply _ (smooth_right hk F.2.1) hg).symm)

open GlobalTheory.CapelliCentral in
lemma rightEnd_apply {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    (F : smoothSpace ε ℂ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    (rightEnd hk F).1 g = F.1 (g * k) := by
  simp only [rightEnd, LinearMap.coe_mk, AddHom.coe_mk]
  exact mk_apply _ _ hg

private lemma Ec_eq_EcV (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : Ec ε Z f g = EcV ε Z f g := by
  simp only [Ec, EcV, rdV_eq, smul_eq_mul]

private lemma mul_single_mul_apply' (M N : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    (M * Matrix.single a b (1 : ℂ) * N : Matrix (Fin n) (Fin n) ℂ) c d = M c a * N b d := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

open GlobalTheory.CapelliCentral in
lemma eabEnd_rightEnd {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k) (a b : Fin n) :
    eabEnd ε ℂ a b * rightEnd hk =
      rightEnd hk * ∑ c, ∑ d, ((k⁻¹)ᵀ a c * kᵀ d b) • eabEnd ε ℂ c d := by
  apply LinearMap.ext
  intro F
  apply ext_on
  intro g hg
  have hgk : inUJ ε (g * k) := inUJ_mul_flag_measures' hg hk
  rw [Module.End.mul_apply, Module.End.mul_apply, rightEnd_apply hk _ hg,
    eabEnd_apply (f := fun x => F.1 (x * k)) a b (rightEnd hk F) (fun x hx => rightEnd_apply hk F hx) hg,
    eabV_eq, Eab, Ec_right hk _ g F.1, Ec_eq_EcV, ecSumV n ε ℂ F.1 _ (g * k) F.2.1 hgk]
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
    Submodule.coe_smul, Pi.smul_apply, eabEnd_apply (f := F.1) _ _ F (fun _ _ => rfl) hgk,
    mul_single_mul_apply', Matrix.transpose_apply]

theorem gelf_right : ∀ (n : ℕ) (ε : Fin n → Bool) (m : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (k g : Matrix (Fin n) (Fin n) ℂ), SmoothOnG ε f → k ∈ UJset ε → g ∈ UJset ε →
    gelf ε m (fun x => f (x * k)) g = gelf ε m f (g * k) := by
  intro n ε m f k g hf hk hg
  have hkU : inUJ ε k := hk
  have hgU : inUJ ε g := hg
  have hd : IsUnit k.det := (Matrix.isUnit_iff_isUnit_det k).mp (isUnit_of_inUJ_flag_measures hkU)
  have hQP : kᵀ * (k⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul k hd, Matrix.transpose_one]
  have hfV : SmoothOnGV ε f := (smoothOnGV_iff ε f).mpr hf
  let F : GlobalTheory.CapelliCentral.smoothSpace ε ℂ := GlobalTheory.CapelliCentral.mk f hfV
  have hFf : ∀ x, inUJ ε x → F.1 x = f x := fun x hx => GlobalTheory.CapelliCentral.mk_apply f hfV hx
  have hcomm := trace_pow_comm (GlobalTheory.CapelliCentral.eabEnd ε ℂ) (rightEnd hkU) (k⁻¹)ᵀ kᵀ hQP
    (eabEnd_rightEnd hkU) (m + 1)
  have h1 := congrArg (fun T : Module.End ℂ (GlobalTheory.CapelliCentral.smoothSpace ε ℂ) => (T F).1 g) hcomm
  simp only [Module.End.mul_apply] at h1
  rw [GlobalTheory.Dec.FormF.gelf_apply (f := fun x => f (x * k)) m (rightEnd hkU F)
      (fun x hx => (rightEnd_apply hkU F hx).trans (hFf _ (inUJ_mul_flag_measures' hx hkU))) hgU,
    rightEnd_apply hkU _ hgU,
    GlobalTheory.Dec.FormF.gelf_apply m F hFf (inUJ_mul_flag_measures' hgU hkU)] at h1
  exact h1

end GlobalTheory.Dec.GelfAd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslationStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandInvariant_comm_rightTranslation : ∀ (n : ℕ) (ε : Fin n → Bool) (m : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (k g : Matrix (Fin n) (Fin n) ℂ), SmoothOnG ε f → k ∈ UJset ε → g ∈ UJset ε → gelf ε m (fun x => f (x * k)) g = gelf ε m f (g * k) := by
  first | exact @GlobalTheory.Dec.GelfAd.gelf_right | exact GlobalTheory.Dec.GelfAd.gelf_right | (intros; apply GlobalTheory.Dec.GelfAd.gelf_right <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
open MeasureTheory NumberField Matrix Finset
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StabUnfold

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

structure Sib (I : AutInst) where
  n : ℕ
  J : Matrix (Fin n) (Fin n) I.E
  J_herm : Formalism.UG.IsHerm (starRingEnd I.E) J
  J_det : J.det ≠ 0
  L : Submodule (𝓞 I.E) (Fin n → I.E)
  L_span : Submodule.span I.E (L : Set (Fin n → I.E)) = ⊤
  L_fg : L.FG
  L_dual : ∀ x : Fin n → I.E, x ∈ L ↔
    ∀ y ∈ L, Formalism.UG.hform (starRingEnd I.E) J y x ∈ (algebraMap (𝓞 I.E) I.E).range
  ε : InfinitePlace I.F → Fin n → Bool
  P : InfinitePlace I.F → Matrix (Fin n) (Fin n) ℂ
  P_unit : ∀ v, IsUnit (P v)
  P_spec : ∀ v, (P v)ᴴ * J.map (I.φ v) * P v = Formalism.REAL.Jm (ε v)

variable {I : AutInst}

def Sib.frames (D : Sib I) : AutInst :=
  GlobalTheory.AutInhab.ofFrames I.cm D.n D.J D.J_herm D.J_det D.L D.L_span D.L_fg D.L_dual D.ε I.φ I.φ_over D.P
    D.P_unit D.P_spec

@[reducible] def Sib.inst (D : Sib I) : AutInst where
  F := I.F
  E := I.E
  cm := I.cm
  n := D.n
  J := D.J
  J_herm := D.J_herm
  J_det := D.J_det
  L := D.L
  L_span := D.L_span
  L_fg := D.L_fg
  L_dual := D.L_dual
  ε := D.ε
  φ := I.φ
  φ_over := I.φ_over
  P := D.P
  P_unit := D.P_unit
  P_spec := D.P_spec
  topf := D.frames.topf
  topf_group := D.frames.topf_group
  topf_open := D.frames.topf_open
  topf_basis := D.frames.topf_basis

instance (D : Sib I) : TopologicalSpace D.inst.Gf := D.inst.topf
instance (D : Sib I) : IsTopologicalGroup D.inst.Gf := D.inst.topf_group
instance (D : Sib I) : MeasurableSpace D.inst.Gf := AutInst.instMeasurableSpaceGf D.inst
instance (D : Sib I) : BorelSpace D.inst.Gf := AutInst.instBorelSpaceGf D.inst

def IsPerp (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf) : Prop :=
  D.n + 1 = I.n ∧ star x ⬝ᵥ (I.J *ᵥ x) = sgn I.E s ∧ star x ᵥ* (I.J * A) = 0 ∧ Aᴴ * I.J * A = D.J ∧
    x ∈ lamX I (1, xf) ∧ ∀ y : Fin D.n → I.E, y ∈ D.L ↔ A *ᵥ y ∈ lamX I (1, xf)

def afVec (I : AutInst) {m : ℕ} (x : Fin m → I.E) : Fin m → I.E ⊗[I.F] Af I.F :=
  fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)

def afMat (I : AutInst) {m k : ℕ} (A : Matrix (Fin m) (Fin k) I.E) : Matrix (Fin m) (Fin k) (I.E ⊗[I.F] Af I.F) :=
  A.map (Formalism.UG.inclE (F := I.F) (Af I.F))

def infVec (I : AutInst) (v : InfinitePlace I.F) (x : Fin I.n → I.E) : Fin I.n → ℂ :=
  (I.P v)⁻¹ *ᵥ fun i => I.φ v (x i)

def infMat (D : Sib I) (v : InfinitePlace I.F) (A : Matrix (Fin I.n) (Fin D.n) I.E) :
    Matrix (Fin I.n) (Fin D.n) ℂ :=
  (I.P v)⁻¹ * A.map (I.φ v) * D.P v

def IsFinEmb (D : Sib I) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (jf : D.inst.Gf →* I.Gf) :
    Prop :=
  ∀ g, I.fmat (jf g) *ᵥ afVec I x = afVec I x ∧ I.fmat (jf g) * afMat I A = afMat I A * D.inst.fmat g

def IsInfEmb (D : Sib I) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E)
    (jv : ∀ v, Formalism.REAL.UJ (D.ε v) →* Formalism.REAL.UJ (I.ε v)) : Prop :=
  ∀ v g, uMat (jv v g) *ᵥ infVec I v x = infVec I v x ∧ uMat (jv v g) * infMat D v A = infMat D v A * uMat g

def embA (D : Sib I) (jv : ∀ v, Formalism.REAL.UJ (D.ε v) →* Formalism.REAL.UJ (I.ε v)) (jf : D.inst.Gf →* I.Gf) :
    D.inst.GA →* I.GA where
  toFun g := (fun v => jv v (g.1 v), jf g.2)
  map_one' := by
    refine Prod.ext (funext fun v => ?_) ?_
    · exact map_one (jv v)
    · exact map_one jf
  map_mul' g h := by
    refine Prod.ext (funext fun v => ?_) ?_
    · exact map_mul (jv v) _ _
    · exact map_mul jf _ _

def gaussAt (I : AutInst) (x : Fin I.n → I.E) (g : I.GA) : ENNReal :=
  (∏ v, ENNReal.ofReal (gauss ((uMat (g.1 v))⁻¹ *ᵥ infVec I v x))) *
    {h : I.Gf | x ∈ lamX I (1, h)}.indicator 1 g.2

def stabF (I : AutInst) (x : Fin I.n → I.E) : Set I.GA :=
  {γ | γ ∈ I.GFset ∧ I.fmat γ.2 *ᵥ afVec I x = afVec I x}

def Ksub (I : AutInst) : Subgroup I.Gf :=
  (Formalism.UG.stabGL I.Lf).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype

end GlobalTheory.StabUnfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtPBijective
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegVol.RefCov

def crd (k r j : ℕ) (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r j) : Mat k r :=
  pTop k r j q.2 * uEmb k r (upperIn β q.1)

abbrev Crd (ι : Type) (k r j : ℕ) (β : Fin r → ℕ) :=
  (UTin β → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) ×
    (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))

def atP {ι : Type} {k r j : ℕ} {β : Fin r → ℕ} (p : Crd ι k r j β) (v : ι) : (UTin β → ℂ) × PTop k r j :=
  (fun i => p.1 i v, fun a => p.2.1 a v, fun s => p.2.2.1 s v, fun a => p.2.2.2 a v)

def CC {ι : Type} {k r j : ℕ} {β : Fin r → ℕ} (p : Crd ι k r j β) : ι → Mat k r := fun v => crd k r j β (atP p v)

theorem usage₂ {ι : Type} {k r j : ℕ} {β : Fin r → ℕ} :
    Function.Bijective (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun q => (fun i v => (q v).1 i, fun a v => (q v).2.1 a,
    fun s v => (q v).2.2.1 s, fun a v => (q v).2.2.2 a), fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.DegVol.RefCov
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetDetNormPos
open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.MeanDual

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def invT (g : MatInf E j) : MatInf E j := fun w a b => (Matrix.of (g w))⁻¹ b a

def trDual (Λ : Submodule (𝓞 E) (Fin j → E)) : Submodule (𝓞 E) (Fin j → E) where
  carrier := {y | ∀ x ∈ Λ, ∃ z : ℤ, Algebra.trace ℚ E (x ⬝ᵥ y) = 2 * (z : ℚ)}
  add_mem' := by
    intro a b ha hb x hx
    obtain ⟨z, hz⟩ := ha x hx
    obtain ⟨z', hz'⟩ := hb x hx
    exact ⟨z + z', by rw [dotProduct_add, map_add (f := _), hz, hz']; push_cast; ring⟩
  zero_mem' := fun x _ => ⟨0, by simp⟩
  smul_mem' := by
    intro c y hy x hx
    obtain ⟨z, hz⟩ := hy (c • x) (Λ.smul_mem c hx)
    refine ⟨z, ?_⟩
    rw [← hz, dotProduct_smul, smul_dotProduct]

theorem mem_trDual {Λ : Submodule (𝓞 E) (Fin j → E)} {y : Fin j → E} :
    y ∈ trDual E j Λ ↔ ∀ x ∈ Λ, ∃ z : ℤ, Algebra.trace ℚ E (x ⬝ᵥ y) = 2 * (z : ℚ) := Iff.rfl

theorem of_invT (g : MatInf E j) (w : InfinitePlace E) :
    Matrix.of (invT E j g w) = ((Matrix.of (g w))⁻¹)ᵀ := rfl

theorem of_mul (g h : MatInf E j) (w : InfinitePlace E) :
    Matrix.of ((g * h) w) = Matrix.of (g w) * Matrix.of (h w) := rfl

theorem matInf_ext {g h : MatInf E j} (H : ∀ w, Matrix.of (g w) = Matrix.of (h w)) : g = h :=
  funext fun w => Matrix.of.injective (H w)

theorem detNorm_pos_iff (g : MatInf E j) :
    0 < detNorm E j g ↔ ∀ w, (Matrix.of (g w)).det ≠ 0 := by
  unfold detNorm
  constructor
  · intro h w hw
    rw [Finset.prod_eq_zero (Finset.mem_univ w) (by simp [hw])] at h
    exact lt_irrefl _ h
  · intro h
    exact Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (h w)) 2

theorem invT_mul (g h : MatInf E j) : invT E j (g * h) = invT E j g * invT E j h := by
  apply matInf_ext
  intro w
  rw [of_invT, of_mul, of_mul, of_invT, of_invT, Matrix.mul_inv_rev, Matrix.transpose_mul]

theorem detNorm_invT_pos_iff (g : MatInf E j) :
    0 < detNorm E j (invT E j g) ↔ 0 < detNorm E j g := by
  simp only [detNorm_pos_iff, of_invT, Matrix.det_transpose, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv', ne_eq, inv_eq_zero]

theorem invT_invT {g : MatInf E j} (hg : 0 < detNorm E j g) : invT E j (invT E j g) = g := by
  apply matInf_ext
  intro w
  rw [of_invT, of_invT, ← Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 ((detNorm_pos_iff E j g).1 hg w))]

theorem detNorm_mul (g h : MatInf E j) : detNorm E j (g * h) = detNorm E j g * detNorm E j h := by
  unfold detNorm
  simp only [of_mul, Matrix.det_mul, norm_mul, mul_pow, Finset.prod_mul_distrib]

theorem continuous_detNorm :
    Continuous (fun g : InfinitePlace E → Fin j → Fin j → ℂ => detNorm E j g) := by
  unfold detNorm
  refine continuous_finsetProd _ fun w _ => ?_
  refine Continuous.pow (Continuous.norm ?_) 2
  exact Continuous.matrix_det (A := fun g : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (g w))
    (continuous_apply w)

theorem measurableSet_detNorm_pos : MeasurableSet {g : MatInf E j | 0 < detNorm E j g} :=
  (isOpen_lt continuous_const (continuous_detNorm E j)).measurableSet

end GlobalTheory.MeanDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsQuotMeas
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgQuot

theorem isMatGroup_GG (k r : ℕ) : PI.IsMatGroup (GG k r) := by

  have hH : IsUnit (Formalism.QuantumDeterminants.Hpk k r).det := by
    have h := congrArg Matrix.det (Formalism.QuantumDeterminants.hpkFacts k r).2.1
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact ⟨⟨_, _, h, (mul_comm _ _).trans h⟩, rfl⟩
  obtain ⟨h1, hmul, hinv⟩ := Formalism.QuantumDeterminants.uHGroup _ _ hH
  refine ⟨?_, h1, hmul, fun a ha => ⟨(hinv a ha).2, Matrix.mul_nonsing_inv a (hinv a ha).1⟩⟩

  show IsClosed {g : Mat k r | gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

theorem exists_isQuotMeas : ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS : Measure (Mt k r)), IsClosedSub k r S →
    IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS → ∃ ν : Measure (Mt k r), IsQuotMeas μG μS ν := by
  intro k r S μG μS hS hG hSμ hU
  obtain ⟨hSG, hcl, h1, hmul, hinv⟩ := hS

  have hSm : PI.IsMatGroup S :=
    ⟨hcl, h1, hmul, fun a ha => ⟨hinv a ha, ((isMatGroup_GG k r).2.2.2 a (hSG ha)).2⟩⟩

  exact GlobalTheory.QuotWeil.exists_isQuotM (2 * r + k + 1) (GG k r) S μG μS (isMatGroup_GG k r) hSm hSG hG hSμ hU.1

end GlobalTheory.SgQuot
end

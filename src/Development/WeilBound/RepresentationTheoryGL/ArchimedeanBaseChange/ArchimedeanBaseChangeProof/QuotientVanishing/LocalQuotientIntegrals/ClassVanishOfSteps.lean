module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PClassVanish
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.CVEmbInfSelf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.T2SpaceAdelicGLCmField
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PCutInt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PAdTop
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB

namespace PositivityTheory.Rg.BcB.CV.AdelicTopology

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem ratCent_subset_range (d : GL (Fin n) E) :
    (ratCent d : Set (GA E n)) ⊆ ((ratGL E n).range : Set (GA E n)) := by
  rintro _ ⟨g, -, rfl⟩
  exact ⟨g, rfl⟩

theorem discrete_ratCent (d : GL (Fin n) E) : DiscreteTopology (ratCent d) :=
  DiscreteTopology.of_subset (s := ((ratGL E n).range : Set (GA E n)))
    GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (ratCent_subset_range d)

theorem countable_ratCent (d : GL (Fin n) E) : Countable (ratCent d) := by
  have := GlobalTheory.CompanionTheory.UnfoldCut.countable_GL (E := E) (n := n)
  have h : (ratCent d : Set (GA E n)).Countable :=
    (Set.countable_range (ratGL E n)).mono fun _ hx => by
      obtain ⟨g, hg⟩ := ratCent_subset_range d hx
      exact ⟨g, hg⟩
  exact h.to_subtype

end PositivityTheory.Rg.BcB.CV.AdelicTopology

theorem PositivityTheory.Rg.BcB.CV.pf_AdTop : PositivityTheory.Rg.BcB.DegBdd → PositivityTheory.Rg.BcB.D4.RatDisc → PositivityTheory.Rg.BcB.CV.AdTop := by
  intro hD _ E _ _ _ n
  haveI : T2Space (GA E n) := GlobalTheory.CompanionTheory.UnfoldCut.t2Space_adelicGL_cmField (E := E) (n := n)
  haveI : T1Space (GA E n) := T2Space.t1Space
  refine ⟨GlobalTheory.CompanionTheory.UnfoldCut.locallyCompact_GA, inferInstance, GlobalTheory.CompanionTheory.UnfoldCut.secondCountable_GA,
    GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA, fun W => ?_, fun d => ?_⟩
  · let _ : MeasurableSpace (GA E n) := borel _
    have : BorelSpace (GA E n) := ⟨rfl⟩
    exact ((hD E n).2 W).measurable
  · have := PositivityTheory.Rg.BcB.CV.AdelicTopology.discrete_ratCent d
    exact ⟨Subgroup.isClosed_of_discrete, inferInstance, PositivityTheory.Rg.BcB.CV.AdelicTopology.countable_ratCent d⟩
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PLocTor
noncomputable section

open Matrix PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.LocalTorus

theorem comm (n : ℕ) (d : GL (Fin n) ℂ) (hs : (d * thC n d).val.charpoly.Separable)
    (s : GL (Fin n) ℂ) (hs' : s ∈ twCent (thC n) d) (t : GL (Fin n) ℂ) (ht : t ∈ twCent (thC n) d) :
    s * t = t * s := by
  have hθθ : ∀ g : GL (Fin n) ℂ, thC n (thC n g) = g := by
    intro g
    apply Units.ext
    show ((((thC n g)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ = (g : Matrix (Fin n) (Fin n) ℂ)
    have e : (((thC n g)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        ((g : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ := rfl
    rw [e]
    ext i j
    simp [Matrix.map_apply, Matrix.transpose_apply]
  have key : ∀ x ∈ twCent (thC n) d,
      Commute ((d * thC n d : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (x : Matrix (Fin n) (Fin n) ℂ) := by
    intro x hx
    have h1 : x⁻¹ * d * thC n x = d := hx
    have h2 : d * thC n x = x * d := by
      calc d * thC n x = x * (x⁻¹ * d * thC n x) := by group
        _ = x * d := by rw [h1]
    have h3 : thC n d * x = thC n x * thC n d := by
      have h4 := congrArg (thC n) h2
      rw [map_mul, map_mul, hθθ] at h4
      exact h4
    apply Commute.units_val
    show (d * thC n d) * x = x * (d * thC n d)
    rw [mul_assoc, h3, ← mul_assoc, h2, mul_assoc]
  have hc := GlobalTheory.BCT.CentComm.commute_of_commute_separable hs (key s hs') (key t ht)
  exact Units.ext (by simpa using hc.eq)

end PositivityTheory.Rg.BcB.CV.LocalTorus

theorem PositivityTheory.Rg.BcB.CV.pf_LocTor : PositivityTheory.Rg.BcB.CV.LocTor := by
  intro n d hs
  exact ⟨GlobalTheory.CompanionTheory.LocVan.isClosed_twCent d, PositivityTheory.Rg.BcB.CV.LocalTorus.comm n d hs,
    GlobalTheory.CompanionTheory.LocVan.continuous_thC, GlobalTheory.CompanionTheory.LocVan.locallyCompact_GL n, GlobalTheory.CompanionTheory.LocVan.secondCountable_GL n⟩

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.EnormOfRealToRealLe
noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace PositivityTheory.Rg.BcB.CV

namespace QuotientIntegral

theorem enorm_ofReal_toReal_le' (r : ℝ≥0∞) : ‖((r.toReal : ℝ) : ℂ)‖ₑ ≤ r := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

theorem integrable_mul {G : Type*} [MeasurableSpace G] {μ : Measure G} {F : G → ℂ}
    {ρ : G → ℝ≥0∞} (hF : Measurable F) (hρ : Measurable ρ) (h : ∫⁻ g, ‖F g‖ₑ * ρ g ∂μ ≠ ⊤) :
    Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μ := by
  refine ⟨(hF.mul (Complex.measurable_ofReal.comp hρ.ennreal_toReal)).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun g => ?_) h.lt_top
  rw [enorm_mul]
  gcongr
  exact enorm_ofReal_toReal_le' _

end QuotientIntegral

theorem pf_QAdd : QAdd := by
  intro G _ _ μ T ν
  classical
  by_cases hex : ∃ ρ, IsQuotNormaliser T ν ρ
  · have hL : ∀ F : G → ℂ, quotLIntegral μ T ν (fun x => ‖F x‖ₑ) =
        ∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ := fun F => by rw [quotLIntegral, dite_eq_left hex]
    have hI : ∀ F : G → ℂ, quotIntegral μ T ν F =
        ∫ g, F g * ((hex.choose g).toReal : ℂ) ∂μ := fun F => by rw [quotIntegral, dite_eq_left hex]
    have hint : ∀ F : G → ℂ, Measurable F → quotLIntegral μ T ν (fun x => ‖F x‖ₑ) ≠ ⊤ →
        Integrable (fun g => F g * ((hex.choose g).toReal : ℂ)) μ := fun F hF h =>
      QuotientIntegral.integrable_mul hF hex.choose_spec.1 (by rwa [hL] at h)
    refine ⟨fun ι s F hF => ?_, fun F F' hF hF' h h' => ?_, fun c F => ?_⟩
    · simp only [hI, Finset.sum_mul]
      exact integral_finsetSum s fun i hi => hint _ (hF i hi).1 (hF i hi).2
    · simp only [hI, sub_mul]
      exact integral_sub (hint _ hF h) (hint _ hF' h')
    · simp only [hI, mul_assoc]
      exact integral_const_mul c _
  · refine ⟨fun _ _ _ _ => ?_, fun _ _ _ _ _ _ => ?_, fun _ _ => ?_⟩ <;>
      simp [quotIntegral, hex]

end PositivityTheory.Rg.BcB.CV
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PFamAt
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.FamilyAtPlace

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

theorem emb_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (v : InfinitePlace E) (x : E) :
    v.embedding (conjE E x) = starRingEnd ℂ (v.embedding x) :=
  IsCMField.complexEmbedding_complexConj E v.embedding x

theorem locGL_theta {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (v : InfinitePlace E)
    (d : GL (Fin n) E) : locGL v (thetaE E n d) = thC n (locGL v d) := by
  apply Units.ext
  have h1 : (locGL v (thetaE E n d)).val = ((thetaR (conjE E) n d).val).map v.embedding := rfl
  have h2 : (locGL v d⁻¹).val = (d⁻¹ : GL (Fin n) E).val.map v.embedding := rfl
  rw [h1, thetaR_val, thetaR_val, ← map_inv, h2]
  ext i j
  simp [emb_conj]

theorem locGL_nrm {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (v : InfinitePlace E)
    (d : GL (Fin n) E) : locGL v (nrm d) = locGL v d * thC n (locGL v d) := by
  rw [nrm, map_mul, locGL_theta]

theorem perp_anti {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {W W' : Submodule K (Fin n → K)} (h : W ≤ W') :
    perp σ W' ≤ perp σ W := fun _ hy x hx => hy x (h hx)

theorem perpD_anti {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (d : GL (Fin n) K) {W W' : Submodule K (Fin n → K)}
    (h : W ≤ W') : perpD σ d W' ≤ perpD σ d W :=
  Submodule.map_mono (perp_anti σ h)

end PositivityTheory.Rg.BcB.CV.FamilyAtPlace

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV.FamilyAtPlace in
theorem PositivityTheory.Rg.BcB.CV.pf_FamAt : PositivityTheory.Rg.BcB.D4.LocFlag → PositivityTheory.Rg.BcB.CV.Ploc → PositivityTheory.Rg.BcB.CV.FamAt := by
  intro hLF hP E _ _ _ n m d Wof a V v hPar hV hemb
  refine ⟨?_, ?_⟩
  · rw [← locGL_nrm]
    have : (locGL v (nrm d)).val = (nrm d).val.map v.embedding := rfl
    rw [this, Matrix.charpoly_map]
    exact hPar.reg.map
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact continuous_pi fun e => (hP E n v (Wof e)).2.1
    · intro x
      exact ((hP E n v (Wof 0)).2.2.2.1 hPar.zero).1 x
    · intro x k hk
      funext e
      exact (hP E n v (Wof e)).2.2.1 x k hk
    · intro t ht x z
      have hs := hemb t ht
      have key : ∀ e, pAt Wof v (t * x) e = pAt Wof v x e - sdot e (a (embInf n v t)) := by
        intro e
        have h1 := (hP E n v (Wof e)).2.2.2.2.2.2.2 t (embInf n v x)
        rw [(hP E n v (Wof e)).2.2.2.2.1 x, hPar.degT _ hs] at h1
        simp only [pAt]
        linarith
      have : pAt Wof v (t * x) + z = fun e => (pAt Wof v x + z) e - sdot e (a (embInf n v t)) := by
        funext e
        simp only [Pi.add_apply, key]
        ring
      rw [this, hV _ hs]
    · intro e he
      have hW : Wof e ≠ ⊥ := by
        intro h
        obtain ⟨e0, _, hu⟩ := hPar.uniq ⊥ (hPar.zero ▸ hPar.iso 0)
        exact he ((hu e h).trans (hu 0 hPar.zero).symm)
      obtain ⟨h1, h2, h3, h4, h5⟩ := hLF E n d (Wof e) v (hPar.iso e) hW (hPar.perp e)
      refine ⟨_, _, ⟨h1, h2, h3, h4⟩, ?_⟩
      intro u hu x e' he'
      have hW' : Wof e' ≤ Wof e ∨ (Wof e ≤ Wof e' ∧ Wof e' ≤ perpD (conjE E) d (Wof e)) := by
        rcases he' with h | h
        · exact Or.inr ⟨hPar.mono _ _ h, (hPar.iso e').2.trans (perpD_anti _ _ (hPar.mono _ _ h))⟩
        · exact Or.inl (hPar.mono _ _ h)
      have c1 := (hP E n v (Wof e')).1 (embInf n v u * embInf n v x)
      have c2 := (hP E n v (Wof e')).1 (embInf n v x)
      rw [map_mul, (hP E n v (Wof e')).2.2.2.2.1 u, (hP E n v (Wof e')).2.2.2.2.1 x] at c1
      rw [(hP E n v (Wof e')).2.2.2.2.1 x] at c2
      simp only [pAt]
      rw [← c1, ← c2]
      exact h5 (embInf n v x) u hu (Wof e') hW'
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PTwoVanish
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open scoped Pointwise

namespace PositivityTheory.Rg.BcB.CV.SecondVanishing

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV

theorem hcs_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X × Y → ℂ} (hf : HasCompactSupport f) (g : X) : HasCompactSupport fun y => f (g, y) := by
  refine HasCompactSupport.intro (IsCompact.image hf continuous_snd) fun y hy => ?_
  by_contra h
  exact hy ⟨(g, y), subset_tsupport _ (Function.mem_support.2 h), rfl⟩

theorem hcs_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    {f : X × Y → ℂ} (hf : HasCompactSupport f) (g : Y) : HasCompactSupport fun y => f (y, g) := by
  refine HasCompactSupport.intro (IsCompact.image hf continuous_fst) fun y hy => ?_
  by_contra h
  exact hy ⟨(y, g), subset_tsupport _ (Function.mem_support.2 h), rfl⟩

theorem vp_bdd_on {X : Type*} [TopologicalSpace X] {m : ℕ} {V : ((Fin m → SignType) → ℝ) → ℂ} (hV : VP V)
    {q : X → (Fin m → SignType) → ℝ} (hq : Continuous q) {K : Set X} (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ‖V (q x)‖ ≤ B := by
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hq.continuousOn
  obtain ⟨B, hB⟩ := hV.bdd R
  refine ⟨max B 0, le_max_right _ _, fun x hx => (hB (q x) fun e => ?_).trans (le_max_left _ _)⟩
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm (q x) e).trans (hR x hx)

theorem tor2 {n m : ℕ} {d₁ d₂ : GL (Fin n) ℂ} {V : ((Fin m → SignType) → ℝ) → ℂ}
    {p₁ p₂ : GL (Fin n) ℂ → (Fin m → SignType) → ℝ} (h₁ : LocFam d₁ V p₁) (h₂ : LocFam d₂ V p₂)
    {t₁ t₂ : GL (Fin n) ℂ} (ht₁ : t₁ ∈ twCent (thC n) d₁) (ht₂ : t₂ ∈ twCent (thC n) d₂) (x₁ x₂ : GL (Fin n) ℂ)
    (z : (Fin m → SignType) → ℝ) : V (p₁ (t₁ * x₁) + p₂ (t₂ * x₂) + z) = V (p₁ x₁ + p₂ x₂ + z) := by
  rw [add_assoc, h₁.tor t₁ ht₁, add_left_comm (p₁ x₁), h₂.tor t₂ ht₂, add_left_comm (p₂ x₂), ← add_assoc]

end PositivityTheory.Rg.BcB.CV.SecondVanishing

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV PositivityTheory.Rg.BcB.CV.SecondVanishing in
theorem PositivityTheory.Rg.BcB.CV.pf_TwoVanish : PositivityTheory.Rg.BcB.LocVanish → PositivityTheory.Rg.BcB.D4.LocProper → PositivityTheory.Rg.BcB.CV.LocTor → PositivityTheory.Rg.BcB.CV.QInt → PositivityTheory.Rg.BcB.CV.QAdd → PositivityTheory.Rg.BcB.CV.QProd → PositivityTheory.Rg.BcB.CV.OneVanish → PositivityTheory.Rg.BcB.CV.TwoVanish := by
  intro hLV hLP hLT hQI hQA hQP hOV n m _ _ μ _ d₁ d₂ ν _ _ f V p₁ p₂ z hm hd₁ hd₂ hfc hfs hcu₁ hcu₂ hV hF₁ hF₂ hz
  obtain ⟨hcl₁, hcomm₁, hθ, hlc, hsc⟩ := hLT n d₁ hd₁
  obtain ⟨hcl₂, hcomm₂, -, -, -⟩ := hLT n d₂ hd₂
  have := hlc
  have := hsc
  have hc₁ : Continuous fun x => twConj (thC n) x d₁ := by
    show Continuous fun x => x⁻¹ * d₁ * thC n x
    exact (continuous_inv.mul continuous_const).mul hθ
  have hc₂ : Continuous fun x => twConj (thC n) x d₂ := by
    show Continuous fun x => x⁻¹ * d₂ * thC n x
    exact (continuous_inv.mul continuous_const).mul hθ
  have hΦc : Continuous fun x : GL (Fin n) ℂ × GL (Fin n) ℂ => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) :=
    hfc.comp ((hc₁.comp continuous_fst).prodMk (hc₂.comp continuous_snd))
  have hΦinv : ∀ t ∈ (twCent (thC n) d₁).prod (twCent (thC n) d₂), ∀ x : GL (Fin n) ℂ × GL (Fin n) ℂ,
      f (twConj (thC n) (t * x).1 d₁, twConj (thC n) (t * x).2 d₂) = f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) := by
    intro t ht x
    rw [Prod.fst_mul, Prod.snd_mul, twConj_mul_left _ _ (Subgroup.mem_prod.1 ht).1,
      twConj_mul_left _ _ (Subgroup.mem_prod.1 ht).2]
  obtain ⟨C₁, hC₁, hsub₁⟩ := hLP n d₁ hd₁ (Prod.fst '' tsupport f) (IsCompact.image hfs continuous_fst)
  obtain ⟨C₂, hC₂, hsub₂⟩ := hLP n d₂ hd₂ (Prod.snd '' tsupport f) (IsCompact.image hfs continuous_snd)
  obtain ⟨Bf, hBf⟩ := hfc.bounded_above_of_compact_support hfs
  have hBf0 : 0 ≤ Bf := (norm_nonneg _).trans (hBf (1, 1))
  have hclosed : IsClosed (((twCent (thC n) d₁).prod (twCent (thC n) d₂) : Subgroup _) :
      Set (GL (Fin n) ℂ × GL (Fin n) ℂ)) := by
    rw [Subgroup.coe_prod]; exact hcl₁.prod hcl₂
  obtain ⟨A₀, -, hA₀⟩ := hQI (GL (Fin n) ℂ × GL (Fin n) ℂ) (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν
    (C₁ ×ˢ C₂) hclosed (hC₁.prod hC₂)
  have hint : ∀ h : GL (Fin n) ℂ × GL (Fin n) ℂ → ℂ, Measurable h →
      (∀ t ∈ (twCent (thC n) d₁).prod (twCent (thC n) d₂), ∀ x, h (t * x) = h x) →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ C₁ ×ˢ C₂, ‖h x‖ ≤ B) →
      quotLIntegral (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν
        (fun x => ‖f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * h x‖ₑ) ≠ ⊤ := by
    intro h hm hinv ⟨B, hB0, hB⟩
    refine (hA₀ (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * h x) (Bf * B) (mul_nonneg hBf0 hB0)
      (hΦc.measurable.mul hm) (fun t ht x => by rw [hΦinv t ht x, hinv t ht x]) ?_ ?_).1
    · intro x hx
      have hfx : f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) ≠ 0 := left_ne_zero_of_mul hx
      have hts : (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) ∈ tsupport f :=
        subset_tsupport _ (Function.mem_support.2 hfx)
      obtain ⟨a₁, ha₁, b₁, hb₁, e₁⟩ := Set.mem_mul.1 (hsub₁ (show twConj (thC n) x.1 d₁ ∈ Prod.fst '' tsupport f from ⟨_, hts, rfl⟩))
      obtain ⟨a₂, ha₂, b₂, hb₂, e₂⟩ := Set.mem_mul.1 (hsub₂ (show twConj (thC n) x.2 d₂ ∈ Prod.snd '' tsupport f from ⟨_, hts, rfl⟩))
      exact Set.mem_mul.2 ⟨(a₁, a₂), Subgroup.mem_prod.2 ⟨ha₁, ha₂⟩, (b₁, b₂), ⟨hb₁, hb₂⟩, Prod.ext e₁ e₂⟩
    · intro x hx
      rw [norm_mul]
      exact mul_le_mul (hBf _) (hB x hx) (norm_nonneg _) hBf0
  have hq : Continuous fun x : GL (Fin n) ℂ × GL (Fin n) ℂ => p₁ x.1 + p₂ x.2 + z :=
    ((hF₁.cont.comp continuous_fst).add (hF₂.cont.comp continuous_snd)).add continuous_const
  have hq' : Continuous fun x : GL (Fin n) ℂ × GL (Fin n) ℂ => p₁ x.1 := hF₁.cont.comp continuous_fst
  have hmF : Measurable fun x : GL (Fin n) ℂ × GL (Fin n) ℂ => V (p₁ x.1 + p₂ x.2 + z) := hV.meas.comp hq.measurable
  have hmB : Measurable fun x : GL (Fin n) ℂ × GL (Fin n) ℂ => V (p₁ x.1) := hV.meas.comp hq'.measurable
  have hiF : ∀ t ∈ (twCent (thC n) d₁).prod (twCent (thC n) d₂), ∀ x : GL (Fin n) ℂ × GL (Fin n) ℂ,
      V (p₁ (t * x).1 + p₂ (t * x).2 + z) = V (p₁ x.1 + p₂ x.2 + z) := fun t ht x =>
    tor2 hF₁ hF₂ (Subgroup.mem_prod.1 ht).1 (Subgroup.mem_prod.1 ht).2 x.1 x.2 z
  have hiB : ∀ t ∈ (twCent (thC n) d₁).prod (twCent (thC n) d₂), ∀ x : GL (Fin n) ℂ × GL (Fin n) ℂ,
      V (p₁ (t * x).1) = V (p₁ x.1) := fun t ht x => by
    simpa using hF₁.tor t.1 (Subgroup.mem_prod.1 ht).1 x.1 0
  have hIF := hint _ hmF hiF (vp_bdd_on hV hq (hC₁.prod hC₂))
  have hIB := hint _ hmB hiB (vp_bdd_on hV hq' (hC₁.prod hC₂))
  have hsplit := (hQA (GL (Fin n) ℂ × GL (Fin n) ℂ) (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν).2.1
    (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1 + p₂ x.2 + z))
    (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1))
    (hΦc.measurable.mul hmF) (hΦc.measurable.mul hmB) hIF hIB

  have hA : quotIntegral (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν
      (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1 + p₂ x.2 + z) -
        f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1)) = 0 := by
    refine hQP _ _ μ μ _ _ ν _ hcl₁ hcl₂ hcomm₁ hcomm₂
      ((hΦc.measurable.mul hmF).sub (hΦc.measurable.mul hmB))
      (fun t ht x => by simp only [hΦinv t ht x, hiF t ht x, hiB t ht x]) (Or.inl fun ν₁ _ _ x₂ => ?_)
    have h1 := hOV n m μ d₁ ν₁ (fun y => f (y, twConj (thC n) x₂ d₂)) V p₁ (p₂ x₂ + z) hd₁
      (hfc.comp (continuous_id.prodMk continuous_const)) (hcs_right hfs _) (hcu₁ _) hV hF₁
      (by rw [Pi.add_apply, hF₂.zero, hz, add_zero])
    calc _ = quotIntegral μ (twCent (thC n) d₁) ν₁ (fun x => f (twConj (thC n) x d₁, twConj (thC n) x₂ d₂) *
          (V (p₁ x + (p₂ x₂ + z)) - V (p₁ x))) := by
          congr 1; funext x; dsimp only; rw [add_assoc]; ring
      _ = 0 := h1

  have hB : quotIntegral (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν
      (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1)) = 0 := by
    refine hQP _ _ μ μ _ _ ν _ hcl₁ hcl₂ hcomm₁ hcomm₂ (hΦc.measurable.mul hmB)
      (fun t ht x => by simp only [hΦinv t ht x, hiB t ht x]) (Or.inr fun ν₂ _ _ x₁ => ?_)
    have hne : (fun _ : Fin m => (1 : SignType)) ≠ 0 := by
      intro h
      have := congrFun h ⟨0, Nat.pos_of_ne_zero hm⟩
      simp at this
    obtain ⟨W₁, W₂, hW, -⟩ := hF₂.nil _ hne
    have h1 := hLV n μ (fun y => f (twConj (thC n) x₁ d₁, y)) (fun _ => 1) d₂ ν₂ W₁ W₂
      (hfc.comp (continuous_const.prodMk continuous_id)) (hcs_left hfs _) (hcu₂ _) hd₂ hW.1 hW.2.1 hW.2.2.1 hW.2.2.2
      measurable_const (fun _ _ => ⟨1, fun _ _ => by simp⟩) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    calc _ = quotIntegral μ (twCent (thC n) d₂) ν₂ (fun x => V (p₁ x₁) *
          (f (twConj (thC n) x₁ d₁, twConj (thC n) x d₂) * (fun _ => (1 : ℂ)) x)) := by
          congr 1; funext x; dsimp only; ring
      _ = V (p₁ x₁) * quotIntegral μ (twCent (thC n) d₂) ν₂ (fun x =>
          f (twConj (thC n) x₁ d₁, twConj (thC n) x d₂) * (fun _ => (1 : ℂ)) x) := (hQA _ μ _ ν₂).2.2 _ _
      _ = 0 := by rw [h1, mul_zero]
  rw [hA, hB] at hsplit
  linear_combination -hsplit
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.ExistsMeasure
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.Glob1Aux

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

theorem emb_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (v : InfinitePlace E) (x : E) :
    v.embedding (conjE E x) = starRingEnd ℂ (v.embedding x) :=
  IsCMField.complexEmbedding_complexConj E v.embedding x

theorem locGL_theta {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (v : InfinitePlace E)
    (d : GL (Fin n) E) : locGL v (thetaE E n d) = thC n (locGL v d) := by
  apply Units.ext
  have h1 : (locGL v (thetaE E n d)).val = ((thetaR (conjE E) n d).val).map v.embedding := rfl
  have h2 : (locGL v d⁻¹).val = (d⁻¹ : GL (Fin n) E).val.map v.embedding := rfl
  rw [h1, thetaR_val, thetaR_val, ← map_inv, h2]
  ext i j
  simp [emb_conj]

theorem locGL_nrm {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (v : InfinitePlace E)
    (d : GL (Fin n) E) : locGL v (nrm d) = locGL v d * thC n (locGL v d) := by
  rw [nrm, map_mul, locGL_theta]

theorem sep {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (v : InfinitePlace E)
    (d : GL (Fin n) E) (hd : IsRegD d) : (locGL v d * thC n (locGL v d)).val.charpoly.Separable := by
  rw [← locGL_nrm]
  have : (locGL v (nrm d)).val = (nrm d).val.map v.embedding := rfl
  rw [this, Matrix.charpoly_map]
  exact hd.map

theorem exists_measure {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (e : G ≃ₜ* H) (T : Subgroup G) (T' : Subgroup H) (hT : T.map e.toMonoidHom = T') (ν : Measure T)
    [ν.IsHaarMeasure] [ν.IsInvInvariant] : ∃ ν' : Measure T', ν'.IsHaarMeasure ∧ ν'.IsInvInvariant := by
  have h1 : ∀ t : T, e t ∈ T' := fun t => by
    rw [← hT]; exact Subgroup.mem_map_of_mem _ t.2
  have h2 : ∀ s : T', e.symm s ∈ T := fun s => by
    have hs : (s : H) ∈ T.map e.toMonoidHom := by rw [hT]; exact s.2
    obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.1 hs
    rw [← hts]
    show e.symm (e t) ∈ T
    rw [e.symm_apply_apply]
    exact ht
  let f : T ≃ₜ* T' :=
    { toFun := fun t => ⟨e t, h1 t⟩
      invFun := fun s => ⟨e.symm s, h2 s⟩
      left_inv := fun t => Subtype.ext (e.symm_apply_apply t)
      right_inv := fun s => Subtype.ext (e.apply_symm_apply s)
      map_mul' := fun a b => Subtype.ext (map_mul e (a : G) (b : G))
      continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _ }
  refine ⟨ν.map f, inferInstance, ⟨?_⟩⟩
  have hf : Measurable f := f.continuous.measurable
  have hinv : Measurable (fun t : T => t⁻¹) := continuous_inv.measurable
  have hν : Measure.map (fun t : T => t⁻¹) ν = ν := Measure.IsInvInvariant.inv_eq_self
  show Measure.map (fun s : T' => s⁻¹) (Measure.map f ν) = Measure.map f ν
  rw [Measure.map_map continuous_inv.measurable hf]
  conv_rhs => rw [← hν, Measure.map_map hf hinv]
  congr 1
  funext t
  exact (map_inv f t).symm

end PositivityTheory.Rg.BcB.CV.Glob1Aux

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV.Glob1Aux in
theorem PositivityTheory.Rg.BcB.CV.pf_Glob1 : PositivityTheory.Rg.BcB.D4.SplitAt → PositivityTheory.Rg.BcB.D4.NonEllFlag → PositivityTheory.Rg.BcB.LocVanish → PositivityTheory.Rg.BcB.CV.LocTor → PositivityTheory.Rg.BcB.CV.QMap → PositivityTheory.Rg.BcB.CV.QProd → PositivityTheory.Rg.BcB.CV.Ploc → PositivityTheory.Rg.BcB.CV.AdTop → PositivityTheory.Rg.BcB.CV.Glob1 := by
  intro hSA hNEF hLV hLT hQM hQP hPl hAT E _ _ _ n _ _ μ _ d ν _ _ φ hreg hne hcomm hcl hφ hvc
  obtain ⟨v, W₁, W₂, hW0, hW12, hp1, hp2⟩ := hNEF E n d hreg hne
  obtain ⟨G', _, _, _, _, _, _, _, _, _, e, μ₁, μ₂, θ', hμ₁, hμ₂, -, he1, hemb, hθ, hcent⟩ := hSA E n v μ
  have hsep := sep v d hreg
  obtain ⟨hT1c, hT1m, -, hLC, hSC⟩ := hLT n (locGL v d) hsep
  obtain ⟨hLCA, hT2A, hSCA, hθA, -, -⟩ := hAT E n
  have := hLC; have := hSC; have := hLCA; have := hT2A; have := hSCA; have := hμ₁; have := hμ₂
  have : T2Space (GL (Fin n) ℂ × G') := e.symm.toHomeomorph.isEmbedding.t2Space
  have : T2Space (GL (Fin n) ℂ) :=
    T2Space.of_injective_continuous (f := fun g : GL (Fin n) ℂ => (g, (1 : G')))
      (fun a b h => (Prod.ext_iff.1 h).1) (continuous_id.prodMk continuous_const)
  have : T2Space G' :=
    T2Space.of_injective_continuous (f := fun b : G' => ((1 : GL (Fin n) ℂ), b))
      (fun a b h => (Prod.ext_iff.1 h).2) (continuous_const.prodMk continuous_id)
  have he1' : (e (ratGL E n d)).1 = locGL v d := by
    rw [he1]; exact (hPl E n v ⊥).2.2.2.2.2.2.1 d
  have hmem : ∀ p, p ∈ (twCent (thC n) (locGL v d)).prod (twCent θ' (e (ratGL E n d)).2) ↔
      p ∈ e '' (adCent d : Set (GA E n)) := by
    intro p; rw [← hcent d]; exact Iff.rfl
  have hT2c : IsClosed (twCent θ' (e (ratGL E n d)).2 : Set G') := by
    have hc : IsClosed (e '' (adCent d : Set (GA E n))) := e.toHomeomorph.isClosedMap _ hcl
    have : (twCent θ' (e (ratGL E n d)).2 : Set G') =
        (fun b => ((1 : GL (Fin n) ℂ), b)) ⁻¹' (e '' (adCent d : Set (GA E n))) := by
      ext b
      rw [Set.mem_preimage, ← hmem, Subgroup.mem_prod]
      exact ⟨fun h => ⟨Subgroup.one_mem _, h⟩, fun h => h.2⟩
    rw [this]
    exact hc.preimage (continuous_const.prodMk continuous_id)
  have hT2m : ∀ s ∈ twCent θ' (e (ratGL E n d)).2, ∀ t ∈ twCent θ' (e (ratGL E n d)).2, s * t = t * s := by
    intro s hs t ht
    obtain ⟨x, hx, hxs⟩ := (hmem (1, s)).1 (Subgroup.mem_prod.2 ⟨Subgroup.one_mem _, hs⟩)
    obtain ⟨y, hy, hyt⟩ := (hmem (1, t)).1 (Subgroup.mem_prod.2 ⟨Subgroup.one_mem _, ht⟩)
    have h := congrArg (fun p => (e p).2) (hcomm x hx y hy)
    simp only [map_mul, Prod.snd_mul, hxs, hyt] at h
    exact h
  obtain ⟨ν', hν'1, hν'2⟩ := exists_measure e (adCent d) _ (hcent d) ν
  have := hν'1; have := hν'2
  have hFc : Continuous fun x : GA E n => φ (twConj (thetaA E n) x (ratGL E n d)) :=
    hφ.cont.comp ((continuous_inv.mul continuous_const).mul hθA)
  refine hQM (GA E n) (GL (Fin n) ℂ × G') e μ (μ₁.prod μ₂) (adCent d) _ ν ν' _ hcl (hcent d) hFc.measurable
    (fun t ht x => congrArg φ (twConj_mul_left (thetaA E n) (ratGL E n d) ht x)) ?_
  refine hQP (GL (Fin n) ℂ) G' μ₁ μ₂ _ _ ν' _ hT1c hT2c hT1m hT2m (hFc.comp e.symm.continuous).measurable ?_ (Or.inl ?_)
  · intro t ht x
    obtain ⟨s, hs, rfl⟩ := (hmem t).1 ht
    show φ (twConj (thetaA E n) (e.symm (e s * x)) (ratGL E n d)) = φ (twConj (thetaA E n) (e.symm x) (ratGL E n d))
    rw [map_mul, e.symm_apply_apply]
    exact congrArg φ (twConj_mul_left (thetaA E n) (ratGL E n d) hs _)
  · intro ν₁ _ _ x₂
    have key : ∀ x₁ : GL (Fin n) ℂ, twConj (thetaA E n) (e.symm (x₁, x₂)) (ratGL E n d) =
        e.symm (twConj (thC n) x₁ (locGL v d), twConj θ' x₂ (e (ratGL E n d)).2) := by
      intro x₁
      apply e.injective
      rw [e.apply_symm_apply]
      simp only [twConj, map_mul, map_inv, hθ, e.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · simp [he1']
      · simp
    have hf : VeryCusp fun g => φ (e.symm (g, twConj θ' x₂ (e (ratGL E n d)).2)) := by
      have h := hvc v (e.symm (1, twConj θ' x₂ (e (ratGL E n d)).2)) (by rw [← he1, e.apply_symm_apply])
      have : (fun g => φ (e.symm (g, twConj θ' x₂ (e (ratGL E n d)).2))) =
          fun g => φ (embInf n v g * e.symm (1, twConj θ' x₂ (e (ratGL E n d)).2)) := by
        funext g
        have hg : embInf n v g = e.symm (g, 1) := by rw [← hemb g, e.symm_apply_apply]
        rw [hg, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
      rw [this]; exact h
    have hfc : Continuous fun g => φ (e.symm (g, twConj θ' x₂ (e (ratGL E n d)).2)) :=
      hφ.cont.comp (e.symm.continuous.comp (continuous_id.prodMk continuous_const))
    have hfs : HasCompactSupport fun g => φ (e.symm (g, twConj θ' x₂ (e (ratGL E n d)).2)) := by
      have hK : IsCompact (e '' tsupport φ) := hφ.supp.image e.continuous
      refine IsCompact.of_isClosed_subset (hK.image continuous_fst) (isClosed_tsupport _) ?_
      have hcl' : IsClosed {g : GL (Fin n) ℂ | (g, twConj θ' x₂ (e (ratGL E n d)).2) ∈ e '' tsupport φ} :=
        hK.isClosed.preimage (continuous_id.prodMk continuous_const)
      refine (closure_minimal ?_ hcl').trans ?_
      · intro g hg
        exact ⟨_, subset_tsupport _ hg, e.apply_symm_apply _⟩
      · intro g hg
        exact ⟨_, hg, rfl⟩
    have hLV' := hLV n μ₁ _ (fun _ => 1) (locGL v d) ν₁ W₁ W₂ hfc hfs hf hsep hW0 hW12 hp1 hp2 measurable_const
      (fun _ _ => ⟨1, fun _ _ => by simp⟩) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    refine Eq.trans ?_ hLV'
    congr 1
    funext x₁
    show φ (twConj (thetaA E n) (e.symm (x₁, x₂)) (ratGL E n d)) = _
    rw [key, mul_one]
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.IsClosedEmbeddingSlice
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.Glob2Aux

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV

theorem exists_haar_map {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (e : G ≃ₜ* H) (S : Subgroup G) (ν : Measure S) [ν.IsHaarMeasure] [ν.IsInvInvariant] (T : Subgroup H)
    (hT : S.map e.toMonoidHom = T) : ∃ ν' : Measure T, ν'.IsHaarMeasure ∧ ν'.IsInvInvariant := by
  subst hT
  have hinv : ∀ y : S.map e.toMonoidHom, e.symm y ∈ S := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
    rw [← hxy]
    change e.symm (e x) ∈ S
    rw [e.symm_apply_apply]
    exact hx
  let ψ : S ≃ₜ* S.map e.toMonoidHom :=
    { toFun := fun x => ⟨e x, Subgroup.mem_map.2 ⟨x, x.2, rfl⟩⟩
      invFun := fun y => ⟨e.symm y, hinv y⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y)
      map_mul' := fun x y => Subtype.ext (map_mul e (x : G) y)
      continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk hinv }
  refine ⟨ν.map ψ, ContinuousMulEquiv.isHaarMeasure_map ν ψ, ⟨?_⟩⟩
  have hψ : Measurable ψ := ψ.continuous.measurable
  have hi : Measurable (Inv.inv : S → S) := continuous_inv.measurable
  have hi' : Measurable (Inv.inv : S.map e.toMonoidHom → S.map e.toMonoidHom) := continuous_inv.measurable
  show Measure.map Inv.inv (ν.map ψ) = ν.map ψ
  rw [Measure.map_map hi' hψ]
  have : (Inv.inv ∘ ψ) = ψ ∘ Inv.inv := funext fun x => (map_inv ψ x).symm
  rw [this, ← Measure.map_map hψ hi, Measure.map_inv_eq_self]

theorem isClosedEmbedding_slice {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] (c : Y) :
    Topology.IsClosedEmbedding (fun x : X => (x, c)) := by
  refine ⟨isEmbedding_prodMkLeft c, ?_⟩
  have : Set.range (fun x : X => (x, c)) = Set.univ ×ˢ {c} := by
    ext p; constructor
    · rintro ⟨x, rfl⟩; exact ⟨trivial, rfl⟩
    · rintro ⟨-, hp⟩; exact ⟨p.1, Prod.ext rfl (Set.mem_singleton_iff.1 hp).symm⟩
  rw [this]; exact isClosed_univ.prod isClosed_singleton

end PositivityTheory.Rg.BcB.CV.Glob2Aux

namespace PositivityTheory.Rg.BcB.CV

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 Glob2Aux

theorem pf_Glob2 : PositivityTheory.Rg.BcB.D4.SplitAt2 → PositivityTheory.Rg.BcB.CV.LocTor → PositivityTheory.Rg.BcB.CV.QMap → PositivityTheory.Rg.BcB.CV.QProd → PositivityTheory.Rg.BcB.CV.TwoVanish → PositivityTheory.Rg.BcB.CV.Ploc → PositivityTheory.Rg.BcB.CV.FamAt → PositivityTheory.Rg.BcB.CV.AdTop → PositivityTheory.Rg.BcB.CV.Glob2 := by
  intro hS hLT hQM hQP hTV hPl hFA hAT
  intro E _ _ _ _ n m _ _ μ _ d ν _ _ Wof a V τ φ hm hP hV hVa hφ hVC
  obtain ⟨v₁, v₂, hv⟩ := exists_pair_ne (InfinitePlace E)
  obtain ⟨G', iG, iT, iTG, iLC, iSC, iM, iB, iMGL, iBGL, e, μ₁, μ₂, θ', hμ₁, hμ₂, -, he1, hev1, hev2, heθ, hcent⟩ :=
    hS E n v₁ v₂ hv μ
  have := hμ₁
  have := hμ₂
  obtain ⟨hLCA, hT2A, hSCA, hθc, hdegm, -⟩ := hAT E n
  have := hLCA
  have := hT2A
  have := hSCA
  have hmem : ∀ g, g ∈ adCent d ↔ e g ∈ ((twCent (thC n) (locGL v₁ d)).prod (twCent (thC n) (locGL v₂ d))).prod
      (twCent θ' (e (ratGL E n d)).2) := by
    intro g
    rw [← hcent d, Subgroup.mem_map]
    constructor
    · intro h; exact ⟨g, h, rfl⟩
    · rintro ⟨x, hx, hxg⟩
      change e x = e g at hxg
      have : x = g := by rw [← e.symm_apply_apply x, hxg, e.symm_apply_apply]
      rwa [← this]
  have hE1 : ∀ t ∈ twCent (thC n) (locGL v₁ d), embInf n v₁ t ∈ adCent d := fun t ht =>
    (hmem _).2 (by rw [hev1]; exact Subgroup.mem_prod.2 ⟨Subgroup.mem_prod.2 ⟨ht, one_mem _⟩, one_mem _⟩)
  have hE2 : ∀ t ∈ twCent (thC n) (locGL v₂ d), embInf n v₂ t ∈ adCent d := fun t ht =>
    (hmem _).2 (by rw [hev2]; exact Subgroup.mem_prod.2 ⟨Subgroup.mem_prod.2 ⟨one_mem _, ht⟩, one_mem _⟩)
  obtain ⟨hsep₁, hL₁⟩ := hFA E n m d Wof a V v₁ hP hVa hE1
  obtain ⟨hsep₂, hL₂⟩ := hFA E n m d Wof a V v₂ hP hVa hE2
  obtain ⟨hcl₁, hcomm₁, -, hLC, hSC⟩ := hLT n _ hsep₁
  obtain ⟨hcl₂, hcomm₂, -, -, -⟩ := hLT n _ hsep₂
  have := hLC
  have := hSC
  have : T2Space ((GL (Fin n) ℂ × GL (Fin n) ℂ) × G') := e.symm.toHomeomorph.isEmbedding.t2Space
  have : T2Space G' := (isEmbedding_prodMkRight ((1 : GL (Fin n) ℂ × GL (Fin n) ℂ))).t2Space

  have hclP : IsClosed (((twCent (thC n) (locGL v₁ d)).prod (twCent (thC n) (locGL v₂ d)) : Subgroup _) :
      Set (GL (Fin n) ℂ × GL (Fin n) ℂ)) := by
    rw [Subgroup.coe_prod]; exact hcl₁.prod hcl₂
  have hcommP : ∀ s ∈ (twCent (thC n) (locGL v₁ d)).prod (twCent (thC n) (locGL v₂ d)),
      ∀ t ∈ (twCent (thC n) (locGL v₁ d)).prod (twCent (thC n) (locGL v₂ d)), s * t = t * s := by
    intro s hs t ht
    rw [Subgroup.mem_prod] at hs ht
    exact Prod.ext (hcomm₁ _ hs.1 _ ht.1) (hcomm₂ _ hs.2 _ ht.2)
  have hcl3 : IsClosed (twCent θ' (e (ratGL E n d)).2 : Set G') := by
    have hA : IsClosed ((((twCent (thC n) (locGL v₁ d)).prod (twCent (thC n) (locGL v₂ d))).prod
        (twCent θ' (e (ratGL E n d)).2) : Subgroup _) : Set ((GL (Fin n) ℂ × GL (Fin n) ℂ) × G')) := by
      rw [← hcent d, Subgroup.coe_map]
      exact e.toHomeomorph.isClosedMap _ hP.closed
    have h2 := hA.preimage (f := fun g : G' => ((1 : GL (Fin n) ℂ × GL (Fin n) ℂ), g))
      (continuous_const.prodMk continuous_id)
    convert h2 using 1
    ext g
    simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_prod, one_mem, and_self, true_and]
  have hcomm3 : ∀ s ∈ twCent θ' (e (ratGL E n d)).2, ∀ t ∈ twCent θ' (e (ratGL E n d)).2, s * t = t * s := by
    intro s hs t ht
    have hs' : e.symm ((1, 1), s) ∈ adCent d := (hmem _).2 (by
      rw [e.apply_symm_apply]; exact Subgroup.mem_prod.2 ⟨Subgroup.mem_prod.2 ⟨one_mem _, one_mem _⟩, hs⟩)
    have ht' : e.symm ((1, 1), t) ∈ adCent d := (hmem _).2 (by
      rw [e.apply_symm_apply]; exact Subgroup.mem_prod.2 ⟨Subgroup.mem_prod.2 ⟨one_mem _, one_mem _⟩, ht⟩)
    have h := congrArg e (hP.comm _ hs' _ ht')
    rw [map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply] at h
    exact congrArg Prod.snd h
  have : SigmaFinite μ₁ := inferInstance
  have : SigmaFinite μ₂ := inferInstance
  have : (μ₁.prod μ₁).IsHaarMeasure := inferInstance
  have : ((μ₁.prod μ₁).prod μ₂).IsHaarMeasure := inferInstance
  obtain ⟨ν', hν'1, hν'2⟩ := exists_haar_map e (adCent d) ν _ (hcent d)
  have := hν'1
  have := hν'2

  have hFm : Measurable fun x => φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x) := by
    have h1 : Continuous fun x : GA E n => twConj (thetaA E n) x (ratGL E n d) :=
      (continuous_inv.mul continuous_const).mul hθc
    refine (hφ.cont.comp h1).measurable.mul (hV.meas.comp (Measurable.of_eval fun e' => ?_))
    have := hdegm (Wof e')
    rw [← BorelSpace.measurable_eq] at this
    exact measurable_const.sub this
  have hFi : ∀ t ∈ adCent d, ∀ x, φ (twConj (thetaA E n) (t * x) (ratGL E n d)) * V (yOf τ Wof (t * x)) =
      φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x) := by
    intro t ht x
    have ht' : t⁻¹ * ratGL E n d * thetaA E n t = ratGL E n d := ht
    have h1 : twConj (thetaA E n) (t * x) (ratGL E n d) = twConj (thetaA E n) x (ratGL E n d) := by
      calc (t * x)⁻¹ * ratGL E n d * thetaA E n (t * x)
          = x⁻¹ * (t⁻¹ * ratGL E n d * thetaA E n t) * thetaA E n x := by rw [map_mul]; group
        _ = x⁻¹ * ratGL E n d * thetaA E n x := by rw [ht']
    have h2 : yOf τ Wof (t * x) = fun e' => yOf τ Wof x e' - sdot e' (a t) := by
      funext e'
      simp only [yOf, hP.degT t ht x e']
      ring
    rw [h1, h2, hVa t ht]
  refine hQM (GA E n) ((GL (Fin n) ℂ × GL (Fin n) ℂ) × G') e μ ((μ₁.prod μ₁).prod μ₂) (adCent d) _ ν ν'
    (fun x => φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x)) hP.closed (hcent d) hFm hFi ?_
  refine hQP (GL (Fin n) ℂ × GL (Fin n) ℂ) G' (μ₁.prod μ₁) μ₂ _ _ ν' _ hclP hcl3 hcommP hcomm3
    (hFm.comp e.symm.continuous.measurable) ?_ (Or.inl ?_)
  · intro t ht x
    show _ * _ = _ * _
    rw [map_mul]
    exact hFi _ ((hmem _).2 (by rw [e.apply_symm_apply]; exact ht)) _
  intro ν₁ _ _ x'

  have hPl7 : ∀ v, GeneralLinearGroup.map (cV v) (ratGL E n d) = locGL v d := fun v =>
    (hPl E n v ⊥).2.2.2.2.2.2.1 d
  have hδ : e (ratGL E n d) = ((locGL v₁ d, locGL v₂ d), (e (ratGL E n d)).2) := by
    have h := he1 (ratGL E n d)
    rw [hPl7 v₁, hPl7 v₂] at h
    exact Prod.ext h rfl
  have hproj : ∀ y : (GL (Fin n) ℂ × GL (Fin n) ℂ) × G',
      GeneralLinearGroup.map (cV v₁) (e.symm y) = y.1.1 ∧ GeneralLinearGroup.map (cV v₂) (e.symm y) = y.1.2 := by
    intro y
    have h := he1 (e.symm y)
    rw [e.apply_symm_apply] at h
    exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩
  set g' := twConj θ' x' (e (ratGL E n d)).2 with hg'
  set g0 := e.symm (((1 : GL (Fin n) ℂ), (1 : GL (Fin n) ℂ)), x') with hg0
  set f : GL (Fin n) ℂ × GL (Fin n) ℂ → ℂ := fun g => φ (e.symm (g, g')) with hf
  set z : (Fin m → SignType) → ℝ := fun e' => yOf τ Wof g0 e' - pAt Wof v₁ 1 e' - pAt Wof v₂ 1 e' with hz
  have hsplit : ∀ x₁ x₂ : GL (Fin n) ℂ, e.symm ((x₁, x₂), x') = embInf n v₁ x₁ * (embInf n v₂ x₂ * g0) := by
    intro x₁ x₂
    rw [← e.symm_apply_apply (embInf n v₁ x₁ * (embInf n v₂ x₂ * g0))]
    congr 1
    rw [map_mul, map_mul, hev1, hev2, hg0, e.apply_symm_apply]
    simp
  have hφpart : ∀ x₁ x₂ : GL (Fin n) ℂ, twConj (thetaA E n) (e.symm ((x₁, x₂), x')) (ratGL E n d) =
      e.symm ((twConj (thC n) x₁ (locGL v₁ d), twConj (thC n) x₂ (locGL v₂ d)), g') := by
    intro x₁ x₂
    rw [← e.symm_apply_apply (twConj (thetaA E n) (e.symm ((x₁, x₂), x')) (ratGL E n d))]
    congr 1
    simp only [twConj, map_mul, map_inv, heθ, e.apply_symm_apply]
    rw [hδ, hg']
    rfl
  have hVpart : ∀ x₁ x₂ : GL (Fin n) ℂ, yOf τ Wof (e.symm ((x₁, x₂), x')) = pAt Wof v₁ x₁ + pAt Wof v₂ x₂ + z := by
    intro x₁ x₂
    funext e'
    have hh : e (embInf n v₂ x₂ * g0) = ((1, x₂), x') := by
      rw [map_mul, hev2, hg0, e.apply_symm_apply]; simp
    have hc1 : GeneralLinearGroup.map (cV v₁) (embInf n v₂ x₂ * g0) = 1 := by
      have h := (hproj (e (embInf n v₂ x₂ * g0))).1
      rw [e.symm_apply_apply, hh] at h
      exact h
    have hc0 : GeneralLinearGroup.map (cV v₂) g0 = 1 := (hproj _).2
    have h8a := (hPl E n v₁ (Wof e')).2.2.2.2.2.2.2 x₁ (embInf n v₂ x₂ * g0)
    have h8b := (hPl E n v₂ (Wof e')).2.2.2.2.2.2.2 x₂ g0
    rw [hc1, mul_one] at h8a
    rw [hc0, mul_one] at h8b
    rw [hsplit]
    simp only [yOf, pAt, Pi.add_apply, hz]
    linarith
  have hkey : (fun x₁ : GL (Fin n) ℂ × GL (Fin n) ℂ =>
      φ (twConj (thetaA E n) (e.symm (x₁, x')) (ratGL E n d)) * V (yOf τ Wof (e.symm (x₁, x')))) =
      fun x => f (twConj (thC n) x.1 (locGL v₁ d), twConj (thC n) x.2 (locGL v₂ d)) *
        V (pAt Wof v₁ x.1 + pAt Wof v₂ x.2 + z) := by
    funext x
    obtain ⟨x₁, x₂⟩ := x
    rw [hφpart, hVpart]
  have hz0 : z 0 = 0 := by
    have hr : Module.finrank E (Wof 0) = 0 := by rw [hP.zero]; exact finrank_bot E _
    have h1 := (hPl E n v₁ (Wof 0)).2.2.2.1 hP.zero
    have h2 := (hPl E n v₂ (Wof 0)).2.2.2.1 hP.zero
    simp only [hz, yOf, pAt, prof, hr, h1.1, h2.1, h1.2 g0]
    simp
  have hfc : Continuous f := hφ.cont.comp (e.symm.continuous.comp (continuous_id.prodMk continuous_const))
  have hfs : HasCompactSupport f :=
    hφ.supp.comp_isClosedEmbedding (e.symm.toHomeomorph.isClosedEmbedding.comp (isClosedEmbedding_slice g'))
  have hvc1 : ∀ g, VeryCusp fun x => f (x, g) := by
    intro g
    have h := hVC v₁ (e.symm ((1, g), g')) (hproj _).1
    have heq : (fun x => f (x, g)) = fun x => φ (embInf n v₁ x * e.symm ((1, g), g')) := by
      funext x
      simp only [hf]
      congr 1
      rw [← e.symm_apply_apply (embInf n v₁ x * e.symm ((1, g), g')), map_mul, hev1, e.apply_symm_apply]
      simp
    rw [heq]; exact h
  have hvc2 : ∀ g, VeryCusp fun x => f (g, x) := by
    intro g
    have h := hVC v₂ (e.symm ((g, 1), g')) (hproj _).2
    have heq : (fun x => f (g, x)) = fun x => φ (embInf n v₂ x * e.symm ((g, 1), g')) := by
      funext x
      simp only [hf]
      congr 1
      rw [← e.symm_apply_apply (embInf n v₂ x * e.symm ((g, 1), g')), map_mul, hev2, e.apply_symm_apply]
      simp
    rw [heq]; exact h
  exact (congrArg (quotIntegral (μ₁.prod μ₁) _ ν₁) hkey).trans
    (hTV n m μ₁ (locGL v₁ d) (locGL v₂ d) ν₁ f V (pAt Wof v₁) (pAt Wof v₂) z hm hsep₁ hsep₂ hfc hfs hvc1 hvc2 hV
      hL₁ hL₂ hz0)

end PositivityTheory.Rg.BcB.CV
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PfQMap
open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal NNReal

noncomputable section

namespace PositivityTheory.Rg.BcB.CV.QuotientMapAlt

def subEquiv {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    (e : G ≃ₜ* G') (T : Subgroup G) : T ≃ₜ* T.map e.toMonoidHom where
  toFun t := ⟨e t, Subgroup.mem_map.2 ⟨t, t.2, rfl⟩⟩
  invFun t := ⟨e.symm t, by
    obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.1 t.2
    have h : e.symm (t : G') = s := by
      rw [← hst]
      exact e.symm_apply_apply s
    rw [h]
    exact hs⟩
  left_inv t := Subtype.ext (e.symm_apply_apply (t : G))
  right_inv t := Subtype.ext (e.apply_symm_apply (t : G'))
  map_mul' s t := Subtype.ext (map_mul e (s : G) (t : G))
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

end PositivityTheory.Rg.BcB.CV.QuotientMapAlt

open PositivityTheory.Rg.BcB.CV.QuotientMapAlt in
theorem PositivityTheory.Rg.BcB.CV.pf_QMap : PositivityTheory.Rg.BcB.D4.NormEq → PositivityTheory.Rg.BcB.CV.QMap := by
  intro hN G _ _ _ _ _ _ _ _ G' _ _ _ _ _ _ _ _ e μ _ μ' _ T T' ν _ _ ν' _ _ F hTc hT hF hFT h0
  subst hT
  have hT'c : IsClosed ((T.map e.toMonoidHom : Subgroup G') : Set G') := by
    rw [Subgroup.coe_map]
    exact e.toHomeomorph.isClosedMap _ hTc
  have : SecondCountableTopology T := inferInstanceAs (SecondCountableTopology (T : Set G))
  have : SecondCountableTopology (T.map e.toMonoidHom) :=
    inferInstanceAs (SecondCountableTopology ((T.map e.toMonoidHom : Subgroup G') : Set G'))
  have : LocallyCompactSpace T := hTc.locallyCompactSpace
  have : LocallyCompactSpace (T.map e.toMonoidHom) := hT'c.locallyCompactSpace
  by_cases hex : ∃ ρ, IsQuotNormaliser T ν ρ
  swap
  · rw [quotIntegral, dite_eq_right hex]
  rw [quotIntegral, dite_eq_left hex]
  have hρ : IsQuotNormaliser T ν hex.choose := hex.choose_spec
  set ρ := hex.choose

  let φ := subEquiv e T
  let c : ℝ≥0 := Measure.haarScalarFactor (Measure.map φ.symm ν') ν
  have hc : Measure.map φ.symm ν' = c • ν := Measure.isMulLeftInvariant_eq_smul _ _
  have hc0 : (0 : ℝ≥0) < c := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have hcne : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0.ne'
  let ρ' : G' → ℝ≥0∞ := fun x => (c : ℝ≥0∞)⁻¹ * ρ (e.symm x)
  have hρ' : IsQuotNormaliser (T.map e.toMonoidHom) ν' ρ' := by
    refine ⟨measurable_const.mul (hρ.1.comp e.symm.continuous.measurable), fun x => ?_⟩
    have hk : Measurable fun t : T => ρ ((t : G) * e.symm x) :=
      hρ.1.comp (measurable_subtype_coe.mul_const _)
    have h1 : ∫⁻ h : T.map e.toMonoidHom, ρ' ((h : G') * x) ∂ν' =
        (c : ℝ≥0∞)⁻¹ * ∫⁻ t, ρ ((t : G) * e.symm x) ∂(Measure.map φ.symm ν') := by
      rw [lintegral_map hk (show Measurable (⇑φ.symm) from φ.symm.continuous.measurable),
        ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hcne)]
      refine lintegral_congr fun h => ?_
      show (c : ℝ≥0∞)⁻¹ * ρ (e.symm ((h : G') * x)) = _
      rw [map_mul]
      rfl
    rw [h1, hc, lintegral_smul_measure, hρ.2, ENNReal.smul_def, smul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel hcne ENNReal.coe_ne_top

  let eM : G' ≃ᵐ G := e.symm.toHomeomorph.toMeasurableEquiv
  have hH : (Measure.map eM μ').IsHaarMeasure :=
    (inferInstance : (Measure.map e.symm μ').IsHaarMeasure)
  let a : ℝ≥0 := Measure.haarScalarFactor (Measure.map eM μ') μ
  have ha : Measure.map eM μ' = a • μ := Measure.isMulLeftInvariant_eq_smul _ _
  have ha0 : (0 : ℝ≥0) < a := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have hF' : Measurable fun x => F (e.symm x) := hF.comp e.symm.continuous.measurable
  have hFT' : ∀ h ∈ T.map e.toMonoidHom, ∀ x, F (e.symm (h * x)) = F (e.symm x) := by
    intro h hh x
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hh
    show F (e.symm (e t * x)) = _
    rw [map_mul, e.symm_apply_apply]
    exact hFT t ht _
  have hex' : ∃ ρ, IsQuotNormaliser (T.map e.toMonoidHom) ν' ρ := ⟨ρ', hρ'⟩
  rw [quotIntegral, dite_eq_left hex', hN G' μ' _ ν' _ _ ρ' hF' hFT' hex'.choose_spec hρ'] at h0
  have key : a • ∫ g, F g * ((((c : ℝ≥0∞)⁻¹ * ρ g).toReal : ℝ) : ℂ) ∂μ = 0 := by
    rw [← integral_smul_nnreal_measure, ← ha, integral_map_equiv]
    exact h0
  have key2 : ∫ g, F g * ((((c : ℝ≥0∞)⁻¹ * ρ g).toReal : ℝ) : ℂ) ∂μ = 0 := by
    have := congrArg (fun z : ℂ => (a⁻¹ : ℝ≥0) • z) key
    simpa [smul_smul, inv_mul_cancel₀ ha0.ne'] using this
  have hcr : ((c : ℝ≥0∞)⁻¹).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top, ENNReal.inv_ne_top.2 hcne⟩
  have key3 : ∫ g, F g * ((((c : ℝ≥0∞)⁻¹ * ρ g).toReal : ℝ) : ℂ) ∂μ =
      (((c : ℝ≥0∞)⁻¹).toReal : ℂ) * ∫ g, F g * (((ρ g).toReal : ℝ) : ℂ) ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [ENNReal.toReal_mul, Complex.ofReal_mul]
    ring
  rw [key3] at key2
  exact (mul_eq_zero.1 key2).resolve_left (by exact_mod_cast hcr)
end
end

namespace PositivityTheory.Rg.BcB.CV

theorem classVanish_of_steps (hNormEq : PositivityTheory.Rg.BcB.D4.NormEq) (hQuotProd : PositivityTheory.Rg.BcB.D4.QuotProd) (hChainSum : PositivityTheory.Rg.BcB.ChainSum) (hRatDisc : PositivityTheory.Rg.BcB.D4.RatDisc) (hLocVanish : PositivityTheory.Rg.BcB.LocVanish) (hLocProper : PositivityTheory.Rg.BcB.D4.LocProper) (hLocFlag : PositivityTheory.Rg.BcB.D4.LocFlag) (hDegBdd : PositivityTheory.Rg.BcB.DegBdd) (hKerFin : PositivityTheory.Rg.BcB.D4.KerFin) (hMahler : PositivityTheory.Rg.BcB.Mahler) (hSplitAt : PositivityTheory.Rg.BcB.D4.SplitAt) (hNonEllFlag : PositivityTheory.Rg.BcB.D4.NonEllFlag) (hSplitAt2 : PositivityTheory.Rg.BcB.D4.SplitAt2) (hPairParam : PositivityTheory.Rg.BcB.D4.PairParam) (hTorusChar : PositivityTheory.Rg.BcB.D4.TorusChar) (hChiGam : PositivityTheory.Rg.BcB.D4.ChiGam) (hQuotStage : PositivityTheory.Rg.BcB.D4.QuotStage) (hSizeBasic : PositivityTheory.Rg.BcB.SizeBasic) :
    PositivityTheory.Rg.BcB.ClassVanish :=
  have hQMap : QMap := pf_QMap hNormEq
  have hQInt : QInt := pf_QInt
  have hQAdd : QAdd := pf_QAdd
  have hQProd : QProd := pf_QProd hQuotProd hQMap
  have hVfun : Vfun := pf_Vfun hChainSum hRatDisc hNormEq hQInt hQAdd
  have hLocTor : LocTor := pf_LocTor
  have hOneVanish : OneVanish := pf_OneVanish hLocVanish hLocProper hLocTor hQInt hQAdd
  have hTwoVanish : TwoVanish := pf_TwoVanish hLocVanish hLocProper hLocTor hQInt hQAdd hQProd hOneVanish
  have hPloc : Ploc := pf_Ploc
  have hFamAt : FamAt := pf_FamAt hLocFlag hPloc
  have hAdTop : AdTop := pf_AdTop hDegBdd hRatDisc
  have hCutInt : CutInt := pf_CutInt hKerFin hMahler hQInt hAdTop
  have hGlob1 : Glob1 := pf_Glob1 hSplitAt hNonEllFlag hLocVanish hLocTor hQMap hQProd hPloc hAdTop
  have hGlob2 : Glob2 := pf_Glob2 hSplitAt2 hLocTor hQMap hQProd hTwoVanish hPloc hFamAt hAdTop
  pf_ClassVanish hPairParam hTorusChar hChiGam hQuotStage hRatDisc hSizeBasic hQAdd hVfun hAdTop hCutInt hGlob1 hGlob2

end PositivityTheory.Rg.BcB.CV

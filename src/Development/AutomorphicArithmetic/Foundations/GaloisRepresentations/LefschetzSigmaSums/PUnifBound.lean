module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PUnifBound
open UpperTheory.Gal.LocalSmoothExtension

open scoped Classical in
private lemma hexp_finite {F : Type} [Field F] [NumberField F] {n : ℕ} (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ)
    (lam : (F →+* ℂ) → Fin n → ℕ) : {h : Fin n → ℕ | IsHExp t₀ ε lam h}.Finite := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Set.toFinite _
  · let i₀ : Fin n := ⟨0, hn⟩
    let c : ℕ := ∑ τ ∈ (Finset.univ.erase t₀).erase (NumberField.ComplexEmbedding.conjugate t₀),
      ε τ * ∑ j, lam τ j
    let h₁ : Fin n → ℕ := fun i => ((n - 1) * lam (NumberField.ComplexEmbedding.conjugate t₀) i₀ + c) +
      (lam t₀ i + (n - 1 - (i : ℕ)))
    let h₂ : Fin n → ℕ := fun i => (lam t₀ i₀ + c) +
      (∑ j ∈ Finset.univ.erase i, lam (NumberField.ComplexEmbedding.conjugate t₀) j + (i : ℕ))
    refine (Set.toFinite ({h₁, h₂} : Set (Fin n → ℕ))).subset ?_
    rintro h (⟨m, hm, hh⟩ | ⟨m, hm, hh⟩)
    · left
      funext i
      rw [hh i, ← hm i₀]
    · right
      funext i
      rw [hh i, ← hm i₀]

theorem UpperTheory.Gal.LocalSmoothExtension.unifBound_of :
    UnifBound := by
  intro F _ _ n I _ t ε lam κ
  have hb : ∀ (π : (F →+* ℂ) → (F →+* ℂ)) (i : I), ∃ b, ∀ h : Fin n → ℕ,
      IsHExp (t i) ε (fun τ => lam (π τ)) h → κ (fun τ => lam (π τ)) i h ≤ b := by
    intro π i
    obtain ⟨b, hb⟩ := ((hexp_finite (t i) ε (fun τ => lam (π τ))).image
      (κ (fun τ => lam (π τ)) i)).bddAbove
    exact ⟨b, fun h hh => hb ⟨h, hh, rfl⟩⟩
  choose b hb using hb
  obtain ⟨k, hk⟩ := Finite.exists_le (fun q : ((F →+* ℂ) → (F →+* ℂ)) × I => b q.1 q.2)
  refine ⟨k, fun σ i h hh => ?_⟩
  exact (hb (fun τ => (σ.symm : ℂ →+* ℂ).comp τ) i h hh).trans
    (hk ((fun τ => (σ.symm : ℂ →+* ℂ).comp τ), i))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PGoodConj
open UpperTheory.Gal.LocalSmoothExtension
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

private lemma map_oneP (σ : ℂ ≃+* ℂ) {p : ℕ} [Fact p.Prime] (G : HTGroup p) (g : Gr G 1) :
    σ (oneP G g) = oneP G g := by
  unfold oneP
  by_cases h : g ∈ (Kp G : Set (Gr G 1))
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

private lemma pointSum_conj (σ : ℂ ≃+* ℂ) {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁)
    (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (f : G₁ → ℂ)
    (φ : G₂ → ℂ) (hφ : ∀ x, σ (φ x) = φ x) :
    GlobalTheory.LKCount.pointSum ι₁ ι₂ θ K₁ K₂ γ δ (fun g => σ (f g)) φ =
      σ (GlobalTheory.LKCount.pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ) := by
  unfold GlobalTheory.LKCount.pointSum
  refine Eq.trans ?_ (AddEquiv.map_finsum σ.toAddEquiv _).symm
  refine finsum_congr fun q => ?_
  simp [map_mul, map_inv₀, map_natCast, hφ]

private lemma orbC_conj (σ : ℂ ≃+* ℂ) {H : Type} [Group H] (θ : H →* H) (K C : Subgroup H) (δ : H) (F : H → ℂ) :
    GlobalTheory.LKCount.orbC θ K C δ (fun g => σ (F g)) = σ (GlobalTheory.LKCount.orbC θ K C δ F) := by
  unfold GlobalTheory.LKCount.orbC
  refine Eq.trans ?_ (AddEquiv.map_finsum σ.toAddEquiv _).symm
  refine finsum_congr fun q => ?_
  simp [map_mul, map_inv₀, map_ratCast]

theorem UpperTheory.Gal.LocalSmoothExtension.goodConj_of :
    GoodConj := by
  intro σ p _ G K f h
  refine ⟨fun g hg => h.reg g fun h0 => hg (by simp [h0]), fun P hm hi => ?_, fun B x t hx y hy => ?_⟩
  · have h0 := h.pairs P hm hi
    unfold Pair.term at h0 ⊢
    split_ifs at h0 ⊢ with hh
    · unfold Pair.termAt at h0 ⊢
      rw [pointSum_conj σ _ _ _ _ _ _ _ f _ (map_oneP σ G), h0, map_zero]
    · rfl
  · have h0 := h.forms B x t hx y hy
    unfold GlobalTheory.LKCount.orbK at h0 ⊢
    have e : (fun h : G.GAf × Gr G 1 => σ (f h.1) * oneP G h.2) =
        fun h : G.GAf × Gr G 1 => σ (f h.1 * oneP G h.2) := by
      funext h
      rw [map_mul, map_oneP]
    rw [e, orbC_conj σ, h0, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PMarkRoots
set_option autoImplicit false

noncomputable section

open NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.W2 (rts)

namespace UpperTheory.Gal.LocalSmoothExtension

theorem markRoots_of : MarkRoots := by
  intro p _ D G L ha i₀ v hv hinv P hP
  obtain ⟨i, rfl⟩ := (L.sig v).1 hv
  have hi : i = i₀ := by
    have : Subsingleton (Fin D.a) := by rw [ha]; infer_instance
    exact Subsingleton.elim _ _
  subst hi
  set φ : G.F →+* ℂ := G.iotaC.comp (L.s i) with hφ
  have hφe : ∀ x : D.F, φ (L.e x) = D.tau i x := fun x => L.s_C i x
  have hcomp : (D.tau i).comp (L.e.symm : G.F →+* D.F) = φ := by
    ext x
    rw [RingHom.comp_apply, ← hφe]
    simp
  have hP' : (map (L.e.symm : G.F →+* D.F) P).coeff 0 ≠ 0 := by
    rw [coeff_map]
    simpa using hP
  have hR : rts (endPol L P) (D.tau i) = Multiset.map (fun z : ℂ => z⁻¹) (map φ P).roots := by
    show rts (invPol (map (L.e.symm : G.F →+* D.F) P)) (D.tau i) = _
    rw [hinv D.F _ hP' (D.tau i)]
    simp only [rts, Polynomial.map_map, hcomp]
  rw [hR]
  have hω : φ (L.e D.ω) = D.ρc := by rw [hφe]; exact D.tau_ω i
  have hρ : (starRingEnd ℂ) D.ρc ≠ D.ρc := by
    intro h
    obtain ⟨r, hr⟩ : ∃ r : ℝ, (r : ℂ) = D.ρc := ⟨D.ρc.re, Complex.conj_eq_iff_re.mp h⟩
    have h0 := D.ρc_root
    rw [← hr] at h0
    have h1 : r ^ 2 - (D.tr : ℝ) * r + (D.nm : ℝ) = 0 := by
      have := congrArg Complex.re h0
      simpa [sq] using this
    have h2 : ((D.tr : ℝ) ^ 2 - 4 * (D.nm : ℝ)) < 0 := by exact_mod_cast D.disc_neg
    nlinarith [sq_nonneg (2 * r - (D.tr : ℝ))]
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
    refine Multiset.map_congr rfl (fun μ _ => ?_)
    simp [markOf, h, hω]
  · rw [h]
    have hmap : map (ComplexEmbedding.conjugate φ) P = map (starRingEnd ℂ) (map φ P) := by
      rw [Polynomial.map_map]
      rfl
    rw [hmap, (IsAlgClosed.splits (map φ P)).roots_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun μ _ => ?_)
    simp [markOf, h, hω, hρ]

end UpperTheory.Gal.LocalSmoothExtension
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PPolyFnConj
set_option autoImplicit false

noncomputable section

open UpperTheory.Gal.CertificateRingHomMap (wop wmul wmap)

namespace UpperTheory.Gal.LocalSmoothExtension

private theorem conv_conj (σ : ℂ ≃+* ℂ) {H : Type} [Group H] (K : Subgroup H) (f₁ f₂ : H → ℂ) :
    Formalism.UG.conv K (fun g => σ (f₁ g)) (fun g => σ (f₂ g)) = fun g => σ (Formalism.UG.conv K f₁ f₂ g) := by
  funext g
  unfold Formalism.UG.conv
  have h := σ.toAddEquiv.map_finsum
    (fun x : H ⧸ K => f₁ (Quotient.out x) * f₂ ((Quotient.out x)⁻¹ * g))
  simpa [map_mul] using h.symm

private theorem wordFn_conj (σ : ℂ ≃+* ℂ) {H J : Type} [Group H] (K : Subgroup H) (ψ : J → H → ℂ) (f : H → ℂ)
    (w : List J) :
    wordFn K (fun j g => σ (ψ j g)) w (fun g => σ (f g)) = fun g => σ (wordFn K ψ w f g) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    show Formalism.UG.conv K (fun g => σ (ψ j g)) (wordFn K (fun j g => σ (ψ j g)) w (fun g => σ (f g))) = _
    rw [ih, conv_conj]
    rfl

private theorem polyFn_conj (σ : ℂ ≃+* ℂ) {H J : Type} [Group H] (K : Subgroup H) (ψ : J → H → ℂ) (f : H → ℂ)
    (s : List J →₀ ℂ) :
    polyFn K (fun j g => σ (ψ j g)) (wmap σ.toRingHom s) (fun g => σ (f g)) = fun g => σ (polyFn K ψ s f g) := by
  funext g
  unfold polyFn wmap
  rw [Finsupp.sum_mapRange_index (by intro w; simp)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Finsupp.sum, Finset.sum_apply, map_sum, wordFn_conj]

private theorem wmap_wmul {J : Type} (f : ℂ →+* ℂ) (a s : List J →₀ ℂ) :
    wmap f (wmul a s) = wmul (wmap f a) (wmap f s) := by
  unfold wmul wmap
  have hm : ∀ t : List J →₀ ℂ, Finsupp.mapRange f f.map_zero t =
      Finsupp.mapRange.addMonoidHom f.toAddMonoidHom t := fun t => rfl
  rw [Finsupp.sum_mapRange_index (by intro w; simp)]
  rw [hm, map_finsuppSum]
  refine Finsupp.sum_congr (fun w _ => ?_)
  rw [map_finsuppSum, Finsupp.sum_mapRange_index (by intro w'; simp)]
  refine Finsupp.sum_congr (fun w' _ => ?_)
  rw [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single]
  congr 1
  exact map_mul f (a w) (s w')

theorem polyFnConj_of : PolyFnConj := fun σ _ _ _ K ψ f =>
  ⟨wordFn_conj σ K ψ f, polyFn_conj σ K ψ f, wmap_wmul σ.toRingHom⟩

end UpperTheory.Gal.LocalSmoothExtension

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PGroupTop
open UpperTheory.Gal.LocalSmoothExtension

private lemma sum_swap {A : Type} (s : Finset A) (a : A → ℂ) (g : A → ℂ → ℂ) (R : Multiset ℂ) :
    (R.map fun μ => ∑ α ∈ s, a α * g α μ).sum = ∑ α ∈ s, a α * (R.map (g α)).sum := by
  induction R using Multiset.induction_on with
  | empty => simp
  | cons b R ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih, mul_add, Finset.sum_add_distrib]

theorem UpperTheory.Gal.LocalSmoothExtension.groupTop_of :
    GlobalTheory.RootSumWeights.MarkWeightedFixedPointEqDefinitePairOdd → GlobalTheory.LKDef.TraceDefinitePairsEqAutomorphicTrace → RootW → InvRoots → InvPolProps → MarkRoots → DPairPol → DSumCongr → TestOf → TestOne → GroupTop := by
  classical
  intro hW hT hR hInv hProps hMark hDP hDS hTest hOne p _ D G L lam i₀ h hh
  have hcj : NumberField.ComplexEmbedding.conjugate (D.tau i₀) ≠ D.tau i₀ := fun e =>
    NumberField.IsTotallyComplex.complexEmbedding_not_isReal (D.tau i₀)
      (NumberField.ComplexEmbedding.isReal_iff.2 e)
  obtain ⟨k₀, hk⟩ := hR D.F G.n (D.tau i₀) (epsOf D) lam h hcj hh
  refine ⟨k₀, fun k hkk => ?_⟩
  obtain ⟨c, hc1, hc2⟩ := hk k hkk
  refine ⟨c, hc1, ?_⟩
  intro ha hga hodd v hv V _ _ _ ξ hξ Lv f hf hG y
  have hTf := hTest _ _ f hf
  have hO := hOne p G
  rw [hW p G hga hodd v hv _ Lv f hTf.1 hG.reg (Kp G) (oneP G) hO.1 hG.pairs]
  have key : ∀ P : GlobalTheory.LKDef.DPair G,
      GlobalTheory.RootSumWeights.rootSum G v (fun P μ => c.sum fun α r => r * cW L i₀ v α y P μ) P.pol =
        (fun P => schW lam (endPol L P)) P.pol * ∑ i, y ^ h i := by
    intro P
    obtain ⟨h0, q, hq⟩ := hDP p G P v
    have hroots := hMark p D G L ha i₀ v hv hInv P.pol h0
    have h0' : (P.pol.map (L.e.symm : G.F →+* D.F)).coeff 0 ≠ 0 := by
      rw [Polynomial.coeff_map]
      exact (map_ne_zero _).2 h0
    obtain ⟨d1, d2, d3⟩ := hProps D.F (P.pol.map (L.e.symm : G.F →+* D.F)) h0'
    have hdeg : (endPol L P.pol).natDegree = G.n := by
      show (invPol _).natDegree = _
      rw [d1, Polynomial.natDegree_map]
      exact P.reg.1
    have hsep : (endPol L P.pol).Separable := d3 (P.reg.2.map)
    have habs : ∃ q : ℝ, ∀ z ∈ UpperTheory.Gal.W2.rts (endPol L P.pol) (D.tau i₀),
        z * (starRingEnd ℂ) z = q := by
      refine ⟨q⁻¹, fun z hz => ?_⟩
      rw [← hroots, Multiset.mem_map] at hz
      obtain ⟨μ, hμ, rfl⟩ := hz
      have hm := hq μ hμ
      have hq' : ((q⁻¹ : ℝ) : ℂ) = (μ * (starRingEnd ℂ) μ)⁻¹ := by
        rw [hm]; push_cast; rfl
      rw [hq']
      unfold markOf
      split_ifs
      · rw [map_inv₀, mul_inv]
      · rw [map_inv₀, Complex.conj_conj, mul_inv, mul_comm]
    have := hc2 (endPol L P.pol) hdeg hsep d2 habs y
    show _ = schW lam (endPol L P.pol) * _
    rw [← this]
    unfold GlobalTheory.RootSumWeights.rootSum
    simp only [Finsupp.sum]
    rw [sum_swap]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← hroots, Multiset.map_map]
    rfl
  rw [hDS p G _ (fun P => schW lam (endPol L P)) (∑ i, y ^ h i) key Lv.K.toSubgroup f 1 (Kp G) (oneP G)]
  rw [hT p G hga V ξ (fun P => schW lam (endPol L P)) hξ Lv f hTf.1 hTf.2 (Kp G) (oneP G) hO.1 hO.2 hG.forms]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCxFlat
set_option autoImplicit false

noncomputable section

open Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open scoped TensorProduct Classical

namespace UpperTheory.Gal.LocalSmoothExtension

private theorem sigma_finsum {α : Type} {δ : α → Type} (F : (Σ a, δ a) → ℂ) (S : Finset (Σ a, δ a))
    (hS : ∀ z, F z ≠ 0 → z ∈ S) : ∑ᶠ a, ∑ᶠ d, F ⟨a, d⟩ = ∑ z ∈ S, F z := by
  have hinj : ∀ a, Set.InjOn (Sigma.mk a : δ a → Σ a, δ a) (Sigma.mk a ⁻¹' (S : Set (Σ a, δ a))) :=
    fun a => sigma_mk_injective.injOn
  let U : ∀ a, Finset (δ a) := fun a => S.preimage (Sigma.mk a) (hinj a)
  have h1 : ∀ a, ∑ᶠ d, F ⟨a, d⟩ = ∑ d ∈ U a, F ⟨a, d⟩ := fun a =>
    finsum_eq_sum_of_support_subset _ (fun d hd => by
      simpa [U] using hS _ hd)
  have hT : Function.support (fun a => ∑ᶠ d, F ⟨a, d⟩) ⊆ ((S.image Sigma.fst : Finset α) : Set α) := by
    intro a ha
    have ha' : ∑ d ∈ U a, F ⟨a, d⟩ ≠ 0 := by
      rw [← h1 a]; exact ha
    obtain ⟨d, hd, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha'
    have hd' : (⟨a, d⟩ : Σ a, δ a) ∈ S := by simpa [U] using hd
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨_, hd', rfl⟩)
  rw [finsum_eq_sum_of_support_subset _ hT]
  simp_rw [h1]
  rw [← Finset.sum_sigma (S.image Sigma.fst) U F]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext ⟨a, d⟩
  simp only [Finset.mem_sigma, Finset.mem_image, U, Finset.mem_preimage]
  exact ⟨fun h => h.2, fun h => ⟨⟨_, h, rfl⟩, h⟩⟩

private theorem flat_finsum {α : Type} {β γ : α → Type} (n : ∀ a, β a → ℂ) (t : ∀ a, β a → γ a → ℂ)
    (S : Finset (Σ a, β a × γ a)) (hS : ∀ z, t z.1 z.2.1 z.2.2 ≠ 0 → z ∈ S) :
    ∑ᶠ a, ∑ᶠ b, n a b * ∑ᶠ y, t a b y = ∑ z ∈ S, n z.1 z.2.1 * t z.1 z.2.1 z.2.2 := by
  rw [← sigma_finsum (fun z : Σ a, β a × γ a => n z.1 z.2.1 * t z.1 z.2.1 z.2.2) S
    (fun z hz => hS z (right_ne_zero_of_mul hz))]
  refine finsum_congr fun a => ?_
  have hfin : (Function.support fun d : β a × γ a => n a d.1 * t a d.1 d.2).Finite := by
    have hinj : Set.InjOn (fun d : β a × γ a => (⟨a, d⟩ : Σ a, β a × γ a))
        ((fun d : β a × γ a => (⟨a, d⟩ : Σ a, β a × γ a)) ⁻¹' (S : Set (Σ a, β a × γ a))) := by
      intro d _ d' _ h
      simpa using h
    refine (S.finite_toSet.preimage hinj).subset ?_
    intro d hd
    exact hS ⟨a, d⟩ (right_ne_zero_of_mul hd)
  rw [finsum_curry _ hfin]
  refine finsum_congr fun b => ?_
  exact mul_finsum _ _

theorem cxFlat_of : CxFlat := by
  intro p _ G v c K f S hS
  unfold cxTotalM cxSumM cxSumAtM
  refine flat_finsum (α := FCls G) (β := fun q => PtsOf G v K q) (γ := fun q => grp G (Quot.out q).β)
    (fun q a => ((Nat.card (Stab G v (Quot.out q).β (Quot.out q).trivAf.choose
      (Quot.out q).trivAf.choose_spec.choose (Quot.out q).trivAf.choose_spec.choose_spec K (Kp G)
      (Quot.out a)) : ℕ) : ℂ)⁻¹)
    (fun q a y => if FixL G v (Quot.out q).β y (Quot.out a).2.1 then
      f ((Quot.out a).1.1⁻¹ * toAfF G (Quot.out q).β (Quot.out q).trivAf.choose
          (Quot.out q).trivAf.choose_spec.choose (Quot.out q).trivAf.choose_spec.choose_spec y *
          (Quot.out a).1.1) *
        oneP G ((Quot.out a).1.2⁻¹ * toP1 G (Quot.out q).β y * (Quot.out a).1.2) *
        c (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (eigL G v (Quot.out q).β y (Quot.out a).2.1)
      else 0) S ?_
  intro z hz
  refine hS z ?_
  beta_reduce at hz
  split_ifs at hz with hfix
  · have h12 := left_ne_zero_of_mul hz
    exact ⟨hfix, left_ne_zero_of_mul h12, right_ne_zero_of_mul h12⟩
  · exact (hz rfl).elim

end UpperTheory.Gal.LocalSmoothExtension
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PEigOf
open UpperTheory.Gal.LocalSmoothExtension

namespace UpperTheory.Gal.LocalSmoothExtension

open UpperTheory.Gal.CertificateRingHomMap Module

private lemma common_eig {M J : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (S : J → End ℂ M) (hS : ∀ i j, S i * S j = S j * S i) (θ : J → ℂ) (y : M) (hy : y ≠ 0)
    (hG : ∀ j, y ∈ (S j).maxGenEigenspace (θ j)) : ∃ x : M, x ≠ 0 ∧ ∀ j, S j x = θ j • x := by
  let G : Submodule ℂ M := ⨅ j, (S j).maxGenEigenspace (θ j)
  have hyG : y ∈ G := (Submodule.mem_iInf _).2 hG
  have hGne : G ≠ ⊥ := fun h => hy (by rw [h] at hyG; simpa using hyG)
  have hst : ∀ j, ∀ x ∈ G, S j x ∈ G := by
    intro j x hx
    refine (Submodule.mem_iInf _).2 fun i => ?_
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (show Commute (S i) (S j) from hS i j) (θ i)
      ((Submodule.mem_iInf _).1 hx i)
  obtain ⟨v, hvG, hv0, hv⟩ := UpperTheory.V.LinAlg.simEig S hS _ G rfl hGne hst
  refine ⟨v, hv0, fun j => ?_⟩
  obtain ⟨c, hc⟩ := hv j
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hvG j)
  have h1 : (S j - θ j • (1 : End ℂ M)) v = (c - θ j) • v := by
    simp [hc, sub_smul]
  have hp : ∀ n : ℕ, ((S j - θ j • (1 : End ℂ M)) ^ n) v = (c - θ j) ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_apply_eq_comp, h1, map_smul, ih, smul_smul, pow_succ']
  rw [hp] at hk
  rcases smul_eq_zero.1 hk with h | h
  · have : c = θ j := sub_eq_zero.1 (by_contra fun h' => pow_ne_zero k h' h)
    rw [hc, this]
  · exact absurd h hv0

private lemma wop_restrict {M J : Type} [AddCommGroup M] [Module ℂ M] (U : Submodule ℂ M)
    (T : J → End ℂ M) (h : ∀ j, ∀ x ∈ U, T j x ∈ U) (s : List J →₀ ℂ) (x : U) :
    ((wop (fun j => (T j).restrict (h j)) s x : U) : M) = wop T s (x : M) := by
  have hw : ∀ (w : List J) (x : U),
      (((w.map fun j => (T j).restrict (h j)).prod x : U) : M) = (w.map T).prod (x : M) := by
    intro w
    induction w with
    | nil => intro x; simp
    | cons j w ih =>
      intro x
      simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp, LinearMap.coe_restrict_apply, ih]
  unfold wop
  simp only [Finsupp.sum, LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply,
    Submodule.coe_smul, hw]

end UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.eigOf_of :
    UpperTheory.Gal.CertificateRingHomMap.ProjOne.{0} → EigOf := by
  open UpperTheory.Gal.CertificateRingHomMap Module in
  intro hP B J _ W _ _ _ T u θ hc
  let U : ∀ b, Submodule ℂ (W b) := fun b =>
    Submodule.span ℂ {x | ∃ (w : List J) (z : W b), x = ((w.map (T b)).prod * u b) z}
  have hst : ∀ b j, ∀ x ∈ U b, T b j x ∈ U b := by
    intro b j x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨w, z, rfl⟩ := h
      exact Submodule.subset_span ⟨j :: w, z, by simp [mul_apply_eq_comp]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have hcm : ∀ b j j', ∀ x ∈ U b, T b j (T b j' x) = T b j' (T b j x) := by
    intro b j j' x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨w, z, rfl⟩ := h
      have := LinearMap.congr_fun (hc b j j' w) z
      simpa [mul_apply_eq_comp] using this
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
    | smul a x _ hx => simp only [map_smul, hx]
  let S : ∀ b, J → End ℂ (U b) := fun b j => (T b j).restrict (hst b j)
  have hS : ∀ b j j', S b j * S b j' = S b j' * S b j := by
    intro b j j'
    ext ⟨x, hx⟩
    exact hcm b j j' x hx
  let T' : J → ∀ b, End ℂ (U b) := fun j b => S b j
  cases nonempty_fintype B
  obtain ⟨s, h1, -, h3⟩ := hP ℂ (∀ b, End ℂ (U b)) J T' (fun i j => funext fun b => hS b i j) θ
  refine ⟨s, h1, fun b hne => ?_⟩
  have hev : (wop T' s) b = wop (S b) s := map_wop (Pi.evalAlgHom ℂ (fun b => End ℂ (U b)) b) T' s
  obtain ⟨z, hz⟩ : ∃ z, (wop (T b) s * u b) z ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (LinearMap.ext h)
  have hu : u b z ∈ U b := Submodule.subset_span ⟨[], z, by simp⟩
  have hcoe : ((wop (S b) s ⟨u b z, hu⟩ : U b) : W b) = wop (T b) s (u b z) :=
    wop_restrict (U b) (T b) (hst b) s ⟨u b z, hu⟩
  have hy : wop (S b) s ⟨u b z, hu⟩ ≠ 0 := by
    intro h
    apply hz
    rw [mul_apply_eq_comp, ← hcoe, h]
    rfl
  have hyG : ∀ j, wop (S b) s ⟨u b z, hu⟩ ∈ (S b j).maxGenEigenspace (θ j) := by
    intro j
    obtain ⟨N, hN⟩ := h3 j
    have hN' := congrArg (Pi.evalAlgHom ℂ (fun b => End ℂ (U b)) b) hN
    rw [map_mul, map_pow, map_sub, AlgHom.commutes, map_zero] at hN'
    refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨N, ?_⟩
    have h2 : (S b j - θ j • (1 : End ℂ (U b))) ^ N * wop (S b) s = 0 := by
      rw [← hev, Algebra.algebraMap_eq_smul_one] at *
      exact hN'
    have := LinearMap.congr_fun h2 ⟨u b z, hu⟩
    simpa [mul_apply_eq_comp] using this
  obtain ⟨x, hx0, hx⟩ := common_eig (S b) (hS b) θ _ hy hyG
  refine ⟨(x : W b), fun h => hx0 (Subtype.ext h), fun j => ?_⟩
  exact congrArg Subtype.val (hx j)
end

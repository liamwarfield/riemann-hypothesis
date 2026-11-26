module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RhoKApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PointsFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsDualNumberPointOfPointDerivationVanishing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerExtend
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsPointDerivationEmbEntryEqSmulMatEntry

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsBasePointDerivationOfWeightHomogeneous
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

private theorem coeff_single_mul {E σ : Type} [CommRing E] (i : σ) (f g : MvPowerSeries σ E) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single i 1) g +
      MvPowerSeries.constantCoeff g * MvPowerSeries.coeff (Finsupp.single i 1) f := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, mul_comm]

private theorem free_ext {O σ Q : Type} [CommRing O] [Fintype σ] [AddCommGroup Q] [Module O Q]
    (D E : MvPowerSeries σ O →ₗ[O] Q)
    (hD : ∀ f g, D (f * g) = MvPowerSeries.constantCoeff f • D g + MvPowerSeries.constantCoeff g • D f)
    (hE : ∀ f g, E (f * g) = MvPowerSeries.constantCoeff f • E g + MvPowerSeries.constantCoeff g • E f)
    (hX : ∀ s, D (MvPowerSeries.X s) = E (MvPowerSeries.X s)) (f : MvPowerSeries σ O) : D f = E f := by
  let W' := WPres.free O (fun _ : σ => (0 : ℤ))
  have h' : W'.HasOrigin := fun f hf => by
    have : f = 0 := hf
    rw [this, map_zero]
  have ho : ∀ f, W'.origin h' f = MvPowerSeries.constantCoeff f := fun f => W'.origin_π h' f
  have h0 := (der_extend O _ ℤ W' h' Q).2 (D - E) (fun f g => by
    rw [ho, ho]
    simp only [LinearMap.sub_apply]
    rw [hD, hE, smul_sub, smul_sub]
    abel) (fun (s : σ) => by
    show D (MvPowerSeries.X s) - E (MvPowerSeries.X s) = 0
    rw [hX, sub_self])
  rw [sub_eq_zero.1 h0]

private theorem free_ex {O σ : Type} [CommRing O] [Fintype σ] (d : σ → O) :
    ∃ L : MvPowerSeries σ O →ₗ[O] O,
      (∀ f g, L (f * g) = MvPowerSeries.constantCoeff f • L g + MvPowerSeries.constantCoeff g • L f) ∧
      (∀ s, L (MvPowerSeries.X s) = d s) ∧
      ∀ f, L f = ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) f • d s := by
  classical
  let L : MvPowerSeries σ O →ₗ[O] O :=
    ∑ s, (MvPowerSeries.coeff (Finsupp.single s 1) : MvPowerSeries σ O →ₗ[O] O).smulRight (d s)
  have hL : ∀ f, L f = ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) f • d s := fun f => by
    simp [L]
  refine ⟨L, fun f g => ?_, fun s => ?_, hL⟩
  · rw [hL, hL, hL]
    simp only [coeff_single_mul, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  · rw [hL]
    simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj]

theorem UpperTheory.exists_base_pointDerivation_of_weight_homogeneous :
    ∀ {O B R S Q : Type} [CommRing O] [CommRing B] [Algebra O B] [CommRing R] [Algebra O R] [CommRing S] [Algebra O S] [AddCommGroup Q] [Module O Q]
          (WB : WPres O ℤ B) (hB : WB.HasOrigin) (W : WPres O ℤ R) (h : W.HasOrigin) {τ : Type} (e : WB.σ ⊕ τ ≃ W.σ), (∀ s, W.wt (e (.inl s)) = WB.wt s) →
          RingHom.ker W.π = (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)) →
          ∀ (qh : R →ₐ[O] S) (x₀ : S →ₐ[O] O), x₀.comp qh = W.origin h → ∀ (p : O →ₗ[O] Q), Function.Surjective p → ∀ (j : ℤ),
          ∀ D ∈ PtDer x₀ Q, (∀ s, W.wt s ≠ j → D (qh (W.z s)) = 0) → ∀ D₁ ∈ PtDer (WB.origin hB) O, (∀ s, WB.wt s ≠ j → D₁ (WB.z s) = 0) →
          (∀ s, p (D₁ (WB.z s)) = D (qh (W.z (e (.inl s))))) →
          ∃ D' ∈ PtDer (W.originA h) O, HasWt W.gr j D' ∧ ∀ f : W.A, D (qh f) = p (D' f) := by
  intro O B R S Q _ _ _ _ _ _ _ _ _ WB hB W h τ e hwt hker qh x₀ hx p hp j D hD hDw D₁ hD₁ hD₁w hpD
  classical
  have hd : ∀ s : W.σ, ∃ d : O, (∀ t, s = e (.inl t) → d = D₁ (WB.z t)) ∧ (W.wt s ≠ j → d = 0) ∧
      p d = D (qh (W.z s)) := fun s => by
    obtain ⟨u, rfl⟩ := e.surjective s
    rcases u with t | t
    · refine ⟨D₁ (WB.z t), fun t' ht => ?_, fun hj => hD₁w t (by rwa [← hwt]), hpD t⟩
      rw [Sum.inl.inj (e.injective ht)]
    · by_cases hj : W.wt (e (.inr t)) = j
      · obtain ⟨a, ha⟩ := hp (D (qh (W.z (e (.inr t)))))
        exact ⟨a, fun t' ht => absurd (e.injective ht) Sum.inr_ne_inl, fun h' => absurd hj h', ha⟩
      · exact ⟨0, fun t' ht => absurd (e.injective ht) Sum.inr_ne_inl, fun _ => rfl,
          by rw [map_zero, hDw _ hj]⟩
  choose d hd1 hd2 hd3 using hd
  obtain ⟨L, hL, hLX, hLs⟩ := free_ex d
  have hren : ∀ g, L (MvPowerSeries.rename (fun s => e (.inl s)) g) = D₁ (WB.π g) :=
    free_ext (L ∘ₗ (MvPowerSeries.rename (fun s => e (.inl s)) : MvPowerSeries WB.σ O →ₐ[O] _).toLinearMap)
      (D₁ ∘ₗ WB.π.toLinearMap)
      (fun f g => by
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, hL,
          MvPowerSeries.constantCoeff_rename])
      (fun f g => by
        have h1 : D₁ (WB.π f * WB.π g) = _ := hD₁ _ _
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, h1, WB.origin_π])
      (fun s => by
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, MvPowerSeries.rename_X, hLX]
        exact hd1 _ s rfl)
  have hk : ∀ f, W.π f = 0 → L f = 0 := fun f hf => by
    have hf' : f ∈ RingHom.ker W.π := hf
    have key : ∀ f ∈ (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)), L f = 0 := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, hg, rfl⟩ := hx
        have hg' : WB.π g = 0 := hg
        rw [hren, hg', map_zero]
      | zero => exact map_zero L
      | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
      | smul a x hx hx' =>
        have : x ∈ RingHom.ker W.π := by rw [hker]; exact hx
        rw [smul_eq_mul, hL, hx', h x this, smul_zero, zero_smul, add_zero]
    exact key f (hker ▸ hf')
  have hs : Function.Surjective W.π.toLinearMap := W.surj
  let E : R →ₗ[O] O := ((LinearMap.ker W.π.toLinearMap).liftQ L (fun f hf => hk f hf)) ∘ₗ
    (W.π.toLinearMap.quotKerEquivOfSurjective hs).symm.toLinearMap
  have hE : ∀ f, E (W.π f) = L f := fun f => by
    have : (W.π.toLinearMap.quotKerEquivOfSurjective hs).symm (W.π f) = Submodule.Quotient.mk f := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show (LinearMap.ker W.π.toLinearMap).liftQ L (fun f hf => hk f hf)
      ((W.π.toLinearMap.quotKerEquivOfSurjective hs).symm (W.π f)) = _
    rw [this]
    rfl
  have hEd : ∀ a b, E (a * b) = W.origin h a • E b + W.origin h b • E a := fun a b => by
    obtain ⟨f, rfl⟩ := W.surj a
    obtain ⟨g, rfl⟩ := W.surj b
    rw [← map_mul, hE, hE, hE, hL, W.origin_π, W.origin_π]
  have hxo : ∀ f, x₀ (qh (W.π f)) = MvPowerSeries.constantCoeff f := fun f => by
    rw [← AlgHom.comp_apply, hx, W.origin_π]
  have hred : ∀ f, D (qh (W.π f)) = p (L f) :=
    free_ext (D ∘ₗ (qh.comp W.π).toLinearMap) (p ∘ₗ L)
      (fun f g => by
        have h1 : D (qh (W.π f) * qh (W.π g)) = _ := hD _ _
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, map_mul, h1, hxo])
      (fun f g => by simp only [LinearMap.comp_apply, hL, map_add (f := _), map_smul])
      (fun s => by
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, hLX, hd3]
        rfl)
  refine ⟨E ∘ₗ W.A.val.toLinearMap, fun a b => hEd a b, fun i hi a ha => ?_, fun a => ?_⟩
  · obtain ⟨f, hf, hfa⟩ := ha
    have hfa' : W.π f = (a : R) := hfa
    show E (a : R) = 0
    rw [← hfa', hE, hLs]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases hs : W.wt s = j
    · rw [hf (Finsupp.single s 1) (by simpa [Finsupp.weight_single, hs] using hi.symm), zero_smul]
    · rw [hd2 s hs, smul_zero]
  · obtain ⟨f, hf⟩ := W.surj (a : R)
    show D (qh (a : R)) = p (E (a : R))
    rw [← hf, hE, hred]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsEqnsOfWeightedGenerators
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

theorem UpperTheory.exists_eqns_of_weighted_generators :
    ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) (x : A →ₐ[O] O) (r s r' s' m : ℕ) {κ : Type} [Finite κ] (g : κ → A) (w : κ → ℤ),
          (∀ i, g i ∈ 𝒜 (w i)) → (∀ i, x (g i) = 0) → (∀ i, -2 ≤ w i ∧ w i ≤ 2) →
          Nat.card {i // w i = -1} = r + 1 → Nat.card {i // w i = -2} = s → Nat.card {i // w i = 1} = r' → Nat.card {i // w i = 2} = s' → Nat.card {i // w i = 0} = m →
          ∃ Q : Eqns 𝒜 x r s r' s' m, Q.ideal = Ideal.span (Set.range g) := by
  intro O A _ _ _ 𝒜 x r s r' s' m κ _ g w hg hx hw h1 h2 h3 h4 h5
  have key : ∀ (j : ℤ) (n : ℕ), Nat.card {i // w i = j} = n →
      ∃ F : Fin n → A, (∀ k, F k ∈ 𝒜 j ∧ x (F k) = 0) ∧ Set.range F = g '' {i | w i = j} := by
    intro j n hn
    let e := Finite.equivFinOfCardEq hn
    refine ⟨fun k => g (e.symm k).1, fun k => ⟨?_, hx _⟩, ?_⟩
    · have := hg (e.symm k).1
      rwa [(e.symm k).2] at this
    · ext a
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨(e.symm k).1, (e.symm k).2, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨e ⟨i, hi⟩, by simp⟩
  obtain ⟨F, hF, rF⟩ := key _ _ h1
  obtain ⟨G, hG, rG⟩ := key _ _ h2
  obtain ⟨E, hE, rE⟩ := key _ _ h3
  obtain ⟨E', hE', rE'⟩ := key _ _ h4
  obtain ⟨Z, hZ, rZ⟩ := key _ _ h5
  refine ⟨⟨F, G, E, E', Z, fun i => (hF i).1, fun i => (hG i).1, fun i => (hE i).1, fun i => (hE' i).1, hZ⟩, ?_⟩
  show Ideal.span (Set.range F ∪ Set.range G ∪ Set.range E ∪ Set.range E' ∪ Set.range Z) = _
  rw [rF, rG, rE, rE', rZ, ← Set.image_union, ← Set.image_union, ← Set.image_union, ← Set.image_union,
    ← Set.image_univ]
  congr 2
  ext i
  have := hw i
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsSurjectionUnivNormCondKerSpanNEq
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

private theorem mat_symm {R : Type} [CommRing R] (x : GG (m := 3) (R := R))
    (h2 : x * x = 1) (hx : x.right = -1) :
    x.mat = Jmat (R := R) 3 * x.matᵀ * Jmat (R := R) 3 := by
  have h : x.left * theta x.left = 1 := by
    have := congrArg SemidirectProduct.left h2
    rwa [SemidirectProduct.mul_left, hx, sgnAct_neg_one] at this
  have h' : x.left = (theta x.left)⁻¹ := eq_inv_of_mul_eq_one_left h
  have := theta_inv_val x.left
  rw [← h'] at this
  exact this

private theorem norm_iff {G R : Type} [Group G] [CommRing R] (c g₁ : G)
    (r : G →* GG (m := 3) (R := R)) (hc : c * c = 1)
    (hr : (r c).right = -1) : Normalised c g₁ r ↔ ∀ i, nEq c g₁ r i = 0 := by
  have hs := mat_symm (r c) (by rw [← map_mul, hc, map_one]) hr
  have hsym : ∀ i j, (r c).mat i j = (r c).mat j.rev i.rev := by
    intro i j
    conv_lhs => rw [hs]
    fin_cases j <;> simp [Matrix.mul_apply, Jmat, Fin.sum_univ_three]
  constructor
  · rintro ⟨h1, h2, h3⟩ i
    fin_cases i <;> simp [nEq, h1, h2, h3]
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    have h6 := h 6
    have h7 := h 7
    simp [nEq, sub_eq_zero] at h0 h1 h2 h3 h4 h5 h6 h7
    have e12 : (r c).mat 1 2 = (r c).mat 0 1 := hsym 1 2
    have e21 : (r c).mat 2 1 = (r c).mat 1 0 := hsym 2 1
    have e22 : (r c).mat 2 2 = (r c).mat 0 0 := hsym 2 2
    refine ⟨?_, h6, h7⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0, h1, h2, h3, h4, h5, e12, e21, e22]

private theorem nEq_map {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} (c g₁ : Γ) {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R']
    [Algebra O R'] [IsCO O R'] (r : GLift O η Ψ R) (f : R →ₐ[O] R') (i : Fin 8) :
    nEq c g₁ (r.map f).hom i = f (nEq c g₁ r.hom i) := by
  have hm : ∀ g, ((r.map f).hom g).mat = (r.hom g).mat.map f := fun g => GG.map_mat (f : R →+* R') (r.hom g)
  fin_cases i <;> simp [nEq, zmat, hm, map_sub, map_one]

private theorem ext_lemma {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (a b : GLift O η Ψ R) (h : ∀ x, (a.hom x).mat = (b.hom x).mat) : a = b := by
  apply GLift.ext
  apply MonoidHom.ext
  intro x
  apply SemidirectProduct.ext
  · exact Units.ext (h x)
  · rw [a.hasMult x, b.hasMult x]

private theorem gLift_map_hom_mat_eq_map {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R']
    [Algebra O R'] [IsCO O R'] (r : GLift O η Ψ R) (f : R →ₐ[O] R') (x : Γ) :
    ((r.map f).hom x).mat = (r.hom x).mat.map f :=
  GG.map_mat (f : R →+* R') (r.hom x)

private theorem comp_lemma_3 {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R R' R'' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R']
    [Algebra O R'] [IsCO O R'] [CommRing R''] [Algebra O R''] [IsCO O R''] (r : GLift O η Ψ R)
    (f : R →ₐ[O] R') (g : R' →ₐ[O] R'') : r.map (g.comp f) = (r.map f).map g := by
  apply ext_lemma
  intro x
  rw [gLift_map_hom_mat_eq_map, gLift_map_hom_mat_eq_map, gLift_map_hom_mat_eq_map]
  ext i j
  simp

private theorem gLift_map_id {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (r : GLift O η Ψ R) : r.map (AlgHom.id O R) = r := by
  apply ext_lemma
  intro x
  rw [gLift_map_hom_mat_eq_map]
  ext i j
  simp

theorem UpperTheory.exists_surjection_univ_normCond_ker_span_nEq :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {P : GCond O η Ψ} (c g₁ : Γ)
          (B : Univ P) (S : Univ (NormCond c g₁ P)), c * c = 1 → η c = -1 →
          ∃ p : B.R →ₐ[O] S.R, Function.Surjective p ∧ B.r.map p = S.r ∧ RingHom.ker p = Ideal.span (Set.range (nEq c g₁ B.r.hom)) := by
  intro O _ _ Γ _ _ η Ψ P c g₁ B S hc hη
  have hr : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r : GLift O η Ψ R),
      (r.hom c).right = -1 := fun R _ _ _ r => by rw [r.hasMult c, hη]
  have hNS : NormCond c g₁ P S.R S.r := by
    have h := (S.rep S.R).1 (AlgHom.id O S.R)
    rwa [gLift_map_id] at h
  obtain ⟨p, hp, -⟩ := (B.rep S.R).2 S.r hNS.2
  have hI : Ideal.span (Set.range (nEq c g₁ B.r.hom)) ≤ RingHom.ker p := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    show p (nEq c g₁ B.r.hom i) = 0
    rw [← nEq_map, hp]
    exact (norm_iff c g₁ S.r.hom hc (hr _ S.r)).1 hNS.1 i
  set I := Ideal.span (Set.range (nEq c g₁ B.r.hom)) with hIdef
  haveI : Nontrivial (B.R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (RingHom.ker_ne_top _) hI)
  haveI : IsCO O (B.R ⧸ I) := co_quot O B.R (B.R ⧸ I) (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ_surjective O I)
  have hNq : NormCond c g₁ P (B.R ⧸ I) (B.r.map (Ideal.Quotient.mkₐ O I)) := by
    refine ⟨(norm_iff c g₁ _ hc (hr _ _)).2 (fun i => ?_), (B.rep _).1 _⟩
    rw [nEq_map]
    show Ideal.Quotient.mk I _ = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
  obtain ⟨s, hs, -⟩ := (S.rep (B.R ⧸ I)).2 _ hNq
  have hsp : s.comp p = Ideal.Quotient.mkₐ O I := by
    obtain ⟨u, -, hu⟩ := (B.rep (B.R ⧸ I)).2 _ hNq.2
    have e1 := hu (s.comp p) (by
      show GLift.map (s.comp p) B.r = _
      rw [comp_lemma_3, hp, hs])
    have e2 := hu (Ideal.Quotient.mkₐ O I) rfl
    rw [e1, e2]
  have hker : RingHom.ker p = I := by
    refine le_antisymm (fun x hx => ?_) hI
    have h0 : Ideal.Quotient.mkₐ O I x = 0 := by
      rw [← hsp, AlgHom.comp_apply, RingHom.mem_ker.1 hx, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.1 h0
  have hI' : ∀ a ∈ I, p a = 0 := fun a ha => RingHom.mem_ker.1 (hI ha)
  let p' := Ideal.Quotient.liftₐ I p hI'
  have hp'q : ∀ z, p' (Ideal.Quotient.mkₐ O I z) = p z := fun z => by
    show Ideal.Quotient.lift I (p : B.R →+* S.R) hI' (Ideal.Quotient.mk I z) = p z
    exact Ideal.Quotient.lift_mk I _ _
  have hpq : p'.comp (Ideal.Quotient.mkₐ O I) = p := AlgHom.ext hp'q
  have hid : p'.comp s = AlgHom.id O S.R := by
    obtain ⟨u, -, hu⟩ := (S.rep S.R).2 S.r hNS
    have e1 := hu (p'.comp s) (by
      show GLift.map (p'.comp s) S.r = S.r
      rw [comp_lemma_3, hs, ← comp_lemma_3, hpq, hp])
    have e2 := hu (AlgHom.id O S.R) (gLift_map_id _)
    rw [e1, e2]
  refine ⟨p, fun y => ?_, hp, hker⟩
  obtain ⟨z, hz⟩ := Ideal.Quotient.mkₐ_surjective O I (s y)
  refine ⟨z, ?_⟩
  rw [← hp'q, hz]
  exact congrArg (fun f => f y) hid
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsSpanEntMonApproxOfMemWtPart
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

private theorem one_mem_entMon {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) :
    (1 : R) ∈ entMon r 0 :=
  ⟨[], rfl, rfl⟩

private theorem mul_mem_entMon {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) {i j : ℤ} {a b : R}
    (ha : a ∈ entMon r i) (hb : b ∈ entMon r j) : a * b ∈ entMon r (i + j) := by
  obtain ⟨L, rfl, rfl⟩ := ha
  obtain ⟨M, rfl, rfl⟩ := hb
  exact ⟨L ++ M, by simp, by simp⟩

private theorem mat_mem_entMon {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (g : G) (a b : Fin 3) :
    (r g).mat a b ∈ entMon r (wt1 a - wt1 b) :=
  ⟨[(g, a, b)], by simp [wt], by simp⟩

private theorem theta_left {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (c : G)
    (h1 : (r c).right = -1) (h2 : (r c).mat = 1) (g : G) :
    (theta (r g).left : Matrix (Fin 3) (Fin 3) R) = (r (c * g)).mat := by
  have h : (r c).left = 1 := Units.ext h2
  rw [map_mul, GG.mat, SemidirectProduct.mul_left, h, h1, one_mul, sgnAct_neg_one]

private theorem emb_mem {O G R : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R]
    (r : G →* GG (m := 3) (R := R)) (c : G)
    (h1 : (r c).right = -1) (h2 : (r c).mat = 1) (g : G) (a b : Fin 3 ⊕ Fin 3) :
    emb (r g) a b ∈ Submodule.span O (entMon r (wt6 a - wt6 b)) := by
  rw [UpperTheory.V.U3.emb_apply, theta_left r c h1 h2]
  split_ifs <;> rcases a with a | a <;> rcases b with b | b <;>
    first
    | exact Submodule.zero_mem _
    | exact Submodule.subset_span (mat_mem_entMon r _ a b)

theorem UpperTheory.exists_span_entMon_approx_of_mem_wtPart :
    ∀ {O G R σ : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R] [Finite σ]
      (η : G →* ℤˣ) (Ψ : G →* Oˣ) (r : G →* GG (m := 3) (R := R)) (c : G),
          (r c).right = -1 → (r c).mat = 1 → ∀ (w : σ → ℤ) (Φ : MvPowerSeries σ O →ₐ[O] R) (m : Ideal R), (∀ s, Φ (MvPowerSeries.X s) ∈ m) →
          (∀ s, ∃ g a b, w s = wt6 a - wt6 b ∧ Φ (MvPowerSeries.X s) =
            emb (r g) a b - algebraMap O R (emb (r0 η Ψ g) a b)) →
          ∀ j, ∀ F ∈ wtPart O w j, ∀ n : ℕ, ∃ y ∈ Submodule.span O (entMon r j), Φ F - y ∈ m ^ n := by
  intro O G R σ _ _ _ _ _ η Ψ r c h1 h2 w Φ m hm hX j F hF n
  refine approx w Φ m (fun j => Submodule.span O (entMon r j))
    (Submodule.subset_span (one_mem_entMon r)) ?_ hm ?_ j F hF n
  · intro i j a ha b hb
    have h := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact mul_mem_entMon r hx hy
  · intro s
    obtain ⟨g, a, b, hw, he⟩ := hX s
    rw [hw, he]
    refine Submodule.sub_mem _ (emb_mem r c h1 h2 g a b) ?_
    by_cases h : wt6 a = wt6 b
    · rw [h, sub_self, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (one_mem_entMon r))
    · rw [unitaryEmbedding_residualRep_eq_zero_of_weight_ne η Ψ g a b h, map_zero]
      exact Submodule.zero_mem _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsTorusTwistEqLocalPointOfWeightedPres
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

open Polynomial in
private theorem pts_int {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have halg : IsIntegral ℚ_[l] x := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[l]) x).isIntegral
  have hmon : (minpoly ℚ_[l] x).Monic := minpoly.monic halg
  have hn : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [hn, spectralValue_le_one_iff hmon]
  constructor
  · intro hx n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hx, Polynomial.coeff_map]
    exact PadicInt.norm_le_one ((minpoly ℤ_[l] x).coeff n)
  · intro h
    have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hmon
    refine ⟨q, hqm, ?_⟩
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l), ← Polynomial.eval₂_map, hq,
      ← Polynomial.aeval_def]
    exact minpoly.aeval ℚ_[l] x

private theorem pts_unit {B K : Type} [CommRing B] [Field K] [Algebra B K] (hi : Function.Injective (algebraMap B K))
    (b : B) (h0 : algebraMap B K b ≠ 0) (h : IsIntegral B (algebraMap B K b)⁻¹) : IsUnit b := by
  classical
  obtain ⟨p, hpm, hp⟩ := h
  set y := (algebraMap B K b)⁻¹ with hy
  have hy0 : y ≠ 0 := inv_ne_zero h0
  letI : Invertible y := invertibleOfNonzero hy0
  have hrev := Polynomial.eval₂_reverse_mul_pow (algebraMap B K) y p
  rw [hp, invOf_eq_inv, hy, inv_inv] at hrev
  have hq : Polynomial.eval₂ (algebraMap B K) (algebraMap B K b) p.reverse = 0 :=
    (mul_eq_zero.mp hrev).resolve_right (pow_ne_zero _ (inv_ne_zero h0))
  rw [Polynomial.eval₂_at_apply] at hq
  have hq' : Polynomial.eval b p.reverse = 0 := hi (by rw [hq, map_zero])
  obtain ⟨r, hr⟩ := Polynomial.X_dvd_sub_C (p := p.reverse)
  have he := congrArg (Polynomial.eval b) hr
  rw [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.coeff_zero_reverse, hpm.leadingCoeff, hq',
    Polynomial.eval_mul, Polynomial.eval_X] at he
  have h1 : b * -Polynomial.eval b r = 1 := by
    rw [mul_neg, ← he]
    ring
  exact ⟨⟨b, _, h1, (mul_comm _ _).trans h1⟩, rfl⟩

private theorem automorphic_points_exist {O R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O ℤ R) (h : W.HasOrigin)
    (s : W.σ) : W.z s ∈ maximalIdeal R := mem_max_of_zero (W.origin h) (origin_presentation_var_eq_zero W h s)

private theorem pts_sur {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] [Field K] [Algebra O K]
    (f : R →ₐ[O] K) (x : R) (h0 : f x ≠ 0) (h3 : IsIntegral O (f x)⁻¹) : IsUnit x := by
  classical
  have hu : IsUnit (⟨f x, AlgHom.mem_range_self f x⟩ : f.range) :=
    pts_unit (B := f.range) (K := K) (fun a b hab => Subtype.ext hab) _ h0 h3.tower_top
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨r, hr⟩ := (AlgHom.mem_range f).1 v.2
  have hfr : f x * f r = 1 := by
    rw [hr]
    exact congrArg Subtype.val hv
  by_contra hxu
  have hm : x * r ∈ maximalIdeal R := Ideal.mul_mem_right r _ hxu
  have hunit := (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (x * r) hm).map f
  rw [map_sub, map_one, map_mul, hfr, sub_self] at hunit
  exact not_isUnit_zero hunit

private theorem pts_loc {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R] [IsLocalRing R]
    (f : R →ₐ[c.O] PadicAlgCl l) : IsLocPt f := by
  intro x hx
  by_contra hge
  push_neg at hge
  have h0 : f x ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hge
    linarith
  have hint : IsIntegral ℤ_[l] (f x)⁻¹ :=
    (pts_int _).mpr (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hge)
  exact hx (pts_sur f x h0 hint.tower_top)

private theorem fg_lemma {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {K : Type} [Field K]
    [Algebra O K] (P : Submodule O A) (I : Ideal A) (ξ : A →ₐ[O] K) (hξ : ∀ a ∈ I, ξ a = 0)
    (h : (Submodule.map (Ideal.Quotient.mkₐ O I).toLinearMap P).FG) :
    (Submodule.map ξ.toLinearMap P).FG := by
  have he : ξ.toLinearMap = (Ideal.Quotient.liftₐ I ξ hξ).toLinearMap ∘ₗ
      (Ideal.Quotient.mkₐ O I).toLinearMap := by
    ext a
    rfl
  rw [he, Submodule.map_comp]
  exact h.map _

set_option maxHeartbeats 1000000 in
theorem UpperTheory.exists_torus_twist_eq_localPoint_of_weightedPres :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {R S : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] [CommRing S] [Algebra c.O S] [IsCO c.O S]
          (W : WPres c.O ℤ R) (h : W.HasOrigin) (qh : R →ₐ[c.O] S), Function.Surjective qh → ∀ {κ : Type} (g : κ → W.A) (w : κ → ℤ), (∀ i, g i ∈ W.gr (w i)) →
          RingHom.ker qh = Ideal.span (Set.range fun i => (g i : R)) → M2 W.gr (Ideal.span (Set.range g)) →
          ∀ ξ : W.A →ₐ[c.O] PadicAlgCl l, OnS (Ideal.span (Set.range g)) ξ →
            ∃ (t : (PadicAlgCl l)ˣ) (f : S →ₐ[c.O] PadicAlgCl l), IsLocPt f ∧ act W.gr (tz t) ξ = f.comp (qh.comp W.A.val) := by
  intro l _ c R S _ _ _ _ _ _ W h qh hqh κ g w hg hk hM ξ hOn
  have hfg : (Submodule.map ξ.toLinearMap (W.gr 0)).FG := fg_lemma (W.gr 0) _ ξ hOn hM
  haveI : IsLocalRing c.O := IsDiscreteValuationRing.toIsLocalRing
  haveI : Module.Finite ℤ_[l] c.O := c.fin
  obtain ⟨hcomp, -, -, hinj, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI := hcomp
  haveI : Algebra.IsAlgebraic c.O (PadicAlgCl l) := Algebra.IsAlgebraic.mk fun x =>
    ((IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] (PadicAlgCl l)).mpr
      (Algebra.IsAlgebraic.isAlgebraic x)).extendScalars hinj
  obtain ⟨t, Ξ, hΞ, -⟩ := points_finite c.O ℤ R W (automorphic_points_exist W h) (PadicAlgCl l) ξ hfg
  have hker : ∀ a ∈ RingHom.ker qh, Ξ a = 0 := by
    intro a ha
    rw [hk] at ha
    have hle : Ideal.span (Set.range fun i => (g i : R)) ≤ RingHom.ker Ξ := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      have h1 := congrArg (fun φ : W.A →ₐ[c.O] PadicAlgCl l => φ (g i)) hΞ
      simp only [AlgHom.comp_apply, Subalgebra.coe_val] at h1
      rw [h1, act_of_mem W.gr t ξ (hg i), hOn (g i) (Ideal.subset_span ⟨i, rfl⟩), mul_zero]
    exact RingHom.mem_ker.mp (hle ha)
  let f : S →ₐ[c.O] PadicAlgCl l := (Ideal.Quotient.liftₐ (RingHom.ker qh) Ξ hker).comp
    (Ideal.quotientKerAlgEquivOfSurjective hqh).symm.toAlgHom
  have hf : ∀ r, f (qh r) = Ξ r := by
    intro r
    have hmk : (Ideal.quotientKerAlgEquivOfSurjective hqh).symm (qh r) =
        Ideal.Quotient.mk (RingHom.ker qh) r := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    show Ideal.Quotient.liftₐ (RingHom.ker qh) Ξ hker
      ((Ideal.quotientKerAlgEquivOfSurjective hqh).symm (qh r)) = Ξ r
    rw [hmk]
    rfl
  refine ⟨(zpowersHom (PadicAlgCl l)ˣ).symm t, f, pts_loc f, ?_⟩
  rw [show tz ((zpowersHom (PadicAlgCl l)ˣ).symm t) = t from Equiv.apply_symm_apply _ _, ← hΞ]
  refine AlgHom.ext fun a => ?_
  simp only [AlgHom.comp_apply, hf]
end

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

private theorem mop_rename_mem {O : Type} [CommRing O] {X : Type} [AddCommGroup X] {σ τ : Type} [Finite σ]
    (u : σ → τ) (wt : τ → X) (ws : σ → X) (h : ∀ s, wt (u s) = ws s) {j : X} {g : MvPowerSeries σ O}
    (hg : g ∈ wtPart O ws j) : MvPowerSeries.rename u g ∈ wtPart O wt j := fun n hn => by
  rw [MvPowerSeries.coeff_rename]
  refine Finset.sum_eq_zero fun d hd => hg d fun hj => hn ?_
  have hd' : Finsupp.mapDomain u d = n := by simpa using hd
  rw [← hd', ← hj, Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by rw [add_smul])]
  simp [h]

private theorem mop_homog {O : Type} [CommRing O] {X : Type} [AddCommGroup X] {σ : Type} [Fintype σ]
    (wt : σ → X) {κ : Type} [Finite κ] (g : κ → MvPowerSeries σ O) (c : κ → X)
    (hg : ∀ i, g i ∈ wtPart O wt (c i)) : IsHomog O wt (Ideal.span (Set.range g)) := by
  have hp : ∀ i, g i ∈ (WPres.free O wt).part (c i) := fun i => ⟨g i, hg i, rfl⟩
  exact (homog_span O _ X (WPres.free O wt) κ (fun i => ⟨g i, (WPres.free O wt).part_le_A (hp i)⟩) c hp).1

private theorem mop_cover {O Bl B S : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing Bl] [Algebra O Bl] [CommRing B] [Algebra O B] [CommRing S]
    [Algebra O S] [Nontrivial S] (WB : WPres O ℤ Bl) (i : Bl →ₐ[O] B) (W : WPres O ℤ B) {τ κ κ' : Type}
    (e : WB.σ ⊕ τ ≃ W.σ) (f : κ → MvPowerSeries W.σ O) (wf : κ → ℤ) (hrel : IsRelPres WB i W e f wf)
    (p : B →ₐ[O] S) (hp : Function.Surjective p) (n : κ' → B) (wn : κ' → ℤ) (hn : ∀ k, n k ∈ W.part (wn k))
    (hk : RingHom.ker p = Ideal.span (Set.range n)) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (WA : WPres O ℤ R) (ε : WB.σ ⊕ τ ≃ WA.σ)
      (qh : R →ₐ[O] S) (g : κ ⊕ κ' → WA.A),
      (∀ s, WA.wt (ε s) = W.wt (e s)) ∧ (∀ s, qh (WA.z (ε s)) = p (W.z (e s))) ∧
      RingHom.ker WA.π = (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => ε (.inl s)) ∧
      Function.Surjective qh ∧ (∀ k, g k ∈ WA.gr (Sum.elim wf wn k)) ∧
      RingHom.ker qh = Ideal.span (Set.range fun k => (g k : R)) ∧
      ∀ j, ∀ y ∈ W.part j, ∃ y' ∈ WA.part j, qh y' = p y := by
  obtain ⟨he1, -, hf, hker⟩ := hrel
  set J : Ideal (MvPowerSeries W.σ O) := (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)) with hJ
  have hJh : IsHomog O W.wt J := by
    obtain ⟨k, f0, c0, hf0, h0⟩ := ker_gen O ℤ WB.σ WB.wt _ WB.homog
    rw [hJ, h0, Ideal.map_span, ← Set.range_comp]
    exact mop_homog W.wt _ c0 fun t => mop_rename_mem _ W.wt WB.wt he1 (hf0 t)
  have hle : ∀ F ∈ J, (p.comp W.π) F = 0 := fun F hF => by
    have : W.π F = 0 := (hker ▸ Ideal.mem_sup_left hF : F ∈ RingHom.ker W.π)
    rw [AlgHom.comp_apply, this, map_zero]
  let qh : (MvPowerSeries W.σ O ⧸ J) →ₐ[O] S := Ideal.Quotient.liftₐ J (p.comp W.π) hle
  have hqh : ∀ F, qh (Ideal.Quotient.mk J F) = p (W.π F) := fun _ => rfl
  haveI : Nontrivial (MvPowerSeries W.σ O ⧸ J) := qh.toRingHom.domain_nontrivial
  haveI := co_mvps O O W.σ
  haveI : IsCO O (MvPowerSeries W.σ O ⧸ J) :=
    co_quot O _ _ (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)
  have hkm : RingHom.ker (Ideal.Quotient.mkₐ O J) = J := Ideal.Quotient.mkₐ_ker O J
  let WA : WPres O ℤ (MvPowerSeries W.σ O ⧸ J) :=
    { σ := W.σ, wt := W.wt, π := Ideal.Quotient.mkₐ O J, surj := Ideal.Quotient.mkₐ_surjective O J
      homog := by rw [hkm]; exact hJh }
  choose N hN hN' using hn
  have hG : ∀ k : κ ⊕ κ', Sum.elim f N k ∈ wtPart O W.wt (Sum.elim wf wn k) := by
    rintro (k | k)
    · exact hf k
    · exact hN k
  have hG' : ∀ k : κ ⊕ κ', Ideal.Quotient.mk J (Sum.elim f N k) ∈ WA.part (Sum.elim wf wn k) :=
    fun k => ⟨_, hG k, rfl⟩
  refine ⟨_, inferInstance, inferInstance, inferInstance, WA, e, qh, fun k => ⟨_, WA.part_le_A (hG' k)⟩,
    fun _ => rfl, fun _ => rfl, hkm, ?_, hG', ?_, ?_⟩
  · intro y
    obtain ⟨y, rfl⟩ := hp y
    obtain ⟨F, rfl⟩ := W.surj y
    exact ⟨_, hqh F⟩
  · refine le_antisymm (fun y hy => ?_) (Ideal.span_le.2 ?_)
    · obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective y
      have h1 : W.π F ∈ (Ideal.span (Set.range N)).map W.π := by
        have h2 : W.π ∘ N = n := funext hN'
        rw [Ideal.map_span, ← Set.range_comp, h2, ← hk]
        exact hy
      obtain ⟨G, hG1, hG2⟩ := (Ideal.mem_map_iff_of_surjective _ W.surj).1 h1
      have h3 : F - G ∈ J ⊔ Ideal.span (Set.range f) := by
        rw [← hker, RingHom.mem_ker, map_sub, hG2, sub_self]
      have h4 : (J ⊔ Ideal.span (Set.range f)) ⊔ Ideal.span (Set.range N) ≤
          (Ideal.span (Set.range fun k => Ideal.Quotient.mk J (Sum.elim f N k))).comap (Ideal.Quotient.mk J) := by
        refine sup_le (sup_le (fun y hy => ?_) (Ideal.span_le.2 ?_)) (Ideal.span_le.2 ?_)
        · rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hy]
          exact zero_mem _
        · rintro _ ⟨k, rfl⟩
          exact Ideal.subset_span ⟨.inl k, rfl⟩
        · rintro _ ⟨k, rfl⟩
          exact Ideal.subset_span ⟨.inr k, rfl⟩
      have h5 := h4 (Ideal.add_mem _ (Ideal.mem_sup_left h3) (Ideal.mem_sup_right hG1))
      rw [sub_add_cancel] at h5
      exact h5
    · rintro _ ⟨k | k, rfl⟩
      · have : W.π (f k) = 0 :=
          (hker ▸ Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩) : f k ∈ RingHom.ker W.π)
        show p (W.π (f k)) = 0
        rw [this, map_zero]
      · have : n k ∈ RingHom.ker p := hk ▸ Ideal.subset_span ⟨k, rfl⟩
        rw [← hN' k] at this
        exact this
  · rintro j _ ⟨F, hF, rfl⟩
    exact ⟨Ideal.Quotient.mk J F, ⟨F, hF, rfl⟩, rfl⟩

private theorem mop_card {α β : Type} [Finite α] [Finite β] (a : α → ℤ) (b : β → ℤ) (j : ℤ) :
    Nat.card {i // Sum.elim a b i = j} = Nat.card {i // a i = j} + Nat.card {i // b i = j} := by
  rw [Nat.card_congr Equiv.subtypeSum, Nat.card_sum]
  rfl

private theorem mop_nWt : Nat.card {i // nWt i = -1} = 2 ∧ Nat.card {i // nWt i = -2} = 1 ∧
    Nat.card {i // nWt i = 1} = 2 ∧ Nat.card {i // nWt i = 2} = 1 ∧ Nat.card {i // nWt i = 0} = 2 := by
  simp only [Nat.card_eq_fintype_card]
  decide

private theorem mop_mat_mem {O G R : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R] {r : G →* GG (m := 3) (R := R)}
    {W : WPres O ℤ R} (h : EntHomog r W) (g : G) (a b : Fin 3) : (r g).mat a b ∈ W.part (wt a b) := by
  rw [mat_eq_emb]
  exact add_mem (h g (.inl a) (.inl b)) (h g (.inl a) (.inr b))

private theorem mop_nEq_mem {O G R : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R] {r : G →* GG (m := 3) (R := R)}
    {W : WPres O ℤ R} (h : EntHomog r W) (c g₁ : G) (k : Fin 8) : nEq c g₁ r k ∈ W.part (nWt k) := by
  have h1 : (1 : R) ∈ W.part 0 := SetLike.GradedOne.one_mem
  have hm := mop_mat_mem h
  fin_cases k
  · exact sub_mem (hm c 0 0) h1
  · exact sub_mem (hm c 1 1) h1
  · exact hm c 0 1
  · exact hm c 1 0
  · exact hm c 0 2
  · exact hm c 2 0
  · exact sub_mem (hm g₁ 0 1) (hm _ 0 1)
  · exact sub_mem (hm g₁ 1 0) (hm _ 1 0)

private theorem mop_der_coord {O : Type} [CommRing O] (s : ℤˣ) (t : Oˣ) (a b : Fin 3 ⊕ Fin 3) :
    ∃ (u : O) (a' b' : Fin 3), wt a' b' = wt6 a - wt6 b ∧
      ∀ {R Q : Type} [CommRing R] [Algebra O R] [AddCommGroup Q] [Module O Q] (x : R →ₐ[O] O), ∀ D ∈ PtDer x Q,
        ∀ y : GG (m := 3) (R := R), GG.map (x : R →+* O) y = ⟨tor O t, s⟩ → ∀ c : O,
          D (emb y a b - algebraMap O R c) = u • D (y.mat a' b') := by
  obtain ⟨u, a', b', h1, h2⟩ := UpperTheory.exists_pointDerivation_emb_entry_eq_smul_mat_entry s t a b
  refine ⟨u, a', b', h1, fun x D hD y hy c => ?_⟩
  have h3 : D 1 = 0 := by simpa using hD 1 1
  rw [map_sub, h2 x D hD y hy, Algebra.algebraMap_eq_smul_one, map_smul, h3, smul_zero, sub_zero]

private theorem mop_main {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] {K : Type} [NormedField K] [Algebra O K]
    (hpts : ∀ {R S : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing S] [Algebra O S] [IsCO O S]
      (W : WPres O ℤ R) (h : W.HasOrigin) (qh : R →ₐ[O] S), Function.Surjective qh → ∀ {κ : Type} (g : κ → W.A) (w : κ → ℤ), (∀ i, g i ∈ W.gr (w i)) →
      RingHom.ker qh = Ideal.span (Set.range fun i => (g i : R)) → M2 W.gr (Ideal.span (Set.range g)) →
      ∀ ξ : W.A →ₐ[O] K, OnS (Ideal.span (Set.range g)) ξ →
        ∃ (t : Kˣ) (f : S →ₐ[O] K), IsLocPt f ∧ act W.gr (tz t) ξ = f.comp (qh.comp W.A.val))
    (hder : ∀ {R S : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing S] [Algebra O S] [IsCO O S]
      (W : WPres O ℤ R) (h : W.HasOrigin) (qh : R →ₐ[O] S), Function.Surjective qh → ∀ {κ : Type} (g : κ → W.A) (w : κ → ℤ), (∀ i, g i ∈ W.gr (w i)) →
      RingHom.ker qh = Ideal.span (Set.range fun i => (g i : R)) → M2 W.gr (Ideal.span (Set.range g)) →
      ∀ f : S →ₐ[O] K, IsLocPt f → ∀ D ∈ PtDer (f.comp (qh.comp W.A.val)) K, (∀ y ∈ Ideal.span (Set.range g), D y = 0) →
        ∃ F : S →ₐ[O] DualNumber K, dualFst F = f ∧ ∀ y : W.A, (F (qh y)).snd = D y)
    {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [Group H] [TopologicalSpace H]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
    {U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁)
    (B : Univ (BoxCond N ι hι U I)) (WB : WPres O ℤ (U.R ⧸ I)) (hM : Marks η Ψ cc g₁) (hL : LocGood U I)
    (hΨ : CharCont Ψ) (hN : ∀ g ∈ N, r0 η Ψ g = 1) (hWB : IsLocPres U I WB) (hbox : BoxPres B WB) :
    Nonempty (Model S K) := by
  classical
  obtain ⟨W, i, τ, κ, _, _, e, f, wf, hrel, hi, hcoord, hent, hcount⟩ := hbox
  obtain ⟨x, τ₀, _, w, φ, hx, hφ, hdim⟩ := hL.chart
  obtain ⟨hB, hBx, φb, hφb⟩ := UpperTheory.exists_origin_and_chart_of_isLocPres U I x w φ WB hx hφ hWB
  obtain ⟨p, hp, hpr, hpk⟩ := UpperTheory.exists_surjection_univ_normCond_ker_span_nEq cc g₁ B S hM.csq hM.ηc
  have hIx : I ≤ RingHom.ker x := fun y hy => by
    rw [← hBx]
    show WB.origin hB (Ideal.Quotient.mk I y) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hy, map_zero]
  obtain ⟨x₀, hx₀, -⟩ := (S.rep O).2 (baseLift O η Ψ hΨ)
    ⟨baseRepGL3_normalised_of_psi_eq_one η Ψ g₁ hM.Ψc, hN, x, GLift.ext hx, hIx⟩
  have hbase : IsBase η Ψ S.r.hom x₀ := congrArg GLift.hom hx₀
  have hSr : S.r.hom = push p B.r.hom := (congrArg GLift.hom hpr).symm
  have hnorm : Normalised cc g₁ S.r.hom := ((S.rep S.R).1 (AlgHom.id _ _)).1
  obtain ⟨R, _, _, _, WA, ε, qh, g, hw, hz, hkA, hq, hg, hkq, hpart⟩ :=
    mop_cover WB i W e f wf hrel p hp (nEq cc g₁ B.r.hom) nWt (mop_nEq_mem hent cc g₁) hpk
  have hwl : ∀ s, WA.wt (ε (.inl s)) = WB.wt s := fun s => (hw _).trans (hrel.1 s)
  have hl : ∀ s, ∃ h a b, WB.wt s = wt6 a - wt6 b ∧
      WB.z s = Ideal.Quotient.mk I (emb (U.r.hom h) a b - algebraMap O U.R (emb (r0 η Ψ (ι h)) a b)) ∧
      qh (WA.z (ε (.inl s))) = emb (S.r.hom (ι h)) a b - algebraMap O S.R (emb (r0 η Ψ (ι h)) a b) := fun s => by
    obtain ⟨h, a, b, h1, h2⟩ := hWB.1 s
    have h3 : WB.z s = Ideal.Quotient.mkₐ O I
        (emb (U.r.hom h) a b - algebraMap O U.R (emb (r0 η Ψ (ι h)) a b)) := by
      rw [h2, map_sub, AlgHom.commutes, emb_push]
      rfl
    refine ⟨h, a, b, h1, h3, ?_⟩
    have h4 : W.z (e (.inl s)) = i (WB.z s) := by
      rw [WPres.z, WPres.z, ← hrel.2.1, MvPowerSeries.rename_X]
    rw [hz, h4, h3, ← AlgHom.comp_apply i, map_sub, AlgHom.commutes, ← emb_push, hi, map_sub, AlgHom.commutes,
      hSr, emb_push]
    rfl
  have hco : ∀ s, ∃ γ a b, WA.wt s = wt6 a - wt6 b ∧
      qh (WA.z s) = emb (S.r.hom γ) a b - algebraMap O S.R (emb (r0 η Ψ γ) a b) := fun s => by
    obtain ⟨s | t, rfl⟩ := ε.surjective s
    · obtain ⟨h, a, b, h1, -, h3⟩ := hl s
      exact ⟨ι h, a, b, (hwl s).trans h1, h3⟩
    · obtain ⟨γ, a, b, h1, h2⟩ := hcoord t
      refine ⟨γ, a, b, (hw _).trans h1, ?_⟩
      rw [hz, h2, map_sub, AlgHom.commutes, hSr, emb_push]
  have hz0 : ∀ s, x₀ (qh (WA.z s)) = 0 := fun s => by
    obtain ⟨γ, a, b, -, h2⟩ := hco s
    rw [h2]
    exact base_coord hbase γ a b
  obtain ⟨h, hor⟩ := origin_of WA (x₀.comp qh) hz0
  have hbd : ∀ s, -2 ≤ WA.wt s ∧ WA.wt s ≤ 2 := fun s => by
    obtain ⟨γ, a, b, h1, -⟩ := hco s
    rw [h1]
    exact blockWeight_sub_mem_Icc a b
  set a : ℤ → ℕ := fun j => Nat.card {t // W.wt (e (.inr t)) = j} with ha
  have ha0 : ∀ j, ¬ (-2 ≤ j ∧ j ≤ 2) → a j = 0 := fun j hj => by
    haveI : IsEmpty {t // W.wt (e (.inr t)) = j} := ⟨fun t => hj (by rw [← t.2, ← hw]; exact hbd _)⟩
    exact Nat.card_of_isEmpty
  have hcnt : ∀ j, Nat.card {u // wf u = j} = a j + boxDef j := hcount
  have hgb : ∀ k, -2 ≤ Sum.elim wf nWt k ∧ Sum.elim wf nWt k ≤ 2 := by
    rintro (k | k)
    · by_contra hj
      have h1 := hcnt (wf k)
      have h2 : boxDef (wf k) = 0 := if_neg fun h3 => hj (by
        have := abs_le.1 h3
        exact ⟨by show -2 ≤ wf k; omega, by show wf k ≤ 2; omega⟩)
      rw [ha0 (wf k) hj, h2] at h1
      haveI : Nonempty {u // wf u = wf k} := ⟨⟨k, rfl⟩⟩
      exact Nat.card_pos.ne' h1
    · revert k
      show ∀ k, -2 ≤ nWt k ∧ nWt k ≤ 2
      decide
  have hgq : ∀ k, qh (g k) = 0 := fun k =>
    (hkq ▸ Ideal.subset_span ⟨k, rfl⟩ : (g k : R) ∈ RingHom.ker qh)
  obtain ⟨n1, n2, n3, n4, n5⟩ := mop_nWt
  obtain ⟨Q, hQ⟩ := UpperTheory.exists_eqns_of_weighted_generators WA.gr (WA.originA h) (a (-1) + 2) (a (-2) + 1) (a 1 + 3) (a 2 + 1) (a 0 + 3) g
    (Sum.elim wf nWt) hg (fun k => by
      show WA.origin h (g k) = 0
      rw [hor, AlgHom.comp_apply, hgq, map_zero]) hgb
    (by rw [mop_card, hcnt, n1]; rfl) (by rw [mop_card, hcnt, n2]; rfl) (by rw [mop_card, hcnt, n3]; rfl)
    (by rw [mop_card, hcnt, n4]; rfl) (by rw [mop_card, hcnt, n5]; rfl)
  obtain ⟨h', ψ, hψ, -⟩ := chart_add O ℤ _ WB hB τ₀ w φb hφb R WA τ ε hwl hkA
  refine ⟨{
    A := WA.A
    𝒜 := WA.gr
    x := WA.originA h
    wring := isWRing O R WA h hbd
    r := a (-1) + 2
    s := a (-2) + 1
    r' := a 1 + 3
    s' := a 2 + 1
    m := a 0 + 3
    Q := Q
    one_le := by omega
    smooth := ⟨τ₀ ⊕ τ, inferInstance, _, _, chart_gr O ℤ R WA h _ _ ψ hψ, fun j => ?_⟩
    q := qh.comp WA.A.val
    ker_q := ?_
    x₀ := x₀
    base := hbase
    x₀_q := by rw [← AlgHom.comp_assoc, ← hor]; rfl
    ent := fun γ a b => ?_
    dense := fun j y hy n => ?_
    pts := ?_
    der := ?_
    lift := ?_ }⟩
  · simp only [hw]
    rw [mop_card, hdim]
    show locDims j + a j = _
    have := ha0 j
    unfold locDims mDims
    split_ifs <;> first | omega | (subst_vars; omega)
  · rw [hQ]
    ext y
    rw [← (homog_span O R ℤ WA _ g _ hg).2 y, ← hkq]
    rfl
  · obtain ⟨y, hy, hy'⟩ := hpart _ _ (mop_mat_mem hent γ a b)
    refine ⟨⟨y, WA.part_le_A hy⟩, hy, ?_⟩
    rw [hSr]
    exact hy'
  · obtain ⟨F, hF, hFy⟩ := hy
    have h1 : (qh.comp WA.A.val) y = (qh.comp WA.π) F := congrArg qh hFy.symm
    rw [h1]
    exact UpperTheory.exists_span_entMon_approx_of_mem_wtPart η Ψ S.r.hom cc ((S.r.hasMult cc).trans hM.ηc) hnorm.atc WA.wt (qh.comp WA.π) _
      (fun s => mem_max_of_zero x₀ (hz0 s)) hco j F hF n
  · rw [hQ]
    exact hpts WA h qh hq g _ hg hkq
  · rw [hQ]
    exact hder WA h qh hq g _ hg hkq
  · intro a₀ _ D hD hDw xl hxl D₁ hD₁ hD₁I hD₁w hcomp
    have hxx : xl = x := ((U.rep O).2 (U.r.map x) trivial).unique (GLift.ext (hxl.trans hx.symm)) rfl
    subst hxx
    let Db : (U.R ⧸ I) →ₗ[O] O := (Submodule.liftQ (I.restrictScalars O) D₁ hD₁I) ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv O I).symm.toLinearMap
    have hDb : ∀ y, Db (Ideal.Quotient.mk I y) = D₁ y := fun _ => rfl
    have hxo : ∀ y, WB.origin hB (Ideal.Quotient.mk I y) = xl y := fun y => DFunLike.congr_fun hBx y
    refine UpperTheory.exists_base_pointDerivation_of_weight_homogeneous WB hB WA h ε hwl hkA qh x₀ hor.symm (Ideal.Quotient.mkₐ O _).toLinearMap
      (Ideal.Quotient.mkₐ_surjective O _) (-1) D hD (fun s hs => ?_) Db (fun y y' => ?_) (fun s hs => ?_) fun s => ?_
    · obtain ⟨γ, a, b, h1, h2⟩ := hco s
      obtain ⟨u, a', b', h3, h4⟩ := mop_der_coord (η γ) (Ψ γ) a b
      rw [h2, h4 x₀ D hD _ (DFunLike.congr_fun hbase γ), hDw γ a' b' (by rwa [h3, ← h1]), smul_zero]
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y'
      rw [← map_mul, hDb, hDb, hDb, hxo, hxo]
      exact hD₁ y y'
    · obtain ⟨γ, a, b, h1, h2, -⟩ := hl s
      obtain ⟨u, a', b', h3, h4⟩ := mop_der_coord (η (ι γ)) (Ψ (ι γ)) a b
      rw [h2, hDb, h4 xl D₁ hD₁ _ (DFunLike.congr_fun hxl γ), hD₁w γ a' b' (by rwa [h3, ← h1]), smul_zero]
    · obtain ⟨γ, a, b, -, h2, h5⟩ := hl s
      obtain ⟨u, a', b', -, h4⟩ := mop_der_coord (η (ι γ)) (Ψ (ι γ)) a b
      rw [h2, h5, hDb, h4 xl D₁ hD₁ _ (DFunLike.congr_fun hxl γ), h4 x₀ D hD _ (DFunLike.congr_fun hbase (ι γ)),
        map_smul, ← hcomp]
      rfl

theorem UpperTheory.V.U3.model_of_pres :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* (c.O)ˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
      {U : Univ (GCond.noCondition c.O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁) (B : Univ (BoxCond N ι hι U I)) (WB : WPres c.O ℤ (U.R ⧸ I)),
      l ≠ 2 → Marks η Ψ cc g₁ → LocGood U I → CharCont Ψ → (∀ g ∈ N, r0 η Ψ g = 1) →
      IsLocPres U I WB → BoxPres B WB → Nonempty (Model S (PadicAlgCl l)) := by
  intro l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S B WB _ hM hL hΨ hN hWB hbox
  haveI := (UpperTheory.V.abelian₂.dvr_finite l c.O).1
  haveI : IsNoetherianRing c.O := PrincipalIdealRing.isNoetherianRing
  exact mop_main (@UpperTheory.exists_torus_twist_eq_localPoint_of_weightedPres l _ c) (@UpperTheory.exists_dualNumber_point_of_pointDerivation_vanishing l _ c) S B WB hM hL hΨ hN hWB hbox

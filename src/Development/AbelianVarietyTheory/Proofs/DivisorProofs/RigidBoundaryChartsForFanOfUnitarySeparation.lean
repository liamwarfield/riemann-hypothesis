module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactificationIsModelOfCharts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleChartUnitaryBoundaryPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryBranchesDistinctPrimesToricChart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationSmoothSncBoundary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictNormalCrossingsDescentEtaleCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictNormalCrossingsDescentEtaleCompletion
open AlgebraicGeometry IsLocalRing ReciprocityTheory.AnForm.R GlobalTheory.Toroidal

namespace GlobalTheory.SncDescent

theorem eq_of_le_span_singleton {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {t : R} (ht : t ∈ maximalIdeal R) {Q : Ideal R} [hQ : Q.IsPrime] (h0 : Q ≠ ⊥)
    (hle : Q ≤ Ideal.span {t}) : Q = Ideal.span {t} := by
  refine le_antisymm hle ?_
  rw [Ideal.span_singleton_le_iff_mem]
  by_contra htQ
  refine h0 (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) Q
    (IsNoetherian.noetherian _) (fun x hx => ?_) ?_)
  · obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.1 (hle hx)
    exact Submodule.smul_mem_smul ht ((hQ.mem_or_mem hx).resolve_left htQ)
  · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]

theorem exists_rsp {A : Type} [CommRing A] [IsRegularLocalRing A] {m : ℕ} (p : Fin m → A)
    (hp : ∀ i, p i ∈ maximalIdeal A)
    (hind : ∀ a : Fin m → A, ∑ i, a i * p i ∈ maximalIdeal A ^ 2 → ∀ i, a i ∈ maximalIdeal A) :
    ∃ (n : ℕ) (r : Fin n → A) (T : Finset (Fin n)), FinalTheorems.Rsp A n r ∧ ∏ i ∈ T, r i = ∏ i, p i := by
  classical
  let τ : Fin m → maximalIdeal A := fun i => ⟨p i, hp i⟩
  have hτ : LinearIndependent (ResidueField A) (fun i => (maximalIdeal A).toCotangent (τ i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose a ha using fun j => residue_surjective (g j)
    have h1 : (maximalIdeal A).toCotangent (∑ j, a j • τ j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← ha j]
      rfl
    rw [Ideal.toCotangent_eq_zero] at h1
    have h2 : ∑ j, a j * p j ∈ maximalIdeal A ^ 2 := by
      simpa [τ] using h1
    rw [← ha i]
    exact (residue_eq_zero_iff _).mpr (hind a h2 i)
  obtain ⟨J, _, t, hs, hd⟩ := GlobalTheory.RegularQuotient.exists_extend A τ hτ
  let e := Fintype.equivFin (J ⊕ Fin m)
  refine ⟨_, Sum.elim t p ∘ e.symm, Finset.univ.map ⟨e ∘ Sum.inr, e.injective.comp Sum.inr_injective⟩,
    ⟨?_, ?_⟩, ?_⟩
  · rw [e.symm.surjective.range_comp, Set.Sum.elim_range]
    exact hs
  · rw [hd, Fintype.card_sum]
  · rw [Finset.prod_map]
    simp

theorem exists_rsp_of_flat {A R : Type} [CommRing A] [IsRegularLocalRing A] [CommRing R] [IsRegularLocalRing R]
    (φ : A →+* R) (hf : φ.Flat) (hm : (maximalIdeal A).map φ = maximalIdeal R) {m : ℕ} (t : Fin m → R)
    (ht : ∀ i, t i ∈ maximalIdeal R)
    (hind : ∀ a : Fin m → R, ∑ i, a i * t i ∈ maximalIdeal R ^ 2 → ∀ i, a i ∈ maximalIdeal R)
    (D : Ideal A) (hD : D.map φ = Ideal.span {∏ i, t i})
    (hinj : ∀ i i', (Ideal.span {t i}).comap φ = (Ideal.span {t i'}).comap φ → i = i') :
    ∃ (n : ℕ) (r : Fin n → A) (T : Finset (Fin n)), FinalTheorems.Rsp A n r ∧ D = Ideal.span {∏ i ∈ T, r i} := by
  classical
  algebraize [φ]
  have hloc : IsLocalHom (algebraMap A R) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : algebraMap A R a ∈ maximalIdeal R := hm ▸ Ideal.mem_map_of_mem _ ((mem_maximalIdeal a).2 hna)
    exact (mem_maximalIdeal _).1 this ha
  have hff : Module.FaithfullyFlat A R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hφ : Function.Injective φ := FaithfulSMul.algebraMap_injective A R
  have : IsDomain A := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have : IsDomain R := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have := isRegularRing_of_isRegularLocalRing A
  have : UniqueFactorizationMonoid A := uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
    exists_hasProjectiveDimensionLE_of_isRegularLocalRing isPrincipal_map_away_of_hasProjectiveDimensionLE A
  have hprime : ∀ i, Prime (t i) := fun i => prime_of_not_mem_sq (ht i) fun h => by
    have := hind (Pi.single i 1) (by simpa [Pi.single_apply] using h) i
    simp at this
  have h0 : ∏ i, t i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (hprime i).ne_zero
  have hDt : ∀ d ∈ D, ∀ i, t i ∣ φ d := fun d hd i =>
    (Finset.dvd_prod_of_mem t (Finset.mem_univ i)).trans
      (Ideal.mem_span_singleton.1 (hD ▸ Ideal.mem_map_of_mem φ hd))
  obtain ⟨d, hd, hd0⟩ : ∃ d ∈ D, d ≠ 0 := by
    refine Submodule.exists_mem_ne_zero_of_ne_bot fun h => h0 ?_
    rw [h, Ideal.map_bot, eq_comm, Ideal.span_singleton_eq_bot] at hD
    exact hD
  have key : ∀ i, ∃ p : A, Prime p ∧ (Ideal.span {t i}).comap φ = Ideal.span {p} := fun i => by
    have hP : (Ideal.span {t i}).IsPrime := (Ideal.span_singleton_prime (hprime i).ne_zero).2 (hprime i)
    have hne : (Ideal.span {t i}).comap φ ≠ ⊥ := fun h => hd0 (by
      rw [← Ideal.mem_bot, ← h]
      exact Ideal.mem_span_singleton.2 (hDt d hd i))
    obtain ⟨p, hp, hpp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot inferInstance hne
    refine ⟨p, hpp, ?_⟩
    have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hpp.ne_zero).2 hpp
    have : (Ideal.span {t i}).LiesOver ((Ideal.span {t i}).comap φ) := ⟨rfl⟩
    obtain ⟨Q, hQ, hQp, hQo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := Ideal.span {p})
      (q := (Ideal.span {t i}).comap φ) (Ideal.span {t i}) ((Ideal.span_singleton_le_iff_mem _).2 hp)
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      have : p ∈ (⊥ : Ideal R).comap φ := hQo.over.le (Ideal.mem_span_singleton_self p)
      exact hpp.ne_zero (hφ (by simpa using this))
    rw [← eq_of_le_span_singleton (ht i) hQ0 hQ]
    exact hQo.over.symm
  choose p hp hP using key
  have htp : ∀ i, t i ∣ φ (p i) := fun i =>
    Ideal.mem_span_singleton.1 (Ideal.mem_comap.1 ((hP i).ge (Ideal.mem_span_singleton_self _)))
  choose u hu using htp
  have hle : D ≤ Ideal.span {∏ i, p i} := fun x hx => by
    rw [Ideal.mem_span_singleton]
    refine Finset.prod_dvd_of_isRelPrime (fun i _ j _ hij => ?_) fun i _ => ?_
    · refine (hp i).irreducible.isRelPrime_iff_not_dvd.2 fun h => hij (hinj i j ?_)
      rw [hP, hP, Ideal.span_singleton_eq_span_singleton]
      exact (hp i).irreducible.associated_of_dvd (hp j).irreducible h
    · rw [← Ideal.mem_span_singleton, ← hP]
      exact Ideal.mem_span_singleton.2 (hDt x hx i)
  have hprod : φ (∏ i, p i) = (∏ i, t i) * ∏ i, u i := by
    simp only [map_prod, hu, Finset.prod_mul_distrib]
  have hU : IsUnit (∏ i, u i) := by
    have := Ideal.map_mono (f := φ) hle
    rw [hD, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_span_singleton, hprod] at this
    exact isUnit_of_dvd_one ((mul_dvd_mul_iff_left h0).1 (by simpa using this))
  have hu1 : ∀ i, IsUnit (u i) := fun i =>
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem u (Finset.mem_univ i)) hU
  obtain ⟨n, r, T, hr, hT⟩ := exists_rsp p (fun i => (mem_maximalIdeal _).2 (hp i).not_isUnit) fun a ha i => by
    have h1 := Ideal.mem_map_of_mem φ ha
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Ideal.map_pow, hm, map_sum] at h1
    have h2 := hind (fun j => φ (a j) * u j) (by
      convert h1 using 2 with j
      rw [map_mul, hu]; ring) i
    rw [mem_maximalIdeal, mem_nonunits_iff] at h2 ⊢
    exact fun h => h2 ((h.map φ).mul (hu1 i))
  refine ⟨n, r, T, hr, ?_⟩
  have h3 : D.map (algebraMap A R) = (Ideal.span {∏ i, p i}).map (algebraMap A R) := by
    change D.map φ = (Ideal.span {∏ i, p i}).map φ
    rw [hD, Ideal.map_span, Set.image_singleton, hprod, Ideal.span_singleton_mul_right_unit hU]
  rw [hT, ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := R) D, h3, Ideal.comap_map_eq_self_of_faithfullyFlat]

theorem coeff_single_eq_zero {k σ : Type} [Field k] {g : MvPowerSeries σ k}
    (hg : g ∈ maximalIdeal (MvPowerSeries σ k) ^ 2) (s : σ) :
    MvPowerSeries.coeff (Finsupp.single s 1) g = 0 := by
  classical
  rw [pow_two] at hg
  refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero]
  rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff, maximalIdeal_eq_bot, Ideal.mem_bot] at ha hb
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single]
  simp [Finset.Nat.antidiagonal_succ, ha, hb]

theorem exists_rsp_of_isEtaleCompletion : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (k : Type) [Field k] (m e : ℕ) (φ : A →+* ChartRing k m e) (D : Ideal A), IsEtaleCompletion φ → D.map φ = Ideal.span {∏ i : Fin m, bdParam k m e i} → (∀ i i' : Fin m, (Ideal.span {bdParam k m e i}).comap φ = (Ideal.span {bdParam k m e i'}).comap φ → i = i') → ∃ (n : ℕ) (r : Fin n → A) (T : Finset (Fin n)), FinalTheorems.Rsp A n r ∧ D = Ideal.span {∏ i ∈ T, r i} := by
  intro A _ _ _ k _ m e φ D hφ hD hinj
  classical
  have hR : IsRegularLocalRing (ChartRing k m e) := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k _
  have hA := (GlobalTheory.RegSmooth.isRegularLocalRing_of_isEtaleCompletion φ hφ).1
  refine exists_rsp_of_flat φ hφ.1 hφ.2.1 (bdParam k m e) (fun i => ?_) (fun a ha i => ?_) D hD hinj
  · rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff]
    simp
  · have h := coeff_single_eq_zero ha (Sum.inl i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single i] at h
    · rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff, maximalIdeal_eq_bot, Ideal.mem_bot]
      rw [bdParam, MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial] at h
      simpa using h
    · intro j _ hj
      rw [bdParam, MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, if_neg]
      simp [Finsupp.single_le_iff, Finsupp.single_apply, hj.symm]
    · simp

end GlobalTheory.SncDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictNormalCrossingsDescentEtaleCompletionStatement
open AlgebraicGeometry IsLocalRing ReciprocityTheory.AnForm.R GlobalTheory.Toroidal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictNormalCrossings_descent_etale_completion : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (k : Type) [Field k] (m e : ℕ) (φ : A →+* ChartRing k m e) (D : Ideal A), IsEtaleCompletion φ → D.map φ = Ideal.span {∏ i : Fin m, bdParam k m e i} → (∀ i i' : Fin m, (Ideal.span {bdParam k m e i}).comap φ = (Ideal.span {bdParam k m e i'}).comap φ → i = i') → ∃ (n : ℕ) (r : Fin n → A) (T : Finset (Fin n)), FinalTheorems.Rsp A n r ∧ D = Ideal.span {∏ i ∈ T, r i} := by
  first | exact @GlobalTheory.SncDescent.exists_rsp_of_isEtaleCompletion | exact GlobalTheory.SncDescent.exists_rsp_of_isEtaleCompletion | (intros; apply GlobalTheory.SncDescent.exists_rsp_of_isEtaleCompletion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncAtOfStalkIdEqSpanProd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncAtOfStalkIdEqSpanProd
open AlgebraicGeometry CategoryTheory ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem sncAt_of_stalkId_eq_span_prod : ∀ (Y : Scheme.{0}) [IsLocallyNoetherian Y] (I : Y.IdealSheafData) (y : Y),
    IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (n : ℕ) (r : Fin n → Y.presheaf.stalk y) (T : Finset (Fin n)),
    FinalTheorems.Rsp (Y.presheaf.stalk y) n r → FinalTheorems.stalkId I y = Ideal.span {∏ i ∈ T, r i} → FinalTheorems.SncAt I y := by
  intro Y _ I y hreg n r T hR hI
  refine ⟨hreg, ?_⟩
  choose O hO t ht using fun i => TopCat.Presheaf.exists_germ_eq Y.presheaf (r i)
  have hSo : IsOpen (⋂ i, (O i : Set Y)) := isOpen_iInter_of_finite fun i => (O i).2
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVS⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_iInter.2 hO) hSo
  have hle : ∀ i, V ≤ O i := fun i z hz => Set.mem_iInter.1 (hVS hz) i
  let f : Fin n → Γ(Y, V) := fun i => Y.presheaf.map (homOfLE (hle i)).op (t i)
  have hgf : ∀ i, Y.presheaf.germ V y hyV (f i) = r i := fun i => by
    simp only [f]; rw [TopCat.Presheaf.germ_res_apply]; exact ht i
  let a : Γ(Y, V) := ∏ i ∈ T, f i
  have hga : Y.presheaf.germ V y hyV a = ∏ i ∈ T, r i := by
    simp only [a, map_prod, hgf]
  let V' : Y.affineOpens := ⟨V, hV⟩
  haveI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian V'
  have hmap := WMult.stalkId_eq_map_germ I y V' hyV
  rw [hI] at hmap

  obtain ⟨h₂, hu₂, hm₂⟩ := IrreducibleComponentPreimages.exists_unit_mul_mem_of_germ_mem hV y hyV (I.ideal V') (t := a)
    (by show _ ∈ Ideal.map (Y.presheaf.germ V y hyV).hom (I.ideal V')
        rw [← hmap, hga]; exact Ideal.mem_span_singleton_self _)

  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (I.ideal V') : (I.ideal V').FG)
  have hgen : ∀ g : s, ∃ d : Γ(Y, V), IsUnit (Y.presheaf.germ V y hyV d) ∧ d * g.1 ∈ Ideal.span {a} := by
    intro g
    apply IrreducibleComponentPreimages.exists_unit_mul_mem_of_germ_mem hV y hyV
    have hg : g.1 ∈ I.ideal V' := hs ▸ Submodule.subset_span g.2
    have : Y.presheaf.germ V y hyV g.1 ∈ Ideal.map (Y.presheaf.germ V y hyV).hom (I.ideal V') :=
      Ideal.mem_map_of_mem _ hg
    rw [← hmap, ← hga, ← Set.image_singleton, ← Ideal.map_span] at this
    exact this
  choose d hdu hdm using hgen
  let h₁ : Γ(Y, V) := ∏ g : s, d g
  have hu₁ : IsUnit (Y.presheaf.germ V y hyV h₁) := by
    simp only [h₁, map_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun g _ => hdu g
  have hcol : I.ideal V' ≤ Submodule.comap (LinearMap.mulLeft Γ(Y, V) h₁) (Ideal.span {a}) := by
    rw [← hs, Submodule.span_le]
    classical
    intro g hg
    show h₁ * g ∈ Ideal.span {a}
    have e : h₁ = (∏ g' ∈ Finset.univ.erase (⟨g, hg⟩ : s), d g') * d ⟨g, hg⟩ :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ _)).symm
    rw [e, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hdm ⟨g, hg⟩)
  let h : Γ(Y, V) := h₁ * h₂
  have hyD : y ∈ Y.basicOpen h := (Y.mem_basicOpen h y hyV).2 (by
    simp only [h, map_mul]; exact hu₁.mul hu₂)
  let D : Y.affineOpens := Y.affineBasicOpen (U := V') h
  let ρ := Y.presheaf.map (homOfLE (Y.basicOpen_le h)).op
  have hρ : IsUnit (ρ h) := Y.toRingedSpace.isUnit_res_basicOpen h
  have hρ₁ : IsUnit (ρ h₁) := by
    simp only [h, map_mul] at hρ; exact isUnit_of_mul_isUnit_left hρ
  have hρ₂ : IsUnit (ρ h₂) := by
    simp only [h, map_mul] at hρ; exact isUnit_of_mul_isUnit_right hρ
  refine ⟨D, hyD, n, fun i => ρ (f i), T, ?_, ?_⟩
  · have e : (fun i => Y.presheaf.germ D.1 y hyD (ρ (f i))) = r := by
      funext i
      show Y.presheaf.germ (Y.basicOpen h) y hyD (ρ (f i)) = r i
      rw [TopCat.Presheaf.germ_res_apply]
      exact hgf i
    rw [e]; exact hR
  · rw [← I.map_ideal' (U := D) (V := V') (homOfLE (Y.basicOpen_le h)).op]
    show Ideal.map ρ.hom (I.ideal V') = Ideal.span {∏ i ∈ T, ρ (f i)}
    have ha : ∏ i ∈ T, ρ (f i) = ρ a := by simp only [a, map_prod]
    rw [ha]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have h1 : h₁ * x ∈ Ideal.span {a} := hcol hx
      have h2 : ρ (h₁ * x) ∈ Ideal.span {ρ a} := by
        rw [← Set.image_singleton, ← Ideal.map_span]; exact Ideal.mem_map_of_mem _ h1
      rw [map_mul, Ideal.unit_mul_mem_iff_mem _ hρ₁] at h2
      exact h2
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have h2 : ρ (h₂ * a) ∈ Ideal.map ρ.hom (I.ideal V') := Ideal.mem_map_of_mem _ hm₂
      rw [map_mul, Ideal.unit_mul_mem_iff_mem _ hρ₂] at h2
      exact h2
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncAtOfStalkIdEqSpanProdStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sncAt_of_stalkId_eq_span_prod_of_isRegularLocalRing : ∀ (Y : Scheme.{0}) [IsLocallyNoetherian Y] (I : Y.IdealSheafData) (y : Y), IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (n : ℕ) (r : Fin n → Y.presheaf.stalk y) (T : Finset (Fin n)), FinalTheorems.Rsp (Y.presheaf.stalk y) n r → FinalTheorems.stalkId I y = Ideal.span {∏ i ∈ T, r i} → FinalTheorems.SncAt I y := by
  first | exact @GlobalTheory.sncAt_of_stalkId_eq_span_prod | exact GlobalTheory.sncAt_of_stalkId_eq_span_prod | (intros; apply GlobalTheory.sncAt_of_stalkId_eq_span_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationSmoothSncBoundary
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChartSmooth

theorem trdeg_residueField_eq_zero {F : Type} [Field F] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of F))
    [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    letI : Algebra F (X.residueField x) := (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra
    Algebra.trdeg F (X.residueField x) = 0 := by
  letI : Algebra F (X.residueField x) := (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have h : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := inferInstance
  rw [← Spec.map_preimage (X.fromSpecResidueField x ≫ f), HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  have : Algebra.FiniteType F (X.residueField x) := RingHom.finiteType_algebraMap.mp h
  have : Module.Finite F (X.residueField x) := finite_of_finite_type_of_isJacobsonRing F _
  have : Algebra.IsAlgebraic F (X.residueField x) := Algebra.IsAlgebraic.of_finite F _
  exact trdeg_eq_zero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)} {Z : Scheme.{0}} {zs : Z ⟶ Sp c.F} {i : Xo.XF c ⟶ Z} {OZ : LB Z}
  {N d : ℕ} {J : Z.IdealSheafData} {S : Scheme.{0}} {π : S ⟶ Z} {j : Xo.XF c ⟶ S} {BD : EffCartierData S}

theorem locallyOfFiniteType (h : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD) : LocallyOfFiniteType (π ≫ zs) := by
  obtain ⟨-, -, -, -, ⟨-, hproj, -⟩, -⟩ := h
  obtain ⟨M, i', hi', hcomp⟩ := hproj
  haveI := hi'
  haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
  rw [← hcomp]
  infer_instance

theorem smooth_j (h : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD) :
    SmoothOfRelativeDimension Dw.dim (j ≫ π ≫ zs) := by
  obtain ⟨⟨-, -, -, -, hizs, -⟩, -, -, -, ⟨-, -, -, -, hji, -⟩, -⟩ := h
  rw [← Category.assoc, hji, hizs]
  exact Formalism.L2.Pj.smoothOfRelativeDimension_strK Xo c

theorem isRegularLocalRing_stalk [IsOpenImmersion j] (h : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD)
    (hU : ∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) (x : S) : IsRegularLocalRing (S.presheaf.stalk x) := by
  haveI := locallyOfFiniteType h
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  by_cases hx : x ∈ Set.range j
  · obtain ⟨z, rfl⟩ := hx
    haveI := smooth_j h
    haveI : Smooth (j ≫ π ≫ zs) := SmoothOfRelativeDimension.smooth Dw.dim _
    haveI := GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth_field (j ≫ π ≫ zs) z
    exact IsRegularLocalRing.of_ringEquiv (asIso (j.stalkMap z)).commRingCatIsoToRingEquiv.symm
  · obtain ⟨k, _, m, e, C, ξ, a, -, -, rfl, hE, -⟩ := hU x hx
    haveI : IsRegularLocalRing (ChartRing k m e) := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin e)
    exact (GlobalTheory.RegSmooth.isRegularLocalRing_of_isEtaleCompletion _ hE).1

theorem smooth [IsOpenImmersion j] (h : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD)
    (hU : ∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) : SmoothOfRelativeDimension Dw.dim (π ≫ zs) := by
  haveI := locallyOfFiniteType h
  refine GlobalTheory.RegSmooth.smoothOfRelativeDimension_of_isRegularLocalRing (π ≫ zs) Dw.dim fun x hx => ⟨isRegularLocalRing_stalk h hU x, ?_⟩
  obtain ⟨a, b, ha, hb, hab⟩ := stalk_dim_add_trdeg_of_uPoinOnX h x
  have h0 := trdeg_residueField_eq_zero (π ≫ zs) x hx
  have hb0 : b = 0 := by
    have := hb.symm.trans h0
    exact_mod_cast this
  rw [ha, ← hab, hb0, add_zero]

end GlobalTheory.UChartSmooth

namespace GlobalTheory.UChartSmooth

theorem smooth_and_snc : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → SmoothOfRelativeDimension Dw.dim (π ≫ zs) ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hno Z zs i OZ N d J S π j _ BD h hsep hU
  refine ⟨smooth h hU, ?_⟩
  haveI := locallyOfFiniteType h
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  intro x
  by_cases hx : x ∈ Set.range j
  · refine sncAt_of_not_mem _ x ?_ (isRegularLocalRing_stalk h hU x)
    intro hc
    exact hc hx
  · obtain ⟨k, _, m, e, C, ξ, a, hT, hy, rfl, hE, hid, hrange, -⟩ := hU x hx
    have hs' := GlobalTheory.T.boundaryBranches_distinct_primes_toricChart Xo c φ hpq hfan hno zs i OZ N d J π j BD h hsep hU k m e C ξ hT hy hx hE hid hrange
    obtain ⟨hm, hs, -⟩ := hT
    have hprod : ∏ i, C.s i = ∏ i : Fin m, bdParam k m e i :=
      Fintype.prod_equiv (finCongr hm) (fun i => C.s i) (fun i => bdParam k m e i) (fun i => by rw [hs i]; rfl)
    rw [hprod] at hid
    obtain ⟨n, r, T, hr, hD⟩ := GlobalTheory.T.strictNormalCrossings_descent_etale_completion _ k m e _ _ hE hid hs'
    exact GlobalTheory.T.sncAt_of_stalkId_eq_span_prod_of_isRegularLocalRing S _ _ (isRegularLocalRing_stalk h hU _) n r T hr hD
end GlobalTheory.UChartSmooth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationSmoothSncBoundaryStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidalCompactification_smooth_snc_boundary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → SmoothOfRelativeDimension Dw.dim (π ≫ zs) ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) := by
  first | exact @GlobalTheory.UChartSmooth.smooth_and_snc | exact GlobalTheory.UChartSmooth.smooth_and_snc | (intros; apply GlobalTheory.UChartSmooth.smooth_and_snc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartsOfUpre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChartOf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem inv_apply_self {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (x : X) : inv f (f x) = x := by
  rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl

theorem chart_of_data {φ : InvFun (𝓞 E)} (Y : Model Xo c (RingHom.id c.F)) (BD' : EffCartierData Y.X) (d : ℕ)
    (x : gen Y) {k : Type} [Field k] {m e : ℕ} (ξ' : Sp (ChartRing k m e) ⟶ gen Y) (t : SAB H (Sp (ChartRing k m e)))
    (P : PELUnif (maximalIdeal (ChartRing k m e)) t) (n : ℕ) (h : n = m) (s : Fin n → ChartRing k m e)
    (hs : ∀ i, s i = bdParam k m e (Fin.cast h i)) (δ : Fin n → LinearMap.BilinForm ℤ P.D.toPre.X) (a : Fin n → ℕ)
    (hx : ξ' (closedPoint _) = x) (het : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ').hom)
    (hid : idlAlong (genBdIdeal Y) ξ' = Ideal.span {∏ i, s i})
    (hset : ∀ p : Sp (ChartRing k m e), ξ' p ∈ genBd Y ↔ ∏ i, s i ∈ p.asIdeal)
    (hsab : Nonempty (SABMap t Y.t (ξ' ≫ genι Y)))
    (hmono : IsMonomial P.D.toPre s (fun i => (l.M' : ℤ) • δ i))
    (hrank : Module.finrank (𝓞 E) P.D.toPre.X ≤ min Dw.p Dw.q) (hcone : IsCone H.bar φ δ)
    (ha : ∀ i, (a i : ℝ) = d * φ.evalZ ((l.M' : ℤ) • δ i))
    (hBD : idlAlong BD'.idealSheaf (ξ' ≫ genι Y) = Ideal.span {∏ i, s i ^ a i})
    (hrig : GlobalTheory.RigChart.IsRigid P.D.toPre s (fun i => (l.M' : ℤ) • δ i)) :
    GlobalTheory.MumfordChart.HasChartOf φ Y BD' d x ∧ GlobalTheory.RigChart.HasRigidChart Y x := by
  subst h
  obtain rfl : s = bdParam k n e := funext fun i => by simpa using hs i
  have hmem : ∀ i, (l.M' : ℤ) • δ i ∈ levelForms H l.M' P.D.toPre.X := fun i =>
    (mem_levelForms_iff_smul (GlobalTheory.MumfordChart.level_ne_zero l)).2
      ⟨δ i, (balForms_eq_levelForms H P.D.toPre.X) ▸ hcone.mem i, rfl⟩
  let gam : Fin n → levelForms H l.M' P.D.toPre.X := fun i => ⟨(l.M' : ℤ) • δ i, hmem i⟩
  have hgam : ∀ i, (gam i : LinearMap.BilinForm ℤ P.D.toPre.X) = (l.M' : ℤ) • δ i := fun _ => rfl
  have hpb : IsPartOfBasis gam := hcone.isPartOfBasis_level (GlobalTheory.MumfordChart.level_ne_zero l) hgam
  exact ⟨⟨k, _, n, e, ξ', t, P, gam, δ, a, hx, het, hid, fun p => (hset p).trans Iff.rfl, hsab, hmono, hrank, hcone, hgam,
      ha, hBD⟩,
    ⟨k, _, n, e, ξ', t, P, gam, hx, het, hid, hset, hsab, hmono, hpb, hrig⟩⟩

end GlobalTheory.UChartOf

namespace GlobalTheory.UChartOf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem charts_of_upre {φ : InvFun (𝓞 E)} {S : Scheme.{0}} {j : Xo.XF c ⟶ S} [IsOpenImmersion j]
    {BD : EffCartierData S} {d : ℕ} (Y : Model Xo c (RingHom.id c.F)) (ε : Y.X ≅ S) (hj : Y.j ≫ ε.hom = j)
    (hsab : ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C →
      ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → Nonempty (SABMap C.t Y.t (ξ ≫ ε.inv)))
    (hpre : ∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) (x : gen Y) (hx : x ∈ genBd Y) :
    GlobalTheory.MumfordChart.HasChartOf φ Y (BD.pull ε.hom (BD.keepsRegular_of_flat _)) d x ∧
      GlobalTheory.RigChart.HasRigidChart Y x := by
  let π : gen Y ⟶ S := genι Y ≫ ε.hom
  have hjQ : Y.jQ ≫ π = j := by
    simp only [π, ← Category.assoc]
    exact hj
  have hrange : ∀ w : gen Y, w ∈ Set.range Y.jQ ↔ π w ∈ Set.range j := by
    intro w
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [← hjQ]; rfl⟩
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      have : π (Y.jQ z) = π w := by rw [← hz, ← hjQ]; rfl
      rw [← inv_apply_self π (Y.jQ z), this, inv_apply_self]
  have hx' : π x ∉ Set.range j := fun h => hx ((hrange x).2 h)
  obtain ⟨k, _, m, e, C, ξ, a, htaut, hy, hcl, het, hbd, hset, ha, hBD⟩ := hpre (π x) hx'
  obtain ⟨hm, hs, -, -, hrig, -, -⟩ := id htaut
  let ξ' : Sp (ChartRing k m e) ⟶ gen Y := ξ ≫ inv π
  have hξ : ξ' ≫ π = ξ := by simp [ξ']
  have hξg : ξ' ≫ genι Y = ξ ≫ ε.inv := by
    simp only [ξ', π, IsIso.inv_comp, IsIso.Iso.inv_hom, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hvan : (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl).comap π = genBdIdeal Y :=
    GlobalTheory.vanishingIdeal_comap_of_isOpenImmersion (gen Y) S π _ (genBd Y) fun w =>
      (not_congr (hrange w)).trans Iff.rfl
  refine chart_of_data Y _ d x ξ' C.t C.P C.m hm C.s hs C.δ a ?_ ?_ ?_ ?_ ?_ C.mono C.rank C.cone ha ?_ hrig.1
  · change inv π (ξ (closedPoint _)) = x
    rw [hcl, inv_apply_self]
  · exact GlobalTheory.Member.isEtaleCompletion_stalkClosedPointTo_comp_iso ξ (inv π) het
  · rw [← hvan, GlobalTheory.TorRef.idlAlong_comap, hξ]
    exact hbd
  · intro p
    rw [mem_genBd, hrange, ← Scheme.Hom.comp_apply, hξ, hset p, not_not]
  · rw [hξg]
    exact hsab C htaut ξ hy
  · rw [EffCartierData.idealSheaf_pull, GlobalTheory.TorRef.idlAlong_comap, hξg, Category.assoc, ε.inv_hom_id,
      Category.comp_id]
    exact hBD

end GlobalTheory.UChartOf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidBoundaryChartsForFanOfUnitarySeparation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChartJoin

theorem rigidForFan_of_uStB : UStB → GlobalTheory.RigChart.RigidForFan := by
  intro hU E _ _ _ H Dw hpq φ hpol hnsi l Xo c
  obtain ⟨Z, zs, i, OZ, N, d, J, S, π, j, BD, hUP, hSep⟩ := hU E H Dw hpq φ hpol hnsi l Xo c
  obtain ⟨⟨-, -, -, -, -, hOZ, -⟩, ⟨hN, hdet⟩, -, ⟨hd, hJ, -⟩, ⟨-, -, hj, -, hji, -, hBD, -⟩, k₀, hamp⟩ := id hUP
  haveI := hj
  have hpre := GlobalTheory.T.exists_tripleChart_unitary_boundary_point Xo c φ hpq hpol hnsi zs i OZ N d J π j BD hUP hSep
  obtain ⟨Y, ε, hYj, hYs, hsab⟩ := GlobalTheory.T.unitary_compactification_isModel_of_charts Xo c φ hpq hpol hnsi zs i OZ N d J π j BD hUP hSep hpre
  obtain ⟨hsm, hsnc⟩ := GlobalTheory.T.toroidalCompactification_smooth_snc_boundary Xo c φ hpq hpol hnsi zs i OZ N d J π j BD hUP hSep hpre
  have hch := fun x hx => GlobalTheory.UChartOf.charts_of_upre Y ε hYj hsab hpre x hx
  have hYi : Y.j ≫ ε.hom ≫ π = i := by rw [← Category.assoc, hYj, hji]
  refine ⟨Y, BD.pull ε.hom (BD.keepsRegular_of_flat _), d, N * max k₀ 1, hd, ?_, ?_, ?_, ?_, fun x hx => (hch x hx).1, ?_,
    fun x hx _ => (hch x hx).2⟩
  · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  ·
    have h2 : genStr Y ≫ spMap (RingHom.id c.F) = genStr Y := by
      rw [show spMap (RingHom.id c.F) = 𝟙 (Sp c.F) by simp [spMap]]
      exact Category.comp_id _
    have e : genStr Y = (genι Y ≫ ε.hom) ≫ (π ≫ zs) := by
      rw [← h2, ← pullback.condition]
      exact (congrArg (genι Y ≫ ·) hYs).trans (by simp only [Category.assoc])
    rw [e]
    have := smoothOfRelativeDimension_comp (n := 0) (m := Dw.dim) (genι Y ≫ ε.hom) (π ≫ zs)
    rwa [zero_add] at this
  ·
    refine GlobalTheory.SncIso.snc_vanishingIdeal_of_isIso (genι Y ≫ ε.hom) j.opensRange.compl (genBd Y) (fun a => ?_) hsnc
    rw [mem_genBd]
    show a ∉ Set.range Y.jQ ↔ (genι Y ≫ ε.hom) a ∉ Set.range j
    refine not_congr ⟨?_, ?_⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [← hYj]; rfl⟩
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      have h1 : (genι Y ≫ ε.hom) (Y.jQ z) = (genι Y ≫ ε.hom) a := by
        rw [← hz, ← hYj]; rfl
      rw [← GlobalTheory.UChartOf.inv_apply_self (genι Y ≫ ε.hom) (Y.jQ z), h1, GlobalTheory.UChartOf.inv_apply_self]
  ·
    intro x hx hab
    rw [EffCartierData.idealSheaf_pull, hBD, Scheme.IdealSheafData.support_comap,
      Scheme.IdealSheafData.support_comap] at hx
    obtain ⟨g, rfl⟩ : ∃ g : gen Y, genι Y g = x := ⟨inv (genι Y) x, by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    have hg : g ∈ Set.range Y.jQ := by rw [← Y.ab_gen]; exact hab
    obtain ⟨z, rfl⟩ := hg
    refine hJ _ hx ⟨z, ?_⟩
    rw [← hYi]
    rfl
  ·
    intro hL
    have hk : k₀ ≤ max k₀ 1 := le_max_left _ _
    have isLB {X : Scheme} (D : EffCartierData X) : D.lb.IsLB := by
      refine { cover := D.cover, g_self := ?_, cocycle := ?_ }
      · intro i
        exact Units.ext (D.eq_trans_on i i le_rfl le_rfl (c := 1) (_root_.one_mul _).symm).symm
      · intro i j k
        have hi : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U i := inf_le_left.trans inf_le_left
        have hj : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U j := inf_le_left.trans inf_le_right
        have hk : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U k := inf_le_right
        refine Units.ext (D.eq_trans_on i k hi hk ?_)
        rw [D.trans_spec_on i j hi hj, D.trans_spec_on j k hj hk, ← _root_.mul_assoc]
        rfl
    have hBL := isLB BD
    have hL' := isLB (BD.pull ε.hom (BD.keepsRegular_of_flat _))
    have hA := (hamp _ hk).pull_of_isAffineHom ε.hom
    have hAS : (CechPic.tens (lbPow (OZ.pull π) (max k₀ 1)) (CechPic.dual BD.lb)).IsLB :=
      CechPic.isLB_tens (isLB_lbPow (LB.isLB_pull hOZ π) _) (CechPic.isLB_dual hBL)
    have hP : (GlobalTheory.TorRef.polOf Y (N * max k₀ 1) (BD.pull ε.hom (BD.keepsRegular_of_flat _))).IsLB :=
      CechPic.isLB_tens (isLB_lbPow hL _) (CechPic.isLB_dual hL')
    refine hA.of_lbIso hP ((CechPic.cls_eq_iff hP (LB.isLB_pull hAS ε.hom)).1 ?_)
    have e1 : CechPic.cls _ (LB.isLB_pull hOZ (ε.hom ≫ π)) = N • CechPic.cls _ hL := by
      rw [(CechPic.cls_eq_iff _ (isLB_lbPow hL N)).2 (hdet Y (ε.hom ≫ π) hYi hL), CechPic.cls_lbPow hL]
    have e2 : CechPic.cls _ hL' = CechPic.pull ε.hom (CechPic.cls _ hBL) := by
      rw [(CechPic.cls_eq_iff _ (LB.isLB_pull hBL _)).2 (BD.lbIso_pull _ _), CechPic.cls_pull hBL]
    rw [CechPic.cls_pull hOZ, CechPic.pull_comp] at e1
    refine (CechPic.cls_tens (isLB_lbPow hL _) (CechPic.isLB_dual hL') hP).trans ?_
    rw [CechPic.cls_pull hAS ε.hom,
      CechPic.cls_tens (isLB_lbPow (LB.isLB_pull hOZ π) _) (CechPic.isLB_dual hBL),
      CechPic.cls_lbPow hL, CechPic.cls_lbPow (LB.isLB_pull hOZ π), CechPic.cls_dual hL', CechPic.cls_dual hBL,
      CechPic.cls_pull hOZ π, e2, map_add, map_nsmul, map_neg, e1, mul_nsmul]

end GlobalTheory.UChartJoin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidBoundaryChartsForFanOfUnitarySeparationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidBoundaryChartsForFan_of_unitarySeparation : UStB → GlobalTheory.RigChart.RigidForFan := by
  first | exact @GlobalTheory.UChartJoin.rigidForFan_of_uStB | exact GlobalTheory.UChartJoin.rigidForFan_of_uStB | (intros; apply GlobalTheory.UChartJoin.rigidForFan_of_uStB <;> assumption)
end

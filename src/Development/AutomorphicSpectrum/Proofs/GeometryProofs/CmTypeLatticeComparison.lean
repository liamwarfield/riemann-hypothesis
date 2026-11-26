module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelConstantsExtension
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsMultiHomogIdealMap
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeLatticeComparison
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeLatticeComparison
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptStalk

theorem isIntegrallyClosed_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (hg : IsCptGen ξ) (q : Cpt ξ) : IsIntegrallyClosed (regAt ξ q) := by
  let e : X.presheaf.stalk q.1 ≃+* regAt ξ q :=
    RingEquiv.ofBijective (genMap ξ q).rangeRestrict
      ⟨fun x y hxy => hg.inj q (congrArg Subtype.val hxy), (genMap ξ q).rangeRestrict_surjective⟩
  haveI := (hn q.1).1
  haveI := (hn q.1).2
  exact IsIntegrallyClosed.of_equiv e

theorem asIdeal_eq_bot {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hg : IsCptGen ξ)
    {F : Type} [Field F] [NumberField F] (s : X ⟶ Spec (CommRingCat.of (𝓞 F))) (b : 𝓞 F →+* Ω)
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom b)) {p : Cpt ξ} (hp : p ∈ genFibre ℤ ξ) :
    (s p.1).asIdeal = ⊥ := by
  letI : Algebra (𝓞 F) Ω := b.toAlgebra
  have hreg := ConstReg.regular_const X Ω ξ (𝓞 F) s hs p
  refine (Submodule.eq_bot_iff _).2 fun o ho => ?_
  by_contra h0
  have hn : Ideal.absNorm (Ideal.span {o}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact h0
  have hmem : ((Ideal.absNorm (Ideal.span {o}) : ℕ) : 𝓞 F) ∈ (s p.1).asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).2 ho (Ideal.absNorm_mem _)
  have hu := hp ((Ideal.absNorm (Ideal.span {o}) : ℕ) : ℤ) (by exact_mod_cast hn)
  have hu' : unitAt ξ p (algebraMap (𝓞 F) Ω ((Ideal.absNorm (Ideal.span {o}) : ℕ) : 𝓞 F)) := by
    simpa using hu
  exact ((hreg _).2 hg).1 hu' hmem

section Eig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
  {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)
  {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] {ξ : Spec (CommRingCat.of Ω₀) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
  {i : Ω₀ →+* Ω} {V V' : Type} [AddCommGroup V] [Module Ω₀ V] [AddCommGroup V'] [Module Ω V']
  {M : LieModel t.G ξ V} {M' : LieModel t'.G ξ' V'} {ρ : 𝓞 E →+* Module.End Ω₀ V}
  {ρ' : 𝓞 E →+* Module.End Ω V'} {j : V →+ V'}


include m in
theorem map_act (hact : M.IsActOf t.act.act ρ) (hact' : M'.IsActOf t'.act.act ρ')
    (hj : ∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left) (a : 𝓞 E) (e : V) :
    j (ρ a e) = ρ' a (j e) := by
  have hcanc : ∀ v w : epsAt ξ' ⟶ t'.G, v.left ≫ m.φ = w.left ≫ m.φ → v = w := by
    intro v w h
    apply Over.OverMorphism.ext
    refine m.cart.1.hom_ext h ?_
    rw [Over.w v, Over.w w]
  refine M'.inj (hcanc _ _ ?_)
  rw [hj, hact a e, hact' a (j e), Over.comp_left, Over.comp_left, Category.assoc, m.act a,
    ← Category.assoc (M'.pt (j e)).left]
  exact congrArg (· ≫ _) (hj e).symm


include m in
theorem map_mem_eigSp (hact : M.IsActOf t.act.act ρ) (hact' : M'.IsActOf t'.act.act ρ')
    (hj : ∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left)
    (hsl : ∀ (a : Ω₀) (e : V), j (a • e) = i a • j e) (σ : 𝓞 E →+* Ω₀) {e : V} (he : e ∈ eigSp ρ σ) :
    j e ∈ eigSp ρ' (i.comp σ) := by
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at he ⊢
  intro a
  rw [← map_act m hact hact' hj, he a, hsl]
  rfl

theorem eigLat_eq_pull [CharZero Ω₀] [CharZero Ω] (cst : c.F →+* Ω₀) (hg : IsCptGen ξ) (hg' : IsCptGen ξ')
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) (hact : M.IsActOf t.act.act ρ) (hact' : M'.IsActOf t'.act.act ρ')
    (hint : ∀ q : Cpt ξ, IsIntegrallyClosed (regAt ξ q)) (hint' : ∀ q : Cpt ξ', IsIntegrallyClosed (regAt ξ' q))
    (hj : ∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left)
    (s : CMType H ⊕ CMType H) (q : Cpt ξ') (hq : ∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q) :
    M'.eigLat ρ' ((i.comp cst).comp (labelEmb c s)) q =
      (M.eigLat ρ (cst.comp (labelEmb c s))).pull ξ' f j q := by
  obtain ⟨j₂, hj₂, hsl₂, -, -, hlat₂⟩ := GlobalTheory.T.lie_model_dominant_hodge E H X t X' t' f m Ω₀ Ω ξ ξ' i V V' M M' hg hg' hd
  have hcanc : ∀ v w : epsAt ξ' ⟶ t'.G, v.left ≫ m.φ = w.left ≫ m.φ → v = w := by
    intro v w h
    apply Over.OverMorphism.ext
    refine m.cart.1.hom_ext h ?_
    rw [Over.w v, Over.w w]
  have hjj : j₂ = j := by
    ext e
    exact M'.inj (hcanc _ _ ((hj₂ e).trans (hj e).symm))
  subst hjj
  have hlat := hlat₂
  have hsl := hsl₂
  obtain ⟨h, -, h2⟩ := RegAtDom.regAt_dominates X Ω₀ ξ X' Ω ξ' f i hd q
  have hp : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r ⟨f q.1, h⟩ := fun r hr hn =>
    hn (by
      have := h2 hg' _ (natCast_mem _ r) (by rw [map_natCast]; exact not_not.1 (hq r hr))
      exact this)
  have hsum := (SatModel.lat_eq_iSup_of_char0 c t ξ hg cst M ρ hact (fun q _ => hint q)).2 _ hp
  have hind := (SatModel.lat_eq_iSup_of_char0 c t' ξ' hg' (i.comp cst) M' ρ' hact' (fun q _ => hint' q)).1
  have hle : ∀ u, ((M.eigLat ρ (cst.comp (labelEmb c u))).pull ξ' f j₂) q ≤ M'.lat q ⊓
      (eigSp ρ' ((i.comp cst).comp (labelEmb c u))).restrictScalars (regAt ξ' q) := by
    intro u
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h', e, he, rfl⟩
    have he2 : e ∈ eigSp ρ (cst.comp (labelEmb c u)) := he.2
    have h3 : j₂ e ∈ eigSp ρ' ((i.comp cst).comp (labelEmb c u)) := by
      rw [RingHom.comp_assoc]
      exact map_mem_eigSp m hact hact' hj₂ hsl _ he2
    refine ⟨?_, h3⟩
    show j₂ e ∈ M'.lat q
    rw [hlat]
    exact Submodule.subset_span ⟨h, e, he.1, rfl⟩
  have hall : M'.lat q ≤ ⨆ u, ((M.eigLat ρ (cst.comp (labelEmb c u))).pull ξ' f j₂) q := by
    rw [hlat]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h', e, he, rfl⟩
    have he1 : e ∈ ⨆ u, M.lat.inter (eigSp ρ (cst.comp (labelEmb c u))) ⟨f q.1, h⟩ := by
      rw [← hsum]
      exact he
    refine Submodule.iSup_induction _ (motive := fun e =>
      j₂ e ∈ ⨆ u, ((M.eigLat ρ (cst.comp (labelEmb c u))).pull ξ' f j₂) q) he1 (fun u e he => ?_) ?_
      (fun x y hx hy => ?_)
    · exact Submodule.mem_iSup_of_mem u (Submodule.subset_span ⟨h, e, he, rfl⟩)
    · simp only [map_zero]
      exact zero_mem _
    · simp only [map_add (f := _)]
      exact add_mem hx hy
  refine le_antisymm ?_ (hle s)
  rintro x ⟨hx1, hx2⟩
  exact FlagStep.mem_of_mem_iSup_of_indep (regAt ξ' q) hind (fun u => (hle u).trans inf_le_right) s (hall hx1) hx2

end Eig

section Labels

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)

theorem labelEmb_inl (τ : CMType H) : labelEmb c (.inl τ) = tauIn c τ.1 := rfl

theorem labelEmb_inr (τ : CMType H) : labelEmb c (.inr τ) = tauIn c (ComplexEmbedding.conjugate τ.1) := by
  refine RingHom.ext fun a => Subtype.ext ?_
  change τ.1 ((H.bar a : 𝓞 E) : E) = (ComplexEmbedding.conjugate τ.1) (a : E)
  rw [H.bar_eq, ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]

end Labels

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li), CptIn.IsTie Z 𝔐 i j → ∀ p ∈ genFibre ℤ 𝔐.ξ, 𝔐.f p.1 ∈ Subtype.val '' Z.genFib ∧ 𝔐.V (.inl τ) p = (Z.eig τ.1).pull 𝔐.ξ 𝔐.f j p ∧ 𝔐.V (.inr τ) p = (Z.eig (ComplexEmbedding.conjugate τ.1)).pull 𝔐.ξ 𝔐.f j p := by
  intro E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 τ i j hT p hp
  obtain ⟨hd, hi, -, hpt⟩ := hT
  have hg' := 𝔐.tie.gen
  have hg := Z.gen
  haveI : CharZero Z.Ω := (RingHom.charZero_iff Z.inc.injective).1 inferInstance
  haveI : CharZero Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
  have hq : ∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r p := fun r hr hf =>
    hf (by simpa using hp (r : ℤ) (by exact_mod_cast hr.ne_zero))
  have hcore : ∀ s, 𝔐.V s p = (Z.M.eigLat Z.ρ (Z.inc.comp (labelEmb c s))).pull 𝔐.ξ 𝔐.f j p := by
    intro s
    have h1 : 𝔐.V s p = 𝔐.M.eigLat 𝔐.ρ (𝔐.cst.comp (labelEmb c s)) p :=
      Lat.patch_of_not S _ _ fun r hr => hq r (𝔐.S_prime r hr)
    rw [h1, ← hi]
    exact eigLat_eq_pull c 𝔐.m Z.inc hg hg' hd Z.act 𝔐.act (isIntegrallyClosed_regAt Y.normal hg)
      (isIntegrallyClosed_regAt (fun x => ⟨𝔐.normal.1 x, 𝔐.normal.2 x⟩) hg') hpt s p hq
  refine ⟨?_, ?_, ?_⟩
  · have hb : (Y.s (𝔐.f p.1)).asIdeal = ⊥ := by
      have := asIdeal_eq_bot hg' (𝔐.f ≫ Y.s) (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) 𝔐.cst_over hp
      rwa [Scheme.Hom.comp_apply] at this
    refine ⟨⟨𝔐.f p.1, hd.specializes p⟩, ?_, rfl⟩
    show 𝔐.f p.1 ∈ Set.range (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
    obtain ⟨w⟩ : Nonempty (Sp c.F) := inferInstance
    have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := IsFractionRing.injective _ _
    have e : Y.s (𝔐.f p.1) = spMap (algebraMap (𝓞 c.F) c.F) w := by
      refine PrimeSpectrum.ext ?_
      rw [hb]
      refine ((Submodule.eq_bot_iff _).2 fun o ho => ?_).symm
      have h1 : algebraMap (𝓞 c.F) c.F o ∈ w.asIdeal := ho
      by_contra h0
      have h2 : algebraMap (𝓞 c.F) c.F o ≠ 0 := fun e0 => h0 (hβ (by rw [e0, map_zero]))
      exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (isUnit_iff_ne_zero.2 h2))
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ e
    exact ⟨z, hz⟩
  · rw [hcore, labelEmb_inl]
    rfl
  · rw [hcore, labelEmb_inr]
    rfl

end GlobalTheory.CompanionTheory.Ar.Flat.CptStalk
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeLatticeComparisonStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_lattice_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li), CptIn.IsTie Z 𝔐 i j → ∀ p ∈ genFibre ℤ 𝔐.ξ, 𝔐.f p.1 ∈ Subtype.val '' Z.genFib ∧ 𝔐.V (.inl τ) p = (Z.eig τ.1).pull 𝔐.ξ 𝔐.f j p ∧ 𝔐.V (.inr τ) p = (Z.eig (ComplexEmbedding.conjugate τ.1)).pull 𝔐.ξ 𝔐.f j p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CptStalk.main | exact GlobalTheory.CompanionTheory.Ar.Flat.CptStalk.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CptStalk.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDegreeComposition
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDegreeComposition
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.DegComp

theorem det_ne_zero_of_injective {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {π : Y → X} (hπ : HoloMap B A π)
    (hinj : Function.Injective π) (j : Fin B.n) (k : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (B.chart j).target) (hk : π ((B.chart j).symm y) ∈ (A.chart k).source) :
    LinearMap.det (fderiv ℂ (A.chart k ∘ π ∘ (B.chart j).symm) y :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
  have hU : IsOpen ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (π ⁻¹' (A.chart k).source)) :=
    (B.chart j).isOpen_inter_preimage_symm ((A.chart k).open_source.preimage hπ.1)
  have hI : Set.InjOn (A.chart k ∘ π ∘ (B.chart j).symm)
      ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (π ⁻¹' (A.chart k).source)) := by
    intro a ha b hb hab
    exact (B.chart j).symm.injOn ha.1 hb.1 (hinj ((A.chart k).injOn ha.2 hb.2 hab))
  have hb := GlobalTheory.InjHol.bijective_fderiv_of_injOn e _ (A.chart k ∘ π ∘ (B.chart j).symm) hU
    (fun w hw => (hπ.2 j k w hw).differentiableAt.differentiableWithinAt) hI y ⟨hy, hk⟩
  intro h0
  have hlt := LinearMap.bot_lt_ker_of_det_eq_zero h0
  have hker : LinearMap.ker (fderiv ℂ (A.chart k ∘ π ∘ (B.chart j).symm) y :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = ⊥ := LinearMap.ker_eq_bot.mpr hb.1
  rw [hker] at hlt
  exact lt_irrefl _ hlt

theorem isDegreeOff_one_of_bijective {e : ℕ} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {π : Y → X}
    (hπ : HoloMap B A π) (hbij : Function.Bijective π) : IsDegreeOff A B π 1 ∅ := by
  refine ⟨isAnalyticSubset_empty A, interior_empty, ?_, ?_, ?_, ?_⟩
  · simpa using isAnalyticSubset_empty B
  · simp
  · intro x _
    obtain ⟨y, rfl⟩ := hbij.2 x
    have hfib : π ⁻¹' {π y} = {y} := by
      ext z
      simp [hbij.1.eq_iff]
    rw [hfib, Set.ncard_singleton]
  · intro j k y hy _ hk
    exact det_ne_zero_of_injective hπ hbij.1 j k hy hk

theorem holoMap_comp_isDegreeOff : ∀ (e d : ℕ) (X Y Z : Type) [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [TopologicalSpace Z] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (C : FinHolAtlas e Z) (π : Y → X) (h : Z → Y) (br : Set Y), HoloMap B A π → Function.Bijective π → HoloMap C B h → IsDegreeOff B C h d br → HoloMap C A (π ∘ h) ∧ IsDegreeOff A C (π ∘ h) d (π '' br) := by
  intro e d X Y Z _ _ _ _ _ _ A B C π h br hπ hbij hh hd
  obtain ⟨g, hgl, hgr, hg⟩ := GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_holoMap_inverse_of_degree_one A B π hπ
    (isDegreeOff_one_of_bijective hπ hbij)
  refine ⟨GlobalTheory.CompanionTheory.Ar.PB.CovMap.holoMap_comp hh hπ, ?_⟩
  obtain ⟨han, hint, hpan, hpint, hfib, hdet⟩ := hd
  have hpre : (π ∘ h) ⁻¹' (π '' br) = h ⁻¹' br := by
    ext z
    simp [hbij.1.mem_set_image]
  have himg : π '' br = g ⁻¹' br := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [hgl] using hy
    · intro hx
      exact ⟨g x, hx, hgr x⟩
  let E : Y ≃ₜ X :=
    { toFun := π, invFun := g, left_inv := hgl, right_inv := hgr,
      continuous_toFun := hπ.1, continuous_invFun := hg.1 }
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [himg]
    intro x
    obtain ⟨W, hW, hxW, r, f, hf, hS⟩ := han (g x)
    refine ⟨g ⁻¹' W, hW.preimage hg.1, hxW, r, fun i => f i ∘ g,
      fun i => GlobalTheory.CompanionTheory.Ar.PB.Cj.holoOn_comp hg (hf i), ?_⟩
    ext y
    simpa using Set.ext_iff.1 hS (g y)
  · change interior (E '' br) = ∅
    rw [← E.image_interior, hint, Set.image_empty]
  · rw [hpre]
    exact hpan
  · rw [hpre]
    exact hpint
  · intro x hx
    have hgx : g x ∉ br := fun hb => hx ⟨g x, hb, hgr x⟩
    have hset : (π ∘ h) ⁻¹' {x} = h ⁻¹' {g x} := by
      ext z
      constructor
      · intro hz
        have hz' : π (h z) = x := hz
        change h z = g x
        rw [← hz', hgl]
      · intro hz
        have hz' : h z = g x := hz
        change π (h z) = x
        rw [hz', hgr]
    rw [hset]
    exact hfib _ hgx
  · intro j k y hy hnot hk
    have hnot' : (C.chart j).symm y ∉ h ⁻¹' br := by rwa [hpre] at hnot
    obtain ⟨l, hl⟩ := B.cover (h ((C.chart j).symm y))
    obtain ⟨Q, hQdef⟩ : ∃ Q : (Fin e → ℂ) → Fin e → ℂ, Q = B.chart l ∘ h ∘ (C.chart j).symm :=
      ⟨_, rfl⟩
    obtain ⟨P, hPdef⟩ : ∃ P : (Fin e → ℂ) → Fin e → ℂ, P = A.chart k ∘ π ∘ (B.chart l).symm :=
      ⟨_, rfl⟩
    have hQa : AnalyticAt ℂ Q y := by
      rw [hQdef]
      exact hh.2 j l y ⟨hy, hl⟩
    have hu : (B.chart l).symm (Q y) = h ((C.chart j).symm y) := by
      rw [hQdef]
      exact (B.chart l).left_inv hl
    have hQt : Q y ∈ (B.chart l).target := by
      rw [hQdef]
      exact (B.chart l).map_source hl
    have hk' : π ((B.chart l).symm (Q y)) ∈ (A.chart k).source := by
      rw [hu]
      exact hk
    have hPa : AnalyticAt ℂ P (Q y) := by
      rw [hPdef]
      exact hπ.2 l k _ ⟨hQt, hk'⟩
    have hc : ContinuousAt (h ∘ (C.chart j).symm) y :=
      hh.1.continuousAt.comp ((C.chart j).continuousAt_symm hy)
    have heq : (A.chart k ∘ (π ∘ h) ∘ (C.chart j).symm) =ᶠ[nhds y] P ∘ Q := by
      filter_upwards [hc ((B.chart l).open_source.mem_nhds hl)] with t ht
      have ht' : h ((C.chart j).symm t) ∈ (B.chart l).source := ht
      rw [hPdef, hQdef]
      simp only [Function.comp, (B.chart l).left_inv ht']
    have hcomp : fderiv ℂ (P ∘ Q) y = (fderiv ℂ P (Q y)).comp (fderiv ℂ Q y) :=
      fderiv_comp y hPa.differentiableAt hQa.differentiableAt
    rw [heq.fderiv_eq, hcomp]
    change LinearMap.det ((fderiv ℂ P (Q y) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ∘ₗ
      (fderiv ℂ Q y : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) ≠ 0
    rw [LinearMap.det_comp]
    refine mul_ne_zero ?_ ?_
    · rw [hPdef]
      exact det_ne_zero_of_injective hπ hbij.1 l k hQt hk'
    · rw [hQdef]
      exact hdet j l y hy hnot' hl

end GlobalTheory.CompanionTheory.Ar.DegComp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDegreeCompositionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_degree_composition : ∀ (e d : ℕ) (X Y Z : Type) [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [TopologicalSpace Z] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (C : FinHolAtlas e Z) (π : Y → X) (h : Z → Y) (br : Set Y), HoloMap B A π → Function.Bijective π → HoloMap C B h → IsDegreeOff B C h d br → HoloMap C A (π ∘ h) ∧ IsDegreeOff A C (π ∘ h) d (π '' br) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DegComp.holoMap_comp_isDegreeOff | exact GlobalTheory.CompanionTheory.Ar.DegComp.holoMap_comp_isDegreeOff | (intros; apply GlobalTheory.CompanionTheory.Ar.DegComp.holoMap_comp_isDegreeOff <;> assumption)
end
end

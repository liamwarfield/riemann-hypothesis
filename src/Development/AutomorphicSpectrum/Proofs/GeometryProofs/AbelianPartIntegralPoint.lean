module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartLatticeEigenCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSandwichOfHodgeTateFree

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.AbelianPartIntegralPointBis
section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.InFibreLoc
section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.AevalCyclotomic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace LevelTowerAlt.LocalPrimeBound

section Lin

variable {F V O : Type} [Field F] [AddCommGroup V] [Module F V] [CommRing O]

theorem mem_eigSp {ρ : O →+* Module.End F V} {σ : O →+* F} {x : V} : x ∈ eigSp ρ σ ↔ ∀ a, ρ a x = σ a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem eigSp_indep (ρ : O →+* Module.End F V) {I : Type} (σ : I → (O →+* F))
    (hσ : Function.Injective σ) : iSupIndep fun s => eigSp ρ (σ s) := by
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun a : O => ρ a)
    (fun a b φ => Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.all b a).map ρ) φ)
  have h2 := h.comp (f := fun s => (σ s : O → F)) (fun s t hst => hσ (DFunLike.coe_injective hst))
  refine h2.mono fun s => ?_
  refine iInf_mono fun a v hv => ?_
  refine Module.End.eigenspace_le_maxGenEigenspace ?_
  rw [Module.End.mem_eigenspace_iff]
  simpa [sub_eq_zero] using hv

theorem mem_of_indep {R : Type} [CommRing R] [Module R V] [Algebra R F] [IsScalarTower R F V] {I : Type}
    (W : I → Submodule F V) (hW : iSupIndep W) (N : I → Submodule R V)
    (hN : ∀ s, N s ≤ (W s).restrictScalars R) (s : I) {x : V} (hx : x ∈ ⨆ t, N t) (hs : x ∈ W s) : x ∈ N s := by
  rw [iSup_split_single N s] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  have h1 : (⨆ t, ⨆ (_ : t ≠ s), N t) ≤ (⨆ t, ⨆ (_ : t ≠ s), W t).restrictScalars R :=
    iSup₂_le fun t ht y hy => (le_iSup₂_of_le (f := fun t (_ : t ≠ s) => W t) t ht le_rfl) (hN t hy)
  have h2 : b ∈ W s := by simpa using (W s).sub_mem hs (hN s ha)
  have h3 : b = 0 := (Submodule.disjoint_def.1 (hW s)) b h2 (h1 hb)
  simpa [h3] using ha

end Lin

section Pt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {R : Type} [CommRing R] [IsLocalRing R]

theorem exists_value (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) {a : Ω}
    (ha : a ∈ regAt ξ ⟨centre z, h⟩) : ∃ r : R, ValAt ξ z a r := by
  obtain ⟨s, hs⟩ := ha
  exact ⟨_, h, s, hs, rfl⟩

theorem value_aeval (hg : IsCptGen ξ) {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r : R} (hv : ValAt ξ z a r)
    (f : Polynomial ℤ) (hf : Polynomial.aeval a f = 0) : Polynomial.aeval r f = 0 := by
  obtain ⟨h, s, hs, rfl⟩ := hv
  let φ : X.presheaf.stalk (centre z) →+* R := (Scheme.stalkClosedPointTo z).hom
  have e1 := Polynomial.aeval_algHom_apply (genMap ξ ⟨centre z, h⟩).toIntAlgHom s f
  have e2 := Polynomial.aeval_algHom_apply φ.toIntAlgHom s f
  have h0 : Polynomial.aeval s f = 0 := by
    apply hg.inj ⟨centre z, h⟩
    rw [map_zero]
    have : (genMap ξ ⟨centre z, h⟩).toIntAlgHom s = a := hs
    rw [this, hf] at e1
    exact e1.symm
  rw [h0] at e2
  exact e2.trans (map_zero φ.toIntAlgHom)

theorem aeval_cyclotomic {S : Type} [CommRing S] (n : ℕ) (x : S) :
    Polynomial.aeval x (Polynomial.cyclotomic n ℤ) = (Polynomial.cyclotomic n S).eval x := by
  rw [← Polynomial.map_cyclotomic n (algebraMap ℤ S), Polynomial.eval_map_algebraMap]

theorem value_cp (hg : IsCptGen ξ) {F : Type} [Field F] [CharZero F] {z : Spec (CommRingCat.of F) ⟶ X} {p : ℕ}
    (hp : p.Prime) {κ : Ω} {r : F} (hκ : HT.IsCp p κ) (hv : ValAt ξ z κ r) :
    (p = 2 → r = 4) ∧ (p ≠ 2 → IsPrimitiveRoot (r + 1) p) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [HT.IsCp, if_pos h] at hκ
    have h3 := value_aeval hg hv (Polynomial.X - Polynomial.C 4) (by
      simp only [map_sub, Polynomial.aeval_X, hκ, map_ofNat, sub_self])
    simp only [map_sub, Polynomial.aeval_X, map_ofNat] at h3
    exact sub_eq_zero.1 h3
  · rw [HT.IsCp, if_neg h] at hκ
    obtain ⟨ζ, hζ, rfl⟩ := hκ
    have hp0 : NeZero (p : F) := ⟨Nat.cast_ne_zero.2 hp.ne_zero⟩
    have h3 := value_aeval hg hv ((Polynomial.cyclotomic p ℤ).comp (Polynomial.X + 1)) (by
      rw [Polynomial.aeval_comp]
      simp only [map_add (f := _), Polynomial.aeval_X, map_one, sub_add_cancel]
      rw [aeval_cyclotomic]
      exact hζ.isRoot_cyclotomic hp.pos)
    rw [Polynomial.aeval_comp] at h3
    simp only [map_add (f := _), Polynomial.aeval_X, map_one] at h3
    rw [aeval_cyclotomic] at h3
    exact Polynomial.isRoot_cyclotomic_iff.1 h3

variable {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li)
  (z : Spec (CommRingCat.of R) ⟶ X) {C : Type} [Field C] [Algebra R C] {EC : Type} [AddCommGroup EC] [Module C EC]
  (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) EC)

theorem val_exists (h : genPt ξ ⤳ centre z)
    (h' : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)) {e : Li}
    (he : e ∈ M.lat ⟨centre z, h⟩) :
    ∃ x, M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) e (MC.pt x) := by
  obtain ⟨u, hu⟩ := (M.exists_valAt_iff z e).2 ⟨h, he⟩
  have ht := hu.isTanAt
  obtain ⟨_, v, hv, hu⟩ := hu
  have h1 := LieFib.valAt_base M z h h' v hv (LieCarrier.epsHom (algebraMap R C) z _ rfl ≫ u) u rfl hu
  obtain ⟨x, hx⟩ := MC.onto _ h1.isTanAt
  exact ⟨x, hx ▸ h1⟩

end Pt

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  (𝔐 : HodgeCpt Y S y) {R : Type} [CommRing R] [IsLocalRing R] (z : Sp R ⟶ 𝔐.X)

omit [∀ k, Fintype (J k)] in
theorem emb_value (s : CMType H ⊕ CMType H) (a : 𝓞 E) : ∃ r, ValAt 𝔐.ξ z (𝔐.emb s a) r := by
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { }
  obtain ⟨ρ, hρ⟩ : ∃ ρ : 𝓞 c.F →+* R, spMap ρ = z ≫ 𝔐.f ≫ Y.s :=
    ⟨(Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom, by simp [spMap]⟩
  letI : Algebra (𝓞 c.F) Ω := (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toAlgebra
  have hint : IsIntegral ℤ (labelEmb c s a) :=
    (NumberField.RingOfIntegers.isIntegral a).map (labelEmb c s).toIntAlgHom
  have hm : algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) _ hint) = labelEmb c s a :=
    IsIntegralClosure.algebraMap_mk' _ _ hint
  have h := LabPt.valAt_of_const 𝔐.ξ (𝔐.f ≫ Y.s) 𝔐.cst_over z ρ hρ.symm (𝔐.all _)
    (IsIntegralClosure.mk' (𝓞 c.F) _ hint)
  have he : algebraMap (𝓞 c.F) Ω (IsIntegralClosure.mk' (𝓞 c.F) _ hint) = 𝔐.emb s a := by
    show 𝔐.cst (algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) _ hint)) = 𝔐.cst (labelEmb c s a)
    rw [hm]
  rw [he] at h
  exact ⟨_, h⟩

variable {C : Type} [Field C] [CharZero C] [Algebra R C] {EC : Type} [AddCommGroup EC] [Module C EC] [Module R EC]
  [IsScalarTower R C EC] (MC : LieModel 𝔐.t.G (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) EC)
  (ρC : 𝓞 E →+* Module.End C EC) (hact : MC.IsActOf 𝔐.t.act.act ρC)

include hact in
omit [∀ k, Fintype (J k)] [CharZero C] [Module R EC] [IsScalarTower R C EC] in
theorem val_mem_eig {s : CMType H ⊕ CMType H} {σ : 𝓞 E →+* R} (hσ : ∀ a, ValAt 𝔐.ξ z (𝔐.emb s a) (σ a))
    {e : 𝔐.Li} {x : EC} (he : e ∈ 𝔐.Vgen s)
    (hx : 𝔐.M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) e (MC.pt x)) :
    x ∈ eigSp ρC ((algebraMap R C).comp σ) := by
  refine mem_eigSp.2 fun a => ?_
  haveI := 𝔐.t.act.hom a
  have h1 := PositivityTheory.HtPt.Gh.valAt_act 𝔐.M MC _ _ _ (𝔐.act a) (hact a) hx
  have h2 := PtHt.FinFrame.val_smul (LieTangent.valAt_base 𝔐.tie.gen (algebraMap R C) (hσ a)) hx
  rw [mem_eigSp.1 he a] at h1
  exact MC.inj (h1.unique 𝔐.tie.gen h2)


include hact in
theorem off_S (σ : CMType H ⊕ CMType H → (𝓞 E →+* R)) (hσ : ∀ s a, ValAt 𝔐.ξ z (𝔐.emb s a) (σ s a))
    (hinj : Function.Injective fun s => (algebraMap R C).comp (σ s)) (hS : ∀ p ∈ S, IsUnit (p : R))
    (hd : IsUnit (((discr E).natAbs : ℕ) : R)) (s : CMType H ⊕ CMType H) :
    𝔐.M.fibAt (𝔐.V s) z MC =
      𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap R C).comp (σ s))).restrictScalars R := by
  classical
  have hξ := 𝔐.tie.gen
  have h : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have h' : genPt 𝔐.ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) := 𝔐.all _
  have hV : 𝔐.V s ⟨centre z, h⟩ = 𝔐.dR s ⟨centre z, h⟩ :=
    Lat.patch_of_not _ _ _ fun p hp hf => hf ((PositivityTheory.HtPt.Gh.unitAt_centre_iff hξ z h p).2 (hS p hp))
  have hfib : 𝔐.M.fibAt (𝔐.V s) z MC = 𝔐.M.fibAt (𝔐.dR s) z MC := by
    unfold LieModel.fibAt
    congr 1
    ext x
    exact ⟨fun ⟨h1, e, h2, h3⟩ => ⟨h1, e, hV ▸ h2, h3⟩, fun ⟨h1, e, h2, h3⟩ => ⟨h1, e, hV.symm ▸ h2, h3⟩⟩
  have hle : ∀ t, 𝔐.M.fibAt (𝔐.dR t) z MC ≤ (eigSp ρC ((algebraMap R C).comp (σ t))).restrictScalars R := fun t =>
    Submodule.span_le.2 fun x ⟨_, e, h2, h3⟩ => val_mem_eig 𝔐 z MC ρC hact (hσ t) h2.2 h3
  rw [hfib]
  refine le_antisymm (le_inf (Submodule.span_mono fun x ⟨h1, e, h2, h3⟩ => ⟨h1, e, h2.1, h3⟩) (hle s)) ?_
  rintro x ⟨hx1, hx2⟩
  refine mem_of_indep _ (eigSp_indep ρC _ hinj) _ hle s ?_ hx2
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  obtain ⟨hli, hcard⟩ := GlobalTheory.T.label_embedding_injective E H l c
  have hσ' : Function.Injective 𝔐.emb := fun s s' h =>
    hli (RingHom.ext fun a => 𝔐.cst.injective (RingHom.congr_fun h a))
  have hlat := (GlobalTheory.T.lie_omega_lattice_vector_bundle 𝔐.X Ω 𝔐.ξ 𝔐.t.G 𝔐.Li 𝔐.M hξ 𝔐.t.semi.smooth).1
  obtain ⟨-, hsup⟩ := GlobalTheory.T.lattice_eigen_vector_bundle 𝔐.X Ω 𝔐.ξ 𝔐.Li E 𝔐.ρ 𝔐.M.lat {⟨centre z, h⟩} _ (CMType H ⊕ CMType H) 𝔐.emb hξ hσ'
    (by rw [← hcard, Nat.card_eq_fintype_card])
    (fun p _ => by
      obtain ⟨U, hU, b, hb, H⟩ := hlat p trivial
      exact ⟨U, hU, b, hb, fun q _ hq => H q trivial hq⟩)
    (fun p _ a => LieStable.lat_stable _ _ _ _ _ 𝔐.M _ 𝔐.t.act 𝔐.ρ 𝔐.act p a)
    (by
      rintro p rfl s a
      obtain ⟨_, t, ht, -⟩ := hσ s a
      exact ⟨t, ht⟩)
    (by
      rintro p rfl
      have h := (PositivityTheory.HtPt.Gh.unitAt_centre_iff hξ z h _).2 hd
      rcases Int.natAbs_eq (NumberField.discr E) with e | e
      · rw [e]; simpa using h
      · rw [e]
        refine ⟨by simpa using h.1, by simpa using h.2.1, ?_⟩
        simpa using h.2.2)
  have hs1 := hsup _ rfl
  refine (Submodule.span_le.2 ?_ : 𝔐.M.fibAt 𝔐.M.lat z MC ≤ _) hx1
  rintro w ⟨_, e, he, hw⟩
  have key : ∀ e ∈ ⨆ s, (𝔐.M.lat.inter (eigSp 𝔐.ρ (𝔐.emb s))) ⟨centre z, h⟩, ∃ x ∈ ⨆ t, 𝔐.M.fibAt (𝔐.dR t) z MC,
      𝔐.M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) e (MC.pt x) := by
    intro e he
    induction he using Submodule.iSup_induction' with
    | mem t e he =>
      obtain ⟨x, hx⟩ := val_exists 𝔐.M z MC h h' he.1
      exact ⟨x, Submodule.mem_iSup_of_mem t (Submodule.subset_span ⟨h, e, he, hx⟩), hx⟩
    | zero => exact ⟨0, zero_mem _, by rw [MC.pt_zero]; exact 𝔐.M.valAt_zero h'⟩
    | add a b _ _ ha hb =>
      obtain ⟨x, hx, ha⟩ := ha
      obtain ⟨x', hx', hb⟩ := hb
      exact ⟨x + x', add_mem hx hx', PtHt.FinFrame.val_add ha hb⟩
  obtain ⟨x', h1, h2⟩ := key e (hs1 ▸ he)
  rwa [MC.inj (hw.unique hξ h2)]


include hact in
theorem on_S {p : ℕ} (hpS : p ∈ S) (κ : Ω) (hfree : HT.HTFree 𝔐 p) (hsand : HT.Sandwich 𝔐 p κ)
    (v : Valuation C NNReal) (hv : v.Integers R) (hvp : v (p : C) < 1) (s : CMType H ⊕ CMType H)
    (σ : 𝓞 E →+* R) (hσ : ∀ a, ValAt 𝔐.ξ z (𝔐.emb s a) (σ a)) (κz : R) (hκ : ValAt 𝔐.ξ z κ κz) :
    𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap R C).comp σ)).restrictScalars R ≤ 𝔐.M.fibAt (𝔐.V s) z MC ∧
    ∀ w ∈ 𝔐.M.fibAt (𝔐.V s) z MC, ∀ d ∈ differentIdeal ℤ (𝓞 E), κz • σ d • w ∈
      𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap R C).comp σ)).restrictScalars R := by
  have hξ := 𝔐.tie.gen
  have hp : p.Prime := 𝔐.S_prime p hpS
  haveI : Fact p.Prime := ⟨hp⟩
  have h : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.sandwich_point_over_field_ext E H D l Xo c _ _ Y S Ω K J y 𝔐 p hpS κ hfree hsand C v R hv hvp z EC MC ρC s σ κz
    hact hσ hκ
  have hpu : ¬ IsUnit (p : R) := fun hu => by
    have := hv.one_of_isUnit hu
    rw [map_natCast] at this
    exact hvp.ne this
  have hq : InFibre 𝔐.ξ p ⟨centre z, h⟩ := fun hu => hpu ((PositivityTheory.HtPt.Gh.unitAt_centre_iff hξ z h p).1 hu)
  have hu : ∀ p' ∈ S, InFibre 𝔐.ξ p' ⟨centre z, h⟩ → p' = p := by
    intro p' hp' hf
    by_contra hne
    have hc : IsCoprime (p' : R) (p : R) :=
      Nat.Coprime.cast ((Nat.coprime_primes (𝔐.S_prime p' hp') hp).2 hne)
    obtain ⟨a, b, hab⟩ := hc
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h1 | h1
    · exact hf ((PositivityTheory.HtPt.Gh.unitAt_centre_iff hξ z h p').2 (isUnit_of_mul_isUnit_right h1))
    · exact hpu (isUnit_of_mul_isUnit_right h1)
  have hV : 𝔐.V s ⟨centre z, h⟩ = 𝔐.HT p s ⟨centre z, h⟩ := Lat.patch_of_unique _ _ _ hpS hq hu
  have hreg : ∀ a, 𝔐.emb s a ∈ regAt 𝔐.ξ ⟨centre z, h⟩ := fun a => by
    obtain ⟨_, t, ht, -⟩ := hσ a
    exact ⟨t, ht⟩
  have hA : ∀ e ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) ⟨centre z, h⟩, e ∈ 𝔐.V s ⟨centre z, h⟩ := by
    intro e he
    rw [hV]
    cases s with
    | inr τ => exact he
    | inl τ =>
      exact Submodule.subset_span ⟨𝔐.M.mem_eigSp_of_mem_htDual _ _ _ _ he, fun d _ =>
        Submodule.smul_mem _ (⟨_, hreg d⟩ : regAt 𝔐.ξ ⟨centre z, h⟩) he⟩
  have hB : ∀ d ∈ differentIdeal ℤ (𝓞 E), ∀ e ∈ 𝔐.V s ⟨centre z, h⟩,
      𝔐.emb s d • e ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) ⟨centre z, h⟩ := by
    intro d hd e he
    rw [hV] at he
    cases s with
    | inr τ => exact Submodule.smul_mem _ (⟨_, hreg d⟩ : regAt 𝔐.ξ ⟨centre z, h⟩) he
    | inl τ =>
      induction he using Submodule.span_induction with
      | mem x hx => exact hx.2 d hd
      | zero => rw [smul_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
      | smul a x _ hx =>
        have e1 : 𝔐.emb (.inl τ) d • a • x = a • 𝔐.emb (.inl τ) d • x := smul_comm (𝔐.emb (.inl τ) d) (a : Ω) x
        rw [e1]
        exact Submodule.smul_mem _ a hx
  refine ⟨h1.trans (Submodule.span_mono fun x ⟨h1, e, h2, h3⟩ => ⟨h1, e, hA e h2, h3⟩), fun w hw d hd => h2 _ ?_⟩
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨_, e, h2, h3⟩ := hx
    refine Submodule.subset_span ⟨h, _, hB d hd e h2, ?_⟩
    have := PtHt.FinFrame.val_smul (LieTangent.valAt_base hξ (algebraMap R C) (hσ d)) h3
    rwa [algebraMap_smul] at this
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

end Model

end LevelTowerAlt.LocalPrimeBound
end
end

section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.NormBound
open NumberField IsDedekindDomain

noncomputable section
namespace LevelTowerAlt.LocalPrimeBound

section Dvr

variable (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem exists_val : ∃ v : Valuation K NNReal, v.Integers V ∧ ∀ x : V, ¬ IsUnit x → v (algebraMap V K x) < 1 := by
  have hmax : IsLocalRing.maximalIdeal V ≠ ⊥ := IsDiscreteValuationRing.not_a_field V
  let P : HeightOneSpectrum V :=
    ⟨IsLocalRing.maximalIdeal V, (IsLocalRing.maximalIdeal.isMaximal V).isPrime, hmax⟩
  have hP : ∀ w : HeightOneSpectrum V, w = P := fun w =>
    HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal (w.isPrime.isMaximal w.ne_bot))
  have he : (1 : NNReal) < 2 := one_lt_two
  let f := WithZeroMulInt.toNNReal he.ne_zero
  have hf : StrictMono f := WithZeroMulInt.toNNReal_strictMono he
  refine ⟨Valuation.map ⟨f, hf.monotone⟩ (P.valuation K),
    ⟨IsFractionRing.injective V K, fun x => ?_, fun r hr => ?_⟩, fun x hx => ?_⟩
  · rw [Valuation.map_apply, ← map_one f]
    exact hf.monotone (P.valuation_le_one (K := K) x)
  · rw [Valuation.map_apply, ← map_one f] at hr
    have hr' : P.valuation K r ≤ 1 := hf.le_iff_le.1 hr
    obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (K := K) (x := r)
      (h := fun w => by rw [hP w]; exact hr')
    exact ⟨y, hy⟩
  · rw [Valuation.map_apply, ← map_one f]
    exact hf ((P.valuation_lt_one_iff_mem (K := K) x).2 ((IsLocalRing.mem_maximalIdeal x).2 hx))

end Dvr

variable {L : Type} [Field L] [NumberField L]

theorem const_int {p : ℕ} (hp : p.Prime) {r : L} (h2 : p = 2 → r = 4) (hodd : p ≠ 2 → IsPrimitiveRoot (r + 1) p) :
    ∃ k : 𝓞 L, algebraMap (𝓞 L) L k = r ∧ k ≠ 0 ∧
      Real.log (Ideal.absNorm (Ideal.span {k})) ≤ Module.finrank ℚ L * (2 * (Real.log p / ((p : ℝ) - 1))) := by
  have hnormZ : ∀ m : ℕ, Ideal.absNorm (Ideal.span {(m : 𝓞 L)}) = m ^ Module.finrank ℚ L := by
    intro m
    rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 L)) m, Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank, Int.natAbs_pow]
    simp
  have hd : (0 : ℝ) ≤ Module.finrank ℚ L := Nat.cast_nonneg _
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have ht : 0 ≤ Real.log p / ((p : ℝ) - 1) := div_nonneg (Real.log_nonneg hp1.le) (by linarith)
  by_cases h2' : p = 2
  · subst h2'
    refine ⟨4, ?_, ?_, ?_⟩
    · rw [h2 rfl]
      exact map_ofNat _ 4
    · intro h
      have h4 := congrArg (algebraMap (𝓞 L) L) h
      rw [map_ofNat, map_zero] at h4
      norm_num at h4
    · rw [show (4 : 𝓞 L) = ((4 : ℕ) : 𝓞 L) by norm_num, hnormZ, Nat.cast_pow, Real.log_pow]
      have h4 : Real.log ((4 : ℕ) : ℝ) = 2 * Real.log 2 := by
        rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      rw [h4]
      norm_num
  · have hζ : IsPrimitiveRoot (r + 1) p := hodd h2'
    let ζ : 𝓞 L := ⟨r + 1, hζ.isIntegral hp.pos⟩
    have hζ' : IsPrimitiveRoot ζ p :=
      IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 L) L) hζ RingOfIntegers.coe_injective
    refine ⟨ζ - 1, ?_, sub_ne_zero.2 (hζ'.ne_one hp.one_lt), ?_⟩
    · rw [map_sub, map_one]
      exact add_sub_cancel_right r 1
    · have hassoc := GroundTheory.Heights₂.Heights.RootsOfUnityValuation.one_sub_pow_associated hp hζ'
      have hsp : Ideal.span {ζ - 1} = Ideal.span {1 - ζ} := by
        rw [← neg_sub, Ideal.span_singleton_neg]
      have hN : Ideal.absNorm (Ideal.span {ζ - 1}) ^ (p - 1) = p ^ Module.finrank ℚ L := by
        rw [← hnormZ, ← Ideal.span_singleton_eq_span_singleton.2 hassoc, ← Ideal.span_singleton_pow,
          map_pow, hsp]
      have hNr : (Ideal.absNorm (Ideal.span {ζ - 1}) : ℝ) ^ (p - 1) = (p : ℝ) ^ Module.finrank ℚ L := by
        exact_mod_cast hN
      have hlog := congrArg Real.log hNr
      rw [Real.log_pow, Real.log_pow, Nat.cast_sub hp.one_le, Nat.cast_one] at hlog
      have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hL : Real.log (Ideal.absNorm (Ideal.span {ζ - 1})) =
          Module.finrank ℚ L * (Real.log p / ((p : ℝ) - 1)) := by
        rw [← mul_div_assoc, eq_div_iff hpos.ne']
        linear_combination hlog
      rw [hL]
      exact mul_le_mul_of_nonneg_left (by linarith) hd

theorem norm_bound {E : Type} [Field E] [NumberField E] (ι : E →+* L) (S : Finset ℕ) (k : ℕ → 𝓞 L)
    (hk : ∀ p ∈ S, k p ≠ 0 ∧
      Real.log (Ideal.absNorm (Ideal.span {k p})) ≤ Module.finrank ℚ L * (2 * (Real.log p / ((p : ℝ) - 1)))) :
    (differentIdeal ℤ (𝓞 E)).map (RingOfIntegers.mapRingHom ι) * Ideal.span {∏ p ∈ S, k p} ≠ ⊥ ∧
    Real.log (Ideal.absNorm ((differentIdeal ℤ (𝓞 E)).map (RingOfIntegers.mapRingHom ι) *
        Ideal.span {∏ p ∈ S, k p})) / Module.finrank ℚ L ≤
      2 * (∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1)) +
        2 * Real.log (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))) := by
  obtain ⟨hne, hlog⟩ := GroundTheory.Heights₂.Heights.NineStatements.DifferentExtNorm.full E L ι
  change (differentIdeal ℤ (𝓞 E)).map (RingOfIntegers.mapRingHom ι) ≠ ⊥ at hne
  change Real.log (Ideal.absNorm ((differentIdeal ℤ (𝓞 E)).map (RingOfIntegers.mapRingHom ι))) = _ at hlog
  set I := (differentIdeal ℤ (𝓞 E)).map (RingOfIntegers.mapRingHom ι) with hI
  have hspan : Ideal.span {∏ p ∈ S, k p} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Finset.prod_ne_zero_iff.2 fun p hp => (hk p hp).1
  refine ⟨by rw [Ne, Ideal.mul_eq_bot, not_or]; exact ⟨hne, hspan⟩, ?_⟩
  have hn : (0 : ℝ) < Module.finrank ℚ L := Nat.cast_pos.2 Module.finrank_pos
  have hN : ∀ p ∈ S, (Ideal.absNorm (Ideal.span {k p}) : ℝ) ≠ 0 := fun p hp => by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact (hk p hp).1
  have hNI : (Ideal.absNorm I : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact hne
  rw [map_mul, ← Ideal.prod_span_singleton, map_prod, Nat.cast_mul, Nat.cast_prod,
    Real.log_mul hNI (Finset.prod_ne_zero_iff.2 hN), Real.log_prod hN, hlog]
  have hB : ∑ p ∈ S, Real.log (Ideal.absNorm (Ideal.span {k p})) ≤
      Module.finrank ℚ L * (2 * ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun p hp => (hk p hp).2
  have hdE : (discr E : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero E
  have hR : 0 ≤ GroundTheory.Heights₂.Heights.NineStatements.logRd E := by
    unfold GroundTheory.Heights₂.Heights.NineStatements.logRd
    refine div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)
    have h1 : (1 : ℤ) ≤ |discr E| := Int.one_le_abs (NumberField.discr_ne_zero E)
    exact_mod_cast h1
  have hlogd : Real.log (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))) =
      GroundTheory.Heights₂.Heights.NineStatements.logRd E := by
    unfold GroundTheory.Heights₂.Heights.NineStatements.logRd
    rw [Real.log_rpow (abs_pos.2 hdE)]
    ring
  rw [hlogd, add_div, mul_div_cancel_left₀ _ hn.ne']
  have hB' : (∑ p ∈ S, Real.log (Ideal.absNorm (Ideal.span {k p}))) / Module.finrank ℚ L ≤
      2 * ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1) := by
    rw [div_le_iff₀ hn]
    linarith [hB]
  linarith

end LevelTowerAlt.LocalPrimeBound
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace LevelTowerAlt.LocalPrimeBound

theorem exists_prime_mem {O : Type} [CommRing O] (P : Ideal O) [hP : P.IsPrime] (n : ℕ) (hn : n ≠ 0)
    (h : (n : O) ∈ P) : ∃ r : ℕ, r.Prime ∧ r ∣ n ∧ (r : O) ∈ P := by
  induction n using induction_on_primes with
  | zero => exact absurd rfl hn
  | one => exact absurd (by simpa using h) ((Ideal.ne_top_iff_one _).1 hP.ne_top)
  | prime_mul p a hp ih =>
    rw [Nat.cast_mul] at h
    rcases hP.mem_or_mem h with h | h
    · exact ⟨p, hp, Dvd.intro _ rfl, h⟩
    · obtain ⟨r, h1, h2, h3⟩ := ih (right_ne_zero_of_mul hn) h
      exact ⟨r, h1, h2.mul_left _, h3⟩

theorem lie_cast {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type}
    [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {w w' : Sp F ⟶ X} (h : w = w') (ML : LieModel G w V) {O : Type} [CommRing O] (act : O → (G ⟶ G))
    (ρ : O →+* Module.End F V) (hact : ML.IsActOf act ρ) :
    ∃ MC : LieModel G w' V, (∀ x, (MC.pt x).left = (ML.pt x).left) ∧
      (∀ e x, M.ValAt w' e (MC.pt x) ↔ M.ValAt w e (ML.pt x)) ∧ MC.IsActOf act ρ := by
  subst h
  exact ⟨ML, fun _ => rfl, fun _ _ => Iff.rfl, hact⟩

theorem centre_loc {X : Scheme.{0}} {O : Type} [CommRing O] (z : Sp O ⟶ X) (P : Ideal O) [hP : P.IsPrime] :
    centre (spMap (algebraMap O (Localization.AtPrime P)) ≫ z) = z (⟨P, hP⟩ : PrimeSpectrum O) := by
  have e : (spMap (algebraMap O (Localization.AtPrime P))) (IsLocalRing.closedPoint (Localization.AtPrime P)) =
      (⟨P, hP⟩ : PrimeSpectrum O) := by
    apply PrimeSpectrum.ext
    show (IsLocalRing.maximalIdeal _).comap (algebraMap O (Localization.AtPrime P)) = P
    exact Localization.AtPrime.under_maximalIdeal
  show z ((spMap (algebraMap O (Localization.AtPrime P))) (IsLocalRing.closedPoint _)) = _
  rw [e]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  (𝔐 : HodgeCpt Y S y) {L : Type} [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X)

omit [∀ k, Fintype (J k)] in
theorem inFibre_loc (P : Ideal (𝓞 L)) [P.IsPrime] {p : ℕ} (hp : (p : 𝓞 L) ∈ P) :
    InFibre 𝔐.ξ p ⟨centre (spMap (algebraMap (𝓞 L) (Localization.AtPrime P)) ≫ z), 𝔐.all _⟩ := fun hu => by
  have h := (PositivityTheory.HtPt.Gh.unitAt_centre_iff 𝔐.tie.gen _ (𝔐.all _) p).1 hu
  rw [← map_natCast (algebraMap (𝓞 L) (Localization.AtPrime P))] at h
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P _).1 h hp


set_option maxHeartbeats 800000 in
theorem loc {V : Type} [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V]
    (ML : LieModel 𝔐.t.G (spMap (algebraMap (𝓞 L) L) ≫ z) V) (ρ : 𝓞 E →+* Module.End L V)
    (hact : ML.IsActOf 𝔐.t.act.act ρ) (σ₀ : CMType H ⊕ CMType H → (𝓞 E →+* 𝓞 L))
    (hσ : ∀ s a, ValAt 𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (𝔐.emb s a) (algebraMap (𝓞 L) L (σ₀ s a)))
    (hinj : Function.Injective fun s => (algebraMap (𝓞 L) L).comp (σ₀ s)) (κ : ℕ → Ω) (k : ℕ → 𝓞 L)
    (hκ : ∀ p ∈ S, HT.HTFree 𝔐 p ∧ HT.Sandwich 𝔐 p (κ p) ∧
      ValAt 𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (κ p) (algebraMap (𝓞 L) L (k p)))
    (hdisc : ∀ r : ℕ, r.Prime → (r : ℤ) ∣ discr E → r ∈ S) (s : CMType H ⊕ CMType H)
    (P : Ideal (𝓞 L)) [hP : P.IsPrime] (cc : Localization.AtPrime P →+* L)
    (hc : cc.comp (algebraMap (𝓞 L) _) = algebraMap (𝓞 L) L) :
    (∀ x ∈ eigSp ρ ((algebraMap (𝓞 L) L).comp (σ₀ s)),
      (∃ v : epsAt z ⟶ 𝔐.t.G, IsTanAt 𝔐.t.G z v ∧
        (ML.pt x).left = spMap (dualMap (algebraMap (𝓞 L) L)) ≫ v.left) →
      ∃ t ∉ P, t • x ∈ Submodule.span (𝓞 L) {x' | ∃ e ∈ 𝔐.V s ⟨z (⟨P, hP⟩ : PrimeSpectrum (𝓞 L)), 𝔐.all _⟩,
        𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')}) ∧
    ∀ x, (∃ t ∉ P, t • x ∈ Submodule.span (𝓞 L) {x' | ∃ e ∈ 𝔐.V s ⟨z (⟨P, hP⟩ : PrimeSpectrum (𝓞 L)), 𝔐.all _⟩,
        𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')}) → ∀ d ∈ differentIdeal ℤ (𝓞 E),
      (∏ p ∈ S, k p) • σ₀ s d • x ∈ eigSp ρ ((algebraMap (𝓞 L) L).comp (σ₀ s)) ∧
      ∃ w : epsAt (spMap (algebraMap (𝓞 L) (Localization.AtPrime P)) ≫ z) ⟶ 𝔐.t.G, IsTanAt 𝔐.t.G _ w ∧
        (ML.pt ((∏ p ∈ S, k p) • σ₀ s d • x)).left = spMap (dualMap cc) ≫ w.left := by
  classical
  have hξ := 𝔐.tie.gen
  let A := Localization.AtPrime P
  letI : Algebra A L := cc.toAlgebra
  have hc' : ∀ a, algebraMap A L (algebraMap (𝓞 L) A a) = algebraMap (𝓞 L) L a := fun a => RingHom.congr_fun hc a
  haveI : IsScalarTower (𝓞 L) A L := IsScalarTower.of_algebraMap_eq fun a => (hc' a).symm
  letI : Module A V := Module.compHom V cc
  haveI : IsScalarTower A L V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower (𝓞 L) A V := IsScalarTower.of_algebraMap_smul fun r x => by
    rw [← algebraMap_smul L (algebraMap (𝓞 L) A r) x, hc', algebraMap_smul]
  haveI : IsFractionRing A L := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl A L
  have inj := IsFractionRing.injective A L
  let zA : Sp A ⟶ 𝔐.X := spMap (algebraMap (𝓞 L) A) ≫ z
  have hzL : spMap (algebraMap (𝓞 L) L) ≫ z = Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ zA := by
    rw [← hc, ← Category.assoc]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    rfl
  obtain ⟨MC, hM1, hM2, hM3⟩ := lie_cast 𝔐.M hzL ML _ ρ hact
  have hq : (⟨centre zA, 𝔐.all _⟩ : Cpt 𝔐.ξ) = ⟨z (⟨P, hP⟩ : PrimeSpectrum (𝓞 L)), 𝔐.all _⟩ :=
    Subtype.ext (centre_loc z P)
  have hmv : ∀ (e : 𝔐.Li) (q q' : Cpt 𝔐.ξ), q = q' → e ∈ 𝔐.V s q → e ∈ 𝔐.V s q' := by
    rintro e _ _ rfl h; exact h
  have hfib : ∀ x, x ∈ 𝔐.M.fibAt (𝔐.V s) zA MC ↔ ∃ t ∉ P, t • x ∈ Submodule.span (𝓞 L)
      {x' | ∃ e ∈ 𝔐.V s ⟨z (⟨P, hP⟩ : PrimeSpectrum (𝓞 L)), 𝔐.all _⟩,
        𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')} := by
    intro x
    have e1 : 𝔐.M.fibAt (𝔐.V s) zA MC = Submodule.span A
        {x' | ∃ e ∈ 𝔐.V s ⟨z (⟨P, hP⟩ : PrimeSpectrum (𝓞 L)), 𝔐.all _⟩,
          𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')} := by
      unfold LieModel.fibAt
      congr 1
      ext w
      exact ⟨fun ⟨_, e, h1, h2⟩ => ⟨e, hmv e _ _ hq h1, (hM2 _ _).1 h2⟩,
        fun ⟨e, h1, h2⟩ => ⟨𝔐.all _, e, hmv e _ _ hq.symm h1, (hM2 _ _).2 h2⟩⟩
    rw [e1, IsLocalization.mem_span_iff P.primeCompl]
    have e2 : ∀ (t : P.primeCompl) (u : V), (t : 𝓞 L) • IsLocalization.mk' A (1 : 𝓞 L) t • u = u := fun t u => by
      rw [← algebraMap_smul A (t : 𝓞 L), smul_smul, IsLocalization.mk'_spec', map_one, one_smul]
    constructor
    · rintro ⟨u, hu, t, rfl⟩
      exact ⟨t, t.2, by rwa [e2]⟩
    · rintro ⟨t, ht, h⟩
      exact ⟨_, h, ⟨t, ht⟩, by rw [smul_comm]; exact (e2 ⟨t, ht⟩ x).symm⟩
  have hlat := GlobalTheory.T.lie_lattice_eval_fraction_field 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M A zA L V MC hξ 𝔐.t.semi.smooth (𝔐.all _) (𝔐.all _)
  have hval : ∀ {a : Ω} {r : A} {n : 𝓞 L}, ValAt 𝔐.ξ zA a r →
      ValAt 𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z) a (algebraMap (𝓞 L) L n) →
      ValAt 𝔐.ξ zA a (algebraMap (𝓞 L) A n) := fun {a r n} h1 h2 => by
    have h3 := LieTangent.valAt_base hξ (algebraMap A L) h1
    rw [← hzL] at h3
    have h4 := LieTangent.valAt_unique hξ h3 h2
    rw [← hc'] at h4
    rwa [← inj h4]
  let σA : CMType H ⊕ CMType H → (𝓞 E →+* A) := fun s => (algebraMap (𝓞 L) A).comp (σ₀ s)
  have hσA : ∀ s a, ValAt 𝔐.ξ zA (𝔐.emb s a) (σA s a) := fun s a => by
    obtain ⟨r, hr⟩ := emb_value 𝔐 zA s a
    exact hval hr (hσ s a)
  have hσe : ∀ s, (algebraMap A L).comp (σA s) = (algebraMap (𝓞 L) L).comp (σ₀ s) := fun s =>
    RingHom.ext fun a => hc' _
  have main : 𝔐.M.fibAt 𝔐.M.lat zA MC ⊓ (eigSp ρ ((algebraMap A L).comp (σA s))).restrictScalars A ≤
      𝔐.M.fibAt (𝔐.V s) zA MC ∧ ∀ w ∈ 𝔐.M.fibAt (𝔐.V s) zA MC, ∀ d ∈ differentIdeal ℤ (𝓞 E),
      algebraMap (𝓞 L) A (∏ p ∈ S, k p) • σA s d • w ∈
        𝔐.M.fibAt 𝔐.M.lat zA MC ⊓ (eigSp ρ ((algebraMap A L).comp (σA s))).restrictScalars A := by
    by_cases hex : ∃ p ∈ S, (p : 𝓞 L) ∈ P
    · obtain ⟨p, hpS, hp⟩ := hex
      have hp0 : (p : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.2 (𝔐.S_prime p hpS).ne_zero
      have hP0 : P ≠ ⊥ := fun h => hp0 (by rwa [h, Ideal.mem_bot] at hp)
      haveI : IsDiscreteValuationRing A :=
        IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) hP0 A
      obtain ⟨v, hv, hv1⟩ := exists_val A L
      have hvp : v (p : L) < 1 := by
        have := hv1 (algebraMap (𝓞 L) A p) fun h => (IsLocalization.AtPrime.isUnit_to_map_iff A P _).1 h hp
        rwa [hc', map_natCast] at this
      obtain ⟨h1, h2, h3⟩ := hκ p hpS
      obtain ⟨r, hr⟩ := exists_value zA (𝔐.all _) (h2 _ (inFibre_loc 𝔐 z P hp)).1
      obtain ⟨a1, a2⟩ := on_S 𝔐 zA MC ρ hM3 hpS (κ p) h1 h2 v hv hvp s (σA s) (hσA s) _ (hval hr h3)
      refine ⟨a1, fun w hw d hd => ?_⟩
      rw [← Finset.prod_erase_mul S k hpS, map_mul, mul_smul]
      exact Submodule.smul_mem _ _ (a2 w hw d hd)
    · have hun : ∀ n : ℕ, (n : 𝓞 L) ∉ P → IsUnit (n : A) := fun n hn => by
        rw [← map_natCast (algebraMap (𝓞 L) A)]
        exact IsLocalization.map_units A (⟨n, hn⟩ : P.primeCompl)
      have e := off_S 𝔐 zA MC ρ hM3 σA hσA (by simpa only [hσe] using hinj)
        (fun p hp => hun p fun h => hex ⟨p, hp, h⟩)
        (hun _ fun h => by
          obtain ⟨r, h1, h2, h3⟩ := exists_prime_mem P _ (Int.natAbs_ne_zero.2 (discr_ne_zero E)) h
          exact hex ⟨r, hdisc r h1 (Int.natCast_dvd.2 h2), h3⟩) s
      refine ⟨e.ge, fun w hw d _ => ?_⟩
      rw [← e]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hw)
  rw [hσe] at main
  refine ⟨fun x hx ⟨v, hv, hxv⟩ => (hfib x).1 (main.1 ⟨(hlat x).2 ?_, hx⟩), fun x hx d hd => ?_⟩
  · refine ⟨LieCarrier.epsHom (algebraMap (𝓞 L) A) z zA rfl ≫ v, LieFib.isTanAt_epsHom _ _ _ _ _ hv, ?_⟩
    rw [hM1, hxv, ← hc]
    exact (congrArg (· ≫ v.left) (LieFib.spec_dualMap_comp _ cc)).trans (Category.assoc _ _ _)
  · obtain ⟨h1, h2⟩ := main.2 x ((hfib x).2 hx) d hd
    have e : algebraMap (𝓞 L) A (∏ p ∈ S, k p) • σA s d • x = (∏ p ∈ S, k p) • σ₀ s d • x := by
      rw [algebraMap_smul]
      exact congrArg _ (algebraMap_smul A (σ₀ s d) x)
    rw [e] at h1 h2
    obtain ⟨w, hw, hw'⟩ := (hlat _).1 h1
    exact ⟨h2, w, hw, (hM1 _).symm.trans hw'⟩

end LevelTowerAlt.LocalPrimeBound
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section
namespace LevelTowerAlt
open LevelTowerAlt.LocalPrimeBound
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem abelian_part_integral_point_bis : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V), 1 ≤ D.p + D.q → (∀ r : ℕ, r.Prime → (r : ℤ) ∣ discr E → r ∈ S) → (∀ p ∈ S, HT.HTFree 𝔐 p) → 𝔐.IsLinPtOf z P MV A → ∀ s, ∃ 𝔞 : Ideal (𝓞 L), 𝔞 ≠ ⊥ ∧ 𝔞 • 𝔐.FibLat (𝔐.V s) z P MV ≤ A.eig s ∧ 𝔞 • A.eig s ≤ 𝔐.FibLat (𝔐.V s) z P MV ∧ Real.log (Ideal.absNorm 𝔞) / Module.finrank ℚ L ≤ 2 * (∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1)) + 2 * Real.log (hostRd E) := by
  intro hG E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 L _ _ z P V _ _ _ _ MV A hpq hdisc hfree hA s
  classical
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  haveI := 𝔐.t.semi.smooth
  obtain ⟨hact, hlab, hΛ, -⟩ := hA
  obtain ⟨ML, hML⟩ := (LieMove.main L 𝔐.X (spMap (algebraMap (𝓞 L) L) ≫ z) 𝔐.t.G P.tK.G P.m.φ V P.m.cart).2 MV
  have hactL : ML.IsActOf 𝔐.t.act.act A.ρ := fun a x => Over.OverMorphism.ext (by
    rw [← hML, hact a x, Over.comp_left, Over.comp_left, Category.assoc, P.m.act, ← hML, Category.assoc])
  let jE : CMType H ⊕ CMType H → (E →+* L) := fun s => IsFractionRing.lift (A.σ_inj s)
  let σ₀ : CMType H ⊕ CMType H → (𝓞 E →+* 𝓞 L) := fun s => RingOfIntegers.mapRingHom (jE s)
  have hσ₀ : ∀ s, (algebraMap (𝓞 L) L).comp (σ₀ s) = A.σ s := fun s => RingHom.ext fun a =>
    IsFractionRing.lift_algebraMap (A.σ_inj s) a
  have hσ : ∀ s a, ValAt 𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (𝔐.emb s a) (algebraMap (𝓞 L) L (σ₀ s a)) :=
    fun s a => by
      have h := hlab s a
      rw [← hσ₀] at h
      exact h
  have hinj : Function.Injective fun s => (algebraMap (𝓞 L) L).comp (σ₀ s) := by
    simpa only [hσ₀] using A.σ_bij.1
  have hex : ∀ p : ℕ, ∃ (κ : Ω) (k : 𝓞 L), p ∈ S → (HT.HTFree 𝔐 p ∧ HT.Sandwich 𝔐 p κ ∧
      ValAt 𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z) κ (algebraMap (𝓞 L) L k)) ∧ k ≠ 0 ∧
      Real.log (Ideal.absNorm (Ideal.span {k})) ≤ Module.finrank ℚ L * (2 * (Real.log p / ((p : ℝ) - 1))) := by
    intro p
    by_cases hpS : p ∈ S
    swap
    · exact ⟨0, 0, fun h => absurd h hpS⟩
    have hp := 𝔐.S_prime p hpS
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨κ, hκ, hS⟩ := GlobalTheory.T.exists_sandwich_of_hodge_tate_free hG.2.2.2.2.2.2.1 E H D l Xo c _ _ Y S Ω K J y 𝔐 p hpS hpq (hfree p hpS)
    have hne : Ideal.span {(p : 𝓞 L)} ≠ ⊤ := fun h => by
      have h1 := congrArg Ideal.absNorm h
      rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top, RingOfIntegers.rank] at h1
      exact (Nat.one_lt_pow Module.finrank_pos.ne' hp.one_lt).ne' h1
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    have hpQ : (p : 𝓞 L) ∈ Q := hle (Ideal.mem_span_singleton_self _)
    have h1 := (hS _ (inFibre_loc 𝔐 z Q hpQ)).1
    have hq : (⟨centre (spMap (algebraMap (𝓞 L) (Localization.AtPrime Q)) ≫ z), 𝔐.all _⟩ : Cpt 𝔐.ξ) =
        ⟨z (⟨Q, hQ.isPrime⟩ : PrimeSpectrum (𝓞 L)), 𝔐.all _⟩ := Subtype.ext (centre_loc z Q)
    rw [hq] at h1
    obtain ⟨r, -, -, hr, -⟩ := PtHt.FinFrame.reg_value z hξ ⟨Q, hQ.isPrime⟩ (𝔐.all _) h1
    obtain ⟨a1, a2⟩ := value_cp hξ hp hκ hr
    obtain ⟨k, rfl, b1, b2⟩ := const_int hp a1 a2
    exact ⟨κ, k, fun _ => ⟨⟨hfree p hpS, hS, hr⟩, b1, b2⟩⟩
  choose κ k hk using hex
  obtain ⟨n1, n2⟩ := norm_bound (jE s) S k fun p hp => (hk p hp).2
  have hset : ∀ 𝔭 : PrimeSpectrum (𝓞 L), {x' : V | ∃ e ∈ 𝔐.V s ⟨z 𝔭, 𝔐.all _⟩,
      ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ 𝔐.t.G,
      𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ (MV.pt x').left ≫ P.m.φ = v.left} =
      {x' | ∃ e ∈ 𝔐.V s ⟨z 𝔭, 𝔐.all _⟩, 𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')} := fun 𝔭 => by
    ext x'
    constructor
    · rintro ⟨e, he, v, hv, h⟩
      have e' : v = ML.pt x' := Over.OverMorphism.ext (h.symm.trans (hML _))
      exact ⟨e, he, e' ▸ hv⟩
    · rintro ⟨e, he, hv⟩
      exact ⟨e, he, _, hv, hML _⟩
  have hF : ∀ x, x ∈ 𝔐.FibLat (𝔐.V s) z P MV ↔ ∀ 𝔭 : PrimeSpectrum (𝓞 L), ∃ t ∉ 𝔭.asIdeal, t • x ∈
      Submodule.span (𝓞 L) {x' | ∃ e ∈ 𝔐.V s ⟨z 𝔭, 𝔐.all _⟩,
        𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')} := fun x => by
    simp only [HodgeCpt.FibLat, hset, Submodule.mem_iInf]
    exact forall_congr' fun 𝔭 => PtHt.FinFrame.span_sat_iff 𝔭.asIdeal le_rfl
      (fun u hu => ⟨1, (Ideal.ne_top_iff_one _).1 𝔭.isPrime.ne_top, by rwa [one_smul]⟩) x
  have hcc : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime], ∃ cc : Localization.AtPrime Q →+* L,
      cc.comp (algebraMap (𝓞 L) _) = algebraMap (𝓞 L) L := fun Q _ => by
    have hunit : ∀ d : Q.primeCompl, IsUnit (algebraMap (𝓞 L) L d) := fun d =>
      isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2
        fun e => d.2 (e ▸ Q.zero_mem))
    exact ⟨IsLocalization.lift (M := Q.primeCompl) hunit, IsLocalization.lift_comp hunit⟩
  have hloc := fun (Q : Ideal (𝓞 L)) [Q.IsPrime] cc hc =>
    loc 𝔐 z ML A.ρ hactL σ₀ hσ hinj κ k (fun p hp => (hk p hp).1) hdisc s Q cc hc
  rw [hσ₀] at hloc
  refine ⟨_, n1, Submodule.smul_le.2 fun a ha x hx => ?_, Submodule.smul_le.2 fun a _ x hx => ?_, n2⟩
  · have hx' := (hF x).1 hx
    have key : ∀ d ∈ differentIdeal ℤ (𝓞 E), (∏ p ∈ S, k p) • σ₀ s d • x ∈ A.eig s := fun d hd => by
      refine ⟨(hΛ _).2 ?_, ?_⟩
      · let MB := LiePull.extModel (g := algebraMap (𝓞 L) L) (x := z) (FaithfulSMul.algebraMap_injective _ _) rfl ML
        obtain ⟨e, he⟩ := GlobalTheory.T.tangent_vector_extends_dvr (𝓞 L) L 𝔐.X z 𝔐.t.G _ MB (ML.pt ((∏ p ∈ S, k p) • σ₀ s d • x)) (ML.tan _)
          fun Q hQ cc hc => ((hloc Q cc hc).2 x (hx' ⟨Q, hQ.isPrime⟩) d hd).2
        exact ⟨MB.pt e, MB.tan e, (hML _).trans ((Category.comp_id _).symm.trans he)⟩
      · obtain ⟨cc, hc⟩ := hcc ⊥
        exact ((hloc ⊥ cc hc).2 x (hx' ⟨⊥, Ideal.isPrime_bot⟩) d hd).1
    have h1 : (differentIdeal ℤ (𝓞 E)).map (σ₀ s) ≤
        (A.eig s).comap (LinearMap.toSpanSingleton (𝓞 L) V ((∏ p ∈ S, k p) • x)) :=
      Ideal.map_le_iff_le_comap.2 fun d hd => by
        show σ₀ s d • (∏ p ∈ S, k p) • x ∈ A.eig s
        rw [smul_comm]
        exact key d hd
    have h2 : (differentIdeal ℤ (𝓞 E)).map (σ₀ s) * Ideal.span {∏ p ∈ S, k p} ≤
        (A.eig s).comap (LinearMap.toSpanSingleton (𝓞 L) V x) :=
      Ideal.mul_le.2 fun r hr t ht => by
        obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ht
        show (r * (u * ∏ p ∈ S, k p)) • x ∈ A.eig s
        rw [mul_left_comm, mul_smul, mul_smul]
        exact Submodule.smul_mem _ _ (h1 hr)
    exact h2 ha
  · refine Submodule.smul_mem _ _ ((hF x).2 fun 𝔭 => ?_)
    obtain ⟨cc, hc⟩ := hcc 𝔭.asIdeal
    obtain ⟨v, hv, hxv⟩ := (hΛ x).1 hx.1
    exact (hloc 𝔭.asIdeal cc hc).1 x hx.2 ⟨v, hv, (hML x).symm.trans hxv⟩

end LevelTowerAlt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartIntegralPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.abelian_part_integral_point : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V), 1 ≤ D.p + D.q → (∀ r : ℕ, r.Prime → (r : ℤ) ∣ discr E → r ∈ S) → (∀ p ∈ S, HT.HTFree 𝔐 p) → 𝔐.IsLinPtOf z P MV A → ∀ s, ∃ 𝔞 : Ideal (𝓞 L), 𝔞 ≠ ⊥ ∧ 𝔞 • 𝔐.FibLat (𝔐.V s) z P MV ≤ A.eig s ∧ 𝔞 • A.eig s ≤ 𝔐.FibLat (𝔐.V s) z P MV ∧ Real.log (Ideal.absNorm 𝔞) / Module.finrank ℚ L ≤ 2 * (∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1)) + 2 * Real.log (hostRd E) := by
  first | exact @LevelTowerAlt.abelian_part_integral_point_bis | exact LevelTowerAlt.abelian_part_integral_point_bis
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartIntegralPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_part_integral_point : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V), 1 ≤ D.p + D.q → (∀ r : ℕ, r.Prime → (r : ℤ) ∣ discr E → r ∈ S) → (∀ p ∈ S, HT.HTFree 𝔐 p) → 𝔐.IsLinPtOf z P MV A → ∀ s, ∃ 𝔞 : Ideal (𝓞 L), 𝔞 ≠ ⊥ ∧ 𝔞 • 𝔐.FibLat (𝔐.V s) z P MV ≤ A.eig s ∧ 𝔞 • A.eig s ≤ 𝔐.FibLat (𝔐.V s) z P MV ∧ Real.log (Ideal.absNorm 𝔞) / Module.finrank ℚ L ≤ 2 * (∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1)) + 2 * Real.log (hostRd E) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.abelian_part_integral_point | exact GlobalTheory.CompanionTheory.Relay.abelian_part_integral_point | (intros; apply GlobalTheory.CompanionTheory.Relay.abelian_part_integral_point <;> assumption)
end

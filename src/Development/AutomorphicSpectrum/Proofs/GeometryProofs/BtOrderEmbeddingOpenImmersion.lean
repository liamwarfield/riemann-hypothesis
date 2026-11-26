module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockPullbackHermLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenCover
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderFlatBaseChange
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundle
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodHermitianTypeCompatibility
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRing
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianPeriodLinearAlgebra
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncModelEmbeddedLogResolution
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinCoordsArithVar
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.FderivAffCoordZero
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenImmersion
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenImmersion
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem btEmb_localData (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤)))
    (hj : Γ.IsEmb (Γ.btOrder ⊤) j) (R' : Type) [CommRing R'] [IsDomain R'] [HenselianLocalRing R'] [Algebra R R']
    [IsIntegrallyClosed R'] (hflat : Module.Flat R R') :
    ∃ (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left) (j' : Γ'.G.left ⟶ Spec (CommRingCat.of (Γ'.btOrder ⊤)))
      (ψ : Γ.btOrder ⊤ →+* Γ'.btOrder ⊤) (U : Γ'.G.left.Opens),
      (∀ (a : Γ.btOrder ⊤) (t : T), (ψ a).1 t = algebraMap R R' (a.1 t)) ∧
      IsPullback (Spec.map (CommRingCat.ofHom ψ)) (Spec.map (CommRingCat.ofHom (algebraMap R' (Γ'.btOrder ⊤))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧
      IsPullback F j' j (Spec.map (CommRingCat.ofHom ψ)) ∧
      IsOpenImmersion (U.ι ≫ j') ∧ Γ'.TranslatesCover (Γ'.btOrder ⊤) j' U ∧
      ∀ x : Γ'.G.left, Spec.map (CommRingCat.ofHom (algebraMap R' (Γ'.btOrder ⊤))) (j' x) =
        IsLocalRing.closedPoint R' → x ∈ U := by
  have hA := GlobalTheory.CompanionTheory.Relay.btOrder_isHopfOrder_noetherian R T Γ
  have hinj : Function.Injective (algebraMap R R') := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hreg : IsSMulRegular R' r :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R') (mem_nonZeroDivisors_of_ne_zero hr0)
    have : r • (1 : R') = r • (0 : R') := by
      simp [Algebra.smul_def, hr]
    exact one_ne_zero (hreg this)
  obtain ⟨Γ', F, hbc⟩ := GlobalTheory.T.exists_base_change_group R T Γ R' (algebraMap R R') hinj
  haveI := Γ'.quasiFinite
  haveI := Γ'.separated
  haveI := Γ'.quasiCompact
  haveI := Γ'.finPres
  obtain ⟨U, hUfin, hUcl⟩ := GlobalTheory.T.henselian_quasi_finite_finite_part R' Γ'.G.left Γ'.G.hom
  have hU : Γ'.IsFinOpenSub U := GlobalTheory.T.isFinOpenSub_of_finite R' T Γ' U hUfin hUcl
  obtain ⟨j', hj'⟩ := (GlobalTheory.T.existsUnique_btOrder_embedding R' T Γ').exists
  have hbt := GlobalTheory.T.btOrder_flat_base_change R T Γ R' Γ' F hbc hflat
  have hfull : ∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ Γ.btOrder ⊤ := by
    obtain ⟨d, hd, hf⟩ := hA.full
    exact ⟨d, fun h => hd (hinj (by simpa using h)), hf⟩
  have hext := (GlobalTheory.T.hopf_order_scalar_extension R T R' (Γ.btOrder ⊤) hA hfull).2
  have hext' : ∃ e : R' ⊗[R] (Γ.btOrder ⊤) ≃ₐ[R'] Γ'.btOrder ⊤,
      ∀ (a : Γ.btOrder ⊤) (t : T), (e (1 ⊗ₜ a)).1 t = algebraMap R R' (a.1 t) := by
    rw [hbt]; exact hext
  obtain ⟨e, he⟩ := hext'
  let iL : R' →+* R' ⊗[R] (Γ.btOrder ⊤) := Algebra.TensorProduct.includeLeftRingHom
  let iR : (Γ.btOrder ⊤) →+* R' ⊗[R] (Γ.btOrder ⊤) :=
    (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := Γ.btOrder ⊤)).toRingHom
  let ψ : Γ.btOrder ⊤ →+* Γ'.btOrder ⊤ := (e : R' ⊗[R] (Γ.btOrder ⊤) →+* Γ'.btOrder ⊤).comp iR
  have hψ : ∀ (a : Γ.btOrder ⊤) (t : T), (ψ a).1 t = algebraMap R R' (a.1 t) := fun a t => he a t
  have sq : IsPullback (Spec.map (CommRingCat.ofHom iL)) (Spec.map (CommRingCat.ofHom iR))
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R R' (Γ.btOrder ⊤))
  let eH : CommRingCat.of (R' ⊗[R] (Γ.btOrder ⊤)) ⟶ CommRingCat.of (Γ'.btOrder ⊤) :=
    CommRingCat.ofHom (e : R' ⊗[R] (Γ.btOrder ⊤) →+* Γ'.btOrder ⊤)
  haveI : IsIso eH := (e.toRingEquiv.toCommRingCatIso).isIso_hom
  have hb : Spec.map (CommRingCat.ofHom ψ) = Spec.map eH ≫ Spec.map (CommRingCat.ofHom iR) := by
    rw [← Spec.map_comp]; rfl
  have hq : Spec.map (CommRingCat.ofHom (algebraMap R' (Γ'.btOrder ⊤))) =
      Spec.map eH ≫ Spec.map (CommRingCat.ofHom iL) := by
    rw [← Spec.map_comp]
    congr 2
    ext r t
    exact congrArg (fun y : Γ'.btOrder ⊤ => y.1 t) (e.commutes r).symm
  have hsq : IsPullback (Spec.map (CommRingCat.ofHom ψ))
      (Spec.map (CommRingCat.ofHom (algebraMap R' (Γ'.btOrder ⊤))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤))))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
    refine IsPullback.of_iso sq.flip (asIso (Spec.map eH)).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [hb]
    · simp [hq]
    · simp
    · simp
  have hw : F ≫ j = j' ≫ Spec.map (CommRingCat.ofHom ψ) :=
    GlobalTheory.T.embedding_base_change_compat R T Γ R' Γ' F hbc _ _ ψ hψ j j' hj hj'
  have hsq2 : IsPullback F j' j (Spec.map (CommRingCat.ofHom ψ)) := by
    refine IsPullback.of_bot ?_ hw hsq
    rw [hj'.isOver, hj.isOver]
    exact hbc.cart
  obtain ⟨ho, hTC⟩ := GlobalTheory.T.btOrder_embedding_open_cover R' T Γ' U hU j' hj'
  refine ⟨Γ', F, j', ψ, U, hψ, hsq, hsq2, ho, hTC, fun x hx => hUcl x ?_⟩
  rw [← hj'.isOver]
  simpa using hx

theorem btEmb_specMap_asIdeal {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (x : Spec (CommRingCat.of B)) :
    (Spec.map (CommRingCat.ofHom φ) x).asIdeal = Ideal.comap φ x.asIdeal := rfl

theorem isOpenImmersion_emb_and_translatesCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsOpenImmersion j ∧ Γ.TranslatesCover (Γ.btOrder ⊤) j ⊤ := by
  intro R _ _ _ _ T _ _ Γ j hj
  have hA := GlobalTheory.CompanionTheory.Relay.btOrder_isHopfOrder_noetherian R T Γ
  refine ⟨?_, ?_⟩
  · haveI := hA.finite
    haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.finiteType_algebraMap.mpr inferInstance
    haveI : LocallyOfFinitePresentation (j ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) := by
      rw [hj.isOver]; exact Γ.finPres
    haveI := GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp j
      (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤))))
    refine GlobalTheory.T.flat_local_extension_exists R Γ.G.left _ j (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) ?_
    intro P _
    obtain ⟨R', _, _, _, _, hic, hflat, hcomap⟩ := GlobalTheory.T.exists_henselian_flat_over_prime R P
    obtain ⟨Γ', F, j', ψ, U, -, hsq, hsq2, ho, -, hcl⟩ := btEmb_localData R T Γ j hj R' hflat
    exact ⟨R', inferInstance, inferInstance, inferInstance, Γ'.G.left, _, j', _, F, _, U, hflat, hcomap, hsq, hsq2, ho, hcl⟩
  · intro P
    let p : Ideal R := P.asIdeal.comap (algebraMap R (Γ.btOrder ⊤))
    haveI : p.IsPrime := Ideal.comap_isPrime _ _
    obtain ⟨R', _, _, _, _, hic, hflat, hcomap⟩ := GlobalTheory.T.exists_henselian_flat_over_prime R p
    obtain ⟨Γ', F, j', ψ, U, hψ, hsq, hsq2, -, hTC, -⟩ := btEmb_localData R T Γ j hj R' hflat
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤))))
      (g := Spec.map (CommRingCat.ofHom (algebraMap R R'))) P (IsLocalRing.closedPoint R')
      (PrimeSpectrum.ext hcomap.symm)
    let Q := hsq.isoPullback.inv z
    have hQ : Spec.map (CommRingCat.ofHom ψ) Q = P := by
      rw [← hz1]
      change (hsq.isoPullback.inv ≫ Spec.map (CommRingCat.ofHom ψ)) z = _
      rw [hsq.isoPullback_inv_fst]
    obtain ⟨t, g', -, H⟩ := hTC Q
    refine ⟨t, F g', trivial, fun f f' hff => ?_⟩
    have h1 := H (ψ f) (ψ f') (fun h => by rw [hψ, hψ, hff])
    have hg : (j (F g')).asIdeal = Ideal.comap ψ (j' g').asIdeal := by
      rw [← btEmb_specMap_asIdeal]
      change ((F ≫ j) g').asIdeal = ((j' ≫ Spec.map (CommRingCat.ofHom ψ)) g').asIdeal
      rw [hsq2.w]
    rw [hg, ← hQ, btEmb_specMap_asIdeal]
    exact h1

end GlobalTheory.CompanionTheory.Ar.BT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenImmersionStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.btOrder_embedding_open_immersion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsOpenImmersion j ∧ Γ.TranslatesCover (Γ.btOrder ⊤) j ⊤ := by
  exact @GlobalTheory.CompanionTheory.Ar.BT.isOpenImmersion_emb_and_translatesCover
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagCmTypeLatticeComparison
section -- merged from Development.AutomorphicSpectrum.Statements.GeometryStatements.DivMemLineLat
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptInputs

theorem labelEmb_inr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (τ : CMType H) : labelEmb c (.inr τ) = tauIn c (ComplexEmbedding.conjugate τ.1) := by
  ext a
  show τ.1 ((H.bar a : 𝓞 E) : E) = ComplexEmbedding.conjugate τ.1 (a : E)
  rw [H.bar_eq]
  exact IsCMField.complexEmbedding_complexConj (K := E) τ.1 (a : E)

theorem labelEmb_inl {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (τ : CMType H) : labelEmb c (.inl τ) = tauIn c τ.1 := rfl

end GlobalTheory.CompanionTheory.Ar.Flat.CptInputs
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagCmTypeLatticeComparison
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptWedge

section LinAlg

variable {Ω₀ Ω V₀ V : Type} [Field Ω₀] [Field Ω] [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V]

theorem exists_wedge_eq_smul {n : ℕ} {e b : Fin n → V} (h : ∀ k, e k ∈ Submodule.span Ω (Set.range b)) :
    ∃ d : Ω, exteriorPower.ιMulti Ω n e = d • exteriorPower.ιMulti Ω n b := by
  choose T hT using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (h k)
  have he : e = fun k => ∑ l, (Matrix.of T) k l • b l := funext fun k => (hT k).symm
  exact ⟨(Matrix.of T).det, by rw [he]; exact GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family Ω V n b _⟩

theorem isPullWedge_smul_ιMulti (i : Ω₀ →+* Ω) (j : V₀ →+ V) (hj : IsExtOver i j) {n : ℕ} {u : Fin n → V₀}
    (hu : LinearIndependent Ω₀ u) {γ : Ω₀} (hγ : γ ≠ 0) :
    CptIn.IsPullWedge i j (γ • exteriorPower.ιMulti Ω₀ n u)
      (i γ • exteriorPower.ιMulti Ω n fun k => j (u k)) := by
  intro b α hab
  have hw := WedgeFrame.ιMulti_ne_zero hu
  have hα : α ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hab
    exact smul_ne_zero hγ hw hab
  have hbe : exteriorPower.ιMulti Ω₀ n b = (α⁻¹ * γ) • exteriorPower.ιMulti Ω₀ n u := by
    rw [mul_smul, hab, smul_smul, inv_mul_cancel₀ hα, one_smul]
  have hm := GlobalTheory.CompanionTheory.WedgeSpan.span_of_wedge_proportional Ω₀ V₀ n b u _ hu (mul_ne_zero (inv_ne_zero hα) hγ) hbe
  choose T hT using fun k => (Submodule.mem_span_range_iff_exists_fun Ω₀).1 (hm k)
  have hb : b = fun k => ∑ l, (Matrix.of T) k l • u l := funext fun k => (hT k).symm
  have h1 : exteriorPower.ιMulti Ω₀ n b = (Matrix.of T).det • exteriorPower.ιMulti Ω₀ n u := by
    rw [hb]; exact GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family Ω₀ V₀ n u _
  have h2 : γ = α * (Matrix.of T).det := by
    rw [h1, smul_smul] at hab
    exact smul_left_injective Ω₀ hw hab
  have h3 : (fun k => j (b k)) = fun k => ∑ l, (i.mapMatrix (Matrix.of T)) k l • j (u l) := by
    funext k
    rw [hb]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, hj.1]
    rfl
  rw [h3, GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family Ω V n _ _, ← RingHom.map_det, smul_smul, ← map_mul, ← h2]

end LinAlg

theorem exists_eq_smul_ιMulti {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type}
    [AddCommGroup E] [Module Ω E] {L : Lat ξ E} {r : ℕ} {u : Fin r → E} {x : Cpt ξ} (hu : L.IsFrameAt u x)
    {a : ⋀[Ω]^r E} {α : Ω} (hα : α ≠ 0) (hw : L.wedge r x = Submodule.span (regAt ξ x) {α • a}) :
    ∃ γ : Ω, γ ≠ 0 ∧ a = γ • exteriorPower.ιMulti Ω r u := by
  obtain ⟨h1, h2⟩ := WedgeFrame.wedge_eq_span_ιMulti X Ω ξ E L r u x hu
  have h3 : exteriorPower.ιMulti Ω r u ∈ Submodule.span (regAt ξ x) {α • a} := by
    rw [← hw, h1]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 h3
  have ht' : ((t : Ω) * α) • a = exteriorPower.ιMulti Ω r u := by
    rw [mul_smul]; exact ht
  have ht0 : (t : Ω) * α ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at ht'
    exact h2 ht'.symm
  exact ⟨((t : Ω) * α)⁻¹, inv_ne_zero ht0, by rw [← ht', smul_smul, inv_mul_cancel₀ ht0, one_smul]⟩

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {U : Set (Xo.XF c)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

theorem tie_act {Z : CptOver Y U} {𝔐 : HodgeCpt Y S y} {i : Z.Ω →+* Ω} {j : Z.V →+ 𝔐.Li}
    (h : CptIn.IsTie Z 𝔐 i j) (a : 𝓞 E) (e : Z.V) : j (Z.ρ a e) = 𝔐.ρ a (j e) := by
  obtain ⟨-, -, -, h4⟩ := h
  refine 𝔐.M.inj (Over.OverMorphism.ext (𝔐.m.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)))
  rw [h4, Z.act a e, 𝔐.act a (j e), Over.comp_left, Over.comp_left, Category.assoc, 𝔐.m.act, ← Category.assoc]
  exact (congrArg (· ≫ Over.Hom.left (Y.t.act.act a)) (h4 e).symm).trans (Category.assoc _ _ _)

theorem tie_mem_eigSp {Z : CptOver Y U} {𝔐 : HodgeCpt Y S y} {i : Z.Ω →+* Ω} {j : Z.V →+ 𝔐.Li}
    (h : CptIn.IsTie Z 𝔐 i j) (σ : 𝓞 E →+* c.F) {e : Z.V} (he : e ∈ eigSp Z.ρ (Z.inc.comp σ)) :
    j e ∈ eigSp 𝔐.ρ (𝔐.cst.comp σ) := by
  have hi := h.2.1
  have hs := h.2.2.1.1
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at he ⊢
  intro a
  rw [← tie_act h, he a, hs, ← hi]
  rfl

theorem exists_side {Z : CptOver Y U} {𝔐 : HodgeCpt Y S y} {i : Z.Ω →+* Ω} {j : Z.V →+ 𝔐.Li}
    (h : CptIn.IsTie Z 𝔐 i j) {L : Lat (Z.ξ₀ ≫ Y.j) Z.V} {r : ℕ} {u : Fin r → Z.V} {x : Cpt (Z.ξ₀ ≫ Y.j)}
    (hu : L.IsFrameAt u x) {a : ⋀[Z.Ω]^r Z.V} {α : Z.Ω} (hα : α ≠ 0)
    (hw : L.wedge r x = Submodule.span (regAt (Z.ξ₀ ≫ Y.j) x) {α • a}) {B : Fin r → 𝔐.Li}
    (hB : ∀ k, j (u k) ∈ Submodule.span Ω (Set.range B)) :
    ∃ (a' : ⋀[Ω]^r 𝔐.Li) (d : Ω), d ≠ 0 ∧ a' ≠ 0 ∧ CptIn.IsPullWedge i j a a' ∧
      a' = d • exteriorPower.ιMulti Ω r B := by
  obtain ⟨γ, hγ, rfl⟩ := exists_eq_smul_ιMulti hu hα hw
  have hj : IsExtOver i j := h.2.2.1
  have hind : LinearIndependent Ω fun k => j (u k) := hj.2 r u hu.1
  have hne := WedgeFrame.ιMulti_ne_zero hind
  obtain ⟨d, hd⟩ := exists_wedge_eq_smul hB
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hd
    exact hne hd
  have hiγ : i γ ≠ 0 := (map_ne_zero i).2 hγ
  exact ⟨_, i γ * d, mul_ne_zero hiγ hd0, smul_ne_zero hiγ hne, isPullWedge_smul_ιMulti i j hj hu.1 hγ,
    by rw [hd, smul_smul]⟩

end Comparison₂

theorem exists_pullWedge_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V), CptIn.IsTie Z 𝔐 i j → IsLineGenOn (Z.eig τ.1) (Z.eig (ComplexEmbedding.conjugate τ.1)) D.p D.q a b Z.genFib → ∃ (a' : ⋀[Ω]^D.p 𝔐.Li) (b' : ⋀[Ω]^D.q 𝔐.Li) (d₁ d₂ : Ω), d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ a' ≠ 0 ∧ b' ≠ 0 ∧ CptIn.IsPullWedge i j a a' ∧ CptIn.IsPullWedge i j b b' ∧ a' = d₁ • (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) ∧ b' = d₂ • (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) := by
  intro E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 Fl τ i j a b hT hL
  have hfr : ∀ x : c.F, ∃ a b : 𝓞 c.F, algebraMap (𝓞 c.F) c.F b ≠ 0 ∧
      x * algebraMap (𝓞 c.F) c.F b = algebraMap (𝓞 c.F) c.F a := by
    intro x
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 c.F)) x
    exact ⟨a, b, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2, hab⟩
  obtain ⟨h1, h2, -, x, hx⟩ := isVBOn_eig_genFib E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y U Z τ.1
    ⟨FaithfulSMul.algebraMap_injective _ _, inferInstance, hfr⟩ τ.2
  obtain ⟨-, -, hg⟩ := hL
  obtain ⟨α, β, hα, hβ, hwa, hwb, -⟩ := hg x hx
  obtain ⟨W₁, hW₁, u₁, hs₁, hf₁⟩ := h1 x hx
  obtain ⟨W₂, hW₂, u₂, hs₂, hf₂⟩ := h2 x hx
  have hu₁ := hf₁ x hx hW₁
  have hu₂ := hf₂ x hx hW₂
  have hB₁ : ∀ k, j (u₁ k) ∈ Submodule.span Ω (Set.range (Fl.b (.inl τ))) := fun k => by
    rw [HodgeCptTest.flag_span 𝔐 Fl]
    have hk : u₁ k ∈ eigSp Z.ρ (Z.inc.comp (tauIn c τ.1)) := hs₁ ▸ Submodule.subset_span ⟨k, rfl⟩
    have := tie_mem_eigSp hT _ hk
    rwa [← CptInputs.labelEmb_inl] at this
  have hB₂ : ∀ k, j (u₂ k) ∈ Submodule.span Ω (Set.range (Fl.b (.inr τ))) := fun k => by
    rw [HodgeCptTest.flag_span 𝔐 Fl]
    have hk : u₂ k ∈ eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ.1))) :=
      hs₂ ▸ Submodule.subset_span ⟨k, rfl⟩
    have := tie_mem_eigSp hT _ hk
    rwa [← CptInputs.labelEmb_inr] at this
  obtain ⟨a', d₁, hd₁, ha', hpa, hea⟩ := exists_side hT hu₁ hα hwa (B := Fl.b (.inl τ)) hB₁
  obtain ⟨b', d₂, hd₂, hb', hpb, heb⟩ := exists_side hT hu₂ hβ hwb (B := Fl.b (.inr τ)) hB₂
  exact ⟨a', b', d₁, d₂, hd₁, hd₂, ha', hb', hpa, hpb, hea, heb⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CptWedge
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagCmTypeLatticeComparisonStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cm_type_lattice_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V), CptIn.IsTie Z 𝔐 i j → IsLineGenOn (Z.eig τ.1) (Z.eig (ComplexEmbedding.conjugate τ.1)) D.p D.q a b Z.genFib → ∃ (a' : ⋀[Ω]^D.p 𝔐.Li) (b' : ⋀[Ω]^D.q 𝔐.Li) (d₁ d₂ : Ω), d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ a' ≠ 0 ∧ b' ≠ 0 ∧ CptIn.IsPullWedge i j a a' ∧ CptIn.IsPullWedge i j b b' ∧ a' = d₁ • (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) ∧ b' = d₂ • (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CptWedge.exists_pullWedge_flag | exact GlobalTheory.CompanionTheory.Ar.Flat.CptWedge.exists_pullWedge_flag | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CptWedge.exists_pullWedge_flag <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFrameOne
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFrameOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem anSolve : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∀ (i : Fin FU.n) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (P : (FU.Di i).La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q), LinearIndependent (𝓞 E) e → IsPeriod (FU.Di i) ty P → under y = FU.u i P → IsFramed Set.univ τ σ y v w → ∃! x : (Fin D.p → Fin g → ℂ) × (Fin D.q → Fin g → ℂ) × Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ × Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ × ℂ, (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (x.1 a) (v a).left) ∧ (∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left) (x.2.1 j) (w j).left) ∧ (∀ n, tyPart ty (ComplexEmbedding.conjugate τ') (P (e n)) = ∑ j, x.2.2.2.1 j n • x.2.1 j) ∧ (∀ j n, ∑ m, x.2.2.1 j m * τ' (sesq (FU.Di i) (e m) (e n)) = x.2.2.2.1 j n) ∧ x.2.2.2.2 ≠ 0 ∧ (∃ C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ, ∀ a, tyPart ty τ' (∑ m, C a m • P (e m)) = x.1 a) ∧ ∀ C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ, (∀ a, tyPart ty τ' (∑ m, C a m • P (e m)) = x.1 a) → (Matrix.fromRows C x.2.2.1).det = x.2.2.2.2 := by
  intro E _ _ _ H D l Xo c τ τ' σ g ty FU _ _ hτ i e P y v w he hP hy hfr
  obtain ⟨-, -, hv, hw⟩ := hfr
  have hc : ∀ a : 𝓞 E, (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) a = ComplexEmbedding.conjugate τ' (a : E) := by
    intro a
    have h1 : tauIn c (ComplexEmbedding.conjugate τ) a = tauIn c τ (H.bar a) := by
      apply Subtype.ext
      show ComplexEmbedding.conjugate τ (a : E) = τ ((H.bar a : 𝓞 E) : E)
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
      rfl
    show σ (tauIn c (ComplexEmbedding.conjugate τ) a) = _
    rw [h1, hτ, H.bar_eq, IsCMField.complexEmbedding_complexConj]
    rfl
  obtain ⟨V, hVd, hVl, hVs⟩ := GlobalTheory.T.period_eigen_frame E H D l Xo _ g ty FU i P (under y) (σ.comp (tauIn c τ)) τ' D.p v hP hy hτ hv
  obtain ⟨W, hWd, hWl, hWs⟩ := GlobalTheory.T.period_eigen_frame E H D l Xo _ g ty FU i P (under y) _ (ComplexEmbedding.conjugate τ') D.q w hP hy hc hw
  obtain ⟨Hm, hHh, hHp, hHi⟩ := id hP.2.2.2.2
  obtain ⟨-, hs, hd⟩ := GlobalTheory.T.period_hermitian_type_compatibility E H (FU.Di i) g ty P Hm hP hHh hHi
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    rw [(FU.sig i).1, (FU.sig i).2]; simp
  have hS : (Matrix.of fun m n => τ' (sesq (FU.Di i) (e m) (e n))).det ≠ 0 := by
    have := hd 0 _ e hcard he
    have h2 : (Matrix.of fun m n => τ' (sesq (FU.Di i) (e m) (e n))) = (Matrix.of fun m n => sesq (FU.Di i) (e m) (e n)).map τ' := rfl
    rw [h2, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ').2 this
  have hlin : IsLinearMap ℂ (tyPart ty τ') := by
    constructor
    · intro a b; funext k; simp only [tyPart, Pi.add_apply]; split_ifs <;> simp
    · intro a b; funext k; simp only [tyPart, Pi.smul_apply]; split_ifs <;> simp
  obtain ⟨⟨Fm, B, d⟩, ⟨h1, h2, h3, h4, h5⟩, hu⟩ := GlobalTheory.T.hermitian_period_linear_algebra D.p D.q g (tyPart ty τ') (tyPart ty (ComplexEmbedding.conjugate τ')) V W (fun m => P (e m)) _ Hm hlin hHh hHp hS hVl hWl (fun n => hVs _) (fun n => hWs _) (fun m n => hs τ' _ _)
  refine ⟨⟨V, W, Fm, B, d⟩, ⟨fun a => (hVd a _).2 rfl, fun j => (hWd j _).2 rfl, h1, h2, h3, h4, h5⟩, ?_⟩
  rintro ⟨V', W', Fm', B', d'⟩ ⟨k1, k2, k3, k4, k5, k6, k7⟩
  have eV : V' = V := funext fun a => (hVd a _).1 (k1 a)
  have eW : W' = W := funext fun a => (hWd a _).1 (k2 a)
  subst eV eW
  have := hu ⟨Fm', B', d'⟩ ⟨k3, k4, k5, k6, k7⟩
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl, rfl⟩ := this
  rfl

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFrameOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_eigen_frame_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∀ (i : Fin FU.n) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (P : (FU.Di i).La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q), LinearIndependent (𝓞 E) e → IsPeriod (FU.Di i) ty P → under y = FU.u i P → IsFramed Set.univ τ σ y v w → ∃! x : (Fin D.p → Fin g → ℂ) × (Fin D.q → Fin g → ℂ) × Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ × Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ × ℂ, (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (x.1 a) (v a).left) ∧ (∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left) (x.2.1 j) (w j).left) ∧ (∀ n, tyPart ty (ComplexEmbedding.conjugate τ') (P (e n)) = ∑ j, x.2.2.2.1 j n • x.2.1 j) ∧ (∀ j n, ∑ m, x.2.2.1 j m * τ' (sesq (FU.Di i) (e m) (e n)) = x.2.2.2.1 j n) ∧ x.2.2.2.2 ≠ 0 ∧ (∃ C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ, ∀ a, tyPart ty τ' (∑ m, C a m • P (e m)) = x.1 a) ∧ ∀ C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ, (∀ a, tyPart ty τ' (∑ m, C a m • P (e m)) = x.1 a) → (Matrix.fromRows C x.2.2.1).det = x.2.2.2.2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.anSolve | exact GlobalTheory.CompanionTheory.Ar.Flat.anSolve | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.anSolve <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBundleUnderEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBundleUnderEquiv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

theorem flagStep_linearEquiv_image {Ω F F' : Type} [Field Ω] [AddCommGroup F] [Module Ω F] [AddCommGroup F']
    [Module Ω F'] (Φ : F ≃ₗ[Ω] F') {r : ℕ} (d : Fin r → F) (i : ℕ) :
    flagStep Ω (fun k => Φ (d k)) i = (flagStep Ω d i).map Φ.toLinearMap := by
  unfold flagStep
  rw [Submodule.map_span, ← Set.image_comp]
  rfl

theorem isFlagVBOn_pull_map : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (E F F' : Type)
    [AddCommGroup E] [Module Ω₀ E] [AddCommGroup F] [Module Ω F] [AddCommGroup F'] [Module Ω F']
    (L : Lat ξ E) (j : E →+ F) (Φ : F ≃ₗ[Ω] F') (T : Set (Cpt ξ')) (r : ℕ) (b : Fin r → F),
    (L.pull ξ' f j).IsFlagVBOn T b →
    (L.pull ξ' f (Φ.toLinearMap.toAddMonoidHom.comp j)).IsFlagVBOn T (fun k => Φ (b k)) := by
  intro X X' Ω₀ Ω _ _ ξ ξ' f E F F' _ _ _ _ _ _ L j Φ T r b h
  unfold Lat.IsFlagVBOn at h ⊢
  intro p hp
  obtain ⟨U, hpU, c, hc, hframe⟩ := h p hp
  refine ⟨U, hpU, fun k => Φ (c k), fun i => ?_, fun q hq hqU => ?_⟩
  · rw [flagStep_linearEquiv_image, flagStep_linearEquiv_image, hc i]
  · have hq' := hframe q hq hqU
    unfold Lat.IsFrameAt at hq' ⊢
    obtain ⟨hli, hsp⟩ := hq'
    refine ⟨hli.map' Φ.toLinearMap Φ.ker, ?_⟩
    let φ : F →ₗ[regAt ξ' q] F' := Φ.toLinearMap.restrictScalars (regAt ξ' q)
    unfold Lat.pull at hsp ⊢
    rw [show Set.range (fun k => Φ (c k)) = φ '' Set.range c from Set.range_comp φ c]
    rw [← Submodule.map_span φ, ← hsp, Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨h, e, he, rfl⟩
      exact ⟨j e, ⟨h, e, he, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨h, e, he, rfl⟩, rfl⟩
      exact ⟨h, e, he, rfl⟩

end GlobalTheory.CompanionTheory.Ar.FlagStep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBundleUnderEquivStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_under_equiv : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (E F F' : Type)
    [AddCommGroup E] [Module Ω₀ E] [AddCommGroup F] [Module Ω F] [AddCommGroup F'] [Module Ω F']
    (L : Lat ξ E) (j : E →+ F) (Φ : F ≃ₗ[Ω] F') (T : Set (Cpt ξ')) (r : ℕ) (b : Fin r → F),
    (L.pull ξ' f j).IsFlagVBOn T b →
    (L.pull ξ' f (Φ.toLinearMap.toAddMonoidHom.comp j)).IsFlagVBOn T (fun k => Φ (b k)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagStep.isFlagVBOn_pull_map | exact GlobalTheory.CompanionTheory.Ar.FlagStep.isFlagVBOn_pull_map | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagStep.isFlagVBOn_pull_map <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TensorEquivOfBasisExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TensorEquivOfBasisExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

theorem exists_tensor_equiv_of_semilinear :
    ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (V V' : Type) [AddCommGroup V]
    [Module Ω₀ V] [AddCommGroup V'] [Module Ω V'] (j : V →+ V'),
    (∀ (a : Ω₀) e, j (a • e) = algebraMap Ω₀ Ω a • j e) →
    (∀ (n : ℕ) (b : Fin n → V), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) →
    Submodule.span Ω (Set.range j) = ⊤ →
    ∃ Φ : TensorProduct Ω₀ Ω V ≃ₗ[Ω] V', ∀ e, Φ (TensorProduct.mk Ω₀ Ω V 1 e) = j e := by
  intro Ω₀ Ω _ _ _ V V' _ _ _ _ j hsemi hind hspan
  letI : Module Ω₀ V' := Module.compHom V' (algebraMap Ω₀ Ω)
  haveI : IsScalarTower Ω₀ Ω V' := ⟨fun a b x => by
    change (a • b) • x = algebraMap Ω₀ Ω a • (b • x)
    rw [Algebra.smul_def, mul_smul]⟩
  let jl : V →ₗ[Ω₀] V' :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun a e => hsemi a e }
  let L : TensorProduct Ω₀ Ω V →ₗ[Ω] V' := jl.liftBaseChange Ω
  have hL : ∀ e, L (TensorProduct.mk Ω₀ Ω V 1 e) = j e := by
    intro e
    change jl.liftBaseChange Ω (1 ⊗ₜ[Ω₀] e) = j e
    rw [LinearMap.liftBaseChange_tmul, one_smul]
    rfl
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    exact ⟨_, hL e⟩
  let B := Module.Basis.ofVectorSpace Ω₀ V
  let C := Algebra.TensorProduct.basis Ω B
  have hC : ∀ i, L (C i) = j (B i) := by
    intro i
    rw [Algebra.TensorProduct.basis_apply]
    exact hL (B i)
  have hli : LinearIndependent Ω (fun i => j (B i)) := by
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    let e := s.equivFin
    have h1 : LinearIndependent Ω₀ (fun k : Fin s.card => B (e.symm k).1) :=
      B.linearIndependent.comp _ (Subtype.val_injective.comp e.symm.injective)
    have h2 := (hind _ _ h1).comp e e.injective
    convert h2 using 1
    funext i
    simp
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : Finsupp.linearCombination Ω (fun i => j (B i)) (C.repr x) = 0 := by
      rw [← hx]
      conv_rhs => rw [← C.linearCombination_repr x]
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum]
      simp [hC]
    have h1 : C.repr x = 0 := hli (h0.trans (map_zero _).symm)
    simpa using h1
  exact ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun e => hL e⟩

end GlobalTheory.CompanionTheory.Ar.FlagStep
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TensorEquivOfBasisExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_equiv_of_basis_extension : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (V V' : Type) [AddCommGroup V]
    [Module Ω₀ V] [AddCommGroup V'] [Module Ω V'] (j : V →+ V'),
    (∀ (a : Ω₀) e, j (a • e) = algebraMap Ω₀ Ω a • j e) →
    (∀ (n : ℕ) (b : Fin n → V), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) →
    Submodule.span Ω (Set.range j) = ⊤ →
    ∃ Φ : TensorProduct Ω₀ Ω V ≃ₗ[Ω] V', ∀ e, Φ (TensorProduct.mk Ω₀ Ω V 1 e) = j e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagStep.exists_tensor_equiv_of_semilinear | exact GlobalTheory.CompanionTheory.Ar.FlagStep.exists_tensor_equiv_of_semilinear | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagStep.exists_tensor_equiv_of_semilinear <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockExtensionArithVar
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddedResolutionAmpleMetric
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddedResolutionAmpleMetric
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem exists_smooth_hermLine_posPot_of_isEmbedded : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e), IsEmbedded R.A P R.U R.lift → ∃ Amp : HermLine ι, IsSmoothHerm Amp ∧ IsPotential R.A (potOf R Amp) ∧ IsPosPot R.A (potOf R Amp) :=
  @PositivityTheory.UnitarySelfGeneration.g_pos

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddedResolutionAmpleMetricStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedded_resolution_ample_metric : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e), IsEmbedded R.A P R.U R.lift → ∃ Amp : HermLine ι, IsSmoothHerm Amp ∧ IsPotential R.A (potOf R Amp) ∧ IsPosPot R.A (potOf R Amp) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.exists_smooth_hermLine_posPot_of_isEmbedded | exact GlobalTheory.CompanionTheory.Ar.Cmp.exists_smooth_hermLine_posPot_of_isEmbedded | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.exists_smooth_hermLine_posPot_of_isEmbedded <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockExtensionArithVar
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp.Good

theorem coord_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (p : Σ k, ι k) (h : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply h
  unfold mCoordIdeal
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem join_blocks {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) {M : ℕ} (y₂ : (Σ _ : Unit, Fin M) → Ω) (hy : IsRelevant (mCoordIdeal y))
    (h₂ : ∃ i, y₂ ⟨(), i⟩ ≠ 0) : ∀ k, ∃ i, joinVec y y₂ ⟨k, i⟩ ≠ 0 := by
  rintro (k | u)
  · obtain ⟨i, hi⟩ := hy k
    exact ⟨i, coord_ne_zero y ⟨k, i⟩ hi⟩
  · obtain ⟨i, hi⟩ := h₂
    exact ⟨i, hi⟩

theorem exists_good_model : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomog β b → β ∉ mCoordIdeal y → ∃ (K' : Type) (_ : Fintype K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (y' : (Σ k, ι' k) → Ω) (J : Ideal (MRing ι')) (R : AnLogRes (mCoordIdeal y') J e) (Amp : HermLine ι'), IsBlockMap κ v ∧ y' ∘ v = y ∧ blockFnField y' = blockFnField y ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y') (e + 1) ∧ IsEmbedded R.A (mCoordIdeal y') R.U R.lift ∧ IsSmoothHerm Amp ∧ IsPotential R.A (potOf R Amp) ∧ IsPosPot R.A (potOf R Amp) ∧ ∀ z ∈ mcPts (mCoordIdeal y'), evC z (rename v β) = 0 → z ∈ mcPts J := by
  intro hRes K _ ι _ Ω _ _ y e β b hV hβ hβP
  obtain ⟨M, y₂, J, ⟨i₀, hi₀⟩, hfield, hJh, hJ, hsnc, hz⟩ :=
    GlobalTheory.T.adjoin_coords_arith_var hRes K ι Ω y e β b hV hβ hβP
  have hj := (GlobalTheory.T.block_join_inclusions_compat).1 K ι Unit (fun _ => Fin M) Ω y y₂
  have hb₁ := hj.1
  have hcomp : joinVec y y₂ ∘ joinInl ι (fun _ : Unit => Fin M) = y := hj.2.2.1
  have hblocks := join_blocks y y₂ hV.2.1.2.2 ⟨i₀, hi₀⟩
  have harith : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal (joinVec y y₂)) (e + 1) := by
    refine GlobalTheory.T.isArithVar_of_block_algebraic K ι (K ⊕ Unit) (joinIdx ι fun _ : Unit => Fin M) Sum.inl
      (joinInl ι fun _ : Unit => Fin M) Ω (joinVec y y₂) (e + 1) hb₁ hblocks ?_ ?_
    · rw [hcomp]; exact hV
    · rw [hcomp, hfield]
      intro t ht
      exact isAlgebraic_algebraMap (⟨t, ht⟩ : blockFnField y)
  obtain ⟨R, hR⟩ := GlobalTheory.T.snc_model_embedded_log_resolution (K ⊕ Unit) (joinIdx ι fun _ : Unit => Fin M) Ω (joinVec y y₂) e J
    harith hJh hJ hsnc
  obtain ⟨Amp, h₁, h₂, h₃⟩ := GlobalTheory.T.embedded_resolution_ample_metric (K ⊕ Unit) (joinIdx ι fun _ : Unit => Fin M)
    (mCoordIdeal (joinVec y y₂)) J e R hR
  exact ⟨K ⊕ Unit, inferInstance, joinIdx ι fun _ : Unit => Fin M, inferInstance, Sum.inl,
    joinInl ι fun _ : Unit => Fin M, joinVec y y₂, J, R, Amp, hb₁, hcomp, hfield, harith, hR, h₁, h₂, h₃, hz⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.Good
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockExtensionArithVarStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_extension_arith_var : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomog β b → β ∉ mCoordIdeal y → ∃ (K' : Type) (_ : Fintype K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (y' : (Σ k, ι' k) → Ω) (J : Ideal (MRing ι')) (R : AnLogRes (mCoordIdeal y') J e) (Amp : HermLine ι'), IsBlockMap κ v ∧ y' ∘ v = y ∧ blockFnField y' = blockFnField y ∧ IsArithVar (mCoordIdeal y') (e + 1) ∧ IsEmbedded R.A (mCoordIdeal y') R.U R.lift ∧ IsSmoothHerm Amp ∧ IsPotential R.A (potOf R Amp) ∧ IsPosPot R.A (potOf R Amp) ∧ ∀ z ∈ mcPts (mCoordIdeal y'), evC z (rename v β) = 0 → z ∈ mcPts J := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.Good.exists_good_model | exact GlobalTheory.CompanionTheory.Ar.Cmp.Good.exists_good_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.Good.exists_good_model <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonLeft
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonLeft
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.CoverLie

section Move

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem tan_up {G : Over S} [GrpObj G] (φ : R →+* R') (x : Sp R ⟶ S) (x' : Sp R' ⟶ S)
    (h : Spec.map (CommRingCat.ofHom φ) ≫ x = x') (v : epsAt x ⟶ G) (hv : IsTanAt G x v) :
    IsTanAt G x' (LieCarrier.epsHom φ x x' h ≫ v) := by
  let u : Over.mk x' ⟶ Over.mk x := Over.homMk (Spec.map (CommRingCat.ofHom φ)) h
  have e : (LieEx.zsec x' : _ ⟶ LieEx.ob x' R') ≫ LieCarrier.epsHom φ x x' h = u ≫ LieEx.zsec x := by
    apply Over.OverMorphism.ext
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun a => ?_
    simp [dualMap]
  refine (LieEx.isTanAt_iff x' G _).2 ?_
  rw [← Category.assoc, e, Category.assoc, (LieEx.isTanAt_iff x G _).1 hv, MonObj.comp_one]

variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {f : X' ⟶ X}
  {i : Ω →+* Ω'} {G : Over X} {G' : Over X'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
  {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']

theorem exists_hom (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) (hG : IsGrpPullback G' G f φ) (M : LieModel G ξ V)
    (M' : LieModel G' ξ' V') :
    ∃ j : V →+ V', ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left := by
  have hx : Spec.map (CommRingCat.ofHom i) ≫ ξ = ξ' ≫ f := hd.symm
  let P := LieMove.pushModel hG M'
  have ex : ∀ e, ∃ e', P.pt e' = LieCarrier.epsHom i ξ (ξ' ≫ f) hx ≫ M.pt e :=
    fun e => P.onto _ (tan_up i ξ (ξ' ≫ f) hx _ (M.tan e))
  choose j hj using ex
  refine ⟨AddMonoidHom.mk' j fun a b => P.inj ?_, fun e => congrArg (fun z => z.left) (hj e)⟩
  rw [P.add, hj, hj, hj, M.add, MonObj.comp_mul]

theorem map_diff {M : LieModel G ξ V} {M' : LieModel G' ξ' V'} {a : G ⟶ G} {a' : G' ⟶ G'}
    (hG : IsGrpPullback G' G f φ) (hφ : a'.left ≫ φ = φ ≫ a.left) {j : V →+ V'}
    (hj : ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left)
    {T : V →ₗ[Ω] V} {T' : V' →ₗ[Ω'] V'} (hT : M.IsDiffOf a T) (hT' : M'.IsDiffOf a' T') (e : V) :
    j (T e) = T' (j e) := by
  refine M'.inj (Over.OverMorphism.ext (hG.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)))
  rw [hj, hT e, hT' (j e), Over.comp_left, Over.comp_left, Category.assoc, hφ, ← Category.assoc, ← Category.assoc, hj]

end Move

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {f' : S'' ⟶ S} (hf : f' = g ≫ f) (m : SABMap t' t f) (n : SABMap t'' t f') :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst hf
  exact sabCancel pullCubCancel E H S S' S'' t t' t'' f g m n

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X), GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → ∃ jA : A.Li →+ B.Li, IsExtOver i jA ∧ (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) ∧ (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) ∧ B.M.lat = A.M.lat.pull B.ξ h jA := by
  intro E _ _ _ H D l Xo c Y S₀ S Ω₁ Ω _ _ K₁ _ J₁ _ y₁ K _ J _ y A B i h hd hf
  obtain ⟨m, hm⟩ := cancel hf A.m B.m
  obtain ⟨j, hj⟩ := exists_hom hd m.cart A.M B.M
  obtain ⟨hx, -, hl⟩ := GlobalTheory.T.lie_lattice_dominant_compat A.X B.X Ω₁ Ω A.ξ B.ξ h i A.t.G B.t.G m.φ A.Li B.Li A.M B.M j A.tie.gen B.tie.gen
    hd m.cart A.t.semi.smooth hj
  refine ⟨j, hx, fun e => ?_, fun a e => ?_, hl⟩
  · rw [hm, ← Category.assoc, hj, Category.assoc]
  · exact map_diff m.cart (m.act a) hj (A.act a) (B.act a) e

end GlobalTheory.CompanionTheory.Ar.CoverLie
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonLeftStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_comparison_left : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X), GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → ∃ jA : A.Li →+ B.Li, IsExtOver i jA ∧ (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) ∧ (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) ∧ B.M.lat = A.M.lat.pull B.ξ h jA := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoverLie.main | exact GlobalTheory.CompanionTheory.Ar.CoverLie.main | (intros; apply GlobalTheory.CompanionTheory.Ar.CoverLie.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPointsTransferDominating
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPointsTransferDominating
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PatchIso

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem unitAt_congr {X' : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
    {p : Cpt ξ} {p' : Cpt ξ'} (h : regAt ξ' p' = regAt ξ p) (a : Ω) : unitAt ξ' p' a ↔ unitAt ξ p a := by
  unfold unitAt
  rw [h]

theorem char_zero_congr {X' : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
    {p : Cpt ξ} {p' : Cpt ξ'} (h : regAt ξ' p' = regAt ξ p) (hp : Char0 ξ p) : Char0 ξ' p' := fun r hr hf =>
  hp r hr fun hu => hf ((unitAt_congr h _).2 hu)

theorem mem_genFib_of_char0 [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ} (hp : Char0 ξ p) :
    p ∈ genFib ξ := by
  have key : ∀ n : ℕ, 0 < n → ((n : Ω))⁻¹ ∈ regAt ξ p := by
    intro n
    induction n using induction_on_primes with
    | zero => exact fun h => absurd h (lt_irrefl 0)
    | one => intro _; simpa using (regAt ξ p).one_mem
    | prime_mul r a hr ih =>
      intro h
      have ha : 0 < a := Nat.pos_of_mul_pos_left h
      have hu : unitAt ξ p (r : Ω) := not_not.1 (hp r hr)
      rw [Nat.cast_mul, mul_inv]
      exact mul_mem hu.2.2 (ih ha)
  exact fun n hn => ⟨Nat.cast_ne_zero.2 hn.ne', natCast_mem _ n, key n hn⟩

theorem exists_below [CharZero Ω] {X₁ X₂ : Scheme.{0}} {ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁}
    {ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂} {g : X₂ ⟶ X₁} (hg : IsCptGen ξ₂)
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω))
    (hi : ∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) (p : Cpt ξ₂) (hp : Char0 ξ₂ p) :
    ∃ p₁ : Cpt ξ₁, p₁.1 = g p.1 ∧ Char0 ξ₁ p₁ ∧ regAt ξ₂ p = regAt ξ₁ p₁ := by
  obtain ⟨h, -, hu⟩ := RegAtDom.regAt_dominates X₁ Ω ξ₁ X₂ Ω ξ₂ g (RingHom.id Ω) hd p
  have c : Char0 ξ₁ ⟨g p.1, h⟩ := fun r hr hf =>
    hf (hu hg (r : Ω) (natCast_mem _ r) (not_not.1 (hp r hr)))
  refine ⟨⟨g p.1, h⟩, rfl, c, ?_⟩
  rw [(hi _ (mem_genFib_of_char0 c)).regAt_eq p rfl, Subring.map_id]

theorem exists_above [CharZero Ω] {X₁ X₂ : Scheme.{0}} {ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁}
    {ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂} {g : X₂ ⟶ X₁}
    (hi : ∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) (p₁ : Cpt ξ₁) (hp : Char0 ξ₁ p₁) :
    ∃ p : Cpt ξ₂, g p.1 = p₁.1 ∧ Char0 ξ₂ p ∧ regAt ξ₂ p = regAt ξ₁ p₁ := by
  have I := hi p₁ (mem_genFib_of_char0 hp)
  obtain ⟨p, hp', -⟩ := I.existsUnique
  have e : regAt ξ₂ p = regAt ξ₁ p₁ := by rw [I.regAt_eq p hp', Subring.map_id]
  exact ⟨p, hp', char_zero_congr e hp, e⟩

theorem sncPts_of_isoAt :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ₁ κ₂ : Type) (x₁ : κ₁ → Ω) (x₂ : κ₂ → Ω) (X₁ X₂ : Scheme.{0}) (ξ₁ : Sp Ω ⟶ X₁) (ξ₂ : Sp Ω ⟶ X₂) (g : X₂ ⟶ X₁) (e : ℕ) (Ab : Set X₁), (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ x₁ → CoordTie ℤ ξ₂ x₂ → GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω) → (∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) → SncPts ξ₁ e {p | Char0 ξ₁ p ∧ p.1 ∉ Ab} → SncPts ξ₂ e {p | Char0 ξ₂ p ∧ g p.1 ∉ Ab} := by
  intro Ω _ _ κ₁ κ₂ x₁ x₂ X₁ X₂ ξ₁ ξ₂ g e Ab _ _ _ t₂ hd hi hs p hp
  have ePts : Pts ξ₂ = Pts ξ₁ := by
    ext R
    constructor
    · rintro ⟨p₂, c, rfl⟩
      obtain ⟨p₁, -, c₁, r⟩ := exists_below t₂.gen hd hi p₂ c
      exact ⟨p₁, c₁, r⟩
    · rintro ⟨p₁, c, rfl⟩
      obtain ⟨p₂, -, c₂, r⟩ := exists_above hi p₁ c
      exact ⟨p₂, c₂, r.symm⟩
  have eB : regAt ξ₂ '' {p | Char0 ξ₂ p ∧ g p.1 ∉ Ab} = regAt ξ₁ '' {p | Char0 ξ₁ p ∧ p.1 ∉ Ab} := by
    ext R
    constructor
    · rintro ⟨p₂, ⟨c, ha⟩, rfl⟩
      obtain ⟨p₁, e₁, c₁, r⟩ := exists_below t₂.gen hd hi p₂ c
      exact ⟨p₁, ⟨c₁, e₁ ▸ ha⟩, r.symm⟩
    · rintro ⟨p₁, ⟨c, ha⟩, rfl⟩
      obtain ⟨p₂, e₂, c₂, r⟩ := exists_above hi p₁ c
      exact ⟨p₂, ⟨c₂, by rwa [e₂]⟩, r⟩
  obtain ⟨p₁, -, c₁, r⟩ := exists_below t₂.gen hd hi p hp
  obtain ⟨A, z, n, q, hP, hq, hl⟩ := hs p₁ c₁
  refine ⟨A, z, n, q, ?_, hq, ?_⟩
  · rw [ePts, eB]
    exact hP
  · rw [r]
    exact hl

end GlobalTheory.CompanionTheory.Ar.PatchIso
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPointsTransferDominatingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_points_transfer_dominating : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ₁ κ₂ : Type) (x₁ : κ₁ → Ω) (x₂ : κ₂ → Ω) (X₁ X₂ : Scheme.{0}) (ξ₁ : Sp Ω ⟶ X₁) (ξ₂ : Sp Ω ⟶ X₂) (g : X₂ ⟶ X₁) (e : ℕ) (Ab : Set X₁), (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ x₁ → CoordTie ℤ ξ₂ x₂ → GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω) → (∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) → SncPts ξ₁ e {p | Char0 ξ₁ p ∧ p.1 ∉ Ab} → SncPts ξ₂ e {p | Char0 ξ₂ p ∧ g p.1 ∉ Ab} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PatchIso.sncPts_of_isoAt | exact GlobalTheory.CompanionTheory.Ar.PatchIso.sncPts_of_isoAt | (intros; apply GlobalTheory.CompanionTheory.Ar.PatchIso.sncPts_of_isoAt <;> assumption)
end
end

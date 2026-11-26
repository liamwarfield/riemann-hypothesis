module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeHermitianFormExists
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LeWchartOne
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionArchimedeanFrame

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixChangeFrame
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixChangeFrame
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem gramAt_unique_of_polarisedAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐.Li) (Γ Γ' : Matrix (Fin r) (Fin r) ℂ), HodgeMetric.PolarisedAt 𝔐.t z → 𝔐.M.GramAt 𝔐.t.PP.L z b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z b Γ' → Γ = Γ' := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 z r b Γ Γ' hP h1 h2
  obtain ⟨v, hv, hΓ⟩ := h1
  obtain ⟨v', hv', hΓ'⟩ := h2
  have hgen : GlobalTheory.CompanionTheory.Ar.IsCptGen 𝔐.ξ := 𝔐.tie.gen
  have hvv : v = v' := funext fun i => GlobalTheory.CompanionTheory.Ar.LieModel.ValAt.unique hgen (hv i) (hv' i)
  subst hvv
  obtain ⟨V, _, _, ⟨M'⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists 𝔐.X 𝔐.t.G ℂ z
  obtain ⟨h, hh, -⟩ := GlobalTheory.T.hodge_hermitian_form_exists E H 𝔐.X 𝔐.t z V M' hP
  have hpre : ∀ i, ∃ e, M'.pt e = v i := by
    intro i
    have hT : GlobalTheory.CompanionTheory.Ar.IsTanAt 𝔐.t.G z (v i) := by
      obtain ⟨-, hT, -⟩ := hΓ i i
      exact hT
    exact M'.onto (v i) hT
  ext p q
  obtain ⟨e, he⟩ := hpre p
  obtain ⟨f, hf⟩ := hpre q
  have k1 := (hh e f (Γ p q)).1 (by rw [he, hf]; exact hΓ p q)
  have k2 := (hh e f (Γ' p q)).1 (by rw [he, hf]; exact hΓ' p q)
  rw [k1, k2]

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixChangeFrameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_matrix_change_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐.Li) (Γ Γ' : Matrix (Fin r) (Fin r) ℂ), HodgeMetric.PolarisedAt 𝔐.t z → 𝔐.M.GramAt 𝔐.t.PP.L z b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z b Γ' → Γ = Γ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_unique_of_polarisedAt | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_unique_of_polarisedAt | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_unique_of_polarisedAt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixTwoFrames
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixTwoFrames
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem valAt_sum_smul {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Type} [AddCommGroup L] [Module Ω L] (M : LieModel G ξ L)
    {z : Spec (CommRingCat.of ℂ) ⟶ X} {V : Type} [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z V)
    (hz : genPt ξ ⤳ centre z) {I : Type} (s : Finset I) (b : I → L) (x : I → V)
    (hx : ∀ p, M.ValAt z (b p) (Mz.pt (x p))) (a : I → Ω) (c : I → ℂ) (hc : ∀ p, ValAt ξ z (a p) (c p)) :
    M.ValAt z (∑ p ∈ s, a p • b p) (Mz.pt (∑ p ∈ s, c p • x p)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa [Mz.pt_zero] using M.valAt_zero hz
  | insert p s hp ih =>
    rw [Finset.sum_insert hp, Finset.sum_insert hp, Mz.add]
    refine LieModel.ValAt.add ?_ ih
    obtain ⟨h1, g, hg, hg'⟩ := hc p
    have := (hx p).smul h1 g
    rw [hg, hg', ← Mz.pt_smul] at this
    exact this

theorem gramAt_change (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω]
    [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b b' : Fin r → 𝔐.Li)
    (Γ Γ' : Matrix (Fin r) (Fin r) ℂ) (T : Matrix (Fin r) (Fin r) Ω) (Tz : Matrix (Fin r) (Fin r) ℂ)
    (hP : HodgeMetric.PolarisedAt 𝔐.t z) (hG : 𝔐.M.GramAt 𝔐.t.PP.L z b Γ) (hG' : 𝔐.M.GramAt 𝔐.t.PP.L z b' Γ')
    (hb : ∀ q, b' q = ∑ p, T p q • b p) (hT : ∀ p q, ValAt 𝔐.ξ z (T p q) (Tz p q)) :
    Γ' = Tz.conjTranspose * Γ * Tz := by
  obtain ⟨V, _, _, ⟨Mz⟩⟩ := lieModel_exists 𝔐.X 𝔐.t.G ℂ z
  obtain ⟨h, hh, -, -⟩ := GlobalTheory.T.hodge_hermitian_form_exists E H 𝔐.X 𝔐.t z V Mz hP
  obtain ⟨v, hv, hΓ⟩ := hG
  obtain ⟨v', hv', hΓ'⟩ := hG'
  choose x hx using fun p => Mz.onto (v p) (hv p).isTanAt
  have hz : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have key : ∀ q, Mz.pt (∑ p, Tz p q • x p) = v' q := fun q => by
    have h1 := valAt_sum_smul 𝔐.M Mz hz Finset.univ b x (fun p => by rw [hx]; exact hv p)
      (fun p => T p q) (fun p => Tz p q) (fun p => hT p q)
    rw [← hb q] at h1
    exact h1.unique 𝔐.tie.gen (hv' q)
  have e1 : ∀ p q, Γ p q = h (x p) (x q) := fun p q =>
    (hh _ _ _).1 (by rw [hx, hx]; exact hΓ p q)
  have e2 : ∀ p q, Γ' p q = h (∑ i, Tz i p • x i) (∑ j, Tz j q • x j) := fun p q =>
    (hh _ _ _).1 (by rw [key, key]; exact hΓ' p q)
  ext p q
  rw [e2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, e1, map_sum, LinearMap.sum_apply, map_smul,
    map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, RCLike.star_def,
    RingHom.id_apply]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixTwoFramesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_matrix_two_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b b' : Fin r → 𝔐.Li) (Γ Γ' : Matrix (Fin r) (Fin r) ℂ) (T : Matrix (Fin r) (Fin r) Ω) (Tz : Matrix (Fin r) (Fin r) ℂ), HodgeMetric.PolarisedAt 𝔐.t z → 𝔐.M.GramAt 𝔐.t.PP.L z b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z b' Γ' → (∀ q, b' q = ∑ p, T p q • b p) → (∀ p q, ValAt 𝔐.ξ z (T p q) (Tz p q)) → Γ' = Tz.conjTranspose * Γ * Tz := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_change | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_change | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_change <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairSumFrameAtPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairSumFrameAtPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramEx

theorem not_inFibre_centre {Ω : Type} [Field Ω] [CharZero Ω] {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {z : Spec (CommRingCat.of ℂ) ⟶ X} (hz : genPt ξ ⤳ centre z) {p : ℕ} (hp : p.Prime) :
    ¬ InFibre ξ p ⟨centre z, hz⟩ := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hs : (Scheme.stalkClosedPointTo z).hom (p : X.presheaf.stalk (centre z)) ≠ 0 := fun h0 =>
    hp0 ((map_natCast (Scheme.stalkClosedPointTo z).hom p).symm.trans h0)
  obtain ⟨u, hu⟩ := CxVal.isUnit _ hs
  have hg : genMap ξ ⟨centre z, hz⟩ (p : X.presheaf.stalk (centre z)) = (p : Ω) := map_natCast _ _
  intro h
  refine h ⟨Nat.cast_ne_zero.2 hp.ne_zero, ⟨_, hg⟩, ⟨((u⁻¹ : (X.presheaf.stalk (centre z))ˣ) : X.presheaf.stalk (centre z)), ?_⟩⟩
  have h1 : genMap ξ ⟨centre z, hz⟩ (u : X.presheaf.stalk (centre z)) = (p : Ω) := by rw [hu, hg]
  have h2 : genMap ξ ⟨centre z, hz⟩ ((u⁻¹ : (X.presheaf.stalk (centre z))ˣ) : X.presheaf.stalk (centre z)) *
      genMap ξ ⟨centre z, hz⟩ (u : X.presheaf.stalk (centre z)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [h1] at h2
  exact eq_inv_of_mul_eq_one_left h2

theorem posDef_of_dual {V : Type} [AddCommGroup V] [Module ℂ V] (h : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hh : ∀ v w, h w v = starRingEnd ℂ (h v w)) (hp : ∀ v, v ≠ 0 → 0 < (h v v).re) {N : ℕ} (x : Fin N → V)
    (g : Fin N → V →ₗ[ℂ] ℂ) (hg : ∀ j k, g j (x k) = if j = k then 1 else 0) :
    (Matrix.of fun p q => h (x p) (x q)).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨Matrix.IsHermitian.ext fun p q => ?_, fun c hc => ?_⟩
  · simp only [Matrix.of_apply]
    rw [hh (x p) (x q)]
    simp
  · set u : V := ∑ k, c k • x k with hu
    have e : star c ⬝ᵥ (Matrix.of fun p q => h (x p) (x q)).mulVec c = h u u := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hu, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, dotProduct, Matrix.mulVec,
        Matrix.of_apply, Finset.mul_sum, Pi.star_apply, smul_eq_mul, RingHom.id_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [RCLike.star_def]
      ring
    have hu0 : u ≠ 0 := fun h0 => hc (funext fun j => by
      have := congrArg (g j) h0
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [hu, map_sum, hg, Finset.sum_ite_eq] using this)
    rw [e, Complex.pos_iff]
    refine ⟨hp u hu0, ?_⟩
    have := (Complex.conj_eq_iff_im.1 (hh u u).symm)
    exact this.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem exists_dual_sum (𝔐 : HodgeCpt Y S y) (hind : iSupIndep 𝔐.Vgen) (q : Cpt 𝔐.ξ)
    (hV : ∀ s, 𝔐.V s q = 𝔐.dR s q) (hlat : 𝔐.M.lat q = ⨆ s, 𝔐.dR s q) (a b : CMType H ⊕ CMType H) {N : ℕ}
    (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b))
    (hfr : (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb q) :
    ∃ π : Fin N → Module.Dual Ω 𝔐.Li,
      (∀ j k, π j ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) = if j = k then 1 else 0) ∧
      ∀ j, ∀ e ∈ 𝔐.M.lat q, π j e ∈ regAt 𝔐.ξ q := by
  classical
  obtain ⟨hli, hspan⟩ := hfr
  have hdis : Disjoint (𝔐.Vgen a ⊔ 𝔐.Vgen b) (⨆ s ∈ ({a, b} : Set (CMType H ⊕ CMType H))ᶜ, 𝔐.Vgen s) :=
    (hind.disjoint_biSup_biSup (s := {a, b}) (t := {a, b}ᶜ) disjoint_compl_right).mono_left
      (sup_le (le_biSup 𝔐.Vgen (by simp)) (le_biSup 𝔐.Vgen (by simp)))
  obtain ⟨C, hC, hc⟩ := hdis.symm.exists_isCompl
  let pr : 𝔐.Li →ₗ[Ω] ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b) := Submodule.projectionOnto _ _ hc.symm
  have hker : LinearMap.ker (Fintype.linearCombination Ω bb) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun m hm => funext fun k => ?_
    exact Fintype.linearIndependent_iff.1 hli m (by rwa [Fintype.linearCombination_apply] at hm) k
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  have hgb : ∀ l, g (bb l) = Pi.single l 1 := fun l => by
    have := LinearMap.congr_fun hg (Pi.single l 1)
    simpa [Fintype.linearCombination_apply_single] using this
  have hpr : ∀ w : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b), pr (w : 𝔐.Li) = w := fun w =>
    Submodule.projectionOnto_apply_left hc.symm w
  refine ⟨fun j => (LinearMap.proj j).comp (g.comp pr), fun j k => ?_, fun j e he => ?_⟩
  · simp only [LinearMap.comp_apply, hpr, hgb, LinearMap.proj_apply]
    simp [Pi.single_apply]
  · rw [hlat] at he
    induction he using Submodule.iSup_induction' with
    | mem s' x hx =>
      by_cases hs : s' ∈ ({a, b} : Set (CMType H ⊕ CMType H))
      · have hxW : x ∈ 𝔐.Vgen a ⊔ 𝔐.Vgen b := by
          rcases hs with rfl | rfl
          · exact Submodule.mem_sup_left hx.2
          · exact Submodule.mem_sup_right hx.2
        have hxV : x ∈ 𝔐.V a q ⊔ 𝔐.V b q := by
          rcases hs with rfl | rfl
          · rw [hV s']; exact Submodule.mem_sup_left hx
          · rw [hV s']; exact Submodule.mem_sup_right hx
        have hm : (⟨x, hxW⟩ : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) ∈
            (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype) q := hxV
        rw [hspan] at hm
        obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hm
        have e1 : ∀ k, (c' k • bb k) = ((c' k : regAt 𝔐.ξ q) : Ω) • bb k := fun _ => rfl
        have e2 : pr x = ∑ k, ((c' k : regAt 𝔐.ξ q) : Ω) • bb k := by
          rw [show x = ((⟨x, hxW⟩ : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) from rfl, hpr, ← hc']
          exact Finset.sum_congr rfl fun k _ => e1 k
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [LinearMap.comp_apply, e2, map_sum, map_smul, hgb, LinearMap.proj_apply]
        simp only [Pi.smul_apply, smul_eq_mul]
        refine sum_mem fun k _ => mul_mem (c' k).2 ?_
        rw [Pi.single_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      · have hxC : x ∈ C := hC (Submodule.mem_iSup_of_mem s' (Submodule.mem_iSup_of_mem hs hx.2))
        have : pr x = 0 := Submodule.projectionOnto_apply_of_mem_right hc.symm hxC
        simp [this]
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy

theorem exists_gramAt_posDef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (h : genPt 𝔐.ξ ⤳ centre z), HodgeMetric.PolarisedAt 𝔐.t z → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre z, h⟩ → ∃ Γ : Matrix (Fin N) (Fin N) ℂ, 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) Γ ∧ Γ.PosDef := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 a b N bb z hgen hpol hfr
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := NumberField.RingOfIntegers.coe_injective
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  obtain ⟨-, -, -, -, -, -, hind, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ
  obtain ⟨hV, -, hlat⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ ⟨centre z, hgen⟩
    fun r hr => not_inFibre_centre hgen hr
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists 𝔐.X 𝔐.t.G ℂ z
  obtain ⟨f, hHI, hh, hp⟩ := GlobalTheory.T.hodge_hermitian_form_exists E H 𝔐.X 𝔐.t z Vz MR hpol
  obtain ⟨π, hπ, hreg⟩ := exists_dual_sum 𝔐 hind ⟨centre z, hgen⟩ hV hlat a b bb hfr
  have hbL : ∀ k, ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) ∈ 𝔐.M.lat ⟨centre z, hgen⟩ := fun k => by
    have hm : bb k ∈ (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype) ⟨centre z, hgen⟩ := by
      rw [hfr.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    have hm' : ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) ∈ 𝔐.V a ⟨centre z, hgen⟩ ⊔ 𝔐.V b ⟨centre z, hgen⟩ := hm
    rw [hV, hV] at hm'
    refine (sup_le ?_ ?_ : 𝔐.dR a ⟨centre z, hgen⟩ ⊔ 𝔐.dR b ⟨centre z, hgen⟩ ≤ 𝔐.M.lat ⟨centre z, hgen⟩) hm'
    · exact fun x hx => hx.1
    · exact fun x hx => hx.1
  have hval : ∀ k, ∃ x : Vz, 𝔐.M.ValAt z ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) (MR.pt x) := fun k => by
    obtain ⟨w, hw⟩ := (𝔐.M.exists_valAt_iff z _).2 ⟨hgen, hbL k⟩
    obtain ⟨x, rfl⟩ := MR.onto w hw.isTanAt
    exact ⟨x, hw⟩
  choose x hx using hval
  have hg : ∀ j, ∃ g : Vz →ₗ[ℂ] ℂ, ∀ k, g (x k) = if j = k then 1 else 0 := fun j => by
    obtain ⟨g, hg⟩ := GlobalTheory.T.lattice_regular_at_local_point 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M ℂ z hgen Vz MR (π j) hξ (hreg j)
    refine ⟨g, fun k => hg _ _ _ (hx k) ?_⟩
    rw [hπ j k]
    split_ifs
    · exact CxVal.one hgen
    · exact ⟨hgen, 0, map_zero _, map_zero _⟩
  choose g hg using hg
  exact ⟨Matrix.of fun p q => f (x p) (x q), ⟨fun k => MR.pt (x k), hx, fun p q => (hHI _ _ _).2 rfl⟩,
    posDef_of_dual f hh hp x g hg⟩

end GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramEx
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairSumFrameAtPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_sum_frame_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (h : genPt 𝔐.ξ ⤳ centre z), HodgeMetric.PolarisedAt 𝔐.t z → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre z, h⟩ → ∃ Γ : Matrix (Fin N) (Fin N) ℂ, 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) Γ ∧ Γ.PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramEx.exists_gramAt_posDef | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramEx.exists_gramAt_posDef | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramEx.exists_gramAt_posDef <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalHermitianFibre
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalHermitianFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeFibre

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexAt NumberField.ComplexEmbedding

section Linear

variable {F W : Type*} [AddCommGroup F] [Module ℂ F] [AddCommGroup W] [Module ℂ W]

@[reducible] def coreOfForm (e : F ≃ₗ[ℂ] W) (h : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hh : ∀ v w, h w v = starRingEnd ℂ (h v w)) (hp : ∀ v, v ≠ 0 → 0 < (h v v).re) :
    InnerProductSpace.Core ℂ F where
  inner a b := h (e a) (e b)
  conj_inner_symm a b := by
    simpa using (hh (e b) (e a)).symm
  re_inner_nonneg a := by
    by_cases ha : e a = 0
    · simp [ha]
    · exact (hp _ ha).le
  add_left a b c := by simp
  smul_left a b r := by simp
  definite a h0 := by
    by_contra ha
    have := hp (e a) (fun h1 => ha (by simpa using h1))
    rw [h0] at this
    simp at this

variable {L : Type} [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module (𝓞 L) V]

theorem exists_metric [Module.Finite (𝓞 L) V] [Module.Projective (𝓞 L) V]
    (W : (L →+* ℂ) → Type) [∀ σ, AddCommGroup (W σ)] [∀ σ, Module ℂ (W σ)]
    (e : ∀ σ, Fibre σ V ≃ₗ[ℂ] W σ) (h : ∀ σ, W σ →ₗ⋆[ℂ] W σ →ₗ[ℂ] ℂ)
    (hh : ∀ σ v w, h σ w v = starRingEnd ℂ (h σ v w)) (hp : ∀ σ v, v ≠ 0 → 0 < (h σ v v).re)
    (hc : ∀ σ (x y : V), h (conjugate σ) (e _ ((1 : ComplexAt (conjugate σ)) ⊗ₜ x)) (e _ ((1 : ComplexAt (conjugate σ)) ⊗ₜ y)) =
      starRingEnd ℂ (h σ (e σ ((1 : ComplexAt σ) ⊗ₜ x)) (e σ ((1 : ComplexAt σ) ⊗ₜ y)))) :
    ∃ m : HermitianMetric L V, ∀ σ (x y : V), (m.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] y) =
      h σ (e σ ((1 : ComplexAt σ) ⊗ₜ x)) (e σ ((1 : ComplexAt σ) ⊗ₜ y)) := by
  have tm : ∀ (σ : L →+* ℂ) (z : ComplexAt σ) (x : V), (z ⊗ₜ[𝓞 L] x : Fibre σ V) =
      ((ofComplex σ).symm z : ℂ) • ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) := fun σ z x => by
    rw [TensorProduct.smul_tmul', ComplexAt.complex_smul_def]
    simp
  have cm : ∀ (σ : L →+* ℂ) (x : V), conjMap σ V ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) =
      (1 : ComplexAt (conjugate σ)) ⊗ₜ[𝓞 L] x := fun σ x => by
    rw [conjMap_tmul, map_one]
  refine ⟨⟨fun σ => coreOfForm (e σ) (h σ) (hh σ) (hp σ), fun σ x y => ?_⟩, fun σ x y => rfl⟩
  change h _ (e _ _) (e _ _) = starRingEnd ℂ (h σ (e σ x) (e σ y))
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]
  | tmul z a =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add c d hc' hd => simp only [map_add (f := _), ← hc', ← hd]
    | tmul w b =>
      rw [tm σ z a, tm σ w b, conjMap_smul, conjMap_smul, cm, cm]
      simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, hc, smul_eq_mul, map_mul, Complex.conj_conj, RingHom.id_apply]

end Linear

section Geo

theorem exists_fibre_equiv {S : Scheme.{0}} (G : Over S) [GrpObj G] [Smooth G.hom] {L : Type} [Field L] [NumberField L]
    (x : Sp (𝓞 L) ⟶ S) {V : Type} [AddCommGroup V] [Module (𝓞 L) V] (M : LieModel G x V) (σ : L →+* ℂ)
    {W : Type} [AddCommGroup W] [Module ℂ W] (Mσ : LieModel G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ x) W)
    (j : V →ₛₗ[σ.comp (algebraMap (𝓞 L) L)] W)
    (hj : ∀ a, ((Mσ.pt (j a)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (M.pt a).left)) :
    ∃ e : Fibre σ V ≃ₗ[ℂ] W, ∀ a, e ((1 : ComplexAt σ) ⊗ₜ a) = j a := by
  letI i₀ : Algebra (𝓞 L) ℂ := (σ.comp (algebraMap (𝓞 L) L)).toAlgebra
  letI i₂ : Module (𝓞 L) W := Module.compHom W (algebraMap (𝓞 L) ℂ)
  haveI i₃ : IsScalarTower (𝓞 L) ℂ W := ⟨fun a z w => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  let j' : V →ₗ[𝓞 L] W := { toFun := j, map_add' := map_add j, map_smul' := fun a v => j.map_smulₛₗ a v }
  have hb : IsBaseChange ℂ j' :=
    GlobalTheory.T.lie_model_isBaseChange S G (𝓞 L) ℂ x V W M Mσ j' hj
  let l : ComplexAt σ ≃ₗ[𝓞 L] ℂ :=
    { toFun := (ofComplex σ).symm, invFun := ofComplex σ, map_add' := map_add _,
      map_smul' := fun a z => rfl, left_inv := (ofComplex σ).left_inv, right_inv := (ofComplex σ).right_inv }
  let e₀ : Fibre σ V ≃ₗ[𝓞 L] ℂ ⊗[𝓞 L] V := TensorProduct.congr l (LinearEquiv.refl _ V)
  let E : Fibre σ V ≃+ W := e₀.toAddEquiv.trans hb.equiv.toAddEquiv
  have he : ∀ z a, E (z ⊗ₜ a) = ((ofComplex σ).symm z) • j a := fun z a => by
    change hb.equiv (e₀ (z ⊗ₜ a)) = _
    change hb.equiv (l z ⊗ₜ a) = _
    rw [hb.equiv_tmul]
    rfl
  refine ⟨{ E with map_smul' := fun c t => ?_ }, fun a => ?_⟩
  · change E (c • t) = c • E t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
      rw [TensorProduct.smul_tmul', he, he, ComplexAt.complex_smul_def, map_mul, mul_smul]
      simp
    | add a b ha hb' => rw [smul_add, map_add (f := _), map_add (f := _), ha, hb', smul_add]
  · exact (he 1 a).trans (by simp)

theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem dualMap_comp_alt {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) :=
  RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem lifts_left {S : Scheme.{0}} {G : Over S} [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] {x : Sp R ⟶ S}
    {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G x V) {c : R →+* R'} {x' : Sp R' ⟶ S} {a : V}
    {v : epsAt x' ⟶ G} (h : (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt a).left)) : v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt a).left :=
  (Category.comp_id _).symm.trans h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polarised_at {L : Type} [Field L] [NumberField L] (t : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L))
    (m : SABMap tK t (spMap (algebraMap (𝓞 L) L))) (hK : IsPrincipal tK) (σ : L →+* ℂ) :
    ∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' t (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _)),
      IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L := by
  obtain ⟨hP, hA, -⟩ := hK
  obtain ⟨t', ⟨m₁⟩⟩ := exists_sab (spMap σ) tK
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₁
  have e : spMap σ ≫ spMap (algebraMap (𝓞 L) L) = spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ := by
    rw [Category.comp_id, spectrumMap_comp]
  refine ⟨t', e ▸ n, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsProper) m₁.cart.1 hP
  · obtain ⟨w, gw, -⟩ := m₁.lin
    exact relAmple_pull m₁.cart.1 tK.PP.isLB t'.PP.isLB ((isGen_iff w).1 gw) ⊤ (isAffineOpen_top _)
      (fun _ => trivial) hA

theorem hodgeInnerProduct_conj_of_eq {X : Scheme.{0}} (t : SAB H X) {z z' : Sp ℂ ⟶ X}
    (hz : z' = spMap (starRingEnd ℂ) ≫ z) {v w : epsAt z ⟶ t.G} {v' w' : epsAt z' ⟶ t.G} {c : ℂ}
    (hv : v'.left = spMap (dualMap (starRingEnd ℂ)) ≫ v.left)
    (hw : w'.left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left) (h : HodgeIP t.G t.PP.L z v w c) :
    HodgeIP t.G t.PP.L z' v' w' (starRingEnd ℂ c) := by
  subst hz
  exact GlobalTheory.T.hodge_inner_product_conjugate E H X t z v w v' w' c hv hw h

end Geo

theorem exists_hermitianBundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (_ : SABMap tK t (spMap (algebraMap (𝓞 L) L))), IsPrincipal tK → ∃ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t.G (𝟙 _) B.carrier), IsFibre (HodgeIP t.G t.PP.L) (𝟙 _) B MB := by
  intro E _ _ _ H L _ _ t tK m hK
  haveI : Smooth t.G.hom := t.semi.smooth
  obtain ⟨V, i₁, i₂, ⟨M⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ t.G (𝓞 L) (𝟙 _)
  obtain ⟨hf, hpj⟩ := GlobalTheory.T.lie_model_finite_projective _ t.G (𝓞 L) (𝟙 _) V M
  have hW := fun σ : L →+* ℂ => GlobalTheory.CompanionTheory.Ar.lieModel_exists _ t.G ℂ (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _)
  choose W iW₁ iW₂ hM using hW
  let Mσ : ∀ σ : L →+* ℂ, LieModel t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _) (W σ) := fun σ => (hM σ).some
  choose j hj using fun σ : L →+* ℂ =>
    (GlobalTheory.CompanionTheory.Ar.LieBaseChange.existsUnique_semilinear_lifts _ t.G (𝓞 L) ℂ (σ.comp (algebraMap (𝓞 L) L)) (𝟙 _) V (W σ) M (Mσ σ)).exists
  choose e he using fun σ : L →+* ℂ => exists_fibre_equiv t.G (𝟙 _) M σ (Mσ σ) (j σ) (hj σ)
  choose h hI hh hp using fun σ : L →+* ℂ =>
    GlobalTheory.CompanionTheory.Ar.exists_hodgeInnerProduct_form E H _ t _ (W σ) (Mσ σ) (polarised_at t tK m hK σ)
  have hcs : ∀ σ : L →+* ℂ, (conjugate σ).comp (algebraMap (𝓞 L) L) =
      (starRingEnd ℂ).comp (σ.comp (algebraMap (𝓞 L) L)) := fun σ => RingHom.ext fun a => rfl
  have hl : ∀ (σ : L →+* ℂ) (x : V), ((Mσ (conjugate σ)).pt (j _ x)).left =
      spMap (dualMap (starRingEnd ℂ)) ≫ ((Mσ σ).pt (j σ x)).left := fun σ x => by
    have e₁ : spMap (dualMap ((conjugate σ).comp (algebraMap (𝓞 L) L))) =
        spMap (dualMap (starRingEnd ℂ)) ≫ spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) := by
      rw [hcs, dualMap_comp_alt, spectrumMap_comp]
    exact (lifts_left M (hj _ x)).trans ((congrArg (· ≫ (M.pt x).left) e₁).trans ((Category.assoc _ _ _).trans
      (congrArg (spMap (dualMap (starRingEnd ℂ)) ≫ ·) (lifts_left M (hj σ x)).symm)))
  have hz : ∀ σ : L →+* ℂ, spMap ((conjugate σ).comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ =
      spMap (starRingEnd ℂ) ≫ spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ := fun σ => by
    rw [Category.comp_id, Category.comp_id, hcs, spectrumMap_comp]
  obtain ⟨mt, hmt⟩ := exists_metric W e h hh hp fun σ x y => by
    rw [he, he, he, he]
    exact ((hI _ _ _ _).1 (hodgeInnerProduct_conj_of_eq t (hz σ) (hl σ x) (hl σ y) ((hI σ _ _ _).2 rfl))).symm
  refine ⟨{ carrier := V, metric := mt }, M, fun σ x x' v v' hv hv' => ?_⟩
  have key : ∀ (a : V) (u : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _) ⟶ t.G),
      (u.left ≫ (𝟙 t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (M.pt a).left) → u = (Mσ σ).pt (j σ a) := fun a u ha => by
    exact Over.OverMorphism.ext ((lifts_left M ha).trans (lifts_left M (hj σ a)).symm)
  obtain rfl := key x v hv
  obtain rfl := key x' v' hv'
  have := hmt σ x x'
  rw [he, he] at this
  rw [this]
  exact (hI σ _ _ _).2 rfl

end GlobalTheory.CompanionTheory.Ar.HodgeFibre
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalHermitianFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_hermitian_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (_ : SABMap tK t (spMap (algebraMap (𝓞 L) L))), IsPrincipal tK → ∃ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t.G (𝟙 _) B.carrier), IsFibre (HodgeIP t.G t.PP.L) (𝟙 _) B MB := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeFibre.exists_hermitianBundle | exact GlobalTheory.CompanionTheory.Ar.HodgeFibre.exists_hermitianBundle | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeFibre.exists_hermitianBundle <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeMetricFrameInner
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeMetricFrameInner
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameGram

theorem inner_eq_pi_herm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) (x y : D.B.carrier) (c c' : Fin D.g → ℂ), D.IsVec a x c → D.IsVec a y c' → ((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] y) : ℂ) = Real.pi * a.herm c' c := by
  intro E _ _ _ H L _ _ D σ a x y c c' hx hy
  obtain ⟨t', m, hP, hA⟩ := GlobalTheory.T.complex_abelian_fibre_ample E H L D σ
  obtain ⟨hab, g, u, Hm, χ, hAH, d₁, d₂⟩ := FrameEx.exists_goodUnif E H _ D.t (emb σ) t' m hP hA
  have hp : IsGrpPullback t'.G D.t.G (emb σ) m.φ := m.cart
  obtain ⟨v, hlift, vA, hvA, hdiff⟩ := hx
  obtain ⟨w, hlift', wA, hwA, hdiff'⟩ := hy
  have e : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L)) = emb σ := Category.comp_id _
  let v₀ : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) ⟶ D.t.G :=
    Over.homMk v.left (by simpa using Over.w v)
  let w₀ : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) ⟶ D.t.G :=
    Over.homMk w.left (by simpa using Over.w w)
  have hl₀ : (v₀.left ≫ (𝟙 D.t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt x).left) := hlift
  have hl₁ : (w₀.left ≫ (𝟙 D.t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt y).left) := hlift'
  obtain ⟨hL, hvt, hwt, A', _, φ', g', u', Hm', χ', p, q, a', b', hp', hah', ep, eq', dp, dq, hval⟩ :=
    D.fib σ x y v₀ w₀ hl₀ hl₁
  have hp₀ : IsGrpPullback t'.G D.t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) m.φ :=
    IsGrpPullback.congr hp e.symm rfl
  have hpz : IsGrpPullback A' D.t.G (emb σ) φ' := IsGrpPullback.congr hp' e rfl
  let x₁ : epsR ℂ ⟶ t'.G := (HodgeLin.tanEquiv hp₀).symm v₀
  let y₁ : epsR ℂ ⟶ t'.G := (HodgeLin.tanEquiv hp₀).symm w₀
  have hx₁ : HodgeLin.tanEquiv hp₀ x₁ = v₀ := (HodgeLin.tanEquiv hp₀).apply_symm_apply _
  have hy₁ : HodgeLin.tanEquiv hp₀ y₁ = w₀ := (HodgeLin.tanEquiv hp₀).apply_symm_apply _
  have tx₁ : IsTangent x₁ := (HodgeLin.isTangent_iff hp₀ x₁).2 (by rw [hx₁]; exact hvt)
  have ty₁ : IsTangent y₁ := (HodgeLin.isTangent_iff hp₀ y₁).2 (by rw [hy₁]; exact hwt)
  have lx₁ : x₁.left ≫ m.φ = v.left := congrArg (fun r => r.left) hx₁
  have ly₁ : y₁.left ≫ m.φ = w.left := congrArg (fun r => r.left) hy₁
  obtain ⟨cx, hcx, -⟩ := d₁ x₁ tx₁
  obtain ⟨cy, hcy, -⟩ := d₁ y₁ ty₁
  have T1 := GlobalTheory.T.hol_unif_compare_isogeny (Sp (𝓞 L)) D.t.G D.t.PP.L (emb σ) t'.G a.A m.φ a.φ g D.g u a.u Hm a.Hm χ a.χ D.t.PP.isLB
    hab hp a.cart d₁ d₂ hAH a.ah y₁ x₁ wA vA cy cx c' c ty₁ tx₁ (hwA.trans ly₁.symm) (hvA.trans lx₁.symm) hcy hcx
    hdiff' hdiff
  have T2 := GlobalTheory.T.hol_unif_compare_isogeny (Sp (𝓞 L)) D.t.G D.t.PP.L (emb σ) t'.G A' m.φ φ' g g' u u' Hm Hm' χ χ' D.t.PP.isLB
    hab hp hpz d₁ d₂ hAH hah' y₁ x₁ q p cy cx b' a' ty₁ tx₁ (eq'.trans ly₁.symm) (ep.trans lx₁.symm) hcy hcx dq dp
  have hH : a.herm c' c = hermForm Hm' b' a' := T1.trans T2.symm
  rw [hH]
  exact hval

end GlobalTheory.CompanionTheory.Ar.Sl.FrameGram
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeMetricFrameInnerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_metric_frame_inner : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) (x y : D.B.carrier) (c c' : Fin D.g → ℂ), D.IsVec a x c → D.IsVec a y c' → ((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] y) : ℂ) = Real.pi * a.herm c' c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.FrameGram.inner_eq_pi_herm | exact GlobalTheory.CompanionTheory.Ar.Sl.FrameGram.inner_eq_pi_herm | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.FrameGram.inner_eq_pi_herm <;> assumption)
end
end

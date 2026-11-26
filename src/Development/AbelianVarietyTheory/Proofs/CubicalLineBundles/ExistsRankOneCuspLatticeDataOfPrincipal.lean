module

public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnitHmA
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipal
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipal
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.LatticeData

theorem cc_eq_conj (D : D7) (x : D.host.E) : ReciprocityTheory.ChartRestriction.G.FD.cc x = D.host.conj x :=
  bridge_star_holds D.R D.host x

theorem flagDomainConj_hostXi_eq_neg (D : D7) : ReciprocityTheory.ChartRestriction.G.FD.cc D.host.xi0 = -D.host.xi0 :=
  conj_xi0_alt D

theorem halfDifferent_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  exact (bB_ne D).1 (by rw [h]; simp)

theorem absNorm_halfDifferent_le (D : D7) :
    (Ideal.absNorm D.host.𝔟 : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| := by
  have ht : differentIdeal ℤ (𝓞 D.host.E) = differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) *
      (differentIdeal ℤ (𝓞 D.host.K)).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) :=
    differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.K) (𝓞 D.host.E)
  have hdvd : D.host.𝔟 ∣ differentIdeal ℤ (𝓞 D.host.E) := by
    rw [ht, D.host.𝔟_spec.1, mul_assoc]
    exact dvd_mul_right _ _
  have h1 := map_dvd Ideal.absNorm hdvd
  rw [NumberField.absNorm_differentIdeal D.host.E (𝓞 D.host.E)] at h1
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 (NumberField.discr_ne_zero D.host.E)) h1
  rw [← Int.cast_abs, ← Nat.cast_natAbs]
  exact_mod_cast h2

theorem absNorm_mul_mem_one (D : D7) {a : D.host.E} (ha : a ∈ D.host.AA) :
    ∃ z : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E z = (Ideal.absNorm D.host.𝔟 : D.host.E) * a := by
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0 at ha
  rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero (bB_ne D).1] at ha
  obtain ⟨w, -, hw⟩ := (FractionalIdeal.mem_coeIdeal _).1
    (ha _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.absNorm_mem D.host.𝔟, rfl⟩))
  exact ⟨w, by rw [hw, map_natCast, mul_comm]⟩

theorem absNorm_ccK_mem (D : D7) : (Ideal.absNorm D.host.ccK : D.host.E) ∈ D.host.AA := by
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0
  rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero (bB_ne D).1]
  intro y hy
  obtain ⟨z, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
  have h : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ D.host.ccE := by
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.ccK)
    rwa [map_natCast] at this
  exact (FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.mul_mem_right z _ h, by rw [map_mul, map_natCast]⟩

theorem exists_dataX_of_hasPrinc : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (hj : InR D j), ∀ σ, GoodEmb T.Q.c σ → GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) T.Q.l.M → ∀ k : (T.U j σ).Comp, ∃ Xx : ReciprocityTheory.ChartRestriction.G.FD.DataX D.host.E D.R.r, Xx.toData = (T.U j σ).X k ∧ Xx.g = T.Q.l.M ∧ Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} ∧ Xx.k0 = 2 * xiR D ∧ (Xx.NA : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| ∧ Xx.NC ≤ Ideal.absNorm D.host.ccK := by
  intro D T h j hj σ hσ hP k
  obtain ⟨-, -, -, hx0, hx1, -⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have habs := h.xiAbs j hj σ hσ k
  have hperf := GlobalTheory.traceForm_integral_perfect_of_isUnf _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ hσ)) k
  have hξ := GlobalTheory.eq_or_eq_neg_of_purelyImaginary_of_norm_eq _ D.host.xi0 ((T.U j σ).X k).ξ0 D.host.φ₀
    (flagDomainConj_hostXi_eq_neg D) ((T.U j σ).X k).ξ0_im (habs _).symm
  have hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) ((T.U j σ).X k).ξ0 * D.host.AA *
      D.host.AAbar * (differentIdeal ℤ (𝓞 D.host.E) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 1 := by
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rcases hξ with e | e
    · rw [e]; exact h1
    · rw [e, show -D.host.xi0 = (-1 : (𝓞 D.host.E)ˣ) • D.host.xi0 by simp,
        ← (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, rfl⟩)]
      exact h1
  have hM : 0 < T.Q.l.M := by have := T.Q.l.three_le; omega
  obtain ⟨Xx, h1, h2, h3⟩ := GlobalTheory.exists_dataX_of_perfect_traceForm _ _ ((T.U j σ).X k) D.host.AA D.host.AAbar
    (xiR D) T.Q.l.M
    (fun a => by
      rw [cc_eq_conj]
      exact ⟨conj_mem_AA D, fun ha => by simpa only [conj_conj] using conj_mem_AAbar D ha⟩)
    hone habs hx1 hperf.1 hperf.2 hM (hP k)
  refine ⟨{ Xx with
    k0 := 2 * xiR D
    minWeight_pos := by positivity
    k0_le := by linarith
    ξ0_abs := fun τ => by rw [show Xx.ξ0 = ((T.U j σ).X k).ξ0 from congrArg _ h1, habs]; ring
    NA := Ideal.absNorm D.host.𝔟
    NC := Ideal.absNorm D.host.ccK
    NA_pos := Nat.pos_of_ne_zero fun e => halfDifferent_ne_bot D (Ideal.absNorm_eq_zero_iff.1 e)
    NC_pos := Nat.pos_of_ne_zero fun e => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
    NA_sub := fun x hx => ?_
    NC_sub := fun x hx => ?_ }, h1, h2, h3, rfl, absNorm_halfDifferent_le D, le_rfl⟩
  · rw [h3] at hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hv
      obtain ⟨z, hz⟩ := absNorm_mul_mem_one D ha
      rw [smul_smul, ← hz, algebraMap_smul]
      exact Xx.L'.smul_mem z hu
    | zero => simp
    | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
    | smul c v _ hv => rw [smul_comm]; exact Xx.L'.smul_mem c hv
  · rw [h3]
    exact Submodule.subset_span ⟨_, absNorm_ccK_mem D, x, hx, rfl⟩

end GlobalTheory.LatticeData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipalStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rankOneCuspLatticeData_of_principal : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (hj : InR D j), ∀ σ, GoodEmb T.Q.c σ → GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) T.Q.l.M → ∀ k : (T.U j σ).Comp, ∃ Xx : ReciprocityTheory.ChartRestriction.G.FD.DataX D.host.E D.R.r, Xx.toData = (T.U j σ).X k ∧ Xx.g = T.Q.l.M ∧ Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} ∧ Xx.k0 = 2 * xiR D ∧ (Xx.NA : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| ∧ Xx.NC ≤ Ideal.absNorm D.host.ccK := by
  first | exact @GlobalTheory.LatticeData.exists_dataX_of_hasPrinc | exact GlobalTheory.LatticeData.exists_dataX_of_hasPrinc | (intros; apply GlobalTheory.LatticeData.exists_dataX_of_hasPrinc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTriplePullback
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTriplePullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem pat_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (T : PAT H (Sp R)), (∃ (T' : PAT H (Sp R')) (_ : SABMap T'.t T.t (spMap f)), T'.g = T.g) ∧ ∀ (T' : PAT H (Sp R')) (m : SABMap T'.t T.t (spMap f)), Nontrivial R' → T'.g = T.g ∧ IsPolFibre f T.pol T'.pol m.φ ∧ ∃ w : LB.Iso T'.t.PP.L (T.t.PP.L.pull m.φ), RigIso m w := by
  intro E _ _ _ H R R' _ _ f T
  refine ⟨?_, fun T' m hR => ?_⟩
  · obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap f) T.t
    obtain ⟨⟨T', ht, hg⟩, -⟩ := PAT.exists_of_sabMap E H _ _ _ T _ m
    exact ⟨T', ht ▸ m, hg⟩
  · obtain ⟨-, e⟩ := PAT.exists_of_sabMap E H _ _ _ T _ m
    have hd : SmoothOfRelativeDimension T.g T'.t.G.hom :=
      have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} T.g
      MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension T.g) m.cart.1 T.dim
    obtain ⟨p⟩ : Nonempty (PrimeSpectrum R') := inferInstance
    have hg : T'.g = T.g := ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ T'.dim hd (eSec T'.t.G p)
    obtain ⟨w, hw, hr, -⟩ := m.lin
    exact ⟨hg, ⟨hg, m.cart, e⟩, w, hw, hr⟩

end GlobalTheory.LamT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTriplePullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalTriple_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (T : PAT H (Sp R)), (∃ (T' : PAT H (Sp R')) (_ : SABMap T'.t T.t (spMap f)), T'.g = T.g) ∧ ∀ (T' : PAT H (Sp R')) (m : SABMap T'.t T.t (spMap f)), Nontrivial R' → T'.g = T.g ∧ IsPolFibre f T.pol T'.pol m.φ ∧ ∃ w : LB.Iso T'.t.PP.L (T.t.PP.L.pull m.φ), RigIso m w := by
  first | exact @GlobalTheory.LamT.pat_pullback | exact GlobalTheory.LamT.pat_pullback | (intros; apply GlobalTheory.LamT.pat_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SabMapCancelAndCompOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory

theorem sabMap_cancel_and_comp_over : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S₁ S₂ : Scheme.{0}) (t : SAB H S) (t₁ : SAB H S₁) (t₂ : SAB H S₂) (f₁ : S₁ ⟶ S) (f₂ : S₂ ⟶ S) (g : S₂ ⟶ S₁) (m₁ : SABMap t₁ t f₁) (m₂ : SABMap t₂ t f₂), f₂ = g ≫ f₁ → (∃ n : SABMap t₂ t₁ g, n.φ ≫ m₁.φ = m₂.φ) ∧ ∀ n : SABMap t₂ t₁ g, ∃ m : SABMap t₂ t f₂, m.φ = n.φ ≫ m₁.φ := by
  intro E _ _ _ H S S₁ S₂ t t₁ t₂ f₁ f₂ g m₁ m₂ h
  subst h
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ t t₁ t₂ f₁ g m₁ m₂
  exact ⟨⟨n, hn.symm⟩, fun n => sabComp pullCubComp E H _ _ _ t t₁ t₂ f₁ g m₁ n⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniformisationOfComplexConjugateKeyDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniformisationOfComplexConjugateKeyDatum
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.ConjUnif

open GlobalTheory.ArchMetricCompare

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g : ℕ}

theorem le_pull_id (x : Sp ℂ ⟶ A.left) (j : (L.pull (𝟙 A.left)).ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.pull (𝟙 A.left)).U j ↔ ⊤ ≤ x ⁻¹ᵁ L.U (j PUnit.unit) := by
  rw [le_pull_iff, Category.comp_id]

def pullId (u : HolUnif A L g) : HolUnif A (L.pull (𝟙 A.left)) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr j := u.fr (j PUnit.unit)
  fr_hol j := by
    have e : {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.pull (𝟙 A.left)).U j} = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j PUnit.unit)} :=
      Set.ext fun z => le_pull_id _ j
    rw [e]
    exact u.fr_hol _
  fr_ne j z hz := u.fr_ne _ z ((le_pull_id _ j).1 hz)
  fr_compat j j' z hz := by
    obtain ⟨hj, hj'⟩ := (top_le_preimage_inf _ _ _).1 hz
    rw [val_pull_g L _ _ j j' hz, u.fr_compat _ _ z
      ((top_le_preimage_inf _ _ _).2 ⟨(le_pull_id _ j).1 hj, (le_pull_id _ j').1 hj'⟩)]
    congr 2

variable {ψ : A'.left ⟶ A.left} (h : IsGrpPullback A' A cj ψ)

theorem cj_le (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) (j : (L.pull ψ).ι) :
    ⊤ ≤ (cjPt h x).left ⁻¹ᵁ (L.pull ψ).U j ↔ ⊤ ≤ x.left ⁻¹ᵁ L.U (j PUnit.unit) := by
  refine (le_pull_iff L _ _ j).trans ?_
  rw [cjPt_comp]
  exact le_cj_iff _ _

def conjPull (u : HolUnif A L g) : HolUnif A' (L.pull ψ) g where
  ex := (cjUnif h (pullId u)).ex
  ex_add := (cjUnif h (pullId u)).ex_add
  ex_onto := (cjUnif h (pullId u)).ex_onto
  Λ := (cjUnif h (pullId u)).Λ
  ker := (cjUnif h (pullId u)).ker
  discrete := (cjUnif h (pullId u)).discrete
  full := (cjUnif h (pullId u)).full
  hol := (cjUnif h (pullId u)).hol
  fr j z := star (u.fr (j PUnit.unit) (star z))
  fr_hol j := by
    have e : {z | ⊤ ≤ ((cjUnif h (pullId u)).ex z).left ⁻¹ᵁ (L.pull ψ).U j} =
        {z | star z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j PUnit.unit)}} :=
      Set.ext fun z => cj_le h _ j
    rw [e]
    exact differentiableOn_star (u.hol _ 0).1 (u.fr_hol _)
  fr_ne j z hz := star_ne_zero.2 (u.fr_ne _ _ ((cj_le h _ j).1 hz))
  fr_compat j j' z hz := by
    obtain ⟨hj, hj'⟩ := (top_le_preimage_inf _ _ _).1 hz
    have hm := (top_le_preimage_inf _ _ _).2 ⟨(cj_le h _ j).1 hj, (cj_le h _ j').1 hj'⟩
    rw [val_pull_g L _ _ j j' hz, u.fr_compat _ _ _ hm, star_mul']
    congr 1
    exact ((congrArg (fun x => valAt' x _ _) (cjPt_comp h (u.ex (star z)))).trans (val_cj _ _ _)).symm

theorem conjPull_isAH (u : HolUnif A L g) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hA : u.IsAH Hm χ) :
    (conjPull h u).IsAH (Hm.map star) fun l => star (χ ⟨star l.1, l.2⟩) := by
  have h0 : (pullId u).IsAH Hm χ :=
    ⟨hA.1, hA.2.1, hA.2.2.1, fun l j z hj => hA.2.2.2 l _ z ((le_pull_id _ j).1 hj)⟩
  have h1 := cj_isAH h _ h0
  exact ⟨h1.1, h1.2.1, h1.2.2.1, fun l j z hj =>
    h1.2.2.2 l j z ((cj_le_pull h _ j).2 ((le_pull_id _ j).2 ((cj_le h _ j).1 hj)))⟩

theorem exists_inv {X : Scheme.{0}} {M N : LB X} (w : LB.Iso M N) (hw : w.IsGen) :
    ∃ w' : LB.Iso N M, w'.IsGen ∧ ∀ (x : Sp ℂ ⟶ X) (j : N.ι) (i : M.ι), ⊤ ≤ x ⁻¹ᵁ (N.U j ⊓ M.U i) →
      valAt' x (M.U i ⊓ N.U j) (w'.s (i, j)).val = (valAt' x (N.U j ⊓ M.U i) (w.s (j, i)).val)⁻¹ := by
  have le : ∀ p : M.ι × N.ι, M.U p.1 ⊓ N.U p.2 ≤ N.U p.2 ⊓ M.U p.1 := fun p y hy => ⟨hy.2, hy.1⟩
  refine ⟨⟨fun p => (res (le p) (w.s (p.2, p.1)))⁻¹⟩, fun p q => unit_ext fun y hy => ?_, fun x j i hx => ?_⟩
  · have hm : (𝟙 X : X ⟶ X) y ∈ N.U p.2 ⊓ M.U p.1 ⊓ (N.U q.2 ⊓ M.U q.1) := ⟨le p hy.1, le q hy.2⟩
    have e := congrArg (gm (𝟙 X) y (N.U p.2 ⊓ M.U p.1 ⊓ (N.U q.2 ⊓ M.U q.1))) (hw (p.2, p.1) (q.2, q.1))
    have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div M N (𝟙 X) y (p.2, p.1) (q.2, q.1) hm) (gm_res _ y _ hm _))))
    have v : ∀ p : M.ι × N.ι, y ∈ M.U p.1 ⊓ N.U p.2 →
        gm (𝟙 X) y (M.U p.1 ⊓ N.U p.2) (res (le p) (w.s (p.2, p.1)))⁻¹ =
        (gm (𝟙 X) y (N.U p.2 ⊓ M.U p.1) (w.s (p.2, p.1)))⁻¹ := fun p hp =>
      (map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))
    refine ((gm_res _ y _ hy _).trans ((v p hy.1).trans (congrArg (·⁻¹) e'))).trans (Eq.symm ?_)
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div N M (𝟙 X) y p q hy)
      ((gm_res _ y _ hy _).trans (v q hy.2)))).trans ?_
    rw [mul_inv, mul_inv, inv_inv, mul_comm (gm (𝟙 X) y _ (M.g p.1 q.1))]
    rfl
  · have hx' : ⊤ ≤ x ⁻¹ᵁ (M.U i ⊓ N.U j) := by rwa [inf_comm]
    exact (valAt'_units_inv x hx' _).trans (congrArg _ (valAt'_res x (le (i, j)) _ hx'))

theorem exists_conj_unif : ∀ (x x' : KeyIn ℂ), KeyPB x' x (starRingEnd ℂ) → ∀ (hg : x'.P.g = x.P.g) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)), u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume → ∃ (u' : HolUnif x'.P.A x'.P.L g) (χ' : u'.Λ → ℂ) (θ' : (Fin g → ℂ) → ℂ) (Fd' : Set (Fin g → ℂ)), u'.IsAH (Hm.map (starRingEnd ℂ)) χ' ∧ u'.IsRig x'.rig ∧ u'.IsFn x'.th θ' ∧ IsAddFundamentalDomain u'.Λ Fd' volume ∧ (∫ z in Fd', ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm (Hm.map (starRingEnd ℂ)) z z).re)) / (volume Fd').toReal = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal ∧ ∀ (cf : Fin x.P.g → ℂ) (w : epsR ℂ ⟶ x.P.A) (w' : epsR ℂ ⟶ x'.P.A) (W : Fin g → ℂ), IsLieComb cf x.v w → IsLieComb (fun i => (starRingEnd ℂ) (cf (i.cast hg))) x'.v w' → u.IsDiff W w → u'.IsDiff (fun i => (starRingEnd ℂ) (W i)) w' := by
  rintro x x' ⟨φ, he, w, hg', F, hφ, hw, hrig, hth, hF, hε, hv⟩ hg g u Hm χ θ Fd ⟨hA, hR, hθ, hFd⟩
  rw [KeyFibre.eq_dualMapR_of_algebraMap _ F hF hε] at hv
  obtain ⟨w', hw', hinv⟩ := exists_inv w hw
  have hP : (x.P.L.pull φ).IsLB := DVR.linComb_isLB x.P.L x.P.isLB _ _
  let u₁ := conjPull hφ u
  have me : MeasurableEmbedding (star : (Fin g → ℂ) → Fin g → ℂ) :=
    (starL' ℝ (A := Fin g → ℂ)).toHomeomorph.measurableEmbedding
  have fr : ∀ (j : x.P.L.ι) (i : x'.P.L.ι) (z : Fin g → ℂ),
      ⊤ ≤ (u₁.ex z).left ⁻¹ᵁ ((x.P.L.pull φ).U (fun _ => j) ⊓ x'.P.L.U i) →
      valAt' (u₁.ex z).left ((x.P.L.pull φ).U (fun _ => j) ⊓ x'.P.L.U i) (w.s (fun _ => j, i)).val *
        (carry u₁ hP x'.P.isLB hw').fr i z = star (u.fr j (star z)) := by
    intro j i z hz
    obtain ⟨hj, hi⟩ := (top_le_preimage_inf _ _ _).1 hz
    rw [carry_fr u₁ hP x'.P.isLB hw' i (fun _ => j) z hi hj, hinv _ _ _ hz]
    exact mul_inv_cancel_left₀ (valAt'_unit_ne_zero _ hz (w.s (fun _ => j, i))) _
  refine ⟨carry u₁ hP x'.P.isLB hw', _, fun z => star (θ (star z)), star ⁻¹' Fd,
    carry_isAH hP x'.P.isLB hw' (conjPull_isAH hφ u hA), ?_, ?_, cj_domain hφ (pullId u) hFd, ?_, ?_⟩
  · intro i hi
    have h0 : (u₁.ex 0).left = eSec x'.P.A := by
      rw [(u₁.ker 0).2 u₁.Λ.zero_mem, Hom.one_def]
      simp [eSec]
    have h0' : (u.ex 0).left = eSec x.P.A := by
      rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def]
      simp [eSec]
    obtain ⟨j, hj⟩ := exists_chart_at hP (u₁.ex 0).left
    have hi' : ⊤ ≤ (u₁.ex 0).left ⁻¹ᵁ x'.P.L.U (i PUnit.unit) := by
      rw [h0]
      exact fun p hp => mem_pull.1 (hi hp)
    have hz := (top_le_preimage_inf _ _ _).2 ⟨hj, hi'⟩
    have e := fr (j PUnit.unit) (i PUnit.unit) 0 hz
    have hj' : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ x.P.L.U (j PUnit.unit) := by
      have := (cj_le hφ _ j).1 hj
      rwa [star_zero] at this
    rw [h0'] at hj'
    have hj'' : ⊤ ≤ (x.P.L.pull (eSec x.P.A)).U fun _ => j PUnit.unit := fun p hp => mem_pull.2 (hj' hp)
    rw [star_zero, hR _ hj'', ← val_cj, Category.comp_id, h0] at e
    rw [h0] at hz
    exact mul_left_cancel₀ (valAt'_unit_ne_zero _ hz _)
      (e.trans (val_rig he w x'.rig x.rig hrig (j PUnit.unit) (i PUnit.unit) hz))
  · intro i z hi
    obtain ⟨j, hj⟩ := exists_chart_at hP (u₁.ex z).left
    have hz := (top_le_preimage_inf _ _ _).2 ⟨hj, hi⟩
    have e := fr (j PUnit.unit) i z hz
    have e₁ := val_via w x.th x'.th hth (u₁.ex z).left (j PUnit.unit) i hz
    have e₂ : valAt' ((u₁.ex z).left ≫ φ) (x.P.L.U (j PUnit.unit)) (x.th.f (j PUnit.unit)) =
        star (θ (star z)) * star (u.fr (j PUnit.unit) (star z)) :=
      (congrArg (fun x => valAt' x _ _) (cjPt_comp hφ (u.ex (star z)))).trans ((val_cj _ _ _).trans
        ((congrArg star (hθ _ (star z) ((cj_le hφ _ j).1 hj))).trans (star_mul' _ _)))
    refine mul_left_cancel₀ (valAt'_unit_ne_zero _ hz (w.s (fun _ => j PUnit.unit, i))) ?_
    refine e₁.symm.trans (e₂.trans ?_)
    rw [← e]
    exact mul_left_comm _ _ _
  · rw [measurePreserving_star.measure_preimage_emb me Fd, ← measurePreserving_star.setIntegral_preimage_emb me _ Fd]
    refine congrArg (fun t : (Fin g → ℂ) → ℝ => (∫ z in star ⁻¹' Fd, t z) / (volume Fd).toReal) (funext fun z => ?_)
    rw [norm_star]
    exact congrArg (fun t : ℝ => ‖θ (star z)‖ ^ 2 * Real.exp (-Real.pi * t)) (hermSq_star Hm z)
  · intro cf v v' W h₁ h₂ hd
    have h₃ : ∀ (n : ℕ) (e : n = x.P.g), IsLieComb (fun i => cf (i.cast e)) (fun i : Fin n => x.v (i.cast e)) v := by
      rintro _ rfl
      exact h₁
    have e := (lieComb_baseChange ℂ ℂ _ _ _ φ hφ _ _ v _ x'.v v' hv (h₃ _ hg)).2 h₂
    exact cj_isDiff hφ (pullId u) (GlobalTheory.Reg.isTangent_of_isLieComb x.basis.1 h₁) e hd

end GlobalTheory.ConjUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniformisationOfComplexConjugateKeyDatumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisation_of_complexConjugate_keyDatum : ∀ (x x' : KeyIn ℂ), KeyPB x' x (starRingEnd ℂ) → ∀ (hg : x'.P.g = x.P.g) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)), u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume → ∃ (u' : HolUnif x'.P.A x'.P.L g) (χ' : u'.Λ → ℂ) (θ' : (Fin g → ℂ) → ℂ) (Fd' : Set (Fin g → ℂ)), u'.IsAH (Hm.map (starRingEnd ℂ)) χ' ∧ u'.IsRig x'.rig ∧ u'.IsFn x'.th θ' ∧ IsAddFundamentalDomain u'.Λ Fd' volume ∧ (∫ z in Fd', ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm (Hm.map (starRingEnd ℂ)) z z).re)) / (volume Fd').toReal = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal ∧ ∀ (cf : Fin x.P.g → ℂ) (w : epsR ℂ ⟶ x.P.A) (w' : epsR ℂ ⟶ x'.P.A) (W : Fin g → ℂ), IsLieComb cf x.v w → IsLieComb (fun i => (starRingEnd ℂ) (cf (i.cast hg))) x'.v w' → u.IsDiff W w → u'.IsDiff (fun i => (starRingEnd ℂ) (W i)) w' := by
  first | exact @GlobalTheory.ConjUnif.exists_conj_unif | exact GlobalTheory.ConjUnif.exists_conj_unif | (intros; apply GlobalTheory.ConjUnif.exists_conj_unif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ImDiagEqTrace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.OrthoHerm


open scoped Matrix ComplexConjugate in
theorem im_diag_eq_trace {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (q : ℕ) (ξ : E)
    (Gm : Matrix (Fin r) (Fin r) E) (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (idx : Fin g ≃ Ψ × Fin r)
    (hξ : FD.cc ξ = -ξ) (x : FD.Frame Ψ r)
    (hx : ∀ τ : Ψ, FD.gram τ.1 Gm (FD.mat x τ) = Matrix.diagonal fun a : Fin r => ((FD.sgn q (a : ℕ) : ℝ) : ℂ))
    (v w : Fin r → E) (z z' : Fin g → ℂ)
    (hz : ∀ k, z k = if ((idx k).2 : ℕ) < q then
      FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 v)
      else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 v) (idx k).2)
    (hz' : ∀ k, z' k = if ((idx k).2 : ℕ) < q then
      FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 w)
      else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 w) (idx k).2) :
    (hermForm (Matrix.diagonal fun k => ((2 * ((idx k).1.1 ξ).im : ℝ) : ℂ)) z z').im =
      ((Algebra.trace ℚ E (ξ * FD.herm Gm v w) : ℚ) : ℝ) := by
  rw [GlobalTheory.UnitFrame.trace_eq_sum_re Ψ hΨ]
  let p : (Fin r → E) → Ψ × Fin r → ℂ := fun v t =>
    if (t.2 : ℕ) < q then
      FD.hermC t.1.1 Gm (FD.col (FD.mat x t.1) t.2) (FD.Data.emb t.1.1 v)
    else ((FD.mat x t.1)⁻¹ *ᵥ FD.Data.emb t.1.1 v) t.2
  have h2 : hermForm (Matrix.diagonal fun k => ((2 * ((idx k).1.1 ξ).im : ℝ) : ℂ)) z z' =
      ∑ t : Ψ × Fin r, ((2 * (t.1.1 ξ).im : ℝ) : ℂ) * (p v t * conj (p w t)) := by
    rw [hermForm, dotProduct]
    refine Fintype.sum_equiv idx _ _ fun k => ?_
    rw [Matrix.mulVec_diagonal, Pi.star_apply, hz, hz']
    simp only [p, RCLike.star_def]
    ring
  rw [h2, Fintype.sum_prod_type, Complex.im_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [p]
  rw [← Finset.mul_sum, Complex.im_ofReal_mul,
    GlobalTheory.UnitFrame.im_sum_periods q τ.1 Gm (FD.mat x τ) (hx τ)]
  have h3 : τ.1 (FD.herm Gm v w) = FD.hermC τ.1 Gm (FD.Data.emb τ.1 v) (FD.Data.emb τ.1 w) := by
    simp [FD.hermC, FD.herm, FD.Data.emb, FD.cc, IsCMField.complexEmbedding_complexConj]
  have hre : (τ.1 ξ).re = 0 := by
    have h := congrArg τ.1 hξ
    rw [FD.cc, IsCMField.complexEmbedding_complexConj, map_neg] at h
    have := congrArg Complex.re h
    simp only [Complex.conj_re, Complex.neg_re] at this
    linarith
  rw [map_mul, h3, Complex.mul_re, hre]
  ring

theorem hm_eq_smul_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (ξ : ℝ), GoodEmb c σ → IsUnf U → ∀ (k : U.Comp) (x : (U.X k).dom) (W : PullbackSections.UnfAt U k x) (Wu : PullbackSections.UnitAt W), (∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = ξ) → (U.X k).IsOrtho x.1 → Wu.Hm = ((2 * ξ : ℝ) : ℂ) • (1 : Matrix (Fin W.g) (Fin W.g) ℂ) := by
  intro E _ _ _ H Dw l Xo c σ r U ξ hσ hU k x W Wu hξ hx
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1 (relab c σ) hbij
    Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  have hper : ∀ (v : Fin r → E) j, perFr (U.X k) x.1 v (relab c σ (W.e j).1) (W.e j).2 =
      if (((W.e.trans f) j).2 : ℕ) < (U.X k).p0 then
        FD.hermC ((W.e.trans f) j).1.1 (U.X k).Gm
          (FD.col (FD.mat x.1 ((W.e.trans f) j).1) ((W.e.trans f) j).2) (FD.Data.emb ((W.e.trans f) j).1.1 v)
      else ((FD.mat x.1 ((W.e.trans f) j).1)⁻¹.mulVec (FD.Data.emb ((W.e.trans f) j).1.1 v))
        ((W.e.trans f) j).2 := by
    intro v j
    have h := hf (W.e j)
    rw [Equiv.trans_apply]
    generalize f (W.e j) = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    generalize ((W.e j).2 : ℕ) = i at h ⊢
    dsimp only at h ⊢
    rw [← hp0] at h
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dite_eq_left a, dite_eq_left hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dite_eq_right a, dite_eq_left (show conjEmb (relab c σ (W.e j).1) ∈ (U.X k).Ψ from hτ), dite_eq_left hn]
      rfl
  have hcc : FD.cc (-(U.X k).ξ0) = -(-(U.X k).ξ0) := by
    have h := (U.X k).ξ0_im
    unfold FD.cc at h ⊢
    rw [map_neg, h]
  have key : Wu.Hm = Matrix.diagonal fun j => ((2 * (((W.e.trans f) j).1.1 (-(U.X k).ξ0)).im : ℝ) : ℂ) := by
    refine PullbackSections.UH.herm_eq_of_im W.Pm W.per.2.2.2.1 _ _ fun a b => ?_
    rw [Wu.c1, im_diag_eq_trace (U.X k).p0 _ (U.X k).Gm (U.X k).Ψ (U.X k).cmType (W.e.trans f) hcc x.1 hx
      (W.φ k a) (W.φ k b) _ _ (fun j => (W.pm_eq a j).trans (hper _ j)) (fun j => (W.pm_eq b j).trans (hper _ j)),
      ← W.isom, Rat.cast_intCast]
  have hd : ∀ j, (((W.e.trans f) j).1.1 (-(U.X k).ξ0)).im = ξ := by
    intro j
    have hpos := Wu.pos (Pi.single j 1) (by simp)
    rw [key, hermForm, single_dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Pi.single_eq_same, star_one,
      _root_.one_mul, _root_.mul_one, Complex.ofReal_re] at hpos
    generalize ((W.e.trans f) j).1.1 = τ at hpos ⊢
    have hre : (τ (-(U.X k).ξ0)).re = 0 := by
      have h := congrArg τ hcc
      rw [FD.cc, IsCMField.complexEmbedding_complexConj, map_neg τ (-(U.X k).ξ0)] at h
      have := congrArg Complex.re h
      simp only [Complex.conj_re, Complex.neg_re] at this
      linarith
    have hp : 0 < (τ (-(U.X k).ξ0)).im := by linarith
    rw [← hξ τ, ← norm_neg, ← map_neg, ← Complex.abs_im_eq_norm.mpr hre, abs_of_pos hp]
  rw [key]
  simp only [hd]
  rw [Matrix.smul_one_eq_diagonal]

end GlobalTheory.OrthoHerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmHostRootNegDiscriminantNeNegSelf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cmHost_rootNegDiscriminant_ne_zero (H : Host E) : H.rt0 ≠ 0 := by
  intro h
  have h2 := H.sqrt_neg_disc_sq
  rw [h] at h2
  have : (H.d : ℂ) = 0 := by simpa using h2.symm
  exact H.d_prime.ne_zero (by exact_mod_cast this)

theorem cmHost_rootNegDiscriminant_ne_neg_self (H : Host E) : H.rt0 ≠ -H.rt0 := by
  intro h
  apply cmHost_rootNegDiscriminant_ne_zero H
  linear_combination h / 2

theorem cmHost_conj_sqrtNegDisc (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have h2 := H.sqrt_neg_disc_sq
  have him := congrArg Complex.im h2
  have hre := congrArg Complex.re h2
  simp [pow_two] at him hre
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h0 : H.rt0.re = 0 := by
    by_contra hne
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext <;> simp [h0]

theorem host_emb_rt_sq (H : Host E) (τ : E →+* ℂ) : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
  have h := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
  rw [H.sqrt_neg_disc_sq]
  simpa using h

theorem host_mem_compl_psiSet (H : Host E) (τ : E →+* ℂ) :
    τ ∈ (psiSet H)ᶜ ↔ τ (H.rt : E) = -H.rt0 := by
  change ¬ (τ (H.rt : E) = H.rt0) ↔ _
  constructor
  · intro h
    exact (sq_eq_sq_iff_eq_or_eq_neg.1 (host_emb_rt_sq H τ)).resolve_left h
  · intro h h'
    exact cmHost_rootNegDiscriminant_ne_neg_self H (h'.symm.trans h)

theorem card_psiSet_eq_card_compl (H : Host E) :
    Nat.card (psiSet H) = Nat.card ((psiSet H)ᶜ : Set (E →+* ℂ)) := by
  refine Nat.card_congr
    { toFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, ?_⟩
      invFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, ?_⟩
      left_inv := fun τ => Subtype.ext (star_star τ.1)
      right_inv := fun τ => Subtype.ext (star_star τ.1) }
  · rw [host_mem_compl_psiSet, ComplexEmbedding.conjugate_coe_eq, ← cmHost_conj_sqrtNegDisc]
    exact congrArg _ τ.2
  · have h := (host_mem_compl_psiSet H τ.1).1 τ.2
    change _ = H.rt0
    rw [ComplexEmbedding.conjugate_coe_eq, h, map_neg, cmHost_conj_sqrtNegDisc, neg_neg]

theorem card_psiSet (H : Host E) : Nat.card (psiSet H) = Module.finrank ℚ E / 2 := by
  have h1 := Set.ncard_add_ncard_compl (psiSet H)
  have h2 := card_psiSet_eq_card_compl H
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h2
  rw [Nat.card_eq_fintype_card, Embeddings.card E ℂ] at h1
  rw [Nat.card_coe_set_eq]
  omega

variable {H : Host E} {l : Level H}

theorem labK_eq_iff (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (τ : E →+* ℂ) (a : E) (x : c.F) :
    labK c K τ a = algebraMap c.F K x ↔ τ a = (x : ℂ) := by
  change algebraMap c.F K (Formalism.L2.Pj.embF c τ a) = _ ↔ _
  rw [(algebraMap c.F K).injective.eq_iff, Subtype.ext_iff]
  rfl

theorem labK_injective (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] : Function.Injective (labK c K) := by
  intro τ τ' h
  refine RingHom.ext fun a => ?_
  exact (labK_eq_iff c K τ a (Formalism.L2.Pj.embF c τ' a)).1 (DFunLike.congr_fun h a)

theorem labK_bijective (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] :
    Function.Bijective (labK c K) := by
  have : Finite (E →+* K) := Finite.of_equiv _ (RingHom.equivRatAlgHom E K).symm
  refine (labK_injective c K).bijective_of_nat_card_le ?_
  rw [Nat.card_eq_fintype_card (α := E →+* ℂ), Embeddings.card E ℂ]
  exact card_ringHom_le_finrank

end

theorem labK_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K], Function.Bijective (labK c K) ∧ Splits E K ∧ (∀ τ, ∃ t : 𝓞 E →+* 𝓞 K, ∀ a : 𝓞 E, (t a : K) = labK c K τ (a : E)) ∧ ∃ ρ : 𝓞 K, ρ ^ 2 = -(H.d : 𝓞 K) ∧ (∀ τ, τ ∈ psiSet H ↔ labK c K τ (H.rt : E) = (ρ : K)) ∧ (∀ τ, τ ∈ (psiSet H)ᶜ ↔ labK c K τ (H.rt : E) = ((-ρ : 𝓞 K) : K)) ∧ Nat.card (psiSet H) = Module.finrank ℚ E / 2 ∧ Nat.card ((psiSet H)ᶜ : Set (E →+* ℂ)) = Module.finrank ℚ E / 2 := by
  intro E _ _ _ H l c K _ _ _
  have hb := labK_bijective c K
  refine ⟨hb, ?_, fun τ => ⟨RingOfIntegers.mapRingHom (labK c K τ), fun a => rfl⟩, ?_⟩
  · rw [splits_iff_card, ← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Embeddings.card E ℂ]
  let r : c.F := ⟨H.rt0, c.le (baseKA l).ρ.2⟩
  have hr : r ^ 2 = -(H.d : c.F) := Subtype.ext (by simpa [r] using H.sqrt_neg_disc_sq)
  have hK : (algebraMap c.F K r) ^ 2 = -(H.d : K) := by
    rw [← map_pow, hr]; simp
  have hint : IsIntegral ℤ (algebraMap c.F K r) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hK]
    exact (isIntegral_natCast H.d).neg
  obtain ⟨ρ, hρ⟩ : ∃ ρ : 𝓞 K, algebraMap (𝓞 K) K ρ = algebraMap c.F K r := ⟨⟨_, hint⟩, rfl⟩
  refine ⟨ρ, RingOfIntegers.ext ?_, fun τ => ?_, fun τ => ?_, card_psiSet H, ?_⟩
  · change algebraMap (𝓞 K) K (_ ^ 2) = algebraMap (𝓞 K) K (-_)
    rw [map_pow, map_neg, map_natCast, hρ]
    exact hK
  · change _ ↔ _ = algebraMap (𝓞 K) K ρ
    rw [hρ]
    exact (labK_eq_iff c K τ _ r).symm
  · rw [host_mem_compl_psiSet]
    have := (labK_eq_iff c K τ (H.rt : E) (-r)).symm
    rw [map_neg, ← hρ, ← map_neg] at this
    exact this
  · rw [← card_psiSet_eq_card_compl, card_psiSet]

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIntegralLevelMulKappa
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn
open scoped Matrix

namespace GlobalTheory.TransvModel

theorem herm_smul_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r) (S : Set E)
    (hΛ : X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ S, ∃ u ∈ X.L', v = a • u}) {v : Fin r → E} (hv : v ∈ X.L')
    {x : Fin r → E} (hx : x ∈ X.Λ) : FD.herm X.Gm x v • v ∈ X.Λ := by
  rw [hΛ] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, u, hu, rfl⟩ := hx
    rw [GlobalTheory.TransvLevel.herm_smul_left, mul_smul, hΛ]
    exact Submodule.subset_span ⟨a, ha, _, GlobalTheory.FlagData.smul_mem_of_isIntegral _ (X.L'_int u hu v hv) hv, rfl⟩
  | zero => simp [FD.herm]
  | add x y _ _ hx hy =>
    have : FD.herm X.Gm (x + y) v = FD.herm X.Gm x v + FD.herm X.Gm y v := (X.toData.hermL v).map_add x y
    rw [this, add_smul]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [← algebraMap_smul E c x, GlobalTheory.TransvLevel.herm_smul_left, mul_smul, algebraMap_smul]
    exact Submodule.smul_mem _ c hx

theorem transv_mem_of_span {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r) (S : Set E)
    (hΛ : X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ S, ∃ u ∈ X.L', v = a • u}) (m : ℕ)
    (hmκ : IsIntegral ℤ ((m : E) * X.κ0)) (v : Fin r → E) (hv : v ∈ X.L') (hiso : FD.herm X.Gm v v = 0) (b : E)
    (hb : cc b = b) (hbi : IsIntegral ℤ b) :
    ∃ γ ∈ X.Γ, ∀ τ : X.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 =
      X.flowMat v τ ((((X.g * m : ℕ) : ℝ) : ℂ) * τ.1 b) := by
  have hξ' : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
  have hκc : IsCMField.complexConj E X.κ0 = -X.κ0 := by
    rcases X.κ0_xi with h | h <;> simp [h, hξ', map_ofNat]
  have hb' : IsCMField.complexConj E b = b := hb
  set α : E := ((X.g * m : ℕ) : E) * b * X.κ0 with hαdef
  have hα : cc α = -α := by
    simp [hαdef, cc, hb', hκc]
  have key : ∀ x ∈ X.Λ, (b * ((m : E) * X.κ0)) • (FD.herm X.Gm x v • v) ∈ X.Λ := fun x hx =>
    GlobalTheory.FlagData.smul_mem_of_isIntegral _ (hbi.mul hmκ) (herm_smul_mem X S hΛ hv hx)
  have e : ∀ x, (α * FD.herm X.Gm x v) • v =
      (X.g : E) • ((b * ((m : E) * X.κ0)) • (FD.herm X.Gm x v • v)) := by
    intro x
    rw [smul_smul, smul_smul, hαdef]
    congr 1
    push_cast
    ring
  have key' : ∀ x ∈ X.Λ, (α * FD.herm X.Gm x v) • v ∈ X.Λ := fun x hx => by
    rw [e]
    exact GlobalTheory.FlagData.smul_mem_of_isIntegral _ (isIntegral_natCast _) (key x hx)
  refine ⟨GlobalTheory.FlagData.transv X.Gm hiso α, X.cong _
    ⟨GlobalTheory.FlagData.herm_transvMat X.Gm_herm hiso hα, fun x => ?_⟩ (fun x hx => ?_), fun τ => ?_⟩
  · change x ∈ X.Λ ↔ transvMat X.Gm v α *ᵥ x ∈ X.Λ
    rw [GlobalTheory.FlagData.transvMat_mulVec]
    refine ⟨fun hx => Submodule.add_mem _ hx (key' x hx), fun hx => ?_⟩
    have h := key' _ hx
    rw [GlobalTheory.FlagData.herm_add_smul_left, hiso, mul_zero, add_zero] at h
    simpa using Submodule.sub_mem _ hx h
  · refine ⟨_, key x hx, ?_⟩
    change transvMat X.Gm v α *ᵥ x - x = _
    rw [GlobalTheory.FlagData.transvMat_mulVec, add_sub_cancel_left, e]
  · change (transvMat X.Gm v α).map τ.1 = _
    refine TransvectionPeriodicity.transvMat_map X.toData v τ α _ ?_
    rw [hαdef, map_mul, map_mul, TransvectionPeriodicity.emb_kappa X.toData τ, map_natCast]
    push_cast
    ring

theorem xiR_eq (D : D7) : xiR D = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := by
  have e1 : D.host.φ₀ D.host.xi0 =
      -1 / ((Ideal.absNorm D.host.ccK : ℂ) * D.host.φ₀ D.host.sqrtMinusD) := by
    unfold Formalism.BasicNotions.Host.xi0; simp [map_div₀, map_mul, map_neg, map_natCast]
  have e2 : ‖D.host.φ₀ D.host.sqrtMinusD‖ = Real.sqrt D.host.d := by
    have h0 : (D.host.φ₀ D.host.sqrtMinusD) ^ 2 = -(D.host.d : ℂ) := by
      rw [← map_pow, Formalism.BasicNotions.Host.sqrtMinusD_sq D.host, map_neg, map_natCast]
    rw [← Real.sqrt_sq (norm_nonneg (D.host.φ₀ D.host.sqrtMinusD)), ← norm_pow, h0, norm_neg,
      Complex.norm_natCast]
  unfold xiR; rw [e1, norm_div, norm_neg, norm_one, norm_mul, Complex.norm_natCast, e2]

theorem isIntegral_level_mul_kappa {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : FD.Data E r)
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d) (τ : E →+* ℂ) (hτ : ‖τ X.ξ0‖ = 1 / ((N : ℝ) * Real.sqrt d)) :
    IsIntegral ℤ (((N * d : ℕ) : E) * X.κ0) := by
  have h1 : τ (cc X.ξ0) = (starRingEnd ℂ) (τ X.ξ0) := IsCMField.complexEmbedding_complexConj E τ X.ξ0
  rw [X.ξ0_im, map_neg] at h1
  have h2 := Complex.mul_conj' (τ X.ξ0)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h3 : ‖τ X.ξ0‖ ^ 2 * ((N : ℝ) ^ 2 * d) = 1 := by
    rw [hτ, div_pow, mul_pow, Real.sq_sqrt hd'.le]
    field_simp
  have h4 : ((‖τ X.ξ0‖ : ℝ) : ℂ) ^ 2 * ((N : ℂ) ^ 2 * d) = 1 := by exact_mod_cast h3
  rw [← h1] at h2
  have h5 : X.κ0 ^ 2 = 4 * X.ξ0 ^ 2 := by
    rcases X.κ0_xi with h | h <;> rw [h] <;> ring
  have h6 : (((N * d : ℕ) : E) * X.κ0) ^ 2 = ((-(4 * d : ℤ) : ℤ) : E) := by
    apply τ.injective
    rw [mul_pow, h5, map_mul, map_mul, map_pow, map_pow, map_natCast, map_intCast, map_ofNat]
    push_cast
    linear_combination (-4 * (N : ℂ) ^ 2 * (d : ℂ) ^ 2) * h2 - 4 * (d : ℂ) * h4
  refine IsIntegral.of_pow two_pos ?_
  rw [h6]
  exact isIntegral_algebraMap (R := ℤ)

theorem transv_model : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ), InR D j → ∀ (k : (T.U j T.σ₀).Comp) (Xx : DataX D.host.E D.R.r), Xx.toData = ((T.U j T.σ₀).X k) → Xx.g = T.Q.l.M → Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} → ((D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK * D.host.d : ℕ) : ℝ) * Xx.k0 = 2 * (D.host.g 0 * D.host.g 1 : ℕ) * Real.sqrt D.host.d ∧ ∀ v ∈ Xx.L', FD.herm ((T.U j T.σ₀).X k).Gm v v = 0 → ∀ b : D.host.E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ ((T.U j T.σ₀).X k).Γ, ∀ τ : ((T.U j T.σ₀).X k).Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = ((T.U j T.σ₀).X k).flowMat v τ ((((D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK * D.host.d : ℕ) : ℝ) : ℂ) * τ.1 b) := by
  intro D T h j hj k Xx hX hg hΛ
  have hM : Xx.g = D.host.g 0 * D.host.g 1 := hg.trans h.pins.2.1.1
  have hN : 0 < Ideal.absNorm D.host.ccK :=
    Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hd : 0 < D.host.d := by have := D.host.qd_big.2; omega
  have habs : ∀ τ : D.host.E →+* ℂ,
      ‖τ Xx.ξ0‖ = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := fun τ => by
    rw [← xiR_eq, ← h.xiAbs j hj T.σ₀ T.good_σ₀ k τ, ← hX]
  rw [← hX]
  refine ⟨?_, fun v hv hiso b hb hbi => ?_⟩
  · obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ Xx.Ψ := by
      by_cases h0 : D.host.φ₀ ∈ Xx.Ψ
      · exact ⟨_, h0⟩
      · by_contra hc
        exact h0 ((Xx.cmType _).2 fun h1 => hc ⟨_, h1⟩)
    have h1 := Xx.ξ0_abs ⟨τ, hτ⟩
    rw [habs] at h1
    have hN' : (0 : ℝ) < Ideal.absNorm D.host.ccK := by exact_mod_cast hN
    have hd' : (0 : ℝ) < D.host.d := by exact_mod_cast hd
    have hs := Real.sqrt_pos.2 hd'
    have hk : Xx.k0 = 2 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := by
      rw [div_eq_mul_one_div, h1]; ring
    have hss := Real.mul_self_sqrt hd'.le
    rw [hk]
    push_cast
    field_simp
    linear_combination (-((D.host.g 0 : ℝ) * D.host.g 1)) * hss
  · have := transv_mem_of_span Xx (D.host.AA : Set D.host.E) hΛ (Ideal.absNorm D.host.ccK * D.host.d)
      (isIntegral_level_mul_kappa Xx.toData hN hd D.host.φ₀ (habs _)) v hv hiso b hb hbi
    rwa [hM, ← mul_assoc] at this

end GlobalTheory.TransvModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEllipticCurvePolarisedLatticeFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEllipticCurvePolarisedLatticeFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem exists_polAV_latticeFamily : ThetaUnifAV → Out.PolBaseChangeSt → (∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ → ∃ (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (Lf : (R →+* ℂ) → PeriodPair), (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : R →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (Lf s').lattice ↔ z • w' ∈ u'.Λ)) ∧ ∀ s : R →+* ℂ, s W.c₄ = 12 * (Lf s).g₂ ∧ s W.c₆ = 216 * (Lf s).g₃ ∧ s W.Δ = (Lf s).g₂ ^ 3 - 27 * (Lf s).g₃ ^ 2) := by
  intro hU hB R _ W hΔ
  obtain ⟨P, v, hg, hv, hbc, hs⟩ := GlobalTheory.T.exists_polarisedAbelianScheme_lieBasis_invariants R W hΔ
  have hex : ∀ s : R →+* ℂ, ∃ L : PeriodPair, s W.c₄ = 12 * L.g₂ ∧ s W.c₆ = 216 * L.g₃ ∧
      s W.Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := fun s => by
    obtain ⟨P', φ, h⟩ := exists_isPolFibre hB s P
    obtain ⟨v', hv', -⟩ := existsUnique_isVecOver h.2.1.1 v
    obtain ⟨rig, hrig⟩ := P'.rigid
    obtain ⟨u, Hm, χ, -, -, -, hd, -⟩ := hU P' rig hrig
    obtain ⟨w, hw, -⟩ := hd v' (hv'.isTangent h.2.1 (hv.1 0))
    obtain ⟨-, L, -, hL⟩ := hs s P' φ v' u w h hv' hw
    exact ⟨L, hL⟩
  choose Lf hLf using hex
  refine ⟨P, v, Lf, ⟨hg, hv, hbc, fun s P' φ v' u w h hv' hw => ?_⟩, hLf⟩
  obtain ⟨hw0, L, hL, h4, h6, -⟩ := hs s P' φ v' u w h hv' hw
  have e : (Lf s).lattice = L.lattice :=
    lattice_eq_of_g₂_eq_of_g₃_eq
      (mul_left_cancel₀ (by norm_num : (12 : ℂ) ≠ 0) ((hLf s).1.symm.trans h4))
      (mul_left_cancel₀ (by norm_num : (216 : ℂ) ≠ 0) ((hLf s).2.1.symm.trans h6))
  exact ⟨hw0, fun z => e ▸ hL z⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEllipticCurvePolarisedLatticeFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve
open scoped CategoryTheory.Obj UpperHalfPlane
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ellipticCurve_polarised_lattice_family : ThetaUnifAV → Out.PolBaseChangeSt → (∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ → ∃ (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (Lf : (R →+* ℂ) → PeriodPair), (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : R →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (Lf s').lattice ↔ z • w' ∈ u'.Λ)) ∧ ∀ s : R →+* ℂ, s W.c₄ = 12 * (Lf s).g₂ ∧ s W.c₆ = 216 * (Lf s).g₃ ∧ s W.Δ = (Lf s).g₂ ^ 3 - 27 * (Lf s).g₃ ^ 2) := by
  first | exact @GlobalTheory.exists_polAV_latticeFamily | exact GlobalTheory.exists_polAV_latticeFamily | (intros; apply GlobalTheory.exists_polAV_latticeFamily <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FormEqPiMulHermForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.CM.LieMetric

theorem form_eq_sum_sum {K : Type} [Field K] {g : ℕ} (h : HermFam K (Fin g → K)) (s : K →+* ℂ) (x y : Fin g → K) :
    h.form s x y = ∑ j, ∑ i, s (y j) * star (s (x i)) * h.form s (Pi.single i 1) (Pi.single j 1) := by
  rw [form_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h.conj_symm, form_sum_right, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, h.conj_symm, _root_.mul_assoc]
  rfl

theorem hermForm_sum_sum {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a b : Fin n → ℂ) (X : Fin n → Fin g → ℂ) :
    hermForm Hm (∑ j, a j • X j) (∑ i, b i • X i) = ∑ j, ∑ i, a j * star (b i) * hermForm Hm (X j) (X i) := by
  simp only [hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem form_eq_pi_mul_hermForm : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (s : K →+* ℂ) (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ F.P₀.A.left) (u : HolUnif Q.A Q.L Q.g) (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ), IsPolFibre s F.P₀ Q ψ → u.IsAH Hm χ → ∀ (c c' : Fin F.P₀.g → K) (w w' : epsR K ⟶ F.P₀.A) (v v' : epsR ℂ ⟶ Q.A) (W W' : Fin Q.g → ℂ), IsLieComb c F.v w → IsLieComb c' F.v w' → IsVecOver s ψ w v → IsVecOver s ψ w' v' → u.IsDiff W v → u.IsDiff W' v' → h.form s c c' = Real.pi * hermForm Hm W' W := by
  intro hU _ K _ _ P F h H s Q ψ u Hm χ hQ hA c c' w w' v v' W W' hw hw' hv hv' hW hW'
  obtain ⟨Q₀, ψ₀, v₀, u₀, Hm₀, χ₀, W₀, a₀, b₀, c₀, d₀⟩ := H s
  obtain ⟨-, -, -, -, t1, -, -⟩ := AHWeil.tangent_and_weil_of_isAH hU Q _ u Hm χ hA
  choose x hx using fun i => (existsUnique_isVecOver hQ.2.1.1 (F.v i)).exists
  have hxt : ∀ i, IsTangent (x i) := fun i => (hx i).isTangent hQ.2.1 (F.basis.1 i)
  choose X hX using fun i => (t1 _ (hxt i)).exists
  have key : ∀ (c : Fin F.P₀.g → K) (w : epsR K ⟶ F.P₀.A) (v : epsR ℂ ⟶ Q.A) (W : Fin Q.g → ℂ), IsLieComb c F.v w →
      IsVecOver s ψ w v → u.IsDiff W v → W = ∑ i, s (c i) • X i := fun c w v W hw hv hW => by
    have h1 := (lieComb_baseChange K ℂ s _ _ ψ hQ.2.1 _ F.v w c x v hx hw).1 hv
    have h3 : IsTangent v := by
      rw [(Chart.isLieComb_iff _ x v).1 h1, ← Chart.isTan_iff]
      refine List.prod_induction Chart.IsTan (fun a b ha hb => Chart.isTan_mul ha hb) Chart.isTan_one ?_
      intro a ha
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 ha
      exact Chart.isTan_scale (s (c i)) ((Chart.isTan_iff _).2 (hxt i))
    exact (t1 v h3).unique hW (UnifDifferential.isDiff_of_isLieComb _ _ _ _ u X x _ v hxt hX h1)
  rw [key c w v W hw hv hW, key c' w' v' W' hw' hv' hW', hermForm_sum_sum, form_eq_sum_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [d₀, hermForm_eq hU a₀ hQ b₀ hA F.basis.1 c₀ (fun i => ⟨hx i, hX i⟩)]
  ring

end GlobalTheory.CM.LieMetric
end
end

module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStepFactorRatioUnitGaussSumQuotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleIntegralsNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPlaneSplitHermitianLatticeSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianSelfDualLatticeHyperbolicPlaneSplit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuRatioValuesRootsOfUnity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem chrEq_pow' {D : D7} {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) (a : ℕ) :
    ChrEq (c ^ a) (χ ^ a) := by
  refine ⟨⟨?_, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · have : ((c ^ a : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => c x ^ a := by
      funext x; simp
    rw [this]
    exact h.1.1.pow a
  · have h1 := h.1.2 x
    simp only [MonoidHom.pow_apply, h1, one_pow]
  · have hp : (χ ^ a).locK P k = χ.locK P k ^ a := by
      have : ∀ x, (χ ^ a).1 x = χ.1 x ^ a := fun x => by rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]
      exact this _
    rw [MonoidHom.pow_apply, hp, Units.val_pow_eq_pow_val, ← h.2 P e he k x hx]
    exact map_pow Circle.coeHom _ _

private theorem exists_prime_power_pow_eq_one {D : D7} {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) {n : ℕ}
    (hn : χ.OrderDvd n) : c ^ n = 1 := by
  have h1 := chrEq_pow' h n
  rw [show χ ^ n = 1 from hn] at h1
  exact MonoidHom.ext fun x => GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 x

theorem _root_.GlobalTheory.T.squareNu_ratio_values_roots_of_unity : GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ →
    ∀ (i j : Fin D.R.m) (t : T) (k : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))ˣ), ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧
      (((GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) = D.what₂.embLL ζ := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D _ _ _ _ T Lc μ₀ hL G W S hN i j t k => ?_⟩⟩
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have hc1 : Lc.xi μ₀ k = 1 := GlobalTheory.ChrEqUnique.eq_one_of_chrEq (hL.xi_base ▸ hL.xi μ₀) k
  have e : (GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k = Lc.xi t k := by
    have key : ∀ {Γ : Type} [CommGroup Γ] (a x y e c : Γ), y = 1 → (a * x * e / (c * e)) / (a * y * e / (c * e)) = x := by
      intro Γ _ a x y e c hy
      subst hy
      rw [mul_one, div_div_div_cancel_right, mul_div_mul_right_eq_div, mul_div_cancel_left]
    exact key (Lc.mu0 ((j : ℕ) + 1) k) (Lc.xi t k) (Lc.xi μ₀ k) ((Lc.eta ^ (rankV D i j % 2)) k) (G.ch.chi (D.R.m - i) k) hc1
  obtain ⟨y, hy⟩ := GlobalTheory.Adopt.heckeCharacter_finiteOrder_values_in_field D (Lc.xi t) (Lc.xiH t) n _ D.what₂.embLL (hL.xi t) hn ho ((hN.chars.xi t).valuesIn) k
  have h1 : ((Lc.xi t k : Circle) : ℂ) ^ n = 1 := by
    have := DFunLike.congr_fun (exists_prime_power_pow_eq_one (hL.xi t) ho) k
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this
    exact (map_pow Circle.coeHom _ _).symm.trans (congrArg _ this)
  have hyn : (y : D.what₂.LL) ^ n = 1 := D.what₂.embLL.injective (by rw [map_pow, hy, h1, map_one])
  exact ⟨y, GlobalTheory.KappaArith.isAwayUnit_of_pow_eq_one _ hn hyn, by rw [e, hy]⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedHyperbolicPlaneRescaleRebasis
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.adaptedHyperbolicPlane_rescale_rebasis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (B₀ B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E), B.emb = B₀.emb → ∀ (n n₁ : ℕ) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n₁)
    (H₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane E n n₁) (i₀ i₁ : ℕ), i₀ < i₁ → i₁ < n → Y.L.IsFullLattice E → Y₁.L.IsFullLattice E →
    H₀.IsAdapted σ B₀ Y Y₁ i₀ i₁ → ∃ (Y' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n₁) (H : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane E n n₁),
      Y'.θ = Y.θ ∧ Y₁'.θ = Y₁.θ ∧ (∀ v : B.P, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y.L (Y'.bas v)) ∧
      (∀ v : B.P, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y₁.L (Y₁'.bas v)) ∧
      H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') (GlobalTheory.ThK.reS Y₁ Y₁') i₀ i₁ := by
  intro F E _ _ _ _ _ σ hcm B₀ B hemb n n₁ Y Y₁ H₀ i₀ i₁ h01 h1n hL hL₁ hH
  classical
  have hss : ∀ a : E, σ (σ a) = a := fun a => by
    let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
    apply τ.injective
    rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]
  have fsl : ∀ (J : Matrix (Fin n) (Fin n) E) (s : E) (a b : Fin n → E),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (s • a) b = s * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J a b := fun J s a b => by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, smul_dotProduct]
  have fsr : ∀ (J : Matrix (Fin n) (Fin n) E) (s : E) (a b : Fin n → E),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J b (s • a) = σ s * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J b a := fun J s a b => by
    have : (fun i => σ ((s • a) i)) = σ s • fun i => σ (a i) := funext fun i => by simp
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have hx0 : H₀.x ≠ 0 := by
    intro h; have := hH.xy; rw [h] at this; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form] at this
  have hy0 : H₀.y ≠ 0 := by
    intro h
    have h1 := hH.xy
    have h2 := fsr Y.J 0 H₀.y H₀.x
    rw [zero_smul, map_zero, zero_mul, ← h, h1] at h2
    exact one_ne_zero h2
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.PlaneSkewScale.exists_rescale_primAt F E σ hcm n Y.L hL H₀.x H₀.y hx0 hy0 B.P B.τ
  have hσc : σ c ≠ 0 := fun h => hc0 (by rw [← hss c, h, map_zero])
  set x : Fin n → E := c • H₀.x with hxdef
  set y : Fin n → E := (σ c)⁻¹ • H₀.y with hydef
  have ex : ∀ s : E, (s * c⁻¹) • x = s • H₀.x := fun s => by
    rw [hxdef, smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
  have ey : ∀ t : E, (t * σ c) • y = t • H₀.y := fun t => by
    rw [hydef, smul_smul, mul_assoc, mul_inv_cancel₀ hσc, mul_one]
  let 𝔟 : FractionalIdeal (𝓞 E)⁰ E := FractionalIdeal.spanSingleton _ c⁻¹ * H₀.𝔟
  have h𝔟 : ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ Y.L := by
    intro s
    rw [FractionalIdeal.mem_singleton_mul, hxdef, smul_smul]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [mul_comm c⁻¹ t, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
      exact (hH.ideal t).1 ht
    · intro h
      refine ⟨s * c, (hH.ideal _).2 h, ?_⟩
      rw [mul_comm s c, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hsplit : ∀ z ∈ Y.L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ Y.L ∧ t • y ∈ Y.L ∧ u ∈ Y₁.L ∧
      z = s • x + H₀.ι *ᵥ u + t • y := by
    intro z hz
    obtain ⟨s, t, u, hs, ht, hu, rfl⟩ := hH.split z hz
    exact ⟨s * c⁻¹, t * σ c, u, by rw [ex]; exact hs, by rw [ey]; exact ht, hu, by rw [ex, ey]⟩
  haveI : Y₁.L.IsFullLattice E := hL₁
  have hcomap : Y.L.comap ((Matrix.mulVecLin H₀.ι).restrictScalars (𝓞 E)) = Y₁.L :=
    Submodule.ext fun u => (hH.low u).symm
  have hb₁ : ∀ v : B.P, ∃ β, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y₁.L β := fun v =>
    GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) Y₁.L hcm
  choose β₁ hβ₁ using hb₁
  let bas₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GL (Fin n₁) (Fv F v) := fun v => if h : v ∈ B.P then β₁ ⟨v, h⟩ else Y₁.bas v
  have hbas₁ : ∀ v : B.P, bas₁ v = β₁ v := fun v => by simp only [bas₁, dif_pos v.2]
  have hb : ∀ v : B.P, ∃ β : GL (Fin n) (Fv F v), (∀ i : Fin n, (i.1 = i₀ → ∀ r, β.1 r i = B.τ v (x r)) ∧
      (i.1 = i₁ → ∀ r, β.1 r i = B.τ v (y r)) ∧
      ∀ j : Fin n₁, i.1 = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.skip i₀ i₁ j → ∀ r, β.1 r i = (H₀.ι.map (B.τ v) * (β₁ v).1) r j) ∧
      GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y.L β := fun v =>
    GlobalTheory.PlaneBasis.exists_isSplitBasis_plane F E σ hcm v (B.τ v) n n₁ Y.L x y H₀.ι (β₁ v) i₀ i₁ hH.rank h01 h1n hL
      (fun z hz => by
        obtain ⟨s, t, u, hs, ht, hu, hz'⟩ := hsplit z hz
        exact ⟨s, t, u, hs, ht, (hH.low u).1 hu, hz'⟩)
      (by simp only [GlobalTheory.AdelicU.valued_apply_eq_valuation]; exact (hc v).1)
      (by simp only [GlobalTheory.AdelicU.valued_apply_eq_valuation]; exact (hc v).2)
      (by rw [hcomap]; exact hβ₁ v)
  choose β hβ using hb
  let bas : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GL (Fin n) (Fv F v) := fun v => if h : v ∈ B.P then β ⟨v, h⟩ else Y.bas v
  have hbas : ∀ v : B.P, bas v = β v := fun v => by simp only [bas, dif_pos v.2]
  let Y' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n := ⟨Y.J, Y.L, Y.θ, bas⟩
  let Y₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n₁ := ⟨Y₁.J, Y₁.L, Y₁.θ, bas₁⟩
  refine ⟨Y', Y₁', ⟨x, y, H₀.ι, 𝔟⟩, rfl, rfl, fun v => ?_, fun v => ?_, ?_⟩
  · rw [show Y'.bas v = β v from hbas v]; exact (hβ v).2
  · rw [show Y₁'.bas v = β₁ v from hbas₁ v]; exact hβ₁ v
  · exact
      { rank := hH.rank
        xx := by
          show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J x x = 0
          rw [hxdef, fsl, fsr, hH.xx, mul_zero, mul_zero]
        yy := by
          show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J y y = 0
          rw [hydef, fsl, fsr, hH.yy, mul_zero, mul_zero]
        xy := by
          show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J x y = 1
          rw [hxdef, hydef, fsl, fsr, hH.xy, map_inv₀, hss, mul_one, mul_inv_cancel₀ hc0]
        orth := fun u => by
          show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J (H₀.ι *ᵥ u) x = 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J (H₀.ι *ᵥ u) y = 0
          rw [hxdef, hydef, fsr, fsr, (hH.orth u).1, (hH.orth u).2, mul_zero, mul_zero]
          exact ⟨rfl, rfl⟩
        gram := hH.gram
        low := hH.low
        split := hsplit
        ideal := h𝔟
        cartan := fun w => by
          obtain ⟨hθι, c₀, hc₀, he⟩ := hH.cartan w
          rw [hemb]
          refine ⟨hθι, (B₀.emb w).1 (σ c)⁻¹ * c₀ * ((B₀.emb w).1 c)⁻¹, ?_, ?_⟩
          · have h1 : (B₀.emb w).1 (σ c)⁻¹ ≠ 0 := (map_ne_zero _).2 (inv_ne_zero hσc)
            have h2 : (B₀.emb w).1 c ≠ 0 := (map_ne_zero _).2 hc0
            exact mul_ne_zero (mul_ne_zero h1 hc₀) (inv_ne_zero h2)
          · have h2 : (B₀.emb w).1 c ≠ 0 := (map_ne_zero _).2 hc0
            have hx' : (fun i => (B₀.emb w).1 (x i)) = (B₀.emb w).1 c • fun i => (B₀.emb w).1 (H₀.x i) :=
              funext fun i => by simp [hxdef]
            have hy' : (fun i => (B₀.emb w).1 (y i)) = (B₀.emb w).1 (σ c)⁻¹ • fun i => (B₀.emb w).1 (H₀.y i) :=
              funext fun i => by simp [hydef]
            show (fun i => (B₀.emb w).1 (y i)) = _ • Y.θ w *ᵥ fun i => (B₀.emb w).1 (x i)
            rw [hx', hy', he, Matrix.mulVec_smul, smul_smul, smul_smul]
            congr 1
            field_simp
        bas := fun v i => by
          rw [show (GlobalTheory.ThK.reS Y Y').bas v = β v from hbas v, show (GlobalTheory.ThK.reS Y₁ Y₁').bas v = β₁ v from hbas₁ v]
          exact (hβ v).1 i }

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualOrientedModelConjugateHermitian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexBoundAll
open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB

namespace GlobalTheory.IdxAll

theorem eq_or_eq_comp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) (e τ : E →+* ℂ) (heτ : e.comp (algebraMap F E) = τ.comp (algebraMap F E)) :
    τ = e ∨ ∀ x, τ x = star (e x) := by
  obtain ⟨-, hc, h2, hσ⟩ := h
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  obtain ⟨g, hg⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := F) e τ heτ
  have hσσ : ∀ x, σ (σ x) = x := fun x => e.injective (by rw [hσ, hσ, star_star])
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσσ) (AlgHom.ext hσσ)
  have hs : s ≠ 1 := by
    intro h1
    refine IsTotallyComplex.complexEmbedding_not_isReal e ?_
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have : σ x = x := congrArg (fun t : E ≃ₐ[F] E => t x) h1
    have h3 := hσ e x
    rw [this] at h3
    exact h3.symm
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  by_cases hg1 : g.symm = 1
  · left
    rw [← hg, hg1]
    rfl
  · right
    intro x
    rw [← hg, (hy _ hg1).trans (hy _ hs).symm]
    exact hσ e x

end GlobalTheory.IdxAll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualOrientedModelConjugateHermitian
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjSpace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc HasSig)
open scoped Matrix

variable {D : D7}

def cO (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E := NumberField.RingOfIntegers.mapRingHom (starRingEnd D.host.E)

instance surj_cO : RingHomSurjective (cO D) :=
  ⟨fun o => ⟨cO D o, by ext; simp [cO]⟩⟩

instance surj_star : RingHomSurjective (starRingEnd D.host.E) :=
  ⟨fun o => ⟨star o, by rw [starRingEnd_apply, star_star]⟩⟩

def cvO (D : D7) (n : ℕ) : (Fin n → D.host.E) →ₛₗ[cO D] (Fin n → D.host.E) where
  toFun z i := star (z i)
  map_add' x y := by ext i; simp
  map_smul' o z := by
    ext i
    simp only [Pi.smul_apply, cO]
    rw [Algebra.smul_def, Algebra.smul_def]
    simp only [smul_eq_mul, star_mul', mul_eq_mul_left_iff, map_mul, Pi.smul_apply]
    first
      | exact Or.inl rfl
      | (simp [mul_comm]; exact Or.inl rfl)

def cvE (D : D7) (n : ℕ) : (Fin n → D.host.E) →ₛₗ[starRingEnd D.host.E] (Fin n → D.host.E) where
  toFun z i := star (z i)
  map_add' x y := by ext i; simp
  map_smul' o z := by
    funext i
    show star (o * z i) = star o * star (z i)
    exact star_mul' _ _

def conjLat {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
  L.map (cvO D n)

theorem mem_conjLat {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (z : Fin n → D.host.E) :
    z ∈ conjLat L ↔ (fun i => star (z i)) ∈ L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : (fun i => star ((cvO D n) y i)) = y := by ext i; simp [cvO]
    rw [e]; exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    ext i; simp [cvO]

theorem isLattice_conjLat {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hL : L.IsLattice D.host.E) :
    (conjLat L).IsLattice D.host.E := by
  exact Submodule.IsLattice.of_fg D.host.E (hL.fg.map _)

theorem isIntegral_star_iff (a : D.host.E) : IsIntegral ℤ (star a) ↔ IsIntegral ℤ a := by
  constructor
  · intro h
    have := map_isIntegral_int (starRingEnd D.host.E) h
    rwa [starRingEnd_apply, star_star] at this
  · intro h
    exact map_isIntegral_int (starRingEnd D.host.E) h

theorem form_conj {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (hJ : ∀ i j, D.sp.cm.sig (J j i) = J i j)
    (a b : Fin n → D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig J (fun i => star (a i)) b =
      star (∑ i, ∑ j, star (star (b i)) * J i j * a j) := by
  have hs : ∀ i j, star (J i j) = J j i := fun i j => hJ j i
  have hσ : ∀ x, D.sp.cm.sig x = star x := fun _ => rfl
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, hσ, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, hs, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable {B : Base D.host.F D.host.E} {n r s : ℕ} {V : Spc D.host.F D.host.E n}

theorem mem_conjLat_iff (hV : V.IsHerm D.sp.cm.sig B r s) (z : Fin n → D.host.E) :
    z ∈ conjLat V.L ↔ ∀ x ∈ conjLat V.L, IsIntegral ℤ (∑ i, ∑ j, star (x i) * V.J i j * z j) := by
  rw [mem_conjLat, hV.dual]
  constructor
  · intro h x hx
    rw [mem_conjLat] at hx
    have h1 := h _ hx
    rw [form_conj V.J hV.herm] at h1
    simpa only [star_star, isIntegral_star_iff] using h1
  · intro h y hy
    have hx : (fun i => star (y i)) ∈ conjLat V.L := by
      rw [mem_conjLat]; simpa only [star_star] using hy
    have h1 := h _ hx
    rw [form_conj V.J hV.herm, isIntegral_star_iff]
    exact h1

theorem sesq_herm (hV : V.IsHerm D.sp.cm.sig B r s) : (GlobalTheory.WeilSchrodinger.sesq D V.J).IsSymm := by
  have hs : ∀ i j, star (V.J i j) = V.J j i := fun i j => hV.herm j i
  refine ⟨fun x y => ?_⟩
  simp only [GlobalTheory.WeilSchrodingerHerm.sesq_apply, starRingEnd_apply, dotProduct, Matrix.mulVec, star_sum, star_mul',
    star_star, Pi.star_apply, hs, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem sesq_nondeg (hV : V.IsHerm D.sp.cm.sig B r s) : (GlobalTheory.WeilSchrodinger.sesq D V.J).Nondegenerate := by
  have hdet : V.J.det ≠ 0 := GlobalTheory.WeilSchrodingerHerm.det_J_ne_zero D B V hV
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have h1 : star x ᵥ* V.J = 0 := by
      refine dotProduct_eq_zero _ fun v => ?_
      rw [← Matrix.dotProduct_mulVec, ← GlobalTheory.WeilSchrodingerHerm.sesq_apply]
      exact hx v
    have h2 : star x = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet h1
    simpa using congrArg star h2
  · have h1 : V.J *ᵥ y = 0 := by
      refine dotProduct_eq_zero _ fun v => ?_
      rw [dotProduct_comm]
      have := hy (star v)
      rwa [GlobalTheory.WeilSchrodingerHerm.sesq_apply, star_star] at this
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet h1

theorem sesq_unimod (hV : V.IsHerm D.sp.cm.sig B r s) :
    Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D V.J) (conjLat V.L) := by
  show Formalism.E.hdual _ (conjLat V.L) = conjLat V.L
  ext x
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
  rw [mem_conjLat_iff hV x]
  refine forall₂_congr fun y _ => ?_
  rw [GlobalTheory.WeilSchrodingerHerm.sesq_apply, GlobalTheory.WeilSchrodingerHerm.mem_one_iff]
  have e : star y ⬝ᵥ (V.J *ᵥ x) = ∑ i, ∑ j, star (y i) * V.J i j * x j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]
  rw [e]

theorem hasSig_map_conj {m a b : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (h : HasSig M a b) :
    HasSig (M.map (starRingEnd ℂ)) a b := by
  obtain ⟨hn, A, hA⟩ := h
  refine ⟨hn, A.map star, ?_⟩
  have e1 : (A.map star).map star = A := by ext i j; simp
  have e2 : (A.map star)ᵀ * M.map (starRingEnd ℂ) * A = (Aᵀ * M * A.map star).map (starRingEnd ℂ) := by
    simp only [Matrix.map_mul, Matrix.transpose_map]
    congr 1
    ext i j; simp
  rw [e1, e2, hA, Matrix.fromBlocks_map]
  have e3 : (-1 : Matrix (Fin b) (Fin b) ℂ).map (starRingEnd ℂ) = -1 := by
    ext i j; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  simp [e3]

theorem hasSignature_all (hG : B.IsGood D.sp.cm.sig) {m a b : ℕ} (J : Matrix (Fin m) (Fin m) D.host.E)
    (hs : ∀ w, HasSig (J.map (B.emb w).1) a b) (φ : D.host.E →+* ℂ) : Formalism.UG.HasSignature (J.map φ) a b := by
  have h := hG.cm
  haveI := h.1
  set w := InfinitePlace.mk (φ.comp (algebraMap D.host.F D.host.E)) with hw
  have hreal : ComplexEmbedding.IsReal (φ.comp (algebraMap D.host.F D.host.E)) :=
    IsTotallyReal.complexEmbedding_isReal _
  have he : (B.emb w).1.comp (algebraMap D.host.F D.host.E) = φ.comp (algebraMap D.host.F D.host.E) := by
    rw [(B.emb w).2, hw, InfinitePlace.embedding_mk_eq_of_isReal hreal]
  refine GlobalTheory.FunObj.hasSignature_of_hasSig_conj ?_
  rcases GlobalTheory.IdxAll.eq_or_eq_comp _ h _ _ he with h1 | h1
  · rw [h1]; exact hasSig_map_conj (hs w)
  · have e : (J.map φ).map (starRingEnd ℂ) = J.map (B.emb w).1 := by
      ext i j; simp [h1]
    rw [e]; exact hs w

end GlobalTheory.ConjSpace


open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc) in
theorem GlobalTheory.ConjSpace.main : ∀ (D : D7) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → GlobalTheory.SqStepBig.EmbCM Bs →
    ∀ (n r p : ℕ) (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n), V.IsHerm D.sp.cm.sig Bs r p →
      ∃ (B : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)),
        IsSelfDualC B Λ ∧ NegIdx B p ∧ GlobalTheory.SqStepBig.OverH 1 B Λ V := by
  intro D Bs hG _ n r p V hV
  have hn : r + p = n := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
    exact (hV.sig w).1
  have hgram := GlobalTheory.WeilSchrodinger.gram_hspOf V.J (GlobalTheory.ConjSpace.sesq_herm hV) (GlobalTheory.ConjSpace.sesq_nondeg hV)
    (GlobalTheory.ConjSpace.conjLat V.L) (GlobalTheory.ConjSpace.isLattice_conjLat hV.lat.toIsLattice) (GlobalTheory.ConjSpace.sesq_unimod hV)
    (fun _ => (n - p, p))
  refine ⟨GlobalTheory.WeilSchrodinger.hspOf D V.J (GlobalTheory.ConjSpace.sesq_herm hV) (GlobalTheory.ConjSpace.sesq_nondeg hV)
    (GlobalTheory.ConjSpace.conjLat V.L) (GlobalTheory.ConjSpace.isLattice_conjLat hV.lat.toIsLattice) (GlobalTheory.ConjSpace.sesq_unimod hV)
    (fun _ => (n - p, p)), GlobalTheory.ConjSpace.conjLat V.L, ⟨GlobalTheory.ConjSpace.isLattice_conjLat hV.lat.toIsLattice, fun y => ?_⟩,
    fun τ => ?_, ⟨rfl, ?_, fun y => ?_⟩⟩
  · rw [hgram]
    refine (GlobalTheory.ConjSpace.mem_conjLat_iff (n := n) hV y).trans ?_
    refine forall₂_congr fun x _ => ?_
    exact ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe⟩
  · show Formalism.UG.HasSignature ((HSpace.gram _).map (tauE D τ)) _ p
    rw [hgram]
    have h := GlobalTheory.ConjSpace.hasSignature_all hG V.J hV.sig (tauE D τ)
    have hr : r = n - p := by omega
    rw [hr] at h
    exact h
  · rw [hgram, one_smul]
    rfl
  · refine Iff.symm ((GlobalTheory.ConjSpace.mem_conjLat (n := n) V.L _).trans ?_)
    simp only [star_star]
    exact Iff.rfl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualOrientedModelConjugateHermitianStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_orientedModel_conjugate_hermitian : ∀ (D : D7) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → GlobalTheory.SqStepBig.EmbCM Bs →
    ∀ (n r p : ℕ) (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n), V.IsHerm D.sp.cm.sig Bs r p →
      ∃ (B : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)),
        IsSelfDualC B Λ ∧ NegIdx B p ∧ GlobalTheory.SqStepBig.OverH 1 B Λ V := by
  first | exact @GlobalTheory.ConjSpace.main | exact GlobalTheory.ConjSpace.main | (intros; apply GlobalTheory.ConjSpace.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualOrientedModelScaledSkewHermitian
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SkewOverW

open Matrix GlobalTheory.SkewLat GlobalTheory.SkewLat.DualPair
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (HasSig form)
open scoped nonZeroDivisors

private theorem hasSignature_of_smul {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {κ : ℝ} (hκ : 0 < κ)
    (h : HasSig ((κ : ℂ) • M) r s) : Formalism.UG.HasSignature M r s := by
  refine GlobalTheory.FunObj.hasSignature_of_hasSig_conj ?_
  obtain ⟨h1, A, hA⟩ := h
  refine ⟨h1, ((Real.sqrt κ : ℝ) : ℂ) • A.map star, ?_⟩
  have h2 := congrArg (fun X : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ => X.map (starRingEnd ℂ)) hA
  simp only [Matrix.map_mul] at h2
  have e2 : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).map (starRingEnd ℂ) =
      Matrix.fromBlocks 1 0 0 (-1) := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.one_apply] <;> split_ifs <;> simp
  have hs : ((Real.sqrt κ : ℝ) : ℂ) * ((Real.sqrt κ : ℝ) : ℂ) = (κ : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hκ.le
  have t1 : (((Real.sqrt κ : ℝ) : ℂ) • A.map star)ᵀ = ((Real.sqrt κ : ℝ) : ℂ) • (Aᵀ).map (starRingEnd ℂ) := by
    ext i j; simp
  have t2 : (((Real.sqrt κ : ℝ) : ℂ) • A.map star).map star =
      ((Real.sqrt κ : ℝ) : ℂ) • (A.map star).map (starRingEnd ℂ) := by
    ext i j; simp
  have t3 : ((κ : ℂ) • M).map (starRingEnd ℂ) = (κ : ℂ) • M.map (starRingEnd ℂ) := by
    ext i j; simp
  rw [t3, e2] at h2
  rw [t1, t2, ← h2]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs]

variable {D : D7}

private theorem form_smul {d : ℕ} (J : Matrix (Fin d) (Fin d) D.host.E) (c e : D.host.E) (y x : Fin d → D.host.E) :
    form D.sp.cm.sig J (c • y) (e • x) = c * star e * form D.sp.cm.sig J y x := by
  have hσ : ∀ z : D.host.E, D.sp.cm.sig z = star z := fun _ => rfl
  simp only [form, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul, hσ, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem mem_lat {d : ℕ} {L : Submodule (𝓞 D.host.E) (Fin d → D.host.E)} {y : Fin d → D.host.E} :
    y ∈ scLat D.host.AA⁻¹ L ↔ ∀ c ∈ D.host.AA, c • y ∈ L := by
  rw [mem_scLat, inv_inv]

private theorem smul_mem_lat {d : ℕ} {L : Submodule (𝓞 D.host.E) (Fin d → D.host.E)} {y : Fin d → D.host.E}
    (hy : y ∈ L) {e : D.host.E} (he : e ∈ D.host.AA⁻¹) : e • y ∈ scLat D.host.AA⁻¹ L := by
  refine mem_lat.2 fun c hc => ?_
  obtain ⟨b, hb⟩ := int_of_inv_mul he hc
  rw [smul_smul, mul_comm, ← hb]
  exact L.smul_mem b hy

private theorem mem_iff {d : ℕ} (L : Submodule (𝓞 D.host.E) (Fin d → D.host.E)) (y : Fin d → D.host.E) :
    y ∈ L ↔ y ∈ scLat D.host.AA (scLat D.host.AA⁻¹ L) := by
  refine ⟨fun hy e he => smul_mem_lat hy he, fun h => ?_⟩
  have key : ∀ u ∈ D.host.AA * D.host.AA⁻¹, u • y ∈ L := fun u hu =>
    FractionalIdeal.mul_induction_on hu (C := fun u => u • y ∈ L)
      (fun a ha e he => by rw [mul_smul]; exact mem_lat.1 (h e he) a ha)
      (fun u v hu hv => by rw [add_smul]; exact L.add_mem hu hv)
  simpa using key 1 one_mem_AA_mul

private theorem dual_iff {d : ℕ} (J : Matrix (Fin d) (Fin d) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin d → D.host.E))
    (hL : ∀ y, y ∈ L ↔ ∀ x ∈ L, IntTr (form D.sp.cm.sig J y x)) (y : Fin d → D.host.E) :
    y ∈ scLat D.host.AA⁻¹ L ↔ ∀ x ∈ scLat D.host.AA⁻¹ L,
      ∃ b : 𝓞 D.host.E, (b : D.host.E) = D.host.xi0⁻¹ * form D.sp.cm.sig J y x := by
  have hξ : D.host.xi0 ≠ 0 := xi_ne
  have hs : ∀ c ∈ D.host.AA, star c ∈ D.host.AAbar := fun c h => by
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj]; exact Formalism.L2.Pj.conj_mem_AAbar D h
  have hc : ∀ c ∈ D.host.AAbar, star c ∈ D.host.AA := fun c h => GlobalTheory.star_mem_AA_of_mem_AAbar h
  constructor
  · intro hy x hx
    have hle : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (form D.sp.cm.sig J y x) * D.host.AA * D.host.AAbar ≤
        FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA * D.host.AAbar := by
      rw [hX, mul_assoc, FractionalIdeal.mul_le]
      intro i hi j hj
      obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
      rw [smul_mul_assoc]
      refine Submodule.smul_mem _ z ?_
      refine FractionalIdeal.mul_induction_on hj
        (C := fun j => form D.sp.cm.sig J y x * j ∈
          (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E))
        (fun a ha b hb => ?_) (fun u v hu hv => by rw [mul_add]; exact Submodule.add_mem _ hu hv)
      have h1 := (intTr_iff_mem_dual _).1 ((hL _).1 (mem_lat.1 hy a ha) _ (mem_lat.1 hx _ (hc b hb)))
      rw [form_smul, star_star, mul_comm] at h1
      exact h1
    have hne : D.host.AA * D.host.AAbar ≠ 0 := mul_ne_zero AA_ne AAbar_ne
    have hle' : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (form D.sp.cm.sig J y x) ≤
        FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 := by
      rw [mul_assoc, mul_assoc] at hle
      calc FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (form D.sp.cm.sig J y x)
          = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (form D.sp.cm.sig J y x) * (D.host.AA * D.host.AAbar) *
            (D.host.AA * D.host.AAbar)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
        _ ≤ FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * (D.host.AA * D.host.AAbar) *
            (D.host.AA * D.host.AAbar)⁻¹ := by gcongr
        _ = _ := by rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
    obtain ⟨z, hz⟩ := (FractionalIdeal.mem_spanSingleton _).1 (hle' (FractionalIdeal.mem_spanSingleton_self _ _))
    refine ⟨z, ?_⟩
    rw [← hz, Algebra.smul_def]
    field_simp
  · intro h
    refine mem_lat.2 fun c hcA => (hL _).2 fun x hx => ?_
    have key : ∀ u ∈ D.host.AA * D.host.AA⁻¹, IntTr (c * star u * form D.sp.cm.sig J y x) := by
      intro u hu
      refine FractionalIdeal.mul_induction_on hu (C := fun u => IntTr (c * star u * form D.sp.cm.sig J y x))
        (fun a ha e he => ?_) (fun u v hu hv => ?_)
      · obtain ⟨b, hb⟩ := h _ (smul_mem_lat hx he)
        have h1 := form_smul J 1 e y x
        rw [one_smul, one_mul] at h1
        have e1 : c * star (a * e) * form D.sp.cm.sig J y x = D.host.xi0 * c * star a * (b : D.host.E) := by
          rw [hb, h1, star_mul']
          field_simp
        rw [e1]
        exact ((intTr_iff_mem_dual _).2 (xi_mem hs hcA ha)).mul_int b
      · rw [star_add, mul_add, add_mul]
        exact hu.add hv
    have h1 := form_smul J c 1 y x
    rw [one_smul] at h1
    rw [h1]
    exact key 1 one_mem_AA_mul

private theorem exists_place (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (h : GlobalTheory.SqStepBig.EmbCM Bs) (τ : D.what₂.Tau) :
    ∃ w, ∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x) := by
  refine ⟨InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)), ?_⟩
  obtain ⟨τ', hτ'⟩ := h (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
  have e : τ' = τ := by
    apply (GlobalTheory.T.cmType_restrict_realSubfield_infinitePlace_bijective D).1
    have h1 := (Bs.emb (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))).2
    have h2 : ComplexEmbedding.conjugate ((tauE D τ').comp (algebraMap D.host.F D.host.E)) =
        (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))).embedding := by
      rw [← h1]
      ext x
      simp [hτ']
    show InfinitePlace.mk _ = InfinitePlace.mk _
    rw [← InfinitePlace.mk_conjugate_eq, h2, InfinitePlace.mk_embedding]
  rwa [e] at hτ'

end GlobalTheory.SkewOverW

open Matrix GlobalTheory.SkewOverW GlobalTheory.SkewLat GlobalTheory.WeilSchrodinger GlobalTheory.WeilSchrodingerHerm in
theorem _root_.GlobalTheory.T.exists_selfDual_orientedModel_scaled_skewHermitian : ∀ (D : D7) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → GlobalTheory.SqStepBig.EmbCM Bs →
    ∀ (d r y : ℕ) (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d), Z.IsSkew D.sp.cm.sig Bs r y →
      ∃ (WW : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
        IsSelfDualC WW Λ ∧ NegIdx WW y ∧ GlobalTheory.SqStepBig.OverW WW Λ Z := by
  intro D Bs _ hemb d r y Z hZ
  have hξ : D.host.xi0 ≠ 0 := DualPair.xi_ne
  have hsξ : star D.host.xi0 = -D.host.xi0 := GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D
  have hσ : ∀ z : D.host.E, D.sp.cm.sig z = star z := fun _ => rfl
  have hsk : ∀ i j, star (Z.J j i) = -Z.J i j := fun i j => hZ.skew i j
  set G : Matrix (Fin d) (Fin d) D.host.E := (D.host.xi0⁻¹ • Z.J)ᵀ with hG
  have hGij : ∀ i j, G i j = D.host.xi0⁻¹ * Z.J j i := fun i j => rfl
  have hsG : ∀ i j, star (G i j) = G j i := fun i j => by
    rw [hGij, hGij, star_mul', star_inv₀, hsξ, hsk, inv_neg, neg_mul_neg]
  have hdetJ : Z.J.det ≠ 0 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
    have h := det_ne_zero_of_hasSig (hZ.sig w)
    intro h0
    apply h
    have hm : (Z.J.map (Bs.emb w).1).det = (Bs.emb w).1 Z.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, hm, h0, map_zero, mul_zero]
  have hdet : G.det ≠ 0 := by
    rw [hG, Matrix.det_transpose, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hξ)) hdetJ
  have hform : ∀ x v, sesq D G x v = D.host.xi0⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig Z.J v x := fun x v => by
    rw [hG, sesq_transpose_eq_form, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul]
  have hsum : ∀ x v : Fin d → D.host.E, ∑ i, ∑ j, star (x i) * G i j * v j =
      D.host.xi0⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig Z.J v x := fun x v => by
    rw [← hform, sesq_apply]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]
  have hdual := dual_iff Z.J Z.L hZ.dual
  have hlat : Submodule.IsLattice D.host.E (scLat D.host.AA⁻¹ Z.L) :=
    PairLatLattice.scLat_isLattice (inv_ne_zero DualPair.AA_ne) hZ.lat.toIsLattice
  have herm : (sesq D G).IsSymm := by
    refine ⟨fun x v => ?_⟩
    simp only [sesq_apply, starRingEnd_apply, dotProduct, Matrix.mulVec, star_sum, star_mul',
      star_star, Pi.star_apply, hsG, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have nd : (sesq D G).Nondegenerate := by
    refine ⟨fun x hx => ?_, fun v hv => ?_⟩
    · have h1 : star x ᵥ* G = 0 := by
        refine dotProduct_eq_zero _ fun v => ?_
        rw [← Matrix.dotProduct_mulVec, ← sesq_apply]
        exact hx v
      have h2 : star x = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet h1
      simpa using congrArg star h2
    · have h1 : G *ᵥ v = 0 := by
        refine dotProduct_eq_zero _ fun u => ?_
        rw [dotProduct_comm]
        have := hv (star u)
        rwa [sesq_apply, star_star] at this
      exact Matrix.eq_zero_of_mulVec_eq_zero hdet h1
  have hU : Formalism.HermitianLatticesTheory.IsUnimodular (sesq D G) (scLat D.host.AA⁻¹ Z.L) := by
    show Formalism.E.hdual _ _ = _
    ext x
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
    rw [hdual x]
    refine forall₂_congr fun v _ => ?_
    rw [hform, Submodule.mem_one]
  have hgram := gram_hspOf G herm nd _ hlat hU (fun _ => (r, y))
  refine ⟨hspOf D G herm nd _ hlat hU (fun _ => (r, y)), scLat D.host.AA⁻¹ Z.L, ⟨hlat, fun v => ?_⟩, fun τ => ?_,
    rfl, ?_, fun v => mem_iff Z.L v⟩
  · rw [hgram]
    refine (hdual v).trans (forall₂_congr fun x _ => ?_)
    exact exists_congr fun b => Eq.congr_right (hsum x v).symm
  · obtain ⟨w, hw⟩ := exists_place Bs hemb τ
    have hs := hZ.sig w
    have hre : (tauE D τ D.host.xi0).re = 0 := by
      have h := congrArg Complex.re (GlobalTheory.FockCompare.tauE_star τ D.host.xi0)
      rw [hsξ, map_neg, Complex.neg_re, Complex.conj_re] at h
      linarith
    have hx : (Bs.emb w).1 D.host.xi0 = -((((tauE D τ D.host.xi0).im : ℝ) : ℂ) * Complex.I) := by
      rw [hw]; apply Complex.ext <;> simp [hre]
    have hJ : ∀ i j, Z.J i j = D.host.xi0 * star (G i j) := fun i j => by
      rw [hsG, hGij, mul_inv_cancel_left₀ hξ]
    have hM : Complex.I • Z.J.map (Bs.emb w).1 = (((tauE D τ D.host.xi0).im : ℝ) : ℂ) • G.map (tauE D τ) := by
      ext i j
      simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      rw [hJ, map_mul, hx, hw, GlobalTheory.FockCompare.tauE_star, Complex.conj_conj]
      linear_combination (-(((tauE D τ D.host.xi0).im : ℝ) : ℂ) * tauE D τ (G i j)) * Complex.I_mul_I
    rw [hM] at hs
    have h := hasSignature_of_smul (xi_zero_im_pos D τ) hs
    have hr : r = d - y := by have := hs.1; omega
    rw [hr] at h
    unfold gramAt
    rw [hgram]
    exact h
  · rw [hgram]
    ext i j
    show Z.J i j = D.host.xi0 * G j i
    rw [hGij, mul_inv_cancel_left₀ hξ]
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.Square

theorem awayUnit_inv {K : Type} [Field K] {m : ℕ} {x : K} (hx : x ≠ 0) (h : IsAwayUnit m x) : IsAwayUnit m x⁻¹ := by
  obtain ⟨a, k, k', ⟨b, hb⟩, hxa⟩ := h
  refine ⟨(m : 𝓞 K) ^ k * b, k', k + k', ?_, ?_⟩
  · rw [pow_add, hb]
    exact mul_dvd_mul_left _ (dvd_mul_left _ _)
  · have hb' : (m : K) ^ k' = (a : K) * (b : K) := by exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) hb
    have : ((((m : 𝓞 K) ^ k * b : 𝓞 K)) : K) = (m : K) ^ k * (b : K) := by push_cast; ring
    rw [this, hb', ← hxa]
    field_simp

theorem stepRatio_swap {K P : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {m : ℕ} {S₀ : Finset P} {cc qq : P → ℕ} {u u₀ C : ℂ} {ζ : K}
    (h : StepRatio σ m S₀ cc qq u₀ u) (h0 : u₀ ≠ 0) (hζ : IsAwayUnit m ζ) :
    StepRatio σ m S₀ cc qq (C * σ ζ * u) (C * u₀) := by
  obtain ⟨b, g, g', hb, hg, e⟩ := h
  have h1 : b * ∏ v ∈ S₀, (g v : K) / (g' v : K) ≠ 0 := fun hz => h0 (by rw [e, hz, map_zero, zero_mul])
  refine ⟨ζ * b⁻¹, g', g, hζ.mul (awayUnit_inv (left_ne_zero_of_mul h1) hb), fun v hv => (hg v hv).symm, ?_⟩
  have h2 : ∏ v ∈ S₀, (g' v : K) / (g v : K) = (∏ v ∈ S₀, (g v : K) / (g' v : K))⁻¹ := by
    rw [← Finset.prod_inv_distrib]; simp only [inv_div]
  have h3 : σ (b * ∏ v ∈ S₀, (g v : K) / (g' v : K)) ≠ 0 := (map_ne_zero σ).2 h1
  rw [h2, mul_assoc ζ, ← mul_inv, map_mul, map_inv₀, e]
  field_simp

theorem gbig_of_three {Q1 Q2 Q3 Q : GP} (h1 : GBig Q1) (h2 : GBig Q2) (h3 : GBig Q3)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q1 G μ₀ C x b → Q2 G μ₀ C x b → Q3 G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨a1, h1⟩ := h1
  obtain ⟨a2, h2⟩ := h2
  obtain ⟨a3, h3⟩ := h3
  refine ⟨max a1 (max a2 a3), fun ε CF hCF => ?_⟩
  obtain ⟨c1, x1, g1⟩ := h1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨c2, x2, g2⟩ := h2 ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨c3, x3, g3⟩ := h3 ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max c1 (max c2 c3), max x1 (max x2 x3), fun C hC D large₂ hε hx hR T Lc μ₀ hμ G => H G μ₀ C _ _ ?_ ?_ ?_⟩
  · exact g1 C (le_trans (le_max_left _ _) hC) D large₂ hε (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hμ G
  · exact g2 C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ hε
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hμ G
  · exact g3 C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ hε
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hμ G

theorem two_le_half {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} {W : G.Weil}
    {i j : Fin D.R.m} {p q e : ℕ} {A A' WW : HSp D} {X : Tri T A A' WW} (h : GlobalTheory.SqTower.IsStageC W i j p q X)
    (he : A.rank = A'.rank + 2 * e) : 2 ≤ e := by
  obtain ⟨hp, hq, hA, hA', -⟩ := h
  obtain ⟨k, hk⟩ := D.R.k_even
  obtain ⟨m, hm⟩ := D.R.m_even
  obtain ⟨t, ht⟩ := D.R.t_odd
  have h2 := D.R.two_le_m
  have h3 := D.R.three_m_lt_t
  have e1 : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have e2 : sLen D = D.R.k + D.R.m - 1 + 6 := rfl
  simp only [pp, qq] at *
  omega

end GlobalTheory.SqStepBig

end

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LFun

section IndefiniteRowSideFullHecke

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem reS_congr {n : ℕ} {X X₂ : Spc F E n} (Y : Spc F E n) (h : X₂.J = X.J ∧ X₂.L = X.L) : reS X₂ Y = reS X Y := by
  cases X; cases X₂; obtain ⟨h1, h2⟩ := h; cases h1; cases h2; rfl

theorem isHerm_rebase {B₀ B : Base F E} (he : B.emb = B₀.emb) {n r s : ℕ} {Y Y' : Spc F E n} (h : Y.IsHerm σ B₀ r s)
    (hθ : Y'.θ = Y.θ) (hb : ∀ v : B.P, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y.L (Y'.bas v)) : (reS Y Y').IsHerm σ B r s :=
  { herm := h.herm, sig := fun w => by rw [he]; exact h.sig w, lat := h.lat, dual := h.dual
    cartan := fun w => by rw [he]; show IsCartan _ (Y'.θ w); rw [hθ]; exact h.cartan w
    bas := hb }

theorem isSkew_rebase {B₀ B : Base F E} (he : B.emb = B₀.emb) {n r s : ℕ} {Y Y' : Spc F E n} (h : Y.IsSkew σ B₀ r s)
    (hθ : Y'.θ = Y.θ) (hb : ∀ v : B.P, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y.L (Y'.bas v)) : (reS Y Y').IsSkew σ B r s :=
  { skew := h.skew, sig := fun w => by rw [he]; exact h.sig w, lat := h.lat, dual := h.dual
    cartan := fun w => by rw [he]; show IsCartan _ (Y'.θ w); rw [hθ]; exact h.cartan w
    bas := hb }

theorem isGood_reG {B : Base F E} {a a' : ℕ} {Γ : Geo σ a a'} (g : Γ.IsGood B) {V : Spc F E a} {V' : Spc F E a'}
    {Z : Spc F E (a + a')} (hV : (reS Γ.V V).IsHerm σ B (a - Γ.p) Γ.p) (hV' : (reS Γ.V' V').IsHerm σ B Γ.q (a' - Γ.q))
    (hZ : (reS Γ.W Z).IsSkew σ B (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) : (reG Γ V V' Z).IsGood B :=
  ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, hV, hV', hZ, ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩,
    ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩

theorem resEtaPow_quot {R K' : Type} [CommRing R] [CommRing K'] [Algebra R K'] {K : Subgroup Rˣ}
    {χ χ' : K'ˣ →* Circle} {n m : ℕ} (h : GlobalTheory.WeilM.ResEtaPow K χ n) (h' : GlobalTheory.WeilM.ResEtaPow K χ' m) :
    GlobalTheory.WeilM.ResEtaPow K (χ / χ') (n + m) := by
  intro a
  rw [MonoidHom.div_apply, Circle.coe_div, h a, h' a]
  split_ifs
  · simp
  · rw [div_eq_mul_inv, ← inv_pow, inv_neg, inv_one, ← pow_add]

theorem stepAlpha_cast {e₁ e₂ s : ℤˣ} (h : StepAlpha σ e₁ e₂ s) (B : Base F E) {a b a' e : ℕ} (hab : a = b + 2)
    (he : a = a' + 2 * e) (Γ : Geo σ a a') (Γ₁ : Geo σ b a') (H : Plane E a b) (H' : Plane E (a + a') (b + a'))
    (R : RealMaps F a a') (R₁ : RealMaps F b a') (h1 : Γ₁.V' = Γ.V') (h2 : Γ.q = 0) (h3 : Γ₁.q = 0) (h4 : Γ₁.p + 1 = Γ.p)
    (h5 : H.IsAdapted σ B Γ.V Γ₁.V 0 (b + 1)) (h6 : H'.IsAdapted σ B Γ.W Γ₁.W 0 (b + 1)) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B Γ X om om' R Rf → IsMatched B Γ₁ X om₁ om₁' R₁ Rf₁ →
      ∀ c c₁, IsConst B Γ X om om' R Rf c → IsConst B Γ₁ X om₁ om₁' R₁ Rf₁ c₁ →
        c = C * stepFac B X e₁ e₂ s H.𝔟 H'.𝔟 (1 - (e : ℤ)) * charL X.ν (X.S₀ : Set (Pl F)) (e : ℂ) * c₁ := by
  subst hab
  have := h B b a' Γ Γ₁ H H' R R₁ h1 h2 h3 h4 h5 h6
  rwa [show (b + 2 - a') / 2 = e by omega] at this

end IndefiniteRowSideFullHecke

theorem gbig_both {Q₁ Q₂ : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) : GBig fun G μ C x b => Q₁ G μ C x b ∧ Q₂ G μ C x b :=
  gbig_of_three h₁ h₂ h₂ fun _ _ _ _ _ a b _ => ⟨a, b⟩

end GlobalTheory.SqStepBig

end

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.Square

end GlobalTheory.SqStepBig

end

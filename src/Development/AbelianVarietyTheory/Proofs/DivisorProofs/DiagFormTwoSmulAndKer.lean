module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoSymmetricBirigidifiedCompl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAddNsmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPeriodValueFractionFiel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfComplexExponential
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfComplexExponential
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.ExpUnifAH

theorem exists_unif_isFactorAH_of_isExp : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (M : LB A.left), M.IsLB → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsExp (𝟙 (Sp ℂ)) e → ∃ (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), (∀ z, u.ex z = e z) ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  intro A _ _ g hA hg M hM e he
  exact GlobalTheory.ExpFrame.exists_isFactorAH_frame_of_isExp A g hA hg e he M hM

end GlobalTheory.ExpUnifAH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfComplexExponentialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_appellHumbertFrame_of_complexExponential : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (M : LB A.left), M.IsLB → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsExp (𝟙 (Sp ℂ)) e → ∃ (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), (∀ z, u.ex z = e z) ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  first | exact @GlobalTheory.ExpUnifAH.exists_unif_isFactorAH_of_isExp | exact GlobalTheory.ExpUnifAH.exists_unif_isFactorAH_of_isExp | (intros; apply GlobalTheory.ExpUnifAH.exists_unif_isFactorAH_of_isExp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackTrivialOfImFormInt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackTrivialOfImFormInt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

namespace GlobalTheory.TorusRM.KerTriv

open GlobalTheory.TorusRM.TransFrame

theorem dot_herm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (a b : Fin g → ℂ) :
    a ⬝ᵥ Hm *ᵥ star b = star (b ⬝ᵥ Hm *ᵥ star a) := by
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hH.apply i j, star_star]
  ring

theorem exp_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (w l : Fin g → ℂ) (n : ℤ)
    (hn : (w ⬝ᵥ Hm *ᵥ star l).im = n) :
    Complex.exp (Real.pi * (l ⬝ᵥ Hm *ᵥ star w)) = Complex.exp (Real.pi * (w ⬝ᵥ Hm *ᵥ star l)) := by
  rw [dot_herm_swap hH l w]
  set a := w ⬝ᵥ Hm *ᵥ star l
  have e : (star a : ℂ) = a + (-n : ℤ) * (2 * Complex.I) := by
    apply Complex.ext <;> simp [hn, Complex.conj_re, Complex.conj_im] <;> ring
  rw [e, mul_add, Complex.exp_add]
  have : (Real.pi : ℂ) * ((-n : ℤ) * (2 * Complex.I)) = ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I, _root_.mul_one]

end GlobalTheory.TorusRM.KerTriv


open GlobalTheory.TorusRM.TransFrame GlobalTheory.TorusRM.KerTriv in
theorem GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ w : Fin g → ℂ, (∀ l ∈ u.Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n) → ∃ t : ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w)).left).Gen, t.IsGen := by
  intro A _ _ g hA M u Hm χ hM hF w hw
  have hp : IsProjOver A.hom :=
    (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1 (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  have hL : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hL' : ((abelian₂ A M).pull (pairRight (u.ex w)).left).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨t, ht⟩ := GlobalTheory.HolUnifSec.hasGen_of_periodic A hA hp _ hL' g (transUnif u w)
    (fun z => Complex.exp (Real.pi * (z ⬝ᵥ Hm *ᵥ star w))) (by
      have hd : Differentiable ℂ (fun z : Fin g → ℂ => z ⬝ᵥ Hm *ᵥ star w) := by
        simp only [dotProduct]; fun_prop
      exact ((differentiable_const _).mul hd).cexp) (fun z => Complex.exp_ne_zero _) (by
      intro l hl i z hz
      obtain ⟨n, hn⟩ := hw l hl
      rw [transUnif_factor u hF w ⟨l, hl⟩ i z hz, add_dotProduct, mul_add, Complex.exp_add,
        exp_swap hF.1 w l n hn]
      ring)
  have hρ : fst A (𝟙_ (Over (Sp ℂ))) ≫ pairRight (u.ex w) =
      lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w) := by
    simp only [pairRight, comp_lift, Category.comp_id]
    rw [← Category.assoc, toUnit_unique (fst A (𝟙_ (Over (Sp ℂ))) ≫ toUnit A) (snd A (𝟙_ (Over (Sp ℂ))))]
  have key : (fun _ : PUnit => (fst A (𝟙_ (Over (Sp ℂ)))).left ≫ (pairRight (u.ex w)).left) =
      (fun _ : PUnit => (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w)).left) := by
    funext _
    rw [← Over.comp_left, hρ]
  have H : ∃ t : (LB.LinComb (abelian₂ A M) (fun _ : PUnit => (fst A (𝟙_ (Over (Sp ℂ)))).left ≫
      (pairRight (u.ex w)).left) (fun _ => 1)).Gen, t.IsGen :=
    ⟨_, ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen (abelian₂ A M) _ _ t ht (fst A (𝟙_ (Over (Sp ℂ)))).left⟩
  rw [key] at H
  exact H
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackTrivialOfImFormIntStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_pullback_trivial_of_im_form_int : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ w : Fin g → ℂ, (∀ l ∈ u.Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n) → ∃ t : ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w)).left).Gen, t.IsGen := by
  first | exact @GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int | exact GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int | (intros; apply GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfLineBundleIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfLineBundleIso
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

namespace GlobalTheory.TransportFrame

open ReciprocityTheory.ChartRestriction.G.TB.ValAt

variable {X : Scheme.{0}}

theorem pspec_eq (p q : PrimeSpectrum ℂ) : p = q :=
  PrimeSpectrum.ext ((Ideal.eq_bot_of_prime p.asIdeal).trans (Ideal.eq_bot_of_prime q.asIdeal).symm)

theorem chart_pt (L : LB X) (hL : L.IsLB) (y : Sp ℂ ⟶ X) : ∃ j, ⊤ ≤ y ⁻¹ᵁ L.U j := by
  let p0 : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  have hmem : y p0 ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  refine ⟨j, fun q _ => ?_⟩
  have : q = p0 := pspec_eq q p0
  rw [this]
  exact hj

theorem val_res_unit (x : Sp ℂ ⟶ X) {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)ˣ) :
    valAt' x V (res hVU a : Γ(X, V)) = valAt' x U (a : Γ(X, U)) :=
  ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_res x hVU h (a : Γ(X, U))

theorem val_inv_unit (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
    valAt' x U ((a⁻¹ : Γ(X, U)ˣ) : Γ(X, U)) = (valAt' x U (a : Γ(X, U)))⁻¹ :=
  map_units_inv (valHom x U h) a

theorem val_unit_ne (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
    valAt' x U (a : Γ(X, U)) ≠ 0 :=
  (a.isUnit.map (valHom x U h)).ne_zero

theorem val_gen {L L' : LB X} (w : LB.Iso L' L) (hw : w.IsGen) (x : Sp ℂ ⟶ X) (i i₂ : L.ι) (j j₂ : L'.ι)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L'.U j)) (h₂ : ⊤ ≤ x ⁻¹ᵁ (L.U i₂ ⊓ L'.U j₂)) :
    valAt' x (L.U i ⊓ L'.U j) (w.s (i, j)).val =
      valAt' x (L.U i ⊓ L.U i₂) (L.g i i₂).val * (valAt' x (L'.U j ⊓ L'.U j₂) (L'.g j j₂).val)⁻¹ *
        valAt' x (L.U i₂ ⊓ L'.U j₂) (w.s (i₂, j₂)).val := by
  have hW : ⊤ ≤ x ⁻¹ᵁ ((L.U i ⊓ L'.U j) ⊓ (L.U i₂ ⊓ L'.U j₂)) := fun p hp => ⟨h₁ hp, h₂ hp⟩
  have E : res (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i ⊓ L'.U j from inf_le_left)
      (w.s (i, j) : Γ(X, L.U i ⊓ L'.U j)ˣ) =
      (res (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i ⊓ L.U i₂ from
          le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) (L.g i i₂) *
        (res (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L'.U j ⊓ L'.U j₂ from
          le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) (L'.g j j₂))⁻¹) *
      res (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i₂ ⊓ L'.U j₂ from inf_le_right)
        (w.s (i₂, j₂) : Γ(X, L.U i₂ ⊓ L'.U j₂)ˣ) := hw (i, j) (i₂, j₂)
  have e := congrArg (fun a : Γ(X, (L.U i ⊓ L'.U j) ⊓ (L.U i₂ ⊓ L'.U j₂))ˣ =>
    valAt' x _ (a : Γ(X, (L.U i ⊓ L'.U j) ⊓ (L.U i₂ ⊓ L'.U j₂)))) E
  simp only [Units.val_mul, ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_mul, val_inv_unit x _ hW, val_res_unit x _ hW] at e
  have a1 := val_res_unit x (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i ⊓ L'.U j from inf_le_left) hW
    (w.s (i, j) : Γ(X, L.U i ⊓ L'.U j)ˣ)
  have a2 := val_res_unit x (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i₂ ⊓ L'.U j₂ from inf_le_right) hW
    (w.s (i₂, j₂) : Γ(X, L.U i₂ ⊓ L'.U j₂)ˣ)
  exact a1.symm.trans (e.trans (congrArg (fun t => _ * t) a2))

end GlobalTheory.TransportFrame

namespace GlobalTheory.TransportFrame

open ReciprocityTheory.ChartRestriction.G.TB.ValAt

theorem val_g_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (x : Sp ℂ ⟶ X) (i : L.ι) (h : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    valAt' x (L.U i ⊓ L.U i) (L.g i i).val = 1 := by
  have e := val_res_unit x (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) h (L.g i i)
  rw [hL.g_self i, Units.val_one, ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_one x _ h] at e
  exact e.symm

variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} {L L' : LB A.left}

def chartOf (hL' : L'.IsLB) (y : Sp ℂ ⟶ A.left) : L'.ι := (chart_pt L' hL' y).choose

theorem chartOf_spec (hL' : L'.IsLB) (y : Sp ℂ ⟶ A.left) : ⊤ ≤ y ⁻¹ᵁ L'.U (chartOf hL' y) :=
  (chart_pt L' hL' y).choose_spec

def frT (u' : HolUnif A L' g) (hL' : L'.IsLB) (w : LB.Iso L' L) (i : L.ι) (z : Fin g → ℂ) : ℂ :=
  valAt' (u'.ex z).left (L.U i ⊓ L'.U (chartOf hL' (u'.ex z).left)) (w.s (i, chartOf hL' (u'.ex z).left)).val *
    u'.fr (chartOf hL' (u'.ex z).left) z

theorem frT_eq (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) (i : L.ι) (j : L'.ι)
    (z : Fin g → ℂ) (hi : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i) (hj : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U j) :
    frT u' hL' w i z = valAt' (u'.ex z).left (L.U i ⊓ L'.U j) (w.s (i, j)).val * u'.fr j z := by
  have h0 := chartOf_spec hL' (u'.ex z).left
  have hij0 : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U (chartOf hL' (u'.ex z).left)) := fun p hp => ⟨hi hp, h0 hp⟩
  have hij : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j) := fun p hp => ⟨hi hp, hj hp⟩
  have h0j : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L'.U (chartOf hL' (u'.ex z).left) ⊓ L'.U j) := fun p hp => ⟨h0 hp, hj hp⟩
  have G := val_gen w hw (u'.ex z).left i i (chartOf hL' (u'.ex z).left) j hij0 hij
  have C := u'.fr_compat (chartOf hL' (u'.ex z).left) j z h0j
  have hne := val_unit_ne (u'.ex z).left _ h0j (L'.g (chartOf hL' (u'.ex z).left) j)
  have hs := val_g_self hL (u'.ex z).left i hi
  unfold frT
  rw [G, hs, C]
  have hc := inv_mul_cancel₀ hne
  linear_combination (valAt' (u'.ex z).left (L.U i ⊓ L'.U j) (w.s (i, j)).val * u'.fr j z) * hc

theorem frT_hol (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) (i : L.ι) :
    DifferentiableOn ℂ (frT u' hL' w i) {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i} := by
  intro z0 hz0
  obtain ⟨j, hj⟩ := chart_pt L' hL' (u'.ex z0).left
  have hT := u'.hol (L.U i ⊓ L'.U j) (w.s (i, j)).val
  have hz0' : ⊤ ≤ (u'.ex z0).left ⁻¹ᵁ L.U i := hz0
  have hz0T : z0 ∈ {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j)} :=
    show ⊤ ≤ (u'.ex z0).left ⁻¹ᵁ (L.U i ⊓ L'.U j) from fun p hp => ⟨hz0' hp, hj hp⟩
  have hd : DifferentiableOn ℂ (fun z => valAt' (u'.ex z).left (L.U i ⊓ L'.U j) (w.s (i, j)).val * u'.fr j z)
      {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j)} :=
    hT.2.mul ((u'.fr_hol j).mono fun z (hz : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j)) p hp => (hz hp).2)
  have hev : frT u' hL' w i =ᶠ[nhds z0]
      fun z => valAt' (u'.ex z).left (L.U i ⊓ L'.U j) (w.s (i, j)).val * u'.fr j z :=
    Filter.eventually_of_mem (hT.1.mem_nhds hz0T) fun z (hz : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j)) =>
      frT_eq u' hL hL' w hw i j z (fun p hp => (hz hp).1) (fun p hp => (hz hp).2)
  exact (((hd z0 hz0T).differentiableAt (hT.1.mem_nhds hz0T)).congr_of_eventuallyEq hev).differentiableWithinAt

theorem frT_ne (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) (i : L.ι)
    (z : Fin g → ℂ) (hi : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i) : frT u' hL' w i z ≠ 0 := by
  obtain ⟨j, hj⟩ := chart_pt L' hL' (u'.ex z).left
  rw [frT_eq u' hL hL' w hw i j z hi hj]
  have hij : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j) := fun p hp => ⟨hi hp, hj hp⟩
  exact mul_ne_zero (val_unit_ne _ _ hij (w.s (i, j) : Γ(A.left, L.U i ⊓ L'.U j)ˣ)) (u'.fr_ne j z hj)

theorem frT_compat (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) (i i₂ : L.ι)
    (z : Fin g → ℂ) (h : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L.U i₂)) :
    frT u' hL' w i z = valAt' (u'.ex z).left (L.U i ⊓ L.U i₂) (L.g i i₂).val * frT u' hL' w i₂ z := by
  obtain ⟨j, hj⟩ := chart_pt L' hL' (u'.ex z).left
  have hi : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i := fun p hp => (h hp).1
  have hi₂ : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i₂ := fun p hp => (h hp).2
  rw [frT_eq u' hL hL' w hw i j z hi hj, frT_eq u' hL hL' w hw i₂ j z hi₂ hj,
    val_gen w hw (u'.ex z).left i i₂ j j (fun p hp => ⟨hi hp, hj hp⟩) (fun p hp => ⟨hi₂ hp, hj hp⟩),
    val_g_self hL' (u'.ex z).left j hj]
  ring

def transport (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) :
    HolUnif A L g where
  ex := u'.ex
  ex_add := u'.ex_add
  ex_onto := u'.ex_onto
  Λ := u'.Λ
  ker := u'.ker
  discrete := u'.discrete
  full := u'.full
  hol := u'.hol
  fr := frT u' hL' w
  fr_hol := frT_hol u' hL hL' w hw
  fr_ne := frT_ne u' hL hL' w hw
  fr_compat := frT_compat u' hL hL' w hw

theorem isFactorAH_transport (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ' : u'.Λ → ℂ} (h : GlobalTheory.TorusRM.IsFactorAH u' Hm χ') :
    GlobalTheory.TorusRM.IsFactorAH (transport u' hL hL' w hw) Hm χ' := by
  refine ⟨h.1, h.2.1, fun (l : u'.Λ) i z hz => ?_⟩
  obtain ⟨j, hj⟩ := chart_pt L' hL' (u'.ex z).left
  have he : u'.ex (z + l) = u'.ex z := by rw [u'.ex_add, (u'.ker l).2 l.2, _root_.mul_one]
  have hz0 : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i := hz
  have hz' : ⊤ ≤ (u'.ex (z + l)).left ⁻¹ᵁ L.U i := he ▸ hz0
  have hj' : ⊤ ≤ (u'.ex (z + l)).left ⁻¹ᵁ L'.U j := he ▸ hj
  show frT u' hL' w i z = χ' l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * frT u' hL' w i (z + l)
  rw [frT_eq u' hL hL' w hw i j z hz0 hj, frT_eq u' hL hL' w hw i j (z + l) hz' hj', h.2.2 l j z hj, he]
  ring

theorem exists_holUnif_isFactorAH_of_lbIso : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L L' : LB A.left)
    (u' : HolUnif A L' g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ' : u'.Λ → ℂ), L.IsLB → L'.IsLB → LBIso L L' →
    GlobalTheory.TorusRM.IsFactorAH u' Hm χ' → ∃ (u : HolUnif A L g) (χ : u.Λ → ℂ), u.ex = u'.ex ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  intro A _ g L L' u' Hm χ' hL hL' hiso h
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  exact ⟨transport u' hL hL' w hw, χ', rfl, isFactorAH_transport u' hL hL' w hw h⟩

end GlobalTheory.TransportFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfLineBundleIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_appellHumbertFrame_of_lineBundleIso : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L L' : LB A.left) (u' : HolUnif A L' g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ' : u'.Λ → ℂ), L.IsLB → L'.IsLB → LBIso L L' → GlobalTheory.TorusRM.IsFactorAH u' Hm χ' → ∃ (u : HolUnif A L g) (χ : u.Λ → ℂ), u.ex = u'.ex ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  exact @GlobalTheory.TransportFrame.exists_holUnif_isFactorAH_of_lbIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFormTwoSmulAndKer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT


open GlobalTheory.CechPic in
theorem GlobalTheory.SymBirig.diag_form_two_smul_and_ker : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → ∃ E₁ : LinearMap.BilinForm ℤ La, EF = (2 : ℤ) • E₁ ∧ ∀ (k : ℕ) (a : La), 0 < k → ((∀ y, (k : ℤ) ∣ E₁ a y) ↔ ∃ t : (P.pull (lift (snd A (Over.mk (𝟙 (Sp ℂ))) ≫ e ((k : ℂ)⁻¹ • Q a)) (fst A (Over.mk (𝟙 (Sp ℂ))))).left).Gen, t.IsGen) := by
  intro A _ _ g hA hg P hP h1 h2 hsym hamp e La _ Q EF hexp hQ hker hW
  obtain ⟨M, hM, hPM⟩ := GlobalTheory.T.exists_mumford_bundle_iso_symmetric_birigidified_complex A g hA hg P hP h1 h2 hsym
  have hPM' : LBIso P (abelian₂ A M) := hPM
  obtain ⟨u, Hm, χ, hue, hF⟩ := GlobalTheory.T.exists_appellHumbertFrame_of_complexExponential A g hA hg M hM e hexp
  obtain ⟨u', χ', hue', hF'⟩ := GlobalTheory.TorusRM.exists_isFactorAH_lam_diag g A hA M u Hm χ hM hF
  have hlam : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hD := GlobalTheory.GenSpread.lbIso_pullback hPM' (lift (𝟙 A) (𝟙 A)).left
  obtain ⟨v, ψ, hve, hFv⟩ := GlobalTheory.T.exists_appellHumbertFrame_of_lineBundleIso A g _ _ u' _ χ' (pull_isLB hP _) (pull_isLB hlam _) hD hF'
  have hpos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple A hA _ (pull_isLB hP _) hamp g v _ ψ hFv.1 hFv.2.1 hFv.2.2
  have hAH := GlobalTheory.TorusRM.isAH_of_isFactorAH hFv hpos
  have hmemu : ∀ z, z ∈ u.Λ ↔ z ∈ Q.range := fun z => by rw [← u.ker, hue]; exact hker z
  have hmemv : ∀ z, z ∈ v.Λ ↔ z ∈ Q.range := fun z => by rw [← v.ker, hve, hue', hue]; exact hker z
  have hvx : ∀ z, v.ex z = e z := fun z => by rw [hve, hue', hue]
  have hNex : ∀ a b : La, ∃ n : ℤ, (hermForm Hm (Q a) (Q b)).im = n := fun a b =>
    GlobalTheory.RiemInt.im_hermForm_int hM u hF ⟨Q a, (hmemu _).2 ⟨a, rfl⟩⟩ ⟨Q b, (hmemu _).2 ⟨b, rfl⟩⟩
  choose N hN using hNex
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have key : ∀ a b : La, EF a b = 2 * N a b := by
    intro a b
    have hk : ∀ k : ℕ, 0 < k → ∃ n : ℤ, ((EF a b : ℂ) - 2 * N a b) / k = n := by
      intro k hk
      let c₁ : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k)) (Complex.exp_ne_zero _)
      let c₂ : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) *
        (((Q a ⬝ᵥ ((2 : ℂ) • Hm) *ᵥ star (Q b)).im : ℝ) : ℂ) / k)) (Complex.exp_ne_zero _)
      have w1 := hW k a b c₁ hk rfl
      have w2 := GlobalTheory.AHWeilAny.weilIs_exp_riemannForm A hA _ (pull_isLB hP _) g v _ ψ hAH k (Q a) (Q b) c₂ hk
        ((hmemv _).2 ⟨a, rfl⟩) ((hmemv _).2 ⟨b, rfl⟩) rfl
      rw [hvx, hvx] at w2
      have h3 := congrArg (fun c : ℂˣ => (c : ℂ)) (GlobalTheory.T.weilPairing_complex_value_unique (Sp ℂ) A g hA hg _ (pull_isLB hP _) (𝟙 (Sp ℂ)) k _ _ c₁ c₂ w1 w2)
      simp only [c₁, c₂, Units.val_mk0] at h3
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h3
      have h2 : ((Q a ⬝ᵥ ((2 : ℂ) • Hm) *ᵥ star (Q b)).im) = 2 * (N a b : ℝ) := by
        have h4 := hN a b
        unfold hermForm at h4
        have h5 : ((2 : ℂ) • Hm) *ᵥ star (Q b) = (2 : ℂ) • (Hm *ᵥ star (Q b)) := by
          rw [Matrix.smul_mulVec]
        rw [h5, dotProduct_smul, smul_eq_mul, Complex.mul_im, h4]
        simp
      rw [h2] at hn
      refine ⟨-n, mul_left_cancel₀ hpi ?_⟩
      push_cast at hn ⊢
      linear_combination (-1 : ℂ) * hn
    obtain ⟨K, hK⟩ : ∃ K : ℕ, K = (EF a b - 2 * N a b).natAbs + 1 := ⟨_, rfl⟩
    obtain ⟨n, hn⟩ := hk K (by omega)
    have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
    rw [div_eq_iff hK0] at hn
    have e2 : EF a b - 2 * N a b = (K : ℤ) * n := Int.cast_injective (α := ℂ) (by push_cast; rw [hn]; ring)
    have e3 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ⟨n, e2⟩ (by rw [Int.natAbs_natCast]; omega)
    omega
  have hadd : ∀ a a' b, N (a + a') b = N a b + N a' b := by
    intro a a' b
    have h := key (a + a') b
    rw [map_add (f := _), LinearMap.add_apply, key, key] at h
    omega
  have hadd' : ∀ a b b', N a (b + b') = N a b + N a b' := by
    intro a b b'
    have h := key a (b + b')
    rw [map_add (f := _), key, key] at h
    omega
  have hsm : ∀ (c : ℤ) a b, N (c • a) b = c * N a b := by
    intro c a b
    have h := key (c • a) b
    rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul, key] at h
    have h' : 2 * (N (c • a) b - c * N a b) = 0 := by linear_combination -h
    linear_combination (mul_eq_zero.1 h').resolve_left two_ne_zero
  have hsm' : ∀ (c : ℤ) a b, N a (c • b) = c * N a b := by
    intro c a b
    have h := key a (c • b)
    rw [map_zsmul, smul_eq_mul, key] at h
    have h' : 2 * (N a (c • b) - c * N a b) = 0 := by linear_combination -h
    linear_combination (mul_eq_zero.1 h').resolve_left two_ne_zero
  refine ⟨LinearMap.mk₂ ℤ N hadd (fun c a b => by rw [hsm, smul_eq_mul]) hadd' (fun c a b => by rw [hsm', smul_eq_mul]), ?_, ?_⟩
  · ext a b
    simp [key]
  · intro k a hk
    simp only [LinearMap.mk₂_apply]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hwl : ∀ y, (((k : ℂ)⁻¹ • Q a) ⬝ᵥ Hm *ᵥ star (Q y)).im = (N a y : ℝ) / k := by
      intro y
      have h4 := hN a y
      unfold hermForm at h4
      rw [smul_dotProduct, smul_eq_mul, show ((k : ℂ)⁻¹) = (((k : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
        Complex.im_ofReal_mul, h4, div_eq_inv_mul]
    have stepA : (∀ y, (k : ℤ) ∣ N a y) ↔
        ∀ l ∈ u.Λ, ∃ n : ℤ, (((k : ℂ)⁻¹ • Q a) ⬝ᵥ Hm.mulVec (star l)).im = n := by
      constructor
      · rintro h l hl
        obtain ⟨y, rfl⟩ := (hmemu l).1 hl
        obtain ⟨n, hn⟩ := h y
        exact ⟨n, by rw [hwl, hn]; push_cast; field_simp⟩
      · intro h y
        obtain ⟨n, hn⟩ := h (Q y) ((hmemu _).2 ⟨y, rfl⟩)
        rw [hwl, div_eq_iff hk0] at hn
        exact ⟨n, by exact_mod_cast (show (N a y : ℝ) = (k : ℝ) * n by rw [hn]; ring)⟩
    have stepB := (show _ ↔ _ from ⟨GlobalTheory.T.mumfordBundle_pullback_trivial_of_im_form_int A g hA M u Hm χ hM hF ((k : ℂ)⁻¹ • Q a), fun h => by
      obtain ⟨θ, hθ, h0, hp⟩ := GlobalTheory.TorusRM.exists_theta_of_hasGen_lam_pull g A hA M u Hm χ hM hF _ h
      exact GlobalTheory.ThetaLiouville.im_form_mem_int g u.Λ u.full Hm hF.1 _ θ hθ h0 hp⟩)
    refine stepA.trans (stepB.trans ?_)
    have c1 := GlobalTheory.RealMult.Elliptic.cls_pull_lam hM (fst A (𝟙_ (Over (Sp ℂ))))
      (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex ((k : ℂ)⁻¹ • Q a)) (pull_isLB hlam _)
    have c2 := GlobalTheory.RealMult.Elliptic.cls_pull_lam hM (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex ((k : ℂ)⁻¹ • Q a))
      (fst A (𝟙_ (Over (Sp ℂ)))) (pull_isLB hlam _)
    have c3 : cls (P.pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex ((k : ℂ)⁻¹ • Q a)) (fst A (𝟙_ (Over (Sp ℂ))))).left)
        (pull_isLB hP _) = cls ((abelian₂ A M).pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex ((k : ℂ)⁻¹ • Q a))
          (fst A (𝟙_ (Over (Sp ℂ))))).left) (pull_isLB hlam _) := by
      rw [cls_pull hP, cls_pull hlam, (cls_eq_iff hP hlam).2 hPM']
    rw [← cls_eq_zero_iff (pull_isLB hlam _), c1, lam_comm, ← c2, ← c3, cls_eq_zero_iff, hue]
    exact Iff.rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFormTwoSmulAndKerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diag_form_two_smul_and_ker_alt : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → ∃ E₁ : LinearMap.BilinForm ℤ La, EF = (2 : ℤ) • E₁ ∧ ∀ (k : ℕ) (a : La), 0 < k → ((∀ y, (k : ℤ) ∣ E₁ a y) ↔ ∃ t : (P.pull (lift (snd A (Over.mk (𝟙 (Sp ℂ))) ≫ e ((k : ℂ)⁻¹ • Q a)) (fst A (Over.mk (𝟙 (Sp ℂ))))).left).Gen, t.IsGen) := by
  first | exact @GlobalTheory.SymBirig.diag_form_two_smul_and_ker | exact GlobalTheory.SymBirig.diag_form_two_smul_and_ker | (intros; apply GlobalTheory.SymBirig.diag_form_two_smul_and_ker <;> assumption)
end

module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnipotentDoubledStabilizerAddsDiagonalBloc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VanishingDescendsBesselToFourierJacobi

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinkedLineVectorsInvertibleOnThetaFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinkedLineVectorsInvertibleOnThetaFunctions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct Matrix GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.LinkInvTheta

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj starAdj_ofAdj)

variable {D : D7}

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : star (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * star (ψ a) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', h1]; simp
  have h3 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ a ≠ 0 := by intro h; rw [h, zero_mul] at h3; exact zero_ne_one h3
  exact mul_left_cancel₀ h0 (h2.trans h3.symm)

theorem map_starAdj_eq_zero {B : Type} [CommRing B] (φ : AE D →+* B) (hφ : ∀ z, φ z = 0 → φ (cA D z) = 0)
    (L S : HSp D) {x : WO L S} (hx : x.map φ = 0) : (starAdj L S x).map φ = 0 := by
  have h1 : (adj x).map φ = 0 := by
    funext i j
    exact hφ (x j i) (congrFun (congrFun hx j) i)
  have h2 := map_mul_eq_zero_right φ (giA L) (map_mul_eq_zero_left φ h1 (gA S))
  funext i j
  have h3 : φ ((giA L ⬝ (adj x ⬝ gA S) : Mx D L.rank S.rank) i j) = 0 := congrFun (congrFun h2 i) j
  show φ (incA D D.host.xi0 * (giA L ⬝ (adj x ⬝ gA S) : Mx D L.rank S.rank) i j) = 0
  rw [map_mul, h3, mul_zero]

theorem continuous_starAdj (L S : HSp D) : Continuous (starAdj L S) := by
  have h1 : Continuous fun x : WO L S => (adj x ⬝ gA S : Mx D L.rank S.rank) :=
    continuous_adj.matrix_mul continuous_const
  have h2 : Continuous fun x : WO L S => (giA L ⬝ (adj x ⬝ gA S) : Mx D L.rank S.rank) :=
    continuous_const.matrix_mul h1
  exact h2.const_smul (incA D D.host.xi0)

theorem starAdj_mem (L S : HSp D) {x : WO L S} (hx : x ∈ ratMx D S.rank L.rank) :
    starAdj L S x ∈ ratMx D L.rank S.rank := by
  obtain ⟨γ, hγ⟩ := mem_ratMx.1 hx
  rw [← hγ, starAdj, giA, gA, ← rat_conjTranspose, ← rat_mul, ← rat_mul, ← rat_smul]
  exact rat_mem _

theorem lnk_simil {L L' : HSp D} {ζ : Fin L.rank → D.host.E} {ζ' : Fin L'.rank → D.host.E} (h : IsLineVec L' ζ')
    (l : Lnk L ζ L' ζ') : l.τᴴ ⬝ (L.gram ⬝ l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram := by
  have e : star ζ' ⬝ᵥ (l.τᴴ ⬝ (L.gram ⬝ l.τ)) *ᵥ ζ' =
      star ζ' ⬝ᵥ ((D.host.xi0 * star D.host.xi0) • L'.gram) *ᵥ ζ' := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.mulVec_mulVec, l.map, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← l.norm, star_neg, Matrix.mulVec_neg, neg_dotProduct_neg]
  have hu : Unique (Fin L'.rank) := by rw [h.1]; infer_instance
  have h2 := h.2
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at e h2
  funext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  have a : star ζ' default ≠ 0 := left_ne_zero_of_mul h2
  have b : ζ' default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
  have c := mul_left_cancel₀ a e
  have c' := mul_right_cancel₀ b c
  exact c'

theorem link_inv_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (L L' S : HSp D) (ζ : Fin L.rank → D.host.E) (ζ' : Fin L'.rank → D.host.E), IsLineVec L ζ → IsLineVec L' ζ' → ∀ l : Lnk L ζ L' ζ', l.τᴴ ⬝ (L.gram ⬝ l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram ∧ ∀ Φ₀, IsThetaFunO ψ S L' Φ₀ → ∃ Ξ, IsThetaFunO ψ L S Ξ ∧ Φ₀ = fun w => star (Ξ (l.κ S w)) := by
  intro D ψ hψ L L' S ζ ζ' hL hL' l
  have hτ := lnk_simil hL' l
  refine ⟨hτ, fun Φ₀ hΦ => ?_⟩
  have hτ' : l.τᴴ ⬝ (L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram := by
    rw [Int.cast_one, one_mul]; exact hτ
  obtain ⟨hadd, -, -, -, hsym, -⟩ := GlobalTheory.LinkKappa.kappa_props D L L' S l.τ 1 hτ' (l.κ S) (fun _ => rfl)
  have hH : ∀ w w', symplOH L S (l.κ S w) (l.κ S w') = -symplOH S L' w w' := fun w w' => by
    unfold symplOH; rw [hsym]; push_cast; ring
  have hτ0 : l.τ ≠ 0 := by
    intro h0
    have e := l.map
    rw [h0, Matrix.zero_mulVec] at e
    have hz : ζ = 0 := neg_eq_zero.mp e.symm
    apply hL.2
    rw [hz]; simp
  obtain ⟨σ, hστ, hτσ⟩ := GlobalTheory.Unf.LinkGram.exists_inv_of_rank_one hL.1 hL'.1 l.τ hτ0
  let g : WO L S → WO S L' := fun x => (rat σ : Mx D L'.rank L.rank) ⬝ starAdj L S x
  have hgk : ∀ w, g (l.κ S w) = w := by
    intro w
    show (rat σ : Mx D L'.rank L.rank) ⬝ starAdj L S (l.κ S w) = w
    rw [Lnk.κ, starAdj_ofAdj, ← Matrix.mul_assoc, ← rat_mul, hστ, rat_one, Matrix.one_mul]
  have hkg : ∀ x, l.κ S (g x) = x := by
    intro x
    show l.κ S ((rat σ : Mx D L'.rank L.rank) ⬝ starAdj L S x) = x
    rw [Lnk.κ, ← Matrix.mul_assoc, ← rat_mul, hτσ, rat_one, Matrix.one_mul, GlobalTheory.Unf.LinkGram.ofAdj_starAdj]
  have gadd : ∀ x y, g (x + y) = g x + g y := fun x y => by
    conv_lhs => rw [← hkg x, ← hkg y, ← hadd, hgk]
  have gH : ∀ x y, symplOH S L' (g x) (g y) = -symplOH L S x y := fun x y => by
    conv_rhs => rw [← hkg x, ← hkg y, hH, neg_neg]
  have gcont : Continuous g := continuous_const.matrix_mul (continuous_starAdj L S)
  have grat : ∀ x ∈ ratMx D S.rank L.rank, g x ∈ ratMx D L'.rank S.rank := fun x hx =>
    ratMx_mul (rat_mem σ) (starAdj_mem L S hx)
  have gfin : ∀ x : WO L S, x.map (finPart D) = 0 → (g x).map (finPart D) = 0 := fun x h =>
    map_mul_eq_zero_right (finPart D) _
      (map_starAdj_eq_zero (finPart D) (fun z hz => by rw [GlobalTheory.LinkKappa.finPart_conj, hz, map_zero]) L S h)
  have ginf : ∀ x : WO L S, x.map (infPart D) = 0 → (g x).map (infPart D) = 0 := fun x h =>
    map_mul_eq_zero_right (infPart D) _
      (map_starAdj_eq_zero (infPart D) (fun z hz => by rw [GlobalTheory.LinkKappa.infPart_conj, hz, map_zero]) L S h)
  let A : WO L S →+ WO S L' := AddMonoidHom.mk' g gadd
  refine ⟨fun x => star (Φ₀ (g x)), ⟨fun γ x => ?_, ?_, continuous_star.comp (hΦ.cont.comp gcont), fun k M h1 h2 x => ?_⟩, ?_⟩
  · obtain ⟨γ', hγ'⟩ := grat (ratW S L γ) ⟨γ, rfl⟩
    have e : g (ratW S L γ) = ratW L' S γ' := hγ'.symm
    show star (Φ₀ (g (ratW S L γ + x))) = ψ (-(symplOH L S (ratW S L γ) x)) * star (Φ₀ (g x))
    rw [gadd, e, hΦ.quasi, star_mul', star_psi hψ, ← e, gH, neg_neg]
  · obtain ⟨U, hU, h⟩ := hΦ.level
    refine ⟨U.comap A, hU.preimage gcont, fun u hu h0 => ?_⟩
    funext x
    have e := congrFun (h _ hu (ginf u h0)) (g x)
    unfold heisO at e ⊢
    show ψ (symplOH L S x u) * star (Φ₀ (g (x + u))) = star (Φ₀ (g x))
    rw [← e, star_mul', star_psi hψ]
    show ψ (symplOH L S x u) * star (Φ₀ (g (x + u))) = ψ (-symplOH S L' (g x) (g u)) * star (Φ₀ (g x + g u))
    rw [gH, neg_neg, gadd]
  · have h3 : ∀ t, (A (M t)).map (finPart D) = 0 := fun t => gfin (M t) (h2 t)
    have := hΦ.smooth k (A.comp M) (gcont.comp h1) h3 (g x)
    have heq : (fun t => Φ₀ (g (x + M t))) = fun t => Φ₀ (g x + A (M t)) :=
      funext fun t => congrArg Φ₀ (gadd x (M t))
    have h4 := (congrArg (ContDiff ℝ _) heq).mpr this
    exact Complex.conjCLE.contDiff.comp h4
  · funext w
    show Φ₀ w = star (star (Φ₀ (g (l.κ S w))))
    rw [hgk, star_star]
end GlobalTheory.LinkInvTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinkedLineVectorsInvertibleOnThetaFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linkedLineVectors_invertible_on_theta_functions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (L L' S : HSp D) (ζ : Fin L.rank → D.host.E) (ζ' : Fin L'.rank → D.host.E), IsLineVec L ζ → IsLineVec L' ζ' → ∀ l : Lnk L ζ L' ζ', l.τᴴ ⬝ (L.gram ⬝ l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram ∧ ∀ Φ₀, IsThetaFunO ψ S L' Φ₀ → ∃ Ξ, IsThetaFunO ψ L S Ξ ∧ Φ₀ = fun w => star (Ξ (l.κ S w)) := by
  first | exact @GlobalTheory.LinkInvTheta.link_inv_theta | exact GlobalTheory.LinkInvTheta.link_inv_theta | (intros; apply GlobalTheory.LinkInvTheta.link_inv_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPeriodGivesBesselPeriodOfLift
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAllDataProductsEqFourierJacobiPeriod
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAllDataProductsEqFourierJacobiPeriod
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.LinkProd

variable {D : D7}

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : star (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * star (ψ a) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', h1]; simp
  have h3 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ a ≠ 0 := by intro h; rw [h, zero_mul] at h3; exact zero_ne_one h3
  exact mul_left_cancel₀ h0 (h2.trans h3.symm)

theorem heisO_at_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w f 0 = f w := by
  simp [heisO, symplOH_zero_left]

theorem lnk_point {L L' : HSp D} {ζ : Fin L.rank → D.host.E} {ζ' : Fin L'.rank → D.host.E} (l : Lnk L ζ L' ζ')
    {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (n : GA D W) :
    l.κ W₀ (ptS d L' (zEll L' ρ ζ') n) = ptT d L (yZero L ρ ζ) n ∧
      cenT d L (yZero L ρ ζ) n = -cenS d L' (zEll L' ρ ζ') n := by
  constructor
  · have h : (rat l.τ : Mx D L.rank L'.rank) ⬝ zEll L' ρ ζ' = yZero L ρ ζ := by
      have h0 : ratV (-ζ) = -ratV ζ := funext fun i => map_neg (incA D) _
      rw [yZero, zEll, zEll, Matrix.mul_vecMulVec, ← ratV_mulVec, l.map, h0, Matrix.neg_vecMulVec]
    rw [GlobalTheory.Unf.LinkPoint.ptT_eq, Lnk.κ, ptS, d.extX_apply, ← h]
    simp only [Matrix.mul_assoc]
  · have hN : D.host.xi0 * star D.host.xi0 ≠ 0 :=
      mul_ne_zero (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) (star_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
    rw [GlobalTheory.Unf.LinkPoint.cenT_eq, GlobalTheory.Unf.LinkPoint.neg_cenS_eq, yZero, adj_neg, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg, GlobalTheory.Unf.LinkPoint.gram_zEll, GlobalTheory.Unf.LinkPoint.gram_zEll,
      smul_smul, ← map_mul, l.norm, inv_mul_cancel_left₀ hN]

theorem perAll_box_eq_per : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), ∀ (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Lnk B.L B.ζ L' ζ') (χA χz χ' : (AE D)ˣ →* Circle) (oma : Om B.A J.W₀) (omz : Om J.W₀ L'), s.χV = χA * χz → IsWeilDatumO ψ B.A J.W₀ χA s.χW oma → IsWeilDatumO ψ J.W₀ L' χ' χz omz → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) Ξ₁ Ξ₂, IsThetaFunO ψ B.A J.W₀ Ξ₁ → IsThetaFunO ψ B.L J.W₀ Ξ₂ → J.perAll ψ B s.om₀ φ G (B.o.boxS J.W₀ Ξ₁ Ξ₂) = J.per ψ ζ' omz (liftT oma B.vA.μ B.vA.𝓕 φ Ξ₁) G (fun w => star (Ξ₂ (l.κ J.W₀ w))) := by
  intro D ψ ρ B J s L' ζ' hL' l χA χz χ' oma omz hχ hoa hoz φ G Ξ₁ Ξ₂ hΞ₁ hΞ₂
  have hψ := hoa.std
  have hrk : B.L.rank = L'.rank := B.line.1.trans hL'.1.symm
  have hres : ResEta D χz B.L.rank := by rw [hrk]; exact hoz.resT
  obtain ⟨omL, hoL⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D B.L J.W₀ ψ χz s.χW hψ hoz.hecT hoa.hecT hres hoa.resT
  obtain ⟨hg, -⟩ := GlobalTheory.T.linkedLineVectors_invertible_on_theta_functions D ψ hψ B.L L' J.W₀ B.ζ ζ' B.line hL' l
  have hg' : l.τᴴ ⬝ (B.L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram := by
    rw [Int.cast_one, one_mul]; exact hg
  have hcl := (GlobalTheory.ConjLine.conj_line D ψ B.L L' J.W₀ l.τ hrk hg' χz s.χW χ' omL omz hoL hoz Ξ₂ hΞ₂).2
  have hTS := GlobalTheory.TensorSrc.tensorSource D ψ hψ B.V₀ B.A B.L B.o J.W₀
  have hw0 : IsWeilDatumO ψ B.V₀ J.W₀ (χA * χz) s.χW s.om₀ := hχ ▸ s.weil₀
  have hbt : IsThetaFunO ψ B.V₀ J.W₀ (B.o.boxS J.W₀ Ξ₁ Ξ₂) := hTS.box_theta Ξ₁ Ξ₂ hΞ₁ hΞ₂
  have key : ∀ n ∈ flagN J.d, ∀ h, ∫ h₀ in B.vA.𝓕, φ h₀ * fjKer ψ J.d B.o B.ζ s.om₀ (B.o.boxS J.W₀ Ξ₁ Ξ₂) h₀ n h ∂B.vA.μ =
      liftT oma B.vA.μ B.vA.𝓕 φ Ξ₁ h * star (thetaJS ψ J.d ζ' omz (fun w => star (Ξ₂ (l.κ J.W₀ w))) n h) := by
    intro n _ h
    obtain ⟨hp, hc⟩ := lnk_point l J.d n
    have e1 : ∀ h₀, φ h₀ * fjKer ψ J.d B.o B.ζ s.om₀ (B.o.boxS J.W₀ Ξ₁ Ξ₂) h₀ n h =
        oma (h₀, h) Ξ₁ 0 * φ h₀ * (ψ (cenT J.d B.L (yZero B.L ρ B.ζ) n) * omL (1, h) Ξ₂ (ptT J.d B.L (yZero B.L ρ B.ζ) n)) := by
      intro h₀
      rw [GlobalTheory.Unf.fjKer_eq_om_apply D ψ J.W J.W₀ B.V₀ B.A B.L ρ J.d B.o B.ζ _ _ s.om₀ s.weil₀ _ hbt,
        hTS.om_box χA χz s.χW s.om₀ oma omL hw0 hoa hoL h₀ 1 h Ξ₁ Ξ₂ hΞ₁ hΞ₂]
      simp only [OrthDec.boxS, AddEquiv.apply_symm_apply]
      ring
    simp_rw [e1]
    rw [integral_mul_const, liftT_apply]
    congr 1
    have hcl' : omz (h, 1) (fun w => star (Ξ₂ (l.κ J.W₀ w))) = fun w => star (omL (1, h) Ξ₂ (l.κ J.W₀ w)) := hcl h
    rw [thetaJS, jacS, hcl', Pi.smul_apply, smul_eq_mul, heisO_at_zero, star_mul', star_star, star_psi hψ, hp, hc]
  unfold JacL.perAll JacL.per fjAll fjSrc
  congr 1
  funext h
  congr 1
  funext n
  rw [fjAllFun, fjSrcFun, key n.1 n.2 h]
  ring

end GlobalTheory.LinkProd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAllDataProductsEqFourierJacobiPeriodStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodAllData_products_eq_fourierJacobiPeriod : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), ∀ (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Lnk B.L B.ζ L' ζ') (χA χz χ' : (AE D)ˣ →* Circle) (oma : Om B.A J.W₀) (omz : Om J.W₀ L'), s.χV = χA * χz → IsWeilDatumO ψ B.A J.W₀ χA s.χW oma → IsWeilDatumO ψ J.W₀ L' χ' χz omz → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) Ξ₁ Ξ₂, IsThetaFunO ψ B.A J.W₀ Ξ₁ → IsThetaFunO ψ B.L J.W₀ Ξ₂ → J.perAll ψ B s.om₀ φ G (B.o.boxS J.W₀ Ξ₁ Ξ₂) = J.per ψ ζ' omz (liftT oma B.vA.μ B.vA.𝓕 φ Ξ₁) G (fun w => star (Ξ₂ (l.κ J.W₀ w))) := by
  first | exact @GlobalTheory.LinkProd.perAll_box_eq_per | exact GlobalTheory.LinkProd.perAll_box_eq_per | (intros; apply GlobalTheory.LinkProd.perAll_box_eq_per <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPeriodAllDataIsTameThetaFunctional
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPeriodAllDataIsTameThetaFunctional
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.PerAllTame

variable {D : D7}

theorem tame_congr {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {ℓ ℓ' : (WO S T → ℂ) → ℂ}
    (h : Tame ψ S T ℓ) (e : ∀ f, IsThetaFunO ψ S T f → ℓ' f = ℓ f) : Tame ψ S T ℓ' := by
  have hθ : ∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f) :=
    fun w f hf => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w
  refine ⟨fun f f' hf hf' => ?_, fun c f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun f hf m _ α hα hs => ?_⟩
  · rw [e _ (GlobalTheory.OrientedHeis.theta_add hf hf'), e _ hf, e _ hf', h.add f f' hf hf']
  · rw [e _ (GlobalTheory.OrientedHeis.theta_smul c hf), e _ hf, h.smul c f hf]
  · have hfun : (fun w => ℓ' (heisO ψ S T w f)) = fun w => ℓ (heisO ψ S T w f) :=
      funext fun w => e _ (hθ w f hf)
    rw [hfun]
    exact h.cont f hf
  · obtain ⟨C, hC⟩ := h.bdd f hf
    exact ⟨C, fun w => (e _ (hθ w f hf)).symm ▸ hC w⟩
  · have hfun : (fun w => α w * ℓ' (heisO ψ S T w f)) = fun w => α w * ℓ (heisO ψ S T w f) :=
      funext fun w => by rw [e _ (hθ w f hf)]
    rw [hfun, e _ hs]
    exact h.sup f hf m α hα hs

theorem decay_of_le {V : HSp D} {F : GA D V → ℂ} (hF : RapidDec V F) (C : ℝ) (a k : ℕ) :
    ∃ C' : ℝ, ∀ (g : GA D V) (t : ℝ), 0 ≤ t → t ≤ C * quotHeight V g ^ a → ‖F g‖ * t ^ k ≤ C' := by
  obtain ⟨-, -, hd⟩ := hF
  obtain ⟨C₀, hC₀⟩ := hd (a * k)
  refine ⟨|C| ^ k * max C₀ 0, fun g t ht0 htle => ?_⟩
  have hq : (0 : ℝ) ≤ quotHeight V g ^ a := pow_nonneg (le_trans zero_le_one (one_le_quotHeight V g)) a
  have ht : t ≤ |C| * quotHeight V g ^ a := htle.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hq)
  calc ‖F g‖ * t ^ k ≤ ‖F g‖ * (|C| * quotHeight V g ^ a) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 ht k) (norm_nonneg _)
    _ = |C| ^ k * (‖F g‖ * quotHeight V g ^ (a * k)) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ |C| ^ k * max C₀ 0 :=
        mul_le_mul_of_nonneg_left ((hC₀ g).trans (le_max_left _ _)) (pow_nonneg (abs_nonneg _) _)

theorem perAll_tame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ σ : ℕ) (B : BesL D σ) (J : JacL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om₀ : Om B.V₀ J.W₀), IsWeilDatumO ψ B.V₀ J.W₀ χ χ' om₀ → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ), RapidDec B.A φ → RapidDec J.W G → Tame ψ B.V₀ J.W₀ (J.perAll ψ B om₀ φ G) := by
  intro D ψ ρ σ B J χ χ' om₀ hW φ G hφ hG
  have hψ : IsStdChar D ψ (-1) := hW.std
  have hψc : Continuous ψ := hψ.1.1
  have hψn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have hGc : Continuous G := hG.2.1
  have hφc : Continuous φ := hφ.2.1
  haveI : SecondCountableTopology (flagN J.d) := TopologicalSpace.Subtype.secondCountableTopology _
  have hF : J.v0.μ J.v0.𝓕 < ⊤ :=
    GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol J.W₀ J.v0.μ J.v0.𝓕 J.v0.haar J.v0.fund
  have hFA : B.vA.μ B.vA.𝓕 < ⊤ :=
    GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol B.A B.vA.μ B.vA.𝓕 B.vA.haar B.vA.fund
  have hN : J.vN.ν J.vN.𝓝 = 1 := J.vN.unit.2.2
  haveI : IsFiniteMeasure (J.v0.μ.restrict J.v0.𝓕) := isFiniteMeasure_restrict.mpr hF.ne
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.mpr hFA.ne
  haveI : IsFiniteMeasure (J.vN.ν.restrict J.vN.𝓝) :=
    isFiniteMeasure_restrict.mpr (by rw [hN]; exact ENNReal.one_ne_top)
  have hpf : Continuous (psiFlag ψ J.d) := GlobalTheory.Unf.EvalCont.continuous_psiFlag hψc J.d
  have hcen : Continuous (cenT J.d B.L (yZero B.L ρ B.ζ)) := GlobalTheory.Unf.EvalCont.continuous_cenT J.d B.L _
  have hpt : Continuous (ptT J.d B.L (yZero B.L ρ B.ζ)) := GlobalTheory.Unf.EvalCont.continuous_ptT J.d B.L _
  have hn : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A => (y.1.2 : GA D J.W) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hh1 : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A => y.1.1 :=
    continuous_fst.comp continuous_fst
  have hx : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A => (y.1.2 : GA D J.W) * J.d.emb0 y.1.1 :=
    hn.mul (J.d.continuous_embed.comp hh1)
  have hgg : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A => B.o.emb (y.2, 1) :=
    B.o.continuous_emb.comp (continuous_snd.prodMk continuous_const)
  have hww : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A =>
      (B.o.resS J.W₀).symm (0, ptT J.d B.L (yZero B.L ρ B.ζ) (y.1.2 : GA D J.W)) :=
    (B.o.continuous_resS_symm J.W₀).comp (continuous_const.prodMk (hpt.comp hn))
  have hcc : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A =>
      G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1) * star (psiFlag ψ J.d (y.1.2 : GA D J.W)) * φ y.2 *
        ψ (cenT J.d B.L (yZero B.L ρ B.ζ) (y.1.2 : GA D J.W)) :=
    (((hGc.comp hx).mul (hpf.comp hn).star).mul (hφc.comp continuous_snd)).mul (hψc.comp (hcen.comp hn))
  obtain ⟨C₁, a₁, hC₁⟩ := GlobalTheory.T.unitaryQuotientHeight_orthogonalSum_comparable D B.V₀ B.A B.L B.o
  obtain ⟨C₂, a₂, hC₂⟩ := GlobalTheory.T.unitaryQuotientHeight_comparable_wittDecomposition D J.W J.W₀ ρ J.d
  have key : ∀ k : ℕ, Integrable (fun y : (GA D J.W₀ × flagN J.d) × GA D B.A =>
      ‖G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1) * star (psiFlag ψ J.d (y.1.2 : GA D J.W)) * φ y.2 *
        ψ (cenT J.d B.L (yZero B.L ρ B.ζ) (y.1.2 : GA D J.W))‖ *
        (quotHeight B.V₀ (B.o.emb (y.2, 1)) * quotHeight J.W₀ y.1.1) ^ k)
      (((J.v0.μ.restrict J.v0.𝓕).prod (J.vN.ν.restrict J.vN.𝓝)).prod (B.vA.μ.restrict B.vA.𝓕)) := by
    intro k
    obtain ⟨K₁, hK₁⟩ := decay_of_le hφ C₁ a₁ k
    obtain ⟨K₂, hK₂⟩ := decay_of_le hG C₂ a₂ k
    have hq : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A =>
        (quotHeight B.V₀ (B.o.emb (y.2, 1)) * quotHeight J.W₀ y.1.1) ^ k :=
      (((continuous_quotHeight B.V₀).comp hgg).mul ((continuous_quotHeight J.W₀).comp hh1)).pow k
    refine Integrable.mono' (integrable_const (K₁ * K₂)) (hcc.norm.mul hq).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    have q1 : 0 ≤ quotHeight B.V₀ (B.o.emb (y.2, 1)) := zero_le_one.trans (one_le_quotHeight _ _)
    have q2 : 0 ≤ quotHeight J.W₀ y.1.1 := zero_le_one.trans (one_le_quotHeight _ _)
    have b1 := hK₁ y.2 _ q1 (hC₁ y.2).2
    have b2 := hK₂ _ _ q2 (hC₂ y.1.2 y.1.2.2 y.1.1).1
    have n1 : ‖star (psiFlag ψ J.d (y.1.2 : GA D J.W))‖ = 1 := by
      rw [norm_star]; unfold psiFlag psiE; exact hψn _
    have p1 : 0 ≤ ‖φ y.2‖ * quotHeight B.V₀ (B.o.emb (y.2, 1)) ^ k := by positivity
    have p2 : 0 ≤ ‖G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1)‖ * quotHeight J.W₀ y.1.1 ^ k := by positivity
    rw [Real.norm_of_nonneg (by positivity), norm_mul, norm_mul, norm_mul, n1, hψn, mul_pow]
    calc ‖G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1)‖ * 1 * ‖φ y.2‖ * 1 *
          (quotHeight B.V₀ (B.o.emb (y.2, 1)) ^ k * quotHeight J.W₀ y.1.1 ^ k)
        = (‖φ y.2‖ * quotHeight B.V₀ (B.o.emb (y.2, 1)) ^ k) *
          (‖G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1)‖ * quotHeight J.W₀ y.1.1 ^ k) := by ring
      _ ≤ K₁ * K₂ := mul_le_mul b1 b2 p2 (p1.trans b1)
  obtain ⟨hint, htame⟩ := GlobalTheory.T.weilKernelFunctional_superposition_isTame D ψ B.V₀ J.W₀ χ χ' om₀ hW ((GA D J.W₀ × flagN J.d) × GA D B.A)
    (((J.v0.μ.restrict J.v0.𝓕).prod (J.vN.ν.restrict J.vN.𝓝)).prod (B.vA.μ.restrict B.vA.𝓕))
    (fun y => G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1) * star (psiFlag ψ J.d (y.1.2 : GA D J.W)) * φ y.2 *
        ψ (cenT J.d B.L (yZero B.L ρ B.ζ) (y.1.2 : GA D J.W)))
    (fun y => B.o.emb (y.2, 1)) (fun y => y.1.1)
    (fun y => (B.o.resS J.W₀).symm (0, ptT J.d B.L (yZero B.L ρ B.ζ) (y.1.2 : GA D J.W)))
    hcc.measurable hgg hh1 hww key
  refine tame_congr hψ htame fun Ξ hΞ => ?_
  have hI := hint Ξ hΞ
  rw [MeasureTheory.integral_prod _ hI, MeasureTheory.integral_prod _ hI.integral_prod_left]
  simp only [JacL.perAll, fjAll, fjAllFun,
    GlobalTheory.Unf.fjKer_eq_om_apply D ψ J.W J.W₀ B.V₀ B.A B.L ρ J.d B.o B.ζ χ χ' om₀ hW Ξ hΞ,
    ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (ae_of_all _ fun h => ?_)
  refine MeasureTheory.integral_congr_ae (ae_of_all _ fun n => ?_)
  refine MeasureTheory.integral_congr_ae (ae_of_all _ fun h₀ => ?_)
  dsimp only
  ring

end GlobalTheory.PerAllTame

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPeriodAllDataIsTameThetaFunctionalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiPeriod_all_data_isTameThetaFunctional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ σ : ℕ) (B : BesL D σ) (J : JacL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om₀ : Om B.V₀ J.W₀), IsWeilDatumO ψ B.V₀ J.W₀ χ χ' om₀ → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ), RapidDec B.A φ → RapidDec J.W G → Tame ψ B.V₀ J.W₀ (J.perAll ψ B om₀ φ G) := by
  first | exact @GlobalTheory.PerAllTame.perAll_tame | exact GlobalTheory.PerAllTame.perAll_tame | (intros; apply GlobalTheory.PerAllTame.perAll_tame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPeriodGivesBesselPeriodOfLift
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.UpBessel

theorem upBF : ∀ D : D7, UpBF D := by
  intro D ψ ρ B J s 𝒮 Γ₀ K hL L' ζ' hζ' l χA χz χ' oma omz hχ hWa hWz φ G hφ hG hK Ξ₁ Ξ₂ hΞ₁ hΞ₂ hbox hJ
  by_contra hnone
  push_neg at hnone

  have hstd : IsStdChar D ψ (-1) := s.weil.std
  have hℓ : Tame ψ B.V₀ J.W₀ (J.perAll ψ B s.om₀ φ G) :=
    GlobalTheory.T.fourierJacobiPeriod_all_data_isTameThetaFunctional D ψ ρ ρ B J s.χV s.χW s.om₀ s.weil₀ φ G hφ hG

  have hkill : ∀ Φ ∈ 𝒮, J.perAll ψ B s.om₀ φ G (flBF s Φ) = 0 :=
    GlobalTheory.T.vanishing_descends_bessel_to_fourierJacobi D ψ ρ B J s 𝒮 Γ₀ K hL φ G hφ hG hK hnone
  obtain ⟨Φ₁, hΦ₁, hΦ₁ne⟩ := hL.ne

  have hall : ∀ f, VacG ψ B.V₀ J.W₀ Γ₀ f → J.perAll ψ B s.om₀ φ G f = 0 := by
    refine GlobalTheory.T.tame_functional_vacuum_irreducibility D ψ hstd B.V₀ J.W₀ Γ₀ _ hℓ (flBF s Φ₁) (hL.vac Φ₁ hΦ₁) hΦ₁ne ?_
    intro w hw
    have hcomm := (GlobalTheory.FlatHeis.flatAt_heisO D ψ hstd B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.vU
      (xZero J.d) (yZero B.V₀ ρ (vecB B.o B.ζ)) Φ₁ (hL.theta Φ₁ hΦ₁)).2.1 w
    have hflat : flBF s (heisO ψ B.V J.W (B.d.ext0 J.W (J.d.inc0 B.V₀ w)) Φ₁) =
        heisO ψ B.V₀ J.W₀ w (flBF s Φ₁) := hcomm
    rw [← hflat]
    exact hkill _ (hL.core Φ₁ hΦ₁ w hw)

  have h0 := hall _ hbox
  rw [GlobalTheory.T.periodAllData_products_eq_fourierJacobiPeriod D ψ ρ B J s L' ζ' hζ' l χA χz χ' oma omz hχ hWa hWz φ G Ξ₁ Ξ₂ hΞ₁ hΞ₂] at h0
  exact hJ h0

end GlobalTheory.UpBessel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPeriodGivesBesselPeriodOfLiftStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_period_gives_bessel_period_of_lift : ∀ D : D7, UpBF D := by
  first | exact @GlobalTheory.UpBessel.upBF | exact GlobalTheory.UpBessel.upBF | (intros; apply GlobalTheory.UpBessel.upBF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselNonvanishingTower
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.AscRungB

theorem rapidDec_star {D : D7} {V : HSp D} {f : GA D V → ℂ} (h : RapidDec V f) : RapidDec V (star f) := by
  first
  | exact h.conj
  | exact RapidDec.of_le h (fun γ hγ g => by simp only [Pi.star_apply]; rw [h.left hγ g])
      h.continuous.star (fun g => by simp only [Pi.star_apply, norm_star, le_refl])

theorem exists_step {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    {χV χW : (AE D)ˣ →* Circle} {om : Om V W} (h : IsWeilDatumO ψ V W χV χW om) (vW : GlobalTheory.Unf.Vol W) :
    ∃ s : Step ψ V V₀ W W₀ ρ σ, s.χV = χV ∧ s.χW = χW ∧ s.om = om ∧ s.vW = vW := by
  have hDesc := GlobalTheory.Unf.descent_of_weilDatumExists D (GlobalTheory.WeilDatumExistence.weilDatumExists D)
  obtain ⟨om₁, h₁⟩ := (hDesc ψ V W χV χW om h).1 V₀ ρ dV
  obtain ⟨om₀, h₀⟩ := (hDesc ψ V₀ W χV χW om₁ h₁).2 W₀ σ dW
  obtain ⟨vS⟩ := GlobalTheory.Unf.VolExist.nonempty_volM D W.rank ρ
  obtain ⟨vT⟩ := GlobalTheory.Unf.VolExist.nonempty_volM D σ V₀.rank
  obtain ⟨vU⟩ := GlobalTheory.Unf.VolExist.nonempty_volU D ρ
  exact ⟨⟨χV, χW, om, om₀, h, h₀, vW, vS, vT, vU⟩, rfl, rfl, rfl, rfl⟩

theorem rungB : FockTot → PartFixed → RungB := by
  intro hF hP
  unfold RungB OnTower
  intro D hD T L μ0 hL sc G W M hM v F ΓL _hEnds hGood Ψ hΨ u hu k h hJ

  have hi : 2 * k + 1 < D.R.m := by omega
  obtain ⟨hw1, hw2, hodd, -, hdepiff, hdn, hpart, hpartEq, hhaar, hfund⟩ :=
    GlobalTheory.T.gridConjugation_weilData_inverseCharacter D hD T L μ0 hL sc G W M hM (2 * k + 1) hi
  obtain ⟨hχS, hχT⟩ := hodd (odd_two_mul_add_one k)
  obtain ⟨hrap, hchain⟩ := hΨ
  obtain ⟨f, hdep, hΨeq⟩ := hchain (2 * k + 1) hi
  obtain ⟨χ', omz, hwz, ρ, Φ, Φ₀, hΦ₀, hne⟩ := hJ

  let vW : GlobalTheory.Unf.Vol (G.V (.grid (2 * k + 1) 0)) := ⟨M.ν _, M.fd _, hhaar, hfund⟩
  obtain ⟨s, hsV, hsW, hsom, hsvW⟩ := exists_step (F.dB k h) (F.dJ k h) hw1 vW
  obtain ⟨𝒮, Γ₀, hLoc, hvacS, hbox⟩ := hGood.bf k h s hsom

  set φ : GA D (G.V (.core (2 * k + 2))) → ℂ := star (Ψ (2 * k + 2))
  set G' : GA D (G.V (.grid (2 * k + 1) 0)) → ℂ := star (part W M ρ Φ u (2 * k + 1) (by omega))
  have hφ : RapidDec _ φ := rapidDec_star (hrap (2 * k + 2) h)
  have hG' : RapidDec _ G' := rapidDec_star (hu ρ Φ (2 * k + 1) (by omega))
  have hfix : ∀ k' ∈ lev G (.grid (2 * k + 1) 0), ∀ g, G' (g * k') = G' g := fun k' hk' g =>
    congrArg star (hP D hD T L μ0 hL sc G W M hM ρ Φ u (2 * k) (by omega) k' hk' g)

  have hvac1 : VacG W.ψ _ _ (latCore G (2 * k + 1)) (star f) := (hdepiff f).1 hdep
  obtain ⟨-, hlink⟩ := GlobalTheory.T.linkedLineVectors_invertible_on_theta_functions D W.ψ W.ψ_std (negSp F.Lz) (negSp F.Lz) (G.V (.core (2 * k + 1)))
    (F.ζ (k + 1)) (F.ζ k) (F.line (k + 1)) (F.line k) (F.lnk k)
  obtain ⟨Ξ₂, hΞ₂, hΦ₀eq⟩ := hlink Φ₀ hΦ₀.1
  have hbox' := hbox (star f) Ξ₂ hvac1 hΞ₂ (by rw [← hΦ₀eq]; exact hΦ₀)

  have hlift : liftT (omCore W (2 * k + 1)) (v (2 * k + 2)).μ (v (2 * k + 2)).𝓕 φ (star f) = star (Ψ (2 * k + 1)) := by
    rw [hΨeq]; exact (hdn v f (Ψ (2 * k + 2))).symm
  have hJper : (F.jac v k h).per W.ψ (F.ζ k) omz
      (liftT (omCore W (2 * k + 1)) (v (2 * k + 2)).μ (v (2 * k + 2)).𝓕 φ (star f)) G'
      (fun w => star (Ξ₂ ((F.lnk k).κ _ w))) ≠ 0 := by
    rw [hlift, ← hΦ₀eq]; exact hne
  have hsχ : s.χV = (G.ch.chi (D.R.m - (2 * k + 1)))⁻¹ * L.eta := by rw [hsV, hχS]
  have hWA : IsWeilDatumO W.ψ _ _ (G.ch.chi (D.R.m - (2 * k + 1)))⁻¹ s.χW (omCore W (2 * k + 1)) := by
    rw [hsW, hχT]; exact hw2
  obtain ⟨Φ₁, hΦ₁S, hper₁⟩ := GlobalTheory.T.fourierJacobi_period_gives_bessel_period_of_lift D W.ψ k (F.bes v k h) (F.jac v k h) s 𝒮 Γ₀ _ hLoc (negSp F.Lz) (F.ζ k)
    (F.line k) (F.lnk k) _ _ χ' (omCore W (2 * k + 1)) omz hsχ hWA hwz φ G' hφ hG' hfix (star f) Ξ₂ hvac1.1 hΞ₂ hbox' hJper

  set ℓ : (WO (G.V (.grid (2 * k + 2) 0)) (G.V (.grid (2 * k + 1) 0)) → ℂ) → ℂ :=
    fun Φ' => (F.bes v k h).per W.ψ φ (liftS (omRow W (2 * k + 1)) vW.μ vW.𝓕 G' Φ')
  have htame : Tame W.ψ _ _ ℓ :=
    (GlobalTheory.T.thetaLift_periods_isTameThetaFunctional D W.ψ _ vW G' hG').1 k (F.bes v k h) _ _ (omRow W (2 * k + 1)) hw1 φ hφ
  have hℓ₁ : ℓ Φ₁ ≠ 0 := by
    have e : s.lift G' Φ₁ = liftS (omRow W (2 * k + 1)) vW.μ vW.𝓕 G' Φ₁ := by
      unfold GlobalTheory.Unf.Step.lift; rw [hsom, hsvW]
    rw [e] at hper₁; exact hper₁

  by_contra hall
  apply hℓ₁
  refine hF D hD T L μ0 hL sc G W M hM ⟨2 * k + 1, hi⟩ ℓ htame ?_ Φ₁ (hvacS Φ₁ hΦ₁S)
  intro κ P
  let ρ' : G.RealVec := Function.update ρ ⟨2 * k + 1, hi⟩ P
  let Φ' : G.Datum := Function.update Φ ⟨2 * k + 1, hi⟩ κ
  have hagree : ∀ j : Fin D.R.m, j.1 < 2 * k + 1 → ρ' j = ρ j ∧ Φ' j = Φ j := by
    intro j hj
    have hne' : j ≠ ⟨2 * k + 1, hi⟩ := fun e => by rw [e] at hj; exact lt_irrefl _ hj
    exact ⟨Function.update_of_ne hne' _ _, Function.update_of_ne hne' _ _⟩
  have hdat : W.datum ρ' Φ' ⟨2 * k + 1, hi⟩ = W.fock (.chi (2 * k + 1) 0) (W.cosVec (2 * k + 1) κ) P := by
    simp only [GlobalTheory.ChiGrid.GridData.Weil.datum, ρ', Φ', Function.update_self]
  have htop := hpart ρ' Φ' u
  rw [hpartEq ρ' Φ' ρ Φ u hagree, hdat] at htop
  have h0 : (F.bes v k h).per W.ψ φ (star (part W M ρ' Φ' u (2 * k + 1 + 1) hi)) = 0 := by
    by_contra hne0
    exact hall ⟨ρ', Φ', hne0⟩
  rw [htop] at h0
  exact h0

end GlobalTheory.AscRungB

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselNonvanishingTowerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_to_bessel_nonvanishing_tower : FockTot → PartFixed → RungB := by
  first | exact @GlobalTheory.AscRungB.rungB | exact GlobalTheory.AscRungB.rungB | (intros; apply GlobalTheory.AscRungB.rungB <;> assumption)
end

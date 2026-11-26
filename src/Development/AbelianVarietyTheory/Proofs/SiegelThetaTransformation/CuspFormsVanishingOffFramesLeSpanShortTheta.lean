module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.StableFormsEqSumThetaSeriesFreeLowerRows
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsComponentsLatticesMovedToLevelFamily
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdmissibleIndicatorFunctions
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumEvalComplexPointEqClassical

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortSeriesReadingsEqClassicalThetaSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortSeriesReadingsEqClassicalThetaSeries
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding Unf GoodEmb IsUnf rdU laU perFr
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ReadAll

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}

theorem isSB_smul' (a : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (a • φ) := by
  obtain ⟨R, hR, hsupp, hper⟩ := h
  refine ⟨R, hR, fun x hx => hsupp x fun h0 => hx (by simp [h0]), fun x y hy => ?_⟩
  simp only [Pi.smul_apply, hper x y hy]

theorem isSB_finsum {J : Sort*} {f : J → TF n g} (h : ∀ i, IsSB (f i)) : IsSB (∑ᶠ i, f i) := by
  rw [finsum_def']
  split_ifs with hfin
  · exact Finset.sum_induction _ IsSB
      (fun φ ψ hφ hψ => (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) φ ψ hφ hψ).1)
      isSB_zero (fun i _ => h i.down)
  · exact isSB_zero

theorem isSB_phiF {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
    (hs : IsSympl X bas) (he : Even n) (D : SW.Level X) (𝔐 : Ideal (𝓞 E)) (hn : r ≤ n)
    (v₀ : Lt E r → TF n g) (L : Lt E r) (Λ : Lt E n) (hv : IsSB (v₀ L)) :
    IsSB (phiF bas D 𝔐 hn v₀ L Λ) := by
  have hH : ∀ (y : Matrix (Fin n) (Fin r) E) (φ : TF n g), IsSB φ → IsSB (heisG X bas y φ) :=
    fun y φ hφ => ((heisG_laws E r X g bas idx n hs he).2.2.2 y φ hφ).1
  have hP : IsSB (projA X bas D.w (tens Λ (D.sh L)) (v₀ L)) := by
    unfold projA
    refine isSB_smul' _ (isSB_finsum fun ψ => isSB_finsum fun hψ => ?_)
    obtain ⟨y, -, rfl⟩ := hψ
    exact isSB_smul' _ (hH y _ hv)
  unfold phiF unitv
  exact isSB_finsum fun c => isSB_smul' _ (hH _ _ (isSB_smul' _ hP))

theorem perFr_cast {X' X : Data E r} (h : SameSp X' X) (x : Frame X'.Ψ r) (v : Fin r → E) (τ : E →+* ℂ)
    (i : ℕ) : Formalism.L2.PjFree.perFr X' x v τ i = Formalism.L2.PjFree.perFr X (castFr h.psi x) v τ i := by
  obtain ⟨hp, hg, h0, hxi, hka⟩ := h
  cases X'
  cases X
  dsimp only at hp hg h0 hxi hka
  subst hp hg h0 hxi hka
  unfold Formalism.L2.PjFree.perFr
  rfl

set_option maxHeartbeats 400000 in
private theorem differentiableOn_and_bchar_equivariant_lact_castFr {X' X : Data E r} (h : SameSp X' X) {ga : GL (Fin r) E} (hUn : IsUn X ga)
    {la : Wt X.Ψ r} {la' : Wt X'.Ψ r} (hl : ∀ (τ : X.Ψ) i, la τ i = la' ⟨τ.1, by rw [h.psi]; exact τ.2⟩ i)
    (Q : Frame X.Ψ r → ℂ) (hQ : DifferentiableOn ℂ Q X.dom)
    (hw : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x) (c0 : ℂ) :
    DifferentiableOn ℂ (fun x => c0 * Q (lact ga (castFr h.psi x))) X'.dom ∧
      ∀ x ∈ X'.dom, ∀ b ∈ Bor X'.Ψ r,
        c0 * Q (lact ga (castFr h.psi (rmul x b))) = bchar la' b * (c0 * Q (lact ga (castFr h.psi x))) := by
  have hm : ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom := fun x hx =>
    GlobalTheory.Dict.Extend.lact_mem hUn (GlobalTheory.Dict.SameSp.castFr_mem_dom h hx)
  refine ⟨(hQ.comp ((GlobalTheory.Dict.Extend.differentiable_lact ga).comp
    (GlobalTheory.Dict.Pull.cast_diff h.psi)).differentiableOn hm).const_mul c0, fun x hx b hb => ?_⟩
  rw [GlobalTheory.Dict.Pull.cast_rmul, GlobalTheory.Dict.Extend.lact_rmul, hw _ (hm x hx) _ (GlobalTheory.Dict.Pull.cast_bor h.psi hb),
    GlobalTheory.Dict.Pull.cast_bchar h.psi hl]
  ring

end GlobalTheory.Dict.ReadAll


open GlobalTheory.Dict.ReadAll GlobalTheory.Dict.Pull GlobalTheory.Dict.Extend in
theorem GlobalTheory.Dict.rdU_short_eq_thP : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ (W : UW U) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ (Dc : Dic Dw c σ X W.g Dw.p n a) (D : SW.Level X) (hn : r ≤ n), Dc.e = W.e → LevTie d σ ph D hn → ∀ v₀ : Lt E r → TF n W.g, (∀ L ∈ D.lats, IsVac X Dc.bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ x0 : Fin n → Dw.La, ∃ u : Lt E n → ℕ → ℂ, (∀ Λ ∈ Vset E n d.l₂.M, ∀ N, NOK Λ N d.l₂.M → u Λ N ≠ 0) ∧ ∀ (k : U.Comp) (h : SameSp (U.X k) X) (ga : GL (Fin r) E) (δ : Dw.La →ₗ[𝓞 E] (Fin r → E)), IsUn X ga → mapL ga (U.X k).Λ ∈ D.lats → IsMark l (mapL ga (U.X k).Λ) (mvMap ga (W.mark k)) → IsDual X l (σ (zetaM c)) (mapL ga (U.X k).Λ) (mvMap ga (W.mark k)) δ → IsBaseClassLevelAdapted d D hn x0 δ → ∃ C : ℂ, C ≠ 0 ∧ ∀ Λ ∈ Vset E n d.l₂.M, ∀ N, NOK Λ N d.l₂.M → ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ f ∈ sec Xo c a n, IsShortRule Xo c d (⟨Λ⟩ : GenLat E n) N x0 P f → ∀ x ∈ (U.X k).dom, rdU U f k x = C * u Λ N * thP X Dc.hr Dc.bas Dc.idx (phiF Dc.bas D (Mfr l) hn v₀ (mapL ga (U.X k).Λ) Λ) (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P)) (lact ga (castFr h.psi x)) := by
  intro hCI E _ _ _ H Dw l Xo c n d σ r U hg hU hr hlev hnab hunitC ph ψ x₀ hpin W X a hdom Dc D hn hDe
    htie v₀ hvac x0
  letI : Algebra c.F ℂ := σ.toAlgebra
  letI : Algebra d.c₂.F ℂ := (σ.comp d.eF.symm.toAlgHom.toRingHom).toAlgebra
  have hU' := hU
  unfold Formalism.L2.PjFree.IsUnf at hU'
  obtain ⟨hrpq, hk, -, -, hsec, -⟩ := hU'
  obtain ⟨u, hu0, hmain⟩ := GlobalTheory.Dict.ShortPt.shortRule_value hCI E H Dw l Xo c n d
    (fun t => by show σ (d.eF.symm (d.eF t)) = σ t; rw [AlgEquiv.symm_apply_apply])
    hlev hnab (fun y₂ => hunitC _ y₂) ph ψ x₀ hpin r W.g Dw.p X a Dc D hn hdom.2 hrpq htie v₀ hvac x0
  refine ⟨u, hu0, ?_⟩
  intro k h ga δ hUn hlat hmark hdual hx0
  obtain ⟨ρ, hρ, hall⟩ := hmain _ hlat _ δ hmark hdual hx0
  rw [hDe] at hall
  have hself : SelfD (U.X k) (U.X k).Λ := (GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r U hg hU hr W k).2.1
  have hvL : IsSB (v₀ (mapL ga (U.X k).Λ)) := (hvac _ hlat).1
  have hwt : ∀ (τ : X.Ψ) (i : Fin r),
      wtOf X Dc.hr Dc.k Dc.k' n τ i = laU U a n k ⟨τ.1, by rw [h.psi]; exact τ.2⟩ i := by
    intro τ i
    rw [Dc.wt_eq]
    unfold wtX Formalism.L2.PjFree.laU
    simp only [h.p0]
  let Jx := {q : Lt E n × ℕ × (HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) ×
      (sec Xo c a n) // q.1 ∈ Vset E n d.l₂.M ∧ NOK q.1 q.2.1 d.l₂.M ∧
        IsShortRule Xo c d (⟨q.1⟩ : GenLat E n) q.2.1 x0 q.2.2.1.1 q.2.2.2.1}
  let R : Jx → Frame (U.X k).Ψ r → ℂ := fun i => rdU U i.1.2.2.2.1 k
  let T : Jx → Frame (U.X k).Ψ r → ℂ := fun i x => u i.1.1 i.1.2.1 *
    thP X Dc.hr Dc.bas Dc.idx (phiF Dc.bas D (Mfr l) hn v₀ (mapL ga (U.X k).Λ) i.1.1)
      (MvPolynomial.rename Dc.eL (MvPolynomial.map σ i.1.2.2.1.1)) (lact ga (castFr h.psi x))
  have hol : ∀ i, DifferentiableOn ℂ (R i) (U.X k).dom ∧ DifferentiableOn ℂ (T i) (U.X k).dom ∧
      ∀ x ∈ (U.X k).dom, ∀ b ∈ Bor (U.X k).Ψ r,
        R i (rmul x b) = bchar (laU U a n k) b * R i x ∧ T i (rmul x b) = bchar (laU U a n k) b * T i x := by
    intro i
    have hs := hsec a n hdom i.1.2.2.2.1 i.1.2.2.2.2 k
    have ht := GlobalTheory.SW.theta_holomorphic_weight E r X W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hdom.2 Dc.k Dc.k' _
      (GlobalTheory.Dict.ReadAll.isSB_phiF Dc.idx Dc.sympl hdom.2 D (Mfr l) hn v₀ _ i.1.1 hvL) _ (Dc.mem _ i.1.2.2.1.2)
    obtain ⟨hd, hw⟩ := GlobalTheory.Dict.ReadAll.differentiableOn_and_bchar_equivariant_lact_castFr h hUn hwt _ ht.1 ht.2.1 (u i.1.1 i.1.2.1)
    exact ⟨hs.1, hd, fun x hx b hb => ⟨hs.2.1 x hx b hb, hw x hx b hb⟩⟩
  have unit : ∀ x ∈ (U.X k).dom, IsUnitFr (U.X k) x → ∃ κ : ℂ, ‖κ‖ = ρ ∧ ∀ i, R i x = κ * T i x := by
    intro x hx hunit
    obtain ⟨Dc', hDe', -⟩ := GlobalTheory.Dict.exists_dic E H Dw l c σ r W.g n (U.X k) a W.e hg hrpq (hk k).1 (hk k).2
      hself hdom
    have hpv' : ∀ x v j, pv (U.X k) Dc'.idx x v j =
        perFr (U.X k) x v (Formalism.L2.PjFree.relab c σ (W.e j).1) (W.e j).2 := by
      rw [← hDe']; exact Dc'.per_eq
    have hrt' : ∀ j, rowType (U.X k) (Dc'.idx j) = Formalism.L2.PjFree.relab c σ (W.e j).1 := by
      rw [← hDe']; exact Dc'.ty_eq
    obtain ⟨A, hMk, θ, hRd, hMn⟩ := GlobalTheory.Dict.uw_anFib E H Dw l Xo c σ r U hg hU hr W k Dc'.bas Dc'.idx
      Dc'.sympl hpv' hrt' ⟨x, hx⟩ hunit
    have hpv : ∀ v, pv (U.X k) Dc'.idx x v = pv X Dc.idx (castFr h.psi x) v := by
      intro v
      funext j
      rw [hpv', Dc.per_eq, hDe, GlobalTheory.Dict.ReadAll.perFr_cast h]
    have hrow : ∀ j, rowType (U.X k) (Dc'.idx j) = rowType X (Dc.idx j) := by
      intro j
      rw [hrt', Dc.ty_eq, hDe]
    obtain ⟨hxm, hun, -, A', hRd', hMn', hMk'⟩ := GlobalTheory.Dict.anFib_move E H Dw l Xo c r W.g (U.X k) X h Dc'.bas
      Dc'.idx Dc.bas Dc.idx W.e x (U.X k).Λ (unC U k ⟨x, hx⟩) A ga Dc'.sympl Dc.sympl hx hself hUn hpv hrow
    obtain ⟨κ, hκn, hκ⟩ := hall _ hxm (hun hunit) _ A' θ (hMk' _ hMk) (hRd' θ hRd) (hMn' θ hMn)
    refine ⟨κ, hκn, fun i => ?_⟩
    have hev := hκ i.1.1 i.2.1 i.1.2.1 i.2.2.1 i.1.2.2.1.1 i.1.2.2.1.2 i.1.2.2.2.1 i.2.2.2
    have hrd : rdU U i.1.2.2.2.1 k x = evR Xo c i.1.2.2.2.1 (unC U k ⟨x, hx⟩) := by
      simp only [Formalism.L2.PjFree.rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hx]
      rfl
    simp only [R, T]
    rw [hrd]
    exact hev.trans (_root_.mul_assoc _ _ _)
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.Dict.const_of_norm_factor_unitFr E r (U.X k) (laU U a n k) Jx R T ρ hρ hol unit
  refine ⟨C, hC0, fun Λ hΛ N hN P hP f hf hsr x hx => ?_⟩
  have hx' := hC ⟨(Λ, N, ⟨P, hP⟩, ⟨f, hf⟩), hΛ, hN, hsr⟩ x hx
  simp only [R, T] at hx'
  rw [hx', _root_.mul_assoc]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortSeriesReadingsEqClassicalThetaSeriesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.short_series_readings_eq_classical_thetaSeries : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ (W : UW U) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ (Dc : Dic Dw c σ X W.g Dw.p n a) (D : SW.Level X) (hn : r ≤ n), Dc.e = W.e → LevTie d σ ph D hn → ∀ v₀ : Lt E r → TF n W.g, (∀ L ∈ D.lats, IsVac X Dc.bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ x0 : Fin n → Dw.La, ∃ u : Lt E n → ℕ → ℂ, (∀ Λ ∈ Vset E n d.l₂.M, ∀ N, NOK Λ N d.l₂.M → u Λ N ≠ 0) ∧ ∀ (k : U.Comp) (h : SameSp (U.X k) X) (ga : GL (Fin r) E) (δ : Dw.La →ₗ[𝓞 E] (Fin r → E)), IsUn X ga → mapL ga (U.X k).Λ ∈ D.lats → IsMark l (mapL ga (U.X k).Λ) (mvMap ga (W.mark k)) → IsDual X l (σ (zetaM c)) (mapL ga (U.X k).Λ) (mvMap ga (W.mark k)) δ → IsBaseClassLevelAdapted d D hn x0 δ → ∃ C : ℂ, C ≠ 0 ∧ ∀ Λ ∈ Vset E n d.l₂.M, ∀ N, NOK Λ N d.l₂.M → ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ f ∈ sec Xo c a n, IsShortRule Xo c d (⟨Λ⟩ : GenLat E n) N x0 P f → ∀ x ∈ (U.X k).dom, Formalism.L2.PjFree.rdU U f k x = C * u Λ N * thP X Dc.hr Dc.bas Dc.idx (phiF Dc.bas D (Mfr l) hn v₀ (mapL ga (U.X k).Λ) Λ) (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P)) (lact ga (castFr h.psi x)) := by
  first | exact @GlobalTheory.Dict.rdU_short_eq_thP | exact GlobalTheory.Dict.rdU_short_eq_thP | (intros; apply GlobalTheory.Dict.rdU_short_eq_thP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumMultiplierEqOneOnStabiliser
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumMultiplierTrivialPrincipalCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumMultiplierTrivialPrincipalCongruence
namespace GlobalTheory.VacMult

section Analytic

open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem factor_ratio {α : Type} (F F' : α → ℂ) (k : ℕ) (A B : ℂ) (hA : A ≠ 0) (z₀ : α) (h₀ : F z₀ ≠ 0)
    (h : ∀ z : Fin (k + 1) → α, A * ∏ i, F (z i) = B * ∏ i, F' (z i)) :
    ∃ κ : ℂ, κ ≠ 0 ∧ (∀ w, F' w = κ * F w) ∧ A = B * κ ^ (k + 1) := by
  have h1 : ∀ w, A * (F w * F z₀ ^ k) = B * (F' w * F' z₀ ^ k) := fun w => by
    simpa [Fin.prod_univ_succ] using h (Fin.cons w fun _ => z₀)
  have h2 : B * (F' z₀ * F' z₀ ^ k) ≠ 0 := by
    rw [← h1]
    exact mul_ne_zero hA (mul_ne_zero h₀ (pow_ne_zero _ h₀))
  have hB : B ≠ 0 := left_ne_zero_of_mul h2
  have h₀' : F' z₀ ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul h2)
  refine ⟨F' z₀ / F z₀, div_ne_zero h₀' h₀, fun w => ?_, ?_⟩
  · rw [div_mul_eq_mul_div, eq_div_iff h₀]
    refine mul_left_cancel₀ (mul_ne_zero hB (pow_ne_zero k h₀')) ?_
    linear_combination F w * h1 z₀ - F z₀ * h1 w
  · rw [div_pow]
    field_simp
    linear_combination h1 z₀

theorem scalar_eq_one {g n : ℕ} (hn : Even n) (σ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hσ : σ ∈ Matrix.symplecticGroup (Fin g) ℤ)
    (h8 : ∀ i j, (8 : ℤ) ∣ σ (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ σ (Sum.inr i) (Sum.inl j))
    (hdet : (8 : ℤ) ∣ σ.toBlocks₂₂.det - 1) (c₁ c₂ : Fin g → ℂ) (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2)
    (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) (τ τ' h h' Q Q' : Matrix (Fin g) (Fin g) ℂ)
    (hτ : τ ∈ SiegelH (Fin g)) (hu : IsUnit h.det) (e₁ : τ' = spAct σ τ)
    (e₂ : h' = ((jAut σ τ)⁻¹)ᵀ * h) (e₃ : h.det = (jAut σ τ).det * h'.det) (C a : ℂ) (hC : C ≠ 0)
    (hz : ∀ z : Fin n → Fin g → ℂ,
      C * h.det ^ (n / 2) * ∏ k, (cexp (Real.pi / 2 * ((h *ᵥ z k) ⬝ᵥ Q *ᵥ (h *ᵥ z k))) *
        thetaChar τ c₁ c₂ (h *ᵥ z k)) =
      a * (C * h'.det ^ (n / 2) * ∏ k, (cexp (Real.pi / 2 * ((h' *ᵥ z k) ⬝ᵥ Q' *ᵥ (h' *ᵥ z k))) *
        thetaChar τ' c₁ c₂ (h' *ᵥ z k)))) : a = 1 := by
  rcases n with _ | k
  · simpa [hC] using (hz 0).symm
  have hχ : ((ZMod.χ₄ ((σ.toBlocks₂₂.det : ℤ) : ZMod 4) : ℤ) : ℂ) = 1 := by
    have h4 : ((4 : ℕ) : ℤ) ∣ σ.toBlocks₂₂.det - 1 := Dvd.dvd.trans (by norm_num) hdet
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).2 h4
    rw [Int.cast_sub, Int.cast_one, sub_eq_zero] at this
    rw [this, map_one, Int.cast_one]
  have hl := theta_sq_transform_level_eight g σ hσ h8
  rw [hχ] at hl
  obtain ⟨w₀, hw₀⟩ : ∃ w, thetaChar τ c₁ c₂ w ≠ 0 := by
    obtain ⟨m, rfl⟩ := ThetaRatio.exists_eq_halfVec h₁
    obtain ⟨m', rfl⟩ := ThetaRatio.exists_eq_halfVec h₂
    by_contra hc
    push_neg at hc
    refine theta_ne_zero hτ (halfVec m) (halfVec m') (funext fun w => ?_)
    have := hc w
    rw [ThetaRatio.thetaChar_ofRealVec] at this
    exact this
  have hi : ∀ w, h *ᵥ (h⁻¹ *ᵥ w) = w := fun w => by
    rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hi' : ∀ w, h' *ᵥ (h⁻¹ *ᵥ w) = zAct σ τ w := fun w => by
    rw [e₂, ← mulVec_mulVec, hi, zAct]
  obtain ⟨κ, hκ, hF, hA⟩ := factor_ratio
    (fun z => cexp (Real.pi / 2 * ((h *ᵥ z) ⬝ᵥ Q *ᵥ (h *ᵥ z))) * thetaChar τ c₁ c₂ (h *ᵥ z))
    (fun z => cexp (Real.pi / 2 * ((h' *ᵥ z) ⬝ᵥ Q' *ᵥ (h' *ᵥ z))) * thetaChar τ' c₁ c₂ (h' *ᵥ z))
    k (C * h.det ^ ((k + 1) / 2)) (a * (C * h'.det ^ ((k + 1) / 2)))
    (mul_ne_zero hC (pow_ne_zero _ hu.ne_zero)) (h⁻¹ *ᵥ w₀)
    (mul_ne_zero (Complex.exp_ne_zero _) (by rwa [hi])) (fun z => by rw [hz z, mul_assoc a])
  have hκ2 := ThetaRatio.ratio_sq_eq_det_jAut g σ hσ h8 hl c₁ c₂ h₁ h₂ τ hτ
    (fun w => cexp (Real.pi / 2 * (zAct σ τ w ⬝ᵥ Q' *ᵥ zAct σ τ w) - Real.pi / 2 * (w ⬝ᵥ Q *ᵥ w))) κ
    (by
      simp only [zAct, mulVec, dotProduct]
      fun_prop)
    (fun w => Complex.exp_ne_zero _) (by simp [zAct]) hκ (fun w => by
      have := hF (h⁻¹ *ᵥ w)
      simp only [hi, hi', e₁] at this
      rw [Complex.exp_sub, ← mul_div_assoc, div_eq_iff (Complex.exp_ne_zero _)]
      linear_combination this)
  obtain ⟨m, hm⟩ := hn
  have hm' : (k + 1) / 2 = m := by omega
  have h'0 : h'.det ≠ 0 := right_ne_zero_of_mul (e₃ ▸ hu.ne_zero)
  rw [hm', hm, e₃, ← hκ2, ← two_mul, pow_mul, mul_pow] at hA
  refine mul_right_cancel₀ (mul_ne_zero hC (mul_ne_zero (pow_ne_zero m h'0)
    (pow_ne_zero m (pow_ne_zero 2 hκ)))) ?_
  linear_combination -hA

end Analytic

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem hostHalfRoot_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have h1 : (H.rt : E) ^ 2 = -(H.d : E) := by simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    simpa [map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h3 : τ H.rt ^ 2 = -(H.d : ℂ) := by simpa using congrArg τ h1
  have h4 : 2 * τ H.w0 = 1 + τ H.rt := by simpa [map_ofNat] using congrArg τ h2
  have h5 : (τ H.rt).re = 0 := by
    have a := congrArg Complex.re h3
    have b := congrArg Complex.im h3
    have c : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    simp only [pow_two, mul_re, mul_im, neg_re, neg_im, natCast_re, natCast_im, neg_zero] at a b
    by_contra h
    have : (τ H.rt).im = 0 := mul_left_cancel₀ h (by linarith)
    rw [this] at a
    nlinarith [mul_self_nonneg (τ H.rt).re]
  apply τ.injective
  rw [map_add (f := _), cc, IsCMField.complexEmbedding_complexConj, map_one, Complex.add_conj]
  have h6 := congrArg Complex.re h4
  simp only [add_re, one_re, h5, add_zero, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero] at h6
  exact_mod_cast h6

theorem wG_vac_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (H : Host E) (Dw : Datum H) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), r = Dw.p + Dw.q → Function.Injective φ → Submodule.span E (Set.range φ) = ⊤ → (∀ a b, ((Dw.EF a b : ℤ) : ℚ) = EF X (φ a) (φ b)) → ∀ L : Lt E r, SelfD X L → ∀ (M : ℕ), 3 ≤ M → ∀ ga : GL (Fin r) E, IsUn X ga → mapL ga L = L → (∀ u ∈ L, ∃ u' ∈ L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u') → ∀ v : TF n g, IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → wG X bas idx ga v = v := by
  intro E _ _ _ r X g bas idx n hs hn H Dw φ hr hφi hφs hφE L hL M hM ga hga hgL hgM v hv
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw' := hostHalfRoot_add_conj_eq_one H
  have hξ : cc (-(X.κ0 / 2)) = -(-(X.κ0 / 2)) := by
    have h1 : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
    rcases X.κ0_xi with h | h <;> simp [cc, h, h1, neg_div]
  obtain ⟨D, ψ, hp, hq, hψL, hψi, -, -, -, hψE⟩ := LatticeDatum.exists_datum_of_selfDual E H Dw r
    (-(X.κ0 / 2)) X.Gm φ L hξ ⟨hφi, hφs, X.Gm_herm, X.Gm_det, hφE⟩ hL.1 (TensLat.span_of_selfD X hL)
    (fun u => (hL.2 u).symm)
  replace hψE : ∀ a b, ((D.EF a b : ℤ) : ℚ) = EF X (ψ a) (ψ b) := hψE
  have hg : g = Module.finrank ℚ E / 2 * (D.p + D.q) := by
    have h1 := Fintype.card_congr idx
    have h2 := RealPlaceEmbeddings.two_card_Psi X
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h1
    rw [hp, hq, ← hr, ← h2, h1, Nat.mul_div_cancel_left _ two_pos]
  obtain ⟨bs, hbs, hb8⟩ := exists_symplectic_basis_adapted_mod_eight E H D g hg
  have hmem : ∀ u, u ∈ L ↔ ∃ a, ψ a = u := fun u => by rw [← hψL]; rfl
  let gi : Matrix (Fin r) (Fin r) E := ((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
  have hgi : ∀ u, (ga : Matrix (Fin r) (Fin r) E) *ᵥ gi *ᵥ u = u := gl_mulVec_inv_mulVec ga
  have hig : ∀ u, gi *ᵥ (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u := RecSum.inv_mulVec ga
  have hgaL : ∀ u ∈ L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u ∈ L := fun u hu => by
    rw [← hgL]
    exact ⟨u, hu, rfl⟩
  have hgiL : ∀ u ∈ L, gi *ᵥ u ∈ L := fun u hu => by
    rw [← hgL] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    exact (hig u').symm ▸ hu'
  obtain ⟨gam, hgam⟩ : ∃ gam : D.La ≃ₗ[𝓞 E] D.La, ∀ a, ψ (gam a) = gi *ᵥ ψ a := by
    choose f hf using fun a => (hmem _).1 (hgiL _ ((hmem _).2 ⟨a, rfl⟩))
    choose f' hf' using fun a => (hmem _).1 (hgaL _ ((hmem _).2 ⟨a, rfl⟩))
    exact ⟨{ toFun := f
             invFun := f'
             map_add' := fun a b => hψi (by rw [map_add (f := _), hf, hf, hf, map_add (f := _), mulVec_add])
             map_smul' := fun c a => hψi (by
               rw [map_smul, hf, hf, map_smul, RingHom.id_apply, mulVec_smul])
             left_inv := fun a => hψi (by rw [hf', hf, hgi])
             right_inv := fun a => hψi (by rw [hf, hf', hig]) }, hf⟩
  have hiso : ∀ a b, D.EF (gam a) (gam b) = D.EF a b := fun a b => by
    refine Int.cast_injective (α := ℚ) ?_
    rw [hψE, hψE, hgam, hgam, EF_def, ← hga, hgi, hgi, EF_def]
  have hfull : ∀ a, ∃ e, gam a = a + M • e := fun a => by
    obtain ⟨u, hu, he⟩ := hgM _ ((hmem _).2 ⟨gam a, rfl⟩)
    obtain ⟨e, rfl⟩ := (hmem _).1 hu
    refine ⟨-e, hψi ?_⟩
    rw [hgam, hgi, ← hgam] at he
    rw [map_add (f := _), map_nsmul, map_neg, he, smul_neg, add_neg_cancel_right]
  let N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
    Matrix.of fun u v => bs.symm (gam (bs (Pi.single v 1))) u
  obtain ⟨h8, hdet⟩ := AdaptedDet.blocks_det_mod_eight E H D g M bs gam N hb8 hM hiso hfull
    (fun _ _ => rfl)
  have hsum : ∀ m : Fin g ⊕ Fin g → ℤ, ψ (bs m) = ∑ j, m j • ψ (bs (Pi.single j 1)) := fun m => by
    have hm : m = ∑ j, m j • Pi.single j (1 : ℤ) := by
      funext j; simp [Pi.single_apply]
    conv_lhs => rw [hm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul]
  obtain ⟨c₁, c₂, C, hC, h₁, h₂, hth⟩ := GlobalTheory.T.periodCoordinateTheta_of_signedHeisenbergVacuum E r X g bas idx n hs hn _ hw hw' L hL v hv
    (fun j => ψ (bs (Pi.single j 1)))
    (fun u => by
      rw [hmem]
      exact ⟨fun ⟨a, ha⟩ => ⟨bs.symm a, by rw [← hsum, bs.apply_symm_apply, ha]⟩,
        fun ⟨m, hm⟩ => ⟨bs m, by rw [hsum, hm]⟩⟩)
    (fun i j => by rw [← hψE, hbs, Int.cast_neg])
  obtain ⟨x, hx⟩ := UnAct.exists_mem_dom X
  have hx' := hga.lact_mem hx
  obtain ⟨hu, hτ, -, -, hz⟩ := hth x hx _ _ rfl rfl
  obtain ⟨hu', hτ', -, -, hz'⟩ := hth _ hx' _ _ rfl rfl
  let P : Frame X.Ψ r → D.La →+ (Fin g → ℂ) := fun y =>
    { toFun := fun a => pv X idx y (ψ a)
      map_zero' := by rw [map_zero, pv, per_zero]; rfl
      map_add' := fun a b => by rw [map_add (f := _), pv, per_add]; rfl }
  have hnorm : ∀ y : Frame X.Ψ r,
      IsUnit (Matrix.of fun i k => pv X idx y (ψ (bs (Pi.single (Sum.inl k) 1))) i)⁻¹.det → ∀ k,
      (Matrix.of fun i k => pv X idx y (ψ (bs (Pi.single (Sum.inl k) 1))) i)⁻¹ *ᵥ
        P y (bs (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧
      (Matrix.of fun i k => pv X idx y (ψ (bs (Pi.single (Sum.inl k) 1))) i)⁻¹ *ᵥ
        P y (bs (Pi.single (Sum.inr k) 1)) =
      ((Matrix.of fun i k => pv X idx y (ψ (bs (Pi.single (Sum.inl k) 1))) i)⁻¹ *
        Matrix.of fun i k => pv X idx y (ψ (bs (Pi.single (Sum.inr k) 1))) i) *ᵥ Pi.single k 1 := by
    intro y hy k
    have e : ∀ s : Fin g → Fin g ⊕ Fin g, P y (bs (Pi.single (s k) 1)) =
        (Matrix.of fun i k => pv X idx y (ψ (bs (Pi.single (s k) 1))) i) *ᵥ Pi.single k 1 := fun s => by
      funext i
      simp [P]
    rw [e Sum.inl, e Sum.inr, mulVec_mulVec, mulVec_mulVec, nonsing_inv_mul _
      (isUnit_nonsing_inv_det_iff.1 hy), one_mulVec]
    exact ⟨rfl, rfl⟩
  obtain ⟨σ, hσ, hσe, e₁, e₂, e₃⟩ := PeriodChange.period_change E H D g bs gam N (P x)
    (P (lact ga x)) _ _ _ _ hbs hiso (fun _ _ => rfl)
    (fun a => by
      change pv X idx _ _ = pv X idx _ _
      rw [hgam, pv, pv, ← per_lact x hga, hgi])
    (hnorm x hu) (hnorm _ hu') hτ hτ' hu
  have hv' := RecSum.isVac_wG (idx := idx) hs hn hga hv
  rw [hgL] at hv'
  have ha := (TensVac.vacua E r X g bas idx n hs hn _ hw hw' L hL 1 _ (stdL_mem_Vset 1)).2.1
    _ _ hv hv'.1 hv'.2.2
  have h1 := (wG_laws E r X g bas idx n hs hn ga hga v hv.1).2.1 x hx
  rw [ha, UnAct.thA_smul] at h1
  have h2 := scalar_eq_one hn σ hσ (fun i j => by rw [hσe]; exact h8 j i)
    (by rw [hσe, Matrix.toBlocks_fromBlocks₂₂, Matrix.det_transpose]; exact hdet)
    c₁ c₂ h₁ h₂ _ _ _ _ _ _ hτ hu e₁ e₂ e₃ C (ip (wG X bas idx ga v) v) hC
    (fun z => by rw [← hz z, ← hz' z, ← h1]; rfl)
  rw [ha, h2, one_smul]

end GlobalTheory.VacMult
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumMultiplierTrivialPrincipalCongruenceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumMultiplier_trivial_principalCongruence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (H : Host E) (Dw : Datum H) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), r = Dw.p + Dw.q → Function.Injective φ → Submodule.span E (Set.range φ) = ⊤ → (∀ a b, ((Dw.EF a b : ℤ) : ℚ) = EF X (φ a) (φ b)) → ∀ L : Lt E r, SelfD X L → ∀ (M : ℕ), 3 ≤ M → ∀ ga : GL (Fin r) E, IsUn X ga → mapL ga L = L → (∀ u ∈ L, ∃ u' ∈ L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u') → ∀ v : TF n g, IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → wG X bas idx ga v = v := by
  first | exact @GlobalTheory.VacMult.wG_vac_eq | exact GlobalTheory.VacMult.wG_vac_eq | (intros; apply GlobalTheory.VacMult.wG_vac_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumMultiplierEqOneOnStabiliser
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem GlobalTheory.Dict.conjI_half {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (l : Geo.Tor.Level H) : conjI (Mfr l) = l.Mb := by
  have hb : ∀ a : 𝓞 E, Lev.bar a = H.bar a := fun a => by
    apply IsFractionRing.injective (𝓞 E) E
    exact (H.bar_eq a).symm
  ext a
  rw [Lev.mem_conjI, hb, Mfr,
    Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective]
  exact ⟨fun ⟨y, hy, e⟩ => H.bar.injective e ▸ hy, fun h => ⟨a, h, rfl⟩⟩

theorem GlobalTheory.Dict.mult_eq_one_on_stab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (D : SW.Level X) (hn : r ≤ n) (ph : (Fin n → LaJ Xo c d) → c.F), IsSympl X bas → Even n → LevTie d σ ph D hn → ∀ (D' : Datum H) (φ : D'.La →ₗ[𝓞 E] (Fin r → E)), r = D'.p + D'.q → Function.Injective φ → Submodule.span E (Set.range φ) = ⊤ → (∀ a b, ((D'.EF a b : ℤ) : ℚ) = EF X (φ a) (φ b)) → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ mu : GL (Fin r) E → Lt E r → ℂ, (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx ga (v₀ L) = (mu ga L * (D.lam k : ℂˣ)) • v₀ (mapL ga L)) → ∀ L ∈ D.lats, ∀ ga ∈ D.grp, mapL ga L = L → mu ga L = 1 ∧ ∀ u ∈ L, ∃ u' ∈ L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u + l.M • u' := by
  intro E _ _ _ H Dw l Xo c n d σ r g X bas idx D hn ph hs hev hT D' φ hr hinj hsp hEF v₀ hv mu hmu L hL ga
    hga hfix
  have hle : D.𝔪 ≤ Mfr l := by rw [hT.prod]; exact Ideal.mul_le.2 fun a ha b _ => Ideal.mul_mem_right b _ ha
  have hN : Mfr l * conjI (Mfr l) = Ideal.span {(l.M : 𝓞 E)} := by
    rw [conjI_half, mul_comm]; exact l.prod
  obtain ⟨h1, h2, h3⟩ := (stab_trivial_mod E r X g bas idx n hs hev D (Mfr l) l.M hle hN
    (fun k hk => (hT.grp k).1 hk) ga hga).2 L hL hfix
  refine ⟨?_, h1⟩
  obtain ⟨-, -, hgrp, hlat, -⟩ := GlobalTheory.SW.level_laws E r X g bas idx n hs hev D hn
  obtain ⟨hu, k, hk, hred⟩ := (hgrp ga).1 hga
  obtain ⟨hsd, -, -, hsh⟩ := hlat L hL
  have hfix' : mapL ga (D.sh L) = D.sh L := by rw [← (hsh ga hga).2, hfix]
  have hvac := hv L hL
  have hw := GlobalTheory.T.vacuumMultiplier_trivial_principalCongruence E r X g bas idx n hs hev H D' φ hr hinj hsp hEF (D.sh L) hsd l.M l.three_le ga hu
    hfix' h2 (v₀ L) (hT.w ▸ hvac)
  have hlam : D.lam ⟨k, hk⟩ = 1 := hT.det _ (h3 ⟨k, hk⟩ hred l.three_le)
  have e := hmu ga hga L hL ⟨k, hk⟩ hred
  rw [hw, hlam, hfix, Units.val_one, _root_.mul_one] at e
  have hne : v₀ L ≠ 0 := fun h0 => by
    have := hvac.2.1
    rw [h0] at this
    simp [ip, haar, haarAt] at this
  have : (mu ga L - 1) • v₀ L = 0 := by rw [sub_smul, one_smul, ← e, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hne)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumMultiplierEqOneOnStabiliserStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_multiplier_eq_one_on_stabiliser : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (D : SW.Level X) (hn : r ≤ n) (ph : (Fin n → LaJ Xo c d) → c.F), IsSympl X bas → Even n → LevTie d σ ph D hn → ∀ (D' : Datum H) (φ : D'.La →ₗ[𝓞 E] (Fin r → E)), r = D'.p + D'.q → Function.Injective φ → Submodule.span E (Set.range φ) = ⊤ → (∀ a b, ((D'.EF a b : ℤ) : ℚ) = EF X (φ a) (φ b)) → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ mu : GL (Fin r) E → Lt E r → ℂ, (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx ga (v₀ L) = (mu ga L * (D.lam k : ℂˣ)) • v₀ (mapL ga L)) → ∀ L ∈ D.lats, ∀ ga ∈ D.grp, mapL ga L = L → mu ga L = 1 ∧ ∀ u ∈ L, ∃ u' ∈ L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u + l.M • u' := by
  first | exact @GlobalTheory.Dict.mult_eq_one_on_stab | exact GlobalTheory.Dict.mult_eq_one_on_stab | (intros; apply GlobalTheory.Dict.mult_eq_one_on_stab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HarmonicRowHighestEqSpanIntegralHarmonic
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HarmonicRowHighestEqSpanIntegralHarmonic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem natCast_mul_X_mem_symO {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (c : Coeff l) {n : ℕ} (Λ : Lt E n) (N : ℕ)
    (hΛ : Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n ≤ Λ) (ℓ : LtN Dw n) :
    (N : MvPolynomial (LtN Dw n) c.F) * MvPolynomial.X ℓ ∈ Formalism.L2.Pj.symO c (⟨Λ⟩ : GenLat E n) := by
  obtain ⟨τ, i, j⟩ := ℓ
  refine Subring.subset_closure (Or.inr ⟨τ, i, Pi.single j (N : E), hΛ ?_, ?_⟩)
  · have h1 : (Pi.single j (1 : E) : Fin n → E) ∈ Formalism.L2.Pj.stdLat E n := by
      intro k _
      by_cases hk : k = j
      · subst hk
        rw [Pi.single_eq_same]
        exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · rw [Pi.single_eq_of_ne hk]
        exact Submodule.zero_mem _
    have h2 := Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 E)) h1
    have h3 : (N : 𝓞 E) • (Pi.single j (1 : E) : Fin n → E) = Pi.single j (N : E) := by
      rw [Nat.cast_smul_eq_nsmul, ← Pi.single_nsmul]
      simp
    rwa [h3] at h2
  · unfold letB
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · simp

theorem exists_natCast_mul_mem_symO {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} (c : Coeff l) {n : ℕ} (Λ : Lt E n) (N : ℕ) (hN : 0 < N)
    (hΛ : Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n ≤ Λ) (P : MvPolynomial (LtN Dw n) c.F) :
    ∃ M : ℕ, 0 < M ∧ (M : MvPolynomial (LtN Dw n) c.F) * P ∈ Formalism.L2.Pj.symO c (⟨Λ⟩ : GenLat E n) := by
  haveI := c.fin
  induction P using MvPolynomial.induction_on with
  | C x =>
    obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := c.F) {x}
    have h1 := h x (Finset.mem_singleton_self x)
    have h2 : MvPolynomial.C (y • x) ∈ Formalism.L2.Pj.symO (Dw := Dw) c (⟨Λ⟩ : GenLat E n) :=
      Subring.subset_closure (Or.inl ⟨⟨y • x, h1⟩, rfl⟩)
    refine ⟨(y * y).natAbs, Int.natAbs_pos.2 (mul_ne_zero hy hy), ?_⟩
    have h3 : (((y * y).natAbs : ℕ) : MvPolynomial (LtN Dw n) c.F) = ((y * y : ℤ) : MvPolynomial (LtN Dw n) c.F) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg y)]
    have h4 := Subring.mul_mem _ (intCast_mem (Formalism.L2.Pj.symO (Dw := Dw) c (⟨Λ⟩ : GenLat E n)) y) h2
    rw [h3]
    convert h4 using 1
    rw [zsmul_eq_mul, map_mul, map_intCast]
    push_cast
    ring
  | add p q hp hq =>
    obtain ⟨M, hM, h⟩ := hp
    obtain ⟨M', hM', h'⟩ := hq
    refine ⟨M * M', Nat.mul_pos hM hM', ?_⟩
    have := Subring.add_mem _ (Subring.mul_mem _ (natCast_mem _ M') h) (Subring.mul_mem _ (natCast_mem _ M) h')
    convert this using 1
    push_cast
    ring
  | mul_X p ℓ hp =>
    obtain ⟨M, hM, h⟩ := hp
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    have := Subring.mul_mem _ h (natCast_mul_X_mem_symO c Λ N hΛ ℓ)
    convert this using 1
    push_cast
    ring

theorem rowHighest_eq_sum_harmL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (σ : c.F →+* ℂ) (r g q0 n : ℕ) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ) (Dc : Dic Dw c σ X g q0 n a) (Λ : Lt E n) (N : ℕ), 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ → ∀ Q ∈ Harm.rowHighest ℂ Dc.k Dc.k', ∃ (m : ℕ) (t : Fin m → ℂ) (P : Fin m → MvPolynomial (LtN Dw n) c.F), (∀ i, P i ∈ harmL c (⟨Λ⟩ : GenLat E n) a) ∧ Q = ∑ i, t i • MvPolynomial.rename Dc.eL (MvPolynomial.map σ (P i)) := by
  intro E _ _ _ H Dw l c σ r g q0 n X a Dc Λ N hN hΛ Q hQ
  obtain ⟨m, t, v, hv⟩ := Submodule.mem_span_set'.1 (Dc.span hQ)
  have hP : ∀ i, ∃ P : MvPolynomial (LtN Dw n) c.F,
      P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ∧
      MvPolynomial.rename Dc.eL (MvPolynomial.map σ P) = (v i).1 := fun i => (v i).2
  choose P hP hPv using hP
  choose M hM hMP using fun i => exists_natCast_mul_mem_symO c Λ N hN hΛ (P i)
  refine ⟨m, fun i => t i / (M i : ℂ), fun i => (M i : MvPolynomial (LtN Dw n) c.F) * P i,
    fun i => ⟨?_, hMP i⟩, ?_⟩
  · have e : (M i : MvPolynomial (LtN Dw n) c.F) * P i = (M i : c.F) • P i := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    change (M i : MvPolynomial (LtN Dw n) c.F) * P i ∈ _
    rw [e]
    exact ⟨Submodule.smul_mem _ _ (hP i).1,
      fun s k k' h u => by rw [map_smul, (hP i).2.1 s k k' h u],
      fun mm hm => (hP i).2.2 mm (MvPolynomial.support_smul hm)⟩
  · rw [← hv]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h0 : (M i : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (hM i).ne'
    rw [map_mul, map_mul, map_natCast, map_natCast, hPv, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      div_mul_cancel₀ _ h0]

end GlobalTheory.Dict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HarmonicRowHighestEqSpanIntegralHarmonicStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicRowHighest_eq_span_integral_harmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (σ : c.F →+* ℂ) (r g q0 n : ℕ) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ) (Dc : Dic Dw c σ X g q0 n a) (Λ : Lt E n) (N : ℕ), 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ → ∀ Q ∈ Harm.rowHighest ℂ Dc.k Dc.k', ∃ (m : ℕ) (t : Fin m → ℂ) (P : Fin m → MvPolynomial (LtN Dw n) c.F), (∀ i, P i ∈ harmL c (⟨Λ⟩ : GenLat E n) a) ∧ Q = ∑ i, t i • MvPolynomial.rename Dc.eL (MvPolynomial.map σ (P i)) := by
  first | exact @GlobalTheory.Dict.rowHighest_eq_sum_harmL | exact GlobalTheory.Dict.rowHighest_eq_sum_harmL | (intros; apply GlobalTheory.Dict.rowHighest_eq_sum_harmL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsVanishingOffFramesLeSpanShortTheta
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem isBddSec_of_mem_holSub {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r) (P : Formalism.L2.PjFree.FDSec X) (h : P ∈ Formalism.L2.PjFree.holSub X la) (k : Comp) (t : ℂ) :
    (X k).IsBddSec (la k) (t • P k) := by
  have h1 : ∀ k, P k ∈ (X k).SS (la k) := by
    induction h using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.1
    | add x y _ _ hx hy => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.1 _ (hx k) _ (hy k)
    | smul a x _ hx => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 a _ (hx k)
  exact ((siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 t _ (h1 k)).1

theorem theta_sum_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} (X : Data E r)
    (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (φ : TF n g)
    {m : ℕ} (t : Fin m → ℂ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (x : Frame X.Ψ r) :
    thP X hr bas idx φ (∑ i, t i • P i) x = ∑ i, t i * thP X hr bas idx φ (P i) x := by
  unfold thP
  rw [I2.jof_polyDeriv_sum]
  exact Finset.sum_congr rfl fun i _ => I2.polyDeriv_smul _ _ _ _ _


set_option maxHeartbeats 800000 in
theorem holSub0_le_span_shortGen : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → l.A = 1 → (∀ k k', (U.X k).Gm = (U.X k').Gm ∧ (U.X k).ξ0 = (U.X k').ξ0) → (∀ k, HasPrinc (U.X k) l.M) → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → ¬ 3 ∣ d.pd → (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, d.PhiPin ph ψ x₀) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < bad → Dom a n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, ChiOne (U.X k) (Formalism.L2.PjFree.laU U a n k)) → ShortValTot Xo c nab bad nV a n d → holSub0 U.X (Formalism.L2.PjFree.laU U a n) ≤ Submodule.span ℂ (Formalism.L2.PjFree.rdU U '' shortGen Xo c nab bad nV a n d) := by
  intro hci E _ _ _ H Dw l Xo c n d σ r U hσ hU hr1 hA hG hpr hlev hnab huc h3 hpin nab bad nV a hbad hdom hbig
    hchi htot P hP
  obtain ⟨hP1, hP0⟩ := hP
  rcases isEmpty_or_nonempty U.Comp with hemp | ⟨⟨k₀⟩⟩
  · have : P = 0 := funext fun k => (hemp.false k).elim
    rw [this]
    exact Submodule.zero_mem _
  obtain ⟨W⟩ := nonempty_uw hU
  have hrpq : r = Dw.p + Dw.q := hU.1
  have hn : r ≤ n := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    nlinarith
  have hev : Even n := by
    unfold Formalism.L2.Pj.Dom at hdom
    tauto
  have huw := GlobalTheory.T.uniformisation_component_lattices_markings E H Dw l Xo c σ r U hσ hU hr1 W
  have hsame : ∀ k, SameSp (U.X k) (U.X k₀) := fun k =>
    ⟨Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k₀).2 τ).symm, (hG k k₀).1,
      (hU.2.1 k).1.trans (hU.2.1 k₀).1.symm, (hG k k₀).2, by rw [(huw k).1, (huw k₀).1, (hG k k₀).2]⟩
  obtain ⟨ph, ψ, x₀, hph⟩ := hpin (hrpq ▸ hn)
  obtain ⟨Dc, hDe, -⟩ := GlobalTheory.T.exists_letterRowWeightDictionary E H Dw l c σ r W.g n (U.X k₀) a W.e hσ hrpq (hU.2.1 k₀).1 (hU.2.1 k₀).2
    (huw k₀).2.1 hdom
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_classicalLevelData_coverSelfDual E H Dw l Xo c n d σ r (U.X k₀) hn hrpq (huw k₀).2.1 hlev h3 ph ψ x₀ hph
  obtain ⟨v₀, mu, hv₀, hmu⟩ := GlobalTheory.SW.exists_vacua_and_multipliers E r (U.X k₀) W.g Dc.bas Dc.idx n Dc.sympl hev D
  obtain ⟨x0, ga, δ, hadm, hset, hsep⟩ := GlobalTheory.T.exists_components_lattices_moved_to_level_family E H Dw l Xo c n d σ r U hσ hU hr1 hA hlev W k₀ hsame ph D hn hD
  obtain ⟨u, hu, hread⟩ := GlobalTheory.T.short_series_readings_eq_classical_thetaSeries hci E H Dw l Xo c n d σ r U hσ hU hr1 hlev hnab huc ph ψ x₀ hph W (U.X k₀) a
    hdom Dc D hn hDe hD v₀ hv₀ x0
  choose C hC hrd using fun k => hread k (hsame k) (ga k) (δ k) (hset k).1 (hset k).2.1 (hset k).2.2.1
    (hset k).2.2.2.1 (hset k).2.2.2.2
  have hmu1 := GlobalTheory.T.vacuum_multiplier_eq_one_on_stabiliser E H Dw l Xo c n d σ r W.g (U.X k₀) Dc.bas Dc.idx D hn ph Dc.sympl hev hD
    (W.F.Di (W.ik k₀)) (W.emb k₀) (huw k₀).2.2.2.1 (huw k₀).2.2.2.2.1 (huw k₀).2.2.2.2.2.1 (huw k₀).2.2.2.2.2.2
    v₀ hv₀ mu hmu
  have hgrp := (GlobalTheory.SW.level_laws E r (U.X k₀) W.g Dc.bas Dc.idx n Dc.sympl hev D hn).2.2.1
  have hpull := fun k => GlobalTheory.T.isStabiliserInvariant_pull_bounded_section E r (U.X k) (U.X k₀) (hsame k) (ga k) (Formalism.L2.PjFree.laU U a n k)
    (wtOf (U.X k₀) Dc.hr Dc.k Dc.k' n) D.grp l.M ((C k)⁻¹ • P k) (hset k).1
    (fun τ i => by
      rw [Dc.wt_eq]
      simp only [wtX, Formalism.L2.PjFree.laU, (hsame k).p0])
    (fun g' hg' => ⟨((hgrp g').1 hg').1, fun hfix => (hmu1 _ (hset k).2.1 g' hg' hfix).2⟩)
    (hpr k) (hchi k) (isBddSec_of_mem_holSub U.X _ P hP1 k _)
  have hM2 : 0 < d.l₂.M := lt_of_lt_of_le (by norm_num) d.l₂.three_le
  have hMm : ((2 * bad * d.l₂.M : ℕ) : 𝓞 E) ∈ D.𝔪 := by
    rw [hD.m, Nat.cast_mul]
    refine Ideal.mul_mem_left _ _ ?_
    have h1 : (d.l₂.M : 𝓞 E) ∈ d.l₂.Mb * d.l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [d.l₂.prod]
      exact Ideal.mem_span_singleton_self _
    unfold Mfr
    exact (Submodule.mem_inf.1 (Ideal.mul_le_inf h1)).2
  obtain ⟨m, Λ, Pj, hΛ, hQ⟩ := GlobalTheory.T.stableForms_eq_sum_thetaSeries_freeLowerRows E r (U.X k₀) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hev hbig D hn
    (2 * bad * d.l₂.M) (Mfr l) (Jd d) (by positivity) hMm hD.prod hD.cop v₀ hv₀ mu hmu Dc.k Dc.k' U.Comp
    (fun k => mapL (ga k) (U.X k).Λ) _ (fun k => (hset k).2.1) hsep
    (fun k g' hg' hfix => (hmu1 _ (hset k).2.1 g' hg' hfix).1) (fun k => (hpull k).1)
  have hgl := fun j => GlobalTheory.Dict.GenLatCmp.genLat_vset E n (Λ j)
  have hg1 := fun j => (hgl j).1 bad d.l₂.M hbad d.l₂.odd (hΛ j).1
  choose N hN using fun j => (hg1 j).2.2.2
  have hV : ∀ j, Λ j ∈ Vset E n d.l₂.M := fun j => (hgl j).2.2.1 _ _ (Dvd.intro_left _ rfl) (hΛ j).1
  choose mj t R hR hPj using fun j => GlobalTheory.T.harmonicRowHighest_eq_span_integral_harmonic E H Dw l c σ r W.g Dw.p n (U.X k₀) a Dc (Λ j) (N j)
    (hN j).1.pos ((hN j).2.2.trans inf_le_left) (Pj j) (hΛ j).2
  choose f hf hfr using fun j i => (htot ⟨Λ j⟩ (N j) x0 (R j i) (hg1 j).1 (hg1 j).2.1 (hg1 j).2.2.1 (hN j)
    (hadm _) (hR j i)).2
  have hPe : P = ∑ j, ∑ i, (t j i * (u (Λ j) (N j))⁻¹) • Formalism.L2.PjFree.rdU U (f j i) := by
    funext k x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hx : x ∈ (U.X k).dom
    · obtain ⟨hx1, hx2, -⟩ := ((hpull k).2 0 (differentiableOn_const 0) (by simp)).2 x hx
      have e1 := hQ k _ hx1
      rw [hx2, Pi.smul_apply, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ (hC k)] at e1
      rw [e1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hPj j, theta_sum_smul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hrd k (Λ j) (hV j) (N j) (hN j) (R j i) (hR j i).1 (f j i) (hf j i) (hfr j i) x hx]
      have := hu (Λ j) (hV j) (N j) (hN j)
      field_simp
    · rw [hP0 k x hx]
      refine (Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => ?_).symm
      have : Formalism.L2.PjFree.rdU U (f j i) k x = 0 := dif_neg hx
      rw [this, mul_zero]
  rw [hPe]
  refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨f j i, ⟨hf j i, ⟨Λ j⟩, N j, x0, R j i, (hg1 j).1, (hg1 j).2.1, (hg1 j).2.2.1, hN j,
    hadm _, hR j i, hfr j i⟩, rfl⟩

end GlobalTheory.Dict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsVanishingOffFramesLeSpanShortThetaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding holSub0
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_vanishing_off_frames_le_span_shortTheta : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → l.A = 1 → (∀ k k', (U.X k).Gm = (U.X k').Gm ∧ (U.X k).ξ0 = (U.X k').ξ0) → (∀ k, HasPrinc (U.X k) l.M) → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → ¬ 3 ∣ d.pd → (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, d.PhiPin ph ψ x₀) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < bad → Dom a n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, ChiOne (U.X k) (Formalism.L2.PjFree.laU U a n k)) → ShortValTot Xo c nab bad nV a n d → holSub0 U.X (Formalism.L2.PjFree.laU U a n) ≤ Submodule.span ℂ (Formalism.L2.PjFree.rdU U '' shortGen Xo c nab bad nV a n d) := by
  first | exact @GlobalTheory.Dict.holSub0_le_span_shortGen | exact GlobalTheory.Dict.holSub0_le_span_shortGen | (intros; apply GlobalTheory.Dict.holSub0_le_span_shortGen <;> assumption)
end

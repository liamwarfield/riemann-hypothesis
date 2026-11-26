module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFramesAnalytic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitAnalyticFunction
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeEigenLineGenerator
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionsFlatAgree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspWeightRegularisationsTied
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompactificationCompEquiv
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AllWeightSectionsCompat

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerWeightOfZero
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerWeightOfZero
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem norm_wt_eq_iSup {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam : Top.Wt Ψ N) :
    ‖lam‖ = ⨆ k : Ψ × Fin N, |lam k.1 k.2| := by
  apply le_antisymm
  · have h0 : 0 ≤ ⨆ k : Ψ × Fin N, |lam k.1 k.2| := Real.iSup_nonneg fun _ => abs_nonneg _
    refine (pi_norm_le_iff_of_nonneg h0).2 fun τ => (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact le_ciSup (f := fun k : Ψ × Fin N => |lam k.1 k.2|) (Set.finite_range _).bddAbove (τ, i)
  · refine Real.iSup_le (fun k => ?_) (norm_nonneg _)
    calc |lam k.1 k.2| = ‖lam k.1 k.2‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖lam k.1‖ := norm_le_pi_norm _ _
      _ ≤ ‖lam‖ := norm_le_pi_norm _ _

theorem flagDeg_eq_const_mul_vdm {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (lam : Top.Wt Ψ N) :
    Top.flagDeg lam = (((Top.dimFl Ψ N).factorial : ℝ) *
      ∏ _τ : Ψ, ∏ i : Fin N, ∏ k : Fin N, (if i < k then ((k : ℝ) - (i : ℝ))⁻¹ else 1)) *
        GlobalTheory.CompHt.vdm lam := by
  rw [(Top.flagDeg_eq_weyl Ψ N lam).1, mul_assoc, GlobalTheory.CompHt.vdm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hI : Finset.Ioi i = Finset.univ.filter (fun k => i < k) := by ext; simp
  rw [hI, Finset.prod_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs
  · rw [div_eq_inv_mul]
  · simp

theorem flagDeg_mul_vdm {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (lam mu : Top.Wt Ψ N) :
    Top.flagDeg lam * GlobalTheory.CompHt.vdm mu = Top.flagDeg mu * GlobalTheory.CompHt.vdm lam := by
  rw [flagDeg_eq_const_mul_vdm lam, flagDeg_eq_const_mul_vdm mu]
  ring

theorem vdm_cast {ι : Type} (i₁ i₂ : Fintype ι) {N : ℕ} (w : ι → Fin N → ℤ) :
    ((@GlobalTheory.CompHt.vdm ι i₁ N ℤ _ w : ℤ) : ℝ) = @GlobalTheory.CompHt.vdm ι i₂ N ℝ _ fun τ i => (w τ i : ℝ) := by
  obtain rfl := Subsingleton.elim i₁ i₂
  simp [GlobalTheory.CompHt.vdm]

section Entries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem towerWt_wtOf (Dw : Datum H) (u : GlobalTheory.AllWt.Weight Dw) :
    towerWt Dw (GlobalTheory.AllWt.wtOf Dw u 0).1 = reW u := by
  funext τ n
  simp only [towerWt, reW]
  split_ifs with hn
  · rw [GlobalTheory.AllWt.wtOf_big (Dw := Dw) u 0 τ n hn]
    simp
  · have hn' := n.isLt
    have hq : Dw.p + Dw.q - 1 - (n : ℕ) < Dw.q := by omega
    rw [GlobalTheory.AllWt.wtOf_small (Dw := Dw) u 0 τ _ hq]
    have hf : (⟨Dw.p + (Dw.q - 1 - (Dw.p + Dw.q - 1 - (n : ℕ))), by omega⟩ : Fin (Dw.p + Dw.q)) = n :=
      Fin.ext (by simp only; omega)
    rw [hf]
    simp

theorem gap_reW {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) (τ : CMType H) (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) :
    Top.gap Dw.p (reW u) τ = (u τ ⟨Dw.p - 1, by omega⟩ : ℝ) - u τ ⟨Dw.p, by omega⟩ := by
  have h1 : Dw.p - 1 < Dw.p + Dw.q := by omega
  have h2 : Dw.p < Dw.p + Dw.q := by omega
  simp only [Top.gap, Top.ent, dif_pos h1, dif_pos h2, reW]

theorem regDominant_reW {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) (h : ∀ τ, StrictAnti (u τ)) :
    Top.RegDominant (reW u) := fun τ _ _ hab => by
  simp only [reW]
  exact_mod_cast h τ hab

theorem weightHyp_reW_one {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q)
    (h : ∀ τ, StrictAnti (u τ)) : Top.WeightHyp Dw.p (reW u) 1 := by
  refine ⟨one_pos, regDominant_reW u h, fun τ => ?_, fun τ a b _ hab => ?_⟩
  · rw [gap_reW u τ hp hq]
    have hlt : (⟨Dw.p - 1, by omega⟩ : Fin (Dw.p + Dw.q)) < ⟨Dw.p, by omega⟩ :=
      Fin.mk_lt_mk.2 (by omega)
    have h1 := h τ hlt
    have h2 : u τ ⟨Dw.p, by omega⟩ + 1 ≤ u τ ⟨Dw.p - 1, by omega⟩ := h1
    have h3 : ((u τ ⟨Dw.p, by omega⟩ : ℝ)) + 1 ≤ u τ ⟨Dw.p - 1, by omega⟩ := by exact_mod_cast h2
    linarith
  · have hne : u τ a - u τ b ≠ 0 := sub_ne_zero.2 fun e => hab ((h τ).injective e)
    have h1 : (1 : ℤ) ≤ |u τ a - u τ b| := Int.one_le_abs hne
    simp only [reW]
    exact_mod_cast h1

theorem weightHyp_reW_of_wtGap {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ) (hq : 1 ≤ Dw.q)
    (hqp : Dw.q < Dw.p) (hg : GlobalTheory.CovHt.WtGap u g) : Top.WeightHyp Dw.p (reW u) g := by
  obtain ⟨hg0, hanti, hdist⟩ := hg
  have hp : 1 ≤ Dw.p := by omega
  refine ⟨hg0, regDominant_reW u hanti, fun τ => ?_, fun τ a b ha hab => ?_⟩
  · rw [gap_reW u τ hp hq]
    have hlt : (⟨Dw.p - 1, by omega⟩ : Fin (Dw.p + Dw.q)) < ⟨Dw.p, by omega⟩ :=
      Fin.mk_lt_mk.2 (by omega)
    have h1 := hdist τ ⟨Dw.p, by omega⟩ ⟨Dw.p - 1, by omega⟩ (le_refl _) (ne_of_gt hlt)
    have h2 : (u τ ⟨Dw.p, by omega⟩ : ℝ) < u τ ⟨Dw.p - 1, by omega⟩ := by
      exact_mod_cast hanti τ hlt
    rw [abs_sub_comm, abs_of_pos (sub_pos.2 h2)] at h1
    exact h1
  · have ha' : Dw.p ≤ (a : ℕ) := by
      have hn : ¬ Dw.p ≤ Dw.p + Dw.q - Dw.p := by omega
      simpa only [Top.InSmall, if_neg hn] using ha
    exact hdist τ a b ha' hab

theorem bound_eq_root_weight_bound {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ) :
    GlobalTheory.CovHt.bndB u g = Top.bigB0 (reW u) g := by
  simp only [GlobalTheory.CovHt.bndB, Top.bigB0, norm_wt_eq_iSup, reW]
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]

theorem covHt_l1_eq_l1_reW {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) : GlobalTheory.CovHt.l1 u = Top.l1 (reW u) := by
  unfold GlobalTheory.CovHt.l1 Top.l1 reW
  congr!

end Entries

theorem integer_weights_vocab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) [DecidableEq (CMType H)] (u : GlobalTheory.AllWt.Weight Dw), towerWt Dw (GlobalTheory.AllWt.wtOf Dw u 0).1 = reW u ∧ (GlobalTheory.AllWt.wtOf Dw u 0) = ((GlobalTheory.AllWt.wtOf Dw u 0).1, 0) ∧ (∀ n : ℕ, n • (GlobalTheory.AllWt.wtOf Dw u 0) = GlobalTheory.AllWt.wtOf Dw (n • u) 0) ∧ (∀ j, (nOf u j : ℝ) = RM.coef (reW u) 0 j) ∧ GlobalTheory.CovHt.l1 u = Top.l1 (reW u) ∧ GlobalTheory.CompHt.dimFlag Dw = (Top.dimFl (CMType H) (Dw.p + Dw.q)) ∧ (∀ v : GlobalTheory.AllWt.Weight Dw, Top.flagDeg (reW u) * ((GlobalTheory.CompHt.vdm v : ℤ) : ℝ) = Top.flagDeg (reW v) * ((GlobalTheory.CompHt.vdm u : ℤ) : ℝ)) ∧ (1 ≤ Dw.p → 1 ≤ Dw.q → (∀ τ, StrictAnti (u τ)) → Top.WeightHyp Dw.p (reW u) 1) ∧ ∀ g : ℝ, GlobalTheory.CovHt.bndB u g = Top.bigB0 (reW u) g ∧ (1 ≤ Dw.q → Dw.q < Dw.p → GlobalTheory.CovHt.WtGap u g → Top.WeightHyp Dw.p (reW u) g) := by
  intro E _ _ _ H Dw l Xo c RM _ u
  refine ⟨towerWt_wtOf Dw u, ?_, fun n => ?_, ?_, covHt_l1_eq_l1_reW u, ?_, fun v => ?_, weightHyp_reW_one u,
    fun g => ⟨bound_eq_root_weight_bound u g, fun hq hqp hg => weightHyp_reW_of_wtGap u g hq hqp hg⟩⟩
  · exact Prod.ext rfl (by simp [GlobalTheory.AllWt.wtOf_snd])
  · rw [GlobalTheory.CompHt.nsmul_wtOf, smul_zero]
  · rintro (_ | r)
    · simp [nOf, Top.RootModel.coef]
    · simp [nOf, Top.RootModel.coef, reW]
  · simp only [GlobalTheory.CompHt.dimFlag, Formalism.DegreeFormula.dimFl, Top.dimFl]
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  · have e : ∀ w : GlobalTheory.AllWt.Weight Dw, ((GlobalTheory.CompHt.vdm w : ℤ) : ℝ) = GlobalTheory.CompHt.vdm (reW w) :=
      fun w => vdm_cast _ _ w
    rw [e, e]
    exact flagDeg_mul_vdm (reW u) (reW v)

end GlobalTheory.CompanionTheory.Ar.Plug
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerWeightOfZeroStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_weight_of_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) [DecidableEq (CMType H)] (u : GlobalTheory.AllWt.Weight Dw), towerWt Dw (GlobalTheory.AllWt.wtOf Dw u 0).1 = reW u ∧ (GlobalTheory.AllWt.wtOf Dw u 0) = ((GlobalTheory.AllWt.wtOf Dw u 0).1, 0) ∧ (∀ n : ℕ, n • (GlobalTheory.AllWt.wtOf Dw u 0) = GlobalTheory.AllWt.wtOf Dw (n • u) 0) ∧ (∀ j, (nOf u j : ℝ) = RM.coef (reW u) 0 j) ∧ GlobalTheory.CovHt.l1 u = Top.l1 (reW u) ∧ GlobalTheory.CompHt.dimFlag Dw = (Top.dimFl (CMType H) (Dw.p + Dw.q)) ∧ (∀ v : GlobalTheory.AllWt.Weight Dw, Top.flagDeg (reW u) * ((GlobalTheory.CompHt.vdm v : ℤ) : ℝ) = Top.flagDeg (reW v) * ((GlobalTheory.CompHt.vdm u : ℤ) : ℝ)) ∧ (1 ≤ Dw.p → 1 ≤ Dw.q → (∀ τ, StrictAnti (u τ)) → Top.WeightHyp Dw.p (reW u) 1) ∧ ∀ g : ℝ, GlobalTheory.CovHt.bndB u g = Top.bigB0 (reW u) g ∧ (1 ≤ Dw.q → Dw.q < Dw.p → GlobalTheory.CovHt.WtGap u g → Top.WeightHyp Dw.p (reW u) g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.integer_weights_vocab | exact GlobalTheory.CompanionTheory.Ar.Plug.integer_weights_vocab | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.integer_weights_vocab <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatZeroFromResolutionAndGaga
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatZeroFromResolutionAndGaga
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.A0

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_typeFn {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H p q ty := by
  classical
  let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then p else q
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))).symm
  have h : ∀ τ, Nat.card {i // (e i).1 = τ} = m τ := fun τ => by
    rw [Nat.card_congr ((e.subtypeEquiv (q := fun x => x.1 = τ) fun _ => Iff.rfl).trans
      (Equiv.sigmaSubtype τ))]
    simp
  exact ⟨_, fun i => (e i).1, fun τ => ⟨fun hτ => by rw [h]; simp [m, hτ], fun hτ => by rw [h]; simp [m, hτ]⟩⟩

theorem exists_basis_of_isVBOn {X : Scheme.{0}} {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Lat ξ V} {T : Set (Cpt ξ)} {r : ℕ} {S : Submodule Ω V}
    (h : L.IsVBOn T r S) (hT : T.Nonempty) :
    ∃ b : Fin r → V, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = S := by
  obtain ⟨p, hp⟩ := hT
  obtain ⟨U, hU, b, hb, hf⟩ := h p hp
  exact ⟨b, (hf p hp hU).1, hb⟩

theorem flat_zero_of_resolution_gaga (hres : Geo.ResK.ResKStatement) (hgaga : GagaSections) : FlatLineGenerator := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ hO hpq hτ hZ
  let σ : c.F →+* ℂ := c.F.val.toRingHom
  obtain ⟨g, ty, hty⟩ := exists_typeFn H D.p D.q
  have hσρ : (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 := rfl
  obtain ⟨FU⟩ := GlobalTheory.familyUnif_of_laws GlobalTheory.abelianSchemeLaws_all.1 E H D l Xo
    (σ.comp (IntermediateField.inclusion c.le).toRingHom) g ty hpq hσρ hty
  have hστ : ∀ a : 𝓞 E, σ (tauIn c τ a) = τ (a : E) := fun a => rfl
  obtain ⟨Φ, hΦ, -⟩ := GlobalTheory.T.exists_unit_analytic_function E H D l Xo c τ τ σ g ty FU hty hτ hστ
  obtain ⟨h1, h2, -, hne⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ hO hτ
  obtain ⟨b₁, hb₁, hs₁⟩ := exists_basis_of_isVBOn h1 hne
  obtain ⟨b₂, hb₂, hs₂⟩ := exists_basis_of_isVBOn h2 hne
  have hσrt : σ (tauIn c τ H.rt) = H.rt0 := (hστ H.rt).trans hτ
  obtain ⟨f, κ, W, -, -, hgen, -⟩ := GlobalTheory.T.eigen_frames_analytic hres hgaga E H D l Xo c O β Y U Z τ σ Φ b₁ b₂ hO hpq hτ hσrt hZ
    hΦ hb₁ hs₁ hb₂ hs₂
  obtain ⟨φ, hφ, hrep⟩ := GlobalTheory.T.wedge_eigen_line_generator E H D l Xo c O β Y U Z τ _ _ hO hτ hgen
  exact ⟨φ, hφ, FlatOnModel.of_gen hφ hgen hrep, fun φ' h1' h2' =>
    GlobalTheory.T.frame_functions_flat_agree E H D l Xo c O β Y U Z τ φ φ' hO hτ hZ hφ (FlatOnModel.of_gen hφ hgen hrep) h1' h2'⟩

end GlobalTheory.CompanionTheory.Ar.Flat.A0
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatZeroFromResolutionAndGagaStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_zero_from_resolution_and_gaga : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.CompanionTheory.Ar.Flat.GagaSections → GlobalTheory.CompanionTheory.Ar.Flat.FlatLineGenerator := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.A0.flat_zero_of_resolution_gaga | exact GlobalTheory.CompanionTheory.Ar.Flat.A0.flat_zero_of_resolution_gaga | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.A0.flat_zero_of_resolution_gaga <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithmeticDegreePositiveHerm
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspClausesOfNineGeoU
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.NineEq

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel GlobalTheory.CompanionTheory.Ar.Small
open GroundTheory.Heights₂.Heights.LowerBoundFree (AmpleOnGenericFibre)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Field

variable {F : Type} [Field F]

end Field

variable {Ω : Type} [Field Ω]


theorem geomDeg_eq (hD : DegreeStatement) {W : Ideal (MRing ι)} {d : ℕ} (hW : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W (d + 1))
    {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) : geomDeg W A d = genDeg W d A.a := by
  classical
  have h := GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree hD K ι W d (fun _ => A) hW (fun _ => hA)
  have hpot : pot (fun _ : Fin d => A) = fun (_ : Fin d) z => Real.log (A.h z) := rfl
  rw [hpot] at h
  unfold geomDeg genDeg
  rw [h]

section Values

variable {y : (Σ k, ι k) → Ω} {L : Type} [Field L] {z : (Σ k, ι k) → L} {c : ∀ k, ι k}

end Values

end GlobalTheory.CompanionTheory.Ar.Cusp.NineEq

end

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.NineEq

open NumberField Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.LowerBoundFree

section Systems

open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

end Systems

section Clauses

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II Ψ K J Ω W} (Hd : HodgeData Dc)

variable {w : ((Σ k, J k) → ℂ) → ℝ} {M : XModel Dc} (S : BoundedRegularisationSetting M Dc.Xo Hd.aMu w)

end Clauses

end GlobalTheory.CompanionTheory.Ar.Cusp.NineEq
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithmeticDegreePositiveHerm
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem nefCount : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι), 1 ≤ D → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A → (∀ W, ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W 2 → mCoordIdeal y ≤ W → 0 ≤ geomDeg W A 1) → (∀ τ, FiniteDimensional ℚ (Submodule.span ℚ (chartLatNm y A.a τ : Set Ω))) ∧ Tendsto (fun τ : ℕ => (D.factorial : ℝ) * (Module.finrank ℚ (Submodule.span ℚ (chartLatNm y A.a τ : Set Ω)) : ℝ) / (τ : ℝ) ^ D) atTop (𝓝 (geomDeg (mCoordIdeal y) A D)) := by
  intro hRR hG II _ K _ ι _ Ω _ _ y D A _ hX hB hA hnef
  obtain ⟨-, -, -, -, -, -, -, -, -, hPB, -⟩ := hG
  obtain ⟨-, ⟨-, hD, -⟩, -⟩ := hPB
  have hN : GroundTheory.Heights₂.Heights.HilbertSamuel.NefOnGenericDeg (mCoordIdeal y) A.a := by
    intro W hW hle
    have h := hnef W hW hle
    rw [GlobalTheory.CompanionTheory.Ar.Cusp.NineEq.geomDeg_eq hD (d := 1) hW hA] at h
    exact_mod_cast h
  have e := GlobalTheory.CompanionTheory.Ar.Cusp.NineEq.geomDeg_eq hD hX hA
  rw [e]
  exact hRR K ι Ω y D A.a hX hB hN

end GlobalTheory.CompanionTheory.Ar.Plug
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithmeticDegreePositiveHermStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_count_tendsto_geomDeg : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι), 1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A → (∀ W, IsArithVar W 2 → mCoordIdeal y ≤ W → 0 ≤ geomDeg W A 1) → (∀ τ, FiniteDimensional ℚ (Submodule.span ℚ (chartLatNm y A.a τ : Set Ω))) ∧ Tendsto (fun τ : ℕ => (D.factorial : ℝ) * (Module.finrank ℚ (Submodule.span ℚ (chartLatNm y A.a τ : Set Ω)) : ℝ) / (τ : ℝ) ^ D) atTop (𝓝 (geomDeg (mCoordIdeal y) A D)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.nefCount | exact GlobalTheory.CompanionTheory.Ar.Plug.nefCount | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.nefCount <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeightZeroSectionMembership
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeightZeroSectionMembership
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug


set_option maxHeartbeats 2000000 in
theorem bdd_mem_cuspOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ (x : ℝ) (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → ∀ f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0), f ∈ GlobalTheory.AllWt.suppOn Z → (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ GlobalTheory.AllWt.framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) x (GlobalTheory.AllWt.wtOf Dw u 0) f z ≤ C) → f ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) := by
  intro E _ _ _ H Dw l Xo c r U h e hL hp hq x Z u hu f hf hfZ hb
  have hF : FnAlgClosed (Xo := Xo) (c := c) :=
    GlobalTheory.CompanionTheory.Ar.Rec.CompOver.fnAlgClosed_of_card (U c.F.val.toRingHom) rfl (hL.unf _ rfl) h (hL.unTest _ rfl) hL.genT
      hL.comps
  refine ⟨GlobalTheory.AllWt.mem_cuspW.2 ⟨hf, fun σ hσ => holCusp_mem_holSub _ _ fun k => ?_⟩, hfZ⟩
  have hU := hL.unf σ hσ
  have hK : Nonempty (GlobalTheory.ShFam.KeySec Xo c) := by
    obtain ⟨hr, -, -, -, -, g, ee, F, -⟩ := hU
    exact GlobalTheory.KeyCover.nonempty_keySec_of_family _ _ _ _ _ _ σ hσ ee F (by omega) hF
  have hdec : ∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ →
      (GlobalTheory.AllWt.wtOf Dw u 0).1 (τ, j) ≤ (GlobalTheory.AllWt.wtOf Dw u 0).1 (τ, i) := by
    intro τ i j hij hj
    by_cases hτ : τ (H.rt : E) = H.rt0
    · have hjp : j < Dw.p := by simpa [Datum.mult, hτ] using hj
      have e1 := GlobalTheory.AllWt.wtOf_big u 0 ⟨τ, hτ⟩ j hjp
      have e2 := GlobalTheory.AllWt.wtOf_big u 0 ⟨τ, hτ⟩ i (by omega)
      simp only at e1 e2
      rw [e1, e2]
      have := (hu ⟨τ, hτ⟩).antitone (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨j, by omega⟩ from hij)
      omega
    · have hjq : j < Dw.q := by simpa [Datum.mult, hτ] using hj
      have hc := GlobalTheory.AllWt.conj_mem hτ
      have e1 := GlobalTheory.AllWt.wtOf_small u 0 ⟨conjEmb τ, hc⟩ j hjq
      have e2 := GlobalTheory.AllWt.wtOf_small u 0 ⟨conjEmb τ, hc⟩ i (by omega)
      simp only [GlobalTheory.AllWt.conjEmb_conjEmb] at e1 e2
      rw [e1, e2]
      have := (hu ⟨conjEmb τ, hc⟩).antitone
        (show (⟨Dw.p + (Dw.q - 1 - j), by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from
          Fin.mk_le_mk.2 (by omega))
      omega
  have hsec := GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU _ _ _ _ _ _ σ _ (U σ) hK hσ hU (by omega) _
    (GlobalTheory.AllWt.even_wtOf u 0) hdec f hf k
  have hr := hU.1
  obtain ⟨hp0, hΨ⟩ := hU.2.1 k

  obtain ⟨t⟩ : Nonempty (GlobalTheory.AllWt.Psi H) := by
    obtain ⟨ρ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases hρ : ρ (H.rt : E) = H.rt0
    · exact ⟨⟨ρ, hρ⟩⟩
    · exact ⟨⟨conjEmb ρ, GlobalTheory.AllWt.conj_mem hρ⟩⟩
  have ht : relab c σ t.1 ∈ ((U σ).X k).Ψ := by
    refine (hΨ _).2 ?_
    have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
    exact (congrArg σ (Subtype.ext t.2)).trans hσ0
  have hbig : ∀ j : Fin r, ∀ hj : Dw.q ≤ (j : ℕ), GlobalTheory.AllWt.modelWt (U σ) (GlobalTheory.AllWt.wtOf Dw u 0) k ⟨_, ht⟩ j =
      u t ⟨(j : ℕ) - Dw.q, by omega⟩ := by
    intro j hj
    have hjr := j.2
    have := GlobalTheory.AllWt.modelWt_wtOf_big (U σ) u 0 k hp0 t ht ((j : ℕ) - Dw.q) (by omega) (by omega)
    rwa [show (⟨Dw.q + ((j : ℕ) - Dw.q), by omega⟩ : Fin r) = j from Fin.ext (by simp only; omega)] at this
  have hsm : ∀ j : Fin r, ∀ hj : (j : ℕ) < Dw.q, GlobalTheory.AllWt.modelWt (U σ) (GlobalTheory.AllWt.wtOf Dw u 0) k ⟨_, ht⟩ j =
      u t ⟨Dw.p + (j : ℕ), by omega⟩ := fun j hj =>
    GlobalTheory.AllWt.modelWt_wtOf_small (U σ) u 0 k hp0 t ht j hj j.2
  obtain ⟨C, hC⟩ := hb σ hσ
  have hpos := GlobalTheory.AllWt.lieFacZ_pos (Dw := Dw) x (GlobalTheory.AllWt.wtOf Dw u 0)
  have hbdd : ((U σ).X k).IsBddSec (GlobalTheory.AllWt.modelWt (U σ) (GlobalTheory.AllWt.wtOf Dw u 0) k) (rdU (U σ) f k) := by
    refine ⟨hsec, max (C / GlobalTheory.AllWt.lieFacZ Dw x (GlobalTheory.AllWt.wtOf Dw u 0)) 0, fun y hy => ?_⟩
    by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ GlobalTheory.AllWt.framesOn (U σ) Z
    · refine le_max_of_le_left ((le_div_iff₀' hpos).2 ?_)
      have h1 := hC ⟨k, y⟩ hz
      simpa only [GlobalTheory.AllWt.homN, GlobalTheory.AllWt.ptN] using h1
    · have h0 : rdU (U σ) f k y = 0 := GlobalTheory.AllWt.rdU_eq_zero (U σ) hfZ hz
      refine le_max_of_le_right (le_of_eq ?_)
      simp [Data.pnorm, h0]
  refine ReciprocityTheory.ChartRestriction.G.AR.Up.cuspStatement_holds r _ _ ⟨_, ht⟩ (by omega) (by omega) (fun i j hij hjp => ?_)
    (fun i0 i1 h0 h1 => ?_) _ hbdd
  · have hjr := j.2
    have hir := i.2
    by_cases hjq : (j : ℕ) < Dw.q
    · rw [hsm j hjq, hsm i (by omega)]
      exact (hu t).antitone (Fin.mk_le_mk.2 (by omega))
    · have hiq : Dw.q ≤ (i : ℕ) := by omega
      rw [hbig j (by omega), hbig i hiq]
      exact (hu t).antitone (Fin.mk_le_mk.2 (by omega))
  · have hi1 := i1.2
    rw [hsm i0 (by omega), hbig i1 (by omega)]
    exact (hu t) (Fin.mk_lt_mk.2 (by omega))

end GlobalTheory.CompanionTheory.Ar.Plug
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeightZeroSectionMembershipStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_zero_section_membership : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ (x : ℝ) (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → ∀ f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0), f ∈ GlobalTheory.AllWt.suppOn Z → (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ GlobalTheory.AllWt.framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) x (GlobalTheory.AllWt.wtOf Dw u 0) f z ≤ C) → f ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.bdd_mem_cuspOn | exact GlobalTheory.CompanionTheory.Ar.Plug.bdd_mem_cuspOn | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.bdd_mem_cuspOn <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodEmbeddingComponentSections
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodEmbeddingComponentSections
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.SameFlag

theorem eq_of_ratios {K A L M : Type} [Field K] [CommRing A] [Algebra K A] [Field L] [Algebra K L] [CommRing M]
    [IsDomain M] [Algebra K M] (ι : A →ₐ[K] L) (hι : Function.Injective ι) (ψ : A →ₐ[K] M) (φ : L →ₐ[K] M) {N : ℕ}
    (G : Fin (N + 1) → A) (h0 : ι (G 0) ≠ 0) (hψ0 : ψ (G 0) ≠ 0)
    (hrat : ∀ j, ψ (G j) * φ (ι (G 0)) = ψ (G 0) * φ (ι (G j)))
    (hgen : IntermediateField.adjoin K (Set.range fun j => ι (G j) / ι (G 0)) = ⊤) (b : A) : ψ b = φ (ι b) := by
  set g₀ : A := G 0 with hg₀
  let S : Subalgebra K L :=
    { carrier := {x | ∃ (a : A) (n : ℕ), x * ι g₀ ^ n = ι a ∧ φ x * ψ g₀ ^ n = ψ a}
      mul_mem' := by
        rintro x x' ⟨a, n, h1, h2⟩ ⟨a', n', h1', h2'⟩
        refine ⟨a * a', n + n', ?_, ?_⟩
        · rw [map_mul, ← h1, ← h1', pow_add]; ring
        · rw [map_mul, map_mul, ← h2, ← h2', pow_add]; ring
      add_mem' := by
        rintro x x' ⟨a, n, h1, h2⟩ ⟨a', n', h1', h2'⟩
        refine ⟨a * g₀ ^ n' + a' * g₀ ^ n, n + n', ?_, ?_⟩
        · rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, ← h1, ← h1', pow_add]; ring
        · rw [map_add (f := _), map_add (f := _), map_mul, map_mul, map_pow, map_pow, ← h2, ← h2', pow_add]; ring
      algebraMap_mem' := fun r => ⟨algebraMap K A r, 0, by simp, by simp⟩ }
  have hmem : ∀ x, x ∈ S ↔ ∃ (a : A) (n : ℕ), x * ι g₀ ^ n = ι a ∧ φ x * ψ g₀ ^ n = ψ a := fun x => Iff.rfl
  have hφ0 : φ (ι g₀) ≠ 0 := (map_ne_zero φ).2 h0
  have hρ : ∀ j, ι (G j) / ι g₀ ∈ S := by
    intro j
    refine (hmem _).2 ⟨G j, 1, by rw [pow_one, div_mul_cancel₀ _ h0], ?_⟩
    have e1 : φ (ι (G j) / ι g₀) * φ (ι g₀) = φ (ι (G j)) := by
      rw [← map_mul, div_mul_cancel₀ _ h0]
    refine mul_right_cancel₀ hφ0 ?_
    rw [pow_one, hrat j, ← e1]; ring
  have hpol : ∀ p : MvPolynomial (Fin (N + 1)) K, MvPolynomial.aeval (fun j => ι (G j) / ι g₀) p ∈ S := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simpa using S.algebraMap_mem a
    | add p q hp hq => simpa using S.add_mem hp hq
    | mul_X p i hp => simpa using S.mul_mem hp (hρ i)
  have hb : ι b ∈ IntermediateField.adjoin K (Set.range fun j => ι (G j) / ι g₀) := by
    rw [hgen]; exact IntermediateField.mem_top
  obtain ⟨p, q, e⟩ := (IntermediateField.mem_adjoin_range_iff K _ _).1 hb
  by_cases hq : MvPolynomial.aeval (fun j => ι (G j) / ι g₀) q = 0
  · rw [hq, div_zero] at e
    have : b = 0 := hι (by rw [e, map_zero])
    rw [this, map_zero, map_zero, map_zero]
  obtain ⟨a₁, n₁, h1, h1'⟩ := (hmem _).1 (hpol q)
  obtain ⟨a₂, n₂, h2, h2'⟩ := (hmem _).1 (hpol p)
  set B := MvPolynomial.aeval (fun j => ι (G j) / ι g₀) q with hB
  set P := MvPolynomial.aeval (fun j => ι (G j) / ι g₀) p with hP
  have hbB : ι b * B = P := by rw [e, div_mul_cancel₀ _ hq]
  have key : b * a₁ * g₀ ^ n₂ = a₂ * g₀ ^ n₁ := by
    apply hι
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, ← h1, ← h2, ← hbB]; ring
  have key' := congrArg ψ key
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, ← h1', ← h2', ← hbB, map_mul] at key'
  have hne : φ B * ψ g₀ ^ n₁ * ψ g₀ ^ n₂ ≠ 0 :=
    mul_ne_zero (mul_ne_zero ((map_ne_zero φ).2 hq) (pow_ne_zero _ hψ0)) (pow_ne_zero _ hψ0)
  refine mul_right_cancel₀ hne ?_
  linear_combination key'

end GlobalTheory.CompanionTheory.Ar.SameFlag

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SameFlag

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_map (hL : GlobalTheory.Reg.EvLaws Xo c) {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {S T : Type} [CommRing S] [IsReduced S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {y : FrPt Xo c S} {z : FrPt Xo c T} (hyz : FrMap φ y z) : evR Xo c f z = φ (evR Xo c f y) := by
  have key : ∀ {S' : Type} [CommRing S'] [Algebra c.F S'] (p : TRing c.F) (χ : p.R →ₐ[c.F] S') (y₀ : FrPt Xo c p.R)
      (w : FrPt Xo c S'), FrMap χ y₀ w → evR Xo c f w = χ (f p y₀) := by
    intro S' _ _ p χ y₀ w hw
    have h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := ⟨p, χ, y₀, hw⟩
    unfold evR evalAt
    rw [dite_eq_left h]
    exact hL.wd f hf S' _ p _ χ _ y₀ w h.choose_spec.choose_spec.choose_spec hw
  obtain ⟨q, χ, y₀, hy₀⟩ := hL.test S y
  rw [key q χ y₀ y hy₀, key q (φ.comp χ) y₀ z (PullbackSections.frMap_trans χ φ hy₀ hyz)]
  rfl

end Main

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem frBor_of_proportional_readings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (Z : Comp Xo c) (k : (U σ).Comp), Over (U σ) (e Z) k → ∀ (a : WZ E) (N : ℕ) (g : Fin (N + 1) → Rul Xo c), (∀ j, g j ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a) → BirOn h Z g → ∀ (φ : Om Z →ₐ[c.F] CAt σ) (x₀ y : ((U σ).X k).dom) (y₁ : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y₁ → FrBor t ((U σ).un k x₀) y₁ → ∀ w : ℂ, w ≠ 0 → (∀ j, rdU (U σ) (g j) k y.1 = w * toC (φ (evC h Z (g j)))) → ∃ t' : Ix Dw → (CAt σ)ˣ, FrBor t' ((U σ).un k x₀) ((U σ).un k y) := by
  intro E _ _ _ H Dw l Xo c r U h e hC σ hσ Z k hOver a N g hg hB φ x₀ y y₁ t hφ hb w hw hr
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hS : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  haveI hdom : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
  haveI hred : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  have hrd : ∀ f : Rul Xo c, rdU (U σ) f k y.1 = toC (evR Xo c f ((U σ).un k y)) := by
    intro f
    classical
    show (if h : y.1 ∈ ((U σ).X k).dom then toC (evR Xo c f ((U σ).un k ⟨y.1, h⟩)) else 0) = _
    rw [dite_eq_left y.2]
  obtain ⟨C, ψ, z, t', hz, hbz⟩ : ∃ (C : GlobalTheory.Reg.FChart h) (ψ : C.R →ₐ[c.F] CAt σ) (z : FrPt Xo c (CAt σ))
      (t' : Ix Dw → (CAt σ)ˣ), FrMap ψ C.y z ∧ FrBor t' z ((U σ).un k y) := by
    letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
    exact hA h (CAt σ) ((U σ).un k y)

  have hCZ : C.Z = Z := by
    by_contra hne
    have he := hC.e_sec Z
    have h0 : evC h C.Z (e Z) = 0 := (hC.e_val Z).2 _ hne
    have h1 : evR Xo c (e Z) C.yg = 0 := by
      rw [hL.wt 0 0 (e Z) he _ C.t _ _ (hL.test _ _) (hL.test _ _) C.bor]
      unfold evC at h0
      rw [h0, mul_zero]
    have h2 : evR Xo c (e Z) C.y = 0 := by
      rw [evR_map hL he.1 C.R.val C.gen] at h1
      exact Subtype.ext h1
    have h3 : evR Xo c (e Z) z = 0 := by rw [evR_map hL he.1 ψ hz, h2, map_zero]
    have h4 : evR Xo c (e Z) ((U σ).un k y) = 0 := by
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      rw [hL.wt 0 0 (e Z) he _ t' _ _ (hL.test _ _) (hL.test _ _) hbz, h3, mul_zero]
    have h5 := hOver y.1 y.2
    rw [hrd, h4] at h5
    exact zero_ne_one (α := ℂ) h5
  subst hCZ
  have hgA : ∀ j, g j ∈ GlobalTheory.AllWt.secZ Xo c (exZ Dw a) := fun j => by
    rw [← secZ_eq_allWt]; exact hg j
  set ex := exZ Dw a with hex

  let G : Fin (N + 1) → C.R := fun j => evR Xo c (g j) C.y
  have hιG : ∀ j, C.R.val (G j) = ((∏ i, C.t i ^ ex i : (Om C.Z)ˣ) : Om C.Z) * evC h C.Z (g j) := by
    intro j
    rw [← evR_map hL (hg j).1 C.R.val C.gen]
    exact GlobalTheory.evR_frBor_of_mem_secZ hS Xo c ex (hgA j) (Om C.Z) C.t _ _ C.bor
  obtain ⟨wc, hwc⟩ : ∃ wc : CAt σ, toC wc = w := ⟨w, rfl⟩
  have hψG : ∀ j, ((∏ i, t' i ^ ex i : (CAt σ)ˣ) : CAt σ) * ψ (G j) = wc * φ (evC h C.Z (g j)) := by
    intro j
    have h1 : evR Xo c (g j) ((U σ).un k y) = ((∏ i, t' i ^ ex i : (CAt σ)ˣ) : CAt σ) * evR Xo c (g j) z :=
      GlobalTheory.evR_frBor_of_mem_secZ hS Xo c ex (hgA j) (CAt σ) t' _ _ hbz
    have h2 : evR Xo c (g j) z = ψ (G j) := evR_map hL (hg j).1 ψ hz
    rw [← h2, ← h1]
    have h3 := hr j
    rw [hrd, ← hwc] at h3
    exact h3
  set T : (Om C.Z)ˣ := ∏ i, C.t i ^ ex i with hT
  set T' : (CAt σ)ˣ := ∏ i, t' i ^ ex i with hT'
  have hw' : wc ≠ 0 := fun h0 => hw (by rw [← hwc, h0]; rfl)
  have hE0 : φ (evC h C.Z (g 0)) ≠ 0 := (map_ne_zero_iff φ φ.toRingHom.injective).2 hB.1
  have hψ0 : ψ (G 0) ≠ 0 := by
    intro h0
    have h1 := hψG 0
    rw [h0, mul_zero] at h1
    exact mul_ne_zero hw' hE0 h1.symm
  have hι0 : C.R.val (G 0) ≠ 0 := by
    rw [hιG]
    exact mul_ne_zero T.ne_zero hB.1
  have hrat : ∀ j, ψ (G j) * φ (C.R.val (G 0)) = ψ (G 0) * φ (C.R.val (G j)) := by
    intro j
    have h1 := hψG j
    have h2 := hψG 0
    refine mul_left_cancel₀ T'.ne_zero ?_
    rw [hιG, hιG, map_mul, map_mul]
    linear_combination (φ (T : Om C.Z) * φ (evC h C.Z (g 0))) * h1 - (φ (T : Om C.Z) * φ (evC h C.Z (g j))) * h2
  have hgen : IntermediateField.adjoin c.F (Set.range fun j => C.R.val (G j) / C.R.val (G 0)) = ⊤ := by
    have e1 : (fun j => C.R.val (G j) / C.R.val (G 0)) = fun j => evC h C.Z (g j) / evC h C.Z (g 0) := by
      funext j
      rw [hιG, hιG, mul_div_mul_left _ _ T.ne_zero]
    rw [e1]
    exact hB.2
  have hψφ : ψ = φ.comp C.R.val :=
    AlgHom.ext fun b => eq_of_ratios C.R.val Subtype.val_injective ψ φ G hι0 hψ0 hrat hgen b

  obtain ⟨w₁, hw₁⟩ := hL.bc _ _ φ C.yg
  have h1 := PullbackSections.frMap_trans _ _ C.gen hw₁
  rw [← hψφ] at h1
  obtain rfl : z = w₁ := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ _ C.y).1 _ _ hz h1
  have hbc := GlobalTheory.SupGeneric.frBor_of_frMap φ C.bor hφ hw₁
  have hgp := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)
  exact ⟨_, hgp.2.1 _ _ _ _ _ (hgp.2.1 _ _ _ _ _ hb hbc) hbz⟩

end GlobalTheory.CompanionTheory.Ar.SameFlag
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodEmbeddingComponentSectionsStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_embedding_component_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (Z : Comp Xo c) (k : (U σ).Comp), Over (U σ) (e Z) k → ∀ (a : WZ E) (N : ℕ) (g : Fin (N + 1) → Rul Xo c), (∀ j, g j ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a) → BirOn h Z g → ∀ (φ : Om Z →ₐ[c.F] CAt σ) (x₀ y : ((U σ).X k).dom) (y₁ : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y₁ → FrBor t ((U σ).un k x₀) y₁ → ∀ w : ℂ, w ≠ 0 → (∀ j, rdU (U σ) (g j) k y.1 = w * toC (φ (evC h Z (g j)))) → ∃ t' : Ix Dw → (CAt σ)ˣ, FrBor t' ((U σ).un k x₀) ((U σ).un k y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SameFlag.frBor_of_proportional_readings | exact GlobalTheory.CompanionTheory.Ar.SameFlag.frBor_of_proportional_readings | (intros; apply GlobalTheory.CompanionTheory.Ar.SameFlag.frBor_of_proportional_readings <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelLeCompact
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasModelOfSpreading

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHolds
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

namespace GlobalTheory.CompanionTheory.SwUnf
open GlobalTheory.Eis

variable {D : D7} {n : ℕ}

theorem sect_facts {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {Φ : schwartzA θ V.rank n} (hS : Std D n V ψ χ θ μ ω H l s ν Φ) {z : ℂ} (hz : (n : ℝ) / 2 < z.re) :
    Continuous (sect ω H Φ z) ∧ LeftInv (P D n ⊓ GF D n) (sect ω H Φ z) ∧
    (∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → Matrix.GeneralLinearGroup.det a = 1 → ∀ g,
      sect ω H Φ z (p * g) = sect ω H Φ z g) ∧
    ∀ C : Set (G D n), IsCompact C → ∃ u : Cosets (P D n) (GF D n) → ℝ, Summable u ∧
      ∀ q, ∀ g ∈ C, ‖term (P D n) (GF D n) (sect ω H Φ z) g q‖ ≤ u q := by
  obtain ⟨𝓕, hμ⟩ := hS.hμ
  have hsec := GlobalTheory.StdUnn.SiegelSection.fock_mem_degenerate D n V ψ hS.hψ χ hS.hχ hS.hη θ hS.hθ μ 𝓕 hμ ω hS.hω l hS.hl s hS.hs Φ hS.hΦ
  have e : ∀ z, sect ω H Φ z = stdSec H (fun g : G D n => (ω g Φ).1 0) (s0 V n) z :=
    fun z => funext fun g => mul_comm _ _
  have hs2 := GlobalTheory.StdUnn.PolesModel.isSection_stdSec hS.hH hsec z
  rw [← e] at hs2
  refine ⟨hs2.2.1, GlobalTheory.StdUnn.LeftInvSect.leftInv_sect D n (GlobalTheory.StdUnn.Iwasawa.exists_mul D n) V ψ χ θ μ ω hS.hχ hS.hω H hS.hH Φ z,
    fun p hp a ha h1 g => ?_, fun C hC => ?_⟩
  · rw [hs2.1 p hp a ha g, h1]
    simp [npow]
  · haveI := t2Space_adeleRing' (F := D.host.F)
    have h1 : Continuous (iwAbs (PolesModel.modP (D := D) (n := n)) (K D n)) :=
      PolesModel.isIwasawa.continuous_iwAbs GlobalTheory.StdUnn.Model.isClosed_P PolesModel.continuous_modP GlobalTheory.StdUnn.Model.isCompact_K
    have h2 : Continuous fun g => Real.log (iwAbs (PolesModel.modP (D := D) (n := n)) (K D n) g) :=
      (NNReal.continuous_coe.comp h1).log fun g => (NNReal.coe_pos.2 (iwAbs_pos _ _ g)).ne'
    have hc : Continuous fun x : ℂ × G D n => stdSec H (fun g : G D n => (ω g Φ).1 0) (s0 V n) x.1 x.2 := by
      simp only [stdSec, PolesModel.height_eq hS.hH, npow_eq_exp (iwAbs_pos _ _ _)]
      exact (hsec.2.1.comp continuous_snd).mul (((Complex.continuous_ofReal.comp (h2.comp continuous_snd)).mul
        (continuous_fst.sub continuous_const)).cexp)
    obtain ⟨u, hu, hb⟩ := exists_majorant (Φ := fun s => stdSec H (fun g : G D n => (ω g Φ).1 0) (s0 V n) s)
      (χ := χ.comp PolesModel.detP) (ρ := (n : ℝ) / 2) (σ := (n : ℝ) / 2) PolesModel.isIwasawa GlobalTheory.StdUnn.Model.isCompact_K
      hc.continuousOn
      (fun z _ => by
        have := (PolesModel.isSection_iff.1 (PolesModel.isSection_stdSec hS.hH hsec z)).1
        push_cast
        exact this) PolesModel.summable_spherical (S := {z}) isCompact_singleton (Set.singleton_subset_iff.2 hz) hC
    refine ⟨u, hu, fun q g hg => ?_⟩
    rw [e]; exact hb q z rfl g hg

end GlobalTheory.CompanionTheory.SwUnf

namespace GlobalTheory.CompanionTheory.SwUnf
open GlobalTheory.Eis GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect

variable {D : D7} {n : ℕ}

theorem nb_add {nb : hermA D n → G D n} (h : IsNMap nb) (a b : hermA D n) : nb (a + b) = nb a * nb b := by
  apply mat_inj
  rw [mat_mul, h, h, h, submatrix_fromBlocks_mul]
  simp [add_comm]

theorem continuous_blk4_right : Continuous fun b : Mx D n n => (blk4 1 b 0 1 : Mx D (n + n) (n + n)) := by
  refine continuous_matrix fun i j => ?_
  simp only [blk4, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j
  · exact continuous_const
  · exact continuous_apply_apply i j
  · exact continuous_const
  · exact continuous_const

theorem nb_continuous {nb : hermA D n → G D n} (h : IsNMap nb) : Continuous nb := by
  have hn : ∀ b, (nb b)⁻¹ = nb (-b) := fun b => by
    rw [eq_comm, eq_inv_iff_mul_eq_one, ← nb_add h]
    apply mat_inj
    rw [neg_add_cancel, h, mat_one]
    simp [block_matrix_one]
  rw [(isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)).continuous_iff, Units.continuous_iff]
  constructor
  · have : Continuous fun b : hermA D n => (blk4 1 b.1 0 1 : Mx D (n + n) (n + n)) :=
      continuous_blk4_right.comp continuous_subtype_val
    exact this.congr fun b => (h b).symm
  · have : Continuous fun b : hermA D n => (blk4 1 (-b).1 0 1 : Mx D (n + n) (n + n)) :=
      continuous_blk4_right.comp (continuous_subtype_val.comp continuous_neg)
    refine this.congr fun b => ?_
    rw [← h, ← hn]
    simp [mat, map_inv]

theorem nb_mem_GF {nb : hermA D n → G D n} (h : IsNMap nb) (l : ratHerm D n) : ∃ b : Matrix (Fin n) (Fin n) D.host.E,
    nb l.1 ∈ GF D n ∧ mat (nb l.1) = blk4 1 (b.map (incA D)) 0 1 := by
  obtain ⟨b, hb⟩ := AddSubgroup.mem_comap.1 l.2
  have hb' : b.map (incA D) = l.1.1 := hb
  refine ⟨b, ?_, by rw [h, hb']⟩
  rw [ChartRat.mem_GF_iff, h]
  refine ⟨blk4 1 b 0 1, ?_⟩
  change (blk4 1 b 0 1).map (incA D) = _
  rw [GlobalTheory.CompanionTheory.Hypotheses₂.WeilU.blk4_map_alt, hb']
  have e0 : (0 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 0 := map_zero (incA D).mapMatrix
  have e1 : (1 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 1 := map_one (incA D).mapMatrix
  rw [e0, e1]

theorem rat_mem_of (b : Matrix (Fin n) (Fin n) D.host.E) : (b.map (incA D) : Mx D n n) ∈ ratMx D n n :=
  ⟨b, rfl⟩

theorem countable_E : Countable D.host.E :=
  (Module.finBasis ℚ D.host.E).equivFun.injective.countable

theorem countable_mat (a b : ℕ) : Countable (Matrix (Fin a) (Fin b) D.host.E) :=
  haveI := countable_E (D := D)
  inferInstanceAs (Countable (Fin a → Fin b → D.host.E))

theorem countable_ratHerm : Countable (ratHerm D n) := by
  haveI := countable_mat (D := D) n n
  have hinj : Function.Injective fun l : ratHerm D n => (Classical.choose (AddSubgroup.mem_comap.1 l.2) :
      Matrix (Fin n) (Fin n) D.host.E) := fun a b h => by
    have ha := Classical.choose_spec (AddSubgroup.mem_comap.1 a.2)
    have hb := Classical.choose_spec (AddSubgroup.mem_comap.1 b.2)
    simp only at h
    rw [h] at ha
    exact Subtype.ext (Subtype.ext (ha.symm.trans hb))
  exact hinj.countable

theorem countable_GF : Countable (GF D n) := by
  haveI := countable_mat (D := D) (n + n) (n + n)
  have hinj : Function.Injective (ratOf (D := D) (n := n)) := fun a b h =>
    Subtype.ext (mat_inj (by rw [mat_ratOf, mat_ratOf, h]))
  exact hinj.countable

theorem countable_cosets : Countable (Cosets (P D n) (GF D n)) := by
  haveI := countable_GF (D := D) (n := n)
  exact Quotient.countable

theorem unfold : PositivityTheory.PfSWUS.Unfold := by
  intro D n V ψ χ θ μ ω H l s ν Φ hS hR nb lam 𝓖 hC w hw β hβ z hz g
  obtain ⟨hcont, hinv, hdet, hmaj⟩ := sect_facts hS hz
  obtain ⟨hNb, hHaar, hFD, hvol⟩ := hC
  have hψ := hS.hψ
  have hcn := nb_continuous hNb
  have hcolat := GlobalTheory.CompanionTheory.HermVol.isCoLat_herm (D := D) (r := n)
  haveI : DiscreteTopology (ratHerm D n) := hcolat.1
  haveI : Countable (ratHerm D n) := countable_ratHerm
  haveI : Countable (Cosets (P D n) (GF D n)) := countable_cosets
  obtain ⟨e, he, hr, hterm⟩ := GlobalTheory.T.big_cell_cosets_hermitian_param hw hNb
  choose bb hbG hbm using nb_mem_GF hNb
  let F : Cosets (P D n) (GF D n) → hermA D n → ℂ := fun q b => term (P D n) (GF D n) (sect ω H Φ z) (nb b * g) q
  let ch : hermA D n → ℂ := fun b => ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))
  let τ : ratHerm D n → Cosets (P D n) (GF D n) ≃ Cosets (P D n) (GF D n) := fun l => rmulEquiv _ _ ⟨nb l.1, hbG l⟩
  have hτ : ∀ (l : ratHerm D n) q b, F q ((l : hermA D n) + b) = F (τ l q) b := fun l q b => by
    simp only [F]
    rw [nb_add hNb, mul_assoc]
    exact term_mul_left hinv ⟨nb l.1, hbG l⟩ _ q
  have hchc : Continuous ch := by
    have := GlobalTheory.CompanionTheory.HermPoisson.continuous_chi hψ (-(β.1.map (incA D)) : Mx D n n)
    exact this.congr fun b => GlobalTheory.CompanionTheory.HermPoisson.chi_neg_left ψ _ b
  obtain ⟨K0, hK0, hKc⟩ := hcolat.2
  obtain ⟨u, hu, hub⟩ := hmaj ((fun d => nb d * g) '' K0) (hK0.image (hcn.mul continuous_const))
  have hM : ∀ b, Summable (fun q => ‖F q b‖) ∧ ∑' q, ‖F q b‖ ≤ ∑' q, u q := fun b => by
    obtain ⟨γ, hγ, hb⟩ := hKc b
    have hb2 : ∀ q, ‖F q b‖ ≤ u ((τ ⟨γ, hγ⟩).symm q) := fun q => by
      have := hτ ⟨γ, hγ⟩ ((τ ⟨γ, hγ⟩).symm q) b
      rw [Equiv.apply_symm_apply] at this
      rw [← this]
      exact hub _ _ ⟨_, hb, rfl⟩
    have hs2 : Summable fun q => u ((τ ⟨γ, hγ⟩).symm q) := (τ ⟨γ, hγ⟩).symm.summable_iff.2 hu
    refine ⟨.of_nonneg_of_le (fun _ => norm_nonneg _) hb2 hs2, ?_⟩
    refine (Summable.tsum_le_tsum hb2 (.of_nonneg_of_le (fun _ => norm_nonneg _) hb2 hs2) hs2).trans_eq ?_
    exact (τ ⟨γ, hγ⟩).symm.tsum_eq u
  have := GlobalTheory.T.fundamental_domain_fourier_unfolding lam (ratHerm D n) 𝓖 hFD hvol cosetCell (⊥ : Submodule D.host.E (Fin n → D.host.E)) F
    (fun b => sect ω H Φ z (w * nb b * g)) ch
    (fun q => Continuous.aestronglyMeasurable (hcont.comp (continuous_const.mul (hcn.mul continuous_const))))
    hchc.aestronglyMeasurable
    (fun b => hψ.2.1 _)
    (fun a b => by
      simp only [ch, AddSubgroup.coe_add]
      rw [Matrix.mul_add, Matrix.trace_add, GlobalTheory.CompanionTheory.HermPoisson.halfTr_add', neg_add, AddChar.map_add_eq_mul])
    (fun l => by
      have := GlobalTheory.CompanionTheory.HermPoisson.chi_rat hψ (m := (-(β.1.map (incA D)) : Mx D n n)) (neg_mem (rat_mem_of β.1)) l
      rw [GlobalTheory.CompanionTheory.HermPoisson.chi_neg_left] at this
      exact this)
    _ hM τ hτ (fun l q => GlobalTheory.T.coset_cell_invariant_unipotent q ⟨nb l.1, hbG l⟩ (bb l) (hbm l)) e he hr
    (fun l b => by
      simp only [F]
      rw [hterm _ hinv, nb_add hNb]
      simp only [mul_assoc])
    (fun y hy => by
      obtain ⟨ν', h1, h2⟩ := GlobalTheory.T.nondegenerate_character_cell_factorization hψ β hβ y hy
      refine ⟨ν', h1, fun q hq b => ?_⟩
      obtain ⟨p, hp, a, ha, hd, hpe⟩ := h2 (q.out : GF D n) (nb ν') (q.out : GF D n).2 (ratOf q.out) (mat_ratOf _) hq (hNb _)
      simp only [F, term]
      rw [nb_add hNb, mul_assoc (nb ν'), ← mul_assoc _ (nb ν'), hpe, mul_assoc, hdet p hp a ha hd])
  exact this

end GlobalTheory.CompanionTheory.SwUnf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHoldsStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_holds : PositivityTheory.PfSWUS.Unfold := by
  first | exact @GlobalTheory.CompanionTheory.SwUnf.unfold | exact GlobalTheory.CompanionTheory.SwUnf.unfold | (intros; apply GlobalTheory.CompanionTheory.SwUnf.unfold <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemKLOfTrivLam
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.KLFinite

theorem memKL_of_triv_lam {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    (x : T ⟶ A) (hx : Triv (ev (abelian₂ A L) (fst T A ≫ x) (snd T A))) : GlobalTheory.MemKL A L x := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have hl : lam (cls L hL) (fst T A ≫ x) (snd T A) = 0 := by
    have e := (triv_ev_iff hP _ _).1 hx
    rwa [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd] at e
  have hD : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
    (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  have e₁ := pull_translDiff hL x hD (fst T A) (snd T A)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have e₂ : cls _ hD = CechPic.pull (fst T A).left
      (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      ← sub_eq_zero, ← hl, lam]
    abel
  rw [cls_pull hD, e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T A).left ⁻¹ᵁ V).ι ≫ (fst T A).left) (fun z ↦ z.2) hc

theorem memKL_congr {S X : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {t t' : X ⟶ S} (e : t = t')
    (x : Over.mk t ⟶ A) (x' : Over.mk t' ⟶ A) (hl : x.left = x'.left) (h : GlobalTheory.MemKL A L x) :
    GlobalTheory.MemKL A L x' := by
  subst e
  have e : x = x' := Over.OverMorphism.ext hl
  rwa [← e]

theorem finite_memKL (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (hB : IsAbelianScheme B)
    (M : LB B.left) (hM : M.IsLB) (hA : Out.RelAmple B M) :
    Finite {x : 𝟙_ (Over (Sp k)) ⟶ B // GlobalTheory.MemKL B M x} := by
  obtain ⟨H, j, -, hfin, hH⟩ :=
    GlobalTheory.KernelRep.exists_finite_closed_kernel GlobalTheory.abelianSchemeLaws_all.1.globalFns k B hB M hM hA
  have : IsFinite H.hom := hfin
  have : IsFinite (toUnit H).left := hfin
  have hf := GlobalTheory.TorsionDivisible.finite_fibre_points (toUnit H) (𝟙 _)
  refine Finite.of_surjective
    (fun z : {x : 𝟙_ (Over (Sp k)) ⟶ H // x ≫ toUnit H = 𝟙 _} ↦
      (⟨z.1 ≫ j, (hH _ _).2 ⟨z.1, rfl⟩⟩ : {x : 𝟙_ (Over (Sp k)) ⟶ B // GlobalTheory.MemKL B M x})) fun x ↦ ?_
  obtain ⟨z, hz⟩ := (hH _ _).1 x.2
  exact ⟨⟨z, toUnit_unique _ _⟩, Subtype.ext hz⟩

theorem kFinite : KFinite := by
  intro S A _ hA L hL hamp k _ _ t
  let B : Over (Sp k) := (Over.pullback t).obj A
  have gp : IsGrpPullback B A t (pullback.fst A.hom t) := isGrpPullback_pullback A t
  have hB : IsAbelianScheme B := by
    have := hA.comm
    have hc : IsCommMonObj B := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (gp.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← gp.2 T x y (pushPt gp.1.w x) (pushPt gp.1.w y) rfl rfl,
        ← gp.2 T y x (pushPt gp.1.w y) (pushPt gp.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) gp.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) gp.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) gp.1 hA.geomConnected⟩
  have := hA.proper
  have hM : (L.pull (pullback.fst A.hom t)).IsLB := pull_isLB hL _
  have hAmp : Out.RelAmple B (L.pull (pullback.fst A.hom t)) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL hamp (IsPullback.of_hasPullback A.hom t)
  have hK := finite_memKL k B hB _ hM hAmp
  have hw : ∀ x : Over.mk t ⟶ A, x.left ≫ A.hom = 𝟙 (Sp k) ≫ t := fun x ↦ by
    rw [Over.w x, Category.id_comp]; rfl
  let pt : (Over.mk t ⟶ A) → (𝟙_ (Over (Sp k)) ⟶ B) := fun x ↦ GlobalTheory.AbDual.liftPt gp (𝟙 _) x.left (hw x)
  have hpt : ∀ x, (pt x).left ≫ pullback.fst A.hom t = x.left := fun x ↦
    GlobalTheory.AbDual.liftPt_left gp _ _ _
  have hmem : ∀ x : Over.mk t ⟶ A, Triv (ev (abelian₂ A L) (fst (Over.mk t) A ≫ x) (snd (Over.mk t) A)) →
      GlobalTheory.MemKL B (L.pull (pullback.fst A.hom t)) (pt x) := fun x hx ↦
    GlobalTheory.memKL_of_push gp hL hM ((cls_eq_iff hM hM).1 rfl) (pt x)
      (memKL_congr (Category.id_comp t).symm x _ (hpt x).symm (memKL_of_triv_lam hL x hx))
  have : Finite {x : Over.mk t ⟶ A | Triv (ev (abelian₂ A L) (fst (Over.mk t) A ≫ x) (snd (Over.mk t) A))} :=
    Finite.of_injective
      (fun x ↦ (⟨pt x.1, hmem x.1 x.2⟩ : {y : 𝟙_ (Over (Sp k)) ⟶ B //
        GlobalTheory.MemKL B (L.pull (pullback.fst A.hom t)) y})) fun x y e ↦ by
      refine Subtype.ext (Over.OverMorphism.ext ?_)
      have e' : pt x.1 = pt y.1 := congrArg Subtype.val e
      rw [← hpt x.1, ← hpt y.1, e']
  exact Set.toFinite _

end GlobalTheory.CompanionTheory.KLFinite
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaFourierJacobiLatticeSwap
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaFourierJacobiLatticeSwap
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem term_after : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ThTwist → ∀ (χ' : (AE D)ˣ →* Circle), IsHeckeChar D χ' → ∀ θ : InfFam D, IsInfFam θ → ∀ Ω, IsTh ψ χ' θ b₀ m.μ Ω → ∀ (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsLaw χ s f → ∀ (g γ : _), γ ∈ GF D p → ∀ (T : Mx D ρ p × Mx D ρ p → Mx D ρ p × Mx D ρ p), (∀ y x : Mx D ρ p, ∃ z' : hermA D ρ, M.emb γ * (M.nzx 0 x * M.sh y) = M.nzx z' (T (y, x)).2 * M.sh (T (y, x)).1 * M.emb γ) → ∀ v : Mx D ρ p × Mx D ρ p, (∀ η : Matrix (Fin ρ) (Fin p) D.host.E, ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g)))‖ = ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + (T v).1) * M.emb γ * g)‖) ∧ (∑' η : Matrix (Fin ρ) (Fin p) D.host.E, Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g)))) * conj (th ψ b₀ (Ω 1) 0 v.2 v.1) = GlobalTheory.CompanionTheory.FJE.Ap ψ b₀ (fun y => Wz M m ψ b₀ f (M.sh y * M.emb γ * g)) (Ω γ) (T v) := by
  intro D n ρ p hn M m ψ hψ b₀ hb₀ hTw χ' hχ' θ hθ Ω hΩ χ s f hf g γ hγ T hT v
  obtain ⟨z', hz'⟩ := hT v.1 v.2
  have hz : M.emb γ * (M.nzx 0 v.2 * M.sh v.1) = M.nzx z' (T v).2 * M.sh (T v).1 * M.emb γ := hz'
  have hterm : ∀ η : Matrix (Fin ρ) (Fin p) D.host.E,
      Wz M m ψ b₀ f (M.sh (rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g))) =
        chz ψ b₀ z' * (chv ψ b₀ (T v).2 (rt η) * Wz M m ψ b₀ f (M.sh (rt η + (T v).1) * M.emb γ * g)) := by
    intro η
    have e1 : M.sh (rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g)) =
        M.sh (rt η) * (M.nzx z' (T v).2 * (M.sh (T v).1 * M.emb γ * g)) := by
      calc M.sh (rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g))
          = M.sh (rt η) * ((M.emb γ * (M.nzx 0 v.2 * M.sh v.1)) * g) := by simp only [mul_assoc]
        _ = M.sh (rt η) * (M.nzx z' (T v).2 * (M.sh (T v).1 * M.emb γ * g)) := by
            rw [hz]; simp only [mul_assoc]
    have e2 : M.sh (rt η) * (M.sh (T v).1 * M.emb γ * g) = M.sh (rt η + (T v).1) * M.emb γ * g := by
      rw [← sh_add M (rt η) (T v).1]; simp only [mul_assoc]
    rw [e1, GlobalTheory.T.coefficient_heisenberg_equivariance M m ψ hψ b₀ χ s f hf (rt η) z' (T v).2 _, e2, mul_assoc]
  obtain ⟨-, hnorm, -, -⟩ := GlobalTheory.CompanionTheory.FJE.CentralChar.chz_facts ψ hψ b₀
  have hchv : ∀ x y : Mx D ρ p, ‖chv ψ b₀ x y‖ = 1 := fun x y => hψ.2.1 _
  have hth : th ψ b₀ (Ω 1) 0 v.2 v.1 = chz ψ b₀ z' * dsum ψ b₀ (Ω γ) (T v).2 (T v).1 := by
    rw [hTw D n ρ p hn M m ψ hψ b₀ hb₀ χ' hχ' θ hθ Ω hΩ γ hγ 0 v.2 v.1 z' (T v).2 (T v).1 hz]
    rfl
  have hcc : chz ψ b₀ z' * conj (chz ψ b₀ z') = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; simp
  refine ⟨fun η => ?_, ?_⟩
  · rw [hterm η, norm_mul, norm_mul, hnorm, hchv, one_mul, one_mul]
  · simp_rw [hterm]
    rw [tsum_mul_left, hth, map_mul, Ap]
    have hd : (∑' η : Matrix (Fin ρ) (Fin p) D.host.E,
        chv ψ b₀ (T v).2 (rt η) * Wz M m ψ b₀ f (M.sh (rt η + (T v).1) * M.emb γ * g)) =
        dsum ψ b₀ (fun y => Wz M m ψ b₀ f (M.sh y * M.emb γ * g)) (T v).2 (T v).1 := rfl
    rw [hd]
    calc _ = (chz ψ b₀ z' * conj (chz ψ b₀ z')) *
          (dsum ψ b₀ (fun y => Wz M m ψ b₀ f (M.sh y * M.emb γ * g)) (T v).2 (T v).1 *
            conj (dsum ψ b₀ (Ω γ) (T v).2 (T v).1)) := by ring
      _ = _ := by rw [hcc, one_mul]

end GlobalTheory.CompanionTheory.FJE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaFourierJacobiLatticeSwapStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_fourier_jacobi_lattice_swap : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ThTwist → ∀ (χ' : (AE D)ˣ →* Circle), IsHeckeChar D χ' → ∀ θ : InfFam D, IsInfFam θ → ∀ Ω, IsTh ψ χ' θ b₀ m.μ Ω → ∀ (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsLaw χ s f → ∀ (g γ : _), γ ∈ GF D p → ∀ (T : Mx D ρ p × Mx D ρ p → Mx D ρ p × Mx D ρ p), (∀ y x : Mx D ρ p, ∃ z' : hermA D ρ, M.emb γ * (M.nzx 0 x * M.sh y) = M.nzx z' (T (y, x)).2 * M.sh (T (y, x)).1 * M.emb γ) → ∀ v : Mx D ρ p × Mx D ρ p, (∀ η : Matrix (Fin ρ) (Fin p) D.host.E, ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g)))‖ = ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + (T v).1) * M.emb γ * g)‖) ∧ (∑' η : Matrix (Fin ρ) (Fin p) D.host.E, Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g)))) * conj (th ψ b₀ (Ω 1) 0 v.2 v.1) = GlobalTheory.CompanionTheory.FJE.Ap ψ b₀ (fun y => Wz M m ψ b₀ f (M.sh y * M.emb γ * g)) (Ω γ) (T v) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.term_after | exact GlobalTheory.CompanionTheory.FJE.term_after | (intros; apply GlobalTheory.CompanionTheory.FJE.term_after <;> assumption)
end
end

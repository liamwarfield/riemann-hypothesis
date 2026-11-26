module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsWeightEqParameterSubRho
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairFixedVectorLatticeVacuumOffLevels
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnCharacterReductionEqExp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCharacterRestrictionTraitSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCharacterRestrictionTraitSurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TorusOnto

theorem exists_finite_quotient_ne_zero {X : Type} [AddCommGroup X] [Module.Finite ℤ X] (M : AddSubgroup X)
    (hM : M ≠ ⊤) : ∃ (F : Type) (_ : AddCommGroup F) (_ : Finite F) (l : X →+ F), l ≠ 0 ∧ ∀ x ∈ M, l x = 0 := by
  have hM' : M.toIntSubmodule ≠ ⊤ := fun h => hM (eq_top_iff.2 fun x _ => by
    have : x ∈ M.toIntSubmodule := h ▸ Submodule.mem_top
    exact this)
  obtain ⟨N, hN, hMN⟩ := (IsCoatomic.eq_top_or_exists_le_coatom M.toIntSubmodule).resolve_left hM'
  haveI : IsSimpleModule ℤ (X ⧸ N) := isSimpleModule_iff_isCoatom.2 hN
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 this
  haveI : Finite (ℤ ⧸ I) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (Ring.ne_bot_of_isMaximal_of_not_isField hI Int.not_isField)
  haveI : Finite (X ⧸ N) := Finite.of_equiv _ e.toEquiv.symm
  refine ⟨X ⧸ N, inferInstance, inferInstance, N.mkQ.toAddMonoidHom, fun h => hN.1 ?_, fun x hx => ?_⟩
  · refine eq_top_iff.2 fun x _ => (Submodule.Quotient.mk_eq_zero N).1 ?_
    exact DFunLike.congr_fun h x
  · exact (Submodule.Quotient.mk_eq_zero N).2 (hMN hx)

instance isFinite_splitTorus (S : Scheme.{0}) (F : Type) [AddCommGroup F] [Finite F] :
    IsFinite (splitTorus S F).hom := by
  have : IsFinite (splitTorusAff ZU.{0} F).hom := by
    show IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ZU.{0} (torusRing ZU.{0} F))))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 inferInstance
  exact inferInstanceAs (IsFinite (pullback.snd _ _))

end GlobalTheory.TorusOnto

namespace GlobalTheory.TorusOnto

theorem restrict_surjective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t')
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    Function.Surjective ρ := by
  intro E _ _ _ H R _ _ _ t P W _ _ _ t' P' V _ _ _ ψ _ tV mV Ω _ α β hβ tΩ n n' j _ t₀ m₀ h₀ m₀' ρ _ hΩ hφ₀ h₀j
  classical
  by_contra hρ
  have hM : ρ.range ≠ ⊤ := fun h => hρ (AddMonoidHom.range_eq_top.1 h)
  obtain ⟨F, _, _, l, hl0, hl⟩ := exists_finite_quotient_ne_zero ρ.range hM
  have hlρ : l.comp ρ = 0 := AddMonoidHom.ext fun x => hl _ ⟨x, rfl⟩
  have key : GlobalTheory.SplitTorus.torusMap (Sp V) l ≫ j = GlobalTheory.SplitTorus.torusMap (Sp V) 0 ≫ j := by
    haveI : IsSeparated tV.G.hom := tV.semi.separated
    have hjac : maximalIdeal V ≤ Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    refine GlobalTheory.hom_eq_of_thickenings_of_isProper V (maximalIdeal V) hjac (splitTorus (Sp V) F) tV.G _ _ fun e => ?_
    have hψ : ∀ x ∈ maximalIdeal R, ψ x ∈ maximalIdeal V := fun x hx =>
      (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 hx (isUnit_of_map_unit ψ x hu)
    have hI : maximalIdeal V ^ (e + 1) ≠ ⊤ := fun h =>
      (maximalIdeal.isMaximal V).ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
    haveI : Nontrivial (V ⧸ maximalIdeal V ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hI
    haveI : IsLocalRing (V ⧸ maximalIdeal V ^ (e + 1)) := .of_surjective' _ Ideal.Quotient.mk_surjective
    let q : V →+* V ⧸ maximalIdeal V ^ (e + 1) := Ideal.Quotient.mk _
    have he := isGrpPullback_pullback tV.G (thick V (maximalIdeal V) e)
    have ha : ∀ x ∈ maximalIdeal R ^ (e + 1), (q.comp ψ) x = 0 := by
      intro x hx
      refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
      have hle : Ideal.map ψ (maximalIdeal R ^ (e + 1)) ≤ maximalIdeal V ^ (e + 1) := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hψ) _
      exact hle (Ideal.mem_map_of_mem ψ hx)
    have hR : IsGrpPullback (thickObj V (maximalIdeal V) e tV.G) t.G (spMap (q.comp ψ))
        (pullback.fst tV.G.hom (thick V (maximalIdeal V) e) ≫ mV.φ) :=
      (he.comp mV.cart).congr (by rw [spMap, spMap, ← Spec.map_comp]; rfl) rfl
    obtain ⟨-, hfac⟩ := GlobalTheory.T.uniformisationTorus_mono_and_factor E H R (maximalIdeal R) t P _ (q.comp ψ) e ha _ _ hR
    obtain ⟨ρe, hρe⟩ := hfac P'.D.toPre.X (GlobalTheory.TorusPart.pullTorus he j) inferInstance

    have hres : ∀ x ∈ maximalIdeal V ^ (e + 1), residue V x = 0 := fun x hx =>
      (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
    have ke := GlobalTheory.TorusPart.isGrpPullback_thickLift hres m₀.cart
    have ha' : ∀ x ∈ maximalIdeal R ^ (e + 1), ((residue V).comp ψ) x = 0 := fun x hx =>
      h₀ x (Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
    have e1 : GlobalTheory.TorusPart.pullTorus ke (GlobalTheory.TorusPart.pullTorus he j) = GlobalTheory.TorusPart.pullTorus m₀.cart j :=
      GlobalTheory.TorusPart.pullTorus_pullTorus ke he m₀.cart (GlobalTheory.TorusPart.thickPt_thick hres).symm
        (GlobalTheory.TorusPart.thickLift_fst hres m₀.cart).symm j
    have e2 : GlobalTheory.TorusPart.pullTorus ke (GlobalTheory.TorusPart.gtTorus (P.U.gt e) ha hR) =
        GlobalTheory.TorusPart.gtTorus (P.U.gt e) ha' m₀'.cart :=
      GlobalTheory.TorusPart.pullTorus_gtTorus (σ := Ideal.Quotient.lift _ (residue V) hres) (P.U.gt e) ha ha' hR m₀'.cart ke
        (RingHom.ext fun x => rfl)
        (hφ₀.trans (by rw [← Category.assoc, GlobalTheory.TorusPart.thickLift_fst]))
    obtain ⟨hmono, hfac'⟩ := GlobalTheory.T.uniformisationTorus_mono_and_factor E H R (maximalIdeal R) t P _ ((residue V).comp ψ) e ha' t₀.G m₀'.φ m₀'.cart
    obtain ⟨u, hu⟩ := hfac' P.D.toPre.X (GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀') inferInstance
    have e3 := congrArg (GlobalTheory.TorusPart.pullTorus ke) hρe
    rw [e1, GlobalTheory.TorusPart.pullTorus_torusMap_comp, e2, h₀j, hu, ← Category.assoc,
      ← GlobalTheory.SplitTorus.torusMap_comp, cancel_mono] at e3
    have e4 : ρe = ρ.comp u := (GlobalTheory.SplitTorus.torusMap_injective e3).symm
    have hstep : GlobalTheory.TorusPart.pullTorus he (GlobalTheory.SplitTorus.torusMap _ l ≫ j) =
        GlobalTheory.TorusPart.pullTorus he (GlobalTheory.SplitTorus.torusMap _ (0 : P'.D.toPre.X →+ F) ≫ j) := by
      rw [GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hρe, ← Category.assoc,
        ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp, e4,
        ← AddMonoidHom.comp_assoc, hlρ, AddMonoidHom.zero_comp, AddMonoidHom.zero_comp]
    have k1 := GlobalTheory.TorusPart.pullTorus_left he (GlobalTheory.SplitTorus.torusMap _ l ≫ j)
    have k2 := GlobalTheory.TorusPart.pullTorus_left he (GlobalTheory.SplitTorus.torusMap _ (0 : P'.D.toPre.X →+ F) ≫ j)
    rw [hstep] at k1
    have k3 := k1.symm.trans k2
    show pullback.fst (splitTorus (Sp V) F).hom (thick V (maximalIdeal V) e) ≫ _ =
      pullback.fst (splitTorus (Sp V) F).hom (thick V (maximalIdeal V) e) ≫ _
    rw [← GlobalTheory.SplitTorus.bcIso_inv_bcMap, Category.assoc, Category.assoc, k3]
  haveI : Mono (GlobalTheory.TorusPart.PELUnif.torus P' hβ n') :=
    (GlobalTheory.T.uniformisationTorus_mono_and_factor E H W (maximalIdeal W) t' P' Ω β 0 (GlobalTheory.TorusPart.map_pow_one_eq_zero hβ) tΩ.G n'.φ n'.cart).1
  have e2 := congrArg (GlobalTheory.TorusPart.pullTorus n.cart) key
  rw [GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hΩ] at e2
  have e3 : GlobalTheory.SplitTorus.torusMap (Sp Ω) l = GlobalTheory.SplitTorus.torusMap (Sp Ω) 0 := (cancel_mono _).1 e2
  exact hl0 (GlobalTheory.SplitTorus.torusMap_injective e3)

end GlobalTheory.TorusOnto
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCharacterRestrictionTraitSurjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusCharacterRestriction_trait_surjective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t')
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    Function.Surjective ρ := by
  first | exact @GlobalTheory.TorusOnto.restrict_surjective | exact GlobalTheory.TorusOnto.restrict_surjective | (intros; apply GlobalTheory.TorusOnto.restrict_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastAllTranspose
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 2000000

namespace GlobalTheory.Mem.Col2.LowerTie

section Gen
open Formalism.L2.Forms
variable {ι : Type} [Fintype ι] {N n : ℕ}

theorem lastAll_transpose (a : ι → ℂˣ) (τ : ι) :
    (((lastAll N a τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))ᵀ = ((lastAll N a τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
  ext i j
  simp only [Matrix.transpose_apply, lastAll, lastGL_apply]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem fnOf_lastAll (G : ι → Matrix (Fin N) (Fin N) ℂ) (lam : ι → DomWeight N) (a : ι → ℂˣ) (P : Pol ℂ ι N) :
    fnOf G (shiftOf lam) (fun τ => ((lastAll N a τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) P =
      fnOf G (shiftOf lam) 1 (actP lam (lastAll N a) P) := by
  have h := fnOf_mul G (shiftOf lam) (fun τ => ((lastAll N a τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) 1 P
  simp only [Pi.one_apply, mul_one] at h
  rw [h]
  refine congrArg (fnOf G (shiftOf lam) 1) ?_
  have e : trAct (lastAll N a) = Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((lastAll N a τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) := by
    unfold trAct
    simp only [lastAll_transpose]
  simp only [actP, detTwK, detPow, shiftOf, LinearMap.smul_apply, AlgHom.toLinearMap_apply, e]
  refine congrArg (· • _) (Finset.prod_congr rfl fun τ _ => ?_)
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]

theorem scalar_last (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) (h : ∀ i, 0 ≤ Br.bBr hN lam sg i) (a : ℂˣ) :
    (a : ℂ) ^ (-Br.nBr lam sg) * ((a : ℂ) ^ lam.detShift * ∏ s, (a : ℂ) ^ (Br.bBr hN lam sg s).toNat) = 1 := by
  subst hN
  have ha : (a : ℂ) ≠ 0 := a.ne_zero
  have e : ∏ s, (a : ℂ) ^ (Br.bBr rfl lam sg s).toNat = (a : ℂ) ^ (∑ s, Br.bBr rfl lam sg s) := by
    have : ∀ s, (a : ℂ) ^ (Br.bBr rfl lam sg s).toNat = (a : ℂ) ^ (Br.bBr rfl lam sg s) := fun s => by
      rw [← zpow_natCast, Int.toNat_of_nonneg (h s)]
    simp only [this]
    induction (Finset.univ : Finset (Fin n)) using Finset.cons_induction with
    | empty => simp
    | cons x s hx ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ ha, ih]
  have e2 : Br.nBr lam sg = lam.detShift + ∑ s, Br.bBr rfl lam sg s := by
    simp only [Br.nBr, Br.bBr, DomWeight.detShift, Finset.sum_sub_distrib, Fin.sum_univ_castSucc]
    simp [Br.iC]
    change ∑ i : Fin n, lam.w i.castSucc + lam.w (Fin.last n) - ∑ i, sg.w i = lam.w (Fin.last n) + (∑ x : Fin n, lam.w x.castSucc - ∑ i, sg.w i)
    ring
  rw [e, ← zpow_add₀ ha, ← zpow_add₀ ha, e2]
  simp

theorem branchingProjection_act_last (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)
    (h : ∀ τ i, 0 ≤ Br.bBr hN (lam τ) (sg τ) i) (a : ι → ℂˣ) (P : Pol ℂ ι N) :
    (∏ τ, (a τ : ℂ) ^ (-Br.nBr (lam τ) (sg τ))) • (Br.brStdP hN lam sg (actP lam (lastAll N a) P) : Pol ℂ ι n) =
      (Br.brStdP hN lam sg P : Pol ℂ ι n) := by
  rw [branchingProjection_last, smul_smul]
  have e : (∏ τ, (a τ : ℂ) ^ (-Br.nBr (lam τ) (sg τ))) * (detTwK lam (lastAll N a) * ∏ τ, ∏ s, (a τ : ℂ) ^ Br.bExp hN lam sg τ s) = 1 := by
    have h2 : detTwK lam (lastAll N a) = ∏ τ, (a τ : ℂ) ^ (lam τ).detShift := by
      simp only [detTwK, detPow, lastAll, det_lastGL' hN, Units.val_zpow_eq_zpow_val]
    rw [h2, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    exact scalar_last hN (lam τ) (sg τ) (h τ) (a τ)
  rw [e, one_smul]
end Gen
end GlobalTheory.Mem.Col2.LowerTie

namespace GlobalTheory.Mem.Col2.LowerTie

section Rec
variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)

theorem embT_eq : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
  funext τ
  ext y
  show B.host.φ₀ _ = _
  rw [← B.embE_φ₀]
  rfl

include l in
theorem pi_mul_star : ((X.piT u : 𝓞 B.host.E) : B.host.E) * star ((X.piT u : 𝓞 B.host.E) : B.host.E) = (B.T u : B.host.E) := by
  have h := congrArg (fun z : 𝓞 B.fields.E => (z : B.fields.E)) (l.pr.piT_norm u)
  simp only [map_mul, map_natCast] at h
  exact h

include l in
theorem star_pi_ne : star ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := (l.per u I.mu0).tz_ne

theorem bZ_std (hO : I.Ok) (hP : TC.Pins B X) (z0 : Fin (B.R.N B.R.m) → B.host.E)
    (hz : ∀ j, z0 j = if j.1 + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0) :
    bZ (D := I.rec7 l Z) u z0 =
      Matrix.diagonal fun i : Fin (B.R.N B.R.m) => if i.1 + 1 = B.R.N B.R.m then (star ((X.piT u : 𝓞 B.host.E) : B.host.E))⁻¹ else 1 := by
  have hc := (spaces_in_coordinates I hO hP l Z).2.2.1
  have hπ := pi_mul_star I l u
  have h0 := star_pi_ne I l u
  have hp0 : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := fun h => h0 (by rw [h, star_zero])
  refine Matrix.ext fun (a b : Fin (B.R.N B.R.m)) => ?_
  have ha := a.2
  have hb := b.2
  rw [Matrix.diagonal_apply]
  by_cases h : b.1 < B.R.N B.R.m - 1
  · have e : bZ (D := I.rec7 l Z) u z0 a b = iXc (I.rec7 l Z) (Pi.single ⟨b.1, h⟩ 1) a := by
      exact (dif_pos h).trans (LinearMap.toMatrix'_apply _ _ _)
    refine (e.trans (hc _ a)).trans ?_
    by_cases hab : a = b
    · subst hab
      rw [dif_pos h, if_pos rfl, if_neg (by omega)]
      exact Pi.single_eq_same (M := fun _ : Fin (B.R.N B.R.m - 1) => B.host.E) _ _
    · rw [if_neg hab]
      split_ifs with h2
      · exact Pi.single_eq_of_ne (M := fun _ : Fin (B.R.N B.R.m - 1) => B.host.E) (fun h3 => hab (Fin.ext (Fin.mk.inj_iff.1 h3))) _
      · rfl
  · have e : bZ (D := I.rec7 l Z) u z0 a b = z0 a / (B.T u : B.host.E) := by
      exact dif_neg h
    rw [e, hz, ← hπ]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos (by omega), if_pos (by omega)]
      field_simp
    · rw [if_neg hab, if_neg (fun h3 => hab (Fin.ext (by omega))), zero_div]

def aT (τ : Tau B.R) : ℂˣ :=
  Units.mk0 (embAt B.embLL B.fields.emb τ (star ((X.piT u : 𝓞 B.host.E) : B.host.E))) ((map_ne_zero _).2 (star_pi_ne I l u))

theorem mZ_std (hO : I.Ok) (hP : TC.Pins B X) (z0 : Fin (B.R.N B.R.m) → B.host.E)
    (hz : ∀ j, z0 j = if j.1 + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0) :
    mZ (D := I.rec7 l Z) u z0 =
      fun τ => ((lastAll (B.R.N B.R.m) (aT I l u) τ : GL (Fin (B.R.N B.R.m)) ℂ) : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) ℂ) := by
  have h0 := star_pi_ne I l u
  have e : (bZ (D := I.rec7 l Z) u z0)⁻¹ =
      Matrix.diagonal fun i : Fin (B.R.N B.R.m) => if i.1 + 1 = B.R.N B.R.m then star ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1 := by
    rw [bZ_std I l Z u hO hP z0 hz]
    refine Matrix.inv_eq_left_inv (A := Matrix.diagonal fun i : Fin (B.R.N B.R.m) =>
      if i.1 + 1 = B.R.N B.R.m then (star ((X.piT u : 𝓞 B.host.E) : B.host.E))⁻¹ else 1) ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    split_ifs
    · exact mul_inv_cancel₀ h0
    · exact mul_one 1
  funext τ
  refine Matrix.ext fun (a b : Fin (B.R.N B.R.m)) => ?_
  have e2 : mZ (D := I.rec7 l Z) u z0 τ a b = embAt B.embLL B.fields.emb τ ((Matrix.diagonal fun i : Fin (B.R.N B.R.m) =>
      if i.1 + 1 = B.R.N B.R.m then star ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) a b) := by
    unfold mZ
    rw [e, embT_eq]
    rfl
  rw [e2]
  simp only [lastAll, lastGL_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [aT]

end Rec
end GlobalTheory.Mem.Col2.LowerTie

namespace GlobalTheory.Mem.Col2.LowerTie

theorem lowerMap_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∀ (u : B.Word) (Ch : ℕ → Type) (chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i) (F : FormsTiedSym (I.rec7 l Z) u Ch chOf),
    I.StdF l Z u F → ∀ (ψ : ((I.rec7 l Z).mem u).P.Wz) (c : ((I.rec7 l Z).fm u).clsP)
      (P : MvPolynomial ((I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m) × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m)) ℂ),
      (∀ s, F.eWz ψ c s = fnOf _ (shiftOf (Formalism.L2.Forms.lamT u (I.rec7 l Z).R.m)) (mZ u F.til.z0) P
        ((F.val (I.rec7 l Z).R.m le_rfl (Or.inr rfl)).eY s)) →
      F.valP.eW (((I.rec7 l Z).mem u).P.lowerMap ψ) c =
        fnOf _ (shiftOf (Formalism.L2.Forms.sgT u)) 1 (Formalism.L2.Ker.brTen (I.rec7 l Z) u P) := by
  intro B X I hO hP l Z u Ch chOf F hS ψ c P hψ
  have hl : Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u = B.wts.lamTrue u B.R.m := funext (trueWeight_lastStep_trueColumns I l Z u)
  have hs : Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u = B.wts.sgTrue := funext (trueRowWeight_trueColumns I l Z u)
  have hl' : Formalism.L2.Forms.lamT (D := I.rec7 l Z) u (I.rec7 l Z).R.m = B.wts.lamTrue u B.R.m := hl
  have hs' : Formalism.L2.Forms.sgT (D := I.rec7 l Z) u = B.wts.sgTrue := hs
  have hI : ∀ τ i, 0 ≤ Br.bBr (N_m_succ B.R) (B.wts.lamTrue u B.R.m τ) (B.wts.sgTrue τ) i := by
    intro τ i
    have h := (Formalism.MainNotions.product_first_zeroth_parts.interlaceTr (I.rec7 l Z) u (sg_interlace F.valP) τ i).1
    rw [hl, hs] at h
    exact sub_nonneg.2 h
  have h1 : ψ c = fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) 1
      (actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P) := by
    refine Eq.trans ?_ (fnOf_lastAll (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (B.wts.lamTrue u B.R.m) (aT I l u) P)
    funext s
    have h := hψ s
    rw [hS.eWz, hl', mZ_std I l Z u hO hP _ hS.z0] at h
    refine h.trans ?_
    have h2 := hS.eY B.R.m le_rfl (Or.inr rfl) s
    exact congrArg (fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) _ P) (Subtype.ext h2)
  have h3 : polOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) (Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m)) (ψ c) =
      actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P := by
    have e : (fun τ => ((Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m)).1 τ)⁻¹) = 1 := funext fun τ => inv_one
    have h := polOf_fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) (Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m))
      (actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P)
    rw [e] at h
    rw [h1]
    exact h
  have h4 : Formalism.L2.Ker.brTen (I.rec7 l Z) u P = (Br.brStdP (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue P : Pol ℂ (Tau B.R) (B.R.N B.R.m - 1)) := by
    have h := blk_brOne (ι := Tau B.R) (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue P
    refine Eq.trans ?_ h
    unfold Formalism.L2.Ker.brTen
    rw [hl, hs]
    rfl
  have h5 := branchingProjection_act_last (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue hI (aT I l u) P
  funext s
  rw [hS.eW _ c s ⟨s.1, s.2⟩ rfl, hs', h4, ← h5, ← h3]
  rfl

end GlobalTheory.Mem.Col2.LowerTie

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalCharacterAdmissibleConductorInertiaSurj
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalCharacterAdmissibleConductorInertiaSurj
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem universalCharacter_admissibleConductor_inertia_surjective : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (b0 b1 : Big D)
    (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (hE : IsEmpty D.nd.Loc) (F : TwF T)
    (i : T.Tw) (Q : Finset (PlE D.host)) (M : ℕ), Formalism.MainNotions.NAdm.AdmQ (T.ntw hE F (TwL.empty T)) i Q M →
    ∀ P (hP : P ∈ Q),
      (∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P →
        Function.Surjective fun σ : Ine (F := D.host.E) A =>
          Multiplicative.toAdd (GlobalTheory.GalChar.delU D.host T.cc (T.l i) Q M σ) ⟨P, hP⟩) ∧
      ∀ P' ∈ Q, P' ≠ P → ¬ IsConjPl D.host P P' → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P' →
        ∀ σ ∈ Ine (F := D.host.E) A, Multiplicative.toAdd (GlobalTheory.GalChar.delU D.host T.cc (T.l i) Q M σ) ⟨P, hP⟩ = 0 := by
  intro _ D cf b0 b1 Sx T Sp hE F i Q M hQ P hP
  obtain ⟨-, hadm⟩ := hQ
  have hcl : ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q := fun P hP P' h => by
    obtain ⟨⟨P'', hP'', h''⟩, -⟩ := hadm P hP
    rw [GlobalTheory.GalChar.isConjPl_unique h h'']
    exact hP''
  obtain ⟨-, χ, h1, h2, h3, h4, h5⟩ := hadm P hP
  have hsP : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P →
      ∀ b, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := fun A hA b => by
    obtain ⟨σ, hσ⟩ := h5 A hA (Multiplicative.toAdd b)
    exact ⟨σ.1, σ.2, Multiplicative.toAdd.injective hσ⟩
  have hDel : GlobalTheory.GalChar.IsDel D.host T.cc (T.l i) M (GlobalTheory.GalChar.pair D.host P) χ := by
    refine ⟨h1, h2, h3, fun w hw => h4 w (fun e => hw (Or.inl e)) (fun e => hw (Or.inr e)), fun w hw A hA b => ?_⟩
    rcases hw with rfl | hw
    · exact hsP A hA b
    · exact GlobalTheory.SpreadRestrict.surj_conj (X := T.ntw hE F (TwL.empty T)) χ h2 hw hsP A hA b
  have hD := GlobalTheory.GalChar.isDel_delOf D.host T.cc (T.l i) ⟨χ, hDel⟩
  have hcoord := (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host T.cc (T.l i)).2.2.2.2.2.2.1 Q M hcl P hP
  refine ⟨fun A hA c => ?_, fun P' _ hne hnc A hA σ hσ => ?_⟩
  · obtain ⟨σ, hσ, e⟩ := hD.2.2.2.2 P (Or.inl rfl) A hA (Multiplicative.ofAdd c)
    refine ⟨⟨σ, hσ⟩, ?_⟩
    show Multiplicative.toAdd (GlobalTheory.GalChar.delU D.host T.cc (T.l i) Q M σ) ⟨P, hP⟩ = c
    rw [hcoord, e, toAdd_ofAdd]
  · rw [hcoord, hD.2.2.2.1 P' (fun h => h.elim (fun e => hne e) (fun e => hnc e)) A hA σ hσ]
    rfl

end GlobalTheory.HeightCounting.FormsStep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalCharacterAdmissibleConductorInertiaSurjStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_surjective_of_admQ : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (b0 b1 : Big D)
    (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (hE : IsEmpty D.nd.Loc) (F : TwF T)
    (i : T.Tw) (Q : Finset (PlE D.host)) (M : ℕ), Formalism.MainNotions.NAdm.AdmQ (T.ntw hE F (TwL.empty T)) i Q M →
    ∀ P (hP : P ∈ Q),
      (∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P →
        Function.Surjective fun σ : Ine (F := D.host.E) A =>
          Multiplicative.toAdd (GlobalTheory.GalChar.delU D.host T.cc (T.l i) Q M σ) ⟨P, hP⟩) ∧
      ∀ P' ∈ Q, P' ≠ P → ¬ IsConjPl D.host P P' → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P' →
        ∀ σ ∈ Ine (F := D.host.E) A, Multiplicative.toAdd (GlobalTheory.GalChar.delU D.host T.cc (T.l i) Q M σ) ⟨P, hP⟩ = 0 := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.universalCharacter_admissibleConductor_inertia_surjective | exact GlobalTheory.HeightCounting.FormsStep.universalCharacter_admissibleConductor_inertia_surjective | (intros; apply GlobalTheory.HeightCounting.FormsStep.universalCharacter_admissibleConductor_inertia_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBasePointChartMulTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBasePointChartMulTwist
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw

theorem carries_mul_self {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    {g h : GL (Fin N) (TensorProduct F E (Formalism.L2.Herm.Af F))} {L : Submodule (𝓞 E) (Fin N → E)}
    (hg : Formalism.L2.Herm.Carries g L L) (hh : Formalism.L2.Herm.Carries h L L) : Formalism.L2.Herm.Carries (g * h) L L := by
  intro x
  rw [hg x, hh, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]


set_option maxHeartbeats 1000000 in
theorem admissibleBasePoint_chart_mul_twist : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (Lb0 : Ch0 → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U0 : Ch0 → Subgroup (GA B (B.R.N i))) (chi0 : ∀ β, U0 β →* ℂˣ) (y0 : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)) (st0 : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k0 : Ch0 → GA B (B.R.N i)), I.Reads u I.mu0 i chOf0 Lb0 U0 chi0 y0 st0 k0 → ∀ (g : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → Ch0) (t : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i)), (∀ β, ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf (t β) p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i)) → (∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) → bc (prV (E := B.host.E) v) (t β) = 1) → (a = I.mu0 → ∀ β, t β = 1) → GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i (fun β => k0 (g β) * t β) := by
  intro B X I hI u a i Ch0 chOf0 Lb0 U0 chi0 y0 st0 k0 hR g t hstd hoff h0
  refine ⟨fun β => ?_, fun β v hT hQ hd => ?_, fun β P r j hr => ?_⟩
  · obtain ⟨p, hp, hN⟩ := hR.k_std (g β)
    obtain ⟨q, hq, hN'⟩ := hstd β
    have h1 := hp.lat
    have h2 := hq.lat
    rw [hN] at h1
    rw [hN'] at h2
    refine ⟨p, ⟨mul_mem hp.uni hq.uni, ?_, fun P => ?_, fun w => ?_, fun P => ?_⟩, hN⟩
    · rw [hN]
      exact carries_mul_self h1 h2
    · exact absurd P.2 (Finset.notMem_empty _)
    · exact absurd w.2 (Finset.notMem_empty _)
    · exact absurd P.2 (Finset.notMem_empty _)
  · have hq0 : I.Q I.mu0 = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty _
    have hk : bc (prV (E := B.host.E) v) (k0 (g β)) = 1 :=
      hR.k_off (g β) v hT (by rintro ⟨P, hP, -⟩; rw [hq0] at hP; simp at hP) (Or.inl rfl)
    have ht : bc (prV (E := B.host.E) v) (t β) = 1 := by
      rcases hd with rfl | hd
      · rw [h0 rfl β, map_one]
      · exact hoff β v (Or.inr hd)
    have hm := map_mul (bc (prV (E := B.host.E) v)) (k0 (g β)) (t β)
    rw [hk, ht, one_mul] at hm
    exact hm
  · have hv : (B.T u : 𝓞 B.host.F) ∈ (P.1.under (𝓞 B.host.F)).asIdeal := by
      have := T_mem_vT (GlobalTheory.BasePrimes.primes_ok B X).1 u P
      rw [HeightOneSpectrum.under, Ideal.mem_comap, map_natCast]
      exact this
    have ht := hoff β _ (Or.inl hv)
    have ht' := (map_inv (bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F)))) (t β)).trans (by rw [ht, inv_one])
    have hent : ∀ r l, adAt B.host.F P.1 (((t β)⁻¹ : GA B (B.R.N i)).1 r l) = if r = l then 1 else 0 := by
      intro r l
      have e := congrArg (fun g => g.1 r l) ht'
      simp only [bc, Units.coe_map, Units.val_one, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at e
      split_ifs with h
      · subst h
        exact FullDt.adAt_eq_one_of_prV P.1 (by simpa using e)
      · exact TilX.adAt_eq_zero_of_prV P.1 _ (by simpa [Matrix.one_apply_ne h] using e)
    have key : adAt B.host.F P.1 (((k0 (g β) * t β)⁻¹ : GA B (B.R.N i)).1 r j) =
        adAt B.host.F P.1 (((k0 (g β))⁻¹ : GA B (B.R.N i)).1 r j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply, map_sum]
      simp only [map_mul, hent, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [key]
    exact hR.k_T (g β) P r j hr

end GlobalTheory.Mem.Col2.TC.ChTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBasePointChartMulTwistStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleBasePoint_chart_mul_twist_alt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (Lb0 : Ch0 → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U0 : Ch0 → Subgroup (GA B (B.R.N i))) (chi0 : ∀ β, U0 β →* ℂˣ) (y0 : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)) (st0 : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k0 : Ch0 → GA B (B.R.N i)), I.Reads u I.mu0 i chOf0 Lb0 U0 chi0 y0 st0 k0 → ∀ (g : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → Ch0) (t : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i)), (∀ β, ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf (t β) p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i)) → (∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) → bc (prV (E := B.host.E) v) (t β) = 1) → (a = I.mu0 → ∀ β, t β = 1) → GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i (fun β => k0 (g β) * t β) := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.admissibleBasePoint_chart_mul_twist | exact GlobalTheory.Mem.Col2.TC.ChTw.admissibleBasePoint_chart_mul_twist | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.admissibleBasePoint_chart_mul_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColsReTo0S
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df GlobalTheory.Mem.Db NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Db.DivTr

open Formalism.L2.Forms GlobalTheory.Mem.Top.ColOwe

section Gen

variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)


set_option maxHeartbeats 4000000 in
def atTTS {u : D.what₂.Word} (A : AtTTied (D := D) u) : AtTTied (D := setDiv D N h) u := { A with }


set_option maxHeartbeats 4000000 in
def forms0S {u : D.what₂.Word} (F : Forms0 D u) : Forms0 (setDiv D N h) u :=
  { F with
    atT := atTTS N h F.atT
    cls0 := { F.cls0 with }
    val0 := { F.val0 with }
    lv0 := { F.lv0 with } }


set_option maxHeartbeats 4000000 in
def herm0S (H : Formalism.L2.Herm.Herm0 D) : Formalism.L2.Herm.Herm0 (setDiv D N h) := { H with }


set_option maxHeartbeats 4000000 in
def fullS (X : Formalism.L2.Herm.FullTiedS D) : Formalism.L2.Herm.FullTiedS (setDiv D N h) :=
  { X with
    base := { X.base with }
    atT := fun u => { X.atT u with }
    ad := { X.ad with } }

set_option maxHeartbeats 4000000 in
theorem fullS_to0 (X : Formalism.L2.Herm.FullTiedS D) : (fullS N h X).to0 = herm0S N h X.to0 := rfl


set_option maxHeartbeats 4000000 in
def gS {Gt : GatTies D} {c : LatCmp D} (g : Formalism.L2.G.GroupCompatibilityAll D Gt c) :
    Formalism.L2.G.GroupCompatibilityAll (setDiv D N h) (gatTr N h Gt) (cmpTr N h c) where
  herm := herm0S N h g.herm
  forms := fun u => forms0S N h (g.forms u)
  cmp := { g.cmp with }
  ring := g.ring
  gat := g.gat

end Gen

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}
variable (w : ColW B f T) (Z : w.Lt) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)

-- Build the transported records at the same index used by the column data.
set_option maxHeartbeats 4000000 in
def fullSZ (X : Formalism.L2.Herm.FullTiedS (w.D Z)) :
    Formalism.L2.Herm.FullTiedS (w.D (setDivZ Z N h)) :=
  { X with
    base := { X.base with }
    atT := fun u => { X.atT u with }
    ad := { X.ad with } }

set_option maxHeartbeats 4000000 in
def forms0SZ {u : B.Word} (F : Forms0 (w.D Z) u) :
    Forms0 (w.D (setDivZ Z N h)) u :=
  { F with
    atT := atTTRe (setDivZ Z N h) F.atT
    cls0 := clsRe (setDivZ Z N h) F.cls0
    val0 := valRe (setDivZ Z N h) F.val0
    lv0 := lvRe (setDivZ Z N h) F.lv0 }

set_option maxHeartbeats 4000000 in
theorem fullS_cols (X : Formalism.L2.Herm.FullTiedS (w.D Z)) :
    (fullSZ w Z N h X).cols = hermRe (setDivZ Z N h) X.cols := rfl

set_option maxHeartbeats 4000000 in
theorem colsRe_to0S (C : ColsTiedSym (w.D Z)) (u : B.Word) :
    ((colsRe (setDivZ Z N h) C).forms u).to0 = forms0SZ w Z N h (C.forms u).to0 := rfl


set_option maxHeartbeats 8000000 in
theorem stdC_tr (C : ColsTiedSym (w.D Z)) (hC : TC.StdC w.I w.l Z C) :
    TC.StdC w.I w.l (setDivZ Z N h) (colsRe (setDivZ Z N h) C) := fun u =>
  { hC u with gl := { (hC u).gl with } }


set_option maxHeartbeats 8000000 in
def colTTr (t : ColT w Z) : ColT w (setDivZ Z N h) where
  C := colsRe (setDivZ Z N h) t.C
  std := stdC_tr w Z N h t.C t.std
  stdLv := fun u => t.stdLv u
  full := ⟨fullSZ w Z N h t.full.1,
    (fullS_cols w Z N h t.full.1).trans (congrArg (hermRe (setDivZ Z N h)) t.full.2)⟩
  stdDt := t.stdDt
  Gt := { t.Gt with }
  cmp := { t.cmp with }
  g :=
    { herm := { t.g.herm with }
      forms := fun u => forms0SZ w Z N h (t.g.forms u)
      cmp := { t.g.cmp with }
      ring := t.g.ring
      gat := t.g.gat }
  herm_eq := congrArg
    (fun H : Formalism.L2.Herm.Herm0 (w.D Z) =>
      ({ H with } : Formalism.L2.Herm.Herm0 (w.D (setDivZ Z N h)))) t.herm_eq
  forms_eq := funext fun u =>
    (congrArg (forms0SZ w Z N h) (congrFun t.forms_eq u)).trans (colsRe_to0S w Z N h t.C u).symm
  gpl := t.gpl

end GlobalTheory.Mem.Db.DivTr

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDetLiftLocal
section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.FinAfLocalIdele
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiGTrue
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.TypePrimes.psiG_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), ColIn.Ok I → TC.Pins B X → ∀ (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)) (G : GLoc (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E (sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g), TC.IdG I l Z G → ∀ ψ, Formalism.L2.Theta.IsStdChar (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ψ (-1) → ∀ (k : Fin 2) (v : HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) (h : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g k : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ v.asIdeal) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F), Formalism.L2.Theta.IsPlaceIdem (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) v ε → ∀ c y : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F, Valued.v (algebraMap (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (c : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) - G.phi k v h (inclE (F := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.xi0)) < 1 → ∀ z : v.adicCompletionIntegers (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F, (z : v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) = algebraMap (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (y : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) → G.psi0 k v h (IsLocalRing.residue _ z) = ψ (ε * algebraMap (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ((c : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) * (y : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) / ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g k : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F))) :=
  by
    intro B X I hI _ l Z G hG ψ hψ k v h ε hε c y hc z hz
    have hs := (TC.rec7 I l Z).nd.g_split k
    have hgp := l.pr.g_prime k
    obtain ⟨hN, hsq⟩ := GlobalTheory.Mem.TypePrimes.Red.absNorm_and_unram hgp hs v h
    obtain ⟨t, ht⟩ := GlobalTheory.Mem.TypePrimes.Red.exists_hostXi0_inverse_integer B.host
    obtain ⟨b, hb, e⟩ := GlobalTheory.Mem.TypePrimes.Red.columnCharacter_reduction_eq_exp
      (X := B.fields) (Pr := B.primes X) I.Ch l.pr B.sp.cm B.embLL B.host.xi0 hI.weil t ht G hG.piG
      (fun _ => rfl) hG.psi k v h hN c y hc z hz
    refine e.trans ?_
    exact (GlobalTheory.T.standardAddChar_placeIdempotent_div_prime (TC.rec7 I l Z) ψ hψ _
      hgp v hN hsq ε hε (c * y) (b : ℤ) (by rw [Int.cast_natCast]; exact hb)).symm
end

noncomputable section

namespace GlobalTheory.Core.Cls.JointsStd

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.L2.Host.CT Neutral.B1

section Refl

variable {E : Type} [Field E] [NumberField E]

end Refl

section Std

open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2 _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem exists_vG_over {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (k : Fin 2) (v : HeightOneSpectrum (𝓞 X.F))
    (h : ((Pr.g k : ℕ) : 𝓞 X.F) ∈ v.asIdeal) : ∃ w ∈ Pr.vG k, w.under (𝓞 X.F) = v := by
  have := v.isPrime
  obtain ⟨⟨w, hwp, hwl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 X.E)) := inferInstance
  have hw : ∀ a : 𝓞 X.F, algebraMap (𝓞 X.F) (𝓞 X.E) a ∈ w ↔ a ∈ v.asIdeal := fun a => by
    rw [hwl.over]; rfl
  have hg0 : ((Pr.g k : ℕ) : 𝓞 X.E) ≠ 0 := Nat.cast_ne_zero.2 (hPr.g_prime k).ne_zero
  have hg : ((Pr.g k : ℕ) : 𝓞 X.E) ∈ w := by simpa using (hw _).2 h
  have h0 : X.conjO (Pr.piG k) ≠ 0 := right_ne_zero_of_mul (a := Pr.piG k) (by rw [hPr.piG_norm k]; exact hg0)
  have hcc : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  have hF : ∀ a : 𝓞 X.F, X.conjO (algebraMap (𝓞 X.F) (𝓞 X.E) a) = algebraMap (𝓞 X.F) (𝓞 X.E) a := fun a =>
    RingOfIntegers.ext (hX.star_F (a : X.F))
  have hg' := hg
  rw [← hPr.piG_norm k] at hg'
  rcases hwp.mem_or_mem hg' with h1 | h1
  · refine ⟨⟨w.comap X.conjO, Ideal.comap_isPrime _ _, fun e => h0 ?_⟩, (mem_divs h0 _).2 ?_, HeightOneSpectrum.ext (Ideal.ext fun a => ?_)⟩
    · exact Ideal.mem_bot.1 (e ▸ (show X.conjO (X.conjO (Pr.piG k)) ∈ w by rw [hcc]; exact h1))
    · show X.conjO (X.conjO (Pr.piG k)) ∈ w
      rw [hcc]; exact h1
    · show X.conjO (algebraMap (𝓞 X.F) (𝓞 X.E) a) ∈ w ↔ _
      rw [hF, hw]
  · exact ⟨⟨w, hwp, fun e => hg0 (Ideal.mem_bot.1 (e ▸ hg))⟩, (mem_divs h0 _).2 h1, HeightOneSpectrum.ext (Ideal.ext hw)⟩

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
include hOk

theorem piBar_std (k : Fin 2) : ∃ y : 𝓞 B.host.K,
    ((y : B.host.K) : B.host.E) = (B.fields.conjO (X.piG k) : B.host.E) ∧ y ∈ (I.C.P.pb k).asIdeal := by
  have hPr := (base_fields_primes_ok B X).2.1
  have hK : (B.fields.conjO (X.piG k) : B.host.E) ∈ B.host.K := by
    have h := HostK.conj_mem B.host (X.piG_K k)
    rw [← B.fields_star] at h
    exact h
  have hi : IsIntegral ℤ (⟨_, hK⟩ : B.host.K) :=
    (isIntegral_algebraMap_iff ).1 (B.fields.conjO (X.piG k)).2
  refine ⟨⟨_, hi⟩, rfl, ?_⟩
  have := (I.C.P.pb k).isPrime
  obtain ⟨⟨w, hwp, hwl⟩⟩ : Nonempty ((I.C.P.pb k).asIdeal.primesOver (𝓞 B.host.E)) := inferInstance
  have hg0 : ((B.host.g k : ℕ) : 𝓞 B.host.E) ≠ 0 := Nat.cast_ne_zero.2 (hPr.g_prime k).ne_zero
  have hg : ((B.host.g k : ℕ) : 𝓞 B.host.E) ∈ w := by
    have h1 := I.C.P.pb_over k
    rw [hwl.over] at h1
    simpa using (Ideal.mem_comap.1 h1)
  have h0 : B.fields.conjO (X.piG k) ≠ 0 := right_ne_zero_of_mul (a := X.piG k) (by rw [hPr.piG_norm k]; exact hg0)
  have h2 := (hOk.pibar k ⟨w, hwp, fun e => hg0 (Ideal.mem_bot.1 (e ▸ hg))⟩).2 (HeightOneSpectrum.ext hwl.over.symm)
  rw [hwl.over]
  exact (mem_divs h0 _).1 h2

theorem om_std (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g) (hG : I.IdG l Z G)
    (k : Fin 2) (v : HeightOneSpectrum (𝓞 B.host.F)) (h : (B.host.g k : 𝓞 B.host.F) ∈ v.asIdeal) (a n : ℕ)
    (hn : n.Coprime (B.host.g k)) (ha : a < B.R.m) :
    G.chiB k v h a (n : kv B.host.F v) = ((I.C.W.om k (ZMod.unitOfCoprime n hn) ^ (2 * (a + 1)) : ℂˣ) : ℂ) := by
  classical
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨w, hw, hv⟩ := exists_vG_over hX hPr k v h
  have hws : w ∈ (B.primes X).vGs := by
    unfold Primes.vGs
    rw [Finset.mem_union]
    fin_cases k
    exacts [Or.inl hw, Or.inr hw]
  have hg : ((B.host.g k : ℕ) : 𝓞 B.host.E) ∈ w.asIdeal := by
    rw [← hv] at h
    simpa using (Ideal.mem_comap.1 h)
  have hu : IsUnit ((n : ℕ) : 𝓞 B.fields.E ⧸ w.asIdeal) := by
    have h1 : IsCoprime ((n : ℕ) : 𝓞 B.fields.E ⧸ w.asIdeal) ((B.host.g k : ℕ) : 𝓞 B.fields.E ⧸ w.asIdeal) := hn.cast
    have h2 : ((B.host.g k : ℕ) : 𝓞 B.fields.E ⧸ w.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk w.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hg
    rwa [h2, isCoprime_zero_right] at h1
  have hn0 : ((n : ℕ) : B.host.E) ≠ 0 := by
    rintro e
    obtain rfl : n = 0 := Nat.cast_eq_zero.1 e
    have := w.isPrime
    simp at hu
  have e1 := hG.chi k v h ⟨w, hws⟩ hv ⟨a, ha⟩ n hu.unit rfl
  have e2 := (hOk.ch_tied.mu0 ⟨a, ha⟩).atg ⟨w, hws⟩ (Units.mk0 _ hn0) (n : 𝓞 B.fields.E) hu.unit (by simp) (by simp)
  have e3 := (I.C.isMu0 ⟨a, ha⟩).atg k w ((hOk.pibar k w).1 hw) n hn (Units.mk0 _ hn0) rfl
  rw [e3, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, inv_inj] at e2
  exact e1.trans e2.symm

variable (hP : TC.Pins B X) {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L}
  {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX}
include hP

end Std

section Local

open Formalism.L2.DIV GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem idem_comp {e : AfE F E} {P : HeightOneSpectrum (𝓞 E)} (he : e * e = e)
    (h : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ e * (((x : E)⁻¹) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) ∉ RInt F E)) :
    afIso F E e P = 1 ∧ ∀ Q, Q ≠ P → afIso F E e Q = 0 := by
  have h01 : ∀ Q, afIso F E e Q = 0 ∨ afIso F E e Q = 1 := fun Q => by
    have h1 : afIso F E e Q * afIso F E e Q = afIso F E e Q := congrArg (fun z => z Q) ((map_mul (afIso F E) e e).symm.trans (congrArg _ he))
    exact IsIdempotentElem.iff_eq_zero_or_one.1 h1
  have hv : ∀ (x : 𝓞 E) Q, afIso F E (e * (((x : E)⁻¹) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))) Q =
      afIso F E e Q * algebraMap E (Q.adicCompletion E) (x : E)⁻¹ := fun x Q => by
    rw [map_mul, afIso_tmul_one]; rfl
  have h0 : ∀ Q, Q ≠ P → afIso F E e Q = 0 := fun Q hQ => by
    refine (h01 Q).resolve_right fun h1 => ?_
    obtain ⟨x, hx, hxP⟩ : ∃ x ∈ Q.asIdeal, x ∉ P.asIdeal := by
      by_contra hc
      push Not at hc
      exact hQ (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top hc))
    have hx0 : x ≠ 0 := fun e0 => hxP (e0 ▸ zero_mem _)
    have h2 := (mem_rInt_iff F E _).1 (not_not.1 ((h x hx0).not.1 hxP)) Q
    rw [hv, h1, one_mul, valued_algebraMap, map_inv₀] at h2
    have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) Q x).2 hx
    have h4 : 0 < Q.valuation E (algebraMap (𝓞 E) E x) :=
      zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx0))
    exact absurd ((inv_le_one₀ h4).1 h2) (not_le.2 h3)
  refine ⟨(h01 P).resolve_left fun h1 => ?_, h0⟩
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  refine (h x hx0).1 hx ((mem_rInt_iff F E _).2 fun Q => ?_)
  rw [hv]
  by_cases hQ : Q = P
  · subst hQ; rw [h1]; simp
  · rw [h0 Q hQ]; simp

theorem finAf_localIdele {e : AfE F E} {P : HeightOneSpectrum (𝓞 E)} (he : e * e = e)
    (h : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ e * (((x : E)⁻¹) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) ∉ RInt F E)) (k : Eˣ) :
    (finAf F E (localIdele E P (atFin P k)) : AfE F E) = 1 + e * ((k : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) - 1) := by
  obtain ⟨h1, h0⟩ := idem_comp he h
  refine (afIso F E).injective (FiniteAdeleRing.ext _ fun Q => ?_)
  have e1 : afIso F E (1 + e * ((k : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) - 1)) Q =
      1 + afIso F E e Q * (algebraMap E (Q.adicCompletion E) (k : E) - 1) := by
    rw [map_add (f := _), map_mul, map_sub, map_one, afIso_tmul_one]; rfl
  rw [e1, GlobalTheory.Mem.ReadTwist.afIso_finAf_apply]
  by_cases hQ : Q = P
  · subst hQ
    rw [show GlobalTheory.Mem.LocTriv.ev Q (localIdele E Q (atFin Q k) : AdeleRing (𝓞 E) E) = atFin Q k from
      Neutral.B1.localIdele_snd_self E Q (atFin Q k), h1, one_mul, add_sub_cancel]
    rfl
  · rw [show GlobalTheory.Mem.LocTriv.ev Q (localIdele E P (atFin P k) : AdeleRing (𝓞 E) E) = 1 from
      (Neutral.B1.localIdele_isSupportedAt E P (atFin P k)).2 Q hQ, h0 Q hQ, zero_mul, add_zero]

open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Local

end GlobalTheory.Core.Cls.JointsStd

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.JointsTrue

open _root_.Formalism.L2 _root_.Formalism.L2.Host ReciprocityTheory.Neutral.Bridge.HCFR


set_option maxHeartbeats 1000000 in
theorem isDetLift_local (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Theta.AE D) (he : JoinChr.IsPlIdem D e P)
    (k : D.host.Eˣ) (y : Theta.AE D) (hy : Joints.IsRatioAt D e (k : D.host.E) y) (x : Herm.unitaryOneFiniteAdeles D.sp.cm)
    (hx : ((Matrix.GeneralLinearGroup.det (x : GL (Fin 1) (D.host.E ⊗[D.host.F] Herm.Af D.host.F)) :
        (D.host.E ⊗[D.host.F] Herm.Af D.host.F)ˣ) : D.host.E ⊗[D.host.F] Herm.Af D.host.F) = Joints.finE D y) :
    IsDetLift D.sp.cm x.1 (Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k)) := by
  let φ : Theta.AE D →+* AfE D.host.F D.host.E := Joints.finE D
  have hinc : ∀ a : D.host.E, φ (Theta.incA D a) = a ⊗ₜ[D.host.F] 1 := fun a => rfl
  have hc : ∀ z, φ (Theta.cA D z) = Formalism.UG.sigR D.sp.cm.sig _ (φ z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [(Theta.cA D).map_zero, φ.map_zero, RingHom.map_zero]
    | tmul a b => rfl
    | add a b ha hb => rw [(Theta.cA D).map_add, φ.map_add, φ.map_add, ha, hb, RingHom.map_add (f := _)]
  have h1 : (finAf D.host.F D.host.E (Neutral.B1.localIdele _ P (Formalism.L2.Host.atFin P k)) : AfE D.host.F D.host.E) = φ (JoinChr.locE D e k) := by
    rw [GlobalTheory.Core.Cls.JointsStd.finAf_localIdele (e := φ e) (by rw [← φ.map_mul, he.1]) (fun a ha => ?_) k, JoinChr.locE, φ.map_add,
      φ.map_mul, φ.map_sub, φ.map_one, hinc]
    rw [he.2.2 a ha, ← hinc, ← φ.map_mul]
    exact not_congr (GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D _)
  have h2 := congrArg φ hy
  rw [φ.map_mul, hc, ← h1] at h2
  unfold IsDetLift h90
  rw [MonoidHom.div_apply, div_eq_iff_eq_mul]
  exact Units.ext (h2.symm.trans (by rw [Units.val_mul, hx]; rfl))


end GlobalTheory.Mem.JointsTrue

end
end

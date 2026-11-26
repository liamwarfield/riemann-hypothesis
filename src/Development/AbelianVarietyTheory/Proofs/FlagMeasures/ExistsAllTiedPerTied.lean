module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitriangularFrameChangeLocalScalings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.AutomorphicFormsFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActionPreservesPrincipalFlagMultiplic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivariantUnitaryCoefficientMapOnto

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.Per.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Iterated

variable {G N : Type} [MeasurableSpace G] [MeasurableSpace N] {μ : Measure G} {𝓕 : Set G} {ν : Measure N} {𝓝 : Set N}
  {P P' R : G → N → ℂ}

theorem iterated_add (h : (∀ g, IntegrableOn (P g) 𝓝 ν) ∧ IntegrableOn (fun g => ∫ n in 𝓝, P g n ∂ν) 𝓕 μ)
    (h' : (∀ g, IntegrableOn (P' g) 𝓝 ν) ∧ IntegrableOn (fun g => ∫ n in 𝓝, P' g n ∂ν) 𝓕 μ)
    (hR : ∀ g n, R g n = P g n + P' g n) :
    ∫ g in 𝓕, ∫ n in 𝓝, R g n ∂ν ∂μ = ∫ g in 𝓕, ∫ n in 𝓝, P g n ∂ν ∂μ + ∫ g in 𝓕, ∫ n in 𝓝, P' g n ∂ν ∂μ := by
  rw [← integral_add h.2 h'.2]
  congr 1
  funext g
  rw [← integral_add (h.1 g) (h'.1 g)]
  simp only [hR]

end Iterated

variable {D : D7}

theorem flag_topology (B : HSp D) {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} (he : IsIsoSub B e) :
    LocallyCompactSpace (NFlag B e) ∧ SecondCountableTopology (NFlag B e) ∧ BorelSpace (NFlag B e) ∧
      Countable (NFlagQ B e) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨K, hK, h⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B ρ e he).1
  haveI : DiscreteTopology (GQ B ⊓ NFlag B e : Subgroup (GA D B)) :=
    DiscreteTopology.of_subset (s := (GQ B : Set (GA D B))) i6 (fun x hx => hx.1)
  have h1 : IsClosed ((GQ B ⊓ NFlag B e : Subgroup (GA D B)) : Set (GA D B)) := Subgroup.isClosed_of_discrete
  have h2 : IsClosed (NFlag B e : Set (GA D B)) := by
    convert h1.mul_right_of_isCompact (hK.image continuous_subtype_val) using 1
    ext x
    constructor
    · intro hx
      obtain ⟨γ, hγ, k, hk, e⟩ := h ⟨x, hx⟩
      exact ⟨γ, ⟨hγ, γ.2⟩, k, ⟨k, hk, rfl⟩, (congrArg Subtype.val e).symm⟩
    · rintro ⟨γ, hγ, _, ⟨k, -, rfl⟩, rfl⟩
      exact mul_mem hγ.2 k.2
  refine ⟨h2.locallyCompactSpace,
    (inferInstance : SecondCountableTopology (NFlag B e : Set (GA D B))), inferInstance, ?_⟩
  exact Function.Injective.countable (f := fun γ : NFlagQ B e => (⟨γ.1.1, γ.2⟩ : GQ B))
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ B => (x : GA D B)) h))

section Invariant

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E}

structure IsRatInv (ι : A.V →ₗ[D.host.E] B.V) (e : Matrix (Fin B.rank) (Fin ρ) D.host.E)
    (Q : GA D A → GA D B → ℂ) : Prop where
  norm : ∀ δ γ, EmbRel B A ι δ γ → ∀ n ∈ NFlag B e, δ * n * δ⁻¹ ∈ NFlag B e
  left : ∀ g, ∀ n ∈ NFlag B e, ∀ γ ∈ NFlag B e, γ ∈ GQ B → Q g (γ * n) = Q g n
  conj : ∀ g, ∀ n ∈ NFlag B e, ∀ γ ∈ GQ A, ∀ δ, EmbRel B A ι δ γ → Q (γ * g) (δ * n * δ⁻¹) = Q g n

variable {Q : GA D A → GA D B → ℂ}

end Invariant

section Integrands

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} {s : GA D A → GA D B} {φ : GA D A → ℂ} {F : GA D B → ℂ}

theorem conj_arg (hι : HSpace.IsIsomEmb A B ι) (hs : ∀ h, EmbRel B A ι (s h) h) (hF : IsAutFun B F) {γ δ}
    (hγ : γ ∈ GQ A) (hδ : EmbRel B A ι δ γ) (g n y) : F (δ * n * δ⁻¹ * s (γ * g) * y) = F (n * s g * y) := by
  obtain ⟨s₀, -, hrel, hq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  obtain rfl : s = s₀ := funext fun h => (hrel h _).1 (hs h)
  rw [(hrel _ _).1 hδ, ← hF.left _ (hq γ hγ) (n * s₀ g * y)]
  simp only [map_mul, mul_assoc, inv_mul_cancel_left]

theorem emb_continuous (hι : HSpace.IsIsomEmb A B ι) (hs : ∀ h, EmbRel B A ι (s h) h) : Continuous s := by
  obtain ⟨s₀, hc, hrel, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  obtain rfl : s = s₀ := funext fun h => (hrel h _).1 (hs h)
  exact hc

theorem bes_inv {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hι : HSpace.IsIsomEmb A B ι) (d : BesDat A B ι)
    (hs : ∀ h, EmbRel B A ι (s h) h) (hφ : IsAutFun A φ) (hF : IsAutFun B F) :
    IsRatInv ι d.e fun h n => star (φ h) * F (n * s h * (d.y : GA D B)) * star (besChar ψ d n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro δ γ h n hn
    exact (BesselChar.besChar_conj ψ d δ γ h n hn).1
  · intro g n hn γ hγ hq
    rw [BesselChar.besChar_mul ψ d γ n hγ hn, BesselChar.besChar_rat ψ hψ.1 d γ hγ hq, one_mul, mul_assoc γ, mul_assoc γ,
      hF.left γ hq]
  · intro g n hn γ hγ δ hδ
    rw [(BesselChar.besChar_conj ψ d δ γ hδ n hn).2, conj_arg hι hs hF hγ hδ, hφ.left γ hγ]

end Integrands

section Periods

variable {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

structure IsGood (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : Prop where
  sigOK : A.SigOK
  aniso : IsAniso A
  rank : 1 < A.rank
  isom : HSpace.IsIsomEmb A B ι

structure Frame (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) where
  μ : Measure (GA D A)
  𝓕 : Set (GA D A)
  ν : Measure (NFlag B e)
  𝓝 : Set (NFlag B e)
  s : GA D A → GA D B
  vol : IsVolPair D A μ 𝓕
  unit : IsUnitN B e ν 𝓝
  emb : ∀ h, EmbRel B A ι (s h) h


section

variable {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} {f f' f'' : Frame A B ι e → ℂ}

end

variable (hg : IsGood A B ι)

include hg

omit hg

end Periods

section Record

variable {X : ThetaX D} {T : ThetaTied D X}

variable (Wl : WeilTied D X T) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

end Record

end GlobalTheory.Per.Inhab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapParamOfIsHCTypeW
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA

theorem capParam_of_isHCTypeW : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (U : ℕ → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (π : B.Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsHCTypeW k r z u π → (∀ i : Fin k, U (i.val + 1) = u i) → Q.CapParam k r z π U := by
  intro k r z u U Wp _ _ _ π hz hT hπ hU
  have hπ' : PI.UpqRep.IsHCTypeW k r z u π := hπ
  obtain ⟨u', hu'⟩ := GlobalTheory.CapelliOfHC.exists_isType k r Wp z π u hz hT hπ'
  intro Bs hB w v
  rw [hu'.2.2.2.2.2 Bs hB w v]
  congr 1
  have key : ∀ f : ℕ → ℝ, ∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (f i : ℂ)) =
      ∏ s : Fin k, (w - (k : ℂ) / 2 + 1 / 2 + (f (s.val + 1) : ℂ)) := by
    intro f
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
      ← Fin.prod_univ_eq_prod_range (fun i => w - (k : ℂ) / 2 + 1 / 2 + (f (1 + i) : ℂ))]
    exact Finset.prod_congr rfl fun s _ => by rw [add_comm 1 s.val]
  rw [key, key, ← GlobalTheory.SupNonzero.prod_eq hu' hπ']
  simp only [hU]

end GlobalTheory.ThA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnsignedLocalTermRowLatticeIsTerm
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnsignedLocalTermRowLatticeIsTerm
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
  Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BBTie
open scoped Classical

namespace GlobalTheory.LocOver

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Scale

open Formalism.MainNotions.S.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem h_scale (H : HermSp M V) (c d : E) (x y : V) :
    H.h (c • x) (d • y) = M.L.cj d * c * H.h x y := by
  rw [H.h_smul_left, H.h_herm (d • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]
  ring

theorem Dl_scale (H : HermSp M V) {r : ℕ} (s s' : Fin (r + 1) → E) (f f' : Fin (r + 1) → V) (l : ℕ)
    (hl : l ≤ r + 1) :
    H.Dl (fun a => s a • f a) (fun b => s' b • f' b) l =
      (∏ i : Fin l, M.L.cj (s (Fin.castLE hl i)) * s' (Fin.castLE hl i)) * H.Dl f f' l := by
  unfold HermSp.Dl
  rw [dif_pos hl, dif_pos hl]
  have hsub : (H.Zhat (fun a => s a • f a) (fun b => s' b • f' b)).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun i => M.L.cj (s (Fin.castLE hl i))) *
        (H.Zhat f f').submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Matrix.diagonal (fun i => s' (Fin.castLE hl i)) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.submatrix_apply, HermSp.Zhat, Matrix.of_apply, h_scale]
    ring
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, Finset.prod_mul_distrib]
  ring

end Scale

section Glob

variable {D : D7}

theorem locU_f_eq (Z : LocDat D) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (Tn T'n : ℕ) :
    (locU Z p Λ F F' Tn T'n).f = fun a => sgnP D p a • (locTerm Z p Λ F F' Tn T'n).f a := by
  funext a
  show frFac Z.δ p a • _ = sgnP D p a • ((sgnP D p a * frFac Z.δ p a) • _)
  rw [smul_smul, ← mul_assoc, localSign_sq, one_mul]

theorem locU_f'_eq (Z : LocDat D) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (Tn T'n : ℕ) :
    (locU Z p Λ F F' Tn T'n).f' = fun b => sgnP' D p b • (locTerm Z p Λ F F' Tn T'n).f' b := by
  funext b
  show frFac Z.δ p b • _ = sgnP' D p b • ((sgnP' D p b * frFac Z.δ p b) • _)
  rw [smul_smul, ← mul_assoc, sgnP'_sq, one_mul]

theorem locU_isTerm : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' F' → Gval (lf D F0) F' ≠ 0 → ∀ p : PlF D, (locH Z p).IsTerm (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) ∧ Tri (D.s.atP p).Ep (scaled Z p (frame F')) (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' := by
  intro D Z u u' F0 Λ hR F' hPD hG p
  have hD1 : Formalism.MainNotions.S.Dl F0 F'.fl (D.R.rS + 1) ≠ 0 := by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    exact Formalism.L2.SG.Closed.DNeZeroAt_holds D.host.E (VS D) τ (D.sp.cm.cmUnram.2.1 τ) (D.sp.Y_sig 0) D.R.rS
      (Tu D u) (Tu D u') (Formalism.L2.SG.GramJoint.sig_hS D τ) (Formalism.L2.SG.GramJoint.Tu_pos D u)
      (Formalism.L2.SG.GramJoint.Tu_pos D u') F0 F'.fl hG
  have hT := bt_isTerm Z (locEqC_holds D Z) (locSatC_holds D Z) (locDiffC_holds D Z) (locUnimodC_holds D Z) p F0 Λ F'
    hR hPD hG hD1
  set t := locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u') with ht
  set U := locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u') with hU
  have hf := locU_f_eq Z p Λ (lf D F0) F' (Tu D u) (Tu D u')
  have hf' := locU_f'_eq Z p Λ (lf D F0) F' (Tu D u) (Tu D u')
  set c : ℕ → (D.s.atP p).Ep := fun l => if hl : l ≤ D.R.rS + 1 then
    ∏ i : Fin l, (Z.M p).L.cj (sgnP D p (Fin.castLE hl i)) * sgnP' D p (Fin.castLE hl i) else 1 with hc
  have hDl : ∀ l, l ≤ D.R.rS + 1 → (locH Z p).Dl U.f U.f' l = c l * (locH Z p).Dl t.f t.f' l := by
    intro l hl
    rw [hf, hf', Dl_scale _ _ _ _ _ l hl, hc]
    simp only [dif_pos hl]
    rfl
  have hcu : ∀ l, IsUnit (c l) := by
    intro l
    simp only [hc]
    split_ifs
    · exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun i _ =>
        ((bt_isUnit_sq (localSign_sq p _)).map (Z.M p).L.cj).mul (bt_isUnit_sq (sgnP'_sq p _))
    · exact isUnit_one
  have hcl : c (D.R.rS + 1) = c D.R.rS := by
    simp only [hc, dif_pos le_rfl, dif_pos (Nat.le_succ _)]
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.castLE_rfl, id, sgnP_last₂, bt_sgnP'_last, map_one, mul_one]
    rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hT.1
  · have h := bt_isFrame Z (locSatC_holds D Z) (locDiffC_holds D Z) p F0 Λ hR.2.1.1.fg hR.2.2
      hR.2.1.2.2.1.1 hR.2.1.2.2.2.2 (fun _ => 1) (fun _ => one_mul 1) rfl 1
      (fun a b h => Matrix.one_apply_ne (ne_of_lt h).symm) (fun a => Matrix.one_apply_eq a)
      (bt_pair_li F0 F' hG).1 (bt_Tu_ne u)
    simp only [one_mul, inv_one, bt_frameAct_one] at h
    exact h
  · have hu := admissibility_witness_unitriangular Λ (lf D F0) F'
    have h := bt_isFrame Z (locSatC_holds D Z) (locDiffC_holds D Z) p F'.fl Λ hR.2.1.1.fg hPD.2.2.2 hPD.1.1
      hPD.2.2.1.2 (fun _ => 1) (fun _ => one_mul 1) rfl _ hu.1 hu.2 (bt_pair_li F0 F' hG).2.1 (bt_Tu_ne u')
    simp only [one_mul] at h
    exact h
  · rw [hDl _ le_rfl]
    exact (hcu _).mul hT.2.2.2.1
  · have e : (locH Z p).Gdet U.f U.f' U.T U.T' = (c D.R.rS * (Z.M p).L.cj (c D.R.rS)) *
        (locH Z p).Gdet t.f t.f' t.T t.T' := by
      unfold Loc.HermSp.Gdet Loc.HermSp.normE
      rw [hDl _ le_rfl, hDl _ (Nat.le_succ _), hcl]
      simp only [map_mul]
      rw [show U.T = t.T from rfl, show U.T' = t.T' from rfl]
      ring
    rw [e]
    intro h0
    exact hT.2.2.2.2.1 ((IsUnit.mul_right_eq_zero ((hcu _).mul ((hcu _).map (Z.M p).L.cj))).1 h0)
  · intro g hg
    obtain ⟨h1, h2, h3⟩ := hT.2.2.2.2.2 g hg
    refine ⟨h1, h2, fun b => ?_⟩
    have hagree := (Z.agree p).2.2.2.2.2
    obtain ⟨sg, hs⟩ : ∃ sg, (D.s.atP p).split = some sg := by
      rcases hs : (D.s.atP p).split with _ | sg
      · rw [hg, hs] at hagree; exact hagree.elim
      · exact ⟨sg, rfl⟩
    have hsg : sgnP' D p b = sgnP D p b := by
      unfold sgnP'; rw [hs]
    have e : U.f' b - U.f b = sgnP D p b • (t.f' b - t.f b) := by
      rw [hf, hf']
      beta_reduce
      rw [hsg, smul_sub]
    have hm := Submodule.smul_mem _ (⟨sgnP D p b, bt_sq_one_mem Z p (localSign_sq p b)⟩ : (Z.M p).L.O) (h3 b)
    show U.f' b - U.f b ∈ _
    rw [e]
    exact hm
  · have hu := admissibility_witness_unitriangular Λ (lf D F0) F'
    have hinv := inv_unitri _ hu.1 hu.2
    obtain ⟨Ap, hAp, -⟩ := GlobalTheory.LocOver.tri_scaled D Z (frame F') (frameAct (frame F') (admXi D Λ (lf D F0) F')⁻¹)
      ((admXi D Λ (lf D F0) F')⁻¹.map (fun x : 𝓞 D.host.E => (x : D.host.E)))
      ⟨fun a b h => by simp [hinv.1 a b h], fun a => by simp [hinv.2 a]⟩ (fun b => rfl)
    exact ⟨Ap p, (hAp p).1, (hAp p).2⟩

end Glob

end GlobalTheory.LocOver
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnsignedLocalTermRowLatticeIsTermStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unsignedLocalTerm_row_lattice_isTerm : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' F' → Gval (lf D F0) F' ≠ 0 → ∀ p : PlF D, (locH Z p).IsTerm (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) ∧ Tri (D.s.atP p).Ep (scaled Z p (frame F')) (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' := by
  first | exact @GlobalTheory.LocOver.locU_isTerm | exact GlobalTheory.LocOver.locU_isTerm | (intros; apply GlobalTheory.LocOver.locU_isTerm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsFinDimLink
namespace GlobalTheory

theorem rowsFinDim_link : Formalism.L2.SG.RowsDef.RowsFinDim :=
  CompanionTheory.D.gk.RF.automorphic_forms_finite_dimensional

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativeAlongLieAlgebraPreservesSmoothSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativeAlongLieAlgebraPreservesSmoothSpace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DerClosedSmooth

open GlobalTheory.Mem.RealTranslate GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.Lift

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exists_coords {n : ℕ} (S : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (m : ℕ) (e : Fin m → Matrix (Fin n) (Fin n) ℂ) (c : Fin m → Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ), (∀ j, e j ∈ S) ∧
      ∀ {A : Type} (L : Matrix (Fin n) (Fin n) ℂ → A → ℂ),
        (∀ (a : ℝ), ∀ X ∈ S, ∀ Y ∈ S, L (a • X + Y) = (a : ℂ) • L X + L Y) →
        ∀ Y ∈ S, ∀ x, L Y x = ∑ j, (c j Y : ℂ) * L (e j) x := by
  let b := Module.finBasis ℝ S
  choose c hc using fun j => LinearMap.exists_extend (b.coord j)
  refine ⟨_, fun j => b j, fun j => LinearMap.toContinuousLinearMap (c j), fun j => (b j).2, fun L hL Y hY x => ?_⟩
  have h0 : L 0 = 0 := by
    have := hL 1 0 S.zero_mem 0 S.zero_mem
    simpa using this
  let l : S →ₗ[ℝ] ℂ :=
    { toFun := fun Z => L Z x
      map_add' := fun Z Z' => by simpa using congrFun (hL 1 Z Z.2 Z' Z'.2) x
      map_smul' := fun a Z => by simpa [h0] using congrFun (hL a Z Z.2 0 S.zero_mem) x }
  have h1 : L Y x = l ⟨Y, hY⟩ := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, ← b.sum_repr ⟨Y, hY⟩, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 : c j Y = b.repr ⟨Y, hY⟩ j := LinearMap.congr_fun (hc j) ⟨Y, hY⟩
  rw [map_smul, LinearMap.coe_toContinuousLinearMap', h2, Complex.real_smul]
  rfl

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}


variable (V) in
def lieSub (τ : D.what₂.Tau) : Submodule ℝ (Matrix (Fin V.rank) (Fin V.rank) ℂ) :=
  GlobalTheory.UnitaryLieAlgebra.unitaryLie (gramAt D V τ)


variable (θ) in
def SmFam {k : ℕ} (B : (Fin k → ℝ) → GA D V) : Prop :=
  ∀ τ, (ContDiff ℝ ∞ fun t => infMat D.sp.cm.sig V.gram (θ τ) (B t)) ∧
    ContDiff ℝ ∞ fun t => infMat D.sp.cm.sig V.gram (θ τ) (B t)⁻¹

theorem SmFam.mul {k : ℕ} {A B : (Fin k → ℝ) → GA D V} (hA : SmFam θ A) (hB : SmFam θ B) :
    SmFam θ fun t => A t * B t := fun τ => by
  simp only [_root_.mul_inv_rev, infMat_mul]
  exact ⟨(hA τ).1.mul (hB τ).1, (hB τ).2.mul (hA τ).2⟩

theorem SmFam.tail {k : ℕ} {A : (Fin k → ℝ) → GA D V} (hA : SmFam θ A) :
    SmFam θ fun t : Fin (k + 1) → ℝ => A (Fin.tail t) := fun τ => by
  have h : ContDiff ℝ ∞ fun t : Fin (k + 1) → ℝ => Fin.tail t := contDiff_pi.2 fun i => contDiff_apply ℝ (fun _ => ℝ) i.succ
  exact ⟨(hA τ).1.comp h, (hA τ).2.comp h⟩

theorem contDiff_oneP (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (τ' : D.what₂.Tau) :
    ContDiff ℝ ∞ fun s : ℝ => infMat D.sp.cm.sig V.gram (θ τ') (oneP θ V τ X s) := by
  by_cases c : τ' = τ
  · subst c
    simp only [(isAtTau_oneP hθ hX _).2.1]
    have h2 : ContDiff ℝ ∞ fun t : ℝ => fun _ : Fin 1 => t := contDiff_pi.2 fun _ => contDiff_id
    simpa [Function.comp_def] using (GlobalTheory.GardingVec.contDiff_expProd fun _ : Fin 1 => X).comp h2
  · simp only [(isAtTau_oneP hθ hX _).2.2 τ' c]
    exact contDiff_const

theorem smFam_oneP (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) {k : ℕ} (i : Fin k) : SmFam θ fun t : Fin k → ℝ => oneP θ V τ X (t i) := fun τ' => by
  have hi : ∀ t, (oneP θ V τ X t)⁻¹ = oneP θ V τ X (-t) := fun t => inv_eq_of_mul_eq_one_right (by
    rw [← oneP_add hθ hX, add_neg_cancel, oneP_zero hθ])
  simp only [hi]
  exact ⟨(contDiff_oneP hθ hX τ').comp (contDiff_apply ℝ (fun _ => ℝ) i),
    (contDiff_oneP hθ hX τ').comp (contDiff_apply ℝ (fun _ => ℝ) i).neg⟩


variable (θ) in
def prodP {k : ℕ} (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : Fin k → ℝ) :
    GA D V := (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod

theorem prodP_succ {k : ℕ} (τs : Fin (k + 1) → D.what₂.Tau) (Xs : Fin (k + 1) → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (t : Fin (k + 1) → ℝ) : prodP θ τs Xs t =
      oneP θ V (τs 0) (Xs 0) (t 0) * prodP θ (Fin.tail τs) (Fin.tail Xs) (Fin.tail t) := by
  unfold prodP
  rw [List.ofFn_succ, List.prod_cons]
  rfl

theorem prodP_laws (hθ : IsInfFam θ) {k : ℕ} (τs : Fin k → D.what₂.Tau)
    (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : ∀ i, Xs i ∈ lieAt V (τs i)) :
    SmFam θ (prodP θ τs Xs) ∧ Continuous (prodP θ τs Xs) ∧ ∀ i, ∃ B : (Fin k → ℝ) → GA D V, SmFam θ B ∧ ∀ t s,
      prodP θ τs Xs (Function.update t i (t i + s)) =
        prodP θ τs Xs t * oneP θ V (τs i) (adAt θ (B t) (τs i) (Xs i)) s := by
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  induction k with
  | zero =>
    have e : prodP θ τs Xs = fun _ => 1 := funext fun t => by simp [prodP]
    rw [e]
    exact ⟨fun _ => ⟨contDiff_const, contDiff_const⟩, continuous_const, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih (Fin.tail τs) (Fin.tail Xs) fun i => hX i.succ
    rw [funext (prodP_succ (θ := θ) τs Xs)]
    refine ⟨(smFam_oneP hθ (hX 0) 0).mul h1.tail, ((continuous_oneP hθ (hX 0)).comp (continuous_apply 0)).mul
      (h2.comp (continuous_pi fun i => continuous_apply i.succ)), fun i => ?_⟩
    refine Fin.cases ⟨_, h1.tail, fun t s => ?_⟩ (fun j => ?_) i
    · simp only [Function.update_self, Fin.tail_update_zero]
      rw [oneP_add hθ (hX 0), mul_assoc, GlobalTheory.Size.oneP_mul_adelic hθ _ (hX 0) s, mul_assoc]
    · obtain ⟨B, hB, h⟩ := h3 j
      refine ⟨_, hB.tail, fun t s => ?_⟩
      simp only [Fin.tail_update_succ, Function.update_of_ne (Fin.succ_ne_zero j).symm]
      rw [mul_assoc]
      exact congrArg _ (h (Fin.tail t) s)

theorem smooth_of_closed : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), IsInfFam θ → ∀ W : Set (GA D V → ℂ), (∀ f ∈ W, Continuous f ∧ ∀ τ, ∃ L : Matrix (Fin V.rank) (Fin V.rank) ℂ → GA D V → ℂ, (∀ X ∈ lieAt V τ, L X ∈ W ∧ ∀ x, HasDerivAt (fun t : ℝ => f (x * oneP θ V τ X t)) (L X x) 0) ∧ ∀ (a : ℝ), ∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt V τ, L (a • X + Y) = (a : ℂ) • L X + L Y) → ∀ f ∈ W, ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
  intro D θ V hθ W hW f hf k τs Xs hX g
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  obtain ⟨-, hc, hP⟩ := prodP_laws hθ τs Xs hX
  choose B hB hP using hP
  suffices h : ∀ n : ℕ, ∀ f ∈ W, ContDiff ℝ n fun t => f (g * prodP θ τs Xs t) from
    contDiff_infty.2 fun n => h n f hf
  intro n
  induction n with
  | zero => exact fun f hf => contDiff_zero.2 ((hW f hf).1.comp (continuous_const.mul hc))
  | succ n ih =>
    intro f hf
    choose L hL hlin using (hW f hf).2
    let d : Fin k → (Fin k → ℝ) → ℂ := fun i t => L (τs i) (adAt θ (B i t) (τs i) (Xs i)) (g * prodP θ τs Xs t)
    have hm : ∀ i t, adAt θ (B i t) (τs i) (Xs i) ∈ lieAt V (τs i) := fun i t =>
      GlobalTheory.Size.adAt_mem_lieAt hθ _ (hX i)
    have hd : ∀ i, ContDiff ℝ n (d i) := fun i => by
      obtain ⟨m, e, c, he, hs⟩ := exists_coords (lieSub V (τs i))
      have e1 : d i = fun t => ∑ j, (c j (adAt θ (B i t) (τs i) (Xs i)) : ℂ) * L (τs i) (e j) (g * prodP θ τs Xs t) :=
        funext fun t => hs _ (hlin (τs i)) _ (hm i t) _
      have e2 : ContDiff ℝ n fun t => adAt θ (B i t) (τs i) (Xs i) :=
        (((hB i (τs i)).2.mul contDiff_const).mul (hB i (τs i)).1).of_le (by exact_mod_cast le_top)
      rw [e1]
      exact ContDiff.sum fun j _ => (Complex.ofRealCLM.contDiff.comp ((c j).contDiff.comp e2)).mul
        (ih _ (hL _ _ (he j)).1)
    have hder := GlobalTheory.T.hasFDerivAt_of_continuous_coordinate_derivs k (fun t => f (g * prodP θ τs Xs t)) d (fun i t => by
      have h1 := HasDerivAt.comp_sub_const (t i) (t i) (by rw [sub_self]; exact (hL _ _ (hm i t)).2 (g * prodP θ τs Xs t))
      refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      simp only [mul_assoc, ← hP, add_sub_cancel]) fun i => (hd i).continuous
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    exact ⟨_, ContDiff.sum fun i _ => contDiff_const.smulRight (hd i), hder⟩

end GlobalTheory.DerClosedSmooth

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativeAlongLieAlgebraPreservesSmoothSpaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_along_lie_algebra_preserves_smooth_space : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), IsInfFam θ → ∀ W : Set (GA D V → ℂ), (∀ f ∈ W, Continuous f ∧ ∀ τ, ∃ L : Matrix (Fin V.rank) (Fin V.rank) ℂ → GA D V → ℂ, (∀ X ∈ lieAt V τ, L X ∈ W ∧ ∀ x, HasDerivAt (fun t : ℝ => f (x * oneP θ V τ X t)) (L X x) 0) ∧ ∀ (a : ℝ), ∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt V τ, L (a • X + Y) = (a : ℂ) • L X + L Y) → ∀ f ∈ W, ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
  first | exact @GlobalTheory.DerClosedSmooth.smooth_of_closed | exact GlobalTheory.DerClosedSmooth.smooth_of_closed | (intros; apply GlobalTheory.DerClosedSmooth.smooth_of_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.JExistsAll
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem jExists_all : ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), JExists D F := by
  intro D F X u wt hw
  obtain ⟨J, hJ, -⟩ := GlobalTheory.T.exists_equivariant_unitary_coefficientMap_onto D X u (F u) wt hw
  exact ⟨J, hJ⟩

end GlobalTheory
end

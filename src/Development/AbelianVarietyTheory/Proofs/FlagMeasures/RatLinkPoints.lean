module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActRow
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Assembly
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.GramMapFibreExistence
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.SdExInst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeCompressionFormulaOfStrictLowestKType
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeDecayGapOfCompressionFormulaGap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatLinkPoints
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RatIsomPoint

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Level Formalism.L2.SG.Pf.Slab Formalism.L2.SG.Pf.Vanish2 Formalism.L2.SG.TermOp.KExpCut
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.SlabCoverPf Formalism.L2.SG.PoincareInHH.Cut
open Matrix

variable {D : D7} (X : HidaSetting D)

theorem crd_injective' {y y' : (VS D).V} (h : X.crd y = X.crd y') : y = y' := by
  rw [← toV_crd X y, ← toV_crd X y', h]

theorem eq_matEC {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} {M : GL (Fin X.B.I.n) X.B.I.E}
    (h3 : ∀ y, X.crd (n y) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y) : n = matEC X M := by
  ext y
  exact crd_injective' X (by rw [h3, matE_crdC])

theorem nrat_iff (u : D.what₂.Word) {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x n) :
    n ∈ NRat (lf D (X.Fu u)) ↔ x.1 ∈ X.NinfU u := by
  constructor
  · intro hn
    have hgtop : Formalism.HermitianLatticesTheory.gmap n (⊤ : Submodule (𝓞 D.host.E) (VS D).V) = ⊤ := by
      unfold Formalism.HermitianLatticesTheory.gmap; rw [Submodule.map_top]; exact LinearMap.range_eq_top.2 n.surjective
    exact nLamNinf_holds D X u ⊤ x n hx ⟨⟨hn.1, hgtop⟩, hn.2.1, hn.2.2⟩
  · intro hν1
    obtain ⟨M, hM, hinf, -, h3⟩ := hx
    have hn := eq_matEC X h3
    subst hn
    obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
    have hGv : ∀ y, uMat (x.1 v) *ᵥ Formalism.L2.SG.Pf.Vanish2.rvHom X.B.I v y = Formalism.L2.SG.Pf.Vanish2.rvHom X.B.I v ((M : Matrix _ _ _) *ᵥ y) := by
      intro y
      rw [Formalism.L2.SG.Pf.Vanish2.rvHom_apply, Formalism.L2.SG.Pf.Vanish2.rvHom_apply, hinf v]
      exact rv_mulVec X v _ y
    have hsub : ∀ y, (uMat (x.1 v) - 1) *ᵥ rv X.B.I v y = rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ y) :=
      fun y => tr_sub (Formalism.L2.SG.Pf.Vanish2.rvHom X.B.I v) _ _ hGv y
    have hcrdn : ∀ y, X.crd (matEC X M y - y) = ((M : Matrix _ _ _) - 1) *ᵥ X.crd y := by
      intro y
      rw [crd_sub', matE_crdC, Matrix.sub_mulVec, Matrix.one_mulVec]
    have hback : ∀ (y : (VS D).V) (T : Set (Fin D.R.rS)),
        ((M : Matrix _ _ _) - 1) *ᵥ X.crd y ∈ Submodule.span X.B.I.E (X.eR '' T) →
        matEC X M y - y ∈ Submodule.span D.host.E (X.eX '' T) := by
      intro y T hy
      rw [← hcrdn] at hy
      have := toV_span X hy
      rwa [toV_crd] at this
    have hInN := hν1 v
    refine ⟨matE_isomC X M hM, ?_, ?_⟩
    · intro j x hx
      change x ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j + 1}) at hx
      change _ ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j})
      rw [X.Fu_e] at hx ⊢
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, ha, rfl⟩ := hy
        have h1 := hInN.1.1 a
        rw [hsub] at h1
        have h2 : rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ X.eR a) ∈
            Submodule.span ℂ (rv X.B.I v '' (X.eR '' {b | b.1 < a.1})) := by
          rw [Set.image_image]; exact h1
        have h3 := rv_desc X v _ _ h2
        have h4 : ((M : Matrix _ _ _) - 1) *ᵥ X.crd (X.eX a) ∈
            Submodule.span X.B.I.E (X.eR '' {b | b.1 < j}) := by
          refine Submodule.span_mono (Set.image_mono fun b hb => ?_) h3
          have : a.1 < j + 1 := ha
          show b.1 < j
          have : b.1 < a.1 := hb
          omega
        exact hback _ _ h4
      | zero => simp
      | add a b _ _ ha hb =>
        rw [map_add (f := _), add_sub_add_comm]
        exact add_mem ha hb
      | smul c a _ ha =>
        rw [map_smul, ← smul_sub]
        exact Submodule.smul_mem _ _ ha
    · intro x hx
      change x ∈ orth (VS D) (Submodule.span D.host.E (Set.range (X.Fu u).e)) at hx
      change _ ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)
      rw [X.Fu_e] at hx ⊢
      have hzero : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.crd x)) = 0 := by
        intro a
        rw [hJ_rv]
        have h0 : hE X (X.eR a) (X.crd x) = 0 := by
          apply X.ιE.injective
          rw [iota_hE, map_zero, HidaSetting.eR, toV_crd, toV_crd]
          exact (mem_orth_iff _ _).1 hx _ (Submodule.subset_span ⟨a, rfl⟩)
        rw [h0, map_zero]
      have h1 := hInN.2 _ hzero
      rw [hsub] at h1
      have huniv : {b : Fin D.R.rS | b.1 < D.R.rS} = Set.univ := Set.eq_univ_of_forall fun b => b.2
      have h2 : rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ X.crd x) ∈
          Submodule.span ℂ (rv X.B.I v '' (X.eR '' {b | b.1 < D.R.rS})) := by
        rw [Set.image_image]; exact h1
      have h3 := hback x _ (rv_desc X v _ _ h2)
      rwa [huniv, Set.image_univ] at h3

end GlobalTheory.RatIsomPoint

namespace GlobalTheory.RatIsomPoint

open Formalism.L2.SG.NonRelPf

variable {D : D7} (X : HidaSetting D)

theorem sgUp_eq {E : Type} [Field E] [NumberField E] {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Formalism.L2.SG.PairVal.sgUp A = ∑ a : Fin r, A a.castSucc a.succ := by
  unfold Formalism.L2.SG.PairVal.sgUp
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last, lt_self_iff_false, dif_neg, not_false_eq_true, add_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dite_eq_left (by omega)]
  rfl

theorem root_entry (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (A : Formalism.L2.SG.PairVal.MatR D)
    (hA : ∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) (a : Fin D.R.rS) :
    (VS D).hT (X.fY a) (n (nxt X.eX (X.zu u) a)) = A a.castSucc a.succ := by
  have e : nxt X.eX (X.zu u) a = frame (lf D (X.Fu u)) a.succ := by
    show _ = (X.Fu u).fvec a.succ
    rw [fvec_succ, X.Fu_e, X.flagZVector]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, hA, map_sum, Fin.sum_univ_castSucc]
  have h1 : ∀ b : Fin D.R.rS, frame (lf D (X.Fu u)) b.castSucc = X.eX b := by
    intro b
    show (X.Fu u).fvec b.castSucc = _
    simp only [FlagG.fvec, Fin.snoc_castSucc, X.Fu_e]
  have h2 : frame (lf D (X.Fu u)) (Fin.last D.R.rS) = X.zu u := by
    show (X.Fu u).fvec (Fin.last _) = _
    simp only [FlagG.fvec, Fin.snoc_last, X.flagZVector]
  simp only [map_smul, smul_eq_mul, h1, h2, hTfe, (X.zu_orth u a).2, mul_zero, add_zero, mul_ite, mul_one]
  rw [Finset.sum_ite_eq']
  simp

theorem psi_eq (u : D.what₂.Word) {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x n)
    (A : Formalism.L2.SG.PairVal.MatR D)
    (hA : ∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) :
    X.psiInfU u x.1 = Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp A) := by
  rw [psi_rat X u hx]
  simp only [root_entry X u n A hA]
  have hs : ∀ v, (∑ a : Fin D.R.rS, (Φ X v (A a.castSucc a.succ) + star (Φ X v (A a.castSucc a.succ)))) =
      X.B.I.φ v (X.ιE.symm (Formalism.L2.SG.PairVal.sgUp A)) +
        star (X.B.I.φ v (X.ιE.symm (Formalism.L2.SG.PairVal.sgUp A))) := by
    intro v
    rw [Finset.sum_add_distrib, ← star_sum, ← Φ_sum, ← sgUp_eq]
    rfl
  simp only [hs]
  rw [Formalism.L2.SG.RealObj.PlaceEmbeddingTraceSums.TraceSum_holds D X X.B.g (X.ιE.symm _), RingEquiv.apply_symm_apply, X.g_eq]
  rfl

end GlobalTheory.RatIsomPoint

namespace GlobalTheory.RatIsomPoint

theorem ratLink_points : ∀ (D : D7) (X : HidaSetting D), (∀ γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, ∃! x : X.B.I.GA, RatLink X x γ) ∧ (∀ x y γ δ, RatLink X x γ → RatLink X y δ → RatLink X (x * y) (γ * δ) ∧ RatLink X x⁻¹ γ⁻¹ ∧ (x.1 = y.1 → γ = δ)) ∧ ∀ (u : D.what₂.Word) x n, RatLink X x n → (n ∈ NRat (lf D (X.Fu u)) ↔ x.1 ∈ X.NinfU u) ∧ (n ∈ NRat (lf D (X.Fu u)) → ∀ A : Formalism.L2.SG.PairVal.MatR D, (∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) → X.psiInfU u x.1 = Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp A)) := by
  intro D X
  refine ⟨fun γ hγ => ?_, fun x y γ δ hx hy => ?_, fun u x n hx => ?_⟩
  · obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X γ hγ
    exact ⟨x, hx, fun y hy => Formalism.L2.SG.TermOp.Vanish.ratLink_unique X hy hx⟩
  · exact ⟨Formalism.L2.SG.TermOp.Vanish.ratLink_mul X hx hy, Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hx,
      Formalism.L2.SG.Pf.IdMeet.lin_eq_of_fst X hx hy⟩
  · exact ⟨nrat_iff X u hx, fun _ A hA => psi_eq X u hx A hA⟩

end GlobalTheory.RatIsomPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFibreMeasuresArchimedeanGramMap
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFibreMeasuresArchimedeanGramMap
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.ArchGramFibre

open Formalism.L2.SG.Sub PI.VolFromSW PI.AdicCompletionValuation PI.VolStabS

theorem exists_real_coords (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M a : ℕ) :
    ∃ (n m : ℕ) (eV : (Fin a → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → ℝ))
      (eH : HermR (Ainf F) σ a ≃ₜ (Fin m → ℝ)),
      (∀ x y, eV (x + y) = eV x + eV y) ∧ ∀ x y, eH (x + y) = eH x + eH y := by
  have : IsTotallyReal F := hCM.1
  obtain ⟨k, eK, hK⟩ := exists_coord_tens F E
  obtain ⟨k1, e1, h1⟩ := exists_coord_pi eK hK (Fin M)
  obtain ⟨n, eV, hV⟩ := exists_coord_pi e1 h1 (Fin a)
  obtain ⟨k2, e2, h2⟩ := exists_coord_pi eK hK (Fin a)
  obtain ⟨N, eM, hM⟩ := exists_coord_pi e2 h2 (Fin a)
  have hdiv : ∀ n : ℕ, 0 < n → ∀ S ∈ HermR (Ainf F) σ a, ∃ T ∈ HermR (Ainf F) σ a, n • T = S := by
    intro n hn S hS
    let c : Ainf F ⊗[F] E := algebraMap F (Ainf F ⊗[F] E) (1 / n)
    have hsc : sigR (Ainf F) σ c = c :=
      (Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ).commutes _
    refine ⟨c • S, ?_, ?_⟩
    · intro i j
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, hsc]
      rw [hS i j]
    · have hc1 : (n : Ainf F ⊗[F] E) * c = 1 := by
        simp only [c]
        rw [← map_natCast (algebraMap F (Ainf F ⊗[F] E)) n, ← map_mul]
        have : (n : F) ≠ 0 := by exact_mod_cast hn.ne'
        rw [mul_one_div_cancel this, map_one]
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, ← mul_assoc, hc1, one_mul]
  obtain ⟨m, eH, hH⟩ := exists_coord_sub (X := Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) eM hM
    (HermR (Ainf F) σ a) (isClosed_HermR (Ainf F) σ a) hdiv
  exact ⟨n, m, eV, eH, hV, hH⟩

theorem gramB_surj_of_free (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M a : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) :
    ∀ X : Fin a → Fin M → Ainf F ⊗[F] E, LinearIndependent (Ainf F ⊗[F] E) X →
      ∀ S : HermR (Ainf F) σ a, ∃ Y, gramB (Ainf F) σ J X Y = S := by
  intro X hX S
  have := semisimpleTens_holds F E σ hCM
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabS.sigma_invol σ hCM.2.2.2
  let s := sigR (Ainf F) σ
  let Z : Fin a → Fin M → Ainf F ⊗[F] E :=
    fun i => Matrix.vecMul (fun l => s (X i l)) (JR (F := F) (Ainf F) J)
  have hZh : ∀ i y, hR (Ainf F) σ J (X i) y = ∑ k, Z i k * y k := by
    intro i y
    simp only [hR, Formalism.UG.hform, Z, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hJu : IsUnit (JR (F := F) (Ainf F) J).det := by
    have e := RingHom.map_det (inclR (F := F) (E := E) (Ainf F)) J
    rw [RingHom.mapMatrix_apply] at e
    show IsUnit (J.map (inclR (Ainf F))).det
    rw [← e]
    exact (isUnit_iff_ne_zero.2 hJ.2).map _
  have hZ : LinearIndependent (Ainf F ⊗[F] E) Z := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    let v : Fin M → Ainf F ⊗[F] E := fun l => ∑ i, g i * s (X i l)
    have hv0 : Matrix.vecMul v (JR (F := F) (Ainf F) J) = 0 := by
      funext j
      have := congrFun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Z, Matrix.vecMul, dotProduct,
        Finset.mul_sum, Pi.zero_apply] at this
      simp only [Matrix.vecMul, dotProduct, v, Finset.sum_mul, Pi.zero_apply]
      rw [Finset.sum_comm]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    have hv : v = 0 := by
      have := congrArg (fun u => Matrix.vecMul u (JR (F := F) (Ainf F) J)⁻¹) hv0
      simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJu, Matrix.vecMul_one,
        Matrix.zero_vecMul] at this
      exact this
    have hX0 : ∑ i, s (g i) • X i = 0 := by
      funext l
      have := congrArg s (congrFun hv l)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [v, map_sum, map_mul, s, sigR_invol (Ainf F) σ hσ, Pi.zero_apply, map_zero] at this
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    have := Fintype.linearIndependent_iff.1 hX _ hX0 i
    have e2 := congrArg s this
    simp only [s, sigR_invol (Ainf F) σ hσ, map_zero] at e2
    exact e2
  let half : Ainf F ⊗[F] E := algebraMap F (Ainf F ⊗[F] E) (1/2)
  have hh : half + half = 1 := by
    simp only [half, ← map_add (f := _)]; norm_num
    first | rfl | exact Algebra.TensorProduct.one_def.symm
  have hsh : s half = half := (Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ).commutes _
  have hw : ∀ j, ∃ w : Fin M → Ainf F ⊗[F] E, ∀ i, ∑ k, Z i k * w k =
      half * (S : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) i j :=
    fun j => exists_dual_of_linIndep Z hZ _
  choose Y hY using hw
  refine ⟨Y, ?_⟩
  funext i j
  have h1 : hR (Ainf F) σ J (X i) (Y j) = half * (S : Matrix _ _ _) i j := by rw [hZh]; exact hY j i
  have h2 : hR (Ainf F) σ J (Y i) (X j) = half * (S : Matrix _ _ _) i j := by
    rw [← hR_herm (Ainf F) σ hσ J hJ.1 (X j) (Y i), hZh, hY i j]
    simp only [map_mul]
    rw [show sigR (Ainf F) σ half = half from hsh, S.2 i j]
  show hR (Ainf F) σ J (X i) (Y j) + hR (Ainf F) σ J (Y i) (X j) = _
  rw [h1, h2, ← add_mul, hh, one_mul]

theorem exists_submersion_coords (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M a : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) :
    ∃ (n m : ℕ) (eV : (Fin a → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → ℝ))
      (eH : HermR (Ainf F) σ a ≃ₜ (Fin m → ℝ)) (f' : (Fin n → ℝ) → (Fin m → ℝ)),
      (∀ x y, eV (x + y) = eV x + eV y) ∧ (∀ x y, eH (x + y) = eH x + eH y) ∧ ContDiff ℝ 1 f' ∧
      (∀ X, ((eH.symm (f' (eV X)) : HermR (Ainf F) σ a) : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) =
        gramR (Ainf F) σ J X) ∧
      ∀ X, LinearIndependent (Ainf F ⊗[F] E) X → Function.Surjective (fderiv ℝ f' (eV X)) := by
  obtain ⟨n, m, eV, eH, hV, hH⟩ := exists_real_coords F E σ hCM M a
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabS.sigma_invol σ hCM.2.2.2
  let Q : (Fin a → Fin M → Ainf F ⊗[F] E) → HermR (Ainf F) σ a := gramH (Ainf F) σ hσ J hJ.1
  let β : (Fin a → Fin M → Ainf F ⊗[F] E) → (Fin a → Fin M → Ainf F ⊗[F] E) →
      HermR (Ainf F) σ a := fun X Y => ⟨gramB (Ainf F) σ J X Y, gramB_mem (Ainf F) σ hσ J hJ.1 X Y⟩
  have hβc : Continuous (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (Fin a → Fin M → Ainf F ⊗[F] E) => β p.1 p.2) := by
    exact (continuous_gramB (Ainf F) σ J).subtype_mk _
  have hβa : ∀ x y z, β (x + y) z = β x z + β y z := by
    intro x y z; apply Subtype.ext; funext i j
    show gramB (Ainf F) σ J (x + y) z i j = gramB (Ainf F) σ J x z i j + gramB (Ainf F) σ J y z i j
    simp only [gramB, Pi.add_apply, PI.VolStabS.hR_add_left, PI.VolStabS.hR_add_right]
    abel
  have hβs : ∀ x y, β x y = β y x := by
    intro x y; apply Subtype.ext; funext i j
    simp only [β, gramB]; exact add_comm _ _
  have hQ : ∀ x, β x x = Q x + Q x := by
    intro x; apply Subtype.ext; funext i j; rfl
  obtain ⟨hC, hD⟩ := quadCoord_holds _ _ n m eV eH Q β hV hH hβc hβa hβs hQ
  refine ⟨n, m, eV, eH, fun y => eH (Q (eV.symm y)), hV, hH, hC, fun X => ?_, fun X hX => ?_⟩
  · simp [Q, gramH]
  · intro t
    obtain ⟨Y, hY⟩ := gramB_surj_of_free F E σ hCM M a J hJ X hX (eH.symm t)
    refine ⟨eV Y, ?_⟩
    rw [hD X Y]
    have : β X Y = eH.symm t := Subtype.ext hY
    rw [this, Homeomorph.apply_symm_apply]

theorem gram_densities (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M a : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (μ : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ a))
    (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure) :
    DensAll μ (gramR (Ainf F) σ J) Subtype.val ν {X | LinearIndependent (Ainf F ⊗[F] E) X} := by
  obtain ⟨n, m, eV, eH, f', hV, hH, hC, hG, hS⟩ := exists_submersion_coords F E σ hCM M a J hJ
  have : ContinuousAdd (Fin a → Fin M → Ainf F ⊗[F] E) := ⟨by
    have e : (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (Fin a → Fin M → Ainf F ⊗[F] E) =>
        p.1 + p.2) = fun p => eV.symm (eV p.1 + eV p.2) := by
      funext p; rw [← hV, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have : ContinuousAdd (HermR (Ainf F) σ a) := ⟨by
    have e : (fun p : HermR (Ainf F) σ a × HermR (Ainf F) σ a => p.1 + p.2) =
        fun p => eH.symm (eH p.1 + eH p.2) := by
      funext p; rw [← hH, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have hμ' : (μ.map eV).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μ (AddMonoidHom.mk' eV hV) eV.continuous eV.surjective
      (eV.map_cocompact).le
  have hν' : (ν.map eH).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map ν (AddMonoidHom.mk' eH hH) eH.continuous eH.surjective
      (eH.map_cocompact).le
  have hD := submDens_holds n m _ _ hμ' hν' f' hC
  refine densAll_transport μ ν (gramR (Ainf F) σ J) Subtype.val _ eV eH f'
    Subtype.val_injective (fun X => hG X) (densAll_mono hD ?_)
  rintro y ⟨X, hX, rfl⟩
  exact hS X hX

theorem exists_fibreFamily : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M a : ℕ) (J : Matrix (Fin M) (Fin M) E),
    IsHermND σ J →
    ∀ (μ : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ a)),
      μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
      ∃ fib : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
        IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val
          {X | LinearIndependent (Ainf F ⊗[F] E) X} ν Set.univ fib := by
  intro F E _ _ _ _ _ σ hCM M a J hJ μ ν hμ hν
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabS.sigma_invol σ hCM.2.2.2
  exact fib_of_tens PI.VolStabS.DiscreteGroups.fibOfDens_holds
    (tensFacts_of σ hσ J hJ.1 a (Ainf F) (isOpen_units_Ainf F) (lip_ainf F)) μ ν hμ hν
    (gram_densities F E σ hCM M a J hJ μ ν hμ hν)

end GlobalTheory.ArchGramFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFibreMeasuresArchimedeanGramMapStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibreMeasures_archimedeanGramMap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M a : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (μ : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ a)),
      μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
      ∃ fib : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
        IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val
          {X | LinearIndependent (Ainf F ⊗[F] E) X} ν Set.univ fib := by
  first | exact @GlobalTheory.ArchGramFibre.exists_fibreFamily | exact GlobalTheory.ArchGramFibre.exists_fibreFamily | (intros; apply GlobalTheory.ArchGramFibre.exists_fibreFamily <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsStarProjectionOfIsOrthProjOnto
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.Dec.ProjCuspGap

theorem rank_le_dim {n : ℕ} (ε : Fin n → Bool) : rkR ε ≤ n := by
  refine (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans ?_)
  simp

theorem gap_numeric {n : ℕ} (ε : Fin n → Bool) (h : ℝ)
    (hh : 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) :
    rkR ε = 0 ∨ 8 * Real.sqrt (rkR ε) * (0 + 4 * n * rkR ε) < h := by
  rcases Nat.eq_zero_or_pos (rkR ε) with h0 | h0
  · exact Or.inl h0
  right
  have hq : (0 : ℝ) < rkR ε := by exact_mod_cast h0
  have hn : (0 : ℝ) < n := by exact_mod_cast h0.trans_le (rank_le_dim ε)
  have e : ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) = Real.sqrt (rkR ε) * rkR ε := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one hq.ne']
    norm_num
  rw [e] at hh
  have hp : 0 < (n : ℝ) * (Real.sqrt (rkR ε) * rkR ε) := by positivity
  nlinarith

theorem rank_pos_of_ne {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : ε a ≠ ε b) : 0 < rkR ε := by
  unfold rkR
  refine lt_min (Finset.card_pos.2 ?_) (Finset.card_pos.2 ?_)
  · by_cases ha : ε a = true
    · exact ⟨a, by simp [ha]⟩
    · exact ⟨b, by revert hab ha; cases ε a <;> cases hb : ε b <;> simp [hb]⟩
  · by_cases ha : ε a = true
    · exact ⟨b, by revert hab ha; cases ε a <;> cases hb : ε b <;> simp [hb]⟩
    · exact ⟨a, by simp [ha]⟩

theorem two_mul_lt {n : ℕ} (ε : Fin n → Bool) (h : ℝ)
    (hh : 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) (h0 : 0 < rkR ε) : 2 * (n : ℝ) < h := by
  have hq : (1 : ℝ) ≤ rkR ε := by exact_mod_cast h0
  have hn : (0 : ℝ) < n := by exact_mod_cast h0.trans_le (rank_le_dim ε)
  have h1 : (1 : ℝ) ≤ ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := Real.one_le_rpow hq (by norm_num)
  nlinarith

theorem isStarProjection_of_isOrthProjOnto {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {T : H →L[ℂ] H} {S : Submodule ℂ H} (hT : IsOrthProjOnto T S) : IsStarProjection T :=
  ⟨hT.1, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 fun x y => hT.2.1 x y⟩

theorem projector_rank_cuspidal : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → GapGe B h → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → Integrable (ph B d) (muInf B.I) ∧ (HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → IsStarProjection T ∧ FiniteDimensional ℂ (LinearMap.range (T : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund)) ∧ Module.finrank ℂ (LinearMap.range (T : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund)) = B.D ∧ ∀ Fv ∈ LinearMap.range (T : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund), B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext Fv)) := by
  intro B d h hds hgap hh
  have hD : DecGap := GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap
  have hloc : LocDec B h := GlobalTheory.Dec.locDec_of_decGap_gapGe hD B d h hds hgap hh
  have hK : ∀ v, IsKTypeOf (B.I.ε v) (B.σ v) (lowK (B.I.ε v) (B.lam v))
      (lowKSub (B.I.ε v) (B.lam v) (B.σ v)) := fun v =>
    GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub _ _ _ _ _ (hds v).1 (hds v).2.1 fun a b hab =>
      (two_mul_lt _ h (hh v) (rank_pos_of_ne _ hab)).trans_le (hgap v a b hab)
  obtain ⟨hc, hle, hint⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hds hloc
  have hI := hint 0 le_rfl fun v => gap_numeric _ h (hh v)
  have hph : Integrable (ph B d) (muInf B.I) := by
    refine hI.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    simpa using hle g
  refine ⟨hph, fun hb hfin T hT => ?_⟩
  obtain ⟨h1, -, -, h4, h5⟩ := (GlobalTheory.GlobProj.globalProj_holds B d hds hph).2.2.2 T hT
  refine ⟨isStarProjection_of_isOrthProjOnto h1, h4 hfin, h5, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact (GlobalTheory.T.convolution_range_cuspidal_of_lowestKType B d h hds hK hh hloc hb hfin T hT y).2

end GlobalTheory.Dec.ProjCuspGap
end
end

module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeIntertwinerCoefficientAtPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralInverseAtSplitPlacesOfUnits
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceHomLatticeComponentsScaledIntegral
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesUnitaryDiagonalTranslate

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexHomLatticeInertMoveSource
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexHomLatticeInertMoveSource
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)

noncomputable section

namespace GlobalTheory.InertHomIdx

def rmul {L : Type} [Ring L] {m n : ℕ} (g : Matrix (Fin n) (Fin n) L) :
    Matrix (Fin m) (Fin n) L →+ Matrix (Fin m) (Fin n) L where
  toFun X := X * g
  map_zero' := Matrix.zero_mul g
  map_add' X Y := Matrix.add_mul X Y g

theorem rmul_apply {L : Type} [Ring L] {m n : ℕ} (g : Matrix (Fin n) (Fin n) L) (X : Matrix (Fin m) (Fin n) L) :
    rmul g X = X * g := rfl

end GlobalTheory.InertHomIdx


open GlobalTheory.FinWeilO in
theorem GlobalTheory.InertHomIdx.heisenbergRelativeIndex_inert_move_source (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (hi : IsInertAt D.host.F D.host.E v w) (g : Gv S v) : GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (embV S v g, 1))) = ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w)).relIndex (((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w)).map (GlobalTheory.InertHomIdx.rmul (locMat D.sp.cm.sig S.gram h g)⁻¹.1)) := by
  obtain ⟨ε, hns, hp⟩ := GlobalTheory.WeilAtPlace.exists_nonSplit_of_inert hi h
  have hε : IsPlaceIdem D v ε := hns.1
  have hη : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _, fun _ hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
  have hk : GlobalTheory.WeilParts.SuppPl ε S (embV S v g) := by
    rw [GlobalTheory.PlaceDatum.placeIdem_eq hε hη]
    exact GlobalTheory.PlaceTensor.suppPl_emb S v g
  have hg : GlobalTheory.WeilParts.SuppPl ε T (1 : GA D T) := fun i j => by rw [mt_one, sub_self]; simp
  have hoff := smul_actO (off_smul_mt_place hk) (off_smul_mt_place hg)
  have hmat : (mt S (embV S v g⁻¹)).map (GlobalTheory.InertHomIdx.compW D w) = (locMat D.sp.cm.sig S.gram h g)⁻¹.1 := by
    have e := finMat_map_compAt D.sp.cm.sig S.gram h (embV S v g⁻¹)
    rw [proj_emb_self] at e
    rw [← map_inv]
    exact e
  refine GlobalTheory.InertHomIdx.relIndex_map_of_proj (latF S T (frameLat S) (frameLat T)).toAddSubgroup
    (rhoF S T (embV S v g, 1)).toAddMonoidHom (mulF S T (algebraMap (AF D.host.F) (AE D) ε)).toAddMonoidHom
    (GlobalTheory.InertHomIdx.matW S T w) (GlobalTheory.InertHomIdx.rmul (locMat D.sp.cm.sig S.gram h g)⁻¹.1) ?_ ?_ ?_ ?_
  · intro x
    show (actO S T (embV S v g) 1 x).map (GlobalTheory.InertHomIdx.compW D w) = (x : WO S T).map (GlobalTheory.InertHomIdx.compW D w) * (locMat D.sp.cm.sig S.gram h g)⁻¹.1
    rw [actO, mt_one, Matrix.one_mul, ← map_inv, Matrix.map_mul, hmat]
  · intro x hx
    refine XF.ext (Matrix.ext fun i j => ?_)
    have h0 : GlobalTheory.InertHomIdx.compW D w ((x : WO S T) i j) = 0 := congrFun (congrFun hx i) j
    show algebraMap (AF D.host.F) (AE D) ε * (x : WO S T) i j = 0
    refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
    · rw [RingHom.map_mul, GlobalTheory.WeilAtPlace.isPrimeIdem_infPart hp, zero_mul, RingHom.map_zero]
    · rw [RingHom.map_mul, finPart_of_isPrimeIdem hp, singleAt_mul, RingHom.map_zero]
      have h1 : compAt D.host.F w (finPart D ((x : WO S T) i j)) = 0 := h0
      rw [h1, mul_zero, ← singleAt_zero]
  · intro a ha
    exact GlobalTheory.PlaceModel.latO_le_top _ (GlobalTheory.PlaceModel.placeIdem_smul_mem hε ha)
  · intro a _
    refine XF.ext ?_
    have := hoff (a : WO S T)
    rw [sub_smul, sub_smul, one_smul, one_smul] at this
    exact this

namespace GlobalTheory.InertHomLattice

theorem mem_map_latF_iff_frames (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hv : w.under (𝓞 D.host.F) = v) (hw : IsInertAt D.host.F D.host.E v w) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (hc : IsConjAt D.sp.cm.sig hv c) (a : GL (Fin T.rank) (w.adicCompletion D.host.E)) (ha : IsFrameAt w (frameLat T) a) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (haS : IsFrameAt w (frameLat S) aS) : ∃ (c₀ : w.adicCompletion D.host.E) (b : GL (Fin S.rank) (w.adicCompletion D.host.E)), c₀ ≠ 0 ∧ (b⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1 = Formalism.UG.cT c aS.1 * S.gram.map (algebraMap D.host.E (w.adicCompletion D.host.E)) ∧ ∀ X : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), X ∈ (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w) ↔ c₀ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * X * b.1) ∈ GlobalTheory.InertHomIdx.intMat (w.adicCompletion D.host.E) T.rank S.rank := by

  obtain ⟨a₀, ha₀, h0, hgen⟩ := exists_gen (D := D) w
  set π := algebraMap D.host.E (w.adicCompletion D.host.E) with hπ
  set G : Matrix (Fin S.rank) (Fin S.rank) (w.adicCompletion D.host.E) := S.gram.map π with hG
  set B : Matrix (Fin S.rank) (Fin S.rank) (w.adicCompletion D.host.E) := Formalism.UG.cT c aS.1 * G with hB
  have hBu : IsUnit B.det := by
    rw [hB, Matrix.det_mul, isUnit_iff_ne_zero]
    refine mul_ne_zero ?_ ?_
    · rw [Formalism.UG.cT, Matrix.det_transpose, show (aS.1.map c).det = c aS.1.det from (RingHom.map_det c aS.1).symm]
      exact (map_ne_zero c).2 (Matrix.det_ne_zero_of_left_inverse (B := (aS⁻¹).1) (by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]))
    · rw [hG, show (S.gram.map π).det = π S.gram.det from (RingHom.map_det π S.gram).symm]
      exact ((GlobalTheory.LatVac.gram_det_isUnit S).map π).ne_zero
  refine ⟨(π a₀)⁻¹, (Matrix.nonsingInvUnit B hBu)⁻¹, inv_ne_zero h0, by rw [inv_inv]; rfl, fun X => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.1 h
    rw [GlobalTheory.InertHomIdx.matW_apply]
    have hx' : (x : WO S T) ∈ latO S T (frameLat S) (frameLat T) fun _ => True := hx
    have hb : ((Matrix.nonsingInvUnit B hBu)⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1 = B⁻¹ := rfl
    let Φ : WO S T →+ Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) := AddMonoidHom.mk'
      (fun u => (π a₀)⁻¹ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *
        u.map (GlobalTheory.InertHomIdx.compW D w) * ((Matrix.nonsingInvUnit B hBu)⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1))
      fun u u' => by simp only [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add]
    suffices hle : latO S T (frameLat S) (frameLat T) (fun _ => True) ≤
        (GlobalTheory.InertHomIdx.intMat (w.adicCompletion D.host.E) T.rank S.rank).comap Φ from hle hx'
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, -, a1, ha1, s, hs, t, ht, rfl⟩
    set lam := GlobalTheory.AdeleBaseChange.locMap D.host.F w (α (w.under (𝓞 D.host.F))) with hlam
    have hlamO : lam ∈ Formalism.UG.Ov D.host.E w := GlobalTheory.AdeleBaseChange.locMap_int w _ (hα _)
    have hmap : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
        (a1 * t i * ∑ k, star (s k) * S.gram k j) : WO S T).map (GlobalTheory.InertHomIdx.compW D w) =
        (lam * π a1) • Matrix.vecMulVec (fun i => π (t i)) ((fun k => c (π (s k))) ᵥ* G) := by
      ext i j
      have e1 : GlobalTheory.InertHomIdx.compW D w (pairA D.host.F 0 α ⊗ₜ[D.host.F]
          (a1 * t i * ∑ k, star (s k) * S.gram k j)) =
          lam * π (a1 * t i * ∑ k, star (s k) * S.gram k j) := compAt_tmul w α _
      rw [Matrix.map_apply, Matrix.of_apply, e1, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
      have hconj : ∀ y, c (π y) = π (star y) := fun y => InertChart.conj_algebraMap hc y
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_mul, map_sum, Matrix.vecMul, dotProduct, hG, Matrix.map_apply, hconj]
      ring_nf
    have hy : ∀ p, ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ fun i => π (t i)) p ∈ Formalism.UG.Ov D.host.E w := by
      refine (ha _).2 ?_
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      exact Submodule.subset_span ⟨t, ht, rfl⟩
    set z := (aS⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1 *ᵥ fun k => π (s k) with hz
    have hzO : ∀ k, z k ∈ Formalism.UG.Ov D.host.E w := by
      refine (haS _).2 ?_
      rw [hz, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      exact Submodule.subset_span ⟨s, hs, rfl⟩
    have hsz : (fun k => π (s k)) = aS.1 *ᵥ z := by
      rw [hz, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have hcs : (fun k => c (π (s k))) = (fun k => c (z k)) ᵥ* Formalism.UG.cT c aS.1 := by
      funext k
      rw [Formalism.UG.cT, Matrix.vecMul_transpose, show c (π (s k)) = c ((fun k => π (s k)) k) from rfl, hsz]
      exact RingHom.map_mulVec c aS.1 z k
    have hr : ((fun k => c (π (s k))) ᵥ* G) ᵥ* ((Matrix.nonsingInvUnit B hBu)⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1 =
        fun k => c (z k) := by
      rw [hb, hcs, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← hB, Matrix.mul_nonsing_inv B hBu, Matrix.vecMul_one]
    intro p q
    show ((π a₀)⁻¹ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
        (a1 * t i * ∑ k, star (s k) * S.gram k j) : WO S T).map (GlobalTheory.InertHomIdx.compW D w) *
        ((Matrix.nonsingInvUnit B hBu)⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1 :
        Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E))) p q ∈ _
    rw [hmap, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_vecMulVec_mul_apply, hr]
    have h1 := hgen a1 ha1
    have h2 := InertChart.conj_mem hw hc (hzO q)
    rw [intL_iff, show (π a₀)⁻¹ * (lam * π a1 * (((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ fun i => π (t i)) p * c (z q))) =
      lam * ((π a₀)⁻¹ * π a1) * ((((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ fun i => π (t i)) p) * c (z q)) by ring]
    exact mul_mem (mul_mem hlamO h1) (mul_mem (hy p) h2)
  · set Y := (π a₀)⁻¹ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * X *
        ((Matrix.nonsingInvUnit B hBu)⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1) with hY
    have hb : ((Matrix.nonsingInvUnit B hBu)⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1 = B⁻¹ := rfl
    have hX : X = π a₀ • (a.1 * Y * B) := by
      rw [hY, hb, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ h0, one_smul]
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul B hBu, Matrix.mul_one, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.one_mul]
    have hsingle : ∀ {n : ℕ} (i : Fin n) (k : Fin n), (Pi.single i 1 : Fin n → w.adicCompletion D.host.E) k ∈ Formalism.UG.Ov D.host.E w := by
      intro n i k
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have htI : ∀ i, (fun k => singleAt D.host.F w (a.1 k i)) ∈ Formalism.L2.NTheta.LamHat T := fun i => by
      have := (ha (Pi.single i 1)).1 (hsingle i)
      rw [Matrix.mulVec_single_one] at this
      exact singleAt_mem_lamHat this
    have hsJ : ∀ j, (fun k => singleAt D.host.F w (aS.1 k j)) ∈ Formalism.L2.NTheta.LamHat S := fun j => by
      have := (haS (Pi.single j 1)).1 (hsingle j)
      rw [Matrix.mulVec_single_one] at this
      exact singleAt_mem_lamHat this
    have hu : (∑ i, ∑ j, GlobalTheory.LatticeStable.liftFin D (singleAt D.host.F w (Y i j)) •
        GlobalTheory.SplitHomLattice.rk S T a₀ (fun k => singleAt D.host.F w (aS.1 k j))
          (fun k => singleAt D.host.F w (a.1 k i)) : WO S T) ∈ latO S T (L0c D S) (L0c D T) fun _ => True :=
      sum_mem fun i _ => sum_mem fun j _ => GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _
        (by rw [GlobalTheory.SplitHomLattice.finPart_liftFin]; exact singleAt_mem_intAE (h i j)) _
        (GlobalTheory.SplitHomLattice.rk_mem S T ha₀ (hsJ j) (htI i))
    rw [hermitianSpaceBaseLattice_eq_frameLattice, hermitianSpaceBaseLattice_eq_frameLattice] at hu
    refine AddSubgroup.mem_map.2 ⟨GlobalTheory.FinWeilO.XF.mk _ (GlobalTheory.SplitScalar.latO_fin hu), hu, ?_⟩
    rw [GlobalTheory.InertHomIdx.matW_apply, GlobalTheory.FinWeilO.XF.coe_mk]
    exact (map_compW_sum S T hv hc a₀ Y a.1 aS.1).trans hX.symm

end GlobalTheory.InertHomLattice

namespace GlobalTheory.InertHomIdx

theorem relIndex_intMat_rmul_cT {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (c : L →+* L)
    (hcc : ∀ x, c (c x) = x) (hcv : ∀ x, Valued.v (c x) = Valued.v x) (m n : ℕ) (k : Matrix (Fin n) (Fin n) L) :
    (intMat L m n).relIndex ((intMat L m n).map (rmul (Formalism.UG.cT c k))) =
      (intMat L n m).relIndex ((intMat L n m).map (lmul k)) := by
  let ψ : Matrix (Fin m) (Fin n) L →+ Matrix (Fin n) (Fin m) L :=
    { toFun := fun Y => Formalism.UG.cT c Y
      map_zero' := by ext i j; simp [Formalism.UG.cT]
      map_add' := fun X Y => by ext i j; simp [Formalism.UG.cT] }
  have hψ : Function.Injective ψ := by
    intro X Y hXY
    ext i j
    have := congrFun (congrFun hXY j) i
    simp only [ψ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    have := congrArg c this
    rwa [hcc, hcc] at this
  have hint : ∀ x : L, c x ∈ Formalism.UG.intL L ↔ x ∈ Formalism.UG.intL L := fun x => by
    show Valued.v (c x) ≤ 1 ↔ Valued.v x ≤ 1
    rw [hcv]
  have h1 : ∀ {p r : ℕ}, (intMat L p r).map
      ({ toFun := fun Y => Formalism.UG.cT c Y
         map_zero' := by ext i j; simp [Formalism.UG.cT]
         map_add' := fun X Y => by ext i j; simp [Formalism.UG.cT] } : Matrix (Fin p) (Fin r) L →+ Matrix (Fin r) (Fin p) L) = intMat L r p := by
    intro p r
    ext Y
    constructor
    · rintro ⟨X, hX, rfl⟩ i j
      exact (hint _).2 (hX j i)
    · intro hY
      refine ⟨Formalism.UG.cT c Y, fun i j => (hint _).2 (hY j i), ?_⟩
      ext i j
      simp [Formalism.UG.cT, hcc]
  have hcomm : ψ.comp (rmul (Formalism.UG.cT c k)) = (lmul k).comp ψ := by
    refine AddMonoidHom.ext fun X => ?_
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ψ, AddMonoidHom.coe_comp, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply, rmul_apply, lmul_apply,
      Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul, hcc]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hψ, AddSubgroup.map_map, hcomm, ← AddSubgroup.map_map]
  exact congrArg₂ _ (h1) (congrArg _ h1)

end GlobalTheory.InertHomIdx

theorem GlobalTheory.InertHomIdx.idx_latF_map_rhoF_eq_qV_pow : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → ∀ c ϖ e, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c e → ∀ (d : Fin S.rank → ℤ) (t : GU c S.rank), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU c S.rank, ∀ k₂ ∈ KU c S.rank, GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (embV S v (e.symm (k₁ * t * k₂)), 1))) = qV D.host.E w ^ (T.rank * (∑ i, max (d i) 0).toNat) := by
  intro D S T v w h hw c ϖ e hU he d t ht k₁ hk₁ k₂ hk₂
  obtain ⟨hc, ⟨a, ha, haJ, hea⟩, -⟩ := he
  have hlat := GlobalTheory.HeckeDual.isLattice_frameLat T
  have hspan : Submodule.span D.host.E (frameLat T : Set (Fin T.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (T.L0 : Set T.V) = ⊤ := by
      let W := Submodule.span D.host.E (T.L0 : Set T.V)
      change W = ⊤
      by_contra h
      let e : T.V ≃ₗ⋆[D.host.E] T.V :=
        (T.frame.equivFun.trans (starLinearEquiv D.host.E)).trans T.frame.equivFun.symm
      let g : T.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (T.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E T.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ T.L0 := by
        rw [← T.baseLattice_isUnimodular]
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hxy : T.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hyx : T.hT y (e x) = 0 := by
          rw [(T.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] T.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict T.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) T.L0 := Module.Finite.iff_fg.mpr T.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have heq : (frameLat T : Set (Fin T.rank → D.host.E)) =
        T.frame.equivFun.toLinearMap '' (T.L0 : Set T.V) :=
      (T.frame.equivFun.toEquiv.image_eq_preimage_symm _).symm
    rw [heq, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  obtain ⟨aT, haT⟩ := InertChart.exists_isFrameAt (L := frameLat T) hw hlat.fg hspan
  obtain ⟨c₀, b, hc₀, hb, hX⟩ := GlobalTheory.InertHomLattice.mem_map_latF_iff_frames D S T v w h hw c hc aT haT a ha
  rw [GlobalTheory.InertHomIdx.heisenbergRelativeIndex_inert_move_source D S T v w h hw]
  set k : GU c S.rank := k₁ * t * k₂ with hk
  have hg : locMat D.sp.cm.sig S.gram h (e.symm k) = a * (k : GL (Fin S.rank) (w.adicCompletion D.host.E)) * a⁻¹ := by
    have h1 := hea (e.symm k)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [h1]
    group
  have hQ : ((b⁻¹ * a * (k : GL (Fin S.rank) (w.adicCompletion D.host.E))⁻¹ * a⁻¹ * b : GL (Fin S.rank) (w.adicCompletion D.host.E))).1 =
      Formalism.UG.cT c k.1.1 := by
    set u : GL (Fin S.rank) (w.adicCompletion D.host.E) := b⁻¹ * a with hu
    have hu1 : u.1 = Formalism.UG.antiJ (w.adicCompletion D.host.E) S.rank := by
      rw [hu, Units.val_mul, hb, haJ]
    have hkU : Formalism.UG.cT c k.1.1 * Formalism.UG.antiJ (w.adicCompletion D.host.E) S.rank * k.1.1 = Formalism.UG.antiJ (w.adicCompletion D.host.E) S.rank := k.2
    have e1 : b⁻¹ * a * (k : GL (Fin S.rank) (w.adicCompletion D.host.E))⁻¹ * a⁻¹ * b = u * (k : GL (Fin S.rank) (w.adicCompletion D.host.E))⁻¹ * u⁻¹ := by
      rw [hu]; group
    rw [e1]
    calc (u * (k : GL (Fin S.rank) (w.adicCompletion D.host.E))⁻¹ * u⁻¹).1
        = (Formalism.UG.cT c k.1.1 * u.1 * k.1.1) * (((k : GL (Fin S.rank) (w.adicCompletion D.host.E))⁻¹ * u⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E))).1 := by
          rw [hu1, hkU, ← hu1, ← Units.val_mul, mul_assoc]
      _ = Formalism.UG.cT c k.1.1 := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel_left, mul_inv_cancel,
            Units.val_one, Matrix.mul_one]
  set M := (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w) with hM
  clear_value M
  let τ : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) →+ Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) :=
    { toFun := fun X => c₀ • ((aT⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * X * b.1)
      map_zero' := by simp
      map_add' := fun X Y => by simp [Matrix.mul_add, Matrix.add_mul, smul_add] }
  have hτ : Function.Injective τ := by
    intro X Y hXY
    have h1 : c₀ • ((aT⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * X * b.1) = c₀ • ((aT⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * Y * b.1) := hXY
    have h2 := congrArg (fun Z => c₀⁻¹ • (aT.1 * Z * (b⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1)) h1
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hc₀, one_smul] at h2
    simpa [← Matrix.mul_assoc, Matrix.mul_assoc _ _ (b⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1] using h2
  have h1 : M.map τ = GlobalTheory.InertHomIdx.intMat (w.adicCompletion D.host.E) T.rank S.rank := by
    ext Y
    constructor
    · rintro ⟨X, hX', rfl⟩
      exact (hX X).1 hX'
    · intro hY
      refine ⟨c₀⁻¹ • (aT.1 * Y * (b⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1), (hX _).2 ?_, ?_⟩
      · show c₀ • ((aT⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * (c₀⁻¹ • (aT.1 * Y * (b⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1)) * b.1) ∈ _
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc₀, one_smul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
        exact hY
      · show c₀ • ((aT⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * (c₀⁻¹ • (aT.1 * Y * (b⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1)) * b.1) = Y
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc₀, one_smul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
        rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have h2 : (M.map (GlobalTheory.InertHomIdx.rmul (locMat D.sp.cm.sig S.gram h (e.symm k))⁻¹.1)).map τ =
      (GlobalTheory.InertHomIdx.intMat (w.adicCompletion D.host.E) T.rank S.rank).map (GlobalTheory.InertHomIdx.rmul (Formalism.UG.cT c k.1.1)) := by
    have hcomm : τ.comp (GlobalTheory.InertHomIdx.rmul (locMat D.sp.cm.sig S.gram h (e.symm k))⁻¹.1) =
        (GlobalTheory.InertHomIdx.rmul (Formalism.UG.cT c k.1.1)).comp τ := by
      refine AddMonoidHom.ext fun X => ?_
      show c₀ • ((aT⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * (X * (locMat D.sp.cm.sig S.gram h (e.symm k))⁻¹.1) * b.1) = (c₀ • ((aT⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * X * b.1)) * Formalism.UG.cT c k.1.1
      rw [← hQ, Matrix.smul_mul]
      congr 1
      have e2 : (locMat D.sp.cm.sig S.gram h (e.symm k))⁻¹ * b =
          b * (b⁻¹ * a * (k : GL (Fin S.rank) (w.adicCompletion D.host.E))⁻¹ * a⁻¹ * b) := by
        rw [hg]; group
      rw [Matrix.mul_assoc, Matrix.mul_assoc X, ← Units.val_mul, e2, Units.val_mul]
      simp only [Matrix.mul_assoc]
    rw [← h1, AddSubgroup.map_map, AddSubgroup.map_map, hcomm]
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hτ, h2, h1,
    GlobalTheory.InertHomIdx.relIndex_intMat_rmul_cT c hU.1 hU.2.1 T.rank S.rank k.1.1, hk,
    GlobalTheory.LatIdx.relIndex_intMat_translate ϖ c _ hU S.rank T.rank d t ht k₁ hk₁ k₂ hk₂]
  congr 1
  show (Ideal.absNorm v.asIdeal) ^ 2 = Ideal.absNorm w.asIdeal
  rw [GlobalTheory.LFun.InertChart.absNorm_eq (Algebra.IsQuadraticExtension.finrank_eq_two _ _) hw]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexHomLatticeInertMoveSourceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_homLattice_inert_move_source : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → ∀ c ϖ e, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c e → ∀ (d : Fin S.rank → ℤ) (t : GU c S.rank), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU c S.rank, ∀ k₂ ∈ KU c S.rank, GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (embV S v (e.symm (k₁ * t * k₂)), 1))) = qV D.host.E w ^ (T.rank * (∑ i, max (d i) 0).toNat) := by
  first | exact @GlobalTheory.InertHomIdx.idx_latF_map_rhoF_eq_qV_pow | exact GlobalTheory.InertHomIdx.idx_latF_map_rhoF_eq_qV_pow | (intros; apply GlobalTheory.InertHomIdx.idx_latF_map_rhoF_eq_qV_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumSourceInertPlaceEqLatticeIntertwiner
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumSourceInertPlaceEqLatticeIntertwiner
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAtPlaceSrc

open GlobalTheory.WeilAtPlace GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {lam : ℕ →* ℂ} {w₀ : 𝓞 D.host.E} {Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)}

theorem weilDatum_source_eq_scalar_smul_latticeIntertwiner (hψ : IsStdChar D ψ (-1)) (hW : IsWeilDatumO ψ S T χS χT om) (hL : IsLatRep hψ.1 ΛS ΛT w₀ lam Om)
    (hlam : GoodNorm (sgO D) lam) {g : GA D S} (hg : g ∈ GfC S) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f (hf : IsThetaFunO ψ S T f), om (g, 1) f = c • (Om (g, 1) ⟨f, hf⟩ : WO S T → ℂ) := by
  obtain ⟨o, ho⟩ := exists_extend (thetaSub ψ S T) Om
  have ho' : ∀ p f (hf : IsThetaFunO ψ S T f), o p f = (Om p ⟨f, hf⟩ : WO S T → ℂ) := fun p f hf => ho p ⟨f, hf⟩
  have hpres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (o p f) := fun p f hf => by
    rw [ho' p f hf]
    exact (Om p ⟨f, hf⟩).2
  have hheis : ∀ (g' : GA D S) (k' : GA D T), g' ∈ GfC S → k' ∈ GfC T → ∀ u f, IsThetaFunO ψ S T f →
      o (g', k') (heisO ψ S T u f) = heisO ψ S T (actO S T g' k' u) (o (g', k') f) := by
    intro g' k' hg' hk' u f hf
    obtain ⟨f', h1, h2⟩ := hL.Heisenberg₂ hψ hg' hk' u ⟨f, hf⟩
    rw [ho' _ f hf, ← h2, ← h1]
    exact ho _ f'
  obtain ⟨c, hc, h⟩ := GlobalTheory.ThetaSchur.schur D ψ hψ S T (om (g, 1) * o (g⁻¹, 1⁻¹))
    (fun f hf => hW.om_pres _ _ (hpres _ _ hf))
    (fun u f hf => by
      rw [Module.End.mul_apply, Module.End.mul_apply, hheis _ _ (inv_mem hg) (inv_mem (one_mem _)) u f hf,
        hW.om_heis _ _ _ _ (hpres _ _ hf), GlobalTheory.FinWeilForm.actO_actO_inv])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, hW.om_unit μ 𝓕 hμ h𝓕 _ _ (hpres _ _ hf), ho' _ f hf,
        hL.unit hlam μ 𝓕 hμ h𝓕 _ ⟨f, hf⟩])
  refine ⟨c, hc, fun f hf => ?_⟩
  have h1 := h _ (hpres (g, 1) f hf)
  rw [Module.End.mul_apply, ← Module.End.mul_apply (o _), ← map_mul,
    show ((g⁻¹, 1⁻¹) * (g, 1) : GA D S × GA D T) = 1 from inv_mul_cancel (g, (1 : GA D T)), map_one,
    Module.End.one_apply] at h1
  rw [h1, ho' _ f hf]

theorem exists_weilScalarCharacter_sourceFinitePart (hψ : IsStdChar D ψ (-1)) (hW : IsWeilDatumO ψ S T χS χT om) (hL : IsLatRep hψ.1 ΛS ΛT w₀ lam Om)
    (hlam : GoodNorm (sgO D) lam) :
    ∃ ν : GA D S →* Circle, ∀ g ∈ GfC S, ∀ f (hf : IsThetaFunO ψ S T f),
      om (g, 1) f = (ν g : ℂ) • (Om (g, 1) ⟨f, hf⟩ : WO S T → ℂ) := by
  have hs := fun g : GA D S => weilDatum_source_eq_scalar_smul_latticeIntertwiner hψ hW hL hlam (pFin_mem S g)
  choose c hc h using hs
  obtain ⟨f, f0, hf⟩ := GlobalTheory.FinWeilForm.exists_theta hψ S T
  have hne : ∀ p, (Om p ⟨f, hf⟩ : WO S T → ℂ) ≠ 0 := fun p h0 => f0 (by
    have h1 : Om p ⟨f, hf⟩ = 0 := Subtype.ext h0
    have h2 := congrArg (Om p⁻¹) h1
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at h2
    exact congrArg Subtype.val h2)
  refine ⟨MonoidHom.mk' (fun g => ⟨c g, mem_sphere_zero_iff_norm.2 (hc g)⟩) fun p q => Circle.ext ?_,
    fun g hg f hf => ?_⟩
  · show c (p * q) = c p * c q
    have e1 : (pFin S (p * q), (1 : GA D T)) = (pFin S p, 1) * (pFin S q, 1) :=
      Prod.ext (map_mul _ _ _) (one_mul _).symm
    have e2 := h (p * q) f hf
    rw [e1, map_mul, Module.End.mul_apply, h q f hf, map_smul, h p _ (Om (pFin S q, 1) ⟨f, hf⟩).2, smul_smul, map_mul,
      Module.End.mul_apply] at e2
    have e3 := smul_left_injective ℂ (hne ((pFin S p, 1) * (pFin S q, 1))) (a₁ := c q * c p) (a₂ := c (p * q)) (by
      simpa only [map_mul, Module.End.mul_apply] using e2)
    rw [← e3, mul_comm]
  · have e := h g f hf
    rwa [pFin_of_mem hg] at e

theorem weilScalar_source_eq_one_nonsplit_unramified (hψ : IsStdChar D ψ (-1)) (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) (hL : IsLatRep hψ.1 ΛS ΛT w₀ lam Om) {ν : GA D S →* Circle}
    (hν : ∀ g ∈ GfC S, ∀ f (hf : IsThetaFunO ψ S T f), om (g, 1) f = (ν g : ℂ) • (Om (g, 1) ⟨f, hf⟩ : WO S T → ℂ))
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hv : NonSplitAt D v ε) (uS : UnramAt ε χS)
    (uT : UnramAt ε χT) {g : GA D S} (hg : SuppPl ε S g) : ν g = 1 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  refine GlobalTheory.T.adelic_unitary_character_trivial_at_nonsplit_place D S ΛS hS v ε hv ν (fun k hk hst => ?_) g hg
  have hvac' : ∃ f, f ≠ 0 ∧ IsThetaFunO ψ S T f ∧ ∀ v η, NonSplitAt D v η →
      ∀ u ∈ (latO S T ΛS ΛT fun w => w = v), heisO ψ S T u f = f := by
    obtain ⟨f, f0, hf⟩ := GlobalTheory.FinWeilForm.exists_theta hψ S T
    obtain ⟨e, he, e0⟩ : ∃ e, Fixes (opF hψ.1 S T w₀) (latF S T ΛS ΛT) e ∧ e ≠ 0 := by
      by_contra hn
      push_neg at hn
      have : (⊤ : Submodule ℂ (thetaSub ψ S T)) ≤ ⊥ := by
        rw [← hL.span, Submodule.span_le]
        rintro _ ⟨x, e, he, rfl⟩
        rw [hn e he, map_zero]
        exact zero_mem _
      exact f0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 (this (Submodule.mem_top (x := ⟨f, hf⟩)))))
    refine ⟨e, fun h0 => e0 (Subtype.ext h0), e.2, fun v η hv u hu => ?_⟩
    obtain ⟨b, hb, hb'⟩ := exists_half_of_nonSplit hv
    have hu' := GlobalTheory.PlaceModel.latO_le_top _ hu
    let a : XF S T := XF.mk u (GlobalTheory.SplitScalar.latO_fin hu')
    have ha : a ∈ latF S T ΛS ΛT := hu'
    have e0 : algebraMap (AF D.host.F) (AE D) η • u = u :=
      GlobalTheory.FinWeilForm.placeIdem_smul_self hv.1 hu
    have e1 : a = 2 • (b • a) := by
      rw [two_nsmul, ← add_smul, ← two_mul, hb']
      exact XF.ext e0.symm
    have e2 : b • a ∈ latF S T ΛS ΛT := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ b hb _ ha
    have h1 := congrArg Subtype.val (he a ha)
    rw [coe_opF] at h1
    have h2 : phase ψ w₀ a = 1 := by rw [e1]; exact phase_two hL.sd w₀ e2
    rwa [h2, one_smul] at h1
  obtain ⟨f₀, f0, hf₀, hvac⟩ := hvac'
  have hfix := hvac v ε hv
  have hst' := GlobalTheory.T.mem_localHomLattice_of_keeps_completedLattices D S T ΛS ΛT hS hT v ε hv.1 k 1 hst
    (fun y => by rw [GlobalTheory.FinWeilForm.finMat_one, Matrix.one_mulVec])
  have s1 : SuppPl ε T (1 : GA D T) := fun i j => by
    rw [GlobalTheory.FinWeilO.mt_one, sub_self, Matrix.zero_apply, mul_zero]
  have a := GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hψ S T ΛS ΛT hS hT χS χT om
    ((GlobalTheory.Mem.EtaTilde.exists_etaTilde D).imp fun _ h => ⟨h.1, h.2.2.2, h.2.2.1, h.2.1⟩) hW v ε hv uS uT k 1 hk s1 hst'
    f₀ hf₀ hfix
  have b := hL.inert hv hk s1 (fun u hu => (hst' u).1 hu) ⟨f₀, hf₀⟩ hfix
  have hkf : k ∈ GfC S := GlobalTheory.IdemSupport.mem_GfC_of_suppF S (GlobalTheory.IdemSupport.place_comp hΦ hv.1).1 hk
  have c := hν k hkf f₀ hf₀
  rw [a, b] at c
  exact Circle.ext (smul_left_injective ℂ f0 (c.symm.trans (one_smul ℂ f₀).symm))

end GlobalTheory.WeilAtPlaceSrc

end

theorem GlobalTheory.WeilAtPlaceSrc.weilDatum_src_inert : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (hψ : IsStdChar D ψ (-1)) (lam : ℕ →* ℂ) (w₀ : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)), GlobalTheory.FinWeilO.IsLatRep hψ.1 (frameLat S) (frameLat T) w₀ lam Om → GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ (a : Gv S v) (f : GlobalTheory.FinWeilO.thetaSub ψ S T), om (embV S v a, 1) f = (Om (embV S v a, 1) f : WO S T → ℂ) := by
  intro D ψ S T χS χT om hW hψ lam w₀ Om hL hlam v w h hi uS uT a f
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨ν, hν⟩ := GlobalTheory.WeilAtPlaceSrc.exists_weilScalarCharacter_sourceFinitePart hψ hW hL hlam
  obtain ⟨ε, hns, hp⟩ := GlobalTheory.WeilAtPlace.exists_nonSplit_of_inert hi h
  have hsu : GlobalTheory.WeilParts.SuppPl ε S (embV S v a) := (Supp.suppF_iff_of_isPrimeIdem S hp h _).2 ⟨a, rfl⟩
  have hk : embV S v a ∈ GfC S :=
    GlobalTheory.IdemSupport.mem_GfC_of_suppF S (GlobalTheory.IdemSupport.place_comp hΦ hns.1).1 hsu
  have e1 := GlobalTheory.WeilAtPlaceSrc.weilScalar_source_eq_one_nonsplit_unramified hψ hW (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat S)
    (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat T) hL hν hns
    (GlobalTheory.WeilAtPlace.unramAt_of_unrAt hp uS) (GlobalTheory.WeilAtPlace.unramAt_of_unrAt hp uT) hsu
  have e2 := hν _ hk f.1 f.2
  rw [e1, Circle.coe_one, one_smul] at e2
  exact e2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumSourceInertPlaceEqLatticeIntertwinerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_source_inertPlace_eq_latticeIntertwiner : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (hψ : IsStdChar D ψ (-1)) (lam : ℕ →* ℂ) (w₀ : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)), GlobalTheory.FinWeilO.IsLatRep hψ.1 (frameLat S) (frameLat T) w₀ lam Om → GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ (a : Gv S v) (f : GlobalTheory.FinWeilO.thetaSub ψ S T), om (embV S v a, 1) f = (Om (embV S v a, 1) f : WO S T → ℂ) := by
  first | exact @GlobalTheory.WeilAtPlaceSrc.weilDatum_src_inert | exact GlobalTheory.WeilAtPlaceSrc.weilDatum_src_inert | (intros; apply GlobalTheory.WeilAtPlaceSrc.weilDatum_src_inert <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumMatrixCoefficientSourceInertPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section


open GlobalTheory.SplitScalar GlobalTheory.FinWeil GlobalTheory.WeilParts GlobalTheory.FinWeilO GlobalTheory.LatCoef in
theorem GlobalTheory.VacSource.latticeIntertwiner_coefficient_vacua_source : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (hψ : IsStdChar D ψ (-1)) (lam : ℕ →* ℂ) (w₀ : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)), GlobalTheory.FinWeilO.IsLatRep hψ.1 (frameLat S) (frameLat T) w₀ lam Om → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (a : Gv S v) (f₁ f₂ : GlobalTheory.FinWeilO.thetaSub ψ S T), VacFin ψ S T v f₁ → VacFin ψ S T v f₂ → Lift.pet μ 𝓕 (Om (embV S v a, 1) f₁ : WO S T → ℂ) f₂ = (lam (GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (embV S v a, 1)))))⁻¹ * Lift.pet μ 𝓕 (f₁ : WO S T → ℂ) f₂ := by
  intro D ψ S T hψ lam w₀ Om h μ 𝓕 hμ v a f₁ f₂ h₁ h₂
  obtain ⟨η, hηdef⟩ : ∃ η : AF D.host.F, η = pairA D.host.F 0 (singleV D.host.F v 1) := ⟨_, rfl⟩
  have hε : IsPlaceIdem D v η := hηdef ▸
    ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _, fun _ hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
  have hg : SuppPl η S (embV S v a) := hηdef ▸ GlobalTheory.PlaceTensor.suppPl_emb S v a
  have hk : SuppPl η T (1 : GA D T) := fun i j => by rw [mt_one, sub_self]; simp
  have hoff := smul_actO (off_smul_mt_place hg) (off_smul_mt_place hk)
  have H := isHeis_opF hψ.1 S T h.hw
  have hphase : ∀ x : XF S T, phase ψ w₀ x * (starRingEnd ℂ) (phase ψ w₀ x) = 1 := fun x => by
    rw [Complex.mul_conj', show ‖phase ψ w₀ x‖ = 1 from hψ.1.2.1 _]; simp
  have laws := fun g : thetaSub ψ S T => GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ g f₂ g.2 f₂.2
  let ℓ : thetaSub ψ S T →ₗ[ℂ] ℂ :=
    { toFun := fun g => GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 (g : WO S T → ℂ) f₂
      map_add' := fun g g' => ((laws g).2.2.2.1 g' g'.2).1
      map_smul' := fun c g => ((laws g).2.2.1 c).1 }
  have hℓ : ∀ a' ∈ latF S T (frameLat S) (frameLat T), ∀ g,
      ℓ (opF hψ.1 S T w₀ (mulF S T (algebraMap (AF D.host.F) (AE D) η) a') g) = ℓ g := by
    intro a' ha' g
    obtain ⟨x, hx⟩ : ∃ x, x = mulF S T (algebraMap (AF D.host.F) (AE D) η) a' := ⟨_, rfl⟩
    have hfix := opF_mulF_fix h hε h₂.2 ha'
    rw [← hx] at hfix ⊢
    have hg' := GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 x.fin g.2
    have hf' := GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 x.fin f₂.2
    have l2' := GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ _ _ hg' hf'
    have l3 := GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ _ _ ((thetaSub ψ S T).smul_mem (phase ψ w₀ x) hg') hf'
    show GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 (opF hψ.1 S T w₀ x g : WO S T → ℂ) f₂ = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 (g : WO S T → ℂ) f₂
    conv_lhs => rw [← hfix]
    rw [coe_opF, coe_opF, (l3.2.2.1 (phase ψ w₀ x)).2, (l2'.2.2.1 (phase ψ w₀ x)).1,
      ((GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ g f₂ g.2 f₂.2).2.2.2.2.2.2.1 x).1, ← mul_assoc, mul_comm (starRingEnd ℂ _),
      hphase, one_mul]
  have hm : ∀ a' ∈ latF S T (frameLat S) (frameLat T),
      opF hψ.1 S T w₀ (mulF S T (algebraMap (AF D.host.F) (AE D) η) a') f₁ = f₁ := fun a' ha' =>
    opF_mulF_fix h hε h₁.2 ha'
  exact coef_of_local_vacuum H lam _ h.sd h.span (rhoF S T (embV S v a, 1)) (h.sd' _) (h.fin _) (Om (embV S v a, 1)) (h.op _)
    (h.vac _) (mulF S T (algebraMap (AF D.host.F) (AE D) η))
    (fun x y => by rw [gamF, gamF, coe_mulF, coe_mulF, symplO_smul, cA_algebraMap])
    (fun a' ha' => GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_placeIdem hε) _ ha')
    (fun x => XF.ext (by
      rw [coe_mulF, coe_mulF, smul_smul, ← map_mul, placeIdem_mul_self hε]))
    (fun x => XF.ext (by
      have e1 : ((x - mulF S T (algebraMap (AF D.host.F) (AE D) η) x : XF S T) : WO S T) =
          (1 - algebraMap (AF D.host.F) (AE D) η) • (x : WO S T) := by
        rw [sub_smul, one_smul]; rfl
      rw [coe_rhoF, e1, actO_smul, hoff]))
    (fun x => XF.ext (actO_smul _ _ _ _)) ℓ hℓ f₁ hm

namespace GlobalTheory.VacSource

theorem isSelfDualC_frameLat {D : D7} (V : HSp D) : IsSelfDualC V (frameLat V) := by
  have h : frameLat V = GlobalTheory.PlaceModel.latFrame V :=
    Submodule.ext fun y => (mem_frameLat V y).trans (GlobalTheory.PlaceModel.mem_latFrame V y).symm
  rw [h]
  exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem inv_neg_pow_mul (x : ℂ) (N M : ℕ) :
    ((-x) ^ (N * M))⁻¹ = ((((-1 : ℂˣ) ^ N : ℂˣ) : ℂ) * (x ^ N)⁻¹) ^ (M : ℤ) := by
  rw [zpow_natCast, pow_mul, ← inv_pow, neg_pow, mul_inv, ← inv_pow (-1 : ℂ), inv_neg_one]
  push_cast
  rfl

theorem vacuum_matrixCoefficient_source_inert_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ c ϖ e, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c e → ∃ φ : GU c S.rank → ℂ, KerU ϖ (qV D.host.F v) T.rank ((-1) ^ T.rank) φ ∧ ∀ (g : GU c S.rank) (f₁ f₂ : WO S T → ℂ), VacFin ψ S T v f₁ → VacFin ψ S T v f₂ → Lift.pet μ 𝓕 (om (embV S v (e.symm g), 1) f₁) f₂ = φ g * Lift.pet μ 𝓕 f₁ f₂ := by
  intro D ψ S T χS χT om hom μ 𝓕 hμ v w h hw uS uT c ϖ e hU he
  classical
  obtain ⟨lam, hlam, hsq⟩ := GlobalTheory.FinWeil.exists_goodNorm D
  obtain ⟨w₀, Om, hL⟩ := GlobalTheory.FinWeilO.exists_isLatRep hom.std (isSelfDualC_frameLat S) (isSelfDualC_frameLat T) hlam
  refine ⟨fun g => (lam (GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T))
    ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (embV S v (e.symm g), 1)))))⁻¹,
    fun d t ht k₁ hk₁ k₂ hk₂ => ?_, fun g f₁ f₂ h₁ h₂ => ?_⟩
  · show (lam _)⁻¹ = _
    rw [GlobalTheory.T.relIndex_homLattice_inert_move_source D S T v w h hw c ϖ e hU he d t ht k₁ hk₁ k₂ hk₂, map_pow, GlobalTheory.LamInert.lam_qV_inert D lam hlam v w hw]
    have hs0 : 0 ≤ ∑ i, max (d i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
    rw [← Int.toNat_of_nonneg hs0, zpow_natCast]
    generalize (∑ i, max (d i) 0).toNat = M
    exact inv_neg_pow_mul _ _ _
  · let g₁ : GlobalTheory.FinWeilO.thetaSub ψ S T := ⟨f₁, h₁.1⟩
    let g₂ : GlobalTheory.FinWeilO.thetaSub ψ S T := ⟨f₂, h₂.1⟩
    have hn := GlobalTheory.T.weilDatum_source_inertPlace_eq_latticeIntertwiner D ψ S T χS χT om hom hom.std lam w₀ Om hL hlam v w h hw uS uT (e.symm g) g₁
    have hc := GlobalTheory.VacSource.latticeIntertwiner_coefficient_vacua_source D ψ S T hom.std lam w₀ Om hL μ 𝓕 hμ v (e.symm g) g₁ g₂ h₁ h₂
    show Lift.pet μ 𝓕 (om (embV S v (e.symm g), 1) (g₁ : WO S T → ℂ)) (g₂ : WO S T → ℂ) = _ * Lift.pet μ 𝓕 (g₁ : WO S T → ℂ) (g₂ : WO S T → ℂ)
    rw [hn, hc]

end GlobalTheory.VacSource

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumMatrixCoefficientSourceInertPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_matrixCoefficient_source_inert_place_alt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ c ϖ e, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c e → ∃ φ : GU c S.rank → ℂ, KerU ϖ (qV D.host.F v) T.rank ((-1) ^ T.rank) φ ∧ ∀ (g : GU c S.rank) (f₁ f₂ : WO S T → ℂ), VacFin ψ S T v f₁ → VacFin ψ S T v f₂ → Lift.pet μ 𝓕 (om (embV S v (e.symm g), 1) f₁) f₂ = φ g * Lift.pet μ 𝓕 f₁ f₂ := by
  first | exact @GlobalTheory.VacSource.vacuum_matrixCoefficient_source_inert_place | exact GlobalTheory.VacSource.vacuum_matrixCoefficient_source_inert_place | (intros; apply GlobalTheory.VacSource.vacuum_matrixCoefficient_source_inert_place <;> assumption)
end

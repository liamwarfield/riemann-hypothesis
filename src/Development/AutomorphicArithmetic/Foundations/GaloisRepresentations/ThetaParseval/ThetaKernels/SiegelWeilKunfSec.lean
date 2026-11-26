module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IsClosedSiegelStabiliser
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Em0Injective
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.OmSch
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.SySmulRight
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinOneMulEqZeroIff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.MeromorphicOnOfWeak
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocDerBig
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylTheta.TWeylOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.ExistsLth
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseHgtFin

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfSec
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfSecA
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries.BRoad
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.kunf.SecA
attribute [local instance] GlobalTheory.ThK.Dbl.St.ae_ring GlobalTheory.ThK.Dbl.St.ae_t2 GlobalTheory.ThK.Dbl.St.ae_smul
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
theorem isCompact_stdK'_k (B : Base F E) (Y : Spc F E n) (hB : _root_.UpperTheory.TP.W.GoodK σ B) (b : GL (Fin n ⊕ Fin n) E)
    (K : Subgroup (G2 σ Y)) (hK : IsStdK (σ := σ) (Y := Y) B b K) : IsCompact (K : Set (G2 σ Y)) := by
  obtain ⟨Φ, hΦ, eΦ⟩ := GlobalTheory.ThK.Dbl.St.exists_section hB.cm B.emb
  have hI : IsCompact (intHat F E : Set (AE F E)) := isCompact_intHat
  have hfe : finOne F = GlobalTheory.ThK.Dbl.St.eF F := rfl
  set T : Set (AE F E) := Φ '' Set.univ.pi (fun _ => Metric.closedBall (0 : ℂ) 1) + (intHat F E : Set (AE F E))
    with hTdef
  have hT : IsCompact T := ((isCompact_univ_pi fun _ => isCompact_closedBall _ _).image hΦ).add hI
  have hentry : ∀ k ∈ K, ∀ i j, inFrame b k i j ∈ T := by
    intro k hk i j
    obtain ⟨h1, h2⟩ := (hK k).1 hk
    rw [eΦ (inFrame b k i j)]
    refine Set.add_mem_add ⟨_, fun w _ => ?_, rfl⟩ ?_
    · rw [mem_closedBall_zero_iff]
      have hu : (inFrame b k).map (piInf (B.emb w)) ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ :=
        Matrix.mem_unitaryGroup_iff.2 (by rw [Matrix.star_eq_conjTranspose]; exact h1 w)
      exact entry_norm_bound_of_unitary hu i j
    · rw [← hfe]
      exact h2 k (Set.mem_insert _ _) i j
  set S : Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :=
    (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) => incM F b.1 * M * incM F (b⁻¹).1) '' Set.univ.pi (fun _ => Set.univ.pi fun _ => T) with hSdef
  have hS : IsCompact S :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hT).image
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
  have hmat : ∀ k ∈ K, mat2 k ∈ S := fun k hk => ⟨inFrame b k, fun i _ j _ => hentry k hk i j, by
    show incM F b.1 * (incM F (b⁻¹).1 * mat2 k * incM F b.1) * incM F (b⁻¹).1 = mat2 k
    simp only [Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv, Matrix.one_mul]⟩
  have hp : ∀ w, Continuous (piInf (B.emb w)) := fun w => GlobalTheory.Grow.continuous_infEmb_compInf F w (B.emb w)
  have hIc := hI.isClosed
  have hfr := GlobalTheory.EisBL.DoubledParabolic.continuous_inFrame (σ := σ) (Y := Y) b
  have hKset : (K : Set (G2 σ Y)) =
      (⋂ w, {k | (inFrame b k).map (piInf (B.emb w)) * ((inFrame b k).map (piInf (B.emb w)))ᴴ = 1}) ∩
        ((⋂ i, ⋂ j, {k : G2 σ Y | finOne F • inFrame b k i j ∈ intHat F E}) ∩
          (⋂ i, ⋂ j, {k : G2 σ Y | finOne F • inFrame b k⁻¹ i j ∈ intHat F E})) := by
    ext k
    simp only [SetLike.mem_coe, hK k, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.forall_mem_insert,
      Set.mem_singleton_iff, forall_eq]
  have hKc : IsClosed (K : Set (G2 σ Y)) := by
    rw [hKset]
    refine (isClosed_iInter fun w => isClosed_eq ?_ continuous_const).inter
      ((isClosed_iInter fun i => isClosed_iInter fun j => hIc.preimage ?_).inter
        (isClosed_iInter fun i => isClosed_iInter fun j => hIc.preimage ?_))
    · exact (hfr.matrix_map (hp w)).matrix_mul (hfr.matrix_map (hp w)).matrix_conjTranspose
    · exact (hfr.matrix_elem i j).const_smul (finOne F)
    · exact ((hfr.comp continuous_inv).matrix_elem i j).const_smul (finOne F)
  exact GlobalTheory.ThK.Dbl.St.isCompact_of_units (UG (cA σ) (dbl (incM F Y.J))) (GlobalTheory.EisBL.DoubledGroupTopology.isClosed_doubled_group σ Y) K hKc S hS
    fun k hk => ⟨hmat k hk, hmat k⁻¹ (K.inv_mem hk)⟩
variable {Y : Spc F E n}
end PositivityTheory.SiegelWeilFormula.kunf.SecA
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.kunf
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem a_pos_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) : 0 < d.a x := by
  obtain ⟨p, t, hp, k, hk, rfl⟩ := d.ok.hgt.iwa x
  rw [d.ok.hgt.val p t hp k hk]
  exact absE_pos _
theorem ht_eq_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) : ((d.Ht x : ℝ) : ℂ) = (d.a x : ℂ) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht]
  rw [Real.coe_toNNReal _ (_root_.PositivityTheory.SiegelWeilFormula.kunf.a_pos_k d x).le]
theorem isCompact_K_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsCompact (d.K : Set d.G) :=
  _root_.PositivityTheory.SiegelWeilFormula.kunf.SecA.isCompact_stdK'_k d.B d.Y d.ok.good d.b d.K d.ok.stdK
theorem isClosed_siegelParabolic (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsClosed (par2 σ d.Y : Set d.G) := by
  have e : (par2 σ d.Y : Set d.G) = (fun p : d.G => (inFrame d.b p).toBlocks₂₁) ⁻¹' {0} := by
    ext p
    exact mem_stabiliser_iff_lower_block_zero d.ok.frame p
  rw [e]
  have hfr := GlobalTheory.EisBL.DoubledParabolic.continuous_inFrame (σ := σ) (Y := d.Y) d.b
  exact isClosed_singleton.preimage
    (continuous_pi fun i => continuous_pi fun j => hfr.matrix_elem (Sum.inr i) (Sum.inl j))
theorem continuous_a_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Continuous d.a := by
  refine GlobalTheory.Doubling.continuous_of_prod (P := par2 σ d.Y) (K := d.K) (_root_.PositivityTheory.SiegelWeilFormula.kunf.isClosed_siegelParabolic d) (_root_.PositivityTheory.SiegelWeilFormula.kunf.isCompact_K_k d)
    (fun g => ?_) ?_
  · obtain ⟨p, t, hp, k, hk, e⟩ := d.ok.hgt.iwa g
    exact ⟨⟨p, mem_parabolic_GL2_iff.2 ⟨t, hp⟩⟩, k, hk, e⟩
  · have hc : Continuous fun x : par2 σ d.Y × d.K => ((GlobalTheory.Doubling.absE F E (SecA.uDet x.1) : ℝ≥0) : ℝ) :=
      NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp (SecA.continuous_uDet.comp continuous_fst))
    refine hc.congr fun x => ?_
    obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 x.1.2
    rw [d.ok.hgt.val _ t ht _ x.2.2, SecA.uDet_eq ht]
end PositivityTheory.SiegelWeilFormula.kunf
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseHgtInt
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseHgtExA
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Hgt
open scoped Matrix TensorProduct NNReal
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl GlobalTheory.WeilM
open GlobalTheory.CompanionTheory.IwaDbl.FrameCore
open Formalism.UG (cT bc)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem exists_scal_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) :
    ∃ ξ : E, ξ ≠ 0 ∧ (∀ i j, σ ((ξ • Y.Jᵀ) j i) = (ξ • Y.Jᵀ) i j) ∧ ∀ w, ∃ (M : Matrix (Fin n) (Fin n) ℂ) (r : ℝ), Mᴴ = M ∧
      IsCartan M (Y.θ w) ∧ r ≠ 0 ∧ (ξ • Y.Jᵀ).map (B.emb w).1 = (r : ℂ) • Mᵀ := by
  have hc := hB.cm
  rcases hY with h | h
  · refine ⟨1, one_ne_zero, fun i j => by simpa using h.herm j i, fun w => ⟨_, 1, ?_, h.cartan w, one_ne_zero, ?_⟩⟩
    · exact Matrix.ext fun i j => (hc.2.2.2 _ _).symm.trans (congrArg _ (h.herm i j))
    · ext i j; simp
  · obtain ⟨x, hx⟩ : ∃ x, x - σ x ≠ 0 := by
      by_contra! e
      have := hc.2.1
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
        (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun y =>
          (hc.2.2.2 τ y).symm.trans (congrArg τ (sub_eq_zero.1 (e y)).symm))))
    have hs : σ (x - σ x) = -(x - σ x) := by rw [map_sub, cm_conj_conj hc, neg_sub]
    refine ⟨_, hx, fun i j => ?_, fun w => ?_⟩
    · change σ (_ * Y.J i j) = _ * Y.J j i
      rw [map_mul, hs, h.skew, neg_mul_neg]
    · have h1 := hc.2.2.2 (B.emb w).1 (x - σ x)
      rw [hs, map_neg] at h1
      have h2 : (B.emb w).1 (x - σ x) = ((B.emb w).1 (x - σ x)).im * Complex.I := by
        have := congrArg Complex.re h1
        simp only [Complex.neg_re, Complex.star_def, Complex.conj_re] at this
        exact Complex.ext (by simp only [Complex.mul_I_re, Complex.ofReal_im]; linarith) (by simp)
      refine ⟨_, ((B.emb w).1 (x - σ x)).im, Matrix.ext fun i j => ?_, h.cartan w, fun e => hx ?_, Matrix.ext fun i j => ?_⟩
      · change star (Complex.I * (B.emb w).1 (Y.J j i)) = Complex.I * (B.emb w).1 (Y.J i j)
        rw [star_mul', ← hc.2.2.2, h.skew]; simp
      · rw [e] at h2
        exact (map_eq_zero _).1 (h2.trans (by simp))
      · change (B.emb w).1 (_ * Y.J j i) = _ * (Complex.I * (B.emb w).1 (Y.J j i))
        rw [map_mul, ← mul_assoc, ← h2]
theorem iwasawa2_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) (x : G2 σ Y) :
    ∃ p : siegelOf (Equiv.refl (Fin n ⊕ Fin n)) (UG (cA σ) (dbl (incM F Y.J))).subtype, ∃ k ∈ stab2 σ Y B, x = p * k := by
  have hL : Y.L.IsFullLattice E := hY.elim (·.lat) (·.lat)
  obtain ⟨ξ, hξ, hh, hw⟩ := _root_.GlobalTheory.ThK.Dbl.Hgt.exists_scal_k hB hY
  choose M r h1 h2 h3 h4 using hw
  choose b hb hb' using fun w => exists_arch hB.cm (B.emb w) (h1 w) (isUnit_of_cartan (h2 w)) (h2 w) (h3 w) (h4 w)
  obtain ⟨a, -, ha⟩ := Frames.exists_isLatticeFrame_of_arch Y.L b
  obtain rfl : b = fun w => bc (compInf F E w) a := (funext ha).symm
  obtain ⟨g, rfl⟩ := back_surj hξ x
  obtain ⟨p, k, hk, rfl⟩ := HasIwasawa.adelic (a := a) (_root_.GlobalTheory.ThK.Dbl.Hgt.hasIwasawa_fin'_k hB hY (det_ne hY) hξ hh) hb g
  have k2 := keeps_back hL.fg hξ (mem_KAd.1 (inv_mem hk)).1
  rw [map_inv] at k2
  exact ⟨⟨_, back_mem_par hξ p.2⟩, back σ Y hξ k, ⟨fun w => back_comm hξ _ ((hb' w _).1 ((mem_KAd.1 hk).2 w)),
    keeps_back hL.fg hξ (mem_KAd.1 hk).1, k2⟩, map_mul _ _ _⟩
theorem hgtEx_core_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s)
    (hK : IsCompact (stab2 σ Y B : Set (G2 σ Y))) :
    (∃ K a, IsStab2 (σ := σ) (Y := Y) B K ∧ IsHgt K a ∧ Continuous a ∧ ∀ x, 0 < a x) ∧
    ∃ e : UA σ Y.J × UA σ Y.J →* G2 σ Y, Continuous e ∧ ∀ h h', IsEmb h h' (e (h, h')) := by
  have := isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have := t2Space_adeleRing' (F := F)
  have := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  have hI := iwasawaOf_of_isCompact (ν := absE F E) continuous_subtype_val continuous_absE hK (_root_.GlobalTheory.ThK.Dbl.Hgt.iwasawa2_k hB hY)
  refine ⟨⟨_, fun x => hgtOf (Equiv.refl _) (UG (cA σ) (dbl (incM F Y.J))).subtype (absE F E) (stab2 σ Y B) x, isStab2_stab2 B,
    ⟨fun x => ?_, fun p t hp k hk => ?_⟩,
    NNReal.continuous_coe.comp (hI.continuous_hgtOf continuous_subtype_val continuous_absE hK), fun x => hgtOf_pos x⟩,
    emb2 σ Y, ((continuous_blkGL _).comp (continuous_subtype_val.prodMap continuous_subtype_val)).subtype_mk _, fun _ _ => rfl⟩
  · obtain ⟨p, h⟩ := _root_.GlobalTheory.ThK.Dbl.Hgt.iwasawa2_k hB hY x
    exact ⟨p, leviOf _ _ p, isPar_iff.2 ⟨mem_siegelOf.1 p.2, rfl⟩, h⟩
  · obtain ⟨h1, h2⟩ := isPar_iff.1 hp
    have := hI.hgtOf_mul ⟨p, mem_siegelOf.2 h1⟩ hk
    rw [show t = leviOf (Equiv.refl _) (UG (cA σ) (dbl (incM F Y.J))).subtype ⟨p, mem_siegelOf.2 h1⟩ from Units.ext h2.symm]
    exact congrArg NNReal.toReal this
end GlobalTheory.ThK.Dbl.Hgt
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped Matrix TensorProduct NNReal
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling GlobalTheory.WeilM Hgt
theorem hgtEx_of_k (hK : _root_.GlobalTheory.ThK.Dbl.Stab2Cpt_k) : _root_.GlobalTheory.ThK.Dbl.HgtEx_k := fun F E _ _ _ _ _ σ B n Y r s hB hY =>
  _root_.GlobalTheory.ThK.Dbl.Hgt.hgtEx_core_k hB hY (hK F E σ B n Y r s hB hY _ (isStab2_stab2 B))
theorem hgtInt_of_k (hC : _root_.GlobalTheory.ThK.Dbl.Stab2Cpt_k) : _root_.GlobalTheory.ThK.Dbl.HgtInt_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY K a e hK ha he μ hμ
  have := isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have := t2Space_adeleRing' (F := F)
  have := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) _
  have : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  have cK := hC F E σ B n Y r s hB hY K hK
  obtain ⟨⟨K', a', hK', ha', ca, a0⟩, e', ce, he'⟩ := _root_.GlobalTheory.ThK.Dbl.hgtEx_of_k hC F E σ B n Y r s hB hY
  obtain rfl : K = K' := Subgroup.ext fun k => (hK k).trans (hK' k).symm
  obtain rfl : a = a' := funext fun x => by
    obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa x
    rw [ha.val p t hp k hk, ha'.val p t hp k hk]
  obtain rfl : e = e' := MonoidHom.ext fun x => Subtype.ext (Units.ext ((he x.1 x.2).trans (he' x.1 x.2).symm))
  have cc : Continuous (cA (F := F) σ) := IsModuleTopology.continuous_of_linearMap (cA (F := F) σ).toLinearMap
  let T : G2 σ Y → Matrix (Fin n) (Fin n) (AE F E) := fun k => (mat2 k⁻¹ * diagCols (E := AE F E) (Fin n)).toRows₁
  let T' : G2 σ Y → Matrix (Fin n) (Fin n) (AE F E) := fun k => (mat2 k⁻¹ * diagCols (E := AE F E) (Fin n)).toRows₂
  have cm : Continuous fun k : G2 σ Y => (mat2 k⁻¹ * diagCols (E := AE F E) (Fin n)) :=
    ((Units.continuous_val.comp continuous_subtype_val).comp continuous_inv).matrix_mul continuous_const
  have cT : Continuous T := cm.matrix_submatrix _ _
  have cT' : Continuous T' := cm.matrix_submatrix _ _
  have : IsModuleTopology (AF F) (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin n → AE F E))
  let c := (Module.Free.chooseBasis (AF F) (Matrix (Fin n) (Fin n) (AE F E))).equivFun
  obtain ⟨R, C, b, h1, h2, h3, h4⟩ := count_ad (E := E) hB.cm.1 c (IsModuleTopology.continuous_of_linearMap c.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap c.symm.toLinearMap) (UG (cA σ) (incM F Y.J))
    (isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.matrix_map cc)) continuous_const)
    ((cK.image ((cc.comp cT'.matrix_det).smul (cT.matrix_mul cT'.matrix_adjugate))).union
      (cK.image ((cc.comp cT.matrix_det).smul (cT'.matrix_mul cT.matrix_adjugate))))
    (cK.image (continuous_norm_tens.comp cT.matrix_det)) μ
  have key : ∀ g : UA σ Y.J, ∃ k ∈ K, ∃ t : GL (Fin n) (AE F E), a (e (1, g)) = absE F E (Matrix.GeneralLinearGroup.det t) ∧
      T k = t.1 ∧ T' k = mat g⁻¹ * t.1 := fun g => by
    obtain ⟨p, t, hp, k, hk, h⟩ := ha.iwa (e (1, g))
    have e1 : k⁻¹ = e (1⁻¹, g⁻¹) * p := by rw [← Prod.inv_mk, map_inv, h]; group
    have hp' : (mat2 p * diagCols (E := AE F E) (Fin n)) = (diagCols (E := AE F E) (Fin n) * t.1) := hp
    have e2 : (mat2 k⁻¹ * diagCols (E := AE F E) (Fin n)) = Matrix.fromRows t.1 (mat g⁻¹ * t.1) := by
      rw [e1, show mat2 (e (1⁻¹, g⁻¹) * p) = mat2 (e (1⁻¹, g⁻¹)) * mat2 p from rfl, Matrix.mul_assoc, hp', he, inv_one,
        show mat (1 : UA σ Y.J) = 1 from rfl, diagCols, Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows]
      simp
    exact ⟨k, hk, t, by rw [h, ha.val p t hp k hk], congrArg Matrix.toRows₁ e2, congrArg Matrix.toRows₂ e2⟩
  refine integrable_of_count μ (ca.comp (ce.comp (Continuous.prodMk_right 1))).measurable (fun g => a0 _) (R := R) h1 (fun g => ?_)
    h2 b fun j => (measure_mono fun g hg => ?_).trans (h4 j)
  · obtain ⟨k, hk, t, e1, e2, -⟩ := key g
    exact e1.trans_le (h3 _ ⟨k, hk, congrArg (fun x => Algebra.norm (AF F) (Matrix.det x)) e2⟩)
  · obtain ⟨k, hk, t, e1, e2, e3⟩ := key g
    have hd : (mat g⁻¹).det * (cA σ).toRingHom (mat g⁻¹).det = 1 := by
      have h := congrArg Matrix.det (show (mat g⁻¹)ᵀ * incM F Y.J * (mat g⁻¹).map (cA σ) = incM F Y.J from (g⁻¹).2)
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
        show ((mat g⁻¹).map (cA σ)).det = (cA σ).toRingHom (mat g⁻¹).det from ((cA σ).toRingHom.map_det _).symm] at h
      refine (isUnit_det_JR (R := AF F) (det_ne hY)).mul_left_cancel ?_
      change (incM F Y.J).det * _ = (incM F Y.J).det * _
      linear_combination h
    obtain ⟨q1, q2⟩ := Hgt.graph_alg (cA σ).toRingHom (g := mat g) g.1.mul_inv e3 hd
    have q : ∀ X : Matrix (Fin n) (Fin n) (AE F E), Algebra.norm (AF F) t.1.det • X = (t.1.det * (cA σ).toRingHom t.1.det) • X :=
      fun X => by rw [← algebraMap_smul (AE F E), algebraMap_norm_eq hB.cm, ← cA_eq]; rfl
    refine ⟨Matrix.GeneralLinearGroup.det t, ⟨k, hk, congrArg (fun x => Algebra.norm (AF F) (Matrix.det x)) e2⟩, e1 ▸ hg,
      .inl ⟨k, hk, Eq.symm ((q _).trans (q1.trans ?_))⟩, .inr ⟨k, hk, Eq.symm ((q _).trans (q2.trans ?_))⟩⟩ <;> rw [← e2] <;> rfl
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldDefs
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def SignOK_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (Y : Spc F E n) : Prop :=
  d.A.IsHerm σ d.B d.r d.s ∧ (∀ i j, σ (Y.J j i) = -Y.J i j) ∨ d.A.IsSkew σ d.B d.r d.s ∧ ∀ i j, σ (Y.J j i) = Y.J i j
def IsJ_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (j : G2 σ Y →* d.G) : Prop :=
  Continuous j ∧
  (∀ g, (inFrame d.b (j g)).submatrix (Sum.map (em0 h) (em0 h)) (Sum.map (em0 h) (em0 h)) = inFrame b g) ∧
  ∀ g, ∀ u ∈ ({Sum.inl (i0 h), Sum.inr (i0 h)} : Set (Fin d.n ⊕ Fin d.n)), ∀ v,
    inFrame d.b (j g) u v = (1 : Matrix _ _ (AE F E)) u v ∧ inFrame d.b (j g) v u = (1 : Matrix _ _ (AE F E)) v u
def Res_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (j : G2 σ Y →* d.G) {κ : Type}
    [Fintype κ] (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F Y.J))) κ)
    (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ Φ ∈ d.sch, ∀ Φ' ∈ schA F κ,
    (∀ X : Mx F E d.m d.n, (∀ a, X a (i0 h) = 0) → Tof d.B.ψ dd l b Φ' (X.submatrix id (em0 h)) = d.T Φ X) →
    ∀ g (X : Mx F E d.m d.n), (∀ a, X a (i0 h) = 0) → Tof d.B.ψ dd l b (om g Φ') (X.submatrix id (em0 h)) = d.T (d.om (j g) Φ) X
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRelA
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SD
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.bb1 : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
  rw [← incM_mul', ← Units.val_mul, mul_inv_cancel, Units.val_one, incM_one']
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.bb2 : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
  rw [← incM_mul', ← Units.val_mul, inv_mul_cancel, Units.val_one, incM_one']
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.inFrame_mul (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y := by
  have hmul : mat2 (x * y) = mat2 x * mat2 y := rfl
  simp only [inFrame, hmul]
  calc incM F (d.b⁻¹).1 * (mat2 x * mat2 y) * incM F d.b.1
      = incM F (d.b⁻¹).1 * mat2 x * (incM F d.b.1 * incM F (d.b⁻¹).1) * mat2 y * incM F d.b.1 := by
        rw [d.bb1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.inFrame_one : inFrame d.b (1 : d.G) = 1 := by
  change incM F (d.b⁻¹).1 * 1 * incM F d.b.1 = 1
  simpa only [Matrix.mul_one] using d.bb2
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.inFrame_inj {x y : d.G} (h : inFrame d.b x = inFrame d.b y) : x = y := by
  have hx : mat2 x = incM F d.b.1 * inFrame d.b x * incM F (d.b⁻¹).1 := by
    simp only [inFrame, ← Matrix.mul_assoc, d.bb1, Matrix.one_mul]
    rw [Matrix.mul_assoc, d.bb1, Matrix.mul_one]
  have hy : mat2 y = incM F d.b.1 * inFrame d.b y * incM F (d.b⁻¹).1 := by
    simp only [inFrame, ← Matrix.mul_assoc, d.bb1, Matrix.one_mul]
    rw [Matrix.mul_assoc, d.bb1, Matrix.mul_one]
  have : mat2 x = mat2 y := by rw [hx, hy, h]
  exact Subtype.ext (Units.ext this)
end SD
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockIntSch
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section Cmb
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem cmb_add_k (c c' : Fin d.m × Fin d.n × Fin 2 → AF F) : d.cmb (c + c') = d.cmb c + d.cmb c' := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, Pi.add_apply, Matrix.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
theorem cmb_eq_k (c : Fin d.m × Fin d.n × Fin 2 → AF F) (i : Fin d.m) (j : Fin d.n) :
    d.cmb c i j = ∑ k, c (i, j, k) • Algebra.TensorProduct.basis (AF F) d.bs k := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
theorem crd_cmb'_k (c : Fin d.m × Fin d.n × Fin 2 → AF F) : d.crd (d.cmb c) = c := by
  funext k
  obtain ⟨i, j, l⟩ := k
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, _root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_eq_k]
  exact congrFun ((Algebra.TensorProduct.basis (AF F) d.bs).repr_sum_self fun k => c (i, j, k)) l
theorem cmb_crd_k (X : Mx F E d.m d.n) : d.cmb (d.crd X) = X := by
  ext i j
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_eq_k]
  exact (Algebra.TensorProduct.basis (AF F) d.bs).sum_repr (X i j)
theorem continuous_cmb_k : Continuous d.cmb := by
  obtain ⟨i1, -, -, -⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_eq_k]
  exact continuous_finsetSum _ fun k _ => ((continuous_apply (i, j, k)).smul continuous_const)
theorem continuous_crd_k : Continuous d.crd := by
  obtain ⟨i1, -, -, -⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  refine continuous_pi fun k => ?_
  have hl : Continuous (((Finsupp.lapply k.2.2).comp (Algebra.TensorProduct.basis (AF F) d.bs).repr.toLinearMap :
      AE F E →ₗ[AF F] AF F)) := IsModuleTopology.continuous_of_linearMap _
  exact hl.comp ((continuous_apply k.2.1).comp (continuous_apply k.1))
def cmbE_k : (Fin d.m × Fin d.n × Fin 2 → AF F) ≃ₜ+ Mx F E d.m d.n where
  toFun := d.cmb
  invFun := d.crd
  left_inv := _root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb'_k d
  right_inv := _root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_crd_k d
  map_add' := _root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_add_k d
  continuous_toFun := _root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_cmb_k d
  continuous_invFun := _root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_crd_k d
end Cmb
theorem int_schM_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ν : Measure (Mx F E d.m d.n)) (hν : ν.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) : Integrable f ν := by
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Fin d.m × Fin d.n × Fin 2 → AF F) := Pi.borelSpace
  let e : (Fin d.m × Fin d.n × Fin 2 → AF F) ≃ᵐ Mx F E d.m d.n := (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmbE_k d).toHomeomorph.toMeasurableEquiv
  haveI : (Measure.map e.symm ν).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmbE_k d).symm
  have h1 : Integrable (f ∘ e) (Measure.map e.symm ν) := by
    have hf' : f ∘ d.cmb ∈ schA F (Fin d.m × Fin d.n × Fin 2) := Submodule.mem_comap.mp hf
    refine intSchA _ ?_ _ inferInstance hf'
    exact congrArg (fun m => @MeasurableSpace.pi (Fin d.m × Fin d.n × Fin 2) (fun _ => AF F) fun _ => m) measAF_eq
  have h2 := (integrable_map_equiv e f).2 h1
  rwa [MeasurableEquiv.map_map_symm] at h2
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTbijFrame
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.TBij
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
section Gen
variable {R E' : Type} [CommRing R] [CommRing E'] [Algebra R E'] (c : E' →ₐ[R] E') {α β : Type} [Fintype α]
  [DecidableEq α] [Fintype β] [DecidableEq β]
end Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace Adp
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
abbrev _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) → Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) → AF F :=
  symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J))
abbrev _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := incM F d.b.1.toCols₂
abbrev _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w' = om (d.dd.e w) (d.dd.e w') :=
  d.dd.form w w'
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_add_left (w₁ w₂ w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (w₁ + w₂) w' = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w₁ w' + _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w₂ w' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq, map_add (f := _), om, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  ring
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_add_right (w w₁ w₂ : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w (w₁ + w₂) = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w₁ + _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w₂ := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq, map_add (f := _), om, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  ring
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_smul_right (a : AF F) (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w (a • w') = a * _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq, map_smul, om, Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_sum_left {ι : Type} (s : Finset ι) (a : ι → AF F) (v : ι → Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E))
    (w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (∑ i ∈ s, a i • v i) w' = ∑ i ∈ s, a i * _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (v i) w' := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq, map_sum, map_smul, om, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, sum_dotProduct,
    dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_antisymm (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w' = -_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w' w := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq, om]
  ring
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_diag (Z Z' : Matrix (Fin d.m) (Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ) (Z' * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ) = 0 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy, symp]
  rw [hTens_outer _ _ _ _ _ _ _ (isLagr_diagCols (cA σ) (incM F d.Y.J)).1, mul_zero, map_zero]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.frame_iso : (d.b.1.toCols₂)ᵀ * dbl d.Y.J * d.b.1.toCols₂.map σ = 0 := by
  obtain ⟨ε, h⟩ := d.ok.frame.1
  have h2 := congrArg Matrix.toBlocks₂₂ h
  rw [Matrix.toBlocks_fromBlocks₂₂] at h2
  rw [← h2]
  ext i j
  simp [Matrix.toBlocks₂₂, Matrix.mul_apply, Matrix.toCols₂]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_frame (X X' : Matrix (Fin d.m) (Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (X * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) (X' * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) = 0 := by
  have h : (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ * dbl (incM F d.Y.J) * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d).map (cA σ) = 0 := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy, cA_incM, ← incM_dbl, ← incM_transpose, ← incM_mul, ← incM_mul, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.frame_iso, incM_zero']
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy, symp]
  rw [hTens_outer _ _ _ _ _ _ _ h, mul_zero, map_zero]
def _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : Matrix (Fin d.m) (Fin d.n) (AE F E) :=
  (w * (incM F (d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1)ᵀ).toCols₂
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_add (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d (w + w') = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w + _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w' := by
  ext i j; simp [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs, Matrix.add_mul, Matrix.toCols₂]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_smul (a : AF F) (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d (a • w) = a • _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w := by
  ext i j; simp [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs, Matrix.smul_mul, Matrix.toCols₂]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.decomp (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    ∃ Z : Matrix (Fin d.m) (Fin d.n) (AE F E), w = Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ + _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ := by
  obtain ⟨t, ht⟩ := d.ok.frame.2
  set V := w * (incM F (d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1)ᵀ with hV
  have h1 : w = V * (incM F d.b.1)ᵀ := by
    rw [hV, Matrix.mul_assoc, ← Matrix.transpose_mul, ← incM_mul, Units.mul_inv, incM_one', Matrix.transpose_one,
      Matrix.mul_one]
  have h2 : incM F d.b.1 = Matrix.fromCols (incM F d.b.1.toCols₁) (incM F d.b.1.toCols₂) := by
    ext i (j | j) <;> rfl
  refine ⟨V.toCols₁ * (incM F t.1)ᵀ, ?_⟩
  have h3 : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w = V.toCols₂ := rfl
  rw [h3]
  conv_lhs => rw [h1, h2, ← Matrix.fromCols_toCols V]
  have ht' : incM F d.b.1.toCols₁ = @HMul.hMul (Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))
      (Matrix (Fin d.n) (Fin d.n) (AE F E)) (Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))
      Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (diagCols (Fin d.n)) (incM F t.1) := by
    rw [ht, ← incM_diagCols (F := F) (E := E)]
    exact incM_mul _ _
  rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows, ht', Matrix.transpose_mul, ← Matrix.mul_assoc]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_frame (X : Matrix (Fin d.m) (Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d (X * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) = X := by
  have h1 : incM F (d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1 * _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).toCols₂ := by
    have : (d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1 * d.b.1.toCols₂ = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E).toCols₂ := by
      rw [← Units.inv_mul d.b]
      ext i j; simp [Matrix.mul_apply, Matrix.toCols₂]
    rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy, ← incM_mul, this]
    ext i j; simp [incM, Matrix.toCols₂, Matrix.one_apply]
  rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs, Matrix.mul_assoc, ← Matrix.transpose_mul, h1]
  ext i j
  simp [Matrix.toCols₂, Matrix.mul_apply, Matrix.one_apply]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_split (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w' = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w' - _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w' * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w := by
  obtain ⟨Z, hZ⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.decomp d w
  obtain ⟨Z', hZ'⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.decomp d w'
  have a1 : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w' = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ) w' + _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w' := by
    conv_lhs => rw [hZ]
    rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_add_left]
  have a2 : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ) w' = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ) (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w' * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) := by
    conv_lhs => rw [hZ']
    rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_add_right, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_diag, zero_add]
  have a3 : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w' * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w' * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ) := by
    conv_lhs => rw [hZ]
    rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_add_right, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_frame, add_zero]
  rw [a1, a2, a3, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_antisymm d (Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ)]
  ring
end Adp
end PositivityTheory.SiegelWeilFormula.TBij
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpLrho
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
abbrev spf_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (a b : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : AF F :=
  symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) a b
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.THeisK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
def TUnit_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ ν : Measure (Mx F E d.m d.n), ν.IsAddHaarMeasure → ∀ x, ∀ Φ ∈ d.sch, ∀ Φ' ∈ d.sch,
  ∫ X, d.T (d.om x Φ) X * star (d.T (d.om x Φ') X) ∂ν = ∫ X, d.T Φ X * star (d.T Φ' X) ∂ν
def THeis_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ ∈ d.sch, ∀ Z X : Mx F E d.m d.n,
  d.T (d.dd.rho d.B.ψ (Z * (incM F d.b.1.toCols₂)ᵀ) Φ) X = d.T Φ (X + Z) ∧
  d.T (d.dd.rho d.B.ψ (Z * (incM F d.b.1.toCols₁)ᵀ) Φ) X = d.B.ψ (d.tt (d.gram Z X)) * d.T Φ X
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKheadSecK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
namespace PositivityTheory.SiegelWeilFormula.Khead
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem secK_k : _root_.PositivityTheory.SiegelWeilFormula.SecK_k := by
  intro F E _ _ _ _ _ σ d Φ hΦ
  obtain ⟨c1, c2⟩ := sec_cont_law d.ok.dbl hΦ.1
  refine ⟨c1, fun p t x hp => ?_, ?_⟩
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, s0]
    exact c2 p t x hp
  · have := hΦ.2
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ)).map
      (LinearMap.pi fun x => d.l ∘ₗ d.om x)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, funext fun x => by simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, map_mul]⟩
end PositivityTheory.SiegelWeilFormula.Khead
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilSteps
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
def ThetaPt_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ ∈ d.sch, ∀ (x : d.G) (h : UA σ d.A.J),
  thetaSum F (d.om x (d.S h Φ)) = ∑' X : Matrix (Fin d.m) (Fin d.n) E, d.T (d.om x Φ) (mat h⁻¹ * incM F X)
def SplitDom_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w L, R.IsLocOp w L → ∀ Ψ ∈ R.away w, ∀ g : d.G,
  ∃ (y₀ : GR d.n) (Ψ' : Mx F E d.m d.n → ℂ),
    (∀ Φ ∈ d.sch, ∀ f, IsSw f → d.T Φ = R.tens w f Ψ → ∀ y, d.T (d.om (g * R.ι w y) Φ) = R.tens w (L (y₀ * y) f) Ψ') ∧
    ∀ δ : ℝ, 0 < δ → R.tens w (fun u => (Real.exp (-δ * sq u) : ℂ)) Ψ' ∈ d.schM
def DecompW_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w (g : d.G),
  ∃ (x : d.G) (y₀ : GR d.n), g = x * R.ι w y₀ ∧ d.cw w (inFrame d.b x) = 1
def ThetaBdd_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Fn ∈ d.schM, ∃ K : ℝ, ∀ h : UA σ d.A.J,
  Summable (fun X : Matrix (Fin d.m) (Fin d.n) E => ‖Fn (mat h⁻¹ * incM F X)‖) ∧
    ∑' X : Matrix (Fin d.m) (Fin d.n) E, ‖Fn (mat h⁻¹ * incM F X)‖ ≤ K
def LocFamG_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w L, R.IsLocOp w L →
  ∀ (X : Fin d.n → ℝ) (a : ℝ → GR d.n), (∀ t, IsDil X t (a t)) →
    ∃ Gf : GR d.n → ℂ → (Fin d.m → Fin d.n → ℂ) → ℂ, (∀ (y : GR d.n) (t : ℝ), Gf y t = L (y * a t) (fP 1)) ∧
    (∀ y u, DifferentiableOn ℂ (fun z => Gf y z u) (strip X)) ∧
    (∀ u, ContinuousOn (fun q : GR d.n × ℂ => Gf q.1 q.2 u) (Set.univ ×ˢ strip X)) ∧
    (∀ q ∈ (Set.univ : Set (GR d.n)) ×ˢ strip X, ∃ N ∈ 𝓝 q, ∃ C δ : ℝ, 0 < δ ∧ ∀ q' ∈ N, q'.2 ∈ strip X → ∀ u,
      ‖Gf q'.1 q'.2 u‖ ≤ C * Real.exp (-δ * sq u)) ∧
    ∀ y : GR d.n, ((mR y).toBlocks₂₂).det ≠ 0 → ∀ (r : ℕ) u,
      iteratedDeriv r (fun z => Gf y z u) 0 = L y (fP ((dil (2 * Real.pi) X ^ r) 1)) u
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwSt
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.TW
def Uniq_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ ν : Measure (Mx F E d.m d.n), ν.IsAddHaarMeasure →
  ∀ Λ : d.Fn →ₗ[ℂ] ℂ, Λ ∈ (adeleClass F).adm d.κ →
    (∀ Z : Mx F E d.m d.n, ∀ Φ ∈ d.sch, Λ (d.dd.rho d.B.ψ (Z * (incM F d.b.1.toCols₂)ᵀ) Φ) = Λ Φ) →
    ∃ C : ℂ, ∀ Φ ∈ d.sch, Λ Φ = C * ∫ Z, d.T Φ Z ∂ν
def UpTo_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ ν : Measure (Mx F E d.m d.n), ν.IsAddHaarMeasure → ∀ ε w, d.IsW ε w → ∃ C : ℂ, ∀ Φ ∈ d.sch,
  ∀ X, d.T (d.om w Φ) X = C * ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * d.T Φ Z ∂ν
def Poisson_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ ν, d.IsCov ν → ∀ ε : ℤˣ, ∀ f ∈ d.schM,
  ∑' X : Matrix (Fin d.m) (Fin d.n) E, ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram (incM F X) Z)) * f Z ∂ν =
    ∑' X : Matrix (Fin d.m) (Fin d.n) E, f (incM F X)
def ThetaW_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), (∀ ε w, d.IsW ε w → ∀ Φ ∈ d.sch, d.om w Φ ∈ d.sch ∧ thetaSum F (d.om w Φ) = thetaSum F Φ) ∧
  ∃ Φ ∈ d.sch, thetaSum F Φ ≠ 0
theorem tWeyl_of_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (h1 : _root_.PositivityTheory.SiegelWeilFormula.TW.UpTo_k) (h2 : _root_.PositivityTheory.SiegelWeilFormula.TW.Poisson_k) (h3 : _root_.PositivityTheory.SiegelWeilFormula.TW.ThetaW_k) : _root_.PositivityTheory.SiegelWeilFormula.TWeyl_k := by
  intro F E _ _ _ _ _ σ d ν hν ε w hw Φ hΦ X
  obtain ⟨C, hC⟩ := h1 F E σ d ν hν.1 ε w hw
  obtain ⟨hθ, Φ₀, h0, hne⟩ := h3 F E σ d
  have e1 := (hT F E σ d _ (hθ ε w hw Φ₀ h0).1).1.tsum_eq
  have e2 := (hT F E σ d _ h0).1.tsum_eq
  have e3 := h2 F E σ d ν hν ε _ ((hB F E σ d).1 Φ₀ h0)
  simp only [hC Φ₀ h0] at e1
  rw [tsum_mul_left, e3, e2, (hθ ε w hw Φ₀ h0).2] at e1
  have : C = 1 := mul_right_cancel₀ hne (e1.trans (one_mul _).symm)
  rw [hC Φ hΦ X, this, one_mul]
end PositivityTheory.SiegelWeilFormula.TW
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRDSt
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Krd
def EpsEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ),
  ∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 ∧
    (d.A.IsHerm σ d.B d.r d.s ∧ ε = -1 ∨ d.A.IsSkew σ d.B d.r d.s ∧ ε = 1)
def FrEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ),
  (d.A.IsHerm σ d.B d.r d.s → ∃ (fr : InfinitePlace F → GL (Fin d.m) ℂ) (sg : InfinitePlace F → ℤˣ),
    ∀ w, (1 : ℂ) • ((fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (fr w).1.map star) = ((sg w : ℤ) : ℂ) • 1) ∧
  (d.A.IsSkew σ d.B d.r d.s → ∃ (fr : InfinitePlace F → GL (Fin d.m) ℂ) (sg : InfinitePlace F → ℤˣ),
    ∀ w, Complex.I • ((fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (fr w).1.map star) = ((sg w : ℤ) : ℂ) • 1)
def IotaEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ),
  ∀ (ε : ℤˣ) (ζ : ℂ), d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 →
    (ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) →
    ∃ ι : InfinitePlace F → (GR d.n →* d.G), (∀ w, Continuous (ι w)) ∧
      (∀ w y, dZ d.n ζ * d.cw w (inFrame d.b (ι w y)) = mR y * dZ d.n ζ) ∧
      (∀ w w' y, w' ≠ w → d.cw w' (inFrame d.b (ι w y)) = 1) ∧
      ∀ w y, finOne F • inFrame d.b (ι w y) = finOne F • (1 : Matrix _ _ (AE F E))
theorem rdEx_of_k (h1 : _root_.PositivityTheory.SiegelWeilFormula.Krd.EpsEx_k) (h2 : _root_.PositivityTheory.SiegelWeilFormula.Krd.FrEx_k) (h3 : _root_.PositivityTheory.SiegelWeilFormula.Krd.IotaEx_k) : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨ε, hε, hs⟩ := h1 F E σ d
  rcases hs with ⟨hA, rfl⟩ | ⟨hA, rfl⟩
  · obtain ⟨fr, sg, hfr⟩ := (h2 F E σ d).1 hA
    obtain ⟨ι, hc, ha, ho, hf⟩ := h3 F E σ d (-1) 1 hε (Or.inl ⟨rfl, rfl⟩)
    exact ⟨⟨-1, 1, fr, sg, ι, hε, Or.inl ⟨rfl, rfl⟩, hfr, hc, ha, ho, hf⟩⟩
  · obtain ⟨fr, sg, hfr⟩ := (h2 F E σ d).2 hA
    obtain ⟨ι, hc, ha, ho, hf⟩ := h3 F E σ d 1 Complex.I hε (Or.inr ⟨rfl, rfl⟩)
    exact ⟨⟨1, Complex.I, fr, sg, ι, hε, Or.inr ⟨rfl, rfl⟩, hfr, hc, ha, ho, hf⟩⟩
end PositivityTheory.SiegelWeilFormula.Krd
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Stab2CptK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Tow St
open scoped Pointwise
attribute [local instance] ae_ring ae_t2 ae_smul
theorem stab2Cpt_k : _root_.GlobalTheory.ThK.Dbl.Stab2Cpt_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY K hK
  obtain ⟨hL, c, c0, hc⟩ : Y.L.IsFullLattice E ∧ ∃ c : ℂ, c ≠ 0 ∧ ∀ w, IsCartan (c • Y.J.map (B.emb w).1) (Y.θ w) :=
    hY.elim (fun h => ⟨h.lat, 1, one_ne_zero, fun w => by simpa using h.cartan w⟩) fun h => ⟨h.lat, _, Complex.I_ne_zero, h.cartan⟩
  obtain ⟨Φ, hΦ, eΦ⟩ := exists_section hB.cm B.emb
  choose C hC h using fin_bound (F := F) Y hL
  choose R hR using fun w => cartan_bound2 (hc w)
  have hD : IsCompact (Φ '' Set.univ.pi fun w => Metric.closedBall (0 : ℂ) (R w)) :=
    (isCompact_univ_pi fun w => isCompact_closedBall _ _).image hΦ
  have hm : Continuous fun g : G2 σ Y => mat2 g := Units.continuous_val.comp continuous_subtype_val
  have hp : ∀ w, Continuous (piInf (B.emb w)) := fun w => GlobalTheory.Grow.continuous_infEmb_compInf F w (B.emb w)
  have cc : Continuous (cA (F := F) σ) := IsModuleTopology.continuous_of_linearMap (cA (F := F) σ).toLinearMap
  have cl := (isCompact_latHat Y hL.fg).isClosed
  have key : ∀ k ∈ K, mat2 k ∈ Set.univ.pi fun i => Set.univ.pi fun j =>
      (Φ '' Set.univ.pi fun w => Metric.closedBall (0 : ℂ) (R w)) + C (Sum.elim id id i) (Sum.elim id id j) := fun k hk i _ j _ => by
    obtain ⟨k1, k2⟩ := (hK k).1 hk
    rw [eΦ (mat2 k i j)]
    refine Set.add_mem_add ⟨_, fun w _ => ?_, rfl⟩ ?_
    · rw [mem_closedBall_zero_iff]
      refine hR w ((mat2 k).map (piInf (B.emb w))) ?_ (k1 w) i j
      have e := congrArg (fun X => c • Matrix.map X (piInf (B.emb w)))
        (show (mat2 k)ᵀ * dbl (incM F Y.J) * (mat2 k).map (cA σ) = dbl (incM F Y.J) from k.2)
      have d : c • (dbl (incM F Y.J)).map (piInf (B.emb w)) = dbl (c • Y.J.map (B.emb w).1) := by
        ext (a | a) (b | b) <;> simp [dbl, incM, Levi.piInf_incl]
      have d2 : ((mat2 k).map (cA σ)).map (piInf (B.emb w)) = ((mat2 k).map (piInf (B.emb w))).map star :=
        Matrix.ext fun a b => Levi.piInf_cA hB.cm _ _
      simp only [Matrix.map_mul] at e
      rwa [← Matrix.smul_mul, ← Matrix.mul_smul, d, d2] at e
    · have a := fun y hy => k2 y 0 hy (zero_mem _) k (.inl rfl)
      have b := fun y hy => k2 0 y (zero_mem _) hy k (.inl rfl)
      rw [← Matrix.fromBlocks_toBlocks (mat2 k)] at a b
      simp only [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_zero, add_zero, zero_add] at a b
      rcases i with i | i <;> rcases j with j | j
      exacts [h i j _ fun y hy => (a y hy).1, h i j _ fun y hy => (b y hy).1, h i j _ fun y hy => (a y hy).2,
        h i j _ fun y hy => (b y hy).2]
  refine isCompact_of_units _ (isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.matrix_map cc)) continuous_const) _ ?_ _
    (isCompact_univ_pi fun i => isCompact_univ_pi fun j => hD.add (hC _ _)) fun k hk => ⟨key k hk, key _ (inv_mem hk)⟩
  rw [show (K : Set (G2 σ Y)) = {k | _} from Set.ext hK]
  simp only [Set.forall_mem_insert, Set.mem_singleton_iff, forall_eq]
  simp only [Set.setOf_and, Set.setOf_forall]
  have v : ∀ {f : G2 σ Y → G2 σ Y}, Continuous f → ∀ z, IsClosed ({k | (mat2 (f k) *ᵥ z) ∘ Sum.inl ∈ latHat Y} ∩
      {k | (mat2 (f k) *ᵥ z) ∘ Sum.inr ∈ latHat Y}) := fun hf z =>
    have t := (hm.comp hf).matrix_mulVec (continuous_const (y := z))
    (cl.preimage (continuous_pi fun i => (continuous_apply _).comp t)).inter
      (cl.preimage (continuous_pi fun i => (continuous_apply _).comp t))
  exact (isClosed_iInter fun w => isClosed_eq ((hm.matrix_map (hp w)).matrix_mul continuous_const)
      (continuous_const.matrix_mul (hm.matrix_map (hp w)))).inter
    (isClosed_iInter fun z => isClosed_iInter fun z' => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      (v continuous_id _).inter (v continuous_inv _))
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTautoMean
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTautoSInv
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem thetaSum_S_rat_k (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {γ : UA σ d.A.J} (hγ : γ ∈ ratU σ d.A.J)
    {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) : thetaSum F (d.S γ Ψ) = thetaSum F Ψ := by
  have hS : d.S γ Ψ ∈ d.sch := d.ok.dbl.lin.pres γ Ψ hΨ
  obtain ⟨g₀, hg₀⟩ := PositivityTheory.ThKF0.Resc.rat_mat (inv_mem hγ)
  obtain ⟨g₁, hg₁⟩ := PositivityTheory.ThKF0.Resc.rat_mat hγ
  have hinj : Function.Injective (incM F : Matrix (Fin d.m) (Fin d.m) E → Matrix (Fin d.m) (Fin d.m) (AE F E)) :=
    PositivityTheory.SiegelWeilFormula.kfour.incM_injective
  have hmul : ∀ {p q r : ℕ} (A : Matrix (Fin p) (Fin q) E) (B : Matrix (Fin q) (Fin r) E),
      incM F (A * B) = incM F A * incM F B := fun A B => Matrix.map_mul (f := inclR (F := F) (E := E) (AF F))
  have hone : incM F (1 : Matrix (Fin d.m) (Fin d.m) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have e01 : g₀ * g₁ = 1 := hinj (by
    rw [hmul, ← hg₀, ← hg₁, hone]
    have := congrArg (fun u : UA σ d.A.J => ((u.1 : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)))
      (inv_mul_cancel γ)
    simp at this; simpa using this)
  have e10 : g₁ * g₀ = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).1 e01
  let e : Matrix (Fin d.m) (Fin d.n) E ≃ Matrix (Fin d.m) (Fin d.n) E :=
    ⟨fun X => g₀ * X, fun X => g₁ * X, fun X => by simp [← Matrix.mul_assoc, e10], fun X => by simp [← Matrix.mul_assoc, e01]⟩
  have h1 := (hT F E σ d (d.S γ Ψ) hS).1
  have h2 := (hT F E σ d Ψ hΨ).1
  have h3 : HasSum (fun X : Matrix (Fin d.m) (Fin d.n) E => d.T Ψ (incM F (e X))) (thetaSum F (d.S γ Ψ)) := by
    refine h1.congr_fun fun X => ?_
    rw [(hP F E σ d Ψ hΨ).2.2 γ (incM F X)]
    simp only [e, Equiv.coe_fn_mk, hmul, mat, ← hg₀]
  exact h3.unique ((e.hasSum_iff).2 h2)
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem cpt_k (hS : GlobalTheory.Published.SiegelSetUnitary) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Cpt σ d.A.J := by
  have h := _root_.GlobalTheory.ThK.Dbl.cptAll_of_k PositivityTheory.ThKEst.grpTop_of _root_.PositivityTheory.ThKEst.epsOf_of_k (PositivityTheory.ThKEst.siegelAll_of hS)
    PositivityTheory.ThKEst.finVolU PositivityTheory.ThKF.unimodularity_holds
  rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
  · exact h F E σ d.B d.m d.A d.r d.s d.ok.good (Or.inl hA) d.ok.aniso
  · exact h F E σ d.B d.m d.A d.r d.s d.ok.good (Or.inr hA) d.ok.aniso
theorem exists_lth_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ l ∈ (adeleClass F).adm d.κ, ∀ Φ ∈ d.sch, l Φ = thetaSum F Φ :=
  GlobalTheory.T.exists_admitted_form_eq_adelicThetaDistribution F d.κ
theorem cont_S_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) : Continuous fun g : UA σ d.A.J => thetaSum F (d.S g Ψ) := by
  obtain ⟨l, hl, hlθ⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.exists_lth_k d
  exact (d.ok.dbl.lin.cont l hl Ψ hΨ).congr fun g => hlθ _ (d.ok.dbl.lin.pres g Ψ hΨ)
theorem inv_S_k (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) :
    ∀ γ ∈ ratU σ d.A.J, ∀ g, thetaSum F (d.S (γ * g) Ψ) = thetaSum F (d.S g Ψ) := fun γ hγ g => by
  rw [map_mul, Module.End.mul_apply, _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaSum_S_rat_k hP hT d hγ (d.ok.dbl.lin.pres g Ψ hΨ)]
theorem bdd_S_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) :
    ∃ C : ℝ, ∀ g, ‖thetaSum F (d.S g Ψ)‖ ≤ C :=
  (_root_.PositivityTheory.SiegelWeilFormula.Tauto.cpt_k hS d).bdd (_root_.PositivityTheory.SiegelWeilFormula.Tauto.cont_S_k d hΨ) (_root_.PositivityTheory.SiegelWeilFormula.Tauto.inv_S_k hP hT d hΨ)
theorem intOn_S_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) :
    IntegrableOn (fun g => thetaSum F (d.S g Ψ)) d.D d.μ := by
  obtain ⟨C, hC⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.bdd_S_k hS hP hT d hΨ
  exact Measure.integrableOn_of_bounded (M := C) ((_root_.PositivityTheory.SiegelWeilFormula.Tauto.cpt_k hS d).fin d.μ d.D d.ok.haar d.ok.dom).ne
    (_root_.PositivityTheory.SiegelWeilFormula.Tauto.cont_S_k d hΨ).aestronglyMeasurable (Eventually.of_forall hC)
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
end

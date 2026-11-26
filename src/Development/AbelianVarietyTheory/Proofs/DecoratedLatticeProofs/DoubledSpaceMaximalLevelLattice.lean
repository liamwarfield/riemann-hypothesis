module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceLeOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslateToSecondModelCuspFormMapValueAutomorphi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledSpaceMaximalLevelLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledSpaceMaximalLevelLattice
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EisCont

open Matrix Formalism.IndefR.Datum

variable {D : D7}

theorem jX_dblDec_mulVec (V : HSp D) (y : Fin V.rank → AE D) :
    (dblDec V).jX *ᵥ y = pairVec finSumFinEquiv (GlobalTheory.MixModel.giA V *ᵥ y) (GlobalTheory.MixModel.giA V *ᵥ y) := by
  funext k
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective k
  · rw [pairVec_inl]
    simp only [mulVec, HypDec.jX, dblDec, GlobalTheory.Core.Rk.SWLaw.stackRows,
      GlobalTheory.MixModel.giA, GlobalTheory.MixModel.rat, Matrix.map_apply,
      Matrix.submatrix_apply, id, Equiv.symm_apply_apply, fromRows_apply_inl, fromRows_apply_inr]
  · rw [pairVec_inr]
    simp only [mulVec, HypDec.jX, dblDec, GlobalTheory.Core.Rk.SWLaw.stackRows,
      GlobalTheory.MixModel.giA, GlobalTheory.MixModel.rat, Matrix.map_apply,
      Matrix.submatrix_apply, id, Equiv.symm_apply_apply, fromRows_apply_inl, fromRows_apply_inr]

theorem mem_siegel_of_mem_stab (V : HSp D) {p : GA D (dblSp V)} (h : p ∈ stab (dblDec V)) : p ∈ siegel V := by
  obtain ⟨α, hα⟩ := h
  refine mem_siegelOf.2 (keepsDiag_of_mulVec fun w hw => ?_)
  obtain ⟨x, rfl⟩ := (mem_diagSub _).1 hw
  have hx : pairVec finSumFinEquiv x x = (dblDec V).jX *ᵥ (GlobalTheory.MixModel.gA V *ᵥ x) := by
    rw [jX_dblDec_mulVec, mulVec_mulVec, GlobalTheory.MixModel.giA_mul_gA, one_mulVec]
  change mt (dblSp V) p *ᵥ _ ∈ _
  rw [hx, mulVec_mulVec, hα, ← mulVec_mulVec, jX_dblDec_mulVec]
  exact (pairVec_mem_diagSub _).2 rfl

theorem mul_jX_dblDec (V : HSp D) {p : GA D (dblSp V)} (h : p ∈ siegel V) :
    mt (dblSp V) p ⬝ (dblDec V).jX = (dblDec V).jX ⬝
      (GlobalTheory.MixModel.gA V * leviMat finSumFinEquiv (mt (dblSp V) p) * GlobalTheory.MixModel.giA V) := by
  have hk : KeepsDiag finSumFinEquiv (mt (dblSp V) p) := mem_siegelOf.1 h
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, jX_dblDec_mulVec, jX_dblDec_mulVec, hk.mulVec_diag, mulVec_mulVec,
    mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.MixModel.giA_mul_gA, Matrix.one_mul]

def gramGL (V : HSp D) : GL (Fin V.rank) (AE D) :=
  ⟨GlobalTheory.MixModel.gA V, GlobalTheory.MixModel.giA V, GlobalTheory.MixModel.gA_mul_giA V, GlobalTheory.MixModel.giA_mul_gA V⟩

theorem mem_stab_of_mem_siegel (V : HSp D) {p : GA D (dblSp V)} (h : p ∈ siegel V) : p ∈ stab (dblDec V) :=
  ⟨gramGL V * leviOf finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V)) ⟨p, h⟩ * (gramGL V)⁻¹,
    mul_jX_dblDec V h⟩

theorem onX_dblDec (V : HSp D) {p : GA D (dblSp V)} (h : p ∈ siegel V) (h' : p ∈ stab (dblDec V)) :
    onX (dblDec V) ⟨p, h'⟩ =
      gramGL V * leviOf finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V)) ⟨p, h⟩ * (gramGL V)⁻¹ :=
  Units.ext ((eq_of_mul_jX _ (mul_jX (dblDec V) ⟨p, h'⟩)).trans (eq_of_mul_jX _ (mul_jX_dblDec V h)).symm)

theorem isAniso_zeroSp (D : D7) : IsAniso (zeroSp D) := by
  rintro r C ⟨hr, hC, -⟩
  exact hC.ne_zero ⟨0, hr⟩ (funext fun i => Fin.elim0 i)

theorem siegel_eq_stab_dblDec : ∀ (D : D7) (V : HSp D), siegel V = stab (dblDec V) ∧ (∀ (p : GA D (dblSp V)) (h : p ∈ siegel V) (h' : p ∈ stab (dblDec V)), aP V ⟨p, h⟩ = Matrix.GeneralLinearGroup.det (onX (dblDec V) ⟨p, h'⟩)) ∧ IsAniso (zeroSp D) ∧ ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → ∃ (L : Submodule (𝓞 D.host.E) (Fin (dblSp V).rank → D.host.E)) (b : GL (Fin (dblSp V).rank) (AE D)), IsLevel (dblSp V) L b ∧ Khat V a = lev (dblSp V) L b := by
  intro D V
  refine ⟨Subgroup.ext fun p => ⟨mem_stab_of_mem_siegel V, mem_siegel_of_mem_stab V⟩, fun p h h' => ?_,
    isAniso_zeroSp D, fun a ha => ⟨frameLat (dblSp V), blkGL finSumFinEquiv (a, a),
      ⟨(isLattice_frameLat_host (dblSp V)).toIsLattice, SelfDual.isSelfDualAt_frameLat D (dblSp V), ha.dbl⟩, Khat_eq V a⟩⟩
  rw [onX_dblDec V h h', map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  rfl

end GlobalTheory.EisCont

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledSpaceMaximalLevelLatticeStatement
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.doubled_space_maximal_level_lattice : ∀ (D : D7) (V : HSp D), siegel V = stab (dblDec V) ∧ (∀ (p : GA D (dblSp V)) (h : p ∈ siegel V) (h' : p ∈ stab (dblDec V)), aP V ⟨p, h⟩ = Matrix.GeneralLinearGroup.det (onX (dblDec V) ⟨p, h'⟩)) ∧ IsAniso (zeroSp D) ∧ ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → ∃ (L : Submodule (𝓞 D.host.E) (Fin (dblSp V).rank → D.host.E)) (b : GL (Fin (dblSp V).rank) (AE D)), IsLevel (dblSp V) L b ∧ Khat V a = lev (dblSp V) L b := by
  first | exact @GlobalTheory.EisCont.siegel_eq_stab_dblDec | exact GlobalTheory.EisCont.siegel_eq_stab_dblDec | (intros; apply GlobalTheory.EisCont.siegel_eq_stab_dblDec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceContinuousPosLeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceContinuousPosLeOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Corev.RealHeight

set_option maxHeartbeats 16000000 in
theorem continuous_hgtW (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)) (w : InfinitePlace D.host.F)
    (hI : GlobalTheory.Doubling.HasIwasawa D.sp.cm.sig (GlobalTheory.Doubling.dblSp V).gram
      (GlobalTheory.Doubling.KArch D.sp.cm.sig (GlobalTheory.Doubling.dblSp V).gram w (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) a))) :
    Continuous (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w) := by
  have hc := GlobalTheory.AdelicU.isCMExt_host D
  have hK := GlobalTheory.Doubling.isCompact_KArch (Q := (GlobalTheory.Doubling.dblSp V).gram) hc w
    (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) a)
  have h1 := hI.continuous_hgtH (GlobalTheory.Doubling.continuous_absEw w) hK
  have h2 := GlobalTheory.Doubling.continuous_ioH (R := w.Completion) (σ := D.sp.cm.sig) (GlobalTheory.Doubling.gram_hdbl V)
  have h3 : Continuous fun g : GlobalTheory.Doubling.Gw V w => ((GlobalTheory.Doubling.hgtArch D.sp.cm.sig (GlobalTheory.Doubling.dblSp V).gram w
      (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) a) (GlobalTheory.Doubling.ioH w.Completion D.sp.cm.sig (GlobalTheory.Doubling.gram_hdbl V) (g, 1)) : ℝ)) :=
    NNReal.continuous_coe.comp (h1.comp (h2.comp (continuous_id.prodMk continuous_const)))
  exact h3
theorem hgtW_pos (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)) (w : InfinitePlace D.host.F) (g : GlobalTheory.Doubling.Gw V w) :
    0 < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w g := by
  have h : 0 < ((GlobalTheory.Doubling.hgtArch D.sp.cm.sig (GlobalTheory.Doubling.dblSp V).gram w
      (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) a) (GlobalTheory.Doubling.ioH w.Completion D.sp.cm.sig (GlobalTheory.Doubling.gram_hdbl V) (g, 1)) : ℝ)) :=
    NNReal.coe_pos.2 (GlobalTheory.Doubling.hgtH_pos _)
  exact h

theorem hgtW_cont_pos_le_one : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), GlobalTheory.Doubling.IsMaj V a → ∀ w, Continuous (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w) ∧ ∀ g, 0 < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w g ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w g ≤ 1 := fun D V a ha w =>
  ⟨continuous_hgtW D V a w (GlobalTheory.T.iwasawa_doubled_hermitian_space_real_place D V a ha w), fun g => ⟨hgtW_pos D V a w g, GlobalTheory.T.doublingHeightAtRealPlace_le_one D V a ha w g⟩⟩

end GlobalTheory.Corev.RealHeight
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceContinuousPosLeOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingHeightAtRealPlace_continuous_pos_le_one : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), GlobalTheory.Doubling.IsMaj V a → ∀ w, Continuous (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w) ∧ ∀ g, 0 < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w g ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w g ≤ 1 := by
  first | exact @GlobalTheory.Corev.RealHeight.hgtW_cont_pos_le_one | exact GlobalTheory.Corev.RealHeight.hgtW_cont_pos_le_one | (intros; apply GlobalTheory.Corev.RealHeight.hgtW_cont_pos_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabiliserSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabiliserSplitPlace
noncomputable section

namespace GlobalTheory.Core.Rk.IwFlagSplit

section Pure

variable {A R : Type} [CommRing A] [CommRing R] {n ρ s : Type} [Fintype n] [Fintype ρ] [Fintype s] [DecidableEq n]
  [DecidableEq ρ] [DecidableEq s]

theorem map_keeps (f : A →+* R) {M : Matrix n n A} {j : Matrix n ρ A} {p : Matrix ρ n A} (hp : p * j = 1)
    {a : Matrix ρ ρ R} (h : M.map f * j.map f = j.map f * a) : (M * j).map f = (j * (p * (M * j))).map f := by
  have h1 : p.map f * j.map f = 1 := by rw [← Matrix.map_mul, hp, Matrix.map_one _ (map_zero f) (map_one f)]
  rw [Matrix.map_mul (L := j), Matrix.map_mul (L := p), Matrix.map_mul, h, ← Matrix.mul_assoc (p.map f), h1,
    Matrix.one_mul]

def lev : (ρ ⊕ s) ⊕ ρ → ℕ := Sum.elim (Sum.elim (fun _ => 0) fun _ => 1) fun _ => 2


omit [DecidableEq ρ] [DecidableEq s] in
theorem keeps_cols (ε : n ≃ (ρ ⊕ s) ⊕ ρ) {e e' : Matrix n ρ A} {i : Matrix n s A} {B b : GL n A}
    (hB : B.1 = (Matrix.fromCols (Matrix.fromCols e i) e').submatrix id ε) (hb : b.1.BlockTriangular (lev ∘ ε)) :
    ∃ a : Matrix ρ ρ A, (B * b * B⁻¹).1 * e = e * a := by
  refine ⟨Matrix.of fun k l => b.1 (ε.symm (.inl (.inl k))) (ε.symm (.inl (.inl l))), ?_⟩
  have h : (B * b * B⁻¹).1 * B.1 = B.1 * b.1 := by rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul]
  generalize (B * b * B⁻¹).1 = x at h
  ext k l
  have h1 := congrFun (congrFun h k) (ε.symm (.inl (.inl l)))
  have h2 : ∀ t, b.1 (ε.symm (.inl (.inr t))) (ε.symm (.inl (.inl l))) = 0 := fun t => hb (by simp [lev])
  have h3 : ∀ t, b.1 (ε.symm (.inr t)) (ε.symm (.inl (.inl l))) = 0 := fun t => hb (by simp [lev])
  rw [hB, Matrix.mul_apply, Matrix.mul_apply, ← ε.symm.sum_comp fun t => _ * b.1 t _] at h1
  simpa [Matrix.mul_apply, h2, h3] using h1


omit [DecidableEq ρ] [DecidableEq s] in
theorem keeps_rows (ε : n ≃ (ρ ⊕ s) ⊕ ρ) {p p' : Matrix ρ n A} {q : Matrix s n A} {B b : GL n A}
    (hB : (B⁻¹).1 = (Matrix.fromRows (Matrix.fromRows p q) p').submatrix ε id) (hb : b.1.BlockTriangular (lev ∘ ε)) :
    ∃ c : Matrix ρ ρ A, p' * (B * b * B⁻¹).1 = c * p' := by
  refine ⟨Matrix.of fun k l => b.1 (ε.symm (.inr k)) (ε.symm (.inr l)), ?_⟩
  have h : (B⁻¹).1 * (B * b * B⁻¹).1 = b.1 * (B⁻¹).1 := by
    rw [← Units.val_mul, mul_assoc, inv_mul_cancel_left, Units.val_mul]
  generalize (B * b * B⁻¹).1 = x at h
  ext k l
  have h1 := congrFun (congrFun h (ε.symm (.inr k))) l
  have h2 : ∀ t, b.1 (ε.symm (.inr k)) (ε.symm (.inl t)) = 0 := fun t => hb (by rcases t with t | t <;> simp [lev])
  rw [hB, Matrix.mul_apply, Matrix.mul_apply, ← ε.symm.sum_comp fun t => b.1 _ t * _] at h1
  simpa [Matrix.mul_apply, h2] using h1


omit [DecidableEq s] [Fintype s] in
theorem keeps_dual {G x x' : Matrix n n A} {e f : Matrix n ρ A} {c : Matrix ρ ρ A} {xi Gi : Matrix n n A}
    (hx : x * xi = 1) (hG : G * Gi = 1) (h : x'.transpose * G * x = G) (hf : e.transpose * G * f = 1)
    (hc : e.transpose * G * x = c * (e.transpose * G)) : ∃ a : Matrix ρ ρ A, x' * e = e * a := by
  have h1 : e.transpose * G = c * (e.transpose * G * xi) := by
    rw [← Matrix.mul_assoc, ← hc, Matrix.mul_assoc _ x, hx, Matrix.mul_one]
  have h2 : c * (e.transpose * G * xi * f) = 1 := by rw [← Matrix.mul_assoc, ← h1, hf]
  have h3 := mul_eq_one_comm.1 h2
  generalize e.transpose * G * xi * f = c' at h3
  have h4 : e.transpose * G * xi = c' * (e.transpose * G) := by
    rw [h1, ← Matrix.mul_assoc c', h3, Matrix.one_mul, ← h1]
  have h5 : x'.transpose * G = G * xi := by
    conv_rhs => rw [← h, Matrix.mul_assoc, hx, Matrix.mul_one]
  refine ⟨c'.transpose, Matrix.transpose_injective ?_⟩
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    ← Matrix.mul_one (e.transpose * _), ← hG, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ G, h5, ← Matrix.mul_assoc, h4,
    Matrix.mul_assoc, Matrix.mul_assoc, hG, Matrix.mul_one]

end Pure

section Local

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open Formalism.UG (bc GLint)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)} {ρ s : Type} [Fintype ρ] [Fintype s] [DecidableEq ρ]
  [DecidableEq s]

theorem emb_keeps (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (q : GLoc σ J v) {j : Matrix (Fin n) ρ (AF F ⊗[F] E)}
    {p : Matrix ρ (Fin n) (AF F ⊗[F] E)} (hp : p * j = 1) {e : Matrix (Fin n) ρ E} (hj : j = e.map (inclR (AF F)))
    {a a' : Matrix ρ ρ (Fv F v)} (h1 : (splitHom σ J τ q).1 * e.map τ = e.map τ * a)
    (h2 : (splitHom σ J (τ.comp σ) q).1 * e.map (τ.comp σ) = e.map (τ.comp σ) * a') :
    (matHom _ σ J (emb σ J v q)).1 * j = j * (p * ((matHom _ σ J (emb σ J v q)).1 * j)) := by
  have key : ∀ (τ : E →ₐ[F] Fv F v) {a : Matrix ρ ρ (Fv F v)}, (splitHom σ J τ q).1 * e.map τ = e.map τ * a →
      (matHom _ σ J (emb σ J v q)).1.map (((splitProj τ).toRingHom).comp (compFin F E v)) *
        j.map (((splitProj τ).toRingHom).comp (compFin F E v)) =
        j.map (((splitProj τ).toRingHom).comp (compFin F E v)) * a := fun τ a ha => by
    have e1 : (matHom _ σ J (emb σ J v q)).1.map (((splitProj τ).toRingHom).comp (compFin F E v)) =
        (splitHom σ J τ q).1 := by
      conv_rhs => rw [← proj_emb_self σ J v q]
      rfl
    have e2 : j.map (((splitProj τ).toRingHom).comp (compFin F E v)) = e.map τ := by
      ext k l
      simp [hj, inclR, compFin]
    rw [e1, e2, ha]
  ext k l
  refine GlobalTheory.Doubling.adele_ext (fun w => ?_) fun u => ?_
  · have e1 : (matHom _ σ J (emb σ J v q)).1.map (compInf F E w) = 1 := by
      change (matHom _ σ J (projArch σ J w (emb σ J v q))).1 = 1
      rw [projArch_emb, map_one, Units.val_one]
    exact congrFun (congrFun (map_keeps (compInf F E w) hp (a := 1) (by rw [e1, Matrix.one_mul, Matrix.mul_one])) k) l
  · by_cases hu : u = v
    · subst hu
      exact split_ext h τ (congrFun (congrFun (map_keeps _ hp (key τ h1)) k) l)
        (congrFun (congrFun (map_keeps _ hp (key _ h2)) k) l)
    · have e1 : (matHom _ σ J (emb σ J v q)).1.map (compFin F E u) = 1 := by
        change (matHom _ σ J (proj σ J u (emb σ J v q))).1 = 1
        rw [proj_emb_ne σ J hu, map_one, Units.val_one]
      exact congrFun (congrFun (map_keeps (compFin F E u) hp (a := 1) (by rw [e1, Matrix.one_mul, Matrix.mul_one])) k) l

theorem exists_flag_basis (τ : E →ₐ[F] Fv F v) (hJ : IsHermND σ J) {e e' : Matrix (Fin n) ρ E}
    {i : Matrix (Fin n) s E} {p : Matrix ρ (Fin n) E} {q : Matrix s (Fin n) E} (ε : Fin n ≃ (ρ ⊕ s) ⊕ ρ)
    (hsum : e * p + i * q + e' * ((e.map σ)ᵀ * J) = 1) (hf : (e.map σ)ᵀ * J * e' = 1) :
    ∃ (B : GL (Fin n) (Fv F v)) (lv : Fin n → ℕ), ∀ g : GLoc σ J v, (B⁻¹ * splitHom σ J τ g * B).1.BlockTriangular lv →
      (∃ a : Matrix ρ ρ (Fv F v), (splitHom σ J τ g).1 * e.map τ = e.map τ * a) ∧
        ∃ a : Matrix ρ ρ (Fv F v), (splitHom σ J (τ.comp σ) g).1 * e.map (τ.comp σ) = e.map (τ.comp σ) * a := by
  have hm : ((e.map σ)ᵀ * J).map τ = (e.map (τ.comp σ))ᵀ * J.map τ := Matrix.map_mul (f := (τ : E →+* Fv F v))
  have hB : (Matrix.fromCols (Matrix.fromCols (e.map τ) (i.map τ)) (e'.map τ)).submatrix id ε *
      (Matrix.fromRows (Matrix.fromRows (p.map τ) (q.map τ)) ((e.map (τ.comp σ))ᵀ * J.map τ)).submatrix ε id = 1 := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.fromCols_mul_fromRows, Matrix.fromCols_mul_fromRows,
      ← hm]
    have := congrArg (τ : E →+* Fv F v).mapMatrix hsum
    rw [map_add (f := _), map_add (f := _), map_one] at this
    simp only [RingHom.mapMatrix_apply, Matrix.map_mul] at this
    rw [hm]
    exact this
  refine ⟨⟨_, _, hB, mul_eq_one_comm.1 hB⟩, lev ∘ ε, fun g hg => ?_⟩
  generalize hBe : (⟨_, _, hB, mul_eq_one_comm.1 hB⟩ : GL (Fin n) (Fv F v)) = B at hg
  have hx : B * (B⁻¹ * splitHom σ J τ g * B) * B⁻¹ = splitHom σ J τ g := by group
  obtain ⟨c, hc⟩ := keeps_rows ε (B := B) (by rw [← hBe]; rfl) hg
  refine ⟨hx ▸ keeps_cols ε (B := B) (by rw [← hBe]) hg, ?_⟩
  rw [hx] at hc
  refine keeps_dual (G := J.map τ) (f := e'.map τ) (Units.mul_inv _) (splitGram hJ τ).mul_inv (splitHom_unitary τ g) ?_ hc
  rw [← hm]
  exact (Matrix.map_mul (f := (τ : E →+* Fv F v))).symm.trans
    (by rw [hf, Matrix.map_one _ (map_zero _) (map_one _)])

theorem iwasawa_of_triangular (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →ₐ[F] Fv F v)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (hL : IsSelfDualAt σ J L v) (Q : Subgroup (GLoc σ J v))
    (B : GL (Fin n) (Fv F v)) (lv : Fin n → ℕ)
    (hQ : ∀ g : GLoc σ J v, (B⁻¹ * splitHom σ J τ g * B).1.BlockTriangular lv → g ∈ Q) (y : GLoc σ J v) :
    ∃ q k : GLoc σ J v, q ∈ Q ∧ k ∈ stabLoc σ J L v ∧ y = q * k := by
  obtain ⟨β, hβ⟩ : ∃ β, IsSplitBasis τ L β := exists_isSplitBasis τ L h
  have iw : ∀ x : GL (Fin n) (Fv F v), ∃ q ∈ Q, ∃ k ∈ stabLoc σ J L v,
      x * β = splitHom σ J τ q * B * β⁻¹ * splitHom σ J τ k * β := fun x => by
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    obtain ⟨b, hb, w, hw, e⟩ := GlobalTheory.SplitWeil.iwasawa_blockTriangular (Fv F v) (Fin n) lv (B⁻¹ * x * β)
    rw [← (GLint_eq_KO_and_princ_eq_KOne v n).1] at hw
    refine ⟨(splitEquivIn h hJ τ B).symm b, hQ _ ?_, (splitEquivIn h hJ τ β).symm w,
      (mem_stabLoc_iff_GLint h hJ hL hβ).2 ?_, ?_⟩
    · rwa [← splitEquivIn_apply h hJ, ContinuousMulEquiv.apply_symm_apply]
    · rwa [ContinuousMulEquiv.apply_symm_apply]
    · rw [splitHom_splitEquivIn_symm, splitHom_splitEquivIn_symm]
      calc x * β = B * (B⁻¹ * x * β) := by group
        _ = _ := by rw [e]; group
  obtain ⟨q₀, hq₀, k₀, hk₀, e₀⟩ := iw 1
  obtain ⟨q₁, hq₁, k₁, hk₁, e₁⟩ := iw (splitHom σ J τ y)
  refine ⟨q₁ * q₀⁻¹, k₀⁻¹ * k₁, mul_mem hq₁ (inv_mem hq₀), mul_mem (inv_mem hk₀) hk₁, splitHom_injective h hJ τ ?_⟩
  rw [mul_left_inj] at e₀ e₁
  rw [e₁, map_mul, map_mul, map_mul, map_inv, map_inv]
  generalize splitHom σ J τ q₀ = a₀, splitHom σ J τ q₁ = a₁, splitHom σ J τ k₀ = c₀, splitHom σ J τ k₁ = c₁ at e₀ ⊢
  rw [eq_inv_of_mul_eq_one_right e₀.symm]
  group

end Local

section Record

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

theorem iwasawa_stab_split : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (v : FinPl D), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → ∀ y : Gv T v, ∃ q k : Gv T v, emb D.sp.cm.sig T.gram v q ∈ stab d ∧ k ∈ stabLoc D.sp.cm.sig T.gram (frameLat T) v ∧ y = q * k := by
  intro D T T₀ r d v ⟨P, P', hne, hP, hP'⟩ y
  obtain ⟨τ, -⟩ := existsUnique_splitPrime_eq (isCMExt_host D) (v := v) hne (HeightOneSpectrum.ext hP)
    (HeightOneSpectrum.ext hP')
  haveI := SelfDual.isLattice_frameLat T
  have hf : d.qY ⬝ d.e' = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.pY_jY)
  obtain ⟨B, lv, hB⟩ := exists_flag_basis τ (GlobalTheory.Doubling.isHermND_gram T) (e := d.e) (e' := d.e') (i := d.i₀)
    (p := d.qX) (q := d.q0) (Fintype.equivOfCardEq (by simp [← d.rank_add]; ring)) d.sum_eq_one_rat hf
  refine iwasawa_of_triangular (isCMExt_host D) (GlobalTheory.Doubling.isHermND_gram T) τ (frameLat T)
    (SelfDual.isSelfDualAt_frameLat D T v) ((stab d).comap (emb D.sp.cm.sig T.gram v)) B lv (fun g hg => ?_) y
  obtain ⟨⟨a, ha⟩, a', ha'⟩ := hB g hg
  have h1 : mt T (emb D.sp.cm.sig T.gram v g) ⬝ d.jX =
      d.jX ⬝ (d.pX ⬝ (mt T (emb D.sp.cm.sig T.gram v g) ⬝ d.jX)) :=
    emb_keeps (isCMExt_host D) τ g d.pX_jX rfl ha ha'
  rw [Subgroup.mem_comap]
  generalize emb D.sp.cm.sig T.gram v g = x at h1 ⊢
  have h2 : (d.pX ⬝ (mt T x⁻¹ ⬝ d.jX)) ⬝ (d.pX ⬝ (mt T x ⬝ d.jX)) = 1 := by
    rw [Matrix.mul_assoc d.pX, Matrix.mul_assoc (mt T x⁻¹), ← h1, ← Matrix.mul_assoc (mt T x⁻¹), ← mt_mul,
      inv_mul_cancel, mt_one, Matrix.one_mul, d.pX_jX]
  exact ⟨⟨_, _, mul_eq_one_comm.1 h2, h2⟩, h1⟩

end Record

end GlobalTheory.Core.Rk.IwFlagSplit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabiliserSplitPlaceStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_isotropic_stabiliser_split_place : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (v : FinPl D), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → ∀ y : Gv T v, ∃ q k : Gv T v, emb D.sp.cm.sig T.gram v q ∈ stab d ∧ k ∈ stabLoc D.sp.cm.sig T.gram (frameLat T) v ∧ y = q * k := by
  first | exact @GlobalTheory.Core.Rk.IwFlagSplit.iwasawa_stab_split | exact GlobalTheory.Core.Rk.IwFlagSplit.iwasawa_stab_split | (intros; apply GlobalTheory.Core.Rk.IwFlagSplit.iwasawa_stab_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthonormalBasisUnimodularHermitianLocalRi
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthonormalBasisUnimodularHermitianLocalRi
open Matrix

namespace GlobalTheory.Core.Rk.Exh

theorem exists_orthonormal_of_isLocalRing (O : Type) [CommRing O] [IsLocalRing O] (s : O →+* O)
    (hs : ∀ x, s (s x) = x) (hτ : ∃ τ : O, τ + s τ = 1)
    (hn : ∀ u : O, IsUnit u → s u = u → ∃ x : O, s x * x = u)
    (n : ℕ) (Q : Matrix (Fin n) (Fin n) O) (hQ : Formalism.UG.cT s Q = Q) (hu : IsUnit Q) :
    ∃ a : GL (Fin n) O, Formalism.UG.cT s a.1 * Q * a.1 = 1 := by
  obtain ⟨P, hP, h⟩ := UnramifiedHermitian.exists_eq_transpose_mul_map_of_isUnit_or s hs
    (fun x _ => IsLocalRing.isUnit_or_isUnit_one_sub_self x) hτ
    (fun u h1 h2 => (hn u h2 h1).imp fun x hx => by rw [mul_comm, hx])
    (G := Q) (fun a b => congrFun (congrFun hQ b) a) ((Matrix.isUnit_iff_isUnit_det Q).1 hu)
  obtain ⟨R, hR, h'⟩ := UnramifiedHermitian.exists_congr_symm s (G := 1) (H := Q) hP
    (by rw [Matrix.mul_one, h])
  have hR' : IsUnit (R.map s) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hR.map s
  refine ⟨hR'.unit, ?_⟩
  rw [IsUnit.unit_spec, h']
  congr 2
  ext i j
  exact hs _

end GlobalTheory.Core.Rk.Exh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthonormalBasisUnimodularHermitianLocalRiStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormal_basis_unimodular_hermitian_local_ring : ∀ (O : Type) [CommRing O] [IsLocalRing O] (s : O →+* O), (∀ x, s (s x) = x) → (∃ τ : O, τ + s τ = 1) → (∀ u : O, IsUnit u → s u = u → ∃ x : O, s x * x = u) → ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) O), Formalism.UG.cT s Q = Q → IsUnit Q → ∃ a : GL (Fin n) O, Formalism.UG.cT s a.1 * Q * a.1 = 1 := by
  first | exact @GlobalTheory.Core.Rk.Exh.exists_orthonormal_of_isLocalRing | exact GlobalTheory.Core.Rk.Exh.exists_orthonormal_of_isLocalRing | (intros; apply GlobalTheory.Core.Rk.Exh.exists_orthonormal_of_isLocalRing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PushforwardHaarRealPointsTimesLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PushforwardHaarRealPointsTimesLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

namespace GlobalTheory.ChainOnto.HaarInf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem finE_of_mem_ginfC (V : HSp D) {x : GA D V} (hx : x ∈ GinfC V) : Lev.finE V x = 1 := by
  simp only [Lev.finE, MonoidHom.comp_apply]
  rw [show finHom V x = 1 from hx, map_one]

theorem finE_toFin (V : HSp D) (g : GA D V) : Lev.finE V (GlobalTheory.AutMult.toFin V g : GA D V) = Lev.finE V g := by
  conv_rhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
  rw [map_mul, finE_of_mem_ginfC V (GlobalTheory.AutMult.toInf V g).2, one_mul]

theorem proj_of_mem_ginfC (V : HSp D) (x : GinfC V) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v (x : GA D V) = 1 := by
  rw [← GlobalTheory.AutMult.toInf_coe x]
  exact GlobalTheory.AdelicU.proj_ofInf _ _ v _

theorem toInf_eq_one_iff (V : HSp D) (g : GA D V) : GlobalTheory.AutMult.toInf V g = 1 ↔ g ∈ GfC V := by
  refine ⟨fun h => ?_, fun h => by simpa using GlobalTheory.AutMult.toInf_coe_fin (⟨g, h⟩ : GfC V)⟩
  have e := GlobalTheory.AutMult.toInf_mul_toFin g
  rw [h, OneMemClass.coe_one, one_mul] at e
  exact e ▸ (GlobalTheory.AutMult.toFin V g).2

theorem pushforward_haar_real : ∀ D : D7, LevFacts D → ForStage D fun c _ s => MeasurableSet (intOff c s) ∧ MeasurableSet {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} ∧ {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} ⊆ intOff c s ∧ (∀ g : GA D s.V, Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L → ∃ b : GinfC s.V, ∃ κ ∈ Lev.levG s.V s.β s.L, g = (b : GA D s.V) * κ) ∧ ∃ mR : Measure (GinfC s.V), mR.IsHaarMeasure ∧ ∀ (f : GinfC s.V → ℂ) (F : GA D s.V → ℂ), Integrable f mR → (∀ (b : GinfC s.V), ∀ κ ∈ Lev.levG s.V s.β s.L, F ((b : GA D s.V) * κ) = f b) → IntegrableOn F {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} s.ν ∧ ∫ g in {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L}, F g ∂s.ν = ∫ b, f b ∂mR := by
  intro D hL c hc j hj s hs
  obtain ⟨h1, -, h3, -, -, -⟩ := hL c hc j hj s hs
  haveI := hs.haar
  set V := s.V
  set K := Lev.levG s.V s.β s.L
  let A : Subgroup (GA D V) := (Formalism.L2.DIV.lev D.sp.cm V.gram s.β s.L).comap (Lev.finE V)
  have hAset : (A : Set (GA D V)) = {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} := rfl

  have hfinK : ∀ g ∈ A, (GlobalTheory.AutMult.toFin V g : GA D V) ∈ K := fun g hg =>
    ⟨(GlobalTheory.AutMult.toFin V g).2, Subgroup.mem_comap.2 (by rw [finE_toFin]; exact Subgroup.mem_comap.1 hg)⟩

  have hAopen : IsOpen (A : Set (GA D V)) := by
    obtain ⟨U, hU, hUK⟩ := h1
    let Lf : Subgroup (GfC V) := K.subgroupOf (GfC V)
    have hLf : IsOpen (Lf : Set (GfC V)) := by
      refine Subgroup.isOpen_mono (H₁ := U.subgroupOf (GfC V)) (fun k hk => ?_) (hU.preimage continuous_subtype_val)
      exact (hUK k hk k.2).1
    have e : (A : Set (GA D V)) = GlobalTheory.AutMult.toFin V ⁻¹' (Lf : Set (GfC V)) := by
      ext g
      refine ⟨fun hg => hfinK g hg, fun hg => ?_⟩
      have := Subgroup.mem_comap.1 hg.2
      refine Subgroup.mem_comap.2 ?_
      rw [← finE_toFin]; exact this
    rw [e]; exact hLf.preimage (GlobalTheory.AutMult.continuous_toFin V)

  have hAint : (A : Set (GA D V)) ⊆ intOff c s := by
    intro g hg v _
    rw [← GlobalTheory.AutMult.toInf_mul_toFin g, map_mul, proj_of_mem_ginfC, one_mul]
    exact h3 _ (hfinK g hg) v

  let I : Subgroup (GA D V) :=
    { carrier := intOff c s
      mul_mem' := fun {a b} ha hb v hv => by rw [map_mul]; exact mul_mem (ha v hv) (hb v hv)
      one_mem' := fun v _ => by rw [map_one]; exact one_mem _
      inv_mem' := fun {a} ha v hv => by rw [map_inv]; exact inv_mem (ha v hv) }
  have hIopen : IsOpen (I : Set (GA D V)) := Subgroup.isOpen_mono (H₁ := A) hAint hAopen

  have hker : {g : GA D V | g ∈ A ∧ GlobalTheory.AutMult.toInf V g = 1} = (K : Set (GA D V)) := by
    ext g
    simp only [Set.mem_setOf_eq, toInf_eq_one_iff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hKc : IsCompact (K : Set (GA D V)) :=
    GlobalTheory.T.isCompact_finite_adelic_subgroup_integral_open D V s.Λ hs.selfDual K inf_le_left h3 (by
      obtain ⟨U, hU, hUK⟩ := h1
      exact ⟨U, hU, fun k hk hk' => (hUK k hk hk').1⟩)
  have hpi : ∀ b : GinfC V, GlobalTheory.AutMult.toInf V ((GinfC V).subtype b) = b := fun b => GlobalTheory.AutMult.toInf_coe b
  have hiA : ∀ b : GinfC V, (GinfC V).subtype b ∈ A := fun b => by
    refine Subgroup.mem_comap.2 ?_
    rw [Subgroup.subtype_apply, finE_of_mem_ginfC V b.2]; exact one_mem _
  have hHaar : (Measure.map (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V)))).IsHaarMeasure :=
    GlobalTheory.T.map_restrict_isHaar_of_open_product_compact (GA D V) (GinfC V) s.ν A (GinfC V).subtype (GlobalTheory.AutMult.toInf V) hAopen
      continuous_subtype_val (GlobalTheory.AutMult.continuous_toInf V) hpi hiA (hker ▸ hKc)
  refine ⟨hIopen.measurableSet, hAopen.measurableSet, hAint, fun g hg => ?_, ?_⟩
  · exact ⟨GlobalTheory.AutMult.toInf V g, GlobalTheory.AutMult.toFin V g, hfinK g hg, (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩
  refine ⟨_, hHaar, fun f F hf hF => ?_⟩
  have hmeas : AEMeasurable (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V))) :=
    (GlobalTheory.AutMult.continuous_toInf V).measurable.aemeasurable
  have hFA : ∀ g ∈ (A : Set (GA D V)), F g = f (GlobalTheory.AutMult.toInf V g) := fun g hg => by
    conv_lhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
    exact hF _ _ (hfinK g hg)
  have hint : IntegrableOn (fun g => f (GlobalTheory.AutMult.toInf V g)) (A : Set (GA D V)) s.ν :=
    (integrable_map_measure hf.aestronglyMeasurable hmeas).1 hf
  refine ⟨hint.congr_fun (fun g hg => (hFA g hg).symm) hAopen.measurableSet, ?_⟩
  rw [← hAset, setIntegral_congr_fun hAopen.measurableSet hFA, integral_map hmeas hf.aestronglyMeasurable]

end GlobalTheory.ChainOnto.HaarInf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PushforwardHaarRealPointsTimesLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushforward_haar_realPoints_times_level : ∀ D : D7, LevFacts D → ForStage D fun c _ s => MeasurableSet (intOff c s) ∧ MeasurableSet {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} ∧ {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} ⊆ intOff c s ∧ (∀ g : GA D s.V, Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L → ∃ b : GinfC s.V, ∃ κ ∈ Lev.levG s.V s.β s.L, g = (b : GA D s.V) * κ) ∧ ∃ mR : Measure (GinfC s.V), mR.IsHaarMeasure ∧ ∀ (f : GinfC s.V → ℂ) (F : GA D s.V → ℂ), Integrable f mR → (∀ (b : GinfC s.V), ∀ κ ∈ Lev.levG s.V s.β s.L, F ((b : GA D s.V) * κ) = f b) → IntegrableOn F {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} s.ν ∧ ∫ g in {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L}, F g ∂s.ν = ∫ b, f b ∂mR := by
  first | exact @GlobalTheory.ChainOnto.HaarInf.pushforward_haar_real | exact GlobalTheory.ChainOnto.HaarInf.pushforward_haar_real | (intros; apply GlobalTheory.ChainOnto.HaarInf.pushforward_haar_real <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrthSumExists

def orthDecHsum (D : D7) (A L : HSp D) : OrthDec (GlobalTheory.Doubling.hsum A L) A L where
  iA := (Matrix.fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (0 : Matrix (Fin L.rank) (Fin A.rank) D.host.E)).submatrix finSumFinEquiv.symm id
  iB := (Matrix.fromRows (0 : Matrix (Fin A.rank) (Fin L.rank) D.host.E) (1 : Matrix (Fin L.rank) (Fin L.rank) D.host.E)).submatrix finSumFinEquiv.symm id
  isoA := by
    rw [GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
    simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
  isoB := by
    rw [GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
    simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
  orth := by
    rw [GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
    simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
  rank_add := rfl

theorem exists_orthDec (D : D7) (A L : HSp D) : Nonempty (Σ V₀ : HSp D, OrthDec V₀ A L) :=
  ⟨⟨GlobalTheory.Doubling.hsum A L, orthDecHsum D A L⟩⟩

end GlobalTheory.OrthSumExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpInjWOfAForm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.Core.Rk.UpInjWProof

theorem upInjW_of_aForm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.LiftRows.AForm R SF → GlobalTheory.LiftRows.UpInjW R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hIrr SF hSF hA
  obtain ⟨a, ha, hAF⟩ := hA
  intro i t x hx h0
  obtain ⟨h, -, -, -, hspan, -⟩ := GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R F hC hS hIrr SF hSF i

  have hpart : ∀ c, GlobalTheory.Hk3.Wcc R SF i c ≤ LinearMap.range (R.thG i t) := by
    intro c y hy
    by_cases hc : GlobalTheory.Hk3.Wcc R SF i c = ⊥
    · rw [hc] at hy
      rw [(Submodule.mem_bot ℂ).1 hy]
      exact Submodule.zero_mem _
    · obtain ⟨z, hz, hS'⟩ := hAF i t c hc
      obtain ⟨B, -, -, hzpos, -⟩ := hz
      have hne : ((a i * z : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (mul_pos (ha i) hzpos).ne'
      refine ⟨((a i * z : ℝ) : ℂ)⁻¹ • LinearMap.adjoint (R.thG i t) y, ?_⟩
      rw [map_smul, hS' y hy, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hxr : x ∈ LinearMap.range (R.thG i t) := by
    have : x ∈ LinearMap.range (GlobalTheory.Hk3.eH R i) := ⟨x, hx⟩
    rw [← hspan] at this
    exact (iSup_le hpart) this
  obtain ⟨v, rfl⟩ := hxr
  have h1 : ⟪R.thG i t v, R.thG i t v⟫_ℂ = 0 := by
    rw [← LinearMap.adjoint_inner_right, h0, inner_zero_right]
  exact inner_self_eq_zero.1 h1

end GlobalTheory.Core.Rk.UpInjWProof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumMatApply
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.SumBox

variable {D : D7}

def sumMat {B W H : HSp D} (o : OrthDec B W H) (sW : RealMat W) (sH : RealMat H) : RealMat B :=
  fun τ => o.iA.map (tauE D τ) * sW τ * o.qA.map (tauE D τ) + o.iB.map (tauE D τ) * sH τ * o.qB.map (tauE D τ)

def sumLatO {B W H : HSp D} (o : OrthDec B W H) (LW : Lat W) (LH : Lat H) : Lat B :=
  LW.map ((Matrix.mulVecLin o.iA).restrictScalars (𝓞 D.host.E)) ⊔
    LH.map ((Matrix.mulVecLin o.iB).restrictScalars (𝓞 D.host.E))

theorem sumMat_apply {B W H : HSp D} (o : OrthDec B W H) (sW : RealMat W) (sH : RealMat H) (τ : D.what₂.Tau) :
    sumMat o sW sH τ =
      o.iA.map (tauE D τ) * sW τ * o.qA.map (tauE D τ) + o.iB.map (tauE D τ) * sH τ * o.qB.map (tauE D τ) := rfl

theorem mem_sumLatO {B W H : HSp D} (o : OrthDec B W H) (LW : Lat W) (LH : Lat H) (y : Fin B.rank → D.host.E) :
    y ∈ sumLatO o LW LH ↔ ∃ x ∈ LW, ∃ x' ∈ LH, o.iA *ᵥ x + o.iB *ᵥ x' = y := by
  simp only [sumLatO, Submodule.mem_sup, Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨x', hx', rfl⟩, rfl⟩
    exact ⟨x, hx, x', hx', rfl⟩
  · rintro ⟨x, hx, x', hx', rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨x', hx', rfl⟩, rfl⟩

end GlobalTheory.Core.Rk.SumBox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHyperspecialSubgroupAtPlaceIffLocalStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHyperspecialSubgroupAtPlaceIffLocalStabilizer
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)

noncomputable section

namespace GlobalTheory.HypDict

theorem mem_hyp_iff_embV : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → ∀ (V : HSp D) (g : GA D V), g ∈ hyp V w ↔ ∃ k ∈ Kv V v, g = embV V v k := by
  intro D v w hw V g
  obtain ⟨e, f, hP⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.1 w
  rw [GlobalTheory.LevOp.mem_hyp hP, GlobalTheory.AdelicU.Supp.suppF_iff_of_isPrimeIdem V hP hw g, GlobalTheory.AdelicU.KsphC_eq]
  constructor
  · rintro ⟨hk, k, rfl⟩
    refine ⟨k, ?_, rfl⟩
    have := (GlobalTheory.AdelicU.mem_levelOff.1 hk).2.2 v (Finset.notMem_empty v)
    simpa using this
  · rintro ⟨k, hk, rfl⟩
    exact ⟨GlobalTheory.AdelicU.emb_mem_levelOff (Finset.notMem_empty v) hk, k, rfl⟩

end GlobalTheory.HypDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHyperspecialSubgroupAtPlaceIffLocalStabilizerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_hyperspecialSubgroupAtPlace_iff_local_stabilizer : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → ∀ (V : HSp D) (g : GA D V), g ∈ hyp V w ↔ ∃ k ∈ Kv V v, g = embV V v k := by
  first | exact @GlobalTheory.HypDict.mem_hyp_iff_embV | exact GlobalTheory.HypDict.mem_hyp_iff_embV | (intros; apply GlobalTheory.HypDict.mem_hyp_iff_embV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeVectorIffInverseDoubleCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeVectorIffInverseDoubleCosets
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

namespace GlobalTheory.ChainOnto.SatInv


open GlobalTheory.LFun.ConjPlace in
theorem Tj_inv_eq_invT {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (u : (w.adicCompletion E)ˣ) (j : ℕ) (g : GL (Fin n) (w.adicCompletion E)) :
    Tj ℂ n (Ov E w) (u : w.adicCompletion E) j g⁻¹ =
      Tj ℂ n (Ov E w) (u : w.adicCompletion E) j (invT (RingEquiv.refl (w.adicCompletion E)) n g) := by
  classical
  have hK := mem_iff_invT (n := n) (RingEquiv.refl (w.adicCompletion E)) (O := Ov E w) (O' := Ov E w)
    fun _ => Iff.rfl
  have hd : invT (RingEquiv.refl (w.adicCompletion E)) n (dGL n u j)⁻¹ = dGL n u j :=
    (invT_dGL _ u j).trans (congrArg (fun v => dGL n v j) (Units.ext rfl))
  rw [Tj_apply, Tj_apply]
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨a, ha, b, hb, H⟩
    refine ⟨_, (hK _).1 (inv_mem hb), _, (hK _).1 (inv_mem ha), ?_⟩
    rw [← hd, ← map_mul, ← map_mul, (invT _ n).apply_eq_iff_eq, ← inv_inv g, H]
    group
  · rintro ⟨a, ha, b, hb, H⟩
    obtain ⟨a, rfl⟩ := (invT (RingEquiv.refl (w.adicCompletion E)) n).surjective a
    obtain ⟨b, rfl⟩ := (invT (RingEquiv.refl (w.adicCompletion E)) n).surjective b
    rw [← hd, ← map_mul, ← map_mul, (invT _ n).apply_eq_iff_eq] at H
    refine ⟨_, inv_mem ((hK b).2 hb), _, inv_mem ((hK a).2 ha), ?_⟩
    rw [H]
    group


open GlobalTheory.LFun.ConjPlace in
theorem invT_invT {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (g : GL (Fin n) (w.adicCompletion E)) :
    invT (RingEquiv.refl (w.adicCompletion E)) n (invT (RingEquiv.refl (w.adicCompletion E)) n g) = g :=
  Units.ext (Matrix.ext fun i j => by
    rw [invT_val, ← map_inv, invT_val, inv_inv]; rfl)


open GlobalTheory.LFun.ConjPlace in
theorem heckeVec_inv_eq {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V)
    (hx : x ∈ fixed ρ (KGL w (n := n))) {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (j : ℕ) :
    heckeVec ρ (KGL w (n := n)) (fun g => Tj ℂ n (Ov E w) ϖ j g⁻¹) x =
      heckeVec (ρ.comp (invT (RingEquiv.refl (w.adicCompletion E)) n).symm.toMonoidHom) (KGL w (n := n))
        (Tj ℂ n (Ov E w) ϖ j) x := by
  have hK := mem_iff_invT (n := n) (RingEquiv.refl (w.adicCompletion E)) (O := Ov E w) (O' := Ov E w)
    fun _ => Iff.rfl
  rw [heckeVec_comp_symm _ hK (Tj_mem_hecke hϖ j).1 hx]
  obtain ⟨u, rfl⟩ : ∃ u : (w.adicCompletion E)ˣ, (u : w.adicCompletion E) = ϖ :=
    ⟨Units.mk0 ϖ fun e => by simp [IsUnifV, e] at hϖ, rfl⟩
  congr 1
  funext g
  exact Tj_inv_eq_invT w n u j g

open GlobalTheory.LFun.ConjPlace in
theorem satVec_iff_inv : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), x ≠ 0 → x ∈ fixed ρ (KGL w (n := n)) → B.card = n → (IsSatVecGL w ρ x B ↔ ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec ρ (KGL w (n := n)) (fun g => Tj ℂ n (Ov E w) ϖ j g⁻¹) x = satEig (qV E w) n (B.map (·⁻¹)) j • x) := by
  intro E _ _ w n V _ _ ρ x B h0 hx hB
  have hK := mem_iff_invT (n := n) (RingEquiv.refl (w.adicCompletion E)) (O := Ov E w) (O' := Ov E w)
    fun _ => Iff.rfl
  let ρ' := ρ.comp (invT (RingEquiv.refl (w.adicCompletion E)) n).symm.toMonoidHom
  have hx' : x ∈ fixed ρ' (KGL w (n := n)) := (mem_fixed_comp_symm _ hK).2 hx
  have hs : ∀ g, (invT (RingEquiv.refl (w.adicCompletion E)) n).symm g =
      invT (RingEquiv.refl (w.adicCompletion E)) n g := fun g =>
    (MulEquiv.symm_apply_eq _).2 (invT_invT w n g).symm
  have hρ : ρ'.comp (invT (RingEquiv.refl (w.adicCompletion E)) n).symm.toMonoidHom = ρ := MonoidHom.ext fun g => by
    simp only [ρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hs, invT_invT]
  constructor
  · intro h ϖ hϖ j hj
    rw [heckeVec_inv_eq w n V ρ x hx hϖ j]
    exact (isSatVecGL_invT (.refl _) (fun _ => rfl) rfl h).2.2.2 ϖ hϖ j hj
  · intro h
    have h1 : IsSatVecGL w ρ' x (B.map (·⁻¹)) :=
      ⟨h0, hx', by simpa using hB, fun ϖ hϖ j hj => (heckeVec_inv_eq w n V ρ x hx hϖ j).symm.trans (h ϖ hϖ j hj)⟩
    have h2 := isSatVecGL_invT (.refl _) (fun _ => rfl) rfl h1
    rw [hρ, Multiset.map_map] at h2
    simpa using h2

end GlobalTheory.ChainOnto.SatInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeVectorIffInverseDoubleCosetsStatement
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
theorem _root_.GlobalTheory.T.satake_vector_iff_inverse_doubleCosets : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), x ≠ 0 → x ∈ fixed ρ (KGL w (n := n)) → B.card = n → (IsSatVecGL w ρ x B ↔ ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec ρ (KGL w (n := n)) (fun g => Tj ℂ n (Ov E w) ϖ j g⁻¹) x = satEig (qV E w) n (B.map (·⁻¹)) j • x) := by
  first | exact @GlobalTheory.ChainOnto.SatInv.satVec_iff_inv | exact GlobalTheory.ChainOnto.SatInv.satVec_iff_inv | (intros; apply GlobalTheory.ChainOnto.SatInv.satVec_iff_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StarEqHostConj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RankOneLine

theorem star_eq_hostConj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

def negLine (D : D7) : HSp D :=
  Formalism.BasicNotions.Examples₂.stdSpace Formalism.BasicNotions.Examples₂.star_isIntegral 1 (fun _ => true) 0 1

theorem negLine_gram (D : D7) : ∀ i j, (negLine D).gram i j = -1 := by
  show ∀ i j : Fin 1, (Formalism.BasicNotions.Examples₂.stdSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral 1
    (fun _ => true) 0 1).gram i j = -1
  intro i j
  rw [Formalism.BasicNotions.Examples₂.stdSpace_gram_apply, Subsingleton.elim i j]
  simp [Formalism.BasicNotions.Examples₂.sgn]

theorem exists_line (D : D7) (X : HidaSetting D) (u : D.what₂.Word) :
    ∃ (L : HSp D) (s : D.host.E), s ≠ 0 ∧ L.rank = 1 ∧ (VS D).hT (X.zu u) (X.zu u) ≠ 0 ∧
      ∀ i j, L.gram i j = star s * s * (VS D).hT (X.zu u) (X.zu u) := by
  obtain ⟨π, -, hπ, -⟩ := D.T_norm u
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have hπ0 : ((π : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    intro h; apply hT0; rw [← hπ, h, zero_mul]
  have hc0 : D.host.conj (π : D.host.E) ≠ 0 := by
    intro h; apply hT0; rw [← hπ, h, mul_zero]
  refine ⟨negLine D, ((π : 𝓞 D.host.E) : D.host.E)⁻¹, inv_ne_zero hπ0, ?_, ?_, fun i j => ?_⟩
  · simp [negLine, Formalism.BasicNotions.Examples₂.stdSpace]
  · rw [X.zu_norm]; exact neg_ne_zero.2 hT0
  · rw [negLine_gram, X.zu_norm, star_inv₀, star_eq_hostConj, ← hπ]
    field_simp <;> ring

end GlobalTheory.RankOneLine
end
end

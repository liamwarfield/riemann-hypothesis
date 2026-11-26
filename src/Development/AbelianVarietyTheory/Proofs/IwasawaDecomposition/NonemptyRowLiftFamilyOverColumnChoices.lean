module

public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicArcSmoothAlgebraNonvanishing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowLiftReadingDefiniteFormCoordinates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodMapFormsEquivRowLiftFormsUpperLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodMapFormsEquivRowLiftFormsUpperLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.PerId
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem exists_crd_equiv (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) {O : Type} [CommRing O] {φ : O →+* ℂ}
    {s : Sp1 O φ (Gc X.B px)} (t : Tie1 X.toD7.what₂.embLL (mAU X I hX Xg tr true a) s) :
    ∃ e : Df.MtCx I a ≃ₗ[ℂ] s.A.T, ∀ y, IsCrd I hX a e
      (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) (t.j y) := by
  obtain ⟨e, he⟩ := ColTie.exists_equiv_of_bases (σ := ColTie.sig X.B)
    (n := ColTie.dimP (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX)
    (ColTie.jP (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX (ColTie.sig X.B)) t.j
    (ColTie.linearIndependent_jP_single (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX (ColTie.sig X.B))
    (ColTie.span_range_jP_single_eq_top (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX (ColTie.sig X.B))
    t.forms.li t.forms.span
  refine ⟨e, fun y => ⟨ColTie.zOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y, ?_, (he y).symm⟩⟩
  exact ⟨(ColTie.resK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX).symm
      (ColTie.formK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y),
    ColTie.zOf_mem (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y,
    heq_of_eq (LinearEquiv.apply_symm_apply _ _), rfl⟩


set_option maxHeartbeats 400000 in
theorem exists_perT : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Xg : Finset (Gc B w.px → B.LL)) (tr : TrI B w.px) (p : PkB B w.C (Gc B w.px)) (tA : ∀ a : w.I.ι, Tie1 (w.st Z).toD7.what₂.embLL (mAU (w.st Z) w.I hX Xg tr true a) (p.sA true a)), ∃ d : PerD p, Nonempty (PerT w Z hX Xg tr p (fun a x => (tA a).j x) d) := by
  intro B f T w Z hX Xg tr p tA
  have hE := fun a : w.I.ι => exists_crd_equiv (w.st Z) w.I hX Xg tr a (tA a)
  choose e he using hE
  have hG : ∀ u a, ∃ g : Df.MtCx w.I a ≃ₗ[ℂ] (TC.per w.I w.l u a).Mt, ∀ F, Df.SameForm w.I w.l u a F (g F) := fun u a =>
    Df.mtCx_equiv_per w.I w.ok w.pins w.l hX u a
  choose g hg using hG
  refine ⟨⟨fun u => (g u w.I.mu0).symm.trans (e w.I.mu0), fun u a => (g u a).symm.trans (e a)⟩, ⟨⟨e, ?_, ?_, he⟩⟩⟩
  · intro u F
    have h1 : ((g u w.I.mu0).symm.trans (e w.I.mu0)).symm (e w.I.mu0 F) = g u w.I.mu0 F := by
      rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm]
    exact h1 ▸ hg u w.I.mu0 F
  · intro u a F
    have h1 : ((g u a).symm.trans (e a)).symm (e a F) = g u a F := by
      rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm]
    exact h1 ▸ hg u a F

end GlobalTheory.Mem.R3.Rw.PerId
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodMapFormsEquivRowLiftFormsUpperLevelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodMapForms_equiv_rowLiftForms_upperLevel : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Xg : Finset (Gc B w.px → B.LL)) (tr : TrI B w.px) (p : PkB B w.C (Gc B w.px)) (tA : ∀ a : w.I.ι, Tie1 (w.st Z).toD7.what₂.embLL (mAU (w.st Z) w.I hX Xg tr true a) (p.sA true a)), ∃ d : PerD p, Nonempty (PerT w Z hX Xg tr p (fun a x => (tA a).j x) d) := by
  first | exact @GlobalTheory.Mem.R3.Rw.PerId.exists_perT | exact GlobalTheory.Mem.R3.Rw.PerId.exists_perT | (intros; apply GlobalTheory.Mem.R3.Rw.PerId.exists_perT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteFormsAllTuplesCoordinateLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteFormsAllTuplesCoordinateLaws
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.Mats

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]


omit [NumberField K] in
theorem isConjAt_mk {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) :
    Formalism.DivisionValues.IsConjAt (InfinitePlace.mk σ) := fun a => by
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · rw [e]
    exact hσ a
  · rw [e, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, hσ a]


omit [NumberField K] [StarRing K] in
theorem posDef_of_mk {n : ℕ} {σ : K →+* ℂ} {H : Matrix (Fin n) (Fin n) K}
    (h : (H.map (InfinitePlace.mk σ).embedding).PosDef) : (H.map σ).PosDef := by
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · rwa [e] at h
  · rw [e] at h
    have h1 := h.isHermitian
    have e2 : H.map σ = (H.map (ComplexEmbedding.conjugate σ))ᵀ := by
      ext i j
      have := h1.apply j i
      simp only [Matrix.map_apply, ComplexEmbedding.conjugate_coe_eq, Matrix.transpose_apply] at this ⊢
      rw [← this]
      simp
    rw [e2]
    exact h.transpose


omit [NumberField K] in
theorem hform_eq_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H x y = star x ⬝ᵥ H.mulVec y := by
  unfold Formalism.DivisionValues.hform
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply, RingHom.id_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring


omit [NumberField K] in
theorem hform_sa {n : ℕ} {H A : Matrix (Fin n) (Fin n) K} (h : Aᴴ * H = H * A) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H (A.mulVec x) y = Formalism.DivisionValues.hform H x (A.mulVec y) := by
  rw [hform_eq_dot, hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]


omit [NumberField K] [StarRing K] [Fintype G] in
theorem zero_laws [NumberField K] [StarRing K] (σ : K →+* ℂ) {e : MonoidAlgebra K G}
    (hc : e ∈ Subalgebra.center K (MonoidAlgebra K G)) (hi : IsIdempotentElem e) : (Mat1.zero K G).Laws σ e := by
  refine
    { pos := ?_
      lat := ?_
      add := fun _ _ => Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _
      smul := fun _ _ => Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _
      one := Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _
      mul := fun _ _ _ _ => Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _
      E_eq := rfl
      cen := hc
      idem := hi
      sa := ?_ }
  · show ((0 : Matrix (Fin 0) (Fin 0) K).map σ).PosDef
    rw [Subsingleton.elim ((0 : Matrix (Fin 0) (Fin 0) K).map σ) 1]
    exact Matrix.PosDef.one
  · change Submodule.IsFullLattice K (⊤ : Submodule (𝓞 K) (Fin 0 → K))
    refine { toIsLattice := Submodule.IsLattice.of_fg K ?_, span_eq_top := Subsingleton.elim _ _ }
    rw [Subsingleton.elim (⊤ : Submodule (𝓞 K) (Fin 0 → K)) ⊥]
    exact Submodule.fg_bot
  · intro x y
    rw [hform_eq_dot, hform_eq_dot]
    rfl

def lvlMat (S : CSD K) (r : Representation K G S.Forms) (P : Subgroup G) (ψ : P →* Kˣ) (e : MonoidAlgebra K G) : Mat1 K G :=
  ⟨S.lvlDim r P ψ, S.lvlH r P ψ, S.lvlOp r P ψ e, S.lvlNab r P ψ, fun a => S.lvlOp r P ψ a⟩

theorem lvlMat_laws {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) (S : CSD K) {s : ℕ} (hS : S.Good s)
    (hpos : ∀ v : InfinitePlace K, (S.H.map v.embedding).PosDef) (r : Representation K G S.Forms) (hr : S.ActGood r)
    (hrat : S.ActRat r) (P : Subgroup G) (ψ : P →* Kˣ) (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) :
    (lvlMat S r P ψ (idemOf X)).Laws σ (idemOf X) := by
  have h0 := isConjAt_mk hσ
  have hP := (level_idempotent_spec K _ h0 G P ψ).1
  have hI := idempotent_spec K _ h0 G X hX
  have hinj : Function.Injective (S.lvlE r P ψ).mulVec := (image_idempotent_spec K _ _).1
  have hE : ∀ i j, S.lvlE r P ψ i j ∈ Formalism.DivisionValues.cmMax K :=
    image_idempotent_rational K S.dim (S.gaMat r (lvlIdem P ψ)) (gaMat_rat S r hrat _ hP.rat)
  have hproj := (orthogonal_projection_spec K _ h0 S (hpos _) G r hr _ hP.idem hP.selfAdj).1.1
  have hop := level_operator_spec K _ h0 S (hpos _) G r hr P ψ
  refine ⟨posDef_of_mk (cut_posDef S.H (S.lvlE r P ψ) hinj hE (Nat.card P) Nat.card_pos _ (hpos _)),
    (Formalism.DivisionValues.exponent_index_lattice.cut_isFullLattice (S.lvlE r P ψ) hinj _
      (Formalism.DivisionValues.ValuationLatticeField.valLatF_isFullLattice S.I S.I_injective S.Nab hS.nab_isFullLattice)),
    fun a b => ?_, fun c a => ?_, ?_,
    fun a _ b hb => (hop b (Subalgebra.mem_center_iff.1 hb _).symm).2 a, rfl, Subalgebra.mem_center_iff.2 hI.2, hI.1.idem,
    hform_sa ?_⟩
  · show S.lvlOp r P ψ (a + b) = S.lvlOp r P ψ a + S.lvlOp r P ψ b
    unfold CSD.lvlOp
    rw [CSD.gaMat_eq_lift, CSD.gaMat_eq_lift, CSD.gaMat_eq_lift, map_add (f := _), Matrix.mul_add, Matrix.add_mul]
  · show S.lvlOp r P ψ (c • a) = c • S.lvlOp r P ψ a
    unfold CSD.lvlOp
    rw [CSD.gaMat_eq_lift, CSD.gaMat_eq_lift, map_smul, Matrix.mul_smul, Matrix.smul_mul]
  · show S.lvlOp r P ψ 1 = 1
    unfold CSD.lvlOp
    rw [(group_action_matrix_hom K S G r).1, Matrix.mul_one]
    exact hproj
  · have h1 := (hop (idemOf X) (hI.2 _).symm).1
    have h2 := group_action_matrix_adjoint K S G r hr (idemOf X)
    rw [hI.1.selfAdj] at h2
    show (S.lvlOp r P ψ (idemOf X))ᴴ * ((Nat.card P : K)⁻¹ • ((S.lvlE r P ψ)ᴴ * S.H * S.lvlE r P ψ)) =
      ((Nat.card P : K)⁻¹ • ((S.lvlE r P ψ)ᴴ * S.H * S.lvlE r P ψ)) * S.lvlOp r P ψ (idemOf X)
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1,
      Matrix.conjTranspose_mul, Matrix.mul_assoc (S.lvlE r P ψ)ᴴ, h2, Matrix.mul_assoc _ (S.lvlE r P ψ), h1]
    simp only [Matrix.mul_assoc]

end Gen

section Col

variable {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Formalism.L2.Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok) (v0 : InfinitePlace X.K)
  (TU : Finset (Tup X.F X.E X.K S)) (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ) {σ : X.K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a))
  (hirr : ∀ χ ∈ Xg, IsAbsIrrChar χ) (P : Subgroup (Formalism.L2.Col.G0 X.E Pr.vGs R.r)) (ψ : P →* X.Kˣ)

include hσ hirr

theorem rows_laws (τ : TupF TU) :
    (lvlMat ((colIn W Ch sel hX v0 TU Xg S0 xiVal).MtildeCSD τ) ((colIn W Ch sel hX v0 TU Xg S0 xiVal).leftGroupActionRight τ) P ψ
      (idemOf Xg)).Laws σ (idemOf Xg) :=
  lvlMat_laws hσ _ (Formalism.L2.Col.MtildeKCSD_good W Ch sel τ.1 hX _) (fun v => (Formalism.L2.Col.mtildeK_rat W Ch sel τ.1 hX).posH _ v) _
    (Formalism.L2.Col.unipotentActionForms_good W Ch sel τ.1 hX _) (Formalism.L2.Col.unipotentActionForms_rational W Ch sel τ.1 hX _) P ψ Xg hirr

theorem lifts_laws (j : Fin R.m) (τ : TupF TU) :
    (lvlMat ((colIn W Ch sel hX v0 TU Xg S0 xiVal).MtCSD j τ) ((colIn W Ch sel hX v0 TU Xg S0 xiVal).leftGroupActionLift j τ) P ψ
      (idemOf Xg)).Laws σ (idemOf Xg) :=
  lvlMat_laws hσ _ (Formalism.L2.Col.MtKCSD_good W Ch sel τ.1 hX (j.1 + 1) _)
    (fun v => (Formalism.L2.Col.mtK_rat W Ch sel τ.1 hX (j.1 + 1)).posH _ v) _
    (Formalism.L2.Col.unipotentActionClassSum_good W Ch sel τ.1 hX (j.1 + 1) _) (Formalism.L2.Col.unipotentActionClassSum_rational W Ch sel τ.1 hX (j.1 + 1) _) P ψ Xg hirr

end Col

section Fam

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m)
  (P : Subgroup G) (ψ : P →* D.what₂.LLˣ)

theorem rMat_eq (t : T) : rMat A P ψ t = lvlMat (A.MtildeCSD t) (A.leftGroupActionRight t) P ψ (idemOf A.X) := rfl

theorem lMat_eq (i : Fin D.R.m) (t : T) : lMat A P ψ i t = lvlMat (A.MtCSD i t) (A.leftGroupActionLift i t) P ψ⁻¹ (idemOf A.X) := rfl

end Fam

theorem mats_laws : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px), I.Ok → (∀ χ ∈ Xg, IsAbsIrrChar χ) → (∀ b a, (mAU X I hX Xg tr b a).Laws X.toD7.what₂.embLL (idemOf Xg)) ∧ ∀ a j, (mLU X I hX Xg tr a j).Laws X.toD7.what₂.embLL (idemOf Xg) := by
  intro X px I hX Xg tr _ hirr
  refine ⟨fun b a => ?_, fun a j => ?_⟩
  · unfold mAU
    rw [rMat_eq]
    exact rows_laws (X := X.B.fields) (Pr := X.B.primes px) X.B.wts I.Ch I.sel hX (InfinitePlace.mk X.B.embLL) (tuOf I Set.univ) Xg ∅
      (xiValOf I) (σ := X.B.embLL) X.B.starLL_cx hirr _ _ (tAll I a)
  · unfold mLU
    split_ifs with h
    · rw [lMat_eq]
      exact lifts_laws (X := X.B.fields) (Pr := X.B.primes px) X.B.wts I.Ch I.sel hX (InfinitePlace.mk X.B.embLL) (tuOf I Set.univ) Xg ∅
        (xiValOf I) (σ := X.B.embLL) X.B.starLL_cx hirr _ _ _ (tAll I a)
    · have hI := idempotent_central X.B.LL (Gc X.B px) Xg hirr
      exact zero_laws _ (Subalgebra.mem_center_iff.2 hI.2) hI.1

end GlobalTheory.Mem.R3.Rw.Mats

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteFormsAllTuplesCoordinateLawsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteFormsAllTuples_coordinateLaws : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px), I.Ok → (∀ χ ∈ Xg, IsAbsIrrChar χ) → (∀ b a, (mAU X I hX Xg tr b a).Laws X.toD7.what₂.embLL (idemOf Xg)) ∧ ∀ a j, (mLU X I hX Xg tr a j).Laws X.toD7.what₂.embLL (idemOf Xg) := by
  first | exact @GlobalTheory.Mem.R3.Rw.Mats.mats_laws | exact GlobalTheory.Mem.R3.Rw.Mats.mats_laws | (intros; apply GlobalTheory.Mem.R3.Rw.Mats.mats_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsDatumPrescribedTuplesDefinedWeights
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsDatumPrescribedTuplesDefinedWeights
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Ex

@[reducible] def reset {B : Base} {C : Cols B} (W : RowsRest B C) (mt ma : B.places.Pl → C.Tup)
    (hmt : ∀ v, mt (B.places.conj v) = mt v) (hma : ∀ v, ma (B.places.conj v) = ma v)
    (hor : ∀ v, ma v = C.mu0 ∨ ma v = mt v) : RowsRest B C :=
  { W with
    muAt := ma
    muAt_conj := hma
    muTw := mt
    muTw_conj := hmt
    muAt_or := hor
    kaBig := GlobalTheory.Mem.DfGen.kaBigB B
    kaSmall := GlobalTheory.Mem.DfGen.kaSmallB B
    shaLen := GaloisStage.shaTrue B.host
    shaLen_nonneg := GaloisStage.shaTrue_nonneg B.host }

theorem kapDef_of_ka {B : Base} {C : Cols B} (W' : RowsRest B C) (hb : W'.kaBig = GlobalTheory.Mem.DfGen.kaBigB B)
    (hs : W'.kaSmall = GlobalTheory.Mem.DfGen.kaSmallB B) : ∀ V S N G, DV.KapDef (assemble B C W' V S N G) := by
  intro V S N G j _ _ τ
  refine ⟨fun i => ?_, fun c => ?_⟩
  · show ((W'.kaBig j τ i : ℤ) : ℚ) = _
    rw [hb]
    exact (GlobalTheory.Mem.DfGen.aPlusB_int B j τ i).choose_spec.symm
  · show ((W'.kaSmall j τ c : ℤ) : ℚ) = _
    rw [hs]
    show ((-(GlobalTheory.Mem.DfGen.aMinusB_int B j τ c).choose : ℤ) : ℚ) = -GlobalTheory.Mem.DfGen.aMinusB B j τ c
    push_cast
    rw [← (GlobalTheory.Mem.DfGen.aMinusB_int B j τ c).choose_spec]

end GlobalTheory.Mem.R3.Rw.Ex

end

open GlobalTheory.Mem.R3.Rw.Ex in
theorem GlobalTheory.Mem.R3.Rw.exists_rowsRest_muW : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (hX : B.fields.Ok) (Wt : Set B.places.Pl), (∀ v, B.places.conj v ∈ Wt ↔ v ∈ Wt) → ∃ W₀ : RowsRest B w.C, MuW w Wt W₀ ∧ (∀ W' : RowsRest B w.C, W'.kaBig = W₀.kaBig → W'.kaSmall = W₀.kaSmall → ∀ V S N G, DV.KapDef (assemble B w.C W' V S N G)) ∧ GlobalTheory.MemN.ShaOK B.toPre W₀.shaLen := by
  intro B f T w hX Wt hWt
  classical
  obtain ⟨R⟩ := GlobalTheory.Mem.Df.rowsDef_nonempty w.I w.ok w.pins w.l hX
  have hmem : ∀ v, ∃ a, w.I.xi a = T.xiTw f v := fun v => by
    have h : T.xiTw f v ∈ Set.range w.I.xi := by
      rw [w.xi_range]; exact Or.inr ⟨v, rfl⟩
    exact h
  have hconj : ∀ v, T.xiTw f (B.places.conj v) = T.xiTw f v := fun v => by
    unfold TwDat.xiTw
    rw [GlobalTheory.Mem.Top.TwFin.resChar_conj, (T.conj v).1]
  let mt : B.places.Pl → w.C.Tup := fun v => Classical.choose (hmem v)
  have hmt : ∀ v, mt (B.places.conj v) = mt v := fun v => by
    show Classical.choose (hmem (B.places.conj v)) = Classical.choose (hmem v)
    have : ∀ x y (hx : ∃ a, w.I.xi a = x) (hy : ∃ a, w.I.xi a = y), x = y →
        Classical.choose hx = Classical.choose hy := by
      rintro x y hx hy rfl; rfl
    exact this _ _ _ _ (hconj v)
  let ma : B.places.Pl → w.C.Tup := fun v => if v ∈ Wt then mt v else w.C.mu0
  have hma : ∀ v, ma (B.places.conj v) = ma v := fun v => by
    simp only [ma, hWt v, hmt v]
  have hor : ∀ v, ma v = w.C.mu0 ∨ ma v = mt v := fun v => by
    by_cases h : v ∈ Wt
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  refine ⟨reset R.W mt ma hmt hma hor, ⟨fun v => Classical.choose_spec (hmem v), fun v h => if_pos h, fun v h => if_neg h⟩,
    fun W' hb hs => kapDef_of_ka W' hb hs, GlobalTheory.MemN.shaOK_shaTrue B.toPre⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsDatumPrescribedTuplesDefinedWeightsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rowsDatum_prescribedTuples_definedWeights : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (hX : B.fields.Ok) (Wt : Set B.places.Pl), (∀ v, B.places.conj v ∈ Wt ↔ v ∈ Wt) → ∃ W₀ : RowsRest B w.C, MuW w Wt W₀ ∧ (∀ W' : RowsRest B w.C, W'.kaBig = W₀.kaBig → W'.kaSmall = W₀.kaSmall → ∀ V S N G, DV.KapDef (assemble B w.C W' V S N G)) ∧ GlobalTheory.MemN.ShaOK B.toPre W₀.shaLen := by
  first | exact @GlobalTheory.Mem.R3.Rw.exists_rowsRest_muW | exact GlobalTheory.Mem.R3.Rw.exists_rowsRest_muW | (intros; apply GlobalTheory.Mem.R3.Rw.exists_rowsRest_muW <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HdExists
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.HdExist

theorem hd_exists : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → D.host.F = maximalRealSubfield D.host.E → Seed.FrmC.StdLat (Yc D 0) → (∀ i, Seed.FrmC.StdLat (Wc D i)) → ∀ (tup : T → D.what₂.Tup) (tupT : D.what₂.Tup → T), (∀ t, tupT (tup t) = t) → tup A3.A.μ0 = D.what₂.mu0 → ∃ y : Hd R.toRealDat, y.tup = tup ∧ y.tupT = tupT := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hF hY hW tup tupT htt ht0
  have hB : R.toRealDat.BaseW F.lv2 := hP.char.base
  obtain ⟨hTop, hinj⟩ := GlobalTheory.DefiniteMult.topMult_and_extV_injective D G Pl0 T A3.A Ks R.toRealDat F.lv2 hB
  obtain ⟨PY, PW, ιW, hPY, hPW, hiso, hmatch⟩ := GlobalTheory.StdFrameExist.frames_std_matched D hF hY hW
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  exact ⟨⟨tup, tupT, htt, ht0, hm, hTop, hinj, PY, PW, ιW, hiso, hmatch, hF, hPY, hPW⟩, rfl, rfl⟩

end GlobalTheory.Mem.R3.Rw.HdExist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFactorisationScalarReferenceTupleEqOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
noncomputable section

namespace GlobalTheory.Mem.R3.Rw.NumDef

section Gen

variable {R : Ranks} (D : Rows.Data R)

def buSec (u : D.Word) (φ : D.Mu u) (x : D.EE) : ℂ := D.perCol u D.mu0 φ (D.sec D.mu0 x)

def lamTrace (μ : D.Tup) (j : ℕ) (π : D.FT) : ℝ :=
  (LinearMap.trace ℂ (D.Mj j)
    (D.thetaP μ j ∘ₗ D.thetaT μ j ∘ₗ ((D.isot j π).starProjection : D.Mj j →ₗ[ℂ] D.Mj j))).re /
    (Module.finrank ℂ (D.isot j π) : ℝ)

def ZeFact (u : D.Word) (μ : D.Tup) (c : ℂ) : Prop :=
  (∀ (φ : D.Mu u) (F : D.Amb μ), F ∈ D.V0 μ →
    D.perCol u μ φ F = c * buSec D u φ (D.iota μ ((D.Qsp μ).starProjection F))) ∧
  ∃ (φ : D.Mu u) (F : D.Amb μ), F ∈ D.V0 μ ∧ D.perCol u μ φ F ≠ 0

theorem ZeFact.unique {D : Rows.Data R} {u : D.Word} {μ : D.Tup} {c c' : ℂ} (h : ZeFact D u μ c)
    (h' : ZeFact D u μ c') : c = c' := by
  obtain ⟨φ, F, hF, hne⟩ := h.2
  have e1 := h.1 φ F hF
  have e2 := h'.1 φ F hF
  have hb : buSec D u φ (D.iota μ ((D.Qsp μ).starProjection F)) ≠ 0 := fun h0 => hne (by rw [e1, h0, mul_zero])
  exact mul_right_cancel₀ hb (e1.symm.trans e2)

theorem ZeFact.mu0 {D : Rows.Data R} {u : D.Word} {c : ℂ} (h : ZeFact D u D.mu0 c) : c = 1 := by
  obtain ⟨φ, F, hF, hne⟩ := h.2
  have hq : (D.Qsp D.mu0).starProjection F ∈ D.Qsp D.mu0 := (D.Qsp D.mu0).starProjection_apply_mem F
  have e1 := h.1 φ F hF
  have e2 := h.1 φ _ hq.1
  rw [Submodule.starProjection_eq_self_iff.2 hq] at e2
  unfold buSec at e1 e2
  rw [D.sec_iota _ _ hq] at e1 e2
  have hb : D.perCol u D.mu0 φ ((D.Qsp D.mu0).starProjection F) ≠ 0 := fun h0 => hne (by rw [e1, h0, mul_zero])
  exact (mul_eq_right₀ hb).1 e2.symm


open Classical in
def zeVal (u : D.Word) (μ : D.Tup) : D.LLˣ :=
  if μ = D.mu0 then 1 else if h : ∃ z : D.LLˣ, ZeFact D u μ (D.embLL (z : D.LL)) then h.choose else 1

theorem periodFactorisationScalar_referenceTuple_eq_one (u : D.Word) : zeVal D u D.mu0 = 1 := by
  unfold zeVal
  exact if_pos rfl

@[reducible] def modLL (μ : D.Tup) (j : ℕ) : Module (𝓞 D.LL) (D.MtL μ j) :=
  Module.compHom _ (algebraMap (𝓞 D.LL) D.LL)

attribute [local instance] modLL

theorem smulLL (μ : D.Tup) (j : ℕ) (s : 𝓞 D.LL) (x : D.MtL μ j) : s • x = (s : D.LL) • x := rfl

def TjLat (μ : D.Tup) (j : ℕ) : Submodule (𝓞 D.LL) (D.MtL μ j) :=
  Submodule.span (𝓞 D.LL) {x | D.jMt μ j x ∈ D.TjSet μ j}

def TjSpan (μ : D.Tup) (j : ℕ) : Submodule D.LL (D.MtL μ j) := Submodule.span D.LL (TjLat D μ j : Set (D.MtL μ j))

def TjDualLat (μ : D.Tup) (j : ℕ) : Submodule (𝓞 D.LL) (D.MtL μ j) where
  carrier := {x | x ∈ TjSpan D μ j ∧ ∀ a ∈ TjLat D μ j, ∃ c : 𝓞 D.LL,
    inner ℂ (D.jMt μ j a) (D.jMt μ j x) = D.embLL (c : D.LL)}
  add_mem' := by
    rintro x y ⟨hx, h1⟩ ⟨hy, h2⟩
    refine ⟨(TjSpan D μ j).add_mem hx hy, fun a ha => ?_⟩
    obtain ⟨c, hc⟩ := h1 a ha
    obtain ⟨d, hd⟩ := h2 a ha
    exact ⟨c + d, by rw [map_add (f := _), inner_add_right, hc, hd]; simp⟩
  zero_mem' := ⟨(TjSpan D μ j).zero_mem, fun a _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro s x ⟨hx, h1⟩
    refine ⟨by rw [smulLL]; exact (TjSpan D μ j).smul_mem _ hx, fun a ha => ?_⟩
    obtain ⟨c, hc⟩ := h1 a ha
    exact ⟨s * c, by rw [smulLL, LinearMap.map_smulₛₗ, inner_smul_right, hc]; simp⟩

def jwLat (μ : D.Tup) (j : ℕ) (p : Ideal (𝓞 D.LL)) [p.IsPrime] : ℤ :=
  Formalism.HermitianLatticesTheory.lidx p (TjLat D μ j) (TjDualLat D μ j)

end Gen

end GlobalTheory.Mem.R3.Rw.NumDef

namespace GlobalTheory.Mem.R3.Rw.NumDef

section Can

variable {R : Ranks} (Dd : Rows.Data R)

@[reducible] def modMj (j : ℕ) : Module (𝓞 Dd.LL) (Dd.Mj j) :=
  Module.compHom _ (Dd.embLL.comp (algebraMap (𝓞 Dd.LL) Dd.LL))

attribute [local instance] modMj

theorem smulMj (j : ℕ) (s : 𝓞 Dd.LL) (z : Dd.Mj j) : s • z = Dd.embLL (s : Dd.LL) • z := rfl

def latCan (j : ℕ) : Submodule (𝓞 Dd.LL) (Dd.Mj j) where
  carrier := {z | ∃ c : Dd.Mj j → 𝓞 Dd.LL, z = ∑ v ∈ (Dd.MjLat j).gen, Dd.embLL ((c v : 𝓞 Dd.LL) : Dd.LL) • v}
  add_mem' := by
    rintro a b ⟨c, rfl⟩ ⟨d, rfl⟩
    refine ⟨c + d, ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [add_smul]
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro s a ⟨c, rfl⟩
    refine ⟨fun v => s * c v, ?_⟩
    rw [smulMj, Finset.smul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [smul_smul]
    simp

def rngSet (j : ℕ) : Set (Dd.Mj j) := {z | ∃ a : Dd.Mj j → Dd.LL, z = ∑ v ∈ (Dd.MjLat j).gen, Dd.embLL (a v) • v}

attribute [local instance] modLL

def thCan (μ : Dd.Tup) (j : ℕ) : Submodule (𝓞 Dd.LL) (Dd.Mj j) where
  carrier := {z | z ∈ rngSet Dd j ∧ ∃ x ∈ TjLat Dd μ j, z = Dd.thetaP μ j (Dd.jMt μ j x)}
  add_mem' := by
    rintro a b ⟨⟨c, rfl⟩, x, hx, hxa⟩ ⟨⟨d, rfl⟩, y, hy, hyb⟩
    refine ⟨⟨c + d, ?_⟩, x + y, (TjLat Dd μ j).add_mem hx hy, ?_⟩
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp [add_smul]
    · rw [map_add (f := _), map_add (f := _), ← hxa, ← hyb]
  zero_mem' := ⟨⟨0, by simp⟩, 0, (TjLat Dd μ j).zero_mem, by simp⟩
  smul_mem' := by
    rintro s a ⟨⟨c, rfl⟩, x, hx, hxa⟩
    refine ⟨⟨fun v => (s : Dd.LL) * c v, ?_⟩, s • x, (TjLat Dd μ j).smul_mem s hx, ?_⟩
    · rw [smulMj, Finset.smul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [smul_smul, map_mul]
    · rw [smulLL, LinearMap.map_smulₛₗ, LinearMap.map_smul, ← hxa, smulMj]

def ijCan (μ : Dd.Tup) (j : ℕ) (p : Ideal (𝓞 Dd.LL)) [p.IsPrime] : ℤ :=
  Formalism.HermitianLatticesTheory.lidx p (latCan Dd j) (thCan Dd μ j)

end Can

end GlobalTheory.Mem.R3.Rw.NumDef

namespace GlobalTheory.Mem.R3.Rw.NumDef

section Lidx

variable {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']

theorem mem_locP (p : Ideal R) [p.IsPrime] (L : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s ∈ p.primeCompl, s • x ∈ L := Iff.rfl

theorem localization_map_of_injective (p : Ideal R) [p.IsPrime] (f : W →ₗ[R] W') (hf : Function.Injective f)
    (hsat : ∀ (s : R) (y : W'), s ∈ p.primeCompl → s • y ∈ LinearMap.range f → y ∈ LinearMap.range f)
    (A : Submodule R W) : Formalism.HermitianLatticesTheory.localization₂ p (A.map f) = (Formalism.HermitianLatticesTheory.localization₂ p A).map f := by
  ext y
  simp only [mem_locP, Submodule.mem_map]
  constructor
  · rintro ⟨s, hs, a, ha, hay⟩
    obtain ⟨x, rfl⟩ := hsat s y hs ⟨a, hay⟩
    refine ⟨x, ⟨s, hs, ?_⟩, rfl⟩
    have : f (s • x) = f a := by rw [map_smul, hay]
    rw [hf this]; exact ha
  · rintro ⟨x, ⟨s, hs, hx⟩, rfl⟩
    exact ⟨s, hs, s • x, hx, by rw [map_smul]⟩

theorem length_map_inj (f : W →ₗ[R] W') (hf : Function.Injective f) (X Z : Submodule R W) :
    Module.length R (↥(Z.map f) ⧸ (X.map f).comap (Z.map f).subtype) =
      Module.length R (↥Z ⧸ X.comap Z.subtype) := by
  symm
  refine LinearEquiv.length_eq
    (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf Z) ?_)
  ext ⟨w, hw⟩
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hw
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨⟨z', hz'⟩, hz'X, he⟩
    have : f z' = f z := congrArg Subtype.val he
    rw [← hf this]
    exact ⟨z', hz'X, rfl⟩
  · rintro ⟨z', hz'X, he⟩
    refine ⟨⟨z, hz⟩, ?_, ?_⟩
    · have := hf he
      simpa [this] using hz'X
    · rfl

theorem lidx_map_inj (p : Ideal R) [p.IsPrime] (f : W →ₗ[R] W') (hf : Function.Injective f)
    (hsat : ∀ (s : R) (y : W'), s ∈ p.primeCompl → s • y ∈ LinearMap.range f → y ∈ LinearMap.range f)
    (A B : Submodule R W) : Formalism.HermitianLatticesTheory.lidx p (A.map f) (B.map f) = Formalism.HermitianLatticesTheory.lidx p A B := by
  unfold Formalism.HermitianLatticesTheory.lidx Formalism.HermitianLatticesTheory.locLen
  rw [← Submodule.map_inf f hf, localization_map_of_injective p f hf hsat, localization_map_of_injective p f hf hsat,
    localization_map_of_injective p f hf hsat, length_map_inj f hf, length_map_inj f hf]

end Lidx

section Tr

attribute [local instance] modMj modLL

variable (D : D7) (X : DivX D)

def jMO (j : ℕ) : (X.MjH j).V →ₗ[𝓞 D.what₂.LL] D.what₂.Mj j where
  toFun := X.jM j
  map_add' := map_add _
  map_smul' s x := by
    rw [← algebraMap_smul D.what₂.LL s x, LinearMap.map_smulₛₗ]
    rfl

theorem exists_jM (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (a : D.what₂.Mj j → D.what₂.LL) :
    ∃ x, X.jM j x = ∑ v ∈ (D.what₂.MjLat j).gen, D.what₂.embLL (a v) • v := by
  refine Finset.sum_induction _ (fun z => ∃ x, X.jM j x = z) ?_ ?_ ?_
  · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  · exact ⟨0, map_zero _⟩
  · intro v hv
    obtain ⟨x, hx⟩ := X.MjLat_sub j h1 h2 v hv
    exact ⟨a v • x, by rw [LinearMap.map_smulₛₗ, hx]⟩

theorem jM_mem_rng (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (y : (X.MjH j).V) : X.jM j y ∈ rngSet D.what₂ j := by
  have hy : y ∈ Submodule.span D.what₂.LL ((X.MjH j).L : Set (X.MjH j).V) := by
    rw [(X.MjH_good j).2.2]; trivial
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc⟩ := (X.jM_lat j h1 h2 x).1 hx
    exact ⟨fun v => ((c v : 𝓞 D.what₂.LL) : D.what₂.LL), hc⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [map_add (f := _), ha, hb, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [add_smul]
  | smul r x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨fun v => r * a v, ?_⟩
    rw [LinearMap.map_smulₛₗ, ha, Finset.smul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [smul_smul, map_mul]

theorem lat_map (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : (X.MjH j).L.map (jMO D X j) = latCan D.what₂ j := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := (X.jM_lat j h1 h2 x).1 hx
    exact ⟨c, hc⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨x, hx⟩ := exists_jM D X j h1 h2 (fun v => ((c v : 𝓞 D.what₂.LL) : D.what₂.LL))
    exact ⟨x, (X.jM_lat j h1 h2 x).2 ⟨c, hx⟩, hx⟩

theorem th_map (μ : D.what₂.Tup) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    (Idx.thTj X μ j).map (jMO D X j) = thCan D.what₂ μ j := by
  ext z
  constructor
  · rintro ⟨y, ⟨x, hx, hxy⟩, rfl⟩
    exact ⟨jM_mem_rng D X j h1 h2 y, x, hx, hxy⟩
  · rintro ⟨⟨a, ha⟩, x, hx, hxz⟩
    obtain ⟨y, hy⟩ := exists_jM D X j h1 h2 a
    refine ⟨y, ⟨x, hx, ?_⟩, ?_⟩
    · rw [hy, ← ha, hxz]
    · show X.jM j y = z
      rw [hy, ← ha]

theorem ijIdx_eq_can (μ : D.what₂.Tup) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (w : D.what₂.places.Pl) :
    Idx.IjIdx X μ j w = ijCan D.what₂ μ j (D.plEq w).asIdeal := by
  unfold Idx.IjIdx ijCan
  rw [← lat_map D X j h1 h2, ← th_map D X μ j h1 h2, lidx_map_inj _ _ (Idx.jM_inj X j)]
  rintro s y hs ⟨a, ha⟩
  have hs0 : (s : D.what₂.LL) ≠ 0 := by
    intro h0
    apply hs
    have : s = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
    rw [this]
    exact zero_mem _
  refine ⟨(s : D.what₂.LL)⁻¹ • a, ?_⟩
  have ha' : X.jM j a = D.what₂.embLL (s : D.what₂.LL) • y := ha
  show X.jM j ((s : D.what₂.LL)⁻¹ • a) = y
  rw [LinearMap.map_smulₛₗ, ha', smul_smul, ← map_mul, inv_mul_cancel₀ hs0, map_one, one_smul]

end Tr

theorem zeOf_eq {R : Ranks} (Dd : Rows.Data R) (u : Dd.Word) (μ : Dd.Tup) (c : ℂ)
    (h : ZeFact Dd u μ c) (hc : ∃ z : Dd.LL, Dd.embLL z = c) :
    Dd.embLL (zeVal Dd u μ : Dd.LL) = c := by
  by_cases hμ : μ = Dd.mu0
  · subst hμ
    rw [periodFactorisationScalar_referenceTuple_eq_one, h.mu0]; simp
  · obtain ⟨z, hz'⟩ := hc
    have hc0 : c ≠ 0 := by
      obtain ⟨φ, F, hF, hne⟩ := h.2
      intro h0
      exact hne (by rw [h.1 φ F hF, h0, zero_mul])
    have hz0 : z ≠ 0 := fun h0 => hc0 (by rw [← hz', h0, map_zero])
    have hex : ∃ z : Dd.LLˣ, ZeFact Dd u μ (Dd.embLL (z : Dd.LL)) :=
      ⟨Units.mk0 z hz0, by simpa [hz'] using h⟩
    unfold zeVal
    rw [if_neg hμ, dite_eq_left hex]
    exact hex.choose_spec.unique h

end GlobalTheory.Mem.R3.Rw.NumDef

namespace GlobalTheory.Mem.R3.Rw.NumDef

variable {B : Base} {C : Cols B} {G : Type} [Group G]

def nums0 (p : PkB B C G) (W₀ : RowsRest B C) : Nums p W₀ where
  Bu := fun _ _ _ => 0
  linL := fun _ _ => ⟨fun _ _ => (add_zero 0).symm, fun _ _ => (smul_zero _).symm⟩
  linR := fun _ _ => ⟨fun _ _ => (add_zero 0).symm, fun _ _ => (smul_zero _).symm⟩
  ze := fun _ _ => 1
  rowsRest_wordColumnUnit_baseTuple := fun _ => rfl
  lamP := fun _ _ _ => 0
  Ij := fun _ _ _ => 0
  jw := fun _ _ _ => 0

abbrev data0 (p : PkB B C G) (e : PerD p) (W₀ : RowsRest B C) : Rows.Data B.R :=
  (p.what₂ e W₀ (nums0 p W₀) (fun _ _ => 0) (fun _ _ => le_refl 0)).what₂

theorem periodAgainstColumnForm_referenceTuple_eq (p : PkB B C G) (e : PerD p) (W₀ : RowsRest B C) (u : B.Word) (φ : W₀.Mu u)
    (F : (p.sA true C.mu0).A.T) :
    perOf p e W₀ u C.mu0 φ F = (C.mem u).P.PtilCol ((W₀.eMu u φ : (C.mem u).A.Mram) :
      (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) ((e.e0 u).symm F) := by
  unfold perOf
  rw [dite_eq_left rfl]
  rfl

theorem perOf_linL (p : PkB B C G) (e : PerD p) (W₀ : RowsRest B C) (u : B.Word) (F : (p.sA true C.mu0).A.T) :
    IsLinearMap ℂ (fun φ : W₀.Mu u => perOf p e W₀ u C.mu0 φ F) := by
  constructor
  · intro φ ψ
    simp only [periodAgainstColumnForm_referenceTuple_eq, PeriodMap.PtilCol, PeriodMap.Ptil, map_add (f := _), Submodule.coe_add,
      Formalism.BasicNotions.Examples₂.NZ.col_add, LinearMap.add_apply]
  · intro s φ
    simp only [periodAgainstColumnForm_referenceTuple_eq, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, Submodule.coe_smul,
      Formalism.BasicNotions.Examples₂.NZ.col_smul, LinearMap.smul_apply]

theorem perOf_linR (p : PkB B C G) (e : PerD p) (W₀ : RowsRest B C) (u : B.Word) (φ : W₀.Mu u) :
    IsLinearMap ℂ (fun F : (p.sA true C.mu0).A.T => perOf p e W₀ u C.mu0 φ F) := by
  constructor
  · intro F F'
    simp only [periodAgainstColumnForm_referenceTuple_eq, PeriodMap.PtilCol, PeriodMap.Ptil, map_add (f := _)]
  · intro s F
    simp only [periodAgainstColumnForm_referenceTuple_eq, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul]

def numsOf (p : PkB B C G) (e : PerD p) (W₀ : RowsRest B C) : Nums p W₀ where
  Bu := buSec (data0 p e W₀)
  linL := fun u F => perOf_linL p e W₀ u _
  linR := fun u φ => by
    have h := perOf_linR p e W₀ u φ
    exact ⟨fun x y => (congrArg (perOf p e W₀ u C.mu0 φ) (((data0 p e W₀).sec C.mu0).map_add x y)).trans (h.map_add _ _),
      fun s x => (congrArg (perOf p e W₀ u C.mu0 φ) (((data0 p e W₀).sec C.mu0).map_smul s x)).trans (h.map_smul _ _)⟩
  ze := zeVal (data0 p e W₀)
  rowsRest_wordColumnUnit_baseTuple := periodFactorisationScalar_referenceTuple_eq_one (data0 p e W₀)
  lamP := lamTrace (data0 p e W₀)
  Ij := fun μ j w => @ijCan _ (data0 p e W₀) μ j (w : HeightOneSpectrum (𝓞 B.LL)).asIdeal (HeightOneSpectrum.isPrime _)
  jw := fun μ j w => @jwLat _ (data0 p e W₀) μ j (w : HeightOneSpectrum (𝓞 B.LL)).asIdeal (HeightOneSpectrum.isPrime _)

end GlobalTheory.Mem.R3.Rw.NumDef

namespace GlobalTheory.Mem.R3.Rw


open NumDef in
theorem exists_nums_numOK : ∀ (B : Base) (C : Cols B) (G : Type) [Group G] (p : PkB B C G) (e : PerD p) (W₀ : RowsRest B C),
    ∃ n : Nums p W₀, ∀ η hη V S N G', NumOK (assemble B C (p.what₂ e W₀ n η hη) V S N G') := by
  intro B C G _ p e W₀
  refine ⟨numsOf p e W₀, fun η hη V S N G' => ?_⟩
  have hd : ∀ (μ : C.Tup) j,
      (data0 p e W₀).downTo μ j = ((p.what₂ e W₀ (numsOf p e W₀) η hη).what₂).downTo μ j := by
    intro μ j
    induction j with
    | zero => rfl
    | succ j ih =>
      simp only [Rows.Data.downTo, ih]
  have hi : ∀ μ : C.Tup, (data0 p e W₀).iota μ = ((p.what₂ e W₀ (numsOf p e W₀) η hη).what₂).iota μ := by
    intro μ
    simp only [Rows.Data.iota, hd]
  have hv : ∀ μ : C.Tup, (data0 p e W₀).V0 μ = ((p.what₂ e W₀ (numsOf p e W₀) η hη).what₂).V0 μ := by
    intro μ
    rfl
  have hq : ∀ μ : C.Tup, (data0 p e W₀).Qsp μ = ((p.what₂ e W₀ (numsOf p e W₀) η hη).what₂).Qsp μ := by
    intro μ
    simp only [Rows.Data.Qsp, Rows.Data.Usp, hv, hi]
  have hs : ∀ μ : C.Tup, (data0 p e W₀).sec μ = ((p.what₂ e W₀ (numsOf p e W₀) η hη).what₂).sec μ := by
    intro μ
    have helper (q₁ q₂ : Submodule ℂ ((p.sA true μ).A.T))
        (f₁ f₂ : (p.sA true μ).A.T →ₗ[ℂ] (p.ch true).EE.T)
        (hf₁ : Function.Injective (f₁.domRestrict q₁))
        (hf₂ : Function.Injective (f₂.domRestrict q₂))
        (hq' : q₁ = q₂) (hf' : f₁ = f₂) :
        q₁.subtype ∘ₗ (LinearEquiv.ofInjective (f₁.domRestrict q₁) hf₁).symm.toLinearMap ∘ₗ
            (LinearMap.range (f₁.domRestrict q₁)).orthogonalProjectionOnto.toLinearMap =
        q₂.subtype ∘ₗ (LinearEquiv.ofInjective (f₂.domRestrict q₂) hf₂).symm.toLinearMap ∘ₗ
            (LinearMap.range (f₂.domRestrict q₂)).orthogonalProjectionOnto.toLinearMap := by
      subst q₂
      subst f₂
      rfl
    exact helper _ _ _ _ ((data0 p e W₀).iotaQ_inj μ)
      (((p.what₂ e W₀ (numsOf p e W₀) η hη).what₂).iotaQ_inj μ) (hq μ) (hi μ)
  exact
  { lam := fun μ j _ _ π _ => rfl
    bu := fun u φ x => by
      change buSec (data0 p e W₀) u φ x = perOf p e W₀ u C.mu0 φ (((p.what₂ e W₀ (numsOf p e W₀) η hη).what₂).sec C.mu0 x)
      simp only [buSec, hs]
    ze := fun u μ c h1 h2 h3 => by
      apply zeOf_eq (data0 p e W₀) u μ c
      · constructor
        · intro φ F hF
          have ht := h1 φ F (by change F ∈ ((p.what₂ e W₀ (numsOf p e W₀) η hη).what₂).V0 μ; rw [← hv μ]; exact hF)
          change perOf p e W₀ u μ φ F = c * buSec (data0 p e W₀) u φ (((p.what₂ e W₀ (numsOf p e W₀) η hη).what₂).iota μ (((p.what₂ e W₀ (numsOf p e W₀) η hη).what₂).Qsp μ |>.starProjection F)) at ht
          change perOf p e W₀ u μ φ F = c * buSec (data0 p e W₀) u φ ((data0 p e W₀).iota μ ((data0 p e W₀).Qsp μ |>.starProjection F))
          rw [hi μ, hq μ]
          exact ht
        · exact h2
      · exact h3
    idx := fun Y => ⟨fun μ j w h1 h2 => (ijIdx_eq_can _ Y μ j h1 h2 w).symm, fun μ j w _ _ => rfl⟩
    jw := fun μ j w _ _ => rfl }

end GlobalTheory.Mem.R3.Rw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyRowLiftFamilyOverColumnChoices
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.PkExist

theorem rowPk_nonempty : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z₀ : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z₀ : Dat (w.st Z₀) w.I hX T Wt), Inputs (w.D Z₀) → (w.D Z₀).host.F = maximalRealSubfield (w.D Z₀).host.E → Seed.FrmC.StdLat (Yc (w.D Z₀) 0) → (∀ i, Seed.FrmC.StdLat (Wc (w.D Z₀) i)) → Holds z₀.R z₀.F → (∀ v, B.places.conj v ∈ Wt ↔ v ∈ Wt) → Nonempty (RowPk w z₀) := by
  intro B f T w Z₀ hX Wt z₀ hIn hF hY hW hH hWt
  classical
  letI : Algebra z₀.core.Q.c.F (w.D Z₀).what₂.LL := z₀.alg
  let tupT : w.I.ι → TupU w.I (usedOf w.I T Wt) := fun a =>
    if h : ∃ t, ixOf w.I (usedOf w.I T Wt) t = a then h.choose else mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))
  have htt : ∀ t, tupT (ixOf w.I (usedOf w.I T Wt) t) = t := fun t => by
    have h : ∃ t', ixOf w.I (usedOf w.I T Wt) t' = ixOf w.I (usedOf w.I T Wt) t := ⟨t, rfl⟩
    simp only [tupT, dif_pos h]
    exact ixOf_injective w.I _ h.choose_spec
  obtain ⟨y, hy, -⟩ := HdExist.hd_exists (w.D Z₀) (Gc B w.px) (PlS B w.px) (PlI B w.px) (TupU w.I (usedOf w.I T Wt))
    (famR (w.st Z₀) w.I hX (usedOf w.I T Wt) z₀.Xg z₀.tr) z₀.core.Q.c.F z₀.R z₀.F z₀.cG z₀.pins hF hY hW
    (ixOf w.I (usedOf w.I T Wt)) tupT htt (ixOf_mu0F w.I _)
  obtain ⟨hLA, hLL⟩ := GlobalTheory.T.definiteFormsAllTuples_coordinateLaws (w.st Z₀) w.px w.I hX z₀.Xg z₀.tr w.ok z₀.good.irr
  have hU := GlobalTheory.T.formsCoordinates_indexOfFamilyTuple_eq (w.st Z₀) w.px w.I hX (usedOf w.I T Wt) z₀.Xg z₀.tr
  have hO : ∀ o : (w.D Z₀).what₂.O, ∃ k : z₀.core.Q.c.F, algebraMap z₀.core.Q.c.F (w.D Z₀).what₂.LL k = (w.D Z₀).what₂.OtoLL o :=
    fun o => z₀.Ks_le _ (SetLike.coe_mem _)
  obtain ⟨p, hpL, ⟨t⟩⟩ := GlobalTheory.T.exists_rowLiftReading_definiteFormCoordinates (w.D Z₀) (Gc B w.px) (PlS B w.px) (PlI B w.px) (TupU w.I (usedOf w.I T Wt))
    (famR (w.st Z₀) w.I hX (usedOf w.I T Wt) z₀.Xg z₀.tr) z₀.core.Q.c.F z₀.R z₀.F z₀.cG hO hIn z₀.pins hH y
    (mAU (w.st Z₀) w.I hX z₀.Xg z₀.tr) (mLU (w.st Z₀) w.I hX z₀.Xg z₀.tr) hLA hLL
    (fun b t => by rw [hy]; exact (hU t).1 b) (fun i t => by rw [hy]; exact (hU t).2 i)
  obtain ⟨d, ⟨per⟩⟩ := GlobalTheory.T.exists_periodMapForms_equiv_rowLiftForms_upperLevel B f T w Z₀ hX z₀.Xg z₀.tr p (fun a => t.tA true a)
  obtain ⟨W₀, hmu, hkap, hsha⟩ := GlobalTheory.T.exists_rowsDatum_prescribedTuples_definedWeights B f T w hX Wt hWt
  obtain ⟨n, hn⟩ := exists_nums_numOK B w.C (Gc B w.px) p d W₀
  exact ⟨{
    y := y
    tup := fun t => (by rw [hy])
    p := p
    t := t
    mL := fun a j => (by rw [hpL])
    e := d
    per := per
    W₀ := W₀
    mu := hmu
    sha := hsha
    n := n
    kap := fun η hη V S N G' => hkap (p.what₂ d W₀ n η hη) rfl rfl V S N G'
    num := hn }⟩

end GlobalTheory.Mem.R3.Rw.PkExist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyRowLiftFamilyOverColumnChoicesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_rowLiftFamily_over_columnChoices : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z₀ : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z₀ : Dat (w.st Z₀) w.I hX T Wt), Inputs (w.D Z₀) → (w.D Z₀).host.F = maximalRealSubfield (w.D Z₀).host.E → Seed.FrmC.StdLat (Yc (w.D Z₀) 0) → (∀ i, Seed.FrmC.StdLat (Wc (w.D Z₀) i)) → Holds z₀.R z₀.F → (∀ v, B.places.conj v ∈ Wt ↔ v ∈ Wt) → Nonempty (RowPk w z₀) := by
  first | exact @GlobalTheory.Mem.R3.Rw.PkExist.rowPk_nonempty | exact GlobalTheory.Mem.R3.Rw.PkExist.rowPk_nonempty | (intros; apply GlobalTheory.Mem.R3.Rw.PkExist.rowPk_nonempty <;> assumption)
end

module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverReadingEqPowMulMovedFrameReading
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ZeroDegreeOfPinFor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFramedPointOverMovedBaseFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFramedPointOverMovedBaseFrame
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverFrameOver

open GlobalTheory.CoverFrameRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem un_over : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (h : GA D (T.V j σ)) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) → ∀ (x : Frame (C.U₂.X (C.dict₂ h).1).Ψ D.R.r) (x' : Frame ((T.U j σ).X (T.dict j σ h).1).Ψ D.R.r) (hx : x ∈ (C.U₂.X (C.dict₂ h).1).dom) (hx' : x' ∈ ((T.U j σ).X (T.dict j σ h).1).dom), (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → CategoryTheory.CategoryStruct.comp ((C.U₂.un (C.dict₂ h).1 ⟨x, hx⟩).x : Sp ℂ ⟶ C.d.Xo₂.X) C.d.r = (((T.U j σ).un (T.dict j σ h).1 ⟨x', hx'⟩).x : Sp ℂ ⟶ (T.Q.Xo j).X) ∧ ∀ (τ : D.host.E →+* ℂ) (i : Fin ((T.Q.Dw j).mult τ)), CategoryTheory.CategoryStruct.comp ((C.U₂.un (C.dict₂ h).1 ⟨x, hx⟩).u τ i : Sp (DualNumber ℂ) ⟶ C.d.Xo₂.univ.t.G.left) C.d.m.φ = (((T.U j σ).un (T.dict j σ h).1 ⟨x', hx'⟩).u τ i : Sp (DualNumber ℂ) ⟶ (T.Q.Xo j).univ.t.G.left) := by
  intro D T hT j hj σ hσ C hC h γ hlat hiso hfr x x' hx hx' hxx
  obtain ⟨hr₁, g₁, e₁, F₁, ik₁, φ₁, th₁, -, -, hth₁, ⟨hEF₁, hper₁⟩, hd₁⟩ := hT.adPin j hj σ hσ
  obtain ⟨hlev, hA₂, hσ₂, hU₂, hdom, hr₂, g₂, e₂, F₂, ik₂, φ₂, th₂, hW₂, hth₂, ⟨hEF₂, hper₂⟩, hd₂⟩ := hC
  obtain ⟨hr₀, hW₁⟩ := hT.modelW j hj σ hσ
  have hU₁ := hT.unf j hj σ hσ
  have hA : T.Q.l.A = 1 := hT.pins.2.1.2
  obtain ⟨-, hpq, -, hq⟩ := GlobalTheory.Member.exists_iotaOK D T.Q hT.pins j hj
  obtain ⟨γ₁, hγ₁, hL₁, hm₁, hf₁⟩ := hd₁ h
  obtain ⟨γ₂, hγ₂, -, hm₂, hf₂⟩ := hd₂ h
  have hΨ : ∀ τ, τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ ↔ τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ := fun τ =>
    ((hU₁.2.1 _).2 τ).trans ((hU₂.2.1 _).2 τ).symm
  obtain ⟨δ, hδf, hδm⟩ := move_mark (T.V j σ) hr₁ h γ₁ γ₂ hγ₁ hγ₂ _ hL₁
  have hγδ : (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) = δ := by
    obtain ⟨τ, t₂⟩ : ∃ τ, τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ := by
      by_cases h0 : D.host.φ₀ ∈ (C.U₂.X (C.dict₂ h).1).Ψ
      · exact ⟨_, h0⟩
      · exact ⟨_, not_not.1 (mt ((C.U₂.X (C.dict₂ h).1).cmType _).2 h0)⟩
    have t₁ := (hΨ τ).2 t₂
    have a₂ := hf₂ ⟨τ, t₂⟩
    have a₁ := hf₁ ⟨τ, t₁⟩
    rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at a₂
    have a₃ := a₁.trans ((hδf τ _ (hth₁ _ ⟨τ, t₁⟩) _).trans (congrArg (_ * ·) a₂.symm))
    have a₄ := (hfr τ t₂ t₁).symm.trans a₃
    have hu : IsUnit (mat (C.dict₂ h).2 ⟨τ, t₂⟩) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit (hdom h ⟨τ, t₂⟩).1)
    exact Matrix.map_injective τ.injective (hu.mul_right_cancel a₄)
  obtain ⟨f, hf⟩ := exists_latEquiv _ _ γ hlat
  let gam := (φ₂ (C.dict₂ h).1).trans (f.trans (φ₁ (T.dict j σ h).1).symm)
  have hgam : ∀ a, (φ₁ (T.dict j σ h).1 (gam a) : Fin D.R.r → D.host.E) =
      (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ (φ₂ (C.dict₂ h).1 a : Fin D.R.r → D.host.E) := fun a =>
    (congrArg Subtype.val ((φ₁ (T.dict j σ h).1).apply_symm_apply _)).trans (hf _)
  obtain ⟨P₁, hP₁, hp₁, hu₁, hv₁⟩ := hper₁ _ ⟨x', hx'⟩
  obtain ⟨P₂, hP₂, hp₂, hu₂, hv₂⟩ := hper₂ _ ⟨x, hx⟩
  have hle : KA T.Q.l ≤ KA C.d.l₂ := by rw [KA, KA, hA, hA₂]
  have hrel : ∀ τ : D.host.E →+* ℂ, relab T.Q.c σ τ = relab C.d.c₂ C.σ₂ τ := fun τ => by
    ext a
    exact (RingHom.congr_fun hσ₂ _).symm.trans (congrArg C.σ₂ (Subtype.ext rfl))
  obtain ⟨k₁, k₂⟩ := point_over C.d hlev (by omega) hA hle
    (RingHom.ext fun a => (congrArg C.σ₂ (Subtype.ext rfl)).trans
      (RingHom.congr_fun hσ₂ ((IntermediateField.inclusion T.Q.c.le).toRingHom a)))
    e₁ e₂ F₁ F₂ _ _ hp₁ hp₂ gam
    (fun a b => by
      have := (hEF₁ _ (gam a) (gam b)).trans (Eq.trans (by rw [hgam, hgam, hiso, (hW₁ _).2, (hW₂ _).2])
        (hEF₂ _ a b).symm)
      exact_mod_cast this)
    (fun a ha => by
      have b₂ := hm₂ a ha
      rw [hlev.2.1] at b₂
      obtain ⟨u, hu, e⟩ := hδm T.Q.l.M C.d.pd (by have := T.Q.l.three_le; omega) _ _ _
        (hm₁ a (Submodule.smul_mono_left (Ideal.map_mono hlev.1.2.1) ha)) b₂
      refine ⟨(φ₁ _).symm ⟨u, hu⟩, (φ₁ (T.dict j σ h).1).injective (Subtype.ext ?_)⟩
      rw [hgam, hγδ, e, map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply]
      rfl)
    (fun a i => by
      rw [hP₁, hP₂, hgam, Equiv.apply_symm_apply, hrel]
      exact perFr_move _ _ hΨ ((hU₁.2.1 _).1.trans (hU₂.2.1 _).1.symm) ((hW₁ _).1.trans (hW₂ _).1.symm) γ hiso x x'
        hxx _ _ _)
  exact ⟨by rw [hu₁, hu₂]; exact k₁, fun τ i => k₂ ⟨τ, i⟩ _ _ (hv₁ τ i) (hv₂ τ i)⟩

end GlobalTheory.CoverFrameOver
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFramedPointOverMovedBaseFrameStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverFramedPoint_over_moved_base_frame : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (h : GA D (T.V j σ)) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) → ∀ (x : Frame (C.U₂.X (C.dict₂ h).1).Ψ D.R.r) (x' : Frame ((T.U j σ).X (T.dict j σ h).1).Ψ D.R.r) (hx : x ∈ (C.U₂.X (C.dict₂ h).1).dom) (hx' : x' ∈ ((T.U j σ).X (T.dict j σ h).1).dom), (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → CategoryTheory.CategoryStruct.comp ((C.U₂.un (C.dict₂ h).1 ⟨x, hx⟩).x : Sp ℂ ⟶ C.d.Xo₂.X) C.d.r = (((T.U j σ).un (T.dict j σ h).1 ⟨x', hx'⟩).x : Sp ℂ ⟶ (T.Q.Xo j).X) ∧ ∀ (τ : D.host.E →+* ℂ) (i : Fin ((T.Q.Dw j).mult τ)), CategoryTheory.CategoryStruct.comp ((C.U₂.un (C.dict₂ h).1 ⟨x, hx⟩).u τ i : Sp (DualNumber ℂ) ⟶ C.d.Xo₂.univ.t.G.left) C.d.m.φ = (((T.U j σ).un (T.dict j σ h).1 ⟨x', hx'⟩).u τ i : Sp (DualNumber ℂ) ⟶ (T.Q.Xo j).univ.t.G.left) := by
  first | exact @GlobalTheory.CoverFrameOver.un_over | exact GlobalTheory.CoverFrameOver.un_over | (intros; apply GlobalTheory.CoverFrameOver.un_over <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateDefiniteFormsDescendNumberField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateDefiniteFormsDescendNumberField
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjDesc


set_option maxHeartbeats 1600000 in
theorem vals : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (a : Tp) (x₀ : A.fam.amb.FL i (tup a)) (h : GA D (Vc D i)), ∃ x : VsV D i M.c'.F, (R.HV i (tup a)).e (jVx R i (tup a) x₀) (fin _ h) = M.c0' x := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC i Tp tup M hP a x₀ h
  obtain ⟨_, _, _, hT, hc⟩ := hP.lift.c0
  obtain ⟨x, hx⟩ := GlobalTheory.RationalValues.placeEx R i M.jL (inC M.c') (tup a) (fun _ : Unit => h) M.c0' hC.models.jV hT hc hC.lev
    hC.grp.chiW hC.fam.pl_onto hC.fam.muVal x₀
  exact ⟨x (), hx ()⟩


set_option maxHeartbeats 1600000 in
theorem c_inj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → Function.Injective c := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ i Tp tup M hP c hc
  obtain ⟨gramR, c0R, c0L, hFT, hC0⟩ := hP.lift.c0
  have hfield : (inC M.c').comp M.jL = D.what₂.embLL := hP.lift.field
  have hbas : ∀ j, c (GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) j)) =
      c0L i (bVV D.what₂.LL (lamV D i) j) := fun j => by
    obtain ⟨v', hv', hcv'⟩ := hC0 (bVV D.what₂.LL (lamV D i) j)
    refine (hc v' _ ?_).trans hcv'
    rw [GlobalTheory.CoefModel.mapVV_coe, hv', MvPolynomial.map_map, hfield]
  have hli : LinearIndependent ℂ fun j => c (GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) j)) := by
    have h := (hFT.mapL i).2.1
    simp only [← hbas] at h
    exact h
  have hli0 := GlobalTheory.CoefModel.linearIndependent_mapVV D.what₂.embLL (lamV D i)
  have hsp0 := GlobalTheory.CoefModel.span_mapVV D.what₂.embLL (lamV D i)
  let B := Module.Basis.mk hli0 hsp0.ge
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have hs := B.sum_repr z
  have h0 : ∑ j, B.repr z j • c (GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) j)) = 0 := by
    calc _ = c (∑ j, B.repr z j • B j) := by
            set_option synthInstance.maxHeartbeats 100000 in
              rw [map_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_smul, Module.Basis.mk_apply]
      _ = 0 := by rw [hs, hz]
  have hc0 := Fintype.linearIndependent_iff.1 hli _ h0
  rw [← hs]
  exact Finset.sum_eq_zero fun j _ => by rw [hc0 j, zero_smul]


set_option maxHeartbeats 4000000 in
theorem conj_desc : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → (∀ t x, ((R.xi (tup t) x : Circle) : ℂ) ∈ M.c'.F) → ∀ a b : Tp, ConjTup R τ (tup a) (tup b) → ∀ (y : (R.HV i (tup a)).H) (y' : (R.HV i (tup b)).H), ConjForm R i τ c (tup a) (tup b) y y' → ∃ (n : ℕ) (α : Fin n → ℂ) (ys : Fin n → (R.HV i (tup a)).H) (ys' : Fin n → (R.HV i (tup b)).H), y = ∑ k, α k • ys k ∧ y' = ∑ k, τ (α k) • ys' k ∧ ∀ k (h : GA D (Vc D i)), ∃ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) ∧ (R.HV i (tup a)).e (ys k) (fin _ h) = M.c0' x ∧ (R.HV i (tup b)).e (ys' k) (fin _ h) = M.c0' x' := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hFW i Tp tup M hP τ ta hta hFix c hc hxi a b hab y y' hy
  obtain ⟨φ, hφs, hφ⟩ := GlobalTheory.T.exists_galoisConj_definiteForms_semilinearEquiv D G Pl0 T0 A T R F κ v₀ hC hFW i Tp tup M hP c hc τ (tup a) (tup b) hFix hab
  have hy' : y' = φ y := (hφ y y').1 hy
  have hmem : y ∈ Submodule.span ℂ (Set.range (R.jV i (tup a))) := by
    rw [GlobalTheory.HeckeClassSums.span_jV hC.models.HV hC.models.jV i (tup a)]; exact Submodule.mem_top
  obtain ⟨n, α, g, hg⟩ := Submodule.mem_span_set'.1 hmem
  have hinj := c_inj D G Pl0 T0 A T R κ v₀ i Tp tup M hP c hc
  refine ⟨n, α, fun k => (g k : (R.HV i (tup a)).H), fun k => φ (g k : (R.HV i (tup a)).H), hg.symm, ?_, ?_⟩
  · subst hy' hg
    exact (map_sum φ _ _).trans (Finset.sum_congr rfl fun k _ => hφs _ _)
  · intro k h
    have hk : ∃ x₀ : A.fam.amb.FL i (tup a), R.jV i (tup a) x₀ = (g k : (R.HV i (tup a)).H) := (g k).2
    obtain ⟨x₀, hx₀⟩ := hk
    have hv := vals D G Pl0 T0 A T R F κ v₀ hC i Tp tup M hP
    have hv2 := hv a x₀ h
    let x := hv2.choose
    have hx : (R.HV i (tup a)).e (jVx R i (tup a) x₀) (fin _ h) = M.c0' x := hv2.choose_spec
    have hx' : ((g k : (R.HV i (tup a)).H)) = jVx R i (tup a) x₀ := hx₀.symm
    have hcf := (hφ (g k : (R.HV i (tup a)).H) (φ (g k))).2 rfl h
    let x1 := hcf.choose
    let x1' := hcf.choose_spec.choose
    have hcv : ConjVec i τ x1 x1' := hcf.choose_spec.choose_spec.1
    have h1 : (R.HV i (tup a)).e (g k : (R.HV i (tup a)).H) (fin _ h) = c x1 := hcf.choose_spec.choose_spec.2.1
    have h1' : (R.HV i (tup b)).e (φ (g k : (R.HV i (tup a)).H)) (fin _ h) = c x1' := hcf.choose_spec.choose_spec.2.2
    let xC : VsV D i ℂ := GlobalTheory.CoefModel.mapVV (inC M.c') (lamV D i) x
    have hxC : c xC = M.c0' x := hc x xC rfl
    have e0 : (R.HV i (tup a)).e (g k : (R.HV i (tup a)).H) (fin _ h) = M.c0' x := by rw [hx']; exact hx
    have e1 : c x1 = c xC := h1.symm.trans (e0.trans hxC.symm)
    have hx1 : x1 = xC := hinj e1
    let x' : VsV D i M.c'.F := ⟨MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank),
      GlobalTheory.Proof.TensorMapDescent.map_mem_VV (ta : M.c'.F →+* M.c'.F) (lamV D i) _ x.2⟩
    have hcomp : (τ : ℂ →+* ℂ).comp (inC M.c') = (inC M.c').comp (ta : M.c'.F →+* M.c'.F) := by
      ext z; exact (hta z).symm
    have hx1' : (x1' : Pol ℂ D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (inC M.c') (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) := by
      rw [hcv, hx1]
      show MvPolynomial.map (τ : ℂ →+* ℂ) (MvPolynomial.map (inC M.c') (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank)) =
        MvPolynomial.map (inC M.c') (MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank))
      rw [MvPolynomial.map_map, MvPolynomial.map_map, hcomp]
    exact ⟨x, x', rfl, e0, h1'.trans (hc x' x1' hx1')⟩

end GlobalTheory.ConjDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateDefiniteFormsDescendNumberFieldStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_definiteForms_descend_numberField : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → (∀ t x, ((R.xi (tup t) x : Circle) : ℂ) ∈ M.c'.F) → ∀ a b : Tp, ConjTup R τ (tup a) (tup b) → ∀ (y : (R.HV i (tup a)).H) (y' : (R.HV i (tup b)).H), ConjForm R i τ c (tup a) (tup b) y y' → ∃ (n : ℕ) (α : Fin n → ℂ) (ys : Fin n → (R.HV i (tup a)).H) (ys' : Fin n → (R.HV i (tup b)).H), y = ∑ k, α k • ys k ∧ y' = ∑ k, τ (α k) • ys' k ∧ ∀ k (h : GA D (Vc D i)), ∃ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) ∧ (R.HV i (tup a)).e (ys k) (fin _ h) = M.c0' x ∧ (R.HV i (tup b)).e (ys' k) (fin _ h) = M.c0' x' := by
  first | exact @GlobalTheory.ConjDesc.conj_desc | exact GlobalTheory.ConjDesc.conj_desc | (intros; apply GlobalTheory.ConjDesc.conj_desc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeReadOfReadsExist
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open Formalism.IndefR.Lev (levG flag1L)
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw}

section Delta

def IsDeltaInv (ρ : Setup D.ntw) (u : ∀ i : D.ntw.Tw, Bool → PlE D.host → (D.ntw.O i)ˣ) : Prop :=
  ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (P : PlE D.host), HkIdx i k P →
    ∀ (α : GA D (Wc D j)) (z : (AE D)ˣ), IsHeckeAt (Wc D j) P k α → IsDetAt (idemAt P) (Wc D j) α z →
      ρ.eO i b (u i b P) ^ k = (((ρ.B i j b).de.chi z : Circle) : ℂ)⁻¹

end Delta

section Pin

variable (Rl cG S) (YS : NX.NExpRealS Rl cG S)



end Pin

section Read

variable (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
  {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

theorem evK_smul (c : NX.KB S i b) (x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    evK YS v₀ hρ i j b (c • x) = ρ.e i b c • evK YS v₀ hρ i j b x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]
  | tmul a f =>
    rw [TensorProduct.smul_tmul', evK_tmul, evK_tmul, smul_smul]
    exact congrArg (· • _) (map_mul (ρ.e i b) c a)

theorem evK_hkFR (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL ((j : ℕ) + 1)))
    (hs : NX.HeckeStabR S ((j : ℕ) + 1) hL) (k : ℕ) (P : PlE D.host) (R : Finset (GA D (Wc D j))) (c : ℂ)
    (h : ∀ w, evW YS v₀ j (hL k P w) = c • fun x => ∑ γ ∈ R, evW YS v₀ j w (x * γ))
    (t : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    evK YS v₀ hρ i j b (NX.hkFR S i _ b hL hs k P t) = c • fun x => ∑ γ ∈ R, evK YS v₀ hρ i j b t (x * γ) := by
  induction t using TensorProduct.inductionOn with
  | add x y hx hy =>
    have e0 : NX.hkFR S i _ b hL hs k P ((x + y : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) : NX.Fm S i ((j : ℕ) + 1) b) =
        NX.hkFR S i _ b hL hs k P x + NX.hkFR S i _ b hL hs k P y := LinearMap.map_add _ _ _
    rw [e0]
    erw [map_add (evK YS v₀ hρ i j b)]
    rw [hx, hy, map_add (f := _), ← smul_add]
    congr 1
    funext x
    simp [Finset.sum_add_distrib]
  | tmul a f =>
    change evK YS v₀ hρ i j b (a ⊗ₜ[S.Ks] _) = _
    rw [evK_tmul, evK_tmul]
    change ρ.e i b a • evW YS v₀ j (hL k P f.1) = _
    rw [h]
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    ring

end Read

section Main

variable (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem heckeAt_of_scaled {ρ : Setup D.ntw} (hpin : RealPin Rl cG ρ) (hIs : Rl.toRealDat.toLevCh.Is A3.A.μ0)
    (hA : Rl.AllPlaces) (hρ : ρ.Good) {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)}
    (hr : GlobalTheory.ExportPin.Reads Rl cG S YS hL) {u} (hδ : IsDeltaInv ρ u) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ)
    (hs : NX.HeckeStabR S ((j : ℕ) + 1) (hL ((j : ℕ) + 1))) {k : ℕ} {P : PlE D.host} (hk : HkIdx i k P)
    {f g : D.nexp.Fm i ((j : ℕ) + 1) b}
    (e1 : YS.eF i _ b (Nat.le_add_left _ _) j.2 g = (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k •
      NX.hkFR S i _ b (hL _) hs k P (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)) :
    HeckeAt (realRd YS v₀ hρ i j b ν) k P f g := by
  rintro α R z ⟨hα, hR, hz⟩
  funext x
  rw [Setup.hecke_apply]
  have hδ' := hδ i j b k P hk α z hα hz
  obtain ⟨hk1, hkr, hsp, hP⟩ := hk
  have ho : Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E)) := by
    have hprime : ∀ Q ∈ Rl.Sb, ∃ l, ((D.host.g l : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
      intro Q hQ
      rw [show Rl.Sb = Rl.Pg from hA] at hQ
      obtain ⟨l, hl⟩ := (hIs.Pg Q).1 hQ
      have hmem := Rl.C.P.pb_over l
      rw [← hl] at hmem
      have hcast : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g l : ℕ) : 𝓞 D.host.K) ∈ Q.asIdeal := hmem
      exact ⟨l, by rwa [map_natCast] at hcast⟩
    refine ⟨(GlobalTheory.HeckeTieCompare.isSplitPl_iff P).1 hsp, ?_, ?_⟩
    · intro h
      obtain ⟨l, hl⟩ := hprime P h
      exact hP (D.ntw.placesOver_subset_exceptional i l hl)
    · intro Q hQ h
      obtain ⟨l, hl⟩ := hprime Q hQ
      rw [h, Formalism.L2.Col.conjIdeal_asIdeal, Formalism.L2.Col.mem_conjP, map_natCast] at hl
      exact hP (D.ntw.placesOver_subset_exceptional i l hl)
  have hR' : Bridge.IsDC (levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv)) α R :=
    GlobalTheory.PrincipalLevel.levK_eq_levG hpin i j b ▸ hR
  have hw : ∀ w, evW YS v₀ j (hL ((j : ℕ) + 1) k P w) =
      ((((Rl.C.mu0 j).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (Formalism.L2.DIV.kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) •
        fun x => ∑ γ ∈ R, evW YS v₀ j w (x * γ) := by
    intro w
    have := hr j k P hsp ho hkr α R hα hR' w
    exact congrArg (fun T => T (v₀ j _)) this
  have hmu : (((ρ.B i j b).mu0 z : Circle) : ℂ) = (((Rl.C.mu0 j).val P : ℂˣ) : ℂ) ^ k := by
    rw [hpin.mu0 i j b]
    refine GlobalTheory.HeckeDetChar.chi_detAt (hIs.mu0 j) (Q := Rl.Pg) ?_ ?_ ?_ hα hz
    · have := (hρ.base i j b).unram
      rwa [hpin.Pg i j b, hpin.mu0 i j b] at this
    · obtain ⟨Q, h1, -, h3⟩ := (hρ.base i j b).places.split
      exact hpin.Pg i j b ▸ h3.mono h1
    · have hA' : Rl.Sb = Rl.Pg := hA
      rw [← hA']; exact ho
  have hrk : (Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  change ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 g) x = _
  rw [e1]
  erw [evK_smul YS v₀ hρ i j b ((algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k)]
  erw [evK_hkFR YS v₀ hρ i j b (hL ((j : ℕ) + 1)) hs k P R _ hw]
  have he : ρ.e i b ((algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k) = ρ.eO i b (u i b P) ^ k := by
    rw [map_pow]; rfl
  have hm : (((ρ.B i j b).mu z : Circle) : ℂ) =
      (((ρ.B i j b).mu0 z : Circle) : ℂ) * (((ρ.B i j b).de.chi z : Circle) : ℂ) := by
    rw [Base.mu, MonoidHom.mul_apply, Circle.coe_mul]
  have hr1 : ∀ y, realRd YS v₀ hρ i j b ν f y =
      ν⁻¹ * evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f) y := fun _ => rfl
  have hq : normV P = Nat.card (Formalism.L2.DIV.kP P) := rfl
  simp only [hr1, Pi.smul_apply, smul_eq_mul, he, hδ', hm, hmu, hrk, hq]
  rw [← Finset.mul_sum]
  ring

end Main

end GlobalTheory.SeriesTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNsmulMemOfSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LatSandwich

variable {E : Type} [Field E] [NumberField E]

theorem exists_nsmul_le {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (s : Finset W) (M : Submodule (𝓞 E) W)
    (h : ∀ x ∈ s, ∃ k : ℕ, 0 < k ∧ k • x ∈ M) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ Submodule.span (𝓞 E) (s : Set W), k • x ∈ M := by
  classical
  choose! n hn hn' using h
  refine ⟨∏ t ∈ s, n t, Finset.prod_pos fun t ht => hn t ht, fun m hm => ?_⟩
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_coe.1 hx)
    rw [hk, mul_comm, mul_smul]
    exact M.nsmul_mem (hn' x (Finset.mem_coe.1 hx)) k
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact M.smul_mem a hx

theorem exists_nat_mul_isIntegral (z : E) : ∃ k : ℕ, 0 < k ∧ IsIntegral ℤ ((k : E) * z) := by
  have hal : IsAlgebraic ℤ z :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, hi⟩ := hal.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  have hc : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E) := (Int.cast_natCast _).symm
  rw [zsmul_eq_mul] at hi
  rcases Int.natAbs_eq y with e | e
  · rw [hc, ← e]; exact hi
  · rw [hc, show ((y.natAbs : ℤ)) = -y by omega, Int.cast_neg, neg_mul]; exact hi.neg

theorem mem_stdLat_iff {n : ℕ} (x : Fin n → E) : x ∈ Formalism.L2.Pj.stdLat E n ↔ ∀ i, IsIntegral ℤ (x i) := by
  simp only [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  refine forall_congr' fun i => ⟨?_, fun h => ⟨⟨x i, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact RingOfIntegers.isIntegral_coe y

theorem exists_nsmul_mem_stdLat {n : ℕ} (v : Fin n → E) : ∃ k : ℕ, 0 < k ∧ k • v ∈ Formalism.L2.Pj.stdLat E n := by
  classical
  obtain ⟨k, hk, h⟩ := exists_nsmul_le (Finset.univ.image fun i => Pi.single i (v i)) (Formalism.L2.Pj.stdLat E n) (by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff]
    intro i
    obtain ⟨k, hk, hi⟩ := exists_nat_mul_isIntegral (v i)
    refine ⟨k, hk, (mem_stdLat_iff _).2 fun j => ?_⟩
    by_cases e : j = i
    · subst e
      simpa [nsmul_eq_mul] using hi
    · simp [Pi.single_eq_of_ne e, isIntegral_zero])
  refine ⟨k, hk, h v ?_⟩
  have hs : ∑ i, Pi.single i (v i) ∈ Submodule.span (𝓞 E) ((Finset.univ.image fun i => Pi.single i (v i) : Finset (Fin n → E)) : Set (Fin n → E)) :=
    Submodule.sum_mem _ fun i _ => Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem (fun i => Pi.single i (v i)) (Finset.mem_univ i)))
  rwa [Finset.univ_sum_single v] at hs

theorem exists_nsmul_mem_of_span {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (v : Fin n → E) : ∃ k : ℕ, 0 < k ∧ k • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hsp]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hy⟩ := hy
    obtain ⟨b, hb, hz⟩ := hz
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.nsmul_mem hy _
    · rw [mul_smul]; exact Λ.nsmul_mem hz _
  | smul a y _ hy =>
    obtain ⟨m, hm, hy⟩ := hy
    obtain ⟨c, hc, hi⟩ := exists_nat_mul_isIntegral a
    refine ⟨c * m, Nat.mul_pos hc hm, ?_⟩
    have h := Λ.smul_mem (⟨(c : E) * a, hi⟩ : 𝓞 E) hy
    convert h using 1
    funext j
    change (c * m) • (a * y j) = ((c : E) * a) * (m • y j)
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring

end GlobalTheory.LatSandwich

namespace GlobalTheory.LatSandwich

variable {E : Type} [Field E] [NumberField E]

theorem sandwich_of_fg {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG)
    (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ a : ℕ, 0 < a ∧ (∀ x ∈ Formalism.L2.Pj.stdLat E n, (a : 𝓞 E) • x ∈ Λ) ∧
      ∀ x ∈ Λ, (a : 𝓞 E) • x ∈ Formalism.L2.Pj.stdLat E n := by
  classical
  obtain ⟨T, hT⟩ := hfg
  obtain ⟨d, hd, hup⟩ := exists_nsmul_le T (Formalism.L2.Pj.stdLat E n) fun x _ => exists_nsmul_mem_stdLat x
  obtain ⟨d', hd', hlo⟩ := exists_nsmul_le (Finset.univ.image fun i : Fin n => (Pi.single i 1 : Fin n → E)) Λ
    fun x _ => exists_nsmul_mem_of_span Λ hsp x
  refine ⟨d * d', Nat.mul_pos hd hd', fun x hx => ?_, fun x hx => ?_⟩
  · rw [Nat.cast_smul_eq_nsmul, mul_smul]
    refine Λ.nsmul_mem (hlo x ?_) d
    have hint := (mem_stdLat_iff x).1 hx
    have hs : ∑ i, (⟨x i, hint i⟩ : 𝓞 E) • (Pi.single i 1 : Fin n → E) ∈ Submodule.span (𝓞 E)
        ((Finset.univ.image fun i : Fin n => (Pi.single i 1 : Fin n → E) : Finset (Fin n → E)) : Set (Fin n → E)) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem (fun i : Fin n => (Pi.single i 1 : Fin n → E)) (Finset.mem_univ i))))
    have e : ∑ i, (⟨x i, hint i⟩ : 𝓞 E) • (Pi.single i 1 : Fin n → E) = x := by
      conv_rhs => rw [← Finset.univ_sum_single x]
      refine Finset.sum_congr rfl fun i _ => ?_
      funext j
      by_cases h : j = i
      · subst h
        change x j * (Pi.single j 1 : Fin n → E) j = _
        simp
      · change x i * (Pi.single i 1 : Fin n → E) j = _
        simp [Pi.single_eq_of_ne h]
    rwa [e] at hs
  · rw [Nat.cast_smul_eq_nsmul, mul_comm, mul_smul]
    exact nsmul_mem (hup x (hT ▸ hx)) d'

end GlobalTheory.LatSandwich

namespace GlobalTheory.LatSandwich

theorem sandwich : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (∀ x, x ∈ Λ ↔ x ∈ L0c D V) →
    ∃ a : ℕ, 0 < a ∧ (∀ x ∈ Formalism.L2.Pj.stdLat D.host.E V.rank, (a : 𝓞 D.host.E) • x ∈ Λ) ∧
      ∀ x ∈ Λ, (a : 𝓞 D.host.E) • x ∈ Formalism.L2.Pj.stdLat D.host.E V.rank := by
  intro D V Λ hΛ
  have e : Λ = V.L0.map (V.frame.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap := by
    ext x
    rw [hΛ, Submodule.mem_map]
    constructor
    · intro hx
      refine ⟨V.frame.equivFun.symm x, ?_, V.frame.equivFun.apply_symm_apply x⟩
      rw [V.frame.equivFun_symm_apply]
      exact hx
    · rintro ⟨y, hy, rfl⟩
      change ∑ i, V.frame.equivFun y i • V.frame i ∈ V.L0
      rw [V.frame.sum_equivFun]
      exact hy
  refine sandwich_of_fg Λ (e ▸ V.standardTuple_isLattice.fg.map _) ?_
  have hs : (Λ : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := by
    rw [e]; rfl
  have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
    classical
    let W := Submodule.span D.host.E (V.L0 : Set V.V)
    change W = ⊤
    by_contra h
    let e : V.V ≃ₗ⋆[D.host.E] V.V :=
      V.frame.equivFun.trans ((starLinearEquiv D.host.E).trans V.frame.equivFun.symm)
    let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
      (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
    have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) <
        Module.finrank D.host.E V.V := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt h
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
      rw [← V.baseLattice_isUnimodular]
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
        Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
      intro y hy
      have hxy : V.hT (e x) y = 0 :=
        congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
          (LinearMap.mem_ker.mp hx)
      have hyx : V.hT y (e x) = 0 := V.herm.eq_iff.mp hxy
      simp [map_smul, hyx]
    let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
      ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
    let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
    let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField D.host.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
  rw [hs, ← Submodule.map_span, hspan, Submodule.map_top, LinearEquiv.range]

end GlobalTheory.LatSandwich
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharInvCentralFlipIdeleEqProdLocalComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharInvCentralFlipIdeleEqProdLocalComponents
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.FlipCharFormula

variable {D : D7}

theorem fa_mul (a b : FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (a * b) Q = a Q * b Q := rfl
theorem fa_add (a b : FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (a + b) Q = a Q + b Q := rfl
theorem fa_sub (a b : FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (a - b) Q = a Q - b Q := rfl
theorem fa_one (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (1 : FiniteAdeleRing (𝓞 D.host.E) D.host.E) Q = 1 := rfl
theorem fa_natCast (n : ℕ) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (n : FiniteAdeleRing (𝓞 D.host.E) D.host.E) Q = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.cast_succ, fa_add, ih, fa_one, Nat.cast_succ]
theorem fa_sum {α : Type*} (s : Finset α) (g : α → FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) : (∑ a ∈ s, g a) Q = ∑ a ∈ s, g a Q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, fa_add, ih, Finset.sum_insert ha]

theorem finPart_incA (k : D.host.E) : finPart D (incA D k) = 1 ⊗ₜ k := rfl

theorem comp_of_isIdemAt (ι : Af ↥D.host.F ⊗[↥D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (h1 : ∀ (x : D.host.E), ι (1 ⊗ₜ[↥D.host.F] x) = (algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) x)
    (h2 : ∀ (y : Af ↥D.host.F ⊗[↥D.host.F] D.host.E),
      y ∈ intAE D ↔ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)), Valued.v ((ι y) P) ≤ 1)
    {e : AE D} {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ι (finPart D e) P = if P = PP then 1 else 0 := by
  obtain ⟨⟨hee, -, -⟩, hP⟩ := he
  have hidem : ∀ Q, ι (finPart D e) Q = 0 ∨ ι (finPart D e) Q = 1 := by
    intro Q
    apply IsIdempotentElem.iff_eq_zero_or_one.mp
    show ι (finPart D e) Q * ι (finPart D e) Q = ι (finPart D e) Q
    rw [← fa_mul, ← map_mul, ← map_mul, hee]
  have key : ∀ x : 𝓞 D.host.E, x ≠ 0 →
      (x ∈ PP.asIdeal ↔ ∃ Q, ι (finPart D e) Q = 1 ∧ x ∈ Q.asIdeal) := by
    intro x hx
    rw [hP x hx, h2, map_mul, finPart_incA, map_mul, h1]
    have hQ : ∀ Q, (Valued.v ((ι (finPart D e) * algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)
        ((x : D.host.E))⁻¹) Q) ≤ 1 ↔ ¬ (ι (finPart D e) Q = 1 ∧ x ∈ Q.asIdeal)) := by
      intro Q
      rw [fa_mul]
      rcases hidem Q with h | h
      · rw [h, zero_mul]; simp
      · rw [h, one_mul]
        have hv : Valued.v ((algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((x : D.host.E))⁻¹) Q)
            = HeightOneSpectrum.valuation D.host.E Q ((x : D.host.E))⁻¹ :=
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q _
        have hx0 : HeightOneSpectrum.valuation D.host.E Q (x : D.host.E) ≠ 0 := by
          simpa using hx
        rw [hv, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hx0), ← not_lt,
          HeightOneSpectrum.valuation_lt_one_iff_mem]
        simp
    simp only [hQ, not_forall, not_not]
  have hne : ∀ Q, Q ≠ PP → ι (finPart D e) Q = 0 := by
    intro Q hQ
    rcases hidem Q with h | h
    · exact h
    · exfalso
      have hnle : ¬ Q.asIdeal ≤ PP.asIdeal := by
        intro hle
        apply hQ
        exact HeightOneSpectrum.ext (Q.isMaximal.eq_of_le PP.isPrime.ne_top hle)
      obtain ⟨x, hxQ, hxP⟩ := Set.not_subset.mp hnle
      have hx0 : x ≠ 0 := by rintro rfl; exact hxP PP.asIdeal.zero_mem
      exact hxP ((key x hx0).mpr ⟨Q, h, hxQ⟩)
  have hPP : ι (finPart D e) PP = 1 := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot PP.ne_bot
    obtain ⟨Q, hQ1, -⟩ := (key x hx0).mp hx
    by_cases hQ : Q = PP
    · rwa [hQ] at hQ1
    · rw [hne Q hQ] at hQ1; exact absurd hQ1 zero_ne_one
  split_ifs with h
  · rw [h, hPP]
  · exact hne P h

theorem infPart_of_isIdemAt {e : AE D} {PP : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt e PP) : infPart D e = 0 := by
  obtain ⟨⟨hee, hec, v, ε, ⟨α, rfl, -, -⟩, hsum⟩, -⟩ := he
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id (↥D.host.F) D.host.E)) ((pairA D.host.F 0 α : AF D.host.F) ⊗ₜ[↥D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    have : (fstA D.host.F) (pairA D.host.F 0 α) = 0 := rfl
    rw [this]
    exact TensorProduct.zero_tmul _ _
  have hs := congrArg (infPart D) hsum
  have hm := congrArg (infPart D) hec
  have hi := congrArg (infPart D) hee
  rw [map_add (f := _), h0] at hs
  rw [map_mul, map_zero] at hm
  rw [map_mul] at hi
  have hc : infPart D (cA D e) = - infPart D e :=
    eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hs)
  rw [hc, mul_neg, hi, neg_eq_zero] at hm
  exact hm


set_option maxHeartbeats 800000 in
theorem char_inv_eq_prod_locK_of_flip : ∀ (D : D7) (V : HSp D) (χW : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (M₀ : ℕ) (u : D.host.Eˣ) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (x : (AE D)ˣ), ChrEq χW χ → (u : D.host.E) = ((M₀ : ℕ) : D.host.E) → IsIdemSum eT T → IsFlipDet V eT M₀ x → ((χW x : Circle) : ℂ)⁻¹ = ∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ V.rank := by
  intro D V χW χ M₀ u T eT x hχ hu hT hx
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) χW χ hχ
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hT
  unfold IsFlipDet at hx
  have heT : ∀ P, ι (finPart D (∑ PP ∈ T, es PP)) P = if P ∈ T then 1 else 0 := by
    intro P
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, fa_sum,
      Finset.sum_congr rfl (fun PP hPP => comp_of_isIdemAt ι h1 h2 (hes PP hPP) P)]
    exact Finset.sum_ite_eq T P (fun _ => (1 : HeightOneSpectrum.adicCompletion D.host.E P))
  have hinfT : infPart D (∑ PP ∈ T, es PP) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero (fun PP hPP => infPart_of_isIdemAt (hes PP hPP))
  have hinf : infPart D (x : AE D) = 1 := by
    have := congrArg (infPart D) hx
    rw [map_mul, map_add (f := _), map_mul, map_sub, hinfT, map_one, zero_mul, zero_add, sub_zero, mul_one] at this
    exact this
  have hcomp : ∀ P, ι (finPart D (x : AE D)) P *
      ((if P ∈ T then 1 else 0) * (((M₀ ^ V.rank : ℕ) : HeightOneSpectrum.adicCompletion D.host.E P))
        + (1 - if P ∈ T then 1 else 0)) = 1 := by
    intro P
    have h0 : ι (finPart D ((x : AE D) * ((∑ PP ∈ T, es PP) * ((M₀ ^ V.rank : ℕ) : AE D)
        + (1 - ∑ PP ∈ T, es PP)))) P = ι (finPart D 1) P := by
      rw [Nat.cast_pow, hx]
    simp only [map_mul, map_add (f := _), map_sub, map_one, map_natCast] at h0
    rw [fa_mul, fa_add, fa_mul, fa_sub, fa_one, fa_natCast, heT] at h0
    exact h0
  let k : HeightOneSpectrum (𝓞 D.host.E) → D.host.Eˣ := fun P => if P ∈ T then (u⁻¹) ^ V.rank else 1
  have hxk : ∀ P, ι (finPart D (x : AE D)) P =
      algebraMap D.host.E (HeightOneSpectrum.adicCompletion D.host.E P) (k P : D.host.E) := by
    intro P
    have hc := hcomp P
    by_cases hP : P ∈ T
    · rw [if_pos hP, one_mul, sub_self, add_zero] at hc
      rw [show k P = (u⁻¹) ^ V.rank from if_pos hP, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hu,
        map_pow, map_inv₀, map_natCast, eq_inv_of_mul_eq_one_left hc, Nat.cast_pow, inv_pow]
    · rw [if_neg hP, zero_mul, sub_zero, zero_add, mul_one] at hc
      rw [show k P = 1 from if_neg hP, Units.val_one, map_one]
      exact hc
  have hI : Ideal.span {((N : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have key := hprod x hinf (T ∪ (Ideal.finite_factors hI).toFinset) k
    (fun P _ => by
      rw [hxk P, sub_self, map_zero]
      exact ⟨HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _, zero_le'⟩)
    (fun P hP => by
      have hPT : P ∉ T := fun h => hP (Finset.mem_union_left _ h)
      refine ⟨?_, ?_⟩
      · rw [hxk P, show k P = 1 from if_neg hPT, Units.val_one, map_one, map_one]
      · intro hNP
        apply hP
        apply Finset.mem_union_right
        rw [Set.Finite.mem_toFinset]
        exact Ideal.dvd_span_singleton.mpr hNP)
  rw [key, ← Finset.prod_subset (Finset.subset_union_left)
    (fun P _ hPT => by rw [show k P = 1 from if_neg hPT, map_one, Units.val_one])]
  rw [Finset.prod_congr rfl (fun P hP => by
    rw [show k P = (u⁻¹) ^ V.rank from if_pos hP, map_pow, map_inv, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val, inv_pow])]
  rw [Finset.prod_inv_distrib, inv_inv]

end GlobalTheory.FlipCharFormula
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharInvCentralFlipIdeleEqProdLocalComponentsStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.char_inv_centralFlipIdele_eq_prod_local_components : ∀ (D : D7) (V : HSp D) (χW : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (M₀ : ℕ) (u : D.host.Eˣ) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (x : (AE D)ˣ), ChrEq χW χ → (u : D.host.E) = ((M₀ : ℕ) : D.host.E) → IsIdemSum eT T → IsFlipDet V eT M₀ x → ((χW x : Circle) : ℂ)⁻¹ = ∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ V.rank := by
  first | exact @GlobalTheory.FlipCharFormula.char_inv_eq_prod_locK_of_flip | exact GlobalTheory.FlipCharFormula.char_inv_eq_prod_locK_of_flip | (intros; apply GlobalTheory.FlipCharFormula.char_inv_eq_prod_locK_of_flip <;> assumption)
end
end

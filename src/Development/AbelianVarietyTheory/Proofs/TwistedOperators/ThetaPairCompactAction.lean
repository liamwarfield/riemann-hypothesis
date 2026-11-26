module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitScalarFourier
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeThetaValueIdentityUnitFrames
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelComplexPointMatchesCosets
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenReadsOfUnitAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairCompactAction
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.KExpLine

section Abstract

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def zeroOn (S : Submodule ℂ (SchwartzMap Y ℂ)) (P : Finset Y) : Submodule ℂ S where
  carrier := {s | ∀ y ∈ P, (s : SchwartzMap Y ℂ) y = 0}
  add_mem' := by
    intro a b ha hb y hy
    simp [ha y hy, hb y hy]
  zero_mem' := by
    intro y _
    simp
  smul_mem' := by
    intro c a ha y hy
    simp [ha y hy]

theorem exists_finset_sep (S : Submodule ℂ (SchwartzMap Y ℂ)) [FiniteDimensional ℂ S] :
    ∃ P : Finset Y, ∀ s ∈ S, (∀ y ∈ P, s y = 0) → s = 0 := by
  classical
  obtain ⟨P, -, hmin⟩ := (measure fun P : Finset Y => Module.finrank ℂ (zeroOn S P)).wf.has_min Set.univ
    ⟨∅, trivial⟩
  refine ⟨P, fun s hs h0 => ?_⟩
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, s y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (SchwartzMap.ext h)
  have hlt : zeroOn S (insert y P) < zeroOn S P := by
    refine lt_of_le_of_ne (fun a ha z hz => ha z (Finset.mem_insert_of_mem hz)) fun heq => ?_
    have hmem : (⟨s, hs⟩ : S) ∈ zeroOn S P := h0
    rw [← heq] at hmem
    exact hy (hmem y (Finset.mem_insert_self y P))
  exact hmin (insert y P) trivial (Submodule.finrank_lt_finrank_of_lt hlt)

theorem sub_mem_of_hasDerivAt (S T : Submodule ℂ (SchwartzMap Y ℂ)) [FiniteDimensional ℂ S]
    (c d : ℝ → SchwartzMap Y ℂ) (hc : ∀ u, c u ∈ S) (hd : ∀ t, d t ∈ T)
    (hder : ∀ y t, HasDerivAt (fun u => c u y) (d t y) t) : c 1 - c 0 ∈ T := by
  classical
  obtain ⟨P, hP⟩ := exists_finset_sep S
  let E : S →ₗ[ℂ] (P → ℂ) :=
    { toFun := fun s p => (s : SchwartzMap Y ℂ) p
      map_add' := by intro a b; funext p; simp
      map_smul' := by intro a b; funext p; simp }
  have hE : LinearMap.ker E = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro s hs
    exact Subtype.ext (hP s s.2 fun y hy => congrFun hs ⟨y, hy⟩)
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective E hE
  let C : ℝ → (P → ℂ) := fun u p => c u p
  have hCd : ∀ t, HasDerivAt C (fun p => d t p) t := fun t => hasDerivAt_pi.2 fun p => hder p t
  have hLC : ∀ u, L (C u) = ⟨c u, hc u⟩ := fun u => LinearMap.congr_fun hL ⟨c u, hc u⟩
  let ev : SchwartzMap Y ℂ → Y → ℂ := fun g y => g y
  have hcomp : ∀ φ : (P → ℂ) →ₗ[ℂ] ℂ, ∀ t, HasDerivAt (fun u => φ (C u)) (φ (fun p => d t p)) t := fun φ t => by
    have h := (((LinearMap.toContinuousLinearMap φ).restrictScalars ℝ).hasFDerivAt (x := C t)).comp_hasDerivAt t (hCd t)
    simpa [Function.comp_def] using h

  have hdS : ∀ t, ((L (fun p => d t p) : S) : SchwartzMap Y ℂ) = d t := by
    intro t
    ext y
    let evy : S →ₗ[ℂ] ℂ :=
      { toFun := fun s => (s : SchwartzMap Y ℂ) y
        map_add' := by intro a b; simp
        map_smul' := by intro a b; simp }
    have h1 := hcomp (evy ∘ₗ L) t
    have h2 : (fun u => (evy ∘ₗ L) (C u)) = fun u => c u y := by
      funext u
      simp only [LinearMap.comp_apply, hLC u]
      rfl
    rw [h2] at h1
    exact (hder y t).unique h1 |>.symm
  let T' : Submodule ℂ S := T.comap S.subtype
  have hdT : ∀ t, L (fun p => d t p) ∈ T' := fun t => by
    show ((L (fun p => d t p) : S) : SchwartzMap Y ℂ) ∈ T
    rw [hdS t]
    exact hd t
  have key : (⟨c 1, hc 1⟩ : S) - ⟨c 0, hc 0⟩ ∈ T' := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    let ψ : (P → ℂ) →ₗ[ℂ] ℂ := φ ∘ₗ T'.mkQ ∘ₗ L
    have hg : ∀ t, HasDerivAt (fun u => ψ (C u)) 0 t := by
      intro t
      have := hcomp ψ t
      have h0 : ψ (fun p => d t p) = 0 := by
        show φ (T'.mkQ (L (fun p => d t p))) = 0
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero T').2 (hdT t), map_zero]
      rwa [h0] at this
    have hconst := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
    have e1 : ∀ u, ψ (C u) = φ (Submodule.Quotient.mk ⟨c u, hc u⟩) := fun u => by
      show φ (T'.mkQ (L (C u))) = _
      rw [hLC u]
      rfl
    rw [e1, e1] at hconst
    rw [Submodule.Quotient.mk_sub, map_sub, hconst, sub_self]
  exact key

end Abstract

end GlobalTheory.KExpLine

namespace GlobalTheory.KExpLine

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

end GlobalTheory.KExpLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslateVacuumReadRationalPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslateVacuumReadRationalPoints
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.NTheta (IsIdemAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.HeisRatRead

open GlobalTheory.FinTranslate Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {D : D7}

theorem ratW_sub_realPt_inf (S T : HSp D) (ℓ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (ratW T S ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T ℓ).map (infPart D) = 0 := by
  ext i j
  change infPart D (incA D (ℓ i j) - pairA D.host.F 1 0 ⊗ₜ[D.host.F] ℓ i j) = 0
  rw [map_sub]
  change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (1 ⊗ₜ ℓ i j) -
    Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 1 0 ⊗ₜ ℓ i j) = 0
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_one]
  exact sub_eq_zero.2 rfl

theorem realPt_sub (S T : HSp D) (X Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T (X - Y) = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T X - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T Y := by
  ext i j
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt, Matrix.of_apply, Matrix.sub_apply, TensorProduct.tmul_sub]

theorem actO_inf (S T : HSp D) (h : GA D T) {w : WO S T} (hw : w.map (infPart D) = 0) :
    (actO S T 1 h w).map (infPart D) = 0 := by
  have hw' : ∀ k l, infPart D (w k l) = 0 := fun k l => congrFun (congrFun hw k) l
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  unfold actO
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul, hw', mul_zero, zero_mul, Finset.sum_const_zero]

theorem actO_add (S T : HSp D) (h : GA D T) (u v : WO S T) :
    actO S T 1 h (u + v) = actO S T 1 h u + actO S T 1 h v := by
  simp only [actO, Matrix.mul_add, Matrix.add_mul]

end GlobalTheory.HeisRatRead

namespace GlobalTheory.HeisRatRead

open GlobalTheory.FinTranslate Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem heis_translate_read : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    R.toLevCh.Is A.μ0 → R.IsFam → R.IsThP → ∀ (i : Fin D.R.m) (g : GA D (Wc D i)) (x : WO (Vc D i) (Wc D i)),
    x.map (infPart D) = 0 → ∀ (ℓ : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (w : WO (Vc D i) (Wc D i)),
    w.map (infPart D) = 0 → heisO R.ψ (Vc D i) (Wc D i) w (R.vacP i) = R.vacP i →
    x = actO (Vc D i) (Wc D i) 1 g⁻¹ (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) + w →
    ∀ X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E,
      R.ωP i A.μ0 (1, g) (heisO R.ψ (Vc D i) (Wc D i) x (R.vacP i)) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X) =
        R.ψ (-(symplOH (Vc D i) (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ)) +
            symplOH (Vc D i) (Wc D i) (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) (actO (Vc D i) (Wc D i) 1 g w))) *
          R.ωP i A.μ0 (1, g) (R.vacP i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ)) := by
  intro D G _ _ Pl0 T0 A T _ R hL hF hT i g x hx ℓ w hw hρw hxe X
  have hW := hT.ωP i A.μ0
  have hv := hT.vP i A.μ0
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) := hv.1.2.theta
  set F := R.ωP i A.μ0 (1, g) (R.vacP i) with hFdef
  have hFθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) F := hW.om_pres _ _ hf
  set lf := ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ with hlf
  have hlf0 : lf.map (infPart D) = 0 := ratW_sub_realPt_inf (Vc D i) (Wc D i) ℓ
  set gw := actO (Vc D i) (Wc D i) 1 g w with hgw
  have hgw0 : gw.map (infPart D) = 0 := actO_inf (Vc D i) (Wc D i) g hw
  have hgx : actO (Vc D i) (Wc D i) 1 g x = lf + gw := by
    rw [hxe, actO_add, ← GlobalTheory.HeckeVacuum.act_mul, mul_inv_cancel, GlobalTheory.HeckeVacuum.act_one]
  have hFw : heisO R.ψ (Vc D i) (Wc D i) gw F = F := by
    have := hW.om_heis 1 g w (R.vacP i) hf
    rw [hρw] at this
    exact this.symm
  set P := GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X
  set z := GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ)
  have hP0 : P.map (finPart D) = 0 := GlobalTheory.FrameConst.realPt_fin (Vc D i) (Wc D i) X
  have hz0 : z.map (finPart D) = 0 := GlobalTheory.FrameConst.realPt_fin (Vc D i) (Wc D i) (X - ℓ)
  have hl0 : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ).map (finPart D) = 0 := GlobalTheory.FrameConst.realPt_fin (Vc D i) (Wc D i) ℓ
  have hzF : F (z + gw) = F z := by
    have := congrFun hFw z
    simp only [heisO, symplOH_real_fin hgw0 hz0, AddChar.map_zero_eq_one, one_mul] at this
    exact this
  have hpt : P + (lf + gw) = ratW (Wc D i) (Vc D i) ℓ + (z + gw) := by
    simp only [z, P, hlf, realPt_sub]
    abel
  have hratW : ratW (Wc D i) (Vc D i) ℓ = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ + lf := by
    rw [hlf]; abel
  rw [hW.om_heis 1 g x (R.vacP i) hf, ← hFdef]
  show R.ψ (symplOH (Vc D i) (Wc D i) P (actO (Vc D i) (Wc D i) 1 g x)) * F (P + actO (Vc D i) (Wc D i) 1 g x) = _
  rw [hgx, hpt, hFθ.quasi, hzF, ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  rw [hratW, symplOH_add_right, symplOH_add_left, symplOH_add_right, symplOH_add_right,
    symplOH_real_fin hlf0 hP0, symplOH_real_fin hgw0 hP0, symplOH_real_fin hgw0 hl0, symplOH_fin_real hlf0 hz0]
  ring

end GlobalTheory.HeisRatRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslateVacuumReadRationalPointsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.NTheta (IsIdemAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergTranslate_vacuum_read_rationalPoints : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    R.toLevCh.Is A.μ0 → R.IsFam → R.IsThP → ∀ (i : Fin D.R.m) (g : GA D (Wc D i)) (x : WO (Vc D i) (Wc D i)),
    x.map (infPart D) = 0 → ∀ (ℓ : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (w : WO (Vc D i) (Wc D i)),
    w.map (infPart D) = 0 → heisO R.ψ (Vc D i) (Wc D i) w (R.vacP i) = R.vacP i →
    x = actO (Vc D i) (Wc D i) 1 g⁻¹ (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) + w →
    ∀ X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E,
      R.ωP i A.μ0 (1, g) (heisO R.ψ (Vc D i) (Wc D i) x (R.vacP i)) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X) =
        R.ψ (-(symplOH (Vc D i) (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ)) +
            symplOH (Vc D i) (Wc D i) (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) (actO (Vc D i) (Wc D i) 1 g w))) *
          R.ωP i A.μ0 (1, g) (R.vacP i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) (X - ℓ)) := by
  first | exact @GlobalTheory.HeisRatRead.heis_translate_read | exact GlobalTheory.HeisRatRead.heis_translate_read | (intros; apply GlobalTheory.HeisRatRead.heis_translate_read <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumLocalFunctionsEqPureTensorScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumLocalFunctionsEqPureTensorScalar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipMatch

open GlobalTheory.BigDat GlobalTheory.WeilM


set_option maxHeartbeats 1600000 in
theorem datum_placesA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X →
    ∀ f₀, IsDatumA (t := t) W e Γ (Finsupp.single (((), ρ.vX i (j + 1)), ρ.vT (i + 1) j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M.vac) →
    ∀ ι : ∀ w : Pl D.host.E, ((Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F (w.under (𝓞 D.host.F))) → ℂ) →ₗ[ℂ]
      (Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) → ℂ),
    (∀ w ∈ locPl G t, IsLagrModel Γ.M W.ψ (w.under (𝓞 D.host.F)) (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w) (ι w)) →
    ∃ s : ℂ, s ≠ 0 ∧ ∀ ε, IsIdemSum ε (locPl G t) → ∀ (n : Pl D.host.E → ℕ) Ψ (τ : TotT G (routeBig t i j)),
      (∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Ψ w)) →
      HasLocal B t ε (X := (i, j + 1)) (M := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩
        (IsLocVec W (.chi i (j + 1)) ε (ρ.vX i (j + 1))) (IsLocVec W (.mu t (i + 1) j) ε (ρ.vT (i + 1) j)) τ Ψ →
      ∀ φ, IsFinPart Γ.M X.T φ → (∀ w ∈ locPl G t, ι w (φ (w.under (𝓞 D.host.F))) = Ψ w) →
        IsDatumA W e Γ τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (s • f₀) φ) := by
  intro D T L sc G μ₀ hL W B ρ t i j M _ e Bs Γ X om om' h hT hti f₀ hdat ι hι
  classical
  have h₁ := ρ.vX_is i (j + 1) i.2 j.2
  have h₂ := ρ.vT_is t (i + 1) j i.2 j.2
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  have hG : Γ.M.IsGood W.ψ := h.ψ ▸ hT.geo.hM
  obtain ⟨hadd, -, -⟩ := GlobalTheory.BigDat.ThBox.thetaPt_box W M t i j e Bs Γ X om om' h hT
  have hf : thetaPt Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M.vac) = box e (ρ.vX i (j + 1)) (ρ.vT (i + 1) j) := by
    funext u
    have := hdat.2 u
    exact this.trans ((Finsupp.sum_single_index (zero_mul _)).trans (one_mul _))
  obtain ⟨hid, hsumid⟩ := GlobalTheory.IdemAtPl.main hL (G := G) t
  have hh := fun w hw => GlobalTheory.BigDat.halves_split hL W i j e Γ h.JW h.JWW _ _ (hid w hw).1 (hid w hw).2
  have hco := GlobalTheory.BigDat.mixCo_spec B t i j e
  have hv := fun w hw => lagr_vac (hι w hw) (hG.vac _).1 (hG.vac _).2.1 (latPt e (w.under (𝓞 D.host.F)) : Set _)
    (fun γ hγ hγ' => GlobalTheory.BigDat.VacFix.vac_fixed W M t i j e Bs Γ X om om' h hT _ (GlobalTheory.BigDat.latPt_le_latAtV t i j e Bs Γ X hti _) γ (.inr ⟨hγ, hγ'.elim
      (fun h => ⟨_, (hid w hw).1, h⟩) fun h => ⟨_, splitIdem_conj (hid w hw).1, h⟩⟩)) (hco w).2.1 (hh w hw).2.2.2.1
  set c := ∏ w ∈ locPl G t, ι w (Γ.M.vac _) 0 with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun w hw => (hv w hw).1
  refine ⟨c, hc0, ?_⟩
  intro ε hε n Ψ τ _ hloc φ hφ hΨ
  obtain ⟨φ₁, φ₂, hmem, hsum⟩ := hloc
  have sW := (node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).sd
  obtain ⟨T₁, hT₁⟩ := (GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _ (isSelfDualC_neg sW)
    (node_isV G hL (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩).sd _ ε hε _ h₁.2.theta h₁.2.lat).1
  obtain ⟨T₂, hT₂⟩ := (GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _
    (node_isV G hL (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩).sd sW _ ε hε _ h₂.2.theta h₂.2.lat).1
  obtain ⟨g0, g1, g2⟩ := GlobalTheory.BigDat.boxGraph_graph_heis hL W i j e Γ h.JW h.JWW ε _ hε _ _ T₁ T₂ hT₁ hT₂
  obtain ⟨hεs, hεw⟩ := hsumid ε hε
  have hb : thetaPt Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f₀) Γ.M.vac) = c • box e (ρ.vX i (j + 1)) (ρ.vT (i + 1) j) := by
    rw [← hf]
    exact funext fun u => (congrArg (thetaPt Γ W.ψ · u) (funext fun _ => mul_assoc _ _ _)).trans (thetaPt_smul _ _ _ _ u)
  let R : Submodule ℂ ((Pt G i j → ℂ) × ((Ix G i j → AF D.host.F) → ℂ)) :=
    { carrier := {p | p.2 ∈ schA D.host.F _ ∧ (p.1, thetaPt Γ W.ψ p.2) ∈ boxGraph e ε T₁ T₂}
      zero_mem' := ⟨zero_mem _, by
        have : thetaPt Γ W.ψ 0 = 0 := funext fun u => by simpa using thetaPt_smul Γ W.ψ 0 0 u
        rw [Prod.snd_zero, this]; exact zero_mem _⟩
      add_mem' := fun {p q} hp hq => ⟨add_mem hp.1 hq.1, by
        rw [Prod.snd_add, hadd _ hp.1 _ hq.1]; exact add_mem hp.2 hq.2⟩
      smul_mem' := fun a p hp => ⟨Submodule.smul_mem _ a hp.1, by
        rw [Prod.smul_snd, show thetaPt Γ W.ψ (a • p.2) = a • thetaPt Γ W.ψ p.2 from funext (thetaPt_smul _ _ _ _)]
        exact Submodule.smul_mem _ a hp.2⟩ }
  have hA : ∀ w ∈ locPl G t, ∀ x ∈ mixHalf e (atPl w 1), x ∈ mixHalf e ε := fun w hw x hx =>
    ⟨isHalf_mono (hεw w hw) hx.1, isHalf_mono (hεw w hw) hx.2⟩
  have hA' : ∀ w ∈ locPl G t, ∀ x ∈ mixHalf e (cA D (atPl w 1)), x ∈ mixHalf e (cA D ε) := fun w hw x hx =>
    have : cA D ε * cA D (atPl w 1) = cA D (atPl w 1) := by rw [← RingHom.map_mul, hεw w hw]
    ⟨isHalf_mono this hx.1, isHalf_mono this hx.2⟩
  have hbase : (Set.indicator (halfPt e ε : Set _) fun u => ∏ w ∈ locPl G t, ι w (Γ.M.vac _) (mixCo B t e w u)) =
      c • box e (halfInd ε (latV G i j)) (halfInd ε (latW G i j)) := by
    funext u
    rw [Pi.smul_apply, smul_eq_mul, box, halfInd, halfInd]
    by_cases hu : u ∈ mixHalf e ε
    · rw [Set.indicator_of_mem (mem_halfPt.2 hu), Finset.prod_congr rfl fun w hw =>
        (congrArg _ ((hco w).2.2.1 u).symm).trans ((hv w hw).2 _ ((hh w hw).2.2.2.2 u).1)]
      by_cases hl : mapV e u ∈ latV G i j ∧ mapW e u ∈ latW G i j
      · rw [if_pos ⟨hl.1, hu.1⟩, if_pos ⟨hl.2, hu.2⟩, mul_one, mul_one]
        exact Finset.prod_congr rfl fun w hw => Set.indicator_of_mem (((hh w hw).2.2.2.2 u).2.2 hl.1 hl.2) _
      · have : ∃ w ∈ locPl G t, ofMaps e (atPl w 1 • mapV e u, atPl w 1 • mapW e u) ∉ latPt e (w.under (𝓞 D.host.F)) := by
          by_contra! hall
          exact hl ⟨mem_of_sum_smul (hεs ▸ hu.1) fun w hw => (mapV_ofMaps e _ ▸ (hall w hw).2.1 :),
            mem_of_sum_smul (hεs ▸ hu.2) fun w hw => (mapW_ofMaps e _ ▸ (hall w hw).2.2 :)⟩
        obtain ⟨w, hw, hn⟩ := this
        rw [Finset.prod_eq_zero hw (Set.indicator_of_notMem hn _)]
        rcases not_and_or.1 hl with hl | hl
        · rw [if_neg fun h => hl h.1, zero_mul, mul_zero]
        · rw [if_neg fun h : _ ∧ IsHalf ε (mapW e u) => hl h.1, mul_zero, mul_zero]
    · rw [Set.indicator_of_notMem (mt mem_halfPt.1 hu)]
      rcases not_and_or.1 hu with hl | hl
      · rw [if_neg fun h => hl h.2, zero_mul, mul_zero]
      · rw [if_neg fun h : _ ∧ IsHalf ε (mapW e u) => hl h.2, mul_zero, mul_zero]
  have hR := GlobalTheory.InductLagr.rel_of_vac Γ.M W.ψ hstd hG (locPl G t) (fun w => w.under (𝓞 D.host.F)) (Good.under_injOn hL G t) _
    (fun w => mixHalf e (atPl w 1)) (fun w => mixHalf e (cA D (atPl w 1))) (mixCo B t e) ι (halfPt e ε) R (c • f₀)
    (fun w hw => hι w hw) (fun w hw u hu => ⟨(hh w hw).1 u hu, mem_halfPt.2 (hA w hw u hu)⟩) (fun w hw => (hh w hw).2.1)
    (fun w hw => (hh w hw).2.2.1) (fun w _ x _ u => (hco w).1 u x)
    (fun w _ w' _ hne x hx u => by rw [(hco w').1, (hco w').2.2.2 w hne.symm x hx, add_zero])
    (fun w hw u => ⟨_, ((hh w hw).2.2.2.2 u).1, (hco w).2.2.1 u, ((hh w hw).2.2.2.2 u).2.1⟩)
    (fun w hw x hx p hp => ⟨GlobalTheory.HeisSchA.rho_mem_schA Γ.M W.ψ hstd x _ hp.1, by
      have := g1 x (hA w hw x hx) _ hp.2
      rwa [← thetaPt_rho] at this⟩)
    (fun w hw x hx p hp => ⟨GlobalTheory.HeisSchA.rho_mem_schA Γ.M W.ψ hstd x _ hp.1, by
      have := g2 x (hA' w hw x hx) _ hp.2
      rwa [← thetaPt_rho] at this⟩)
    ⟨(isFinPart_vac hG ∅).fam.mem hG _, by
      have := (boxGraph e ε T₁ T₂).smul_mem c (Submodule.subset_span
        ⟨_, _, GlobalTheory.isSBHalf_halfInd ε _, GlobalTheory.isSBHalf_halfInd ε _, rfl⟩)
      rw [(congrArg T₁ (one_smul ℂ _).symm).trans hT₁.vac, (congrArg T₂ (one_smul ℂ _).symm).trans hT₂.vac] at this
      show (_, thetaPt Γ W.ψ _) ∈ _
      rw [hbase, hb]
      exact this⟩
    φ hφ.1 fun v hv => hφ.2 v fun hm => let ⟨w, hw, e⟩ := (hti.2.2.1 v).1 hm; hv w hw e
  have hτ : (∑ d ∈ τ.support, τ d • (box e (φ₁ d) (φ₂ d), box e d.1.2 d.2)) ∈ boxGraph e ε T₁ T₂ :=
    sum_mem fun d hd => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, (hmem d hd).1.1, (hmem d hd).2.1, by
      rw [← (hmem d hd).1.2.2 T₁ hT₁, ← (hmem d hd).2.2.2 T₂ hT₂]⟩)
  have hfst : (Set.indicator (halfPt e ε : Set _) fun u => ∏ w ∈ locPl G t, ι w (φ _) (mixCo B t e w u)) =
      (∑ d ∈ τ.support, τ d • (box e (φ₁ d) (φ₂ d), box e d.1.2 d.2)).1 := by
    funext u
    rw [Prod.fst_sum, Finset.sum_apply]
    by_cases hu : u ∈ mixHalf e ε
    · rw [Set.indicator_of_mem (mem_halfPt.2 hu), Finset.prod_congr rfl fun w hw => congrFun (hΨ w hw) _]
      exact (hsum _ _ hu.1 hu.2).symm
    · rw [Set.indicator_of_notMem (mt mem_halfPt.1 hu)]
      refine (Finset.sum_eq_zero fun d hd => mul_eq_zero_of_right _ ?_).symm
      by_contra hne
      exact hu ⟨(hmem d hd).1.1.1 _ (left_ne_zero_of_mul hne), (hmem d hd).2.1.1 _ (right_ne_zero_of_mul hne)⟩
  refine ⟨hR.1, fun u => ?_⟩
  have := g0 _ (by
    have := sub_mem hR.2 hτ
    rwa [← Prod.mk.eta (p := Finset.sum _ _), Prod.mk_sub_mk, ← hfst, sub_self] at this)
  have := congrFun (sub_eq_zero.1 this) u
  rw [Prod.snd_sum, Finset.sum_apply] at this
  exact this

end GlobalTheory.FlipMatch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumLocalFunctionsEqPureTensorScalarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_localFunctions_eq_pureTensor_scalar : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X →
    ∀ f₀, IsDatumA (t := t) W e Γ (Finsupp.single (((), ρ.vX i (j + 1)), ρ.vT (i + 1) j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M.vac) →
    ∀ ι : ∀ w : Pl D.host.E, ((Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F (w.under (𝓞 D.host.F))) → ℂ) →ₗ[ℂ]
      (Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) → ℂ),
    (∀ w ∈ locPl G t, IsLagrModel Γ.M W.ψ (w.under (𝓞 D.host.F)) (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w) (ι w)) →
    ∃ s : ℂ, s ≠ 0 ∧ ∀ ε, IsIdemSum ε (locPl G t) → ∀ (n : Pl D.host.E → ℕ) Ψ (τ : TotT G (routeBig t i j)),
      (∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Ψ w)) →
      HasLocal B t ε (X := (i, j + 1)) (M := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩
        (IsLocVec W (.chi i (j + 1)) ε (ρ.vX i (j + 1))) (IsLocVec W (.mu t (i + 1) j) ε (ρ.vT (i + 1) j)) τ Ψ →
      ∀ φ, IsFinPart Γ.M X.T φ → (∀ w ∈ locPl G t, ι w (φ (w.under (𝓞 D.host.F))) = Ψ w) →
        IsDatumA W e Γ τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (s • f₀) φ) := by
  first | exact @GlobalTheory.FlipMatch.datum_placesA | exact GlobalTheory.FlipMatch.datum_placesA | (intros; apply GlobalTheory.FlipMatch.datum_placesA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapIncAMulRealPt
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.NTheta (IsIdemAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.FrameChangeRead

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.FD Formalism.IndefR.Datum

variable {D : D7}

theorem map_incA_mul_realPt (S T : HSp D) (M : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    HMul.hMul (M.map (incA D)) (realPt S T X : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = realPt S T (M * X) := by
  ext a c
  simp only [realPt, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.tmul_sum]

theorem exists_frAt {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
    {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    (hM : R.IsModels) (ht : TieIn T R κ v₀) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hσ : σ = T.σ₀)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (h : GA D (Wc D i)) :
    ∃ γ ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (dictW T i σ hV) γ h := by
  have e : res T (sg0 D A) = T.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]
    exact res_embLL T ht.alg ht.laws.pins.2.2.1
  have hg : GoodEmb T.Q.c (res T (sg0 D A)) := e ▸ T.toCore.good_σ₀
  obtain rfl : σ = res T (sg0 D A) := hσ.trans e.symm
  have hb : BaseFrT T.toCore R := by
    intro j τ hτ hW
    have hj : InR D ((j : ℕ) + 1) := inR j
    obtain ⟨th, hr, hth, hd⟩ := ht.laws.dictU _ hj _ hτ
    obtain ⟨hr', g, e, F, ik, φ, th', -, -, hth', -, hL⟩ := ht.laws.adPin _ hj _ hτ
    obtain ⟨hr'', hw⟩ := ht.laws.modelW _ hj _ hτ
    have e' : th' = th := funext fun k => funext fun τ => GlobalTheory.SmoothForms.RealPts.infEmb_unique _ _ _ (hth' k τ) (hth k τ)
    subst e'
    exact GlobalTheory.HolDict.BaseFrame.baseFr_of hW _ hM.inf hr _ hth hd (ht.x0 j τ hτ)
      (fun k ρ => (((ht.laws.unf _ hj _ hτ).2.1 k).2 _).2 (ht.laws.pins.1.2.2.2 ρ)) hw (ht.laws.familyUniformisationBasePointOrthogonal _ hj _ hτ)
      fun h => (hL h).imp fun γ hγ => ⟨hγ.1, hγ.2.2.2⟩
  obtain ⟨γ, h1, h2, -⟩ := (hb i (sg0 D A) hg hV).2.2 h
  exact ⟨γ, h1, h2⟩

set_option maxHeartbeats 12000000 in
theorem frame_change : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
    ∀ (ph : ℂ) (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E), ‖ph‖ = 1 → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis (Vc D i) b →
      (∀ (h : GA D (Wc D i)), ∀ γ ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ h →
      ∀ (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom)
        (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) (Y : UnitAt Wt)
        (X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (z : Fin (Vc D i).rank → Fin Wt.g → ℂ),
        (∀ a, z a = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt fun m => ∑ n, X (Fin.cast (rank_Wc i).symm m) n * b n a) →
        Complex.exp (Real.pi / 2 * ∑ a, hermForm Y.Hm (z a) (z a)) *
            GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * h) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X) =
          ph * (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) * ∏ a, Y.θ (z a)) →
    ∀ γ' ∈ GQ (Wc D i),
    ∃ γ ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ h ∧
      ∃ M : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E, Formalism.L2.Theta.mt (Wc D i) (γ * γ'⁻¹) = M.map (Formalism.L2.Theta.incA D) ∧
      ∃ (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) (Y : UnitAt Wt),
        ∀ (Z : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (w : Fin (Vc D i).rank → Fin Wt.g → ℂ),
          (∀ c, w c = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt fun m => ∑ n, (M * Z) (Fin.cast (rank_Wc i).symm m) n * b n c) →
          GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ' * h) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) Z) =
            ph * (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) * ∏ c, (Complex.exp (-(Real.pi / 2 * hermForm Y.Hm (w c) (w c))) * Y.θ (w c)) := by
  intro D hHk hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV P p k α Rc hS h hx
    ph b hph hbON hpin γ' hγ'
  obtain ⟨γ, hγ, hfr⟩ := exists_frAt hMod hTie i σ hσ hV h
  obtain ⟨M, hM⟩ := Formalism.IndefR.Eqv.mt_GQ _ (mul_mem hγ (inv_mem hγ'))
  obtain ⟨_, Wt, ⟨Y⟩⟩ := exists_witness T i σ hV hTie.laws.toLawsM (hσ ▸ T.toCore.good_σ₀) h
  refine ⟨γ, hγ, hfr, M, hM, Wt, Y, fun Z w hw => ?_⟩
  have hω := hThP.ωP i A.μ0
  have hv : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) := (hThP.vP i A.μ0).1.2.theta
  have key : thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ' * h) (realPt (Vc D i) (Wc D i) Z) =
      thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * h) (realPt (Vc D i) (Wc D i) (M * Z)) := by
    rw [thetaAt_eq, thetaAt_eq]
    have e : ((1 : GA D (Vc D i)), γ' * h) = (1, (γ * γ'⁻¹)⁻¹) * (1, γ * h) := by
      simp [mul_assoc]
    rw [e, map_mul, Module.End.mul_apply,
      GlobalTheory.RawLift.Move.om_rat_inv_apply hω (mul_mem hγ (inv_mem hγ')) (hω.om_pres _ _ hv),
      GlobalTheory.RawLift.Move.actO_one_left, hM, map_incA_mul_realPt]
  have h1 := hpin h γ hγ hfr hx Wt Y (M * Z) w hw
  rw [key]
  have h3 : Complex.exp (Real.pi / 2 * ∑ c, hermForm Y.Hm (w c) (w c)) *
      ∏ c, Complex.exp (-(Real.pi / 2 * hermForm Y.Hm (w c) (w c))) = 1 := by
    rw [← Complex.exp_sum, ← Complex.exp_add, Finset.sum_neg_distrib, Finset.mul_sum, add_neg_cancel, Complex.exp_zero]
  rw [Finset.prod_mul_distrib]
  linear_combination (∏ c, Complex.exp (-(Real.pi / 2 * hermForm Y.Hm (w c) (w c)))) * h1 -
    thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * h) (realPt (Vc D i) (Wc D i) (M * Z)) * h3

end GlobalTheory.FrameChangeRead
end
end

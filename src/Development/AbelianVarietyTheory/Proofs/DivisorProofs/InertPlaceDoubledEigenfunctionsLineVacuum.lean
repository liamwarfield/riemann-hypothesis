module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegmentRepresentation
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGLOfExhaustion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceDoubledEigenfunctionsLineVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceDoubledEigenfunctionsLineVacuum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.VDblLine

theorem vdbl_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • G.M.vac v)) →
    ∀ φ ∈ SB ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v), (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ)) → ∃ c : ℂ, φ = c • (boxFun (G.M.vac v) (fun x => star (G.M.vac v x))) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv d' hd' dd hdc θ hθ hvac φ hφSB hφ
  classical
  have hψ := hT.base.std
  have hn := GlobalTheory.StdCharFromIsStd.norm_psi hψ
  have hnv : ∀ t, ‖GlobalTheory.LatVac.psiAt B.ψ v t‖ = 1 := fun t => hn (GlobalTheory.LatVac.liftV v t)
  set Λ := latAtV G.V G.W v with hΛ
  have hat : ∀ γ ∈ Λ, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).1
  have hatT : ∀ γ ∈ Λ, At (evFin F v) γᵀ := fun γ h u hu => by
    rw [← Matrix.transpose_smul, hat γ h u hu, Matrix.transpose_zero]
  obtain ⟨hvSB, hv0, -⟩ := hT.geo.hM.vac v
  set φ₀ := G.M.vac v with hφ₀
  set φd := boxFun φ₀ (fun x => star (φ₀ x)) with hφd

  have loc : ∀ {κ : Type} [Fintype κ] {W' : Type} [AddCommGroup W'] [Module (AF F) W'] {Bf : W' → W' → AF F}
      (d : Darboux Bf κ) (f : (κ → Fv F v) → ℂ), f ∈ SB _ → ∀ γ, At (evFin F v) γ → ∀ c : ℂ,
      Acts (evFin F v) (d.rho B.ψ γ) f (c • f) →
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo d v γ) f = c • f := by
    intro κ _ W' _ _ Bf d f hf γ hγ c h
    obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v f hf
    refine GlobalTheory.DblVacLine.eq_of_tens v hr.1 hx₀ ?_
    rw [← GlobalTheory.VacBridge.rho_acts_locCo d B.ψ v γ hγ f r hr]
    exact h r hr
  have hco : ∀ w₁ w₂ : Matrix (Fin a) (Fin (a + a')) (AE F E),
      GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ᵀ w₂ᵀ) =
      (Sum.elim (GlobalTheory.LatVac.locCo G.M.co v w₁).1 (GlobalTheory.LatVac.locCo G.M.co v w₂).1,
        Sum.elim (GlobalTheory.LatVac.locCo G.M.co v w₁).2 (-(GlobalTheory.LatVac.locCo G.M.co v w₂).2)) := by
    intro w₁ w₂
    change ((fun k => evFin F v ((dd.e (Matrix.fromCols w₁ᵀ w₂ᵀ)).1 k)),
      fun k => evFin F v ((dd.e (Matrix.fromCols w₁ᵀ w₂ᵀ)).2 k)) = _
    rw [hdc, hd', hd']
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · cases k <;> rfl
    · cases k with
      | inl k => rfl
      | inr k => exact map_neg (evFin F v) _
  let χ : Matrix (Fin a) (Fin (a + a')) (AE F E) → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ)
  let cf : Matrix (Fin a) (Fin (a + a')) (AE F E) → Matrix (Fin a) (Fin (a + a')) (AE F E) → ℂ := fun w₁ w₂ =>
    B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
      (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ))
  have ht : ∀ w : Matrix (Fin a) (Fin (a + a')) (AE F E),
      symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) wᵀ wᵀ =
        symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w w := fun w => by
    rw [GlobalTheory.WeilTr.symp_transpose (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) _ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) wᵀ wᵀ, Matrix.transpose_transpose]
  have hcf : ∀ w₁ w₂, cf w₁ w₂ = χ w₁ * star (χ w₂) := by
    intro w₁ w₂
    simp only [cf, χ]
    rw [GlobalTheory.DblVacLine.symp_dbl, GlobalTheory.DblVacLine.star_eq_neg B.ψ hn, ht, ht, ← AddChar.map_add_eq_mul, mul_sub,
      sub_eq_add_neg]
  have hvl : ∀ γ ∈ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) φ₀ = χ γ • φ₀ :=
    fun γ h => loc G.M.co φ₀ hvSB γ (hat γ h) _ (hvac γ h)
  have hφl : ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ,
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ = cf w₁ w₂ • φ :=
    fun w₁ h₁ w₂ h₂ => loc dd φ hφSB _ (GlobalTheory.DblVacLine.at_fromCols v (hatT w₁ h₁) (hatT w₂ h₂)) _ (hφ w₁ h₁ w₂ h₂)
  have hdl : ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ,
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ᵀ w₂ᵀ)) φd = cf w₁ w₂ • φd := by
    intro w₁ h₁ w₂ h₂
    rw [hco, hφd, GlobalTheory.DblVacLine.schr_box _ hnv, hvl w₁ h₁, hvl w₂ h₂, hcf]
    funext x
    simp only [boxFun, Pi.smul_apply, smul_eq_mul, star_mul']
    ring

  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded G.V G.W v G.M.co hT.geo.hV.lat.toIsLattice hT.geo.hW.lat.toIsLattice
  have hsd := GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B _ _ G.V G.W _ _ _ _ hT.base hT.geo.hV hT.geo.hW v
  have hfill := GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (GlobalTheory.LatVac.psiAt B.ψ v)
    (Λ.map (GlobalTheory.LatVac.locCo G.M.co v)) c hc0 (fun x => (hT.base.inert v w hw).2.2 x)
    (GlobalTheory.LatVac.DualLoc.map_selfDual v G.M.co B.ψ Λ hat hsd)
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  have hφd0 : φd ≠ 0 := by
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hv0
    refine Function.ne_iff.mpr ⟨Sum.elim t t, ?_⟩
    show φ₀ t * star (φ₀ t) ≠ 0
    exact mul_ne_zero ht (star_ne_zero.mpr ht)
  obtain ⟨c', hc'⟩ := GlobalTheory.VacUniqInert.eq_smul_of_eigen (GlobalTheory.LatVac.psiAt B.ψ v)
    (fun i : Λ × Λ => GlobalTheory.LatVac.locCo dd v (Matrix.fromCols i.1.1ᵀ i.2.1ᵀ))
    (fun i => cf i.1.1 i.2.1) (fun u hu => by
      have eu : u = Sum.elim (u ∘ Sum.inl) (u ∘ Sum.inr) := (Sum.elim_comp_inl_inr u).symm
      obtain ⟨y₁, γ₁, h₁, e₁⟩ := hfill (u ∘ Sum.inl) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (⟨γ, hγ⟩, 0) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero]
          funext k; cases k <;> rfl)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      obtain ⟨y₂, γ₂, h₂, e₂⟩ := hfill (u ∘ Sum.inr) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (0, ⟨-γ, neg_mem hγ⟩) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg]
          funext k; cases k <;> simp)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      refine ⟨(⟨γ₁, h₁⟩, ⟨γ₂, h₂⟩), ?_⟩
      simp only [hco, e₁, e₂]
      exact eu.symm) φ φd
    (fun i => hφl _ i.1.2 _ i.2.2) (fun i => hdl _ i.1.2 _ i.2.2) hφd0
  exact ⟨c', hc'⟩

end GlobalTheory.VDblLine

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceDoubledEigenfunctionsLineVacuumStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_doubledEigenfunctions_line_vacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • G.M.vac v)) →
    ∀ φ ∈ SB ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v), (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ)) → ∃ c : ℂ, φ = c • (boxFun (G.M.vac v) (fun x => star (G.M.vac v x))) := by
  first | exact @GlobalTheory.VDblLine.vdbl_line | exact GlobalTheory.VDblLine.vdbl_line | (intros; apply GlobalTheory.VDblLine.vdbl_line <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightCombinatorialDataULeUZero
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)

namespace GlobalTheory.ExpTie.Lift

variable {D : D7}

abbrev lamL (j : Fin D.R.m) (τ : D.what₂.Tau) : DomWeight (Vc D j).rank :=
  Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ

def lamT (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) : ℕ :=
  if h : a < (Vc D j).rank then (lamL j τ).natW ⟨a, h⟩ else 0

def cT (j : Fin D.R.m) (τ : D.what₂.Tau) : ℝ :=
  ((Vc D j).rank : ℝ) / 2 - 1 - ((lamL j τ).detShift : ℝ)


open Classical in
def wts (L : SizeData₂ D) (j : Fin D.R.m) : Wts D.what₂.Tau where
  lam := lamT j
  T2 := Finset.univ.filter fun τ => (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
  j := fun _ => (j : ℕ) + 1
  q := fun _ => D.R.m - ((j : ℕ) + 1)
  xm := fun τ => ⌈cT j τ⌉
  xp := fun τ => ⌊cT j τ + L.Sc⌋
  c := cT j
  e := fun τ => wj D ((j : ℕ) + 1) τ
  fr := fun _ τ => τ
  cj := fun _ _ => false
  Sp := Formalism.MainNotions.JumpSetsAlt.excSet D

def ValsAt (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) : Prop :=
  (∀ (a : ℕ) (ha : a < D.R.k - 1),
      ((wts L j).U (parOf L j) τ a : ℝ) - (wts L j).c τ = (((D.hc τ).v ⟨a, ha⟩ : ℚ) : ℝ)) ∧
    (∀ i : Fin D.R.m, (i : ℕ) ≤ j →
      ((wts L j).U (parOf L j) τ (D.R.k - 1 + i) : ℝ) - (wts L j).c τ = -(((D.hc τ).b i : ℚ) : ℝ)) ∧
    (∀ s : ℕ, s < D.R.t →
      ((wts L j).U (parOf L j) τ (D.R.k + j + s) : ℝ) - (wts L j).c τ =
        -wj D ((j : ℕ) + 1) τ + ((D.R.t : ℝ) - 1) / 2 - s) ∧
    (∀ i : Fin D.R.m, (j : ℕ) < i →
      ((wts L j).U (parOf L j) τ (D.R.k - 1 + i + D.R.t) : ℝ) - (wts L j).c τ = -(((D.hc τ).b i : ℚ) : ℝ))

end GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

open Formalism.IndefR.Bridge

variable {D : D7}

theorem lamT_of_lt (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) (h : a < (Vc D j).rank) :
    (lamT j τ a : ℤ) = (lamL j τ).w ⟨a, h⟩ - (lamL j τ).detShift := by
  have hn : 0 < (Vc D j).rank := by omega
  have hle : (lamL j τ).detShift ≤ (lamL j τ).w ⟨a, h⟩ := by
    unfold DomWeight.detShift
    rw [dite_eq_left hn]
    exact (lamL j τ).anti (Fin.mk_le_mk.2 (by omega))
  unfold lamT DomWeight.natW
  rw [dite_eq_left h]
  omega

theorem anti (L : SizeData₂ D) (j : Fin D.R.m) : ∀ τ a b, a ≤ b → b < (parOf L j).Nr → (wts L j).lam τ b ≤ (wts L j).lam τ a := by
  intro τ a b hab hb
  have ha : a < (Vc D j).rank := lt_of_le_of_lt hab hb
  have h1 := lamT_of_lt j τ a ha
  have h2 := lamT_of_lt j τ b hb
  have h3 := (lamL j τ).anti (show (⟨a, ha⟩ : Fin _) ≤ ⟨b, hb⟩ from Fin.mk_le_mk.2 hab)
  show lamT j τ b ≤ lamT j τ a
  omega

theorem rank_eq (j : Fin D.R.m) : (Vc D j).rank = D.R.k - 1 + D.R.m + D.R.t := by
  have h := D.sp.V_rank ((j : ℕ) + 1) (by omega) (by omega)
  have hk := D.R.m_add_three_le_k
  simp only [Vc, h, Ranks.nV, Ranks.r]
  omega

theorem what₂ (L : SizeData₂ D) (j : Fin D.R.m) : ∀ τ, Formalism.CohomologicalDescent.ShortWeightBounds.kc (parOf L j) + (wts L j).j τ + (parOf L j).t + (wts L j).q τ = (parOf L j).Nr := by
  intro τ
  have := rank_eq j
  have hj := j.2
  simp only [Formalism.CohomologicalDescent.ShortWeightBounds.kc, parOf, wts]
  omega

end GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

open Formalism.IndefR.Bridge

variable {D : D7}

theorem U_last (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) :
    (wts L j).U (parOf L j) τ ((Vc D j).rank - 1) = 0 := by
  have hn := rank_eq j
  have ht0 := D.R.t_odd.pos
  have hlt : (Vc D j).rank - 1 < (Vc D j).rank := by omega
  have h1 := lamT_of_lt j τ _ hlt
  have h2 : (lamL j τ).detShift = (lamL j τ).w ⟨(Vc D j).rank - 1, hlt⟩ := by
    unfold DomWeight.detShift; rw [dite_eq_left (by omega)]
  show Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) ((Vc D j).rank - 1) = 0
  unfold Formalism.CohomologicalDescent.UnitNormBounds.UN
  omega

theorem liftWeightCombinatorialData_U_le_U_zero (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) (ha : a < (Vc D j).rank) :
    (wts L j).U (parOf L j) τ a ≤ (wts L j).U (parOf L j) τ 0 := by
  have h := anti L j τ 0 a (Nat.zero_le _) ha
  show Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) a ≤ Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) 0
  change lamT j τ a ≤ lamT j τ 0 at h
  unfold Formalism.CohomologicalDescent.UnitNormBounds.UN
  omega

theorem U_nonneg (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) (ha : a < (Vc D j).rank) :
    0 ≤ (wts L j).U (parOf L j) τ a := by
  show 0 ≤ Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) a
  unfold Formalism.CohomologicalDescent.UnitNormBounds.UN
  omega

theorem T2_card (L : SizeData₂ D) (j : Fin D.R.m) : (wts L j).T2.card ≤ D.host.T2.card := by
  classical
  calc (wts L j).T2.card ≤ D.host.thickPlaces.card := by
        refine Finset.card_le_card_of_injOn (fun τ => (D.eTau τ : D.R.GG)) ?_ ?_
        · intro τ hτ
          simp only [wts, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hτ
          exact hτ
        · intro a _ b _ h
          exact D.eTau.injective (Subtype.ext h)
    _ ≤ D.host.T2.card := by
        unfold Host.thickPlaces
        exact Finset.card_image_le

theorem c_le (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (hv : ValsAt L j τ) :
    (wts L j).c τ ≤ wj D D.R.m τ + ((D.R.t : ℝ) - 1) / 2 := by
  have hn := rank_eq j
  have hU := U_last L j τ
  have ht : (1 : ℝ) ≤ D.R.t := by exact_mod_cast D.R.t_odd.pos
  have ht0 := D.R.t_odd.pos
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hm : 0 < D.R.m := by omega
  by_cases hj : (j : ℕ) + 1 < D.R.m
  · have h := hv.2.2.2 ⟨D.R.m - 1, by omega⟩ (by simp; omega)
    have hrow : D.R.k - 1 + (D.R.m - 1) + D.R.t = (Vc D j).rank - 1 := by omega
    simp only [hrow, hU] at h
    have hg := (D.hc τ).gap_be ⟨D.R.m - 1, by omega⟩
    have hw : wj D D.R.m τ = (((D.hc τ).e ⟨D.R.m - 1, by omega⟩ : ℚ) : ℝ) := by
      unfold wj; rw [dite_eq_left (by omega)]
    have hg' : (((D.hc τ).b ⟨D.R.m - 1, by omega⟩ : ℚ) : ℝ) + ((D.R.t : ℝ) + 3) / 2 ≤
        (((D.hc τ).e ⟨D.R.m - 1, by omega⟩ : ℚ) : ℝ) := by
      have h2 : ((((D.hc τ).e ⟨D.R.m - 1, by omega⟩ - (D.hc τ).b ⟨D.R.m - 1, by omega⟩ : ℚ)) : ℝ) ≥ ((((D.R.t : ℚ) + 3) / 2 : ℚ) : ℝ) := by
        exact_mod_cast hg
      push_cast at h2
      linarith
    push_cast at h
    rw [hw]; linarith
  · have hjm : (j : ℕ) + 1 = D.R.m := by omega
    have h := hv.2.2.1 (D.R.t - 1) (by omega)
    have hrow : D.R.k + (j : ℕ) + (D.R.t - 1) = (Vc D j).rank - 1 := by omega
    simp only [hrow, hU] at h
    have hts : ((D.R.t - 1 : ℕ) : ℝ) = (D.R.t : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hts, hjm] at h
    push_cast at h
    linarith

end GlobalTheory.ExpTie.Lift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaPrimeAllPoints
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie

namespace GlobalTheory.LiftWeightForced

open Formalism.IndefR.IndefiniteWeightData

def wd (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau) : WeightData where
  k := D.R.k
  m := D.R.m
  t := D.R.t
  j := (j : ℕ) + 1
  e := ((D.hc τ).e_int j).choose
  v := fun n => if h : 2 ≤ n ∧ n - 2 < D.R.k - 1 then ((D.hc τ).v_int ⟨n - 2, h.2⟩).choose else 0
  b := fun n => if h : 1 ≤ n ∧ n - 1 < D.R.m then ((D.hc τ).b_int ⟨n - 1, h.2⟩).choose else 0

variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)

theorem wd_e : ((wd D j τ).e : ℚ) = (D.hc τ).e j := ((D.hc τ).e_int j).choose_spec.symm

theorem wd_v (n : ℕ) (h : 2 ≤ n ∧ n - 2 < D.R.k - 1) : ((wd D j τ).v n : ℚ) = (D.hc τ).v ⟨n - 2, h.2⟩ := by
  show (((if h : 2 ≤ n ∧ n - 2 < D.R.k - 1 then ((D.hc τ).v_int ⟨n - 2, h.2⟩).choose else 0 : ℤ)) : ℚ) = _
  rw [dite_eq_left h]
  exact ((D.hc τ).v_int _).choose_spec.symm

theorem wd_b (n : ℕ) (h : 1 ≤ n ∧ n - 1 < D.R.m) : ((wd D j τ).b n : ℚ) = (D.hc τ).b ⟨n - 1, h.2⟩ := by
  show (((if h : 1 ≤ n ∧ n - 1 < D.R.m then ((D.hc τ).b_int ⟨n - 1, h.2⟩).choose else 0 : ℤ)) : ℚ) = _
  rw [dite_eq_left h]
  exact ((D.hc τ).b_int _).choose_spec.symm

end GlobalTheory.LiftWeightForced

namespace GlobalTheory.LiftWeightForced

open Formalism.IndefR.IndefiniteWeightData

variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)

theorem wd_lam_lo (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ D.R.k - 1) :
    ((wd D j τ).lam i : ℚ) = (D.hc τ).v ⟨i - 1, by omega⟩ := by
  have hk : (wd D j τ).k = D.R.k := rfl
  unfold WeightData.lam
  rw [if_pos (by rw [hk]; exact h2), wd_v D j τ (i + 1) ⟨by omega, by omega⟩]
  exact congrArg _ (Fin.ext (by simp))

theorem wd_lam_hi (i : ℕ) (h1 : D.R.k - 1 < i) (h2 : i - (D.R.k - 1) - 1 < D.R.m) :
    ((wd D j τ).lam i : ℚ) = -(D.hc τ).b ⟨i - (D.R.k - 1) - 1, h2⟩ := by
  have hk : (wd D j τ).k = D.R.k := rfl
  unfold WeightData.lam
  rw [if_neg (by rw [hk]; omega)]
  push_cast
  rw [hk, wd_b D j τ _ ⟨by omega, h2⟩]

theorem wd_hyp : (wd D j τ).Hyp := by
  have hR := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hjm := j.2
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  set P := D.hc τ with hP
  have hu : ∀ a b : Fin D.R.k, a.1 = b.1 → P.u a = P.u b := fun a b h => congrArg _ (Fin.ext h)
  have hb : ∀ a b : Fin D.R.m, a.1 = b.1 → P.b a = P.b b := fun a b h => congrArg _ (Fin.ext h)
  refine ⟨show 1 ≤ D.R.k by omega, show 1 ≤ (j : ℕ) + 1 by omega, show (j : ℕ) + 1 ≤ D.R.m by omega, ?_, D.R.t_odd, ?_, ?_, ?_⟩
  · show Odd (D.R.k + D.R.m - 1)
    exact Nat.Even.sub_odd (by omega) (D.R.k_even.add D.R.m_even) odd_one
  · intro i hi1 hi2
    have hi2' : i < D.R.k + D.R.m - 1 := hi2
    suffices ((wd D j τ).lam (i + 1) : ℚ) < (wd D j τ).lam i by exact_mod_cast this
    rcases lt_trichotomy (i + 1) (D.R.k) with h | h | h
    · rw [wd_lam_lo D j τ (i + 1) (by omega) (by omega), wd_lam_lo D j τ i hi1 (by omega)]
      have h1 := P.u_gt_v ⟨i, by omega⟩
      have h2 := P.v_gt_u ⟨i - 1, by omega⟩
      rw [hu ⟨i - 1 + 1, _⟩ ⟨i, by omega⟩ (by simp; omega)] at h2
      have e1 : (⟨i + 1 - 1, by omega⟩ : Fin (D.R.k - 1)) = ⟨i, by omega⟩ := Fin.ext (by simp)
      rw [e1]
      exact h1.trans h2
    · rw [wd_lam_hi D j τ (i + 1) (by omega) (by omega), wd_lam_lo D j τ i hi1 (by omega)]
      have h1 := P.u_last_gt (by omega) (by omega)
      have h2 := P.v_gt_u ⟨i - 1, by omega⟩
      rw [hu ⟨i - 1 + 1, _⟩ ⟨D.R.k - 1, by omega⟩ (by simp; omega)] at h2
      rw [hb ⟨i + 1 - (D.R.k - 1) - 1, _⟩ ⟨0, by omega⟩ (by simp; omega)]
      exact h1.trans h2
    · rw [wd_lam_hi D j τ (i + 1) (by omega) (by omega), wd_lam_hi D j τ i (by omega) (by omega)]
      have h1 := P.gap_be ⟨i - (D.R.k - 1) - 1, by omega⟩
      have h2 := P.gap_eb ⟨i - (D.R.k - 1) - 1, by omega⟩ (by simp; omega)
      rw [hb ⟨i - (D.R.k - 1) - 1 + 1, _⟩ ⟨i + 1 - (D.R.k - 1) - 1, by omega⟩ (by simp; omega)] at h2
      linarith
  · show (((wd D j τ).b ((j : ℕ) + 1)) : ℤ) < (wd D j τ).e
    suffices ((wd D j τ).b ((j : ℕ) + 1) : ℚ) < (wd D j τ).e by exact_mod_cast this
    rw [wd_b D j τ _ ⟨by omega, by omega⟩, wd_e, hb _ j (by simp)]
    have := P.gap_be j
    linarith
  · intro hj'
    have hj'' : (j : ℕ) + 1 < D.R.m := hj'
    show ((wd D j τ).e : ℤ) < (wd D j τ).b ((j : ℕ) + 1 + 1)
    suffices ((wd D j τ).e : ℚ) < (wd D j τ).b ((j : ℕ) + 1 + 1) by exact_mod_cast this
    rw [wd_b D j τ _ ⟨by omega, by omega⟩, wd_e, hb _ ⟨(j : ℕ) + 1, hj''⟩ (by simp)]
    have := P.gap_eb j hj''
    linarith

theorem wd_gap : (wd D j τ).GapHyp := by
  have hjm := j.2
  set P := D.hc τ with hP
  have hb : ∀ a b : Fin D.R.m, a.1 = b.1 → P.b a = P.b b := fun a b h => congrArg _ (Fin.ext h)
  refine ⟨?_, ?_⟩
  · show ((D.R.t : ℚ) + 3) / 2 ≤ ((wd D j τ).e : ℚ) - (wd D j τ).b ((j : ℕ) + 1)
    rw [wd_b D j τ _ ⟨by omega, by omega⟩, wd_e, hb _ j (by simp)]
    exact P.gap_be j
  · intro hj'
    have hj'' : (j : ℕ) + 1 < D.R.m := hj'
    show ((D.R.t : ℚ) + 3) / 2 ≤ ((wd D j τ).b ((j : ℕ) + 1 + 1) : ℚ) - (wd D j τ).e
    rw [wd_b D j τ _ ⟨by omega, by omega⟩, wd_e, hb _ ⟨(j : ℕ) + 1, hj''⟩ (by simp)]
    exact P.gap_eb j hj''

end GlobalTheory.LiftWeightForced

namespace GlobalTheory.LiftWeightForced

open Formalism.IndefR.IndefiniteWeightData

variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)

theorem exists_isLamPrime :
    ∃ lam : DomWeight (Vc D j).rank, Formalism.IndefR.Bridge.IsLamPrime (D := D) lam ((j : ℕ) + 1) τ := by
  have hjm := j.2
  have hC := GlobalTheory.LowestKType.thetaSide (wd D j τ) (wd_hyp D j τ) (wd_gap D j τ)
  have hint := hC.2.2.2.1
  have hdom := hC.2.2.2.2.1
  have hN : (Vc D j).rank = (wd D j τ).nV := D.sp.V_rank _ (by omega) (by omega)

  have hmono : ∀ d a : ℕ, 1 ≤ a → a + d ≤ (wd D j τ).nV →
      (wd D j τ).lamPrime (a + d) ≤ (wd D j τ).lamPrime a := by
    intro d
    induction d with
    | zero => intro a _ _; simp
    | succ d ih =>
      intro a ha had
      have := hdom (a + d) (by omega) (by omega)
      rw [← add_assoc]
      exact this.trans (ih a ha (by omega))
  let w : Fin (Vc D j).rank → ℤ := fun i => (hint (i.1 + 1) (by omega) (by have := i.2; omega)).choose
  have hw : ∀ i, (w i : ℚ) = (wd D j τ).lamPrime (i.1 + 1) := fun i =>
    (hint (i.1 + 1) (by omega) (by have := i.2; omega)).choose_spec.symm
  have hanti : Antitone w := by
    intro a b hab
    have hab' : a.1 ≤ b.1 := hab
    have := hmono (b.1 - a.1) (a.1 + 1) (by omega) (by have := b.2; omega)
    rw [show a.1 + 1 + (b.1 - a.1) = b.1 + 1 by omega] at this
    have h' : (w b : ℚ) ≤ w a := by rw [hw, hw]; exact this
    exact_mod_cast h'
  refine ⟨⟨w, hanti⟩, ⟨by omega, by omega⟩, wd D j τ, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [wd_e]
    exact congrArg _ (Fin.ext (by simp))
  · intro a
    rw [wd_v D j τ _ ⟨by omega, by have := a.2; omega⟩]
    exact congrArg _ (Fin.ext (by simp))
  · intro a
    rw [wd_b D j τ _ ⟨by omega, by have := a.2; omega⟩]
    exact congrArg _ (Fin.ext (by simp))
  · intro i
    exact hw i

theorem isLamPrime_lamLdef :
    Formalism.IndefR.Bridge.IsLamPrime (D := D)
      (Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ := by
  have hex := exists_isLamPrime D j τ
  unfold Formalism.IndefR.Bridge.lamLdef
  rw [dite_eq_left hex]
  exact hex.choose_spec

end GlobalTheory.LiftWeightForced
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSectionsFiniteSpan
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Adelic

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SectionsFieldChange

open GlobalTheory.AbLaw
open scoped TensorProduct

variable {X Y : Scheme.{0}}

theorem ofSec_secPull {L : LB X} (s : L.Sec) (π : Y ⟶ X) (V : X.Opens) :
    GlobalTheory.LB.ofSec (secPull s π) (π ⁻¹ᵁ V) =
      SecOn.pullLE L π V (π ⁻¹ᵁ V) le_rfl (GlobalTheory.LB.ofSec s V) := by
  refine GlobalTheory.LB.sec_ext fun j => ?_
  rw [GlobalTheory.LB.coord_ofSec, SecOn.coord_pullLE, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.appLE_resG]
  exact GlobalTheory.LB.resG_appLE π _ _ (s.f (j PUnit.unit))

theorem ofSec_smul {L : LB X} (a : Γ(X, ⊤)) (s : L.Sec) (V : X.Opens) :
    GlobalTheory.LB.ofSec (a • s) V = rs X (le_top : V ≤ ⊤) a • GlobalTheory.LB.ofSec s V := by
  refine GlobalTheory.LB.sec_ext fun j => ?_
  rw [GlobalTheory.LB.coord_smul, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.coord_ofSec, LB.smul_f, map_mul, GlobalTheory.resG_resG]
  exact congrArg (· * _) (GlobalTheory.resG_resG _ _ _).symm

variable {F E : Type} [Field F] [Field E] [Algebra F E]

abbrev secModule {k : Type} [Field k] (S : LinSys k) : Module k S.L.Sec :=
  Module.compHom _ (algebraMap k Γ(S.Y, ⊤))

attribute [local instance] secModule

theorem secTower {k : Type} [Field k] (S : LinSys k) : IsScalarTower k Γ(S.Y, ⊤) S.L.Sec :=
  ⟨fun a g s => by
    show (algebraMap k Γ(S.Y, ⊤) a * g) • s = algebraMap k Γ(S.Y, ⊤) a • (g • s)
    rw [mul_smul]⟩

attribute [local instance] secTower

theorem isProper_str {k : Type} [Field k] {S : LinSys k} (hS : S.IsVariety) : IsProper S.str := by
  obtain ⟨N, i, hi, e⟩ := hS.proj
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str k N
  rw [← e]
  infer_instance

theorem finite_sec {k : Type} [Field k] {S : LinSys k} (hS : S.IsVariety) : Module.Finite k S.L.Sec := by
  have hfin : Module.Finite k (coh (twist (structureModule S.Y) S.L) 0) :=
    finite_coh_zero_twist_of_isProjOver (f := S.str) (fun _ => rfl) hS.proj S.isLB
  exact Module.Finite.equiv ((cohZeroTwistEquiv S.L).restrictScalars k)

theorem finrank_baseChange (S : LinSys F) (hS : S.IsVariety) :
    Module.finrank E (S.baseChange E).L.Sec = Module.finrank F S.L.Sec := by
  have := isProper_str hS
  rw [← lineBundleGlobalSectionsDim_eq_finrank, ← lineBundleGlobalSectionsDim_eq_finrank, lineBundleGlobalSectionsDim_def, lineBundleGlobalSectionsDim_def]
  exact FieldChangeInter.hdim_pull (S.isPullback_baseChange E) S.isLB 0

def resTo {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (L : LB X) (V : X.Opens) :
    L.Sec →+ SecOnR f L V where
  toFun s := SecOnR.of f L V (GlobalTheory.LB.ofSec s V)
  map_zero' := SecOnR.ext fun i => by
    rw [SecOnR.coord_of, GlobalTheory.LB.coord_ofSec, LB.zero_f, map_zero, SecOnR.coord_zero]
  map_add' s t := SecOnR.ext fun i => by
    rw [SecOnR.coord_add, SecOnR.coord_of, SecOnR.coord_of, SecOnR.coord_of, GlobalTheory.LB.coord_ofSec,
      GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.coord_ofSec, LB.add_f, map_add]

theorem resTo_smul {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (L : LB X) (V : X.Opens)
    (a : R) (s : L.Sec) :
    letI := algebraΓOfHom f
    resTo f L V (algebraMap R Γ(X, ⊤) a • s) = a • resTo f L V s :=
  ofSec_smul _ s V

theorem resTo_secPull (S : LinSys F) (E : Type) [Field E] [Algebra F E] (V : S.Y.Opens) (s : S.L.Sec) :
    resTo (S.baseChange E).str (S.baseChange E).L (S.bcFst E ⁻¹ᵁ V) (secPull s (S.bcFst E)) =
      SecOnR.pull S.L (S.isPullback_baseChange E).w V _ le_rfl (resTo S.str S.L V s) :=
  congrArg (SecOnR.of _ _ _) (ofSec_secPull s (S.bcFst E) V)

def pullSecs (S : LinSys F) (E : Type) [Field E] [Algebra F E] {n : ℕ} (b : Fin n → S.L.Sec) :
    Fin n → (S.baseChange E).L.Sec := fun j => secPull (b j) (S.bcFst E)

theorem linearIndependent_secPull (S : LinSys F) (hS : S.IsVariety) {n : ℕ} (b : Fin n → S.L.Sec)
    (hb : LinearIndependent F b) :
    LinearIndependent E (pullSecs S E b) := by
  classical
  have := isProper_str hS
  haveI : CompactSpace S.Y := QuasiCompact.compactSpace_of_compactSpace S.str
  obtain ⟨m, D, hD, hc⟩ := GlobalTheory.exists_fin_affine_cover (X := S.Y) (V := ⊤) isCompact_univ
  have H := S.isPullback_baseChange E
  let R : (Fin n → F) →ₗ[F] (∀ i, SecOnR S.str S.L (D i)) :=
    LinearMap.pi fun i => ∑ j, (LinearMap.proj j).smulRight (resTo S.str S.L (D i) (b j))
  have hRi : ∀ u i, R u i = resTo S.str S.L (D i) (∑ j, u j • b j) := fun u i => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [R, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.proj_apply]
    exact Finset.sum_congr rfl fun j _ => (resTo_smul S.str S.L (D i) (u j) (b j)).symm
  have hR : Function.Injective R := by
    refine (injective_iff_map_eq_zero R).2 fun u hu => ?_
    have h2 : ∑ j, u j • b j = 0 := by
      refine (SecOn.ofSec_bijective (M := S.L) (V := ⊤) rfl).injective ?_
      refine SecOn.ext_of_cover D (fun _ => le_top) hc.ge fun a => ?_
      rw [SecOn.restrict_ofSec, SecOn.restrict_ofSec]
      have := (hRi u a).symm.trans (congrFun hu a)
      exact this.trans (map_zero (resTo S.str S.L (D a))).symm
    funext j
    exact Fintype.linearIndependent_iff.1 hb u h2 j
  let Bc : ∀ i, E ⊗[F] SecOnR S.str S.L (D i) →ₗ[E]
      SecOnR (S.baseChange E).str (S.baseChange E).L (S.bcFst E ⁻¹ᵁ D i) := fun i =>
    SecOnR.baseChangeHom S.L H.w (D i) (S.bcFst E ⁻¹ᵁ D i) le_rfl
  have hBc : ∀ i, Function.Bijective (Bc i) := fun i =>
    SecOnR.baseChangeHom_bijective S.isLB H (hD i) rfl
  let Φ : (Fin n → E) →ₗ[E] ∀ i, SecOnR (S.baseChange E).str (S.baseChange E).L (S.bcFst E ⁻¹ᵁ D i) :=
    LinearMap.pi (fun i => Bc i ∘ₗ LinearMap.proj i) ∘ₗ
      (TensorProduct.piRight F E E fun i => SecOnR S.str S.L (D i)).toLinearMap ∘ₗ
      R.baseChange E ∘ₗ (TensorProduct.piScalarRight F E E (Fin n)).symm.toLinearMap
  have hΦ : Function.Injective Φ := by
    have h1 : Function.Injective (R.baseChange E) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap R hR
    have h2 : Function.Injective (LinearMap.pi (fun i => Bc i ∘ₗ LinearMap.proj i) :
        (∀ i, E ⊗[F] SecOnR S.str S.L (D i)) →ₗ[E] _) :=
      fun x y h => funext fun i => (hBc i).1 (congrFun h i)
    exact h2.comp ((TensorProduct.piRight F E E fun i => SecOnR S.str S.L (D i)).injective.comp
      (h1.comp (TensorProduct.piScalarRight F E E (Fin n)).symm.injective))
  have hΦc : ∀ c : Fin n → E, Φ c = fun i =>
      resTo (S.baseChange E).str (S.baseChange E).L (S.bcFst E ⁻¹ᵁ D i) (∑ j, c j • pullSecs S E b j) := by
    intro c
    conv_lhs => rw [← Finset.univ_sum_single c]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Φ, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.piScalarRight_symm_single,
      LinearMap.baseChange_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
      LinearMap.pi_apply, LinearMap.proj_apply, Bc, SecOnR.baseChangeHom_tmul]
    change SecOnR.baseChangeHom S.L H.w (D i) (S.bcFst E ⁻¹ᵁ D i) le_rfl
      (c j ⊗ₜ[F] R (Pi.single j 1) i) = _
    rw [SecOnR.baseChangeHom_tmul, hRi]
    have hs : ∑ k, (Pi.single j (1 : F) : Fin n → F) k • b k = b j := by
      rw [Finset.sum_eq_single j (fun k _ hk => by rw [Pi.single_eq_of_ne hk, zero_smul])
        (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, one_smul]
    rw [hs, ← resTo_secPull]
    exact (resTo_smul _ _ _ (c j) _).symm
  refine Fintype.linearIndependent_iff.2 fun c hc => ?_
  have h0 : Φ c = Φ 0 := by
    rw [hΦc, hc, map_zero]
    funext i
    exact map_zero _
  exact congrFun (hΦ h0)

theorem exists_pullSecs_spanning : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (S : LinSys F),
    S.IsVariety → ∃ (n : ℕ) (b : Fin n → S.L.Sec), ∀ t : (S.baseChange E).L.Sec, ∃ u : Fin n → E,
      (({ S with N := n, b := b } : LinSys F).baseChange E).comb u = t := by
  intro F E _ _ _ S hS
  haveI := finite_sec hS
  haveI : Module.Finite E (S.baseChange E).L.Sec := finite_sec (hS.baseChange E)
  let B := Module.finBasis F S.L.Sec
  refine ⟨_, B, fun t => ?_⟩
  have hli := linearIndependent_secPull (E := E) S hS B B.linearIndependent
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, finrank_baseChange S hS])
  have ht : t ∈ Submodule.span E (Set.range (pullSecs S E B)) := hsp ▸ Submodule.mem_top
  obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 ht
  exact ⟨u, hu⟩

end GlobalTheory.SectionsFieldChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotientProdIrrUc
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GenSph

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in
abbrev uc (a : ℂˣ) : IrrGL (k := k) := IrrGL.ofChar (unrChar k a) (isSmoothChar_of_isUnram (isUnram_unrChar k a))

theorem eq_first_of_isLSeg {Δ : Segment k} {y : IrrGL (k := k)} (h : IsLSeg Δ y.rep) (h1 : Δ.len = 1) : y = Δ.first := by
  have h2 := h.hasSupport
  obtain ⟨z, hz⟩ := Multiset.card_eq_one.1 ((Segment.card_ms Δ).trans h1)
  have h3 : z = Δ.first := by
    have hm : z ∈ Δ.ms := by rw [hz]; exact Multiset.mem_singleton_self z
    obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 hm)
    obtain rfl : a = 0 := by omega
    simp
  rw [hz, h3] at h2
  exact GlobalTheory.CompanionTheory.CuspPairSub.eq_of_hasSupport_singleton h2

theorem isSpherical_prodIrr_uc {c N : ℕ} (β : Fin c → ℂˣ) (hd : ∑ i, (uc k (β i)).1 = N) :
    IsSpherical (prodIrr (fun i => uc k (β i)) hd) := by
  have hv : ∀ i, ∃ v : (uc k (β i)).2.rep.V, v ≠ 0 ∧
      ∀ g ∈ GlobalTheory.SplitWeil.KO k (Fin (uc k (β i)).1), (uc k (β i)).rep g v = v := fun i => by
    let r := IrrRep.det (Fin 1) (unrChar k (β i)) (isSmoothChar_of_isUnram (isUnram_unrChar k (β i)))
    let e := equivRep r
    let u : r.V := (1 : ℂ)
    have hu : u ≠ 0 := show (1 : ℂ) ≠ 0 from one_ne_zero
    refine ⟨e u, fun h0 => hu (e.toLinearEquiv.injective (h0.trans (map_zero _).symm)), fun g hg => ?_⟩
    change GL (Fin 1) k at g
    have h1 := e.toIntertwiningMap.isIntertwining _ _ g u
    refine h1.symm.trans (congrArg e ?_)
    have h4 : unrChar k (β i) (Matrix.GeneralLinearGroup.det g) = 1 :=
      isUnram_unrChar k (β i) _ (GlobalTheory.StepData.valuation_det_of_mem_KO hg)
    show ((ofChar (detChar (Fin 1) (unrChar k (β i)))) g) (1 : ℂ) = (1 : ℂ)
    simp [detChar_apply, h4]
  choose v hv0 hvK using hv
  obtain ⟨f, hf, hf1⟩ := GlobalTheory.SatInd.exists_fixed_apply_one (stdBlocks (fun i => (uc k (β i)).1) hd)
    (ρ := piTensor fun i => (uc k (β i)).rep) (x := PiTensorProduct.tprod ℂ v) fun g hg => by
      rw [piTensor_tprod]
      congr 1
      funext a
      exact hvK a _ (hg a)
  refine (Submodule.ne_bot_iff _).2 ⟨f, hf, fun h0 => ?_⟩
  have h5 : PiTensorProduct.tprod ℂ v = 0 := by rw [← hf1, h0]; rfl
  have hl : ∀ i, ∃ l : Module.Dual ℂ (uc k (β i)).2.rep.V, l (v i) ≠ 0 := fun i => by
    by_contra! hn
    exact hv0 i ((Module.forall_dual_apply_eq_zero_iff ℂ (v i)).1 hn)
  choose l hl using hl
  let ev : (⨂[ℂ] i, (uc k (β i)).2.rep.V) →ₗ[ℂ] ℂ :=
    PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ (Fin c) ℂ).compLinearMap l)
  have h6 : ev (PiTensorProduct.tprod ℂ v) = ∏ i, l i (v i) := by simp [ev]
  rw [h5, map_zero] at h6
  exact Finset.prod_ne_zero_iff.2 (fun i _ => hl i) h6.symm

theorem isSubquotient_prodIrr_uc {N : ℕ} (α : Fin N → ℂˣ) (hd : ∑ i, (uc k (α i)).1 = N) :
    IsSubquotient (prodIrr (fun i => uc k (α i)) hd) (prinSeries fun i => unrChar k (α i)) := by
  let φ := multiProdEquiv (stdBlocks (fun i => (uc k (α i)).1) hd) fun a =>
    (equivRep (IrrRep.det (Fin 1) (unrChar k (α a)) (isSmoothChar_of_isUnram (isUnram_unrChar k (α a))))).symm
  exact (IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective).trans
    (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries _ _)

end GlobalTheory.GenSph

namespace GlobalTheory.GenSph
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel

end GlobalTheory.GenSph

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatFamOfIsDiscrete
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem exists_satFam_of_isDiscrete : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ), (∀ x : CuspSub E N, ∀ᶠ v in Filter.cofinite, ∃ C, (CG.mk x).HasSat v C) ∧ ∀ (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∃ B, SatFam V B := by
  intro E _ _ _ N
  have hF := GlobalTheory.automorphicFormsFiniteGL
  refine ⟨fun x => UnrSat.eventually_hasSatGL_locRep hF E N x, fun V hV => ?_⟩
  choose σ hσ using GlobalTheory.DiscLocEx.exists_isLocCompGL hF E N V hV
  have h : ∀ w, ∃ B, GlobalTheory.LGrp.IsSpherical (σ w).ρ (GlobalTheory.LFun.KGL w (n := N)) → GlobalTheory.LFun.HasSatGL w (σ w).ρ B := fun w => by
    by_cases hs : GlobalTheory.LGrp.IsSpherical (σ w).ρ (GlobalTheory.LFun.KGL w (n := N))
    · obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible (σ w).smooth (σ w).irred hs
      exact ⟨B, fun _ => hB⟩
    · exact ⟨0, fun h => absurd h hs⟩
  choose B hB using h
  refine ⟨B, fun φ hφ h0 => ?_⟩
  filter_upwards [GlobalTheory.SpehPair.eventually_spherical hV,
    LocSph.eventually_mem ((hV.aut φ hφ).level.mem_nhds (by simp))] with w hw hK
  refine GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup (σ w).irred (hB w (hw _ (hσ w)))
    (fun f : GlobalTheory.LocDual.Maps V w (σ w) => f.1) (fun f => f.2.2) ?_ (GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_) h0
  · rw [GlobalTheory.LocDual.iSup_range_eq V hV.stable hV.irred w (σ w) (hσ w)]
    exact hφ
  · obtain ⟨g, rfl⟩ := hk
    exact hK g

end GlobalTheory.ResW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwSecMulPow
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatTw.TwSec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c}

theorem exists_pow {G₀ : WTZ E} (s : TwSec U x Z G₀) (n : ℕ) :
    ∃ u : TwSec U x Z (n • G₀), u.lo = n • s.lo ∧ u.degLo = n * s.degLo := by
  induction n with
  | zero =>
    obtain ⟨-, -, h2, -, h3⟩ := const_spec (x := x) s.pts (1 : c.F) one_ne_zero
    refine ⟨(const x s.pts 1 one_ne_zero).copy (zero_nsmul G₀).symm, ?_, ?_⟩
    · funext w
      show (const x s.pts 1 one_ne_zero).lo w = _
      rw [h2 w]
      simp [vAdd]
    · show (const x s.pts 1 one_ne_zero).degLo = _
      rw [h3]; simp
  | succ n ih =>
    obtain ⟨u, hl, hd⟩ := ih
    refine ⟨(u.mul s).copy (succ_nsmul G₀ n).symm, ?_, ?_⟩
    · show u.lo + s.lo = _
      rw [hl, succ_nsmul]
    · show (u.mul s).degLo = _
      rw [degLo_mul, hd]; push_cast; ring

end GlobalTheory.FlatTw.TwSec

theorem GlobalTheory.FlatTw.twSec_mul_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c), (∀ (G₀ G₁ : WTZ E) (s : TwSec U x Z G₀) (t : TwSec U x Z G₁), ∃ u : TwSec U x Z (G₀ + G₁), u.sig = s.sig * t.sig ∧ u.cInf = s.cInf * t.cInf ∧ u.lo = s.lo + t.lo ∧ u.degLo = s.degLo + t.degLo) ∧ ∀ (G₀ : WTZ E) (s : TwSec U x Z G₀) (n : ℕ), ∃ u : TwSec U x Z (n • G₀), u.lo = n • s.lo ∧ u.degLo = n * s.degLo := by
  intro E _ _ _ H Dw l Xo c r U x Z
  exact ⟨fun G₀ G₁ s t => ⟨s.mul t, rfl, rfl, rfl, TwSec.degLo_mul s t⟩, fun G₀ s n => s.exists_pow n⟩
end
end

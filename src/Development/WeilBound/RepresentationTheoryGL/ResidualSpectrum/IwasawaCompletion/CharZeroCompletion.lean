module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericUnitaryDualGl
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.ExpBound
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.GenericUnitary.IsGenericOfEquiv
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.GenericUnlinkedGLOfSegRep2
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.LanglandsMultisegmentsOfSeg

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.SpehCosocleUc
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace PositivityTheory.Rg.Rs.C3.UC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}


set_option maxHeartbeats 1000000 in
theorem spehCosocle_uc (hG : PositivityTheory.RgUd.Exp.GenUnitCC) (hSC : GlobalTheory.Published.StandardCosocleGL)
    [CharZero k] (x : GlobalTheory.LocGL.IrrGL (k := k)) (hg : GlobalTheory.LocGL.IsGeneric x.rep)
    (hu : GlobalTheory.SmGL.IsUnitarisable x.rep) (d : ℕ) (hd : ∑ i, (GlobalTheory.LocGL.spehFactor x d i).1 = N) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (τ : Representation ℂ (GL (Fin N) k) W),
      GlobalTheory.LocGL.IsCosocle τ (GlobalTheory.LocGL.prodIrr (GlobalTheory.LocGL.spehFactor x d) hd) := by
  obtain ⟨m, δ, Δ, s, hΔ, hδu, hs, hd0, ⟨φ⟩⟩ := hG k _ _ x.rep x.2.rep.smooth x.2.rep.irr hu hg
  let y : Fin d → Fin m → IrrGL (k := k) := fun i j => ((δ j).nu (s j)).nu (((d : ℂ) - 1) / 2 - (i : ℕ))
  have hN : ∀ i, ∑ j, (y i j).1 = (spehFactor x d i).1 := fun _ => hd0
  let Y : Fin (d * m) → IrrGL (k := k) := fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
  have hM' : ∑ p, (Y p).1 = N := by
    rw [← hd, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Y, Equiv.symm_apply_apply]
    exact hN i
  let e1 : ∀ i : Fin d, (spehFactor x d i).rep.Equiv (prodIrr (y i) (hN i)) := fun i =>
    (x.twEquiv _ (isSmoothChar_absPow _)).symm.trans
      ((twistEquiv φ _).trans (prodIrrTwistEquiv _ hd0 _ (isSmoothChar_absPow _)))
  obtain ⟨e2⟩ := GlobalTheory.T.parabolicInduction_in_stages_product_of_products k d m y (fun i => (spehFactor x d i).1) N hN hd hM'
  let E := (multiProdEquiv _ e1).trans e2
  let Γs : Fin (d * m) → Segment k := fun p =>
    ((Δ (finProdFinEquiv.symm p).2).nu (s (finProdFinEquiv.symm p).2)).nu
      ((((d : ℝ) - 1) / 2 - ((finProdFinEquiv.symm p).1 : ℕ) : ℝ) : ℂ)
  have hcast : ∀ i : ℕ, (((((d : ℝ) - 1) / 2 - i : ℝ)) : ℂ) = ((d : ℂ) - 1) / 2 - (i : ℕ) := fun i => by
    push_cast; ring
  have hL : ∀ p, IsLSeg (Γs p) (Y p).rep := fun p => by
    simp only [Γs, Y, y, hcast]
    exact GlobalTheory.isLSeg_nu (GlobalTheory.isLSeg_nu (hΔ _) _) _
  have hord : ∀ p p' : Fin (d * m), p < p' → ¬ (Γs p).Precedes (Γs p') := by
    intro p p' hpp' hP
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
    obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective p'
    have hii : (i : ℕ) ≤ i' := by
      by_contra hlt
      have h1 : (i' : ℕ) + 1 ≤ i := by omega
      have h2 := Nat.mul_le_mul_left m h1
      have h3 := Fin.lt_def.1 hpp'
      simp only [finProdFinEquiv_apply_val] at h3
      have := j.2
      have := j'.2
      nlinarith
    simp only [Γs, Equiv.symm_apply_apply, GlobalTheory.segment_nu_nu] at hP
    have key := PositivityTheory.RgUd.UOrder.add_one_le_of_precedes_u k (δ j) (δ j') (Δ j) (Δ j') (hΔ j) (hδu j) (hΔ j')
      (hδu j') (s j + (((d : ℝ) - 1) / 2 - (i : ℕ))) (s j' + (((d : ℝ) - 1) / 2 - (i' : ℕ)))
      (by push_cast at hP ⊢; exact hP)
    have hi : ((i : ℕ) : ℝ) ≤ (i' : ℕ) := by exact_mod_cast hii
    have := abs_lt.1 (hs j)
    have := abs_lt.1 (hs j')
    linarith
  have hLF : LFactors (↑((List.range d).flatMap fun i : ℕ =>
      (List.ofFn fun j => (Δ j).nu (s j)).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ))) Y :=
    ⟨Γs, ⟨GlobalTheory.univ_map_speh_segments d m Δ s, hord⟩, hL⟩
  obtain ⟨π, hπ⟩ := hSC k _ (d * m) N Y hM' hLF
  exact ⟨_, _, _, π.ρ, hπ.of_equiv (.refl _) E.symm⟩

end PositivityTheory.Rg.Rs.C3.UC

end
end

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.C3

theorem isSpeh_of_quot {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin N) k) V}
    (hi : ρ.IsIrreducible) (x : GlobalTheory.LocGL.IrrGL (k := k)) (d : ℕ)
    (hd : ∑ i, (GlobalTheory.LocGL.spehFactor x d i).1 = N)
    (hc : ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (τ : Representation ℂ (GL (Fin N) k) W),
      GlobalTheory.LocGL.IsCosocle τ (GlobalTheory.LocGL.prodIrr (GlobalTheory.LocGL.spehFactor x d) hd))
    (f : (GlobalTheory.LocGL.prodIrr (GlobalTheory.LocGL.spehFactor x d) hd).IntertwiningMap ρ) (hf : Function.Surjective f) :
    GlobalTheory.LocGL.IsSpeh x d ρ := by
  obtain ⟨W, _, _, τ, hτ⟩ := hc
  obtain ⟨e⟩ := hτ.equiv_of_surjective hi f hf
  exact ⟨hd, hτ.of_equiv e.symm (.refl _)⟩

theorem charZero_completion {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    CharZero (w.adicCompletion E) :=
  charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective

theorem clause3Asc_of (hL : LocSub) (hD : LocDual) (hG : PositivityTheory.RgUd.Exp.GenUnitCC)
    (hSC : GlobalTheory.Published.StandardCosocleGL) : Clause3Asc := by
  intro E _ _ _ N a d V π hN hV hu hn hasc w σ σ' hσ hσ'
  obtain ⟨hd, f, hf⟩ := hL E N a d V π hN hV hasc w σ σ' hσ hσ'
  obtain ⟨hg, hun⟩ := PositivityTheory.RSHS.LocalComponentGL.generic_unitarisable hu hn hσ
  have hU' : IsUnitarisable σ'.ρ := GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL E N V hV w σ' hσ'
  have := charZero_completion (E := E) w
  obtain ⟨hd', g, hg'⟩ := hD _ N d _ σ' hun hU' hd f hf
  exact isSpeh_of_quot σ'.irred _ d hd' (UC.spehCosocle_uc hG hSC _ hg hun d hd') g hg'

theorem clause3Asc_holds (hL : LocSub) (hD : LocDual) : Clause3Asc :=
  have hZ := PositivityTheory.RgGu.segmentRepresentation
  clause3Asc_of hL hD
    (PositivityTheory.RgUd.Exp.genUnitCCOf (fun k _ _ _ _ => PositivityTheory.RgUd.expBound k) (GlobalTheory.RgGu.genericUnlinkedGL_of_segRep2 hZ))
    (PositivityTheory.Exh.standardCosocleGL_of_seg hZ)

end PositivityTheory.Rg.Rs.C3

end

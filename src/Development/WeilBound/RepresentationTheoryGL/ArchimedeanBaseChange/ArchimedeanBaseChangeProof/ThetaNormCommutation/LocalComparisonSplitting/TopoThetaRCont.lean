module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.TopoThetaRCont
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT

namespace PositivityTheory.Rg.BcB.G8

theorem topo_units {R : Type} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] (n : ℕ) :
    LocallyCompactSpace (GL (Fin n) R) ∧ SecondCountableTopology (GL (Fin n) R) ∧ T2Space (GL (Fin n) R) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  have : T2Space (Matrix (Fin n) (Fin n) R) := inferInstanceAs (T2Space (Fin n → Fin n → R))
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) R)).symm.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) R)).symm.isEmbedding.secondCountableTopology
  have : T2Space (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) R)).symm.isEmbedding.t2Space
  have h := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) R)
  exact ⟨h.locallyCompactSpace, h.isEmbedding.secondCountableTopology, h.isEmbedding.t2Space⟩

theorem topo_thetaR_cont {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (c : R →+* R)
    (hc : Continuous c) (n : ℕ) : Continuous (thetaR c n) := by
  rw [Units.continuous_iff]
  exact ⟨(Units.continuous_coe_inv.matrix_map hc).matrix_transpose,
    (Units.continuous_val.matrix_map hc).matrix_transpose⟩

theorem topo_countable (E : Type) [Field E] [NumberField E] (n : ℕ) : Countable (GL (Fin n) E) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  exact Function.Injective.countable (f := fun u : GL (Fin n) E => (u : Matrix (Fin n) (Fin n) E))
    fun _ _ h => Units.ext h

theorem topo_thF_cont (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Continuous (thF E n) := by
  have h : ∀ g, thF E n g = PhiU n (Af E) * thetaR (conjFin (IsCMField.complexConj E).toRingEquiv) n g *
      (PhiU n (Af E))⁻¹ := fun g => thetaGL_eq n (Af E) _ g
  rw [show (thF E n : GL (Fin n) (Af E) → GL (Fin n) (Af E)) = _ from funext h]
  exact (continuous_const.mul (topo_thetaR_cont _ (continuous_conjFin _) n)).mul continuous_const

theorem topo_holds : Topo := by
  intro E _ _ _ n
  have := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  have := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  obtain ⟨hc, hs, -⟩ := topo_units (R := ℂ) n
  exact ⟨topo_units n, topo_units n, ⟨hc, hs⟩, topo_countable E n, topo_thF_cont E n,
    topo_thetaR_cont _ Complex.continuous_conj n⟩

end PositivityTheory.Rg.BcB.G8

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PTranslAd
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8

theorem translad_map_PhiU (n : ℕ) {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) :
    GeneralLinearGroup.map p (PhiU n R) = PhiU n S := by
  apply Units.ext
  ext i j
  change p ((PhiU n R).val i j) = (PhiU n S).val i j
  rw [phiU_val, phiU_val]
  simp only [GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem translad_thetaR_thetaR {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (n : ℕ)
    (g : GL (Fin n) A) : thetaR σ n (thetaR σ n g) = g := by
  apply Units.ext
  rw [thetaR_val, ← map_inv (thetaR σ n) g, thetaR_val, inv_inv]
  ext i j
  simp [Matrix.map_apply, Matrix.transpose_apply, hσ]

theorem translad_central (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (u : GL (Fin n) E)
    (hu : IsTransl u) : u⁻¹ * PhiU n E ∈ Subgroup.center (GL (Fin n) E) := by
  have hcc : ∀ x, conjE E (conjE E x) = x := fun x => IsCMField.complexConj_apply_apply (K := E) x
  refine Subgroup.mem_center_iff.mpr fun h => ?_
  have h2 : thetaE E n (thetaE E n h) = h := translad_thetaR_thetaR (conjE E) hcc n h
  have h1 := hu.1 (thetaE E n h)
  rw [h2] at h1
  have h3 : thE E n (thetaE E n h) = PhiU n E * h * (PhiU n E)⁻¹ := by
    rw [show thE E n (thetaE E n h) = thetaGL n (conjE E) (thetaE E n h) from rfl, thetaGL_eq]
    exact congrArg (fun x => PhiU n E * x * (PhiU n E)⁻¹) h2
  rw [h3] at h1
  calc h * (u⁻¹ * PhiU n E) = u⁻¹ * (u * h * u⁻¹) * PhiU n E := by group
    _ = u⁻¹ * (PhiU n E * h * (PhiU n E)⁻¹) * PhiU n E := by rw [h1]
    _ = u⁻¹ * PhiU n E * h := by group

theorem translAd_holds : TranslAd := by
  intro E _ _ _ n u hu g
  have hz := GeneralLinearGroup.map_center_le (algebraMap E (Ad E)) (translad_central E n u hu)
  rw [Subgroup.mem_comap, map_mul, map_inv, translad_map_PhiU] at hz
  have hr : ratGL E n u = GeneralLinearGroup.map (algebraMap E (Ad E)) u := rfl
  rw [hr, thetaGL_eq]
  change PhiU n (Ad E) * thetaR (conjAd E) n g * (PhiU n (Ad E))⁻¹ =
    GeneralLinearGroup.map (algebraMap E (Ad E)) u * thetaR (conjAd E) n g *
      (GeneralLinearGroup.map (algebraMap E (Ad E)) u)⁻¹
  have hcomm := Subgroup.mem_center_iff.mp hz (thetaR (conjAd E) n g)
  generalize thetaR (conjAd E) n g = T at hcomm ⊢
  generalize GeneralLinearGroup.map (algebraMap E (Ad E)) u = U at hcomm ⊢
  generalize PhiU n (Ad E) = P at hcomm ⊢
  calc P * T * P⁻¹ = U * ((U⁻¹ * P) * T) * (U⁻¹ * P)⁻¹ * U⁻¹ := by group
    _ = U * (T * (U⁻¹ * P)) * (U⁻¹ * P)⁻¹ * U⁻¹ := by rw [hcomm]
    _ = U * T * U⁻¹ := by group

end PositivityTheory.Rg.BcB.G8

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PAdelEqOf
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT

namespace PositivityTheory.Rg.BcB.G8

open PositivityTheory.Rg.Tf.Loc (twConj)

theorem adeleqof_map_Phi {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m : ℕ) :
    (GlobalTheory.Tw.Phi m R).map f = GlobalTheory.Tw.Phi m S := by
  ext i j
  simp only [GlobalTheory.Tw.Phi, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem adeleqof_map_PhiU {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m : ℕ) :
    GeneralLinearGroup.map f (PhiU m R) = PhiU m S := by
  apply Units.ext
  show (PhiU m R).val.map f = (PhiU m S).val
  rw [phiU_val, phiU_val]
  exact adeleqof_map_Phi f m

theorem adeleqof_map_thetaR {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (σ : R →+* R) (τ : S →+* S)
    (hf : ∀ y, f (σ y) = τ (f y)) (m : ℕ) (g : GL (Fin m) R) :
    GeneralLinearGroup.map f (thetaR σ m g) = thetaR τ m (GeneralLinearGroup.map f g) := by
  apply Units.ext
  show (thetaR σ m g).val.map f = (thetaR τ m (GeneralLinearGroup.map f g)).val
  rw [thetaR_val, thetaR_val, ← map_inv]
  ext i j
  exact hf _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem adeleqof_pFin_conj (y : Ad E) :
    pFin E (conjAd E y) = conjFin (IsCMField.complexConj E).toRingEquiv (pFin E y) := rfl

theorem adeleqof_pFin_thetaGL (g : GA E n) :
    GeneralLinearGroup.map (pFin E) (thetaGL n (conjAd E) g) = thF E n (GeneralLinearGroup.map (pFin E) g) := by
  rw [thF, thetaGL_eq, thetaGL_eq, map_mul, map_mul, map_inv, adeleqof_map_PhiU,
    adeleqof_map_thetaR (pFin E) (conjAd E) _ adeleqof_pFin_conj]

omit [IsCMField E] in
theorem adeleqof_pFin_ratGL (d : GL (Fin n) E) : GeneralLinearGroup.map (pFin E) (ratGL E n d) = ratF E n d := by
  ext i j
  rfl

omit [IsCMField E] in
theorem adeleqof_map_cW (w : Pl E) (g : GA E n) :
    GeneralLinearGroup.map (cW w) g = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := rfl

theorem adeleqof_twist (hT : TranslAd) {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) (g : GA E n) :
    twConj (thetaA E n) g (ratGL E n d) * (ratGL E n u)⁻¹ = g⁻¹ * ratGL E n (d * u⁻¹) * thetaGL n (conjAd E) g := by
  rw [hT E n u hu g, twConj, map_mul, map_inv]
  group

theorem adeleqof_cpt (hT : TranslAd) {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) (g : GA E n) (w : Pl E) :
    cpt w u (twConj (thetaA E n) g (ratGL E n d)) = GeneralLinearGroup.map (pLoc E w)
      ((GeneralLinearGroup.map (pFin E) g)⁻¹ * ratF E n (d * u⁻¹) * thF E n (GeneralLinearGroup.map (pFin E) g)) := by
  rw [cpt, adeleqof_map_cW, adeleqof_twist hT hu]
  simp only [map_mul, map_inv, adeleqof_pFin_thetaGL, adeleqof_pFin_ratGL]

end PositivityTheory.Rg.BcB.G8

end
end

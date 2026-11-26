module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasModelOfSpreading
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinUnfoldingSecondTerm

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LPartFTE
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LPartFTD
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LPartFTC
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LPartFTB
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LPartFTA
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.ThetaPoisson GlobalTheory.CompanionTheory.ThetaInv GlobalTheory.CompanionTheory.EisCovar

namespace PositivityTheory.Rg.Rsw.L.LPartFT

def SetW (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D)
    (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) : Prop :=
  IsCharAF D.host.F ψ ∧ IsHeckeChar D χ ∧ IsInfFam θ ∧ (∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕) ∧ IsWeilSch ψ χ θ V μ ω

theorem theta_levi_w {D : D7} {n : ℕ} {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω)
    (g : G D n) (a : GL (Fin n) D.host.E) (hg : mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))))
    (Φ : schwartzA θ V.rank n) :
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  obtain ⟨-, hχ, -, -, hω⟩ := hS
  let a' : GL (Fin n) (AE D) := Matrix.GeneralLinearGroup.map (incA D) a
  have hdet : Matrix.GeneralLinearGroup.det a' =
      Units.map (incA D).toMonoidHom (Matrix.GeneralLinearGroup.det a) := by
    apply Units.ext
    simp [a', Matrix.GeneralLinearGroup.map]
    exact (RingHom.map_det _ _).symm
  have h1 : absA D (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]; exact absE_inclR _
  have h2 : χ (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]; exact hχ.2 _
  have hinv : (a'⁻¹).1 = (a⁻¹).1.map (incA D) := by
    show ((Matrix.GeneralLinearGroup.map (incA D) a)⁻¹).1 = _
    rw [← map_inv]; rfl
  have hg' : mat g = blk4 a'.1 0 0 (adj (a'⁻¹).1) := by
    rw [hinv]; exact hg
  have hm : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      (ω g Φ).1 (ξ.map (incA D)) = Φ.1 ((ξ * a.1).map (incA D)) := by
    intro ξ
    rw [hω.levi g a' hg' Φ, h1, h2]
    have e : (HMul.hMul (ξ.map (incA D)) a'.1 : Mx D V.rank n) = (ξ * a.1).map (incA D) := by
      rw [Matrix.map_mul]; rfl
    rw [e]
    simp [npow]
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    { toFun := fun ξ => ξ * a.1
      invFun := fun ξ => ξ * (a⁻¹).1
      left_inv := fun ξ => by
        show ξ * a.1 * (a⁻¹).1 = ξ
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      right_inv := fun ξ => by
        show ξ * (a⁻¹).1 * a.1 = ξ
        rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one] }
  simp_rw [hm]
  exact e.tsum_eq (fun ξ => Φ.1 (ξ.map (incA D)))

theorem theta_unip_w {D : D7} {n : ℕ} {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω)
    (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E) (hg : mat g = blk4 1 (b.map (incA D)) 0 1)
    (Φ : schwartzA θ V.rank n) :
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  refine tsum_congr fun ξ => ?_
  rw [hS.2.2.2.2.unip g (b.map (incA D)) hg Φ (ξ.map (incA D)), psi_unip_rat hS.1, one_mul]

theorem theta_weyl_w {D : D7} {n : ℕ} {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω)
    (g : G D n) (hg : mat g = blk4 0 1 (-1) 0) (Φ : schwartzA θ V.rank n) :
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  obtain ⟨hψ, -, hθ, ⟨𝓕, hμ⟩, hω⟩ := hS
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D V.rank n
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have hT := isHermND_gram V
  obtain ⟨h1, h2⟩ := GlobalTheory.T.rationalAdelicMatrices_self_annihilator D V.rank n V.gram hT ψ hψ
  have hs := pairing_symm (n := n) hT ψ
  have hval : ∀ x, (ω g Φ).1 x = ∫ y, Φ.1 y * GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing V.gram ψ y x ∂μ := fun x => by
    rw [hω.weyl g hg Φ x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [hs y x]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing, GlobalTheory.SiegelWeilLitCompare.gramQ_eq]
    rfl
  haveI := hμ.1
  have key := poisson_translates (ratMx D V.rank n) K hK hKc (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing (n := n) V.gram ψ)
    (fun y => ?_) hs (fun x x' y => ?_) (fun x y => hψ.2.1 _) h1 h2 μ 𝓕 hμ.2.1 hμ.2.2 (f := Φ.1) ?_
    (translates_bound hθ Φ) ?_
  · simp only [← hval] at key
    rw [tsum_ratMx, tsum_ratMx (fun x => (ω g Φ).1 x)] at key
    exact key.symm
  · simp only [hs _ y]
    haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    have ht : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA (D := D)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
    exact hψ.1.comp (ht.comp (continuous_const.matrix_mul continuous_id).matrix_trace)
  · simp only [hs _ y]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.trA GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.gramQ GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.mmul
    rw [Matrix.mul_add, Matrix.trace_add, map_add (f := _), AddChar.map_add_eq_mul]
  · exact (GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ _ n Φ.1
      (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ _ n Φ.1 Φ.2)).1
  · simp only [← hval]
    exact (ratEquiv D V.rank n).summable_iff.1 (GlobalTheory.SiegelWeilLitCompare.summable_rat hθ (ω g Φ))

theorem thetaInv_w {D : D7} {n : ℕ} {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω)
    (Φ : schwartzA θ V.rank n) (γ : G D n) (hγ : γ ∈ GF D n) :
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω γ Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  let S : Subgroup (G D n) :=
    { carrier := {γ | ∀ Φ : schwartzA θ V.rank n,
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω γ Φ).1 (ξ.map (incA D)) =
          ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D))}
      one_mem' := fun Φ => by simp
      mul_mem' := fun {g h} hg hh Φ => by
        rw [map_mul, Module.End.mul_apply]
        exact (hg _).trans (hh Φ)
      inv_mem' := fun {g} hg Φ => by
        have := hg (ω g⁻¹ Φ)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
        exact this.symm }
  have hle : GF D n ≤ S := GlobalTheory.T.rational_group_le_of_generators_mem D n S (fun g a hg Φ => theta_levi_w hS g a hg Φ)
    (fun g b hg Φ => theta_unip_w hS g b hg Φ) (fun g hg Φ => theta_weyl_w hS g hg Φ)
  exact hle hγ Φ

theorem covar_w {D : D7} {n : ℕ} {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω)
    (γ : G D n) (hγ : γ ∈ GF D n) (v : Mx D V.rank (n + n)) (Φ Ψ : schwartzA θ V.rank n) (hΨ : Ψ.1 = Heisenberg₂ ψ V v Φ.1) :
    (ω γ Ψ).1 = Heisenberg₂ ψ V (HMul.hMul v (mat γ⁻¹)) (ω γ Φ).1 := by
  obtain ⟨-, -, -, ⟨𝓕, hC⟩, hW⟩ := hS
  have hF : FieldGen D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) n :=
    FieldGenPf.fieldGen_of_bruhat GlobalTheory.CompanionTheory.BruhatCell.bruhat D.host.E _ (fun x => star_star x) two_ne_zero n
  exact Transfer.ratPts_transfer GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn D n hF (CovAt ψ V ω) (fun _ _ h₁ h₂ => covAt_mul h₁ h₂)
    (fun g a h => covAt_levi D n V ψ χ θ μ ω hW g a h)
    (fun g b hb h => covAt_unip D n V ψ χ θ μ ω hW g b hb h)
    (fun g h => covAt_weyl D n V ψ χ θ μ ω hW hC.1 g h) γ hγ v Φ Ψ hΨ

theorem partial_fourier_second_term {D : D7} {n : ℕ} {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω)
    (Φ : schwartzA θ V.rank n) (r : ℕ) (hr : r ≤ n) (μr : Measure (Mx D V.rank r))
    (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕)
    (c : Matrix (Fin r) (Fin n) D.host.E) (a : Matrix (Fin n) (Fin n) D.host.E) (hc : IsCompl c a)
    (b : HermE D r) (γ : G D n) (hγ : γ ∈ GF D n)
    (hmat : mat γ = (repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b.1 a).map (incA D)) :
    (ω γ Φ).1 0 = J ψ V μr (pull c Φ.1) b := by
  obtain ⟨hψ, -, hθ, ⟨𝓕, hcov⟩, -⟩ := id hS
  have hinv : mat γ * mat γ⁻¹ = 1 := mat_mul_inv' γ
  rw [GlobalTheory.T.eisenstein_vanishing D ψ hψ θ hθ V n μ 𝓕 hcov (ω γ Φ).1 (ω γ Φ).2,
    ← GlobalTheory.T.eisenstein_unfolding_second_term D ψ hψ θ hθ V n r hr μ 𝓕 hcov μr hμr c a hc b Φ.1 Φ.2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [← hmat]
  have hΨ := GlobalTheory.T.eisenstein_heisenberg_schwartz D ψ hψ θ hθ V n (HMul.hMul (zy y) (mat γ)) Φ.1 Φ.2
  have h1 := covar_w hS γ hγ (HMul.hMul (zy y) (mat γ)) Φ
    ⟨Heisenberg₂ ψ V (HMul.hMul (zy y) (mat γ)) Φ.1, hΨ⟩ rfl
  have h2 := thetaInv_w hS ⟨Heisenberg₂ ψ V (HMul.hMul (zy y) (mat γ)) Φ.1, hΨ⟩ γ hγ
  have hv : HMul.hMul (HMul.hMul (zy y) (mat γ)) (mat γ⁻¹) = zy y := by
    rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
  rw [hv] at h1
  rw [h1] at h2
  exact h2

end PositivityTheory.Rg.Rsw.L.LPartFT
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar

namespace PositivityTheory.Rg.Rsw.L.LPartFT

variable {n r t : ℕ}

abbrev ee (hn : r + t = n) : Fin r ⊕ Fin t ≃ Fin n := finSumFinEquiv.trans (finCongr hn)

abbrev ff (hn : r + t = n) : Fin t ⊕ Fin r ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))

theorem ee_inl_val (hn : r + t = n) (k : Fin r) : (ee hn (Sum.inl k) : ℕ) = k := by simp [ee]
theorem ee_inr_val (hn : r + t = n) (k : Fin t) : (ee hn (Sum.inr k) : ℕ) = r + k := by simp [ee]
theorem ff_inl_val (hn : r + t = n) (k : Fin t) : (ff hn (Sum.inl k) : ℕ) = k := by simp [ff]
theorem ff_inr_val (hn : r + t = n) (k : Fin r) : (ff hn (Sum.inr k) : ℕ) = t + k := by simp [ff]

theorem ext_ee (hn : r + t = n) {R : Type} {M N : Matrix (Fin n) (Fin n) R}
    (h : ∀ s s', M (ee hn s) (ee hn s') = N (ee hn s) (ee hn s')) : M = N := by
  ext i j
  simpa using h ((ee hn).symm i) ((ee hn).symm j)

theorem bl_ee {R : Type} (hn : r + t = n) (a : Matrix (Fin r) (Fin r) R) (b : Matrix (Fin r) (Fin t) R)
    (c : Matrix (Fin t) (Fin r) R) (d : Matrix (Fin t) (Fin t) R) (s s' : Fin r ⊕ Fin t) :
    bl hn a b c d (ee hn s) (ee hn s') = Matrix.fromBlocks a b c d s s' := by
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem blockRowSubstitution_one {R : Type} [CommRing R] (hn : r + t = n) : bl hn (1 : Matrix (Fin r) (Fin r) R) 0 0 1 = 1 := by
  refine ext_ee hn fun s s' => ?_
  rw [bl_ee, Matrix.fromBlocks_one, Matrix.one_apply, Matrix.one_apply]
  simp only [(ee hn).injective.eq_iff]

theorem bl_add {R : Type} [CommRing R] (hn : r + t = n) (a a' : Matrix (Fin r) (Fin r) R) (b b' : Matrix (Fin r) (Fin t) R)
    (c c' : Matrix (Fin t) (Fin r) R) (d d' : Matrix (Fin t) (Fin t) R) :
    bl hn a b c d + bl hn a' b' c' d' = bl hn (a + a') (b + b') (c + c') (d + d') := by
  refine ext_ee hn fun s s' => ?_
  rw [Matrix.add_apply, bl_ee, bl_ee, bl_ee, ← Matrix.add_apply, Matrix.fromBlocks_add]

theorem block_neg {R : Type} [CommRing R] (hn : r + t = n) (a : Matrix (Fin r) (Fin r) R) (b : Matrix (Fin r) (Fin t) R)
    (c : Matrix (Fin t) (Fin r) R) (d : Matrix (Fin t) (Fin t) R) :
    -bl hn a b c d = bl hn (-a) (-b) (-c) (-d) := by
  refine ext_ee hn fun s s' => ?_
  rw [Matrix.neg_apply, bl_ee, bl_ee, ← Matrix.neg_apply, Matrix.fromBlocks_neg]

theorem block_map {R S : Type} (hn : r + t = n) (a : Matrix (Fin r) (Fin r) R) (b : Matrix (Fin r) (Fin t) R)
    (c : Matrix (Fin t) (Fin r) R) (d : Matrix (Fin t) (Fin t) R) (f : R → S) :
    (bl hn a b c d).map f = bl hn (a.map f) (b.map f) (c.map f) (d.map f) := by
  simp only [bl, ← Matrix.submatrix_map, Matrix.fromBlocks_map]

theorem one_sub_bl {R : Type} [CommRing R] (hn : r + t = n) :
    1 - bl hn (0 : Matrix (Fin r) (Fin r) R) 0 0 1 = bl hn 1 0 0 0 := by
  rw [← blockRowSubstitution_one hn, sub_eq_iff_eq_add, bl_add]; simp

theorem eId_eq {K : Type} [Field K] (hn : r + t = n) : eId K n r = bl hn 1 0 0 0 := by
  refine ext_ee hn fun s s' => ?_
  rw [bl_ee, eId, Matrix.diagonal_apply]
  simp only [(ee hn).injective.eq_iff]
  rcases s with k | k <;> rcases s' with k' | k' <;>
    simp [Matrix.one_apply, ee_inl_val, ee_inr_val]

theorem cT_blk4 {K : Type} [Field K] (σ : K →+* K) (A B C E : Matrix (Fin n) (Fin n) K) :
    cT σ (blk4 A B C E) = blk4 (cT σ A) (cT σ C) (cT σ B) (cT σ E) := by
  simp only [cT, blk4, ← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.transpose_submatrix,
    Matrix.fromBlocks_transpose]

def wE {K : Type} [Field K] (e : Matrix (Fin n) (Fin n) K) : Matrix (Fin (n + n)) (Fin (n + n)) K := blk4 (1 - e) e (-e) (1 - e)

theorem cT_one {K : Type} [Field K] (σ : K →+* K) : cT σ (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  simp [cT]

theorem cT_sub {K : Type} [Field K] (σ : K →+* K) (A B : Matrix (Fin n) (Fin n) K) : cT σ (A - B) = cT σ A - cT σ B := by
  have h : (A - B).map σ = A.map σ - B.map σ := by ext; simp
  rw [cT, cT, cT, h, Matrix.transpose_sub]

theorem cT_neg {K : Type} [Field K] (σ : K →+* K) (A : Matrix (Fin n) (Fin n) K) : cT σ (-A) = -cT σ A := by
  have h : (-A).map σ = -A.map σ := by ext; simp
  rw [cT, cT, h, Matrix.transpose_neg]

theorem block_matrix_map {R S : Type} (A B C E : Matrix (Fin n) (Fin n) R) (f : R → S) :
    (blk4 A B C E).map f = blk4 (A.map f) (B.map f) (C.map f) (E.map f) := by
  simp only [blk4, ← Matrix.submatrix_map, Matrix.fromBlocks_map]

theorem wE_unit {K : Type} [Field K] (σ : K →+* K) (e : Matrix (Fin n) (Fin n) K) (he : e * e = e) (hσ : cT σ e = e) :
    IsUnit (wE e).det ∧ IsUnitary σ (PositivityTheory.GramSchwartzFunctions.EC.Jm K n) (wE e) := by
  have h1 : e * (1 - e) = 0 := by rw [Matrix.mul_sub, he, Matrix.mul_one, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [Matrix.sub_mul, he, Matrix.one_mul, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_zero]
  constructor
  · refine Matrix.isUnit_det_of_right_inverse (B := blk4 (1 - e) (-e) e (1 - e)) ?_
    rw [wE, submatrix_fromBlocks_mul, ← block_matrix_one]
    congr 1 <;> (simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, h1, h2, h3, he, neg_zero, add_zero, zero_add,
      sub_add_cancel, neg_add_cancel]; try abel)
  · unfold IsUnitary
    rw [wE, cT_blk4, cT_sub, cT_one, hσ, cT_neg, hσ, PositivityTheory.GramSchwartzFunctions.EC.Jm, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
    congr 1 <;> (simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, h1, h2, h3, he, neg_zero, add_zero, zero_add,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, sub_add_cancel, neg_add_cancel]; try abel)

def πe (hn : r + t = n) : Equiv.Perm (Fin n) := (ff hn).symm.trans ((Equiv.sumComm _ _).trans (ee hn))

theorem πe_ff_inl (hn : r + t = n) (k : Fin t) : πe hn (ff hn (Sum.inl k)) = ee hn (Sum.inr k) := by
  rw [πe, Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply]; rfl

theorem πe_symm_ee_inl (hn : r + t = n) (k : Fin r) : (πe hn).symm (ee hn (Sum.inl k)) = ff hn (Sum.inr k) := by
  rw [Equiv.symm_apply_eq, πe, Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply]; rfl

theorem πe_symm_ee_inr (hn : r + t = n) (k : Fin t) : (πe hn).symm (ee hn (Sum.inr k)) = ff hn (Sum.inl k) := by
  rw [Equiv.symm_apply_eq, πe_ff_inl]

def Pm (K : Type) [Field K] (hn : r + t = n) : Matrix (Fin n) (Fin n) K := (1 : Matrix (Fin n) (Fin n) K).submatrix (πe hn) id

theorem permutation_matrix_transpose {K : Type} [Field K] (hn : r + t = n) : (Pm K hn)ᵀ = (1 : Matrix (Fin n) (Fin n) K).submatrix id (πe hn) := by
  simp [Pm, Matrix.transpose_submatrix]

theorem Pm_mul_alt {K : Type} [Field K] (hn : r + t = n) : Pm K hn * (Pm K hn)ᵀ = 1 := by
  rw [permutation_matrix_transpose, Pm]
  have := Matrix.submatrix_mul_equiv (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (πe hn) (Equiv.refl _) (πe hn)
  simpa using this

theorem T_mul_Pm {K : Type} [Field K] (hn : r + t = n) : (Pm K hn)ᵀ * Pm K hn = 1 := by
  rw [permutation_matrix_transpose, Pm]
  have := Matrix.submatrix_mul_equiv (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) id (πe hn) id
  simpa using this

theorem conj_Pm {K : Type} [Field K] (hn : r + t = n) (M : Matrix (Fin n) (Fin n) K) :
    (Pm K hn)ᵀ * M * Pm K hn = M.submatrix (πe hn).symm (πe hn).symm := by
  have e1 : M = (M.submatrix (πe hn).symm id).submatrix (πe hn) id := by ext; simp
  have e2 : M.submatrix (πe hn).symm id = (M.submatrix (πe hn).symm (πe hn).symm).submatrix id (πe hn) := by ext; simp
  rw [permutation_matrix_transpose, Pm]
  nth_rewrite 1 [e1]
  rw [Matrix.submatrix_mul_equiv (1 : Matrix (Fin n) (Fin n) K) _ id (πe hn) id, Matrix.one_mul, Matrix.submatrix_id_id, e2,
    Matrix.submatrix_mul_equiv _ (1 : Matrix (Fin n) (Fin n) K) id (πe hn) id, Matrix.mul_one, Matrix.submatrix_id_id]

theorem eId_conj {K : Type} [Field K] (hn : r + t = n) :
    (Pm K hn)ᵀ * eId K n t * Pm K hn = bl hn 0 0 0 1 := by
  rw [conj_Pm]
  refine ext_ee hn fun s s' => ?_
  rcases s with k | k <;> rcases s' with k' | k' <;>
    simp only [bl_ee, Matrix.submatrix_apply, πe_symm_ee_inl, πe_symm_ee_inr] <;>
    rw [eId, Matrix.diagonal_apply] <;>
    simp [(ff hn).injective.eq_iff, ff_inl_val, ff_inr_val, Matrix.one_apply] <;> simp [Fin.ext_iff] <;> omega

end PositivityTheory.Rg.Rsw.L.LPartFT
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar

namespace PositivityTheory.Rg.Rsw.L.LPartFT

variable {n r t : ℕ}

theorem block_mul₂ {R : Type} [CommRing R] (hn : r + t = n) (a a' : Matrix (Fin r) (Fin r) R) (b b' : Matrix (Fin r) (Fin t) R)
    (c c' : Matrix (Fin t) (Fin r) R) (d d' : Matrix (Fin t) (Fin t) R) :
    bl hn a b c d * bl hn a' b' c' d' = bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [PositivityTheory.Rg.Rsw.bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem cT_bl {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) (a : Matrix (Fin r) (Fin r) K) (b : Matrix (Fin r) (Fin t) K)
    (c : Matrix (Fin t) (Fin r) K) (d : Matrix (Fin t) (Fin t) K) :
    cT σ (bl hn a b c d) = bl hn (cT σ a) (cT σ c) (cT σ b) (cT σ d) := by
  unfold PositivityTheory.GramSchwartzFunctions.EC.cT
  rw [block_map]
  simp only [PositivityTheory.Rg.Rsw.bl, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]

theorem cT_zero {K : Type} [Field K] (σ : K →+* K) {a b : ℕ} : cT σ (0 : Matrix (Fin a) (Fin b) K) = 0 := by
  simp [cT]

theorem first_block_hermitian_idempotent {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) :
    bl hn (1 : Matrix (Fin r) (Fin r) K) 0 0 0 * bl hn 1 0 0 0 = bl hn 1 0 0 0 ∧
      cT σ (bl hn (1 : Matrix (Fin r) (Fin r) K) 0 0 0) = bl hn 1 0 0 0 := by
  refine ⟨?_, ?_⟩
  · rw [block_mul₂]
    simp
  · simp only [cT_bl, cT_one, cT_zero]

theorem second_block_hermitian_idempotent {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) :
    bl hn (0 : Matrix (Fin r) (Fin r) K) 0 0 1 * bl hn 0 0 0 1 = bl hn 0 0 0 1 ∧
      cT σ (bl hn (0 : Matrix (Fin r) (Fin r) K) 0 0 1) = bl hn 0 0 0 1 := by
  refine ⟨?_, ?_⟩
  · rw [block_mul₂]
    simp
  · simp only [cT_bl, cT_one, cT_zero]

theorem Pm_map {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) : (Pm K hn).map σ = Pm K hn := by
  rw [Pm, ← Matrix.submatrix_map, Matrix.map_one _ (map_zero σ) (map_one σ)]

theorem cT_Pm {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) : cT σ (Pm K hn) = (Pm K hn)ᵀ := by
  rw [cT, Pm_map]

theorem cT_PmT {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) : cT σ (Pm K hn)ᵀ = Pm K hn := by
  rw [cT, Matrix.transpose_map, Pm_map, Matrix.transpose_transpose]

theorem repMat_zero {K : Type} [Field K] (σ : K →+* K) {p : ℕ} (a : Matrix (Fin n) (Fin n) K) :
    repMat σ (0 : Matrix (Fin p) (Fin p) K) a = wr K n p * mA σ a := by
  have h0 : (PositivityTheory.GramSchwartzFunctions.EC.extB (n := n) (0 : Matrix (Fin p) (Fin p) K)) = 0 := by
    ext i j
    simp [PositivityTheory.GramSchwartzFunctions.EC.extB]
  simp only [PositivityTheory.GramSchwartzFunctions.EC.repMat, h0, PositivityTheory.GramSchwartzFunctions.EC.nB, GlobalTheory.CompanionTheory.EisCovar.block_matrix_one, Matrix.mul_one]

theorem mA_one {K : Type} [Field K] (σ : K →+* K) : mA σ (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  simp only [PositivityTheory.GramSchwartzFunctions.EC.mA, cT_one, inv_one, GlobalTheory.CompanionTheory.EisCovar.block_matrix_one]

theorem mA_Pm {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) : mA σ (Pm K hn) = blk4 (Pm K hn) 0 0 (Pm K hn) := by
  simp only [PositivityTheory.GramSchwartzFunctions.EC.mA, cT_Pm, Matrix.inv_eq_left_inv (Pm_mul_alt (K := K) hn)]

theorem key3 {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) :
    blk4 (Pm K hn)ᵀ 0 0 (Pm K hn)ᵀ * repMat σ (0 : Matrix (Fin t) (Fin t) K) (Pm K hn) = wE (bl hn 0 0 0 1) := by
  have hc := eId_conj (K := K) hn
  have h1 : (Pm K hn)ᵀ * (1 - PositivityTheory.GramSchwartzFunctions.EC.eId K n t) * Pm K hn = 1 - bl hn 0 0 0 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, T_mul_Pm, hc]
  have h2 : (Pm K hn)ᵀ * (-PositivityTheory.GramSchwartzFunctions.EC.eId K n t) * Pm K hn = -bl hn 0 0 0 1 := by
    rw [Matrix.mul_neg, Matrix.neg_mul, hc]
  rw [repMat_zero, mA_Pm, ← Matrix.mul_assoc]
  simp only [PositivityTheory.GramSchwartzFunctions.EC.wr, GlobalTheory.CompanionTheory.EisCovar.submatrix_fromBlocks_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [h1, h2, hc]
  rfl

theorem gQ_unit {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) :
    IsUnit (blk4 (Pm K hn)ᵀ 0 0 (Pm K hn)ᵀ).det ∧ IsUnitary σ (PositivityTheory.GramSchwartzFunctions.EC.Jm K n) (blk4 (Pm K hn)ᵀ 0 0 (Pm K hn)ᵀ) := by
  have hinv : blk4 (Pm K hn)ᵀ 0 0 (Pm K hn)ᵀ * blk4 (Pm K hn) 0 0 (Pm K hn) = 1 := by
    rw [GlobalTheory.CompanionTheory.EisCovar.submatrix_fromBlocks_mul]
    simp only [T_mul_Pm, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, GlobalTheory.CompanionTheory.EisCovar.block_matrix_one]
  refine ⟨Matrix.isUnit_det_of_right_inverse hinv, ?_⟩
  unfold PositivityTheory.GramSchwartzFunctions.EC.IsUnitary PositivityTheory.GramSchwartzFunctions.EC.Jm
  rw [cT_blk4, cT_PmT, cT_zero]
  simp only [GlobalTheory.CompanionTheory.EisCovar.submatrix_fromBlocks_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.mul_neg, Matrix.neg_mul, Pm_mul_alt, Matrix.one_mul, neg_zero]

theorem wr_unit {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) :
    IsUnit (wr K n r).det ∧ IsUnitary σ (PositivityTheory.GramSchwartzFunctions.EC.Jm K n) (wr K n r) := by
  have h : PositivityTheory.GramSchwartzFunctions.EC.wr K n r = wE (bl hn (1 : Matrix (Fin r) (Fin r) K) 0 0 0) := by
    rw [← eId_eq hn]
    rfl
  rw [h]
  exact wE_unit σ _ (first_block_hermitian_idempotent σ hn).1 (first_block_hermitian_idempotent σ hn).2

theorem second_block_weyl_unitary {K : Type} [Field K] (σ : K →+* K) (hn : r + t = n) :
    IsUnit (wE (bl hn (0 : Matrix (Fin r) (Fin r) K) 0 0 1)).det ∧
      IsUnitary σ (PositivityTheory.GramSchwartzFunctions.EC.Jm K n) (wE (bl hn (0 : Matrix (Fin r) (Fin r) K) 0 0 1)) :=
  wE_unit σ _ (second_block_hermitian_idempotent σ hn).1 (second_block_hermitian_idempotent σ hn).2

end PositivityTheory.Rg.Rsw.L.LPartFT
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar

namespace PositivityTheory.Rg.Rsw.L.LPartFT

variable {D : D7} {n r t a : ℕ}

def c₁ (D : D7) (hn : r + t = n) : Matrix (Fin r) (Fin n) D.host.E :=
  (1 : Matrix (Fin n) (Fin n) D.host.E).submatrix (fun k => ee hn (Sum.inl k)) id

def c₃ (D : D7) (hn : r + t = n) : Matrix (Fin t) (Fin n) D.host.E :=
  (1 : Matrix (Fin n) (Fin n) D.host.E).submatrix (fun k => ee hn (Sum.inr k)) id

theorem jn_ee (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) (i : Fin a) (s : Fin r ⊕ Fin t) :
    jn hn x v i (ee hn s) = Matrix.fromCols x v i s := by
  simp only [jn, Matrix.submatrix_apply, id, Equiv.symm_apply_apply]

theorem mul_c₁ (hn : r + t = n) (y : Mx D a r) : mm y ((c₁ D hn).map (incA D)) = jn hn y 0 := by
  ext i j
  obtain ⟨s, rfl⟩ := (ee hn).surjective j
  rw [jn_ee]
  rcases s with k | k <;>
    simp [mm, c₁, Matrix.mul_apply, Matrix.one_apply, (ee hn).injective.eq_iff] <;>
    exact Finset.sum_eq_zero fun x _ => if_neg (by simp [Fin.ext_iff]; omega)

theorem mul_c₃ (hn : r + t = n) (y : Mx D a t) : mm y ((c₃ D hn).map (incA D)) = jn hn 0 y := by
  ext i j
  obtain ⟨s, rfl⟩ := (ee hn).surjective j
  rw [jn_ee]
  rcases s with k | k <;>
    simp [mm, c₃, Matrix.mul_apply, Matrix.one_apply, (ee hn).injective.eq_iff] <;>
    exact Finset.sum_eq_zero fun x _ => if_neg (by simp [Fin.ext_iff]; omega)

theorem compl_c₁ (hn : r + t = n) : IsCompl (c₁ D hn) 1 := by
  refine ⟨by simp, fun i hi => ?_⟩
  have : ee hn (Sum.inl ⟨i, hi⟩) = i := Fin.ext (ee_inl_val hn _)
  simp only [c₁, this]
  rfl

theorem compl_c₃ (hn : r + t = n) : IsCompl (c₃ D hn) (Pm D.host.E hn) := by
  refine ⟨Matrix.isUnit_det_of_right_inverse (Pm_mul_alt hn), fun i hi => ?_⟩
  have h1 : ff hn (Sum.inl ⟨i, hi⟩) = i := Fin.ext (ff_inl_val hn _)
  have h2 : πe hn i = ee hn (Sum.inr ⟨i, hi⟩) := by
    have := πe_ff_inl hn ⟨i, hi⟩
    rwa [h1] at this
  funext j
  simp only [Pm, c₃, Matrix.submatrix_apply]
  rw [h2]

theorem linInd_c₁ (hn : r + t = n) : LinearIndependent D.host.E (c₁ D hn) := by
  have h : c₁ D hn = (Pi.basisFun D.host.E (Fin n)) ∘ (fun k => ee hn (Sum.inl k)) := by
    funext k j
    simp [c₁, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [h]
  exact (Pi.basisFun D.host.E (Fin n)).linearIndependent.comp _
    (fun k k' h => Sum.inl_injective ((ee hn).injective h))

theorem jn_mul_bl (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) (A : Mx D r r) (B : Mx D r t) (C : Mx D t r)
    (E : Mx D t t) :
    HMul.hMul (jn hn x v) (bl hn A B C E) = jn hn (x * A + v * C) (x * B + v * E) := by
  simp only [jn, bl]
  rw [show (Matrix.fromCols x v).submatrix id (finSumFinEquiv.trans (finCongr hn)).symm =
    (Matrix.fromCols x v).submatrix id (⇑(finSumFinEquiv.trans (finCongr hn)).symm) from rfl,
    Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]

theorem jn_add (hn : r + t = n) (x x' : Mx D a r) (v v' : Mx D a t) : jn hn x v + jn hn x' v' = jn hn (x + x') (v + v') := by
  ext i j
  obtain ⟨s, rfl⟩ := (ee hn).surjective j
  simp only [Matrix.add_apply, jn_ee]
  rcases s with k | k <;> simp

end PositivityTheory.Rg.Rsw.L.LPartFT
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar GlobalTheory.CompanionTheory.ThetaPoisson

namespace PositivityTheory.Rg.Rsw.L.LPartFT

variable {D : D7} {n r t : ℕ}

theorem mem_gf_of {γ : G D n} (g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (hu : IsUnit g.det)
    (hU : IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (PositivityTheory.GramSchwartzFunctions.EC.Jm D.host.E n) g)
    (h : mat γ = g.map (incA D)) : γ ∈ GF D n := by
  obtain ⟨γ₀, h0, e⟩ := (GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn D n).2.1 g hu hU
  rwa [mat_injective' (e.trans h.symm)] at h0

theorem one_sub_bl' {R : Type} [CommRing R] (hn : r + t = n) :
    1 - bl hn (1 : Matrix (Fin r) (Fin r) R) 0 0 0 = bl hn 0 0 0 1 := by
  rw [← blockRowSubstitution_one hn, sub_eq_iff_eq_add, bl_add]; simp

theorem mat_w (hn : r + t = n) (M : Maps D hn) : mat M.w = (wr D.host.E n r).map (incA D) := by
  have hm : (-1 : Matrix (Fin r) (Fin r) D.host.E).map (incA D) = -1 := by
    ext i j; by_cases h : i = j <;> simp [h]
  rw [M.w_mat, wr, eId_eq hn, block_matrix_map, one_sub_bl', block_neg]
  simp [block_map, hm]

theorem mat_emb (hn : r + t = n) (M : Maps D hn) (w : G D t) (hw : IsW w) :
    mat (M.emb w) = (wE (bl hn (0 : Matrix (Fin r) (Fin r) D.host.E) 0 0 1)).map (incA D) := by
  have hm : (-1 : Matrix (Fin t) (Fin t) D.host.E).map (incA D) = -1 := by
    ext i j; by_cases h : i = j <;> simp [h]
  rw [M.emb_mat w 0 1 (-1) 0 hw, wE, one_sub_bl, block_neg, block_matrix_map]
  simp [block_map, hm]

theorem mat_emb' (hn : r + t = n) (M : Maps D hn) (w : G D t) (hw : IsW w) :
    mat (M.emb w) = blk4 (bl hn 1 0 0 0) (bl hn 0 0 0 1) (bl hn 0 0 0 (-1)) (bl hn 1 0 0 0) :=
  M.emb_mat w 0 1 (-1) 0 hw

theorem adj_Pm (hn : r + t = n) : adj ((Pm D.host.E hn).map (incA D)) = (Pm D.host.E hn)ᵀ.map (incA D) := by
  have h1 : (Pm D.host.E hn).map (incA D) = (1 : Mx D n n).submatrix (πe hn) id := by
    rw [Pm, ← Matrix.submatrix_map, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [adj, Matrix.transpose_map, h1, ← Matrix.submatrix_map, Matrix.map_one _ (map_zero _) (map_one _)]

def uP (D : D7) (hn : r + t = n) : GL (Fin n) D.host.E := ⟨(Pm D.host.E hn)ᵀ, Pm D.host.E hn, T_mul_Pm hn, Pm_mul_alt hn⟩

theorem mat_gQ {γ : G D n} (hn : r + t = n) (h : mat γ = (blk4 (Pm D.host.E hn)ᵀ 0 0 (Pm D.host.E hn)ᵀ).map (incA D)) :
    mat γ = blk4 ((uP D hn).1.map (incA D)) 0 0 (adj (((uP D hn)⁻¹).1.map (incA D))) := by
  rw [h, block_matrix_map]
  show blk4 _ _ _ _ = blk4 _ _ _ (adj ((Pm D.host.E hn).map (incA D)))
  rw [adj_Pm]
  simp [uP]

def xz {m : ℕ} (X : Mx D m n) : Mx D m (n + n) :=
  Matrix.of fun i k => Sum.elim (X i) (fun _ => (0 : AE D)) (finSumFinEquiv.symm k)

theorem xPart_xz {m : ℕ} (X : Mx D m n) : xPart (xz X) = X := by
  ext i j
  show Sum.elim (X i) (fun _ => (0 : AE D)) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) = _
  rw [Equiv.symm_apply_apply]; rfl

theorem yPart_xz {m : ℕ} (X : Mx D m n) : yPart (xz X) = 0 := by
  ext i j
  show Sum.elim (X i) (fun _ => (0 : AE D)) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))) = _
  rw [Equiv.symm_apply_apply]; rfl

theorem heis_xz (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (X : Mx D V.rank n) (F : Mx D V.rank n → ℂ) :
    PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂ ψ V (xz X) F 0 = F X := by
  simp [PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂, xPart_xz, yPart_xz, GlobalTheory.StdUnn.inner, halfTr]

theorem trace_inner_jn (V : HSp D) (hn : r + t = n) (x x' : Mx D V.rank r) (v v' : Mx D V.rank t) :
    Matrix.trace (GlobalTheory.StdUnn.inner V (jn hn x v) (jn hn x' v')) = Matrix.trace (ip V x x') + Matrix.trace (ip V v v') := by
  simp only [Matrix.trace, Matrix.diag, GlobalTheory.StdUnn.inner, ip, mm]
  rw [← (ee hn).sum_comp, Fintype.sum_sum_type]
  simp only [Matrix.mul_apply, adj, Matrix.transpose_apply, Matrix.map_apply, jn_ee, Matrix.fromCols_apply_inl,
    Matrix.fromCols_apply_inr]

theorem psi_ip_symm (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (x y : Mx D V.rank t) :
    ψ (trA (Matrix.trace (ip V x y))) = ψ (trA (Matrix.trace (ip V y x))) := by
  have hs := pairing_symm (n := t) (isHermND_gram V) ψ x y
  have e : ∀ a b : Mx D V.rank t, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing V.gram ψ a b = ψ (trA (Matrix.trace (ip V a b))) :=
    fun a b => by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing, GlobalTheory.SiegelWeilLitCompare.gramQ_eq]
      rfl
  rw [← e, ← e, hs]

theorem levi_zero {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω) (g : G D n) (u : GL (Fin n) D.host.E)
    (hg : mat g = blk4 (u.1.map (incA D)) 0 0 (adj ((u⁻¹).1.map (incA D)))) (F : schwartzA θ V.rank n) :
    (ω g F).1 0 = F.1 0 := by
  obtain ⟨-, hχ, -, -, hω⟩ := hS
  let a' : GL (Fin n) (AE D) := Matrix.GeneralLinearGroup.map (incA D) u
  have hdet : Matrix.GeneralLinearGroup.det a' =
      Units.map (incA D).toMonoidHom (Matrix.GeneralLinearGroup.det u) := by
    apply Units.ext
    simp [a', Matrix.GeneralLinearGroup.map]
    exact (RingHom.map_det _ _).symm
  have h1 : absA D (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]; exact absE_inclR _
  have h2 : χ (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]; exact hχ.2 _
  have hinv : (a'⁻¹).1 = (u⁻¹).1.map (incA D) := by
    show ((Matrix.GeneralLinearGroup.map (incA D) u)⁻¹).1 = _
    rw [← map_inv]; rfl
  have hg' : mat g = blk4 a'.1 0 0 (adj (a'⁻¹).1) := by
    rw [hinv]; exact hg
  rw [hω.levi g a' hg' F, h1, h2]
  simp [npow]

end PositivityTheory.Rg.Rsw.L.LPartFT
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar

namespace PositivityTheory.Rg.Rsw.L.LPartFT

variable {D : D7} {n r t : ℕ}

def h0 (D : D7) (p : ℕ) : HermE D p := ⟨0, by simp⟩

theorem j_zero (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {p : ℕ} (y : Mx D V.rank p) :
    ψ (halfTr (Matrix.trace (HMul.hMul ((h0 D p).1.map (incA D)) (GlobalTheory.StdUnn.inner V y y) : Mx D p p))) = 1 := by
  simp [h0, halfTr]

theorem clause1 {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω) (hn : r + t = n) (M : Maps D hn)
    (μr : Measure (Mx D V.rank r)) (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕) (Φ : schwartzA θ V.rank n) :
    (ω M.w Φ).1 0 = ∫ x, Φ.1 (jn hn x 0) ∂μr := by
  have hmat : mat M.w = (repMat (D.sp.cm.sig : D.host.E →+* D.host.E) (h0 D r).1 1).map (incA D) := by
    rw [h0, repMat_zero, mA_one, Matrix.mul_one, mat_w]
  have hγ : M.w ∈ GF D n := mem_gf_of _ (wr_unit (D.sp.cm.sig : D.host.E →+* D.host.E) hn).1 (wr_unit (D.sp.cm.sig : D.host.E →+* D.host.E) hn).2 (mat_w hn M)
  rw [partial_fourier_second_term hS Φ r (by omega) μr hμr (c₁ D hn) 1 (compl_c₁ hn) (h0 D r) M.w hγ hmat]
  unfold J pull
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [j_zero, mul_one]
  exact congrArg Φ.1 (mul_c₁ hn y)

theorem clause2 {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (hn : r + t = n) (Φ : schwartzA θ V.rank n) :
    (fun x => Φ.1 (jn hn x 0)) ∈ schwartzA θ V.rank r := by
  have := GlobalTheory.T.pullback_schwartz_linear_independent D θ hθ V.rank r n (c₁ D hn) (linInd_c₁ hn) Φ.1 Φ.2
  convert this using 1
  funext x
  exact congrArg Φ.1 (mul_c₁ hn x).symm

theorem clause3 {V : HSp D} {ψ χ θ μ ω} (hS : SetW D n V ψ χ θ μ ω) (hn : r + t = n) (M : Maps D hn)
    (μt : Measure (Mx D V.rank t)) (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕) (Φ : schwartzA θ V.rank n)
    (w : G D t) (hw : IsW w) (x : Mx D V.rank r) (v₀ : Mx D V.rank t) :
    (ω (M.emb w) Φ).1 (jn hn x v₀) = ∫ v, Φ.1 (jn hn x v) * ψ (trA (Matrix.trace (ip V v₀ v))) ∂μt := by
  have hγ : M.emb w ∈ GF D n := mem_gf_of _ (second_block_weyl_unitary (D.sp.cm.sig : D.host.E →+* D.host.E) hn).1 (second_block_weyl_unitary (D.sp.cm.sig : D.host.E →+* D.host.E) hn).2 (mat_emb hn M w hw)
  obtain ⟨γQ, hQ, hmQ⟩ := (GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn D n).2.1 _ (gQ_unit (D.sp.cm.sig : D.host.E →+* D.host.E) hn).1 (gQ_unit (D.sp.cm.sig : D.host.E →+* D.host.E) hn).2
  have hγ' : γQ⁻¹ * M.emb w ∈ GF D n := (GF D n).mul_mem ((GF D n).inv_mem hQ) hγ
  have hmat' : mat (γQ⁻¹ * M.emb w) =
      (repMat (D.sp.cm.sig : D.host.E →+* D.host.E) (h0 D t).1 (Pm D.host.E hn)).map (incA D) := by
    have h1 : mat γQ * (repMat (D.sp.cm.sig : D.host.E →+* D.host.E) (h0 D t).1 (Pm D.host.E hn)).map (incA D) =
        mat (M.emb w) := by
      rw [hmQ, ← Matrix.map_mul, h0, key3, mat_emb hn M w hw]
    rw [mat_mul', ← h1, ← Matrix.mul_assoc, mat_inv_mul', Matrix.one_mul]
  have hψ := hS.1
  have hθ := hS.2.2.1
  have hΨm := GlobalTheory.T.eisenstein_heisenberg_schwartz D ψ hψ θ hθ V n (HMul.hMul (xz (jn hn x v₀)) (mat (M.emb w))) Φ.1 Φ.2
  let Ψ : schwartzA θ V.rank n := ⟨Heisenberg₂ ψ V (HMul.hMul (xz (jn hn x v₀)) (mat (M.emb w))) Φ.1, hΨm⟩
  have hc := covar_w hS (M.emb w) hγ (HMul.hMul (xz (jn hn x v₀)) (mat (M.emb w))) Φ Ψ rfl
  have hv : HMul.hMul (HMul.hMul (xz (jn hn x v₀)) (mat (M.emb w))) (mat (M.emb w)⁻¹) = xz (jn hn x v₀) := by
    rw [Matrix.mul_assoc, mat_mul_inv', Matrix.mul_one]
  rw [hv] at hc
  have step1 : (ω (M.emb w) Φ).1 (jn hn x v₀) = (ω (M.emb w) Ψ).1 0 := by
    rw [hc]
    simp [PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂, xPart_xz, yPart_xz,
      GlobalTheory.StdUnn.inner, halfTr]
  have step2 : (ω (M.emb w) Ψ).1 0 = (ω (γQ⁻¹ * M.emb w) Ψ).1 0 := by
    conv_lhs => rw [show M.emb w = γQ * (γQ⁻¹ * M.emb w) by group]
    rw [map_mul, mul_apply_eq_comp]
    obtain ⟨-, hχ, -, -, hω⟩ := hS
    let u := uP D hn
    let a : GL (Fin n) (AE D) := Matrix.GeneralLinearGroup.map (incA D) u
    have hdet : Matrix.GeneralLinearGroup.det a =
        Units.map (incA D).toMonoidHom (Matrix.GeneralLinearGroup.det u) := by
      apply Units.ext
      simp [a, Matrix.GeneralLinearGroup.map]
      exact (RingHom.map_det _ _).symm
    have habs : absA D (Matrix.GeneralLinearGroup.det a) = 1 := by
      rw [hdet]
      exact absE_inclR _
    have hchar : χ (Matrix.GeneralLinearGroup.det a) = 1 := by
      rw [hdet]
      exact hχ.2 _
    have hinv : (a⁻¹).1 = (u⁻¹).1.map (incA D) := by
      show ((Matrix.GeneralLinearGroup.map (incA D) u)⁻¹).1 = _
      rw [← map_inv]
      rfl
    have hmatQ : mat γQ = blk4 a.1 0 0 (adj (a⁻¹).1) := by
      rw [hinv]
      exact mat_gQ hn hmQ
    rw [hω.levi γQ a hmatQ _, habs, hchar]
    simp [npow]
  rw [step1, step2, partial_fourier_second_term hS Ψ t (by omega) μt hμt (c₃ D hn) (Pm D.host.E hn) (compl_c₃ hn) (h0 D t) _ hγ' hmat']
  have hx : xPart (HMul.hMul (xz (jn hn x v₀)) (mat (M.emb w))) = jn hn x 0 := by
    rw [mat_emb' hn M w hw, x_part_mul_block, xPart_xz, yPart_xz, jn_mul_bl]; simp
  have hy : yPart (HMul.hMul (xz (jn hn x v₀)) (mat (M.emb w))) = jn hn 0 v₀ := by
    rw [mat_emb' hn M w hw, y_part_mul_block, xPart_xz, yPart_xz, jn_mul_bl]; simp
  have hip1 : ∀ {a b : ℕ} (z : Mx D V.rank b), ip V (0 : Mx D V.rank a) z = 0 := fun z => by simp [ip, mm, adj]
  have hip2 : ∀ {a b : ℕ} (z : Mx D V.rank a), ip V z (0 : Mx D V.rank b) = 0 := fun z => by simp [ip, mm]
  have htrace (a a' : Mx D V.rank r) (b b' : Mx D V.rank t) :
      Matrix.trace (GlobalTheory.StdUnn.inner V (jn hn a b) (jn hn a' b')) =
        Matrix.trace (ip V a a') + Matrix.trace (ip V b b') := by
    simp only [Matrix.trace, Matrix.diag, GlobalTheory.StdUnn.inner, ip, mm]
    rw [← (ee hn).sum_comp, Fintype.sum_sum_type]
    simp only [Matrix.mul_apply, adj, Matrix.transpose_apply, Matrix.map_apply, jn_ee,
      Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr]
  unfold J pull
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [j_zero, mul_one]
  show PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂ ψ V _ Φ.1 _ = _
  rw [show (HMul.hMul y ((c₃ D hn).map (incA D)) : Mx D V.rank n) = jn hn 0 y from mul_c₃ hn y]
  simp only [PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂]
  rw [hx, hy, jn_add, htrace, htrace, hip1, hip1, hip2]
  simp only [Matrix.trace_zero, zero_add, add_zero, halfTr, map_zero, mul_zero]
  rw [psi_ip_symm, mul_comm]

end PositivityTheory.Rg.Rsw.L.LPartFT

namespace PositivityTheory.Rg.Rsw.L

theorem partFT : PartFT := by
  intro D n r t hn M V ψ hψ χ hχ hη θ hθ μ hμ ω hω μr μt hμr hμt Φ
  have hS : LPartFT.SetW D n V ψ χ θ μ ω := ⟨hψ, hχ, hθ, hμ, hω⟩
  exact ⟨LPartFT.clause1 hS hn M μr hμr Φ, LPartFT.clause2 hθ hn Φ,
    fun w hw x v₀ => LPartFT.clause3 hS hn M μt hμt Φ w hw x v₀⟩

end PositivityTheory.Rg.Rsw.L

module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictOut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CyclicDiscriminantLatticesFormOneGenus
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitRowLatticeMiddleIffGluedLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameFixingIsometrySplitRowLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeEqMassOfReal
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.RankVolume

theorem definiteSpaceVolume_eq_mass_of_volumeComparison (hU : ∀ D : D7, StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D) :
    ∀ D : D7, Formalism.L2.Theta.RealTied D → StandardLattice.volY0 D = StandardLattice.massI D D.R.r := fun D h =>
  have hT : StandardLattice.VolTie D := Formalism.L2.Theta.VolTieG.volTie h.vol
  StandardLattice.volume_eq_mass_at_rank D (StandardLattice.volume_eq_mass_of_definite D (StandardLattice.volumeMass_of_unfolding D (hU D hT))
    (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.mass_volume_identity_of_class_decomp D hT (GlobalTheory.genusMassStd_all D)
      (GlobalTheory.DefiniteDecompObj.doubleCosets_mass D)))

end GlobalTheory.RankVolume
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermRowDoubleCosetEqIffIsometries
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermRowDoubleCosetEqIffIsometries
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.KeyIff

variable {D : D7}

theorem one_mem {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : (1 : GV D) ∈ NRat F := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, fun j x _ => ?_, fun x _ => ?_⟩
  · simp
  · simp

theorem dcoset_eq_iff {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (γ₁ γ₂ : GV D) :
    ({δ | ∃ n ∈ NRat F, ∃ n' ∈ NRat F', δ = n * γ₁ * n'} : Set (GV D)) =
        {δ | ∃ n ∈ NRat F, ∃ n' ∈ NRat F', δ = n * γ₂ * n'} ↔
      ∃ n ∈ NRat F, ∃ n' ∈ NRat F', γ₂ = n * γ₁ * n' := by
  constructor
  · intro h
    have hm : γ₂ ∈ {δ | ∃ n ∈ NRat F, ∃ n' ∈ NRat F', δ = n * γ₂ * n'} :=
      ⟨1, one_mem F, 1, one_mem F', by simp⟩
    rw [← h] at hm
    exact hm
  · rintro ⟨n, hn, n', hn', rfl⟩
    ext δ
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨a * n⁻¹, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F ha (Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv F hn),
        n'⁻¹ * b, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F' (Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_inv F' hn') hb, ?_⟩
      group
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a * n, Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F ha hn, n' * b,
        Formalism.L2.SG.NGCut.NormalVectorPairings.NRat_mul F' hn' hb, by group⟩

theorem key_eq_iff : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', key t = key t' ↔ t.lam = t'.lam ∧ t.lam' = t'.lam' ∧ KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lin t'.lin := by
  intro D X Y u u' t t'
  have hkey : key t = key t' ↔
      (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' ∧ nmlOf Y u u' t = nmlOf Y u u' t' := Prod.ext_iff
  have hrow : (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' ↔ t.lam = t'.lam ∧ t.lam' = t'.lam' ∧
      iotaOf Y.TR (Y.cs u) (Y.cs u') t = iotaOf Y.TR (Y.cs u) (Y.cs u') t' := by
    show rowOf Y.TR (Y.cs u) (Y.cs u') t = rowOf Y.TR (Y.cs u) (Y.cs u') t' ↔ _
    simp only [rowOf, Prod.mk.injEq, Subtype.mk.injEq]
  have hnml : nmlOf Y u u' t = nmlOf Y u u' t' ↔
      ∃ n ∈ NRat (lf D (X.Fu u)), ∃ n' ∈ NRat (lf D (X.Fu u')), t'.lin = n * t.lin * n' :=
    dcoset_eq_iff _ _ _ _
  rw [hkey, hrow, hnml]
  unfold KeyEq
  constructor
  · rintro ⟨⟨hl, hl', hi⟩, hc⟩
    exact ⟨hl, hl', hc, (Formalism.L2.SG.Pf.iotaDictAllC_holds D X Y u u' t t' hl hl').1 hi⟩
  · rintro ⟨hl, hl', hc, hi⟩
    exact ⟨⟨hl, hl', (Formalism.L2.SG.Pf.iotaDictAllC_holds D X Y u u' t t' hl hl').2 hi⟩, hc⟩

end GlobalTheory.Unfold.KeyIff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermRowDoubleCosetEqIffIsometriesStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.term_row_double_coset_eq_iff_isometries : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', key t = key t' ↔ t.lam = t'.lam ∧ t.lam' = t'.lam' ∧ KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lin t'.lin := by
  first | exact @GlobalTheory.Unfold.KeyIff.key_eq_iff | exact GlobalTheory.Unfold.KeyIff.key_eq_iff | (intros; apply GlobalTheory.Unfold.KeyIff.key_eq_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BinaryHermitianFormRepresentsTotallyPositive
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BinaryHermitianFormRepresentsTotallyPositive
noncomputable section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G

namespace GlobalTheory.BinaryRep

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem gram_diag_pos {r : ℕ} (τ : E →+* ℂ) (d : Fin r → E)
    (hd : ∀ i, (τ (d i)).im = 0 ∧ 0 < (τ (d i)).re) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      FD.gram τ (Matrix.diagonal d) Q = Matrix.diagonal fun a : Fin r => ((FD.sgn r (a : ℕ) : ℝ) : ℂ) := by
  classical
  set q : Fin r → ℝ := fun i => (Real.sqrt (τ (d i)).re)⁻¹ with hq
  have hq2 : ∀ i, (q i : ℂ) * τ (d i) * (q i : ℂ) = 1 := by
    intro i
    have h1 : τ (d i) = ((τ (d i)).re : ℂ) := Complex.ext rfl (by simp [(hd i).1])
    have h2 : q i * q i * (τ (d i)).re = 1 := by
      rw [hq]
      simp only
      rw [← mul_inv, Real.mul_self_sqrt (hd i).2.le, inv_mul_cancel₀ (hd i).2.ne']
    rw [h1]
    exact_mod_cast (by linarith [h2] : q i * (τ (d i)).re * q i = 1)
  refine ⟨Matrix.diagonal fun i => (q i : ℂ), ?_, ?_⟩
  · rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    have : (q i : ℂ) ≠ 0 := fun h => by simpa [h] using hq2 i
    exact this
  · ext a b
    simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      have hs : FD.sgn r (a : ℕ) = 1 := by simp [FD.sgn, a.isLt]
      simp [hs, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', Complex.conj_ofReal]
      rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp only [if_true, Complex.conj_ofReal]
      linear_combination hq2 a
    · simp [hab, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : a = x
      · subst hx
        simp [hab]
      · simp [hx]

end GlobalTheory.BinaryRep

namespace GlobalTheory.BinaryRep

theorem represents_totallyPositive : ∀ (K : Type) [Field K] [NumberField K] [StarRing K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ a b n : K, star a = a → star b = b → star n = n →
    (∀ φ : K →+* ℂ, 0 < (φ a).re) → (∀ φ : K →+* ℂ, 0 < (φ b).re) → (∀ φ : K →+* ℂ, 0 < (φ n).re) →
    ∃ s t : K, a * (s * star s) + b * (t * star t) = n := by
  intro K _ _ _ hc a b n ha hb hn hpa hpb hpn
  haveI : IsCMField K := GlobalTheory.OrthoLattice.isCMField_of_star K hc.1 hc.2.1
  let φ0 : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have hst : ∀ x : K, star x = FD.cc x := fun x =>
    φ0.injective (by rw [FD.cc, IsCMField.complexEmbedding_complexConj]; exact hc.2.1 φ0 x)
  have hreal : ∀ x : K, star x = x → ∀ τ : K →+* ℂ, (τ x).im = 0 := by
    intro x hx τ
    have h := hc.2.1 τ x
    rw [hx] at h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hne : ∀ x : K, (∀ φ : K →+* ℂ, 0 < (φ x).re) → x ≠ 0 := by
    intro x hx h0
    have := hx φ0
    simp [h0] at this
  have ha0 := hne a hpa
  have hb0 := hne b hpb
  have hn0 := hne n hpn
  have hca : FD.cc a = a := by rw [← hst, ha]
  have hcb : FD.cc b = b := by rw [← hst, hb]
  have hcn : FD.cc n = n := by rw [← hst, hn]
  have hcab : FD.cc (a * b * n) = a * b * n := by
    rw [← hst, star_mul, star_mul, ha, hb, hn]; ring
  set G : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![a, b] with hG
  set G' : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![n, a * b * n] with hG'
  have herm_diag : ∀ d : Fin 2 → K, (∀ i, FD.cc (d i) = d i) →
      ∀ i j, FD.cc (Matrix.diagonal d i j) = Matrix.diagonal d j i := by
    intro d hd i j
    by_cases h : i = j
    · subst h; simp [hd]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h), FD.cc]
  have hGh : ∀ i j, FD.cc (G i j) = G j i :=
    herm_diag _ (fun i => by fin_cases i <;> simp [hca, hcb])
  have hG'h : ∀ i j, FD.cc (G' i j) = G' j i :=
    herm_diag _ (fun i => by fin_cases i <;> simp [hcn, hcab])
  have hdG : G.det = a * b := by simp [hG, Matrix.det_diagonal, Fin.prod_univ_two]
  have hdG' : G'.det = n * (a * b * n) := by simp [hG', Matrix.det_diagonal, Fin.prod_univ_two]
  have hpos : ∀ d : Fin 2 → K, (∀ i, star (d i) = d i ∧ ∀ φ : K →+* ℂ, 0 < (φ (d i)).re) →
      ∀ τ : K →+* ℂ, ∀ i, (τ (d i)).im = 0 ∧ 0 < (τ (d i)).re :=
    fun d hd τ i => ⟨hreal _ (hd i).1 τ, (hd i).2 τ⟩
  have habn : star (a * b * n) = a * b * n := by rw [star_mul, star_mul, ha, hb, hn]; ring
  have hpabn : ∀ φ : K →+* ℂ, 0 < (φ (a * b * n)).re := by
    intro φ
    have e : ∀ x : K, star x = x → (φ x : ℂ) = ((φ x).re : ℂ) := fun x hx =>
      Complex.ext rfl (by simp [hreal x hx φ])
    rw [map_mul, map_mul, e a ha, e b hb, e n hn]
    simp only [← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_pos (mul_pos (hpa φ) (hpb φ)) (hpn φ)
  obtain ⟨γ, hγ⟩ := (GlobalTheory.QNorm.landherr_and_landherrSt.2) K 2 G G' hGh hG'h
    (by rw [hdG]; exact mul_ne_zero ha0 hb0)
    (by rw [hdG']; exact mul_ne_zero hn0 (mul_ne_zero (mul_ne_zero ha0 hb0) hn0))
    (fun τ => ⟨2,
      gram_diag_pos τ ![a, b] (hpos _ (fun i => by fin_cases i <;> simp [ha, hb, hpa, hpb]) τ),
      gram_diag_pos τ ![n, a * b * n]
        (hpos _ (fun i => by fin_cases i; exacts [⟨hn, hpn⟩, ⟨habn, hpabn⟩]) τ)⟩)
    ⟨n, by rw [hdG', hdG, hcn]; ring⟩
  have h := hγ (Pi.single 0 1) (Pi.single 0 1)
  set v := (γ : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single 0 1 with hv
  refine ⟨v 0, v 1, ?_⟩
  simp only [FD.herm, Fin.sum_univ_two, hG, hG', Matrix.diagonal_apply_eq,
    Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
    Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)] at h
  simp [FD.cc] at h
  rw [hst, hst]
  simp only [FD.cc]
  linear_combination h

end GlobalTheory.BinaryRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BinaryHermitianFormRepresentsTotallyPositiveStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.binaryHermitianForm_represents_totallyPositive : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ a b n : K, star a = a → star b = b → star n = n → (∀ φ : K →+* ℂ, 0 < (φ a).re) → (∀ φ : K →+* ℂ, 0 < (φ b).re) → (∀ φ : K →+* ℂ, 0 < (φ n).re) → ∃ s t : K, a * (s * star s) + b * (t * star t) = n := by
  first | exact @GlobalTheory.BinaryRep.represents_totallyPositive | exact GlobalTheory.BinaryRep.represents_totallyPositive | (intros; apply GlobalTheory.BinaryRep.represents_totallyPositive <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalLatticeOfUnimodularLandherr
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalLatticeOfUnimodularLandherr
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass

theorem exists_orthoLattice_of_unimodular : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], IsCMUnram K → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) :=
  fun K _ _ _ hK => GlobalTheory.OrthoLattice.hasOrtho K hK

end GlobalTheory.Mass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalLatticeOfUnimodularLandherrStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormalLattice_of_unimodular_landherr : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], IsCMUnram K → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) := by
  first | exact @GlobalTheory.Mass.exists_orthoLattice_of_unimodular | exact GlobalTheory.Mass.exists_orthoLattice_of_unimodular | (intros; apply GlobalTheory.Mass.exists_orthoLattice_of_unimodular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowBaseLatticesMemSameHermitianGenus
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowBaseLatticesMemSameHermitianGenus
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.RowsGenus

theorem main : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ Λ' : LatV D, IsRowLat D F0 Λ' → L0X D Λ' (lf D F0) ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0)) := by
  intro D u hp _ hs F0 he hz Λ hΛ Λ' hΛ'
  have h := (GlobalTheory.Mass.RowPerp.main D u F0 he hz).2
  exact ((GlobalTheory.Mass.CyclicGenus.main D.host.E (D.sp.X 0).V (D.sp.X 0).hT D.sp.cm.cmUnram (D.sp.X 0).herm
    (D.sp.X 0).nondeg (Tu D u) hp hs).2 _ _ (h Λ hΛ).1 (h Λ hΛ).2).2 (h Λ' hΛ')

end GlobalTheory.LoopC.RowsGenus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowBaseLatticesMemSameHermitianGenusStatement
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowBaseLattices_mem_same_hermitianGenus : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ Λ' : LatV D, IsRowLat D F0 Λ' → L0X D Λ' (lf D F0) ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0)) := by
  first | exact @GlobalTheory.LoopC.RowsGenus.main | exact GlobalTheory.LoopC.RowsGenus.main | (intros; apply GlobalTheory.LoopC.RowsGenus.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesSameMiddleConjugateUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesSameMiddleConjugateUnipotent
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LoopC

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}

theorem rowsLift_mem_orth {U : Submodule E S.V} {x : S.V} :
    x ∈ orth S U ↔ ∀ y ∈ U, S.hT y x = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem rowsLift_fix_span {ι : Type} (v : ι → S.V) (s : Set ι) (n : S.V ≃ₗ[E] S.V)
    (hn : ∀ a, n (v a) = v a) : ∀ x ∈ Submodule.span E (v '' s), n x = x := by
  intro x hx
  have hle : Submodule.span E (v '' s) ≤ LinearMap.eqLocus (n : S.V →ₗ[E] S.V) LinearMap.id := by
    rw [Submodule.span_le]
    rintro _ ⟨a, -, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_eqLocus]
    simpa using hn a
  have h := hle hx
  rw [LinearMap.mem_eqLocus] at h
  simpa using h

theorem rowsLift_map_eq (U : Submodule E S.V) (n : S.V ≃ₗ[E] S.V) (hn : ∀ x ∈ U, n x = x) :
    U.map (n : S.V →ₗ[E] S.V) = U := by
  ext y
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [hn x hx]
  · intro hy
    exact ⟨y, hy, hn y hy⟩

theorem rowsLift_orth_iff (U : Submodule E S.V) (n : S.V ≃ₗ[E] S.V) (hi : n ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hn : ∀ x ∈ U, n x = x) (x : S.V) : n x ∈ orth S U ↔ x ∈ orth S U := by
  have hi' : ∀ a b, S.hT (n a) (n b) = S.hT a b := hi
  rw [rowsLift_mem_orth, rowsLift_mem_orth]
  refine forall₂_congr fun y hy => ?_
  have h := hi' y x
  rw [hn y hy] at h
  rw [h]

theorem rowsLift_Lsub_gmap (F : LFlag S r T) (Λ : Submodule (𝓞 E) S.V) (n : S.V ≃ₗ[E] S.V)
    (hi : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hn : ∀ x ∈ Xsp F, n x = x)
    (hq : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F) :
    Lsub (Formalism.HermitianLatticesTheory.gmap n Λ) F = Lsub Λ F := by
  ext y
  unfold Lsub Lrep
  constructor
  · intro hy
    obtain ⟨hy1, hyO⟩ := Submodule.mem_inf.mp hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy1
    obtain ⟨ha1, haO⟩ := Submodule.mem_inf.mp ha
    obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.mp ha1
    have hlO : l ∈ orth S (Xsp F) := (rowsLift_orth_iff _ n hi hn l).mp haO
    have hd : n l - l ∈ Xsp F := hq l hlO
    refine Submodule.mem_inf.mpr ⟨Submodule.mem_sup.mpr
      ⟨l, Submodule.mem_inf.mpr ⟨hl, hlO⟩, (n l - l) + b, (toO S (Xsp F)).add_mem hd hb, ?_⟩, hyO⟩
    show l + (n l - l + b) = n l + b
    abel
  · intro hy
    obtain ⟨hy1, hyO⟩ := Submodule.mem_inf.mp hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy1
    obtain ⟨hl, haO⟩ := Submodule.mem_inf.mp ha
    have hnO : n a ∈ orth S (Xsp F) := (rowsLift_orth_iff _ n hi hn a).mpr haO
    have hd : n a - a ∈ Xsp F := hq a haO
    refine Submodule.mem_inf.mpr ⟨Submodule.mem_sup.mpr
      ⟨n a, Submodule.mem_inf.mpr ⟨Submodule.mem_map.mpr ⟨a, hl, rfl⟩, hnO⟩, b - (n a - a),
        (toO S (Xsp F)).sub_mem hb hd, ?_⟩, hyO⟩
    abel

theorem rowsLift_cancel (X W : Submodule E S.V) (hXW : ∀ x ∈ X, x ∈ W → x = 0)
    (A B : Submodule (𝓞 E) S.V) (h : (A ⊓ toO S W) ⊔ toO S X = (B ⊓ toO S W) ⊔ toO S X) :
    A ⊓ toO S W ≤ B ⊓ toO S W := by
  intro y hy
  have h1 : y ∈ (A ⊓ toO S W) ⊔ toO S X := Submodule.mem_sup_left hy
  rw [h] at h1
  obtain ⟨b, hb, x, hx, rfl⟩ := Submodule.mem_sup.mp h1
  have hxW : x ∈ W := by
    have h2 : b + x - b ∈ W := W.sub_mem (Submodule.mem_inf.mp hy).2 (Submodule.mem_inf.mp hb).2
    simpa using h2
  rw [hXW x hx hxW, add_zero]
  exact hb

end Generic

theorem rowsLift_X_inf_Wb (D : D7) (x : (hS D).V)
    (hx : x ∈ Submodule.span D.host.E (Set.range D.sp.hypE)) (hW : x ∈ Wb D) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).mp hx
  have hW' : (∑ i, c i • D.sp.hypE i) ∈ orth (hS D)
      (Submodule.span D.host.E (Set.range D.sp.hypE ∪ Set.range D.sp.hypF)) := hW
  have hc : ∀ j, c j = 0 := by
    intro j
    have h1 : (hS D).hT (D.sp.hypF j) (∑ i, c i • D.sp.hypE i) = 0 :=
      (rowsLift_mem_orth.mp hW') _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩))
    have hs : ∀ i, (hS D).hT (D.sp.hypF j) (D.sp.hypE i) = if i = j then 1 else 0 := by
      intro i
      rw [← (hS D).herm.eq (D.sp.hypE i) (D.sp.hypF j), D.sp.hyp_ef]
      split_ifs <;> simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h1
    simpa [hs] using h1
  simp [hc]

theorem rowsLift_fixX {D : D7} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}
    {n : (hS D).V ≃ₗ[D.host.E] (hS D).V} (hn : FixFr D (lf D F0) n) :
    (∀ a, n (F0.e a) = F0.e a) ∧ n F0.z = F0.z ∧ ∀ x ∈ F0.X, n x = x := by
  obtain ⟨-, hfr, -⟩ := hn
  have he : ∀ a, n (F0.e a) = F0.e a := by
    intro a
    have h := hfr (Fin.castSucc a)
    simpa [frame, FlagG.fvec, lf] using h
  have hz : n F0.z = F0.z := by
    have h := hfr (Fin.last _)
    simpa [frame, FlagG.fvec, lf] using h
  refine ⟨he, hz, ?_⟩
  intro x hx
  rw [FlagG.X, ← Set.image_univ] at hx
  exact rowsLift_fix_span F0.e Set.univ n he x hx

theorem rowsLift : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ₁ Λ₂ : LatV D, IsRowLat D F0 Λ₁ → IsRowLat D F0 Λ₂ → Lsub Λ₁ (lf D F0) = Lsub Λ₂ (lf D F0) → ∃ n ∈ stabF D F0, (∀ x ∈ orth (hS D) F0.X, n x - x ∈ F0.X) ∧ Formalism.HermitianLatticesTheory.gmap n Λ₁ = Λ₂ := by
  intro D u _ hT3 _ F0 he hz Λ₁ Λ₂ h₁ h₂ hL
  have hT1 : 1 ≤ Tu D u := by omega
  have hB : IsBase D u F0 := ⟨he, hz⟩
  obtain ⟨n₁, hf₁, hs₁, hr₁⟩ := GlobalTheory.T.exists_frameFixing_isometry_split_rowLattice D u F0 Λ₁ hB h₁ hT1
  obtain ⟨n₂, hf₂, hs₂, hr₂⟩ := GlobalTheory.T.exists_frameFixing_isometry_split_rowLattice D u F0 Λ₂ hB h₂ hT1
  have hfx₁ := rowsLift_fixX hf₁
  have hfx₂ := rowsLift_fixX hf₂
  have hLs : ∀ (n : (hS D).V ≃ₗ[D.host.E] (hS D).V) (Λ : LatV D), FixFr D (lf D F0) n →
      Lsub (Formalism.HermitianLatticesTheory.gmap n Λ) (lf D F0) = Lsub Λ (lf D F0) := by
    intro n Λ hf
    have hX := (rowsLift_fixX hf).2.2
    obtain ⟨hi, -, hq⟩ := hf
    exact rowsLift_Lsub_gmap (lf D F0) Λ n hi hX hq
  have hW : ∀ Λ : LatV D, IsRowLat D F0 Λ → IsSplit D F0 Λ →
      Lsub Λ (lf D F0) = (Λ ⊓ toO (hS D) (Wb D)) ⊔ toO (hS D) F0.X := fun Λ hr hs =>
    ((GlobalTheory.T.splitRowLattice_middle_iff_gluedLattice D u F0 Λ hT1 hB hr).1 hs).2
  have heq : (Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ ⊓ toO (hS D) (Wb D)) ⊔ toO (hS D) F0.X =
      (Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ ⊓ toO (hS D) (Wb D)) ⊔ toO (hS D) F0.X :=
    (hW _ hr₁ hs₁).symm.trans
      (((hLs n₁ Λ₁ hf₁).trans (hL.trans (hLs n₂ Λ₂ hf₂).symm)).trans (hW _ hr₂ hs₂))
  have hXW : ∀ x ∈ F0.X, x ∈ Wb D → x = 0 := fun x hx hw =>
    rowsLift_X_inf_Wb D x (by rw [← he]; exact hx) hw
  have hM : Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ ⊓ toO (hS D) (Wb D) = Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ ⊓ toO (hS D) (Wb D) :=
    le_antisymm (rowsLift_cancel _ _ hXW _ _ heq) (rowsLift_cancel _ _ hXW _ _ heq.symm)
  have e₁ : Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ = XS D F0 ⊔ (Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ ⊓ toO (hS D) (Wb D)) ⊔ YS D := hs₁
  have e₂ : Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ = XS D F0 ⊔ (Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ ⊓ toO (hS D) (Wb D)) ⊔ YS D := hs₂
  have hMM : Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ = Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ := by
    rw [e₁, e₂, hM]
  have hfix : ∀ v, n₁ v = v → n₂ v = v → (n₁.trans n₂.symm) v = v := by
    intro v h1 h2
    rw [LinearEquiv.trans_apply, h1, LinearEquiv.symm_apply_eq, h2]
  obtain ⟨hi₁, -, hq₁⟩ := hf₁
  obtain ⟨hi₂, -, hq₂⟩ := hf₂
  have hmem : n₁.trans n₂.symm ∈ stabF D F0 := by
    simp only [stabF, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩
    · exact (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).inv_mem hi₂) hi₁
    · intro j
      exact rowsLift_map_eq (F0.Xa j) (n₁.trans n₂.symm) (fun x hx =>
        rowsLift_fix_span F0.e _ _ (fun a => hfix _ (hfx₁.1 a) (hfx₂.1 a)) x hx)
    · exact hfix _ hfx₁.2.1 hfx₂.2.1
  refine ⟨n₁.trans n₂.symm, hmem, ?_, ?_⟩
  · intro x hx
    have hy : n₁ x ∈ orth (hS D) F0.X := (rowsLift_orth_iff F0.X n₁ hi₁ hfx₁.2.2 x).mpr hx
    obtain ⟨w, hw⟩ : ∃ w, w = n₂.symm (n₁ x) := ⟨_, rfl⟩
    have hnw : n₂ w = n₁ x := by rw [hw, LinearEquiv.apply_symm_apply]
    have hwO : w ∈ orth (hS D) F0.X :=
      (rowsLift_orth_iff F0.X n₂ hi₂ hfx₂.2.2 w).mp (by rw [hnw]; exact hy)
    have h1 : n₁ x - x ∈ F0.X := hq₁ x hx
    have h2 : n₂ w - w ∈ F0.X := hq₂ w hwO
    rw [hnw] at h2
    have h3 : (n₁.trans n₂.symm) x - x = (n₁ x - x) - (n₁ x - w) := by
      rw [LinearEquiv.trans_apply, ← hw]
      abel
    rw [h3]
    exact F0.X.sub_mem h1 h2
  · have hcomp : Formalism.HermitianLatticesTheory.gmap (n₁.trans n₂.symm) Λ₁ =
        Formalism.HermitianLatticesTheory.gmap n₂.symm (Formalism.HermitianLatticesTheory.gmap n₁ Λ₁) := by
      ext y
      simp [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
    have hback : Formalism.HermitianLatticesTheory.gmap n₂.symm (Formalism.HermitianLatticesTheory.gmap n₂ Λ₂) = Λ₂ := by
      ext y
      simp [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
    rw [hcomp, hMM, hback]

end GlobalTheory.LoopC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesSameMiddleConjugateUnipotentStatement
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_lattices_same_middle_conjugate_unipotent : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ₁ Λ₂ : LatV D, IsRowLat D F0 Λ₁ → IsRowLat D F0 Λ₂ → Lsub Λ₁ (lf D F0) = Lsub Λ₂ (lf D F0) → ∃ n ∈ stabF D F0, (∀ x ∈ orth (hS D) F0.X, n x - x ∈ F0.X) ∧ Formalism.HermitianLatticesTheory.gmap n Λ₁ = Λ₂ := by
  first | exact @GlobalTheory.LoopC.rowsLift | exact GlobalTheory.LoopC.rowsLift | (intros; apply GlobalTheory.LoopC.rowsLift <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsGenusWeightedSumComparison
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BlkOfOfPtEntry
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXVolH
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalCommonStabiliserUnitriangularCoords

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitriangularFramesGramEqCellPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitriangularFramesGramEqCellPoint
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocOver

section MatrixFacts

variable {K : Type*} [Field K] {N : ℕ}

theorem upUni_inv_facts {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) :
    IsUpUni U⁻¹ ∧ U * U⁻¹ = 1 ∧ U⁻¹ * U = 1 := by
  have hbt : U.BlockTriangular id := fun i j hij => (hU i j).1 hij
  have hdet : U.det = 1 := by
    rw [Matrix.det_of_upperTriangular hbt]
    exact Finset.prod_eq_one fun i _ => (hU i i).2 rfl
  have hu : IsUnit U.det := by rw [hdet]; exact isUnit_one
  have h1 : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hu
  have h2 : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U hu
  letI := Matrix.invertibleOfIsUnitDet U hu
  have hbt' : U⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  refine ⟨fun i j => ⟨fun hij => hbt' hij, fun hij => ?_⟩, h1, h2⟩
  subst hij
  have e := congrFun (congrFun h2 i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at e
  · rw [(hU i i).2 rfl, mul_one] at e; simpa using e
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hbt' h, zero_mul]
    · rw [(hU k i).1 h, mul_zero]
  · simp

theorem loUni_inv_facts {L : Matrix (Fin N) (Fin N) K} (hL : IsLoUni L) :
    IsLoUni L⁻¹ ∧ L * L⁻¹ = 1 ∧ L⁻¹ * L = 1 := by
  have hT : IsUpUni L.transpose := fun i j => ⟨fun hij => (hL j i).1 hij, fun hij => by subst hij; simpa using (hL i i).2 rfl⟩
  obtain ⟨h0, -, -⟩ := upUni_inv_facts hT
  have hbt : L.transpose.BlockTriangular id := fun i j hij => (hT i j).1 hij
  have hdet : L.det = 1 := by
    rw [← Matrix.det_transpose, Matrix.det_of_upperTriangular hbt]
    exact Finset.prod_eq_one fun i _ => (hT i i).2 rfl
  have hu : IsUnit L.det := by rw [hdet]; exact isUnit_one
  refine ⟨fun i j => ?_, Matrix.mul_nonsing_inv L hu, Matrix.nonsing_inv_mul L hu⟩
  have e : L⁻¹ i j = (L.transpose)⁻¹ j i := by rw [← Matrix.transpose_nonsing_inv]; rfl
  rw [e]
  exact ⟨fun hij => (h0 j i).1 hij, fun hij => (h0 j i).2 hij.symm⟩

end MatrixFacts

theorem tw_tw {K : Type*} [CommRing K] {r : ℕ} (B : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Formalism.MainNotions.BridgeLemma₂.rows_tw (Formalism.MainNotions.BridgeLemma₂.rows_tw B) = B := by
  have hs : ∀ n : ℕ, ((-1 : K) ^ n) * ((-1) ^ n) = 1 := by
    intro n; rw [← mul_pow]; simp
  ext i j
  simp only [Formalism.MainNotions.BridgeLemma₂.rows_tw, Matrix.of_apply]
  linear_combination (B i j * (-1) ^ (r - j.val) * (-1) ^ (r - j.val)) * hs (r - i.val) + B i j * hs (r - j.val)

theorem tw_upUni {K : Type*} [CommRing K] {r : ℕ} {B : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hB : IsUpUni B) : IsUpUni (Formalism.MainNotions.BridgeLemma₂.rows_tw B) := by
  intro i j
  refine ⟨fun hij => by simp [Formalism.MainNotions.BridgeLemma₂.rows_tw, (hB i j).1 hij], fun hij => ?_⟩
  subst hij
  simp only [Formalism.MainNotions.BridgeLemma₂.rows_tw, Matrix.of_apply, (hB i i).2 rfl, mul_one]
  rw [← mul_pow]; simp

variable {D : D7}

theorem zhatL_chg {T T' : D.host.E} {F F₂ : LFlag (D.sp.Y 0) D.R.rS T} {F₁ F₃ : LFlag (D.sp.Y 0) D.R.rS T'}
    {A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E}
    (h₂ : Chg (frame F) A (frame F₂)) (h₃ : Chg (frame F₁) A' (frame F₃)) :
    ZhatL F₂ F₃ = A.conjTranspose * ZhatL F F₁ * A' := by
  ext a b
  have e2 : F₂.fl.fvec a = ∑ c, A c a • F.fl.fvec c := h₂ a
  have e3 : F₃.fl.fvec b = ∑ d, A' d b • F₁.fl.fvec d := h₃ b
  simp only [ZhatL, Zhat, brS, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [e2, e3]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [RingHom.id_apply, starRingEnd_apply]
  ring

theorem zhatL_leadMinor {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ : LFlag (D.sp.Y 0) D.R.rS T')
    {A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E} (hA : Uni A) (hA' : Uni A') (l : ℕ) :
    leadMinorE (A.conjTranspose * ZhatL F F₁ * A') l = leadMinorE (ZhatL F F₁) l := by
  unfold leadMinorE
  split_ifs with hl
  · exact Formalism.HermitianLatticeCounting.P.leadingMinorTriangularInvariant D.host.E _ l hl _ _ _
      (fun i => by simp [Matrix.conjTranspose_apply, hA.2 i])
      (fun i j hij => by simp [Matrix.conjTranspose_apply, hA.1 j i hij])
      (fun i => hA'.2 i) (fun i j hij => hA'.1 i j hij)
  · rfl

theorem base_frames_at_point : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ : LFlag (D.sp.Y 0) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)), T ≠ 0 → T' ≠ 0 → IsInCell (ZhatOM (ZhatL F F₁)) w → (∃ (F00 : LFlag (D.sp.Y 0) D.R.rS T) (F'0 : LFlag (D.sp.Y 0) D.R.rS T'), Tri D.host.E (frame F) (frame F00) ∧ Tri D.host.E (frame F₁) (frame F'0) ∧ ZhatOM (ZhatL F00 F'0) = ptMat w) ∧ ∀ (F₂ : LFlag (D.sp.Y 0) D.R.rS T) (F₃ : LFlag (D.sp.Y 0) D.R.rS T'), Tri D.host.E (frame F) (frame F₂) → Tri D.host.E (frame F₁) (frame F₃) → IsInCell (ZhatOM (ZhatL F₂ F₃)) w ∧ Gval F₂ F₃ = Gval F F₁ := by
  intro D T T' F F₁ w hT hT' hcell
  obtain ⟨L, U, hL, hU, hZ⟩ := hcell
  refine ⟨?_, ?_⟩
  · obtain ⟨hLi, -, hLL⟩ := loUni_inv_facts hL
    obtain ⟨hUi, hUU, -⟩ := upUni_inv_facts hU
    have hA : Uni (L⁻¹).conjTranspose :=
      ⟨fun a b hba => by simp [Matrix.conjTranspose_apply, (hLi b a).1 hba],
        fun a => by simp [Matrix.conjTranspose_apply, (hLi a a).2 rfl]⟩
    have hA'u := tw_upUni hUi
    have hA' : Uni (Formalism.MainNotions.BridgeLemma₂.rows_tw U⁻¹) := ⟨fun a b hba => (hA'u a b).1 hba, fun a => (hA'u a a).2 rfl⟩
    obtain ⟨F00, h00⟩ := (GlobalTheory.T.unitriangularChange_rationalFlag_iff_rationalUnipotent D F hT).1 _ hA
    obtain ⟨F'0, h'0⟩ := (GlobalTheory.T.unitriangularChange_rationalFlag_iff_rationalUnipotent D F₁ hT').1 _ hA'
    refine ⟨F00, F'0, ⟨_, hA, h00⟩, ⟨_, hA', h'0⟩, ?_⟩
    rw [zhatL_chg h00 h'0, Formalism.MainNotions.BridgeLemma₂.rows_ZhatOM_mul, hZ, tw_tw, Matrix.conjTranspose_conjTranspose]
    calc L⁻¹ * (L * ptMat w * U) * U⁻¹ = (L⁻¹ * L) * ptMat w * (U * U⁻¹) := by simp only [Matrix.mul_assoc]
      _ = ptMat w := by rw [hLL, hUU, Matrix.one_mul, Matrix.mul_one]
  · rintro F₂ F₃ ⟨A, hA, h2⟩ ⟨A', hA', h3⟩
    have hZ2 := zhatL_chg h2 h3
    constructor
    · have hAl : IsLoUni A.conjTranspose := fun i j =>
        ⟨fun hij => by simp [Matrix.conjTranspose_apply, hA.1 j i hij],
          fun hij => by subst hij; simp [Matrix.conjTranspose_apply, hA.2 i]⟩
      have hAu : IsUpUni A' := fun i j => ⟨fun hij => hA'.1 i j hij, fun hij => by subst hij; exact hA'.2 i⟩
      refine ⟨A.conjTranspose * L, U * Formalism.MainNotions.BridgeLemma₂.rows_tw A', Formalism.MainNotions.BridgeLemma₂.rows_loUni_mul hAl hL,
        Formalism.MainNotions.BridgeLemma₂.rows_upUni_mul hU (tw_upUni hAu), ?_⟩
      rw [hZ2, Formalism.MainNotions.BridgeLemma₂.rows_ZhatOM_mul, hZ]
      simp only [Matrix.mul_assoc]
    · show Gflag F₂.fl F₃.fl = Gflag F.fl F₁.fl
      have hD : ∀ l, Dl F₂.fl F₃.fl l = Dl F.fl F₁.fl l := fun l => by
        show leadMinorE (ZhatL F₂ F₃) l = leadMinorE (ZhatL F F₁) l
        rw [hZ2]; exact zhatL_leadMinor F F₁ hA hA' l
      unfold Gflag
      rw [hD, hD]

end GlobalTheory.LocOver
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitriangularFramesGramEqCellPointStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitriangular_frames_gram_eq_cell_point : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ : LFlag (D.sp.Y 0) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)), T ≠ 0 → T' ≠ 0 → IsInCell (ZhatOM (ZhatL F F₁)) w → (∃ (F00 : LFlag (D.sp.Y 0) D.R.rS T) (F'0 : LFlag (D.sp.Y 0) D.R.rS T'), Tri D.host.E (frame F) (frame F00) ∧ Tri D.host.E (frame F₁) (frame F'0) ∧ ZhatOM (ZhatL F00 F'0) = ptMat w) ∧ ∀ (F₂ : LFlag (D.sp.Y 0) D.R.rS T) (F₃ : LFlag (D.sp.Y 0) D.R.rS T'), Tri D.host.E (frame F) (frame F₂) → Tri D.host.E (frame F₁) (frame F₃) → IsInCell (ZhatOM (ZhatL F₂ F₃)) w ∧ Gval F₂ F₃ = Gval F F₁ := by
  first | exact @GlobalTheory.LocOver.base_frames_at_point | exact GlobalTheory.LocOver.base_frames_at_point | (intros; apply GlobalTheory.LocOver.base_frames_at_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsMeanBoundOfGenusMean
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsMeanBoundOfGenusMean
noncomputable section
open scoped Classical ENNReal
open NumberField Formalism.HermitianLatticesTheory GlobalTheory.Mass

namespace GlobalTheory.RowsMean

section General
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem sameGenus_trans (h : V →ₗ⋆[K] V →ₗ[K] K) {L M N : Submodule (𝓞 K) V}
    (h1 : SameGenus h L M) (h2 : SameGenus h M N) : SameGenus h L N := by
  intro p hp
  obtain ⟨g₁, hg₁, e₁⟩ := h1 p hp
  obtain ⟨g₂, hg₂, e₂⟩ := h2 p hp
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_⟩
  rw [genusBasic_gmap_mul, e₁, e₂]

theorem sameGenus_refl (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : SameGenus h L L :=
  fun _ _ => ⟨1, one_mem _, genusBasic_gmap_one _⟩

theorem genus_eq_iff (h : V →ₗ⋆[K] V →ₗ[K] K) {L M : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hM : Submodule.IsFullLattice K M) :
    genus h L = genus h M ↔ L ∈ genus h M := by
  constructor
  · intro e; rw [← e]; exact ⟨hL, sameGenus_refl h L⟩
  · intro hLM
    ext N
    constructor
    · rintro ⟨hN, hs⟩
      exact ⟨hN, sameGenus_trans h hLM.2 hs⟩
    · rintro ⟨hN, hs⟩
      exact ⟨hN, sameGenus_trans h (genusBasic_symm h _ _ hLM.2) hs⟩

theorem mass_nonneg (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : 0 ≤ mass h L := by
  unfold mass
  split_ifs
  · exact Finset.sum_nonneg fun _ _ => by positivity
  · exact le_rfl

end General
end GlobalTheory.RowsMean

namespace GlobalTheory.RowsMean
section General
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem inv_card_eq (X : Type) [Nonempty X] :
    ((ENat.card X : ℕ∞) : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((Nat.card X : ℝ))⁻¹ := by
  rcases finite_or_infinite X with hX | hX
  · rw [ENat.card_eq_coe_natCard]
    have hp : 0 < Nat.card X := Nat.card_pos
    rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hp), ENNReal.ofReal_natCast]
    simp
  · rw [ENat.card_eq_top_of_infinite, Nat.card_eq_zero_of_infinite]
    simp

def stabEquiv (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V) :
    MulAction.stabilizer (isom h) M ≃ Formalism.ThetaLiftIndependence.autL h M where
  toFun g := ⟨g.1.1, g.1.2, g.2⟩
  invFun a := ⟨⟨a.1, a.2.1⟩, a.2.2⟩
  left_inv g := rfl
  right_inv a := rfl

theorem mass_le_orbMass (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) :
    ENNReal.ofReal (mass h L) ≤ orbMass (isom h) (genus h L) := by
  unfold mass
  split_ifs with hs
  swap
  · simp
  have hs' : Formalism.ThetaLiftIndependence.IsClassReps h L hs.choose := hs.choose_spec
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  have hrel : ∀ M : Submodule (𝓞 K) V, MulAction.orbitRel (isom h) (Submodule (𝓞 K) V)
      (Quotient.out (Quotient.mk'' M : MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V))) M :=
    fun M => Quotient.exact' (Quotient.out_eq' _)
  have hq : ∀ M ∈ hs.choose, Quotient.out (Quotient.mk'' M :
      MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V)) ∈ genus h L := by
    intro M hM
    obtain ⟨g, hg⟩ := hrel M
    rw [← hg]
    exact GlobalTheory.Mass.Transp.genus_stable L g M (hs'.1 M hM)
  let qm : hs.choose → {q : MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V) //
      Quotient.out q ∈ genus h L} := fun M => ⟨Quotient.mk'' M.1, hq M.1 M.2⟩
  have hinj : Function.Injective qm := by
    rintro ⟨M₁, h₁⟩ ⟨M₂, h₂⟩ e
    have e' : (Quotient.mk'' M₁ : MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V)) =
        Quotient.mk'' M₂ := congrArg Subtype.val e
    obtain ⟨g, hg⟩ := Quotient.exact' e'
    have hM₁ : M₁ ∈ genus h L := hs'.1 M₁ h₁
    have u := (hs'.2 M₁ hM₁).unique ⟨h₁, 1, one_mem _, genusBasic_gmap_one _⟩ ⟨h₂, g.1, g.2, hg⟩
    exact Subtype.ext u
  unfold orbMass orbSum
  rw [← Finset.sum_attach]
  have hterm : ∀ M : hs.choose, ENNReal.ofReal (((Nat.card (Formalism.ThetaLiftIndependence.autL h M.1) : ℕ) : ℝ))⁻¹ =
      ((ENat.card (MulAction.stabilizer (isom h) (Quotient.out (qm M).1)) : ℕ∞) : ℝ≥0∞)⁻¹ * 1 := by
    intro M
    rw [mul_one]
    have e1 : ENat.card (MulAction.stabilizer (isom h) (Quotient.out (qm M).1)) =
        ENat.card (Formalism.ThetaLiftIndependence.autL h M.1) :=
      ENat.card_congr (((MulAction.stabilizerEquivStabilizerOfOrbitRel (hrel M.1)).toEquiv).trans
        (stabEquiv h M.1))
    haveI : Nonempty (Formalism.ThetaLiftIndependence.autL h M.1) := ⟨stabEquiv h M.1 1⟩
    rw [e1, inv_card_eq]
  simp_rw [hterm]
  exact (Finset.sum_image (s := hs.choose.attach) (g := qm)
    (f := fun q : {q : MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V) // Quotient.out q ∈ genus h L} =>
      ((ENat.card (MulAction.stabilizer (isom h) (Quotient.out q.1)) : ℕ∞) : ℝ≥0∞)⁻¹ * 1)
    (fun a _ b _ e => hinj e)).symm.le.trans (ENNReal.sum_le_tsum _)

end General
end GlobalTheory.RowsMean

namespace GlobalTheory.RowsMean

theorem sum_le_of_classes {ι α : Type} (s : Finset ι) (L : ι → α) (G : α → Set α) (P : α → Prop)
    (hP : ∀ i ∈ s, P (L i)) (hG : ∀ a b, P a → P b → (G a = G b ↔ a ∈ G b))
    (F w : ι → ℝ≥0∞) (b : ℝ≥0∞)
    (hcl : ∀ i₀ ∈ s, ∑ i ∈ s.filter (fun i => L i ∈ G (L i₀)), F i ≤
      (∑ i ∈ s.filter (fun i => L i ∈ G (L i₀)), w i) * b) :
    ∑ i ∈ s, F i ≤ (∑ i ∈ s, w i) * b := by
  have hmap : ∀ i ∈ s, G (L i) ∈ s.image (fun i => G (L i)) := fun i hi => Finset.mem_image_of_mem _ hi
  rw [← Finset.sum_fiberwise_of_maps_to hmap F, ← Finset.sum_fiberwise_of_maps_to hmap w, Finset.sum_mul]
  refine Finset.sum_le_sum fun y hy => ?_
  obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hy
  have e : s.filter (fun i => G (L i) = G (L i₀)) = s.filter (fun i => L i ∈ G (L i₀)) :=
    Finset.filter_congr fun i hi => hG _ _ (hP i hi) (hP i₀ hi₀)
  rw [e]
  exact hcl i₀ hi₀

end GlobalTheory.RowsMean

namespace GlobalTheory.TypeAsm
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rowsMean : RowsMeanC := by
  intro D large₂ X Y u hStd W HW hEmb φ B hB hφ hbd
  have hOrb := GlobalTheory.T.rowsGenus_weightedSumComparison D large₂ X Y u hStd W HW hEmb
  have hLat := GlobalTheory.T.base_lattice_construction_holds D large₂ X Y u hStd W HW hEmb
  have hw : ∀ Λ, 0 ≤ wRow D (X.Fu u) Λ := fun Λ => by unfold wRow; positivity
  have hm : 0 ≤ massRows D (X.Fu u) (Y.what₂ u) := Finset.sum_nonneg fun Λ _ => hw Λ
  rw [ENNReal.ofReal_mul hm]
  unfold massRows
  rw [ENNReal.ofReal_sum_of_nonneg fun Λ _ => hw Λ]
  refine GlobalTheory.RowsMean.sum_le_of_classes (Y.what₂ u) (fun Λ => GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ)
    (Formalism.HermitianLatticesTheory.genus HW.B.flip) (Submodule.IsFullLattice D.host.E) (fun Λ hΛ => (hLat Λ hΛ).1.1)
    (fun a b ha hb => GlobalTheory.RowsMean.genus_eq_iff _ ha hb) _ _ _ ?_
  intro Λ₀ hΛ₀
  have h1 := hOrb φ hφ Λ₀ hΛ₀
  have h2 := hOrb (fun _ => 1) (fun _ _ => rfl) Λ₀ hΛ₀
  simp only [mul_one] at h2
  rw [h1, h2, mul_assoc]
  gcongr
  refine (hbd Λ₀ hΛ₀).trans ?_
  rw [ENNReal.ofReal_mul (GlobalTheory.RowsMean.mass_nonneg _ _)]
  gcongr
  exact GlobalTheory.RowsMean.mass_le_orbMass _ _

end GlobalTheory.TypeAsm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsMeanBoundOfGenusMeanStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowsMeanC_holds : GlobalTheory.TypeAsm.RowsMeanC := by
  first | exact @GlobalTheory.TypeAsm.rowsMean | exact GlobalTheory.TypeAsm.rowsMean | (intros; apply GlobalTheory.TypeAsm.rowsMean <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatEqOfIndep
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.CovDict

open Formalism.L2.SG.Pf.VolPinAsm

section Gen

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {m : ℕ}

theorem sum_smul_sum (e : Fin m → V) (P Q : Matrix (Fin m) (Fin m) K) (b : Fin m) :
    ∑ a, P a b • ∑ c, Q c a • e c = ∑ c, (Q * P) c b • e c := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]

theorem fm_conj {e f : Fin m → V} (ψ τ : V ≃ₗ[K] V) {P B : Matrix (Fin m) (Fin m) K} (hP : IsUnit P.det)
    (hψ : ∀ b, ψ (e b) = ∑ a, P a b • f a) (hτ : FM f τ B) :
    FM e (fun y => ψ.symm (τ (ψ y))) (P⁻¹ * B * P) := by
  intro b
  have hτ' : ∀ a, τ (f a) = ∑ c, B c a • f c := hτ
  apply ψ.injective
  show ψ (ψ.symm (τ (ψ (e b)))) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearEquiv.apply_symm_apply, hψ b, map_sum]
  simp only [map_smul, hτ']
  set_option synthInstance.maxHeartbeats 100000 in
    rw [sum_smul_sum, map_sum]
  simp only [map_smul, hψ]
  rw [sum_smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mul_assoc P⁻¹ B P, Matrix.mul_nonsing_inv_cancel_left _ _ hP]

theorem mat_eq_of_indep {e : Fin m → V} (he : LinearIndependent K e) (y : Fin m → V)
    {M M' : Matrix (Fin m) (Fin m) K} (h1 : ∀ b, y b = ∑ a, M a b • e a) (h2 : ∀ b, y b = ∑ a, M' a b • e a) :
    M = M' := by
  ext c b
  have h0 : ∑ i, (M i b - M' i b) • e i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← h1 b, ← h2 b, sub_self]
  exact sub_eq_zero.1 ((Fintype.linearIndependent_iff.1 he) _ h0 c)

end Gen

end GlobalTheory.HL.CovDict

namespace GlobalTheory.HL.CovDict

open Formalism.L2.SG.Pf.VolPinAsm Formalism.L2.SG.Pf.StabilizerIndexVolumes Matrix

theorem dict_coords : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → ∀ (γw s s' : X.B.I.Ginf), Formalism.L2.SG.RealObj.IsPtRep X u u' w γw → s ∈ X.SinfU u → s' ∈ X.SinfU u' → t₀.pt.1 = s * γw * s'⁻¹ → ∃ σ : Formalism.L2.SG.RealObj.FreeE w → ℂ, (∀ p, ‖σ p‖ = (D.host.rdE : ℝ) ^ (p.1.2.val - p.1.1.val)) ∧ ∃ A : InfinitePlace X.B.I.F → (Formalism.L2.SG.RealObj.FreeE w → ℂ) →ₗ[ℂ] (Formalism.L2.SG.RealObj.FreeE w → ℂ), (∀ v x x' p, (∀ q : Formalism.L2.SG.RealObj.FreeE w, q.1.2.val - q.1.1.val < p.1.2.val - p.1.1.val → x q = x' q) → A v x p - x p = A v x' p - x' p) ∧ ∀ (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X x n → c.grp ρ n ∈ G.K0 → ∀ v, Formalism.L2.SG.RealObj.stCoord X u' w γw (s⁻¹ * x.1 * s) v = A v (fun p => σ p * Formalism.L2.SG.Pf.VolPinAsm.phiV X v (GlobalTheory.HL.TraceConjugationCover.stMat G (c.grp ρ n) p.1.1 p.1.2)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv _ γw s s' _ _ hs' hpt
  obtain ⟨-, -, hU', -, hρ'⟩ := hMv
  have hrd : (0 : ℝ) < D.host.rdE := (Formalism.BasicNotions.rdE_pos_le D).1
  have hrdc : (D.host.rdE : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hrd.ne'
  have hU'u : IsUnit U'.det := by rw [up_det hU']; exact isUnit_one
  choose S hSU hS using fun v => inS_frame (hs' v)
  have hSu : ∀ v, IsUnit (S v).det := fun v => by rw [up_det (hSU v)]; exact isUnit_one
  set N : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun v =>
    U'.map (phiV X v) * S v with hN
  have hNU : ∀ v, IsUpUni (N v) := fun v => up_mul (upUni_map (phiV X v) hU') (hSU v)
  have hNu : ∀ v, IsUnit (N v).det := fun v => by rw [up_det (hNU v)]; exact isUnit_one
  refine ⟨fun p => (D.host.rdE : ℂ) ^ (p.1.2.1 - p.1.1.1), fun p => ?_,
    fun v => Alin w (D.host.rdE : ℂ) (N v), fun v x x' p hxx => Alin_shear w _ (hNU v) hrdc x x' p hxx, ?_⟩
  · rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hrd.le]
  intro x n hxn hK v
  funext p

  have hStm : c.grp ρ n ∈ G.St := fun q => by
    obtain ⟨g', hg', he⟩ := hK q
    exact ⟨g', hg'.1.1, he⟩
  obtain ⟨B, hBU, hBf, hBblk⟩ :=
    (GlobalTheory.T.rationalCommonStabiliser_unitriangular_coords D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c).1 _ hStm
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u').A.T_prime.ne_zero
  have hli : LinearIndependent D.host.E G.f' := by
    have e : G.f' = fun a => c.e (frame F'0 a) := funext c.f'_eq
    rw [e]
    exact (Formalism.L2.SG.Pf.TupLift.frame_li F'0 hT').map' _ (LinearEquiv.ker _)
  have hB : GlobalTheory.HL.TraceConjugationCover.stMat G (c.grp ρ n) = B :=
    mat_eq_of_indep hli _ (GlobalTheory.HL.TraceConjugationCover.stMat_spec G _ ⟨B, hBf⟩) hBf
  rw [hB]

  set τ : (VS D).V ≃ₗ[D.host.E] (VS D).V := ρ.symm.trans (n.trans ρ) with hτdef
  have hτ : FM (frame F'0) τ B := by
    intro b
    apply c.e.injective
    have e1 : c.e (τ (frame F'0 b)) = c.grp ρ n (G.f' b) := by
      rw [c.f'_eq]; simp [GCoord.grp, τ]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, hBf b, map_sum]
    simp only [map_smul, c.f'_eq]
  set ψ : (VS D).V ≃ₗ[D.host.E] (VS D).V := t₀.lin.trans ρ with hψdef
  have hψ : ∀ b, ψ ((X.Fu u').fvec b) = ∑ a, U' a b • frame F'0 a := by
    intro b
    show ρ (t₀.lin _) = _
    rw [← Formalism.L2.SG.Pf.FibreCounting.frame_apply]
    exact hρ' b
  have hFMm := fm_conj ψ τ hU'u hψ hτ
  have hFMm' : FM (X.Fu u').fvec (t₀.lin⁻¹ * n * t₀.lin) (U'⁻¹ * B * U') := by
    intro b
    rw [← hFMm b]
    show t₀.lin.symm (n (t₀.lin _)) = _
    simp [ψ, τ]
  have hγx : RatLink X t₀.pt t₀.lin := t₀.rep.2.1
  set zz := t₀.pt⁻¹ * x * t₀.pt with hzz
  have hzL : RatLink X zz (t₀.lin⁻¹ * n * t₀.lin) :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X
      (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hγx) hxn) hγx
  have hgrp : γw⁻¹ * (s⁻¹ * x.1 * s) * γw = s'⁻¹ * zz.1 * s' := by
    have e1 : zz.1 = t₀.pt.1⁻¹ * x.1 * t₀.pt.1 := by simp only [hzz, Prod.fst_mul, Prod.fst_inv]
    have e2 : γw = s⁻¹ * t₀.pt.1 * s' := by rw [hpt]; group
    rw [e1, e2]; group
  have hmi : ∀ a : Formalism.REAL.UJ (X.B.I.ε v), Formalism.MainNotions.S.uMat a * Formalism.MainNotions.S.uMat a⁻¹ = 1 := by
    intro a
    show _ * (((a⁻¹ : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  have hu : Formalism.MainNotions.S.uMat ((s'⁻¹ * zz.1 * s') v) =
      (Formalism.MainNotions.S.uMat (s' v))⁻¹ * Formalism.MainNotions.S.uMat (zz.1 v) * Formalism.MainNotions.S.uMat (s' v) := by
    have hi : Formalism.MainNotions.S.uMat ((s' v)⁻¹) = (Formalism.MainNotions.S.uMat (s' v))⁻¹ :=
      (Matrix.inv_eq_right_inv (hmi (s' v))).symm
    show Formalism.MainNotions.S.uMat ((s' v)⁻¹ * zz.1 v * s' v) = _
    show Formalism.MainNotions.S.uMat ((s' v)⁻¹) * Formalism.MainNotions.S.uMat (zz.1 v) * Formalism.MainNotions.S.uMat (s' v) = _
    rw [hi]
  have hs'u : IsUnit (Formalism.MainNotions.S.uMat (s' v)).det := by
    have := congrArg Matrix.det (hmi (s' v))
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one this)
  have hFM : FM (efr X u' v) (fun y => ((Formalism.MainNotions.S.uMat (s' v))⁻¹ * Formalism.MainNotions.S.uMat (zz.1 v) *
      Formalism.MainNotions.S.uMat (s' v)) *ᵥ y) ((S v)⁻¹ * (U'⁻¹ * B * U').map (phiV X v) * S v) :=
    FMm_mul (FMm_mul (FMm_inv hs'u (hS v) (hSu v)) (realFM X hzL hFMm' v)) (hS v)
  have hG : (S v)⁻¹ * (U'⁻¹ * B * U').map (phiV X v) * S v = (N v)⁻¹ * B.map (phiV X v) * N v := by
    have hinv : (U'.map (phiV X v))⁻¹ = (U'⁻¹).map (phiV X v) :=
      Matrix.inv_eq_left_inv (map_inv_mul (phiV X v) hU'u)
    rw [show N v = U'.map (phiV X v) * S v from rfl, Matrix.mul_inv_rev, hinv, Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  have hY : Yhat w (D.host.rdE : ℂ) (fun q => (D.host.rdE : ℂ) ^ (q.1.2.1 - q.1.1.1) *
      phiV X v (B q.1.1 q.1.2)) = B.map (phiV X v) - 1 := by
    ext c' d
    rw [Matrix.sub_apply, Matrix.map_apply]
    simp only [Yhat]
    split_ifs with hcd
    · rw [Matrix.one_apply_ne (ne_of_lt hcd.1), sub_zero]
      field_simp
    · by_cases hlt : c' < d
      · rw [hBblk c' d (fun he => hcd ⟨hlt, he⟩), map_zero, Matrix.one_apply_ne (ne_of_lt hlt), sub_zero]
      · rcases lt_or_eq_of_le (not_lt.1 hlt) with hgt | heq
        · rw [(hBU c' d).1 hgt, map_zero, Matrix.one_apply_ne (ne_of_gt hgt), sub_zero]
        · rw [heq, (hBU c' c').2 rfl, map_one, Matrix.one_apply_eq, sub_self]
  have hab : p.1.1 < p.1.2 := p.2.1
  have har : p.1.1.1 < D.R.rS := lt_of_lt_of_le hab (Nat.lt_succ_iff.1 p.1.2.2)
  show Formalism.L2.SG.RealObj.stCoord X u' w γw _ v p = Alin w (D.host.rdE : ℂ) (N v) _ p
  unfold Formalism.L2.SG.RealObj.stCoord
  rw [hgrp, hu, Alin_apply, hY]
  have hfrm : Formalism.L2.SG.RealObj.frm X u' D.host.rdE v p.1.2 =
      (((D.host.rdE : ℂ)) ^ (D.R.rS - p.1.2.1))⁻¹ • efr X u' v p.1.2 := rfl
  rw [hfrm, coef_efr X u' v hFM ⟨p.1.1.1, har⟩ p.1.2, hG]
  have hcs : (Fin.castSucc (⟨p.1.1.1, har⟩ : Fin D.R.rS)) = p.1.1 := Fin.ext rfl
  rw [hcs, conj_off (hNu v) (ne_of_lt hab)]
  have hpow : (D.host.rdE : ℂ) ^ (D.R.rS - p.1.1.1) =
      (D.host.rdE : ℂ) ^ (D.R.rS - p.1.2.1) * (D.host.rdE : ℂ) ^ (p.1.2.1 - p.1.1.1) := by
    rw [← pow_add]; congr 1
    have : (p.1.2 : ℕ) ≤ D.R.rS := Nat.lt_succ_iff.1 p.1.2.2
    have : (p.1.1 : ℕ) < p.1.2 := hab
    omega
  rw [hpow]
  field_simp

end GlobalTheory.HL.CovDict
end
end

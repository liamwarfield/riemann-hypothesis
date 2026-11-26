module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksDefs
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.EventuallySatV
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgE
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgD
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgC
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgB
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgA
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

theorem h2 (r s : ℕ) : ∑ i, (![r, s] : Fin 2 → ℕ) i = r + s := CapFactor.two_sum _

def sl0 (m₂ : GA E s) : Sm E (r + s) →ₗ[ℂ] Sm E r :=
  GlobalTheory.BlockCap.restrLin (stdBlocks ![r, s] (h2 r s)) (CapFactor.levPair (1, m₂)) 0

def sl1 (m₁ : GA E r) : Sm E (r + s) →ₗ[ℂ] Sm E s :=
  GlobalTheory.BlockCap.restrLin (stdBlocks ![r, s] (h2 r s)) (CapFactor.levPair (m₁, 1)) 1

theorem update0 (m₁ : GA E r) (m₂ : GA E s) :
    Function.update (CapFactor.levPair (n := ![r, s]) (1, m₂)) 0 m₁ = CapFactor.levPair (m₁, m₂) := by
  funext i
  fin_cases i <;> rfl

theorem update1 (m₁ : GA E r) (m₂ : GA E s) :
    Function.update (CapFactor.levPair (n := ![r, s]) (m₁, 1)) 1 m₂ = CapFactor.levPair (m₁, m₂) := by
  funext i
  fin_cases i <;> rfl

theorem left_slice_apply (m₂ : GA E s) (F : Sm E (r + s)) (m₁ : GA E r) :
    (sl0 m₂ F).1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂)) := by
  show F.1 (leviEmb (Ad E) (stdBlocks ![r, s] (h2 r s))
    (Function.update (CapFactor.levPair (n := ![r, s]) (1, m₂)) 0 m₁)) = _
  rw [update0]
  exact congrArg F.1 (CapFactor.lev_eq_leviEmb (R := Ad E) ![r, s] (h2 r s) (m₁, m₂)).symm

theorem right_slice_apply (m₁ : GA E r) (F : Sm E (r + s)) (m₂ : GA E s) :
    (sl1 m₁ F).1 m₂ = F.1 (lev (Ad E) r s (m₁, m₂)) := by
  show F.1 (leviEmb (Ad E) (stdBlocks ![r, s] (h2 r s))
    (Function.update (CapFactor.levPair (n := ![r, s]) (m₁, 1)) 1 m₂)) = _
  rw [update1]
  exact congrArg F.1 (CapFactor.lev_eq_leviEmb (R := Ad E) ![r, s] (h2 r s) (m₁, m₂)).symm

theorem yp_one {a : ℕ} : BlockDerivatives.yp (1 : Kinf E a) (1 : GL (Fin a) (Af E)) = 1 := by
  simp [BlockDerivatives.yp]

abbrev e2 (r s : ℕ) := stdBlocks ![r, s] (h2 r s)

theorem left_slice_lie_first_block (m₂ : GA E s) (Y : Lie E r) (F : Sm E (r + s)) :
    sl0 m₂ (lie E (r + s) (GlobalTheory.BlockCap.blockCLM (e2 r s) 0 Y) F) = lie E r Y (sl0 m₂ F) :=
  LinearMap.congr_fun (GlobalTheory.BlockCap.restrLin_lie (e2 r s) (CapFactor.levPair (1, m₂)) 0 Y) F

theorem right_slice_lie_second_block (m₁ : GA E r) (Y : Lie E s) (F : Sm E (r + s)) :
    sl1 m₁ (lie E (r + s) (GlobalTheory.BlockCap.blockCLM (e2 r s) 1 Y) F) = lie E s Y (sl1 m₁ F) :=
  LinearMap.congr_fun (GlobalTheory.BlockCap.restrLin_lie (e2 r s) (CapFactor.levPair (m₁, 1)) 1 Y) F

theorem std0 (p : Fin r) : (e2 r s) ⟨0, p⟩ = Fin.castAdd s p := CapFactor.std_zero ![r, s] (h2 r s) p

theorem std1 (q : Fin s) : (e2 r s) ⟨1, q⟩ = Fin.natAdd r q := CapFactor.std_one ![r, s] (h2 r s) q

theorem lev_eq (m : GA E r × GA E s) : lev (Ad E) r s m = leviEmb (Ad E) (e2 r s) (CapFactor.levPair m) :=
  CapFactor.lev_eq_leviEmb ![r, s] (h2 r s) m

theorem toL_single_cc (p q : Fin r) (x : Cinf E) :
    (toL (Matrix.single (Fin.castAdd s p) (Fin.castAdd s q) x) : Lie E (r + s)) =
      GlobalTheory.BlockCap.blockCLM (e2 r s) 0 (toL (Matrix.single p q x)) := by
  have h := GlobalTheory.BlockCap.blockLin_single (E := E) (e2 r s) 0 p q x
  rw [std0, std0] at h
  exact h.symm

theorem toL_single_nn (p q : Fin s) (x : Cinf E) :
    (toL (Matrix.single (Fin.natAdd r p) (Fin.natAdd r q) x) : Lie E (r + s)) =
      GlobalTheory.BlockCap.blockCLM (e2 r s) 1 (toL (Matrix.single p q x)) := by
  have h := GlobalTheory.BlockCap.blockLin_single (E := E) (e2 r s) 1 p q x
  rw [std1, std1] at h
  exact h.symm

theorem unipRad_inv (F : Sm E (r + s)) (hF : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g) :
    ∀ u ∈ unipRad (Ad E) (e2 r s), ∀ g, F.1 (u * g) = F.1 g := fun u hu g => by
  obtain ⟨x, rfl⟩ := CapFactor.exists_unip_of_mem ![r, s] (h2 r s) hu
  exact hF x g

theorem lie_upper_lev (F : Sm E (r + s)) (hF : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (p : Fin r) (q : Fin s) (x : Cinf E) (m : GA E r × GA E s) :
    (lie E (r + s) (toL (Matrix.single (Fin.castAdd s p) (Fin.natAdd r q) x)) F).1 (lev (Ad E) r s m) = 0 := by
  have hpq : blk (e2 r s) (Fin.castAdd s p) < blk (e2 r s) (Fin.natAdd r q) := by
    have b0 : blk (e2 r s) ((e2 r s) ⟨0, p⟩) = 0 := blk_apply (e2 r s) 0 p
    have b1 : blk (e2 r s) ((e2 r s) ⟨1, q⟩) = 1 := blk_apply (e2 r s) 1 q
    rw [std0] at b0
    rw [std1] at b1
    rw [b0, b1]
    decide
  have := GlobalTheory.UnipZero.lieD_single_leviEmb_eq_zero E ![r, s] (e2 r s) F (unipRad_inv F hF) _ _ hpq x
    (CapFactor.levPair m)
  rw [lev_eq]
  exact this

theorem lie_sum_single (X : Lie E (r + s)) (F : Sm E (r + s)) :
    lie E (r + s) X F = ∑ p, ∑ q, lie E (r + s) (toL (Matrix.single p q (X p q))) F := by
  have hdec : X = ∑ p, ∑ q, (toL (Matrix.single p q (X p q)) : Lie E (r + s)) :=
    Matrix.matrix_eq_sum_single (Matrix.of X)
  conv_lhs => rw [hdec]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply]

theorem right_slice_eq_sum (F : Sm E (r + s)) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2) (m₁ : GA E r) :
    sl1 m₁ F = ∑ i, (b i).1 m₁ • q i := by
  refine Subtype.ext (funext fun m₂ => ?_)
  rw [right_slice_apply, hexp (m₁, m₂), Submodule.coe_sum, Finset.sum_apply]
  rfl

theorem left_slice_eq_sum (F : Sm E (r + s)) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2) (m₂ : GA E s) :
    sl0 m₂ F = ∑ i, (q i).1 m₂ • b i := by
  refine Subtype.ext (funext fun m₁ => ?_)
  rw [left_slice_apply, hexp (m₁, m₂), Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  change _ = (q i).1 m₂ * (b i).1 m₁
  ring

theorem left_slice_lie_second_block (F : Sm E (r + s)) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2) (Y : Lie E s)
    (m₂ : GA E s) :
    sl0 m₂ (lie E (r + s) (GlobalTheory.BlockCap.blockCLM (e2 r s) 1 Y) F) = ∑ i, (lie E s Y (q i)).1 m₂ • b i := by
  refine Subtype.ext (funext fun m₁ => ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [left_slice_apply, ← right_slice_apply, right_slice_lie_second_block, right_slice_eq_sum F b q hexp, map_sum, Submodule.coe_sum, Finset.sum_apply,
    Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  change (b i).1 m₁ * (lie E s Y (q i)).1 m₂ = (lie E s Y (q i)).1 m₂ * (b i).1 m₁
  ring

theorem right_slice_lie_first_block (F : Sm E (r + s)) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2) (Y : Lie E r)
    (m₁ : GA E r) :
    sl1 m₁ (lie E (r + s) (GlobalTheory.BlockCap.blockCLM (e2 r s) 0 Y) F) = ∑ i, (lie E r Y (b i)).1 m₁ • q i := by
  refine Subtype.ext (funext fun m₂ => ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [right_slice_apply, ← left_slice_apply, left_slice_lie_first_block, left_slice_eq_sum F b q hexp, map_sum, Submodule.coe_sum, Finset.sum_apply,
    Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  change (q i).1 m₂ * (lie E r Y (b i)).1 m₁ = (lie E r Y (b i)).1 m₁ * (q i).1 m₂
  ring

theorem left_slice_single_first (m₂ : GA E s) (p q : Fin r) (x : Cinf E) (F : Sm E (r + s)) :
    sl0 m₂ (lie E (r + s) (toL (Matrix.single (Fin.castAdd s p) (Fin.castAdd s q) x)) F) =
      lie E r (toL (Matrix.single p q x)) (sl0 m₂ F) := by
  rw [toL_single_cc]
  exact left_slice_lie_first_block m₂ _ F

theorem right_slice_single_second (m₁ : GA E r) (p q : Fin s) (x : Cinf E) (F : Sm E (r + s)) :
    sl1 m₁ (lie E (r + s) (toL (Matrix.single (Fin.natAdd r p) (Fin.natAdd r q) x)) F) =
      lie E s (toL (Matrix.single p q x)) (sl1 m₁ F) := by
  rw [toL_single_nn]
  exact right_slice_lie_second_block m₁ _ F

theorem left_slice_single_second (F : Sm E (r + s)) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2) (p p' : Fin s)
    (x : Cinf E) (m₂ : GA E s) :
    sl0 m₂ (lie E (r + s) (toL (Matrix.single (Fin.natAdd r p) (Fin.natAdd r p') x)) F) =
      ∑ i, (lie E s (toL (Matrix.single p p' x)) (q i)).1 m₂ • b i := by
  rw [toL_single_nn]
  exact left_slice_lie_second_block F b q hexp _ m₂

theorem right_slice_single_first (F : Sm E (r + s)) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2) (p p' : Fin r)
    (x : Cinf E) (m₁ : GA E r) :
    sl1 m₁ (lie E (r + s) (toL (Matrix.single (Fin.castAdd s p) (Fin.castAdd s p') x)) F) =
      ∑ i, (lie E r (toL (Matrix.single p p' x)) (b i)).1 m₁ • q i := by
  rw [toL_single_cc]
  exact right_slice_lie_first_block F b q hexp _ m₁

theorem key_left (W : Submodule ℂ (Sm E r)) (hW : _root_.GlobalTheory.CuspRep.IsStable W) (F : Sm E (r + s))
    (hu : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (hP : ∀ m₂, sl0 m₂ F ∈ W) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s) (hb : ∀ i, b i ∈ W)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2)
    (X : Lie E (r + s)) (hX : ∀ (i : Fin s) (j : Fin r), X (Fin.natAdd r i) (Fin.castAdd s j) = 0)
    (m₂ : GA E s) : sl0 m₂ (lie E (r + s) X F) ∈ W := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [lie_sum_single, map_sum]
  refine W.sum_mem fun p _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine W.sum_mem fun q' _ => ?_
  induction p using Fin.addCases with
  | left p =>
    induction q' using Fin.addCases with
    | left q' =>
      rw [left_slice_single_first]
      exact hW (.lie _) _ (hP m₂)
    | right q' =>
      have h0 : sl0 m₂ (lie E (r + s) (toL (Matrix.single (Fin.castAdd s p) (Fin.natAdd r q')
          (X (Fin.castAdd s p) (Fin.natAdd r q')))) F) = 0 :=
        Subtype.ext (funext fun m₁ => by rw [left_slice_apply]; exact lie_upper_lev F hu p q' _ (m₁, m₂))
      rw [h0]
      exact W.zero_mem
  | right p =>
    induction q' using Fin.addCases with
    | left q' =>
      rw [hX p q', Matrix.single_zero]
      have : (toL (0 : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) : Lie E (r + s)) = 0 := rfl
      rw [this, map_zero, LinearMap.zero_apply, map_zero]
      exact W.zero_mem
    | right q' =>
      rw [left_slice_single_second F b q hexp]
      exact W.sum_mem fun i _ => W.smul_mem _ (hb i)

theorem key_right (W : Submodule ℂ (Sm E s)) (hW : _root_.GlobalTheory.CuspRep.IsStable W) (F : Sm E (r + s))
    (hu : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (hP : ∀ m₁, sl1 m₁ F ∈ W) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s) (hq : ∀ i, q i ∈ W)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2)
    (X : Lie E (r + s)) (hX : ∀ (i : Fin s) (j : Fin r), X (Fin.natAdd r i) (Fin.castAdd s j) = 0)
    (m₁ : GA E r) : sl1 m₁ (lie E (r + s) X F) ∈ W := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [lie_sum_single, map_sum]
  refine W.sum_mem fun p _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine W.sum_mem fun q' _ => ?_
  induction p using Fin.addCases with
  | left p =>
    induction q' using Fin.addCases with
    | left q' =>
      rw [right_slice_single_first F b q hexp]
      exact W.sum_mem fun i _ => W.smul_mem _ (hq i)
    | right q' =>
      have h0 : sl1 m₁ (lie E (r + s) (toL (Matrix.single (Fin.castAdd s p) (Fin.natAdd r q')
          (X (Fin.castAdd s p) (Fin.natAdd r q')))) F) = 0 :=
        Subtype.ext (funext fun m₂ => by rw [right_slice_apply]; exact lie_upper_lev F hu p q' _ (m₁, m₂))
      rw [h0]
      exact W.zero_mem
  | right p =>
    induction q' using Fin.addCases with
    | left q' =>
      rw [hX p q', Matrix.single_zero]
      have : (toL (0 : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) : Lie E (r + s)) = 0 := rfl
      rw [this, map_zero, LinearMap.zero_apply, map_zero]
      exact W.zero_mem
    | right q' =>
      rw [right_slice_single_second]
      exact hW (.lie _) _ (hP m₁)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Curve

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

def ecurve {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) (t : ℝ) : Matrix (Fin N) (Fin N) (Cinf E) :=
  NormedSpace.exp (t • Z)

theorem hasDerivAt_ecurve {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) : HasDerivAt (ecurve Z) Z 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h

theorem ecurve_zero {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) : ecurve Z 0 = 1 := by
  simp [ecurve]

theorem ecurve_mem {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) (hZ : Zᴴ = -Z) (t : ℝ) :
    ecurve Z t ∈ Matrix.unitaryGroup (Fin N) (Cinf E) := by
  have hc : (t • Z)ᴴ = -(t • Z) := by
    rw [conjTranspose_smul, hZ]; simp
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ecurve, ← Matrix.exp_conjTranspose, hc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_right]
  simp

def toLclm (N : ℕ) : Matrix (Fin N) (Fin N) (Cinf E) →L[ℝ] Lie E N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => toL A, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem hasDerivAt_toL_ecurve {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) :
    HasDerivAt (fun t => (toL (ecurve Z t) : Lie E N)) (toL Z) 0 := by
  have h := ((toLclm (E := E) N).hasFDerivAt (x := ecurve Z 0)).comp_hasDerivAt (0 : ℝ) (hasDerivAt_ecurve Z)
  exact h

end Curve

def kcurve {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) (hZ : Zᴴ = -Z) (t : ℝ) : Kinf E N :=
  ⟨ecurve Z t, ecurve_mem Z hZ t⟩

theorem lie_mem_orbSpan {N : ℕ} (φ : Sm E N) [FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan φ)]
    (Z : Matrix (Fin N) (Fin N) (Cinf E)) (hZ : Zᴴ = -Z) :
    lie E N (toL Z) φ ∈ GlobalTheory.CuspRep.LocEx.orbSpan φ := by
  set A : Submodule ℂ (GA E N → ℂ) := (GlobalTheory.CuspRep.LocEx.orbSpan φ).map (Sm E N).subtype with hA
  have : FiniteDimensional ℂ A := inferInstance
  obtain ⟨S, a, ha⟩ := SliceTensor.interp A
  let c : ℝ → GL (Fin N) (Cinf E) := fun t => Unitary.toUnits (kcurve Z hZ t)
  have h0 : c 0 = 1 := Units.ext (ecurve_zero Z)
  have hc : HasDerivAt (fun t => toL (c t).val) (toL Z) 0 := hasDerivAt_toL_ecurve Z
  have hmem : ∀ t, (cptRep E N (kcurve Z hZ t) φ).1 ∈ A := fun t =>
    ⟨_, Submodule.subset_span ⟨kcurve Z hZ t, rfl⟩, rfl⟩
  have hval : ∀ t g, (cptRep E N (kcurve Z hZ t) φ).1 g = φ.1 (g * infGL E N (c t)) := fun _ _ => rfl
  have key : ∀ g, lieD (toL Z) φ.1 g = ∑ κ : S, lieD (toL Z) φ.1 κ.1 * (a κ : GA E N → ℂ) g := by
    intro g
    have e : ∀ t, φ.1 (g * infGL E N (c t)) = ∑ κ : S, φ.1 (κ.1 * infGL E N (c t)) * (a κ : GA E N → ℂ) g := by
      intro t
      have := congrFun (ha _ (hmem t)) g
      rw [hval, Finset.sum_apply] at this
      rw [this]
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, hval]
    have d1 := hasDerivAt_curve φ g c (toL Z) h0 hc
    have d2 : HasDerivAt (fun t => ∑ κ : S, φ.1 (κ.1 * infGL E N (c t)) * (a κ : GA E N → ℂ) g)
        (∑ κ : S, lieD (toL Z) φ.1 κ.1 * (a κ : GA E N → ℂ) g) 0 :=
      HasDerivAt.fun_sum fun κ _ => (hasDerivAt_curve φ κ.1 c (toL Z) h0 hc).mul_const _
    rw [show (fun t => φ.1 (g * infGL E N (c t))) = fun t =>
      ∑ κ : S, φ.1 (κ.1 * infGL E N (c t)) * (a κ : GA E N → ℂ) g from funext e] at d1
    exact d1.unique d2
  have hL : (lie E N (toL Z) φ).1 ∈ A := by
    have e : (lie E N (toL Z) φ).1 = ∑ κ : S, lieD (toL Z) φ.1 κ.1 • (a κ : GA E N → ℂ) := by
      funext g
      rw [GlobalTheory.CuspRep.lie_apply, key g, Finset.sum_apply]
      rfl
    rw [e]
    exact A.sum_mem fun κ _ => A.smul_mem _ (a κ).2
  obtain ⟨y, hy, e⟩ := hL
  have : y = lie E N (toL Z) φ := Subtype.ext e
  rw [← this]
  exact hy

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

def lowL (X : Lie E (r + s)) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E) :=
  Matrix.of fun i j => if r ≤ (i : ℕ) ∧ (j : ℕ) < r then X i j else 0

def skw (X : Lie E (r + s)) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E) := lowL X - (lowL X)ᴴ

theorem skw_skew (X : Lie E (r + s)) : (skw X)ᴴ = -skw X := by
  rw [skw, conjTranspose_sub, conjTranspose_conjTranspose, neg_sub]

theorem par_low (X : Lie E (r + s)) (i : Fin s) (j : Fin r) :
    (X - toL (skw X)) (Fin.natAdd r i) (Fin.castAdd s j) = 0 := by
  have h1 : lowL X (Fin.natAdd r i) (Fin.castAdd s j) = X (Fin.natAdd r i) (Fin.castAdd s j) := by
    simp [lowL]
  have h2 : lowL X (Fin.castAdd s j) (Fin.natAdd r i) = 0 := by
    simp [lowL]
  change X (Fin.natAdd r i) (Fin.castAdd s j) - (lowL X (Fin.natAdd r i) (Fin.castAdd s j) -
    star (lowL X (Fin.castAdd s j) (Fin.natAdd r i))) = 0
  rw [h1, h2, star_zero, sub_zero, sub_self]

theorem lie_split (X : Lie E (r + s)) (F : Sm E (r + s)) :
    lie E (r + s) X F = lie E (r + s) (X - toL (skw X)) F + lie E (r + s) (toL (skw X)) F := by
  rw [← LinearMap.add_apply, ← map_add (f := _), sub_add_cancel]

theorem yp_mul {a : ℕ} (k k' : Kinf E a) (g g' : GL (Fin a) (Af E)) :
    BlockDerivatives.yp k g * BlockDerivatives.yp k' g' = BlockDerivatives.yp (k * k') (g * g') :=
  InducedTensorMap.cf_mul a k k' g g'

theorem rt_yp_rt {a : ℕ} (k k' : Kinf E a) (g g' : GL (Fin a) (Af E)) (φ : Sm E a) :
    GlobalTheory.CuspRep.rt E a (BlockDerivatives.yp k g) (GlobalTheory.CuspRep.rt E a (BlockDerivatives.yp k' g') φ) = GlobalTheory.CuspRep.rt E a (BlockDerivatives.yp (k * k') (g * g')) φ := by
  rw [← yp_mul, map_mul, Module.End.mul_apply]

theorem act_fin_eq {a : ℕ} (h : GL (Fin a) (Af E)) (φ : Sm E a) : act (.fin h) φ = GlobalTheory.CuspRep.rt E a (BlockDerivatives.yp 1 h) φ := by
  refine Subtype.ext (funext fun x => ?_)
  simp [BlockDerivatives.yp]
  rfl

theorem act_cpt_eq {a : ℕ} (κ : Kinf E a) (φ : Sm E a) : act (.cpt κ) φ = GlobalTheory.CuspRep.rt E a (BlockDerivatives.yp κ 1) φ := by
  refine Subtype.ext (funext fun x => ?_)
  simp [BlockDerivatives.yp]
  rfl

theorem rt_lie_yp {a : ℕ} (k : Kinf E a) (g : GL (Fin a) (Af E)) (X : Lie E a) :
    ∃ X' : Lie E a, GlobalTheory.CuspRep.rt E a (BlockDerivatives.yp k g) * lie E a X = lie E a X' * GlobalTheory.CuspRep.rt E a (BlockDerivatives.yp k g) := by
  refine ⟨toL ((Unitary.toUnits k).val * Matrix.of X * ((Unitary.toUnits k)⁻¹).val), ?_⟩
  rw [BlockDerivatives.yp, map_mul, mul_assoc, ← lie_rt_fin, ← mul_assoc, ← mul_assoc]
  exact congrArg (· * _) (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) (Matrix.of X))

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

def HExp (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) : Prop :=
  ∀ ψ ∈ U, ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)), ∃ (n : ℕ) (b : Fin n → Sm E r) (q : Fin n → Sm E s),
    (∀ i, b i ∈ Submodule.span ℂ (BlockDerivatives.lsF r s (T ψ) k g)) ∧ (∀ i, q i ∈ BlockDerivatives.rsF r s (T ψ) k g) ∧
    ∀ m : GA E r × GA E s, (T ψ).1 (lev (Ad E) r s m * BlockDerivatives.yp k g) = ∑ i, (b i).1 m.1 * (q i).1 m.2

theorem lsF_yp (F : Sm E (r + s)) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    ∀ ℓ ∈ BlockDerivatives.lsF r s F k g, ∃ m₂, ℓ = sl0 m₂ (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k g) F) := by
  rintro ℓ ⟨m₂, h⟩
  exact ⟨m₂, Subtype.ext (funext fun m₁ => by rw [h, left_slice_apply, rt_apply])⟩

theorem rsF_yp (F : Sm E (r + s)) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    ∀ ℓ ∈ BlockDerivatives.rsF r s F k g, ∃ m₁, ℓ = sl1 m₁ (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k g) F) := by
  rintro ℓ ⟨m₁, h⟩
  exact ⟨m₁, Subtype.ext (funext fun m₂ => by rw [h, right_slice_apply, rt_apply])⟩

theorem rt_one {a : ℕ} (F : Sm E a) : GlobalTheory.CuspRep.rt E a (BlockDerivatives.yp 1 1) F = F := by
  rw [yp_one, map_one, Module.End.one_apply]

theorem lsF_one (F : Sm E (r + s)) : ∀ ℓ ∈ BlockDerivatives.lsF r s F 1 1, ∃ m₂, ℓ = sl0 m₂ F := by
  intro ℓ hℓ
  obtain ⟨m₂, h⟩ := lsF_yp F 1 1 ℓ hℓ
  exact ⟨m₂, by rw [h, rt_one]⟩

theorem rsF_one (F : Sm E (r + s)) : ∀ ℓ ∈ BlockDerivatives.rsF r s F 1 1, ∃ m₁, ℓ = sl1 m₁ F := by
  intro ℓ hℓ
  obtain ⟨m₁, h⟩ := rsF_yp F 1 1 ℓ hℓ
  exact ⟨m₁, by rw [h, rt_one]⟩

theorem exp_one {U : Submodule ℂ (Sm E (r + s))} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} (hexp : HExp U T)
    {ψ : Sm E (r + s)} (hψ : ψ ∈ U) :
    ∃ (n : ℕ) (b : Fin n → Sm E r) (q : Fin n → Sm E s),
      (∀ i, b i ∈ Submodule.span ℂ (BlockDerivatives.lsF r s (T ψ) 1 1)) ∧ (∀ i, q i ∈ BlockDerivatives.rsF r s (T ψ) 1 1) ∧
      ∀ m : GA E r × GA E s, (T ψ).1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2 := by
  obtain ⟨n, b, q, hb, hq, he⟩ := hexp ψ hψ 1 1
  refine ⟨n, b, q, hb, hq, fun m => ?_⟩
  rw [← he m, yp_one, mul_one]

theorem rt_yp_eq {a : ℕ} (k : Kinf E a) (g : GL (Fin a) (Af E)) (φ : Sm E a) :
    GlobalTheory.CuspRep.rt E a (BlockDerivatives.yp k g) φ = act (.cpt k) (act (.fin g) φ) := by
  rw [act_cpt_eq, act_fin_eq, rt_yp_rt, mul_one, one_mul]

theorem rt_yp_mem {a : ℕ} {U : Submodule ℂ (Sm E a)} (hU : _root_.GlobalTheory.CuspRep.IsStable U) (k : Kinf E a) (g : GL (Fin a) (Af E))
    {φ : Sm E a} (hφ : φ ∈ U) : GlobalTheory.CuspRep.rt E a (BlockDerivatives.yp k g) φ ∈ U := by
  rw [rt_yp_eq]
  exact hU _ _ (hU _ _ hφ)

theorem T_rt_yp {a : ℕ} {U : Submodule ℂ (Sm E a)} (hU : _root_.GlobalTheory.CuspRep.IsStable U) {T : Sm E a →ₗ[ℂ] Sm E a}
    (hT : ∀ o, ∀ φ ∈ U, T (act o φ) = act o (T φ)) (k : Kinf E a) (g : GL (Fin a) (Af E)) {φ : Sm E a}
    (hφ : φ ∈ U) : T (GlobalTheory.CuspRep.rt E a (BlockDerivatives.yp k g) φ) = GlobalTheory.CuspRep.rt E a (BlockDerivatives.yp k g) (T φ) := by
  rw [rt_yp_eq, rt_yp_eq, hT _ _ (hU _ _ hφ), hT _ _ hφ]

def Mleft (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) (W : Submodule ℂ (Sm E r)) :
    Submodule ℂ (Sm E (r + s)) where
  carrier := {ψ | ψ ∈ U ∧ ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₂ : GA E s),
    sl0 m₂ (T (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k g) ψ)) ∈ W}
  add_mem' := fun {a b} ha hb => ⟨U.add_mem ha.1 hb.1, fun k g m₂ => by
    rw [map_add (f := _), map_add (f := _), map_add (f := _)]; exact W.add_mem (ha.2 k g m₂) (hb.2 k g m₂)⟩
  zero_mem' := ⟨U.zero_mem, fun k g m₂ => by rw [map_zero, map_zero, map_zero]; exact W.zero_mem⟩
  smul_mem' := fun c a ha => ⟨U.smul_mem c ha.1, fun k g m₂ => by
    rw [map_smul, map_smul, map_smul]; exact W.smul_mem c (ha.2 k g m₂)⟩

def Mright (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) (W : Submodule ℂ (Sm E s)) :
    Submodule ℂ (Sm E (r + s)) where
  carrier := {ψ | ψ ∈ U ∧ ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₁ : GA E r),
    sl1 m₁ (T (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k g) ψ)) ∈ W}
  add_mem' := fun {a b} ha hb => ⟨U.add_mem ha.1 hb.1, fun k g m₁ => by
    rw [map_add (f := _), map_add (f := _), map_add (f := _)]; exact W.add_mem (ha.2 k g m₁) (hb.2 k g m₁)⟩
  zero_mem' := ⟨U.zero_mem, fun k g m₁ => by rw [map_zero, map_zero, map_zero]; exact W.zero_mem⟩
  smul_mem' := fun c a ha => ⟨U.smul_mem c ha.1, fun k g m₁ => by
    rw [map_smul, map_smul, map_smul]; exact W.smul_mem c (ha.2 k g m₁)⟩

theorem Mleft_stable {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ}
    {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} (hT : IsSliceMap U c T) (hexp : HExp U T) (W : Submodule ℂ (Sm E r))
    (hW : _root_.GlobalTheory.CuspRep.IsStable W) : _root_.GlobalTheory.CuspRep.IsStable (Mleft U T W) := by
  rintro o ψ ⟨hψU, hψ⟩
  cases o with
  | fin h =>
    refine ⟨hU.1 _ _ hψU, fun k g m₂ => ?_⟩
    rw [act_fin_eq, rt_yp_rt, mul_one]
    exact hψ k (g * h) m₂
  | cpt κ =>
    refine ⟨hU.1 _ _ hψU, fun k g m₂ => ?_⟩
    rw [act_cpt_eq, rt_yp_rt, mul_one]
    exact hψ (k * κ) g m₂
  | lie X =>
    refine ⟨hU.1 _ _ hψU, fun k g m₂ => ?_⟩
    obtain ⟨X', hX'⟩ := rt_lie_yp k g X
    have hψ'U : GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k g) ψ ∈ U := rt_yp_mem hU.1 k g hψU
    have e1 : GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k g) (act (.lie X) ψ) = lie E (r + s) X' (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k g) ψ) :=
      LinearMap.congr_fun hX' ψ
    rw [e1]
    have e2 := hT.equiv (.lie X') _ hψ'U
    change T (lie E (r + s) X' _) = lie E (r + s) X' _ at e2
    rw [e2]
    set ψ' := GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k g) ψ with hψ'
    have hP : ∀ m₂, sl0 m₂ (T ψ') ∈ W := fun m₂ => hψ k g m₂
    obtain ⟨n, b, q, hb, -, he⟩ := exp_one hexp hψ'U
    have hsub : BlockDerivatives.lsF r s (T ψ') 1 1 ⊆ W := fun ℓ hℓ => by
      obtain ⟨m, rfl⟩ := lsF_one _ ℓ hℓ
      exact hP m
    have hbW : ∀ i, b i ∈ W := fun i => (Submodule.span_le.2 hsub) (hb i)
    rw [lie_split, map_add (f := _)]
    refine W.add_mem (key_left W hW (T ψ') (hT.unipInv ψ' hψ'U) hP b q hbW he _ (par_low X') m₂) ?_
    have e3 := hT.equiv (.lie (toL (skw X'))) _ hψ'U
    change T (lie E (r + s) (toL (skw X')) ψ') = lie E (r + s) (toL (skw X')) (T ψ') at e3
    rw [← e3]
    have : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan ψ') := (hU.2 ψ' hψ'U).kfin
    have hmem := lie_mem_orbSpan ψ' (skw X') (skw_skew X')
    have hle : GlobalTheory.CuspRep.LocEx.orbSpan ψ' ≤ W.comap (sl0 m₂ ∘ₗ T) := Submodule.span_le.2 (by
      rintro _ ⟨κ, rfl⟩
      change sl0 m₂ (T (act (.cpt κ) ψ')) ∈ W
      rw [act_cpt_eq, hψ', rt_yp_rt, one_mul]
      exact hψ (κ * k) g m₂)
    exact hle hmem

theorem Mright_stable {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ}
    {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} (hT : IsSliceMap U c T) (hexp : HExp U T) (W : Submodule ℂ (Sm E s))
    (hW : _root_.GlobalTheory.CuspRep.IsStable W) : _root_.GlobalTheory.CuspRep.IsStable (Mright U T W) := by
  rintro o ψ ⟨hψU, hψ⟩
  cases o with
  | fin h =>
    refine ⟨hU.1 _ _ hψU, fun k g m₁ => ?_⟩
    rw [act_fin_eq, rt_yp_rt, mul_one]
    exact hψ k (g * h) m₁
  | cpt κ =>
    refine ⟨hU.1 _ _ hψU, fun k g m₁ => ?_⟩
    rw [act_cpt_eq, rt_yp_rt, mul_one]
    exact hψ (k * κ) g m₁
  | lie X =>
    refine ⟨hU.1 _ _ hψU, fun k g m₁ => ?_⟩
    obtain ⟨X', hX'⟩ := rt_lie_yp k g X
    have hψ'U : GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k g) ψ ∈ U := rt_yp_mem hU.1 k g hψU
    have e1 : GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k g) (act (.lie X) ψ) = lie E (r + s) X' (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k g) ψ) :=
      LinearMap.congr_fun hX' ψ
    rw [e1]
    have e2 := hT.equiv (.lie X') _ hψ'U
    change T (lie E (r + s) X' _) = lie E (r + s) X' _ at e2
    rw [e2]
    set ψ' := GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k g) ψ with hψ'
    have hP : ∀ m₁, sl1 m₁ (T ψ') ∈ W := fun m₁ => hψ k g m₁
    obtain ⟨n, b, q, -, hq, he⟩ := exp_one hexp hψ'U
    have hqW : ∀ i, q i ∈ W := fun i => by
      obtain ⟨m, hm⟩ := rsF_one _ _ (hq i)
      rw [hm]
      exact hP m
    rw [lie_split, map_add (f := _)]
    refine W.add_mem (key_right W hW (T ψ') (hT.unipInv ψ' hψ'U) hP b q hqW he _ (par_low X') m₁) ?_
    have e3 := hT.equiv (.lie (toL (skw X'))) _ hψ'U
    change T (lie E (r + s) (toL (skw X')) ψ') = lie E (r + s) (toL (skw X')) (T ψ') at e3
    rw [← e3]
    have : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan ψ') := (hU.2 ψ' hψ'U).kfin
    have hmem := lie_mem_orbSpan ψ' (skw X') (skw_skew X')
    have hle : GlobalTheory.CuspRep.LocEx.orbSpan ψ' ≤ W.comap (sl1 m₁ ∘ₗ T) := Submodule.span_le.2 (by
      rintro _ ⟨κ, rfl⟩
      change sl1 m₁ (T (act (.cpt κ) ψ')) ∈ W
      rw [act_cpt_eq, hψ', rt_yp_rt, one_mul]
      exact hψ (κ * k) g m₁)
    exact hle hmem

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

theorem collect {α β : Type} (S : Finset α) (X : Set β) (Q : α → Finset β → Prop)
    (hmono : ∀ a (F F' : Finset β), F ⊆ F' → Q a F → Q a F')
    (h : ∀ a ∈ S, ∃ F : Finset β, (↑F : Set β) ⊆ X ∧ Q a F) :
    ∃ F : Finset β, (↑F : Set β) ⊆ X ∧ ∀ a ∈ S, Q a F := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | insert a S ha ih =>
    obtain ⟨F, hF, hQ⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    obtain ⟨F', hF', hQ'⟩ := h a (Finset.mem_insert_self a S)
    refine ⟨F ∪ F', by rw [Finset.coe_union]; exact Set.union_subset hF hF', fun b hb => ?_⟩
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact hmono _ _ _ Finset.subset_union_right hQ'
    · exact hmono _ _ _ Finset.subset_union_left (hQ b hb)

theorem finGL_unip' {N k : ℕ} (x : BlockIx N k → Af E) :
    finGL E N (unip x) = unip (fun p => sFin E (x p)) := by
  apply Units.ext
  change 1 - (1 : Matrix (Fin N) (Fin N) (Af E)).map (sFin E) + (1 + nilM x).map (sFin E) = 1 + nilM _
  rw [Matrix.map_add _ (map_add (sFin E))]
  have : (nilM x).map (sFin E) = nilM (r := k) (fun p => sFin E (x p)) := by
    ext i j
    simp only [nilM, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  rw [this]; abel

theorem cover (L : Subgroup (GL (Fin (r + s)) (Af E))) (hL : IsOpen (L : Set (GL (Fin (r + s)) (Af E)))) :
    ∃ Tf : Finset (GL (Fin (r + s)) (Af E)), ∀ g : GL (Fin (r + s)) (Af E),
      ∃ (x : BlockIx (r + s) r → Af E) (a : GL (Fin r) (Af E)) (b : GL (Fin s) (Af E)) (t l : GL (Fin (r + s)) (Af E)),
        t ∈ Tf ∧ l ∈ L ∧ g = unip x * lev (Af E) r s (a, b) * t * l := by
  obtain ⟨Tf, hTf⟩ := IwaAd.exists_finset_cover E (r + s) L hL
  refine ⟨Tf, fun g => ?_⟩
  obtain ⟨x, m, c, hc, rfl⟩ := IwaFin.exists_unip_lev_integral E r s g
  obtain ⟨t, ht, l, hl, rfl⟩ := hTf c hc
  exact ⟨x, m.1, m.2, t, l, ht, hl, by rw [← mul_assoc]⟩

theorem yp_decomp (k : Kinf E (r + s)) (x : BlockIx (r + s) r → Af E) (a : GL (Fin r) (Af E))
    (b : GL (Fin s) (Af E)) (t l : GL (Fin (r + s)) (Af E)) :
    BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l) =
      unip (fun p => sFin E (x p)) * lev (Ad E) r s (finGL E r a, finGL E s b) * BlockDerivatives.yp k t * finGL E (r + s) l := by
  have hP : finGL E (r + s) (unip x * lev (Af E) r s (a, b)) =
      unip (fun p => sFin E (x p)) * lev (Ad E) r s (finGL E r a, finGL E s b) := by
    rw [map_mul, finGL_unip', Slice1.lev_finGL]
  rw [← hP, BlockDerivatives.yp, BlockDerivatives.yp]
  have e : finGL E (r + s) (unip x * lev (Af E) r s (a, b) * t * l) =
      finGL E (r + s) (unip x * lev (Af E) r s (a, b)) * finGL E (r + s) t * finGL E (r + s) l := by
    rw [map_mul, map_mul]
  rw [e]
  simp only [mul_assoc]
  rw [← mul_assoc (infGL E (r + s) (Unitary.toUnits k)) (finGL E (r + s) (unip x * lev (Af E) r s (a, b))),
    infGL_comm, mul_assoc]

theorem yp_one_fin {a : ℕ} (h : GL (Fin a) (Af E)) : BlockDerivatives.yp (1 : Kinf E a) h = finGL E a h := by
  simp [BlockDerivatives.yp]

theorem grp_step (m : GA E r × GA E s) (x : BlockIx (r + s) r → Af E) (a : GL (Fin r) (Af E)) (b : GL (Fin s) (Af E))
    (y : GA E (r + s)) (z : GA E (r + s)) :
    ∃ v : BlockIx (r + s) r → Ad E, lev (Ad E) r s m * (unip (fun p => sFin E (x p)) *
        lev (Ad E) r s (finGL E r a, finGL E s b) * y * z) =
      unip v * (lev (Ad E) r s (m.1 * finGL E r a, m.2 * finGL E s b) * y) * z := by
  obtain ⟨v, hv⟩ := InducedTensorMap.lev_mul_unip m (fun p => sFin E (x p))
  refine ⟨v, ?_⟩
  have e : lev (Ad E) r s (m.1 * finGL E r a, m.2 * finGL E s b) =
      lev (Ad E) r s m * lev (Ad E) r s (finGL E r a, finGL E s b) := by
    rw [← map_mul]; rfl
  rw [e]
  simp only [mul_assoc]
  rw [← mul_assoc (lev (Ad E) r s m) (unip _), hv]
  simp only [mul_assoc]

theorem slice_decomp_left (F : Sm E (r + s)) (hu : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (l : GL (Fin (r + s)) (Af E)) (hl : ∀ y, F.1 (y * finGL E (r + s) l) = F.1 y) (k : Kinf E (r + s))
    (x : BlockIx (r + s) r → Af E) (a : GL (Fin r) (Af E)) (b : GL (Fin s) (Af E)) (t : GL (Fin (r + s)) (Af E))
    (m₂ : GA E s) :
    sl0 m₂ (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) F) =
      act (.fin a) (sl0 (m₂ * finGL E s b) (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k t) F)) := by
  refine Subtype.ext (funext fun m₁ => ?_)
  have L : (sl0 m₂ (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) F)).1 m₁ =
      F.1 (lev (Ad E) r s (m₁, m₂) * BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) := by
    rw [left_slice_apply, rt_apply]
  have R : (act (.fin a) (sl0 (m₂ * finGL E s b) (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k t) F))).1 m₁ =
      F.1 (lev (Ad E) r s (m₁ * finGL E r a, m₂ * finGL E s b) * BlockDerivatives.yp k t) := by
    rw [act_fin_eq, rt_apply, yp_one_fin, left_slice_apply, rt_apply]
  rw [L, R, yp_decomp]
  obtain ⟨v, hv⟩ := grp_step (m₁, m₂) x a b (BlockDerivatives.yp k t) (finGL E (r + s) l)
  rw [hv, hl, hu]

theorem slice_decomp_right (F : Sm E (r + s)) (hu : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (l : GL (Fin (r + s)) (Af E)) (hl : ∀ y, F.1 (y * finGL E (r + s) l) = F.1 y) (k : Kinf E (r + s))
    (x : BlockIx (r + s) r → Af E) (a : GL (Fin r) (Af E)) (b : GL (Fin s) (Af E)) (t : GL (Fin (r + s)) (Af E))
    (m₁ : GA E r) :
    sl1 m₁ (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) F) =
      act (.fin b) (sl1 (m₁ * finGL E r a) (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k t) F)) := by
  refine Subtype.ext (funext fun m₂ => ?_)
  have L : (sl1 m₁ (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) F)).1 m₂ =
      F.1 (lev (Ad E) r s (m₁, m₂) * BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) := by
    rw [right_slice_apply, rt_apply]
  have R : (act (.fin b) (sl1 (m₁ * finGL E r a) (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k t) F))).1 m₂ =
      F.1 (lev (Ad E) r s (m₁ * finGL E r a, m₂ * finGL E s b) * BlockDerivatives.yp k t) := by
    rw [act_fin_eq, rt_apply, yp_one_fin, right_slice_apply, rt_apply]
  rw [L, R, yp_decomp]
  obtain ⟨v, hv⟩ := grp_step (m₁, m₂) x a b (BlockDerivatives.yp k t) (finGL E (r + s) l)
  rw [hv, hl, hu]

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))}
  {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}

theorem orbSpan_le {a : ℕ} {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) {φ : Sm E a} (hφ : φ ∈ V) :
    GlobalTheory.CuspRep.LocEx.orbSpan φ ≤ V :=
  Submodule.span_le.2 (by rintro _ ⟨κ, rfl⟩; exact hV (.cpt κ) φ hφ)

theorem stepA_left (hexp : HExp U T) {β : Sm E (r + s)} (hβ : β ∈ U) :
    ∃ F : Finset (Sm E r), (↑F : Set (Sm E r)) ⊆ BlockDerivatives.LS U T ∧
      ∀ m₂, sl0 m₂ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E r)) := by
  classical
  have hx := exp_one hexp hβ
  obtain ⟨n, b, q, hb, -, he⟩ := hx
  have h : ∀ i, ∃ Fi : Finset (Sm E r), (↑Fi : Set (Sm E r)) ⊆ BlockDerivatives.lsF r s (T β) 1 1 ∧
      b i ∈ Submodule.span ℂ (↑Fi : Set (Sm E r)) := fun i => Submodule.mem_span_finite_of_mem_span (hb i)
  choose Fi hFi hbFi using h
  refine ⟨Finset.univ.biUnion Fi, ?_, fun m₂ => ?_⟩
  · intro ℓ hℓ
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hℓ)
    exact BlockDerivatives.lsF_sub_LS hβ 1 1 (hFi i hi)
  · rw [left_slice_eq_sum (T β) b q he m₂]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact Submodule.span_mono (fun x hx => Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hx⟩))
      (hbFi i)

theorem stepA_right (hexp : HExp U T) {β : Sm E (r + s)} (hβ : β ∈ U) :
    ∃ F : Finset (Sm E s), (↑F : Set (Sm E s)) ⊆ BlockDerivatives.RS U T ∧
      ∀ m₁, sl1 m₁ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E s)) := by
  classical
  have hx := exp_one hexp hβ
  obtain ⟨n, b, q, -, hq, he⟩ := hx
  refine ⟨Finset.univ.image q, ?_, fun m₁ => ?_⟩
  · intro ℓ hℓ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hℓ)
    exact BlockDerivatives.rsF_sub_RS hβ 1 1 (hq i)
  · rw [right_slice_eq_sum (T β) b q he m₁]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem q (Finset.mem_univ i))))

theorem stepB_left (hU : IsAutSt U) (hexp : HExp U T) {φ : Sm E (r + s)} (hφ : φ ∈ U) :
    ∃ F : Finset (Sm E r), (↑F : Set (Sm E r)) ⊆ BlockDerivatives.LS U T ∧
      ∀ (κ : Kinf E (r + s)) (m₂ : GA E s), sl0 m₂ (T (act (.cpt κ) φ)) ∈ Submodule.span ℂ (↑F : Set (Sm E r)) := by
  classical
  have hfd : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan φ) := (hU.2 φ hφ).kfin
  have hfg' := (Submodule.fg_iff_finiteDimensional _).2 hfd
  obtain ⟨B, hB⟩ := hfg'
  have hBU : ∀ β ∈ B, β ∈ U := fun β hβ =>
    orbSpan_le hU.1 hφ (hB ▸ Submodule.subset_span (Finset.mem_coe.2 hβ))
  have hc := collect (α := Sm E (r + s)) (β := Sm E r) B (BlockDerivatives.LS U T)
    (fun (β : Sm E (r + s)) (F : Finset (Sm E r)) => ∀ m₂, sl0 m₂ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E r)))
    (fun β F F' hFF' h m₂ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h m₂))
    (fun β hβ => stepA_left hexp (hBU β hβ))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun κ m₂ => ?_⟩
  have hmem : act (.cpt κ) φ ∈ Submodule.span ℂ (↑B : Set (Sm E (r + s))) :=
    hB ▸ Submodule.subset_span ⟨κ, rfl⟩
  have hle : Submodule.span ℂ (↑B : Set (Sm E (r + s))) ≤
      (Submodule.span ℂ (↑F : Set (Sm E r))).comap (sl0 m₂ ∘ₗ T) :=
    Submodule.span_le.2 fun β hβ => hQ β (Finset.mem_coe.1 hβ) m₂
  exact hle hmem

theorem stepB_right (hU : IsAutSt U) (hexp : HExp U T) {φ : Sm E (r + s)} (hφ : φ ∈ U) :
    ∃ F : Finset (Sm E s), (↑F : Set (Sm E s)) ⊆ BlockDerivatives.RS U T ∧
      ∀ (κ : Kinf E (r + s)) (m₁ : GA E r), sl1 m₁ (T (act (.cpt κ) φ)) ∈ Submodule.span ℂ (↑F : Set (Sm E s)) := by
  classical
  have hfd : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan φ) := (hU.2 φ hφ).kfin
  have hfg' := (Submodule.fg_iff_finiteDimensional _).2 hfd
  obtain ⟨B, hB⟩ := hfg'
  have hBU : ∀ β ∈ B, β ∈ U := fun β hβ =>
    orbSpan_le hU.1 hφ (hB ▸ Submodule.subset_span (Finset.mem_coe.2 hβ))
  have hc := collect (α := Sm E (r + s)) (β := Sm E s) B (BlockDerivatives.RS U T)
    (fun (β : Sm E (r + s)) (F : Finset (Sm E s)) => ∀ m₁, sl1 m₁ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E s)))
    (fun β F F' hFF' h m₁ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h m₁))
    (fun β hβ => stepA_right hexp (hBU β hβ))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun κ m₁ => ?_⟩
  have hmem : act (.cpt κ) φ ∈ Submodule.span ℂ (↑B : Set (Sm E (r + s))) :=
    hB ▸ Submodule.subset_span ⟨κ, rfl⟩
  have hle : Submodule.span ℂ (↑B : Set (Sm E (r + s))) ≤
      (Submodule.span ℂ (↑F : Set (Sm E s))).comap (sl1 m₁ ∘ₗ T) :=
    Submodule.span_le.2 fun β hβ => hQ β (Finset.mem_coe.1 hβ) m₁
  exact hle hmem

theorem right_inv_of_stab (_hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) {ψ₀ : Sm E (r + s)} (hψ₀ : ψ₀ ∈ U)
    {l : GL (Fin (r + s)) (Af E)} (hl : l ∈ JFinTr.stabFin ψ₀) (y : GA E (r + s)) :
    (T ψ₀).1 (y * finGL E (r + s) l) = (T ψ₀).1 y := by
  have h1 : act (.fin l) ψ₀ = ψ₀ := hl
  have h2 := hT.equiv (.fin l) ψ₀ hψ₀
  rw [h1] at h2
  have h3 := congrArg (fun F : Sm E (r + s) => F.1 y) h2
  rw [act_fin_eq, rt_apply, yp_one_fin] at h3
  exact h3.symm

theorem stepC_left (hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) (hexp : HExp U T) {ψ₀ : Sm E (r + s)}
    (hψ₀ : ψ₀ ∈ U) :
    ∃ F : Finset (Sm E r), (↑F : Set (Sm E r)) ⊆ BlockDerivatives.LS U T ∧ ∀ W : Submodule ℂ (Sm E r), _root_.GlobalTheory.CuspRep.IsStable W →
      (↑F : Set (Sm E r)) ⊆ W → ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₂ : GA E s),
        sl0 m₂ (T (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k g) ψ₀)) ∈ W := by
  classical
  have hL : IsOpen ((JFinTr.stabFin ψ₀ : Subgroup (GL (Fin (r + s)) (Af E))) : Set (GL (Fin (r + s)) (Af E))) :=
    (hU.2 ψ₀ hψ₀).level
  have hcov := cover (r := r) (s := s) (JFinTr.stabFin ψ₀) hL
  obtain ⟨Tf, hTf⟩ := hcov
  have hc := collect (α := GL (Fin (r + s)) (Af E)) (β := Sm E r) Tf (BlockDerivatives.LS U T)
    (fun (t : GL (Fin (r + s)) (Af E)) (F : Finset (Sm E r)) => ∀ (κ : Kinf E (r + s)) (m₂ : GA E s),
      sl0 m₂ (T (act (.cpt κ) (act (.fin t) ψ₀))) ∈ Submodule.span ℂ (↑F : Set (Sm E r)))
    (fun t F F' hFF' h κ m₂ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h κ m₂))
    (fun t _ => stepB_left hU hexp (hU.1 (.fin t) ψ₀ hψ₀))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun W hW hFW k g m₂ => ?_⟩
  obtain ⟨x, a, b, t, l, ht, hl, rfl⟩ := hTf g
  rw [T_rt_yp hU.1 hT.equiv k _ hψ₀,
    slice_decomp_left (T ψ₀) (hT.unipInv ψ₀ hψ₀) l (right_inv_of_stab hU hT hψ₀ hl) k x a b t m₂]
  refine hW (.fin a) _ ?_
  rw [← T_rt_yp hU.1 hT.equiv k t hψ₀, rt_yp_eq]
  exact Submodule.span_le.2 hFW (hQ t ht k _)

theorem stepC_right (hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) (hexp : HExp U T) {ψ₀ : Sm E (r + s)}
    (hψ₀ : ψ₀ ∈ U) :
    ∃ F : Finset (Sm E s), (↑F : Set (Sm E s)) ⊆ BlockDerivatives.RS U T ∧ ∀ W : Submodule ℂ (Sm E s), _root_.GlobalTheory.CuspRep.IsStable W →
      (↑F : Set (Sm E s)) ⊆ W → ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₁ : GA E r),
        sl1 m₁ (T (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k g) ψ₀)) ∈ W := by
  classical
  have hL : IsOpen ((JFinTr.stabFin ψ₀ : Subgroup (GL (Fin (r + s)) (Af E))) : Set (GL (Fin (r + s)) (Af E))) :=
    (hU.2 ψ₀ hψ₀).level
  have hcov := cover (r := r) (s := s) (JFinTr.stabFin ψ₀) hL
  obtain ⟨Tf, hTf⟩ := hcov
  have hc := collect (α := GL (Fin (r + s)) (Af E)) (β := Sm E s) Tf (BlockDerivatives.RS U T)
    (fun (t : GL (Fin (r + s)) (Af E)) (F : Finset (Sm E s)) => ∀ (κ : Kinf E (r + s)) (m₁ : GA E r),
      sl1 m₁ (T (act (.cpt κ) (act (.fin t) ψ₀))) ∈ Submodule.span ℂ (↑F : Set (Sm E s)))
    (fun t F F' hFF' h κ m₁ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h κ m₁))
    (fun t _ => stepB_right hU hexp (hU.1 (.fin t) ψ₀ hψ₀))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun W hW hFW k g m₁ => ?_⟩
  obtain ⟨x, a, b, t, l, ht, hl, rfl⟩ := hTf g
  rw [T_rt_yp hU.1 hT.equiv k _ hψ₀,
    slice_decomp_right (T ψ₀) (hT.unipInv ψ₀ hψ₀) l (right_inv_of_stab hU hT hψ₀ hl) k x a b t m₁]
  refine hW (.fin b) _ ?_
  rw [← T_rt_yp hU.1 hT.equiv k t hψ₀, rt_yp_eq]
  exact Submodule.span_le.2 hFW (hQ t ht k _)

theorem LS_fg (hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) (hfg : FinGen U) (hexp : HExp U T) :
    ∃ S₁ : Finset (Sm E r), (↑S₁ : Set (Sm E r)) ⊆ BlockDerivatives.LS U T ∧
      ∀ W : Submodule ℂ (Sm E r), _root_.GlobalTheory.CuspRep.IsStable W → (↑S₁ : Set (Sm E r)) ⊆ W → BlockDerivatives.LS U T ≤ W := by
  classical
  obtain ⟨S₀, hS₀U, hS₀⟩ := id hfg
  have hc := collect (α := Sm E (r + s)) (β := Sm E r) S₀ (BlockDerivatives.LS U T)
    (fun (ψ₀ : Sm E (r + s)) (F : Finset (Sm E r)) => ∀ W : Submodule ℂ (Sm E r), _root_.GlobalTheory.CuspRep.IsStable W → (↑F : Set (Sm E r)) ⊆ W →
      ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₂ : GA E s),
        sl0 m₂ (T (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k g) ψ₀)) ∈ W)
    (fun ψ₀ F F' hFF' h W hW hW' => h W hW ((Finset.coe_subset.2 hFF').trans hW'))
    (fun ψ₀ hψ₀ => stepC_left hU hT hexp (hS₀U hψ₀))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun W hW hFW => ?_⟩
  have hUM : U ≤ Mleft U T W :=
    hS₀ _ (Mleft_stable hU hT hexp W hW) fun ψ₀ hψ₀ => ⟨hS₀U hψ₀, hQ ψ₀ hψ₀ W hW hFW⟩
  refine Submodule.span_le.2 ?_
  rintro ℓ ⟨ψ, hψ, k, g, hℓ⟩
  obtain ⟨m₂, rfl⟩ := lsF_yp (T ψ) k g ℓ hℓ
  rw [← T_rt_yp hU.1 hT.equiv k g hψ]
  exact (hUM hψ).2 k g m₂

theorem RS_fg (hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) (hfg : FinGen U) (hexp : HExp U T) :
    ∃ S₁ : Finset (Sm E s), (↑S₁ : Set (Sm E s)) ⊆ BlockDerivatives.RS U T ∧
      ∀ W : Submodule ℂ (Sm E s), _root_.GlobalTheory.CuspRep.IsStable W → (↑S₁ : Set (Sm E s)) ⊆ W → BlockDerivatives.RS U T ≤ W := by
  classical
  obtain ⟨S₀, hS₀U, hS₀⟩ := id hfg
  have hc := collect (α := Sm E (r + s)) (β := Sm E s) S₀ (BlockDerivatives.RS U T)
    (fun (ψ₀ : Sm E (r + s)) (F : Finset (Sm E s)) => ∀ W : Submodule ℂ (Sm E s), _root_.GlobalTheory.CuspRep.IsStable W → (↑F : Set (Sm E s)) ⊆ W →
      ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₁ : GA E r),
        sl1 m₁ (T (GlobalTheory.CuspRep.rt E (r + s) (BlockDerivatives.yp k g) ψ₀)) ∈ W)
    (fun ψ₀ F F' hFF' h W hW hW' => h W hW ((Finset.coe_subset.2 hFF').trans hW'))
    (fun ψ₀ hψ₀ => stepC_right hU hT hexp (hS₀U hψ₀))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun W hW hFW => ?_⟩
  have hUM : U ≤ Mright U T W :=
    hS₀ _ (Mright_stable hU hT hexp W hW) fun ψ₀ hψ₀ => ⟨hS₀U hψ₀, hQ ψ₀ hψ₀ W hW hFW⟩
  refine Submodule.span_le.2 ?_
  rintro ℓ ⟨ψ, hψ, k, g, hℓ⟩
  obtain ⟨m₁, rfl⟩ := rsF_yp (T ψ) k g ℓ hℓ
  rw [← T_rt_yp hU.1 hT.equiv k g hψ]
  exact (hUM hψ).2 k g m₁

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryProdLocalPointsMulLatticeStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartAlgebraMapLiftV
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicStripSetMeasurableReadOnRealPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceHeisenbergDerivThetaTransformAlgebraicD
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelAction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingEvaluation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitRowsBarPhaseCompatibility

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemAdelicLatticeAtPlaceOfTensorWithLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemAdelicLatticeAtPlaceOfTensorWithLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp
noncomputable section

namespace GlobalTheory.LatExtract

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc latAtV incM At)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def mulL {d : ℕ} (c : E) : (Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) →+ (Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) where
  toFun z := fun j => inclR (F := F) (AF F) c * z j
  map_zero' := by ext j; simp
  map_add' z z' := by ext j; simp [mul_add]

lemma mulL_apply {d : ℕ} (c : E) (z : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (j : Fin d) :
    mulL (F := F) c z j = inclR (F := F) (AF F) c * z j := rfl

lemma mulL_int_mem {d : ℕ} (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (o : 𝓞 E)
    {z : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)}
    (hz : z ∈ GlobalTheory.InertSph.latAt W v) : mulL (F := F) (o : E) z ∈ GlobalTheory.InertSph.latAt W v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hai, o • y, W.L.smul_mem o hy, ?_⟩
    ext j
    simp only [mulL_apply, Pi.smul_apply]
    rw [Algebra.smul_def (A := E) o (y j), map_mul, mul_smul_comm]
  | zero => simpa using (GlobalTheory.InertSph.latAt W v).zero_mem
  | add z z' _ _ h h' => rw [map_add (f := _)]; exact (GlobalTheory.InertSph.latAt W v).add_mem h h'
  | neg z _ h => rw [map_neg]; exact (GlobalTheory.InertSph.latAt W v).neg_mem h

end GlobalTheory.LatExtract

namespace GlobalTheory.LatExtract

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc latAtV incM At)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rowL {n d : ℕ} (i₀ : Fin n) (c : E) :
    Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) →+ (Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) where
  toFun Γ := fun j => inclR (F := F) (AF F) c * Γ i₀ j
  map_zero' := by ext j; simp
  map_add' z z' := by ext j; simp [mul_add]

lemma rowL_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (i₀ : Fin n) (c : E)
    (hc : ∀ x ∈ X.L, ∃ o : 𝓞 E, (o : E) = c * x i₀)
    {Γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hΓ : Γ ∈ latAtV X W v) :
    rowL (F := F) i₀ c Γ ∈ GlobalTheory.InertSph.latAt W v := by
  induction hΓ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
    obtain ⟨o, ho⟩ := hc x hx
    refine AddSubgroup.subset_closure ⟨a, ha, hai, o • y, W.L.smul_mem o hy, ?_⟩
    ext j
    show inclR (F := F) (AF F) c * (a • incM F (Matrix.vecMulVec x y)) i₀ j = _
    simp only [Matrix.smul_apply, Pi.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply]
    rw [Algebra.smul_def (A := E) o (y j), mul_smul_comm, ← map_mul, ← mul_assoc]
    congr 2
    rw [← ho]
  | zero => simpa using (GlobalTheory.InertSph.latAt W v).zero_mem
  | add z z' _ _ h h' => rw [map_add (f := _)]; exact (GlobalTheory.InertSph.latAt W v).add_mem h h'
  | neg z _ h => rw [map_neg]; exact (GlobalTheory.InertSph.latAt W v).neg_mem h

lemma rowL_vecMulVec {n d : ℕ} (i₀ : Fin n) (c : E) (x : Fin n → E) (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    rowL (F := F) i₀ c (Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q) = mulL (F := F) (c * x i₀) q := by
  ext j
  simp only [rowL, mulL, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.vecMulVec_apply, map_mul, mul_assoc]

end GlobalTheory.LatExtract

namespace GlobalTheory.LatExtract

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc latAtV incM At)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def coefSub {d : ℕ} (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    Submodule (𝓞 E) E where
  carrier := {c | mulL (F := F) c q ∈ GlobalTheory.InertSph.latAt W v}
  zero_mem' := by
    change mulL (F := F) (0 : E) q ∈ GlobalTheory.InertSph.latAt W v
    have : mulL (F := F) (0 : E) q = 0 := by ext j; simp [mulL_apply]
    rw [this]; exact (GlobalTheory.InertSph.latAt W v).zero_mem
  add_mem' {a b} ha hb := by
    change mulL (F := F) (a + b) q ∈ GlobalTheory.InertSph.latAt W v
    have : mulL (F := F) (a + b) q = mulL (F := F) a q + mulL (F := F) b q := by
      ext j; simp [mulL_apply, add_mul]
    rw [this]; exact (GlobalTheory.InertSph.latAt W v).add_mem ha hb
  smul_mem' o c hc := by
    change mulL (F := F) (o • c) q ∈ GlobalTheory.InertSph.latAt W v
    have : mulL (F := F) (o • c) q = mulL (F := F) (o : E) (mulL (F := F) c q) := by
      ext j; simp only [mulL_apply, Algebra.smul_def, map_mul, mul_assoc]
    rw [this]; exact mulL_int_mem W v o hc

theorem extract (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hn : 0 < n) (hL : X.L.IsFullLattice E)
    (h : ∀ x ∈ X.L, Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q ∈ latAtV X W v) :
    q ∈ GlobalTheory.InertSph.latAt W v := by
  set i₀ : Fin n := ⟨0, hn⟩
  let b₀ : Submodule (𝓞 E) E := X.L.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin n => E) i₀)
  have hfg : b₀.FG := hL.fg.map _
  let 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨b₀, FractionalIdeal.isFractional_of_fg hfg⟩
  have hmem : ∀ b, b ∈ 𝔟 ↔ ∃ x ∈ X.L, x i₀ = b := fun b => by
    rw [← FractionalIdeal.mem_coe]; exact Submodule.mem_map
  have hne : 𝔟 ≠ 0 := by
    intro h0
    have hle : Submodule.span E (X.L : Set (Fin n → E)) ≤ LinearMap.ker (LinearMap.proj (R := E) (φ := fun _ : Fin n => E) i₀) := by
      rw [Submodule.span_le]
      intro x hx
      have : x i₀ ∈ 𝔟 := (hmem _).2 ⟨x, hx, rfl⟩
      rw [h0, FractionalIdeal.mem_zero_iff] at this
      simpa using this
    rw [Submodule.IsFullLattice.span_eq_top (self := hL)] at hle
    have := hle (Submodule.mem_top (x := Pi.single i₀ (1 : E)))
    simp at this
  have hone : (1 : E) ∈ ((𝔟⁻¹ * 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) := by
    rw [inv_mul_cancel₀ hne, FractionalIdeal.mem_coe]; exact FractionalIdeal.one_mem_one _
  have hle : ((𝔟⁻¹ * 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) ≤ coefSub W v q := by
    rw [FractionalIdeal.coe_mul, Submodule.mul_le]
    intro c hc b hb
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_inv_iff hne] at hc
    rw [FractionalIdeal.mem_coe, hmem] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    have hc' : ∀ x ∈ X.L, ∃ o : 𝓞 E, (o : E) = c * x i₀ := by
      intro x hx
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 (hc _ ((hmem _).2 ⟨x, hx, rfl⟩))
      exact ⟨o, ho⟩
    change mulL (F := F) (c * x i₀) q ∈ GlobalTheory.InertSph.latAt W v
    rw [← rowL_vecMulVec]
    exact rowL_mem X W v i₀ c hc' (h x hx)
  have h1 : mulL (F := F) (1 : E) q ∈ GlobalTheory.InertSph.latAt W v := hle hone
  have : mulL (F := F) (1 : E) q = q := by ext j; simp [mulL_apply]
  rwa [this] at h1

end GlobalTheory.LatExtract

theorem GlobalTheory.LatExtract.main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), 0 < n → X.L.IsFullLattice E →
    (∀ x ∈ X.L, Matrix.vecMulVec (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (x i)) q ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W v) →
    q ∈ GlobalTheory.InertSph.latAt W v := fun F E _ _ _ _ _ n d X W v q hn hL h =>
  GlobalTheory.LatExtract.extract n d X W v q hn hL h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemAdelicLatticeAtPlaceOfTensorWithLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_adelicLatticeAtPlace_of_tensor_with_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), 0 < n → X.L.IsFullLattice E →
    (∀ x ∈ X.L, Matrix.vecMulVec (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (x i)) q ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W v) →
    q ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ n d X W v q hn hL h
  letI := hL
  exact GlobalTheory.LatExtract.main F E n d X W v q hn inferInstance h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselCharacterRealPlaceUnipotentEqTrace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselCharacterRealPlaceUnipotentEqTrace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesselCoords

open GlobalTheory.BesselChar

section Alg

variable {R : Type} [CommRing R] {n r : ℕ}

theorem cols_resid {L : Matrix (Fin r) (Fin n) R} {E : Matrix (Fin n) (Fin r) R} (hL : L * E = 1)
    {U : Matrix (Fin n) (Fin n) R} (h : ∀ i : Fin r, ∃ a : Fin r → R, (U - 1) *ᵥ (fun k => E k i) = E *ᵥ a) :
    (U - 1) * E - E * (L * (U - 1) * E) = 0 := by
  choose a ha using h
  have e1 : (U - 1) * E = E * (Matrix.of a)ᵀ := by
    ext k i
    exact congr_fun (ha i) k
  rw [Matrix.mul_assoc, e1, ← Matrix.mul_assoc L, hL, Matrix.one_mul, sub_self]

theorem vec_resid {L : Matrix (Fin r) (Fin n) R} {E : Matrix (Fin n) (Fin r) R} (hL : L * E = 1)
    {U : Matrix (Fin n) (Fin n) R} {z : Fin n → R} {a : Fin r → R} (h : (U - 1) *ᵥ z = E *ᵥ a) :
    (U - 1) *ᵥ z - E *ᵥ ((L * (U - 1)) *ᵥ z) = 0 := by
  have e2 : L *ᵥ (E *ᵥ a) = a := by rw [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, h, e2, sub_self]

theorem cols_resid_map {S : Type} [CommRing S] (f : R →+* S) (L : Matrix (Fin r) (Fin n) R)
    (E : Matrix (Fin n) (Fin r) R) (U : Matrix (Fin n) (Fin n) R) :
    ((U - 1) * E - E * (L * (U - 1) * E)).map f =
      (U.map f - 1) * E.map f - E.map f * (L.map f * (U.map f - 1) * E.map f) := by
  have hm : (U - 1).map f = U.map f - 1 := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hm]

theorem vec_resid_map {S : Type} [CommRing S] (f : R →+* S) (L : Matrix (Fin r) (Fin n) R)
    (E : Matrix (Fin n) (Fin r) R) (U : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    (fun i => f ((((U - 1) *ᵥ z - E *ᵥ ((L * (U - 1)) *ᵥ z) : Fin n → R)) i)) =
      (U.map f - 1) *ᵥ (fun i => f (z i)) - E.map f *ᵥ ((L.map f * (U.map f - 1)) *ᵥ (fun i => f (z i))) := by
  have hm : (U - 1).map f = U.map f - 1 := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← hm, ← Matrix.map_mul, mulVec_map, mulVec_map, mulVec_map]
  funext i
  simp only [Pi.sub_apply, map_sub]

theorem cols_of_resid {M : Matrix (Fin n) (Fin n) R} {E : Matrix (Fin n) (Fin r) R} {T : Matrix (Fin r) (Fin r) R}
    (h : (M - 1) * E - E * T = 0) : M * E = E + E * T := by
  rw [sub_eq_zero, Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add'] at h
  exact h

theorem vec_of_resid {M : Matrix (Fin n) (Fin n) R} {E : Matrix (Fin n) (Fin r) R} {z : Fin n → R} {b : Fin r → R}
    (h : (M - 1) *ᵥ z - E *ᵥ b = 0) : M *ᵥ z = z + E *ᵥ b := by
  rw [sub_eq_zero, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add'] at h
  exact h

theorem coordSum_one (c : Fin r → R) (L : Matrix (Fin r) (Fin n) R) (E : Matrix (Fin n) (Fin r) R) (z : Fin n → R) :
    coordSum c L E z 1 = 0 := by
  simp [coordSum, superSum]

end Alg

theorem coordSum_flag {n r : ℕ} (c : Fin r → ℂ) {L : Matrix (Fin r) (Fin n) ℂ} {e : Matrix (Fin n) (Fin r) ℂ}
    (hL : L * e = 1) (z : Fin n → ℂ) (u : Matrix (Fin n) (Fin n) ℂ) (a : Fin r → Fin r → ℂ)
    (ha : ∀ j : Fin r, (u - 1) *ᵥ GlobalTheory.RealBessel.flagVec e z j.succ = e *ᵥ a j) :
    coordSum c L e z u = ∑ j, c j * a j j := by
  have key : ∀ j : Fin r, (L * (u - 1)) *ᵥ GlobalTheory.RealBessel.flagVec e z j.succ = a j := by
    intro j
    rw [← Matrix.mulVec_mulVec, ha j, Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]
  have hT : ∀ i j : Fin r, j.1 = i.1 + 1 → (L * (u - 1) * e : Matrix (Fin r) (Fin r) ℂ) i j = a i i := by
    intro i j hij
    have hf : GlobalTheory.RealBessel.flagVec e z i.succ = fun k => e k j := by
      have : i.succ = Fin.castSucc j := Fin.ext (by simp [hij])
      rw [this, GlobalTheory.RealBessel.flagVec, Fin.snoc_castSucc]
    have := congr_fun (key i) i
    rw [hf] at this
    rw [← this, Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct]
  have hb : ∀ i : Fin r, i.1 + 1 = r → ((L * (u - 1)) *ᵥ z) i = a i i := by
    intro i hi
    have hf : GlobalTheory.RealBessel.flagVec e z i.succ = z := by
      have : i.succ = Fin.last r := Fin.ext (by simp [hi])
      rw [this, GlobalTheory.RealBessel.flagVec, Fin.snoc_last]
    have := congr_fun (key i) i
    rwa [hf] at this
  have hrow : ∀ i : Fin r, (∑ j : Fin r, if j.1 = i.1 + 1 then c i * (L * (u - 1) * e : Matrix (Fin r) (Fin r) ℂ) i j else 0) =
      if i.1 + 1 < r then c i * a i i else 0 := by
    intro i
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨i.1 + 1, h⟩]
      · rw [if_pos rfl, hT i ⟨i.1 + 1, h⟩ rfl]
      · intro j _ hj
        rw [if_neg]
        intro h'
        exact hj (Fin.ext h')
      · intro h'; exact absurd (Finset.mem_univ _) h'
    · refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg]
      intro h'
      have := j.2
      omega
  unfold coordSum superSum
  simp only [hrow]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := i.2
  by_cases h : i.1 + 1 < r
  · rw [if_pos h, if_neg (by omega), add_zero]
  · rw [if_neg h, if_pos (by omega), zero_add, hb i (by omega)]

variable {D : D7}

theorem mat_eq_zero (θ : InfFam D) (hθ : IsInfFam θ) {m k : ℕ} (Y : Matrix (Fin m) (Fin k) (AE D))
    (h1 : Y.map (finPart D) = 0) (h2 : ∀ ρ, Y.map ((θ ρ).comp (infPart D)) = 0) : Y = 0 := by
  ext i j
  refine (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2 _ (fun ρ => ?_) ?_
  · exact congr_fun (congr_fun (h2 ρ) i) j
  · exact congr_fun (congr_fun h1 i) j

theorem vec_eq_zero (θ : InfFam D) (hθ : IsInfFam θ) {m : ℕ} (Y : Fin m → AE D)
    (h1 : (fun i => finPart D (Y i)) = 0) (h2 : ∀ ρ, (fun i => (θ ρ).comp (infPart D) (Y i)) = 0) : Y = 0 := by
  funext i
  refine (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2 _ (fun ρ => ?_) ?_
  · exact congr_fun (h2 ρ) i
  · exact congr_fun h1 i

theorem comp_incA (θ : InfFam D) (hθ : IsInfFam θ) (ρ : D.what₂.Tau) :
    ((θ ρ).comp (infPart D)).comp (incA D) = tauE D ρ :=
  RingHom.ext fun x => (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.1 x ρ

end GlobalTheory.BesselCoords

namespace GlobalTheory.BesselCoords

open GlobalTheory.BesselChar


set_option maxHeartbeats 1000000 in
theorem besChar_atTau_coords : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesDat A B ι) (τ : D.what₂.Tau) (u : Matrix (Fin B.rank) (Fin B.rank) ℂ),
  u ∈ GlobalTheory.RealBessel.unipRad (gramAt D B τ) (d.e.map (tauE D τ)) →
  ∀ a : Fin d.ρ → Fin d.ρ → ℂ, (∀ j : Fin d.ρ, (u - 1) *ᵥ GlobalTheory.RealBessel.flagVec (d.e.map (tauE D τ)) (fun k => tauE D τ (d.z k)) j.succ = d.e.map (tauE D τ) *ᵥ a j) →
  ∃ t : AE D, finPart D t = 0 ∧ (∀ ρ, ρ ≠ τ → θ ρ (infPart D t) = 0) ∧ θ τ (infPart D t) = ∑ j, tauE D τ (d.c j) * a j j ∧
    besChar ψ d (atTau θ B τ u) = ψ (Algebra.trace (AF D.host.F) (AE D) t) := by
  intro D θ hθ ψ A B ι d τ u hu a ha
  obtain ⟨hgC, hgτ, hgρ⟩ := GlobalTheory.PointAtPlaceHom.atTau_spec hθ B τ hu.1
  obtain ⟨L, hL⟩ := exists_leftInv d.e d.e_iso.1
  have hfin : (Formalism.L2.Theta.mt B (atTau θ B τ u)).map (finPart D) = 1 := GlobalTheory.StripBorel.mt_map_fin hgC
  have hinf : ∀ ρ, (Formalism.L2.Theta.mt B (atTau θ B τ u)).map ((θ ρ).comp (infPart D)) =
      infMat D.sp.cm.sig B.gram (θ ρ) (atTau θ B τ u) := fun ρ => rfl
  have hmap : ∀ ρ {m k : ℕ} (X : Matrix (Fin m) (Fin k) D.host.E),
      (X.map (incA D)).map ((θ ρ).comp (infPart D)) = X.map (tauE D ρ) := by
    intro ρ m k X
    rw [Matrix.map_map, ← RingHom.coe_comp, comp_incA θ hθ ρ]
  have hvec : ∀ ρ {m : ℕ} (x : Fin m → D.host.E),
      (fun i => ((θ ρ).comp (infPart D)) (incA D (x i))) = fun i => tauE D ρ (x i) := by
    intro ρ m x
    funext i
    exact (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.1 (x i) ρ
  have hL' := map_leftInv (incA D) hL
  have hLτ := map_leftInv (tauE D τ) hL

  have hperp : ((d.e.map (tauE D τ))ᴴ * gramAt D B τ) *ᵥ (fun k => tauE D τ (d.z k)) = 0 := by
    have h0 := mulVec_map (tauE D τ) (perpMat B d.e) d.z
    rw [d.z_perpE] at h0
    have hm : (perpMat B d.e).map (tauE D τ) = (d.e.map (tauE D τ))ᴴ * gramAt D B τ := by
      rw [perpMat, Matrix.map_mul]
      refine congrArg₂ (· * ·) ?_ rfl
      ext i j
      simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
      exact GlobalTheory.Mem.Isom.tauE_sig D τ _
    rw [hm] at h0
    rw [h0]
    funext i
    exact map_zero _
  have h1 : Formalism.L2.Theta.mt B (atTau θ B τ u) * d.e.map (incA D) = d.e.map (incA D) +
      d.e.map (incA D) * (L.map (incA D) * (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1) * d.e.map (incA D)) := by
    have hK : (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1) * d.e.map (incA D) - d.e.map (incA D) *
        (L.map (incA D) * (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1) * d.e.map (incA D)) = 0 := by
      refine mat_eq_zero θ hθ _ ?_ ?_
      · rw [cols_resid_map, hfin]; simp
      · intro ρ
        rw [cols_resid_map, hinf, hmap, hmap]
        by_cases hρ : ρ = τ
        · subst hρ
          rw [hgτ]
          exact cols_resid (map_leftInv (tauE D ρ) hL) fun i => by
            obtain ⟨a, -, h⟩ := hu.2.1 i
            exact ⟨a, h⟩
        · rw [hgρ ρ hρ]; simp
    exact cols_of_resid hK
  have h2 : Formalism.L2.Theta.mt B (atTau θ B τ u) *ᵥ ratV d.z = ratV d.z +
      d.e.map (incA D) *ᵥ ((L.map (incA D) * (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1)) *ᵥ ratV d.z) := by
    have hK : (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1) *ᵥ ratV d.z - d.e.map (incA D) *ᵥ
        ((L.map (incA D) * (Formalism.L2.Theta.mt B (atTau θ B τ u) - 1)) *ᵥ ratV d.z) = 0 := by
      refine vec_eq_zero θ hθ _ ?_ ?_
      · refine (vec_resid_map (finPart D) _ _ _ _).trans ?_
        rw [hfin]
        simp only [sub_self, Matrix.zero_mulVec, Matrix.mul_zero, Matrix.mulVec_zero]
      · intro ρ
        refine (vec_resid_map ((θ ρ).comp (infPart D)) _ _ _ _).trans ?_
        rw [hinf, hmap, hmap]
        have hz : (fun i => ((θ ρ).comp (infPart D)) (ratV d.z i)) = fun i => tauE D ρ (d.z i) := hvec ρ d.z
        rw [hz]
        by_cases hρ : ρ = τ
        · subst hρ
          rw [hgτ]
          obtain ⟨b, hb⟩ := hu.2.2 _ hperp
          exact vec_resid (map_leftInv (tauE D ρ) hL) hb
        · rw [hgρ ρ hρ]
          simp only [sub_self, Matrix.zero_mulVec, Matrix.mul_zero, Matrix.mulVec_zero]
    exact vec_of_resid hK
  refine ⟨coordSum (fun i => incA D (d.c i)) (L.map (incA D)) (d.e.map (incA D)) (ratV d.z)
    (Formalism.L2.Theta.mt B (atTau θ B τ u)), ?_, ?_, ?_, ?_⟩
  · rw [← coordSum_map, hfin, coordSum_one]
  · intro ρ hρ
    show ((θ ρ).comp (infPart D)) _ = 0
    rw [← coordSum_map, hinf, hgρ ρ hρ, coordSum_one]
  · show ((θ τ).comp (infPart D)) _ = _
    rw [← coordSum_map, hinf, hgτ, hmap, hmap, hvec τ d.c]
    have hz : (fun i => ((θ τ).comp (infPart D)) (ratV d.z i)) = fun i => tauE D τ (d.z i) := hvec τ d.z
    rw [hz]
    exact coordSum_flag _ hLτ _ u a ha
  · exact besChar_eq ψ d _ _ _ h1 h2

end GlobalTheory.BesselCoords
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselCharacterRealPlaceUnipotentEqTraceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselCharacter_realPlace_unipotent_eq_trace : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesDat A B ι) (τ : D.what₂.Tau) (u : Matrix (Fin B.rank) (Fin B.rank) ℂ),
  u ∈ GlobalTheory.RealBessel.unipRad (gramAt D B τ) (d.e.map (tauE D τ)) →
  ∀ a : Fin d.ρ → Fin d.ρ → ℂ, (∀ j : Fin d.ρ, (u - 1) *ᵥ GlobalTheory.RealBessel.flagVec (d.e.map (tauE D τ)) (fun k => tauE D τ (d.z k)) j.succ = d.e.map (tauE D τ) *ᵥ a j) →
  ∃ t : AE D, finPart D t = 0 ∧ (∀ ρ, ρ ≠ τ → θ ρ (infPart D t) = 0) ∧ θ τ (infPart D t) = ∑ j, tauE D τ (d.c j) * a j j ∧
    besChar ψ d (atTau θ B τ u) = ψ (Algebra.trace (AF D.host.F) (AE D) t) := by
  first | exact @GlobalTheory.BesselCoords.besChar_atTau_coords | exact GlobalTheory.BesselCoords.besChar_atTau_coords | (intros; apply GlobalTheory.BesselCoords.besChar_atTau_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianTransform
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HoweGlobal.FinPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem one_mem_UAt {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ X.J) ∈ UAt σ X ev := by
  intro u _
  have e : mat (1 : UA σ X.J) = 1 := rfl
  show u • (mat (1 : UA σ X.J) - 1) = 0
  rw [e, sub_self, smul_zero]

variable {Bs : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem exists_image (hT : IsTriple Bs G Xc om om') (v : Pl F) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v))
    (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) (hφ : φ ∈ SB (Fin a × Fin (a + a') → Fv F v)) :
    ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ :=
  GlobalTheory.ThK.LocalOps.acts_exists (GlobalTheory.ThK.RealUniq.isPair_V hT) v (1, h) (one_mem_UAt _ _) hh φ hφ

def locOp (hT : IsTriple Bs G Xc om om') (v : Pl F) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    Module.End ℂ ↥(SB (Fin a × Fin (a + a') → Fv F v)) where
  toFun φ := ⟨Classical.choose (exists_image hT v hh φ φ.2), (Classical.choose_spec (exists_image hT v hh φ φ.2)).1⟩
  map_add' φ ψ := by
    apply Subtype.ext
    have hφ := (Classical.choose_spec (exists_image hT v hh φ φ.2)).2
    have hψ := (Classical.choose_spec (exists_image hT v hh ψ ψ.2)).2
    have hs := (Classical.choose_spec (exists_image hT v hh (φ + ψ : ↥(SB _)) (φ + ψ).2)).2
    have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (fun χ hχ => exists_image hT v hh χ hχ) φ.2 ψ.2 hφ hψ 1 1
    simp only [one_smul] at hl
    exact GlobalTheory.ThK.LocalOps.acts_unique v _ (φ + ψ).2 hs hl
  map_smul' c φ := by
    apply Subtype.ext
    have hφ := (Classical.choose_spec (exists_image hT v hh φ φ.2)).2
    have hs := (Classical.choose_spec (exists_image hT v hh (c • φ : ↥(SB _)) (c • φ).2)).2
    have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (fun χ hχ => exists_image hT v hh χ hχ) φ.2 φ.2 hφ hφ c 0
    simp only [zero_smul, add_zero] at hl
    exact GlobalTheory.ThK.LocalOps.acts_unique v _ (c • φ).2 hs hl

theorem locOp_acts (hT : IsTriple Bs G Xc om om') (v : Pl F) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v))
    (φ : ↥(SB (Fin a × Fin (a + a') → Fv F v))) :
    Acts (evFin F v) (om (1, h)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ)
      ((locOp hT v hh φ : ↥(SB (Fin a × Fin (a + a') → Fv F v))) : (Fin a × Fin (a + a') → Fv F v) → ℂ) :=
  (Classical.choose_spec (exists_image hT v hh φ φ.2)).2

theorem locOp_mem (hT : IsTriple Bs G Xc om om') (v : Pl F) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    locOp hT v hh ∈ GlobalTheory.HoweGlobal.opFin G om v :=
  ⟨h, hh, locOp_acts hT v hh⟩

end GlobalTheory.HoweGlobal.FinPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsOrbitKernel
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

noncomputable section

namespace GlobalTheory.HoweGlobalPair.FinPlaceSmall

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem one_mem_UAt {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ X.J) ∈ UAt σ X ev := by
  intro u _
  have e : mat (1 : UA σ X.J) = 1 := rfl
  show u • (mat (1 : UA σ X.J) - 1) = 0
  rw [e, sub_self, smul_zero]

variable {Bs : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem exists_image (hT : IsTriple Bs G Xc om om') (v : Pl (F := F)) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v))
    (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ) (hφ : φ ∈ SB (Fin a' × Fin (a + a') → Fv F v)) :
    ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ :=
  GlobalTheory.ThK.LocalOps.acts_exists (GlobalTheory.ThK.RealUniq.isPair_V' hT) v (1, h) (one_mem_UAt _ _) hh φ hφ

def locOp (hT : IsTriple Bs G Xc om om') (v : Pl (F := F)) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    Module.End ℂ ↥(SB (Fin a' × Fin (a + a') → Fv F v)) where
  toFun φ := ⟨Classical.choose (exists_image hT v hh φ φ.2), (Classical.choose_spec (exists_image hT v hh φ φ.2)).1⟩
  map_add' φ ψ := by
    apply Subtype.ext
    have hφ := (Classical.choose_spec (exists_image hT v hh φ φ.2)).2
    have hψ := (Classical.choose_spec (exists_image hT v hh ψ ψ.2)).2
    have hs := (Classical.choose_spec (exists_image hT v hh (φ + ψ : ↥(SB _)) (φ + ψ).2)).2
    have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om' (1, h)) (fun χ hχ => exists_image hT v hh χ hχ) φ.2 ψ.2 hφ hψ 1 1
    simp only [one_smul] at hl
    exact GlobalTheory.ThK.LocalOps.acts_unique v _ (φ + ψ).2 hs hl
  map_smul' c φ := by
    apply Subtype.ext
    have hφ := (Classical.choose_spec (exists_image hT v hh φ φ.2)).2
    have hs := (Classical.choose_spec (exists_image hT v hh (c • φ : ↥(SB _)) (c • φ).2)).2
    have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om' (1, h)) (fun χ hχ => exists_image hT v hh χ hχ) φ.2 φ.2 hφ hφ c 0
    simp only [zero_smul, add_zero] at hl
    exact GlobalTheory.ThK.LocalOps.acts_unique v _ (c • φ).2 hs hl

theorem locOp_acts (hT : IsTriple Bs G Xc om om') (v : Pl (F := F)) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v))
    (φ : ↥(SB (Fin a' × Fin (a + a') → Fv F v))) :
    Acts (evFin F v) (om' (1, h)) (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ)
      ((locOp hT v hh φ : ↥(SB (Fin a' × Fin (a + a') → Fv F v))) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
  (Classical.choose_spec (exists_image hT v hh φ φ.2)).2

theorem locOp_mem (hT : IsTriple Bs G Xc om om') (v : Pl (F := F)) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    locOp hT v hh ∈ GlobalTheory.HoweGlobalPair.opFin om' v :=
  ⟨h, hh, locOp_acts hT v hh⟩

end GlobalTheory.HoweGlobalPair.FinPlaceSmall
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairListAction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

open Filter Topology

noncomputable section
open scoped Classical

namespace GlobalTheory.LineAdd

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem tens_add_smul (f s : SInf F κ) (t : ℝ) (r : (κ → AF F) → ℂ) :
    tens (evI F) ⇑(f + t • s) r = tens (evI F) ⇑f r + (t : ℂ) • tens (evI F) ⇑s r := by
  funext x
  simp only [tens, SchwartzMap.add_apply, SchwartzMap.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Complex.real_smul]
  ring

theorem hasDerivAt_of_curve {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f g : SInf F κ} {c : ℝ → SInf F κ}
    {r : (κ → AF F) → ℂ} (hc : ∀ t, T t (tens (evI F) ⇑f r) = tens (evI F) ⇑(c t) r) (hc0 : c 0 = f)
    (hlim : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 g)) :
    ∀ x, HasDerivAt (fun t => T t (tens (evI F) ⇑f r) x) (tens (evI F) ⇑g r x) 0 := by
  intro x
  have ev : ∀ y : κ → mixedEmbedding.mixedSpace F, Continuous fun s : SInf F κ => s y := by
    intro y
    have h1 := (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ).continuous
    exact (continuous_eval_const (F := BoundedContinuousFunction (κ → mixedEmbedding.mixedSpace F) ℂ) y).comp h1
  have e : (fun t => T t (tens (evI F) ⇑f r) x) = fun t => tens (evI F) ⇑(c t) r x := by
    funext t; rw [hc t]
  rw [e, hasDerivAt_iff_tendsto_slope]
  refine ((((ev _).tendsto g).comp hlim).mul_const (r x)).congr' (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply, tens]
  rw [slope_def_module, hc0]
  simp only [SchwartzMap.smul_apply, SchwartzMap.sub_apply, sub_zero, Complex.real_smul, smul_eq_mul]
  ring

end

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}

theorem om_prod_one (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd) (a b : UA σ Y.J) (Φ : (Fin n × Fin d → AF F) → ℂ) :
    om (a * b, 1) Φ = om (a, 1) (om (b, 1) Φ) := by
  have e : ((a * b, (1 : UA σ Wd.J)) : UA σ Y.J × UA σ Wd.J) = (a, 1) * (b, 1) := by
    simp [Prod.mk_mul_mk]
  rw [e, map_mul, Module.End.mul_apply]

theorem om_one_one (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd) (Φ : (Fin n × Fin d → AF F) → ℂ) :
    om ((1 : UA σ Y.J), (1 : UA σ Wd.J)) Φ = Φ := by
  rw [show ((1 : UA σ Y.J), (1 : UA σ Wd.J)) = (1 : UA σ Y.J × UA σ Wd.J) from rfl, map_one, Module.End.one_apply]

end GlobalTheory.LineAdd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicModelInvariantSub
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.KFinAlg

def tensDeg (F : Type) [Field F] [NumberField F] (P Q R S D : ℕ) : Submodule ℂ (GlobalTheory.RealLift.Tens F P Q R S) :=
  LinearMap.range (PiTensorProduct.map fun _ : InfinitePlace F =>
    (MvPolynomial.restrictTotalDegree (Formalism.BasicNotions.TH.Ix P Q × Formalism.BasicNotions.TH.Ix R S) ℂ D).subtype)

theorem tensDeg_mono {F : Type} [Field F] [NumberField F] {P Q R S D D' : ℕ} (h : D ≤ D') :
    tensDeg F P Q R S D ≤ tensDeg F P Q R S D' := by
  have hi : MvPolynomial.restrictTotalDegree (Formalism.BasicNotions.TH.Ix P Q × Formalism.BasicNotions.TH.Ix R S) ℂ D ≤
      MvPolynomial.restrictTotalDegree _ ℂ D' := fun x hx => by
    rw [MvPolynomial.mem_restrictTotalDegree] at hx ⊢; omega
  rintro _ ⟨t, rfl⟩
  refine ⟨PiTensorProduct.map (fun _ => Submodule.inclusion hi) t, ?_⟩
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  rfl

theorem exists_tensDeg {F : Type} [Field F] [NumberField F] {P Q R S : ℕ} (T : GlobalTheory.RealLift.Tens F P Q R S) :
    ∃ D, T ∈ tensDeg F P Q R S D := by
  classical
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    refine ⟨Finset.univ.sup fun w => (m w).totalDegree, r • PiTensorProduct.tprod ℂ (fun w =>
      (⟨m w, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 (Finset.le_sup (f := fun w => (m w).totalDegree)
        (Finset.mem_univ w))⟩ : MvPolynomial.restrictTotalDegree _ ℂ _)), ?_⟩
    simp [PiTensorProduct.map_tprod]
  | add x y hx hy =>
    obtain ⟨D₁, h₁⟩ := hx
    obtain ⟨D₂, h₂⟩ := hy
    exact ⟨max D₁ D₂, Submodule.add_mem _ (tensDeg_mono (le_max_left _ _) h₁) (tensDeg_mono (le_max_right _ _) h₂)⟩

theorem exp_stable {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (hU : GlobalTheory.RealLift.IsExp L U)
    (N : Submodule ℂ V) (hN : ∀ y ∈ N, L y ∈ N) : ∀ y ∈ N, U y ∈ N := by
  intro y hy
  by_contra hne
  obtain ⟨l, hl1, hl2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hne inferInstance
  have hpow : ∀ m : ℕ, (L ^ m) y ∈ N := by
    intro m
    induction m with
    | zero => simpa using hy
    | succ m ih => rw [pow_succ', Module.End.mul_apply]; exact hN _ ih
  have hz : ∀ m : ℕ, ((m.factorial : ℂ))⁻¹ * l ((L ^ m) y) = 0 := fun m => by
    have hm : l ((L ^ m) y) ∈ N.map l := Submodule.mem_map_of_mem (hpow m)
    rw [hl2, Submodule.mem_bot] at hm
    rw [hm, mul_zero]
  have h1 := hU y l
  simp only [hz] at h1
  exact hl1 (h1.unique hasSum_zero)

def pureL {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F]
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' c f := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

end GlobalTheory.SquareAgree.KFinAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaContinuation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ThetaRealDeriv

theorem schr_comp_apply {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) (x : κ → R) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ w' Φ) x =
      ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) * GlobalTheory.WeilM.schr ψ (w + w') Φ x := by
  simp only [GlobalTheory.WeilM.schr, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  rw [dotProduct_comm w'.1 w.2]
  first
    | linear_combination (w.1 ⬝ᵥ w'.2) * invOf_mul_self (2 : R)
    | linear_combination (-(w.1 ⬝ᵥ w'.2)) * invOf_mul_self (2 : R)

theorem exists_transpose_mul_equiv {A : Type} [CommRing A] {α β γ : Type} [Fintype β] [DecidableEq β] (e : γ ≃ α)
    {G H : Matrix β β A} (hHG : H * G = 1) :
    ∃ T : Matrix β γ A ≃+ Matrix α β A, (∀ u, T u = uᵀ.submatrix e.symm id * G) ∧
      ∀ u, ((T u * H)ᵀ).submatrix id e = u := by
  have hGH : G * H = 1 := mul_eq_one_comm.1 hHG
  have hl : ∀ u : Matrix β γ A, ((uᵀ.submatrix e.symm id * G * H)ᵀ).submatrix id e = u := fun u => by
    rw [Matrix.mul_assoc, hGH, Matrix.mul_one]
    ext i j
    simp
  refine ⟨⟨⟨fun u => uᵀ.submatrix e.symm id * G, fun x => ((x * H)ᵀ).submatrix id e, hl, fun x => ?_⟩, fun u v => ?_⟩,
    fun _ => rfl, hl⟩
  · show ((((x * H)ᵀ).submatrix id e)ᵀ).submatrix e.symm id * G = x
    have : ((((x * H)ᵀ).submatrix id e)ᵀ).submatrix e.symm id = x * H := by
      ext i j
      simp only [submatrix_apply, transpose_apply, id, Equiv.apply_symm_apply]
    rw [this, Matrix.mul_assoc, hHG, Matrix.mul_one]
  · show (u + v)ᵀ.submatrix e.symm id * G = uᵀ.submatrix e.symm id * G + vᵀ.submatrix e.symm id * G
    rw [← Matrix.add_mul]
    rfl

theorem finPart_realAd_smul (D : D7) (t : ℝ) (y : AE D) :
    finPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • y) = 0 := by
  have h0 : finPart D (algebraMap (AF D.host.F) (AE D) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t)) = 0 := by
    show ((0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    exact TensorProduct.zero_tmul _ _
  rw [Algebra.smul_def, map_mul, h0, zero_mul]


set_option maxHeartbeats 1600000 in
theorem exists_line (D : D7) (S X : HSp D) {d : ℕ} (e : Fin d ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (hBs : Bs.IsGood D.sp.cm.sig)
    (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d)
    (hVJ : Vs.J = -S.gram) (hJW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    (hV : ∀ i j, D.sp.cm.sig (Vs.J j i) = Vs.J i j)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws) (u₀ : Matrix (Fin S.rank) (Fin d) (AE D))
    (Φ Φ₁ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (hΦ : Φ ∈ GlobalTheory.WeilM.schA D.host.F _)
    (h1 : Φ₁ ∈ GlobalTheory.WeilM.schA D.host.F _)
    (hd : ∀ x, HasDerivAt (fun t : ℝ => M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) Φ x) (Φ₁ x) 0) :
    ∃ L : ℝ →+ WO S X, Continuous L ∧ (∀ t, (L t).map (finPart D) = 0) ∧
      GlobalTheory.TripleRead.thO M Bs.ψ S.gram e Φ₁ =
        fun x => deriv (fun t : ℝ => heisO Bs.ψ S X (L t) (GlobalTheory.TripleRead.thO M Bs.ψ S.gram e Φ) x) 0 := by
  have hF : IsTotallyReal D.host.F := hBs.cm.1
  have hψc : IsCharAF D.host.F Bs.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hBs.std
  have hdet : IsUnit S.gram.det := (Formalism.L2.Theta.gram_det_ne S).isUnit
  have hHG : (S.gram⁻¹).map (incA D) * S.gram.map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hG : (S.gram.map (incA D)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = (S.gram.map (incA D))ᵀ := by
    ext i j
    have h := hV j i
    rw [hVJ, Matrix.neg_apply, Matrix.neg_apply, map_neg, neg_inj] at h
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig (incA D (S.gram i j)) = incA D (S.gram j i)
    rw [← h]
    rfl
  obtain ⟨cS, hc, hci⟩ := exists_transpose_mul_equiv e (α := Fin X.rank) hHG
  have hth : ∀ Ψ u, GlobalTheory.TripleRead.thO M Bs.ψ S.gram e Ψ (cS u) = GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u Ψ) :=
    fun Ψ u => congrArg (fun v => GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ v Ψ)) (hci u)
  obtain ⟨co, hco⟩ := GlobalTheory.SquareAgree.exists_darboux_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e.symm
    (X.gram.map (incA D)) (incA D D.host.xi0) hHG hG (JV := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J)
    (JW := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (JA := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
    (JB := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹))
    (by rw [hVJ]; exact Matrix.map_neg _ (map_neg (incA D)) _) (by rw [hJW]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) rfl
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) M.co cS hc
  have hform : ∀ w w' : Matrix (Fin S.rank) (Fin d) (AE D), symplO S X (cS w) (cS w') =
      (M.co.e w).1 ⬝ᵥ (M.co.e w').2 - (M.co.e w').1 ⬝ᵥ (M.co.e w).2 := by
    intro w w'
    rw [← GlobalTheory.WeilSchrodinger.symp_eq_symplO D S X X.gramᵀ (D.host.xi0 • S.gram⁻¹) 1 rfl
      (one_smul _ _), co.form, hco, hco]
  have hcs : ∀ (a : AF D.host.F) (v : Matrix (Fin S.rank) (Fin d) (AE D)), cS (a • v) = a • cS v := by
    intro a v
    rw [hc, hc, ← Matrix.smul_mul]
    rfl
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) = ⅟(2 : AF D.host.F) :=
    (invOf_eq_right_inv (by rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]; norm_num)).symm
  refine ⟨AddMonoidHom.mk' (fun t => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • cS u₀) fun s t => by
    rw [GlobalTheory.ThetaLineDeriv.realAd_add, add_smul], ?_, fun t => ?_, funext fun x => ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun t : ℝ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • cS u₀ i j
    exact (GlobalTheory.ThetaLineDeriv.continuous_realAd (F := D.host.F)).fun_smul continuous_const
  · ext i j
    exact finPart_realAd_smul D t (cS u₀ i j)
  obtain ⟨u, rfl⟩ := cS.surjective x
  have hkey : ∀ t : ℝ, heisO Bs.ψ S X (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • cS u₀)
      (GlobalTheory.TripleRead.thO M Bs.ψ S.gram e Φ) (cS u) =
      GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ u (M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) Φ)) := by
    intro t
    rw [← hcs]
    set u' := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀
    have e1 : ∀ x, M.co.rho Bs.ψ u (M.co.rho Bs.ψ u' Φ) x =
        Bs.ψ (⅟(2 : AF D.host.F) * ((M.co.e u).1 ⬝ᵥ (M.co.e u').2 - (M.co.e u').1 ⬝ᵥ (M.co.e u).2)) *
          M.co.rho Bs.ψ (u + u') Φ x := by
      intro x
      simp only [GlobalTheory.WeilM.Darboux.rho, map_add (f := _)]
      exact schr_comp_apply Bs.ψ _ _ _ x
    simp only [heisO]
    rw [← map_add (f := _), hth]
    simp only [GlobalTheory.WeilM.thetaSum, e1, tsum_mul_left]
    rw [symplOH, hform, h2]
  rw [hth]
  have hder := GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho M.co Bs.ψ hF hψc u₀ _ hΦ _ h1 hd u
  exact (hder.deriv.symm.trans (congrArg (fun g => deriv g 0) (funext hkey)).symm)


end GlobalTheory.ThetaRealDeriv

end
end

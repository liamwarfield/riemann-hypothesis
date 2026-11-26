module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterSubgroupTransposeGramRealPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxGraphGraphHeis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RouteBigVertexKernelProductEqConstMulThetaKernel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsRelevantSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbeddingColumnLatticeIff
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbeddingColumnLatticeIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.UnitaryEmbeddingLine

variable {D : D7}

theorem tmul_mul_inc (α : AF D.host.F) (b x : D.host.E) :
    (α ⊗ₜ[D.host.F] b : AE D) * incA D x = α ⊗ₜ[D.host.F] (b * x) := by
  change (α ⊗ₜ[D.host.F] b) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x : AE D) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem exists_coeff {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0) (p : Fin c) :
    ∃ r : Fin B.rank → D.host.E, ∀ (y : Fin A.rank → D.host.E) (u : Fin c → D.host.E),
      r ⬝ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) = u p := by
  have hG : B.gramᴴ = B.gram := Matrix.ext fun i j => B.herm.eq _ _
  have h1 : d.aᴴ * B.gram * d.a = antiDiagonalSignGramMatrix c ε := d.gram
  have h2 : (frameMat B A d.ι)ᴴ * B.gram * d.a = 0 := d.perp
  have h3 : d.aᴴ * B.gram * frameMat B A d.ι = 0 := by
    have := congrArg Matrix.conjTranspose h2
    rw [Matrix.conjTranspose_zero, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hG,
      Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc] at this
    exact this
  have hκ : antiDiagonalSignGramMatrix c ε p.rev p ≠ 0 := by
    have := p.2
    have e : p.rev.1 + p.1 + 1 = c := by rw [Fin.val_rev]; omega
    simp only [antiDiagonalSignGramMatrix, if_pos e]
    split_ifs
    · exact hε
    · exact one_ne_zero
  refine ⟨(antiDiagonalSignGramMatrix c ε p.rev p)⁻¹ • (d.aᴴ * B.gram) p.rev, fun y u => ?_⟩
  have e : (d.aᴴ * B.gram) p.rev ⬝ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) =
      ((d.aᴴ * B.gram) *ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u)) p.rev := rfl
  rw [smul_dotProduct, e, mulVec_add, mulVec_mulVec, mulVec_mulVec, h1, h3, zero_mulVec, zero_add]
  have e2 : (antiDiagonalSignGramMatrix c ε *ᵥ u) p.rev = antiDiagonalSignGramMatrix c ε p.rev p * u p := by
    show ∑ q, antiDiagonalSignGramMatrix c ε p.rev q * u q = _
    refine Finset.sum_eq_single p (fun q _ hq => ?_) (by simp)
    have := p.2
    have hne : ¬ (p.rev.1 + q.1 + 1 = c) := by
      intro h; apply hq; apply Fin.ext; rw [Fin.val_rev] at h; omega
    simp only [antiDiagonalSignGramMatrix, if_neg hne, zero_mul]
  rw [e2, smul_eq_mul, inv_mul_cancel_left₀ hκ]

def formHom {R : Type} [CommRing R] {n : ℕ} (r : Fin n → R) : (Fin n → R) →+ R where
  toFun y := ∑ k, y k * r k
  map_zero' := by simp
  map_add' x y := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

def lineHom {R : Type} [CommRing R] {n : ℕ} (a : Fin n → R) : R →+ (Fin n → R) where
  toFun s := fun k => s * a k
  map_zero' := by funext k; simp
  map_add' x y := by funext k; simp only [Pi.add_apply, add_mul]

theorem form_line {K R : Type} [CommRing K] [CommRing R] (f : K →+* R) {n : ℕ} (r a : Fin n → K) (h : r ⬝ᵥ a = 1) (s : R) :
    formHom (fun k => f (r k)) (fun k => s * f (a k)) = s := by
  show ∑ k, s * f (a k) * f (r k) = s
  simp only [mul_assoc, ← map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.mul_sum, ← map_sum]
  have : ∑ k, a k * r k = 1 := by
    rw [← h, dotProduct]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [this, map_one, mul_one]

theorem col_eq {K : Type} [CommRing K] {n k c : ℕ} (M : Matrix (Fin n) (Fin k) K) (a : Matrix (Fin n) (Fin c) K) (p : Fin c)
    (b : K) : (fun i => b * a i p) = M *ᵥ 0 + a *ᵥ Pi.single p b := by
  funext k; simp [mul_comm]

theorem line_mp {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D)
    (S : Set D.host.E) (I : GlobalTheory.SeeSaw.FI D) (hε : ε ≠ 0) (hI : ∀ a ∈ S, ∀ b ∈ 𝔟 p, a * b ∈ I) (s : AE D)
    (h : (fun k => s * incA D (d.a k p)) ∈ GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v)) : s ∈ GlobalTheory.SeeSaw.idV I v := by
  obtain ⟨r, hr⟩ := exists_coeff d hε p
  have key : GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v) ≤ (GlobalTheory.SeeSaw.idV I v).comap (formHom fun k => incA D (r k)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hαv, a, ha, x, ⟨y0, -, u, hu, hx⟩, rfl⟩
    have e : ∑ k, ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * x k) : AE D) * incA D (r k) =
        (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * u p) := by
      rw [Finset.sum_congr rfl fun k _ => tmul_mul_inc (pairA D.host.F 0 α) (a * x k) (r k),
        ← TensorProduct.tmul_sum, ← hr y0 u, ← hx, dotProduct, Finset.mul_sum]
      exact congrArg _ (Finset.sum_congr rfl fun k _ => by ring)
    have h2 : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * u p) ∈ GlobalTheory.SeeSaw.idV I v :=
      AddSubgroup.subset_closure ⟨α, hα, hαv, _, hI a ha _ (hu p), rfl⟩
    rw [← e] at h2
    exact h2
  have h1 := hr 0 (Pi.single p 1)
  rw [← col_eq, Pi.single_eq_same] at h1
  simp only [one_mul] at h1
  have := AddSubgroup.mem_comap.1 (key h)
  rwa [form_line (incA D) r (fun k => d.a k p) h1 s] at this

theorem line_mpr {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D)
    (S : Set D.host.E) (I : GlobalTheory.SeeSaw.FI D)
    (hI' : ∀ C : D.host.E → Prop, (∀ a ∈ S, ∀ b ∈ 𝔟 p, C (a * b)) → (∀ x y, C x → C y → C (x + y)) → ∀ z ∈ I, C z)
    (s : AE D) (h : s ∈ GlobalTheory.SeeSaw.idV I v) :
    (fun k => s * incA D (d.a k p)) ∈ GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v) := by
  have key : GlobalTheory.SeeSaw.idV I v ≤ (GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v)).comap (lineHom fun k => incA D (d.a k p)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hαv, z, hz, rfl⟩
    refine hI' (fun z => ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] z : AE D) ∈
      (GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v)).comap (lineHom fun k => incA D (d.a k p))) ?_ ?_ z hz
    · intro a ha b hb
      refine AddSubgroup.mem_comap.2 (AddSubgroup.subset_closure ⟨α, hα, hαv, a, ha, fun k => b * d.a k p,
        ⟨0, Λ.zero_mem, Pi.single p b, fun q => ?_, col_eq _ _ p b⟩, ?_⟩)
      · by_cases hq : q = p
        · subst hq; rwa [Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne hq]; exact (𝔟 q).zero_mem
      · funext k
        exact (tmul_mul_inc _ _ _).trans (congrArg _ (mul_assoc _ _ _))
    · intro x y hx hy
      rw [TensorProduct.tmul_add]
      exact add_mem hx hy
  exact AddSubgroup.mem_comap.1 (key h)

theorem line_gen {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D)
    (S : Set D.host.E) (I : GlobalTheory.SeeSaw.FI D) (hε : ε ≠ 0) (hI : ∀ a ∈ S, ∀ b ∈ 𝔟 p, a * b ∈ I)
    (hI' : ∀ C : D.host.E → Prop, (∀ a ∈ S, ∀ b ∈ 𝔟 p, C (a * b)) → (∀ x y, C x → C y → C (x + y)) → ∀ z ∈ I, C z)
    (s : AE D) :
    (fun k => s * incA D (d.a k p)) ∈ GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV I v :=
  ⟨line_mp d Λ 𝔟 p v S I hε hI s, line_mpr d Λ 𝔟 p v S I hI' s⟩

theorem embedding_line_mem_lattice_iff : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε), ε ≠ 0 → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D) (s : AE D), (((fun k => s * incA D (d.a k p)) ∈ latV B (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV (𝔟 p) v) ∧ ((fun k => s * incA D (d.a k p)) ∈ latA B (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA * 𝔟 p) v)) := by
  intro D A B c ε d hε Λ 𝔟 p v s
  refine ⟨line_gen d Λ 𝔟 p v {1} (𝔟 p) hε ?_ ?_ s, line_gen d Λ 𝔟 p v {a | a ∈ D.host.AA} _ hε ?_ ?_ s⟩
  · rintro a rfl b hb; rwa [one_mul]
  · intro C h _ z hz
    have := h 1 rfl z hz
    rwa [one_mul] at this
  · intro a ha b hb; exact FractionalIdeal.mul_mem_mul ha hb
  · intro C h h' z hz
    exact FractionalIdeal.mul_induction_on hz h h'

end GlobalTheory.AscFin.UnitaryEmbeddingLine

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbeddingColumnLatticeIffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedding_column_lattice_iff : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε), ε ≠ 0 → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D) (s : AE D), (((fun k => s * incA D (d.a k p)) ∈ latV B (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV (𝔟 p) v) ∧ ((fun k => s * incA D (d.a k p)) ∈ latA B (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA * 𝔟 p) v)) := by
  first | exact @GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff | exact GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff | (intros; apply GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HTensMixHalfS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.SmallDat.VacFix

theorem hTens_mixHalfS {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ} (e : Num G i j)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e) (ε : AE D)
    (hε : ε * cA D ε = 0) (γ : GlobalTheory.SmallDat.PtS G i j) (hγ : γ ∈ mixHalfS e ε) :
    hTens (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ = 0 := by
  refine GlobalTheory.BigDat.VacFix.hTens_eq_zero (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) GlobalTheory.DualPairCheck.cA_cA e _ _
    (fun a b => ?_) (fun a b => ?_) ε hε γ (fun a b => ?_) (fun a b => ?_)
  · exact (congrArg (incA D) ((congrFun (congrFun hWW _) _).trans (GlobalTheory.BigDat.VacFix.skewGram_inl_inr _ _ e a b))).trans (map_zero _)
  · exact (congrArg (incA D) ((congrFun (congrFun hWW _) _).trans (GlobalTheory.BigDat.VacFix.skewGram_inr_inl _ _ e a b))).trans (map_zero _)
  · exact GlobalTheory.BigDat.VacFix.isHalf_of_mulG (spW₁ G i j) ε (colV e γ)ᵀ hγ.1 b a
  · refine GlobalTheory.BigDat.VacFix.isHalf_of_mulG (spV₁ G i j) ε ((γ.submatrix id fun k => e (.inr k)).map (cA D)) (fun a b => ?_) a b
    exact neg_injective ((mul_neg _ _).symm.trans (hγ.2 a b))

theorem vac_fixed : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : ℕ) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X → IsTriple Bs Γ X om om' →
    ∀ v : Pl D.host.F, (∀ u ∈ GlobalTheory.SmallDat.latPtS t e v, u ∈ latAtV Γ.V' Γ.W v) →
      ∀ γ ∈ GlobalTheory.SmallDat.genPtS t e v, Acts (evFin D.host.F v) (Γ.M'.co.rho W.ψ γ) (Γ.M'.vac v) (Γ.M'.vac v) := by
  intro D T L sc G W M t i j e Bs Γ X om om' h hT v hL γ hγ
  obtain ⟨-, -, θ, -, hθ⟩ := hT.geo.hM'.vac v
  have h1 := hθ γ (hL γ (GlobalTheory.SmallDat.genPtS_subset t e v hγ))
  have h2 : Bs.ψ (⅟(2 : AF D.host.F) * symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)
      (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) = 1 := by
    rcases hγ with ⟨γ', hγ', rfl⟩ | ⟨-, ε, hε, hγ⟩
    · exact GlobalTheory.BigDat.VacFix.psi_double _ Bs Γ.V' Γ.W _ _ _ _ hT.base hT.geo.hV' hT.geo.hW v θ γ' (hL γ' hγ')
    · unfold symp
      rw [hTens_mixHalfS e Γ h.JWW ε hε.2.1 γ hγ, mul_zero, map_zero, mul_zero, AddChar.map_zero_eq_one]
  rw [h2, one_smul, h.ψ] at h1
  exact h1

end GlobalTheory.SmallDat.VacFix

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeRowMulVecMemModulusScaledCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeRowMulVecMemModulusScaledCompletion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.DepthRowLem

variable {D : D7}

theorem pairA_mul (α β : Af D.host.F) : pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) :=
  Prod.ext (mul_zero _) rfl

theorem intAf_mul {α β : Af D.host.F} (hα : α ∈ intAf D.host.F) (hβ : β ∈ intAf D.host.F) : α * β ∈ intAf D.host.F :=
  fun v => by rw [map_mul]; exact mul_mem (hα v) (hβ v)

theorem mulVec_mem_smul {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (𝔪 : Ideal (𝓞 D.host.E)) {x : Matrix (Fin m) (Fin n) D.host.E}
    (hx : x ∈ 𝔪 • homLat Λ Λ') {y : Fin n → D.host.E} (hy : y ∈ Λ) : x *ᵥ y ∈ 𝔪 • Λ' := by
  refine Submodule.smul_induction_on hx (fun a ha h hh => ?_) (fun x x' hx hx' => ?_)
  · rw [smul_mulVec]; exact Submodule.smul_mem_smul ha (hh y hy)
  · rw [add_mulVec]; exact add_mem hx hx'


open GlobalTheory.FinPl in
theorem tmul_mem_latMul {T : HSp D} {Λ' : Lat T} (𝔪 : Ideal (𝓞 D.host.E)) {P : Pl D → Prop} {γ : Af D.host.F}
    (hγ : γ ∈ intAf D.host.F) (hγP : ∀ v, ¬ P v → evalV D.host.F v γ = 0) {w : Fin T.rank → D.host.E} (hw : w ∈ 𝔪 • Λ') :
    (fun r => pairA D.host.F 0 γ ⊗ₜ[D.host.F] w r) ∈
      latMul T {a | a ∈ ((𝔪 : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)} Λ' P := by
  refine Submodule.smul_induction_on hw (fun m hm l hl => ?_) (fun w w' hw hw' => ?_)
  · refine AddSubgroup.subset_closure ⟨γ, hγ, hγP, algebraMap (𝓞 D.host.E) D.host.E m,
      (FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).2 ⟨m, hm, rfl⟩, l, hl, ?_⟩
    funext r
    simp only [Pi.smul_apply, Algebra.smul_def]
  · have : (fun r => pairA D.host.F 0 γ ⊗ₜ[D.host.F] (w + w') r) =
        (fun r => pairA D.host.F 0 γ ⊗ₜ[D.host.F] w r) + (fun r => pairA D.host.F 0 γ ⊗ₜ[D.host.F] w' r) := by
      funext r; simp only [Pi.add_apply, TensorProduct.tmul_add]
    rw [this]; exact add_mem hw hw'


open GlobalTheory.FinPl in
theorem mulVec_mem_latMul {S T : HSp D} {Λ : Lat S} {Λ' : Lat T} (𝔪 : Ideal (𝓞 D.host.E)) {P : Pl D → Prop}
    {Z : Mx D T.rank S.rank} (hZ : Z ∈ hatMx (𝔪 • homLat Λ Λ')) {y : Fin S.rank → AE D} (hy : y ∈ latV S Λ P) :
    Z *ᵥ y ∈ latMul T {a | a ∈ ((𝔪 : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)} Λ' P := by
  change y ∈ AddSubgroup.closure _ at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβ, hβP, a, ha, y₀, hy₀, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at ha
    subst ha
    change Z ∈ AddSubgroup.closure _ at hZ
    induction hZ using AddSubgroup.closure_induction with
    | mem Z hZ =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hZ
      have e : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] x i j) *ᵥ
          (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * y₀ i)) =
          fun r => pairA D.host.F 0 (α * β) ⊗ₜ[D.host.F] (x *ᵥ y₀) r := by
        funext r
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, pairA_mul, one_mul,
          ← TensorProduct.tmul_sum]
      rw [e]
      refine tmul_mem_latMul 𝔪 (intAf_mul hα hβ) (fun v hv => ?_) (mulVec_mem_smul 𝔪 hx hy₀)
      rw [map_mul, hβP v hv, mul_zero]
    | zero => rw [zero_mulVec]; exact zero_mem _
    | add Z Z' _ _ h h' => rw [add_mulVec]; exact add_mem h h'
    | neg Z _ h => rw [neg_mulVec]; exact neg_mem h
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [mulVec_add]; exact add_mem h h'
  | neg y _ h => rw [mulVec_neg]; exact neg_mem h

end GlobalTheory.DepthRowLem

theorem GlobalTheory.DepthRowLem.latRow_mulVec : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ Y ∈ latRow G i, ∀ (v : GlobalTheory.FinPl.Pl D) (y : Fin (G.V (.grid (i + 1) 0)).rank → AE D), y ∈ latV _ (G.Λ (.grid (i + 1) 0)) (· = v) → (e • Y) *ᵥ y ∈ GlobalTheory.FinPl.latMul _ {a | a ∈ ((G.modul : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)} (G.Λ (.grid i 0)) (· = v) := by
  intro D _ T L μ0 _ sc G W M _ i _ e he Y hY v y hy
  exact GlobalTheory.DepthRowLem.mulVec_mem_latMul _ (hY.2 e he) hy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeRowMulVecMemModulusScaledCompletionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthLatticeRow_mulVec_mem_modulus_scaledCompletion : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ Y ∈ latRow G i, ∀ (v : GlobalTheory.FinPl.Pl D) (y : Fin (G.V (.grid (i + 1) 0)).rank → AE D), y ∈ latV _ (G.Λ (.grid (i + 1) 0)) (· = v) → (e • Y) *ᵥ y ∈ GlobalTheory.FinPl.latMul _ {a | a ∈ ((G.modul : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)} (G.Λ (.grid i 0)) (· = v) := by
  first | exact @GlobalTheory.DepthRowLem.latRow_mulVec | exact GlobalTheory.DepthRowLem.latRow_mulVec | (intros; apply GlobalTheory.DepthRowLem.latRow_mulVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulOfMapsInlMemS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.SmallDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem ofMaps_inlS (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) (p : Fin (spW₁ G i j).rank)
    (k : Fin (spV G i j).rank) : ofMaps t e x p (e (.inl k)) = GlobalTheory.BigDat.divG (spW₁ G i j) x.1 k p := by
  simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, transpose_apply]

theorem ofMaps_inrS (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) (p : Fin (spW₁ G i j).rank)
    (k : Fin (spV₁ G i j).rank) : ofMaps t e x p (e (.inr k)) = cA D (GlobalTheory.BigDat.divG (spV₁ G i j) (-x.2) p k) := by
  simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply]

theorem ofMaps_genA (t : T) (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spW₁ G i j).rank → D.host.E)
    (r : Fin (spV G i j).rank → D.host.E) :
    ofMaps t e (Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (spW₁ G i j).gram k j'), 0) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star s) (Sum.elim (a • r) 0 ∘ e.symm)) := by
  ext p q
  obtain ⟨k | k, rfl⟩ := e.surjective q
  · refine (ofMaps_inlS t e _ p k).trans ((GlobalTheory.BigDat.divG_gen (spW₁ G i j) β a s r k p).trans ?_)
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, mul_comm]
    rfl
  · refine (ofMaps_inrS t e _ p k).trans ?_
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, neg_zero,
      GlobalTheory.BigDat.divG_zero, Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
    exact map_zero _

theorem ofMaps_genB (t : T) (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spV₁ G i j).rank → D.host.E)
    (r : Fin (spW₁ G i j).rank → D.host.E) :
    ofMaps t e (0, Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (negSp (spV₁ G i j)).gram k j')) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star r) (Sum.elim 0 (star (a • star s)) ∘ e.symm)) := by
  have hneg : -(Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (negSp (spV₁ G i j)).gram k j') :
      Matrix _ _ (AE D)) = Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (spV₁ G i j).gram k j') := by
    ext p q
    simp only [Matrix.neg_apply, of_apply, negSp_gram, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_neg,
      TensorProduct.tmul_neg]
  ext p q
  obtain ⟨k | k, rfl⟩ := e.surjective q
  · refine (ofMaps_inlS t e _ p k).trans ((congrFun (congrFun (GlobalTheory.BigDat.divG_zero (spW₁ G i j)) k) p).trans ?_)
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl,
      Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
    rfl
  · refine (ofMaps_inrS t e _ p k).trans ?_
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, hneg,
      GlobalTheory.BigDat.divG_gen]
    change β ⊗ₜ[D.host.F] star (a * r p * star (s k)) = β ⊗ₜ[D.host.F] (star (r p) * star (a * star (s k)))
    rw [← star_mul']
    congr 2
    ring

theorem smul_ofMaps_inl_memS {t : T} {e : Num G i j} {Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} (h : IsDoublyCompatible t i j e Bs Γ X) (v : Pl D.host.F) {x : HomA G t i j}
    (hx : x ∈ latA G t i j) : GlobalTheory.LatVac.liftV v 1 • ofMaps t e (x, 0) ∈ latAtV Γ.V' Γ.W v := by
  refine GlobalTheory.BigDat.map_mem_of_closure ((DistribSMul.toAddMonoidHom (PtS G i j) (GlobalTheory.LatVac.liftV v 1)).comp
    ((maps t e).symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inl _ _))) ?_ hx
  rintro _ ⟨α, hα, -, a, ha, s, hs, r, hr, rfl⟩
  exact (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV Γ.V' Γ.W v) (ofMaps_genA t e (pairA _ 0 α) a s r)).mpr
    (GlobalTheory.BigDat.one_smul_gen_mem _ _ v hα (h.2.ge (GlobalTheory.BigDat.star_mem_conjSub hs))
      (h.1.2.1.ge (GlobalTheory.BigDat.pair_mem e (GlobalTheory.BigDat.smul_mem_scLat_of_mem ha hr) (zero_mem _))))

theorem smul_ofMaps_inr_memS {t : T} {e : Num G i j} {Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} (h : IsDoublyCompatible t i j e Bs Γ X) (v : Pl D.host.F) {x : HomB G i j}
    (hx : x ∈ latB G i j) : GlobalTheory.LatVac.liftV v 1 • ofMaps t e (0, x) ∈ latAtV Γ.V' Γ.W v := by
  refine GlobalTheory.BigDat.map_mem_of_closure ((DistribSMul.toAddMonoidHom (PtS G i j) (GlobalTheory.LatVac.liftV v 1)).comp
    ((maps t e).symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inr _ _))) ?_ hx
  rintro _ ⟨α, hα, -, a, ha, s, hs, r, hr, rfl⟩
  exact (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV Γ.V' Γ.W v) (ofMaps_genB t e (pairA _ 0 α) a s r)).mpr
    (GlobalTheory.BigDat.one_smul_gen_mem _ _ v hα (h.2.ge (GlobalTheory.BigDat.star_mem_conjSub hr))
      (h.1.2.1.ge (GlobalTheory.BigDat.pair_mem e (zero_mem _)
        (GlobalTheory.BigDat.star_mem_conjSub (GlobalTheory.BigDat.smul_mem_scLat_of_mem ha (GlobalTheory.BigDat.star_mem_conjSub hs))))))

theorem latPtS_le_latAtV : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (i j : ℕ) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E), GlobalTheory.FlipMatch.IsDoublyCompatible t i j e Bs Γ X →
    ∀ v : Pl D.host.F, ∀ u ∈ GlobalTheory.SmallDat.latPtS t e v, u ∈ latAtV Γ.V' Γ.W v := by
  intro D T L sc G t i j e Bs Γ X h v u hu
  obtain ⟨hat, h1, h2⟩ := hu
  have e1 : GlobalTheory.LatVac.liftV v 1 • u = u := by
    have := hat (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  have e2 : u = ofMaps t e (mapA t e u, 0) + ofMaps t e (0, mapB e u) :=
    ((ofMaps_maps t e u).symm.trans (congrArg (ofMaps t e) (Prod.ext (add_zero _).symm (zero_add _).symm))).trans
      (map_add (maps t e).symm (mapA t e u, 0) (0, mapB e u))
  have e3 := add_mem (smul_ofMaps_inl_memS h v h1) (smul_ofMaps_inr_memS h v h2)
  rwa [← smul_add, ← e2, e1] at e3

end GlobalTheory.SmallDat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsFourierTransform
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

open scoped Classical

namespace GlobalTheory.HoweGlobal.Transfer

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}

theorem mem_of_pure {A : Type} [AddCommGroup A] [Module ℂ A] {ι : Type} [Fintype ι] {B : ι → Type}
    [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (S : Submodule ℂ (A ⊗[ℂ] (⨂[ℂ] i, B i)))
    (h : ∀ x φ, x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ ∈ S) : ∀ t, t ∈ S := by
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact S.zero_mem
  | tmul x y =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r φ => rw [TensorProduct.tmul_smul]; exact S.smul_mem r (h x φ)
    | add y z hy hz => rw [TensorProduct.tmul_add]; exact S.add_mem hy hz
  | add s t hs ht => exact S.add_mem hs ht

theorem mem_of_tprod {ι : Type} [Fintype ι] {B : ι → Type} [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)]
    (S : Submodule ℂ (⨂[ℂ] i, B i)) (h : ∀ φ, PiTensorProduct.tprod ℂ φ ∈ S) : ∀ y, y ∈ S := by
  intro y
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r φ => exact S.smul_mem r (h φ)
  | add y z hy hz => exact S.add_mem hy hz

def ext (M : Model σ Y W) (T : Finset (Pl F)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ :=
  fun v => if h : v ∈ T then ((φ ⟨v, h⟩ : ↥(SB (Fin n × Fin d → Fv F v))) : (Fin n × Fin d → Fv F v) → ℂ) else M.vac v

variable (M : Model σ Y W) (T : Finset (Pl F))

theorem ext_of_mem (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : T) :
    ext M T φ v.1 = (φ v : (Fin n × Fin d → Fv F v.1) → ℂ) := by
  simp [ext, v.2]

theorem ext_of_not_mem (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : Pl F) (hv : v ∉ T) :
    ext M T φ v = M.vac v := by
  simp [ext, hv]

theorem ext_mem_SB {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1)))
    (v : Pl F) : ext M T φ v ∈ SB _ := by
  by_cases hv : v ∈ T
  · rw [ext_of_mem M T φ ⟨v, hv⟩]; exact (φ ⟨v, hv⟩).2
  · rw [ext_of_not_mem M T φ v hv]; exact (hM.vac v).1

theorem ext_vac (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    ∀ᶠ v in Filter.cofinite, ext M T φ v = M.vac v := by
  filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv
  exact ext_of_not_mem M T φ v hv

theorem ext_std {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    ∀ᶠ v in Filter.cofinite, ext M T φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  filter_upwards [ext_vac M T φ, hM.std] with v h1 h2
  rw [h1, h2]

theorem ext_update [DecidableEq T] (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : T)
    (z : ↥(SB (Fin n × Fin d → Fv F v.1))) :
    ext M T (Function.update φ v z) = Function.update (ext M T φ) v.1 (z : (Fin n × Fin d → Fv F v.1) → ℂ) := by
  funext w
  by_cases hw : w ∈ T
  · by_cases hwv : w = v.1
    · subst hwv
      rw [ext_of_mem M T _ v, Function.update_self, Function.update_self]
    · have hne : (⟨w, hw⟩ : T) ≠ v := fun e => hwv (congrArg Subtype.val e)
      rw [ext_of_mem M T _ ⟨w, hw⟩, Function.update_of_ne hwv, Function.update_of_ne hne, ext_of_mem M T _ ⟨w, hw⟩]
  · have hwv : w ≠ v.1 := fun e => hw (e ▸ v.2)
    rw [ext_of_not_mem M T _ w hw, Function.update_of_ne hwv, ext_of_not_mem M T _ w hw]

end GlobalTheory.HoweGlobal.Transfer

end

noncomputable section

open scoped Classical

namespace GlobalTheory.HoweGlobal.Transfer

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (T : Finset (Pl F))

theorem rest_ext {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ) (f : SInf F (Fin n × Fin d))
    (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    Rest (evI F) ⇑f (fun x => ∏ᶠ v, ext M T φ v fun i => evFin F v (x i)) :=
  GlobalTheory.ThK.EvUniqInf.rest_pure f _ (ext_mem_SB M T hM φ) (ext_std M T hM φ)

theorem acts_ext [DecidableEq T] {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ) (f : SInf F (Fin n × Fin d))
    (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : T) (z : ↥(SB (Fin n × Fin d → Fv F v.1)))
    (Op : ((Fin n × Fin d → AF F) → ℂ) → (Fin n × Fin d → AF F) → ℂ)
    (h : Acts (evFin F v.1) Op (φ v : (Fin n × Fin d → Fv F v.1) → ℂ) (z : (Fin n × Fin d → Fv F v.1) → ℂ)) :
    Op (pure f (ext M T φ)) = pure f (ext M T (Function.update φ v z)) := by
  rw [ext_update]
  refine GlobalTheory.ThK.LocalOps.acts_pure v.1 Op f (ext M T φ) _
    (GlobalTheory.TensUniq.pure_mem_schA f _ (ext_mem_SB M T hM φ) (ext_std M T hM φ))
    (GlobalTheory.PureFactor.mulSupport_finite _ (ext_std M T hM φ)) ?_
  simpa only [ext_of_mem] using h

theorem pure_mem_algD {ψ : AddChar (AF F) ℂ} (emb : ∀ w : InfinitePlace F, EmbOver E w) (hM : M.IsGood ψ)
    (f : SInf F (Fin n × Fin d)) (hf : f ∈ M.Pol ψ emb) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    pure f (ext M T φ) ∈ GlobalTheory.SquareAgree.algD M ψ emb :=
  Submodule.subset_span ⟨f, ext M T φ, hf, ext_mem_SB M T hM φ, ext_vac M T φ, rfl⟩

end GlobalTheory.HoweGlobal.Transfer


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnMemLatticeIffIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnMemLatticeIffIdeal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.ChiGrid
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.UnitaryEmbeddingColumns

open GlobalTheory.FinPl GlobalTheory.SeeSaw

theorem gram_star {D : D7} (B : HSp D) (i j : Fin B.rank) : star (B.gram i j) = B.gram j i := by
  have := B.herm.eq (B.frame i) (B.frame j)
  simpa [HSpace.gram, starRingEnd_apply] using this

theorem incA_mul_tmul' {D : D7} (e : D.host.E) (y : AF D.host.F) (z : D.host.E) :
    incA D e * (y ⊗ₜ[D.host.F] z) = y ⊗ₜ[D.host.F] (e * z) := by
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) * (y ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem tmul_mul_incA {D : D7} (y : AF D.host.F) (t e : D.host.E) :
    (y ⊗ₜ[D.host.F] t) * incA D e = y ⊗ₜ[D.host.F] (t * e) := by
  show (y ⊗ₜ[D.host.F] t) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]


set_option maxHeartbeats 1000000 in
theorem mem_idV_of_mem {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D)
    (q : Fin c) (b : AE D)
    (h : (fun k => b * incA D (d.a k q)) ∈ GlobalTheory.FinPl.latV B (d.lat Λ 𝔟) (· = v)) : b ∈ GlobalTheory.SeeSaw.idV (𝔟 q) v := by
  classical
  set r : Fin c := q.rev with hr
  set κ : D.host.E := antiDiagonalSignGramMatrix c ε r q with hκdef
  have hcond : ∀ p : Fin c, (r.1 + p.1 + 1 = c ↔ p = q) := by
    intro p
    have := q.2; have := p.2
    rw [hr, Fin.val_rev, Fin.ext_iff]; omega
  have hκ : κ ≠ 0 := by
    rw [hκdef, antiDiagonalSignGramMatrix, ite_eq_left ((hcond q).2 rfl)]
    split_ifs
    · exact hε
    · exact one_ne_zero
  let π : Fin B.rank → D.host.E := fun j => κ⁻¹ * ∑ l, star (d.a l r) * B.gram l j
  have hπa : ∀ p, ∑ j, π j * d.a j p = if p = q then 1 else 0 := by
    intro p
    have e := congrFun (congrFun d.gram r) p
    simp only [Matrix.mul_apply, Formalism.UG.cT, transpose_apply, map_apply] at e
    have e2 : ∑ j, π j * d.a j p = κ⁻¹ * antiDiagonalSignGramMatrix c ε r p := by
      rw [← e, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [π]
      rw [mul_assoc]
      congr 2
    rw [e2]
    split_ifs with hp
    · subst hp; rw [← hκdef]; exact inv_mul_cancel₀ hκ
    · rw [antiDiagonalSignGramMatrix, ite_eq_right (fun h' => hp ((hcond p).1 h')), mul_zero]
  have hπM : ∀ i, ∑ j, π j * frameMat B A d.ι j i = 0 := by
    intro i
    have e := congrFun (congrFun d.perp i) r
    simp only [Matrix.mul_apply, Formalism.UG.cT, transpose_apply, map_apply, Matrix.zero_apply] at e
    have hsig : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x := fun _ => rfl
    have e3 : ∑ j, π j * frameMat B A d.ι j i =
        κ⁻¹ * ∑ j, ∑ l, star (d.a l r) * B.gram l j * frameMat B A d.ι j i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [π]
      rw [mul_assoc, Finset.sum_mul]
    rw [e3]
    have e4 : ∑ j, ∑ l, star (d.a l r) * B.gram l j * frameMat B A d.ι j i =
        star (∑ l, (∑ x, (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι x i) * B.gram x l) * d.a l r) := by
      simp only [star_sum, star_mul', Finset.sum_mul, hsig, star_star, gram_star]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e4, e, star_zero, mul_zero]
  let Φ : (Fin B.rank → AE D) →+ AE D :=
    { toFun := fun Y => ∑ k, incA D (π k) * Y k
      map_zero' := by simp
      map_add' := fun Y Z => by simp [mul_add, Finset.sum_add_distrib] }
  have hΦ : ∀ Y ∈ latV B (d.lat Λ 𝔟) (· = v), Φ Y ∈ idV (𝔟 q) v := by
    intro Y hY
    induction hY using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, hαv, a, ha, x, hx, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      obtain ⟨y, -, u, hu, rfl⟩ := hx
      have e : Φ (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) i)) =
          pairA D.host.F 0 α ⊗ₜ[D.host.F] u q := by
        show ∑ k, incA D (π k) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) k)) = _
        simp only [incA_mul_tmul', one_mul]
        rw [← TensorProduct.tmul_sum]
        congr 1
        have h1 : ∑ k, π k * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) k =
            ∑ i, (∑ j, π j * frameMat B A d.ι j i) * y i + ∑ p, (∑ j, π j * d.a j p) * u p := by
          simp only [Pi.add_apply, mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
            Finset.sum_mul]
          congr 1
          · rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          · rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        rw [h1]
        simp only [hπM, hπa, zero_mul, Finset.sum_const_zero, zero_add, ite_mul, one_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [e]
      exact AddSubgroup.subset_closure ⟨α, hα, hαv, u q, hu q, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add Y Z _ _ hY hZ => rw [map_add]; exact add_mem hY hZ
    | neg Y _ hY => rw [map_neg]; exact neg_mem hY
  have key := hΦ _ h
  have e : Φ (fun k => b * incA D (d.a k q)) = b := by
    show ∑ k, incA D (π k) * (b * incA D (d.a k q)) = b
    have : ∀ k, incA D (π k) * (b * incA D (d.a k q)) = b * incA D (π k * d.a k q) := fun k => by
      rw [map_mul (incA D) (π k) (d.a k q)]; ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl (fun k _ => this k), ← Finset.mul_sum, ← map_sum, hπa q, ite_eq_left rfl, map_one, mul_one]
  rwa [e] at key


set_option maxHeartbeats 1000000 in
theorem mem_of_mem_idV {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D)
    (q : Fin c) (b : AE D)
    (h : b ∈ GlobalTheory.SeeSaw.idV (𝔟 q) v) : (fun k => b * incA D (d.a k q)) ∈ GlobalTheory.FinPl.latV B (d.lat Λ 𝔟) (· = v) := by
  classical
  let Ψ : AE D →+ (Fin B.rank → AE D) := AddMonoidHom.pi fun k => AddMonoidHom.mulRight (incA D (d.a k q))
  have hle : idV (𝔟 q) v ≤ (latV B (d.lat Λ 𝔟) (· = v)).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hαv, t, ht, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨α, hα, hαv, 1, Set.mem_singleton _, d.a *ᵥ Pi.single q t, ?_, ?_⟩
    · refine ⟨0, Λ.zero_mem, Pi.single q t, fun p => ?_, by simp⟩
      by_cases hp : p = q
      · subst hp; simpa using ht
      · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
    · funext k
      show (pairA D.host.F 0 α ⊗ₜ[D.host.F] t) * incA D (d.a k q) = _
      rw [tmul_mul_incA, one_mul]
      congr 1
      rw [mulVec_single, Pi.smul_apply, op_smul_eq_mul, Matrix.col_apply, mul_comm]
  exact hle h

theorem mem_latV_iff {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D)
    (q : Fin c) (b : AE D) :
    (fun k => b * incA D (d.a k q)) ∈ GlobalTheory.FinPl.latV B (d.lat Λ 𝔟) (· = v) ↔ b ∈ GlobalTheory.SeeSaw.idV (𝔟 q) v :=
  ⟨mem_idV_of_mem d hε Λ 𝔟 v q b, mem_of_mem_idV d Λ 𝔟 v q b⟩

end GlobalTheory.UnitaryEmbeddingColumns

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnMemLatticeIffIdealStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.ChiGrid
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.column_mem_lattice_iff_ideal : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε), ε ≠ 0 → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D) (q : Fin c) (b : AE D), (fun k => b * incA D (d.a k q)) ∈ GlobalTheory.FinPl.latV B (d.lat Λ 𝔟) (· = v) ↔ b ∈ GlobalTheory.SeeSaw.idV (𝔟 q) v := by
  first | exact @GlobalTheory.UnitaryEmbeddingColumns.mem_latV_iff | exact GlobalTheory.UnitaryEmbeddingColumns.mem_latV_iff | (intros; apply GlobalTheory.UnitaryEmbeddingColumns.mem_latV_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatPtSLeClosureAndSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.SmallDatLat

theorem latPtS_le_closure_and_selfDual : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j),
    Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram → Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e → ∀ v : Pl D.host.F,
      GlobalTheory.SmallDat.latPtS t e v ≤ AddSubgroup.closure (GlobalTheory.SmallDat.genPtS t e v) ∧
      ∀ z : GlobalTheory.SmallDat.PtS G i j, At (evFin D.host.F v) z → (z ∈ GlobalTheory.SmallDat.latPtS t e v ↔ ∀ γ ∈ GlobalTheory.SmallDat.latPtS t e v, W.ψ (GlobalTheory.SmallDat.sympS Γ z γ) = 1) := by
  intro D T L sc G μ₀ hL W t i j e Γ hW₁ hWW v
  have s0 := (node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).sd
  have s1 := (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have s2 := (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  refine ⟨GlobalTheory.BigDatLat.le_of_gen (GlobalTheory.SmallDat.maps t e) v _ (fun _ => Iff.rfl) _
    (fun u hu => AddSubgroup.subset_closure (Or.inl ⟨u, hu, rfl⟩))
    fun ε hε u hu h1 h2 => AddSubgroup.subset_closure (Or.inr ⟨hu, ε, hε, h1, h2⟩), fun z hz => ?_⟩
  exact GlobalTheory.BigDatLat.mem_iff_char (GlobalTheory.SmallDat.maps t e) v _ s0 s1 (isSelfDualC_neg s2) s0 (fun _ => Iff.rfl) W.ψ_std
    (GlobalTheory.SmallDat.sympS Γ) (GlobalTheory.SmallDat.sympS_eq t e Γ hW₁ hWW) hz

end GlobalTheory.SmallDatLat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineCmModelSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ArchCont

open scoped SchwartzMap

theorem lintegral_of_integral {l : Type} [Fintype l] (f g : GlobalTheory.RealWeil.Sch l)
    (h : ∫ x, ‖f x‖ ^ 2 = ∫ x, ‖g x‖ ^ 2) : ∫⁻ x, ‖f x‖ₑ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 := by
  have hi : ∀ u : GlobalTheory.RealWeil.Sch l, MeasureTheory.Integrable (fun x => ‖u x‖ ^ 2) MeasureTheory.volume := fun u =>
    (u.memLp 2 MeasureTheory.volume).integrable_norm_pow two_ne_zero
  have e : ∀ u : GlobalTheory.RealWeil.Sch l, ∫⁻ x, ‖u x‖ₑ ^ 2 = ENNReal.ofReal (∫ x, ‖u x‖ ^ 2) := fun u => by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hi u) (.of_forall fun x => by positivity)]
    congr 1
    funext x
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [e, e, h]

end GlobalTheory.ArchCont

namespace GlobalTheory.ArchCont

open scoped SchwartzMap RealInnerProductSpace

end GlobalTheory.ArchCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineCmModelAction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SchwartzSlope

open Filter Topology
open scoped SchwartzMap RealInnerProductSpace

theorem lintegral_of_integral (l : Type) [Fintype l] (f g : GlobalTheory.RealWeil.Sch l)
    (h : ∫ x, ‖f x‖ ^ 2 = ∫ x, ‖g x‖ ^ 2) : ∫⁻ x, ‖f x‖ₑ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 := by
  have key : ∀ u : GlobalTheory.RealWeil.Sch l, ∫ x, ‖u x‖ ^ 2 = (∫⁻ x, ‖u x‖ₑ ^ 2).toReal := by
    intro u
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖u x‖ ^ 2) (Eventually.of_forall fun x => sq_nonneg ‖u x‖)
      ((by fun_prop : Continuous fun x => ‖u x‖ ^ 2).aestronglyMeasurable)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have fin : ∀ u : GlobalTheory.RealWeil.Sch l, ∫⁻ x, ‖u x‖ₑ ^ 2 ≠ ⊤ := by
    intro u
    rw [GlobalTheory.MetaplecticScalarDeriv.lintegral_sq_eq]
    exact ENNReal.pow_ne_top (Lp.eLpNorm_ne_top _)
  rw [key, key] at h
  exact (ENNReal.toReal_eq_toReal_iff' (fin f) (fin g)).1 h


end GlobalTheory.SchwartzSlope

end
end

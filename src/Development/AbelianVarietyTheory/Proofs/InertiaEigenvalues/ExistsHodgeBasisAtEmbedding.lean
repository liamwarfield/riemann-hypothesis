module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFacts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiSTmul
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.HodgeAt

variable {l : ℕ} [Fact l.Prime]

def emb (P : LocPrime l) (σ : GQ l) (L : FinExt l) : ↥L.1 →ₐ[ℚ_[l]] P.R.BdR :=
  (IsScalarTower.toAlgHom ℚ_[l] (Om l) P.R.BdR).comp (σ.toAlgHom.comp L.1.val)

def phiS (P : LocPrime l) (σ : GQ l) (L : FinExt l) : ↥L.1 ⊗[ℚ_[l]] P.R.BdR →ₐ[ℚ_[l]] P.R.BdR :=
  Algebra.TensorProduct.lift (emb P σ L) (AlgHom.id ℚ_[l] P.R.BdR) (fun _ _ => Commute.all _ _)

def PhiS (P : LocPrime l) (σ : GQ l) (L : FinExt l) (a : ℕ) (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    Fin a → P.R.BdR :=
  fun i => phiS P σ L (GlobalTheory.DRFil.ext ℚ_[l] P.R.BdR (LinearMap.proj i : (Fin a → ↥L.1) →ₗ[↥L.1] ↥L.1) x)

variable (P : LocPrime l) (σ : GQ l) (L : FinExt l) (a : ℕ)

theorem emb_apply (c : ↥L.1) : emb P σ L c = algebraMap (Om l) P.R.BdR (σ (c : Om l)) := rfl

theorem phiS_tmul (c : ↥L.1) (b : P.R.BdR) :
    phiS P σ L (c ⊗ₜ b) = algebraMap (Om l) P.R.BdR (σ (c : Om l)) * b := by
  simp [phiS, emb]

theorem PhiS_tmul (v : Fin a → ↥L.1) (b : P.R.BdR) :
    PhiS P σ L a (v ⊗ₜ b) = fun i => algebraMap (Om l) P.R.BdR (σ (v i : Om l)) * b := by
  funext i
  simp [PhiS, phiS_tmul]

theorem PhiS_add (x y : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    PhiS P σ L a (x + y) = PhiS P σ L a x + PhiS P σ L a y := by
  funext i
  simp [PhiS]

theorem PhiS_zero : PhiS P σ L a 0 = 0 := by
  funext i
  simp [PhiS]

theorem PhiS_sum {ι : Type} (s : Finset ι) (x : ι → (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    PhiS P σ L a (∑ i ∈ s, x i) = ∑ i ∈ s, PhiS P σ L a (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [PhiS_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, PhiS_add, ih]

theorem PhiS_sm (r : ↥L.1 ⊗[ℚ_[l]] P.R.BdR) (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    PhiS P σ L a (GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) r x) = fun i => phiS P σ L r * PhiS P σ L a x i := by
  funext i
  simp only [PhiS]
  rw [GlobalTheory.DRFil.ext_sm, GlobalTheory.DRFil.sm_self, map_mul]

theorem PhiS_mulR (b : P.R.BdR) (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    PhiS P σ L a (GlobalTheory.DRFil.mulR ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) b x) = fun i => b * PhiS P σ L a x i := by
  rw [← GlobalTheory.DRFil.sm_one_tmul, PhiS_sm, phiS_tmul]
  funext i
  simp

end GlobalTheory.HodgeAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExtFixing
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.HodgeAt

theorem phiS_idem : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K L : FinExt l) [FiniteDimensional ℚ_[l] ↥K.1] (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (σ : GQ l), (∀ x : ↥K.1, σ ((τ x : ↥L.1) : Om l) = (x : Om l)) → phiS P σ L (GlobalTheory.DRFil.idem P.R.BdR τ) = 1 := by
  intro l _ P K L _ τ σ hσ
  obtain ⟨n, a, c, h, h1⟩ := GlobalTheory.DRFil.idem_repr P.R.BdR τ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum]
  simp only [phiS_tmul]
  have hc : ∀ i, algebraMap ↥K.1 P.R.BdR (c i) = algebraMap (Om l) P.R.BdR ((c i : ↥K.1) : Om l) := fun i => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hc, ← map_mul, ← map_sum]
  have : ∑ i, σ ((a i : ↥L.1) : Om l) * ((c i : ↥K.1) : Om l) = σ (((∑ i, a i * τ (c i) : ↥L.1)) : Om l) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [IntermediateField.coe_sum, IntermediateField.coe_mul, map_sum, map_mul, hσ]
  rw [this, h1]
  simp

theorem phiS_mem_Fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K L : FinExt l) (σ : GQ l) (n : ℤ) (r : ↥L.1 ⊗[ℚ_[l]] P.R.BdR), r ∈ FilV (P.PD K) (LL := ↥L.1) (V := ↥L.1) n → phiS P σ L r ∈ (P.PD K).Fil n := by
  intro l _ P AI T K L σ n r hr
  have h0 : ∀ x : Om l, algebraMap (Om l) P.R.BdR x ∈ (P.PD K).Fil 0 := by
    intro x
    rw [T.fil]
    obtain ⟨y, hy, -⟩ := T.om x
    rw [hy]
    exact ((GlobalTheory.MemLoc.filD_laws l).2.2.2.2.2.2 0 y).2 (GlobalTheory.MemLoc.FilSeed.mem_filtration_zero' y)
  refine GlobalTheory.DRFil.FilV_induction (P.PD K) (p := fun r => phiS P σ L r ∈ (P.PD K).Fil n) ?_ ?_ ?_ hr
  · simp
  · intro c b hb
    rw [phiS_tmul]
    simpa using (P.PD K).Fil_mul 0 n _ _ (h0 _) hb
  · intro x y hx hy
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hx hy

end GlobalTheory.HodgeAt

namespace GlobalTheory.HodgeAt

theorem exists_ext_fixing : ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (σ : GQ l), ∃ K' : FinExt l, K.1 ≤ K'.1 ∧ ∀ g ∈ GK K', ∀ y : ↥L.1, g (σ (y : Om l)) = σ (y : Om l) := by
  intro l _ K L σ
  haveI := K.2
  haveI := L.2
  haveI : FiniteDimensional ℚ_[l] ↥(L.1.map (σ : Om l →ₐ[ℚ_[l]] Om l)) :=
    LinearEquiv.finiteDimensional (IntermediateField.equivMap L.1 (σ : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv
  refine ⟨⟨K.1 ⊔ L.1.map (σ : Om l →ₐ[ℚ_[l]] Om l), IntermediateField.finiteDimensional_sup _ _⟩, le_sup_left, ?_⟩
  intro g hg y
  have hmem : σ (y : Om l) ∈ K.1 ⊔ L.1.map (σ : Om l →ₐ[ℚ_[l]] Om l) :=
    le_sup_right (a := K.1) ((IntermediateField.mem_map _).2 ⟨y, y.2, rfl⟩)
  exact (mem_fixingSubgroup_iff _).1 hg _ hmem

end GlobalTheory.HodgeAt

namespace GlobalTheory.HodgeAt

theorem exists_xi_pow_mul : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l) (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (K : FinExt l) (k : ℤ) (q p : ℕ), k + q = p → ∀ x ∈ (P.PD K).Fil k, ∃ z : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ q * T.eD x = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ p * z) := by
  intro l _ P AI T C ξ hξ K k q p hkp x hx
  obtain ⟨hP, -, -, -, -, hshift, -⟩ := GlobalTheory.MemLoc.seed_fil l C ξ hξ
  rw [T.fil] at hx
  have hy := (hshift k q (T.eD x)).2 hx
  rw [hkp] at hy
  obtain ⟨y, hye⟩ := (GlobalTheory.MemLoc.mem_FilD_iff_xi_pow l C.ε (GlobalTheory.MemLoc.core_isEps l C) p _).1 hy
  have h0 : (-(p : ℤ)).toNat = 0 := by omega
  rw [h0, pow_zero, mul_one, Int.toNat_natCast] at hye
  have hz : aDp l (xi C.ε) ^ p * y ∈ Per.FilP l p :=
    ((GlobalTheory.MemLoc.filtration_eq_xi_pow l C.ε (GlobalTheory.MemLoc.core_isEps l C)).1 p _).2 (dvd_mul_right _ _)
  rw [hP, Ideal.mem_span_singleton'] at hz
  obtain ⟨z', hz'⟩ := hz
  refine ⟨z', ?_⟩
  rw [mul_comm (aDp l ξ ^ p) z', hz', hye]

end GlobalTheory.HodgeAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardEqOfLinIndepSpanningDeRham
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardEqOfLinIndepSpanningDeRham
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

namespace GlobalTheory

theorem card_eq_of_indep_spans_dR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (a m : ℕ) (w : Fin m → Fin a → P.R.BdR), (∀ β : Fin m → P.R.BdR, ∑ i, β i • w i = 0 → β = 0) → (∀ j, ∃ u : Fin m → P.R.BdR, ∑ i, u i • w i = Pi.single j 1) → m = a := by
  intro l _ P AI T a m w hind hspan
  haveI : Nontrivial P.R.BdR := (GlobalTheory.DRFil.isField_dR T).nontrivial
  have hli : LinearIndependent P.R.BdR w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    exact congrFun (hind g hg) i
  have h1 : m ≤ a := by
    have := hli.fintype_card_le_finrank
    simpa [Module.finrank_fin_fun] using this
  have hsurj : Function.Surjective (Fintype.linearCombination P.R.BdR w) := by
    rw [← LinearMap.range_eq_top, Submodule.eq_top_iff']
    intro x
    have hj : ∀ j, Pi.single j (x j) ∈ LinearMap.range (Fintype.linearCombination P.R.BdR w) := by
      intro j
      obtain ⟨u, hu⟩ := hspan j
      refine ⟨x j • u, ?_⟩
      rw [map_smul, Fintype.linearCombination_apply, hu]
      ext k
      by_cases h : k = j
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [← Finset.univ_sum_single x]
    exact Submodule.sum_mem _ fun j _ => hj j
  have h2 : a ≤ m := by
    simpa using card_le_of_surjective P.R.BdR _ hsurj
  exact le_antisymm h1 h2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardEqOfLinIndepSpanningDeRhamStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_eq_of_linIndep_spanning_deRham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (a m : ℕ) (w : Fin m → Fin a → P.R.BdR), (∀ β : Fin m → P.R.BdR, ∑ i, β i • w i = 0 → β = 0) → (∀ j, ∃ u : Fin m → P.R.BdR, ∑ i, u i • w i = Pi.single j 1) → m = a := by
  first | exact @GlobalTheory.card_eq_of_indep_spans_dR | exact GlobalTheory.card_eq_of_indep_spans_dR | (intros; apply GlobalTheory.card_eq_of_indep_spans_dR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorDeRhamCoordMulGaloisAction
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorDeRhamCoordMulGaloisAction
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

noncomputable section
namespace GlobalTheory.HodgeAt

theorem PhiS_act : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K L : FinExt l) (σ : GQ l) (a : ℕ) (r : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), (∀ g v, R g v = (r g).val *ᵥ v) → ∀ g : ↥(GK K), (∀ y : ↥L.1, (g : GQ l) (σ (y : Om l)) = σ (y : Om l)) → ∀ x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR, PhiS P σ L a (actVdR (P.PD K) R g x) = ((r g).val.map fun y => algebraMap (Om l) P.R.BdR (σ (y : Om l))) *ᵥ fun i => P.actQdR (g : GQ l) (PhiS P σ L a x i) := by
  intro l _ P K L σ a r R hR g hg x
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, PhiS_zero, Pi.zero_apply]
    exact (Matrix.mulVec_zero _).symm
  | add x y hx hy =>
    rw [map_add (f := _), PhiS_add, hx, hy, PhiS_add]
    rw [← Matrix.mulVec_add]
    congr 1
    ext i
    simp only [Pi.add_apply, map_add]
  | tmul v b =>
    rw [GlobalTheory.DRFil.actVdR_tmul, P.PD_actdR, hR, PhiS_tmul, PhiS_tmul]
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [IntermediateField.coe_sum, IntermediateField.coe_mul, map_sum, map_mul, Finset.sum_mul,
      P.actQdR_Om, hg, mul_assoc]

end GlobalTheory.HodgeAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorDeRhamCoordMulGaloisActionStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorDeRhamCoordMul_galois_action : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K L : FinExt l) (σ : GQ l) (a : ℕ) (r : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), (∀ g v, R g v = (r g).val *ᵥ v) → ∀ g : ↥(GK K), (∀ y : ↥L.1, (g : GQ l) (σ (y : Om l)) = σ (y : Om l)) → ∀ x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR, PhiS P σ L a (actVdR (P.PD K) R g x) = ((r g).val.map fun y => algebraMap (Om l) P.R.BdR (σ (y : Om l))) *ᵥ fun i => P.actQdR (g : GQ l) (PhiS P σ L a x i) := by
  first | exact @GlobalTheory.HodgeAt.PhiS_act | exact GlobalTheory.HodgeAt.PhiS_act | (intros; apply GlobalTheory.HodgeAt.PhiS_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiKernelKillingElement
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiKernelKillingElement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

noncomputable section
namespace GlobalTheory.HodgeAt

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (σ : GQ l) (L : FinExt l)

theorem phiS_map_emb (u : ↥L.1 ⊗[ℚ_[l]] ↥L.1) :
    phiS P σ L (Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) u) =
      emb P σ L (Algebra.TensorProduct.lift (AlgHom.id ℚ_[l] ↥L.1) (AlgHom.id ℚ_[l] ↥L.1)
        (fun _ _ => Commute.all _ _) u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul c d => simp [phiS, map_mul]

theorem key_emb (t : ↥L.1 ⊗[ℚ_[l]] ↥L.1)
    (ht : ∀ c : ↥L.1, ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] c) * t = (AlgHom.id ℚ_[l] ↥L.1) c • t) (c : ↥L.1) :
    ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) * Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) t =
      (c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) * Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) t := by
  have h := congrArg (Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L)) (ht c)
  rw [map_mul, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] at h
  rw [h, Algebra.smul_def, map_mul]
  congr 1
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  simp

theorem mul_eq_mul_phiS (e : ↥L.1 ⊗[ℚ_[l]] P.R.BdR)
    (hkey : ∀ c : ↥L.1, ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) * e = (c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) * e)
    (s : ↥L.1 ⊗[ℚ_[l]] P.R.BdR) : e * s = e * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] phiS P σ L s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [mul_add, hx, hy, map_add (f := _), TensorProduct.tmul_add, mul_add]
  | tmul c b =>
    calc e * (c ⊗ₜ[ℚ_[l]] b) = ((c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) * e) * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) := by
          rw [mul_comm (c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) e, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul]
      _ = (((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) * e) * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) := by rw [hkey]
      _ = e * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] phiS P σ L (c ⊗ₜ[ℚ_[l]] b)) := by
          rw [mul_comm ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) e, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
            one_mul, phiS_tmul, emb_apply]

theorem sm_eq_zero_of_PhiS (a : ℕ) (e : ↥L.1 ⊗[ℚ_[l]] P.R.BdR)
    (hmul : ∀ s : ↥L.1 ⊗[ℚ_[l]] P.R.BdR, e * s = e * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] phiS P σ L s))
    (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) (hx : PhiS P σ L a x = 0) :
    GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) e x = 0 := by
  have hc : ∀ i, phiS P σ L (GlobalTheory.DRFil.ext ℚ_[l] P.R.BdR ((Pi.basisFun ↥L.1 (Fin a)).coord i) x) = 0 := by
    intro i
    have : (Pi.basisFun ↥L.1 (Fin a)).coord i = (LinearMap.proj i : (Fin a → ↥L.1) →ₗ[↥L.1] ↥L.1) := by
      ext v; simp
    rw [this]
    exact congrFun hx i
  have hsum := GlobalTheory.DRFil.eq_sum_basis (Qp := ℚ_[l]) (F := P.R.BdR) (Pi.basisFun ↥L.1 (Fin a)) x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← GlobalTheory.DRFil.sm_mul, hmul, hc i, TensorProduct.tmul_zero, mul_zero]
  simp

end GlobalTheory.HodgeAt

theorem GlobalTheory.HodgeAt.exists_idem_phiS_ker : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (σ : GQ l) (L : FinExt l) [FiniteDimensional ℚ_[l] ↥L.1] (a : ℕ), ∃ e : ↥L.1 ⊗[ℚ_[l]] P.R.BdR, phiS P σ L e = 1 ∧ ∀ x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR, PhiS P σ L a x = 0 → GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) e x = 0 := by
  intro l _ P σ L _ a
  obtain ⟨t, ht1, ht2⟩ := GlobalTheory.DRFil.exists_idem (Qp := ℚ_[l]) (AlgHom.id ℚ_[l] ↥L.1)
  refine ⟨Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) t, ?_, ?_⟩
  · rw [phiS_map_emb, ht1, map_one]
  · exact sm_eq_zero_of_PhiS P σ L a _ (mul_eq_mul_phiS P σ L _ (key_emb P σ L t ht2))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiKernelKillingElementStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bdR_element_normalized_killing_phi_kernel : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (σ : GQ l) (L : FinExt l) [FiniteDimensional ℚ_[l] ↥L.1] (a : ℕ), ∃ e : ↥L.1 ⊗[ℚ_[l]] P.R.BdR, phiS P σ L e = 1 ∧ ∀ x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR, PhiS P σ L a x = 0 → GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) e x = 0 := by
  first | (exact @GlobalTheory.HodgeAt.exists_idem_phiS_ker) | (exact GlobalTheory.HodgeAt.exists_idem_phiS_ker) | (intros; apply GlobalTheory.HodgeAt.exists_idem_phiS_ker  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeBasisOfAdaptedInvariantFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeBasisOfAdaptedInvariantFamily
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

namespace GlobalTheory.HodgeAt

theorem hodge_of_adapted : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (K K' : FinExt l) (a : ℕ) (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (w : Fin a → Fin a → P.R.BdR) (k : Fin a → ℤ), (∀ i j, w i j ∈ (P.PD K).Fil (k i)) → (∀ j, ∃ u : Fin a → P.R.BdR, (∀ i, u i ∈ (P.PD K).Fil (-k i)) ∧ ∑ i, u i • w i = Pi.single j 1) → (∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → ∀ i, (ρ g).map (algebraMap (Om l) P.R.BdR) *ᵥ (fun j => P.actQdR (g : GQ l) (w i j)) = w i) → ∃ H : Hodge C ξ ρ K', ∀ n : ℤ, ((Finset.univ.filter fun i => (H.p i : ℤ) - H.q = n).card : ℤ) = ∑ i, if k i = n then 1 else 0 := by
  intro l _ P AI T C hFit ξ hξ K K' a ρ w k hw hspan hinv
  classical
  set ι := algebraMap (Per.BdRp l) (Per.BdR l) with hι
  obtain ⟨-, hinj, -, -⟩ := BdRField.bdR_isField l

  have hE : IsUnit (ι (aDp l ξ)) := by
    have hxiker : xi C.ε ∈ Ideal.span {ξ} := by
      rw [hξ, C.ker_theta]; exact Ideal.mem_span_singleton_self _
    obtain ⟨c0, hc0⟩ := Ideal.mem_span_singleton'.1 hxiker
    have h1 := GlobalTheory.MemLoc.TiedUnif.isUnit_xi (core_isEps l C)
    rw [← hc0, map_mul, map_mul] at h1
    exact isUnit_of_mul_isUnit_right h1

  set q : ℕ := ∑ i, (k i).natAbs with hq
  have hkq : ∀ i, 0 ≤ k i + q := by
    intro i
    have h1 : (k i).natAbs ≤ q := Finset.single_le_sum (f := fun i => (k i).natAbs) (by simp) (Finset.mem_univ i)
    omega
  set p : Fin a → ℕ := fun i => (k i + q).toNat with hp
  have hkp : ∀ i, k i + q = (p i : ℤ) := fun i => (Int.toNat_of_nonneg (hkq i)).symm

  have hV0 : ∀ i j, ∃ v : Per.BdRp l, ι (aDp l ξ) ^ q * T.eD (w j i) = ι (aDp l ξ ^ p j * v) :=
    fun i j => exists_xi_pow_mul l P AI T C ξ hξ K (k j) q (p j) (hkp j) (w j i) (hw j i)
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin a) (Fin a) (Per.BdRp l), ∀ i j, ι (aDp l ξ) ^ q * T.eD (w j i) = ι (aDp l ξ ^ p j * V i j) :=
    ⟨fun i j => Classical.choose (hV0 i j), fun i j => Classical.choose_spec (hV0 i j)⟩

  choose u hu hsum using hspan
  have hz0 : ∀ j i, ∃ z : Per.BdRp l, ι (aDp l ξ) ^ p i * T.eD (u j i) = ι (aDp l ξ ^ q * z) :=
    fun j i => exists_xi_pow_mul l P AI T C ξ hξ K (-k i) (p i) q (by have := hkp i; omega) (u j i) (hu j i)
  choose z hz using hz0
  have key : ∀ j j', ∑ i, z j i * V j' i = if j' = j then 1 else 0 := by
    intro j j'
    apply hinj
    have hs := congrFun (hsum j) j'
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
    have h1 : ι (aDp l ξ) ^ q * ι (∑ i, z j i * V j' i) =
        ι (aDp l ξ) ^ q * T.eD (∑ i, u j i * w i j') := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have ha := hV j' i
      have hb := hz j i
      simp only [map_mul, map_pow] at ha hb ⊢
      calc ι (aDp l ξ) ^ q * (ι (z j i) * ι (V j' i))
          = (ι (aDp l ξ) ^ q * ι (z j i)) * ι (V j' i) := by ring
        _ = (ι (aDp l ξ) ^ p i * T.eD (u j i)) * ι (V j' i) := by rw [hb]
        _ = T.eD (u j i) * (ι (aDp l ξ) ^ p i * ι (V j' i)) := by ring
        _ = T.eD (u j i) * (ι (aDp l ξ) ^ q * T.eD (w i j')) := by rw [ha]
        _ = ι (aDp l ξ) ^ q * (T.eD (u j i) * T.eD (w i j')) := by ring
    rw [(hE.pow q).mul_left_cancel h1, hs, Pi.single_apply]
    split_ifs <;> simp
  set N : Matrix (Fin a) (Fin a) (Per.BdRp l) := Matrix.of fun i j => z j i with hN
  have hVN : V * N = 1 := by
    ext j' j
    rw [Matrix.mul_apply, Matrix.one_apply, ← key j j']
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hN, Matrix.of_apply]; ring
  have hNV : N * V = 1 := mul_eq_one_comm.1 hVN
  refine ⟨⟨V, ⟨⟨V, N, hVN, hNV⟩, rfl⟩, p, q, Matrix.of fun i j => T.eD (w j i), fun i j => by simpa using hV i j, ?_⟩, ?_⟩
  · intro g hg
    ext r c
    have h := congrArg T.eD (congrFun (hinv g hg c) r)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, T.actD, hFit.o] at h
    rw [Matrix.mul_apply]
    simpa [Matrix.map_apply, Matrix.of_apply, GlobalTheory.MemLoc.Core.oD] using h
  · intro n
    have hf : (Finset.univ.filter fun i => ((p i : ℕ) : ℤ) - (q : ℤ) = n) = Finset.univ.filter fun i => k i = n := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := hkp i
      omega
    show ((Finset.univ.filter fun i => ((p i : ℕ) : ℤ) - (q : ℤ) = n).card : ℤ) = _
    rw [hf, Finset.card_filter]
    push_cast
    rfl

end GlobalTheory.HodgeAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeBasisOfAdaptedInvariantFamilyStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_basis_of_adapted_invariant_family : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (K K' : FinExt l) (a : ℕ) (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (w : Fin a → Fin a → P.R.BdR) (k : Fin a → ℤ), (∀ i j, w i j ∈ (P.PD K).Fil (k i)) → (∀ j, ∃ u : Fin a → P.R.BdR, (∀ i, u i ∈ (P.PD K).Fil (-k i)) ∧ ∑ i, u i • w i = Pi.single j 1) → (∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → ∀ i, (ρ g).map (algebraMap (Om l) P.R.BdR) *ᵥ (fun j => P.actQdR (g : GQ l) (w i j)) = w i) → ∃ H : Hodge C ξ ρ K', ∀ n : ℤ, ((Finset.univ.filter fun i => (H.p i : ℤ) - H.q = n).card : ℤ) = ∑ i, if k i = n then 1 else 0 := by
  first | (exact @GlobalTheory.HodgeAt.hodge_of_adapted) | (exact GlobalTheory.HodgeAt.hodge_of_adapted) | (intros; apply GlobalTheory.HodgeAt.hodge_of_adapted  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeBasisAtEmbedding
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.HodgeAt


set_option maxHeartbeats 1000000 in
theorem exists_hodge_at_embedding : ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (a : ℕ) (r : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), (∀ g v, R g v = (r g).val *ᵥ v) → Formalism.MainNotions.N.IsDR (P.PD K) R → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (σ : GQ l), (∀ x : ↥K.1, σ ((τ x : ↥L.1) : Om l) = (x : Om l)) → ∃ (K' : FinExt l) (H : Hodge C ξ (fun g => (r g).val.map fun x => σ (x : Om l)) K'), K.1 ≤ K'.1 ∧ ∀ n : ℤ, ((Finset.univ.filter fun i => (H.p i : ℤ) - H.q = n).card : ℤ) = multV (P.PD K) R τ n := by
  intro l _ K L P AI T C hC ξ hξ a r R hR hDR τ σ hσ
  haveI := K.2
  haveI := L.2
  haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K L (Fin a → ↥L.1) R).1
  obtain ⟨m, d, k, hA⟩ := GlobalTheory.DRFil.exists_adapted (P.PD K) (GlobalTheory.DRFil.isField_dR T) R
    (GlobalTheory.DRFil.filSpans T K L R hDR) τ
  obtain ⟨K', hKK', hK'⟩ := exists_ext_fixing l K L σ
  obtain ⟨e, he1, he0⟩ := GlobalTheory.T.exists_bdR_element_normalized_killing_phi_kernel l P σ L a
  have hid := phiS_idem l P K L τ σ hσ
  set w : Fin m → Fin a → P.R.BdR := fun i => PhiS P σ L a (d i) with hw
  have hfil : ∀ i j, w i j ∈ (P.PD K).Fil (k i) := fun i j =>
    phiS_mem_Fil l P AI T K L σ (k i) _ (GlobalTheory.DRFil.ext_mem_FilV (P.PD K) _ (hA.mem i).2)
  have hind : ∀ β : Fin m → P.R.BdR, ∑ i, β i • w i = 0 → β = 0 := by
    intro β hβ
    have h0 : ∑ i, GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) (e * ((1 : ↥L.1) ⊗ₜ β i)) (d i) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [GlobalTheory.DRFil.sm_mul, GlobalTheory.DRFil.sm_one_tmul, ← map_sum]
      apply he0
      rw [PhiS_sum]
      simp only [PhiS_mulR]
      rw [← hβ]
      funext j
      simp [hw]
    funext i
    have := congrArg (phiS P σ L) (hA.indep _ h0 i)
    simpa [map_mul, hid, he1, phiS_tmul] using this
  have hspan : ∀ j, ∃ u : Fin m → P.R.BdR, (∀ i, u i ∈ (P.PD K).Fil (-k i)) ∧ ∑ i, u i • w i = Pi.single j 1 := by
    intro j
    obtain ⟨rr, hrr, hy⟩ := hA.span 0 (Pi.single j 1 ⊗ₜ (1 : P.R.BdR))
      (GlobalTheory.DRFil.tmul_mem_FilV (P.PD K) _ (P.PD K).one_mem)
    refine ⟨fun i => phiS P σ L (rr i), fun i => by simpa using phiS_mem_Fil l P AI T K L σ _ _ (hrr i), ?_⟩
    have h2 := congrArg (PhiS P σ L a) hy
    rw [PhiS_sm] at h2
    simp only [hid, one_mul, PhiS_sum, PhiS_sm] at h2
    have h3 : ∑ i, (fun i => phiS P σ L (rr i)) i • w i = ∑ x, fun i => phiS P σ L (rr x) * PhiS P σ L a (d x) i := rfl
    rw [h3, ← h2, PhiS_tmul]
    funext i
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Pi.single_eq_of_ne hij]
  have hinv : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → ∀ i,
      ((fun g => (r g).val.map fun x => σ (x : Om l)) g).map (algebraMap (Om l) P.R.BdR) *ᵥ
        (fun j => P.actQdR (g : GQ l) (w i j)) = w i := by
    intro g hg i
    have h1 := GlobalTheory.T.tensorDeRhamCoordMul_galois_action l P K L σ a r R hR g (fun y => hK' g hg y) (d i)
    rw [(GlobalTheory.DRFil.mem_DdR (P.PD K) R _).1 (hA.mem i).1.1 g] at h1
    rw [Matrix.map_map]
    exact h1.symm
  have hma := GlobalTheory.T.card_eq_of_linIndep_spanning_deRham l P AI T a m w hind (fun j => (hspan j).imp fun u hu => hu.2)
  subst hma
  obtain ⟨H, hH⟩ := GlobalTheory.T.hodge_basis_of_adapted_invariant_family l P AI T C hC ξ hξ K K' m _ w k hfil hspan hinv
  exact ⟨K', H, hKK', fun n => by rw [hH n, hA.multV_eq]⟩

end GlobalTheory.HodgeAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeBasisAtEmbeddingStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hodge_basis_at_embedding : ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (a : ℕ) (r : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), (∀ g v, R g v = (r g).val *ᵥ v) → Formalism.MainNotions.N.IsDR (P.PD K) R → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (σ : GQ l), (∀ x : ↥K.1, σ ((τ x : ↥L.1) : Om l) = (x : Om l)) → ∃ (K' : FinExt l) (H : Hodge C ξ (fun g => (r g).val.map fun x => σ (x : Om l)) K'), K.1 ≤ K'.1 ∧ ∀ n : ℤ, ((Finset.univ.filter fun i => (H.p i : ℤ) - H.q = n).card : ℤ) = multV (P.PD K) R τ n := by
  first | (exact @GlobalTheory.HodgeAt.exists_hodge_at_embedding) | (exact GlobalTheory.HodgeAt.exists_hodge_at_embedding) | (intros; apply GlobalTheory.HodgeAt.exists_hodge_at_embedding  <;> assumption)
end

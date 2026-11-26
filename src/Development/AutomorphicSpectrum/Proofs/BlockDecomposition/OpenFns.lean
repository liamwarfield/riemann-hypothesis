module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.StTopClass
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.FdSetIntegralCharEqZero
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.BlockMatrixIdentity.BlockMatOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.Rodier

section Pi

variable {α : Type} [Fintype α] {Γ : α → Type} [∀ a, Group (Γ a)]

abbrev piSub (H : ∀ a, Subgroup (Γ a)) : Subgroup (∀ a, Γ a) := Subgroup.pi Set.univ H

def piChar {H : ∀ a, Subgroup (Γ a)} (χ : ∀ a, H a →* ℂˣ) : piSub H →* ℂˣ where
  toFun m := ∏ a, χ a ⟨m.1 a, m.2 a (Set.mem_univ a)⟩
  map_one' := Finset.prod_eq_one fun a _ => map_one (χ a)
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a _ => map_mul (χ a) ⟨x.1 a, x.2 a (Set.mem_univ a)⟩ ⟨y.1 a, y.2 a (Set.mem_univ a)⟩

end Pi

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

abbrev pm (w : Equiv.Perm (Fin N)) : GL (Fin N) k := GroundTheory.Automorphic.permGL k w

def cell (w : Equiv.Perm (Fin N)) : Set (GL (Fin N) k) :=
  {g | ∃ p ∈ parab k (stdBlocks d hd), ∃ n ∈ unipB k (Fin N), g = p * pm k w * n}

def wKey (i : Fin N) : (Fin h)ᵒᵈ ×ₗ Fin N := toLex (OrderDual.toDual (blk (stdBlocks d hd) i), i)

def wOpen : Equiv.Perm (Fin N) := Tuple.sort (wKey d hd)

variable {k}
variable {W : Type} [AddCommGroup W] [Module ℂ W]

def openFns (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) : Submodule ℂ (IndSp (stdBlocks d hd) ρ) where
  carrier := {f | ∀ g, f.1.1 g ≠ 0 → g ∈ cell k d hd (wOpen d hd)}
  add_mem' := by
    intro a b ha hb g hg
    by_cases h1 : a.1.1 g = 0
    · refine hb g fun h2 => hg ?_
      show a.1.1 g + b.1.1 g = 0
      rw [h1, h2, add_zero]
    · exact ha g h1
  zero_mem' := fun g hg => absurd rfl hg
  smul_mem' := by
    intro c a ha g hg
    refine ha g fun h1 => hg ?_
    show c • a.1.1 g = 0
    rw [h1, smul_zero]

variable (k)

abbrev unipM : Subgroup (Levi k fun a => Fin (d a)) := piSub fun a => unipB k (Fin (d a))

variable {k}

abbrev whitM (ψ : AddChar k Circle) : unipM k d →* ℂˣ := piChar fun a => whitChar ψ (d a)

variable (k)

def unipU : Subgroup (GL (Fin N) k) :=
  unipB k (Fin N) ⊓ (unipRadLower k (stdBlocks d hd)).comap (MulAut.conj (pm k (wOpen d hd))).toMonoidHom

def unipL : Subgroup (GL (Fin N) k) :=
  unipB k (Fin N) ⊓ (leviEmb k (stdBlocks d hd)).range.comap (MulAut.conj (pm k (wOpen d hd))).toMonoidHom

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem OpenFactor.mem_unipL {u : GL (Fin N) k} : u ∈ unipL k d hd ↔
    u ∈ unipB k (Fin N) ∧
      pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ ∈ (leviEmb k (stdBlocks d hd)).range := by
  simp only [unipL, Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]

end GlobalTheory.CompanionTheory.Rodier

namespace GlobalTheory.CompanionTheory.Rodier

def smInt {X W : Type} [MeasurableSpace X] [AddCommGroup W] [Module ℂ W] (μ : MeasureTheory.Measure X) (φ : X → W) : W :=
  ∑ᶠ v : W, (((μ (φ ⁻¹' {v})).toReal : ℝ) : ℂ) • v

end GlobalTheory.CompanionTheory.Rodier

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS
noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.CTFin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def capR (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : Module.End ℂ (Sm E (r + s)) :=
  Formalism.REAL.qdet (fun i j : Fin r => Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s j)) (u + ((r : ℂ) - 1) / 2)

def capS (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : Module.End ℂ (Sm E (r + s)) :=
  Formalism.REAL.qdet (fun i j : Fin s => Eop (a := r + s) τ (Fin.natAdd r i) (Fin.natAdd r j)) (u + ((s : ℂ) - 1) / 2)

end GlobalTheory.CompanionTheory.CTFin

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityGenericProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityGenericProduct
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Leib

theorem nontrivial_piTensorProduct_iff {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] :
    Nontrivial (⨂[ℂ] i, M i) ↔ ∀ i, Nontrivial (M i) := by
  classical
  constructor
  · intro hN i
    by_contra hi
    rw [not_nontrivial_iff_subsingleton] at hi
    have h0 : ∀ x : ⨂[ℂ] i, M i, x = 0 := by
      intro x
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r f =>
        rw [(PiTensorProduct.tprod ℂ).map_coord_zero i (Subsingleton.elim (f i) 0), smul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    obtain ⟨x, y, hxy⟩ := hN.exists_pair_ne
    exact hxy ((h0 x).trans (h0 y).symm)
  · intro hM
    have hv : ∀ i, ∃ v : M i, v ≠ 0 := fun i => @exists_ne _ (hM i) 0
    choose v hv using hv
    have hφ : ∀ i, ∃ φ : Module.Dual ℂ (M i), φ (v i) ≠ 0 := fun i => by
      by_contra hc
      simp only [not_exists, ne_eq, not_not] at hc
      exact hv i ((Module.forall_dual_apply_eq_zero_iff ℂ (v i)).1 hc)
    choose φ hφ using hφ
    refine ⟨⟨PiTensorProduct.tprod ℂ v, 0, fun h => ?_⟩⟩
    have h1 := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap φ)) h
    simp only [PiTensorProduct.lift.tprod, map_zero, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply] at h1
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hφ i) h1

theorem genericProdIff_of_whitHeredity (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : WhitHeredity k → GenericProdIff k := by
  intro hW h N d hd X _ _ π hsm
  obtain ⟨ψ, hψc, hψ1⟩ := GlobalTheory.LocGL.exists_continuous_addChar_ne_one (k := k)
  obtain ⟨e⟩ := hW ψ hψc hψ1 h N d hd X π hsm
  simp only [GlobalTheory.LocGL.isGeneric_iff_isGenericFor hψc hψ1, GlobalTheory.LocGL.IsGenericFor]
  exact Iff.trans ⟨fun hn => @Equiv.nontrivial _ _ e.symm.toEquiv hn, fun hn => @Equiv.nontrivial _ _ e.toEquiv hn⟩
    (nontrivial_piTensorProduct_iff _)

end GlobalTheory.CompanionTheory.Leib

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityGenericProductStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_heredity_generic_product : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], WhitHeredity k → GenericProdIff k := by
  first | exact @GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity | exact GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity | (intros; apply GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimCoefficientsFiniteDetermining
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimCoefficientsFiniteDetermining
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

noncomputable section

namespace GlobalTheory.CompanionTheory.CTFin.UniSol

theorem exists_finset_separating {K : Type} (A : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ A] :
    ∃ S : Finset K, ∀ c ∈ A, (∀ κ ∈ S, c κ = 0) → c = 0 := by
  classical
  have key : ∀ (n : ℕ) (B : Submodule ℂ A), Module.finrank ℂ B = n →
      ∃ S : Finset K, ∀ c ∈ B, (∀ κ ∈ S, (c : K → ℂ) κ = 0) → c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro B hB
      by_cases hbot : B = ⊥
      · refine ⟨∅, fun c hc _ => ?_⟩
        rw [hbot] at hc
        exact (Submodule.mem_bot ℂ).mp hc
      · obtain ⟨c0, hc0B, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
        obtain ⟨κ0, hκ0⟩ : ∃ κ0, (c0 : K → ℂ) κ0 ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hc0 (Subtype.ext (funext hcon))
        let ev : A →ₗ[ℂ] ℂ := (LinearMap.proj κ0).comp A.subtype
        let B' : Submodule ℂ A := B ⊓ LinearMap.ker ev
        have hlt : B' < B := by
          refine lt_of_le_of_ne inf_le_left (fun h => hκ0 ?_)
          have hmem : c0 ∈ B' := by
            rw [h]
            exact hc0B
          exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hmem).2
        have hrk : Module.finrank ℂ B' < n := by
          have := Submodule.finrank_lt_finrank_of_lt hlt
          omega
        obtain ⟨S', hS'⟩ := ih _ hrk B' rfl
        refine ⟨insert κ0 S', fun c hc hvan => hS' c ?_ (fun κ hκ => hvan κ (Finset.mem_insert_of_mem hκ))⟩
        refine Submodule.mem_inf.mpr ⟨hc, LinearMap.mem_ker.mpr ?_⟩
        exact hvan κ0 (Finset.mem_insert_self κ0 S')
  obtain ⟨S, hS⟩ := key _ ⊤ rfl
  refine ⟨S, fun c hc hvan => ?_⟩
  have h0 := hS ⟨c, hc⟩ Submodule.mem_top hvan
  exact congrArg Subtype.val h0

theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  classical
  let b := Module.Free.chooseBasis ℂ W
  let m : (Module.Free.ChooseBasisIndex ℂ W) × (Module.Free.ChooseBasisIndex ℂ W) → (K → ℂ) :=
    fun ij k => b.repr (ρ k (b ij.2)) ij.1
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range m)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range m)
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ Submodule.span ℂ (Set.range m) := by
    unfold GlobalTheory.Published.AutFin.coeffSpan
    refine Submodule.span_le.mpr ?_
    rintro f ⟨ℓ, w, rfl⟩
    have hw : ∀ v : W, ℓ v = ∑ i, b.repr v i * ℓ (b i) := by
      intro v
      conv_lhs => rw [← b.sum_repr v]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul]
    have hf : (fun k => ℓ ((ρ k) w)) = ∑ ij, (b.repr w ij.2 * ℓ (b ij.1)) • m ij := by
      funext k
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, m]
      rw [Fintype.sum_prod_type]
      dsimp only
      have h1 : ℓ (ρ k w) = ∑ j, b.repr w j * ℓ (ρ k (b j)) := by
        conv_lhs => rw [← b.sum_repr w]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, smul_eq_mul]
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hw (ρ k (b j)), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [hf]
    exact Submodule.sum_mem _ (fun ij _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ij, rfl⟩))
  exact Submodule.finiteDimensional_of_le hle

theorem coeffSpan_unisolvent : ∀ (K W : Type) [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W), ∃ S : Finset K, ∀ c ∈ GlobalTheory.Published.AutFin.coeffSpan ρ, (∀ κ ∈ S, c κ = 0) → c = 0 := by
  intro K W _ _ _ _ ρ
  haveI := finiteDimensional_coeffSpan ρ
  exact exists_finset_separating _

end GlobalTheory.CompanionTheory.CTFin.UniSol

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimCoefficientsFiniteDeterminingStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dim_coefficients_finite_determining : ∀ (K W : Type) [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W), ∃ S : Finset K, ∀ c ∈ GlobalTheory.Published.AutFin.coeffSpan ρ, (∀ κ ∈ S, c κ = 0) → c = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.UniSol.coeffSpan_unisolvent | exact GlobalTheory.CompanionTheory.CTFin.UniSol.coeffSpan_unisolvent | (intros; apply GlobalTheory.CompanionTheory.CTFin.UniSol.coeffSpan_unisolvent <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipLevIntegral
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin IsDedekindDomain Matrix

namespace GlobalTheory.CompanionTheory.CTFin.IwaFin

theorem exists_unip_mul_lev {R : Type} [CommRing R] (r s : ℕ) (P : GL (Fin (r + s)) R)
    (h1 : ∀ i j : Fin (r + s), r ≤ (i : ℕ) → (j : ℕ) < r → (P : Matrix _ _ R) i j = 0)
    (h2 : ∀ i j : Fin (r + s), r ≤ (i : ℕ) → (j : ℕ) < r → ((P⁻¹ : GL _ R) : Matrix _ _ R) i j = 0) :
    ∃ (x : BlockIx (r + s) r → R) (m : GL (Fin r) R × GL (Fin s) R), P = unip x * lev R r s m := by
  set e := GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) with he
  set Q : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) R := (P : Matrix _ _ R).submatrix e e with hQd
  set Q' : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) R := ((P⁻¹ : GL _ R) : Matrix _ _ R).submatrix e e with hQ'd
  have hQQ : Q * Q' = 1 := by
    rw [hQd, hQ'd, Matrix.submatrix_mul_equiv, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.submatrix_one_equiv]
  have hQQ' : Q' * Q = 1 := by
    rw [hQd, hQ'd, Matrix.submatrix_mul_equiv, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.submatrix_one_equiv]
  have hz : Q.toBlocks₂₁ = 0 := by
    ext i j
    exact h1 _ _ (by simp [he]) (by simp [he])
  have hz' : Q'.toBlocks₂₁ = 0 := by
    ext i j
    exact h2 _ _ (by simp [he]) (by simp [he])
  have hb : Q = fromBlocks Q.toBlocks₁₁ Q.toBlocks₁₂ 0 Q.toBlocks₂₂ := by
    rw [← hz, fromBlocks_toBlocks]
  have hb' : Q' = fromBlocks Q'.toBlocks₁₁ Q'.toBlocks₁₂ 0 Q'.toBlocks₂₂ := by
    rw [← hz', fromBlocks_toBlocks]
  generalize Q.toBlocks₁₁ = A at hb
  generalize Q.toBlocks₁₂ = B at hb
  generalize Q.toBlocks₂₂ = D at hb
  generalize Q'.toBlocks₁₁ = A' at hb'
  generalize Q'.toBlocks₁₂ = B' at hb'
  generalize Q'.toBlocks₂₂ = D' at hb'
  rw [hb, hb', fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hQQ hQQ'
  simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add] at hQQ
  simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add] at hQQ'
  obtain ⟨a1, -, -, d1⟩ := hQQ
  obtain ⟨a2, -, -, d2⟩ := hQQ'
  let X : Matrix (Fin r) (Fin s) R := B * D'
  let x : BlockIx (r + s) r → R := fun p =>
    X ⟨p.1.1, p.2.1⟩ ⟨p.1.2 - r, by have := p.1.2.isLt; have := p.2.2; omega⟩
  let m : GL (Fin r) R × GL (Fin s) R := (⟨A, A', a1, a2⟩, ⟨D, D', d1, d2⟩)
  refine ⟨x, m, Units.ext ?_⟩
  have hn : (nilM x : Matrix (Fin (r + s)) (Fin (r + s)) R).submatrix e e = fromBlocks 0 X 0 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [nilM, he]
    · have h : (((e (Sum.inl i) : Fin (r + s)) : ℕ) < r ∧ r ≤ ((e (Sum.inr j) : Fin (r + s)) : ℕ)) := by
        simp [he]
      simp only [submatrix_apply, nilM, of_apply, dif_pos h, fromBlocks_apply₁₂, x]
      congr 1
      exact Fin.ext (by simp [he])
    · simp [nilM, he]
    · simp [nilM, he]
  have hu : ((unip x : GL (Fin (r + s)) R) : Matrix _ _ R).submatrix e e = fromBlocks 1 X 0 1 := by
    change (1 + nilM x : Matrix _ _ R).submatrix e e = _
    have h : (1 + nilM x : Matrix (Fin (r + s)) (Fin (r + s)) R).submatrix e e =
        (1 : Matrix (Fin (r + s)) (Fin (r + s)) R).submatrix e e + (nilM x).submatrix e e := rfl
    rw [h, Matrix.submatrix_one_equiv, hn, ← fromBlocks_one, fromBlocks_add]
    simp
  have hl : ((lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R).submatrix e e = fromBlocks A 0 0 D := by
    rw [lev, GlobalTheory.SmGL.val_emb₂]
    ext i j
    simp [m, ← he]
  have hinj : ∀ M N : Matrix (Fin (r + s)) (Fin (r + s)) R, M.submatrix e e = N.submatrix e e → M = N := by
    intro M N h
    ext i j
    have := congrFun (congrFun h (e.symm i)) (e.symm j)
    simpa using this
  apply hinj
  rw [Units.val_mul, ← Matrix.submatrix_mul_equiv _ _ _ e, hu, hl, fromBlocks_multiply, ← hQd, hb]
  simp [X, Matrix.mul_assoc, d2]

theorem exists_unip_lev_integral (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ)
    (k : GL (Fin (r + s)) (Af E)) :
    ∃ (x : BlockIx (r + s) r → Af E) (m : GL (Fin r) (Af E) × GL (Fin s) (Af E)) (c : GL (Fin (r + s)) (Af E)),
      c ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (r + s) ∧ k = unip x * lev (Af E) r s m * c := by
  classical
  let φ := GroundTheory.Automorphic.AdelicGLn.finiteRestrictedEquiv E (r + s)
  let β : Fin (r + s) → ℕ := fun i => if (i : ℕ) < r then 0 else 1
  have hβ : Monotone β := by
    intro i j hij
    have : (i : ℕ) ≤ j := hij
    simp only [β]
    split_ifs <;> omega
  have loc : ∀ v : HeightOneSpectrum (𝓞 E), ∃ p ∈ GroundTheory.Automorphic.Iwasawa.blockUpper (v.adicCompletion E) (r + s) β,
      ∃ c ∈ GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion E) (r + s),
        (φ k v : GL (Fin (r + s)) (v.adicCompletion E)) = p * c ∧
        (φ k v ∈ GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion E) (r + s) → p = 1) := by
    intro v
    by_cases h : φ k v ∈ GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion E) (r + s)
    · exact ⟨1, one_mem _, φ k v, h, (one_mul _).symm, fun _ => rfl⟩
    · obtain ⟨p, hp, c, hc, e⟩ := GroundTheory.Automorphic.Iwasawa.exists_blockUpper_mul_integralGL
        (v.adicCompletion E) (r + s) hβ (φ k v)
      exact ⟨p, hp, c, hc, e, fun h' => absurd h' h⟩
  choose p hp c hc hk h1 using loc
  let P' : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => GL (Fin (r + s)) (v.adicCompletion E))
      (fun v => (GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion E) (r + s) : Set _)) Filter.cofinite :=
    ⟨p, by
      filter_upwards [(φ k).2] with v hv
      rw [h1 v hv]
      exact one_mem _⟩
  let C' : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => GL (Fin (r + s)) (v.adicCompletion E))
      (fun v => (GroundTheory.Automorphic.GLnLocal.integralGL (v.adicCompletion E) (r + s) : Set _)) Filter.cofinite :=
    ⟨c, Filter.Eventually.of_forall hc⟩
  have hs : ∀ y, φ (φ.symm y) = y := fun y => φ.apply_symm_apply y
  have hPC : k = φ.symm P' * φ.symm C' := by
    apply φ.injective
    rw [map_mul, hs, hs]
    ext v : 1
    exact hk v
  have hPv : ∀ v, φ (φ.symm P') v = p v := fun v => by rw [hs]; rfl
  have hzero : ∀ (q : GL (Fin (r + s)) (Af E)),
      (∀ v, φ q v ∈ GroundTheory.Automorphic.Iwasawa.blockUpper (v.adicCompletion E) (r + s) β) →
      ∀ i j : Fin (r + s), r ≤ (i : ℕ) → (j : ℕ) < r → (q : Matrix _ _ (Af E)) i j = 0 := by
    intro q hq i j hi hj
    refine FiniteAdeleRing.ext _ fun v => ?_
    have hlt : β j < β i := by simp [β, hj, Nat.not_lt.2 hi]
    exact hq v hlt
  obtain ⟨x, m, hxm⟩ := exists_unip_mul_lev r s (φ.symm P')
    (hzero _ fun v => by rw [hPv]; exact hp v)
    (hzero _ fun v => by
      rw [map_inv, RestrictedProduct.inv_apply, hPv]
      exact inv_mem (hp v))
  refine ⟨x, m, φ.symm C', ?_, by rw [hPC, hxm]⟩
  rw [GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff_forall]
  intro v
  have : φ (φ.symm C') v = c v := by rw [hs]; rfl
  change φ (φ.symm C') v ∈ _
  rw [this]
  exact hc v

end GlobalTheory.CompanionTheory.CTFin.IwaFin
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceSingleMulSingle
open Matrix MvPolynomial

noncomputable section

namespace GlobalTheory.CompanionTheory.TopClass

open PositivityTheory.RgTw

variable {n : ℕ}

theorem trace_single_mul_single (a b c e : Fin n) :
    trace (Matrix.single a b (1 : ℂ) * Matrix.single c e 1) = if a = e ∧ b = c then 1 else 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]
  by_cases h1 : a = e <;> by_cases h2 : b = c <;> simp [h1, h2, ite_and, Finset.sum_ite_eq', eq_comm]

theorem sqrt_two_inv_sq : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem trace_hb_mul_hb (p q : Fin n × Fin n) : trace (hb p * hb q) = if p = q then 1 else 0 := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, e⟩ := q
  have hs := sqrt_two_inv_sq
  simp only [hb]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 <;>
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      trace_add, trace_sub, trace_smul, trace_single_mul_single, smul_eq_mul, Prod.mk.injEq] at * <;> (simp only [Fin.ext_iff, Fin.lt_iff_val_lt_val] at * ; split_ifs at * <;> (try omega)) <;>
  (generalize ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = s at hs ⊢
   have hs2 : s ^ 2 = 1 / 2 := by rw [sq]; exact hs
   first | ring1 | (ring_nf; simp only [Complex.I_sq, hs2]; ring_nf))

theorem hb_linInd : LinearIndependent ℂ (hb (n := n)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  have h := congrArg (fun X => trace (X * hb q)) hg
  simpa [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, trace_smul, trace_hb_mul_hb] using h

def hbB (n : ℕ) : Module.Basis (Fin n × Fin n) ℂ (Mat n) :=
  basisOfLinearIndependentOfCardEqFinrank' hb hb_linInd (by simp [Module.finrank_matrix])

theorem hbB_apply (p : Fin n × Fin n) : hbB n p = hb p := by
  simp [hbB]

theorem hbB_repr (X : Mat n) (q : Fin n × Fin n) : (hbB n).repr X q = trace (X * hb q) := by
  conv_rhs => rw [← (hbB n).sum_repr X]
  simp [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, trace_smul, hbB_apply, trace_hb_mul_hb]

theorem det_of_trace (L : Mat n →ₗ[ℂ] Mat n) :
    (Matrix.of fun p q : Fin n × Fin n => trace (L (hb p) * hb q)).det = LinearMap.det L := by
  rw [← LinearMap.det_toMatrix (hbB n) L, ← Matrix.det_transpose (LinearMap.toMatrix (hbB n) (hbB n) L)]
  congr 1
  ext p q
  simp [LinearMap.toMatrix_apply, hbB_repr, hbB_apply]

end GlobalTheory.CompanionTheory.TopClass
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermTranslateFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermTranslateFormula
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

namespace GlobalTheory.CompanionTheory.CTFin

theorem constTerm_unip_left : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (φ : Sm E a),
    (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} →
    ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
      (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ →
    ∀ (y : BlockIx a r → Ad E) (g : GA E a),
      ∫ x in 𝓕, φ.1 (unip x * (unip y * g)) ∂μ = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ := by
  intro E _ _ _ a r φ hl _ _ _ μ 𝓕 hμ h𝓕 y g
  haveI := countable_ratN (E := E) (a := a) r
  have hper : ∀ n ∈ ratN E a r, ∀ x, φ.1 (unip (n + x) * g) = φ.1 (unip x * g) := by
    rintro _ ⟨q, rfl⟩ x
    rw [unip_add, mul_assoc]
    exact (congrArg (fun u => φ.1 (u * _)) (unip_algebraMap q)).trans (hl _ _)
  have h := Formalism.IndefR.Tow.fd_setIntegral_add h𝓕 (f := fun x => φ.1 (unip x * g)) hper y
  simpa only [unip_add, mul_assoc] using h

end GlobalTheory.CompanionTheory.CTFin
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermTranslateFormulaStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_translate_formula : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (φ : Sm E a), (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ (y : BlockIx a r → Ad E) (g : GA E a), ∫ x in 𝓕, φ.1 (unip x * (unip y * g)) ∂μ = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.constTerm_unip_left | exact GlobalTheory.CompanionTheory.CTFin.constTerm_unip_left | (intros; apply GlobalTheory.CompanionTheory.CTFin.constTerm_unip_left <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOnFundamentalDomain
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl PositivityTheory.Affgl.CT Topology Matrix
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.ConstTerm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_map_pFin :
    Continuous (GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd :
    Continuous fun x : InfiniteAdeleRing E × IsDedekindDomain.FiniteAdeleRing (𝓞 E) E => x.2))

theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)).comp
    (continuous_fst : Continuous fun x : InfiniteAdeleRing E × IsDedekindDomain.FiniteAdeleRing (𝓞 E) E => x.1)

theorem continuous_map_pInf :
    Continuous (GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf)

theorem continuous_of_isOpen_stab (φ : Sm E a) (hU : IsOpen {k | finRep E a k φ = φ}) : Continuous φ.1 := by
  rw [continuous_iff_continuousAt]
  intro g
  have hF : ContinuousAt (fun h : GA E a => chart φ.1 g (toL (GeneralLinearGroup.map (pInf E) h).val)) 1 := by
    have h1 : ContinuousAt (chart φ.1 g) (toL ((GeneralLinearGroup.map (pInf E) (1 : GA E a)).val)) := by
      rw [map_one]
      exact (contDiffAt_chart φ.2 g isUnit_one).continuousAt
    have h0 : Continuous (fun h : GA E a =>
        ((GeneralLinearGroup.map (n := Fin a) (pInf E) h : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))) :=
      Units.continuous_val.comp continuous_map_pInf
    have h2 : Continuous (fun h : GA E a => toL (GeneralLinearGroup.map (pInf E) h).val) := h0
    exact ContinuousAt.comp (f := fun h : GA E a => toL (GeneralLinearGroup.map (pInf E) h).val) h1 h2.continuousAt
  have hev : ∀ᶠ h in 𝓝 (1 : GA E a), GeneralLinearGroup.map (pFin E) h ∈ {k | finRep E a k φ = φ} := by
    refine (continuous_map_pFin.continuousAt (x := (1 : GA E a))).eventually (hU.mem_nhds ?_)
    rw [map_one]
    change finRep E a 1 φ = φ
    simp
  have hG : ContinuousAt (fun h : GA E a => φ.1 (g * h)) 1 := by
    refine hF.congr ?_
    filter_upwards [hev] with h hh
    have e := congrArg (fun ψ : Sm E a => ψ.1 (g * infGL E a (GeneralLinearGroup.map (pInf E) h))) hh
    change φ.1 (g * infGL E a _ * finGL E a _) = φ.1 _ at e
    rw [mul_assoc, infGL_mul_finGL] at e
    rw [e, chart_val]
  have h2 : ContinuousAt (fun x : GA E a => g⁻¹ * x) g := (continuous_const.mul continuous_id).continuousAt
  have h3 : ContinuousAt (fun h : GA E a => φ.1 (g * h)) (g⁻¹ * g) := by rwa [inv_mul_cancel]
  simpa [Function.comp_def] using h3.comp h2


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_unip : Continuous (unip : (BlockIx a r → Ad E) → GA E a) := by
  have hn : Continuous (fun x : BlockIx a r → Ad E => (nilM x : Matrix (Fin a) (Fin a) (Ad E))) :=
    continuous_matrix fun i j => by
      simp only [nilM, Matrix.of_apply]
      split_ifs with h
      · exact continuous_apply _
      · exact continuous_const
  exact Units.continuous_iff.2 ⟨continuous_const.add hn, continuous_const.sub hn⟩


omit [_root_.NumberField.IsTotallyComplex E] in
theorem exists_isCompact_sub_mem :
    ∃ C : Set (BlockIx a r → Ad E), IsCompact C ∧ ∀ x, ∃ n ∈ ratN E a r, x - n ∈ C := by
  obtain ⟨K, hK, h⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  choose y hy using h
  refine ⟨Set.pi Set.univ fun _ => K, isCompact_univ_pi fun _ => hK, fun x => ?_⟩
  exact ⟨fun p => algebraMap E (Ad E) (y (x p)), ⟨fun p => y (x p), rfl⟩, fun p _ => hy (x p)⟩


omit [_root_.NumberField.IsTotallyComplex E] in
theorem periodic_integrand (φ : GA E a → ℂ) (hl : ∀ (γ : GL (Fin a) E) (g : GA E a), φ (ratGL E a γ * g) = φ g)
    (g : GA E a) {n : BlockIx a r → Ad E} (hn : n ∈ ratN E a r) (x : BlockIx a r → Ad E) :
    φ (unip (n + x) * g) = φ (unip x * g) := by
  obtain ⟨y, rfl⟩ := hn
  have e : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) y =
      fun p => algebraMap E (Ad E) (y p) := rfl
  rw [e, unip_add, unip_algebraMap, mul_assoc, hl]

theorem integrableOn_fundamentalDomain :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (φ : Sm E a),
      (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) →
      IsOpen {k | finRep E a k φ = φ} →
      ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
        (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratN E a r) 𝓕 μ →
        μ 𝓕 < ⊤ ∧ ∀ g : GA E a, IntegrableOn (fun x => φ.1 (unip x * g)) 𝓕 μ := by
  intro E _ _ _ a r φ hl hU _ _ μ 𝓕 hμ hF
  obtain ⟨C, hC, hcov⟩ := exists_isCompact_sub_mem (E := E) (a := a) (r := r)
  have hφ := continuous_of_isOpen_stab φ hU
  haveI : Countable (ratN E a r) := by
    have : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.countable_iff.2 inferInstance
    exact Function.Surjective.countable
      (f := (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)).rangeRestrict)
      (AddMonoidHom.rangeRestrict_surjective _)
  have hfin : μ 𝓕 < ⊤ := by
    have h1 : 𝓕 ⊆ ⋃ n : ratN E a r, (n +ᵥ C) ∩ 𝓕 := fun x hx => by
      obtain ⟨n, hn, h⟩ := hcov x
      refine Set.mem_iUnion.2 ⟨⟨n, hn⟩, ⟨x - n, h, ?_⟩, hx⟩
      simp [AddSubgroup.vadd_def]
    calc μ 𝓕 ≤ ∑' n : ratN E a r, μ ((n +ᵥ C) ∩ 𝓕) := (measure_mono h1).trans (measure_iUnion_le _)
      _ = μ C := (hF.measure_eq_tsum C).symm
      _ < ⊤ := hC.measure_lt_top
  refine ⟨hfin, fun g => ?_⟩
  have hc : Continuous fun x : BlockIx a r → Ad E => φ.1 (unip x * g) :=
    hφ.comp (continuous_unip.mul continuous_const)
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  refine Measure.integrableOn_of_bounded hfin.ne hc.aestronglyMeasurable (M := B) (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨n, hn, h⟩ := hcov x
  have := periodic_integrand φ.1 hl g hn (x - n)
  rw [add_sub_cancel] at this
  rw [this]
  exact hB _ h

end GlobalTheory.CompanionTheory.ConstTerm

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetConjUnitary
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Vol

def I0 : ℝ≥0∞ := ∫⁻ z : ℂ, ENNReal.ofReal (((1 + ‖z‖) ^ 3)⁻¹)

theorem I0_lt_top : I0 < ⊤ := by
  have h := integrable_one_add_norm (E := ℂ) (μ := volume) (r := 3)
    (by rw [Complex.finrank_real_complex]; norm_num)
  have h2 := h.lintegral_lt_top
  refine lt_of_le_of_lt (le_of_eq ?_) h2
  refine lintegral_congr fun z => ?_
  congr 1
  rw [Real.rpow_neg (by positivity), show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]

def wt (l : ℝ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (((1 + ‖z‖) ^ 3)⁻¹ * ((1 + |l| * ‖z‖) ^ 3)⁻¹)

theorem measurable_wt (l : ℝ) : Measurable (wt l) := by
  unfold wt
  fun_prop

theorem lint_scale {l : ℝ} (hl : l ≠ 0) :
    ∫⁻ z : ℂ, ENNReal.ofReal (((1 + |l| * ‖z‖) ^ 3)⁻¹) = ENNReal.ofReal ((l ^ 2)⁻¹) * I0 := by
  have hr : |l| ≠ 0 := abs_ne_zero.mpr hl
  have hm := Measure.map_addHaar_smul (volume : Measure ℂ) hr
  have hF : Measurable fun w : ℂ => ENNReal.ofReal (((1 + ‖w‖) ^ 3)⁻¹) := by fun_prop
  have h1 : ∫⁻ z : ℂ, ENNReal.ofReal (((1 + |l| * ‖z‖) ^ 3)⁻¹)
      = ∫⁻ w : ℂ, ENNReal.ofReal (((1 + ‖w‖) ^ 3)⁻¹) ∂(Measure.map (fun x : ℂ => |l| • x) volume) := by
    rw [lintegral_map hF (measurable_const_smul _)]
    refine lintegral_congr fun z => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_abs]
  rw [h1, hm, lintegral_smul_measure, Complex.finrank_real_complex]
  simp only [smul_eq_mul, I0]
  congr 2
  rw [abs_of_nonneg (by positivity), sq_abs]

theorem one_var (l : ℝ) :
    ∫⁻ z : ℂ, wt l z ≤ ENNReal.ofReal (2 * I0.toReal * (1 + l ^ 2)⁻¹) := by
  have hI : ENNReal.ofReal I0.toReal = I0 := ENNReal.ofReal_toReal I0_lt_top.ne
  have hI0 : 0 ≤ I0.toReal := ENNReal.toReal_nonneg
  rcases le_or_gt |l| 1 with h | h
  · have h1 : ∫⁻ z : ℂ, wt l z ≤ I0 := by
      refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
      have ha : (0:ℝ) ≤ ((1 + ‖z‖) ^ 3)⁻¹ := by positivity
      have hb : ((1 + |l| * ‖z‖) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀
        (one_le_pow₀ (by nlinarith [norm_nonneg z, abs_nonneg l]))
      nlinarith
    refine h1.trans ?_
    conv_lhs => rw [← hI]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : l ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg l]
    have h3 : (1 : ℝ) ≤ 2 * (1 + l ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      linarith
    nlinarith
  · have hl : l ≠ 0 := by
      rintro rfl
      simp at h
      linarith
    have h1 : ∫⁻ z : ℂ, wt l z ≤ ∫⁻ z : ℂ, ENNReal.ofReal (((1 + |l| * ‖z‖) ^ 3)⁻¹) := by
      refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
      have ha : (0:ℝ) ≤ ((1 + |l| * ‖z‖) ^ 3)⁻¹ := by positivity
      have hb : ((1 + ‖z‖) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀
        (one_le_pow₀ (by linarith [norm_nonneg z]))
      nlinarith
    refine h1.trans ?_
    rw [lint_scale hl]
    conv_lhs => rw [← hI]
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : 1 ≤ l ^ 2 := by
      rw [← sq_abs]
      nlinarith
    have h3 : (l ^ 2)⁻¹ ≤ 2 * (1 + l ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    nlinarith

theorem pi_bound {n : ℕ} (l : Fin n → ℝ) :
    ∫⁻ z : Fin n → ℂ, ∏ i, wt (l i) (z i) ≤
      ENNReal.ofReal ((2 * I0.toReal) ^ n * (∏ i, (1 + l i ^ 2))⁻¹) := by
  have hI0 : 0 ≤ I0.toReal := ENNReal.toReal_nonneg
  rw [volume_pi, GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod
    (f := fun i => wt (l i)) fun i => (measurable_wt (l i)).aemeasurable]
  refine (Finset.prod_le_prod' fun i _ => one_var (l i)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => by positivity, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_inv_distrib]

theorem prod_le_pow {n K : ℕ} (hK : 3 * n ≤ K) {x : Fin n → ℝ} {a : ℝ} (h0 : ∀ i, 0 ≤ x i)
    (hx : ∀ i, x i ≤ a) (ha : 0 ≤ a) :
    ((1 + a) ^ K)⁻¹ ≤ ∏ i, ((1 + x i) ^ 3)⁻¹ := by
  rw [Finset.prod_inv_distrib]
  refine inv_anti₀ (Finset.prod_pos fun i _ => by have := h0 i; positivity) ?_
  calc ∏ i, (1 + x i) ^ 3 ≤ ∏ _i : Fin n, (1 + a) ^ 3 :=
        Finset.prod_le_prod₀ (fun i _ => by have := h0 i; positivity)
          fun i _ => pow_le_pow_left₀ (by have := h0 i; positivity) (by linarith [hx i]) 3
    _ = (1 + a) ^ (3 * n) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
    _ ≤ (1 + a) ^ K := pow_le_pow_right₀ (by linarith) hK

theorem weight_le {n K : ℕ} (hK : 3 * n ≤ K) (l : Fin n → ℝ) {a d : ℝ} (z : Fin n → ℂ)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (h1 : ∀ i, ‖z i‖ ≤ a) (h2 : ∀ i, |l i| * ‖z i‖ ≤ d) :
    ENNReal.ofReal (((1 + a) ^ K)⁻¹ * ((1 + d) ^ K)⁻¹) ≤ ∏ i, wt (l i) (z i) := by
  unfold wt
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => by positivity, Finset.prod_mul_distrib]
  refine ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul (prod_le_pow hK (fun i => norm_nonneg _) h1 ha)
    (prod_le_pow hK (fun i => by positivity) h2 hd) (by positivity)
    (Finset.prod_nonneg fun i _ => by positivity)

theorem det_conj_unitary {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    det ((U : Matrix (Fin n) (Fin n) ℂ) * X * star (U : Matrix (Fin n) (Fin n) ℂ)) = det X := by
  rw [det_mul, det_mul, mul_comm (det (U : Matrix (Fin n) (Fin n) ℂ)), mul_assoc, ← det_mul,
    mem_unitaryGroup_iff.mp U.2, det_one, mul_one]

theorem detW_eq {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) :
    detW b = ∏ i, (1 + hb.eigenvalues i ^ 2) := by
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ hb.eigenvalues) with hD
  have hs := hb.spectral_theorem
  have h1 : 1 + b * b = Unitary.conjStarAlgAut ℂ _ hb.eigenvectorUnitary (1 + D * D) := by
    rw [map_add (f := _), map_one, map_mul, ← hs]
  have h2 : 1 + D * D = diagonal fun i => (((1 + hb.eigenvalues i ^ 2 : ℝ)) : ℂ) := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one, diagonal_add]
    congr 1
    ext i
    simp [sq]
  rw [detW, h1, Unitary.conjStarAlgAut_apply, det_conj_unitary, h2, det_diagonal,
    ← Complex.ofReal_prod, Complex.ofReal_re]

theorem repr_apply_lin {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian)
    (y : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    hb.eigenvectorBasis.repr (Matrix.toEuclideanLin b y) i =
      (hb.eigenvalues i : ℂ) * hb.eigenvectorBasis.repr y i := by
  have hs : (Matrix.toEuclideanLin b).IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hb
  have he : Matrix.toEuclideanLin b (hb.eigenvectorBasis i) =
      (hb.eigenvalues i : ℂ) • hb.eigenvectorBasis i := by
    have := hb.mulVec_eigenvectorBasis i
    apply PiLp.ext
    intro j
    have h2 := congrFun this j
    simpa [toLpLin_apply] using h2
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply, ← hs, he, inner_smul_left]
  simp

theorem map_isometry {n : ℕ} (m : Measure (EuclideanSpace ℂ (Fin n))) [m.IsAddHaarMeasure]
    (R : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    MeasurePreserving R m m := by
  have hp := LinearIsometryEquiv.measurePreserving
    (⟨R.toLinearEquiv.restrictScalars ℝ, R.norm_map⟩ :
      EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n))
  have hc := Measure.isAddLeftInvariant_eq_smul m (volume : Measure (EuclideanSpace ℂ (Fin n)))
  refine ⟨R.continuous.measurable, ?_⟩
  have hm : Measure.map R (volume : Measure (EuclideanSpace ℂ (Fin n))) = volume := hp.map_eq
  conv_lhs => rw [hc]
  rw [Measure.map_smul, hm, ← hc]
  exact R.continuous.aemeasurable

theorem exists_scale (n : ℕ) (m : Measure (EuclideanSpace ℂ (Fin n))) [m.IsAddHaarMeasure] :
    ∃ c : NNReal, ∀ P : (Fin n → ℂ) → ℝ≥0∞, Measurable P →
      ∫⁻ y, P (WithLp.ofLp y) ∂m = c * ∫⁻ x, P x := by
  let e := EuclideanSpace.equiv (Fin n) ℂ
  haveI : (Measure.map e m).IsAddHaarMeasure := e.isAddHaarMeasure_map m
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map e m = c • (volume : Measure (Fin n → ℂ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  refine ⟨c, fun P hP => ?_⟩
  have h1 : ∫⁻ y, P (WithLp.ofLp y) ∂m = ∫⁻ x, P x ∂(Measure.map e m) := by
    rw [lintegral_map hP e.continuous.measurable]
    rfl
  rw [h1, hc, lintegral_smul_measure]
  rfl

theorem volume_bound : ∀ (n K : ℕ), 3 * n ≤ K → ∀ m : Measure (EuclideanSpace ℂ (Fin n)), m.IsAddHaarMeasure →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : Matrix (Fin n) (Fin n) ℂ, b.IsHermitian →
    ∫⁻ y, ENNReal.ofReal (((1 + ‖y‖) ^ K)⁻¹ * ((1 + ‖Matrix.toEuclideanLin b y‖) ^ K)⁻¹) ∂m ≤
      ENNReal.ofReal (C * (detW b)⁻¹) := by
  intro n K hK m hm
  obtain ⟨c, hc⟩ := exists_scale n m
  have hI0 : 0 ≤ I0.toReal := ENNReal.toReal_nonneg
  refine ⟨c * (2 * I0.toReal) ^ n, by positivity, fun b hb => ?_⟩
  set l := hb.eigenvalues with hl
  set R := hb.eigenvectorBasis.repr with hR
  let P : (Fin n → ℂ) → ℝ≥0∞ := fun x => ∏ i, wt (l i) (x i)
  have hP : Measurable P :=
    Finset.measurable_prod _ fun i _ => (measurable_wt (l i)).comp (measurable_pi_apply i)
  have hG : Measurable fun y : EuclideanSpace ℂ (Fin n) => P (WithLp.ofLp y) :=
    hP.comp (EuclideanSpace.equiv (Fin n) ℂ).continuous.measurable
  have h1 : ∀ y : EuclideanSpace ℂ (Fin n),
      ENNReal.ofReal (((1 + ‖y‖) ^ K)⁻¹ * ((1 + ‖Matrix.toEuclideanLin b y‖) ^ K)⁻¹) ≤
        P (WithLp.ofLp (R y)) := by
    intro y
    refine weight_le hK l _ (norm_nonneg _) (norm_nonneg _) (fun i => ?_) (fun i => ?_)
    · rw [← R.norm_map y]
      exact PiLp.norm_apply_le (R y) i
    · rw [← R.norm_map (Matrix.toEuclideanLin b y)]
      refine le_trans (le_of_eq ?_) (PiLp.norm_apply_le (R (Matrix.toEuclideanLin b y)) i)
      rw [hR, repr_apply_lin hb, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc _ ≤ ∫⁻ y, P (WithLp.ofLp (R y)) ∂m := lintegral_mono h1
    _ = ∫⁻ y, P (WithLp.ofLp y) ∂m := (map_isometry m R).lintegral_comp hG
    _ = c * ∫⁻ x, P x := hc P hP
    _ ≤ c * ENNReal.ofReal ((2 * I0.toReal) ^ n * (∏ i, (1 + l i ^ 2))⁻¹) := by
        gcongr
        exact pi_bound l
    _ = ENNReal.ofReal (c * (2 * I0.toReal) ^ n * (detW b)⁻¹) := by
        rw [detW_eq hb, mul_assoc, ENNReal.ofReal_mul (p := (c : ℝ)) (by positivity),
          ENNReal.ofReal_coe_nnreal]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Vol
end
end

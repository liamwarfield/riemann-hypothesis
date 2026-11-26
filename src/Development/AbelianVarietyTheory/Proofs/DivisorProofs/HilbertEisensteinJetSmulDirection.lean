module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHilbertEisensteinFourierCoeffFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsSeparateQuotientGenericFibreDescends

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetSmulDirection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeJetSplitSmulDirection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagHomogeneous
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem lag_homogeneous : ∀ (k n : ℕ) (c y v : ℂ), lag k n (v * c) (v * y) = v ^ n * lag k n c y ∧ lag k n 0 y = y ^ n := by
  intro k n c y v
  refine ⟨?_, ?_⟩
  · unfold lag
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have h : v ^ n = v ^ (n - m) * v ^ m := by rw [← pow_add, Nat.sub_add_cancel hmn]
    rw [h, mul_pow, mul_pow]; ring
  · unfold lag
    rw [Finset.sum_range_succ, Finset.sum_eq_zero]
    · simp [rco]
    · intro m hm
      have hmn : n - m ≠ 0 := Nat.sub_ne_zero_of_lt (Finset.mem_range.mp hm)
      simp [hmn]

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeJetSplitSmulDirection
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem jet_split_smul_direction : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t v : ℂ) (κ : Emb F → ℕ), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → jet k (split 𝔞 𝔟 x) κ τ (v * c) (v * t) = v ^ (∑ i, κ i) * jet k (split 𝔞 𝔟 x) κ τ c t := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t v κ hk ha hτ
  have h1 := GlobalTheory.T.hasSum_hilbertEisenstein_jet_split_lattice F k 𝔞 𝔟 a₀ a x τ (v * c) (v * t) κ hk ha hτ
  have h2 := (GlobalTheory.T.hasSum_hilbertEisenstein_jet_split_lattice F k 𝔞 𝔟 a₀ a x τ c t κ hk ha hτ).mul_left (v ^ (∑ i, κ i))
  refine h1.unique (HasSum.congr_fun h2 fun ξ ↦ ?_)
  have hp : (∏ i : Emb F, lag k (κ i) (v * c) ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * (v * t))) =
      v ^ (∑ i, κ i) * ∏ i : Emb F, lag k (κ i) c ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [show (2 * Real.pi * Complex.I) * (i ξ : ℂ) * (v * t) = v * ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t) by ring]
    exact (lag_homogeneous k (κ i) c _ v).1
  rw [hp]; ring

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeJetSplitSmulDirectionStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisensteinLatticeJet_split_smul_direction : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t v : ℂ) (κ : Emb F → ℕ), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → jet k (split 𝔞 𝔟 x) κ τ (v * c) (v * t) = v ^ (∑ i, κ i) * jet k (split 𝔞 𝔟 x) κ τ c t := by
  first | exact @GlobalTheory.HilbFam.jet_split_smul_direction | exact GlobalTheory.HilbFam.jet_split_smul_direction | (intros; apply GlobalTheory.HilbFam.jet_split_smul_direction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetSmulDirection
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

set_option autoImplicit false

namespace GlobalTheory.HilbFam

theorem jet_smul_dir_of_hasLevel : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ c t v : ℂ) (κ : Emb F → ℕ), 0 < τ.im → jet (2 * s) L κ τ (v * c) (v * t) = v ^ (∑ i, κ i) * jet (2 * s) L κ τ c t := by
  intro hE F _ _ _ hf s N L hs hN hL τ c t v κ hτ
  obtain ⟨𝔞, 𝔟, x, rfl⟩ := GlobalTheory.T.exists_split_of_hilbertLatticeHasLevel F N L hN hL
  obtain ⟨Z, a, -, hc⟩ := GlobalTheory.T.exists_hilbertEisenstein_fourierCoeffFamily hE F hf 𝔞 𝔟 s hs
  exact GlobalTheory.T.hilbertEisensteinLatticeJet_split_smul_direction F (2 * s) 𝔞 𝔟 _ a x τ c t v κ (even_two_mul s) hc hτ

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetSmulDirectionStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_eisenstein_jet_smul_direction : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ c t v : ℂ) (κ : Emb F → ℕ), 0 < τ.im → jet (2 * s) L κ τ (v * c) (v * t) = v ^ (∑ i, κ i) * jet (2 * s) L κ τ c t := by
  first | exact @GlobalTheory.HilbFam.jet_smul_dir_of_hasLevel | exact GlobalTheory.HilbFam.jet_smul_dir_of_hasLevel | (intros; apply GlobalTheory.HilbFam.jet_smul_dir_of_hasLevel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedPresentationCocycleMemBialgebraSymmetr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedPresentationCocycleMemBialgebraSymmetr
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

open Algebra.TensorProduct in
theorem coc_mem_symCocycles (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (hg : IsSymCoc d.g) (n : ℕ) :
    d.coc n ∈ symCocycles R (G.A n) := by
  set H := G.A n

  have V : ∀ (D : Type) [CommRing D] [Algebra R D] (φ ψ : H →ₐ[R] D),
      lift φ ψ (fun _ _ ↦ Commute.all _ _) (d.coc n) = d.g D (spOver φ ≫ t.y n) (spOver ψ ≫ t.y n) -
        ((fv d.f H D (toConv φ * toConv ψ).ofConv (t.y n) + (toConv φ * toConv ψ).ofConv (d.h n)) -
          (fv d.f H D φ (t.y n) + φ (d.h n)) - (fv d.f H D ψ (t.y n) + ψ (d.h n))) :=
    fun D _ _ φ ψ ↦ GlobalTheory.T.cocycle_tensorLift_apply_eq_twoPointValue R A p G t c d n D φ ψ
  have M : ∀ (D : Type) [CommRing D] [Algebra R D] (φ ψ : H →ₐ[R] D),
      spOver (toConv φ * toConv ψ).ofConv ≫ t.y n = (spOver φ ≫ t.y n) * (spOver ψ ≫ t.y n) :=
    fun D _ _ φ ψ ↦ t.mul n D (toConv φ) (toConv ψ)
  rw [mem_symCocycles]
  constructor
  · let i1 : H →ₐ[R] H ⊗[R] (H ⊗[R] H) := includeLeft
    let i2 : H →ₐ[R] H ⊗[R] (H ⊗[R] H) := (includeRight : H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H)).comp includeLeft
    let i3 : H →ₐ[R] H ⊗[R] (H ⊗[R] H) := (includeRight : H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H)).comp includeRight
    let i12 := (toConv i1 * toConv i2).ofConv
    let i23 := (toConv i2 * toConv i3).ofConv
    have e1 : ∀ x : H ⊗[R] H, (1 : H) ⊗ₜ[R] x = lift i2 i3 (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | add x y hx hy => rw [tmul_add, map_add (f := _), hx, hy]
      | tmul a b => simp [i2, i3, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    have e2 : ∀ x : H ⊗[R] H, TensorProduct.assoc R H H H ((Coalgebra.comul (R := R) (A := H)).rTensor H x) =
        lift i12 i3 (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
      | tmul a b =>
        rw [LinearMap.rTensor_tmul, lift_tmul]
        simp only [i12, AlgHom.convMul_apply]
        induction (Coalgebra.comul (R := R) a : H ⊗[R] H) with
        | add x y hx hy => simp only [add_tmul, map_add (f := _), hx, hy, add_mul]
        | tmul a1 a2 => simp [i1, i2, i3, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    have e3 : ∀ x : H ⊗[R] H, (Coalgebra.comul (R := R) (A := H)).lTensor H x = lift i1 i23 (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      | tmul a b =>
        rw [LinearMap.lTensor_tmul, lift_tmul]
        simp only [i23, AlgHom.convMul_apply]
        induction (Coalgebra.comul (R := R) b : H ⊗[R] H) with
        | add x y hx hy => simp only [tmul_add, map_add (f := _), hx, hy, mul_add]
        | tmul b1 b2 => simp [i1, i2, i3, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    have e4 : ∀ x : H ⊗[R] H, ((TensorProduct.mk R H H).flip 1).lTensor H x =
        lift i1 i2 (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      | tmul a b => simp [i1, i2, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    rw [cobTwo_apply, e1, e2, e3, e4, V, V, V, V]
    simp only [i12, i23, toConv_ofConv, M]
    rw [_root_.mul_assoc (toConv i1) (toConv i2) (toConv i3)]
    have hc := (hg (H ⊗[R] (H ⊗[R] H))).2 (spOver i1 ≫ t.y n) (spOver i2 ≫ t.y n) (spOver i3 ≫ t.y n)
    linear_combination hc
  · have e : ∀ x : H ⊗[R] H, TensorProduct.comm R H H x =
        lift (includeRight : H →ₐ[R] H ⊗[R] H) (includeLeft : H →ₐ[R] H ⊗[R] H) (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    have e' : d.coc n = lift (includeLeft : H →ₐ[R] H ⊗[R] H) includeRight (fun _ _ ↦ Commute.all _ _) (d.coc n) := by
      exact (DFunLike.congr_fun (lift_includeLeft_includeRight (R := R) (S := R) (A := H) (B := H)) (d.coc n)).symm
    rw [e, V]
    conv_rhs => rw [e', V]
    rw [mul_comm (toConv (includeRight : H →ₐ[R] H ⊗[R] H)), (hg _).1]
    ring

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedPresentationCocycleMemBialgebraSymmetrStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.rigidifiedPresentation_cocycle_mem_bialgebraSymmetricCocycles :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
      (t : G.TorsionTower A) (c : primDR A) (d : Dat t c),
      IsSymCoc d.g → ∀ n, d.coc n ∈ symCocycles R (G.A n) :=
  @GlobalTheory.PtExt.coc_mem_symCocycles
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialScaledFini
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialScaledFini
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

open Polynomial

private theorem symTup_mul_left {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (a : R) (j : Fin N) :
    symTup (fun b => a * c b) j = a ^ N.factorial * symTup c j := by
  have h : (Finset.univ.val.map fun b => a * c b) = (Finset.univ.val.map c).map (fun x => a • x) := by
    rw [Multiset.map_map]; rfl
  have hd : ((j : ℕ) + 1) ∣ N.factorial := Nat.dvd_factorial (Nat.succ_pos _) j.isLt
  unfold symTup
  rw [h, ← Multiset.pow_smul_esymm, smul_eq_mul, mul_pow, ← pow_mul, Nat.mul_div_cancel' hd]

theorem symTup_eq_finite (K : Type) [Field K] (N : ℕ) (e : Fin N → K) :
    {c : Fin N → K | symTup c = e}.Finite := by
  classical

  let A : Fin (N + 1) → Set K := fun k =>
    {x | ((k : ℕ) = 0 → x = 1) ∧ ∀ j : Fin N, (j : ℕ) + 1 = k → x ^ (N.factorial / ((j : ℕ) + 1)) = e j}
  have hA : ∀ k, (A k).Finite := by
    intro k
    by_cases hk : (k : ℕ) = 0
    · exact (Set.finite_singleton (1 : K)).subset fun x hx => hx.1 hk
    · have hk1 : (k : ℕ) - 1 < N := by omega
      let j : Fin N := ⟨(k : ℕ) - 1, hk1⟩
      have hj : (j : ℕ) + 1 = k := by simp [j]; omega
      have hpos : 0 < N.factorial / ((j : ℕ) + 1) :=
        Nat.div_pos ((Nat.succ_le_of_lt j.isLt).trans (Nat.self_le_factorial N)) (Nat.succ_pos _)
      refine (Polynomial.finite_setOf_isRoot (X_pow_sub_C_ne_zero hpos (e j))).subset ?_
      intro x hx
      simp [IsRoot, hx.2 j hj]
  let V : Set (Fin (N + 1) → K) := Set.pi Set.univ A
  have hV : V.Finite := Set.Finite.pi hA
  let poly : (Fin (N + 1) → K) → K[X] := fun s =>
    ∑ k : Fin (N + 1), (-1) ^ (k : ℕ) * (C (s k) * X ^ (N - (k : ℕ)))
  let R : Set K := ⋃ p ∈ poly '' V, {x | x ∈ p.roots}
  have hR : R.Finite := (hV.image poly).biUnion fun p _ => Multiset.finite_toSet p.roots
  refine (Set.Finite.pi (t := fun _ : Fin N => R) fun _ => hR).subset ?_
  intro c hc
  simp only [Set.mem_setOf_eq] at hc
  let m : Multiset K := Finset.univ.val.map c
  have hm : Multiset.card m = N := by simp [m]
  let s : Fin (N + 1) → K := fun k => m.esymm k
  have hs : s ∈ V := by
    intro k _
    refine ⟨fun hk => ?_, fun j hj => ?_⟩
    · simp [s, hk, Multiset.esymm]
    · have := congrFun hc j
      simp only [symTup] at this
      simp only [s, ← hj]
      exact this
  have hpoly : poly s = (m.map fun t => X - C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, hm, Finset.sum_range (fun j => (-1) ^ j * (C (m.esymm j) * X ^ (N - j)))]
  intro a _
  simp only [R, Set.mem_iUnion, Set.mem_image]
  refine ⟨poly s, ⟨s, hs, rfl⟩, ?_⟩
  simp only [Set.mem_setOf_eq, hpoly, Polynomial.roots_multiset_prod_X_sub_C]
  exact Multiset.mem_map_of_mem c (Finset.mem_univ a)

theorem symTup_scale_finite : ∀ (K : Type) [Field K] [IsAlgClosed K] (N : ℕ) (e : Fin N → K), ∃ T : Finset (Fin N → K),
    ∀ (c : Fin N → K) (a : K), a ≠ 0 → (∀ j, symTup c j = a * e j) → ∃ mu : K, mu ≠ 0 ∧ (fun b => mu * c b) ∈ T := by
  intro K _ _ N e
  refine ⟨(symTup_eq_finite K N e).toFinset, ?_⟩
  intro c a ha hc
  obtain ⟨mu, hmu⟩ := IsAlgClosed.exists_pow_nat_eq a⁻¹ (Nat.factorial_pos N)
  have hmu0 : mu ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.factorial_pos N).ne'] at hmu
    exact inv_ne_zero ha hmu.symm
  refine ⟨mu, hmu0, ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  funext j
  rw [symTup_mul_left, hmu, hc, ← _root_.mul_assoc, inv_mul_cancel₀ ha, _root_.one_mul]

end GlobalTheory.UMin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialScaledFiniStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSymmetricFunctionsDegreeFactorial_scaled_finite : ∀ (K : Type) [Field K] [IsAlgClosed K] (N : ℕ) (e : Fin N → K), ∃ T : Finset (Fin N → K), ∀ (c : Fin N → K) (a : K), a ≠ 0 → (∀ j, symTup c j = a * e j) → ∃ mu : K, mu ≠ 0 ∧ (fun b => mu * c b) ∈ T := by
  first | exact @GlobalTheory.UMin.symTup_scale_finite | exact GlobalTheory.UMin.symTup_scale_finite | (intros; apply GlobalTheory.UMin.symTup_scale_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackFormVanishesTangentsOfLieBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackFormVanishesTangentsOfLieBasis
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR
open MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieDual

variable {R R' : Type} [CommRing R] [CommRing R']

theorem tanVal_pullForm_baseChange {σ : R →+* R'} {A : Over (Sp R)} {B : Over (Sp R')}
    {φ : B.left ⟶ A.left}
    (m : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R') (B.hom ≫ 𝟙 _) σ φ) {v : epsR R ⟶ A} {v' : epsR R' ⟶ B}
    (e : v'.left ≫ φ = spMap (Chart.dualMapR σ) ≫ v.left) (f : Form (A.hom ≫ 𝟙 _)) :
    tanVal v' (m.pullForm f) = σ (tanVal v f) := by
  let E := SqExt.dual R
  let E' := SqExt.dual R'
  have hy := pt_w v
  have hy' := pt_w v'
  have hc : ∀ r : R, Chart.dualMapR σ (algebraMap R (DualNumber R) r) =
      algebraMap R' (DualNumber R') (σ r) := fun r => by
    ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have e₀ : spMap σ ≫ spMap (E.π : E.C →+* E.B) ≫ v.left =
      (spMap (E'.π : E'.C →+* E'.B) ≫ v'.left) ≫ φ := by
    rw [Category.assoc, e, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 2
    ext a <;> simp [Chart.dualMapR, E, E', TrivSqZeroExt.algebraMap_eq_inl]
  let Φ : E.thick _ (E.red_w hy) ⟶ m.obj (E'.thick _ (E'.red_w hy')) :=
    { φ := { Chart.dualMapR σ with commutes' := hc }
      φ₀ := σ
      comm := fun b => by
        change σ b.fst = (Chart.dualMapR σ b).fst
        simp [Chart.dualMapR]
      dp := isDPMorphism_sqDP E.sq E'.sq _ fun a ha => by
        have ha' : a.fst = 0 := ha
        change (Chart.dualMapR σ a).fst = 0
        simp [Chart.dualMapR, ha']
      pt := e₀ }
  let a : Thick.triv E.C _ hy ⟶ m.obj (Thick.triv E'.C _ hy') :=
    Thick.trivHom { Chart.dualMapR σ with commutes' := hc } e.symm
  let b : Thick.triv E.B _ (E.red_w hy) ⟶ m.obj (Thick.triv E'.B _ (E'.red_w hy')) :=
    Thick.trivHom { σ with commutes' := fun _ => rfl } e₀
  have k1 := Form.ev_sq f a (m.functor.map (E'.idHom hy')) (E.idHom hy) Φ rfl rfl fun _ => rfl
  have k2 := Form.ev_sq f b (m.functor.map (E'.secHom (E'.red_w hy') E'.i E'.π_i))
    (E.secHom (E.red_w hy) E.i E.π_i) Φ rfl rfl fun c => (hc c).symm
  have k : E'.val v'.left hy' (m.pullForm f).1 = Chart.dualMapR σ (E.val v.left hy f.1) :=
    (congrArg₂ (fun u v : E'.C => u - v) k2 k1).trans
      ((add_sub_add_right_eq_sub (G := E'.C) _ _ _).trans (map_sub (Chart.dualMapR σ) _ _).symm)
  rw [tanVal_apply, tanVal_apply]
  refine (congrArg (TrivSqZeroExt.snd (R := R')) k).trans ?_
  exact zero_add _

theorem tanVal_list_prod_eq_zero {A : Over (Sp R)} [GrpObj A] (f : Form (A.hom ≫ 𝟙 _)) :
    ∀ l : List (epsR R ⟶ A), (∀ u ∈ l, IsTangent u ∧ tanVal u f = 0) →
      IsTangent l.prod ∧ tanVal l.prod f = 0 := by
  intro l
  induction l with
  | nil =>
    intro _
    refine ⟨?_, by rw [List.prod_nil]; exact tanVal_one f⟩
    rw [List.prod_nil, GrpTangent.isTangent_iff, MonObj.comp_one]
  | cons u l ih =>
    intro h
    obtain ⟨hu, hu0⟩ := h u List.mem_cons_self
    obtain ⟨hl, hl0⟩ := ih fun w hw => h w (List.mem_cons_of_mem _ hw)
    rw [List.prod_cons]
    refine ⟨?_, by rw [tanVal_mul hu hl, hu0, hl0, add_zero]⟩
    rw [GrpTangent.isTangent_iff] at hu hl ⊢
    rw [MonObj.comp_mul, hu, hl, _root_.mul_one]

theorem tanVal_pullForm_eq_zero_of_lieBasis : ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], Smooth B.hom → ∀ (n : ℕ) (y : Fin n → (epsR R ⟶ B)), IsLieBasis y → ∀ f : Form (B.hom ≫ 𝟙 (Sp R)), (∀ i, tanVal (y i) f = 0) → ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (B' : Over (Sp R')) [GrpObj B'] [IsCommMonObj B'] (φ : B'.left ⟶ B.left), IsGrpPullback B' B (spMap σ) φ → ∀ (m : IsMor (dp0 R) (B.hom ≫ 𝟙 (Sp R)) (dp0 R') (B'.hom ≫ 𝟙 (Sp R')) σ φ) (v : epsR R' ⟶ B'), IsTangent v → tanVal v (m.pullForm f) = 0 := by
  intro R _ B _ _ hs n y hy f hf R' _ σ B' _ _ φ hφ m v hv
  obtain ⟨y', hy', e⟩ := GlobalTheory.exists_isLieBasis_baseChange R R' σ B B' φ hφ hs n y hy
  have h0 : ∀ i, tanVal (y' i) (m.pullForm f) = 0 := fun i => by
    rw [tanVal_pullForm_baseChange m (e i) f, hf i, map_zero]
  obtain ⟨c, ⟨u, hu, rfl⟩, -⟩ := hy'.2 v hv
  have hu' : ∀ i, u i = GrpTangent.epsScale (c i) ≫ y' i := fun i => Over.OverMorphism.ext (hu i)
  refine (tanVal_list_prod_eq_zero (m.pullForm f) _ fun w hw => ?_).2
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hw
  rw [hu' i]
  exact ⟨GrpTangent.isTangent_epsScale _ (hy'.1 i), by rw [tanVal_epsScale, h0 i, mul_zero]⟩

end GlobalTheory.LieDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackFormVanishesTangentsOfLieBasisStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackForm_vanishes_tangents_of_lieBasis : ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], Smooth B.hom → ∀ (n : ℕ) (y : Fin n → (epsR R ⟶ B)), IsLieBasis y → ∀ f : Form (B.hom ≫ 𝟙 (Sp R)), (∀ i, tanVal (y i) f = 0) → ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (B' : Over (Sp R')) [GrpObj B'] [IsCommMonObj B'] (φ : B'.left ⟶ B.left), IsGrpPullback B' B (spMap σ) φ → ∀ (m : IsMor (dp0 R) (B.hom ≫ 𝟙 (Sp R)) (dp0 R') (B'.hom ≫ 𝟙 (Sp R')) σ φ) (v : epsR R' ⟶ B'), IsTangent v → tanVal v (m.pullForm f) = 0 := by
  first | exact @GlobalTheory.LieDual.tanVal_pullForm_eq_zero_of_lieBasis | exact GlobalTheory.LieDual.tanVal_pullForm_eq_zero_of_lieBasis | (intros; apply GlobalTheory.LieDual.tanVal_pullForm_eq_zero_of_lieBasis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelThetaPointOfThetaConstantsLevelSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelThetaPointOfThetaConstantsLevelSquare
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem nonempty_level_algClosed (hL : Laws) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (M : ℕ)
    (hM : (M : K) ≠ 0) (ze : Γ(Sp K, ⊤)ˣ) (hz : IsPrimitiveRoot ze M) : Nonempty (Level P M ze) := by
  let e := Scheme.ΓSpecIso (CommRingCat.of K)
  let z' : Kˣ := Units.map e.hom.hom.toMonoidHom ze
  have hz' : IsPrimitiveRoot z' M := hz.map_of_injective (f := Units.map e.hom.hom.toMonoidHom)
    (Units.map_injective (ConcreteCategory.bijective_of_isIso e.hom).1)
  have hze : unitOn z' = ze := Units.ext (e.hom_inv_id_apply (ze : Γ(Sp K, ⊤)))
  obtain ⟨pt, hpt, hw⟩ := EllipticLevel.exists_symplectic_system hL P M hM z' hz'
  rw [hze] at hw
  have nt : ∀ (F : Type) [Field F], Nontrivial Γ(Spec (CommRingCat.of F), ⊤) := fun F _ =>
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  obtain ⟨lev, -⟩ := exists_level_of_pairing hL.globalFns hL.weil hL.mulN (Sp K) P M ze hz
    (fun F _ s => by
      have := nt F
      refine ⟨?_, ?_⟩
      · rw [← map_natCast (Spec.preimage s).hom]; exact (map_ne_zero _).2 hM
      · rw [← hze]
        exact hz'.map_of_injective (f := Units.map (s.appTop.hom.comp e.inv.hom).toMonoidHom)
          (Units.map_injective (RingHom.injective _)))
    pt hpt hw
  exact ⟨lev⟩

theorem exists_level_isThetaPt_of_hasTh : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (rig : LB.Gen (P.L.pull (eSec P.A))) (g m N : ℕ) (hg : P.g = g) (c : Fin N → K) (ze : Γ(Sp K, ⊤)ˣ), rig.IsGen → Odd m → (m : K) ≠ 0 → IsPrimitiveRoot ze (m ^ 2) → HasTh P.A P.L rig m (𝟙 (Sp K)) c → ∃ (lev : Out.Level P (m ^ 2) ze) (β : (Fin (2 * g) → ZMod (m ^ 2)) → Fin N), ∀ mu : K, mu ≠ 0 → IsThetaPt P m (levelPoint lev hg) (fun a => GlobalTheory.ZH.fn (mu * c (β a))) := by
  intro K _ _ P rig g m N hg c ze hrig hm hK hze hc
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hK2 : ((m ^ 2 : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hK
  obtain ⟨lev⟩ := nonempty_level_algClosed hL K P (m ^ 2) hK2 ze hze
  obtain ⟨v, hv⟩ := ThetaPtDet.exists_thetaPt_of_level hL K P hg m hm hK lev
  let e := Scheme.ΓSpecIso (CommRingCat.of K)
  let v' : (Fin (2 * g) → ZMod (m ^ 2)) → K := fun a => e.hom.hom (v a)
  have hvv : v = fun a => GlobalTheory.Ex.fnOf (v' a) := funext fun a => (e.hom_inv_id_apply (v a)).symm
  rw [hvv] at hv
  obtain ⟨th, hth, hthG⟩ :=
    exists_gen_thG_of_isThetaPt K P rig hrig m _ (levelPoint lev hg) v' (ThetaPtDet.levelPoint_pow lev hg) hv
  obtain ⟨θ, pt, hgen, hinj, hG, hall⟩ := hc
  have hβ : ∀ a, ∃ b, pt b = levelPoint lev hg a := fun a => by
    let u : Over.mk (spMap (RingHom.id K) ≫ 𝟙 (Sp K)) ⟶ Over.mk (𝟙 (Sp K)) := Over.homMk (spMap (RingHom.id K)) rfl
    obtain ⟨b, hb⟩ := hall K (RingHom.id K) (u ≫ levelPoint lev hg a) (by
      rw [← MonObj.comp_pow, ThetaPtDet.levelPoint_pow, MonObj.comp_one])
    exact ⟨b, TorsionFieldExt.comp_injective u _ (Over.OverMorphism.ext hb.symm)⟩
  choose β hβ using hβ
  refine ⟨lev, β, fun mu hmu => ?_⟩
  have hun : IsUnit ((m ^ 2 : ℕ) : Γ(Sp K, ⊤)) := by
    rw [← map_natCast e.inv.hom]
    exact (IsUnit.mk0 _ hK2).map _
  obtain ⟨s, hs⟩ := hth θ
  have e₁ : SecM.ofSec P.A θ = s • SecM.ofSec P.A th := Subtype.ext (funext hs)
  obtain ⟨r, hr⟩ := hgen th
  have e₂ : SecM.ofSec P.A th = r • SecM.ofSec P.A θ := Subtype.ext (funext hr)
  have k₁ : ∀ a, c (β a) = e.hom.hom s * v' a := fun a => by
    have q₁ := hG (β a)
    rw [hβ a] at q₁
    have q := congrArg e.hom.hom (ThG.unique hL P hm hun q₁ (ThG.smul P.isLB e₁ (hthG a)))
    rw [map_mul, show e.hom.hom (GlobalTheory.ZH.fn (c (β a))) = c (β a) from e.inv_hom_id_apply _,
      show e.hom.hom (GlobalTheory.Ex.fnOf (v' a)) = v' a from e.inv_hom_id_apply _] at q
    exact q
  have k₂ : ∀ a, v' a = e.hom.hom r * c (β a) := fun a => by
    have q₁ := hG (β a)
    rw [hβ a] at q₁
    have q := congrArg e.hom.hom (ThG.unique hL P hm hun (hthG a) (ThG.smul P.isLB e₂ q₁))
    rw [map_mul, show e.hom.hom (GlobalTheory.ZH.fn (c (β a))) = c (β a) from e.inv_hom_id_apply _,
      show e.hom.hom (GlobalTheory.Ex.fnOf (v' a)) = v' a from e.inv_hom_id_apply _] at q
    exact q
  by_cases hs₀ : e.hom.hom s = 0
  · have h0 : ∀ a, c (β a) = 0 := fun a => by rw [k₁, hs₀, zero_mul]
    have : (fun a => GlobalTheory.ZH.fn (mu * c (β a))) = fun a => GlobalTheory.Ex.fnOf (v' a) := funext fun a => by
      rw [k₂, h0, mul_zero, mul_zero]
    rw [this]
    exact hv
  · refine GenericObject.isThetaPt_unit_mul P m (levelPoint lev hg) _ _ (e.inv.hom (mu * e.hom.hom s))
      ((IsUnit.mk0 _ (mul_ne_zero hmu hs₀)).map _) (fun a => ?_) hv
    rw [k₁, ← _root_.mul_assoc]
    exact map_mul e.inv.hom _ _

end GlobalTheory.UMin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelThetaPointOfThetaConstantsLevelSquareStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_thetaPoint_of_thetaConstants_level_square : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (rig : LB.Gen (P.L.pull (eSec P.A))) (g m N : ℕ) (hg : P.g = g) (c : Fin N → K) (ze : Γ(Sp K, ⊤)ˣ), rig.IsGen → Odd m → (m : K) ≠ 0 → IsPrimitiveRoot ze (m ^ 2) → HasTh P.A P.L rig m (𝟙 (Sp K)) c → ∃ (lev : Out.Level P (m ^ 2) ze) (β : (Fin (2 * g) → ZMod (m ^ 2)) → Fin N), ∀ mu : K, mu ≠ 0 → IsThetaPt P m (levelPoint lev hg) (fun a => GlobalTheory.ZH.fn (mu * c (β a))) := by
  first | exact @GlobalTheory.UMin.exists_level_isThetaPt_of_hasTh | exact GlobalTheory.UMin.exists_level_isThetaPt_of_hasTh | (intros; apply GlobalTheory.UMin.exists_level_isThetaPt_of_hasTh <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigLineBundleKodairaLemma
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KodairaLemma

theorem lineBundleGlobalSectionsDim_eq_zero_of_isEmpty (k : Type) [Field k] {Z : Scheme.{0}} [Algebra k Γ(Z, ⊤)] [IsEmpty Z]
    (L : LB Z) : lbH0 k L = 0 := by
  have e : (⊤ : Z.Opens) = ⊥ := Opens.ext (Set.eq_empty_of_isEmpty _)
  have : Subsingleton Γ(Z, ⊤) := by rw [e]; infer_instance
  have : Subsingleton L.Sec := Module.subsingleton Γ(Z, ⊤) _
  have : Subsingleton (coh (twist (structureModule Z) L) 0) := (cohZeroTwistEquiv L).toEquiv.subsingleton
  exact Module.finrank_zero_of_subsingleton

theorem isEmpty_zeroScheme {X : Scheme.{0}} [IsIntegral X] (hd : topologicalKrullDim X ≤ 0) {L : LB X}
    (hL : L.IsLB) (t : L.Sec) (ht : genericPoint X ∈ nonzeroLocus t) :
    IsEmpty (GlobalTheory.ThickeningDetermines.secIdeal hL t).subscheme := by
  refine ⟨fun z => ?_⟩
  have hx : (GlobalTheory.ThickeningDetermines.secIdeal hL t).subschemeι z ∈
      ((GlobalTheory.ThickeningDetermines.secIdeal hL t).support : Set X) := by
    rw [← (GlobalTheory.ThickeningDetermines.secIdeal hL t).range_subschemeι]; exact ⟨z, rfl⟩
  rw [coe_support_secIdeal] at hx
  set x := (GlobalTheory.ThickeningDetermines.secIdeal hL t).subschemeι z
  have hmax := Order.krullDim_nonpos_iff_forall_isMax.1
    (show Order.krullDim (IrreducibleCloseds X) ≤ 0 from hd)
  have hst : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  let A : IrreducibleCloseds X := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let B : IrreducibleCloseds X := ⟨closure {genericPoint X}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hAB : A ≤ B := specializes_iff_closure_subset.1 hst
  have hBA : B ≤ A := hmax A hAB
  have hts : x ⤳ genericPoint X := specializes_iff_closure_subset.2 hBA
  exact hx (hts.mem_open (nonzeroLocus t).isOpen ht)

open GlobalTheory.ThickeningDetermines (secIdeal)
open GlobalTheory.QuotSep

theorem exists_nsmul_cls_eq_add_toPic_of_isBig : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), IsProjOver p → ∀ (M A : LB X) (hM : letI := algebraΓOfHom p; IsBig k M) (hA : IsAmpleLB A), ∃ (a : ℕ) (D : CartierDiv X), 0 < a ∧ D.Eff ∧ a • cls M (letI := algebraΓOfHom p; hM.isLB) = cls A hA.isLB + toPic D := by
  intro k _ _ X _ p hp M A hM hA
  letI := algebraΓOfHom p
  have hp' : IsProjOver (strHom k (X := X)) := by rwa [strHom_eq (f := p) fun _ => rfl]
  have := isNoetherian_of_isProjOver hp'
  suffices h : ∃ a : ℕ, 0 < a ∧ ∃ (N : LB X) (hN : N.IsLB),
      cls N hN = a • cls M hM.isLB - cls A hA.isLB ∧ HasNonzeroSec N by
    obtain ⟨a, ha, N, hN, e, hs⟩ := h
    obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 hs
    refine ⟨a, divOfSec hN s hs, ha, GlobalTheory.PairStep.eff_divOfSec_of_sec hN s hs, ?_⟩
    rw [(presents_divOfRatSec hN (isRatSec_ratOfSec s hs)).toPic_eq, e]
    abel
  obtain ⟨q, hq, hq'⟩ := hA.exists_hasNonzeroSec (LB.isLB_triv X)
  have hAq : IsAmpleLB (lbPow A q) := (isAmpleLB_pow_iff hA.isLB hq).2 hA
  obtain ⟨r, -, hr'⟩ := hAq.exists_hasNonzeroSec (isLB_dual hA.isLB)
  have hP : (lbPow (lbPow A q) r).IsLB := isLB_lbPow hAq.isLB r
  have hPs : HasNonzeroSec (lbPow (lbPow A q) r) :=
    (hq' _ hAq.isLB (by rw [cls_triv, zero_add, cls_lbPow hA.isLB])).pow hAq.isLB r
  have hE := isLB_tens (isLB_dual hA.isLB) hP
  have hEs : HasNonzeroSec (tens (dual A) (lbPow (lbPow A q) r)) :=
    hr' _ hE (by rw [cls_tens (isLB_dual hA.isLB) hP, cls_lbPow hAq.isLB])
  obtain ⟨t, ht⟩ := hasNonzeroSec_iff.1 hPs
  have ht0 : t ≠ 0 := sec_ne_zero_of_mem ht
  letI := algebraΓAlong k (secIdeal hP t).subschemeι
  obtain ⟨m, hm, hlt⟩ : ∃ m : ℕ, 0 < m ∧
      lbH0 k ((lbPow M m).pull (secIdeal hP t).subschemeι) < lbH0 k (lbPow M m) := by
    obtain ⟨D, hD, c, hc, hfreq⟩ := hM.growth
    rcases D with _ | d
    · have hd0 : topologicalKrullDim X ≤ 0 := by rw [hD]; rfl
      haveI := isEmpty_zeroScheme hd0 hP t ht
      obtain ⟨m, hcm, hm⟩ := (hfreq.and_eventually (eventually_ge_atTop 1)).exists
      refine ⟨m, hm, ?_⟩
      rw [lineBundleGlobalSectionsDim_eq_zero_of_isEmpty]
      have h0 : (0 : ℝ) < lbH0 k (lbPow M m) := hc.trans_le (by simpa using hcm)
      exact_mod_cast h0
    · set ι := (secIdeal hP t).subschemeι
      have hMι := LB.isLB_pull hM.isLB ι
      obtain ⟨C, hC⟩ := GlobalTheory.exists_hdim_twist_lbPow_zero_le k _ (isProjOver_along hp' ι) d (M.pull ι) hMι
        (structureModule _) (by rw [QCoh.suppDim_structureModule]; exact dim_zeroScheme_le hP ht0 hD.le)
      have hev : ∀ᶠ m : ℕ in atTop, (C : ℝ) * 2 ^ d < c * m :=
        (tendsto_natCast_atTop_atTop.const_mul_atTop hc).eventually_gt_atTop _
      obtain ⟨m, h₁, h₂, h₃⟩ := (hfreq.and_eventually (hev.and (eventually_ge_atTop 1))).exists
      refine ⟨m, h₃, ?_⟩
      have e₂ : lbH0 k ((lbPow M m).pull ι) = lbH0 k (lbPow (M.pull ι) m) :=
        lineBundleGlobalSectionsDim_congr_picardClass (LB.isLB_pull (isLB_lbPow hM.isLB m) ι) (isLB_lbPow hMι m)
          ((cls_eq_iff _ _).2 (lbIso_lbPow_pull hM.isLB ι m)).symm
      rw [e₂]
      by_contra hle
      push_neg at hle
      have hb : (lbH0 k (lbPow (M.pull ι) m) : ℝ) ≤ C * ((m : ℝ) + 1) ^ d := by exact_mod_cast hC m
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h₃
      have hm2 : ((m : ℝ) + 1) ^ d ≤ 2 ^ d * (m : ℝ) ^ d := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) d
      have hle' : (lbH0 k (lbPow M m) : ℝ) ≤ lbH0 k (lbPow (M.pull ι) m) := by exact_mod_cast hle
      have hmd : (0 : ℝ) < (m : ℝ) ^ d := pow_pos (by linarith) d
      have h₄ := mul_lt_mul_of_pos_right h₂ hmd
      have h₅ := mul_le_mul_of_nonneg_left hm2 (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
      push_cast at h₁
      rw [pow_succ] at h₁
      nlinarith
  have hB := isLB_lbPow hM.isLB m
  have e₁ := globalSections_dim_le_div_add_restriction hp' hP hB ht0
  have hpos : 0 < lbH0 k (LB.div (lbPow M m) (lbPow (lbPow A q) r)) := by omega
  have hD := LB.isLB_div hB hP
  refine ⟨m, hm, _, isLB_tens hD hE, ?_, (lineBundleHasNonzeroSection_of_globalSectionsDim_pos hpos).tens hEs hD hE⟩
  rw [cls_tens hD hE, cls_div hB hP, cls_lbPow hM.isLB, cls_tens (isLB_dual hA.isLB) hP,
    cls_dual hA.isLB, cls_lbPow hAq.isLB, cls_lbPow hA.isLB]
  abel

end GlobalTheory.KodairaLemma
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralElementAffineSectionGenerated
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddSumIntegral
namespace GlobalTheory.IntegralAddSum

theorem add_sum_integral {A C K B : Type} [CommRing A] [CommRing C] [CommRing K] [CommRing B]
    (φ : A →+* K) (gc : C →+* B) (gk : K →+* B) {x y : B}
    (hx : ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K),
      (∀ m : Fin n, RingHom.IsIntegralElem φ (b m)) ∧ x = ∑ m : Fin n, gc (c m) * gk (b m))
    (hy : ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K),
      (∀ m : Fin n, RingHom.IsIntegralElem φ (b m)) ∧ y = ∑ m : Fin n, gc (c m) * gk (b m)) :
    ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K),
      (∀ m : Fin n, RingHom.IsIntegralElem φ (b m)) ∧ x + y = ∑ m : Fin n, gc (c m) * gk (b m) := by
  obtain ⟨n, c, b, hb, rfl⟩ := hx
  obtain ⟨n', c', b', hb', rfl⟩ := hy
  refine ⟨n + n', Fin.append c c', Fin.append b b', ?_, ?_⟩
  · intro m
    refine Fin.addCases (fun i => ?_) (fun i => ?_) m
    · rw [Fin.append_left]; exact hb i
    · rw [Fin.append_right]; exact hb' i
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

end GlobalTheory.IntegralAddSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralElementAffineSectionGenerated
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem sumForm_add {A C K B : Type} [CommRing A] [CommRing C] [CommRing K] [CommRing B]
    (φ : A →+* K) (gc : C →+* B) (gk : K →+* B) {x y : B}
    (hx : ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K), (∀ m, φ.IsIntegralElem (b m)) ∧ x = ∑ m, gc (c m) * gk (b m))
    (hy : ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K), (∀ m, φ.IsIntegralElem (b m)) ∧ y = ∑ m, gc (c m) * gk (b m)) :
    ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K), (∀ m, φ.IsIntegralElem (b m)) ∧ x + y = ∑ m, gc (c m) * gk (b m) := by
  first
  | exact @_root_.GlobalTheory.IntegralAddSum.add_sum_integral
  | exact _root_.GlobalTheory.IntegralAddSum.add_sum_integral
  | (apply _root_.GlobalTheory.IntegralAddSum.add_sum_integral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralAddSum.add_sum_integral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralAddSum.add_sum_integral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralAddSum.add_sum_integral ..)

theorem isAffineOpen_Sp_field (K : Type) [Field K] (V : (Sp K).Opens) : IsAffineOpen V := by
  haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  by_cases h : (V : Set (Sp K)).Nonempty
  · obtain ⟨x, hx⟩ := h
    have : V = ⊤ := by
      ext y
      simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      exact Subsingleton.elim x y ▸ hx
    rw [this]; exact isAffineOpen_top _
  · have : V = ⊥ := by
      ext y
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hy => h ⟨y, hy⟩
    rw [this]; exact isAffineOpen_bot _

theorem eq_sum_of_isIntegral_genericChart : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (W : G.left.Opens) (U : M.S.Opens) (hWU : W ≤ G.hom ⁻¹ᵁ U), IsAffineOpen W → IsAffineOpen U → ∀ f : Γ(Y, α ⁻¹ᵁ W), (α.app W).hom.IsIntegralElem f → ∃ (n : ℕ) (c : Fin n → Γ(G.left, W)) (b : Fin n → Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)), (∀ m, (M.gp.app U).hom.IsIntegralElem (b m)) ∧ f = ∑ m, (α.app W).hom (c m) * (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) (locInt_le_gen G.hom α t M.gp hpb.w W U hWU)).hom (b m) := by
  intro R _ _ M G hG Y α t hpb W U hWU hW hU f hf
  have hV : IsAffineOpen (M.gp ⁻¹ᵁ U) := isAffineOpen_Sp_field _ _
  have hle := locInt_le_gen G.hom α t M.gp hpb.w W U hWU
  have hUY : α ⁻¹ᵁ W = α ⁻¹ᵁ W ⊓ t ⁻¹ᵁ (M.gp ⁻¹ᵁ U) := (inf_eq_left.2 hle).symm
  have po := (isIso_pushoutSection_iff hpb (US := U) (UT := M.gp ⁻¹ᵁ U) (UX := W) le_rfl hWU hUY).mp
    (isIso_pushoutSection_of_isAffineOpen hpb le_rfl hWU hUY hU hV hW)
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app] at po
  letI : Algebra Γ(M.S, U) Γ(G.left, W) := (G.hom.appLE U W hWU).hom.toAlgebra
  letI : Algebra Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) := (M.gp.app U).hom.toAlgebra
  letI : Algebra Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom.toAlgebra
  letI : Algebra Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) hle).hom.toAlgebra
  letI : Algebra Γ(M.S, U) Γ(Y, α ⁻¹ᵁ W) := (G.hom.appLE U W hWU ≫ α.app W).hom.toAlgebra
  haveI : IsScalarTower Γ(M.S, U) Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom po.w)
  haveI : Algebra.IsPushout Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    CommRingCat.isPushout_iff_isPushout.mp po
  haveI : Algebra.Smooth Γ(M.S, U) Γ(G.left, W) :=
    HasRingHomProperty.appLE @AlgebraicGeometry.Smooth G.hom hG ⟨U, hU⟩ ⟨W, hW⟩ hWU
  let e := Algebra.IsPushout.equiv Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W)
  have hf' : IsIntegral Γ(G.left, W) f := hf
  have hx : IsIntegral Γ(G.left, W) (e.symm f) := hf'.map e.symm.toAlgHom
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := Γ(M.S, U)) (S := Γ(G.left, W))
    (B := Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U))).2 ⟨e.symm f, hx⟩
  have hfy : f = e ((TensorProduct.toIntegralClosure Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) y : _)) := by
    rw [congrArg Subtype.val hy]; exact (e.apply_symm_apply f).symm
  rw [hfy]
  clear hfy hy
  induction y with
  | tmul c b =>
    refine ⟨1, fun _ => c, fun _ => (b : Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)), fun _ => b.2, ?_⟩
    rw [Fin.sum_univ_one]
    exact Algebra.IsPushout.equiv_tmul _ _ _ _ c (b : Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U))
  | add u v hu hv =>
    rw [map_add (f := _), Subalgebra.coe_add, map_add (f := _)]
    exact sumForm_add _ _ _ hu hv

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralElementAffineSectionGeneratedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_element_affine_section_generated : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (W : G.left.Opens) (U : M.S.Opens) (hWU : W ≤ G.hom ⁻¹ᵁ U), IsAffineOpen W → IsAffineOpen U → ∀ f : Γ(Y, α ⁻¹ᵁ W), (α.app W).hom.IsIntegralElem f → ∃ (n : ℕ) (c : Fin n → Γ(G.left, W)) (b : Fin n → Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)), (∀ m, (M.gp.app U).hom.IsIntegralElem (b m)) ∧ f = ∑ m, (α.app W).hom (c m) * (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) (locInt_le_gen G.hom α t M.gp hpb.w W U hWU)).hom (b m) := by
  first | exact @GlobalTheory.Mum.eq_sum_of_isIntegral_genericChart | exact GlobalTheory.Mum.eq_sum_of_isIntegral_genericChart | (intros; apply GlobalTheory.Mum.eq_sum_of_isIntegral_genericChart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistedThetaValuePullbackBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistedThetaValuePullbackBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UPoinc.USum

theorem ptSecT_comp_whisker {B : Scheme.{0}} {A : Over B} [GrpObj A] {T T' : Over B} (c : T' ⟶ T) (y : T ⟶ A) :
    (ptSecT A (c ≫ y)).left ≫ (c ▷ A).left = c.left ≫ (ptSecT A y).left := by
  rw [← Over.comp_left, ← Over.comp_left, ptSecT, ptSecT, lift_whiskerRight, comp_lift, Category.id_comp,
    Category.comp_id]

theorem isTwVal_pull {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀))
    {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1)))
    (β : T ⟶ T₀) (x h : T ⟶ P.A) (v : Γ(T.left, ⊤)) {T' : Over B} (c : T' ⟶ T) :
    IsTwVal P N m θ τ β x h v → IsTwVal P N m θ τ (c ≫ β) (c ≫ x) (c ≫ h) (c.left.appTop.hom v) := by
  rintro ⟨α, U, hα, hU, H⟩
  obtain ⟨α', hα', vα⟩ := GlobalTheory.VVRank.exists_gen_pullTo
    (φ' := ![(snd T' P.A).left, (snd T' P.A ^ m).left]) α hα (c ▷ P.A).left (fun k => by
      fin_cases k
      · exact GlobalTheory.VVRank.whisker_snd_left P.A c
      · change (c ▷ P.A).left ≫ (snd T P.A ^ m).left = (snd T' P.A ^ m).left
        rw [← Over.comp_left, MonObj.comp_pow, whiskerRight_snd])
  obtain ⟨U', hU', vU⟩ := GlobalTheory.SymLiftGlobal.exists_symLift_pull_val P.isLB c hU
  refine ⟨α', U', hα', hU', fun Z r z J hJ => ?_⟩
  have eq₁ : (c ≫ x) * (c ≫ h) = c ≫ (x * h) := (MonObj.comp_mul _ _ _).symm
  have q := H Z (r ≫ c.left) z J hJ
  have g : gs r z ⊤ (c.left.appTop.hom v) = gs (r ≫ c.left) z ⊤ v := gs_pull r c.left z ⊤ trivial v
  have w : ∀ (y : T ⟶ P.A) {W : Scheme.{0}} (k : (T ⊗ P.A).left ⟶ W),
      (ptSecT P.A (c ≫ y)).left ≫ (c ▷ P.A).left ≫ k = c.left ≫ (ptSecT P.A y).left ≫ k := fun y W k => by
    rw [← Category.assoc, ptSecT_comp_whisker, Category.assoc]
  have eq₃ : (c ≫ (x * h)) ^ m = c ≫ (x * h) ^ m := (MonObj.comp_pow _ _ _).symm
  rw [g, vα _ _ z J hJ, vα _ _ z J hJ, vU _ _ z J hJ, eq₁, eq₃]
  simp only [Category.assoc, ptSecT_comp_whisker, comp_whiskerRight, Over.comp_left, w]
  simpa only [Category.assoc] using q

end GlobalTheory.UPoinc.USum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistedThetaValuePullbackBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTwistedThetaValue_pullback_base_change : ∀ {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀) (x h : T ⟶ P.A) (v : Γ(T.left, ⊤)) {T' : Over B} (c : T' ⟶ T), IsTwVal P N m θ τ β x h v → IsTwVal P N m θ τ (c ≫ β) (c ≫ x) (c ≫ h) (c.left.appTop.hom v) := by
  first | exact @GlobalTheory.UPoinc.USum.isTwVal_pull | exact GlobalTheory.UPoinc.USum.isTwVal_pull | (intros; apply GlobalTheory.UPoinc.USum.isTwVal_pull <;> assumption)
end
end

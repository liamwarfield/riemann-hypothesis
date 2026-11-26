module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.NeronOggShafarevich
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentNumberFieldEndomorphismsTateMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExponentInertiaTateModuleFiniteResidue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfNeronOggShafarevich

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleGaloisImagesCommuteOfComplexMultiplica
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemSpanOrbitOfNumberFieldLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLinearIndependentOfIsFractionRing
open scoped Matrix
open IntermediateField

namespace GlobalTheory

theorem exists_pow_linearIndependent_of_isFractionRing (O F : Type) [CommRing O] [Field F]
    [NumberField F] [Algebra O F] [IsFractionRing O F] :
    ∃ α : O, LinearIndependent ℚ (fun i : Fin (Module.finrank ℚ F) => algebraMap O F (α ^ (i : ℕ))) := by
  obtain ⟨γ, hγ⟩ := Field.exists_primitive_element ℚ F
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := O) γ
  have hfin : Finite (IntermediateField ℚ F) :=
    Field.finite_intermediateField_of_exists_primitive_element ℚ F ⟨γ, hγ⟩
  obtain ⟨t, t', htt, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun t : ℕ => ℚ⟮algebraMap O F x + (t : F) * algebraMap O F y⟯)
  have h1 : algebraMap O F x + (t : F) * algebraMap O F y ∈
      ℚ⟮algebraMap O F x + (t : F) * algebraMap O F y⟯ := mem_adjoin_simple_self _ _
  have h2 : algebraMap O F x + (t' : F) * algebraMap O F y ∈
      ℚ⟮algebraMap O F x + (t : F) * algebraMap O F y⟯ := by
    rw [he]; exact mem_adjoin_simple_self _ _
  set L := ℚ⟮algebraMap O F x + (t : F) * algebraMap O F y⟯ with hL
  have hyL : algebraMap O F y ∈ L := by
    have hd : ((t : F) - t') * algebraMap O F y ∈ L := by
      have := L.sub_mem h1 h2
      convert this using 1; ring
    have htt' : ((t : F) - t') ≠ 0 := sub_ne_zero.2 (by exact_mod_cast htt)
    have hc : ((t : F) - t') ∈ L := L.sub_mem (L.natCast_mem t) (L.natCast_mem t')
    have := L.mul_mem (L.inv_mem hc) hd
    rwa [← mul_assoc, inv_mul_cancel₀ htt', one_mul] at this
  have hxL : algebraMap O F x ∈ L := by
    have := L.sub_mem h1 (L.mul_mem (L.natCast_mem t) hyL)
    simpa using this
  have hγL : γ ∈ L := hxy ▸ L.div_mem hxL hyL
  have htop : L = ⊤ := by
    rw [eq_top_iff, ← hγ, adjoin_simple_le_iff]; exact hγL
  refine ⟨x + t • y, ?_⟩
  have ha : algebraMap O F (x + t • y) = algebraMap O F x + (t : F) * algebraMap O F y := by
    rw [map_add (f := _), map_nsmul, nsmul_eq_mul]
  have hint : IsIntegral ℚ (algebraMap O F (x + t • y)) := Algebra.IsIntegral.isIntegral _
  have hdeg : (minpoly ℚ (algebraMap O F (x + t • y))).natDegree = Module.finrank ℚ F := by
    rw [← adjoin.finrank hint, ha, ← hL, htop, finrank_top']
  have h' := (linearIndependent_pow (K := ℚ) (algebraMap O F (x + t • y))).comp
    (Fin.cast hdeg.symm) (Fin.cast_injective _)
  have hf : (fun i : Fin (Module.finrank ℚ F) => algebraMap O F ((x + t • y) ^ (i : ℕ))) =
      (fun i : Fin (minpoly ℚ (algebraMap O F (x + t • y))).natDegree =>
        algebraMap O F (x + t • y) ^ (i : ℕ)) ∘ Fin.cast hdeg.symm := by
    ext i; simp [map_pow]
  rw [hf]; exact h'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearIndependentIteratesOfLinearIndepende
open scoped Matrix
open Polynomial

namespace GlobalTheory.CyclicVector

theorem exists_linearIndependent_iterates_of_linearIndependent_pow {K : Type} [Field K] {r : ℕ}
    (g : Matrix (Fin r) (Fin r) K)
    (hg : LinearIndependent K (fun i : Fin r => g ^ (i : ℕ))) :
    ∃ v : Fin r → K, LinearIndependent K (fun i : Fin r => (g ^ (i : ℕ)) *ᵥ v) := by
  classical
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator K[X]
    (Module.AEval' (Matrix.toLin' g))
  set v := (Module.AEval'.of (Matrix.toLin' g)).symm x with hv
  refine ⟨v, ?_⟩
  rw [Fintype.linearIndependent_iff] at hg ⊢
  intro c hc
  let q : K[X] := ∑ j : Fin r, monomial (j : ℕ) (c j)
  have haq : aeval g q = ∑ j : Fin r, c j • g ^ (j : ℕ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [q, map_sum, aeval_monomial, Algebra.smul_def]
  have ha : ∀ p : K[X], aeval (Matrix.toLin' g) p = Matrix.toLin' (aeval g p) := fun p =>
    (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin r)) g p)
  have hqv : aeval g q *ᵥ v = 0 := by
    rw [haq, Matrix.sum_mulVec]
    have hs : ∀ j : Fin r, (c j • g ^ (j : ℕ)) *ᵥ v = c j • (g ^ (j : ℕ) *ᵥ v) := fun j => by
      ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    simpa [hs] using hc
  have hmem : q ∈ Module.annihilator K[X] (Module.AEval' (Matrix.toLin' g)) := by
    rw [← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    apply (Module.AEval'.of (Matrix.toLin' g)).symm.injective
    rw [Module.AEval.of_symm_smul, map_zero, ha]
    exact hqv
  have hq : aeval g q = 0 := by
    apply Matrix.toLin'.injective
    rw [map_zero, ← ha]
    refine LinearMap.ext fun u => ?_
    have := Module.mem_annihilator.1 hmem (Module.AEval'.of (Matrix.toLin' g) u)
    have h2 := congrArg (Module.AEval'.of (Matrix.toLin' g)).symm this
    rw [Module.AEval.of_symm_smul, map_zero] at h2
    simpa using h2
  exact hg c (haq ▸ hq)

end GlobalTheory.CyclicVector
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemSpanOrbitOfNumberFieldLattice
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open scoped Matrix

namespace GlobalTheory.CyclicLattice

theorem exists_linearIndependent_mulVec_pow {R : Type} [CommRing R] [IsDomain R] {r : ℕ}
    (g : Matrix (Fin r) (Fin r) R) (hg : LinearIndependent R (fun i : Fin r => g ^ (i : ℕ))) :
    ∃ v : Fin r → R, LinearIndependent R (fun i : Fin r => (g ^ (i : ℕ)) *ᵥ v) := by
  classical
  let K := FractionRing R
  let f := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  let gK := g.map f
  let Φ : Matrix (Fin r) (Fin r) R →ₗ[R] Matrix (Fin r) (Fin r) K :=
    (Algebra.linearMap R K).mapMatrix
  have hΦ : Function.Injective Φ := fun a a' h => by
    ext i j
    exact hf (congrFun (congrFun h i) j)
  have hgK : LinearIndependent K (fun i : Fin r => gK ^ (i : ℕ)) := by
    have h1 := hg.map' Φ (LinearMap.ker_eq_bot.2 hΦ)
    have h2 : (Φ ∘ fun i : Fin r => g ^ (i : ℕ)) = fun i : Fin r => gK ^ (i : ℕ) := by
      funext i
      simp only [Function.comp_apply, gK, ← Matrix.map_pow]
      rfl
    rw [h2] at h1
    exact (LinearIndependent.iff_fractionRing R K).mp h1
  obtain ⟨w, hw⟩ :=
    GlobalTheory.CyclicVector.exists_linearIndependent_iterates_of_linearIndependent_pow gK hgK
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) w
  choose u hu using hs
  refine ⟨u, ?_⟩
  let Ψ : (Fin r → R) →ₗ[R] (Fin r → K) :=
    LinearMap.pi (fun i => (Algebra.linearMap R K).comp (LinearMap.proj i))
  have hΨ : Function.Injective Ψ := fun a a' h => funext fun i => hf (congrFun h i)
  have hfu : (f ∘ u) = (f s) • w := funext fun j => by
    simpa [Algebra.smul_def] using hu j
  have key : (Ψ ∘ fun i : Fin r => g ^ (i : ℕ) *ᵥ u) =
      fun i : Fin r => (f s) • (gK ^ (i : ℕ) *ᵥ w) := by
    funext i
    ext k
    have e1 := RingHom.map_mulVec f (g ^ (i : ℕ)) u k
    simp only [Function.comp_apply]
    change f ((g ^ (i : ℕ) *ᵥ u) k) = _
    rw [e1, Matrix.map_pow, hfu, Matrix.mulVec_smul]
  have hsK : f s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have h3 : LinearIndependent K (fun i : Fin r => (f s) • (gK ^ (i : ℕ) *ᵥ w)) := by
    have := hw.units_smul (fun _ => Units.mk0 (f s) hsK)
    have e : (fun i : Fin r => (f s) • (gK ^ (i : ℕ) *ᵥ w)) =
        (fun _ : Fin r => Units.mk0 (f s) hsK) • (fun i : Fin r => gK ^ (i : ℕ) *ᵥ w) := by
      funext i
      simp [Units.smul_def]
    rw [e]
    exact this
  have h4 := (LinearIndependent.iff_fractionRing R K).mpr h3
  rw [← key] at h4
  exact h4.of_comp

theorem exists_smul_mem_span_of_linearIndependent {R M : Type} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] {r : ℕ} (b : Module.Basis (Fin r) R M) (w : Fin r → M)
    (hw : LinearIndependent R w) :
    ∃ c : R, c ≠ 0 ∧ ∀ t : M, c • t ∈ Submodule.span R (Set.range w) := by
  classical
  let N : Matrix (Fin r) (Fin r) R := b.toMatrix w
  have hsum : ∀ z : Fin r → R, b.equivFun (∑ j, z j • w j) = N *ᵥ z := by
    intro z
    ext i
    simp [N, Module.Basis.toMatrix_apply, Matrix.mulVec, dotProduct, mul_comm]
  have hdet : N.det ≠ 0 := by
    intro h0
    obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hz0
    have : ∑ j, z j • w j = 0 := b.equivFun.injective (by rw [hsum, hz, map_zero])
    funext j
    exact Fintype.linearIndependent_iff.1 hw z this j
  refine ⟨N.det, hdet, fun t => ?_⟩
  have : N.det • t = ∑ j, (N.adjugate *ᵥ b.equivFun t) j • w j := by
    apply b.equivFun.injective
    rw [hsum, map_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem exists_smul_mem_span_orbit : ∀ (l : ℕ) [Fact l.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (O F : Type) [CommRing O] [Field F] [NumberField F] [Algebra O F] [IsFractionRing O F] (ρ : O →+* Module.End ℤ_[l] T), Module.finrank ℤ_[l] T = Module.finrank ℚ F → (∀ (n : ℕ) (a : Fin n → O), LinearIndependent ℚ (fun i => algebraMap O F (a i)) → LinearIndependent ℤ_[l] (fun i => ρ (a i))) → ∃ (v : T) (c : ℤ_[l]), c ≠ 0 ∧ ∀ t : T, c • t ∈ Submodule.span ℤ_[l] (Set.range fun a => ρ a v) := by
  intro l _ T _ _ _ _ O F _ _ _ _ _ ρ hrank hind
  obtain ⟨α, hα⟩ := GlobalTheory.exists_pow_linearIndependent_of_isFractionRing O F
  set n := Module.finrank ℚ F with hn
  let b : Module.Basis (Fin n) ℤ_[l] T := Module.finBasisOfFinrankEq ℤ_[l] T hrank
  set φ := ρ α with hφdef
  set g := LinearMap.toMatrix b b φ with hgdef
  have hpow : ∀ i : ℕ, LinearMap.toMatrix b b (φ ^ i) = g ^ i := fun i => by
    induction i with
    | zero => simp [LinearMap.toMatrix_one]
    | succ k ih => rw [pow_succ, LinearMap.toMatrix_mul, ih, pow_succ]
  have hφ : LinearIndependent ℤ_[l] (fun i : Fin n => φ ^ (i : ℕ)) := by
    have := hind n (fun i => α ^ (i : ℕ)) hα
    simpa [φ, map_pow] using this
  have hg : LinearIndependent ℤ_[l] (fun i : Fin n => g ^ (i : ℕ)) := by
    have := hφ.map' (LinearMap.toMatrix b b).toLinearMap (LinearMap.toMatrix b b).ker
    simpa [Function.comp_def, hpow] using this
  obtain ⟨u, hu⟩ := exists_linearIndependent_mulVec_pow g hg
  set v : T := b.equivFun.symm u with hv
  have hw : ∀ i : ℕ, b.equivFun ((φ ^ i) v) = g ^ i *ᵥ u := by
    intro i
    have hu' : u = ⇑(b.repr v) := by
      rw [hv, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [← hpow, hu', LinearMap.toMatrix_mulVec_repr, Module.Basis.equivFun_apply]
  have hli : LinearIndependent ℤ_[l] (fun i : Fin n => (φ ^ (i : ℕ)) v) := by
    have hfun : (fun i : Fin n => (φ ^ (i : ℕ)) v) =
        b.equivFun.symm.toLinearMap ∘ (fun i : Fin n => g ^ (i : ℕ) *ᵥ u) := by
      funext i
      apply b.equivFun.injective
      simp only [Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hw]
    rw [hfun]
    exact hu.map' _ b.equivFun.symm.ker
  obtain ⟨c, hc, hct⟩ := exists_smul_mem_span_of_linearIndependent b _ hli
  refine ⟨v, c, hc, fun t => Submodule.span_mono ?_ (hct t)⟩
  rintro _ ⟨i, rfl⟩
  exact ⟨α ^ (i : ℕ), by simp [φ, map_pow]⟩

end GlobalTheory.CyclicLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemSpanOrbitOfNumberFieldLatticeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_mem_span_orbit_of_numberField_lattice : ∀ (l : ℕ) [Fact l.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (O F : Type) [CommRing O] [Field F] [NumberField F] [Algebra O F] [IsFractionRing O F] (ρ : O →+* Module.End ℤ_[l] T), Module.finrank ℤ_[l] T = Module.finrank ℚ F → (∀ (n : ℕ) (a : Fin n → O), LinearIndependent ℚ (fun i => algebraMap O F (a i)) → LinearIndependent ℤ_[l] (fun i => ρ (a i))) → ∃ (v : T) (c : ℤ_[l]), c ≠ 0 ∧ ∀ t : T, c • t ∈ Submodule.span ℤ_[l] (Set.range fun a => ρ a v) := by
  first | exact @GlobalTheory.CyclicLattice.exists_smul_mem_span_orbit | exact GlobalTheory.CyclicLattice.exists_smul_mem_span_orbit | (intros; apply GlobalTheory.CyclicLattice.exists_smul_mem_span_orbit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleGaloisImagesCommuteOfComplexMultiplica
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CMComm

theorem commute_of_cyclic {l : ℕ} [Fact l.Prime] {T : Type} [AddCommGroup T] [Module ℤ_[l] T]
    [Module.IsTorsionFree ℤ_[l] T] {O : Type} [CommRing O] (ρ : O →+* Module.End ℤ_[l] T) (v : T) (c : ℤ_[l])
    (hc : c ≠ 0) (hv : ∀ t : T, c • t ∈ Submodule.span ℤ_[l] (Set.range fun a => ρ a v))
    (g h : Module.End ℤ_[l] T) (hg : ∀ a, g * ρ a = ρ a * g) (hh : ∀ a, h * ρ a = ρ a * h) :
    g * h = h * g := by
  set P := Submodule.span ℤ_[l] (Set.range ρ) with hP
  have hcen : ∀ k : Module.End ℤ_[l] T, (∀ a, k * ρ a = ρ a * k) → ∀ x ∈ P, k * x = x * k := by
    intro k hk x hx
    have : P ≤ Subalgebra.toSubmodule (Subalgebra.centralizer ℤ_[l] {k}) := by
      rw [hP, Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      exact hk a
    have h1 := this hx
    rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff] at h1
    exact h1 k rfl
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have hx' : ∀ a, x * ρ a = ρ a * x := fun a => by
      have := hcen (ρ a) (fun b => by rw [← map_mul, ← map_mul, mul_comm]) x hx
      exact this.symm
    exact hcen x hx' y hy
  have hev : ∀ w : T, ∃ x ∈ P, x v = c • w := by
    intro w
    have := hv w
    rw [show (Set.range fun a => ρ a v) = (LinearMap.applyₗ v : Module.End ℤ_[l] T →ₗ[ℤ_[l]] T) '' Set.range ρ by
      rw [← Set.range_comp]; rfl, Submodule.span_image] at this
    obtain ⟨x, hx, e⟩ := this
    exact ⟨x, hx, e⟩
  refine LinearMap.ext fun t => ?_
  obtain ⟨x, hx, ex⟩ := hev t
  obtain ⟨y, hy, ey⟩ := hev (g v)
  obtain ⟨z, hz, ez⟩ := hev (h v)
  have hgx := hcen g hg x hx
  have hhx := hcen h hh x hx
  have k1 : c • c • c • (g * h) t = x (z (y v)) := by
    have e1 : c • (g * h) t = x (g (h v)) := by
      rw [← map_smul, ← ex, Module.End.mul_apply]
      change (g * (h * x)) v = x (g (h v))
      rw [hhx, ← _root_.mul_assoc, hgx, _root_.mul_assoc]; rfl
    have e2 : c • x (g (h v)) = x (z (g v)) := by
      rw [← map_smul, ← map_smul, ← ez]
      change x ((g * z) v) = x ((z * g) v)
      rw [hcen g hg z hz]
    rw [e1, e2, ← map_smul, ← map_smul, ← ey]
  have k2 : c • c • c • (h * g) t = x (y (z v)) := by
    have e1 : c • (h * g) t = x (h (g v)) := by
      rw [← map_smul, ← ex, Module.End.mul_apply]
      change (h * (g * x)) v = x (h (g v))
      rw [hgx, ← _root_.mul_assoc, hhx, _root_.mul_assoc]; rfl
    have e2 : c • x (h (g v)) = x (y (h v)) := by
      rw [← map_smul, ← map_smul, ← ey]
      change x ((h * y) v) = x ((y * h) v)
      rw [hcen h hh y hy]
    rw [e1, e2, ← map_smul, ← map_smul, ← ez]
  have k3 : x (z (y v)) = x (y (z v)) := by
    change (x * (z * y)) v = (x * (y * z)) v
    rw [hcomm z hz y hy]
  have k4 : (c * c * c) • (g * h) t = (c * c * c) • (h * g) t := by
    rw [mul_smul, mul_smul, k1, k3, ← k2, mul_smul, mul_smul]
  exact smul_right_injective T (mul_ne_zero (mul_ne_zero hc hc) hc) k4

theorem galTate_comm_actTate {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A]
    [IsCommMonObj A] {O : Type} [CommRing O] (α : OAct O A) (l : ℕ) [Fact l.Prime] (σ : Ω ≃ₐ[K] Ω) (a : O) :
    galTate A l σ * actTate α.toRingAct l (ptOver K Ω) a = actTate α.toRingAct l (ptOver K Ω) a * galTate A l σ :=
  LinearMap.ext fun t => Tate.ext fun n => by
    change specAut σ ≫ (t.lev n ≫ α.act a) = (specAut σ ≫ t.lev n) ≫ α.act a
    rw [Category.assoc]

theorem galTate_commute_of_hasCMBy : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F], HasCMBy A F → ∀ (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ := by
  intro K Ω _ _ _ _ A _ _ hA F _ _ hF l _ hl σ τ
  obtain ⟨⟨d, hd, hdeg⟩, O, _, _, _, ⟨α⟩⟩ := hF
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hcard : ∀ n : ℕ, Nat.card {x : ptOver K Ω ⟶ A // x ^ (l ^ n) = 1} = l ^ (2 * d * n) := fun n => by
    rw [GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K Ω A hA d hd (l ^ n) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl), ← pow_mul, mul_comm n]
  obtain ⟨hfree, hfin, hrank⟩ := GlobalTheory.TateFree.free_finite_finrank (ptOver K Ω ⟶ A) l (2 * d) hcard
  haveI := hfree
  haveI := hfin
  obtain ⟨v, c, hc, hv⟩ := GlobalTheory.T.exists_smul_mem_span_orbit_of_numberField_lattice l (Tate l (ptOver K Ω ⟶ A)) O F (actTate α.toRingAct l (ptOver K Ω))
    (hrank.trans hdeg.symm) (GlobalTheory.T.linearIndependent_numberFieldEndomorphisms_tateModule K Ω A hA
      ⟨d, by have := Module.finrank_pos (R := ℚ) (M := F); omega, hd⟩ F O α l hl)
  exact commute_of_cyclic _ v c hc hv _ _ (galTate_comm_actTate A α l σ) (galTate_comm_actTate A α l τ)

end GlobalTheory.CMComm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleGaloisImagesCommuteOfComplexMultiplicaStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateModule_galoisImages_commute_of_complexMultiplication : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F], HasCMBy A F → ∀ (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ := by
  first | exact @GlobalTheory.CMComm.galTate_commute_of_hasCMBy | exact GlobalTheory.CMComm.galTate_commute_of_hasCMBy | (intros; apply GlobalTheory.CMComm.galTate_commute_of_hasCMBy <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteImageTateModuleOfBoundedExponentComm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderOfTrivialModSqTateModule
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderOfTrivialModSqTateModule
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.MinkowskiTate

section Lemmas

variable {l : ℕ} {M : Type} [CommGroup M]

theorem lev_nsmul (t : Tate l M) (n m : ℕ) : (n • t).lev m = t.lev m ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero]; rfl
  | succ n ih => rw [succ_nsmul, Tate.lev_add, ih, pow_succ]

theorem lev_neg (t : Tate l M) (m : ℕ) : (-t).lev m = (t.lev m)⁻¹ := rfl

theorem lev_sub (s t : Tate l M) (m : ℕ) : (s - t).lev m = s.lev m * (t.lev m)⁻¹ := by
  rw [sub_eq_add_neg, Tate.lev_add, lev_neg]

def Dv (k : ℕ) (t : Tate l M) : Prop := ∃ s : Tate l M, t = (l ^ k) • s

theorem dv_zero (k : ℕ) : Dv k (0 : Tate l M) := ⟨0, (smul_zero _).symm⟩

theorem dv_add {k : ℕ} {s t : Tate l M} (hs : Dv k s) (ht : Dv k t) : Dv k (s + t) := by
  obtain ⟨a, rfl⟩ := hs
  obtain ⟨b, rfl⟩ := ht
  exact ⟨a + b, (smul_add _ _ _).symm⟩

theorem dv_neg {k : ℕ} {t : Tate l M} (ht : Dv k t) : Dv k (-t) := by
  obtain ⟨a, rfl⟩ := ht
  exact ⟨-a, (smul_neg _ _).symm⟩

theorem dv_nsmul {k : ℕ} (n : ℕ) {t : Tate l M} (ht : Dv k t) : Dv k (n • t) := by
  obtain ⟨a, rfl⟩ := ht
  exact ⟨n • a, smul_comm _ _ _⟩

theorem dv_sum {k : ℕ} {Ix : Type} (s : Finset Ix) (f : Ix → Tate l M) (h : ∀ i ∈ s, Dv k (f i)) :
    Dv k (∑ i ∈ s, f i) :=
  Finset.sum_induction f (Dv k) (fun _ _ => dv_add) (dv_zero k) h

theorem dv_mono {k k' : ℕ} (hk : k ≤ k') {t : Tate l M} (ht : Dv k' t) : Dv k t := by
  obtain ⟨a, rfl⟩ := ht
  refine ⟨l ^ (k' - k) • a, ?_⟩
  rw [smul_smul, ← pow_add, Nat.add_sub_cancel' hk]

theorem eq_zero_of_nsmul {t : Tate l M} (h : l • t = 0) : t = 0 := by
  refine Tate.ext fun m => ?_
  show t.lev m = 1
  calc t.lev m = t.lev (m + 1) ^ l := (Tate.lev_succ t m).symm
    _ = (l • t).lev (m + 1) := (lev_nsmul t l (m + 1)).symm
    _ = 1 := by rw [h]; rfl

theorem eq_zero_of_pow_nsmul (a : ℕ) {z : Tate l M} (h : (l ^ a) • z = 0) : z = 0 := by
  induction a generalizing z with
  | zero => simpa using h
  | succ a ih => exact eq_zero_of_nsmul (ih (by rw [smul_smul, ← pow_succ]; exact h))

theorem pow_nsmul_cancel (a : ℕ) {x y : Tate l M} (h : (l ^ a) • x = (l ^ a) • y) : x = y :=
  sub_eq_zero.1 (eq_zero_of_pow_nsmul a (by rw [smul_sub, h, sub_self]))

theorem dv_of_pow_nsmul {a b : ℕ} {s : Tate l M} (h : Dv (a + b) ((l ^ a) • s)) : Dv b s := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, pow_nsmul_cancel a (by rw [hr, pow_add, smul_smul])⟩

theorem dv_one_of_nsmul {q : ℕ} (hq : Nat.Coprime q l) {s : Tate l M} (h : Dv 1 (q • s)) :
    Dv 1 s := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hq
  refine ⟨a • r + b • s, ?_⟩
  calc s = (a * (q : ℤ) + b * (l : ℤ)) • s := by rw [hab, one_smul]
    _ = a • ((q : ℤ) • s) + b • ((l : ℤ) • s) := by rw [add_smul, mul_smul, mul_smul]
    _ = l ^ 1 • (a • r + b • s) := by
      rw [natCast_zsmul, natCast_zsmul, hr, pow_one, smul_add, smul_comm a l r, smul_comm b l s]

theorem eq_zero_of_dv {t : Tate l M} (h : ∀ k, Dv k t) : t = 0 := by
  refine Tate.ext fun k => ?_
  show t.lev k = 1
  obtain ⟨s, hs⟩ := h k
  rw [hs, lev_nsmul, Tate.lev_pow]

theorem dv_two_of_lev {w : Tate l M} (h : w.lev 2 = 1) : Dv 2 w := by
  refine ⟨Tate.mk (fun n => w.lev (n + 2)) fun n => ⟨?_, ?_⟩, ?_⟩
  · rw [add_comm, Tate.lev_add_pow, h]
  · exact Tate.lev_succ w (n + 2)
  · refine Tate.ext fun n => ?_
    rw [lev_nsmul, Tate.lev_mk, Tate.lev_add_pow]

end Lemmas

end GlobalTheory.MinkowskiTate

namespace GlobalTheory.MinkowskiTate

section Endo

variable {l : ℕ} [Fact l.Prime] {M : Type} [CommGroup M]

theorem dv_pow_sub (k : ℕ) {u : Module.End ℤ_[l] (Tate l M)} (h : ∀ t, Dv k (u t - t)) (n : ℕ) :
    ∀ t, Dv k ((u ^ n) t - t) := by
  induction n with
  | zero => intro t; rw [pow_zero, Module.End.one_apply, sub_self]; exact dv_zero k
  | succ n ih =>
    intro t
    rw [pow_succ', Module.End.mul_apply]
    have e : u ((u ^ n) t) - t = (u ((u ^ n) t) - (u ^ n) t) + ((u ^ n) t - t) := by abel
    rw [e]
    exact dv_add (h _) (ih t)

theorem dv_succ_of_pow_eq_one {q : ℕ} (hq : q.Prime) {v : Module.End ℤ_[l] (Tate l M)}
    (hv : v ^ q = 1) {k : ℕ} (hk : 2 ≤ k) (h : ∀ t, Dv k (v t - t)) (t : Tate l M) :
    Dv (k + 1) (v t - t) := by
  set D := v - 1 with hD
  have hDt : ∀ t, D t = v t - t := fun t => by
    rw [hD, LinearMap.sub_apply, Module.End.one_apply]
  have hmap : ∀ a t, Dv a t → Dv (a + k) (D t) := by
    rintro a _ ⟨s, rfl⟩
    obtain ⟨r, hr⟩ := h s
    refine ⟨r, ?_⟩
    rw [map_nsmul, hDt, hr, pow_add, smul_smul]
  have hpow : ∀ j t, Dv (j * k) ((D ^ j) t) := by
    intro j
    induction j with
    | zero => intro t; exact ⟨t, by rw [pow_zero, Module.End.one_apply, zero_mul, pow_zero, one_smul]⟩
    | succ j ih =>
      intro t
      rw [pow_succ', Module.End.mul_apply, Nat.succ_mul]
      exact hmap _ _ (ih t)
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 + 1 := ⟨q - 2, by have := hq.two_le; omega⟩
  have hvD : v = D + 1 := by rw [hD, sub_add_cancel]
  have key := congrArg (fun f : Module.End ℤ_[l] (Tate l M) => f t) hv
  rw [hvD, (Commute.one_right D).add_pow, Finset.sum_range_succ', Finset.sum_range_succ'] at key
  simp only [LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply,
    one_pow, _root_.mul_one, Module.End.natCast_apply, map_nsmul, pow_zero, Nat.choose_zero_right,
    Nat.choose_one_right, pow_one, Module.End.one_apply, one_smul, zero_add, Nat.cast_one] at key
  have hS : Dv (k + 2) (∑ x ∈ Finset.range (r + 1),
      (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) :=
    dv_sum _ _ fun x _ => dv_nsmul _ (dv_mono (by nlinarith) (hpow (x + 1 + 1) t))
  have hqD : (r + 1 + 1) • D t = -(∑ x ∈ Finset.range (r + 1),
      (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) := by
    calc (r + 1 + 1) • D t = ((∑ x ∈ Finset.range (r + 1),
          (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) + (r + 1 + 1) • D t + t) - t -
          (∑ x ∈ Finset.range (r + 1), (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) := by
          abel
      _ = t - t - (∑ x ∈ Finset.range (r + 1),
          (r + 1 + 1).choose (x + 1 + 1) • (D ^ (x + 1 + 1)) t) := by rw [key]
      _ = _ := by abel
  have hq2 : Dv (k + 2) ((r + 1 + 1) • D t) := hqD ▸ dv_neg hS
  obtain ⟨s, hs⟩ := h t
  rw [hDt, hs, smul_comm (r + 1 + 1) (l ^ k) s] at hq2
  have h2 : Dv 2 ((r + 1 + 1) • s) := dv_of_pow_nsmul hq2
  have h1 : Dv 1 s := by
    by_cases hql : r + 1 + 1 = l
    · rw [hql] at h2
      exact dv_of_pow_nsmul (a := 1) (b := 1) (by rw [pow_one]; exact h2)
    · exact dv_one_of_nsmul ((Nat.coprime_primes hq Fact.out).2 hql) (dv_mono (by norm_num) h2)
  obtain ⟨r', hr'⟩ := h1
  exact ⟨r', by rw [hs, hr', pow_one, smul_smul, ← pow_succ]⟩

theorem eq_one_of_prime {q : ℕ} (hq : q.Prime) {v : Module.End ℤ_[l] (Tate l M)} (hv : v ^ q = 1)
    (h : ∀ t, Dv 2 (v t - t)) : v = 1 := by
  have hall : ∀ k, 2 ≤ k → ∀ t, Dv k (v t - t) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact h
    | succ k hk ih => exact dv_succ_of_pow_eq_one hq hv hk ih
  refine LinearMap.ext fun t => ?_
  have h0 : v t - t = 0 :=
    eq_zero_of_dv fun k => dv_mono (le_max_left k 2) (hall _ (le_max_right k 2) t)
  rw [Module.End.one_apply]
  exact sub_eq_zero.1 h0

end Endo

end GlobalTheory.MinkowskiTate

theorem GlobalTheory.HTLat.Tate.eq_one_of_pow_eq_one_of_lev_two : ∀ (l : ℕ) [Fact l.Prime] (M : Type)
    [CommGroup M] (u : Module.End ℤ_[l] (Tate l M)) (E : ℕ), 0 < E → u ^ E = 1 →
    (∀ t, (u t).lev 2 = t.lev 2) → u = 1 := by
  intro l _ M _ u E hE hu h2
  have h : ∀ t, GlobalTheory.MinkowskiTate.Dv 2 (u t - t) := fun t =>
    GlobalTheory.MinkowskiTate.dv_two_of_lev (by rw [GlobalTheory.MinkowskiTate.lev_sub, h2, mul_inv_cancel])
  induction E using Nat.strong_induction_on with
  | _ E ih =>
    rcases Nat.lt_or_ge E 2 with hlt | hge
    · obtain rfl : E = 1 := by omega
      rwa [pow_one] at hu
    · have hq : E.minFac.Prime := Nat.minFac_prime (by omega)
      obtain ⟨E₁, hE₁⟩ := Nat.minFac_dvd E
      have hpos : 0 < E₁ := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hE₁; omega
      have hlt : E₁ < E := by
        have := hq.two_le
        rw [hE₁]
        nlinarith
      have hv : (u ^ E₁) ^ E.minFac = 1 := by rw [← pow_mul, mul_comm, ← hE₁, hu]
      exact ih E₁ hlt hpos (GlobalTheory.MinkowskiTate.eq_one_of_prime hq hv
        (GlobalTheory.MinkowskiTate.dv_pow_sub 2 h E₁))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderOfTrivialModSqTateModuleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_finite_order_of_trivial_mod_sq_tateModule : ∀ (l : ℕ) [Fact l.Prime] (M : Type) [CommGroup M] (u : Module.End ℤ_[l] (Tate l M)) (E : ℕ), 0 < E → u ^ E = 1 → (∀ t, (u t).lev 2 = t.lev 2) → u = 1 := by
  first | exact @GlobalTheory.HTLat.Tate.eq_one_of_pow_eq_one_of_lev_two | exact GlobalTheory.HTLat.Tate.eq_one_of_pow_eq_one_of_lev_two | (intros; apply GlobalTheory.HTLat.Tate.eq_one_of_pow_eq_one_of_lev_two <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteImageTateModuleOfBoundedExponentComm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Proof.FiniteInertiaImage

theorem galTate_eq_of_agree {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A]
    [IsCommMonObj A] (l : ℕ) [Fact l.Prime] (I : Subgroup (Ω ≃ₐ[K] Ω)) (E : ℕ) (hE0 : 0 < E)
    (hE : ∀ σ ∈ I, galTate A l σ ^ E = 1) {σ τ : Ω ≃ₐ[K] Ω} (hσ : σ ∈ I) (hτ : τ ∈ I)
    (h : ∀ x : ptOver K Ω ⟶ A, x ^ (l ^ 2) = 1 → galPts A σ x = galPts A τ x) :
    galTate A l σ = galTate A l τ := by
  have hu : galTate A l (σ * τ⁻¹) = 1 := by
    refine GlobalTheory.T.eq_one_of_finite_order_of_trivial_mod_sq_tateModule l (ptOver K Ω ⟶ A) _ E hE0 (hE _ (I.mul_mem hσ (I.inv_mem hτ))) fun t => ?_
    rw [lev_galTate]
    have hy : galPts A τ⁻¹ (t.lev 2) ^ (l ^ 2) = 1 := by rw [← map_pow, t.lev_pow, map_one]
    have e1 : galPts A (σ * τ⁻¹) (t.lev 2) = galPts A σ (galPts A τ⁻¹ (t.lev 2)) := by
      change specAut (σ * τ⁻¹) ≫ t.lev 2 = specAut σ ≫ specAut τ⁻¹ ≫ t.lev 2
      rw [specAut_mul, Category.assoc]
    have e2 : galPts A τ (galPts A τ⁻¹ (t.lev 2)) = t.lev 2 := by
      change specAut τ ≫ specAut τ⁻¹ ≫ t.lev 2 = t.lev 2
      rw [← Category.assoc, ← specAut_mul, mul_inv_cancel, specAut_one, Category.id_comp]
    rw [e1, h _ hy, e2]
  calc galTate A l σ = galTate A l (σ * τ⁻¹ * τ) := by rw [inv_mul_cancel_right]
    _ = galTate A l τ := by rw [map_mul, hu, _root_.one_mul]

theorem finite_image_galTate : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A]
    [IsCommMonObj A] (l : ℕ) [Fact l.Prime] (I : Subgroup (Ω ≃ₐ[K] Ω)),
    Finite {x : ptOver K Ω ⟶ A // x ^ (l ^ 2) = 1} →
    (∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ) →
    (∃ E : ℕ, 0 < E ∧ ∀ σ ∈ I, galTate A l σ ^ E = 1) →
    (galTate A l '' (I : Set (Ω ≃ₐ[K] Ω))).Finite := by
  intro K Ω _ _ _ A _ _ l _ I hS _ ⟨E, hE0, hE⟩
  let S := {x : ptOver K Ω ⟶ A // x ^ (l ^ 2) = 1}
  have hmap : ∀ (σ : Ω ≃ₐ[K] Ω) (x : S), galPts A σ x.1 ^ (l ^ 2) = 1 := fun σ x => by
    rw [← map_pow, x.2, map_one]
  let g : (Ω ≃ₐ[K] Ω) → S → S := fun σ x => ⟨galPts A σ x.1, hmap σ x⟩
  let F : galTate A l '' (I : Set (Ω ≃ₐ[K] Ω)) → S → S := fun u => g u.2.choose
  have hF : Function.Injective F := by
    rintro ⟨u, hu⟩ ⟨u', hu'⟩ e
    have h1 := hu.choose_spec
    have h2 := hu'.choose_spec
    refine Subtype.ext ?_
    change u = u'
    rw [← h1.2, ← h2.2]
    refine galTate_eq_of_agree A l I E hE0 hE h1.1 h2.1 fun x hx => ?_
    have := congrFun e ⟨x, hx⟩
    exact congrArg Subtype.val this
  exact Set.finite_coe_iff.1 (Finite.of_injective F hF)

end GlobalTheory.Proof.FiniteInertiaImage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteImageTateModuleOfBoundedExponentCommStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_image_tateModule_of_bounded_exponent_comm : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (l : ℕ) [Fact l.Prime] (I : Subgroup (Ω ≃ₐ[K] Ω)), Finite {x : ptOver K Ω ⟶ A // x ^ (l ^ 2) = 1} → (∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ) → (∃ E : ℕ, 0 < E ∧ ∀ σ ∈ I, galTate A l σ ^ E = 1) → (galTate A l '' (I : Set (Ω ≃ₐ[K] Ω))).Finite := by
  first | exact @GlobalTheory.Proof.FiniteInertiaImage.finite_image_galTate | exact GlobalTheory.Proof.FiniteInertiaImage.finite_image_galTate | (intros; apply GlobalTheory.Proof.FiniteInertiaImage.finite_image_galTate <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.CMGood
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Lit

theorem cmPotentialGoodReduction_of_nos (hN : GlobalTheory.Published.NeronOggShafarevichSt) :
    GlobalTheory.Published.CMPotentialGoodReductionSt := by
  intro R K _ _ _ _ _ _ _ A _ hA F _ _ hF
  have : IsCommMonObj A := hA.comm
  obtain ⟨V, hV⟩ := exists_isAbove R K (SeparableClosure K)
  obtain ⟨l, hl, hlk⟩ := GlobalTheory.Proof.exists_prime_natCast_ne_zero (ResidueField R)
  have hlK : (l : K) ≠ 0 := by
    intro h
    apply hlk
    have h1 : (l : R) = 0 := IsFractionRing.injective R K (by rw [map_natCast, map_zero, h])
    rw [← map_natCast (residue R), h1, map_zero]
  have hc := GlobalTheory.T.tateModule_galoisImages_commute_of_complexMultiplication K (SeparableClosure K) A hA F hF l hlK
  have he := GlobalTheory.T.exists_exponent_inertia_tateModule_finite_residue R K (SeparableClosure K) V hV A hA l hlk hc
  obtain ⟨⟨d, hd, -⟩, -⟩ := hF
  have hcard := GlobalTheory.T.card_abelianVariety_torsion_sepClosed K (SeparableClosure K) A hA d hd (l ^ 2)
    (by rw [Nat.cast_pow]; exact pow_ne_zero _ hlK)
  have hfin : Finite {x : ptOver K (SeparableClosure K) ⟶ A // x ^ (l ^ 2) = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (pow_ne_zero _ hl.out.ne_zero))
  exact (GlobalTheory.potentialGoodReduction_of_neronOggShafarevich hN R K (SeparableClosure K) V hV A hA l hlk).2
    (GlobalTheory.T.finite_image_tateModule_of_bounded_exponent_comm K (SeparableClosure K) A l _ hfin hc he)

end UpperTheory.Lit
end

namespace UpperTheory.Lit

theorem neronOggShafarevich : GlobalTheory.Published.NeronOggShafarevichSt := UpperTheory.Lit.Nos.Nos.neronOggShafarevich

theorem potentialGoodReduction : GlobalTheory.Published.PotentialGoodReductionSt :=
  GlobalTheory.potentialGoodReduction_of_neronOggShafarevich neronOggShafarevich

theorem cmPotentialGoodReduction : GlobalTheory.Published.CMPotentialGoodReductionSt :=
  cmPotentialGoodReduction_of_nos neronOggShafarevich

theorem serreTateGoodReduction : GlobalTheory.Published.SerreTateGoodReductionSt :=
  ⟨neronOggShafarevich, potentialGoodReduction, cmPotentialGoodReduction⟩

end UpperTheory.Lit

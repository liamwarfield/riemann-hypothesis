module

public import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideEdge
public import Formalism.LocalToGlobal.GroupLattices.FockModels.DualInclusionLattices

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideLat
section -- merged from Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideTen
section -- merged from Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideDef
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

def nabO (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (ν : Fin (m + 1) → ℕ) :
    Submodule O (MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :=
  Submodule.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap (dualWeyl O (m + 1) (m + 1) ν)

def expN (p m : ℕ) (lam : Fin (m + 1) → ℤ) : ℕ :=
  if ellWt lam = 0 then 0 else N0 (m + 1) * deF p (m + 1) (ellWt lam)

def FormCore : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
    ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam →
    ∃ B : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] Kf,
      (∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf),
        B (rowAct Kf g P) Q = B P (rowAct Kf g.transpose Q)) ∧
      (∀ Q ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam),
        (∀ P ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam), B P Q = 0) → Q = 0) ∧
      (∀ Q ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam),
        (∀ P ∈ nabO O Kf m (nuOf lam), B P Q ∈ Set.range (algebraMap O Kf)) → Q ∈ nabO O Kf m (nuOf lam)) ∧
      (∀ Q ∈ nabO O Kf m (nuOf lam), ∀ P ∈ nabO O Kf m (nuOf lam),
        B P (((p : Kf) ^ expN p m lam) • Q) ∈ Set.range (algebraMap O Kf))

end Formalism.L2.G.Model
end
end

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

section Ten

variable {Kf : Type} [Field Kf] {S : Type} [Fintype S] [DecidableEq S] {k n : ℕ}

theorem prodBasis (V : S → Submodule Kf (MvPolynomial (Fin k × Fin n) Kf)) {I : S → Type}
    (b : ∀ s, Module.Basis (I s) Kf (V s)) :
    ∃ x : Module.Basis (∀ s, I s) Kf (tensorLat Kf Kf V),
      ∀ i, ((x i : tensorLat Kf Kf V) : MvPolynomial (S × (Fin k × Fin n)) Kf) =
        ∏ s, blockEmb Kf s ((b s (i s) : V s) : MvPolynomial (Fin k × Fin n) Kf) := by
  have hKK : IsFractionRing Kf Kf := jr_KK Kf
  have hLI : ∀ s, LinearIndependent Kf (fun i => ((b s i : V s) : MvPolynomial (Fin k × Fin n) Kf)) :=
    fun s => (b s).linearIndependent.map' (V s).subtype (Submodule.ker_subtype _)
  have hsp : ∀ s, Submodule.span Kf
      (Set.range fun i => ((b s i : V s) : MvPolynomial (Fin k × Fin n) Kf)) = V s := by
    intro s
    have : (Set.range fun i => ((b s i : V s) : MvPolynomial (Fin k × Fin n) Kf)) =
        (V s).subtype '' Set.range (b s) := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, (b s).span_eq, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨kL, kS⟩ := tensorBasis Kf Kf S k n I V _ hLI hsp
  refine ⟨(Module.Basis.span kL).map (LinearEquiv.ofEq _ _ kS), fun i => ?_⟩
  show (((LinearEquiv.ofEq _ _ kS) (Module.Basis.span kL i) : tensorLat Kf Kf V) :
    MvPolynomial (S × (Fin k × Fin n)) Kf) = _
  rw [LinearEquiv.coe_ofEq_apply]
  exact congrArg Subtype.val (Module.Basis.span_apply kL i)

theorem repr_prod (V : S → Submodule Kf (MvPolynomial (Fin k × Fin n) Kf)) {I : S → Type} [∀ s, Fintype (I s)]
    (b : ∀ s, Module.Basis (I s) Kf (V s)) (x : Module.Basis (∀ s, I s) Kf (tensorLat Kf Kf V))
    (hx : ∀ i, ((x i : tensorLat Kf Kf V) : MvPolynomial (S × (Fin k × Fin n)) Kf) =
        ∏ s, blockEmb Kf s ((b s (i s) : V s) : MvPolynomial (Fin k × Fin n) Kf))
    (F : ∀ s, V s) (T : tensorLat Kf Kf V)
    (hT : (T : MvPolynomial (S × (Fin k × Fin n)) Kf) =
      ∏ s, blockEmb Kf s ((F s : V s) : MvPolynomial (Fin k × Fin n) Kf)) (i : ∀ s, I s) :
    x.repr T i = ∏ s, (b s).repr (F s) (i s) := by
  classical
  set c : (∀ s, I s) → Kf := fun p => ∏ s, (b s).repr (F s) (p s) with hc
  have hT' : T = ∑ p, c p • x p := by
    apply Subtype.ext
    rw [hT, Submodule.coe_sum]
    simp only [Submodule.coe_smul, hx]
    have hF : ∀ s, ((F s : V s) : MvPolynomial (Fin k × Fin n) Kf) =
        ∑ j, (b s).repr (F s) j • ((b s j : V s) : MvPolynomial (Fin k × Fin n) Kf) := by
      intro s
      conv_lhs => rw [← (b s).sum_repr (F s)]
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hF, map_sum, map_smul]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr (by simp) fun p _ => ?_
    simp only [hc, MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]
  rw [hT']
  first
  | rw [Module.Basis.repr_sum_self]
  | simp [map_sum, Finsupp.single_apply, hc]

end Ten

section Dual

variable {Kf : Type} [Field Kf]

def dualB {V : Type} [AddCommGroup V] [Module Kf V] {I : Type} [Fintype I] [DecidableEq I]
    (β : V ≃ₗ[Kf] Module.Dual Kf V) (Z : Module.Basis I Kf V) : Module.Basis I Kf V :=
  Z.dualBasis.map β.symm

theorem beta_dualB {V : Type} [AddCommGroup V] [Module Kf V] {I : Type} [Fintype I] [DecidableEq I]
    (β : V ≃ₗ[Kf] Module.Dual Kf V) (Z : Module.Basis I Kf V) (j : I) : β (dualB β Z j) = Z.coord j := by
  unfold dualB
  rw [Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
  ext x
  simp [Module.Basis.dualBasis_apply]

theorem dualB_repr {V : Type} [AddCommGroup V] [Module Kf V] {I : Type} [Fintype I] [DecidableEq I]
    (β : V ≃ₗ[Kf] Module.Dual Kf V) (b : Module.Basis I Kf V) (Q : V) (a : I) :
    (dualB β b).repr Q a = β Q (b a) := by
  unfold dualB
  simp [Module.Basis.map_repr, Module.Basis.dualBasis_repr]

end Dual

section Psi

variable {Kf : Type} [Field Kf] {S : Type} [Fintype S] [DecidableEq S] {k n : ℕ}

theorem psi_exists (V : S → Submodule Kf (MvPolynomial (Fin k × Fin n) Kf))
    (β : ∀ s, V s ≃ₗ[Kf] Module.Dual Kf (V s)) {I : S → Type} [∀ s, Fintype (I s)] [∀ s, DecidableEq (I s)]
    (b : ∀ s, Module.Basis (I s) Kf (V s)) :
    ∃ Ψ : Module.Dual Kf (tensorLat Kf Kf V) ≃ₗ[Kf] tensorLat Kf Kf V,
      ∀ (Z : ∀ s, Module.Basis (I s) Kf (V s)) (z z' : Module.Basis (∀ s, I s) Kf (tensorLat Kf Kf V)),
        (∀ i, ((z i : tensorLat Kf Kf V) : MvPolynomial (S × (Fin k × Fin n)) Kf) =
          ∏ s, blockEmb Kf s ((Z s (i s) : V s) : MvPolynomial (Fin k × Fin n) Kf)) →
        (∀ i, ((z' i : tensorLat Kf Kf V) : MvPolynomial (S × (Fin k × Fin n)) Kf) =
          ∏ s, blockEmb Kf s ((dualB (β s) (Z s) (i s) : V s) : MvPolynomial (Fin k × Fin n) Kf)) →
        ∀ j, Ψ (z.coord j) = z' j := by
  obtain ⟨x, hx⟩ := prodBasis V b
  obtain ⟨x', hx'⟩ := prodBasis V (fun s => dualB (β s) (b s))
  refine ⟨x.dualBasis.equiv x' (Equiv.refl _), ?_⟩
  intro Z z z' hz hz' j
  have hΨ : ∀ (φ : Module.Dual Kf (tensorLat Kf Kf V)) i,
      x'.repr ((x.dualBasis.equiv x' (Equiv.refl _)) φ) i = φ (x i) := by
    intro φ i
    have h1 : (x.dualBasis.equiv x' (Equiv.refl _)) φ = ∑ a, φ (x a) • x' a := by
      conv_lhs => rw [← x.dualBasis.sum_repr φ]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [map_smul, Module.Basis.equiv_apply, Module.Basis.dualBasis_repr, Equiv.refl_apply]
    rw [h1, x'.repr_sum_self]
  apply x'.ext_elem
  intro i
  rw [hΨ, Module.Basis.coord_apply, repr_prod V Z z hz (fun s => b s (i s)) (x i) (hx i) j,
    repr_prod V (fun s => dualB (β s) (b s)) x' hx' (fun s => dualB (β s) (Z s) (j s)) (z' j) (hz' j) i]
  apply Finset.prod_congr rfl
  intro s _
  rw [dualB_repr, beta_dualB, Module.Basis.coord_apply]

end Psi

end Formalism.L2.G.Model
end
end

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

structure PosCore (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (p m : ℕ) (lam : Fin (m + 1) → ℤ) (N : ℕ)
    (β : ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf lam)) ≃ₗ[Kf]
      Module.Dual Kf ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf lam))) : Prop where
  up : ∀ M : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit M.det →
    ∀ Q : ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf lam)),
      (∀ P : ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf lam)),
        (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) ∈ nablaLTw O Kf m lam M →
          β Q P ∈ Set.range (algebraMap O Kf)) →
      (Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) ∈ nablaLTw O Kf m lam (M⁻¹).transpose
  low : ∀ M : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit M.det →
    ∀ Q P : ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf lam)),
      (Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) ∈ nablaLTw O Kf m lam (M⁻¹).transpose →
      (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) ∈ nablaLTw O Kf m lam M →
        β (((p : Kf) ^ N) • Q) P ∈ Set.range (algebraMap O Kf)

theorem latBasis {O Kf : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hM : IsUnit M.det) :
    ∃ Z : Module.Basis ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) Kf ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf lam)),
      Submodule.span O (Set.range fun i => ((Z i : ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf lam))) :
        MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)) = nablaLTw O Kf m lam M := by
  obtain ⟨B, -, b2, b3, b4⟩ := la_basis hinj m lam M hM
  refine ⟨(Module.Basis.span b3).map (LinearEquiv.ofEq _ _ b4), ?_⟩
  rw [← b2]
  congr 2
  funext i
  show (((LinearEquiv.ofEq _ _ b4) (Module.Basis.span b3 i) : ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf lam))) :
    MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) = _
  rw [LinearEquiv.coe_ofEq_apply]
  exact congrArg Subtype.val (Module.Basis.span_apply b3 i)

theorem repr_int {O Kf V : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V] [Module Kf V]
    [Module O V] [IsScalarTower O Kf V] {I : Type} (Z : Module.Basis I Kf V) (P : V)
    (hP : P ∈ Submodule.span O (Set.range Z)) (j : I) : Z.repr P j ∈ Set.range (algebraMap O Kf) := by
  classical
  induction hP using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact ⟨1, map_one _⟩
    · exact ⟨0, map_zero _⟩
  | zero => exact ⟨0, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a1, h1⟩ := hu
    obtain ⟨a2, h2⟩ := hv
    exact ⟨a1 + a2, by rw [map_add (f := _), map_add (f := _), Finsupp.add_apply, h1, h2]⟩
  | smul c v _ hv =>
    obtain ⟨a1, h1⟩ := hv
    refine ⟨c * a1, ?_⟩
    rw [← algebraMap_smul Kf c v, map_smul, Finsupp.smul_apply, map_mul, h1, smul_eq_mul]

theorem li_coe {O Kf X : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X]
    [Module O X] [IsScalarTower O Kf X] (hinj : Function.Injective (algebraMap O Kf)) {I : Type}
    (Vs : Submodule Kf X) (Z : Module.Basis I Kf Vs) : LinearIndependent O (fun i => ((Z i : Vs) : X)) := by
  have h1 : LinearIndependent Kf (fun i => ((Z i : Vs) : X)) :=
    Z.linearIndependent.map' Vs.subtype (Submodule.ker_subtype _)
  exact h1.restrict_scalars (by
    intro a b hab
    apply hinj
    simpa [Algebra.smul_def] using hab)

theorem ten_side (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf]
    (p : ℕ) {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant lam0) (N : Fin n' → ℕ)
    (β : ∀ s : Fin n', ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s))) ≃ₗ[Kf]
      Module.Dual Kf ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s))))
    (hβ : ∀ s, PosCore O Kf p m (lamAt lam0 s) (N s) (β s))
    (Vs : Submodule Kf (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf))
    (hVs : Vs = tensorLat Kf Kf (fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)))) :
    ∃ Ψ : Module.Dual Kf Vs ≃ₗ[Kf] Vs,
      ∀ Ms : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, (∀ s, IsUnit (Ms s).det) →
        (dualLat O Kf ((Hten O lam0 fun s => colSpan O (Ms s)).comap (Vs.subtype.restrictScalars O))).map
            (Ψ.toLinearMap.restrictScalars O) ≤
          (Hten O lam0 fun s => colSpan O ((Ms s)⁻¹).transpose).comap (Vs.subtype.restrictScalars O) ∧
        scale ((p : Kf) ^ (∑ s, N s))
            ((Hten O lam0 fun s => colSpan O ((Ms s)⁻¹).transpose).comap (Vs.subtype.restrictScalars O)) ≤
          (dualLat O Kf ((Hten O lam0 fun s => colSpan O (Ms s)).comap (Vs.subtype.restrictScalars O))).map
            (Ψ.toLinearMap.restrictScalars O) := by
  subst hVs
  classical
  have hinj : Function.Injective (algebraMap O Kf) := IsFractionRing.injective O Kf
  have hanti := kp_lamAt_antitone lam0 hd
  have hfin : ∀ s : Fin n', Finite ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s))) :=
    fun s => (sSIdxFinite (m + 1) (m + 1) (nuOf (lamAt lam0 s))).to_subtype
  let _ : ∀ s : Fin n', Fintype ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s))) := fun s => Fintype.ofFinite _
  set V : Fin n' → Submodule Kf (MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :=
    fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)) with hV
  have hb := fun s : Fin n' => latBasis (O := O) hinj m (lamAt lam0 s) 1 (by simp)
  choose b _ using hb
  obtain ⟨Ψ, hΨ⟩ := psi_exists V β b
  refine ⟨Ψ, fun Ms hMs => ?_⟩
  have hMs' : ∀ s, IsUnit (((Ms s)⁻¹).transpose).det := fun s => det_invT _ (hMs s)
  have hZ := fun s : Fin n' => latBasis (O := O) hinj m (lamAt lam0 s) (Ms s) (hMs s)
  choose Z hZ using hZ
  obtain ⟨z, hz⟩ := prodBasis V Z
  obtain ⟨z', hz'⟩ := prodBasis V (fun s => dualB (β s) (Z s))
  have hH : ∀ Ns : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, (∀ s, IsUnit (Ns s).det) →
      Hten O lam0 (fun s => colSpan O (Ns s)) =
        tensorLat O Kf (fun s => nablaLTw O Kf m (lamAt lam0 s) (Ns s)) := by
    intro Ns hNs
    unfold Hten
    congr 1
    funext s
    rw [H0_eq_twisted_nabla (la_indep hinj) _ _ (hanti s) _ (hNs s)]

  have hΛ : (Hten O lam0 fun s => colSpan O (Ms s)).comap ((tensorLat Kf Kf V).subtype.restrictScalars O) =
      Submodule.span O (Set.range z) := by
    obtain ⟨-, oS⟩ := tensorBasis O Kf (Fin n') (m + 1) (m + 1) _ _
      (fun s i => ((Z s i : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf))
      (fun s => li_coe hinj (V s) (Z s)) hZ
    rw [hH Ms hMs, ← oS, ← comap_span_coe]
    congr 3
    funext i
    exact (hz i).symm
  have hdual : dualLat O Kf (Submodule.span O (Set.range z)) =
      Submodule.span O (Set.range fun i => z.coord i) := by
    have := dualLat_span (O := O) z (fun _ => 1) (fun _ => one_ne_zero)
    simpa using this
  have hmap : (dualLat O Kf ((Hten O lam0 fun s => colSpan O (Ms s)).comap
      ((tensorLat Kf Kf V).subtype.restrictScalars O))).map (Ψ.toLinearMap.restrictScalars O) =
      Submodule.span O (Set.range z') := by
    rw [hΛ, hdual, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    exact hΨ Z z z' hz hz' j
  rw [hmap]
  have hPmem : ∀ s (P : V s), (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) ∈
      nablaLTw O Kf m (lamAt lam0 s) (Ms s) → P ∈ Submodule.span O (Set.range (Z s)) := by
    intro s P hP
    rw [← hZ s] at hP
    rw [← comap_span_coe]
    exact hP
  constructor
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show ((z' j : tensorLat Kf Kf V) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
      Hten O lam0 fun s => colSpan O ((Ms s)⁻¹).transpose
    rw [hz', hH _ hMs']
    apply Submodule.subset_span
    refine ⟨fun s => ((dualB (β s) (Z s) (j s) : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf),
      fun s => ?_, rfl⟩
    apply (hβ s).up (Ms s) (hMs s)
    intro P hP
    rw [beta_dualB, Module.Basis.coord_apply]
    exact repr_int (Z s) P (hPmem s P hP) (j s)
  · rintro _ ⟨Q, hQ, rfl⟩
    show ((p : Kf) ^ (∑ s, N s)) • Q ∈ Submodule.span O (Set.range z')
    rw [← comap_span_coe]
    show ((((p : Kf) ^ (∑ s, N s)) • Q : tensorLat Kf Kf V) :
      MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
      Submodule.span O (Set.range fun i => ((z' i : tensorLat Kf Kf V) :
        MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf))
    obtain ⟨-, oS'⟩ := tensorBasis O Kf (Fin n') (m + 1) (m + 1) _
      (fun s => Submodule.span O (Set.range fun i =>
        ((dualB (β s) (Z s) i : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)))
      (fun s i => ((dualB (β s) (Z s) i : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf))
      (fun s => li_coe hinj (V s) (dualB (β s) (Z s))) (fun s => rfl)
    have hr : (Set.range fun i => ((z' i : tensorLat Kf Kf V) :
        MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) =
        Set.range fun i : (∀ s, ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s)))) =>
          ∏ s, blockEmb Kf s ((dualB (β s) (Z s) (i s) : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) := by
      congr 1
      funext i
      exact hz' i
    rw [hr, oS', Submodule.coe_smul, ← Finset.prod_pow_eq_pow_sum]
    have hQ' : (Q : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
        tensorLat O Kf (fun s => nablaLTw O Kf m (lamAt lam0 s) ((Ms s)⁻¹).transpose) := by
      rw [← hH _ hMs']
      exact hQ
    refine lb_tensor O Kf _ _ (fun s => (p : Kf) ^ N s) (fun s F hF => ?_) _ hQ'
    have hFV : F ∈ V s := la_nablaLTw_le m (lamAt lam0 s) _ (hMs' s) F hF
    have h1 : (((p : Kf) ^ N s) • (⟨F, hFV⟩ : V s)) ∈
        Submodule.span O (Set.range fun i => (1 : Kf) • dualB (β s) (Z s) i) := by
      apply mem_span_of_coord (dualB (β s) (Z s)) (fun _ => 1) (fun _ => one_ne_zero)
      intro i
      rw [inv_one, one_mul, Module.Basis.coord_apply, dualB_repr]
      apply (hβ s).low (Ms s) (hMs s) ⟨F, hFV⟩ (Z s i) hF
      rw [← hZ s]
      exact Submodule.subset_span ⟨i, rfl⟩
    simp only [one_smul] at h1
    rw [← comap_span_coe] at h1
    exact h1

end Formalism.L2.G.Model
end
end

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

private theorem exists_twistVec_smul_eq_smul_twistVec {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}
    (h : HidaSetting p n' W Qq O Kf ι σ j w) {k : ℕ} (s : ℕ) (a : W) (x : Fin k → Qq) :
    ∃ b : O, twistVec ι σ s (a • x) = b • twistVec ι σ s x := by
  have hσ : ∀ (t : ℕ) (x : W), ∃ y : W, (σ ^ t) (algebraMap W Qq x) = algebraMap W Qq y := by
    intro t
    induction t with
    | zero => exact fun x => ⟨x, by simp⟩
    | succ t ih =>
      intro x
      obtain ⟨y, hy⟩ := ih x
      obtain ⟨z, hz⟩ := h.frob y
      refine ⟨y ^ p + (p : W) * z, ?_⟩
      have hs : (σ ^ (t + 1)) (algebraMap W Qq x) = σ ((σ ^ t) (algebraMap W Qq x)) := by
        rw [pow_succ']
        rfl
      rw [hs, hy, hz]
  obtain ⟨y, hy⟩ := hσ s a
  refine ⟨j y, ?_⟩
  funext i
  simp only [twistVec, Pi.smul_apply, Algebra.smul_def, map_mul, hy, h.ι_comp]

private theorem leAt_eq_colSpan_la_tw_mul_lb_D_of_edgeBasis {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}
    (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (e : Edge W Qq (m + 1))
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hgb : IsEdgeBasis p r e g) (s : ℕ) :
    LeAt p ι σ w s e = colSpan O (la_tw ι σ s g * lb_D (m + 1) r (algebraMap O Kf w)) := by
  obtain ⟨_, hsrc, htgt⟩ := hgb
  haveI := h.frac_alt
  have hpW : (p : W) ≠ 0 := h.p_unif.ne_zero
  have hpQ : (p : Qq) ≠ 0 := by
    have := (IsFractionRing.injective W Qq).ne hpW
    simpa using this
  have hpK : (p : Kf) ≠ 0 := by
    have := (map_ne_zero ι).mpr hpQ
    simpa using this
  have hpw : (p : Kf) = (algebraMap O Kf w) ^ 2 := by rw [← map_pow, h.w_sq, map_natCast]
  have hw0 : algebraMap O Kf w ≠ 0 := by
    intro h0
    apply hpK
    rw [hpw, h0]
    ring
  have tadd : ∀ x y : Fin (m + 1) → Qq, twistVec ι σ s (x + y) = twistVec ι σ s x + twistVec ι σ s y := by
    intro x y
    funext i
    simp [twistVec]
  have tzero : twistVec ι σ s (0 : Fin (m + 1) → Qq) = 0 := by
    funext i
    simp [twistVec]
  have tcol : ∀ c : Fin (m + 1), twistVec ι σ s (fun i => g i c) = fun i => la_tw ι σ s g i c := by
    intro c
    funext i
    simp [twistVec, la_tw, RingHom.mapMatrix_apply]
  have Rcol : ∀ c : Fin (m + 1), (fun i => (la_tw ι σ s g * lb_D (m + 1) r (algebraMap O Kf w)) i c) =
      (if c.val < r then (algebraMap O Kf w)⁻¹ else 1) • fun i => la_tw ι σ s g i c := by
    intro c
    funext i
    unfold lb_D
    rw [Matrix.mul_diagonal]
    split_ifs <;> simp [mul_comm]
  unfold LeAt
  rw [htgt]
  set T : (Fin (m + 1) → Qq) → (Fin (m + 1) → Kf) :=
    fun v => (algebraMap O Kf w)⁻¹ • twistVec ι σ s ((p : W) • v) with hT
  have Tadd : ∀ x y, T (x + y) = T x + T y := by
    intro x y
    simp only [hT, smul_add, tadd]
  have Tzero : T 0 = 0 := by
    simp only [hT, smul_zero, tzero]
  have Tsmul : ∀ (a : W) (x : Fin (m + 1) → Qq), ∃ b : O, T (a • x) = b • T x := by
    intro a x
    obtain ⟨b, hb⟩ := exists_twistVec_smul_eq_smul_twistVec h s a ((p : W) • x)
    refine ⟨b, ?_⟩
    simp only [hT]
    rw [smul_comm (p : W) a x, hb]
    exact smul_comm _ _ _
  have key : ∀ c : Fin (m + 1),
      T (fun i => (g * Matrix.diagonal fun c : Fin (m + 1) => if c.val < r then ((p : Qq))⁻¹ else 1) i c) =
        (if c.val < r then (algebraMap O Kf w)⁻¹ else algebraMap O Kf w) • fun i => la_tw ι σ s g i c := by
    clear Tadd Tzero Tsmul Rcol tcol tadd tzero hsrc htgt hpW hpQ
    intro c
    funext i
    have e1 : (g * Matrix.diagonal fun c : Fin (m + 1) => if c.val < r then ((p : Qq))⁻¹ else 1) i c =
        g i c * (if c.val < r then ((p : Qq))⁻¹ else 1) := Matrix.mul_diagonal _ _ _ _
    simp only [hT, Pi.smul_apply, smul_eq_mul, twistVec, e1]
    simp only [Algebra.smul_def, map_natCast, map_mul]
    split_ifs with hc
    · simp [la_tw, RingHom.mapMatrix_apply, map_inv₀]
      field_simp
      try simp
    · simp [la_tw, RingHom.mapMatrix_apply]
      rw [hpw]
      field_simp
  have hext : extO O ι σ s e.src = colSpan O (la_tw ι σ s g) := by
    rw [hsrc]
    unfold extO colSpan
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe] at hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨c, rfl⟩ := hx
        exact Submodule.subset_span ⟨c, (tcol c).symm⟩
      | zero => rw [tzero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [tadd]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
        obtain ⟨b, hb⟩ := exists_twistVec_smul_eq_smul_twistVec h s a x
        rw [hb]
        exact Submodule.smul_mem _ _ hx
    · rw [Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      exact Submodule.subset_span ⟨fun i => g i c, Submodule.subset_span ⟨c, rfl⟩, tcol c⟩
  rw [hext]
  unfold colSpan
  apply le_antisymm
  · apply sup_le
    · rw [Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      by_cases hc : c.val < r
      · have hA : (fun i => la_tw ι σ s g i c) =
            w • (fun i => (la_tw ι σ s g * lb_D (m + 1) r (algebraMap O Kf w)) i c) := by
          rw [Rcol c, if_pos hc, ← algebraMap_smul Kf w, smul_smul, mul_inv_cancel₀ hw0, one_smul]
        rw [SetLike.mem_coe]
        beta_reduce
        rw [hA]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
      · have hA : (fun i => la_tw ι σ s g i c) =
            (fun i => (la_tw ι σ s g * lb_D (m + 1) r (algebraMap O Kf w)) i c) := by
          rw [Rcol c, if_neg hc, one_smul]
        rw [SetLike.mem_coe]
        beta_reduce
        rw [hA]
        exact Submodule.subset_span ⟨c, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe] at hv ⊢
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨c, rfl⟩ := hx
        beta_reduce
        rw [key c]
        by_cases hc : c.val < r
        · rw [if_pos hc]
          exact Submodule.subset_span ⟨c, by beta_reduce; rw [Rcol c, if_pos hc]⟩
        · rw [if_neg hc, algebraMap_smul]
          refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, ?_⟩)
          beta_reduce
          rw [Rcol c, if_neg hc, one_smul]
      | zero => rw [Tzero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [Tadd]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
        obtain ⟨b, hb⟩ := Tsmul a x
        rw [hb]
        exact Submodule.smul_mem _ _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe]
    beta_reduce
    by_cases hc : c.val < r
    · have hk := key c
      rw [if_pos hc] at hk
      rw [Rcol c, if_pos hc, ← hk]
      apply Submodule.mem_sup_right
      exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨c, rfl⟩, rfl⟩
    · rw [Rcol c, if_neg hc, one_smul]
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨c, rfl⟩)

section
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem leAt_of_basis (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (e : Edge W Qq (m + 1))
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hgb : IsEdgeBasis p r e g) (s : ℕ) :
    LeAt p ι σ w s e = colSpan O (la_tw ι σ s g * lb_D (m + 1) r (algebraMap O Kf w)) := by
  exact leAt_eq_colSpan_la_tw_mul_lb_D_of_edgeBasis h m r e g hgb s

theorem extO_colSpan (h : HidaSetting p n' W Qq O Kf ι σ j w) {k : ℕ} (g : Matrix (Fin k) (Fin k) Qq) (s : ℕ) :
    extO O ι σ s (colSpan W g) = colSpan O (la_tw ι σ s g) := by
  have hσ : ∀ (t : ℕ) (x : W), ∃ y : W, (σ ^ t) (algebraMap W Qq x) = algebraMap W Qq y := by
    intro t
    induction t with
    | zero => exact fun x => ⟨x, by simp⟩
    | succ t ih =>
      intro x
      obtain ⟨y, hy⟩ := ih x
      obtain ⟨z, hz⟩ := h.frob y
      refine ⟨y ^ p + (p : W) * z, ?_⟩
      have hs : (σ ^ (t + 1)) (algebraMap W Qq x) = σ ((σ ^ t) (algebraMap W Qq x)) := by
        rw [pow_succ']
        rfl
      rw [hs, hy, hz]
  have tadd : ∀ x y : Fin k → Qq, twistVec ι σ s (x + y) = twistVec ι σ s x + twistVec ι σ s y := by
    intro x y
    funext i
    simp [twistVec]
  have tzero : twistVec ι σ s (0 : Fin k → Qq) = 0 := by
    funext i
    simp [twistVec]
  have tsmul : ∀ (a : W) (x : Fin k → Qq), ∃ b : O, twistVec ι σ s (a • x) = b • twistVec ι σ s x := by
    intro a x
    obtain ⟨y, hy⟩ := hσ s a
    refine ⟨j y, ?_⟩
    funext i
    simp only [twistVec, Pi.smul_apply, Algebra.smul_def, map_mul, hy, h.ι_comp]
  have tcol : ∀ c : Fin k, twistVec ι σ s (fun i => g i c) = fun i => la_tw ι σ s g i c := by
    intro c
    funext i
    simp [twistVec, la_tw, RingHom.mapMatrix_apply]
  unfold extO colSpan
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v ∈ Submodule.span W (Set.range fun c : Fin k => fun i => g i c) := hv
    clear hv
    induction hv' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact Submodule.subset_span ⟨c, (tcol c).symm⟩
    | zero => rw [tzero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [tadd]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      obtain ⟨b, hb⟩ := tsmul a x
      rw [hb]
      exact Submodule.smul_mem _ _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact Submodule.subset_span ⟨fun i => g i c, Submodule.subset_span ⟨c, rfl⟩, tcol c⟩

end

section
variable {Qq Kf : Type} [Field Qq] [Field Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (s : ℕ) {k : ℕ}

theorem tw_mul (A B : Matrix (Fin k) (Fin k) Qq) : la_tw ι σ s (A * B) = la_tw ι σ s A * la_tw ι σ s B := by
  unfold la_tw
  exact map_mul _ A B

theorem tw_invT (g : Matrix (Fin k) (Fin k) Qq) (hg : IsUnit g.det) :
    la_tw ι σ s (g⁻¹).transpose = ((la_tw ι σ s g)⁻¹).transpose := by
  have key : la_tw ι σ s g⁻¹ = (la_tw ι σ s g)⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    rw [← tw_mul, Matrix.nonsing_inv_mul _ hg]
    unfold la_tw
    exact map_one _
  rw [← key]
  ext a b
  rfl

theorem tw_dE (r p : ℕ) : la_tw ι σ s (dE k r (p : Qq)) = dE k r (p : Kf) := by
  unfold la_tw dE
  rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext a
  split_ifs <;> simp

theorem dE_sq_D (r : ℕ) (c : Kf) (hc : c ≠ 0) : dE k r (c ^ 2) * lb_D k r c = dE k r c := by
  unfold dE lb_D
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  split_ifs <;> simp [pow_two, mul_assoc, hc]

end

theorem det_invT_zpow {Kf : Type} [Field Kf] {k : ℕ} (M : Matrix (Fin k) (Fin k) Kf) (hM : IsUnit M.det) (e : ℤ) :
    M.det ^ e * ((M⁻¹).transpose).det ^ e = 1 := by
  rw [Matrix.det_transpose, Matrix.det_nonsing_inv, ← mul_zpow, Ring.mul_inverse_cancel _ hM, one_zpow]

theorem posCore_of_form {O Kf : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (p m : ℕ) (lam : Fin (m + 1) → ℤ) (N : ℕ)
    (B : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] Kf)
    (ha : ∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf),
        B (rowAct Kf g P) Q = B P (rowAct Kf g.transpose Q))
    (hb : ∀ Q ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam),
        (∀ P ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam), B P Q = 0) → Q = 0)
    (hc : ∀ Q ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam),
        (∀ P ∈ nabO O Kf m (nuOf lam), B P Q ∈ Set.range (algebraMap O Kf)) → Q ∈ nabO O Kf m (nuOf lam))
    (hdd : ∀ Q ∈ nabO O Kf m (nuOf lam), ∀ P ∈ nabO O Kf m (nuOf lam),
        B P (((p : Kf) ^ N) • Q) ∈ Set.range (algebraMap O Kf)) :
    ∃ β, PosCore O Kf p m lam N β := by
  classical
  set V := dualWeyl Kf (m + 1) (m + 1) (nuOf lam) with hV
  obtain ⟨Z0, -⟩ := latBasis (O := O) hinj m lam 1 (by simp)
  have hfinI : Finite ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) := (sSIdxFinite (m + 1) (m + 1) (nuOf lam)).to_subtype
  have hfd : FiniteDimensional Kf V := Module.Finite.of_basis Z0
  let β0 : V →ₗ[Kf] Module.Dual Kf V :=
    LinearMap.mk₂ Kf (fun (Q P : V) => B (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) Q)
      (by intro Q Q' P; simp)
      (by intro c Q P; simp)
      (by intro Q P P'; simp)
      (by intro c Q P; simp)
  have hβ0 : ∀ Q P : V, β0 Q P = B (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) Q := fun _ _ => rfl
  have hinjβ : Function.Injective β0 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Q hQ
    apply Subtype.ext
    apply hb _ Q.2
    intro P hP
    have := congrArg (fun f => f ⟨P, hP⟩) hQ
    exact this
  let β : V ≃ₗ[Kf] Module.Dual Kf V := LinearMap.linearEquivOfInjective β0 hinjβ Subspace.dual_finrank_eq.symm
  have hβ : ∀ Q P : V, β Q P = B (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) Q := fun _ _ => rfl
  set e : ℤ := lam (Fin.last m) with he
  have key : ∀ (M : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf), IsUnit M.det →
      ∀ P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf,
      B (M.det ^ e • rowAct Kf M P) (((M⁻¹).transpose).det ^ e • rowAct Kf (M⁻¹).transpose Q) = B P Q := by
    intro M hM P Q
    rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul, smul_eq_mul, mul_comm (((M⁻¹).transpose).det ^ e),
      det_invT_zpow M hM e, one_mul, ← ha, ldlat_rowAct_inv_right rowActMul M hM]
  have mem_iff : ∀ (M : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf), IsUnit M.det →
      ∀ F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf,
      F ∈ nablaLTw O Kf m lam M ↔ M.det ^ e • rowAct Kf M F ∈ nabO O Kf m (nuOf lam) :=
    fun M hM F => nablaLTwMem O Kf m lam M hM F
  refine ⟨β, ⟨?_, ?_⟩⟩
  · intro M hM Q hQ
    rw [mem_iff _ (det_invT M hM)]
    apply hc
    · exact Submodule.smul_mem _ _ (dualWeylRowStable Kf _ _ _ _ _ Q.2)
    · intro P0 hP0
      set P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf := M.det ^ (-e) • rowAct Kf M⁻¹ P0 with hP
      have h1 : M.det ^ e • rowAct Kf M P = P0 := by
        rw [hP, map_smul, smul_smul, ← zpow_add₀ hM.ne_zero, add_neg_cancel, zpow_zero, one_smul,
          ldlat_rowAct_inv_left rowActMul M hM]
      have h2 : P ∈ nablaLTw O Kf m lam M := by
        rw [mem_iff M hM, h1]; exact hP0
      have h3 := hQ ⟨P, la_nablaLTw_le m lam M hM P h2⟩ h2
      rw [hβ, ← key M hM, h1] at h3
      exact h3
  · intro M hM Q P hQ hP
    rw [hβ]
    have h1 := (mem_iff M hM _).1 hP
    have h2 := (mem_iff _ (det_invT M hM) _).1 hQ
    have h3 := hdd _ h2 _ h1
    rw [map_smul, key M hM] at h3
    rw [Submodule.coe_smul, map_smul]
    exact h3

end Formalism.L2.G.Model

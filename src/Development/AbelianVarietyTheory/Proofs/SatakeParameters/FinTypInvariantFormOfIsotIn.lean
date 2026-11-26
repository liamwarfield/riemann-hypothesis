module

public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowEqSpanNormOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormResFormPullFormPull

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinTypInvariantFormOfIsotIn
open Formalism.BasicNotions Formalism.L2 Formalism.L2.NG Formalism.AUTREP Formalism.IndefR.principalLevelFrame

namespace GlobalTheory

theorem finTyp_invariant_form_of_isotIn : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (B : A → A → ℂ), (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z) → (∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x)) → (∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) → (∀ h, ∀ x ∈ C, ρ h x ∈ C) → (∀ h, ∀ x ∈ C, ∀ y ∈ C, B (ρ h x) (ρ h y) = B x y) → ∀ π : FinTyp D.host.E n, isotIn (D := D) ρ C π ≠ ⊥ → ∃ B' : π.S → π.S → ℂ, (∀ x y z (c : ℂ), B' x (y + c • z) = B' x y + c * B' x z) ∧ (∀ x y, B' x y = starRingEnd ℂ (B' y x)) ∧ (∀ x, x ≠ 0 → 0 < (B' x x).re) ∧ ∀ h (x y x' y' : π.S), (x' : GAf D.host.E n → ℂ) = rt D.host.E n h x → (y' : GAf D.host.E n → ℂ) = rt D.host.E n h y → B' x' y' = B' x y := by
  intro D n A _ _ ρ C B hlin hherm hpos _hstab hinv π hne

  obtain ⟨Φ, ⟨hΦe, hΦC⟩, hΦne⟩ : ∃ Φ : π.S →ₗ[ℂ] A, (IsEqvA ρ π Φ ∧ LinearMap.range Φ ≤ C) ∧ LinearMap.range Φ ≠ ⊥ := by
    by_contra hcon
    push_neg at hcon
    apply hne
    unfold isotIn
    refine iSup_eq_bot.2 fun Φ => iSup_eq_bot.2 fun hΦ => hcon Φ hΦ
  have hmemC : ∀ x : π.S, Φ x ∈ C := fun x => hΦC (LinearMap.mem_range_self Φ x)

  let S' : Submodule ℂ (GAf D.host.E n → ℂ) := (LinearMap.ker Φ).map π.S.subtype
  have hS'le : S' ≤ π.S := by
    rintro f ⟨k, _, rfl⟩
    exact k.2
  have hS'st : ∀ h, ∀ f ∈ S', rt D.host.E n h f ∈ S' := by
    rintro h f ⟨k, hk, rfl⟩
    refine ⟨⟨rt D.host.E n h k, π.stable h k k.2⟩, ?_, rfl⟩
    have hk' : Φ k = 0 := hk
    show Φ _ = 0
    rw [hΦe h k, hk', map_zero]
  have hinj : ∀ x : π.S, Φ x = 0 → x = 0 := by
    intro x hx
    rcases π.irr S' hS'le hS'st with h0 | hall
    · have : (x : GAf D.host.E n → ℂ) ∈ S' := ⟨x, hx, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact Subtype.ext this
    · exfalso
      apply hΦne
      rw [eq_bot_iff]
      rintro a ⟨y, rfl⟩
      have : (y : GAf D.host.E n → ℂ) ∈ S' := by rw [hall]; exact y.2
      obtain ⟨k, hk, hky⟩ := this
      have : k = y := Subtype.ext hky
      subst this
      have hk' : Φ k = 0 := hk
      exact (Submodule.mem_bot ℂ).2 hk'
  refine ⟨fun x y => B (Φ x) (Φ y), ?_, ?_, ?_, ?_⟩
  · intro x y z c
    simp only [map_add (f := _), map_smul]
    exact hlin _ (hmemC x) _ (hmemC y) _ (hmemC z) c
  · intro x y
    exact hherm _ (hmemC x) _ (hmemC y)
  · intro x hx
    exact hpos _ (hmemC x) (fun h0 => hx (hinj x h0))
  · intro h x y x' y' hx hy
    have ex : x' = ⟨rt D.host.E n h x, π.stable h x x.2⟩ := Subtype.ext hx
    have ey : y' = ⟨rt D.host.E n h y, π.stable h y y.2⟩ := Subtype.ext hy
    simp only
    rw [ex, ey, hΦe h x, hΦe h y]
    exact hinv h _ (hmemC x) _ (hmemC y)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharPolLpCharOfUnr
noncomputable section

namespace GlobalTheory.SplitRead.BlockParam

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
open GlobalTheory.WeilDeligne (WD Weil ineIncl)

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem charpoly_smul_one {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (c : ℂ) :
    (c • (1 : Module.End ℂ V)).charpoly = (X - C c) ^ Module.finrank ℂ V := by
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, LinearMap.toMatrix_one,
    Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal]
  simp

theorem charPol_lpChar_of_unr (a χ : WD h) (ha : a.unr) (σ : Ine (F := E) B) (c : ℂ)
    (hc : χ.charPol (ineIncl h σ) = X - C c) :
    (a.lpChar χ).charPol (ineIncl h σ) = (X - C c) ^ a.lpDim := by
  have hd : χ.lpDim = 1 := by rw [← WD.charPol_natDegree χ (ineIncl h σ), hc, natDegree_X_sub_C]
  induction a using WD.ind with
  | hP n a =>
  induction χ using WD.ind with
  | hP m b =>
    rw [WD.unr_mk] at ha
    rw [WD.lpDim_mk] at hd
    rw [WD.charPol_mk] at hc
    have h3 := LinearMap.aeval_self_charpoly (b.ρ (ineIncl h σ))
    rw [hc, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at h3
    rw [WD.lpChar_mk, WD.charPol_mk, WD.lpDim_mk, GlobalTheory.WeilDeligne.WDRep.tensor_ρ, ha.2, h3,
      TensorProduct.map_smul_right, TensorProduct.map_one, charpoly_smul_one, Module.finrank_tensorProduct, hd,
      mul_one]

theorem irreducible_twist {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ Γ V}
    (hρ : ρ.IsIrreducible) (χ : Γ →* ℂˣ) : (twist ρ χ).IsIrreducible :=
  OrderIso.isSimpleOrder_iff (α := Subrepresentation (twist ρ χ)) (β := Subrepresentation ρ)
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have := S.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
        simpa [smul_smul] using this⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl } |>.2 hρ

def detIrr (n : ℕ) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Irr k n where
  V := ℂ
  π := detRep (Fin n) χ
  smooth := (isSmooth_ofChar_iff _).2 hχ.detChar
  irr := isIrreducible_ofChar _

def twistIrr {n : ℕ} (π : Irr k n) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Irr k n where
  V := π.V
  π := twist π.π (detChar (Fin n) χ)
  smooth := isSmooth_twist π.smooth hχ.detChar
  irr := irreducible_twist π.irr _

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.SplitRead.BlockParam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockCharIntegral
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.SplitRead

open Formalism.MainNotions.SumRepresentations.At

theorem charpoly_fin_one {k : Type} [CommRing k] (M : Matrix (Fin 1) (Fin 1) k) :
    M.charpoly = X - C (M 0 0) := by
  simp [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply]

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def blockShift (R : Ranks) : ℝ := ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2

theorem blockChar_integral (hAut : TieAut N A) (hMu : MuInt N A) (i : N.Loc) (τ : H.E →+* ℂ) (z : ℂ)
    (hz : z ∈ A.infG (A.tw (A.muC i) A.etaTinv) τ) : ∃ k : ℤ, z + ((blockShift R : ℝ) : ℂ) = (k : ℂ) := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have h2 := R.two_le_m
  obtain ⟨c, hc⟩ : ∃ c : ℕ, R.r = 2 * c + 1 := ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have hs : ((blockShift R : ℝ) : ℂ) = -(c : ℂ) - 1 / 2 := by
    have : blockShift R = -(c : ℝ) - 1 / 2 := by
      simp only [blockShift, Ranks.nV, hc]
      push_cast
      ring
    rw [this]
    push_cast
    ring
  obtain ⟨h1, h3⟩ := hAut.2.1 τ
  rcases h1 with h1 | h1
  · have he : A.infG A.etaTinv τ = {-(1 / 2)} := by rw [h3, h1]; simp
    rw [A.infG_tw _ _ _ _ he, Multiset.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨m, rfl⟩ := hMu i τ y hy
    exact ⟨m - c - 1, by rw [hs]; push_cast; ring⟩
  · have he : A.infG A.etaTinv τ = {1 / 2} := by rw [h3, h1]; simp
    rw [A.infG_tw _ _ _ _ he, Multiset.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨m, rfl⟩ := hMu i τ y hy
    exact ⟨m - c, by rw [hs]; push_cast; ring⟩

theorem finite_placesOver (l : ℕ) (hl : l ≠ 0) : (placesOver H.E l).Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 H.E)} ≠ 0 := by
    simpa using hl
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv

theorem blockChar_eq (h5 : JacquetShalikaStrongMultOne N A) (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin 1) (Qbar (N.l i)))
    (hρ : ContQ N i ρ)
    (hwd : ∀ w, w ∉ placesOver H.E (N.l i) →
      A.wdOf i ρ w = A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w) (blockShift R))
    (g : G H.E N.Om) :
    ((ρ g : GL (Fin 1) (Qbar (N.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (N.l i))) 0 0 =
      iotaOQ N A i (chi1 N i g) := by
  have hl : N.l i ≠ 0 := (Fact.out : (N.l i).Prime).ne_zero
  have hfin : (placesOver H.E (N.l i) ∪ ((N.S i : Set _) ∪ (N.Q i : Set _))).Finite :=
    (finite_placesOver (H := H) _ hl).union ((N.S i).finite_toSet.union (N.Q i).finite_toSet)
  have hd := h5.2.2.1 _ hfin
  have hc1 : Continuous fun g : G H.E N.Om =>
      ((ρ g : GL (Fin 1) (Qbar (N.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (N.l i))) 0 0 :=
    (continuous_apply_apply 0 0).comp hρ
  have hc2 : Continuous fun g : G H.E N.Om => iotaOQ N A i (chi1 N i g) :=
    (GlobalTheory.CoeffEmbedding.continuous_iotaOQ_of_data N A i).comp (N.chi_cont i 1)
  refine congrFun (Continuous.ext_on (dense_iff_closure_eq.2 hd) hc1 hc2 ?_) g
  rintro σ ⟨w, hw, hsp, B, hB, hσ⟩
  simp only [Set.mem_union, Finset.mem_coe, not_or] at hw
  obtain ⟨hwl, hwS, hwQ⟩ := hw
  have hso : SplitOut N i w := ⟨hsp, hwl, hwS, hwQ⟩
  obtain ⟨hu, hf⟩ := A.chi_mu i w hso
  have hun : A.unr (A.wdOf i ρ w) := by
    rw [hwd w hwl]; exact (A.unr_tw _ _).2 hu
  have e := A.wdOf_frob i ρ w hwl hρ hun B σ hB hσ
  rw [hwd w hwl, show blockShift R = ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 from rfl, hf B σ hB hσ,
    charpoly_fin_one] at e
  simp only [Multiset.map_singleton, Multiset.prod_singleton, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C] at e
  have e2 := C_injective (sub_right_injective e)
  exact (A.iotaQC i).injective e2

end GlobalTheory.SplitRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHyperspecialDoubleCosetOfElementaryDivisor
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHyperspecialDoubleCosetOfElementaryDivisor
namespace GlobalTheory.SplitLabel

open Matrix

section Alg

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem smul_mulVec_congr (ε : R) (M : Matrix n n R) {x y : n → R} (h : ε • x = ε • y) :
    ε • M *ᵥ x = ε • M *ᵥ y := by
  rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, h]

omit [DecidableEq n] in
theorem smul_mulVec_mat (ε : R) {A B B' : Matrix n n R} (h : ε • (A * B) = ε • B') (x : n → R) :
    ε • A *ᵥ (B *ᵥ x) = ε • B' *ᵥ x := by
  rw [Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, h, Matrix.smul_mulVec]


omit [DecidableEq n] in
theorem stab_of_bases (ε : R) (hε : ε * ε = ε) (Λ Z : Set (n → R)) {A B B' : Matrix n n R}
    (h : ε • (A * B) = ε • B')
    (h1 : ∀ z ∈ Z, ε • B *ᵥ z ∈ Λ) (h2 : ∀ y ∈ Λ, ∃ z ∈ Z, ε • y = ε • B *ᵥ z)
    (h1' : ∀ z ∈ Z, ε • B' *ᵥ z ∈ Λ) (h2' : ∀ y ∈ Λ, ∃ z ∈ Z, ε • y = ε • B' *ᵥ z) :
    (∀ y ∈ Λ, ε • A *ᵥ y ∈ Λ) ∧ ∀ y ∈ Λ, ∃ z ∈ Λ, ε • y = ε • A *ᵥ z := by
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨z, hz, e⟩ := h2 y hy
    rw [smul_mulVec_congr ε A e, smul_mulVec_mat ε h]
    exact h1' z hz
  · obtain ⟨z, hz, e⟩ := h2' y hy
    refine ⟨_, h1 z hz, ?_⟩
    rw [e, ← smul_mulVec_mat ε h]
    apply smul_mulVec_congr
    rw [smul_smul, hε]

theorem stab_of_div (ε : R) (Λ Z : Set (n → R)) {A B B' M M' N b : Matrix n n R}
    (t t' : n → R) (h : ε • (A * B) = ε • B') (hN : N * (A * M) = 1) (hb : b = N * M')
    (hΛ : ∀ y ∈ Λ, ε • y ∈ Λ)
    (hu : ∀ z ∈ Z, ∃ w ∈ Z, ε • (fun i => t' i * z i) = ε • fun i => t i * w i)
    (hu' : ∀ z ∈ Z, ∃ w ∈ Z, ε • (fun i => t i * z i) = ε • fun i => t' i * w i)
    (h3 : ∀ y ∈ Λ, ∃ z ∈ Z, ε • M *ᵥ y = ε • B *ᵥ fun i => t i * z i)
    (h4 : ∀ z ∈ Z, ∃ y ∈ Λ, ε • M *ᵥ y = ε • B *ᵥ fun i => t i * z i)
    (h3' : ∀ y ∈ Λ, ∃ z ∈ Z, ε • M' *ᵥ y = ε • B' *ᵥ fun i => t' i * z i)
    (h4' : ∀ z ∈ Z, ∃ y ∈ Λ, ε • M' *ᵥ y = ε • B' *ᵥ fun i => t' i * z i) :
    (∀ y ∈ Λ, ε • b *ᵥ y ∈ Λ) ∧ ∀ y ∈ Λ, ∃ z ∈ Λ, ε • y = ε • b *ᵥ z := by
  have key : ∀ y y' : n → R, ε • M' *ᵥ y' = ε • A *ᵥ (M *ᵥ y) → ε • b *ᵥ y' = ε • y := by
    intro y y' e
    rw [hb, ← Matrix.mulVec_mulVec, smul_mulVec_congr ε N e, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, hN, Matrix.one_mulVec]
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨z, hz, e⟩ := h3' y hy
    obtain ⟨w, hw, ew⟩ := hu z hz
    obtain ⟨y', hy', e'⟩ := h4 w hw
    rw [key y' y]
    · exact hΛ y' hy'
    · rw [e, smul_mulVec_congr ε B' ew, smul_mulVec_congr ε A e', smul_mulVec_mat ε h]
  · obtain ⟨z, hz, e⟩ := h3 y hy
    obtain ⟨w, hw, ew⟩ := hu' z hz
    obtain ⟨y', hy', e'⟩ := h4' w hw
    refine ⟨y', hy', (key y y' ?_).symm⟩
    rw [e', smul_mulVec_congr ε A e, smul_mulVec_mat ε h, smul_mulVec_congr ε B' ew]

omit [DecidableEq n] in
theorem smul_mul_congr_left (ε : R) {X Y : Matrix n n R} (h : ε • X = ε • Y) (Z : Matrix n n R) :
    ε • (X * Z) = ε • (Y * Z) := by
  rw [← Matrix.smul_mul, h, Matrix.smul_mul]

omit [DecidableEq n] in
theorem smul_mul_congr_right (ε : R) {X Y : Matrix n n R} (h : ε • X = ε • Y) (Z : Matrix n n R) :
    ε • (Z * X) = ε • (Z * Y) := by
  rw [← Matrix.mul_smul, h, Matrix.mul_smul]

end Alg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem change_unif {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D)
    (ϖ ϖ' : 𝓞 D.host.E) (k : Fin V.rank → ℤ) (he : IsIdemAt e P) (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2)
    (h1' : ϖ' ∈ P.asIdeal) (h2' : ϖ' ∉ P.asIdeal ^ 2)
    (z : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (hz : IntVec z) :
    ∃ w, IntVec w ∧ finPart D e • (fun i => finPart D (incA D ((ϖ' : D.host.E) ^ k i)) * z i) =
      finPart D e • fun i => finPart D (incA D ((ϖ : D.host.E) ^ k i)) * w i := by
  have hε : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1.1]
  have h0 : (ϖ : D.host.E) ≠ 0 := by
    intro h
    have : ϖ = 0 := by exact_mod_cast h
    exact h2 (this ▸ zero_mem _)
  refine ⟨fun i => finPart D e * finPart D (incA D ((ϖ' : D.host.E) ^ k i / (ϖ : D.host.E) ^ k i)) * z i,
    fun i => GlobalTheory.SplitLatBasis.mul_mem_intAE D ((GlobalTheory.T.completedLattice_integrality V).2.1 P e ϖ ϖ' he h1 h2 h1' h2' (k i)) (hz i), ?_⟩
  funext i
  have e1 : finPart D (incA D ((ϖ' : D.host.E) ^ k i)) = finPart D (incA D ((ϖ : D.host.E) ^ k i)) *
      finPart D (incA D ((ϖ' : D.host.E) ^ k i / (ϖ : D.host.E) ^ k i)) := by
    rw [← map_mul, ← map_mul, mul_div_cancel₀ _ (zpow_ne_zero _ h0)]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [e1]
  linear_combination (-(finPart D (incA D ((ϖ : D.host.E) ^ k i)) *
      finPart D (incA D ((ϖ' : D.host.E) ^ k i / (ϖ : D.host.E) ^ k i)) * z i)) * hε

theorem split_label : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ ϖ' : 𝓞 D.host.E) (d : List ℤ) (α α' : GA D V), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → Formalism.L2.Theta.SuppAt e V α → Formalism.L2.Theta.SuppAt e V α' → DivAt V e (ϖ : D.host.E) d α → DivAt V e (ϖ' : D.host.E) d α' → ∃ a ∈ locPart V (KsphC V ∅) e, ∃ b ∈ locPart V (KsphC V ∅) e, α' = a * α * b := by
  intro D V P e ϖ ϖ' d α α' he h1 h2 h1' h2' hα hα' hd hd'
  obtain ⟨-, B, hB1, hB2, hB3, hB4⟩ := hd
  obtain ⟨-, B', hB1', hB2', hB3', hB4'⟩ := hd'
  have hε : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1.1]
  obtain ⟨C, hBC, hCB⟩ := (GlobalTheory.T.completedLattice_integrality V).2.2 _ B hε fun y hy => (hB2 y hy).imp fun _ h => h.2
  obtain ⟨C', hBC', hCB'⟩ := (GlobalTheory.T.completedLattice_integrality V).2.2 _ B' hε fun y hy => (hB2' y hy).imp fun _ h => h.2
  have hinv : finPart D e • ((B' * C) * (B * C')) = finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) := by
    have := smul_mul_congr_right _ (smul_mul_congr_left _ hCB C') B'
    rw [Matrix.one_mul, hBC'] at this
    rw [← this]
    simp only [Matrix.mul_assoc]
  obtain ⟨a, haS, ha⟩ := GlobalTheory.T.exists_adelic_unitary_split_place_component V e he.1 _ _ hinv
  have hAB : finPart D e • (finMat D.sp.cm.sig V.gram a * B) = finPart D e • B' := by
    rw [smul_mul_congr_left _ ha B, Matrix.mul_assoc, smul_mul_congr_right _ hCB B', Matrix.mul_one]
  have hs := stab_of_bases (finPart D e) hε {y | y ∈ LamHat V} {z | IntVec z} hAB
    (fun z hz => hB1 z hz) (fun y hy => hB2 y hy) (fun z hz => hB1' z hz) (fun y hy => hB2' y hy)
  have haK : a ∈ KsphC V ∅ := GlobalTheory.T.mem_hyperspecial_of_split_place_stabilizer V e a he.1 haS hs.1 hs.2
  obtain ⟨hf1, hf2, -⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e (e + cA D e) (Or.inl ⟨he, rfl⟩)
  obtain ⟨L, hL⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 _ hf1 hf2).1
  have hbS : Formalism.L2.Theta.SuppAt e V ((a * α)⁻¹ * α') :=
    (hL _).1 (L.mul_mem (L.inv_mem (L.mul_mem ((hL _).2 haS) ((hL _).2 hα))) ((hL _).2 hα'))
  have hN : finMat D.sp.cm.sig V.gram (a * α)⁻¹ *
      (finMat D.sp.cm.sig V.gram a * finMat D.sp.cm.sig V.gram α) = 1 := by
    rw [← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, ← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, inv_mul_cancel,
      Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one]
  have ht := stab_of_div (finPart D e) {y | y ∈ LamHat V} {z | IntVec z}
    (fun i => finPart D (incA D ((ϖ : D.host.E) ^ d.getD i.1 0)))
    (fun i => finPart D (incA D ((ϖ' : D.host.E) ^ d.getD i.1 0))) hAB hN
    (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul _ _ (a * α)⁻¹ α')
    (fun y hy => (GlobalTheory.T.completedLattice_integrality V).1 _ (GlobalTheory.AdIdem.idempotent_mem_intAE D _ hε) y hy)
    (fun z hz => change_unif V P e ϖ ϖ' _ he h1 h2 h1' h2' z hz)
    (fun z hz => change_unif V P e ϖ' ϖ _ he h1' h2' h1 h2 z hz)
    (fun y hy => hB3 y hy) (fun z hz => hB4 z hz) (fun y hy => hB3' y hy) (fun z hz => hB4' z hz)
  have hbK : (a * α)⁻¹ * α' ∈ KsphC V ∅ := GlobalTheory.T.mem_hyperspecial_of_split_place_stabilizer V e _ he.1 hbS ht.1 ht.2
  exact ⟨a, ⟨haK, haS⟩, _, ⟨hbK, hbS⟩, by rw [mul_inv_cancel_left]⟩

end GlobalTheory.SplitLabel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHyperspecialDoubleCosetOfElementaryDivisorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hyperspecial_doubleCoset_of_elementaryDivisors : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ ϖ' : 𝓞 D.host.E) (d : List ℤ) (α α' : GA D V), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → Formalism.L2.Theta.SuppAt e V α → Formalism.L2.Theta.SuppAt e V α' → DivAt V e (ϖ : D.host.E) d α → DivAt V e (ϖ' : D.host.E) d α' → ∃ a ∈ locPart V (KsphC V ∅) e, ∃ b ∈ locPart V (KsphC V ∅) e, α' = a * α * b := by
  first | exact @GlobalTheory.SplitLabel.split_label | exact GlobalTheory.SplitLabel.split_label | (intros; apply GlobalTheory.SplitLabel.split_label <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.VEqKZeroOfNormOne
noncomputable section

namespace GlobalTheory.UnitK

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

theorem vEqK_zero_of_norm_one : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
    (x : X.G.Kf), ‖E.iK x‖ = 1 → X.vEqK x 0 := by
  intro p _ X hfr E x hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨N, hN⟩ := Formalism.MainNotions.FormalGroupSystem.Pf.exists_rep X hfr hx0

  have hint : ∀ y : X.G.Kf, ‖E.iK y‖ = 1 → y ∈ X.intK := fun y hy =>
    (E.mem_iff y).1 (by rw [mem_OcC]; exact hy.le)
  have h1 : X.vGeK x 0 := (Formalism.MainNotions.FormalGroupSystem.Pf.vGeK_zero_iff X).2 (hint x hx)
  have h2 : X.vGeK x⁻¹ 0 := (Formalism.MainNotions.FormalGroupSystem.Pf.vGeK_zero_iff X).2 (hint x⁻¹ (by rw [map_inv₀, norm_inv, hx, inv_one]))
  have hN1 := (Formalism.MainNotions.FormalGroupSystem.Pf.vGeK_iff_of_rep X hfr hN 0).1 h1
  have hN2 := (Formalism.MainNotions.FormalGroupSystem.Pf.vGeK_iff_of_rep X hfr (Formalism.MainNotions.FormalGroupSystem.Pf.Rep.inv X hN) 0).1 h2
  simp only [zero_mul] at hN1 hN2
  have hN0 : N = 0 := by
    have a : (0 : ℤ) ≤ N := by exact_mod_cast hN1
    have b : (0 : ℤ) ≤ -N := by exact_mod_cast hN2
    omega

  have he : 0 < X.eO := by
    rcases Nat.eq_zero_or_pos X.eO with h0 | h0
    · exfalso
      obtain ⟨u, hu⟩ := X.eO_spec
      rw [h0, pow_zero] at hu

      have hpu : IsUnit (p : X.G.O) := by
        exact IsUnit.of_mul_eq_one _ hu
      obtain ⟨w, hw⟩ := hpu.exists_right_inv
      have hb := E.int w
      have hmul : E.iK (algebraMap X.G.O X.G.Kf (p : X.G.O)) * E.iK (algebraMap X.G.O X.G.Kf w) = 1 := by
        rw [← map_mul, ← map_mul, hw, map_one, map_one]
      have hn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
        have : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
        rw [this, norm_algebraMap', Padic.norm_p]
      rw [map_natCast, map_natCast] at hmul
      have hn2 := congrArg norm hmul
      rw [norm_mul, norm_one, hn] at hn2
      have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
      have hp0 : (0 : ℝ) < p := by linarith
      have : ‖E.iK (algebraMap X.G.O X.G.Kf w)‖ = p := by
        field_simp at hn2
        linarith
      linarith
    · exact h0
  exact (Formalism.MainNotions.FormalGroupSystem.Pf.vEqK_iff_of_rep X hfr hN 0).2 ⟨he, by simp [hN0]⟩

end GlobalTheory.UnitK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgePullHodgeTraceHodgePull
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

set_option autoImplicit false

open Opposite TensorProduct Limits GlobalTheory.Points

noncomputable section
namespace GlobalTheory.GalTrace

theorem preimage_le {Z Y W : Scheme.{0}} {c : Y ⟶ Z} {π : W ⟶ Z} {σ : W ⟶ Y} (hσ : σ ≫ c = π)
    (U : Z.Opens) : π ⁻¹ᵁ U ≤ σ ⁻¹ᵁ (c ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, hσ]

section Forms

variable {k : Type} [CommRing k] {Z Y W : Scheme.{0}} {s : Z ⟶ Sp k} {s' : Y ⟶ Sp k}
  {sW : W ⟶ Sp k} {c : Y ⟶ Z} {π : W ⟶ Z}

def liftPull {σ : W ⟶ Y} (hσ : σ ≫ c = π) (hσs : σ ≫ s' = sW) (j : ℕ) :
    (Scheme.Modules.pushforward c).obj (Omega s' j) ⟶
      (Scheme.Modules.pushforward π).obj (Omega sW j) :=
  (Scheme.Modules.pushforward c).map (omegaPull hσs j) ≫
    (Scheme.Modules.pushforwardComp σ c).hom.app _ ≫
      (Scheme.Modules.pushforwardCongr hσ).hom.app _

theorem liftPull_app (hc : c ≫ s = s') (hπ : π ≫ s = sW) {σ : W ⟶ Y} (hσ : σ ≫ c = π)
    (hσs : σ ≫ s' = sW) (j : ℕ) (U : Z.Opens) (b : Sec s' (c ⁻¹ᵁ U)) (x : OmU s U j) :
    (liftPull hσ hσs j).app U (toOm s' j (c ⁻¹ᵁ U) (b • formPull hc U j x)) =
      toOm sW j (π ⁻¹ᵁ U) (Sec.res sW (preimage_le hσ U) (appSec s' sW σ (c ⁻¹ᵁ U) b) •
        formPull hπ U j x) := by
  change (Omega sW j).presheaf.map (homOfLE (preimage_le hσ U)).op
    ((omegaPull hσs j).val.app (op (c ⁻¹ᵁ U))
      ((toOmega s' j).app (op (c ⁻¹ᵁ U)) (b • formPull hc U j x))) = _
  rw [omegaPull_toOmega]
  refine (res_toOm sW j (preimage_le hσ U) (formPull hσs (c ⁻¹ᵁ U) j (b • formPull hc U j x))).trans
    (congrArg (toOm sW j (π ⁻¹ᵁ U)) ?_)
  have h : (σ ≫ c) ≫ s = sW := by rw [hσ, hπ]
  rw [formPull_smul hσs (c ⁻¹ᵁ U) b (formPull hc U j x), formRes_smul,
    formPull_formPull hc hσs h U j x]
  exact congrArg (_ • ·) (formRes_formPull_congr hσ h hπ U (preimage_le hσ U) j x)

theorem sum_app {F G : Z.Modules} {ι : Type} (R : Finset ι) (φ : ι → (F ⟶ G)) (U : Z.Opens)
    (y : Γ(F, U)) : (∑ r ∈ R, φ r).app U y = ∑ r ∈ R, (φ r).app U y := by
  classical
  induction R using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert a R ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Scheme.Modules.Hom.add_app]
    exact congrArg ((φ a).app U y + ·) ih

variable [IsFinite c] [Etale c] (hc : c ≫ s = s') (hπ : π ≫ s = sW) {ι : Type} (R : Finset ι)
  {σ : ι → (W ⟶ Y)} (hσ : ∀ r, σ r ≫ c = π) (hσs : ∀ r, σ r ≫ s' = sW)

theorem omegaTrace_omegaPull
    (hF : ∀ (U : Z.Opens) (hU : IsAffineOpen U) (b : Sec s' (c ⁻¹ᵁ U)),
      appSec s sW π U (secTrace s s' hU b) =
        ∑ r ∈ R, Sec.res sW (preimage_le (hσ r) U) (appSec s' sW (σ r) (c ⁻¹ᵁ U) b)) (j : ℕ) :
    omegaTrace hc j ≫ omegaPull hπ j = ∑ r ∈ R, liftPull (hσ r) (hσs r) j := by
  refine hom_ext_affine fun U hU y ↦ ?_
  obtain ⟨z, rfl⟩ := toOm_surjective (s := s') (j := j) (hU.preimage c) y
  refine formOm_induction (P := fun z ↦ (omegaTrace hc j ≫ omegaPull hπ j).app U
      (toOm s' j (c ⁻¹ᵁ U) z) = (∑ r ∈ R, liftPull (hσ r) (hσs r) j).app U
        (toOm s' j (c ⁻¹ᵁ U) z)) hc hU ?_ (fun y z hy hz ↦ ?_) (fun b x ↦ ?_) z
  · erw [map_zero, map_zero, map_zero]
  · erw [map_add, map_add, map_add]; exact congrArg₂ (· + ·) hy hz
  · refine Eq.trans ?_ (sum_app R _ U _).symm
    refine Eq.trans ?_ (Finset.sum_congr rfl fun r _ ↦
      liftPull_app hc hπ (hσ r) (hσs r) j U b x).symm
    rw [Scheme.Modules.Hom.comp_app]
    change (omegaPull hπ j).val.app (op U)
      ((omegaTrace hc j).app U (toOm s' j (c ⁻¹ᵁ U) (b • formPull hc U j x))) = _
    rw [omegaTrace_toOm_smul_formPull hc j hU, toOm_apply, omegaPull_toOmega, formPull_smul, hF,
      Finset.sum_smul]
    exact map_sum (toOm sW j (π ⁻¹ᵁ U)) _ _

theorem hodgePull_hodgeTrace (j : ℕ)
    (H : omegaTrace hc j ≫ omegaPull hπ j = ∑ r ∈ R, liftPull (hσ r) (hσs r) j) (q : ℕ)
    (x : hodgeH s' j q) :
    hodgePull hπ j q (hodgeTrace hc j q x) = ∑ r ∈ R, hodgePull (hσs r) j q x := by
  letI := algΓ s; letI := algΓ s'; letI := algΓ sW
  obtain ⟨y, rfl⟩ := (coh.pushforwardEquiv k (appTop_algebraMap hc) (Omega s' j) q).surjective x
  have e1 : hodgeTrace hc j q (coh.pushforwardEquiv k (appTop_algebraMap hc) (Omega s' j) q y) =
      cohOn.map k (omegaTrace hc j) ⊤ q y :=
    congrArg (cohOn.map k (omegaTrace hc j) ⊤ q)
      ((coh.pushforwardEquiv k (appTop_algebraMap hc) (Omega s' j) q).symm_apply_apply y)
  have e2 : ∀ φ : (Scheme.Modules.pushforward c).obj (Omega s' j) ⟶
      (Scheme.Modules.pushforward π).obj (Omega sW j),
      cohOn.pull (σ := RingHom.id k) (appTop_algebraMap hπ) (𝟙 _) (le_refl (π ⁻¹ᵁ ⊤)) q
        (cohOn.map k φ ⊤ q y) =
      cohOn.pull (σ := RingHom.id k) (appTop_algebraMap hπ) φ (le_refl (π ⁻¹ᵁ ⊤)) q y := fun φ ↦ by
    rw [cohOn.pull_map, Category.comp_id]
  have e4 := cohOn.pull_map (σ := RingHom.id k) (appTop_algebraMap hπ)
    (omegaPull hπ j) (omegaTrace hc j) (le_refl (π ⁻¹ᵁ ⊤)) (n := q) y
  have e5 : cohOn.map k (∑ r ∈ R, liftPull (hσ r) (hσs r) j) ⊤ q =
      ∑ r ∈ R, cohOn.map k (liftPull (hσ r) (hσs r) j) ⊤ q :=
    map_sum (cohOn.mapAddHom k _ _ ⊤ q) _ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [H, ← e2, e5, LinearMap.sum_apply, map_sum] at e4
  rw [e1]
  refine e4.trans (Finset.sum_congr rfl fun r _ ↦ (e2 _).trans ?_)
  have h : (σ r ≫ c) ≫ s = sW := by rw [hσ, hπ]
  have s2 := cohOn_pull_pull (appTop_algebraMap hc) (appTop_algebraMap (hσs r))
    (appTop_algebraMap h) (𝟙 _) (omegaPull (hσs r) j) (le_refl (c ⁻¹ᵁ ⊤)) (le_refl _) (le_refl _) q y
  have s3 := cohOn_pull_congr (hσ r) (appTop_algebraMap h) (appTop_algebraMap hπ)
    (G := Omega sW j) (𝟙 ((Scheme.Modules.pushforward c).obj (Omega s' j)) ≫
      (Scheme.Modules.pushforward c).map (omegaPull (hσs r) j) ≫
        (Scheme.Modules.pushforwardComp (σ r) c).hom.app _)
    (V := ⊤) (W := σ r ⁻¹ᵁ (c ⁻¹ᵁ ⊤)) (le_refl _) (fun _ _ ↦ trivial) q y
  have hm : liftPull (hσ r) (hσs r) j = (𝟙 ((Scheme.Modules.pushforward c).obj (Omega s' j)) ≫
      (Scheme.Modules.pushforward c).map (omegaPull (hσs r) j) ≫
        (Scheme.Modules.pushforwardComp (σ r) c).hom.app _) ≫
          (Scheme.Modules.pushforwardCongr (hσ r)).hom.app _ := by
    simp [liftPull]
  rw [hm]
  exact s3.symm.trans s2.symm

end Forms

end GlobalTheory.GalTrace
end
end

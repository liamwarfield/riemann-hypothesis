module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsImEqLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCoefficientChangeCompare
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory.BlochKatoBaseChangeLe

open Formalism.WeaklyAdmissibleFiltrations GlobalTheory.TwistedSelmerCompare

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O₀ O : Type} [CommRing O₀] [IsDomain O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]

theorem mem_HfD_gen {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} [TopologicalSpace G]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    (L : Lattice (O := O) ρ) (w : G → V ⧸ L.T) :
    w ∈ HfD PD L ↔ ∃ z ∈ finiteCocycles PD ρ, ∃ m : V, ∀ g, w g = Submodule.Quotient.mk (z g + (ρ g m - m)) := by
  constructor
  · intro h
    obtain ⟨_, ⟨z, hz, rfl⟩, _, ⟨x, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨z, hz, m, fun g => rfl⟩
  · rintro ⟨z, hz, m, h⟩
    refine Submodule.mem_sup.2 ⟨_, ⟨z, hz, rfl⟩, _, ⟨Submodule.Quotient.mk m, rfl⟩, ?_⟩
    funext g
    exact (h g).symm


set_option synthInstance.maxHeartbeats 400000 in
omit [IsDomain O] in
theorem mem_HfD_iff (B : LocBridge l E Ω Gw O) {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (w : ↥(GK B.Kw) → (Fin k → Br.LLw B) ⧸ stdG (Br.Ow B) (Br.LLw B) k) :
    w ∈ HfD (P.PD B.Kw) (Br.lat B M) ↔
      ∃ z ∈ finiteCocycles (P.PD B.Kw) (matRep (Br.locM B M)), ∃ m : Fin k → Br.LLw B, ∀ g,
        w g = Submodule.Quotient.mk (z g + ((Br.locM B M g).mulVec m - m)) :=
  mem_HfD_gen (P.PD B.Kw) (Br.lat B M) w


set_option synthInstance.maxHeartbeats 400000 in
def transport (B : LocBridge l E Ω Gw O) (k : ℕ) :
    (↥Gw → KOG O k) →ₛₗ[B.eO.toRingHom]
      (↥(GK B.Kw) → (Fin k → Br.LLw B) ⧸ stdG (Br.Ow B) (Br.LLw B) k) where
  toFun c g := Br.phi B k (c (Br.ι B g))
  map_add' a b := by
    funext g
    exact (Br.phi B k).map_add _ _
  map_smul' c a := by
    funext g
    exact (Br.phi B k).map_smulₛₗ c _

theorem locM_apply (B : LocBridge l E Ω Gw O) {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (g : ↥(GK B.Kw)) (i j : Fin k) :
    Br.locM B M g i j = Br.toLLK B (algebraMap O (FractionRing O) (M (Br.ι B g) i j)) := by
  rw [Br.toLLK_alg]; rfl

theorem vecS_mulVec (B : LocBridge l E Ω Gw O) {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (g : ↥(GK B.Kw)) (u : Fin k → FractionRing O) :
    Br.vecS B k ((mapM (algebraMap O (FractionRing O)) M (Br.ι B g)).mulVec u) =
      (Br.locM B M g).mulVec (Br.vecS B k u) := by
  funext i
  change Br.toLLK B (∑ j, algebraMap O (FractionRing O) (M (Br.ι B g) i j) * u j) =
    ∑ j, Br.locM B M g i j * Br.toLLK B (u j)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, locM_apply]


set_option synthInstance.maxHeartbeats 400000 in
theorem phi_mem_of_mem_bkG (B : LocBridge l E Ω Gw O) {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (c : ↥(Z1 (WKG M))) (hc : Submodule.Quotient.mk c ∈ Br.bkG B P (WKG M) M) :
    Br.Phi B (WKG M) c ∈ HfD (P.PD B.Kw) (Br.lat B M) := by
  obtain ⟨c₁, h₁, he⟩ := hc
  have he' : c₁ - c ∈ (ReciprocityTheory.Gal.B1 (WKG M)).comap (Z1 (WKG M)).subtype :=
    (Submodule.Quotient.eq _).1 he
  obtain ⟨x, hx⟩ := (mem_coboundaries1 _ _).1 he'
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hB : Br.Phi B (WKG M) (c₁ - c) ∈ HfD (P.PD B.Kw) (Br.lat B M) := by
    refine (mem_HfD_iff P B M _).2 ⟨0, Submodule.zero_mem _, Br.vecS B k u, fun g => ?_⟩
    have := congrArg (Br.phi B k) (hx (Br.ι B g))
    refine this.trans ?_
    rw [Pi.zero_apply, zero_add, ← vecS_mulVec, ← map_sub]
    rfl
  have h2 : c = c₁ - (c₁ - c) := by abel
  rw [h2, map_sub]
  exact Submodule.sub_mem _ h₁ hB


set_option synthInstance.maxHeartbeats 400000 in
theorem push_mem (B₀ : LocBridge l E Ω Gw O₀) (B : LocBridge l E Ω Gw O) (σ : GQ l)
    (hσ : ∀ g : ↥Gw, ((B.e g : ↥(GK B.Kw)) : GQ l) = σ * ((B₀.e g : ↥(GK B₀.Kw)) : GQ l) * σ⁻¹)
    (f : O₀ →+* O) (hf : Function.Injective f)
    (hz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z) {k : ℕ}
    (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀) (c₀ : ↥Gw → KOG O₀ k)
    (hc : (fun g => Br.phi B₀ k (c₀ (Br.ι B₀ g))) ∈ HfD (P.PD B₀.Kw) (Br.lat B₀ M₀)) :
    (fun g => Br.phi B k (pushKO f hf k (c₀ (Br.ι B g)))) ∈ HfD (P.PD B.Kw) (Br.lat B (mapM f M₀)) := by
  obtain ⟨φ, hφ⟩ := exists_coefMap B₀ B f hf hz
  obtain ⟨z, hzf, m, h⟩ := (mem_HfD_iff P B₀ M₀ _).1 hc
  let θ : ↥(GK B.Kw) →* ↥(GK B₀.Kw) := B₀.e.toMonoidHom.comp (Br.ι B)
  have hθι : ∀ g, Br.ι B₀ (θ g) = Br.ι B g := fun g => B₀.e.symm_apply_apply _
  have hθ : Continuous θ := B₀.e_cont.comp (Br.ι_cont B)
  have hσ' : ∀ g : ↥(GK B.Kw), (g : GQ l) = σ * (θ g : GQ l) * σ⁻¹ := fun g => by
    have := hσ (Br.ι B g)
    rwa [show B.e (Br.ι B g) = g from B.e.apply_symm_apply g] at this
  have hp : ∀ g (v : Fin k → ↥B₀.LL.1), (fun j => φ ((Br.locM B₀ M₀ (θ g)).mulVec v j)) =
      (Br.locM B (mapM f M₀) g).mulVec fun j => φ (v j) := by
    intro g v
    funext i
    change φ (∑ j, Br.locM B₀ M₀ (θ g) i j * v j) = ∑ j, Br.locM B (mapM f M₀) g i j * φ (v j)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, locM_apply, hφ, fracMap_alg, hθι]
    rfl
  refine (mem_HfD_iff P B _ _).2 ⟨_, crystallineCocycle_transport_conjugation P B₀.Kw B.Kw B₀.LL B.LL θ hθ σ hσ' _ _ φ.toLinearMap hp z hzf,
    fun j => φ (m j), fun g => ?_⟩
  have hg := h (θ g)
  simp only [hθι] at hg
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (c₀ (Br.ι B g))
  rw [← hu] at hg ⊢
  obtain ⟨n, hn⟩ : Br.vecS B₀ k u - (z (θ g) + ((Br.locM B₀ M₀ (θ g)).mulVec m - m)) ∈
      stdG (Br.Ow B₀) (Br.LLw B₀) k := (Submodule.Quotient.eq _).1 hg
  refine (Submodule.Quotient.eq (stdG (Br.Ow B) (Br.LLw B) k)).2
    ⟨fun j => B.eO (f (B₀.eO.symm (n j))), ?_⟩
  funext j
  have h1 := congrArg φ (congrFun hn j)
  have h2 : algebraMap (Br.Ow B₀) (Br.LLw B₀) (n j) =
      Br.toLLK B₀ (algebraMap O₀ (FractionRing O₀) (B₀.eO.symm (n j))) := by
    rw [Br.toLLK_alg, RingEquiv.apply_symm_apply]
  change φ (algebraMap (Br.Ow B₀) (Br.LLw B₀) (n j)) =
    φ (Br.toLLK B₀ (u j) - (z (θ g) j + ((Br.locM B₀ M₀ (θ g)).mulVec m j - m j))) at h1
  rw [h2, hφ, fracMap_alg, Br.toLLK_alg, map_sub, map_add (f := _), map_sub, hφ, congrFun (hp g m) j] at h1
  exact h1


set_option synthInstance.maxHeartbeats 400000 in
theorem extCond_le_bkG : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O₀ O : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra ℤ_[l] O₀] [Module.Finite ℤ_[l] O₀] [TopologicalSpace O₀] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] (B₀ : LocBridge l E Ω Gw O₀) (B : LocBridge l E Ω Gw O) (σ : GQ l), (∀ g : ↥Gw, ((B.e g : ↥(GK B.Kw)) : GQ l) = σ * ((B₀.e g : ↥(GK B₀.Kw)) : GQ l) * σ⁻¹) → ∀ (f : O₀ →+* O) (hf : Function.Injective f), (∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z) → ∀ (k : ℕ) (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀), extCond f hf (WKG M₀) (Br.bkG B₀ P (WKG M₀) M₀) (WKG (mapM f M₀)) ≤ Br.bkG B P (WKG (mapM f M₀)) (mapM f M₀) := by
  intro l _ P E Ω _ _ _ Gw O₀ O _ _ _ _ _ _ _ _ _ _ _ _ B₀ B σ hσ f hf hz k M₀
  refine Submodule.map_mono ?_
  intro c hc
  have key : Submodule.span O {c : ↥Gw → KOG O k | ∃ c₀ : Z1 (WKG M₀),
      Submodule.Quotient.mk c₀ ∈ Br.bkG B₀ P (WKG M₀) M₀ ∧
      c = fun g => pushKO f hf k ((c₀ : ↥Gw → KOG O₀ k) g)} ≤
      (HfD (P.PD B.Kw) (Br.lat B (mapM f M₀))).comap (transport B k) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c₀, h₀, rfl⟩
    exact push_mem P B₀ B σ hσ f hf hz M₀ c₀ (phi_mem_of_mem_bkG P B₀ M₀ c₀ h₀)
  exact key hc

end GlobalTheory.BlochKatoBaseChangeLe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMatrixUnitStableSubspaceOfExtremal
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMatrixUnitStableSubspaceOfExtremal
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.ExtremalGen

open GlobalTheory.TensorHW (mem_wt diag_comm)

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def Supp (S : Ix p q → Ix p q → Prop) (Z : Mat p q) : Prop := ∀ a b, ¬ S a b → Z a b = 0

lemma supp_Eab {S : Ix p q → Ix p q → Prop} {a b : Ix p q} (h : S a b) : Supp S (Eab a b) := by
  intro c d hcd
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd h

lemma supp_mul {S : Ix p q → Ix p q → Prop} (hS : Equivalence S) {Y Z : Mat p q}
    (hY : Supp S Y) (hZ : Supp S Z) : Supp S (Y * Z) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hac : S a c
  · rw [hZ c b (fun hcb => hab (hS.trans hac hcb)), mul_zero]
  · rw [hY a c hac, zero_mul]

lemma supp_comm {S : Ix p q → Ix p q → Prop} (hS : Equivalence S) {Y Z : Mat p q}
    (hY : Supp S Y) (hZ : Supp S Z) : Supp S (Y * Z - Z * Y) := by
  intro a b hab
  rw [Matrix.sub_apply, supp_mul hS hY hZ a b hab, supp_mul hS hZ hY a b hab, sub_zero]

lemma supp_ind {S : Ix p q → Ix p q → Prop} (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (N : Submodule ℂ V) (y : V)
    (h : ∀ a b, S a b → act (Eab a b) y ∈ N) {Z : Mat p q} (hZ : Supp S Z) : act Z y ∈ N := by
  rw [Matrix.matrix_eq_sum_single Z]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply]
  refine N.sum_mem fun a _ => N.sum_mem fun b _ => ?_
  by_cases hab : S a b
  · have : (Matrix.single a b (Z a b) : Mat p q) = Z a b • Eab a b := by
      rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, LinearMap.smul_apply]
    exact N.smul_mem _ (h a b hab)
  · rw [hZ a b hab]
    simp

lemma lie_apply {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (Y Z : Mat p q) (y : V) :
    act Y (act Z y) = act Z (act Y y) + act (Y * Z - Z * Y) y := by
  rw [hL Y Z]
  simp

lemma eig_shift {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (c : Ix p q → ℂ)
    (a b : Ix p q) {t : ℂ} {y : V}
    (hy : y ∈ Module.End.eigenspace (act (Matrix.diagonal c)) t) :
    act (Eab a b) y ∈ Module.End.eigenspace (act (Matrix.diagonal c)) (t + (c a - c b)) := by
  rw [Module.End.mem_eigenspace_iff] at hy ⊢
  rw [lie_apply hL, diag_comm, hy, map_smul, map_smul, LinearMap.smul_apply, add_smul]

lemma eig_of_wt {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (c : Ix p q → ℂ) {μ : Ix p q → ℚ} {v : V}
    (hv : v ∈ wtSub act μ) :
    v ∈ Module.End.eigenspace (act (Matrix.diagonal c)) (∑ a, c a * ((μ a : ℚ) : ℂ)) := by
  rw [mem_wt] at hv
  rw [Module.End.mem_eigenspace_iff]
  have : (Matrix.diagonal c : Mat p q) = ∑ a, c a • Eab a a := by
    ext i j
    simp only [Matrix.sum_apply, Eab, Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  rw [this]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hv, Finset.sum_smul,
    mul_smul]

theorem exists_generated :
    ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (S : Ix p q → Ix p q → Prop), Equivalence S → ∀ (r : Ix p q → ℕ), Function.Injective r → ∀ (μ : Ix p q → ℚ) (v : V), v ∈ wtSub act μ → (∀ a b, S a b → r a < r b → act (Eab a b) v = 0) → ∃ U : Submodule ℂ V, v ∈ U ∧ (∀ a b, S a b → ∀ x ∈ U, act (Eab a b) x ∈ U) ∧ (∀ U' : Submodule ℂ V, v ∈ U' → (∀ a b, S a b → r a < r b → ∀ x ∈ U', act (Eab b a) x ∈ U') → U ≤ U') ∧ (∀ x ∈ U, x ∈ wtSub act μ → ∃ c : ℂ, x = c • v) ∧ ∀ (ν : Ix p q → ℚ), ∀ x ∈ U, x ≠ 0 → x ∈ wtSub act ν → ν = μ ∨ ∑ a, (r a : ℚ) * μ a < ∑ a, (r a : ℚ) * ν a := by
  intro p q V _ _ act hL S hS r hr μ v hv hup
  have hv' := mem_wt.1 hv
  set F : Set (Submodule ℂ V) :=
    {N | v ∈ N ∧ ∀ a b, S a b → r a < r b → ∀ y ∈ N, act (Eab b a) y ∈ N} with hF
  have hG : sInf F ∈ F := by
    refine ⟨Submodule.mem_sInf.2 fun M hM => hM.1, fun a b hab hlt y hy => ?_⟩
    exact Submodule.mem_sInf.2 fun M hM => hM.2 a b hab hlt y (Submodule.mem_sInf.1 hy M hM)
  have hG' : (sInf F ⊓ ⨅ (Z : Mat p q) (_ : Supp S Z), (sInf F).comap (act Z)) ∈ F := by
    constructor
    · simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
      refine ⟨hG.1, fun Z hZ => supp_ind act _ v (fun a b hab => ?_) hZ⟩
      rcases lt_trichotomy (r a) (r b) with h | h | h
      · rw [hup a b hab h]; exact Submodule.zero_mem _
      · obtain rfl := hr h
        rw [hv']; exact Submodule.smul_mem _ _ hG.1
      · exact hG.2 b a (hS.symm hab) h v hG.1
    · intro a b hab hlt y hy
      simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hy ⊢
      refine ⟨hG.2 a b hab hlt y hy.1, fun Z hZ => ?_⟩
      have hE := supp_Eab (hS.symm hab)
      rw [lie_apply hL]
      exact Submodule.add_mem _ (hG.2 a b hab hlt _ (hy.2 Z hZ)) (hy.2 _ (supp_comm hS hZ hE))
  set c : Ix p q → ℂ := fun a => (r a : ℂ) with hc
  set h : Module.End ℂ V := act (Matrix.diagonal c) with hh
  have hcast : ∀ ν : Ix p q → ℚ,
      ∑ a, c a * ((ν a : ℚ) : ℂ) = ((∑ a, (r a : ℚ) * ν a : ℚ) : ℂ) := by
    intro ν; simp [hc]
  have heig : ∀ (ν : Ix p q → ℚ) (x : V), x ∈ wtSub act ν →
      x ∈ h.eigenspace ((∑ a, (r a : ℚ) * ν a : ℚ) : ℂ) := by
    intro ν x hx
    rw [← hcast]; exact eig_of_wt c hx
  set m : ℚ := ∑ a, (r a : ℚ) * μ a with hm
  have hvm : v ∈ h.eigenspace (m : ℂ) := heig μ v hv
  set Q : Submodule ℂ V := ⨆ (t : ℚ) (_ : m < t), h.eigenspace (t : ℂ) with hQ
  have hshift : ∀ a b, r a < r b → ∀ t : ℚ, m ≤ t →
      ∀ y ∈ h.eigenspace (t : ℂ), act (Eab b a) y ∈ Q := by
    intro a b hab t ht y hy
    have h1 := eig_shift hL c b a hy
    have h2 : (t : ℂ) + (c b - c a) = ((t + ((r b : ℚ) - (r a : ℚ)) : ℚ) : ℂ) := by simp [hc]
    rw [h2] at h1
    have h3 : (r a : ℚ) < r b := by exact_mod_cast hab
    exact (le_iSup₂_of_le (f := fun (t : ℚ) (_ : m < t) => h.eigenspace (t : ℂ)) _
      (by linarith) le_rfl : _ ≤ Q) h1
  have hlow : ∀ a b, r a < r b → ∀ y ∈ (ℂ ∙ v) ⊔ Q, act (Eab b a) y ∈ Q := by
    intro a b hab
    have : (ℂ ∙ v) ⊔ Q ≤ Q.comap (act (Eab b a)) := by
      refine sup_le ?_ (iSup₂_le fun t ht y hy => hshift a b hab t ht.le y hy)
      rw [Submodule.span_singleton_le_iff_mem]
      exact hshift a b hab m le_rfl v hvm
    exact this
  have hle : sInf F ≤ (ℂ ∙ v) ⊔ Q :=
    sInf_le ⟨Submodule.mem_sup_left (Submodule.mem_span_singleton_self v),
      fun a b _ hab y hy => Submodule.mem_sup_right (hlow a b hab y hy)⟩
  have hQle : ∀ n : ℚ, n ≤ m → Q ≤ ⨆ (j : ℂ) (_ : j ≠ (n : ℂ)), h.eigenspace j := by
    intro n hn
    refine iSup₂_le fun t ht => le_iSup₂_of_le (t : ℂ) ?_ le_rfl
    intro he
    have : t = n := by exact_mod_cast he
    linarith
  have hline : ∀ x ∈ sInf F, x ∈ h.eigenspace (m : ℂ) → ∃ s : ℂ, x = s • v := by
    intro x hx hxm
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hle hx)
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hzm : z ∈ h.eigenspace (m : ℂ) := by
      have := Submodule.sub_mem _ hxm (Submodule.smul_mem _ s hvm)
      simpa using this
    have hz0 : z = 0 :=
      Submodule.disjoint_def.1 (Module.End.eigenspaces_iSupIndep h (m : ℂ)) z hzm
        (hQle m le_rfl hz)
    exact ⟨s, by rw [hz0, add_zero]⟩
  refine ⟨sInf F, hG.1, fun a b hab x hx => ?_, fun U' h1 h2 => sInf_le ⟨h1, h2⟩,
    fun x hx hxμ => hline x hx (heig μ x hxμ), fun ν x hx hx0 hxν => ?_⟩
  · have := sInf_le hG' hx
    simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at this
    exact this.2 _ (supp_Eab hab)
  · have hxn := heig ν x hxν
    set n : ℚ := ∑ a, (r a : ℚ) * ν a with hn
    rcases lt_trichotomy m n with hlt | heq | hgt
    · exact Or.inr hlt
    · left
      rw [← heq] at hxn
      obtain ⟨s, hs⟩ := hline x hx hxn
      have hxμ : x ∈ wtSub act μ := hs ▸ Submodule.smul_mem _ s hv
      funext a
      have h1 := mem_wt.1 hxν a
      rw [mem_wt.1 hxμ a] at h1
      have h2 := smul_left_injective ℂ hx0 h1
      exact_mod_cast h2.symm
    · exfalso
      apply hx0
      refine Submodule.disjoint_def.1 (Module.End.eigenspaces_iSupIndep h (n : ℂ)) x hxn ?_
      refine (sup_le ?_ (hQle n hgt.le) : (ℂ ∙ v) ⊔ Q ≤ _) (hle hx)
      rw [Submodule.span_singleton_le_iff_mem]
      have hne : (m : ℂ) ≠ (n : ℂ) := by exact_mod_cast hgt.ne'
      exact (le_iSup₂_of_le (f := fun (j : ℂ) (_ : j ≠ (n : ℂ)) => h.eigenspace j) (m : ℂ) hne
        le_rfl : _ ≤ _) hvm

end GlobalTheory.ExtremalGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMatrixUnitStableSubspaceOfExtremalStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrixUnit_stable_subspace_of_extremal : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (S : Ix p q → Ix p q → Prop), Equivalence S → ∀ (r : Ix p q → ℕ), Function.Injective r → ∀ (μ : Ix p q → ℚ) (v : V), v ∈ wtSub act μ → (∀ a b, S a b → r a < r b → act (Eab a b) v = 0) → ∃ U : Submodule ℂ V, v ∈ U ∧ (∀ a b, S a b → ∀ x ∈ U, act (Eab a b) x ∈ U) ∧ (∀ U' : Submodule ℂ V, v ∈ U' → (∀ a b, S a b → r a < r b → ∀ x ∈ U', act (Eab b a) x ∈ U') → U ≤ U') ∧ (∀ x ∈ U, x ∈ wtSub act μ → ∃ c : ℂ, x = c • v) ∧ ∀ (ν : Ix p q → ℚ), ∀ x ∈ U, x ≠ 0 → x ∈ wtSub act ν → ν = μ ∨ ∑ a, (r a : ℚ) * μ a < ∑ a, (r a : ℚ) * ν a := by
  first | exact @GlobalTheory.ExtremalGen.exists_generated | exact GlobalTheory.ExtremalGen.exists_generated | (intros; apply GlobalTheory.ExtremalGen.exists_generated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AreaBoundedOfDiscrEqOne
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators UpperHalfPlane Real

namespace GlobalTheory.LatticeAreaBound

theorem eisG_eq_G (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) {k : ℕ}
    (hk : k ≠ 0) : eisG Λ k = L.G (2 * k) := by
  have h1 := tsum_subtype {w : ℂ | w ∈ Λ ∧ w ≠ 0} fun w : ℂ => (w ^ (2 * k))⁻¹
  have h2 := tsum_subtype (L.lattice : Set ℂ) fun w : ℂ => (w ^ (2 * k))⁻¹
  simp only [eisG, PeriodPair.G, one_div]
  refine h1.trans (Eq.trans (tsum_congr fun w => ?_) h2.symm)
  rcases eq_or_ne w 0 with rfl | hw
  · simp [Set.indicator, hk]
  · simp [Set.indicator, hw, h]

theorem discr_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    TaylorLogMetric.discr Λ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
  rw [TaylorLogMetric.discr, g2, g3, eisG_eq_G L Λ h (by norm_num), eisG_eq_G L Λ h (by norm_num)]
  rfl

theorem area_eq {Λ : AddSubgroup ℂ} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ Λ ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) :
    area Λ = ‖a‖ ^ 2 * τ.im := by
  have hy := τ.im_pos
  have hn := norm_pos_iff.2 ha
  have hA : 0 < ‖a‖ ^ 2 * τ.im := by positivity
  have key : ∀ m n m' n' : ℤ,
      ((starRingEnd ℂ) (a * (m * (τ : ℂ) + n)) * (a * (m' * (τ : ℂ) + n'))).im
        = ((n * m' - m * n' : ℤ) : ℝ) * (‖a‖ ^ 2 * τ.im) := fun m n m' n' => by
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  refine IsLeast.csInf_eq ⟨⟨hA, _, (h _).2 ⟨0, 1, rfl⟩, _, (h _).2 ⟨1, 0, rfl⟩, ?_⟩, ?_⟩
  · rw [key, abs_of_nonneg (by simpa using hA.le)]
    simp
  · rintro b ⟨hb, w₁, h₁, w₂, h₂, rfl⟩
    obtain ⟨m, n, rfl⟩ := (h _).1 h₁
    obtain ⟨m', n', rfl⟩ := (h _).1 h₂
    rw [key, abs_mul, abs_of_pos hA] at hb ⊢
    have h0 : n * m' - m * n' ≠ 0 := fun e => by simp [e] at hb
    have h1 : (1 : ℝ) ≤ |((n * m' - m * n' : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs h0
    exact le_mul_of_one_le_left hA.le h1

theorem exists_bound_discriminant :
    ∃ C : ℝ, ∀ τ : ℍ, τ.im ^ 6 * ‖ModularForm.discriminant τ‖ ≤ C := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound CuspForm.discriminant
  refine ⟨C, fun τ => ?_⟩
  have h := hC τ
  have hy := τ.im_pos
  rw [CuspForm.coe_discriminant, show (((12 : ℤ) : ℝ) / 2 : ℝ) = ((6 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, le_div_iff₀ (by positivity)] at h
  rwa [mul_comm]

theorem area_bounded_of_discr_eq_one : ∃ C : ℝ, 0 < C ∧ ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → TaylorLogMetric.discr Λ = 1 → 0 < area Λ ∧ area Λ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_discriminant
  refine ⟨max 1 ((2 * π) ^ 12 * C), lt_max_of_lt_left one_pos, ?_⟩
  rintro Λ ⟨w₁, w₂, hi, rfl⟩ hd
  let L : PeriodPair := ⟨w₁, w₂, hi⟩
  have hL : ∀ z, z ∈ AddSubgroup.closure {w₁, w₂} ↔ z ∈ L.lattice := fun z => by
    rw [AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp [L]
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  have hy := τ.im_pos
  have hn := norm_pos_iff.2 ha
  rw [area_eq ha fun x => (hL x).trans (h x)]
  rw [discr_eq L _ hL, ← latticeCurve_Δ, latticeCurve_Δ_eq_discriminant ha h] at hd
  have e := congrArg norm hd
  rw [norm_mul, norm_pow, norm_div, show ‖(2 * π : ℂ)‖ = 2 * π by simp [Real.pi_pos.le],
    norm_one, div_pow, div_mul_eq_mul_div, div_eq_one_iff_eq (by positivity)] at e
  have hb : (‖a‖ ^ 2 * τ.im) ^ 6 ≤ (2 * π) ^ 12 * C := by
    calc (‖a‖ ^ 2 * τ.im) ^ 6 = ‖a‖ ^ 12 * τ.im ^ 6 := by ring
      _ = (2 * π) ^ 12 * (τ.im ^ 6 * ‖ModularForm.discriminant τ‖) := by rw [← e]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hC τ) (by positivity)
  refine ⟨by positivity, ?_⟩
  rcases le_total (‖a‖ ^ 2 * τ.im) 1 with h1 | h1
  · exact le_max_of_le_left h1
  · exact le_max_of_le_right ((le_self_pow₀ h1 (by norm_num)).trans hb)

end GlobalTheory.LatticeAreaBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormJetExpNegMulLe
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ExpJets

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem expPS_eq_subst (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 0) :
    expPS F = (PowerSeries.exp ℂ_[p]).subst F := by
  ext n
  rw [PowerSeries.coeff_subst' (HasSubst.of_constantCoeff_zero' hF), expPS, coeff_mk,
    finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [PowerSeries.coeff_exp, div_eq_inv_mul]
  · intro k hk
    by_contra h
    apply hk
    have hlt : n < k := by simpa using h
    have h0 : coeff n (F ^ k) = 0 := by
      have : (X : PowerSeries ℂ_[p]) ^ k ∣ F ^ k := pow_dvd_pow_of_dvd (X_dvd_iff.2 hF) k
      exact X_pow_dvd_iff.1 this n hlt
    simp [h0]

theorem derivative_expPS (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 0) :
    d⁄dX (expPS F) = expPS F * d⁄dX F := by
  rw [expPS_eq_subst F hF, PowerSeries.derivative_subst (HasSubst.of_constantCoeff_zero' hF),
    PowerSeries.derivative_exp]

theorem norm_jet_mul_le (A B : PowerSeries ℂ_[p]) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ i j, i + j = n →
      ‖(i.factorial : ℂ_[p]) * coeff i A‖ * ‖(j.factorial : ℂ_[p]) * coeff j B‖ ≤ C) :
    ‖(n.factorial : ℂ_[p]) * coeff n (A * B)‖ ≤ C := by
  rw [coeff_mul, Finset.mul_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun x hx => ?_
  obtain ⟨i, j⟩ := x
  have hij : i + j = n := by simpa using hx
  have e : (n.factorial : ℂ_[p]) * (coeff i A * coeff j B) =
      (((i + j).choose j : ℕ) : ℂ_[p]) *
        (((i.factorial : ℂ_[p]) * coeff i A) * ((j.factorial : ℂ_[p]) * coeff j B)) := by
    rw [← hij, ← Nat.add_choose_mul_factorial_mul_factorial i j]
    push_cast
    ring
  simp only
  rw [e, norm_mul, norm_mul]
  have h1 : ‖(((i + j).choose j : ℕ) : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
  calc _ ≤ 1 * C := mul_le_mul h1 (h i j hij) (by positivity) zero_le_one
    _ = C := one_mul C

theorem jet_derivative (A : PowerSeries ℂ_[p]) (n : ℕ) :
    (n.factorial : ℂ_[p]) * coeff n (d⁄dX A) =
      ((n + 1).factorial : ℂ_[p]) * coeff (n + 1) A := by
  rw [PowerSeries.coeff_derivative, Nat.factorial_succ]
  push_cast
  ring

theorem norm_jet_expPS_le (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 0) (s : ℝ)
    (hs : 0 ≤ s) (h : ∀ n : ℕ, ‖(n.factorial : ℂ_[p]) * coeff n F‖ ≤ s ^ n) (n : ℕ) :
    ‖(n.factorial : ℂ_[p]) * coeff n (expPS F)‖ ≤ s ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [expPS]
    | succ n =>
      rw [← jet_derivative, derivative_expPS F hF]
      refine norm_jet_mul_le _ _ n _ (by positivity) fun i j hij => ?_
      rw [jet_derivative, ← hij, add_assoc, pow_add]
      exact mul_le_mul (ih i (by omega)) (h (j + 1)) (norm_nonneg _) (by positivity)

theorem norm_jet_exp_neg_mul_le : ∀ (p : ℕ) [Fact p.Prime] (ph : PowerSeries ℂ_[p]) (s : ℝ), 1 ≤ s → PowerSeries.constantCoeff ph = 0 → (∀ i, i ≠ 2 → ‖(i.factorial : ℂ_[p]) * PowerSeries.coeff i ph‖ ≤ 1) → ‖(2 : ℂ_[p]) * PowerSeries.coeff 2 ph‖ ≤ s ^ 2 → ∀ (f : PowerSeries ℂ_[p]), (∀ n : ℕ, ‖(n.factorial : ℂ_[p]) * PowerSeries.coeff n f‖ ≤ 1) → ∀ n : ℕ, ‖(n.factorial : ℂ_[p]) * PowerSeries.coeff n (expPS (-ph) * f)‖ ≤ s ^ n := by
  intro p _ ph s hs h0 h1 h2 f hf n
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have hE := norm_jet_expPS_le (-ph) (by simp [h0]) s hs0 fun m => by
    rw [map_neg, mul_neg, norm_neg]
    by_cases hm : m = 2
    · subst hm
      simpa using h2
    · exact (h1 m hm).trans (one_le_pow₀ hs)
  refine norm_jet_mul_le _ _ n _ (by positivity) fun i j hij => ?_
  rw [← hij, pow_add]
  exact mul_le_mul (hE i) ((hf j).trans (one_le_pow₀ hs)) (norm_nonneg _) (by positivity)

end GlobalTheory.ExpJets
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaFunctionSelfDualExistsEqSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaFunctionSelfDualExistsEqSmul
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaCoordLine

open Matrix
open scoped ComplexOrder

noncomputable def coordEquiv (D : D7) (N N' g : ℕ) (e : D.what₂.Tau × Fin N' × Fin N ≃ Fin g) :
    (Fin g → ℂ) ≃L[ℂ] VC D N N' :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun w τ i j => w (e (τ, i, j))
      invFun := fun z k => z (e.symm k).1 (e.symm k).2.1 (e.symm k).2.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun w => by ext k; simp
      right_inv := fun z => by ext τ i j; simp }

theorem Hf_coordEquiv (D : D7) (T : Tor D) (N N' g : ℕ) (e : D.what₂.Tau × Fin N' × Fin N ≃ Fin g)
    (z a : Fin g → ℂ) :
    star a ⬝ᵥ ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).mulVec z =
      Hf D T (coordEquiv D N N' g e z) (coordEquiv D N N' g e a) := by
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, Hf, dotProduct,
    ← e.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  exact mul_comm _ _

theorem norm_al (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') : ‖al D T x‖ = 1 := by
  simp [al, norm_zpow]

theorem transl_of_mem (D : D7) (T : Tor D) {N N' : ℕ} {A : AddSubgroup (VC D N N')}
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T A) {x : VC D N N'} (hx : x ∈ A) (z : VC D N N') :
    G (z + x) = (al D T x)⁻¹ * Complex.exp (Real.pi * Hf D T z x + Real.pi / 2 * Hf D T x x) * G z := by
  have h := hG.2 x hx z
  have h0 : al D T x ≠ 0 := fun h => by simpa [h] using norm_al D T x
  have h1 : Complex.exp (Real.pi * Hf D T z x + Real.pi / 2 * Hf D T x x) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; ring
  rw [← h, U]
  have h2 := inv_mul_cancel₀ h0
  linear_combination (-(G (z + x)) * (Complex.exp (Real.pi * Hf D T z x + Real.pi / 2 * Hf D T x x) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2))) * h2 - G (z + x) * h1

theorem exists_eq_smul : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), 0 < area T.abelian₂ → DiscreteTopology A → (∀ x, x ∈ A ↔ ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) → ∀ F ∈ ThSp D T A, ∀ G ∈ ThSp D T A, G ≠ 0 → ∃ c : ℂ, F = c • G := by
  intro D T N N' A ha hd hA F hF G hG h0
  let e := Fintype.equivFin (D.what₂.Tau × Fin N' × Fin N)
  set g := Fintype.card (D.what₂.Tau × Fin N' × Fin N)
  let L := coordEquiv D N N' g e
  have hH : ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (inv_pos.2 ha)
  let Λ : AddSubgroup (Fin g → ℂ) := A.comap L.toLinearEquiv.toAddEquiv.toAddMonoidHom
  have hΛ : ∀ a, a ∈ Λ ↔ L a ∈ A := fun a => Iff.rfl
  haveI : DiscreteTopology Λ :=
    DiscreteTopology.of_continuous_injective (f := fun a : Λ => (⟨L a, a.2⟩ : A))
      (Continuous.subtype_mk (L.continuous.comp continuous_subtype_val) _)
      (fun a b h => Subtype.ext (L.injective (congrArg Subtype.val h)))
  have hsw : ∀ v a, (star v ⬝ᵥ ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).mulVec a).im =
      -(Hf D T (L v) (L a)).im := fun v a => by
    rw [ThetaTranslSpan.herm_swap hH, Hf_coordEquiv D T N N' g e]; simp [L]
  have htr : ∀ P ∈ ThSp D T A, ∀ a ∈ Λ, ∀ z, (P ∘ L) (z + a) = (al D T (L a))⁻¹ * Complex.exp
      (Real.pi * (star a ⬝ᵥ ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).mulVec z) +
        Real.pi / 2 * (star a ⬝ᵥ ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).mulVec a)) *
          (P ∘ L) z := fun P hP a haΛ z => by
    rw [Hf_coordEquiv D T N N' g e, Hf_coordEquiv D T N N' g e, Function.comp_apply, map_add (f := _)]
    exact transl_of_mem D T hP ((hΛ a).1 haΛ) _
  have hsd : ∀ v, (∀ a ∈ Λ, ∃ k : ℤ,
      (star v ⬝ᵥ ((area T.abelian₂)⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ)).mulVec a).im = k) ↔ v ∈ Λ := by
    intro v
    rw [hΛ, hA]
    constructor
    · intro h y hy
      obtain ⟨k, hk⟩ := h (L.symm y) (by simpa [hΛ] using hy)
      rw [hsw, L.apply_symm_apply] at hk
      exact ⟨-k, by push_cast; linarith⟩
    · intro h a haΛ
      obtain ⟨k, hk⟩ := h (L a) ((hΛ a).1 haΛ)
      exact ⟨-k, by rw [hsw, hk]; push_cast; rfl⟩
  obtain ⟨c, hc⟩ := ThetaTranslSpan.exists_eq_smul hH Λ hsd (fun a => (al D T (L a))⁻¹)
    (G ∘ L) (F ∘ L) (fun a _ => by rw [norm_inv, norm_al, inv_one])
    (hG.1.comp L.differentiable)
    (fun h => h0 (funext fun z => by simpa using congrFun h (L.symm z)))
    (htr G hG) (hF.1.comp L.differentiable) (htr F hF)
  exact ⟨c, funext fun z => by simpa using congrFun hc (L.symm z)⟩

end GlobalTheory.ThetaCoordLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaFunctionSelfDualExistsEqSmulStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_selfDual_exists_eq_smul : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), 0 < area T.abelian₂ → DiscreteTopology A → (∀ x, x ∈ A ↔ ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) → ∀ F ∈ ThSp D T A, ∀ G ∈ ThSp D T A, G ≠ 0 → ∃ c : ℂ, F = c • G := by
  first | exact @GlobalTheory.ThetaCoordLine.exists_eq_smul | exact GlobalTheory.ThetaCoordLine.exists_eq_smul | (intros; apply GlobalTheory.ThetaCoordLine.exists_eq_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylExtremalReproducingNormSqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylExtremalReproducingNormSqOne
open GlobalTheory.DualWeyl MvPolynomial NumberField MeasureTheory
open scoped Matrix ComplexConjugate InnerProductSpace

namespace GlobalTheory.DualWeyl.Repro

variable {N : ℕ} {la : Fin N → ℕ}

theorem exists_repr (la : Fin N → ℕ) :
    ∃ k : nabla la ℂ, ∀ f : nabla la ℂ, form la f.1 k.1 = evalAt 1 f.1 := by
  have : CompleteSpace (Space la) := FiniteDimensional.complete ℂ _
  refine ⟨(toSpace la).symm ((InnerProductSpace.toDual ℂ (Space la)).symm
    (LinearMap.toContinuousLinearMap (evSpace la 1))), fun f => ?_⟩
  rw [← inner_toSpace, LinearEquiv.apply_symm_apply, InnerProductSpace.toDual_symm_apply]
  rfl

theorem form_rhoU_repr {k : nabla la ℂ} (hk : ∀ f : nabla la ℂ, form la f.1 k.1 = evalAt 1 f.1)
    (u : UN N) (f : nabla la ℂ) :
    form la f.1 (rhoU la u⁻¹ k : Pol N ℂ) = evalAt u.1ᵀ f.1 := by
  rw [← form_rhoU u, Representation.self_inv_apply, hk, rhoU_apply, evalAt_rho, Matrix.mul_one]

theorem normSq_repr (hla : Antitone la) {k : nabla la ℂ}
    (hk : ∀ f : nabla la ℂ, form la f.1 k.1 = evalAt 1 f.1) : normSq la k.1 = 1 := by
  let e : Idx la → nabla la ℂ := fun i => (toSpace la).symm (onBasis la i)
  have he : ∀ i, toSpace la (e i) = onBasis la i := fun i => (toSpace la).apply_symm_apply _
  have h1 : ∀ g : UN N, ∑ i, ‖evalAt g.1 (e i).1‖ ^ 2 = normSq la k.1 := by
    intro g
    let u : UN N := ⟨g.1ᵀ, transpose_mem_unitaryGroup g.2⟩
    rw [← normSq_rhoU u⁻¹, ← norm_toSpace_sq, ← (onBasis la).sum_sq_norm_inner_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← he, inner_toSpace, form_rhoU_repr hk]
    rfl
  have h2 : ∑ i, normSq la (e i).1 = dim la := by
    simp only [← norm_toSpace_sq, he, (onBasis la).orthonormal.1]
    simp [dim_eq_card]
  have h3 : ∑ i, normSq la (e i).1 = dim la * normSq la k.1 := by
    conv_lhs => simp only [normSq]
    rw [← Finset.mul_sum, ← integral_finsetSum _ fun i _ => integrable_norm_sq _]
    simp only [h1]
    simp
  have hd : (dim la : ℝ) ≠ 0 := by exact_mod_cast (dim_pos hla).ne'
  exact mul_left_cancel₀ hd (by rw [← h3, h2, mul_one])

theorem rowAct_diagonal_repr {k : nabla la ℂ}
    (hk : ∀ f : nabla la ℂ, form la f.1 k.1 = evalAt 1 f.1) (t : Fin N → ℂ) (ht : ∀ a, ‖t a‖ = 1) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal t) k.1 = (∏ a, t a ^ la a) • k.1 := by
  have hu : Matrix.diagonal t ∈ Matrix.unitaryGroup (Fin N) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp [Complex.mul_conj', ht]
  let u : UN N := ⟨_, hu⟩
  have hinv : (u⁻¹).1ᵀ = Matrix.diagonal (star t) := by
    change (star (Matrix.diagonal t))ᵀ = _
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_transpose]
  have h : rhoU la u k = (∏ a, t a ^ la a) • k := by
    apply (toSpace la).injective
    refine ext_inner_right ℂ fun v => ?_
    obtain ⟨f, rfl⟩ := (toSpace la).surjective v
    rw [inner_toSpace, inner_toSpace, ← inv_inv u, form_rhoU_repr hk, hinv, Submodule.coe_smul, form_smul_right,
      hk, ← Matrix.one_mul (Matrix.diagonal (star t)), ← evalAt_colAct,
      colAct_of_mem f.2 _ (Matrix.blockTriangular_diagonal _), map_smul]
    simp [diagChar]
  have h' := congrArg Subtype.val h
  rwa [rhoU_apply, coe_rho, Matrix.diagonal_transpose] at h'

theorem isWeightedHomogeneous_of_torus {f : Pol N ℂ}
    (h : ∀ t : Fin N → ℂ, (∀ a, ‖t a‖ = 1) →
      Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal t) f = (∏ a, t a ^ la a) • f) :
    IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW N N) f la := by
  classical
  intro m hm
  funext a
  rw [Formalism.GradedWeylDivisibility.ldrow_weight_rowW]
  have hn : Formalism.GradedWeylDivisibility.rowDeg m a + la a + 1 ≠ 0 := by omega
  have hz := Complex.isPrimitiveRoot_exp _ hn
  have hz1 := hz.norm'_eq_one hn
  generalize Complex.exp _ = z at hz hz1
  have h1 := congrArg (AddMonoidAlgebra.coeff · m) (h (Function.update 1 a z) fun b => by
    by_cases hb : b = a
    · subst hb; simpa using hz1
    · simp [Function.update_of_ne hb])
  rw [Formalism.GradedWeylDivisibility.ldrow_coeff_rowAct_diag, coeff_smul, smul_eq_mul, mul_comm] at h1
  have h2 := mul_right_cancel₀ hm h1
  have h3 : ∀ d : Fin N → ℕ, ∏ b, Function.update (1 : Fin N → ℂ) a z b ^ d b = z ^ d a := by
    intro d
    rw [Finset.prod_eq_single a]
    · simp
    · intro b _ hb
      simp [Function.update_of_ne hb]
    · simp
  rw [h3, h3] at h2
  exact hz.pow_inj (by omega) (by omega) h2

theorem extremal_reproducing : ∀ (N : ℕ) (la : Fin N → ℕ), Antitone la →
    (∀ f ∈ nabla la ℂ, form la f (extremal la ℂ) = evalAt 1 f) ∧ normSq la (extremal la ℂ) = 1 := by
  intro N la hla
  obtain ⟨k, hk⟩ := exists_repr la
  have h1 := normSq_repr hla hk
  have h2 : evalAt 1 k.1 = 1 := by rw [← hk, form_self, h1, Complex.ofReal_one]
  have h3 := GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight ℂ N la hla k.1 k.2 (isWeightedHomogeneous_of_torus (rowAct_diagonal_repr hk))
  rw [h2, one_smul] at h3
  rw [← h3]
  exact ⟨fun f hf => hk ⟨f, hf⟩, h1⟩

end GlobalTheory.DualWeyl.Repro
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylExtremalReproducingNormSqOneStatement
open GlobalTheory.DualWeyl MvPolynomial NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_extremal_reproducing_normSq_one : ∀ (N : ℕ) (la : Fin N → ℕ), Antitone la → (∀ f ∈ nabla la ℂ, form la f (extremal la ℂ) = evalAt 1 f) ∧ normSq la (extremal la ℂ) = 1 := by
  first | exact @GlobalTheory.DualWeyl.Repro.extremal_reproducing | exact GlobalTheory.DualWeyl.Repro.extremal_reproducing | (intros; apply GlobalTheory.DualWeyl.Repro.extremal_reproducing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicHighestWeightEqLowestKTypeHighestWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicHighestWeightEqLowestKTypeHighestWeight
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts GlobalTheory.JointHarm

namespace GlobalTheory.HarmonicShape

theorem weight_eq_wtK (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ)
    (μ : Ix p q → ℚ) (P : Pol p q n 0) (h1 : IsHW (fockAct1 p q n 0) μ P)
    (h2 : P ∈ hwSub (fockAct2 p q n 0) (wtH n ap am))
    (h3 : KilledByLower (fockAct1 p q n 0) P) : μ = wtK n ap am := by
  have hj : P ∈ jointHW μ (wtH n ap am) := by
    refine ⟨⟨h1.2, h2⟩, ⟨fun a b => ?_, fun a b => by simp⟩, fun _ j => j.elim0, fun i => i.elim0⟩
    have := h3 a b
    rw [GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.fockAct1_lower, neg_eq_zero] at this
    exact this
  obtain ⟨α, β, γ, δ, ⟨-, -, -, -, a1, b1, c1, d1, -, -, -, -, e1, e2, e3, -⟩, -⟩ :=
    four_of_joint h1.1 hj
  funext x
  rcases x with i | j
  · have hi := i.2
    have u := e1 i
    have v := e3 ⟨i.1, by omega⟩
    rw [b1 _ (by simp)] at u
    rw [d1 _ ((min_le_left _ _).trans (by rw [Fin.val_rev]; dsimp only; omega))] at v
    simp only [shiftNu, cPair, wtH, hi, dif_pos, Fin.eta] at u v
    simp only [wtK]
    push_cast at u v
    linarith
  · have hj := j.2
    have hr := j.rev.2
    have u := e2 j
    have v := e3 (Fin.rev ⟨j.rev.1, by omega⟩)
    have hp : ¬ (Fin.rev (⟨j.rev.1, by omega⟩ : Fin n)).1 < p := by
      rw [Fin.val_rev]; dsimp only; omega
    rw [c1 _ (by simp)] at u
    rw [a1 _ ((min_le_left _ _).trans (not_lt.1 hp))] at v
    simp only [shiftNu, cPair, wtH, dif_neg hp, Fin.rev_rev, hr, dif_pos, Fin.eta] at u v
    simp only [wtK]
    push_cast at u v
    linarith

end GlobalTheory.HarmonicShape
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicHighestWeightEqLowestKTypeHighestWeightStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_highestWeight_eq_lowestKTypeHighestWeight : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) (μ : Ix p q → ℚ) (P : Pol p q n 0), IsHW (fockAct1 p q n 0) μ P → P ∈ hwSub (fockAct2 p q n 0) (wtH n ap am) → KilledByLower (fockAct1 p q n 0) P → μ = wtK n ap am := by
  first | exact @GlobalTheory.HarmonicShape.weight_eq_wtK | exact GlobalTheory.HarmonicShape.weight_eq_wtK | (intros; apply GlobalTheory.HarmonicShape.weight_eq_wtK <;> assumption)
end
end

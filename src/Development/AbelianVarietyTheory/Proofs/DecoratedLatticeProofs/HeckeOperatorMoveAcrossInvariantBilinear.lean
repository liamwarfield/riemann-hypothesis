module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicMajorantFrameForCartanInvolutions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrXLeKOOfPrCat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParametersBoundedEigenfunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwap
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspRapidDecayOfSobolev
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctionsStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeOperatorMoveAcrossInvariantBilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeOperatorMoveAcrossInvariantBilinear
noncomputable section

namespace GlobalTheory.ChainOnto

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

section Move

variable {G : Type} [Group G] {K : Subgroup G}

theorem mem_doubleCoset_inv_iff {a g : G} :
    g⁻¹ ∈ DoubleCoset.doubleCoset a (K : Set G) K ↔ g ∈ DoubleCoset.doubleCoset a⁻¹ (K : Set G) K := by
  simp only [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨h, hh, k, hk, e⟩
    refine ⟨k⁻¹, K.inv_mem hk, h⁻¹, K.inv_mem hh, ?_⟩
    have hg : g = (h * a * k)⁻¹ := by rw [← e, inv_inv]
    rw [hg]
    group
  · rintro ⟨h, hh, k, hk, e⟩
    refine ⟨k⁻¹, K.inv_mem hk, h⁻¹, K.inv_mem hh, ?_⟩
    rw [e]
    group

theorem dosetInd_comp_inv (a : G) : (fun g => dosetInd ℂ K a g⁻¹) = dosetInd ℂ K a⁻¹ := by
  funext g
  simp only [dosetInd]
  by_cases h : g ∈ DoubleCoset.doubleCoset a⁻¹ (K : Set G) K
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (mem_doubleCoset_inv_iff.mpr h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (mem_doubleCoset_inv_iff.mp h'))]

theorem out_mem_doubleCoset_iff (a : G) (c : G ⧸ K) :
    c.out ∈ DoubleCoset.doubleCoset a (K : Set G) K ↔ ∃ k ∈ K, c = ((k * a : G) : G ⧸ K) := by
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨h, hh, k, hk, e⟩
    refine ⟨h, hh, ?_⟩
    have hc : ((c.out : G) : G ⧸ K) = c := QuotientGroup.out_eq' c
    rw [← hc, e, QuotientGroup.eq]
    have hx : (h * a * k)⁻¹ * (h * a) = k⁻¹ := by group
    rw [hx]
    exact K.inv_mem hk
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K (k * a)
    exact ⟨k, hk, h, h.2, hh⟩

private theorem finite_left_cosets_of_isCommensurated (hK : IsCommensurated K) (a : G) :
    {c : G ⧸ K | ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)}.Finite := by
  have h := hK a
  set H := K.map (MulAut.conj a).toMonoidHom with hH
  have hfin : Finite (K ⧸ H.subgroupOf K) := by
    unfold Subgroup.relIndex at h
    exact Subgroup.index_ne_zero_iff_finite.mp h
  apply (Set.finite_range (fun q : K ⧸ H.subgroupOf K => ((((q.out : K) : G) * a : G) : G ⧸ K))).subset
  rintro c ⟨k, hk, rfl⟩
  obtain ⟨h', hh'⟩ := QuotientGroup.mk_out_eq_mul (H.subgroupOf K) (⟨k, hk⟩ : K)
  refine ⟨QuotientGroup.mk ⟨k, hk⟩, ?_⟩
  simp only
  rw [hh', QuotientGroup.eq]
  have hm : ((h' : K) : G) ∈ H := Subgroup.mem_subgroupOf.mp h'.2
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hm
  have hy' : ((h' : K) : G) = a * y * a⁻¹ := by
    rw [← hyeq]
    simp [MulAut.conj_apply]
  have hx : ((((⟨k, hk⟩ : K) * (h' : K) : K) : G) * a)⁻¹ * (k * a) = y⁻¹ := by
    rw [Subgroup.coe_mul, hy']
    simp only [Subgroup.coe_mk]
    group
  rw [hx]
  exact K.inv_mem hy

theorem finsum_dosetInd_out (hK : IsCommensurated K) (a : G) :
    ∑ᶠ c : G ⧸ K, dosetInd ℂ K a c.out = (Nat.card {c : G ⧸ K // ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)} : ℂ) := by
  classical
  set S := {c : G ⧸ K | ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)} with hSdef
  have hS : S.Finite := finite_left_cosets_of_isCommensurated hK a
  have hind : ∀ c : G ⧸ K, dosetInd ℂ K a c.out = S.indicator (fun _ => (1 : ℂ)) c := by
    intro c
    simp only [dosetInd, Set.indicator_apply, out_mem_doubleCoset_iff, hSdef, Set.mem_setOf_eq, Pi.one_apply]
  rw [finsum_congr hind, ← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hS, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  have hcard : Nat.card S = hS.toFinset.card := Nat.card_eq_card_finite_toFinset hS
  exact_mod_cast hcard.symm

private theorem apply_eq_of_mem_fixed {G V : Type} [Group G] {K : Subgroup G} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) {v : V} (hv : v ∈ fixed ρ K) {k : G} (hk : k ∈ K) : ρ k v = v := by
  have h : ∀ h : K, ρ h v = ((1 : K →* ℂˣ) h : ℂ) • v := hv
  simpa using h ⟨k, hk⟩

private theorem invariant_pairing_doubleCoset_eq {G U X X' : Type} [Group G] {K : Subgroup G} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    (π : Representation ℂ G U) (ρ : Representation ℂ G X) (b : U →ₗ[ℂ] X →ₗ[ℂ] X')
    (hb : ∀ g u y, b (π g u) (ρ g y) = b u y) {u : U} (hu : u ∈ fixed π K) {y : X} (hy : y ∈ fixed ρ K)
    {a w : G} (hw : w ∈ DoubleCoset.doubleCoset a (K : Set G) K) : b (π w u) y = b (π a u) y := by
  obtain ⟨k, hk, k', hk', rfl⟩ := DoubleCoset.mem_doubleCoset.mp hw
  have hu' : π k' u = u := apply_eq_of_mem_fixed π hu hk'
  have hy' : ρ k⁻¹ y = y := apply_eq_of_mem_fixed ρ hy (K.inv_mem hk)
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hu']
  calc b (π k (π a u)) y = b (π k (π a u)) (ρ k (ρ k⁻¹ y)) := by rw [Representation.self_inv_apply]
    _ = b (π a u) (ρ k⁻¹ y) := hb k _ _
    _ = b (π a u) y := by rw [hy']

private theorem pairing_heckeVec_dosetInd_eq_card_smul {G U X X' : Type} [Group G] {K : Subgroup G} (hK : IsCommensurated K)
    [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    (π : Representation ℂ G U) (ρ : Representation ℂ G X) (b : U →ₗ[ℂ] X →ₗ[ℂ] X')
    (hb : ∀ g u y, b (π g u) (ρ g y) = b u y) {u : U} (hu : u ∈ fixed π K) {y : X} (hy : y ∈ fixed ρ K)
    (r : ℂ) (a : G) :
    b (heckeVec π K (r • dosetInd ℂ K a) u) y =
      (r * (Nat.card {c : G ⧸ K // ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)} : ℂ)) • b (π a u) y := by
  classical
  have hS := finite_left_cosets_of_isCommensurated hK a
  have hind : ∀ c : G ⧸ K, c ∉ {c : G ⧸ K | ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)} → dosetInd ℂ K a c.out = 0 := by
    intro c hc
    simp only [dosetInd]
    exact Set.indicator_of_notMem (fun h => hc ((out_mem_doubleCoset_iff a c).mp h)) _
  rw [← LinearMap.flip_apply b (heckeVec π K (r • dosetInd ℂ K a) u) y]
  unfold heckeVec
  have hsupp : (Function.support fun c : G ⧸ K => (r • dosetInd ℂ K a) c.out • π c.out u).Finite := by
    apply hS.subset
    intro c hc
    by_contra hcS
    apply hc
    simp [hind c hcS]
  rw [map_finsum _ hsupp]
  have hterm : ∀ c : G ⧸ K, (b.flip y) ((r • dosetInd ℂ K a) c.out • π c.out u) =
      (r * dosetInd ℂ K a c.out) • b (π a u) y := by
    intro c
    rw [map_smul, LinearMap.flip_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hc : c ∈ {c : G ⧸ K | ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)}
    · rw [invariant_pairing_doubleCoset_eq π ρ b hb hu hy ((out_mem_doubleCoset_iff a c).mpr hc)]
    · simp [hind c hc]
  rw [finsum_congr hterm, ← finsum_smul, ← mul_finsum, finsum_dosetInd_out hK a]

private theorem comp_inv_mem_hecke {G : Type} [Group G] {K : Subgroup G} {ψ : G → ℂ} (hψ : ψ ∈ Hecke ℂ K) :
    (fun g => ψ g⁻¹) ∈ Hecke ℂ K := by
  classical
  have h : IsBiInv K ψ ∧ FinDosetSupp K ψ := hψ
  obtain ⟨hbi, S, hS⟩ := h
  show IsBiInv K (fun g => ψ g⁻¹) ∧ FinDosetSupp K (fun g => ψ g⁻¹)
  refine ⟨fun a b g => ?_, S.image (fun s => s⁻¹), fun g hg => ?_⟩
  · have e := hbi b⁻¹ a⁻¹ g⁻¹
    simp only [Subgroup.coe_inv] at e
    simp only
    rw [← e]
    congr 1
    group
  · obtain ⟨s, hs, a, b, e⟩ := hS g⁻¹ hg
    refine ⟨s⁻¹, Finset.mem_image_of_mem _ hs, b⁻¹, a⁻¹, ?_⟩
    have hg' : g = (↑a * s * ↑b)⁻¹ := by rw [← e, inv_inv]
    rw [hg', Subgroup.coe_inv, Subgroup.coe_inv]
    group

end Move

theorem heckeVec_move : ∀ (G : Type) [Group G] (K : Subgroup G), IsCommensurated K → CosetSym K →
    ∀ (U X X' : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    (π : Representation ℂ G U) (ρ : Representation ℂ G X) (b : U →ₗ[ℂ] X →ₗ[ℂ] X'),
    (∀ g u y, b (π g u) (ρ g y) = b u y) → ∀ f ∈ fixed π K, ∀ x ∈ fixed ρ K, ∀ φ ∈ Hecke ℂ K,
    (fun g => φ g⁻¹) ∈ Hecke ℂ K ∧ b (heckeVec π K φ f) x = b f (heckeVec ρ K (fun g => φ g⁻¹) x) := by
  intro G _ K hK hsym U X X' _ _ _ _ _ _ π ρ b hb f hf x hx φ hφ
  refine ⟨comp_inv_mem_hecke hφ, ?_⟩
  refine hecke_induction (p := fun ψ => b (heckeVec π K ψ f) x = b f (heckeVec ρ K (fun g => ψ g⁻¹) x))
    ?_ ?_ ?_ hφ
  · simp [heckeVec]
  · intro ψ hψ ψ' hψ' e e'
    have hsum : (fun g => (ψ + ψ') g⁻¹) = (fun g => ψ g⁻¹) + (fun g => ψ' g⁻¹) := rfl
    rw [heckeVec_add hK π hψ hψ' f, hsum, heckeVec_add hK ρ (comp_inv_mem_hecke hψ) (comp_inv_mem_hecke hψ') x,
      map_add, LinearMap.add_apply, map_add, e, e']
  · intro r a
    have hc : (fun g => (r • dosetInd ℂ K a) g⁻¹) = r • dosetInd ℂ K a⁻¹ := by
      funext g
      rw [Pi.smul_apply, Pi.smul_apply, ← dosetInd_comp_inv a]
    have hb' : ∀ g y u, b.flip (ρ g y) (π g u) = b.flip y u := fun g y u => by
      rw [LinearMap.flip_apply, LinearMap.flip_apply, hb]
    rw [hc, pairing_heckeVec_dosetInd_eq_card_smul hK π ρ b hb hf hx r a, ← LinearMap.flip_apply b f (heckeVec ρ K (r • dosetInd ℂ K a⁻¹) x),
      pairing_heckeVec_dosetInd_eq_card_smul hK ρ π b.flip hb' hx hf r a⁻¹, LinearMap.flip_apply, hsym a]
    congr 1
    rw [← hb a f (ρ a⁻¹ x), Representation.self_inv_apply]

end GlobalTheory.ChainOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeOperatorMoveAcrossInvariantBilinearStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_operator_move_across_invariant_bilinear : ∀ (G : Type) [Group G] (K : Subgroup G), IsCommensurated K → CosetSym K → ∀ (U X X' : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X'] (π : Representation ℂ G U) (ρ : Representation ℂ G X) (b : U →ₗ[ℂ] X →ₗ[ℂ] X'), (∀ g u y, b (π g u) (ρ g y) = b u y) → ∀ f ∈ fixed π K, ∀ x ∈ fixed ρ K, ∀ φ ∈ Hecke ℂ K, (fun g => φ g⁻¹) ∈ Hecke ℂ K ∧ b (heckeVec π K φ f) x = b f (heckeVec ρ K (fun g => φ g⁻¹) x) := by
  first | exact @GlobalTheory.ChainOnto.heckeVec_move | exact GlobalTheory.ChainOnto.heckeVec_move | (intros; apply GlobalTheory.ChainOnto.heckeVec_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainInnerProductsExistOfRapidDecay
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainInnerProductsExistOfRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainMetric

theorem integ_pair {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    {X : Type} [MeasurableSpace X] {μ : Measure X} {A : Set X}
    (f g : (⨂[ℂ] i, E i) →ₗ[ℂ] (X → ℂ)) (B : (⨂[ℂ] i, E i) →ₗ[ℂ] (⨂[ℂ] i, E i) →ₗ⋆[ℂ] ℂ) (k : ℂ)
    (h : ∀ v v' : ∀ i, E i, IntegrableOn (fun x => f (PiTensorProduct.tprod ℂ v) x * conj (g (PiTensorProduct.tprod ℂ v') x)) A μ ∧
      ∫ x in A, f (PiTensorProduct.tprod ℂ v) x * conj (g (PiTensorProduct.tprod ℂ v') x) ∂μ =
        k * B (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v')) :
    ∀ w w', IntegrableOn (fun x => f w x * conj (g w' x)) A μ ∧ ∫ x in A, f w x * conj (g w' x) ∂μ = k * B w w' := by

  have left : ∀ (w : ⨂[ℂ] i, E i) (v' : ∀ i, E i),
      IntegrableOn (fun x => f w x * conj (g (PiTensorProduct.tprod ℂ v') x)) A μ ∧
        ∫ x in A, f w x * conj (g (PiTensorProduct.tprod ℂ v') x) ∂μ = k * B w (PiTensorProduct.tprod ℂ v') := by
    intro w v'
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      obtain ⟨h1, h2⟩ := h v v'
      have e : (fun x => f (r • PiTensorProduct.tprod ℂ v) x * conj (g (PiTensorProduct.tprod ℂ v') x)) =
          fun x => r * (f (PiTensorProduct.tprod ℂ v) x * conj (g (PiTensorProduct.tprod ℂ v') x)) := by
        funext x
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      refine ⟨?_, ?_⟩
      · rw [e]
        exact Integrable.const_mul h1 r
      · rw [e, integral_const_mul, h2]
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring
    | add a b ha hb =>
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨hb1, hb2⟩ := hb
      have e : (fun x => f (a + b) x * conj (g (PiTensorProduct.tprod ℂ v') x)) =
          fun x => f a x * conj (g (PiTensorProduct.tprod ℂ v') x) + f b x * conj (g (PiTensorProduct.tprod ℂ v') x) := by
        funext x
        simp only [map_add (f := _), Pi.add_apply, add_mul]
      refine ⟨?_, ?_⟩
      · rw [e]
        exact Integrable.add ha1 hb1
      · rw [e, integral_add ha1 hb1, ha2, hb2]
        simp only [map_add (f := _), LinearMap.add_apply, mul_add]

  intro w w'
  induction w' using PiTensorProduct.induction_on with
  | smul_tprod r v' =>
    obtain ⟨h1, h2⟩ := left w v'
    have e : (fun x => f w x * conj (g (r • PiTensorProduct.tprod ℂ v') x)) =
        fun x => conj r * (f w x * conj (g (PiTensorProduct.tprod ℂ v') x)) := by
      funext x
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
      ring
    refine ⟨?_, ?_⟩
    · rw [e]
      exact Integrable.const_mul h1 (conj r)
    · rw [e, integral_const_mul, h2]
      simp only [LinearMap.map_smulₛₗ, smul_eq_mul]
      ring
  | add a b ha hb =>
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    have e : (fun x => f w x * conj (g (a + b) x)) =
        fun x => f w x * conj (g a x) + f w x * conj (g b x) := by
      funext x
      simp only [map_add (f := _), Pi.add_apply, mul_add]
    refine ⟨?_, ?_⟩
    · rw [e]
      exact Integrable.add ha1 hb1
    · rw [e, integral_add ha1 hb1, ha2, hb2]
      simp only [map_add (f := _), mul_add]

variable {D : D7}

theorem val_tprod {V' : HSp D} {S' : D.what₂.Tau → SPar} {M' : DSModel V' S'} (x : (⨂[ℂ] τ, M'.sm τ) →ₗ[ℂ] (GA D V' → ℂ))
    (v : M'.Vec) : x (PiTensorProduct.tprod ℂ v) = PiTensorProduct.lift.symm x v := by
  rw [PiTensorProduct.lift_symm, LinearMap.compMultilinearMap_apply]

theorem metEx : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D := by
  intro hP D c hc j _ s hs
  obtain ⟨ipD, hpure, hhermD, hposD⟩ := GlobalTheory.T.exists_inner_product_smooth_vectors_tensor D s.V s.par s.M
  have hθ : IsInfFam c.θ := hc.inf
  have hμ := hs.haar
  have h𝓕 := hs.fund
  have hSM : SchurMult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) s.ν s.fd :=
    GlobalTheory.MultFinite.schurMult hP s.ν s.fd
  have hmem : ∀ x : s.CC c, PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
      Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) :=
    fun x => (mem_multT c.θ s.M _ _ _).1 x.2
  by_cases hsm : ∀ τ, s.M.sm τ ≠ ⊥
  ·
    obtain ⟨hlin, hpos⟩ := GlobalTheory.SchurConst.ipM_posDef D c.θ s.V s.par s.M _ _ s.ν s.fd hθ hμ h𝓕 hSM hsm
    have hherm : ∀ T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
        ∀ T' ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
          ipM s.M s.ν s.fd T' T = star (ipM s.M s.ν s.fd T T') :=
      fun T hT T' hT' => (hlin T hT T' hT' T' hT' 0).2
    have hadd : ∀ T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
        ∀ T' ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
          ∀ T'' ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
            ipM s.M s.ν s.fd T (T' + T'') = ipM s.M s.ν s.fd T T' + ipM s.M s.ν s.fd T T'' := by
      intro T hT T' hT' T'' hT''
      have := (hlin T hT T' hT' T'' hT'' 1).1
      rwa [one_smul, one_mul] at this
    have hzero : ∀ T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L), ipM s.M s.ν s.fd T 0 = 0 := by
      intro T hT
      have := hadd T hT 0 (zero_mem _) 0 (zero_mem _)
      rw [add_zero] at this
      linear_combination -this
    have hsmul : ∀ T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
        ∀ T' ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L), ∀ a : ℂ,
          ipM s.M s.ν s.fd T (a • T') = a * ipM s.M s.ν s.fd T T' := by
      intro T hT T' hT' a
      have := (hlin T hT 0 (zero_mem _) T' hT' a).1
      rwa [zero_add, hzero T hT, zero_add] at this

    have hIP : ∀ x y : s.CC c, ∀ w w',
        IntegrableOn (fun g => (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w g *
          conj ((y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w' g)) s.fd s.ν ∧
        ∫ g in s.fd, (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w g * conj ((y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w' g) ∂s.ν =
          ipM s.M s.ν s.fd (PiTensorProduct.lift.symm (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))
            (PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))) * ipD w w' := by
      intro x y
      apply integ_pair
      intro v v'
      have hex := hSM hθ hμ h𝓕 _ (hmem y) _ (hmem x)
      have hc : IsMultIP s.M s.ν s.fd (PiTensorProduct.lift.symm (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))
          (PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))
          (ipM s.M s.ν s.fd (PiTensorProduct.lift.symm (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))
            (PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))) := by
        rw [ipM, dite_eq_left hex]
        exact hex.choose_spec
      obtain ⟨h1, h2⟩ := hc v' v
      have e : (fun g => (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) (PiTensorProduct.tprod ℂ v) g *
          conj ((y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) (PiTensorProduct.tprod ℂ v') g)) =
          fun g => star (PiTensorProduct.lift.symm (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v' g) *
            PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v g := by
        funext g
        rw [val_tprod, val_tprod, mul_comm, starRingEnd_apply]
      refine ⟨?_, ?_⟩
      · rw [e]
        exact h1
      · rw [e, h2, hpure]
    refine ⟨ipD, LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun x y : s.CC c => ipM s.M s.ν s.fd (PiTensorProduct.lift.symm (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))
        (PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))) ?_ ?_ ?_ ?_, ?_⟩
    · intro x x' y
      simp only [Submodule.coe_add, map_add (f := _)]
      exact hadd _ (hmem y) _ (hmem x) _ (hmem x')
    · intro a x y
      simp only [Submodule.coe_smul, map_smul, RingHom.id_apply, smul_eq_mul]
      exact hsmul _ (hmem y) _ (hmem x) a
    · intro x y y'
      simp only [Submodule.coe_add, map_add (f := _)]
      rw [hherm _ (hmem x) _ (add_mem (hmem y) (hmem y')), hadd _ (hmem x) _ (hmem y) _ (hmem y'), star_add,
        ← hherm _ (hmem x) _ (hmem y), ← hherm _ (hmem x) _ (hmem y')]
    · intro a x y
      simp only [Submodule.coe_smul, map_smul, smul_eq_mul]
      rw [hherm _ (hmem x) _ (Submodule.smul_mem _ a (hmem y)), hsmul _ (hmem x) _ (hmem y), star_mul',
        ← hherm _ (hmem x) _ (hmem y), starRingEnd_apply]
    · refine ⟨hpure, hhermD, hposD, ?_, ?_, ?_, ?_⟩
      · intro x y
        simp only [LinearMap.mk₂'ₛₗ_apply]
        rw [hherm _ (hmem x) _ (hmem y), starRingEnd_apply]
      · intro x hx
        simp only [LinearMap.mk₂'ₛₗ_apply]
        refine hpos _ (hmem x) fun h0 => hx ?_
        apply Subtype.ext
        rw [Submodule.coe_zero]
        exact (LinearEquiv.map_eq_zero_iff _).1 h0
      · intro x y w w'
        exact (hIP x y w w').1
      · intro x y w w'
        simp only [Lift.pet, LinearMap.mk₂'ₛₗ_apply]
        exact (hIP x y w w').2
  ·
    push_neg at hsm
    obtain ⟨τ₀, hτ₀⟩ := hsm
    have htp : ∀ v : s.M.Vec, PiTensorProduct.tprod ℂ v = 0 := by
      intro v
      apply (PiTensorProduct.tprod ℂ).map_coord_zero τ₀
      have : (v τ₀ : s.M.H τ₀) ∈ (⊥ : Submodule ℂ (s.M.H τ₀)) := hτ₀ ▸ (v τ₀).2
      exact Subtype.ext ((Submodule.mem_bot ℂ).1 this)
    have hz : ∀ w : SmT s.M, w = 0 := by
      intro w
      induction w using PiTensorProduct.induction_on with
      | smul_tprod r v => rw [htp v, smul_zero]
      | add a b ha hb => rw [ha, hb, add_zero]
    refine ⟨ipD, 0, hpure, hhermD, hposD, ?_, ?_, ?_, ?_⟩
    · intro x y
      simp
    · intro x hx
      exfalso
      apply hx
      apply Subtype.ext
      apply LinearMap.ext
      intro w
      rw [hz w]
      simp
    · intro x y w w'
      rw [hz w, hz w']
      simp
    · intro x y w w'
      rw [hz w, hz w']
      simp [Lift.pet]

end GlobalTheory.ChainMetric
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainInnerProductsExistOfRapidDecayStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainInnerProductsExist_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D := by
  first | exact @GlobalTheory.ChainMetric.metEx | exact GlobalTheory.ChainMetric.metEx | (intros; apply GlobalTheory.ChainMetric.metEx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepCharsUnramifiedOffS
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepCharsUnramifiedOffS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem step_chars_unrAt : ∀ (D : D7) (c : Com D), c.Is → ∀ k < D.R.m, ∀ v ∉ c.S, ∀ w : HeightOneSpectrum (𝓞 D.host.E),
    w.under (𝓞 D.host.F) = v → UnrAt (c.chS (k + 1)) w ∧ UnrAt (c.chT (k + 1)) w := by
  intro D c hc k hk v hv w hw
  have hμ : UnrAt (c.μ (k + 1)) w := by
    have := hc.unr ⟨k, hk⟩ w
    exact this (by rw [GlobalTheory.LFun.above, Set.mem_setOf_eq, hw]; exact hv)
  have hη : UnrAt c.η⁻¹ w := (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 w).inv
  have hμη : UnrAt (c.μ (k + 1) * c.η⁻¹) w := hμ.mul hη
  unfold Com.chS Com.chT Lift.chrStep
  split_ifs <;> exact ⟨by assumption, by assumption⟩

end GlobalTheory.ChainOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepCharsUnramifiedOffSStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChain_step_chars_unramified_off_S : ∀ (D : D7) (c : Com D), c.Is → ∀ k < D.R.m, ∀ v ∉ c.S, ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → UnrAt (c.chS (k + 1)) w ∧ UnrAt (c.chT (k + 1)) w := by
  first | exact @GlobalTheory.ChainOnto.step_chars_unrAt | exact GlobalTheory.ChainOnto.step_chars_unrAt | (intros; apply GlobalTheory.ChainOnto.step_chars_unrAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStagePeterssonValueRealLevelTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStagePeterssonValueRealLevelTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.PetCoef

theorem pet_smul_left {D : D7} (s : PiLocalization₂ D) (a : ℂ) (f g : GA D s.V → ℂ) :
    s.pet (a • f) g = a * s.pet f g := by
  unfold PiLocalization₂.pet Lift.pet
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact MeasureTheory.integral_const_mul a _

theorem petco : ∀ D : D7, ForStage D fun c _ s => ∀ ipD ip, IsMet c s ipD ip → ∀ (u : s.CC c) (v : s.M.Vec) (b : GinfC s.V), ∀ κ ∈ Lev.levG s.V s.β s.L, s.pet (rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v))) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) = Lev.levChi s.V s.β s.L κ * ip u u * ∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ := by
  intro D c hc j hj s hs ipD ip hM u v b κ hκ
  have hmem := (mem_multT c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))).1 u.2
  have hmap := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hmem
  obtain ⟨w, hw, hU⟩ := GlobalTheory.T.multiplicitySpace_equivariant_real_points D c.θ s.V s.par s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) hc.inf v b
  have hUw := hU _ hmem
  have ev : ∀ x : s.M.Vec, PiLocalization₂.val u (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) x := by
    intro x; simp [PiLocalization₂.val, PiTensorProduct.lift_symm]
  have key : rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) =
      Lev.levChi s.V s.β s.L κ • PiLocalization₂.val u (PiTensorProduct.tprod ℂ w) := by
    funext g
    rw [ev, ev, hUw]
    simp only [rTr, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc]
    exact hmap.lev v κ hκ (g * (b : GA D s.V))
  have hsch : s.pet (PiLocalization₂.val u (PiTensorProduct.tprod ℂ w)) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) =
      ip u u * ipD (PiTensorProduct.tprod ℂ w) (PiTensorProduct.tprod ℂ v) := hM.schur u u _ _
  rw [key, pet_smul_left, hsch, hM.pure w v]
  simp only [hw, mul_assoc]

end GlobalTheory.ChainOnto.PetCoef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStagePeterssonValueRealLevelTranslateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStage_petersson_value_realLevelTranslate : ∀ D : D7, ForStage D fun c _ s => ∀ ipD ip, IsMet c s ipD ip → ∀ (u : s.CC c) (v : s.M.Vec) (b : GinfC s.V), ∀ κ ∈ Lev.levG s.V s.β s.L, s.pet (rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v))) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) = Lev.levChi s.V s.β s.L κ * ip u u * ∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ := by
  first | exact @GlobalTheory.ChainOnto.PetCoef.petco | exact GlobalTheory.ChainOnto.PetCoef.petco | (intros; apply GlobalTheory.ChainOnto.PetCoef.petco <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearIndependentOfIsParamFunV
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearIndependentOfIsParamFunV
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem linearIndependent_of_isParamFunV : ∀ (D : D7) (V : HSp D) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (ι : Type)
    (f : ι → (GA D V → ℂ)) (B : ι → GlobalTheory.LFun.Fam D.host.E), (∀ i, f i ≠ 0) → (∀ i, GlobalTheory.LFun.IsParamFunV V Sb (f i) (B i)) →
    (∀ i i', i ≠ i' → ∃ w ∉ GlobalTheory.LFun.above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F))), B i w ≠ B i' w) →
    LinearIndependent ℂ f := by
  intro D V Sb ι f B h0 hP hB
  have hJ := GlobalTheory.LFun.sphOff_KsphC V Sb
  choose a ha using fun i => GlobalTheory.T.sphericalOperator_eigenvalues_determined_by_params D V (KsphC V ∅) (fun _ => 1) Sb hJ (B i)
  have hfix : ∀ i, ∀ v ∉ Sb, ∀ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) v, ∀ g,
      f i (g * GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k) = f i g := by
    intro i v hv k hk g
    obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
      have := v.isPrime
      obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 D.host.E)).some
      exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
    have hx := (hP i v hv w hw).mem_fixed
    exact congrFun (GlobalTheory.LGrp.mem_fixed.1 hx k hk) g
  let α := {t : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D V) //
    Hecke₂ V (KsphC V ∅) (fun _ => 1) Sb t.1 t.2.1 t.2.2}
  refine GlobalTheory.FinWeil.linearIndependent_of_simultaneous_eigen f (fun i (t : α) => a i t.1.1 t.1.2.1)
    (fun t : α => heckeLin V t.1.2.2) ?_ (fun t i => ha i (f i) (hP i) _ _ _ t.2) h0
  intro i i' hii
  by_contra hne
  obtain ⟨w, hw, hne'⟩ := hB i i' hne
  have hc : ∀ P d R, Hecke₂ V (KsphC V ∅) (fun _ => 1) Sb P d R → heckeLin V R (f i') = a i P d • f i' := by
    intro P d R hR
    have := congrFun hii ⟨(P, d, R), hR⟩
    rw [ha i' (f i') (hP i') P d R hR]
    exact congrArg (· • f i') this.symm
  have h1 := (GlobalTheory.LFun.isParamFunV_iff_isSysParamD hJ (h0 i) (hfix i) (ha i (f i) (hP i)) (B i)).1 (hP i)
  have h2 := (GlobalTheory.LFun.isParamFunV_iff_isSysParamD hJ (h0 i') (hfix i') hc (B i')).1 (hP i')
  exact hne' (GlobalTheory.LFun.IsSysParamOff.unique h1 h2 hw)

end GlobalTheory.ChainOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearIndependentOfIsParamFunVStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_of_ne_zero_of_isParamFunV_of_separated : ∀ (D : D7) (V : HSp D) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (ι : Type) (f : ι → (GA D V → ℂ)) (B : ι → GlobalTheory.LFun.Fam D.host.E), (∀ i, f i ≠ 0) → (∀ i, GlobalTheory.LFun.IsParamFunV V Sb (f i) (B i)) → (∀ i i', i ≠ i' → ∃ w ∉ GlobalTheory.LFun.above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F))), B i w ≠ B i' w) → LinearIndependent ℂ f := by
  first | exact @GlobalTheory.ChainOnto.linearIndependent_of_isParamFunV | exact GlobalTheory.ChainOnto.linearIndependent_of_isParamFunV | (intros; apply GlobalTheory.ChainOnto.linearIndependent_of_isParamFunV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParamsTrivialBoundRapidDecay
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParamsTrivialBoundRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.ChainOnto.parBound_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LevFacts D → ParBound D := by
  intro hCRD D _hLF c hc j hj s hs u B hB
  obtain ⟨hu0, hpar⟩ := hB
  have hex : ∃ v, PiLocalization₂.val u v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hu0
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact h v
  obtain ⟨v, hv⟩ := hex
  set f : GA D s.V → ℂ := fun g => conj (PiLocalization₂.val u v g) with hfdef
  have hPF : ParFun c s (PiLocalization₂.val u v) B := hpar v hv
  have h3 : GlobalTheory.LFun.IsParamFunV s.V c.S f B := ((GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hc j hj s hs).2 f B).1 hPF
  obtain ⟨h4a, _, _⟩ := GlobalTheory.T.thetaChainStage_conjugate_values_hecke_operators hCRD D c hc j hj s hs
  obtain ⟨hcont, ⟨C, hC⟩, hinv, hlev⟩ := h4a u v
  obtain ⟨_, hsph, _⟩ := GlobalTheory.T.thetaChainStage_level_spherical_off_set D c hc j hj s hs
  have hfmem : f ∈ GlobalTheory.FinZeta.bddAut s.V := by
    refine ⟨(Complex.continuous_conj).comp hcont, fun γ hγ g => ?_, C, fun g => ?_⟩
    · simp only [hfdef, hinv γ hγ g]
    · simpa [hfdef] using hC g
  have hf0 : f ≠ 0 := by
    intro h0
    apply hv
    funext g
    have := congrFun h0 g
    simpa [hfdef] using this
  have hlev' : ∀ k ∈ levS s.V s.β s.L, ∀ g, f (g * k) = conj (Lev.levChi s.V s.β s.L k) * f g := by
    intro k hk g
    simp only [hfdef, hlev k hk g, map_mul]
  obtain ⟨a, ha⟩ := GlobalTheory.T.sphericalOperator_eigenvalues_determined_by_params D s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S hsph B
  obtain ⟨B', hB', hbd⟩ := GlobalTheory.T.exists_satake_parameters_bounded_eigenfunction D s.V _ _ c.S hsph f hfmem hf0 hlev' a (fun P d R hR => ha f h3 P d R hR)
  intro w hw
  rw [GlobalTheory.LFun.IsParamVecOff.unique h3 hB' hw]
  exact hbd w hw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParamsTrivialBoundRapidDecayStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChain_heckeParams_trivialBound_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LevFacts D → ParBound D := by
  first | exact @GlobalTheory.ChainOnto.parBound_of_rapidDecay | exact GlobalTheory.ChainOnto.parBound_of_rapidDecay | (intros; apply GlobalTheory.ChainOnto.parBound_of_rapidDecay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelLeviDetHomLeviMulUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelLeviDetHomLeviMulUnipotent
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw

namespace GlobalTheory.Core.Rk.SWLaw

theorem aP_levi_mul_nC : ∀ (D : D7) (A : HSp D) (p : siegel A) (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank), (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c → aP A p = Matrix.GeneralLinearGroup.det a := by
  intro D A p a c hp
  have hM : Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A)) ⬝ (dblDec A).jX = (dblDec A).jX ⬝ a.1 := by
    rw [hp, GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, HypDec.nC_jX, HypDec.levi_jX]
  apply Units.ext
  rw [GlobalTheory.Doubling.val_aOf]
  show (GlobalTheory.Doubling.leviMat finSumFinEquiv (Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A)))).det = a.1.det
  set M := Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A)) with hMdef
  have key : GlobalTheory.Doubling.leviMat finSumFinEquiv M * rat A.gram⁻¹ = rat A.gram⁻¹ * a.1 := by
    ext i j
    have h := congrFun (congrFun hM (finSumFinEquiv (Sum.inl i))) j
    simp only [HypDec.jX, dblDec, rat, stackRows, Matrix.mul_apply, Matrix.map_apply, Matrix.submatrix_apply,
      Fin.sum_univ_add, finSumFinEquiv_apply_left, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, id] at h
    simp only [GlobalTheory.Doubling.leviMat, rat, Matrix.mul_apply, Matrix.add_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.of_apply, Matrix.submatrix_apply, Matrix.map_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      add_mul, Finset.sum_add_distrib]
    exact h
  have hu : IsUnit (rat (D := D) A.gram⁻¹).det := by
    rw [rat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Matrix.isUnit_nonsing_inv_det _ (gram_det_ne A).isUnit).map _
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm] at hd
  exact hu.mul_left_cancel hd

end GlobalTheory.Core.Rk.SWLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelLeviDetHomLeviMulUnipotentStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingSiegelLeviDetHom_levi_mul_unipotent : ∀ (D : D7) (A : HSp D) (p : siegel A) (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank), (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c → aP A p = Matrix.GeneralLinearGroup.det a := by
  first | exact @GlobalTheory.Core.Rk.SWLaw.aP_levi_mul_nC | exact GlobalTheory.Core.Rk.SWLaw.aP_levi_mul_nC | (intros; apply GlobalTheory.Core.Rk.SWLaw.aP_levi_mul_nC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsAdjointOfRapidDecay
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsAdjointOfRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

variable {D : D7}

theorem rapidDec_val (hP : GlobalTheory.Published.CuspRapidDecay) {c : Com D} (hc : c.Is) {s : PiLocalization₂ D} (u : s.CC c)
    (v : SmT s.M) : GlobalTheory.Grow.RapidDec s.V (PiLocalization₂.val u v) := by
  have hM := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 u.2)
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r w =>
    have h1 := GlobalTheory.Grow.rapidDec_of_cuspForm hP hc.inf (hM.aut w) (hM.cusp w)
    have h2 : PiLocalization₂.val u (r • PiTensorProduct.tprod ℂ w) =
        r • PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w := by
      simp [PiLocalization₂.val, PiTensorProduct.lift_symm]
    rw [h2]
    exact Grow.RapidDec.smul r h1
  | add x y hx hy =>
    have : PiLocalization₂.val u (x + y) = PiLocalization₂.val u x + PiLocalization₂.val u y := by simp [PiLocalization₂.val]
    rw [this]; exact hx.add hy

theorem upAdj_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, UpAdj D := by
  intro hP D _ c hc k _ s s' hs hs' p hp u y φ v _ w _
  have hF := GlobalTheory.T.thetaKernel_iterated_integrals_swap D c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) p.ω hc.inf hp.weil (p.pt φ) (hp.theta φ)
    s.ν s.fd s'.ν s'.fd hs.haar hs.fund hs'.haar hs'.fund (PiLocalization₂.val u v) (PiLocalization₂.val y w)
    (rapidDec_val hP hc u v) (rapidDec_val hP hc y w)
  simp only [PiLocalization₂.pet, Lift.pet, Step.up]
  calc ∫ h in s'.fd, PiLocalization₂.val y w h * starRingEnd ℂ (∫ g in s.fd, conj (thetaKO p.ω g h (p.pt φ)) * PiLocalization₂.val u v g ∂s.ν) ∂s'.ν
      = ∫ h in s'.fd, ∫ g in s.fd, thetaKO p.ω g h (p.pt φ) * PiLocalization₂.val y w h * conj (PiLocalization₂.val u v g) ∂s.ν ∂s'.ν := by
        congr 1; funext h
        rw [← integral_conj, ← integral_const_mul]
        congr 1; funext g
        simp only [map_mul, Complex.conj_conj]; ring
    _ = ∫ g in s.fd, ∫ h in s'.fd, thetaKO p.ω g h (p.pt φ) * PiLocalization₂.val y w h * conj (PiLocalization₂.val u v g) ∂s'.ν ∂s.ν := hF
    _ = ∫ g in s.fd, PiLocalization₂.val (p.io y) (p.It φ w) g * starRingEnd ℂ (PiLocalization₂.val u v g) ∂s.ν := by
        congr 1; funext g
        rw [integral_mul_const]
        congr 1
        exact hp.io.eq y φ w g

end GlobalTheory.ChainOnto
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsAdjointOfRapidDecayStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftUpwardsAdjoint_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, UpAdj D := by
  first | exact @GlobalTheory.ChainOnto.upAdj_of_cuspRapidDecay | exact GlobalTheory.ChainOnto.upAdj_of_cuspRapidDecay | (intros; apply GlobalTheory.ChainOnto.upAdj_of_cuspRapidDecay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftConvContGrowth
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff Topology

namespace GlobalTheory.Unf.LiftRapid

theorem lift_conv_cont_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (v : Vol T) (G : GA D T → ℂ) (f : WO S T → ℂ), RapidDec T G → IsThetaFunO ψ S T f → (∀ g, IntegrableOn (fun h => om (g, h) f 0 * G h) v.𝓕 v.μ) ∧ IsAutFun S (liftS om v.μ v.𝓕 G f) ∧ IsContAut S (liftS om v.μ v.𝓕 G f) ∧ ModGrowth S (liftS om v.μ v.𝓕 G f) ∧ ∀ g₀ h₀, liftS om v.μ v.𝓕 (rTrans h₀ G) (om (g₀, h₀) f) = rTrans g₀ (liftS om v.μ v.𝓕 G f) := by
  intro D ψ S T χS χT om hω v G f hG hf
  have hν := v.haar
  have h𝓕 := v.fund
  have : BorelSpace (GA D T) := ⟨rfl⟩
  have : SecondCountableTopology (GA D S) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S).2.1
  have : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.Chain.LiftReg.vol_ne_top hν h𝓕)
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.weilOperator_thetaFun_sup_moderate_growth D ψ S T χS χT om hω f hf
  obtain ⟨B, hB⟩ := hG.decay A
  have hk : ∀ g h, ‖om (g, h) f 0‖ ≤ C * height S g ^ A * height T h ^ A := fun g h => by
    rw [mul_assoc, ← mul_pow]; exact hC g h 0
  have hleft := fun g => GlobalTheory.Chain.LiftConv.thetaKO_left hω hf g
  have hcont := fun g => GlobalTheory.Chain.LiftConv.thetaKO_continuous hω hf g
  have hint : ∀ g, IntegrableOn (fun h => om (g, h) f 0 * G h) v.𝓕 v.μ := fun g =>
    hG.integrableOn_modGrowth_mul hν h𝓕 ⟨C * height S g ^ A, A, hk g⟩ (hleft g)
      (hcont g).measurable.aestronglyMeasurable
  have hbd : ∀ g h, ‖om (g, h) f 0 * G h‖ ≤ C * 2 ^ A * B * height S g ^ A := fun g h => by
    have h1 := norm_le_quotHeight_pow (f := fun h => thetaKO om g h f) (hleft g) (hk g) h
    have hC0 : 0 ≤ C * height S g ^ A * 2 ^ A :=
      (mul_nonneg (nonneg_of_growth (hk g)) (by positivity))
    rw [norm_mul]
    calc ‖om (g, h) f 0‖ * ‖G h‖ ≤ C * height S g ^ A * 2 ^ A * quotHeight T h ^ A * ‖G h‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = C * height S g ^ A * 2 ^ A * (‖G h‖ * quotHeight T h ^ A) := by ring
      _ ≤ C * height S g ^ A * 2 ^ A * B := mul_le_mul_of_nonneg_left (hB h) hC0
      _ = C * 2 ^ A * B * height S g ^ A := by ring
  have hm : ∀ g, AEStronglyMeasurable (fun h => om (g, h) f 0 * G h) (v.μ.restrict v.𝓕) := fun g =>
    ((hcont g).mul hG.continuous).measurable.aestronglyMeasurable
  have hc : Continuous (liftS om v.μ v.𝓕 G f) := by
    refine continuous_iff_continuousAt.2 fun g₀ => ?_
    have hcb : Continuous fun g => C * 2 ^ A * B * height S g ^ A := continuous_const.mul ((continuous_height S).pow A)
    have hev := hcb.continuousAt.eventually_lt (continuousAt_const (y := C * 2 ^ A * B * height S g₀ ^ A + 1))
      (lt_add_one _)
    exact continuousAt_of_dominated (bound := fun _ => C * 2 ^ A * B * height S g₀ ^ A + 1)
      (.of_forall hm) (hev.mono fun g hg => .of_forall fun h => (hbd g h).trans hg.le) (integrable_const _)
      (.of_forall fun h => (((hω.om_cont f hf 0).comp (Continuous.prodMk_left h)).mul continuous_const).continuousAt)
  have hl : ∀ γ ∈ GQ S, ∀ g, liftS om v.μ v.𝓕 G f (γ * g) = liftS om v.μ v.𝓕 G f g := fun γ hγ g => by
    have e : ∀ h, om (γ * g, h) f 0 = om (g, h) f 0 := fun h => by
      have e' : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by simp
      rw [e', map_mul, Module.End.mul_apply]
      exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hf)
    simp only [liftS_apply, e]
  have heq : ∀ g₀ h₀, liftS om v.μ v.𝓕 (rTrans h₀ G) (om (g₀, h₀) f) = rTrans g₀ (liftS om v.μ v.𝓕 G f) :=
    fun g₀ h₀ => GlobalTheory.Chain.LiftReg.lift_om hω hν h𝓕 hf hG.1 g₀ h₀
  refine ⟨hint, ⟨hl, ?_, hc⟩, ⟨hl, hc⟩, ⟨C * 2 ^ A * B * (v.μ.restrict v.𝓕).real Set.univ, A, fun g => ?_⟩, heq⟩
  · obtain ⟨U, U', hU, -, e⟩ := GlobalTheory.Mem.ThetaLevel.exists_level D ψ hω.std S T om (GlobalTheory.Ker.isWeak_of_datum hω)
      hω.om_cont f hf
    refine ⟨U, hU, fun k h1 h2 g => ?_⟩
    have := congrFun (heq k 1) g
    rw [e k h1 h2 1 (one_mem _) (one_mem _), show rTrans 1 G = G from funext fun h => congrArg G (mul_one h)] at this
    exact this.symm
  · rw [liftS_apply]
    refine (norm_integral_le_of_norm_le_const (.of_forall fun h => hbd g h)).trans_eq ?_
    ring

end GlobalTheory.Unf.LiftRapid

end
end

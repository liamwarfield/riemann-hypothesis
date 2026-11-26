module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TypeExNZ
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Uniformizer₂
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Isotypic₂
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PJinv
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.MemKCOfRedEq
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PTpow
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Iwahori₂
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PExGrp
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PNonint
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.IsClosedUnipRad
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SupportProduct

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PJone
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

namespace P_Jone

theorem inPow_zero (c : ℕ) : InPow c (0 : k) :=
  ⟨0, zero_mem _, map_zero _⟩

end P_Jone

theorem step_Jone {n : ℕ} (G : Grp k n) : G.JacquetOneProp := by
  refine ⟨⟨Subgroup.one_mem _, fun i j hij => ?_⟩, fun g hg => ⟨hg.1, fun i j hij => ?_⟩⟩
  · have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hij
    rw [Units.val_one, Matrix.one_apply_ne hne]
    exact P_Jone.inPow_zero _
  · rw [(mem_parab.1 hg.2) i j hij]
    exact P_Jone.inPow_zero _

end Grp

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PDMul
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_DMul

theorem minor_mul_sub_mem {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → Prop) [DecidablePred p]
    (Q : Ideal R) (A B : Matrix ι ι R) (hB : ∀ i j, ¬ p i → p j → B i j ∈ Q) :
    ((A * B).submatrix (Subtype.val : {i // p i} → ι) Subtype.val).det -
      (A.submatrix (Subtype.val : {i // p i} → ι) Subtype.val).det *
        (B.submatrix (Subtype.val : {i // p i} → ι) Subtype.val).det ∈ Q := by
  rw [← Ideal.Quotient.eq, RingHom.map_mul, RingHom.map_det, RingHom.map_det, RingHom.map_det, ← det_mul]
  congr 1
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, Matrix.mul_apply, map_sum, map_mul]
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  have h0 : ∑ l : {x // ¬ p x}, (Ideal.Quotient.mk Q) (A i l) * (Ideal.Quotient.mk Q) (B l j) = 0 := by
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hB l j l.2 j.2), mul_zero]
  rw [h0, add_zero]

theorem minor_isUnit {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → Prop) [DecidablePred p]
    (M : Matrix ι ι R) (hM : IsUnit M.det) (hl : ∀ i j, ¬ p i → p j → M i j ∈ IsLocalRing.maximalIdeal R) :
    IsUnit (M.submatrix (Subtype.val : {i // p i} → ι) Subtype.val).det := by
  have ht := twoBlockTriangular_det ((IsLocalRing.residue R).mapMatrix M) p
    (fun i hi j hj => (IsLocalRing.residue_eq_zero_iff _).mpr (hl i j hi hj))
  rw [← RingHom.map_det] at ht
  have hu : IsUnit ((IsLocalRing.residue R) M.det) := hM.map _
  rw [ht] at hu
  have h1 := isUnit_of_mul_isUnit_left hu
  refine IsUnit.of_map (IsLocalRing.residue R) _ ?_
  rw [RingHom.map_det]
  exact h1

theorem unit_factor {R : Type} [CommRing R] [IsLocalRing R] (Q : Ideal R) (hQ : Q ≤ IsLocalRing.maximalIdeal R)
    (x y z : R) (hy : IsUnit y) (hz : IsUnit z) (hxyz : x - y * z ∈ Q) :
    ∃ u : Rˣ, (u : R) - 1 ∈ Q ∧ x = y * z * u := by
  obtain ⟨W, hW⟩ : IsUnit (y * z) := hy.mul hz
  have hsub : x * ((W⁻¹ : Rˣ) : R) - 1 ∈ Q := by
    have e : x * ((W⁻¹ : Rˣ) : R) - 1 = (x - y * z) * ((W⁻¹ : Rˣ) : R) := by
      rw [sub_mul, ← hW, Units.mul_inv]
    rw [e]
    exact Ideal.mul_mem_right _ _ hxyz
  have hunit : IsUnit (x * ((W⁻¹ : Rˣ) : R)) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hm
    have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ hm (hQ hsub)
      simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  refine ⟨hunit.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec]; exact hsub
  · rw [IsUnit.unit_spec, ← hW, mul_left_comm, Units.mul_inv, mul_one]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem low {n : ℕ} (G : Grp k n) (a : Fin G.s) (h1 : (a : ℕ) + 1 < G.s) (X : GL (Fin n) 𝒪[k])
    (x : GL (Fin n) k) (hX : Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) X = x) (hx : x ∈ G.JSet)
    (i j : Fin n) (hi : ¬ (G.bl i ≤ a)) (hj : G.bl j ≤ a) :
    (X : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ cc G.μ a ⟨a + 1, h1⟩ := by
  have hlt : G.bl j < G.bl i := lt_of_le_of_lt hj (not_le.mp hi)
  obtain ⟨y, hy, hyx⟩ := hx.2 i j hlt
  have hyX : y = (X : Matrix (Fin n) (Fin n) 𝒪[k]) i j := by
    apply FaithfulSMul.algebraMap_injective 𝒪[k] k
    rw [hyx, ← hX]
    rfl
  rw [← hyX]
  have hia : (a : ℕ) < (G.bl i : ℕ) := not_le.mp hi
  have hle : cc G.μ a ⟨a + 1, h1⟩ ≤ cc G.μ (G.bl j) (G.bl i) :=
    G.ball (G.bl j) a ⟨a + 1, h1⟩ (G.bl i) hj (Fin.lt_def.mpr (Nat.lt_succ_self _)) (Fin.le_def.mpr hia)
  exact Ideal.pow_le_pow_right hle hy

theorem delta_eq {n : ℕ} (G : Grp k n) (a : Fin G.s) (X : Matrix (Fin n) (Fin n) 𝒪[k]) (x : GL (Fin n) k)
    (hx : (x : Matrix (Fin n) (Fin n) k) = X.map (algebraMap 𝒪[k] k)) :
    G.Δ a x = algebraMap 𝒪[k] k (X.submatrix (Subtype.val : {i : Fin n // G.bl i ≤ a} → Fin n) Subtype.val).det := by
  unfold Grp.Δ
  rw [hx, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem coe_map_eq {n : ℕ} (X : GL (Fin n) 𝒪[k]) (x : GL (Fin n) k)
    (hX : Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) X = x) :
    (x : Matrix (Fin n) (Fin n) k) = (X : Matrix (Fin n) (Fin n) 𝒪[k]).map (algebraMap 𝒪[k] k) := by
  rw [← hX]; rfl

end UpperTheory.TNZ.Grp.P_DMul

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_DMul {n : ℕ} (G : Grp k n) : ModulusMultiplicativeProp G := by
  intro _ hB g hg h hh a h1
  have hab : a ≠ ⟨a + 1, h1⟩ := fun e => by
    have := congrArg Fin.val e
    simp at this
  have hc1 : 1 ≤ cc G.μ a ⟨a + 1, h1⟩ := hB.1 a _ hab
  have hQ : IsLocalRing.maximalIdeal 𝒪[k] ^ cc G.μ a ⟨a + 1, h1⟩ ≤ IsLocalRing.maximalIdeal 𝒪[k] := by
    have := Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal 𝒪[k]) hc1
    rwa [pow_one] at this
  obtain ⟨G', hG'⟩ := hg.1
  obtain ⟨H', hH'⟩ := hh.1
  have uG := P_DMul.minor_isUnit (fun i => G.bl i ≤ a) _ ((Matrix.isUnit_iff_isUnit_det _).mp G'.isUnit)
    (fun i j hi hj => hQ (P_DMul.low G a h1 G' g hG' hg i j hi hj))
  have uH := P_DMul.minor_isUnit (fun i => G.bl i ≤ a) _ ((Matrix.isUnit_iff_isUnit_det _).mp H'.isUnit)
    (fun i j hi hj => hQ (P_DMul.low G a h1 H' h hH' hh i j hi hj))
  have key := P_DMul.minor_mul_sub_mem (fun i => G.bl i ≤ a) _ (G' : Matrix (Fin n) (Fin n) 𝒪[k]) _
    (P_DMul.low G a h1 H' h hH' hh)
  obtain ⟨u, hu1, hu2⟩ := P_DMul.unit_factor _ hQ _ _ _ uG uH key
  refine ⟨u, hu1, ?_⟩
  have hgm := P_DMul.coe_map_eq G' g hG'
  have hhm := P_DMul.coe_map_eq H' h hH'
  have hghm : ((g * h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      ((G' : Matrix (Fin n) (Fin n) 𝒪[k]) * (H' : Matrix (Fin n) (Fin n) 𝒪[k])).map (algebraMap 𝒪[k] k) := by
    rw [Units.val_mul, hgm, hhm, Matrix.map_mul]
  rw [P_DMul.delta_eq G a _ _ hghm, P_DMul.delta_eq G a _ _ hgm, P_DMul.delta_eq G a _ _ hhm, ← map_mul, ← map_mul]
  exact congrArg _ hu2

end UpperTheory.TNZ.Grp
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SphericalOfUnramified
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

theorem step_sphOfUnr : SphericalOfUnramifiedProp := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc H d v hv hd
  obtain ⟨⟨n, c⟩, rfl⟩ := H.bij.2 v
  have hn : n = d := by rw [← hd, H.dim]
  subst hn
  exact ⟨c.rep.V, inferInstance, inferInstance, c.rep.ρ, c.rep.smooth, c.rep.irr, (H.sph ⟨n, c⟩).2 hv,
    congrArg rc (IrrGL.of_rep ⟨n, c⟩)⟩

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PArtinIne
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

namespace P_artinIne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ}

theorem val_ine (ha : IsLocalArtin h a) (t : Ine (F := E) A) :
    valuation (w.adicCompletion E) ((a (ineIncl h t) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
  have h0 := ha.ord_eq (ineIncl h t)
  rw [deg_ineIncl, neg_zero] at h0
  exact ord_eq_zero_iff.mp h0

theorem exists_ine (ha : IsLocalArtin h a) (u : (w.adicCompletion E)ˣ)
    (hu : valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1) :
    ∃ t : Ine (F := E) A, a (ineIncl h t) = u := by
  obtain ⟨σ, hσ⟩ := ha.surj u
  have h0 := ha.ord_eq σ
  rw [hσ, ord_eq_zero hu] at h0
  have hd : deg σ = 0 := by omega
  refine ⟨⟨(σ : G E Ω), deg_eq_zero_iff.mp hd⟩, ?_⟩
  have e : ineIncl h ⟨(σ : G E Ω), deg_eq_zero_iff.mp hd⟩ = σ := Subtype.ext rfl
  rw [e, hσ]

end P_artinIne

theorem step_artinIne : ArtinInertiaProp := by
  intro E Ω _ _ _ _ _ A w h a ha
  exact ⟨P_artinIne.val_ine ha, P_artinIne.exists_ine ha⟩

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PTwistRc
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

theorem step_twistRc : TwistRestrictionProp := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc H d X _ _ σ hs hi η hη
  refine ⟨isSmooth_twist hs hη.detChar, isIrreducible_twist hi _, ?_⟩
  rw [← IrrGL.tw_of (hχ := hη), H.twist, H.one]

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SubrepresentationTransport
noncomputable section

namespace UpperTheory.NonzeroTypeTheory

namespace SubrepresentationTransport

variable {K : Type} [Group K] {m : ℕ}

def transport (V : Representation ℂ K (Fin m → ℂ)) (S : Submodule ℂ (Fin m → ℂ))
    (hS : ∀ k, ∀ s ∈ S, V k s ∈ S) {d : ℕ} (e : (Fin d → ℂ) ≃ₗ[ℂ] S) : Representation ℂ K (Fin d → ℂ) where
  toFun k := e.symm.toLinearMap ∘ₗ (V k).restrict (fun s hs => hS k s hs) ∘ₗ e.toLinearMap
  map_one' := by
    refine LinearMap.ext fun v => ?_
    apply e.injective
    apply Subtype.ext
    simp [LinearMap.restrict_apply]
  map_mul' a b := by
    refine LinearMap.ext fun v => ?_
    apply e.injective
    apply Subtype.ext
    simp [LinearMap.restrict_apply]

lemma transport_apply (V : Representation ℂ K (Fin m → ℂ)) (S : Submodule ℂ (Fin m → ℂ))
    (hS : ∀ k, ∀ s ∈ S, V k s ∈ S) {d : ℕ} (e : (Fin d → ℂ) ≃ₗ[ℂ] S) (k : K) (v : Fin d → ℂ) :
    ((e (transport V S hS e k v) : S) : Fin m → ℂ) = V k (e v) := by
  simp [transport, LinearMap.restrict_apply]

end SubrepresentationTransport

open SubrepresentationTransport in
theorem minimalSubrepresentation_holds : SmoothRepMinimalSubrepresentation := by
  intro K _ _ _ m V hV S hS0 hS hmin
  set d := Module.finrank ℂ S
  let e : (Fin d → ℂ) ≃ₗ[ℂ] S := (Module.finBasis ℂ S).equivFun.symm
  let ξ := transport V S hS e
  let ι : (Fin d → ℂ) →ₗ[ℂ] (Fin m → ℂ) := S.subtype ∘ₗ e.toLinearMap
  have hι : ∀ v, ι v = ((e v : S) : Fin m → ℂ) := fun v => rfl
  have hinj : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hint : ∀ k v, V k (ι v) = ι (ξ k v) := by
    intro k v
    rw [hι, hι]
    exact (transport_apply V S hS e k v).symm
  have hrange : LinearMap.range ι = S := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (e v).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by rw [hι]; simp⟩
  refine ⟨d, ξ, ι, hinj, hrange, hint, ?_, ?_⟩
  · have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.mpr hS0
    have : Nontrivial (Fin d → ℂ) := e.toEquiv.nontrivial
    have hne : (⊥ : Subrepresentation ξ) ≠ ⊤ := by
      intro h
      have h' := congrArg Subrepresentation.toSubmodule h
      exact bot_ne_top h'
    have : Nontrivial (Subrepresentation ξ) := ⟨⟨⊥, ⊤, hne⟩⟩
    refine { eq_bot_or_eq_top := ?_ }
    intro W
    have hle : W.toSubmodule.map ι ≤ S := by
      rw [← hrange]
      exact LinearMap.map_le_range
    have hst : ∀ k, ∀ s ∈ W.toSubmodule.map ι, V k s ∈ W.toSubmodule.map ι := by
      rintro k s ⟨w, hw, rfl⟩
      exact ⟨ξ k w, W.apply_mem_toSubmodule k hw, (hint k w).symm⟩
    rcases hmin _ hle hst with h | h
    · left
      apply Subrepresentation.toSubmodule_injective
      apply Submodule.map_injective_of_injective hinj
      rw [h]
      exact (Submodule.map_bot ι).symm
    · right
      apply Subrepresentation.toSubmodule_injective
      apply Submodule.map_injective_of_injective hinj
      rw [h, ← hrange, LinearMap.range_eq_map]
      rfl
  · intro v
    have hset : {k : K | ξ k v = v} = {k : K | V k (ι v) = ι v} := by
      ext k
      change ξ k v = v ↔ V k (ι v) = ι v
      rw [hint]
      exact hinj.eq_iff.symm
    rw [hset]
    exact hV (ι v)

end UpperTheory.NonzeroTypeTheory
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SchurKernelSubmodule
noncomputable section

namespace UpperTheory.NonzeroTypeTheory

namespace SchurKernelSubmodule

def kerSub {K : Type} [Group K] {d : ℕ} (ξ : Representation ℂ K (Fin d → ℂ)) {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ K W) (g : (Fin d → ℂ) →ₗ[ℂ] W)
    (hint : ∀ k v, g (ξ k v) = ρ k (g v)) : Subrepresentation ξ :=
  ⟨LinearMap.ker g, fun k v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hint, hv, map_zero]⟩

end SchurKernelSubmodule

open SchurKernelSubmodule in
theorem schurInjective_holds : SchurInjectiveFromIrreducible := by
  intro K _ d ξ hξ W _ _ ρ g hg hint
  haveI : IsSimpleOrder (Subrepresentation ξ) := hξ
  rcases eq_bot_or_eq_top (kerSub ξ ρ g hint) with h | h
  · rw [← LinearMap.ker_eq_bot]
    have hk := congrArg Subrepresentation.toSubmodule h
    first
      | exact hk
      | simpa [kerSub] using hk
  · exfalso
    apply hg
    rw [← LinearMap.ker_eq_top]
    have hk := congrArg Subrepresentation.toSubmodule h
    first
      | exact hk
      | simpa [kerSub] using hk

end UpperTheory.NonzeroTypeTheory
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.MaschkeCompactGroup
noncomputable section

namespace UpperTheory.NonzeroTypeTheory.MaschkeCompactGroup

variable {K : Type} [Group K] {m : ℕ}

theorem ker_isOpen [TopologicalSpace K] [IsTopologicalGroup K] (V : Representation ℂ K (Fin m → ℂ))
    (hs : GlobalTheory.PRep.IsSmooth V) : IsOpen ((MonoidHom.ker V : Subgroup K) : Set K) := by
  refine Subgroup.isOpen_of_mem_nhds (MonoidHom.ker V) (g := 1) (Filter.mem_of_superset
    ((isOpen_iInter_of_finite fun i : Fin m => hs (Pi.single i 1)).mem_nhds (by simp)) fun g hg => ?_)
  refine MonoidHom.mem_ker.2 ((Pi.basisFun ℂ (Fin m)).ext fun i => ?_)
  rw [Pi.basisFun_apply]
  exact Set.mem_iInter.1 hg i

theorem maschke [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    (V : Representation ℂ K (Fin m → ℂ)) (hs : GlobalTheory.PRep.IsSmooth V)
    (U : Submodule ℂ (Fin m → ℂ)) (hU : ∀ k, ∀ u ∈ U, V k u ∈ U) :
    ∃ S : Submodule ℂ (Fin m → ℂ), IsCompl U S ∧ ∀ k, ∀ s ∈ S, V k s ∈ S := by
  classical
  have : Finite (K ⧸ MonoidHom.ker V) := Subgroup.quotient_finite_of_isOpen _ (ker_isOpen V hs)
  let _ : Fintype (K ⧸ MonoidHom.ker V) := Fintype.ofFinite _
  let ρ : K ⧸ MonoidHom.ker V →* Module.End ℂ (Fin m → ℂ) :=
    QuotientGroup.lift (MonoidHom.ker V) V le_rfl
  have hρ : ∀ k : K, ρ (k : K ⧸ MonoidHom.ker V) = V k := fun k => rfl
  have hmul : ∀ a b : K ⧸ MonoidHom.ker V, ∀ w, ρ a (ρ b w) = ρ (a * b) w := fun a b w => by
    rw [map_mul]; rfl
  have hρU : ∀ g, ∀ u ∈ U, ρ g u ∈ U := by
    intro g u hu
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    rw [hρ]
    exact hU k u hu
  obtain ⟨T, hT⟩ := Submodule.exists_isCompl U
  let π := U.projection T hT
  have hπU : ∀ v, π v ∈ U := fun v => Submodule.projection_apply_mem hT v
  have hπid : ∀ u ∈ U, π u = u := fun u hu => Submodule.projection_apply_of_mem_left hT hu
  let P : Module.End ℂ (Fin m → ℂ) := ∑ g : K ⧸ MonoidHom.ker V, (ρ g).comp (π.comp (ρ g⁻¹))
  have hP : ∀ v, P v = ∑ g : K ⧸ MonoidHom.ker V, ρ g (π (ρ g⁻¹ v)) := fun v => by
    simp only [P, LinearMap.sum_apply, LinearMap.comp_apply]
  have hPU : ∀ v, P v ∈ U := fun v => by
    rw [hP]
    exact Submodule.sum_mem _ fun g _ => hρU g _ (hπU _)
  have hPid : ∀ u ∈ U, P u = Fintype.card (K ⧸ MonoidHom.ker V) • u := by
    intro u hu
    have h1 : ∀ g : K ⧸ MonoidHom.ker V, ρ g (π (ρ g⁻¹ u)) = u := fun g => by
      rw [hπid _ (hρU _ _ hu), hmul, mul_inv_cancel, map_one]
      rfl
    rw [hP, Finset.sum_congr rfl fun g _ => h1 g, Finset.sum_const, Finset.card_univ]
  have hPeq : ∀ h v, P (ρ h v) = ρ h (P v) := by
    intro h v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hP, hP, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun x => ?_
    simp only [Equiv.coe_mulLeft]
    rw [hmul h, mul_inv_cancel_left, mul_inv_rev, inv_inv, ← hmul]
  have hc : (Fintype.card (K ⧸ MonoidHom.ker V) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let f : (Fin m → ℂ) →ₗ[ℂ] U :=
    LinearMap.codRestrict U (((Fintype.card (K ⧸ MonoidHom.ker V) : ℂ)⁻¹) • P)
      (fun v => U.smul_mem _ (hPU v))
  have hf : ∀ x : U, f x = x := by
    intro x
    apply Subtype.ext
    change ((Fintype.card (K ⧸ MonoidHom.ker V) : ℂ)⁻¹) • P x = x
    rw [hPid _ x.2, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hker : ∀ x, x ∈ LinearMap.ker f ↔ P x = 0 := by
    intro x
    rw [LinearMap.mem_ker, ← Submodule.coe_eq_zero]
    change ((Fintype.card (K ⧸ MonoidHom.ker V) : ℂ)⁻¹) • P x = 0 ↔ P x = 0
    rw [smul_eq_zero]
    simp [hc]
  refine ⟨LinearMap.ker f, LinearMap.isCompl_of_proj hf, fun k s hs => ?_⟩
  rw [hker] at hs ⊢
  rw [← hρ, hPeq, hs, map_zero]

end UpperTheory.NonzeroTypeTheory.MaschkeCompactGroup

namespace UpperTheory.NonzeroTypeTheory

open MaschkeCompactGroup in
theorem invariantComplement_holds : SmoothRepIrreducibleSubcontainingVector := by
  intro K _ _ _ _ m V hs v0 hv0
  classical
  have hbot : (∀ k, ∀ w ∈ (⊥ : Submodule ℂ (Fin m → ℂ)), V k w ∈ (⊥ : Submodule ℂ (Fin m → ℂ))) ∧
      v0 ∉ (⊥ : Submodule ℂ (Fin m → ℂ)) := by
    refine ⟨fun k w hw => ?_, fun h => hv0 ((Submodule.mem_bot ℂ).1 h)⟩
    rw [Submodule.mem_bot] at hw ⊢
    rw [hw, map_zero]
  obtain ⟨U, ⟨hUst, hv0U⟩, hUmax⟩ := set_has_maximal_iff_noetherian.mpr inferInstance
    {W : Submodule ℂ (Fin m → ℂ) | (∀ k, ∀ w ∈ W, V k w ∈ W) ∧ v0 ∉ W} ⟨⊥, hbot⟩
  obtain ⟨S, hUS, hSst⟩ := maschke V hs U hUst
  let p := S.projection U hUS.symm
  have hpS : ∀ v, p v ∈ S := fun v => Submodule.projection_apply_mem hUS.symm v
  have hpid : ∀ s ∈ S, p s = s := fun s hs => Submodule.projection_apply_of_mem_left hUS.symm hs
  have hp0 : ∀ v, p v = 0 ↔ v ∈ U := fun v => Submodule.projection_apply_eq_zero_iff hUS.symm
  have hdec : ∀ v, v - p v ∈ U := fun v => Submodule.sub_projection_mem hUS.symm v
  have hpU : ∀ u ∈ U, p u = 0 := fun u hu => (hp0 u).2 hu
  have hpv0 : p v0 ≠ 0 := fun h => hv0U ((hp0 v0).1 h)

  have key : ∀ W : Submodule ℂ (Fin m → ℂ), W ≤ S → (∀ k, ∀ w ∈ W, V k w ∈ W) → W ≠ ⊥ → p v0 ∈ W := by
    intro W hWS hWst hW0
    have hsup : ∀ k, ∀ x ∈ U ⊔ W, V k x ∈ U ⊔ W := by
      intro k x hx
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (hUst k u hu) (hWst k w hw)
    have hmem : v0 ∈ U ⊔ W := by
      by_contra hn
      refine hUmax (U ⊔ W) ⟨hsup, hn⟩ (lt_of_le_of_ne le_sup_left fun heq => hW0 ?_)
      refine eq_bot_iff.2 ((le_inf (le_sup_right.trans heq.ge) hWS).trans (disjoint_iff.1 hUS.disjoint).le)
    obtain ⟨u, hu, w, hw, hsum⟩ := Submodule.mem_sup.1 hmem
    rw [← hsum, map_add (f := _), hpU u hu, zero_add, hpid w (hWS hw)]
    exact hw
  refine ⟨S, p, fun h => hpv0 ?_, hSst, fun S' hS'S hS'st => ?_, hpS, hpid, fun k v => ?_, hpv0⟩
  · have := hpS v0
    rw [h, Submodule.mem_bot] at this
    exact this
  · by_cases h0 : S' = ⊥
    · exact Or.inl h0
    right
    have h1 := key S' hS'S hS'st h0
    obtain ⟨T, hST, hTst⟩ := maschke V hs S' hS'st
    have hST0 : S ⊓ T = ⊥ := by
      by_contra hn
      have h2 := key (S ⊓ T) inf_le_left
        (fun k x hx => Submodule.mem_inf.2 ⟨hSst k x (Submodule.mem_inf.1 hx).1, hTst k x (Submodule.mem_inf.1 hx).2⟩) hn
      have h3 : p v0 ∈ S' ⊓ T := Submodule.mem_inf.2 ⟨h1, (Submodule.mem_inf.1 h2).2⟩
      rw [disjoint_iff.1 hST.disjoint, Submodule.mem_bot] at h3
      exact hpv0 h3
    refine le_antisymm hS'S fun s hs => ?_
    have hs' : s ∈ S' ⊔ T := by rw [hST.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, t, ht, hat⟩ := Submodule.mem_sup.1 hs'
    have htS : t ∈ S := by
      have : t = s - a := by rw [← hat]; abel
      rw [this]
      exact S.sub_mem hs (hS'S ha)
    have ht0 : t = 0 := by
      have : t ∈ S ⊓ T := Submodule.mem_inf.2 ⟨htS, ht⟩
      rwa [hST0, Submodule.mem_bot] at this
    rw [← hat, ht0, add_zero]
    exact ha
  · have hv : V k v = V k (p v) + V k (v - p v) := by
      rw [← map_add (f := _)]
      congr 1
      abel
    rw [hv, map_add (f := _), hpid _ (hSst k _ (hpS v)), hpU _ (hUst k _ (hdec v)), add_zero]

end UpperTheory.NonzeroTypeTheory
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.GEmb
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct

namespace UpperTheory.TNZ

theorem gEmb (e1 : TensorProductVectors) (e2 : LeviSubgroupRestriction) (e3 : ParabolicInductionKernel) (e4 : InducedDeterminantTwist)
    (e5 : InductionExtension) : GEmb := by
  intro k _ _ _ _ n G V _ _ π hπ
  obtain ⟨X, instA, instM, σ, -, -, hdet, ⟨e⟩⟩ := hπ
  let _ := instA
  let _ := instM
  obtain ⟨v, hv0, hv⟩ := e1 k G.s G.d X σ G.μ hdet
  choose F hF using fun φ : ↥G.V0sp => e5 e2 e3 k n G X σ v hv φ.1 φ.2
  have hadd : ∀ φ ψ, F (φ + ψ) = F φ + F ψ := fun φ ψ =>
    e4 k G.s n G.d G.hd _ (piTensor σ) _ _ fun κ hκ => by
      have h1 := hF (φ + ψ) ⟨κ, hκ⟩
      have h2 := hF φ ⟨κ, hκ⟩
      have h3 := hF ψ ⟨κ, hκ⟩
      change _ = (F φ).1.1 κ + (F ψ).1.1 κ
      rw [h1, h2, h3, ← add_smul]
      rfl
  have hsmul : ∀ (c : ℂ) φ, F (c • φ) = c • F φ := fun c φ =>
    e4 k G.s n G.d G.hd _ (piTensor σ) _ _ fun κ hκ => by
      have h1 := hF (c • φ) ⟨κ, hκ⟩
      have h2 := hF φ ⟨κ, hκ⟩
      change _ = c • (F φ).1.1 κ
      rw [h1, h2, smul_smul]
      rfl
  let f0 : ↥G.V0sp →ₗ[ℂ] IndSp G.e (piTensor σ) :=
    { toFun := F, map_add' := hadd, map_smul' := hsmul }
  refine ⟨e.symm.toLinearEquiv.toLinearMap ∘ₗ f0, fun φ ψ h => ?_, fun κ φ φ' hφ' => ?_⟩
  · have h' : F φ = F ψ := e.symm.toLinearEquiv.injective h
    refine Subtype.ext (funext fun κ => ?_)
    have h2 := congrArg (fun F : IndSp G.e (piTensor σ) => F.1.1 (κ : GL (Fin n) k)) h'
    simp only [hF] at h2
    exact smul_left_injective ℂ hv0 h2
  · have key : F φ' = parInd G.e (piTensor σ) (κ : GL (Fin n) k) (F φ) :=
      e4 k G.s n G.d G.hd _ (piTensor σ) _ _ fun x hx => by
        rw [hF φ' ⟨x, hx⟩, parInd_apply, hF φ ⟨x * κ, mul_mem hx κ.2⟩, hφ']
        rfl
    change e.symm.toLinearEquiv (F φ') = π κ (e.symm.toLinearEquiv (F φ))
    rw [key, Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply]
    exact Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap (κ : GL (Fin n) k) (F φ)

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PIndExt
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct Pointwise

namespace UpperTheory.TNZ

namespace P_indExt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_inPow (r : ℕ) : IsOpen {x : k | InPow r x} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have hne : ((ϖ : k) ^ r) ≠ 0 := pow_ne_zero _ fun h => hϖ.ne_zero (Subtype.ext h)
  have e : {x : k | InPow r x} = ((ϖ : k) ^ r) • (𝒪[k] : Set k) := by
    ext x
    simp only [Set.mem_ofPred_eq, InPow, Set.mem_smul_set, smul_eq_mul]
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      exact ⟨(z : k), z.2, by simp only [map_mul, map_pow]; rw [mul_comm]; rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨ϖ ^ r * ⟨z, hz⟩, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _), by simp only [map_mul, map_pow]; rfl⟩
  have hO : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  rw [e]
  exact hO.smul₀ hne

theorem isOpen_KC (n r : ℕ) : IsOpen (KC k n r) := by
  have e : KC k n r = (KO k (Fin n) : Set (GL (Fin n) k)) ∩ ⋂ i, ⋂ j,
      (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j - if i = j then 1 else 0) ⁻¹'
        {x | InPow r x} := by
    ext g
    simp only [KC, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [e]
  refine GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  exact (isOpen_inPow r).preimage ((Units.continuous_val.matrix_elem i j).sub continuous_const)

theorem one_mem_KC (n r : ℕ) : (1 : GL (Fin n) k) ∈ KC k n r := by
  refine ⟨one_mem _, fun i j => ⟨0, zero_mem _, ?_⟩⟩
  by_cases h : i = j
  · subst h; simp
  · simp [h, Matrix.one_apply_ne h]

section Ext

variable {n : ℕ} (G : Grp k n) {X : Fin G.s → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  (σ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (X a))

def extFun (φ : ↥(KO k (Fin n)) → ℂ) (v : ⨂[ℂ] a, X a) (x : GL (Fin n) k) : ⨂[ℂ] a, X a :=
  (deltaHalf k (fun a => Fin (G.d a)) (leviProj k G.e (MultiIrr.exists_parab_mul G.e x).choose) : ℂ) •
    piTensor σ (leviProj k G.e (MultiIrr.exists_parab_mul G.e x).choose)
      (φ ⟨(MultiIrr.exists_parab_mul G.e x).choose_spec.choose,
        (MultiIrr.exists_parab_mul G.e x).choose_spec.choose_spec.1⟩ • v)

variable {G σ}

theorem expr_eq (hL : LeviSubgroupRestriction) (hP : ParabolicInductionKernel) {φ : ↥(KO k (Fin n)) → ℂ} (hφ : φ ∈ G.V0sp)
    {v : ⨂[ℂ] a, X a}
    (hv : ∀ m : Levi k (fun a => Fin (G.d a)), (∀ a, m a ∈ KO k (Fin (G.d a))) →
      piTensor σ m v = (∏ a, ((G.μ a (GeneralLinearGroup.det (m a)) : ℂˣ) : ℂ)) • v)
    (p p' : parab k G.e) (w w' : GL (Fin n) k) (hw : w ∈ KO k (Fin n)) (hw' : w' ∈ KO k (Fin n))
    (he : (p : GL (Fin n) k) * w = p' * w') :
    (deltaHalf k (fun a => Fin (G.d a)) (leviProj k G.e p') : ℂ) • piTensor σ (leviProj k G.e p') (φ ⟨w', hw'⟩ • v) =
      (deltaHalf k (fun a => Fin (G.d a)) (leviProj k G.e p) : ℂ) • piTensor σ (leviProj k G.e p) (φ ⟨w, hw⟩ • v) := by
  obtain ⟨hφ1, -⟩ := hφ
  obtain ⟨q, rfl⟩ : ∃ q : parab k G.e, p = p' * q := ⟨p'⁻¹ * p, (mul_inv_cancel_left p' p).symm⟩
  have hw'eq : w' = (q : GL (Fin n) k) * w := by
    rw [Subgroup.coe_mul, mul_assoc] at he
    exact (mul_left_cancel he).symm
  have hqK : (q : GL (Fin n) k) ∈ KO k (Fin n) := by
    have : (q : GL (Fin n) k) = w' * w⁻¹ := by rw [hw'eq, mul_inv_cancel_right]
    rw [this]
    exact mul_mem hw' (inv_mem hw)
  subst hw'eq
  have h1 : φ ⟨(q : GL (Fin n) k) * w, hw'⟩ = G.lam (q : GL (Fin n) k) * φ ⟨w, hw⟩ :=
    hφ1 ⟨q, hqK⟩ ⟨hqK, q.2⟩ ⟨w, hw⟩
  have hP' := hP k G.s n G.d G.hd q hqK
  have hδ : deltaHalf k (fun a => Fin (G.d a)) (leviProj k G.e q) = 1 := hP'.2
  have hρ : piTensor σ (leviProj k G.e q) v = G.lam (q : GL (Fin n) k) • v := by
    rw [hv _ hP'.1, hL k n G q hqK]
  rw [(leviProj k G.e).map_mul p' q, (deltaHalf k (fun a => Fin (G.d a))).map_mul, hδ, mul_one,
    (piTensor σ).map_mul, Module.End.mul_apply, map_smul (piTensor σ (leviProj k G.e q)), hρ, h1, smul_smul, mul_comm]

theorem extFun_mul (hL : LeviSubgroupRestriction) (hP : ParabolicInductionKernel) {φ : ↥(KO k (Fin n)) → ℂ} (hφ : φ ∈ G.V0sp)
    {v : ⨂[ℂ] a, X a}
    (hv : ∀ m : Levi k (fun a => Fin (G.d a)), (∀ a, m a ∈ KO k (Fin (G.d a))) →
      piTensor σ m v = (∏ a, ((G.μ a (GeneralLinearGroup.det (m a)) : ℂˣ) : ℂ)) • v)
    (p : parab k G.e) (w : GL (Fin n) k) (hw : w ∈ KO k (Fin n)) :
    extFun G σ φ v ((p : GL (Fin n) k) * w) =
      (deltaHalf k (fun a => Fin (G.d a)) (leviProj k G.e p) : ℂ) • piTensor σ (leviProj k G.e p) (φ ⟨w, hw⟩ • v) := by
  obtain ⟨hw', he⟩ := (MultiIrr.exists_parab_mul G.e ((p : GL (Fin n) k) * w)).choose_spec.choose_spec
  exact expr_eq hL hP hφ hv p _ w _ hw hw' he

theorem extFun_mem (hL : LeviSubgroupRestriction) (hP : ParabolicInductionKernel) {φ : ↥(KO k (Fin n)) → ℂ} (hφ : φ ∈ G.V0sp)
    {v : ⨂[ℂ] a, X a}
    (hv : ∀ m : Levi k (fun a => Fin (G.d a)), (∀ a, m a ∈ KO k (Fin (G.d a))) →
      piTensor σ m v = (∏ a, ((G.μ a (GeneralLinearGroup.det (m a)) : ℂˣ) : ℂ)) • v) :
    extFun G σ φ v ∈ indSpace (parab k G.e)
      ((twist (piTensor σ) (deltaHalf k (fun a => Fin (G.d a)))).comp (leviProj k G.e)) := by
  intro h g
  obtain ⟨p, w, hw, rfl⟩ := MultiIrr.exists_parab_mul G.e g
  rw [← mul_assoc, ← Subgroup.coe_mul, extFun_mul hL hP hφ hv (h * p) w hw, extFun_mul hL hP hφ hv p w hw]
  generalize φ ⟨w, hw⟩ • v = x
  rw [MonoidHom.comp_apply, twist_apply, map_smul, smul_smul, (leviProj k G.e).map_mul,
    (deltaHalf k (fun a => Fin (G.d a))).map_mul, Units.val_mul, (piTensor σ).map_mul, Module.End.mul_apply]

theorem exists_ext (hL : LeviSubgroupRestriction) (hP : ParabolicInductionKernel) {φ : ↥(KO k (Fin n)) → ℂ} (hφ : φ ∈ G.V0sp)
    {v : ⨂[ℂ] a, X a}
    (hv : ∀ m : Levi k (fun a => Fin (G.d a)), (∀ a, m a ∈ KO k (Fin (G.d a))) →
      piTensor σ m v = (∏ a, ((G.μ a (GeneralLinearGroup.det (m a)) : ℂˣ) : ℂ)) • v) :
    ∃ F : IndSp G.e (piTensor σ), ∀ κ : ↥(KO k (Fin n)), F.1.1 κ = φ κ • v := by
  have hφ' := hφ
  obtain ⟨-, hφ2⟩ := hφ'
  refine ⟨⟨⟨extFun G σ φ v, extFun_mem hL hP hφ hv⟩, ?_⟩, fun κ => ?_⟩
  · refine mem_smoothPart_of_nhds (Filter.mem_of_superset ((isOpen_KC n G.lev).mem_nhds (one_mem_KC n G.lev))
      fun u hu => ?_)
    refine Subtype.ext (funext fun x => ?_)
    show extFun G σ φ v (x * u) = extFun G σ φ v x
    obtain ⟨p, w, hw, rfl⟩ := MultiIrr.exists_parab_mul G.e x
    have h2 : φ ⟨w * u, mul_mem hw hu.1⟩ = φ ⟨w, hw⟩ := hφ2 ⟨w, hw⟩ ⟨u, hu.1⟩ hu
    rw [mul_assoc, extFun_mul hL hP hφ hv p (w * u) (mul_mem hw hu.1), h2, extFun_mul hL hP hφ hv p w hw]
  · have h := extFun_mul hL hP hφ hv 1 κ κ.2
    rw [Subgroup.coe_one, one_mul] at h
    show extFun G σ φ v κ = _
    rw [h, map_one, map_one, map_one, Units.val_one, one_smul, Module.End.one_apply]

end Ext

end P_indExt

theorem step_indExt : InductionExtension := by
  intro hL hP k _ _ _ _ n G X _ _ σ v hv φ hφ
  exact P_indExt.exists_ext hL hP hφ hv

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ParabolicMaximalCompact
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace ParabolicMaximalCompact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem leviProj_mem_KO {s n : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = n) (p : parab k (stdBlocks d hd))
    (hp : (p : GL (Fin n) k) ∈ KO k (Fin n)) (a : Fin s) :
    leviProj k (stdBlocks d hd) p a ∈ KO k (Fin (d a)) := by
  rw [GlobalTheory.StepData.mem_KO] at hp ⊢
  have hinv : ((GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.stdBlocks d hd) p a)⁻¹ :
      GL (Fin (d a)) k) =
      GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.stdBlocks d hd) p⁻¹ a := by
    rw [map_inv, Pi.inv_apply]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [GlobalTheory.SmGL.leviProj_apply]
    exact hp.1 _ _
  · rw [hinv, GlobalTheory.SmGL.leviProj_apply]
    exact hp.2 _ _

end ParabolicMaximalCompact

theorem step_parabKO : ParabolicInductionKernel := by
  intro k _ _ _ _ s n d hd p hp
  have h := fun a => ParabolicMaximalCompact.leviProj_mem_KO d hd p hp a
  exact ⟨h, deltaHalf_of_mem_leviK ((Subgroup.mem_pi _).2 fun a _ => h a)⟩

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PLamLevi
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace P_lamLevi

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tele {H : Type} [CommGroup H] (ν : ℕ → H) (b : ℕ) :
    ∀ s, b ≤ s → ∏ i ∈ Finset.range s, (if b ≤ i then ν i / ν (i + 1) else 1) = ν b / ν s := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base =>
    rw [div_self', Finset.prod_eq_one]
    intro i hi
    rw [if_neg (by simpa using hi)]
  | succ s hbs ih =>
    rw [Finset.prod_range_succ, ih, if_pos hbs, div_mul_div_cancel]

variable {n : ℕ} (G : Grp k n)

theorem prod_ge (b : Fin G.s) :
    ∏ a : Fin G.s, (if b ≤ a then G.μ a / G.μnext a else 1) = G.μ b := by
  let ν : ℕ → (kˣ →* ℂˣ) := fun i => if h : i < G.s then G.μ ⟨i, h⟩ else 1
  have h1 : ∀ a : Fin G.s, (if b ≤ a then G.μ a / G.μnext a else 1) =
      (fun i : ℕ => if (b : ℕ) ≤ i then ν i / ν (i + 1) else 1) a := by
    intro a
    have ha : ν a = G.μ a := by simp [ν, a.isLt]
    have hn : ν (a + 1) = G.μnext a := rfl
    simp only [ha, hn, Fin.le_iff_val_le_val]
  rw [Finset.prod_congr rfl (fun a _ => h1 a),
    Fin.prod_univ_eq_prod_range (fun i : ℕ => if (b : ℕ) ≤ i then ν i / ν (i + 1) else 1) G.s,
    tele ν b G.s b.isLt.le]
  have hb : ν b = G.μ b := by simp [ν, b.isLt]
  have hs : ν G.s = 1 := by simp [ν]
  rw [hb, hs, div_one]

theorem Δ_parab (p : parab k G.e) (a : Fin G.s) :
    G.Δ a (p : GL (Fin n) k) =
      ((∏ b : Fin G.s, (if b ≤ a then GeneralLinearGroup.det (leviProj k G.e p b) else 1) : kˣ) : k) := by
  unfold Grp.Δ
  set M' : Matrix {i : Fin n // G.bl i ≤ a} {i : Fin n // G.bl i ≤ a} k :=
    ((p : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).submatrix Subtype.val Subtype.val with hM'
  have hbt : M'.BlockTriangular (fun i => G.bl i.val) := fun i j h => p.2 h
  rw [BlockTriangular.det_fintype hbt, Units.coe_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  split_ifs with hb
  · rw [GeneralLinearGroup.val_det_apply]
    let f : Fin (G.d b) ≃ {j : {i : Fin n // G.bl i ≤ a} // G.bl j.val = b} :=
      Equiv.ofBijective (fun i => ⟨⟨G.e ⟨b, i⟩, by simp [Grp.bl, hb]⟩, by simp [Grp.bl]⟩) ⟨fun i j h => by
        simpa using h, by
          rintro ⟨⟨i, hi⟩, hib⟩
          obtain ⟨⟨c, j⟩, rfl⟩ := G.e.surjective i
          obtain rfl : c = b := by simpa [Grp.bl] using hib
          exact ⟨j, rfl⟩⟩
    rw [← det_submatrix_equiv_self f]
    rfl
  · have : IsEmpty {j : {i : Fin n // G.bl i ≤ a} // G.bl j.val = b} :=
      ⟨fun j => hb (j.2 ▸ j.1.2)⟩
    rw [det_isEmpty, Units.val_one]

end P_lamLevi

open P_lamLevi in
theorem step_lamLevi : LeviSubgroupRestriction := by
  intro k _ _ _ _ n G p _
  set D : Fin G.s → kˣ := fun b => GeneralLinearGroup.det (leviProj k G.e p b) with hD
  have hΔ : ∀ a, G.Δ a (p : GL (Fin n) k) = ((∏ b, (if b ≤ a then D b else 1) : kˣ) : k) :=
    fun a => Δ_parab G p a
  have hchk : ∀ a, Grp.chk (G.μ a / G.μnext a) (G.Δ a (p : GL (Fin n) k)) =
      (((G.μ a / G.μnext a) (∏ b, (if b ≤ a then D b else 1)) : ℂˣ) : ℂ) := by
    intro a
    rw [Grp.chk, dite_eq_right (by rw [hΔ a]; exact Units.ne_zero _)]
    congr 3
    ext
    simp [hΔ a]
  unfold Grp.lam
  rw [Finset.prod_congr rfl (fun a _ => hchk a), ← Units.coe_prod, ← Units.coe_prod]
  congr 1
  simp_rw [map_prod, apply_ite (G.μ _ / G.μnext _), map_one]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← prod_ge G b, MonoidHom.finsetProd_apply]
  refine Finset.prod_congr rfl fun a _ => ?_
  split_ifs <;> simp [hD]

end UpperTheory.TNZ
end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel UpperTheory.TNZ

namespace UpperTheory.NonzeroTypeTheory

theorem cSteps_all
     :
    CSteps := by
  intro k _ _ _ _
  exact ⟨Grp.step_ccBasic (k := k), Grp.step_unif (k := k), Grp.step_exGrp (k := k), fun n G => ⟨Grp.step_ccBound (G := G), Grp.step_Jone (G := G), Grp.step_Jmul (G := G), Grp.step_Jinv (G := G), Grp.step_KC (G := G), Grp.step_DUnit (G := G), Grp.step_DMul (G := G), Grp.step_lamMul (G := G), Grp.step_lamBasic (G := G), Grp.step_lamUnip (G := G), Grp.step_iwahori (G := G), Grp.step_V0stable (G := G), Grp.step_V0fin (G := G), Grp.leviEigenvector_holds (G := G), Grp.step_PJ (G := G), Grp.step_kill (G := G), Grp.step_nonint (G := G), Grp.step_TzE (G := G), Grp.step_Tpow (G := G), Grp.step_jacKer (G := G), Grp.step_TzInj (G := G), Grp.step_jacImage (G := G), Grp.step_jacFin (G := G), Grp.step_subq (G := G), Grp.step_tensor (G := G), Grp.step_suppProd (G := G)⟩⟩

theorem types_nonzero_level_holds (P : GlobalTheory.Mem.LiteralAutomorphy.LitN)
     : NZ :=
  nz_of_steps P invariantComplement_holds minimalSubrepresentation_holds schurInjective_holds artinTransferDecomposition_holds localArtinCharacterProduct_holds finiteDimensionalTranslation_holds twistedSphericalRepresentative_holds distinctOnInertia_holds smoothVectorsFixed_holds
    (gMain step_detVec step_unrTwist step_sumList step_isotypic step_scalarInertia step_sphOfUnr step_sphUnr step_twistRc
      step_untwistRc step_prodRc step_cuspSupp step_prodIrr step_artinIne)
    (gEmb step_tensorVec step_lamLevi step_parabKO step_indDetK step_indExt) step_artinIne
    (fun L => need_CMain (cSteps_all ) step_lamLevi L) (need_CProps (cSteps_all ))
    (need_Grp (cSteps_all ))

end UpperTheory.NonzeroTypeTheory

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.NonzeroTypeTheory.exists_type_for_residual_rep :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∃ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), TypeFor r ι τ₀ :=
  fun P => UpperTheory.NonzeroTypeTheory.typeEx P (UpperTheory.NonzeroTypeTheory.types_nonzero_level_holds P )

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end

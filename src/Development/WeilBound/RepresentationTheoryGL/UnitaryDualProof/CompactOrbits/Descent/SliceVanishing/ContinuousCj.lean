module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.IsClosedGzS
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.NilpotentPowers.IsNilpotentPowSub

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FiberLocalization.EqZeroOfFiberEquivariant
noncomputable section

open Set GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.PfBern.Loc

abbrev SC (X : Type*) [TopologicalSpace X] : Submodule ℂ (X → ℂ) :=
  locallyConstantCompactSupport X ℂ ℂ

abbrev Distr (X : Type*) [TopologicalSpace X] : Type _ := Module.Dual ℂ (SC X)

variable {X : Type*} [TopologicalSpace X]

def mulInd (A : Set X) (hA : IsClopen A) : SC X →ₗ[ℂ] SC X where
  toFun f := ⟨fun x => A.indicator 1 x * (f : X → ℂ) x,
    (indicator_mul_mem (U := univ) hA ⟨f.2, subset_univ _⟩).1⟩
  map_add' f g := Subtype.ext <| funext fun x => by simp [mul_add]
  map_smul' c f := Subtype.ext <| funext fun x => by simp [mul_left_comm]

section General

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [TotallyDisconnectedSpace Y]



end General

section Conj

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [TotallyDisconnectedSpace Y]

end Conj

section Restrict

variable {Z : Set X}

def restr (hZ : IsClosed Z) : SC X →ₗ[ℂ] SC Z where
  toFun f := ⟨fun z => (f : X → ℂ) z,
    ⟨f.2.1.comp_continuous continuous_subtype_val,
      f.2.2.comp_isClosedEmbedding hZ.isClosedEmbedding_subtypeVal⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]

theorem restr_surjective (hZ : IsClosed Z) : Function.Surjective (restr hZ) := by
  intro φ
  obtain ⟨f, hf, hfφ⟩ := exists_lift (U := univ) isOpen_univ (subset_univ Z) φ.2
  exact ⟨⟨f, hf.1⟩, Subtype.ext (funext hfφ)⟩

end Restrict

section FiberSubspace

variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [TotallyDisconnectedSpace Y]


end FiberSubspace

section OpenSubset

variable {U : Set X}




variable [T2Space X]

end OpenSubset

section Transport

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]

def pullL (h : A ≃ₜ B) : SC B →ₗ[ℂ] SC A where
  toFun f := ⟨fun a => (f : B → ℂ) (h a), f.2.1.comp_continuous h.continuous, f.2.2.comp_homeomorph h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pullL_pullL_symm (h : A ≃ₜ B) (f : SC A) : pullL h (pullL h.symm f) = f :=
  Subtype.ext <| funext fun a => by simp [pullL]

end Transport

end PositivityTheory.PfBern.Loc

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.DistrC
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.ExistsQuotientHomeo
noncomputable section

namespace PositivityTheory.RgUd.T.Desc.SLF

open MulAction

variable {G T : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SigmaCompactSpace G]
  [TopologicalSpace T] [T2Space T] [BaireSpace T] [MulAction G T] [ContinuousSMul G T] [IsPretransitive G T]

theorem exists_quotient_homeo (t : T) :
    ∃ e : G ⧸ stabilizer G t ≃ₜ T, ∀ g : G, e (g : G ⧸ stabilizer G t) = g • t := by
  let f : G ⧸ stabilizer G t → T := ofQuotientStabilizer G t
  have hinj : Function.Injective f := injective_ofQuotientStabilizer G t
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨g, hg⟩ := exists_smul_eq G t y
    exact ⟨(g : G ⧸ stabilizer G t), by simp [f, hg]⟩
  have hmk : ∀ g : G, f (g : G ⧸ stabilizer G t) = g • t := fun g => ofQuotientStabilizer_mk G t g
  have hcont : Continuous f := by
    rw [(QuotientGroup.isQuotientMap_mk (stabilizer G t)).continuous_iff]
    have : f ∘ (QuotientGroup.mk : G → G ⧸ stabilizer G t) = fun g => g • t := funext hmk
    rw [this]
    exact continuous_id.smul continuous_const
  have hopen : IsOpenMap f := by
    intro U hU
    have : f '' U = (fun g : G => g • t) '' ((QuotientGroup.mk : G → G ⧸ stabilizer G t) ⁻¹' U) := by
      ext y
      constructor
      · rintro ⟨c, hc, rfl⟩
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
        exact ⟨g, hc, (hmk g).symm⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨_, hg, hmk g⟩
    rw [this]
    exact isOpenMap_smul_of_sigmaCompact t _ (hU.preimage QuotientGroup.continuous_mk)
  exact ⟨(Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopen, hmk⟩

end PositivityTheory.RgUd.T.Desc.SLF
end
end

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Desc.SLF

open PositivityTheory.PfBern.Loc

variable {S : Type*} [TopologicalSpace S] [T2Space S] [LocallyCompactSpace S] [TotallyDisconnectedSpace S]

theorem exists_distr_on (ξ : (S → ℂ) →ₗ[ℂ] ℂ) {C : Set S} (hC : IsClosed C)
    (hξ : ∀ f ∈ supportedIn (Set.univ : Set S), (∀ p ∈ C, f p = 0) → ξ f = 0) :
    ∃ D : Distr C, ∀ f : SC S, ξ f = D (restr hC f) := by
  let ξ' : SC S →ₗ[ℂ] ℂ := ξ ∘ₗ (SC S).subtype
  have hker : LinearMap.ker (restr hC) ≤ LinearMap.ker ξ' := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    apply hξ
    · exact ⟨f.2, Set.subset_univ _⟩
    · intro p hp
      have h0 := congrArg (fun g : SC C => (g : C → ℂ) ⟨p, hp⟩) hf
      simpa [restr] using h0
  let D0 : LinearMap.range (restr hC) →ₗ[ℂ] ℂ :=
    (LinearMap.ker (restr hC)).liftQ ξ' hker ∘ₗ (restr hC).quotKerEquivRange.symm.toLinearMap
  obtain ⟨r, hr⟩ := (LinearMap.range (restr hC)).subtype.exists_leftInverse_of_injective
    (LinearMap.range (restr hC)).ker_subtype
  refine ⟨D0 ∘ₗ r, fun f => ?_⟩
  have h1 : r (restr hC f) = ⟨restr hC f, LinearMap.mem_range_self _ f⟩ :=
    LinearMap.congr_fun hr ⟨_, _⟩
  rw [LinearMap.comp_apply, h1]
  simp only [D0, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image,
    Submodule.liftQ_apply]
  rfl

theorem exists_functional {C : Set S} (hC : IsClosed C) (E : Distr C) :
    ∃ η : (S → ℂ) →ₗ[ℂ] ℂ, ∀ f : SC S, η f = E (restr hC f) := by
  obtain ⟨r, hr⟩ := (SC S).subtype.exists_leftInverse_of_injective (SC S).ker_subtype
  refine ⟨E ∘ₗ restr hC ∘ₗ r, fun f => ?_⟩
  have h1 : r (f : S → ℂ) = f := LinearMap.congr_fun hr f
  simp only [LinearMap.comp_apply, h1]

end PositivityTheory.RgUd.T.Desc.SLF
end
end

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Desc.SLF

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def Tset (F : Set (Matrix (Fin n) (Fin n) k)) (P : k[X]) : Set (Matrix (Fin n) (Fin n) k) := {x | x ∈ F ∧ aeval x P = x}

def cj (g : GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) : Matrix (Fin n) (Fin n) k := g.val * x * g⁻¹.val

theorem cj_mul (g h : GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) : cj (g * h) x = cj g (cj h x) := by
  simp [cj, mul_assoc]

theorem cj_one (x : Matrix (Fin n) (Fin n) k) : cj (1 : GL (Fin n) k) x = x := by simp [cj]

theorem continuous_cj : Continuous fun p : GL (Fin n) k × Matrix (Fin n) (Fin n) k => cj p.1 p.2 :=
  ((Units.continuous_val.comp continuous_fst).matrix_mul continuous_snd).matrix_mul
    (Units.continuous_coe_inv.comp continuous_fst)

section Hyp

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {F : Set (Matrix (Fin n) (Fin n) k)} {P : k[X]}
  (hFinv : ∀ g ∈ Gz Z, ∀ x ∈ F, g.val * x * g⁻¹.val ∈ F)

include hFinv in
theorem cj_mem_Tset {g : GL (Fin n) k} (hg : g ∈ Gz Z) {x} (hx : x ∈ Tset F P) : cj g x ∈ Tset F P :=
  ⟨hFinv g hg x hx.1, by rw [cj, Asm.aeval_conj, hx.2]⟩

def actT : MulAction (GzS Z) (Tset F P) where
  smul g x := ⟨cj g.1 x.1, cj_mem_Tset hFinv g.2 x.2⟩
  one_smul x := Subtype.ext (cj_one x.1)
  mul_smul g h x := Subtype.ext (cj_mul g.1 h.1 x.1)

end Hyp

end PositivityTheory.RgUd.T.Desc.SLF

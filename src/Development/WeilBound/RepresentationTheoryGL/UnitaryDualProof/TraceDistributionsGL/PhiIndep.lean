module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.IsInvForm

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.FormTraceEq
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.FormTrace
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.HasTraceDistrOfAdmissible
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.KirillovEndUnitaryOfTheoremA
noncomputable section

open GroundTheory.Automorphic

namespace PositivityTheory.PfBern.Unit

section General

variable {G : Type} [Group G] [TopologicalSpace G]

def conjFn (g : G) (f : G → ℂ) : G → ℂ := fun x => f (g⁻¹ * x * g)


variable (G) in
abbrev testFn : Submodule ℂ (G → ℂ) := locallyConstantCompactSupport G ℂ ℂ


variable (G) in
def PInvIsGInv (P : Subgroup G) : Prop :=
  ∀ D : (G → ℂ) →ₗ[ℂ] ℂ, (∀ p ∈ P, ∀ f ∈ testFn G, D (conjFn p f) = D f) →
    ∀ (g : G), ∀ f ∈ testFn G, D (conjFn g f) = D f

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def HasTraceDistr (ρ : Representation ℂ G V) : Prop :=
  ∃ D : Module.End ℂ V →ₗ[ℂ] (G → ℂ) →ₗ[ℂ] ℂ,
    (∀ (g : G) (S : Module.End ℂ V), ∀ f ∈ testFn G, D (ρ g⁻¹ * S * ρ g) f = D S (conjFn g f)) ∧
    (∀ S : Module.End ℂ V, (∀ f ∈ testFn G, D S f = 0) → S = 0)

abbrev Sesq (V : Type) [AddCommGroup V] [Module ℂ V] : Type := V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ

def HasFormTraceDistr (ρ : Representation ℂ G V) : Prop :=
  ∃ D : Sesq V →ₗ[ℂ] (G → ℂ) →ₗ[ℂ] ℂ,
    (∀ (g : G) (B : Sesq V), ∀ f ∈ testFn G, D ((B ∘ₗ ρ g).compl₂ (ρ g)) f = D B (conjFn g f)) ∧
    (∀ B : Sesq V, (∀ f ∈ testFn G, D B f = 0) → B = 0)

def InvFormScalar (ρ : Representation ℂ G V) (B₀ : Sesq V) : Prop :=
  ∀ B : Sesq V, (∀ g v w, B (ρ g v) (ρ g w) = B v w) → ∃ c : ℂ, B = c • B₀

def PFormScalar (P : Subgroup G) (ρ : Representation ℂ G V) (B₀ : Sesq V) : Prop :=
  ∀ B : Sesq V, (∀ p ∈ P, ∀ v w, B (ρ p v) (ρ p w) = B v w) → ∃ c : ℂ, B = c • B₀

theorem form_inv_of_trace (P : Subgroup G) (ρ : Representation ℂ G V) (hA : PInvIsGInv G P)
    (hD : HasFormTraceDistr ρ) (B : Sesq V) (hB : ∀ p ∈ P, ∀ v w, B (ρ p v) (ρ p w) = B v w) (g : G) (v w : V) :
    B (ρ g v) (ρ g w) = B v w := by
  obtain ⟨D, hequiv, hfaith⟩ := hD
  have hP : ∀ p ∈ P, ∀ f ∈ testFn G, D B (conjFn p f) = D B f := by
    intro p hp f hf
    have e : (B ∘ₗ ρ p).compl₂ (ρ p) = B := by
      ext v w
      exact hB p hp v w
    rw [← hequiv p B f hf, e]
  have hG := hA (D B) hP
  have h0 : (B ∘ₗ ρ g).compl₂ (ρ g) - B = 0 := hfaith _ fun f hf => by
    rw [map_sub, LinearMap.sub_apply, hequiv g B f hf, hG g f hf, sub_self]
  have h1 := congrArg (fun C : Sesq V => C v w) (sub_eq_zero.1 h0)
  simpa using h1

theorem pFormScalar_of (P : Subgroup G) (ρ : Representation ℂ G V) (B₀ : Sesq V) (hA : PInvIsGInv G P)
    (hD : HasFormTraceDistr ρ) (hS : InvFormScalar ρ B₀) : PFormScalar P ρ B₀ :=
  fun B hB => hS B (form_inv_of_trace P ρ hA hD B hB)

private theorem eigen_lemma (W : Submodule ℂ V) [FiniteDimensional ℂ W] [Nontrivial W] (B B₀ : Sesq V)
    (hpos : ∀ v, v ≠ 0 → 0 < (B₀ v v).re) :
    ∃ c : ℂ, ∃ x : V, x ∈ W ∧ x ≠ 0 ∧ ∀ y ∈ W, B x y = c * B₀ x y := by
  let b := Module.finBasis ℂ W
  let L0 : W →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    { toFun := fun x j => B₀ (x : V) (b j : V)
      map_add' := by
        intro x y
        ext j
        simp
      map_smul' := by
        intro c x
        ext j
        simp }
  let L : W →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    { toFun := fun x j => B (x : V) (b j : V)
      map_add' := by
        intro x y
        ext j
        simp
      map_smul' := by
        intro c x
        ext j
        simp }
  have hext : ∀ (C : Sesq V) (c : ℂ) (x : V), (∀ j, C x (b j : V) = c * B₀ x (b j : V)) →
      ∀ y ∈ W, C x y = c * B₀ x y := by
    intro C c x h y hy
    have key : (C x).comp W.subtype = c • ((B₀ x).comp W.subtype) := by
      apply b.ext
      intro j
      simp [h j]
    have := LinearMap.congr_fun key ⟨y, hy⟩
    simpa using this
  have hinj : Function.Injective L0 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : ∀ j, B₀ (x : V) (b j : V) = 0 * B₀ (x : V) (b j : V) := by
      intro j
      have := congrFun hx j
      simpa [L0] using this
    have hxx := hext B₀ 0 x h0 x x.2
    by_contra hne
    have hx0 : (x : V) ≠ 0 := by simpa using hne
    have := hpos _ hx0
    rw [hxx] at this
    simp at this
  let E := L0.linearEquivOfInjective hinj (by simp)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (E.symm.toLinearMap ∘ₗ L)
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  refine ⟨c, x, x.2, ?_, ?_⟩
  · simpa using hx.2
  · apply hext B c x
    intro j
    have h1 := hx.apply_eq_smul
    have h2 : L x = E (c • x) := by
      rw [← h1]
      simp
    have h3 := congrFun h2 j
    simpa [E, L, L0, LinearMap.linearEquivOfInjective_apply] using h3

theorem invFormScalar_of_admissible [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] (ρ : Representation ℂ G V) (hadm : GroundTheory.Automorphic.IsAdmissible ρ) [ρ.IsIrreducible]
    (B₀ : Sesq V) (hpos : ∀ v, v ≠ 0 → 0 < (B₀ v v).re) (hinv : ∀ g v w, B₀ (ρ g v) (ρ g w) = B₀ v w) :
    InvFormScalar ρ B₀ := by
  intro B hB
  obtain ⟨v0, hv0⟩ := exists_ne_zero_of_isIrreducible (ρ := ρ)
  obtain ⟨K, hKc, hKle⟩ := hasBasis_nhds_one_compactOpenSubgroup.mem_iff.1
    ((hadm.1 v0).mem_nhds (stabilizerOf ρ v0).one_mem)
  have hKo : IsOpen ((K : Subgroup G) : Set G) := K.isOpen
  haveI : FiniteDimensional ℂ (fixedVectors ρ (K : Subgroup G)) := hadm.2 _ hKc hKo
  have hv0W : v0 ∈ fixedVectors ρ (K : Subgroup G) := mem_fixedVectors.2 (fun k hk => hKle hk)
  haveI : Nontrivial (fixedVectors ρ (K : Subgroup G)) :=
    ⟨⟨⟨v0, hv0W⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, x0, hx0W, hx0, hxy⟩ := eigen_lemma (fixedVectors ρ (K : Subgroup G)) B B₀ hpos
  refine ⟨c, ?_⟩
  have hB'inv : ∀ g v w, (B - c • B₀) (ρ g v) (ρ g w) = (B - c • B₀) v w := by
    intro g v w
    simp [hB, hinv]
  have hW0 : ∀ y ∈ fixedVectors ρ (K : Subgroup G), (B - c • B₀) x0 y = 0 := by
    intro y hy
    simp [hxy y hy]
  have hall : ∀ y, (B - c • B₀) x0 y = 0 := by
    intro y
    have hker : coinvariantsKer ρ (K : Subgroup G) ≤ LinearMap.ker ((B - c • B₀) x0) := by
      apply Submodule.span_le.2
      rintro _ ⟨⟨k, v⟩, rfl⟩
      have hk : ρ (k : G) x0 = x0 := (mem_fixedVectors.1 hx0W) k k.2
      have e := hB'inv k x0 v
      rw [hk] at e
      change (B - c • B₀) x0 (ρ (k : G) v - v) = 0
      rw [map_sub, e, sub_self]
    have h1 := hker (sub_fixedProj_mem hadm.1 hKc hKo y)
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
    rw [h1]
    exact hW0 _ (fixedProj ρ hadm.1 hKc hKo y).2
  let U : Subrepresentation ρ := ⟨LinearMap.ker (B - c • B₀), by
    intro g v hv
    rw [LinearMap.mem_ker] at hv ⊢
    ext w
    have hw : ρ g (ρ g⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [LinearMap.zero_apply, ← hw, hB'inv, hv, LinearMap.zero_apply]⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top U with h | h
  · exfalso
    have hmem : x0 ∈ U.toSubmodule := LinearMap.mem_ker.2 (LinearMap.ext hall)
    rw [h] at hmem
    exact hx0 ((Submodule.mem_bot ℂ).1 hmem)
  · have hmem : ∀ v, v ∈ U.toSubmodule := by
      intro v
      rw [h]
      exact Submodule.mem_top
    refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
    have h2 := LinearMap.congr_fun (LinearMap.mem_ker.1 (hmem v)) w
    simpa [sub_eq_zero] using h2

end General

section GeneralLinearIntegers

def TheoremA (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop := ∀ n : ℕ, PInvIsGInv (GL (Fin (n + 1)) k) (GlobalTheory.BZMir.Mir k n)

def FormTraceDistrGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (n + 1)) k) V),
    GroundTheory.Automorphic.IsAdmissible π → π.IsIrreducible → (∃ B₀ : Sesq V, (∀ v w, B₀ w v = starRingEnd ℂ (B₀ v w)) ∧
      (∀ v, v ≠ 0 → 0 < (B₀ v v).re) ∧ ∀ g v w, B₀ (π g v) (π g w) = B₀ v w) → HasFormTraceDistr π

def FormSchurGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (n + 1)) k) V)
    (B₀ : Sesq V), GroundTheory.Automorphic.IsAdmissible π → π.IsIrreducible → (∀ v w, B₀ w v = starRingEnd ℂ (B₀ v w)) →
    (∀ v, v ≠ 0 → 0 < (B₀ v v).re) → (∀ g v w, B₀ (π g v) (π g w) = B₀ v w) → InvFormScalar π B₀

def KirillovForm (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (n + 1)) k) V)
    (B₀ : Sesq V), GroundTheory.Automorphic.IsAdmissible π → π.IsIrreducible → (∀ v w, B₀ w v = starRingEnd ℂ (B₀ v w)) →
    (∀ v, v ≠ 0 → 0 < (B₀ v v).re) → (∀ g v w, B₀ (π g v) (π g w) = B₀ v w) → PFormScalar (GlobalTheory.BZMir.Mir k n) π B₀

theorem kirillovForm_of_theoremA (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : TheoremA k) (hD : FormTraceDistrGL k) (hS : FormSchurGL k) :
    KirillovForm k := by
  intro n V _ _ π B₀ hadm hirr h1 h2 h3
  exact pFormScalar_of _ π B₀ (hA n) (hD n V π hadm hirr ⟨B₀, h1, h2, h3⟩) (hS n V π B₀ hadm hirr h1 h2 h3)

theorem formSchurGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : FormSchurGL k := by
  intro n V _ _ π B₀ hadm hirr _ h2 h3
  exact invFormScalar_of_admissible π hadm B₀ h2 h3

theorem kirillovForm_of_theoremA' (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : TheoremA k) (hD : FormTraceDistrGL k) : KirillovForm k :=
  kirillovForm_of_theoremA k hA hD (formSchurGL k)

end GeneralLinearIntegers

end PositivityTheory.PfBern.Unit
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.LevelSmulSmul
noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.ContragredientTranspose
  GroundTheory.Automorphic.Whittaker MeasureTheory

namespace PositivityTheory.PfBern.Unit

section Faith

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

section Level

variable {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))

theorem level_smul_smul (c : ℂ) (h : HeckeAlgebraLevel μ K hKc hKo) (w : fixedVectors ρ K) :
    (c • h) • w = c • (h • w) := Subtype.ext (by
  change heckeAct μ ρ ((c • (h : HeckeAlgebra μ) : HeckeAlgebra μ) : G → ℂ) (w : V) =
    c • heckeAct μ ρ ((h : HeckeAlgebra μ) : G → ℂ) (w : V)
  rw [HeckeAlgebra.coe_smul]
  exact heckeAct_smul_left c (h : HeckeAlgebra μ).mem (smooth_of_mem_fixedVectors hKo w.2))

theorem level_smul_comm (c : ℂ) (h : HeckeAlgebraLevel μ K hKc hKo) (w : fixedVectors ρ K) :
    h • (c • w) = c • (h • w) := Subtype.ext (by
  change heckeAct μ ρ ((h : HeckeAlgebra μ) : G → ℂ) (c • (w : V)) =
    c • heckeAct μ ρ ((h : HeckeAlgebra μ) : G → ℂ) (w : V)
  exact heckeAct_smul_right (h : HeckeAlgebra μ).mem c (smooth_of_mem_fixedVectors hKo w.2))

theorem level_schur (hρ : IsSmooth ρ) [ρ.IsIrreducible] [FiniteDimensional ℂ (fixedVectors ρ K)]
    (hK : fixedVectors ρ K ≠ ⊥) (φ : Module.End (HeckeAlgebraLevel μ K hKc hKo) (fixedVectors ρ K)) :
    ∃ c : ℂ, ∀ w, φ w = c • w := by
  have hs := isSimpleModule_fixedVectors (μ := μ) hKc hKo hρ hK
  let φℂ : Module.End ℂ (fixedVectors ρ K) :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun c w => by
        have e : c • w = (c • (1 : HeckeAlgebraLevel μ K hKc hKo)) • w := by
          rw [level_smul_smul, one_smul]
        rw [RingHom.id_apply, e, φ.map_smul, level_smul_smul, one_smul] }
  have hnt : Nontrivial (fixedVectors ρ K) := Submodule.nontrivial_iff_ne_bot.2 hK
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue φℂ
  obtain ⟨w₀, hw₀⟩ := hc.exists_hasEigenvector
  let ψ : Module.End (HeckeAlgebraLevel μ K hKc hKo) (fixedVectors ρ K) :=
    { toFun := fun w => φ w - c • w
      map_add' := fun a b => by rw [map_add (f := _), smul_add]; abel
      map_smul' := fun h w => by rw [RingHom.id_apply, φ.map_smul, smul_sub, level_smul_comm] }
  have hw₀ker : w₀ ∈ LinearMap.ker ψ := by
    rw [LinearMap.mem_ker]
    show φ w₀ - c • w₀ = 0
    rw [sub_eq_zero]
    exact Module.End.mem_eigenspace_iff.1 hw₀.1
  have hker : LinearMap.ker ψ ≠ ⊥ := fun hb => hw₀.2 (by rw [hb] at hw₀ker; exact (Submodule.mem_bot _).1 hw₀ker)
  have htop := (eq_bot_or_eq_top (LinearMap.ker ψ)).resolve_left hker
  refine ⟨c, fun w => ?_⟩
  have hw : w ∈ LinearMap.ker ψ := by rw [htop]; exact Submodule.mem_top
  exact sub_eq_zero.1 hw

theorem level_density (hρ : IsSmooth ρ) [ρ.IsIrreducible] [FiniteDimensional ℂ (fixedVectors ρ K)]
    (hK : fixedVectors ρ K ≠ ⊥) (A : Module.End ℂ (fixedVectors ρ K)) :
    ∃ r : HeckeAlgebraLevel μ K hKc hKo, levelLin hKc hKo ρ r = A := by
  classical
  have hs := isSimpleModule_fixedVectors (μ := μ) hKc hKo hρ hK
  let fE : Module.End (Module.End (HeckeAlgebraLevel μ K hKc hKo) (fixedVectors ρ K)) (fixedVectors ρ K) :=
    { toFun := A
      map_add' := A.map_add
      map_smul' := fun φ w => by
        rw [Module.End.smul_def, RingHom.id_apply, Module.End.smul_def]
        obtain ⟨c, hc⟩ := level_schur hKc hKo hρ hK φ
        rw [hc, hc, A.map_smul] }
  let b := Module.finBasis ℂ (fixedVectors ρ K)
  obtain ⟨r, hr⟩ := jacobson_density fE (Finset.univ.image b)
  refine ⟨r, b.ext fun i => ?_⟩
  have := hr (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  exact this.symm

end Level

end Faith

end PositivityTheory.PfBern.Unit
end
end

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose GroundTheory.Automorphic.Whittaker MeasureTheory

namespace PositivityTheory.PfBern.Unit

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_testProj : ∃ Pr : (G → ℂ) →ₗ[ℂ] testFn G, ∀ f : testFn G, Pr f = f := by
  obtain ⟨Pr, hPr⟩ := LinearMap.exists_leftInverse_of_injective (testFn G).subtype (Submodule.ker_subtype _)
  exact ⟨Pr, fun f => LinearMap.congr_fun hPr f⟩

end Gen

end PositivityTheory.PfBern.Unit
end
end

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.ContragredientTranspose
  GroundTheory.Automorphic.Whittaker MeasureTheory

namespace PositivityTheory.PfBern.Unit

section Riesz

variable {V : Type} [AddCommGroup V] [Module ℂ V] (B₀ : Sesq V) (W : Submodule ℂ V)

def IsRieszRepresentative (C : Sesq V) (A : W →ₗ[ℂ] V) (N : Module.End ℂ W) : Prop :=
  ∀ x y : W, B₀ (N x) y = C (A x) y

variable {B₀ W}

theorem riesz_unique (hpos : ∀ v, v ≠ 0 → 0 < (B₀ v v).re) {C : Sesq V} {A : W →ₗ[ℂ] V}
    {N N' : Module.End ℂ W} (h : IsRieszRepresentative B₀ W C A N) (h' : IsRieszRepresentative B₀ W C A N') : N = N' := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  by_contra hne
  have hd : ((N x : V) - (N' x : V)) ≠ 0 := sub_ne_zero.2 hne
  have hp := hpos _ hd
  have h1 := h x (N x - N' x)
  have h2 := h' x (N x - N' x)
  have e : B₀ ((N x : V) - (N' x : V)) ((N x - N' x : W) : V) = 0 := by
    rw [map_sub, LinearMap.sub_apply, h1, h2, sub_self]
  have hc : ((N x - N' x : W) : V) = (N x : V) - (N' x : V) := rfl
  rw [hc] at e
  rw [e] at hp
  simp at hp

theorem antilin_ext_basis [FiniteDimensional ℂ W] (φ ψ : V →ₗ⋆[ℂ] ℂ)
    (h : ∀ i, φ (Module.finBasis ℂ W i : V) = ψ (Module.finBasis ℂ W i : V)) (u : W) : φ u = ψ u := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (Module.finBasis ℂ W).sum_repr u, Submodule.coe_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_smul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, h i]

theorem riesz_exists [FiniteDimensional ℂ W] (hpos : ∀ v, v ≠ 0 → 0 < (B₀ v v).re) (C : Sesq V)
    (A : W →ₗ[ℂ] V) : ∃ N, IsRieszRepresentative B₀ W C A N := by
  let b := Module.finBasis ℂ W
  let β : Sesq V → (W →ₗ[ℂ] V) → (W →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ)) := fun C A =>
    LinearMap.pi fun i => (C.flip (b i : V)) ∘ₗ A
  have hβ : ∀ C A w i, β C A w i = C (A w) (b i) := fun _ _ _ _ => rfl
  have hinj : Function.Injective (β B₀ W.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    have := hpos w (fun h' => hne (Subtype.ext h'))
    have hz := antilin_ext_basis (W := W) (B₀ w) 0 (fun i => by
      have := congrFun hw i
      rw [hβ] at this
      simpa using this) w
    rw [hz] at this
    simp at this
  let e := LinearMap.linearEquivOfInjective (β B₀ W.subtype) hinj (by simp)
  refine ⟨e.symm.toLinearMap ∘ₗ β C A, fun x y => ?_⟩
  refine antilin_ext_basis (W := W) (B₀ _) (C (A x)) (fun i => ?_) y
  have h1 : β B₀ W.subtype (e.symm (β C A x)) = β C A x := by
    have := e.apply_symm_apply (β C A x)
    rw [LinearMap.linearEquivOfInjective_apply] at this
    exact this
  have := congrFun h1 i
  rw [hβ, hβ] at this
  exact this

end Riesz

section Rep

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
  {B₀ : Sesq V} (hpos : ∀ v, v ≠ 0 → 0 < (B₀ v v).re)

def BiInv (K : Subgroup G) (f : G → ℂ) : Prop := ∀ k ∈ K, ∀ x, f (k * x) = f x ∧ f (x * k) = f x

def resA (K : Subgroup G) (f : locallyConstantCompactSupport G ℂ ℂ) : fixedVectors ρ K →ₗ[ℂ] V :=
  heckeLin μ hρ.1 f ∘ₗ (fixedVectors ρ K).subtype

def rN {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) (C : Sesq V)
    (f : locallyConstantCompactSupport G ℂ ℂ) : Module.End ℂ (fixedVectors ρ K) :=
  haveI := hρ.2 K hKc hKo
  Classical.choose (riesz_exists hpos C (resA μ hρ K f))

theorem rN_spec {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) (C : Sesq V)
    (f : locallyConstantCompactSupport G ℂ ℂ) : IsRieszRepresentative B₀ _ C (resA μ hρ K f) (rN μ hρ hpos hKc hKo C f) :=
  haveI := hρ.2 K hKc hKo
  Classical.choose_spec (riesz_exists hpos C (resA μ hρ K f))

def DK {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) (C : Sesq V)
    (f : locallyConstantCompactSupport G ℂ ℂ) : ℂ :=
  LinearMap.trace ℂ _ (rN μ hρ hpos hKc hKo C f)

theorem B0_fixedProj (hinv : ∀ g v w, B₀ (ρ g v) (ρ g w) = B₀ v w) {K : Subgroup G} (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (z y : V) (hy : y ∈ fixedVectors ρ K) :
    B₀ (fixedProj ρ hρ.1 hKc hKo z) y = B₀ z y := by
  have hc : ∀ u ∈ coinvariantsKer ρ K, B₀ u y = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨κ, w⟩, rfl⟩ := hx
      have h1 := hinv κ w y
      rw [hy κ κ.2] at h1
      show B₀ (ρ κ w - w) y = 0
      rw [map_sub, LinearMap.sub_apply, h1, sub_self]
    | zero => simp
    | add x y' _ _ hx hy' => rw [map_add (f := _), LinearMap.add_apply, hx, hy', add_zero]
    | smul a x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]
  have := hc _ (sub_fixedProj_mem hρ.1 hKc hKo z)
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
  exact this.symm

theorem heckeLin_fixedProj {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (f : locallyConstantCompactSupport G ℂ ℂ) (hf : BiInv K f) (v : V) :
    heckeLin μ hρ.1 f (fixedProj ρ hρ.1 hKc hKo v) = heckeLin μ hρ.1 f v := by
  let F : HeckeAlgebra μ := f
  have hmem : F ∈ biInvariant μ K := fun k hk x => hf k hk x
  have hri := (mem_biInvariant_iff_idem hKc hKo).1 hmem
  have e : groupConv μ (f : G → ℂ) (idem μ hKc hKo) = f := by
    have := congrArg (fun F' : HeckeAlgebra μ => (F' : G → ℂ)) hri.2
    rw [HeckeAlgebra.coe_mul] at this
    exact this
  rw [heckeLin_apply, heckeLin_apply, ← heckeAct_idem_eq_fixedProj (μ := μ) hKc hKo hρ.1,
    ← heckeAct_groupConv f.2 (idem μ hKc hKo).mem (hρ.1 _), e]

theorem DK_mono (hinv : ∀ g v w, B₀ (ρ g v) (ρ g w) = B₀ v w) {K K' : Subgroup G} (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (hK'c : IsCompact (K' : Set G)) (hK'o : IsOpen (K' : Set G)) (hle : K' ≤ K)
    (C : Sesq V) (f : locallyConstantCompactSupport G ℂ ℂ) (hf : BiInv K f) :
    DK μ hρ hpos hK'c hK'o C f = DK μ hρ hpos hKc hKo C f := by
  haveI := hρ.2 K hKc hKo
  haveI := hρ.2 K' hK'c hK'o
  have hWW : fixedVectors ρ K ≤ fixedVectors ρ K' := fixedVectors_antitone ρ hle
  let ι : fixedVectors ρ K →ₗ[ℂ] fixedVectors ρ K' := Submodule.inclusion hWW
  let p : fixedVectors ρ K' →ₗ[ℂ] fixedVectors ρ K := fixedProj ρ hρ.1 hKc hKo ∘ₗ (fixedVectors ρ K').subtype
  have sN' := rN_spec μ hρ hpos hK'c hK'o C f
  have sN := rN_spec μ hρ hpos hKc hKo C f
  have h1 : rN μ hρ hpos hK'c hK'o C f = rN μ hρ hpos hK'c hK'o C f ∘ₗ ι ∘ₗ p := by
    refine riesz_unique hpos sN' fun x y => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, sN']
    show C (heckeLin μ hρ.1 f (fixedProj ρ hρ.1 hKc hKo (x : V) : V)) y = C (heckeLin μ hρ.1 f x) y
    rw [heckeLin_fixedProj μ hρ hKc hKo f hf]
  have h2 : p ∘ₗ rN μ hρ hpos hK'c hK'o C f ∘ₗ ι = rN μ hρ hpos hKc hKo C f := by
    refine riesz_unique hpos (fun x y => ?_) sN
    show B₀ (fixedProj ρ hρ.1 hKc hKo (rN μ hρ hpos hK'c hK'o C f (ι x) : V) : V) y = _
    rw [B0_fixedProj hρ hinv hKc hKo _ _ y.2]
    have := sN' (ι x) (ι y)
    exact this
  unfold DK
  calc LinearMap.trace ℂ _ (rN μ hρ hpos hK'c hK'o C f)
      = LinearMap.trace ℂ _ ((rN μ hρ hpos hK'c hK'o C f ∘ₗ ι) ∘ₗ p) := by
        conv_lhs => rw [h1]
        rfl
    _ = LinearMap.trace ℂ _ (p ∘ₗ (rN μ hρ hpos hK'c hK'o C f ∘ₗ ι)) := LinearMap.trace_comp_comm' _ _
    _ = LinearMap.trace ℂ _ (rN μ hρ hpos hKc hKo C f) := congrArg _ h2

end Rep

section Lin

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
  {B₀ : Sesq V} (hpos : ∀ v, v ≠ 0 → 0 < (B₀ v v).re)

theorem BiInv.mono {K K' : Subgroup G} {f : G → ℂ} (hf : BiInv K f) (hle : K' ≤ K) : BiInv K' f :=
  fun k hk x => hf k (hle hk) x

theorem BiInv.add {K : Subgroup G} {f g : G → ℂ} (hf : BiInv K f) (hg : BiInv K g) : BiInv K (f + g) :=
  fun k hk x => ⟨by simp [(hf k hk x).1, (hg k hk x).1], by simp [(hf k hk x).2, (hg k hk x).2]⟩

theorem BiInv.smul {K : Subgroup G} {f : G → ℂ} (c : ℂ) (hf : BiInv K f) : BiInv K (c • f) :=
  fun k hk x => ⟨by simp [(hf k hk x).1], by simp [(hf k hk x).2]⟩

theorem exists_K (f : locallyConstantCompactSupport G ℂ ℂ) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ BiInv (K : Subgroup G) f := by
  obtain ⟨K, hKc, hK⟩ := exists_forall_mul_left_mul_right f.2
  exact ⟨K, hKc, fun k hk x => ⟨by simpa using hK k hk x 1 (one_mem _), by simpa using hK 1 (one_mem _) x k hk⟩⟩

theorem rN_add_C {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) (C₁ C₂ : Sesq V)
    (f : locallyConstantCompactSupport G ℂ ℂ) :
    rN μ hρ hpos hKc hKo (C₁ + C₂) f = rN μ hρ hpos hKc hKo C₁ f + rN μ hρ hpos hKc hKo C₂ f := by
  refine riesz_unique hpos (rN_spec μ hρ hpos hKc hKo _ f) fun x y => ?_
  have s1 := rN_spec μ hρ hpos hKc hKo C₁ f x y
  have s2 := rN_spec μ hρ hpos hKc hKo C₂ f x y
  show B₀ ((rN μ hρ hpos hKc hKo C₁ f x : V) + (rN μ hρ hpos hKc hKo C₂ f x : V)) y = _
  rw [map_add (f := _), LinearMap.add_apply, s1, s2, LinearMap.add_apply, LinearMap.add_apply]

theorem rN_smul_C {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) (c : ℂ) (C : Sesq V)
    (f : locallyConstantCompactSupport G ℂ ℂ) :
    rN μ hρ hpos hKc hKo (c • C) f = c • rN μ hρ hpos hKc hKo C f := by
  refine riesz_unique hpos (rN_spec μ hρ hpos hKc hKo _ f) fun x y => ?_
  have s1 := rN_spec μ hρ hpos hKc hKo C f x y
  show B₀ (c • (rN μ hρ hpos hKc hKo C f x : V)) y = _
  rw [map_smul, LinearMap.smul_apply, s1, LinearMap.smul_apply, LinearMap.smul_apply]

theorem rN_add_f {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) (C : Sesq V)
    (f₁ f₂ : locallyConstantCompactSupport G ℂ ℂ) :
    rN μ hρ hpos hKc hKo C (f₁ + f₂) = rN μ hρ hpos hKc hKo C f₁ + rN μ hρ hpos hKc hKo C f₂ := by
  refine riesz_unique hpos (rN_spec μ hρ hpos hKc hKo C _) fun x y => ?_
  have s1 := rN_spec μ hρ hpos hKc hKo C f₁ x y
  have s2 := rN_spec μ hρ hpos hKc hKo C f₂ x y
  show B₀ ((rN μ hρ hpos hKc hKo C f₁ x : V) + (rN μ hρ hpos hKc hKo C f₂ x : V)) y =
    C (heckeLin μ hρ.1 (f₁ + f₂) x) y
  rw [map_add (f := _), LinearMap.add_apply, s1, s2, heckeLin_add μ hρ.1, LinearMap.add_apply, map_add (f := _), LinearMap.add_apply]
  rfl

theorem rN_smul_f {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) (C : Sesq V) (c : ℂ)
    (f : locallyConstantCompactSupport G ℂ ℂ) :
    rN μ hρ hpos hKc hKo C (c • f) = c • rN μ hρ hpos hKc hKo C f := by
  refine riesz_unique hpos (rN_spec μ hρ hpos hKc hKo C _) fun x y => ?_
  have s1 := rN_spec μ hρ hpos hKc hKo C f x y
  show B₀ (c • (rN μ hρ hpos hKc hKo C f x : V)) y = C (heckeLin μ hρ.1 (c • f) x) y
  rw [map_smul, LinearMap.smul_apply, s1, heckeLin_smul μ hρ.1, LinearMap.smul_apply, map_smul, LinearMap.smul_apply]
  rfl

def DF (C : Sesq V) (f : locallyConstantCompactSupport G ℂ ℂ) : ℂ :=
  DK μ hρ hpos (Classical.choose_spec (exists_K f)).1 (Classical.choose (exists_K f)).isOpen C f

theorem DF_eq (hinv : ∀ g v w, B₀ (ρ g v) (ρ g w) = B₀ v w) (C : Sesq V) (f : locallyConstantCompactSupport G ℂ ℂ)
    {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) (hf : BiInv K f) :
    DF μ hρ hpos C f = DK μ hρ hpos hKc hKo C f := by
  have hL := Classical.choose_spec (exists_K f)
  set L := Classical.choose (exists_K f)
  have hMc : IsCompact ((K ⊓ (L : Subgroup G) : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKc.inter_right L.isClosed
  have hMo : IsOpen ((K ⊓ (L : Subgroup G) : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKo.inter L.isOpen
  unfold DF
  rw [← DK_mono μ hρ hpos hinv hL.1 L.isOpen hMc hMo inf_le_right C f hL.2,
    DK_mono μ hρ hpos hinv hKc hKo hMc hMo inf_le_left C f hf]

def formD (hinv : ∀ g v w, B₀ (ρ g v) (ρ g w) = B₀ v w) (Pr : (G → ℂ) →ₗ[ℂ] testFn G) :
    Sesq V →ₗ[ℂ] (G → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun C g => DF μ hρ hpos C (Pr g))
    (fun C₁ C₂ g => by
      unfold DF DK
      rw [rN_add_C, map_add (f := _)])
    (fun c C g => by
      unfold DF DK
      rw [rN_smul_C, map_smul, smul_eq_mul])
    (fun C g₁ g₂ => by
      obtain ⟨K₁, h₁c, h₁⟩ := exists_K (Pr g₁)
      obtain ⟨K₂, h₂c, h₂⟩ := exists_K (Pr g₂)
      have hMc : IsCompact (((K₁ : Subgroup G) ⊓ (K₂ : Subgroup G) : Subgroup G) : Set G) := by
        rw [Subgroup.coe_inf]; exact h₁c.inter_right K₂.isClosed
      have hMo : IsOpen (((K₁ : Subgroup G) ⊓ (K₂ : Subgroup G) : Subgroup G) : Set G) := by
        rw [Subgroup.coe_inf]; exact K₁.isOpen.inter K₂.isOpen
      have b₁ := h₁.mono (inf_le_left : (K₁ : Subgroup G) ⊓ K₂ ≤ K₁)
      have b₂ := h₂.mono (inf_le_right : (K₁ : Subgroup G) ⊓ K₂ ≤ K₂)
      rw [map_add (f := _), DF_eq μ hρ hpos hinv C _ hMc hMo (by exact b₁.add b₂), DF_eq μ hρ hpos hinv C _ hMc hMo b₁,
        DF_eq μ hρ hpos hinv C _ hMc hMo b₂]
      unfold DK
      rw [rN_add_f, map_add (f := _)])
    (fun c C g => by
      obtain ⟨K₁, h₁c, h₁⟩ := exists_K (Pr g)
      rw [map_smul, DF_eq μ hρ hpos hinv C _ h₁c K₁.isOpen (by exact h₁.smul c), DF_eq μ hρ hpos hinv C _ h₁c K₁.isOpen h₁]
      unfold DK
      rw [rN_smul_f, map_smul, smul_eq_mul])

theorem formD_apply (hinv : ∀ g v w, B₀ (ρ g v) (ρ g w) = B₀ v w) (Pr : (G → ℂ) →ₗ[ℂ] testFn G) (C : Sesq V)
    (g : G → ℂ) : formD μ hρ hpos hinv Pr C g = DF μ hρ hpos C (Pr g) := rfl

end Lin

end PositivityTheory.PfBern.Unit
end
end

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.ContragredientTranspose
  GroundTheory.Automorphic.Whittaker MeasureTheory

namespace PositivityTheory.PfBern.Unit

section Eq

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
  {B₀ : Sesq V} (hpos : ∀ v, v ≠ 0 → 0 < (B₀ v v).re)

def conjSub (g : G) (K : Subgroup G) : Subgroup G := K.comap (MulAut.conj g⁻¹).toMonoidHom

theorem mem_conjSub {g : G} {K : Subgroup G} {x : G} : x ∈ conjSub g K ↔ g⁻¹ * x * g ∈ K := by
  simp [conjSub, MulAut.conj_apply]

def conjHomeo (g : G) : G ≃ₜ G := (Homeomorph.mulLeft g⁻¹).trans (Homeomorph.mulRight g)

theorem coe_conjSub (g : G) (K : Subgroup G) : (conjSub g K : Set G) = conjHomeo g ⁻¹' (K : Set G) := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_preimage, mem_conjSub, conjHomeo, Homeomorph.trans_apply,
    Homeomorph.coe_mulLeft, Homeomorph.coe_mulRight]

theorem isCompact_conjSub (g : G) {K : Subgroup G} (hKc : IsCompact (K : Set G)) :
    IsCompact (conjSub g K : Set G) := by
  rw [coe_conjSub, ← congrFun (conjHomeo g).image_symm (K : Set G)]
  exact hKc.image (conjHomeo g).symm.continuous

theorem isOpen_conjSub (g : G) {K : Subgroup G} (hKo : IsOpen (K : Set G)) : IsOpen (conjSub g K : Set G) := by
  rw [coe_conjSub]
  exact hKo.preimage (conjHomeo g).continuous

def conjEquiv (g : G) (K : Subgroup G) : fixedVectors ρ K ≃ₗ[ℂ] fixedVectors ρ (conjSub g K) where
  toFun v := ⟨ρ g v, by
    rw [mem_fixedVectors]
    intro x hx
    have h := v.2
    rw [mem_fixedVectors] at h
    have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (ρ g⁻¹),
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, h _ (mem_conjSub.1 hx)]⟩
  map_add' v w := Subtype.ext (map_add _ _ _)
  map_smul' c v := Subtype.ext (map_smul _ _ _)
  invFun w := ⟨ρ g⁻¹ w, by
    rw [mem_fixedVectors]
    intro x hx
    have h := w.2
    rw [mem_fixedVectors] at h
    have hx' : g * x * g⁻¹ ∈ conjSub g K := mem_conjSub.2 (by group; exact hx)
    have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (ρ g),
      ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, h _ hx']⟩
  left_inv v := Subtype.ext (by
    show ρ g⁻¹ (ρ g v) = v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply])
  right_inv w := Subtype.ext (by
    show ρ g (ρ g⁻¹ w) = w
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])

theorem conjEquiv_apply (g : G) (K : Subgroup G) (v : fixedVectors ρ K) :
    (conjEquiv g K v : V) = ρ g v := rfl

theorem conjEquiv_symm_apply (g : G) (K : Subgroup G) (w : fixedVectors ρ (conjSub g K)) :
    ((conjEquiv g K).symm w : V) = ρ g⁻¹ w := rfl

theorem biInv_conj (g : G) {K : Subgroup G} {f : G → ℂ} (hf : BiInv K f) : BiInv (conjSub g K) (conjFn g f) := by
  intro k hk x
  have hk' := mem_conjSub.1 hk
  constructor
  · show f (g⁻¹ * (k * x) * g) = f (g⁻¹ * x * g)
    have := (hf _ hk' (g⁻¹ * x * g)).1
    rw [← this]; congr 1; group
  · show f (g⁻¹ * (x * k) * g) = f (g⁻¹ * x * g)
    have := (hf _ hk' (g⁻¹ * x * g)).2
    rw [← this]; congr 1; group

theorem formD_equiv [μ.IsMulRightInvariant] (hinv : ∀ g v w, B₀ (ρ g v) (ρ g w) = B₀ v w)
    (Pr : (G → ℂ) →ₗ[ℂ] testFn G) (hPr : ∀ f : testFn G, Pr f = f) (g : G) (B : Sesq V) (f : G → ℂ)
    (hf : f ∈ testFn G) :
    formD μ hρ hpos hinv Pr ((B ∘ₗ ρ g).compl₂ (ρ g)) f = formD μ hρ hpos hinv Pr B (conjFn g f) := by
  have hcoe : ((biTranslL g g (⟨f, hf⟩ : testFn G) : testFn G) : G → ℂ) = conjFn g f := by
    ext x
    simp [biTranslL, conjFn]
  have h1 : Pr f = ⟨f, hf⟩ := hPr ⟨f, hf⟩
  have h2 : Pr (conjFn g f) = biTranslL g g (⟨f, hf⟩ : testFn G) := by
    rw [← hcoe]
    exact hPr _
  rw [formD_apply, formD_apply, h1, h2]
  obtain ⟨K, hKc, hKf⟩ := exists_K (⟨f, hf⟩ : testFn G)
  have hKo : IsOpen ((K : Subgroup G) : Set G) := K.isOpen
  have hK'c := isCompact_conjSub g hKc
  have hK'o := isOpen_conjSub g hKo
  have hK'f : BiInv (conjSub g (K : Subgroup G)) (biTranslL g g (⟨f, hf⟩ : testFn G) : G → ℂ) := by
    rw [hcoe]
    exact biInv_conj g hKf
  rw [DF_eq μ hρ hpos hinv _ _ hKc hKo hKf, DF_eq μ hρ hpos hinv _ _ hK'c hK'o hK'f]
  haveI := hρ.2 _ hKc hKo
  haveI := hρ.2 _ hK'c hK'o
  have hR : rN μ hρ hpos hK'c hK'o B (biTranslL g g (⟨f, hf⟩ : testFn G)) =
      (conjEquiv (ρ := ρ) g (K : Subgroup G)).conj
        (rN μ hρ hpos hKc hKo ((B ∘ₗ ρ g).compl₂ (ρ g)) ⟨f, hf⟩) := by
    apply riesz_unique hpos (rN_spec μ hρ hpos hK'c hK'o B _)
    intro x' y'
    have hs := rN_spec μ hρ hpos hKc hKo ((B ∘ₗ ρ g).compl₂ (ρ g)) ⟨f, hf⟩
      ((conjEquiv (ρ := ρ) g (K : Subgroup G)).symm x') ((conjEquiv (ρ := ρ) g (K : Subgroup G)).symm y')
    have ex : (((conjEquiv (ρ := ρ) g (K : Subgroup G)).conj
        (rN μ hρ hpos hKc hKo ((B ∘ₗ ρ g).compl₂ (ρ g)) ⟨f, hf⟩) x' : fixedVectors ρ _) : V) =
        ρ g (rN μ hρ hpos hKc hKo ((B ∘ₗ ρ g).compl₂ (ρ g)) ⟨f, hf⟩
          ((conjEquiv (ρ := ρ) g (K : Subgroup G)).symm x')) := by
      rw [LinearEquiv.conj_apply_apply, conjEquiv_apply]
    have ey : (y' : V) = ρ g ((conjEquiv (ρ := ρ) g (K : Subgroup G)).symm y') := by
      rw [← conjEquiv_apply, LinearEquiv.apply_symm_apply]
    have eA : resA μ hρ (conjSub g (K : Subgroup G)) (biTranslL g g (⟨f, hf⟩ : testFn G)) x' =
        ρ g (heckeAct μ ρ f ((conjEquiv (ρ := ρ) g (K : Subgroup G)).symm x')) := by
      rw [conjEquiv_symm_apply]
      simp only [resA, LinearMap.comp_apply, Submodule.subtype_apply, heckeLin_apply]
      exact heckeAct_biTranslL μ hρ.1 g _ _
    rw [ex, ey, hinv, eA]
    simpa [resA, heckeLin_apply] using hs
  simp only [DK]
  rw [hR, LinearMap.trace_conj']

end Eq

end PositivityTheory.PfBern.Unit
end
end

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.BZMir GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.AB

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev Mx (n : ℕ) : Type := Matrix (Fin (n + 1)) (Fin (n + 1)) k

abbrev Vc (n : ℕ) : Type := Fin (n + 1) → k

variable {k}

def cj {n : ℕ} (g : GL (Fin (n + 1)) k) (x : Mx k n) : Mx k n :=
  (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) * x * ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)

def PInvX {n : ℕ} (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ) : Prop := ∀ p ∈ Mir k n, ∀ f ∈ SB (Mx k n), Λ (f ∘ cj p) = Λ f

def GInvX {n : ℕ} (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ) : Prop := ∀ g : GL (Fin (n + 1)) k, ∀ f ∈ SB (Mx k n), Λ (f ∘ cj g) = Λ f


open Classical in
def sec {n : ℕ} (w : Vc k n) : GL (Fin (n + 1)) k :=
  if h : ∃ s : GL (Fin (n + 1)) k, ∀ j, (s : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j then h.choose else 1


open Classical in
def phi {n : ℕ} (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ) (F : Mx k n × Vc k n → ℂ) (w : Vc k n) : ℂ :=
  if w = 0 then 0 else Λ (fun x => F (cj (sec w)⁻¹ x, w))

def lt [MeasurableSpace k] (ν : Measure k) {n : ℕ} (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ) (F : Mx k n × Vc k n → ℂ) : ℂ :=
  ∫ w, phi Λ F w ∂(Measure.pi fun _ => ν)

variable (k)

def SecSpec : Prop := ∀ (n : ℕ) (w : Vc k n), w ≠ 0 → ∀ j, ((sec w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j

def PhiIndep : Prop := ∀ (n : ℕ) (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ), PInvX Λ → ∀ F ∈ SB (Mx k n × Vc k n), ∀ w : Vc k n, w ≠ 0 →
  ∀ s : GL (Fin (n + 1)) k, (∀ j, (s : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j) →
    phi Λ F w = Λ (fun x => F (cj s⁻¹ x, w))

def PhiLin : Prop := ∀ (n : ℕ) (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ), ∀ F ∈ SB (Mx k n × Vc k n), ∀ G ∈ SB (Mx k n × Vc k n),
  ∀ a b : ℂ, phi Λ (a • F + b • G) = a • phi Λ F + b • phi Λ G

def PhiEquiv : Prop := ∀ (n : ℕ) (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ), PInvX Λ → ∀ F ∈ SB (Mx k n × Vc k n), ∀ h : GL (Fin (n + 1)) k,
  ∀ w : Vc k n, phi Λ (fun q => F (cj h⁻¹ q.1, (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ q.2)) w =
    phi Λ F ((h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ w)

def PhiInt : Prop := ∀ [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : ℕ)
  (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ), PInvX Λ → ∀ F ∈ SB (Mx k n × Vc k n), Integrable (phi Λ F) (Measure.pi fun _ => ν)

def eN (n : ℕ) : Vc k n := Pi.single (Fin.last n) 1

def PhiNear : Prop := ∀ (n : ℕ) (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ), PInvX Λ → ∀ f₀ ∈ SB (Mx k n), ∃ t : kˣ, ∀ s : kˣ,
  box (Fin (n + 1)) s ⊆ box (Fin (n + 1)) t →
    phi Λ (fun q => f₀ q.1 * ({w : Vc k n | w - eN k n ∈ box (Fin (n + 1)) s}.indicator 1 q.2)) =
      {w : Vc k n | w - eN k n ∈ box (Fin (n + 1)) s}.indicator fun _ => Λ f₀

def PfAct : Prop := ∀ [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ),
  HasConductor ψ c → ∀ (n : ℕ) (F : Mx k n × Vc k n → ℂ), F ∈ SB (Mx k n × Vc k n) → ∀ h : GL (Fin (n + 1)) k,
    GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ => ν) (fun q => F (cj h⁻¹ q.1, (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ q.2)) =
      fun z => (((nabs k (GeneralLinearGroup.det h))⁻¹ : ℝ) : ℂ) * GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ => ν) F
        (cj h⁻¹ z.1, ((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ z.2)

def LtEquiv : Prop := ∀ [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : ℕ)
  (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ), PInvX Λ → ∀ F ∈ SB (Mx k n × Vc k n), ∀ h : GL (Fin (n + 1)) k,
    lt ν Λ (fun q => F (cj h⁻¹ q.1, (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ q.2)) =
      (((nabs k (GeneralLinearGroup.det h))⁻¹ : ℝ) : ℂ) * lt ν Λ F

def Recover : Prop := ThmT k → ∀ (n : ℕ) (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ), PInvX Λ →
  ∃ L : (Mx k n → ℂ) →ₗ[ℂ] ℂ, GInvX L ∧ ∀ f ∈ SB (Mx k n), Λ f = L f

def CoreX : Prop := ThmT k → ∀ (n : ℕ) (Λ : (Mx k n → ℂ) →ₗ[ℂ] ℂ), PInvX Λ → GInvX Λ

end PositivityTheory.RgUd.AB

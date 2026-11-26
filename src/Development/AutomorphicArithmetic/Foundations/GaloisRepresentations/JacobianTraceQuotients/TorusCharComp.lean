module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ImStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.OfSupportHolds

@[expose] public section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom
attribute [local instance 10000] DivisionSemiring.to_moduleIsTorsionFree Module.Free.of_divisionRing

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsCommonEigenvectorSecond
theorem UpperTheory.Reformulated.B.CommonEigenvectorInInvariantComplexSubspace.exists_common_eigenvector :
    ∀ {ι M : Type} [inst : AddCommGroup M]
    [inst_1 : _root_.Module ℂ M] [FiniteDimensional ℂ M] (f : ι → Module.End ℂ M),
    (∀ (i j : ι), f i * f j = f j * f i) →
      ∀ (W : Submodule ℂ M),
        W ≠ ⊥ →
          (∀ (i : ι), ∀ y ∈ W, (f i : M → M) y ∈ W) →
            ∃ y ∈ W, y ≠ (0 : M) ∧ ∀ (i : ι), ∃ (c : ℂ), (f i : M → M) y = c • y := by
  intro ι M _ _ _ f hc W hW hinv
  obtain ⟨V, ⟨hVW, hV0, hVinv⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule ℂ M)).has_min
      {V : Submodule ℂ M | V ≤ W ∧ V ≠ ⊥ ∧ ∀ i, ∀ y ∈ V, f i y ∈ V} ⟨W, le_rfl, hW, hinv⟩
  obtain ⟨y, hyV, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
  refine ⟨y, hVW hyV, hy0, fun i => ?_⟩
  haveI : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV0
  obtain ⟨c, hcv⟩ := Module.End.exists_eigenvalue ((f i).restrict (hVinv i) : Module.End ℂ V)
  obtain ⟨v, hv⟩ := hcv.exists_hasEigenvector
  have hv1 : f i (v : M) = c • (v : M) := by
    have h := congrArg Subtype.val hv.apply_eq_smul
    simpa using h
  have hv0 : (v : M) ≠ 0 := fun h => hv.2 (Subtype.ext h)
  refine ⟨c, ?_⟩
  by_contra hne
  refine hmin (V ⊓ (f i).eigenspace c) ⟨inf_le_left.trans hVW, ?_, ?_⟩ ?_
  · intro h
    have hm : (v : M) ∈ V ⊓ (f i).eigenspace c :=
      ⟨v.2, Module.End.mem_eigenspace_iff.mpr hv1⟩
    rw [h] at hm
    exact hv0 ((Submodule.mem_bot ℂ).mp hm)
  · intro j z hz
    refine ⟨hVinv j z hz.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
    have hz2 : f i z = c • z := Module.End.mem_eigenspace_iff.mp hz.2
    have h : f i (f j z) = f j (f i z) := by
      rw [← Module.End.mul_apply, hc i j, Module.End.mul_apply]
    rw [h, hz2, map_smul]
  · refine lt_of_le_of_ne inf_le_left fun h => hne ?_
    have hm : y ∈ V ⊓ (f i).eigenspace c := by rw [h]; exact hyV
    exact Module.End.mem_eigenspace_iff.mp hm.2
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LiftEigen
theorem UpperTheory.Reformulated.B.R4.lift_eigen :
    ∀ {T V : Type} [inst : CommGroup T]
    [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ T V) {ψ μ : T →* ℂˣ} {v y : V},
    (∀ (t : T), ((ρ : T → V →ₗ[ℂ] V) t : V → V) v = (↑((ψ : T → ℂˣ) t) : ℂ) • v) →
      μ ≠ ψ →
        y ∉ ℂ ∙ v →
          (∀ (t : T), ((ρ : T → V →ₗ[ℂ] V) t : V → V) y - (↑((μ : T → ℂˣ) t) : ℂ) • y ∈ ℂ ∙ v) →
            v ≠ (0 : V) →
              ∃ (z : V), z ≠ (0 : V) ∧ ∀ (t : T), ((ρ : T → V →ₗ[ℂ] V) t : V → V) z = (↑((μ : T → ℂˣ) t) : ℂ) • z := by
  intro T V _ _ _ ρ ψ μ v y hv hne hy hmod _
  obtain ⟨s, hs⟩ : ∃ s, μ s ≠ ψ s := DFunLike.ne_iff.mp hne
  have hs' : ((μ s : ℂˣ) : ℂ) - ((ψ s : ℂˣ) : ℂ) ≠ 0 :=
    sub_ne_zero.mpr fun h => hs (Units.ext h)
  refine ⟨ρ s y - ((ψ s : ℂˣ) : ℂ) • y, ?_, ?_⟩
  · intro h0
    apply hy
    have h1 := hmod s
    rw [sub_eq_zero.mp h0, ← sub_smul, ← neg_sub, neg_smul, neg_mem_iff] at h1
    exact (Submodule.smul_mem_iff _ hs').mp h1
  · intro t
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hmod t)
    have hty : ρ t y = ((μ t : ℂˣ) : ℂ) • y + b • v := by
      rw [hb]; abel
    have hcomm : ρ t (ρ s y) = ρ s (ρ t y) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
    rw [map_sub, map_smul, hcomm, hty, map_add (f := _), map_smul, map_smul, hv s]
    module
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.SubQuot
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

private theorem jointEig {ι V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : ι → Module.End ℂ V) (c : ι → ℂ) (hc : ∀ i j, Commute (f i) (f j))
    (h : (⨅ i, Module.End.maxGenEigenspace (f i) (c i) : Submodule ℂ V) ≠ ⊥) :
    ∃ y, y ≠ 0 ∧ ∀ i, f i y = c i • y := by
  classical
  have hcN : ∀ i j, Commute (f i) (f j - c j • (1 : Module.End ℂ V)) := fun i j =>
    (hc i j).sub_right ((Commute.one_right _).smul_right _)
  have hW_inv : ∀ i, ∀ u ∈ (⨅ i, Module.End.maxGenEigenspace (f i) (c i) : Submodule ℂ V),
      f i u ∈ (⨅ i, Module.End.maxGenEigenspace (f i) (c i) : Submodule ℂ V) := by
    intro i u hu
    rw [Module.End.mem_iInf_maxGenEigenspace_iff] at hu ⊢
    intro j
    obtain ⟨k, hk⟩ := hu j
    refine ⟨k, ?_⟩
    rw [← Module.End.mul_apply, ← ((hcN i j).pow_right k).eq, Module.End.mul_apply, hk, map_zero]
  have hex : ∃ n, ∃ U : Submodule ℂ V, U ≠ ⊥ ∧
      U ≤ (⨅ i, Module.End.maxGenEigenspace (f i) (c i) : Submodule ℂ V) ∧
      (∀ i, ∀ u ∈ U, f i u ∈ U) ∧ Module.finrank ℂ U = n :=
    ⟨_, _, h, le_rfl, hW_inv, rfl⟩
  obtain ⟨U, hU0, hUW, hUinv, hUn⟩ := Nat.find_spec hex
  have hker : ∀ i, ∀ u ∈ U, f i u = c i • u := by
    intro i
    have hNU : ∀ m : ℕ, ∀ u ∈ U, ((f i - c i • (1 : Module.End ℂ V)) ^ m) u ∈ U := by
      intro m
      induction m with
      | zero => intro u hu; simpa using hu
      | succ m ih =>
        intro u hu
        rw [pow_succ', Module.End.mul_apply]
        have hv := ih u hu
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
        exact U.sub_mem (hUinv i _ hv) (U.smul_mem _ hv)
    let K : Submodule ℂ V := U ⊓ LinearMap.ker (f i - c i • (1 : Module.End ℂ V))
    have hKinv : ∀ j, ∀ u ∈ K, f j u ∈ K := by
      intro j u hu
      refine ⟨hUinv j u hu.1, ?_⟩
      have h2 : (f i - c i • (1 : Module.End ℂ V)) u = 0 := hu.2
      show (f i - c i • (1 : Module.End ℂ V)) (f j u) = 0
      rw [← Module.End.mul_apply, ← (hcN j i).eq, Module.End.mul_apply, h2, map_zero]
    have hK0 : K ≠ ⊥ := by
      obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
      have hexk : ∃ k, ((f i - c i • (1 : Module.End ℂ V)) ^ k) u = 0 :=
        (Module.End.mem_iInf_maxGenEigenspace_iff f c u).mp (hUW huU) i
      obtain ⟨k, hk, hkmin⟩ : ∃ k, ((f i - c i • (1 : Module.End ℂ V)) ^ k) u = 0 ∧
          ∀ m < k, ((f i - c i • (1 : Module.End ℂ V)) ^ m) u ≠ 0 :=
        ⟨Nat.find hexk, Nat.find_spec hexk, fun m hm => Nat.find_min hexk hm⟩
      have hk0 : k ≠ 0 := by
        rintro rfl
        simp at hk
        exact hu0 hk
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      refine (Submodule.ne_bot_iff K).mpr ⟨((f i - c i • (1 : Module.End ℂ V)) ^ m) u,
        ⟨hNU m u huU, ?_⟩, hkmin m (Nat.lt_succ_self m)⟩
      show (f i - c i • (1 : Module.End ℂ V)) (((f i - c i • (1 : Module.End ℂ V)) ^ m) u) = 0
      rw [← Module.End.mul_apply, ← pow_succ']
      exact hk
    have hle : Nat.find hex ≤ Module.finrank ℂ K :=
      Nat.find_min' hex ⟨K, hK0, le_trans inf_le_left hUW, hKinv, rfl⟩
    have hKU : K = U := Submodule.eq_of_le_of_finrank_eq inf_le_left
      (le_antisymm (Submodule.finrank_mono inf_le_left) (hUn ▸ hle))
    intro u hu
    have hu' : u ∈ K := hKU ▸ hu
    have h3 : (f i - c i • (1 : Module.End ℂ V)) u = 0 := hu'.2
    simpa [sub_eq_zero] using h3
  obtain ⟨y, hyU, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  exact ⟨y, hy0, fun i => hker i y hyU⟩

theorem UpperTheory.Gal.Join.subQuot :
    UpperTheory.Gal.Join.SubQuot := by
  intro T X _ _ _ _ ρ μ
  have hc : ∀ s t : T, Commute (ρ s) (ρ t) := fun s t => by
    show ρ s * ρ t = ρ t * ρ s
    rw [← map_mul, ← map_mul, mul_comm]
  have iff1 : (∃ y, y ≠ 0 ∧ ∀ t : T, ρ t y = (μ t : ℂ) • y) ↔
      (⨅ t, Module.End.maxGenEigenspace (ρ t) (μ t : ℂ) : Submodule ℂ X) ≠ ⊥ := by
    constructor
    · rintro ⟨y, hy0, hy⟩
      refine (Submodule.ne_bot_iff _).mpr ⟨y, ?_, hy0⟩
      rw [Module.End.mem_iInf_maxGenEigenspace_iff]
      intro t
      refine ⟨1, ?_⟩
      simp [hy t]
    · intro h
      exact jointEig (fun t => ρ t) (fun t => (μ t : ℂ)) hc h
  refine ⟨iff1, fun hy => ?_⟩
  have hWne := iff1.mp hy
  let c : T → ℂ := fun t => (μ t : ℂ)
  let Wχ : (T → ℂ) → Submodule ℂ X := fun χ => ⨅ t, Module.End.maxGenEigenspace (ρ t) (χ t)
  let S : Submodule ℂ X := ⨆ χ ∈ {χ : T → ℂ | χ ≠ c}, Wχ χ
  have hind : iSupIndep Wχ :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo _
      (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)
  have hdisj : Disjoint (Wχ c) S := hind.disjoint_biSup (fun h => h rfl)
  have htop : Wχ c ⊔ S = ⊤ := by
    have h1 : ⨆ χ : T → ℂ, Wχ χ = ⊤ :=
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo _
        (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)
        (fun i => Module.End.iSup_maxGenEigenspace_eq_top _)
    refine eq_top_iff.mpr (h1.symm.le.trans (iSup_le fun χ => ?_))
    by_cases hχ : χ = c
    · subst hχ; exact le_sup_left
    · exact le_sup_of_le_right (le_biSup Wχ (show χ ∈ {χ : T → ℂ | χ ≠ c} from hχ))
  have hWinv : ∀ χ t, ∀ x ∈ Wχ χ, ρ t x ∈ Wχ χ := by
    intro χ t x hx
    simp only [Wχ, Submodule.mem_iInf] at hx ⊢
    intro s
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (hc s t) (χ s) (hx s)
  have hSinv : ∀ t, ∀ x ∈ S, ρ t x ∈ S := by
    intro t
    have : S ≤ S.comap (ρ t) := iSup₂_le fun χ hχ x hx =>
      (le_biSup Wχ hχ) (hWinv χ t x hx)
    exact fun x hx => this hx
  have hNS : ∀ t (k : ℕ), ∀ x ∈ S, ((ρ t - c t • (1 : Module.End ℂ X)) ^ k) x ∈ S := by
    intro t k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply]
      have hv := ih x hx
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact S.sub_mem (hSinv t _ hv) (S.smul_mem _ hv)
  have hSlt : S < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun hS => hWne ?_
    have : Disjoint (Wχ c) ⊤ := hS ▸ hdisj
    exact disjoint_top.mp this
  obtain ⟨l0, hl00, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hSlt inferInstance
  let g : T → Module.End ℂ (Module.Dual ℂ X) := fun t => Module.Dual.transpose (R := ℂ) (ρ t)
  have hg : ∀ s t, Commute (g s) (g t) := by
    intro s t
    show g s * g t = g t * g s
    ext φ x
    simp only [Module.End.mul_apply, g, Module.Dual.transpose_apply, LinearMap.comp_apply]
    rw [← Module.End.mul_apply, (hc t s).eq, Module.End.mul_apply]
  have hpow : ∀ t (k : ℕ) (φ : Module.Dual ℂ X),
      ((g t - c t • (1 : Module.End ℂ (Module.Dual ℂ X))) ^ k) φ =
        φ ∘ₗ ((ρ t - c t • (1 : Module.End ℂ X)) ^ k) := by
    intro t k
    induction k with
    | zero => intro φ; ext x; simp
    | succ k ih =>
      intro φ
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ]
      ext x
      simp [g, Module.Dual.transpose_apply, Module.End.mul_apply, smul_eq_mul]
  obtain ⟨l, hl0, hl⟩ := jointEig g c hg (by
    refine (Submodule.ne_bot_iff _).mpr ⟨l0, ?_, hl00⟩
    rw [Module.End.mem_iInf_maxGenEigenspace_iff]
    intro t
    refine ⟨Module.finrank ℂ X, ?_⟩
    rw [hpow]
    ext x
    have hx : x ∈ Wχ c ⊔ S := htop ▸ Submodule.mem_top
    obtain ⟨w, hw, s, hs, rfl⟩ := Submodule.mem_sup.mp hx
    have hw' : w ∈ Module.End.maxGenEigenspace (ρ t) (c t) :=
      (Submodule.mem_iInf _).mp hw t
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.mem_genEigenspace_nat,
      LinearMap.mem_ker] at hw'
    have hs' : l0 (((ρ t - c t • (1 : Module.End ℂ X)) ^ Module.finrank ℂ X) s) = 0 := by
      have hm := Submodule.mem_map_of_mem (f := l0) (hNS t (Module.finrank ℂ X) s hs)
      rw [hmap] at hm
      exact (Submodule.mem_bot ℂ).mp hm
    simp only [LinearMap.comp_apply, map_add (f := _), hw', map_zero, zero_add, LinearMap.zero_apply]
    exact hs')
  refine ⟨l, hl0, fun t y => ?_⟩
  have := congrArg (fun φ : Module.Dual ℂ X => φ y) (hl t)
  simpa [g, Module.Dual.transpose_apply, smul_eq_mul] using this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ExpSub
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.QuotEmb
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.quotEmb :
    UpperTheory.Gal.Join.QuotEmb := by
  intro k _ _ _ _ n V _ _ π hπ hirr ω l hl0 hl
  exact GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hirr (torusChar ω) l hl0 hl
end

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

private theorem continuous_mulSingle_units {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] {n : ℕ} (i : Fin n) :
    Continuous (MonoidHom.mulSingle (fun _ : Fin n => kˣ) i) :=
  continuous_mulSingle (A := fun _ : Fin n => kˣ) i

theorem UpperTheory.Gal.Join.expSub :
    UpperTheory.Gal.Join.ExpSub := by
  intro k _ _ _ _ n V _ _ π hsm hirr μ hexp
  obtain ⟨y, hy0, hy⟩ := hexp
  have hJs : IsSmooth (jacB π) := isSmooth_jacB hsm
  have hμ : IsSmoothChar μ := by
    show IsOpen (μ.ker : Set (Fin n → kˣ))
    refine Subgroup.isOpen_of_mem_nhds μ.ker (g := 1) ?_
    refine Filter.mem_of_superset ((hJs y).mem_nhds (by simp)) ?_
    intro t ht
    have h1 : ((μ t : ℂˣ) : ℂ) • y = (1 : ℂ) • y := by
      rw [one_smul, ← hy t]
      exact ht
    have h2 : ((μ t : ℂˣ) : ℂ) = 1 := smul_left_injective ℂ hy0 h1
    simp only [SetLike.mem_coe, MonoidHom.mem_ker]
    exact Units.ext h2
  set ω : Fin n → kˣ →* ℂˣ := fun i => μ.comp (MonoidHom.mulSingle (fun _ : Fin n => kˣ) i) with hωdef
  have hωμ : torusChar ω = μ := by
    refine MonoidHom.ext fun t => ?_
    rw [torusChar_apply]
    simp only [hωdef, MonoidHom.comp_apply, MonoidHom.mulSingle_apply]
    rw [← map_prod, Finset.univ_prod_mulSingle]
  have hωs : ∀ i, IsSmoothChar (ω i) := fun i => hμ.comp _ (continuous_mulSingle_units i)
  have hlen : HasFiniteLength (jacB π) := by
    have hj := (GlobalTheory.T.bernstein_zelevinsky_finiteness k).2.1 (Fin n) (Fin n) (fun _ => Unit) (points (Fin n)) V π hsm
      (hasFiniteLength_of_isIrreducible hirr)
    exact (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).mpr hj
  obtain ⟨ψ, l, hl0, hl, hψω⟩ := GlobalTheory.T.exists_torusEigenform_of_compactTorus_eigenvector k n _ (jacB π) y ω hJs hlen hωs hy0
    (fun t _ => by rw [hy t, hωμ])
  have hψs : ∀ i, IsSmoothChar (ψ i) := fun i =>
    GlobalTheory.TameIwahori.isSmoothChar_of_eq_on_units (hωs i) (hψω i)
  have hsubψ : IsSubquotient π (prinSeries ψ) := quotEmb k n V π hsm hirr ψ l hl0 hl
  haveI : Nontrivial V := GroundTheory.Automorphic.RestrictedTensor.nontrivial_of_isIrreducible hirr
  have hcyc : Cyc (RingEquiv.refl k) 1 := ⟨fun _ => rfl, one_pos, fun _ => rfl⟩
  have hsemi : Semi (RingEquiv.refl k) π LinearMap.id := by
    intro g v
    simp [sg]
  have hinv : ∀ i, UpperTheory.Gal.LocD.Inv (RingEquiv.refl k) (ψ i) := by
    intro i x
    congr 1
  obtain ⟨-, hfd, -⟩ := locDesc_holds k n (RingEquiv.refl k) 1 hcyc V π hirr ψ hψs hinv hsubψ LinearMap.id hsemi
    (by
      intro h
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      exact hv (by simpa using LinearMap.congr_fun h v))
  haveI := hfd
  obtain ⟨l', hl'0, hl'⟩ := (subQuot (Fin n → kˣ) _ (jacB π) μ).2 ⟨y, hy0, hy⟩
  refine ⟨ω, hωμ.symm, hωs, quotEmb k n V π hsm hirr ω l' hl'0 ?_⟩
  intro t z
  rw [hωμ]
  exact hl' t z
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceExp
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

private theorem lift_eigen {T V : Type} [CommGroup T] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ T V) {ψ μ : T →* ℂˣ} {v y : V} (hψ : ∀ t, ρ t v = (ψ t : ℂ) • v)
    (hne : μ ≠ ψ) (hy : y ∉ Submodule.span ℂ {v})
    (hq : ∀ t, ρ t y - (μ t : ℂ) • y ∈ Submodule.span ℂ {v}) (hv : v ≠ 0) :
    ∃ z, z ≠ 0 ∧ ∀ t, ρ t z = (μ t : ℂ) • z :=
  _root_.UpperTheory.Reformulated.B.R4.lift_eigen ρ hψ hne hy hq hv

private theorem exists_eigenchars {T : Type} [CommGroup T] (d : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ T V), Module.finrank ℂ V = d →
    ∃ E : Multiset (T →* ℂˣ), (∀ t, LinearMap.trace ℂ V (ρ t) = (E.map fun χ => (χ t : ℂ)).sum) ∧
      ∀ μ, μ ∈ E ↔ ∃ y, y ≠ 0 ∧ ∀ t, ρ t y = (μ t : ℂ) • y := by
  induction d with
  | zero =>
    intro V _ _ _ ρ h
    haveI : Subsingleton V := Module.finrank_zero_iff.1 h
    refine ⟨0, fun t => ?_, fun μ => ?_⟩
    · simp [Subsingleton.elim (ρ t) 0]
    · simp [Subsingleton.elim _ (0 : V)]
  | succ d ih =>
    intro V _ _ _ ρ h
    haveI : Nontrivial V := Module.finrank_pos_iff.1 (by rw [h]; exact d.succ_pos)
    obtain ⟨ψ, v, hv, hψ⟩ := GlobalTheory.exists_character_eigenvector_of_commute ℂ T V ρ fun a b => by
      rw [← map_mul, mul_comm, map_mul]
    have hst : ∀ g, Submodule.span ℂ {v} ≤ (Submodule.span ℂ {v}).comap (ρ g) := fun g => by
      rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_comap, hψ]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    have hd : Module.finrank ℂ (V ⧸ Submodule.span ℂ {v}) = d := by
      have := (Submodule.span ℂ {v}).finrank_quotient_add_finrank
      rw [finrank_span_singleton hv, h] at this
      omega
    obtain ⟨E, h1, h2⟩ := ih _ (ρ.quotient _ hst) hd
    refine ⟨ψ ::ₘ E, fun t => ?_, fun μ => ⟨fun hμ => ?_, ?_⟩⟩
    · rw [GlobalTheory.IwahoriTraceProof.trace_eq_add_quot (ρ t) hv (hψ t) (ρ.quotient _ hst t) fun _ => rfl, h1,
        Multiset.map_cons, Multiset.sum_cons]
    · by_cases hne : μ = ψ
      · exact ⟨v, hv, hne ▸ hψ⟩
      obtain ⟨q, hq0, hq⟩ := (h2 μ).1 ((Multiset.mem_cons.1 hμ).resolve_left hne)
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      refine lift_eigen ρ hψ hne (fun hy => hq0 ((Submodule.Quotient.mk_eq_zero _).2 hy)) (fun t => ?_) hv
      refine (Submodule.Quotient.eq _).1 ?_
      exact hq t
    · rintro ⟨y, hy, hμ⟩
      by_cases hne : μ = ψ
      · exact hne ▸ Multiset.mem_cons_self _ _
      refine Multiset.mem_cons_of_mem ((h2 μ).2 ⟨Submodule.Quotient.mk y, fun h0 => hne ?_, fun t => ?_⟩)
      · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
        refine MonoidHom.ext fun t => Units.ext ?_
        have h3 := hμ t
        rw [map_smul, hψ, smul_comm, ← sub_eq_zero, ← sub_smul] at h3
        rcases smul_eq_zero.1 h3 with h3 | h3
        · exact (sub_eq_zero.1 h3).symm
        · exact absurd h3 hy
      · exact congrArg (Submodule.Quotient.mk (p := Submodule.span ℂ {v})) (hμ t)

theorem UpperTheory.Gal.Join.traceExp :
    UpperTheory.Gal.Join.TraceExp := by
  intro T X _ _ _ ρ P _ hP
  let R : Representation ℂ T P :=
    { toFun := fun t => (ρ t).restrict (hP t)
      map_one' := by
        ext y
        simp
      map_mul' := fun a b => by
        ext y
        simp }
  obtain ⟨E, h1, h2⟩ := exists_eigenchars (T := T) _ P R rfl
  refine ⟨E, fun t => ?_, fun μ => ?_⟩
  · rw [trIn, dite_eq_left (hP t)]
    exact h1 t
  · rw [h2]
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨y, y.2, fun h0 => hy (Subtype.ext h0), fun t => congrArg Subtype.val (h t)⟩
    · rintro ⟨y, hyP, hy, h⟩
      exact ⟨⟨y, hyP⟩, fun h0 => hy (congrArg Subtype.val h0), fun t => Subtype.ext (h t)⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ExistsCommonEigenvector
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

private lemma exists_common_eigenvector {ι M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (f : ι → Module.End ℂ M) (hc : ∀ i j, f i * f j = f j * f i) (W : Submodule ℂ M) (hW : W ≠ ⊥)
    (hst : ∀ i, ∀ y ∈ W, f i y ∈ W) :
    ∃ y ∈ W, y ≠ 0 ∧ ∀ i, ∃ c : ℂ, f i y = c • y :=
  _root_.UpperTheory.Reformulated.B.CommonEigenvectorInInvariantComplexSubspace.exists_common_eigenvector f hc W hW hst

theorem UpperTheory.Gal.Join.twExp :
    UpperTheory.Gal.Join.TwExp := by
  intro T X _ _ _ ρ P _ s A hρ hA hAρ t₁ htr
  let r : T → Module.End ℂ P := fun t => (ρ t).restrict (hρ t)
  let A' : Module.End ℂ P := A.restrict hA
  have r_apply : ∀ t (y : P), ((r t y : P) : X) = ρ t y := fun t y => rfl
  have A_apply : ∀ y : P, ((A' y : P) : X) = A y := fun y => rfl
  have r_mul : ∀ a b, r (a * b) = r a * r b := by
    intro a b
    ext y
    simp [r_apply, Module.End.mul_apply, map_mul]
  have hcomm : ∀ a b, r a * r b = r b * r a := by
    intro a b
    rw [← r_mul, ← r_mul, mul_comm]
  have hsemi : ∀ t, A' * r t = r (s t) * A' := by
    intro t
    ext y
    simp [r_apply, A_apply, Module.End.mul_apply, hAρ]
  let N : (T → ℂ) → Submodule ℂ P := fun χ => ⨅ t, (r t).maxGenEigenspace (χ t)
  have hmaps : ∀ a b c, Set.MapsTo (r a) ((r b).maxGenEigenspace c) ((r b).maxGenEigenspace c) :=
    fun a b c => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm b a) c
  have hind : iSupIndep N := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo r hmaps
  have htop : ⨆ χ, N χ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute r
      (fun a b _ => hcomm a b) (fun t => Module.End.iSup_maxGenEigenspace_eq_top (r t))
  let f : Module.End ℂ P := r t₁ * A'
  have hAN : ∀ χ, Set.MapsTo f (N χ) (N (χ ∘ s.symm)) := by
    intro χ y hy
    have hy' : ∀ t, y ∈ (r t).maxGenEigenspace (χ t) := fun t => (Submodule.mem_iInf _).mp hy t
    refine (Submodule.mem_iInf _).mpr fun t => ?_
    have key : A' y ∈ (r t).maxGenEigenspace (χ (s.symm t)) := by
      obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp (hy' (s.symm t))
      refine (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨k, ?_⟩
      have hsb : SemiconjBy A' (r (s.symm t) - χ (s.symm t) • (1 : Module.End ℂ P))
          (r t - χ (s.symm t) • (1 : Module.End ℂ P)) := by
        have h1 := hsemi (s.symm t)
        rw [MulEquiv.apply_symm_apply] at h1
        unfold SemiconjBy
        rw [mul_sub, sub_mul, h1]
        simp
      have := congrArg (fun g : Module.End ℂ P => g y) (hsb.pow_right k).eq
      simp only [Module.End.mul_apply, hk, map_zero] at this
      exact this.symm
    exact hmaps t₁ t _ key

  have hex : ∃ χ : T → ℂ, χ ∘ s = χ ∧ N χ ≠ ⊥ := by
    by_contra hno
    push_neg at hno
    let J := {χ : T → ℂ // χ ∘ s ≠ χ}
    let N' : J → Submodule ℂ P := fun j => N j.1
    have hind' : iSupIndep N' := hind.comp Subtype.val_injective
    have htop' : ⨆ j, N' j = ⊤ := by
      rw [eq_top_iff, ← htop]
      refine iSup_le fun χ => ?_
      by_cases h : χ ∘ s = χ
      · rw [hno χ h]
        exact bot_le
      · exact le_iSup N' ⟨χ, h⟩
    have hint : DirectSum.IsInternal N' :=
      DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind' htop'
    have hne : ∀ χ : T → ℂ, χ ∘ s ≠ χ → χ ∘ s.symm ≠ χ := by
      intro χ h e
      apply h
      funext t
      have := congrFun e (s t)
      simpa using this.symm
    let σ : J → J := fun j => ⟨j.1 ∘ s.symm, by
      intro e
      apply hne j.1 j.2
      funext t
      have := congrFun e t
      simpa [Function.comp] using this.symm⟩
    have hσ : ∀ j, σ j ≠ j := fun j e => hne j.1 j.2 (congrArg Subtype.val e)
    have hzero : LinearMap.trace ℂ P f = 0 :=
      LinearMap.trace_eq_zero_of_mapsTo_ne hint σ hσ (fun j => hAN j.1)
    apply htr
    have hst : ∀ y ∈ P, (ρ t₁ ∘ₗ A) y ∈ P := fun y hy => hρ t₁ _ (hA y hy)
    have hfeq : (ρ t₁ ∘ₗ A).restrict hst = f := by
      ext y
      rfl
    unfold trIn
    rw [dite_eq_left hst, hfeq, hzero]
  obtain ⟨χ, hχ, hN⟩ := hex
  have hNst : ∀ t, ∀ y ∈ N χ, r t y ∈ N χ := by
    intro t y hy
    exact (Submodule.mem_iInf _).mpr fun t' => hmaps t t' _ ((Submodule.mem_iInf _).mp hy t')
  obtain ⟨y, hyN, hy0, hy⟩ := exists_common_eigenvector r hcomm (N χ) hN hNst
  choose c hc using hy
  have hcχ : ∀ t, c t = χ t := by
    intro t
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp ((Submodule.mem_iInf _).mp hyN t)
    have hpow : ∀ m : ℕ, ((r t - χ t • (1 : Module.End ℂ P)) ^ m) y = (c t - χ t) ^ m • y := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, hc t]
        simp only [LinearMap.smul_apply, Module.End.one_apply, ← sub_smul, smul_smul, pow_succ']
        ring_nf
    rw [hpow k] at hk
    have := (smul_eq_zero.mp hk).resolve_right hy0
    by_contra hne
    exact pow_ne_zero k (sub_ne_zero.mpr hne) this
  have hc1 : c 1 = 1 := by
    have h1 : r 1 = 1 := by
      ext v
      simp [r_apply]
    have h2 := hc 1
    rw [h1, Module.End.one_apply] at h2
    have h3 : (c 1 - 1) • y = 0 := by
      rw [sub_smul, one_smul, ← h2, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hy0)
  have hcmul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    have h2 := hc (a * b)
    rw [r_mul, Module.End.mul_apply, hc b, map_smul, hc a, smul_smul] at h2
    have h3 : (c (a * b) - c b * c a) • y = 0 := by
      rw [sub_smul, ← h2, sub_self]
    rw [sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hy0), mul_comm]
  let m : T →* ℂ := { toFun := c, map_one' := hc1, map_mul' := hcmul }
  refine ⟨m.toHomUnits, fun t => ?_, (y : X), y.2, fun h => hy0 (Subtype.ext h), fun t => ?_⟩
  · apply Units.ext
    simp only [MonoidHom.coe_toHomUnits]
    change c (s t) = c t
    rw [hcχ, hcχ]
    exact congrFun hχ t
  · simp only [MonoidHom.coe_toHomUnits]
    change ρ t (y : X) = c t • (y : X)
    exact congrArg Subtype.val (hc t)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ExpLev
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.expLev :
    UpperTheory.Gal.Join.ExpLev := by
  intro k _ _ _ _ n V _ _ π hs y
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ y
  let U : Subgroup (GL (Fin n) k) :=
    { carrier := {g | π g v = v}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  refine ⟨U, hs v, fun K hK => ?_⟩
  refine Submodule.mem_map_of_mem (p := fixed π K) ?_
  intro h
  have hv : π (h : GL (Fin n) k) v = v := hK h.2
  simpa using hv
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.CharDom
noncomputable section

open ValuativeRel
open scoped Classical

namespace UpperTheory.Gal.Join

private theorem indep {T : Type} [CommGroup T] (M : Submonoid T) (hM : ∀ t : T, ∃ s ∈ M, s * t ∈ M) (t₀ : T)
    (E E' : Multiset (T →* ℂˣ)) (c c' : ℂ) (hc : c ≠ 0)
    (h : ∀ t ∈ M, c * (E.map fun μ => (μ (t₀ * t) : ℂ)).sum = c' * (E'.map fun μ => (μ (t₀ * t) : ℂ)).sum) :
    ∀ μ ∈ E, μ ∈ E' := by
  classical
  let ρ : (T →* ℂˣ) → (M →* ℂ) := fun μ => (Units.coeHom ℂ).comp (μ.comp M.subtype)
  have hρm : ∀ μ (m : M), ρ μ m = (μ m : ℂ) := fun _ _ => rfl
  have hρinj : Function.Injective ρ := by
    intro μ ν hμν
    have hM' : ∀ m ∈ M, μ m = ν m := by
      intro m hm
      apply Units.ext
      have := DFunLike.congr_fun hμν ⟨m, hm⟩
      rw [hρm, hρm] at this
      exact this
    refine MonoidHom.ext fun t => ?_
    obtain ⟨s, hs, hst⟩ := hM t
    have e : t = s⁻¹ * (s * t) := by rw [inv_mul_cancel_left]
    rw [e, map_mul μ, map_mul ν, map_inv μ, map_inv ν, hM' s hs, hM' _ hst]
  have hli : LinearIndependent ℂ (fun μ : T →* ℂˣ => ((ρ μ : M →* ℂ) : M → ℂ)) :=
    (linearIndependent_monoidHom M ℂ).comp ρ hρinj
  intro μ hμ
  by_contra hμ'
  let S := (E + E').toFinset
  let g : (T →* ℂˣ) → ℂ := fun ν => (c * E.count ν - c' * E'.count ν) * (ν t₀ : ℂ)
  have conv : ∀ F : Multiset (T →* ℂˣ), F.toFinset ⊆ S → ∀ t : T,
      (F.map fun ν => (ν (t₀ * t) : ℂ)).sum = ∑ ν ∈ S, (F.count ν : ℂ) * ((ν t₀ : ℂ) * (ν t : ℂ)) := by
    intro F hF t
    rw [Finset.sum_multiset_map_count, Finset.sum_subset hF]
    · apply Finset.sum_congr rfl
      intro ν _
      rw [nsmul_eq_mul, map_mul, Units.val_mul]
    · intro ν _ hν
      rw [Multiset.count_eq_zero.mpr (by simpa using hν)]
      simp
  have hsum : ∑ ν ∈ S, g ν • ((ρ ν : M →* ℂ) : M → ℂ) = 0 := by
    funext m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have h1 := h m m.2
    rw [conv E (fun x hx => Multiset.mem_toFinset.mpr
        (Multiset.mem_add.mpr (Or.inl (Multiset.mem_toFinset.mp hx)))) m,
      conv E' (fun x hx => Multiset.mem_toFinset.mpr
        (Multiset.mem_add.mpr (Or.inr (Multiset.mem_toFinset.mp hx)))) m,
      Finset.mul_sum, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
    rw [← h1]
    apply Finset.sum_congr rfl
    intro ν _
    rw [hρm]
    simp only [g]
    ring
  have h0 := linearIndependent_iff'.mp hli S g hsum μ
    (Multiset.mem_toFinset.mpr (Multiset.mem_add.mpr (Or.inl hμ)))
  simp only [g, Multiset.count_eq_zero.mpr hμ', Nat.cast_zero, mul_zero, sub_zero] at h0
  rcases mul_eq_zero.mp h0 with h2 | h2
  · rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hc h3
    · exact (Multiset.count_pos.mpr hμ).ne' (by exact_mod_cast h3)
  · exact (μ t₀).ne_zero h2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private def domM (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    Submonoid (Fin n → kˣ) where
  carrier := {t | Dom t}
  mul_mem' := by
    intro a b ha hb i j hij
    simp only [Pi.mul_apply, Units.val_mul, map_mul]
    exact mul_le_mul' (ha i j hij) (hb i j hij)
  one_mem' := by
    intro i j _
    simp

private theorem dom_translate (t : Fin n → kˣ) : ∃ s ∈ domM k n, s * t ∈ domM k n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, (domM k 0).one_mem, ?_⟩
    show Dom _
    intro i
    exact i.elim0
  · obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
      (fun p => valuation k ((t p.1 / t p.2 : kˣ) : k)) ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
    have hx1 : 1 ≤ valuation k ((t p.1 / t p.2 : kˣ) : k) := by
      have := hp (⟨0, hn⟩, ⟨0, hn⟩) (Finset.mem_univ _)
      simpa using this
    have hxt : ∀ i j, valuation k (t i : k) ≤
        valuation k ((t p.1 / t p.2 : kˣ) : k) * valuation k (t j : k) := by
      intro i j
      have := hp (i, j) (Finset.mem_univ _)
      have e : (t i : k) = ((t i / t j : kˣ) : k) * (t j : k) := by simp
      rw [e, map_mul]
      gcongr
    refine ⟨fun i => (t p.1 / t p.2) ^ (i : ℕ), ?_, ?_⟩
    · show Dom _
      intro i j hij
      simp only [Units.val_pow_eq_pow_val, map_pow]
      exact pow_le_pow_right₀ hx1 (le_of_lt hij)
    · show Dom _
      intro i j hij
      simp only [Pi.mul_apply, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
      have hij' : (i : ℕ) + 1 ≤ j := hij
      have hpw := pow_le_pow_right₀ hx1 hij'
      calc valuation k ((t p.1 / t p.2 : kˣ) : k) ^ (i : ℕ) * valuation k (t i : k)
          ≤ valuation k ((t p.1 / t p.2 : kˣ) : k) ^ (i : ℕ) *
            (valuation k ((t p.1 / t p.2 : kˣ) : k) * valuation k (t j : k)) := by
            gcongr
            exact hxt i j
        _ = valuation k ((t p.1 / t p.2 : kˣ) : k) ^ ((i : ℕ) + 1) * valuation k (t j : k) := by
            rw [pow_succ, mul_assoc]
        _ ≤ valuation k ((t p.1 / t p.2 : kˣ) : k) ^ (j : ℕ) * valuation k (t j : k) := by
            gcongr

theorem charDom : CharDom := by
  intro k _ _ _ _ n t₀ E E' c c' hc h
  have hind := indep (domM k n) (fun t => dom_translate t) t₀ E E' c c' hc h
  refine ⟨hind, fun hE => ?_⟩
  by_contra hne
  push_neg at hne
  obtain ⟨μ, hμ⟩ := Multiset.exists_mem_of_ne_zero hE
  have := indep (domM k n) (fun t => dom_translate t) t₀ E 0 1 0 one_ne_zero
    (fun t ht => by rw [one_mul, hne t ht]; simp) μ hμ
  simp at this

end UpperTheory.Gal.Join
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.SubPerm
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.LocGL
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.subPerm :
    UpperTheory.Gal.Join.SubPerm := by
  intro k _ _ _ _ n V _ _ π hi ω hω w h
  have hw : ∀ i, IsSmoothChar ((ω ∘ w) i) := fun i => hω (w i)
  have h1 := (UpperTheory.Gal.LocD.ofSupport k n V π ω hω).2 ⟨hi, h⟩
  have e : (Finset.univ.val.map fun i => IrrGL.ofChar ((ω ∘ w) i) (hw i)) =
      Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i) := by
    have e' := congrArg (Multiset.map fun i => IrrGL.ofChar (ω i) (hω i)) (Multiset.map_univ_val_equiv w)
    rw [Multiset.map_map] at e'
    exact e'
  rw [← e] at h1
  exact ((UpperTheory.Gal.LocD.ofSupport k n V π (ω ∘ w) hw).1 h1).2
end

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

namespace UpperTheory.Gal.Join

private theorem trIn_smul {X : Type} [AddCommGroup X] [Module ℂ X] {P : Submodule ℂ X} {T : X →ₗ[ℂ] X}
    (h : ∀ y ∈ P, T y ∈ P) (c : ℂ) : trIn P (T ∘ₗ (c • LinearMap.id)) = c * trIn P T := by
  have h' : ∀ y ∈ P, (T ∘ₗ (c • LinearMap.id)) y ∈ P := fun y hy => h _ (P.smul_mem c hy)
  rw [trIn, trIn, dite_eq_left h, dite_eq_left h', ← smul_eq_mul, ← map_smul]
  congr 1
  ext y
  simp [LinearMap.restrict_apply]

private theorem adm {K : Type} [Field K] [NumberField K] {n : ℕ} {w : Pl K} (τ : SmIrr (Gw n w)) : IsAdmissible τ.ρ :=
  PositivityTheory.Exh.irreducibleAdmissibleGL _ n τ.V τ.ρ τ.smooth τ.irred

theorem liftExp (h : CoreId) : LiftExp := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ' μ ⟨y, hy0, hy⟩
  obtain ⟨A, hA, hA0, hc⟩ := h F E σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ'
  obtain ⟨U, hU, hy'⟩ := expLev _ n _ τ.ρ τ.smooth y
  obtain ⟨K', -, K, hK, l', l, hst, c, t₀, hc0, hid⟩ := hc ⊤ U (by simp) hU
  obtain ⟨f', st', sa'⟩ := imStab _ n _ τ'.ρ (adm τ') K' l'
  obtain ⟨f, st, -⟩ := imStab _ n _ τ.ρ (adm τ) K l
  obtain ⟨E', e', m'⟩ := traceExp _ _ (jacB τ'.ρ) (imK τ'.ρ K') st'
  obtain ⟨E₀, e, m⟩ := traceExp _ _ (jacB τ.ρ) (imK τ.ρ K) st
  have hμ : μ.comp (nT n N) ∈ E₀.map fun μ => μ.comp (nT n N) :=
    Multiset.mem_map_of_mem _ ((m μ).2 ⟨y, hy' K hK, hy0, hy⟩)
  have hid' : ∀ t, Dom t → trIn (imK τ'.ρ K') (jacB τ'.ρ (t₀ * t) ∘ₗ jacA hA) =
      c * ((E₀.map fun μ => μ.comp (nT n N)).map fun μ => (μ (t₀ * t) : ℂ)).sum := fun t ht => by
    rw [hid t ht, e, Multiset.map_map]
    rfl
  obtain ⟨t₁, ht₁, hne⟩ := (charDom _ n t₀ (E₀.map fun μ => μ.comp (nT n N)) _ 1 1 one_ne_zero fun _ _ => rfl).2
    (fun h0 => by rw [h0] at hμ; exact Multiset.notMem_zero _ hμ)
  obtain ⟨μ', hinv, z, -, hz0, hz⟩ := twExp _ _ (jacB τ'.ρ) (imK τ'.ρ K')
    (MulEquiv.piCongrRight fun _ => Units.mapEquiv σw.toMulEquiv) (jacA hA) st' (sa' σw A hA hst)
    (fun t y => jacSemi _ n σw hN.cyc.isom _ τ'.ρ A hA t y) (t₀ * t₁) (by rw [hid' t₁ ht₁]; exact mul_ne_zero hc0 hne)
  obtain ⟨ω', rfl, s', q'⟩ := expSub _ n _ τ'.ρ τ'.smooth τ'.irred μ' ⟨z, hz0, hz⟩
  have i' : ∀ i, Inv σw (ω' i) := fun i x => by
    have h1 := hinv (Pi.mulSingle i x)
    have h2 : ∀ x, torusChar ω' (Pi.mulSingle i x) = ω' i x := fun x => by
      rw [torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, map_one]) (by simp),
        Pi.mulSingle_eq_same]
    rw [← h2, ← h2, ← h1]
    congr 1
    funext j
    change _ = Units.mapEquiv σw.toMulEquiv ((Pi.mulSingle i x : Fin n → _) j)
    by_cases hj : j = i
    · subst hj
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
      rfl
    · rw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, map_one]
  obtain ⟨-, -, -, c', hc', hsc, -⟩ := locDesc_holds _ n σw _ hN.cyc _ τ'.ρ τ'.irred ω' s' i' q' A hA hA0
  have key := (charDom _ n t₀ (E₀.map fun μ => μ.comp (nT n N)) E' c c' hc0 fun t ht => by
    rw [← hid' t ht, hsc, trIn_smul (st' _), e']).1 _ hμ
  obtain ⟨x, -, hx0, hx⟩ := (m' _).1 key
  exact ⟨x, hx0, hx⟩

private theorem exp_of_sub {K : Type} [Field K] [NumberField K] {n : ℕ} {w : Pl K} (τ : SmIrr (Gw n w))
    {ω : Fin n → (w.adicCompletion K)ˣ →* ℂˣ} (s : ∀ i, IsSmoothChar (ω i)) (q : IsSubquotient τ.ρ (prinSeries ω)) :
    ∃ p : Equiv.Perm (Fin n), IsExp τ.ρ (torusChar (ω ∘ p)) := by
  have hnt : Nontrivial τ.V := GroundTheory.Automorphic.RestrictedTensor.nontrivial_of_isIrreducible τ.irred
  obtain ⟨h1, h2, h3, -⟩ := locDesc_holds _ n (RingEquiv.refl _) 1 ⟨fun _ => rfl, one_pos, fun _ => rfl⟩ _ τ.ρ τ.irred ω s
    (fun _ _ => rfl) q LinearMap.id (fun _ _ => rfl) (fun h => by
      obtain ⟨x, hx⟩ := exists_ne (0 : τ.V)
      exact hx (LinearMap.congr_fun h x))
  obtain ⟨E₀, e, m⟩ := traceExp _ _ (jacB τ.ρ) ⊤ fun _ _ _ => trivial
  have hne : E₀ ≠ 0 := by
    rintro rfl
    have h4 := e 1
    rw [map_one, trIn, dite_eq_left fun _ _ => Submodule.mem_top] at h4
    have h5 : LinearMap.trace ℂ (⊤ : Submodule ℂ (Jacquet τ.ρ (unipB _ (Fin n)))) 1 = 0 := h4
    rw [LinearMap.trace_one, finrank_top, Nat.cast_eq_zero] at h5
    exact Module.finrank_pos.ne' h5
  obtain ⟨μ, hμ⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨y, -, hy⟩ := (m μ).1 hμ
  obtain ⟨p, rfl⟩ := h3 μ ((subQuot _ _ (jacB τ.ρ) μ).1.1 ⟨y, hy⟩)
  exact ⟨p, y, hy⟩

private theorem torusChar_inj {R : Type} [CommRing R] {n : ℕ} {a b : Fin n → Rˣ →* ℂˣ} (h : torusChar a = torusChar b) : a = b := by
  have h2 : ∀ (a : Fin n → Rˣ →* ℂˣ) i x, torusChar a (Pi.mulSingle i x) = a i x := fun a i x => by
    rw [torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, map_one]) (by simp),
      Pi.mulSingle_eq_same]
  funext i
  ext1 x
  rw [← h2, ← h2, h]

private theorem torusChar_comp {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (a : Fin n → Rˣ →* ℂˣ) (N : Sˣ →* Rˣ) :
    (torusChar a).comp (nT n N) = torusChar fun i => (a i).comp N := by
  refine MonoidHom.ext fun t => ?_
  rw [MonoidHom.comp_apply, torusChar_apply, torusChar_apply]
  rfl

theorem liftGood (h : CoreId) : LiftGood := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ' ω s q
  obtain ⟨p, hp'⟩ := exp_of_sub τ s q
  have h1 := liftExp h F E σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ' _ hp'
  obtain ⟨ω', e, s', q'⟩ := expSub _ n _ τ'.ρ τ'.smooth τ'.irred _ h1
  rw [torusChar_comp] at e
  obtain rfl := torusChar_inj e
  have h2 := subPerm _ n _ τ'.ρ τ'.irred _ s' p.symm q'
  have h3 : (fun i => ((ω ∘ p) i).comp N) ∘ p.symm = fun i => (ω i).comp N := funext fun i => by simp
  rwa [h3] at h2

end UpperTheory.Gal.Join

module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis
public import Development.EtaleCohomology.EtaleTrace.PtCoverPf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PPieceStab
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.pieceStab_of :
    HopGal → PieceStab := by
  intro hG l _ k _ hl H hfet Ω _ _ L _ _ θ σ x hx
  simp only [piece, Submodule.mem_iInf] at hx ⊢
  intro g
  obtain ⟨d, hd⟩ := hfet g
  have hc := hG l k hl H Ω g d hd σ
  have hxg := hx g
  rw [Module.End.mem_eigenspace_iff] at hxg ⊢
  have e : (LinearMap.baseChange L (hop l H Ω g)) ((galV l H Ω L σ) x)
      = (galV l H Ω L σ) ((LinearMap.baseChange L (hop l H Ω g)) x) := by
    show ((LinearMap.baseChange L (hop l H Ω g)) ∘ₗ (LinearMap.baseChange L (galTot l Ω H.q σ))) x
      = ((LinearMap.baseChange L (galTot l Ω H.q σ)) ∘ₗ (LinearMap.baseChange L (hop l H Ω g))) x
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hc]
  rw [e, hxg, map_smul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PExtCont
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.extCont_of :
    ExtCont := by
  intro Γ F L _ _ _ _ _ _ _ hF M _ _ _ a ha v μ
  induction v using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add (f := _)]
    exact hx.add hy
  | tmul l m =>
    let b := Module.finBasis F M
    have key : ∀ g, μ ((LinearMap.baseChange L (a g)) (l ⊗ₜ m)) =
        ∑ i, algebraMap F L (b.coord i (a g m)) * μ (l ⊗ₜ b i) := by
      intro g
      rw [LinearMap.baseChange_tmul]
      conv_lhs => rw [← b.sum_repr (a g m)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [TensorProduct.tmul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.tmul_smul, ← algebraMap_smul L, map_smul, smul_eq_mul]
      rfl
    simp_rw [key]
    exact continuous_finsetSum _ fun i _ => (hF.comp (ha m (b.coord i))).mul continuous_const
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PStabOpen
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.stabOpen_of :
    HtDesc → StabOpen := by
  intro h l _ k Ω _ _ _ _ X p hqc hqs n i x m
  obtain ⟨L, hL, z, hz⟩ := h (l ^ m) k Ω p hqc hqs n i (x.1 m)
  have fix : ∀ τ ∈ L.fixingSubgroup,
      GlobalTheory.EtC.pull (ZMod (l ^ m)) (sch.map (galMap Ω p τ)) (tw (l ^ m) i) n (x.1 m) = x.1 m := by
    intro τ hτ
    rw [← hz, ← GlobalTheory.EtC.pull_comp, ← Functor.map_comp, LateralTheory.EWeil.StabPf.galMap_proj L p τ hτ]
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun g => g * σ⁻¹) ⁻¹' (L.fixingSubgroup : Set _), ?_, ?_, ?_⟩
  · intro g hg
    have hg' : g * σ⁻¹ ∈ L.fixingSubgroup := hg
    have e : g = (g * σ⁻¹) * σ := by group
    show ((galHl l Ω p n i g) x).1 m = x.1 m
    rw [e, map_mul, Module.End.mul_apply]
    change GlobalTheory.EtC.pull (ZMod (l ^ m)) (sch.map (galMap Ω p (g * σ⁻¹))) (tw (l ^ m) i) n
      (((galHl l Ω p n i σ) x).1 m) = x.1 m
    have hσ' : ((galHl l Ω p n i σ) x).1 m = x.1 m := hσ
    rw [hσ']
    exact fix _ hg'
  · exact (IntermediateField.fixingSubgroup_isOpen L).preimage (continuous_mul_const σ⁻¹)
  · show σ * σ⁻¹ ∈ L.fixingSubgroup
    rw [mul_inv_cancel]
    exact one_mem _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PHtotFin
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem finOfDeg {K : Type} [Field K] {A : ℤ → Type*} [∀ n, AddCommGroup (A n)]
    [∀ n, Module K (A n)] (hf : ∀ n, FiniteDimensional K (A n)) (N : ℤ)
    (hs : ∀ n, (n < 0 ∨ N < n) → Subsingleton (A n)) :
    FiniteDimensional K (DirectSum ℤ A) := by
  classical
  let S : Finset ℤ := Finset.Icc 0 N
  have hall : ∀ x : DirectSum ℤ A, x ∈ ⨆ n ∈ S, LinearMap.range (DirectSum.lof K ℤ A n) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact Submodule.zero_mem _
    | of i a =>
      by_cases hi : i ∈ S
      · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi ⟨a, rfl⟩)
      · have hout : i < 0 ∨ N < i := by
          simp only [S, Finset.mem_Icc, not_and_or, not_le] at hi
          exact hi
        haveI := hs i hout
        rw [Subsingleton.elim a 0, map_zero]
        exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  have htop : (⨆ n ∈ S, LinearMap.range (DirectSum.lof K ℤ A n)) = ⊤ :=
    eq_top_iff.2 (fun x _ => hall x)
  refine Module.finite_def.2 ?_
  rw [← htop]
  refine Submodule.fg_biSup S _ (fun n _ => ?_)
  rw [LinearMap.range_eq_map]
  exact (Module.finite_def.1 (hf n)).map _

theorem UpperTheory.Gal.Int.Geo.htotFin_of :
    DegFin → HtotFin := by
  intro h l _ k _ _ hl X p hp hproj
  obtain ⟨hf, N, hN⟩ := h l k hl p hp hproj
  exact finOfDeg hf N hN
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PCompSum
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.compSum_of :
    CompSum := by
  intro k _ X p hs hpr
  haveI := hs
  haveI := hpr
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : GlobalTheory.IsNormalScheme X := LateralTheory.EtaleTrace.LFinCut.normal_of_smooth p
  haveI : CompactSpace X :=
    ⟨by simpa using QuasiCompact.isCompact_preimage (f := p) Set.univ isOpen_univ isCompact_univ⟩
  haveI : IsNoetherian X := {}
  haveI : Finite (irreducibleComponents X) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  let e := Finite.equivFin (irreducibleComponents X)
  have hopen : ∀ Z : irreducibleComponents X, IsOpen (Z : Set X) :=
    fun Z => (GlobalTheory.IsNormalScheme.component Z).isOpen
  refine ⟨Nat.card (irreducibleComponents X), fun s => (GlobalTheory.IsNormalScheme.component (e.symm s) : Scheme),
    fun s => (GlobalTheory.IsNormalScheme.component (e.symm s)).ι, ⟨fun s => inferInstance, ?_, ?_⟩, ?_⟩
  · intro x
    refine ⟨e ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
    rw [Scheme.Opens.range_ι, Equiv.symm_apply_apply]
    exact mem_irreducibleComponent
  · intro s s' hss'
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    have hne : e.symm s ≠ e.symm s' := fun h => hss' (e.symm.injective h)
    show Disjoint ((e.symm s : Set X)) ((e.symm s' : Set X))
    rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hn
    apply hne
    have h12 : ((e.symm s : Set X)) ⊆ (e.symm s' : Set X) :=
      (subset_closure_inter_of_isPreirreducible_of_isOpen (e.symm s).2.1.isPreirreducible
        (hopen (e.symm s')) hn).trans
        (closure_minimal Set.inter_subset_right (isClosed_of_mem_irreducibleComponents _ (e.symm s').2))
    exact Subtype.ext (le_antisymm h12 ((e.symm s).2.2 (e.symm s').2.1 h12))
  · intro s
    haveI : IsReduced X := by
      haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
        obtain ⟨hd, -⟩ := ‹GlobalTheory.IsNormalScheme X›
        haveI := hd x
        infer_instance
      exact isReduced_of_isReduced_stalk X
    haveI : IrreducibleSpace ((GlobalTheory.IsNormalScheme.component (e.symm s) : X.Opens) : Set X) :=
      Subtype.irreducibleSpace (e.symm s).2.1
    exact isIntegral_of_irreducibleSpace_of_isReduced _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RepAsm
noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N

namespace UpperTheory.Gal.Int.Geo

theorem repEx_of (h1 : GrEx) (h2 : ContGL) (h3 : MatEx) (h4 : MatConj) (h5 : PieceStab) (h6 : HtotFin) (h7 : ExtCont)
    (h8 : TotCont) (h9 : KunnethLefschetz.ProjBC) : RepEx := by
  intro E Ω _ _ _ _ _ l _ H θ hnice
  obtain ⟨hsm, hproj, hfet⟩ := hnice
  have hlE : (l : E) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime l).ne_zero
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hlΩ : (l : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime l).ne_zero
  haveI : Smooth H.q := hsm
  have hsm' : Smooth (pullback.snd H.q (Spec.map (CommRingCat.ofHom (algebraMap E Ω)))) := inferInstance
  have hproj' := h9.1 E Ω (algebraMap E Ω) H.q hproj
  haveI hfin : FiniteDimensional ℚ_[l] (Htot l (sch.obj (H.geomZ Ω))) := h6 l Ω hlΩ _ hsm' hproj'
  let U := piece l H Ω (Qbar l) θ
  let a : Gal(Ω/E) → _ := fun σ => galV l H Ω (Qbar l) σ
  have ha1 : a 1 = LinearMap.id := by
    simp only [a, galV, GlobalTheory.GalV.galTot_one, LinearMap.baseChange_id]
  have hamul : ∀ g h, a (g * h) = a g ∘ₗ a h := by
    intro g h
    simp only [a, galV, GlobalTheory.GalV.galTot_mul, LinearMap.baseChange_comp]
  have hU : ∀ g, ∀ x ∈ U, a g x ∈ U := fun g x hx => h5 l E hlE H hfet Ω (Qbar l) θ g x hx
  let b := Module.finBasis (Qbar l) U
  obtain ⟨ρ₀, hmat, hμ⟩ := h3 (Gal(Ω/E)) (Qbar l) _ a ha1 hamul U hU _ b
  have hM : IsMat l H Ω (Qbar l) θ ρ₀ := ⟨b, hmat⟩
  obtain ⟨P, ρ, hgr, hss⟩ := h1 (Gal(Ω/E)) (Qbar l) _ ρ₀
  have hM' := h4 l E H Ω (Qbar l) θ _ ρ₀ P hM
  have hT := h8 l E Ω hlE H.q (h9.2 E H.q hproj)
  have hcont0 : ∀ i j, Continuous fun g => (ρ₀ g).val i j := by
    intro i j
    obtain ⟨μ, hμij⟩ := hμ i j
    have hE := h7 (Gal(Ω/E)) ℚ_[l] (Qbar l) (continuous_algebraMap ℚ_[l] (Qbar l)) _
      (galTot l Ω H.q) hT (b j : _) μ
    refine hE.congr fun g => ?_
    rw [hμij g]
    rfl
  refine ⟨_, ρ, ?_, hss, cj P ρ₀, hM', hgr⟩
  obtain ⟨c, hc⟩ := hgr
  refine (h2 _ (Qbar l) _ ρ).2 fun i j => ?_
  have hfun : (fun g => (ρ g).val i j) = fun g => if c i = c j then (cj P ρ₀ g).val i j else 0 :=
    funext fun g => (hc g).2 i j
  rw [hfun]
  split_ifs
  · simp only [cj_apply, Units.val_mul, Matrix.mul_apply]
    refine continuous_finsetSum _ fun x _ => ?_
    refine Continuous.mul ?_ continuous_const
    refine continuous_finsetSum _ fun y _ => ?_
    exact continuous_const.mul (hcont0 y x)
  · exact continuous_const

end UpperTheory.Gal.Int.Geo

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PFlagBasis
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem exists_linearIndep_levels_span_eq_of_monotone {k : Type} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    (W : ℕ → Submodule k V) (hW : Monotone W) (h0 : W 0 = ⊥) (n : ℕ) :
    ∃ (s : Set V) (lev : V → ℕ), LinearIndepOn k id s ∧ (∀ x ∈ s, lev x < n) ∧
      ∀ i ≤ n, Submodule.span k {x | x ∈ s ∧ lev x < i} = W i := by
  induction n with
  | zero =>
    refine ⟨∅, fun _ => 0, linearIndepOn_empty k id, by simp, ?_⟩
    intro i hi
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    simp [h0]
  | succ n ih =>
    obtain ⟨s, lev, hs, hlev, hspan⟩ := ih
    have hsW : s ⊆ (W (n + 1) : Set V) := by
      intro x hx
      have hx' : x ∈ W n := by
        rw [← hspan n le_rfl]
        exact Submodule.subset_span ⟨hx, hlev x hx⟩
      exact hW (Nat.le_succ n) hx'
    obtain ⟨b, hbt, hsb, htb, hb⟩ := exists_linearIndepOn_id_extension hs hsW
    classical
    refine ⟨b, fun x => if x ∈ s then lev x else n, hb, ?_, ?_⟩
    · intro x hx
      by_cases h : x ∈ s
      · simp only [h, if_true]
        exact Nat.lt_succ_of_lt (hlev x h)
      · simp [h]
    · intro i hi
      rcases Nat.lt_or_ge i (n + 1) with hi' | hi'
      · have hset : {x | x ∈ b ∧ (if x ∈ s then lev x else n) < i} = {x | x ∈ s ∧ lev x < i} := by
          ext x
          by_cases h : x ∈ s
          · simp [h, hsb h]
          · simp only [Set.mem_setOf_eq, h, if_false, false_and, iff_false]
            rintro ⟨-, h'⟩
            omega
        rw [hset]
        exact hspan i (Nat.lt_succ_iff.mp hi')
      · have hi2 : i = n + 1 := le_antisymm hi hi'
        subst hi2
        have hset : {x | x ∈ b ∧ (if x ∈ s then lev x else n) < n + 1} = b := by
          ext x
          constructor
          · exact fun h => h.1
          · intro hx
            refine ⟨hx, ?_⟩
            by_cases h : x ∈ s
            · simp only [h, if_true]
              exact Nat.lt_succ_of_lt (hlev x h)
            · simp [h]
        rw [hset]
        apply le_antisymm
        · exact Submodule.span_le.mpr hbt
        · intro y hy
          exact htb hy

theorem UpperTheory.Gal.Int.Geo.flagBasis_of :
    FlagBasis := by
  intro k _ d m W hW h0 hm
  obtain ⟨s, lev, hs, hlev, hspan⟩ := exists_linearIndep_levels_span_eq_of_monotone W hW h0 m
  have hall : ∀ i, Submodule.span k {x | x ∈ s ∧ lev x < i} = W i := by
    intro i
    rcases le_or_gt i m with h | h
    · exact hspan i h
    · have e1 : {x | x ∈ s ∧ lev x < i} = {x | x ∈ s ∧ lev x < m} := by
        ext x
        constructor
        · rintro ⟨hx, -⟩
          exact ⟨hx, hlev x hx⟩
        · rintro ⟨hx, h'⟩
          exact ⟨hx, by omega⟩
      have hle := hW h.le
      rw [hm] at hle
      rw [e1, hspan m le_rfl, hm]
      exact (top_le_iff.mp hle).symm
  have hsall : Submodule.span k s = ⊤ := by
    have e1 : {x | x ∈ s ∧ lev x < m} = s := by
      ext x
      exact ⟨fun h => h.1, fun h => ⟨h, hlev x h⟩⟩
    rw [← e1, hspan m le_rfl, hm]
  let b0 : Module.Basis s k (Fin d → k) :=
    Module.Basis.mk (v := ((↑) : s → Fin d → k)) hs (by rw [Subtype.range_coe]; exact hsall.ge)
  let e : s ≃ Fin d := b0.indexEquiv (Pi.basisFun k (Fin d))
  let b : Module.Basis (Fin d) k (Fin d → k) := b0.reindex e
  have hb : ∀ j, b j = (e.symm j : Fin d → k) := by
    intro j
    simp only [b, Module.Basis.reindex_apply]
    exact Module.Basis.mk_apply _ _ _
  let L := b.equivFun.symm
  let P : GL (Fin d) k :=
    ⟨LinearMap.toMatrix' (L : (Fin d → k) →ₗ[k] (Fin d → k)),
      LinearMap.toMatrix' (L.symm : (Fin d → k) →ₗ[k] (Fin d → k)),
      by rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id],
      by rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]⟩
  refine ⟨P, fun j => lev (e.symm j), ?_⟩
  intro i v
  have hPv : (↑P : Matrix (Fin d) (Fin d) k).mulVec v = L v := LinearMap.toMatrix'_mulVec _ v
  rw [hPv, ← hall i]
  have himg : (⇑b '' {j | lev (e.symm j) < i}) = {x | x ∈ s ∧ lev x < i} := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [hb]
      exact ⟨(e.symm j).2, hj⟩
    · rintro ⟨hx, hl⟩
      refine ⟨e ⟨x, hx⟩, ?_, ?_⟩
      · simpa using hl
      · rw [hb]
        simp
  rw [← himg, Module.Basis.mem_span_image]
  have hrep : ⇑(b.repr (L v)) = v := by
    rw [← Module.Basis.equivFun_apply]
    exact b.equivFun.apply_symm_apply v
  constructor
  · intro hv j hj
    change ∀ j, i ≤ lev (e.symm j) → v j = 0 at hv
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hrep] at hj
    show lev (e.symm j) < i
    by_contra hlt
    exact hj (hv j (not_lt.mp hlt))
  · intro hsub
    change ∀ j, i ≤ lev (e.symm j) → v j = 0
    intro j hj
    by_contra hne
    have hmem : j ∈ ((b.repr (L v)).support : Set (Fin d)) := by
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hrep]
      exact hne
    have h2 := hsub hmem
    simp only [Set.mem_setOf_eq] at h2
    omega
end

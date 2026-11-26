module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCentreAnnihilatorCompatibleMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizableSiegelWeilFiniteSet

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndex
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndex
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

variable {K : Type} [Field K] [NumberField K] {m : ℕ}

theorem delta_ne_zero (c : Matrix (Fin m) (Fin m) K) : delta c ≠ 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K))
    (Finset.univ : Finset (Fin m × Fin m)) (fun p => c p.1 p.2)
  have hb0 : (b : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero b.2
  choose r hr using fun (i j : Fin m) => RingHom.mem_rangeS.1 (hb (i, j) (Finset.mem_univ _))
  have hr' : ∀ i j, algebraMap (𝓞 K) K (r i j) = algebraMap (𝓞 K) K (b : 𝓞 K) * c i j := by
    intro i j
    rw [hr i j, Algebra.smul_def]
  let I : Ideal (𝓞 K) := Ideal.span {(b : 𝓞 K)}
  have hI : I ≠ ⊥ := fun h => hb0 (Ideal.span_singleton_eq_bot.1 h)
  haveI : Finite (𝓞 K ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let π : (Fin m → 𝓞 K) →+ (Fin m → 𝓞 K ⧸ I) :=
    AddMonoidHom.pi (fun i => (Ideal.Quotient.mk I).toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun _ : Fin m => 𝓞 K) i))
  have hker : π.ker ≤ Kc c := by
    intro y hy
    have h0 : π y = 0 := AddMonoidHom.mem_ker.1 hy
    have hyI : ∀ j, y j ∈ I := fun j =>
      Ideal.Quotient.eq_zero_iff_mem.1 (congrFun h0 j)
    choose z hz using fun j => Ideal.mem_span_singleton'.1 (hyI j)
    change ∀ i : Fin m, ∃ o : 𝓞 K,
      algebraMap (𝓞 K) K o = c.mulVec (fun j => algebraMap (𝓞 K) K (y j)) i
    intro i
    refine ⟨∑ j, r i j * z j, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_mul, hr' i j, ← hz j, map_mul]
    ring
  have hfin : (π.ker).index ≠ 0 := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_pos.ne'
  exact ne_zero_of_dvd_ne_zero hfin (AddSubgroup.index_dvd_of_le hker)

theorem delta_eq_relIndex (c : Matrix (Fin m) (Fin m) K) :
    delta c = (intVec K m).toAddSubgroup.relIndex (lam c).toAddSubgroup := by
  classical
  let L := (lam c).toAddSubgroup
  let H : AddSubgroup L := (intVec K m).toAddSubgroup.addSubgroupOf L
  let f0 : (Fin m → 𝓞 K) →+ (Fin m → K) :=
    (c.mulVecLin.toAddMonoidHom).comp (AddMonoidHom.pi fun i =>
      (algebraMap (𝓞 K) K).toAddMonoidHom.comp (Pi.evalAddMonoidHom (fun _ : Fin m => 𝓞 K) i))
  have hmap : ∀ y, f0 y ∈ L := by
    intro y
    have : f0 y ∈ lam c := by
      unfold lam
      refine Submodule.mem_sup_right (Submodule.mem_map.2 ⟨fun j => algebraMap (𝓞 K) K (y j),
        fun j => ⟨y j, rfl⟩, rfl⟩)
    exact this
  let ψ : (Fin m → 𝓞 K) →+ L := f0.codRestrict L hmap
  let φ : (Fin m → 𝓞 K) →+ L ⧸ H := (QuotientAddGroup.mk' H).comp ψ
  have hker : Kc c = φ.ker := by
    ext y
    rw [AddMonoidHom.mem_ker]
    change _ ↔ (QuotientAddGroup.mk (ψ y) : L ⧸ H) = 0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    rfl
  have hsurj : Function.Surjective φ := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨x, hx⟩ := x
      have hx' : x ∈ lam c := hx
      unfold lam at hx'
      obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
      choose y hy using hv
      refine ⟨y, ?_⟩
      have hyv : (fun j => algebraMap (𝓞 K) K (y j)) = v := funext hy
      change (QuotientAddGroup.mk (ψ y) : L ⧸ H) = QuotientAddGroup.mk _
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      have key : ((-(ψ y) + ⟨_, hx⟩ : L) : Fin m → K) = a := by
        rw [AddSubgroup.coe_add, AddSubgroup.coe_neg]
        change -(c.mulVec (fun j => algebraMap (𝓞 K) K (y j))) + (a + c.mulVec v) = a
        rw [hyv]
        abel
      rw [key]
      exact ha
  show (Kc c).index = H.index
  rw [hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top]
  rfl

theorem delta_index : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ)
    (c : Matrix (Fin m) (Fin m) K),
    delta c ≠ 0 ∧ delta c = (intVec K m).toAddSubgroup.relIndex (lam c).toAddSubgroup := by
  intro K _ _ m c
  exact ⟨delta_ne_zero c, delta_eq_relIndex c⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndexStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_eq_lattice_index : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (c : Matrix (Fin m) (Fin m) K), delta c ≠ 0 ∧ delta c = (intVec K m).toAddSubgroup.relIndex (lam c).toAddSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_index | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_index | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_index <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofiniteOfCapelliMonic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AutomorphicFormsFiniteGLOfGenFin
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.HCFin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem mul_mem_span_zalg_mul {J : Set (Module.End ℂ (Sm E a))} {x : Module.End ℂ (Sm E a)} (hx : x ∈ Zalg E a)
    {s : Module.End ℂ (Sm E a)} (hs : s ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E a, ∃ j ∈ J, y = x * j}) :
    x * s ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E a, ∃ j ∈ J, y = x * j} := by
  induction hs using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x', hx', j, hj, rfl⟩ := hy
    exact Submodule.subset_span ⟨x * x', Subalgebra.mul_mem _ hx hx', j, hj, (mul_assoc _ _ _).symm⟩
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy

end GlobalTheory.CompanionTheory.HCFin
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofiniteOfCapelliMonic
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Polynomial

namespace GlobalTheory.CompanionTheory.CTFin.MonicCofin

theorem exists_finiteDimensional_sub_mem {C : Type*} [CommRing C] [Algebra ℂ C] (I : Ideal C) {s : Set C}
    (hs : s.Finite) (hgen : Algebra.adjoin ℂ s = ⊤) (hq : ∀ x ∈ s, ∃ q : ℂ[X], q.Monic ∧ aeval x q ∈ I) :
    ∃ V : Submodule ℂ C, FiniteDimensional ℂ V ∧ ∀ z : C, ∃ v ∈ V, z - v ∈ I := by
  let π : C →ₐ[ℂ] C ⧸ I := Ideal.Quotient.mkₐ ℂ I
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective ℂ I
  have hint : ∀ y ∈ π '' s, IsIntegral ℂ y := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨q, hm, hqI⟩ := hq x hx
    refine ⟨q, hm, ?_⟩
    rw [← aeval_def, aeval_algHom_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hqI
  have htop : Algebra.adjoin ℂ (π '' s) = ⊤ := by
    rw [← AlgHom.map_adjoin, hgen, Algebra.map_top, AlgHom.range_eq_top]
    exact hπ
  have hfg := fg_adjoin_of_finite (hs.image π) hint
  rw [htop, Algebra.top_toSubmodule] at hfg
  obtain ⟨t, ht⟩ := hfg
  refine ⟨Submodule.span ℂ (Function.surjInv hπ '' (t : Set (C ⧸ I))),
    FiniteDimensional.span_of_finite ℂ (t.finite_toSet.image _), fun z => ?_⟩
  have hmap : (Submodule.span ℂ (Function.surjInv hπ '' (t : Set (C ⧸ I)))).map π.toLinearMap = ⊤ := by
    rw [Submodule.map_span, ← Set.image_comp, ← ht]
    congr 1
    convert Set.image_id _
    funext y
    exact Function.surjInv_eq hπ y
  have hz : π z ∈ (Submodule.span ℂ (Function.surjInv hπ '' (t : Set (C ⧸ I)))).map π.toLinearMap := by
    rw [hmap]; exact Submodule.mem_top
  obtain ⟨v, hv, hvz⟩ := hz
  refine ⟨v, hv, ?_⟩
  rw [← Ideal.Quotient.eq]
  exact hvz.symm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem cap_mem_span_coeffs (τ : E →+* ℂ) (u : ℂ) :
    cap (a := n) τ u ∈ Submodule.span ℂ
      ((GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly (Eop (a := n) τ)).coeffs : Set (Module.End ℂ (Sm E n))) := by
  rw [cap, ← GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_qdetPoly, GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_apply, eval₂_eq_sum,
    Polynomial.sum]
  refine Submodule.sum_mem _ fun k hk => ?_
  rw [RingHom.id_apply, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (coeff_mem_coeffs (by simpa using hk)))

theorem exists_finite_subset_span_cap :
    ∃ b : Set (Module.End ℂ (Sm E n)), b.Finite ∧ b ⊆ {z | ∃ τ u, z = cap (a := n) τ u} ∧
      Submodule.span ℂ b = Submodule.span ℂ {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = cap (a := n) τ u} := by
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent ℂ {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = cap (a := n) τ u}
  have hF : (⋃ τ : E →+* ℂ, ((GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly (Eop (a := n) τ)).coeffs :
      Set (Module.End ℂ (Sm E n)))).Finite := Set.finite_iUnion fun τ => Finset.finite_toSet _
  haveI := FiniteDimensional.span_of_finite ℂ hF
  have hle : Submodule.span ℂ {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = cap (a := n) τ u} ≤ Submodule.span ℂ
      (⋃ τ : E →+* ℂ, ((GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly (Eop (a := n) τ)).coeffs :
      Set (Module.End ℂ (Sm E n)))) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨τ, u, rfl⟩
    exact Submodule.span_mono (Set.subset_iUnion (fun τ : E →+* ℂ =>
      ((GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly (Eop (a := n) τ)).coeffs : Set (Module.End ℂ (Sm E n)))) τ)
      (cap_mem_span_coeffs τ u)
  haveI := Submodule.finiteDimensional_of_le hle
  have hfin : b.Finite := by
    have hli' : LinearIndependent ℂ (fun x : b => (⟨x.1, hspan ▸ Submodule.subset_span x.2⟩ :
        Submodule.span ℂ {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = cap (a := n) τ u})) :=
      LinearIndependent.of_comp (Submodule.subtype _) hli
    have := hli'.finite
    exact Set.toFinite b
  exact ⟨b, hfin, hb, hspan⟩

theorem cofin_of_algHom {C : Type} [CommRing C] [Algebra ℂ C] (ι : C →ₐ[ℂ] Module.End ℂ (Sm E n))
    (hι : Function.Injective ι) (hr : ι.range = Zalg E n) (J : Set (Module.End ℂ (Sm E n))) (hJ : J ⊆ Zalg E n)
    (hq : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ q : Polynomial ℂ, q.Monic ∧ Polynomial.aeval (cap (a := n) τ u) q ∈ J) :
    Cofin J := by
  have hZ : ∀ c : C, ι c ∈ Zalg E n := fun c => hr ▸ AlgHom.mem_range_self ι c
  have hZ' : ∀ z ∈ Zalg E n, ∃ c : C, ι c = z := fun z hz => by
    rw [← hr] at hz
    exact hz
  obtain ⟨b, hbfin, hbT, hspan⟩ := exists_finite_subset_span_cap (E := E) (n := n)
  have hbZ : b ⊆ Zalg E n := fun x hx => Algebra.subset_adjoin (hbT hx)
  let s : Set C := ι ⁻¹' b
  have hs : s.Finite := hbfin.preimage hι.injOn
  have himg : ι '' s = b := Set.image_preimage_eq_of_subset fun x hx => hZ' x (hbZ hx)
  have hgen : Algebra.adjoin ℂ s = ⊤ := by
    refine Subalgebra.map_injective hι ?_
    rw [AlgHom.map_adjoin, himg, Algebra.map_top, hr]
    refine le_antisymm (Algebra.adjoin_le hbZ) (Algebra.adjoin_le ?_)
    intro x hx
    have h1 : x ∈ Submodule.span ℂ b := hspan ▸ Submodule.subset_span hx
    exact (Submodule.span_le.2 Algebra.subset_adjoin :
      Submodule.span ℂ b ≤ Subalgebra.toSubmodule (Algebra.adjoin ℂ b)) h1
  let I : Ideal C := Ideal.span (ι ⁻¹' J)
  have hI : ∀ w ∈ I, ι w ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E n, ∃ j ∈ J, y = x * j} := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact Submodule.subset_span ⟨1, Subalgebra.one_mem _, ι w, hw, (one_mul _).symm⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [smul_eq_mul, map_mul]
      exact GlobalTheory.CompanionTheory.HCFin.mul_mem_span_zalg_mul (hZ a) hx
  have hrel : ∀ x ∈ s, ∃ q : ℂ[X], q.Monic ∧ aeval x q ∈ I := by
    intro x hx
    obtain ⟨τ, u, hτ⟩ := hbT hx
    obtain ⟨q, hm, hqJ⟩ := hq τ u
    refine ⟨q, hm, Ideal.subset_span ?_⟩
    change ι (aeval x q) ∈ J
    rw [← aeval_algHom_apply, hτ]
    exact hqJ
  obtain ⟨V, hV, hz⟩ := exists_finiteDimensional_sub_mem I hs hgen hrel
  refine ⟨hJ, V.map ι.toLinearMap, inferInstance, fun z hzZ => ?_⟩
  obtain ⟨c, rfl⟩ := hZ' z hzZ
  obtain ⟨v, hv, hvI⟩ := hz c
  refine Submodule.mem_sup.2 ⟨ι v, Submodule.mem_map_of_mem hv, ι (c - v), hI _ hvI, ?_⟩
  rw [map_sub]
  abel

theorem cofin_of_monic (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ)
    (J : Set (Module.End ℂ (Sm E n))) (hJ : J ⊆ Zalg E n)
    (hq : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ q : Polynomial ℂ, q.Monic ∧ Polynomial.aeval (cap (a := n) τ u) q ∈ J) :
    Cofin J := by
  letI : CommRing (Zalg E n) := { (inferInstance : Ring (Zalg E n)) with
    mul_comm := fun x y => Subtype.ext (GlobalTheory.AutGrowth.KilledFin.Zalg_commute x.property y.property).eq }
  exact @cofin_of_algHom E _ _ _ n (Zalg E n) inferInstance (Subalgebra.algebra _)
    (Zalg E n).val Subtype.val_injective (Subalgebra.range_val _) J hJ hq

end GlobalTheory.CompanionTheory.CTFin.MonicCofin

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofiniteOfCapelliMonicStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cofinite_of_capelli_monic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (J : Set (Module.End ℂ (Sm E n))), J ⊆ Zalg E n → (∀ (τ : E →+* ℂ) (u : ℂ), ∃ q : Polynomial ℂ, q.Monic ∧ Polynomial.aeval (cap (a := n) τ u) q ∈ J) → Cofin J := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.MonicCofin.cofin_of_monic | exact GlobalTheory.CompanionTheory.CTFin.MonicCofin.cofin_of_monic | (intros; apply GlobalTheory.CompanionTheory.CTFin.MonicCofin.cofin_of_monic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionSchwartzBruhat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionSchwartzBruhat
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.SchGlue

open GlobalTheory.Published.SiegelOneVector

variable {D : D7}

theorem exists_homeomorph_of_sections {A Y Z : Type} [TopologicalSpace A] [TopologicalSpace Y] [TopologicalSpace Z]
    (p : A → Y) (s : Y → A) (c : Y → Z) (σ : Z → A) (hp : Continuous p) (hs : Continuous s)
    (hc : Continuous fun a => c (p a)) (hσ : Continuous σ) (h1 : ∀ y, p (s y) = y)
    (h2 : ∀ z, c (p (σ z)) = z) (h3 : ∀ y, p (σ (c y)) = y) :
    ∃ P : Y ≃ₜ Z, ∀ y, P y = c y := by
  have hcc : Continuous c := by
    have : c = (fun a => c (p a)) ∘ s := funext fun y => by simp only [Function.comp, h1]
    rw [this]
    exact hc.comp hs
  exact ⟨{ toFun := c, invFun := fun z => p (σ z), left_inv := h3, right_inv := h2,
           continuous_toFun := hcc, continuous_invFun := hp.comp hσ }, fun _ => rfl⟩


set_option maxHeartbeats 1600000 in
theorem exists_infHomeo {θ : InfFam D} (hθ : IsInfFam θ) :
    ∃ P : (Ainf D.host.F ⊗[D.host.F] D.host.E) ≃ₜ (D.what₂.Tau → ℂ), ∀ y τ, P y τ = θ τ y := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, he, hec, hec'⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hinf : ∀ y, infPart D (e.symm (y, 0)) = y := fun y => by
    have := (he (e.symm (y, 0))).1
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  have hfin : ∀ y, finPart D (e.symm (y, 0)) = 0 := fun y => by
    have := (he (e.symm (y, 0))).2
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  have hci : Continuous (infPart D) := by
    have : (infPart D : AE D → _) = fun z => (e z).1 := funext fun z => ((he z).1).symm
    rw [this]
    exact continuous_fst.comp hec
  have hs : Continuous fun y : Ainf D.host.F ⊗[D.host.F] D.host.E => e.symm (y, 0) :=
    hec'.comp (continuous_id.prodMk continuous_const)
  have hback : ∀ a : AE D, finPart D a = 0 → a = σ fun τ => θ τ (infPart D a) := fun a ha => by
    refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
    · rw [(finPart D).map_sub, ha, hσ.fin, sub_zero]
    · rw [(infPart D).map_sub, (θ τ).map_sub, hσ.comp, sub_self]
  obtain ⟨P, hP⟩ := exists_homeomorph_of_sections (infPart D : AE D → _) (fun y => e.symm (y, 0))
    (fun (y : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : D.what₂.Tau) => θ τ y) σ hci hs
    (continuous_pi fun τ => GlobalTheory.FockCompare.continuous_comp hθ τ) hσ.cont hinf
    (fun z => funext fun τ => hσ.comp z τ)
    (fun y => by
      obtain ⟨a, ha⟩ : ∃ a : AE D, a = e.symm (y, 0) := ⟨_, rfl⟩
      have h1 : infPart D a = y := ha ▸ hinf y
      have h2 : finPart D a = 0 := ha ▸ hfin y
      subst h1
      exact congrArg (infPart D) (hback a h2).symm)
  exact ⟨P, fun y τ => congrFun (hP y) τ⟩

theorem isSchwartzArch_comp {θ : InfFam D} (hθ : IsInfFam θ) {m r : ℕ}
    (f : SchwartzMap (D.what₂.Tau → Fin m → Fin r → ℂ) ℂ) :
    IsSchwartzArch (F := D.host.F) (E := D.host.E) (M := m) (n := r)
      fun Y => f fun τ i j => θ τ (Y j i) := by
  obtain ⟨P, hP⟩ := exists_infHomeo hθ
  let Q : (Fin r → Fin m → Ainf D.host.F ⊗[D.host.F] D.host.E) ≃ₜ (D.what₂.Tau → Fin m → Fin r → ℂ) :=
    { toFun := fun Y τ i j => P (Y j i) τ
      invFun := fun c j i => P.symm fun τ => c τ i j
      left_inv := fun Y => by simp
      right_inv := fun c => by simp
      continuous_toFun := continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply τ).comp (P.continuous.comp ((continuous_apply i).comp (continuous_apply j)))
      continuous_invFun := continuous_pi fun j => continuous_pi fun i => P.symm.continuous.comp
        (continuous_pi fun τ => (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ))) }
  have hQ : ∀ Y τ i j, Q Y τ i j = θ τ (Y j i) := fun Y τ i j => hP _ _
  have hadd : ∀ X Y, Q (X + Y) = Q X + Q Y := fun X Y => by
    funext τ i j
    simp only [hQ, Pi.add_apply, map_add (f := _)]
  let B : (D.what₂.Tau → Fin m → Fin r → ℂ) ≃L[ℝ]
      (Fin (Module.finrank ℝ (D.what₂.Tau → Fin m → Fin r → ℂ)) → ℝ) :=
    (Module.finBasis ℝ (D.what₂.Tau → Fin m → Fin r → ℂ)).equivFun.toContinuousLinearEquiv
  refine ⟨_, (AddEquiv.mk' Q.toEquiv hadd).trans B.toLinearEquiv.toAddEquiv,
    B.continuous.comp Q.continuous, Q.symm.continuous.comp B.symm.continuous,
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ B.symm f, fun Y => ?_⟩
  show _ = f (B.symm (B (Q Y)))
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact congrArg f (funext fun τ => funext fun i => funext fun j => (hQ Y τ i j).symm)

theorem isSB_swap {m r : ℕ} {g : (Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E)) :
    IsSB fun Y : Fin r → Fin m → Af D.host.F ⊗[D.host.F] D.host.E => g fun i j => Y j i := by
  let S : (Fin r → Fin m → Af D.host.F ⊗[D.host.F] D.host.E) ≃ₜ
      (Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E) :=
    { toFun := fun Y i j => Y j i
      invFun := fun Y j i => Y i j
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply i).comp (continuous_apply j)
      continuous_invFun := continuous_pi fun j => continuous_pi fun i =>
        (continuous_apply j).comp (continuous_apply i) }
  exact ⟨hg.1.comp_continuous S.continuous, hg.2.comp_homeomorph S⟩

theorem isSchwartzArch_smul {M n : ℕ} (c : ℂ) {Φ : (Fin n → Fin M → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℂ}
    (h : IsSchwartzArch (F := D.host.F) (E := D.host.E) Φ) :
    IsSchwartzArch (F := D.host.F) (E := D.host.E) fun X => c * Φ X := by
  obtain ⟨N, e, h1, h2, f, hf⟩ := h
  exact ⟨N, e, h1, h2, c • f, fun X => by simp [hf]⟩

theorem sb_zero {M n : ℕ} :
    IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (0 : (Fin n → Fin M → AE D) → ℂ) :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun _ => by simp⟩

theorem sb_add {M n : ℕ} {Φ Ψ : (Fin n → Fin M → AE D) → ℂ}
    (hΦ : IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Φ)
    (hΨ : IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Ψ) :
    IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (Φ + Ψ) := by
  obtain ⟨k, a, b, ha, hb, hs⟩ := hΦ
  obtain ⟨k', a', b', ha', hb', hs'⟩ := hΨ
  refine ⟨k + k', Fin.append a a', Fin.append b b', fun i => ?_, fun i => ?_, fun X => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact ha i
    · rw [Fin.append_right]; exact ha' i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact hb i
    · rw [Fin.append_right]; exact hb' i
  · rw [Fin.sum_univ_add, Pi.add_apply, hs, hs']
    simp only [Fin.append_left, Fin.append_right]

theorem sb_smul {M n : ℕ} (c : ℂ) {Φ : (Fin n → Fin M → AE D) → ℂ}
    (hΦ : IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Φ) :
    IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (c • Φ) := by
  obtain ⟨k, a, b, ha, hb, hs⟩ := hΦ
  refine ⟨k, fun i X => c * a i X, b, fun i => isSchwartzArch_smul c (ha i), hb, fun X => ?_⟩
  rw [Pi.smul_apply, hs, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.CompanionTheory.SiegelND.SchGlue

namespace GlobalTheory.CompanionTheory.SiegelND

open GlobalTheory.CompanionTheory.SiegelND.SchGlue

theorem isSchwartzBruhat_tupOf_of_mem_schwartzA : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m r : ℕ) (φ : Mx D m r → ℂ), φ ∈ schwartzA θ m r →
  GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (fun X : Fin r → Fin m → AE D => φ (tupOf X)) := by
  intro D θ hθ m r φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨1, fun _ Y => f fun τ i j => θ τ (Y j i), fun _ Y => g fun i j => Y j i,
      fun _ => isSchwartzArch_comp hθ f, fun _ => isSB_swap hg, fun X => ?_⟩
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rfl
  | zero => exact sb_zero
  | add a b _ _ ha hb => exact sb_add ha hb
  | smul c a _ ha => exact sb_smul c ha

end GlobalTheory.CompanionTheory.SiegelND
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionSchwartzBruhatStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_function_schwartz_bruhat : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m r : ℕ) (φ : Mx D m r → ℂ), φ ∈ schwartzA θ m r →
  GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (fun X : Fin r → Fin m → AE D => φ (tupOf X)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.isSchwartzBruhat_tupOf_of_mem_schwartzA | exact GlobalTheory.CompanionTheory.SiegelND.isSchwartzBruhat_tupOf_of_mem_schwartzA | (intros; apply GlobalTheory.CompanionTheory.SiegelND.isSchwartzBruhat_tupOf_of_mem_schwartzA <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPrincipalElementNormBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPrincipalElementNormBound
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink

theorem exists_ne_zero_mem_absNorm_le :
    ∀ (E : Type) [Field E] [NumberField E], ∃ C : ℝ, 0 < C ∧ ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ →
      ∃ t ∈ 𝔞, t ≠ 0 ∧ (Ideal.absNorm (Ideal.span {t}) : ℝ) ≤ C * Ideal.absNorm 𝔞 := by
  intro E _ _
  refine ⟨(4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E *
      ((Module.finrank ℚ E).factorial : ℝ) / (Module.finrank ℚ E : ℝ) ^ Module.finrank ℚ E *
      Real.sqrt |(discr E : ℝ)|, ?_, ?_⟩
  · have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
    have hd : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero E)
    have h1 : (0 : ℝ) < (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E :=
      pow_pos (div_pos (by norm_num) Real.pi_pos) _
    have h2 : (0 : ℝ) < ((Module.finrank ℚ E).factorial : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have h3 : (0 : ℝ) < (Module.finrank ℚ E : ℝ) ^ Module.finrank ℚ E :=
      pow_pos (Nat.cast_pos.mpr hn) _
    exact mul_pos (div_pos (mul_pos h1 h2) h3) (Real.sqrt_pos.mpr hd)
  · intro 𝔞 h𝔞
    have hmem : (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
      rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
    obtain ⟨a, ha, ha0, hle⟩ :=
      exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr E (Units.mk0 _ hmem)
    rw [Units.val_mk0] at ha
    obtain ⟨t, ht, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp ha
    refine ⟨t, ht, ?_, ?_⟩
    · rintro rfl
      simp at ha0
    · have key : ((Ideal.absNorm (Ideal.span {t}) : ℚ)) =
          |Algebra.norm ℚ (algebraMap (𝓞 E) E t)| := by
        rw [← FractionalIdeal.coeIdeal_absNorm (K := E), FractionalIdeal.coeIdeal_span_singleton,
          FractionalIdeal.absNorm_span_singleton]
      have key' : (Ideal.absNorm (Ideal.span {t}) : ℝ) =
          ((|Algebra.norm ℚ (algebraMap (𝓞 E) E t)| : ℚ) : ℝ) := by
        rw [← key, Rat.cast_natCast]
      rw [key']
      refine hle.trans (le_of_eq ?_)
      simp only [Units.val_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
      ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPrincipalElementNormBoundStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_principal_element_norm_bound : ∀ (E : Type) [Field E] [NumberField E], ∃ C : ℝ, 0 < C ∧ ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ t ∈ 𝔞, t ≠ 0 ∧ (Ideal.absNorm (Ideal.span {t}) : ℝ) ≤ C * Ideal.absNorm 𝔞 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink.exists_ne_zero_mem_absNorm_le | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink.exists_ne_zero_mem_absNorm_le | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink.exists_ne_zero_mem_absNorm_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeNormCmAbsNorm
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeNormCmAbsNorm
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig

theorem norm_eq_mul_conj_and_absNorm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ t : 𝓞 E, algebraMap F E ((RingOfIntegers.norm F t : 𝓞 F) : F) = (t : E) * σ (t : E) ∧ Ideal.absNorm (Ideal.span {RingOfIntegers.norm F t}) = Ideal.absNorm (Ideal.span {t}) := by
  intro F E _ _ _ _ _ σ hσ t
  classical
  obtain ⟨_, hE, hdeg, hconj⟩ := hσ
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hdeg]; norm_num)
  refine ⟨?_, ?_⟩
  · set σ' : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (AlgHom.bijective σ) with hσ'
    have hne : σ' ≠ 1 := by
      intro h
      have hx : ∀ x, σ x = x := fun x => by
        have := congrArg (fun g : E ≃ₐ[F] E => g x) h
        simpa [hσ'] using this
      obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
      have hwc : w.IsComplex := hE.isComplex w
      rw [InfinitePlace.isComplex_iff] at hwc
      apply hwc
      rw [ComplexEmbedding.isReal_iff]
      ext x
      rw [ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply, ← hconj, hx]
    have hcard_le : Fintype.card (E ≃ₐ[F] E) ≤ 2 := by
      rw [← hdeg]
      exact (Fintype.card_le_of_injective (fun g : E ≃ₐ[F] E => (g : E →ₐ[F] E))
        (fun a b h => AlgEquiv.ext fun x => DFunLike.congr_fun h x)).trans AlgHom.card_le
    have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, σ'} := by
      symm
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_univ, Finset.card_pair hne.symm]
      exact hcard_le
    haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by
      rw [hdeg, Nat.card_eq_fintype_card]
      apply le_antisymm hcard_le
      rw [← Finset.card_univ, huniv, Finset.card_pair hne.symm])
    change algebraMap F E (Algebra.norm F (t : E)) = _
    rw [Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair hne.symm]
    simp [hσ']
  · rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton]
    congr 1
    apply Int.cast_injective (α := ℚ)
    rw [Algebra.coe_norm_int, Algebra.coe_norm_int]
    change Algebra.norm ℚ (Algebra.norm F (t : E)) = Algebra.norm ℚ (t : E)
    rw [Algebra.norm_norm]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeNormCmAbsNormStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relative_norm_cm_absNorm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ t : 𝓞 E, algebraMap F E ((RingOfIntegers.norm F t : 𝓞 F) : F) = (t : E) * σ (t : E) ∧ Ideal.absNorm (Ideal.span {RingOfIntegers.norm F t}) = Ideal.absNorm (Ideal.span {t}) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig.norm_eq_mul_conj_and_absNorm | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig.norm_eq_mul_conj_and_absNorm | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig.norm_eq_mul_conj_and_absNorm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactElementEigenvaluesUnits
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactElementEigenvaluesUnits
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.DiagBd

theorem valued_eq_one_of_isCompact_closure_zpowers (E : Type) [Field E] [NumberField E] [IsCMField E]
    (w : Pl E) (n : ℕ) (H : Subgroup (GLw n w)) (g : H) (p : GLw n w)
    (s : Fin n → (w.adicCompletion E)ˣ) (hg : g.1 = p * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s * p⁻¹)
    (hc : IsCompact (closure (Subgroup.zpowers g : Set H))) (i : Fin n) :
    Valued.v (s i : w.adicCompletion E) = 1 := by
  set φ : H → w.adicCompletion E :=
    fun x => ((p⁻¹ * x.1 * p : GLw n w) : Matrix (Fin n) (Fin n) _) i i with hφdef
  have hφ : Continuous φ := by
    have h1 : Continuous fun x : H => (p⁻¹ * x.1 * p : GLw n w) :=
      (continuous_const.mul continuous_subtype_val).mul continuous_const
    have h2 : Continuous fun x : H => ((p⁻¹ * x.1 * p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
      Units.continuous_val.comp h1
    exact (continuous_apply i).comp ((continuous_apply i).comp h2)
  have hpow : ∀ m : ℤ, φ (g ^ m) = ((s i ^ m : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    intro m
    have h1 : p⁻¹ * ((g ^ m : H) : GLw n w) * p = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) (s ^ m) := by
      rw [Subgroup.coe_zpow, hg, map_zpow]
      rw [show p * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s * p⁻¹ =
        MulAut.conj p (GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) from rfl, ← map_zpow]
      simp [MulAut.conj_apply, mul_assoc]
    simp only [hφdef, h1, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_eq, Pi.pow_apply]
  obtain ⟨R, hR⟩ := (hc.image hφ).isBounded.exists_norm_le
  have hb : ∀ m : ℤ, ‖((s i ^ m : (w.adicCompletion E)ˣ) : w.adicCompletion E)‖ ≤ R := by
    intro m
    rw [← hpow m]
    exact hR _ ⟨g ^ m, subset_closure (Subgroup.zpow_mem_zpowers g m), rfl⟩
  have hne : (s i : w.adicCompletion E) ≠ 0 := (s i).ne_zero
  have hpos : 0 < ‖(s i : w.adicCompletion E)‖ := norm_pos_iff.mpr hne
  have hnorm : ‖(s i : w.adicCompletion E)‖ = 1 := by
    rcases lt_trichotomy ‖(s i : w.adicCompletion E)‖ 1 with h | h | h
    · exfalso
      have h' : 1 < ‖(s i : w.adicCompletion E)‖⁻¹ := (one_lt_inv₀ hpos).mpr h
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R h'
      have := hb (-(k : ℤ))
      rw [Units.val_zpow_eq_zpow_val, norm_zpow, _root_.zpow_neg, zpow_natCast, ← inv_pow] at this
      linarith
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R h
      have := hb (k : ℤ)
      rw [Units.val_zpow_eq_zpow_val, norm_zpow, zpow_natCast] at this
      linarith
  refine le_antisymm (Valued.toNormedField.norm_le_one_iff.1 hnorm.le) (not_lt.1 fun h => ?_)
  exact absurd (Valued.toNormedField.norm_lt_one_iff.2 h) (by rw [hnorm]; exact lt_irrefl _)

end GlobalTheory.CompanionTheory.DiagBd
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactElementEigenvaluesUnitsStatement
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_element_eigenvalues_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) (H : Subgroup (GLw n w)) (g : H) (p : GLw n w) (s : Fin n → (w.adicCompletion E)ˣ), g.1 = p * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s * p⁻¹ → IsCompact (closure (Subgroup.zpowers g : Set H)) → ∀ i, Valued.v (s i : w.adicCompletion E) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers | exact GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers | (intros; apply GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeQuotientTorsionNonzero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeQuotientTorsionNonzero
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

theorem exists_ne_zero_smul_mem_of_mem_span {K : Type} [Field K] [NumberField K] {m : ℕ}
    (L : Submodule (𝓞 K) (Fin m → K)) {v : Fin m → K}
    (hv : v ∈ Submodule.span K (L : Set (Fin m → K))) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ L := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, mul_smul, mul_comm, mul_smul]
      rw [smul_comm a b x, smul_comm b a y]
    rw [e]
    exact L.add_mem (L.smul_mem _ hax) (L.smul_mem _ hby)
  | smul k x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) k
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hdK : algebraMap (𝓞 K) K d ≠ 0 := by
      simpa using hd0
    refine ⟨d * a, mul_ne_zero hd0 ha, ?_⟩
    have e : (d * a) • ((algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K d) • x) = n • (a • x) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_mul]
      field_simp
    rw [e]
    exact L.smul_mem _ hax

theorem torsionOf_quot_lat_ne_bot : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)), IsLat L →
    ∀ x : (Fin m → K) ⧸ L, Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x ≠ ⊥ := by
  intro K _ _ m L hL x h
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective L x
  obtain ⟨a, ha, hav⟩ := exists_ne_zero_smul_mem_of_mem_span L
    (show v ∈ Submodule.span K (L : Set (Fin m → K)) by rw [hL.2]; trivial)
  have hmem : a ∈ Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) (Submodule.Quotient.mk v) := by
    rw [Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.mk_eq_zero L).2 hav
  rw [h] at hmem
  exact ha ((Submodule.mem_bot _).1 hmem)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeQuotientTorsionNonzeroStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_quotient_torsion_nonzero : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : Submodule (𝓞 K) (Fin m → K)), IsLat L → ∀ x : (Fin m → K) ⧸ L, Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x ≠ ⊥ := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.torsionOf_quot_lat_ne_bot | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.torsionOf_quot_lat_ne_bot | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.torsionOf_quot_lat_ne_bot <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousThetaKernelComponents
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousThetaKernelComponents
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RCellCont

theorem continuity_characters_projection : ∀ {D : D7} {t ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) (b₀ : HermE D ρ) (b : hermA D t), Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => pch ψ b.1 (ip V z.2 z.2)) ∧ Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => yv V b₀ z) ∧ Continuous (fun q : Mx D ρ t × (Mx D V.rank ρ × Mx D V.rank t) => ψ (trA (Matrix.trace (pr b₀ q.1 (yv V b₀ q.2))))) ∧ Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => pch ψ b.1 (qv V b₀ z)) ∧ (∀ T, ‖pch ψ b.1 T‖ = 1) ∧ ∀ u, ‖ψ u‖ = 1 := by
  intro D t ρ ψ hψ V b₀ b
  have hψc : Continuous ψ := hψ.1
  have hψn : ∀ u, ‖ψ u‖ = 1 := hψ.2.1
  have htr : Continuous (trA (D := D)) := by unfold trA; fun_prop
  have hhalf : Continuous (halfTr (D := D)) := by
    unfold halfTr
    exact continuous_const.mul htr
  have hpch : ∀ {n : ℕ} (x : Mx D n n), Continuous (fun T : Mx D n n => pch ψ x T) := by
    intro n x
    unfold pch mm
    exact hψc.comp (hhalf.comp ((continuous_const.matrix_mul continuous_id).matrix_trace))
  have hip : ∀ {a c : ℕ} {X : Type} [TopologicalSpace X] (f : X → Mx D V.rank a) (g : X → Mx D V.rank c),
      Continuous f → Continuous g → Continuous (fun x => ip V (f x) (g x)) := by
    intro a c X _ f g hf hg
    unfold ip mm
    exact (GlobalTheory.MixModel.continuous_adj.comp hf).matrix_mul (continuous_const.matrix_mul hg)
  have hyv : Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => yv V b₀ z) := by
    unfold yv mm
    exact continuous_const.matrix_mul (hip _ _ continuous_fst continuous_snd)
  have hpr : ∀ {p : ℕ} {X : Type} [TopologicalSpace X] (f g : X → Mx D ρ p),
      Continuous f → Continuous g → Continuous (fun x => pr b₀ (f x) (g x)) := by
    intro p X _ f g hf hg
    unfold pr
    exact (GlobalTheory.MixModel.continuous_adj.comp hf).matrix_mul (continuous_const.matrix_mul hg)
  refine ⟨?_, hyv, ?_, ?_, ?_, hψn⟩
  · exact (hpch b.1).comp (hip _ _ continuous_snd continuous_snd)
  · exact hψc.comp (htr.comp (hpr _ _ continuous_fst (hyv.comp continuous_snd)).matrix_trace)
  · have hq : Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => qv V b₀ z) := by
      unfold qv
      set_option synthInstance.maxHeartbeats 200000 in
        exact (hip _ _ continuous_snd continuous_snd).sub (hpr _ _ hyv hyv)
    exact (hpch b.1).comp hq
  · intro T
    unfold pch
    exact hψn _

end GlobalTheory.CompanionTheory.RCellCont

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousThetaKernelComponentsStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_theta_kernel_components : ∀ {D : D7} {t ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) (b₀ : HermE D ρ) (b : hermA D t), Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => pch ψ b.1 (ip V z.2 z.2)) ∧ Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => yv V b₀ z) ∧ Continuous (fun q : Mx D ρ t × (Mx D V.rank ρ × Mx D V.rank t) => ψ (trA (Matrix.trace (pr b₀ q.1 (yv V b₀ q.2))))) ∧ Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => pch ψ b.1 (qv V b₀ z)) ∧ (∀ T, ‖pch ψ b.1 T‖ = 1) ∧ ∀ u, ‖ψ u‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.RCellCont.continuity_characters_projection | exact GlobalTheory.CompanionTheory.RCellCont.continuity_characters_projection | (intros; apply GlobalTheory.CompanionTheory.RCellCont.continuity_characters_projection <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizableSchwartzOrbitalIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizableSchwartzOrbitalIntegral
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem pureN_isSchwartzBruhat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : (∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))), IsSchwartzArch φ → (∀ v, IsCompact (A v) ∧ IsOpen (A v)) → (∀ v, v ∉ S → A v = latV b v) → IsSchwartzBruhat (pureN φ A) := by
  intro F E _ _ _ _ _ σ _ M J _ n _ d b S φ A hφ hA hS
  have hc : IsCompact (boxFN A) := GlobalTheory.CompanionTheory.WhitFree.PureTuple.isCompact_boxF b S A (fun v => (hA v).1) hS
  have hcl : IsClosed (boxFN A) := GlobalTheory.CompanionTheory.WhitFree.PureTuple.isClosed_boxF b A fun v => (hA v).1
  have ho : IsOpen (boxFN A) := GlobalTheory.CompanionTheory.WhitFree.PureTuple.isOpen_boxF b S A (fun v => (hA v).2) hS
  refine isSchwartzBruhat_of_prod hφ (Φf := (boxFN A).indicator fun _ => (1 : ℂ)) ⟨?_, ?_⟩ fun _ => rfl
  · exact (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) ⟨hcl, ho⟩).isLocallyConstant
  · exact HasCompactSupport.intro' hc hcl fun Y hY => Set.indicator_of_notMem hY _

end GlobalTheory.CompanionTheory.SiegelND.Coef
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizableSchwartzOrbitalIntegralStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorizable_schwartz_orbital_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : (∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))), IsSchwartzArch φ → (∀ v, IsCompact (A v) ∧ IsOpen (A v)) → (∀ v, v ∉ S → A v = latV b v) → IsSchwartzBruhat (pureN φ A) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.pureN_isSchwartzBruhat | exact GlobalTheory.CompanionTheory.SiegelND.Coef.pureN_isSchwartzBruhat | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.pureN_isSchwartzBruhat <;> assumption)
end
end

module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioConjOfUnimod

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.IsOpenAddSubgroup
noncomputable section

open ValuativeRel

namespace PI.ProdFormulaE.ROpen

theorem isOpen_addSubgroup {G : Type*} [TopologicalSpace G] [AddCommGroup G] [ContinuousAdd G]
    (H : AddSubgroup G) (U : Set G) (hU : IsOpen U) (h0 : (0 : G) ∈ U) (hUH : U ⊆ H) :
    IsOpen (H : Set G) := by
  exact H.isOpen_of_mem_nhds (Filter.mem_of_superset (hU.mem_nhds h0) hUH)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem isOpen_integer : IsOpen ((𝒪[F] : Subring F) : Set F) :=
  Valuation.isOpen_integer (v := ValuativeRel.valuation F)

theorem isOpen_O (L : Formalism.MainNotions.S.Loc.LocE F E) : IsOpen (L.O : Set E) := by
  classical
  haveI := L.top
  haveI := L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  haveI : ContinuousAdd E := by
    first
      | exact IsModuleTopology.toContinuousAdd F E
      | exact inferInstance
      | (rw [IsModuleTopology.eq_moduleTopology F E]; exact ModuleTopology.continuousAdd F E)
  set b := Module.finBasis F E
  have hint : ∀ i, ∃ d : 𝒪[F], d ≠ 0 ∧ IsIntegral 𝒪[F] (algebraMap 𝒪[F] E d * b i) := by
    intro i
    have halg : IsAlgebraic 𝒪[F] (b i) :=
      (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 (Algebra.IsIntegral.isIntegral (b i)).isAlgebraic
    obtain ⟨d, hd, hdi⟩ := halg.exists_integral_multiple
    exact ⟨d, hd, by simpa [Algebra.smul_def] using hdi⟩
  choose d hd0 hdi using hint
  set D : 𝒪[F] := ∏ i, d i with hD
  have hDint : ∀ i, IsIntegral 𝒪[F] (algebraMap 𝒪[F] E D * b i) := by
    intro i
    rw [hD, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul, mul_assoc]
    exact (isIntegral_algebraMap).mul (hdi i)
  let f : E →ₗ[F] (Fin (Module.finrank F E) → F) := b.equivFun.toLinearMap
  have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f
  let U : Set E := f ⁻¹' Set.pi Set.univ (fun _ => (fun c : F => c * ((D : 𝒪[F]) : F)⁻¹) ⁻¹' (𝒪[F] : Set F))
  have hcont : Continuous (fun c : F => c * ((D : 𝒪[F]) : F)⁻¹) := continuous_id.mul continuous_const
  have hUo : IsOpen U := hf.isOpen_preimage _
    (isOpen_set_pi Set.finite_univ fun _ _ => hcont.isOpen_preimage _ isOpen_integer)
  refine isOpen_addSubgroup L.O.toAddSubgroup U hUo ?_ ?_
  · intro i _
    simp [U, f]
  · intro x hx
    have hx' : ∀ i, b.repr x i * ((D : 𝒪[F]) : F)⁻¹ ∈ 𝒪[F] := fun i => hx i (Set.mem_univ i)
    show x ∈ L.O
    rw [← b.sum_repr x]
    refine Subring.sum_mem _ fun i _ => ?_
    have hD0 : ((D : 𝒪[F]) : F) ≠ 0 := by
      rw [hD]
      push_cast
      exact Finset.prod_ne_zero_iff.2 fun j _ => by exact_mod_cast hd0 j
    have e : b.repr x i • b i = algebraMap 𝒪[F] E ⟨_, hx' i⟩ * (algebraMap 𝒪[F] E D * b i) := by
      rw [← mul_assoc, ← map_mul, Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪[F] F E]
      congr 2
      show b.repr x i = b.repr x i * ((D : 𝒪[F]) : F)⁻¹ * ((D : 𝒪[F]) : F)
      rw [mul_assoc, inv_mul_cancel₀ hD0, mul_one]
    rw [e]
    exact L.O.mul_mem ((L.O_def _).2 isIntegral_algebraMap) ((L.O_def _).2 (hDint i))

theorem isOpen_R [MeasurableSpace E] (M : Formalism.MainNotions.S.Loc.Model F E) : IsOpen (M.R : Set E) := by
  classical
  haveI := M.L.top
  haveI : ContinuousAdd E := by
    first
      | exact IsModuleTopology.toContinuousAdd F E
      | exact inferInstance
  rcases hs : M.split with _ | g
  · have hR : M.R = M.L.O := by
      simp only [Formalism.MainNotions.S.Loc.Model.R, hs]
    rw [hR]
    exact isOpen_O M.L
  · have hq0 : ((g.q : 𝒪[F]) : F) ≠ 0 := by
      intro h
      exact g.q_irr.ne_zero (Subtype.ext h)
    have he : Continuous g.e := IsModuleTopology.continuous_of_linearMap g.e.toLinearMap
    have hV : IsOpen ((fun c : F => c * ((g.q : 𝒪[F]) : F)⁻¹) ⁻¹' (𝒪[F] : Set F)) :=
      (continuous_id.mul continuous_const).isOpen_preimage _ isOpen_integer
    have hU : IsOpen (g.e ⁻¹' (((fun c : F => c * ((g.q : 𝒪[F]) : F)⁻¹) ⁻¹' (𝒪[F] : Set F)) ×ˢ
        ((fun c : F => c * ((g.q : 𝒪[F]) : F)⁻¹) ⁻¹' (𝒪[F] : Set F)))) :=
      he.isOpen_preimage _ (hV.prod hV)
    refine isOpen_addSubgroup M.R.toAddSubgroup _ hU ?_ ?_
    · simp
    · intro x hx
      obtain ⟨h1, h2⟩ := hx
      simp only [Set.mem_preimage] at h1 h2
      have m1 : (g.e x).1 ∈ 𝒪[F] := by
        have : (g.e x).1 = (g.e x).1 * ((g.q : 𝒪[F]) : F)⁻¹ * ((g.q : 𝒪[F]) : F) := by
          rw [mul_assoc, inv_mul_cancel₀ hq0, mul_one]
        rw [this]
        exact Subring.mul_mem _ h1 (g.q).2
      have m2 : (g.e x).2 ∈ 𝒪[F] := by
        have : (g.e x).2 = (g.e x).2 * ((g.q : 𝒪[F]) : F)⁻¹ * ((g.q : 𝒪[F]) : F) := by
          rw [mul_assoc, inv_mul_cancel₀ hq0, mul_one]
        rw [this]
        exact Subring.mul_mem _ h2 (g.q).2
      have z1 : (⟨(g.e x).1, m1⟩ : 𝒪[F]) ∈ Ideal.span {g.q} := by
        rw [Ideal.mem_span_singleton']
        exact ⟨⟨_, h1⟩, Subtype.ext (by
          show (g.e x).1 * ((g.q : 𝒪[F]) : F)⁻¹ * ((g.q : 𝒪[F]) : F) = (g.e x).1
          rw [mul_assoc, inv_mul_cancel₀ hq0, mul_one])⟩
      have z2 : (⟨(g.e x).2, m2⟩ : 𝒪[F]) ∈ Ideal.span {g.q} := by
        rw [Ideal.mem_span_singleton']
        exact ⟨⟨_, h2⟩, Subtype.ext (by
          show (g.e x).2 * ((g.q : 𝒪[F]) : F)⁻¹ * ((g.q : 𝒪[F]) : F) = (g.e x).2
          rw [mul_assoc, inv_mul_cancel₀ hq0, mul_one])⟩
      show x ∈ (M.R : Set E)
      simp only [Formalism.MainNotions.S.Loc.Model.R, hs]
      rw [SetLike.mem_coe, Subring.mem_comap, Subring.mem_map]
      refine ⟨(⟨(g.e x).1, m1⟩, ⟨(g.e x).2, m2⟩), ?_, rfl⟩
      show _ = _
      show Ideal.Quotient.mk (Ideal.span {g.q}) (⟨(g.e x).1, m1⟩ : 𝒪[F]) =
        Ideal.Quotient.mk (Ideal.span {g.q}) (⟨(g.e x).2, m2⟩ : 𝒪[F])
      rw [(Ideal.Quotient.eq_zero_iff_mem).2 z1, (Ideal.Quotient.eq_zero_iff_mem).2 z2]

end PI.ProdFormulaE.ROpen

end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CommonDenom
noncomputable section

open ValuativeRel Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.ProdEP2Uni

section LocTop

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem topE (M : Loc.Model F E) : IsTopologicalRing E := by
  haveI := M.L.top
  haveI := M.L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  first
    | exact IsModuleTopology.isTopologicalRing F E
    | exact IsModuleTopology.topologicalRing F E

theorem t2E (M : Loc.Model F E) : T2Space E := by
  haveI := M.L.top
  haveI := M.L.free
  haveI : T2Space F := MainNotions.LocalModelPeriodLattices.nonarchimedean_local_field_t2 inferInstance
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  let b := Module.Free.chooseBasis F E
  have hc : Continuous (b.equivFun : E → (Module.Free.ChooseBasisIndex F E → F)) :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  exact T2Space.of_injective_continuous b.equivFun.injective hc

theorem int_mem {x : F} (h : IsIntegral 𝒪[F] x) : x ∈ 𝒪[F] := by
  first
    | exact (Valuation.integer.integers (ValuativeRel.valuation F)).mem_of_integral h
    | (obtain ⟨y, hy⟩ := (Valuation.integer.integers (ValuativeRel.valuation F)).mem_of_integral h
       rw [← hy]
       exact y.2)

theorem alg_int (x : 𝒪[F]) : algebraMap F E (x : F) = algebraMap 𝒪[F] E x := by
  first
    | rfl
    | exact (IsScalarTower.algebraMap_apply 𝒪[F] F E x).symm

private theorem R_eq_O_of_split_eq_none (M : Loc.Model F E) (hg : M.split = none) : M.R = M.L.O := by
  simp only [Loc.Model.R, hg]

private theorem mem_R_iff_of_split_eq_some (M : Loc.Model F E) (g : Loc.SplitG M.L) (hg : M.split = some g) (z : E) :
    z ∈ M.R ↔ ∃ a b : 𝒪[F], g.e z = ((a : F), (b : F)) ∧
      Ideal.Quotient.mk (Ideal.span {g.q}) a = Ideal.Quotient.mk (Ideal.span {g.q}) b := by
  simp only [Loc.Model.R, hg, Subring.mem_comap, Subring.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hab, he⟩
    exact ⟨a, b, he.symm, RingHom.mem_eqLocus.mp hab⟩
  · rintro ⟨a, b, he, hab⟩
    exact ⟨(a, b), RingHom.mem_eqLocus.mpr hab, he.symm⟩

theorem alg_mem_R (M : Loc.Model F E) (a : 𝒪[F]) : algebraMap F E (a : F) ∈ M.R := by
  cases hg : M.split with
  | none =>
    rw [R_eq_O_of_split_eq_none M hg, M.L.O_def, alg_int]
    exact isIntegral_algebraMap
  | some g =>
    rw [mem_R_iff_of_split_eq_some M g hg]
    refine ⟨a, a, ?_, rfl⟩
    rw [AlgEquiv.commutes]
    first
      | rfl
      | simp

private theorem splitG_e_mem_integers_of_mem_O (L : Loc.LocE F E) (g : Loc.SplitG L) {z : E} (hz : z ∈ L.O) :
    (g.e z).1 ∈ 𝒪[F] ∧ (g.e z).2 ∈ 𝒪[F] := by
  have h1 : IsIntegral 𝒪[F] (g.e z) := ((L.O_def z).mp hz).map (g.e.toAlgHom.restrictScalars 𝒪[F])
  exact ⟨int_mem (h1.map ((AlgHom.fst F F F).restrictScalars 𝒪[F])),
    int_mem (h1.map ((AlgHom.snd F F F).restrictScalars 𝒪[F]))⟩

private theorem mem_O_of_mem_R (M : Loc.Model F E) {z : E} (hz : z ∈ M.R) : z ∈ M.L.O := by
  cases hg : M.split with
  | none =>
    rwa [R_eq_O_of_split_eq_none M hg] at hz
  | some g =>
    obtain ⟨a, b, he, -⟩ := (mem_R_iff_of_split_eq_some M g hg z).mp hz
    rw [M.L.O_def]
    have ha : IsIntegral 𝒪[F] (a : F) := (isIntegral_algebraMap : IsIntegral 𝒪[F] (algebraMap 𝒪[F] F a))
    have hb : IsIntegral 𝒪[F] (b : F) := (isIntegral_algebraMap : IsIntegral 𝒪[F] (algebraMap 𝒪[F] F b))
    have h1 : IsIntegral 𝒪[F] (((a : F), (b : F)) : F × F) := IsIntegral.pair ha hb
    have h2 := h1.map (g.e.symm.toAlgHom.restrictScalars 𝒪[F])
    rw [← he] at h2
    have e : (g.e.symm.toAlgHom.restrictScalars 𝒪[F]) (g.e z) = z := g.e.symm_apply_apply z
    rwa [e] at h2

theorem R_compact [CharZero F] (M : Loc.Model F E) : IsCompact (M.R : Set E) := by
  haveI := topE M
  have hO := (MainNotions.LocalModelPeriodLattices.O_top M.L).2.1
  have hRo : IsOpen (M.R : Set E) := PI.ProdFormulaE.ROpen.isOpen_R M
  have hRc : IsClosed (M.R : Set E) := M.R.toAddSubgroup.isClosed_of_isOpen hRo
  exact hO.of_isClosed_subset hRc (fun z hz => mem_O_of_mem_R M hz)

theorem R_denom (M : Loc.Model F E) (y : E) : ∃ a : 𝒪[F], a ≠ 0 ∧ algebraMap F E (a : F) * y ∈ M.R := by
  haveI := M.L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  haveI : Nontrivial E := by
    first
      | exact Module.nontrivial_of_finrank_pos (R := F) (by rw [M.L.rank]; norm_num)
      | exact Module.nontrivial_of_finrank_eq_succ M.L.rank
  haveI : IsFractionRing 𝒪[F] F := ValuationRing.instIsFractionRingInteger (ValuativeRel.valuation F)
  have hinj : ∀ x : 𝒪[F], algebraMap 𝒪[F] E x = 0 → x = 0 := by
    intro x hx
    rw [← alg_int] at hx
    exact Subtype.ext ((map_eq_zero_iff _ (algebraMap F E).injective).mp hx)
  have halg : IsAlgebraic 𝒪[F] y := by
    have hF : IsAlgebraic F y := (Algebra.IsIntegral.isIntegral (R := F) y).isAlgebraic
    exact (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).mpr hF
  have hex : ∃ s : 𝒪[F], s ≠ 0 ∧ IsIntegral 𝒪[F] (algebraMap 𝒪[F] E s * y) := by
    first
      | (obtain ⟨z, s, hs, hz⟩ := exists_integral_multiple halg hinj
         exact ⟨s, hs, by rw [mul_comm, hz]; exact z.2⟩)
      | (obtain ⟨s, hs, hi⟩ := halg.exists_integral_multiple
         exact ⟨s, hs, by rwa [Algebra.smul_def] at hi⟩)
  obtain ⟨s, hs, hsi⟩ := hex
  have hsy : algebraMap F E (s : F) * y ∈ M.L.O := by
    rw [M.L.O_def, alg_int]
    exact hsi
  cases hg : M.split with
  | none =>
    exact ⟨s, hs, by rw [R_eq_O_of_split_eq_none M hg]; exact hsy⟩
  | some g =>
    refine ⟨g.q * s, mul_ne_zero g.q_irr.ne_zero hs, ?_⟩
    obtain ⟨h1, h2⟩ := splitG_e_mem_integers_of_mem_O M.L g hsy
    rw [mem_R_iff_of_split_eq_some M g hg]
    refine ⟨g.q * ⟨_, h1⟩, g.q * ⟨_, h2⟩, ?_, ?_⟩
    · have e : algebraMap F E ((g.q * s : 𝒪[F]) : F) * y =
          algebraMap F E (g.q : F) * (algebraMap F E (s : F) * y) := by
        rw [MulMemClass.coe_mul, map_mul, mul_assoc]
      rw [e, map_mul, AlgEquiv.commutes]
      ext <;> simp
    · have hq : ∀ t : 𝒪[F], Ideal.Quotient.mk (Ideal.span {g.q}) (g.q * t) = 0 := fun t =>
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right t _ (Ideal.mem_span_singleton_self _))
      rw [hq, hq]

theorem common_denom (M : Loc.Model F E) {ι : Type} [Fintype ι] (y : ι → E) :
    ∃ a : 𝒪[F], a ≠ 0 ∧ ∀ k, algebraMap F E (a : F) * y k ∈ M.R := by
  classical
  choose d hd0 hd using fun k => R_denom M (y k)
  refine ⟨∏ k, d k, Finset.prod_ne_zero_iff.mpr fun k _ => hd0 k, fun k => ?_⟩
  have hp : (∏ j, d j) = (∏ j ∈ Finset.univ.erase k, d j) * d k :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ k)).symm
  rw [hp]
  have e : algebraMap F E (((∏ j ∈ Finset.univ.erase k, d j) * d k : 𝒪[F]) : F) * y k =
      algebraMap F E ((∏ j ∈ Finset.univ.erase k, d j : 𝒪[F]) : F) * (algebraMap F E (d k : F) * y k) := by
    rw [MulMemClass.coe_mul, map_mul, mul_assoc]
  rw [e]
  exact M.R.mul_mem (alg_mem_R M _) (hd k)

end LocTop

end Formalism.L2.SG.Pf.ProdEP2Uni
end
end

noncomputable section

open scoped Classical
open NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape Formalism.L2.SG.Pf.ProdE
  Formalism.L2.SG.Pf.ProdEP2Core Formalism.L2.SG.Pf.IndexCocycleOrbits Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.ProdEP2Uni

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unimod_of_norm {G : Type} [Group G] (A B' : Subgroup G) (s : G) (hAB' : A ≤ B') (hB : cj s B' = B')
    (hf : A.relIndex B' ≠ 0) : IdxRatio A (cj s A) = 1 := by
  have hA'le : cj s A ≤ B' := hB ▸ cj_le hAB'
  have hA'idx : (cj s A).relIndex B' = A.relIndex B' := by rw [← relIndex_cj s A B', hB]
  have e2 := idxCocycle G A (cj s A) B' hA'le (by rw [hA'idx]; exact hf)
  have e3 := idxCocycle G A A B' hAB' hf
  rw [idxRatio_self] at e3
  rw [e2, hA'idx, ← e3]

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) {p : PlF D}

section Mat

def dg (x : (D.s.atP p).Ep) : MP p := Matrix.diagonal fun i => x ^ (i : ℕ)

theorem dg_mul_dg (x y : (D.s.atP p).Ep) : (dg x : MP p) * dg y = dg (x * y) := by
  simp only [dg, Matrix.diagonal_mul_diagonal, mul_pow]

theorem dg_one : (dg 1 : MP p) = 1 := by
  simp [dg]

theorem dg_entry (x y : (D.s.atP p).Ep) (m : MP p) (i j : Fin (D.R.rS + 1)) :
    (dg x * m * dg y) i j = x ^ (i : ℕ) * m i j * y ^ (j : ℕ) := by
  simp only [dg, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem pow_inv_pow {a : (D.s.atP p).Fp} (ha : a ≠ 0) (k : ℕ) :
    (algebraMap _ (D.s.atP p).Ep a⁻¹) ^ k * (algebraMap _ (D.s.atP p).Ep a) ^ k = 1 := by
  rw [← mul_pow, ← map_mul, inv_mul_cancel₀ ha, map_one, one_pow]

theorem pow_scale {a : (D.s.atP p).Fp} (ha : a ≠ 0) {i j : ℕ} (hij : j ≤ i) :
    (algebraMap _ (D.s.atP p).Ep a) ^ i * (algebraMap _ (D.s.atP p).Ep a⁻¹) ^ j =
      (algebraMap _ (D.s.atP p).Ep a) ^ (i - j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [Nat.add_sub_cancel_left, pow_add, mul_comm ((algebraMap _ (D.s.atP p).Ep a) ^ j), mul_assoc,
    mul_comm ((algebraMap _ (D.s.atP p).Ep a) ^ j), pow_inv_pow ha, mul_one]

def tU (a : (D.s.atP p).Fp) (ha : a ≠ 0) : GLp p :=
  ⟨dg (algebraMap _ _ a), dg (algebraMap _ _ a⁻¹),
    by rw [dg_mul_dg, ← map_mul, mul_inv_cancel₀ ha, map_one, dg_one],
    by rw [dg_mul_dg, ← map_mul, inv_mul_cancel₀ ha, map_one, dg_one]⟩

def tG (a : (D.s.atP p).Fp) (ha : a ≠ 0) : GG p := (tU a ha, MulOpposite.op (tU a ha))

def KD (a : (D.s.atP p).Fp) (ha : a ≠ 0) : Subgroup (GG p) := cj (tG a ha) (KP M p)

theorem mem_KP {x : GG p} : x ∈ KP M p ↔
    TieN.IntLow (M p) ((x.1 : GLp p) : MP p) ∧ TieN.IntUp (M p) ((x.2.unop : GLp p) : MP p) := Iff.rfl

theorem mem_KD {a : (D.s.atP p).Fp} (ha : a ≠ 0) {x : GG p} : x ∈ KD M a ha ↔
    TieN.IntLow (M p) (dg (algebraMap _ _ a) * ((x.1 : GLp p) : MP p) * dg (algebraMap _ _ a⁻¹)) ∧
    TieN.IntUp (M p) (dg (algebraMap _ _ a⁻¹) * ((x.2.unop : GLp p) : MP p) * dg (algebraMap _ _ a)) := by
  rw [KD, mem_cj]
  show TieN.IntLow (M p) (dg (algebraMap _ _ a) * ((x.1 : GLp p) : MP p) * dg (algebraMap _ _ a⁻¹)) ∧
    TieN.IntUp (M p) (dg (algebraMap _ _ a⁻¹) * (((x.2.unop : GLp p) : MP p) * dg (algebraMap _ _ a))) ↔ _
  rw [← Matrix.mul_assoc]

end Mat

section Scale

variable {a : (D.s.atP p).Fp}

theorem intLow_scale (ha : a ≠ 0) (haO : a ∈ 𝒪[(D.s.atP p).Fp]) {l : MP p} (hl : TieN.IntLow (M p) l) :
    TieN.IntLow (M p) (dg (algebraMap _ _ a) * l * dg (algebraMap _ _ a⁻¹)) := by
  haveI := (D.s.atP p).lf
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j => ?_⟩
  · rw [dg_entry, hl.1 i, mul_one, mul_comm, pow_inv_pow ha]
  · rw [dg_entry, hl.2.1 i j hij, mul_zero, zero_mul]
  · rw [dg_entry]
    rcases le_or_gt (j : ℕ) i with h | h
    · rw [mul_right_comm, pow_scale ha h]
      exact (M p).R.mul_mem ((M p).R.pow_mem (alg_mem_R (M p) ⟨a, haO⟩) _) (hl.2.2 i j)
    · rw [hl.2.1 i j h, mul_zero, zero_mul]
      exact (M p).R.zero_mem

theorem intUp_scale (ha : a ≠ 0) (haO : a ∈ 𝒪[(D.s.atP p).Fp]) {ρ : MP p} (hρ : TieN.IntUp (M p) ρ) :
    TieN.IntUp (M p) (dg (algebraMap _ _ a⁻¹) * ρ * dg (algebraMap _ _ a)) := by
  haveI := (D.s.atP p).lf
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j => ?_⟩
  · rw [dg_entry, hρ.1 i, mul_one, pow_inv_pow ha]
  · rw [dg_entry, hρ.2.1 i j hij, mul_zero, zero_mul]
  · rw [dg_entry]
    rcases le_or_gt (i : ℕ) j with h | h
    · rw [mul_right_comm, mul_comm ((algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (i : ℕ)), pow_scale ha h]
      exact (M p).R.mul_mem ((M p).R.pow_mem (alg_mem_R (M p) ⟨a, haO⟩) _) (hρ.2.2 i j)
    · rw [hρ.2.1 i j h, mul_zero, zero_mul]
      exact (M p).R.zero_mem

theorem intLow_scale_of (ha : a ≠ 0) (haO : a ∈ 𝒪[(D.s.atP p).Fp]) {l : MP p} (hl : IsLoUni l)
    (hR : ∀ i j, algebraMap _ (D.s.atP p).Ep a * l i j ∈ (M p).R) :
    TieN.IntLow (M p) (dg (algebraMap _ _ a) * l * dg (algebraMap _ _ a⁻¹)) := by
  haveI := (D.s.atP p).lf
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j => ?_⟩
  · rw [dg_entry, (hl i i).2 rfl, mul_one, mul_comm, pow_inv_pow ha]
  · rw [dg_entry, (hl i j).1 hij, mul_zero, zero_mul]
  · rw [dg_entry]
    rcases lt_trichotomy (j : ℕ) i with h | h | h
    · rw [mul_right_comm, pow_scale ha h.le]
      obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) - j = k + 1 := ⟨(i : ℕ) - j - 1, by omega⟩
      rw [hk, pow_succ, mul_assoc]
      exact (M p).R.mul_mem ((M p).R.pow_mem (alg_mem_R (M p) ⟨a, haO⟩) _) (hR i j)
    · have hij : j = i := Fin.ext h
      subst hij
      rw [(hl j j).2 rfl, mul_one, mul_comm, pow_inv_pow ha]
      exact (M p).R.one_mem
    · rw [(hl i j).1 h, mul_zero, zero_mul]
      exact (M p).R.zero_mem

theorem intUp_scale_of (ha : a ≠ 0) (haO : a ∈ 𝒪[(D.s.atP p).Fp]) {ρ : MP p} (hρ : IsUpUni ρ)
    (hR : ∀ i j, algebraMap _ (D.s.atP p).Ep a * ρ i j ∈ (M p).R) :
    TieN.IntUp (M p) (dg (algebraMap _ _ a⁻¹) * ρ * dg (algebraMap _ _ a)) := by
  haveI := (D.s.atP p).lf
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j => ?_⟩
  · rw [dg_entry, (hρ i i).2 rfl, mul_one, pow_inv_pow ha]
  · rw [dg_entry, (hρ i j).1 hij, mul_zero, zero_mul]
  · rw [dg_entry]
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · rw [mul_right_comm, mul_comm ((algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (i : ℕ)), pow_scale ha h.le]
      obtain ⟨k, hk⟩ : ∃ k, (j : ℕ) - i = k + 1 := ⟨(j : ℕ) - i - 1, by omega⟩
      rw [hk, pow_succ, mul_assoc]
      exact (M p).R.mul_mem ((M p).R.pow_mem (alg_mem_R (M p) ⟨a, haO⟩) _) (hR i j)
    · have hij : i = j := Fin.ext h
      subst hij
      rw [(hρ i i).2 rfl, mul_one, pow_inv_pow ha]
      exact (M p).R.one_mem
    · rw [(hρ i j).1 h, mul_zero, zero_mul]
      exact (M p).R.zero_mem

theorem intLow_of_scaled (ha : a ≠ 0) {l : MP p}
    (h : TieN.IntLow (M p) (dg (algebraMap _ _ a) * l * dg (algebraMap _ _ a⁻¹))) (hR : ∀ i j, l i j ∈ (M p).R) :
    TieN.IntLow (M p) l := by
  have hu : ∀ i j, l i j = (algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (i : ℕ) *
      (dg (algebraMap _ _ a) * l * dg (algebraMap _ _ a⁻¹) : MP p) i j * (algebraMap _ (D.s.atP p).Ep a) ^ (j : ℕ) := by
    intro i j
    rw [dg_entry]
    calc l i j = ((algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (i : ℕ) * (algebraMap _ (D.s.atP p).Ep a) ^ (i : ℕ)) * l i j *
          ((algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (j : ℕ) * (algebraMap _ (D.s.atP p).Ep a) ^ (j : ℕ)) := by
          rw [pow_inv_pow ha, pow_inv_pow ha, one_mul, mul_one]
      _ = _ := by ring
  refine ⟨fun i => ?_, fun i j hij => ?_, hR⟩
  · rw [hu i i, h.1 i, mul_one, pow_inv_pow ha]
  · rw [hu i j, h.2.1 i j hij, mul_zero, zero_mul]

theorem intUp_of_scaled (ha : a ≠ 0) {ρ : MP p}
    (h : TieN.IntUp (M p) (dg (algebraMap _ _ a⁻¹) * ρ * dg (algebraMap _ _ a))) (hR : ∀ i j, ρ i j ∈ (M p).R) :
    TieN.IntUp (M p) ρ := by
  have hu : ∀ i j, ρ i j = (algebraMap _ (D.s.atP p).Ep a) ^ (i : ℕ) *
      (dg (algebraMap _ _ a⁻¹) * ρ * dg (algebraMap _ _ a) : MP p) i j * (algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (j : ℕ) := by
    intro i j
    rw [dg_entry]
    calc ρ i j = ((algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (i : ℕ) * (algebraMap _ (D.s.atP p).Ep a) ^ (i : ℕ)) * ρ i j *
          ((algebraMap _ (D.s.atP p).Ep a⁻¹) ^ (j : ℕ) * (algebraMap _ (D.s.atP p).Ep a) ^ (j : ℕ)) := by
          rw [pow_inv_pow ha, pow_inv_pow ha, one_mul, mul_one]
      _ = _ := by ring
  refine ⟨fun i => ?_, fun i j hij => ?_, hR⟩
  · rw [hu i i, h.1 i, mul_one, mul_comm, pow_inv_pow ha]
  · rw [hu i j, h.2.1 i j hij, mul_zero, zero_mul]

theorem KP_le_KD (ha : a ≠ 0) (haO : a ∈ 𝒪[(D.s.atP p).Fp]) : KP M p ≤ KD M a ha := fun x hx =>
  (mem_KD M ha).2 ⟨intLow_scale M ha haO hx.1, intUp_scale M ha haO hx.2⟩

end Scale

section Top

theorem isClosed_imp {X : Type*} [TopologicalSpace X] (P : Prop) {s : Set X} (hs : IsClosed s) :
    IsClosed {x | P → x ∈ s} := by
  by_cases h : P
  · simpa [h] using hs
  · simp [h]

include M in
theorem isClosed_loUni (p : PlF D) : IsClosed {m : MP p | IsLoUni m} := by
  haveI := (D.s.atP p).lf
  haveI := t2E (M p)
  have e : {m : MP p | IsLoUni m} = ⋂ i, ⋂ j, ({m : MP p | i < j → m ∈ {m : MP p | m i j = 0}} ∩
      {m : MP p | i = j → m ∈ {m : MP p | m i j = 1}}) := by
    ext m
    simp only [IsLoUni, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [e]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    (isClosed_imp _ (isClosed_eq (continuous_id.matrix_elem i j) continuous_const)).inter
      (isClosed_imp _ (isClosed_eq (continuous_id.matrix_elem i j) continuous_const))

include M in
theorem isClosed_upUni (p : PlF D) : IsClosed {m : MP p | IsUpUni m} := by
  haveI := (D.s.atP p).lf
  haveI := t2E (M p)
  have e : {m : MP p | IsUpUni m} = ⋂ i, ⋂ j, ({m : MP p | j < i → m ∈ {m : MP p | m i j = 0}} ∩
      {m : MP p | i = j → m ∈ {m : MP p | m i j = 1}}) := by
    ext m
    simp only [IsUpUni, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [e]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    (isClosed_imp _ (isClosed_eq (continuous_id.matrix_elem i j) continuous_const)).inter
      (isClosed_imp _ (isClosed_eq (continuous_id.matrix_elem i j) continuous_const))

theorem isClosed_intLowSet (hRcl : IsClosed ((M p).R : Set (D.s.atP p).Ep)) :
    IsClosed {l : MP p | TieN.IntLow (M p) l} := by
  haveI := (D.s.atP p).lf
  haveI := t2E (M p)
  have e : {l : MP p | TieN.IntLow (M p) l} = (⋂ i, {l : MP p | l i i = 1}) ∩
      (⋂ i, ⋂ j, {l : MP p | i < j → l ∈ {l : MP p | l i j = 0}}) ∩ ⋂ i, ⋂ j, {l : MP p | l i j ∈ (M p).R} := by
    ext l
    simp only [TieN.IntLow, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, and_assoc]
  rw [e]
  exact ((isClosed_iInter fun i => isClosed_eq (continuous_id.matrix_elem i i) continuous_const).inter
    (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_imp _ (isClosed_eq (continuous_id.matrix_elem i j) continuous_const))).inter
    (isClosed_iInter fun i => isClosed_iInter fun j => hRcl.preimage (continuous_id.matrix_elem i j))

theorem isClosed_intUpSet (hRcl : IsClosed ((M p).R : Set (D.s.atP p).Ep)) :
    IsClosed {l : MP p | TieN.IntUp (M p) l} := by
  haveI := (D.s.atP p).lf
  haveI := t2E (M p)
  have e : {l : MP p | TieN.IntUp (M p) l} = (⋂ i, {l : MP p | l i i = 1}) ∩
      (⋂ i, ⋂ j, {l : MP p | j < i → l ∈ {l : MP p | l i j = 0}}) ∩ ⋂ i, ⋂ j, {l : MP p | l i j ∈ (M p).R} := by
    ext l
    simp only [TieN.IntUp, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, and_assoc]
  rw [e]
  exact ((isClosed_iInter fun i => isClosed_eq (continuous_id.matrix_elem i i) continuous_const).inter
    (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_imp _ (isClosed_eq (continuous_id.matrix_elem i j) continuous_const))).inter
    (isClosed_iInter fun i => isClosed_iInter fun j => hRcl.preimage (continuous_id.matrix_elem i j))

theorem isCompact_intLowSet (hRc : IsCompact ((M p).R : Set (D.s.atP p).Ep)) :
    IsCompact {l : MP p | TieN.IntLow (M p) l} := by
  haveI := (D.s.atP p).lf
  haveI := t2E (M p)
  have hK : IsCompact (Set.univ.pi fun _ : Fin (D.R.rS + 1) => Set.univ.pi fun _ : Fin (D.R.rS + 1) =>
      ((M p).R : Set (D.s.atP p).Ep)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hRc
  refine hK.of_isClosed_subset (isClosed_intLowSet M hRc.isClosed) ?_
  intro l hl
  exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => hl.2.2 i j

theorem isCompact_intUpSet (hRc : IsCompact ((M p).R : Set (D.s.atP p).Ep)) :
    IsCompact {l : MP p | TieN.IntUp (M p) l} := by
  haveI := (D.s.atP p).lf
  haveI := t2E (M p)
  have hK : IsCompact (Set.univ.pi fun _ : Fin (D.R.rS + 1) => Set.univ.pi fun _ : Fin (D.R.rS + 1) =>
      ((M p).R : Set (D.s.atP p).Ep)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hRc
  refine hK.of_isClosed_subset (isClosed_intUpSet M hRc.isClosed) ?_
  intro l hl
  exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => hl.2.2 i j

theorem isCompact_KP (hRc : IsCompact ((M p).R : Set (D.s.atP p).Ep)) : IsCompact (KP M p : Set (GG p)) := by
  haveI := (D.s.atP p).lf
  haveI := topE (M p)
  haveI := t2E (M p)
  let ι : GG p → (MP p × (MP p)ᵐᵒᵖ) × (MP p × (MP p)ᵐᵒᵖ) :=
    fun x => (Units.embedProduct _ x.1, Units.embedProduct _ x.2.unop)
  have hι : Topology.IsClosedEmbedding ι :=
    Units.isClosedEmbedding_embedProduct.prodMap
      (Units.isClosedEmbedding_embedProduct.comp MulOpposite.opHomeomorph.symm.isClosedEmbedding)
  have hIL := isCompact_intLowSet M hRc
  have hIU := isCompact_intUpSet M hRc
  let Kset : Set ((MP p × (MP p)ᵐᵒᵖ) × (MP p × (MP p)ᵐᵒᵖ)) :=
    ({l : MP p | TieN.IntLow (M p) l} ×ˢ (MulOpposite.op '' {l : MP p | TieN.IntLow (M p) l})) ×ˢ
      ({l : MP p | TieN.IntUp (M p) l} ×ˢ (MulOpposite.op '' {l : MP p | TieN.IntUp (M p) l}))
  have hK : IsCompact Kset :=
    (hIL.prod (hIL.image MulOpposite.continuous_op)).prod (hIU.prod (hIU.image MulOpposite.continuous_op))
  have hcl : IsClosed (KP M p : Set (GG p)) :=
    ((isClosed_intLowSet M hRc.isClosed).preimage (Units.continuous_val.comp continuous_fst)).inter
      ((isClosed_intUpSet M hRc.isClosed).preimage
        (Units.continuous_val.comp (MulOpposite.continuous_unop.comp continuous_snd)))
  have hsub : (KP M p : Set (GG p)) ⊆ ι ⁻¹' Kset := by
    intro x hx
    have hx1 := ((mem_KP M).1 hx).1
    have hx2 := ((mem_KP M).1 hx).2
    have hy := (mem_KP M).1 ((KP M p).inv_mem hx)
    exact ⟨⟨hx1, _, hy.1, rfl⟩, hx2, _, hy.2, rfl⟩
  exact (hι.isCompact_preimage hK).of_isClosed_subset hcl hsub

theorem isCompact_KD (hRc : IsCompact ((M p).R : Set (D.s.atP p).Ep)) {a : (D.s.atP p).Fp} (ha : a ≠ 0) :
    IsCompact (KD M a ha : Set (GG p)) := by
  haveI := (D.s.atP p).lf
  haveI := topE (M p)
  rw [KD, cj, Subgroup.coe_map]
  refine (isCompact_KP M hRc).image ?_
  have e : ((MulAut.conj (tG a ha)⁻¹).toMonoidHom : GG p → GG p) =
      fun x => (tG a ha)⁻¹ * x * (tG a ha)⁻¹⁻¹ := by
    funext x
    rfl
  rw [e]
  exact (continuous_const.mul continuous_id).mul continuous_const

theorem relIndex_ne_zero (hRc : IsCompact ((M p).R : Set (D.s.atP p).Ep)) {a : (D.s.atP p).Fp} (ha : a ≠ 0)
    (S' : Subgroup (GG p)) (hS : IsClosed (S' : Set (GG p))) :
    (KP M p ⊓ S').relIndex (KD M a ha ⊓ S') ≠ 0 := by
  haveI := (D.s.atP p).lf
  haveI := topE (M p)
  haveI := t2E (M p)
  have hBc : IsCompact ((KD M a ha ⊓ S' : Subgroup (GG p)) : Set (GG p)) := (isCompact_KD M hRc ha).inter_right hS
  haveI : CompactSpace (KD M a ha ⊓ S' : Subgroup (GG p)) := isCompact_iff_compactSpace.1 hBc
  have hR : IsOpen ((M p).R : Set (D.s.atP p).Ep) := PI.ProdFormulaE.ROpen.isOpen_R (M p)
  have h1 : Continuous fun x : GG p => ((x.1 : GLp p) : MP p) := Units.continuous_val.comp continuous_fst
  have h2 : Continuous fun x : GG p => ((x.2.unop : GLp p) : MP p) :=
    Units.continuous_val.comp (MulOpposite.continuous_unop.comp continuous_snd)
  let Eset : Set (GG p) := (⋂ i, ⋂ j, (fun x : GG p => ((x.1 : GLp p) : MP p) i j) ⁻¹' ((M p).R : Set _)) ∩
    ⋂ i, ⋂ j, (fun x : GG p => ((x.2.unop : GLp p) : MP p) i j) ⁻¹' ((M p).R : Set _)
  have hE : IsOpen Eset :=
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hR.preimage (h1.matrix_elem i j)).inter
      (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hR.preimage (h2.matrix_elem i j))
  have hopen : IsOpen (((KP M p ⊓ S').subgroupOf (KD M a ha ⊓ S') : Subgroup _) :
      Set (KD M a ha ⊓ S' : Subgroup (GG p))) := by
    have e : (((KP M p ⊓ S').subgroupOf (KD M a ha ⊓ S') : Subgroup _) : Set (KD M a ha ⊓ S' : Subgroup (GG p))) =
        Subtype.val ⁻¹' Eset := by
      ext y
      obtain ⟨hK, hS'⟩ := Subgroup.mem_inf.1 y.2
      rw [mem_KD] at hK
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Set.mem_preimage, Eset,
        Set.mem_inter_iff, Set.mem_iInter, mem_KP]
      constructor
      · rintro ⟨⟨hl, hu⟩, -⟩
        exact ⟨hl.2.2, hu.2.2⟩
      · rintro ⟨hl, hu⟩
        exact ⟨⟨intLow_of_scaled M ha hK.1 hl, intUp_of_scaled M ha hK.2 hu⟩, hS'⟩
    rw [e]
    exact hE.preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen _ hopen
  show ((KP M p ⊓ S').subgroupOf (KD M a ha ⊓ S')).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

theorem idxRatio_norm (hRc : IsCompact ((M p).R : Set (D.s.atP p).Ep)) (S' : Subgroup (GG p))
    (hS : IsClosed (S' : Set (GG p))) (c : GG p) (hc1 : IsLoUni ((c.1 : GLp p) : MP p))
    (hc2 : IsUpUni ((c.2.unop : GLp p) : MP p)) (hcS : cj c S' = S') :
    IdxRatio (KP M p ⊓ S') (cj c (KP M p ⊓ S')) = 1 := by
  haveI := (D.s.atP p).lf
  obtain ⟨a, ha0, haR⟩ := common_denom (M p)
    (fun k : (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) ⊕ (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) =>
      Sum.elim (fun ij => ((c.1 : GLp p) : MP p) ij.1 ij.2) (fun ij => ((c.2.unop : GLp p) : MP p) ij.1 ij.2) k)
  have ha : (a : (D.s.atP p).Fp) ≠ 0 := fun h => ha0 (Subtype.ext h)
  have hcK : c ∈ KD M (a : (D.s.atP p).Fp) ha :=
    (mem_KD M ha).2 ⟨intLow_scale_of M ha a.2 hc1 fun i j => haR (Sum.inl (i, j)),
      intUp_scale_of M ha a.2 hc2 fun i j => haR (Sum.inr (i, j))⟩
  have hB : cj c (KD M (a : (D.s.atP p).Fp) ha ⊓ S') = KD M (a : (D.s.atP p).Fp) ha ⊓ S' := by
    ext g
    rw [mem_cj, Subgroup.mem_inf, Subgroup.mem_inf, ← mem_cj, ← mem_cj, cj_self hcK, hcS]
  exact unimod_of_norm _ _ c (inf_le_inf_right S' (KP_le_KD M ha a.2)) hB (relIndex_ne_zero M hRc ha S' hS)

theorem isClosed_StP (w : Point D.host.E (D.R.rS + 1)) :
    IsClosed ((StP M δ u u' w p : Subgroup (GG p)) : Set (GG p)) := by
  haveI := (D.s.atP p).lf
  haveI := topE (M p)
  haveI := t2E (M p)
  have h1 : Continuous fun x : GG p => ((x.1 : GLp p) : MP p) := Units.continuous_val.comp continuous_fst
  have h2 : Continuous fun x : GG p => ((x.2.unop : GLp p) : MP p) :=
    Units.continuous_val.comp (MulOpposite.continuous_unop.comp continuous_snd)
  exact ((isClosed_loUni M p).preimage h1).inter (((isClosed_upUni M p).preimage h2).inter
    (isClosed_eq ((h1.mul continuous_const).mul h2) continuous_const))

theorem unimodAt_holds (w : Point D.host.E (D.R.rS + 1)) : UnimodAt M δ u u' (p := p) w := by
  haveI := (D.s.atP p).lf
  haveI := (D.s.atP p).char0
  have hRc := R_compact (M p)
  intro s hs
  have hAg : Ag M δ u u' (p := p) w = KP M p ⊓ StP M δ u u' w p := by
    ext x
    rw [Ag, Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(mem_KP M).2 hy, y.2⟩
    · rintro ⟨hK, hS⟩
      exact ⟨⟨x, hS⟩, hK, rfl⟩
  rw [hAg]
  exact idxRatio_norm M hRc _ (isClosed_StP M δ u u' w) s hs.1 hs.2.1 (cj_self hs)

variable (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

end Top

end Formalism.L2.SG.Pf.ProdEP2Uni

module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ImStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.CmpIso
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL

@[expose] public section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.DcosVol
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

namespace UpperTheory.Gal.Join

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem mem_dcos_iff {K : Subgroup (GL (Fin n) k)} (hK : IwLev K) {t : Fin n → kˣ} (ht : Dom t)
    (g : GL (Fin n) k) :
    g ∈ dcos K t ↔ ∃ u ∈ unipB k (Fin n), u ∈ K ∧ ∃ i ∈ K, g = u * diagT k (Fin n) t * i := by
  refine ⟨?_, fun ⟨u, _, hu, i, hi, e⟩ => ⟨u, hu, i, hi, e⟩⟩
  rintro ⟨a, ha, b, hb, rfl⟩
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := hK.fact a ha
  refine ⟨u, hu.2, hu.1, _, mul_mem (mul_mem hd (hK.low t ht c hc)) hb, ?_⟩
  have e : diagT k (Fin n) t * diagT k (Fin n) d = diagT k (Fin n) d * diagT k (Fin n) t := by
    rw [← map_mul, mul_comm, map_mul]
  calc u * diagT k (Fin n) d * c * diagT k (Fin n) t * b
      = u * (diagT k (Fin n) d * diagT k (Fin n) t) * ((diagT k (Fin n) t)⁻¹ * c * diagT k (Fin n) t) * b := by
        group
    _ = _ := by rw [← e]; group

private theorem dcos_eq_image (K : Subgroup (GL (Fin n) k)) (t : Fin n → kˣ) :
    dcos K t = (fun x : GL (Fin n) k × GL (Fin n) k => x.1 * diagT k (Fin n) t * x.2) ''
      ((K : Set (GL (Fin n) k)) ×ˢ (K : Set (GL (Fin n) k))) := by
  ext g
  exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨(a, b), ⟨ha, hb⟩, e.symm⟩, fun ⟨x, hx, e⟩ => ⟨x.1, hx.1, x.2, hx.2, e.symm⟩⟩

private theorem isCompact_dcos {K : Subgroup (GL (Fin n) k)} (hK : CO K) (t : Fin n → kˣ) :
    IsCompact (dcos K t) := by
  rw [dcos_eq_image]
  exact (hK.1.prod hK.1).image (by fun_prop)

private theorem isOpen_dcos {K : Subgroup (GL (Fin n) k)} (hK : CO K) (t : Fin n → kˣ) :
    IsOpen (dcos K t) := by
  have e : dcos K t = ⋃ a ∈ (K : Set (GL (Fin n) k)),
      (fun g => (a * diagT k (Fin n) t) * g) '' (K : Set (GL (Fin n) k)) := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop]
    exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨a, ha, b, hb, e.symm⟩, fun ⟨a, ha, b, hb, e⟩ => ⟨a, ha, b, hb, e.symm⟩⟩
  rw [e]
  exact isOpen_biUnion fun a _ => (Homeomorph.mulLeft (a * diagT k (Fin n) t)).isOpenMap _ hK.2

open GlobalTheory.SplitWeil GlobalTheory.IwahoriTraceProof in
private theorem isClosed_unipB : IsClosed (unipB k (Fin n) : Set (GL (Fin n) k)) := by
  have e : (unipB k (Fin n) : Set (GL (Fin n) k)) = (⋂ i, ⋂ j, ⋂ _ : j < i, {g : GL (Fin n) k | g.val i j = 0}) ∩
      ⋂ i, {g : GL (Fin n) k | g.val i i = 1} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    exact mem_unipB k
  rw [e]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const).inter
    (isClosed_iInter fun i => isClosed_eq (Units.continuous_val.matrix_elem i i) continuous_const)


open GlobalTheory.SplitWeil GlobalTheory.IwahoriTraceProof in
private theorem measure_dcos [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : Measure (GL (Fin n) k))
    [μ.IsHaarMeasure] {K : Subgroup (GL (Fin n) k)} (hK : IwLev K) {t : Fin n → kˣ} (ht : Dom t) :
    μ.real (dcos K t) = μ.real (K : Set (GL (Fin n) k)) * (deltaB t)⁻¹ := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  letI : MeasurableSpace (unipRad k (points (Fin n))) := _root_.borel _
  haveI : BorelSpace (unipRad k (points (Fin n))) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unipRad k (points (Fin n))) :=
    (UnipHaar.unipHomeo (points (Fin n))).isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (unipRad k (points (Fin n))) :=
    (UnipHaar.unipHomeo (points (Fin n))).secondCountableTopology
  let ν : Measure (unipRad k (points (Fin n))) := Measure.haar
  have ho : IsOpen {s : unipRad k (points (Fin n)) | (s : GL (Fin n) k) ∈ K} :=
    hK.co.2.preimage continuous_subtype_val
  have hcl : IsClosed (unipRad k (points (Fin n)) : Set (GL (Fin n) k)) := isClosed_unipB
  have hc : IsCompact {s : unipRad k (points (Fin n)) | (s : GL (Fin n) k) ∈ K} :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK.co.1
  have h1 := measure_mul_eq μ ν hK.co.2 (t := diagT k (Fin n) t)
    (fun u hu => by simpa [unipB] using conj_mem_unipB t⁻¹ hu)
    (fun u hu hI => hK.up t ht u ⟨hI, hu⟩)
    (isCompact_dcos hK.co t).measurableSet (mem_dcos_iff hK ht)
  have h2 := UnipHaar.haar_conj_eq_modulus_mul k (Fin n) (Fin n) (fun _ => Unit) (points (Fin n)) ν
    (leviTorus k (Fin n) t) _ ho.measurableSet
  rw [← deltaB_eq_modulus] at h2
  have h3 := (congrArg (· * μ (dcos K t)) h2).symm.trans h1
  rw [mul_right_comm, ENNReal.mul_left_inj (ho.measure_pos ν ⟨1, one_mem K⟩).ne' hc.measure_lt_top.ne] at h3
  rw [measureReal_def, measureReal_def, ← h3, ENNReal.toReal_mul, ENNReal.toReal_ofReal (deltaB_pos t).le,
    mul_right_comm, mul_inv_cancel₀ (deltaB_pos t).ne', one_mul]

end

end UpperTheory.Gal.Join

theorem UpperTheory.Gal.Join.dcosVol :
    UpperTheory.Gal.Join.DcosVol := by
  intro k _ _ _ _ n _ _ μ _ K hK t ht
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc := isCompact_dcos hK.co t
  refine ⟨⟨(LocallyConstant.indicator (1 : LocallyConstant (GL (Fin n) k) ℂ) ⟨hc.isClosed, isOpen_dcos hK.co t⟩).2,
    HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩, measure_dcos μ hK ht⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.CasTrace
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.DcosOp
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.dcosOp :
    UpperTheory.Gal.Join.DcosOp := by
  intro G V _ _ _ _ _ _ μ _ _ _ _ π hπ K hK e he x
  have hfx : ∀ {v : V}, v ∈ fixed π K ↔ ∀ k ∈ K, π k v = v := GlobalTheory.IwahoriInj.mem_fixed
  set D : Set G := {g | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b} with hDdef
  have hDc : IsCompact D := by
    convert (hK.1.prod hK.1).image (f := fun y : G × G => y.1 * x * y.2) (by fun_prop) using 1
    ext g
    exact ⟨fun ⟨a, ha, b, hb, h⟩ => ⟨(a, b), ⟨ha, hb⟩, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y.1, hy.1, y.2, hy.2, h.symm⟩⟩
  have hDm : MeasurableSet D := hDc.measurableSet
  have hL : ∀ k ∈ K, ∀ g, k * g ∈ D ↔ g ∈ D := by
    have h1 : ∀ k ∈ K, ∀ g, g ∈ D → k * g ∈ D := by
      rintro k hk _ ⟨a, ha, b, hb, rfl⟩
      exact ⟨k * a, mul_mem hk ha, b, hb, by simp only [mul_assoc]⟩
    refine fun k hk g => ⟨fun h => ?_, h1 k hk g⟩
    simpa using h1 _ (inv_mem hk) _ h
  have hR : ∀ k ∈ K, ∀ g, g * k ∈ D ↔ g ∈ D := by
    have h1 : ∀ k ∈ K, ∀ g, g ∈ D → g * k ∈ D := by
      rintro k hk _ ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b * k, mul_mem hb hk, by simp only [mul_assoc]⟩
    refine fun k hk g => ⟨fun h => ?_, h1 k hk g⟩
    simpa using h1 _ (inv_mem hk) _ h
  obtain ⟨A, hA⟩ := GlobalTheory.IwahoriTraceProof.exists_setOp μ hπ hDc hDm
  have hsep : ∀ y z : V, (∀ l : Module.Dual ℂ V, l y = l z) → y = z := fun y z h => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, h l, sub_self]
  have hAr : ∀ k ∈ K, ∀ v, A (π k v) = A v := fun k hk v => hsep _ _ fun l => by
    rw [(hA _ l).2, (hA v l).2, ← integral_indicator hDm, ← integral_indicator hDm,
      ← integral_mul_right_eq_self (D.indicator fun g => l (π g v)) k]
    congr 1
    funext g
    by_cases h : g ∈ D
    · simp [h, (hR k hk g).2 h]
    · have h' : g * k ∉ D := fun h' => h ((hR k hk g).1 h')
      simp [h, h']
  have hAl : ∀ k ∈ K, ∀ v, π k (A v) = A v := fun k hk v => hsep _ _ fun l => by
    have h0 := (hA v (l ∘ₗ π k)).2
    rw [LinearMap.comp_apply] at h0
    rw [h0, (hA v l).2, ← integral_indicator hDm, ← integral_indicator hDm,
      ← integral_mul_left_eq_self (D.indicator fun g => l (π g v)) k]
    congr 1
    funext g
    by_cases h : g ∈ D
    · simp [h, (hL k hk g).2 h]
    · have h' : k * g ∉ D := fun h' => h ((hL k hk g).1 h')
      simp [h, h']
  have hAe : ∀ v, A (e v) = A v := fun v => he.lin V A v fun k hk => hAr k hk v
  have heA : ∀ v, e (A v) = A v := fun v => he.fix _ (hfx.2 fun k hk => hAl k hk v)
  have hval : ∀ v, A v = (μ.real D : ℂ) • e (π x (e v)) := fun v => hsep _ _ fun l => by
    have hw : ∀ k ∈ K, π k (e v) = e v := hfx.1 (he.mem v)
    have h0 := (hA (e v) (l ∘ₗ e)).2
    rw [LinearMap.comp_apply, heA, hAe] at h0
    rw [h0, map_smul, smul_eq_mul,
      setIntegral_congr_fun (g := fun _ => l (e (π x (e v)))) hDm fun g hg => ?_]
    · simp [Measure.real]
    · obtain ⟨a, ha, b, hb, rfl⟩ := hg
      simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply, hw b hb, he.inv a ha]
  intro v l
  have hind : (fun g => D.indicator (fun _ => (1 : ℂ)) g * l (π g v)) = D.indicator fun g => l (π g v) := by
    funext g
    by_cases h : g ∈ D <;> simp [h]
  rw [hind]
  refine ⟨(integrable_indicator_iff hDm).2 (hA v l).1, ?_⟩
  rw [integral_indicator hDm, ← (hA v l).2, hval v]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.KerKill
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

namespace UpperTheory.Gal.Join.KernelKilling

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem conj_entry (t : Fin n → kˣ) (u : GL (Fin n) k) (i j : Fin n) :
    ((diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (t i : k) * (u : Matrix (Fin n) (Fin n) k) i j * (t j : k)⁻¹ := by
  have hinv : (((diagT k (Fin n) t)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      Matrix.diagonal fun i => ((t i : k))⁻¹ := by
    rw [← map_inv, val_diagT]
    congr 1
    funext i
    simp
  rw [Units.val_mul, Units.val_mul, hinv, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem conj_close {u : GL (Fin n) k} (hu : u ∈ unipB k (Fin n))
    {c B : ValueGroupWithZero k} (hc : c ≤ 1) (hB0 : B ≠ 0)
    (hB : ∀ i j, valuation k ((u : Matrix (Fin n) (Fin n) k) i j) ≤ B)
    (t : Fin n → kˣ)
    (ht : ∀ i j, i < j → valuation k (t i : k) ≤ c * B⁻¹ * valuation k (t j : k)) (i j : Fin n) :
    valuation k (((diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ c ∧
      valuation k (((diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
  rw [conj_entry]
  rw [mem_unipB] at hu
  obtain ⟨hlow, hdiag⟩ := hu
  have hc1 : c ≤ 1 := hc
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hne : i ≠ j := ne_of_lt hij
    have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = 0 := Matrix.one_apply_ne hne
    have hvj : valuation k (t j : k) ≠ 0 := by simp
    have key : valuation k ((t i : k) * (u : Matrix (Fin n) (Fin n) k) i j * (t j : k)⁻¹) ≤ c := by
      rw [map_mul, map_mul, map_inv₀]
      calc valuation k (t i : k) * valuation k ((u : Matrix (Fin n) (Fin n) k) i j) *
            (valuation k (t j : k))⁻¹
          ≤ c * B⁻¹ * valuation k (t j : k) * B * (valuation k (t j : k))⁻¹ := by
            gcongr
            · exact ht i j hij
            · exact hB i j
        _ = c * (B⁻¹ * B) * (valuation k (t j : k) * (valuation k (t j : k))⁻¹) := by
            simp only [mul_comm, mul_assoc, mul_left_comm]
        _ = c := by rw [inv_mul_cancel₀ hB0, mul_inv_cancel₀ hvj, mul_one, mul_one]
    rw [h1, sub_zero]
    exact ⟨key, le_trans key hc1⟩
  · rw [hdiag i, Matrix.one_apply_eq]
    have : (t i : k) * 1 * (t i : k)⁻¹ = 1 := by simp
    rw [this, sub_self, map_zero, map_one]
    exact ⟨zero_le', le_refl _⟩
  · have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = 0 := Matrix.one_apply_ne (ne_of_gt hij)
    rw [hlow i j hij, h1]
    simp

private theorem exists_bound (u : GL (Fin n) k) : ∃ B : ValueGroupWithZero k, B ≠ 0 ∧ ∀ i j,
    valuation k ((u : Matrix (Fin n) (Fin n) k) i j) ≤ B ∧
      valuation k (((u⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ B := by
  obtain ⟨M, hM⟩ := Finite.exists_le (fun p : Fin n × Fin n =>
    max (valuation k ((u : Matrix (Fin n) (Fin n) k) p.1 p.2))
      (valuation k (((u⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p.1 p.2)))
  refine ⟨max M 1, ?_, fun i j => ⟨?_, ?_⟩⟩
  · exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  · exact le_trans (le_trans (le_max_left _ _) (hM (i, j))) (le_max_left _ _)
  · exact le_trans (le_trans (le_max_right _ _) (hM (i, j))) (le_max_left _ _)

private theorem conj_mem {K : Subgroup (GL (Fin n) k)} (hK : IsOpen (K : Set (GL (Fin n) k)))
    {u : GL (Fin n) k} (hu : u ∈ unipB k (Fin n)) :
    ∃ r : ValueGroupWithZero k, r ≠ 0 ∧ ∀ t : Fin n → kˣ,
      (∀ i j, i < j → valuation k (t i : k) ≤ r * valuation k (t j : k)) →
        diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ ∈ K := by
  obtain ⟨m, -, hm⟩ := (GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one k n).mem_iff.1
    (hK.mem_nhds K.one_mem)
  obtain ⟨B, hB0, hB⟩ := exists_bound u
  set c : ValueGroupWithZero k :=
    valuation k ((GroundTheory.Automorphic.GLnLocal.uniformizer k : k)) ^ m with hcdef
  have hc : c ≤ 1 := pow_le_one₀ zero_le'
    (le_of_lt (GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_lt_one k))
  have hc0 : c ≠ 0 := pow_ne_zero _ (GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_ne_zero k)
  have hui : u⁻¹ ∈ unipB k (Fin n) := inv_mem hu
  refine ⟨c * B⁻¹, mul_ne_zero hc0 (inv_ne_zero hB0), fun t ht => hm ?_⟩
  have hA := conj_close hu hc hB0 (fun i j => (hB i j).1) t ht
  have hI := conj_close hui hc hB0 (fun i j => (hB i j).2) t ht
  have hinv : (diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹)⁻¹ =
      diagT k (Fin n) t * u⁻¹ * (diagT k (Fin n) t)⁻¹ := by group
  rw [SetLike.mem_coe, GroundTheory.Automorphic.GLnLocal.mem_congruenceSubgroup_iff,
    GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff, hinv]
  refine ⟨⟨fun i j => (Valuation.mem_integer_iff _ _).2 (hA i j).2,
    fun i j => (Valuation.mem_integer_iff _ _).2 (hI i j).2⟩, fun i j => (hA i j).1⟩

end UpperTheory.Gal.Join.KernelKilling

theorem UpperTheory.Gal.Join.kerKill :
    UpperTheory.Gal.Join.KerKill := by
  intro k _ _ _ _ n V _ _ π K hK e he v hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨u, x, rfl⟩ := hw
    obtain ⟨r, hr, h⟩ := UpperTheory.Gal.Join.KernelKilling.conj_mem hK.co.2 u.2
    refine ⟨r, hr, fun t ht => ?_⟩
    have hk := he.inv _ (h t ht) (π (diagT k (Fin n) t) x)
    have hc : π (diagT k (Fin n) t * (u : GL (Fin n) k) * (diagT k (Fin n) t)⁻¹)
        (π (diagT k (Fin n) t) x) = π (diagT k (Fin n) t) (π (u : GL (Fin n) k) x) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    rw [hc] at hk
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hk, sub_self]
  | zero => exact ⟨1, one_ne_zero, fun t _ => by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨r₁, h₁, ha⟩ := ha
    obtain ⟨r₂, h₂, hb⟩ := hb
    refine ⟨min r₁ r₂, ?_, fun t ht => ?_⟩
    · rcases min_choice r₁ r₂ with h | h <;> rw [h] <;> assumption
    · rw [map_add (f := _), map_add (f := _),
        ha t fun i j hij => (ht i j hij).trans (mul_le_mul' (min_le_left _ _) le_rfl),
        hb t fun i j hij => (ht i j hij).trans (mul_le_mul' (min_le_right _ _) le_rfl), add_zero]
  | smul c a _ ha =>
    obtain ⟨r, hr, ha⟩ := ha
    exact ⟨r, hr, fun t ht => by rw [map_smul, map_smul, ha t ht, smul_zero]⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuotAlt
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.traceQuot :
    UpperTheory.Gal.Join.TraceQuot := by
  intro V W _ _ _ _ S _ B p T hB hBT hnil
  have hTP : ∀ y ∈ Submodule.map p S, T y ∈ Submodule.map p S := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨B v, hB v, hBT v hv⟩
  have hBS : ∀ v ∈ S, B v ∈ S := fun v _ => hB v
  have hRS : LinearMap.range B ≤ S := by
    rintro _ ⟨v, rfl⟩
    exact hB v
  haveI : FiniteDimensional ℂ (LinearMap.range B) := Submodule.finiteDimensional_of_le hRS
  refine ⟨inferInstance, ?_⟩
  unfold trIn
  rw [dite_eq_left hTP]
  have h1 : LinearMap.trace ℂ (LinearMap.range B) (B.restrict (fun x _ => (⟨x, rfl⟩ : B x ∈ LinearMap.range B)))
      = LinearMap.trace ℂ S (B.restrict hBS) := by
    have key := LinearMap.trace_restrict_eq_of_forall_mem ((LinearMap.range B).comap S.subtype)
      (B.restrict hBS) (fun x => show B x ∈ LinearMap.range B from ⟨x, rfl⟩)
    rw [← key, ← LinearMap.trace_conj' _ (Submodule.comapSubtypeEquivOfLe hRS)]
    congr 1
  rw [h1]
  set q : S →ₗ[ℂ] Submodule.map p S := p.submoduleMap S with hqdef
  have hq : Function.Surjective q := p.submoduleMap_surjective S
  haveI : FiniteDimensional ℂ (Submodule.map p S) := Module.Finite.of_surjective q hq
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  set BS := B.restrict hBS with hBSdef
  set TP := T.restrict hTP with hTPdef
  have hint : q ∘ₗ BS = TP ∘ₗ q := by
    ext x
    exact hBT x.1 x.2
  have hT : TP = q ∘ₗ (BS ∘ₗ s) := by
    rw [← LinearMap.comp_assoc, hint, LinearMap.comp_assoc, hs, LinearMap.comp_id]
  rw [hT, LinearMap.trace_comp_comm']
  set E : S →ₗ[ℂ] S := LinearMap.id - s ∘ₗ q with hEdef
  have hsplit : BS = (BS ∘ₗ s) ∘ₗ q + BS ∘ₗ E := by
    ext x
    simp [hEdef]
  have hqs : ∀ y, q (s y) = y := fun y => LinearMap.congr_fun hs y
  have hqB : ∀ y : S, q y = 0 → q (BS y) = 0 := by
    intro y hy
    have := LinearMap.congr_fun hint y
    simp only [LinearMap.comp_apply] at this
    rw [this, hy, map_zero]
  have hzero : LinearMap.trace ℂ S (BS ∘ₗ E) = 0 := by
    rw [LinearMap.trace_comp_comm']
    have hK : ∀ x, (E ∘ₗ BS) x ∈ LinearMap.ker q := by
      intro x
      simp [hEdef, hqs]
    rw [← LinearMap.trace_restrict_eq_of_forall_mem _ _ hK]
    set f := (E ∘ₗ BS).restrict (fun x _ => hK x) with hfdef
    apply IsNilpotent.eq_zero
    apply LinearMap.isNilpotent_trace_of_isNilpotent
    rw [Module.End.isNilpotent_iff_of_finite]
    intro k
    have hk0 : q k.1 = 0 := k.2
    have hpk : p k.1.1 = 0 := congrArg Subtype.val hk0
    obtain ⟨m, hm⟩ := hnil k.1.1 k.1.2 hpk
    refine ⟨m, ?_⟩
    have step : ∀ n : ℕ, ((f ^ n) k).1.1 = (B ^ n) k.1.1 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
        have hy : q ((f ^ n) k).1 = 0 := ((f ^ n) k).2
        show ((E (BS ((f ^ n) k).1)) : V) = B ((f ^ n) k).1.1
        rw [hEdef, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hqB _ hy, map_zero, sub_zero]
        rfl
    apply Subtype.ext
    apply Subtype.ext
    rw [step]
    simpa using hm
  conv_lhs => rw [hsplit]
  rw [map_add (f := _), hzero, add_zero]
end

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) k) V}

private def pw (σ : k ≃+* k) (t : Fin n → kˣ) : ℕ → Fin n → kˣ
  | 0 => 1
  | m + 1 => t * fun i => Units.map (σ : k →* k) (pw σ t m i)

private theorem val_pw {σ : k ≃+* k} (h : Isom σ) (t : Fin n → kˣ) (i : Fin n) :
    ∀ m, valuation k (pw σ t m i : k) = valuation k (t i : k) ^ m
  | 0 => by simp [pw]
  | m + 1 => by
    have := h (pw σ t m i)
    simp only [pw, Pi.mul_apply, Units.val_mul, map_mul, Units.coe_map, MonoidHom.coe_coe, this, val_pw h t i m, pow_succ']

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem sg_diag (σ : k ≃+* k) (s : Fin n → kˣ) :
    Loc.sg σ (diagT k (Fin n) s) = diagT k (Fin n) fun i => Units.map (σ : k →* k) (s i) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [sg_val, val_diagT, val_diagT, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

private theorem small {t : Fin n → kˣ} (ht : Strict t) {r : ValueGroupWithZero k} (hr : r ≠ 0) :
    ∀ᶠ m : ℕ in atTop, ∀ i j, i < j → valuation k (t i : k) ^ m ≤ r * valuation k (t j : k) ^ m := by
  simp only [eventually_all]
  intro i j hij
  have h0 : valuation k (t j : k) ≠ 0 := by simp
  have h1 : valuation k (t i : k) / valuation k (t j : k) < 1 := (div_lt_one₀ (zero_lt_iff.2 h0)).2 (ht i j hij)
  obtain ⟨M, hM⟩ := exists_pow_lt₀ h1 (Units.mk0 r hr)
  filter_upwards [eventually_ge_atTop M] with m hm
  have h2 : (valuation k (t i : k) / valuation k (t j : k)) ^ m ≤ r := (pow_le_pow_right_of_le_one' h1.le hm).trans hM.le
  rwa [div_pow, div_le_iff₀ (zero_lt_iff.2 (pow_ne_zero _ h0))] at h2

private theorem unif {K : Subgroup (GL (Fin n) k)} (hK : IwLev K) {e : V →ₗ[ℂ] V} (he : IsAvg π K e) (Z : Submodule ℂ V)
    [FiniteDimensional ℂ Z] (hZ : Z ≤ twKer π (unipB k (Fin n)) 1) {t : Fin n → kˣ} (ht : Strict t) {σ : k ≃+* k} (h : Isom σ) :
    ∃ m, 0 < m ∧ ∀ v ∈ Z, e (π (diagT k (Fin n) (pw σ t m)) v) = 0 := by
  obtain ⟨s, hs⟩ := (Submodule.fg_top Z).1 (Module.finite_def.1 inferInstance)
  have : ∀ᶠ m : ℕ in atTop, ∀ v ∈ s, e (π (diagT k (Fin n) (pw σ t m)) v) = 0 := by
    rw [eventually_all_finset]
    intro v hv
    obtain ⟨r, hr, hk⟩ := kerKill k n V π K hK e he v (hZ (hs ▸ Submodule.subset_span hv))
    filter_upwards [small ht hr] with m hm
    exact hk _ fun i j hij => by rw [val_pw h, val_pw h]; exact hm i j hij
  obtain ⟨m, hm, h0⟩ := (this.and (eventually_gt_atTop 0)).exists
  refine ⟨m, h0, fun v hv => ?_⟩
  have : Z ≤ LinearMap.ker (e ∘ₗ π (diagT k (Fin n) (pw σ t m))) := hs ▸ Submodule.span_le.2 hm
  exact this hv

end SlopeTestRemainingChoices

private theorem trIn_smul' {X : Type} [AddCommGroup X] [Module ℂ X] {P : Submodule ℂ X} {T : X →ₗ[ℂ] X}
    (h : ∀ y ∈ P, T y ∈ P) (c : ℂ) : trIn P (c • T) = c * trIn P T := by
  have h' : ∀ y ∈ P, (c • T) y ∈ P := fun y hy => P.smul_mem c (h y hy)
  rw [trIn, trIn, dite_eq_left h, dite_eq_left h', ← smul_eq_mul, ← map_smul]
  rfl

theorem UpperTheory.Gal.Join.casTrace :
    UpperTheory.Gal.Join.CasTrace := by
  intro k _ _ _ _ n V _ _ π ha _ _ μ _ K hK σ A hA hσ hst t ht
  have hd : Dom t := fun i j h => (ht i j h).le
  obtain ⟨e, he, hc⟩ := avgEx _ V π ha.1 K hK.co
  have hAe : ∀ v, A (e v) = e (A v) := hc (Loc.sg σ) A hA (fun g hg => (hst g).2 hg) fun g hg => by
    have e1 : Loc.sg σ (Loc.sg σ.symm g) = g := Units.ext (Matrix.ext fun i j => σ.apply_symm_apply _)
    exact ⟨Loc.sg σ.symm g, (hst _).1 (by rwa [e1]), e1⟩
  have hfix : ∀ v ∈ fixed π K, A v ∈ fixed π K := fun v hv => by rw [← he.fix v hv, hAe]; exact he.mem _
  haveI : μ.IsMulRightInvariant := GroundTheory.Automorphic.Measures.isMulRightInvariant_GL k n μ
  haveI : FiniteDimensional ℂ (fixed π K) := ha.2 K hK.co.2 hK.co.1
  refine ⟨_, dcosOp _ V μ π ha.1 K hK.co e he (diagT k (Fin n) t), ?_⟩
  obtain ⟨-, s1, s2⟩ := imStab k n V π ha K hK
  change HasFinTrace (((μ.real (dcos K t) : ℂ) • (e ∘ₗ π (diagT k (Fin n) t) ∘ₗ e)) ∘ₗ A) _
  have hq : ((Real.sqrt (deltaB t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (deltaB_pos _)).ne'
  have key := traceQuot V _ (fixed π K) (((μ.real (dcos K t) : ℂ) • (e ∘ₗ π (diagT k (Fin n) t) ∘ₗ e)) ∘ₗ A)
    (twKer π (unipB k (Fin n)) 1).mkQ
    (((μ.real (K : Set (GL (Fin n) k)) : ℂ) * ((Real.sqrt (deltaB t) : ℝ) : ℂ)⁻¹) • (jacB π t ∘ₗ jacA hA))
    (fun v => Submodule.smul_mem _ _ (he.mem _)) (fun v hv => ?_) fun v hv h0 => ?_
  · rwa [trIn_smul' (P := (fixed π K).map (twKer π (unipB k (Fin n)) 1).mkQ) (T := jacB π t ∘ₗ jacA hA)
      fun y hy => s1 t _ (s2 σ A hA hst y hy)] at key
  · simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
    rw [he.fix _ (hfix v hv), (heckeMul k n V π K hK e he t hd _ (hfix v hv)).2, jacNorm k n V π, smul_smul,
      (dcosVol k n μ K hK t hd).2]
    congr 1
    have h2 : ((deltaB t : ℝ) : ℂ) = ((Real.sqrt (deltaB t) : ℝ) : ℂ) * ((Real.sqrt (deltaB t) : ℝ) : ℂ) := by
      exact_mod_cast (Real.mul_self_sqrt (deltaB_pos t).le).symm
    push_cast
    rw [h2]
    field_simp
  · obtain ⟨m, -, hm⟩ := unif hK he (fixed π K ⊓ twKer π (unipB k (Fin n)) 1) inf_le_right ht hσ
    have hZ : ∀ j : ℕ, (A ^ j) v ∈ fixed π K ⊓ twKer π (unipB k (Fin n)) 1 := fun j => by
      induction j with
      | zero => exact ⟨hv, (Submodule.Quotient.mk_eq_zero _).1 h0⟩
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply]
        refine ⟨hfix _ ih.1, (Submodule.Quotient.mk_eq_zero _).1 ?_⟩
        rw [← jacA_mk hA, (Submodule.Quotient.mk_eq_zero _).2 ih.2, map_zero]
    have hP : ∀ j : ℕ, ((((μ.real (dcos K t) : ℂ) • (e ∘ₗ π (diagT k (Fin n) t) ∘ₗ e)) ∘ₗ A) ^ j) v =
        (μ.real (dcos K t) : ℂ) ^ j • e (π (diagT k (Fin n) (pw σ t j)) ((A ^ j) v)) := fun j => by
      induction j with
      | zero => simp [pw, he.fix v hv]
      | succ j ih =>
        have hdj : Dom fun i => Units.map (σ : k →* k) (pw σ t j i) := fun a b hab => by
          have h1 := hσ (pw σ t j a)
          have h2 := hσ (pw σ t j b)
          simp only [Units.coe_map, MonoidHom.coe_coe, h1, h2, val_pw hσ]
          exact pow_le_pow_left' (hd a b hab) j
        rw [pow_succ', Module.End.mul_apply, ih, map_smul]
        simp only [LinearMap.comp_apply, LinearMap.smul_apply]
        rw [hAe, he.fix _ (he.mem _), hA, sg_diag, (heckeMul k n V π K hK e he _ hdj _ (hfix _ (hZ j).1)).1 t hd, smul_smul,
          ← pow_succ, pow_succ' A]
        rfl
    exact ⟨m, by rw [hP, hm _ (hZ m), smul_zero]⟩
end

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

private theorem semi_refl {k V : Type} [Field k] {n : ℕ} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) :
    Semi (RingEquiv.refl k) π LinearMap.id := fun _ _ => rfl

private theorem jacA_refl {k V : Type} [Field k] {n : ℕ} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) :
    jacA (semi_refl π) = LinearMap.id := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rfl

set_option maxHeartbeats 1600000 in
theorem UpperTheory.Gal.Join.coreId (h1 : VarEx) (h2 : VarTrace) (h3 : ElemPairJ) : CoreId := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn v w hns σw N hs hN π P hP hW τ τ' hτ hτ'
  obtain ⟨s, hs', hI⟩ := h1 F E σ hσ hp n hn P hP v w hns
  obtain ⟨I, hI⟩ := hI τ' hτ'
  have e : ∀ g, s g = Loc.sg σw g := fun g => by
    obtain ⟨x, rfl⟩ : ∃ x, GM.cmp w x = g := by
      obtain ⟨e, he⟩ := (cmpIso F E n v w fun u => (UpperTheory.ConvolutionTheory.T.places F E hp).2.2.2.1 v hns w u).1
      exact ⟨e.symm g, by rw [← he, e.apply_symm_apply]⟩
    exact (hs' x).symm.trans (hs x)
  have hA : Semi σw τ'.ρ (I : τ'.V →ₗ[ℂ] τ'.V) := fun g x => by rw [← e]; exact hI g x
  have hnt : Nontrivial τ'.V := GroundTheory.Automorphic.RestrictedTensor.nontrivial_of_isIrreducible τ'.irred
  refine ⟨I, hA, fun h0 => ?_, fun U' U hU' hU => ?_⟩
  · obtain ⟨x, hx⟩ := exists_ne (0 : τ'.V)
    exact hx (I.injective ((LinearMap.congr_fun h0 x).trans (map_zero I).symm))
  obtain ⟨K', hK', K, hK, l', l, hst, c₁, t₀, hc₁, ht₀, hm⟩ := h3 F E σ hσ hp n hn v w hns σw N hs hN U' U hU' hU
  borelize (Gw n v) (Gw n w.1)
  obtain ⟨c, hc, hT⟩ := h2 F E σ hσ hp n hn π P hP hW v w hns Measure.haar Measure.haar inferInstance inferInstance τ τ' hτ hτ'
    (Loc.sg σw) I hs hA
  have a := PositivityTheory.Exh.irreducibleAdmissibleGL _ n τ.V τ.ρ τ.smooth τ.irred
  have a' := PositivityTheory.Exh.irreducibleAdmissibleGL _ n τ'.V τ'.ρ τ'.smooth τ'.irred
  have p : (Measure.haar : Measure (Gw n v)).real (K : Set (Gw n v)) ≠ 0 :=
    (ENNReal.toReal_pos (l.co.2.measure_pos _ ⟨1, K.one_mem⟩).ne' l.co.1.measure_lt_top.ne).ne'
  have p' : (Measure.haar : Measure (Gw n w.1)).real (K' : Set (Gw n w.1)) ≠ 0 :=
    (ENNReal.toReal_pos (l'.co.2.measure_pos _ ⟨1, K'.one_mem⟩).ne' l'.co.1.measure_lt_top.ne).ne'
  refine ⟨K', hK', K, hK, l', l, hst, c * c₁ * ((Measure.haar : Measure (Gw n v)).real (K : Set (Gw n v)) : ℂ) /
    ((Measure.haar : Measure (Gw n w.1)).real (K' : Set (Gw n w.1)) : ℂ), t₀,
    div_ne_zero (mul_ne_zero (mul_ne_zero hc hc₁) (by exact_mod_cast p)) (by exact_mod_cast p'), fun t ht => ?_⟩
  obtain ⟨n1, n2, n3⟩ := (normDom _ _ _ σw _ N hN).2 n (t₀ * t)
  have st : Strict (t₀ * t) := ((normDom _ _ _ σw _ N hN).2 n t₀).2.2 t ht₀ ht
  obtain ⟨B, hB, hBt⟩ := casTrace _ n _ τ.ρ a Measure.haar K l (RingEquiv.refl _) _ (semi_refl τ.ρ) (fun _ => rfl)
    (fun _ => Iff.rfl) _ (n1 st)
  obtain ⟨B', hB', hBt'⟩ := casTrace _ n _ τ'.ρ a' Measure.haar K' l' σw _ hA hN.cyc.isom hst _ st
  rw [jacA_refl, LinearMap.comp_id, LinearMap.comp_id] at hBt
  obtain ⟨B'', hB'', hBt''⟩ := hT _ _ c₁ _ (dcosVol _ n Measure.haar K' l' _ fun i j h => (st i j h).le).1
    (dcosVol _ n Measure.haar K l _ fun i j h => (n1 st i j h).le).1 (hm t ht).1
    (fun g hg => (hm t ht).2 (Set.mem_of_indicator_ne_zero hg)) ⟨B, hB, hBt⟩
  obtain rfl := hB'.unique hB''
  have h4 := hBt'.2.symm.trans hBt''.2
  rw [n2] at h4
  have q : ((Real.sqrt (deltaB (t₀ * t)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (deltaB_pos _)).ne'
  have p2 : (((Measure.haar : Measure (Gw n w.1)).real (K' : Set (Gw n w.1)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast p'
  field_simp at h4 ⊢
  linear_combination h4

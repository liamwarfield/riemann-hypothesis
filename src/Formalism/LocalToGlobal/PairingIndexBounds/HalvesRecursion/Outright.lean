module

public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.MemLamOfIff
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.SplitElementExistsHolds
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep

@[expose] public section

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.ModelXiAll
namespace Formalism.L2.PairingIndexBounds.Rec

theorem modelXi_all (hH : HalvesRec) (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.modelXi D := modelXi_of hH D (discrNZ D)

end Formalism.L2.PairingIndexBounds.Rec
end

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.MovesComposeOfParts
noncomputable section

namespace Formalism.L2.PairingIndexBounds.Rec

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Mv Formalism.L2.Th1.H Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem eqOffSplit_trans (D : D7) {N : ℕ} {L₁ L₂ L₃ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (h₁ : EqOffSplit D L₁ L₂) (h₂ : EqOffSplit D L₂ L₃) : EqOffSplit D L₁ L₃ := by
  obtain ⟨a, ha0, hsa, ha1, ha2⟩ := h₁
  obtain ⟨b, hb0, hsb, hb1, hb2⟩ := h₂
  refine ⟨b * a, mul_ne_zero hb0 ha0, fun Q hQ => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rcases Q.isPrime.mem_or_mem hQ with h | h
    · exact hsb Q h
    · exact hsa Q h
  · rw [mul_smul]; exact hb1 _ (ha1 x hx)
  · rw [mul_comm, mul_smul]; exact ha2 _ (hb2 x hx)

theorem eqOffSplit_dvd (D : D7) {N : ℕ} {L L₀ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {a w : 𝓞 D.host.E}
    (hL : (∀ x ∈ L, a • x ∈ L₀) ∧ ∀ x ∈ L₀, a • x ∈ L) (hw : a ∣ w) :
    (∀ x ∈ L, w • x ∈ L₀) ∧ ∀ x ∈ L₀, w • x ∈ L := by
  obtain ⟨r, rfl⟩ := hw
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [mul_comm, mul_smul]; exact L₀.smul_mem r (hL.1 x hx)
  · rw [mul_comm, mul_smul]; exact L.smul_mem r (hL.2 x hx)

theorem good_rec (hA : HfIntRec) (hB : SelfDualRec) (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0) (N N' : ℕ)
    (L₀ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₀' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hAdm : admitted D N N' L₀ L₀') (u : D.host.E) (hu1 : u * D.host.conj u = 1) :
    IsSemiChar (HfS D (tor0 D cc δ) N N') ((ccE D cc • sMod u (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N'))
        (al D (tor0 D cc δ)) ∧
    IsSemiChar (HfS D (tor0 D cc δ) N N') ((ccE D cc • sMod u⁻¹ (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N'))
        (al D (tor0 D cc δ)) ∧
    ∀ (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      admitted D N N' L L' →
      (∀ y ∈ ccE D cc • YYl D L L', ∃ a ∈ ccE D cc • YYl D L L' ⊓ ccE D cc • sMod u (YYl D L₀ L₀'),
        ∃ b ∈ ccE D cc • YYl D L L' ⊓ ccE D cc • sMod u⁻¹ (YYl D L₀ L₀'), y = a + b) →
      (∀ a ∈ ccE D cc • sMod u (YYl D L₀ L₀'), ∀ b ∈ ccE D cc • sMod u⁻¹ (YYl D L₀ L₀'),
        a + b ∈ ccE D cc • YYl D L L' → a ∈ ccE D cc • YYl D L L') →
      GoodLat (HfS D (tor0 D cc δ) N N') (al D (tor0 D cc δ))
        ((ccE D cc • sMod u (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N'))
        ((ccE D cc • sMod u⁻¹ (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N')) (La D (tor0 D cc δ) L L') := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  have hu1' : u⁻¹ * D.host.conj u⁻¹ = 1 := by rw [map_inv₀, ← mul_inv, hu1, inv_one]
  have hinj : Function.Injective (Phi D cc δ N N') := phi_injective_holds D cc δ N N' hδ0
  have hAdmA := admissible_unipotent_holds D N N' L₀ L₀' u hu1 hAdm
  have hAdmB := admissible_unipotent_holds D N N' L₀ L₀' u⁻¹ hu1' hAdm
  have hLaeq : ∀ (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      La D (tor0 D cc δ) L L' = (ccE D cc • YYl D L L').toAddSubgroup.map (Phi D cc δ N N') := fun L L' => by
    rw [lattice_equality_map_holds, multiplicity_equality_holds]
  have hAeq : La D (tor0 D cc δ) L₀ (sLat D u L₀') =
      (ccE D cc • sMod u (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N') := by
    rw [hLaeq, unipotent_pairing_holds D N N' L₀ L₀' u hu0]
  have hBeq : La D (tor0 D cc δ) L₀ (sLat D u⁻¹ L₀') =
      (ccE D cc • sMod u⁻¹ (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N') := by
    rw [hLaeq, unipotent_pairing_holds D N N' L₀ L₀' u⁻¹ (inv_ne_zero hu0)]
  obtain ⟨hHerm, -, -, -, hSC⟩ := local_global_comparison_holds D (tor0 D cc δ) N N'
  have hIA := hA D cc hcc δ hδ hδ0 N N' L₀ _ hAdmA
  have hIB := hA D cc hcc δ hδ hδ0 N N' L₀ _ hAdmB
  have intOf : ∀ Λ : AddSubgroup (VC D N N'), IO.HfInt (tor0 D cc δ) Λ →
      ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ m : ℤ, altE (HfS D (tor0 D cc δ) N N') x y = m := by
    intro Λ hI x hx y hy
    obtain ⟨a, b, -, hab⟩ := hI x hx y hy
    exact ⟨b, by simp only [altE, HfS_apply, hab]; simp⟩
  refine ⟨hAeq ▸ hSC _ hIA, hBeq ▸ hSC _ hIB, ?_⟩
  intro L L' hLL c1 c2
  have hΛ := hLaeq L L'
  have hsum : La D (tor0 D cc δ) L L' ≤
      (La D (tor0 D cc δ) L L' ⊓ (ccE D cc • sMod u (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N')) ⊔
      (La D (tor0 D cc δ) L L' ⊓ (ccE D cc • sMod u⁻¹ (YYl D L₀ L₀')).toAddSubgroup.map (Phi D cc δ N N')) := by
    rw [hΛ]
    intro z hz
    obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.1 hz
    obtain ⟨a, ha, b, hb, rfl⟩ := c1 y hy
    rw [map_add (f := _)]
    exact AddSubgroup.add_mem_sup
      ⟨AddSubgroup.mem_map_of_mem _ (Submodule.mem_inf.1 ha).1, AddSubgroup.mem_map_of_mem _ (Submodule.mem_inf.1 ha).2⟩
      ⟨AddSubgroup.mem_map_of_mem _ (Submodule.mem_inf.1 hb).1, AddSubgroup.mem_map_of_mem _ (Submodule.mem_inf.1 hb).2⟩
  have hsd : ∀ v : VC D N N', (∀ y ∈ La D (tor0 D cc δ) L L', ∃ b : ℤ, altE (HfS D (tor0 D cc δ) N N') v y = b) →
      v ∈ La D (tor0 D cc δ) L L' :=
    fun v hv => hB D cc hcc δ hδ hδ0 N N' L L' hLL v hv
  obtain ⟨d1, d2⟩ := good_duality_holds (VC D N N') (HfS D (tor0 D cc δ) N N') _ _ _ hHerm (intOf _ (hAeq ▸ hIA))
    (intOf _ (hBeq ▸ hIB)) hsum hsd
  refine ⟨hSC _ (hA D cc hcc δ hδ hδ0 N N' L L' hLL), hsum, ?_, d1, d2⟩
  intro a ha b hb hab
  obtain ⟨a', ha', rfl⟩ := AddSubgroup.mem_map.1 ha
  obtain ⟨b', hb', rfl⟩ := AddSubgroup.mem_map.1 hb
  rw [hΛ] at hab ⊢
  rw [← map_add (f := _), AddSubgroup.mem_map_iff_mem hinj] at hab
  exact AddSubgroup.mem_map_of_mem _ (c2 a' ha' b' hb' hab)

theorem movesCompose_of_parts (hA : HfIntRec) (hB : SelfDualRec) (D : D7) : movesCompose D := by
  intro cc δ hcc hδ N N' L₁ L₂ L₃ L₁' L₂' L₃' h1 h2 h3 e12 e23 e12' e23' th hth
  classical
  have hδ0 : δ ≠ 0 := by
    intro h0
    apply discrNZ D cc hcc
    rw [← hδ, h0]
    norm_num
  have e13 := eqOffSplit_trans D e12 e23
  have e13' := eqOffSplit_trans D e12' e23'
  obtain ⟨a2, ha2, hs2, hb2⟩ := e12
  obtain ⟨a3, ha3, hs3, hb3⟩ := e13
  obtain ⟨a2', ha2', hs2', hb2'⟩ := e12'
  obtain ⟨a3', ha3', hs3', hb3'⟩ := e13'
  set a := a2 * a3 * a2' * a3' with ha
  have ha0 : a ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero ha2 ha3) ha2') ha3'
  have hsa : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), a ∈ Q.asIdeal → SplitP D Q := by
    intro Q hQ
    rcases Q.isPrime.mem_or_mem hQ with h | h
    · rcases Q.isPrime.mem_or_mem h with h | h
      · rcases Q.isPrime.mem_or_mem h with h | h
        · exact hs2 Q h
        · exact hs3 Q h
      · exact hs2' Q h
    · exact hs3' Q h
  obtain ⟨π, hπ0, hcop, j, hj⟩ := split_element_exists_holds D a ha0 hsa
  set w := (π * cO D π) ^ j with hw
  have d2 : a2 ∣ w := (Dvd.intro (a3 * a2' * a3') (by rw [ha]; ring)).trans hj
  have d3 : a3 ∣ w := (Dvd.intro (a2 * a2' * a3') (by rw [ha]; ring)).trans hj
  have d2' : a2' ∣ w := (Dvd.intro (a2 * a3 * a3') (by rw [ha]; ring)).trans hj
  have d3' : a3' ∣ w := (Dvd.intro (a2 * a3 * a2') (by rw [ha]; ring)).trans hj

  have B2 := eqOffSplit_dvd D (L := L₂) (L₀ := L₁) ⟨hb2.2, hb2.1⟩ d2
  have B3 := eqOffSplit_dvd D (L := L₃) (L₀ := L₁) ⟨hb3.2, hb3.1⟩ d3
  have B2' := eqOffSplit_dvd D (L := L₂') (L₀ := L₁') ⟨hb2'.2, hb2'.1⟩ d2'
  have B3' := eqOffSplit_dvd D (L := L₃') (L₀ := L₁') ⟨hb3'.2, hb3'.1⟩ d3'
  let Yf : Fin 3 → Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E) := ![YYl D L₁ L₁', YYl D L₂ L₂', YYl D L₃ L₃']
  have hww : (π * cO D π) ^ (j + j) = w * w := by rw [pow_add]
  have hbd1 : ∀ i, ∀ y ∈ YYl D L₁ L₁', (π * cO D π) ^ (j + j) • y ∈ Yf i := by
    intro i y hy
    rw [hww]
    fin_cases i
    · exact Submodule.smul_mem _ _ hy
    · exact pairing_bound_holds D w N N' L₂ L₁ L₂' L₁' B2.1 B2'.2 y hy
    · exact pairing_bound_holds D w N N' L₃ L₁ L₃' L₁' B3.1 B3'.2 y hy
  have hbd2 : ∀ i, ∀ y ∈ Yf i, (π * cO D π) ^ (j + j) • y ∈ YYl D L₁ L₁' := by
    intro i y hy
    rw [hww]
    fin_cases i
    · exact Submodule.smul_mem _ _ hy
    · exact pairing_bound_holds D w N N' L₁ L₂ L₁' L₂' B2.2 B2'.1 y hy
    · exact pairing_bound_holds D w N N' L₁ L₃ L₁' L₃' B3.2 B3'.1 y hy
  have hπb0 : cO D π ≠ 0 := by
    intro h0; apply hπ0; rw [← cO_cO D π, h0, map_zero]
  have HG := generic_splitting_holds (𝓞 D.host.E) D.host.E (Fin N') (Fin N) (ccE D cc) π (cO D π) (j + j) (Fin 3)
    (YYl D L₁ L₁') Yf hπ0 hπb0 hcop hbd1 hbd2
  have hπE0 : algebraMap (𝓞 D.host.E) D.host.E π ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]; exact hπ0
  have hπbE0 : algebraMap (𝓞 D.host.E) D.host.E (cO D π) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]; exact hπb0
  set u : D.host.E := (algebraMap (𝓞 D.host.E) D.host.E (cO D π) / algebraMap (𝓞 D.host.E) D.host.E π) ^ (j + j)
    with hu
  have hc1 : D.host.conj (algebraMap (𝓞 D.host.E) D.host.E (cO D π)) = algebraMap (𝓞 D.host.E) D.host.E π :=
    conj_conj' D _
  have hc2 : D.host.conj (algebraMap (𝓞 D.host.E) D.host.E π) = algebraMap (𝓞 D.host.E) D.host.E (cO D π) := rfl
  have hu1 : u * D.host.conj u = 1 := by
    rw [hu, map_pow, map_div₀, hc1, hc2, ← mul_pow]
    have e : algebraMap (𝓞 D.host.E) D.host.E (cO D π) / algebraMap (𝓞 D.host.E) D.host.E π *
        (algebraMap (𝓞 D.host.E) D.host.E π / algebraMap (𝓞 D.host.E) D.host.E (cO D π)) = 1 := by
      field_simp
    rw [e, one_pow]
  obtain ⟨sA, sB, good⟩ := good_rec hA hB D cc δ hcc hδ hδ0 N N' L₁ L₁' h1 u hu1
  obtain ⟨c1₁, c2₁⟩ := HG 0
  obtain ⟨c1₂, c2₂⟩ := HG 1
  obtain ⟨c1₃, c2₃⟩ := HG 2
  have g1 := good L₁ L₁' h1 c1₁ c2₁
  have g2 := good L₂ L₂' h2 c1₂ c2₂
  have g3 := good L₃ L₃' h3 c1₃ c2₃
  obtain ⟨hHerm, -, hIop, hTh, -⟩ := local_global_comparison_holds D (tor0 D cc δ) N N'
  have fin : ∀ {La La' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {Lb Lb' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)},
      admitted D N N' La Lb → admitted D N N' La' Lb' →
      relIdx (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) La Lb) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) La' Lb') ≠ 0 := by
    intro La La' Lb Lb' hx hy
    have := IO.La_index_finite cc hcc δ La La' Lb Lb' hx hy
    exact AddSubgroup.index_ne_zero_of_finite
  have key := movesComposeU (VC D N N') (HfS D (tor0 D cc δ) N N') (al D (tor0 D cc δ)) _ _ _ _ _ hHerm sA sB g1 g2 g3
    (fin h1 h2) (fin h2 h3) (fin h1 h3) th (hTh _ hth)
  rw [hIop, hIop, hIop]
  exact key

end Formalism.L2.PairingIndexBounds.Rec
end
end

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.ModelXiOfParts
section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.AdicBoxOpenness.ClosureCharacterHolds
noncomputable section
open scoped BigOperators
open IsDedekindDomain Topology Filter

namespace Formalism.L2.PairingIndexBounds.Rec

theorem denseInt_adic {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) (w : v.adicCompletion K) (hw : Valued.v w ≤ 1) :
    w ∈ closure (Set.range fun r : R => algebraMap K (v.adicCompletion K) (algebraMap R K r)) := by
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hU
  set g := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hgdef
  have hg : g ≠ 0 := (map_ne_zero _).mpr γ.ne_zero
  have hV : {y : v.adicCompletion K | Valued.v (y - w) < g} ∈ 𝓝 w := by
    rw [Valued.mem_nhds]
    exact ⟨γ, fun y hy => by
      simp only [Set.mem_ofPred_eq] at hy ⊢
      rwa [Valuation.restrict_lt_iff_lt_embedding] at hy⟩
  have hO : ((v.adicCompletionIntegers K : ValuationSubring _) : Set (v.adicCompletion K)) ∈ 𝓝 w :=
    (Valued.isOpen_valuationSubring (v.adicCompletion K)).mem_nhds hw
  obtain ⟨_, ⟨k, rfl⟩, hk1, hk2⟩ := Dense.inter_nhds_nonempty (HeightOneSpectrum.denseRange_algebraMap K v) (inter_mem hV hO)
  have hkv : v.valuation K k ≤ 1 := by
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
    rw [← this]; exact hk2
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hkv (Units.mk0 g hg)
  refine ⟨algebraMap K (v.adicCompletion K) (algebraMap R K a), hγ ?_, a, rfl⟩
  simp only [Set.mem_ofPred_eq]
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hgdef]
  have e : algebraMap K (v.adicCompletion K) (algebraMap R K a) - w =
      algebraMap K (v.adicCompletion K) (algebraMap R K a - k) + (algebraMap K (v.adicCompletion K) k - w) := by
    rw [map_sub]; ring
  rw [e]
  refine Valuation.map_add_lt _ ?_ hk1
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap R K a - k)
  rw [show algebraMap K (v.adicCompletion K) (algebraMap R K a - k) = ((algebraMap R K a - k : K) : v.adicCompletion K) from rfl, this]
  simpa using ha

theorem valAlg_adic {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

theorem isOpen_boxW_adic {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) (m n : Type) [Fintype m] [Fintype n] (t : v.adicCompletion K) :
    IsOpen {ζ : Matrix m n (v.adicCompletion K) | ∀ i j, t * ζ i j ∈ v.adicCompletionIntegers K} := by
  have e : {ζ : Matrix m n (v.adicCompletion K) | ∀ i j, t * ζ i j ∈ v.adicCompletionIntegers K} =
      ⋂ i, ⋂ j, (fun ζ : Matrix m n (v.adicCompletion K) => t * ζ i j) ⁻¹'
        ((v.adicCompletionIntegers K : ValuationSubring _) : Set (v.adicCompletion K)) := by
    ext ζ; simp [Set.mem_iInter]
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage
      (continuous_const.mul (continuous_id.matrix_elem i j))

theorem boxW_sub_closure {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) {m n : Type} (M : Set (Matrix m n K)) (d : R) (hd : d ≠ 0)
    (hM : LowB d M) :
    {ζ : Matrix m n (v.adicCompletion K) |
        ∀ i j, (algebraMap K (v.adicCompletion K) (algebraMap R K d))⁻¹ * ζ i j ∈ v.adicCompletionIntegers K} ⊆
      closure (matI v '' M) := by
  intro ζ hζ
  set e := algebraMap K (v.adicCompletion K) (algebraMap R K d) with he
  have hne : e ≠ 0 := (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd)
  let T : Set (v.adicCompletion K) := Set.range fun r : R => e * algebraMap K (v.adicCompletion K) (algebraMap R K r)
  have hT : ∀ i j, ζ i j ∈ closure T := by
    intro i j
    have h1 := denseInt_adic v _ (hζ i j)
    have h2 : ζ i j = e * (e⁻¹ * ζ i j) := by rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rw [h2]
    exact map_mem_closure (continuous_const.mul continuous_id) h1 (by rintro _ ⟨r, rfl⟩; exact ⟨r, rfl⟩)
  have hpi : ζ ∈ closure (Set.univ.pi fun _ : m => Set.univ.pi fun _ : n => T) := by
    rw [closure_pi_set]; intro i _; rw [closure_pi_set]; intro j _; exact hT i j
  refine closure_mono ?_ hpi
  intro ξ hξ
  choose A hA using fun i j => hξ i (Set.mem_univ _) j (Set.mem_univ _)
  refine ⟨(algebraMap R K d) • (Matrix.of A).map (algebraMap R K), hM (Matrix.of A), ?_⟩
  refine Matrix.ext fun i j => ?_
  simp only [matI, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.of_apply]
  exact hA i j

theorem low_approximation_holds : ApproxLow := by
  intro R _ _ K _ _ _ v m n _ _ M M' d hd hM' z hz
  set e := algebraMap K (v.adicCompletion K) (algebraMap R K d)
  have hU : {x | z - x ∈ {ζ : Matrix m n (v.adicCompletion K) | ∀ i j, e⁻¹ * ζ i j ∈ v.adicCompletionIntegers K}} ∈ 𝓝 z :=
    ((isOpen_boxW_adic v m n e⁻¹).preimage (continuous_const.sub continuous_id)).mem_nhds
      (by show ∀ i j, e⁻¹ * (z - z) i j ∈ v.adicCompletionIntegers K
          intro i j; rw [sub_self, Matrix.zero_apply, mul_zero]; exact zero_mem _)
  obtain ⟨_, hx, A, hA, rfl⟩ := mem_closure_iff_nhds.mp hz _ hU
  exact ⟨A, hA, boxW_sub_closure v _ d hd hM' hx⟩

theorem closure_character_holds : ClosChar := by
  intro R _ _ K _ _ _ v m n _ _ M d hd hM y
  set e := algebraMap K (v.adicCompletion K) (algebraMap R K d) with he
  have hdK : algebraMap R K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd
  constructor
  · intro hy
    have hU : {x | matI v y - x ∈ {ζ : Matrix m n (v.adicCompletion K) | ∀ i j, e⁻¹ * ζ i j ∈ v.adicCompletionIntegers K}} ∈ 𝓝 (matI v y) :=
      ((isOpen_boxW_adic v m n e⁻¹).preimage (continuous_const.sub continuous_id)).mem_nhds
        (by show ∀ i j, e⁻¹ * (matI v y - matI v y) i j ∈ v.adicCompletionIntegers K
            intro i j; rw [sub_self, Matrix.zero_apply, mul_zero]; exact zero_mem _)
    obtain ⟨_, hx, A, hA, rfl⟩ := mem_closure_iff_nhds.mp hy _ hU
    have hx' : ∀ p : m × n, v.valuation K ((y p.1 p.2 - A p.1 p.2) / algebraMap R K d) ≤ 1 := by
      intro p
      rw [← valAlg_adic v]
      have h := hx p.1 p.2
      have e2 : algebraMap K (v.adicCompletion K) ((y p.1 p.2 - A p.1 p.2) / algebraMap R K d) =
          e⁻¹ * (matI v y - matI v A) p.1 p.2 := by
        simp only [matI, Matrix.sub_apply, Matrix.map_apply, map_div₀, map_sub, he]
        rw [div_eq_inv_mul]
      rw [e2]; exact h
    choose nn ss hns using fun p : m × n => HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v _ (hx' p)
    refine ⟨∏ p, (ss p : R), ?_, ?_⟩
    · exact Submonoid.prod_mem _ fun p _ => (ss p).2
    · choose c hc using fun p : m × n => Finset.dvd_prod_of_mem (fun p => (ss p : R)) (Finset.mem_univ p)
      have key : (∏ p, (ss p : R)) • (y - A) =
          (algebraMap R K d) • (Matrix.of fun i j => c (i, j) * nn (i, j)).map (algebraMap R K) := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul,
          Algebra.smul_def, map_mul]
        rw [← hns (i, j), hc (i, j), map_mul]
        field_simp
      have : (∏ p, (ss p : R)) • y = (∏ p, (ss p : R)) • (y - A) + (∏ p, (ss p : R)) • A := by
        rw [smul_sub, sub_add_cancel]
      rw [this, key]
      exact M.add_mem (hM _) (M.smul_mem _ hA)
  · rintro ⟨s, hs, hsy⟩
    set es := algebraMap K (v.adicCompletion K) (algebraMap R K s) with hes
    have hs0 : s ≠ 0 := by rintro rfl; exact hs (zero_mem _)
    have hne : es ≠ 0 := (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs0)
    have hval : Valued.v es⁻¹ ≤ 1 := by
      rw [map_inv₀, hes, valAlg_adic v, HeightOneSpectrum.valuation_of_algebraMap,
        (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v s).mpr hs, inv_one]
    have h1 := denseInt_adic v _ hval
    have key := map_mem_closure (f := fun c : v.adicCompletion K => c • matI v (s • y))
      (t := matI v '' (M : Set (Matrix m n K))) (continuous_id.smul continuous_const) h1 (by
        rintro _ ⟨r, rfl⟩
        refine ⟨r • s • y, M.smul_mem r hsy, ?_⟩
        refine Matrix.ext fun i j => ?_
        simp only [matI, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul,
          Algebra.algebraMap_self, RingHom.id_apply])
    convert key using 1
    refine Matrix.ext fun i j => ?_
    simp only [matI, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul,
      Algebra.algebraMap_self, RingHom.id_apply, ← hes]
    rw [inv_mul_cancel_left₀ hne]

end Formalism.L2.PairingIndexBounds.Rec
end
end

namespace Formalism.L2.PairingIndexBounds.Rec

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem HalvesRec_of (hA : HfIntRec) (hB : SelfDualRec) : HalvesRec :=
  halvesRec_of_clos closure_character_holds low_approximation_holds hA hB

theorem modelXi_of_parts (hA : HfIntRec) (hB : SelfDualRec) (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.modelXi D :=
  modelXi_all (HalvesRec_of hA hB) D

end Formalism.L2.PairingIndexBounds.Rec
end

namespace Formalism.L2.PairingIndexBounds.Rec

theorem model_at_split_places_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.modelXi D :=
  modelXi_of_parts Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.self_dual_lattice D

theorem split_place_moves_compose (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.movesCompose D :=
  movesCompose_of_parts Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.self_dual_lattice D

end Formalism.L2.PairingIndexBounds.Rec

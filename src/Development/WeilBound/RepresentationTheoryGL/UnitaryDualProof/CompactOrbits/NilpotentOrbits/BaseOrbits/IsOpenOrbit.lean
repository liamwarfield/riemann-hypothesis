module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseP

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.IsOpenCball1
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.IntOfSm
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.OneDim
noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Nil.BasePf

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem cent_le (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (h0 : dB0 Z = 0)
    (x : Matrix (Fin n) (Fin n) k) (hx : ∀ a ∈ Z, a * x = x * a) : x ∈ Z := by
  have hle : Subalgebra.toSubmodule Z ≤ Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) := by
    intro a ha
    rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
    intro b hb
    exact hZ.1 b hb a ha
  have hfin : Module.finrank k (Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))))
      ≤ Module.finrank k (Subalgebra.toSubmodule Z) := Nat.sub_eq_zero_iff_le.1 h0
  have heq := Submodule.eq_of_le_of_finrank_le hle hfin
  have hxc : x ∈ Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) := by
    rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
    intro g hg
    exact hx g hg
  rw [← heq] at hxc
  exact hxc

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem prim_lemma (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hr : IsReduced Z) (c : Z) (hc0 : c ≠ 0) :
    ∃ b : Z, b * c * (b * c) = b * c ∧ b * c ≠ 0 := by
  letI : CommRing Z := { (inferInstance : Ring Z) with mul_comm := fun a b => Subtype.ext (hc _ a.2 _ b.2) }
  haveI : IsArtinianRing Z := IsArtinianRing.of_finite k Z
  obtain ⟨m, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd c (1 : Z)
  simp only [smul_eq_mul, mul_one] at hy
  have hpow : ∀ j : ℕ, c ^ m * (c * y) ^ j = c ^ m := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc c ^ m * (c * y) ^ (j + 1) = c ^ (m + 1) * y * (c * y) ^ j := by ring
        _ = c ^ m := by rw [hy, ih]
  have hcm : c ^ m ≠ 0 := fun h0 => hc0 (IsReduced.eq_zero c ⟨m, h0⟩)
  have he : c ^ m * y ^ (m + 1) * c = (c * y) ^ (m + 1) := by ring
  refine ⟨c ^ m * y ^ (m + 1), ?_, ?_⟩
  · rw [he]
    calc (c * y) ^ (m + 1) * (c * y) ^ (m + 1) = c * y ^ (m + 1) * (c ^ m * (c * y) ^ (m + 1)) := by ring
      _ = (c * y) ^ (m + 1) := by rw [hpow]; ring
  · intro h0
    apply hcm
    rw [he] at h0
    rw [← hpow (m + 1), h0, mul_zero]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem prim_lemma_2 (f g : Matrix (Fin n) (Fin n) k) (hf : f * f = f) (hg : g * g = g)
    (hfg : f * g = 0) (hgf : g * f = 0) (hg0 : g ≠ 0) : f.rank < (f + g).rank := by
  have hle : LinearMap.range f.mulVecLin ≤ LinearMap.range (f + g).mulVecLin := by
    rintro y ⟨w, rfl⟩
    refine ⟨f *ᵥ w, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, add_mul, hf, hgf, add_zero]
  have hne : LinearMap.range f.mulVecLin ≠ LinearMap.range (f + g).mulVecLin := by
    intro heq
    obtain ⟨w, hw⟩ : ∃ w, g *ᵥ w ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hg0
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun w => ?_
      simp [Matrix.toLin'_apply, hall w]
    have hmem : g *ᵥ w ∈ LinearMap.range (f + g).mulVecLin := by
      refine ⟨g *ᵥ w, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, add_mul, hg, hfg, zero_add]
    rw [← heq] at hmem
    obtain ⟨w', hw'⟩ := hmem
    simp only [Matrix.mulVecLin_apply] at hw'
    apply hw
    calc g *ᵥ w = g *ᵥ (g *ᵥ w) := by rw [Matrix.mulVec_mulVec, hg]
      _ = g *ᵥ (f *ᵥ w') := by rw [hw']
      _ = 0 := by rw [Matrix.mulVec_mulVec, hgf, Matrix.zero_mulVec]
  exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem prim (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hr : IsReduced Z) (v : Fin n → k) (hv : v ≠ 0) :
    ∃ e ∈ Z, e * e = e ∧ e *ᵥ v ≠ 0 ∧
      ∀ u ∈ Z, u * e = u → u ≠ 0 → ∃ u' ∈ Z, u' * e = u' ∧ u' * u = e := by
  classical
  let P : ℕ → Prop := fun r => ∃ e ∈ Z, e * e = e ∧ e *ᵥ v ≠ 0 ∧ e.rank = r
  have hP : ∃ r, P r := ⟨_, 1, Z.one_mem, mul_one 1, by simpa using hv, rfl⟩
  obtain ⟨e, heZ, hee, hev, hre⟩ := Nat.find_spec hP
  refine ⟨e, heZ, hee, hev, ?_⟩
  intro u huZ hue hu0
  obtain ⟨b, hidem, hne⟩ := prim_lemma Z hc hr ⟨u, huZ⟩ (fun h => hu0 (congrArg Subtype.val h))
  have hidem' : (b : Matrix (Fin n) (Fin n) k) * u * ((b : Matrix (Fin n) (Fin n) k) * u) = (b : Matrix (Fin n) (Fin n) k) * u :=
    congrArg Subtype.val hidem
  have hne' : (b : Matrix (Fin n) (Fin n) k) * u ≠ 0 := fun h => hne (Subtype.ext h)
  have hbZ := b.2
  obtain ⟨f, hfdef⟩ : ∃ f, f = (b : Matrix (Fin n) (Fin n) k) * u := ⟨_, rfl⟩
  rw [← hfdef] at hidem' hne'
  have hfZ : f ∈ Z := hfdef ▸ Z.mul_mem hbZ huZ
  have hfe : f * e = f := by rw [hfdef, mul_assoc, hue]
  have hef : e * f = f := by rw [hc e heZ f hfZ, hfe]
  by_cases hfe' : f = e
  · refine ⟨(b : Matrix (Fin n) (Fin n) k) * e, Z.mul_mem hbZ heZ, by rw [mul_assoc, hee], ?_⟩
    calc (b : Matrix (Fin n) (Fin n) k) * e * u = b * (e * u) := mul_assoc _ _ _
      _ = b * (u * e) := by rw [hc e heZ u huZ]
      _ = b * u := by rw [hue]
      _ = e := by rw [← hfdef, hfe']
  · exfalso
    have hgZ : e - f ∈ Z := Z.sub_mem heZ hfZ
    have hgg : (e - f) * (e - f) = e - f := by
      rw [sub_mul, mul_sub, mul_sub, hee, hef, hfe, hidem', sub_self, sub_zero]
    have hfg : f * (e - f) = 0 := by rw [mul_sub, hfe, hidem', sub_self]
    have hgf : (e - f) * f = 0 := by rw [sub_mul, hef, hidem', sub_self]
    have hg0 : e - f ≠ 0 := sub_ne_zero.2 (Ne.symm hfe')
    by_cases hfv : f *ᵥ v = 0
    · have hgv : (e - f) *ᵥ v ≠ 0 := by rw [Matrix.sub_mulVec, hfv, sub_zero]; exact hev
      have hlt : (e - f).rank < e.rank := by
        have := prim_lemma_2 (e - f) f hgg hidem' hgf hfg hne'
        rwa [sub_add_cancel] at this
      have := Nat.find_min' hP ⟨e - f, hgZ, hgg, hgv, rfl⟩
      omega
    · have hlt : f.rank < e.rank := by
        have := prim_lemma_2 f (e - f) hidem' hgg hfg hgf hg0
        rwa [add_sub_cancel] at this
      have := Nat.find_min' hP ⟨f, hfZ, hidem', hfv, rfl⟩
      omega

theorem one_dim (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (h0 : dB0 Z = 0)
    (e : Matrix (Fin n) (Fin n) k) (he : e ∈ Z) (hee : e * e = e)
    (hprim : ∀ u ∈ Z, u * e = u → u ≠ 0 → ∃ u' ∈ Z, u' * e = u' ∧ u' * u = e)
    (w0 w : Fin n → k) (hw0 : e *ᵥ w0 = w0) (hw0' : w0 ≠ 0) (hw : e *ᵥ w = w) :
    ∃ u ∈ Z, u * e = u ∧ u *ᵥ w0 = w := by
  classical
  haveI hred : IsReduced Z := hZ.2
  letI : CommRing Z := { (inferInstance : Ring Z) with mul_comm := fun a b => Subtype.ext (hZ.1 _ a.2 _ b.2) }
  haveI : IsArtinianRing Z := IsArtinianRing.of_finite k Z
  haveI : IsSemisimpleRing Z := IsArtinianRing.isSemisimpleRing_of_isReduced Z
  let ρ : Z →+* Module.End k (Fin n → k) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).toRingHom.comp
      Z.val.toRingHom
  letI : Module Z (Fin n → k) := Module.compHom (Fin n → k) ρ
  have hsmul : ∀ (z : Z) (v : Fin n → k), z • v = (z : Matrix (Fin n) (Fin n) k) *ᵥ v := fun _ _ => rfl
  have halg : ∀ (c : k) (v : Fin n → k), (algebraMap k Z c) • v = c • v := by
    intro c v
    rw [hsmul]
    simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
  let W : Submodule Z (Fin n → k) := Submodule.span Z {w0}
  obtain ⟨W', hWW'⟩ := exists_isCompl W
  let q := W'.projectionOnto W hWW'.symm
  let qk : (Fin n → k) →ₗ[k] (Fin n → k) :=
    { toFun := fun v => (q v : Fin n → k)
      map_add' := fun a b => by simp
      map_smul' := fun c v => by
        simp only [RingHom.id_apply]
        calc (q (c • v) : Fin n → k) = (q (algebraMap k Z c • v) : Fin n → k) :=
              congrArg (fun x => (q x : Fin n → k)) (halg c v).symm
          _ = ((algebraMap k Z c • q v : W') : Fin n → k) := congrArg Subtype.val (q.map_smul _ _)
          _ = algebraMap k Z c • (q v : Fin n → k) := rfl
          _ = c • (q v : Fin n → k) := halg _ _ }
  have hX : ∀ v, LinearMap.toMatrix' qk *ᵥ v = (q v : Fin n → k) := fun v => LinearMap.toMatrix'_mulVec qk v
  have hcomm : ∀ a ∈ Z, a * LinearMap.toMatrix' qk = LinearMap.toMatrix' qk * a := by
    intro a ha
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hX]
    have h1 := congrArg Subtype.val (q.map_smul ⟨a, ha⟩ v)
    exact h1.symm
  have hXZ : LinearMap.toMatrix' qk ∈ Z := cent_le Z hZ h0 _ hcomm
  have hqW : ∀ x, (q x : Fin n → k) = 0 ↔ x ∈ W := by
    intro x
    rw [← Submodule.linearProjOfIsCompl_apply_eq_zero_iff hWW'.symm]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hXw0 : LinearMap.toMatrix' qk *ᵥ w0 = 0 := by
    rw [hX, hqW]
    exact Submodule.subset_span rfl
  have hXe : LinearMap.toMatrix' qk * e = 0 := by
    by_contra hne
    obtain ⟨u', hu'Z, hu'e, hu'⟩ := hprim _ (Z.mul_mem hXZ he) (by rw [mul_assoc, hee]) hne
    apply hw0'
    calc w0 = e *ᵥ w0 := hw0.symm
      _ = (u' * (LinearMap.toMatrix' qk * e)) *ᵥ w0 := by rw [hu']
      _ = u' *ᵥ (LinearMap.toMatrix' qk *ᵥ (e *ᵥ w0)) := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc]
      _ = 0 := by rw [hw0, hXw0, Matrix.mulVec_zero]
  have hwW : w ∈ W := by
    rw [← hqW, ← hX, ← hw, Matrix.mulVec_mulVec, hXe, Matrix.zero_mulVec]
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.1 hwW
  refine ⟨(z : Matrix (Fin n) (Fin n) k) * e, Z.mul_mem z.2 he, by rw [mul_assoc, hee], ?_⟩
  rw [← Matrix.mulVec_mulVec, hw0]
  exact hz

end PositivityTheory.RgUd.T.Nil.BasePf
end
end

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Nil.BasePf

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

abbrev Wt (e : Matrix (Fin n) (Fin n) k) : Type := {w : Fin n → k // e *ᵥ w = w}

def Gs (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (e : Matrix (Fin n) (Fin n) k) : Subgroup (GL (Fin n) k) where
  carrier := {g | g ∈ Gz Z ∧ g.val * e = e * g.val ∧ g.val * (1 - e) = 1 - e}
  mul_mem' := by
    rintro g h ⟨hg, hge, hg'⟩ ⟨hh, hhe, hh'⟩
    refine ⟨fun a ha => ?_, ?_, ?_⟩
    · simp only [Units.val_mul]; rw [← mul_assoc, hg a ha, mul_assoc, hh a ha, mul_assoc]
    · simp only [Units.val_mul]; rw [mul_assoc, hhe, ← mul_assoc, hge, mul_assoc]
    · simp only [Units.val_mul]; rw [mul_assoc, hh', hg']
  one_mem' := ⟨fun a _ => by simp, by simp, by simp⟩
  inv_mem' := by
    rintro g ⟨hg, hge, hg'⟩
    have comm : ∀ a, a * g.val = g.val * a → a * g⁻¹.val = g⁻¹.val * a := fun a h1 =>
      calc a * g⁻¹.val = g⁻¹.val * (g.val * a) * g⁻¹.val := by rw [← mul_assoc, Units.inv_mul, one_mul]
        _ = g⁻¹.val * (a * g.val) * g⁻¹.val := by rw [h1]
        _ = g⁻¹.val * a := by rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
    refine ⟨fun a ha => comm a (hg a ha), (comm e hge.symm).symm, ?_⟩
    calc g⁻¹.val * (1 - e) = g⁻¹.val * (g.val * (1 - e)) := by rw [hg']
      _ = 1 - e := by rw [← mul_assoc, Units.inv_mul, one_mul]

theorem Gs_mem {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {e : Matrix (Fin n) (Fin n) k} (g : Gs Z e) :
    (g : GL (Fin n) k) ∈ Gz Z ∧ (g : GL (Fin n) k).val * e = e * (g : GL (Fin n) k).val ∧
      (g : GL (Fin n) k).val * (1 - e) = 1 - e := g.2

instance (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (e : Matrix (Fin n) (Fin n) k) :
    MulAction (Gs Z e) (Wt e) where
  smul g w := ⟨(g : GL (Fin n) k).val *ᵥ w.1, by rw [mulVec_mulVec, ← (Gs_mem g).2.1, ← mulVec_mulVec, w.2]⟩
  one_smul w := Subtype.ext (by
    show ((1 : Gs Z e) : GL (Fin n) k).val *ᵥ w.1 = w.1
    simp)
  mul_smul g h w := Subtype.ext (by
    show ((g * h : Gs Z e) : GL (Fin n) k).val *ᵥ w.1 = (g : GL (Fin n) k).val *ᵥ ((h : GL (Fin n) k).val *ᵥ w.1)
    simp [mulVec_mulVec])

theorem smul_val (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (e : Matrix (Fin n) (Fin n) k) (g : Gs Z e)
    (w : Wt e) : (g • w).1 = (g : GL (Fin n) k).val *ᵥ w.1 := rfl

theorem Gs_comm (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (h0 : dB0 Z = 0)
    (e : Matrix (Fin n) (Fin n) k) (g h : Gs Z e) : g * h = h * g := by
  have hsub : Z ≤ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) := fun a ha =>
    (Subalgebra.mem_centralizer_iff k).mpr (fun b hb => hZ.1 b hb a ha)
  have hle : Module.finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) ≤
      Module.finrank k Z := by
    have h0' := h0
    unfold dB0 at h0'
    omega
  have heq : Subalgebra.toSubmodule Z =
      Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) :=
    Submodule.eq_of_le_of_finrank_le hsub hle
  have hmem : ∀ x : Gs Z e, ((x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈ Z := by
    intro x
    have hc : ((x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈
        Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) :=
      (Subalgebra.mem_centralizer_iff k).mpr (fun a ha => (Gs_mem x).1 a ha)
    rw [← heq] at hc
    exact hc
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  exact hZ.1 _ (hmem g) _ (hmem h)

def sm (γ : (ValueGroupWithZero k)ˣ) (A : Matrix (Fin n) (Fin n) k) : Prop :=
  ∀ i j, valuation k (A i j) < γ ∧ valuation k (A i j) < 1

theorem ent_lt (c : ValueGroupWithZero k) (hc : c ≠ 0) (a b : Matrix (Fin n) (Fin n) k)
    (ha : ∀ i j, valuation k (a i j) < c) (hb : ∀ i j, valuation k (b i j) < c)
    (hb1 : ∀ i j, valuation k (b i j) ≤ 1) (i j : Fin n) : valuation k ((a * b + a + b) i j) < c := by
  simp only [Matrix.add_apply, Matrix.mul_apply]
  refine (valuation k).map_add_lt ((valuation k).map_add_lt ?_ (ha i j)) (hb i j)
  refine (valuation k).map_sum_lt hc (fun l _ => ?_)
  rw [map_mul]
  calc valuation k (a i l) * valuation k (b l j) ≤ valuation k (a i l) * 1 := by
        gcongr
        exact hb1 l j
    _ = valuation k (a i l) := mul_one _
    _ < c := ha i l

theorem sm_mul (γ : (ValueGroupWithZero k)ˣ) (A B : Matrix (Fin n) (Fin n) k) (hA : sm γ (A - 1))
    (hB : sm γ (B - 1)) : sm γ (A * B - 1) := by
  have e : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
  unfold sm at *
  intro i j
  rw [e]
  exact ⟨ent_lt _ γ.ne_zero _ _ (fun i j => (hA i j).1) (fun i j => (hB i j).1) (fun i j => (hB i j).2.le) i j,
    ent_lt _ one_ne_zero _ _ (fun i j => (hA i j).2) (fun i j => (hB i j).2) (fun i j => (hB i j).2.le) i j⟩

theorem sm_zero (γ : (ValueGroupWithZero k)ˣ) : sm γ (0 : Matrix (Fin n) (Fin n) k) := by
  intro i j
  simp only [Matrix.zero_apply, map_zero]
  exact ⟨zero_lt_iff.mpr γ.ne_zero, zero_lt_one⟩

def Ks (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (e : Matrix (Fin n) (Fin n) k) (γ : (ValueGroupWithZero k)ˣ) :
    Subgroup (Gs Z e) where
  carrier := {g | sm γ ((g : GL (Fin n) k).val - 1) ∧ sm γ ((g : GL (Fin n) k)⁻¹.val - 1)}
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨?_, ?_⟩
    · simp only [Subgroup.coe_mul, Units.val_mul]
      exact sm_mul γ _ _ hg hh
    · simp only [Subgroup.coe_mul, _root_.mul_inv_rev, Units.val_mul]
      exact sm_mul γ _ _ hh' hg'
  one_mem' := ⟨by simpa using sm_zero γ, by simpa using sm_zero γ⟩
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    refine ⟨?_, ?_⟩
    · simpa using hg'
    · simpa using hg

theorem int_of_sm {γ : (ValueGroupWithZero k)ˣ} {A : Matrix (Fin n) (Fin n) k} (hA : sm γ (A - 1)) (i j : Fin n) :
    valuation k (A i j) ≤ 1 := by
  have h1 : A i j = (A - 1) i j + (1 : Matrix (Fin n) (Fin n) k) i j := by simp
  rw [h1]
  refine ((valuation k).map_add _ _).trans (max_le (hA i j).2.le ?_)
  rw [Matrix.one_apply]
  split_ifs <;> simp

end PositivityTheory.RgUd.T.Nil.BasePf
end
end

noncomputable section

open Matrix Topology

namespace PositivityTheory.RgUd.T.Nil.BasePf

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem isOpen_ball' (γ : (ValueGroupWithZero k)ˣ) : IsOpen {x : k | valuation k x < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨γ, fun y hy => ?_⟩
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have h := (valuation k).map_add (y - x) x
  rw [sub_add_cancel] at h
  exact lt_of_le_of_lt h (max_lt hy hx)

theorem isOpen_cball1 : IsOpen {x : k | valuation k x ≤ 1} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨1, fun y hy => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_one] at hx hy ⊢
  have h := (valuation k).map_add (y - x) x
  rw [sub_add_cancel] at h
  exact le_trans h (max_le hy.le hx)

theorem isOpen_sm (γ : (ValueGroupWithZero k)ˣ) : IsOpen {A : Matrix (Fin n) (Fin n) k | sm γ A} := by
  have : {A : Matrix (Fin n) (Fin n) k | sm γ A} = ⋂ i, ⋂ j, (fun A : Matrix (Fin n) (Fin n) k => A i j) ⁻¹'
      ({x | valuation k x < γ} ∩ {x | valuation k x < ((1 : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)}) := by
    ext A
    simp [sm]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    ((isOpen_ball' γ).inter (isOpen_ball' 1)).preimage (continuous_id.matrix_elem i j)

theorem nhds_one_ball {U : Set (Matrix (Fin n) (Fin n) k)} (hU : U ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) k)) :
    ∃ γ : (ValueGroupWithZero k)ˣ, ∀ A : Matrix (Fin n) (Fin n) k,
      (∀ i j, valuation k ((A - 1) i j) < γ) → A ∈ U := by
  let B : (ValueGroupWithZero k)ˣ → Set (Matrix (Fin n) (Fin n) k) :=
    fun γ => {A | ∀ i j, valuation k ((A - 1) i j) < γ}
  have hdir : Directed (· ≥ ·) (fun γ => Filter.principal (B γ)) := by
    intro a b
    refine ⟨min a b, ?_, ?_⟩
    · simp only [ge_iff_le, Filter.principal_mono]
      intro A hA i j
      exact lt_of_lt_of_le (hA i j) (by exact_mod_cast min_le_left a b)
    · simp only [ge_iff_le, Filter.principal_mono]
      intro A hA i j
      exact lt_of_lt_of_le (hA i j) (by exact_mod_cast min_le_right a b)
  have ht : Filter.Tendsto (fun A : Matrix (Fin n) (Fin n) k => A)
      (⨅ γ, Filter.principal (B γ)) (𝓝 (1 : Matrix (Fin n) (Fin n) k)) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    rw [(IsValuativeTopology.hasBasis_nhds ((1 : Matrix (Fin n) (Fin n) k) i j)).tendsto_right_iff]
    intro δ _
    rw [Filter.eventually_iff]
    refine Filter.mem_iInf_of_mem δ ?_
    rw [Filter.mem_principal]
    intro A hA
    simpa [Matrix.sub_apply] using hA i j
  obtain ⟨γ, hγ⟩ := (Filter.mem_iInf_of_directed hdir _).mp (ht hU)
  exact ⟨γ, fun A hA => Filter.mem_principal.mp hγ hA⟩

theorem cont_inv_one : ContinuousAt (fun A : Matrix (Fin n) (Fin n) k => A⁻¹) 1 := by
  apply continuousAt_matrix_inv
  rw [det_one, Ring.inverse_eq_inv']
  exact continuousAt_inv₀ one_ne_zero

theorem isClosed_Wt (e : Matrix (Fin n) (Fin n) k) : IsClosed {w : Fin n → k | e *ᵥ w = w} :=
  isClosed_eq (continuous_const.matrix_mulVec continuous_id) continuous_id

theorem isCompact_L (e : Matrix (Fin n) (Fin n) k) :
    IsCompact {w : Wt e | ∀ i, valuation k (w.1 i) ≤ 1} := by
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin n => {x : k | valuation k x ≤ 1}) :=
    isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have heq : {w : Wt e | ∀ i, valuation k (w.1 i) ≤ 1} =
      (Subtype.val : Wt e → (Fin n → k)) ⁻¹' (Set.pi Set.univ fun _ : Fin n => {x : k | valuation k x ≤ 1}) := by
    ext w
    simp
  rw [heq]
  exact (isClosed_Wt e).isClosedEmbedding_subtypeVal.isCompact_preimage hK

theorem isOpen_L (e : Matrix (Fin n) (Fin n) k) :
    IsOpen {w : Wt e | ∀ i, valuation k (w.1 i) ≤ 1} := by
  have hO : IsOpen (Set.pi Set.univ fun _ : Fin n => {x : k | valuation k x ≤ 1}) :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball1
  have := hO.preimage (continuous_subtype_val : Continuous (Subtype.val : Wt e → (Fin n → k)))
  convert this using 1
  ext w
  simp

end PositivityTheory.RgUd.T.Nil.BasePf
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.PieceMem
noncomputable section

open Set GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Nil.BasePf

variable {Y W G : Type*} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace W] [T2Space W]
  [Group G] [MulAction G W]

def rel (K : Subgroup G) : Setoid W where
  r a b := ∃ g ∈ K, g • b = a
  iseqv :=
    { refl := fun a => ⟨1, K.one_mem, one_smul _ _⟩
      symm := fun {a b} ⟨g, hg, h⟩ => ⟨g⁻¹, K.inv_mem hg, by rw [← h, inv_smul_smul]⟩
      trans := fun {a b c} ⟨g, hg, h⟩ ⟨g', hg', h'⟩ => ⟨g * g', K.mul_mem hg hg', by rw [mul_smul, h', h]⟩ }

theorem rel_iff (K : Subgroup G) (a b : W) :
    Quotient.mk (rel K) a = Quotient.mk (rel K) b ↔ ∃ g ∈ K, g • b = a :=
  Quotient.eq (r := rel K)

abbrev TF (X : Type*) [TopologicalSpace X] : Submodule ℂ (X → ℂ) :=
  GroundTheory.Automorphic.locallyConstantCompactSupport X ℂ ℂ

theorem comp_mem {F : Y × W → ℂ} (hF : F ∈ TF (Y × W)) (g : G) (hg : Continuous fun w : W => g • w)
    (hg' : Continuous fun w : W => g⁻¹ • w) : (fun p : Y × W => F (p.1, g • p.2)) ∈ TF (Y × W) := by
  refine ⟨hF.1.comp_continuous (continuous_fst.prodMk (hg.comp continuous_snd)), ?_⟩
  refine HasCompactSupport.intro ((hF.2.isCompact).image
    (continuous_fst.prodMk (hg'.comp continuous_snd))) fun x hx => ?_
  by_contra h
  refine hx ⟨(x.1, g • x.2), subset_tsupport _ h, ?_⟩
  all_goals simp

theorem tens_mem {a : Y → ℂ} (ha : a ∈ TF Y) {U : Set W} (hUc : IsCompact U) (hUo : IsOpen U) :
    (fun p : Y × W => a p.1 * U.indicator 1 p.2) ∈ TF (Y × W) := by
  have h1 : IsLocallyConstant (U.indicator (1 : W → ℂ)) :=
    (LocallyConstant.indicator (LocallyConstant.const W (1 : ℂ)) ⟨hUc.isClosed, hUo⟩).isLocallyConstant
  refine ⟨(ha.1.comp_continuous continuous_fst).comp₂ (h1.comp_continuous continuous_snd) (· * ·), ?_⟩
  refine HasCompactSupport.intro (ha.2.isCompact.prod hUc) fun p hp => ?_
  simp only [mem_prod, not_and_or] at hp
  rcases hp with h | h
  · simp [image_eq_zero_of_notMem_tsupport h]
  · simp [Set.indicator_of_notMem h]

theorem slice_mem {F : Y × W → ℂ} (hF : F ∈ TF (Y × W)) (w : W) : (fun y => F (y, w)) ∈ TF Y := by
  refine ⟨hF.1.comp_continuous (continuous_id.prodMk continuous_const), ?_⟩
  refine HasCompactSupport.intro (hF.2.isCompact.image continuous_fst) fun y hy => ?_
  by_contra h
  exact hy ⟨(y, w), subset_tsupport _ h, rfl⟩


open Classical in
theorem piece_mem (K : Subgroup G) (S : Set W) (hKo : ∀ w ∈ S, IsOpen {w' | ∃ g ∈ K, g • w = w'})
    {F : Y × W → ℂ} (hF : F ∈ TF (Y × W)) (hFS : ∀ p : Y × W, p.2 ∉ S → F p = 0)
    (q : Quotient (rel K)) :
    (fun p : Y × W => F p * if Quotient.mk (rel K) p.2 = q then 1 else 0) ∈ TF (Y × W) := by
  refine ⟨?_, hF.2.mul_right⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro p
  by_cases hp : p.2 ∈ S
  · have hO : {w' | ∃ g ∈ K, g • p.2 = w'} ∈ nhds p.2 := (hKo p.2 hp).mem_nhds ⟨1, K.one_mem, one_smul _ _⟩
    have h1 := ((IsLocallyConstant.iff_eventually_eq _).1 hF.1) p
    have h2 : ∀ᶠ x : Y × W in nhds p, x.2 ∈ {w' | ∃ g ∈ K, g • p.2 = w'} :=
      continuous_snd.continuousAt.preimage_mem_nhds hO
    filter_upwards [h1, h2] with x hx1 hx2
    obtain ⟨g, hg, hgx⟩ := hx2
    have : Quotient.mk (rel K) x.2 = Quotient.mk (rel K) p.2 := (rel_iff K _ _).2 ⟨g, hg, hgx⟩
    rw [hx1, this]
  · have h0 : F p = 0 := hFS p hp
    have h1 := ((IsLocallyConstant.iff_eventually_eq _).1 hF.1) p
    filter_upwards [h1] with x hx1
    rw [hx1, h0, zero_mul, zero_mul]

variable {ι : Type*}

open Classical in
theorem core (hcomm : ∀ a b : G, a * b = b * a) (hcont : ∀ g : G, Continuous fun w : W => g • w)
    (D : (Y × W → ℂ) →ₗ[ℂ] ℂ)
    (hD : ∀ g : G, ∀ f ∈ TF (Y × W), D (fun p => f (p.1, g • p.2)) = D f)
    (S : Set W) (w0 : W) (htr : ∀ w ∈ S, ∃ g : G, g • w0 = w)
    (K : ι → Subgroup G) (hKo : ∀ i, ∀ w ∈ S, IsOpen {w' | ∃ g ∈ K i, g • w = w'})
    (hKf : ∀ f ∈ supportedIn (univ ×ˢ S : Set (Y × W)), ∃ i, ∀ g ∈ K i, ∀ p : Y × W, f (p.1, g • p.2) = f p)
    (t : G) (L : Set W) (hLc : IsCompact L) (hLo : IsOpen L) (hLK : ∀ i, ∀ g ∈ K i, ∀ w ∈ L, g • w ∈ L)
    (htL : ∀ w, t⁻¹ • w ∈ L → w ∈ L) (hLS : ∀ w ∈ L, t⁻¹ • w ∉ L → w ∈ S)
    (hne : ∃ w ∈ L, t⁻¹ • w ∉ L) :
    ∀ f ∈ supportedIn (univ ×ˢ S : Set (Y × W)), D f = 0 := by

  set tL : Set W := {w | t⁻¹ • w ∈ L} with htLdef
  have htLc : IsClopen tL := ⟨hLc.isClosed.preimage (hcont t⁻¹), hLo.preimage (hcont t⁻¹)⟩
  set B : Set W := L ∩ tLᶜ with hBdef
  have hBc : IsCompact B := hLc.inter_right htLc.compl.isClosed
  have hBo : IsOpen B := hLo.inter htLc.isClosed.isOpen_compl
  have hBS : B ⊆ S := fun w hw => hLS w hw.1 hw.2
  have hBK : ∀ i, ∀ g ∈ K i, ∀ w ∈ B, g • w ∈ B := by
    intro i g hg w hw
    refine ⟨hLK i g hg w hw.1, fun h => hw.2 ?_⟩
    have h' : g⁻¹ • (t⁻¹ • (g • w)) ∈ L := hLK i g⁻¹ ((K i).inv_mem hg) _ h
    have e : g⁻¹ • (t⁻¹ • (g • w)) = t⁻¹ • w := by
      rw [← mul_smul, ← mul_smul, hcomm g⁻¹ t⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    show t⁻¹ • w ∈ L
    rwa [e] at h'

  have claimA : ∀ i, ∀ F ∈ TF (Y × W), (∀ g ∈ K i, ∀ p : Y × W, F (p.1, g • p.2) = F p) →
      (∀ p : Y × W, F p ≠ 0 → ∃ g ∈ K i, g • w0 = p.2) → D F = 0 := by
    intro i F hF hFK hFO
    set a : Y → ℂ := fun y => F (y, w0) with ha
    have haT : a ∈ TF Y := slice_mem hF w0
    set Φ : Y × W → ℂ := fun p => a p.1 * B.indicator 1 p.2 with hΦ
    have hΦT : Φ ∈ TF (Y × W) := tens_mem haT hBc hBo

    have hΦ0 : D Φ = 0 := by
      set ΦL : Y × W → ℂ := fun p => a p.1 * L.indicator 1 p.2
      have hLT : ΦL ∈ TF (Y × W) := tens_mem haT hLc hLo
      have e1 : (fun p : Y × W => ΦL (p.1, t⁻¹ • p.2)) = fun p => a p.1 * tL.indicator 1 p.2 := by
        funext p
        by_cases h : t⁻¹ • p.2 ∈ L
        · simp [ΦL, Set.indicator_of_mem h, Set.indicator_of_mem (show p.2 ∈ tL from h)]
        · simp [ΦL, Set.indicator_of_notMem h, Set.indicator_of_notMem (show p.2 ∉ tL from h)]
      have e2 : Φ = ΦL - fun p => a p.1 * tL.indicator 1 p.2 := by
        funext p
        simp only [Φ, ΦL, Pi.sub_apply, B]
        by_cases h1 : p.2 ∈ tL
        · have h2 : p.2 ∈ L := htL _ h1
          simp [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
            Set.indicator_of_notMem (show p.2 ∉ L ∩ tLᶜ from fun h => h.2 h1)]
        · by_cases h2 : p.2 ∈ L
          · simp [Set.indicator_of_notMem h1, Set.indicator_of_mem h2,
              Set.indicator_of_mem (show p.2 ∈ L ∩ tLᶜ from ⟨h2, h1⟩)]
          · simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2,
              Set.indicator_of_notMem (show p.2 ∉ L ∩ tLᶜ from fun h => h2 h.1)]
      rw [e2, map_sub, ← e1, hD t⁻¹ ΦL hLT, sub_self]

    obtain ⟨b, hbB, hbfin, hbcov⟩ := hBc.elim_finite_subcover_image (b := B)
      (c := fun r => {w' | ∃ g ∈ K i, g • r = w'}) (fun r hr => hKo i r (hBS hr))
      (fun w hw => mem_iUnion₂.2 ⟨w, hw, 1, (K i).one_mem, one_smul _ _⟩)
    set Q : Finset (Quotient (rel (K i))) := hbfin.toFinset.image (Quotient.mk (rel (K i))) with hQ
    have hΦsum : Φ = ∑ q ∈ Q, fun p : Y × W => Φ p * if Quotient.mk (rel (K i)) p.2 = q then 1 else 0 := by
      funext p
      rw [Finset.sum_apply]
      simp only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.sum_const_zero]
      by_cases hp : p.2 ∈ B
      · obtain ⟨r, hr, g, hg, hgr⟩ := mem_iUnion₂.1 (hbcov hp)
        have : Quotient.mk (rel (K i)) p.2 ∈ Q :=
          Finset.mem_image.2 ⟨r, hbfin.mem_toFinset.2 hr, ((rel_iff _ _ _).2 ⟨g, hg, hgr⟩).symm⟩
        simp [this]
      · simp [Φ, Set.indicator_of_notMem hp]
    have hpiece : ∀ q ∈ Q, D (fun p : Y × W => Φ p * if Quotient.mk (rel (K i)) p.2 = q then 1 else 0) = D F := by
      intro q hq
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hq
      have hrB : r ∈ B := hbB (hbfin.mem_toFinset.1 hr)
      obtain ⟨h, hh⟩ := htr r (hBS hrB)
      have hPT := piece_mem (K i) S (hKo i) hΦT
        (fun p hp => by simp [Φ, Set.indicator_of_notMem (fun h' => hp (hBS h'))])
        (Quotient.mk (rel (K i)) r)
      rw [← hD h _ hPT]
      congr 1
      funext p
      have key : Quotient.mk (rel (K i)) (h • p.2) = Quotient.mk (rel (K i)) r ↔ ∃ g ∈ K i, g • w0 = p.2 := by
        rw [rel_iff, ← hh]
        constructor
        · rintro ⟨g, hg, hgx⟩
          refine ⟨g, hg, ?_⟩
          have : h • (g • w0) = h • p.2 := by rw [← hgx, ← mul_smul, ← mul_smul, hcomm]
          exact smul_left_cancel h this
        · rintro ⟨g, hg, hgx⟩
          exact ⟨g, hg, by rw [← hgx, ← mul_smul, ← mul_smul, hcomm]⟩
      by_cases hp : ∃ g ∈ K i, g • w0 = p.2
      · have hk := key.2 hp
        obtain ⟨g, hg, hgx⟩ := hp
        have hhB : h • p.2 ∈ B := by
          rw [← hgx, ← mul_smul, hcomm, mul_smul, hh]
          exact hBK i g hg r hrB
        simp only [Φ, Set.indicator_of_mem hhB, hk, if_true, Pi.one_apply, mul_one, a]
        have e3 := hFK g hg (p.1, w0)
        simp only [hgx] at e3
        rw [← e3]
      · have hk : ¬ Quotient.mk (rel (K i)) (h • p.2) = Quotient.mk (rel (K i)) r := fun h' => hp (key.1 h')
        simp only [hk, if_false, mul_zero]
        by_contra h0
        exact hp (hFO p (Ne.symm h0))
    have hQne : Q.Nonempty := by
      obtain ⟨w, hwL, hwt⟩ := hne
      have hwB : w ∈ B := ⟨hwL, hwt⟩
      obtain ⟨r, hr, -⟩ := mem_iUnion₂.1 (hbcov hwB)
      exact ⟨_, Finset.mem_image.2 ⟨r, hbfin.mem_toFinset.2 hr, rfl⟩⟩
    have hsum : D Φ = (Q.card : ℂ) * D F := by
      conv_lhs => rw [hΦsum]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_congr rfl hpiece, Finset.sum_const, nsmul_eq_mul]
    rw [hΦ0] at hsum
    have hc : (Q.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hQne)
    exact (mul_eq_zero.1 hsum.symm).resolve_left hc

  intro f hf
  obtain ⟨i, hfK⟩ := hKf f hf
  have hfT : f ∈ TF (Y × W) := hf.1
  have hfS : ∀ p : Y × W, p.2 ∉ S → f p = 0 := fun p hp => by
    by_contra h
    exact hp (hf.2 h).2
  set C : Set W := Prod.snd '' Function.support f
  have hCc : IsCompact C := (isCompact_support hf.1).image continuous_snd
  have hCS : C ⊆ S := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hf.2 hp).2
  obtain ⟨b, hbC, hbfin, hbcov⟩ := hCc.elim_finite_subcover_image (b := C)
    (c := fun r => {w' | ∃ g ∈ K i, g • r = w'}) (fun r hr => hKo i r (hCS hr))
    (fun w hw => mem_iUnion₂.2 ⟨w, hw, 1, (K i).one_mem, one_smul _ _⟩)
  set Q : Finset (Quotient (rel (K i))) := hbfin.toFinset.image (Quotient.mk (rel (K i))) with hQ
  have hfsum : f = ∑ q ∈ Q, fun p : Y × W => f p * if Quotient.mk (rel (K i)) p.2 = q then 1 else 0 := by
    funext p
    rw [Finset.sum_apply]
    simp only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.sum_const_zero]
    by_cases hp : f p = 0
    · simp [hp]
    · obtain ⟨r, hr, g, hg, hgr⟩ := mem_iUnion₂.1 (hbcov ⟨p, hp, rfl⟩)
      have : Quotient.mk (rel (K i)) p.2 ∈ Q :=
        Finset.mem_image.2 ⟨r, hbfin.mem_toFinset.2 hr, ((rel_iff _ _ _).2 ⟨g, hg, hgr⟩).symm⟩
      simp [this]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hfsum, map_sum]
  refine Finset.sum_eq_zero fun q hq => ?_
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hq
  have hrS : r ∈ S := hCS (hbC (hbfin.mem_toFinset.1 hr))
  obtain ⟨h, hh⟩ := htr r hrS
  have hPT := piece_mem (K i) S (hKo i) hfT hfS (Quotient.mk (rel (K i)) r)
  rw [← hD h _ hPT]
  refine claimA i _ (comp_mem hPT h (hcont h) (hcont h⁻¹)) ?_ ?_
  · intro g hg p
    have e : Quotient.mk (rel (K i)) (g • h • p.2) = Quotient.mk (rel (K i)) (h • p.2) :=
      (rel_iff _ _ _).2 ⟨g, hg, rfl⟩
    have e2 : h • g • p.2 = g • h • p.2 := by rw [← mul_smul, ← mul_smul, hcomm]
    have e3 := hfK g hg (p.1, h • p.2)
    simp only at e3
    simp only [e2]
    rw [e, e3]
  · intro p hp
    have hk : Quotient.mk (rel (K i)) (h • p.2) = Quotient.mk (rel (K i)) r := by
      by_contra hk
      exact hp (by simp [hk])
    obtain ⟨g, hg, hgx⟩ := (rel_iff _ _ _).1 hk
    refine ⟨g, hg, smul_left_cancel h ?_⟩
    rw [← hgx, ← hh, ← mul_smul, ← mul_smul, hcomm]

end PositivityTheory.RgUd.T.Nil.BasePf
end
end

noncomputable section

open Matrix Topology

namespace PositivityTheory.RgUd.T.Nil.BasePf

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem uniq_eZ (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (e : Matrix (Fin n) (Fin n) k)
    (hprim : ∀ u ∈ Z, u * e = u → u ≠ 0 → ∃ u' ∈ Z, u' * e = u' ∧ u' * u = e)
    (w : Fin n → k) (hw : e *ᵥ w = w) (hw0 : w ≠ 0) (u1 u2 : Matrix (Fin n) (Fin n) k) (h1 : u1 ∈ Z)
    (h2 : u2 ∈ Z) (h1e : u1 * e = u1) (h2e : u2 * e = u2) (h12 : u1 *ᵥ w = u2 *ᵥ w) : u1 = u2 := by
  by_contra hne
  have hu : u1 - u2 ∈ Z := Z.sub_mem h1 h2
  have hue : (u1 - u2) * e = u1 - u2 := by rw [sub_mul, h1e, h2e]
  obtain ⟨u', -, -, hu'⟩ := hprim _ hu hue (sub_ne_zero.mpr hne)
  apply hw0
  have hz : (u1 - u2) *ᵥ w = 0 := by rw [sub_mulVec, h12, sub_self]
  rw [← hw, ← hu', ← mulVec_mulVec, hz, mulVec_zero]

theorem exists_psi (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (h0 : dB0 Z = 0)
    (e : Matrix (Fin n) (Fin n) k) (he : e ∈ Z) (hee : e * e = e)
    (hprim : ∀ u ∈ Z, u * e = u → u ≠ 0 → ∃ u' ∈ Z, u' * e = u' ∧ u' * u = e)
    (w : Fin n → k) (hw : e *ᵥ w = w) (hw0 : w ≠ 0) :
    ∃ ψ : (Fin n → k) →ₗ[k] Matrix (Fin n) (Fin n) k,
      ∀ v, ψ v ∈ Z ∧ ψ v * e = ψ v ∧ ψ v *ᵥ w = e *ᵥ v := by
  have hex : ∀ v : Fin n → k, ∃ u ∈ Z, u * e = u ∧ u *ᵥ w = e *ᵥ v := fun v =>
    one_dim Z hZ h0 e he hee hprim w (e *ᵥ v) hw hw0 (by rw [mulVec_mulVec, hee])
  choose φ hφZ hφe hφw using hex
  refine ⟨{ toFun := φ, map_add' := ?_, map_smul' := ?_ }, fun v => ⟨hφZ v, hφe v, hφw v⟩⟩
  · intro v1 v2
    apply uniq_eZ Z e hprim w hw hw0 _ _ (hφZ _) (Z.add_mem (hφZ v1) (hφZ v2))
      (hφe _) (by rw [add_mul, hφe, hφe])
    rw [hφw, add_mulVec, hφw, hφw, mulVec_add]
  · intro c v
    apply uniq_eZ Z e hprim w hw hw0 _ _ (hφZ _) (Z.smul_mem (hφZ v) c)
      (hφe _) (by rw [smul_mul_assoc, hφe])
    rw [hφw, smul_mulVec, hφw, mulVec_smul]

theorem orbit_nhds (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (h0 : dB0 Z = 0)
    (e : Matrix (Fin n) (Fin n) k) (he : e ∈ Z) (hee : e * e = e)
    (hprim : ∀ u ∈ Z, u * e = u → u ≠ 0 → ∃ u' ∈ Z, u' * e = u' ∧ u' * u = e)
    (γ : (ValueGroupWithZero k)ˣ) (w : Wt e) (hw0' : w.1 ≠ 0) :
    {w' | ∃ g ∈ Ks Z e γ, g • w = w'} ∈ 𝓝 w := by
  obtain ⟨ψ, hψ⟩ := exists_psi Z hZ h0 e he hee hprim w.1 w.2 hw0'
  have hψc : Continuous ψ := by
    have hrep : ∀ v : Fin n → k, ψ v = ∑ i, v i • ψ (fun j => if i = j then 1 else 0) := by
      intro v
      conv_lhs => rw [pi_eq_sum_univ v]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_smul]
    have hfun : (ψ : (Fin n → k) → Matrix (Fin n) (Fin n) k) =
        fun v => ∑ i, v i • ψ (fun j => if i = j then 1 else 0) := funext hrep
    rw [hfun]
    exact continuous_finsetSum _ (fun i _ => (continuous_apply i).smul continuous_const)
  let Φ : Wt e → Matrix (Fin n) (Fin n) k := fun w' => 1 + ψ (w'.1 - w.1)
  have hΦ : Continuous Φ :=
    continuous_const.add (hψc.comp (continuous_subtype_val.sub continuous_const))
  have hΦw : Φ w = 1 := by simp [Φ]
  have hU : {A : Matrix (Fin n) (Fin n) k | A.det ≠ 0} ∩
      ({A : Matrix (Fin n) (Fin n) k | sm γ (A - 1)} ∩ {A | sm γ (A⁻¹ - 1)}) ∈ 𝓝 (Φ w) := by
    rw [hΦw]
    refine Filter.inter_mem ?_ (Filter.inter_mem ?_ ?_)
    · exact (isOpen_ne_fun (continuous_id.matrix_det) continuous_const).mem_nhds (by simp)
    · exact (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
        ((isOpen_sm γ).mem_nhds (by simpa using sm_zero γ))
    · exact (cont_inv_one.sub continuousAt_const).preimage_mem_nhds
        ((isOpen_sm γ).mem_nhds (by simpa using sm_zero γ))
  refine Filter.mem_of_superset (hΦ.continuousAt.preimage_mem_nhds hU) ?_
  rintro w' ⟨hdet, hs1, hs2⟩
  obtain ⟨huZ, hue, huw⟩ := hψ (w'.1 - w.1)
  have hA : Φ w' = 1 + ψ (w'.1 - w.1) := rfl
  have hmemG : (Matrix.nonsingInvUnit (Φ w') (isUnit_iff_ne_zero.mpr hdet) : GL (Fin n) k) ∈ Gs Z e := by
    refine ⟨fun a ha => ?_, ?_, ?_⟩
    · show a * Φ w' = Φ w' * a
      rw [hA, mul_add, add_mul, mul_one, one_mul, hZ.1 a ha _ huZ]
    · show Φ w' * e = e * Φ w'
      rw [hA, add_mul, mul_add, one_mul, mul_one, hZ.1 _ huZ e he]
    · show Φ w' * (1 - e) = 1 - e
      rw [hA, add_mul, one_mul, mul_sub, mul_one, hue, sub_self, add_zero]
  refine ⟨⟨_, hmemG⟩, ⟨hs1, hs2⟩, ?_⟩
  apply Subtype.ext
  rw [smul_val]
  show Φ w' *ᵥ w.1 = w'.1
  rw [hA, add_mulVec, one_mulVec, huw, mulVec_sub, w'.2, w.2]
  abel

theorem isOpen_orbit (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (h0 : dB0 Z = 0)
    (e : Matrix (Fin n) (Fin n) k) (he : e ∈ Z) (hee : e * e = e)
    (hprim : ∀ u ∈ Z, u * e = u → u ≠ 0 → ∃ u' ∈ Z, u' * e = u' ∧ u' * u = e)
    (γ : (ValueGroupWithZero k)ˣ) (w : Wt e) (hw0 : w.1 ≠ 0) :
    IsOpen {w' | ∃ g ∈ Ks Z e γ, g • w = w'} := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨g, hg, rfl⟩
  have hne : (g • w).1 ≠ 0 := by
    intro h
    apply hw0
    have h' := congrArg (fun x => ((g : GL (Fin n) k)⁻¹ : GL (Fin n) k).val *ᵥ x) h
    simp only [smul_val, mulVec_mulVec, mulVec_zero] at h'
    simpa using h'
  refine Filter.mem_of_superset (orbit_nhds Z hZ h0 e he hee hprim γ (g • w) hne) ?_
  rintro _ ⟨h, hh, rfl⟩
  exact ⟨h * g, (Ks Z e γ).mul_mem hh hg, mul_smul h g w⟩

theorem unif (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (e : Matrix (Fin n) (Fin n) k) (hee : e * e = e)
    {Y : Type*} [TopologicalSpace Y] (f : Y × Wt e → ℂ) (hf : f ∈ TF (Y × Wt e)) :
    ∃ γ : (ValueGroupWithZero k)ˣ, ∀ g ∈ Ks Z e γ, ∀ p : Y × Wt e, f (p.1, g • p.2) = f p := by
  obtain ⟨hlc, hcs⟩ := hf
  have key : ∀ᶠ A in 𝓝 (1 : Matrix (Fin n) (Fin n) k), ∀ q ∈ tsupport f,
      ∀ q' : Y × Wt e, q'.1 = q.1 → q'.2.1 = A *ᵥ q.2.1 → f q' = f q := by
    refine hcs.eventually_forall_of_forall_eventually (fun p _ => ?_)
    have hS : IsOpen {x | f x = f p} := hlc.isOpen_fiber _
    have hι : Topology.IsInducing (Prod.map id Subtype.val : Y × Wt e → Y × (Fin n → k)) :=
      Topology.IsInducing.id.prodMap
        (Topology.IsInducing.subtypeVal (t := {w : Fin n → k | e *ᵥ w = w}))
    obtain ⟨t, ht, hte⟩ := hι.isOpen_iff.mp hS
    have hH : Continuous (fun z : Matrix (Fin n) (Fin n) k × (Y × Wt e) => (z.2.1, z.1 *ᵥ z.2.2.1)) :=
      continuous_snd.fst.prodMk (continuous_fst.matrix_mulVec (continuous_subtype_val.comp continuous_snd.snd))
    have hpt : p ∈ Prod.map id Subtype.val ⁻¹' t := by
      rw [hte]
      exact rfl
    have h1 : ∀ᶠ z : Matrix (Fin n) (Fin n) k × (Y × Wt e) in 𝓝 (1, p), (z.2.1, z.1 *ᵥ z.2.2.1) ∈ t := by
      apply hH.continuousAt.preimage_mem_nhds
      apply ht.mem_nhds
      show (p.1, (1 : Matrix (Fin n) (Fin n) k) *ᵥ p.2.1) ∈ t
      rw [one_mulVec]
      exact hpt
    have hm : ∀ᶠ x in 𝓝 p, f x = f p := hS.mem_nhds rfl
    have h2 : ∀ᶠ z : Matrix (Fin n) (Fin n) k × (Y × Wt e) in 𝓝 (1, p), f z.2 = f p :=
      (continuous_snd.tendsto ((1 : Matrix (Fin n) (Fin n) k), p)).eventually hm
    filter_upwards [h1, h2] with z hz1 hz2 q' hq1 hq2
    have hq' : q' ∈ Prod.map id Subtype.val ⁻¹' t := by
      show (q'.1, q'.2.1) ∈ t
      rw [hq1, hq2]
      exact hz1
    rw [hte] at hq'
    exact (hq' : f q' = f p).trans hz2.symm
  obtain ⟨γ, hγ⟩ := nhds_one_ball key
  have hP : ∀ g ∈ Ks Z e γ, ∀ q ∈ tsupport f, f (q.1, g • q.2) = f q := fun g hg q hq =>
    hγ _ (fun i j => (hg.1 i j).1) q hq (q.1, g • q.2) rfl (smul_val Z e g q.2)
  refine ⟨γ, fun g hg p => ?_⟩
  by_cases hp : p ∈ tsupport f
  · exact hP g hg p hp
  · by_cases hp' : (p.1, g • p.2) ∈ tsupport f
    · have h' := hP g⁻¹ ((Ks Z e γ).inv_mem hg) _ hp'
      simp only [inv_smul_smul] at h'
      exact h'.symm
    · rw [image_eq_zero_of_notMem_tsupport hp', image_eq_zero_of_notMem_tsupport hp]

end PositivityTheory.RgUd.T.Nil.BasePf

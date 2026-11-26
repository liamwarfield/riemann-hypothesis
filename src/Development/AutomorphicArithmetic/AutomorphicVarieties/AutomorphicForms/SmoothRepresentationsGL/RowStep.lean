module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.RowStep
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem mul_rowM_apply {R : Type} [CommRing R] {n : ℕ} (m : Fin n) (ξ : Fin n → R)
    (q : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (q * rowM m ξ) i j
      = (if j = m then 0 else q i j) + q i m * (if j ≤ m then ξ j else 0) := by
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ m)]
  have hs : ∑ k ∈ Finset.univ.erase m, q i k * rowM m ξ k j = if j = m then 0 else q i j := by
    have hk1 : ∀ k ∈ Finset.univ.erase m,
        q i k * rowM m ξ k j = q i k * (1 : Matrix (Fin n) (Fin n) R) k j := by
      intro k hk
      have hkm : k ≠ m := Finset.ne_of_mem_erase hk
      simp [rowM, hkm]
    rw [Finset.sum_congr rfl hk1]
    split_ifs with hjm
    · apply Finset.sum_eq_zero
      intro k hk
      rw [Matrix.one_apply_ne (by rw [hjm]; exact Finset.ne_of_mem_erase hk), mul_zero]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        rw [Matrix.one_apply_ne hb, mul_zero]
      · intro hj
        exact absurd (Finset.mem_erase.mpr ⟨hjm, Finset.mem_univ j⟩) hj
  rw [hs, add_comm]
  congr 1
  by_cases hjm : j ≤ m
  · simp [rowM, hjm]
  · have hmj : m ≠ j := fun h => hjm (le_of_eq h.symm)
    simp [rowM, hjm, Matrix.one_apply_ne hmj]

theorem UpperTheory.V.Af.Smo.rowStep :
    UpperTheory.V.Af.Smo.RowStep := by
  unfold UpperTheory.V.Af.Smo.RowStep IsY
  intro R _ n m p s hp hs
  have key : ∀ i j, (p : Matrix (Fin n) (Fin n) R) i j
      = (if j = m then 0 else ((p * s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j)
        + ((p * s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i m
          * (if j ≤ m then (p : Matrix (Fin n) (Fin n) R) m j else 0) := by
    intro i j
    have h := mul_rowM_apply m ((p : Matrix (Fin n) (Fin n) R) m)
      ((p * s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j
    rw [← hs, ← Units.val_mul, inv_mul_cancel_right] at h
    exact h
  have hu : ((s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) m m
      * (p : Matrix (Fin n) (Fin n) R) m m = 1 := by
    have h := mul_rowM_apply m ((p : Matrix (Fin n) (Fin n) R) m)
      ((s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) m m
    rw [← hs, ← Units.val_mul, inv_mul_cancel] at h
    simpa using h.symm
  generalize ((s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) m m = t at hu
  generalize ((p * s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Q at key ⊢
  generalize (p : Matrix (Fin n) (Fin n) R) = P at key hu hp
  intro i hi
  rcases eq_or_lt_of_le hi with h | h
  · have him : i = m := Fin.ext h.symm
    rw [him]
    have k := key m m
    rw [if_pos rfl, if_pos le_rfl, zero_add] at k
    have hQ : Q m m = 1 := by linear_combination (-t) * k + (1 - Q m m) * hu
    refine ⟨hQ, fun j hj => ?_⟩
    have k2 := key m j
    rw [if_neg (ne_of_lt hj), if_pos (le_of_lt hj), hQ, one_mul] at k2
    linear_combination -k2
  · have hi1 : (m : ℕ) + 1 ≤ (i : ℕ) := h
    obtain ⟨hpi, hpj⟩ := hp i hi1
    have hmi : m < i := h
    have k := key i m
    rw [if_pos rfl, if_pos le_rfl, zero_add, hpj m hmi] at k
    have hQm : Q i m = 0 := by linear_combination (-Q i m) * hu - t * k
    constructor
    · have k2 := key i i
      rw [if_neg (ne_of_gt hmi), if_neg (not_le.mpr hmi), mul_zero, add_zero, hpi] at k2
      exact k2.symm
    · intro j hj
      have k2 := key i j
      rw [hpj j hj] at k2
      by_cases hjm : j = m
      · rw [hjm]
        exact hQm
      · rw [if_neg hjm, hQm, zero_mul, add_zero] at k2
        exact k2.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LocDual
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem mul_inv_lt_mul_inv_mul_inv_of_le_of_lt_one {G : Type} [LinearOrderedCommGroupWithZero G] (ua g ux p : G) (hua : ua ≠ 0)
    (hg : 0 < g) (hgx : g ≤ ux) (hp : p < 1) (hp0 : p ≠ 0) :
    ua * ux⁻¹ < ua * g⁻¹ * p⁻¹ := by
  have h1 : ux⁻¹ ≤ g⁻¹ := inv_anti₀ hg hgx
  have h2 : ua * ux⁻¹ ≤ ua * g⁻¹ := by gcongr
  have h3 : 1 < p⁻¹ := one_lt_inv₀ (zero_lt_iff.mpr hp0) |>.mpr hp
  have h4 : 0 < ua * g⁻¹ := by
    apply zero_lt_iff.mpr
    exact mul_ne_zero hua (inv_ne_zero hg.ne')
  calc ua * ux⁻¹ ≤ ua * g⁻¹ := h2
    _ = ua * g⁻¹ * 1 := (mul_one _).symm
    _ < ua * g⁻¹ * p⁻¹ := mul_lt_mul_of_pos_left h3 h4

private theorem mul_lt_of_lt_mul_inv_of_lt {G : Type} [LinearOrderedCommGroupWithZero G] (q y r g1 : G) (hr : 0 < r)
    (hy : y < r) (hq : q < g1 * r⁻¹) : q * y < g1 := by
  calc q * y ≤ q * r := by gcongr
    _ < g1 * r⁻¹ * r := mul_lt_mul_of_pos_right hq hr
    _ = g1 := by rw [mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]

theorem UpperTheory.V.Af.Smo.locDual :
    UpperTheory.V.Af.Smo.LocDual := by
  intro E _ _ w ψ hψ V hV
  obtain ⟨a, ha⟩ : ∃ a, ψ a ≠ 1 := by
    by_contra h
    push_neg at h
    exact hψ (AddChar.ext _ _ fun x => by simpa using h x)
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hV
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : HeightOneSpectrum.adicCompletion E w)
  obtain ⟨γ₁, hγ₁⟩ := Valued.mem_nhds_zero.mp hC0
  obtain ⟨π₀, hπ₀⟩ := HeightOneSpectrum.valuation_exists_uniformizer E w
  have hvπ : Valued.v (π₀ : HeightOneSpectrum.adicCompletion E w) = WithZero.exp (-1 : ℤ) := by
    simp [hπ₀]
  have hπ0 : (π₀ : HeightOneSpectrum.adicCompletion E w) ≠ 0 := by
    intro h
    rw [h, map_zero] at hvπ
    exact WithZero.zero_ne_coe hvπ
  have hπ1 : Valued.v.restrict (π₀ : HeightOneSpectrum.adicCompletion E w) < 1 := by
    rw [Valuation.restrict_lt_one_iff, hvπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπn : Valued.v.restrict (π₀ : HeightOneSpectrum.adicCompletion E w) ≠ 0 := by
    rw [Ne, Valuation.restrict_eq_zero_iff, hvπ]
    exact WithZero.exp_ne_zero
  have hua : Valued.v.restrict a ≠ 0 := by simp [ha0]
  set R := Units.mk0 (Valued.v.restrict a * (γ : _)⁻¹ *
    (Valued.v.restrict (π₀ : HeightOneSpectrum.adicCompletion E w))⁻¹)
    (mul_ne_zero (mul_ne_zero hua γ⁻¹.ne_zero) (inv_ne_zero hπn)) with hR
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hπ1 (γ₁ * R⁻¹)
  refine ⟨Valued.v.restrict.ltAddSubgroup R, ?_, ?_, ?_⟩
  · rw [Valuation.coe_ltAddSubgroup]
    exact Valued.isOpen_ball _ _
  · rw [Valuation.coe_ltAddSubgroup]
    refine IsCompact.of_isClosed_subset
      (hC.image (continuous_const.mul continuous_id :
        Continuous fun z : HeightOneSpectrum.adicCompletion E w =>
          ((π₀ : HeightOneSpectrum.adicCompletion E w) ^ n)⁻¹ * z))
      (Valued.isClosed_ball _ _) ?_
    intro y hy
    refine ⟨(π₀ : HeightOneSpectrum.adicCompletion E w) ^ n * y, hγ₁ ?_, ?_⟩
    · show Valued.v.restrict ((π₀ : HeightOneSpectrum.adicCompletion E w) ^ n * y) < γ₁
      rw [map_mul, map_pow]
      refine mul_lt_of_lt_mul_inv_of_lt _ _ _ _ (zero_lt_iff.mpr R.ne_zero) hy ?_
      simpa using hn
    · exact inv_mul_cancel_left₀ (pow_ne_zero n hπ0) y
  · intro x hx
    by_contra hxV
    have hxg : (γ : _) ≤ Valued.v.restrict x := by
      by_contra h
      push_neg at h
      exact hxV (hγ h)
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hxg
      exact γ.ne_zero (le_antisymm hxg zero_le')
    have hy : a * x⁻¹ ∈ Valued.v.restrict.ltAddSubgroup R := by
      rw [← SetLike.mem_coe, Valuation.coe_ltAddSubgroup]
      show Valued.v.restrict (a * x⁻¹) < R
      rw [map_mul, map_inv₀, hR, Units.val_mk0, Units.val_inv_eq_inv_val]
      exact mul_inv_lt_mul_inv_mul_inv_of_le_of_lt_one _ _ _ _ hua (zero_lt_iff.mpr γ.ne_zero) hxg hπ1 hπn
    have h1 := hx _ hy
    rw [mul_comm a, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul] at h1
    exact ha h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LocKir
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem exists_conj_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenSubgroup G) (s : Finset G) : ∃ U₁ : OpenSubgroup G, ∀ u ∈ U₁, ∀ x ∈ s, x⁻¹ * u * x ∈ U := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, by simp⟩
  | insert a s _ ih =>
    obtain ⟨V, hV⟩ := ih
    have hc : Continuous (MulAut.conj a⁻¹).toMonoidHom := by
      change Continuous fun u : G => a⁻¹ * u * a⁻¹⁻¹
      fun_prop
    refine ⟨V ⊓ U.comap (MulAut.conj a⁻¹).toMonoidHom hc, fun u hu x hx => ?_⟩
    obtain ⟨h1, h2⟩ := OpenSubgroup.mem_inf.1 hu
    rcases Finset.mem_insert.1 hx with rfl | hx
    · have h3 : x⁻¹ * u * x⁻¹⁻¹ ∈ U := OpenSubgroup.mem_comap.1 h2
      rwa [inv_inv] at h3
    · exact hV u h1 x hx

private theorem supN_one {R : Type} [CommRing R] {n : ℕ} : supN (1 : Matrix (Fin n) (Fin n) R) = 0 := by
  unfold supN
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · exact Matrix.one_apply_ne (by rintro rfl; omega)
  · rfl

private theorem rowM_one {R : Type} [CommRing R] {n : ℕ} (m : Fin n) :
    rowM m ((1 : Matrix (Fin n) (Fin n) R) m) = 1 := by
  ext i j
  simp only [rowM, Matrix.of_apply]
  split_ifs with h
  · rw [h.1]
  · rfl

private theorem isWh_comb {R : Type} [CommRing R] {n : ℕ} {ψ : R → ℂ} {W : GL (Fin n) R → ℂ} (hW : IsWh ψ W)
    (c : GL (Fin n) R →₀ ℂ) : IsWh ψ (comb c W) := by
  intro ν hν g
  unfold comb
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [mul_assoc, hW ν hν]
  ring

theorem UpperTheory.V.Af.Smo.locKir :
    UpperTheory.V.Af.Smo.ColConj → UpperTheory.V.Af.Smo.RowStep → UpperTheory.V.Af.Smo.LocStep → UpperTheory.V.Af.Smo.LocKir := by
  classical
  intro hcol hrow hstep E _ _ w ψ h0 h1 n m hm U
  induction m with
  | zero =>
    refine ⟨Finsupp.single 1 1, fun p => ψ (supN p.val), ?_, fun W hW _ p hp => ?_⟩
    · simp only [Units.val_one, supN_one, AddChar.map_zero_eq_one]
    · unfold comb
      rw [Finsupp.sum_single_index (by simp), one_mul, hW p hp]
  | succ m ih =>
    obtain ⟨c₀, H₀, hH₀, hc₀⟩ := ih (by omega)
    obtain ⟨U₁, hU₁⟩ := exists_conj_le U c₀.support
    let m' : Fin n := ⟨m, by omega⟩
    obtain ⟨c₁, h, hh1, hh, hc₁⟩ := hstep E w ψ h0 h1 n m' hm U₁
    obtain ⟨c, -, hc⟩ := exists_comb_comb c₁ c₀
    have hσ : ∃ σ : (Fin n → w.adicCompletion E) → GL (Fin n) (w.adicCompletion E),
        ∀ ξ (s : GL (Fin n) (w.adicCompletion E)), s.val = rowM m' ξ → σ ξ = s := by
      refine ⟨fun ξ => if e : ∃ s : GL (Fin n) (w.adicCompletion E), s.val = rowM m' ξ then e.choose else 1,
        fun ξ s hs => ?_⟩
      have e : ∃ s : GL (Fin n) (w.adicCompletion E), s.val = rowM m' ξ := ⟨s, hs⟩
      simp only [dif_pos e]
      exact Units.ext (e.choose_spec.trans hs.symm)
    obtain ⟨σ, hσ⟩ := hσ
    refine ⟨c, fun p => h (p.val m') * H₀ (p * (σ (p.val m'))⁻¹), ?_, fun W hW hWU p hp => ?_⟩
    · have : σ ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) m') = 1 := hσ _ 1 (rowM_one m').symm
      simp only [Units.val_one, hh1, this, inv_one, mul_one, one_mul, hH₀]
    · have hinv : ∀ g, ∀ u ∈ U₁, comb c₀ W (g * u) = comb c₀ W g := by
        intro g u hu
        unfold comb
        refine Finsupp.sum_congr fun x hx => ?_
        rw [← hWU (g * x) _ (hU₁ u hu x hx)]
        congr 2
        group
      rw [hc, hc₁ (comb c₀ W) hinv p (p.val m') ?_]
      · by_cases hz : h (p.val m') = 0
        · simp only [hz, zero_mul]
        · obtain ⟨s, hsU, hs⟩ := hh _ hz
          simp only [hσ _ s hs]
          rw [← hinv p s⁻¹ (U₁.inv_mem hsU), hc₀ W hW hWU _ (hrow _ n m' p s hp hs), mul_assoc]
      · intro u t ht
        obtain ⟨ν, hν, e1, e2⟩ := hcol _ n m' hm p hp u
        have e : p * t = ν * p := Units.ext (by rw [Units.val_mul, Units.val_mul, ht, e2])
        rw [e, isWh_comb hW c₀ ν hν, e1]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.IsYBlockGL
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology


open GroundTheory.Automorphic.FourierWhittaker in
private theorem isY_blockGL {K : Type} [Field K] {n k : ℕ} (hk : k < n) (γ : GL (Fin k) K) :
    IsY (n - 1) (blockGL hk.le γ : GL (Fin n) K).val := by
  intro i hi
  have hik : ¬ i.val < k := by omega
  refine ⟨?_, fun j hj => ?_⟩
  · rw [coe_blockGL, blockMat_apply, dite_eq_right hik, if_pos rfl]
  · rw [coe_blockGL, blockMat_apply, dite_eq_right hik, if_neg hj.ne']


open GroundTheory.Automorphic.FourierWhittaker in
open scoped NumberField.AdeleRing in
private theorem step {K : Type} [Field K] [NumberField K] {n : ℕ} {ϕ : AdelicGLn.AdelicGL K n → ℂ}
    (hc : Continuous ϕ) (hl : IsLeftInvariant ϕ) (hcusp : AutomorphicForm.IsCuspidal ϕ)
    {V : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n)}
    (hV : ∀ g, ∀ v ∈ V, ϕ (g * finEmb K n v) = ϕ g) {k : ℕ} (hk0 : 0 < k) (hk : k < n)
    (g : AdelicGLn.AdelicGL K n)
    (h0 : ∀ γ : GL (Fin k) K, partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk.le γ) * g) = 0) :
    partialCoeff ϕ (k + 1) g = 0 := by
  classical
  obtain ⟨δ, hδ, hδV⟩ := exists_integer_colGL_mem (n := n) k V (AdelicGLn.prodEquiv K n g).2
  have hδK : (algebraMap (𝓞 K) K δ) ≠ 0 := by
    simpa using (RingOfIntegers.coe_ne_zero_iff).2 hδ
  set u : Kˣ := Units.mk0 _ hδK
  set D := AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) with hD
  have hconj : ∀ w : Fin k → 𝔸[K], colGL k w * D =
      D * colGL k (fun i => algebraMap K 𝔸[K] u * w i) := by
    intro w
    simp only [D]
    rw [diagonal_blockGL, colGL_mul_blockGL hk, mulVec_map_inv, ← map_inv, inv_inv, coe_scalarGL,
      matVec_scalar]
  set F : (Fin k → 𝔸[K]) → ℂ := fun x => partialCoeff ϕ (k + 1) (colGL k x * (D * g))
  have hip : IsIntegralPeriodic F := by
    refine ⟨(continuous_partialCoeff hc _).comp ((continuous_colGL k).mul continuous_const),
      fun ξ hξ x => ?_, fun x z hz => ?_⟩
    · obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
      simp only [F]
      rw [colGL_add, mul_assoc, ← diagonal_colGL, partialCoeff_succ_diagonal_colGL hl hk]
    · have e1 : (fun i => algebraMap K 𝔸[K] (u : K) * GroundTheory.Global.finiteAdeleInr (z i)) =
          fun i => GroundTheory.Global.finiteAdeleInr (algebraMap K (FiniteAdeleRing (𝓞 K) K)
            (algebraMap (𝓞 K) K δ) * z i) := by
        funext i; rw [GroundTheory.Global.algebraMap_mul_finiteAdeleInr]; rfl
      change partialCoeff ϕ (k + 1)
          (colGL k (x + fun i => GroundTheory.Global.finiteAdeleInr (z i)) * (D * g)) =
        partialCoeff ϕ (k + 1) (colGL k x * (D * g))
      rw [colGL_add, mul_assoc (colGL k x),
        ← mul_assoc (colGL k fun i => GroundTheory.Global.finiteAdeleInr (z i)), hconj, e1,
        colGL_finiteAdeleInr, mul_assoc D, finEmb_mul_eq, ← mul_assoc,
        ← mul_assoc, partialCoeff_mul_finEmb hV _ _ (hδV z hz), mul_assoc]
  have hcoeff : vecCoeff F = 0 := by
    funext ξ
    by_cases hξ : ξ = 0
    · rw [hξ]
      exact vecCoeff_zero_of_isCuspidal hc hl hcusp hk0 hk (D * g)
    · have h1 := partialCoeff_diagonal_blockGL_eq_vecCoeff hl hk (rowCompletion ξ) (D * g)
      rw [vecMul_rowCompletion hξ] at h1
      refine h1.symm.trans ?_
      rw [hD, ← mul_assoc, ← map_mul, ← map_mul]
      exact h0 _
  have H := hip.hasSum_vecCoeff (hcoeff ▸ summable_zero) 0
  simp only [hcoeff, Pi.zero_apply, zero_mul] at H
  have hF0 : F 0 = 0 := (hasSum_zero.unique H).symm
  rw [← partialCoeff_succ_diagonal_blockGL hl hk (scalarGL k u⁻¹) g]
  change partialCoeff ϕ (k + 1) (D * g) = 0
  simpa [F, colGL_zero] using hF0

open GroundTheory.Automorphic.FourierWhittaker in
theorem UpperTheory.V.Af.Smo.injP :
    UpperTheory.V.Af.Smo.InjP := by
  intro E _ _ n hn f hf X hX hW
  obtain ⟨V, hV⟩ := hf.level
  rw [← Fb.finEmb_eq] at hV
  have key : ∀ k, k < n → ∀ g ∈ X, partialCoeff f (k + 1) g = 0 := by
    intro k
    induction k with
    | zero =>
      intro _ g hg
      exact (whittaker_eq_partialCoeff hf.cont hn g).symm.trans (hW g hg)
    | succ m ih =>
      intro hm g hg
      exact step hf.cont hf.left hf.cusp hV (Nat.succ_pos m) hm g fun γ =>
        ih (by omega) _ (hX _ (isY_blockGL hm γ) g hg)
  intro g hg
  have := key (n - 1) (by omega) g hg
  rwa [Nat.sub_add_cancel hn, partialCoeff_self] at this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SchOfClosed
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.schOfClosed :
    UpperTheory.V.Af.Smo.SchOfClosed := by
  intro X _ _ _ A hA
  have b : Module.Basis (Fin (Module.finrank ℝ X)) ℝ X := Module.finBasis ℝ X
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank ℝ X) → (X →L[ℝ] ℝ), ∀ i x, c i x = b.repr x i :=
    ⟨fun i => LinearMap.toContinuousLinearMap (b.coord i), fun i x => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : Fin (Module.finrank ℝ X) → (ℂ →L[ℝ] (X →L[ℝ] ℂ)),
      ∀ i z v, L i z v = c i v • z :=
    ⟨fun i => ContinuousLinearMap.smulRightL ℝ X ℂ (c i), fun i z v => rfl⟩
  have hsm : ∀ n : ℕ, ∀ f ∈ A, ContDiff ℝ n f := by
    intro n
    induction n with
    | zero => intro f hf; exact contDiff_zero.2 (hA f hf).2.1.continuous
    | succ n ih =>
      intro f hf
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
      refine ⟨(hA f hf).2.1, by simp, ?_⟩
      rw [contDiff_clm_apply_iff]
      intro v
      exact ih _ ((hA f hf).2.2.1 v)
  have hinf : ∀ f ∈ A, ContDiff ℝ ∞ f := fun f hf => contDiff_infty.2 fun n => hsm n f hf
  have hx : ∀ x : X, ‖x‖ ≤ ∑ i, ‖b i‖ * ‖c i x‖ := by
    intro x
    calc ‖x‖ = ‖∑ i, b.repr x i • b i‖ := by rw [b.sum_repr]
      _ ≤ ∑ i, ‖b.repr x i • b i‖ := norm_sum_le _ _
      _ = ∑ i, ‖b i‖ * ‖c i x‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_smul, hc, mul_comm]
  have h0 : ∀ k : ℕ, ∀ f ∈ A, ∃ C, ∀ x, ‖x‖ ^ k * ‖f x‖ ≤ C := by
    intro k
    induction k with
    | zero =>
      intro f hf
      obtain ⟨C, hC⟩ := (hA f hf).1
      exact ⟨C, fun x => by simpa using hC x⟩
    | succ k ih =>
      intro f hf
      choose C hC using fun i => ih _ ((hA f hf).2.2.2 (c i))
      refine ⟨∑ i, ‖b i‖ * C i, fun x => ?_⟩
      calc ‖x‖ ^ (k + 1) * ‖f x‖ = ‖x‖ * (‖x‖ ^ k * ‖f x‖) := by ring
        _ ≤ (∑ i, ‖b i‖ * ‖c i x‖) * (‖x‖ ^ k * ‖f x‖) := by gcongr; exact hx x
        _ = ∑ i, ‖b i‖ * (‖x‖ ^ k * ‖(↑(c i x) : ℂ) * f x‖) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [norm_mul, Complex.norm_real]
            ring
        _ ≤ ∑ i, ‖b i‖ * C i := by
            gcongr with i
            exact hC i x
  have hd : ∀ n k : ℕ, ∀ f ∈ A, ∃ C, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
    intro n
    induction n with
    | zero =>
      intro k f hf
      obtain ⟨C, hC⟩ := h0 k f hf
      exact ⟨C, fun x => by rw [norm_iteratedFDeriv_zero]; exact hC x⟩
    | succ n ih =>
      intro k f hf
      obtain ⟨g, hg⟩ : ∃ g : Fin (Module.finrank ℝ X) → X → ℂ, ∀ i x, g i x = fderiv ℝ f x (b i) :=
        ⟨fun i x => fderiv ℝ f x (b i), fun _ _ => rfl⟩
      have hgA : ∀ i, g i ∈ A := by
        intro i
        have : g i = fun x => fderiv ℝ f x (b i) := funext (hg i)
        rw [this]
        exact (hA f hf).2.2.1 (b i)
      have hfd : fderiv ℝ f = fun x => ∑ i, L i (g i x) := by
        funext x
        ext v
        rw [ContinuousLinearMap.sum_apply]
        simp only [hL, hg, hc]
        conv_lhs => rw [← b.sum_repr v]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [map_smul]
      have hsum : iteratedFDeriv ℝ n (fun x => ∑ i, L i (g i x))
          = ∑ i, iteratedFDeriv ℝ n (fun y => L i (g i y)) :=
        iteratedFDeriv_sum (f := fun i y => L i (g i y)) (u := Finset.univ)
          (fun i _ => (L i).contDiff.comp (hsm n _ (hgA i)))
      choose C hC using fun i => ih k (g i) (hgA i)
      refine ⟨∑ i, ‖L i‖ * C i, fun x => ?_⟩
      rw [← norm_iteratedFDeriv_fderiv, hfd, hsum, Finset.sum_apply]
      calc ‖x‖ ^ k * ‖∑ i, iteratedFDeriv ℝ n (fun y => L i (g i y)) x‖
          ≤ ‖x‖ ^ k * ∑ i, ‖iteratedFDeriv ℝ n (fun y => L i (g i y)) x‖ := by
            gcongr
            exact norm_sum_le _ _
        _ ≤ ‖x‖ ^ k * ∑ i, ‖L i‖ * ‖iteratedFDeriv ℝ n (g i) x‖ := by
            gcongr with i
            exact (L i).norm_iteratedFDeriv_comp_left (hsm n _ (hgA i)).contDiffAt le_rfl
        _ = ∑ i, ‖L i‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (g i) x‖) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ ≤ ∑ i, ‖L i‖ * C i := by
            gcongr with i
            exact hC i x
  intro f hf
  exact ⟨⟨f, hinf f hf, fun k n => hd n k f hf⟩, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ColConj
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem inv_row {R : Type} [CommRing R] {n : ℕ} (m : ℕ) (k : Fin n) (hk : k.val = m + 1) (p : GL (Fin n) R)
    (hp : IsY (m + 1) p.val) : (∀ j, j < k → (p⁻¹).val k j = 0) ∧ (p⁻¹).val k k = 1 := by
  have h1 : ∀ j, j < k → (p⁻¹).val k j = 0 := by
    have hb : p.val.BlockTriangular (fun i : Fin n => if i.val ≤ m then 0 else i.val) := by
      intro i j hij
      dsimp only at hij
      have hi : m + 1 ≤ i.val := by split_ifs at hij <;> omega
      refine (hp i hi).2 j ?_
      rw [Fin.lt_def]
      split_ifs at hij <;> omega
    haveI : Invertible p.val := p.invertible
    have hq := Matrix.blockTriangular_inv_of_blockTriangular hb
    intro j hj
    rw [Matrix.coe_units_inv]
    refine hq ?_
    rw [Fin.lt_def] at hj
    dsimp only
    split_ifs <;> omega
  refine ⟨h1, ?_⟩
  have h2 : ((p⁻¹).val * p.val) k k = 1 := by rw [Units.inv_mul, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single k, (hp k hk.ge).1, mul_one] at h2
  · exact h2
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [h1 j h, zero_mul]
    · rw [(hp j (by rw [Fin.lt_def] at h; omega)).2 k h, mul_zero]
  · simp

theorem UpperTheory.V.Af.Smo.colConj :
    UpperTheory.V.Af.Smo.ColConj := by
  intro R _ n m hm p hp u
  set k : Fin n := ⟨m.val + 1, hm⟩ with hkdef
  have hk : k.val = m.val + 1 := rfl
  obtain ⟨hb0, hb1⟩ := inv_row m.val k hk p hp
  set c : Fin n → R := fun i => if i ≤ m then u i else 0 with hc
  set a : Fin n → R := p.val *ᵥ c with ha
  set b : Fin n → R := (p⁻¹).val k with hb
  have ha0 : ∀ i, m < i → a i = 0 := by
    intro i hi
    change ∑ j, p.val i j * c j = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j ≤ m
    · rw [(hp i hi).2 j (lt_of_le_of_lt hj hi), zero_mul]
    · simp [hc, hj]
  have hab : ∀ i j, j ≤ i → a i * b j = 0 := by
    intro i j hij
    by_cases hi : m < i
    · rw [ha0 i hi, zero_mul]
    · rw [hb0 j (by rw [Fin.lt_def] at hi ⊢; rw [Fin.le_def] at hij; omega), mul_zero]
  have hdot : b ⬝ᵥ a = 0 := Finset.sum_eq_zero fun i _ => by rw [mul_comm]; exact hab i i le_rfl
  have hsq : vecMulVec a b * vecMulVec a b = 0 := by
    rw [vecMulVec_mul_vecMulVec, hdot, zero_smul, vecMulVec_zero]
  refine ⟨⟨1 + vecMulVec a b, 1 - vecMulVec a b, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [add_mul, mul_sub, mul_sub, hsq]; simp
  · rw [sub_mul, mul_add, mul_add, hsq]; simp
  · intro i _
    refine ⟨?_, fun j hj => ?_⟩
    · simp [vecMulVec_apply, hab i i le_rfl]
    · simp [vecMulVec_apply, hab i j hj.le, Matrix.one_apply_ne hj.ne']
  · have : dotLe m (p.val m) u = a m := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [hc]
    rw [this]
    unfold supN
    rw [Finset.sum_eq_single m, Finset.sum_eq_single k]
    · have : m ≠ k := fun h => by have := congrArg Fin.val h; omega
      simp [hk, vecMulVec_apply, hb1, Matrix.one_apply_ne this]
    · intro j _ hj
      rw [if_neg fun h => hj (Fin.ext (by omega))]
    · simp
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      split_ifs with h
      · have hne : i ≠ j := fun e => by have := congrArg Fin.val e; omega
        have : a i * b j = 0 := by
          rcases lt_or_gt_of_ne hi with h' | h'
          · rw [hb0 j (by rw [Fin.lt_def] at h' ⊢; omega), mul_zero]
          · rw [ha0 i h', zero_mul]
        simp [vecMulVec_apply, this, Matrix.one_apply_ne hne]
      · rfl
    · simp
  · have h1 : colM m u = 1 + vecMulVec c (Pi.single k 1) := by
      unfold colM
      congr 1
      ext i j
      by_cases hj : j = k
      · subst hj
        simp [vecMulVec_apply, hc, hk]
      · have : j.val ≠ m.val + 1 := fun h => hj (Fin.ext h)
        simp [vecMulVec_apply, hj, this]
    have h2 : b ᵥ* p.val = Pi.single k 1 := by
      ext j
      have : ((p⁻¹).val * p.val) k j = (1 : Matrix (Fin n) (Fin n) R) k j := by rw [Units.inv_mul]
      rw [Matrix.one_apply] at this
      rw [Pi.single_apply, ← if_congr eq_comm rfl rfl, ← this]
      rfl
    change p.val * colM m u = (1 + vecMulVec a b) * p.val
    rw [h1, mul_add, add_mul, mul_one, one_mul, mul_vecMulVec, vecMulVec_mul, h2]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.PftMul
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

section SlopeTestRemainingChoices

variable {V M : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup M] [NormedSpace ℝ M]

end SlopeTestRemainingChoices

open LineDeriv in
theorem UpperTheory.V.Af.Smo.pftMul :
    UpperTheory.V.Af.Smo.PftMul := by
  unfold UpperTheory.V.Af.Smo.PftMul
  intro V M _ _ _ _ _ _ _ _ G
  have hbd : ∃ C, ∀ (z : V × M), ‖pft (⇑G) z‖ ≤ C := by
    set k : ℕ := Module.finrank ℝ V + 1 with hk
    set C0 : ℝ := 2 ^ k * ((Finset.Iic (k, 0)).sup fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) G with hC0
    have hint : Integrable (fun ξ : V ↦ (1 + ‖ξ‖) ^ (-(k : ℝ))) := by
      apply integrable_one_add_norm
      rw [hk]; push_cast; linarith
    refine ⟨C0 * ∫ ξ : V, (1 + ‖ξ‖) ^ (-(k : ℝ)), fun z ↦ ?_⟩
    have hpt : ∀ ξ : V, ‖G (ξ, z.2)‖ ≤ C0 * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
      intro ξ
      have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (le_refl k) (le_refl 0) G (ξ, z.2)
      rw [norm_iteratedFDeriv_zero] at h
      have hpos : 0 < 1 + ‖ξ‖ := by positivity
      have hn : ‖ξ‖ ≤ ‖((ξ, z.2) : V × M)‖ := norm_fst_le ((ξ, z.2) : V × M)
      have hle : (1 + ‖ξ‖) ^ k ≤ (1 + ‖((ξ, z.2) : V × M)‖) ^ k := by
        gcongr
      rw [Real.rpow_neg hpos.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      calc ‖G (ξ, z.2)‖ * (1 + ‖ξ‖) ^ k ≤ (1 + ‖((ξ, z.2) : V × M)‖) ^ k * ‖G (ξ, z.2)‖ := by
            rw [mul_comm]; gcongr
        _ ≤ C0 := h
    calc ‖pft (⇑G) z‖ = ‖∫ ξ : V, 𝐞 (-⟪ξ, z.1⟫) • G (ξ, z.2)‖ := by
          simp only [pft, Real.fourier_eq]
      _ ≤ ∫ ξ : V, ‖𝐞 (-⟪ξ, z.1⟫) • G (ξ, z.2)‖ := norm_integral_le_integral_norm _
      _ = ∫ ξ : V, ‖G (ξ, z.2)‖ := by simp [Circle.norm_smul]
      _ ≤ ∫ ξ : V, C0 * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
          apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) (hint.const_mul C0)
          exact Filter.Eventually.of_forall hpt
      _ = C0 * ∫ ξ : V, (1 + ‖ξ‖) ^ (-(k : ℝ)) := integral_const_mul _ _
  refine ⟨hbd, fun l ↦ ?_⟩
  set l1 : V →L[ℝ] ℝ := l.comp (ContinuousLinearMap.inl ℝ V M) with hl1
  set w : V := (InnerProductSpace.toDual ℝ V).symm l1 with hw
  have hwl : ∀ ξ : V, ⟪ξ, w⟫ = l1 ξ := by
    intro ξ
    rw [real_inner_comm, hw, InnerProductSpace.toDual_symm_apply]
  set L2 : V × M →L[ℝ] ℂ := Complex.ofRealCLM.comp
    (l.comp ((ContinuousLinearMap.inr ℝ V M).comp (ContinuousLinearMap.snd ℝ V M))) with hL2
  have hL2t : Function.HasTemperateGrowth (⇑L2) := L2.hasTemperateGrowth
  set c : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹ with hc
  refine ⟨c • LineDeriv.lineDerivOp ((w, (0 : M)) : V × M) G + SchwartzMap.smulLeftCLM ℂ (⇑L2) G, ?_⟩
  funext z
  obtain ⟨v, m⟩ := z
  have hg : Function.HasTemperateGrowth (fun ξ : V => (ξ, m)) := by
    have h1 : Function.HasTemperateGrowth (fun ξ : V => ((ContinuousLinearMap.inl ℝ V M) ξ + ((0 : V), m))) :=
      (ContinuousLinearMap.inl ℝ V M).hasTemperateGrowth.add (Function.HasTemperateGrowth.const _)
    convert h1 using 2 with ξ
    simp
  have hgu : ∃ (k : ℕ) (C : ℝ), ∀ ξ : V, ‖ξ‖ ≤ C * (1 + ‖((ξ, m) : V × M)‖) ^ k := by
    refine ⟨1, 1, fun ξ ↦ ?_⟩
    have hn : ‖ξ‖ ≤ ‖((ξ, m) : V × M)‖ := norm_fst_le ((ξ, m) : V × M)
    simp only [pow_one, one_mul]
    linarith
  set S : 𝓢(V, ℂ) := SchwartzMap.compCLM ℝ hg hgu G with hS
  have hSa : ∀ ξ, S ξ = G (ξ, m) := fun ξ ↦ by
    rw [hS, SchwartzMap.compCLM_apply]; rfl
  have hder : ∀ ξ : V, fderiv ℝ (⇑S) ξ w = fderiv ℝ (⇑G) (ξ, m) (w, 0) := by
    intro ξ
    have hgd : HasFDerivAt (fun η : V => ((η, m) : V × M)) ((ContinuousLinearMap.id ℝ V).prod 0) ξ :=
      (hasFDerivAt_id ξ).prodMk (hasFDerivAt_const m ξ)
    have hGd : HasFDerivAt (⇑G) (fderiv ℝ (⇑G) (ξ, m)) (ξ, m) := (G.differentiableAt).hasFDerivAt
    have hc' := hGd.comp ξ hgd
    have hSf : (⇑S) = (⇑G) ∘ (fun η : V => ((η, m) : V × M)) := by
      funext η; exact hSa η
    rw [hSf, hc'.fderiv]
    simp
  have key : (fun ξ : V => (c • LineDeriv.lineDerivOp ((w, (0 : M)) : V × M) G + SchwartzMap.smulLeftCLM ℂ (⇑L2) G) (ξ, m))
      = ⇑(c • LineDeriv.lineDerivOp w S + ((l (0, m) : ℝ) : ℂ) • S) := by
    funext ξ
    simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hL2t,
      SchwartzMap.lineDerivOp_apply_eq_fderiv, hder, hSa]
    simp [hL2, smul_eq_mul]
  simp only [pft]
  rw [key, ← SchwartzMap.fourier_coe]
  simp only [FourierTransform.fourier_add, FourierTransform.fourier_smul, SchwartzMap.fourier_lineDerivOp_eq]
  have hSf' : (fun ξ : V => G (ξ, m)) = ⇑S := by
    funext ξ; exact (hSa ξ).symm
  have hit : Function.HasTemperateGrowth (fun x : V ↦ ⟪x, w⟫) := ((innerSL ℝ).flip w).hasTemperateGrowth
  rw [hSf', ← SchwartzMap.fourier_coe]
  simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hit]
  simp only [hwl]
  have hlv : l (v, m) = l1 v + l (0, m) := by
    rw [hl1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, ← map_add (f := _)]
    simp
  rw [hlv, hc]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [smul_eq_mul, Complex.real_smul]
  field_simp
  push_cast
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.HalfBound
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.schTw :
    UpperTheory.V.Af.Smo.SchTensor → UpperTheory.V.Af.Smo.SchTw := by
  intro hT V M _ _ _ _ _ _ A e
  obtain ⟨δ, hδ, hAδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ‖A‖ * δ ≤ 1 / 2 := by
    refine ⟨1 / (2 * (‖A‖ + 1)), by positivity, ?_⟩
    have h0 : 0 ≤ ‖A‖ := norm_nonneg _
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hball : ∀ ξ ∈ Metric.ball e δ, ‖A (ξ - e)‖ ≤ 1 / 2 := by
    intro ξ hξ
    calc ‖A (ξ - e)‖ ≤ ‖A‖ * ‖ξ - e‖ := A.le_opNorm _
      _ ≤ ‖A‖ * δ := by
        gcongr
        rw [← dist_eq_norm]
        exact (Metric.mem_ball.mp hξ).le
      _ ≤ 1 / 2 := hAδ
  let φ : ContDiffBump e := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  let χ : ContDiffBump e := ⟨δ / 2, δ, by positivity, by linarith⟩
  let g : V → (M →L[ℝ] M) := fun ξ => χ ξ • A (ξ - e)
  have hsmall : ∀ ξ : V, ‖g ξ‖ ≤ 1 / 2 := by
    intro ξ
    by_cases hξ : χ ξ = 0
    · simp [g, hξ]
    · have hmem : ξ ∈ Metric.ball e δ := by
        have h1 : ξ ∈ Function.support χ := hξ
        rwa [χ.support_eq] at h1
      simp only [g]
      rw [norm_smul, Real.norm_of_nonneg χ.nonneg]
      calc χ ξ * ‖A (ξ - e)‖ ≤ 1 * (1 / 2) := by
            gcongr
            · exact χ.le_one
            · exact hball ξ hmem
        _ = 1 / 2 := by norm_num
  refine ⟨fun ξ => ((φ ξ : ℝ) : ℂ), ?_, ?_, ?_⟩
  · have h1 : φ e = 1 := φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le)
    simp [h1]
  · intro ξ hξ y hy
    have hφ : φ ξ ≠ 0 := by
      intro h1
      apply hξ
      simp [h1]
    have hmem : ξ ∈ Metric.ball e δ := by
      have h1 : ξ ∈ Function.support φ := hφ
      rw [φ.support_eq] at h1
      exact Metric.ball_subset_ball (show δ / 2 ≤ δ by linarith) h1
    have h2 : y = -(A (ξ - e)) y := eq_neg_of_add_eq_zero_left hy
    have h3 : ‖y‖ ≤ 1 / 2 * ‖y‖ := by
      calc ‖y‖ = ‖(A (ξ - e)) y‖ := by
            conv_lhs => rw [h2]
            exact norm_neg _
        _ ≤ ‖A (ξ - e)‖ * ‖y‖ := (A (ξ - e)).le_opNorm y
        _ ≤ 1 / 2 * ‖y‖ := mul_le_mul_of_nonneg_right (hball ξ hmem) (norm_nonneg _)
    have h4 : ‖y‖ = 0 := le_antisymm (by linarith [norm_nonneg y]) (norm_nonneg y)
    exact norm_eq_zero.mp h4
  · intro α
    have hh : ContDiff ℝ ∞ (fun ξ => ((φ ξ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp φ.contDiff
    have hhc : HasCompactSupport (fun ξ => ((φ ξ : ℝ) : ℂ)) :=
      φ.hasCompactSupport.comp_left Complex.ofReal_zero
    obtain ⟨G0, hG0⟩ := hT V M (fun ξ => ((φ ξ : ℝ) : ℂ)) hh hhc α
    have hg : Function.HasTemperateGrowth g := by
      apply HasCompactSupport.hasTemperateGrowth
      · exact χ.hasCompactSupport.smul_right (f' := fun ξ => A (ξ - e))
      · exact χ.contDiff.smul (A.contDiff.comp (contDiff_id.sub contDiff_const))
    let Φ : V × M → V × M := fun p => p + ContinuousLinearMap.inr ℝ V M (g p.1 p.2)
    have hΦ : Function.HasTemperateGrowth Φ := by
      have h1 : Function.HasTemperateGrowth (fun p : V × M => g p.1) :=
        hg.comp (ContinuousLinearMap.fst ℝ V M).hasTemperateGrowth
      have h2 : Function.HasTemperateGrowth (fun p : V × M => g p.1 p.2) :=
        (ContinuousLinearMap.id ℝ (M →L[ℝ] M)).bilinear_hasTemperateGrowth h1
          (ContinuousLinearMap.snd ℝ V M).hasTemperateGrowth
      exact Function.HasTemperateGrowth.add Function.HasTemperateGrowth.id
        ((ContinuousLinearMap.inr ℝ V M).hasTemperateGrowth.comp h2)
    have hΦp : ∀ p : V × M, Φ p = (p.1, p.2 + g p.1 p.2) := by
      intro p
      ext <;> simp [Φ]
    have hup : ∃ (k : ℕ) (C : ℝ), ∀ p, ‖p‖ ≤ C * (1 + ‖Φ p‖) ^ k := by
      refine ⟨1, 2, fun p => ?_⟩
      have e1 : ‖p.2‖ ≤ ‖p.2 + g p.1 p.2‖ + ‖g p.1 p.2‖ := by
        simpa using norm_sub_le (p.2 + g p.1 p.2) (g p.1 p.2)
      have e2 : ‖g p.1 p.2‖ ≤ 1 / 2 * ‖p.2‖ :=
        ((g p.1).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hsmall _) (norm_nonneg _))
      have e3 : ‖p.2 + g p.1 p.2‖ ≤ ‖Φ p‖ := by
        rw [hΦp]
        exact norm_snd_le (p.1, p.2 + g p.1 p.2)
      have e4 : ‖p.1‖ ≤ ‖Φ p‖ := by
        rw [hΦp]
        exact norm_fst_le (p.1, p.2 + g p.1 p.2)
      rw [pow_one]
      refine norm_prod_le_iff.mpr ⟨?_, ?_⟩ <;> nlinarith [norm_nonneg (Φ p), norm_nonneg p.2]
    refine ⟨SchwartzMap.compCLM ℂ hΦ hup G0, fun ξ y => ?_⟩
    rw [SchwartzMap.compCLM_apply, Function.comp_apply, hΦp, hG0]
    by_cases hφ : φ ξ = 0
    · simp [hφ]
    · have hmem : ξ ∈ Metric.closedBall e χ.rIn := by
        have h1 : ξ ∈ Function.support φ := hφ
        rw [φ.support_eq] at h1
        exact Metric.ball_subset_closedBall h1
      simp [g, χ.one_of_mem_closedBall hmem]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LinChange
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem linearMap_comp_eq_on_smul_of_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (A B : V →L[ℝ] V)
    (h1 : ∀ x, B (A x) = x) (h2 : ∀ x, A (B x) = x) (f : V → ℂ) :
    ∫ x, f (A x) ∂μ = ((|(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| : ℝ) : ℂ) * ∫ x, f x ∂μ := by
  let e : V ≃L[ℝ] V := ContinuousLinearEquiv.equivOfInverse A B h1 h2
  have hd : LinearMap.det (A : V →ₗ[ℝ] V) ≠ 0 := (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hm : MeasurableEmbedding (A : V →ₗ[ℝ] V) := e.toHomeomorph.measurableEmbedding
  have := hm.integral_map (μ := μ) f
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ hd, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _)] at this
  rw [← Complex.real_smul, this]
  rfl

theorem UpperTheory.V.Af.Smo.linChange :
    UpperTheory.V.Af.Smo.LinChange := by
  intro E _ _ n
  refine ⟨fun s => ((|(LinearMap.det (lmul (toL s.val) : Lie E n →ₗ[ℝ] Lie E n))⁻¹| : ℝ) : ℂ), ?_, fun s f => ?_⟩
  · have : (lmul (toL (1 : GL (Fin n) (Rinf E)).val) : Lie E n →ₗ[ℝ] Lie E n) = LinearMap.id :=
      LinearMap.ext fun x => one_mul (Matrix.of x)
    simp only [this]
    simp
  · haveI : (volume : Measure (Rinf E)).IsAddHaarMeasure := inferInstance
    haveI : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    exact linearMap_comp_eq_on_smul_of_eq volume (lmul (toL s.val)) (lmul (toL (s⁻¹).val))
      (fun x => s.inv_mul_cancel_left (Matrix.of x)) (fun x => s.mul_inv_cancel_left (Matrix.of x)) f
end

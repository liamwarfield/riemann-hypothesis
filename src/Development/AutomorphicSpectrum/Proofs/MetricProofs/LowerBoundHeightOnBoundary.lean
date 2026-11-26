module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncModelEmbeddedLogResolution
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.HoloOnLocMono

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.EvalFam
section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.BlkDegLeTotalDegree
namespace PositivityTheory.Xgp.c_bm_exists_boundary

open MvPolynomial Classical

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def blkDeg (m : (Σ k, ι k) →₀ ℕ) (k : K) : ℕ := ∑ i, m ⟨k, i⟩

def padExp (p : (k : K) → ι k) (T : ℕ) (m : (Σ k, ι k) →₀ ℕ) : (Σ k, ι k) →₀ ℕ :=
  ∑ k, Finsupp.single ⟨k, p k⟩ (T - blkDeg m k)

theorem padExp_apply (p : (k : K) → ι k) (T : ℕ) (m : (Σ k, ι k) →₀ ℕ) (k : K) (i : ι k) :
    padExp p T m ⟨k, i⟩ = if i = p k then T - blkDeg m k else 0 := by
  classical
  simp only [padExp, Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · rw [Finsupp.single_apply]
    by_cases h : i = p k
    · subst h; simp
    · rw [if_neg, if_neg h]
      intro e
      exact h (eq_of_heq (Sigma.mk.inj_iff.1 e).2).symm
  · intro b _ hb
    rw [Finsupp.single_apply, if_neg]
    intro e
    exact hb (Sigma.mk.inj_iff.1 e).1
  · simp

theorem blkDeg_padExp (p : (k : K) → ι k) (T : ℕ) (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    blkDeg (padExp p T m) k = T - blkDeg m k := by
  classical
  unfold blkDeg
  simp only [padExp_apply]
  rw [Finset.sum_eq_single (p k)]
  · simp [blkDeg]
  · intro b _ hb; rw [if_neg hb]
  · simp

theorem blkDeg_le_totalDegree {Q : MvPolynomial (Σ k, ι k) ℂ} {m : (Σ k, ι k) →₀ ℕ} (hm : m ∈ Q.support)
    (k : K) : blkDeg m k ≤ Q.totalDegree := by
  classical
  refine le_trans ?_ (le_totalDegree hm)
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
  exact Finset.single_le_sum (f := fun k => ∑ i, m ⟨k, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

theorem exists_homogenize (p : (k : K) → ι k) (Q : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) :
    ∃ (G : MvPolynomial (Σ k, ι k) ℂ) (T : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G (fun _ => T) ∧
      (∀ z : (Σ k, ι k) → ℂ, (∀ k, z ⟨k, p k⟩ ≠ 0) →
        eval z G = (∏ k, z ⟨k, p k⟩ ^ T) * eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord p z)) Q) ∧
      ∀ z : (Σ k, ι k) → ℂ, (∃ k, z ⟨k, p k⟩ = 0) → eval z G = 0 := by
  classical
  set Q' : MvPolynomial (Σ k, ι k) ℂ := rename (Fintype.equivFin (Σ k, ι k)).symm Q with hQ'
  have hren : ∀ v : (Σ k, ι k) → ℂ, eval (ReciprocityTheory.AnForm.R.renPt v) Q = eval v Q' := fun v => by
    rw [hQ', eval_rename]
  set T := Q'.totalDegree + 1 with hT
  have hlt : ∀ m ∈ Q'.support, ∀ k, blkDeg m k < T := fun m hm k =>
    Nat.lt_succ_of_le (blkDeg_le_totalDegree hm k)
  refine ⟨∑ m ∈ Q'.support, monomial (m + padExp p T m) (AddMonoidAlgebra.coeff Q' m), T, ?_, ?_, ?_⟩
  · intro n hn k
    obtain ⟨m, hm, hn'⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hn)
    have hn'' := support_monomial_subset hn'
    rw [Finset.mem_singleton] at hn''
    subst hn''
    have e1 : ∑ i, (m + padExp p T m) ⟨k, i⟩ = blkDeg (m + padExp p T m) k := rfl
    rw [e1]
    unfold blkDeg
    simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
    have := blkDeg_padExp p T m k
    unfold blkDeg at this
    rw [this]
    have h2 := (hlt m hm k).le
    unfold blkDeg at h2
    omega
  · intro z hz
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [hren, Q'.as_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [eval_monomial, eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [Finsupp.coe_add, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    rw [Fintype.prod_sigma, Fintype.prod_sigma, Fintype.prod_sigma]
    have hpad : ∀ k, ∏ i, z ⟨k, i⟩ ^ padExp p T m ⟨k, i⟩ = z ⟨k, p k⟩ ^ (T - blkDeg m k) := fun k => by
      rw [Finset.prod_eq_single (p k)]
      · rw [padExp_apply, if_pos rfl]
      · intro b _ hb; rw [padExp_apply, if_neg hb, pow_zero]
      · simp
    simp only [hpad, ReciprocityTheory.AnForm.R.affCoord, div_pow]
    have hden : ∀ k, ∏ i, z ⟨k, p k⟩ ^ m ⟨k, i⟩ = z ⟨k, p k⟩ ^ blkDeg m k := fun k => by
      rw [Finset.prod_pow_eq_pow_sum]; rfl
    rw [show (∏ k, ∏ i, z ⟨k, i⟩ ^ m ⟨k, i⟩ / z ⟨k, p k⟩ ^ m ⟨k, i⟩) =
        (∏ k, ∏ i, z ⟨k, i⟩ ^ m ⟨k, i⟩) / ∏ k, z ⟨k, p k⟩ ^ blkDeg m k by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [Finset.prod_div_distrib, hden]]
    have hsub : ∀ k, z ⟨k, p k⟩ ^ (T - blkDeg m k) = z ⟨k, p k⟩ ^ T / z ⟨k, p k⟩ ^ blkDeg m k := fun k =>
      pow_sub₀ _ (hz k) (hlt m hm k).le
    simp only [hsub, Finset.prod_div_distrib]
    have h0 : (∏ k, z ⟨k, p k⟩ ^ blkDeg m k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k)
    field_simp
  · rintro z ⟨k, hk⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨k, p k⟩) ?_)
    rw [hk, Finsupp.coe_add, Pi.add_apply, padExp_apply, if_pos rfl]
    exact zero_pow (by have := hlt m hm k; omega)

end

end PositivityTheory.Xgp.c_bm_exists_boundary
end

namespace PositivityTheory.Xgp.c_bm_exists_boundary

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes


set_option maxHeartbeats 1000000 in
theorem exists_res {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
    (x : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)) (hP : IsArithVar (mCoordIdeal x) (e + 1))
    (hJ : IsMultiHomogIdeal J) (hJP : ¬ J ≤ mCoordIdeal x) (hsnc : IsSncModel x e J) :
    ∃ (Rb : AnLogRes (mCoordIdeal x) ⊤ e) (nb : ℕ) (W : Fin nb → Set Rb.X), ∀ x₀ : Rb.X,
      ∃ (ψ : OpenPartialHomeomorph Rb.X (Fin e → ℂ)) (σ : Fin nb → Option (Fin e)),
      IsCompatChart Rb.A ψ ∧ x₀ ∈ ψ.source ∧ ψ.source ⊆ Rb.U x₀ ∧
      (∀ k k' i, σ k = some i → σ k' = some i → k = k') ∧
      (∀ k, W k ∩ ψ.source = {y ∈ ψ.source | ∃ i, σ k = some i ∧ ψ y i = 0}) ∧
      (∀ y ∈ ψ.source, Rb.lift x₀ y ∈ mcPts (mCoordIdeal x) ∩ mcPts J ↔ locMono ψ σ y = 0) ∧
      (∀ (G : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), IsMultiHomog G a →
        (∀ z ∈ mcPts (mCoordIdeal x) ∩ mcPts J, MvPolynomial.eval z G = 0) →
        ∃ v : Rb.X → ℂ, Rb.A.HoloOn ψ.source v ∧ ∀ y ∈ ψ.source,
          MvPolynomial.eval (Rb.lift x₀ y) G = v y * locMono ψ σ y) ∧
      ∃ (G : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (v : Rb.X → ℂ), IsMultiHomog G a ∧
        (∀ z ∈ mcPts (mCoordIdeal x) ∩ mcPts J, MvPolynomial.eval z G = 0) ∧ Rb.A.HoloOn ψ.source v ∧
        v x₀ ≠ 0 ∧ ∀ y ∈ ψ.source, MvPolynomial.eval (Rb.lift x₀ y) G = v y * locMono ψ σ y := by
  classical
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal x)) := isMultiHomogIdeal_pC hP.2.1.2.1
  have hDh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC J) := isMultiHomogIdeal_pC hJ
  obtain ⟨hcpt, hsrc⟩ := GlobalTheory.T.snc_resolution_compact_embedded K ι _ hPh
  obtain ⟨himage, htrans⟩ := GlobalTheory.T.snc_resolution_transition_polynomial K ι _ hPh
  obtain ⟨hcover, hliftmem, hcompat, hsurj, hinj, hzero⟩ := GlobalTheory.T.snc_resolution_cover_and_cone K ι _ _ hPh hDh
  have hinv := GlobalTheory.T.snc_resolution_local_chart_polynomial K ι _ hPh
  have hreg := GlobalTheory.T.snc_resolution_regular_local_ring K ι Ω x e J hP hsnc
  have hsc := GlobalTheory.T.snc_resolution_boundary_normal_crossing K ι Ω x e J hP hJ hJP hsnc
  let E := Fintype.equivFin ((k : K) → ι k)
  let R : ReciprocityTheory.AnForm.R.AlgRes ι (pC (mCoordIdeal x)) (pC J) e :=
    { M := Pts (pC (mCoordIdeal x))
      compact := hcpt
      n := Fintype.card ((k : K) → ι k)
      amb := fun _ => Fintype.card (Σ k, ι k)
      ideal := fun i => ideal _ (E.symm i)
      src := fun i => src _ (E.symm i)
      isOpen_alt_bis := fun i => (hsrc _).1
      cover := fun y => by
        obtain ⟨p, hp⟩ := hcover y
        obtain ⟨i, rfl⟩ := E.symm.surjective p
        exact ⟨i, hp⟩
      coord := fun i => coord _ (E.symm i)
      isEmbedding := fun i => (hsrc _).2
      image := fun i => himage _
      trans := fun i j => htrans _ _
      regular := fun i y hy => (hreg _ y hy).1
      dim := fun i y hy => (hreg _ y hy).2
      lift := fun i => lift (E.symm i)
      lift_one := fun i => ⟨E.symm i, fun k => by simp [lift]⟩
      lift_mem := fun i => hliftmem _
      compat := fun i j => hcompat _ _
      surj := fun z hz _ => by
        obtain ⟨p, y, hy, h⟩ := hsurj z hz
        obtain ⟨i, rfl⟩ := E.symm.surjective p
        exact ⟨i, y, hy, h⟩
      inj := fun i j y hy y' hy' _ h => hinj _ _ y hy y' hy' h
      inv := fun i y hy _ p' hp' => hinv _ y hy p' hp'
      bd := fun i => bd _ (pC J) (E.symm i)
      le_bd := fun i => le_trans (Ideal.map_mono (sup_le_sup_right le_sup_left _)) Ideal.le_radical
      zero_bd := fun i => hzero _
      rc := rc _ (pC J)
      comp := comp _ (pC J)
      sncAt := fun i y hy => (hsc _ y hy).choose
      comp_eq := fun i y hy => (hsc _ y hy).choose_spec.1
      mult := fun f a hf hfP hz => ⟨fun k => ordAlong (compIdeal _ (pC J) k) _ f,
        fun i y hy => (hsc _ y hy).choose_spec.2 f a hf hfP hz⟩ }
  have hsurj' : ∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC (mCoordIdeal x)), ∃ i, ∃ y ∈ R.src i,
      ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (R.coord i y) (R.lift i q)) z := by
    intro z hz
    obtain ⟨p, y, hy, h⟩ := hsurj z hz
    obtain ⟨i, rfl⟩ := E.symm.surjective p
    exact ⟨i, y, hy, h⟩
  have hinj' : ∀ i j, ∀ y ∈ R.src i, ∀ y' ∈ R.src j,
      ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (R.coord i y) (R.lift i q))
        (fun q => eval (R.coord j y') (R.lift j q)) → y = y' :=
    fun i j y hy y' hy' h => hinj _ _ y hy y' hy' h
  let R0 : ReciprocityTheory.AnForm.R.AlgRes ι (pC (mCoordIdeal x)) ⊤ e :=
    { M := R.M
      n := R.n
      amb := R.amb
      ideal := R.ideal
      src := R.src
      isOpen_alt_bis := R.isOpen_alt_bis
      cover := R.cover
      coord := R.coord
      isEmbedding := R.isEmbedding
      image := R.image
      trans := R.trans
      regular := R.regular
      dim := R.dim
      lift := R.lift
      lift_one := R.lift_one
      lift_mem := R.lift_mem
      compat := R.compat
      surj := fun z hz _ => hsurj' z hz
      inj := fun i j y hy y' hy' _ h => hinj' i j y hy y' hy' h
      inv := fun i y hy _ p hp => hinv _ y hy p hp
      bd := fun _ => ⊤
      le_bd := fun _ => le_top
      zero_bd := fun i y hy =>
        ⟨fun h => absurd (h 1 Submodule.mem_top) (by simp), fun h => absurd h (not_mem_conePts_top _)⟩
      rc := 0
      comp := Fin.elim0
      sncAt := fun i y hy =>
        { r := (R.sncAt i y hy).r
          J := ∅
          h := 1
          σ := fun _ => none
          σ_injOn := by simp
          σ_eq_none := by simp
          span_eq := (R.sncAt i y hy).span_eq
          eval_h := by simp
          mem_bd := Submodule.mem_top
          le_span := fun g _ => by simp }
      comp_eq := fun i y hy => ⟨R.src i, R.isOpen_alt_bis i, hy, subset_rfl, fun k => k.elim0⟩
      mult := fun f a hf hfP hz => ⟨Fin.elim0, fun i y hy =>
        ⟨_, isUnit_algebraMap_locRing _ _ _ (by
          rw [ReciprocityTheory.AnForm.R.eval_bind_one]
          intro h
          exact not_mem_conePts_top _ (hz _ (R.lift_mem i y hy) h)), by simp⟩⟩ }
  obtain ⟨A, hA⟩ := R0.exists_atlas
  have hA' : R.IsGoodAtlas A := hA
  choose idx hidx using R.cover
  have htop : IsMultiHomogIdeal (⊤ : Ideal (MRing ι)) := by
    refine ⟨{1}, fun f hf => ⟨0, ?_⟩, (Ideal.span_singleton_one).symm⟩
    rw [Set.mem_singleton_iff.1 hf]
    intro m hm k
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    simp [hm]
  let Rb : AnLogRes (mCoordIdeal x) ⊤ e :=
    { homog := htop
      nondeg := fun h => hP.2.1.1.ne_top (top_le_iff.1 h)
      X := R.M
      A := A
      U := fun y => R.src (idx y)
      isOpen_U := fun y => R.isOpen_alt_bis (idx y)
      mem_U := hidx
      lift := fun y y' q => eval (R.coord (idx y) y') (R.lift (idx y) q)
      holo := fun y q => hA'.1 (idx y) (R.lift (idx y) q)
      mem := fun y y' hy' => by
        rw [mem_mcPts_iff_conePts_pC]
        exact R.lift_mem (idx y) y' hy'
      compat := fun y y' t ht => R.compat (idx y) (idx y') t ht
      surj := fun z hz _ => by
        rw [mem_mcPts_iff_conePts_pC] at hz
        obtain ⟨i, y, hy, hyz⟩ := hsurj' z hz
        exact ⟨y, ReciprocityTheory.ChartRestriction.G.Geo.sameOrbit_trans (R.compat (idx y) i y ⟨hidx y, hy⟩) hyz⟩
      inj := fun y y' _ hyy => hinj' (idx y) (idx y') y (hidx y) y' (hidx y') hyy
      immersion := fun y _ p hp j hj =>
        R0.fderiv_affCoord_ker_eq_bot A hA (idx y) y (hidx y) (not_mem_conePts_top _) p hp j hj
      snc := fun f a hfP hf hz => by
        have hf' : ReciprocityTheory.AnForm.R.IsMultiHomog (map (Int.castRingHom ℂ) f) a :=
          fun m hm k => hf m (support_map_subset _ _ hm) k
        have hfP' : map (Int.castRingHom ℂ) f ∉ pC (mCoordIdeal x) := fun h => hfP (pcContract K ι _ e hP f h)
        have hz' : ∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC (mCoordIdeal x)), eval z (map (Int.castRingHom ℂ) f) = 0 →
            z ∈ ReciprocityTheory.AnForm.R.conePts (⊤ : Ideal (MvPolynomial (Σ k, ι k) ℂ)) := by
          intro z hz1 hz2
          have h3 : z ∈ mcPts (⊤ : Ideal (MRing ι)) := hz z ((mem_mcPts_iff_conePts_pC _ z).2 hz1) hz2
          exact absurd h3 (fun h => by simpa using h.2 1 trivial)
        obtain ⟨m, hm⟩ := R0.isSNC_pullback A hA idx hidx (fun _ _ => 0) _ a hf' hfP' hz'
        exact ⟨R0.rc, m, R0.comp, hm⟩
      null := fun j => by
        refine MeasureTheory.measure_mono_null (fun t ht => ?_) MeasureTheory.measure_empty
        have h3 := ht.2
        simp only [Set.mem_preimage, Set.mem_setOf_eq] at h3
        exact absurd h3 (fun h => by simpa using h.2 1 trivial) }
  refine ⟨Rb, R.rc, R.comp, fun x₀ => ?_⟩
  have hx : x₀ ∈ R.src (idx x₀) := hidx x₀
  obtain ⟨O, hOo, hxO, -, hOc⟩ := R.comp_eq (idx x₀) x₀ hx
  have hO' : IsOpen (O ∩ {y | y ∈ R.src (idx x₀) ∧ eval (R.coord (idx x₀) y) (R.sncAt (idx x₀) x₀ hx).h ≠ 0}) :=
    hOo.inter (R.isOpen_nonvan _ _)
  obtain ⟨ψ, hψc, hxψ, hψs, hψe⟩ := hA'.2 (idx x₀) x₀ hx (R.sncAt (idx x₀) x₀ hx).r
    (R.sncAt (idx x₀) x₀ hx).span_eq _ hO' ⟨hxO, hx, (R.sncAt (idx x₀) x₀ hx).eval_h⟩
  set d := R.sncAt (idx x₀) x₀ hx with hd
  have hJ' : ∀ l k, d.σ l = some k → l ∈ d.J := by
    intro l k hl; by_contra hJ; rw [(d.σ_eq_none l).2 hJ] at hl; cases hl
  let σ' : Fin R.rc → Option (Fin e) := fun k =>
    if h : ∃ l, d.σ l = some k then some (Classical.choose h) else none
  have hσ' : ∀ k l, σ' k = some l ↔ d.σ l = some k := by
    intro k l
    by_cases h : ∃ l, d.σ l = some k
    · have hc0 := Classical.choose_spec h
      simp only [σ', dif_pos h, Option.some.injEq]
      constructor
      · rintro rfl; exact hc0
      · intro hl
        exact d.σ_injOn (hJ' _ _ hc0) (hJ' _ _ hl) (by rw [hc0, hl])
    · simp only [σ', dif_neg h]
      constructor
      · intro h'; cases h'
      · intro hl; exact absurd ⟨l, hl⟩ h
  have hmono : ∀ y ∈ ψ.source, locMono ψ σ' y = eval (R.coord (idx x₀) y) (∏ l ∈ d.J, d.r l) := by
    intro y hy
    rw [map_prod]
    have h1 := ReciprocityTheory.AnForm.R.prod_reindex_option d.J d.σ d.σ_eq_none σ' hσ' (fun _ => 1)
      (fun l => eval (R.coord (idx x₀) y) (d.r l))
    have h2 : ∏ l ∈ d.J, eval (R.coord (idx x₀) y) (d.r l) ^ (d.σ l).elim 0 (fun _ => 1) =
        ∏ l ∈ d.J, eval (R.coord (idx x₀) y) (d.r l) := Finset.prod_congr rfl fun l hl => by
      obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 (fun h => (d.σ_eq_none l).1 h hl)
      rw [hk]; simp
    rw [← h2, h1]
    unfold locMono
    refine Finset.prod_congr rfl fun k _ => ?_
    rcases σ' k with _ | l
    · rfl
    · simp [hψe y hy, ReciprocityTheory.AnForm.R.evalFam]
  refine ⟨ψ, σ', hψc, hxψ, fun y hy => (hψs hy).2, ?_, ?_, ?_, ?_, ?_⟩
  · intro k k' l h1 h2
    rw [hσ'] at h1 h2
    rw [h1] at h2
    exact Option.some.inj h2
  · intro k
    ext y
    constructor
    · rintro ⟨hyk, hyψ⟩
      have hyO : y ∈ R.comp k ∩ O := ⟨hyk, (hψs hyψ).1.1⟩
      rw [hOc k] at hyO
      obtain ⟨-, l, hl, h0⟩ := hyO
      refine ⟨hyψ, l, (hσ' k l).2 hl, ?_⟩
      rw [hψe y hyψ]; exact h0
    · rintro ⟨hyψ, l, hl, h0⟩
      refine ⟨?_, hyψ⟩
      have hyO : y ∈ {y ∈ O | ∃ l, d.σ l = some k ∧ eval (R.coord (idx x₀) y) (d.r l) = 0} := by
        refine ⟨(hψs hyψ).1.1, l, (hσ' k l).1 hl, ?_⟩
        rw [hψe y hyψ] at h0; exact h0
      rw [← hOc k] at hyO
      exact hyO.1
  · intro y hy
    have hys : y ∈ R.src (idx x₀) := (hψs hy).2
    have hh : eval (R.coord (idx x₀) y) d.h ≠ 0 := (hψs hy).1.2.2
    rw [hmono y hy]
    show (fun q => eval (R.coord (idx x₀) y) (R.lift (idx x₀) q)) ∈ _ ↔ _
    rw [Set.mem_inter_iff, mem_mcPts_iff_conePts_pC, mem_mcPts_iff_conePts_pC, ← R.zero_bd (idx x₀) y hys]
    constructor
    · rintro ⟨-, h0⟩
      have := h0 _ d.mem_bd
      rw [map_mul] at this
      exact (mul_eq_zero.1 this).resolve_left hh
    · intro h0
      refine ⟨R.lift_mem (idx x₀) y hys, fun g hg => ?_⟩
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (d.le_span g hg)
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      have hb0 := R.coord_mem_zero (idx x₀) hys b hb
      have := congrArg (eval (R.coord (idx x₀) y)) hab
      rw [map_add (f := _), map_mul, h0, mul_zero, zero_add, hb0, map_mul] at this
      exact (mul_eq_zero.1 this.symm).resolve_left hh
  · intro G a _ hG
    have hmem : bind₁ (R.lift (idx x₀)) G ∈ R.bd (idx x₀) := by
      have hrad : (R.bd (idx x₀)).radical = R.bd (idx x₀) := Ideal.radical_idem _
      rw [← hrad, ← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ), MvPolynomial.mem_vanishingIdeal_iff]
      intro t ht
      rw [MvPolynomial.mem_zeroLocus_iff] at ht
      have ht2 : ∀ h ∈ R.bd (idx x₀), eval t h = 0 := ht
      change eval t _ = 0
      have ht' : t ∈ R.coord (idx x₀) '' R.src (idx x₀) := by
        rw [R.image (idx x₀)]; exact fun h hh => ht2 h (R.le_bd (idx x₀) hh)
      obtain ⟨y, hy, rfl⟩ := ht'
      rw [ReciprocityTheory.AnForm.R.eval_bind_one]
      exact hG _ ⟨(mem_mcPts_iff_conePts_pC _ _).2 (R.lift_mem (idx x₀) y hy),
        (mem_mcPts_iff_conePts_pC _ _).2 ((R.zero_bd (idx x₀) y hy).1 fun h hh => ht2 h hh)⟩
    obtain ⟨a', ha', b, hb, hab⟩ := Submodule.mem_sup.1 (d.le_span _ hmem)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha'
    refine ⟨fun y => eval (R.coord (idx x₀) y) c / eval (R.coord (idx x₀) y) d.h, ?_, fun y hy => ?_⟩
    · intro j z hz
      have hz' : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.src (idx x₀) := ⟨hz.1, (hψs hz.2).2⟩
      exact (hA'.1 (idx x₀) c j z hz').div (hA'.1 (idx x₀) d.h j z hz') (hψs hz.2).1.2.2
    · have hys : y ∈ R.src (idx x₀) := (hψs hy).2
      have hh : eval (R.coord (idx x₀) y) d.h ≠ 0 := (hψs hy).1.2.2
      have hb0 := R.coord_mem_zero (idx x₀) hys b hb
      have := congrArg (eval (R.coord (idx x₀) y)) hab
      rw [map_add (f := _), map_mul, hb0, add_zero, map_mul] at this
      show eval (fun q => eval (R.coord (idx x₀) y) (R.lift (idx x₀) q)) G = _
      rw [← ReciprocityTheory.AnForm.R.eval_bind_one, hmono y hy, div_mul_eq_mul_div, eq_div_iff hh]
      linear_combination (-1 : ℂ) * this
  · obtain ⟨G, T, hGh, hG1, hG0⟩ := exists_homogenize (E.symm (idx x₀)) (d.h * ∏ l ∈ d.J, d.r l)
    refine ⟨G, fun _ => T, fun y => eval (R.coord (idx x₀) y) d.h, hGh, ?_, ?_, d.eval_h, fun y hy => ?_⟩
    · intro z hz
      by_cases h0 : ∃ k, z ⟨k, E.symm (idx x₀) k⟩ = 0
      · exact hG0 z h0
      push_neg at h0
      rw [hG1 z h0]
      refine mul_eq_zero_of_right _ ?_
      obtain ⟨N, hN⟩ := d.mem_bd
      obtain ⟨f, hf, hfe⟩ := (Ideal.mem_map_of_equiv _ _).1 hN
      have hw : ReciprocityTheory.AnForm.R.affCoord (E.symm (idx x₀)) z =
          fun q => (z ⟨q.1, E.symm (idx x₀) q.1⟩)⁻¹ * z q := funext fun q => by
        simp [ReciprocityTheory.AnForm.R.affCoord, div_eq_inv_mul]
      have hz1 := (mem_mcPts_iff_conePts_pC _ z).1 hz.1
      have hz2 := (mem_mcPts_iff_conePts_pC _ z).1 hz.2
      have hker : ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal x) ⊔ pC J) (E.symm (idx x₀)) ≤
          RingHom.ker (eval (ReciprocityTheory.AnForm.R.affCoord (E.symm (idx x₀)) z)) := by
        unfold ReciprocityTheory.AnForm.R.chartIdeal
        apply sup_le
        apply sup_le
        · intro g hg
          rw [RingHom.mem_ker, hw]
          exact ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hPh (fun k => (z ⟨k, E.symm (idx x₀) k⟩)⁻¹) z hz1.2 g hg
        · intro g hg
          rw [RingHom.mem_ker, hw]
          exact ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hDh (fun k => (z ⟨k, E.symm (idx x₀) k⟩)⁻¹) z hz2.2 g hg
        · rw [Ideal.span_le]
          rintro _ ⟨k, rfl⟩
          simp [ReciprocityTheory.AnForm.R.affCoord, div_self (h0 k)]
      have h4 := hker hf
      rw [RingHom.mem_ker] at h4
      have h5 : eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord (E.symm (idx x₀)) z))
          ((d.h * ∏ l ∈ d.J, d.r l) ^ N) = 0 := by
        rw [← hfe]
        exact (ReciprocityTheory.AnForm.R.eval_renC _ f).trans h4
      rw [map_pow] at h5
      by_contra hne
      exact pow_ne_zero N hne h5
    · intro j z hz
      exact hA'.1 (idx x₀) d.h j z ⟨hz.1, (hψs hz.2).2⟩
    · have hys : y ∈ src _ (E.symm (idx x₀)) := (hψs hy).2
      have hl : (fun q => eval (R.coord (idx x₀) y) (R.lift (idx x₀) q)) =
          ReciprocityTheory.AnForm.R.affCoord (E.symm (idx x₀)) (rep y) :=
        funext fun q => eval_lift (E.symm (idx x₀)) y hys q
      have h1 : ∀ k, ReciprocityTheory.AnForm.R.affCoord (E.symm (idx x₀)) (rep y) ⟨k, E.symm (idx x₀) k⟩ = 1 :=
        fun k => div_self (hys k)
      show eval (fun q => eval (R.coord (idx x₀) y) (R.lift (idx x₀) q)) G = _
      rw [hl, hG1 _ (fun k => by rw [h1]; exact one_ne_zero)]
      simp only [h1, one_pow, Finset.prod_const_one, one_mul]
      have h2 : ReciprocityTheory.AnForm.R.affCoord (E.symm (idx x₀)) (ReciprocityTheory.AnForm.R.affCoord (E.symm (idx x₀)) (rep y)) =
          ReciprocityTheory.AnForm.R.affCoord (E.symm (idx x₀)) (rep y) :=
        funext fun q => by rw [ReciprocityTheory.AnForm.R.affCoord, h1, div_one]
      rw [h2]
      show eval (R.coord (idx x₀) y) (d.h * ∏ l ∈ d.J, d.r l) = _
      rw [map_mul, hmono y hy]

end PositivityTheory.Xgp.c_bm_exists_boundary
end

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.LeMCoordIdealOfTorus
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_boundary

section HomogIdeal

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem eval_mConeMap {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) (c : K → Ω) (f : MRing J) :
    MvPolynomial.eval c (mConeMap y f) = MvPolynomial.aeval (fun p : Σ k, J k => y p * c p.1) f := by
  have h : (MvPolynomial.eval c).comp (mConeMap y).toRingHom =
      (MvPolynomial.aeval (fun p : Σ k, J k => y p * c p.1) : MRing J →ₐ[ℤ] Ω).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro p; simp [mConeMap]
  exact congrArg (fun φ : MRing J →+* Ω => φ f) h

theorem aeval_eq_eval_map (w : (Σ k, J k) → ℂ) (f : MRing J) :
    MvPolynomial.aeval w f = MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) f) := by
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def, algebraMap_int_eq]

theorem aeval_eq_zero_of_mem {w : (Σ k, J k) → ℂ} {f : MRing J} (hf : f ∈ mCoordIdeal w) :
    MvPolynomial.aeval w f = 0 := by
  have hf' : mConeMap w f = 0 := hf
  have h := eval_mConeMap w (fun _ => 1) f
  rw [hf', map_zero] at h
  simpa using h.symm

theorem aeval_ratio_eq_zero {Ω : Type} [Field Ω] {x : (Σ k, J k) → Ω} (c : (k : K) → J k) {f : MRing J}
    (hf : f ∈ mCoordIdeal x) : MvPolynomial.aeval (fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩) f = 0 := by
  have hf' : mConeMap x f = 0 := hf
  have h := eval_mConeMap x (fun k => (x ⟨k, c k⟩)⁻¹) f
  rw [hf', map_zero] at h
  simpa [div_eq_mul_inv] using h.symm

theorem eq_zero_of_eval_torus {F : MvPolynomial K ℂ}
    (h : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → MvPolynomial.eval c F = 0) : F = 0 := by
  have h2 : F * ∏ k, (MvPolynomial.X k : MvPolynomial K ℂ) = 0 := by
    apply MvPolynomial.funext
    intro c
    rw [map_mul, map_zero, map_prod]
    by_cases hc : ∀ k, c k ≠ 0
    · rw [h c hc, zero_mul]
    · push_neg at hc
      obtain ⟨k, hk⟩ := hc
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk]), mul_zero]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd h3 (Finset.prod_ne_zero_iff.2 fun k _ => MvPolynomial.X_ne_zero k)

theorem le_mCoordIdeal_of_torus {bd : Ideal (MRing J)} {z : (Σ k, J k) → ℂ}
    (h : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → ∀ f ∈ bd, MvPolynomial.aeval (fun p : Σ k, J k => z p * c p.1) f = 0) :
    bd ≤ mCoordIdeal z := by
  intro f hf
  show mConeMap z f = 0
  refine eq_zero_of_eval_torus fun c hc => ?_
  rw [eval_mConeMap]
  exact h c hc f hf

theorem exists_algHom_ker_eq {S : Type} [CommRing S] [Algebra ℚ S] [Algebra.FiniteType ℚ S] (m : Ideal S)
    [m.IsMaximal] : ∃ ev : S →ₐ[ℚ] ℂ, RingHom.ker ev = m := by
  let _ : Field (S ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType ℚ (S ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ m) (Ideal.Quotient.mkₐ_surjective ℚ m)
  haveI : Module.Finite ℚ (S ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℚ (S ⧸ m)
  haveI : Algebra.IsAlgebraic ℚ (S ⧸ m) := Algebra.IsAlgebraic.of_finite ℚ _
  let φ : (S ⧸ m) →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ.comp (Ideal.Quotient.mkₐ ℚ m), ?_⟩
  ext s
  rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, map_eq_zero_iff φ φ.toRingHom.injective,
    Ideal.Quotient.eq_zero_iff_mem]

theorem cond_of_bd {Ω : Type} [Field Ω] [CharZero Ω] {x : (Σ k, J k) → Ω} {bd : Ideal (MRing J)}
    {c : (k : K) → J k} (hc : ∀ k, x ⟨k, c k⟩ ≠ 0) {S : Subalgebra ℚ Ω} [Algebra.FiniteType ℚ S]
    (hρ : ∀ p : Σ k, J k, x p / x ⟨p.1, c p.1⟩ ∈ S) (q : Ideal S) (hq : q.IsPrime)
    (hbd : ∀ g ∈ bd, ∀ s : S, (s : Ω) = MvPolynomial.aeval (fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩) g → s ∈ q) :
    ∀ g ∈ (⨅ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, mCoordIdeal z), ∀ s : S,
      (s : Ω) = MvPolynomial.aeval (fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩) g → s ∈ q := by
  intro g hg s hs
  haveI : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := ℚ)
  have hjac : q.jacobson = q := isJacobsonRing_iff_prime_eq.mp inferInstance q hq
  rw [← hjac]
  refine Ideal.mem_sInf.2 ?_
  rintro m ⟨hqm, hm⟩
  obtain ⟨ev, hev⟩ := exists_algHom_ker_eq m
  let ρS : (Σ k, J k) → S := fun p => ⟨_, hρ p⟩
  let w : (Σ k, J k) → ℂ := fun p => ev (ρS p)
  have hval : ∀ f : MRing J, ev (MvPolynomial.aeval ρS f) = MvPolynomial.aeval w f := fun f => by
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, ← AlgHom.coe_toRingHom, MvPolynomial.eval₂_comp_left]
    congr 1 <;> first | rfl | exact RingHom.ext_int _ _
  have hsub : ∀ f : MRing J, ((MvPolynomial.aeval ρS f : S) : Ω) =
      MvPolynomial.aeval (fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩) f := fun f => by
    show S.val.toRingHom (MvPolynomial.aeval ρS f) = _
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
    congr 1 <;> first | rfl | exact RingHom.ext_int _ _
  have hwP : w ∈ mcPts (mCoordIdeal x) := by
    refine ⟨fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩
    · have h1 : ρS ⟨k, c k⟩ = 1 := Subtype.ext (div_self (hc k))
      simp only [w, h1, map_one]
      exact one_ne_zero
    · rw [← aeval_eq_eval_map, ← hval]
      have h1 : MvPolynomial.aeval ρS f = 0 := Subtype.ext (by rw [hsub]; exact aeval_ratio_eq_zero c hf)
      rw [h1, map_zero]
  have hwbd : w ∈ mcPts bd := by
    refine ⟨hwP.1, fun f hf => ?_⟩
    rw [← aeval_eq_eval_map, ← hval, ← RingHom.mem_ker, hev]
    exact hqm (hbd f hf _ (hsub f))
  have hg' : g ∈ mCoordIdeal w := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hg w) ⟨hwP, hwbd⟩
  have hs' : s = MvPolynomial.aeval ρS g := Subtype.ext (hs.trans (hsub g).symm)
  rw [← hev, RingHom.mem_ker, hs', hval]
  exact aeval_eq_zero_of_mem hg'

end HomogIdeal

theorem exists_homogIdeal {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    [CharZero Ω] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)) (hs : Cmp.IsSncModel x n bd)
    (ha : IsArithVar (mCoordIdeal x) (n + 1))
    (ht : ∀ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd) :
    ∃ I : Ideal (MRing J), IsMultiHomogIdeal I ∧ ¬ I ≤ mCoordIdeal x ∧ Cmp.IsSncModel x n I ∧
      mcPts (mCoordIdeal x) ∩ mcPts I = mcPts (mCoordIdeal x) ∩ mcPts bd := by
  classical
  set I : Ideal (MRing J) := ⨅ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, mCoordIdeal z with hIdef
  have hle : bd ≤ I := by
    intro f hf
    refine (Submodule.mem_iInf _).2 fun z => (Submodule.mem_iInf _).2 fun hz => ?_
    refine le_mCoordIdeal_of_torus (fun c hc g hg => ?_) hf
    have e : (fun p : Σ k, J k => z p * c p.1) = GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c z :=
      funext fun p => mul_comm _ _
    rw [e, aeval_eq_eval_map]
    exact (ht z hz c hc).2.2 g hg
  have hhom : IsMultiHomogIdeal I := by
    refine (GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff I).mp ?_
    intro f hf b
    refine (Submodule.mem_iInf _).2 fun z => (Submodule.mem_iInf _).2 fun hz => ?_
    exact GroundTheory.Heights₂.Heights.CoordinateConeArithVar.component_mem z f
      ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hf z) hz) b

  have hrel := ha.2.1.2.2
  have hc0 : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap x (MvPolynomial.X ⟨k, i⟩) = 0
    simp [mConeMap, h0]
  choose c hc using hc0
  refine ⟨I, hhom, ?_, ?_, ?_⟩
  · intro hIP
    obtain ⟨m, f, a, -, -, hsum, hl⟩ := hs c hc
    obtain ⟨l, hfl⟩ : ∃ l, f l ≠ 0 := by
      by_contra h
      push_neg at h
      rw [Finset.sum_eq_zero fun l _ => by rw [h l, mul_zero]] at hsum
      exact zero_ne_one hsum
    obtain ⟨-, z, n', -, hli, -, hq⟩ := hl l hfl _ rfl
    have hbot := hq ⊥ Ideal.isPrime_bot
    have hR : ¬ ∃ i : Fin n, (i : ℕ) < n' ∧ z i ∈ (⊥ : Ideal _) := by
      rintro ⟨i, -, hzi⟩
      rw [Ideal.mem_bot] at hzi
      exact hli.ne_zero i (by rw [hzi, map_zero])
    rw [← hbot] at hR
    push_neg at hR
    obtain ⟨g, hg, s, hs1, hs2⟩ := hR
    have hs3 : (s : Ω) ≠ 0 := fun h0 => hs2 ((Ideal.mem_bot).2 (Subtype.ext h0))
    rw [hs1] at hs3
    exact hs3 (aeval_ratio_eq_zero c (hIP (hle hg)))
  · intro c' hc'
    obtain ⟨m, f, a, hf, ha', hsum, hl⟩ := hs c' hc'
    refine ⟨m, f, a, hf, ha', hsum, fun l hfl S hS => ?_⟩
    obtain ⟨hsm, z, n', hn', hli, hsp, hq⟩ := hl l hfl S hS
    refine ⟨hsm, z, n', hn', hli, hsp, fun q hqp => ?_⟩
    rw [← hq q hqp]
    constructor
    · intro h g hg s hs'
      exact h g (hle hg) s hs'
    · intro h
      have hfin : (insert (f l)⁻¹ (Set.range fun p : Σ k, J k => x p / x ⟨p.1, c' p.1⟩)).Finite :=
        (Set.finite_range _).insert _
      haveI : Algebra.FiniteType ℚ S := by
        rw [← Subalgebra.fg_iff_finiteType, hS, ← hfin.coe_toFinset]
        exact Subalgebra.fg_adjoin_finset _
      have hρ : ∀ p : Σ k, J k, x p / x ⟨p.1, c' p.1⟩ ∈ S := fun p => by
        rw [hS]
        exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_range_self p))
      exact cond_of_bd hc' hρ q hqp h
  · ext z
    constructor
    · rintro ⟨hzP, hzI⟩
      exact ⟨hzP, hzI.1, fun f hf => hzI.2 f (hle hf)⟩
    · rintro ⟨hzP, hzb⟩
      refine ⟨hzP, hzP.1, fun f hf => ?_⟩
      rw [← aeval_eq_eval_map]
      exact aeval_eq_zero_of_mem ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hf z) ⟨hzP, hzb⟩)

end PositivityTheory.Xgp.c_bm_exists_boundary
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerBoundHeightOnBoundary
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.lowerBound_height_on_boundary : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), Cmp.IsSncModel x n bd → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x) (n + 1) → IsClosed ((↑) ⁻¹' (mcPts (mCoordIdeal x) ∩ mcPts bd) : Set (mcPts (mCoordIdeal x))) → (∀ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd) → (∀ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd) → ∃ (Rb : AnLogRes (mCoordIdeal x) ⊤ n) (L : LocPot Rb.X) (s : Rb.X → Rb.X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set Rb.X), IsPotential Rb.A L ∧ IsSection Rb.A L s ∧ IsSNC Rb.A L s m W ∧ (∀ p, logNormSec L s p ≤ 0) ∧ (∀ p, p ∈ bdry s ↔ Rb.lift p p ∈ mcPts bd) ∧ ∀ p p', SameOrbit (Rb.lift p' p') (fun q => starRingEnd ℂ (Rb.lift p p q)) → rW L s p' = rW L s p := by
  intro K _ J _ Ω _ _ x n bd hsnc harith _ htor hconj
  obtain ⟨I, hIh, hIle, hIsnc, hIeq⟩ :=
    PositivityTheory.Xgp.c_bm_exists_boundary.exists_homogIdeal x n bd hsnc harith htor
  obtain ⟨Rb, nb, W, hloc⟩ :=
    PositivityTheory.Xgp.c_bm_exists_boundary.exists_res x n I harith hIh hIle hIsnc
  rw [hIeq] at hloc
  obtain ⟨L, s, h1, h2, h3, h4, h5, h6⟩ :=
    PositivityTheory.Xgp.c_bm_exists_boundary.assemble Rb (mcPts (mCoordIdeal x) ∩ mcPts bd)
      (fun z hz c hc => htor z hz c hc) (fun z hz => hconj z hz) nb W hloc
  refine ⟨Rb, L, s, nb, fun _ => 1, W, h1, h2, h3, h4, fun p => ?_, h6⟩
  rw [h5 p]
  exact ⟨fun hp => hp.2, fun hp => ⟨Rb.mem p p (Rb.mem_U p), hp⟩⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerBoundHeightOnBoundaryStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerBound_height_on_boundary : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), Cmp.IsSncModel x n bd → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x) (n + 1) → IsClosed ((↑) ⁻¹' (mcPts (mCoordIdeal x) ∩ mcPts bd) : Set (mcPts (mCoordIdeal x))) → (∀ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd) → (∀ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd) → ∃ (Rb : AnLogRes (mCoordIdeal x) ⊤ n) (L : LocPot Rb.X) (s : Rb.X → Rb.X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set Rb.X), IsPotential Rb.A L ∧ IsSection Rb.A L s ∧ IsSNC Rb.A L s m W ∧ (∀ p, logNormSec L s p ≤ 0) ∧ (∀ p, p ∈ bdry s ↔ Rb.lift p p ∈ mcPts bd) ∧ ∀ p p', SameOrbit (Rb.lift p' p') (fun q => starRingEnd ℂ (Rb.lift p p q)) → rW L s p' = rW L s p := by
  first | exact @GlobalTheory.CompanionTheory.Relay.lowerBound_height_on_boundary | exact GlobalTheory.CompanionTheory.Relay.lowerBound_height_on_boundary | (intros; apply GlobalTheory.CompanionTheory.Relay.lowerBound_height_on_boundary <;> assumption)
end
